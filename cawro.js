// Global Vars
var ghost;

var timeStep = 1.0 / 60.0;

var doDraw = true;
var cw_paused = false;

var box2dfps = 60;
var screenfps = 60;

var debugbox = document.getElementById("debug");

var canvas = document.getElementById("mainbox");
var ctx = canvas.getContext("2d");

var cameraspeed = 0.05;
var camera_y = 0;
var camera_x = 0;
var camera_target = -1; // which car should we follow? -1 = leader
var minimapcamera = document.getElementById("minimapcamera").style;

var graphcanvas = document.getElementById("graphcanvas");
var graphctx = graphcanvas.getContext("2d");
var graphheight = 250;
var graphwidth = 400;

var minimapcanvas = document.getElementById("minimap");
var minimapctx = minimapcanvas.getContext("2d");
var minimapscale = 3;
var minimapfogdistance = 0;
var fogdistance = document.getElementById("minimapfog").style;

var generationSize = 20;
var cw_carArray = new Array();
var cw_carGeneration = new Array();
var cw_carScores = new Array();
var cw_topScores = new Array();
var cw_graphTop = new Array();
var cw_graphElite = new Array();
var cw_graphAverage = new Array();

var number_user_cars = 1;
var evolve_with_user_cars = false;
var gen_champions = 1;
var gen_parentality = 0.2;
var gen_mutation = 0.05;
var mutation_range = 1;
var gen_counter = 0;
var nAttributes = 15;

var gravity = new b2Vec2(0.0, -9.81);
var doSleep = true;

var world;

var zoom = 70;

var mutable_floor = false;

var maxFloorTiles = 200;
var cw_floorTiles = new Array();
var last_drawn_tile = 0;

var groundPieceWidth = 1.5;
var groundPieceHeight = 0.15;

var chassisMaxAxis = 1.1;
var chassisMinAxis = 0.1;
var chassisMinDensity = 30;
var chassisMaxDensity = 300;

var wheelMaxRadius = 0.5;
var wheelMinRadius = 0.2;
var wheelMaxDensity = 100;
var wheelMinDensity = 40;

var velocityIndex = 0;
var deathSpeed = 0.1;
var max_car_health = box2dfps * 10;
var car_health = max_car_health;

var motorSpeed = 20;

var swapPoint1 = 0;
var swapPoint2 = 0;

var cw_ghostReplayInterval = null;

var distanceMeter = document.getElementById("distancemeter");

var leaderPosition = new Object();
leaderPosition.x = 0;
leaderPosition.y = 0;

minimapcamera.width = 12*minimapscale+"px";
minimapcamera.height = 6*minimapscale+"px";

function debug(str, clear) {
  if (clear) {
    debugbox.innerHTML = "";
  }
  debugbox.innerHTML += str + "<br />";
}

function showDistance(distance, height) {
  distanceMeter.innerHTML = "distance: " + distance + " meters<br />";
  distanceMeter.innerHTML += "height: " + height + " meters";
  if (distance > minimapfogdistance) {
    fogdistance.width = 800 - Math.round(distance + 15) * minimapscale + "px";
    minimapfogdistance = distance;
  }
}

/* ========================================================================= */
/* === Car ================================================================= */
var cw_Car = function() {
  this.__constructor.apply(this, arguments);
};

cw_Car.prototype.chassis = null;

cw_Car.prototype.wheels = [];

cw_Car.prototype.__constructor = function(car_def) {
  this.velocityIndex = 0;
  this.health = max_car_health;
  this.maxPosition = 0;
  this.maxPositiony = 0;
  this.minPositiony = 0;
  this.frames = 0;
  this.car_def = car_def
  this.alive = true;
  this.is_elite = car_def.is_elite;
  this.is_user = car_def.is_user;
  this.healthBar = document.getElementById("health" + car_def.index).style;
  this.healthBarText = document.getElementById("health" + car_def.index).nextSibling.nextSibling;
  this.healthBarText.innerHTML = car_def.index;
  this.minimapmarker = document.getElementById("bar" + car_def.index);

  if (this.is_elite) {
    this.healthBar.backgroundColor = "#44c";
    this.minimapmarker.style.borderLeft = "1px solid #44c";
    this.minimapmarker.innerHTML = car_def.index;
  } else if (this.is_user) {
    this.healthBar.backgroundColor = "#4c4";
    this.minimapmarker.style.borderLeft = "1px solid #4c4";
    this.minimapmarker.innerHTML = car_def.index;
  } else {
    this.healthBar.backgroundColor = "#c44";
    this.minimapmarker.style.borderLeft = "1px solid #c44";
    this.minimapmarker.innerHTML = car_def.index;
  }

  this.chassis = cw_createChassis(car_def.vertex_list, car_def.chassis_density);

  this.wheels = [];
  for (var i = 0; i < car_def.wheels_list.length; i++) {
    this.wheels[i] = cw_createWheel(car_def.wheels_list[i].radius, car_def.wheels_list[i].density);
  }

  var carmass = this.chassis.GetMass();
  for (var i = 0; i < car_def.wheels_list.length; i++) {
    carmass += this.wheels[i].GetMass();
  }
  var torque = [];
  for (var i = 0; i < car_def.wheels_list.length; i++) {
    torque[i] = carmass * -gravity.y / car_def.wheels_list[i].radius;
  }

  var joint_def = new b2RevoluteJointDef();

  for (var i = 0; i < car_def.wheels_list.length; i++) {
    var randvertex = this.chassis.vertex_list[car_def.wheels_list[i].vertex];
    joint_def.localAnchorA.Set(randvertex.x, randvertex.y);
    joint_def.localAnchorB.Set(0, 0);
    joint_def.maxMotorTorque = torque[i];
    joint_def.motorSpeed = -motorSpeed;
    joint_def.enableMotor = true;
    joint_def.bodyA = this.chassis;
    joint_def.bodyB = this.wheels[i];
    var joint = world.CreateJoint(joint_def);
  }

  this.replay = ghost_create_replay();
  ghost_add_replay_frame(this.replay, this);
}

cw_Car.prototype.getPosition = function() {
  return this.chassis.GetPosition();
}

cw_Car.prototype.draw = function() {
  drawObject(this.chassis);

  for (var i = 0; i < this.wheels.length; i++) {
    drawObject(this.wheels[i]);
  }
}

cw_Car.prototype.kill = function() {
  var avgspeed = (this.maxPosition / this.frames) * box2dfps;
  var position = this.maxPosition;
  var score = position + avgspeed;
  ghost_compare_to_replay(this.replay, ghost, score);
  cw_carScores.push({
    car_def: this.car_def,
    v: score,
    s: avgspeed,
    x: position,
    y: this.maxPositiony,
    y2: this.minPositiony
  });
  world.DestroyBody(this.chassis);

  for (var i = 0; i < this.wheels.length; i++) {
    world.DestroyBody(this.wheels[i]);
  }
  this.alive = false;

  // refocus camera to leader on death
  if (camera_target === this.car_def.index) {
    cw_setCameraTarget(-1);
  }
}

cw_Car.prototype.checkDeath = function() {
  // check health
  var position = this.getPosition();
  if (position.y > this.maxPositiony) {
    this.maxPositiony = position.y;
  }
  if (position .y < this.minPositiony) {
    this.minPositiony = position.y;
  }
  if (position.x > this.maxPosition + 0.02) {
    this.health = max_car_health;
    this.maxPosition = position.x;
  } else {
    if (position.x > this.maxPosition) {
      this.maxPosition = position.x;
    }
    if (Math.abs(this.chassis.GetLinearVelocity().x) < 0.001) {
      this.health -= 5;
    }
    this.health--;
    if (this.health <= 0) {
      this.healthBarText.innerHTML = "&#8708;";
      this.healthBar.width = "0";
      return true;
    }
  }
}

function cw_createChassisPart(body, vertex1, vertex2, density) {
  var vertex_list = new Array();
  vertex_list.push(vertex1);
  vertex_list.push(vertex2);
  vertex_list.push(b2Vec2.Make(0, 0));
  var fix_def = new b2FixtureDef();
  fix_def.shape = new b2PolygonShape();
  fix_def.density = density;
  fix_def.friction = 10;
  fix_def.restitution = 0.2;
  fix_def.filter.groupIndex = -1;
  fix_def.shape.SetAsArray(vertex_list,3);

  body.CreateFixture(fix_def);
}

function cw_createChassis(vertex_list, density) {
  var body_def = new b2BodyDef();
  body_def.type = b2Body.b2_dynamicBody;
  body_def.position.Set(0.0, 4.0);

  var body = world.CreateBody(body_def);

  for (var i = 0; i < vertex_list.length; ++i) {
    cw_createChassisPart(body, vertex_list[i], vertex_list[(i + 1) % vertex_list.length], density);
  }

  body.vertex_list = vertex_list;

  return body;
}

function cw_createWheel(radius, density) {
  var body_def = new b2BodyDef();
  body_def.type = b2Body.b2_dynamicBody;
  body_def.position.Set(0, 0);

  var body = world.CreateBody(body_def);

  var fix_def = new b2FixtureDef();
  fix_def.shape = new b2CircleShape(radius);
  fix_def.density = density;
  fix_def.friction = 1;
  fix_def.restitution = 0.2;
  fix_def.filter.groupIndex = -1;

  body.CreateFixture(fix_def);
  return body;
}

function cw_createRandomCar(wheel_count) {
  var v = [];
  var car_def = new Object();

  car_def.wheels_list = Array.from(new Array(wheel_count), () => new Object());
  for (var i = 0; i < car_def.wheels_list.length; i++) {
    car_def.wheels_list[i].radius = Math.random()*wheelMaxRadius+wheelMinRadius;
    car_def.wheels_list[i].density = Math.random()*wheelMaxDensity+wheelMinDensity;
  }

  car_def.chassis_density = Math.random()*chassisMaxDensity+chassisMinDensity

  car_def.vertex_list = new Array();
  car_def.vertex_list.push({
    x: Math.random() * chassisMaxAxis + chassisMinAxis,
    y: 0
  });
  car_def.vertex_list.push({
    x: Math.random() * chassisMaxAxis + chassisMinAxis,
    y: Math.random() * chassisMaxAxis + chassisMinAxis
  });
  car_def.vertex_list.push({
    x: 0,
    y: Math.random() * chassisMaxAxis + chassisMinAxis
  });
  car_def.vertex_list.push({
    x: -Math.random() * chassisMaxAxis - chassisMinAxis,
    y: Math.random() * chassisMaxAxis + chassisMinAxis
  });
  car_def.vertex_list.push({
    x: -Math.random() * chassisMaxAxis - chassisMinAxis,
    y: 0
  });
  car_def.vertex_list.push({
    x: -Math.random() * chassisMaxAxis - chassisMinAxis,
    y: -Math.random() * chassisMaxAxis - chassisMinAxis
  });
  car_def.vertex_list.push({
    x: 0,
    y: -Math.random() * chassisMaxAxis - chassisMinAxis
  });
  car_def.vertex_list.push({
    x: Math.random() * chassisMaxAxis + chassisMinAxis,
    y: -Math.random() * chassisMaxAxis - chassisMinAxis
  });

  var left = [];
  for (var i = 0; i < car_def.vertex_list.length; i++) {
    left.push(i);
  }
  for (var i = 0; i < car_def.wheels_list.length; i++) {
    var indexOfNext = Math.floor(Math.random() * left.length);
    car_def.wheels_list[i].vertex = left[indexOfNext];
    left.splice(indexOfNext, 1);
  }

  return cw_sortCarVertexes(car_def);
}

/* === END Car ============================================================= */
/* ========================================================================= */


/* ========================================================================= */
/* ==== Generation ========================================================= */

function cw_generationZero() {
  for (var k = 0; k < number_user_cars; k++) {
    var car_def = cw_createUserCar();
    car_def.index = k;
    car_def.is_user = true;
    cw_carGeneration.push(car_def);
  }
  for (var k = number_user_cars; k < generationSize; k++) {
    var car_def = cw_createRandomCar(2);
    car_def.index = k;
    cw_carGeneration.push(car_def);
  }
  gen_counter = 0;
  cw_deadCars = 0;
  leaderPosition = new Object();
  leaderPosition.x = 0;
  leaderPosition.y = 0;
  cw_materializeGeneration();
  document.getElementById("generation").innerHTML = "generation 0";
  document.getElementById("population").innerHTML = "cars alive: "+generationSize;
  ghost = ghost_create_ghost();
}

function cw_materializeGeneration() {
  cw_carArray = new Array();
  for (var k = 0; k < generationSize; k++) {
    var car;
    try {
      car = new cw_Car(cw_carGeneration[k]);
    } catch (exception) {
      console.error("Failed to generate car " + k + ", creating a new one in its place", exception);
      cw_carGeneration[k] = {
        ...cw_carGeneration[k],
        ...cw_createRandomCar(cw_carGeneration[k].wheels_list.length)
      };
      car = new cw_Car(cw_carGeneration[k]);
    }
    cw_carArray.push(car);
  }
}

function cw_nextGeneration() {
  var newGeneration = new Array();
  var newborn;
  var champions = cw_getChampions();
  cw_topScores.push({
    i: gen_counter,
    v: cw_carScores[0].v,
    x: cw_carScores[0].x,
    y: cw_carScores[0].y,
    y2: cw_carScores[0].y2
  });
  plot_graphs();
  for (var k = 0; k < number_user_cars; k++) {
    var car_def = cw_createUserCar();
    car_def.index = k;
    car_def.is_user = true;
    newGeneration.push(car_def);
  }
  for (var k = 0; k < gen_champions; k++) {
    champions[k].car_def.is_user = false;
    champions[k].car_def.is_elite = true;
    champions[k].car_def.index = number_user_cars + k;
    newGeneration.push(champions[k].car_def);
  }
  for (var k = number_user_cars + gen_champions; k < generationSize; k++) {
    var parent1 = cw_getParents();
    var parent2 = parent1;
    while (parent2 === parent1) {
      parent2 = cw_getParents();
    }
    var newborn = cw_makeChild(champions[parent1].car_def, champions[parent2].car_def);
    newborn = cw_mutate(newborn);
    newborn.is_user = false;
    newborn.is_elite = false;
    newborn.index = k;
    newGeneration.push(cw_sortCarVertexes(newborn));
  }
  cw_carScores = new Array();
  cw_carGeneration = newGeneration;
  gen_counter++;
  cw_materializeGeneration();
  cw_deadCars = 0;
  leaderPosition = new Object();
  leaderPosition.x = 0;
  leaderPosition.y = 0;
  document.getElementById("generation").innerHTML = "generation " + gen_counter;
  document.getElementById("cars").innerHTML = "";
  document.getElementById("population").innerHTML = "cars alive: " + generationSize;
}

function cw_getChampions() {
  var ret = new Array();
  cw_carScores.sort(function(a, b) { return (a.v > b.v) ? -1 : 1 });
  for (var k = 0; k < generationSize; k++) {
    if (evolve_with_user_cars || !cw_carScores[k].car_def.is_user) {
      ret.push(cw_carScores[k]);
    }
  }
  return ret;
}

function cw_getParents() {
    var r = Math.random();
    if (r === 0) {
      return 0;
    }
    return Math.floor(-Math.log(r) * (generationSize - number_user_cars)) % (generationSize - number_user_cars);
}

function cw_makeChild(car_def1, car_def2) {
  var newCarDef = new Object();
  swapPoint1 = Math.round(Math.random() * (nAttributes - 1));
  swapPoint2 = swapPoint1;
  while (swapPoint2 === swapPoint1) {
    swapPoint2 = Math.round(Math.random() * (nAttributes - 1));
  }

  var parents = [car_def1, car_def2];
  var curparent = 0;

  // Parent genetics ratios
  parents[0].score = cw_carScores[parents[0].index].v;
  parents[1].score = cw_carScores[parents[1].index].v;
  totalParentScore = parents[0].score + parents[1].score;

  // Inheriting vertexes
  var vertex_count = Math.round((parents[0].score * parents[0].vertex_list.length + parents[1].score * parents[1].vertex_list.length) / totalParentScore);
  newCarDef.vertex_list = new Array(vertex_count);

  for (var i = 0; i < newCarDef.vertex_list.length; i++) {
    curparent = cw_chooseParent(curparent, i + 4);
    var parentVertexes = parents[curparent].vertex_list;

    var parentVertexRatio = parentVertexes.length / newCarDef.vertex_list.length;
    var preParentVertex = parentVertexes[Math.floor(i * parentVertexRatio)];
    var posParentVertex = parentVertexes[Math.ceil(i * parentVertexRatio) % parentVertexes.length];

    var x = preParentVertex.x + (posParentVertex.x - preParentVertex.x) * i / newCarDef.vertex_list.length;
    var y = preParentVertex.y + (posParentVertex.y - preParentVertex.y) * i / newCarDef.vertex_list.length;

    newCarDef.vertex_list[i] = { x, y };
  }

  // Inheriting wheels
  var wheel_count = Math.floor((parents[0].score * parents[0].wheels_list.length + parents[1].score * parents[1].wheels_list.length) / totalParentScore);
  newCarDef.wheels_list = Array.from(new Array(wheel_count), () => new Object());

  for (var i = 0; i < newCarDef.wheels_list.length; i++) {
    curparent = cw_chooseParent(curparent, i);
    var parentWheelIndex = Math.floor(i * parents[curparent].wheels_list.length / newCarDef.wheels_list.length);
    newCarDef.wheels_list[i].radius = parents[curparent].wheels_list[parentWheelIndex].radius;
  }

  for (var i = 0; i < newCarDef.wheels_list.length; i++) {
    curparent = cw_chooseParent(curparent, i + 2);
    var parentWheelIndex = Math.floor(i * parents[curparent].wheels_list.length / newCarDef.wheels_list.length);
    newCarDef.wheels_list[i].vertex = Math.floor(parents[curparent].wheels_list[parentWheelIndex].vertex * newCarDef.vertex_list.length / parents[curparent].vertex_list.length);
  }

  for (var i = 0; i < newCarDef.wheels_list.length; i++) {
    curparent = cw_chooseParent(curparent, i + 12);
    var parentWheelIndex = Math.floor(i * parents[curparent].wheels_list.length / newCarDef.wheels_list.length);
    newCarDef.wheels_list[i].density = parents[curparent].wheels_list[parentWheelIndex].density;
  }

  curparent = cw_chooseParent(curparent, 14);
  newCarDef.chassis_density = parents[curparent].chassis_density;

  return newCarDef;
}

function cw_mutate1(old, min, range) {
    var span = range * mutation_range;
    var base = old - 0.5 * span;
    if (base < min)
        base = min;
    if (base > min + (range - span))
        base = min + (range - span);
    return base + span * Math.random();
}

function cw_mutatev(car_def, n, xfact, yfact) {
    if (Math.random() >= gen_mutation) {
        return;
    }

    var v = car_def.vertex_list[n];
    var x = 0;
    var y = 0;
    if (xfact !== 0) {
        x = xfact * cw_mutate1(xfact * v.x, chassisMinAxis, chassisMaxAxis);
    }
    if (yfact !== 0) {
        y = yfact * cw_mutate1(yfact * v.y, chassisMinAxis, chassisMaxAxis);
    }
    car_def.vertex_list[n].x = x;
    car_def.vertex_list[n].y = y;
}

function cw_mutate(car_def) {
  for (var i = 0; i < car_def.wheels_list.length; i++) {
    if (Math.random() < gen_mutation) {
      car_def.wheels_list[i].radius = cw_mutate1(car_def.wheels_list[i].radius, wheelMinRadius, wheelMaxRadius);
    }
  }

  var wheel_m_rate = mutation_range < gen_mutation ? mutation_range : gen_mutation;

  for (var i = 0; i < car_def.wheels_list.length; i++) {
    if (Math.random() < wheel_m_rate) {
      car_def.wheels_list[i].vertex = Math.floor(Math.random() * car_def.vertex_list.length) % car_def.vertex_list.length;
    }
  }

  for (var i = 0; i < car_def.wheels_list.length; i++) {
    if (Math.random() < gen_mutation) {
      car_def.wheels_list[i].density = cw_mutate1(car_def.wheels_list[i].density, wheelMinDensity, wheelMaxDensity);
    }
  }

  if (Math.random() < gen_mutation) {
    car_def.chassis_density = cw_mutate1(car_def.chassis_density, chassisMinDensity, chassisMaxDensity);
  }

  for (var i = 0; i < car_def.vertex_list.length; i++) {
    var factIndex = i * 8 / car_def.vertex_list.length;
    var xfact = Math.sign((4 - (factIndex + 2) % 8) % 4);
    var yfact = Math.sign((4 - factIndex) % 4);
    cw_mutatev(car_def, i, xfact, yfact);
  }

  return car_def;
}

function cw_chooseParent(curparent, attributeIndex) {
  var ret;
  if ((swapPoint1 === attributeIndex) || (swapPoint2 === attributeIndex)) {
    ret = (curparent === 1) ? 0 : 1;
  } else {
    ret = curparent;
  }
  return ret;
}

function cw_setMutation(mutation) {
  gen_mutation = parseFloat(mutation);
}

function cw_setMutationRange(range) {
  mutation_range = parseFloat(range);
}

function cw_setMutableFloor(choice) {
  mutable_floor = (choice==1);
}

function cw_setGravity(choice) {
  gravity = new b2Vec2(0.0, -parseFloat(choice));
  // CHECK GRAVITY CHANGES
  if (world.GetGravity().y !== gravity.y) {
    world.SetGravity(gravity);
  }
}

function cw_setEliteSize(clones) {
  gen_champions = parseInt(clones, 10);
}

function cw_setEvolveWithUserCars(evolveWithUserCars) {
  evolve_with_user_cars = evolveWithUserCars;
}

/* ==== END Genration ====================================================== */
/* ========================================================================= */

/* ========================================================================= */
/* ==== Drawing ============================================================ */

function cw_drawScreen() {
  ctx.clearRect(0, 0, canvas.width, canvas.height);
  ctx.save();
  cw_setCameraPosition();
  ctx.translate(200 - (camera_x * zoom), 200 + (camera_y * zoom));
  ctx.scale(zoom, -zoom);
  cw_drawFloor();
  ghost_draw_frame(ctx, ghost);
  cw_drawCars();
  ctx.restore();
}

function cw_minimapCamera(x, y) {
  minimapcamera.left = Math.round((2 + camera_x) * minimapscale) + "px";
  minimapcamera.top = Math.round((31 - camera_y) * minimapscale) + "px";
}

function cw_setCameraTarget(k) {
  camera_target = k;
}

function cw_setCameraPosition() {
  var cameraTargetPosition;
  if (camera_target >= 0) {
    cameraTargetPosition = cw_carArray[camera_target].getPosition();
  } else {
    cameraTargetPosition = leaderPosition;
  }
  var diff_y = camera_y - cameraTargetPosition.y;
  var diff_x = camera_x - cameraTargetPosition.x;
  camera_y -= cameraspeed * diff_y;
  camera_x -= cameraspeed * diff_x;
  cw_minimapCamera(camera_x, camera_y);
}

function cw_drawGhostReplay() {
  var carPosition = ghost_get_position(ghost);
  camera_x = carPosition.x;
  camera_y = carPosition.y;
  cw_minimapCamera(camera_x, camera_y);
  showDistance(Math.round(carPosition.x * 100) / 100, Math.round(carPosition.y * 100) / 100);
  ctx.clearRect(0, 0, canvas.width, canvas.height);
  ctx.save();
  ctx.translate(200 - (carPosition.x * zoom), 200 + (carPosition.y * zoom));
  ctx.scale(zoom, -zoom);
  ghost_draw_frame(ctx, ghost);
  ghost_move_frame(ghost);
  cw_drawFloor();
  ctx.restore();
}

function cw_drawCars() {
  for (var k = (cw_carArray.length - 1); k >= 0; k--) {
    var myCar = cw_carArray[k];
    if (!myCar.alive) {
      continue;
    }
    myCarPos = myCar.getPosition();

    if (myCarPos.x < (camera_x - 5)) {
      // too far behind, don't draw
      continue;
    }

    ctx.strokeStyle = "#444";
    ctx.lineWidth = 1 / zoom;

    for (var i = 0; i < myCar.wheels.length; i++) {
      var b = myCar.wheels[i];
      for (f = b.GetFixtureList(); f; f = f.m_next) {
        var s = f.GetShape();
        var color = Math.round(255 - (255 * (f.m_density - wheelMinDensity)) / wheelMaxDensity).toString();
        var rgbcolor = "rgb(" + color + ", " + color + ", " + color + ")";
        cw_drawCircle(ctx, b, s.m_p, s.m_radius, b.m_sweep.a, rgbcolor);
      }
    }

    var densitycolor = Math.round(100 - (70 * ((myCar.car_def.chassis_density - chassisMinDensity) / chassisMaxDensity))).toString() + "%";
    if (myCar.is_elite) {
      ctx.strokeStyle = "#44c";
      //ctx.fillStyle = "#ddf";
      ctx.fillStyle = "hsl(240, 50%, " + densitycolor + ")";
    } else if (myCar.is_user) {
      ctx.strokeStyle = "#4c4";
      //ctx.fillStyle = "#dfd";
      ctx.fillStyle = "hsl(120, 50%, " + densitycolor + ")";
    } else {
      ctx.strokeStyle = "#c44";
      //ctx.fillStyle = "#fdd";
      ctx.fillStyle = "hsl(0, 50%, " + densitycolor + ")";
    }
    ctx.beginPath();
    var b = myCar.chassis;
    for (f = b.GetFixtureList(); f; f = f.m_next) {
      var s = f.GetShape();
      cw_drawVirtualPoly(ctx, b, s.m_vertices, s.m_vertexCount);
    }
    ctx.fill();
    ctx.stroke();
  }
}

function toggleDisplay() {
  if (cw_paused) {
    return;
  }
  canvas.width = canvas.width;
  if (doDraw) {
    doDraw = false;
    cw_stopSimulation();
    cw_runningInterval = setInterval(simulationStep, 1); // simulate 1000x per second when not drawing
  } else {
    doDraw = true;
    clearInterval(cw_runningInterval);
    cw_startSimulation();
  }
}

function cw_drawVirtualPoly(ctx, body, vtx, n_vtx) {
  // set strokestyle and fillstyle before call
  // call beginPath before call

  var p0 = body.GetWorldPoint(vtx[0]);
  ctx.moveTo(p0.x, p0.y);
  for (var i = 1; i < n_vtx; i++) {
    p = body.GetWorldPoint(vtx[i]);
    ctx.lineTo(p.x, p.y);
  }
  ctx.lineTo(p0.x, p0.y);
}

function cw_drawPoly(body, vtx, n_vtx) {
  // set strokestyle and fillstyle before call
  ctx.beginPath();

  var p0 = body.GetWorldPoint(vtx[0]);
  ctx.moveTo(p0.x, p0.y);
  for (var i = 1; i < n_vtx; i++) {
    var p = body.GetWorldPoint(vtx[i]);
    ctx.lineTo(p.x, p.y);
  }
  ctx.lineTo(p0.x, p0.y);

  ctx.fill();
  ctx.stroke();
}

function cw_drawCircle(ctx, body, center, radius, angle, color) {
  var p = body.GetWorldPoint(center);
  ctx.fillStyle = color;

  ctx.beginPath();
  ctx.arc(p.x, p.y, radius, 0, 2 * Math.PI, true);

  ctx.moveTo(p.x, p.y);
  ctx.lineTo(p.x + radius*Math.cos(angle), p.y + radius*Math.sin(angle));

  ctx.fill();
  ctx.stroke();
}

function cw_drawMiniMap() {
  var last_tile = null;
  var tile_position = new b2Vec2(-5, 0);
  minimapfogdistance = 0;
  fogdistance.width = "800px";
  minimapcanvas.width = minimapcanvas.width;
  minimapctx.strokeStyle = "#000";
  minimapctx.beginPath();
  minimapctx.moveTo(0, 35 * minimapscale);
  for (var k = 0; k < cw_floorTiles.length; k++) {
    last_tile = cw_floorTiles[k];
    last_fixture = last_tile.GetFixtureList();
    last_world_coords = last_tile.GetWorldPoint(last_fixture.GetShape().m_vertices[3]);
    tile_position = last_world_coords;
    minimapctx.lineTo((tile_position.x + 5) * minimapscale, (-tile_position.y + 35) * minimapscale);
  }
  minimapctx.stroke();
}

/* ==== END Drawing ======================================================== */
/* ========================================================================= */

/* ========================================================================= */
/* ==== User Car============================================================ */

var user_car_def;

var user_car_handler_color_wheel_radius = "#ff00ff";
var user_car_handler_color_wheel_vertex = "#ff0000";
var user_car_handler_color_wheel_density = "#0000ff";
var user_car_handler_color_chassis_vertex = "#ff0000";
var user_car_handler_color_chassis_density = "#0000ff";

function cw_initRandomUserCar() {
  user_car_def = cw_createRandomCar(2);
  cw_initUserCar();
}

function cw_initUserCar(userCarDef) {
  var stage = new Kinetic.Stage({
    container: "user_car_container",
    width: 800,
    height: 600,
    offsetX: -400,
    offsetY: 300,
    scaleY: -1
  });

  var layer = new Kinetic.Layer();
  stage.add(layer);

  cw_initUserCarWheels(layer);
  cw_initUserCarChassis(layer);

  cw_initUserCarWheelHandlers(layer);
  cw_initUserCarChassisHandlers(layer);

  layer.draw();

  document.getElementById("serialize_user_car").onclick = cw_serializeUserCar();
  document.getElementById("deserialize_user_car").onclick = cw_deserializeUserCar(layer);
}

function cw_serializeUserCar() {
  return function() {
    document.getElementById("user_car_json").value = JSON.stringify(user_car_def);
  };
}

function cw_deserializeUserCar(layer) {
  return function() {
    layer.clear();
    user_car_def = cw_sortCarVertexes(JSON.parse(document.getElementById("user_car_json").value));
    cw_initUserCar();
  };
}

function cw_initUserCarWheels(layer) {
  for (var i = 0; i < user_car_def.wheels_list.length; i++) {
    cw_initUserCarWheel(layer, i);
  }
}

function cw_initUserCarWheel(layer, wheel_index) {
  var wheel_circle = new Kinetic.Shape({
    id: "user_car_wheel_circle_" + wheel_index,
    sceneFunc: function(context) {
      var wheel_vertex = user_car_def.vertex_list[user_car_def.wheels_list[wheel_index].vertex];
      var wheel_radius = user_car_def.wheels_list[wheel_index].radius;
      var wheel_density = user_car_def.wheels_list[wheel_index].density;
      var wheel_color = Math.round(255 - (255 * (wheel_density - wheelMinDensity)) / wheelMaxDensity);

      wheel_circle.fill("rgb(" + wheel_color + "," + wheel_color + "," + wheel_color + ")");

      context.beginPath();
      context.arc(100 * wheel_vertex.x, 100 * wheel_vertex.y, 100 * wheel_radius, 0, 2 * Math.PI);
      context.closePath();
      context.fillStrokeShape(this);
    },
    stroke: "#000000",
    strokeWidth: 1
  });
  layer.add(wheel_circle);

  layer.add(new Kinetic.Shape({
    id: "user_car_wheel_radius_" + wheel_index,
    sceneFunc: function(context) {
      var wheel_vertex = user_car_def.vertex_list[user_car_def.wheels_list[wheel_index].vertex];
      var wheel_radius = user_car_def.wheels_list[wheel_index].radius;

      context.beginPath();
      context.moveTo(100 * wheel_vertex.x, 100 * wheel_vertex.y);
      context.lineTo(100 * (wheel_vertex.x + wheel_radius), 100 * wheel_vertex.y);
      context.closePath();
      context.fillStrokeShape(this);
    },
    stroke: "#000000",
    strokeWidth: 1
  }));

  layer.add(new Kinetic.Shape({
    id: "user_car_wheel_density_" + wheel_index,
    sceneFunc: function(context) {
      var wheel_vertex = user_car_def.vertex_list[user_car_def.wheels_list[wheel_index].vertex];
      var wheel_density = user_car_def.wheels_list[wheel_index].density;

      context.beginPath();
      context.moveTo(100 * wheel_vertex.x, 100 * wheel_vertex.y);
      context.lineTo(100 * wheel_vertex.x, 100 * (wheel_vertex.y + wheel_density / wheelMaxDensity));
      context.closePath();
      context.fillStrokeShape(this);
    },
    stroke: "#000000",
    strokeWidth: 1
  }));
}

function cw_initUserCarWheelHandlers(layer) {
  for (var i = 0; i < user_car_def.wheels_list.length; i++) {
    cw_initUserCarWheelRadiusHandler(layer, i);
    cw_initUserCarWheelVertexHandler(layer, i);
    cw_initUserCarWheelDensityHandler(layer, i);
  }
}

function cw_initUserCarWheelRadiusHandler(layer, wheel_index) {
  var wheel_vertex = user_car_def.vertex_list[user_car_def.wheels_list[wheel_index].vertex];
  var wheel_radius = user_car_def.wheels_list[wheel_index].radius;

  var wheel_radius_handler = new Kinetic.Circle({
    id: "user_car_wheel_radius_handler_" + wheel_index,
    x: 100 * (wheel_vertex.x + wheel_radius),
    y: 100 * wheel_vertex.y,
    radius: 10,
    stroke: user_car_handler_color_wheel_radius,
    strokeWidth: 1,
    draggable: true
  });

  wheel_radius_handler.on("dragmove", function() {
    var wheel_vertex = user_car_def.vertex_list[user_car_def.wheels_list[wheel_index].vertex];
    wheel_radius_handler.setY(100 * wheel_vertex.y);
    user_car_def.wheels_list[wheel_index].radius = Math.abs((wheel_radius_handler.x() / 100) - wheel_vertex.x);
  });

  layer.add(wheel_radius_handler);
}

function cw_initUserCarWheelVertexHandler(layer, wheel_index) {
  var wheel_vertex = user_car_def.vertex_list[user_car_def.wheels_list[wheel_index].vertex];

  var wheel_vertex_handler = new Kinetic.Circle({
    id: "user_car_wheel_vertex_handler_" + wheel_index,
    x: 100 * wheel_vertex.x,
    y: 100 * wheel_vertex.y,
    radius: 20,
    stroke: user_car_handler_color_wheel_vertex,
    strokeWidth: 1,
    draggable: true
  });

  wheel_vertex_handler.on("dragmove", function() {
    var wheel_vertex_handler_x = wheel_vertex_handler.x() / 100;
    var wheel_vertex_handler_y = wheel_vertex_handler.y() / 100;

    var first_wheel_vertex = user_car_def.wheels_list[wheel_index].vertex;
    var final_wheel_vertex = cw_findClosestUserCarVertexIndex(wheel_vertex_handler_x, wheel_vertex_handler_y);
    if (first_wheel_vertex !== final_wheel_vertex) {
      user_car_def.wheels_list[wheel_index].vertex = final_wheel_vertex;
      cw_redrawUserCarWheelRadiusHandler(layer, wheel_index);
      cw_redrawUserCarWheelDensityHandler(layer, wheel_index);
    }
  });

  wheel_vertex_handler.on("dragend", function() {
    cw_redrawUserCarWheelRadiusHandler(layer, wheel_index);
    cw_redrawUserCarWheelVertexHandler(layer, wheel_index);
    cw_redrawUserCarWheelDensityHandler(layer, wheel_index);
  });

  layer.add(wheel_vertex_handler);
}

function cw_initUserCarWheelDensityHandler(layer, wheel_index) {
  var wheel_vertex = user_car_def.vertex_list[user_car_def.wheels_list[wheel_index].vertex];
  var wheel_density = user_car_def.wheels_list[wheel_index].density;

  var wheel_density_handler = new Kinetic.Circle({
    id: "user_car_wheel_density_handler_" + wheel_index,
    x: 100 * wheel_vertex.x,
    y: 100 * (wheel_vertex.y + wheel_density / wheelMaxDensity),
    radius: 10,
    stroke: user_car_handler_color_wheel_density,
    strokeWidth: 1,
    draggable: true
  });

  wheel_density_handler.on("dragmove", function() {
    var wheel_vertex = user_car_def.vertex_list[user_car_def.wheels_list[wheel_index].vertex];

    wheel_density_handler.setX(100 * wheel_vertex.x);
    user_car_def.wheels_list[wheel_index].density = wheelMaxDensity * ((wheel_density_handler.y() / 100) - wheel_vertex.y);
  });

  layer.add(wheel_density_handler);
}

function cw_initUserCarChassis(layer) {
  for (var i = 0; i < user_car_def.vertex_list.length; i++) {
    cw_initUserCarChassisPart(layer, i);
  }

  layer.add(new Kinetic.Shape({
    id: "user_car_chassis_density",
    sceneFunc: function(context) {
      var chassis_density = user_car_def.chassis_density;

      context.beginPath();
      context.moveTo(0, 0);
      context.lineTo(0, 100 * chassis_density / chassisMaxDensity);
      context.closePath();
      context.fillStrokeShape(this);
    },
    stroke: "#000000",
    strokeWidth: 1
  }));
}

function cw_initUserCarChassisPart(layer, vertex_index) {
  var chassis_part = new Kinetic.Shape({
    id: "user_car_chassis_part_" + vertex_index,
    sceneFunc: function(context) {
      var vertex_0 = user_car_def.vertex_list[vertex_index];
      var vertex_1 = user_car_def.vertex_list[(vertex_index + 1) % user_car_def.vertex_list.length];
      var chassis_color = Math.round(100 - (70 * ((user_car_def.chassis_density - chassisMinDensity) / chassisMaxDensity))).toString() + "%";

      chassis_part.fill("hsla(120, 50%, " + chassis_color + ", 0.7)");

      context.beginPath();
      context.moveTo(0, 0);
      context.lineTo(100 * vertex_0.x, 100 * vertex_0.y);
      context.lineTo(100 * vertex_1.x, 100 * vertex_1.y);
      context.closePath();
      context.fillStrokeShape(this);
    },
    fill: "#ff00ff",
    stroke: "#44cc44"
  });
  layer.add(chassis_part);
}

function cw_initUserCarChassisHandlers(layer) {
  for (var i = 0; i < user_car_def.vertex_list.length; i++) {
    cw_initUserCarVertexHandler(layer, i);
  }

  cw_initUserCarChassisDensityHandler(layer);
}

function cw_initUserCarVertexHandler(layer, vertex_index) {
  var vertex = user_car_def.vertex_list[vertex_index];

  var vertex_handler = new Kinetic.Circle({
    id: "user_car_vertex_handler_" + vertex_index,
    x: 100 * vertex.x,
    y: 100 * vertex.y,
    radius: 10,
    stroke: user_car_handler_color_chassis_vertex,
    strokeWidth: 1,
    draggable: true
  });

  vertex_handler.on("dragmove", function(event) {
    vertex.x = event.target.x() / 100;
    vertex.y = event.target.y() / 100;

    for (var i = 0; i < user_car_def.wheels_list.length; ++i) {
      cw_redrawUserCarWheelRadiusHandler(layer, i);
      cw_redrawUserCarWheelVertexHandler(layer, i);
      cw_redrawUserCarWheelDensityHandler(layer, i);
    }
  })

  layer.add(vertex_handler);
}

function cw_initUserCarChassisDensityHandler(layer) {
  var chassis_density_handler = new Kinetic.Circle({
    id: "user_car_chassis_density_handler",
    x: 0,
    y: 100 * user_car_def.chassis_density / chassisMaxDensity,
    radius: 10,
    stroke: user_car_handler_color_chassis_density,
    strokeWidth: 1,
    draggable: true
  });

  chassis_density_handler.on("dragmove", function() {
    chassis_density_handler.setX(0);
    user_car_def.chassis_density = chassisMaxDensity * (chassis_density_handler.y() / 100);
  });

  layer.add(chassis_density_handler);
}

function cw_createUserCar() {
  return JSON.parse(JSON.stringify(user_car_def));
}

function cw_findClosestUserCarVertexIndex(x, y) {
    var closest_vertex_distance = -1;
    var closest_vertex_index = -1;

    for (var i = 0; i < user_car_def.vertex_list.length; i++) {
      var vertex = user_car_def.vertex_list[i];
      var vertex_distance = Math.sqrt(Math.pow(vertex.x - x, 2) + Math.pow(vertex.y - y, 2));

      if ((closest_vertex_distance < 0)|| (vertex_distance < closest_vertex_distance)) {
        closest_vertex_distance = vertex_distance;
        closest_vertex_index = i;
      }
    }

    return closest_vertex_index;
}

function cw_sortCarVertexes(car_def) {
  var vertex_list = cw_rearrangeVertexes(car_def.vertex_list);
  var wheels_list = car_def.wheels_list.map((wheel) => {
    var wheelVertex = vertex_list.find((vertex) => vertex.index === wheel.vertex)
    if (!wheelVertex) {
      wheelVertex = vertex_list[Math.floor(Math.random() * vertex_list.length) % vertex_list.length];
    }
    return {
      ...wheel,
      vertex: wheelVertex.index,
    }
  });

  return {
    ...car_def,
    vertex_list,
    wheels_list,
  };
}

function cw_rearrangeVertexes(vertexes) {
  var centroid = vertexes.reduce((centroid, vertex) => ({
    x: centroid.x + vertex.x / vertexes.length,
    y: centroid.y + vertex.y / vertexes.length,
  }), { x: 0, y: 0 });

  return vertexes.map((vertex, index) => ({
    x: vertex.x - centroid.x,
    y: vertex.y - centroid.y,
    index,
  })).filter((vertex) => (
    // The center can't be one of the vertex
    vertex.x !== 0 || vertex.y !== 0
  )).sort((vertex1, vertex2) => {
    var orientation = cw_getVertexesOrientation(vertex1, vertex2);
    if (orientation === 0) {
      return cw_getModulusSquared(vertex1) < cw_getModulusSquared(vertex2) ? 1 : -1;
    }
    return (orientation === 2) ? -1 : 1;
  }).filter((vertex1, index, rearrangedVertexes) => {
    if (index === 0) {
      return true;
    }
    
    // Colinear points can't be vertexes
    var vertex0 = rearrangedVertexes[index - 1];
    return (vertex0.y - vertex1.y) / (vertex0.x - vertex1.x) != vertex1.y / vertex1.x;
  });
}

function cw_getVertexesOrientation(vertex1, vertex2) {
  var crossProduct = vertex1.y * vertex2.x - vertex1.x * vertex2.y;
  if (crossProduct === 0) {
    return 0;
  }
  return (crossProduct > 0) ? 1 : 2;
}

function cw_getModulusSquared(vertex) {
  return vertex.x * vertex.x + vertex.y * vertex.y;
}

function cw_redrawUserCarWheelRadiusHandler(layer, wheel_index) {
  var wheel_radius_handler = layer.find("#user_car_wheel_radius_handler_" + wheel_index);
  var wheel_vertex = user_car_def.vertex_list[user_car_def.wheels_list[wheel_index].vertex];
  var wheel_radius = user_car_def.wheels_list[wheel_index].radius;
  wheel_radius_handler.setX(100 * (wheel_vertex.x + wheel_radius));
  wheel_radius_handler.setY(100 * wheel_vertex.y);

  layer.draw();
}

function cw_redrawUserCarWheelVertexHandler(layer, wheel_index) {
  var wheel_vertex_handler = layer.find("#user_car_wheel_vertex_handler_" + wheel_index);
  var wheel_vertex = user_car_def.vertex_list[user_car_def.wheels_list[wheel_index].vertex];
  wheel_vertex_handler.setX(100 * wheel_vertex.x);
  wheel_vertex_handler.setY(100 * wheel_vertex.y);

  layer.draw();
}

function cw_redrawUserCarWheelDensityHandler(layer, wheel_index) {
  var wheel_density_handler = layer.find("#user_car_wheel_density_handler_" + wheel_index);
  var wheel_vertex = user_car_def.vertex_list[user_car_def.wheels_list[wheel_index].vertex];
  var wheel_density = user_car_def.wheels_list[wheel_index].density;

  wheel_density_handler.setX(100 * wheel_vertex.x);
  wheel_density_handler.setY(100 * (wheel_vertex.y + wheel_density / wheelMaxDensity));

  layer.draw();
}

function cw_redrawUserCarChassisVertexHandler(layer, vertex_index) {
  var vertex_handler = layer.find("#user_car_vertex_handler_" + vertex_index);
  var vertex = user_car_def.vertex_list[vertex_index];
  vertex_handler.setX(100 * vertex.x);
  vertex_handler.setY(100 * vertex.y);

  layer.draw();
}

function cw_redrawUserCarChassisDensityHandler(layer) {
  var chassis_density_handler = layer.find("#user_car_chassis_density_handler");
  var chassis_density = user_car_def.chassis_density;
  chassis_density_handler.setX(0);
  chassis_density_handler.setY(100 * chassis_density / chassisMaxDensity);

  layer.draw();
}

/* ==== END User Car ======================================================= */
/* ========================================================================= */

var last_tile_world_coords = null;

function simulationStep() {
  world.Step(1 / box2dfps, 20, 20);
  ghost_move_frame(ghost);
  for (var k = 0; k < generationSize; k++) {
    if (!cw_carArray[k].alive) {
      continue;
    }
    ghost_add_replay_frame(cw_carArray[k].replay, cw_carArray[k]);
    cw_carArray[k].frames++;
    var position = cw_carArray[k].getPosition();
    cw_carArray[k].minimapmarker.style.left = Math.round((position.x + 5) * minimapscale) + "px";
    cw_carArray[k].healthBar.width = Math.round((cw_carArray[k].health / max_car_health) * 100) + "%";
    if (cw_carArray[k].checkDeath()) {
      cw_carArray[k].kill();
      cw_deadCars++;
      document.getElementById("population").innerHTML = "cars alive: " + (generationSize-cw_deadCars);
      cw_carArray[k].minimapmarker.style.borderLeft = "1px solid #ccc";
      if (cw_deadCars >= generationSize) {
        cw_newRound();
      }
      if (leaderPosition.leader === k) {
        // leader is dead, find new leader
        cw_findLeader();
      }
      continue;
    }
    if (position.x > leaderPosition.x) {
      leaderPosition = position;
      leaderPosition.leader = k;
    }
  }

  if (last_tile_world_coords.x - leaderPosition.x <= 10) {
    maxFloorTiles += 100;
    cw_createFloor();
    cw_drawMiniMap();
  }

  showDistance(Math.round(leaderPosition.x * 100) / 100, Math.round(leaderPosition.y * 100) / 100);
}

function cw_findLeader() {
  var lead = 0;
  for (var k = 0; k < cw_carArray.length; k++) {
    if (!cw_carArray[k].alive) {
      continue;
    }
    var position = cw_carArray[k].getPosition();
    if (position.x > lead) {
      leaderPosition = position;
      leaderPosition.leader = k;
    }
  }
}

function cw_newRound() {
  if (mutable_floor) {
    // GHOST DISABLED
    ghost = null;
    floorseed = Math.seedrandom();

    world = new b2World(gravity, doSleep);
    cw_createFloor();
    cw_drawMiniMap();
  } else {
    // RE-ENABLE GHOST
    ghost_reset_ghost(ghost);
  }

  cw_nextGeneration();
  camera_x = camera_y = 0;
  cw_setCameraTarget(-1);
}

function cw_startSimulation() {
  cw_runningInterval = setInterval(simulationStep, Math.round(1000 / box2dfps));
  cw_drawInterval = setInterval(cw_drawScreen, Math.round(1000 / screenfps));
}

function cw_stopSimulation() {
  clearInterval(cw_runningInterval);
  clearInterval(cw_drawInterval);
}

function cw_kill() {
  var avgspeed = (myCar.maxPosition / myCar.frames) * box2dfps;
  var position = myCar.maxPosition;
  var score = position + avgspeed;
  document.getElementById("cars").innerHTML += Math.round(position * 100) / 100 + "m + " + " " + Math.round(avgspeed * 100) / 100 + " m/s = " + Math.round(score * 100) / 100 + "pts<br />";
  ghost_compare_to_replay(replay, ghost, score);
  cw_carScores.push({
    i: current_car_index,
    v: score,
    s: avgspeed,
    x: position,
    y: myCar.maxPositiony,
    y2: myCar.minPositiony
  });
  current_car_index++;
  cw_killCar();
  if (current_car_index >= generationSize) {
    cw_nextGeneration();
    current_car_index = 0;
  }
  myCar = cw_createNextCar();
  last_drawn_tile = 0;
}

function cw_resetPopulation() {
  document.getElementById("generation").innerHTML = "";
  document.getElementById("cars").innerHTML = "";
  document.getElementById("topscores").innerHTML = "";
  cw_clearGraphics();
  cw_carArray = new Array();
  cw_carGeneration = new Array();
  cw_carScores = new Array();
  cw_topScores = new Array();
  cw_graphTop = new Array();
  cw_graphElite = new Array();
  cw_graphAverage = new Array();
  lastmax = 0;
  lastaverage = 0;
  lasteliteaverage = 0;
  swapPoint1 = 0;
  swapPoint2 = 0;
  cw_generationZero();
}

function cw_resetWorld() {
  doDraw = true;
  cw_stopSimulation();
  for (b = world.m_bodyList; b; b = b.m_next) {
    world.DestroyBody(b);
  }
  cw_floorTiles = new Array();
  floorseed = document.getElementById("newseed").value;
  Math.seedrandom(floorseed);
  cw_createFloor();
  cw_drawMiniMap();
  Math.seedrandom();
  cw_resetPopulation();
  cw_startSimulation();
}

function cw_confirmResetWorld() {
  if (confirm('Really reset world?')) {
    cw_resetWorld();
  } else {
    return false;
  }
}

// ghost replay stuff

function cw_pauseSimulation() {
  cw_paused = true;
  clearInterval(cw_runningInterval);
  clearInterval(cw_drawInterval);
  old_last_drawn_tile = last_drawn_tile;
  last_drawn_tile = 0;
  ghost_pause(ghost);
}

function cw_resumeSimulation() {
  cw_paused = false;
  ghost_resume(ghost);
  last_drawn_tile = old_last_drawn_tile;
  cw_runningInterval = setInterval(simulationStep, Math.round(1000/box2dfps));
  cw_drawInterval = setInterval(cw_drawScreen, Math.round(1000/screenfps));
}

function cw_startGhostReplay() {
  if (!doDraw) {
    toggleDisplay();
  }
  cw_pauseSimulation();
  cw_ghostReplayInterval = setInterval(cw_drawGhostReplay, Math.round(1000 / screenfps));
}

function cw_stopGhostReplay() {
  clearInterval(cw_ghostReplayInterval);
  cw_ghostReplayInterval = null;
  cw_findLeader();
  camera_x = leaderPosition.x;
  camera_y = leaderPosition.y;
  cw_resumeSimulation();
}

function cw_toggleGhostReplay(button) {
  if (cw_ghostReplayInterval === null) {
    cw_startGhostReplay();
    button.value = "Resume simulation";
  } else {
    cw_stopGhostReplay();
    button.value = "View top replay";
  }
}
// ghost replay stuff END

// initial stuff, only called once (hopefully)
function cw_init() {
  cw_initRandomUserCar();

  // clone silver dot and health bar
  var mmm  = document.getElementsByName('minimapmarker')[0];
  var hbar = document.getElementsByName('healthbar')[0];

  for (var k = 0; k < generationSize; k++) {

    // minimap markers
    var newbar = mmm.cloneNode(true);
    newbar.id = "bar" + k;
    newbar.style.paddingTop = k * 9 + "px";
    minimapholder.appendChild(newbar);

    // health bars
    var newhealth = hbar.cloneNode(true);
    newhealth.getElementsByTagName("DIV")[0].id = "health" + k;
    newhealth.car_index = k;
    document.getElementById("health").appendChild(newhealth);
  }
  mmm.parentNode.removeChild(mmm);
  hbar.parentNode.removeChild(hbar);
  floorseed = Math.seedrandom();
  world = new b2World(gravity, doSleep);
  cw_createFloor();
  cw_drawMiniMap();
  cw_generationZero();
  cw_runningInterval = setInterval(simulationStep, Math.round(1000 / box2dfps));
  cw_drawInterval    = setInterval(cw_drawScreen,  Math.round(1000 / screenfps));
}

function relMouseCoords(event) {
    var totalOffsetX = 0;
    var totalOffsetY = 0;
    var canvasX = 0;
    var canvasY = 0;
    var currentElement = this;

    do {
        totalOffsetX += currentElement.offsetLeft - currentElement.scrollLeft;
        totalOffsetY += currentElement.offsetTop - currentElement.scrollTop;
    } while (currentElement = currentElement.offsetParent);

    canvasX = event.pageX - totalOffsetX;
    canvasY = event.pageY - totalOffsetY;

    return {
      x: canvasX,
      y: canvasY
    };
}
HTMLDivElement.prototype.relMouseCoords = relMouseCoords;
minimapholder.onclick = function(event) {
  var coords = minimapholder.relMouseCoords(event);
  var closest = {
    index: 0,
    dist: Math.abs(((cw_carArray[0].getPosition().x + 6) * minimapscale) - coords.x),
    x: cw_carArray[0].getPosition().x
  };

  var maxX = 0;
  for (var i = 0; i < cw_carArray.length; i++) {
    if (!cw_carArray[i].alive) {
      continue;
    }
    var pos = cw_carArray[i].getPosition();
    var dist = Math.abs(((pos.x + 6) * minimapscale) - coords.x);
    if (dist < closest.dist) {
      closest.index = i;
      closest.dist = dist;
      closest.x = pos.x;
    }
    maxX = Math.max(pos.x, maxX);
  }

  if (closest.x === maxX) { // focus on leader again
    cw_setCameraTarget(-1);
  } else {
    cw_setCameraTarget(closest.index);
  }
}

cw_init();
