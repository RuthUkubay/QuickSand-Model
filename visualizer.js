function fam(expr) {
    if (!expr.empty()) return expr.tuples()[0].atoms()[0];
    return "none";
}

var current_state = 0;
const stage = new Stage();

function cs_str() {
    return `Current State: ${current_state}`;
}

function incrementState() {
    var last_state = instances.length - 1;
    if (current_state < last_state) {
        current_state += 1;
    }
    stage.render(svg);
}

function decrementState() {
    if (current_state != 0) {
        current_state -= 1;
    }
    stage.render(svg);
}

var state_label = new TextBox({
    text: () => cs_str(),
    coords: { x: 300, y: 510 },
    fontSize: 20,
    fontWeight: "Bold",
    color: "black",
});
stage.add(state_label);

var prev_button = new TextBox({
    text: "▬",
    color: "gray",
    coords: { x: 225, y: 550 },
    fontSize: 200,
    events: [
        {
            event: "click",
            callback: function (ele, ev, d) {
                decrementState();
            },
        },
    ],
});
stage.add(prev_button);

var prev_button_label = new TextBox({
    text: "Previous State",
    coords: { x: 225, y: 570 },
    fontSize: 15,
    fontWeight: "Bold",
    color: "white",
    events: [
        {
            event: "click",
            callback: function (ele, ev, d) {
                decrementState();
            },
        },
    ],
});
stage.add(prev_button_label);

var next_button = new TextBox({
    text: "▬",
    color: "gray",
    coords: { x: 375, y: 550 },
    fontSize: 200,
    events: [
        {
            event: "click",
            callback: function (ele, ev, d) {
                incrementState();
            },
        },
    ],
});
stage.add(next_button);

var next_button_label = new TextBox({
    text: "Next State",
    coords: { x: 375, y: 570 },
    fontSize: 15,
    fontWeight: "Bold",
    color: "white",
    events: [
        {
            event: "click",
            callback: function (ele, ev, d) {
                incrementState();
            },
        },
    ],
});
stage.add(next_button_label);

function proclet_color(proclet_name) {
    var proclet = instances[current_state].atom(proclet_name);
    var memory = proclet_name.substring(0, 3) == "Mem";
    if (memory) {
        return "cornflowerblue";
    } else {
        var state = proclet.runState.toString()
        if (state == "Not_Yet_Run0") {
            return "red"
        }
        else if (state == "Running0") {
            return "yellow"
        }
        else {
            return "green"
        }
    }
}

const machines = Machine.atoms().map((ltup) => fam(ltup));

let machineWidth = 240;
let machineHeight = 160;
let procletWidth = 30;
let procletHeight = 20;
let spacing = 20;

machines.forEach((machine, i) => {
    // Draw the machine rectangle
    let machineRect = new Rectangle({
        coords: { x: 50, y: 50 + i * (machineHeight + spacing) },
        width: machineWidth,
        height: machineHeight,
        color: "lightgray",
        borderColor: "black",
        borderWidth: 2,
        label: `Machine ${i}`
    });
    stage.add(machineRect);

    // Draw the proclets inside the machine
    var proclets = machine.proclets.tuples().map((ltup) => fam(ltup));
    proclets.forEach((proclet, j) => {
        var proclet_name = proclet.toString().replace("[", "");
        let procletRect = new Rectangle({
            coords: {
                x: 60 + (j % 3) * (procletWidth + 5),
                y: 60 + i * (machineHeight + spacing) + Math.floor(j / 3) * (procletHeight + 5)
            },
            width: procletWidth,
            height: procletHeight,
            color: () => proclet_color(proclet_name),
            borderColor: "black",
            borderWidth: 2,
            label: proclet_name.substring(proclet_name.length - 1)
        });
        stage.add(procletRect);
    });
});

stage.render(svg);