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
}

function decrementState() {
    if (current_state != 0) {
        current_state -= 1;
    }
}

var state_label = new TextBox({
    text: () => cs_str(),
    coords: { x: 300, y: 570 },
    fontSize: 20,
    fontWeight: "Bold",
    color: "black",
});
stage.add(state_label);

var prev_button = new TextBox({
    text: "▬",
    color: "gray",
    coords: { x: 225, y: 600 },
    fontSize: 200,
    events: [
        {
            event: "click",
            callback: function (ele, ev, d) {
                decrementState();
                render();
            },
        },
    ],
});
stage.add(prev_button);

var prev_button_label = new TextBox({
    text: "Previous State",
    coords: { x: 225, y: 620 },
    fontSize: 15,
    fontWeight: "Bold",
    color: "white",
    events: [
        {
            event: "click",
            callback: function (ele, ev, d) {
                decrementState();
                render();
            },
        },
    ],
});
stage.add(prev_button_label);

var next_button = new TextBox({
    text: "▬",
    color: "gray",
    coords: { x: 375, y: 600 },
    fontSize: 200,
    events: [
        {
            event: "click",
            callback: function (ele, ev, d) {
                incrementState();
                render();
            },
        },
    ],
});
stage.add(next_button);

var next_button_label = new TextBox({
    text: "Next State",
    coords: { x: 375, y: 620 },
    fontSize: 15,
    fontWeight: "Bold",
    color: "white",
    events: [
        {
            event: "click",
            callback: function (ele, ev, d) {
                incrementState();
                render();
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

function render() {
    const machines = Machine.atoms().map((ltup) => fam(ltup));
    var placed_proclets = [];
    stage.elements = [];

    let machineWidth = 220;
    let machineHeight = 140;
    let procletWidth = 30;
    let procletHeight = 20;
    let spacing = 20;

    machines.forEach((machine, i) => {
        // Draw the machine rectangle
        let machineRect = new Rectangle({
            coords: {
                x: 50,
                y: 70 + i * (machineHeight + spacing)
            },
            width: machineWidth,
            height: machineHeight,
            color: "lightgray",
            borderColor: "black",
            borderWidth: 2,
            label: `Machine ${i}`
        });
        stage.add(machineRect);

        // Draw the proclets inside the machine
        var mach_name = machine.toString().replace("[", "");
        var mach_instance = instances[current_state].atom(mach_name);
        var mach_proclets = mach_instance.proclets.tuples().map((ltup) => fam(ltup));
        var mach_proc_array = [];

        mach_proclets.forEach((proclet, j) => {
            var proclet_name = proclet.toString().replace("[", "");
            placed_proclets.push(proclet_name);
            let procletRect = new Rectangle({
                coords: {
                    x: 60 + (j % 3) * (procletWidth + 5),
                    y: 80 + i * (machineHeight + spacing) + Math.floor(j / 3) * (procletHeight + 5)
                },
                width: procletWidth,
                height: procletHeight,
                color: () => proclet_color(proclet_name),
                borderColor: "black",
                borderWidth: 2,
                label: proclet_name.substring(proclet_name.length - 1)
            });
            stage.add(procletRect);
            mach_proc_array.push(proclet_name);
        });

    });

    polypoints = [
        { x: 95 + machineWidth, y: 30 },
        { x: 95 + machineWidth, y: 540 }
    ]

    let line = new Line({
        points: polypoints,
        color: 'black',
        width: 2,
        arrow: false,
        style: "dotted"
    });
    stage.add(line)


    stage.add(new TextBox({
        text: 'Machines & Scheduled Proclets:',
        coords: { x: 170, y: 30 },
        color: 'black',
        fontSize: 16
    }))

    stage.add(new TextBox({
        text: 'All Proclets:',
        coords: { x: 160 + machineWidth, y: 30 },
        color: 'black',
        fontSize: 16
    }))

    // draw all compute proclets
    const comp_proclets = Compute_Proclet.atoms().map((ltup) => fam(ltup));
    comp_proclets.forEach((proclet, j) => {
        var proclet_name = proclet.toString().replace("[", "");
        let procletRect = new Rectangle({
            coords: {
                x: 120 + machineWidth + (j % 3) * (procletWidth + 5),
                y: 70 + Math.floor(j / 3) * (procletHeight + 5)
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


    // draw all memory proclets
    const mem_proclets = Memory_Proclet.atoms().map((ltup) => fam(ltup));
    mem_proclets.forEach((proclet, j) => {
        var proclet_name = proclet.toString().replace("[", "");
        let procletRect = new Rectangle({
            coords: {
                x: 120 + machineWidth + (j % 3) * (procletWidth + 5),
                y: 110 + Math.floor(j / 3) * (procletHeight + 5)
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

    stage.render(svg);

}

render();