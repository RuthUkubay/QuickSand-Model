# QuickSand-Model

## Project Overview:

The utilization of resources such as memory and CPU in cloud computing centers is low. This is because while applications utilize resources at fluctuating rates throughout their runtimes, clouds only offer resources at fixed rates. Quicksand is a system that attempts to remedy this by using granular computing and disaggregation of resources to harness stranded datacenter resources. In this system, applications are split into “resource proclets”, a unit of execution using only one resource (CPU, memory, etc.) which can migrate across servers quickly due to its small size. The reasoning is that these small execution units can help fill in gaps of available resources which may only be available for small amounts of time. In this project, we used temporal forge to model the scheduling of these “resource proclets” across servers over time.

## Design Choices:

Model: What tradeoffs did you make in choosing your representation? What else did you try that didn’t work as well? What assumptions did you make about scope? What are the limits of your model?

One significant design choice or model made was our lack of representation of hybrid proclets. Hybrid proclets are proclets that utilize both compute and memory, yet are still small enough that they are not costly to move across servers to fill in gaps in resource utilization. While these are utilized in the actual Quicksand system for certain applications (not all), we found attempting to include them in our model to be extremely complicated, and while we hoped to have time at the end to include them, we were unable to do so. Including these would be an interesting challenge to attempt if further work is done on this project, and would help to provide a more full picture of the actual scheduler. In the meantime, our scheduler is able to accurately represent and schedule both compute and memory proclets, and the relationships between them. One important challenge if disaggregated systems is that compute resources often need to access information stored in memory resources to run their applications. For this reason, inside of the Compute_Proclet and Memory_Proclet sigs, we have variables that store a set of the opposite type of proclet they interact with. For compute proclets, this would be the set of memory proclets they must access information from, and for memory proclets this is the set of compute proclets that access information from them. This is important because when a compute proclet is running, any memory proclets that it accesses need to be placed on a machine. Our model is able to represent these relationships and ensure that when a compute proclet is scheduled, any of its corresponding memory proclets are also scheduled.

Visualization: 

We created a custom visualizer for our model which is located in visualizer.js. The visualizer consists of a view of the machines available, and all of the proclets available. The proclets are color coded such that all memory proclets are blue, and compute proclets are either red, yellow, or green depending on their runState. All compute proclets that have not yet run will be red, those that are running will be yellow, and the ones that have finished execution will be green. When compute proclets are scheduled on a machine and begin running, not only will they turn yellow, they will also appear inside of the visible machine to show which machine they have been scheduled on. This is also the case for when memory proclets are placed on machines. The visualizer provides you with next and previous state buttons, which, similar to the numbered state buttons in the default visualizer, allow you to toggle between different temporal states. As you move between states you should see the proclets go from all not being scheduled, to all being scheduled and the compute proclets running, to once again all not being scheduled. If you would like to see more details on resource consumption within the machines, you will have to look at the default visualizer, but showing this in our visualizer would be interesting future work for this project.

Example Visualization:
![QuickSank](<Final Project Plan.jpg>)


### Properties:

In our QuickSand scheduler, we were able to formally verify several properties about correctness and reliability of resource management over time. These include resource safety (machines never allocate more compute or memory than they have), proclet placement consistency( proclets are always placed on machines that recognize them), and bidirectional linkage between compute and memory proclet. We also proved liveness property such that every compute proclet that is eligible to run will eventually be scheduled and reach Finished state, provided enough resources. Additionally we validated resource conservation, ensuring that machine resources are properly tracked and accounted for across transitions. These formal guarantees give us confidence in the correctness of the scheduler’s behaviour.  


### Signatures:
Machine: represents a computational resource node with total and free memory/compute capacity. It also tracks its proclets
Proclet: represents a lightweight process that can be assigned to a machine. 
Compute_Proclet: Requires compute and memory resources to run. Has a runtime behavior defined by starttime, runtime, runState, stepsRunning, and stepsBeforeRun.
Memory_Proclet: Stores data needed by compute proclets. Has a memory cost and a bidirectional relationship with compute proclets.
     -    Run State: represents the current state of a compute proclet. Not_Yet_Run, Running or Finished
  

### Predicates:

validResources: Ensures machines have non-negative, correctly bounded memory and compute availability.

validProcletLocation: Maintains consistency between a proclet’s location and a machine’s proclets set.

resourcesMatchUsage: Ensures the resources used by assigned proclets match the machine’s tracked free resources.

validProcletRelationships: Maintains consistent many-to-many relationships between memory and compute proclets.

validStateTimeRelationships: Enforces consistency between proclet run state and time-related variables.

validState: A combined invariant capturing all valid configuration checks.

init: Defines a valid starting configuration for machines and proclets, with all resources available and no assignments.

final: Represents a terminal state where all compute proclets have finished, and all are unassigned.

canSchedule[cp]: Helper to check whether a compute proclet and its required memory proclets can be placed on machines given available resources.

procletStateEvolves: Encodes the transition behavior of compute proclets through their lifecycle (Not_Yet_Run → Running → Finished).

updateInternalVariables: Advances internal counters like stepsBeforeRun and stepsRunning based on proclet state.

traces: The main system behavior predicate: starts from init, follows valid transitions, maintains invariants, and eventually reaches final

## Testing:
### Philosophy
Our testing strategy focused on heavily verifying state invariants and initial/final predicates to ensure the model behaves as expected. This approach was important because we had a monolithic transition predicate that made individual transitions difficult to test. Additionally, state invariants provided a strong foundation to catch errors early which helped avoid cascading issues in more complex model behaviors

### Test Organization
validResources validates basic resource constraints
validProcletLocation ensures proper bidirectional relationships between proclets and machines
resourcesMatchUsage validates correct resource accounting 
validProcletRelationships validates bidirectional relationships between compute and memory proclets
validStateTimeRelationships verifies proper state transitions for compute proclets
validState combines all previous state invariant predicates
Init and Final verify proper initial and termination conditions
Traces are our set of temporal property tests

### Key Testing Patterns
Boundary testing: We extensively tested edge cases (zero values, negative values, exact boundaries…)
Resource accounting: All resource allocation and release operations are checked
Bidirectional relationship verification: All relationships are checked in both directions
Temporal Properties: System behavior is validate over complete traces

## Reflection:

We were able to successfully model our system and verify the key properties identified in our foundational and target goals. These included correctness properties around resource usage, proclet scheduling, and state transitions, all of which were formalized and proven.  

However, we did not reach our stretch goals. One of these was modeling the migration of proclets between machines, which we initially thought might be feasible. Upon deeper consideration, we realized that introducing migration would require significant changes to the way we model proclet evolution by adding context around location over time. This would increase complexity in both the state transitions and the resource accounting, which we decided to defer in order to focus on property validation and visualization, which were higher priority.

### Collaborators:

Thank you to Sarah Ridley, our mentor TA, for the help! Significant parts of the visualization were based on the visualizer from her final project which she provided us with as an example.


