# CSCI1710_Final_Project


# Authors:
Aaron Caveney, Matias Gersberg, Griff Taylor

## Overview

This project models predator reintroduction in an ecosystem using Temporal Forge. Inspired by real-world cases such as wolf reintroduction in Yellowstone, the goal is to explore how interactions between predators, prey, and vegetation evolve over time and lead to outcomes such as coexistence, extinction, or ecosystem imbalance.

Rather than using exact numeric populations, this model represents population sizes using qualitative levels, allowing us to study ecosystem dynamics without relying on arithmetic.

# Core Modeling Idea

Populations are not represented as integers. Each species is given a level:
- Empty
- Low
- Medium
- High
- Overpopulated

Population dynamics are modeled as transitions between these levels. Population sizes are implemented as vars of a Habitat sig so multiple habitats can be easily generated (we use 2) - this was a fix to an issue we ran into when population levels were sigs. One tradeoff with this representation of population size is that it is not hyper-accurate. The benefit, however, is simplicity in traces. Higher population levels leads to a dramatic increase in runtime and would lead the model to be slow. The population size’s simplicity is also a benefit, as it allows the observer to easily understand the actions. 

## Assumptions
- Population is represented as discrete qualitative tiers rather than exact counts. 
  This means a "Low" wolf population of 3 theoretically behaves identically to one of 8.
- Only one transition fires per habitat per step. In reality, predation and vegetation 
  degradation could occur simultaneously.
- Habitats are symmetric and there is no notion of habitat quality beyond population levels.
- Adjacent habitats are bidirectional. Migration in one direction implies 
  migration is possible in the other.

## Limitations
- With only 2 habitats and 5 population tiers, the state space is small. Real ecosystems 
  have far more spatial complexity. We were limited by the trace counts of Forge
- The model has no notion of time beyond trace steps and there is no seasonality, no 
  multi-year dynamics, and no distinction between a step taking a day vs. a decade.
- Vegetation is treated as a single undifferentiated resource. In reality, willows, grasses, 
  and shrubs respond differently to elk grazing and wolf presence.
- The model cannot distinguish between a population crashing due to predation vs. starvation 
  vs. dispersal  only the level change is visible and the rest has to be determined by the runner.


# Running the Model

To run the model, run the desired model as you would normally run a forge file. This can be done by either pressing the green play button in the top right corner of the IDE or by executing this command in the terminal: racket desired_file.frg.

To use the custom visualizer, follow these steps after running PROJECT_WORKING.FRG

1: Run the racket file
2: run the default visualizer creating a trace
3: press the script button in the top right of the visualizer
4: Make sure <svg> is selected and then copy & paste the visualizer script into the script section
5: Press run, and you should see the visualization of the trace
6: to move between states, the light grey button decreases the state, and the dark grey button increases the state

# Model Representation

- Habitat: represents a location in the ecosystem
    - wolfPop: current wolf population level in this habitat
    - wolfLocation: implicit (wolves belong to the habitat)
    - elkPop: current elk population level in this habitat  
    - elkLocation: implicit (elk belong to the habitat)
    - vegLevel: current vegetation level in this habitat
    - vegLocation: implicit (vegetation belongs to the habitat)
- PopLevel: discrete population tier (Empty, Low, Medium, High, Overpopulated)
- Event: records which transition fired last step

## State Definition

Each state represents the population level of wolves, elk, and vegetation within each habitat, the neighboring relationships between habitats, and the last ecological event that occurred.

## Transitions
At each step, the system performs one of the following:

- Wolf Predation: wolves reduce elk population and grow
- Elk Growth: elk pop grow when wolves are absent and vegetation exists
- Elk Reproduction: elk reproduce further when vegetation is abundant
- Elk Dispersal: overpopulated elk migrate to an adjacent habitat when food is scarce
- Elk Degrades Vegetation: overpopulated elk degrade local vegetation
- Vegetation Recovery: vegetation grows back when elk pressure is low
- Wolf Starvation: wolves decline when elk are absent
- Wolf Migration: wolves move to an adjacent habitat when prey is scarce
- Wolf Reintroduction: wolves introduced at Low population, fires at most once
- No Change: system holds current state



## Initial State

The model begins with:

- Wolves absent (Empty)
- Elk overpopulated (Overpopulated)
- Vegetation at a medium level (Medium) 
This mimics the real initial state of Yellowstone, and can be changed according to what the modeler wants to get out of the demonstration.


# Learning

We use the model to determine which ecological outcomes are reachable and what sequence of events leads to them. Unlike a Python simulation, Forge searches all possible traces simultaneously rather than one at a time, leading to faster runtime and a more exhaustive result.

# Goals

## Core Goals
- Build a temporal model with predators, prey, and vegetation across multiple habitats
- Represent ecological interactions including predation, growth, starvation, and vegetation dynamics
- Verify that outcomes such as coexistence, collapse, and overpopulation are reachable and have valid traces
- Create a custom Sterling visualizer showing population levels and last event per habitat for ease of understanding

## Closely Related Goals
- Add cross-habitat dynamics including wolf migration and elk dispersal
- Model vegetation as an active participant (recovery, degradation) rather than a passive resource
- Compare ecosystem outcomes across different starting configurations
- Extend the base model with hysteresis. Model how environment degradation can trap the ecosystem in an alternate stable state even after wolf reintroduction

## Unrelated Goals (Not Completed)
- Include real-life population numbers via SMT solving
- Model complex animal behaviors such as hibernation or seasonal predation patterns
- Include additional species beyond wolves, elk, and vegetation 
- More quantitatively compare habitat structures for reintroduction success rates

## How our goals changed over time

Initially, our goal was to model a habitat with different animal counts and follow along with the populations in a numerical sense. With the limitations in Forge and its limited ability to handle numbers, this quickly became out of scope, and we had to change the idea of how we would handle these things. This led us to use generic categories for the model, such as low population or high population instead of exact counts. 

## Example
Starting with wolves absent and elk overpopulated, we ask: can a stable coexistence state ever be reached? Forge either returns a concrete trace showing exactly which transitions fired in order to get there, or proves no such trace exists. Forge additionally shows not one possibility, but many, theoretically helping researchers find the most efficient method. Our model is fundamentally far more qualitative than a python model. Wildlife and nature is unpredictable and our model gives it far more wiggle room than python. 

# Project Extension
    - The extension builds on our existing base model. Inspired by a study driven from Colorado State University on hysteresis and reachable alternate stable states (cited in resource section below)

## Extension Key Idea:
Wolf reintroduction successfully limits elk population, but environment degradation prevents ecosystem to fully returning
Beaver-willow relationship breaks with deep water table (caused by overgrazing elk). Even though wolves limited elk population, the environment became stuck in an alternative stable state (stuck in degradation). No beavers to restore water level

## Extension Implementation
Added degradation (in the form of stream incision) and waterTableDepth
Modeled loop between willows and beavers (beavers build dams to maintain water table level, allows willows to grow, willows are beavers’ source of food
Recovery occurs w/ medium elk population and shallow water, but needs zero elk if water is deep

# Scenarios (run model through normal visualizer)
Scenario 1: represents the baseline trophic cascade. Shows what should happen with predator-prey dynamics
Scenario 2: represents a hysteresis trap, which demonstrates the alternative stable state, which proves wolf reintroduction alone cannot restore the ecosystem
Scenario 3: Demonstrates the different fates of the two habitats. Reflects real-world recovery where ecosystem engineering is necessary for different geographical habitats. Not all habitats respond the same way to predator reintroduction. 

# Project Extension Conclusion
The scenarios above show that predator reintroduction is necessary, but not sufficient for restoring (specifically Yellowstone’s) ecosystem. Addressing variables that have slowly changed over time is important (hydrology, degradation), can be overlooked and add much more variance to different habitats. Interestingly, the model also reflects reachability in state space. Adding the new variables creates multiple stable attractors, and the hysteresis trap modeled in scenario two shows that once entered, the healthy ecosystem becomes unreachable without external intervention (similar to path dependence in dynamic systems). 

# Understanding the Results

By looking at the two habitats side by side on the custom visualizer you can follow along with how the population is doing by watching what happens in each state. At any given state, the size of the population in both habitats is displayed along with the transition phase that took place in order to achieve that. On the right hand side of the habitats, there is a legend that shares what different colors stand for. Depending on the run that is taking place, the model will either run until it has reached a steady state of mediums across the board or until the wolves have killed off all the available elk.

# What We Learned

Modeling this ecosystem in Forge revealed several findings:

- Coexistence is reachable but not guaranteed. From the initial state, a specific sequence 
  of transitions must occur and wolf reintroduction alone is not sufficient if vegetation has 
  already collapsed before the wolves arrive.

- Complete habitat collapse is impossible (all go to empty) with our current model. They run UNSATs. This is likely because we do not have lifespan limits on our animals. For example, if only Elk remain, the ecosystem is as good as dead as the Elk realistically would not be able to survive without vegetation.

- Elk dispersal plays a larger role than expected. Without inter-habitat movement, one 
  habitat collapses while the other overpopulates. Dispersal is what allows pressure to 
  redistribute and create conditions for recovery. Static habitats revealed less realistic outcomes.

- The model confirmed the hysteresis finding from our extension and even after wolves 
  successfully limit elk, the ecosystem can get stuck in a degraded state if the water 
  table is already too deep. Recovery requires additional conditions beyond just predator 
  presence.

- doNothing is necessary. Without a nothing transition, many states became deadlocked 
  because no single transition is enabled, making valid traces impossible to find. This 
  was a modeling insight rather than an ecological one.

The biggest takeaway is that Forge is uniquely suited to this kind of question. A Python 
simulation would tell you what happens in one scenario while Forge tells you what is possible 
across all scenarios simultaneously, which is a fundamentally different and more powerful 
kind of answer.

## TESTING
Testing explanations can be found above each test in test_working_version.frg. Generally used positive and negative examples to test each part of our code.

# Collaboration

- No other group/student collaboration

- AI Use:  We used AI to help with the custom visualizer by having it give us a template that we could manipulate for our needs and also for help with brainstorming in pseudocode/verbally how to approach our reach goal modeling.


