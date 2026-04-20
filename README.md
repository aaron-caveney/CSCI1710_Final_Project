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

Population dynamics are modeled as transitions between these levels.

# Model Representation

- Wolf: represents the predator population
- wolfPop: current population level
- wolfLocation: current habitat
- Elk: represents the prey population
- elkPop: current population level
- elkLocation: current habitat
- Vegetation: represents food resources
- vegLevel: current vegetation level
- vegLocation: associated habitat
- Habitat: represents locations in the ecosystem

# State Definition

Each state in the model represents:

- The population level of wolves, elk, and vegetation
- The location of each population within habitats
- The neigboring relationships between habitats 

At each step, the system performs one of the following:

- Predation
- Elk growth
- Wolf starvation
- Vegetation degradation
- Wolf migration
- Wolf reintroduction
- No change


# Initial State

The model begins with:

- Wolves absent (Empty)
- Elk overpopulated (Overpopulated)
- Vegetation at a low level (Low)

# Main Goal

The model is used to explore whether certain ecological outcomes are possible over time.

