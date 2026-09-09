# MHDSingularity

This project studies ideal magnetic transport in the singular velocity fields
from the inherited OpenAI Navier–Stokes formalization. The magnetic field is
passive: no Lorentz-force backreaction or coupled MHD solution is asserted.
The inherited results and their attribution are retained below.

## Magnetic transport: completed foundation

- `NavierStokes/MagneticInduction.lean` reuses the existing spacetime field
  representation and separates solenoidality from stretching-form induction.
- `NavierStokes/MagneticTrajectory.lean` proves the material chain rule along
  a supplied Lagrangian trajectory, with endpoint continuity and interior ODEs.
- `NavierStokes/MagneticCauchy.lean` constructs the deformation operator solving
  `F(a) = I`, `F′ = Dₓu(t, γ(t)) ∘ F`, proves uniqueness, and proves
  `B(t, γ(t)) = F(t) B(a, x₀)`.

These results do not assume that `F` is a spatial derivative of a global flow.

## Research roadmap

`NavierStokes/MagneticSimilarityTrajectory.lean` now proves the constant-eta
trajectory for the natural core, using the inherited unique-root theorem:
`q(t) = (1-t)/(1-η₀²)` and `γ*(t) = q(t)^(1/2-h) η₀ e₂`.
The theorem `distinguished_trajectory_isLagrangian` applies on every finite
`[a,b]` with `b < 1`, under `SmallParameters` and `IsNaturalSolution`.
The assembled-velocity transfer theorem has an explicit path-agreement
hypothesis; that hypothesis has not yet been discharged for the final solution.

The sequence is:

1. Use the proved root `H(h, j₀, η₀) = 0` to construct a path with constant
   similarity coordinate `η(t) = η₀` and prove that it is Lagrangian.
2. Establish the region and times on which the assembled Navier–Stokes velocity
   agrees with the natural core along that path. Equality of spatial derivatives
   requires local spatial agreement, not just equality of velocity values.
3. Calculate `A_mag(t) = Dₓu_NS(t, γ*(t))` on that exact path and apply the
   existing deformation/Cauchy theorem.
4. Analyze the resulting operator ODE and derive the exact parameter-dependent
   exponent `β₀(h, j₀)`, including hypotheses on the initial magnetic direction
   and any nonzero leading coefficient.
5. Prove an asymptotic such as `B_z = C q^(-β₀) (1 + o(1))` and, if supported
   by the calculation, a quantitative estimate `β₀ = 4 + O(j₀²)` with its
   parameter regime and uniformity stated explicitly.

The exponent and magnetic amplification asymptotic are research targets, not
proved results. In particular, `β₀ = 4` is not hard-coded. Curl identities,
resistivity, global flow derivatives, and MHD backreaction are deferred.

The Lake package name remains `NavierStokesAndEuler`, consistently in
`lakefile.toml` and `lake-manifest.json`; MHDSingularity is the repository name.
No npm packages or Node build step are needed.

---

# Finite time blowup for Navier–Stokes and Euler equations

This repository contains Lean 4 formalizations of the results presented in
“Finite time blowup for Navier–Stokes” and
“Finite time blowup for the Euler equation” by OpenAI.

## Navier Stokes

For every positive viscosity, we prove two results:

- **Whole space $\mathbb{R}^3$:** There exist smooth initial data and forcing for
  which no global smooth solution with uniformly bounded kinetic energy exists.
- **Periodic torus $\mathbb{R}^3/\mathbb{Z}^3$:** There exist smooth periodic
  initial data and forcing for which no global smooth solution exists.

These are alternatives [**(C)**](https://www.claymath.org/wp-content/uploads/2022/06/navierstokes.pdf#page=2) “Breakdown of Navier–Stokes solutions on ℝ³”
and [**(D)**](https://www.claymath.org/wp-content/uploads/2022/06/navierstokes.pdf#page=2) “Breakdown of Navier–Stokes Solutions on ℝ³/ℤ³”
in the Clay Mathematics Institute’s [official problem description](https://www.claymath.org/wp-content/uploads/2022/06/navierstokes.pdf)
of the [Navier–Stokes existence and smoothness](https://www.claymath.org/millennium/navier-stokes-equation/)
[Millennium Prize Problem](https://www.claymath.org/millennium-problems/).

## Euler

We construct smooth, compactly supported, divergence-free initial velocity on
$\mathbb{R}^3$ whose solution to the unforced incompressible Euler equations
develops a singularity in finite time. The velocity’s $C^1$ norm becomes unbounded
near that time, and the time integral of the vorticity’s $L^\infty$ norm diverges.

## Building the formalizations

The project uses Lean 4.34.0-rc2, Mathlib, and Lake. With
[elan](https://github.com/leanprover/elan) installed, fetch the mathlib cache and build the formalizations with:

```sh
lake exe cache get
lake build
```

## Independent proof checking

For instructions on checking the formalizations with Comparator, see the
[ComparatorChallenges README](ComparatorChallenges/README.md).
