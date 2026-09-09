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

## Natural-core amplification: proved, conditional on induction

`MagneticSimilarityTrajectory.lean` proves the distinguished natural-core
trajectory `γ(t) = q(t)^D η₀ e₂`, where `q(t) = (1-t)/d₀` and `η₀` is the
proved unique root of `H(h,j,η₀)=0`. The existing definitions are
`D=1/2-h`, `A=1/2+h`, `d₀=1-η₀²`, and `L₀=1-2hη₀²`.

`MagneticSimilarityGradient.lean` proves the exact Cartesian gradient:

```text
[ -α/2  -rot   0 ]
[  rot  -α/2   0 ]
[   0     0    α ]
```

Its strain trace is zero. `MagneticCoreAmplification.lean` proves

```text
K = (4*d₀² + 2*A*D*η₀²)/L₀
α(t) = K/(1-t)
4-K = η₀²*(15/2 - 8*h + 2*h² - 4*η₀²)/L₀
0 < 4-K < j²/2
3.9999995 < K < 4
```

These bounds use the actual `SmallParameters` assumptions:
`0<h≤1/1000` and `0<j≤1/1000`. The exponent is exact and is strictly below four.
For a supplied natural solution and ideal induction field `B`, on
`a≤t≤b<1`, `pure_axial_seed_transport` proves

```text
B(a,γ(a)) = Bz0 e₂  ⇒  B(t,γ(t)) = Bz0*((1-a)/(1-t))^K e₂.
```

`axial_component_transport` proves the same scalar formula for the axial
component of an arbitrary seed. The magnetic hypotheses are continuity along
the closed path, joint differentiability at its interior points, and the ideal
induction equation on the interior time slab. The amplification factor is
positive and is greater than one when `a<t`.

## Assembled-velocity transfer: separate minimal-condition audit

`MagneticAxisTransfer.lean` proves exact axial-line agreement of the slow Borel
base with the natural core. Differentiating that line identity supplies the
axial Jacobian column without asserting full gradient or swirl equality.
For every schedule retained by the actual candidate witness,
`selected_schedule_minimal_transfer_late_interval` proves that there is `T<1`
such that, for `T<t<1`, both the periodic and compact whole-space velocities obey

```text
γ′(t) = u_final(t,γ(t))
Dₓu_final(t,γ(t)) e₂ = (K/(1-t)) e₂.
```

This audit uses the actual parameters and a supplied natural solution with those
parameters. It checks the actual correction germs, zeroth cutoff, spatial
plateau, and time activation. See [MHD_PROGRESS.md](MHD_PROGRESS.md) for the
correction-by-correction value and axial-derivative audit.

The magnetic amplification theorems concern the natural core and are conditional
on a supplied induction solution. They do not prove global magnetic PDE
existence, divergence propagation, finite-volume amplification, or magnetic
amplification for an assembled Navier–Stokes field. No full rotating deformation
matrix is needed. Curl identities, resistivity, global flow derivatives, and
MHD backreaction remain deferred.

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
