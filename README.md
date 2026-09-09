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

## Assembled magnetic amplification: conditional theorems

`MagneticAssembledAmplification.lean` now combines that audit with the generic
magnetic transport ODE. For the same selected schedule, it chooses one proved
late threshold `T₀<1`, shared by the periodic and compact whole-space fields.
For `T₀<a≤t≤b<1`, `periodic_pure_axial_transport` and
`compact_pure_axial_transport` prove

```text
B(a,γ(a)) = Bz0 e₂  ⇒  B(t,γ(t)) = Bz0*((1-a)/(1-t))^K e₂.
```

Each theorem assumes ideal induction for its **assembled velocity**, path
continuity on `[a,b]`, and joint differentiability at interior path points.
Jacobian continuity and the two minimal transfer conditions are proved from
the actual construction. The actual budget, geometric threshold, schedule,
and natural-solution parameters are retained. Both fields use viscosity-one
physical time with singular time `1`; neither needs a different time formula.

`periodic_magnetic_norm_tendsto_atTop` and
`compact_magnetic_norm_tendsto_atTop` prove `‖B(t,γ(t))‖ → ∞` as `t→1-` for
`Bz0≠0`. They require **one fixed induction field on the entire interval
`[a,1)`**, with path continuity and interior joint differentiability. They do
not choose new magnetic fields on successive finite intervals. Periodicity of
`B` is not needed for the pathwise theorem. The periodic existence
construction below now supplies it.

The generic `pure_axial_follows_scalar_ode` proves invariance of the axial line
and its scalar ODE for any prescribed axial-column coefficient. No
arbitrary-seed component formula is transferred to either assembled field:
that would require an axial **row** identity, which is not proved here.

## Closed periodic Navier–Stokes and magnetic main theorem

`MagneticPeriodicMain.periodic_main` has **no upstream construction
hypotheses**. It instantiates `ActualCandidateAssembly.selected_witness` and
uses the natural solution already retained in
`ActualPrimary.nominal.axis.natural.profile.family.natural`, preserving its
exact parameters. The same schedule supplies the actual periodic velocity,
its actual pressure sum, and the forcing with `CandidateProperties`, global
forcing smoothness, and `CandidateConsequences.Consequences`.

The theorem chooses that prescribed viscosity-one velocity and a time
`0<a<1` before the magnetic seed. For every scalar seed `Bz0`, it constructs
one periodic divergence-free classical induction field on `[a,1)` and proves
its spatial smoothness and exact distinguished-trajectory amplification.
For `Bz0≠0`, both the pathwise norm and the **global spatial supremum norm**
diverge as `t→1-`. The latter is the uniform norm defined by a supremum,
not an essential supremum.

`MagneticPeriodicNorms.slab_norm_energy_bound` gives uniform finite spatial
supremum and cell-energy bounds on every fixed `[a,b]`, `b<1`. Cell energy is
`(1/2) integral_cell |B|²`, represented by a nonnegative extended Lebesgue
integral and proved finite. These bounds may depend on b; no magnetic-energy
blow-up or finite-volume energy-growth claim follows.

`MagneticPeriodicMain.arbitrarily_small_seed` keeps the same prescribed
velocity and reference time and constructs a seed `0<Bz0<epsilon` for each
`epsilon>0`, with global supremum-norm divergence. No Lorentz backreaction
or resistivity is introduced. Joint regularity remains C1 in the interior;
all spatial orders are proved separately.

See [the theorem and proof outline](Paper/PeriodicPassiveInduction.md) and
[MHD_PROGRESS.md](MHD_PROGRESS.md) for the exact statements, scope, and
validation. The full build passes (11,265 jobs); the nine new and 29 prior
axiom audits use only `propext`, `Classical.choice`, and `Quot.sound`.
Four unrelated inherited challenge warnings remain. No novelty or
publication-readiness claim is made.

## Constructed periodic ideal-induction solution

`MagneticPeriodicCoefficient.lean` adapts the actual selected periodic velocity
to `SmoothTimeField`, using the compact periodic cell to bound every spatial
jet on each finite slab. It discharges smoothness, periodicity, and
incompressibility from the actual construction. Bounds may depend on `b<1`.

`MagneticPeriodicFlow.actual_finite_slab` constructs a field on `[a,b]`,
`a<b<1`, with constant seed `Bz0 e₂`. The fixed-start flow `Phi` and its inverse
`Y` come from the existing bounded-flow API; `F` is defined as the actual
spatial derivative of `Phi`. The field is
`B(t,x)=Bz0 • (F(t,Y(t,x)) e₂)`. It is jointly continuous on the slab,
jointly C1 at interior spacetime points, and spatially smooth at each slab
time. The variational ODE proves stretching-form induction. Incompressibility
gives `det F=1`; the existing Hessian-symmetry/determinant argument proves
magnetic divergence freedom. No joint C-infinity claim is made.

`MagneticPeriodicCompatibility.lean` proves flow, inverse, Jacobian, and
magnetic-field agreement on overlaps with the same initial time.
`MagneticPeriodicSolution.exists_actual_solution` glues an increasing cofinal
family of finite slabs into **one** periodic, divergence-free classical field
on `[a,1)`, for every `a<1` and constant axial seed.

`MagneticPeriodicSolution.exists_actual_amplifying_solution` constructs that
one field and derives both the exact power law and pathwise norm divergence
for `lateStart<a<1` and `Bz0≠0`. It retains the actual selected schedule and
natural-solution parameters. Induction, continuity, differentiability, and
initial data are conclusions of construction, not assumed properties of `B`.
The physical-time formula remains `((1-a)/(1-t))^K`.

Remaining scope: no whole-space compact-seed existence construction,
arbitrary-seed amplification transfer, resistivity, magnetic backreaction,
finite-volume amplification, or magnetic-energy/coupled-MHD blow-up theorem.
Validation: the full build passes (11,263 jobs); all 29 declarations in
`scripts/audit_magnetic_periodic.lean` use only `propext`, `Classical.choice`,
and `Quot.sound`. The build retains four unrelated inherited challenge
`sorry` warnings. See [MHD_PROGRESS.md](MHD_PROGRESS.md) for exact statements,
assumptions, and audit details.

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
