# MHDSingularity

This project studies ideal and resistive magnetic induction in the singular velocity fields
from the inherited OpenAI Navier–Stokes formalization. The magnetic field is
passive: no Lorentz-force backreaction or coupled MHD solution is asserted.
The inherited results and their attribution are retained below.

## Physical periodic heat interface

The existing three-dimensional periodic Gaussian operators now have a proved
semigroup law, uniform strong continuity, genuine C0-to-C1 derivative gain,
and the physical generator `eta_m * Delta`. The original Space-valued
operators are preserved; derivative-valued extensions have explicit equality
bridges. Constants remain admissible.

`PeriodicC1` is a proved complete graph of the actual derivative with norm
`max(||f||_infinity, ||Df||_infinity)`. For eta_m,tau>0, the bounded linear
`heatGain` has norm at most `1 + C_heat/sqrt(eta_m*tau)`, with one finite
constant independent of eta_m, tau, and f. The same operator commutes with
spatial differentiation, is strongly continuous on C1 through zero, and
has jointly continuous positive-time gain in the C1 norm. The time majorant
has integral `T + 2*C_heat*sqrt(T/eta_m)` on `(0,T]`.

`heat_generator_limit` proves the right generator limit in uniform norm for
supplied C2 periodic input, including eta_m=0. `heat_contDiff_two`,
`heat_hasDerivAt`, and `heat_equation` give positive-time spatial C2 and the
actual heat equation from merely continuous input. No joint C-infinity or
operator-norm continuity at time zero is claimed.

**Resistive induction existence is still open.** This checkpoint stops at the
physical heat interface. The [Paper II handoff](Paper/ResistiveMagneticInduction.md)
lists the exact Volterra spaces/kernel, remaining source estimates,
continuation, classical regularity, divergence preservation, and gluing work.
All pre-existing Lean files and theorem statements remain unchanged.

Validation: the targeted heat build and full `lake build` pass (**11,312
full-build jobs**). The new heat audit passes 213 checks, and all 358 previous
magnetic checks pass: **571 total**, using only `propext`, `Classical.choice`,
and `Quot.sound` (or no axioms). No admitted proof or axiom is added. The four
inherited challenge admissions are unchanged and are absent from these
audited dependencies.

## Periodic PDE-to-comparison: complete

`ResistiveActualComparison.lean` closes the fixed-slab comparison with
Paper I's **actual constructed periodic ideal field**. For each fixed
`a < b < 1`, it proves finite, diffusivity-independent `L,D >= 0` bounding
`||D_x u||` and `||Delta Bideal||`. Every supplied periodic resistive solution
with the matching constant axial seed obeys, uniformly on `[a,b]` and space,

```
||Bres(t,x) - Bideal(t,x)|| <= eta_m * C_b,
C_b = D * sqrt((exp((2*L+1)*(b-a))-1)/(2*L+1)).
```

`Slice.comparison` proves the scalar barrier by a compact-cell maximum
argument, using derivatives only for `a<t<b` and continuity at both endpoints.
`Comparison.ideal_resistive` derives the difference PDE and squared-norm
inequality before applying it. The fields need joint continuity on the
closed slab, differentiable time slices and C2 spatial slices in its interior,
periodicity, the two PDEs, and matching initial data. Zero diffusivity and
zero Laplacian bound are included. No magnetic axial invariance is assumed.

`MagneticPeriodicSolution.Data.magnetic_laplacian_continuousOn` proves the
needed joint continuity through the initial time from the actual forward
path-space jets, inverse-Jacobian identity, and slab overlap compatibility.
`magnetic_laplacian_bound` supplies D. This does not assert joint C-infinity.
`Comparison.periodic_comparison_main` closes the NS schedule/data and chooses
one ideal field for each seed, then a constant for each slab, **before**
diffusivity and the supplied resistive field. `resistive_unique` and
`actual_resistive_unique` prove forward uniqueness in this class.

**Resistive existence remains open.** No solution family on `[a,1)` or closed
finite-gain theorem is constructed here. The physical heat interface is now
available; the source, Volterra construction, and induction-regularity
obligations remain. The ideal Laplacian bound and scalar comparison principle
are discharged. No estimate is uniform through
`t=1`, and fixed-positive-diffusivity terminal behavior is undetermined.
All prior Lean proofs are unchanged. See [the Paper II proof outline](Paper/ResistiveMagneticInduction.md)
and [the handoff](MHD_PROGRESS.md) for exact statements and validation.

Targeted builds and the full `lake build` pass (**11,300 jobs**). The new
64-check audit and all 294 previous magnetic checks pass with only
`propext`, `Classical.choice`, and `Quot.sound` (or no axioms). The four
inherited challenge warnings are unchanged. No admitted proof or axiom is
added.

## Paper II: resistive identities and conditional cutoff

Paper I's Lean results are preserved unchanged. The new `Resistive*.lean`
modules define the passive resistive PDE, prove its exact ideal limit,
propagate divergence freedom from initial data in periodic and specified
whole-space L2 classes, and prove the half-normalized energy balance with
Ohmic dissipation. The actual assembled periodic and compact velocities
are connected explicitly; magnetic resistive solutions are still supplied
hypotheses.

The full moving/dilating coordinate equation retains advection and every
stretching component, with diffusion coefficient `eta_m/ell(t)^2`.
For an assumed magnetic scale `ell=L*(1-t)^beta`, the effective ratio is
`Rm_eff=(K*L^2/eta_m)*(1-t)^(2*beta-1)`: it tends to infinity for beta<1/2,
to zero for beta>1/2, and is constant for beta=1/2.

An explicit curvature closure gives a rigorous damped axial mode with a
finite peak and terminal decay when its curvature exponent exceeds one.
The exact peak formula and rate-equality cutoff are proved. **This is not
a cutoff or survival theorem for the actual assembled resistive solution.**
Its existence, magnetic length scale, and curvature estimates remain open.
The ideal positive-volume region bound extends geometrically to a supplied
smooth resistive field, using that field's own central norm and variation
bound; no minimum magnetic length scale follows yet.

See [Paper/ResistiveMagneticInduction.md](Paper/ResistiveMagneticInduction.md)
for theorem names, exact formulas, regularity/integrability assumptions,
and the existing heat/Volterra APIs to reuse for the next construction.

Targeted and full builds pass (11,290 jobs). All 77 new and 151 prior
magnetic theorem audits use only `propext`, `Classical.choice`, and
`Quot.sound`. The four inherited challenge `sorry` warnings are unchanged.

## Compact-seed high-field regions and small initial energy

The extension after `3c5badb` preserves the completed periodic and whole-space
proofs. `MagneticSeedScaling.lean` proves seed/transport homogeneity and exact
quadratic initial-energy scaling. `MagneticCompactMain.small_initial_energy_main`
chooses one prescribed actual compact NS velocity and late reference time,
then gives, for every epsilon > 0, a constructed field with
`0 < E(a) < ofReal epsilon` and global spatial supremum diverging at t=1.

`MagneticMaterialRegion.lean` exposes the actual fixed-start flow and Jacobian
of `Data.magnetic W`, using overlap compatibility. For the distinguished
label, `constructed_label_amplification` identifies the flow with gamma and
proves `||Q(t,gamma(a))|| = M(t) = |Bz0|*((1-a)/(1-t))^K`.

For any fixed r0 > 0, the actual label derivative supremum H(t) is finite and
uniformly bounded on each fixed compact preterminal slab. With
`r(t)=r0*M(t)/(2*(M(t)+r0*H(t)))`, `constructed_quantitative_region` proves an
open positive-volume image of the label ball, field norm at least M(t)/2
there, and
`E(t) >= ofReal((c3/8)*M(t)^2*r(t)^3)`, where c3=4*pi/3.
The image-volume proof uses both the actual homeomorphism and measure
preservation. It does not require an extra integrability hypothesis.

**Terminal energy divergence remains conditional.**
`constructed_conditional_energy_divergence` assumes an eventual bound
`H(t) <= C*(1-t)^(-p)` with C>0 and `0 <= p < 5*K/3`.
The generic lower bound is a positive constant times
`(1-t)^(-2*K+3*max(p-K,0))`. The current deformation APIs prove fixed-slab
finiteness but do not discharge that terminal H-bound for the actual velocity.
This does not establish that energy stays bounded either.

These are time-dependent high-field regions, not an indefinitely amplifying
fixed material set or a stability/attraction theorem. Exact assumptions,
theorem names, and the deformation audit are in
[the region proof outline](Paper/MagneticRegions.md) and [MHD_PROGRESS](MHD_PROGRESS.md).
Targeted and full builds pass (11,277 full-build jobs); 47 new and 104 prior
magnetic theorem audits use only `propext`, `Classical.choice`, and `Quot.sound`.
The four inherited challenge `sorry` warnings are unchanged.

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

## Closed whole-space compact-seed main theorem

`MagneticCompactMain.whole_space_main` constructs one whole-space
ideal-induction field for the **existing** `actualCompactVelocity`, with no
upstream construction hypotheses. It uses the same selected schedule,
actual pressure sum, compact forcing, and retained natural profile as the
existing Navier–Stokes construction. The velocity is not modified.

`MagneticCompactSeed` constructs the curl of a translated cutoff times
`(Bz0/2) e₂ × (x-gamma(a))`. The seed is smooth, compactly supported,
divergence free, and exactly `Bz0 e₂` near `gamma(a)`.
`MagneticCompactFlow` transports this spatially varying seed by the actual
flow Jacobian, `B(t,x)=F(t,Y(t,x)) B_a(Y(t,x))`, using the existing Euler flow,
inverse, determinant, and divergence-pushforward results.

`MagneticCompactSolution` glues compatible finite slabs into **one** field
on `[a,1)`. It proves joint continuity, interior joint C1 regularity, spatial
smoothness, induction, and divergence freedom. Closed support is contained
in the flow image of the seed support; on each fixed `[a,b]`, `b<1`, it lies
in one compact tube. The global spatial supremum and **whole-space** magnetic
energy have uniform finite upper bounds on each such slab.

For nonzero `Bz0`, the main theorem reuses the exact compact-velocity
amplification law and proves pathwise and global spatial supremum-norm
divergence as `t→1-`. The subsequent region extension above adds fixed-time
energy lower bounds; terminal energy blow-up remains unproved.
Joint C-infinity regularity, arbitrary-direction amplification,
resistivity, Lorentz backreaction, and coupled MHD remain outside the result.

See [the whole-space proof outline](Paper/WholeSpacePassiveInduction.md) and
[MHD_PROGRESS.md](MHD_PROGRESS.md) for exact statements and validation.
The completed periodic Lean proofs remain unchanged. The full build passes
(11,270 jobs), and all 66 new plus 38 prior audited declarations use only
`propext`, `Classical.choice`, and `Quot.sound`; no `sorryAx` occurs in these
proof chains. Four unrelated inherited challenge warnings remain.

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

Remaining scope: no arbitrary-seed amplification transfer, resistivity, magnetic backreaction,
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
