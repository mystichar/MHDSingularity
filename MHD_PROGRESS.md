# MHDSingularity handoff: classical periodic resistive fields

## Current checkpoint after 6a9a5f0

The same actual mild path is now classical for every **constant vector
seed**, including the axial seed used by Paper I. One compatible field on
`[a,1)` is constructed for each positive diffusivity, with divergence freedom
and the actual fixed-slab comparison. The existing finite-gain argument is
instantiated, including a closed theorem tied to the compatible NS witness.

The requested arbitrary-`PeriodicC1` positive-time C2 upgrade remains
unproved. This is an explicit general-data regularity gap, not a hypothesis
in the constant-seed classical/finite-gain theorems. All previous Lean files
and theorem statements are unchanged. The history below records earlier
states; its outstanding-work descriptions are superseded by this section.

### Exact objects, parameters, and regularity

All new names below are under `NavierStokes.ResistiveMagnetic`, except where
qualified otherwise. The spaces are unchanged:

```
X = PeriodicGaussian.PeriodicC1,
  ||B||_X = max(sup_x ||B(x)||, sup_x ||DB(x)||_operator);
Y = PeriodicGaussian.PeriodicField, ||f||_Y = sup_x ||f(x)||;
PeriodicMild.Path T = C(Icc 0 T,X), with the uniform time norm.
```

The derivative data remain the actual derivatives (`c1_fderiv`). Space is
the physical unit-periodic R3 cover. The source is the old unprojected
`-DB[u]+Du[B]`. Heat variance remains `2*eta_m*tau`; magnetic diffusivity is
not fluid viscosity. No mean restriction or whole-cover L2 requirement is
introduced.

For `scales : Nat -> Nat`, `hsel : MagneticPeriodicMain.Selected scales`,
`a < b < 1`, `eta_m > 0`, and `c : Space`, define exactly

```
z = PeriodicMild.actualPath scales hsel a b hab hb eta_m heta (c1Constant c),
B = PeriodicMild.physicalField a (b-a) (sub_nonneg.mpr hab.le) z.
```

`PeriodicClassicalGlue.actual_constant_classical` proves:

- `ContinuousOn B (Icc a b ×ˢ univ)` and unit spatial periods on `[a,b]`;
- `DifferentiableAt Real (fun s => B(s,x)) t` for `a<t<b` and every x;
- `ContDiff Real ∞ (fun x => B(t,x))` for every `t∈[a,b]`;
- `ResistiveInductionOn eta_m (Ioo a b) (MagneticPeriodicMain.velocity scales) B`;
- `B(a,x)=c` and `spatialDivergence B t x=0` for `t∈[a,b]`.

`actual_constant_spatial_jet_continuous` proves, for every natural n,
joint continuity of the actual n-th spatial derivative of the clamped
finite-slab field, including both endpoints. The more fundamental
`PeriodicTranslation.fieldPath_contDiff` proves smoothness of
`x -> (tau -> B(a+tau,x))` into the uniform time-path space.
`magneticValues_translation_contDiff` and `laplacianPath_eq` also give the
Laplacian as a continuous periodic uniform-space path. No joint spacetime
C-infinity theorem is exported.

The velocity is exactly `actualPeriodicVelocity budget threshold geometry
scales`, with Paper I's canonical `MagneticPeriodicMain` parameters and
`ActualPrimary` profile. `MagneticPeriodicCoefficient.actualOnSlab`
discharges the smooth coefficient path and all spatial-jet continuity
requirements. Its actual incompressibility is separately instantiated.
Existence needs no late-start condition: every `a<b<1` is covered for
constant seeds. Each bound can depend on the fixed slab and diffusivity;
there is no terminal uniformity claim.

### How the existing path becomes classical

1. `LinearMild.convolutionCLM` bundles the **existing** Volterra convolution
   linearly. `mild_family_contDiffAt` proves parameter regularity by inverting
   `id - convolution ∘ coefficientMap` on the same continuous C1 path space.
   The already proved exponential weight supplies the strict norm bound.
   This is a local inverse argument, not another existence construction.
2. `PeriodicTranslation.translatePath_contDiff` proves smooth translation
   dependence of actual smooth coefficient paths. `mild_translate` proves
   covariance of the original mild equation using the **same** heat operator,
   its C1 lift, and its singular integral kernel. For a constant seed the
   translated free path is unchanged. `constant_seed_translation_contDiff`
   applies the inverse argument and cancels the weight, proving smooth
   translation dependence of the original z. `actual_constant_translation_contDiff`
   supplies `actual_mild` and the actual assembled coefficients.
3. `PeriodicTranslation.direction_apply`, `laplacianPath_eq`, and
   `magnetic_laplacianPath_eq` identify the resulting jets with actual spatial
   derivatives and the project's `spatialLaplacian`. This proves regularity
   through time zero in uniform path norms, not just separate spatial
   smoothness. It uses the smooth constant datum; it does not claim derivative
   gain for an arbitrary C1 datum.
4. `PeriodicMild.mild_value_equation` passes the same C1 mild equation to Y.
   `value_heat_restart` and `value_heat_restart_short` prove the exact restart
   identity from the old physical semigroup. `shortDuhamel_hasDerivAt_zero`
   rescales the short integral to `[0,1]`; its quotient tends to the continuous
   source F(t) in Y. The old heat generator then gives
   `value_heat_right_derivative`. No second-derivative r^(-1) integrability
   assumption, temporal Hölder assumption, or dropped advection term occurs.
5. `mild_hasDerivAt_of_laplacianPath` uses the continuous Laplacian path and
   a Banach-valued right-derivative/FTC argument. The hypotheses of this
   reusable lemma are proved for the actual constant-seed z.
   `smooth_mild_hasDerivAt` gives the **strong Y derivative**
   `z' = eta_m • laplacianEvolution z + valueSource S z` on `(0,T)`.
   `smooth_mild_physical_hasDerivAt` commutes bounded evaluation and the
   physical clock shift. `actual_constant_induction` identifies the actual
   source and exports exactly

   ```
   temporalDerivative B t x + spatialDerivative B t x (u(t,x))
     = spatialDerivative u t x (B(t,x))
       + eta_m • spatialLaplacian B t x,          a<t<b.
   ```

`mild_hasDerivWithinAt_of_laplacianPath` proves a derivative *within* `[0,T]`
at both endpoints. This supplies the forward endpoint hypothesis for the
existing `EulerSmoothPathTimeJets.jetFamily_hasDerivWithinAt`; it asserts
no two-sided derivative of the clamped field at an endpoint.

### Divergence, compatibility, and one family

`PeriodicTranslation.mild_spatial_jet_time_derivative` differentiates the
proved time integral identity in space, in continuous path spaces.
`delta_hasDerivAt` takes the trace of the first jet equation. The spatial
identity `spatial_divergence_rhs` uses smooth spatial slices to commute
divergence with the vector Laplacian and cancel the stretching/advection
cross terms when `div u=0`; it does not impose joint spacetime smoothness.
`delta_operator_zero` proves the scalar advection-diffusion equation for
the actual divergence. `constant_mild_divergence_free` applies the existing
`Slice.nonpos` to divergence and its negative. C1 path continuity supplies
continuity of divergence at the initial endpoint, where the constant seed's
divergence is zero. `actual_constant_divergence_free` discharges coefficient
incompressibility with `MagneticPeriodicCoefficient.actual_divergence`.

`PeriodicClassicalGlue.slabField` is exactly the old finite-slab physical
field. `slabField_overlap` uses `PeriodicMild.actual_overlap`.
`field` uses the cofinal endpoints/index already constructed by Paper I's
`actualData`. `field_eq_slab` proves equality at all t,x in **any** observation
slab `[a,b]`, not just one selected subsequence. The neighborhood equality
`field_eventuallyEq` transports time derivatives and the PDE; whole spatial
slice equality transports all spatial derivatives and divergence.

`family scales hsel a ha c : Real -> MagneticField` is fixed after scales,
a and c. For eta>0 it is `field ... eta heta (c1Constant c)`; for eta<=0 it is
arbitrarily zero, with no physical theorem there. `family_classical` returns
`ClassicalOn eta (velocity scales) (family ... eta) a 1 c`, recording continuity
on `[a,1)`, periods, interior time differentiability/C2, the PDE and initial
seed. `family_divergence_free` proves zero divergence for every t in `[a,1)`.
Separate spatial smoothness is exported by `field_constant_spatial_smooth`.
Different observation slabs never select different magnetic families.

### Actual comparison and the closed finite-gain corollary

`PeriodicClassicalGlue.actual_family_comparison` has only the selected
schedule, real a,Bz0, `a<1`, and `a<b<1` as data/hypotheses. With
`I=(actualData ... a ha).magnetic Bz0`, it proves

```
exists C >= 0, forall eta_m > 0, forall t in [a,b], forall x,
  ||family scales hsel a ha (Bz0 • e2) eta_m (t,x)-I(t,x)|| <= eta_m*C.
```

No resistive field, scalar barrier, coefficient bound or comparison estimate
is supplied as a hypothesis. The old `Comparison.actual_comparison_constant`
chooses C before eta_m and uses the already proved ideal Laplacian/velocity
bounds. Its sufficient value is
`D*sqrt((exp((2*L+1)*(b-a))-1)/(2*L+1))`. L,D may depend on the prescribed
velocity, seed and fixed slab, but not eta_m. The new existence weight is
not substituted for this constant.

`actual_ideal_path_norm` reuses Paper I's transport law for **that same**
actual ideal witness. `actual_family_finite_gain` assumes Bz0!=0 and
`lateStart ... naturalSolution < a < 1`, and proves

```
forall G > 1, exists t_G in (a,1), exists eta_G > 0,
  forall eta_m in (0,eta_G),
    G*abs(Bz0) <= ||family ... (Bz0 • e2) eta_m(t_G,gamma(t_G))||.
```

It is an immediate application of the existing `Comparison.family_finite_gain`:
`t_G=1-(1-a)*(2*G)^(-1/K)`, with exact ideal gain 2G, and the conservative
threshold `G*abs(Bz0)/(1+C_[a,t_G])`. The old positivity and rpow proofs are
reused. No resistive axial invariance is asserted or needed.

`periodic_classical_finite_gain` is closed: it instantiates
`ActualCandidateAssembly.selected_witness`, uses the same pressure/forcing
and `MagneticPeriodicMain.naturalSolution`, and chooses a late a with 0<a<1.
It exports `CandidateProperties`, smooth forcing, and the existing
`CandidateConsequences.Consequences` for that same viscosity-one NS velocity;
then one fixed unit axial seed and one family with classical regularity,
spatial smoothness, divergence freedom, and the displayed finite-gain
quantifiers. No new upstream compatibility or magnetic-existence assumption
remains in this closed theorem.

### Exact remaining work and scope

The requested general-data lemma is still missing: for arbitrary
`B_a : PeriodicC1`, the same `actualPath` should have C2 spatial slices for
`0<tau<T` and a continuous positive-time Laplacian path. One must also
localize the right-derivative/FTC bridge to an interior subslab: `mild_hasDerivAt_of_laplacianPath` currently takes its Laplacian
path through the supplied slab endpoints. C1 membership of z only makes
`-Dz[u]+Du[z]` a C0 source; differentiating that source again requires another
spatial derivative. The constant-seed translation proof does not provide
this smoothing theorem. A valid Hölder/cancellation or interior bootstrap
argument remains to be developed, without treating r^(-1) as integrable.
There is no placeholder declaration for this missing result.

Fixed-positive-diffusivity terminal divergence, a finite terminal maximum,
terminal decay, a magnetic length-scale exponent, eigen-curvature closure,
sharp gain/diffusivity asymptotics, useful numerical conductivity thresholds,
magnetic-energy blow-up, stability/attraction and whole-space resistive
existence remain unproved. Previously conditional curvature-mode results
remain separate. The field is passive, with no Lorentz feedback or coupled
MHD. The slab-dependent sufficient threshold is a mathematical bound, not
an engineering prediction. No bound uniform at t=1 is claimed.

### Validation and changed modules

- Incremental builds pass. The final targeted command
  `lake build NavierStokes.ResistiveActualFiniteGain` passes **9,428 jobs**.
- Full `lake build` passes **11,334 jobs**. The new modules have no warnings.
  The four inherited `ComparatorChallenges` admissions and fourteen existing
  heat-module unused-section-variable warnings are unchanged.
- `lake env lean scripts/audit_resistive_classical.lean` passes **154 checks**:
  all 128 public named declarations in the 17 new modules, plus 26 explicit
  inherited dependencies. Every check traverses its construction dependencies.
  These include the actual mild path/uniqueness, weighted contraction, actual
  coefficient path and incompressibility, heat generator, spatial/time jet
  bridge, maximum principle, actual comparison, ideal field, exponent, transfer
  theorem and compatible NS witness. All 154 use only `propext`,
  `Classical.choice`, and `Quot.sound`; none uses `sorryAx`.
- All nine previous audits pass their **687 checks**. Total: **841 checks**,
  with only those standard axioms (or no axioms in older checks).
- No previous Lean file is modified. No new `sorry`, `admit`, axiom or
  placeholder declaration is present. The staged diff passes whitespace checks.

| New module (under NavierStokes/) | Role |
| --- | --- |
| ResistivePeriodicTranslationRegularity.lean | Translation regularity in periodic coefficient path spaces |
| ResistiveMildParameter.lean | Smooth inverse of the existing linear mild residual |
| ResistivePeriodicTranslatedMild.lean | Exact translation covariance of source, heat and mild equation |
| ResistivePeriodicPathJets.lean | Actual spatial jets from uniform translation derivatives |
| ResistivePeriodicSmoothSeed.lean | Spatial smoothness of the same constant-seed actualPath |
| ResistivePeriodicMildRestart.lean | Uniform-space equation and semigroup restart |
| ResistiveMildRightDerivative.lean | Short Duhamel derivative and forward heat-generator bridge |
| ResistiveMildToPDE.lean | Strong time derivative from a continuous actual Laplacian path |
| ResistivePeriodicClassical.lean | Actual physical-time resistive PDE |
| ResistivePeriodicTimeJets.lean | Mixed spatial/time jet equations through the forward endpoint |
| ResistiveSpatialDivergence.lean | Spatial divergence of stretching/advection and diffusion |
| ResistivePeriodicSolenoidal.lean | Actual divergence's scalar transport equation |
| ResistivePeriodicDivergence.lean | Maximum-principle propagation, actual and glued fields |
| ResistivePeriodicClassicalGlue.lean | One field and equality with every finite representative |
| ResistivePeriodicClassicalResult.lean | Classical output predicate and actual constant-seed conclusions |
| ResistiveActualClassicalComparison.lean | Diffusivity-independent comparison for the constructed family |
| ResistiveActualFiniteGain.lean | Parameterized and closed actual finite-gain theorems |

Also added: `scripts/audit_resistive_classical.lean`. Updated: README,
this handoff and `Paper/ResistiveMagneticInduction.md`.

## Historical checkpoint after 106fc10: entire finite-slab mild construction

Continued the current local `main` without resetting. Five new Lean modules
construct periodic positive-diffusivity mild solutions on every fixed
preterminal slab. Every previously committed Lean file and theorem statement
is unchanged. This is an actual construction, not a supplied-solution theorem.

All namespaces below are inside `NavierStokes.ResistiveMagnetic`. Physical
space is the unit-periodic cover of Euclidean R3. The prescribed velocity is
exactly `MagneticPeriodicMain.velocity scales`, equivalently
`actualPeriodicVelocity budget threshold geometry scales`, with Paper I's
canonical budget, threshold, geometry, and `Selected scales` condition.
There is no new schedule/profile, fluid-viscosity change, or time rescaling.
Magnetic diffusivity `eta_m` remains a separate positive real parameter.

### Exact function spaces and source

`X = PeriodicGaussian.PeriodicC1` is the existing complete derivative graph,
with norm `max(||B||_infinity, ||DB||_infinity)`; its derivative is identified
by `c1_fderiv`. `Y = PeriodicGaussian.PeriodicField` is the complete continuous
periodic uniform space. Constants are included, with no mean restriction,
whole-cover L2 requirement, vector potential, or solenoidal projection.
`PeriodicMild.Path T = C(Icc 0 T, X)` has the time-supremum of the C1 norm.
`Coefficient T = C(Icc 0 T, X ->L[Real] Y)` has the uniform operator norm.

`ResistivePeriodicSource.lean` exports:

- `PeriodicSource.sourceOperator u G : X ->L[Real] Y`, with exact value
  `-(c1Derivative B)(x) (u(x)) + G(x) ((c1Value B)(x))`.
  Continuity, unit periods, additivity and scalar linearity are proved in
  the constructed periodic field and bounded-linear-map objects.
- `sourceOperator_opNorm_le`: bounds `||u||<=U`, `||G||<=L` imply
  `||sourceOperator u G||<=U+L`. `sourceOperator_lipschitz` gives the same
  global Lipschitz bound on all X. `sourceOperator_continuous` is continuity
  in operator norm, obtained from the bounded bilinear `pairing`.
- `sourceOperator_eq_source` identifies the operator with the existing
  `Comparison.source = -DB[u]+Du[B]` when G is the actual velocity derivative.
  It uses `c1_fderiv`, with no smoothness assumption beyond membership in X.
- `actualVelocityPath` and `actualSourcePath scales hsel a b hb` construct
  the actual continuous coefficient paths from
  `MagneticPeriodicCoefficient.actualOnSlab`, including its actual spatial
  derivative path. `actualVelocityPath_value`,
  `actualVelocityPath_derivative`, and `actualSourcePath_eq_source` identify
  the physical time as `a+tau`.
- `actualSourcePath_bound` proves `||S(tau) B|| <= ||S||*||B||` throughout
  `[0,b-a]`. Thus A=`||S||>=0` is finite and chosen before eta_m or B_a.
  No bound through time 1 is used.

### Whole-slab weighting and existence

`ResistiveWeightedVolterra.lean` defines
`weightedKernel K lambda r = exp(-lambda*r) • K r` and
`weightedMajorant k lambda r = exp(-lambda*r)*k(r)`.
`weightedKernel_continuous`, `weightedKernel_bound`, and
`weightedMajorant_integrable` prove the needed analytic hypotheses.
`WeightedVolterra.weightedMass_tendsto_zero` states, for every k integrable
on `(0,T]`,

```
lim_(n : Nat -> infinity) Integral_(0,T] exp(-n*r)*k(r) dr = 0.
```

Dominated convergence uses `|k|` and r>0, never a false limit at r=0.
`exists_weight` chooses n with weighted mass times A at most 1/2; it includes
A=0 without division. The original kernel is
`PeriodicGaussian.heatKernel eta_m heta`, its majorant is the completed
`1 + heatConstant/sqrt(eta_m*r)`, and its variance remains `2*eta_m*r`.

`ResistiveLinearMild.lean` proves a reusable globally linear Volterra theorem
in real normed X,Y, with X complete for existence. `LinearMild.IsMild` is
only the displayed integral equation. `duhamel_integrable` proves genuine
Bochner integrability for continuous paths. `weight` and `unweight` prove
exact equivalence with the weighted equation using source/kernel linearity,
the exponential identity, and scalar multiplication through the integral.
Clamping agrees with `tau-r` at every integration time.

`LinearMild.exists_unique_of_weight` applies the existing
`EulerVolterraConvolution.exists_mild_solution` with N=`||free||`,
R=`2*N+1`, M=`A*R`, and Lipschitz constant A. Weighted mass times A is at most
1/2. The free-path norm is at most N; both invariant-ball and strict
contraction inequalities are proved. A second estimate gives `||Z||<=2*N`,
and recovering `z(tau)=exp(n*tau) • Z(tau)` removes the weight completely.
`exists_unique` chooses n before quantifying over the free path.

`ResistivePeriodicMild.lean` instantiates every heat and completeness premise:

```
PeriodicMild.exists_mild
  (T : Real) (hT : 0 <= T) (eta_m : Real) (heta : 0 < eta_m)
  (S : Coefficient T) (B_a : PeriodicC1) :
  exists z : Path T,
    Mild T hT eta_m heta S B_a z /\
    ||z|| <= 2*exp(contractionWeight(T,hT,eta_m,heta,S)*T)*||B_a|| /\
    forall w, Mild T hT eta_m heta S B_a w -> w = z.
```

Here `Mild` is exactly, for every tau in `[0,T]`,

```
z(tau) = heatC1 eta_m tau B_a
       + integral_0^tau heatKernel eta_m heta r
           (S(projIcc(0,T,tau-r))(z(projIcc(0,T,tau-r)))) dr.
```

`mild_integrable` proves this integral is Bochner integrable in C1.
`mild_initial` gives z(0)=B_a. `solution` chooses the proved witness;
`solution_mild`, `solution_bound`, and `solution_zero` export its equation,
finite bound and zero-data behavior. `contractionWeight` has no initial-data
argument. Its size can depend on eta_m, the prescribed velocity and slab;
the resulting bound is not a diffusivity-independent comparison estimate.

### Uniqueness, physical field, and actual instantiation

`PeriodicMild.mild_unique` proves equality of **any two** continuous C1
paths satisfying the same original mild equation. No construction ball,
weight, classical PDE, time derivative, or C2 hypothesis remains. Its proof
weights arbitrary paths and uses global source linearity; the ball needed
by the inherited mild uniqueness API is chosen after those paths are given.
`recovered_unique` proves independence from any two auxiliary weights.
`mild_restrict` and `solution_restrict` restrict the unweighted equation and
identify constructed restrictions using uniqueness.

`ResistivePeriodicMildActual.lean` constructs
`actualPath scales hsel a b hab hb eta_m heta B_a`. In particular,
`PeriodicMild.actual_exists_mild` has assumptions exactly

```
scales : Nat -> Nat, hsel : MagneticPeriodicMain.Selected scales,
a b : Real, hab : a < b, hb : b < 1,
eta_m : Real, heta : 0 < eta_m, B_a : PeriodicC1.
```

It returns a mild path for `actualSourcePath scales hsel a b hb`, a jointly
continuous physical field with unit periods and spatial C1 slices, matching
initial data, and uniqueness among all paths for these same data.
`actual_axial_exists` specializes to `c1Constant (Bz0 • coordinateVector 2)`
for every real Bz0, including zero. No late-start condition is needed for
mild existence; the theorem covers every a<b<1. The compatible selected
schedule remains explicit, as permitted for this reusable theorem. No
additional upstream compatibility or magnetic-existence assumption is added.

`physicalField a T hT z` evaluates the path at clamped elapsed time t-a.
`physicalField_at_elapsed` identifies the exact slice at physical time a+tau.
`physicalField_continuous`, `physicalField_periodic`,
`physicalField_spatialC1`, `physicalField_spatialDerivative`, and
`physicalField_derivative_continuous` export the actual regularity. The field
AND its actual first spatial derivative are jointly continuous through the
closed slab. Clamping gives a continuous extension outside it, not an
induction equation outside it.

`actual_physical_mild_equation` gives the same equation after bounded spatial
evaluation, with the original physical Gaussian heat operator.
`actualSourcePath_eq_field_source` identifies its integrand with the actual
evolving field's `-DB[u]+Du[B]` at time a+tau-r. The heat operator is identity
at elapsed time zero; the singular integration kernel is zero there. Their
difference at that point does not affect the integral.
`actual_bound` supplies the bound above for the same actual path.
`actual_restrict` and `actual_overlap` prove C1-valued agreement for any two
fixed slabs with the same scales, a, eta_m and B_a, even with different weights.

### Validation of the mild checkpoint

- Incremental builds of all five new modules pass. The final target
  `lake build NavierStokes.ResistivePeriodicMildActual` passes, 9,396 jobs.
- Full `lake build` passes, 11,317 jobs. The new modules emit no warnings.
  Four inherited `ComparatorChallenges` admissions and fourteen existing
  heat-module unused-section-variable warnings remain unchanged.
- `lake env lean scripts/audit_resistive_mild.lean` passes 116 transitive
  checks: all 95 new named declarations and 21 explicit dependencies. These
  include derivative-graph completeness/identification, the physical heat
  kernel and its bounds, actualOnSlab, dominated convergence, and the existing
  Volterra fixed-point, convolution and mild uniqueness theorems.
- All eight previous audit scripts pass their 571 checks. The nine scripts
  total 687 successful checks, with only `propext`, `Classical.choice` and
  `Quot.sound`, or no axioms. No `sorryAx` occurs in audited dependencies.
- No new `sorry`, `admit`, axiom, or placeholder declaration is present.
  All previously committed Lean files are unchanged; `git diff --check` passes.

### Next task and stopping point

This checkpoint is complete at the **continuous C1-valued mild** level.
The source, weighted fixed point, entire fixed-slab bound, all-class mild
uniqueness, and restriction/overlap obligations are discharged. Short-time
subdivision or mild continuation was not needed and is not also implemented.

Still unproved for this constructed witness: interior time differentiability,
spatial C2 or higher induction regularity, the classical pointwise resistive
PDE, and forward-endpoint divergence preservation. Homogeneous heat smoothing
does not justify these properties for the Duhamel integral: its endpoint r=0
requires separate estimates. If further regularity is constructed in stronger
spaces, equality with THIS C1 path must be proved, using mild uniqueness.
Preterminal gluing is outside this run; overlap compatibility alone is not
an exported field on `[a,1)`. The classical comparison and closed finite-gain
theorem cannot yet be applied to these paths.

No result here assumes or determines an eigen-curvature closure, magnetic
length scale, fixed-positive-diffusivity terminal behavior, sharp gain law,
energy blow-up, stability, attraction, backreaction, or coupled MHD. These
finite existence bounds are not numerical conductivity thresholds.

The earlier checkpoints below are historical records. Their descriptions
of outstanding work refer to their respective commits; this section is the
current handoff.

## Historical heat checkpoint after 9618457

Continued from the clean local main at 9618457 without resetting. Every
pre-existing Lean file is preserved. Twelve new modules construct the
physical heat interface; no resistive induction solution is constructed.

All new names use `NavierStokes.ResistiveMagnetic.PeriodicGaussian`.

- `ResistivePeriodicHeatSpace`: `PeriodicValue`, physical translations,
  `periodicValueCompleteSpace`, and the definitional Space specialization
  `periodicValue_space`.
- `ResistivePeriodicHeatSemigroup`: `valueLine_eq_lineOperator`,
  `valueSpatial_eq_spatialOperator`, `spatialOperator_semigroup`,
  `spatialOperator_zero`, `heat_semigroup` (eta_m,r,s>=0), contraction and
  constant preservation, `heat_strong_continuous`, `heat_joint_continuous`,
  and the existing absolute-time bridge `heat_eq_physicalAverage`.
- `ResistivePeriodicC1`: `derivativeGraph_closed`,
  `periodicC1ValueCompleteSpace`, `c1_fderiv`, `c1_norm`, `c1Inclusion`,
  `c1Value_injective`, and constants. The exact norm is max(C0 value norm,
  C0 Frechet-derivative norm); the derivative is actual, not arbitrary data.
- `ResistivePeriodicHeatKernel`: the explicit integrable shifted-Gaussian
  envelope and `valueLine_hasDerivAt` from merely continuous input, in
  uniform norm, with the Gaussian moment divided by sqrt(variance).
- `ResistivePeriodicTranslationDerivative`: finite-dimensional continuous
  partial derivatives give a full Frechet derivative; `derivativeTranspose`
  produces the actual periodic derivative-valued field.
- `ResistivePeriodicHeatSmoothing`: `valueSpatial_hasFDerivAt`,
  `heat_fderiv_bound`, `gainVariance`, `heatGain`, `heatGain_value`, and
  `heatGain_norm_le`. The full derivative constant is
  `heatConstant = 3 * EulerGaussianCylinderHeat.gaussianAbsMoment 1`,
  independent of eta_m,tau,f; the input is only continuous.
- `ResistivePeriodicHeatC1`: differentiation commutes with the same heat
  operator (`spatialC1_derivative`, `heatC1_derivative`), and
  `heatC1_strong_continuous` includes zero for C1 input. The proof integrates
  C1 translations in the proved complete derivative graph.
- `ResistivePeriodicHeatVolterra`: positive-time/input continuity of gain
  in C1 norm, the actual zero-extended `heatKernel`, its joint continuity
  and bound, and integrability/exact mass of `kernelMajorant`:
  `T + 2*heatConstant*sqrt(T/eta_m)` for eta_m>0, T>=0 (including T=0).
- `ResistivePeriodicHeatDerivatives`: `c1OfContDiff` obtains bounded
  derivative data by physical periodic compactness;
  `c1_translation_hasDerivAt` proves strong translation differentiation by
  the fundamental theorem of calculus in uniform space.
- `ResistivePeriodicHeatLineGenerator`: the genuine directional Gaussian
  generator is half the second strong derivative, both at positive
  variance and as a right derivative at zero.
- `ResistivePeriodicHeatGenerator`: `laplacianField_eq_spatialLaplacian`,
  `variance_generator_limit`, `variance_generator_zero`,
  `heat_generator_zero`, and `heat_generator_limit`. For C2 periodic f,
  `(T_eta(tau)f-f)/tau -> eta_m*Delta f` in uniform norm as tau->0+,
  for every eta_m>=0. No bounded C0 generator is asserted.
- `ResistivePeriodicHeatEquation`: positive-time C2 smoothing by two C1
  gains, `laplacianField_heat`, `variance_generator_pos`,
  `heat_contDiff_two`, `heat_hasDerivAt`, and `heat_equation` for C0 data
  when eta_m,tau>0. The time derivative is in the uniform Banach space.

The domain is the physical unit-periodic cover of R3. No zero-mean,
whole-cover L2, periodic-vector-potential, or cylinder identification is
used. The variance is exactly `2*eta_m*tau`; fluid viscosity and the original
physical time have not been changed. The clamped negative-time extension
is used only as an extension of a continuous function, never to assert
negative-time semigroup laws. The Volterra kernel's zero extension is
separate from the actual identity heat operator at tau=0.

Actual exported regularity: strong C0 continuity through zero; positive-time
C1 target-norm continuity; strong C1 continuity at zero for C1 input;
positive-time spatial C2 slices and uniform-space time differentiability.
No joint C-infinity regularity or C0-to-C1 continuity at zero is claimed.

### Validation

- `lake build NavierStokes.ResistivePeriodicHeatEquation`: passed, 9,338 jobs;
  this target imports all twelve new modules.
- Full `lake build`: passed, 11,312 jobs.
- `lake env lean scripts/audit_resistive_heat.lean`: passed, 213 transitive
  checks covering all 199 new named declarations and fourteen explicit
  construction/analytic dependencies. This includes the two completeness
  instances, the original Gaussian operators, Gaussian convolution,
  differentiation under the integral, integration by parts, and the inspected
  Volterra existence theorem.
- All seven previous audit scripts pass their 358 checks; combined total 571.
  Every audited declaration uses only `propext`, `Classical.choice`, and
  `Quot.sound`, or no axioms. No `sorryAx` occurs in these dependencies.
- No new Lean declaration uses `sorry`, `admit`, or an added axiom. The four
  inherited `ComparatorChallenges` admissions are unchanged. The new modules'
  nonfatal linter warnings concern unused section variables only.
- All pre-existing Lean files are unchanged; `git diff --check` passes.

### Next task and exact remaining obligations

The inspected `EulerVolterraConvolution.exists_mild_solution` fits
X=PeriodicC1, Y=PeriodicField, K=`heatKernel eta_m heta`,
k=`kernelMajorant eta_m`, with its continuity, completeness, integrability,
nonnegativity and kernel bound discharged. Use the free path
`tau -> heatC1 eta_m tau B_a`, with the same constant axial seed.

Next construct `Source(tau,B) = -DB[u(a+tau)] + Du(a+tau)[B]` as an
unprojected bounded linear C1-to-C0 map. Prove its time continuity and
norm/Lipschitz bounds from `Comparison.actual_velocity_bounds` and
`MagneticPeriodicCoefficient.actualOnSlab` for the SAME selected actual
periodic NS velocity. Then instantiate the ball budget and short-time
contraction using the explicit kernel mass. Slab continuation, compatible
higher regularity, the mild-to-classical-PDE bridge, forward divergence
preservation, and restriction/gluing remain unproved. Only after that
construction can the existing actual comparison be used for a closed
finite-gain theorem. No induction existence is concealed in a new structure
or assumed heat wrapper.

See `Paper/ResistiveMagneticInduction.md` for exact formulas, assumptions,
proof routes, and the full Volterra signature. The scope still excludes
fixed-diffusivity terminal conclusions, length-scale closure, numerical
conductivity predictions, energy blow-up, backreaction, and coupled MHD.


## Completed checkpoint after 4d513f8: periodic PDE-to-comparison

The current local state was continued without resetting. Paper I and all
previous Paper II Lean files are unchanged. Five new modules close the
comparison and uniqueness package; resistive existence is deliberately not
part of this checkpoint.

1. `ResistivePeriodicMaximum.lean`, namespace `ResistiveMagnetic.Slice`:
   `comparison` assumes a<b, eta_m>=0, c>0, F0>=0, joint continuity of a
   unit-periodic scalar q on `[a,b] x R3`, differentiable time slices and C2
   spatial slices for a<t<b, the slice PDE inequality
   `q_t+Dq[u]-eta_m*Delta q <= c*q+F0`, and q(a,x)<=0. It proves
   `q(t,x)<=F0*(exp(c*(t-a))-1)/c` for every a<=t<=b and x. No bound,
   smoothness, periodicity, or incompressibility of u is needed here.
   The proof subtracts a strict epsilon time barrier after an integrating
   factor, obtains a maximum on a compact cell, lifts it to a spatial
   maximum on the cover using actual coordinate periods, and uses the time
   derivative from the left. The final endpoint follows by continuity.
2. `ResistiveSquaredNormSlices.lean`: `Slice.squared_equation` and
   `Slice.squared_inequality` use just a differentiable time slice and C2
   spatial slice. They compute the full squared-norm Laplacian, including
   the nonnegative derivative-square sum. The older joint-smooth theorems
   are preserved. `scalarTime_eq`, `scalarPartial_eq`, and
   `scalarLaplacian_eq` give explicit bridges to the joint scalar operators;
   the last states the additional joint-partial differentiability it needs.
   `Comparison.difference_equation_of_slices` subtracts the actual PDEs.
3. `ResistivePeriodicComparison.lean`: `Comparison.ideal_resistive` assumes
   both supplied fields have joint closed-slab continuity, unit periods,
   differentiable interior time slices and C2 interior spatial slices,
   their respective ideal/resistive PDEs, identical initial data, eta_m>=0,
   L,D>=0, and the displayed interior bounds on Du and Delta Bideal. It proves
   `||Bres-Bideal|| <= eta_m * Comparison.constant L D a b` everywhere on
   the closed slab. It derives the scalar barrier; neither the barrier nor
   the error bound is a hypothesis. `forced_estimate` is the reusable forced
   vector theorem. `resistive_unique` proves equality of two supplied
   resistive solutions with the same initial field and diffusivity using
   zero forcing, with no ideal Laplacian bound required.
4. `ResistiveIdealJetBounds.lean`: `Jets.Slab.F_jets`, `Y_jets`, and
   `magnetic_jets` prove joint continuity of every finite spatial jet on a
   finite-slab time subtype. The forward proof differentiates the existing
   smooth map into continuous paths. The inverse coefficient is the inverse
   of the actual F, proved smooth at its invertible values; all coefficient
   jet and DY=A(Y) premises of `Euler/InverseMapJetContinuity.lean` are
   discharged. For the SAME glued field `Data.magnetic Bz0`,
   `MagneticPeriodicSolution.Data.magnetic_laplacian_continuousOn` proves
   joint Laplacian continuity on every `[D.a,b] x R3`, b<1, including a.
   `magnetic_laplacian_periodic` proves its periods, and
   `magnetic_laplacian_bound` supplies a finite nonnegative bound independent
   of eta_m. Whole spatial slices are identified with a larger finite-slab
   representative by the existing overlap theorem.
5. `ResistiveActualComparison.lean`: `Comparison.actual_ideal_resistive`
   constructs `actualData budget threshold geometry scales hsel a ha` and
   proves both L,D bounds before quantifying over eta_m and Bres.
   `actual_comparison_constant` packages C>=0 before those quantifiers.
   `actual_resistive_unique` also discharges the actual velocity bound.
   `periodic_comparison_main` instantiates the closed Paper I NS witnesses,
   pressure, forcing, physical time and viscosity-one velocity. It exports
   the ideal classical solution and separate spatial smoothness, joint
   Laplacian continuity, and the universally quantified comparison theorem.
   Its only supplied magnetic solution is the resistive field with the
   explicit regularity, periodicity, PDE and matching seed hypotheses.

The constant is exactly
`D*sqrt((exp((2*L+1)*(b-a))-1)/(2*L+1))`. It can depend on the selected
velocity, reference time, seed and fixed b, but not on eta_m or Bres.
Both eta_m=0 and D=0 are included. The proof compares the vector squared
norm and never assumes that Bres remains axial. It needs no divergence
hypothesis on Bres. It proves uniqueness in the stated class, not existence
or a new divergence-propagation theorem.

### Remaining obligations and stopping point

There is no remaining barrier or ideal-Laplacian hypothesis in the actual
comparison theorem. There is still no constructed positive-diffusivity
solution, no family on `[a,1)`, and no closed finite-gain theorem. The next
existence task must supply a physical-periodic heat generator/smoothing
adapter, derivative-loss source estimates, Volterra construction and
continuation, compatible regularity and slab restrictions, and forward
endpoint divergence preservation for the constructed class. This run does
not develop those objects. The older conditional curvature-mode and finite-
gain transfer statements are unchanged. There is no terminal-uniform
comparison, fixed-diffusivity blow-up/cutoff conclusion, length-scale law,
energy blow-up, stability, attraction, or magnetic backreaction claim.


### Validation of the completed comparison checkpoint

- Targeted builds passed for `ResistivePeriodicMaximum`,
  `ResistiveSquaredNormSlices`, `ResistivePeriodicComparison`,
  `ResistiveIdealJetBounds`, and `ResistiveActualComparison`.
- Full `lake build` passed: **11,300 jobs**. The only warnings were the four
  unchanged inherited `ComparatorChallenges` declarations using `sorry`.
- `scripts/audit_resistive_periodic_comparison.lean` passed all **64** checks:
  all 46 new theorems, four scalar operator definitions, and 14 explicit
  construction/comparison dependencies. Every audit is transitive.
- All **294** previous checks passed again: Paper I 151, the resistive
  foundation 77, and the earlier comparison/Gaussian checkpoint 66.
  Across all 358 checks, dependencies are limited to `propext`,
  `Classical.choice`, and `Quot.sound` (or no axioms).
- No `sorry`, `admit`, or new axiom declaration occurs in the five new Lean
  files. Previously completed Lean files are unchanged. `git diff --check`
  passed.

## Historical partial checkpoint 4d513f8: finite-gain extension

The following inventory records that commit. Its comparison and ideal-jet
gaps are closed by the checkpoint above; its resistive-existence gaps remain.

Starting state was the clean local `3a9b968`, matching origin/main. No reset
was performed. No AGENTS.md was present in the repository or its ancestor
paths checked. All existing Paper I and Paper II Lean files are unchanged.

Sound completed work:

- `ResistivePeriodicGaussian.lean`: actual three-dimensional periodic
  bounded-continuous Banach subspace, containing all constant vectors;
  constructed Gaussian averaging, directional variance continuity,
  contractive bounded linear three-coordinate operator, periodicity,
  initial and constant-seed preservation, physical variance `2*eta_m*(t-a)`.
  No heat-generator or derivative-gain theorem yet.
- `ResistivePeriodicCoefficient.lean`: uniform |u| and |Du| bounds from the
  SAME selected periodic velocity on each fixed [a,b], b<1, independent
  of eta_m; pointwise source difference and smoothness lemmas. The magnetic
  Laplacian bound remains conditional on its genuine joint continuity.
- `ResistiveIdealComparison.lean`: exact source and difference equation,
  initial difference, Young/operator bounds, exact scalar barrier ODE,
  nonnegative comparison constant and square-root step, including D=0.
- `ResistiveSquaredNorm.lean`: exact squared-norm Laplacian, forced scalar
  identity and inequality derived from the resistive/ideal PDEs. The
  parabolic maximum principle remains unproved.
- `ResistiveFiniteGain.lean`: exact observation time/gain, positive
  zero-safe diffusivity threshold, triangle-inequality gain transfer for
  arbitrary vectors, and the correct fixed-family quantifier order
  CONDITIONAL on a supplied fixed-slab pointwise comparison estimate.

**There is no actual resistive solution on [a,1) and no closed finite-gain
PDE theorem yet.** In particular, no eigen-curvature or magnetic-scale
hypothesis has been used to replace these gaps. Full statements and the
six precise analytic obligations are in the new first section of
[Paper/ResistiveMagneticInduction.md](Paper/ResistiveMagneticInduction.md).

The inherited Sobolev heat API is on R3 x S1, with four derivative directions
and a noncompact L2 measure. It was not identified with T3. The new uniform
periodic space avoids the constant-seed L2 obstruction, but completing its
Ck derivative scale, proving the physical generator/smoothing estimate,
Volterra source estimates, continuation, regularity, uniqueness, divergence
preservation and gluing remain checkpoint A work. Checkpoint B additionally
needs the ideal witness's uniform Laplacian bound and an endpoint-compatible
periodic maximum principle. Checkpoint C then needs actual instantiation.


### Validation of this partial checkpoint

- All five new Lean modules passed targeted builds.
- Full `lake build` passed: 11,295 jobs.
- `scripts/audit_resistive_comparison.lean` passed 66 audits: all 52 new
  theorems, all 13 named definitions, and the periodic completeness instance.
- The existing Paper II audit passed all 77 theorem audits; the four Paper I
  audit scripts passed all 151 theorem audits.
- Every audited dependency is among `propext`, `Classical.choice`, and
  `Quot.sound`. No new `sorry`, `admit`, or axiom declaration is present.
- The four inherited ComparatorChallenges sorry warnings are unchanged.
  No previously existing Lean file was modified. `git diff --check` passed.

## Current Paper II extension from d7d2adb

Paper I is frozen; none of its Lean files is changed. Read
[Paper/ResistiveMagneticInduction.md](Paper/ResistiveMagneticInduction.md)
for the complete statement/assumption inventory, proof outline and analytic
construction audit. All new theorems are in `NavierStokes.ResistiveMagnetic`
(with `Calculus` and `Mode` subnamespaces).

Completed:

- `ResistiveInductionOn`, `resistive_zero_iff`, `material_derivative`:
  actual project derivatives, a diffusivity distinct from similarity eta,
  and the material Laplacian term retained.
- `divergence_transport`: classical div B solves scalar advection-diffusion,
  proved by derivative commutation and cross-term cancellation.
- `periodic_divergence_preserved`, `whole_divergence_preserved_l2`:
  zero initial divergence implies zero divergence on a finite slab for
  eta_m>=0. Whole-space preservation states the smooth-L2 jets and L2 time
  derivative assumptions for the lifted divergence explicitly.
- `periodic_energy_hasDerivAt`, `whole_energy_hasDerivAt_l2`:
  half-normalized magnetic energy derivative equals stretching work minus
  eta_m times the squared-gradient integral. Whole-space integration by
  parts allows magnetic tails and uses compact u and smooth-L2 magnetic
  jets. The compact-B variant is only an alternative sufficient class.
- `actual_axial_material_derivative`, `actual_periodic_energy`,
  `actual_periodic_divergence_preserved`, `actual_compact_energy_l2`:
  reuse the same selected-schedule parameters, natural solution and actual
  velocity; the last theorem keeps the matching NS certificate explicit.
- `rescaled_induction`, `laplacian_pullback`, `stretching_pathQ`:
  exact translated/dilated PDE, coefficient eta_m/ell², and s=d0*q.
  No full natural-core gradient/Hessian transfer is assumed.
- `effectiveRm_power`, `effectiveRm_tendsto_infinity`,
  `effectiveRm_tendsto_zero`, `effectiveRm_critical`, `effectiveRm_cutoff`:
  ratio and cutoff classification under an explicitly chosen power scale.
- `pure_axial_of_curvature_closure`, `Mode.trajectory_mode`,
  `Mode.gain_le_peak`, `Mode.peakGain_formula`,
  `Mode.axial_mode_norm_le_peak`, `Mode.gain_tendsto_zero`:
  exact conditional mode amplification, finite peak and terminal decay
  for positive damping and r>0. The curvature closure is an extra magnetic
  hypothesis, not an assembled-velocity property.
- `material_high_field_region`: fixed-time region/volume/ENNReal energy
  bound for the supplied smooth field and incompressible material flow.
  No ideal Cauchy representation is asserted for resistive B.

Remaining obligations:

1. Construct a classical resistive solution for the actual prescribed
   velocity. Adapt `EulerSobolevHeat.exists_viscous_mild_solution` to the
   source `-DB[u]+Du[B]`, prove its derivative-loss/product estimates and
   match the geometry and heat normalization. Prove compatibility across
   finite slabs, classical regularity, and the needed L2 time/jet statements.
2. Derive an actual resistive magnetic scale or curvature/profile bound.
   The effective Rm classification and damped-mode cutoff do not supply it.
   No transverse-only assembled PDE or controlled remainder is proved.
3. Decide actual finite-eta supremum amplification and energy behavior.
   There is currently no actual cutoff time, maximum field, or minimum
   magnetic length theorem. No ideal blow-up survival is assumed.

No resistive PDE existence, perpetual-divergence, or length-scale axiom is
introduced. The results do not concern backreaction, coupled MHD, Hall
terms, reconnection modeling, attractors, or performance claims.

### Validation of this extension

- Targeted build of `NavierStokes.ResistiveActualAssembly` and
  `NavierStokes.ResistiveWholeDivergence` passed, covering all new modules.
- Full `lake build` passed: 11,290 jobs.
- `scripts/audit_resistive_magnetic.lean`: all 77 exported new theorems
  audited; dependencies are limited to `propext`, `Classical.choice`,
  and `Quot.sound`.
- All four prior magnetic audit scripts passed again: 151 theorem audits.
- No `sorry`, `admit`, or axiom declarations occur in the new Lean files.
  The four inherited `ComparatorChallenges` sorry warnings are unchanged.
- Paper I's Lean files are unchanged; `git diff --check` passed.

## Current extension from 3c5badb

All existing periodic and whole-space Lean results are unchanged. The new
construction bridge uses the actual `Data.magnetic W` witness throughout.
Read [Paper/MagneticRegions.md](Paper/MagneticRegions.md) for the exact
formulas, proof outline, and deformation-estimate audit.

### Amplitude and initial total energy

- `MagneticCompactSeed.potential_homogeneous`, `seed_homogeneous`.
- `MagneticCompactSolution.Data.magnetic_smul`, `energy_smul`,
  `initial_energy_scaling`, `initial_unit_energy_pos`, `small_initial_energy`.
- `MagneticCompactMain.constructed_sup_divergence`,
  `small_initial_energy_sup_divergence`, `small_initial_energy_main`.

Initial energy scales exactly as `ofReal(c^2) * E_unit(a)`, with E_unit(a)
strictly positive and finite. The closed main theorem fixes compatible
selected-schedule NS data and a late reference time before choosing epsilon
or amplitude. Every positive real epsilon admits c>0 and the actual constructed
field with `0<E(a)<ofReal epsilon` and global spatial supremum divergence.

### Deliverable A: derivative-bound theorem

`MagneticAmplificationRegion.radius_bounds` and `high_field_ball` prove the
quantitative mean-value neighborhood for r0>0, M>0, H>=0, a differentiable Q
on the closed r0-ball, central norm M, and derivative norm <=H there.
The radius is `r0*M/(2*(M+r0*H))`; it is positive, <=r0/2, and H*r<=M/2.
The theorem includes H=0.

`MagneticEnergyLowerBounds.energy_of_region` proves
`ofReal(M^2/8)*volume(U) <= energy B t` from a measurable U and the high-field
inequality. `c3_pos`, `unit_ball_volume`, `unit_ball_finite_positive`, and
`ball_volume` establish the dimensional constant and ball measure.

`MagneticCompactFlow.Slab.Phi_measurePreserving`, `region_open`,
`region_volume`, and `quantitative_region` prove the physical image-volume
and energy conclusions using the actual invertible flow.

### Deliverable B: constructed witness and finite bounds

`MagneticCompactFlow.Slab.qPath_smooth`, `extendedDQ_continuous`,
`extendedDQ_eq`, and `exists_uniform_DQ_bound` use smooth maps into continuous
path spaces to prove uniform derivative bounds through slab endpoints.
`Q_fderiv_apply` proves `DQ[v]=(DF[v])W+F(DW[v])`; `Q_fderiv_plateau`
removes the second term on the constant-seed plateau.

`MagneticCompactSolution.Data.Phi_eq_slab`, `Q_eq_slab`, `magnetic_Phi_Q`,
`Phi_eq_trajectory` bridge the actual glued flow, Jacobian, field and trajectory.
`exists_uniform_DQ_bound`, `derivativeBound_spec`, `derivativeBound_uniform`
prove finite H(t), and a uniform bound on every fixed [a,b], b<1.
`quantitative_region` transfers the slab theorem to that single field.

`MagneticCompactMain.constructed_label_amplification` proves the exact norm
M(t) at the distinguished label. `constructed_quantitative_region` exports
open positive-volume regions U_t, exact volume `ofReal(c3*r(t)^3)`, the
M(t)/2 pointwise lower bound, and
`ofReal((c3/8)*M(t)^2*r(t)^3) <= energy B t`.
It takes the existing actual selected/NS data, `0<=a<1`, `lateStart<a`,
Bz0!=0, r0>0, and a<=t<1. It assumes neither a magnetic representation for an
arbitrary existential witness nor a bound on H: these are constructed.

### Deliverable C: conditional criterion, actual rate still open

`MagneticEnergyLowerBounds.radius_lower`, `power_lower`,
`eventual_power_lower`, `energy_exponent_negative`, and
`conditional_energy_divergence` prove the criterion. For fixed C>0, p>=0,
assuming an eventual `H(t)<=C*(1-t)^(-p)`, the eventual lower bound is
`ofReal(c*(1-t)^(-2*K+3*max(p-K,0)))`, c>0. The exponent is negative
when p<5*K/3. ENNReal energy then tends to `nhds top`.
`MagneticCompactMain.constructed_eventual_energy_lower` exports the actual
field’s eventual power lower bound. `constructed_conditional_energy_divergence` specializes
this to the actual derivative supremum and actual field, with only that
late power bound left as an additional analytic assumption.

The flow APIs establish fixed-slab finiteness. The slow-base Eulerian jet
rates (`ActualBaseVelocityBounds.velocity_rate`, losses 18 and 40 for orders
1 and 2 in physicalQ) are not label-deformation bounds for the full assembled
velocity. Diagonal tail jet estimates require their own stage hypotheses.
Gevrey derivative bounds
require all velocity-jet bounds and a small B*R*T; there is no instantiated
terminal estimate for the actual material tube. An adequate upper bound on
D_xi(F W), or D_xi^2 Phi acting on the seed on the plateau, is still missing.
No full natural-core gradient or Hessian transfer is assumed. No magnetic
variation scale is inferred from the Eulerian core radius. Failure of this
sufficient estimate does not imply bounded terminal energy.

Positive-volume high fields at each time and their explicit time-dependent
volume bounds are proved. An indefinitely amplifying fixed material set,
perturbation stability, and attraction are not. No resistive, backreaction,
coupled-MHD, fusion, or novelty claims are added.

### Validation

- Targeted `lake build NavierStokes.MagneticSeedScaling` passed, including all
  seven new modules.
- Full `lake build` passed: 11,277 jobs. The only sorry warnings are the four
  inherited declarations in `ComparatorChallenges/Euler.lean` and
  `ComparatorChallenges/NavierStokes.lean`; no new module has such a warning.
- All 47 new theorems in `scripts/audit_magnetic_regions.lean` passed axiom
  audits, with only `propext`, `Classical.choice`, and `Quot.sound`.
- Re-ran all 104 prior magnetic audits: compact 66, periodic main 9,
  periodic construction 29; the same three standard axioms only.
- No sorry, admit, new axioms, or placeholder declarations were added.
  Existing periodic and whole-space Lean files are unchanged.

---

## Previous milestone: closed whole-space compact-seed ideal induction

## Current milestone after 4e276b5

The completed periodic Lean proofs are preserved unchanged. Five new modules
construct a compact smooth solenoidal seed, transport spatially varying
seeds, control supports and whole-space energy on finite slabs, glue one
preterminal field, and instantiate the exact compact NS/amplification data.
The readable outline is `Paper/WholeSpacePassiveInduction.md`.

### Seed: exact convention and statements

In `MagneticCompactSeed`, with `center=gamma(a)`:

```text
linearPotential Bz0 (x-center)
  = (Bz0/2) * (-(x-center)_1 e0 + (x-center)_0 e1)
potential center Bz0 x
  = spatialCutoff(x-center) • linearPotential Bz0 (x-center)
seed center Bz0 = SpatialCurl.curl (potential center Bz0)
```

This is the requested half-cutoff cross-product potential in the project's
curl convention. `curl_linear` proves its uncut curl is exactly `Bz0 e2`,
checking the sign and factor. `seed_eq_on_plateau`, `seed_local_constant`,
and `seed_at_center` give the local constant identity. `seed_smooth`,
`seed_supported`, `seed_compact`, and `seed_divergence` prove global spatial
smoothness, closed support in the translated support cylinder, compact
support, and zero divergence, for every center and amplitude.

### Actual finite-slab construction

`MagneticCompactFlow.Slab.coefficient` uses
`SmoothTimeField.ofContDiffOnCompactSupport` for the internally shifted
interval `[0,b-a]`. `coefficient_apply` identifies it with the original
velocity at physical time `a+s`; `coefficient_lipschitz` supplies a uniform
finite-slab spatial Lipschitz constant from its bounded derivative path.
The bounds may depend on b. No bound through t=1 is assumed.

`MagneticCompactMain.velocity_supported` proves the actual compact velocity
has closed spatial support in the existing support cylinder at every time.
`actualData` uses exactly this support, the selected-schedule smoothness
from `assembled_velocities_smooth`, and the existing compact NS divergence
property. It does not modify or further localize the velocity.

The physical-time flow wrappers reuse the existing `EulerSmoothBanachFlow`
Picard flow, inverse, path-space regularity, Jacobian evolution, and
determinant-one theorem. For a smooth seed W, the actual definitions are

```text
F t xi = fderiv real (Phi t) xi
magnetic W (t,x) = F t (Y t x) (W (Y t x)).
```

`Slab.magnetic_initial`, `magnetic_continuousOn`, `magnetic_contDiffAt`,
`magnetic_spatial_smooth`, and `magnetic_induction` prove initial data,
endpoint continuity, interior joint C1 regularity, all finite spatial
orders, and stretching-form ideal induction. The proof differentiates
`magnetic W (t,Phi t xi)=F t xi (W xi)` with fixed xi, using `F_hasDerivAt`.
`magnetic_divergence_free` uses `F_det_one` and the existing
`EulerPacketVolumeDivergence.divergence_pushforward` with the varying seed.
No second time derivative or unjustified C2 regularity of B is invoked.

### Support, whole-space energy, and overlap

`MagneticCompactFlow.Slab.transported_support` states:

```text
tsupport (fun x => magnetic W (t,x)) subset Phi t '' tsupport W.
```

`supportTube_compact` proves compactness of the image of
`[a,b] × tsupport W`; `magnetic_supported_tube` gives uniform support
containment in this tube. These are actual transported-support statements,
not amplitude estimates substituted for support information.

`MagneticCompactFlow.energy B t` is the ENNReal nonnegative Lebesgue integral
`(1/2) * integral_R3 norm(B(t,x))^2 dx`. `compact_slab_bounds` proves:

```text
exists C >= 0, exists E < infinity, forall t in [a,b],
  (forall x, norm(B(t,x)) <= C) and supNorm B t <= C and
  energy B t <= E and energy B t < infinity.
```

Its hypotheses are joint continuity on the fixed slab and support in one
compact set. The integral is bounded by an indicator of that set, giving
`E=(1/2)*C^2*volume(K)`. It does not integrate a nonzero constant over all
of R3. There is no upper bound asserted uniformly as b approaches one.

`Slab.Phi_overlap`, `F_overlap`, `Y_overlap`, and `magnetic_overlap` compare
slabs with the same velocity, initial time, and seed, using the established
flow-uniqueness argument. `MagneticCompactSolution.Data.magnetic` glues a
strictly increasing cofinal sequence of upper endpoints into ONE field.
`magnetic_eq_slab` proves compatibility. The exported regularity, induction,
divergence, and initial-data theorems all apply to that single field.
`Data.transported_support` retains the precise flow-image containment on
finite restrictions; `uniform_support` and `slab_bounds` give the compact
support and norm/energy estimates for every fixed preterminal slab.

### Closed theorem and exact upstream matching

In `NavierStokes.MagneticCompactMain`:

```text
whole_space_main : exists scales, Selected scales and
  exists forcing a, 0 < a and a < 1 and
  R3CompactCandidate.Properties (velocity scales) (pressure scales) forcing and
  ContDiff real infinity forcing and
  forall Bz0 : real, exists B,
    MagneticConclusions (velocity scales) a Bz0 B.
```

`velocity scales` is exactly `actualCompactVelocity` at the existing
`selectedBudget`, `selectedThreshold`, and `selectedThreshold_geometry`.
`pressure scales` is the existing compact pressure of the actual pressure
sum using the same schedule. The forcing is the existing `compactForce`
of the forcing supplied by `ActualCandidateAssembly.selected_witness`.
`R3CompactCandidate.of_localized_fields` proves the NS properties for these
same fields. No new velocity localization is introduced.

The natural-profile proof is
`MagneticPeriodicMain.naturalSolution`, i.e. the same retained
`ActualPrimary.nominal.axis.natural.profile.family.natural`. No independent
natural witness or schedule is used. The main theorem chooses a late regular
time before choosing a seed amplitude. Its `MagneticConclusions` exports:

- `B(a,x)=seed (gamma a) Bz0 x` for every x and local equality to `Bz0 e2`;
- joint continuity on `[a,1)`, interior joint C1 regularity, and spatial
  smoothness at every time;
- induction for this actual compact velocity and magnetic divergence freedom;
- uniform compact support and finite supremum/whole-space-energy bounds on
  every fixed `[a,b]`, `b<1`;
- `B(t,gamma t)=Bz0*((1-a)/(1-t))^K e2` for every `a<=t<1`;
- for `Bz0 != 0`, pathwise norm divergence and global spatial supremum-norm
  divergence as `t -> 1-`.

The compact amplification and norm-divergence theorems are reused without
changing their exponent or physical-time formula. Global supremum divergence
uses the actual spatial supremum and its pointwise lower bound, justified
by the proved slab boundedness; it is not an essential-supremum assertion.

### Remaining assumptions and exclusions

`whole_space_main` has no upstream construction hypotheses. The generic
transport lemmas retain explicit regularity, compact-support, and divergence
assumptions, all discharged in the closed theorem. No magnetic PDE solution
or suitable flow wrapper is assumed. Joint C-infinity regularity is not
claimed; all spatial orders and interior joint C1 regularity are proved.

At this earlier construction checkpoint there was no finite-volume lower
bound; the current extension above supplies one. Actual terminal energy
blow-up, arbitrary-direction amplification, resistive amplification, Lorentz
backreaction, and coupled MHD remain unproved. Finite-slab energy upper bounds
alone imply no energy-growth lower bound. The velocity remains prescribed and forced, with viscosity one
and physical singular time one. No novelty or publication claim is made.

### Validation

- Targeted `lake build NavierStokes.MagneticCompactMain` passed, including
  all five new modules.
- Full `lake build` passed: 11,270 jobs. Four pre-existing challenge `sorry`
  warnings remain in `ComparatorChallenges/Euler.lean` and
  `ComparatorChallenges/NavierStokes.lean`, outside the audited proof chain.
- `scripts/audit_magnetic_compact.lean` passed for all 66 audited declarations:
  every new public theorem, plus the coefficient and actual-data definitions.
  The closed whole-space main theorem uses only `propext`, `Classical.choice`,
  and `Quot.sound`, with no `sorryAx` or custom axiom dependency.
- Both prior periodic audit scripts passed again (9 + 29 declarations).
  All 104 audited declarations use only the same standard logical axioms.
- The new Lean modules contain no `sorry`, `admit`, or axiom declarations.
  Existing Lean proofs and the prior audit scripts are unchanged from
  `4e276b5`. Whitespace checks passed.

---

# Historical handoff: closed periodic main theorem and norm consequences

## Current milestone

New modules `MagneticPeriodicMain.lean` and `MagneticPeriodicNorms.lean`
package the previous construction without changing its proofs. The readable
statement and proof outline are in `Paper/PeriodicPassiveInduction.md`.
The historical entries below retain their original assumptions; the closed
main theorem here discharges the selected-schedule and natural-solution
hypotheses that were explicit at commit `1aab808`.

### Upstream closure and exact velocity identity

`MagneticPeriodicMain.naturalSolution` is the retained proof
`CorrectionInitialization.ActualPrimary.nominal.axis.natural.profile.family.natural`.
This is the already selected entrance/profile-family solution used by the
actual nominal construction, not an independently selected solution sharing
only nominal parameter names. Its h, j, pressure datum, scale, and
normalization match ActualPrimary by their dependent types.

`periodic_main` instantiates `ActualCandidateAssembly.selected_witness` with
its selected budget, selected threshold, and selected threshold geometry.
One returned schedule supplies both the magnetic construction and the NS
witness. The velocity is exactly `actualPeriodicVelocity` with those values.
`MagneticPeriodicMain.pressure` is the activated periodic pressure sum of the
same schedule's actual pressure stages. `CandidateProperties`, global smooth
forcing, and `CandidateConsequences.Consequences` are retained for precisely
this velocity, pressure, and forcing.

There are **no remaining upstream compatibility or existence assumptions**
in `periodic_main`. The reusable `constructed_conclusions` deliberately
retains `Selected scales`, `lateStart ... < a`, and `a<1`; the closed theorem
instantiates them. Standard Lean logical axioms are listed in the audit.

### Exact main statements

In namespace `NavierStokes.MagneticPeriodicMain`, abbreviations `budget`,
`threshold`, and `geometry` are the existing selected constants;
`velocity scales` is the corresponding actual assembled periodic velocity.

```text
periodic_main : exists scales, Selected scales and
  exists forcing a, 0 < a and a < 1 and
  CandidateProperties (velocity scales) (pressure scales) forcing and
  ContDiff real infinity forcing and
  CandidateConsequences.Consequences (velocity scales) (pressure scales) forcing and
  forall Bz0 : real, exists B,
    MagneticConclusions (velocity scales) a Bz0 B
```

`MagneticConclusions u a Bz0 B` exports:

1. The existing `ClassicalSolution u B a 1 Bz0`: joint continuity,
   interior joint C1 regularity, periodicity, magnetic divergence freedom,
   stretching-form induction, and constant axial seed at every spatial point.
2. `forall t in [a,1), ContDiff real infinity (fun x => B(t,x))`.
3. Exact amplification `B(t,gamma(t)) = Bz0*((1-a)/(1-t))^K e2` on `[a,1)`.
4. For `Bz0 != 0`, pathwise norm divergence and global spatial supremum-norm
   divergence as `t -> 1-`.
5. For every `b in [a,1)`, constants `C>=0` and `E<infinity` such that, uniformly
   for `t in [a,b]`, `supNorm B t <= C` and `cellEnergy B t <= E < infinity`.

The velocity and the late time are selected BEFORE quantifying over seed
amplitudes. `arbitrarily_small_seed` states:

```text
exists scales forcing a, 0 < a and a < 1 and
  CandidateProperties (velocity scales) (pressure scales) forcing and
  forall epsilon > 0, exists Bz0, 0 < Bz0 and Bz0 < epsilon and
    exists B, MagneticConclusions (velocity scales) a Bz0 B and
      Tendsto (supNorm B) (nhdsWithin 1 (Iio 1)) atTop.
```

It uses `Bz0=epsilon/2`. The velocity remains prescribed for every seed.

### Norm and finite-time energy proofs

`MagneticPeriodicNorms.supNorm B t` is `sSup (range (fun x => norm(B(t,x))))`.
`slab_bound` proves boundedness of all spatial values on a fixed time slab
by compactness of its product with the existing unit cube and exact periodic
reduction to fractional coordinates. `supNorm_bounds` justifies this real
supremum and the lower bound by every point value. `supNorm_tendsto` then
compares it with the diverging trajectory norm. An essential supremum is
not used, so no pointwise-to-essential-supremum assumption is hidden here.

`cellEnergy B t` is the ENNReal nonnegative Lebesgue integral
`(1/2) * integral_cell norm(B(t,x))^2 dx`.
`energy_bound` proves it is at most `(1/2)*C^2*volume(cell)` under a global
pointwise bound C. `slab_norm_energy_bound` combines this with compact-cell
finite measure to prove finiteness and a uniform upper bound on each fixed
`[a,b]`. Spatial smoothness of the same B is exported separately. No bound
uniform in b as b tends to one is asserted, and no energy lower bound or
energy blow-up is proved.

### Scope and validation

The physical clock is unchanged: viscosity one, singular time one, and
power-law factor `((1-a)/(1-t))^K`. The earlier exponent, amplification,
transport, and flow proofs are unchanged. Joint C-infinity regularity is not
claimed. Whole-space compact-seed transport remains the following milestone.
No arbitrary-direction amplification transfer, finite-volume energy-growth
result, resistivity, Lorentz backreaction, coupled MHD, or fusion-performance
claim is made. Novelty and publication readiness have not been assessed.

Validation completed:

- `lake build NavierStokes.MagneticPeriodicMain` passed. The small-seed
  corollary's final explicit norm-divergence conclusion was also checked by
  the subsequent full build.
- Full `lake build` passed: 11,265 jobs. Four inherited `sorry` warnings in
  `ComparatorChallenges/Euler.lean` and `ComparatorChallenges/NavierStokes.lean`
  remain outside this proof chain.
- `lake env lean scripts/audit_magnetic_main.lean` passed for all nine new
  audited declarations, including the retained natural-solution proof, the
  energy/supremum estimates, and both closed main results.
- `lake env lean scripts/audit_magnetic_periodic.lean` passed again for all
  29 prior construction declarations. All 38 audited declarations depend
  only on `propext`, `Classical.choice`, and `Quot.sound`; none uses `sorryAx`.
- The new modules contain no `sorry`, `admit`, or added axiom declarations.
  Existing Lean proofs and the prior audit script are unchanged from
  `1aab808`. Whitespace checks passed.

---

# Historical handoff: constructed periodic ideal induction

## Current milestone: checkpoints A and B

The existing exponent and amplification proofs are unchanged. New modules:

- `MagneticPeriodicCoefficient.lean`: compact-cell coefficient adapter and
  actual assembled periodic incompressibility.
- `MagneticPeriodicFlow.lean`: physical-time flow, inverse, actual Jacobian,
  finite-slab magnetic construction, regularity, induction, and divergence.
- `MagneticPeriodicCompatibility.lean`: overlap compatibility of flows,
  inverse flows, actual spatial derivatives, and transported fields.
- `MagneticPeriodicSolution.lean`: cofinal gluing into one preterminal field
  and existential periodic magnetic amplification.

The earlier sections below are historical. Their statements that periodic
magnetic existence or divergence preservation is unproved are superseded by
this milestone. Whole-space compact-seed existence remains unproved.

### Checkpoint A: exact construction and exported statements

`MagneticPeriodicCoefficient.ofPeriodicSlab` converts a jointly smooth
periodic field on a compact time set into `SmoothTimeField`. The bounded
continuous field and every spatial jet use the existing periodic unit cube.
Uniform continuity on that cube proves continuity in the uniform spatial
norm. There is no bound assumed as `b` approaches one.

`onSlab` and `actualOnSlab` use internal time `s=t-a` in `[0,b-a]`.
`actualOnSlab_apply` states that the coefficient is precisely the actual
selected velocity at physical time `a+s`. `actual_periodic` and
`actual_divergence` discharge periodicity and divergence freedom, including
localization of the direct angular series and the final time activation.

In namespace `MagneticPeriodicFlow.Slab`:

```text
Phi t xi = data.forward (t-a) xi
Y t x    = data.backward (t-a) x
F t xi   = fderiv real (Phi t) xi
magnetic Bz0 (t,x) = Bz0 • (F t (Y t x) e2)
```

`Phi_initial`, `Y_initial`, `Y_Phi`, and `Phi_Y` establish the fixed-start
flow and its two-sided inverse. `Phi_hasDerivAt` states the actual physical
ODE at every time in `[a,b]`. `F_eq_evolution` identifies the actual spatial
derivative with the existing `jacobianEvolution`; `F_initial` gives the
identity operator and `F_hasDerivAt` gives

```text
forall t in (a,b), HasDerivAt (fun s => F s xi)
  ((spatialDerivative velocity t (Phi t xi)).comp (F t xi)) t.
```

`magnetic_Phi` is the exact pullback identity. Differentiating it, using the
variational ODE, the material chain rule, and `Phi_Y`, proves
`magnetic_induction`. `F_det_one` uses the existing trace-free linear
evolution determinant theorem. `magnetic_divergence_free` instantiates
`EulerPacketVolumeDivergence.divergence_pushforward` with the constant seed;
that proved geometric identity uses Hessian symmetry and the determinant
derivative. No C2 regularity of B is inferred from C2 regularity of Phi.

`MagneticPeriodicFlow.actual_finite_slab` has the actual `budget`, `N0`,
`hN`, `scales`, and `hsel : SelectedSchedule ... scales` parameters and states:

```text
forall a b Bz0, a < b -> b < 1 -> exists B,
  (forall x, B(a,x) = Bz0 • e2) and
  ContinuousOn B ([a,b] × univ) and
  (forall t in (a,b), forall x, ContDiffAt real 1 B (t,x)) and
  (forall t in [a,b], ContDiff real infinity (fun x => B(t,x))) and
  UnitSpatialPeriodsOn [a,b] B and
  IdealInductionOn (a,b) (actualPeriodicVelocity budget N0 hN scales) B and
  (forall t in [a,b], forall x, spatialDivergence B t x = 0).
```

This theorem constructs its flow and its field. It assumes neither an
induction solution nor a suitable flow wrapper.

### Checkpoint B: one field and existential amplification

`Slab.Phi_overlap` proves equality on intersecting slabs with equal velocity
and initial time, by the bounded-flow Lipschitz estimate and Gronwall
uniqueness. `F_overlap` differentiates equality of spatial maps, `Y_overlap`
uses the two-sided inverse identities, and `magnetic_overlap` follows.

`MagneticPeriodicSolution.Data.endpoints_spec` supplies a strictly increasing
sequence in `(a,1)` tending to one. `Data.magnetic` defines one field from
these slabs. `magnetic_eq_slab` proves independence of the chosen index on
all of `[a,b_n]`; local equality transfers continuity at the initial boundary
and interior C1 regularity, induction, and divergence freedom.
`magnetic_spatial_smooth` additionally proves all finite spatial orders at
each preterminal time. No joint C-infinity regularity is claimed.

`ClassicalSolution u B a 1 Bz0` means exactly:

```text
ContinuousOn B ([a,1) × univ)
forall t in (a,1), forall x, ContDiffAt real 1 B (t,x)
UnitSpatialPeriodsOn [a,1) B
forall t in [a,1), forall x, spatialDivergence B t x = 0
IdealInductionOn (a,1) u B
forall x, B(a,x) = Bz0 • e2.
```

`exists_actual_solution` states, with the same selected-schedule data:

```text
forall a Bz0, a < 1 -> exists B,
  ClassicalSolution (actualPeriodicVelocity budget N0 hN scales) B a 1 Bz0.
```

`exists_actual_amplifying_solution` additionally retains
`hs : NaturalProfile.IsNaturalSolution h nominal.axis.j Lambda P0 a0 f U V Pr`.
For `lateStart budget N0 hN scales hsel hs < a < 1` and `Bz0 != 0`, it states:

```text
exists B,
  ClassicalSolution (actualPeriodicVelocity budget N0 hN scales) B a 1 Bz0 and
  (forall t in [a,1),
    B(t,gamma t) = (Bz0 * ((1-a)/(1-t))^K) • e2) and
  Tendsto (fun t => norm (B(t,gamma t))) (nhdsWithin 1 (Iio 1)) atTop.
```

Here `gamma` and `K` are precisely the existing distinguished trajectory and
`axialExponent nominal.axis.small`. The proof derives every magnetic
hypothesis before applying the existing conditional amplification theorems.
It never chooses unrelated induction fields on successive intervals.

### Upstream assumptions and exact scope

The coefficient adapter uses the smooth sums already included in the
actual `SelectedSchedule`; it introduces no additional smoothness, bound,
flow-existence, or magnetic-solution assumption. The nonlinear flow is the
existing `EulerSmoothBanachFlow.flowData` construction, with its Picard flow,
path-space smooth dependence, constructed Jacobian evolution, invertibility,
and determinant-one theorem. The inverse C1 proof specializes the existing
smooth implicit-lift machinery. The selected schedule remains an explicit
parameter; its upstream existence is provided by
`ActualCandidateAssembly.selected_witness`, not reselected by this milestone.
The natural-solution hypothesis remains explicit in amplification only; it
is not needed for the ideal-induction existence theorem itself.

All exported statements use the existing viscosity-one assembled periodic
velocity and physical singular time one. The internal shift cancels on export;
there is no different physical-time power law and no new viscosity rescaling.

No remaining gap within the two requested periodic checkpoints is advertised
as an assumption on B. Scope still excluded: whole-space compact-seed
construction, arbitrary-seed amplification transfer, resistivity, Lorentz
backreaction, finite-volume amplification, magnetic-energy blow-up, and
coupled MHD blow-up. The norm-divergence conclusion is along one trajectory.

### Validation

- Targeted build of `NavierStokes.MagneticPeriodicSolution` passed, including
  all four new modules. The final spatial-regularity addition was checked by
  the subsequent full build.
- Full `lake build` passed: 11,263 jobs. It replayed four pre-existing
  `sorry` warnings in `ComparatorChallenges/Euler.lean` and
  `ComparatorChallenges/NavierStokes.lean`; none are in the new proof chain.
- `lake env lean scripts/audit_magnetic_periodic.lean` passed. All 29 audited
  declarations depend only on `propext`, `Classical.choice`, and `Quot.sound`.
  This includes both actual existence theorems and the existential
  amplification/norm-divergence theorem. There is no `sorryAx` dependency.
- The separate checkpoint-A audit passed for the actual velocity divergence,
  Jacobian identification, variational ODE, determinant, magnetic divergence,
  and `actual_finite_slab`, with the same three axioms.
- No `sorry`, `admit`, or new axiom declaration occurs in the new modules.
  `git diff --check` passed. Existing amplification and gradient files are
  unchanged.

The audit script is retained in the repository for reproduction.

---

# Historical handoff: assembled conditional magnetic amplification

## Current milestone after local commit 07a694d

New module: `NavierStokes/MagneticAssembledAmplification.lean`.
The earlier trajectory, gradient, core amplification, and minimal transfer
proofs are preserved. README now records the assembled conditional results.
No magnetic field or global magnetic PDE solution is constructed.

### Exact candidates, parameters, and physical clock

The new theorems use `MagneticAxisTransfer.actualPeriodicVelocity` and
`actualCompactVelocity` without changing their definitions. Parameters remain
`budget N0 : Nat`, `hN : geometricThreshold≤N0`, `scales : Nat→Nat`, and the
actual `MixedCandidateWitness.SelectedSchedule ... scales`, including the
same potential, direct, and pressure sequences. A supplied
`NaturalProfile.IsNaturalSolution h nominal.axis.j Λ P0 a0 f U V Pr` uses
`CorrectionInitialization.ActualPrimary.h` and `nominal.axis.j`.

Write `γ=trajectory h (distinguishedEta nominal.axis.small)` and
`K=axialExponent nominal.axis.small`. These are existing definitions. All exact
exponent identities and `3.9999995<K<4` are reused, not rederived.

Both assembled fields include the existing time activation and spatial cutoffs;
the periodic one additionally periodizes. Both are viscosity-one fields in
physical time `t`, with singular time `1`. The formula in both theorems is
`((1-a)/(1-t))^K`. There is no new time or spatial rescaling.
The comparator's separate positive-viscosity force rescaling is not silently
applied to either field, and no arbitrary-viscosity induction theorem is claimed.

`assembled_velocities_smooth` extracts smoothness of the actual sums from
`SelectedSchedule` and proves both final velocities smooth on `t<1`.
`gradient_continuousOn_along_path` derives Jacobian continuity from smoothness.
`exists_late_axial_flows` combines this with the existing minimal transfer
interval. `lateStart` chooses one common threshold; `lateStart_spec` proves
it is below one and retains the late-flow facts for both candidates. This
threshold only restricts theorem applicability; it does not alter either field.

### Generic scalar transport

`pure_axial_transport_of_scalar_solution` assumes a supplied Lagrangian path,
ideal induction, continuity of `B(t,γ(t))` on `[a,b]`, joint differentiability
of `B` at the interior path points, and continuity of `Dₓu(t,γ(t))` on `[a,b]`.
If the axial column is `α(t)e₂`, and a continuous scalar function `β` satisfies
`β′=αβ` on `(a,b)` and `β(a)=Bz0`, then a pure seed implies
`B(t,γ(t))=β(t)e₂` on `[a,b]`.

`pure_axial_follows_scalar_ode` removes the supplied scalar-solution assumption:
it constructs such a `β` using `TangentODE.exists_linear_solution`. The
continuous scalar coefficient comes from the axial component of the actual
continuous Jacobian column, agreeing with `α` on interior times. It concludes

```text
exists β, β(a)=Bz0 and ContinuousOn β [a,b]
  and (forall t in (a,b), HasDerivAt β (α(t)*β(t)) t)
  and (forall t in [a,b], B(t,γ(t))=β(t)e₂).
```

Both proofs use the existing material chain rule and linear-ODE uniqueness.
They do not assume the entire magnetic field is axial away from the path.

`LateAxialFlow u γ K T` packages path/Jacobian continuity on `(T,1)`, the
trajectory derivative, and the column `K/(1-t)e₂`. Its three proved consumers
are `LateAxialFlow.pure_axial_transport`,
`LateAxialFlow.pure_axial_transport_preterminal`, and
`LateAxialFlow.magnetic_norm_tendsto_atTop`. The power-law consumer reuses
`MagneticCoreAmplification.pure_axial_transport_of_directional_gradient` and
its previously verified exponent/power-law lemmas.

### Assembled finite-interval theorem statements

In namespace `NavierStokes.MagneticAssembledAmplification`:

- `periodic_pure_axial_transport` uses
  `u=actualPeriodicVelocity budget N0 hN scales`.
- `compact_pure_axial_transport` uses
  `u=actualCompactVelocity budget N0 hN scales`.

For both, let `T₀=lateStart budget N0 hN scales hsel hs`. In addition to the
construction parameters and supplied natural solution above, the hypotheses
are exactly:

1. `T₀<a`, `a≤b`, `b<1`.
2. A supplied `B : MagneticField` with
   `IdealInductionOn (Ioo a b) u B`, referring to the ASSEMBLED velocity.
3. `ContinuousOn (fun t => B(t,γ(t))) (Icc a b)`.
4. `∀t∈Ioo a b, DifferentiableAt ℝ B (t,γ(t))`.
5. `B(a,γ(a))=Bz0 • e₂`.

For every `t∈Icc a b`, the conclusion is

```text
B(t,γ(t)) = (Bz0*((1-a)/(1-t))^K) • e₂.
```

No extra assumed Jacobian continuity, neighborhood equality to the natural
core, or full-gradient equality appears in these specializations. The
necessary velocity regularity and late column identity are discharged.

### One-solution conditional norm divergence

`periodic_magnetic_norm_tendsto_atTop` and
`compact_magnetic_norm_tendsto_atTop` have the same construction data and
`T₀<a<1`, but assume `Bz0≠0` and ONE fixed `B` satisfying:

```text
IdealInductionOn (Ioo a 1) u B
ContinuousOn (fun t => B(t,γ(t))) (Ico a 1)
forall t in Ioo a 1, DifferentiableAt real B (t,γ(t))
B(a,γ(a)) = Bz0 • e₂.
```

They conclude `Tendsto (fun t => norm(B(t,γ(t)))) (nhdsWithin 1 (Iio 1)) atTop`.
The same `B` is restricted to `[a,t]` for each evaluation time, giving the exact
formula on `[a,1)`. The norm becomes
`abs(Bz0)*(1-a)^K*(1-t)^(-K)`, whose constant prefactor is strictly positive.
`axialExponent_pos` and `BlowupImplication.negative_power_tendsto_atTop` give
the limit. No sequence of unrelated interval-wise solutions is selected.

The periodic-velocity theorem does not require spatial periodicity of `B` for
this pathwise implication. A future periodic existence theorem should provide
that property in addition to the induction and regularity hypotheses.

### Remaining mathematical assumptions and limits

A suitable induction solution is still supplied, not proved to exist. Magnetic
divergence preservation is not proved; the stretching-form predicate and the
incompressible-induction predicate remain distinct. No arbitrary-seed axial
component theorem is transferred: a column identity preserves axial seeds,
but does not control the axial contribution of a transverse seed. The required
axial row/covector identity is not part of this milestone.

No finite-volume amplification, magnetic-energy blow-up, finite-resistivity
growth, or coupled MHD blow-up is asserted. The norm limit is along one path.

### Validation

The targeted new-module build passed. Full `lake build` passed with 11,259 jobs.
All 13 new theorem declarations were checked with `#print axioms`; each uses
only `propext`, `Classical.choice`, and `Quot.sound`. No new `sorry`, `sorryAx`,
or axiom declaration was introduced. The four inherited comparator-challenge
`sorry` warnings remain. The printed main theorem types were also inspected to
verify that their induction hypotheses name the correct assembled velocities.

## Next implementation plan: smallest periodic flow-map API

This is an implementation plan, not a set of placeholder Lean declarations.
Fix ONE actual periodic candidate and a reference time `a>T₀`. The intended
initial field is spatially constant at that time:
`B(a,x)=Bz0*e₂` for every `x`. A constant seed at time zero would be a different
problem; its value on the distinguished path at a later reference time must
not be assumed to remain axial.

### Minimal interface

Work on the existing `Space=real^3` periodic cover; no quotient or volume API is
needed to construct stretching-form induction. On each `[a,b]`, `b<1`, expose:

| Data or law | Purpose |
| --- | --- |
| Fixed-start forward map `X(t,y)` with `X(a,y)=y` and `d_t X=u(t,X)` | Supplies the actual particle paths |
| Inverse `Y(t,x)` with `Y(t,X(t,y))=y` and `X(t,Y(t,x))=x` | Turns label-dependent transport into an Eulerian field |
| One vector column `C(t,y)`, `C(a,y)=e₂`, `d_t C=Dₓu(t,X(t,y)) C` | Transports the constant axial seed; a full deformation-matrix API is not required |
| Joint continuity through interval endpoints, joint differentiability of `Y` and `C` at interior points | Makes `B(t,x)=Bz0*C(t,Y(t,x))` differentiable and allows the material chain rule |
| `X(t,y+n)=X(t,y)+n`, `Y(t,x+n)=Y(t,x)+n`, and `C(t,y+n)=C(t,y)` for lattice translations | Proves periodicity of the constructed magnetic field |
| Restriction compatibility for `X,Y,C` on overlapping finite intervals with the same start time and velocity | Glues ONE field on `[a,1)` for the norm-divergence theorem |

The column need not stay axial at arbitrary labels. Only the distinguished
trajectory has the column-invariance property established in this milestone.
No determinant, volume preservation, or full inverse-Jacobian interface is
needed for this stretching-form construction. These do not discharge magnetic
divergence preservation, which remains a separate theorem.

### Existing APIs to reuse and the missing adapters

1. **Periodic smooth field to bounded coefficient paths.** Build the existing
   `SmoothTimeField (Icc 0 (b-a)) Space Space` for
   `u(a+s,x)`, plus its time-derivative field. Periodicity reduces each spatial
   jet bound and its uniform time continuity to a compact fundamental cell.
   `assembled_velocities_smooth`, the actual velocity periodicity lemmas, and
   `ResidualRegularity.space_fderiv_periods` supply the source facts.
   `PeriodicUniqueness.exists_gradient_bound` gives the relevant compact
   gradient bound; extend it periodically to obtain a global Lipschitz bound
   on each finite interval. Bounds may depend on `b`; no bound through time
   one is required. This packaging adapter is not yet implemented.
2. **Construct the fixed-start flow and inverse.** Reuse
   `EulerBoundedLipschitzFlow.exists_flow_and_inverse` from
   `Euler/FiniteIntervalFlow.lean`, or the already smooth
   `EulerSmoothBanachFlow.flowData` from `Euler/SmoothBanachFlow.lean`.
   The latter derives its Lipschitz bound from `SmoothTimeField`.
   Shift `s=t-a` only inside the adapter and export all statements in the
   original physical time. The generic `Space` API is sufficient; the
   repository's lifted four-dimensional cylinder-flow API is unnecessary.
3. **Construct one differentiated column.**
   `Euler/SmoothFlowJacobian.lean` provides `jacobianEvolution`,
   `forward_hasFDerivAt_label`, `forward_fderiv`, and inverse differentiability.
   Apply the actual Jacobian to `e₂` to define `C`. Its variational ODE comes
   from that evolution; `Euler/LinearDuhamel.lean` supplies initial-value and
   derivative/uniqueness laws. `Euler/SmoothFlowJoint.lean` supplies
   `forward_joint_contDiffAt_two` and `backward_joint_contDiffAt_two` from the
   time-derivative data, sufficient for joint `C¹` regularity of the column
   and inverse. A small wrapper should export only the column laws needed
   here. Gevrey smallness estimates from stronger flow modules are not needed.
4. **Periodicity and Eulerian induction.** Use
   `EulerBoundedLipschitzFlow.Data.flow_add_eq` from
   `Euler/BoundedFlowPeriodicity.lean` for each coordinate lattice shift;
   differentiation or variational uniqueness gives periodicity of `C`.
   Define `B(t,x)=Bz0*C(t,Y(t,x))`. Prove the initial constant field and
   periodicity. Differentiate `B(t,X(t,y))=Bz0*C(t,y)` and use surjectivity of
   `X` to obtain `IdealInductionOn` pointwise. This avoids separately deriving
   a PDE for the inverse map.
5. **Compatibility and a single preterminal solution.** Use trajectory
   uniqueness on overlaps and the existing linear-ODE uniqueness for columns,
   with the same initial time and seed. `SmoothTimeField.compTime` and its
   restriction API help align the finite-interval inputs. Glue along a
   cofinal family `b→1` only AFTER proving overlap equality; regularity and
   induction then follow locally from one finite slab. Apply the new
   assembled norm theorem to this one field. No such gluing or magnetic
   existence proof was added in the current milestone.

## Previous milestone at 07a694d (historical)

The following material preserves the prior handoff and correction audit.
Earlier statements that assembled magnetic amplification is unproved are
superseded by the conditional results above; magnetic existence is still open.


## Prior natural-core milestone

The natural-core amplification milestone is proved in
`NavierStokes/MagneticCoreAmplification.lean`. Existing
`MagneticSimilarityGradient.lean` proofs have been preserved.
The separate minimal assembled-flow audit is proved in
`NavierStokes/MagneticAxisTransfer.lean`.

### Exact exponent and bounds

Use the existing `NaturalAxisData.A`, `D`, `d`, and `L`, and set
`eta0 = MagneticSimilarityTrajectory.distinguishedEta p`. The only new exponent
definition is `MagneticCoreAmplification.axialExponent p`:

```text
K = (4*d(eta0)^2 + 2*A(h)*D(h)*eta0^2)/L(h,eta0).
```

With `p : SmallParameters h j` (`0<h≤1/1000`, `0<j≤1/1000`), Lean proves:

- `axialExponent_pos`: `0 < K`.
- `axialExponent_defect`:
  `4-K = eta0^2*(15/2 - 8*h + 2*h^2 - 4*eta0^2)/(1-2*h*eta0^2)`.
- `axialExponent_defect_bounds`: `0 < 4-K ∧ 4-K < j^2/2`.
- `axialExponent_bounds`: `7999999/2000000 < K ∧ K < 4`.
- `axialStrain_eq_exponent`: for a supplied
  `NaturalProfile.IsNaturalSolution h j Λ P0 a0 f U V Pr` and `t<1`,
  `axialStrain h eta0 V t = K/(1-t)`.
- `spatialDerivative_core_axial`:
  `spatialDerivative (coreVelocity h f V) t (trajectory h eta0 t) e₂
   = (K/(1-t)) • e₂`.

The identities were checked algebraically in Lean. The root bound
`-j/4 < eta0 < -j/5` supplies `0<eta0²<j²/16`. The defect factor divided by
`L` lies strictly between zero and eight. No value of `K` is assumed to equal
four, and the swirl datum does not enter this exponent.

### Exact transport statements and hypotheses

Let `γ = trajectory h eta0` and `g(t)=((1-a)/(1-t))^K`.
`pure_axial_seed_transport` assumes:

1. `p : SmallParameters h j` and
   `hs : NaturalProfile.IsNaturalSolution h j Λ P0 a0 f U V Pr`.
2. `a≤b`, `b<1`, and a supplied `B : MagneticField`.
3. `IdealInductionOn (Ioo a b) (coreVelocity h f V) B`.
4. `ContinuousOn (fun t => B(t,γ(t))) (Icc a b)`.
5. `∀t∈Ioo a b, DifferentiableAt ℝ B (t,γ(t))`.
6. `B(a,γ(a)) = Bz0 • e₂`.

It concludes, for every `t∈Icc a b`:

```text
B(t,γ(t)) = (Bz0 * ((1-a)/(1-t))^K) • e₂.
```

`axial_component_transport` drops assumption 6 and concludes

```text
B(t,γ(t)) 2 = B(a,γ(a)) 2 * ((1-a)/(1-t))^K.
```

No nonzero seed is required for these equality statements. The separate
`amplificationFactor_gt_one` shows the factor exceeds one for `a<t<1`;
`amplificationFactor_pos` proves positivity whenever `a<1` and `t<1`.
The power-law derivative proof establishes positive numerator, denominator,
and ratio before using the real-power identities.

`pure_axial_transport_of_directional_gradient` is the reusable generic theorem:
it assumes a supplied Lagrangian trajectory, the same magnetic regularity and
induction hypotheses, continuity of the velocity Jacobian on the closed path,
and only `Dₓu(t,γ(t)) e₂ = (K/(1-t))e₂` at interior times. Its conclusion is
the same pure-seed formula. Full Jacobian equality to a model is unnecessary.
The core specialization proves Jacobian continuity rather than imposing an
extra hypothesis on the natural solution. Both transport proofs reuse the
material chain rule and `linearODE_eq_zero_on_interval`; neither solves the
full rotating deformation matrix.

These are conditional transport results for a supplied induction solution.
There is no claim of global magnetic PDE existence, divergence propagation,
finite-volume amplification, or an assembled Navier–Stokes magnetic result.
The stretching-form induction predicate keeps divergence conditions separate;
a supplied `IncompressibleInductionOn` provides its `.induction` hypothesis.

### Separate minimal assembled-velocity audit: proved

The exact viscosity-one fields from an explicit common schedule `a` are named
`actualPeriodicVelocity B N0 hN a` and `actualCompactVelocity B N0 hN a` in
`MagneticAxisTransfer`. They are the same formulas retained by the periodic
witness and whole-space extraction:

```text
ASum = potentialSum (fun j => (a j : real)) (physicalQ h) potentialStages
BSum = potentialSum (fun j => (a j : real)) (physicalQ h) directStages
u_periodic = activatedVelocity (MixedPeriodicAssembly.periodicVelocity ASum BSum)
u_compact  = R3CompactCandidate.velocity ASum BSum
           = activatedVelocity (fun w => cutVelocity ASum w + cutPotential BSum w).
```

`slowBase_axis` proves the exact identity, for every `t<1` and every real `z`:

```text
FinalSlowBase.velocity H v upper B (t,z*e₂)
  = physicalQ(h,t,0,z)^(-A(h)) * U(j,physicalEta(h,t,0,z)) * e₂.
```

`slowBase_axis_eq_core` identifies this with any supplied natural solution
using the same `h` and `j`. `axial_derivative_of_line_germ` explicitly requires
differentiability and equality on a LINE NEIGHBORHOOD. It proves equality of
only the axial Jacobian column. Applying it gives `slowBase_axial_derivative`.
No derivative is inferred from equality at one point or merely along the
spacetime trajectory.

`actual_raw_eq_slowBase_germ`, `actual_periodic_eq_slowBase_germ`, and
`actual_compact_eq_slowBase_germ` instantiate the actual potential and direct
sequences. `minimal_transfer_of_slowBase_germ` combines their retained germ
with the slow-base line calculation. `actual_minimal_transfer_eventually`
proves the two required conditions sufficiently late for both final fields.

`selected_schedule_minimal_transfer_late_interval` has the exact quantified
form: for any `B,N0,hN,a`, with `hN : geometricThreshold≤N0`, the actual
`SelectedSchedule ... a`, and a supplied natural solution using
`CorrectionInitialization.ActualPrimary.h` and `nominal.axis.j`, there exists
`T<1` such that for every `T<t<1` and each of the two final velocities:

```text
HasDerivAt γ (u_final(t,γ(t))) t
spatialDerivative u_final t (γ(t)) e₂ = (K/(1-t)) • e₂.
```

The chosen `γ` and `K` use `nominal.axis.small`. `selected_witness` supplies
such a schedule at the selected budget and threshold. Every compact interval
`[aTime,bTime]` with `T<aTime≤bTime<1` lies within this proved interval.
This is a minimal-condition audit, kept separate from the magnetic transport
specialization. It asserts no full natural-core neighborhood or gradient
agreement and no magnetic solution for either final field.

### Correction-by-correction value and axial derivative

All entries refer to velocity contributions at the path. For potentials, the
contribution means their spatial curl, not the undifferentiated potential.
A zero spacetime germ implies zero value and zero axial Jacobian column via
`zero_germ_value_and_axial_derivative`; curl locality first applies this to
potential corrections.

| Term | Velocity value on the path | Axial directional derivative | Exact reason/conditions |
| --- | --- | --- | --- |
| Leading slow meridional field | `q^(-A)*U(j,eta0)*e₂ = γ′` | `(K/(1-t))*e₂` | Prescribed leading axial data and differentiation of the full axial-line identity |
| Positive slow Borel meridional terms, including their Borel cutoffs | Zero | Zero | Positive axial coefficient values vanish for every axial eta; radial averages agree with axial values. `slowSum_eq_leading_of_positive_zero` preserves the identity for the actual sum. No cutoff-derivative estimate is used. |
| Slow-base swirl, leading and positive orders | Zero | Zero | Axisymmetric swirl velocity vanishes on the entire spatial axis; differentiating that line identity gives zero axial derivative. Transverse swirl derivatives can be nonzero and are not identified. |
| Tail gauge subtraction from the base potential | Zero curl contribution | Zero | `finalPotential_sameCurl` holds throughout the open preterminal region. The gauge potential itself need not vanish. |
| Initial potential (initial physical wave plus initial stream mean) | Zero | Zero | `initialPotential_axisZeroOn`; spatial-curl locality, within `localDomain` |
| Positive particular potentials | Zero | Zero | `particular_axisZeroOn`; spatial-curl locality |
| Signed-copy potentials | Zero | Zero | `signed_axisZeroOn`; spatial-curl locality |
| Positive stream-mean potentials | Zero | Zero | `stream_axisZeroOn`; combined in `positivePotential_axisZeroOn` |
| Direct angular stages and their sum, including the initial direct stage | Zero | Zero | `LocalAngularDiagonal.angularSupport`, `directDiagonal_zero_germ`, and schedule local finiteness; the proof uses germs, not small amplitude |
| Zeroth diagonal cutoff of the retained base | No change | No change | Strict plateau `abs((a 0)*q)<1/2`; its derivatives vanish locally |
| Spatial potential/direct cutoffs | No change | No change | `γ(t)` in `SpatialLocalization.plateau`; includes all curl cutoff derivatives |
| Periodization | No change | No change | `MixedPeriodicAssembly.periodicVelocity_eventuallyEq`; other copies do not change the local germ |
| Time activation | No change for `t>3/4` | No change for `t>3/4` | Time switch equals one locally. Earlier it multiplies both spatial value and axial derivative; unrestricted early-time transfer is not asserted. |
| Pressure and force stages | Not a velocity contribution | Not a velocity contribution | They do not enter the two kinematic transfer conditions |

`path_eventually_in_plateaus` proves the required common late-time conditions:
`t<1`, `q(t)<qbig`, `abs((a 0)*q(t))<1/2`, `3/4<t`, and spatial plateau
membership. It uses `q(t)→0` and `γ(t)→0` as `t→1-`, with `D(h)>0`.
Thus the finite chosen schedule value is fixed before selecting the late
interval. No small-amplitude-to-small-derivative inference is made.

### Validation and remaining scope

- Full `lake build`: passed, 11,258 jobs.
- A separate Lean audit imported `MagneticSimilarityGradient`,
  `MagneticCoreAmplification`, and `MagneticAxisTransfer`, then ran
  `#print axioms` for all 40 theorem declarations (11 preserved gradient,
  15 amplification, 14 transfer). Every theorem depends only on `propext`,
  `Classical.choice`, and `Quot.sound`; none depends on `sorryAx`.
- Neither new module contains `sorry` or a new axiom declaration.
- The full build reports four inherited `sorry` warnings in
  `ComparatorChallenges/Euler.lean` and `ComparatorChallenges/NavierStokes.lean`.
- `git diff --check` passed. The existing gradient module was preserved.
- All task changes, including the previously staged gradient and handoff files,
  are included in the milestone commit on `main`; no push is requested.

Remaining work, if requested: specialize the generic magnetic transport theorem
to a supplied induction solution for one of the assembled fields; prove any
additional magnetic PDE existence or solenoidality statements separately.
Full transverse gradient/swirl transfer remains unproved and is unnecessary
for this pure-axial milestone. Resistivity, backreaction, global flow
identification, and finite-volume amplification remain outside this task.

## Historical sessions (superseded by the milestone above)

The rest of this file preserves earlier handoff notes. Statements below about
unfinished compilation or unresolved minimal transfer describe those earlier
sessions, not the current proof status.

## Historical pause state

The sections below, until “Resumed implementation”, record the earlier pause.
The unfinished-compilation statements in this historical section are superseded
by the current status above.

This note records the state when the user paused implementation and requested
that the active prompt and progress be documented. No further Lean changes were
made while writing this note. The new gradient module is unfinished and does
not currently compile. Do not treat its final coefficient theorem as verified.

## Active user request

Continue MHDSingularity from the current local state. Do not implement resistive
MHD, curl form, backreaction, or magnetic amplification.

1. Inspect the final assembled OpenAI Navier–Stokes velocity: locate natural-core
   insertion, all cutoffs/localizations, actual neighborhood agreement with the
   distinguished trajectory, and existing agreement lemmas.
2. If justified by the construction, prove
   `assembled_agrees_with_naturalCore_near_distinguishedTrajectory` on compact
   intervals `[a,b]`, `b < 1`, preferably as genuine neighborhood equality.
3. From genuine local equality prove
   `distinguished_trajectory_isLagrangian_for_assembled` and
   `spatialDerivative_assembled_eq_naturalCore_on_distinguishedTrajectory` at
   interior times. Never infer derivative equality from pointwise equality.
4. In `NavierStokes/MagneticSimilarityGradient.lean`, derive the exact continuous
   linear map `spatialDerivative u_core t (gamma_* t)` in a basis-friendly form.
5. Expose transverse isotropic strain, axial strain, xy rotation/swirl, and all
   axial/transverse coupling entries in terms of `h`, `j`, `eta_0`, `q`, and
   existing profile quantities.
6. Prove the trace of the strain part is zero.
7. Keep the axial coefficient exact. Do not claim `kappa = 4` or `B_z ~ q^-4`.
8. Run `lake build`.
9. Report the exact final velocity, local-agreement status, gradient matrix and
   block structure, remaining profile quantities, theorem names, assumptions,
   and any `sorry` or axioms.

The latest instruction supersedes further implementation for this turn:
“Ok simply document your current prompt and progress so far in markdown document
in the repo currently”.

## Previously completed baseline

The existing modules are:

- `NavierStokes/MagneticInduction.lean`: `MagneticField` aliases the existing
  time-first `VelocityField`. Solenoidality and stretching-form induction are
  separate predicates.
- `NavierStokes/MagneticTrajectory.lean`: endpoint-continuous trajectories with
  interior derivatives, and the material chain rule.
- `NavierStokes/MagneticCauchy.lean`: deformation existence and uniqueness and
  trajectory-level Cauchy transport, reusing `NavierStokes.TangentODE` and
  `Euler.ComparatorBridge.linearODE_eq_zero`.
- `NavierStokes/MagneticSimilarityTrajectory.lean`: the constant-eta natural-core
  trajectory, selected from the inherited unique root of `NaturalAxisData.H`.

Write

```text
D(h) = 1/2 - h
A(h) = 1/2 + h
d(eta) = 1 - eta^2
L(h,eta) = 1 - 2*h*eta^2
U(j,eta) = 4*eta + j
H(h,j,eta) = D(h)*eta + d(eta)*U(j,eta).
```

For the selected root `eta_0`, the proved core path is

```text
q(t) = (1-t)/d(eta_0)
gamma_*(t) = q(t)^D(h) * eta_0 * e_2.
```

The principal existing theorem is
`NavierStokes.MagneticSimilarityTrajectory.distinguished_trajectory_isLagrangian`.
It assumes `NaturalAxisData.SmallParameters h j`, a
`NaturalProfile.IsNaturalSolution`, and `a <= b < 1`. Its `_of_agrees` variant
requires explicit velocity agreement along the path; that hypothesis has not
been discharged for the assembled solution.

The last full baseline build succeeded with 11,255 jobs. The baseline trajectory
theorems were audited and use only `propext`, `Classical.choice`, and `Quot.sound`.
There are inherited comparator challenge `sorry` warnings, independent of those
proofs. The unrelated npm files were removed in the preceding work, and README
was updated. The Lake name `NavierStokesAndEuler` was deliberately retained to
match `lakefile.toml`.

## Construction inspection: established findings

### Exact final witness expression

`NavierStokes/ComparatorTheorem.lean` obtains its candidate from
`ActualCandidateAssembly.selected_candidate`.

In `NavierStokes/ActualCandidateAssembly.lean`:

- `Witness` (around line 1121) existentially supplies a selected schedule
  `a : ℕ → ℕ`, the extensions, forcing, and candidate properties.
- `selected_witness` specializes it to the selected budget and threshold.
- `selected_candidate` unpacks that witness; there is no single exported named
  selected velocity definition here.
- The exact viscosity-one periodic candidate velocity in that witness is

```lean
TimeLocalization.activatedVelocity
  (MixedPeriodicAssembly.periodicVelocity ASum BSum)
```

where `ASum` and `BSum` are `SolenoidalDiagonal.potentialSum`s, using scales
`fun j => (a j : ℝ)`, `PhysicalWaveSum.physicalQ h`, and the selected potential
and direct stage sequences. The raw velocity is

```lean
MixedPeriodicAssembly.velocity ASum BSum
-- spatialCurl ASum + BSum
```

The whole-space comparator route was not fully traced in this session. Do not
silently conflate its candidate or viscosity rescaling with the periodic
viscosity-one witness above.

### Cutoffs and neighborhoods

- `TimeLocalization.activatedVelocity u z = timeSwitch z.1 • u z`.
- `TimeLocalization.activatedVelocity_zero_early`: zero when `|t| <= 3/8`.
- `TimeLocalization.activatedVelocity_eq_late`: equals `u` for `3/4 <= t`.
- `TimeLocalization.activatedVelocity_eventuallyEq_late`: full spacetime germ
  equality for `3/4 < t`.
- `SpatialLocalization.spatialCutoff` uses
  `cutoff (16 * radialSquare x) * cutoff (4 * x 2)` and acts on potentials (and
  on the direct field separately). All curl derivatives of the cutoff are kept.
- `MixedPeriodicAssembly.periodicVelocity` periodizes the localized potential
  curl and the localized direct field separately.
- `MixedPeriodicAssembly.periodicVelocity_eventuallyEq` gives full spacetime
  neighborhood equality to the raw mixed velocity when the spatial point is
  in `SpatialLocalization.plateau`.
- `GermCandidateAssembly.potentialSum_eq_base_germ` uses local finiteness,
  zero germs of initialization/stage corrections, and the strict zeroth-cutoff
  condition `|scales 0 * q w| < 1/2`.
- `MixedAxisPreservation.mixedDiagonal_eq_base_germ` gives a true neighborhood
  equality to the **base curl**, under its axis/domain/support/scale conditions.
- `SolenoidalDiagonal.spatialCurl_eventuallyEq` transfers potential germs to
  velocity germs.
- `ResidualRegularity.space_fderiv_congr` transfers full spacetime germs to
  ordinary spatial Fréchet derivatives. It requires no differentiability
  assumption because it uses locality of `fderiv`.

### Important obstruction: natural core versus slow base

The actual inserted base is
`TailGaugePotential.finalPotential H v upper bandFloor`, whose curl is related by
`TailGaugePotential.finalPotential_sameCurl` to
`FinalSlowBase.velocity H v upper bandFloor`.

`FinalSlowBase.velocity` is a `SlowBorelBase.baseVelocity` constructed from a
Borel sum of slow profiles. It is not definitionally
`NaturalCore.coreVelocity`. The natural profiles enter its leading coefficients
through the nominal/aligned/modulated hierarchy, including:

- `AssembledSlowBase.nominalHierarchy_base`
- `AssembledSlowBase.nominalCoefficients_zero_fields`
- `EntranceAlignedBase.modulated_zero_fields`
- `EntranceAlignedBase.modulated_leading_axis`
- `EntranceAlignedBase.modulated_positive_axis`

The last lemma proves positive-order `phi`, `axial`, and `pressure` values vanish
**on the axis**. It does not prove they vanish in a neighborhood.

`GlobalSlowProfiles.profiles_inner_eq` says the positive profiles agree in an
inner region with the original local slow hierarchy. That hierarchy solves
inhomogeneous equations involving preceding diffusion:
`SlowRecursion.sequence_positive_order`.

Do not misread `EntranceAlignedBase.positive_coefficients_zero`: its conclusion
is about `SlowExpansionResidual.angularCoefficient` and `axialCoefficient`
(residual coefficients), not about the velocity profiles vanishing.

Consequences:

1. The requested unrestricted agreement on every `[a,b]` with `b < 1` is false
   for the activated candidate: it is zero at early times whereas the
   distinguished natural-core axial velocity is nonzero.
2. Even late, inspected lemmas supply neighborhood agreement with the **slow
   base**, not with the natural core. No late neighborhood equality theorem
   between the assembled velocity and natural core was proved.
3. This inspection does not prove that such late equality is impossible for
   every particular constructed profile; it establishes that it cannot be
   inferred from the cited axis-value lemmas.
4. A promising alternative is an actual axis-jet calculation: in an
   axisymmetric smooth velocity, the first Cartesian derivative only uses
   axial derivatives of axis meridional data and axis swirl data. Those may
   agree exactly even if whole neighborhoods of the fields differ. This must
   be proved using structure and derivative identities, not inferred from
   equality along a curve. This alternative has not yet been implemented for
   the assembled slow base.

No new assembled-velocity definition or agreement/transfer theorem has been
written in this interrupted session.

## Current new file and exact calculation

The only new Lean file in the working tree at the pause is
`NavierStokes/MagneticSimilarityGradient.lean` (untracked at the time of writing).
Its namespace is `NavierStokes.MagneticSimilarityGradient`.

The proposed exact core matrix is

```text
          [ -alpha/2   -rot       0 ]
Du_core = [  rot       -alpha/2   0 ]
          [  0          0      alpha ]
```

This is encoded as a continuous linear map `axisOperator alpha rot`, not merely
as a matrix abbreviation. Its transverse strain is `-alpha/2`, its axial strain
is `alpha`, and the four axial/transverse couplings vanish. Positive `rot` means
counterclockwise rotation, hence the negative `(0,1)` entry. The trace is zero.

The generic axis-gradient theorem starts with the existing formulas in
`AxisymmetricFields.velocity_zero`, `velocity_one`, and `velocity_two`, proves
local equality to their Cartesian expression using `C²` profile regularity,
and differentiates that expression. It does not infer a derivative from a
single point's value.

The coefficient definitions and intended exact formulas are

```text
alpha = partialZ (NaturalCore.meridionalPotential h V) (t,0,pathZ h eta t)
rot   = -partialS (NaturalCore.swirlPotential h f) (t,0,pathZ h eta t)

axialCoefficientExact(h,j,eta)
  = [4*d(eta) - 2*A(h)*eta*U(j,eta)] / L(h,eta)

alpha = q(t)^(-1) * axialCoefficientExact(h,j,eta)
rot   = q(t)^(-h) / q(t) * a0(eta).
```

These formulas concern the velocity gradient. `axialCoefficientExact` is **not**
defined as a magnetic exponent. No amplification, `kappa = 4`, or asymptotic
claim has been introduced. The swirl still contains the prescribed axis datum
`a0(eta)`. The axial formula has no remaining unknown radial profile quantity.
The closed axial formula is mathematically derived but its final Lean algebra
step remains unfinished, as detailed below.

Declarations currently written:

- `axisOperator`
- `axisOperator_apply`
- `axisOperator_matrix`
- `axisOperator_trace`
- `spatialDerivative_velocity_on_axis`
- `axialStrain`
- `swirlRate`
- `spatialDerivative_naturalCore_on_trajectory`
- `axialCoefficientExact`
- `swirlRate_eq`
- `meridionalPotential_axis`
- `axialStrain_eq` — unfinished compilation

The last Lean invocation reported only the final `axialStrain_eq` algebra error.
Earlier declarations elaborated without reported errors in that invocation,
but the module as a whole has not passed, has no successful new build, and has
not received a final axiom audit.

## Exact unfinished proof state

Last command:

```sh
lake env lean NavierStokes/MagneticSimilarityGradient.lean
```

It exited with code 1. The remaining error is near line 206, the first `calc`
step at the end of `axialStrain_eq`, using `by ring`.

The proof already establishes:

```text
q^(1-D) * q^(-A-1) = q^(-1)             -- hp1
q^(-A) / q^D = q^(-1)                  -- hp2
```

It obtains the axial derivative by differentiating the meridional potential
identity on the entire spatial axis, using the inherited coordinate derivative
lemmas. After substitution at the path, the remaining regrouping involves

```text
1 / (q^D * L)   versus   (1/q^D) * (1/L).
```

`ring` treats the inverse of the product as a separate atom and does not close
the equality. A likely next fix is to normalize product inverses/division
before `ring` (for example `simp only [div_eq_mul_inv, mul_inv_rev]` with the
applicable real-field lemma), or use `field_simp` with proved nonzero `q^D`
and `L`. This suggestion has not been tried. Avoid altering the mathematics
or adding assumptions merely to make the algebra tactic succeed.

Other Lean details already resolved:

- The imported scope reserves `ω`; the file uses the name `rot` instead.
- `HasFDerivAt` has `mul_const`, not the attempted `div_const`; division by two
  was handled as multiplication by `1/2`.
- Give profile-direction derivatives explicit types to avoid metavariables.
- Pull eventual smoothness back using `ContinuousAt.eventually`.
- The field-level axis-operator proof uses actual local equality and
  `EventuallyEq.fderiv_eq (𝕜 := ℝ)`.
- `mem_setOf_eq` was replaced by `mem_ofPred_eq` to avoid deprecation warnings.

## Regularity and parameter assumptions in the new file

- Generic Cartesian axis-gradient theorem: `ContDiffAt ℝ 2` for both scalar
  potentials at the profile point, and `x 0 = x 1 = 0`.
- Natural-core specialization and coefficient formulas: `0 < h < 1/2`,
  `NaturalProfile.IsNaturalSolution h j Λ P0 a0 f U V Pr`, `eta^2 < 1`, `t < 1`.
- The gradient formulas work for any such constant eta; they do not need the
  root condition. Specialize to the distinguished eta with
  `distinguishedEta_sq_lt_one` and the existing small-parameter bounds.
- The existing `IsNaturalSolution` packages more regularity/PDE data than the
  isolated gradient calculation minimally needs. It is used to reuse the
  established smoothness and prescribed axis values.

No literal `sorry` or new axiom declaration was intentionally added. Since the
new module does not compile, do not claim it is fully verified or axiom-audited.

## Next actions after resuming implementation

1. Resolve the last rational-algebra normalization in `axialStrain_eq`.
2. Add a concise combined closed-form operator/matrix theorem if useful.
3. Decide the correct assembled-flow theorem: restrict to sufficiently late
   times and distinguish true local equality to the slow base from a separate
   first-axis-jet comparison to the natural core. Do not insert a hypothetical
   natural-core germ as if it were discharged by the construction.
4. Trace the chosen schedule, local domain, zeroth cutoff, direct-field zero
   germs, spatial plateau, and time-switch plateau for the distinguished path.
5. Prove the valid assembled trajectory/gradient connection, or precisely
   document remaining mathematical obligations without asserting agreement.
6. Run `lake build`, then audit all new principal theorems with `#print axioms`.
7. Report all assumptions and any remaining limitations. Keep amplification,
   resistivity, curl form, global flow derivatives, and backreaction deferred.

## Environment and working-tree notes

- Repository: `/mnt/ssd/homedirs/harpe-svc/MHDSingularity`.
- Tools run through bash. The ordinary filesystem sandbox has repeatedly failed
  to initialize (`bwrap: loopback: Failed RTM_NEWADDR: Operation not permitted`).
  Inspection and edits have therefore used explicit escalated command calls.
- At the pause, `git status --short` showed only
  `?? NavierStokes/MagneticSimilarityGradient.lean`; writing this note also adds
  `MHD_PROGRESS.md`.
- No commit or push was performed in this session.


## Resumed implementation

### Completed proofs and validation

The last `axialStrain_eq` step now normalizes division and inverses of products
with `simp only [div_eq_mul_inv, mul_inv_rev]` before `ring`. No mathematical
assumption was added. The following combined results were added:

- `spatialDerivative_naturalCore_on_trajectory_exact`: the full continuous
  linear map with both coefficients substituted.
- `spatialDerivative_naturalCore_on_distinguishedTrajectory`: specializes that
  map to `distinguishedEta p`, under `SmallParameters h j`, the natural-solution
  predicate, and `t < 1`.
- `axisOperator_strain_trace`: zero trace of `axisOperator alpha 0`.

Together with `axisOperator_matrix`, these give precisely the matrix in the
calculation section. Its symmetric part is `diag(-alpha/2,-alpha/2,alpha)`;
its skew part is the xy rotation with entries `-rot` and `rot`. The four
axial/transverse couplings are zero. The general calculation assumes `0<h<1/2`,
`eta^2<1`, `t<1`, and `NaturalProfile.IsNaturalSolution`; the root condition is
only needed to identify the curve as Lagrangian. The only remaining prescribed
profile datum in the coefficients is `a0(eta)`.

Validation: `lake build` succeeded with 11,256 jobs. A separate Lean file imported
the built module and printed axioms for all eleven theorem declarations; every
result listed only `propext`, `Classical.choice`, and `Quot.sound`. No magnetic
amplification or exponent claim was introduced.

### Whole-space candidate traced

`ComparatorR3Theorem.navier_stokes_breakdown_R3` extracts
`R3CompactCandidate.selected_compact_candidate`. In `R3ActualCandidate.lean`,
this extracts the same `ActualCandidateAssembly.selected_witness` sums and
applies `R3CompactCandidate.of_localized_fields`. Its exact viscosity-one
velocity is:

```lean
R3CompactCandidate.velocity ASum BSum
-- TimeLocalization.activatedVelocity
--   (fun z => SpatialLocalization.cutVelocity ASum z +
--             SpatialLocalization.cutPotential BSum z)
```

Thus the whole-space field retains the spatial cutoff and its curl derivatives,
but has no periodization. Its force is `R3CompactCandidate.compactForce forcing`.
The periodic velocity remains the activated `MixedPeriodicAssembly.periodicVelocity`
from the earlier section. The comparator adapters rescale the force to
`nu^2 • forcing (nu*t,x)` and argue by normalization of hypothetical solutions;
the exact gradient proved here is for the unrescaled natural core.

### Precise remaining assembled-flow obligations

Let `eta = distinguishedEta p`, `d = 1-eta^2 > 0`,
`q(t) = (1-t)/d`, `z(t) = eta*q(t)^D(h)`, and let `a` be a schedule supplied by
`selected_witness`. `MixedCandidateWitness.SelectedSchedule` supplies `1 ≤ a 0`,
positivity, doubling, strict monotonicity, divergence of the real scales, and
`1/(a j : real) < qbig`. The following are sufficient geometric conditions for
using the inspected germ lemmas at `(t, trajectory h eta t)`:

1. `t < 1` and `q(t) < qbig`, putting the point in `localDomain`.
2. `(a 0 : real)*q(t) < 1/2`, the strict zeroth-cutoff plateau.
3. `|eta|*q(t)^D(h) < 1/8`, the spatial plateau; radial square is zero.
4. `3/4 < t`, the open time-activation plateau.

For `t<1`, the first two bounds follow respectively from
`t > 1-d*qbig` and `t > 1-d/(2*(a 0 : real))`. Since `D(h)>0`, the third also
holds sufficiently late. These threshold deductions and their uniform use on
compact intervals `[aTime,bTime]` lying after a common threshold have not yet
been packaged as Lean theorems for the selected witness. They do not establish
agreement on arbitrary early intervals.

At such points, `initialPotential_axisZeroOn` and
`positivePotential_axisZeroOn` supply the actual potential correction germs;
`GermCandidateAssembly.potentialSum_eq_base_germ` then identifies the potential
sum germ with `TailGaugePotential.finalPotential`. To obtain the full mixed
velocity germ, also instantiate the direct-series zero-germ/local-finiteness
argument with `LocalAngularDiagonal.rawSeries` and its angular supports.
The existing actual-candidate origin proof uses the direct field's axis VALUE
identity, so that proof alone does not supply this derivative-level step.
Compose the potential curl germ, direct zero germ, spatial plateau, and time
plateau, and use `TailGaugePotential.finalPotential_sameCurl` on the open
preterminal region. The resulting comparison is to `FinalSlowBase.velocity`.

The decisive additional mathematical obligation is then to compute the first
Cartesian axis derivative of that Borel-summed slow base. This requires:

- Axis identities for the actual summed meridional data on an axial interval,
  including all Borel cutoff factors, so their axial derivative can be computed.
- The radial derivative of the actual summed swirl potential on the axis.
  Positive-order `phi` values being zero is insufficient by itself to identify
  that derivative.
- Identification of the leading profile and swirl normalization with the
  particular natural solution used in the gradient theorem.

`modulated_leading_axis` identifies the zeroth axial coefficient with
`4*eta+j`; `modulated_positive_axis` makes positive `phi`, axial, and pressure
VALUES vanish on the axis. Neither is a neighborhood identity of velocities.
The new generic `spatialDerivative_velocity_on_axis` can be used once the
actual slow-base potentials, their regularity, and those two derivative data
are identified. A proved axis-value identity would suffice for the Lagrangian
transfer; the gradient transfer additionally needs the independently proved
axis derivative identities or a genuine neighborhood equality.

No theorem named `assembled_agrees_with_naturalCore_near_distinguishedTrajectory`,
`distinguished_trajectory_isLagrangian_for_assembled`, or
`spatialDerivative_assembled_eq_naturalCore_on_distinguishedTrajectory` is claimed
by this work. The unresolved identification is explicit rather than hidden in a
new hypothesis advertised as a construction theorem.
