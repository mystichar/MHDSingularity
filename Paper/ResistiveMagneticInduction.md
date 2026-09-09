# Paper II: passive resistive induction and fixed-slab comparison

## Physical periodic heat interface (after 9618457)

This checkpoint concerns the heat operators needed for a later induction
construction. It preserves every pre-existing Lean file, including the
comparison/uniqueness package and the Paper I results. It constructs no
resistive induction solution and makes no positive-diffusivity terminal claim.

All names below are in `NavierStokes.ResistiveMagnetic.PeriodicGaussian`
unless a different namespace is specified.

### Geometry, spaces, and the same Gaussian operator

`PeriodicField` remains the original complete uniform space of continuous
unit-periodic `Space -> Space` fields, where `Space` is Euclidean R3.
`PeriodicValue V` extends its codomain to real Banach spaces, including
`Space ->L[Real] Space`. `periodicValue_space` is a definitional equality
with the original space, and `valueLine_eq_lineOperator` and
`valueSpatial_eq_spatialOperator` identify the extended operators with the
original ones. The cylinder R3 x T is never identified with the physical
three-torus. There is no zero-mean, cover-L2, or vector-potential requirement.

`derivativeGraph_closed` proves that the pairs (f,G) satisfying
`HasFDerivAt f (G x) x` at every x form a closed linear subspace of the
product of two periodic uniform spaces. The proof uses uniform convergence
of the derivatives and pointwise convergence of the functions.
`periodicC1ValueCompleteSpace` proves completeness. `PeriodicC1` is its
Space-valued specialization, with the exact norm

```
||f||_C1 = max(||f||_infinity, ||Df||_infinity).
```

`c1_fderiv` identifies the stored derivative with the actual Frechet
derivative. `c1Inclusion` is a continuous linear injection into the original
`PeriodicField`; `c1Value_injective` proves injectivity. `c1Constant` contains
every constant vector, has zero derivative, and has norm equal to that
vector's norm. No all-orders Banach hierarchy is introduced.

### Semigroup, smoothing, and time budget

Write A(r) for the original `spatialOperator r`, r>=0. The exact statements
`spatialOperator_zero` and `spatialOperator_semigroup` are

```
A(0) = id,
A(r+s) = A(r).comp(A(s)).
```

The proof combines Gaussian convolution in the same direction, commuting
physical translations in different directions, and Bochner Fubini under
finite Gaussian measures with uniform integrable bounds. Zero variance uses
the original Dirac convention.

`heat eta_m tau = A((2*eta_m*tau).toNNReal)` uses elapsed physical time.
`heat_semigroup` requires eta_m,r,s>=0; `heat_zero`, `heat_norm_le`, and
`heat_constant` export identity, contraction, and constant preservation.
`heat_eq_physicalAverage` gives the exact bridge to the earlier absolute-time
formula. `heat_strong_continuous` and `heat_joint_continuous` prove uniform-norm
strong continuity for every datum, including time zero. The clamped real-time
extension is continuous, but no negative-time semigroup is asserted.
There is no assertion of operator-norm continuity at zero.

For positive variance, `valueLine_hasDerivAt` proves a strong translation
derivative for **merely continuous** input. It rewrites translation of the
Gaussian average as integration against the shifted density and differentiates
that density. `shiftedGaussian_derivative_bound` and
`shiftEnvelope_integrable` justify differentiation under the Bochner integral.
The derivative's bound uses the proved finite Gaussian first absolute moment.
`translate_hasFDerivAt_coordinates` combines the three genuine directional
derivatives, using continuity of partial derivatives, into a full derivative.

`valueSpatial_hasFDerivAt`, `valueSpatial_fderiv_bound`, and `heat_fderiv_bound`
therefore give genuine smoothing, with no differentiability hypothesis on f:

```
||D T_eta(tau) f||_infinity
  <= C_heat / sqrt(eta_m*tau) * ||f||_infinity,
C_heat = heatConstant = 3 * EulerGaussianCylinderHeat.gaussianAbsMoment 1.
```

This is a bound for the full Frechet operator norm, not only separate
coordinate entries. The three-coordinate sum gives a nonoptimal constant;
only scalar Gaussian estimates are reused from the cylinder modules. The
function space remains the physical three-dimensional periodic cover.
C_heat is a finite nonnegative real independent of eta_m, tau, and f.
The variance estimate retains the stronger denominator sqrt(2*eta_m*tau).

For eta_m,tau>0, `heatGain eta_m tau heta htau` is a constructed bounded
linear map `PeriodicField ->L[Real] PeriodicC1`, with

```
c1Inclusion (heatGain eta_m tau heta htau f) = heat eta_m tau f,
||heatGain eta_m tau heta htau|| <= 1 + C_heat/sqrt(eta_m*tau).
```

`gainVariance_joint_continuous` and `heatGain_joint_continuous` prove joint
positive-time/input continuity in the target C1 norm. The proof factors off
a fixed positive smoothing step and uses the semigroup plus injectivity of
the C1 inclusion. `lineC1_derivative`, `spatialC1_derivative`, and
`heatC1_derivative` prove derivative commutation by integrating translations
in the proved complete derivative graph. `heatC1_strong_continuous` includes
time zero for C1 input. This is not C0-to-C1 continuity at zero.

`heatKernel eta_m heta tau` agrees with heatGain for tau>0 and is zero
otherwise. Its zero value is a Volterra integration convention, separate
from the identity heat operator at zero. `heatKernel_joint_continuous`,
`heatKernel_bound`, `kernelMajorant_integrable`, and
`kernelMajorant_integral` supply, for eta_m>0 and T>=0,

```
k_eta(tau) = 1 + C_heat/sqrt(eta_m*tau),
Integral_(0,T] k_eta(tau) d tau = T + 2*C_heat*sqrt(T/eta_m).
```

`kernelMajorant_integral_zero` includes T=0 explicitly. Bounds may deteriorate
as eta_m tends to zero.

### Generator and established regularity

`c1_translation_hasDerivAt` uses the fundamental theorem of calculus and
bounded point evaluations to turn actual spatial C1 derivatives into strong
uniform-space translation derivatives. `c1OfContDiff` obtains the required
uniform derivative field for every supplied classical C1 periodic input from
the physical compact cell.

`realValueLine_generator_zero` and `realValueLine_generator_pos` prove the
half-second-directional-derivative variance generator. For supplied C2
periodic f, `variance_generator_limit` and `variance_generator_zero` add its
three coordinate contributions. `laplacianField_eq_spatialLaplacian` identifies
the resulting bounded continuous periodic field with the project's actual
`spatialLaplacian` convention. `heat_generator_zero` and
`heat_generator_limit` state, for eta_m>=0,

```
HasDerivWithinAt (fun tau => heat eta_m tau f)
  (eta_m • laplacianField f hf) (Ici 0) 0,
lim_(tau -> 0+) tau^(-1) • (heat eta_m tau f - f)
  = eta_m • laplacianField f hf.
```

The limit is in the uniform function-space norm. The C2 hypothesis is on
the supplied spatial input; no bounded generator on the entire C0 space is
claimed. Zero diffusivity is included.

`valueSpatial_contDiff_two` obtains positive-time spatial C2 from C0 input
by composing two C1 gains, with derivative-valued averaging and the proved
commutation identity. `laplacianField_heat` proves Laplacian commutation.
`variance_generator_pos` and `heat_hasDerivAt` give positive-time derivatives
in the uniform space for merely continuous input. `heat_equation` is exactly

```
temporalDerivative (fun p => (heat eta_m p.1 f).val p.2) tau x
  = eta_m • spatialLaplacian (fun p => (heat eta_m p.1 f).val p.2) tau x
```

for eta_m,tau>0. The left time derivative uses only positive heat times;
it does not invert the heat operator. The proved bridges
`temporalDerivative_of_uniform_derivative` and
`heat_equation_of_uniform_derivative` convert the uniform derivative into
the project's pointwise operators; `heat_equation` instantiates both its
spatial regularity and uniform time derivative from the actual heat operator.
The established exports are strong C0
continuity through zero, positive-time C1 target-norm continuity, spatial C2
slices, and uniform-space time differentiability at positive times. Joint
C-infinity regularity is not asserted.

### Next existence handoff: inspected Volterra hypotheses

The pinned `EulerVolterraConvolution.exists_mild_solution` accepts real Banach
X, a real normed Y, elapsed slab length T>=0, K:Real->Y->L[Real]X, and k, with:

1. joint continuity of `(r,y) -> K r y` on `(0,infinity) x Y`;
2. integrability and nonnegativity of k on `(0,T]`;
3. `||K r y|| <= k(r)*||y||` on that interval;
4. a free path in `C(Icc 0 T,X)` and a jointly continuous source
   `F : Icc 0 T -> X -> Y`;
5. nonnegative R,M,L, a source bound M and Lipschitz constant L on the
   radius-R ball, and the two inequalities
   `||free|| + kernelMass(T,k)*M <= R` and `kernelMass(T,k)*L < 1`.

Use **X=PeriodicC1**, **Y=PeriodicField**, K=`heatKernel eta_m heta`, and
k=`kernelMajorant eta_m`. Items 1--3 and completeness are constructed here.
The initial path is `tau -> heatC1 eta_m tau B_a`; its continuity through zero
is proved, and a constant axial seed belongs to C1 and is preserved.
The exact kernel mass above tends to zero with T for fixed eta_m>0, as needed
for a short-time contraction. The final contraction inequalities still need
to be proved after constructing the source adapter.

The next source is the **unprojected linear** map, in the existing physical
clock and viscosity-one prescribed NS velocity,

```
Source(tau,B)(x) = -(c1Derivative B)(x) (u(a+tau,x))
                  + D_x u(a+tau,x) ((c1Value B)(x)).
```

Construct its bounded-linear C1-to-C0 product adapter and prove joint time
continuity. On a fixed slab the expected norm/Lipschitz bound is U_b+L_b,
where `Comparison.actual_velocity_bounds` already supplies the uniform
bounds on u and Du for the SAME selected actual periodic velocity.
`MagneticPeriodicCoefficient.actualOnSlab` supplies the existing continuous
coefficient/derivative paths. The older pointwise `source_difference_bound`
requires smooth fields; it should not be silently used as a C1-space theorem.

Still required, after that adapter: instantiate the local Volterra budgets;
prove mild uniqueness and linear continuation over each fixed preterminal
slab; establish sufficient compatible higher regularity and the mild-to-PDE
bridge; prove forward-endpoint divergence preservation; prove restriction
compatibility and glue one solution for each eta_m on `[a,1)`; then apply the
already-completed ideal/resistive comparison and finite-gain argument with
the correct fixed-data quantifiers. First-derivative heat smoothing alone is
not a classical **induction** existence theorem. None of these steps is
implemented in this checkpoint. Fixed-diffusivity terminal behavior, a
magnetic length scale, and a quantitative conductivity threshold remain open.

### Heat-checkpoint validation

The targeted `ResistivePeriodicHeatEquation` build passes (9,338 jobs), and
the full `lake build` passes (11,312 jobs). The new
`scripts/audit_resistive_heat.lean` checks all 199 new named declarations and
fourteen explicit analytic/construction dependencies. Its 213 checks and the
358 checks in all seven previous magnetic audit scripts pass: 571 total.
Only `propext`, `Classical.choice`, and `Quot.sound` occur, or no axioms.
There is no new admitted proof or axiom. The four inherited challenge
admissions remain unchanged and are absent from the audited dependencies.
New linter warnings concern unused section variables only.


## Completed periodic PDE-to-comparison checkpoint (after 4d513f8)

This checkpoint proves comparison and uniqueness for supplied resistive
solutions. It constructs the comparison's ideal witness and discharges its
coefficient bounds. It does **not** construct a resistive solution. The
physical domain is the unit-periodic cover of R3; time and fluid viscosity
are the existing physical time and viscosity one. Magnetic diffusivity
eta_m is a separate nonnegative real parameter.

### Main statement and quantifiers

In `NavierStokes.ResistiveMagnetic.Comparison`,
`periodic_comparison_main` proves the following quantifier order:

```
exists scales, hsel : Selected scales, forcing, a, ha : a < 1,
  0 < a and
  CandidateProperties (velocity scales) (pressure scales) forcing and
  ContDiff Real infinity forcing and the existing CandidateConsequences,
  for every Bz0,
    let I = (actualData budget threshold geometry scales hsel a ha).magnetic Bz0;
    ClassicalSolution (velocity scales) I a 1 Bz0 and
    separate spatial smoothness of I at every a <= t < 1 and
    for every a < b < 1,
      joint continuity of Delta I on [a,b] x R3 and
      exists C >= 0, for every eta_m >= 0 and every supplied B,
        [regularity, periodicity, resistive PDE and matching seed] imply
        for every t in [a,b] and every x,
          norm(B(t,x)-I(t,x)) <= eta_m*C.
```

The `ClassicalSolution` conclusion includes one periodic divergence-free
ideal field, joint continuity on `[a,1)`, joint C1 regularity for a<t<1,
initial constant axial data, and stretching-form ideal induction. The field
I is the actual glued flow construction, not an arbitrary witness from
`MagneticConclusions`. The theorem obtains the compatible selected schedule,
pressure and forcing from the existing closed `MagneticPeriodicMain.periodic_main`.
There is no new upstream compatibility or magnetic-existence axiom.

The supplied resistive field needs exactly:

- joint continuity on `[a,b] x R3` and unit coordinate periods at every slab time;
- differentiability of `t -> B(t,x)` at every a<t<b and x;
- `ContDiff Real 2 (fun x => B(t,x))` for every a<t<b;
- `ResistiveInductionOn eta_m (Ioo a b) (velocity scales) B`;
- `B(a,x)=Bz0 • coordinateVector 2` for every x.

No derivatives or PDE before a, or at either endpoint, are required of B.
No divergence or axial-invariance hypothesis on B is needed for comparison.
The new result does not separately propagate its divergence.

`actual_ideal_resistive` exports the more explicit choice of finite L,D>=0,
with the actual bounds valid everywhere on the **closed** slab, before eta_m
and B are quantified. Its estimate uses the existing exact real constant

\[
 C_b=D\sqrt{\frac{\exp((2L+1)(b-a))-1}{2L+1}},\qquad
 \|B(t,x)-I(t,x)\|\le\eta_m C_b.
\]

`actual_comparison_constant` exports the same result using a single C.
L,D,C may depend on the schedule, seed, a and b, but never on eta_m or the
supplied resistive field. They are finite and nonnegative. D=0 and eta_m=0
are included. These are fixed-slab estimates, with no uniformity as b tends
to one and no computed numerical conductivity threshold.

### Proof of the scalar comparison

`ResistiveMagnetic.Slice.comparison` is a reusable theorem for a scalar q
with the same endpoint continuity, unit periods, interior time derivative
and C2 spatial slices. For a<b, eta_m>=0, c>0 and F0>=0, it proves

\[
 q_t+D_xq[u]-\eta_m\Delta q\le cq+F_0,\quad q(a,x)\le0
 \quad\Longrightarrow\quad
 q(t,x)\le F_0\frac{e^{c(t-a)}-1}{c}.
\]

There is no regularity, boundedness, periodicity or divergence assumption on
u in this scalar theorem. The proof applies an integrating factor, subtracts
an epsilon multiple of elapsed time, and takes a maximum on `[a,t]` times
a compact unit cell, initially with t<b. Periodicity lifts a cell maximizer
(including one on its boundary) to a global spatial maximizer. Its gradient
is zero and its Laplacian nonpositive. A slope limit from past times makes
the time derivative nonnegative. This contradicts the strict PDE inequality.
The initial-time alternative is excluded using initial data; continuity
extends the conclusion to b. No derivative of a time-dependent supremum is
introduced.

`ResistiveSquaredNormSlices.lean` uses slice derivatives, matching the
vector PDE conventions. `Slice.scalarTime_eq` and `scalarPartial_eq` bridge
the joint operators where the joint derivative exists; `scalarLaplacian_eq`
states its additional joint-partial hypotheses explicitly. The comparison
itself uses no such extra joint-derivative assumptions.
`Slice.squared_equation` proves, for the forced difference W,

\[
 (\partial_t+u\cdot\nabla-\eta_m\Delta)\|W\|^2
 =2\langle W,D_xu[W]\rangle
 -2\eta_m\sum_i\|D_xW[e_i]\|^2+2\eta_m\langle W,f\rangle.
\]

`Comparison.difference_equation_of_slices` derives W=B-I and f=Delta I
from the two PDEs. `Slice.squared_inequality` bounds the right side by
`(2L+1)*norm(W)^2+eta_m^2*D^2` using the existing Young inequality.
`Comparison.forced_estimate` applies the proved scalar comparison, then
`norm_le_of_squared_barrier`. `Comparison.ideal_resistive` composes these
steps. Neither final theorem assumes a barrier or an error bound. The
stronger joint-smooth results in `ResistiveSquaredNorm.lean` are unchanged.

### Actual ideal Laplacian continuity and bounds

The new `ResistiveMagnetic.Jets.Slab.magnetic_jets` proves joint continuity
of every finite spatial jet of the **finite-slab** Eulerian field on its
closed time subtype. The proof is:

1. `path_jets` evaluates spatial derivatives of a smooth function into the
   uniform continuous-path Banach space. `Slab.F_jets` applies it to the
   spatial derivative of the actual forward path family. This supplies all
   required forward derivatives with their time continuity.
2. `Slab.inverseF_jets` uses smoothness of operator inversion at the actual
   invertible F and the parameterized composition chain rule. `Y_derivative`
   identifies DY with inverse F evaluated at Y. `Y_jets` instantiates
   `EulerGevreyComposition.continuous_iteratedFDeriv_of_fderiv_eq_comp`,
   discharging its coefficient smoothness, coefficient jets and derivative
   identity; no inverse-jet continuity is postulated.
3. Composing F with Y and applying the fixed seed gives the actual magnetic
   field's spatial jets. `laplacian_eq_jet` traces the second derivative.
4. For the glued `MagneticPeriodicSolution.Data.magnetic`, a cofinal endpoint
   strictly beyond b gives one compatible finite-slab representative on all
   of `[a,b]`. Equality of entire spatial slices identifies their Laplacians,
   including at a. `Data.magnetic_laplacian_continuousOn` exports that joint
   continuity. `magnetic_laplacian_periodic` supplies its unit periods;
   `magnetic_laplacian_bound` applies the existing compact-cell bound.

All-order **spatial-jet continuity** on finite slabs is proved; joint
C-infinity is not asserted. The previously proved joint C1 interior
regularity and separate spatial smoothness of the glued field remain the
exported classical regularity. Together with `actual_velocity_bounds`, the
new Laplacian theorem discharges both coefficient hypotheses in the actual
comparison package.

### Uniqueness, remaining analytic obligations, and scope

`Comparison.resistive_unique` applies the same squared-norm argument to the
difference of two resistive fields with the same u, eta_m and initial data.
Its forcing is zero, so the norm vanishes on the whole closed slab.
`actual_resistive_unique` supplies the actual velocity-gradient bound.
The common initial field may be arbitrary. Both theorems have the forward
endpoint conventions and regularity stated above. They assert uniqueness
in this class, without constructing a member of it.

The comparison and uniqueness checkpoint has no remaining analytic gap.
**Resistive existence is still outstanding:** a correct physical-periodic
heat generator and smoothing estimates, derivative-loss source estimates,
short-time construction, continuation, compatible spatial regularity and
slab gluing, and forward-endpoint divergence preservation for the eventual
constructed field still need to be instantiated. No solution B_eta on
`[a,1)` is constructed here. The earlier conditional finite-gain theorem is
unchanged; this run does not package a closed finite-gain result.

Nothing in this checkpoint determines fixed-positive-diffusivity terminal
behavior, a sharp gain law, a magnetic length scale, an eigen-curvature
closure, a numerical threshold, energy blow-up, stability, attraction, or
magnetic backreaction. The older conditional curvature-mode results remain
separate.


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

## Historical checkpoint 4d513f8: partial progress after 3a9b968

The following records the earlier checkpoint. Items 4 and 5 of its analytic
obligations (ideal jets and scalar comparison) are discharged above. Its
resistive-existence obligations and closed finite-gain gap remain.

**The requested closed resistive-existence and finite-gain theorem is not
complete.** No actual resistive solution has been constructed, either on a
whole finite slab or on `[a,1)`. The results below are checked construction
primitives and conditional comparison algebra. None of the missing analytic
steps is a structure field presented as an existence theorem.

### A. Physical periodic representation and Gaussian averaging

`ResistiveMagnetic.PeriodicGaussian` in
`NavierStokes/ResistivePeriodicGaussian.lean` uses
`Field = Space →ᵇ Space`, the Banach space of bounded continuous functions
on the actual three-dimensional cover. `periodicFields` is its **closed
linear subspace** satisfying `f(x+e_i)=f(x)` for the three physical
coordinate vectors; `PeriodicField` has a complete uniform norm.
`constantField c` belongs for every vector c. No zero-mean constraint,
whole-cover L2 norm, or periodic vector potential is required.

`lineAverage` is a Bochner integral of translated fields against
`gaussianReal 0 variance`. `orbit_continuous` proves continuity in the
uniform norm by compact-cell periodicity, rather than assuming all bounded
continuous functions are uniformly continuous. `orbit_integrable` justifies
the Banach-valued integral. `lineAverage_norm_le`, `lineAverage_periodic`,
`lineAverage_zero`, `lineAverage_const`, and `lineAverage_continuous` prove
contraction, periods, initial value, preservation of constants, and strong
continuity of each directional average in variance. `lineAverage_add` and
`lineAverage_smul` prove linearity. `spatialOperator` is the composition of
exactly three physical coordinate averages as a bounded linear operator on
`PeriodicField`; `spatialOperator_norm_le` bounds its operator norm by one.
`average_constant` retains the constant seed.

`physicalAverage` uses variance `2*eta_m*(t-a)`, with
`physical_variance` proving that the conversion to nonnegative variance
agrees with this expression when eta_m>=0 and t>=a.
`physicalAverage_initial` and `physicalAverage_axial_seed` prove the initial
and constant-seed identities. **The variance-generator identity and
one-derivative smoothing bound for these new physical operators are still
unproved.** The variance factor alone is not claimed to prove the generator.
Nor is a semigroup or mild-solution theorem for these operators exported.

The geometry audit found that the inherited
`EulerLiftedGradientSpace.LiftDomain period` is `Vector3 × AddCircle period`,
with product Lebesgue/angle measure (`Euler/EulerProof.lean:1085`).
`EulerCylinderSobolevSpace.SobolevWord` uses `Fin 4`, and its underlying
field is L2 on that noncompact cylinder. This is not the physical three-torus.
`EulerSobolevHeat.exists_viscous_mild_solution`, `heatKernel`, and
`EulerMildEquationBridge.viscous_mild_hasDerivAt` were inspected with their
actual types. Their `2*nu*time` variance and cylinder Laplacian do not justify
instantiating them with this physical constant seed. The abstract
`EulerVolterraConvolution.exists_mild_solution` remains reusable once the
physical derivative-gaining kernel and function-space scale are available.

### B. Comparison algebra and actual velocity bounds

Names in this and the next subsection have prefix
`NavierStokes.ResistiveMagnetic.Comparison`.

`source` is exactly `-DB[u]+Du[B]`, without a solenoidal projection.
`source_norm_le`, `source_sub`, `source_difference_bound`, and
`source_smooth` prove its local bound, linear difference identity, C1-to-C0
pointwise difference estimate, and local smoothness under supplied smooth
inputs. If the field and first-derivative differences are both bounded by
`delta`, and `||u||<=U`, `||Du||<=L`, the source difference is bounded by
`(U+L)*delta`. This is not yet a product/Lipschitz theorem on a completed
periodic Ck or Sobolev scale.

`actual_velocity_bounds scales hsel hb` uses the SAME actual selected
periodic velocity and the existing `actualOnSlab` coefficient path. For any
b<1 it proves finite real U,L>=0 such that, for all t in [a,b] and all x,
`||u(t,x)||<=U` and `||Du(t,x)||<=L`. Its constants depend on the slab and
schedule and contain no diffusivity parameter. No terminal uniform bound
is asserted.

`difference_equation` subtracts the supplied resistive and ideal PDEs to
prove, for W=B-I,

```
partial_t W + DW[u] = Du[W] + eta_m Delta W + eta_m Delta I.
```

It requires smooth spatial slices and differentiable time slices at the
evaluated point. `difference_initial` derives W(a)=0 from identical data.
`norm_sq_directional`, `norm_sq_second_directional`, `norm_sq_time`,
`norm_sq_advection`, and `norm_sq_laplacian` compute the derivatives of
`q=||W||²`. In particular, the scalar Laplacian is exactly
`2 sum_i ||partial_i W||² + 2 inner(W,Delta W)`.

`squared_equation` proves the full forced vector identity

```
(partial_t + u.grad - eta_m Delta) q
  = 2 inner(W,Du[W]) - 2 eta_m sum_i ||partial_i W||²
    + 2 eta_m inner(W,f).
```

Here f is the supplied forcing in the difference equation.
`squared_residual_bound` applies operator-norm bounds and Young's inequality.
`squared_inequality` gives the resulting scalar differential inequality.
`ideal_resistive_squared_inequality` DERIVES it directly from the two PDEs,
with `f=Delta I`, for jointly smooth B,I on an open time domain:

```
(partial_t + u.grad - eta_m Delta) q <= (2L+1) q + eta_m² D².
```

No norm derivative at zero or independent component comparison is used.
These local statements do not require a backward parabolic extension, but
they do not yet prove the endpoint-compatible maximum principle.

`barrier_hasDerivAt` and `barrier_initial` verify that
`R(t)=(exp((2L+1)*(t-a))-1)/(2L+1)` solves `R'=(2L+1)R+1`, R(a)=0.
`constant L D a b = D*sqrt(R(b))` is finite as a real expression and
`constant_nonneg` proves it is nonnegative for D>=0.
`constant_zero` covers D=0. `norm_le_of_squared_barrier` proves
`||W||<=eta_m*constant L D a b` from the EXPLICIT scalar barrier premise
`||W||²<=eta_m² D² R(b)`, for eta_m,L,D>=0 and a<=b.
**The barrier premise has not been established for the actual fields.**

`laplacian_bound_of_joint_continuity` proves a uniform D on a compact slab
from joint continuity and periodicity of the actual spatial Laplacian.
Its continuity premise is not inferred from separate spatial smoothness.
It is not yet instantiated for Paper I's constructed periodic ideal field.

### C. Exact finite-gain transfer, still conditional

`observationTime a K G = 1-(1-a)*(2G)^(-1/K)`.
For a<1, K>0, G>1, `observationTime_bounds` proves a<t_G<1 and
`observationTime_gain` proves `((1-a)/(1-t_G))^K=2G`, with all rpow
positivity and denominator conditions discharged.

`diffusivityThreshold G Bz0 C = G*abs(Bz0)/(1+C)` is positive for
G>0, Bz0!=0, C>=0. `finite_gain_of_error` proves the following implication
for ARBITRARY vectors v and ideal:

```
||ideal|| = 2G*abs(Bz0),   ||v-ideal|| <= eta_m*C,
0 < eta_m < G*abs(Bz0)/(1+C)
  => G*abs(Bz0) <= ||v||.
```

The proof uses only the triangle inequality and the stated threshold; it
assumes neither an axial resistive field nor an eigen-curvature closure.
`error_tendsto_zero` gives the limit as eta_m tends to zero from above from
any supplied nonnegative error bounded by eta_m*C.

`family_finite_gain` fixes a, K, nonzero Bz0, gamma, one ideal field and
one FAMILY of fields before G. Assuming the ideal path norm formula and
that family's fixed-slab uniform comparison bound, it proves:

```
forall G>1, exists t_G in (a,1), exists eta_G>0,
  forall eta_m in (0,eta_G),
    G*abs(Bz0) <= ||family eta_m (t_G,gamma t_G)||.
```

The family is not reselected per target. However, its existence as a family
of resistive PDE solutions and its comparison estimate are not proved here.
This theorem is deliberately **not** named or advertised as the closed
Navier-Stokes/resistive amplification theorem. No new schedule/profile
witness or upstream compatibility assumption is introduced.

### Exact remaining analytic obligations

1. Complete a physical periodic derivative scale containing the constants
   (for example closed uniform Ck derivative graphs over `PeriodicField`).
   Prove the new Gaussian operators' semigroup law, strong continuity on
   that scale, generator `(1/2) Delta` in variance, and a Ck-to-C(k+1) bound
   of the form `C*(1+(eta_m*tau)^(-1/2))` for eta_m,tau>0. Consequently prove
   the physical generator `eta_m Delta`; the arithmetic variance theorem
   is not a substitute.
2. Prove the source product, continuity and Lipschitz estimates in that
   scale for the actual coefficient paths. Instantiate abstract Volterra,
   prove uniqueness and bounds sufficient for finite-slab continuation,
   and prove compatibility across regularity orders and overlapping slabs.
3. Obtain one classical field per eta_m on [a,1), with continuity at a,
   interior derivatives and continuous initial divergence. Prove divergence
   preservation with forward endpoint hypotheses, avoiding any assumed
   backward-time PDE extension. No such field currently exists in Lean.
4. For the SAME ideal constructed witness, prove joint continuity of
   `(t,x) -> spatialLaplacian Bideal t x` through the initial endpoint.
   The existing smooth label-to-path family supplies forward jets;
   `Euler/InverseMapJetContinuity.lean` offers a reusable inverse-jet route
   from `DY=A o Y` and continuous coefficient jets. The periodic Eulerian
   composition still needs to be instantiated (third forward spatial
   derivatives and second inverse spatial derivatives suffice here).
   Then `laplacian_bound_of_joint_continuity` supplies the diffusivity-free D.
5. Prove the scalar periodic parabolic maximum/comparison principle for
   continuous initial data, interior time derivative and spatial C2
   regularity. Apply it to the proved squared inequality to obtain the
   barrier and the uniform O(eta_m) error. No such maximum principle or
   actual pointwise comparison theorem is exported in this extension.
6. Instantiate `family_finite_gain` with those constructions and with the
   existing closed compatible NS/ideal witnesses. The closed quantifier
   theorem remains open until steps 1–5 are supplied.

Nothing here determines fixed-positive-diffusivity terminal behavior, a
sharp gain law, a magnetic scale exponent, a useful numerical conductivity
threshold, energy blow-up, stability, attraction, or backreaction. The
existing conditional curvature-mode theorems remain separate and unchanged.

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

## Previously completed foundation (3a9b968)

Paper I's theorem scope and Lean files are unchanged. This extension proves
identities, divergence preservation in specified classical energy classes,
an exact coordinate transformation, and a conditional damped-mode cutoff.
**It does not yet decide amplification for a positive-diffusivity solution in
the actual assembled flows. No such resistive solution is constructed here.**

Unless qualified by `Calculus` or `Mode`, theorem names below are in
`NavierStokes.ResistiveMagnetic`. Definitions and proofs are in the new
`NavierStokes/Resistive*.lean` files. Constants are dimensionless; time is the
existing physical time, with terminal time 1. `eta_m` is magnetic diffusivity,
not a similarity coordinate named eta.

## PDE and divergence

The exact definition is:

```lean
def ResistiveInductionOn (eta_m : ℝ) (times : Set ℝ)
    (u : VelocityField) (B : MagneticField) : Prop :=
  ∀ t ∈ times, ∀ x,
    temporalDerivative B t x + spatialDerivative B t x (u (t,x)) =
      spatialDerivative u t x (B (t,x)) + eta_m • spatialLaplacian B t x
```

The algebraic interface admits real coefficients; dissipativity and
preservation theorems impose `0 ≤ eta_m`. `resistive_zero_iff` is an exact
iff with `MagneticTransport.IdealInductionOn` at zero diffusivity.
`material_derivative` proves the material chain rule for a differentiable
supplied B and a supplied Lagrangian trajectory, including the Laplacian.

`divergence_transport` assumes an open time set, joint `ContDiffOn ℝ ∞`
regularity of u and B there, the resistive PDE, and `div u = 0`. For
`f = divergenceScalar B`, it proves

\[
 \partial_t f+u\cdot\nabla f=\eta_m\Delta f.
\]

`divergenceScalar_eq` identifies f with the project's `spatialDivergence`.
The scalar time/space operators are actual Frechet directional derivatives
in spacetime. Component bridges identify these with the project's vector
operators. The proof establishes product rules, commutation through third
spatial derivatives, cancellation of the two cross contractions, and the
vanishing derivative of `div u`; none is an additional PDE assumption.

`periodic_divergence_preserved` gives `div B(t,x)=0` for every
`t ∈ Icc a b` and x. Assumptions: `a ≤ b`, `eta_m ≥ 0`, an open smoothness
domain containing `[a,b]`, joint smoothness of u and B on that domain,
unit spatial periods of both, `div u=0`, induction on `(a,b)`, and initial
`div B(a,x)=0`. The equation is required only on the forward slab interior;
the open-domain regularity supplies derivatives at its endpoints.
`periodic_passive_zero` proves the zero-data uniqueness used here by the
nonincreasing squared L2 norm and the existing Gronwall theorem.

`whole_divergence_preserved_l2` proves the same pointwise conclusion in
whole space. It replaces periodicity with compact support of u at each
interior time and an explicit energy class for
`W = scalarLift (divergenceScalar B) = (div B) e2`:

- W's slices are represented by `A t : SmoothL2Field Space` on `[a,b]`;
- the actual temporal derivative of W is represented by `C t` on `(a,b)`;
- `t ↦ (A t).toLp` is continuous on `[a,b]`, with derivative `(C t).toLp`
  at each interior time.

The smooth-L2 class supplies L2 integrability of all spatial jets.
`whole_passive_zero_l2` proves uniqueness in this class; it does not assume
magnetic divergence remains zero. Constructing these representatives and
the L2 time derivative for a resistive solution remains an existence and
regularity obligation. Compact support of B or W is not required.
These hypotheses are sufficient and have not been optimized to minimal Ck
regularity. No new witness with joint C-infinity regularity is asserted.

## Energy and Ohmic loss

`periodicEnergy B t` is one half of the existing unit-cell `cubeIntegral`
of `‖B(t,x)‖²`. `ohmicDissipation eta_m B t` is eta_m times the sum of the
three integrals of squared spatial partial derivatives.
`periodic_energy_hasDerivAt` proves

\[
 E'(t)=\int_{\rm cell}\langle B,D_xu[B]\rangle
       -\eta_m\sum_{i=0}^2\int_{\rm cell}\|\partial_i B\|^2.
\]

It assumes joint smoothness on the closed slab, unit periods of u and B,
`div u=0` and the PDE on the interior, and an interior evaluation time.
Magnetic divergence freedom is not needed for this energy identity.
The proof differentiates the integral using the existing compact-cell API,
then applies transport cancellation and periodic Laplacian integration by
parts. `periodic_energy_balance` exports the spatial integral step.
`ohmicDissipation_nonneg` and `accumulatedOhmicDissipation_nonneg` prove
nonnegativity for eta_m ≥ 0 (and ordered endpoints for the time integral).
`accumulatedOhmicDissipation` is the physical-time integral of the spatial
Ohmic loss; a separate integrated-in-time energy equality is not exported.

`wholeEnergy` uses the same half normalization with the existing whole-space
real L2-square integral. `whole_energy_hasDerivAt_l2` proves the analogous
whole-space identity with these explicit hypotheses:

- the actual slices of B are `A s : SmoothL2Field Space`;
- C represents the actual temporal derivative at t;
- the magnetic curve in L2 has derivative C at t;
- u is spatially smooth and compactly supported, with zero divergence;
- the resistive PDE holds at t.

`l2_laplacian_integrable` and `l2_laplacian_energy` reuse
`EulerOrdinarySobolev.field_directional_ibp`. They discharge the magnetic
Laplacian pairing and integration by parts from the spatial L2 jets. Compact
u supplies integrability of transport and stretching, without requiring
compact B. `whole_energy_balance_l2` exports this spatial identity.
The additional `whole_energy_hasDerivAt` theorem covers uniformly compact B
on a fixed slab; that is only a sufficient class, not a claim that diffusion
preserves compact support. The real integral identities are used with their
stated integrability premises. Paper I's ENNReal energy is retained for
region lower bounds; no unconditional conversion of a possibly infinite
energy to a real integral is made.

## Actual assembled flows and clocks

`actual_axial_material_derivative` uses the exact `MagneticPeriodicMain`
budget, threshold, geometry, selected schedule, natural solution, gamma,
and exponent. For either `actualPeriodicVelocity` or
`actualCompactVelocity`, at t in the existing `Ioo (lateStart ...) 1`, a
supplied differentiable resistive solution with instantaneous axial value
`B(t,gamma t)=b e2` satisfies

\[
 \frac{d}{dt}B(t,\gamma(t))=\frac{K b}{1-t}e_2
                         +\eta_m\Delta B(t,\gamma(t)).
\]

Only the proved axial column and trajectory transfer are used. The
Laplacian need not be axial, so even preservation of an axial direction
requires additional information in the resistive case. The result does not
transfer the natural-core transverse gradient or Hessian to the assembled
velocity. `actual_periodic_energy` and
`actual_periodic_divergence_preserved` discharge velocity smoothness,
periodicity, and incompressibility from that exact selected schedule.
`actual_compact_energy_l2` discharges compact support and spatial smoothness,
and uses the existing NS properties for the same velocity, pressure, and
forcing to discharge incompressibility. It retains this matching NS
certificate explicitly, as well as the magnetic L2 and PDE hypotheses.
No independent natural-profile witness is introduced.

`stretching_pathQ` proves `K/(1-t)=K/(d(eta)*pathQ eta t)` using the
existing `NaturalAxisData.d`, for eta²<1. Both candidates use the original
physical clock here; no additional viscosity or time rescaling occurs.

## Exact transformed equation and effective Reynolds ratio

For positive differentiable ell(t), set
`C(t,y)=B(t,gamma(t)+ell(t)y)` and `U(t,y)=u(t,gamma(t)+ell(t)y)`.
`rescaled_induction` proves the exact identity

\[
 \partial_t C+\ell^{-1}D_yC[U-\gamma'-\ell' y]
 =\ell^{-1}D_yU[C]+\frac{\eta_m}{\ell^2}\Delta_y C.
\]

The theorem assumes B differentiable at the evaluated spacetime point,
spatially smooth slices of u and B, derivatives of gamma and ell, positive
ell, and the resistive PDE. `laplacian_pullback` proves the factor ell²
before division. The transformation retains all advection, dilation,
rotation and coupling terms present in U. There is no reduction to a
transverse-only PDE for the actual assembled field in this milestone.
Choosing gamma to be the existing distinguished trajectory instantiates the
translation term; the actual-flow theorem above identifies its axial
stretching. The generic transformation itself does not assume a magnetic
profile or make ell an actual magnetic length scale.

With `s=1-t=d0*q`, the comparison definitions give

\[
 Rm_{\rm eff}=\frac{K/s}{\eta_m/\ell^2}
            =\frac{K\ell^2}{\eta_m s}.
\]

For the **additional scale hypothesis** ell=L s^beta with K,L,eta_m>0,
`effectiveRm_power` gives `(K L²/eta_m) s^(2 beta-1)`.
`effectiveRm_tendsto_infinity`, `effectiveRm_tendsto_zero`, and
`effectiveRm_critical` classify the limits: infinity for beta<1/2, zero
for beta>1/2, and the positive constant K L²/eta_m at beta=1/2.
This classification is conditional on interpreting ell as the magnetic
variation scale. The actual resistive magnetic beta is unknown.

`cutoffRemaining` and `effectiveRm_cutoff` give the rate-equality scale

\[
 s_\eta=\left(\frac{\eta_m}{K L^2}\right)^{1/(2\beta-1)},\qquad
 Rm_{\rm eff}(s_\eta)=1 \quad (\beta\ne1/2).
\]

The scale is positive, but need not lie in the chosen preterminal interval.
`idealGainAtCutoff=(s0/s_eta)^K` is a dimensionless comparison definition,
not a guaranteed maximum of a resistive solution. SI conversion is absent.

## Honest conditional reduced mode and cutoff

`pure_axial_of_curvature_closure` assumes a supplied resistive solution,
a Lagrangian trajectory, the existing continuity/differentiability and
continuous-gradient hypotheses for linear ODE uniqueness, the axial column
`Du e2=alpha e2`, and the extra identity

\[
 \Delta B(t,\gamma(t))=-\mu(t)B(t,\gamma(t)).
\]

It proves that an initially pure axial field follows any supplied scalar
solution `b'=(alpha-eta_m*mu)b` with matching initial data. This is an exact
conditional path reduction; advection is removed by the material chain rule,
and transverse coupling is excluded by the two explicit column/curvature
identities. The curvature identity is not a consequence of the velocity
transfer theorem. In particular, no transverse eigenprofile, or error bound
for neglected terms, has been constructed for the actual flow.

For `mu=(d/eta_m) s^(-(r+1))`, `Mode.trajectory_mode` proves the exact law
for one supplied field on a finite slab with b<1, eta_m>0 and r>0:

\[
 b(t)=B_0 G(s),\qquad
 G(s)=\left(\frac{s_0}{s}\right)^K
       \exp\left[-\frac d r(s^{-r}-s_0^{-r})\right],\quad s_0=1-a.
\]

`Mode.gain_as_power`, `gain_initial` and `physical_time_mode` establish
this formula, its normalized initial value, and its ODE. Under the further
positive parameters K,d,r,s0, `gain_le_peak`, `gain_at_peak`,
`peakGain_formula`, and `axial_mode_norm_le_peak` give

\[
 s_{\rm peak}=(d/K)^{1/r},\qquad
 G(s)\le G_{\rm peak}
 =s_0^K(K/d)^{K/r}\exp\left[\frac d r s_0^{-r}-\frac K r\right],
 \qquad \|b(t)e_2\|\le |B_0|G_{\rm peak}.
\]

The global positive-s maximum is attained on a chosen forward interval only
if it contains s_peak; `trajectory_peak_time` gives the interval condition.
`gain_tendsto_zero` proves terminal decay of this mode for d,r>0.
These are rigorous finite-eta **conditional mode** bounds. A closure with
transverse eigenvalue lambda and ell=L s^beta would set
`d=eta_m*lambda/L²`, `r=2 beta-1`; this interpretation requires an actual
profile proof. No global supremum bound or guaranteed finite amplification
factor for the assembled resistive PDE is concluded. No limit theorem with
eta_m tending to zero is needed or claimed beyond the displayed exact law.

## Relation to the ideal high-field regions

`material_high_field_region` applies to any spatially smooth supplied B on
an existing incompressible compact-velocity flow slab. For positive central
norm M and any label radius r0>0, it proves a finite derivative bound H for
`Q(xi)=B(t,Phi(t,xi))`. With
`r=r0*M/(2*(M+r0*H))`, the image of the label ball is open, has volume
`c3*r³`, has field norm at least M/2, and obeys the existing ENNReal bound
`E(t) ≥ ofReal((c3/8)*M²*r³)`. The proof uses the actual invertible,
measure-preserving flow API, not a determinant-only inference.

For positive diffusivity Q is not asserted to equal F times the initial
seed. Its M and H must come from the resistive solution. No terminal bound
for H, diffusion-imposed minimum length, fixed material set amplification,
energy divergence, or stability/attraction theorem follows from this
fixed-time statement. Paper I's shrinking ideal regions do not discharge
those resistive hypotheses.

## Analytic construction audit and next obligations

The repository already has substantial heat machinery; a new parabolic
foundation should not be started from scratch. In particular:

1. `EulerSobolevHeat.exists_viscous_mild_solution` in
   `Euler/SobolevHeatVolterra.lean` handles a continuous, locally Lipschitz
   source from Sobolev order q+1 to q. It has explicit budgets involving
   `T + 2*parabolicConstant eta_m*sqrt T`. It reuses the contraction theorem
   `EulerVolterraConvolution.exists_mild_solution`.
2. `Euler/MildEquationBridge.lean` supplies Sobolev-level time derivative
   bridges. `Euler/DivergenceFreeHeat.lean` supplies gradient-annihilator
   preservation in its existing lifted heat/mild setting. Neither is an
   instantiated classical resistive induction theorem for the actual
   physical-space velocity and magnetic seed.
3. The next adapter must represent `F(t,B)=-D B[u(t)]+D u(t)[B]` in the
   appropriate existing Sobolev geometry, prove the derivative-loss product
   and Lipschitz bounds for the actual selected coefficients on each fixed
   finite slab, and match the heat generator normalization to eta_m Delta.
4. It must construct compatible solutions across slabs, bootstrap enough
   regularity for the pointwise PDE, and establish the displayed periodic
   or whole-space L2 time/spatial hypotheses. For whole space, transport of
   compact support must be replaced by justified magnetic-tail estimates.
   All coefficient bounds may depend on the upper endpoint b<1.
5. Separately, amplification needs resistive curvature/profile estimates
   or valid comparison principles for this vector system. Neither the
   ideal axial column nor the ideal derivative-bound region theorem
   supplies the magnetic scale, eigen-curvature closure, or lower-order
   remainder control. Without that additional analysis, the actual
   finite-eta supremum and energy behavior remain undetermined.

No resistive existence axiom, placeholder, or admitted theorem is added.
There is no Lorentz feedback, coupled MHD, Hall term, reconnection model,
energy blow-up assertion, attractor claim, or performance interpretation.

## Validation

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
