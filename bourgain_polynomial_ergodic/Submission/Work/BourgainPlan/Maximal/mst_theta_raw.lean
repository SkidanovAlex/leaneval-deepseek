import Mathlib
import Submission.Work.BourgainPlan.Maximal.mst_theta_weighted_defs
import Submission.Work.BourgainPlan.Maximal.mst_theta_defs
import Submission.Work.BourgainPlan.Maximal.mst_scalar_defs
import Submission.Work.BourgainPlan.Maximal.bandedBlockMultiplier_lp
import Submission.Work.BourgainPlan.Maximal.polyProfile_family_sum_le
import Submission.Work.BourgainPlan.Maximal.mst_theta_real_defs
import Submission.Work.BourgainPlan.Maximal.mst_theta_real
import Submission.Work.BourgainPlan.Maximal.mstThetaRawMult_of_real
import Submission.Work.BourgainPlan.Maximal.iwmult_const

/-!
# The raw (unweighted) `(C2)` input of the Mirek–Stein–Trojan route

**Target of this file** (`Work.BourgainPlan.Maximal.mst_theta_raw`): for every integer polynomial
`P` of degree `≥ 2` with positive leading coefficient and every `r ≥ 2` there is `A > 0` such that
the signed lacunary profile-difference symbol

  `Θ_ε = Σ_{j<M} ε_j (Φ_{2^{(j+1)·2^i}} − Φ_{2^{j·2^i}})`,  `‖ε j‖ ≤ 1`,

read on the circle through the canonical lift `iwRep`, is an `L^{2r}(ℝ)` multiplier with norm
`≤ A`, uniformly in the level `i`, the number of terms `M` and the signs `ε` — and likewise for its
conjugate.  This is the *raw* form of MST's input `(C2)` (Mirek–Stein–Trojan, arXiv:1512.07518,
§4.4, and their Theorem 17: "the multiplier `Θ` corresponds to a continuous singular Radon
transform; thus `Θ` defines a bounded operator on `L^r(ℝ^d)` for any `r ∈ (1,∞)`, with a bound
independent of the underlying sign sequence", citing `[bigs, §11]` = Stein's *Harmonic Analysis*,
and Duoandikoetxea–Rubio de Francia, Invent. Math. 84 (1986)).  The *weighted* form
`MSTThetaWeightedMult` (with the level bump `η_s` and the factor `Mη`) is obtained from the raw
form by composition with the bump; see `Maximal/mst_theta_weighted_defs.lean`.

## Findings and route (this session; for whoever continues)

1. **The symbol is a sharp truncation of a periodic function.**  The lift `circleLift ψ x` equals
   `ψ (-(x : Circle))` on `Ioc (-1/2) (1/2]` (`Thm52/CircleLiftDefs.circleLift_of_mem`) and `0`
   outside; since `iwRep` is the canonical representative in `Ioc (-1/2) (1/2]`, for the symbol
   `ψ = Θ_ε ∘ iwRep` the lift is the indicator of the fundamental domain times the honest symbol:
   `circleLift (Θ_ε ∘ iwRep) x = 1_{x ∈ Ioc (-1/2) (1/2]} · Θ_ε (-x)` (the caveat being the single
   point `x = 1/2`, where the canonical representative jumps).  Consequently the circle multiplier
   factorises as `T_{Θ_ε} ∘ T_{1_{(-1/2,1/2)}}` up to the norm-preserving reflection `ξ ↦ -ξ`, so the
   raw input follows from

   * the *interval (Dirichlet) multiplier* `1_{(-1/2,1/2)}` being `L^{2r}`-bounded — classical
     (`1_{(-1/2,1/2)} = ½(sgn(·+1/2) − sgn(·−1/2))` is a difference of two modulations of the
     Hilbert/sign multiplier); delegated as `Maximal/iwmult_const`;
   * the *real-variable* signed-sum bound `MSTThetaRealMult` below, delegated as
     `Maximal/mst_theta_real`.

2. **The real-variable form** (`MSTThetaRealMult`): since `Φ_N` is the Fourier transform of the
   pushforward `μ_N` of `N⁻¹ dy` on `[0,N]` under `P`, the operator of `conj (Φ_N)` is the
   averaging operator `x ↦ ∫₀¹ h (x − P(N s)) ds` (`polyProfile_fourier_dilation`), so the
   real-variable statement is the `L^{2r}`-boundedness of the signed sum of the polynomial
   *averaging* operators, uniformly in the signs and the scales.  This is the honest content of
   MST's citation ("continuous singular Radon transform").

3. **What does not work (recorded so as not to repeat it).**
   * `Θ_ε` is *not* a Mikhlin symbol uniformly in the signs (`Maximal/mstThetaEpsDefs.lean`
     header): for `P = X²`, `ξ = 1/5`, `ε_j = (-1)^j` one has `|ξ| ‖Θ_ε' ξ‖ ≍ M`.  Hence the
     Mikhlin discharge (`mikhlin_multiplier_lift`) is unavailable.  The band-localised version *is*
     Mikhlin uniformly (`bandLocalizedIncrement_mikhlin`, `bandedBlockMultiplier_lp`), but the
     off-band part of the partition of unity does not sum uniformly.
   * The kernel of the circle symbol has the Dirichlet-type tail `K(x) ≈ c e^{iπ x}/(2π i x) + …`:
     the truncation `1_{(-1/2,1/2)} Θ_ε` has jumps at `±1/2` whose size is `|Θ_ε(1/2)|`, and
     `|Θ_ε(1/2)| ≲ Σ_j N_j^{-1}` is generically of order `1` — it is *not* small.  Hence the
     classical `L¹`-Hörmander condition `∫_{|x| ≥ 2|y|} |K(x-y) − K(x)| dx ≤ C` *fails* for this
     kernel (the Dirichlet multiplier is nevertheless bounded, so the `L¹`-Hörmander condition is
     simply not the right sufficient tool).  In particular `cz_lp_small_general` cannot be fed
     directly.
   * Kernel side, the averages satisfy the sharp bounds (with `a = P(N)`, `d = deg P`,
     `D(u) = sin(πu)/(πu)`, `W_N(x) = ∫₀¹ D(x + P(N t)) dt = (d a^{1/d})⁻¹ ∫₀^{a} u^{1/d-1} D(x+u) du`):
     `|W_N(x)| ≲ N⁻¹ (1+|x|)^{-(d-1)/d}` (both regimes `x ≲ a`, `x ≳ a`, using that
     `∫₀^{A} u^{1/d-1} e^{iπu} du` is bounded for `u^{1/d-1}` monotone, by integration by parts),
     and `W_N(x) = π⁻¹ x⁻¹ Im[e^{iπx} Φ_N(1/2)] + O(N^{d} x^{-2})` for `x ≳ N^{d}`, together with
     the van der Corput decay `|Φ_N(1/2)| ≲ N⁻¹` (`polyProfile_decay_sharp`).  Summed over the
     lacunary blocks this gives `Σ_j |W_{N_{j+1}} − W_{N_j}|(x) ≲ (1+|x|)^{-1}` — but only the
     *marginal* Dirichlet-type decay, so the `L^p` conclusion for `p ≠ 2` needs the full strength of
     the Duoandikoetxea–Rubio de Francia / Stein theory of lacunary dilations of measures with
     decaying Fourier transform (maximal function + square function + Khintchine), not merely a
     kernel smoothness condition.
## Status and final assembly (end of this session)

Proved and available (import them):

* `Maximal/iwmult_const` : `∃ A > 0, IWMult r (fun _ => 1) A` (the interval/Dirichlet multiplier);
* `Maximal/mstThetaRawMult_of_real` : `MSTThetaRealMult P r A → ∃ B > 0, MSTThetaRawMult P r B`
  (the bridge: real-variable bound + Dirichlet bound ⟹ the circle-lift bound);
* `Maximal/interpolate_two_p` : sublinear Riesz–Thorin `(2,2)+(p₁,p₁) ⟹ (p,p)`, `2 < p < p₁`;
* `Maximal/polyAverageKernel_decay` : `|∫₀¹ sin(π(x+P(Nt)))/(π(x+P(Nt))) dt| ≤ C N⁻¹ (1+|x|)^{-(d-1)/d}`.

In flight (delegated, child ids of this session): `Maximal/mst_theta_real` (the core, via the
Duoandikoetxea–Rubio de Francia route written up by the project lead in `Maximal/DRDF_ROUTE.md`:
telescoping to dyadic signs ⟹ Littlewood–Paley split `T = Σ_s T_s` ⟹ `‖T_s‖_{2→2} ≲ 2^{-|s|/d}`
(step 3, from the van der Corput symbol bounds) and `‖T_s‖_{p₁→p₁} ≲ 1` (step 4: dual LP +
`lp_square_function_finite_multiplier` + the polynomial maximal function) ⟹ `interpolate_two_p`
(step 5) ⟹ sum over `s` and Fatou (step 6)).  The remaining route items are
`dyadic_reduction` (step 0), `Ts_l2_decay` (step 3), `dual_lp_square` (4a),
`maximal_vector_valued` (4b), `Ts_lp_uniform` (4c), and the step-6 assembly.

Once the core `mst_theta_real` is available, the target follows in three lines: apply it with
`P, hdeg, hlc, r, hr` to get `A > 0` together with the real-variable bound (which is definitionally
the `Prop` `MSTThetaRealMult P r A`), then feed that into `mstThetaRawMult_of_real` (with the same
`hr`), which produces `B > 0` and `MSTThetaRawMult P r B`.  Those three lines are exactly what the
proof of the theorem below does; the imports needed are
`Submission.Work.BourgainPlan.Maximal.mst_theta_real` and
`Submission.Work.BourgainPlan.Maximal.mstThetaRawMult_of_real`.
-/

open MeasureTheory Finset
open scoped BigOperators ENNReal Topology

namespace Work.BourgainPlan.Maximal

theorem mst_theta_raw (P : Polynomial ℤ) (hdeg : 2 ≤ P.natDegree) (hlc : 0 < P.leadingCoeff)
    (r : ℕ) (hr : 2 ≤ r) :
    ∃ A : ℝ, 0 < A ∧ Work.BourgainPlan.Maximal.MSTThetaRawMult P r A := by
  obtain ⟨A, hA, hreal⟩ := mst_theta_real P hdeg hlc r hr
  exact mstThetaRawMult_of_real hr hA hreal

end Work.BourgainPlan.Maximal
