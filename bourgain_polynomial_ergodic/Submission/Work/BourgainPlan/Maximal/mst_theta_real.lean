import Mathlib
import Submission.Work.BourgainPlan.Maximal.mstThetaEpsDefs
import Submission.Work.BourgainPlan.Maximal.polyProfile_fourier_dilation
import Submission.Work.BourgainPlan.Maximal.dilation_hl
import Submission.Work.BourgainPlan.Maximal.polyProfile_family_sum_le
import Submission.Work.BourgainPlan.Maximal.poly_dilation_lp_leading
import Submission.Work.BourgainPlan.Maximal.curveAvgDefs
import Submission.Work.BourgainPlan.Maximal.DRDFDefs
import Submission.Work.BourgainPlan.Maximal.mst_theta_real_assembly

/-!
# MST's input `(C2)` in real-variable form: the signed lacunary curve-average sum

Mirek–Stein–Trojan (arXiv:1512.07518, §4.4 and Theorem 17) cite the theory of *continuous singular
Radon transforms* (Stein, *Harmonic Analysis*, Chapter XI; Duoandikoetxea–Rubio de Francia,
Invent. Math. 84 (1986)) for: the multiplier `Θ_ε = Σ_{j<M} ε_j (Φ_{N_{j+1}} − Φ_{N_j})`
(`N_j = 2^{j·2^i}`, `‖ε_j‖ ≤ 1`, `Φ_N(β) = ∫₀¹ e(β P(N s)) ds` the oscillatory profile of `P`)
defines an `L^r(ℝ)`-bounded operator, `1 < r < ∞`, with a bound independent of the signs and of `M`.

By `polyProfile_fourier_dilation` the operator of `conj (Φ_N)` is the curve average
`σ_N h (x) = ∫₀¹ h (x − P (N t)) dt`, so the real-variable form of the cited theorem is the
`L^{2r}`-boundedness of the signed sum of the differences of the curve averages, uniformly in the
signs and in the number of terms.

The proof follows the Calderón–Zygmund-free route of `Maximal/DRDF_ROUTE.md` (Duoandikoetxea–Rubio
de Francia, specialised to `p = 2r ≥ 4`): telescope to the dyadic differences `D_k`, split the sum
into the Littlewood–Paley blocks `T_s`, use the van der Corput symbol decay for `L²` and a
vector-valued maximal/square-function argument for a uniform `L^{p₁}` bound, and interpolate.
-/

open MeasureTheory Finset
open scoped BigOperators ENNReal

set_option autoImplicit false

namespace Work.BourgainPlan.Maximal

noncomputable section

end

theorem mst_theta_real (P : Polynomial ℤ) (hdeg : 2 ≤ P.natDegree) (hlc : 0 < P.leadingCoeff) (r : ℕ) (hr : 2 ≤ r) : ∃ A : ℝ, 0 < A ∧ ∀ (i M : ℕ) (ε : ℕ → ℂ), (∀ j : ℕ, ‖ε j‖ ≤ 1) → ∀ (h : ℝ → ℂ), MeasureTheory.Integrable h → ∫⁻ x : ℝ, ‖∑ j ∈ Finset.range M, ε j * ((∫ t in (0:ℝ)..1, h (x - (Work.BourgainPlan.Maximal.toRealPoly P).eval (((2:ℝ) ^ (j * 2 ^ i)) * t))) - (∫ t in (0:ℝ)..1, h (x - (Work.BourgainPlan.Maximal.toRealPoly P).eval (((2:ℝ) ^ ((j+1) * 2 ^ i)) * t))))‖ₑ ^ (2 * (r : ℝ)) ∂MeasureTheory.volume ≤ ENNReal.ofReal (A ^ (2 * (r : ℝ))) * ∫⁻ x : ℝ, ‖h x‖ₑ ^ (2 * (r : ℝ)) ∂MeasureTheory.volume := mst_theta_real_assembly P hdeg hlc r hr

end Work.BourgainPlan.Maximal
