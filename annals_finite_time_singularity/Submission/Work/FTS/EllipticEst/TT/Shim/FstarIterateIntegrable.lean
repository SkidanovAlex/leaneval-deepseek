import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Integral.IntegrableOn
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.FTS.EllipticEst.TT.Shim.EllHyp_certificates
import Submission.Work.Elliptic.L12Iterate
import Submission.Work.FTS.EllipticEst.GbarSetup
import Submission.Work.FTS.EllipticEst.FstarDzIter_sq_mul_w_le_open
import Submission.Work.FTS.EllipticEst.Cert.GbarSin.OpenCore

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.EllipticEst.Cert

open scoped Real Topology
open MeasureTheory Set Filter

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
set_option maxHeartbeats 1600000

/-! ## The angular moment of the `j`-th radial iterate

`Work.Elliptic.Qang g j` is the angular moment of `D_z^j g` against the weight
`K(θ) = 3 sinθcos²θ`, whereas the paper's moment `F_*(D_z^j g)` uses the weight `sinθcos²θ`
(`Work.FTS.EllipticEst.Bmom`, `Work.FTS.EllipticEst.Cert.GbarSin.Uj`).  The two differ by the
factor `3`; this bridge makes the differentiation-under-the-integral lemma
`Work.Elliptic.Qang_deriv_mul` (proved for `SmoothNbhd` data) available for the paper's moment.

Everything here is `sorry`-free and rests on `[propext, Classical.choice, Quot.sound]`. -/

/-- `Qang` is three times the angular moment `F_*(D_z^j g)`. -/
theorem Qang_eq_three_moment (g : ℝ → ℝ → ℝ) (j : ℕ) (z : ℝ) :
    Work.Elliptic.Qang g j z = 3 * Work.Elliptic.Fstar (Work.Spaces.DzIter j g) z := by
  rw [Work.Elliptic.Qang, Work.Elliptic.Fstar]
  rw [show (fun θ : ℝ => Work.Elliptic.Ktheta θ * Work.Spaces.DzIter j g z θ)
      = fun θ : ℝ => 3 * (Work.Spaces.DzIter j g z θ * Work.Elliptic.sinCos2 θ) from by
    funext θ
    rw [Work.Elliptic.Ktheta, Work.Elliptic.sinCos2]
    ring]
  rw [MeasureTheory.integral_const_mul]

/-- **Differentiation under the `θ`-integral for the angular moment.**  For `h` smooth on a
neighbourhood of the closed quadrant and `z > 0`, the one-variable operator `z ∂_z` commutes
with the angular moment: `z ∂_z (F_*(h))(z) = F_*(D_z h)(z)`.

Immediate from `Work.Elliptic.Qang_deriv_mul` (the recursion `z ∂_z Q_j = Q_{j+1}` for the
weighted moment `Q_j = ∫_θ K(θ) D_z^j h`) together with the factor `3` of
`Qang_eq_three_moment`. -/
theorem rDz_Fstar_eq (h : ℝ → ℝ → ℝ) (hsm : Work.Spaces.SmoothNbhd h) {z : ℝ} (hz : 0 < z) :
    z * deriv (fun z' => Work.Elliptic.Fstar h z') z = Work.Elliptic.Fstar (Work.Spaces.Dz h) z := by
  have hQ := Work.Elliptic.Qang_deriv_mul h hsm 0 hz
  have hfun : (fun z' => Work.Elliptic.Qang h 0 z') = fun z' => 3 * Work.Elliptic.Fstar h z' := by
    funext z'
    rw [Qang_eq_three_moment]
    rfl
  rw [hfun, deriv_const_mul_field] at hQ
  rw [Qang_eq_three_moment] at hQ
  simp only [Work.Spaces.DzIter_succ, Work.Spaces.DzIter_zero] at hQ
  linarith

/-- **The moment of the `j`-th radial iterate is the `j`-th radial iterate of the moment**:
`(D_z^j F_*)(z) = F_*(D_z^j g)(z)` for every `z > 0` and every `g` smooth on a neighbourhood of
the closed quadrant.  This is the one-variable recursion of `rDz_Fstar_eq`, iterated; no
integrability hypothesis is needed, only the smoothness that legitimises
`Work.Elliptic.Qang_deriv_mul`. -/
theorem rDzIter_Fstar_eq (g : ℝ → ℝ → ℝ) (hsm : Work.Spaces.SmoothNbhd g) (j : ℕ) {z : ℝ}
    (hz : 0 < z) :
    rDzIter j (fun z => Work.Elliptic.Fstar g z) z
      = Work.Elliptic.Fstar (Work.Spaces.DzIter j g) z := by
  have haux : ∀ j : ℕ, ∀ z : ℝ, 0 < z →
      rDzIter j (fun z => Work.Elliptic.Fstar g z) z
        = Work.Elliptic.Fstar (Work.Spaces.DzIter j g) z := by
    intro j
    induction j with
    | zero => intro z _; rfl
    | succ n ih =>
        intro z hz
        rw [rDzIter_succ]
        show z * deriv (rDzIter n (fun z => Work.Elliptic.Fstar g z)) z
          = Work.Elliptic.Fstar (Work.Spaces.DzIter (n + 1) g) z
        have hev : rDzIter n (fun z => Work.Elliptic.Fstar g z)
            =ᶠ[𝓝 z] fun z' => Work.Elliptic.Fstar (Work.Spaces.DzIter n g) z' := by
          filter_upwards [isOpen_Ioi.mem_nhds hz] with z' hz'
          exact ih z' hz'
        rw [hev.deriv_eq]
        exact rDz_Fstar_eq (Work.Spaces.DzIter n g) (Work.Elliptic.smoothNbhd_DzIter hsm n) hz
  exact haux j z hz

/-- **Weighted `L²` integrability of the radial iterates of the angular moment `F_*(g)`.**
For `g` smooth on a neighbourhood of the closed quadrant with `g ∈ ℋ^k` and `j ≤ k`,
`z ↦ w(z)² (D_z^j (F_*(g)) z)²` is integrable on `[0,∞)`.

Route: `D_z^j (F_*(g)) = F_*(D_z^j g)` on `(0,∞)` — the moment of the `j`-th radial iterate is
the `j`-th iterate of the moment (the one-variable recursion `z ∂_z Qang g j = Qang g (j+1)` of
`Work.Elliptic.L12Iterate` / `Work.Elliptic.Qang_deriv_mul`, proved, for `K(θ) = 3 sinθcos²θ`,
together with `F_*(h) = Qang h 0 / 3` and `F_*(D_z^j g) = Bmom g j`).  Then Cauchy–Schwarz
gives `w(z)² (F_*(D_z^j g) z)² ≤ (π/2)·w(z)²·∫_θ (D_z^j g z θ)² dθ` — available directly as
`Work.FTS.EllipticEst.FstarDzIter_sq_mul_w_le_open` — and the `i = j` summand of
`Work.Spaces.HkIntegrand α k g` is `(D_z^j g·w/sin(2θ)^{η/2})² ≥ w(z)²(D_z^j g)²` (as
`sin(2θ)^{η/2} ≤ 1`), so the bound is integrable by `hmem`. -/
theorem FstarIterateIntegrable (α : ℝ) (k : ℕ) (g : ℝ → ℝ → ℝ) (hα : 0 < α)
    (hg : Work.Spaces.SmoothNbhd g) (hmem : Work.Spaces.HkMem α k g) (j : ℕ) (hj : j ≤ k) :
    MeasureTheory.IntegrableOn (fun z : ℝ => (Work.Spaces.w z) ^ 2 *
      (Work.FTS.EllipticEst.rDzIter j (fun z : ℝ => Work.Elliptic.Fstar g z) z) ^ 2)
      Work.Spaces.Iz := by
  have hF : SmoothOpen g := SmoothNbhd_smoothOpen hg
  -- the moments `U_j = F_*(D_z^j g)` satisfy the desired weighted `L²` bound
  have hU : MeasureTheory.Integrable (fun z : ℝ => (Work.Spaces.w z) ^ 2 *
      (GbarSin.Uj g j z) ^ 2) (volume.restrict Work.Spaces.Iz) := by
    rw [← GbarSin.restrict_Ioi_eq_restrict_Iz]
    exact (GbarSin.Uj_sq_mul_w_integrable α k g hF hmem j hj).1
  -- and `D_z^j (F_*(g)) = F_*(D_z^j g)` for every `z > 0`
  have hcongr : (fun z : ℝ => (Work.Spaces.w z) ^ 2 * (GbarSin.Uj g j z) ^ 2)
      =ᵐ[volume.restrict Work.Spaces.Iz]
        (fun z : ℝ => (Work.Spaces.w z) ^ 2 *
          (Work.FTS.EllipticEst.rDzIter j (fun z : ℝ => Work.Elliptic.Fstar g z) z) ^ 2) := by
    rw [← GbarSin.restrict_Ioi_eq_restrict_Iz]
    filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Ioi] with z hz
    rw [GbarSin.Uj_apply, rDzIter_Fstar_eq g hg j hz]
  exact MeasureTheory.Integrable.congr hU hcongr

end Work.FTS.EllipticEst.Cert
