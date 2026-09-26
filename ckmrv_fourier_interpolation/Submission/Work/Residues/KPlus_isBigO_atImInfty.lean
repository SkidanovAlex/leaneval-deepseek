import Mathlib
import Submission.Work.Residues.KPlusAux
import Submission.Work.Residues.KPlus8Bound
import Submission.Work.Residues.KPlus24Bound

noncomputable section
open UpperHalfPlane ModularForm ModularGroup Matrix
open scoped MatrixGroups ModularForm Modular Manifold Bundle

namespace Work.Residues
open Work.Kernels
open Work.Residues.KPlusAux

set_option maxHeartbeats 8000000

/-- **The `i∞` bound of CKMRV Theorem 4.9(4)** for `K_+`: for fixed `z`,
`K_+^{(8)}(τ,z) = O(|τ e^{2πiτ}|)` and `K_+^{(24)}(τ,z) = O(|τ e^{4πiτ}|)` as `Im τ → ∞`.
The threshold `H` eliminates the poles of `K_+`, whose set is the `SL(2,ℤ)`-orbit of `z` and
hence has bounded imaginary part; the leading `τ`-linear terms cancel, leaving a bound with a
constant depending only on `z`. -/
theorem KPlus_isBigO_atImInfty (d : ℕ) (hd : d = 8 ∨ d = 24) (z : UpperHalfPlane) :
    ∃ H C : ℝ, 0 < C ∧ ∀ τ : UpperHalfPlane, H ≤ τ.im →
      ‖Work.Kernels.KPlus d τ z‖ ≤ C * ‖(τ : ℂ)‖ *
        Real.exp (-((if d = 8 then (2 : ℝ) else 4) * Real.pi * τ.im)) := by
  rcases hd with rfl | rfl
  · obtain ⟨H, C, hC, hb⟩ := kplus_eight_bound z
    refine ⟨H, C, hC, fun τ hτ => ?_⟩
    have h8 : (if (8 : ℕ) = 8 then (2 : ℝ) else 4) = 2 := by norm_num
    rw [h8]
    exact hb τ hτ
  · obtain ⟨H, C, hC, hb⟩ := kplus_twentyfour_bound z
    refine ⟨H, C, hC, fun τ hτ => ?_⟩
    have h1 : (if (24 : ℕ) = 8 then (2 : ℝ) else 4) = 4 := by norm_num
    rw [h1]
    have h2 : Real.exp (-(4 * Real.pi * τ.im)) = (eps τ)^2 := by
      rw [eps, sq, ← Real.exp_add]; ring_nf
    rw [h2]
    exact hb τ hτ

end Work.Residues
