import Mathlib
import Submission.Work.Modular.Basic

namespace Work.Modular

open UpperHalfPlane ModularForm
open scoped MatrixGroups ModularForm

/-- Depth is monotone in the successor step: a quasimodular form of weight `k` and depth
at most `d` is also one of depth at most `d + 1` (the extra `E₂`-coefficient is `0`). -/
theorem isQuasiModularFormDepth_succ {d : ℕ} {k : ℤ} {f : ℍ → ℂ}
    (hf : IsQuasiModularFormDepth d k f) : IsQuasiModularFormDepth (d + 1) k f := by
  obtain ⟨m, hm⟩ := hf
  refine ⟨Fin.lastCases (motive := fun j => ModularForm 𝒮ℒ (k - 2 * (j : ℤ))) 0 (fun i => m i), ?_⟩
  rw [hm]
  conv_rhs => rw [Fin.sum_univ_castSucc]
  simp [Fin.lastCases_castSucc, Fin.lastCases_last]

theorem isQuasiModularFormDepth_mono {d d' : ℕ} {k : ℤ} {f : ℍ → ℂ} (h : d ≤ d')
    (hf : IsQuasiModularFormDepth d k f) : IsQuasiModularFormDepth d' k f := by
  have key : ∀ t, d ≤ t → IsQuasiModularFormDepth t k f := fun t ht =>
    Nat.le_induction hf (fun n _ ih => isQuasiModularFormDepth_succ ih) t ht
  exact key d' h

end Work.Modular
