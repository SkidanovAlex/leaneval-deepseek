import Mathlib
import Submission.Work.WilE3.Frame.Vcoef

namespace Work.WilE3.Frame

/-- On coordinates `i` outside the range of `ι`, the tangential frame vector `V_l` is just the
coordinate vector `e_l`: the Cramer correction `Σ_b (if ι b = i then β_b else 0)` is empty. -/
lemma VcoefC_not_mem_range {k r j : ℕ} (c : WilkiesDesign.E.EAChain k r) (h : Fin j → WilkiesDesign.E.EAPoly k r)
    (ι : Fin j → Fin k) (l : Fin k) (z : Fin k → ℂ) {i : Fin k} (hi : i ∉ Set.range ι) :
    Work.WilE3.Frame.VcoefC c h ι l z i = if i = l then (1:ℂ) else 0 := by
  rw [VcoefC]
  have hsum : (∑ b : Fin j, if ι b = i then betaC c h ι l z b else 0) = 0 := by
    apply Finset.sum_eq_zero
    intro b _
    rw [ite_eq_right (fun hb => hi ⟨b, hb⟩)]
  rw [hsum, sub_zero]

end Work.WilE3.Frame
