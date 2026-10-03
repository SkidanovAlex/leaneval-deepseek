/-
Copyright: subproject `OROneRel` -- one-relator combinatorics (node N2).

# The exponent-sum-zero engine of the Freiheitssatz

This is the glue between the HNN step of the Freiheitssatz and its two case engines: given a
cyclically reduced relator `s` with `sigma t s = 1` (exponent sum zero) whose letter `x ≠ t` is
outside the generating set `T'` (or `t` is), the Freiheitssatz holds for `s` and `T'`, provided the
Freiheitssatz is known for all relators of norm below the norm of the Magnus rewriting.

The relator is first rotated (`exists_rotation_to_head`) so that its reduced word begins with `x`:
this is what makes the `x`-decorations of the Magnus rewriting `magRewRel t s` straddle the index
`0`, as required by the HNN step `exists_hnnStepCore`.  The rotation preserves everything the
argument needs: the norm of the Magnus rewriting (`relatorNorm_magRewRel_rotate`), the letters
(hence the hypothesis that `s` is not a word in `T'`), the exponent sums, and the cyclically reduced
form.  Depending on which of `x ∉ T'`, `t ∉ T'` holds, one then applies
`freiheitssatz_zero_expsum` respectively `freiheitssatz_zero_expsum_not_mem`, and transports the
conclusion back along the conjugacy (`injective_presentedGroupMap_of_isConj`).
-/
import Mathlib
import Submission.Work.OROneRel.HNNStep
import Submission.Work.OROneRel.letters_closure_iff
import Submission.Work.OROneRel.injective_presentedGroupMap_of_isConj
import Submission.Work.OROneRel.exists_rotation_to_head
import Submission.Work.OROneRel.relatorNorm_magRewRel_rotate
import Submission.Work.OROneRel.hnn_step_core_exists
import Submission.Work.OROneRel.theta_apply_rewrite
import Submission.Work.OROneRel.zero_expsum_x_not_mem
import Submission.Work.OROneRel.zero_expsum_t_not_mem

namespace Work.OROneRel

universe u

variable {α : Type u}

theorem freiheitssatz_zero_expsum_engine {α : Type u} {t x : α} (htx : x ≠ t) (N : ℕ) :
    ZeroExpsumEngine t x N := by
  intro s T' hcyc ht hx hσ hdisj hnotmem hbnd hIH
  classical
  -- rotate `s` so that its reduced word begins with the letter `x`
  obtain ⟨k, s₁, c, hs₁, hcyc₁, hconj, hnrm, hlet, hsig, hhead⟩ :=
    exists_rotation_to_head s x hcyc hx
  have ht₁ : t ∈ relatorLetters s₁ := by rw [hlet]; exact ht
  have hx₁ : x ∈ relatorLetters s₁ := by rw [hlet]; exact hx
  have hσ₁ : sigma t s₁ = 1 := by rw [hsig]; exact hσ
  -- the bound on the Magnus rewriting is invariant under the rotation
  have hbnd₁ : relatorNorm (magRewRel t s₁) < N := by
    have hcycL : FreeGroup.IsCyclicallyReduced (FreeGroup.toWord s) := hcyc
    rw [hs₁, relatorNorm_magRewRel_rotate t hcycL k, FreeGroup.mk_toWord]
    exact hbnd
  -- the hypothesis that `T'` does not generate `s` is invariant (the letters are preserved)
  have hnotmem₁ : s₁ ∉ Subgroup.closure (FreeGroup.of '' T') := by
    rw [letters_closure_iff] at hnotmem ⊢
    simp only [SupportedOn] at hnotmem ⊢
    intro hsu
    exact hnotmem (by rwa [hlet] at hsu)
  -- the induction hypothesis in the form needed at the HNN base
  have hIH₁ : FreiheitssatzBelow (relatorNorm (magRewRel t s₁) + 1) :=
    fun β u hu => hIH β u (by omega)
  obtain ⟨i, j, -, -, -, -, -, ⟨d⟩⟩ := hnn_step_core_exists s₁ t x hcyc₁ ht₁ hx₁ htx hσ₁ hhead hIH₁
  rcases hdisj with hxT | htT
  · -- `x ∉ T'`: rewrite words of `F(T')` with exponent sum zero
    have hrew : ∀ w : FreeGroup α, sigma t w = 1 → x ∉ relatorLetters w →
        d.theta (PresentedGroup.mk ({s₁} : Set (FreeGroup α)) w) =
          hnnOf s₁ t (PresentedGroup.mk
            ({magRewRel t s₁} : Set (FreeGroup ({a : α // a ≠ t} × ℤ)))
            (magRewRel t w)) :=
      fun w h₁ h₂ => theta_apply_rewrite d w h₁ h₂
    exact injective_presentedGroupMap_of_isConj (isConj_iff.mpr ⟨c, hconj.symm⟩)
      (zero_expsum_x_not_mem s₁ T' t x i j hcyc₁ ht₁ hx₁ htx hσ₁ hxT hnotmem₁ d hrew hIH₁)
  · -- `t ∉ T'`: the whole generating set lies in the HNN base
    exact injective_presentedGroupMap_of_isConj (isConj_iff.mpr ⟨c, hconj.symm⟩)
      (zero_expsum_t_not_mem s₁ T' t x i j hcyc₁ ht₁ hx₁ htx hσ₁ htT hnotmem₁ d hIH₁)

end Work.OROneRel
