import Mathlib
import Submission.Work.Peluse.Prop36SW.LStateAbs

namespace Work.Peluse.Prop36SW

noncomputable section

open Work.Peluse.UControl

/-- `LStateAbs.abs_iff`: the sign-agnostic state may be read with either the signed coefficient
function `p` or its absolute value `|p|`.  The two side conditions differ only through the trivial
identities `|p| = 0 ↔ p = 0` and `||p|| = |p|`, and the family hypothesis is carried across by the
sign substitution `sum_LState_hyp_abs` of `signBridge.lean` (`pDirG` sees the coefficient only
through `p s a` at the fixed outer parameter `a`, so the two coefficient functions
`(fun s _ => |p s a|)` and `(fun i a' => |p i a'|)` are interchangeable there). -/
theorem lstateAbsAbsIff {ι : Type} [Fintype ι] [DecidableEq ι]
    {kω : Work.Peluse.UControl.SlotSet ι (fun _ => 1) → ℕ}
    {P : Type} [DecidableEq P] (p : ι → P → ℤ) (M₁ M₂ N D : ℕ) (A : Finset P)
    (g : P → ℤ → ℂ) (γ : ℝ) :
    Work.Peluse.Prop36SW.LStateAbs kω p M₁ M₂ N D A g γ ↔
      Work.Peluse.Prop36SW.LStateAbs kω (fun i a => |p i a|) M₁ M₂ N D A g γ := by
  have hsum :
      (∑ a ∈ A, ∑ a' ∈ paramBox (k := fun _ : ι => 1) M₂,
          boxNorm (Fintype.card (FamIdx kω))
            (fun j => pDirFamG (kω := kω) p M₁ a a'
              ((Fintype.equivFin (FamIdx kω)).symm j)) (symIcc N) (g a))
        = ∑ a ∈ A, ∑ a' ∈ paramBox (k := fun _ : ι => 1) M₂,
          boxNorm (Fintype.card (FamIdx kω))
            (fun j => pDirFamG (kω := kω) (fun i a => |p i a|) M₁ a a'
              ((Fintype.equivFin (FamIdx kω)).symm j)) (symIcc N) (g a) := by
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [sum_paramBox_boxNorm_abs kω p M₁ M₂ a (symIcc N) (g a)]
    refine Finset.sum_congr rfl fun b _ => ?_
    refine congrArg (fun F => boxNorm (Fintype.card (FamIdx kω)) F (symIcc N) (g a)) ?_
    exact funext fun j => rfl
  constructor
  · intro h
    obtain ⟨h0, h1, h2, h3, h4, h5, hp, hpl, hpa, hg1, hg2, hfam⟩ := h
    refine ⟨h0, h1, h2, h3, h4, h5, ?_, ?_, ?_, hg1, hg2, ?_⟩
    · intro i a ha
      simpa only [abs_ne_zero] using hp i a ha
    · intro i a ha
      simpa only [abs_abs] using hpl i a ha
    · intro i a ha
      simpa only [abs_abs] using hpa i a ha
    · rw [← hsum]
      exact hfam
  · intro h
    obtain ⟨h0, h1, h2, h3, h4, h5, hp, hpl, hpa, hg1, hg2, hfam⟩ := h
    refine ⟨h0, h1, h2, h3, h4, h5, ?_, ?_, ?_, hg1, hg2, ?_⟩
    · intro i a ha
      exact fun h0 => hp i a ha (by simp only [h0, abs_zero])
    · intro i a ha
      simpa only [abs_abs] using hpl i a ha
    · intro i a ha
      simpa only [abs_abs] using hpa i a ha
    · rw [hsum]
      exact hfam

end

end Work.Peluse.Prop36SW
