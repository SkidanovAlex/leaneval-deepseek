import Mathlib
import Submission.Work.Peluse.Prop36SW.roundDefs
import Submission.Work.Peluse.Ulower.finalTarget

/-!
# The absolute-value invariance of the chain state `LStateBox`

`Work.Peluse.Prop36SW.LStateBox kω p M₁ M₂ N Dc A g γ` differs from `LStateAbs` only by the
dropping of the non-vanishing conjunct, and it mentions the coefficient `p` in exactly three
places:

* the two shift bounds `|p i a| · M₁ · M₂ ≤ N` and `|p i a| · M₁ · M₂ ≤ Dc · N`, which only see
  `|p i a|`;
* the family hypothesis, whose directions are
  `pDirG p M₁ a a' ω = arithIcc (∑_{s ∈ ω} p s.1 a · a' s) M₁`.

This module proves that the state is **invariant under replacing `p` by `|p|`**:

`LStateBox kω p … γ ↔ LStateBox kω (fun i a => |p i a|) … γ`.

This is the form in which the state is fed to the ladder (`Work.Peluse.Prop36SW.PeluseLadderAG`
demands `0 < p i a` on the parameter set, which for a state carrying the non-vanishing conjunct is
supplied by `|p|`).

The point is the family hypothesis.  The *multiset* of directions changes when the coefficients are
replaced by their absolute values, but the average over the parameter box — which is a product of
*symmetric* intervals `(-M₂, M₂) ∩ ℤ` — is unchanged: the box carries the involution
`Θ(a')_s = -(a'_s)` for the slots `s` with `p s.1 a < 0` and `Θ(a')_s = a'_s` otherwise, and

    ∑_{s ∈ ω} p s.1 a · Θ(a')_s = ∑_{s ∈ ω} |p s.1 a| · a'_s

for every `ω` (pointwise in `s`: if `p s.1 a < 0` then `p · (-a') = (-p) · a' = |p| · a'`, and
otherwise `p = |p|`).  Hence `boxNorm` of the `p`-family at `a'` equals `boxNorm` of the `|p|`-family
at `Θ a'`, and reindexing the sum by the involution `Θ` gives the claim.

No invariance of the box norm under negating its directions is needed: the reindexing is done at
the level of the (pointwise equal) direction *values*.
-/

open scoped BigOperators
open Work.Peluse Work.Peluse.UControl Work.Peluse.Prop36SW

namespace Work.Prop36SW

noncomputable section

/-- The interval `(-M, M) ∩ ℤ` is symmetric under negation. -/
private lemma neg_mem_Ioo {M : ℕ} {y : ℤ} (hy : y ∈ Finset.Ioo (-(M : ℤ)) (M : ℤ)) :
    -y ∈ Finset.Ioo (-(M : ℤ)) (M : ℤ) := by
  rw [Finset.mem_Ioo] at hy ⊢
  omega

/-- **The family average is unchanged by replacing the coefficients by their absolute values.**
For a single parameter `a`, the sum over the parameter box of the box norms of the `pDirFamG`
family agrees for `p` and for `|p|`. -/
private lemma sum_boxNorm_pDirFamG_abs {ι : Type} [Fintype ι] [DecidableEq ι] {P : Type}
    (kω : SlotSet ι (fun _ => 1) → ℕ) (p : ι → P → ℤ) (M₁ M₂ N : ℕ) (a : P) (g : ℤ → ℂ) :
    (∑ a' ∈ paramBox (k := fun _ : ι => 1) M₂,
        boxNorm (Fintype.card (FamIdx kω))
          (fun j => pDirFamG p M₁ a a' ((Fintype.equivFin (FamIdx kω)).symm j)) (symIcc N) g)
      = (∑ a' ∈ paramBox (k := fun _ : ι => 1) M₂,
        boxNorm (Fintype.card (FamIdx kω))
          (fun j => pDirFamG (fun i a => |p i a|) M₁ a a'
            ((Fintype.equivFin (FamIdx kω)).symm j)) (symIcc N) g) := by
  -- the sign involution of the parameter box
  let Θ : (Slot ι (fun _ => 1) → ℤ) → (Slot ι (fun _ => 1) → ℤ) :=
    fun a' s => if p s.1 a < 0 then -(a' s) else a' s
  have hΘ_apply : ∀ a' s, Θ a' s = (if p s.1 a < 0 then -(a' s) else a' s) := fun a' s => rfl
  -- `Θ` maps the box to itself
  have hΘmem : ∀ a' ∈ paramBox (k := fun _ : ι => 1) M₂,
      Θ a' ∈ paramBox (k := fun _ : ι => 1) M₂ := by
    intro a' ha'
    rw [paramBox, Fintype.mem_piFinset] at ha' ⊢
    intro s
    have hs := ha' s
    simp only [hΘ_apply]
    by_cases h : p s.1 a < 0
    · simp only [h, if_pos]
      exact neg_mem_Ioo hs
    · simp only [h, ↓reduceIte]
      exact hs
  -- `Θ` is an involution
  have hΘinv : ∀ a', Θ (Θ a') = a' := by
    intro a'
    funext s
    simp only [hΘ_apply]
    by_cases h : p s.1 a < 0
    · simp only [h, if_pos, neg_neg]
    · simp only [h, ↓reduceIte]
  -- the direction sums agree
  have hdir : ∀ a' ∈ paramBox (k := fun _ : ι => 1) M₂, ∀ ω : SlotSet ι (fun _ => 1),
      (∑ s ∈ ω.1, p s.1 a * a' s) = (∑ s ∈ ω.1, |p s.1 a| * Θ a' s) := by
    intro a' ha' ω
    refine Finset.sum_congr rfl (fun s _ => ?_)
    simp only [hΘ_apply]
    by_cases h : p s.1 a < 0
    · simp only [h, if_pos, abs_of_neg h]; ring
    · simp only [h, ↓reduceIte, abs_of_nonneg (le_of_not_gt h)]
  -- hence the two direction families agree, `Θ` reindexing the parameters
  have hfam : ∀ a' ∈ paramBox (k := fun _ : ι => 1) M₂,
      (fun j : Fin (Fintype.card (FamIdx kω)) =>
          pDirFamG p M₁ a a' ((Fintype.equivFin (FamIdx kω)).symm j))
        = (fun j : Fin (Fintype.card (FamIdx kω)) =>
          pDirFamG (fun i a => |p i a|) M₁ a (Θ a')
            ((Fintype.equivFin (FamIdx kω)).symm j)) := by
    intro a' ha'
    funext j
    simp only [pDirFamG, pDirG]
    rw [hdir a' ha' ((Fintype.equivFin (FamIdx kω)).symm j).1]
  refine Finset.sum_bij' (i := fun a' _ => Θ a') (j := fun b' _ => Θ b')
    (fun a' ha' => hΘmem a' ha') (fun b' hb' => hΘmem b' hb')
    (fun a' _ => hΘinv a') (fun b' _ => hΘinv b') (fun a' ha' => ?_)
  rw [hfam a' ha']

/-- The average over the parameter set `A` of the family bound, with the coefficients replaced by
their absolute values. -/
private lemma famSum_abs {ι : Type} [Fintype ι] [DecidableEq ι] {P : Type} [DecidableEq P]
    (kω : SlotSet ι (fun _ => 1) → ℕ) (p : ι → P → ℤ) (M₁ M₂ N : ℕ) (A : Finset P)
    (g : P → ℤ → ℂ) :
    (∑ a ∈ A, ∑ a' ∈ paramBox (k := fun _ : ι => 1) M₂,
        boxNorm (Fintype.card (FamIdx kω))
          (fun j => pDirFamG p M₁ a a' ((Fintype.equivFin (FamIdx kω)).symm j)) (symIcc N) (g a))
      = (∑ a ∈ A, ∑ a' ∈ paramBox (k := fun _ : ι => 1) M₂,
        boxNorm (Fintype.card (FamIdx kω))
          (fun j => pDirFamG (fun i a => |p i a|) M₁ a a'
            ((Fintype.equivFin (FamIdx kω)).symm j)) (symIcc N) (g a)) := by
  refine Finset.sum_congr rfl (fun a _ => ?_)
  exact sum_boxNorm_pDirFamG_abs kω p M₁ M₂ N a (g a)

theorem LStateBoxAbsIff {ι : Type} [Fintype ι] [DecidableEq ι]
    {kω : Work.Peluse.UControl.SlotSet ι (fun _ => 1) → ℕ} {P : Type} [DecidableEq P]
    {p : ι → P → ℤ} {M₁ M₂ N Dc : ℕ} {A : Finset P} {g : P → ℤ → ℂ} {γ : ℝ} :
    (Work.Peluse.Prop36SW.LStateBox kω p M₁ M₂ N Dc A g γ ↔
      Work.Peluse.Prop36SW.LStateBox kω (fun i a => |p i a|) M₁ M₂ N Dc A g γ) := by
  have hsum := famSum_abs (kω := kω) (p := p) (M₁ := M₁) (M₂ := M₂) (N := N) (A := A) (g := g)
  simp only [Work.Peluse.Prop36SW.LStateBox]
  constructor
  · rintro ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10⟩
    refine ⟨h0, h1, h2, h3, h4, h5, ?_, ?_, h8, h9, ?_⟩
    · intro i a ha; simpa only [abs_abs] using h6 i a ha
    · intro i a ha; simpa only [abs_abs] using h7 i a ha
    · rw [← hsum]; exact h10
  · rintro ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10⟩
    refine ⟨h0, h1, h2, h3, h4, h5, ?_, ?_, h8, h9, ?_⟩
    · intro i a ha; simpa only [abs_abs] using h6 i a ha
    · intro i a ha; simpa only [abs_abs] using h7 i a ha
    · rw [hsum]; exact h10

end

end Work.Prop36SW
