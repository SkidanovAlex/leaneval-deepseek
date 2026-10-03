import Mathlib
import Submission.Work.Peluse.ladderA_defs

namespace Work.Peluse.LadderA

/-- Splitting a sum over a `Fintype.piFinset` along one coordinate: the functions ranging over the
`pi`-box are indexed by the value `y` of the coordinate `x` together with the choice of the
remaining coordinates, recorded here as the "canonical" representative whose `x`-coordinate is a
fixed admissible value `c`. -/
private theorem sum_piFinset_update_split {α : Type} [DecidableEq α] [Fintype α]
    {β : α → Type} [(a : α) → DecidableEq (β a)] (u : ∀ a, Finset (β a))
    (x : α) (c : β x) (hc : c ∈ u x) {M : Type*} [AddCommMonoid M]
    (G : (∀ a, β a) → M) :
    (∑ y ∈ u x, ∑ f ∈ (Fintype.piFinset u).filter (fun f => f x = c),
        G (Function.update f x y)) = ∑ f ∈ Fintype.piFinset u, G f := by
  classical
  -- decompose `piFinset u` into the fibres of the evaluation at `x` ...
  have hstep1 : (∑ y ∈ u x, ∑ f ∈ (Fintype.piFinset u).filter (fun f => f x = y), G f)
      = ∑ f ∈ Fintype.piFinset u, G f :=
    Finset.sum_fiberwise_of_maps_to (s := Fintype.piFinset u) (t := u x)
      (g := fun f => f x) (fun f hf => Fintype.mem_piFinset.mp hf x) G
  -- ... and rewrite each fibre as the canonical fibre `{· x = c}` via `update`.
  have hstep2 : ∀ y ∈ u x,
      (∑ f ∈ (Fintype.piFinset u).filter (fun f => f x = c), G (Function.update f x y))
      = ∑ f ∈ (Fintype.piFinset u).filter (fun f => f x = y), G f := by
    intro y hy
    refine Finset.sum_bij (fun (f : ∀ a, β a) _ => Function.update f x y) ?_ ?_ ?_ ?_
    · intro f hf
      obtain ⟨hfs, _⟩ := Finset.mem_filter.mp hf
      refine Finset.mem_filter.mpr ⟨?_, by simp⟩
      rw [Fintype.mem_piFinset] at hfs ⊢
      intro a
      rcases eq_or_ne a x with rfl | ha
      · simpa using hy
      · rw [Function.update_of_ne ha]; exact hfs a
    · intro f₁ hf₁ f₂ hf₂ heq
      obtain ⟨hfs₁, hfx₁⟩ := Finset.mem_filter.mp hf₁
      obtain ⟨hfs₂, hfx₂⟩ := Finset.mem_filter.mp hf₂
      funext a
      rcases eq_or_ne a x with rfl | ha
      · have h₁ : f₁ a = c := hfx₁
        have h₂ : f₂ a = c := hfx₂
        rw [h₁, h₂]
      · have := congr_fun heq a
        rw [Function.update_of_ne ha, Function.update_of_ne ha] at this
        exact this
    · intro g hg
      obtain ⟨hgs, hgx⟩ := Finset.mem_filter.mp hg
      refine ⟨Function.update g x c, ?_, ?_⟩
      · refine Finset.mem_filter.mpr ⟨?_, by simp⟩
        rw [Fintype.mem_piFinset] at hgs ⊢
        intro a
        rcases eq_or_ne a x with rfl | ha
        · simpa using hc
        · rw [Function.update_of_ne ha]; exact hgs a
      · rw [Function.update_idem, ← hgx, Function.update_eq_self]
    · intro f hf; rfl
  calc (∑ y ∈ u x, ∑ f ∈ (Fintype.piFinset u).filter (fun f => f x = c),
          G (Function.update f x y))
      = ∑ y ∈ u x, ∑ f ∈ (Fintype.piFinset u).filter (fun f => f x = y), G f :=
        Finset.sum_congr rfl (fun y hy => hstep2 y hy)
    _ = ∑ f ∈ Fintype.piFinset u, G f := hstep1

theorem sum_paramBox_split {ι : Type} [Fintype ι] [DecidableEq ι] (k : ι → ℕ)
    (M₂ : ℕ) (s₀ : Work.Peluse.UControl.Slot ι k) {M : Type*} [AddCommMonoid M]
    (G : (Work.Peluse.UControl.Slot ι k → ℤ) → M) :
    (∑ a' ∈ Work.Peluse.UControl.paramBox (k := k) M₂, G a') =
      ∑ a₀ ∈ Finset.Ioo (-(M₂ : ℤ)) (M₂ : ℤ),
        ∑ a'' ∈ (Work.Peluse.UControl.paramBox (k := k) M₂).filter (fun a'' => a'' s₀ = 0),
          G (Function.update a'' s₀ a₀) := by
  classical
  by_cases hM₂ : M₂ = 0
  · -- the box (and the index set) are empty
    subst hM₂
    have hbox : Work.Peluse.UControl.paramBox (k := k) 0 = ∅ := by
      rw [Work.Peluse.UControl.paramBox, Fintype.piFinset_eq_empty]
      exact ⟨s₀, by simp⟩
    rw [hbox]
    simp
  · -- otherwise split off the `s₀`-coordinate at the admissible value `0`
    refine (sum_piFinset_update_split (u := fun _ : Work.Peluse.UControl.Slot ι k =>
        Finset.Ioo (-(M₂ : ℤ)) (M₂ : ℤ)) (x := s₀) (c := 0) ?_ G).symm
    rw [Finset.mem_Ioo]
    have hpos : 0 < (M₂ : ℤ) := by exact_mod_cast Nat.pos_of_ne_zero hM₂
    omega

end Work.Peluse.LadderA
