import Mathlib

namespace Work.DSCOH

theorem dsAttachSdiffMem {α R : Type*} [DecidableEq α] [AddCommGroup R]
    (T Z : Finset α) (P : α → Prop) [DecidablePred P] (s : α → ℤ)
    (v : (i : α) → i ∈ T → P i → R) (w : (i : α) → i ∈ T → i ∉ Z → R)
    (hP : ∀ i, i ∈ T → i ∈ Z → ¬ P i)
    (hP2 : ∀ i, i ∈ T → i ∉ Z → P i)
    (hv : ∀ (i : α) (hiT : i ∈ T) (hiZ : i ∉ Z) (h : P i), v i hiT h = w i hiT hiZ) :
    (∑ i ∈ T.attach, s i.1 • (if h : P i.1 then v i.1 i.2 h else 0))
      = ∑ i ∈ (T \ Z).attach, s i.1 • w i.1 (Finset.mem_sdiff.mp i.2).1 (Finset.mem_sdiff.mp i.2).2 := by
  -- We compare both sides with the sum over `T.attach` restricted to the complement of `Z`.
  -- On `T ∩ Z` the `P`-condition fails (hP), so the corresponding term vanishes;
  -- on `T \ Z` the `P`-condition holds (hP2) and `v` agrees with `w` (hv).
  have hbij : (∑ i ∈ (T \ Z).attach, s i.1 • w i.1 (Finset.mem_sdiff.mp i.2).1 (Finset.mem_sdiff.mp i.2).2)
      = ∑ i ∈ T.attach.filter (fun i => i.1 ∉ Z), s i.1 • (if h : P i.1 then v i.1 i.2 h else 0) := by
    refine Finset.sum_bij (s := (T \ Z).attach) (t := T.attach.filter (fun i => i.1 ∉ Z))
      (f := fun i : ↥(T \ Z) => s i.1 • w i.1 (Finset.mem_sdiff.mp i.2).1 (Finset.mem_sdiff.mp i.2).2)
      (g := fun i : ↥T => s i.1 • (if h : P i.1 then v i.1 i.2 h else 0))
      (fun i _ => ⟨i.1, (Finset.mem_sdiff.mp i.2).1⟩) ?_ ?_ ?_ ?_
    · intro i hi
      exact Finset.mem_filter.mpr
        ⟨Finset.mem_attach _ ⟨i.1, (Finset.mem_sdiff.mp i.2).1⟩, (Finset.mem_sdiff.mp i.2).2⟩
    · intro a1 h1 a2 h2 hh
      exact Subtype.ext (congrArg (fun x : ↥T => (x : α)) hh)
    · intro b hb
      rw [Finset.mem_filter] at hb
      exact ⟨⟨b.1, Finset.mem_sdiff.mpr ⟨b.2, hb.2⟩⟩, Finset.mem_attach _ _, Subtype.ext rfl⟩
    · intro i hi
      have hT : i.1 ∈ T := (Finset.mem_sdiff.mp i.2).1
      have hZ : i.1 ∉ Z := (Finset.mem_sdiff.mp i.2).2
      have hP' : P i.1 := hP2 i.1 hT hZ
      show s i.1 • w i.1 hT hZ = s i.1 • (if h : P i.1 then v i.1 hT h else 0)
      rw [dite_eq_left hP', hv i.1 hT hZ hP']
  have hsub : (∑ i ∈ T.attach.filter (fun i => i.1 ∉ Z), s i.1 • (if h : P i.1 then v i.1 i.2 h else 0))
      = ∑ i ∈ T.attach, s i.1 • (if h : P i.1 then v i.1 i.2 h else 0) := by
    refine Finset.sum_subset (f := fun i : ↥T => s i.1 • (if h : P i.1 then v i.1 i.2 h else 0))
      (Finset.filter_subset _ _) ?_
    intro x hx hxf
    have hxZ : x.1 ∈ Z := by
      by_contra h
      exact hxf (Finset.mem_filter.mpr ⟨Finset.mem_attach _ x, h⟩)
    have hnotP : ¬ P x.1 := hP x.1 x.2 hxZ
    rw [dite_eq_right hnotP, smul_zero]
  rw [hbij, ← hsub]

end Work.DSCOH
