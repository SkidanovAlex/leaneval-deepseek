import Mathlib
import Submission.Work.Wilkies.CG.Spec

set_option autoImplicit false

namespace Work.WilC5

/-- A finite set `S` of points of `F ⊆ K`, a monotone injective map `σ : F → N` into a linearly
ordered field `N`, and a cut point `x : K`.  One can place a point `y : N` in the cut defined by
`x` transported along `σ`: `y` lies above the `σ`-images of the members of `S` that are `≤ x` and
below those that are `≥ x`, and `y` avoids every `σ f` with `(f : K) ≠ x`.  (When some `f ∈ S` has
`(f : K) = x`, `y` is forced to be `σ f`.) -/
theorem exists_cut_point_finset {K N : Type}
    [FirstOrder.Language.Structure WilkiesDesign.CG.LRc K]
    [Field K] [LinearOrder K]
    [Field N] [LinearOrder N] [IsStrictOrderedRing N]
    (F : WilkiesDesign.CG.LRc.Substructure K) (σ : F → N) (x : K) (S : Finset F)
    (hord : ∀ f g : F, (f : K) ≤ (g : K) → σ f ≤ σ g)
    (hinj : Function.Injective σ) :
    ∃ y : N, (∀ f ∈ S, (f : K) ≤ x → σ f ≤ y) ∧ (∀ f ∈ S, x ≤ (f : K) → y ≤ σ f) ∧
      (∀ f ∈ S, (f : K) ≠ x → y ≠ σ f) := by
  classical
  by_cases hE : ∃ f ∈ S, (f : K) = x
  · -- some element of `S` sits exactly at the cut: `y = σ f` is forced
    obtain ⟨f0, hf0S, hf0x⟩ := hE
    refine ⟨σ f0, ?_, ?_, ?_⟩
    · intro f hf hle
      exact hord f f0 (by rw [hf0x]; exact hle)
    · intro f hf hle
      exact hord f0 f (by rw [hf0x]; exact hle)
    · intro f hf hne hfeq
      exact hne (by rw [← hinj hfeq]; exact hf0x)
  · -- no element of `S` sits at the cut
    have hE' : ∀ f ∈ S, (f : K) ≠ x := fun f hf h => hE ⟨f, hf, h⟩
    -- trichotomy: every element is strictly below or strictly above the cut
    have hAB : ∀ f ∈ S, (f : K) < x ∨ x < (f : K) := by
      intro f hf
      rcases lt_trichotomy (f : K) x with h | h | h
      · exact Or.inl h
      · exact absurd h (hE' f hf)
      · exact Or.inr h
    let A : Finset F := S.filter (fun f => (f : K) < x)
    let B : Finset F := S.filter (fun f => x < (f : K))
    have hA1 : ∀ {f : F}, f ∈ A ↔ f ∈ S ∧ (f : K) < x := fun {f} => Finset.mem_filter
    have hB1 : ∀ {f : F}, f ∈ B ↔ f ∈ S ∧ x < (f : K) := fun {f} => Finset.mem_filter
    rcases A.eq_empty_or_nonempty with hA | hA
    · rcases B.eq_empty_or_nonempty with hB | hB
      · -- `S` is empty: anything works
        have hSne : ¬ S.Nonempty := by
          rintro ⟨f, hf⟩
          rcases hAB f hf with hlt | hgt
          · have hmem : f ∈ A := hA1.mpr ⟨hf, hlt⟩
            rw [hA] at hmem
            exact absurd hmem (Finset.notMem_empty f)
          · have hmem : f ∈ B := hB1.mpr ⟨hf, hgt⟩
            rw [hB] at hmem
            exact absurd hmem (Finset.notMem_empty f)
        have hS : S = ∅ := Finset.not_nonempty_iff_eq_empty.mp hSne
        exact ⟨0, by simp [hS], by simp [hS], by simp [hS]⟩
      · -- `S` lies entirely above the cut: push below the minimum
        have hSB : ∀ f ∈ S, x < (f : K) := by
          intro f hf
          rcases hAB f hf with hlt | hgt
          · exfalso
            have hmem : f ∈ A := hA1.mpr ⟨hf, hlt⟩
            rw [hA] at hmem
            exact absurd hmem (Finset.notMem_empty f)
          · exact hgt
        obtain ⟨g0, hg0B, hg0min⟩ := Finset.exists_min_image B (fun f => σ f) hB
        refine ⟨σ g0 - 1, ?_, ?_, ?_⟩
        · intro f hf hle
          exact absurd (lt_of_lt_of_le (hSB f hf) hle) (lt_irrefl x)
        · intro f hf hle
          have hfB : f ∈ B := hB1.mpr ⟨hf, hSB f hf⟩
          exact le_of_lt
            (lt_of_lt_of_le (sub_lt_self (σ g0) (zero_lt_one (α := N))) (hg0min f hfB))
        · intro f hf hne hfeq
          have hfB : f ∈ B := hB1.mpr ⟨hf, hSB f hf⟩
          have hlt : σ g0 - 1 < σ f :=
            lt_of_lt_of_le (sub_lt_self (σ g0) (zero_lt_one (α := N))) (hg0min f hfB)
          exact (ne_of_lt hlt) hfeq
    · rcases B.eq_empty_or_nonempty with hB | hB
      · -- `S` lies entirely below the cut: push above the maximum
        have hSA : ∀ f ∈ S, (f : K) < x := by
          intro f hf
          rcases hAB f hf with hlt | hgt
          · exact hlt
          · exfalso
            have hmem : f ∈ B := hB1.mpr ⟨hf, hgt⟩
            rw [hB] at hmem
            exact absurd hmem (Finset.notMem_empty f)
        obtain ⟨f0, hf0A, hf0max⟩ := Finset.exists_max_image A (fun f => σ f) hA
        refine ⟨σ f0 + 1, ?_, ?_, ?_⟩
        · intro f hf hle
          have hfA : f ∈ A := hA1.mpr ⟨hf, hSA f hf⟩
          exact le_of_lt (lt_of_le_of_lt (hf0max f hfA)
            (lt_add_of_pos_right (σ f0) (zero_lt_one (α := N))))
        · intro f hf hle
          exact absurd (lt_of_lt_of_le (hSA f hf) hle) (lt_irrefl _)
        · intro f hf hne hfeq
          have hfA : f ∈ A := hA1.mpr ⟨hf, hSA f hf⟩
          have hlt : σ f < σ f0 + 1 :=
            lt_of_le_of_lt (hf0max f hfA) (lt_add_of_pos_right (σ f0) (zero_lt_one (α := N)))
          exact (ne_of_lt hlt) hfeq.symm
      · -- elements strictly on both sides: the interval between the maximum of the lower ones and
        -- the minimum of the upper ones is nondegenerate, and its interior contains `y`
        obtain ⟨f0, hf0A, hf0max⟩ := Finset.exists_max_image A (fun f => σ f) hA
        obtain ⟨g0, hg0B, hg0min⟩ := Finset.exists_min_image B (fun f => σ f) hB
        have hf0lt : (f0 : K) < x := (hA1.mp hf0A).2
        have hg0gt : x < (g0 : K) := (hB1.mp hg0B).2
        have hgap : σ f0 < σ g0 := by
          have hle : σ f0 ≤ σ g0 := hord f0 g0 (le_of_lt (lt_trans hf0lt hg0gt))
          rcases lt_or_eq_of_le hle with h | h
          · exact h
          · exfalso
            have hfg : f0 = g0 := hinj h
            rw [hfg] at hf0lt
            exact absurd (lt_trans hf0lt hg0gt) (lt_irrefl (g0 : K))
        obtain ⟨y, hy1, hy2⟩ := exists_between hgap
        refine ⟨y, ?_, ?_, ?_⟩
        · intro f hf hle
          have hfx : (f : K) < x := lt_of_le_of_ne hle (hE' f hf)
          have hfA : f ∈ A := hA1.mpr ⟨hf, hfx⟩
          exact le_of_lt (lt_of_le_of_lt (hf0max f hfA) hy1)
        · intro f hf hle
          have hfx : x < (f : K) := lt_of_le_of_ne hle (Ne.symm (hE' f hf))
          have hfB : f ∈ B := hB1.mpr ⟨hf, hfx⟩
          exact le_of_lt (lt_of_lt_of_le hy2 (hg0min f hfB))
        · intro f hf hne hfeq
          rcases hAB f hf with hlt | hgt
          · have hfA : f ∈ A := hA1.mpr ⟨hf, hlt⟩
            have : σ f < y := lt_of_le_of_lt (hf0max f hfA) hy1
            exact (ne_of_lt this) hfeq.symm
          · have hfB : f ∈ B := hB1.mpr ⟨hf, hgt⟩
            have : y < σ f := lt_of_lt_of_le hy2 (hg0min f hfB)
            exact (ne_of_gt this) hfeq.symm

end Work.WilC5
