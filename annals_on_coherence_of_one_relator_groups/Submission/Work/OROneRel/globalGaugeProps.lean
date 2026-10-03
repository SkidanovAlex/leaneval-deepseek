import Mathlib
import Submission.Work.OROneRel.globalGauge
import Submission.Work.OROneRel.levelChain
import Submission.Work.OROneRel.WrelGen_supported
import Submission.Work.OROneRel.WrelDown_supported
import Submission.Work.OROneRel.walkWord_step_up
import Submission.Work.OROneRel.walkWord_step_down

/-!
# The trivial-edge tree of the global gauge

Let `Wt' = gaugeExt p q hq Wt` be the global gauge of
`Submission/Work/OROneRel/globalGauge.lean` and write `pq = (p : ℤ) * (q : ℤ)`.  This file collects
the facts that let the window chain of `Submission/Work/OROneRel/levelChain.lean` run with the
*actual* trivial-edge tree of `Wt'`: writing `τb = {e | coverClassAt Wt' (tlW p q) e = 1}`,

* `coverClassAt_gaugeExt_of_band`: on the band the gauge `Wt'` computes the same loop classes as `Wt`;
* `trivTree_band`: consequently `τb ∩ Wedge p q 0 pq = winTree Wt (tlW p q) 0 pq` (definitionally the
  edge sets `Wedge p q` and `winE (tlW p q)` agree);
* `trivTree_sub`: every trivial edge of a window `[A,B]` (`A ≤ 0 ≤ pq ≤ B`) lies in
  `TallGlob p q T₀`, i.e. is a band tree edge or an `a`-edge outside the band (the `a`-edges outside
  the band are trivial by construction; the `b`-edges outside the band are not, by the hypotheses
  `hbgt` and `hblt`);
* `trivTree_chain`: the window chain from `[A,B]` down to the band, with that tree.
-/

namespace Work.OROneRel

noncomputable section

variable {p q : ℕ} {hq : 1 ≤ q} {Wt : ℤ → FreeGroup (Fin 2)}

/-- **On the band, the global gauge computes the same loop classes as `Wt`.** -/
theorem coverClassAt_gaugeExt_of_band {e : Fin 2 × ℤ}
    (he : e ∈ winE (tlW p q) 0 ((p : ℤ) * (q : ℤ))) :
    coverClassAt (gaugeExt p q hq Wt) (tlW p q) e = coverClassAt Wt (tlW p q) e := by
  obtain ⟨h1, h2, h3, h4⟩ := he
  rw [coverClassAt, coverClassAt, gaugeMap_of, gaugeMap_of,
    gaugeExt_of_band (p := p) (q := q) h1 h2, gaugeExt_of_band (p := p) (q := q) h3 h4]

/-- **The trivial edges of the global gauge inside the band are the tree of `Wt`.** -/
theorem trivTree_band {p q : ℕ} {hq : 1 ≤ q} {Wt : ℤ → FreeGroup (Fin 2)} :
    {e : Fin 2 × ℤ | coverClassAt (gaugeExt p q hq Wt) (tlW p q) e = 1}
        ∩ Wedge p q 0 ((p : ℤ) * (q : ℤ))
      = winTree Wt (tlW p q) 0 ((p : ℤ) * (q : ℤ)) := by
  ext e
  simp only [Set.mem_inter_iff, Set.mem_ofPred_eq, mem_Wedge, winTree, mem_winE]
  constructor
  · rintro ⟨hcl, h1, h2, h3, h4⟩
    exact ⟨⟨h1, h2, h3, h4⟩,
      by rw [← coverClassAt_gaugeExt_of_band (p := p) (q := q) (hq := hq)
            (e := e) ⟨h1, h2, h3, h4⟩]; exact hcl⟩
  · rintro ⟨⟨h1, h2, h3, h4⟩, hcl⟩
    exact ⟨by rw [coverClassAt_gaugeExt_of_band (p := p) (q := q) (hq := hq)
            (e := e) ⟨h1, h2, h3, h4⟩]; exact hcl, h1, h2, h3, h4⟩

/-- The trivial edges of the band of the window are the tree of the gauge. -/
theorem trivTree_band' {p q : ℕ} {Wt' : ℤ → FreeGroup (Fin 2)} :
    {e : Fin 2 × ℤ | coverClassAt Wt' (tlW p q) e = 1} ∩ Wedge p q 0 ((p : ℤ) * (q : ℤ))
      = winTree Wt' (tlW p q) 0 ((p : ℤ) * (q : ℤ)) := by
  ext e
  simp only [Set.mem_inter_iff, Set.mem_ofPred_eq, mem_Wedge, winTree, mem_winE]
  tauto

/-- **Every trivial edge of a window `[A,B]` lies in `TallGlob`.**  The `a`-edges outside the band
are trivial by construction, and the `b`-edges outside the band are not (the hypotheses `hbgt`,
`hblt`), so the only trivial `b`-edges are the band ones, which are already in the band tree. -/
theorem trivTree_sub {p q : ℕ} {hq : 1 ≤ q} {Wt' : ℤ → FreeGroup (Fin 2)}
    {T₀ : Set (Fin 2 × ℤ)} (hT₀ : T₀ = winTree Wt' (tlW p q) 0 ((p : ℤ) * (q : ℤ)))
    (hbgt : ∀ {j : ℤ}, (p : ℤ) * (q : ℤ) < j →
      coverClassAt Wt' (tlW p q) ((1 : Fin 2), j) ≠ 1)
    (hblt : ∀ {j : ℤ}, j ≤ (p : ℤ) - 1 →
      coverClassAt Wt' (tlW p q) ((1 : Fin 2), j) ≠ 1)
    {A B : ℤ} (hA : A ≤ 0) (hB : (p : ℤ) * (q : ℤ) ≤ B) :
    {e : Fin 2 × ℤ | coverClassAt Wt' (tlW p q) e = 1} ∩ Wedge p q A B
      ⊆ Wtree p q T₀ A B := by
  intro e he
  obtain ⟨hcl, hw⟩ := he
  obtain ⟨x, i⟩ := e
  have hcl : coverClassAt Wt' (tlW p q) (x, i) = 1 := hcl
  have hw : A ≤ i ∧ i ≤ B ∧ A ≤ i + tlW p q x ∧ i + tlW p q x ≤ B := hw
  rw [Wtree, Set.mem_inter_iff]
  refine ⟨?_, by rw [mem_Wedge]; exact hw⟩
  rw [TallGlob, Set.mem_union, Set.mem_ofPred_eq]
  have hx : x = 0 ∨ x = 1 := by fin_cases x <;> simp
  rcases hx with h0 | h1
  · subst h0
    by_cases hi : i < 0
    · exact Or.inr ⟨rfl, Or.inl hi⟩
    · by_cases hi2 : (p : ℤ) * (q : ℤ) - (q : ℤ) < i
      · exact Or.inr ⟨rfl, Or.inr hi2⟩
      · refine Or.inl ?_
        simp only [hT₀, winTree, mem_winE, Set.mem_ofPred_eq, tlW_zero]
        exact ⟨⟨by omega, by omega, by omega, by omega⟩, hcl⟩
  · subst h1
    by_cases hj : i < (p : ℤ)
    · exact absurd hcl (hblt (by omega))
    · by_cases hj2 : (p : ℤ) * (q : ℤ) < i
      · exact absurd hcl (hbgt hj2)
      · refine Or.inl ?_
        simp only [hT₀, winTree, mem_winE, Set.mem_ofPred_eq, tlW_one]
        exact ⟨⟨by omega, by omega, by omega, by omega⟩, hcl⟩

/-- At the level `pq` the two-sided relator set is the one-sided one. -/
theorem WrelGen_eq_WrelDown (p q l : ℕ) (a : ℤ) :
    WrelGen p q l a ((p : ℤ) * (q : ℤ)) = WrelDown p q l a := by
  ext w
  simp only [WrelGen, WrelDown, Set.mem_ofPred_eq]
  constructor
  · rintro ⟨m, hm1, hm2, rfl⟩
    exact ⟨m, hm1, by omega, rfl⟩
  · rintro ⟨m, hm1, hm2, rfl⟩
    exact ⟨m, hm1, by omega, rfl⟩

/-- `T₀` is the tree of the window `[0,pq]` of the `Wtree` family. -/
theorem Wtree_band {p q : ℕ} {T₀ : Set (Fin 2 × ℤ)}
    (hT₀sub : T₀ ⊆ Wedge p q 0 ((p : ℤ) * (q : ℤ))) :
    Wtree p q T₀ 0 ((p : ℤ) * (q : ℤ)) = T₀ := by
  ext e
  rw [Wtree, Set.mem_inter_iff, TallGlob, Set.mem_union, Set.mem_ofPred_eq, mem_Wedge]
  constructor
  · rintro ⟨h | h, hw⟩
    · exact h
    · obtain ⟨h1, h2 | h2⟩ := h
      · exact absurd hw.1 (by omega)
      · have h4 : e.2 + tlW p q e.1 ≤ (p : ℤ) * (q : ℤ) := hw.2.2.2
        rw [h1, tlW_zero] at h4
        omega
  · intro h
    exact ⟨Or.inl h, hT₀sub h⟩

/-! ## The chain of windows, with the actual trivial-edge tree -/

/-- **The window chain with the trivial-edge tree of the gauge.** -/
theorem trivTree_chain {p q l : ℕ} (hp : 1 ≤ p) {hq : 1 ≤ q} {Wt' : ℤ → FreeGroup (Fin 2)}
    {T₀ : Set (Fin 2 × ℤ)} (hT₀ : T₀ = winTree Wt' (tlW p q) 0 ((p : ℤ) * (q : ℤ)))
    (hT₀sub : T₀ ⊆ Wedge p q 0 ((p : ℤ) * (q : ℤ)))
    (hbgt : ∀ {j : ℤ}, (p : ℤ) * (q : ℤ) < j →
      coverClassAt Wt' (tlW p q) ((1 : Fin 2), j) ≠ 1)
    (hblt : ∀ {j : ℤ}, j ≤ (p : ℤ) - 1 →
      coverClassAt Wt' (tlW p q) ((1 : Fin 2), j) ≠ 1)
    {A B : ℤ} (hA : A ≤ 0) (hB : (p : ℤ) * (q : ℤ) ≤ B)
    {y : FreeGroup (Fin 2 × ℤ)}
    (hy : y ∈ Subgroup.closure (FreeGroup.of '' Wedge p q 0 ((p : ℤ) * (q : ℤ))))
    (hy' : y ∈ Subgroup.normalClosure (FreeGroup.of ''
      ({e : Fin 2 × ℤ | coverClassAt Wt' (tlW p q) e = 1} ∩ Wedge p q A B)
      ∪ WrelGen p q l A B)) :
    y ∈ Subgroup.normalClosure (FreeGroup.of ''
      ({e : Fin 2 × ℤ | coverClassAt Wt' (tlW p q) e = 1}
        ∩ Wedge p q 0 ((p : ℤ) * (q : ℤ)))
      ∪ {FreeGroup.mk (decor (tlW p q) 0 (wordOf (tlU p q ^ l)))}) := by
  have hsub := trivTree_sub (p := p) (q := q) (hq := hq) hT₀ hbgt hblt hA hB
  have hsup : ∀ {a b : ℤ}, WrelGen p q l a b ⊆
      Subgroup.closure (FreeGroup.of '' Wedge p q a b) := fun {a b} => WrelGen_supported p q l hp
  have hwalkUp : ∀ {A₀ b : ℤ}, A₀ ≤ 0 → (p : ℤ) * (q : ℤ) ≤ b → ∃ A' B' : FreeGroup (Fin 2 × ℤ),
      A' ∈ Subgroup.closure (FreeGroup.of '' Wedge p q A₀ b) ∧
      B' ∈ Subgroup.closure (FreeGroup.of '' Wedge p q A₀ b) ∧
      FreeGroup.mk (decor (tlW p q) (b + 1 - (p : ℤ) * (q : ℤ)) (wordOf (tlU p q ^ l))) =
        (A' * FreeGroup.of ((0 : Fin 2), b + 1 - (q : ℤ)) *
          FreeGroup.of ((1 : Fin 2), b + 1) * B') ^ l := by
    intro A₀ b hA₀ hb
    obtain ⟨A', B', hA', hB', hdec⟩ :=
      walkWord_step_up (p := p) (q := q) (l := l) hp hq b (by omega)
    refine ⟨A', B', ?_, ?_, hdec⟩
    · exact Subgroup.closure_mono (Set.image_mono (Wedge_mono p q hA₀ (by omega))) hA'
    · exact Subgroup.closure_mono (Set.image_mono (Wedge_mono p q hA₀ (by omega))) hB'
  have hwalkDown : ∀ {a : ℤ}, a ≤ 1 → ∃ C : FreeGroup (Fin 2 × ℤ),
      C ∈ Subgroup.closure (FreeGroup.of '' Wedge p q a ((p : ℤ) * (q : ℤ))) ∧
      FreeGroup.mk (decor (tlW p q) (a - 1) (wordOf (tlU p q ^ l))) =
        (FreeGroup.of ((0 : Fin 2), a - 1) * C *
          FreeGroup.of ((1 : Fin 2), a + (p : ℤ) - 1)) ^ l := by
    intro a ha
    obtain ⟨C, hC, hdec⟩ := walkWord_step_down (p := p) (q := q) (l := l) hp hq a ha
    exact ⟨C, hC, hdec⟩
  have h1 : y ∈ Subgroup.normalClosure (FreeGroup.of '' Wtree p q T₀ A B ∪ WrelGen p q l A B) :=
    Subgroup.normalClosure_mono (Set.union_subset_union (Set.image_mono hsub) subset_rfl) hy'
  have h2 := chain_up_iterate_gen (p := p) (q := q) l hp (by omega) (T₀ := T₀) hT₀sub
      (fun {a b} => hsup) hwalkUp hA hB
      (Subgroup.closure_mono (Set.image_mono (Wedge_mono p q hA le_rfl)) hy) h1
  rw [WrelGen_eq_WrelDown] at h2
  have h3 := chain_down_iterate (p := p) (q := q) l hp (by omega) (T₀ := T₀) hT₀sub
      (fun {a} ha => WrelDown_supported p q l hp ha) hwalkDown hA hy h2
  rw [Wtree_band (p := p) (q := q) hT₀sub] at h3
  rw [show WrelDown p q l 0 = {FreeGroup.mk (decor (tlW p q) 0 (wordOf (tlU p q ^ l)))} from by
        ext w
        simp only [WrelDown, Set.mem_ofPred_eq, Set.mem_singleton_iff]
        constructor
        · rintro ⟨m, hm1, hm2, rfl⟩
          rw [show m = 0 from by omega]
        · rintro rfl
          exact ⟨0, le_rfl, le_rfl, rfl⟩] at h3
  rw [hT₀] at h3
  rwa [← trivTree_band' (p := p) (q := q) (Wt' := Wt')] at h3


end

end Work.OROneRel
