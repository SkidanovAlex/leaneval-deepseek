import Submission.Work.WilG1.OneDim.thin_nointerval

set_option autoImplicit false
noncomputable section
open Classical

namespace Work.WilG1.OneDim

open WilkiesDesign

/-! ## 11. Finiteness of thin `Ω`-sets inside an interval -/

/-- An `Ω`-subset of `ℝ¹` that contains no non-degenerate subinterval of `(c,d)` meets `(c,d)`
in a finite set.  (`comps` writes it as a finite union of preconnected pieces; each piece is
order-convex, so its trace on `(c,d)` is a subsingleton.) -/
theorem finite_of_omega_noInterval {S : WilkiesDesign.SOMin} {a b : ℕ} {g : ℝ → ℝ} {P : Set ℝ}
    {c d : ℝ} (hA : Work.WilG1.liftR P ∈ S.Ω a b 1)
    (hno : ∀ u v : ℝ, c ≤ u → u < v → v ≤ d → Set.Ioo u v ⊆ P → False) :
    ({x : ℝ | x ∈ Set.Ioo c d ∧ x ∈ P} : Set ℝ).Finite := by
  obtain ⟨p, hp⟩ := S.comps a
  obtain ⟨s, hcard, hconn, hAeq⟩ := hp b (Work.WilG1.liftR P) hA
  set emb : ℝ → (Fin 1 → ℝ) := fun x _ => x with hemb
  set e : (Fin 1 → ℝ) ≃ₜ ℝ := Homeomorph.funUnique (Fin 1) ℝ with he
  have he_emb : ∀ x : ℝ, e (emb x) = x := fun x => rfl
  have hstep : ∀ κ ∈ s, ∀ x y : ℝ, emb x ∈ κ → emb y ∈ κ → Set.Ioo x y ⊆ P := by
    intro κ hκ x y hxκ hyκ
    have hpre : IsPreconnected (e '' κ) := (hconn κ hκ).image e e.continuous.continuousOn
    have hIcc : Set.Icc x y ⊆ e '' κ :=
      hpre.Icc_subset ⟨emb x, hxκ, he_emb x⟩ ⟨emb y, hyκ, he_emb y⟩
    intro t ht
    obtain ⟨w, hwκ, hwt⟩ := hIcc ⟨le_of_lt ht.1, le_of_lt ht.2⟩
    have hwt' : w = emb t := e.injective (by rw [hwt, he_emb])
    have htκ : emb t ∈ κ := hwt' ▸ hwκ
    have hmem : emb t ∈ Work.WilG1.liftR P := by
      rw [hAeq]; exact Set.mem_sUnion.mpr ⟨κ, hκ, htκ⟩
    simpa [Work.WilG1.liftR, hemb] using hmem
  have hpiece : ∀ κ ∈ s,
      ({x : ℝ | x ∈ Set.Ioo c d ∧ emb x ∈ κ} : Set ℝ).Subsingleton := by
    intro κ hκ x hx y hy
    by_contra hne
    rcases lt_or_gt_of_ne hne with hlt | hlt
    · exact hno x y hx.1.1.le hlt hy.1.2.le (hstep κ hκ x y hx.2 hy.2)
    · exact hno y x hy.1.1.le hlt hx.1.2.le (hstep κ hκ y x hy.2 hx.2)
  have hset : {x : ℝ | x ∈ Set.Ioo c d ∧ x ∈ P} =
      ⋃ κ ∈ (s : Set (Set (Fin 1 → ℝ))), {x : ℝ | x ∈ Set.Ioo c d ∧ emb x ∈ κ} := by
    ext x
    simp only [Set.mem_setOf_eq, Set.mem_iUnion, exists_prop]
    constructor
    · intro hx
      have hmem : emb x ∈ Work.WilG1.liftR P := by
        simpa [Work.WilG1.liftR, hemb] using hx.2
      rw [hAeq] at hmem
      obtain ⟨κ, hκ, hxκ⟩ := Set.mem_sUnion.mp hmem
      exact ⟨κ, hκ, hx.1, hxκ⟩
    · rintro ⟨κ, hκ, hx1, hx2⟩
      refine ⟨hx1, ?_⟩
      have hmem : emb x ∈ Work.WilG1.liftR P := by
        rw [hAeq]; exact Set.mem_sUnion.mpr ⟨κ, hκ, hx2⟩
      simpa [Work.WilG1.liftR, hemb] using hmem
  rw [hset]
  exact Set.Finite.biUnion s.finite_toSet (fun κ hκ => (hpiece κ hκ).finite)

/-! ## 12. Countably many discontinuities -/

/-- If the boundaries of the level sets of `g` are finite (at every rational level), then `g`
has only countably many discontinuities. -/
theorem countable_not_continuousAt {g : ℝ → ℝ}
    (hfin1 : ∀ r : ℚ, ({x : ℝ | x ∈ closure {y : ℝ | g y > (r:ℝ)} ∧
        x ∈ closure {y : ℝ | g y > (r:ℝ)}ᶜ} : Set ℝ).Finite)
    (hfin2 : ∀ r : ℚ, ({x : ℝ | x ∈ closure {y : ℝ | g y ≥ (r:ℝ)} ∧
        x ∈ closure {y : ℝ | g y ≥ (r:ℝ)}ᶜ} : Set ℝ).Finite) :
    {x : ℝ | ¬ ContinuousAt g x}.Countable := by
  refine Set.Countable.mono ?_
    (Set.countable_iUnion (fun r : ℚ => ((hfin1 r).union (hfin2 r)).countable))
  intro x hx
  rw [Set.mem_setOf_eq] at hx
  have key : ∃ ε > 0, ∀ δ > 0, ∃ y : ℝ, dist y x < δ ∧ ε ≤ dist (g y) (g x) := by
    by_contra hcon
    push_neg at hcon
    exact hx (Metric.continuousAt_iff.mpr fun ε hε => hcon ε hε)
  obtain ⟨ε, hε, hwit⟩ := key
  by_cases hP : ∀ δ > 0, ∃ y : ℝ, dist y x < δ ∧ g x + ε ≤ g y
  · obtain ⟨r, hr1, hr2⟩ := exists_rat_btwn (show g x < g x + ε by linarith)
    refine Set.mem_iUnion.mpr ⟨r, Or.inl ⟨?_, ?_⟩⟩
    · rw [Metric.mem_closure_iff]
      intro η hη
      obtain ⟨y, hy1, hy2⟩ := hP (η/2) (by linarith)
      have hy1' : |y - x| < η / 2 := by rwa [Real.dist_eq] at hy1
      refine ⟨y, ?_, ?_⟩
      · show (r:ℝ) < g y
        linarith
      · rw [Real.dist_eq, abs_sub_comm]; linarith
    · apply subset_closure
      simp only [Set.mem_compl_iff, Set.mem_setOf_eq, not_lt]
      linarith
  · push_neg at hP
    obtain ⟨δ₀, hδ₀, hP'⟩ := hP
    have hQ : ∀ δ > 0, ∃ y : ℝ, dist y x < δ ∧ g y ≤ g x - ε := by
      intro δ hδ
      obtain ⟨y, hy1, hy2⟩ := hwit (min δ δ₀) (lt_min hδ hδ₀)
      have hnot : ¬ (g x + ε ≤ g y) :=
        not_le.mpr (hP' y (lt_of_lt_of_le hy1 (min_le_right δ δ₀)))
      refine ⟨y, lt_of_lt_of_le hy1 (min_le_left δ δ₀), ?_⟩
      have habs : ε ≤ |g y - g x| := by rw [← Real.dist_eq]; exact hy2
      rcases le_total 0 (g y - g x) with hpos | hneg
      · rw [abs_of_nonneg hpos] at habs; linarith
      · rw [abs_of_nonpos hneg] at habs; linarith
    obtain ⟨r, hr1, hr2⟩ := exists_rat_btwn (show g x - ε < g x by linarith)
    refine Set.mem_iUnion.mpr ⟨r, Or.inr ⟨?_, ?_⟩⟩
    · apply subset_closure
      simp only [Set.mem_setOf_eq]
      linarith
    · rw [Metric.mem_closure_iff]
      intro η hη
      obtain ⟨y, hy1, hy2⟩ := hQ (η/2) (by linarith)
      have hy1' : |y - x| < η / 2 := by rwa [Real.dist_eq] at hy1
      refine ⟨y, ?_, ?_⟩
      · simp only [Set.mem_compl_iff, Set.mem_setOf_eq, not_le]
        linarith
      · rw [Real.dist_eq, abs_sub_comm]; linarith

end Work.WilG1.OneDim
