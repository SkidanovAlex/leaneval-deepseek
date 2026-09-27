import Mathlib

namespace Work.Topology

open MeasureTheory Set

/-- For a finite measure and a real-valued measurable function, the set of levels whose preimage
has positive measure is countable: a finite measure has at most countably many atoms. -/
private lemma countable_bad_levels {α : Type*} [MeasurableSpace α]
    (μ : MeasureTheory.Measure α) [MeasureTheory.IsFiniteMeasure μ] {f : α → ℝ}
    (hf : Measurable f) : {t : ℝ | μ (f ⁻¹' {t}) ≠ 0}.Countable := by
  classical
  have hcover : {t : ℝ | μ (f ⁻¹' {t}) ≠ 0} ⊆
      ⋃ n : ℕ, {t : ℝ | (n + 1 : ℝ)⁻¹ ≤ μ.real (f ⁻¹' {t})} := by
    intro t ht
    rw [Set.mem_iUnion]
    have hne : μ.real (f ⁻¹' {t}) ≠ 0 := fun h =>
      ht ((MeasureTheory.measureReal_eq_zero_iff (MeasureTheory.measure_ne_top μ _)).mp h)
    have hpos : 0 < μ.real (f ⁻¹' {t}) :=
      lt_of_le_of_ne MeasureTheory.measureReal_nonneg (Ne.symm hne)
    obtain ⟨n, hn⟩ := exists_nat_one_div_lt hpos
    exact ⟨n, by simpa using le_of_lt hn⟩
  refine Set.Countable.mono hcover (Set.countable_iUnion fun n => ?_)
  have hfin : ({t : ℝ | (n + 1 : ℝ)⁻¹ ≤ μ.real (f ⁻¹' {t})} : Set ℝ).Finite := by
    by_contra hc
    rw [Set.not_finite] at hc
    obtain ⟨N, hN⟩ := exists_nat_gt (μ.real Set.univ * ((n:ℝ) + 1))
    obtain ⟨s, hs_sub, hs_card⟩ := hc.exists_subset_card_eq N
    have hs : ∀ t ∈ s, (n + 1 : ℝ)⁻¹ ≤ μ.real (f ⁻¹' {t}) := fun t ht => hs_sub ht
    have hle : (s.card : ℝ) * (((n:ℝ) + 1)⁻¹) ≤ μ.real Set.univ := by
      have h1 : ∑ t ∈ s, μ.real (f ⁻¹' {t}) ≤ μ.real Set.univ := by
        rw [MeasureTheory.sum_measureReal_preimage_singleton s
          (fun y _ => hf (measurableSet_singleton y)) (fun a _ => MeasureTheory.measure_ne_top μ _)]
        exact MeasureTheory.measureReal_mono (Set.subset_univ _)
      have h2 : (s.card : ℝ) * (((n:ℝ) + 1)⁻¹) ≤ ∑ t ∈ s, μ.real (f ⁻¹' {t}) := by
        have h3 := Finset.card_nsmul_le_sum s (fun t => μ.real (f ⁻¹' {t})) (((n:ℝ) + 1)⁻¹) hs
        simpa [nsmul_eq_mul] using h3
      linarith
    rw [hs_card] at hle
    have hpos2 : (0:ℝ) < (n:ℝ) + 1 := by positivity
    have hmul := mul_le_mul_of_nonneg_right hle (le_of_lt hpos2)
    rw [mul_assoc, inv_mul_cancel₀ (ne_of_gt hpos2), mul_one] at hmul
    linarith
  exact hfin.countable

/-- For a finite measure on the measurable space and a measurable real-valued function, some
level in the open unit interval has null preimage. -/
private lemma exists_good_level {α : Type*} [MeasurableSpace α]
    (μ : MeasureTheory.Measure α) [MeasureTheory.IsFiniteMeasure μ] {f : α → ℝ}
    (hf : Measurable f) : ∃ t ∈ Set.Ioo (0:ℝ) 1, μ (f ⁻¹' {t}) = 0 := by
  have hcount := countable_bad_levels μ hf
  have hnot : ¬ (Set.Ioo (0:ℝ) 1).Countable := by
    rw [Cardinal.Real.Ioo_countable_iff]; norm_num
  by_contra h
  push Not at h
  exact hnot (Set.Countable.mono h hcount)

/-- Peeling lemma: if a compact set is covered by two open sets, one can cut out an open piece of
the first one, leaving a compact remainder inside the second, whose boundary meets the compact set
in a null set. -/
private lemma exists_open_peel {X : Type*} [TopologicalSpace X] [T2Space X] [NormalSpace X]
    [MeasurableSpace X] [BorelSpace X] {μ : MeasureTheory.Measure X}
    [MeasureTheory.IsFiniteMeasure μ]
    {K U W : Set X} (hK : IsCompact K) (hU : IsOpen U)
    (hW : IsOpen W) (hKUW : K ⊆ U ∪ W) :
    ∃ P K' : Set X, IsOpen P ∧ P ⊆ U ∧ IsCompact K' ∧ K' ⊆ W ∧ K \ P ⊆ K' ∧
      μ (K' ∩ closure P) = 0 := by
  classical
  have hTcl : IsClosed (K \ W) := (hK.diff hW).isClosed
  have hdisj : Disjoint (Uᶜ) (K \ W) := by
    rw [Set.disjoint_left]
    intro x hx hx'
    rcases hKUW hx'.1 with h | h
    · exact hx h
    · exact hx'.2 h
  obtain ⟨f, hf0, hf1, -⟩ := exists_continuous_zero_one_of_isClosed hU.isClosed_compl hTcl hdisj
  obtain ⟨θ, hθ, hθνull⟩ := exists_good_level μ f.continuous.measurable
  refine ⟨f ⁻¹' Set.Ioi θ, K ∩ f ⁻¹' Set.Iic θ, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact isOpen_Ioi.preimage f.continuous
  · intro x hx
    by_contra hxU
    have hx' : θ < f x := by simpa using hx
    have h0 : f x = 0 := hf0 hxU
    linarith [hθ.1]
  · exact hK.inter_right (isClosed_Iic.preimage f.continuous)
  · intro x hx
    have hxle : f x ≤ θ := by simpa using hx.2
    by_contra hxW
    have h2 : f x = 1 := hf1 ⟨hx.1, hxW⟩
    linarith [hθ.2]
  · intro x hx
    refine ⟨hx.1, ?_⟩
    have h : ¬ (θ < f x) := by simpa using hx.2
    simpa using not_lt.mp h
  · refine MeasureTheory.measure_mono_null ?_ hθνull
    have hclo : closure (f ⁻¹' Set.Ioi θ) ⊆ f ⁻¹' Set.Ici θ :=
      closure_minimal (Set.preimage_mono Set.Ioi_subset_Ici_self)
        (isClosed_Ici.preimage f.continuous)
    rintro x ⟨⟨-, hxle⟩, hxcl⟩
    have hxle' : f x ≤ θ := by simpa using hxle
    have hxge : θ ≤ f x := by simpa using hclo hxcl
    simpa using le_antisymm hxle' hxge

theorem exists_disjoint_open_shrink {X : Type*} [TopologicalSpace X] [T2Space X] [NormalSpace X]
    [ParacompactSpace X] [MeasurableSpace X] [BorelSpace X] (μ : MeasureTheory.Measure X)
    [MeasureTheory.IsFiniteMeasure μ]
    {M : ℕ} (U : Fin M → Set X) (hU : ∀ i, IsOpen (U i))
    {K : Set X} (hK : IsCompact K) (hKU : K ⊆ ⋃ i, U i) :
    ∃ P : Fin M → Set X, (∀ i, IsOpen (P i)) ∧ (∀ i, P i ⊆ U i) ∧
      (∀ i j, i ≠ j → Disjoint (P i) (P j)) ∧ μ (K \ ⋃ i, P i) = 0 := by
  classical
  have aux : ∀ (m : ℕ) (U : Fin m → Set X), (∀ i, IsOpen (U i)) →
      ∀ K : Set X, IsCompact K → K ⊆ ⋃ i, U i →
      ∃ P : Fin m → Set X, (∀ i, IsOpen (P i)) ∧ (∀ i, P i ⊆ U i) ∧
        (∀ i j, i ≠ j → Disjoint (P i) (P j)) ∧ μ (K \ ⋃ i, P i) = 0 := by
    intro m
    induction m with
    | zero =>
      intro U hU K hK hKU
      have hK0 : K = ∅ := by
        have h0 : (⋃ i : Fin 0, U i) = ∅ := by simp
        rw [h0] at hKU
        exact Set.eq_empty_iff_forall_notMem.mpr fun x hx => hKU hx
      refine ⟨Fin.elim0, ?_, ?_, ?_, ?_⟩
      · intro i; exact i.elim0
      · intro i; exact i.elim0
      · intro i; exact i.elim0
      · rw [hK0]; simp
    | succ m ih =>
      intro U hU K hK hKU
      have hV : ∀ i : Fin m, IsOpen (U i.castSucc) := fun i => hU i.castSucc
      have hW : IsOpen (⋃ i : Fin m, U i.castSucc) := isOpen_iUnion hV
      have hKUW : K ⊆ U (Fin.last m) ∪ ⋃ i : Fin m, U i.castSucc := by
        intro x hx
        obtain ⟨i, hi⟩ := Set.mem_iUnion.mp (hKU hx)
        rcases Fin.eq_castSucc_or_eq_last i with ⟨k, hk⟩ | hlast
        · rw [hk] at hi
          exact Or.inr (Set.mem_iUnion.mpr ⟨k, hi⟩)
        · exact Or.inl (hlast ▸ hi)
      obtain ⟨P, K', hPopen, hPU, hK'c, hK'W, hKPK', hnull⟩ :=
        exists_open_peel (μ := μ) hK (hU (Fin.last m)) hW hKUW
      obtain ⟨Q, hQopen, hQV, hQdisj, hQnull⟩ :=
        ih (fun i : Fin m => U i.castSucc) hV K' hK'c hK'W
      let Pfin : Fin (m + 1) → Set X := Fin.lastCases P (fun j => Q j ∩ (closure P)ᶜ)
      have hPfin_last : Pfin (Fin.last m) = P := Fin.lastCases_last
      have hPfin_cast : ∀ j : Fin m, Pfin j.castSucc = Q j ∩ (closure P)ᶜ :=
        fun j => Fin.lastCases_castSucc j
      refine ⟨Pfin, ?_, ?_, ?_, ?_⟩
      · intro i
        rcases Fin.eq_castSucc_or_eq_last i with ⟨a, hia⟩ | hia
        · rw [hia, hPfin_cast]; exact (hQopen a).inter isClosed_closure.isOpen_compl
        · rw [hia, hPfin_last]; exact hPopen
      · intro i
        rcases Fin.eq_castSucc_or_eq_last i with ⟨a, hia⟩ | hia
        · rw [hia, hPfin_cast]; exact Set.inter_subset_left.trans (hQV a)
        · rw [hia, hPfin_last]; exact hPU
      · intro i j hij
        rcases Fin.eq_castSucc_or_eq_last i with ⟨a, hia⟩ | hia
        · rcases Fin.eq_castSucc_or_eq_last j with ⟨b, hjb⟩ | hjb
          · rw [hia, hjb, hPfin_cast, hPfin_cast]
            exact (hQdisj a b (fun hab => hij (by rw [hia, hjb, hab]))).mono
              Set.inter_subset_left Set.inter_subset_left
          · rw [hia, hjb, hPfin_cast, hPfin_last]
            rw [Set.disjoint_left]
            intro x hx hxP
            exact hx.2 (subset_closure hxP)
        · rcases Fin.eq_castSucc_or_eq_last j with ⟨b, hjb⟩ | hjb
          · rw [hia, hjb, hPfin_last, hPfin_cast]
            rw [Set.disjoint_left]
            intro x hx hxQ
            exact hxQ.2 (subset_closure hx)
          · exact absurd (by rw [hia, hjb]) hij
      · have hsub : K \ ⋃ i, Pfin i ⊆ (K' \ ⋃ i, Q i) ∪ (K' ∩ closure P) := by
          intro x hx
          obtain ⟨hxK, hxnot⟩ := hx
          have hxnotP : x ∉ P := by
            intro hxP
            exact hxnot (Set.mem_iUnion.mpr ⟨Fin.last m, by rw [hPfin_last]; exact hxP⟩)
          have hxK' : x ∈ K' := hKPK' ⟨hxK, hxnotP⟩
          by_cases hxQ : x ∈ ⋃ i : Fin m, Q i
          · obtain ⟨a, ha⟩ := Set.mem_iUnion.mp hxQ
            have hxcl : x ∈ closure P := by
              by_contra hxcl
              exact hxnot (Set.mem_iUnion.mpr ⟨a.castSucc,
                by rw [hPfin_cast]; exact ⟨ha, hxcl⟩⟩)
            exact Or.inr ⟨hxK', hxcl⟩
          · exact Or.inl ⟨hxK', hxQ⟩
        have hle : μ (K \ ⋃ i, Pfin i) ≤ μ ((K' \ ⋃ i, Q i) ∪ (K' ∩ closure P)) :=
          measure_mono hsub
        rw [measure_union_null hQnull hnull] at hle
        exact le_antisymm hle bot_le
  exact aux M U hU K hK hKU

end Work.Topology
