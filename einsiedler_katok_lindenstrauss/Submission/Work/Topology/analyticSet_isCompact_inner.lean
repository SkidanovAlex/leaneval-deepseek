import Mathlib
import Submission.Work.Topology.analyticSet_eq_iInter_iUnion_proj

namespace Work.Topology

open MeasureTheory Set
open scoped ENNReal

set_option linter.unusedSectionVars false

section Sion

variable {X Ω : Type*} [TopologicalSpace X] [T2Space X]
  [TopologicalSpace Ω] [CompactSpace Ω] [T2Space Ω]

/-- The union of the first `k+1` members of the `r`-th row of a doubly-indexed family of sets. -/
def finUn (E : ℕ → ℕ → Set (X × Ω)) (r k : ℕ) : Set (X × Ω) :=
  ⋃ k' ∈ Finset.Icc 0 k, E r k'

lemma isClosed_finUn {E : ℕ → ℕ → Set (X × Ω)} (hE : ∀ n k, IsClosed (E n k)) (r k : ℕ) :
    IsClosed (finUn E r k) :=
  isClosed_biUnion_finset (fun i _ => hE r i)

lemma mem_finUn {E : ℕ → ℕ → Set (X × Ω)} {r k : ℕ} {p : X × Ω} :
    p ∈ finUn E r k ↔ ∃ k' ≤ k, p ∈ E r k' := by
  simp only [finUn, Set.mem_iUnion, Finset.mem_Icc]
  constructor
  · rintro ⟨k', ⟨-, h2⟩, h3⟩; exact ⟨k', h2, h3⟩
  · rintro ⟨k', h2, h3⟩; exact ⟨k', ⟨Nat.zero_le _, h2⟩, h3⟩

lemma finUn_mono {E : ℕ → ℕ → Set (X × Ω)} (r : ℕ) : Monotone (finUn E r) := by
  intro k k' hkk' p hp
  rw [mem_finUn] at hp ⊢
  obtain ⟨k'', hk'', hpk''⟩ := hp
  exact ⟨k'', hk''.trans hkk', hpk''⟩

lemma mem_fst_image {T : Set (X × Ω)} {x : X} : x ∈ Prod.fst '' T ↔ ∃ y, (x, y) ∈ T := by
  constructor
  · rintro ⟨p, hp, rfl⟩; exact ⟨p.2, hp⟩
  · rintro ⟨y, hy⟩; exact ⟨(x, y), hy, rfl⟩

lemma isClosed_slice {S : Set (X × Ω)} (hS : IsClosed S) (x : X) :
    IsClosed {y : Ω | (x, y) ∈ S} :=
  hS.preimage (continuous_const.prodMk continuous_id)

lemma isCompact_slice {S : Set (X × Ω)} (hS : IsClosed S) (x : X) :
    IsCompact {y : Ω | (x, y) ∈ S} := (isClosed_slice hS x).isCompact

lemma iInter_fst_image_eq {S : ℕ → Set (X × Ω)} (hS : ∀ r, IsClosed (S r))
    (hmono : Antitone S) :
    (⋂ r, Prod.fst '' (S r)) = Prod.fst '' (⋂ r, S r) := by
  apply Subset.antisymm
  · intro x hx
    simp only [Set.mem_iInter, mem_fst_image] at hx ⊢
    have hne : ∀ r, ({y : Ω | (x, y) ∈ S r}).Nonempty := fun r => hx r
    have htd : ∀ r, {y : Ω | (x, y) ∈ S (r+1)} ⊆ {y : Ω | (x, y) ∈ S r} := by
      intro r y hy; exact hmono (Nat.le_succ r) hy
    obtain ⟨y, hy⟩ := IsCompact.nonempty_iInter_of_sequence_nonempty_isCompact_isClosed
      (fun r => {y : Ω | (x, y) ∈ S r}) htd hne (isCompact_slice (hS 0) x)
      (fun r => isClosed_slice (hS r) x)
    exact ⟨y, fun r => (Set.mem_iInter.mp hy) r⟩
  · intro x hx
    simp only [Set.mem_iInter, mem_fst_image] at hx ⊢
    rcases hx with ⟨y, hy⟩
    exact fun r => ⟨y, hy r⟩

noncomputable def nextK [MeasurableSpace X] (μ : Measure X)
    (T : Set (X × Ω)) (E : ℕ → ℕ → Set (X × Ω)) (b ε : ℝ≥0∞)
    (S : Set (X × Ω)) (r : ℕ) : ℕ := by
  classical
  exact if h : ∃ k, b - ε < μ (Prod.fst '' (T ∩ S ∩ finUn E r k)) then Classical.choose h else 0

noncomputable def Sseq [MeasurableSpace X] (μ : Measure X)
    (T : Set (X × Ω)) (E : ℕ → ℕ → Set (X × Ω)) (b ε : ℝ≥0∞) : ℕ → Set (X × Ω) := fun r =>
  Nat.rec Set.univ (fun r ih => ih ∩ finUn E r (nextK μ T E b ε ih r)) r

lemma Sseq_zero [MeasurableSpace X] (μ : Measure X) (T : Set (X × Ω))
    (E : ℕ → ℕ → Set (X × Ω)) (b ε : ℝ≥0∞) : Sseq μ T E b ε 0 = Set.univ := rfl

lemma Sseq_succ [MeasurableSpace X] (μ : Measure X) (T : Set (X × Ω))
    (E : ℕ → ℕ → Set (X × Ω)) (b ε : ℝ≥0∞) (r : ℕ) :
    Sseq μ T E b ε (r+1) =
      Sseq μ T E b ε r ∩ finUn E r (nextK μ T E b ε (Sseq μ T E b ε r) r) := rfl

lemma nextK_eq_choose [MeasurableSpace X] (μ : Measure X) (T : Set (X × Ω))
    (E : ℕ → ℕ → Set (X × Ω)) (b ε : ℝ≥0∞) (S : Set (X × Ω)) (r : ℕ)
    (h : ∃ k, b - ε < μ (Prod.fst '' (T ∩ S ∩ finUn E r k))) :
    nextK μ T E b ε S r = Classical.choose h := by
  unfold nextK
  rw [dif_pos h]

lemma isClosed_Sseq [MeasurableSpace X] {μ : Measure X} {T : Set (X × Ω)}
    {E : ℕ → ℕ → Set (X × Ω)} {b ε : ℝ≥0∞} (hE : ∀ n k, IsClosed (E n k)) :
    ∀ r, IsClosed (Sseq μ T E b ε r) := by
  intro r
  induction r with
  | zero => rw [Sseq_zero]; exact isClosed_univ
  | succ r ih => rw [Sseq_succ]; exact ih.inter (isClosed_finUn hE _ _)

lemma antitone_Sseq [MeasurableSpace X] (μ : Measure X) (T : Set (X × Ω))
    (E : ℕ → ℕ → Set (X × Ω)) (b ε : ℝ≥0∞) : Antitone (Sseq μ T E b ε) := by
  intro r r' hrr'
  induction r' with
  | zero =>
      have h : r = 0 := Nat.le_zero.mp hrr'
      subst h; exact subset_rfl
  | succ r'' ih =>
      rcases Nat.lt_or_ge r (r''+1) with h | h
      · have h1 : Sseq μ T E b ε (r''+1) ⊆ Sseq μ T E b ε r'' := by
          rw [Sseq_succ]; exact Set.inter_subset_left
        exact h1.trans (ih (Nat.lt_succ_iff.mp h))
      · have h2 : r = r''+1 := le_antisymm hrr' h
        subst h2; exact subset_rfl

end Sion

/-- Choquet–Sion capacitability step: the projection of `⋂ n, ⋃ k, E n k` (with `Ω` compact,
`E n k` closed, and `E n k ⊆ K₀ × Ω` with `K₀` compact) admits a compact subset of almost the
same measure. -/
theorem exists_isCompact_subset_proj_iInter_iUnion
    {X Ω : Type*} [TopologicalSpace X] [T2Space X]
    [TopologicalSpace Ω] [CompactSpace Ω] [T2Space Ω]
    [MeasurableSpace X] [BorelSpace X] (μ : Measure X) [IsFiniteMeasure μ]
    {K₀ : Set X} (hK₀ : IsCompact K₀)
    {E : ℕ → ℕ → Set (X × Ω)} (hE : ∀ n k, IsClosed (E n k))
    (hEK : ∀ n k, E n k ⊆ K₀ ×ˢ (Set.univ : Set Ω))
    {ε : ℝ≥0∞} (hε : 0 < ε) :
    ∃ K : Set X, IsCompact K ∧ K ⊆ Prod.fst '' (⋂ n, ⋃ k, E n k) ∧
      μ (Prod.fst '' (⋂ n, ⋃ k, E n k)) ≤ μ K + ε := by
  classical
  set T : Set (X × Ω) := ⋂ n, ⋃ k, E n k with hT
  set b : ℝ≥0∞ := μ (Prod.fst '' T) with hb
  by_cases hb0 : b = 0
  · refine ⟨∅, isCompact_empty, Set.empty_subset _, ?_⟩
    rw [measure_empty, zero_add, hb0]
    exact hε.le
  · have hbne_top : b ≠ ⊤ := by
      rw [hb]
      exact ne_top_of_le_ne_top (measure_ne_top μ Set.univ) (measure_mono (Set.subset_univ _))
    have hbt : b - ε < b := ENNReal.sub_lt_self hbne_top hb0 (ne_of_gt hε)
    have hSseq_closed := isClosed_Sseq (μ := μ) (T := T) (b := b) (ε := ε) hE
    have hSseq_anti := antitone_Sseq μ T E b ε
    have hmain : ∀ r, b - ε < μ (Prod.fst '' (T ∩ Sseq μ T E b ε r)) := by
      intro r
      induction r with
      | zero =>
          rw [Sseq_zero, Set.inter_univ, ← hb]
          exact hbt
      | succ r ih =>
          have hmono : Monotone (fun k => Prod.fst '' (T ∩ Sseq μ T E b ε r ∩ finUn E r k)) := by
            intro k k' hkk'
            apply Set.image_mono
            intro p hp
            exact ⟨hp.1, finUn_mono r hkk' hp.2⟩
          have hunion : (⋃ k, (T ∩ Sseq μ T E b ε r ∩ finUn E r k))
              = T ∩ Sseq μ T E b ε r := by
            apply Subset.antisymm
            · intro p hp
              obtain ⟨k, hk⟩ := Set.mem_iUnion.mp hp
              exact hk.1
            · intro p hp
              have hpT : p ∈ T := hp.1
              have hEr : p ∈ ⋃ k, E r k := by
                rw [hT] at hpT
                exact Set.mem_iInter.mp hpT r
              obtain ⟨k, hk⟩ := Set.mem_iUnion.mp hEr
              refine Set.mem_iUnion.mpr ⟨k, hp, ?_⟩
              exact (mem_finUn).mpr ⟨k, le_rfl, hk⟩
          have hsup : (⨆ k, μ (Prod.fst '' (T ∩ Sseq μ T E b ε r ∩ finUn E r k)))
              = μ (Prod.fst '' (T ∩ Sseq μ T E b ε r)) := by
            rw [← Monotone.measure_iUnion hmono, ← Set.image_iUnion, hunion]
          have hex : ∃ k, b - ε < μ (Prod.fst '' (T ∩ Sseq μ T E b ε r ∩ finUn E r k)) := by
            refine lt_iSup_iff.mp ?_
            rw [hsup]; exact ih
          rw [Sseq_succ, nextK_eq_choose μ T E b ε _ _ hex, ← Set.inter_assoc]
          exact Classical.choose_spec hex
    refine ⟨⋂ r, Prod.fst '' (Sseq μ T E b ε r), ?_, ?_, ?_⟩
    · have hclosed : IsClosed (⋂ r, Prod.fst '' (Sseq μ T E b ε r)) :=
        isClosed_iInter (fun r => isClosedMap_fst_of_compactSpace _ (hSseq_closed r))
      refine hK₀.of_isClosed_subset hclosed ?_
      refine (Set.iInter_subset (fun r => Prod.fst '' (Sseq μ T E b ε r)) 1).trans ?_
      intro x hx
      obtain ⟨y, hy⟩ := mem_fst_image.mp hx
      have hy1 : (x, y) ∈ Sseq μ T E b ε (0+1) := hy
      rw [Sseq_succ, Sseq_zero, Set.univ_inter] at hy1
      rw [mem_finUn] at hy1
      obtain ⟨k, -, hyk⟩ := hy1
      exact (hEK 0 k hyk).1
    · rw [iInter_fst_image_eq hSseq_closed hSseq_anti]
      intro x hx
      rw [mem_fst_image] at hx
      obtain ⟨y, hy⟩ := hx
      refine mem_fst_image.mpr ⟨y, ?_⟩
      rw [hT]
      refine Set.mem_iInter.mpr (fun n => ?_)
      have hSn : (x, y) ∈ Sseq μ T E b ε (n+1) := Set.mem_iInter.mp hy (n+1)
      rw [Sseq_succ] at hSn
      rw [Set.mem_inter_iff, mem_finUn] at hSn
      obtain ⟨k, -, hk⟩ := hSn.2
      exact Set.mem_iUnion.mpr ⟨k, hk⟩
    · have hanti : Antitone (fun r => Prod.fst '' (Sseq μ T E b ε r)) :=
        fun r r' h => Set.image_mono (hSseq_anti h)
      have hnull : ∀ r, NullMeasurableSet (Prod.fst '' (Sseq μ T E b ε r)) μ :=
        fun r => (isClosedMap_fst_of_compactSpace _ (hSseq_closed r)).measurableSet.nullMeasurableSet
      have hfin : ∃ r, μ (Prod.fst '' (Sseq μ T E b ε r)) ≠ ⊤ :=
        ⟨0, ne_top_of_le_ne_top (measure_ne_top μ Set.univ) (measure_mono (Set.subset_univ _))⟩
      have hmeasure : μ (⋂ r, Prod.fst '' (Sseq μ T E b ε r))
          = ⨅ r, μ (Prod.fst '' (Sseq μ T E b ε r)) :=
        Antitone.measure_iInter hanti hnull hfin
      have hle : b - ε ≤ μ (⋂ r, Prod.fst '' (Sseq μ T E b ε r)) := by
        rw [hmeasure]
        refine le_iInf (fun r => ?_)
        exact le_of_lt ((hmain r).trans_le (measure_mono (Set.image_mono Set.inter_subset_right)))
      rw [tsub_le_iff_right] at hle
      exact hle


theorem analyticSet_isCompact_inner {α : Type*} [TopologicalSpace α] [PolishSpace α]
    [T2Space α] [MeasurableSpace α] [BorelSpace α] (ν : MeasureTheory.Measure α)
    [MeasureTheory.IsFiniteMeasure ν] {S B : Set α} (hB : MeasurableSet B) (hSB : S ⊆ B)
    (hS : MeasureTheory.AnalyticSet S)
    (hmin : ∀ B' : Set α, MeasurableSet B' → S ⊆ B' → ν B ≤ ν B')
    {ε : ENNReal} (hε : 0 < ε) :
    ∃ K : Set α, IsCompact K ∧ K ⊆ S ∧ ν B ≤ ν K + ε := by
  classical
  have hSB' : ν S ≤ ν B := measure_mono hSB
  have hBS : ν B ≤ ν S := by
    rw [MeasureTheory.measure_eq_iInf (μ := ν) S]
    exact le_iInf (fun (B' : Set α) =>
      le_iInf (fun (hsub : S ⊆ B') => le_iInf (fun (hmeas : MeasurableSet B') =>
        hmin B' hmeas hsub)))
  have hν : ν B = ν S := le_antisymm hBS hSB'
  have htight : IsTightMeasureSet ({ν} : Set (MeasureTheory.Measure α)) :=
    isTightMeasureSet_singleton
  rw [isTightMeasureSet_iff_exists_isCompact_measure_compl_le] at htight
  have hε2 : 0 < ε / 2 := ENNReal.half_pos hε.ne'
  obtain ⟨K₀, hK₀c, hK₀le⟩ := htight (ε / 2) hε2
  have hK₀m : ν K₀ᶜ ≤ ε / 2 := hK₀le ν (by simp)
  obtain ⟨E, hE, hSE⟩ := analyticSet_eq_iInter_iUnion_proj (α := α) hS
  obtain ⟨K, hKc, hKsub, hKmeas⟩ :=
    exists_isCompact_subset_proj_iInter_iUnion (X := α) (Ω := ℕ → Set.Icc (0 : ℝ) 1) ν hK₀c
      (E := fun n k => E n k ∩ (K₀ ×ˢ (Set.univ : Set (ℕ → Set.Icc (0 : ℝ) 1))))
      (fun n k => (hE n k).inter (hK₀c.isClosed.prod isClosed_univ))
      (fun n k => Set.inter_subset_right) hε2
  have h1 : (⋂ n, ⋃ k, (E n k ∩ (K₀ ×ˢ (Set.univ : Set (ℕ → Set.Icc (0 : ℝ) 1)))))
      = (⋂ n, ⋃ k, E n k) ∩ (K₀ ×ˢ (Set.univ : Set (ℕ → Set.Icc (0 : ℝ) 1))) := by
    ext p
    simp only [Set.mem_iInter, Set.mem_iUnion, Set.mem_inter_iff, Set.mem_prod, Set.mem_univ,
      and_true]
    constructor
    · intro h
      exact ⟨fun n => (h n).imp (fun k hk => hk.1), (h 0).choose_spec.2⟩
    · rintro ⟨h1', h2⟩
      exact fun n => (h1' n).imp (fun k hk => ⟨hk, h2⟩)
  have hproj : Prod.fst '' (⋂ n, ⋃ k,
        (E n k ∩ (K₀ ×ˢ (Set.univ : Set (ℕ → Set.Icc (0 : ℝ) 1))))) = S ∩ K₀ := by
    rw [h1]
    ext x
    rw [mem_fst_image]
    constructor
    · rintro ⟨y, hy1, hy2⟩
      refine ⟨?_, hy2.1⟩
      rw [hSE]
      exact mem_fst_image.mpr ⟨y, hy1⟩
    · rintro ⟨hxS, hxK⟩
      rw [hSE] at hxS
      obtain ⟨y, hy⟩ := mem_fst_image.mp hxS
      exact ⟨y, hy, by simpa using hxK⟩
  refine ⟨K, hKc, ?_, ?_⟩
  · calc K ⊆ Prod.fst '' (⋂ n, ⋃ k,
          (E n k ∩ (K₀ ×ˢ (Set.univ : Set (ℕ → Set.Icc (0 : ℝ) 1))))) := hKsub
      _ = S ∩ K₀ := hproj
      _ ⊆ S := Set.inter_subset_left
  · have hSm : ν S ≤ ν (S ∩ K₀) + ν K₀ᶜ := by
      calc ν S ≤ ν ((S ∩ K₀) ∪ K₀ᶜ) := measure_mono (fun x hx => by
              by_cases hxK : x ∈ K₀
              · exact Or.inl ⟨hx, hxK⟩
              · exact Or.inr hxK)
        _ ≤ ν (S ∩ K₀) + ν K₀ᶜ := measure_union_le _ _
    have hSK : ν (S ∩ K₀) ≤ ν K + ε / 2 := by
      rw [← hproj]; exact hKmeas
    have hmain2 : ν S ≤ ν K + ε := by
      calc ν S ≤ ν (S ∩ K₀) + ν K₀ᶜ := hSm
        _ ≤ (ν K + ε / 2) + ε / 2 := add_le_add hSK hK₀m
        _ = ν K + ε := by rw [add_assoc, ENNReal.add_halves]
    rw [hν]
    exact hmain2

end Work.Topology
