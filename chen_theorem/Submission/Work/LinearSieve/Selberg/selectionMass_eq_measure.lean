/-
# The law of a finite sum of indicators under multiplicativity

Given a finite family of measurable sets `H i` in a probability space `(Ω, μ)` whose
measures of finite intersections factor as
`μ (⋂ i ∈ U, H i) = ∏ i ∈ U, (1 - q i)` (so that `μ (H i) = 1 - q i`), the events `H i`
behave like independent Bernoulli variables.  The measure of the event
`∑ i, t i * 1_{H i} < θ` is therefore obtained by summing over the atoms
"exactly the indices in `T` are hit":

`∑ T, (∑ i ∈ T, t i < θ) → (∏ i ∈ T, (1 - q i)) * ∏ i ∉ T, q i`.

This is the "selection mass" computation used by Selberg's Λ² upper bound sieve.
-/
import Mathlib

namespace Work.LinearSieve.Selberg

open MeasureTheory

variable {Ω : Type*} [MeasurableSpace Ω]

/-- The finset of those indices `i` for which `ω ∈ H i`. -/
private noncomputable def hitSet {ι : Type*} [Fintype ι] [DecidableEq ι] (H : ι → Set Ω)
    (ω : Ω) : Finset ι := by
  classical
  exact Finset.univ.filter fun i => ω ∈ H i

/-- The atom consisting of those `ω` which lie in exactly the sets `H i` with `i ∈ T`. -/
private def atomSet {ι : Type*} [Fintype ι] [DecidableEq ι] (H : ι → Set Ω) (T : Finset ι) :
    Set Ω :=
  (⋂ i ∈ T, H i) ∩ ⋂ i ∈ (Finset.univ \ T), (H i)ᶜ

/-- The hypothesis `hup` pins down the measure of any finite intersection of the sets
`H i`, without any need to take a `toReal`. -/
private lemma measure_iInter_eq {ι : Type*} [Fintype ι] (μ : Measure Ω)
    [IsProbabilityMeasure μ] (H : ι → Set Ω) (q : ι → ℝ)
    (hup : ∀ U : Finset ι, ENNReal.toReal (μ (⋂ i ∈ U, H i)) = ∏ i ∈ U, (1 - q i))
    (T : Finset ι) :
    μ (⋂ i ∈ T, H i) = ENNReal.ofReal (∏ i ∈ T, (1 - q i)) := by
  rw [← ENNReal.ofReal_toReal (measure_ne_top μ _), hup T]

/-- Each `q i` lies in the unit interval. -/
private lemma q_mem_Icc {ι : Type*} [Fintype ι] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (H : ι → Set Ω) (q : ι → ℝ)
    (hup : ∀ U : Finset ι, ENNReal.toReal (μ (⋂ i ∈ U, H i)) = ∏ i ∈ U, (1 - q i)) (i : ι) :
    0 ≤ q i ∧ q i ≤ 1 := by
  have h' : ENNReal.toReal (μ (H i)) = 1 - q i := by
    simpa using hup {i}
  have h2 : (0 : ℝ) ≤ ENNReal.toReal (μ (H i)) := ENNReal.toReal_nonneg
  have h3 : ENNReal.toReal (μ (H i)) ≤ 1 := by
    refine ENNReal.toReal_mono ENNReal.one_ne_top ?_
    calc μ (H i) ≤ μ Set.univ := measure_mono (Set.subset_univ _)
      _ = 1 := measure_univ
  constructor <;> linarith

omit [MeasurableSpace Ω] in
private lemma atomSet_eq {ι : Type*} [Fintype ι] [DecidableEq ι] (H : ι → Set Ω)
    (T : Finset ι) : atomSet H T = {ω | hitSet H ω = T} := by
  ext ω
  simp only [atomSet, Set.mem_inter_iff, Set.mem_iInter, Set.mem_compl_iff, Set.mem_ofPred_eq]
  constructor
  · intro h
    simp only [hitSet]
    ext i
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    constructor
    · intro hi
      by_contra hni
      exact h.2 i (Finset.mem_sdiff.mpr ⟨Finset.mem_univ i, hni⟩) hi
    · exact h.1 i
  · intro hω
    constructor
    · intro i hi
      have hmem : i ∈ hitSet H ω := by rw [hω]; exact hi
      simpa only [hitSet, Finset.mem_filter, Finset.mem_univ, true_and] using hmem
    · intro i hi hcon
      have hni : i ∉ T := (Finset.mem_sdiff.mp hi).2
      have hmem : i ∈ hitSet H ω := by
        simpa only [hitSet, Finset.mem_filter, Finset.mem_univ, true_and] using hcon
      rw [hω] at hmem
      exact hni hmem

/-- The measure of an atom: the indices in `T` are hit (each contributing a factor
`1 - q i`) and the indices in `S` are missed (each contributing `q i`).  Proved by
induction on `S`, peeling off one index at a time. -/
private lemma atom_measure {ι : Type*} [Fintype ι] [DecidableEq ι] (μ : Measure Ω)
    [IsProbabilityMeasure μ] (H : ι → Set Ω) (hHmeas : ∀ i, MeasurableSet (H i)) (q : ι → ℝ)
    (hup : ∀ U : Finset ι, ENNReal.toReal (μ (⋂ i ∈ U, H i)) = ∏ i ∈ U, (1 - q i))
    (h0 : ∀ i, 0 ≤ q i) (h1 : ∀ i, q i ≤ 1) (T S : Finset ι) (hTS : Disjoint T S) :
    μ ((⋂ i ∈ T, H i) ∩ ⋂ i ∈ S, (H i)ᶜ)
      = ENNReal.ofReal ((∏ i ∈ T, (1 - q i)) * ∏ i ∈ S, q i) := by
  classical
  induction S using Finset.induction_on generalizing T with
  | empty =>
      have hset : (⋂ i ∈ T, H i) ∩ ⋂ i ∈ (∅ : Finset ι), (H i)ᶜ = ⋂ i ∈ T, H i := by simp
      rw [hset, Finset.prod_empty, mul_one]
      exact measure_iInter_eq μ H q hup T
  | insert j S' hj ih =>
      obtain ⟨hjT, hTS'⟩ := Finset.disjoint_insert_right.mp hTS
      have hdisj : Disjoint (insert j T) S' := by
        rw [Finset.disjoint_insert_left]
        exact ⟨hj, hTS'⟩
      -- the two measures we subtract
      have hX : μ ((⋂ i ∈ T, H i) ∩ ⋂ i ∈ S', (H i)ᶜ)
          = ENNReal.ofReal ((∏ i ∈ T, (1 - q i)) * ∏ i ∈ S', q i) := ih T hTS'
      have hXj : μ ((⋂ i ∈ insert j T, H i) ∩ ⋂ i ∈ S', (H i)ᶜ)
          = ENNReal.ofReal ((∏ i ∈ insert j T, (1 - q i)) * ∏ i ∈ S', q i) :=
        ih (insert j T) hdisj
      -- set identifications
      have hset2 : ((⋂ i ∈ T, H i) ∩ ⋂ i ∈ S', (H i)ᶜ) ∩ H j
          = (⋂ i ∈ insert j T, H i) ∩ ⋂ i ∈ S', (H i)ᶜ := by
        rw [show (⋂ i ∈ insert j T, H i) = H j ∩ ⋂ i ∈ T, H i by simp]
        ext ω
        simp only [Set.mem_inter_iff]
        constructor
        · rintro ⟨⟨hx, hy⟩, hj'⟩; exact ⟨⟨hj', hx⟩, hy⟩
        · rintro ⟨⟨hj', hx⟩, hy⟩; exact ⟨⟨hx, hy⟩, hj'⟩
      have hXj' : μ (((⋂ i ∈ T, H i) ∩ ⋂ i ∈ S', (H i)ᶜ) ∩ H j)
          = ENNReal.ofReal ((∏ i ∈ insert j T, (1 - q i)) * ∏ i ∈ S', q i) := by
        rw [hset2]; exact hXj
      have hset : (⋂ i ∈ T, H i) ∩ ⋂ i ∈ insert j S', (H i)ᶜ
          = ((⋂ i ∈ T, H i) ∩ ⋂ i ∈ S', (H i)ᶜ) \ H j := by
        rw [show (⋂ i ∈ insert j S', (H i)ᶜ) = (H j)ᶜ ∩ ⋂ i ∈ S', (H i)ᶜ by simp,
          Set.sdiff_eq]
        ext ω
        simp only [Set.mem_inter_iff, Set.mem_compl_iff]
        constructor
        · rintro ⟨hx, hjy, hy⟩; exact ⟨⟨hx, hy⟩, hjy⟩
        · rintro ⟨⟨hx, hy⟩, hjy⟩; exact ⟨hx, hjy, hy⟩
      have hsdiff : ((⋂ i ∈ T, H i) ∩ ⋂ i ∈ S', (H i)ᶜ) \ H j
          = ((⋂ i ∈ T, H i) ∩ ⋂ i ∈ S', (H i)ᶜ)
            \ (((⋂ i ∈ T, H i) ∩ ⋂ i ∈ S', (H i)ᶜ) ∩ H j) := by
        ext ω
        simp only [Set.mem_sdiff, Set.mem_inter_iff]
        constructor
        · rintro ⟨hx, hj'⟩; exact ⟨hx, fun h => hj' h.2⟩
        · rintro ⟨hx, h⟩; exact ⟨hx, fun hc => h ⟨hx, hc⟩⟩
      -- arithmetic on the products
      have ha_nonneg : 0 ≤ (∏ i ∈ T, (1 - q i)) * ∏ i ∈ S', q i :=
        mul_nonneg (Finset.prod_nonneg fun i _ => by linarith [h1 i])
          (Finset.prod_nonneg fun i _ => h0 i)
      have hb_eq : (∏ i ∈ insert j T, (1 - q i)) * ∏ i ∈ S', q i
          = (1 - q j) * ((∏ i ∈ T, (1 - q i)) * ∏ i ∈ S', q i) := by
        rw [Finset.prod_insert hjT]; ring
      have hb_nonneg : 0 ≤ (∏ i ∈ insert j T, (1 - q i)) * ∏ i ∈ S', q i := by
        rw [hb_eq]; exact mul_nonneg (by linarith [h1 j]) ha_nonneg
      have hsub : (∏ i ∈ T, (1 - q i)) * ∏ i ∈ S', q i
            - (∏ i ∈ insert j T, (1 - q i)) * ∏ i ∈ S', q i
          = (∏ i ∈ T, (1 - q i)) * ∏ i ∈ insert j S', q i := by
        rw [hb_eq, Finset.prod_insert hj]; ring
      -- the measurable structure needed for `measure_sdiff`
      have hmeasX : MeasurableSet ((⋂ i ∈ T, H i) ∩ ⋂ i ∈ S', (H i)ᶜ) :=
        MeasurableSet.inter (Finset.measurableSet_biInter T fun i _ => hHmeas i)
          (Finset.measurableSet_biInter _ fun i _ => (hHmeas i).compl)
      calc μ ((⋂ i ∈ T, H i) ∩ ⋂ i ∈ insert j S', (H i)ᶜ)
          = μ (((⋂ i ∈ T, H i) ∩ ⋂ i ∈ S', (H i)ᶜ) \ H j) := by rw [hset]
        _ = μ (((⋂ i ∈ T, H i) ∩ ⋂ i ∈ S', (H i)ᶜ)
              \ (((⋂ i ∈ T, H i) ∩ ⋂ i ∈ S', (H i)ᶜ) ∩ H j)) := by rw [hsdiff]
        _ = μ ((⋂ i ∈ T, H i) ∩ ⋂ i ∈ S', (H i)ᶜ)
              - μ (((⋂ i ∈ T, H i) ∩ ⋂ i ∈ S', (H i)ᶜ) ∩ H j) :=
            measure_sdiff Set.inter_subset_left (hmeasX.inter (hHmeas j)).nullMeasurableSet
              (by rw [hXj']; exact ENNReal.ofReal_ne_top)
        _ = ENNReal.ofReal ((∏ i ∈ T, (1 - q i)) * ∏ i ∈ S', q i)
              - ENNReal.ofReal ((∏ i ∈ insert j T, (1 - q i)) * ∏ i ∈ S', q i) := by
            rw [hX, hXj']
        _ = ENNReal.ofReal ((∏ i ∈ T, (1 - q i)) * ∏ i ∈ S', q i
              - (∏ i ∈ insert j T, (1 - q i)) * ∏ i ∈ S', q i) :=
            (ENNReal.ofReal_sub _ hb_nonneg).symm
        _ = ENNReal.ofReal ((∏ i ∈ T, (1 - q i)) * ∏ i ∈ insert j S', q i) := by rw [hsub]

theorem selectionMass_eq_measure {Ω : Type*} [MeasurableSpace Ω] (μ : MeasureTheory.Measure Ω)
    [MeasureTheory.IsProbabilityMeasure μ] {ι : Type*} [Fintype ι] [DecidableEq ι]
    (H : ι → Set Ω) (hHmeas : ∀ i, MeasurableSet (H i)) (q : ι → ℝ)
    (hup : ∀ U : Finset ι, ENNReal.toReal (μ (⋂ i ∈ U, H i)) = ∏ i ∈ U, (1 - q i))
    (t : ι → ℝ) (θ : ℝ) :
    ENNReal.toReal (μ {ω | (∑ i, t i * (H i).indicator (fun _ => (1:ℝ)) ω) < θ})
      = ∑ T ∈ Finset.univ.powerset.filter (fun T => (∑ i ∈ T, t i) < θ),
          (∏ i ∈ T, (1 - q i)) * ∏ i ∈ Finset.univ \ T, q i := by
  classical
  have hq0 : ∀ i, 0 ≤ q i := fun i => (q_mem_Icc μ H q hup i).1
  have hq1 : ∀ i, q i ≤ 1 := fun i => (q_mem_Icc μ H q hup i).2
  set F : Finset (Finset ι) :=
    Finset.univ.powerset.filter (fun T => (∑ i ∈ T, t i) < θ) with hF
  -- the sum of indicators only sees the hit set
  have hsum : ∀ ω : Ω, (∑ i, t i * (H i).indicator (fun _ => (1:ℝ)) ω)
      = ∑ i ∈ hitSet H ω, t i := by
    intro ω
    simp only [hitSet, Finset.sum_filter]
    refine Finset.sum_congr rfl fun i _ => ?_
    by_cases h : ω ∈ H i <;> simp [h]
  -- the level set is the disjoint union of the atoms
  have hS : {ω | (∑ i, t i * (H i).indicator (fun _ => (1:ℝ)) ω) < θ}
      = ⋃ T ∈ F, atomSet H T := by
    ext ω
    simp only [Set.mem_ofPred_eq, Set.mem_iUnion]
    rw [hsum ω]
    constructor
    · intro h
      refine ⟨hitSet H ω, ?_, ?_⟩
      · rw [hF]
        simp only [Finset.mem_filter, Finset.mem_powerset]
        exact ⟨fun i _ => Finset.mem_univ i, h⟩
      · simp only [atomSet_eq, Set.mem_ofPred_eq]
    · rintro ⟨T, hTF, hωT⟩
      have hωT' : hitSet H ω = T := by simpa only [atomSet_eq, Set.mem_ofPred_eq] using hωT
      rw [hF] at hTF
      simp only [Finset.mem_filter] at hTF
      rw [hωT']
      exact hTF.2
  have hmeas_atom : ∀ T ∈ F, MeasurableSet (atomSet H T) := by
    intro T _
    rw [atomSet]
    exact MeasurableSet.inter (Finset.measurableSet_biInter T fun i _ => hHmeas i)
      (Finset.measurableSet_biInter _ fun i _ => (hHmeas i).compl)
  have hdisj_atom : (F : Set (Finset ι)).PairwiseDisjoint (atomSet H) := by
    rw [Set.pairwiseDisjoint_iff]
    intro T _ T' _ hne
    obtain ⟨ω, hωT, hωT'⟩ := hne
    have h1 : hitSet H ω = T := by simpa only [atomSet_eq, Set.mem_ofPred_eq] using hωT
    have h2 : hitSet H ω = T' := by simpa only [atomSet_eq, Set.mem_ofPred_eq] using hωT'
    rw [← h1, h2]
  have hμ_atom : ∀ T ∈ F, μ (atomSet H T)
      = ENNReal.ofReal ((∏ i ∈ T, (1 - q i)) * ∏ i ∈ (Finset.univ \ T), q i) := by
    intro T _
    have hd : Disjoint T (Finset.univ \ T) := disjoint_comm.mpr Finset.sdiff_disjoint
    rw [atomSet]
    exact atom_measure μ H hHmeas q hup hq0 hq1 T (Finset.univ \ T) hd
  have hμ : μ {ω | (∑ i, t i * (H i).indicator (fun _ => (1:ℝ)) ω) < θ}
      = ∑ T ∈ F, ENNReal.ofReal ((∏ i ∈ T, (1 - q i)) * ∏ i ∈ (Finset.univ \ T), q i) := by
    rw [hS, measure_biUnion_finset hdisj_atom hmeas_atom]
    exact Finset.sum_congr rfl fun T hT => hμ_atom T hT
  rw [hμ, ENNReal.toReal_sum fun T _ => ENNReal.ofReal_ne_top]
  refine Finset.sum_congr rfl fun T _ => ENNReal.toReal_ofReal ?_
  exact mul_nonneg (Finset.prod_nonneg fun i _ => by linarith [hq1 i])
    (Finset.prod_nonneg fun i _ => hq0 i)

end Work.LinearSieve.Selberg
