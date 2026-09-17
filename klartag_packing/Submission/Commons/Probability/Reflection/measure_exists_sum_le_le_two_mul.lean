import Mathlib.Order.CompletePartialOrder
import Mathlib.Probability.IdentDistrib
import Mathlib.Probability.Independence.InfinitePi

set_option linter.unusedVariables false
set_option linter.style.haveILetI false

/-!
# The reflection principle for symmetric random walks

For a symmetric probability measure `ν` on `ℝ` (i.e. `ν.map Neg.neg = ν`) we prove the
classical reflection (ballot) inequality for the partial sums of an i.i.d. sequence with law
`ν`:

`P(∃ k ≤ K, S_k ≤ -a) ≤ 2 * P(S_K ≤ -a)`,  for `a ≥ 0`.

The proof is the standard one.  Consider the event `A = {∃ k ≤ K, S_k ≤ -a}` and
`B = {S_K ≤ -a}`.  Reflect the increments *after* the first passage time: this is a measure
preserving involution mapping `A \ B` into `B`, whence `P(A) ≤ P(B) + P(A\B) ≤ 2 P(B)`.  The
computation is carried out on the product space `(ℕ → ℝ, ν^{⊗ℕ})`, and then transferred to an
abstract probability space carrying independent, identically distributed, symmetric real random
variables via `iIndepFun.map_fun_eq_infinitePi_map`.
-/

namespace Commons.Probability.Reflection

open MeasureTheory ProbabilityTheory
open scoped ENNReal

noncomputable section

/-- `psum k x` is the sum of the first `k` coordinates of `x`. -/
def psum (k : ℕ) (x : ℕ → ℝ) : ℝ := ∑ i ∈ Finset.range k, x i

/-- `sflip k x` changes the sign of the coordinates of `x` indexed by `i ≥ k`. -/
def sflip (k : ℕ) (x : ℕ → ℝ) : ℕ → ℝ := fun i => if k ≤ i then -x i else x i

/-- The set on the product space where some partial sum of length `≤ K` is `≤ -a`. -/
def badSet (K : ℕ) (a : ℝ) : Set (ℕ → ℝ) := {x | ∃ k, k ≤ K ∧ psum k x ≤ -a}

/-- The set on the product space where the partial sum of length `K` is `≤ -a`. -/
def goodSet (K : ℕ) (a : ℝ) : Set (ℕ → ℝ) := {x | psum K x ≤ -a}

/-- The event that the first passage below the level `-a` happens exactly at time `k`. -/
def firstHit (K : ℕ) (a : ℝ) (k : ℕ) : Set (ℕ → ℝ) :=
  {x | (∀ j ∈ Finset.range k, psum j x > -a) ∧ psum k x ≤ -a ∧ psum K x > -a}

lemma measurable_psum (k : ℕ) : Measurable (psum k) := by
  change Measurable (fun x : ℕ → ℝ => ∑ i ∈ Finset.range k, x i)
  exact Finset.measurable_sum (Finset.range k) (fun i _ => measurable_pi_apply i)

lemma measurable_sflip (k : ℕ) : Measurable (sflip k) := by
  rw [measurable_pi_iff]
  intro i
  simp only [sflip]
  by_cases h : k ≤ i
  · simp only [h, if_true]
    exact (measurable_pi_apply i).neg
  · simp only [h, if_false]
    exact measurable_pi_apply i

lemma sflip_sflip (k : ℕ) (x : ℕ → ℝ) : sflip k (sflip k x) = x := by
  funext i
  simp only [sflip]
  by_cases h : k ≤ i <;> simp [h]

lemma psum_sflip_of_le {j m : ℕ} (hjm : j ≤ m) (x : ℕ → ℝ) :
    psum j (sflip m x) = psum j x := by
  simp only [psum]
  apply Finset.sum_congr rfl
  intro i hi
  simp only [sflip]
  rw [if_neg]
  exact Nat.not_le.mpr (lt_of_lt_of_le (Finset.mem_range.mp hi) hjm)

lemma psum_sflip_K {m K : ℕ} (hm : m ≤ K) (x : ℕ → ℝ) :
    psum K (sflip m x) = 2 * psum m x - psum K x := by
  have hK : m + (K - m) = K := Nat.add_sub_of_le hm
  have hsplit : ∀ f : ℕ → ℝ,
      psum K f = psum m f + ∑ i ∈ Finset.range (K - m), f (m + i) := by
    intro f
    have hthis : psum K f = psum (m + (K - m)) f := by rw [hK]
    rw [hthis]
    simp only [psum]
    rw [Finset.sum_range_add]
  have hsum : (∑ i ∈ Finset.range (K - m), sflip m x (m + i))
      = - ∑ i ∈ Finset.range (K - m), x (m + i) := by
    rw [← Finset.sum_neg_distrib]
    apply Finset.sum_congr rfl
    intro i _
    simp only [sflip]
    rw [if_pos (Nat.le_add_right m i)]
  rw [hsplit (sflip m x), psum_sflip_of_le (le_refl m) x, hsum, hsplit x]
  ring

/-- Flipping all coordinates `≥ k` preserves the infinite product of the symmetric measure `ν`. -/
lemma map_sflip {ν : Measure ℝ} [IsProbabilityMeasure ν]
    (hν : ν.map (fun x : ℝ => -x) = ν) (k : ℕ) :
    (Measure.infinitePi (fun _ : ℕ => ν)).map (sflip k)
      = Measure.infinitePi (fun _ : ℕ => ν) := by
  have hf : ∀ i : ℕ, Measurable (fun x : ℝ => if k ≤ i then -x else x) := by
    intro i
    by_cases h : k ≤ i
    · simp only [h, if_true]; exact measurable_neg
    · simp only [h, if_false]; exact measurable_id
  have hmain := Measure.infinitePi_map_pi (μ := fun _ : ℕ => ν)
      (f := fun (i : ℕ) (x : ℝ) => if k ≤ i then -x else x) hf
  have hflip : (fun x : ℕ → ℝ => fun i => if k ≤ i then -x i else x i) = sflip k := rfl
  have hR : (fun i : ℕ => ν.map (fun x : ℝ => if k ≤ i then -x else x)) = (fun _ : ℕ => ν) := by
    funext i
    by_cases h : k ≤ i
    · simp only [h, if_true]; exact hν
    · simp only [h, if_false]; exact Measure.map_id
  rw [hflip, hR] at hmain
  exact hmain

lemma measurableSet_badSet (K : ℕ) (a : ℝ) : MeasurableSet (badSet K a) := by
  have heq : badSet K a = ⋃ k : Fin (K + 1), {x : ℕ → ℝ | psum (k : ℕ) x ≤ -a} := by
    ext x
    constructor
    · rintro ⟨k, hk, hkx⟩
      exact Set.mem_iUnion.mpr ⟨⟨k, Nat.lt_succ_of_le hk⟩, hkx⟩
    · intro h
      rw [Set.mem_iUnion] at h
      obtain ⟨k, hkx⟩ := h
      exact ⟨k, Nat.le_of_lt_succ k.2, hkx⟩
  rw [heq]
  exact MeasurableSet.iUnion
    (fun k => measurableSet_le (measurable_psum (k : ℕ)) measurable_const)

lemma measurableSet_goodSet (K : ℕ) (a : ℝ) : MeasurableSet (goodSet K a) :=
  measurableSet_le (measurable_psum K) measurable_const

lemma measurableSet_firstHit (K k : ℕ) (a : ℝ) : MeasurableSet (firstHit K a k) := by
  have h1 : MeasurableSet {x : ℕ → ℝ | ∀ j ∈ Finset.range k, psum j x > -a} := by
    have heq : {x : ℕ → ℝ | ∀ j ∈ Finset.range k, psum j x > -a}
        = ⋂ j ∈ Finset.range k, {x : ℕ → ℝ | -a < psum j x} := by
      ext x; simp [Set.mem_iInter]
    rw [heq]
    exact MeasurableSet.biInter (Finset.countable_toSet _)
      (fun j _ => measurableSet_lt measurable_const (measurable_psum j))
  show MeasurableSet ({x : ℕ → ℝ | ∀ j ∈ Finset.range k, psum j x > -a}
    ∩ ({x : ℕ → ℝ | psum k x ≤ -a} ∩ {x : ℕ → ℝ | psum K x > -a}))
  exact h1.inter ((measurableSet_le (measurable_psum k) measurable_const).inter
    (measurableSet_lt measurable_const (measurable_psum K)))

lemma badSet_diff_goodSet_subset (K : ℕ) (a : ℝ) :
    badSet K a \ goodSet K a ⊆ ⋃ k ∈ Finset.range K, firstHit K a k := by
  intro x hx
  obtain ⟨hxA, hxB⟩ := hx
  rw [badSet] at hxA
  rw [goodSet] at hxB
  obtain ⟨k, hkK, hkx⟩ := hxA
  have hklt : k < K := by
    rcases lt_or_eq_of_le hkK with h | h
    · exact h
    · exfalso; rw [h] at hkx; exact hxB hkx
  set s := (Finset.range K).filter (fun j => psum j x ≤ -a) with hs
  have hsne : s.Nonempty :=
    ⟨k, by rw [hs, Finset.mem_filter]; exact ⟨Finset.mem_range.mpr hklt, hkx⟩⟩
  have hk0mem : s.min' hsne ∈ s := Finset.min'_mem s hsne
  have hk0range : s.min' hsne ∈ Finset.range K := (Finset.mem_filter.mp hk0mem).1
  rw [Set.mem_iUnion₂]
  refine ⟨s.min' hsne, hk0range, ?_⟩
  refine ⟨?_, (Finset.mem_filter.mp hk0mem).2, not_le.mp hxB⟩
  intro j hj
  have hjlt : j < s.min' hsne := Finset.mem_range.mp hj
  have hjk : j < K := lt_trans hjlt (Finset.mem_range.mp hk0range)
  by_contra hcon
  have hle : psum j x ≤ -a := le_of_not_gt hcon
  have hjs : j ∈ s := by rw [hs, Finset.mem_filter]; exact ⟨Finset.mem_range.mpr hjk, hle⟩
  have hmin : s.min' hsne ≤ j := Finset.min'_le s j hjs
  exact absurd hmin (not_le.mpr hjlt)

lemma firstHit_pairwiseDisjoint (K : ℕ) (a : ℝ) :
    (↑(Finset.range K) : Set ℕ).PairwiseDisjoint (firstHit K a) := by
  intro k _ k' _ hne
  change Disjoint (firstHit K a k) (firstHit K a k')
  rw [Set.disjoint_left]
  intro x hx1 hx2
  rcases lt_or_gt_of_ne hne with hlt | hlt
  · have h1 : psum k x > -a := hx2.1 k (Finset.mem_range.mpr hlt)
    exact absurd hx1.2.1 (not_le.mpr h1)
  · have h1 : psum k' x > -a := hx1.1 k' (Finset.mem_range.mpr hlt)
    exact absurd hx2.2.1 (not_le.mpr h1)

/-- The reflected copies of the first-passage pieces are disjoint. -/
lemma sflip_preimage_pairwiseDisjoint (K : ℕ) (a : ℝ) :
    (↑(Finset.range K) : Set ℕ).PairwiseDisjoint
      (fun k => sflip k ⁻¹' firstHit K a k) := by
  intro k _ k' _ hne
  change Disjoint (sflip k ⁻¹' firstHit K a k) (sflip k' ⁻¹' firstHit K a k')
  rw [Set.disjoint_left]
  intro x hx1 hx2
  rcases lt_or_gt_of_ne hne with hlt | hlt
  · have h1 : psum k (sflip k' x) > -a := hx2.1 k (Finset.mem_range.mpr hlt)
    have h1' : psum k x > -a := by
      rw [psum_sflip_of_le (le_of_lt hlt) x] at h1; exact h1
    have h2 := hx1.2.1
    have h2' : psum k x ≤ -a := by
      rwa [psum_sflip_of_le (le_refl k) x] at h2
    exact absurd h2' (not_le.mpr h1')
  · have h1 : psum k' (sflip k x) > -a := hx1.1 k' (Finset.mem_range.mpr hlt)
    have h1' : psum k' x > -a := by
      rw [psum_sflip_of_le (le_of_lt hlt) x] at h1; exact h1
    have h2 := hx2.2.1
    have h2' : psum k' x ≤ -a := by
      rwa [psum_sflip_of_le (le_refl k') x] at h2
    exact absurd h2' (not_le.mpr h1')

/-- The reflected first-passage pieces lie in `goodSet`. -/
lemma sflip_preimage_subset_goodSet (K : ℕ) (a : ℝ) :
    (⋃ k ∈ Finset.range K, sflip k ⁻¹' firstHit K a k) ⊆ goodSet K a := by
  intro x hx
  rw [Set.mem_iUnion₂] at hx
  obtain ⟨k, hk, hxk⟩ := hx
  have hkK : k < K := Finset.mem_range.mp hk
  have hkx : sflip k x ∈ firstHit K a k := hxk
  have hle : psum k (sflip k x) ≤ -a := hkx.2.1
  have hgt : psum K (sflip k x) > -a := hkx.2.2
  show psum K x ≤ -a
  have hkey : psum K x = 2 * psum k (sflip k x) - psum K (sflip k x) := by
    have h := psum_sflip_K (m := k) (K := K) (le_of_lt hkK) (sflip k x)
    rwa [sflip_sflip k x] at h
  rw [hkey]
  linarith

theorem product_reflection {ν : Measure ℝ} [IsProbabilityMeasure ν]
    (hν : ν.map (fun x : ℝ => -x) = ν) (K : ℕ) {a : ℝ} (ha : 0 ≤ a) :
    (Measure.infinitePi (fun _ : ℕ => ν)) (badSet K a)
      ≤ 2 * (Measure.infinitePi (fun _ : ℕ => ν)) (goodSet K a) := by
  classical
  set P : Measure (ℕ → ℝ) := Measure.infinitePi (fun _ : ℕ => ν) with hP
  set A : Set (ℕ → ℝ) := badSet K a with hA
  set B : Set (ℕ → ℝ) := goodSet K a with hB
  have hAmeas : MeasurableSet A := by rw [hA]; exact measurableSet_badSet K a
  have hBmeas : MeasurableSet B := by rw [hB]; exact measurableSet_goodSet K a
  have hsub : A \ B ⊆ ⋃ k ∈ Finset.range K, firstHit K a k := by
    rw [hA, hB]; exact badSet_diff_goodSet_subset K a
  have hFmeas : ∀ k, MeasurableSet (firstHit K a k) := fun k => measurableSet_firstHit K k a
  have hstep1 : P (A \ B) ≤ ∑ k ∈ Finset.range K, P (firstHit K a k) := by
    calc P (A \ B) ≤ P (⋃ k ∈ Finset.range K, firstHit K a k) := measure_mono hsub
      _ = ∑ k ∈ Finset.range K, P (firstHit K a k) :=
          measure_biUnion_finset (firstHit_pairwiseDisjoint K a) (fun k _ => hFmeas k)
  have hPres : ∀ k, P (sflip k ⁻¹' firstHit K a k) = P (firstHit K a k) := by
    intro k
    have hmap : P.map (sflip k) = P := by rw [hP]; exact map_sflip hν k
    rw [← Measure.map_apply (measurable_sflip k) (hFmeas k), hmap]
  have hstep2 : ∑ k ∈ Finset.range K, P (firstHit K a k) ≤ P B := by
    have hsum_eq : ∑ k ∈ Finset.range K, P (firstHit K a k)
        = ∑ k ∈ Finset.range K, P (sflip k ⁻¹' firstHit K a k) := by
      apply Finset.sum_congr rfl
      intro k _
      rw [hPres k]
    rw [hsum_eq]
    have hsub2 : (⋃ k ∈ Finset.range K, sflip k ⁻¹' firstHit K a k) ⊆ B := by
      rw [hB]; exact sflip_preimage_subset_goodSet K a
    calc ∑ k ∈ Finset.range K, P (sflip k ⁻¹' firstHit K a k)
        = P (⋃ k ∈ Finset.range K, sflip k ⁻¹' firstHit K a k) :=
          (measure_biUnion_finset (sflip_preimage_pairwiseDisjoint K a)
            (fun k _ => (hFmeas k).preimage (measurable_sflip k))).symm
      _ ≤ P B := measure_mono hsub2
  have hAB : A = (A ∩ B) ∪ (A \ B) := by
    ext x; simp only [Set.mem_union, Set.mem_inter_iff, Set.mem_sdiff]; tauto
  have hdecomp : P A = P (A ∩ B) + P (A \ B) := by
    conv_lhs => rw [hAB]
    exact measure_union (s₁ := A ∩ B) (s₂ := A \ B) (by
      rw [Set.disjoint_left]
      intro x hx1 hx2
      exact hx2.2 hx1.2) (hAmeas.diff hBmeas)
  have hfinal : P A ≤ 2 * P B := by
    rw [hdecomp]
    calc P (A ∩ B) + P (A \ B) ≤ P B + P B :=
          add_le_add (measure_mono Set.inter_subset_right) (le_trans hstep1 hstep2)
      _ = 2 * P B := (two_mul (P B)).symm
  simpa only [hP, hA, hB] using hfinal

theorem measure_exists_sum_le_le_two_mul {Ω : Type*} [MeasurableSpace Ω] {μ : MeasureTheory.Measure Ω}
    [MeasureTheory.IsProbabilityMeasure μ] (X : ℕ → Ω → ℝ) (hX : ∀ n, Measurable (X n))
    (hindep : ProbabilityTheory.iIndepFun X μ)
    (hid : ∀ n, ProbabilityTheory.IdentDistrib (X n) (X 0) μ μ)
    (hsym : ProbabilityTheory.IdentDistrib (X 0) (fun ω => -X 0 ω) μ μ)
    {a : ℝ} (ha : 0 ≤ a) (K : ℕ) :
    μ {ω | ∃ k, k ≤ K ∧ (∑ i ∈ Finset.range k, X i ω) ≤ -a}
      ≤ 2 * μ {ω | (∑ i ∈ Finset.range K, X i ω) ≤ -a} := by
  classical
  haveI : IsProbabilityMeasure (μ.map (X 0)) :=
    inferInstance
  have hν : (μ.map (X 0)).map (fun x : ℝ => -x) = μ.map (X 0) := by
    rw [Measure.map_map measurable_neg (hX 0)]
    rw [show (fun x : ℝ => -x) ∘ X 0 = (fun ω => -X 0 ω) from rfl]
    exact hsym.map_eq.symm
  have hT : Measurable (fun ω (i : ℕ) => X i ω) := measurable_pi_iff.mpr hX
  have hmap : μ.map (fun ω (i : ℕ) => X i ω)
      = Measure.infinitePi (fun _ : ℕ => μ.map (X 0)) := by
    have h0 := ProbabilityTheory.iIndepFun.map_fun_eq_infinitePi_map hX hindep
    have hlaws : (fun i : ℕ => μ.map (X i)) = (fun _ : ℕ => μ.map (X 0)) := by
      funext i; exact (hid i).map_eq
    rw [hlaws] at h0
    exact h0
  have hAmeas : MeasurableSet (badSet K a) := measurableSet_badSet K a
  have hBmeas : MeasurableSet (goodSet K a) := measurableSet_goodSet K a
  have hbridgeA : {ω | ∃ k, k ≤ K ∧ (∑ i ∈ Finset.range k, X i ω) ≤ -a}
      = (fun ω (i : ℕ) => X i ω) ⁻¹' badSet K a := by
    ext ω; simp [badSet, psum]
  have hbridgeB : {ω | (∑ i ∈ Finset.range K, X i ω) ≤ -a}
      = (fun ω (i : ℕ) => X i ω) ⁻¹' goodSet K a := by
    ext ω; simp [goodSet, psum]
  have hAval : μ {ω | ∃ k, k ≤ K ∧ (∑ i ∈ Finset.range k, X i ω) ≤ -a}
      = (Measure.infinitePi (fun _ : ℕ => μ.map (X 0))) (badSet K a) := by
    rw [hbridgeA, ← Measure.map_apply hT hAmeas, hmap]
  have hBval : μ {ω | (∑ i ∈ Finset.range K, X i ω) ≤ -a}
      = (Measure.infinitePi (fun _ : ℕ => μ.map (X 0))) (goodSet K a) := by
    rw [hbridgeB, ← Measure.map_apply hT hBmeas, hmap]
  rw [hAval, hBval]
  exact product_reflection hν K ha

end

end Commons.Probability.Reflection