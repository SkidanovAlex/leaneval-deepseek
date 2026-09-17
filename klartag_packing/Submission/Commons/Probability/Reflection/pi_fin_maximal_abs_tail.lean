import Mathlib.MeasureTheory.Order.Group.Lattice
import Mathlib.Topology.UniformSpace.Uniformizable
import Submission.Commons.Probability.Subgaussian.iid_maximal_abs_tail

namespace Commons.Probability.Reflection

open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal

/-- Reindexing a sum over the first `k` coordinates of `Fin n` (with `k ≤ n`) as a sum over
`Finset.range k`. -/
lemma sum_filter_univ_fin (f : ℕ → ℝ) {k n : ℕ} (hk : k ≤ n) :
    ∑ i ∈ Finset.univ.filter (fun i : Fin n => (i : ℕ) < k), f i.val
      = ∑ i ∈ Finset.range k, f i := by
  refine Finset.sum_bij
    (fun (b : Fin n) (_ : b ∈ Finset.univ.filter (fun i : Fin n => (i : ℕ) < k)) => (b : ℕ))
    ?_ ?_ ?_ ?_
  · intro b hb
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hb
    exact Finset.mem_range.mpr hb
  · intro b1 _ b2 _ h
    exact Fin.ext h
  · intro a ha
    refine ⟨⟨a, lt_of_lt_of_le (Finset.mem_range.mp ha) hk⟩, ?_, rfl⟩
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    exact Finset.mem_range.mp ha
  · intro b _
    rfl

/-- The law of the first `n` coordinates of an infinite product of `ν` is the `n`-fold product
measure `Measure.pi (fun _ : Fin n => ν)`. -/
lemma infinitePi_map_restrict_fin {ν : Measure ℝ} [IsProbabilityMeasure ν] (n : ℕ) :
    (Measure.infinitePi (fun _ : ℕ => ν)).map (fun ω : ℕ → ℝ => fun j : Fin n => ω j)
      = Measure.pi (fun _ : Fin n => ν) := by
  refine (Measure.pi_eq (μ := fun _ : Fin n => ν) (fun s hs => ?_)).symm
  rw [Measure.map_apply (by fun_prop) (MeasurableSet.univ_pi hs)]
  have hset : (fun ω : ℕ → ℝ => fun j : Fin n => ω ↑j) ⁻¹' (Set.univ.pi s)
      = Set.pi (Finset.range n) (fun i : ℕ => if h : i < n then s ⟨i, h⟩ else Set.univ) := by
    ext ω
    rw [Set.mem_preimage, Set.mem_univ_pi, Set.mem_pi]
    constructor
    · intro hω i hi
      have hin : i < n := Finset.mem_range.mp (Finset.mem_coe.mp hi)
      rw [dif_pos hin]
      exact hω ⟨i, hin⟩
    · intro hω j
      have h := hω j.val (Finset.mem_coe.mpr (Finset.mem_range.mpr j.isLt))
      rw [dif_pos j.isLt] at h
      simpa using h
  rw [hset]
  rw [Measure.infinitePi_pi (μ := fun _ : ℕ => ν) (s := Finset.range n)
        (fun i hi => by
          simp only [dif_pos (Finset.mem_range.mp hi)]
          exact hs ⟨i, Finset.mem_range.mp hi⟩)]
  rw [← Fin.prod_univ_eq_prod_range (fun i => ν (if h : i < n then s ⟨i, h⟩ else Set.univ)) n]
  apply Finset.prod_congr rfl
  intro j _
  simp only [dif_pos j.isLt]

/-- Maximal inequality for the partial sums of an i.i.d. sequence with symmetric sub-Gaussian law,
stated for the `n`-fold product measure on `Fin n → ℝ`: the probability that some prefix sum of
length `≤ n` exceeds `r` in absolute value is at most `4 * exp (-r ^ 2 / (2 * n * c))`. -/
theorem pi_fin_maximal_abs_tail {ν : MeasureTheory.Measure ℝ} [MeasureTheory.IsProbabilityMeasure ν]
    (hsym : ν.map (fun x : ℝ => -x) = ν) {c : NNReal}
    (hG : ProbabilityTheory.HasSubgaussianMGF (fun x : ℝ => x) c ν)
    {r : ℝ} (hr : 0 ≤ r) (n : ℕ) :
    (MeasureTheory.Measure.pi (fun _ : Fin n => ν)).real
        {y : Fin n → ℝ |
          ∃ k ≤ n, r ≤ |∑ i ∈ Finset.univ.filter (fun i : Fin n => (i : ℕ) < k), y i|}
      ≤ 4 * Real.exp (-r ^ 2 / (2 * (n : ℝ) * (c : ℝ))) := by
  classical
  -- the infinite product space, where the i.i.d. maximal inequality applies
  set P : Measure (ℕ → ℝ) := Measure.infinitePi (fun _ : ℕ => ν) with hP
  set Einf : Set (ℕ → ℝ) :=
    {ω | ∃ k, k ≤ n ∧ r ≤ |∑ i ∈ Finset.range k, ω i|} with hEinf
  set Efin : Set (Fin n → ℝ) :=
    {y | ∃ k ≤ n, r ≤ |∑ i ∈ Finset.univ.filter (fun i : Fin n => (i : ℕ) < k), y i|}
    with hEfin
  -- measurability of the finite-dimensional event
  have hEfin_meas : MeasurableSet Efin := by
    have heq : Efin = ⋃ k : Fin (n + 1),
        {y : Fin n → ℝ |
          r ≤ |∑ i ∈ Finset.univ.filter (fun i : Fin n => (i : ℕ) < (k : ℕ)), y i|} := by
      rw [hEfin]; ext y; constructor
      · rintro ⟨k, hk, hk'⟩
        exact Set.mem_iUnion.mpr ⟨⟨k, Nat.lt_succ_of_le hk⟩, hk'⟩
      · intro h
        rw [Set.mem_iUnion] at h
        obtain ⟨k, hk⟩ := h
        exact ⟨k, Nat.le_of_lt_succ k.2, hk⟩
    rw [heq]
    exact MeasurableSet.iUnion (fun k =>
      measurableSet_le measurable_const
        (Measurable.abs (Finset.measurable_sum _ (fun i _ => measurable_pi_apply i))))
  -- the infinite-dimensional event is the preimage of the finite one
  have hEinf_eq : Einf = (fun ω : ℕ → ℝ => fun j : Fin n => ω j) ⁻¹' Efin := by
    rw [hEinf, hEfin]
    ext ω
    simp only [Set.mem_preimage, Set.mem_ofPred_eq]
    constructor
    · rintro ⟨k, hk, hk'⟩
      exact ⟨k, hk, by rwa [sum_filter_univ_fin (fun i => ω i) hk]⟩
    · rintro ⟨k, hk, hk'⟩
      exact ⟨k, hk, by rwa [← sum_filter_univ_fin (fun i => ω i) hk]⟩
  -- apply the i.i.d. maximal inequality on the infinite product space
  have hmain : P.real Einf ≤ 4 * Real.exp (-r ^ 2 / (2 * (n : ℝ) * (c : ℝ))) := by
    rw [hP, hEinf]
    refine Commons.Probability.Subgaussian.iid_maximal_abs_tail
      (μ := Measure.infinitePi (fun _ : ℕ => ν))
      (X := fun i (ω : ℕ → ℝ) => ω i) (fun i => measurable_pi_apply i) ?_ ?_ ?_ ?_ hr n
    · -- independence of the coordinates
      exact iIndepFun_infinitePi (X := fun _ (x : ℝ) => x) (fun _ => measurable_id)
    · -- identical distribution of the coordinates
      intro i
      refine ⟨(measurable_pi_apply i).aemeasurable, (measurable_pi_apply 0).aemeasurable, ?_⟩
      rw [Measure.infinitePi_map_eval, Measure.infinitePi_map_eval]
    · -- symmetry of the law
      refine ⟨(measurable_pi_apply 0).aemeasurable, (measurable_pi_apply 0).neg.aemeasurable, ?_⟩
      have hL : Measure.map (fun ω : ℕ → ℝ => ω 0) (Measure.infinitePi (fun _ : ℕ => ν)) = ν :=
        Measure.infinitePi_map_eval (fun _ : ℕ => ν) 0
      have hR : Measure.map (fun ω : ℕ → ℝ => -ω 0)
          (Measure.infinitePi (fun _ : ℕ => ν)) = ν := by
        have hmm := Measure.map_map (μ := Measure.infinitePi (fun _ : ℕ => ν))
          (g := fun x : ℝ => -x) (f := fun ω : ℕ → ℝ => ω 0) measurable_neg
          (measurable_pi_apply 0)
        rw [show (fun ω : ℕ → ℝ => -ω 0)
              = (fun x : ℝ => -x) ∘ (fun ω : ℕ → ℝ => ω 0) from rfl,
          ← hmm, Measure.infinitePi_map_eval]
        exact hsym
      exact hL.trans hR.symm
    · -- sub-Gaussianity, transported along the identification of laws
      refine hG.congr_identDistrib
        ⟨measurable_id.aemeasurable, (measurable_pi_apply 0).aemeasurable, ?_⟩
      rw [Measure.infinitePi_map_eval]
      exact Measure.map_id
  -- transfer the value of the measure back to the finite product
  have hmeasure : P Einf = (Measure.pi (fun _ : Fin n => ν)) Efin := by
    rw [hEinf_eq, ← Measure.map_apply (by fun_prop) hEfin_meas, hP,
      infinitePi_map_restrict_fin n]
  have hreal : (Measure.pi (fun _ : Fin n => ν)).real Efin = P.real Einf := by
    rw [Measure.real_def, Measure.real_def, hmeasure]
  rw [hreal]
  exact hmain

end Commons.Probability.Reflection