import Mathlib
import Submission.Work.EKLC6Core.towerDefs
import Submission.Work.EKLC6Core.returnTimeDefs
import Submission.Work.EKLC6Core.firstReturn_partition
import Submission.Work.EKLC6Core.neverReturnSet_null

/-!
# Kac's inequality for the first-return sets of `x ↦ aDiag t • x`

For a `aDiag t`-invariant probability measure `μ` on `X₃ = SL₃(ℝ)/SL₃(ℤ)` and a measurable set
`Ω ⊆ X₃`, this file proves

`∑' i, ENNReal.ofReal (i * (μ (firstReturnSet t Ω i)).toReal) ≤ 1`
and the summability of `i ↦ i * (μ (firstReturnSet t Ω i)).toReal` together with the same bound
for its sum.  This is Kac's formula for the return-time tower of `Ω`: the total `μ`-mass of the
tower built over `Ω` is at most `μ X₃ = 1`.

The proof avoids the Rokhlin-tower disjointness argument (which would need the tower levels
`(aDiag t)^j • Q_i` and the inverse of the map) and instead uses the *entrance* sets
`E n = {x | (T^[n]) x ∈ Ω, (T^[j]) x ∉ Ω for j < n}` of `T = aDiag t • ·`, whose disjointness is
immediate.  The two are linked by the recursion (both sides hold for any self-map `T`)

`T ⁻¹' (E n) = E (n+1) ⊔ Q (n+1)`,

which gives `μ (Q (n+1)) = μ (E n) - μ (E (n+1))`, i.e. `a (n+1) = b n - b (n+1)` with
`a i = μ (Q i)`, `b n = μ (E n)`.  Abel summation then yields, for every `N`,

`∑_{i < N} i * a i = ∑_{n < N} (b n - b N) ≤ ∑_{n < N} b n = μ (⋃_{n < N} E n) ≤ 1`,

using the disjointness of the entrance sets and `b N ≥ 0`.
-/

open MeasureTheory Set
open scoped ENNReal

namespace Work.EKLComp

open Work.EKLC6Core
open Work.EKLContract

noncomputable section

/-- The self-map `x ↦ aDiag t • x` whose return-time tower we study. -/
private noncomputable def Tmap (t : Fin 3 → ℝ) : X3 → X3 := fun x => aDiag t • x

private lemma Tmap_continuous (t : Fin 3 → ℝ) : Continuous (Tmap t) := by
  unfold Tmap; fun_prop

private lemma Tmap_measurable (t : Fin 3 → ℝ) : Measurable (Tmap t) :=
  (Tmap_continuous t).measurable

/-! ## 1. The entrance tower of an abstract self-map

`firstHitSet T Ω n` is the set of points that enter `Ω` for the first time at time `n`.  Its
members are certainly disjoint, whence the partial sums of `μ (firstHitSet T Ω ·)` are bounded
by `μ X = 1`. -/

private lemma sum_range_toReal_firstHitSet_le_one {X : Type*} [MeasurableSpace X] {μ : Measure X}
    [IsProbabilityMeasure μ] (T : X → X) (hT : Measurable T) {Ω : Set X}
    (hΩ : MeasurableSet Ω) (N : ℕ) :
    ∑ n ∈ Finset.range N, (μ (firstHitSet T Ω n)).toReal ≤ 1 := by
  classical
  have hfin : ∀ s : Set X, μ s ≠ ⊤ := by
    intro s
    have h1 : μ s ≤ 1 := by simpa using measure_mono (μ := μ) (Set.subset_univ s)
    exact ne_top_of_lt (lt_of_le_of_lt h1 ENNReal.one_lt_top)
  have hmeas : ∀ n, MeasurableSet (firstHitSet T Ω n) := by
    intro n
    rw [firstHitSet]
    exact ((hT.iterate n) hΩ).inter
      (Finset.measurableSet_biInter _ (fun j _ => ((hT.iterate j) hΩ).compl))
  have hdisj : ∀ a ∈ Finset.range N, ∀ b ∈ Finset.range N, a ≠ b →
      Disjoint (firstHitSet T Ω a) (firstHitSet T Ω b) := by
    intro a _ b _ hab
    rw [Set.disjoint_left]
    intro x hx hx'
    rw [mem_firstHitSet] at hx hx'
    rcases lt_or_gt_of_ne hab with h | h
    · exact hx'.2 a h hx.1
    · exact hx.2 b h hx'.1
  have hbU : μ (⋃ n ∈ Finset.range N, firstHitSet T Ω n) =
      ∑ n ∈ Finset.range N, μ (firstHitSet T Ω n) :=
    measure_biUnion_finset (μ := μ) hdisj (fun b _ => hmeas b)
  have hle : ∑ n ∈ Finset.range N, μ (firstHitSet T Ω n) ≤ 1 := by
    rw [← hbU]
    calc μ (⋃ n ∈ Finset.range N, firstHitSet T Ω n) ≤ μ univ :=
          measure_mono (μ := μ) (Set.subset_univ _)
      _ = 1 := measure_univ
  have htoReal : (∑ n ∈ Finset.range N, μ (firstHitSet T Ω n)).toReal =
      ∑ n ∈ Finset.range N, (μ (firstHitSet T Ω n)).toReal :=
    ENNReal.toReal_sum (fun n _ => hfin _)
  rw [← htoReal]
  calc (∑ n ∈ Finset.range N, μ (firstHitSet T Ω n)).toReal
      ≤ (1 : ℝ≥0∞).toReal := ENNReal.toReal_mono (by simp) hle
    _ = 1 := by simp

/-! ## 2. Unwinding the first-return sets -/

private lemma mem_firstReturnSet {t : Fin 3 → ℝ} {Ω : Set X3} {i : ℕ} (hi : 1 ≤ i) {x : X3} :
    x ∈ firstReturnSet t Ω i ↔
      x ∈ Ω ∧ ((fun y : X3 => aDiag t • y)^[i]) x ∈ Ω ∧
        ∀ j : ℕ, 1 ≤ j → j < i → ((fun y : X3 => aDiag t • y)^[j]) x ∉ Ω := by
  rw [firstReturnSet]
  simp only [Set.mem_inter_iff, Set.mem_preimage, Set.mem_iInter, Set.mem_compl_iff,
    Finset.mem_Icc]
  constructor
  · rintro ⟨⟨h1, h2⟩, h3⟩
    exact ⟨h1, h2, fun j hj1 hji => h3 j ⟨hj1, by omega⟩⟩
  · rintro ⟨h1, h2, h3⟩
    exact ⟨⟨h1, h2⟩, fun j ⟨hj1, hji⟩ => h3 j hj1 (by omega)⟩

/-- Reindexing of the "no intermediate return" condition between the entrance description and
the first-return description. -/
private lemma forall_Icc_iff (p : ℕ → Prop) (n : ℕ) :
    (∀ j, 1 ≤ j → j < n + 1 → p j) ↔ (∀ j, j < n → p (j + 1)) := by
  constructor
  · intro h j hj
    exact h (j + 1) (Nat.succ_le_succ (Nat.zero_le j)) (by omega)
  · intro h j hj1 hj
    obtain ⟨k, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : j ≠ 0)
    exact h k (by omega)

/-- **The entrance recursion.**  The preimage under `T` of the `n`-th entrance set is the
`(n+1)`-st entrance set together with the `(n+1)`-st first-return set.  The two are disjoint
(`E (n+1) ⊆ Ωᶜ`, `Q (n+1) ⊆ Ω`). -/
private lemma preimage_firstHitSet_Tmap (t : Fin 3 → ℝ) (Ω : Set X3) (n : ℕ) :
    (fun x : X3 => aDiag t • x) ⁻¹' firstHitSet (fun x : X3 => aDiag t • x) Ω n =
      firstHitSet (fun x : X3 => aDiag t • x) Ω (n + 1) ∪ firstReturnSet t Ω (n + 1) := by
  ext x
  simp only [Set.mem_preimage, Set.mem_union, mem_firstHitSet]
  rw [mem_firstReturnSet (t := t) (Ω := Ω) (i := n + 1) (Nat.succ_le_succ (Nat.zero_le n))]
  have hA : ((fun y : X3 => aDiag t • y)^[n]) ((fun y : X3 => aDiag t • y) x) ∈ Ω ↔
      ((fun y : X3 => aDiag t • y)^[n + 1]) x ∈ Ω := by
    rw [Function.iterate_succ_apply]
  have hfun : ∀ j : ℕ, ((fun y : X3 => aDiag t • y)^[j])
      ((fun y : X3 => aDiag t • y) x) = ((fun y : X3 => aDiag t • y)^[j + 1]) x :=
    fun j => (Function.iterate_succ_apply _ j x).symm
  have hC : (∀ j : ℕ, j < n →
        ((fun y : X3 => aDiag t • y)^[j]) ((fun y : X3 => aDiag t • y) x) ∉ Ω) ↔
      (∀ j : ℕ, 1 ≤ j → j < n + 1 → ((fun y : X3 => aDiag t • y)^[j]) x ∉ Ω) := by
    rw [forall_Icc_iff (fun j => ((fun y : X3 => aDiag t • y)^[j]) x ∉ Ω) n]
    simp only [hfun]
  rw [hA, hC]
  constructor
  · rintro ⟨h1, h2⟩
    by_cases hx : x ∈ Ω
    · exact Or.inr ⟨hx, h1, h2⟩
    · refine Or.inl ⟨h1, fun j hj => ?_⟩
      rcases Nat.eq_zero_or_pos j with rfl | hjpos
      · simpa using hx
      · exact h2 j hjpos hj
  · rintro (⟨h1, h2⟩ | ⟨-, h1, h2⟩)
    · exact ⟨h1, fun j _ hj => h2 j hj⟩
    · exact ⟨h1, h2⟩

/-! ## 3. Two elementary summation lemmas -/

/-- Abel summation: the weighted sum of first differences telescopes into a difference of
partial sums. -/
private lemma sum_range_mul_sub_eq (b : ℕ → ℝ) (N : ℕ) :
    (∑ n ∈ Finset.range N, ((n : ℝ) + 1) * (b n - b (n + 1))) =
      (∑ n ∈ Finset.range N, b n) - (N : ℝ) * b N := by
  induction N with
  | zero => simp
  | succ N ih =>
    rw [Finset.sum_range_succ, Finset.sum_range_succ, ih]
    push_cast
    ring

/-- Bounded partial sums of a nonnegative series give summability, the bound on the sum, and the
same bound for the `ℝ≥0∞`-valued sum of `ofReal`s. -/
private lemma summable_and_tsum_of_partial_le_one {f : ℕ → ℝ} (hnonneg : ∀ n, 0 ≤ f n)
    (h : ∀ N, ∑ i ∈ Finset.range N, f i ≤ 1) :
    (∑' i, ENNReal.ofReal (f i)) ≤ 1 ∧ Summable f ∧ (∑' i, f i) ≤ 1 := by
  have hsumm : Summable f := summable_of_sum_range_le hnonneg h
  have htsum : ∑' i, f i ≤ 1 := Real.tsum_le_of_sum_range_le hnonneg h
  refine ⟨?_, hsumm, htsum⟩
  rw [← ENNReal.ofReal_tsum_of_nonneg hnonneg hsumm, ← ENNReal.ofReal_one]
  exact ENNReal.ofReal_le_ofReal htsum

/-! ## 4. Kac's inequality -/

theorem kac_return_ineq {μ : MeasureTheory.Measure Work.EKLContract.X3}
    [MeasureTheory.IsProbabilityMeasure μ] {t : Fin 3 → ℝ}
    (hmp : MeasureTheory.MeasurePreserving
      (fun x : Work.EKLContract.X3 => Work.EKLContract.aDiag t • x) μ μ)
    {Ω : Set Work.EKLContract.X3} (hΩ : MeasurableSet Ω) :
    (∑' i : ℕ,
        ENNReal.ofReal ((i : ℝ) * (μ (Work.EKLC6Core.firstReturnSet t Ω i)).toReal)) ≤ 1 ∧
      Summable (fun i : ℕ =>
        ((i : ℝ) * (μ (Work.EKLC6Core.firstReturnSet t Ω i)).toReal)) ∧
      (∑' i : ℕ, ((i : ℝ) * (μ (Work.EKLC6Core.firstReturnSet t Ω i)).toReal)) ≤ 1 := by
  classical
  have hT : MeasurePreserving (Tmap t) μ μ := hmp
  have hfin : ∀ s : Set X3, μ s ≠ ⊤ := by
    intro s
    have h1 : μ s ≤ 1 := by simpa using measure_mono (μ := μ) (Set.subset_univ s)
    exact ne_top_of_lt (lt_of_le_of_lt h1 ENNReal.one_lt_top)
  have hQmeas : ∀ i, MeasurableSet (firstReturnSet t Ω i) := (firstReturn_partition hΩ).1
  have hQsub : ∀ i, firstReturnSet t Ω i ⊆ Ω := by
    intro i x hx
    simp only [firstReturnSet, Set.mem_inter_iff] at hx
    exact hx.1.1
  have hEmeas : ∀ n, MeasurableSet (firstHitSet (Tmap t) Ω n) := by
    intro n
    have hc : Measurable (Tmap t) := Tmap_measurable t
    rw [firstHitSet]
    exact ((hc.iterate n) hΩ).inter
      (Finset.measurableSet_biInter _ (fun j _ => ((hc.iterate j) hΩ).compl))
  -- the step relation `a (n+1) = b n - b (n+1)`
  have hstep : ∀ n : ℕ,
      (μ (firstReturnSet t Ω (n + 1))).toReal =
        (μ (firstHitSet (Tmap t) Ω n)).toReal -
          (μ (firstHitSet (Tmap t) Ω (n + 1))).toReal := by
    intro n
    have hrec : (Tmap t) ⁻¹' (firstHitSet (Tmap t) Ω n) =
        firstHitSet (Tmap t) Ω (n + 1) ∪ firstReturnSet t Ω (n + 1) :=
      preimage_firstHitSet_Tmap t Ω n
    have hdisj : Disjoint (firstHitSet (Tmap t) Ω (n + 1)) (firstReturnSet t Ω (n + 1)) := by
      rw [Set.disjoint_left]
      intro x hx hx'
      have hx0 : x ∉ Ω := by
        have h := (mem_firstHitSet.mp hx).2 0 (Nat.succ_pos n)
        simpa using h
      exact hx0 (hQsub (n + 1) hx')
    have hunion := measure_union (μ := μ) hdisj (hQmeas (n + 1))
    have hpre : μ ((Tmap t) ⁻¹' (firstHitSet (Tmap t) Ω n)) =
        μ (firstHitSet (Tmap t) Ω n) :=
      hT.measure_preimage (hEmeas n).nullMeasurableSet
    have hkey : μ (firstHitSet (Tmap t) Ω n) =
        μ (firstHitSet (Tmap t) Ω (n + 1)) + μ (firstReturnSet t Ω (n + 1)) := by
      rw [← hpre, hrec, hunion]
    have h2 := congrArg ENNReal.toReal hkey
    rw [ENNReal.toReal_add (hfin _) (hfin _)] at h2
    rw [h2]
    ring
  -- the entrance sums are bounded by `μ X₃ = 1`
  have hb_le : ∀ N, ∑ n ∈ Finset.range N, (μ (firstHitSet (Tmap t) Ω n)).toReal ≤ 1 :=
    fun N => sum_range_toReal_firstHitSet_le_one (Tmap t) (Tmap_measurable t) hΩ N
  -- partial sums of the return-time series
  have hpartial : ∀ M : ℕ,
      ∑ i ∈ Finset.range M, (i : ℝ) * (μ (firstReturnSet t Ω i)).toReal ≤ 1 := by
    intro M
    rcases M with _ | N
    · simp
    · rw [Finset.sum_range_succ']
      simp only [Nat.cast_zero, zero_mul, add_zero, Nat.cast_add, Nat.cast_one]
      simp_rw [hstep]
      rw [sum_range_mul_sub_eq]
      have hN : 0 ≤ (N : ℝ) * (μ (firstHitSet (Tmap t) Ω N)).toReal := by positivity
      have := hb_le N
      linarith
  exact summable_and_tsum_of_partial_le_one (fun i => by positivity) hpartial

end

end Work.EKLComp
