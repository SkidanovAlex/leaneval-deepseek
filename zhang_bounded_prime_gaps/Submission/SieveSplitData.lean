import Mathlib
import Submission.SieveWeightSplit
import Submission.TensorConvergence

open scoped BigOperators Topology
open Filter Finset MeasureTheory

set_option maxHeartbeats 1000000

/-!
# The §5.3 split from the tensor data: the `J₁`-set and the positivity of `α`

Two ingredients of the §5.3 construction of Polymath8a are isolated here:

* `splitBox` — the index set (90) of the paper in the form adapted to the
  tensor-product data: `J₁(i) = {j | Σ_{l ≠ i} M j l < c}`, where `M j l` is the
  support radius of the component `f j l` and `c = (1-ε)ϑ/2` is the radius of the
  `J`-domain.  `splitBox_hM2` shows that this set satisfies the criterion's
  pairwise support condition `hM2` as soon as every component family has
  `Σ_l M j l ≤ ρ` with `ρ - μ + c < ϑ`, where `μ` is a floor on the individual
  support radii (`μ = 12η` for the data of `exists_criterion_tensorData`).

* `exists_tensorData_pos` — the criterion's `hα` (`0 < tpAlpha c f`) follows from
  the data of `exists_tensorData_JFunc` as soon as the target function satisfies
  `0 < IFuncOrth k F` and the approximation error is smaller than `IFuncOrth k F/2`.

The exact algebraic identity
`β_i - β_i^{J₁} = Σ_{j,j' ∉ J₁} c_jc_{j'} f_{ji}(0)f_{j'i}(0)∏_{l≠i}∫f'f'`
(so that the split only discards the quadratic form of the `J₂`-part) is proven
separately once the sum bookkeeping is set up.
-/

namespace Commons.NumberTheory.MaynardSieve

/-- The `J₁`-set of Polymath8a (90) adapted to the tensor data: the components
whose support in the coordinates `≠ i` fits inside the `J`-domain of radius `c`. -/
noncomputable def splitBox {k J : ℕ} (M : Fin J → Fin k → ℝ) (c : ℝ) (i : Fin k) :
    Finset (Fin J) :=
  Finset.univ.filter (fun j => ∑ l ∈ Finset.univ.erase i, M j l < c)

theorem mem_splitBox {k J : ℕ} {M : Fin J → Fin k → ℝ} {c : ℝ} {i : Fin k} {j : Fin J} :
    j ∈ splitBox M c i ↔ ∑ l ∈ Finset.univ.erase i, M j l < c := by
  classical
  simp [splitBox]

/-- **`hM2` for the box-based split.**  If every component family has total
support radius `≤ ρ` and every individual component support radius is `≥ μ`, then
the set `splitBox M c i₀` satisfies the criterion's pairwise support condition
whenever `ρ - μ + c < ϑ`. -/
theorem splitBox_hM2 {k J : ℕ} {M : Fin J → Fin k → ℝ} {ρ c ϑ μ : ℝ}
    (hMnn : ∀ j i, 0 ≤ M j i) (hMsum : ∀ j, ∑ i, M j i ≤ ρ)
    (hMμ : ∀ j i, μ ≤ M j i) (hle : ρ - μ + c < ϑ) :
    ∀ j j' (i₀ : Fin k), j' ∈ splitBox M c i₀ →
      ∑ i ∈ Finset.univ.erase i₀, (M j i + M j' i) < ϑ := by
  classical
  intro j j' i₀ hj'
  have hj'c : ∑ i ∈ Finset.univ.erase i₀, M j' i < c := mem_splitBox.1 hj'
  have hsplit : (∑ i ∈ Finset.univ.erase i₀, M j i) = (∑ i, M j i) - M j i₀ := by
    have h := Finset.sum_erase_add (Finset.univ : Finset (Fin k)) (fun i => M j i)
      (Finset.mem_univ i₀)
    linarith
  have hleρ : (∑ i ∈ Finset.univ.erase i₀, M j i) ≤ ρ - μ := by
    rw [hsplit]
    have h1 : M j i₀ ≥ μ := hMμ j i₀
    have h2 : (∑ i, M j i) ≤ ρ := hMsum j
    linarith
  have hsum : (∑ i ∈ Finset.univ.erase i₀, (M j i + M j' i)) =
      (∑ i ∈ Finset.univ.erase i₀, M j i) + ∑ i ∈ Finset.univ.erase i₀, M j' i :=
    Finset.sum_add_distrib
  rw [hsum]
  linarith

/-- If `tpAlpha c f` is within `δ` of a positive value `I` and `δ ≤ I/2` then
`0 < tpAlpha c f`: this is the criterion's `hα`. -/
theorem tpAlpha_pos_of_approx {k J : ℕ} {c : Fin J → ℝ} {f : Fin J → Fin k → ℝ → ℝ}
    {I δ : ℝ} (h : |tpAlpha c f - I| < δ) (hI : 0 < I) (hδ : δ ≤ I / 2) :
    0 < tpAlpha c f := by
  have h1 : -δ < tpAlpha c f - I := (abs_lt.1 h).1
  linarith

/-- **The criterion's data with `0 < tpAlpha c f`.**  The data of
`exists_tensorData_JFunc` for a target function with `0 < IFuncOrth k F`, together
with the positivity of `α` (the criterion's `hα`), for a sufficiently accurate
tensor approximation. -/
theorem exists_tensorData_pos {k : ℕ} {F : (Fin k → ℝ) → ℝ} (hFc : Continuous F)
    (hFcs : HasCompactSupport F) {R : ℝ} (hR0 : 0 ≤ R)
    (hR : ∀ t, F t ≠ 0 → (∀ i, 0 ≤ t i) ∧ ∑ i, t i ≤ R)
    (hk : 1 ≤ k) {η δ : ℝ} (hη : 0 < η) (hδ : 0 < δ)
    (h1 : R + 24 * (k : ℝ) * η ≤ 1)
    (hI : 0 < IFuncOrth k F) (hδI : δ ≤ IFuncOrth k F / 2) :
    ∃ (J : ℕ) (c : Fin J → ℝ) (f : Fin J → Fin k → ℝ → ℝ) (M : Fin J → Fin k → ℝ),
      (∀ j i, ContDiff ℝ (↑(⊤ : ℕ∞)) (f j i)) ∧
      (∀ j i, HasCompactSupport (f j i)) ∧
      (∀ j i, 0 ≤ M j i) ∧
      (∀ j i t, M j i < |t| → f j i t = 0) ∧
      (∀ j i, M j i ≤ R + 24 * (k : ℝ) * η) ∧
      (∀ j, ∑ i, M j i ≤ R + 24 * (k : ℝ) * η) ∧
      (∀ j i t, 1 ≤ t → f j i t = 0) ∧
      |tpAlpha c f - IFuncOrth k F| < δ ∧
      (∀ i₀, |tpBeta c f i₀ - JFunc k i₀ R F| < δ) ∧
      0 < tpAlpha c f := by
  obtain ⟨J, c, f, M, h1', h2', h3', h4', h5', h6', h7', h8', h9'⟩ :=
    exists_tensorData_JFunc hFc hFcs hR0 hR hk hη hδ h1
  exact ⟨J, c, f, M, h1', h2', h3', h4', h5', h6', h7', h8', h9',
    tpAlpha_pos_of_approx h8' hI hδI⟩

/-- **The split identity** (Polymath8a §5.3): the difference between the full `β_i`
(Polymath8a (14)) and the restricted `β_i^{(J₁)}` (Polymath8a (91)) is exactly the
quadratic form of the `J₂`-part. -/
theorem tpBeta_sub_tpBetaSplit {k J : ℕ} (S : Finset (Fin J)) (c : Fin J → ℝ)
    (f : Fin J → Fin k → ℝ → ℝ) (i : Fin k) :
    tpBeta c f i - tpBetaSplit S c f i =
      ∑ j ∈ (Finset.univ \ S), ∑ j' ∈ (Finset.univ \ S),
        c j * c j' * (f j i 0) * (f j' i 0) *
          ∏ l ∈ (Finset.univ.erase i),
            (∫ t : ℝ in Set.Ioi 0, deriv (f j l) t * deriv (f j' l) t) := by
  classical
  set X : Fin J → Fin J → ℝ := fun j j' =>
    (f j i 0) * (f j' i 0) *
      ∏ l ∈ (Finset.univ.erase i),
        (∫ t : ℝ in Set.Ioi 0, deriv (f j l) t * deriv (f j' l) t) with hX
  have hsym : ∀ j j', X j j' = X j' j := by
    intro j j'
    simp only [hX]
    rw [mul_comm (f j i 0) (f j' i 0)]
    congr 1
    refine Finset.prod_congr rfl fun l _ => ?_
    exact integral_congr_ae (Eventually.of_forall fun t => mul_comm _ _)
  have hbeta : tpBeta c f i = ∑ j : Fin J, ∑ j' : Fin J, c j * c j' * X j j' := by
    rw [tpBeta]
    refine Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun j' _ => ?_
    rw [hX]; ring
  have hsplit : tpBetaSplit S c f i =
      ∑ j : Fin J, ∑ j' ∈ S,
        (if j ∈ S then c j * c j' else 2 * (c j * c j')) * X j j' := by
    rw [tpBetaSplit]
    refine Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun j' _ => ?_
    rw [hX]; ring
  -- expand the two sums
  have hinner : ∀ j : Fin J, (∑ j' : Fin J, c j * c j' * X j j') =
      (∑ j' ∈ (Finset.univ \ S), c j * c j' * X j j') +
        (∑ j' ∈ S, c j * c j' * X j j') :=
    fun j => (Finset.sum_sdiff (Finset.subset_univ S)).symm
  have houter : ∀ (G : Fin J → ℝ),
      (∑ j : Fin J, G j) = (∑ j ∈ (Finset.univ \ S), G j) + (∑ j ∈ S, G j) :=
    fun G => (Finset.sum_sdiff (Finset.subset_univ S)).symm
  have hexp : (∑ j : Fin J, ∑ j' : Fin J, c j * c j' * X j j') =
      (∑ j ∈ (Finset.univ \ S), ∑ j' ∈ (Finset.univ \ S), c j * c j' * X j j') +
      (∑ j ∈ S, ∑ j' ∈ (Finset.univ \ S), c j * c j' * X j j') +
      (∑ j ∈ (Finset.univ \ S), ∑ j' ∈ S, c j * c j' * X j j') +
      (∑ j ∈ S, ∑ j' ∈ S, c j * c j' * X j j') := by
    rw [Finset.sum_congr rfl (fun j _ => hinner j), Finset.sum_add_distrib,
      houter (fun j => ∑ j' ∈ (Finset.univ \ S), c j * c j' * X j j'),
      houter (fun j => ∑ j' ∈ S, c j * c j' * X j j')]
    ring
  have hexp2 : (∑ j : Fin J, ∑ j' ∈ S,
        (if j ∈ S then c j * c j' else 2 * (c j * c j')) * X j j') =
      2 * (∑ j ∈ (Finset.univ \ S), ∑ j' ∈ S, c j * c j' * X j j') +
      (∑ j ∈ S, ∑ j' ∈ S, c j * c j' * X j j') := by
    rw [houter (fun j => ∑ j' ∈ S,
        (if j ∈ S then c j * c j' else 2 * (c j * c j')) * X j j')]
    have hS : (∑ j ∈ S, ∑ j' ∈ S,
        (if j ∈ S then c j * c j' else 2 * (c j * c j')) * X j j') =
        ∑ j ∈ S, ∑ j' ∈ S, c j * c j' * X j j' := by
      refine Finset.sum_congr rfl fun j hj => ?_
      refine Finset.sum_congr rfl fun j' _ => ?_
      rw [if_pos hj]
    have hT : (∑ j ∈ (Finset.univ \ S), ∑ j' ∈ S,
        (if j ∈ S then c j * c j' else 2 * (c j * c j')) * X j j') =
        2 * (∑ j ∈ (Finset.univ \ S), ∑ j' ∈ S, c j * c j' * X j j') := by
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun j hj => ?_
      have hnot : ¬ (j ∈ S) := (Finset.mem_sdiff.1 hj).2
      have hinner2 : (∑ j' ∈ S,
          (if j ∈ S then c j * c j' else 2 * (c j * c j')) * X j j') =
          2 * (∑ j' ∈ S, c j * c j' * X j j') := by
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl fun j' _ => ?_
        rw [if_neg hnot]; ring
      rw [hinner2]
    rw [hS, hT]
  -- the cross terms cancel by symmetry of `X`
  have hcross : (∑ j ∈ S, ∑ j' ∈ (Finset.univ \ S), c j * c j' * X j j') =
      (∑ j ∈ (Finset.univ \ S), ∑ j' ∈ S, c j * c j' * X j j') := by
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun j' _ => ?_
    rw [hsym j' j]
    ring
  rw [hbeta, hsplit, hexp, hexp2, hcross]
  simp only [hX]
  ring

/-- **`hkey` from a `J₂`-loss bound.**  If (i) the total `Σ_i β_i` beats a threshold `A` by
`margin`, (ii) the `J₂`-loss `Σ_i (β_i - β_i^{J₁})` is below `margin`, and (iii) `α < A`, then
the criterion's key inequality `α < Σ_i β_i^{J₁}` holds.  This isolates the *only* remaining
analytic input of §5.3: a bound on the `J₂`-loss. -/
theorem hkey_of_loss {k J : ℕ} (Sf : Fin k → Finset (Fin J)) (c : Fin J → ℝ)
    (f : Fin J → Fin k → ℝ → ℝ) {A margin : ℝ}
    (hβ : A + margin < ∑ i : Fin k, tpBeta c f i)
    (hloss : ∑ i : Fin k, (tpBeta c f i - tpBetaSplit (Sf i) c f i) < margin)
    (hα : tpAlpha c f < A) :
    tpAlpha c f < ∑ i : Fin k, tpBetaSplit (Sf i) c f i := by
  have hsum : (∑ i : Fin k, tpBetaSplit (Sf i) c f i) =
      (∑ i : Fin k, tpBeta c f i) - ∑ i : Fin k, (tpBeta c f i - tpBetaSplit (Sf i) c f i) := by
    rw [Finset.sum_sub_distrib]
    ring
  rw [hsum]
  linarith

end Commons.NumberTheory.MaynardSieve
