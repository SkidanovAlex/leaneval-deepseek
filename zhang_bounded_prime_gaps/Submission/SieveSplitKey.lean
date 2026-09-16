import Mathlib
import Submission.AntiderivConv
import Submission.SieveWeightSplit
import Submission.SieveSplitData
import Submission.Commons.MeasureTheory.Integral.sum_integral_prod_eq_integral_mul

open scoped BigOperators Topology
open Filter Finset MeasureTheory

set_option maxHeartbeats 2000000

/-!
# §5.3: the integral representation of the split `β`-coefficient

This module transcribes the `J₁/J₂` split of Polymath8a §5.3 into the
antiderivative ("`G`") language of `Submission/AntiderivConv.lean`, where the
support of each component is under control.

For `f j i = anti ψ (G j) i` one has `f j i 0 = ∫_{s>0} G j i s` and
`∫_{s>0} f'_{j,l} f'_{j',l} = ∫_{s>0} G_{j,l} G_{j',l}`, so the coefficient forms of
`tpBeta` and `tpBetaSplit` turn into integrals of products of tensor sums.
-/

namespace Commons.NumberTheory.MaynardSieve

/-- **The cross-form integral representation of the restricted `β`-coefficient.**

`tpBetaSplit S c f i₀` is the integral over the orthant of
`(Σ_j splitA_j · u_j · ∏_{l≠i₀} G_{j,l}) · (Σ_j splitB_j · u_j · ∏_{l≠i₀} G_{j,l})`,
where `u_j = ∫_{s>0} G_{j,i₀}` and `f j i = anti ψ (G j) i`. -/
theorem tpBetaSplit_anti {J k : ℕ} {ψ : ℝ → ℝ}
    (hψ0 : ψ 0 = 1) (hψ1 : ∀ u : ℝ, 0 ≤ u → ψ u = 1)
    (G : Fin J → Fin k → ℝ → ℝ) (hGc : ∀ j i, Continuous (G j i))
    (hGcs : ∀ j i, HasCompactSupport (G j i))
    (hGi : ∀ j i, Integrable (G j i))
    (hGv : ∀ j i, ∃ R : ℝ, ∀ x : ℝ, R ≤ x → G j i x = 0)
    (c : Fin J → ℝ) (S : Finset (Fin J)) (i₀ : Fin k) :
    tpBetaSplit S c (fun j i => anti ψ (G j) i) i₀
      = ∫ t : {l : Fin k // l ≠ i₀} → ℝ,
          ((∑ j : Fin J, splitA S c j * (∫ x in Set.Ioi (0:ℝ), G j i₀ x) *
              ∏ l : {l : Fin k // l ≠ i₀}, G j (l : Fin k) (t l)) *
            (∑ j : Fin J, splitB S c j * (∫ x in Set.Ioi (0:ℝ), G j i₀ x) *
              ∏ l : {l : Fin k // l ≠ i₀}, G j (l : Fin k) (t l))) * orthInd t := by
  classical
  set f : Fin J → Fin k → ℝ → ℝ := fun j i => anti ψ (G j) i with hf
  have hsplit := sum_splitA_mul_splitB S c
    (fun j j' : Fin J => (f j i₀ 0) * (f j' i₀ 0) *
      ∏ l ∈ (Finset.univ.erase i₀),
        (∫ t : ℝ in Set.Ioi 0, deriv (f j l) t * deriv (f j' l) t))
  have hB0 : tpBetaSplit S c f i₀ =
      ∑ j : Fin J, ∑ j' : Fin J,
        splitA S c j * splitB S c j' *
          ((f j i₀ 0) * (f j' i₀ 0) *
            ∏ l ∈ (Finset.univ.erase i₀),
              (∫ t : ℝ in Set.Ioi 0, deriv (f j l) t * deriv (f j' l) t)) := by
    rw [tpBetaSplit]
    trans ∑ j : Fin J, ∑ j' ∈ S,
        (if j ∈ S then c j * c j' else 2 * (c j * c j')) *
          ((f j i₀ 0) * (f j' i₀ 0) *
            ∏ l ∈ (Finset.univ.erase i₀),
              (∫ t : ℝ in Set.Ioi 0, deriv (f j l) t * deriv (f j' l) t))
    · refine Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun j' _ => ?_
      ring
    · exact hsplit.symm
  rw [hB0]
  have h0 : ∀ j : Fin J, f j i₀ 0 = ∫ x in Set.Ioi (0:ℝ), G j i₀ x := by
    intro j
    exact anti_zero_of_eq_one hψ0 (G j) i₀
  have hA : ∀ j j' : Fin J,
      (∏ l : {l : Fin k // l ≠ i₀},
          (∫ t : ℝ in Set.Ioi 0, deriv (f j (l : Fin k)) t * deriv (f j' (l : Fin k)) t))
        = ∏ l : {l : Fin k // l ≠ i₀},
          (∫ t : ℝ in Set.Ioi 0, G j (l : Fin k) t * G j' (l : Fin k) t) := by
    intro j j'
    refine Finset.prod_congr rfl fun l _ => ?_
    show (∫ t in Set.Ioi (0:ℝ), deriv (fun u : ℝ => ψ u * ∫ s in Set.Ioi u, G j l.1 s) t
          * deriv (fun u : ℝ => ψ u * ∫ s in Set.Ioi u, G j' (l : Fin k) s) t)
      = ∫ t in Set.Ioi (0:ℝ), G j (l : Fin k) t * G j' (l : Fin k) t
    exact integral_deriv_anti_mul hψ1 (hGc j (l : Fin k)) (hGi j (l : Fin k)) (hGv j (l : Fin k))
      (hGc j' (l : Fin k)) (hGi j' (l : Fin k)) (hGv j' (l : Fin k))
  have hprod : ∀ j j' : Fin J,
      (∏ l ∈ (Finset.univ.erase i₀),
          (∫ t : ℝ in Set.Ioi 0, deriv (f j l) t * deriv (f j' l) t))
        = ∏ l : {l : Fin k // l ≠ i₀},
          (∫ t : ℝ in Set.Ioi 0, G j (l : Fin k) t * G j' (l : Fin k) t) := by
    intro j j'
    rw [prod_erase_eq_prod_subtype i₀
      (fun l => ∫ t : ℝ in Set.Ioi 0, deriv (f j l) t * deriv (f j' l) t)]
    exact hA j j'
  simp only [h0, hprod]
  have hB : ∀ j j' : Fin J,
      (∏ l : {l : Fin k // l ≠ i₀}, (∫ t : ℝ in Set.Ioi 0, G j (l : Fin k) t * G j' (l : Fin k) t))
        = ∫ t : {l : Fin k // l ≠ i₀} → ℝ,
            ∏ l : {l : Fin k // l ≠ i₀}, (Set.Ici (0:ℝ)).indicator (fun s => G j (l : Fin k) s * G j' (l : Fin k) s) (t l) := by
    intro j j'
    have h1 : (∏ l : {l : Fin k // l ≠ i₀},
          (∫ t : ℝ in Set.Ioi 0, G j (l : Fin k) t * G j' (l : Fin k) t))
        = ∏ l : {l : Fin k // l ≠ i₀}, ∫ t : ℝ,
            (Set.Ici (0:ℝ)).indicator (fun s => G j (l : Fin k) s * G j' (l : Fin k) s) t := by
      refine Finset.prod_congr rfl fun l _ => ?_
      rw [MeasureTheory.integral_indicator measurableSet_Ici]
      exact MeasureTheory.setIntegral_congr_set MeasureTheory.Ioi_ae_eq_Ici
    rw [h1, ← MeasureTheory.integral_fintype_prod_volume_eq_prod
      (f := fun (l : {l : Fin k // l ≠ i₀}) (s : ℝ) =>
        (Set.Ici (0:ℝ)).indicator (fun s => G j (l : Fin k) s * G j' (l : Fin k) s) s)]
  simp only [hB]
  have hgen := Commons.MeasureTheory.Integral.sum_integral_prod_eq_integral_mul
    (ι := {l : Fin k // l ≠ i₀}) (J := J)
    (fun j l => G j (l : Fin k)) (fun j l => G j (l : Fin k))
    (fun j l => hGc j (l : Fin k)) (fun j l => hGcs j (l : Fin k))
    (fun j l => hGc j (l : Fin k)) (fun j l => hGcs j (l : Fin k))
    (fun j => ∫ x in Set.Ioi (0:ℝ), G j i₀ x)
    (fun j => ∫ x in Set.Ioi (0:ℝ), G j i₀ x)
    (splitA S c) (splitB S c)
  refine hgen.trans ?_
  refine MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall fun t => ?_)
  simp only [orthInd]

/-! ## Partial tensor marginal sums

For a set `S` of component indices,
`tenP G c i S t = Σ_{j ∈ S} c_j (∫G_{j,i}) ∏_{l≠i} G_{j,l}(t_l)`
is the `S`-partial sum of the marginal tensor sum.  The `J₁`-part is `tenP G c i S`
and the `J₂`-part is `tenP G c i (univ \ S)`; the `splitA`/`splitB` marginal sums of
`tpBetaSplit_anti` are `2 P - P_S` and `P_S`, where `P = tenP G c i univ`. -/

/-- The `S`-partial sum of the marginal tensor sum. -/
noncomputable def tenP {J k : ℕ} (G : Fin J → Fin k → ℝ → ℝ) (c : Fin J → ℝ) (i : Fin k)
    (S : Finset (Fin J)) (t : {l : Fin k // l ≠ i} → ℝ) : ℝ :=
  ∑ j ∈ S, c j * (∫ x in Set.Ioi (0:ℝ), G j i x) *
    ∏ l : {l : Fin k // l ≠ i}, G j (l : Fin k) (t l)

/-- The `splitA` marginal sum of `tpBetaSplit_anti`. -/
noncomputable def tenPA {J k : ℕ} (G : Fin J → Fin k → ℝ → ℝ) (c : Fin J → ℝ) (i : Fin k)
    (S : Finset (Fin J)) (t : {l : Fin k // l ≠ i} → ℝ) : ℝ :=
  ∑ j : Fin J, splitA S c j * (∫ x in Set.Ioi (0:ℝ), G j i x) *
    ∏ l : {l : Fin k // l ≠ i}, G j (l : Fin k) (t l)

/-- The `splitB` marginal sum of `tpBetaSplit_anti`. -/
noncomputable def tenPB {J k : ℕ} (G : Fin J → Fin k → ℝ → ℝ) (c : Fin J → ℝ) (i : Fin k)
    (S : Finset (Fin J)) (t : {l : Fin k // l ≠ i} → ℝ) : ℝ :=
  ∑ j : Fin J, splitB S c j * (∫ x in Set.Ioi (0:ℝ), G j i x) *
    ∏ l : {l : Fin k // l ≠ i}, G j (l : Fin k) (t l)

/-! ## Algebraic identities for the partial marginal sums -/

/-- Splitting a sum over `univ` at a finite subset (in the order `S` first). -/
lemma sum_univ_sdiff {ι M : Type*} [Fintype ι] [DecidableEq ι] [AddCommMonoid M]
    (S : Finset ι) (f : ι → M) :
    (∑ j ∈ (Finset.univ : Finset ι), f j)
      = (∑ j ∈ S, f j) + ∑ j ∈ (Finset.univ \ S), f j := by
  rw [← Finset.sum_sdiff (Finset.subset_univ S)]
  exact add_comm _ _

/-- The partial marginal sum over `univ` splits into the parts `S` and `univ \ S`. -/
theorem tenP_sdiff {J k : ℕ} (G : Fin J → Fin k → ℝ → ℝ) (c : Fin J → ℝ) (i : Fin k)
    (S : Finset (Fin J)) (t : {l : Fin k // l ≠ i} → ℝ) :
    tenP G c i Finset.univ t = tenP G c i S t + tenP G c i (Finset.univ \ S) t := by
  show (∑ j ∈ (Finset.univ : Finset (Fin J)), c j * (∫ x in Set.Ioi (0:ℝ), G j i x) *
      ∏ l : {l : Fin k // l ≠ i}, G j (l : Fin k) (t l))
    = tenP G c i S t + tenP G c i (Finset.univ \ S) t
  simp only [tenP]
  exact sum_univ_sdiff S _

/-- **The `splitA` marginal sum is `2P - P_S`.** -/
theorem tenPA_eq {J k : ℕ} (G : Fin J → Fin k → ℝ → ℝ) (c : Fin J → ℝ) (i : Fin k)
    (S : Finset (Fin J)) (t : {l : Fin k // l ≠ i} → ℝ) :
    tenPA G c i S t = 2 * tenP G c i Finset.univ t - tenP G c i S t := by
  classical
  set X : Fin J → ℝ := fun j =>
    (∫ x in Set.Ioi (0:ℝ), G j i x) *
      ∏ l : {l : Fin k // l ≠ i}, G j (l : Fin k) (t l) with hX
  have hA : tenPA G c i S t = ∑ j : Fin J, splitA S c j * X j := by
    rw [tenPA]
    refine Finset.sum_congr rfl fun j _ => ?_
    simp only [hX]; ring
  have hP : tenP G c i S t = ∑ j ∈ S, c j * X j := by
    rw [tenP]
    refine Finset.sum_congr rfl fun j _ => ?_
    simp only [hX]; ring
  have hU : tenP G c i Finset.univ t
      = ∑ j ∈ (Finset.univ : Finset (Fin J)), c j * X j := by
    rw [tenP]
    refine Finset.sum_congr rfl fun j _ => ?_
    simp only [hX]; ring
  rw [hA, hP, hU,
    sum_univ_sdiff S (f := fun j => splitA S c j * X j)]
  have h1 : (∑ j ∈ S, splitA S c j * X j) = ∑ j ∈ S, c j * X j := by
    refine Finset.sum_congr rfl fun j hj => ?_
    rw [splitA, if_pos hj]
  have h2 : (∑ j ∈ (Finset.univ \ S), splitA S c j * X j)
      = 2 * ∑ j ∈ (Finset.univ \ S), c j * X j := by
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun j hj => ?_
    have hjn : j ∉ S := (Finset.mem_sdiff.mp hj).2
    rw [splitA, if_neg hjn]; ring
  rw [h1, h2, sum_univ_sdiff S (f := fun j => c j * X j)]
  ring

/-- **The `splitB` marginal sum is `P_S`.** -/
theorem tenPB_eq {J k : ℕ} (G : Fin J → Fin k → ℝ → ℝ) (c : Fin J → ℝ) (i : Fin k)
    (S : Finset (Fin J)) (t : {l : Fin k // l ≠ i} → ℝ) :
    tenPB G c i S t = tenP G c i S t := by
  classical
  rw [tenPB, tenP]
  rw [show (∑ j : Fin J, splitB S c j * (∫ x in Set.Ioi (0:ℝ), G j i x) *
        ∏ l : {l : Fin k // l ≠ i}, G j (l : Fin k) (t l))
      = ∑ j ∈ S, splitB S c j * (∫ x in Set.Ioi (0:ℝ), G j i x) *
        ∏ l : {l : Fin k // l ≠ i}, G j (l : Fin k) (t l) from
    (Finset.sum_subset (Finset.subset_univ S) (fun j _ hj => by
      rw [splitB, if_neg hj]; ring)).symm]
  refine Finset.sum_congr rfl fun j hj => ?_
  rw [splitB, if_pos hj]

/-! ## Integrability of the orthant-restricted tensor sums -/

/-- Integrability of `orthInd · (∑_{j∈S} c_j ∏ H_{j,i}) · (∑_{j'∈T} d_{j'} ∏ H_{j',i})`. -/
lemma integrable_orthInd_finset_prod_mul {ι : Type*} [Fintype ι] {J : ℕ}
    (H : Fin J → ι → ℝ → ℝ) (hHc : ∀ j i, Continuous (H j i))
    (hHcs : ∀ j i, HasCompactSupport (H j i)) (c d : Fin J → ℝ)
    (S T : Finset (Fin J)) :
    Integrable (fun t : ι → ℝ => orthInd t *
      ((∑ j ∈ S, c j * ∏ i, H j i (t i)) * (∑ j' ∈ T, d j' * ∏ i, H j' i (t i)))) := by
  have hpt : ∀ t : ι → ℝ, orthInd t *
      ((∑ j ∈ S, c j * ∏ i, H j i (t i)) * (∑ j' ∈ T, d j' * ∏ i, H j' i (t i)))
      = ∑ j ∈ S, ∑ j' ∈ T, (c j * d j') *
          ∏ i, (Set.Ici (0:ℝ)).indicator (fun s => H j i s * H j' i s) (t i) := by
    intro t
    rw [Finset.sum_mul_sum, Finset.mul_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun j' _ => ?_
    have h2 : (∏ i, H j i (t i)) * (∏ i, H j' i (t i)) * orthInd t
        = ∏ i, (Set.Ici (0:ℝ)).indicator (fun s => H j i s * H j' i s) (t i) := by
      rw [← orthInd_mul_prod (fun i s => H j i s * H j' i s) t, mul_comm]
      congr 1
      rw [Finset.prod_mul_distrib]
    calc orthInd t * ((c j * ∏ i, H j i (t i)) * (d j' * ∏ i, H j' i (t i)))
        = (c j * d j') *
            ((∏ i, H j i (t i)) * (∏ i, H j' i (t i)) * orthInd t) := by ring
      _ = (c j * d j') *
            ∏ i, (Set.Ici (0:ℝ)).indicator (fun s => H j i s * H j' i s) (t i) := by rw [h2]
  rw [funext hpt]
  refine integrable_finsetSum _ fun j _ => ?_
  refine integrable_finsetSum _ fun j' _ => ?_
  exact (integrable_prod_indicator_Ici (fun i => H j i * H j' i)
    (fun i => (hHc j i).mul (hHc j' i))
    (fun i => hasCompactSupport_mul (hHcs j i) (hHcs j' i))).const_mul _

/-- Integrability of the square of a partial tensor marginal sum against the orthant. -/
theorem integrable_tenP_sq {J k : ℕ} (G : Fin J → Fin k → ℝ → ℝ)
    (hGc : ∀ j i, Continuous (G j i)) (hGcs : ∀ j i, HasCompactSupport (G j i))
    (c : Fin J → ℝ) (i : Fin k) (S : Finset (Fin J)) :
    Integrable (fun t : {l : Fin k // l ≠ i} → ℝ => (tenP G c i S t) ^ 2 * orthInd t) := by
  have hmain := integrable_orthInd_finset_prod_mul
    (fun j (l : {l : Fin k // l ≠ i}) s => G j (l : Fin k) s)
    (fun j l => hGc j (l : Fin k)) (fun j l => hGcs j (l : Fin k))
    (fun j => c j * (∫ x in Set.Ioi (0:ℝ), G j i x))
    (fun j => c j * (∫ x in Set.Ioi (0:ℝ), G j i x)) S S
  refine hmain.congr (Filter.Eventually.of_forall fun t => ?_)
  simp only [tenP]
  ring

/-- Integrability of `tenPA · tenPB` against the orthant. -/
theorem integrable_tenPA_mul_tenPB {J k : ℕ} (G : Fin J → Fin k → ℝ → ℝ)
    (hGc : ∀ j i, Continuous (G j i)) (hGcs : ∀ j i, HasCompactSupport (G j i))
    (c : Fin J → ℝ) (i : Fin k) (S : Finset (Fin J)) :
    Integrable (fun t : {l : Fin k // l ≠ i} → ℝ =>
      (tenPA G c i S t * tenPB G c i S t) * orthInd t) := by
  have hmain := integrable_orthInd_finset_prod_mul
    (fun j (l : {l : Fin k // l ≠ i}) s => G j (l : Fin k) s)
    (fun j l => hGc j (l : Fin k)) (fun j l => hGcs j (l : Fin k))
    (fun j => splitA S c j * (∫ x in Set.Ioi (0:ℝ), G j i x))
    (fun j => splitB S c j * (∫ x in Set.Ioi (0:ℝ), G j i x)) Finset.univ Finset.univ
  refine hmain.congr (Filter.Eventually.of_forall fun t => ?_)
  simp only [tenPA, tenPB]
  ring

/-- **The marginal tensor sum as the inner integral** (Polymath8a (79)). -/
lemma integral_tensorSum_extendAt {J k : ℕ} (G : Fin J → Fin k → ℝ → ℝ)
    (hGi : ∀ j i, Integrable (G j i)) (c : Fin J → ℝ) (i₀ : Fin k)
    (t : {l : Fin k // l ≠ i₀} → ℝ) :
    (∫ x in Set.Ioi (0:ℝ), ∑ j : Fin J, c j * ∏ l, G j l (extendAt i₀ x t l))
      = tenP G c i₀ Finset.univ t := by
  have hfac : ∀ (j : Fin J) (x : ℝ),
      (∏ l : Fin k, G j l (extendAt i₀ x t l))
        = G j i₀ x * ∏ l : {l : Fin k // l ≠ i₀}, G j (l : Fin k) (t l) := by
    intro j x
    rw [← Finset.mul_prod_erase Finset.univ (fun l => G j l (extendAt i₀ x t l))
      (Finset.mem_univ i₀)]
    congr 1
    · simp [extendAt]
    · rw [prod_erase_eq_prod_subtype]
      refine Finset.prod_congr rfl fun l _ => ?_
      have hl : extendAt i₀ x t l.1 = t l := by
        simp only [extendAt, dif_neg l.2]
      rw [hl]
  simp only [hfac]
  rw [tenP]
  rw [MeasureTheory.integral_finsetSum (Finset.univ) (fun j _ => ?_)]
  · refine Finset.sum_congr rfl fun j _ => ?_
    rw [MeasureTheory.integral_const_mul, MeasureTheory.integral_mul_const]
    ring
  · have heq : (fun x : ℝ => c j * (G j i₀ x * ∏ l : {l : Fin k // l ≠ i₀}, G j (l : Fin k) (t l)))
        = fun x : ℝ =>
          (c j * ∏ l : {l : Fin k // l ≠ i₀}, G j (l : Fin k) (t l)) * G j i₀ x := by
      funext x; ring
    rw [heq]
    exact ((hGi j i₀).integrableOn).const_mul _

/-- **The `β`-coefficient of the antiderivative tensor data as the orthant integral of the
square of the marginal tensor sum.** -/
theorem tpBeta_anti_sq {J k : ℕ} {ψ : ℝ → ℝ} (hψ0 : ψ 0 = 1)
    (hψ1 : ∀ u : ℝ, 0 ≤ u → ψ u = 1)
    (G : Fin J → Fin k → ℝ → ℝ) (hGc : ∀ j i, Continuous (G j i))
    (hGcs : ∀ j i, HasCompactSupport (G j i))
    (hGi : ∀ j i, Integrable (G j i))
    (hGv : ∀ j i, ∃ R : ℝ, ∀ x : ℝ, R ≤ x → G j i x = 0) (c : Fin J → ℝ) (i₀ : Fin k) :
    tpBeta c (fun j i => anti ψ (G j) i) i₀
      = ∫ t : {l : Fin k // l ≠ i₀} → ℝ, (tenP G c i₀ Finset.univ t) ^ 2 * orthInd t := by
  rw [tpBeta_anti hψ0 hψ1 G hGc hGcs hGi hGv c i₀]
  refine MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall fun t => ?_)
  dsimp only
  rw [integral_tensorSum_extendAt G hGi c i₀ t]

/-- **The `J₂`-loss of the split is the orthant integral of the square of the complement.**
For antiderivative tensor data, the difference between the full `β`-coefficient and its
restricted (`J₁`) version is exactly the squared integral of the marginal tensor sum over the
complement of the `J₁`-set. -/
theorem tpBeta_sub_tpBetaSplit_anti {J k : ℕ} {ψ : ℝ → ℝ} (hψ0 : ψ 0 = 1)
    (hψ1 : ∀ u : ℝ, 0 ≤ u → ψ u = 1)
    (G : Fin J → Fin k → ℝ → ℝ) (hGc : ∀ j i, Continuous (G j i))
    (hGcs : ∀ j i, HasCompactSupport (G j i))
    (hGi : ∀ j i, Integrable (G j i))
    (hGv : ∀ j i, ∃ R : ℝ, ∀ x : ℝ, R ≤ x → G j i x = 0) (c : Fin J → ℝ)
    (S : Finset (Fin J)) (i₀ : Fin k) :
    tpBeta c (fun j i => anti ψ (G j) i) i₀
        - tpBetaSplit S c (fun j i => anti ψ (G j) i) i₀
      = ∫ t : {l : Fin k // l ≠ i₀} → ℝ,
          (tenP G c i₀ (Finset.univ \ S) t) ^ 2 * orthInd t := by
  rw [tpBeta_anti_sq hψ0 hψ1 G hGc hGcs hGi hGv c i₀,
    tpBetaSplit_anti hψ0 hψ1 G hGc hGcs hGi hGv c S i₀]
  have h2fun : (fun t : {l : Fin k // l ≠ i₀} → ℝ =>
      ((∑ j : Fin J, splitA S c j * (∫ x in Set.Ioi (0:ℝ), G j i₀ x) *
          ∏ l : {l : Fin k // l ≠ i₀}, G j (l : Fin k) (t l)) *
        (∑ j : Fin J, splitB S c j * (∫ x in Set.Ioi (0:ℝ), G j i₀ x) *
          ∏ l : {l : Fin k // l ≠ i₀}, G j (l : Fin k) (t l))) * orthInd t)
      = fun t : {l : Fin k // l ≠ i₀} → ℝ =>
        (tenPA G c i₀ S t * tenPB G c i₀ S t) * orthInd t := by
    funext t; simp only [tenPA, tenPB]
  rw [h2fun]
  rw [← MeasureTheory.integral_sub (integrable_tenP_sq G hGc hGcs c i₀ Finset.univ)
    (integrable_tenPA_mul_tenPB G hGc hGcs c i₀ S)]
  refine MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall fun t => ?_)
  dsimp only
  rw [tenPA_eq, tenPB_eq, tenP_sdiff (G := G) (c := c) (i := i₀) (S := S) t]
  ring

/-! ## The support of the `J₁`-part

If every component family `j ∈ S` has total support radius `Σ_{l ≠ i} β j l < c`, then on the
orthant the partial marginal sum `tenP G c i S` vanishes as soon as `Σ_{l ≠ i} t_l ≥ c`:
the support of `tenP G c i S` lies inside the marginal simplex of radius `c`. -/

/-- The `J₁`-part of the marginal tensor sum vanishes where the coordinate sum reaches its
support radius. -/
theorem tenP_eq_zero_of_sum_ge {J k : ℕ} (G : Fin J → Fin k → ℝ → ℝ) (c : Fin J → ℝ)
    (i : Fin k) (S : Finset (Fin J)) (M β : Fin J → Fin k → ℝ) {η rad : ℝ}
    (t : ({l : Fin k // l ≠ i} → ℝ))
    (hS : ∀ j ∈ S, ∑ l : {l : Fin k // l ≠ i}, M j (l : Fin k) < rad)
    (hβM : ∀ j l, β j l ≤ M j l)
    (hthin : ∀ j l u, 0 ≤ u → G j l u ≠ 0 → β j l - 6 * η < u ∧ u < β j l)
    (ht0 : ∀ l, 0 ≤ t l) (hge : rad ≤ ∑ l, t l) :
    tenP G c i S t = 0 := by
  classical
  rw [tenP]
  refine Finset.sum_eq_zero fun j hj => ?_
  by_cases hprod : ∏ l : {l : Fin k // l ≠ i}, G j (l : Fin k) (t l) = 0
  · rw [hprod, mul_zero]
  · exfalso
    have hlt : ∀ l : {l : Fin k // l ≠ i}, t l < M j (l : Fin k) := by
      intro l
      have hne : G j (l : Fin k) (t l) ≠ 0 := fun h0 =>
        hprod (Finset.prod_eq_zero (Finset.mem_univ l) h0)
      exact lt_of_lt_of_le (hthin j (l : Fin k) (t l) (ht0 l) hne).2 (hβM j (l : Fin k))
    have hsum : (∑ l : {l : Fin k // l ≠ i}, t l)
        ≤ ∑ l : {l : Fin k // l ≠ i}, M j (l : Fin k) :=
      Finset.sum_le_sum fun l _ => le_of_lt (hlt l)
    have := hS j hj
    linarith

/-- If the orthant indicator does not vanish then all coordinates are nonnegative. -/
lemma nonneg_of_orthInd_ne_zero {ι : Type*} [Fintype ι] {x : ι → ℝ}
    (h : orthInd x ≠ 0) : ∀ i, 0 ≤ x i := by
  intro i
  by_contra hi
  exact h (Finset.prod_eq_zero (Finset.mem_univ i)
    (Set.indicator_of_notMem (by simpa using hi) _))

/-- On the nonnegative orthant the orthant indicator equals one. -/
lemma orthInd_eq_one_of_nonneg {ι : Type*} [Fintype ι] {x : ι → ℝ}
    (h : ∀ i, 0 ≤ x i) : orthInd x = 1 :=
  Finset.prod_eq_one fun i _ => Set.indicator_of_mem (Set.mem_Ici.mpr (h i)) _

/-- The indicator of the marginal simplex of radius `c`, as a real-valued multiplier. -/
noncomputable def margInd (k : ℕ) (i : Fin k) (c : ℝ) :
    ({l : Fin k // l ≠ i} → ℝ) → ℝ :=
  (marginalSet k i c).indicator (fun _ => (1 : ℝ))

/-- **The restricted `β`-coefficient as the marginal functional minus the `J₂`-loss.**
With the `J₁`-set `S` (whose components have marginal support radius `< cc`), the restricted
coefficient `tpBetaSplit` equals the radius-`cc` marginal functional of the full marginal
tensor sum minus the corresponding functional of the complement (the `J₂`-part). -/
theorem tpBetaSplit_eq_marginal {J k : ℕ} {ψ : ℝ → ℝ} (hψ0 : ψ 0 = 1)
    (hψ1 : ∀ u : ℝ, 0 ≤ u → ψ u = 1)
    (G : Fin J → Fin k → ℝ → ℝ) (hGc : ∀ j i, Continuous (G j i))
    (hGcs : ∀ j i, HasCompactSupport (G j i))
    (hGi : ∀ j i, Integrable (G j i))
    (hGv : ∀ j i, ∃ R : ℝ, ∀ x : ℝ, R ≤ x → G j i x = 0) (c : Fin J → ℝ)
    (S : Finset (Fin J)) (i₀ : Fin k) (M β : Fin J → Fin k → ℝ) {η cc : ℝ}
    (hS : ∀ j ∈ S, ∑ l : {l : Fin k // l ≠ i₀}, M j (l : Fin k) < cc)
    (hβM : ∀ j l, β j l ≤ M j l)
    (hthin : ∀ j l u, 0 ≤ u → G j l u ≠ 0 → β j l - 6 * η < u ∧ u < β j l) :
    tpBetaSplit S c (fun j i => anti ψ (G j) i) i₀
      = (∫ t : ({l : Fin k // l ≠ i₀} → ℝ), (tenP G c i₀ Finset.univ t) ^ 2 *
            margInd k i₀ cc t)
        - ∫ t : ({l : Fin k // l ≠ i₀} → ℝ),
            (tenP G c i₀ (Finset.univ \ S) t) ^ 2 * margInd k i₀ cc t := by
  classical
  set P : (({l : Fin k // l ≠ i₀} → ℝ)) → ℝ :=
    fun t => tenP G c i₀ Finset.univ t with hP
  set PT : (({l : Fin k // l ≠ i₀} → ℝ)) → ℝ :=
    fun t => tenP G c i₀ (Finset.univ \ S) t with hPT
  have hmb : ∀ᵐ t ∂volume, ‖margInd k i₀ cc t‖ ≤ 1 := by
    refine Filter.Eventually.of_forall fun t => ?_
    by_cases ht : t ∈ marginalSet k i₀ cc
    · have h1 : margInd k i₀ cc t = 1 := Set.indicator_of_mem ht _
      rw [h1]; simp
    · have h0 : margInd k i₀ cc t = 0 := Set.indicator_of_notMem ht _
      rw [h0]; simp
  have hmeas : AEStronglyMeasurable (margInd k i₀ cc) volume :=
    (measurable_const.indicator (measurableSet_marginalSet k i₀ cc)).aestronglyMeasurable
  have horth1 : ∀ t : ({l : Fin k // l ≠ i₀} → ℝ), t ∈ marginalSet k i₀ cc →
      orthInd t = 1 :=
    fun t ht => orthInd_eq_one_of_nonneg fun l => (Set.mem_ofPred_eq.mp ht).1 l
  have hIntP : Integrable (fun t : (({l : Fin k // l ≠ i₀} → ℝ)) =>
      (P t) ^ 2 * margInd k i₀ cc t) := by
    have h0 : Integrable (fun t : (({l : Fin k // l ≠ i₀} → ℝ)) =>
        (P t) ^ 2 * orthInd t) := by
      simp only [hP]
      exact integrable_tenP_sq G hGc hGcs c i₀ Finset.univ
    refine (h0.mul_bdd (g := margInd k i₀ cc) hmeas hmb).congr
      (Filter.Eventually.of_forall fun t => ?_)
    dsimp only
    by_cases ht : t ∈ marginalSet k i₀ cc
    · have h1 : margInd k i₀ cc t = 1 := Set.indicator_of_mem ht _
      rw [h1, horth1 t ht]; ring
    · have h0' : margInd k i₀ cc t = 0 := Set.indicator_of_notMem ht _
      rw [h0']; ring
  have hIntT : Integrable (fun t : (({l : Fin k // l ≠ i₀} → ℝ)) =>
      (PT t) ^ 2 * margInd k i₀ cc t) := by
    have h0 : Integrable (fun t : (({l : Fin k // l ≠ i₀} → ℝ)) =>
        (PT t) ^ 2 * orthInd t) := by
      simp only [hPT]
      exact integrable_tenP_sq G hGc hGcs c i₀ (Finset.univ \ S)
    refine (h0.mul_bdd (g := margInd k i₀ cc) hmeas hmb).congr
      (Filter.Eventually.of_forall fun t => ?_)
    dsimp only
    by_cases ht : t ∈ marginalSet k i₀ cc
    · have h1 : margInd k i₀ cc t = 1 := Set.indicator_of_mem ht _
      rw [h1, horth1 t ht]; ring
    · have h0' : margInd k i₀ cc t = 0 := Set.indicator_of_notMem ht _
      rw [h0']; ring
  rw [tpBetaSplit_anti hψ0 hψ1 G hGc hGcs hGi hGv c S i₀]
  have hstep : (∫ t : (({l : Fin k // l ≠ i₀} → ℝ)),
      ((∑ j : Fin J, splitA S c j * (∫ x in Set.Ioi (0:ℝ), G j i₀ x) *
          ∏ l : {l : Fin k // l ≠ i₀}, G j (l : Fin k) (t l)) *
        (∑ j : Fin J, splitB S c j * (∫ x in Set.Ioi (0:ℝ), G j i₀ x) *
          ∏ l : {l : Fin k // l ≠ i₀}, G j (l : Fin k) (t l))) * orthInd t)
      = ∫ t : (({l : Fin k // l ≠ i₀} → ℝ)), ((P t) ^ 2 - (PT t) ^ 2) * margInd k i₀ cc t := by
    refine MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall fun t => ?_)
    dsimp only
    have hel : tenPA G c i₀ S t * tenPB G c i₀ S t = (P t) ^ 2 - (PT t) ^ 2 := by
      simp only [hP, hPT, tenPA_eq, tenPB_eq,
        tenP_sdiff (G := G) (c := c) (i := i₀) (S := S) t]
      ring
    have hAB : (∑ j : Fin J, splitA S c j * (∫ x in Set.Ioi (0:ℝ), G j i₀ x) *
          ∏ l : {l : Fin k // l ≠ i₀}, G j (l : Fin k) (t l)) *
        (∑ j : Fin J, splitB S c j * (∫ x in Set.Ioi (0:ℝ), G j i₀ x) *
          ∏ l : {l : Fin k // l ≠ i₀}, G j (l : Fin k) (t l))
        = tenPA G c i₀ S t * tenPB G c i₀ S t := by
      simp only [tenPA, tenPB]
    rw [hAB, hel]
    by_cases ht : t ∈ marginalSet k i₀ cc
    · have h1 : margInd k i₀ cc t = 1 := Set.indicator_of_mem ht _
      rw [h1, horth1 t ht]
    · have h0' : margInd k i₀ cc t = 0 := Set.indicator_of_notMem ht _
      rw [h0']
      by_cases horth0 : orthInd t = 0
      · rw [horth0]
      · have hnn := nonneg_of_orthInd_ne_zero horth0
        have hsum : cc ≤ ∑ l : {l : Fin k // l ≠ i₀}, t l := by
          have hnot : ¬ (∑ l : {l : Fin k // l ≠ i₀}, t l) ≤ cc := fun h => ht ⟨hnn, h⟩
          linarith
        have hPS : tenP G c i₀ S t = 0 :=
          tenP_eq_zero_of_sum_ge G c i₀ S M β t hS hβM hthin hnn hsum
        have hel2 : (P t) ^ 2 - (PT t) ^ 2 = 0 := by
          simp only [hP, hPT, tenP_sdiff (G := G) (c := c) (i := i₀) (S := S) t, hPS]
          ring
        rw [hel2]; ring
  rw [hstep]
  simp only [sub_mul]
  rw [integral_sub hIntP hIntT]

/-- Integrability of the square of a partial tensor marginal sum against the marginal simplex. -/
theorem integrable_tenP_sq_margInd {J k : ℕ} (G : Fin J → Fin k → ℝ → ℝ)
    (hGc : ∀ j i, Continuous (G j i)) (hGcs : ∀ j i, HasCompactSupport (G j i))
    (c : Fin J → ℝ) (i : Fin k) (S : Finset (Fin J)) (cc : ℝ) :
    Integrable (fun t : ({l : Fin k // l ≠ i} → ℝ) =>
      (tenP G c i S t) ^ 2 * margInd k i cc t) := by
  classical
  have h0 : Integrable (fun t : ({l : Fin k // l ≠ i} → ℝ) =>
      (tenP G c i S t) ^ 2 * orthInd t) := integrable_tenP_sq G hGc hGcs c i S
  have hmeas : AEStronglyMeasurable (margInd k i cc) volume :=
    (measurable_const.indicator (measurableSet_marginalSet k i cc)).aestronglyMeasurable
  have hbdd : ∀ᵐ t ∂volume, ‖margInd k i cc t‖ ≤ 1 := by
    refine Filter.Eventually.of_forall fun t => ?_
    by_cases ht : t ∈ marginalSet k i cc
    · have h1 : margInd k i cc t = 1 := Set.indicator_of_mem ht _
      rw [h1]; simp
    · have h0' : margInd k i cc t = 0 := Set.indicator_of_notMem ht _
      rw [h0']; simp
  refine (h0.mul_bdd (g := margInd k i cc) hmeas hbdd).congr
    (Filter.Eventually.of_forall fun t => ?_)
  dsimp only
  by_cases ht : t ∈ marginalSet k i cc
  · have h1 : margInd k i cc t = 1 := Set.indicator_of_mem ht _
    have horth : orthInd t = 1 :=
      orthInd_eq_one_of_nonneg fun l => (Set.mem_ofPred_eq.mp ht).1 l
    rw [h1, horth]; ring
  · have h0' : margInd k i cc t = 0 := Set.indicator_of_notMem ht _
    rw [h0']; ring

end Commons.NumberTheory.MaynardSieve
