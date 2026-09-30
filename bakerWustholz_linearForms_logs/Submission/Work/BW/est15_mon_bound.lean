import Mathlib
import Submission.Work.BW.est15defs
import Submission.Work.BW.LiouvilleAux.posLog_hasFiniteSupport

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

namespace Work.BW

/-- Interchange of a `finsum` with a finite sum of functions of finite support:
`∑ᶠ a, ∑ i, f i a = ∑ i, ∑ᶠ a, f i a`. -/
lemma finsum_sum_univ {ι α : Type*} [Fintype ι] {f : ι → α → ℝ}
    (h : ∀ i, Function.HasFiniteSupport (f i)) :
    (∑ᶠ a, ∑ i : ι, f i a) = ∑ i, ∑ᶠ a, f i a := by
  classical
  have hmem : ∀ i (a : α), a ∈ (h i).toFinset ↔ f i a ≠ 0 := fun i a =>
    Iff.trans (Set.Finite.mem_toFinset _) Function.mem_support
  have hsub_i : ∀ i, Function.support (f i) ⊆
      (((Finset.univ.biUnion (fun i => (h i).toFinset) : Finset α)) : Set α) := by
    intro i a ha
    rw [Function.mem_support] at ha
    exact Finset.subset_biUnion_of_mem (fun i => (h i).toFinset) (Finset.mem_univ i)
      ((hmem i a).mpr ha)
  have hsub_sum : Function.support (fun a => ∑ i, f i a) ⊆
      (((Finset.univ.biUnion (fun i => (h i).toFinset) : Finset α)) : Set α) := by
    intro a ha
    by_contra hcon
    rw [Function.mem_support] at ha
    exact ha (Finset.sum_eq_zero (fun i _ => by
      by_contra hne
      exact hcon (Finset.subset_biUnion_of_mem (fun i => (h i).toFinset) (Finset.mem_univ i)
        ((hmem i a).mpr hne))))
  rw [finsum_eq_finsetSum_of_support_subset _ hsub_sum, Finset.sum_comm]
  exact Finset.sum_congr rfl
    (fun i _ => (finsum_eq_finsetSum_of_support_subset _ (hsub_i i)).symm)

theorem est15_mon_bound {K : Type*} [Field K] [NumberField K] {r : ℕ} {σ : Fin r → ℝ}
    (v₀ : NumberField.InfinitePlace K) [DecidableEq (NumberField.InfinitePlace K)]
    (β : Fin r → K) (J : ℕ) (s : ℤ)
    (hβ : (∑ j : Fin r, (pDj r (dK K) σ j : ℝ) *
        ((∑ w ∈ Finset.univ.erase v₀, ((w.mult : ℕ) : ℝ) * Real.posLog (w (β j)))
          + (∑ᶠ w : NumberField.FinitePlace K, Real.posLog (w (β j))))) ≤ acD K σ) :
    (∑ w ∈ Finset.univ.erase v₀, ((w.mult : ℕ) : ℝ) * estMon K σ β J s w)
      + (∑ᶠ w : NumberField.FinitePlace K, estMon K σ β J s w)
    ≤ (((|s| : ℤ) : ℝ) / 2 ^ J) * acD K σ := by
  classical
  -- ### Finite support of the finite-place summands
  have hfs : ∀ j : Fin r, Function.HasFiniteSupport
      (fun w : NumberField.FinitePlace K => Real.posLog (w (β j))) := by
    intro j
    by_cases hj : β j = 0
    · rw [hj]
      simp [Function.HasFiniteSupport, Function.support]
    · exact LiouvilleAux.posLog_hasFiniteSupport (β j) hj
  have hfs_mul : ∀ j : Fin r, Function.HasFiniteSupport
      (fun w : NumberField.FinitePlace K =>
        (pDj r (dK K) σ j : ℝ) * Real.posLog (w (β j))) := by
    intro j
    refine (hfs j).subset ?_
    intro w hw
    rw [Function.mem_support] at hw ⊢
    intro h
    exact hw (by rw [h, mul_zero])
  -- ### The finite-place part factors out the common scalar
  have hfin : (∑ᶠ w : NumberField.FinitePlace K, estMon K σ β J s w)
      = (((|s| : ℤ) : ℝ) / 2 ^ J) * ∑ j : Fin r, (pDj r (dK K) σ j : ℝ) *
          (∑ᶠ w : NumberField.FinitePlace K, Real.posLog (w (β j))) := by
    have e1 : (∑ᶠ w : NumberField.FinitePlace K, estMon K σ β J s w)
        = ∑ᶠ w : NumberField.FinitePlace K,
            (((|s| : ℤ) : ℝ) / 2 ^ J) *
              ∑ j : Fin r, (pDj r (dK K) σ j : ℝ) * Real.posLog (w (β j)) :=
      finsum_congr (fun w => by rw [estMon])
    have e2 : (∑ᶠ w : NumberField.FinitePlace K,
            (((|s| : ℤ) : ℝ) / 2 ^ J) *
              ∑ j : Fin r, (pDj r (dK K) σ j : ℝ) * Real.posLog (w (β j)))
        = (((|s| : ℤ) : ℝ) / 2 ^ J) * ∑ᶠ w : NumberField.FinitePlace K,
              ∑ j : Fin r, (pDj r (dK K) σ j : ℝ) * Real.posLog (w (β j)) :=
      (mul_finsum _ _).symm
    rw [e1, e2, finsum_sum_univ hfs_mul]
    congr 1
    exact Finset.sum_congr rfl (fun j _ => (mul_finsum _ _).symm)
  -- ### The infinite-place part factors out the common scalar
  have hinf : (∑ w ∈ Finset.univ.erase v₀, ((w.mult : ℕ) : ℝ) * estMon K σ β J s w)
      = (((|s| : ℤ) : ℝ) / 2 ^ J) * ∑ j : Fin r, (pDj r (dK K) σ j : ℝ) *
          (∑ w ∈ Finset.univ.erase v₀, ((w.mult : ℕ) : ℝ) * Real.posLog (w (β j))) := by
    have e1 : ∀ w : NumberField.InfinitePlace K, ((w.mult : ℕ) : ℝ) * estMon K σ β J s w
        = ∑ j : Fin r, (((|s| : ℤ) : ℝ) / 2 ^ J) *
            ((pDj r (dK K) σ j : ℝ) * (((w.mult : ℕ) : ℝ) * Real.posLog (w (β j)))) := by
      intro w
      rw [estMon, Finset.mul_sum, Finset.mul_sum]
      exact Finset.sum_congr rfl (fun j _ => by ring)
    have e1' : (∑ w ∈ Finset.univ.erase v₀, ((w.mult : ℕ) : ℝ) * estMon K σ β J s w)
        = ∑ w ∈ Finset.univ.erase v₀, ∑ j : Fin r, (((|s| : ℤ) : ℝ) / 2 ^ J) *
            ((pDj r (dK K) σ j : ℝ) * (((w.mult : ℕ) : ℝ) * Real.posLog (w (β j)))) :=
      Finset.sum_congr rfl (fun w _ => e1 w)
    rw [e1', Finset.sum_comm]
    have key : ∀ j : Fin r,
        (∑ w ∈ Finset.univ.erase v₀, (((|s| : ℤ) : ℝ) / 2 ^ J) *
            ((pDj r (dK K) σ j : ℝ) * (((w.mult : ℕ) : ℝ) * Real.posLog (w (β j)))))
        = (((|s| : ℤ) : ℝ) / 2 ^ J) * ((pDj r (dK K) σ j : ℝ) *
            (∑ w ∈ Finset.univ.erase v₀, ((w.mult : ℕ) : ℝ) * Real.posLog (w (β j)))) := by
      intro j
      rw [Finset.mul_sum, Finset.mul_sum]
    rw [Finset.sum_congr rfl (fun j _ => key j)]
    exact (Finset.mul_sum Finset.univ
      (fun j : Fin r => (pDj r (dK K) σ j : ℝ) *
        (∑ w ∈ Finset.univ.erase v₀, ((w.mult : ℕ) : ℝ) * Real.posLog (w (β j))))
      (((|s| : ℤ) : ℝ) / 2 ^ J)).symm
  -- ### Split the hypothesis into its infinite- and finite-place parts
  have hXY : ((∑ j : Fin r, (pDj r (dK K) σ j : ℝ) *
          (∑ w ∈ Finset.univ.erase v₀, ((w.mult : ℕ) : ℝ) * Real.posLog (w (β j))))
      + (∑ j : Fin r, (pDj r (dK K) σ j : ℝ) *
          (∑ᶠ w : NumberField.FinitePlace K, Real.posLog (w (β j))))) ≤ acD K σ := by
    have hsplit : (∑ j : Fin r, (pDj r (dK K) σ j : ℝ) *
          ((∑ w ∈ Finset.univ.erase v₀, ((w.mult : ℕ) : ℝ) * Real.posLog (w (β j)))
            + (∑ᶠ w : NumberField.FinitePlace K, Real.posLog (w (β j)))))
        = (∑ j : Fin r, (pDj r (dK K) σ j : ℝ) *
            (∑ w ∈ Finset.univ.erase v₀, ((w.mult : ℕ) : ℝ) * Real.posLog (w (β j))))
          + (∑ j : Fin r, (pDj r (dK K) σ j : ℝ) *
            (∑ᶠ w : NumberField.FinitePlace K, Real.posLog (w (β j)))) := by
      simp only [mul_add, Finset.sum_add_distrib]
    rw [hsplit] at hβ
    exact hβ
  -- ### Assemble
  have hLHS : (∑ w ∈ Finset.univ.erase v₀, ((w.mult : ℕ) : ℝ) * estMon K σ β J s w)
      + (∑ᶠ w : NumberField.FinitePlace K, estMon K σ β J s w)
      = (((|s| : ℤ) : ℝ) / 2 ^ J) *
          ((∑ j : Fin r, (pDj r (dK K) σ j : ℝ) *
              (∑ w ∈ Finset.univ.erase v₀, ((w.mult : ℕ) : ℝ) * Real.posLog (w (β j))))
            + (∑ j : Fin r, (pDj r (dK K) σ j : ℝ) *
              (∑ᶠ w : NumberField.FinitePlace K, Real.posLog (w (β j))))) := by
    rw [hinf, hfin, ← mul_add]
  rw [hLHS]
  have hc_nonneg : (0 : ℝ) ≤ ((|s| : ℤ) : ℝ) / 2 ^ J := by
    have h1 : (0 : ℝ) ≤ ((|s| : ℤ) : ℝ) := by exact_mod_cast abs_nonneg s
    have h2 : (0 : ℝ) < (2 : ℝ) ^ J := by positivity
    exact div_nonneg h1 h2.le
  exact mul_le_mul_of_nonneg_left hXY hc_nonneg

end Work.BW
