import Mathlib
import Submission.Work.BourgainPlan.IonescuWainger.tsum_norm_prod_union_eq_sum_tuples

/-!
# The core rearrangement step of Tao's `ortho-apply`(i), first inequality

Source: T. Tao, *The Ionescu–Wainger multiplier theorem and the adeles*, arXiv:2008.05066, §4,
Theorem `ortho-apply`(i), first inequality.

For a fixed core `A₀ ⊆ S` and the family `F = (S \ A₀).powerset.filter (·.card ≤ k - A₀.card)` of
admissible petals, the sum over tuples of *pairwise disjoint* petals of `∫ ∏_i ‖f_{Σ_{A₀∪A_i}}‖²` is
bounded by the "core sum" `∫ (Σ_{α ∈ Σ_{(A₀)}} ‖f_{α+Σ_{A₀}}‖²)^r`.

The two bookkeeping lemmas needed are proved here:

* `prod_QA_le_QA_of_pairwiseDisjoint` — for pairwise disjoint `P i ⊆ S`, the product
  `∏_i Q_{P_i}` is at most `Q_S`; this is what upgrades the smallness hypothesis of the statement
  (stated for the single denominator `Q_{A₀} · Q_S`) to the smallness hypothesis of
  `tsum_norm_prod_union_eq_sum_tuples` (stated for `Q_{A₀} · ∏_i Q_{P_i}`);
* `tsum_pow_sum_eq_sum_tuples_finset` — the `Finset` (as opposed to `Fintype`) form of
  `tsum_pow_sum_eq_sum_tuples`, needed because the circle `𝕋 = Circle` has no `Fintype` instance.

With those, the proof is the `calc` below: expand each admissible tuple by the Pythagoras identity
`tsum_norm_prod_union_eq_sum_tuples`, drop the disjointness filter (every term is nonnegative),
re-index the `(petal, arc point)` tuples by tuples of arc points of `Σ_{(A₀)} = F.biUnion
sigmaAFinset` (`sum_pi_sigmaAFinset_eq_sum_pi_biUnion`), and recognise the result as the expansion
of the `r`-th power of the core sum (`tsum_pow_sum_eq_sum_tuples_finset`).
-/

open Finset MeasureTheory
open scoped BigOperators ENNReal lp

set_option autoImplicit false

namespace Work.BourgainPlan.IonescuWainger

/-- **`Q` is monotone along a pairwise disjoint family.**  For a pairwise disjoint family
`P : Fin r → Finset ℕ` with `P i ⊆ S` and `S` consisting of integers `≥ 2`, the product of the
denominators `Q_{P i} = ∏_{q ∈ P i} q` is at most `Q_S = ∏_{q ∈ S} q`.

Indeed `∏_i Q_{P i} = Q_{⋃_i P i}` (the disjointness makes `Q` multiplicative over the union) and
`Q` is monotone on subsets of a set of positive integers, since `Q_T` divides `Q_S` for `T ⊆ S`. -/
theorem prod_QA_le_QA_of_pairwiseDisjoint {S : Finset ℕ} {r : ℕ} {P : Fin r → Finset ℕ}
    (h2 : ∀ q ∈ S, 2 ≤ q) (hP : ∀ i : Fin r, P i ⊆ S)
    (hdisj : ∀ i j : Fin r, i ≠ j → Disjoint (P i) (P j)) :
    ∏ i : Fin r, QA (P i) ≤ QA S := by
  classical
  have hpd : Set.PairwiseDisjoint (↑(Finset.univ : Finset (Fin r)) : Set (Fin r)) P :=
    fun i _ j _ hij => hdisj i j hij
  have hprod : QA (Finset.univ.biUnion P) = ∏ i : Fin r, QA (P i) := by
    rw [QA, Finset.prod_biUnion (f := fun x : ℕ => x) hpd]
    simp [QA]
  have hsub : Finset.univ.biUnion P ⊆ S := Finset.biUnion_subset.mpr (fun i _ => hP i)
  have hdvd : QA (Finset.univ.biUnion P) ∣ QA S :=
    Finset.prod_dvd_prod_of_subset (Finset.univ.biUnion P) S (fun x : ℕ => x) hsub
  calc ∏ i : Fin r, QA (P i) = QA (Finset.univ.biUnion P) := hprod.symm
    _ ≤ QA S := Nat.le_of_dvd (Nat.pos_of_ne_zero (QA_ne_zero_of_two_le h2)) hdvd

/-- **Expansion of the `r`-th power of a `Finset`-indexed sum into `r`-tuples**, in the
`Finset` (as opposed to `Fintype`) form: for a `Finset E` in an arbitrary type `ι`,

`∑'_m (∑_{α ∈ E} ‖g α m‖²)^r = ∑_{α : Fin r → ↥E} ∑'_m ∏_i ‖g (α i).1 m‖²`.

This is `tsum_pow_sum_eq_sum_tuples` with the ambient type `ι` replaced by the subtype `↥E` (which
is a fintype as soon as `E` is a finset, no `Fintype ι` being needed — the circle `𝕋` being the
case of interest). -/
theorem tsum_pow_sum_eq_sum_tuples_finset {ι : Type*} (E : Finset ι)
    {r : ℕ} (hr : 1 ≤ r) {g : ι → ℤ → ℂ} (hg : ∀ α, Memℓp (g α) 2) :
    ∑' m : ℤ, (∑ α ∈ E, ‖g α m‖ ^ 2) ^ r
      = ∑ α : Fin r → ↥E, ∑' m : ℤ, ∏ i, ‖g (α i).1 m‖ ^ 2 := by
  classical
  have hpoint : ∀ m : ℤ, (∑ α ∈ E, ‖g α m‖ ^ 2) ^ r
      = ∑ α : Fin r → ↥E, ∏ i, ‖g (α i).1 m‖ ^ 2 := by
    intro m
    have h1 : (∑ α ∈ E, ‖g α m‖ ^ 2) = ∑ α : ↥E, ‖g α.1 m‖ ^ 2 := by
      rw [← Finset.sum_attach (s := E) (f := fun α => ‖g α m‖ ^ 2), Finset.attach_eq_univ]
    rw [h1, Fintype.sum_pow]
  rw [tsum_congr hpoint]
  -- Each single squared modulus is summable.
  have hsq : ∀ β : ι, Summable (fun m : ℤ => ‖g β m‖ ^ 2) := by
    intro β
    have h := (memℓp_gen_iff (p := 2) (by norm_num)).mp (hg β)
    simpa [Real.rpow_two] using h
  have hbdd : ∀ β : ι, ∀ m : ℤ, ‖g β m‖ ^ 2 ≤ ∑' j : ℤ, ‖g β j‖ ^ 2 :=
    fun β m => (hsq β).le_tsum m (fun j _ => sq_nonneg _)
  -- Each tuple product is summable: bound all factors but `i = 0` by their `ℓ²`-mass.
  have hsum : ∀ α : Fin r → ↥E, Summable (fun m : ℤ => ∏ i, ‖g (α i).1 m‖ ^ 2) := by
    intro α
    refine Summable.of_nonneg_of_le (fun m => Finset.prod_nonneg (fun i _ => sq_nonneg _))
      (fun m => ?_) ((hsq (α ⟨0, hr⟩).1).mul_left
        (∏ i ∈ Finset.univ.erase ⟨0, hr⟩, ∑' j : ℤ, ‖g (α i).1 j‖ ^ 2))
    rw [← Finset.prod_erase_mul Finset.univ (fun i => ‖g (α i).1 m‖ ^ 2)
      (Finset.mem_univ ⟨0, hr⟩)]
    exact mul_le_mul_of_nonneg_right
      (Finset.prod_le_prod₀ (fun i _ => sq_nonneg _) (fun i _ => hbdd (α i).1 m)) (sq_nonneg _)
  -- Exchange the outer `tsum` with the finite tuple sum.
  rw [Summable.tsum_finsetSum (fun α _ => hsum α)]

end Work.BourgainPlan.IonescuWainger
