import Mathlib
import Submission.Work.BourgainPlan.IonescuWainger.tsum_norm_sq_sum_of_orthogonal
import Submission.Work.BourgainPlan.IonescuWainger.coe_sigmaAFinset
import Submission.Work.BourgainPlan.IonescuWainger.ShiftArcDefs
import Submission.Work.BourgainPlan.IonescuWainger.sigmaA_petal_sum_shift_perturbed_ne_zero
import Submission.Work.BourgainPlan.IonescuWainger.tsum_prod_mul_conj_eq_zero_of_freqSupport

/-!
# The Pythagoras step of Tao's `ortho-apply`(i): expanding the major-arc product into tuples

Source: T. Tao, *The Ionescu–Wainger multiplier theorem and the adeles*, arXiv:2008.05066, §4,
Theorem `ortho-apply`(i) (the Pythagoras step of the proof), and its ℓ²-band-limited
implementation in this workspace (`tsum_prod_shift_mul_conj_eq_zero_of_petal_l2`,
`tsum_norm_sq_sum_of_orthogonal`).

The major-arc system `f_{Σ_{A₀ ∪ P i}} = Σ_{δ ∈ Σ_{A₀ ∪ P i}} f δ` of a sunflower with core `A₀`
and pairwise disjoint petals `P i` decomposes, by the direct-sum identity
`Σ_{A₀ ∪ P i} = Σ_{A₀} ⊕ Σ_{P i}` (`sigmaAFinset_union_add`), as the sum over `α i ∈ Σ_{P i}` of
the *shifted* major-arc functions `f_{Σ_{A₀} + α i} = Σ_{γ ∈ Σ_{A₀}} f (γ + α i)`.  Consequently
the pointwise product of the `r` systems is a sum over the tuples
`α : Π i, Σ_{P i}` of the products `Π i, f_{Σ_{A₀} + α i}`.

Since the tuples are pairwise orthogonal in ℓ²(ℤ) (`tsum_prod_shift_mul_conj_eq_zero_of_petal_l2`,
which is Tao's `ortho`(iii) with a core), Pythagoras
(`tsum_norm_sq_sum_of_orthogonal`) turns the squared ℓ²-norm of the product into the sum of the
squared ℓ²-norms of the tuple products:

`Σ_m ‖Π_i f_{Σ_{A₀ ∪ P i}}(m)‖² = Σ_α Σ_m ‖Π_i f_{Σ_{A₀} + α_i}(m)‖²`.

## Main declarations

* `Work.BourgainPlan.IonescuWainger.prod_sum_attach` — a product of sums is the sum over the
  dependent tuples of the products (the `Finset.pi`/subtype bookkeeping);
* `Work.BourgainPlan.IonescuWainger.memℓp_prod_of_memℓp` — a finite pointwise product of `ℓ²(ℤ)`
  sequences is `ℓ²` (the `ℓ² ⊆ ℓ^∞` bound absorbs all but one factor into a summable one);
* `Work.BourgainPlan.IonescuWainger.tsum_prod_shift_orthogonal_fin` — the orthogonality of the
  shifted tuple products for `Fin r` (transport of the `Fin (n+1)` capstone along `finCongr`);
* `Work.BourgainPlan.IonescuWainger.tsum_norm_prod_union_eq_sum_tuples` — the target identity.
-/

open Finset MeasureTheory
open scoped BigOperators ENNReal lp

set_option autoImplicit false

namespace Work.BourgainPlan.IonescuWainger

/-- **A product of finite sums is the sum over the dependent tuples of the products.**  For a
finite index type `ι` and finsets `t i`,

`∏ i, ∑ j ∈ t i, g i j = ∑ x : ((i : ι) → ↥(t i)), ∏ i, g i (x i).1`,

the `Finset.pi`-type bookkeeping behind the expansion of the major-arc product into the tuple
sums `∑ α : Π i, Σ_{P i}, Π i, f_{Σ_{A₀} + α i}`. -/
theorem prod_sum_attach {ι : Type*} [Fintype ι] [DecidableEq ι] {κ : ι → Type*}
    (t : (i : ι) → Finset (κ i)) (g : (i : ι) → κ i → ℂ) :
    (∏ i, ∑ j ∈ t i, g i j) = ∑ x : ((i : ι) → ↥(t i)), ∏ i, g i (x i).1 := by
  classical
  rw [Finset.prod_univ_sum]
  refine (Finset.sum_bij (fun (y : (i : ι) → ↥(t i)) (_ : y ∈ Finset.univ) => fun i => (y i).1)
    ?_ ?_ ?_ ?_).symm
  · intro y _
    exact Fintype.mem_piFinset.mpr (fun i => (y i).2)
  · intro y₁ _ y₂ _ h
    funext i
    exact Subtype.ext (congr_fun h i)
  · intro x hx
    refine ⟨fun i => ⟨x i, (Fintype.mem_piFinset.mp hx) i⟩, Finset.mem_univ _, ?_⟩
    rfl
  · intro y _
    rfl

/-- **A finite pointwise product of `ℓ²(ℤ)` sequences is `ℓ²`.**  Each factor is bounded by its
`ℓ²`-norm (as `ℓ² ⊆ ℓ^∞` for the counting measure), so all factors except one may be bounded by
constants and the remaining squared modulus is summable. -/
theorem memℓp_prod_of_memℓp {ι : Type*} [Fintype ι] [DecidableEq ι] (i₀ : ι) {h : ι → ℤ → ℂ}
    (hh : ∀ i, Memℓp (h i) 2) :
    Memℓp (fun m : ℤ => ∏ i, h i m) 2 := by
  classical
  refine memℓp_gen (p := 2) ?_
  simp only [ENNReal.toReal_ofNat]
  have hsq : ∀ i, Summable fun m : ℤ => ‖h i m‖ ^ 2 := by
    intro i
    have := (memℓp_gen_iff (p := 2) (by norm_num)).mp (hh i)
    simpa [Real.rpow_two] using this
  have hbound : ∀ i m, ‖h i m‖ ^ 2 ≤ ∑' j, ‖h i j‖ ^ 2 := fun i m =>
    (hsq i).le_tsum m (fun j _ => sq_nonneg _)
  have hmain : Summable fun m : ℤ =>
      (∏ i ∈ Finset.univ.erase i₀, (∑' j, ‖h i j‖ ^ 2)) * ‖h i₀ m‖ ^ 2 :=
    (hsq i₀).mul_left _
  rw [show (fun m : ℤ => ‖∏ i, h i m‖ ^ (2:ℝ)) = (fun m => ∏ i, ‖h i m‖ ^ 2) from by
    funext m; rw [Real.rpow_two, norm_prod, ← Finset.prod_pow]]
  refine Summable.of_nonneg_of_le (fun m => Finset.prod_nonneg fun i _ => sq_nonneg _)
    (fun m => ?_) hmain
  rw [← Finset.prod_erase_mul Finset.univ (fun i => ‖h i m‖ ^ 2) (Finset.mem_univ i₀)]
  exact mul_le_mul_of_nonneg_right
    (Finset.prod_le_prod₀ (fun i _ => sq_nonneg _) (fun i _ => hbound i m)) (sq_nonneg _)

end Work.BourgainPlan.IonescuWainger
