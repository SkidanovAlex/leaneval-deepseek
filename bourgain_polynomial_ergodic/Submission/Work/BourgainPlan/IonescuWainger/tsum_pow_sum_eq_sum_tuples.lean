import Mathlib
import Submission.Work.BourgainPlan.IonescuWainger.FourierL2Sum

/-!
# Expanding `∑'_m (∑_{α∈E} ‖g α m‖²)^r` into tuples

For a finite index type `ι`, a finset `E : Finset ι` and an `ℓ²(ℤ)`-family `g : ι → ℤ → ℂ`, the
`r`-th power of the pointwise inner sum `∑_{α∈E} ‖g α m‖²` expands, by the multinomial identity
`(∑_a f a)^r = ∑_{p : Fin r → ↥E} ∏_i f (p i)`, as the sum over the tuples `p : Fin r → ↥E` of the
products `∏_i ‖g (p i).1 m‖²`.  The `tsum` over `m` then exchanges with the finite tuple sum
(`Summable.tsum_finsetSum`), each individual tuple product being summable because all but one of its
nonnegative factors can be bounded by the finite `ℓ²`-norms of `g` (`ℓ² ⊆ ℓ^∞` on the counting
measure of `ℤ`).

This is the "expand the `r`-th power into an `r`-tuple" bookkeeping step used when squaring a
finite sum of band-limited `ℓ²`-functions.
-/

open MeasureTheory
open scoped BigOperators

set_option autoImplicit false

namespace Work.BourgainPlan.IonescuWainger

/-- **Expansion of the `r`-th power of a finite sum of `ℓ²`-densities into `r`-tuples.**  For an
`ℓ²(ℤ)`-family `g : ι → ℤ → ℂ` indexed by a finite type `ι`, a finset `E : Finset ι` and `r ≥ 1`,

`∑'_m (∑_{α ∈ E} ‖g α m‖²)^r = ∑_{p : Fin r → ↥E} ∑'_m ∏_i ‖g (p i).1 m‖²`.

The pointwise multinomial expansion turns the inner `r`-th power into the finite sum over the
tuples `p : Fin r → ↥E`, which is then exchanged with the outer `tsum`. -/
theorem tsum_pow_sum_eq_sum_tuples {ι : Type*} [Fintype ι] [DecidableEq ι] (E : Finset ι)
    {r : ℕ} (hr : 1 ≤ r) {g : ι → ℤ → ℂ} (hg : ∀ α, Memℓp (g α) 2) :
    ∑' m : ℤ, (∑ α ∈ E, ‖g α m‖ ^ 2) ^ r
      = ∑ α : Fin r → ↥E, ∑' m : ℤ, ∏ i, ‖g (α i).1 m‖ ^ 2 := by
  classical
  -- Pointwise, the `r`-th power of the inner sum expands into the tuples.
  have hpoint : ∀ m : ℤ, (∑ α ∈ E, ‖g α m‖ ^ 2) ^ r
      = ∑ α : Fin r → ↥E, ∏ i, ‖g (α i).1 m‖ ^ 2 := by
    intro m
    have h1 : (∑ α ∈ E, ‖g α m‖ ^ 2) = ∑ α : ↥E, ‖g α.1 m‖ ^ 2 := by
      rw [← Finset.sum_attach (s := E) (f := fun α => ‖g α m‖ ^ 2), Finset.attach_eq_univ]
    rw [h1, Fintype.sum_pow]
  rw [tsum_congr hpoint]
  -- Each single squared modulus is summable (the `ℓ²`-hypothesis on the counting measure of `ℤ`).
  have hsq : ∀ β : ι, Summable (fun m : ℤ => ‖g β m‖ ^ 2) := by
    intro β
    have h := (memℓp_gen_iff (p := 2) (by norm_num)).mp (hg β)
    simpa [Real.rpow_two] using h
  -- `ℓ² ⊆ ℓ^∞`: every term is bounded by the total `ℓ²`-mass.
  have hbdd : ∀ β : ι, ∀ m : ℤ, ‖g β m‖ ^ 2 ≤ ∑' j : ℤ, ‖g β j‖ ^ 2 :=
    fun β m => (hsq β).le_tsum m (fun j _ => sq_nonneg _)
  -- Hence each tuple product is summable: bound all factors but `i = 0` by their `ℓ²`-mass.
  have hsum : ∀ α : Fin r → ↥E, Summable (fun m : ℤ => ∏ i, ‖g (α i).1 m‖ ^ 2) := by
    intro α
    refine Summable.of_nonneg_of_le (fun m => Finset.prod_nonneg (fun i _ => sq_nonneg _))
      (fun m => ?_) ((hsq (α ⟨0, hr⟩).1).mul_left
        (∏ i ∈ Finset.univ.erase ⟨0, hr⟩, ∑' j : ℤ, ‖g (α i).1 j‖ ^ 2))
    rw [← Finset.prod_erase_mul Finset.univ (fun i => ‖g (α i).1 m‖ ^ 2) (Finset.mem_univ ⟨0, hr⟩)]
    exact mul_le_mul_of_nonneg_right
      (Finset.prod_le_prod₀ (fun i _ => sq_nonneg _) (fun i _ => hbdd (α i).1 m)) (sq_nonneg _)
  -- Exchange the outer `tsum` with the finite tuple sum.
  rw [Summable.tsum_finsetSum (fun α _ => hsum α)]

end Work.BourgainPlan.IonescuWainger
