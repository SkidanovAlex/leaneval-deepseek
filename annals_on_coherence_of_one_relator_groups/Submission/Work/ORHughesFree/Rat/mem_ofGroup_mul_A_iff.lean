import Mathlib
import Submission.Work.ORHughesFree.Rat.SourceCore
import Submission.Work.ORHughesFree.Rat.Orbit
import Submission.Work.ORHughesFree.Rat.mem_A_mul_ofGroup_iff

namespace Work.ORHughesFree.Rat

/-!
# Left translates of `Rat.A V`: the `Ugen`-criterion

The mirror of `mem_A_mul_ofGroup_iff` for *left* multiplication by a group element.  The bridge
`Psi (φu * x) = single (Ugen u) 1 * Psi x` (a consequence of `Psi_ofGroup`) turns membership of
`φu * x` in `Rat.A V` — which by `Psi_mem_A_iff` is the statement that the support of
`Psi (φu * x)` lies in the `V`-part `NUV V` — into the statement that the *shift* of the support of
`Psi x` by `Ugen u` lies in `NUV V`.

The passage between these two descriptions is the monoid-algebra fact proved below: over `ℕ`
there are no cancellative issues, the coefficient of `single p 1 * z` at `p * q` is at least
`z.coeff q`, so the support of `single p 1 * z` is *exactly* the translate `p * supp z` of the
support of `z` (`coeff_support_single_one_mul`, mirroring `coeff_support_mul_single_one`).

* `coeff_single_one_mul_eq` computes the coefficient of `single p 1 * z` at `r` as the sum of the
  coefficients of `z` at the elements `q` with `p * q = r`;
* `coeff_support_single_one_mul` reads off the support;
* `mem_ofGroup_mul_A_iff` is the statement of the file.
-/

/-- Coefficients of the product with `single p 1` on the left, over `ℕ`: the coefficient at `r` is
the sum of the coefficients of `z` at the elements `q` with `p * q = r`. -/
theorem coeff_single_one_mul_eq {M : Type} [Monoid M] [DecidableEq M]
    (z : MonoidAlgebra ℕ M) (p r : M) :
    (MonoidAlgebra.single p 1 * z).coeff r =
      ∑ q ∈ z.coeff.support, if p * q = r then z.coeff q else 0 := by
  rw [MonoidAlgebra.coeff_mul, MonoidAlgebra.single, MonoidAlgebra.coeff_ofCoeff,
    Finsupp.sum_single_index]
  · rw [Finsupp.sum]
    apply Finset.sum_congr rfl
    intro q _
    simp
  · simp

/-- The support of `single p 1 * z` is the translate `p * q` of the support of `z`.  Since the
coefficients lie in `ℕ`, the coefficient at `p * q` never drops to zero. -/
theorem coeff_support_single_one_mul {M : Type} [Monoid M] [DecidableEq M]
    (z : MonoidAlgebra ℕ M) (p : M) :
    (MonoidAlgebra.single p 1 * z).coeff.support = (z.coeff.support).image (fun q => p * q) := by
  classical
  ext r
  rw [Finsupp.mem_support_iff, Finset.mem_image]
  constructor
  · intro h
    rw [coeff_single_one_mul_eq] at h
    obtain ⟨a, ha, ha'⟩ := Finset.exists_ne_zero_of_sum_ne_zero h
    have hap : p * a = r := by
      by_contra hne
      exact ha' (by rw [if_neg hne])
    exact ⟨a, ha, hap⟩
  · rintro ⟨a, ha, rfl⟩
    rw [coeff_single_one_mul_eq, ← Nat.pos_iff_ne_zero, Finset.sum_pos_iff]
    exact ⟨a, ha, by rw [if_pos rfl]; exact Nat.pos_of_ne_zero (Finsupp.mem_support_iff.mp ha)⟩

/-- **Left translates of `Rat.A V`.**  `φu · x ∈ Rat.A V` iff the whole support of `Psi x`, shifted
by the group letter `Ugen u`, lies in the `V`-part `NUV V` of the free product `U ♮ X`. -/
theorem mem_ofGroup_mul_A_iff {U : Type} [Group U] (V : Subgroup U)
    (x : Work.ORHughesFree.RatU U) (u : U) :
    Work.ORHughesFree.RatU.ofGroup u * x ∈ Work.ORHughesFree.Rat.A V ↔
      ∀ p ∈ (Work.ORHughesFree.Rat.FreeProduct.Psi x).coeff.support,
        Work.ORHughesFree.Rat.FreeProduct.NU.Ugen u * p ∈ Work.ORHughesFree.Rat.Orbit.NUV V := by
  classical
  rw [mem_A_iff_exists, Psi_mem_A_iff V (RatU.ofGroup u * x), NUV_eq_VPart,
    map_mul, FreeProduct.Psi_ofGroup, coeff_support_single_one_mul]
  simp only [Finset.mem_image]
  constructor
  · intro h p hp
    exact h (FreeProduct.NU.Ugen u * p) ⟨p, hp, rfl⟩
  · rintro h q ⟨a, ha, rfl⟩
    exact h a ha

end Work.ORHughesFree.Rat
