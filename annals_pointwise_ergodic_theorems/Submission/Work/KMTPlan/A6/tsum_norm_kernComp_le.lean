/-
# The `ℓ¹` Young inequality for `kernComp`

The kernel of the composition of a bilinear operator with two linear convolutions,

  `kernComp K κ κ' a b = ∑'_{a'} ∑'_{b'} K (a - a') (b - b') * κ a' * κ' b'`
  (`Work.KMTAreas.A7.kernComp`, see `ModelOps`),

is the *fourfold* convolution of `K`, `κ` and `κ'`; in particular its `ℓ¹(ℤ²)`-mass is bounded by
the product of the `ℓ¹`-masses of the three factors ("Young's inequality"):

  `∑' p, ‖kernComp K κ κ' p.1 p.2‖ ≤ (∑' p, ‖K p.1 p.2‖) * (∑' j, ‖κ j‖) * (∑' j, ‖κ' j‖)`.

This is the quantitative companion of `Work.A7.ModelApproxCore_aux.summable_kernComp` and is what
makes the composition of kernels an *isometry-like* operation on `ℓ¹(ℤ²)`, so that the §6
functional calculus `B_{M·(ψ₁⊗ψ₂)}(u,v) = B_M(T_{ψ₁}u, T_{ψ₂}v)` is norm-controlled at the kernel
level.

The proof is Fubini together with the elementary product factorisation of the `ℓ¹`-mass of a
product family.  Write `g p q = ‖K (p - q).1 (p - q).2‖ * (‖κ q.1‖ * ‖κ' q.2‖)`.  Then

* `‖kernComp K κ κ' p.1 p.2‖ ≤ ∑' q, g p q` for every `p` (triangle inequality for `tsum`, after
  evaluating the defining iterated sum as a single sum — `kernComp_eq_tsum`),
* `∑' p, ∑' q, g p q = ∑' z, ‖K z.1.1 z.1.2‖ * (‖κ z.2.1‖ * ‖κ' z.2.2‖)` by `Summable.tsum_prod`
  and the reindexing `(p, q) ↦ (p - q, q)` (`kernCompSubEquiv`),
* and the latter is `(∑' p, ‖K p.1 p.2‖) * (∑' q, ‖κ q.1‖ * ‖κ' q.2‖)` by `Summable.tsum_mul_tsum`,
  with the second factor itself equal to `(∑' j, ‖κ j‖) * (∑' j, ‖κ' j‖)`.
-/
import Mathlib
import Submission.Work.A7.ModelApproxCore_aux.summable_kernComp
import Submission.Work.A7.ModelApproxCore_aux.kernComp_eq_tsum

set_option autoImplicit false
set_option maxHeartbeats 1000000

namespace Work.KMTPlan.A6

open scoped BigOperators

theorem tsum_norm_kernComp_le {K : ℤ → ℤ → ℂ} {κ κ' : ℤ → ℂ}
    (hK : Summable fun p : ℤ × ℤ => ‖K p.1 p.2‖) (hκ : Summable fun j : ℤ => ‖κ j‖)
    (hκ' : Summable fun j : ℤ => ‖κ' j‖) :
    (∑' p : ℤ × ℤ, ‖Work.KMTAreas.A7.kernComp K κ κ' p.1 p.2‖)
      ≤ (∑' p : ℤ × ℤ, ‖K p.1 p.2‖) * (∑' j : ℤ, ‖κ j‖) * (∑' j : ℤ, ‖κ' j‖) := by
  classical
  -- The `ℓ¹`-mass of the product family `(a, b) ↦ κ a * κ' b`.
  have hκκ' : Summable fun q : ℤ × ℤ => ‖κ q.1‖ * ‖κ' q.2‖ :=
    Summable.mul_of_nonneg hκ hκ' (fun _ => norm_nonneg _) (fun _ => norm_nonneg _)
  -- The joint summand family of the fourfold convolution, in independent variables.
  have hH : Summable fun z : (ℤ × ℤ) × (ℤ × ℤ) =>
      ‖K z.1.1 z.1.2‖ * (‖κ z.2.1‖ * ‖κ' z.2.2‖) :=
    Summable.mul_of_nonneg hK hκκ' (fun _ => norm_nonneg _)
      (fun _ => mul_nonneg (norm_nonneg _) (norm_nonneg _))
  -- Reindexing `(p, q) ↦ (p - q, q)` (a bijection) turns it into the family of `kernComp`'s
  -- summands.
  have hHge : Summable fun z : (ℤ × ℤ) × (ℤ × ℤ) =>
      ‖K (z.1 - z.2).1 (z.1 - z.2).2‖ * (‖κ z.2.1‖ * ‖κ' z.2.2‖) :=
    (Equiv.summable_iff Work.A7.ModelApproxCore_aux.kernCompSubEquiv).mpr hH
  -- Fubini: the iterated sum is summable.
  have hiter : Summable fun p : ℤ × ℤ =>
      ∑' q : ℤ × ℤ, ‖K (p - q).1 (p - q).2‖ * (‖κ q.1‖ * ‖κ' q.2‖) := hHge.prod
  -- Pointwise domination of `‖kernComp‖` by the iterated sum.
  have hbound : ∀ p : ℤ × ℤ, ‖Work.KMTAreas.A7.kernComp K κ κ' p.1 p.2‖
      ≤ ∑' q : ℤ × ℤ, ‖K (p - q).1 (p - q).2‖ * (‖κ q.1‖ * ‖κ' q.2‖) := by
    intro p
    -- For fixed `p` the map `q ↦ (p - q, q)` is injective, so the summand norms are summable.
    have hinj : Function.Injective (fun q : ℤ × ℤ => (p - q, q)) := by
      intro q₁ q₂ h
      simpa using congrArg Prod.snd h
    have hp : Summable fun q : ℤ × ℤ =>
        ‖K (p - q).1 (p - q).2‖ * (‖κ q.1‖ * ‖κ' q.2‖) := by
      simpa only [Function.comp_def] using hH.comp_injective hinj
    have hwnorm : Summable fun q : ℤ × ℤ =>
        ‖K (p - q).1 (p - q).2 * κ q.1 * κ' q.2‖ :=
      hp.congr (fun q => by rw [norm_mul, norm_mul, mul_assoc])
    have hw : Summable fun q : ℤ × ℤ =>
        K (p - q).1 (p - q).2 * κ q.1 * κ' q.2 := Summable.of_norm hwnorm
    -- The defining iterated sum of `kernComp` as a single sum over `ℤ × ℤ`.
    rw [Work.A7.ModelApproxCore_aux.kernComp_eq_tsum hK hκ hκ' p.1 p.2]
    calc ‖∑' q : ℤ × ℤ, K (p - q).1 (p - q).2 * κ q.1 * κ' q.2‖
        ≤ ∑' q : ℤ × ℤ, ‖K (p - q).1 (p - q).2 * κ q.1 * κ' q.2‖ :=
          norm_tsum_le_tsum_norm hwnorm
      _ = ∑' q : ℤ × ℤ, ‖K (p - q).1 (p - q).2‖ * (‖κ q.1‖ * ‖κ' q.2‖) := by
          refine tsum_congr (fun q => ?_)
          rw [norm_mul, norm_mul, mul_assoc]
  have hkern : Summable fun p : ℤ × ℤ => ‖Work.KMTAreas.A7.kernComp K κ κ' p.1 p.2‖ :=
    Work.A7.ModelApproxCore_aux.summable_kernComp hK hκ hκ'
  -- The chain of equalities/inequalities.
  calc (∑' p : ℤ × ℤ, ‖Work.KMTAreas.A7.kernComp K κ κ' p.1 p.2‖)
      ≤ ∑' p : ℤ × ℤ, ∑' q : ℤ × ℤ,
          ‖K (p - q).1 (p - q).2‖ * (‖κ q.1‖ * ‖κ' q.2‖) :=
        Summable.tsum_le_tsum hbound hkern hiter
    _ = ∑' z : (ℤ × ℤ) × (ℤ × ℤ),
          ‖K (z.1 - z.2).1 (z.1 - z.2).2‖ * (‖κ z.2.1‖ * ‖κ' z.2.2‖) :=
        hHge.tsum_prod.symm
    _ = ∑' z : (ℤ × ℤ) × (ℤ × ℤ),
          ‖K z.1.1 z.1.2‖ * (‖κ z.2.1‖ * ‖κ' z.2.2‖) :=
        Equiv.tsum_eq Work.A7.ModelApproxCore_aux.kernCompSubEquiv
          (fun w : (ℤ × ℤ) × (ℤ × ℤ) =>
            ‖K w.1.1 w.1.2‖ * (‖κ w.2.1‖ * ‖κ' w.2.2‖))
    _ = (∑' p : ℤ × ℤ, ‖K p.1 p.2‖) * (∑' q : ℤ × ℤ, ‖κ q.1‖ * ‖κ' q.2‖) :=
        (Summable.tsum_mul_tsum hK hκκ' hH).symm
    _ = (∑' p : ℤ × ℤ, ‖K p.1 p.2‖) * ((∑' j : ℤ, ‖κ j‖) * (∑' j : ℤ, ‖κ' j‖)) := by
        rw [← Summable.tsum_mul_tsum hκ hκ' hκκ']
    _ = (∑' p : ℤ × ℤ, ‖K p.1 p.2‖) * (∑' j : ℤ, ‖κ j‖) * (∑' j : ℤ, ‖κ' j‖) := by
        ring

end Work.KMTPlan.A6
