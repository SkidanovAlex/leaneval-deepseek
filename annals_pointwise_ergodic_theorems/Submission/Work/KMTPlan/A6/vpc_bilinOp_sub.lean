/-
# Linearity of the bilinear convolution operator in its kernel

`Work.KMTAreas.A7.bilinOp K u v x = ∑'_a ∑'_b K a b * u (x - a) * v (x - b)` is the bilinear
convolution operator with kernel `K : ℤ → ℤ → ℂ` (`ModelOps.lean`).  This file proves that, for two
kernels with summable (i.e. `ℓ¹(ℤ²)`) norm and two bounded functions `u`, `v`, it is **additive in
the kernel**:

  `bilinOp K u v x - bilinOp L u v x = bilinOp (K - L) u v x`.

This is *not* a definitional identity for Mathlib's unconditional `tsum` (which takes the junk value
`0` on non-summable families), so it has to be derived from summability: if `K`, `L ∈ ℓ¹(ℤ²)` and
`u`, `v` are bounded then the product families
`p ↦ K p.1 p.2 * u (x - p.1) * v (x - p.2)` and `p ↦ L p.1 p.2 * u (x - p.1) * v (x - p.2)` are
absolutely summable (`vpc_summable_mul_of_kernel`, by comparison with `‖K p.1 p.2‖ * (Cu * Cv)`),
so

* the iterated sum may be replaced by the sum over the product `ℤ × ℤ`
  (`Work.A7.ModelApproxCore_aux.bilinOp_eq_tsum`, Fubini for absolutely summable families), and
* `Summable.tsum_sub` applies at the level of the product family.

The proof of the product form and the difference of the two products are then glued by a `calc`
chain of four steps: the two Fubini identities (for `K` and `L`), `tsum_sub` for the product family,
and `tsum_congr` with the factorization `(K - L) * u * v = K * u * v - L * u * v` of the summand.

*Elaboration note.*  The statements of `bilinOp_eq_tsum` have all of `K, u, v, Cᵤ, Cᵥ` implicit;
leaving them to be inferred by unification against an expected type that again mentions `∑'` makes
the elaborator spend a very large number of heartbeats (it timed out at `10^6` heartbeats before
being written with explicit arguments).  Every application below therefore names its implicit
arguments explicitly, which reduces the whole file to a fraction of the default heartbeat budget.
-/
import Mathlib
import Submission.Work.A7.ModelApproxCore_aux.bilinOp_eq_tsum

open scoped BigOperators

namespace Work.KMTPlan.A6

/-- The product family of an `ℓ¹(ℤ²)` kernel against two bounded functions is absolutely
summable: it is dominated by `p ↦ ‖K p.1 p.2‖ * (Cu * Cv)`. -/
private theorem vpc_summable_mul_of_kernel {K : ℤ → ℤ → ℂ} {u v : ℤ → ℂ} {Cu Cv : ℝ}
    (hK : Summable fun p : ℤ × ℤ => ‖K p.1 p.2‖) (hu : ∀ y : ℤ, ‖u y‖ ≤ Cu)
    (hv : ∀ y : ℤ, ‖v y‖ ≤ Cv) (x : ℤ) :
    Summable fun p : ℤ × ℤ => K p.1 p.2 * u (x - p.1) * v (x - p.2) := by
  have hCu : 0 ≤ Cu := le_trans (norm_nonneg _) (hu 0)
  have hCv : 0 ≤ Cv := le_trans (norm_nonneg _) (hv 0)
  refine Summable.of_norm_bounded (hK.mul_right (Cu * Cv)) (fun p => ?_)
  rw [norm_mul, norm_mul]
  have h1 : ‖K p.1 p.2‖ * ‖u (x - p.1)‖ ≤ ‖K p.1 p.2‖ * Cu :=
    mul_le_mul_of_nonneg_left (hu _) (norm_nonneg _)
  have h2 : ‖K p.1 p.2‖ * ‖u (x - p.1)‖ * ‖v (x - p.2)‖ ≤ ‖K p.1 p.2‖ * Cu * Cv :=
    mul_le_mul h1 (hv _) (norm_nonneg _) (mul_nonneg (norm_nonneg _) hCu)
  calc ‖K p.1 p.2‖ * ‖u (x - p.1)‖ * ‖v (x - p.2)‖ ≤ ‖K p.1 p.2‖ * Cu * Cv := h2
    _ = ‖K p.1 p.2‖ * (Cu * Cv) := by ring

/-- The difference of the two absolutely summable product families is the product family of the
difference kernel, at the level of the sums over the product index `ℤ × ℤ`. -/
private theorem vpc_tsum_sub_prod {F G : ℤ × ℤ → ℂ} (hF : Summable F) (hG : Summable G) :
    (∑' p, F p) - (∑' p, G p) = ∑' p, (F p - G p) := (Summable.tsum_sub hF hG).symm

/-- **Linearity of `bilinOp` in its kernel.**  For two `ℓ¹(ℤ²)` kernels `K`, `L` and two bounded
functions `u`, `v`, the bilinear convolution with the difference kernel `K − L` is the difference of
the two bilinear convolutions. -/
theorem vpc_bilinOp_sub {K L : ℤ → ℤ → ℂ} {u v : ℤ → ℂ} {Cu Cv : ℝ}
    (hK : Summable fun p : ℤ × ℤ => ‖K p.1 p.2‖)
    (hL : Summable fun p : ℤ × ℤ => ‖L p.1 p.2‖)
    (hu : ∀ a : ℤ, ‖u a‖ ≤ Cu) (hv : ∀ b : ℤ, ‖v b‖ ≤ Cv) (x : ℤ) :
    Work.KMTAreas.A7.bilinOp K u v x - Work.KMTAreas.A7.bilinOp L u v x
      = Work.KMTAreas.A7.bilinOp (fun a b => K a b - L a b) u v x := by
  have hsumK := vpc_summable_mul_of_kernel (K := K) (u := u) (v := v) (Cu := Cu) (Cv := Cv)
    hK hu hv x
  have hsumL := vpc_summable_mul_of_kernel (K := L) (u := u) (v := v) (Cu := Cu) (Cv := Cv)
    hL hu hv x
  have hD : Summable fun p : ℤ × ℤ => ‖K p.1 p.2 - L p.1 p.2‖ :=
    Summable.of_nonneg_of_le (fun p => norm_nonneg _) (fun p => norm_sub_le _ _) (hK.add hL)
  have h1 : Work.KMTAreas.A7.bilinOp K u v x
      = ∑' p : ℤ × ℤ, K p.1 p.2 * u (x - p.1) * v (x - p.2) :=
    Work.A7.ModelApproxCore_aux.bilinOp_eq_tsum (K := K) (u := u) (v := v) (Cu := Cu) (Cv := Cv)
      hK hu hv x
  have h2 : Work.KMTAreas.A7.bilinOp L u v x
      = ∑' p : ℤ × ℤ, L p.1 p.2 * u (x - p.1) * v (x - p.2) :=
    Work.A7.ModelApproxCore_aux.bilinOp_eq_tsum (K := L) (u := u) (v := v) (Cu := Cu) (Cv := Cv)
      hL hu hv x
  have h3 : Work.KMTAreas.A7.bilinOp (fun a b => K a b - L a b) u v x
      = ∑' p : ℤ × ℤ, (K p.1 p.2 - L p.1 p.2) * u (x - p.1) * v (x - p.2) :=
    Work.A7.ModelApproxCore_aux.bilinOp_eq_tsum
      (K := fun a b => K a b - L a b) (u := u) (v := v) (Cu := Cu) (Cv := Cv) hD hu hv x
  have hsub : (∑' p : ℤ × ℤ, K p.1 p.2 * u (x - p.1) * v (x - p.2))
      - (∑' p : ℤ × ℤ, L p.1 p.2 * u (x - p.1) * v (x - p.2))
      = ∑' p : ℤ × ℤ, (K p.1 p.2 * u (x - p.1) * v (x - p.2)
          - L p.1 p.2 * u (x - p.1) * v (x - p.2)) :=
    vpc_tsum_sub_prod hsumK hsumL
  have hcongr : (∑' p : ℤ × ℤ, (K p.1 p.2 * u (x - p.1) * v (x - p.2)
          - L p.1 p.2 * u (x - p.1) * v (x - p.2)))
      = ∑' p : ℤ × ℤ, (K p.1 p.2 - L p.1 p.2) * u (x - p.1) * v (x - p.2) :=
    tsum_congr fun p => by ring
  calc Work.KMTAreas.A7.bilinOp K u v x - Work.KMTAreas.A7.bilinOp L u v x
      = (∑' p : ℤ × ℤ, K p.1 p.2 * u (x - p.1) * v (x - p.2))
        - (∑' p : ℤ × ℤ, L p.1 p.2 * u (x - p.1) * v (x - p.2)) := by rw [h1, h2]
    _ = ∑' p : ℤ × ℤ, (K p.1 p.2 * u (x - p.1) * v (x - p.2)
          - L p.1 p.2 * u (x - p.1) * v (x - p.2)) := hsub
    _ = ∑' p : ℤ × ℤ, (K p.1 p.2 - L p.1 p.2) * u (x - p.1) * v (x - p.2) := hcongr
    _ = Work.KMTAreas.A7.bilinOp (fun a b => K a b - L a b) u v x := h3.symm

end Work.KMTPlan.A6
