import Mathlib

set_option maxHeartbeats 1000000

namespace Work.KMTAreas.A7

open MeasureTheory
open scoped BigOperators ENNReal

noncomputable section

/-- **The coset-reproduction identity for a convolution family.**  `K` is a reproducing kernel
whose coset spread is bounded by `A` (in the `ℝ≥0∞`-form, which also gives the summability of the
coset families), `κ` is an `ℓ¹` sequence reproduced by `K` from *every* coset `qℤ + r₀`, and `hh`
is an arbitrary bounded sequence.  Then the convolution `Ξ x = ∑'_j κ j * hh (x - j)` is
reproduced by `K` from the single coset `qℤ + c'`. -/
theorem convCosetRepIdentityBdd (q : ℕ) (hq : 0 < q) (c' : ℤ) (K : ℤ → ℂ) (κ hh : ℤ → ℂ)
    (A B : ℝ) (hA : 0 ≤ A)
    (hKspread : ∀ d : ℤ, (∑' u : ℤ, ‖K (q * u + d)‖ₑ) ≤ ENNReal.ofReal A)
    (hκ : Summable (fun j : ℤ => ‖κ j‖))
    (hrep : ∀ r₀ j : ℤ, κ j = ∑' m : ℤ, K (j - (q * m + r₀)) * κ (q * m + r₀))
    (hhb : ∀ z : ℤ, ‖hh z‖ ≤ B) :
    ∀ x : ℤ, (∑' j : ℤ, κ j * hh (x - j))
      = ∑' m : ℤ, K (x - (q * m + c')) * (∑' j : ℤ, κ j * hh (q * m + c' - j)) := by
  intro x
  have hB0 : 0 ≤ B := le_trans (norm_nonneg (hh 0)) (hhb 0)
  -- summability of the coset family of the kernel, from the `ℝ≥0∞`-bound
  have hKs : Summable (fun u : ℤ => ‖K (q * u + (x - c'))‖) := by
    refine summable_of_sum_le (c := A) (fun u => norm_nonneg _) (fun s => ?_)
    have h1 : ∑ u ∈ s, ‖K (q * u + (x - c'))‖ₑ ≤ ENNReal.ofReal A :=
      le_trans (ENNReal.sum_le_tsum s) (hKspread (x - c'))
    have h2 : (∑ u ∈ s, ‖K (q * u + (x - c'))‖ₑ).toReal
        = ∑ u ∈ s, ‖K (q * u + (x - c'))‖ := by
      rw [show (∑ u ∈ s, ‖K (q * u + (x - c'))‖ₑ)
            = ∑ u ∈ s, ENNReal.ofReal ‖K (q * u + (x - c'))‖ from
          Finset.sum_congr rfl (fun u _ => (ofReal_norm _).symm)]
      rw [ENNReal.toReal_sum (fun u _ => ENNReal.ofReal_ne_top)]
      exact Finset.sum_congr rfl (fun u _ => ENNReal.toReal_ofReal (norm_nonneg _))
    have h3 : (∑ u ∈ s, ‖K (q * u + (x - c'))‖ₑ).toReal ≤ A := by
      have h4 := ENNReal.toReal_mono ENNReal.ofReal_ne_top h1
      rwa [ENNReal.toReal_ofReal hA] at h4
    rw [← h2]
    exact h3
  have hKs' : Summable (fun m : ℤ => ‖K (x - q * m - c')‖) := by
    have h1 : (fun m : ℤ => ‖K (q * (-m) + (x - c'))‖) = fun m => ‖K (x - q * m - c')‖ := by
      funext m
      have h2 : q * (-m) + (x - c') = x - q * m - c' := by ring
      rw [h2]
    rw [← h1]
    exact (Equiv.summable_iff (Equiv.neg ℤ)).mpr hKs
  have hKmaj : Summable (fun m : ℤ => B * ‖K (x - (q * m + c'))‖) := by
    refine (hKs'.mul_left B).congr (fun m => ?_)
    have h2 : x - q * m - c' = x - (q * m + c') := by ring
    rw [h2]
  have hT : Summable (fun p : ℤ × ℤ => ‖κ p.1‖ * (B * ‖K (x - (q * p.2 + c'))‖)) :=
    Summable.mul_of_nonneg hκ hKmaj (fun _ => norm_nonneg _)
      (fun _ => mul_nonneg hB0 (norm_nonneg _))
  -- the shear `(l,m) ↦ (q*m+c'-l, m)`
  let e : ℤ × ℤ ≃ ℤ × ℤ :=
    { toFun := fun p => (q * p.2 + c' - p.1, p.2)
      invFun := fun p => (q * p.2 + c' - p.1, p.2)
      left_inv := fun p => by
        have h1 : q * p.2 + c' - (q * p.2 + c' - p.1) = p.1 := by ring
        exact Prod.ext h1 rfl
      right_inv := fun p => by
        have h1 : q * p.2 + c' - (q * p.2 + c' - p.1) = p.1 := by ring
        exact Prod.ext h1 rfl }
  have hshear : Summable ((fun p : ℤ × ℤ => ‖κ p.1‖ * (B * ‖K (x - (q * p.2 + c'))‖)) ∘ e) :=
    (Equiv.summable_iff e).mpr hT
  -- the double family
  set F : ℤ × ℤ → ℂ := fun p =>
    K (x - (q * p.2 + c')) * κ (q * p.2 + c' - p.1) * hh p.1 with hFdef
  have hF : Summable F := by
    refine Summable.of_norm_bounded hshear (fun p => ?_)
    have harg : (e p).1 = q * p.2 + c' - p.1 := rfl
    have harg2 : (e p).2 = p.2 := rfl
    rw [Function.comp_apply, harg, harg2, norm_mul, norm_mul]
    have h1 : ‖hh p.1‖ ≤ B := hhb p.1
    have h2 : 0 ≤ ‖K (x - (q * p.2 + c'))‖ := norm_nonneg _
    have h3 : 0 ≤ ‖κ (q * p.2 + c' - p.1)‖ := norm_nonneg _
    calc ‖K (x - (q * p.2 + c'))‖ * ‖κ (q * p.2 + c' - p.1)‖ * ‖hh p.1‖
        ≤ ‖K (x - (q * p.2 + c'))‖ * ‖κ (q * p.2 + c' - p.1)‖ * B :=
          mul_le_mul_of_nonneg_left h1 (mul_nonneg h2 h3)
      _ = ‖κ (q * p.2 + c' - p.1)‖ * (B * ‖K (x - (q * p.2 + c'))‖) := by ring
  have hFswap : Summable (fun p : ℤ × ℤ => F p.swap) :=
    (Equiv.summable_iff (Equiv.prodComm ℤ ℤ)).mpr hF
  have hswap : (∑' p : ℤ × ℤ, F p.swap) = ∑' p : ℤ × ℤ, F p :=
    Equiv.tsum_eq (Equiv.prodComm ℤ ℤ) F
  -- the identity
  have hstep : (∑' j : ℤ, κ j * hh (x - j)) = ∑' l : ℤ, κ (x - l) * hh l := by
    rw [← Equiv.tsum_eq (Equiv.subLeft x) (fun j : ℤ => κ j * hh (x - j))]
    refine tsum_congr (fun l => ?_)
    rw [Equiv.subLeft_apply]
    congr 2
    ring
  have hrep' : ∀ l : ℤ, κ (x - l) = ∑' m : ℤ, K (x - (q * m + c')) * κ (q * m + c' - l) := by
    intro l
    have h := hrep (c' - l) (x - l)
    rw [h]
    refine tsum_congr (fun m => ?_)
    rw [show (x - l) - (q * m + (c' - l)) = x - (q * m + c') by ring,
      show q * m + (c' - l) = q * m + c' - l by ring]
  have hA' : (∑' l : ℤ, κ (x - l) * hh l)
      = ∑' p : ℤ × ℤ, F p := by
    calc (∑' l : ℤ, κ (x - l) * hh l)
        = ∑' l : ℤ, (∑' m : ℤ, K (x - (q * m + c')) * κ (q * m + c' - l)) * hh l :=
          tsum_congr (fun l => by rw [hrep' l])
      _ = ∑' l : ℤ, ∑' m : ℤ, K (x - (q * m + c')) * κ (q * m + c' - l) * hh l := by
          refine tsum_congr (fun l => ?_)
          rw [tsum_mul_right]
      _ = ∑' p : ℤ × ℤ, F p := (hF.tsum_prod).symm
  have hB' : (∑' m : ℤ, K (x - (q * m + c')) * (∑' j : ℤ, κ j * hh (q * m + c' - j)))
      = ∑' p : ℤ × ℤ, F p := by
    calc (∑' m : ℤ, K (x - (q * m + c')) * (∑' j : ℤ, κ j * hh (q * m + c' - j)))
        = ∑' m : ℤ, ∑' j : ℤ, K (x - (q * m + c')) * (κ j * hh (q * m + c' - j)) :=
          tsum_congr (fun m => (tsum_mul_left (a := K (x - (q * m + c')))
            (f := fun j : ℤ => κ j * hh (q * m + c' - j))).symm)
      _ = ∑' m : ℤ, ∑' l : ℤ, F (l, m) := by
          refine tsum_congr (fun m => ?_)
          rw [← Equiv.tsum_eq (Equiv.subLeft (q * m + c'))
            (fun j : ℤ => K (x - (q * m + c')) * (κ j * hh (q * m + c' - j)))]
          refine tsum_congr (fun l => ?_)
          rw [Equiv.subLeft_apply]
          have h2 : q * m + c' - (q * m + c' - l) = l := by ring
          rw [h2, hFdef]
          ring
      _ = ∑' p : ℤ × ℤ, F p := by
          rw [show (∑' m : ℤ, ∑' l : ℤ, F (l, m))
                = ∑' (b : ℤ) (c : ℤ), F ((b, c).swap) from by
              refine tsum_congr (fun b => tsum_congr (fun c => ?_))
              rfl]
          rw [← Summable.tsum_prod hFswap, hswap]
  rw [hstep, hA', hB']

end

end Work.KMTAreas.A7
