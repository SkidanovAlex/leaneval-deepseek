import Mathlib
import Submission.Theorem36i
import Submission.SieveSupport
import Submission.Commons.Analysis.Asymptotics.tendsto_mul_rpow_mul_log_pow_zero
import Submission.TensorConvergence

open scoped BigOperators Topology
open Filter MeasureTheory

set_option maxHeartbeats 1000000

/-!
# Theorem 3.6(i) with *separate* per-coordinate support bounds

`theorem36_i` (and its `_real` form) control the residue-window product
`∏ᵢ λ_{Fᵢ}(n+hᵢ)λ_{Gᵢ}(n+hᵢ)` under a *single* per-coordinate support bound
`M i` for the pair `(F i, G i)`, with `2 Σᵢ M i < 1`.

In §5.3 of Polymath8a one needs the version of (27) in the paper:
a single support bound `Mᶜ` for the *whole* family (so that the divisor sums
truncate at `D ≥ x^{Mᶜ}`) together with the *separated* error bound whose
exponent is the sum of the individual support radii,

  `σ := Σᵢ (M(Fᵢ) + M(Gᵢ)) < 1`.

This is strictly weaker: applying `theorem36_i_real` with the common bound
`M i := max (M(Fᵢ)) (M(Gᵢ))` requires `2 Σᵢ max(M(Fᵢ),M(Gᵢ)) < 1`, whereas
the separated form only needs `Σᵢ(M(Fᵢ)+M(Gᵢ)) < 1` and a *max* bound that is
much smaller than the sum.  In the sieve application the two boxes `f_{j,·}`
and `f_{j',·}` can be concentrated in *different* coordinates, so the
separated form is the correct one.
-/

namespace Commons.NumberTheory.MaynardSieve

/-- **Polymath8a Theorem 3.6(i) with separated support bounds** (complex form).
`hMc` is the common support bound used to truncate the divisor sums at `D`, and
`hvan` is the explicit vanishing of the `O(x^σ)` error, `σ = Σᵢ(MFᵢ+MGᵢ)`. -/
theorem theorem36_i_sep {k : ℕ} (hk : 1 ≤ k) (H : Fin k → ℕ)
    (hHinj : Function.Injective H)
    (F G : Fin k → ℝ → ℝ) (hcsF : ∀ i, HasCompactSupport (F i))
    (hsmF : ∀ i, ContDiff ℝ (↑(⊤ : ℕ∞)) (F i)) (hcsG : ∀ i, HasCompactSupport (G i))
    (hsmG : ∀ i, ContDiff ℝ (↑(⊤ : ℕ∞)) (G i))
    (MF MG : Fin k → ℝ) (hMFnn : ∀ i, 0 ≤ MF i) (hMGnn : ∀ i, 0 ≤ MG i)
    (hsuppF : ∀ i t, MF i < |t| → F i t = 0)
    (hsuppG : ∀ i t, MG i < |t| → G i t = 0)
    {Mc : ℝ} (hMc : ∀ i t, Mc < |t| → F i t = 0 ∧ G i t = 0)
    (W : ℕ → ℕ) (hW : ∀ x, W x ≠ 0) (w : ℕ → ℕ) (hw : Tendsto w atTop atTop)
    (hsmall : ∀ x p : ℕ, p.Prime → p ≤ w x → p ∣ W x)
    (hlq : Tendsto (fun x : ℕ => Real.log (W x : ℝ) / Real.sqrt (Real.log (x : ℝ)))
      atTop (𝓝 0))
    (D : ℕ → ℕ) (hD : ∀ᶠ x : ℕ in atTop, (x : ℝ) ^ Mc ≤ (D x : ℝ))
    (b : ℕ → ℕ) (hbW : ∀ x i, (b x + H i).Coprime (W x))
    (hvan : Tendsto (fun x : ℕ => (W x : ℝ) * (x : ℝ) ^ ((∑ i, MF i) + (∑ i, MG i) - 1) *
      (Real.log (x : ℝ)) ^ k) atTop (𝓝 0)) :
    ∃ x₀ : ℕ, ∃ ε : ℕ → ℝ, Tendsto ε atTop (𝓝 0) ∧ ∀ x : ℕ, x₀ ≤ x →
      ‖(((windowDivisorProduct F G H (W x) (b x) (D x) x : ℝ)) : ℂ) - mainTarget F G W x‖
        ≤ ε x * mainScale k W x := by
  classical
  obtain ⟨x₀s, εs, hεs, hbd⟩ := goodMainSum_asymptotic (k := k) hk F G hcsF hsmF hcsG hsmG
    W hW w hw hsmall hlq (M := Mc) hMc D hD
  have hBFex : ∀ i, ∃ C, 0 ≤ C ∧ ∀ t, |F i t| ≤ C := fun i =>
    exists_abs_bound_of_hasCompactSupport (F i) (hcsF i) (hsmF i).continuous
  have hBGex : ∀ i, ∃ C, 0 ≤ C ∧ ∀ t, |G i t| ≤ C := fun i =>
    exists_abs_bound_of_hasCompactSupport (G i) (hcsG i) (hsmG i).continuous
  choose BF hBF0 hBF using hBFex
  choose BG hBG0 hBG using hBGex
  set C₀ : ℝ := 2 * 4 ^ (2 * k) * (∏ i, BF i) * (∏ i, BG i) with hC₀
  have hC₀nn : 0 ≤ C₀ := by
    rw [hC₀]
    have h1 : (0:ℝ) ≤ (∏ i, BF i) := Finset.prod_nonneg fun i _ => hBF0 i
    have h2 : (0:ℝ) ≤ (∏ i, BG i) := Finset.prod_nonneg fun i _ => hBG0 i
    have h3 : (0:ℝ) ≤ 4 ^ (2 * k) := by positivity
    exact mul_nonneg (mul_nonneg (mul_nonneg (by norm_num) h3) h1) h2
  obtain ⟨x₀w, hx₀w⟩ := Filter.eventually_atTop.mp
    ((hw.eventually_ge_atTop (2 : ℕ)).and (hw.eventually_gt_atTop (∑ i, H i)))
  refine ⟨max (max x₀s x₀w) 2,
    fun x => εs x + C₀ * (x : ℝ) ^ ((∑ i, MF i) + (∑ i, MG i)) / mainScale k W x, ?_, ?_⟩
  · have hg : Tendsto (fun x : ℕ => C₀ * (x : ℝ) ^ ((∑ i, MF i) + (∑ i, MG i)) /
        mainScale k W x) atTop (𝓝 0) := by
      refine squeeze_zero' (g := fun x : ℕ => C₀ * ((W x : ℝ) *
        (x : ℝ) ^ ((∑ i, MF i) + (∑ i, MG i) - 1) * (Real.log (x : ℝ)) ^ k)) ?_ ?_ ?_
      · filter_upwards [eventually_ge_atTop (2 : ℕ)] with x hx2
        have hms : 0 < mainScale k W x := mainScale_pos (W := W) (x := x) (hW x) hx2 k
        exact div_nonneg (mul_nonneg hC₀nn
          (Real.rpow_nonneg (by positivity) _)) hms.le
      · filter_upwards [eventually_ge_atTop (2 : ℕ)] with x hx2
        exact errRatio_le (W := W) (x := x) (hW x) hx2 k (C := C₀)
          (σ := (∑ i, MF i) + (∑ i, MG i)) hC₀nn
      · have h1 : Tendsto (fun x : ℕ => C₀ * ((W x : ℝ) *
            (x : ℝ) ^ ((∑ i, MF i) + (∑ i, MG i) - 1) * (Real.log (x : ℝ)) ^ k))
            atTop (𝓝 (C₀ * 0)) := hvan.const_mul C₀
        simpa using h1
    simpa using hεs.add hg
  · intro x hx
    have hx2 : 2 ≤ x := le_trans (le_max_right (max x₀s x₀w) 2) hx
    have hx1 : 1 < x := by omega
    have hlog : 0 < Real.log (x : ℝ) := Real.log_pos (by exact_mod_cast hx1)
    have hxs : x₀s ≤ x :=
      le_trans (le_max_left x₀s x₀w) (le_trans (le_max_left (max x₀s x₀w) 2) hx)
    have hxw : x₀w ≤ x :=
      le_trans (le_max_right x₀s x₀w) (le_trans (le_max_left (max x₀s x₀w) 2) hx)
    obtain ⟨hw2, hwd⟩ := hx₀w x hxw
    have hWdiv : ∀ p : ℕ, p.Prime → p ≤ w x → p ∣ W x := fun p hp hle => hsmall x p hp hle
    have hsep : ∀ i j : Fin k, i ≠ j → H j - H i < w x := by
      intro i j hij
      have h1 : H j - H i ≤ H j := Nat.sub_le _ _
      have h2 : H j ≤ ∑ i, H i :=
        Finset.single_le_sum (fun i _ => Nat.zero_le _) (Finset.mem_univ j)
      omega
    have hWx2 : 2 ≤ W x := by
      have h2dvd : 2 ∣ W x := hsmall x 2 Nat.prime_two hw2
      rcases h2dvd with ⟨m, hm⟩
      have : W x ≠ 0 := hW x
      omega
    have hms : 0 < mainScale k W x := mainScale_pos (W := W) (x := x) (hW x) hx2 k
    set gm : ℝ := goodMainSum (k := k) (D := D x) (N := x) (W := W x)
            (fun i d => lamDivWeight (F i) x d) (fun i d => lamDivWeight (G i) x d) with hgm
    set ge : ℝ := goodErrSum (k := k) (D := D x) (N := x) (W := W x) (b := b x) (H := H)
            (fun i d => lamDivWeight (F i) x d) (fun i d => lamDivWeight (G i) x d) with hge
    set g1 : ℝ := goodMainSum (k := k) (D := D x) (N := 1) (W := W x)
            (fun i d => lamDivWeight (F i) x d) (fun i d => lamDivWeight (G i) x d) with hg1
    set MS1 : ℂ := (((1 : ℝ) / (W x : ℝ) : ℝ) : ℂ) *
      (((prefactor W (fun _ => 1) x : ℝ) : ℂ) ^ k *
        ∏ j : Fin k, (∫ t : ℝ in Set.Ioi 0,
          ((deriv (F j) t : ℝ) : ℂ) * ((deriv (G j) t : ℝ) : ℂ))) with hMS1
    have hwin : windowDivisorProduct F G H (W x) (b x) (D x) x = gm + ge := by
      rw [hgm, hge]
      exact windowLambdaProduct_eq_main_add_error (k := k) (D := D x) (N := x) (W := W x)
        (b := b x) (wd := w x) (R := x) (H := H) (F := F) (G := G) hWdiv hHinj (hbW x) hsep
    have key : ∀ (r a p : ℝ) (Z : ℂ),
        (r : ℂ) * ((a : ℂ) * ((p : ℂ) ^ k * Z)) = (((r * a * p ^ k : ℝ)) : ℂ) * Z := by
      intro r a p Z
      rw [Complex.ofReal_mul, Complex.ofReal_mul, Complex.ofReal_pow]
      ring
    have hMT1 : ((x : ℝ) : ℂ) * MS1 = mainTarget F G W x := by
      rw [hMS1]
      rw [key x ((1 : ℝ) / (W x : ℝ)) (prefactor W (fun _ => 1) x)
        (∏ j : Fin k, (∫ t : ℝ in Set.Ioi 0,
          ((deriv (F j) t : ℝ) : ℂ) * ((deriv (G j) t : ℝ) : ℂ)))]
      rw [mainTarget]
      congr 1
      push_cast
      ring
    have hscaled : ‖(((gm : ℝ) : ℂ) - mainTarget F G W x)‖ ≤ εs x * mainScale k W x := by
      rw [hgm]
      have hs := hbd x hxs
      rw [← hMS1, ← hg1] at hs
      have hgx : ((goodMainSum (k := k) (D := D x) (N := x) (W := W x)
            (fun i d => lamDivWeight (F i) x d) (fun i d => lamDivWeight (G i) x d) : ℝ) : ℂ) =
          ((x : ℝ) : ℂ) * ((g1 : ℝ) : ℂ) := by
        rw [hg1, goodMainSum_eq_mul_goodMainSum_one]
        push_cast
        ring
      have hstep : ((goodMainSum (k := k) (D := D x) (N := x) (W := W x)
            (fun i d => lamDivWeight (F i) x d) (fun i d => lamDivWeight (G i) x d) : ℝ) : ℂ) -
            mainTarget F G W x = ((x : ℝ) : ℂ) * (((g1 : ℝ) : ℂ) - MS1) := by
        rw [hgx, ← hMT1]
        ring
      rw [hstep, norm_mul, norm_ofReal_complex, abs_of_nonneg (by positivity : (0:ℝ) ≤ (x:ℝ))]
      calc (x : ℝ) * ‖((g1 : ℝ) : ℂ) - MS1‖
            ≤ (x : ℝ) * (εs x * ((1 : ℝ) / (W x : ℝ)) * (prefactor W (fun _ => 1) x) ^ k) :=
              mul_le_mul_of_nonneg_left hs (by positivity)
        _ = εs x * mainScale k W x := by rw [mainScale]; ring
    have herr := goodErrSum_le_rpow (k := k) (D := D x) (N := x) (W := W x) (b := b x)
      (H := H) (R := x) (F := F) (G := G) (MF := MF) (MG := MG) (BF := BF) (BG := BG)
      hWx2 hx1 hMFnn hMGnn hBF0 hBG0 hBF hBG hsuppF hsuppG
    have herrC : ‖(((ge : ℝ) : ℂ))‖ ≤
        C₀ * (x : ℝ) ^ ((∑ i, MF i) + (∑ i, MG i)) := by
      rw [hge, norm_ofReal_complex]
      refine herr.trans (le_of_eq ?_)
      rw [hC₀, Finset.sum_add_distrib]
    calc ‖(((windowDivisorProduct F G H (W x) (b x) (D x) x : ℝ)) : ℂ) - mainTarget F G W x‖
        = ‖(((gm : ℝ) : ℂ) + ((ge : ℝ) : ℂ) - mainTarget F G W x)‖ := by
            rw [hwin]; push_cast; ring_nf
      _ = ‖(((gm : ℝ) : ℂ) - mainTarget F G W x) + ((ge : ℝ) : ℂ)‖ := by ring_nf
      _ ≤ ‖(((gm : ℝ) : ℂ) - mainTarget F G W x)‖ + ‖((ge : ℝ) : ℂ)‖ := norm_add_le _ _
      _ ≤ εs x * mainScale k W x + C₀ * (x : ℝ) ^ ((∑ i, MF i) + (∑ i, MG i)) :=
            add_le_add hscaled herrC
      _ = (εs x + C₀ * (x : ℝ) ^ ((∑ i, MF i) + (∑ i, MG i)) / mainScale k W x) *
            mainScale k W x := by
          rw [add_mul, div_mul_cancel₀ _ (ne_of_gt hms)]

/-- **Polymath8a Theorem 3.6(i), separated support bounds, unconditional form**:
the error term `O(x^σ)`, `σ = Σᵢ(MFᵢ+MGᵢ)`, vanishes against the main term as soon as
`σ < 1` and `log W(x) = o(√(log x))`. -/
theorem theorem36_i_sep_uncond {k : ℕ} (hk : 1 ≤ k) (H : Fin k → ℕ)
    (hHinj : Function.Injective H)
    (F G : Fin k → ℝ → ℝ) (hcsF : ∀ i, HasCompactSupport (F i))
    (hsmF : ∀ i, ContDiff ℝ (↑(⊤ : ℕ∞)) (F i)) (hcsG : ∀ i, HasCompactSupport (G i))
    (hsmG : ∀ i, ContDiff ℝ (↑(⊤ : ℕ∞)) (G i))
    (MF MG : Fin k → ℝ) (hMFnn : ∀ i, 0 ≤ MF i) (hMGnn : ∀ i, 0 ≤ MG i)
    (hsuppF : ∀ i t, MF i < |t| → F i t = 0)
    (hsuppG : ∀ i t, MG i < |t| → G i t = 0)
    (hσ : (∑ i, MF i) + (∑ i, MG i) < 1)
    {Mc : ℝ} (hMc : ∀ i t, Mc < |t| → F i t = 0 ∧ G i t = 0)
    (W : ℕ → ℕ) (hW : ∀ x, W x ≠ 0) (w : ℕ → ℕ) (hw : Tendsto w atTop atTop)
    (hsmall : ∀ x p : ℕ, p.Prime → p ≤ w x → p ∣ W x)
    (hlq : Tendsto (fun x : ℕ => Real.log (W x : ℝ) / Real.sqrt (Real.log (x : ℝ)))
      atTop (𝓝 0))
    (D : ℕ → ℕ) (hD : ∀ᶠ x : ℕ in atTop, (x : ℝ) ^ Mc ≤ (D x : ℝ))
    (b : ℕ → ℕ) (hbW : ∀ x i, (b x + H i).Coprime (W x)) :
    ∃ x₀ : ℕ, ∃ ε : ℕ → ℝ, Tendsto ε atTop (𝓝 0) ∧ ∀ x : ℕ, x₀ ≤ x →
      ‖(((windowDivisorProduct F G H (W x) (b x) (D x) x : ℝ)) : ℂ) - mainTarget F G W x‖
        ≤ ε x * mainScale k W x :=
  theorem36_i_sep hk H hHinj F G hcsF hsmF hcsG hsmG MF MG hMFnn hMGnn hsuppF hsuppG hMc
    W hW w hw hsmall hlq D hD b hbW
    (Commons.Analysis.Asymptotics.tendsto_mul_rpow_mul_log_pow_zero hσ k hlq)

end Commons.NumberTheory.MaynardSieve
