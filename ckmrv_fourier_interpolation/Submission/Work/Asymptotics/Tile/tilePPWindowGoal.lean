/-
# The tile principal-part window `Work.Asymptotics.TilePPWindow` (ckmrv_fourier_interpolation)

Target: for `w` in the cusp-`0` neighbourhood `E = KEpsilon`, `n = ±1`, `t ∈ [Im w / 2, 1]`,

  `‖Kaxis (Kfun ℓ d) (n +ᵥ w) t - (n/(2π)) · ((i t - w)⁻¹)‖ ≤ C (scale w)^N`.

## Route

The window splits at the translate pole `ζ = w = (n +ᵥ w) - n`:

* `i t ≠ w`: the *unguarded* window bound `Work.Asymptotics.TileWindow.tile_pp_window_full`
  (proved in `Submission/Work/Asymptotics/TileWindow/tile_pp_spike.lean` as the conjunction of
  the cone-separated bound `offspike_window_bound` and the maximum-modulus spike bound
  `tilePPWindowSpike`);
* `i t = w`: there the principal part is the junk value `0` and the target is the *coincidence*
  value `‖Kaxis (Kfun ℓ d) (n +ᵥ w) w.im‖`, which is what `tilePPWindow_coincidence` below
  provides.  At the coincidence `w ∈ DomainD` and `j w = j (i t)` force `w = i t`
  (`MiddleRange.eq_or_eq_S_of_re_eq_zero`; the `S • w` branch is excluded because it gives
  `t = (S • w).im ≥ 2 > 1`), so the value is the translated *diagonal* one: `Kfun ℓ d (n+ᵥw) w`.

At the translated coincidence `j ((n+ᵥw)) = j w` the kernel is evaluated with `0⁻¹ = 0`: `K⁻ = 0`
and `Kfun = K⁺/2`, and `MiddleRange.UpsilonPlus24_entry_of_coincidence` writes every entry of
`Υ₊^{(24)}` as `(c₀ Δ z)⁻¹ f_k(τ) M_{kj}(j τ) f_k'(z)`; the middle column of `M` vanishes, which
kills the `f₂ = E₁₄/Δ` term (the only source of an exponentially small `Δ(z)⁻¹`).  Clearing the
remaining `Δ(w)` with `Δ·j = E₄³` leaves the explicit expression

  `c₀ Δ(w) K⁺(τ,w) = w² ( 6 E₄²E₆ (E₄ - (E₂|₂S)²) τ + φ₀(τ)(-12E₄³(E₄-(E₂|₂S)²) + 1728Δ(5E₄-7(E₂|₂S)²))
                          + 6 E₄E₆ (E₄-(E₂|₂S)²) φ₂(τ) )`,

which the cusp bounds at height `t ≤ 1` (`norm_Eisenstein_imagAxis_atZero`, `MFix`) estimate by
`C (scale w)^{18} ‖Δ w‖`; dividing by `c₀Δ(w)` gives the claim.
-/
import Mathlib
import Submission.Work.Asymptotics.Tile.tileLayerDefs
import Submission.Work.Asymptotics.TileWindow.tile_pp_spike
import Submission.Work.Asymptotics.MiddleRange.Classify
import Submission.Work.Asymptotics.MiddleRange.exists_bound_Kfun_of_coincidence
import Submission.Work.Asymptotics.Funnel_Kfun_diag_bound
import Submission.Work.Asymptotics.MFix.KXiDefs
import Submission.Work.Asymptotics.norm_Eisenstein_imagAxis_atZero
import Submission.Work.Kernels.KernelFacts.KPlus_T2

noncomputable section

namespace Work.Asymptotics.Tile

open Work.Kernels UpperHalfPlane ModularGroup
open scoped MatrixGroups

/-! ## Elementary `T`-invariance by `±1` -/

/-- If `F` is invariant under `τ ↦ τ + 1`, it is invariant under `τ ↦ τ + n` for `n = ±1`. -/
private lemma vadd_int_one {F : ℍ → ℂ} (h : ∀ τ, F ((1 : ℝ) +ᵥ τ) = F τ) (n : ℤ)
    (hn : n = 1 ∨ n = -1) (τ : ℍ) : F ((n : ℝ) +ᵥ τ) = F τ := by
  rcases hn with rfl | rfl
  · simpa using h τ
  · have h3 := h ((-1 : ℝ) +ᵥ τ)
    rw [← add_vadd] at h3
    simpa using h3.symm

private lemma jInv_vadd_int (n : ℤ) (hn : n = 1 ∨ n = -1) (τ : ℍ) :
    jInvariantFun ((n : ℝ) +ᵥ τ) = jInvariantFun τ :=
  vadd_int_one (fun τ => KernelFacts.jInvariantFun_vadd_one τ) n hn τ

/-- `Δ · j = E₄³`. -/
private lemma Delta_mul_j (w : ℍ) : DeltaFun w * jInvariantFun w = E4Fun w ^ 3 := by
  have h : DeltaFun w ≠ 0 := ClassicalFacts.DeltaFun_ne_zero w
  rw [jInvariantFun]
  field_simp

private lemma c0_ne_zero : Work.Asymptotics.c0 ≠ 0 := by
  rw [Work.Asymptotics.c0, c1728]
  exact mul_ne_zero
    (mul_ne_zero (mul_ne_zero (by norm_num) (by norm_num))
      (zpow_ne_zero _ (Complex.ofReal_ne_zero.mpr Real.pi_ne_zero))) Complex.I_ne_zero

/-! ## The explicit value of `K⁺` at the translated coincidence -/

/-- The `(i,j)` entry of `Υ₊^{(24)}(τ,w)` at a coincidence, cleared of the prefactor. -/
private lemma c0_mul_Delta_mul_Upsilon24 (w : ℍ) (n : ℤ) (hn : n = 1 ∨ n = -1) (i j : Fin 3) :
    Work.Asymptotics.c0 * (DeltaFun w * UpsilonPlus 24 ((n : ℝ) +ᵥ w) w i j)
      = fk (![14, 12, 10] i) w * MiddleRange.Mpos24 (jInvariantFun w) i j
          * fk (![4, 2, 0] j) w := by
  have hjj : jInvariantFun ((n : ℝ) +ᵥ w) = jInvariantFun w := jInv_vadd_int n hn w
  have hfk : fk (![14, 12, 10] i) ((n : ℝ) +ᵥ w) = fk (![14, 12, 10] i) w :=
    vadd_int_one (fun τ => KernelFacts.fk_vadd_one (![14, 12, 10] i) τ) n hn w
  have hΔ : DeltaFun w ≠ 0 := ClassicalFacts.DeltaFun_ne_zero w
  have hc : Work.Asymptotics.c0 * DeltaFun w ≠ 0 := mul_ne_zero c0_ne_zero hΔ
  rw [MiddleRange.UpsilonPlus24_entry_of_coincidence ((n : ℝ) +ᵥ w) w hjj i j, hfk, hjj]
  rw [show Work.Asymptotics.c0 * (DeltaFun w *
        ((Work.Asymptotics.c0 * DeltaFun w)⁻¹ * fk (![14, 12, 10] i) w
          * MiddleRange.Mpos24 (jInvariantFun w) i j * fk (![4, 2, 0] j) w))
      = (Work.Asymptotics.c0 * DeltaFun w)
        * ((Work.Asymptotics.c0 * DeltaFun w)⁻¹
          * (fk (![14, 12, 10] i) w * MiddleRange.Mpos24 (jInvariantFun w) i j
            * fk (![4, 2, 0] j) w)) from by ring,
    ← mul_assoc, mul_inv_cancel₀ hc, one_mul]

/-- `c₀ Δ(w) K⁺^{(24)}(τ,w)` as the cleared sum over the entries. -/
private lemma c0_mul_Delta_mul_KPlus24_vadd (w : ℍ) (n : ℤ) (hn : n = 1 ∨ n = -1) :
    Work.Asymptotics.c0 * (DeltaFun w * KPlus 24 ((n : ℝ) +ᵥ w) w)
      = ∑ i : Fin 3, ∑ j : Fin 3, phiVec ((n : ℝ) +ᵥ w) i
          * (fk (![14, 12, 10] i) w * MiddleRange.Mpos24 (jInvariantFun w) i j
            * fk (![4, 2, 0] j) w) * phitVec w j := by
  have hterm : ∀ i j : Fin 3, Work.Asymptotics.c0 *
      (DeltaFun w * (phiVec ((n : ℝ) +ᵥ w) i
        * UpsilonPlus 24 ((n : ℝ) +ᵥ w) w i j * phitVec w j))
      = phiVec ((n : ℝ) +ᵥ w) i * (fk (![14, 12, 10] i) w
          * MiddleRange.Mpos24 (jInvariantFun w) i j * fk (![4, 2, 0] j) w)
        * phitVec w j := by
    intro i j
    rw [show Work.Asymptotics.c0 * (DeltaFun w * (phiVec ((n : ℝ) +ᵥ w) i
          * UpsilonPlus 24 ((n : ℝ) +ᵥ w) w i j * phitVec w j))
        = phiVec ((n : ℝ) +ᵥ w) i
          * (Work.Asymptotics.c0 * (DeltaFun w * UpsilonPlus 24 ((n : ℝ) +ᵥ w) w i j))
          * phitVec w j from by ring,
      c0_mul_Delta_mul_Upsilon24 w n hn i j]
  rw [KPlus]
  simp only [Finset.mul_sum]
  exact Finset.sum_congr rfl (fun i _ => Finset.sum_congr rfl (fun j _ => hterm i j))

/-- **The explicit value at the translated coincidence.** -/
private lemma c0_mul_Delta_mul_KPlus24_vadd_value (w : ℍ) (n : ℤ) (hn : n = 1 ∨ n = -1) :
    Work.Asymptotics.c0 * (DeltaFun w * KPlus 24 ((n : ℝ) +ᵥ w) w)
      = (w : ℂ) ^ 2 * (
          6 * E4Fun w ^ 2 * E6Fun w * (E4Fun w - E2S w ^ 2) * (((n : ℝ) +ᵥ w : ℍ) : ℂ)
        + phi0 ((n : ℝ) +ᵥ w) * (-12 * E4Fun w ^ 3 * (E4Fun w - E2S w ^ 2)
            + c1728 * DeltaFun w * (5 * E4Fun w - 7 * E2S w ^ 2))
        + phi2 ((n : ℝ) +ᵥ w) * (6 * E4Fun w * E6Fun w * (E4Fun w - E2S w ^ 2))) := by
  rw [c0_mul_Delta_mul_KPlus24_vadd w n hn]
  have hΔ : DeltaFun w ≠ 0 := ClassicalFacts.DeltaFun_ne_zero w
  simp only [Fin.sum_univ_three, Fin.isValue, Int.reduceEq, reduceIte, MiddleRange.Mpos24,
    phiVec, phitVec, fk, phiNeg2, phi0, phi2, E8Fun, E10Fun, E14Fun, c1728, jInvariantFun,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons,
    Matrix.tail_cons, Matrix.of_apply, mul_zero, zero_mul]
  field_simp
  ring

/-! ## Cusp bounds on the imaginary axis below height `1` -/

private lemma ia_coe (s : ℝ) (hs : 0 < s) :
    ((imagAxis s hs : ℍ) : ℂ) = (s : ℂ) * Complex.I := rfl

private lemma ia_im (s : ℝ) (hs : 0 < s) : (imagAxis s hs : ℍ).im = s := by simp [imagAxis]

private lemma ia_norm (s : ℝ) (hs : 0 < s) : ‖((imagAxis s hs : ℍ) : ℂ)‖ = s := by
  rw [ia_coe, norm_mul, Complex.norm_I, mul_one, Complex.norm_real, Real.norm_eq_abs,
    abs_of_pos hs]

private lemma ia_S (t : ℝ) (ht : 0 < t) :
    ModularGroup.S • imagAxis t ht = imagAxis t⁻¹ (inv_pos.mpr ht) :=
  Work.Asymptotics.imagAxis_smul_S t ht

private lemma pi_norm : ‖(Real.pi : ℂ)‖ = Real.pi := by
  rw [Complex.norm_real, Real.norm_of_nonneg Real.pi_pos.le]

/-- `‖E₂‖` at the imaginary axis point `i t`, `t ≤ 1`. -/
private lemma E2_imagAxis_bound :
    ∃ C : ℝ, 0 < C ∧ ∀ (t : ℝ) (ht : 0 < t), t ≤ 1 →
      ‖E2Fun (imagAxis t ht)‖ ≤ C * (t⁻¹) ^ 2 := by
  obtain ⟨A2E, hA2Epos, hA2E⟩ := Work.Asymptotics.MFix.E2Fun_bound
  refine ⟨A2E + 6 / Real.pi, by positivity, fun t ht ht1 => ?_⟩
  have hu : 1 ≤ t⁻¹ := (one_le_inv₀ ht).mpr ht1
  set σ : ℍ := imagAxis t⁻¹ (inv_pos.mpr ht) with hσ
  have hσn : ‖(σ : ℂ)‖ = t⁻¹ := by rw [hσ]; exact ia_norm _ _
  have hσim : 1 ≤ σ.im := by rw [hσ, ia_im]; exact hu
  have hb : ‖E2Fun σ‖ ≤ A2E := hA2E σ hσim
  have hτ : imagAxis t ht = ModularGroup.S • σ := by
    rw [hσ, ← ia_S t ht]
    exact (S_smul_S_smul _).symm
  have heq : E2Fun (imagAxis t ht)
      = (σ : ℂ) ^ 2 * E2Fun σ - 6 * Complex.I * (σ : ℂ) / (Real.pi : ℂ) := by
    rw [hτ]; exact E2Fun_S_smul σ
  have hA : ‖(σ : ℂ) ^ 2 * E2Fun σ‖ = ‖(σ : ℂ)‖ ^ 2 * ‖E2Fun σ‖ := by rw [norm_mul, norm_pow]
  have hB : ‖(6 : ℂ) * Complex.I * (σ : ℂ) / (Real.pi : ℂ)‖ = 6 * ‖(σ : ℂ)‖ / Real.pi := by
    rw [norm_div, pi_norm, norm_mul, norm_mul, Complex.norm_I, mul_one, Complex.norm_ofNat]
  rw [heq]
  calc ‖(σ : ℂ) ^ 2 * E2Fun σ - 6 * Complex.I * (σ : ℂ) / (Real.pi : ℂ)‖
      ≤ ‖(σ : ℂ) ^ 2 * E2Fun σ‖ + ‖(6 : ℂ) * Complex.I * (σ : ℂ) / (Real.pi : ℂ)‖ :=
        norm_sub_le _ _
    _ = ‖(σ : ℂ)‖ ^ 2 * ‖E2Fun σ‖ + 6 * ‖(σ : ℂ)‖ / Real.pi := by rw [hA, hB]
    _ ≤ (t⁻¹) ^ 2 * A2E + 6 * (t⁻¹) / Real.pi := by
        rw [hσn]
        exact add_le_add (mul_le_mul_of_nonneg_left hb (by positivity)) le_rfl
    _ ≤ (A2E + 6 / Real.pi) * (t⁻¹) ^ 2 := by
        have h6 : (6 / Real.pi) * t⁻¹ ≤ (6 / Real.pi) * (t⁻¹) ^ 2 :=
          mul_le_mul_of_nonneg_left (by nlinarith [hu, sq_nonneg t⁻¹]) (by positivity)
        have h2 : 6 * (t⁻¹) / Real.pi = (6 / Real.pi) * t⁻¹ := by ring
        rw [h2]
        nlinarith [h6]

/-- `‖E₄ - (E₂|₂S)²‖` at the imaginary axis point `i t`, `t ≤ 1`. -/
private lemma delta1_imagAxis_bound :
    ∃ C : ℝ, 0 < C ∧ ∀ (t : ℝ) (ht : 0 < t), t ≤ 1 →
      ‖E4Fun (imagAxis t ht) - E2S (imagAxis t ht) ^ 2‖
        ≤ C * (t⁻¹) ^ 4 * ‖DeltaFun (imagAxis t ht)‖ := by
  obtain ⟨cΔ, hcΔpos, hcΔ⟩ := Work.Asymptotics.MFix.DeltaFun_lower
  obtain ⟨Cd, hCdpos, hCd⟩ := Work.Asymptotics.MFix.delta1_isBigOq
  refine ⟨Cd / cΔ, by positivity, fun t ht ht1 => ?_⟩
  have hu : 1 ≤ t⁻¹ := (one_le_inv₀ ht).mpr ht1
  set σ : ℍ := imagAxis t⁻¹ (inv_pos.mpr ht) with hσ
  have hσn : ‖(σ : ℂ)‖ = t⁻¹ := by rw [hσ]; exact ia_norm _ _
  have hσim : 1 ≤ σ.im := by rw [hσ, ia_im]; exact hu
  have hτ : imagAxis t ht = ModularGroup.S • σ := by
    rw [hσ, ← ia_S t ht]
    exact (S_smul_S_smul _).symm
  have hb1 : ‖E4Fun σ - E2Fun σ ^ 2‖ ≤ Cd * ‖qParamFun σ‖ := by simpa using hCd σ hσim
  have hb2 : cΔ * ‖qParamFun σ‖ ≤ ‖DeltaFun σ‖ := hcΔ σ hσim
  have hE4 : E4Fun (imagAxis t ht) = (σ : ℂ) ^ 4 * E4Fun σ := by
    rw [hτ]
    exact KernelFacts.kpc_smul_S_of_slash KernelFacts.kpc_E4_slash_S σ
  have hE2S : E2S (imagAxis t ht) = (σ : ℂ) ^ 2 * E2Fun σ := by
    rw [hτ]; exact TildeFacts.E2S_S_smul σ
  have hD : DeltaFun (imagAxis t ht) = (σ : ℂ) ^ 12 * DeltaFun σ := by
    rw [hτ]
    exact KernelFacts.kpc_smul_S_of_slash KernelFacts.kpc_Delta_slash_S σ
  have hfact : E4Fun (imagAxis t ht) - E2S (imagAxis t ht) ^ 2
      = (σ : ℂ) ^ 4 * (E4Fun σ - E2Fun σ ^ 2) := by
    rw [hE4, hE2S]; ring
  have hDlow : cΔ * (t⁻¹) ^ 12 * ‖qParamFun σ‖ ≤ ‖DeltaFun (imagAxis t ht)‖ := by
    rw [hD, norm_mul, norm_pow, hσn]
    calc cΔ * (t⁻¹) ^ 12 * ‖qParamFun σ‖
        = (t⁻¹) ^ 12 * (cΔ * ‖qParamFun σ‖) := by ring
      _ ≤ (t⁻¹) ^ 12 * ‖DeltaFun σ‖ := mul_le_mul_of_nonneg_left hb2 (by positivity)
  rw [hfact, norm_mul, norm_pow, hσn]
  have step1 : (t⁻¹) ^ 4 * ‖E4Fun σ - E2Fun σ ^ 2‖ ≤ (t⁻¹) ^ 4 * (Cd * ‖qParamFun σ‖) :=
    mul_le_mul_of_nonneg_left hb1 (by positivity)
  have hqle : ‖qParamFun σ‖ ≤ t ^ 12 * ‖DeltaFun (imagAxis t ht)‖ / cΔ := by
    rw [le_div_iff₀ hcΔpos]
    have huu : (t⁻¹) ^ 12 * t ^ 12 = 1 := by
      rw [← mul_pow, inv_mul_cancel₀ (ne_of_gt ht), one_pow]
    have h3 : cΔ * (t⁻¹) ^ 12 * ‖qParamFun σ‖ * t ^ 12 = cΔ * ‖qParamFun σ‖ := by
      calc cΔ * (t⁻¹) ^ 12 * ‖qParamFun σ‖ * t ^ 12
          = cΔ * ‖qParamFun σ‖ * ((t⁻¹) ^ 12 * t ^ 12) := by ring
        _ = cΔ * ‖qParamFun σ‖ * 1 := by rw [huu]
        _ = cΔ * ‖qParamFun σ‖ := by ring
    calc ‖qParamFun σ‖ * cΔ
        = cΔ * (t⁻¹) ^ 12 * ‖qParamFun σ‖ * t ^ 12 := by rw [h3]; ring
      _ ≤ ‖DeltaFun (imagAxis t ht)‖ * t ^ 12 :=
          mul_le_mul_of_nonneg_right hDlow (by positivity)
      _ = t ^ 12 * ‖DeltaFun (imagAxis t ht)‖ := by ring
  calc (t⁻¹) ^ 4 * ‖E4Fun σ - E2Fun σ ^ 2‖
      ≤ (t⁻¹) ^ 4 * (Cd * ‖qParamFun σ‖) := step1
    _ ≤ (t⁻¹) ^ 4 * (Cd * (t ^ 12 * ‖DeltaFun (imagAxis t ht)‖ / cΔ)) := by
        refine mul_le_mul_of_nonneg_left ?_ (by positivity)
        exact mul_le_mul_of_nonneg_left hqle hCdpos.le
    _ ≤ (Cd / cΔ) * (t⁻¹) ^ 4 * ‖DeltaFun (imagAxis t ht)‖ := by
        have ht12 : t ^ 12 ≤ 1 := pow_le_one₀ (le_of_lt ht) ht1
        have hu4 : (0 : ℝ) ≤ (t⁻¹) ^ 4 := by positivity
        have hDn : (0 : ℝ) ≤ ‖DeltaFun (imagAxis t ht)‖ := norm_nonneg _
        have hEq : (t⁻¹) ^ 4 * (Cd * (t ^ 12 * ‖DeltaFun (imagAxis t ht)‖ / cΔ))
            = (Cd / cΔ) * (t⁻¹) ^ 4 * t ^ 12 * ‖DeltaFun (imagAxis t ht)‖ := by ring
        rw [hEq]
        have hmono : (t⁻¹) ^ 4 * t ^ 12 ≤ (t⁻¹) ^ 4 := by
          simpa using mul_le_mul_of_nonneg_left ht12 hu4
        have hK : (0 : ℝ) ≤ Cd / cΔ := by positivity
        nlinarith [hmono, hK, mul_nonneg (mul_nonneg hK hu4) hDn, hDn]

/-! ## The coincidence value for `d = 24` -/

set_option maxHeartbeats 1000000 in
private lemma coin_d24_bound (ℓ : LogLambdaData) :
    ∃ C N : ℝ, 0 ≤ C ∧ 0 ≤ N ∧ ∀ (w : ℍ), w ∈ KEpsilon → w.re = 0 → w.im ≤ 1 →
      ∀ n : ℤ, (n = 1 ∨ n = -1) →
      ‖Kfun ℓ 24 ((n : ℝ) +ᵥ w) w‖ ≤ C * (scale w) ^ N := by
  obtain ⟨A4, hA4pos, hA4⟩ := (norm_Eisenstein_imagAxis_atZero).1
  obtain ⟨A6, hA6pos, hA6⟩ := (norm_Eisenstein_imagAxis_atZero).2.1
  obtain ⟨A2S, hA2Spos, hA2S⟩ := (norm_Eisenstein_imagAxis_atZero).2.2
  obtain ⟨CE, hCEpos, hCE⟩ := E2_imagAxis_bound
  obtain ⟨CD, hCDpos, hCD⟩ := delta1_imagAxis_bound
  set K : ℝ := 12 * A4 ^ 2 * A6 * CD
    + (2 * CE + 3 / Real.pi) * (12 * A4 ^ 3 * CD + 1728 * (5 * A4 + 7 * A2S ^ 2))
    + 6 * A4 * A6 * CD * (2 * CE ^ 2 + 6 * CE / Real.pi) with hK
  have hKpos : 0 < K := by rw [hK]; positivity
  refine ⟨K / (2 * ‖Work.Asymptotics.c0‖), 18, by positivity, by norm_num, ?_⟩
  intro w _hw hre hwim n hn
  have hw_eq : w = imagAxis w.im w.im_pos := Work.Asymptotics.eq_imagAxis_of_re_eq_zero hre
  have hwnorm : ‖(w : ℂ)‖ = w.im := by
    rw [hw_eq, ia_im]
    exact ia_norm w.im w.im_pos
  have hτ2 : ‖(((n : ℝ) +ᵥ w : ℍ) : ℂ)‖ ≤ 2 := by
    have hcoe : (((n : ℝ) +ᵥ w : ℍ) : ℂ) = (n : ℂ) + (w : ℂ) := UpperHalfPlane.coe_vadd _ _
    rw [hcoe]
    have hn1 : ‖(n : ℂ)‖ = 1 := by rcases hn with h | h <;> rw [h] <;> norm_num
    calc ‖(n : ℂ) + (w : ℂ)‖ ≤ ‖(n : ℂ)‖ + ‖(w : ℂ)‖ := norm_add_le _ _
      _ = 1 + w.im := by rw [hn1, hwnorm]
      _ ≤ 2 := by linarith
  set u : ℝ := (w.im)⁻¹ with hu
  have hu0 : (0 : ℝ) ≤ u := by
    rw [hu]; exact le_of_lt (inv_pos.mpr w.im_pos)
  have hu1 : (1 : ℝ) ≤ u := by rw [hu]; exact (one_le_inv₀ w.im_pos).mpr hwim
  have hu_le : u ≤ scale w := by
    rw [hu, scale]
    have := norm_nonneg (w : ℂ); linarith
  have hpow : u ^ 18 ≤ (scale w) ^ 18 := pow_le_pow_left₀ hu0 hu_le 18
  have hwim2 : (w.im) ^ 2 ≤ 1 := by nlinarith [w.im_pos, hwim]
  have hA4w : ‖E4Fun w‖ ≤ A4 * u ^ 4 := by
    have h := hA4 w.im w.im_pos hwim
    rw [← hw_eq] at h
    rw [hu]; simpa only [inv_pow] using h
  have hA6w : ‖E6Fun w‖ ≤ A6 * u ^ 6 := by
    have h := hA6 w.im w.im_pos hwim
    rw [← hw_eq] at h
    rw [hu]; simpa only [inv_pow] using h
  have hA2Sw : ‖E2S w‖ ≤ A2S * u ^ 2 := by
    have h := hA2S w.im w.im_pos hwim
    rw [← hw_eq] at h
    rw [hu]; simpa only [inv_pow] using h
  have hCEw : ‖E2Fun w‖ ≤ CE * u ^ 2 := by
    have h := hCE w.im w.im_pos hwim
    rw [← hw_eq] at h
    rw [hu]; exact h
  have hCDw : ‖E4Fun w - E2S w ^ 2‖ ≤ CD * u ^ 4 * ‖DeltaFun w‖ := by
    have h := hCD w.im w.im_pos hwim
    rw [← hw_eq] at h
    rw [hu]; exact h
  have hDpos : 0 < ‖DeltaFun w‖ := norm_pos_iff.mpr (ClassicalFacts.DeltaFun_ne_zero w)
  have hE2τ : E2Fun ((n : ℝ) +ᵥ w) = E2Fun w :=
    vadd_int_one (fun τ => E2Fun_vadd_one τ) n hn w
  have hE2τb : ‖E2Fun ((n : ℝ) +ᵥ w)‖ ≤ CE * u ^ 2 := by rw [hE2τ]; exact hCEw
  -- the two `φ` bounds at `τ = n +ᵥ w`, where `E₂ (n +ᵥ w) = E₂ w`
  have hPhi0 : ‖phi0 ((n : ℝ) +ᵥ w)‖ ≤ (2 * CE + 3 / Real.pi) * u ^ 2 := by
    have hb : ‖(((n : ℝ) +ᵥ w : ℍ) : ℂ) * E2Fun ((n : ℝ) +ᵥ w)
        - (3 : ℂ) * Complex.I / (Real.pi : ℂ)‖
        ≤ 2 * (CE * u ^ 2) + 3 / Real.pi := by
      have hnorm : ‖(3 : ℂ) * Complex.I / (Real.pi : ℂ)‖ = 3 / Real.pi := by
        rw [norm_div, pi_norm, norm_mul, Complex.norm_I, mul_one, Complex.norm_ofNat]
      calc ‖(((n : ℝ) +ᵥ w : ℍ) : ℂ) * E2Fun ((n : ℝ) +ᵥ w)
            - (3 : ℂ) * Complex.I / (Real.pi : ℂ)‖
          ≤ ‖(((n : ℝ) +ᵥ w : ℍ) : ℂ) * E2Fun ((n : ℝ) +ᵥ w)‖
              + ‖(3 : ℂ) * Complex.I / (Real.pi : ℂ)‖ := norm_sub_le _ _
        _ = ‖(((n : ℝ) +ᵥ w : ℍ) : ℂ)‖ * ‖E2Fun ((n : ℝ) +ᵥ w)‖ + 3 / Real.pi := by
            rw [norm_mul, hnorm]
        _ ≤ 2 * (CE * u ^ 2) + 3 / Real.pi :=
            add_le_add (mul_le_mul hτ2 hE2τb (norm_nonneg _) (by norm_num)) le_rfl
    rw [phi0]
    refine le_trans hb ?_
    have h1 : (1 : ℝ) ≤ u ^ 2 := one_le_pow₀ hu1
    have hA : 2 * CE ≤ 2 * CE * u ^ 2 := by
      simpa using mul_le_mul_of_nonneg_left h1 (by positivity : (0 : ℝ) ≤ 2 * CE)
    have hB : 3 / Real.pi ≤ 3 / Real.pi * u ^ 2 := by
      simpa using mul_le_mul_of_nonneg_left h1 (by positivity : (0 : ℝ) ≤ 3 / Real.pi)
    calc 2 * (CE * u ^ 2) + 3 / Real.pi = 2 * CE * u ^ 2 + 3 / Real.pi := by ring
      _ ≤ 2 * CE * u ^ 2 + 3 / Real.pi * u ^ 2 := add_le_add le_rfl hB
      _ = (2 * CE + 3 / Real.pi) * u ^ 2 := by ring
  have hPhi2 : ‖phi2 ((n : ℝ) +ᵥ w)‖ ≤ (2 * CE ^ 2 + 6 * CE / Real.pi) * u ^ 4 := by
    have hb : ‖(((n : ℝ) +ᵥ w : ℍ) : ℂ) * E2Fun ((n : ℝ) +ᵥ w) ^ 2
        - ((6 : ℂ) * Complex.I / (Real.pi : ℂ)) * E2Fun ((n : ℝ) +ᵥ w)‖
        ≤ 2 * (CE * u ^ 2) ^ 2 + 6 / Real.pi * (CE * u ^ 2) := by
      have h6 : ‖((6 : ℂ) * Complex.I / (Real.pi : ℂ))‖ = 6 / Real.pi := by
        rw [norm_div, pi_norm, norm_mul, Complex.norm_I, mul_one, Complex.norm_ofNat]
      calc ‖(((n : ℝ) +ᵥ w : ℍ) : ℂ) * E2Fun ((n : ℝ) +ᵥ w) ^ 2
            - ((6 : ℂ) * Complex.I / (Real.pi : ℂ)) * E2Fun ((n : ℝ) +ᵥ w)‖
          ≤ ‖(((n : ℝ) +ᵥ w : ℍ) : ℂ) * E2Fun ((n : ℝ) +ᵥ w) ^ 2‖
              + ‖((6 : ℂ) * Complex.I / (Real.pi : ℂ)) * E2Fun ((n : ℝ) +ᵥ w)‖ :=
            norm_sub_le _ _
        _ = ‖(((n : ℝ) +ᵥ w : ℍ) : ℂ)‖ * ‖E2Fun ((n : ℝ) +ᵥ w)‖ ^ 2
              + 6 / Real.pi * ‖E2Fun ((n : ℝ) +ᵥ w)‖ := by
            rw [norm_mul, norm_mul, norm_pow, h6]
        _ ≤ 2 * (CE * u ^ 2) ^ 2 + 6 / Real.pi * (CE * u ^ 2) := by
            refine add_le_add ?_ ?_
            · exact mul_le_mul hτ2 (pow_le_pow_left₀ (norm_nonneg _) hE2τb 2) (by positivity)
                (by norm_num)
            · exact mul_le_mul_of_nonneg_left hE2τb (by positivity)
    rw [phi2]
    refine le_trans hb ?_
    have h1 : u ^ 2 ≤ u ^ 4 := pow_le_pow_right₀ hu1 (by norm_num)
    have hB : 6 / Real.pi * (CE * u ^ 2) ≤ 6 / Real.pi * (CE * u ^ 4) := by
      refine mul_le_mul_of_nonneg_left ?_ (by positivity)
      exact mul_le_mul_of_nonneg_left h1 (le_of_lt hCEpos)
    have hA : 2 * (CE * u ^ 2) ^ 2 = 2 * CE ^ 2 * u ^ 4 := by ring
    calc 2 * (CE * u ^ 2) ^ 2 + 6 / Real.pi * (CE * u ^ 2)
        ≤ 2 * CE ^ 2 * u ^ 4 + 6 / Real.pi * (CE * u ^ 4) := by
          rw [hA]; exact add_le_add le_rfl hB
      _ = (2 * CE ^ 2 + 6 * CE / Real.pi) * u ^ 4 := by ring
  -- the three summands of the explicit expression
  set E1 : ℂ := 6 * E4Fun w ^ 2 * E6Fun w * (E4Fun w - E2S w ^ 2)
    * (((n : ℝ) +ᵥ w : ℍ) : ℂ) with hE1
  set E2 : ℂ := phi0 ((n : ℝ) +ᵥ w) * (-12 * E4Fun w ^ 3 * (E4Fun w - E2S w ^ 2)
    + c1728 * DeltaFun w * (5 * E4Fun w - 7 * E2S w ^ 2)) with hE2
  set E3 : ℂ := phi2 ((n : ℝ) +ᵥ w) * (6 * E4Fun w * E6Fun w * (E4Fun w - E2S w ^ 2)) with hE3
  have hb1 : ‖E1‖ ≤ 12 * A4 ^ 2 * A6 * CD * u ^ 18 * ‖DeltaFun w‖ := by
    rw [hE1]
    have hexp : ‖6 * E4Fun w ^ 2 * E6Fun w * (E4Fun w - E2S w ^ 2)
          * (((n : ℝ) +ᵥ w : ℍ) : ℂ)‖
        = 6 * ‖E4Fun w‖ ^ 2 * ‖E6Fun w‖ * ‖E4Fun w - E2S w ^ 2‖
          * ‖(((n : ℝ) +ᵥ w : ℍ) : ℂ)‖ := by
      simp only [norm_mul, norm_pow, Complex.norm_ofNat]
    rw [hexp]
    have h1 : ‖E4Fun w‖ ^ 2 ≤ (A4 * u ^ 4) ^ 2 := pow_le_pow_left₀ (norm_nonneg _) hA4w 2
    calc 6 * ‖E4Fun w‖ ^ 2 * ‖E6Fun w‖ * ‖E4Fun w - E2S w ^ 2‖
          * ‖(((n : ℝ) +ᵥ w : ℍ) : ℂ)‖
        ≤ 6 * (A4 * u ^ 4) ^ 2 * (A6 * u ^ 6) * (CD * u ^ 4 * ‖DeltaFun w‖) * 2 := by
          gcongr
      _ = 12 * A4 ^ 2 * A6 * CD * u ^ 18 * ‖DeltaFun w‖ := by ring
  have hb3 : ‖E3‖ ≤ 6 * A4 * A6 * CD * (2 * CE ^ 2 + 6 * CE / Real.pi) * u ^ 18
      * ‖DeltaFun w‖ := by
    rw [hE3]
    have hexp : ‖phi2 ((n : ℝ) +ᵥ w) * (6 * E4Fun w * E6Fun w * (E4Fun w - E2S w ^ 2))‖
        = ‖phi2 ((n : ℝ) +ᵥ w)‖ * (6 * ‖E4Fun w‖ * ‖E6Fun w‖
          * ‖E4Fun w - E2S w ^ 2‖) := by
      simp only [norm_mul, norm_pow, Complex.norm_ofNat]
    rw [hexp]
    calc ‖phi2 ((n : ℝ) +ᵥ w)‖ * (6 * ‖E4Fun w‖ * ‖E6Fun w‖ * ‖E4Fun w - E2S w ^ 2‖)
        ≤ ((2 * CE ^ 2 + 6 * CE / Real.pi) * u ^ 4)
            * (6 * (A4 * u ^ 4) * (A6 * u ^ 6) * (CD * u ^ 4 * ‖DeltaFun w‖)) := by
          refine mul_le_mul hPhi2 ?_ (by positivity) (by positivity)
          gcongr
      _ = 6 * A4 * A6 * CD * (2 * CE ^ 2 + 6 * CE / Real.pi) * u ^ 18
            * ‖DeltaFun w‖ := by ring
  have hb2 : ‖E2‖ ≤ (2 * CE + 3 / Real.pi)
      * (12 * A4 ^ 3 * CD + 1728 * (5 * A4 + 7 * A2S ^ 2)) * u ^ 18 * ‖DeltaFun w‖ := by
    rw [hE2]
    have hexp : ‖phi0 ((n : ℝ) +ᵥ w) * (-12 * E4Fun w ^ 3 * (E4Fun w - E2S w ^ 2)
          + c1728 * DeltaFun w * (5 * E4Fun w - 7 * E2S w ^ 2))‖
        = ‖phi0 ((n : ℝ) +ᵥ w)‖ * ‖-12 * E4Fun w ^ 3 * (E4Fun w - E2S w ^ 2)
          + c1728 * DeltaFun w * (5 * E4Fun w - 7 * E2S w ^ 2)‖ := by rw [norm_mul]
    rw [hexp]
    have h5 : ‖(5 : ℂ) * E4Fun w - (7 : ℂ) * E2S w ^ 2‖
        ≤ (5 * A4 + 7 * A2S ^ 2) * u ^ 4 := by
      calc ‖(5 : ℂ) * E4Fun w - (7 : ℂ) * E2S w ^ 2‖
          ≤ ‖(5 : ℂ) * E4Fun w‖ + ‖(7 : ℂ) * E2S w ^ 2‖ := norm_sub_le _ _
        _ = 5 * ‖E4Fun w‖ + 7 * ‖E2S w‖ ^ 2 := by
            rw [norm_mul, norm_mul, norm_pow, Complex.norm_ofNat, Complex.norm_ofNat]
        _ ≤ 5 * (A4 * u ^ 4) + 7 * (A2S * u ^ 2) ^ 2 := by
            refine add_le_add (mul_le_mul_of_nonneg_left hA4w (by norm_num)) ?_
            exact mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (norm_nonneg _) hA2Sw 2)
              (by norm_num)
        _ = (5 * A4 + 7 * A2S ^ 2) * u ^ 4 := by ring
    have hf : ‖-12 * E4Fun w ^ 3 * (E4Fun w - E2S w ^ 2)‖
        ≤ 12 * (A4 * u ^ 4) ^ 3 * (CD * u ^ 4 * ‖DeltaFun w‖) := by
      have hexp : ‖-12 * E4Fun w ^ 3 * (E4Fun w - E2S w ^ 2)‖
          = 12 * (‖E4Fun w‖ ^ 3 * ‖E4Fun w - E2S w ^ 2‖) := by
        simp only [norm_mul, norm_pow, norm_neg, Complex.norm_ofNat]
        ring
      rw [hexp]
      have h1 : ‖E4Fun w‖ ^ 3 ≤ (A4 * u ^ 4) ^ 3 := pow_le_pow_left₀ (norm_nonneg _) hA4w 3
      calc 12 * (‖E4Fun w‖ ^ 3 * ‖E4Fun w - E2S w ^ 2‖)
          ≤ 12 * ((A4 * u ^ 4) ^ 3 * (CD * u ^ 4 * ‖DeltaFun w‖)) := by
            refine mul_le_mul_of_nonneg_left ?_ (by norm_num)
            exact mul_le_mul h1 hCDw (norm_nonneg _) (by positivity)
        _ = 12 * (A4 * u ^ 4) ^ 3 * (CD * u ^ 4 * ‖DeltaFun w‖) := by ring
    have hs : ‖c1728 * DeltaFun w * (5 * E4Fun w - 7 * E2S w ^ 2)‖
        ≤ 1728 * ‖DeltaFun w‖ * ((5 * A4 + 7 * A2S ^ 2) * u ^ 4) := by
      have hexp : ‖c1728 * DeltaFun w * (5 * E4Fun w - 7 * E2S w ^ 2)‖
          = 1728 * ‖DeltaFun w‖ * ‖(5 : ℂ) * E4Fun w - (7 : ℂ) * E2S w ^ 2‖ := by
        simp only [norm_mul, Complex.norm_ofNat, c1728]
      rw [hexp]
      exact mul_le_mul_of_nonneg_left h5 (by positivity)
    have hinner : ‖-12 * E4Fun w ^ 3 * (E4Fun w - E2S w ^ 2)
          + c1728 * DeltaFun w * (5 * E4Fun w - 7 * E2S w ^ 2)‖
        ≤ (12 * A4 ^ 3 * CD * u ^ 16 + 1728 * (5 * A4 + 7 * A2S ^ 2) * u ^ 4)
            * ‖DeltaFun w‖ := by
      calc ‖-12 * E4Fun w ^ 3 * (E4Fun w - E2S w ^ 2)
            + c1728 * DeltaFun w * (5 * E4Fun w - 7 * E2S w ^ 2)‖
          ≤ ‖-12 * E4Fun w ^ 3 * (E4Fun w - E2S w ^ 2)‖
              + ‖c1728 * DeltaFun w * (5 * E4Fun w - 7 * E2S w ^ 2)‖ := norm_add_le _ _
        _ ≤ 12 * (A4 * u ^ 4) ^ 3 * (CD * u ^ 4 * ‖DeltaFun w‖)
              + 1728 * ‖DeltaFun w‖ * ((5 * A4 + 7 * A2S ^ 2) * u ^ 4) := add_le_add hf hs
        _ = (12 * A4 ^ 3 * CD * u ^ 16 + 1728 * (5 * A4 + 7 * A2S ^ 2) * u ^ 4)
              * ‖DeltaFun w‖ := by ring
    calc ‖phi0 ((n : ℝ) +ᵥ w)‖ * ‖-12 * E4Fun w ^ 3 * (E4Fun w - E2S w ^ 2)
          + c1728 * DeltaFun w * (5 * E4Fun w - 7 * E2S w ^ 2)‖
        ≤ ((2 * CE + 3 / Real.pi) * u ^ 2)
            * ((12 * A4 ^ 3 * CD * u ^ 16 + 1728 * (5 * A4 + 7 * A2S ^ 2) * u ^ 4)
              * ‖DeltaFun w‖) :=
          mul_le_mul hPhi0 hinner (norm_nonneg _) (by positivity)
      _ = ((2 * CE + 3 / Real.pi) * (12 * A4 ^ 3 * CD) * u ^ 18
            + (2 * CE + 3 / Real.pi) * (1728 * (5 * A4 + 7 * A2S ^ 2)) * u ^ 6)
            * ‖DeltaFun w‖ := by ring
      _ ≤ ((2 * CE + 3 / Real.pi) * (12 * A4 ^ 3 * CD) * u ^ 18
            + (2 * CE + 3 / Real.pi) * (1728 * (5 * A4 + 7 * A2S ^ 2)) * u ^ 18)
            * ‖DeltaFun w‖ := by
          refine mul_le_mul_of_nonneg_right ?_ (norm_nonneg _)
          refine add_le_add le_rfl ?_
          exact mul_le_mul_of_nonneg_left (pow_le_pow_right₀ hu1 (by norm_num : (6 : ℕ) ≤ 18))
            (by positivity)
      _ = (2 * CE + 3 / Real.pi) * (12 * A4 ^ 3 * CD + 1728 * (5 * A4 + 7 * A2S ^ 2))
            * u ^ 18 * ‖DeltaFun w‖ := by ring
  -- assembling
  have htri : ‖E1 + E2 + E3‖ ≤ ‖E1‖ + ‖E2‖ + ‖E3‖ := by
    calc ‖E1 + E2 + E3‖ ≤ ‖E1 + E2‖ + ‖E3‖ := norm_add_le _ _
      _ ≤ (‖E1‖ + ‖E2‖) + ‖E3‖ := add_le_add (norm_add_le _ _) le_rfl
      _ = ‖E1‖ + ‖E2‖ + ‖E3‖ := by ring
  have hsum : ‖E1‖ + ‖E2‖ + ‖E3‖ ≤ K * u ^ 18 * ‖DeltaFun w‖ := by
    rw [hK]
    calc ‖E1‖ + ‖E2‖ + ‖E3‖
        ≤ 12 * A4 ^ 2 * A6 * CD * u ^ 18 * ‖DeltaFun w‖
          + (2 * CE + 3 / Real.pi) * (12 * A4 ^ 3 * CD + 1728 * (5 * A4 + 7 * A2S ^ 2))
            * u ^ 18 * ‖DeltaFun w‖
          + 6 * A4 * A6 * CD * (2 * CE ^ 2 + 6 * CE / Real.pi) * u ^ 18 * ‖DeltaFun w‖ :=
          add_le_add (add_le_add hb1 hb2) hb3
      _ = (12 * A4 ^ 2 * A6 * CD
            + (2 * CE + 3 / Real.pi) * (12 * A4 ^ 3 * CD + 1728 * (5 * A4 + 7 * A2S ^ 2))
            + 6 * A4 * A6 * CD * (2 * CE ^ 2 + 6 * CE / Real.pi)) * u ^ 18 * ‖DeltaFun w‖ := by
          ring
  have hbig : ‖Work.Asymptotics.c0 * (DeltaFun w * KPlus 24 ((n : ℝ) +ᵥ w) w)‖
      ≤ K * (scale w) ^ 18 * ‖DeltaFun w‖ := by
    rw [c0_mul_Delta_mul_KPlus24_vadd_value w n hn]
    have hgoal : ‖(w : ℂ) ^ 2 * (E1 + E2 + E3)‖ = w.im ^ 2 * ‖E1 + E2 + E3‖ := by
      rw [norm_mul, norm_pow, hwnorm]
    rw [hgoal]
    calc w.im ^ 2 * ‖E1 + E2 + E3‖
        ≤ w.im ^ 2 * (‖E1‖ + ‖E2‖ + ‖E3‖) :=
          mul_le_mul_of_nonneg_left htri (by positivity)
      _ ≤ w.im ^ 2 * (K * u ^ 18 * ‖DeltaFun w‖) :=
          mul_le_mul_of_nonneg_left hsum (by positivity)
      _ ≤ 1 * (K * u ^ 18 * ‖DeltaFun w‖) :=
          mul_le_mul_of_nonneg_right hwim2 (by positivity)
      _ = K * u ^ 18 * ‖DeltaFun w‖ := by ring
      _ ≤ K * (scale w) ^ 18 * ‖DeltaFun w‖ :=
          mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hpow (le_of_lt hKpos))
            (norm_nonneg _)
  have hc0pos : 0 < ‖Work.Asymptotics.c0‖ := norm_pos_iff.mpr c0_ne_zero
  have hKP : ‖KPlus 24 ((n : ℝ) +ᵥ w) w‖ ≤ K * (scale w) ^ 18 / ‖Work.Asymptotics.c0‖ := by
    have hnorm : ‖Work.Asymptotics.c0 * (DeltaFun w * KPlus 24 ((n : ℝ) +ᵥ w) w)‖
        = ‖Work.Asymptotics.c0‖ * (‖DeltaFun w‖ * ‖KPlus 24 ((n : ℝ) +ᵥ w) w‖) := by
      simp only [norm_mul]
    have h2 : ‖Work.Asymptotics.c0‖ * (‖DeltaFun w‖ * ‖KPlus 24 ((n : ℝ) +ᵥ w) w‖)
        ≤ K * (scale w) ^ 18 * ‖DeltaFun w‖ := by rw [← hnorm]; exact hbig
    rw [le_div_iff₀ hc0pos]
    have h3 : ‖KPlus 24 ((n : ℝ) +ᵥ w) w‖ * ‖Work.Asymptotics.c0‖ * ‖DeltaFun w‖
        ≤ K * (scale w) ^ 18 * ‖DeltaFun w‖ := by
      rw [show ‖KPlus 24 ((n : ℝ) +ᵥ w) w‖ * ‖Work.Asymptotics.c0‖ * ‖DeltaFun w‖
          = ‖Work.Asymptotics.c0‖ * (‖DeltaFun w‖ * ‖KPlus 24 ((n : ℝ) +ᵥ w) w‖) from by
        ring]
      exact h2
    exact le_of_mul_le_mul_right h3 hDpos
  have hKfun : Kfun ℓ 24 ((n : ℝ) +ᵥ w) w = KPlus 24 ((n : ℝ) +ᵥ w) w / 2 := by
    rw [Kfun, MiddleRange.KMinus_eq_zero_of_coincidence ℓ (Or.inr rfl) (jInv_vadd_int n hn w),
      add_zero]
  rw [hKfun, norm_div, Complex.norm_ofNat]
  calc ‖KPlus 24 ((n : ℝ) +ᵥ w) w‖ / 2
      ≤ (K * (scale w) ^ 18 / ‖Work.Asymptotics.c0‖) / 2 := by linarith
    _ = K / (2 * ‖Work.Asymptotics.c0‖) * (scale w) ^ (18 : ℝ) := by
        have h18 : (scale w) ^ (18 : ℝ) = (scale w) ^ 18 := by
          rw [show (18 : ℝ) = ((18 : ℕ) : ℝ) from by norm_num, Real.rpow_natCast]
        rw [h18]; ring

/-- **The coincidence value, both dimensions.** -/
private lemma coin_d_bound (ℓ : LogLambdaData) (d : ℕ) (hd : d = 8 ∨ d = 24) :
    ∃ C N : ℝ, 0 ≤ C ∧ 0 ≤ N ∧ ∀ (w : ℍ), w ∈ KEpsilon → w.re = 0 → w.im ≤ 1 →
      ∀ n : ℤ, (n = 1 ∨ n = -1) →
      ‖Kfun ℓ d ((n : ℝ) +ᵥ w) w‖ ≤ C * (scale w) ^ N := by
  rcases hd with rfl | rfl
  · refine ⟨1, 0, zero_le_one, le_rfl, ?_⟩
    intro w _hw hre _hwim n hn
    have hjj : jInvariantFun ((n : ℝ) +ᵥ w) = jInvariantFun w := jInv_vadd_int n hn w
    have hz : Kfun ℓ 8 ((n : ℝ) +ᵥ w) w = 0 := by
      rw [Kfun, MiddleRange.KPlus_eight_eq_zero hjj,
        MiddleRange.KMinus_eq_zero_of_coincidence ℓ (Or.inl rfl) hjj, add_zero, zero_div]
    rw [hz, norm_zero, one_mul, Real.rpow_zero]
    norm_num
  · exact coin_d24_bound ℓ

/-- **The coincidence case of the tile principal-part window.**  At a coincidence
`j w = j (i t)` (with `w ∈ E` and `t ≤ 1`) one has `w = i t`, and the target value is the
translated coincidence value `K(n +ᵥ w, w)`. -/
theorem tilePPWindow_coincidence (ℓ : LogLambdaData) (d : ℕ) (hd : d = 8 ∨ d = 24) :
    ∃ C N : ℝ, 0 ≤ C ∧ 0 ≤ N ∧
      ∀ (w : ℍ), w ∈ KEpsilon →
      ∀ n : ℤ, (n = 1 ∨ n = -1) → ∀ (t : ℝ) (ht : 0 < t), t ≤ 1 →
        jInvariantFun w = jInvariantFun (imagAxis t ht) →
        ‖Kaxis (Kfun ℓ d) ((n : ℝ) +ᵥ w) t‖ ≤ C * (scale w) ^ N := by
  obtain ⟨C, N, hC, hN, hb⟩ := coin_d_bound ℓ d hd
  refine ⟨C, N, hC, hN, ?_⟩
  intro w hw n hn t ht ht1 hj
  have hzre : ((imagAxis t ht : ℍ) : ℂ).re = 0 := by simp [imagAxis]
  rcases Work.Asymptotics.eq_or_eq_S_of_re_eq_zero hw.1 hzre hj with h | h
  · have hKax : Kaxis (Kfun ℓ d) ((n : ℝ) +ᵥ w) t = Kfun ℓ d ((n : ℝ) +ᵥ w) w := by
      rw [Kaxis, dif_pos ht, h]
    have hre : w.re = 0 := by rw [← h]; simp [imagAxis]
    have hwim : w.im ≤ 1 := by rw [← h]; simp [imagAxis]; exact ht1
    rw [hKax]
    exact hb w hw hre hwim n hn
  · exfalso
    have h2 : 2 ≤ (imagAxis t ht).im := by rw [h]; exact hw.2
    simp [imagAxis] at h2
    linarith

/-- **The tile principal-part window `Work.Asymptotics.TilePPWindow`.** -/
theorem tilePPWindowGoal (ℓ : Work.Kernels.LogLambdaData) (d : ℕ) (hd : d = 8 ∨ d = 24) :
    Work.Asymptotics.TilePPWindow ℓ d := by
  obtain ⟨C₁, N₁, hC₁, hN₁, hfull⟩ := TileWindow.tile_pp_window_full ℓ d hd
  obtain ⟨C₂, N₂, hC₂, hN₂, hcoin⟩ := tilePPWindow_coincidence ℓ d hd
  refine ⟨max C₁ C₂, max N₁ N₂, le_max_of_le_left hC₁, le_max_of_le_left hN₁, ?_⟩
  intro w hw n hn t h1 h2
  have ht : 0 < t := lt_of_lt_of_le (by linarith [w.im_pos]) h1
  have hsc : (1 : ℝ) ≤ scale w := one_le_scale w
  have hsc0 : (0 : ℝ) ≤ scale w := le_trans zero_le_one hsc
  have hm₁ : (scale w) ^ N₁ ≤ (scale w) ^ (max N₁ N₂) :=
    Real.rpow_le_rpow_of_exponent_le hsc (le_max_left _ _)
  have hm₂ : (scale w) ^ N₂ ≤ (scale w) ^ (max N₁ N₂) :=
    Real.rpow_le_rpow_of_exponent_le hsc (le_max_right _ _)
  by_cases hne : ((t : ℂ) * Complex.I) = (w : ℂ)
  · have hzero : ((t : ℂ) * Complex.I - (w : ℂ))⁻¹ = 0 := by
      rw [sub_eq_zero.mpr hne, inv_zero]
    have hweq : w = imagAxis t ht := by
      apply UpperHalfPlane.ext
      show (w : ℂ) = (t : ℂ) * Complex.I
      exact hne.symm
    have hjj : jInvariantFun w = jInvariantFun (imagAxis t ht) := by rw [hweq]
    have hc := hcoin w hw n hn t ht h2 hjj
    calc ‖Kaxis (Kfun ℓ d) ((n : ℝ) +ᵥ w) t
          - ((n : ℂ) / (2 * (Real.pi : ℂ))) * (((t : ℂ) * Complex.I - (w : ℂ))⁻¹)‖
        = ‖Kaxis (Kfun ℓ d) ((n : ℝ) +ᵥ w) t‖ := by rw [hzero, mul_zero, sub_zero]
      _ ≤ C₂ * (scale w) ^ N₂ := hc
      _ ≤ max C₁ C₂ * (scale w) ^ (max N₁ N₂) :=
          mul_le_mul (le_max_right _ _) hm₂ (Real.rpow_nonneg hsc0 N₂)
            (le_trans hC₂ (le_max_right _ _))
  · have hb := hfull w hw n hn t ht h1 h2 hne
    calc ‖Kaxis (Kfun ℓ d) ((n : ℝ) +ᵥ w) t
          - ((n : ℂ) / (2 * (Real.pi : ℂ))) * (((t : ℂ) * Complex.I - (w : ℂ))⁻¹)‖
        ≤ C₁ * (scale w) ^ N₁ := hb
      _ ≤ max C₁ C₂ * (scale w) ^ (max N₁ N₂) :=
          mul_le_mul (le_max_left _ _) hm₁ (Real.rpow_nonneg hsc0 N₁)
            (le_trans hC₁ (le_max_left _ _))

end Work.Asymptotics.Tile
