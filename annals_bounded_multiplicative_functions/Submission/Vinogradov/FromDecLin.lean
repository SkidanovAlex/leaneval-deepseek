/-
Copyright: the formalization team of the Vinogradov mean value theorem project.
-/
import Submission.Vinogradov.Ne89
import Submission.Vinogradov.NikolskiiGlobal
import Submission.Vinogradov.BilinearReduction
import Submission.Vinogradov.ExtOpClass
import Submission.Vinogradov.PlateGeometry

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

/-!
# From ℓ²-decoupling to BDG's discrete restriction theorem (the localisation step)

This module carries out the passage

  (GLYZ / BDG decoupling for the moment curve at scale `1/N`)
    ⟹  (`bdg_thm_ntmain`, i.e. `Decouples k (k(k+1)) N (C·N^ε)`)

i.e. the step that turns the **global** ℓ²-decoupling inequality of Guo–Li–Yung–Zorin-Kranich
(arXiv:1912.09798, Theorem 1.1 / Definition 1.1) into the **ball-weighted** inequality
at the canonical radius `R = Nᵏ` that BDG use (Bourgain–Demeter–Guth, Ann. of Math. 184 (2016),
Theorem 1.2 in the form of their §4).

The mechanism is the standard localisation:

* multiply the pieces `E_{J_i} g` of the extension operator by the (dilated) localisation
  weight `ψ = locWeight k c' (ΛR)`, whose Fourier transform is supported in a ball of radius
  `locBand k / (ΛR)`.  Since `R ≥ Nᵏ` this ball is far smaller than the smallest side `N^{-k}`
  of a plate at scale `1/N`, so the localised pieces still satisfy the plate-support hypothesis
  of the decoupling theorem;
* the decoupling theorem then controls the global `L^{p_k}` norm of `ψ·E_{[0,1]}g`;
* the transfer estimate `∫_{c'} w_{B(c,R)}(c') |ψ_{c'}(x)|^{Q} dc' ≲ Rᵏ w_{B(c,R)}(x)`
  turns the `c'`-average back into the ball weight.

## Conventions

`DecLin k m C` (of `BilinearReduction.lean`) uses plates `plate k (1/(2m)) (pieceCenter m j)`,
i.e. plates whose scale is *half* the length of the corresponding piece of `[0,1]`.  The
localisation step needs a plate that contains the whole `γ`-image of a piece together with a
frequency perturbation, and that requires plates of the full piece length.  This is exactly the
convention of Guo–Li–Yung–Zorin-Kranich (their `U_J` has side lengths `|J|^1, …, |J|^k`), so we
introduce the predicate `DecLinScale k m λ C` (plates `plate k (λ/(2m)) (pieceCenter m j)`,
so `λ = 1` is `DecLin` and `λ = 2` is the paper's convention), and derive `DecLin` from it.
-/

noncomputable section
open MeasureTheory Complex Classical Filter
open scoped Real BigOperators Topology RealInnerProductSpace ENNReal

set_option autoImplicit false
set_option linter.style.haveILetI false
set_option linter.style.emptyLine false
set_option linter.unusedVariables false
set_option maxHeartbeats 4000000

namespace Submission.Vinogradov

/-! ## 1. The dilated localisation weight -/

/-- The dilation factor of the localisation weight.  It is chosen large enough that the
Fourier support of `locWeight k c' (lwScale k * R)` (a ball of radius
`locBand k / (lwScale k * R)`) is comfortably inside a plate of scale `1/N` whenever
`R ≥ Nᵏ`: the geometric condition is `2^{2k} · locBand k / (lwScale k · R) ≤ N^{-k}`. -/
noncomputable def lwScale (k : ℕ) : ℝ := 2 * (2:ℝ)^(2*k) * max 1 (locBand k)

lemma lwScale_pos (k : ℕ) : 0 < lwScale k := by
  unfold lwScale
  have h1 : (0:ℝ) < (2:ℝ)^(2*k) := by positivity
  have h2 : (0:ℝ) < max 1 (locBand k) := lt_of_lt_of_le one_pos (le_max_left _ _)
  positivity

lemma one_le_lwScale (k : ℕ) : 1 ≤ lwScale k := by
  unfold lwScale
  have h1 : (1:ℝ) ≤ (2:ℝ)^(2*k) := one_le_pow₀ (by norm_num)
  have h2 : (1:ℝ) ≤ max 1 (locBand k) := le_max_left _ _
  nlinarith

/-- The defining estimate of `lwScale`: `2^{2k} · locBand k ≤ lwScale k`. -/
lemma two_pow_mul_locBand_le_lwScale (k : ℕ) : (2:ℝ)^(2*k) * locBand k ≤ lwScale k := by
  unfold lwScale
  have h2 : locBand k ≤ max 1 (locBand k) := le_max_right _ _
  have h3 : (0:ℝ) < (2:ℝ)^(2*k) := by positivity
  have h4 : (1:ℝ) ≤ max 1 (locBand k) := le_max_left _ _
  nlinarith [h2, h3, h4, mul_nonneg (le_of_lt h3) (le_of_lt (lt_of_lt_of_le one_pos h4))]

lemma lwScale_pos' {k : ℕ} : (0:ℝ) < lwScale k := lwScale_pos k
lemma one_le_lwScale' {k : ℕ} : (1:ℝ) ≤ lwScale k := one_le_lwScale k

/-! ## 2. The geometric step

The localised pieces have Fourier support inside `γ(J) + B(0, ε)`; we show that this set is
contained in the full-scale plate of the piece `J`. -/

/-- Coordinate bound for the inverse frame transformation: if `|c| ≤ 1` then every coordinate
of `A_{1,-c} w` is bounded by `2^{2k} ‖w‖`. -/
lemma abs_affVecDual_one_neg_le (k : ℕ) {c : ℝ} (hc : |c| ≤ 1) (w : E k) (l : Fin k) :
    |affVecDual k 1 (-c) w l| ≤ (2:ℝ)^(2*k) * ‖w‖ := by
  have hk : (0:ℝ) ≤ (k:ℝ) := by positivity
  rw [affVecDual_apply]
  have h1 : ∀ j : Fin k,
      |w j * ((l.val + 1).choose (j.val + 1) : ℝ) * 1 ^ (j.val + 1) * (-c) ^ (l.val - j.val)|
        ≤ ‖w‖ * ((l.val + 1).choose (j.val + 1) : ℝ) := by
    intro j
    have hch : (0:ℝ) ≤ ((l.val + 1).choose (j.val + 1) : ℝ) := by positivity
    have hcj : |c| ^ (l.val - j.val) ≤ 1 := pow_le_one₀ (abs_nonneg _) hc
    have hwj : |w j| ≤ ‖w‖ := PiLp.norm_apply_le w j
    have h1p : |(1:ℝ) ^ (j.val + 1)| = 1 := by simp
    have hcd : |(-c) ^ (l.val - j.val)| = |c| ^ (l.val - j.val) := by rw [abs_pow, abs_neg]
    have habs : |w j * ((l.val + 1).choose (j.val + 1) : ℝ) * 1 ^ (j.val + 1) * (-c) ^ (l.val - j.val)|
        = |w j| * ((l.val + 1).choose (j.val + 1) : ℝ) * |c| ^ (l.val - j.val) := by
      simp only [abs_mul, abs_of_nonneg hch, h1p, hcd, mul_one]
    rw [habs]
    calc |w j| * ((l.val + 1).choose (j.val + 1) : ℝ) * |c| ^ (l.val - j.val)
        ≤ ‖w‖ * ((l.val + 1).choose (j.val + 1) : ℝ) * |c| ^ (l.val - j.val) := by
          gcongr
      _ ≤ ‖w‖ * ((l.val + 1).choose (j.val + 1) : ℝ) * 1 := by
          gcongr
      _ = ‖w‖ * ((l.val + 1).choose (j.val + 1) : ℝ) := by ring
  calc |∑ j : Fin k, w j * ((l.val + 1).choose (j.val + 1) : ℝ) * 1 ^ (j.val + 1) * (-c) ^ (l.val - j.val)|
      ≤ ∑ j : Fin k, |w j * ((l.val + 1).choose (j.val + 1) : ℝ) * 1 ^ (j.val + 1) * (-c) ^ (l.val - j.val)| :=
        Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ j : Fin k, ‖w‖ * ((l.val + 1).choose (j.val + 1) : ℝ) := Finset.sum_le_sum (fun j _ => h1 j)
    _ = ‖w‖ * ∑ j : Fin k, ((l.val + 1).choose (j.val + 1) : ℝ) := by rw [Finset.mul_sum]
    _ ≤ ‖w‖ * (2:ℝ)^(2*k) := by
        refine mul_le_mul_of_nonneg_left ?_ (norm_nonneg _)
        calc ∑ j : Fin k, ((l.val + 1).choose (j.val + 1) : ℝ)
            ≤ ∑ _j : Fin k, (2:ℝ)^k := by
              refine Finset.sum_le_sum fun j _ => ?_
              have hle : (l.val + 1).choose (j.val + 1) ≤ 2 ^ (l.val + 1) :=
                Nat.choose_le_two_pow _ _
              have h1 : ((l.val + 1).choose (j.val + 1) : ℝ) ≤ (2:ℝ)^(l.val + 1) := by
                exact_mod_cast hle
              have h2 : (2:ℝ)^(l.val+1) ≤ (2:ℝ)^k := by
                apply pow_le_pow_right₀ (by norm_num) (by omega)
              linarith
          _ = (k:ℝ) * (2:ℝ)^k := by
              rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
          _ ≤ (2:ℝ)^(2*k) := by
              have hk2 : (k:ℝ) ≤ (2:ℝ)^k := by
                have h2 : k ≤ 2 ^ k := le_of_lt Nat.lt_two_pow_self
                exact_mod_cast h2
              have hpos : (0:ℝ) < (2:ℝ)^k := pow_pos (by norm_num) k
              have h4 : (2:ℝ)^k * (2:ℝ)^k = (4:ℝ)^k := by rw [← mul_pow]; norm_num
              have h5 : (4:ℝ)^k = (2:ℝ)^(2*k) := by
                rw [show (4:ℝ) = 2 ^ 2 by norm_num, pow_mul]
              have h6 : (k:ℝ) * (2:ℝ)^k ≤ (2:ℝ)^k * (2:ℝ)^k := by nlinarith [hk2, hpos]
              linarith
    _ = (2:ℝ)^(2*k) * ‖w‖ := by ring

/-- **The geometric core of the localisation.**  If `|Δ| ≤ δ/2` and the frequency
perturbation `w` is small enough (`2^{2k}‖w‖ ≤ δ^k`), then the perturbed curve point
`γ(c+Δ) + w` still lies in the plate `𝒰_{[c]}(δ)`. -/
theorem gammaVec_add_mem_plate (k : ℕ) (hk : 1 ≤ k) {δ : ℝ} (hδ0 : 0 < δ) (hδ1 : δ ≤ 1)
    {c Δ : ℝ} (hc : |c| ≤ 1) (hΔ : |Δ| ≤ δ / 2) {w : E k}
    (hw : (2:ℝ)^(2*k) * ‖w‖ ≤ δ ^ k) :
    gammaVec k (c + Δ) + w ∈ plate k δ c := by
  have hδne : δ ≠ 0 := ne_of_gt hδ0
  set y : E k := affVecDual k 1 (-c) w with hy
  have hwy : affVecDual k 1 c y = w := by
    rw [hy]
    simpa using affVecDual_inv_comp k (ρ := 1) (by norm_num) c w
  have hδk_le : δ ^ k ≤ δ := by
    calc δ ^ k ≤ δ ^ 1 := pow_le_pow_of_le_one (le_of_lt hδ0) hδ1 hk
      _ = δ := by ring
  have hyi : ∀ i : Fin k, |y i| ≤ (2:ℝ)^(2*k) * ‖w‖ := fun i => abs_affVecDual_one_neg_le k hc w i
  have hy0eq : ∀ (h : 0 < k), y ⟨0, h⟩ = w ⟨0, h⟩ := by
    intro h
    rw [hy, affVecDual_apply]
    rw [Finset.sum_eq_single (⟨0, h⟩ : Fin k)]
    · simp
    · intro j _ hj
      have hjne : j.val ≠ 0 := by intro hc'; exact hj (Fin.ext (by simpa using hc'))
      rw [Nat.choose_eq_zero_of_lt (by omega : 1 < j.val + 1)]
      simp
    · intro hmem; exact absurd (Finset.mem_univ _) hmem
  have hwk : ‖w‖ ≤ δ ^ k := by
    have h2 : (1:ℝ) ≤ (2:ℝ)^(2*k) := one_le_pow₀ (by norm_num)
    nlinarith [norm_nonneg w]
  have hwδ : ‖w‖ ≤ δ / 2 := by
    have h2 : (2:ℝ) ≤ (2:ℝ)^(2*k) := by
      calc (2:ℝ) = (2:ℝ)^1 := by ring
        _ ≤ (2:ℝ)^(2*k) := by
            apply pow_le_pow_right₀ (by norm_num) (by omega)
    nlinarith [norm_nonneg w, hwk, hδk_le]
  refine ⟨affVecDual k δ⁻¹ 0 (shiftVec k Δ + y), ?_, ?_⟩
  · intro i
    rw [affVecDual_zero_apply, PiLp.add_apply, shiftVec_apply]
    rw [show (δ⁻¹) ^ (i.val + 1) = (δ ^ (i.val + 1))⁻¹ by rw [inv_pow]]
    rw [abs_mul, abs_of_nonneg (by positivity : (0:ℝ) ≤ (δ ^ (i.val + 1))⁻¹), ← div_eq_mul_inv]
    have hden : 0 < δ ^ (i.val + 1) := pow_pos hδ0 _
    rcases Nat.eq_zero_or_pos i.val with h0 | hpos
    · -- the first coordinate: only `y 0 = w 0` can be used
      have hi0 : i = (⟨0, by omega⟩ : Fin k) := Fin.ext h0
      rw [hi0, hy0eq (by omega)]
      simp only [Nat.add_one, Nat.cast_one, Nat.factorial_one]
      rw [pow_one, pow_one]
      have hnum : |Δ + w ⟨0, by omega⟩| ≤ δ := by
        calc |Δ + w ⟨0, by omega⟩| ≤ |Δ| + |w ⟨0, by omega⟩| := abs_add_le _ _
          _ ≤ δ / 2 + δ / 2 := by
              have h1 := PiLp.norm_apply_le w (⟨0, by omega⟩ : Fin k)
              rw [Real.norm_eq_abs] at h1
              linarith
          _ = δ := by ring
      calc |Δ + w ⟨0, by omega⟩| / δ ≤ δ / δ :=
            div_le_div_of_nonneg_right hnum (le_of_lt hδ0)
        _ = 1 := by field_simp
    · -- the higher coordinates: there is slack
      have hifac : (2:ℝ) ≤ ((i.val + 1).factorial : ℝ) := by
        have h2 : 2 ≤ (i.val + 1).factorial := by
          calc (2:ℕ) = 2 * 1 := by ring
            _ ≤ (i.val+1) * (i.val).factorial := by
                have := Nat.factorial_pos i.val
                nlinarith
            _ = (i.val+1).factorial := (Nat.factorial_succ i.val).symm
        exact_mod_cast h2
      have hdenk : δ ^ k ≤ δ ^ (i.val + 1) :=
        pow_le_pow_of_le_one (le_of_lt hδ0) hδ1 (by omega)
      have hΔb : |Δ| ^ (i.val + 1) ≤ (δ / 2) ^ (i.val + 1) :=
        pow_le_pow_left₀ (abs_nonneg _) hΔ _
      have hA : ((δ/2) ^ (i.val+1)) / δ ^ (i.val+1) = ((1/2:ℝ)) ^ (i.val+1) := by
        have h1 : (δ/2)/δ = (1/2:ℝ) := by field_simp
        rw [← div_pow, h1]
      have hB : ((2:ℝ)^(2*k) * ‖w‖) / δ ^ (i.val+1) ≤ 1 := by
        rw [div_le_one hden]
        exact le_trans hw hdenk
      have hhalf : ((1/2:ℝ)) ^ (i.val + 1) ≤ 1 / 2 := by
        calc ((1/2:ℝ))^(i.val+1) ≤ (1/2)^1 :=
              pow_le_pow_of_le_one (by norm_num) (by norm_num) (by omega)
          _ = 1/2 := by norm_num
      have hkey : |Δ ^ (i.val + 1) + y i| ≤ (δ/2)^(i.val+1) + (2:ℝ)^(2*k)*‖w‖ := by
        refine le_trans (abs_add_le _ _) ?_
        rw [abs_pow]
        exact add_le_add hΔb (hyi i)
      calc |Δ ^ (i.val + 1) + y i| / δ ^ (i.val + 1)
          ≤ ((δ/2)^(i.val+1) + (2:ℝ)^(2*k)*‖w‖) / δ ^ (i.val + 1) :=
            div_le_div_of_nonneg_right hkey (le_of_lt hden)
        _ = (δ/2)^(i.val+1)/δ^(i.val+1) + ((2:ℝ)^(2*k)*‖w‖)/δ^(i.val+1) := by
            rw [add_div]
        _ ≤ 1/2 + 1 := by rw [hA]; linarith
        _ ≤ ((i.val + 1).factorial : ℝ) := by linarith
  · rw [affMap_apply]
    have hcomp : affVecDual k δ c (affVecDual k δ⁻¹ 0 (shiftVec k Δ + y))
        = affVecDual k 1 c (shiftVec k Δ + y) := by
      rw [affVecDual_comp, show δ * δ⁻¹ = (1:ℝ) from mul_inv_cancel₀ hδne]
      norm_num
    rw [hcomp]
    have h2 : gammaVec k (c + Δ) = gammaVec k c + affVecDual k 1 c (shiftVec k Δ) := by
      simpa using gammaVec_add_eq k c Δ
    have hadd : affVecDual k 1 c (shiftVec k Δ + y)
        = affVecDual k 1 c (shiftVec k Δ) + affVecDual k 1 c y := by
      rw [← affVecDualLin_apply, ← affVecDualLin_apply, ← affVecDualLin_apply, map_add]
    rw [h2, ← hwy]
    rw [show gammaVec k c + affVecDual k 1 c (shiftVec k Δ) + affVecDual k 1 c y
        = gammaVec k c + (affVecDual k 1 c (shiftVec k Δ) + affVecDual k 1 c y) from by abel,
      ← hadd]



/-! ## 3. The localised pieces still satisfy the plate-support hypothesis -/

/-- **The Fourier representation of the localisation weight.** -/
lemma locWeight_eq_integral_chat (k : ℕ) (c' : E k) {R' : ℝ} (hR' : R' ≠ 0) (x : E k) :
    locWeight k c' R' x
      = ∫ ξ : E k, chat k x ((R')⁻¹ • ξ) * (locBumpF k ξ * (chat k c' ((R')⁻¹ • ξ))⁻¹) := by
  rw [locWeight_apply, locBump_invFourier]
  refine integral_congr_ae (Filter.Eventually.of_forall fun ξ => ?_)
  simp only [chat]
  have harg : (((2 * Real.pi : ℂ) * Complex.I)
        * ((⟪(R')⁻¹ • (x - c'), ξ⟫ : ℝ) : ℂ))
      = (((2 * Real.pi : ℂ) * Complex.I) * ((⟪x, (R')⁻¹ • ξ⟫ : ℝ) : ℂ))
        + (-(((2 * Real.pi : ℂ) * Complex.I) * ((⟪c', (R')⁻¹ • ξ⟫ : ℝ) : ℂ))) := by
    have h1 : ⟪(R')⁻¹ • (x - c'), ξ⟫ = (R')⁻¹ * (⟪x, ξ⟫ - ⟪c', ξ⟫) := by
      rw [inner_smul_left, inner_sub_left]
      simp only [starRingEnd_apply, star_trivial]
    have h2 : ⟪x, (R')⁻¹ • ξ⟫ = (R')⁻¹ * ⟪x, ξ⟫ := inner_smul_right x ξ (R')⁻¹
    have h3 : ⟪c', (R')⁻¹ • ξ⟫ = (R')⁻¹ * ⟪c', ξ⟫ := inner_smul_right c' ξ (R')⁻¹
    rw [h1, h2, h3]
    push_cast
    ring
  rw [harg, Complex.exp_add, Complex.exp_neg]
  ring_nf

/-- The same representation, but with the measure restricted to the (finite) ball that
carries the support of `locBumpF`. -/
lemma locWeight_eq_integral_chat_restrict (k : ℕ) (c' : E k) {R' : ℝ} (hR' : R' ≠ 0)
    (x : E k) :
    locWeight k c' R' x
      = ∫ ξ : E k, chat k x ((R')⁻¹ • ξ) * (locBumpF k ξ * (chat k c' ((R')⁻¹ • ξ))⁻¹)
          ∂(volume.restrict (Metric.ball 0 (locBand k))) := by
  set F : E k → ℂ := fun ξ =>
    chat k x ((R')⁻¹ • ξ) * (locBumpF k ξ * (chat k c' ((R')⁻¹ • ξ))⁻¹) with hF
  have hzero : ∀ ξ, ξ ∉ Metric.ball (0 : E k) (locBand k) → F ξ = 0 := by
    intro ξ hξ
    have h0 : locBumpF k ξ = 0 := by
      by_contra hc
      exact hξ (locBand_spec k (subset_tsupport _ (by simpa [Function.mem_support] using hc)))
    show chat k x ((R')⁻¹ • ξ) * (locBumpF k ξ * (chat k c' ((R')⁻¹ • ξ))⁻¹) = 0
    rw [h0]
    ring
  rw [locWeight_eq_integral_chat k c' hR' x]
  exact (MeasureTheory.setIntegral_eq_integral_of_forall_compl_eq_zero hzero).symm

lemma integrable_locBumpF_restrict (k : ℕ) :
    Integrable (locBumpF k) (volume.restrict (Metric.ball 0 (locBand k))) :=
  (locBumpF k).integrable.integrableOn

/-- **The localised pieces belong to the class of the full-scale plates.**
If `R ≥ Nᵏ` then multiplying `E_{((i)/N,((i+1)/N)]} g` by the dilated localisation weight
`locWeight k c' (lwScale k * R)` does not move its Fourier support out of the plate
`plate k (1/N) (pieceCenter N i)`. -/
theorem localised_piece_isFourierRep (k : ℕ) (hk : 1 ≤ k) {N : ℕ} (hN : 1 ≤ N) {R : ℝ}
    (hR : (N:ℝ)^k ≤ R) (c' : E k) (i : Fin N) {g : ℝ → ℂ} (hgm : Measurable g)
    (hgi : IntegrableOn g (Set.Icc 0 1) volume) :
    IsFourierRep k (plate k ((1:ℝ) / N) (pieceCenter N i))
      (fun x => locWeight k c' (lwScale k * R) x
        * extOp k g (((i:ℕ):ℝ) / N) ((((i:ℕ):ℝ) + 1) / N) x) := by
  set R' : ℝ := lwScale k * R with hR'def
  have hNpos : (0:ℝ) < N := by exact_mod_cast hN
  have hR'pos : 0 < R' := by
    rw [hR'def]; exact mul_pos (lwScale_pos k) (lt_of_lt_of_le (by positivity) hR)
  have hR'ne : R' ≠ 0 := ne_of_gt hR'pos
  set a : ℝ := (((i:ℕ):ℝ)) / N with hadef
  set b : ℝ := ((((i:ℕ):ℝ)) + 1) / N with hbdef
  have hab : a ≤ b := by
    rw [hadef, hbdef]
    rw [div_le_div_iff_of_pos_right hNpos]
    linarith
  have ha0 : 0 ≤ a := by rw [hadef]; positivity
  have hb1 : b ≤ 1 := by
    rw [hbdef, div_le_one hNpos]
    have : ((i:ℕ) : ℝ) + 1 ≤ N := by
      have := i.isLt
      exact_mod_cast this
    linarith
  -- the frequency bound
  have hfreq : ∀ ξ : E k, ξ ∈ tsupport (locBumpF k) →
      (2:ℝ)^(2*k) * ‖(R')⁻¹ • ξ‖ ≤ ((1:ℝ)/N)^k := by
    intro ξ hξ
    have hξb : ‖ξ‖ ≤ locBand k := by
      have := locBand_spec k hξ
      rw [Metric.mem_ball, dist_zero_right] at this
      exact le_of_lt this
    have h1 : ‖(R')⁻¹ • ξ‖ = ‖ξ‖ / R' := by
      rw [norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hR'pos), inv_mul_eq_div]
    have hNk : (0:ℝ) < (N:ℝ)^k := by positivity
    have hR'ge : lwScale k * (N:ℝ)^k ≤ R' := by
      rw [hR'def]
      exact mul_le_mul_of_nonneg_left hR (le_of_lt (lwScale_pos k))
    rw [h1]
    rcases le_total 0 (locBand k) with hlbpos | hlbneg
    · have h5 : (0:ℝ) ≤ (2:ℝ)^(2*k) := by positivity
      have h3 : ‖ξ‖ / R' ≤ locBand k / R' := div_le_div_of_nonneg_right hξb (le_of_lt hR'pos)
      have h4 : locBand k / R' ≤ locBand k / (lwScale k * (N:ℝ)^k) :=
        div_le_div_of_nonneg_left hlbpos (mul_pos (lwScale_pos k) hNk) hR'ge
      have h6 : (2:ℝ)^(2*k) * (locBand k / (lwScale k * (N:ℝ)^k)) ≤ ((1:ℝ)/N)^k := by
        have h7 : (2:ℝ)^(2*k) * locBand k ≤ lwScale k := two_pow_mul_locBand_le_lwScale k
        rw [mul_div_assoc', div_le_iff₀ (mul_pos (lwScale_pos k) hNk)]
        have h9 : ((1:ℝ)/N)^k * (N:ℝ)^k = 1 := by
          rw [← mul_pow, div_mul_cancel₀ _ (ne_of_gt hNpos), one_pow]
        have h10 : ((1:ℝ)/N)^k * (lwScale k * (N:ℝ)^k) = lwScale k := by
          calc ((1:ℝ)/N)^k * (lwScale k * (N:ℝ)^k)
              = lwScale k * (((1:ℝ)/N)^k * (N:ℝ)^k) := by ring
            _ = lwScale k * 1 := by rw [h9]
            _ = lwScale k := by ring
        rw [h10]
        exact h7
      calc (2:ℝ)^(2*k) * (‖ξ‖ / R')
          ≤ (2:ℝ)^(2*k) * (locBand k / R') := mul_le_mul_of_nonneg_left h3 h5
        _ ≤ (2:ℝ)^(2*k) * (locBand k / (lwScale k * (N:ℝ)^k)) := mul_le_mul_of_nonneg_left h4 h5
        _ ≤ ((1:ℝ)/N)^k := h6
    · have hzero : ‖ξ‖ = 0 := le_antisymm (le_trans hξb hlbneg) (norm_nonneg _)
      rw [hzero, zero_div, mul_zero]
      positivity
  -- the measure and the density
  set ν₁ : Measure (E k) := volume.restrict (Metric.ball 0 (locBand k)) with hν₁
  set ν₂ : Measure ℝ := volume.restrict (Set.Ioc a b) with hν₂
  set hg' : ℝ → ℂ := Set.indicator (Set.Icc a b) g with hg'def
  have hg'm : Measurable hg' := hgm.indicator measurableSet_Icc
  have hgab : IntegrableOn g (Set.Icc a b) volume :=
    hgi.mono_set (Set.Icc_subset_Icc ha0 hb1)
  have hg'i : Integrable hg' volume := by
    rw [hg'def]
    exact (integrable_indicator_iff measurableSet_Icc).mpr hgab
  have hfin₁ : IsFiniteMeasure ν₁ := by
    rw [hν₁, isFiniteMeasure_iff, Measure.restrict_apply MeasurableSet.univ, Set.univ_inter]
    exact measure_ball_lt_top
  haveI hfin₂ : IsFiniteMeasure ν₂ := by rw [hν₂]; infer_instance
  haveI := hfin₁
  -- the a.e. statement identifying `hg'` with `g`
  have hae2 : ∀ᵐ t ∂ν₂, hg' t = g t := by
    rw [hν₂]
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with t ht
    rw [hg'def]
    exact Set.indicator_of_mem (Set.Ioc_subset_Icc_self ht) g
  -- consequences for the product measure
  have hae2' : ∀ᵐ z ∂(ν₁.prod ν₂), hg' z.2 = g z.2 := by
    rw [ae_iff]
    have hzero : ν₂ {t : ℝ | ¬ (hg' t = g t)} = 0 := by
      have := hae2
      rwa [ae_iff] at this
    have hm : MeasurableSet {z : E k × ℝ | ¬ (hg' z.2 = g z.2)} :=
      (measurableSet_eq_fun (hg'm.comp measurable_snd) (hgm.comp measurable_snd)).compl
    rw [Measure.prod_apply hm]
    have hz : ∀ x : E k, Prod.mk x ⁻¹' {z : E k × ℝ | ¬ (hg' z.2 = g z.2)}
        = {t : ℝ | ¬ (hg' t = g t)} := fun x => by ext y; simp
    simp only [hz, hzero, lintegral_zero]
  refine IsFourierRep.mk' (ι := E k × ℝ)
    (Γ := fun u : E k × ℝ => (R')⁻¹ • u.1 + gammaVec k u.2)
    (ν := ν₁.prod ν₂)
    (φ := fun u : E k × ℝ => locBumpF k u.1 * (chat k c' ((R')⁻¹ • u.1))⁻¹ * hg' u.2)
    inferInstance ?_ ?_ ?_ ?_ ?_
  · -- integrability of the density
    have hF : Integrable (fun ξ : E k => locBumpF k ξ * (chat k c' ((R')⁻¹ • ξ))⁻¹) ν₁ := by
      refine (integrable_locBumpF_restrict k).mul_bdd (c := 1) ?_ ?_
      · refine ((((continuous_chat_left k c').comp (continuous_const_smul _)).inv₀ ?_).aestronglyMeasurable)
        intro ξ h
        simp only [Function.comp_apply] at h
        have h1 := chat_norm k c' ((R')⁻¹ • ξ)
        rw [h] at h1
        simp at h1
      · filter_upwards with ξ
        rw [norm_inv, chat_norm, inv_one]
    have hG : Integrable hg' ν₂ := by
      rw [hν₂]
      exact hg'i.mono_measure Measure.restrict_le_self
    have hprod := hF.mul_prod hG
    simpa only [mul_assoc] using hprod
  · -- measurability of `Γ`
    exact (((continuous_const_smul ((R')⁻¹)).measurable.comp measurable_fst).add
      ((measurable_gammaVec k).comp measurable_snd))
  · -- measurability of the density
    have hcont : Continuous (fun ξ : E k => (chat k c' ((R')⁻¹ • ξ))⁻¹) :=
      ((continuous_chat_left k c').comp (continuous_const_smul _)).inv₀ (fun ξ h => by
        simp only [Function.comp_apply] at h
        have h1 := chat_norm k c' ((R')⁻¹ • ξ)
        rw [h] at h1
        simp at h1)
    exact ((((locBumpF k).continuous.measurable.comp measurable_fst).mul
      (hcont.measurable.comp measurable_fst)).mul (hg'm.comp measurable_snd))
  · -- the support condition
    intro u hu
    have hne1 : locBumpF k u.1 ≠ 0 := by
      intro h
      exact hu (by simp [h])
    have hne2 : hg' u.2 ≠ 0 := by
      intro h
      exact hu (by simp [h])
    have hsupp : u.1 ∈ tsupport (locBumpF k) := subset_tsupport _ (by simpa [Function.mem_support] using hne1)
    have ht : u.2 ∈ Set.Icc a b := by
      by_contra h
      exact hne2 (by simp [hg'def, h])
    have hba : b - a = 1 / N := by rw [hadef, hbdef]; ring
    have hΔ : |u.2 - pieceCenter N i| ≤ ((1:ℝ)/N) / 2 := by
      have hc : pieceCenter N i = (a + b) / 2 := by
        rw [hadef, hbdef, pieceCenter]
        field_simp
        ring
      rw [hc, abs_le]
      constructor <;> linarith [ht.1, ht.2, hba]
    have hc1 : |pieceCenter N i| ≤ 1 := by
      rw [abs_le]
      constructor
      · have : (0:ℝ) ≤ pieceCenter N i := by rw [pieceCenter]; positivity
        linarith
      · rw [pieceCenter, div_le_one hNpos]
        have : ((i:ℕ) : ℝ) + 1 ≤ N := by
          have := i.isLt
          exact_mod_cast this
        linarith
    have hw := hfreq u.1 hsupp
    have hmain := gammaVec_add_mem_plate k hk (δ := (1:ℝ)/N) (by positivity)
      (by rw [div_le_one hNpos]; exact_mod_cast hN) hc1 hΔ hw
    have hsub : pieceCenter N i + (u.2 - pieceCenter N i) = u.2 := by ring
    rw [hsub] at hmain
    rw [add_comm]
    exact hmain
  · -- the representation
    intro x
    rw [locWeight_eq_integral_chat_restrict k c' hR'ne x, extOp,
      intervalIntegral.integral_of_le hab]
    rw [← integral_prod_mul
      (fun ξ : E k => chat k x ((R')⁻¹ • ξ) * (locBumpF k ξ * (chat k c' ((R')⁻¹ • ξ))⁻¹))
      (fun t : ℝ => g t * momChar k x t)]
    refine integral_congr_ae ?_
    filter_upwards [hae2'] with z hz
    simp only [hz]
    have hchat : chat k x ((R')⁻¹ • z.1 + gammaVec k z.2)
        = chat k x ((R')⁻¹ • z.1) * momChar k x z.2 := by
      rw [chat_add, chat_gammaVec]
    rw [hchat]
    ring_nf


/-! ## 4. The transfer estimate at an arbitrary power `Q`

The bridge needs the `η_{B'}`-step of BDG's Lemma `nl9` at the critical power `Q = k(k+1)`
(not only at `Q = 2`), for *any* fixed dilation `Λ ≥ 1` of the localisation weight.  The two
lemmas below are the `Q`-general forms of `Ne89.locBump_decay_sq` and
`Ne89.exists_locWeight_transfer`; their proofs are the same computations with `^2` replaced
by `^Q`.
-/

/-- The decay of the localisation bump at an arbitrary power `Q ≥ 1`. -/
lemma locBump_decay_pow (k : ℕ) {Q : ℝ} (hQ : 1 ≤ Q) :
    ∃ C : ℝ, 0 < C ∧ ∀ z : E k,
      ‖locBump k z‖ ^ Q ≤ C * (1 + ‖z‖) ^ (-(100 * (k:ℝ))) := by
  obtain ⟨C₀, hC₀pos, hC₀⟩ :=
    Commons.Analysis.Distribution.schwartzMap_decay_one_add_norm (locBump k) (100*k)
  refine ⟨max 1 (C₀ ^ Q), ?_, fun z => ?_⟩
  · have h1 : (0:ℝ) < C₀ ^ Q := Real.rpow_pos_of_pos hC₀pos Q
    exact lt_of_lt_of_le one_pos (le_max_left _ _)
  have hCz : ‖locBump k z‖ ≤ C₀ * (1 + ‖z‖) ^ (-(100 * (k:ℝ))) := by
    simpa only [Nat.cast_mul, Nat.cast_ofNat] using hC₀ z
  have hb : 1 ≤ 1 + ‖z‖ := by have h := norm_nonneg z; linarith
  have hz : 0 ≤ ‖locBump k z‖ := norm_nonneg _
  have hstep : ‖locBump k z‖ ^ Q ≤ (C₀ * (1 + ‖z‖) ^ (-(100 * (k:ℝ)))) ^ Q :=
    Real.rpow_le_rpow hz hCz (le_trans zero_le_one hQ)
  have hbase : 0 ≤ (1 + ‖z‖) ^ (-(100 * (k:ℝ))) := Real.rpow_nonneg (by linarith) _
  have hsq : (C₀ * (1 + ‖z‖) ^ (-(100 * (k:ℝ)))) ^ Q
      = C₀ ^ Q * (1 + ‖z‖) ^ (-(100 * (k:ℝ)) * Q) := by
    rw [Real.mul_rpow hC₀pos.le hbase, ← Real.rpow_mul (by linarith)]
  have hcmp : (1 + ‖z‖) ^ (-(100 * (k:ℝ)) * Q) ≤ (1 + ‖z‖) ^ (-(100 * (k:ℝ))) := by
    refine Real.rpow_le_rpow_of_exponent_le hb ?_
    have : (0:ℝ) ≤ 100 * (k:ℝ) := by positivity
    nlinarith
  calc ‖locBump k z‖ ^ Q
      ≤ C₀ ^ Q * (1 + ‖z‖) ^ (-(100 * (k:ℝ)) * Q) := hstep.trans (le_of_eq hsq)
    _ ≤ C₀ ^ Q * (1 + ‖z‖) ^ (-(100 * (k:ℝ))) :=
        mul_le_mul_of_nonneg_left hcmp (Real.rpow_nonneg hC₀pos.le _)
    _ ≤ max 1 (C₀ ^ Q) * (1 + ‖z‖) ^ (-(100 * (k:ℝ))) :=
        mul_le_mul_of_nonneg_right (le_max_right _ _) (Real.rpow_nonneg (by linarith) _)

/-- **Transfer of the localisation weight to the ball weight, at an arbitrary power `Q ≥ 1`**
(the `η_{B'}`-step of BDG's Lemma `nl9`, proved here by integrating over *all* centres `c'`
instead of over a discrete cover):
`∫_{c'} w_{B(c,R)}(c') · ‖locWeight k c' (ΛR) y‖^Q dc' ≤ C Rᵏ w_{B(c,R)}(y)`,
uniformly in `c`, `R > 0`, `y` (for every fixed `Λ ≥ 1`). -/
lemma exists_locWeight_transfer_pow (k : ℕ) (hk : 1 ≤ k) {Q : ℝ} (hQ : 1 ≤ Q) {Λ : ℝ}
    (hΛ : 1 ≤ Λ) :
    ∃ C : ℝ, 0 < C ∧ ∀ (c : E k) {R : ℝ}, 0 < R → ∀ y : E k,
      ∫ c' : E k, ballWeight k c R c' * ‖locWeight k c' (Λ * R) y‖ ^ Q
        ≤ C * R^k * ballWeight k c R y := by
  obtain ⟨C₀, hC₀pos, hC₀⟩ := locBump_decay_pow k hQ
  have hknn : (0:ℝ) ≤ k := by positivity
  have hAc : (k:ℝ) < (100 * (k:ℝ)) := by
    have hkR : (0:ℝ) < k := by exact_mod_cast hk
    nlinarith
  obtain ⟨C₁, hC₁pos, hC₁⟩ :=
    Commons.Analysis.Integral.integrable_and_integral_one_add_norm_neg_mul_le
      (k := k) (A := (100 * (k:ℝ))) (B := (100 * (k:ℝ))) hAc hAc
  refine ⟨Λ ^ (100 * (k:ℝ)) * (C₀ * C₁),
    mul_pos (Real.rpow_pos_of_pos (lt_of_lt_of_le one_pos hΛ) _) (mul_pos hC₀pos hC₁pos), ?_⟩
  intro c R hR y
  set th : ℝ := Λ with hth
  have hth1 : 1 ≤ th := hΛ
  have hth0 : 0 < th := lt_of_lt_of_le one_pos hΛ
  have hthne : th ≠ 0 := hth0.ne'
  have hthkne : th ^ k ≠ 0 := (by positivity : (0:ℝ) < th ^ k).ne'
  set Rθ : ℝ := th * R with hRθdef
  have hRθ : 0 < Rθ := by rw [hRθdef]; exact mul_pos (lt_of_lt_of_le one_pos hΛ) (by positivity)
  set z : E k := (Rθ)⁻¹ • (y - c) with hz
  have hyc : y - c = Rθ • z := by rw [hz, smul_inv_smul₀ hRθ.ne']
  have hpos1 : ∀ v : E k, (0:ℝ) < 1 + th * ‖z - v‖ := fun v => by
    have h := norm_nonneg (z - v); nlinarith [hth1, h]
  have hpos2 : ∀ v : E k, (0:ℝ) < 1 + ‖v‖ := fun v => by
    have h := norm_nonneg v; linarith
  have hpos0 : ∀ v : E k, (0:ℝ) < 1 + ‖z - v‖ := fun v => by
    have h := norm_nonneg (z - v); linarith
  set H : E k → ℝ := fun c' => ballWeight k c R c' * ‖locWeight k c' Rθ y‖ ^ Q with hH
  have hmeas : AEStronglyMeasurable H volume := by
    have hcont1 : Continuous (fun c' : E k => locWeight k c' Rθ y) :=
      (locBump k).continuous.comp (by fun_prop)
    have : Continuous H := by
      simp only [hH]
      exact (ballWeight_continuous k c hR).mul (hcont1.norm.rpow_const (fun x => Or.inr (le_trans zero_le_one hQ)))
    exact this.aestronglyMeasurable
  have h1 : ∫ c' : E k, H c' = ∫ u : E k, H (y - u) := integral_sub_left k y H hmeas
  set G : E k → ℝ := fun v => ballWeight k c R (y - Rθ • v) * ‖locBump k v‖ ^ Q with hG
  have h2 : (fun u : E k => H (y - u)) = fun u : E k => G ((Rθ)⁻¹ • u) := by
    funext u
    simp only [hH, hG, locWeight]
    have e1 : y - (y - u) = u := by abel
    rw [e1, smul_inv_smul₀ hRθ.ne']
  have h3 : ∫ u : E k, G ((Rθ)⁻¹ • u) = Rθ^k * ∫ v : E k, G v :=
    integral_smul_inv k hRθ G
  have h4 : ∫ v : E k, G v
      = ∫ v : E k, (1 + th * ‖z - v‖) ^ (-(100 * (k:ℝ))) * ‖locBump k v‖ ^ Q := by
    refine integral_congr_ae (Filter.Eventually.of_forall fun v => ?_)
    simp only [hG]
    rw [ballWeight_eq_rpow k c hR (y - Rθ • v)]
    have hfac : ‖y - Rθ • v - c‖ / R = th * ‖z - v‖ := by
      have hsub : y - Rθ • v - c = Rθ • (z - v) := by rw [smul_sub, ← hyc]; abel
      rw [hsub, norm_smul, Real.norm_eq_abs, abs_of_pos hRθ, hRθdef]
      field_simp
    rw [hfac]
  -- (iv) Schwartz decay and the convolution bound
  set f : E k → ℝ := fun v => (1 + th * ‖z - v‖) ^ (-(100 * (k:ℝ)))
      * (1 + ‖v‖) ^ (-(100 * (k:ℝ))) with hf
  have hfcont : Continuous f := by
    simp only [hf]
    exact ((continuous_const.add (continuous_const.mul
        (by fun_prop : Continuous fun v : E k => ‖z - v‖))).rpow_const
      (fun v => Or.inl (hpos1 v).ne')).mul
      ((continuous_const.add (by fun_prop : Continuous fun v : E k => ‖v‖)).rpow_const
        (fun v => Or.inl (hpos2 v).ne'))
  have h5 : ∫ v : E k, (1 + th * ‖z - v‖) ^ (-(100 * (k:ℝ))) * ‖locBump k v‖ ^ Q
      ≤ C₀ * ∫ v : E k, f v := by
    rw [← integral_const_mul]
    refine integral_mono_of_nonneg ?_ ?_ ?_
    · filter_upwards with v
      exact mul_nonneg (Real.rpow_nonneg (by positivity) _) (Real.rpow_nonneg (norm_nonneg _) Q)
    · refine ((hC₁ z).1.const_mul C₀).mono' (hfcont.const_mul C₀).aestronglyMeasurable ?_
      filter_upwards with v
      rw [Real.norm_of_nonneg (mul_nonneg hC₀pos.le (by simp only [hf]; positivity))]
      refine mul_le_mul_of_nonneg_left ?_ hC₀pos.le
      calc f v = (1 + ‖v‖) ^ (-(100 * (k:ℝ))) * (1 + th * ‖z - v‖) ^ (-(100 * (k:ℝ))) := by
            simp only [hf]; ring
        _ ≤ (1 + ‖v‖) ^ (-(100 * (k:ℝ))) * (1 + ‖z - v‖) ^ (-(100 * (k:ℝ))) := by
            refine mul_le_mul_of_nonneg_left ?_ (Real.rpow_nonneg (by positivity) _)
            refine Real.rpow_le_rpow_of_nonpos (hpos0 v) ?_ (by nlinarith [hknn])
            nlinarith [hth1, norm_nonneg (z - v)]
    · filter_upwards with v
      have hw : 0 ≤ (1 + th * ‖z - v‖) ^ (-(100 * (k:ℝ))) := Real.rpow_nonneg (by positivity) _
      calc (1 + th * ‖z - v‖) ^ (-(100 * (k:ℝ))) * ‖locBump k v‖ ^ Q
          ≤ (1 + th * ‖z - v‖) ^ (-(100 * (k:ℝ)))
              * (C₀ * (1 + ‖v‖) ^ (-(100 * (k:ℝ)))) :=
            mul_le_mul_of_nonneg_left (hC₀ v) hw
        _ = C₀ * f v := by simp only [hf]; ring
  -- the substitution `v = th⁻¹ • w`
  set G' : E k → ℝ := fun w => (1 + ‖th • z - w‖) ^ (-(100 * (k:ℝ)))
      * (1 + ‖th⁻¹ • w‖) ^ (-(100 * (k:ℝ))) with hG'
  have hfG' : ∀ w : E k, f (th⁻¹ • w) = G' w := by
    intro w
    simp only [hf, hG']
    have e : th * ‖z - th⁻¹ • w‖ = ‖th • z - w‖ := by
      rw [show th • z - w = th • (z - th⁻¹ • w) from by rw [smul_sub, smul_inv_smul₀ hthne],
        norm_smul, Real.norm_eq_abs, abs_of_pos hth0]
    rw [e]
  have hfg : ∫ v : E k, f v = (th ^ k)⁻¹ * ∫ w : E k, G' w := by
    have hc := MeasureTheory.Measure.integral_comp_inv_smul_of_nonneg
      (μ := (volume : Measure (E k))) (f := f) (R := th) hth0.le
    rw [finrank_euclideanSpace, Fintype.card_fin, smul_eq_mul] at hc
    rw [show (fun x : E k => f (th⁻¹ • x)) = fun w : E k => G' w from funext hfG'] at hc
    rw [hc, ← mul_assoc, inv_mul_cancel₀ hthkne, one_mul]
  have hG'bound : ∫ w : E k, G' w
      ≤ th ^ (100 * (k:ℝ)) * (C₁ * (1 + th * ‖z‖) ^ (-(100 * (k:ℝ)))) := by
    set Φ : E k → ℝ := fun w => th ^ (100 * (k:ℝ))
        * ((1 + ‖w‖) ^ (-(100 * (k:ℝ))) * (1 + ‖th • z - w‖) ^ (-(100 * (k:ℝ)))) with hΦ
    have hposw : ∀ w : E k, (0:ℝ) < 1 + ‖w‖ := fun w => by
      have h := norm_nonneg w; linarith
    have hpt : ∀ w, G' w ≤ Φ w := by
      intro w
      simp only [hG', hΦ]
      have hw1 : 1 ≤ 1 + ‖w‖ := by have h := norm_nonneg w; linarith
      have hle : (1 + ‖w‖) / th ≤ 1 + ‖th⁻¹ • w‖ := by
        rw [norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hth0), inv_mul_eq_div]
        rw [div_le_iff₀ hth0]
        nlinarith [hth1, div_mul_cancel₀ (‖w‖) hthne]
      have hb0 : 0 < (1 + ‖w‖) / th := by positivity
      have hneg : -(100 * (k:ℝ)) ≤ 0 := by nlinarith [hknn]
      have h1' : (1 + ‖th⁻¹ • w‖) ^ (-(100 * (k:ℝ)))
          ≤ ((1 + ‖w‖) / th) ^ (-(100 * (k:ℝ))) :=
        Real.rpow_le_rpow_of_nonpos hb0 hle hneg
      have h2' : ((1 + ‖w‖) / th) ^ (-(100 * (k:ℝ)))
          = th ^ (100 * (k:ℝ)) * (1 + ‖w‖) ^ (-(100 * (k:ℝ))) := by
        rw [Real.div_rpow (hposw w).le hth0.le, Real.rpow_neg hth0.le, div_inv_eq_mul]
        ring
      calc (1 + ‖th • z - w‖) ^ (-(100 * (k:ℝ))) * (1 + ‖th⁻¹ • w‖) ^ (-(100 * (k:ℝ)))
          ≤ (1 + ‖th • z - w‖) ^ (-(100 * (k:ℝ)))
              * (((1 + ‖w‖) / th) ^ (-(100 * (k:ℝ)))) :=
            mul_le_mul_of_nonneg_left h1' (Real.rpow_nonneg (by positivity) _)
        _ = th ^ (100 * (k:ℝ)) * ((1 + ‖w‖) ^ (-(100 * (k:ℝ)))
              * (1 + ‖th • z - w‖) ^ (-(100 * (k:ℝ)))) := by rw [h2']; ring
    have hΦint : Integrable Φ volume := by
      have h' : Integrable (fun w : E k => (1 + ‖w‖) ^ (-(100 * (k:ℝ)))
          * (1 + ‖th • z - w‖) ^ (-(100 * (k:ℝ)))) volume := (hC₁ (th • z)).1
      exact h'.const_mul (th ^ (100 * (k:ℝ)))
    refine le_trans (integral_mono_of_nonneg ?_ hΦint (Filter.Eventually.of_forall hpt)) ?_
    · filter_upwards with w
      simp only [hG']
      exact mul_nonneg (Real.rpow_nonneg (by positivity) _) (Real.rpow_nonneg (by positivity) _)
    · rw [integral_const_mul]
      refine mul_le_mul_of_nonneg_left ?_ (le_of_lt (Real.rpow_pos_of_pos hth0 (100 * (k:ℝ))))
      have h := (hC₁ (th • z)).2
      rw [min_self] at h
      have hnorm : ‖th • z‖ = th * ‖z‖ := by
        rw [norm_smul, Real.norm_eq_abs, abs_of_pos hth0]
      rw [hnorm] at h
      exact h
  have hzb : (1 + th * ‖z‖) ^ (-(100 * (k:ℝ))) = ballWeight k c R y := by
    have hval : th * ‖z‖ = ‖y - c‖ / R := by
      rw [hz, norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hRθ), inv_mul_eq_div,
        hRθdef]
      field_simp
    rw [hval, ballWeight_eq_rpow k c hR y]
  calc ∫ c' : E k, H c'
      = Rθ^k * ∫ v : E k, G v := by rw [h1, h2, h3]
    _ = Rθ^k * ∫ v : E k, (1 + th * ‖z - v‖) ^ (-(100 * (k:ℝ))) * ‖locBump k v‖ ^ Q := by
        rw [h4]
    _ ≤ Rθ^k * (C₀ * ∫ v : E k, f v) := mul_le_mul_of_nonneg_left h5 (by positivity)
    _ = Rθ^k * (C₀ * ((th ^ k)⁻¹ * ∫ w : E k, G' w)) := by rw [hfg]
    _ ≤ Rθ^k * (C₀ * ((th ^ k)⁻¹
          * (th ^ (100 * (k:ℝ)) * (C₁ * (1 + th * ‖z‖) ^ (-(100 * (k:ℝ))))))) := by
        refine mul_le_mul_of_nonneg_left ?_ (by positivity)
        refine mul_le_mul_of_nonneg_left ?_ hC₀pos.le
        exact mul_le_mul_of_nonneg_left hG'bound (by positivity)
    _ = Λ ^ (100 * (k:ℝ)) * (C₀ * C₁) * R^k * ballWeight k c R y := by
        rw [hzb, hRθdef, mul_pow]
        have key : th ^ k * R ^ k * (C₀ * ((th ^ k)⁻¹
              * (th ^ (100 * (k:ℝ)) * (C₁ * ballWeight k c R y))))
            = th ^ (100 * (k:ℝ)) * (C₀ * C₁) * R ^ k * ballWeight k c R y := by
          field_simp [hthkne]
        rw [key, hth]





/-! ## 5. The `λ`-enlarged decoupling predicate

The localisation step below (`localised_piece_isFourierRep`) shows that the localised pieces
`locWeight k c' (lwScale k * R) · E_{J_i}g` have Fourier support inside the plate
`plate k (1/N) (pieceCenter N i)`, which is the plate of the piece `J_i` *enlarged by the fixed
factor* `2` (the plate `piecePlate k N i` of `BilinearReduction.lean` is
`plate k (1/(2*N)) (pieceCenter N i)`).  We therefore record the decoupling inequality for
enlarged plates as a separate predicate: GLYZ's own theorem is the case `λ = 1`, and the bridge
needs `λ = 2`.  Since a larger `λ` means a *larger* plate, i.e. a weaker hypothesis, the
statement is antitone in `λ`. -/

/-- The `λ`-enlarged plate of the `j`-th piece at level `m`: `λ = 1` is `piecePlate`. -/
noncomputable def plateScale (k m : ℕ) (lam : ℝ) (j : Fin m) : Set (E k) :=
  plate k (lam / (2 * m)) (pieceCenter m j)

/-- **The `λ`-enlarged ℓ²-decoupling inequality** at scale `m`: the same as `DecLin`, but for
functions whose Fourier transform is supported in the plate of the `j`-th piece enlarged by the
factor `λ ≥ 1`. -/
def DecLinScale (k : ℕ) (m : ℕ) (lam : ℝ) (C : ℝ≥0∞) : Prop :=
  ∀ f : Fin m → E k → ℂ,
    (∀ j, IsFourierRep k (plateScale k m lam j) (f j)) →
    lpNorm k (pE k) (fun x => ∑ j, f j x) ≤ C * l2Norm (fun j => lpNorm k (pE k) (f j))

/-- `λ = 1` is the original `DecLin`. -/
lemma decLinScale_one_iff (k m : ℕ) (C : ℝ≥0∞) :
    DecLinScale k m 1 C ↔ DecLin k m C := by
  have h : ∀ j : Fin m, plateScale k m 1 j = piecePlate k m j := by
    intro j
    rw [plateScale, piecePlate]
  simp only [DecLinScale, DecLin, h]

/-- Monotonicity in the constant. -/
lemma DecLinScale_mono {k m : ℕ} {lam : ℝ} {C C' : ℝ≥0∞} (h : C ≤ C')
    (hD : DecLinScale k m lam C) : DecLinScale k m lam C' :=
  fun f hf => (hD f hf).trans (mul_le_mul_left h _)

/-- **The plate is monotone in its scale parameter.**  With the fixed directions
`A_{1,c}e_j` (the columns of `A_{d,c}/d^{j+1}`, independent of `d`) the plate
`plate k d c` is a parallelepiped of semi-axes `d^{j+1}(j+1)!` about `γ(c)`; hence
`plate k d c ⊆ plate k d' c` for `0 ≤ d ≤ d'`. -/
lemma plate_mono {k : ℕ} {c d d' : ℝ} (hd : 0 ≤ d) (hdd : d ≤ d') :
    plate k d c ⊆ plate k d' c := by
  rcases eq_or_lt_of_le hdd with h | h
  · rw [h]
  have hd' : 0 < d' := lt_of_le_of_lt hd h
  intro x hx
  obtain ⟨y, hy, hyx⟩ := hx
  have hyi : ∀ i : Fin k, |y i| ≤ ((i.val + 1).factorial : ℝ) := hy
  refine ⟨WithLp.toLp 2 (fun i : Fin k => (d / d') ^ (i.val + 1) * y i), ?_, ?_⟩
  · intro i
    rw [WithLp.ofLp_toLp, abs_mul,
      abs_of_nonneg (by positivity : (0:ℝ) ≤ (d / d') ^ (i.val + 1))]
    have hle1 : (d / d') ^ (i.val + 1) ≤ 1 :=
      pow_le_one₀ (by positivity) (by rw [div_le_one hd']; exact hdd)
    calc (d / d') ^ (i.val + 1) * |y i| ≤ 1 * |y i| :=
          mul_le_mul_of_nonneg_right hle1 (abs_nonneg _)
      _ ≤ ((i.val + 1).factorial : ℝ) := by rw [one_mul]; exact hyi i
  · rw [← hyx]
    have hkey : affVecDual k d' c (WithLp.toLp 2 (fun i : Fin k => (d / d') ^ (i.val + 1) * y i))
        = affVecDual k d c y := by
      ext l
      rw [affVecDual_apply, affVecDual_apply]
      refine Finset.sum_congr rfl fun j _ => ?_
      have hj : (d / d') ^ (j.val + 1) * d' ^ (j.val + 1) = d ^ (j.val + 1) := by
        rw [div_pow, div_mul_cancel₀]
        exact pow_ne_zero _ (ne_of_gt hd')
      simp only [WithLp.ofLp_toLp]
      rw [show ((d / d') ^ (j.val + 1) * y j) * ((l.val + 1).choose (j.val + 1) : ℝ)
            * d' ^ (j.val + 1) * c ^ (l.val - j.val)
          = y j * ((l.val + 1).choose (j.val + 1) : ℝ) * d ^ (j.val + 1)
              * c ^ (l.val - j.val) from by rw [← hj]; ring]
    rw [affMap_apply, affMap_apply, hkey]

end Submission.Vinogradov
