/-
# The single-scale model approximation at arithmetic height `(0,0)`
(`Work.KMTAreas.A7.LoErrSingleScale00`)

Target: `Work.KMTAreas.A7.LoErrStatement P p₁ p₂`, the paper's §6 Proposition `mod-approx` at
`l₁ = l₂ = 0` (Krause--Mirek--Tao, *Pointwise ergodic theorems for non-conventional bilinear
polynomial averages*, Ann. of Math. **195** (3) 2022).

## The route

* On the guard `loGuard` the concrete column is the bilinear convolution
  `bilinOp (coeff2 (symC ρ P ⌊a n⌋ 0 0 k₁ k₂)) f g` (`loMainPart_eq_bilinOp_symC` below) and the
  level-`0` model is `bilinOp (coeff2 (symM ρ P ⌊a n⌋ 0 0 k₁ k₂)) f g`
  (`loModel_eq_bilinOp_symM`), where `symC`, `symM` are the symbols of area A6
  (`Work.KMTPlan.A6`); the §6 collapse `symC − symM = symD` (`loSymCollapse`) turns the difference
  into `bilinOp (coeff2 (symD …)) f g`, with `symD` the aliasing-fibre sum of the paper's symbol
  difference `M₀ = weylAvg − m_Ẑ·m̃_{N,ℝ}` against the two §5 bumps.
* The `ℓ¹(ℤ²)` mass of `coeff2 (symD ρ P N 0 0 k₁ k₂)` is then bounded by the paper's
  `crude-mult`(ii) (`SymToolbox_tsum_coeff2_le`) from the `ξ`-derivative bounds of `symD`
  (`loSymD_deriv_bound`, whose analytic content is `Work.A7.M0SharpBound` and
  `Work.A7.ModelApproxCore_M0_deriv_bound`), and `BilinOpLp` (Young's inequality for `bilinOp`)
  converts the mass bound into the `ℓ^p` estimate.
* Off the guard both tuples vanish, so the estimate holds trivially.
* The guard gives `k + 2u ≤ Log N` (`u = uScale ρ L`, `L = max k₁ k₂`), which is exactly one unit
  short of the window slack `k + 2u + 1 ≤ Log N` needed by the `m_*`-window of the §6 functional
  calculus.  Where the slack fails one has `k + 2u = Log N > 2^u`, hence
  `L + 2u ≥ k + 2u > 2^u`; since `uScale ρ L` grows doubly exponentially in `L`
  (`uScale_growth`) this forces `L < L₀(ρ)`, and then `Log N ≤ L₀ + 2uScale ρ L₀`, so `N` is
  bounded in terms of `ρ`.  On that (finitely many, `ρ`-dependent) regime the crude
  `ℓ^p` bound `loMainPart_sub_loModel_crude` — uniform in everything, with an absolute constant —
  is absorbed by the constant `K(Λ)`.
-/
import Mathlib
import Submission.Work.KMTAreas.A7.LoErrSymD
import Submission.Work.KMTPlan.A6.SymToolbox_tsum_coeff2_le
import Submission.Work.KMTPlan.A6.symD_period_contDiff
import Submission.Work.KMTPlan.A6.symC_symM_summable
import Submission.Work.KMTAreas.A7.goodRegime
import Submission.Work.KMTAreas.A7.farey_and_strict_of_large_L
import Submission.Work.KMTAreas.A7.LoModelEqBilinOpSymM
import Submission.Work.KMTAreas.A7.LoMainSubLoModelCrude

set_option autoImplicit false
set_option maxHeartbeats 8000000

namespace Work.KMTAreas.A7

noncomputable section

open MeasureTheory Polynomial Finset Filter Topology
open scoped ENNReal NNReal BigOperators
open PointwiseErgodicTheorems Submission.PointwiseErgodicTheorems
open Work.Analysis.IonescuWainger Work.Analysis.IWMultiplier
open Work.Analysis.EndVar

/-! ## Additivity of `bilinOp` in its kernel -/

/-- **The bilinear convolution operator is additive in its kernel** (for bounded inputs and
absolutely summable kernels). -/
theorem bilinOp_sub_kernel {K K' : ℤ → ℤ → ℂ}
    (hK : Summable fun p : ℤ × ℤ => ‖K p.1 p.2‖)
    (hK' : Summable fun p : ℤ × ℤ => ‖K' p.1 p.2‖) {u v : ℤ → ℂ} {Cu Cv : ℝ}
    (hu : ∀ y, ‖u y‖ ≤ Cu) (hv : ∀ y, ‖v y‖ ≤ Cv) (x : ℤ) :
    bilinOp K u v x - bilinOp K' u v x = bilinOp (fun a b => K a b - K' a b) u v x := by
  have hCu : 0 ≤ Cu := le_trans (norm_nonneg _) (hu 0)
  have hCv : 0 ≤ Cv := le_trans (norm_nonneg _) (hv 0)
  have hsum1 : Summable fun p : ℤ × ℤ => K p.1 p.2 * u (x - p.1) * v (x - p.2) := by
    refine Summable.of_norm_bounded (hK.mul_right (Cu * Cv)) (fun p => ?_)
    rw [norm_mul, norm_mul]
    have h1 : ‖K p.1 p.2‖ * ‖u (x - p.1)‖ ≤ ‖K p.1 p.2‖ * Cu :=
      mul_le_mul_of_nonneg_left (hu _) (norm_nonneg _)
    have h2 : ‖K p.1 p.2‖ * ‖u (x - p.1)‖ * ‖v (x - p.2)‖ ≤ ‖K p.1 p.2‖ * Cu * Cv :=
      mul_le_mul h1 (hv _) (norm_nonneg _) (mul_nonneg (norm_nonneg _) hCu)
    calc ‖K p.1 p.2‖ * ‖u (x - p.1)‖ * ‖v (x - p.2)‖ ≤ ‖K p.1 p.2‖ * Cu * Cv := h2
      _ = ‖K p.1 p.2‖ * (Cu * Cv) := by ring
  have hsum2 : Summable fun p : ℤ × ℤ => K' p.1 p.2 * u (x - p.1) * v (x - p.2) := by
    refine Summable.of_norm_bounded (hK'.mul_right (Cu * Cv)) (fun p => ?_)
    rw [norm_mul, norm_mul]
    have h1 : ‖K' p.1 p.2‖ * ‖u (x - p.1)‖ ≤ ‖K' p.1 p.2‖ * Cu :=
      mul_le_mul_of_nonneg_left (hu _) (norm_nonneg _)
    have h2 : ‖K' p.1 p.2‖ * ‖u (x - p.1)‖ * ‖v (x - p.2)‖ ≤ ‖K' p.1 p.2‖ * Cu * Cv :=
      mul_le_mul h1 (hv _) (norm_nonneg _) (mul_nonneg (norm_nonneg _) hCu)
    calc ‖K' p.1 p.2‖ * ‖u (x - p.1)‖ * ‖v (x - p.2)‖ ≤ ‖K' p.1 p.2‖ * Cu * Cv := h2
      _ = ‖K' p.1 p.2‖ * (Cu * Cv) := by ring
  have hKsub : Summable fun p : ℤ × ℤ => ‖K p.1 p.2 - K' p.1 p.2‖ :=
    Summable.of_nonneg_of_le (fun p => norm_nonneg _) (fun p => norm_sub_le _ _) (hK.add hK')
  rw [Work.A7.ModelApproxCore_aux.bilinOp_eq_tsum hK hu hv x,
    Work.A7.ModelApproxCore_aux.bilinOp_eq_tsum hK' hu hv x,
    Work.A7.ModelApproxCore_aux.bilinOp_eq_tsum hKsub hu hv x,
    ← Summable.tsum_sub hsum1 hsum2]
  exact tsum_congr (fun p => by ring)

/-! ## The analytic inputs of the assembly -/

/-- **The level-`0` model column is `bilinOp` with the kernel `coeff2 symM`.**  On the guard and
under the window slack `max k₁ k₂ + 2u + 1 ≤ Log N` (which makes the §6 window `m_* = η_{≤-2u}`
equal to `1` on the support of the modulated §5 bumps), the `t`-integral of the products of the
two modulated height-`0` multipliers is the bilinear convolution with the `symM`-kernel. -/
theorem loModel_eq_bilinOp_symM (ρ : ℝ) (hρ : 0 < ρ) (hρ1 : ρ ≤ 1) (P : Polynomial ℤ)
    (C₀ : ℕ) (a : ℕ → NNReal) (f g : ℤ → ℂ) (k₁ k₂ n : ℕ) (x : ℤ)
    (hd : 1 ≤ P.natDegree)
    (hf : Work.KMTAreas.A5.BoundedZ f) (hg : Work.KMTAreas.A5.BoundedZ g)
    (h : loGuard ρ C₀ a 0 0 k₁ k₂ n)
    (hC2 : max k₁ k₂ + 2 * uScale ρ (max k₁ k₂) + 1
      ≤ (Work.Analysis.EndVar.logN (Nat.floor (a n))).toNat) :
    loModelTuple ρ P C₀ a f g 0 0 k₁ k₂ n x
      = bilinOp (fun u v =>
          Work.KMTPlan.A6.coeff2 (Work.KMTPlan.A6.symM ρ P (Nat.floor (a n)) 0 0 k₁ k₂) u v)
          f g x := by
  exact LoModelEqBilinOpSymM ρ hρ hρ1 P C₀ a f g k₁ k₂ n x hd hf hg h hC2

/-- **The §6 collapse `symC − symM = symD` at arithmetic heights `(0,0)`** (the paper's
Proposition `mod-approx` at the level of symbols, restricted to `l₁ = l₂ = 0`). -/
theorem loSymCollapse (P : Polynomial ℤ) (hd : 1 ≤ P.natDegree) (ρ : ℝ) (hρ : 0 < ρ)
    (hρ1 : ρ ≤ 1) (N k₁ k₂ : ℕ) (hN : 1 ≤ N)
    (hC2 : max k₁ k₂ + 2 * uScale ρ (max k₁ k₂) + 1
      ≤ (Work.Analysis.EndVar.logN N).toNat) (x y : ℝ) :
    Work.KMTPlan.A6.symC ρ P N 0 0 k₁ k₂ x y - Work.KMTPlan.A6.symM ρ P N 0 0 k₁ k₂ x y
      = Work.KMTPlan.A6.symD ρ P N 0 0 k₁ k₂ x y := by
  have hlcL : Work.KMTPlan.A6.lcL 0 0 k₁ k₂ = max k₁ k₂ := by
    simp [Work.KMTPlan.A6.lcL]
  refine Work.KMTPlan.A6.symC_sub_symM_eq_symD P hd ρ hρ hρ1 N 0 0 k₁ k₂ hN ?_ ?_ x y
  · rw [hlcL]; exact hC2
  · rw [hlcL]
    exact nonAliasing_iwArithFreqs_zero ρ (uScale_pos hρ.le (max k₁ k₂))

/-- **The crude `ℓ^p` bound for the level-`0` model-approximation error.**  Uniformly on the guard
(and in all the parameters, with an absolute constant) the difference is bounded by
`C ‖f‖_{ℓ^{p₁}} ‖g‖_{ℓ^{p₂}}`. -/
theorem loMainPart_sub_loModel_crude (P : Polynomial ℤ) (p₁ p₂ : ENNReal)
    (hdeg : 2 ≤ P.natDegree) (hp₁ : 1 < p₁) (htp₁ : p₁ < ⊤) (hp₂ : 1 < p₂) (htp₂ : p₂ < ⊤)
    (hsum : p₁⁻¹ + p₂⁻¹ ≤ 1) :
    ∃ C : ℝ, 0 < C ∧ ∀ (ρ : ℝ) (C₀ : ℕ) (a : ℕ → NNReal) (k₁ k₂ n : ℕ) (f g : ℤ → ℂ),
      loGuard ρ C₀ a 0 0 k₁ k₂ n →
      MeasureTheory.eLpNorm (fun x : ℤ => mainPartTuple ρ P C₀ a f g 0 0 k₁ k₂ n x
          - loModelTuple ρ P C₀ a f g 0 0 k₁ k₂ n x)
        (p₁⁻¹ + p₂⁻¹)⁻¹ MeasureTheory.Measure.count
        ≤ ENNReal.ofReal C * MeasureTheory.eLpNorm f p₁ MeasureTheory.Measure.count
          * MeasureTheory.eLpNorm g p₂ MeasureTheory.Measure.count := by
  exact LoMainSubLoModelCrude P p₁ p₂ hdeg hp₁ htp₁ hp₂ htp₂ hsum

/-- **The growth of `uScale`**: for `ρ > 0` there is `L₀` such that for all `L ≥ L₀` the auxiliary
scale `uScale ρ L` (which is `⌊2^{2ρL}⌋`, hence doubly exponential in `L`) dominates `L + 2u`. -/
theorem uScale_growth (ρ : ℝ) (hρ : 0 < ρ) :
    ∃ L₀ : ℕ, ∀ L : ℕ, L₀ ≤ L → L + 2 * uScale ρ L + 1 ≤ 2 ^ (uScale ρ L) := by
  obtain ⟨L₀, hL₀⟩ := exists_uScale_ge ρ hρ
  refine ⟨L₀, fun L hL => ?_⟩
  obtain ⟨h1, h2⟩ := hL₀ L hL
  have h3 := three_mul_add_one_le_two_pow h2
  omega

/-! ## The target -/

/-- **The single-scale model-approximation error at arithmetic height `(0,0)`** (the paper's §6
Proposition `mod-approx` at `l₁ = l₂ = 0`), in the shape consumed by
`Work.KMTAreas.A7.ModelApproxLo`.  See the module docstring for the route. -/
theorem bound_of_eLpNorm_ne_top {p : ENNReal} (hp : 1 < p) {f : ℤ → ℂ}
    (hf : eLpNorm f p Measure.count ≠ ⊤) : Work.KMTAreas.A5.BoundedZ f := by
  have hp0 : p ≠ 0 := by
    intro h; rw [h] at hp; exact absurd hp (by norm_num)
  have hdirac : ∀ x : ℤ, Measure.dirac x ≤ (Measure.count : Measure ℤ) := by
    intro x
    rw [Measure.count]
    exact Measure.le_sum Measure.dirac x
  refine ⟨(eLpNorm f p Measure.count).toReal, fun x => ?_⟩
  have h1 : ‖f x‖ₑ ≤ eLpNorm f p Measure.count := by
    rw [← eLpNorm_dirac f x hp0]
    exact eLpNorm_mono_measure f (hdirac x)
  have h2 := ENNReal.toReal_mono (lt_top_iff_ne_top.mpr hf).ne h1
  rwa [bilin_enorm_eq_ofReal_norm (f x), ENNReal.toReal_ofReal (norm_nonneg _)] at h2

/-- The Fourier coefficient functional `coeff2` is compatible with pointwise equality. -/
lemma coeff2_congr_lo {σ τ : ℝ → ℝ → ℂ} (h : ∀ x y, σ x y = τ x y) (p₁ p₂ : ℤ) :
    Work.KMTPlan.A6.coeff2 σ p₁ p₂ = Work.KMTPlan.A6.coeff2 τ p₁ p₂ := by
  refine intervalIntegral.integral_congr (fun x _ => ?_)
  refine intervalIntegral.integral_congr (fun y _ => ?_)
  rw [h x y]

/-- `(N⁻¹)^{1-j₁}·((N^d)⁻¹)^{1-j₂} = N^{j₁ + d j₂ - d - 1}` for `N ≥ 1`. -/
lemma inv_rpow_prod_lo (N d j₁ j₂ : ℕ) (hN : 1 ≤ N) :
    ((N : ℝ))⁻¹ ^ ((1 : ℝ) - (j₁ : ℝ)) * (((N : ℝ) ^ d)⁻¹) ^ ((1 : ℝ) - (j₂ : ℝ))
      = (N : ℝ) ^ ((((j₁ : ℤ) + (d : ℤ) * (j₂ : ℤ) - (d : ℤ) - 1 : ℤ)) : ℝ) := by
  have hN0 : (0 : ℝ) < (N : ℝ) := by exact_mod_cast hN
  have hN1 : (0 : ℝ) ≤ (N : ℝ) := hN0.le
  have e1 : ((N : ℝ))⁻¹ ^ ((1 : ℝ) - (j₁ : ℝ)) = (N : ℝ) ^ (-(1 - (j₁ : ℝ))) := by
    rw [Real.inv_rpow hN1, ← Real.rpow_neg hN1]
  have e2 : (((N : ℝ) ^ d)⁻¹) ^ ((1 : ℝ) - (j₂ : ℝ))
      = (N : ℝ) ^ (-((d : ℝ) * (1 - (j₂ : ℝ)))) := by
    rw [← Real.rpow_natCast (N : ℝ) d,
      Real.inv_rpow (show (0 : ℝ) ≤ (N : ℝ) ^ ((d : ℕ) : ℝ) from by positivity),
      ← Real.rpow_neg (show (0 : ℝ) ≤ (N : ℝ) ^ ((d : ℕ) : ℝ) from by positivity),
      ← Real.rpow_mul hN1]
    congr 1
    ring
  rw [e1, e2, ← Real.rpow_add hN0]
  congr 1
  push_cast
  ring

lemma lo_exceptional_N_bound (ρ : ℝ) (hρ : 0 < ρ) (L₀ : ℕ)
    (hL₀ : ∀ L : ℕ, L₀ ≤ L → L + 2 * uScale ρ L + 1 ≤ 2 ^ (uScale ρ L))
    {C₀ : ℕ} {a : ℕ → NNReal} {k₁ k₂ n : ℕ}
    (hsplit : splitCut ρ (max k₁ k₂) < Nat.floor (a n))
    (hreg : k₁ + 2 * uScale ρ (max k₁ k₂) ≤ (Work.Analysis.EndVar.logN (Nat.floor (a n))).toNat
      ∧ k₂ + 2 * uScale ρ (max k₁ k₂) ≤ (Work.Analysis.EndVar.logN (Nat.floor (a n))).toNat)
    (hC2 : ¬ (max k₁ k₂ + 2 * uScale ρ (max k₁ k₂) + 1
      ≤ (Work.Analysis.EndVar.logN (Nat.floor (a n))).toNat)) :
    Nat.floor (a n) ≤ 2 ^ (L₀ + 2 * uScale ρ L₀ + 1) := by
  have hsplit0 : 2 ^ (2 ^ uScale ρ (max k₁ k₂)) < Nat.floor (a n) := hsplit
  set L : ℕ := max k₁ k₂ with hLdef
  set u : ℕ := uScale ρ (max k₁ k₂) with hudef
  set N : ℕ := Nat.floor (a n) with hNdef
  set M : ℕ := (Work.Analysis.EndVar.logN N).toNat with hMdef
  have hk1L : k₁ ≤ L := by rw [hLdef]; exact le_max_left _ _
  have hk2L : k₂ ≤ L := by rw [hLdef]; exact le_max_right _ _
  -- the exceptional case is exactly `M = L + 2u`
  have hMeq : M = L + 2 * u := by
    have h1 : L + 2 * u ≤ M := by omega
    have h2 : M ≤ L + 2 * u := by
      have := not_le.mp hC2; omega
    omega
  have hLlt : L < L₀ := by
    by_contra hnot
    have hstr := hL₀ L (not_lt.mp hnot)
    have hu2 : u = uScale ρ L := by rw [hudef, ← hLdef]
    have hsplit' : 2 ^ (2 ^ u) < N := hsplit0
    have hlog1 : 2 ^ u ≤ Nat.log 2 N := Nat.le_log_of_pow_le (by norm_num) (le_of_lt hsplit')
    have hlog2 : Nat.log 2 N ≤ Nat.log 2 (max N 2) := Nat.log_mono_right (le_max_left N 2)
    have hMval : M = Nat.log 2 (max N 2) := by
      rw [hMdef, hNdef, Work.Analysis.EndVar.logN, Int.toNat_natCast]
    rw [← hu2] at hstr
    have hMge : L + 2 * u + 1 ≤ M := by
      rw [hMval]
      exact le_trans hstr (le_trans hlog1 hlog2)
    exact hC2 hMge
  have hule : u ≤ uScale ρ L₀ := by
    rw [hudef]; exact uScale_mono hρ.le (le_of_lt hLlt)
  have hMle : M ≤ L₀ + 2 * uScale ρ L₀ := by omega
  have hNlt : N < 2 ^ (M + 1) := by
    have h := Nat.lt_pow_succ_log_self (by norm_num : 1 < 2) (max N 2)
    have hMval : M = Nat.log 2 (max N 2) := by
      rw [hMdef, hNdef, Work.Analysis.EndVar.logN, Int.toNat_natCast]
    have hle : N ≤ max N 2 := le_max_left N 2
    rw [hMval]
    exact lt_of_le_of_lt hle h
  calc N ≤ 2 ^ (M + 1) := le_of_lt hNlt
    _ ≤ 2 ^ (L₀ + 2 * uScale ρ L₀ + 1) := Nat.pow_le_pow_right (by norm_num) (by omega)

/-- **The weight arithmetic of the main case**: the `crude-mult` mass bound `40 A` is dominated by
`KΛ · 2^{c' L} · N⁻¹` with `c' = Kd + 2d`, `L = max k₁ k₂`. -/
lemma lo_weight_bound (P : Polynomial ℤ) (hd : 1 ≤ P.natDegree)
    {D Kd Cc : ℝ} (hD : 0 < D) (hKd : 0 ≤ Kd) {L₀ : ℕ} {ρ : ℝ} {N k₁ k₂ : ℕ}
    (hN : 1 ≤ N) :
    40 * (D * (2 : ℝ) ^ (Kd * ((max k₁ k₂ : ℕ) : ℝ))
        * (1 + (Work.A7.Sval P k₁ k₂) ^ 2 / (N : ℝ)) * ((N : ℝ))⁻¹)
      ≤ (max (320 * D) (Cc * (((2 : ℕ) ^ (L₀ + 2 * uScale ρ L₀ + 1) : ℕ) : ℝ)))
        * (2 : ℝ) ^ ((Kd + 2 * (P.natDegree : ℝ)) * ((max k₁ k₂ : ℕ) : ℝ)) * ((N : ℝ))⁻¹ := by
  have hN0 : (0 : ℝ) < (N : ℝ) := by exact_mod_cast hN
  have hN1 : (1 : ℝ) ≤ (N : ℝ) := by exact_mod_cast hN
  set L : ℝ := ((max k₁ k₂ : ℕ) : ℝ) with hLdef
  set d : ℝ := (P.natDegree : ℝ) with hddef
  have hLnn : 0 ≤ L := by rw [hLdef]; positivity
  have hd1 : (1 : ℝ) ≤ d := by rw [hddef]; exact_mod_cast hd
  have hk1 : (k₁ : ℝ) ≤ L := by rw [hLdef]; exact_mod_cast (le_max_left k₁ k₂)
  have hk2 : (k₂ : ℝ) ≤ L := by rw [hLdef]; exact_mod_cast (le_max_right k₁ k₂)
  have hb : (2 : ℝ) ^ (d * L) * 2 = (2 : ℝ) ^ (d * L + 1) := by
    rw [Real.rpow_add (by norm_num), Real.rpow_one]
  have hSval : Work.A7.Sval P k₁ k₂ ≤ (2 : ℝ) ^ (d * L + 1) := by
    have h1 : (2 : ℝ) ^ k₁ ≤ (2 : ℝ) ^ (d * L) := by
      rw [← Real.rpow_natCast (2 : ℝ) k₁]
      exact Real.rpow_le_rpow_of_exponent_le (by norm_num) (by nlinarith)
    have h2 : (2 : ℝ) ^ (P.natDegree * k₂) ≤ (2 : ℝ) ^ (d * L) := by
      rw [← Real.rpow_natCast (2 : ℝ) (P.natDegree * k₂)]
      refine Real.rpow_le_rpow_of_exponent_le (by norm_num) ?_
      rw [Nat.cast_mul, hddef]
      nlinarith
    simp only [Work.A7.Sval]
    linarith
  have hS2 : (Work.A7.Sval P k₁ k₂) ^ 2 ≤ (2 : ℝ) ^ (2 * d * L + 2) := by
    have hSnn : (0 : ℝ) ≤ Work.A7.Sval P k₁ k₂ := by
      simp only [Work.A7.Sval]; positivity
    have h1 : (Work.A7.Sval P k₁ k₂) ^ 2 ≤ ((2 : ℝ) ^ (d * L + 1)) ^ 2 :=
      pow_le_pow_left₀ hSnn hSval 2
    refine h1.trans (le_of_eq ?_)
    rw [← Real.rpow_natCast ((2 : ℝ) ^ (d * L + 1)) 2,
      ← Real.rpow_mul (show (0 : ℝ) ≤ 2 by norm_num)]
    congr 1
    ring
  have hSN : (Work.A7.Sval P k₁ k₂) ^ 2 / (N : ℝ) ≤ (2 : ℝ) ^ (2 * d * L + 2) := by
    rw [div_le_iff₀ hN0]
    nlinarith [hS2, hN1, Real.rpow_pos_of_pos (by norm_num : (0 : ℝ) < 2) (2 * d * L + 2)]
  have hbase : 1 + (Work.A7.Sval P k₁ k₂) ^ 2 / (N : ℝ) ≤ (2 : ℝ) ^ (2 * d * L + 3) := by
    have hX : (1 : ℝ) ≤ (2 : ℝ) ^ (2 * d * L + 2) :=
      Real.one_le_rpow (by norm_num) (by positivity)
    have hY : (2 : ℝ) ^ (2 * d * L + 3) = (2 : ℝ) ^ (2 * d * L + 2) * 2 := by
      rw [show 2 * d * L + 3 = 2 * d * L + 2 + 1 by ring, Real.rpow_add (by norm_num),
        Real.rpow_one]
    rw [hY]; linarith
  have hstep : 40 * (D * (2 : ℝ) ^ (Kd * L) * (1 + (Work.A7.Sval P k₁ k₂) ^ 2 / (N : ℝ))
        * ((N : ℝ))⁻¹)
      ≤ 40 * (D * (2 : ℝ) ^ (Kd * L) * (2 : ℝ) ^ (2 * d * L + 3) * ((N : ℝ))⁻¹) := by
    have h2 := mul_le_mul_of_nonneg_left hbase
      (show (0 : ℝ) ≤ D * (2 : ℝ) ^ (Kd * L) by positivity)
    have h3 := mul_le_mul_of_nonneg_right h2 (le_of_lt (inv_pos.mpr hN0))
    exact mul_le_mul_of_nonneg_left h3 (by norm_num)
  have hA1 : (2 : ℝ) ^ (2 * d * L + 3) = 8 * (2 : ℝ) ^ (2 * d * L) := by
    rw [Real.rpow_add (by norm_num : (0 : ℝ) < 2),
      show (2 : ℝ) ^ (3 : ℝ) = 8 from by norm_num]
    ring
  have hA2 : (2 : ℝ) ^ ((Kd + 2 * d) * L) = (2 : ℝ) ^ (Kd * L) * (2 : ℝ) ^ (2 * d * L) := by
    rw [show (Kd + 2 * d) * L = Kd * L + 2 * d * L by ring, Real.rpow_add (by norm_num)]
  have hLHS : 40 * (D * (2 : ℝ) ^ (Kd * L) * (2 : ℝ) ^ (2 * d * L + 3) * ((N : ℝ))⁻¹)
      = 320 * D * (2 : ℝ) ^ ((Kd + 2 * d) * L) * ((N : ℝ))⁻¹ := by
    rw [hA1, hA2]; ring
  have hfin : 320 * D * (2 : ℝ) ^ ((Kd + 2 * d) * L) * ((N : ℝ))⁻¹
      ≤ (max (320 * D) (Cc * (((2 : ℕ) ^ (L₀ + 2 * uScale ρ L₀ + 1) : ℕ) : ℝ)))
        * (2 : ℝ) ^ ((Kd + 2 * d) * L) * ((N : ℝ))⁻¹ :=
    mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right (le_max_left _ _) (Real.rpow_nonneg (by norm_num) _))
      (le_of_lt (inv_pos.mpr hN0))
  calc 40 * (D * (2 : ℝ) ^ (Kd * L) * (1 + (Work.A7.Sval P k₁ k₂) ^ 2 / (N : ℝ))
        * ((N : ℝ))⁻¹)
      ≤ 40 * (D * (2 : ℝ) ^ (Kd * L) * (2 : ℝ) ^ (2 * d * L + 3) * ((N : ℝ))⁻¹) := hstep
    _ = 320 * D * (2 : ℝ) ^ ((Kd + 2 * d) * L) * ((N : ℝ))⁻¹ := hLHS
    _ ≤ (max (320 * D) (Cc * (((2 : ℕ) ^ (L₀ + 2 * uScale ρ L₀ + 1) : ℕ) : ℝ)))
        * (2 : ℝ) ^ ((Kd + 2 * d) * L) * ((N : ℝ))⁻¹ := hfin


/-- The constant `K(Λ)` of the assembly: it dominates both the `320 D` of the main case and the
absolute crude constant `Cc` of the exceptional case (where `N ≤ 2^{L₀+2u}`). -/
noncomputable def loK (D Cc : ℝ) (hD : 0 < D) (L₀ : ℕ) (ρ : ℝ) : NNReal :=
  ⟨max (320 * D) (Cc * (((2 : ℕ) ^ (L₀ + 2 * uScale ρ L₀ + 1) : ℕ) : ℝ)),
    le_max_of_le_left (by linarith)⟩

/-- **The weight arithmetic of the exceptional case.**  Since `N ≤ 2^{L₀ + 2 u}` there, the
absolute crude constant is dominated by the `K(Λ)` of the target times the weight. -/
lemma lo_exceptional_weight (P : Polynomial ℤ) {D Kd Cc : ℝ} (hD : 0 < D) (hKd : 0 ≤ Kd)
    {L₀ : ℕ} {ρ : ℝ} {N k₁ k₂ : ℕ} (hN : 1 ≤ N)
    (hNbound : N ≤ 2 ^ (L₀ + 2 * uScale ρ L₀ + 1)) :
    ENNReal.ofReal Cc
      ≤ (loK D Cc hD L₀ ρ : ENNReal)
        * ENNReal.ofReal ((2 : ℝ) ^ ((Kd + 2 * (P.natDegree : ℝ)) * (lmaxR 0 0 k₁ k₂)))
        * ENNReal.ofReal (((N : ℝ))⁻¹) := by
  by_cases hCc : Cc ≤ 0
  · rw [ENNReal.ofReal_of_nonpos hCc]; exact zero_le
  · have hCc' : 0 < Cc := not_le.mp hCc
    set T : ℝ := (((2 : ℕ) ^ (L₀ + 2 * uScale ρ L₀ + 1) : ℕ) : ℝ) with hTdef
    have hT1 : (1 : ℝ) ≤ T := by
      rw [hTdef]; exact_mod_cast Nat.one_le_two_pow
    have hNT : (N : ℝ) ≤ T := by rw [hTdef]; exact_mod_cast hNbound
    have hN0 : (0 : ℝ) < (N : ℝ) := by exact_mod_cast hN
    have hTpos : (0 : ℝ) < T := lt_of_lt_of_le (by norm_num) hT1
    have hKval : ((loK D Cc hD L₀ ρ : NNReal) : ℝ) = max (320 * D) (Cc * T) := rfl
    have hloKpos : (0 : ℝ) < ((loK D Cc hD L₀ ρ : NNReal) : ℝ) := by
      rw [hKval]; exact lt_of_lt_of_le (mul_pos hCc' hTpos) (le_max_right _ _)
    have h3 : Cc ≤ ((loK D Cc hD L₀ ρ : NNReal) : ℝ) / (N : ℝ) := by
      rw [hKval, le_div_iff₀ hN0]
      calc Cc * (N : ℝ) ≤ Cc * T := mul_le_mul_of_nonneg_left hNT (le_of_lt hCc')
        _ ≤ max (320 * D) (Cc * T) := le_max_right _ _
    have h4 : ENNReal.ofReal Cc
        ≤ (loK D Cc hD L₀ ρ : ENNReal) * ENNReal.ofReal (((N : ℝ))⁻¹) := by
      refine (ENNReal.ofReal_le_ofReal h3).trans (le_of_eq ?_)
      rw [div_eq_mul_inv, ENNReal.ofReal_mul (le_of_lt hloKpos), ENNReal.ofReal_coe_nnreal]
    refine h4.trans ?_
    have hLm : (0 : ℝ) ≤ lmaxR 0 0 k₁ k₂ := by
      have h1 : Work.Analysis.EndVar.lmax 0 0 (k₁ : ℤ) (k₂ : ℤ) = ((max k₁ k₂ : ℕ) : ℤ) := by
        rw [Work.Analysis.EndVar.lmax, Nat.cast_max, max_self]
        exact max_eq_right (le_trans (Int.natCast_nonneg k₁) (le_max_left _ _))
      have h2 : lmaxR 0 0 k₁ k₂ = ((max k₁ k₂ : ℕ) : ℝ) := by
        rw [lmaxR, h1]; push_cast; ring
      rw [h2]; positivity
    have hB1 : (1 : ENNReal)
        ≤ ENNReal.ofReal ((2 : ℝ) ^ ((Kd + 2 * (P.natDegree : ℝ)) * (lmaxR 0 0 k₁ k₂))) := by
      rw [← ENNReal.ofReal_one]
      refine ENNReal.ofReal_le_ofReal ?_
      exact Real.one_le_rpow (by norm_num)
        (mul_nonneg (add_nonneg hKd (by positivity)) hLm)
    exact mul_le_mul_of_nonneg_right (le_mul_of_one_le_right zero_le hB1) zero_le


theorem LoErrSingleScale00 (P : Polynomial ℤ) (p₁ p₂ : ENNReal) (hdeg : 2 ≤ P.natDegree)
    (hA1 : Work.KMTContract.AreaA1) (hp₁ : 1 < p₁) (htp₁ : p₁ < ⊤) (hp₂ : 1 < p₂)
    (htp₂ : p₂ < ⊤) (hsum : p₁⁻¹ + p₂⁻¹ ≤ 1) :
    Work.KMTAreas.A7.LoErrStatement P p₁ p₂ := by
  intro C₀ hC₀
  obtain ⟨Kd, D, hKd, hD, hderD⟩ := Work.KMTPlan.A6.loSymD_deriv_bound P hdeg
  obtain ⟨Cc, hCc, hcrude⟩ := loMainPart_sub_loModel_crude P p₁ p₂ hdeg hp₁ htp₁ hp₂ htp₂ hsum
  refine ⟨Kd + 2 * (P.natDegree : ℝ), by positivity, 1, by norm_num, ?_⟩
  intro ρ hρ hρ1
  obtain ⟨L₀, hL₀⟩ := uScale_growth ρ hρ
  refine ⟨fun _ => loK D Cc hD L₀ ρ, ?_⟩
  intro a Λ l₁ l₂ k₁ k₂ f g hΛ ha ha1 hl₁ hl₂ n
  subst hl₁; subst hl₂
  have key : Work.KMTAreas.A5.BoundedZ f → Work.KMTAreas.A5.BoundedZ g →
      eLpNorm (fun x : ℤ => mainPartTuple ρ P C₀ a f g 0 0 k₁ k₂ n x
          - loModelTuple ρ P C₀ a f g 0 0 k₁ k₂ n x)
        (p₁⁻¹ + p₂⁻¹)⁻¹ Measure.count
        ≤ (loK D Cc hD L₀ ρ : ENNReal)
          * ENNReal.ofReal ((2 : ℝ) ^ ((Kd + 2 * (P.natDegree : ℝ)) * (lmaxR 0 0 k₁ k₂)))
          * ENNReal.ofReal (((((Nat.floor (a n) : ℕ)) : ℝ))⁻¹)
          * eLpNorm f p₁ Measure.count * eLpNorm g p₂ Measure.count := by
    intro hBf hBg
    by_cases hguard : loGuard ρ C₀ a 0 0 k₁ k₂ n
    · set N : ℕ := Nat.floor (a n) with hNdef
      have hN1 : 1 ≤ N := by
        have h' : (1 : ℝ) ≤ (a n : ℝ) := by exact_mod_cast ha1 n
        exact Nat.one_le_iff_ne_zero.mpr (Nat.floor_pos.mpr h').ne'
      have hLcast : lmaxR 0 0 k₁ k₂ = ((max k₁ k₂ : ℕ) : ℝ) := by
        have h1 : Work.Analysis.EndVar.lmax 0 0 (k₁ : ℤ) (k₂ : ℤ) = ((max k₁ k₂ : ℕ) : ℤ) := by
          rw [Work.Analysis.EndVar.lmax, Nat.cast_max, max_self]
          exact max_eq_right (le_trans (Int.natCast_nonneg k₁) (le_max_left _ _))
        rw [lmaxR, h1]
        push_cast; ring
      by_cases hC2 : max k₁ k₂ + 2 * uScale ρ (max k₁ k₂) + 1
          ≤ (Work.Analysis.EndVar.logN N).toNat
      · -- ================= main case =================
        have hN2 : 2 ≤ N := by
          have h2 : 2 ≤ splitCut ρ (max k₁ k₂) := by
            rw [splitCut]
            exact Nat.le_trans (by norm_num) (Nat.pow_le_pow_right (by norm_num)
              (Nat.one_le_two_pow))
          exact le_of_lt (lt_of_le_of_lt h2 hguard.2.1)
        have hu1 : 1 ≤ uScale ρ (max k₁ k₂) := uScale_pos hρ.le _
        have hk₁ : k₁ + 3 ≤ (Work.Analysis.EndVar.logN N).toNat := by
          have := Nat.le_max_left k₁ k₂; omega
        have hk₂ : k₂ + 3 ≤ (Work.Analysis.EndVar.logN N).toNat := by
          have := Nat.le_max_right k₁ k₂; omega
        have hsumC := (Work.KMTPlan.A6.symC_symM_summable ρ hρ hρ1 P N 0 0 k₁ k₂).1
        have hsumM := (Work.KMTPlan.A6.symC_symM_summable ρ hρ hρ1 P N 0 0 k₁ k₂).2
        have hpt : (fun x : ℤ => mainPartTuple ρ P C₀ a f g 0 0 k₁ k₂ n x
              - loModelTuple ρ P C₀ a f g 0 0 k₁ k₂ n x)
            = fun x : ℤ => bilinOp (fun u v =>
                Work.KMTPlan.A6.coeff2 (Work.KMTPlan.A6.symD ρ P N 0 0 k₁ k₂) u v) f g x := by
          funext x
          rw [loMainPart_eq_bilinOp_symC ρ hρ hρ1 P C₀ a f g 0 k₁ k₂ n x hBf hBg hguard,
            loModel_eq_bilinOp_symM ρ hρ hρ1 P C₀ a f g k₁ k₂ n x (le_trans (by norm_num) hdeg)
              hBf hBg hguard hC2,
            bilinOp_sub_kernel hsumC hsumM hBf.choose_spec hBg.choose_spec x]
          congr 1
          funext u v
          rw [Work.KMTPlan.A6.coeff2_sub_symC_symM ρ hρ hρ1 P N 0 0 k₁ k₂ u v]
          exact coeff2_congr_lo (fun x y =>
            loSymCollapse P (le_trans (by norm_num) hdeg) ρ hρ hρ1 N k₁ k₂ hN1 hC2 x y) u v
        rw [hLcast, hpt]
        have hNpos : (0 : ℝ) < (N : ℝ) := by exact_mod_cast hN1
        set A : ℝ := D * (2 : ℝ) ^ (Kd * ((max k₁ k₂ : ℕ) : ℝ))
          * (1 + (Work.A7.Sval P k₁ k₂) ^ 2 / (N : ℝ)) * ((N : ℝ))⁻¹ with hA
        have hAnn : 0 ≤ A := by
          rw [hA]
          have h2 : 0 ≤ 1 + (Work.A7.Sval P k₁ k₂) ^ 2 / (N : ℝ) := by positivity
          have h3 : 0 ≤ (2 : ℝ) ^ (Kd * ((max k₁ k₂ : ℕ) : ℝ)) := Real.rpow_nonneg (by norm_num) _
          positivity
        have hr₁ : 0 < ((N : ℝ))⁻¹ := inv_pos.mpr hNpos
        have hr₁1 : ((N : ℝ))⁻¹ ≤ 1 := by
          rw [inv_le_one₀ hNpos]; exact_mod_cast hN1
        have hr₂ : 0 < (((N : ℝ)) ^ P.natDegree)⁻¹ := inv_pos.mpr (by positivity)
        have hr₂1 : (((N : ℝ)) ^ P.natDegree)⁻¹ ≤ 1 := by
          rw [inv_le_one₀ (by positivity)]
          exact one_le_pow₀ (by exact_mod_cast hN1)
        have hder' : ∀ j₁ j₂ : ℕ, j₁ ≤ 2 → j₂ ≤ 2 →
            (∫⁻ x in Set.Icc (0 : ℝ) 1, ∫⁻ y in Set.Icc (0 : ℝ) 1,
                ENNReal.ofReal ‖Work.KMTPlan.A6.dp j₁ j₂
                  (Work.KMTPlan.A6.symD ρ P N 0 0 k₁ k₂) x y‖)
              ≤ ENNReal.ofReal (A * ((N : ℝ))⁻¹ ^ ((1 : ℝ) - (j₁ : ℝ))
                  * (((N : ℝ) ^ P.natDegree)⁻¹) ^ ((1 : ℝ) - (j₂ : ℝ))) := by
          intro j₁ j₂ hj₁ hj₂
          refine (hderD ρ N k₁ k₂ hρ hρ1 hN2 hk₁ hk₂ j₁ j₂ hj₁ hj₂).trans ?_
          refine ENNReal.ofReal_le_ofReal ?_
          have hNpow : (N : ℝ) ^ (((j₁ : ℤ) - 2) + (P.natDegree : ℤ) * ((j₂ : ℤ) - 1))
              = (N : ℝ)⁻¹ * (((N : ℝ))⁻¹ ^ ((1 : ℝ) - (j₁ : ℝ))
                  * (((N : ℝ) ^ P.natDegree)⁻¹) ^ ((1 : ℝ) - (j₂ : ℝ))) := by
            rw [← Real.rpow_intCast (N : ℝ)
                (((j₁ : ℤ) - 2) + (P.natDegree : ℤ) * ((j₂ : ℤ) - 1)),
              inv_rpow_prod_lo N P.natDegree j₁ j₂ hN1,
              show ((((j₁ : ℤ) - 2) + (P.natDegree : ℤ) * ((j₂ : ℤ) - 1) : ℤ) : ℝ)
                = (-1 : ℝ) + ((((j₁ : ℤ) + (P.natDegree : ℤ) * (j₂ : ℤ)
                    - (P.natDegree : ℤ) - 1) : ℤ) : ℝ) from by push_cast; ring,
              Real.rpow_add hNpos (-1)
                ((((j₁ : ℤ) + (P.natDegree : ℤ) * (j₂ : ℤ) - (P.natDegree : ℤ) - 1) : ℤ) : ℝ),
              Real.rpow_neg_one]
          rw [hA]
          exact le_of_eq (by rw [hNpow]; ring)
        obtain ⟨hsumD, hmassD⟩ := Work.KMTPlan.A6.SymToolbox_tsum_coeff2_le
          (fun x y => Work.KMTPlan.A6.symD ρ P N 0 0 k₁ k₂ x y)
          (fun x y => (Work.KMTPlan.A6.symD_period_contDiff P ρ N 0 0 k₁ k₂).1 x y)
          (fun x y => (Work.KMTPlan.A6.symD_period_contDiff P ρ N 0 0 k₁ k₂).2.1 x y)
          (Work.KMTPlan.A6.symD_period_contDiff P ρ N 0 0 k₁ k₂).2.2 hr₁ hr₁1 hr₂ hr₂1 hAnn hder'
        have hpeq : p₁⁻¹ + p₂⁻¹ = ((p₁⁻¹ + p₂⁻¹)⁻¹)⁻¹ := by rw [inv_inv]
        have hone : (1 : ENNReal) ≤ (p₁⁻¹ + p₂⁻¹)⁻¹ := ENNReal.one_le_inv.mpr hsum
        have hLP := BilinOpLp (K := fun u v =>
            Work.KMTPlan.A6.coeff2 (Work.KMTPlan.A6.symD ρ P N 0 0 k₁ k₂) u v)
          (p := (p₁⁻¹ + p₂⁻¹)⁻¹) (p₁ := p₁) (p₂ := p₂) hpeq hone hsumD f g
        have hAbound : 40 * A ≤ (max (320 * D)
              (Cc * (((2 : ℕ) ^ (L₀ + 2 * uScale ρ L₀ + 1) : ℕ) : ℝ)))
            * (2 : ℝ) ^ ((Kd + 2 * (P.natDegree : ℝ)) * ((max k₁ k₂ : ℕ) : ℝ)) * ((N : ℝ))⁻¹ := by
          rw [hA]; exact lo_weight_bound P (by omega) hD hKd hN1
        have hineq : ENNReal.ofReal (∑' q : ℤ × ℤ, ‖Work.KMTPlan.A6.coeff2
              (Work.KMTPlan.A6.symD ρ P N 0 0 k₁ k₂) q.1 q.2‖)
            ≤ (loK D Cc hD L₀ ρ : ENNReal)
              * ENNReal.ofReal ((2 : ℝ) ^ ((Kd + 2 * (P.natDegree : ℝ)) * ((max k₁ k₂ : ℕ) : ℝ)))
              * ENNReal.ofReal (((N : ℝ))⁻¹) := by
          have hreal : (∑' q : ℤ × ℤ, ‖Work.KMTPlan.A6.coeff2
                (Work.KMTPlan.A6.symD ρ P N 0 0 k₁ k₂) q.1 q.2‖)
              ≤ ((loK D Cc hD L₀ ρ : NNReal) : ℝ)
                * (2 : ℝ) ^ ((Kd + 2 * (P.natDegree : ℝ)) * ((max k₁ k₂ : ℕ) : ℝ))
                * ((N : ℝ))⁻¹ := by
            have hlo : ((loK D Cc hD L₀ ρ : NNReal) : ℝ)
                = max (320 * D)
                    (Cc * (((2 : ℕ) ^ (L₀ + 2 * uScale ρ L₀ + 1) : ℕ) : ℝ)) := rfl
            rw [hlo]
            exact hmassD.trans hAbound
          have hnn : (0 : ℝ) ≤ ((loK D Cc hD L₀ ρ : NNReal) : ℝ) := by
            rw [show ((loK D Cc hD L₀ ρ : NNReal) : ℝ)
                = max (320 * D)
                  (Cc * (((2 : ℕ) ^ (L₀ + 2 * uScale ρ L₀ + 1) : ℕ) : ℝ)) from rfl]
            exact le_trans (by linarith) (le_max_left _ _)
          refine (ENNReal.ofReal_le_ofReal hreal).trans (le_of_eq ?_)
          rw [ENNReal.ofReal_mul (mul_nonneg hnn (Real.rpow_nonneg (by norm_num) _)),
            ENNReal.ofReal_mul hnn,
            ENNReal.ofReal_coe_nnreal]
        exact hLP.trans (mul_le_mul' (mul_le_mul' hineq le_rfl) le_rfl)
      · -- ================= exceptional case =================
        have hmm : max (max 0 0) (max k₁ k₂) = max k₁ k₂ := by
          rw [show max 0 0 = (0 : ℕ) from max_eq_left le_rfl, max_eq_right (Nat.zero_le _)]
        have hb := hcrude ρ C₀ a k₁ k₂ n f g hguard
        refine hb.trans (mul_le_mul' (mul_le_mul' ?_ le_rfl) le_rfl)
        exact lo_exceptional_weight P hD hKd hN1
          (lo_exceptional_N_bound (C₀ := C₀) ρ hρ L₀ hL₀ (by rw [← hmm]; exact hguard.2.1)
            (by rw [← hmm]; exact hguard.2.2) hC2)
    · -- off the guard both tuples vanish
      have h0 : (fun x : ℤ => mainPartTuple ρ P C₀ a f g 0 0 k₁ k₂ n x
          - loModelTuple ρ P C₀ a f g 0 0 k₁ k₂ n x) = 0 := by
        funext x
        simp [mainPartTuple_apply, loModelTuple, hguard]
      rw [h0]
      simp
  have hz1 : (fun x : ℤ => mainPartTuple ρ P C₀ a (0 : ℤ → ℂ) g 0 0 k₁ k₂ n x
      - loModelTuple ρ P C₀ a (0 : ℤ → ℂ) g 0 0 k₁ k₂ n x) = 0 := by
    funext x
    simp only [mainPartTuple_apply, loModelTuple]
    split_ifs <;> simp [intervalIntegral.integral_zero]
  have hz2 : (fun x : ℤ => mainPartTuple ρ P C₀ a f (0 : ℤ → ℂ) 0 0 k₁ k₂ n x
      - loModelTuple ρ P C₀ a f (0 : ℤ → ℂ) 0 0 k₁ k₂ n x) = 0 := by
    funext x
    simp only [mainPartTuple_apply, loModelTuple]
    split_ifs <;> simp [intervalIntegral.integral_zero]
  have hp₁0 : p₁ ≠ 0 := by
    intro h; rw [h] at hp₁; exact absurd hp₁ (by norm_num)
  have hp₂0 : p₂ ≠ 0 := by
    intro h; rw [h] at hp₂; exact absurd hp₂ (by norm_num)
  have hNge1 : 1 ≤ Nat.floor (a n) := by
    have h' : (1 : ℝ) ≤ (a n : ℝ) := by exact_mod_cast ha1 n
    exact Nat.one_le_iff_ne_zero.mpr (Nat.floor_pos.mpr h').ne'
  have hNpos' : (0 : ℝ) < (((Nat.floor (a n) : ℕ) : ℝ))⁻¹ :=
    inv_pos.mpr (by exact_mod_cast hNge1)
  have hKpos : (0 : ℝ) < ((loK D Cc hD L₀ ρ : NNReal) : ℝ) := by
    have h1 : ((loK D Cc hD L₀ ρ : NNReal) : ℝ)
        = max (320 * D) (Cc * (((2 : ℕ) ^ (L₀ + 2 * uScale ρ L₀ + 1) : ℕ) : ℝ)) := rfl
    rw [h1]; exact lt_of_lt_of_le (by linarith) (le_max_left _ _)
  have hKne : ((fun _ => loK D Cc hD L₀ ρ) Λ : ENNReal) ≠ 0 :=
    ENNReal.coe_ne_zero.mpr (ne_of_gt (NNReal.coe_pos.mp hKpos))
  have hBne : ENNReal.ofReal ((2 : ℝ) ^ ((Kd + 2 * (P.natDegree : ℝ)) * (lmaxR 0 0 k₁ k₂)))
      ≠ 0 := (ENNReal.ofReal_pos.mpr (Real.rpow_pos_of_pos (by norm_num) _)).ne'
  have hCne : ENNReal.ofReal (((((Nat.floor (a n) : ℕ)) : ℝ))⁻¹) ≠ 0 :=
    (ENNReal.ofReal_pos.mpr hNpos').ne'
  by_cases hf0 : f = 0
  · rw [hf0, hz1]; simp [eLpNorm_zero]
  by_cases hg0 : g = 0
  · rw [hg0, hz2]; simp [eLpNorm_zero]
  have hfne : eLpNorm f p₁ Measure.count ≠ 0 := by
    intro h
    exact hf0 (eq_zero_of_eLpNorm_eq_zero_loc hp₁0 h)
  have hgne : eLpNorm g p₂ Measure.count ≠ 0 := by
    intro h
    exact hg0 (eq_zero_of_eLpNorm_eq_zero_loc hp₂0 h)
  by_cases hBf : Work.KMTAreas.A5.BoundedZ f
  · by_cases hBg : Work.KMTAreas.A5.BoundedZ g
    · exact key hBf hBg
    · -- `¬ BoundedZ g`: the right-hand side is `⊤`
      have hginf : eLpNorm g p₂ Measure.count = ⊤ := by
        by_contra hne
        exact hBg (bound_of_eLpNorm_ne_top hp₂ hne)
      rw [hginf]
      refine le_top.trans (le_of_eq ?_)
      rw [ENNReal.mul_top (mul_ne_zero (mul_ne_zero (mul_ne_zero hKne hBne) hCne) hfne)]
  · -- `¬ BoundedZ f`: the right-hand side is `⊤`
    have hfinf : eLpNorm f p₁ Measure.count = ⊤ := by
      by_contra hne
      exact hBf (bound_of_eLpNorm_ne_top hp₁ hne)
    rw [hfinf]
    refine le_top.trans (le_of_eq ?_)
    rw [ENNReal.mul_top (mul_ne_zero (mul_ne_zero hKne hBne) hCne),
      ENNReal.top_mul hgne]

end

end Work.KMTAreas.A7
