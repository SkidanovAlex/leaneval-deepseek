import ChallengeDeps
import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.Topology.UniformSpace.Uniformizable
import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Submission.Work.BoseBoxFock.PCFU.BslotNormLe
import Submission.Work.BoseBoxFock.PCFU.SlotPieceDefs
import Submission.Work.BoseBoxFock.PCFU.chBW1farIntegrable
import Submission.Work.BoseBoxFock.PCFU.chB_img_le
import Submission.Work.BoseBoxFock.PCFU.chBbigarith
import Submission.Work.BoseBoxFock.PCFU.chBlatTailSum
import Submission.Work.BoseBoxFock.PCFU.chBpointwise
import Submission.Work.BoseBoxFock.PCFU.chiStarE_le
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Work.BoseBoxFock.PCFU.chBslot_le` — the `(B)` slot of the cubic dictionary

**Read `Submission/Work/BoseBoxFock/PCFU/FINDING_chBslot_le.md` first**; it contains the complete
reduction, the constants and the status of every input.  In one paragraph:

* `SlotPiece` unfolds to `∃ K₀ > 0, SlotPieceBound … (fun μ => K₀·(μ·a v)) _`; the budget then
  forces `A μ ≤ K₀a/(8μ(ℓ³+1))` with `ℓ = ellH v μ`, which is what makes `A μ → ∞` as `μ → 0` —
  so every term of the pointwise estimate must decay in `Λℓ = πN/2` or in `ℓ`.
* The bracket of `chBslot` is `F(x j)`, `F z = KχfrU v h μ fu N z − ∫ y, χ_Λ y·W₁(y−z)`.
  By the PROVED `Bdecomp`, `F = χ_Λ ⋆ E + Img` with `E = uvSmear fu Λ W₁ − W₁` and
  `Img z = ∫_w χ_Λ w · Σ'_{d≠0} uvSmear fu Λ W₁ (z − w + ℓ•latVec d) dw`.
* `chiStarE_le` bounds `sup|χ_Λ ⋆ E| ≤ C(ℓ)/Λ`; `chB_img_le` bounds
  `χ_Λ z·|Img z| ≤ K_img·(∫|W₁|)·((Λℓ)⁻¹ + (R/ℓ)^4 + ((Λℓ)²)⁻¹)`; and
  `∫|W₁| ≤ 2∫|g₀|` (`chBslotAux.W1fun_L1_le`, needs `R ≤ ℓ·chiR0`).
* `BslotNormLe` converts `∀z, χ_Λ z·‖F z‖ ≤ M` into
  `‖chBslot … (boxRestrictR ℓ Φ)‖ ≤ M·normB v μ n Φ`; `chBarith` is the final arithmetic.
-/

noncomputable section

open MeasureTheory
open scoped Real Topology BigOperators

namespace Work.BoseBoxFock.PCFU

local notation "E3" => EuclideanSpace ℝ (Fin 3)

/-! ## Elementary helpers for the assembly -/

/-- `uvRad ℓ N = π N / (2 ℓ)`: the `N`-th UV cut-off radius, in the form used by `chBarith`. -/
private lemma uvRad_eq (ℓ : ℝ) (N : ℕ) :
    Work.BoseBoxFock.uvRad ℓ N = Real.pi * (N : ℝ) / (2 * ℓ) := by
  rw [Work.BoseBoxFock.uvRad]
  ring

/-- A state multiplied by the indicator of the compact box `abox n ℓ` is bounded by the sup of
the state on the box. -/
private lemma boxRestrictR_abs_le {n : ℕ} (ℓ C : ℝ) {Φ : Submission.BoseGases.X n → ℝ}
    (hC : ∀ x ∈ Submission.BoseGases.abox n ℓ, |Φ x| ≤ C) (x : Submission.BoseGases.X n) :
    |Work.BoseBoxFock.boxRestrictR ℓ Φ x| ≤ max C 0 := by
  rw [Work.BoseBoxFock.boxRestrictR]
  by_cases hx : x ∈ Submission.BoseGases.abox n ℓ
  · rw [Set.indicator_of_mem hx, mul_one]
    exact le_trans (hC x hx) (le_max_left _ _)
  · rw [Set.indicator_of_notMem hx, mul_zero, abs_zero]
    exact le_max_right _ _

/-- The low-momentum cut-off `chKappa v μ = ((d²)·sideAt μ (a v))⁻¹` is positive at admissible
`μ`.  (Local copy of `PCFU.chKappa_pos_of`, to keep the import cone of this node small.) -/
private lemma chKappa_pos' (v : E3 → ℝ) {μ : ℝ} (hμ : 0 < μ) (hav : 0 < BoseGases.a v) :
    0 < chKappa v μ := by
  have hd : 0 < (Work.BoseBox.paramsAt μ (BoseGases.a v)).d := by
    simp only [Work.BoseBox.paramsAt, Work.BoseBox.fsParams]
    exact Work.BoseBox.fsXp_pos (by positivity)
  rw [chKappa]
  exact inv_pos.mpr (mul_pos (pow_pos hd 2) (Work.BoseBox.sideAt_pos hμ hav))

theorem chBslot_le (v : EuclideanSpace ℝ (Fin 3) → ℝ) (h : Work.UBB.ScatSol v) (hv : 0 ≤ v)
    (hv1 : MeasureTheory.MemLp v 1) (hvrad : _root_.BoseGases.IsRadial v) {R : ℝ} (hR : 0 < R)
    (hv_supp : tsupport v ⊆ Metric.ball (0 : EuclideanSpace ℝ (Fin 3)) R)
    (hav : 0 < BoseGases.a v) (fc fu : Work.BoseBoxFix.LowCut) (J ε₀ : ℝ) :
    Work.BoseBoxFock.SlotPiece v h fc fu R J ε₀
      (fun n μ N i j Θ => Work.BoseBoxFock.PCFU.chBslot v h fc fu μ N i j Θ) := by
  classical
  -- ⚑ (1) the `Λ`-uniform fourth moment of the smoothing kernel (PROVED)
  obtain ⟨Bm, hBm0, hBm⟩ := Work.BoseBoxFock.PCFU.uvKernel_moment_le fu 4
  -- ⚑ (2) the images constant, uniform in `ℓ` and `Λ ≥ 1` (colleague: `PCFU/chB_img_le`)
  have himg : ∃ K : ℝ, 0 ≤ K ∧
      ∀ (ℓ : ℝ) (_hℓ : 0 < ℓ) (_hRℓ : 2 * R ≤ ℓ) (_hchi : R ≤ ℓ * Submission.BoseGases.chiR0)
        (Λ : ℝ) (_hΛ : 1 ≤ Λ) (_hΛℓ : 1 ≤ Λ * ℓ) (z : E3),
        (Work.BoseK15.corpusBox.chiLam ℓ z) *
          (∫ w : E3, (Work.BoseK15.corpusBox.chiLam ℓ w) *
            ‖(∑' d : Fin 3 → ℤ, if d = 0 then 0 else
                ((Work.BoseBoxFock.uvSmear fu Λ (Work.BoseFixR.W1fun v h ℓ)
                  (z - w + ℓ • Work.BoseBoxFock.latVec d) : ℝ) : ℂ))‖)
        ≤ K * (∫ x : E3, |Work.BoseFixR.W1fun v h ℓ x|) *
            ((Λ * ℓ)⁻¹ + (R / ℓ) ^ 4 + ((Λ * ℓ) ^ 2)⁻¹) :=
    Work.BoseBoxFock.PCFU.chB_img_le_of_inputs (v := v) (h := h) (fu := fu) (R := R) hR hv_supp
      Work.BoseBoxFock.PCFU.chiLam_mul_le_of_alias
      Work.BoseBoxFock.PCFU.chBimg_J_le
      (fun {R' ℓ Λ Cd} (hR' : 0 < R') (hℓ : 0 < ℓ) (h2R' : 2 * R' ≤ ℓ) (hΛ : 1 ≤ Λ)
          (hCd : 0 ≤ Cd) (hv_supp' : tsupport v ⊆ Metric.ball (0 : E3) R')
          (hdec : ∀ z : E3,
            ‖Work.BoseBoxFock.uvKernel fu Λ z‖ ≤ Cd * Λ ^ 3 * (1 + Λ * ‖z‖) ^ (-(5 : ℤ)))
          {x : E3} (hx : ‖x‖ ≤ ℓ) =>
        Work.BoseBoxFock.PCFU.chBimg_far_tail_core (v := v) (h := h) (fu := fu) (R := R')
          (ℓ := ℓ) (Λ := Λ) (Cd := Cd) hR' hℓ h2R' hΛ hCd hv_supp' hdec
          (Work.BoseBoxFock.PCFU.chBW1farIntegrable (v := v) (h := h) (R := R') (ℓ := ℓ)
            hR' hℓ h2R' hv_supp')
          (Work.BoseBoxFock.PCFU.chBlatTailSum) hx)
      Work.BoseBoxFock.PCFU.chBimg_near_d Bm hBm0 hBm
  obtain ⟨Kimg, hKimg0, hKimg⟩ := himg
  -- the total `L¹` mass of `g₀` (the `μ`-uniform part of `∫|W₁|`) and the constants
  set G0 : ℝ := ∫ x : E3, |Submission.BoseGases.g0 v h x| with hG0def
  have hG00 : 0 ≤ G0 := integral_nonneg fun x => abs_nonneg _
  set K0 : ℝ := 2 + 64 * Kimg * G0 * (|ε₀| / BoseGases.a v ^ 4) * (R ^ 3 / 2 + 1 / 16) with hK0def
  have hK0pos : 0 < K0 := by
    rw [hK0def]
    have h1 : (0 : ℝ) ≤ 64 * Kimg * G0 * (|ε₀| / BoseGases.a v ^ 4) * (R ^ 3 / 2 + 1 / 16) := by
      have h2 : (0 : ℝ) ≤ |ε₀| / BoseGases.a v ^ 4 := by positivity
      have h3 : (0 : ℝ) ≤ R ^ 3 / 2 + 1 / 16 := by positivity
      positivity
    linarith
  -- the two `μ`-dependent constants of the pointwise estimate (the `E`-constant `CE` is the
  -- explicitly-known constant of `chiStarE_le`; its `μ`-dependence is harmless because `T` below
  -- may depend on `μ`)
  have hCE : ∀ (ℓ : ℝ), 0 < ℓ → MeasureTheory.Integrable (Work.BoseFixR.W1fun v h ℓ) →
      ∃ C : ℝ, 0 ≤ C ∧ ∀ (Λ : ℝ), 1 ≤ Λ → ∀ z : E3,
        |∫ w : E3, (Work.BoseK15.corpusBox.chiLam ℓ w) *
            (Work.BoseBoxFock.uvSmear fu Λ (Work.BoseFixR.W1fun v h ℓ) (z - w)
              - Work.BoseFixR.W1fun v h ℓ (z - w))| ≤ C / Λ :=
    fun ℓ hℓ hI => Work.BoseBoxFock.PCFU.chiStarE_le (v := v) (h := h) (fu := fu) hℓ hI
  have hWint : ∀ (ℓ : ℝ), 0 < ℓ → R ≤ ℓ * Submission.BoseGases.chiR0 →
      MeasureTheory.Integrable (Work.BoseFixR.W1fun v h ℓ) :=
    fun ℓ hℓ hRℓ => Submission.BoseGases.wScaled_g0_integrable hR hv_supp h hℓ hRℓ
  -- `CE` and `Wm`: the `E`-constant and the mass of `W₁`, as functions of `μ`
  set CE : ℝ → ℝ := fun μ =>
    if hμ : 0 < ellH v μ ∧ MeasureTheory.Integrable (Work.BoseFixR.W1fun v h (ellH v μ))
      then Classical.choose (hCE (ellH v μ) hμ.1 hμ.2) else 0 with hCEdef
  set Wm : ℝ → ℝ := fun μ => ∫ x : E3, |Work.BoseFixR.W1fun v h (ellH v μ) x| with hWmdef
  set Af : ℝ → ℝ := fun μ =>
    if 0 < μ then K0 * BoseGases.a v / (8 * μ * (ellH v μ ^ 3 + 1)) else 0 with hAdef
  -- The `N`-threshold: the supply bound of `chBarith` together with the cut-off condition
  -- `2ℓ ≤ πN` (i.e. `1 ≤ Λ = uvRad ℓ N`).  Both may depend on `μ`.
  set Tf : ℝ → ℕ := fun μ => Nat.ceil (4 * (1 + ellH v μ)
      * (1 + (Real.sqrt Submission.BoseGases.chiNormSq)⁻¹ * CE μ)
      * (1 + Kimg * Wm μ) * (1 + Kimg * Wm μ / Af μ) / Af μ)
      + Nat.ceil (2 * ellH v μ / Real.pi) + 4 with hTdef
  refine ⟨K0, hK0pos, Af, Tf, ?_, ?_, ?_⟩
  · -- `0 ≤ A μ`:  on `μ > 0` this is `K₀a/(8μ(ℓ³+1)) > 0`, otherwise it is `0`
    intro μ
    rw [hAdef]
    by_cases hμ : 0 < μ
    · simp only [hμ, if_true]
      have hℓ0' : 0 < ellH v μ := Work.BoseBoxFock.ellH_pos v μ
      exact div_nonneg (mul_nonneg hK0pos.le hav.le) (by positivity)
    · simp only [hμ, if_false]
      exact le_refl 0
  · -- the budget: `2ℓ⁻³·4μ²ℓ⁶(1+ℓ⁻³)·A μ = K₀·μ·a` — an *identity*: `A μ = K₀a/(8μ(ℓ³+1))`
    -- on `μ > 0` and `ℓ³(1+ℓ⁻³) = ℓ³+1` cancels the denominator; the remaining factors are
    -- `2·4·(1/8) = 1` and `μ²·μ⁻¹ = μ`.
    intro μ hμ
    rw [hAdef]
    simp only [hμ, if_true]
    have hℓ : 0 < ellH v μ := Work.BoseBoxFock.ellH_pos v μ
    rw [zpow_neg]
    field_simp
    linarith
  · -- the per-slot bound
    intro Nmin hNmin hT hreg HM hMono μ hAdm hJ n Φ hn hnorm hlowB hspec i j hij
    -- ## the data
    have hμ : 0 < μ := hAdm.1
    have hε₀ : μ * BoseGases.a v ^ 3 ≤ ε₀ := hAdm.2.1
    have hℓ : 0 < ellH v μ := Work.BoseBoxFock.ellH_pos v μ
    have hRchi : R ≤ ellH v μ * Submission.BoseGases.chiR0 := (hreg μ hAdm).1
    have h4R : 4 * R ≤ ellH v μ := (hreg μ hAdm).2
    have h2R : 2 * R ≤ ellH v μ := by linarith
    have hside : ellH v μ = Work.BoseBox.sideAt μ (BoseGases.a v) := by
      rw [Work.BoseBoxFock.ellH, if_pos (Work.BoseBox.sideAt_pos hμ hav)]
    have huv : Work.BoseBoxFock.uvRad (ellH v μ) (HM μ).N
        = Real.pi * ((HM μ).N : ℝ) / (2 * ellH v μ) := uvRad_eq _ _
    -- ## the two threshold facts extracted from `N ≥ Tf μ`
    set Ax : ℕ := Nat.ceil (4 * (1 + ellH v μ)
        * (1 + (Real.sqrt Submission.BoseGases.chiNormSq)⁻¹ * CE μ)
        * (1 + Kimg * Wm μ) * (1 + Kimg * Wm μ / Af μ) / Af μ) with hAx
    set Bx : ℕ := Nat.ceil (2 * ellH v μ / Real.pi) with hBx
    have hNceil : Ax + Bx + 4 ≤ (HM μ).N := by
      have h0 : Tf μ ≤ (HM μ).N := le_trans (hT μ) (hMono μ)
      rw [hTdef] at h0
      rw [hAx, hBx]
      exact h0
    have hhalf : 2 * ellH v μ / Real.pi ≤ ((HM μ).N : ℝ) := by
      have h1 : 2 * ellH v μ / Real.pi ≤ ((Bx : ℕ) : ℝ) := by
        rw [hBx]; exact Nat.le_ceil _
      have h2 : ((Bx : ℕ) : ℝ) ≤ ((HM μ).N : ℝ) := by
        exact_mod_cast (by omega : Bx ≤ (HM μ).N)
      linarith
    have hΛ1 : 1 ≤ Work.BoseBoxFock.uvRad (ellH v μ) (HM μ).N := by
      rw [huv, le_div_iff₀ (by positivity : (0 : ℝ) < 2 * ellH v μ)]
      have hh := hhalf
      rw [div_le_iff₀ Real.pi_pos] at hh
      linarith
    have hN1 : 1 ≤ (HM μ).N := by
      have hch2 : (2 : ℝ) ≤ chNThresh v μ := by
        rw [chNThresh]
        have h1 : (0 : ℝ) ≤ 4 * ((Work.BoseBox.paramsAt μ (BoseGases.a v)).d ^ 2 * ellH v μ)⁻¹
            * ellH v μ / (2 * Real.pi) := by positivity
        linarith
      have hc2 : (2 : ℕ) ≤ ⌈chNThresh v μ⌉₊ := by
        have := Nat.ceil_mono hch2
        simpa using this
      have := le_trans hc2 (le_trans (hNmin μ) (hMono μ))
      omega
    have hΛℓ : 1 ≤ Work.BoseBoxFock.uvRad (ellH v μ) (HM μ).N * ellH v μ := by
      rw [huv]
      have hN1' : (1 : ℝ) ≤ ((HM μ).N : ℝ) := by exact_mod_cast hN1
      have he : Real.pi * ((HM μ).N : ℝ) / (2 * ellH v μ) * ellH v μ
          = Real.pi * ((HM μ).N : ℝ) / 2 := by field_simp
      rw [he]
      nlinarith [Real.pi_gt_three, hN1']
    -- ## the `E`-constant of `chiStarE_le`
    have hI : MeasureTheory.Integrable (Work.BoseFixR.W1fun v h (ellH v μ)) :=
      hWint (ellH v μ) hℓ hRchi
    have hCEμ : 0 ≤ CE μ ∧ ∀ (Λ : ℝ), 1 ≤ Λ → ∀ z : E3,
        |∫ w : E3, (Work.BoseK15.corpusBox.chiLam (ellH v μ) w) *
            (Work.BoseBoxFock.uvSmear fu Λ (Work.BoseFixR.W1fun v h (ellH v μ)) (z - w)
              - Work.BoseFixR.W1fun v h (ellH v μ) (z - w))| ≤ CE μ / Λ := by
      have hd : CE μ = Classical.choose (hCE (ellH v μ) hℓ hI) := by
        simp only [hCEdef]
        exact dif_pos ⟨hℓ, hI⟩
      rw [hd]
      exact Classical.choose_spec (hCE (ellH v μ) hℓ hI)
    have hev : ∀ x : E3,
        Work.BoseFixR.W1fun v h (ellH v μ) (-x) = Work.BoseFixR.W1fun v h (ellH v μ) x :=
      Work.BoseFixR.isEven_W1fun h hvrad (ellH v μ)
    have hcs : HasCompactSupport (Work.BoseFixR.W1fun v h (ellH v μ)) :=
      HasCompactSupport.of_support_subset_isCompact (isCompact_closedBall (0 : E3) R) fun x hx =>
        Metric.ball_subset_closedBall
          (hv_supp (subset_tsupport _ (Work.BoseFixR.support_W1fun_subset h (ellH v μ) hx)))
    -- ## the `chBarith` data
    have hE0 : 0 ≤ (Real.sqrt Submission.BoseGases.chiNormSq)⁻¹ * CE μ :=
      mul_nonneg (inv_nonneg.mpr (Real.sqrt_nonneg _)) hCEμ.1
    have hG0' : 0 ≤ Kimg * Wm μ :=
      mul_nonneg hKimg0 (integral_nonneg fun x => abs_nonneg _)
    have hWmle : Wm μ ≤ 2 * G0 := by
      simpa only [hWmdef, hG0def] using
        (Work.BoseBoxFock.PCFU.W1fun_L1_le (v := v) (h := h) hR hℓ hRchi hv_supp)
    have hbig : 32 * (Kimg * Wm μ) * μ * (ellH v μ ^ 3 + 1) * (R / ellH v μ) ^ 4
        / BoseGases.a v ≤ K0 :=
      chBbigarith (K0 := K0) (Kimg := Kimg) (G0 := G0) (Wm := Wm μ) (μ := μ)
        (ℓ := ellH v μ) (R := R) (a := BoseGases.a v) (ε₀ := ε₀)
        (hK0le := le_of_eq hK0def.symm) hKimg0 hG00 hWmle hav hμ hℓ hR h2R hε₀
    have hAeq : Af μ = K0 * BoseGases.a v / (8 * μ * (ellH v μ ^ 3 + 1)) := by
      rw [hAdef]
      simp only [hμ, if_true]
    have hApos : 0 < Af μ := by
      rw [hAeq]
      positivity
    have hNbig : 4 * (1 + ellH v μ) * (1 + (Real.sqrt Submission.BoseGases.chiNormSq)⁻¹ * CE μ)
        * (1 + Kimg * Wm μ) * (1 + Kimg * Wm μ / Af μ) / Af μ + 4 ≤ ((HM μ).N : ℝ) := by
      have h1 : 4 * (1 + ellH v μ) * (1 + (Real.sqrt Submission.BoseGases.chiNormSq)⁻¹ * CE μ)
          * (1 + Kimg * Wm μ) * (1 + Kimg * Wm μ / Af μ) / Af μ ≤ ((Ax : ℕ) : ℝ) := by
        rw [hAx]
        exact Nat.le_ceil _
      have h2 : ((Ax + 4 : ℕ) : ℝ) ≤ ((HM μ).N : ℝ) := by
        exact_mod_cast (by omega : Ax + 4 ≤ (HM μ).N)
      push_cast at h2
      linarith
    have harith : (Real.sqrt Submission.BoseGases.chiNormSq)⁻¹ * CE μ
          / (Real.pi * ((HM μ).N : ℝ) / (2 * ellH v μ))
        + (Kimg * Wm μ) * (((Real.pi * ((HM μ).N : ℝ) / (2 * ellH v μ)) * ellH v μ)⁻¹
            + (R / ellH v μ) ^ 4
            + (((Real.pi * ((HM μ).N : ℝ) / (2 * ellH v μ)) * ellH v μ) ^ 2)⁻¹) ≤ Af μ :=
      chBarith (A := Af μ) (E := (Real.sqrt Submission.BoseGases.chiNormSq)⁻¹ * CE μ)
        (G := Kimg * Wm μ) (K0 := K0) (a := BoseGases.a v) (ℓ := ellH v μ) (μ := μ) (R := R)
        (N := ((HM μ).N : ℝ)) hAeq hav hμ hℓ hApos hE0 hG0' hR.le h2R hbig hNbig
    -- ## the pointwise bound `χ_Λ z·‖F z‖ ≤ A μ`
    have hpt : ∀ z : E3, (Work.BoseK15.corpusBox.chiLam (ellH v μ) z) *
        ‖Work.BoseBoxFock.PCFU.KχfrU v h μ fu (HM μ).N z
          - (∫ y : E3, ((Work.BoseK15.corpusBox.chiLam (ellH v μ) y : ℝ) : ℂ) *
              ((Work.BoseFixR.W1fun v h (ellH v μ) (y - z) : ℝ) : ℂ))‖ ≤ Af μ := by
      intro z
      have hb : (Work.BoseK15.corpusBox.chiLam (ellH v μ) z) *
          ‖Work.BoseBoxFock.PCFU.KχfrU v h μ fu (HM μ).N z
            - (∫ y : E3, ((Work.BoseK15.corpusBox.chiLam (ellH v μ) y : ℝ) : ℂ) *
                ((Work.BoseFixR.W1fun v h (ellH v μ) (y - z) : ℝ) : ℂ))‖
          ≤ (Real.sqrt Submission.BoseGases.chiNormSq)⁻¹ * CE μ
              / Work.BoseBoxFock.uvRad (ellH v μ) (HM μ).N
            + Kimg * Wm μ *
                ((Work.BoseBoxFock.uvRad (ellH v μ) (HM μ).N * ellH v μ)⁻¹ + (R / ellH v μ) ^ 4
                  + ((Work.BoseBoxFock.uvRad (ellH v μ) (HM μ).N * ellH v μ) ^ 2)⁻¹) :=
        chBpointwise (v := v) (h := h) (fu := fu) (μ := μ) (R := R) (N := (HM μ).N)
          (Work.BoseBox.sideAt_pos hμ hav) hN1 hΛ1 hΛℓ hI hcs hev hCEμ.1
          (hCEμ.2 (Work.BoseBoxFock.uvRad (ellH v μ) (HM μ).N) hΛ1)
          (hKimg (ellH v μ) hℓ h2R hRchi (Work.BoseBoxFock.uvRad (ellH v μ) (HM μ).N)
            hΛ1 hΛℓ) z
      rw [huv] at hb
      exact le_trans hb harith
    -- ## the state data for `BslotNormLe`
    have hΘm : Measurable (Work.BoseBoxFock.boxRestrictR (ellH v μ) Φ.toFun) := by
      unfold Work.BoseBoxFock.boxRestrictR
      exact (Φ.contDiff.continuous.measurable).mul
        (measurable_const.indicator (Submission.BoseGases.abox_measurable n (ellH v μ)))
    have hΘb : ∃ C : ℝ, ∀ x, |Work.BoseBoxFock.boxRestrictR (ellH v μ) Φ.toFun x| ≤ C := by
      obtain ⟨C, hC⟩ := (Submission.BoseGases.abox_compact n hℓ).exists_bound_of_continuousOn
        Φ.contDiff.continuous.continuousOn
      exact ⟨max C 0, fun x => boxRestrictR_abs_le (ellH v μ) C
        (fun x hx => by simpa [Real.norm_eq_abs] using hC x hx) x⟩
    have hΘs : Function.support (Work.BoseBoxFock.boxRestrictR (ellH v μ) Φ.toFun)
        ⊆ Submission.BoseGases.abox n (ellH v μ) := by
      intro x hx
      rw [Function.mem_support] at hx
      by_contra hcon
      exact hx (by rw [Work.BoseBoxFock.boxRestrictR, Set.indicator_of_notMem hcon, mul_zero])
    -- ## the pairing bound and the identification of the box norm
    have hbs := Work.BoseBoxFock.PCFU.BslotNormLe (v := v) (h := h) (fc := fc) (fu := fu)
      (μ := μ) (N := (HM μ).N) (n := n) i j hij hℓ (chKappa_pos' v hμ hav) hpt hΘm hΘb hΘs
    have hnormB : (∫ x in Submission.BoseGases.abox n (ellH v μ),
        (Work.BoseBoxFock.boxRestrictR (ellH v μ) Φ.toFun x) ^ 2)
        = Work.BoseBoxFix.normB v μ n Φ.toFun := by
      rw [Work.BoseBoxFix.normB, Work.BoseKinLoc.sqNormB, hside]
      refine MeasureTheory.setIntegral_congr_fun (Submission.BoseGases.abox_measurable n _)
        fun x hx => ?_
      rw [Work.BoseBoxFock.boxRestrictR, Set.indicator_of_mem hx, mul_one]
    rw [hnormB] at hbs
    exact hbs

end Work.BoseBoxFock.PCFU
