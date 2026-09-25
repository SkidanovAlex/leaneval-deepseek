import Mathlib
import Submission.Work.BourgainPlan.Maximal.mst_scalar_defs
import Submission.Work.BourgainPlan.Maximal.khatZMult_coeFn_star_mstWeyl
import Submission.Work.BourgainPlan.Maximal.mst_minor_lp_per_n
import Submission.Work.BourgainPlan.Maximal.ellp_interpolation
import Submission.Work.BourgainPlan.Maximal.eLpNorm_two_opMul_le

namespace Work.BourgainPlan.Maximal

open MeasureTheory Finset
open scoped BigOperators ENNReal
open Work.BourgainPlan.IonescuWainger

noncomputable section

/-! ## The multiplier with an `L^∞`-symbol on finitely supported sequences -/

/-- The Fourier multiplier `opMul Φ` with an `L^∞(𝕋)`-symbol, as a `ℂ`-linear map on the finitely
supported sequences (`opMul` needs a proof of `Memℓp · 2`, which `memℓp_finsupp` supplies).  This is
the analogue of `IonescuWainger.opArcLM` for a general symbol, and is the linear map to which the
Riesz–Thorin interpolation `ellp_interpolation` is applied. -/
def opMulFinsuppLM (Φ : Lp ℂ ⊤ (AddCircle.haarAddCircle (T := 1))) :
    (ℤ →₀ ℂ) →ₗ[ℂ] (ℤ → ℂ) where
  toFun f := opMul Φ (⇑f) (memℓp_finsupp f)
  map_add' f g := by
    have hft : ftLp (⇑(f + g)) (memℓp_finsupp (f + g))
        = ftLp (⇑f) (memℓp_finsupp f) + ftLp (⇑g) (memℓp_finsupp g) :=
      (ftLp_congr_memℓp (f := ⇑(f + g)) (g := ⇑f + ⇑g) (by funext i; simp)
          (memℓp_finsupp (f + g))
          ((memℓp_finsupp f).add (memℓp_finsupp g))).trans
        (ftLp_add (memℓp_finsupp f) (memℓp_finsupp g))
    funext n
    simp only [opMul, opMulLp]
    rw [hft, Lp.add_smul, map_add]
    rfl
  map_smul' c f := by
    have hft : ftLp (⇑(c • f)) (memℓp_finsupp (c • f))
        = c • ftLp (⇑f) (memℓp_finsupp f) :=
      (ftLp_congr_memℓp (f := ⇑(c • f)) (g := c • ⇑f) (by funext i; simp)
          (memℓp_finsupp (c • f))
          ((memℓp_finsupp f).const_smul c)).trans (ftLp_smul c (memℓp_finsupp f))
    funext n
    simp only [opMul, opMulLp]
    rw [hft, ← Lp.smul_comm c Φ (ftLp (⇑f) (memℓp_finsupp f)), map_smul]
    rfl

theorem opMulFinsuppLM_apply (Φ : Lp ℂ ⊤ (AddCircle.haarAddCircle (T := 1))) (f : ℤ →₀ ℂ) :
    opMulFinsuppLM Φ f = opMul Φ (⇑f) (memℓp_finsupp f) := rfl

/-! ## The two conversions between the `∫⁻ ‖·‖ₑ^q` and the `eLpNorm` shapes -/

/-- From an `eLpNorm` bound to the `∫⁻ ‖·‖ₑ^p` shape: raise the bound to the power `p`. -/
lemma lintegral_rpow_le_of_eLpNorm_le_count {p B : ℝ} (hp : 0 < p) (hB : 0 ≤ B)
    {g f : ℤ → ℂ}
    (h : eLpNorm g (ENNReal.ofReal p) Measure.count
      ≤ ENNReal.ofReal B * eLpNorm f (ENNReal.ofReal p) Measure.count) :
    ∫⁻ n : ℤ, ‖g n‖ₑ ^ p ∂Measure.count
      ≤ ENNReal.ofReal (B ^ p) * ∫⁻ n : ℤ, ‖f n‖ₑ ^ p ∂Measure.count := by
  have hne : ENNReal.ofReal p ≠ 0 := ENNReal.ofReal_ne_zero_iff.mpr hp
  have htop : ENNReal.ofReal p ≠ ⊤ := ENNReal.ofReal_ne_top
  have hg : (eLpNorm g (ENNReal.ofReal p) Measure.count) ^ p
      = ∫⁻ n : ℤ, ‖g n‖ₑ ^ p ∂Measure.count := by
    rw [eLpNorm_eq_lintegral_rpow_enorm_toReal hne htop AEStronglyMeasurable.of_discrete,
      ENNReal.toReal_ofReal hp.le, ← ENNReal.rpow_mul, one_div_mul_cancel hp.ne',
      ENNReal.rpow_one]
  have hf : (eLpNorm f (ENNReal.ofReal p) Measure.count) ^ p
      = ∫⁻ n : ℤ, ‖f n‖ₑ ^ p ∂Measure.count := by
    rw [eLpNorm_eq_lintegral_rpow_enorm_toReal hne htop AEStronglyMeasurable.of_discrete,
      ENNReal.toReal_ofReal hp.le, ← ENNReal.rpow_mul, one_div_mul_cancel hp.ne',
      ENNReal.rpow_one]
  calc ∫⁻ n : ℤ, ‖g n‖ₑ ^ p ∂Measure.count
      = (eLpNorm g (ENNReal.ofReal p) Measure.count) ^ p := hg.symm
    _ ≤ (ENNReal.ofReal B * eLpNorm f (ENNReal.ofReal p) Measure.count) ^ p :=
        ENNReal.rpow_le_rpow h hp.le
    _ = ENNReal.ofReal (B ^ p) * ∫⁻ n : ℤ, ‖f n‖ₑ ^ p ∂Measure.count := by
        rw [ENNReal.mul_rpow_of_nonneg _ _ hp.le,
          ENNReal.ofReal_rpow_of_nonneg hB hp.le, hf]

/-- From a `∫⁻ ‖·‖ₑ^q ≤ C ∫⁻ ‖·‖^q` bound to the `eLpNorm` shape, taking the `q`-th root. -/
lemma eLpNorm_le_of_lintegral_rpow_le_count {q C : ℝ} (hq : 0 < q) (hC : 0 ≤ C)
    {f v : ℤ → ℂ}
    (h : ∫⁻ x : ℤ, ‖f x‖ₑ ^ q ∂Measure.count
        ≤ ENNReal.ofReal (C ^ q) * ∫⁻ x : ℤ, ‖v x‖ₑ ^ q ∂Measure.count) :
    eLpNorm f (ENNReal.ofReal q) Measure.count
      ≤ ENNReal.ofReal C * eLpNorm v (ENNReal.ofReal q) Measure.count := by
  have hqne : ENNReal.ofReal q ≠ 0 := ne_of_gt (ENNReal.ofReal_pos.mpr hq)
  have hL : (eLpNorm f (ENNReal.ofReal q) Measure.count) ^ q
      = ∫⁻ x : ℤ, ‖f x‖ₑ ^ q ∂Measure.count := by
    rw [eLpNorm_eq_lintegral_rpow_enorm_toReal hqne ENNReal.ofReal_ne_top
      AEStronglyMeasurable.of_discrete,
      ENNReal.toReal_ofReal hq.le, ← ENNReal.rpow_mul, one_div, inv_mul_cancel₀ hq.ne',
      ENNReal.rpow_one]
  have hR : (eLpNorm v (ENNReal.ofReal q) Measure.count) ^ q
      = ∫⁻ x : ℤ, ‖v x‖ₑ ^ q ∂Measure.count := by
    rw [eLpNorm_eq_lintegral_rpow_enorm_toReal hqne ENNReal.ofReal_ne_top
      AEStronglyMeasurable.of_discrete,
      ENNReal.toReal_ofReal hq.le, ← ENNReal.rpow_mul, one_div, inv_mul_cancel₀ hq.ne',
      ENNReal.rpow_one]
  rw [← hL, ← hR] at h
  rw [← ENNReal.ofReal_rpow_of_nonneg hC hq.le,
    ← ENNReal.mul_rpow_of_nonneg (ENNReal.ofReal C)
      (eLpNorm v (ENNReal.ofReal q) Measure.count) hq.le] at h
  exact (ENNReal.rpow_le_rpow_iff hq).mp h

/-- **The pointwise values of the minor-arc symbol class**: the `L^∞`-class `mstMinorCls` of
`khatZMult P (2^n) · (1 − Ξ_n)` is a.e. the product `star (mstWeyl P (2^n)) · (1 − mstXi …)`. -/
lemma mstMinorCls_coeFn (P : Polynomial ℤ) (l d : ℕ) (χ : ℝ) (η : ℝ → ℂ) (n : ℕ)
    (hη : MemLp (mstEta d χ η n) ⊤ (AddCircle.haarAddCircle (T := 1))) :
    (mstMinorCls P l d χ η n hη : AddCircle (1 : ℝ) → ℂ)
      =ᵐ[AddCircle.haarAddCircle (T := 1)]
      fun ξ => star (mstWeyl P (2 ^ n) ξ) * (1 - mstXi l d χ η n ξ) := by
  change ((khatZMult P (2 ^ n) - khatZMult P (2 ^ n) •
      arcSymbolLp (mstEta d χ η n) hη (mstU l n) :
      Lp ℂ ⊤ (AddCircle.haarAddCircle (T := 1))) : AddCircle (1 : ℝ) → ℂ)
    =ᵐ[AddCircle.haarAddCircle (T := 1)]
    fun ξ => star (mstWeyl P (2 ^ n) ξ) * (1 - mstXi l d χ η n ξ)
  have hsub := Lp.coeFn_sub (khatZMult P (2 ^ n))
    (khatZMult P (2 ^ n) • arcSymbolLp (mstEta d χ η n) hη (mstU l n))
  have hsmul := Lp.coeFn_lpSMul (r := ⊤) (khatZMult P (2 ^ n))
    (arcSymbolLp (mstEta d χ η n) hη (mstU l n))
  have hsmul' : ((khatZMult P (2 ^ n) •
        arcSymbolLp (mstEta d χ η n) hη (mstU l n) :
        Lp ℂ ⊤ (AddCircle.haarAddCircle (T := 1))) : AddCircle (1 : ℝ) → ℂ)
      =ᵐ[AddCircle.haarAddCircle (T := 1)]
      fun ξ => (khatZMult P (2 ^ n) : AddCircle (1 : ℝ) → ℂ) ξ
        * (arcSymbolLp (mstEta d χ η n) hη (mstU l n) : AddCircle (1 : ℝ) → ℂ) ξ := by
    filter_upwards [hsmul] with ξ h
    rw [h]; rfl
  have hk := khatZMult_coeFn_star_mstWeyl P (2 ^ n)
  have hx := arcSymbolLp_coeFn (mstEta d χ η n) hη (mstU l n)
  filter_upwards [hsub, hsmul', hk, hx] with ξ h1 h2 h3 h4
  rw [h1, Pi.sub_apply, h2, h3, h4]
  rw [show arcSymbol (mstEta d χ η n) (mstU l n) = mstXi l d χ η n from rfl]
  simp only [mul_sub, mul_one]

/-- **MST §4.1, eq. (61): the minor-arc `ℓᵖ` gain `(n+1)^{−2}` per scale.** Interpolating the two endpoints of the minor-arc operator `mstMinorOp = A_{2^n} − A_{2^n}Π_n` — the `ℓ^r` endpoint (`r = (1+p)/2`) from the landed `mst_minor_lp_per_n`, and the `ℓ²` endpoint with gain `(n+1)^{−α}` obtained from the pointwise bound `hsup` on the symbol `star (mstWeyl P (2^n) ξ) * (1 − mstXi l (P.natDegree) χ η n ξ)` together with the a.e. description of the class `mstMinorCls` (`khatZMult_coeFn_star_mstWeyl`, `arcSymbolLp_coeFn`) and Plancherel (`eLpNorm_two_opMul_le`) — Riesz–Thorin (`ellp_interpolation`, applied to the `ℂ`-linear map on finitely supported sequences built from `opMul`, cf. `opArcLM`) gives the `ℓᵖ` bound with the exponent `αθ`, where `θ = 2(p−1)/(p(3−p))`; hence `αθ ≥ 2` (i.e. `α ≥ p(3−p)/(p−1)`, the hypothesis `hα`) yields the gain `(n+1)^{−2}`. The conclusion is stated for finitely supported `g`, which is the form the interpolation produces and the form the §6 assembly consumes. -/
theorem mst_minor_per_n (hIW : Work.BourgainPlan.Maximal.IWSupersetBoundLift)
    (P : Polynomial ℤ) {p : ℝ} (hp : 1 < p) (hp2 : p < 2) (l : ℕ) (hl : 1 ≤ l) (χ : ℝ) (η : ℝ → ℂ)
    (hη : ∀ n : ℕ, MeasureTheory.MemLp
      (Work.BourgainPlan.Maximal.mstEta P.natDegree χ η n) ⊤ (AddCircle.haarAddCircle (T := 1)))
    (A : ℝ) (hA : 0 < A)
    (hcd : ∀ n : ℕ, ContDiff ℝ 2 (Work.BourgainPlan.Thm52.circleLift
      (Work.BourgainPlan.Maximal.mstEta P.natDegree χ η n)))
    (hbdd : ∀ (n : ℕ) (x : ℝ), ‖Work.BourgainPlan.Thm52.circleLift
      (Work.BourgainPlan.Maximal.mstEta P.natDegree χ η n) x‖ ≤ A)
    (hder : ∀ (n : ℕ) (x : ℝ), |x| * ‖deriv (Work.BourgainPlan.Thm52.circleLift
      (Work.BourgainPlan.Maximal.mstEta P.natDegree χ η n)) x‖ ≤ A)
    (hder2 : ∀ (n : ℕ) (x : ℝ), |x| ^ 2 * ‖iteratedDeriv 2 (Work.BourgainPlan.Thm52.circleLift
      (Work.BourgainPlan.Maximal.mstEta P.natDegree χ η n)) x‖ ≤ A)
    (hsupp : ∃ N₀ : ℕ, ∀ n : ℕ, N₀ ≤ n → ∀ ξ : Work.BourgainPlan.IonescuWainger.Circle,
      Work.BourgainPlan.Maximal.iwEps (Work.BourgainPlan.Maximal.mstRho l) (n ^ l) < ‖ξ‖ →
        Work.BourgainPlan.Maximal.mstEta P.natDegree χ η n ξ = 0)
    {α : ℝ} (hα : p * (3 - p) / (p - 1) ≤ α)
    (hsup : ∃ C : ℝ, 0 < C ∧ ∃ N₀ : ℕ, ∀ n : ℕ, N₀ ≤ n →
      ∀ ξ : Work.BourgainPlan.IonescuWainger.Circle,
        ‖star (Work.BourgainPlan.Maximal.mstWeyl P (2 ^ n) ξ) *
            (1 - Work.BourgainPlan.Maximal.mstXi l P.natDegree χ η n ξ)‖
          ≤ C * ((n : ℝ) + 1) ^ (-α)) :
    ∃ C : ℝ, 0 < C ∧ ∃ N₁ : ℕ, ∀ n : ℕ, N₁ ≤ n → ∀ (g : ℤ →₀ ℂ),
      ∫⁻ m : ℤ, ‖Work.BourgainPlan.Maximal.mstMinorOp P l P.natDegree χ η n (hη n)
          (⇑g) (Work.BourgainPlan.IonescuWainger.memℓp_finsupp g) m‖ₑ ^ p
          ∂MeasureTheory.Measure.count
        ≤ ENNReal.ofReal ((C * ((n : ℝ) + 1) ^ (-2 : ℝ)) ^ p) *
          ∫⁻ m : ℤ, ‖(⇑g : ℤ → ℂ) m‖ₑ ^ p ∂MeasureTheory.Measure.count := by
  classical
  have hp0 : (0 : ℝ) < p := lt_trans zero_lt_one hp
  have hpm1 : (0 : ℝ) < p - 1 := by linarith
  have h3p : (0 : ℝ) < 3 - p := by linarith
  have hαpos : 0 < α := lt_of_lt_of_le (by positivity) hα
  set r : ℝ := (1 + p) / 2 with hrdef
  have hr1 : 1 < r := by rw [hrdef]; linarith
  have hr2 : r < 2 := by rw [hrdef]; linarith
  set θ : ℝ := 2 * (p - 1) / (p * (3 - p)) with hθdef
  have hθ0 : 0 ≤ θ := by rw [hθdef]; positivity
  have hθ1 : θ ≤ 1 := by
    rw [hθdef]
    have hden : (0 : ℝ) < p * (3 - p) := by nlinarith
    rw [div_le_one hden]; nlinarith
  have hθp : 1 / p = (1 - θ) / r + θ / 2 := by
    rw [hθdef, hrdef]
    have hpn : p ≠ 0 := by linarith
    have h3n : 3 - p ≠ 0 := by linarith
    have h1n : 1 + p ≠ 0 := by linarith
    field_simp
    ring
  have hαθ : 2 ≤ α * θ := by
    rw [hθdef]
    have hz : 0 ≤ 2 * (p - 1) / (p * (3 - p)) := by positivity
    have hkey : p * (3 - p) / (p - 1) * (2 * (p - 1) / (p * (3 - p))) = 2 := by
      have hden : (0 : ℝ) < p * (3 - p) := by nlinarith
      field_simp
    calc (2 : ℝ) = p * (3 - p) / (p - 1) * (2 * (p - 1) / (p * (3 - p))) := hkey.symm
      _ ≤ α * (2 * (p - 1) / (p * (3 - p))) := mul_le_mul_of_nonneg_right hα hz
  obtain ⟨Cα, hCαpos, Nα, hNα⟩ := hsup
  obtain ⟨C₁, hC₁pos, N₁', hN₁'⟩ :=
    mst_minor_lp_per_n hIW P hr1 hr2 l hl χ η hη A hA hcd hbdd hder hder2 hsupp
  refine ⟨C₁ ^ (1 - θ) * Cα ^ θ, ?_, max Nα N₁', ?_⟩
  · exact mul_pos (Real.rpow_pos_of_pos hC₁pos (1 - θ)) (Real.rpow_pos_of_pos hCαpos θ)
  intro n hn g
  have hnα : Nα ≤ n := le_trans (le_max_left _ _) hn
  have hn₁ : N₁' ≤ n := le_trans (le_max_right _ _) hn
  set N : ℝ := (n : ℝ) + 1 with hNdef
  have hn0 : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg n
  have hN1 : (1 : ℝ) ≤ N := by rw [hNdef]; linarith
  have hNpos : (0 : ℝ) < N := lt_of_lt_of_le one_pos hN1
  set T : (ℤ →₀ ℂ) →ₗ[ℂ] (ℤ → ℂ) :=
    opMulFinsuppLM (mstMinorCls P l P.natDegree χ η n (hη n)) with hTdef
  have hTf : ∀ f : ℤ →₀ ℂ,
      T f = mstMinorOp P l P.natDegree χ η n (hη n) (⇑f) (memℓp_finsupp f) := by
    intro f
    rw [hTdef, opMulFinsuppLM_apply]
    rfl
  have hTf' : ∀ f : ℤ →₀ ℂ,
      T f = opMul (mstMinorCls P l P.natDegree χ η n (hη n)) (⇑f) (memℓp_finsupp f) := by
    intro f
    rw [hTdef, opMulFinsuppLM_apply]
  have hsymb : ∀ᵐ ξ ∂(AddCircle.haarAddCircle (T := 1)),
      ‖(mstMinorCls P l P.natDegree χ η n (hη n) : AddCircle (1 : ℝ) → ℂ) ξ‖
        ≤ Cα * N ^ (-α) := by
    filter_upwards [mstMinorCls_coeFn P l P.natDegree χ η n (hη n)] with ξ h
    rw [h, hNdef]
    exact hNα n hnα ξ
  have hT1 : ∀ f : ℤ →₀ ℂ, eLpNorm (T f) (ENNReal.ofReal 2) Measure.count
      ≤ ENNReal.ofReal (Cα * N ^ (-α)) * eLpNorm f (ENNReal.ofReal 2) Measure.count := by
    intro f
    have hμ : (0 : ℝ) ≤ Cα * N ^ (-α) :=
      le_of_lt (mul_pos hCαpos (Real.rpow_pos_of_pos hNpos _))
    have h := eLpNorm_two_opMul_le (Φ := mstMinorCls P l P.natDegree χ η n (hη n))
      (f := (⇑f : ℤ → ℂ)) (memℓp_finsupp f) (μ := Cα * N ^ (-α)) hμ hsymb
    rwa [← hTf' f] at h
  have hT0 : ∀ f : ℤ →₀ ℂ, eLpNorm (T f) (ENNReal.ofReal r) Measure.count
      ≤ ENNReal.ofReal C₁ * eLpNorm f (ENNReal.ofReal r) Measure.count := by
    intro f
    have h := hN₁' n hn₁ (⇑f) (memℓp_finsupp f)
    have h' : ∫⁻ m : ℤ, ‖(T f) m‖ₑ ^ r ∂Measure.count
        ≤ ENNReal.ofReal (C₁ ^ r) *
            ∫⁻ m : ℤ, ‖(⇑f : ℤ → ℂ) m‖ₑ ^ r ∂Measure.count := by
      have hcongr : (fun m : ℤ => ‖(T f) m‖ₑ ^ r)
          = fun m : ℤ =>
            ‖mstMinorOp P l P.natDegree χ η n (hη n) (⇑f) (memℓp_finsupp f) m‖ₑ ^ r := by
        funext m; rw [hTf f]
      rw [hcongr]; exact h
    exact eLpNorm_le_of_lintegral_rpow_le_count (lt_trans zero_lt_one hr1) hC₁pos.le h'
  have hmain := ellp_interpolation (q₀ := r) (q₁ := 2) (p := p) (θ := θ)
    (A := C₁) (B := Cα * N ^ (-α)) hr1.le hr2.le hp hθ0 hθ1 hθp hC₁pos
    (mul_pos hCαpos (Real.rpow_pos_of_pos hNpos _)) T hT0 hT1 g
  have hle : C₁ ^ (1 - θ) * (Cα * N ^ (-α)) ^ θ
      ≤ (C₁ ^ (1 - θ) * Cα ^ θ) * N ^ (-2 : ℝ) := by
    have h1 : (Cα * N ^ (-α)) ^ θ = Cα ^ θ * N ^ (-(α * θ)) := by
      rw [Real.mul_rpow hCαpos.le (Real.rpow_nonneg hNpos.le (-α)),
        ← Real.rpow_mul hNpos.le (-α) θ,
        show -α * θ = -(α * θ) by ring]
    have h2 : N ^ (-(α * θ)) ≤ N ^ (-2 : ℝ) :=
      Real.rpow_le_rpow_of_exponent_le hN1 (by linarith)
    rw [h1]
    calc C₁ ^ (1 - θ) * (Cα ^ θ * N ^ (-(α * θ)))
        = (C₁ ^ (1 - θ) * Cα ^ θ) * N ^ (-(α * θ)) := by ring
      _ ≤ (C₁ ^ (1 - θ) * Cα ^ θ) * N ^ (-2 : ℝ) :=
          mul_le_mul_of_nonneg_left h2
            (mul_nonneg (Real.rpow_nonneg hC₁pos.le _) (Real.rpow_nonneg hCαpos.le _))
  have hstep : eLpNorm (T g) (ENNReal.ofReal p) Measure.count
      ≤ ENNReal.ofReal ((C₁ ^ (1 - θ) * Cα ^ θ) * N ^ (-2 : ℝ))
        * eLpNorm g (ENNReal.ofReal p) Measure.count :=
    hmain.trans (mul_le_mul_of_nonneg_right (ENNReal.ofReal_le_ofReal hle) (by simp))
  have hBnn : (0 : ℝ) ≤ (C₁ ^ (1 - θ) * Cα ^ θ) * N ^ (-2 : ℝ) := by positivity
  have hfin := lintegral_rpow_le_of_eLpNorm_le_count (p := p)
    (B := (C₁ ^ (1 - θ) * Cα ^ θ) * N ^ (-2 : ℝ)) hp0 hBnn hstep
  have hcongr : (fun m : ℤ =>
        ‖mstMinorOp P l P.natDegree χ η n (hη n) (⇑g) (memℓp_finsupp g) m‖ₑ ^ p)
      = fun m : ℤ => ‖(T g) m‖ₑ ^ p := by
    funext m; rw [hTf g]
  rw [hcongr]
  rw [hNdef] at hfin
  exact hfin

end

end Work.BourgainPlan.Maximal
