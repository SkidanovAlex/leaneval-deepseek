import Mathlib
import Submission.Work.BourgainPlan.Maximal.mst_major_defs
import Submission.Work.BourgainPlan.Maximal.mst_scalar_defs
import Submission.Work.BourgainPlan.Maximal.mst_level_defs
import Submission.Work.BourgainPlan.Maximal.mst_iw_lift
import Submission.Work.BourgainPlan.Maximal.contDiff_polyProfile
import Submission.Work.BourgainPlan.Maximal.mikhlin_conditions_scaled_bump
import Submission.Work.BourgainPlan.Maximal.eLpNorm_two_opMul_le
import Submission.Work.BourgainPlan.Maximal.mst_majErr_interp
import Submission.Work.BourgainPlan.Maximal.mstProfBumpS_coeff
import Submission.Work.BourgainPlan.Maximal.mst_theta_defs
import Submission.Work.BourgainPlan.IonescuWainger.OpArcDefs
import Submission.Work.BourgainPlan.IonescuWainger.OpArcLinear
import Submission.Work.BourgainPlan.Maximal.mst_minor_per_n
import Submission.Work.BourgainPlan.Maximal.mstU_annulus_tiling
import Submission.Work.BourgainPlan.Maximal.mstKernel_helpers
import Submission.Work.BourgainPlan.Maximal.mstEta_bump_data
import Submission.Work.BourgainPlan.Maximal.mstEta_arcSum_le
import Submission.Work.BourgainPlan.Maximal.memLp_scaled_bump
import Submission.Work.BourgainPlan.Maximal.polyProfile_fourier_dilation
import Submission.Work.BourgainPlan.KPWW.opArc_lp_bound_of_coeff
import Submission.Work.Maximal.mstPiBump_data

namespace Work.Maximal

open MeasureTheory Finset
open scoped BigOperators ENNReal

local notation "haarT" => (AddCircle.haarAddCircle (T := 1))
local notation "Circ" => Work.BourgainPlan.IonescuWainger.Circle

/-! ## The arc-symbol difference -/

lemma lrs_arcSymbolLp_sdiff {φ : Circ → ℂ} (hφ : MemLp φ ⊤ haarT) {E F : Finset Circ}
    (hFE : F ⊆ E) :
    Work.BourgainPlan.IonescuWainger.arcSymbolLp φ hφ (E \ F)
      = Work.BourgainPlan.IonescuWainger.arcSymbolLp φ hφ E
        - Work.BourgainPlan.IonescuWainger.arcSymbolLp φ hφ F := by
  refine Lp.ext ?_
  filter_upwards [Work.BourgainPlan.IonescuWainger.arcSymbolLp_coeFn φ hφ (E \ F),
    Work.BourgainPlan.IonescuWainger.arcSymbolLp_coeFn φ hφ E,
    Work.BourgainPlan.IonescuWainger.arcSymbolLp_coeFn φ hφ F,
    Lp.coeFn_sub (Work.BourgainPlan.IonescuWainger.arcSymbolLp φ hφ E)
      (Work.BourgainPlan.IonescuWainger.arcSymbolLp φ hφ F)] with ξ h1 h2 h3 h4
  rw [h1, h4, Pi.sub_apply, h2, h3, Work.BourgainPlan.IonescuWainger.arcSymbol_apply,
    Work.BourgainPlan.IonescuWainger.arcSymbol_apply,
    Work.BourgainPlan.IonescuWainger.arcSymbol_apply]
  exact eq_sub_of_add_eq (Finset.sum_sdiff hFE)

lemma lrs_opArc_sdiff {φ : Circ → ℂ} (hφ : MemLp φ ⊤ haarT) {E F : Finset Circ} (hFE : F ⊆ E)
    (f : ℤ → ℂ) (hf : Memℓp f 2) :
    Work.BourgainPlan.IonescuWainger.opArc φ hφ (E \ F) f hf
      = Work.BourgainPlan.IonescuWainger.opArc φ hφ E f hf
        - Work.BourgainPlan.IonescuWainger.opArc φ hφ F f hf := by
  simp only [Work.BourgainPlan.IonescuWainger.opArc]
  rw [lrs_arcSymbolLp_sdiff (φ := φ) hφ hFE]
  exact (Work.BourgainPlan.IonescuWainger.opMul_sub _ _ f hf).symm

/-! ## The lift of the level-`0` bump -/

lemma lrs_circleLift_mstEta_zero (d : ℕ) (χ : ℝ) (η : ℝ → ℂ)
    (hηsup : ∀ x : ℝ, 1 / 2 ≤ |x| → η x = 0) :
    Work.BourgainPlan.Thm52.circleLift (Work.BourgainPlan.Maximal.mstEta d χ η 0)
      = fun x : ℝ => η (-x) := by
  funext x
  by_cases hx : x ∈ Set.Ioc (-(1/2 : ℝ)) (1/2)
  · rw [Work.BourgainPlan.Thm52.circleLift_of_mem hx,
      Work.BourgainPlan.Maximal.mstEta_apply]
    have h1 : (2 : ℝ) ^ (((0 : ℕ) : ℝ) * ((d : ℝ) - χ)) = 1 := by norm_num
    rw [h1, one_mul]
    rcases eq_or_ne x (1/2) with h | h
    · subst h
      rw [Work.BourgainPlan.Maximal.iwRep_neg_half, hηsup (1/2) (by norm_num),
        hηsup (-(1/2)) (by norm_num)]
    · have hx' : -(1/2 : ℝ) < x ∧ x < 1/2 := ⟨hx.1, lt_of_le_of_ne hx.2 h⟩
      have hmem : -x ∈ Set.Ioc (-(1/2 : ℝ)) (1/2) :=
        ⟨by linarith [hx'.2], by linarith [hx'.1]⟩
      have hcoe : -((x : ℝ) : Circ) = ((-x : ℝ) : Circ) :=
        (AddCircle.coe_neg (1 : ℝ) (x := x)).symm
      rw [hcoe, Work.BourgainPlan.Maximal.iwRep_coe_of_mem hmem]
  · rw [Work.BourgainPlan.Thm52.circleLift_of_notMem hx]
    symm
    refine hηsup (-x) ?_
    have hxabs : (1 : ℝ) / 2 ≤ |x| := by
      by_cases h : x ≤ -(1/2 : ℝ)
      · rw [abs_of_nonpos (by linarith)]; linarith
      · have hlt : -(1/2 : ℝ) < x := lt_of_not_ge h
        have hx' : ¬(x ≤ (1/2 : ℝ)) := fun hle => hx ⟨hlt, hle⟩
        have h' : (1/2 : ℝ) < x := lt_of_not_ge hx'
        rw [abs_of_nonneg (by linarith)]; linarith
    rwa [abs_neg]

/-! ## Narrowness of the level bumps at the scale `(s+1)^l` -/

lemma lrs_mstEta_narrow_succ (l : ℕ) (hl : 1 ≤ l) (d : ℕ) (hd : 1 ≤ d) {χ : ℝ}
    (hχd : χ < (d : ℝ)) (η : ℝ → ℂ) (hηc : Continuous η)
    (hηsup : ∀ x : ℝ, 1 / 2 ≤ |x| → η x = 0) :
    ∃ s₀ : ℕ, ∀ s : ℕ, s₀ ≤ s → ∀ ξ : Circ,
      Work.BourgainPlan.Maximal.iwEps (Work.BourgainPlan.Maximal.mstRho l) ((s + 1) ^ l) < ‖ξ‖ →
        Work.BourgainPlan.Maximal.mstEta d χ η s ξ = 0 := by
  have hσ : 0 < (d : ℝ) - χ := by
    have h1 : (1 : ℝ) ≤ (d : ℝ) := by exact_mod_cast hd
    linarith
  obtain ⟨s₁, hs₁⟩ := Work.BourgainPlan.Maximal.exists_rpow_ten_add_one_lt ((d : ℝ) - χ) hσ
  refine ⟨max s₁ 1, fun s hs ξ hξ => ?_⟩
  have hs1 : 1 ≤ s := le_trans (le_max_right _ _) hs
  have hsle : s₁ ≤ s := le_trans (le_max_left _ _) hs
  have hlt : 1 / (2 * (2 : ℝ) ^ ((s : ℝ) * ((d : ℝ) - χ)))
      < Real.exp (-(((s : ℝ) + 1) ^ (1 / 10 : ℝ))) :=
    Work.BourgainPlan.Maximal.inv_two_mul_two_rpow_lt_exp (σ := (d : ℝ) - χ) (hs₁ s hsle)
  have hE : Work.BourgainPlan.Maximal.iwEps (Work.BourgainPlan.Maximal.mstRho l) ((s + 1) ^ l)
      = Real.exp (-(((s : ℝ) + 1) ^ (1 / 10 : ℝ))) := by
    rw [Work.BourgainPlan.Maximal.iwEps,
      Work.BourgainPlan.Maximal.mstRho_pow_eq l hl (s + 1) (by omega)]
    simp only [Nat.cast_add, Nat.cast_one]
  rw [hE] at hξ
  set c : ℝ := (2 : ℝ) ^ ((s : ℝ) * ((d : ℝ) - χ)) with hcdef
  have hcpos : 0 < c := Real.rpow_pos_of_pos (by norm_num) _
  have hc1 : 1 ≤ |c| := by
    rw [abs_of_pos hcpos]
    exact Real.one_le_rpow (by norm_num) (by positivity)
  have hmem := (Work.BourgainPlan.Maximal.memLp_scaled_bump (η := η) (c := c) hc1 hηc hηsup).2
  have hgt : 1 / (2 * |c|) < ‖ξ‖ := by
    rw [abs_of_pos hcpos]
    linarith
  have h0 := hmem ξ hgt
  rw [Work.BourgainPlan.Maximal.mstEta_apply]
  simpa only [hcdef] using h0



/-- **The base term of the Rademacher–Menshov reduction of the level-`s` model of MST Theorem 7.**  The weight-free arc operator at the *first* scale (`k = 0`, i.e. the profile `Φ_{2^0} = Φ_1`) of the level-`s` annulus model — the symbol `star (Φ_1) · η_s` translated to the arcs `𝒰(s+1) ∖ 𝒰(s)` — is `ℓ^r`-bounded by `C (s+1) log(s+2)`, uniformly in `s`, for `1 < r < 2`.

Route (granted for this lemma).  The hypothesis `hΘ` is *not* needed if the Ionescu–Wainger route below is taken; it is included because either route is acceptable.

* **IW route (preferred).**  Apply `Work.BourgainPlan.Maximal.IWSupersetBoundLift` (`mst_iw_lift.lean`, unconditional) to the circle symbol `ψ_s := fun ξ => star (mstProf P 1 ξ) * mstEta d χ η s ξ`, over the arc sets `iwSigma (mstRho l) ((s+1)^l) = mstU l (s+1)` and `iwSigma (mstRho l) (s^l) = mstU l s`, and combine the two bounds with `opArc_sdiff` (the annulus `mstLevel l (s+1) \ mstLevel l s` is the difference, using `mstLevel_mono`).  The hypotheses of `IWSupersetBoundLift`:
  - *lift identity*: `circleLift ψ_s = fun x : ℝ => polyProfile P 1 x * η (2^{s(d-χ)} * (-x))`.  (Warning: `circleLift ψ x = ψ (-(x : 𝕋))`, so `star (mstProf P 1 (-(x:𝕋))) = star (polyProfile P 1 (-x)) = polyProfile P 1 x` and `mstEta d χ η s (-(x:𝕋)) = η (-(c_s x))` — mind the sign, and mind `iwRep_coe_of_mem` for `x ∈ Ioc (-1/2) (1/2)`.  For `x ∉ Ioc (-1/2) (1/2)` both sides vanish because `η (c_s * u) = 0` whenever `|c_s * u| ≥ 1/2` and `|u| ≥ 1/2 ⟹ |c_s u| ≥ c_s/2 ≥ 1/2` (as `c_s = 2^{s(d-χ)} ≥ 1`, which follows from `χ < 1/10`, `2 ≤ P.natDegree`).)
  - *smoothness*: that function is `ContDiff ℝ 2` — a product of `polyProfile P 1` (a fixed `C²` function of the real variable, `contDiff_polyProfile`) and `η (c_s ·)` (`ContDiff ℝ 2 η` composed with a linear map) — and it is compactly supported in `[-1/(2c_s), 1/(2c_s)]`, strictly inside the fundamental domain for `s ≥ 1`.
  - *Mikhlin bounds*: `‖·‖ ≤ M·1`, `|x|‖D·‖ ≤ C₁`, `|x|²‖D²·‖ ≤ C₂` with constants depending only on `M`, `P` and `1` (not on `s`): use `‖polyProfile P 1‖ ≤ 1`, the boundedness of its normalised derivatives on the fundamental interval, Leibniz, and `|x|·c_s·‖η'(c_s x)‖ = |c_s x|·‖η'(c_s x)‖ ≤ M` (the same computation as `scaled_bump_mikhlin_bounds`).
  - *narrowness*: for large `s` the support radius `1/(2c_s)` is `≤ ε := exp(-(s+1)^{1/10}) = exp(-(((s+1)^l))^{mstRho l})`; likewise for `N = s^l`.  For the finitely many small `s` a crude bound (the symbol is a fixed arc sum of finitely many bounded symbols) must be absorbed into `C` — e.g. the trivial `ℓ^r` kernel bound from `mstProfBumpS_coeff` at `N = 1`, `s` fixed.
  The conclusion of `IWSupersetBoundLift` is a `lintegral` bound; convert it to the `eLpNorm` shape with the `eLpNorm`/`lintegral` conversions, and absorb the resulting constant (a fixed multiple of `M`, independent of `s`) into `C (s+1) log(s+2) ≥ C log 2` (valid for all `s` since `s+1 ≥ 1`, `log (s+2) ≥ log 2`).
* **RM/Θ route (alternative).**  Write `Φ_1 = Φ_{2^M} - Σ_{j<M}(Φ_{2^{j+1}} - Φ_{2^j})` for a free integer `M`; the second group is the signed lacunary combination `Θ_ε` with `i = 0` and `ε_j ∈ {0,1}`, bounded by `C log(s+2)` through `MSTThetaBound` + `mstThetaBump_opArc_lp` (`mst_lvl_defs.lean`); the first term has a symbol of pointwise modulus `≲ 2^{-M/d}` on the bump support (`polyProfile_decay_sharp`), so it is `ℓ²`-small and trivial-`ℓ^{r₀}`-bounded (coefficient kernel from `mstProfBumpS_coeff`), interpolated by `opMulFinsuppLM_interp`. -/
theorem mst_lrs_base
    (P : Polynomial ℤ) (hd : 2 ≤ P.natDegree) (hc : 0 < P.leadingCoeff)
    (l : ℕ) (hl : 1 ≤ l) {χ : ℝ} (hχ0 : 0 < χ) (hχ1 : χ < 1 / 10)
    (η : ℝ → ℂ) (M : ℝ) (hM : 0 < M) (hηc : ContDiff ℝ 2 η)
    (hηbd : ∀ x : ℝ, ‖η x‖ ≤ M)
    (hder1 : ∀ x : ℝ, |x| * ‖deriv η x‖ ≤ M)
    (hder2 : ∀ x : ℝ, |x| ^ 2 * ‖iteratedDeriv 2 η x‖ ≤ M)
    (hηsup : ∀ x : ℝ, 1 / 2 ≤ |x| → η x = 0)
    (hΘ : Work.BourgainPlan.Maximal.MSTThetaBound)
    (hpi : ∀ (N s : ℕ), MeasureTheory.MemLp
      (fun ζ : Work.BourgainPlan.IonescuWainger.Circle =>
        star (Work.BourgainPlan.Maximal.mstProf P N ζ) *
          Work.BourgainPlan.Maximal.mstEta P.natDegree χ η s ζ) ⊤
      (AddCircle.haarAddCircle (T := 1)))
    {r : ℝ} (hr : 1 < r) (hr2 : r < 2) :
    ∃ C : ℝ, 0 < C ∧ ∀ s : ℕ, ∀ g : ℤ →₀ ℂ,
      MeasureTheory.eLpNorm (fun m : ℤ =>
          Work.BourgainPlan.IonescuWainger.opMul
            (Work.BourgainPlan.IonescuWainger.arcSymbolLp
              (fun ζ : Work.BourgainPlan.IonescuWainger.Circle =>
                star (Work.BourgainPlan.Maximal.mstProf P (2 ^ 0) ζ) *
                  Work.BourgainPlan.Maximal.mstEta P.natDegree χ η s ζ)
              (hpi (2 ^ 0) s)
              (Work.BourgainPlan.Maximal.mstLevel l (s + 1) \
                Work.BourgainPlan.Maximal.mstLevel l s))
            (⇑g) (Work.BourgainPlan.IonescuWainger.memℓp_finsupp g) m)
        (ENNReal.ofReal r) (MeasureTheory.Measure.count)
        ≤ ENNReal.ofReal (C * (((s : ℝ) + 1) * Real.log ((s : ℝ) + 2)))
          * MeasureTheory.eLpNorm (⇑g) (ENNReal.ofReal r) MeasureTheory.Measure.count := by
  have hd1 : 1 ≤ P.natDegree := by omega
  have hχd : χ < (P.natDegree : ℝ) := by
    have h2 : (2 : ℝ) ≤ (P.natDegree : ℝ) := by exact_mod_cast hd
    linarith
  have hχ1d : χ + 1 ≤ (P.natDegree : ℝ) := by
    have h2 : (2 : ℝ) ≤ (P.natDegree : ℝ) := by exact_mod_cast hd
    linarith
  have hη2 : ∀ x : ℝ, 1 / 2 < |x| → η x = 0 := fun x hx => hηsup x hx.le
  have hρ : 0 < Work.BourgainPlan.Maximal.mstRho l := by
    rw [Work.BourgainPlan.Maximal.mstRho]
    have hl0 : (0 : ℝ) < (l : ℝ) := by exact_mod_cast (by omega : 0 < l)
    positivity
  have hlog2 : 0 < Real.log 2 := Real.log_pos one_lt_two
  obtain ⟨Ciw, hCiwpos, N₁, hN₁⟩ :=
    Work.BourgainPlan.Maximal.iwSupersetBoundLift_proof
      (Work.BourgainPlan.Maximal.mstRho l) hρ r hr
  obtain ⟨A, hApos, hAdata⟩ :=
    mstPiBump_data P hd hχ1 η hM hηc hηbd hder1 hder2 hηsup
  obtain ⟨s₀, hs₀⟩ := lrs_mstEta_narrow_succ l hl P.natDegree hd1 hχd η hηc.continuous hηsup
  have hcd0 : ContDiff ℝ 2 (Work.BourgainPlan.Thm52.circleLift
      (Work.BourgainPlan.Maximal.mstEta P.natDegree χ η 0)) := by
    rw [lrs_circleLift_mstEta_zero P.natDegree χ η hηsup]
    exact hηc.comp (by fun_prop)
  obtain ⟨Kb, hKbpos, hKb⟩ := Work.BourgainPlan.Maximal.mstProfBumpS_coeff P P.natDegree χ η M
    hM.le hχ1d hηbd hη2 hcd0
  have hCiwA : 0 < Ciw * A := mul_pos hCiwpos hApos
  set S : ℕ := max N₁ (max s₀ 1) with hSdef
  have hSge1 : 1 ≤ S := by
    rw [hSdef]
    exact le_trans (le_max_right s₀ 1) (le_max_right N₁ (max s₀ 1))
  have hSgeN₁ : N₁ ≤ S := by rw [hSdef]; exact le_max_left _ _
  have hSges₀ : s₀ ≤ S := by
    rw [hSdef]
    exact le_trans (le_max_left s₀ 1) (le_max_right N₁ (max s₀ 1))
  set Ksum : ℝ := ∑ t ∈ Finset.range (S + 1),
      (((Work.BourgainPlan.Maximal.mstLevel l (t + 1) \
        Work.BourgainPlan.Maximal.mstLevel l t).card : ℝ)) * Kb with hKsumdef
  have hKsum_nonneg : 0 ≤ Ksum := by
    rw [hKsumdef]
    exact Finset.sum_nonneg (fun t _ => mul_nonneg (Nat.cast_nonneg _) hKbpos.le)
  set Ctot : ℝ := (2 * (Ciw * A) + Ksum + 1) / Real.log 2 with hCtotdef
  have hCtotpos : 0 < Ctot := by
    rw [hCtotdef]
    exact div_pos (by linarith) hlog2
  have hCtotlog : Ctot * Real.log 2 = 2 * (Ciw * A) + Ksum + 1 := by
    rw [hCtotdef, div_mul_cancel₀ _ hlog2.ne']
  have hlogkey : ∀ s : ℕ, Real.log 2 ≤ ((s : ℝ) + 1) * Real.log ((s : ℝ) + 2) := by
    intro s
    have h1 : Real.log 2 ≤ Real.log ((s : ℝ) + 2) :=
      Real.log_le_log (by norm_num) (by linarith [Nat.cast_nonneg (α := ℝ) s])
    have h2 : (1 : ℝ) ≤ (s : ℝ) + 1 := by linarith [Nat.cast_nonneg (α := ℝ) s]
    have h3 : 0 ≤ Real.log ((s : ℝ) + 2) := Real.log_nonneg (by linarith [Nat.cast_nonneg (α := ℝ) s])
    calc Real.log 2 ≤ Real.log ((s : ℝ) + 2) := h1
      _ = 1 * Real.log ((s : ℝ) + 2) := (one_mul _).symm
      _ ≤ ((s : ℝ) + 1) * Real.log ((s : ℝ) + 2) := mul_le_mul_of_nonneg_right h2 h3
  refine ⟨Ctot, hCtotpos, fun s g => ?_⟩
  set ψ : Circ → ℂ := fun ζ => star (Work.BourgainPlan.Maximal.mstProf P (2 ^ 0) ζ) *
      Work.BourgainPlan.Maximal.mstEta P.natDegree χ η s ζ with hψdef
  set E : Finset Circ := Work.BourgainPlan.Maximal.mstLevel l (s + 1) \
      Work.BourgainPlan.Maximal.mstLevel l s with hEdef
  have hψml : MemLp ψ ⊤ haarT := hpi (2 ^ 0) s
  have hgl : Memℓp (⇑g : ℤ → ℂ) 2 := Work.BourgainPlan.IonescuWainger.memℓp_finsupp g
  set Nf : ℝ≥0∞ := MeasureTheory.eLpNorm (⇑g) (ENNReal.ofReal r) MeasureTheory.Measure.count
    with hNfdef
  change MeasureTheory.eLpNorm (Work.BourgainPlan.IonescuWainger.opArc ψ hψml E (⇑g) hgl)
      (ENNReal.ofReal r) MeasureTheory.Measure.count
      ≤ ENNReal.ofReal (Ctot * (((s : ℝ) + 1) * Real.log ((s : ℝ) + 2))) * Nf
  by_cases hs : S ≤ s
  · -- ================= large scales =================
    have hsub : Work.BourgainPlan.Maximal.mstLevel l s ⊆
        Work.BourgainPlan.Maximal.mstLevel l (s + 1) :=
      Work.BourgainPlan.Maximal.mstLevel_mono l s
    have hEs : Work.BourgainPlan.Maximal.mstLevel l s = Work.BourgainPlan.Maximal.mstU l s := by
      rw [Work.BourgainPlan.Maximal.mstLevel, if_neg (by omega : s ≠ 0)]
    have hsdiff : Work.BourgainPlan.IonescuWainger.opArc ψ hψml E (⇑g) hgl
        = Work.BourgainPlan.IonescuWainger.opArc ψ hψml
            (Work.BourgainPlan.Maximal.mstLevel l (s + 1)) (⇑g) hgl
          - Work.BourgainPlan.IonescuWainger.opArc ψ hψml
            (Work.BourgainPlan.Maximal.mstLevel l s) (⇑g) hgl := by
      rw [hEdef]
      exact lrs_opArc_sdiff hψml hsub _ _
    obtain ⟨hcdψ, hbdψ, hderψ, hder2ψ⟩ := hAdata s
    have hsuppψ : ∀ ξ : Circ,
        Work.BourgainPlan.Maximal.iwEps (Work.BourgainPlan.Maximal.mstRho l) ((s + 1) ^ l)
          < ‖ξ‖ → ψ ξ = 0 := by
      intro ξ hξ
      have h0 := hs₀ s (le_trans hSges₀ hs) ξ hξ
      simp only [hψdef]
      exact mul_eq_zero.mpr (Or.inr h0)
    have hNle1 : N₁ ≤ (s + 1) ^ l :=
      le_trans (le_trans hSgeN₁ hs)
        (le_trans (by omega : s ≤ s + 1) (Nat.le_self_pow (by omega : l ≠ 0) (s + 1)))
    have hb1 : MeasureTheory.eLpNorm (Work.BourgainPlan.IonescuWainger.opArc ψ hψml
          (Work.BourgainPlan.Maximal.mstU l (s + 1)) (⇑g) hgl)
        (ENNReal.ofReal r) MeasureTheory.Measure.count
        ≤ ENNReal.ofReal (Ciw * A) * Nf := by
      have h := hN₁ ((s + 1) ^ l) hNle1
        (ε := Work.BourgainPlan.Maximal.iwEps (Work.BourgainPlan.Maximal.mstRho l) ((s + 1) ^ l))
        (Real.exp_pos _) le_rfl ψ hψml hcdψ hApos.le hbdψ hderψ hder2ψ hsuppψ (⇑g) hgl
      have h' := Work.BourgainPlan.Maximal.eLpNorm_le_of_lintegral_rpow_le_count
        (q := r) (C := Ciw * A) (lt_trans zero_lt_one hr) hCiwA.le
        (f := fun n : ℤ => Work.BourgainPlan.IonescuWainger.opArc ψ hψml
          (Work.BourgainPlan.Maximal.mstU l (s + 1)) (⇑g) hgl n) (v := ⇑g)
        (by simpa only [Work.BourgainPlan.Maximal.mstU_apply] using h)
      rw [hNfdef]
      exact h'
    have hNle2 : N₁ ≤ s ^ l :=
      le_trans (le_trans hSgeN₁ hs) (Nat.le_self_pow (by omega : l ≠ 0) s)
    have hεle2 : Work.BourgainPlan.Maximal.iwEps (Work.BourgainPlan.Maximal.mstRho l) ((s + 1) ^ l)
        ≤ Work.BourgainPlan.Maximal.iwEps (Work.BourgainPlan.Maximal.mstRho l) (s ^ l) := by
      rw [Work.BourgainPlan.Maximal.iwEps, Work.BourgainPlan.Maximal.iwEps, Real.exp_le_exp,
        neg_le_neg_iff]
      exact Real.rpow_le_rpow (Nat.cast_nonneg _)
        (Nat.cast_le.mpr (Nat.pow_le_pow_left (by omega) l)) hρ.le
    have hb2 : MeasureTheory.eLpNorm (Work.BourgainPlan.IonescuWainger.opArc ψ hψml
          (Work.BourgainPlan.Maximal.mstU l s) (⇑g) hgl)
        (ENNReal.ofReal r) MeasureTheory.Measure.count
        ≤ ENNReal.ofReal (Ciw * A) * Nf := by
      have h := hN₁ (s ^ l) hNle2
        (ε := Work.BourgainPlan.Maximal.iwEps (Work.BourgainPlan.Maximal.mstRho l) ((s + 1) ^ l))
        (Real.exp_pos _) hεle2 ψ hψml hcdψ hApos.le hbdψ hderψ hder2ψ hsuppψ (⇑g) hgl
      have h' := Work.BourgainPlan.Maximal.eLpNorm_le_of_lintegral_rpow_le_count
        (q := r) (C := Ciw * A) (lt_trans zero_lt_one hr) hCiwA.le
        (f := fun n : ℤ => Work.BourgainPlan.IonescuWainger.opArc ψ hψml
          (Work.BourgainPlan.Maximal.mstU l s) (⇑g) hgl n) (v := ⇑g)
        (by simpa only [Work.BourgainPlan.Maximal.mstU_apply] using h)
      rw [hNfdef]
      exact h'
    have hb1' : MeasureTheory.eLpNorm (Work.BourgainPlan.IonescuWainger.opArc ψ hψml
          (Work.BourgainPlan.Maximal.mstLevel l (s + 1)) (⇑g) hgl)
        (ENNReal.ofReal r) MeasureTheory.Measure.count ≤ ENNReal.ofReal (Ciw * A) * Nf := by
      rw [Work.BourgainPlan.Maximal.mstLevel_succ]
      exact hb1
    have hb2' : MeasureTheory.eLpNorm (Work.BourgainPlan.IonescuWainger.opArc ψ hψml
          (Work.BourgainPlan.Maximal.mstLevel l s) (⇑g) hgl)
        (ENNReal.ofReal r) MeasureTheory.Measure.count ≤ ENNReal.ofReal (Ciw * A) * Nf := by
      rw [hEs]
      exact hb2
    rw [hsdiff]
    refine (eLpNorm_sub_le (ENNReal.one_le_ofReal.mpr hr.le)).trans ?_
    refine (add_le_add hb1' hb2').trans ?_
    rw [← add_mul, ← ENNReal.ofReal_add (by positivity) (by positivity)]
    refine mul_le_mul_of_nonneg_right (ENNReal.ofReal_le_ofReal ?_) bot_le
    have hstep : Ctot * Real.log 2 ≤ Ctot * (((s : ℝ) + 1) * Real.log ((s : ℝ) + 2)) :=
      mul_le_mul_of_nonneg_left (hlogkey s) hCtotpos.le
    rw [hCtotlog] at hstep
    linarith
  · -- ================= small scales =================
    have hslt : s < S := lt_of_not_ge hs
    have hK := hKb 1 s le_rfl
    have hcsum : Summable (fun n : ℤ =>
        ‖∫ θ : Circ, ψ θ * star (fourier n θ) ∂haarT‖) := by
      simp only [hψdef, pow_zero]
      exact hK.1
    have hcK : (∑' n : ℤ, ‖∫ θ : Circ, ψ θ * star (fourier n θ) ∂haarT‖) ≤ Kb := by
      simp only [hψdef, pow_zero]
      exact hK.2
    have htriv : MeasureTheory.eLpNorm (Work.BourgainPlan.IonescuWainger.opArc ψ hψml E (⇑g) hgl)
        (ENNReal.ofReal r) MeasureTheory.Measure.count
        ≤ ENNReal.ofReal ((E.card : ℝ) * Kb) * Nf := by
      have h := Work.BourgainPlan.KPWW.opArc_lp_bound_of_coeff (p := r) hr.le hψml hcsum
        (fun m => rfl) hcK E (⇑g) hgl
      rw [hNfdef]
      exact h
    have hsingle : ((E.card : ℝ)) * Kb ≤ Ksum := by
      rw [hEdef, hKsumdef]
      refine Finset.single_le_sum (f := fun t : ℕ =>
        (((Work.BourgainPlan.Maximal.mstLevel l (t + 1) \
          Work.BourgainPlan.Maximal.mstLevel l t).card : ℝ)) * Kb) ?_
        (Finset.mem_range.mpr (by omega))
      intro t _
      exact mul_nonneg (Nat.cast_nonneg _) hKbpos.le
    have hfinal : ((E.card : ℝ)) * Kb ≤ Ctot * (((s : ℝ) + 1) * Real.log ((s : ℝ) + 2)) := by
      have hstep : Ksum ≤ Ctot * Real.log 2 := by
        rw [hCtotlog]; linarith
      have hstep2 : Ctot * Real.log 2 ≤ Ctot * (((s : ℝ) + 1) * Real.log ((s : ℝ) + 2)) :=
        mul_le_mul_of_nonneg_left (hlogkey s) hCtotpos.le
      linarith
    refine htriv.trans ?_
    exact mul_le_mul_of_nonneg_right (ENNReal.ofReal_le_ofReal hfinal) bot_le
end Work.Maximal
