import Mathlib
import Submission.Work.Maximal.mstWide_defs
import Submission.Work.Maximal.mstNuS_sub_mstWideModel_pointwise
import Submission.Work.BourgainPlan.Maximal.ellp_interpolation
import Submission.Work.BourgainPlan.Maximal.mst_majErr_interp
import Submission.Work.BourgainPlan.Maximal.eLpNorm_two_opMul_le
import Submission.Work.BourgainPlan.Maximal.opMul_sub
import Submission.Work.BourgainPlan.Maximal.eLpNorm_varRhoAll_le_geometric
import Submission.Work.BourgainPlan.Maximal.mstU_card_le_exp
import Submission.Work.BourgainPlan.Maximal.mstKernel_helpers
import Submission.Work.Maximal.mstNuS_sub_mstWideModel_triv_lp
import Submission.Work.Maximal.mstNuS_sub_mstWideModel_coeff
import Submission.Work.Maximal.mstNuS_sub_mstWideModel_tail_arith

/-!
# Half 1 of the large-scale `ℓʳ` level estimate: the narrow-to-wide replacement in the tail

This file proves `Work.Maximal.mstNuS_sub_mstWideModel_lr_tail`, the first half of the large-scale
`ℓʳ` level estimate of Mirek–Stein–Trojan (arXiv:1512.07518, Theorem 8), as recorded in
`Submission/Work/Maximal/MST_WIDE_ROUTE.md`.

The narrow level model `A_k = opMul (mstNuSCls …) ` and the wide model `Ω_k = opMul (mstWideModel …)`
differ by a multiplier whose symbol is bounded pointwise by `ε_k = C (s+1)^{-δl} 2^{-k/(2d)}`
(`Work.Maximal.mstNuS_sub_mstWideModel_pointwise`).  Combined with

* the trivial kernel bound `‖(A_k - Ω_k) g‖_{ℓ^q} ≤ A_s ‖g‖_{ℓ^q}` for every `q ≥ 1`
  (`Work.Maximal.mstNuS_sub_mstWideModel_triv_lp`, whose constant `A_s` grows like
  `♯𝒰(s+1) ≲ e^{(s+1)^{1/10}}`),
* the `ℓ²` bound `≤ ε_k` (Plancherel) and
* Riesz–Thorin (`Work.BourgainPlan.Maximal.opMulFinsuppLM_interp`),

the `ℓʳ`-norm of the operator is `≤ A_s^{1-θ} ε_k^θ` with `θ = (1/q - 1/r)/(1/q - 1/2) > 0`, which is
geometrically decaying in `k`.  Since `2^{κ_s}` is doubly exponentially larger than
`e^{(s+1)^{1/10}}` (`Work.Maximal.mstNuS_sub_mstWideModel_tail_arith`), the triangle inequality over
the tail `k ≥ 2^{κ_s}` gives the bound `≤ 1 · ‖g‖_{ℓʳ}` for all large `s`.
-/

namespace Work.Maximal

open MeasureTheory Finset
open scoped BigOperators ENNReal

set_option autoImplicit false
set_option maxHeartbeats 4000000

local notation "Circ" => Work.BourgainPlan.IonescuWainger.Circle
local notation "haarT" => (AddCircle.haarAddCircle (T := 1))

noncomputable section

open Work.BourgainPlan.Maximal
open Work.BourgainPlan.IonescuWainger

/-- The fundamental-domain lift of the level-`0` bump is `x ↦ η (-x)`. -/
private lemma circleLift_mstEta_zero_eq_neg {d : ℕ} {χ : ℝ} {η : ℝ → ℂ}
    (hηsup : ∀ x : ℝ, 1 / 2 ≤ |x| → η x = 0) :
    Work.BourgainPlan.Thm52.circleLift (mstEta d χ η 0) = fun x : ℝ => η (-x) := by
  funext x
  by_cases hx : x ∈ Set.Ioc (-(1 / 2 : ℝ)) (1 / 2)
  · rw [Work.BourgainPlan.Thm52.circleLift_of_mem hx, mstEta_zero_eq]
    rcases eq_or_ne x (1 / 2) with h | h
    · subst h
      rw [iwRep_neg_half, hηsup (1 / 2) (by norm_num), hηsup (-(1 / 2)) (by norm_num)]
    · have hx' : -(1 / 2 : ℝ) < x ∧ x < 1 / 2 := ⟨hx.1, lt_of_le_of_ne hx.2 h⟩
      have hmem : -x ∈ Set.Ioc (-(1 / 2 : ℝ)) (1 / 2) :=
        ⟨by linarith [hx'.2], by linarith [hx'.1]⟩
      have hcoe : -((x : ℝ) : Circ) = ((-x : ℝ) : Circ) :=
        (AddCircle.coe_neg (1 : ℝ) (x := x)).symm
      rw [hcoe, iwRep_coe_of_mem hmem]
  · rw [Work.BourgainPlan.Thm52.circleLift_of_notMem hx]
    symm
    refine hηsup (-x) ?_
    have habs : (1 : ℝ) / 2 ≤ |x| := by
      rw [Set.mem_Ioc, not_and_or, not_lt, not_le] at hx
      rcases hx with h | h
      · rw [abs_of_nonpos (by linarith)]; linarith
      · rw [abs_of_pos (by linarith)]; linarith
    rwa [abs_neg]

/-- **The tail supremum of a family over `k ≥ K₀` as a supremum over the shifted family.** -/
private lemma iSup_tail_eq (K₀ : ℕ) (T : ℕ → ℤ → ℂ) (m : ℤ) :
    (⨆ k : ℕ, ⨆ (_ : K₀ ≤ k), ‖T k m‖ₑ) = ⨆ j : ℕ, ‖T (K₀ + j) m‖ₑ := by
  refine le_antisymm ?_ ?_
  · refine iSup_le fun k => iSup_le fun hk => ?_
    obtain ⟨j, rfl⟩ := Nat.exists_eq_add_of_le hk
    exact le_iSup (fun j : ℕ => ‖T (K₀ + j) m‖ₑ) j
  · refine iSup_le fun j => ?_
    exact (le_iSup (fun _ : K₀ ≤ K₀ + j => ‖T (K₀ + j) m‖ₑ) (Nat.le_add_right K₀ j)).trans
      (le_iSup (fun k : ℕ => ⨆ (_ : K₀ ≤ k), ‖T k m‖ₑ) (K₀ + j))

/-- Monotonicity of `eLpNorm` for `ℝ≥0∞`-valued functions (the general `eLpNorm_mono` needs a
`NormedAddCommGroup`, which `ℝ≥0∞` is not). -/
private lemma eLpNorm_mono_enorm {α : Type*} [MeasurableSpace α] {μ : Measure α} {p : ℝ}
    (hp : 0 < p) {f g : α → ℝ≥0∞} (hf : AEStronglyMeasurable f μ) (h : f ≤ g) :
    MeasureTheory.eLpNorm f (ENNReal.ofReal p) μ ≤ MeasureTheory.eLpNorm g (ENNReal.ofReal p) μ :=
  MeasureTheory.eLpNorm_mono_enorm hf (fun x => by simpa only [enorm_eq_self] using h x)

/-- **The summation step.**  If the individual operators of a family `T k`, `k ≥ K₀`, satisfy the
`ℓʳ` bound `‖T (K₀+j) v‖_{ℓʳ} ≤ M_j ‖v‖_{ℓʳ}` with `Σ_j M_j ≤ 1`, then the `ℓʳ`-norm of the
pointwise supremum over the tail is bounded by `‖v‖_{ℓʳ}`.  The proof is the triangle inequality
`sup_j ‖·‖ ≤ Σ_j ‖·‖` for `ℓʳ` (`eLpNorm_tsum_le_tsum_eLpNorm`). -/
private lemma tail_sup_le_of_per_k (K₀ : ℕ) (T : ℕ → ℤ → ℂ) (v : ℤ → ℂ) (Mexp : ℕ → ℝ)
    {r : ℝ} (hr : 1 ≤ r)
    (hperj : ∀ j : ℕ, MeasureTheory.eLpNorm (T (K₀ + j)) (ENNReal.ofReal r) Measure.count
      ≤ ENNReal.ofReal (Mexp j) * MeasureTheory.eLpNorm v (ENNReal.ofReal r) Measure.count)
    (hMnn : ∀ j : ℕ, 0 ≤ Mexp j) (hsumm : Summable Mexp) (hbound : (∑' j : ℕ, Mexp j) ≤ 1) :
    MeasureTheory.eLpNorm (fun m : ℤ => ⨆ k : ℕ, ⨆ (_ : K₀ ≤ k), ‖T k m‖ₑ)
        (ENNReal.ofReal r) Measure.count
      ≤ MeasureTheory.eLpNorm v (ENNReal.ofReal r) Measure.count := by
  set N : ℝ≥0∞ := MeasureTheory.eLpNorm v (ENNReal.ofReal r) Measure.count with hNdef
  have hfun : (fun m : ℤ => ⨆ k : ℕ, ⨆ (_ : K₀ ≤ k), ‖T k m‖ₑ)
      = fun m : ℤ => ⨆ j : ℕ, ‖T (K₀ + j) m‖ₑ := funext fun m => iSup_tail_eq K₀ T m
  have h1 : MeasureTheory.eLpNorm (fun m : ℤ => ⨆ j : ℕ, ‖T (K₀ + j) m‖ₑ)
        (ENNReal.ofReal r) Measure.count
      ≤ MeasureTheory.eLpNorm (fun m : ℤ => ∑' j : ℕ, ‖T (K₀ + j) m‖ₑ)
        (ENNReal.ofReal r) Measure.count :=
    eLpNorm_mono_enorm (lt_of_lt_of_le zero_lt_one hr) (measurable_of_countable _).aestronglyMeasurable
      (fun m => iSup_le (fun j => ENNReal.le_tsum (f := fun j : ℕ => ‖T (K₀ + j) m‖ₑ) j))
  have h2 : MeasureTheory.eLpNorm (fun m : ℤ => ∑' j : ℕ, ‖T (K₀ + j) m‖ₑ)
        (ENNReal.ofReal r) Measure.count
      ≤ ∑' j : ℕ, MeasureTheory.eLpNorm (fun m : ℤ => ‖T (K₀ + j) m‖ₑ)
        (ENNReal.ofReal r) Measure.count :=
    eLpNorm_tsum_le_tsum_eLpNorm (ENNReal.one_le_ofReal.mpr hr) ENNReal.ofReal_ne_top
      (fun j => measurable_of_int _)
  have h3 : ∑' j : ℕ, MeasureTheory.eLpNorm (fun m : ℤ => ‖T (K₀ + j) m‖ₑ)
        (ENNReal.ofReal r) Measure.count
      ≤ ∑' j : ℕ, ENNReal.ofReal (Mexp j) * N := by
    refine ENNReal.tsum_le_tsum fun j => ?_
    rw [eLpNorm_enorm _ (measurable_of_countable _).aestronglyMeasurable, hNdef]
    exact hperj j
  have h4 : ∑' j : ℕ, ENNReal.ofReal (Mexp j) * N
      = (∑' j : ℕ, ENNReal.ofReal (Mexp j)) * N := ENNReal.tsum_mul_right
  have h5 : (∑' j : ℕ, ENNReal.ofReal (Mexp j)) ≤ 1 := by
    have htsum : (∑' j : ℕ, ENNReal.ofReal (Mexp j)) = ENNReal.ofReal (∑' j : ℕ, Mexp j) :=
      (ENNReal.ofReal_tsum_of_nonneg hMnn hsumm).symm
    rw [htsum]
    calc ENNReal.ofReal (∑' j : ℕ, Mexp j) ≤ ENNReal.ofReal 1 := ENNReal.ofReal_le_ofReal hbound
      _ = 1 := ENNReal.ofReal_one
  calc MeasureTheory.eLpNorm (fun m : ℤ => ⨆ k : ℕ, ⨆ (_ : K₀ ≤ k), ‖T k m‖ₑ)
        (ENNReal.ofReal r) Measure.count
      = MeasureTheory.eLpNorm (fun m : ℤ => ⨆ j : ℕ, ‖T (K₀ + j) m‖ₑ)
        (ENNReal.ofReal r) Measure.count := by rw [hfun]
    _ ≤ MeasureTheory.eLpNorm (fun m : ℤ => ∑' j : ℕ, ‖T (K₀ + j) m‖ₑ)
        (ENNReal.ofReal r) Measure.count := h1
    _ ≤ ∑' j : ℕ, MeasureTheory.eLpNorm (fun m : ℤ => ‖T (K₀ + j) m‖ₑ)
        (ENNReal.ofReal r) Measure.count := h2
    _ ≤ ∑' j : ℕ, ENNReal.ofReal (Mexp j) * N := h3
    _ = (∑' j : ℕ, ENNReal.ofReal (Mexp j)) * N := h4
    _ ≤ 1 * N := mul_le_mul_of_nonneg_right h5 (bot_le)
    _ = N := one_mul N
    _ = MeasureTheory.eLpNorm v (ENNReal.ofReal r) Measure.count := hNdef


/-- **Half 1 of the large-scale `ℓʳ` level estimate: the narrow-to-wide replacement is summable in
the scale `k`.**  With `ε_k = C (s+1)^{−δl} 2^{−k/(2d)}` (the pointwise symbol bound of
`mstNuS_sub_mstWideModel_pointwise`), Plancherel (`ℓ²` bound `≤ ε_k`), the trivial `♯`-bound in
`ℓʳ` and Riesz–Thorin (`ellp_interpolation`) give

  `‖(A_k − Ω_k) g‖_{ℓʳ} ≤ ε_k^{2−2/r} (♯ (s+1)^{−δl})^{2/r−1} ‖g‖_{ℓʳ}`,

and the geometric sum over `k ≥ 2^{κ_s}` is `≲ 1` because `2^{κ_s}` dominates `e^{C(s+1)^{1/10}}`
(`exists_rpow_ten_add_one_lt`).  Hence the `ℓʳ` norm of the pointwise supremum over the tail
`k ≥ 2^{κ_s}` of the modulus of the difference is bounded by `C‖g‖_{ℓʳ}`. -/
theorem mstNuS_sub_mstWideModel_lr_tail (P : Polynomial ℤ) (hd : 2 ≤ P.natDegree)
    (hc : 0 < P.leadingCoeff) (l : ℕ) (hl : 1 ≤ l) {χ : ℝ} (hχ0 : 0 < χ) (hχ1 : χ < 1 / 10)
    (η : ℝ → ℂ) (hηc : ContDiff ℝ 2 η) (hηsup : ∀ x : ℝ, 1 / 2 ≤ |x| → η x = 0)
    {δ : ℝ} (hδ : 0 < δ) (D : ℝ) (hD : 0 < D)
    (hGauss : ∀ (s : ℕ) (β : Work.BourgainPlan.IonescuWainger.Circle),
      β ∈ Work.BourgainPlan.Maximal.mstU l (s + 1) \ Work.BourgainPlan.Maximal.mstU l s →
      ‖Work.BourgainPlan.Maximal.mstG P β‖ ≤ D * ((s : ℝ) + 1) ^ (-(δ * l)))
    (hνsml : ∀ n s : ℕ, MeasureTheory.MemLp
      (Work.BourgainPlan.Maximal.mstNuS P l P.natDegree χ η n s) ⊤
      (AddCircle.haarAddCircle (T := 1)))
    (hΩml : ∀ k s : ℕ, MeasureTheory.MemLp
      (Work.Maximal.mstWideModel P l χ η k s) ⊤ (AddCircle.haarAddCircle (T := 1)))
    {r : ℝ} (hr : 1 < r) (hr2 : r < 2) :
    ∃ C : ℝ, 0 < C ∧ ∃ s₀ : ℕ, ∀ s : ℕ, s₀ ≤ s → ∀ g : ℤ →₀ ℂ,
      MeasureTheory.eLpNorm (fun m : ℤ => (⨆ k : ℕ,
          ⨆ (_ : 2 ^ (Work.BourgainPlan.Maximal.mstKappa P s) ≤ k),
          ‖Work.BourgainPlan.IonescuWainger.opMul
              (Work.BourgainPlan.Maximal.mstNuSCls P l P.natDegree χ η k s (hνsml k s))
              (⇑g) (Work.BourgainPlan.IonescuWainger.memℓp_finsupp g) m
            - Work.BourgainPlan.IonescuWainger.opMul
              ((hΩml k s).toLp (Work.Maximal.mstWideModel P l χ η k s))
              (⇑g) (Work.BourgainPlan.IonescuWainger.memℓp_finsupp g) m‖ₑ))
          (ENNReal.ofReal r) MeasureTheory.Measure.count
        ≤ ENNReal.ofReal C
          * MeasureTheory.eLpNorm (⇑g) (ENNReal.ofReal r) MeasureTheory.Measure.count := by
  -- ## 0. elementary consequences of the hypotheses
  have hd1 : 1 ≤ P.natDegree := by omega
  have hdR1 : (1 : ℝ) ≤ (P.natDegree : ℝ) := by exact_mod_cast hd1
  have hχd : χ ≤ (P.natDegree : ℝ) := by linarith
  have hδl : 0 < δ * l := mul_pos hδ (by exact_mod_cast hl)
  have hη2 : ∀ x : ℝ, 1 / 2 < |x| → η x = 0 := fun x hx => hηsup x hx.le
  -- ## 1. a bound for η and the `C²`-ness of the level-`0` lift
  obtain ⟨Mb, hMbpos, hηbd⟩ : ∃ M : ℝ, 0 < M ∧ ∀ x : ℝ, ‖η x‖ ≤ M := by
    obtain ⟨Cb, hCb⟩ := (isCompact_Icc (a := -(1 / 2 : ℝ)) (b := 1 / 2)).exists_bound_of_continuousOn
      hηc.continuous.continuousOn
    refine ⟨max Cb 1, by positivity, fun x => ?_⟩
    by_cases hx : |x| ≤ 1 / 2
    · exact le_trans (hCb x (by rw [Set.mem_Icc]; exact abs_le.mp hx)) (le_max_left _ _)
    · have hx' : (1 / 2 : ℝ) ≤ |x| := le_of_lt (lt_of_not_ge hx)
      rw [hηsup x hx']
      exact le_trans (by simp : ‖(0 : ℂ)‖ ≤ 1) (le_max_right _ _)
  have hcd0 : ContDiff ℝ 2 (Work.BourgainPlan.Thm52.circleLift (mstEta P.natDegree χ η 0)) := by
    rw [circleLift_mstEta_zero_eq_neg hηsup]
    exact hηc.comp contDiff_neg
  -- ## 2. the pointwise symbol estimate
  obtain ⟨Cpt, hCptpos, sP, hpt⟩ :=
    mstNuS_sub_mstWideModel_pointwise P hd hc l hl hχ0 hχ1 η hηc hηsup hδ D hD hGauss
  -- ## 3. the coefficient-kernel bound
  obtain ⟨Kc, hKcpos, hcoeffN⟩ : ∃ K : ℝ, 0 < K ∧ ∀ N s : ℕ, 1 ≤ N →
      Summable (fun m : ℤ => ‖∫ ξ : Circ,
          (star (mstProf P N ξ) * (mstEta P.natDegree χ η s ξ - Work.Maximal.mstWideBump P χ η s ξ))
            * star (fourier m ξ) ∂haarT‖)
      ∧ (∑' m : ℤ, ‖∫ ξ : Circ,
          (star (mstProf P N ξ) * (mstEta P.natDegree χ η s ξ - Work.Maximal.mstWideBump P χ η s ξ))
            * star (fourier m ξ) ∂haarT‖) ≤ K := by
    exact mstNuS_sub_mstWideModel_coeff P P.natDegree χ η Mb hMbpos hχd hηbd hη2 hcd0
  have hcoeff : ∀ k s : ℕ, Summable (fun m : ℤ => ‖∫ ξ : Circ,
          (star (mstProf P (2 ^ k) ξ)
            * (mstEta P.natDegree χ η s ξ - Work.Maximal.mstWideBump P χ η s ξ))
            * star (fourier m ξ) ∂haarT‖)
      ∧ (∑' m : ℤ, ‖∫ ξ : Circ,
          (star (mstProf P (2 ^ k) ξ)
            * (mstEta P.natDegree χ η s ξ - Work.Maximal.mstWideBump P χ η s ξ))
            * star (fourier m ξ) ∂haarT‖) ≤ Kc :=
    fun k s => hcoeffN (2 ^ k) s (Nat.one_le_two_pow)
  -- ## 4. the two exponents
  set q : ℝ := (1 + r) / 2 with hqdef
  have hq1 : 1 < q := by rw [hqdef]; linarith
  have hqr : q < r := by rw [hqdef]; linarith
  set θ : ℝ := (1 / q - 1 / r) / (1 / q - 1 / 2) with hθdef
  have hθpos : 0 < θ := by
    rw [hθdef]
    have h1 : (1 : ℝ) / r < 1 / q :=
      one_div_lt_one_div_of_lt (by linarith : (0 : ℝ) < q) hqr
    exact div_pos (by linarith) (by
      have h2 : (1 : ℝ) / 2 < 1 / q :=
        one_div_lt_one_div_of_lt (by linarith : (0 : ℝ) < q) (by linarith : q < 2)
      linarith)
  have hθlt : θ < 1 := by
    rw [hθdef, div_lt_one (by
      have h2 : (1 : ℝ) / 2 < 1 / q :=
        one_div_lt_one_div_of_lt (by linarith : (0 : ℝ) < q) (by linarith : q < 2)
      linarith)]
    have h : (1 : ℝ) / 2 < 1 / r := one_div_lt_one_div_of_lt (by linarith : (0 : ℝ) < r) hr2
    linarith
  -- ## 5. the trivial `ℓ^q` bound for the difference
  obtain ⟨Atriv, hApos, htriv⟩ : ∃ A : ℝ, 0 < A ∧ ∀ s : ℕ, 1 ≤ s → ∀ k : ℕ, ∀ g : ℤ →₀ ℂ,
      MeasureTheory.eLpNorm (fun m : ℤ => ‖Work.BourgainPlan.IonescuWainger.opMul
          (Work.BourgainPlan.Maximal.mstNuSCls P l P.natDegree χ η k s (hνsml k s))
          (⇑g) (Work.BourgainPlan.IonescuWainger.memℓp_finsupp g) m
        - Work.BourgainPlan.IonescuWainger.opMul
          ((hΩml k s).toLp (Work.Maximal.mstWideModel P l χ η k s))
          (⇑g) (Work.BourgainPlan.IonescuWainger.memℓp_finsupp g) m‖ₑ)
        (ENNReal.ofReal q) MeasureTheory.Measure.count
      ≤ ENNReal.ofReal (A * ((s : ℝ) + 1) ^ (-(δ * l)) * ((mstAnnulus l s).card : ℝ))
        * MeasureTheory.eLpNorm (⇑g) (ENNReal.ofReal q) MeasureTheory.Measure.count := by
    exact mstNuS_sub_mstWideModel_triv_lp P hd hc l hl hχ0 hχ1 η hηc hηsup hδ D hD hGauss
      hνsml hΩml hKcpos hcoeff hq1.le
  -- ## 6. the cardinality bound
  obtain ⟨Cc, hCcpos, hCcb⟩ := mstU_card_le_exp l hl
  have hcard : ∀ s : ℕ, ((mstAnnulus l s).card : ℝ)
      ≤ Cc * Real.exp (((s : ℝ) + 1) ^ (1 / 10 : ℝ)) := by
    intro s
    have hsub : mstAnnulus l s ⊆ mstU l (s + 1) := by
      intro β hβ
      have hβ' : β ∈ mstLevel l (s + 1) \ mstLevel l s := hβ
      rw [mstLevel_succ] at hβ'
      exact (Finset.mem_sdiff.mp hβ').1
    have h1 : ((mstAnnulus l s).card : ℝ) ≤ ((mstU l (s + 1)).card : ℝ) := by
      exact_mod_cast Finset.card_le_card hsub
    have h2 := hCcb (s + 1)
    have h3 : ((((s + 1 : ℕ) : ℝ) ^ l) ^ mstRho l) = ((s : ℝ) + 1) ^ (1 / 10 : ℝ) := by
      have hx : (0 : ℝ) ≤ ((s : ℝ) + 1) := by positivity
      have hl0 : (l : ℝ) ≠ 0 := by exact_mod_cast (by omega : l ≠ 0)
      rw [mstRho,
        show (((s + 1 : ℕ) : ℝ)) = (s : ℝ) + 1 by push_cast; ring,
        show ((s : ℝ) + 1) ^ l = ((s : ℝ) + 1) ^ ((l : ℝ)) from
          (Real.rpow_natCast ((s : ℝ) + 1) l).symm,
        ← Real.rpow_mul hx (l : ℝ) (1 / (10 * (l : ℝ)))]
      congr 1
      field_simp
    rw [h3] at h2
    exact le_trans h1 h2
  -- ## 7. the tail arithmetic
  obtain ⟨sA, hsA⟩ : ∃ s₀ : ℕ, ∀ s : ℕ, s₀ ≤ s →
      Summable (fun j : ℕ =>
        (Atriv * ((s : ℝ) + 1) ^ (-(δ * l)) * ((mstAnnulus l s).card : ℝ)) ^ (1 - θ)
          * (Cpt * (D * ((s : ℝ) + 1) ^ (-(δ * l)))
              * (2 : ℝ) ^ (-((((2 ^ mstKappa P s : ℕ) : ℝ) + (j : ℝ))
                  / (2 * (P.natDegree : ℝ))))) ^ θ)
      ∧ (∑' j : ℕ,
        (Atriv * ((s : ℝ) + 1) ^ (-(δ * l)) * ((mstAnnulus l s).card : ℝ)) ^ (1 - θ)
          * (Cpt * (D * ((s : ℝ) + 1) ^ (-(δ * l)))
              * (2 : ℝ) ^ (-((((2 ^ mstKappa P s : ℕ) : ℝ) + (j : ℝ))
                  / (2 * (P.natDegree : ℝ))))) ^ θ) ≤ 1 := by
    exact mstNuS_sub_mstWideModel_tail_arith P hd l hl hApos hCptpos hCcpos hD hδ hcard
      hq1 hqr hr2 hθpos hθlt
  -- ## 8. the main bound
  refine ⟨1, one_pos, max (max sP sA) 1, fun s hs g => ?_⟩
  have hsP : sP ≤ s := le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) hs
  have hsA' : sA ≤ s := le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) hs
  have hs1 : 1 ≤ s := le_trans (le_max_right _ _) hs
  obtain ⟨hsumm0, hbound0⟩ := hsA s hsA'
  by_cases hcard0 : (mstAnnulus l s).card = 0
  · -- the annulus is empty: both operators vanish
    have hE : mstAnnulus l s = ∅ := Finset.card_eq_zero.mp hcard0
    have hE' : mstLevel l (s + 1) \ mstLevel l s = ∅ := hE
    have hcls0 : ∀ k : ℕ, mstNuSCls P l P.natDegree χ η k s (hνsml k s) = 0 := by
      intro k
      refine Lp.ext ?_
      filter_upwards [mstNuSCls_coeFn P l P.natDegree χ η k s (hνsml k s)] with ξ hξ
      rw [hξ]
      have hnu : mstNuS P l P.natDegree χ η k s ξ = 0 := by
        rw [mstNuS_apply, hE', Finset.sum_empty]
      rw [hnu]
      simp
    have hcls0w : ∀ k : ℕ, (hΩml k s).toLp (mstWideModel P l χ η k s) = 0 := by
      intro k
      refine Lp.ext ?_
      filter_upwards [MemLp.coeFn_toLp (hΩml k s)] with ξ hξ
      rw [hξ]
      have hw : mstWideModel P l χ η k s ξ = 0 := by
        rw [mstWideModel_apply, hE, Finset.sum_empty]
      rw [hw]
      simp
    have hfun0 : (fun m : ℤ => (⨆ k : ℕ, ⨆ (_ : 2 ^ mstKappa P s ≤ k),
        ‖opMul (mstNuSCls P l P.natDegree χ η k s (hνsml k s)) (⇑g) (memℓp_finsupp g) m
          - opMul ((hΩml k s).toLp (mstWideModel P l χ η k s))
              (⇑g) (memℓp_finsupp g) m‖ₑ)) = fun _ : ℤ => 0 := by
      funext m
      simp only [hcls0, hcls0w]
      simp [opMul, opMulLp]
    rw [hfun0]
    simp
  · -- the annulus is nonempty
    have hcardpos : 0 < ((mstAnnulus l s).card : ℝ) :=
      Nat.cast_pos.mpr (Nat.pos_of_ne_zero hcard0)
    set As : ℝ := Atriv * ((s : ℝ) + 1) ^ (-(δ * l)) * ((mstAnnulus l s).card : ℝ) with hAsdef
    have hAspos : 0 < As := by
      rw [hAsdef]
      exact mul_pos (mul_pos hApos (Real.rpow_pos_of_pos (by positivity) _)) hcardpos
    set Mexp : ℕ → ℝ := (fun j : ℕ => As ^ (1 - θ)
        * (Cpt * (D * ((s : ℝ) + 1) ^ (-(δ * l)))
            * (2 : ℝ) ^ (-((((2 ^ mstKappa P s + j : ℕ)) : ℝ) / (2 * (P.natDegree : ℝ))))) ^ θ)
      with hMexpdef
    have hMexp_eq : ∀ j : ℕ, Mexp j
        = (Atriv * ((s : ℝ) + 1) ^ (-(δ * l)) * ((mstAnnulus l s).card : ℝ)) ^ (1 - θ)
          * (Cpt * (D * ((s : ℝ) + 1) ^ (-(δ * l)))
              * (2 : ℝ) ^ (-((((2 ^ mstKappa P s : ℕ) : ℝ) + (j : ℝ))
                  / (2 * (P.natDegree : ℝ))))) ^ θ := by
      intro j
      simp only [hMexpdef, hAsdef, Nat.cast_add]
    have hMnn : ∀ j : ℕ, 0 ≤ Mexp j := by
      intro j
      rw [hMexpdef]
      refine mul_nonneg (Real.rpow_nonneg hAspos.le _) (Real.rpow_nonneg ?_ _)
      positivity
    have hsummM : Summable Mexp := hsumm0.congr (fun j => (hMexp_eq j).symm)
    have hboundM : (∑' j : ℕ, Mexp j) ≤ 1 := by
      rw [tsum_congr (fun j => hMexp_eq j)]
      exact hbound0
    have hper : ∀ k : ℕ, 2 ^ mstKappa P s ≤ k →
        MeasureTheory.eLpNorm (fun m : ℤ => opMul (mstNuSCls P l P.natDegree χ η k s (hνsml k s))
              (⇑g) (memℓp_finsupp g) m
            - opMul ((hΩml k s).toLp (mstWideModel P l χ η k s)) (⇑g) (memℓp_finsupp g) m)
          (ENNReal.ofReal r) MeasureTheory.Measure.count
        ≤ ENNReal.ofReal (As ^ (1 - θ)
            * (Cpt * (D * ((s : ℝ) + 1) ^ (-(δ * l)))
                * (2 : ℝ) ^ (-((k : ℝ) / (2 * (P.natDegree : ℝ))))) ^ θ)
          * MeasureTheory.eLpNorm (⇑g) (ENNReal.ofReal r) MeasureTheory.Measure.count := by
      intro k hk
      have hεnn : 0 ≤ Cpt * (D * ((s : ℝ) + 1) ^ (-(δ * l)))
          * (2 : ℝ) ^ (-((k : ℝ) / (2 * (P.natDegree : ℝ)))) := by positivity
      have hsymb : ∀ᵐ ξ ∂haarT, ‖((mstNuSCls P l P.natDegree χ η k s (hνsml k s)
            - (hΩml k s).toLp (mstWideModel P l χ η k s) : Lp ℂ ⊤ haarT) : Circ → ℂ) ξ‖
          ≤ Cpt * (D * ((s : ℝ) + 1) ^ (-(δ * l)))
              * (2 : ℝ) ^ (-((k : ℝ) / (2 * (P.natDegree : ℝ)))) := by
        filter_upwards [Lp.coeFn_sub (mstNuSCls P l P.natDegree χ η k s (hνsml k s))
              ((hΩml k s).toLp (mstWideModel P l χ η k s)),
            mstNuSCls_coeFn P l P.natDegree χ η k s (hνsml k s),
            MemLp.coeFn_toLp (hΩml k s)] with ξ h1 h2 h3
        rw [h1, Pi.sub_apply, h2, h3]
        exact hpt s hsP k hk ξ
      have h2g : ∀ f : ℤ →₀ ℂ, MeasureTheory.eLpNorm ((opMulFinsuppLM (mstNuSCls P l P.natDegree χ η k s
            (hνsml k s) - (hΩml k s).toLp (mstWideModel P l χ η k s))) f)
          (ENNReal.ofReal 2) MeasureTheory.Measure.count
          ≤ ENNReal.ofReal (Cpt * (D * ((s : ℝ) + 1) ^ (-(δ * l)))
              * (2 : ℝ) ^ (-((k : ℝ) / (2 * (P.natDegree : ℝ)))))
            * MeasureTheory.eLpNorm (⇑f) (ENNReal.ofReal 2) MeasureTheory.Measure.count := by
        intro f
        rw [opMulFinsuppLM_apply]
        exact eLpNorm_two_opMul_le (memℓp_finsupp f) hεnn hsymb
      have hqg : ∀ f : ℤ →₀ ℂ, MeasureTheory.eLpNorm ((opMulFinsuppLM (mstNuSCls P l P.natDegree χ η k s
            (hνsml k s) - (hΩml k s).toLp (mstWideModel P l χ η k s))) f)
          (ENNReal.ofReal q) MeasureTheory.Measure.count
          ≤ ENNReal.ofReal As * MeasureTheory.eLpNorm (⇑f) (ENNReal.ofReal q) MeasureTheory.Measure.count := by
        intro f
        have h' := htriv s hs1 k f
        rw [opMulFinsuppLM_apply, ← opMul_sub, ← eLpNorm_enorm _ (measurable_of_countable _).aestronglyMeasurable, hAsdef]
        exact h'
      have hrg := opMulFinsuppLM_interp (mstNuSCls P l P.natDegree χ η k s (hνsml k s)
            - (hΩml k s).toLp (mstWideModel P l χ η k s)) (r := q) (p := r) (A := As)
        (B := Cpt * (D * ((s : ℝ) + 1) ^ (-(δ * l)))
            * (2 : ℝ) ^ (-((k : ℝ) / (2 * (P.natDegree : ℝ)))))
        hq1 hqr hr2 hAspos (by positivity) hqg h2g g
      have hkey : As ^ (1 - (1 / q - 1 / r) / (1 / q - 1 / 2))
            * (Cpt * (D * ((s : ℝ) + 1) ^ (-(δ * l)))
                * (2 : ℝ) ^ (-((k : ℝ) / (2 * (P.natDegree : ℝ)))))
              ^ ((1 / q - 1 / r) / (1 / q - 1 / 2))
          = As ^ (1 - θ) * (Cpt * (D * ((s : ℝ) + 1) ^ (-(δ * l)))
              * (2 : ℝ) ^ (-((k : ℝ) / (2 * (P.natDegree : ℝ))))) ^ θ := by
        rw [hθdef]
      have hTk : (opMulFinsuppLM (mstNuSCls P l P.natDegree χ η k s (hνsml k s)
            - (hΩml k s).toLp (mstWideModel P l χ η k s))) g
          = fun m : ℤ => opMul (mstNuSCls P l P.natDegree χ η k s (hνsml k s))
                (⇑g) (memℓp_finsupp g) m
              - opMul ((hΩml k s).toLp (mstWideModel P l χ η k s)) (⇑g) (memℓp_finsupp g) m := by
        rw [opMulFinsuppLM_apply, ← opMul_sub]
        funext m
        rfl
      rw [hkey, hTk] at hrg
      exact hrg
    have hperj : ∀ j : ℕ,
        MeasureTheory.eLpNorm (fun m : ℤ =>
            opMul (mstNuSCls P l P.natDegree χ η (2 ^ mstKappa P s + j) s
                (hνsml (2 ^ mstKappa P s + j) s)) (⇑g) (memℓp_finsupp g) m
              - opMul ((hΩml (2 ^ mstKappa P s + j) s).toLp
                  (mstWideModel P l χ η (2 ^ mstKappa P s + j) s)) (⇑g) (memℓp_finsupp g) m)
          (ENNReal.ofReal r) MeasureTheory.Measure.count
        ≤ ENNReal.ofReal (Mexp j)
          * MeasureTheory.eLpNorm (⇑g) (ENNReal.ofReal r) MeasureTheory.Measure.count := by
      intro j
      have h' := hper (2 ^ mstKappa P s + j) (Nat.le_add_right _ _)
      simpa only [hMexpdef] using h'
    have hfin := tail_sup_le_of_per_k (2 ^ mstKappa P s)
      (fun k m => opMul (mstNuSCls P l P.natDegree χ η k s (hνsml k s))
          (⇑g) (memℓp_finsupp g) m
        - opMul ((hΩml k s).toLp (mstWideModel P l χ η k s)) (⇑g) (memℓp_finsupp g) m)
      (⇑g) Mexp hr.le hperj hMnn hsummM hboundM
    exact le_trans hfin (le_of_eq (by rw [ENNReal.ofReal_one, one_mul]))

end

end Work.Maximal
