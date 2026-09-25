import Mathlib
import Submission.Work.BourgainPlan.Maximal.mst_major_defs
import Submission.Work.BourgainPlan.Maximal.level_l2_mst_small_n
import Submission.Work.BourgainPlan.Maximal.level_l2_mst_large_n
import Submission.Work.BourgainPlan.Maximal.mstG_gauss_uniform
import Submission.Work.BourgainPlan.Maximal.mstFreeze
import Submission.Work.BourgainPlan.Maximal.mstFreezeDefs
import Submission.Work.BourgainPlan.Maximal.mstSumResidue
import Submission.Work.BourgainPlan.Maximal.level_l2_mst_large_n_aux_defs
import Submission.Work.BourgainPlan.Maximal.mstMaximal_single
import Submission.Work.BourgainPlan.Maximal.mstMaximal_all
import Submission.Work.BourgainPlan.Maximal.mstOrthogonality
import Submission.Work.BourgainPlan.Maximal.mstG_spec
import Submission.Work.BourgainPlan.Maximal.mstEta_arcSum_le
import Submission.Work.BourgainPlan.Maximal.mst_level_defs
import Submission.Work.BourgainPlan.Maximal.memLp_mst_symbols
import Submission.Work.BourgainPlan.Maximal.mstModelFn_modSeq
import Submission.Work.BourgainPlan.Maximal.neg_mstU
import Submission.Work.BourgainPlan.Maximal.mstG_neg
import Submission.Work.BourgainPlan.Maximal.mstProf_neg_ae
import Submission.Work.BourgainPlan.Maximal.mstEta_neg_ae
import Submission.Work.BourgainPlan.Maximal.mstFreeze_diff_eq
import Submission.Work.BourgainPlan.IonescuWainger.opArc_strata_incl_excl

set_option maxHeartbeats 400000000
set_option linter.unusedVariables false

namespace Work.BourgainPlan.Maximal

open MeasureTheory Finset
open scoped BigOperators ENNReal

open Work.BourgainPlan.IonescuWainger

noncomputable section

local notation "Circ" => Work.BourgainPlan.IonescuWainger.Circle
local notation "haarT" => (AddCircle.haarAddCircle (T := 1))

/-! ## 0. The coefficient kernel of a multiplier symbol -/

/-- The coefficient kernel `K m = ∫ ξ, Φ ξ · star (fourier m ξ)` of an `L^∞(𝕋)`-class. -/
noncomputable def mulKernel (Φ : Lp ℂ ⊤ haarT) : ℤ → ℂ :=
  fun m => ∫ ξ : Circ, (Φ : Circ → ℂ) ξ * star (fourier m ξ) ∂haarT

@[simp] lemma mulKernel_apply (Φ : Lp ℂ ⊤ haarT) (m : ℤ) :
    mulKernel Φ m = ∫ ξ : Circ, (Φ : Circ → ℂ) ξ * star (fourier m ξ) ∂haarT := rfl

/-! ## 1. The general arc-sum identity -/

private lemma toLp_mul_fourier_integral' {F : Circ → ℂ} (hF : MemLp F ⊤ haarT) (m : ℤ) :
    ∫ ξ : Circ, (hF.toLp F : Circ → ℂ) ξ * star (fourier m ξ) ∂haarT
      = ∫ ξ : Circ, F ξ * star (fourier m ξ) ∂haarT := by
  refine integral_congr_ae ?_
  filter_upwards [hF.coeFn_toLp] with ξ hξ
  rw [hξ]

private lemma integral_mstModelFn_mul_fourier' {Φ ψ : Circ → ℂ}
    (hφ : MemLp (fun y : Circ => Φ y * ψ y) ⊤ haarT)
    (G : Circ → ℂ) (E : Finset Circ) (m : ℤ) :
    ∫ ξ : Circ, mstModelFn G Φ ψ E ξ * star (fourier m ξ) ∂haarT
      = (∑ β ∈ E, G β * star (fourier m β))
          * (∫ ξ : Circ, (Φ ξ * ψ ξ) * star (fourier m ξ) ∂haarT) := by
  have hchar : MemLp (fun ξ : Circ => star (fourier m ξ)) ⊤ haarT :=
    memLp_top_of_bound ((continuous_star.comp (map_continuous (fourier m))).aestronglyMeasurable) 1
      (Filter.Eventually.of_forall fun ξ => by rw [norm_star, norm_fourier_apply'])
  have hInt : ∀ β ∈ E, Integrable (fun ξ : Circ =>
      G β * (arcTranslate β (fun y : Circ => Φ y * ψ y) ξ * star (fourier m ξ))) haarT := by
    intro β _
    have h1 : MemLp (arcTranslate β (fun y : Circ => Φ y * ψ y)) ⊤ haarT := memLp_arcTranslate hφ β
    have haesm : AEStronglyMeasurable
        (fun ξ : Circ => arcTranslate β (fun y : Circ => Φ y * ψ y) ξ * star (fourier m ξ)) haarT :=
      h1.aestronglyMeasurable.mul hchar.aestronglyMeasurable
    have hle : ∀ᵐ ξ ∂haarT,
        ‖arcTranslate β (fun y : Circ => Φ y * ψ y) ξ * star (fourier m ξ)‖
          ≤ ‖arcTranslate β (fun y : Circ => Φ y * ψ y) ξ‖ :=
      Filter.Eventually.of_forall fun ξ => by rw [norm_mul, norm_star, norm_fourier_apply', mul_one]
    exact ((h1.of_le haesm hle).const_mul (G β)).integrable le_top
  have hpt : ∀ ξ : Circ, mstModelFn G Φ ψ E ξ * star (fourier m ξ)
      = ∑ β ∈ E, G β * (arcTranslate β (fun y : Circ => Φ y * ψ y) ξ * star (fourier m ξ)) := by
    intro ξ
    rw [mstModelFn_apply, Finset.sum_mul]
    refine Finset.sum_congr rfl fun β _ => ?_
    simp only [arcTranslate_apply]
    ring
  rw [show (fun ξ : Circ => mstModelFn G Φ ψ E ξ * star (fourier m ξ))
      = (fun ξ : Circ => ∑ β ∈ E,
          G β * (arcTranslate β (fun y : Circ => Φ y * ψ y) ξ * star (fourier m ξ)))
      from funext hpt,
    integral_finsetSum E hInt, Finset.sum_mul]
  refine Finset.sum_congr rfl fun β _ => ?_
  rw [integral_const_mul, fourierCoeff_arcTranslate (fun y : Circ => Φ y * ψ y) hφ β m]
  ring

/-- **The general arc-sum identity.** -/
theorem mstModelFn_modSeq_gen (G Φ ψ : Circ → ℂ) (E : Finset Circ)
    (hφ : MemLp (fun y : Circ => Φ y * ψ y) ⊤ haarT)
    (hA : MemLp (mstModelFn G Φ ψ E) ⊤ haarT)
    (f : ℤ → ℂ) (hf : Memℓp f 2) (y : ℤ) :
    opMul (MemLp.toLp (mstModelFn G Φ ψ E) hA) f hf y
      = opMul (MemLp.toLp (fun ζ : Circ => Φ ζ * ψ ζ) hφ)
          (mstModSeq G E f y) (memℒp_mstModSeq hf y) y := by
  classical
  have hkerA : ∀ m : ℤ,
      mulKernel (MemLp.toLp (mstModelFn G Φ ψ E) hA) m
        = (∑ β ∈ E, G β * star (fourier m β))
            * (∫ ξ : Circ, (Φ ξ * ψ ξ) * star (fourier m ξ) ∂haarT) := by
    intro m
    rw [mulKernel_apply, toLp_mul_fourier_integral' hA m, integral_mstModelFn_mul_fourier' hφ G E m]
  rw [opMul_eq_tsum_kernel (MemLp.toLp (mstModelFn G Φ ψ E) hA) f hf hkerA y,
      opMul_eq_tsum_kernel (MemLp.toLp (fun ζ : Circ => Φ ζ * ψ ζ) hφ)
        (mstModSeq G E f y) (memℒp_mstModSeq hf y)
        (fun m => toLp_mul_fourier_integral' hφ m) y]
  refine tsum_congr fun k => ?_
  have hβ : ∀ β : Circ, star (fourier (y - k) β) = fourier (k - y) β := by
    intro β
    rw [show star (fourier (y - k) β) = fourier (-(y - k)) β from
      (fourier_neg (n := y - k) (x := β)).symm]
    congr 1
    ring
  have hsumeq : (∑ β ∈ E, G β * star (fourier (y - k) β))
      = (∑ β ∈ E, G β * fourier (k - y) β) :=
    Finset.sum_congr rfl fun β _ => by rw [hβ β]
  rw [mstModSeq_apply, mstArc_apply, hsumeq]
  ring

/-! ## 2. Star of the arc comb, and the conjugation of `mstModSeq` -/

lemma star_mstArc (G : Circ → ℂ) (E : Finset Circ) (t : ℤ) :
    star (mstArc (fun β => star (G β)) E t) = mstArc G E (-t) := by
  rw [mstArc_apply, mstArc_apply, star_sum]
  refine Finset.sum_congr rfl fun β _ => ?_
  rw [star_mul, star_star,
    show star (fourier t β) = fourier (-t) β from (fourier_neg (n := t) (x := β)).symm,
    mul_comm]

lemma star_mstModSeq_neg (G : Circ → ℂ) (E : Finset Circ) (f : ℤ → ℂ) (m : ℤ) :
    (fun k : ℤ => star (mstModSeq (fun β => star (G β)) E f m (-k)))
      = mstModSeq G E (fun k : ℤ => star (f (-k))) (-m) := by
  funext k
  show star (mstArc (fun β => star (G β)) E (-k - m) * f (-k))
      = mstArc G E (k - -m) * star (f (-k))
  rw [star_mul, star_mstArc, mul_comm]
  congr 1
  ring

/-! ## 3. The conjugation identity for `opMul` -/

/-- **Conjugation of a multiplier.** -/
theorem opMul_star_conj (X Xs : Lp ℂ ⊤ haarT)
    (hXs : (Xs : Circ → ℂ) =ᵐ[haarT] fun ξ => star ((X : Circ → ℂ) ξ))
    (w : ℤ → ℂ) (hw : Memℓp w 2) (hw2 : Memℓp (fun k : ℤ => star (w (-k))) 2) (n : ℤ) :
    opMul Xs w hw n = star (opMul X (fun k : ℤ => star (w (-k))) hw2 (-n)) := by
  classical
  have hkerXs : ∀ m : ℤ, mulKernel Xs m = star (mulKernel X (-m)) := by
    intro m
    have h1 : mulKernel Xs m
        = ∫ ξ : Circ, star ((X : Circ → ℂ) ξ * fourier m ξ) ∂haarT := by
      rw [mulKernel_apply]
      refine integral_congr_ae ?_
      filter_upwards [hXs] with ξ hξ
      rw [hξ, star_mul, mul_comm]
    rw [h1, mulKernel_apply]
    rw [show (∫ ξ : Circ, star ((X : Circ → ℂ) ξ * fourier m ξ) ∂haarT)
        = star (∫ ξ : Circ, (X : Circ → ℂ) ξ * fourier m ξ ∂haarT) from integral_conj]
    congr 1
    rw [show (fun ξ : Circ => (X : Circ → ℂ) ξ * fourier m ξ)
        = fun ξ : Circ => (X : Circ → ℂ) ξ * star (fourier (-m) ξ) from by
      funext ξ
      have hf : fourier m ξ = star (fourier (-m) ξ) := by
        simpa using fourier_neg (n := -m) (x := ξ)
      rw [hf]]
  rw [opMul_eq_tsum_kernel (K := mulKernel Xs) Xs w hw (fun m => (mulKernel_apply Xs m).symm) n,
      opMul_eq_tsum_kernel (K := mulKernel X) X (fun k : ℤ => star (w (-k))) hw2
        (fun m => (mulKernel_apply X m).symm) (-n)]
  simp only [hkerXs]
  rw [tsum_star]
  have hR : (∑' b : ℤ, star (star (w (-b)) * mulKernel X (-n - b)))
      = ∑' b : ℤ, w (-b) * star (mulKernel X (-n - b)) :=
    tsum_congr fun b => by rw [star_mul, star_star, mul_comm]
  rw [hR]
  have hre : (∑' k : ℤ, w k * star (mulKernel X (-(n - k))))
      = ∑' k : ℤ, w (-k) * star (mulKernel X (-n - k)) := by
    rw [show (∑' k : ℤ, w k * star (mulKernel X (-(n - k))))
        = ∑' k : ℤ, (fun j : ℤ => w (-j) * star (mulKernel X (-n - j))) (-k) from
      tsum_congr fun k => by simp only [neg_neg]; congr 2; ring]
    exact Equiv.tsum_eq (Equiv.neg ℤ) (fun j : ℤ => w (-j) * star (mulKernel X (-n - j)))
  rw [hre]

/-! ## 3b. Reflection of a multiplier symbol -/

/-- **Reflection of a multiplier symbol.**  If `Xn` is the class of the reflected symbol
`ξ ↦ X (-ξ)`, then the multiplier with symbol `Xn` applied to `w` is (up to the reflection of the
index) the multiplier with symbol `X` applied to the reflected sequence `k ↦ w (-k)`.  (Kernel
computation: the kernel of the reflected symbol is `m ↦ K (-m)`.) -/
theorem opMul_negFun (X Xn : Lp ℂ ⊤ haarT)
    (hXn : (Xn : Circ → ℂ) =ᵐ[haarT] fun ξ => (X : Circ → ℂ) (-ξ))
    (w : ℤ → ℂ) (hw : Memℓp w 2) (hw2 : Memℓp (fun k : ℤ => w (-k)) 2) (n : ℤ) :
    opMul Xn w hw n = opMul X (fun k : ℤ => w (-k)) hw2 (-n) := by
  classical
  have hstar_fourier : ∀ (m : ℤ) (ξ : Circ), star (fourier m (-ξ)) = fourier m ξ := by
    intro m ξ
    have h := fourier_neg (n := m) (x := -ξ)
    rw [Complex.star_def]
    rw [← h]
    rw [fourier_apply, fourier_apply, neg_smul_neg]
  have hkerXn : ∀ m : ℤ, mulKernel Xn m = mulKernel X (-m) := by
    intro m
    have h1 : mulKernel Xn m
        = ∫ ξ : Circ, (X : Circ → ℂ) ξ * star (fourier m (-ξ)) ∂haarT := by
      rw [mulKernel_apply]
      have ha : ∫ ξ : Circ, (Xn : Circ → ℂ) ξ * star (fourier m ξ) ∂haarT
          = ∫ ξ : Circ, (X : Circ → ℂ) (-ξ) * star (fourier m ξ) ∂haarT := by
        refine integral_congr_ae ?_
        filter_upwards [hXn] with ξ hξ
        rw [hξ]
      rw [ha]
      simpa only [neg_neg] using integral_neg_eq_self
        (fun ζ : Circ => (X : Circ → ℂ) ζ * star (fourier m (-ζ))) haarT
    rw [h1, mulKernel_apply]
    refine integral_congr_ae ?_
    filter_upwards with ξ
    have hf2 : star (fourier (-m) ξ) = fourier m ξ := by
      have h := fourier_neg (n := m) (x := ξ)
      rw [Complex.star_def]
      rw [h]
      simp
    rw [hstar_fourier m ξ, hf2]
  rw [opMul_eq_tsum_kernel (K := mulKernel Xn) Xn w hw (fun m => (mulKernel_apply Xn m).symm) n,
      opMul_eq_tsum_kernel (K := mulKernel X) X (fun k : ℤ => w (-k)) hw2
        (fun m => (mulKernel_apply X m).symm) (-n)]
  simp only [hkerXn]
  have hre : (∑' k : ℤ, w (-k) * mulKernel X (-n - k))
      = ∑' k : ℤ, w k * mulKernel X (-(n - k)) := by
    rw [show (∑' k : ℤ, w (-k) * mulKernel X (-n - k))
        = ∑' k : ℤ, (fun j : ℤ => w j * mulKernel X (-(n - j))) (-k) from by
      refine tsum_congr fun k => ?_
      simp only [neg_neg]
      congr 2
      ring]
    exact Equiv.tsum_eq (Equiv.neg ℤ) (fun j : ℤ => w j * mulKernel X (-(n - j)))
  rw [hre]

/-! ## 4. The reflected sequence, and the transfer to the unconjugated model -/

/-- `negSeq g = k ↦ g (-k)`. -/
abbrev negSeq (g : ℤ → ℂ) : ℤ → ℂ := fun k => g (-k)

lemma memℓp_negSeq {g : ℤ → ℂ} (hg : Memℓp g 2) : Memℓp (negSeq g) 2 := by
  rw [memℓp_gen_iff (p := (2 : ℝ≥0∞)) (by norm_num : (0 : ℝ) < (2 : ℝ≥0∞).toReal),
    show (2 : ℝ≥0∞).toReal = 2 from by norm_num]
  have h := (memℓp_gen_iff (p := (2 : ℝ≥0∞)) (by norm_num : (0 : ℝ) < (2 : ℝ≥0∞).toReal)).mp hg
  rw [show (2 : ℝ≥0∞).toReal = 2 from by norm_num] at h
  have hfun : (fun k : ℤ => ‖negSeq g k‖ ^ (2 : ℝ)) = fun k : ℤ => ‖g (-k)‖ ^ (2 : ℝ) := by
    funext k; simp [negSeq]
  rw [hfun]
  exact h.comp_injective neg_injective

lemma lintegral_neg_enorm (F : ℤ → ℝ≥0∞) (q : ℝ) :
    ∫⁻ n : ℤ, ‖F (-n)‖ₑ ^ q ∂MeasureTheory.Measure.count
      = ∫⁻ n : ℤ, ‖F n‖ₑ ^ q ∂MeasureTheory.Measure.count := by
  rw [MeasureTheory.lintegral_count, MeasureTheory.lintegral_count]
  exact Equiv.tsum_eq (Equiv.neg ℤ) (fun n : ℤ => ‖F n‖ₑ ^ q)

lemma eLpNorm_neg_enorm (F : ℤ → ℝ≥0∞) :
    eLpNorm (fun n : ℤ => F (-n)) (ENNReal.ofReal 2) MeasureTheory.Measure.count
      = eLpNorm F (ENNReal.ofReal 2) MeasureTheory.Measure.count := by
  rw [MeasureTheory.eLpNorm_eq_lintegral_rpow_enorm_toReal
      (ne_of_gt (ENNReal.ofReal_pos.mpr (by norm_num : (0:ℝ) < 2))) ENNReal.ofReal_ne_top
      AEStronglyMeasurable.of_discrete,
    MeasureTheory.eLpNorm_eq_lintegral_rpow_enorm_toReal
      (ne_of_gt (ENNReal.ofReal_pos.mpr (by norm_num : (0:ℝ) < 2))) ENNReal.ofReal_ne_top
      AEStronglyMeasurable.of_discrete]
  rw [ENNReal.toReal_ofReal (by norm_num : (0:ℝ) ≤ 2)]
  rw [lintegral_neg_enorm]

lemma eLpNorm_neg_cplx (v : ℤ → ℂ) :
    eLpNorm (fun n : ℤ => v (-n)) (ENNReal.ofReal 2) MeasureTheory.Measure.count
      = eLpNorm v (ENNReal.ofReal 2) MeasureTheory.Measure.count := by
  have h := eLpNorm_neg_enorm (fun n : ℤ => ‖v n‖ₑ)
  rwa [MeasureTheory.eLpNorm_enorm (fun n : ℤ => v (-n)) AEStronglyMeasurable.of_discrete,
    MeasureTheory.eLpNorm_enorm v AEStronglyMeasurable.of_discrete] at h

/-! ## 5. The symbolic identity: `mstNuS` is the reflection of the unconjugated model -/

/-- `mstLevel l s = mstU l s` for `s ≠ 0`. -/
lemma mstLevel_of_ne (l s : ℕ) (h : s ≠ 0) : mstLevel l s = mstU l s := by
  simp [mstLevel, h]

/-- The MST level annulus `mstLevel l (s+1) \ mstLevel l s` is closed under negation. -/
lemma neg_mem_mstLevel_sdiff (l s : ℕ) {x : Circ}
    (hx : x ∈ mstLevel l (s + 1) \ mstLevel l s) :
    -x ∈ mstLevel l (s + 1) \ mstLevel l s := by
  rw [Finset.mem_sdiff] at hx ⊢
  refine ⟨?_, ?_⟩
  · rw [mstLevel_succ] at hx ⊢
    exact (neg_mstU l (s + 1) x).mpr hx.1
  · rcases eq_or_ne s 0 with h | h
    · subst h
      rw [mstLevel_zero]
      simp
    · rw [mstLevel_of_ne l s h] at hx ⊢
      intro hmem
      exact hx.2 ((neg_mstU l s x).mp hmem)

/-- **`mstNuS` is the reflection of the unconjugated model with the reflected bump.**  For every
level `k`, `s`, the conjugated model symbol `mstNuS P l d χ η k s` equals the unconjugated model
symbol with weight `mstG P`, profile `mstProf P (2^k)` and the *reflected* bump
`ζ ↦ mstEta d χ η s (-ζ)`, evaluated at `-ξ`. -/
theorem mstNuS_neg_model (P : Polynomial ℤ) (l d : ℕ) (χ : ℝ) (η : ℝ → ℂ) (k s : ℕ) :
    mstNuS P l d χ η k s =ᵐ[haarT]
      fun ξ => mstModelFn (mstG P) (mstProf P (2 ^ k)) (mstEta d χ (fun x => η (-x)) s)
        (mstLevel l (s + 1) \ mstLevel l s) (-ξ) := by
  classical
  set E : Finset Circ := mstLevel l (s + 1) \ mstLevel l s with hE
  have hprof : ∀ᵐ ξ ∂haarT, ∀ γ ∈ E,
      mstProf P (2 ^ k) (-(ξ + γ)) = star (mstProf P (2 ^ k) (ξ + γ)) := by
    refine (Finset.eventually_all E).mpr fun γ _ => ?_
    exact (measurePreserving_add_right haarT γ).quasiMeasurePreserving.ae
      (mstProf_neg_ae P (2 ^ k))
  have heta : ∀ᵐ ξ ∂haarT, ∀ γ ∈ E,
      mstEta d χ (fun x => η (-x)) s (-(ξ + γ)) = mstEta d χ η s (ξ + γ) := by
    refine (Finset.eventually_all E).mpr fun γ _ => ?_
    have hcomp : MeasurePreserving (fun ξ : Circ => -(ξ + γ)) haarT haarT :=
      (Measure.measurePreserving_neg haarT).comp (measurePreserving_add_right haarT γ)
    simpa using hcomp.quasiMeasurePreserving.ae (mstEta_neg_ae d χ η s)
  filter_upwards [hprof, heta] with ξ hξprof hξη
  rw [mstNuS_apply, mstModelFn_apply]
  have hterm : ∀ γ ∈ E, mstG P γ * (mstProf P (2 ^ k) (-ξ - γ)
        * mstEta d χ (fun x => η (-x)) s (-ξ - γ))
      = mstG P γ * (star (mstProf P (2 ^ k) (ξ + γ)) * mstEta d χ η s (ξ + γ)) := by
    intro γ hγ
    rw [show -ξ - γ = -(ξ + γ) by abel, hξprof γ hγ, hξη γ hγ]
  rw [Finset.sum_congr rfl hterm]
  have himg : E.image (fun γ : Circ => -γ) = E := by
    refine Finset.Subset.antisymm ?_ ?_
    · intro x hx
      rw [Finset.mem_image] at hx
      obtain ⟨y, hy, rfl⟩ := hx
      exact neg_mem_mstLevel_sdiff l s hy
    · intro x hx
      rw [Finset.mem_image]
      exact ⟨-x, neg_mem_mstLevel_sdiff l s hx, neg_neg x⟩
  have hreindex : (∑ γ ∈ E, mstG P γ * (star (mstProf P (2 ^ k) (ξ + γ))
        * mstEta d χ η s (ξ + γ)))
      = ∑ β ∈ E, mstG P (-β) * (star (mstProf P (2 ^ k) (ξ - β))
          * mstEta d χ η s (ξ - β)) := by
    conv_lhs => rw [← himg]
    rw [Finset.sum_image (fun a _ b _ h => neg_injective h)]
    refine Finset.sum_congr rfl fun β _ => ?_
    have harg : ξ + -β = ξ - β := by abel
    rw [harg]
  rw [hreindex]
  refine Finset.sum_congr rfl fun β _ => ?_
  rw [mstG_neg]

/-- The `L^∞`-class of the level-`s` model symbol (the unconjugated model with weight `mstG P`,
profile `mstProf P (2^k)` and the level-`s` bump). -/
noncomputable def mstModelCls (P : Polynomial ℤ) (l d : ℕ) (χ : ℝ) (η : ℝ → ℂ) (s k : ℕ)
    (h : MemLp (mstModelFn (mstG P) (mstProf P (2 ^ k)) (mstEta d χ η s) (mstLvl l s))
      ⊤ haarT) : Lp ℂ ⊤ haarT :=
  h.toLp (mstModelFn (mstG P) (mstProf P (2 ^ k)) (mstEta d χ η s) (mstLvl l s))

/-- The level bump `mstEta d χ η s` is `L^∞`. -/
lemma memLp_mstEta_gen (d : ℕ) (χ : ℝ) (η : ℝ → ℂ) (hη : Continuous η) (s : ℕ) :
    MemLp (mstEta d χ η s) ⊤ haarT := by
  have h := (memLp_mst_symbols (0 : Polynomial ℤ) 0
    ((2 : ℝ) ^ ((s : ℝ) * ((d : ℝ) - χ))) η hη).2.2
  have hfun : (fun ξ : Circ => η ((2 : ℝ) ^ ((s : ℝ) * ((d : ℝ) - χ)) * iwRep ξ))
      = mstEta d χ η s := by
    funext ξ
    rw [mstEta]
  rwa [hfun] at h

/-- The product `Φ_{2^k}·ψ_s` is `L^∞` (with the bound `M` on the bump). -/
lemma memLp_mstProfBump (P : Polynomial ℤ) (d : ℕ) (χ : ℝ) (η : ℝ → ℂ) (hη : Continuous η)
    (s k : ℕ) {M : ℝ} (hM0 : 0 ≤ M) (hM : ∀ ζ : Circ, ‖mstEta d χ η s ζ‖ ≤ M) :
    MemLp (fun ζ : Circ => mstProf P (2 ^ k) ζ * mstEta d χ η s ζ) ⊤ haarT := by
  have hmemψ : MemLp (mstEta d χ η s) ⊤ haarT := memLp_mstEta_gen d χ η hη s
  have hmemΦ : MemLp (mstProf P (2 ^ k)) ⊤ haarT :=
    (memLp_mst_symbols P (2 ^ k) 1 η hη).2.1
  refine MemLp.of_bound (hmemΦ.aestronglyMeasurable.mul hmemψ.aestronglyMeasurable) M
    (Filter.Eventually.of_forall fun ξ => ?_)
  rw [norm_mul]
  refine le_trans (mul_le_mul_of_nonneg_right ?_ (norm_nonneg _)) (by rw [one_mul]; exact hM ξ)
  rw [mstProf_apply]
  exact norm_polyProfile_le_one P (2 ^ k) (iwRep ξ)

/-- The model symbol `Σ_{β∈E} G β (Φ_{2^k}ψ_s)(·-β)` is `L^∞`. -/
lemma memLp_mstModelFn_mstG (P : Polynomial ℤ) (l : ℕ) (d : ℕ) (χ : ℝ) (η : ℝ → ℂ)
    (hη : Continuous η) (s k : ℕ) {M : ℝ} (hM0 : 0 ≤ M)
    (hM : ∀ ζ : Circ, ‖mstEta d χ η s ζ‖ ≤ M) :
    MemLp (mstModelFn (mstG P) (mstProf P (2 ^ k)) (mstEta d χ η s) (mstLvl l s)) ⊤ haarT := by
  have hmemprod := memLp_mstProfBump P d χ η hη s k hM0 hM
  have h := memLp_arcSymbolW (fun β : Circ => β) (mstG P) (mstLvl l s) hmemprod
  simpa only [mstModelFn] using h

/-- The `L^∞`-class of the single level-`s` symbol `Φ_{2^k}·ψ_s`. -/
noncomputable def mstProfBumpCls (P : Polynomial ℤ) (d : ℕ) (χ : ℝ) (η : ℝ → ℂ) (s k : ℕ)
    (h : MemLp (fun ζ : Circ => mstProf P (2 ^ k) ζ * mstEta d χ η s ζ) ⊤ haarT) :
    Lp ℂ ⊤ haarT :=
  h.toLp (fun ζ : Circ => mstProf P (2 ^ k) ζ * mstEta d χ η s ζ)


/-! ## 6. The arc-sum identity for classes, and the per-arc bound -/

/-- `MemLp` of a general model symbol. -/
lemma memLp_mstModelFn_gen (P : Polynomial ℤ) (d : ℕ) (χ : ℝ) (η : ℝ → ℂ) (hη : Continuous η)
    (s k : ℕ) (E : Finset Circ) {M : ℝ} (hM0 : 0 ≤ M)
    (hM : ∀ ζ : Circ, ‖mstEta d χ η s ζ‖ ≤ M) :
    MemLp (mstModelFn (mstG P) (mstProf P (2 ^ k)) (mstEta d χ η s) E) ⊤ haarT := by
  have hmemprod := memLp_mstProfBump P d χ η hη s k hM0 hM
  have h := memLp_arcSymbolW (fun β : Circ => β) (mstG P) E hmemprod
  simpa only [mstModelFn] using h

/-- The `L²`-norm of the multiplier with a symbol bounded by `M`. -/
lemma lintegral_opMul_le_of_symbol (Φ : Lp ℂ ⊤ haarT) (z : ℤ → ℂ) (hz : Memℓp z 2) {M : ℝ}
    (hM : 0 ≤ M) (hb : ∀ᵐ ζ ∂haarT, ‖(Φ : Circ → ℂ) ζ‖ ≤ M) :
    ∫⁻ n : ℤ, ‖opMul Φ z hz n‖ₑ ^ (2 : ℝ) ∂MeasureTheory.Measure.count
      ≤ ENNReal.ofReal (M ^ 2) * ∫⁻ n : ℤ, ‖z n‖ₑ ^ (2 : ℝ) ∂MeasureTheory.Measure.count := by
  have h := eLpNorm_two_opMul_le (Φ := Φ) hz hM hb
  have hsq := pow_le_pow_left₀ (by positivity) h 2
  rw [eLpNorm_two_sq (opMul Φ z hz), mul_pow, eLpNorm_two_sq z, ← ENNReal.ofReal_pow hM] at hsq
  exact hsq

/-- **The general arc-sum identity at the level of `L^∞`-classes.** -/
lemma toLp_modelFn_eq_arcsum (G Φ ψ : Circ → ℂ) (E : Finset Circ)
    (hφ : MemLp (fun y : Circ => Φ y * ψ y) ⊤ haarT)
    (hA : MemLp (mstModelFn G Φ ψ E) ⊤ haarT) :
    hA.toLp (mstModelFn G Φ ψ E)
      = ∑ β ∈ E, G β • mstArcTransLp β (hφ.toLp (fun y : Circ => Φ y * ψ y)) := by
  refine Lp.ext ?_
  have hsum := Lp.coeFn_fun_finsetSum E (fun β : Circ =>
    G β • mstArcTransLp β (hφ.toLp (fun y : Circ => Φ y * ψ y)))
  have hsmul : ∀ᵐ ξ ∂haarT, ∀ β ∈ E,
      ((G β • mstArcTransLp β (hφ.toLp (fun y : Circ => Φ y * ψ y)) : Lp ℂ ⊤ haarT)
        : Circ → ℂ) ξ
        = G β * ((hφ.toLp (fun y : Circ => Φ y * ψ y) : Lp ℂ ⊤ haarT) : Circ → ℂ) (ξ - β) := by
    refine (Finset.eventually_all E).mpr fun β _ => ?_
    filter_upwards [Lp.coeFn_smul (G β)
        (mstArcTransLp β (hφ.toLp (fun y : Circ => Φ y * ψ y))),
      mstArcTransLp_coeFn β (hφ.toLp (fun y : Circ => Φ y * ψ y))] with ξ h1 h2
    rw [h1]
    simp only [Pi.smul_apply, smul_eq_mul]
    rw [h2]
    simp only [arcTranslate_apply]
  have hprod : ∀ᵐ ξ ∂haarT, ∀ β ∈ E,
      ((hφ.toLp (fun y : Circ => Φ y * ψ y) : Lp ℂ ⊤ haarT) : Circ → ℂ) (ξ - β)
        = Φ (ξ - β) * ψ (ξ - β) := by
    refine (Finset.eventually_all E).mpr fun β _ => ?_
    have hmp := (measurePreserving_add_right haarT (-β)).quasiMeasurePreserving.ae
      (MemLp.coeFn_toLp hφ)
    simpa only [sub_eq_add_neg] using hmp
  filter_upwards [MemLp.coeFn_toLp hA, hsum, hsmul, hprod] with ξ h0 h1 h2 h3
  rw [h0, h1, mstModelFn_apply]
  refine Finset.sum_congr rfl fun β hβ => ?_
  rw [h2 β hβ, h3 β hβ]

/-- **The model multiplier is the sum of its arc multipliers.** -/
lemma opMul_modelFn_eq_sum (G Φ ψ : Circ → ℂ) (E : Finset Circ)
    (hφ : MemLp (fun y : Circ => Φ y * ψ y) ⊤ haarT)
    (hA : MemLp (mstModelFn G Φ ψ E) ⊤ haarT)
    (f : ℤ → ℂ) (hf : Memℓp f 2) (n : ℤ) :
    opMul (hA.toLp (mstModelFn G Φ ψ E)) f hf n
      = ∑ β ∈ E, G β * opMul (mstArcTransLp β (hφ.toLp (fun y : Circ => Φ y * ψ y)))
          f hf n := by
  rw [toLp_modelFn_eq_arcsum G Φ ψ E hφ hA]
  have h := congrFun (opMul_finset_sum E G
    (fun β : Circ => mstArcTransLp β (hφ.toLp (fun y : Circ => Φ y * ψ y))) f hf) n
  simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul] at h
  exact h

/-- **(F1)**: the modulus of the multiplier with a translated symbol. -/
lemma norm_opMul_arcTranslate (Θ : Lp ℂ ⊤ haarT) (ρ : ℤ → ℂ) (hρ : Memℓp ρ 2) (α : Circ)
    (y : ℤ) :
    ‖opMul (mstArcTransLp α Θ) ρ hρ y‖ = ‖opMul Θ (modSeq ρ α) (memℓp_modSeq hρ α) y‖ := by
  have h := congrFun (opMul_modSeq Θ ρ hρ α) y
  rw [h, modSeq, norm_mul, norm_fourier_apply', mul_one]

/-- **The per-arc bound**: the modulus of the model multiplier is bounded by the sum over the arcs
of the modulus of the single-symbol multiplier applied to the modulated input. -/
lemma norm_opMul_modelFn_le (G Φ ψ : Circ → ℂ) (E : Finset Circ)
    (hφ : MemLp (fun y : Circ => Φ y * ψ y) ⊤ haarT)
    (hA : MemLp (mstModelFn G Φ ψ E) ⊤ haarT)
    (f : ℤ → ℂ) (hf : Memℓp f 2) (n : ℤ) :
    ‖opMul (hA.toLp (mstModelFn G Φ ψ E)) f hf n‖
      ≤ ∑ β ∈ E, ‖G β‖ * ‖opMul (hφ.toLp (fun y : Circ => Φ y * ψ y))
            (modSeq f β) (memℓp_modSeq hf β) n‖ := by
  rw [opMul_modelFn_eq_sum G Φ ψ E hφ hA f hf n]
  refine le_trans (norm_sum_le E (fun β : Circ => G β *
      opMul (mstArcTransLp β (hφ.toLp (fun y : Circ => Φ y * ψ y))) f hf n))
    (Finset.sum_le_sum fun β _ => ?_)
  rw [norm_mul, norm_opMul_arcTranslate]

/-- A pointwise bound on the model symbol. -/
lemma norm_mstModelFn_le (G Φ ψ : Circ → ℂ) (E : Finset Circ) {Pg : ℝ} {M : ℝ}
    (hG : ∀ β ∈ E, ‖G β‖ ≤ Pg) (hΦ : ∀ ζ : Circ, ‖Φ ζ‖ ≤ 1)
    (hψ : ∀ ζ : Circ, ‖ψ ζ‖ ≤ M) (ξ : Circ) :
    ‖mstModelFn G Φ ψ E ξ‖ ≤ (E.card : ℝ) * (Pg * M) := by
  rw [mstModelFn_apply]
  calc ‖∑ β ∈ E, G β * (Φ (ξ - β) * ψ (ξ - β))‖
      ≤ ∑ β ∈ E, ‖G β * (Φ (ξ - β) * ψ (ξ - β))‖ := norm_sum_le _ _
    _ ≤ ∑ β ∈ E, Pg * M := by
        refine Finset.sum_le_sum fun β hβ => ?_
        have h1 : ‖Φ (ξ - β) * ψ (ξ - β)‖ ≤ 1 * M := by
          rw [norm_mul]
          exact mul_le_mul (hΦ _) (hψ _) (norm_nonneg _) zero_le_one
        calc ‖G β * (Φ (ξ - β) * ψ (ξ - β))‖
            = ‖G β‖ * ‖Φ (ξ - β) * ψ (ξ - β)‖ := norm_mul _ _
          _ ≤ Pg * (1 * M) := mul_le_mul (hG β hβ) h1 (norm_nonneg _) (le_trans (norm_nonneg _) (hG β hβ))
          _ = Pg * M := by ring
    _ = (E.card : ℝ) * (Pg * M) := by
        rw [Finset.sum_const, nsmul_eq_mul]

/-- For `s ≠ 0` the annulus `mstLevel l (s+1) \ mstLevel l s` is the *auxiliary* annulus
`mstLvl l s = mstU l (s+1) \ mstU l s` used by the level estimates. -/
lemma mstLevel_sdiff_eq_mstLvl (l s : ℕ) (h : s ≠ 0) :
    mstLevel l (s + 1) \ mstLevel l s = mstLvl l s := by
  rw [mstLevel_succ, mstLevel_of_ne l s h, mstLvl]

/-! ## 7. The reflection of the conjugated model class -/

/-- **Reflection of a multiplier class.** -/
lemma norm_opMul_neg_eq (Xn X : Lp ℂ ⊤ haarT)
    (hXn : (Xn : Circ → ℂ) =ᵐ[haarT] fun ξ => (X : Circ → ℂ) (-ξ))
    (g : ℤ → ℂ) (hg : Memℓp g 2) (n : ℤ) :
    ‖opMul Xn g hg n‖ = ‖opMul X (negSeq g) (memℓp_negSeq hg) (-n)‖ := by
  rw [opMul_negFun X Xn hXn g hg (memℓp_negSeq hg) n]

/-- **`mstNuSCls` is the reflection of the unconjugated model class.** -/
lemma mstNuSCls_ae_reflect (P : Polynomial ℤ) (l d : ℕ) (χ : ℝ) (η : ℝ → ℂ) (k s : ℕ)
    (hA : MemLp (mstNuS P l d χ η k s) ⊤ haarT)
    (E : Finset Circ) (hE : E = mstLevel l (s + 1) \ mstLevel l s)
    (hB : MemLp (mstModelFn (mstG P) (mstProf P (2 ^ k))
      (mstEta d χ (fun x : ℝ => η (-x)) s) E) ⊤ haarT) :
    ((hA.toLp (mstNuS P l d χ η k s) : Lp ℂ ⊤ haarT) : Circ → ℂ)
      =ᵐ[haarT] fun ξ : Circ => ((hB.toLp (mstModelFn (mstG P) (mstProf P (2 ^ k))
          (mstEta d χ (fun x : ℝ => η (-x)) s) E) : Lp ℂ ⊤ haarT) : Circ → ℂ) (-ξ) := by
  have h1 := mstNuS_neg_model P l d χ η k s
  have h2 : (fun ξ : Circ => mstModelFn (mstG P) (mstProf P (2 ^ k))
        (mstEta d χ (fun x : ℝ => η (-x)) s) (mstLevel l (s + 1) \ mstLevel l s) (-ξ))
      = fun ξ : Circ => mstModelFn (mstG P) (mstProf P (2 ^ k))
        (mstEta d χ (fun x : ℝ => η (-x)) s) E (-ξ) := by
    funext ξ
    rw [hE]
  have h3 : (fun ξ : Circ => ((hB.toLp (mstModelFn (mstG P) (mstProf P (2 ^ k))
        (mstEta d χ (fun x : ℝ => η (-x)) s) E) : Lp ℂ ⊤ haarT) : Circ → ℂ) (-ξ))
      =ᵐ[haarT] fun ξ : Circ => mstModelFn (mstG P) (mstProf P (2 ^ k))
        (mstEta d χ (fun x : ℝ => η (-x)) s) E (-ξ) :=
    (Measure.measurePreserving_neg haarT).quasiMeasurePreserving.ae (MemLp.coeFn_toLp hB)
  exact (MemLp.coeFn_toLp hA).trans ((h1.trans (Filter.EventuallyEq.of_eq h2)).trans h3.symm)

/-- The `eLpNorm` of a modulated sequence equals that of the sequence. -/
lemma eLpNorm_modSeq (ρ : ℤ → ℂ) (β : Circ) :
    MeasureTheory.eLpNorm (modSeq ρ β) (ENNReal.ofReal 2) MeasureTheory.Measure.count
      = MeasureTheory.eLpNorm ρ (ENNReal.ofReal 2) MeasureTheory.Measure.count := by
  rw [← MeasureTheory.eLpNorm_enorm (modSeq ρ β) AEStronglyMeasurable.of_discrete,
    ← MeasureTheory.eLpNorm_enorm ρ AEStronglyMeasurable.of_discrete]
  refine MeasureTheory.eLpNorm_congr_ae ?_
  filter_upwards with m
  have h1 : ‖fourier m β‖ₑ = 1 := by
    rw [← ofReal_norm, norm_fourier_apply', ENNReal.ofReal_one]
  rw [modSeq, enorm_mul, h1, mul_one]

/-- The `L^∞`-bound on the model symbol of a level-`s` arc set with the weight `mstG P`. -/
lemma norm_mstModelFn_mstG_le (P : Polynomial ℤ) (d : ℕ) (χ : ℝ) (η : ℝ → ℂ) (s k : ℕ)
    (E : Finset Circ) {M : ℝ} (hM : ∀ ζ : Circ, ‖mstEta d χ η s ζ‖ ≤ M) (ξ : Circ) :
    ‖mstModelFn (mstG P) (mstProf P (2 ^ k)) (mstEta d χ η s) E ξ‖ ≤ (E.card : ℝ) * M := by
  refine le_trans (norm_mstModelFn_le (mstG P) (mstProf P (2 ^ k)) (mstEta d χ η s) E
    (fun β _ => mstG_norm_le_one P β) (fun ζ => norm_polyProfile_le_one P (2 ^ k) (iwRep ζ)) hM ξ) ?_
  rw [one_mul]
lemma mst_level_crude (P : Polynomial ℤ) (l : ℕ) (χ : ℝ) (η : ℝ → ℂ)
    (hη'cont : Continuous (fun x : ℝ => η (-x)))
    {M C₃ : ℝ} (hM0 : 0 ≤ M)
    (hM : ∀ s (ζ : Circ), ‖mstEta P.natDegree χ (fun x : ℝ => η (-x)) s ζ‖ ≤ M)
    (hC₃pos : 0 < C₃)
    (hmax : ∀ (s : ℕ) (g : ℤ → ℂ) (hg : Memℓp g 2) (hA : ℕ → Lp ℂ ⊤ haarT),
      HasModel P P.natDegree χ (fun x : ℝ => η (-x)) s hA →
      ∀ (hB : Lp ℂ ⊤ haarT), HasBump P.natDegree χ (fun x : ℝ => η (-x)) s hB →
        ∫⁻ m : ℤ, (⨆ n : ℕ, ⨆ (_ : mstN₀' P s ≤ n), ‖opMul (hA n) g hg m‖ₑ) ^ (2 : ℝ)
            ∂MeasureTheory.Measure.count
          ≤ ENNReal.ofReal (C₃ ^ 2)
            * (∫⁻ m : ℤ, ‖opMul hB g hg m‖ₑ ^ (2 : ℝ) ∂MeasureTheory.Measure.count))
    (hνsml : ∀ n s : ℕ, MemLp (mstNuS P l P.natDegree χ η n s) ⊤ haarT)
    (s : ℕ) (Ccrude : ℝ) (hCcrude_le : ((mstU l (s + 1)).card : ℝ)
      * (((mstN₀' P s : ℝ) + 1 + C₃) * M) ≤ Ccrude) (g : ℤ →₀ ℂ) :
    MeasureTheory.eLpNorm (fun m : ℤ => (⨆ k : ℕ,
        ‖opMul (mstNuSCls P l P.natDegree χ η k s (hνsml k s)) (⇑g)
          (memℓp_finsupp g) m‖ₑ))
        (ENNReal.ofReal 2) MeasureTheory.Measure.count
      ≤ ENNReal.ofReal Ccrude
        * MeasureTheory.eLpNorm (⇑g) (ENNReal.ofReal 2) MeasureTheory.Measure.count := by
  classical
  have hg : Memℓp (⇑g) 2 := memℓp_finsupp g
  have hneg : Memℓp (negSeq (⇑g)) 2 := memℓp_negSeq hg
  have hEn : MeasureTheory.eLpNorm (negSeq (⇑g)) (ENNReal.ofReal 2) MeasureTheory.Measure.count
      = MeasureTheory.eLpNorm (⇑g) (ENNReal.ofReal 2) MeasureTheory.Measure.count :=
    eLpNorm_neg_cplx (⇑g)
  let E : Finset Circ := mstLevel l (s + 1) \ mstLevel l s
  let hB : ∀ k : ℕ, MemLp (mstModelFn (mstG P) (mstProf P (2 ^ k))
      (mstEta P.natDegree χ (fun x : ℝ => η (-x)) s) E) ⊤ haarT :=
    fun k => memLp_mstModelFn_gen P P.natDegree χ (fun x : ℝ => η (-x)) hη'cont s k E hM0 (hM s)
  let Y : ℕ → Lp ℂ ⊤ haarT := fun k => (hB k).toLp
    (mstModelFn (mstG P) (mstProf P (2 ^ k)) (mstEta P.natDegree χ (fun x : ℝ => η (-x)) s) E)
  let hφ : ∀ k : ℕ, MemLp (fun y : Circ => mstProf P (2 ^ k) y
      * mstEta P.natDegree χ (fun x : ℝ => η (-x)) s y) ⊤ haarT :=
    fun k => memLp_mstProfBump P P.natDegree χ (fun x : ℝ => η (-x)) hη'cont s k hM0 (hM s)
  let Bcl : ℕ → Lp ℂ ⊤ haarT := fun k => (hφ k).toLp (fun y : Circ => mstProf P (2 ^ k) y
      * mstEta P.natDegree χ (fun x : ℝ => η (-x)) s y)
  let Bc : Lp ℂ ⊤ haarT := (memLp_mstEta_gen P.natDegree χ (fun x : ℝ => η (-x)) hη'cont s).toLp
      (mstEta P.natDegree χ (fun x : ℝ => η (-x)) s)
  have href : ∀ k : ℕ,
      ((mstNuSCls P l P.natDegree χ η k s (hνsml k s) : Lp ℂ ⊤ haarT) : Circ → ℂ)
        =ᵐ[haarT] fun ξ : Circ => ((Y k : Lp ℂ ⊤ haarT) : Circ → ℂ) (-ξ) :=
    fun k => mstNuSCls_ae_reflect P l P.natDegree χ η k s (hνsml k s) E rfl (hB k)
  have hBclmod : HasModel P P.natDegree χ (fun x : ℝ => η (-x)) s Bcl := by
    intro n
    filter_upwards [MemLp.coeFn_toLp (hφ n)] with ξ h
    exact h
  have hBcmod : HasBump P.natDegree χ (fun x : ℝ => η (-x)) s Bc := by
    filter_upwards [MemLp.coeFn_toLp
      (memLp_mstEta_gen P.natDegree χ (fun x : ℝ => η (-x)) hη'cont s)] with ξ h
    exact h
  have hLHS : MeasureTheory.eLpNorm (fun m : ℤ => (⨆ k : ℕ,
        ‖opMul (mstNuSCls P l P.natDegree χ η k s (hνsml k s)) (⇑g) hg m‖ₑ))
      (ENNReal.ofReal 2) MeasureTheory.Measure.count
      = MeasureTheory.eLpNorm (fun m : ℤ => (⨆ k : ℕ, ‖opMul (Y k) (negSeq (⇑g)) hneg m‖ₑ))
        (ENNReal.ofReal 2) MeasureTheory.Measure.count := by
    have hfun : (fun m : ℤ => (⨆ k : ℕ,
          ‖opMul (mstNuSCls P l P.natDegree χ η k s (hνsml k s)) (⇑g) hg m‖ₑ))
        = fun m : ℤ => (⨆ k : ℕ, ‖opMul (Y k) (negSeq (⇑g)) hneg (-m)‖ₑ) := by
      funext m
      refine iSup_congr fun k => ?_
      simpa only [← ofReal_norm] using congrArg ENNReal.ofReal
        (norm_opMul_neg_eq (mstNuSCls P l P.natDegree χ η k s (hνsml k s)) (Y k) (href k) (⇑g) hg m)
    rw [hfun, eLpNorm_neg_enorm (fun m : ℤ => (⨆ k : ℕ, ‖opMul (Y k) (negSeq (⇑g)) hneg m‖ₑ))]
  have harc : ∀ (n : ℕ) (m : ℤ), ‖opMul (Y n) (negSeq (⇑g)) hneg m‖
      ≤ ∑ β ∈ E, ‖opMul (Bcl n) (modSeq (negSeq (⇑g)) β) (memℓp_modSeq hneg β) m‖ := by
    intro n m
    refine le_trans (norm_opMul_modelFn_le (mstG P) (mstProf P (2 ^ n))
      (mstEta P.natDegree χ (fun x : ℝ => η (-x)) s) E (hφ n) (hB n) (negSeq (⇑g)) hneg m) ?_
    exact Finset.sum_le_sum fun β _ =>
      mul_le_of_le_one_left (norm_nonneg _) (mstG_norm_le_one P β)
  have hsup : ∀ m : ℤ, (⨆ n : ℕ, ‖opMul (Y n) (negSeq (⇑g)) hneg m‖ₑ)
      ≤ ∑ β ∈ E, (⨆ n : ℕ,
          ‖opMul (Bcl n) (modSeq (negSeq (⇑g)) β) (memℓp_modSeq hneg β) m‖ₑ) := by
    intro m
    refine iSup_le fun n => ?_
    calc ‖opMul (Y n) (negSeq (⇑g)) hneg m‖ₑ
        = ENNReal.ofReal ‖opMul (Y n) (negSeq (⇑g)) hneg m‖ := (ofReal_norm _).symm
      _ ≤ ENNReal.ofReal
            (∑ β ∈ E, ‖opMul (Bcl n) (modSeq (negSeq (⇑g)) β) (memℓp_modSeq hneg β) m‖) :=
          ENNReal.ofReal_le_ofReal (harc n m)
      _ = ∑ β ∈ E, ‖opMul (Bcl n) (modSeq (negSeq (⇑g)) β) (memℓp_modSeq hneg β) m‖ₑ := by
          rw [ENNReal.ofReal_sum_of_nonneg (fun β _ => norm_nonneg _)]
          exact Finset.sum_congr rfl fun β _ => ofReal_norm _
      _ ≤ ∑ β ∈ E, (⨆ n : ℕ,
            ‖opMul (Bcl n) (modSeq (negSeq (⇑g)) β) (memℓp_modSeq hneg β) m‖ₑ) :=
          Finset.sum_le_sum fun β _ => le_iSup
            (fun n => ‖opMul (Bcl n) (modSeq (negSeq (⇑g)) β) (memℓp_modSeq hneg β) m‖ₑ) n
  have hsupR : ∀ m : ℤ, (⨆ n : ℕ, ⨆ (_ : mstN₀' P s ≤ n),
        ‖opMul (Y n) (negSeq (⇑g)) hneg m‖ₑ)
      ≤ ∑ β ∈ E, (⨆ n : ℕ, ⨆ (_ : mstN₀' P s ≤ n),
          ‖opMul (Bcl n) (modSeq (negSeq (⇑g)) β) (memℓp_modSeq hneg β) m‖ₑ) := by
    intro m
    refine iSup_le fun n => iSup_le fun hn => ?_
    refine le_trans (le_of_eq (ofReal_norm _).symm) ?_
    refine le_trans (ENNReal.ofReal_le_ofReal (harc n m)) ?_
    rw [ENNReal.ofReal_sum_of_nonneg (fun β _ => norm_nonneg _)]
    refine le_trans (le_of_eq (Finset.sum_congr rfl fun β _ => ofReal_norm _)) ?_
    exact Finset.sum_le_sum fun β _ => le_iSup_of_le n (le_iSup_of_le hn le_rfl)
  have hpoint2 : ∀ m : ℤ, (⨆ n : ℕ, ‖opMul (Y n) (negSeq (⇑g)) hneg m‖ₑ)
      ≤ (⨆ n ∈ Finset.range (mstN₀' P s + 1), ‖opMul (Y n) (negSeq (⇑g)) hneg m‖ₑ)
        + (⨆ n : ℕ, ⨆ (_ : mstN₀' P s ≤ n), ‖opMul (Y n) (negSeq (⇑g)) hneg m‖ₑ) := by
    intro m
    refine iSup_le fun n => ?_
    rcases lt_or_ge n (mstN₀' P s + 1) with hn | hn
    · exact le_add_right (le_iSup_of_le n (le_iSup_of_le (Finset.mem_range.mpr hn) le_rfl))
    · exact le_add_left (le_iSup_of_le n (le_iSup_of_le (by omega) le_rfl))
  have hhead : MeasureTheory.eLpNorm (fun m : ℤ => (⨆ n ∈ Finset.range (mstN₀' P s + 1),
        ‖opMul (Y n) (negSeq (⇑g)) hneg m‖ₑ)) (ENNReal.ofReal 2) MeasureTheory.Measure.count
      ≤ ENNReal.ofReal (((mstN₀' P s + 1 : ℕ) : ℝ) * ((E.card : ℝ) * M))
        * MeasureTheory.eLpNorm (negSeq (⇑g)) (ENNReal.ofReal 2) MeasureTheory.Measure.count := by
    have hpt : ∀ m : ℤ, (⨆ n ∈ Finset.range (mstN₀' P s + 1),
          ‖opMul (Y n) (negSeq (⇑g)) hneg m‖ₑ)
        ≤ ∑ n ∈ Finset.range (mstN₀' P s + 1), ‖opMul (Y n) (negSeq (⇑g)) hneg m‖ₑ := by
      intro m
      exact iSup_le fun n => iSup_le fun hn =>
        Finset.single_le_sum (f := fun n : ℕ => ‖opMul (Y n) (negSeq (⇑g)) hneg m‖ₑ)
          (fun _ _ => bot_le) hn
    have hmono1 : MeasureTheory.eLpNorm (fun m : ℤ =>
          (⨆ n ∈ Finset.range (mstN₀' P s + 1), ‖opMul (Y n) (negSeq (⇑g)) hneg m‖ₑ))
        (ENNReal.ofReal 2) MeasureTheory.Measure.count
        ≤ MeasureTheory.eLpNorm (fun m : ℤ =>
          ∑ n ∈ Finset.range (mstN₀' P s + 1), ‖opMul (Y n) (negSeq (⇑g)) hneg m‖ₑ)
        (ENNReal.ofReal 2) MeasureTheory.Measure.count := by
      refine eLpNorm_mono_enorm AEStronglyMeasurable.of_discrete (fun m => ?_)
      rw [enorm_eq_self, enorm_eq_self]
      exact hpt m
    have hstep1 : (∑ n ∈ Finset.range (mstN₀' P s + 1),
          MeasureTheory.eLpNorm (fun m : ℤ => ‖opMul (Y n) (negSeq (⇑g)) hneg m‖ₑ)
            (ENNReal.ofReal 2) MeasureTheory.Measure.count)
        ≤ ∑ _n ∈ Finset.range (mstN₀' P s + 1),
            (ENNReal.ofReal ((E.card : ℝ) * M)
              * MeasureTheory.eLpNorm (negSeq (⇑g)) (ENNReal.ofReal 2)
                MeasureTheory.Measure.count) :=
      Finset.sum_le_sum fun n _ => by
        have hb : ∀ᵐ ζ ∂haarT, ‖(Y n : Circ → ℂ) ζ‖ ≤ (E.card : ℝ) * M := by
          filter_upwards [MemLp.coeFn_toLp (hB n)] with ζ h
          rw [h]
          exact norm_mstModelFn_mstG_le P P.natDegree χ (fun x : ℝ => η (-x)) s n E (hM s) ζ
        have h := eLpNorm_two_opMul_le (Φ := Y n) hneg (by positivity) hb
        rw [MeasureTheory.eLpNorm_enorm _ AEStronglyMeasurable.of_discrete]
        exact h
    have hstep2 : (∑ _n ∈ Finset.range (mstN₀' P s + 1),
            (ENNReal.ofReal ((E.card : ℝ) * M)
              * MeasureTheory.eLpNorm (negSeq (⇑g)) (ENNReal.ofReal 2)
                MeasureTheory.Measure.count))
        = ENNReal.ofReal (((mstN₀' P s + 1 : ℕ) : ℝ) * ((E.card : ℝ) * M))
          * MeasureTheory.eLpNorm (negSeq (⇑g)) (ENNReal.ofReal 2)
            MeasureTheory.Measure.count := by
      rw [Finset.sum_const, nsmul_eq_mul, Finset.card_range, ← mul_assoc,
        ← ENNReal.ofReal_natCast, ← ENNReal.ofReal_mul (Nat.cast_nonneg _)]
    refine le_trans hmono1 ?_
    rw [← show (∑ n ∈ Finset.range (mstN₀' P s + 1),
          fun m : ℤ => ‖opMul (Y n) (negSeq (⇑g)) hneg m‖ₑ)
        = (fun m : ℤ => ∑ n ∈ Finset.range (mstN₀' P s + 1),
            ‖opMul (Y n) (negSeq (⇑g)) hneg m‖ₑ) from by
      funext m; rw [Finset.sum_apply]]
    exact le_trans (eLpNorm_sum_le (by norm_num))
      (le_of_le_of_eq hstep1 hstep2)
  have htail : MeasureTheory.eLpNorm (fun m : ℤ => (⨆ n : ℕ, ⨆ (_ : mstN₀' P s ≤ n),
        ‖opMul (Y n) (negSeq (⇑g)) hneg m‖ₑ)) (ENNReal.ofReal 2) MeasureTheory.Measure.count
      ≤ ENNReal.ofReal ((E.card : ℝ) * (C₃ * M))
        * MeasureTheory.eLpNorm (negSeq (⇑g)) (ENNReal.ofReal 2) MeasureTheory.Measure.count := by
    have hmono2 : MeasureTheory.eLpNorm (fun m : ℤ =>
          (⨆ n : ℕ, ⨆ (_ : mstN₀' P s ≤ n), ‖opMul (Y n) (negSeq (⇑g)) hneg m‖ₑ))
        (ENNReal.ofReal 2) MeasureTheory.Measure.count
        ≤ MeasureTheory.eLpNorm (fun m : ℤ => ∑ β ∈ E,
          (⨆ n : ℕ, ⨆ (_ : mstN₀' P s ≤ n),
            ‖opMul (Bcl n) (modSeq (negSeq (⇑g)) β) (memℓp_modSeq hneg β) m‖ₑ))
        (ENNReal.ofReal 2) MeasureTheory.Measure.count := by
      refine eLpNorm_mono_enorm AEStronglyMeasurable.of_discrete (fun m => ?_)
      rw [enorm_eq_self, enorm_eq_self]
      exact hsupR m
    refine le_trans hmono2 ?_
    rw [← show (∑ β ∈ E, fun m : ℤ => (⨆ n : ℕ, ⨆ (_ : mstN₀' P s ≤ n),
          ‖opMul (Bcl n) (modSeq (negSeq (⇑g)) β) (memℓp_modSeq hneg β) m‖ₑ))
        = (fun m : ℤ => ∑ β ∈ E, (⨆ n : ℕ, ⨆ (_ : mstN₀' P s ≤ n),
          ‖opMul (Bcl n) (modSeq (negSeq (⇑g)) β) (memℓp_modSeq hneg β) m‖ₑ)) from by
      funext m; rw [Finset.sum_apply]]
    refine le_trans (eLpNorm_sum_le (by norm_num)) ?_
    have hstep1 : (∑ β ∈ E, MeasureTheory.eLpNorm (fun m : ℤ => (⨆ n : ℕ,
          ⨆ (_ : mstN₀' P s ≤ n),
          ‖opMul (Bcl n) (modSeq (negSeq (⇑g)) β) (memℓp_modSeq hneg β) m‖ₑ))
            (ENNReal.ofReal 2) MeasureTheory.Measure.count)
        ≤ ∑ _β ∈ E, (ENNReal.ofReal (C₃ * M)
            * MeasureTheory.eLpNorm (negSeq (⇑g)) (ENNReal.ofReal 2)
              MeasureTheory.Measure.count) := by
      refine Finset.sum_le_sum ?_
      intro β _
      have hmaxs := hmax s (modSeq (negSeq (⇑g)) β) (memℓp_modSeq hneg β)
          Bcl hBclmod Bc hBcmod
      have hbc : ∀ᵐ ζ ∂haarT, ‖(Bc : Circ → ℂ) ζ‖ ≤ M := by
        filter_upwards [MemLp.coeFn_toLp
          (memLp_mstEta_gen P.natDegree χ (fun x : ℝ => η (-x)) hη'cont s)] with ζ h
        rw [h]
        exact hM s ζ
      have hb2 := lintegral_opMul_le_of_symbol Bc (modSeq (negSeq (⇑g)) β)
        (memℓp_modSeq hneg β) hM0 hbc
      have hmain : ∫⁻ m : ℤ, (⨆ n : ℕ, ⨆ (_ : mstN₀' P s ≤ n),
            ‖opMul (Bcl n) (modSeq (negSeq (⇑g)) β) (memℓp_modSeq hneg β) m‖ₑ) ^ (2 : ℝ)
            ∂MeasureTheory.Measure.count
          ≤ ENNReal.ofReal ((C₃ * M) ^ 2)
            * ∫⁻ m : ℤ, ‖modSeq (negSeq (⇑g)) β m‖ₑ ^ (2 : ℝ)
                ∂MeasureTheory.Measure.count := by
        refine le_trans hmaxs ?_
        refine le_trans (mul_le_mul_of_nonneg_left hb2
          (by positivity : (0:ℝ≥0∞) ≤ ENNReal.ofReal (C₃ ^ 2))) ?_
        rw [← mul_assoc, ← ENNReal.ofReal_mul (sq_nonneg C₃),
          show C₃ ^ 2 * M ^ 2 = (C₃ * M) ^ 2 from by ring]
      have hstep := eLpNorm_le_of_lintegral_sq_le (μ := C₃ * M) (by positivity) hmain
      rwa [eLpNorm_modSeq] at hstep
    have hstep2 : (∑ _β ∈ E, (ENNReal.ofReal (C₃ * M)
            * MeasureTheory.eLpNorm (negSeq (⇑g)) (ENNReal.ofReal 2)
              MeasureTheory.Measure.count))
        = ENNReal.ofReal ((E.card : ℝ) * (C₃ * M))
          * MeasureTheory.eLpNorm (negSeq (⇑g)) (ENNReal.ofReal 2) MeasureTheory.Measure.count := by
      rw [Finset.sum_const, nsmul_eq_mul, ← mul_assoc, ← ENNReal.ofReal_natCast,
        ← ENNReal.ofReal_mul (Nat.cast_nonneg _)]
    exact le_of_le_of_eq hstep1 hstep2
  have hsplit2 : MeasureTheory.eLpNorm (fun m : ℤ => (⨆ n : ℕ, ‖opMul (Y n) (negSeq (⇑g)) hneg m‖ₑ))
        (ENNReal.ofReal 2) MeasureTheory.Measure.count
      ≤ ENNReal.ofReal Ccrude
        * MeasureTheory.eLpNorm (negSeq (⇑g)) (ENNReal.ofReal 2) MeasureTheory.Measure.count := by
    have hmono3 : MeasureTheory.eLpNorm (fun m : ℤ =>
          (⨆ n : ℕ, ‖opMul (Y n) (negSeq (⇑g)) hneg m‖ₑ))
        (ENNReal.ofReal 2) MeasureTheory.Measure.count
        ≤ MeasureTheory.eLpNorm (fun m : ℤ =>
          (⨆ n ∈ Finset.range (mstN₀' P s + 1), ‖opMul (Y n) (negSeq (⇑g)) hneg m‖ₑ)
          + (⨆ n : ℕ, ⨆ (_ : mstN₀' P s ≤ n), ‖opMul (Y n) (negSeq (⇑g)) hneg m‖ₑ))
        (ENNReal.ofReal 2) MeasureTheory.Measure.count := by
      refine eLpNorm_mono_enorm AEStronglyMeasurable.of_discrete (fun m => ?_)
      rw [enorm_eq_self, enorm_eq_self]
      exact hpoint2 m
    refine le_trans hmono3 ?_
    have hm1 : AEStronglyMeasurable (fun m : ℤ => (⨆ n ∈ Finset.range (mstN₀' P s + 1),
        ‖opMul (Y n) (negSeq (⇑g)) hneg m‖ₑ)) MeasureTheory.Measure.count :=
      Measurable.of_discrete.aestronglyMeasurable
    have hm2 : AEStronglyMeasurable (fun m : ℤ => (⨆ n : ℕ, ⨆ (_ : mstN₀' P s ≤ n),
        ‖opMul (Y n) (negSeq (⇑g)) hneg m‖ₑ)) MeasureTheory.Measure.count :=
      Measurable.of_discrete.aestronglyMeasurable
    refine le_trans (eLpNorm_add_le (by norm_num : (1:ℝ≥0∞) ≤ ENNReal.ofReal 2)) ?_
    refine le_trans (add_le_add hhead htail) ?_
    rw [← add_mul, ← ENNReal.ofReal_add (by positivity) (by positivity)]
    refine mul_le_mul_of_nonneg_right (ENNReal.ofReal_le_ofReal ?_) (by positivity)
    have hcard : ((E.card : ℕ) : ℝ) ≤ ((mstU l (s + 1)).card : ℝ) := by
      have hsub : E.card ≤ (mstU l (s + 1)).card :=
        Finset.card_le_card fun x hx => by
          rw [Finset.mem_sdiff] at hx
          rw [mstLevel_succ] at hx
          exact hx.1
      exact_mod_cast hsub
    have hN : (0:ℝ) ≤ (mstN₀' P s : ℝ) := Nat.cast_nonneg _
    have h3 : (0:ℝ) ≤ C₃ := le_of_lt hC₃pos
    refine le_trans ?_ hCcrude_le
    push_cast
    have hpos : (0:ℝ) ≤ M * ((mstN₀' P s : ℝ) + 1 + C₃) :=
      mul_nonneg hM0 (by linarith)
    have hmul := mul_le_mul_of_nonneg_right hcard hpos
    nlinarith [hmul]
  refine le_trans hLHS.le ?_
  rw [hEn] at hsplit2
  exact hsplit2
/-- **The `ℓ²` half of MST's level estimate, eq. (88) of arXiv:1512.07518, for the CONJUGATED model `mstNuS`** (the model actually used in this chapter: the density symbol is `star ∘ mstWeyl`, so MST's model must be conjugated).

`mstNuS P l d χ η n s = Σ_{β ∈ mstLevel l (s+1) ∖ mstLevel l s} star (mstG P β) · star (mstProf P (2^n) (ξ − β)) · mstEta d χ η s (ξ − β)`; the pointwise increments of this symbol are the *conjugates* of those of the unconjugated model `mstModelFn (star ∘ mstG) (mstProf P (2^n)) (mstEta d χ η s) E`, hence have identical norms, so every modulus-based bound of `level_l2_mst_small_n` (proved) and `level_l2_mst_large_n` (the sibling lane's, in flight) carries over verbatim.

Route: `sup_{k} ≤ sup_{k ≤ 2^{κ_s}} + sup_{k ≥ 2^{κ_s}}` with `κ_s = mstKappa P s ≤ 40·d·(s+1)^{1/10}`; the first half is `level_l2_of_symbol_bounds` (proved, abstract in `S`) applied to `S k := mstNuSCls P l d χ η k s (hνsml k s)` with `μ := D(s+1)^{-δl}·max 1 Cdec` — verify `h0` and `hΔ` exactly as in `level_l2_mst_small_n`'s proof (`mstProf_sub_one_le` for the small regime, `polyProfile_decay_sharp` for the large one, `mstEta_arcSum_le` for the bump sum, `sigmaN_separated` for the disjointness, `mstG_norm_le_one`), using `‖star z‖ = ‖z‖` to move the conjugation across; the second half is `level_l2_mst_large_n`'s argument (freezing + `msw_sampling_lp`) with the same conjugation.  The cases `s = 0` (where `mstNuS` is the single term `β = 0`, `G(0) = 1`, outside the range of `hGauss`) and the finitely many `s` below the threshold of `level_l2_mst_large_n` are absorbed into the existential constant `C`. -/
theorem mst_level_l2 (P : Polynomial ℤ) (hd : 2 ≤ P.natDegree) (hc : 0 < P.leadingCoeff)
    (l : ℕ) (hl : 1 ≤ l) {χ : ℝ} (hχ0 : 0 < χ) (hχ1 : χ < 1 / 10)
    (η : ℝ → ℂ) (hηc : ContDiff ℝ 2 η) (hη1 : η 0 = 1)
    (hηsup : ∀ x : ℝ, 1 / 2 ≤ |x| → η x = 0)
    {δ : ℝ} (hδ : 0 < δ) (D : ℝ) (hD : 0 < D)
    (hGauss : ∀ (s : ℕ) (β : Work.BourgainPlan.IonescuWainger.Circle),
      β ∈ Work.BourgainPlan.Maximal.mstU l (s + 1) \ Work.BourgainPlan.Maximal.mstU l s →
      ‖Work.BourgainPlan.Maximal.mstG P β‖ ≤ D * ((s : ℝ) + 1) ^ (-(δ * l)))
    (hνsml : ∀ n s : ℕ, MeasureTheory.MemLp
      (Work.BourgainPlan.Maximal.mstNuS P l P.natDegree χ η n s) ⊤
      (AddCircle.haarAddCircle (T := 1))) :
    ∃ C : ℝ, 0 < C ∧ ∀ s : ℕ, ∀ g : ℤ →₀ ℂ,
      MeasureTheory.eLpNorm (fun m : ℤ => (⨆ k : ℕ,
          ‖Work.BourgainPlan.IonescuWainger.opMul
            (Work.BourgainPlan.Maximal.mstNuSCls P l P.natDegree χ η k s (hνsml k s))
            (⇑g) (Work.BourgainPlan.IonescuWainger.memℓp_finsupp g) m‖ₑ))
          (ENNReal.ofReal 2) MeasureTheory.Measure.count
        ≤ ENNReal.ofReal (C * ((s : ℝ) + 1) ^ ((1 / 10 : ℝ) - δ * l))
          * MeasureTheory.eLpNorm (⇑g) (ENNReal.ofReal 2) MeasureTheory.Measure.count := by
  classical
  have hη'c : ContDiff ℝ 2 (fun x : ℝ => η (-x)) := hηc.comp contDiff_neg
  have hη'1 : (fun x : ℝ => η (-x)) 0 = 1 := by simpa using hη1
  have hη'sup : ∀ x : ℝ, 1 / 2 ≤ |x| → (fun x : ℝ => η (-x)) x = 0 := by
    intro x hx
    exact hηsup (-x) (by rw [abs_neg]; exact hx)
  have hη'cont : Continuous (fun x : ℝ => η (-x)) := hη'c.continuous
  obtain ⟨M, hM0, hM⟩ := exists_bound_mstEta P.natDegree χ (fun x : ℝ => η (-x)) hη'c hη'sup
  obtain ⟨C₁, hC₁pos, hsmall⟩ := level_l2_mst_small_n P hd l hl χ hχ0 hχ1
    (fun x : ℝ => η (-x)) hη'c hη'1 hη'sup δ hδ
  obtain ⟨C₂, hC₂pos, s₂, hlarge⟩ := level_l2_mst_large_n P hd l hl χ hχ0 hχ1
    (fun x : ℝ => η (-x)) hη'c hη'1 hη'sup δ hδ
  obtain ⟨C₃, hC₃pos, hmax⟩ := mstMaximal_all P hd l hl χ hχ0 hχ1
    (fun x : ℝ => η (-x)) hη'c hη'1 hη'sup
  set S : ℕ := max s₂ 1 with hSdef
  set Ccrude : ℕ → ℝ := fun s => ((mstU l (s + 1)).card : ℝ) * (((mstN₀' P s : ℝ) + 1 + C₃) * M)
    with hCcrudedef
  set CA : ℝ := C₁ * ((20 * P.natDegree + 20 * P.natDegree + 1 : ℕ) : ℝ) * D + C₂ * D + 1
    with hCAdef
  set Cbig : ℝ := ∑ t ∈ Finset.range S,
    (Ccrude t * (((t : ℝ) + 1) ^ ((δ * l) - (1 / 10 : ℝ))) + 1) with hCbigdef
  set C : ℝ := CA + Cbig + 1 with hCdef
  have hCcrude_nn : ∀ s : ℕ, 0 ≤ Ccrude s := by
    intro s
    rw [hCcrudedef]
    have h3 : (0:ℝ) ≤ ((mstU l (s + 1)).card : ℝ) := Nat.cast_nonneg _
    have h4 : (0:ℝ) ≤ (mstN₀' P s : ℝ) + 1 + C₃ := by
      have := Nat.cast_nonneg (α := ℝ) (mstN₀' P s)
      linarith [hC₃pos]
    exact mul_nonneg h3 (mul_nonneg h4 hM0)
  have hCbig_nn : 0 ≤ Cbig := by
    rw [hCbigdef]
    refine Finset.sum_nonneg fun t _ => ?_
    have h1 := hCcrude_nn t
    have h2 : (0:ℝ) ≤ ((t : ℝ) + 1) ^ ((δ * l) - (1 / 10 : ℝ)) :=
      Real.rpow_nonneg (by positivity) _
    exact add_nonneg (mul_nonneg h1 h2) zero_le_one
  have hCApos : 0 < CA := by
    rw [hCAdef]
    have h1 : (0:ℝ) < ((20 * P.natDegree + 20 * P.natDegree + 1 : ℕ) : ℝ) := by positivity
    have h2 : (0:ℝ) < C₁ * ((20 * P.natDegree + 20 * P.natDegree + 1 : ℕ) : ℝ) * D :=
      mul_pos (mul_pos hC₁pos h1) hD
    linarith [h2, mul_nonneg hC₂pos.le hD.le]
  have hCAleC : CA ≤ C := by rw [hCdef]; linarith
  refine ⟨C, by rw [hCdef]; linarith, fun s g => ?_⟩
  have hg : Memℓp (⇑g) 2 := memℓp_finsupp g
  have hneg : Memℓp (negSeq (⇑g)) 2 := memℓp_negSeq hg
  have hEn : MeasureTheory.eLpNorm (negSeq (⇑g)) (ENNReal.ofReal 2) MeasureTheory.Measure.count
      = MeasureTheory.eLpNorm (⇑g) (ENNReal.ofReal 2) MeasureTheory.Measure.count :=
    eLpNorm_neg_cplx (⇑g)
  by_cases hs : S ≤ s
  · -- ================= sharp case: s ≥ S =================
    have hne : s ≠ 0 := by
      have h1 : 1 ≤ s := le_trans (le_max_right s₂ 1) hs
      omega
    have hs₂ : s₂ ≤ s := le_trans (le_max_left s₂ 1) hs
    let hB : ∀ k : ℕ, MemLp (mstModelFn (mstG P) (mstProf P (2 ^ k))
        (mstEta P.natDegree χ (fun x : ℝ => η (-x)) s) (mstLvl l s)) ⊤ haarT :=
      fun k => memLp_mstModelFn_mstG P l P.natDegree χ (fun x : ℝ => η (-x)) hη'cont s k hM0 (hM s)
    let X : ℕ → Lp ℂ ⊤ haarT := fun k => (hB k).toLp
      (mstModelFn (mstG P) (mstProf P (2 ^ k)) (mstEta P.natDegree χ (fun x : ℝ => η (-x)) s)
        (mstLvl l s))
    have hXcoe : ∀ n : ℕ, (X n : Circ → ℂ) =ᵐ[haarT]
        mstModelFn (mstG P) (mstProf P (2 ^ n)) (mstEta P.natDegree χ (fun x : ℝ => η (-x)) s)
          ((mstU l (s + 1)) \ (mstU l s)) :=
      fun n => MemLp.coeFn_toLp _
    have href : ∀ k : ℕ,
        ((mstNuSCls P l P.natDegree χ η k s (hνsml k s) : Lp ℂ ⊤ haarT) : Circ → ℂ)
          =ᵐ[haarT] fun ξ : Circ => ((X k : Lp ℂ ⊤ haarT) : Circ → ℂ) (-ξ) :=
      fun k => mstNuSCls_ae_reflect P l P.natDegree χ η k s (hνsml k s) (mstLvl l s)
        (mstLevel_sdiff_eq_mstLvl l s hne).symm (hB k)
    have hLHS : MeasureTheory.eLpNorm (fun m : ℤ => (⨆ k : ℕ,
          ‖opMul (mstNuSCls P l P.natDegree χ η k s (hνsml k s)) (⇑g) hg m‖ₑ))
        (ENNReal.ofReal 2) MeasureTheory.Measure.count
        = MeasureTheory.eLpNorm (fun m : ℤ => (⨆ k : ℕ, ‖opMul (X k) (negSeq (⇑g)) hneg m‖ₑ))
          (ENNReal.ofReal 2) MeasureTheory.Measure.count := by
      have hfun : (fun m : ℤ => (⨆ k : ℕ,
            ‖opMul (mstNuSCls P l P.natDegree χ η k s (hνsml k s)) (⇑g) hg m‖ₑ))
          = fun m : ℤ => (⨆ k : ℕ, ‖opMul (X k) (negSeq (⇑g)) hneg (-m)‖ₑ) := by
        funext m
        refine iSup_congr fun k => ?_
        simpa only [← ofReal_norm] using congrArg ENNReal.ofReal
          (norm_opMul_neg_eq (mstNuSCls P l P.natDegree χ η k s (hνsml k s)) (X k) (href k) (⇑g) hg m)
      rw [hfun, eLpNorm_neg_enorm (fun m : ℤ => (⨆ k : ℕ, ‖opMul (X k) (negSeq (⇑g)) hneg m‖ₑ))]
    have hpoint : ∀ m : ℤ, (⨆ k : ℕ, ‖opMul (X k) (negSeq (⇑g)) hneg m‖ₑ)
        ≤ (⨆ n ∈ Finset.range (2 ^ (mstKappa P s) + 1), ‖opMul (X n) (negSeq (⇑g)) hneg m‖ₑ)
          + (⨆ n : ℕ, ⨆ (_ : 2 ^ (mstKappa P s) ≤ n), ‖opMul (X n) (negSeq (⇑g)) hneg m‖ₑ) := by
      intro m
      refine iSup_le fun k => ?_
      rcases lt_or_ge k (2 ^ (mstKappa P s) + 1) with hk | hk
      · exact le_add_right (le_iSup_of_le k (le_iSup_of_le (Finset.mem_range.mpr hk) le_rfl))
      · exact le_add_left (le_iSup_of_le k (le_iSup_of_le (by omega) le_rfl))
    have hmeas1 : AEStronglyMeasurable (fun m : ℤ =>
        (⨆ n ∈ Finset.range (2 ^ (mstKappa P s) + 1), ‖opMul (X n) (negSeq (⇑g)) hneg m‖ₑ))
        MeasureTheory.Measure.count := Measurable.of_discrete.aestronglyMeasurable
    have hmeas2 : AEStronglyMeasurable (fun m : ℤ =>
        (⨆ n : ℕ, ⨆ (_ : 2 ^ (mstKappa P s) ≤ n), ‖opMul (X n) (negSeq (⇑g)) hneg m‖ₑ))
        MeasureTheory.Measure.count := Measurable.of_discrete.aestronglyMeasurable
    have hsm := hsmall s (mstKappa P s) (mstG P) D hD.le (fun β hβ => hGauss s β hβ) X hXcoe
      (negSeq (⇑g)) hneg
    have hsmb : ENNReal.ofReal
          ((C₁ * ((mstKappa P s : ℝ) + 1) * D * ((s : ℝ) + 1) ^ (-(δ * l))) ^ 2)
          * ∫⁻ m : ℤ, ‖negSeq (⇑g) m‖ₑ ^ (2:ℝ) ∂MeasureTheory.Measure.count
        = ENNReal.ofReal
          ((C₁ * ((mstKappa P s : ℝ) + 1) * D * ((s : ℝ) + 1) ^ (-(δ * l))) ^ 2)
          * ∫⁻ m : ℤ, ‖negSeq (⇑g) m‖ₑ ^ (2:ℕ) ∂MeasureTheory.Measure.count := by
      refine congrArg (fun Z => ENNReal.ofReal
        ((C₁ * ((mstKappa P s : ℝ) + 1) * D * ((s : ℝ) + 1) ^ (-(δ * l))) ^ 2) * Z) ?_
      refine lintegral_congr fun m => ?_
      first
        | exact ENNReal.rpow_natCast _ 2
        | exact (ENNReal.rpow_natCast _ 2).symm
    have hsmE := eLpNorm_le_of_lintegral_sq_le
      (μ := C₁ * ((mstKappa P s : ℝ) + 1) * D * ((s : ℝ) + 1) ^ (-(δ * l)))
      (by positivity) (le_of_le_of_eq hsm hsmb.symm)
    have hlg := hlarge s hs₂ (mstG P) D hD.le (fun β hβ => hGauss s β hβ) X hXcoe (negSeq (⇑g)) hneg
    have hlgb : ENNReal.ofReal ((C₂ * D * ((s : ℝ) + 1) ^ (-(δ * l))) ^ 2)
          * ∫⁻ m : ℤ, ‖negSeq (⇑g) m‖ₑ ^ (2:ℝ) ∂MeasureTheory.Measure.count
        = ENNReal.ofReal ((C₂ * D * ((s : ℝ) + 1) ^ (-(δ * l))) ^ 2)
          * ∫⁻ m : ℤ, ‖negSeq (⇑g) m‖ₑ ^ (2:ℕ) ∂MeasureTheory.Measure.count := by
      refine congrArg (fun Z => ENNReal.ofReal
        ((C₂ * D * ((s : ℝ) + 1) ^ (-(δ * l))) ^ 2) * Z) ?_
      refine lintegral_congr fun m => ?_
      first
        | exact ENNReal.rpow_natCast _ 2
        | exact (ENNReal.rpow_natCast _ 2).symm
    have hlgE := eLpNorm_le_of_lintegral_sq_le
      (μ := C₂ * D * ((s : ℝ) + 1) ^ (-(δ * l))) (by positivity)
      (le_of_le_of_eq hlg hlgb.symm)
    have harith : C₁ * ((mstKappa P s : ℝ) + 1) * D * ((s : ℝ) + 1) ^ (-(δ * l))
        + C₂ * D * ((s : ℝ) + 1) ^ (-(δ * l))
        ≤ CA * ((s : ℝ) + 1) ^ ((1 / 10 : ℝ) - δ * l) := by
      have hu : 0 < (s : ℝ) + 1 := by positivity
      have hU1 : (1 : ℝ) ≤ ((s : ℝ) + 1) ^ (1 / 10 : ℝ) :=
        Real.one_le_rpow (by linarith [Nat.cast_nonneg (α := ℝ) s]) (by norm_num)
      have hw : 0 ≤ ((s : ℝ) + 1) ^ (-(δ * l)) := Real.rpow_nonneg (by positivity) _
      have hκ : (mstKappa P s : ℝ) + 1
          ≤ ((20 * P.natDegree + 20 * P.natDegree + 1 : ℕ) : ℝ) * ((s : ℝ) + 1) ^ (1 / 10 : ℝ) := by
        rw [mstKappa]
        push_cast
        have hfl : (((⌊((s : ℝ) + 1) ^ (1 / 10 : ℝ)⌋₊ : ℕ) : ℝ)
            ≤ ((s : ℝ) + 1) ^ (1 / 10 : ℝ)) :=
          Nat.floor_le (Real.rpow_nonneg (by positivity) _)
        nlinarith [hfl, hU1, Nat.cast_nonneg (α := ℝ) P.natDegree]
      rw [hCAdef, show (1 / 10 : ℝ) - δ * l = (1 / 10 : ℝ) + (-(δ * l)) by ring,
        Real.rpow_add hu]
      have hCw : (0:ℝ) ≤ C₁ * D * ((s : ℝ) + 1) ^ (-(δ * l)) := by positivity
      have hCw2 : (0:ℝ) ≤ C₂ * D * ((s : ℝ) + 1) ^ (-(δ * l)) := by positivity
      nlinarith [hκ, hU1, hw, hCw, hCw2, hC₁pos, hC₂pos, hD]
    have hmono : MeasureTheory.eLpNorm (fun m : ℤ =>
          (⨆ k : ℕ, ‖opMul (X k) (negSeq (⇑g)) hneg m‖ₑ))
        (ENNReal.ofReal 2) MeasureTheory.Measure.count
        ≤ MeasureTheory.eLpNorm (fun m : ℤ =>
          (⨆ n ∈ Finset.range (2 ^ (mstKappa P s) + 1), ‖opMul (X n) (negSeq (⇑g)) hneg m‖ₑ)
          + (⨆ n : ℕ, ⨆ (_ : 2 ^ (mstKappa P s) ≤ n), ‖opMul (X n) (negSeq (⇑g)) hneg m‖ₑ))
        (ENNReal.ofReal 2) MeasureTheory.Measure.count := by
      refine eLpNorm_mono_enorm AEStronglyMeasurable.of_discrete (fun m => ?_)
      rw [enorm_eq_self, enorm_eq_self]
      exact hpoint m
    refine le_trans hLHS.le ?_
    refine le_trans hmono ?_
    refine le_trans (eLpNorm_add_le
      (by norm_num : (1:ℝ≥0∞) ≤ ENNReal.ofReal 2)) ?_
    rw [hEn] at hsmE hlgE
    refine le_trans (add_le_add hsmE hlgE) ?_
    have hμ₁ : 0 ≤ C₁ * ((mstKappa P s : ℝ) + 1) * D * ((s : ℝ) + 1) ^ (-(δ * l)) := by positivity
    have hμ₂ : 0 ≤ C₂ * D * ((s : ℝ) + 1) ^ (-(δ * l)) := by positivity
    rw [← add_mul, ← ENNReal.ofReal_add hμ₁ hμ₂]
    refine mul_le_mul_of_nonneg_right (ENNReal.ofReal_le_ofReal ?_) (by positivity)
    exact le_trans harith (mul_le_mul_of_nonneg_right hCAleC (Real.rpow_nonneg (by positivity) _))
  · -- ================= crude case: s < S =================
    have hsS : s < S := not_le.mp hs
    have hCrudeLe : Ccrude s ≤ C * ((s : ℝ) + 1) ^ ((1 / 10 : ℝ) - δ * l) := by
      have hmem : s ∈ Finset.range S := Finset.mem_range.mpr hsS
      have hsingle : Ccrude s * ((s : ℝ) + 1) ^ ((δ * l) - (1 / 10 : ℝ)) + 1 ≤ Cbig := by
        rw [hCbigdef]
        exact Finset.single_le_sum
          (f := fun t : ℕ => Ccrude t * (((t : ℝ) + 1) ^ ((δ * l) - (1 / 10 : ℝ))) + 1)
          (fun t _ => by
            have h1 := hCcrude_nn t
            have h2 : (0:ℝ) ≤ ((t : ℝ) + 1) ^ ((δ * l) - (1 / 10 : ℝ)) :=
              Real.rpow_nonneg (by positivity) _
            exact add_nonneg (mul_nonneg h1 h2) zero_le_one) hmem
      have hCle : Ccrude s * ((s : ℝ) + 1) ^ ((δ * l) - (1 / 10 : ℝ)) ≤ C := by
        rw [hCdef]; linarith
      have hupos : (0:ℝ) < (s : ℝ) + 1 := by positivity
      have hmul : ((s : ℝ) + 1) ^ ((δ * l) - (1 / 10 : ℝ))
          * ((s : ℝ) + 1) ^ ((1 / 10 : ℝ) - δ * l) = 1 := by
        rw [← Real.rpow_add hupos,
          show (δ * l) - (1 / 10 : ℝ) + ((1 / 10 : ℝ) - δ * l) = 0 by ring, Real.rpow_zero]
      calc Ccrude s
          = Ccrude s * (((s : ℝ) + 1) ^ ((δ * l) - (1 / 10 : ℝ))
              * ((s : ℝ) + 1) ^ ((1 / 10 : ℝ) - δ * l)) := by rw [hmul, mul_one]
        _ = Ccrude s * ((s : ℝ) + 1) ^ ((δ * l) - (1 / 10 : ℝ))
              * ((s : ℝ) + 1) ^ ((1 / 10 : ℝ) - δ * l) := by ring
        _ ≤ C * ((s : ℝ) + 1) ^ ((1 / 10 : ℝ) - δ * l) :=
            mul_le_mul_of_nonneg_right hCle (Real.rpow_nonneg (by positivity) _)
    have hmax0 : ∀ (s' : ℕ) (g' : ℤ → ℂ) (hg' : Memℓp g' 2) (hA : ℕ → Lp ℂ ⊤ haarT),
        HasModel P P.natDegree χ (fun x : ℝ => η (-x)) s' hA →
        ∀ (hB : Lp ℂ ⊤ haarT), HasBump P.natDegree χ (fun x : ℝ => η (-x)) s' hB →
          ∫⁻ m : ℤ, (⨆ n : ℕ, ⨆ (_ : mstN₀' P s' ≤ n),
              ‖opMul (hA n) g' hg' m‖ₑ) ^ (2 : ℝ) ∂MeasureTheory.Measure.count
            ≤ ENNReal.ofReal (C₃ ^ 2)
              * (∫⁻ m : ℤ, ‖opMul hB g' hg' m‖ₑ ^ (2 : ℝ)
                  ∂MeasureTheory.Measure.count) :=
      fun s' g' hg' hA hAmod hB hBmod =>
        hmax s' (Nat.zero_le s') g' hg' hA hAmod hB hBmod
    have hCcrude_le : ((mstU l (s + 1)).card : ℝ)
        * (((mstN₀' P s : ℝ) + 1 + C₃) * M) ≤ Ccrude s := by
      rw [hCcrudedef]
    have hcrude := mst_level_crude P l χ η hη'cont hM0 hM hC₃pos hmax0 hνsml s
      (Ccrude s) hCcrude_le g
    exact le_trans hcrude
      (mul_le_mul_of_nonneg_right (ENNReal.ofReal_le_ofReal hCrudeLe) (by positivity))

end

end Work.BourgainPlan.Maximal
