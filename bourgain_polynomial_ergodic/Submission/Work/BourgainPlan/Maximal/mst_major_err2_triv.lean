import Mathlib
import Submission.Work.BourgainPlan.Maximal.mst_major_defs
import Submission.Work.BourgainPlan.Maximal.sigmaN_card_le
import Submission.Work.BourgainPlan.Maximal.sigmaN_nested
import Submission.Work.BourgainPlan.Maximal.mstU_annulus_tiling
import Submission.Work.BourgainPlan.Maximal.ellp_interpolation
import Submission.Work.BourgainPlan.IonescuWainger.norm_opMul_le_of_kernel
import Submission.Work.BourgainPlan.IonescuWainger.fourierCoeff_arcTranslate
import Submission.Work.BourgainPlan.Maximal.memLp_mst_symbols
import Submission.Work.BourgainPlan.Maximal.mstKernel_helpers
import Submission.Work.BourgainPlan.Maximal.mstProfBumpS_coeff
import Submission.Work.IonescuWainger.young_count_lp

namespace Work.BourgainPlan.Maximal

open MeasureTheory Finset
open scoped BigOperators ENNReal
open Work.BourgainPlan.IonescuWainger

local notation "haarT" => (AddCircle.haarAddCircle (T := 1))
local notation "Circ" => Work.BourgainPlan.IonescuWainger.Circle

set_option autoImplicit false
set_option maxHeartbeats 1000000

noncomputable section

/-! ## 1. The `ℓʳ` multiplier bound from an `ℓ¹` coefficient kernel -/

private lemma eLpNorm_count_eq_tsum_ofReal' (f : ℤ → ℂ) {q : ℝ} (hq : 0 < q) :
    eLpNorm f (ENNReal.ofReal q) Measure.count
      = (∑' n : ℤ, ENNReal.ofReal (‖f n‖ ^ q)) ^ (1 / q) := by
  rw [MeasureTheory.eLpNorm_eq_eLpNorm' (ENNReal.ofReal_ne_zero_iff.mpr hq) ENNReal.ofReal_ne_top
    (measurable_of_countable _).aestronglyMeasurable, MeasureTheory.eLpNorm', ENNReal.toReal_ofReal hq.le, MeasureTheory.lintegral_count]
  congr 1
  apply tsum_congr
  intro n
  rw [show ‖f n‖ₑ = ENNReal.ofReal ‖f n‖ by simp [enorm_eq_nnnorm],
    ENNReal.ofReal_rpow_of_nonneg (norm_nonneg _) hq.le]

private lemma ofReal_norm_tsum_le' (x : ℤ → ℂ) :
    ENNReal.ofReal ‖∑' i : ℤ, x i‖ ≤ ∑' i : ℤ, ENNReal.ofReal ‖x i‖ := by
  simpa using enorm_tsum_le_tsum_enorm (f := x)

theorem eLpNorm_opMul_le_kernel_tsum {Φ : Lp ℂ ⊤ haarT} {K : ℤ → ℂ}
    (hker : ∀ p : ℤ, ∫ ξ : Circ, (Φ : Circ → ℂ) ξ * star (fourier p ξ) ∂haarT = K p)
    (hK : Summable fun m : ℤ => ‖K m‖) {r : ℝ} (hr : 1 ≤ r) (f : ℤ → ℂ) (hf : Memℓp f 2) :
    eLpNorm (Work.BourgainPlan.IonescuWainger.opMul Φ f hf) (ENNReal.ofReal r) Measure.count
      ≤ ENNReal.ofReal (∑' m : ℤ, ‖K m‖)
        * eLpNorm f (ENNReal.ofReal r) Measure.count := by
  classical
  have hr0 : 0 < r := lt_of_lt_of_le zero_lt_one hr
  set w : ℤ → ENNReal := fun m => ENNReal.ofReal ‖K m‖ with hwdef
  set g : ℤ → ENNReal := fun k => ENNReal.ofReal ‖f k‖ with hgdef
  have hsumw : (∑' m : ℤ, w m) = ENNReal.ofReal (∑' m : ℤ, ‖K m‖) := by
    rw [← ENNReal.ofReal_tsum_of_nonneg (f := fun m : ℤ => ‖K m‖)
      (fun m => norm_nonneg _) hK]
  have hpoint : ∀ n : ℤ, ENNReal.ofReal
        (‖Work.BourgainPlan.IonescuWainger.opMul Φ f hf n‖ ^ r)
      ≤ (∑' k : ℤ, w k * g (n - k)) ^ r := by
    intro n
    have h1 : ENNReal.ofReal ‖Work.BourgainPlan.IonescuWainger.opMul Φ f hf n‖
        ≤ ∑' k : ℤ, g k * w (n - k) := by
      rw [Work.BourgainPlan.IonescuWainger.opMul_eq_tsum_kernel Φ f hf hker n]
      calc ENNReal.ofReal ‖∑' k : ℤ, f k * K (n - k)‖
          ≤ ∑' k : ℤ, ENNReal.ofReal ‖f k * K (n - k)‖ := ofReal_norm_tsum_le' _
        _ = ∑' k : ℤ, g k * w (n - k) := by
            refine tsum_congr fun k => ?_
            simp only [hwdef, hgdef]
            rw [norm_mul, ENNReal.ofReal_mul (norm_nonneg (f k))]
    have hswap : (∑' k : ℤ, g k * w (n - k)) = ∑' k : ℤ, w k * g (n - k) := by
      rw [← Equiv.tsum_eq (Equiv.subLeft n) (fun j : ℤ => w j * g (n - j))]
      refine tsum_congr fun k => ?_
      rw [Equiv.subLeft_apply]
      have hnk : n - (n - k) = k := by ring
      rw [hnk, mul_comm]
    calc ENNReal.ofReal (‖Work.BourgainPlan.IonescuWainger.opMul Φ f hf n‖ ^ r)
        = (ENNReal.ofReal ‖Work.BourgainPlan.IonescuWainger.opMul Φ f hf n‖) ^ r :=
          (ENNReal.ofReal_rpow_of_nonneg (norm_nonneg _) hr0.le).symm
      _ ≤ (∑' k : ℤ, g k * w (n - k)) ^ r := ENNReal.rpow_le_rpow h1 hr0.le
      _ = (∑' k : ℤ, w k * g (n - k)) ^ r := by rw [hswap]
  have hS1 : eLpNorm (Work.BourgainPlan.IonescuWainger.opMul Φ f hf)
        (ENNReal.ofReal r) Measure.count
      = (∑' n : ℤ, ENNReal.ofReal
          (‖Work.BourgainPlan.IonescuWainger.opMul Φ f hf n‖ ^ r)) ^ (1 / r) :=
    eLpNorm_count_eq_tsum_ofReal' _ hr0
  have hS2 : (∑' n : ℤ, ENNReal.ofReal (‖f n‖ ^ r)) = ∑' n : ℤ, g n ^ r := by
    refine tsum_congr fun n => ?_
    simp only [hgdef]
    exact (ENNReal.ofReal_rpow_of_nonneg (norm_nonneg _) hr0.le).symm
  have hstep : (∑' n : ℤ, ENNReal.ofReal
        (‖Work.BourgainPlan.IonescuWainger.opMul Φ f hf n‖ ^ r))
      ≤ (∑' k : ℤ, w k) ^ r * ∑' n : ℤ, ENNReal.ofReal (‖f n‖ ^ r) :=
    calc ∑' n : ℤ, ENNReal.ofReal
          (‖Work.BourgainPlan.IonescuWainger.opMul Φ f hf n‖ ^ r)
        ≤ ∑' n : ℤ, (∑' k : ℤ, w k * g (n - k)) ^ r := ENNReal.tsum_le_tsum hpoint
      _ ≤ (∑' k : ℤ, w k) ^ r * ∑' n : ℤ, g n ^ r :=
          Work.IonescuWainger.young_count_lp hr w g
      _ = (∑' k : ℤ, w k) ^ r * ∑' n : ℤ, ENNReal.ofReal (‖f n‖ ^ r) := by rw [← hS2]
  rw [hS1, eLpNorm_count_eq_tsum_ofReal' f hr0]
  calc (∑' n : ℤ, ENNReal.ofReal
        (‖Work.BourgainPlan.IonescuWainger.opMul Φ f hf n‖ ^ r)) ^ (1 / r)
      ≤ ((∑' k : ℤ, w k) ^ r * ∑' n : ℤ, ENNReal.ofReal (‖f n‖ ^ r)) ^ (1 / r) :=
        ENNReal.rpow_le_rpow hstep (one_div_pos.mpr hr0).le
    _ = (∑' k : ℤ, w k) * (∑' n : ℤ, ENNReal.ofReal (‖f n‖ ^ r)) ^ (1 / r) := by
        rw [ENNReal.mul_rpow_of_nonneg _ _ (one_div_pos.mpr hr0).le, ← ENNReal.rpow_mul,
          show r * (1 / r) = 1 by field_simp, ENNReal.rpow_one]
    _ = ENNReal.ofReal (∑' m : ℤ, ‖K m‖)
          * (∑' n : ℤ, ENNReal.ofReal (‖f n‖ ^ r)) ^ (1 / r) := by rw [hsumw]

/-! ## 2. The a.e. values of the second major-arc error class -/

private lemma eventuallyEq_finset_range_sum {α : Type*} [AddCommMonoid α]
    (n : ℕ) {f g : ℕ → Circ → α} (h : ∀ i ∈ Finset.range n, f i =ᵐ[haarT] g i) :
    (∑ i ∈ Finset.range n, f i) =ᵐ[haarT] (∑ i ∈ Finset.range n, g i) := by
  classical
  induction n with
  | zero => simp
  | succ n ih =>
      have hf : (∑ i ∈ Finset.range (n + 1), f i) = (∑ i ∈ Finset.range n, f i) + f n :=
        Finset.sum_range_succ f n
      have hg : (∑ i ∈ Finset.range (n + 1), g i) = (∑ i ∈ Finset.range n, g i) + g n :=
        Finset.sum_range_succ g n
      rw [hf, hg]
      have h1 : (∑ i ∈ Finset.range n, f i) =ᵐ[haarT] (∑ i ∈ Finset.range n, g i) :=
        ih (fun i hi => h i (Finset.mem_range.mpr
          (lt_trans (Finset.mem_range.mp hi) (Nat.lt_succ_self n))))
      have h2 : f n =ᵐ[haarT] g n := h n (Finset.mem_range.mpr (Nat.lt_succ_self n))
      exact h1.add h2

private lemma memLp_star_fourier (p : ℤ) :
    MemLp (fun ξ : Circ => star (fourier p ξ)) ⊤ haarT := by
  have h : MemLp (fun ξ : Circ => (fourier p) ξ) ⊤ haarT :=
    (Lp.memLp (fourierLp (T := 1) ⊤ p)).ae_eq (coeFn_fourierLp (T := 1) ⊤ p)
  exact h.star

theorem mstMajErr2Cls_ae (P : Polynomial ℤ) (l d : ℕ) (χ : ℝ) (η : ℝ → ℂ) (n : ℕ)
    (hν : MemLp (mstNu P l d χ η n) ⊤ haarT)
    (hνs : ∀ s : ℕ, MemLp (mstNuS P l d χ η n s) ⊤ haarT) :
    ((mstMajErr2Cls P l d χ η n hν hνs : Lp ℂ ⊤ haarT) : Circ → ℂ)
      =ᵐ[haarT] fun ξ => mstNu P l d χ η n ξ - ∑ s ∈ Finset.range n, mstNuS P l d χ η n s ξ := by
  have hsub := Lp.coeFn_sub (mstNuCls P l d χ η n hν) (mstNuSumCls P l d χ η n hνs)
  have hnu : ((mstNuCls P l d χ η n hν : Lp ℂ ⊤ haarT) : Circ → ℂ) =ᵐ[haarT] mstNu P l d χ η n :=
    MemLp.coeFn_toLp hν
  have hsum : ((mstNuSumCls P l d χ η n hνs : Lp ℂ ⊤ haarT) : Circ → ℂ)
      =ᵐ[haarT] (∑ s ∈ Finset.range n, ((hνs s).toLp (mstNuS P l d χ η n s) : Circ → ℂ)) :=
    Lp.coeFn_finsetSum (Finset.range n) (fun s : ℕ => (hνs s).toLp (mstNuS P l d χ η n s))
  have hsum2 : (∑ s ∈ Finset.range n, ((hνs s).toLp (mstNuS P l d χ η n s) : Circ → ℂ))
      =ᵐ[haarT] (∑ s ∈ Finset.range n, mstNuS P l d χ η n s) :=
    eventuallyEq_finset_range_sum n (fun s _ => MemLp.coeFn_toLp (hνs s))
  have heq : (fun ξ => (∑ s ∈ Finset.range n, mstNuS P l d χ η n s) ξ)
      = fun ξ => ∑ s ∈ Finset.range n, mstNuS P l d χ η n s ξ := by
    funext ξ; rw [Finset.sum_apply]
  unfold mstMajErr2Cls
  exact hsub.trans (hnu.sub (hsum.trans (hsum2.trans
    (Filter.Eventually.of_forall (fun ξ => congrFun heq ξ)))))

/-! ## 3. The assembly -/

private lemma summable_range_sum {ι : Type*} {f : ℕ → ι → ℝ} (n : ℕ)
    (h : ∀ s, Summable (f s)) : Summable (fun i => ∑ s ∈ Finset.range n, f s i) := by
  classical
  induction n with
  | zero => simpa using summable_zero
  | succ n ih =>
      have heq : (fun i => ∑ s ∈ Finset.range (n + 1), f s i)
          = fun i => (∑ s ∈ Finset.range n, f s i) + f n i := by
        funext i; rw [Finset.sum_range_succ]
      rw [heq]; exact ih.add (h n)

theorem mst_major_err2_triv_of_model (P : Polynomial ℤ) (l : ℕ) (hl : 1 ≤ l) {χ : ℝ}
    (η : ℝ → ℂ) {r : ℝ} (hr : 1 < r) {C : ℝ} (hCpos : 0 < C)
    (hCk : ∀ (N s : ℕ), 1 ≤ N → ∀ (Es : Finset Circ),
      Summable (fun p : ℤ => ‖∫ ξ : Circ,
          mstModelFn (fun β => star (mstG P β)) (fun ζ => star (mstProf P N ζ))
            (mstEta P.natDegree χ η s) Es ξ * star (fourier p ξ) ∂haarT‖)
      ∧ (∑' p : ℤ, ‖∫ ξ : Circ,
          mstModelFn (fun β => star (mstG P β)) (fun ζ => star (mstProf P N ζ))
            (mstEta P.natDegree χ η s) Es ξ * star (fourier p ξ) ∂haarT‖)
        ≤ C * (Es.card : ℝ))
    (hνml : ∀ n : ℕ, MemLp (mstNu P l P.natDegree χ η n) ⊤ haarT)
    (hνsml : ∀ n s : ℕ, MemLp (mstNuS P l P.natDegree χ η n s) ⊤ haarT) :
    ∃ C' : ℝ, 0 < C' ∧ ∀ n : ℕ, ∀ (f : ℤ → ℂ) (hf : Memℓp f 2),
        eLpNorm (Work.BourgainPlan.IonescuWainger.opMul
            (mstMajErr2Cls P l P.natDegree χ η n (hνml n) (hνsml n)) f hf)
            (ENNReal.ofReal r) Measure.count
          ≤ ENNReal.ofReal (C' * Real.exp (((n : ℝ) ^ l) ^ (mstRho l)))
              * eLpNorm f (ENNReal.ofReal r) Measure.count := by
  classical
  obtain ⟨N₁, hN₁⟩ := sigmaN_card_le (mstRho l) (by unfold mstRho; positivity)
  have hcardN : ∀ N : ℕ, N₁ ≤ N ^ l →
      ((mstU l N).card : ℝ) ≤ (⌈Real.exp (((N : ℝ) ^ l) ^ (mstRho l))⌉₊ : ℝ) := by
    intro N hN
    have h := hN₁ (N ^ l) hN
    refine Nat.cast_le.mpr ?_
    have heq : mstU l N
        = Work.BourgainPlan.IonescuWainger.sigmaLeFinset
            (Work.BourgainPlan.IonescuWainger.taoSetS (mstRho l) (N ^ l))
            (⌊2 / (mstRho l)⌋₊ + 1) := by
      rw [mstU_apply, iwSigma, iwK]
    rw [heq]
    have hcast : Real.exp (((N ^ l : ℕ) : ℝ) ^ (mstRho l))
        = Real.exp (((N : ℝ) ^ l) ^ (mstRho l)) := by
      rw [Nat.cast_pow]
    rw [hcast] at h
    exact h
  refine ⟨max (4 * C) (2 * C * ((mstU l N₁).card : ℝ)), ?_, ?_⟩
  · exact lt_of_lt_of_le (by positivity : (0 : ℝ) < 4 * C) (le_max_left _ _)
  · intro n f hf
    -- the model-kernel bounds at this `n`
    have hnu : Summable (fun p : ℤ => ‖∫ ξ : Circ,
            mstNu P l P.natDegree χ η n ξ * star (fourier p ξ) ∂haarT‖)
        ∧ (∑' p : ℤ, ‖∫ ξ : Circ,
            mstNu P l P.natDegree χ η n ξ * star (fourier p ξ) ∂haarT‖)
          ≤ C * ((mstU l n).card : ℝ) := by
      simpa only [mstNu] using hCk (2 ^ n) n Nat.one_le_two_pow (mstU l n)
    have hnuS : ∀ s : ℕ, Summable (fun p : ℤ => ‖∫ ξ : Circ,
            mstNuS P l P.natDegree χ η n s ξ * star (fourier p ξ) ∂haarT‖)
        ∧ (∑' p : ℤ, ‖∫ ξ : Circ,
            mstNuS P l P.natDegree χ η n s ξ * star (fourier p ξ) ∂haarT‖)
          ≤ C * ((mstLevel l (s + 1) \ mstLevel l s).card : ℝ) := by
      intro s
      simpa only [mstNuS] using hCk (2 ^ n) s Nat.one_le_two_pow (mstLevel l (s + 1) \ mstLevel l s)
    set Ψfn : Circ → ℂ := fun ξ => mstNu P l P.natDegree χ η n ξ
        - ∑ s ∈ Finset.range n, mstNuS P l P.natDegree χ η n s ξ with hΨfn
    set cls : Lp ℂ ⊤ haarT := mstMajErr2Cls P l P.natDegree χ η n (hνml n) (hνsml n) with hcls
    set K : ℤ → ℂ := fun p => ∫ ξ : Circ, (cls : Circ → ℂ) ξ * star (fourier p ξ) ∂haarT
      with hKdef
    have hae : (cls : Circ → ℂ) =ᵐ[haarT] Ψfn := by
      rw [hcls]; exact mstMajErr2Cls_ae P l P.natDegree χ η n (hνml n) (hνsml n)
    have hKeq : ∀ p : ℤ, K p = ∫ ξ : Circ, Ψfn ξ * star (fourier p ξ) ∂haarT := by
      intro p
      rw [hKdef]
      refine integral_congr_ae ?_
      filter_upwards [hae] with ξ hξ
      rw [hξ]
    -- the integrability of the individual pieces
    have haesm : ∀ p : ℤ, AEStronglyMeasurable (fun ξ : Circ => star (fourier p ξ)) haarT :=
      fun p => (memLp_star_fourier p).aestronglyMeasurable
    have hfbdd : ∀ p : ℤ, ∀ᵐ ξ ∂haarT, ‖(fun ξ : Circ => star (fourier p ξ)) ξ‖ ≤ 1 :=
      fun p => Filter.Eventually.of_forall (fun ξ => by
        rw [norm_star, Work.BourgainPlan.IonescuWainger.norm_fourier_apply'])
    have hIntP : ∀ p : ℤ, Integrable (fun ξ : Circ => mstNu P l P.natDegree χ η n ξ
        * star (fourier p ξ)) haarT := fun p =>
      ((hνml n).integrable le_top).mul_bdd (haesm p) (hfbdd p)
    have hIntS : ∀ (s : ℕ) (p : ℤ), Integrable (fun ξ : Circ => mstNuS P l P.natDegree χ η n s ξ
        * star (fourier p ξ)) haarT := fun s p =>
      ((hνsml n s).integrable le_top).mul_bdd (haesm p) (hfbdd p)
    -- the kernel of `Ψfn` splits into the model kernels
    have hKsplit : ∀ p : ℤ, (∫ ξ : Circ, Ψfn ξ * star (fourier p ξ) ∂haarT)
        = (∫ ξ : Circ, mstNu P l P.natDegree χ η n ξ * star (fourier p ξ) ∂haarT)
          - ∑ s ∈ Finset.range n, ∫ ξ : Circ,
              mstNuS P l P.natDegree χ η n s ξ * star (fourier p ξ) ∂haarT := by
      intro p
      have hsplit : (fun ξ : Circ => Ψfn ξ * star (fourier p ξ))
          = (fun ξ : Circ => mstNu P l P.natDegree χ η n ξ * star (fourier p ξ)
              - ∑ s ∈ Finset.range n,
                  mstNuS P l P.natDegree χ η n s ξ * star (fourier p ξ)) := by
        funext ξ
        simp only [hΨfn, Finset.sum_apply, sub_mul, Finset.sum_mul]
      rw [hsplit]
      rw [integral_sub (hIntP p) (integrable_finsetSum _ (fun s _ => hIntS s p)),
        integral_finsetSum _ (fun s _ => hIntS s p)]
    -- the pointwise bound on the kernel coefficients
    have hKle : ∀ p : ℤ, ‖K p‖
        ≤ ‖∫ ξ : Circ, mstNu P l P.natDegree χ η n ξ * star (fourier p ξ) ∂haarT‖
          + ∑ s ∈ Finset.range n, ‖∫ ξ : Circ,
              mstNuS P l P.natDegree χ η n s ξ * star (fourier p ξ) ∂haarT‖ := by
      intro p
      rw [hKeq p, hKsplit p]
      calc ‖(∫ ξ : Circ, mstNu P l P.natDegree χ η n ξ * star (fourier p ξ) ∂haarT)
            - ∑ s ∈ Finset.range n, ∫ ξ : Circ,
                mstNuS P l P.natDegree χ η n s ξ * star (fourier p ξ) ∂haarT‖
          ≤ ‖∫ ξ : Circ, mstNu P l P.natDegree χ η n ξ * star (fourier p ξ) ∂haarT‖
            + ‖∑ s ∈ Finset.range n, ∫ ξ : Circ,
                mstNuS P l P.natDegree χ η n s ξ * star (fourier p ξ) ∂haarT‖ :=
            norm_sub_le _ _
        _ ≤ ‖∫ ξ : Circ, mstNu P l P.natDegree χ η n ξ * star (fourier p ξ) ∂haarT‖
            + ∑ s ∈ Finset.range n, ‖∫ ξ : Circ,
                mstNuS P l P.natDegree χ η n s ξ * star (fourier p ξ) ∂haarT‖ := by
            gcongr
            exact norm_sum_le _ _
    -- summability and the sum bound
    have hBsum : Summable (fun p : ℤ => ∑ s ∈ Finset.range n,
        ‖∫ ξ : Circ, mstNuS P l P.natDegree χ η n s ξ * star (fourier p ξ) ∂haarT‖) :=
      summable_range_sum n (fun s => (hnuS s).1)
    have hKsm : Summable (fun p : ℤ => ‖K p‖) :=
      Summable.of_nonneg_of_le (fun p => norm_nonneg _) hKle (hnu.1.add hBsum)
    have hcard : (∑ s ∈ Finset.range n,
          ((mstLevel l (s + 1) \ mstLevel l s).card : ℝ)) ≤ ((mstU l n).card : ℝ) := by
      have h := sum_range_sdiff_of_mono (mstLevel l) (mstLevel_mono l)
        (fun _ : Circ => (1 : ℝ)) n
      simp only [Finset.sum_const, nsmul_eq_mul, mul_one, mstLevel_zero, Finset.sum_empty,
        sub_zero] at h
      have hun : ((mstLevel l n).card : ℝ) ≤ ((mstU l n).card : ℝ) := by
        rcases Nat.eq_zero_or_pos n with hn | hn
        · subst hn; simp
        · rw [show mstLevel l n = mstU l n by rw [mstLevel, if_neg (by omega)]]
      rw [h]
      simpa using hun
    have hKbd : (∑' p : ℤ, ‖K p‖) ≤ 2 * C * ((mstU l n).card : ℝ) := by
      have h1 : (∑' p : ℤ, ‖K p‖) ≤ ∑' p : ℤ,
          (‖∫ ξ : Circ, mstNu P l P.natDegree χ η n ξ * star (fourier p ξ) ∂haarT‖
            + ∑ s ∈ Finset.range n, ‖∫ ξ : Circ,
                mstNuS P l P.natDegree χ η n s ξ * star (fourier p ξ) ∂haarT‖) :=
        Summable.tsum_le_tsum hKle hKsm (hnu.1.add hBsum)
      have h2 : (∑' p : ℤ,
            (‖∫ ξ : Circ, mstNu P l P.natDegree χ η n ξ * star (fourier p ξ) ∂haarT‖
              + ∑ s ∈ Finset.range n, ‖∫ ξ : Circ,
                  mstNuS P l P.natDegree χ η n s ξ * star (fourier p ξ) ∂haarT‖))
          = (∑' p : ℤ, ‖∫ ξ : Circ,
                mstNu P l P.natDegree χ η n ξ * star (fourier p ξ) ∂haarT‖)
            + ∑ s ∈ Finset.range n, ∑' p : ℤ, ‖∫ ξ : Circ,
                mstNuS P l P.natDegree χ η n s ξ * star (fourier p ξ) ∂haarT‖ := by
        rw [Summable.tsum_add hnu.1 hBsum,
          Summable.tsum_finsetSum (fun s _ => (hnuS s).1)]
      calc (∑' p : ℤ, ‖K p‖)
          ≤ (∑' p : ℤ, ‖∫ ξ : Circ,
                mstNu P l P.natDegree χ η n ξ * star (fourier p ξ) ∂haarT‖)
            + ∑ s ∈ Finset.range n, ∑' p : ℤ, ‖∫ ξ : Circ,
                mstNuS P l P.natDegree χ η n s ξ * star (fourier p ξ) ∂haarT‖ :=
            h1.trans h2.le
        _ ≤ C * ((mstU l n).card : ℝ) + ∑ s ∈ Finset.range n,
              C * ((mstLevel l (s + 1) \ mstLevel l s).card : ℝ) :=
            add_le_add hnu.2 (Finset.sum_le_sum (fun s _ => (hnuS s).2))
        _ = C * ((mstU l n).card : ℝ) + C * ∑ s ∈ Finset.range n,
              ((mstLevel l (s + 1) \ mstLevel l s).card : ℝ) := by rw [Finset.mul_sum]
        _ ≤ C * ((mstU l n).card : ℝ) + C * ((mstU l n).card : ℝ) :=
            add_le_add le_rfl (mul_le_mul_of_nonneg_left hcard (le_of_lt hCpos))
        _ = 2 * C * ((mstU l n).card : ℝ) := by ring
    -- the `ℓʳ` multiplier bound
    have hstep := eLpNorm_opMul_le_kernel_tsum (Φ := cls) (K := K) (fun p => rfl) hKsm hr.le f hf
    refine hstep.trans ?_
    gcongr
    -- the arithmetic
    rcases lt_or_ge n N₁ with hn | hn
    · have hcardle : ((mstU l n).card : ℝ) ≤ ((mstU l N₁).card : ℝ) := by
        refine Nat.cast_le.mpr (Finset.card_le_card ?_)
        rw [mstU_apply, mstU_apply]
        exact sigmaN_nested (mstRho l) (Nat.pow_le_pow_left (by omega) l)
      have hexp1 : (1 : ℝ) ≤ Real.exp (((n : ℝ) ^ l) ^ (mstRho l)) :=
        Real.one_le_exp (by positivity)
      calc (∑' p : ℤ, ‖K p‖) ≤ 2 * C * ((mstU l n).card : ℝ) := hKbd
        _ ≤ 2 * C * ((mstU l N₁).card : ℝ) := by
            exact mul_le_mul_of_nonneg_left hcardle (by positivity)
        _ ≤ max (4 * C) (2 * C * ((mstU l N₁).card : ℝ)) := le_max_right _ _
        _ = max (4 * C) (2 * C * ((mstU l N₁).card : ℝ)) * 1 := (mul_one _).symm
        _ ≤ max (4 * C) (2 * C * ((mstU l N₁).card : ℝ))
              * Real.exp (((n : ℝ) ^ l) ^ (mstRho l)) :=
            mul_le_mul_of_nonneg_left hexp1 (le_trans (by positivity : (0:ℝ) ≤ 4 * C)
              (le_max_left _ _))
    · have h1 : N₁ ≤ n ^ l := by
        rcases Nat.eq_zero_or_pos n with h0 | hpos
        · subst h0
          rw [Nat.zero_pow (by omega : 0 < l)]
          exact hn
        · exact le_trans hn (Nat.le_self_pow (n := l) (show l ≠ 0 by omega) n)
      have hcardle : ((mstU l n).card : ℝ)
          ≤ 2 * Real.exp (((n : ℝ) ^ l) ^ (mstRho l)) := by
        have h2 := hcardN n h1
        have h4 : (⌈Real.exp (((n : ℝ) ^ l) ^ (mstRho l))⌉₊ : ℝ)
            ≤ Real.exp (((n : ℝ) ^ l) ^ (mstRho l)) + 1 := by
          have := Nat.ceil_lt_add_one (a := Real.exp (((n : ℝ) ^ l) ^ (mstRho l)))
            (le_of_lt (Real.exp_pos _))
          have h4' : (⌈Real.exp (((n : ℝ) ^ l) ^ (mstRho l))⌉₊ : ℝ)
              < Real.exp (((n : ℝ) ^ l) ^ (mstRho l)) + 1 := by exact_mod_cast this
          linarith
        have h5 : (1 : ℝ) ≤ Real.exp (((n : ℝ) ^ l) ^ (mstRho l)) :=
          Real.one_le_exp (by positivity)
        linarith
      have hexp1 : (1 : ℝ) ≤ Real.exp (((n : ℝ) ^ l) ^ (mstRho l)) :=
        Real.one_le_exp (by positivity)
      calc (∑' p : ℤ, ‖K p‖) ≤ 2 * C * ((mstU l n).card : ℝ) := hKbd
        _ ≤ 2 * C * (2 * Real.exp (((n : ℝ) ^ l) ^ (mstRho l))) :=
            mul_le_mul_of_nonneg_left hcardle (by positivity)
        _ = 4 * C * Real.exp (((n : ℝ) ^ l) ^ (mstRho l)) := by ring
        _ ≤ max (4 * C) (2 * C * ((mstU l N₁).card : ℝ))
              * Real.exp (((n : ℝ) ^ l) ^ (mstRho l)) := by
            refine mul_le_mul_of_nonneg_right (le_max_left _ _) (Real.exp_pos _).le

/-! ## 4. The model-sum kernel bound from the per-term coefficient bound -/

/-- **From the per-term `ℓ¹` coefficient bound to the `ℓ¹` kernel bound for a whole model symbol.**

Given the per-term bound `hterm` (the conclusion of
`Work.BourgainPlan.Maximal.mstProfBumpS_coeff`), the model symbol
`mstModelFn (star ∘ mstG P) (star ∘ mstProf P N) (mstEta d χ η s) Es` has summable `ℓ¹` coefficient
kernel of mass `≤ K * #Es`, for every profile scale `N ≥ 1`, level `s` and finite arc set `Es`.

Route: `mstModelFn_apply` expands the model symbol as `Σ_{β ∈ Es} star (mstG P β) * arcTranslate β h`
with `h = star (mstProf P N ·) * mstEta d χ η s`; the `p`-th coefficient of `arcTranslate β h` is
`star (fourier p β)` times that of `h` (`fourierCoeff_arcTranslate`); hence the `p`-th coefficient of
the model symbol is `(Σ_{β ∈ Es} star (mstG P β) * star (fourier p β)) * A_p` with `A_p` the `p`-th
coefficient of `h`, and `‖Σ_{β} star (mstG P β) * star (fourier p β)‖ ≤ #Es`
(`mstG_norm_le_one`, `norm_fourier_apply'`).  Summing in `p` with `hterm` gives the claim. -/
theorem mstModelFn_kernel_l1_of_term (P : Polynomial ℤ) (d : ℕ) (χ : ℝ) (η : ℝ → ℂ)
    (hd : 1 ≤ d) (hχ0 : 0 ≤ χ) (hχd : χ ≤ (d : ℝ))
    (hη2 : ∀ x : ℝ, 1 / 2 < |x| → η x = 0)
    (hcd : ∀ s : ℕ, ContDiff ℝ 2 (Work.BourgainPlan.Thm52.circleLift (mstEta d χ η s)))
    {K : ℝ}
    (hterm : ∀ (N s : ℕ), 1 ≤ N →
      Summable (fun m : ℤ => ‖∫ ξ : Circ,
          (star (mstProf P N ξ) * mstEta d χ η s ξ) * star (fourier m ξ) ∂haarT‖)
      ∧ (∑' m : ℤ, ‖∫ ξ : Circ,
          (star (mstProf P N ξ) * mstEta d χ η s ξ) * star (fourier m ξ) ∂haarT‖) ≤ K) :
    ∀ (N s : ℕ), 1 ≤ N → ∀ (Es : Finset Circ),
      Summable (fun p : ℤ => ‖∫ ξ : Circ,
          mstModelFn (fun β => star (mstG P β)) (fun ζ => star (mstProf P N ζ))
            (mstEta d χ η s) Es ξ * star (fourier p ξ) ∂haarT‖)
      ∧ (∑' p : ℤ, ‖∫ ξ : Circ,
          mstModelFn (fun β => star (mstG P β)) (fun ζ => star (mstProf P N ζ))
            (mstEta d χ η s) Es ξ * star (fourier p ξ) ∂haarT‖) ≤ K * (Es.card : ℝ) := by
  intro N s hN Es
  set h : Circ → ℂ := fun ξ => star (mstProf P N ξ) * mstEta d χ η s ξ with hhdef
  have hprofmem : MemLp (fun ξ : Circ => star (mstProf P N ξ)) ⊤ haarT :=
    ((memLp_mst_symbols P N 1 (fun _ : ℝ => 0) continuous_const).2.1).star
  have hetamem : MemLp (mstEta d χ η s) ⊤ haarT :=
    memLp_mstEta d χ η hη2 (hcd 0).continuous hd hχ0 hχd s
  have hhmem : MemLp h ⊤ haarT := by
    rw [hhdef]
    exact hprofmem.mul hetamem
  -- the model symbol is a sum of translates of `h`
  have hmodel : mstModelFn (fun β => star (mstG P β)) (fun ζ => star (mstProf P N ζ))
        (mstEta d χ η s) Es
      = fun ξ => ∑ β ∈ Es, star (mstG P β) * arcTranslate β h ξ := by
    funext ξ
    rw [mstModelFn_apply]
    refine Finset.sum_congr rfl fun β _ => ?_
    simp only [hhdef, arcTranslate]
  -- the coefficient identity
  have hKp : ∀ p : ℤ, (∫ ξ : Circ, mstModelFn (fun β => star (mstG P β))
        (fun ζ => star (mstProf P N ζ)) (mstEta d χ η s) Es ξ * star (fourier p ξ) ∂haarT)
      = (∑ β ∈ Es, star (mstG P β) * star (fourier p β))
        * (∫ ξ : Circ, h ξ * star (fourier p ξ) ∂haarT) := by
    intro p
    have hint : ∀ β ∈ Es, Integrable (fun ξ : Circ =>
        (star (mstG P β) * arcTranslate β h ξ) * star (fourier p ξ)) haarT := by
      intro β _
      have h1 : Integrable (fun ξ : Circ => star (mstG P β) * arcTranslate β h ξ) haarT :=
        ((memLp_arcTranslate hhmem β).const_mul (star (mstG P β))).integrable le_top
      exact h1.mul_bdd (memLp_star_fourier p).aestronglyMeasurable
        (Filter.Eventually.of_forall fun ξ => by
          rw [norm_star, Work.BourgainPlan.IonescuWainger.norm_fourier_apply'])
    have step1 : (∫ ξ : Circ, mstModelFn (fun β => star (mstG P β))
          (fun ζ => star (mstProf P N ζ)) (mstEta d χ η s) Es ξ * star (fourier p ξ) ∂haarT)
        = ∑ β ∈ Es, ∫ ξ : Circ,
            (star (mstG P β) * arcTranslate β h ξ) * star (fourier p ξ) ∂haarT := by
      rw [hmodel]
      rw [show (fun ξ : Circ => (∑ β ∈ Es, star (mstG P β) * arcTranslate β h ξ) * star (fourier p ξ))
          = (fun ξ : Circ => ∑ β ∈ Es,
              (star (mstG P β) * arcTranslate β h ξ) * star (fourier p ξ)) from by
            funext ξ; rw [Finset.sum_mul]]
      exact integral_finsetSum _ hint
    rw [step1]
    have hstep : ∀ β ∈ Es, (∫ ξ : Circ,
            (star (mstG P β) * arcTranslate β h ξ) * star (fourier p ξ) ∂haarT)
          = star (mstG P β) * (star (fourier p β)
              * ∫ ξ : Circ, h ξ * star (fourier p ξ) ∂haarT) := by
      intro β _
      rw [show (fun ξ : Circ => (star (mstG P β) * arcTranslate β h ξ) * star (fourier p ξ))
          = (fun ξ : Circ => star (mstG P β)
              * (arcTranslate β h ξ * star (fourier p ξ))) from by
            funext ξ; ring]
      rw [integral_const_mul, fourierCoeff_arcTranslate h hhmem β p]
    rw [Finset.sum_congr rfl hstep, Finset.sum_congr rfl
      (fun β (_ : β ∈ Es) => (mul_assoc _ _ _).symm), ← Finset.sum_mul]
  -- the bound
  obtain ⟨hsumA, hbdA⟩ := hterm N s hN
  have hAeq : (fun p : ℤ => ‖∫ ξ : Circ, h ξ * star (fourier p ξ) ∂haarT‖)
      = fun p : ℤ => ‖∫ ξ : Circ,
          (star (mstProf P N ξ) * mstEta d χ η s ξ) * star (fourier p ξ) ∂haarT‖ := by
    funext p
    congr 1
  have hBd : ∀ p : ℤ, ‖∫ ξ : Circ, mstModelFn (fun β => star (mstG P β))
        (fun ζ => star (mstProf P N ζ)) (mstEta d χ η s) Es ξ * star (fourier p ξ) ∂haarT‖
      ≤ (Es.card : ℝ) * ‖∫ ξ : Circ, h ξ * star (fourier p ξ) ∂haarT‖ := by
    intro p
    rw [hKp p, norm_mul]
    refine mul_le_mul_of_nonneg_right ?_ (norm_nonneg _)
    calc ‖∑ β ∈ Es, star (mstG P β) * star (fourier p β)‖
        ≤ ∑ β ∈ Es, ‖star (mstG P β) * star (fourier p β)‖ := norm_sum_le _ _
      _ ≤ ∑ _β ∈ Es, (1 : ℝ) := by
          refine Finset.sum_le_sum fun β _ => ?_
          rw [norm_mul, norm_star, norm_star,
            Work.BourgainPlan.IonescuWainger.norm_fourier_apply', mul_one]
          exact mstG_norm_le_one P β
      _ = (Es.card : ℝ) := by simp
  have hsumA' : Summable (fun p : ℤ => ‖∫ ξ : Circ, h ξ * star (fourier p ξ) ∂haarT‖) := by
    rw [hAeq]; exact hsumA
  have hbdA' : (∑' p : ℤ, ‖∫ ξ : Circ, h ξ * star (fourier p ξ) ∂haarT‖) ≤ K := by
    rw [hAeq]; exact hbdA
  have hKsm : Summable (fun p : ℤ => ‖∫ ξ : Circ, mstModelFn (fun β => star (mstG P β))
      (fun ζ => star (mstProf P N ζ)) (mstEta d χ η s) Es ξ * star (fourier p ξ) ∂haarT‖) :=
    Summable.of_nonneg_of_le (fun p => norm_nonneg _) hBd (hsumA'.mul_left _)
  refine ⟨hKsm, ?_⟩
  calc (∑' p : ℤ, ‖∫ ξ : Circ, mstModelFn (fun β => star (mstG P β))
            (fun ζ => star (mstProf P N ζ)) (mstEta d χ η s) Es ξ * star (fourier p ξ) ∂haarT‖)
      ≤ ∑' p : ℤ, (Es.card : ℝ) * ‖∫ ξ : Circ, h ξ * star (fourier p ξ) ∂haarT‖ :=
        Summable.tsum_le_tsum hBd hKsm (hsumA'.mul_left _)
    _ = (Es.card : ℝ) * ∑' p : ℤ, ‖∫ ξ : Circ, h ξ * star (fourier p ξ) ∂haarT‖ :=
        tsum_mul_left
    _ ≤ (Es.card : ℝ) * K := mul_le_mul_of_nonneg_left hbdA' (Nat.cast_nonneg _)
    _ = K * (Es.card : ℝ) := by ring

/-- Mirek-Stein-Trojan arXiv:1512.07518 §4.2 eq. (78): the trivial `ℓʳ` bound (all `r > 1`) for the second major-arc error `ν_{2^n} − Σ_{0 ≤ s < n} ν_{2^n}^s`, namely `‖opMul (mstMajErr2Cls …) f‖_{ℓʳ} ≤ C exp((n^l)^{1/(10l)}) ‖f‖_{ℓʳ}` uniformly in `n`.  Interpolating with the `ℓ²` gain (`mst_major_err2_l2`) at `r = (1+p)/2` yields `2^{−c n}`, summable in `n`.

Route: the a.e. symbol of `mstMajErr2Cls` is `Σ_{0 ≤ s < n} Σ_{β ∈ mstLevel l (s+1) ∖ mstLevel l s} star (G β · Φ_{2^n}(ξ−β)) (η_s − η_n)(ξ−β)` (with the `𝒰(0) := ∅` convention of `mstLevel`), a sum of at most `2 #(mstU l n)` terms.  Each term is an `ℓʳ`-multiplier of norm `O(1)` uniformly in `(n, s, β)`: the profile factor is an average of modulated bumps of `ℓʳ`-norm `O(1)` (`poly_dilation_lp_shift_const`), a modulation does not change the multiplier norm, and the bump factor obeys the Mikhlin conditions `hcd/hbdd/hder/hder2` (`mikhlin_multiplier_lift`, with the scaled-bump transfer), so its `ℓʳ`-norm is bounded by a constant depending only on `A`, `r`.  Hence the norm of the whole class is `≲ #(mstU l n) ≤ exp((n^l)^{1/(10l)})` (`sigmaN_card_le`); products of two bounded multipliers need `‖T₁T₂‖ ≤ ‖T₁‖‖T₂‖` on `ℓʳ`.  The bookkeeping between the class difference and this pointwise sum is `=ᵐ` reasoning (`MemLp.coeFn_toLp`, `Finset` sums of classes, `mstNu_apply`, `mstNuS_apply`, `Lp.coeFn_sub`). -/
theorem mst_major_err2_triv (P : Polynomial ℤ) (hd : 2 ≤ P.natDegree) (hc : 0 < P.leadingCoeff)
    {χ : ℝ} (hχ0 : 0 < χ) (hχ1 : χ < 1 / 10) (η : ℝ → ℂ) (M : ℝ) (hM : 0 ≤ M)
    (hηbd : ∀ x : ℝ, ‖η x‖ ≤ M)
    (hη1 : ∀ x : ℝ, |x| ≤ 1 / 4 → η x = 1) (hη2 : ∀ x : ℝ, 1 / 2 < |x| → η x = 0)
    (l : ℕ) (hl : 1 ≤ l) {r : ℝ} (hr : 1 < r)
    (A : ℝ) (hA : 0 < A)
    (hcd : ∀ n : ℕ, ContDiff ℝ 2 (Work.BourgainPlan.Thm52.circleLift
      (Work.BourgainPlan.Maximal.mstEta P.natDegree χ η n)))
    (hbdd : ∀ (n : ℕ) (x : ℝ), ‖Work.BourgainPlan.Thm52.circleLift
      (Work.BourgainPlan.Maximal.mstEta P.natDegree χ η n) x‖ ≤ A)
    (hder : ∀ (n : ℕ) (x : ℝ), |x| * ‖deriv (Work.BourgainPlan.Thm52.circleLift
      (Work.BourgainPlan.Maximal.mstEta P.natDegree χ η n)) x‖ ≤ A)
    (hder2 : ∀ (n : ℕ) (x : ℝ), |x| ^ 2 * ‖iteratedDeriv 2 (Work.BourgainPlan.Thm52.circleLift
      (Work.BourgainPlan.Maximal.mstEta P.natDegree χ η n)) x‖ ≤ A)
    (hνml : ∀ n : ℕ, MeasureTheory.MemLp
      (Work.BourgainPlan.Maximal.mstNu P l P.natDegree χ η n) ⊤
      (AddCircle.haarAddCircle (T := 1)))
    (hνsml : ∀ n s : ℕ, MeasureTheory.MemLp
      (Work.BourgainPlan.Maximal.mstNuS P l P.natDegree χ η n s) ⊤
      (AddCircle.haarAddCircle (T := 1))) :
    ∃ C : ℝ, 0 < C ∧ ∀ n : ℕ, ∀ (f : ℤ → ℂ) (hf : Memℓp f 2),
        MeasureTheory.eLpNorm (Work.BourgainPlan.IonescuWainger.opMul
            (Work.BourgainPlan.Maximal.mstMajErr2Cls P l P.natDegree χ η n (hνml n) (hνsml n))
            f hf) (ENNReal.ofReal r) MeasureTheory.Measure.count
          ≤ ENNReal.ofReal (C * Real.exp (((n : ℝ) ^ l) ^ (Work.BourgainPlan.Maximal.mstRho l)))
              * MeasureTheory.eLpNorm f (ENNReal.ofReal r) MeasureTheory.Measure.count := by
  -- the per-term `ℓ¹` coefficient bound (`mstProfBumpS_coeff`), then the model-sum kernel bound
  have hcd0 : ContDiff ℝ 2 (Work.BourgainPlan.Thm52.circleLift
      (mstEta P.natDegree χ η 0)) := hcd 0
  obtain ⟨K, hKpos, hK⟩ :=
    mstProfBumpS_coeff P P.natDegree χ η M hM (by
      have : (2 : ℝ) ≤ (P.natDegree : ℝ) := by exact_mod_cast hd
      linarith) hηbd hη2 hcd0
  refine mst_major_err2_triv_of_model P l hl η hr hKpos
    (mstModelFn_kernel_l1_of_term P P.natDegree χ η (by omega) (le_of_lt hχ0) (by
      have : (2 : ℝ) ≤ (P.natDegree : ℝ) := by exact_mod_cast hd
      linarith) hη2 hcd hK) hνml hνsml

end

end Work.BourgainPlan.Maximal
