import Mathlib
import Submission.Work.LinnikAreas.TuranOther.Defs
import Submission.Work.LinnikAreas.TuranOther.orderZeta_eq_orderLambda_add_invGammaR
import Submission.Work.LinnikAreas.TuranOther.orderInvGammaR_eq_indicator
import Submission.Work.LinnikAreas.TuranOther.levelFactorZeroSumSummable
import Submission.Work.LinnikAreas.TuranOther.lFunction_eq_completed_mul_invGamma
import Submission.Work.LinnikAreas.OtherCharRepel.LFunction_eq_primitiveCharacter_mul
import Submission.Work.LinnikAreas.P3Rect.Work_LinnikAreas_TuranOther_lFunctionOrderAddInvGammaR
import Submission.Work.LinnikAreas.P3Rect.Work_LinnikAreas_TuranOther_pfUncompleted
import Submission.Work.LinnikAreas.P3Rect.Work_LinnikAreas_DhExplicit_zeroSumKMultBound
import Submission.Work.LinnikAreas.FarRepel.zeroSumInvSqBound
import Submission.Work.LinnikAreas.turanAux2.completedZetaInvSq
import Submission.Work.LinnikAreas.turanAux2.gammaRShiftInvSq
import Submission.Work.LinnikAreas.TwMass.latticeInvSqSumLe
import Submission.Work.LinnikAreas.turanAux2.completedLInvSq
import Submission.Work.LinnikAreas.turanAux2.completedLFunction_primitiveFactor
import Submission.Work.LinnikAreas.turanAux2.notAnalyticLFunctionTrivChar

open scoped Classical BigOperators Topology
open Filter
open DirichletCharacter

noncomputable section

namespace Work.LinnikAreas.turanAux2

open Work.LinnikAreas.TuranOther (multZeta multL)

/-- For two functions analytic at a point, the vanishing order of the product is at most the sum
of the vanishing orders. -/
lemma analyticOrderNatAt_mul_le {f g : ℂ → ℂ} {z : ℂ} (hf : AnalyticAt ℂ f z)
    (hg : AnalyticAt ℂ g z) :
    analyticOrderNatAt (f * g) z ≤ analyticOrderNatAt f z + analyticOrderNatAt g z := by
  have h : analyticOrderNatAt (f * g) z
      ≤ (analyticOrderAt f z).toNat + (analyticOrderAt g z).toNat := by
    rw [analyticOrderNatAt, analyticOrderAt_mul hf hg]
    rcases eq_or_ne (analyticOrderAt f z) ⊤ with ha | ha
    · rw [ha]; simp
    rcases eq_or_ne (analyticOrderAt g z) ⊤ with hb | hb
    · rw [hb]; simp
    rw [ENat.toNat_add ha hb]
  calc analyticOrderNatAt (f * g) z
      ≤ (analyticOrderAt f z).toNat + (analyticOrderAt g z).toNat := h
    _ = analyticOrderNatAt f z + analyticOrderNatAt g z := rfl

/-- `riemannZeta` is analytic away from its pole at `1`. -/
lemma analyticAt_riemannZeta_off_one {u : ℂ} (hu : u ≠ 1) : AnalyticAt ℂ riemannZeta u := by
  rw [Complex.analyticAt_iff_eventually_differentiableAt]
  filter_upwards [eventually_ne_nhds hu] with z hz
  exact differentiableAt_riemannZeta hz

/-- The vanishing order of `ζ` at `u` is dominated by the orders of the completed zeta function
`Λ` and of the inverse archimedean factor `1/Γ_ℝ`. -/
lemma multZeta_le_lambda_add_invGammaR (u : ℂ) :
    multZeta u ≤ analyticOrderNatAt completedRiemannZeta u
      + analyticOrderNatAt (fun s : ℂ => (Complex.Gammaℝ s)⁻¹) u := by
  rcases eq_or_ne u 0 with rfl | hu
  · have h0 : analyticOrderNatAt riemannZeta (0 : ℂ) = 0 :=
      Work.LinnikAreas.TuranOther.analyticOrderNatAt_eq_zero_of_analyticAt_ne_zero
        (analyticAt_riemannZeta_off_one (by norm_num))
        (by rw [riemannZeta_zero]; norm_num)
    simp only [multZeta, h0]
    exact Nat.zero_le _
  · simp only [multZeta]
    rw [Work.LinnikAreas.TuranOther.orderZeta_eq_orderLambda_add_invGammaR u hu]

/-- A single level factor `s ↦ 1 - c·p^{-s}` is entire. -/
lemma levelFactorDiff' {p : ℕ} (hp : p ≠ 0) (c : ℂ) :
    Differentiable ℂ (fun s : ℂ => 1 - c * (p : ℂ) ^ (-s)) := by
  rw [show (fun s : ℂ => 1 - c * (p : ℂ) ^ (-s))
      = fun s : ℂ => 1 - c * Complex.exp (Complex.log (p : ℂ) * (-s)) from by
    funext s
    rw [Complex.cpow_def_of_ne_zero (Nat.cast_ne_zero.mpr hp)]]
  fun_prop

/-- The level-correction product with coefficients `1` is entire. -/
lemma levelProdBareDiff (q : ℕ) :
    Differentiable ℂ (fun s : ℂ => ∏ p ∈ q.primeFactors, (1 - (p : ℂ) ^ (-s))) :=
  Work.LinnikAreas.TuranOther.diff_finsetProd q.primeFactors _
    (fun p hp => by
      have h := levelFactorDiff' (Nat.prime_of_mem_primeFactors hp).ne_zero (1 : ℂ)
      simpa using h)

/-- The vanishing order of the constant function `1` is zero everywhere. -/
lemma analyticOrderNatAt_const_one (u : ℂ) :
    analyticOrderNatAt (fun _ : ℂ => (1 : ℂ)) u = 0 := by
  have h : analyticOrderAt (fun _ : ℂ => (1 : ℂ)) u = 0 :=
    analyticOrderAt_eq_zero.mpr (Or.inr one_ne_zero)
  simp [analyticOrderNatAt, h]

/-- A finite product of functions analytic at `u` is analytic at `u`. -/
lemma analyticAt_finsetProd {s : Finset ℕ} {f : ℕ → ℂ → ℂ} {u : ℂ}
    (hf : ∀ p ∈ s, AnalyticAt ℂ (f p) u) :
    AnalyticAt ℂ (s.prod f) u := by
  induction s using Finset.induction_on with
  | empty =>
      have h : ((∅ : Finset ℕ).prod f : ℂ → ℂ) = fun _ : ℂ => (1 : ℂ) := by
        funext z; simp
      rw [h]
      exact analyticAt_const
  | insert a s ha ih =>
      have h1 : AnalyticAt ℂ (f a) u := hf a (Finset.mem_insert_self a s)
      have h2 : AnalyticAt ℂ (s.prod f) u := ih (fun p hp => hf p (Finset.mem_insert_of_mem hp))
      rw [Finset.prod_insert ha]
      exact h1.mul h2

/-- The vanishing order of a finite product of functions analytic at `u` is at most the sum of
the vanishing orders of the factors. -/
lemma ord_finsetProd_le (s : Finset ℕ) (f : ℕ → ℂ → ℂ) (u : ℂ)
    (hf : ∀ p ∈ s, AnalyticAt ℂ (f p) u) :
    analyticOrderNatAt (s.prod f) u ≤ ∑ p ∈ s, analyticOrderNatAt (f p) u := by
  induction s using Finset.induction_on with
  | empty =>
      have h : ((∅ : Finset ℕ).prod f : ℂ → ℂ) = fun _ : ℂ => (1 : ℂ) := by
        funext z; simp
      rw [h]
      simpa using le_of_eq (analyticOrderNatAt_const_one u)
  | insert a s ha ih =>
      have h1 : AnalyticAt ℂ (f a) u := hf a (Finset.mem_insert_self a s)
      have h2 : AnalyticAt ℂ (s.prod f) u :=
        analyticAt_finsetProd (fun p hp => hf p (Finset.mem_insert_of_mem hp))
      have h3 : analyticOrderNatAt (s.prod f) u ≤ ∑ p ∈ s, analyticOrderNatAt (f p) u :=
        ih (fun p hp => hf p (Finset.mem_insert_of_mem hp))
      have h4 := analyticOrderNatAt_mul_le (f := f a) (g := s.prod f) h1 h2
      rw [Finset.prod_insert ha, Finset.sum_insert ha]
      linarith only [h3, h4]

/-- Summability and the total sum of a finite sum of summable families. -/
lemma summable_finset_sum_tsum {ι : Type*} (s : Finset ι) (g : ι → ℂ → ℝ)
    (hg : ∀ i ∈ s, Summable (g i)) :
    Summable (fun u : ℂ => ∑ i ∈ s, g i u) ∧
      (∑' u : ℂ, ∑ i ∈ s, g i u) = ∑ i ∈ s, ∑' u : ℂ, g i u := by
  classical
  induction s using Finset.induction_on with
  | empty =>
      refine ⟨?_, ?_⟩
      · have h : (fun u : ℂ => ∑ i ∈ (∅ : Finset ι), g i u) = fun _ : ℂ => (0:ℝ) := by
          funext u; simp
        rw [h]; exact summable_zero
      · have h : (fun u : ℂ => ∑ i ∈ (∅ : Finset ι), g i u) = fun _ : ℂ => (0:ℝ) := by
          funext u; simp
        rw [h, tsum_zero]; simp
  | insert a s ha ih =>
      have h1 : Summable (g a) := hg a (Finset.mem_insert_self a s)
      have h2 : Summable (fun u : ℂ => ∑ i ∈ s, g i u) :=
        (ih (fun i hi => hg i (Finset.mem_insert_of_mem hi))).1
      have hEq : (fun u : ℂ => ∑ i ∈ insert a s, g i u)
          = fun u : ℂ => g a u + ∑ i ∈ s, g i u := by
        funext u; rw [Finset.sum_insert ha]
      rw [hEq]
      refine ⟨h1.add h2, ?_⟩
      rw [Summable.tsum_add h1 h2, (ih (fun i hi => hg i (Finset.mem_insert_of_mem hi))).2,
        Finset.sum_insert ha]

/-- For the principal character mod `q`, the vanishing order of `L(·,1_q)` is at most that of `ζ`
plus that of the level-correction product `∏_{p ∣ q} (1 - p^{-s})`. -/
lemma multL_one_le (q : ℕ) [NeZero q] (u : ℂ) :
    multL (1 : DirichletCharacter ℂ q) u ≤ multZeta u
      + analyticOrderNatAt (fun s : ℂ => ∏ p ∈ q.primeFactors, (1 - (p : ℂ) ^ (-s))) u := by
  rcases eq_or_ne u 1 with rfl | hu1
  · rw [multL, analyticOrderNatAt_of_not_analyticAt (notAnalyticLFunctionTrivChar q)]
    exact Nat.zero_le _
  · have hev : DirichletCharacter.LFunction (1 : DirichletCharacter ℂ q) =ᶠ[𝓝 u]
        fun s : ℂ => (∏ p ∈ q.primeFactors, (1 - (p : ℂ) ^ (-s))) * riemannZeta s := by
      filter_upwards [eventually_ne_nhds hu1] with s hs
      exact DirichletCharacter.LFunctionTrivChar_eq_mul_riemannZeta hs
    have hcongr : analyticOrderNatAt (DirichletCharacter.LFunction (1 : DirichletCharacter ℂ q)) u
        = analyticOrderNatAt (fun s : ℂ =>
            (∏ p ∈ q.primeFactors, (1 - (p : ℂ) ^ (-s))) * riemannZeta s) u := by
      simp only [analyticOrderNatAt]
      rw [analyticOrderAt_congr hev]
    have h2 := analyticOrderNatAt_mul_le
      (f := fun s : ℂ => ∏ p ∈ q.primeFactors, (1 - (p : ℂ) ^ (-s))) (g := riemannZeta) (z := u)
      ((levelProdBareDiff q).analyticAt u) (analyticAt_riemannZeta_off_one hu1)
    simp only [multL]
    calc analyticOrderNatAt (DirichletCharacter.LFunction (1 : DirichletCharacter ℂ q)) u
        = analyticOrderNatAt (fun s : ℂ =>
            (∏ p ∈ q.primeFactors, (1 - (p : ℂ) ^ (-s))) * riemannZeta s) u := hcongr
      _ ≤ analyticOrderNatAt (fun s : ℂ => ∏ p ∈ q.primeFactors, (1 - (p : ℂ) ^ (-s))) u
            + analyticOrderNatAt riemannZeta u := h2
      _ = multZeta u
            + analyticOrderNatAt (fun s : ℂ => ∏ p ∈ q.primeFactors, (1 - (p : ℂ) ^ (-s))) u := by
          simp only [multZeta]
          exact Nat.add_comm _ _

/-- Reindexing of an `ℝ`-valued sum supported on the range of an injective `ℤ`-indexed
family. -/
lemma tsum_eq_tsum_of_supported_real {f : ℂ → ℝ} {φ : ℤ → ℂ} (hφ : Function.Injective φ)
    (hsupp : ∀ u : ℂ, (∀ n : ℤ, u ≠ φ n) → f u = 0) (hf : Summable fun n : ℤ => f (φ n)) :
    Summable f ∧ (∑' u : ℂ, f u) = ∑' n : ℤ, f (φ n) := by
  have hsupp' : ∀ u : ℂ, u ∉ Set.range φ → f u = 0 := by
    intro u hu
    exact hsupp u fun n h => hu ⟨n, h.symm⟩
  have hsupp'' : Function.support f ⊆ Set.range φ := fun u hu =>
    by_contra fun h => hu (hsupp' u h)
  exact ⟨(hφ.summable_iff hsupp').mp hf, (hφ.tsum_eq hsupp'').symm⟩

/-- The coordinates of the `n`-th lattice zero of a level factor: real part `0` and imaginary
part `Im(lvlRoot p c) + n·(2π/log p)`. -/
lemma lvlZero_re_im {p : ℕ} (hp : p.Prime) {c : ℂ} (hc : ‖c‖ = 1) (n : ℤ) :
    (Work.LinnikAreas.TuranOther.lvlZero p c n).re = 0 ∧
      (Work.LinnikAreas.TuranOther.lvlZero p c n).im
        = (Work.LinnikAreas.TuranOther.lvlRoot p c).im
          + (n : ℝ) * (2 * Real.pi / Work.LinnikAreas.TuranOther.lvlL p) := by
  have hP : Work.LinnikAreas.TuranOther.lvlPeriod p
      = (((2 * Real.pi / Work.LinnikAreas.TuranOther.lvlL p : ℝ)) : ℂ) * Complex.I := by
    rw [Work.LinnikAreas.TuranOther.lvlPeriod]
    push_cast
    field_simp
  have key : Work.LinnikAreas.TuranOther.lvlZero p c n
      = Work.LinnikAreas.TuranOther.lvlRoot p c
        + ((((n : ℝ) * (2 * Real.pi / Work.LinnikAreas.TuranOther.lvlL p) : ℝ)) : ℂ)
            * Complex.I := by
    rw [Work.LinnikAreas.TuranOther.lvlZero, hP]
    push_cast
    ring
  constructor
  · rw [key, Complex.add_re, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
      Complex.I_re, Complex.I_im, Work.LinnikAreas.TuranOther.lvlRoot_re hc]
    ring
  · rw [key, Complex.add_im, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im,
      Complex.I_re, Complex.I_im]
    ring

/-- The vanishing order of `lvlE p c` is `1` at every lattice point `lvlZero p c n` and `0`
everywhere else. -/
lemma lvlE_order_support {p : ℕ} (hp : p.Prime) {c : ℂ} (hc : ‖c‖ = 1) :
    (∀ n : ℤ, analyticOrderNatAt (Work.LinnikAreas.TuranOther.lvlE p c)
        (Work.LinnikAreas.TuranOther.lvlZero p c n) = 1) ∧
      (∀ u : ℂ, (∀ n : ℤ, u ≠ Work.LinnikAreas.TuranOther.lvlZero p c n) →
        analyticOrderNatAt (Work.LinnikAreas.TuranOther.lvlE p c) u = 0) := by
  refine ⟨fun n => Work.LinnikAreas.TuranOther.analyticOrderNatAt_lvlE_lvlZero hp c hc n, ?_⟩
  intro u hu
  have hne : Work.LinnikAreas.TuranOther.lvlE p c u ≠ 0 := by
    intro h
    obtain ⟨n, hn⟩ := (Work.LinnikAreas.TuranOther.lvlE_eq_zero_iff hp hc u).mp h
    exact hu n hn
  have h : analyticOrderAt (Work.LinnikAreas.TuranOther.lvlE p c) u = 0 :=
    analyticOrderAt_eq_zero.mpr (Or.inr hne)
  simp [analyticOrderNatAt, h]

/-- The squared distance from `w` to the `n`-th lattice zero of a level factor. -/
lemma lvlZero_normSq {p : ℕ} (hp : p.Prime) {c : ℂ} (hc : ‖c‖ = 1) (w : ℂ) (n : ℤ) :
    ‖w - Work.LinnikAreas.TuranOther.lvlZero p c n‖ ^ 2
      = w.re ^ 2 + ((w.im - (Work.LinnikAreas.TuranOther.lvlRoot p c).im)
          - (n : ℝ) * (2 * Real.pi / Work.LinnikAreas.TuranOther.lvlL p)) ^ 2 := by
  obtain ⟨hre, him⟩ := lvlZero_re_im hp hc n
  have h1 : (w - Work.LinnikAreas.TuranOther.lvlZero p c n).re = w.re := by
    simp [Complex.sub_re, hre]
  have h2 : (w - Work.LinnikAreas.TuranOther.lvlZero p c n).im
      = (w.im - (Work.LinnikAreas.TuranOther.lvlRoot p c).im)
          - (n : ℝ) * (2 * Real.pi / Work.LinnikAreas.TuranOther.lvlL p) := by
    rw [Complex.sub_im, him]; ring
  rw [Complex.sq_norm, Complex.normSq_apply, h1, h2]
  ring

/-- **Mass of a single level factor** `1 - c·p^{-s}` with `‖c‖ = 1`: the inverse-square
multiplicity-weighted zero sum is `O(1 + log p)`, uniformly in `w` with `Re w ≥ 3/2`. -/
lemma lvlEMass :
    ∃ C : ℝ, 0 < C ∧ ∀ {p : ℕ} (hp : p.Prime) {c : ℂ}, ‖c‖ = 1 →
      ∀ (w : ℂ), (3 / 2 : ℝ) ≤ w.re →
        Summable (fun u : ℂ =>
            (analyticOrderNatAt (Work.LinnikAreas.TuranOther.lvlE p c) u : ℝ) / ‖w - u‖ ^ 2) ∧
          (∑' u : ℂ,
            (analyticOrderNatAt (Work.LinnikAreas.TuranOther.lvlE p c) u : ℝ) / ‖w - u‖ ^ 2)
            ≤ C * (1 + Real.log p) := by
  obtain ⟨C1, hC1pos, hC1⟩ := Work.LinnikAreas.TwMass.latticeInvSqSumLe
  refine ⟨C1 + 1, by linarith only [hC1pos], ?_⟩
  intro p hp c hc w hw
  obtain ⟨hord1, hord0⟩ := lvlE_order_support hp hc
  have hφinj : Function.Injective (Work.LinnikAreas.TuranOther.lvlZero p c) :=
    Work.LinnikAreas.TuranOther.lvlZero_injective (Work.LinnikAreas.TuranOther.lvlL_ne_zero hp) c
  set h : ℝ := 2 * Real.pi / Work.LinnikAreas.TuranOther.lvlL p with hhdef
  have hhpos : 0 < h := by
    rw [hhdef]
    exact div_pos (by positivity) (Work.LinnikAreas.TuranOther.lvlL_pos hp)
  set B : ℝ := w.im - (Work.LinnikAreas.TuranOther.lvlRoot p c).im with hBdef
  have hA1 : 1 ≤ w.re ^ 2 := by nlinarith only [hw]
  have hkey : ∀ n : ℤ, ‖w - Work.LinnikAreas.TuranOther.lvlZero p c n‖ ^ 2
      = w.re ^ 2 + (B - (n : ℝ) * h) ^ 2 := by
    intro n
    rw [lvlZero_normSq hp hc w n, hBdef, hhdef]
  have hApos : 0 < w.re ^ 2 := by positivity
  obtain ⟨hsumL, hbndL⟩ := hC1 (w.re ^ 2) B h hApos hhpos
  have hsqrt1 : 1 ≤ Real.sqrt (w.re ^ 2) := by
    rw [Real.sqrt_sq_eq_abs]
    have habs : |w.re| ^ 2 = w.re ^ 2 := sq_abs w.re
    nlinarith only [hA1, abs_nonneg w.re, habs, hw]
  have hsqrtle : 1 / (h * Real.sqrt (w.re ^ 2)) ≤ 1 / h := by
    refine one_div_le_one_div_of_le hhpos ?_
    calc h = h * 1 := (mul_one h).symm
      _ ≤ h * Real.sqrt (w.re ^ 2) := by
          exact mul_le_mul_of_nonneg_left hsqrt1 hhpos.le
  have hsumφ : Summable (fun n : ℤ =>
      ((analyticOrderNatAt (Work.LinnikAreas.TuranOther.lvlE p c)
          (Work.LinnikAreas.TuranOther.lvlZero p c n) : ℕ) : ℝ)
        / ‖w - Work.LinnikAreas.TuranOther.lvlZero p c n‖ ^ 2) := by
    refine hsumL.congr (fun n => ?_)
    rw [hord1 n, hkey n]
    norm_num
  have hsupp : ∀ u : ℂ, (∀ n : ℤ, u ≠ Work.LinnikAreas.TuranOther.lvlZero p c n) →
      (fun u : ℂ =>
        ((analyticOrderNatAt (Work.LinnikAreas.TuranOther.lvlE p c) u : ℕ) : ℝ) / ‖w - u‖ ^ 2)
        u = 0 := by
    intro u hu
    have h0 := hord0 u hu
    show ((analyticOrderNatAt (Work.LinnikAreas.TuranOther.lvlE p c) u : ℕ) : ℝ) / ‖w - u‖ ^ 2 = 0
    rw [h0]; norm_num
  obtain ⟨hsum, htsum⟩ :=
    tsum_eq_tsum_of_supported_real hφinj hsupp hsumφ
  refine ⟨hsum, ?_⟩
  rw [htsum]
  have h1 : (∑' n : ℤ, ((analyticOrderNatAt (Work.LinnikAreas.TuranOther.lvlE p c)
          (Work.LinnikAreas.TuranOther.lvlZero p c n) : ℕ) : ℝ)
        / ‖w - Work.LinnikAreas.TuranOther.lvlZero p c n‖ ^ 2)
      = ∑' n : ℤ, (1 : ℝ) / (w.re ^ 2 + (B - (n : ℝ) * h) ^ 2) := by
    apply tsum_congr
    intro n
    rw [hord1 n, hkey n]
    norm_num
  rw [h1]
  refine hbndL.trans ?_
  have hlogp : 0 ≤ Real.log p :=
    Real.log_nonneg (by exact_mod_cast hp.one_le)
  have hAinv : (1 : ℝ) / w.re ^ 2 ≤ 1 := by
    rw [div_le_one (by positivity)]; linarith only [hA1]
  have h1h : (1 : ℝ) / h ≤ Real.log p := by
    rw [hhdef, Work.LinnikAreas.TuranOther.lvlL, one_div_div,
      div_le_iff₀ (by positivity : (0 : ℝ) < 2 * Real.pi)]
    nlinarith only [Real.pi_gt_three, hlogp]
  calc C1 * (1 / w.re ^ 2 + 1 / (h * Real.sqrt (w.re ^ 2)))
      ≤ C1 * (1 / w.re ^ 2 + 1 / h) :=
        mul_le_mul_of_nonneg_left (by linarith only [hsqrtle]) hC1pos.le
    _ ≤ C1 * (1 + Real.log p) :=
        mul_le_mul_of_nonneg_left (by linarith only [hAinv, h1h]) hC1pos.le
    _ ≤ (C1 + 1) * (1 + Real.log p) := by linarith only [hC1pos, hlogp]

/-- **Mass of a level-correction product** `∏_{p ∣ q} (1 - χ(p) p^{-s})`: the inverse-square
multiplicity-weighted zero sum is `O(log q)`, uniformly in the modulus `d` of `χ` and in
`w` with `Re w ≥ 3/2`. -/
lemma levelProdMass :
    ∃ C : ℝ, 0 < C ∧ ∀ (q d : ℕ) [NeZero d] (χ : DirichletCharacter ℂ d) (w : ℂ),
      (3 / 2 : ℝ) ≤ w.re →
      Summable (fun u : ℂ =>
          (analyticOrderNatAt (fun s : ℂ => ∏ p ∈ q.primeFactors,
            (1 - χ (p : ZMod d) * (p : ℂ) ^ (-s))) u : ℝ) / ‖w - u‖ ^ 2) ∧
        (∑' u : ℂ,
          (analyticOrderNatAt (fun s : ℂ => ∏ p ∈ q.primeFactors,
            (1 - χ (p : ZMod d) * (p : ℂ) ^ (-s))) u : ℝ) / ‖w - u‖ ^ 2)
          ≤ C * (Real.log (q : ℝ) + 1) := by
  obtain ⟨C0, hC0pos, hC0⟩ := lvlEMass
  refine ⟨3 * C0 + 1, by linarith only [hC0pos], ?_⟩
  intro q d _inst χ w hw
  by_cases hq : q = 0
  · subst hq
    have hz : (fun u : ℂ => (analyticOrderNatAt (fun s : ℂ => ∏ p ∈ (0:ℕ).primeFactors,
          (1 - χ (p : ZMod d) * (p : ℂ) ^ (-s))) u : ℝ) / ‖w - u‖ ^ 2)
        = fun _ : ℂ => 0 := by
      funext u
      simp [analyticOrderNatAt_const_one]
    rw [hz]
    refine ⟨summable_zero, ?_⟩
    rw [tsum_zero]
    have h0 : (0:ℝ) ≤ 3 * C0 + 1 := by linarith only [hC0pos]
    simpa using h0
  · set f : ℕ → ℂ → ℂ := fun p s => 1 - χ (p : ZMod d) * (p : ℂ) ^ (-s) with hf
    have hf_an : ∀ p : ℕ, p.Prime → Differentiable ℂ (f p) := fun p hp =>
      Work.LinnikAreas.TuranOther.levelFactor_differentiable χ hp.ne_zero
    have hS : ∀ p ∈ q.primeFactors, p.Prime := fun p hp => Nat.prime_of_mem_primeFactors hp
    have hG : ∀ p : ℕ, p.Prime →
        Summable (fun u : ℂ => (analyticOrderNatAt (f p) u : ℝ) / ‖w - u‖ ^ 2) ∧
          (∑' u : ℂ, (analyticOrderNatAt (f p) u : ℝ) / ‖w - u‖ ^ 2)
            ≤ C0 * (1 + Real.log p) := by
      intro p hp
      by_cases hpd : p ∣ d
      · have hχ0 : χ (p : ZMod d) = 0 := by
          refine MulChar.map_nonunit χ ?_
          intro h
          exact (Nat.Prime.coprime_iff_not_dvd hp).mp
            ((ZMod.isUnit_iff_coprime p d).mp h) hpd
        have hfun : f p = fun _ : ℂ => (1 : ℂ) := by
          funext s
          rw [hf]
          simp [hχ0]
        rw [hfun]
        have hz : (fun u : ℂ => (analyticOrderNatAt (fun _ : ℂ => (1 : ℂ)) u : ℝ)
            / ‖w - u‖ ^ 2) = fun _ : ℂ => 0 := by
          funext u
          rw [analyticOrderNatAt_const_one]
          norm_num
        rw [hz]
        refine ⟨summable_zero, ?_⟩
        rw [tsum_zero]
        have hlogp : 0 ≤ Real.log p := Real.log_nonneg (by exact_mod_cast hp.one_le)
        nlinarith only [hC0pos, hlogp]
      · have hc : ‖χ (p : ZMod d)‖ = 1 :=
          Work.LinnikAreas.TuranOther.norm_apply_eq_one_of_isUnit χ
            ((ZMod.isUnit_iff_coprime p d).mpr ((Nat.Prime.coprime_iff_not_dvd hp).mpr hpd))
        have hfe : f p = Work.LinnikAreas.TuranOther.lvlE p (χ (p : ZMod d)) := by
          funext s
          rw [hf, Work.LinnikAreas.TuranOther.lvlE_eq hp]
        rw [hfe]
        exact hC0 hp hc w hw
    have hsumS := summable_finset_sum_tsum q.primeFactors
      (fun p u => (analyticOrderNatAt (f p) u : ℝ) / ‖w - u‖ ^ 2)
      (fun p hp => (hG p (hS p hp)).1)
    have hpt : ∀ u : ℂ,
        (analyticOrderNatAt (q.primeFactors.prod f) u : ℝ) / ‖w - u‖ ^ 2
          ≤ ∑ p ∈ q.primeFactors, (analyticOrderNatAt (f p) u : ℝ) / ‖w - u‖ ^ 2 := by
      intro u
      rw [← Finset.sum_div]
      refine div_le_div_of_nonneg_right ?_ (by positivity)
      exact_mod_cast ord_finsetProd_le q.primeFactors f u
        (fun p hp => (hf_an p (hS p hp)).analyticAt u)
    have hsumm : Summable (fun u : ℂ =>
        (analyticOrderNatAt (q.primeFactors.prod f) u : ℝ) / ‖w - u‖ ^ 2) :=
      Summable.of_nonneg_of_le (fun u => div_nonneg (Nat.cast_nonneg _) (by positivity))
        hpt hsumS.1
    have hbnd : (∑' u : ℂ, (analyticOrderNatAt (q.primeFactors.prod f) u : ℝ) / ‖w - u‖ ^ 2)
        ≤ (3 * C0 + 1) * (Real.log (q : ℝ) + 1) := by
      have hle := Summable.tsum_le_tsum hpt hsumm hsumS.1
      rw [hsumS.2] at hle
      have h1 : ∑ p ∈ q.primeFactors, (∑' u : ℂ, (analyticOrderNatAt (f p) u : ℝ) / ‖w - u‖ ^ 2)
          ≤ ∑ p ∈ q.primeFactors, C0 * (1 + Real.log (p : ℝ)) :=
        Finset.sum_le_sum (fun p hp => (hG p (hS p hp)).2)
      refine hle.trans (h1.trans ?_)
      have hlogq : 0 ≤ Real.log (q : ℝ) :=
        Real.log_nonneg (by exact_mod_cast Nat.one_le_iff_ne_zero.mpr hq)
      have hlogprod : ∑ p ∈ q.primeFactors, Real.log (p : ℝ)
          = Real.log (∏ p ∈ q.primeFactors, (p : ℝ)) := by
        rw [Real.log_prod]
        intro p hp
        exact_mod_cast (hS p hp).ne_zero
      have hprodposR : 0 < ∏ p ∈ q.primeFactors, (p : ℝ) :=
        Finset.prod_pos (fun p hp => by exact_mod_cast (hS p hp).pos)
      have hprodR : (∏ p ∈ q.primeFactors, (p : ℝ)) ≤ (q : ℝ) := by
        have h1 : ((∏ p ∈ q.primeFactors, p : ℕ) : ℝ) ≤ (q : ℝ) :=
          by exact_mod_cast Nat.le_of_dvd (Nat.pos_of_ne_zero hq) (Nat.prod_primeFactors_dvd q)
        simpa using h1
      have hlogprodle : Real.log (∏ p ∈ q.primeFactors, (p : ℝ)) ≤ Real.log (q : ℝ) :=
        Real.log_le_log hprodposR hprodR
      have hcard : ((q.primeFactors.card : ℕ) : ℝ) ≤ 2 * Real.log (q : ℝ) := by
        have hp2 : (2:ℕ) ^ q.primeFactors.card ≤ ∏ p ∈ q.primeFactors, p := by
          have h := Finset.prod_le_prod' (s := q.primeFactors) (f := fun _ => (2:ℕ))
            (g := fun p => p) (fun p hp => (hS p hp).two_le)
          simpa [Finset.prod_const] using h
        have hp2R : (2:ℝ) ^ q.primeFactors.card ≤ (∏ p ∈ q.primeFactors, (p : ℝ)) := by
          have h1 : ((2:ℕ) ^ q.primeFactors.card : ℝ)
              ≤ ((∏ p ∈ q.primeFactors, p : ℕ) : ℝ) := by exact_mod_cast hp2
          simpa using h1
        have hlog2' : Real.log ((2:ℝ) ^ q.primeFactors.card)
            ≤ Real.log (∏ p ∈ q.primeFactors, (p : ℝ)) :=
          Real.log_le_log (by positivity) hp2R
        rw [Real.log_pow] at hlog2'
        have hlog2pos : (1:ℝ) / 2 ≤ Real.log 2 := by
          have := Real.log_two_gt_d9; linarith only [this]
        have hcardnn : (0:ℝ) ≤ ((q.primeFactors.card : ℕ) : ℝ) := Nat.cast_nonneg _
        have hstep := mul_le_mul_of_nonneg_left hlog2pos hcardnn
        push_cast at hlog2' hstep ⊢
        linarith only [hlog2', hlogprodle, hstep]
      have hsum1 : ∑ p ∈ q.primeFactors, (1 + Real.log (p : ℝ))
          = ((q.primeFactors.card : ℕ) : ℝ) + ∑ p ∈ q.primeFactors, Real.log (p : ℝ) := by
        rw [Finset.sum_add_distrib]
        congr 1
        simp [Finset.sum_const, nsmul_eq_mul]
      have hsum2 : ∑ p ∈ q.primeFactors, (1 + Real.log (p : ℝ)) ≤ 3 * Real.log (q : ℝ) := by
        rw [hsum1, hlogprod]
        linarith only [hcard, hlogprodle]
      rw [← Finset.mul_sum]
      have hmu := mul_le_mul_of_nonneg_left hsum2 hC0pos.le
      linarith only [hmu, hC0pos, hlogq]
    have hfe : q.primeFactors.prod f
        = fun s : ℂ => ∏ p ∈ q.primeFactors, (1 - χ (p : ZMod d) * (p : ℂ) ^ (-s)) := by
      funext s
      rw [Finset.prod_apply]
      try rfl
    rw [hfe] at hsumm hbnd
    exact ⟨hsumm, hbnd⟩

/-- **The `ζ`-half of the mass bound.** -/
lemma zetaMass_le :
    ∃ C : ℝ, 0 < C ∧ ∀ (w : ℂ), (3 / 2 : ℝ) ≤ w.re →
      Summable (fun u : ℂ => (multZeta u : ℝ) / ‖w - u‖ ^ 2) ∧
        (∑' u : ℂ, (multZeta u : ℝ) / ‖w - u‖ ^ 2)
          ≤ C * (Real.log (2 + ‖w‖) + 2) := by
  obtain ⟨CA, hCApos, hCA⟩ := completedZetaInvSq
  obtain ⟨CB, hCBpos, hCB⟩ := gammaRShiftInvSq
  refine ⟨CA + CB, by linarith only [hCApos, hCBpos], ?_⟩
  intro w hw
  obtain ⟨hAs, hAb⟩ := hCA w hw
  obtain ⟨hBs, hBb⟩ := hCB 0 w hw
  have hBeq : (fun z : ℂ => (Complex.Gammaℝ (z + ((0 : ℕ) : ℂ)))⁻¹)
      = fun z : ℂ => (Complex.Gammaℝ z)⁻¹ := by
    funext z; norm_num
  rw [hBeq] at hBs hBb
  have hpt : ∀ u : ℂ, (multZeta u : ℝ) / ‖w - u‖ ^ 2
      ≤ (analyticOrderNatAt completedRiemannZeta u : ℝ) / ‖w - u‖ ^ 2
        + (analyticOrderNatAt (fun z : ℂ => (Complex.Gammaℝ z)⁻¹) u : ℝ) / ‖w - u‖ ^ 2 := by
    intro u
    rw [← add_div]
    exact div_le_div_of_nonneg_right
      (by exact_mod_cast multZeta_le_lambda_add_invGammaR u) (by positivity)
  have hsum : Summable (fun u : ℂ =>
      (analyticOrderNatAt completedRiemannZeta u : ℝ) / ‖w - u‖ ^ 2
        + (analyticOrderNatAt (fun z : ℂ => (Complex.Gammaℝ z)⁻¹) u : ℝ) / ‖w - u‖ ^ 2) :=
    hAs.add hBs
  have hZs : Summable (fun u : ℂ => (multZeta u : ℝ) / ‖w - u‖ ^ 2) :=
    Summable.of_nonneg_of_le (fun u => div_nonneg (Nat.cast_nonneg _) (by positivity)) hpt hsum
  refine ⟨hZs, ?_⟩
  have hle := Summable.tsum_le_tsum hpt hZs hsum
  rw [Summable.tsum_add hAs hBs] at hle
  refine hle.trans ?_
  have hL2 : 0 ≤ Real.log (2 + ‖w‖) := Real.log_nonneg (by linarith only [norm_nonneg w])
  nlinarith only [hAb, hBb, hCApos, hCBpos, hL2]

/-- **The `L`-half of the mass bound.** -/
lemma lMass_le :
    ∃ C : ℝ, 0 < C ∧ ∀ (q : ℕ) [NeZero q] (ψ : DirichletCharacter ℂ q) (w : ℂ),
      (3 / 2 : ℝ) ≤ w.re →
      Summable (fun u : ℂ => (multL ψ u : ℝ) / ‖w - u‖ ^ 2) ∧
        (∑' u : ℂ, (multL ψ u : ℝ) / ‖w - u‖ ^ 2)
          ≤ C * (Real.log (q : ℝ) + Real.log (2 + ‖w‖) + 2) := by
  obtain ⟨Cz, hCzpos, hCz⟩ := zetaMass_le
  obtain ⟨CE, hCEpos, hCE⟩ := levelProdMass
  obtain ⟨CL, hCLpos, hCL⟩ := completedLInvSq
  obtain ⟨CB, hCBpos, hCB⟩ := gammaRShiftInvSq
  refine ⟨Cz + CE + CL + CB, by linarith only [hCzpos, hCEpos, hCLpos, hCBpos], ?_⟩
  intro q _inst ψ w hw
  by_cases hψ : ψ = 1
  · subst ψ
    obtain ⟨hZs, hZb⟩ := hCz w hw
    obtain ⟨hEs, hEb⟩ := hCE q 1 (1 : DirichletCharacter ℂ 1) w hw
    have hone : ∀ p : ℕ, (1 : DirichletCharacter ℂ 1) (p : ZMod 1) = 1 := by
      intro p
      have hp1 : (p : ZMod 1) = 1 := Subsingleton.elim _ _
      rw [hp1]
      exact MulChar.one_apply isUnit_one
    have hEeq : (fun s : ℂ => ∏ p ∈ q.primeFactors,
          (1 - (1 : DirichletCharacter ℂ 1) (p : ZMod 1) * (p : ℂ) ^ (-s)))
        = fun s : ℂ => ∏ p ∈ q.primeFactors, (1 - (p : ℂ) ^ (-s)) := by
      funext s
      refine Finset.prod_congr rfl (fun p _ => ?_)
      rw [hone p, one_mul]
    rw [hEeq] at hEs hEb
    let F1 : ℂ → ℝ := fun u => (multZeta u : ℝ) / ‖w - u‖ ^ 2
    let F2 : ℂ → ℝ := fun u =>
      (analyticOrderNatAt (fun s : ℂ => ∏ p ∈ q.primeFactors, (1 - (p : ℂ) ^ (-s))) u : ℝ)
        / ‖w - u‖ ^ 2
    have hF1 : Summable F1 := hZs
    have hF2 : Summable F2 := hEs
    have hpt : ∀ u : ℂ, (multL (1 : DirichletCharacter ℂ q) u : ℝ) / ‖w - u‖ ^ 2
        ≤ F1 u + F2 u := by
      intro u
      have h := multL_one_le q u
      have hR : (multL (1 : DirichletCharacter ℂ q) u : ℝ)
          ≤ (multZeta u : ℝ)
            + (analyticOrderNatAt (fun s : ℂ => ∏ p ∈ q.primeFactors, (1 - (p : ℂ) ^ (-s))) u : ℝ) :=
        by exact_mod_cast h
      rw [show F1 u + F2 u
          = ((multZeta u : ℝ)
            + (analyticOrderNatAt (fun s : ℂ => ∏ p ∈ q.primeFactors, (1 - (p : ℂ) ^ (-s))) u : ℝ))
            / ‖w - u‖ ^ 2 from by simp only [F1, F2]; ring]
      exact div_le_div_of_nonneg_right hR (by positivity)
    have hsum : Summable (fun u : ℂ => F1 u + F2 u) := hF1.add hF2
    have hLs : Summable (fun u : ℂ => (multL (1 : DirichletCharacter ℂ q) u : ℝ) / ‖w - u‖ ^ 2) :=
      Summable.of_nonneg_of_le (fun u => div_nonneg (Nat.cast_nonneg _) (by positivity)) hpt hsum
    refine ⟨hLs, ?_⟩
    have hle : (∑' u : ℂ, (multL (1 : DirichletCharacter ℂ q) u : ℝ) / ‖w - u‖ ^ 2)
        ≤ (∑' u : ℂ, F1 u) + (∑' u : ℂ, F2 u) := by
      have h1 := Summable.tsum_le_tsum hpt hLs hsum
      rwa [Summable.tsum_add hF1 hF2] at h1
    refine hle.trans ?_
    have hlogq : 0 ≤ Real.log (q : ℝ) :=
      Real.log_nonneg (by exact_mod_cast Nat.one_le_iff_ne_zero.mpr (NeZero.ne q))
    have hL2 : 0 ≤ Real.log (2 + ‖w‖) := Real.log_nonneg (by linarith only [norm_nonneg w])
    nlinarith only [hZb, hEb, hCzpos, hCEpos, hL2, hlogq, hCLpos, hCBpos]
  · letI : NeZero ψ.conductor := ⟨ψ.conductor_ne_zero⟩
    obtain ⟨a, ha0, ha1, -⟩ :=
      Work.LinnikAreas.TuranOther.lFunction_eq_completed_mul_invGamma ψ hψ
    have hdvd : ψ.conductor ∣ q := ψ.conductor_dvd_level
    have hne0 : ψ.conductor ≠ 0 := ψ.conductor_ne_zero
    have hd2 : 2 ≤ ψ.conductor := by
      have hne1 : ψ.conductor ≠ 1 := fun h => hψ ((eq_one_iff_conductor_eq_one).mpr h)
      omega
    have hprim_ne_one : ψ.primitiveCharacter ≠ 1 := by
      intro h
      apply hψ
      rw [← DirichletCharacter.changeLevel_primitiveCharacter (χ := ψ), h]
      exact DirichletCharacter.changeLevel_one _
    obtain ⟨hLs, hLb⟩ := hCL ψ.conductor hd2 ψ.primitiveCharacter hprim_ne_one
      (DirichletCharacter.primitiveCharacter_isPrimitive ψ) w hw
    obtain ⟨hEs, hEb⟩ := hCE q ψ.conductor ψ.primitiveCharacter w hw
    obtain ⟨hGs, hGb⟩ := hCB a w hw
    set E : ℂ → ℂ := fun s : ℂ => ∏ p ∈ q.primeFactors,
      (1 - ψ.primitiveCharacter (p : ZMod ψ.conductor) * (p : ℂ) ^ (-s)) with hEdef
    have hEdiff : Differentiable ℂ E :=
      Work.LinnikAreas.TuranOther.diff_finsetProd q.primeFactors _
        (fun p hp => Work.LinnikAreas.TuranOther.levelFactor_differentiable ψ.primitiveCharacter
          (Nat.prime_of_mem_primeFactors hp).ne_zero)
    have hEs' : Summable (fun u : ℂ => (analyticOrderNatAt E u : ℝ) / ‖w - u‖ ^ 2) := hEs
    have hLfac := completedLFunction_primitiveFactor ψ hψ
    have hpt : ∀ u : ℂ, (multL ψ u : ℝ) / ‖w - u‖ ^ 2
        ≤ (analyticOrderNatAt (DirichletCharacter.completedLFunction ψ.primitiveCharacter) u : ℝ)
              / ‖w - u‖ ^ 2
          + (analyticOrderNatAt E u : ℝ) / ‖w - u‖ ^ 2
          + (analyticOrderNatAt (fun z : ℂ => (Complex.Gammaℝ (z + (a : ℂ)))⁻¹) u : ℝ)
              / ‖w - u‖ ^ 2 := by
      intro u
      have h1 := Work.LinnikAreas.TuranOther.lFunctionOrderAddInvGammaR ψ hψ a ha0 ha1 u
      have h2 : analyticOrderNatAt (DirichletCharacter.completedLFunction ψ) u
          ≤ analyticOrderNatAt (DirichletCharacter.completedLFunction ψ.primitiveCharacter) u
            + analyticOrderNatAt E u := by
        have h3 := analyticOrderNatAt_mul_le
          (f := DirichletCharacter.completedLFunction ψ.primitiveCharacter) (g := E) (z := u)
          ((DirichletCharacter.differentiable_completedLFunction hprim_ne_one).analyticAt u)
          (hEdiff.analyticAt u)
        rw [hLfac]
        exact h3
      have h2R : (analyticOrderNatAt (DirichletCharacter.completedLFunction ψ) u : ℝ)
          ≤ (analyticOrderNatAt (DirichletCharacter.completedLFunction ψ.primitiveCharacter) u : ℝ)
            + (analyticOrderNatAt E u : ℝ) := by exact_mod_cast h2
      have hR : (multL ψ u : ℝ)
          ≤ (analyticOrderNatAt (DirichletCharacter.completedLFunction ψ.primitiveCharacter) u : ℝ)
            + (analyticOrderNatAt E u : ℝ)
            + (analyticOrderNatAt (fun z : ℂ => (Complex.Gammaℝ (z + (a : ℂ)))⁻¹) u : ℝ) := by
        simp only [multL]
        rw [h1]
        push_cast
        linarith only [_inst, this, h2R]
      rw [show (analyticOrderNatAt (DirichletCharacter.completedLFunction ψ.primitiveCharacter) u : ℝ)
              / ‖w - u‖ ^ 2
          + (analyticOrderNatAt E u : ℝ) / ‖w - u‖ ^ 2
          + (analyticOrderNatAt (fun z : ℂ => (Complex.Gammaℝ (z + (a : ℂ)))⁻¹) u : ℝ)
              / ‖w - u‖ ^ 2
          = ((analyticOrderNatAt (DirichletCharacter.completedLFunction ψ.primitiveCharacter) u : ℝ)
            + (analyticOrderNatAt E u : ℝ)
            + (analyticOrderNatAt (fun z : ℂ => (Complex.Gammaℝ (z + (a : ℂ)))⁻¹) u : ℝ))
            / ‖w - u‖ ^ 2 from by rw [add_div, add_div]]
      exact div_le_div_of_nonneg_right hR (by positivity)
    have hsum : Summable (fun u : ℂ =>
        (analyticOrderNatAt (DirichletCharacter.completedLFunction ψ.primitiveCharacter) u : ℝ)
            / ‖w - u‖ ^ 2
          + (analyticOrderNatAt E u : ℝ) / ‖w - u‖ ^ 2
          + (analyticOrderNatAt (fun z : ℂ => (Complex.Gammaℝ (z + (a : ℂ)))⁻¹) u : ℝ)
              / ‖w - u‖ ^ 2) := (hLs.add hEs').add hGs
    have hLs' : Summable (fun u : ℂ => (multL ψ u : ℝ) / ‖w - u‖ ^ 2) :=
      Summable.of_nonneg_of_le (fun u => div_nonneg (Nat.cast_nonneg _) (by positivity)) hpt hsum
    refine ⟨hLs', ?_⟩
    have hle := Summable.tsum_le_tsum hpt hLs' hsum
    rw [Summable.tsum_add (hLs.add hEs') hGs, Summable.tsum_add hLs hEs'] at hle
    refine hle.trans ?_
    have hlogq : 0 ≤ Real.log (q : ℝ) :=
      Real.log_nonneg (by exact_mod_cast Nat.one_le_iff_ne_zero.mpr (NeZero.ne q))
    have hL2 : 0 ≤ Real.log (2 + ‖w‖) := Real.log_nonneg (by linarith only [norm_nonneg w])
    have hlogd : Real.log (ψ.conductor : ℝ) ≤ Real.log (q : ℝ) :=
      Real.log_le_log (by exact_mod_cast Nat.pos_of_ne_zero hne0)
        (by exact_mod_cast Nat.le_of_dvd (Nat.pos_of_ne_zero (NeZero.ne q)) hdvd)
    nlinarith only [hLb, hEb, hGb, hlogd, hL2, hlogq, hCLpos, hCEpos, hCBpos, hCzpos, this]

theorem lMultMassRect : ∃ C : ℝ, 0 < C ∧ ∀ (q : ℕ) [NeZero q] (ψ : DirichletCharacter ℂ q) (w : ℂ),
    (3 / 2 : ℝ) ≤ w.re →
    Summable (fun u : ℂ => ((Work.LinnikAreas.TuranOther.multZeta u : ℝ) + (Work.LinnikAreas.TuranOther.multL ψ u : ℝ)) / ‖w - u‖ ^ 2) ∧
      (∑' u : ℂ, ((Work.LinnikAreas.TuranOther.multZeta u : ℝ) + (Work.LinnikAreas.TuranOther.multL ψ u : ℝ)) / ‖w - u‖ ^ 2)
        ≤ C * (Real.log (q : ℝ) + Real.log (2 + ‖w‖) + 2) := by
  obtain ⟨Cz, hCzpos, hCz⟩ := zetaMass_le
  obtain ⟨Cl, hClpos, hCl⟩ := lMass_le
  refine ⟨Cz + Cl, by linarith only [hCzpos, hClpos], ?_⟩
  intro q _inst ψ w hw
  obtain ⟨hZs, hZb⟩ := hCz w hw
  obtain ⟨hLs, hLb⟩ := hCl q ψ w hw
  have hpt : (fun u : ℂ => ((multZeta u : ℝ) + (multL ψ u : ℝ)) / ‖w - u‖ ^ 2)
      = fun u : ℂ => (multZeta u : ℝ) / ‖w - u‖ ^ 2 + (multL ψ u : ℝ) / ‖w - u‖ ^ 2 := by
    funext u
    rw [add_div]
  refine ⟨?_, ?_⟩
  · rw [hpt]
    exact hZs.add hLs
  · rw [hpt, Summable.tsum_add hZs hLs]
    have hlogq : 0 ≤ Real.log (q : ℝ) :=
      Real.log_nonneg (by exact_mod_cast Nat.one_le_iff_ne_zero.mpr (NeZero.ne q))
    have hL2 : 0 ≤ Real.log (2 + ‖w‖) := Real.log_nonneg (by linarith only [norm_nonneg w])
    nlinarith only [hZb, hLb, hCzpos, hClpos, hlogq, hL2, _inst]

end Work.LinnikAreas.turanAux2
