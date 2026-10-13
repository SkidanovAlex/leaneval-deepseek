import Mathlib.Analysis.Calculus.ContDiff.Deriv
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Mathlib.MeasureTheory.Integral.IntervalIntegral.IntegrationByParts

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

open scoped ContDiff
open MeasureTheory

namespace Work.FTS.StrongEps.EComparison

/-- The interval integral of a function vanishing on `[[c, d]]` is zero. -/
private lemma intervalIntegral_eq_zero_of_forall_mem_uIcc {f : ℝ → ℝ} {c d : ℝ}
    (h : ∀ x ∈ Set.uIcc c d, f x = 0) : (∫ x in c..d, f x) = 0 := by
  rw [intervalIntegral.integral_congr h]
  exact intervalIntegral.integral_zero

/-- `[[c, d]] ⊆ (-∞, A]` as soon as both endpoints are `≤ A`. -/
private lemma uIcc_subset_Iic {c d A : ℝ} (hc : c ≤ A) (hd : d ≤ A) :
    Set.uIcc c d ⊆ Set.Iic A := by
  intro x hx
  rcases Set.mem_uIcc.mp hx with ⟨h1, h2⟩ | ⟨h1, h2⟩
  · exact le_trans h2 hd
  · exact le_trans h2 hc

/-- `[[c, d]] ⊆ [B, ∞)` as soon as both endpoints are `≥ B`. -/
private lemma uIcc_subset_Ici {c d B : ℝ} (hc : B ≤ c) (hd : B ≤ d) :
    Set.uIcc c d ⊆ Set.Ici B := by
  intro x hx
  rcases Set.mem_uIcc.mp hx with ⟨h1, h2⟩ | ⟨h1, h2⟩
  · exact le_trans hc h1
  · exact le_trans hd h1

/-- The indefinite integral `t ↦ ∫ s in a..t, g s` of a function `g : ℝ → ℝ` which is `C^n` for
every `n` is again `C^n` for every `n`, and its derivative is `g`. -/
private lemma contDiff_indefiniteIntegral {a : ℝ} {g : ℝ → ℝ} (hg : ∀ n : ℕ, ContDiff ℝ n g) :
    (∀ n : ℕ, ContDiff ℝ n (fun t => ∫ s in a..t, g s)) ∧
      deriv (fun t => ∫ s in a..t, g s) = g := by
  have hgc : Continuous g := contDiff_zero.mp (hg 0)
  have hderiv : ∀ t : ℝ, HasDerivAt (fun u => ∫ s in a..u, g s) (g t) t := fun t =>
    intervalIntegral.integral_hasDerivAt_right (f := g) (a := a) (b := t)
      (hgc.intervalIntegrable a t)
      (hgc.stronglyMeasurableAtFilter volume (nhds t)) hgc.continuousAt
  have hder : deriv (fun t => ∫ s in a..t, g s) = g := funext fun t => (hderiv t).deriv
  have hdiff : Differentiable ℝ (fun t => ∫ s in a..t, g s) :=
    fun t => (hderiv t).differentiableAt
  have hinf : ContDiff ℝ ∞ (fun t => ∫ s in a..t, g s) := by
    rw [contDiff_infty_iff_deriv]
    exact ⟨hdiff, by rw [hder]; exact contDiff_infty.mpr hg⟩
  exact ⟨fun n => contDiff_infty.mp hinf n, hder⟩

/-- **Second antiderivative of a test function with two vanishing moments.**

Given `ψ` of class `C^∞` with compact support contained in the open interval `(a,b)` and with
vanishing zeroth and first moments against the interval `(a,b)`, there is a `C^∞` function `ρ`
with compact support contained in `(a,b)` whose second derivative is `ψ`. -/
theorem ExistsTestfunSecondDeriv {a b : ℝ} (hab : a < b) {ψ : ℝ → ℝ}
    (hψ : ∀ n : ℕ, ContDiff ℝ n ψ) (hψc : HasCompactSupport ψ) (hsupp : tsupport ψ ⊆ Set.Ioo a b)
    (h1 : (∫ t in a..b, ψ t) = 0) (h2 : (∫ t in a..b, t * ψ t) = 0) :
    ∃ ρ : ℝ → ℝ, (∀ n : ℕ, ContDiff ℝ n ρ) ∧ HasCompactSupport ρ ∧ tsupport ρ ⊆ Set.Ioo a b ∧
      ∀ t : ℝ, deriv (deriv ρ) t = ψ t := by
  have hψcont : Continuous ψ := contDiff_zero.mp (hψ 0)
  have hsupp_sub : Function.support ψ ⊆ Set.Ioo a b :=
    fun x hx => hsupp (subset_tsupport ψ hx)
  have hzts : ∀ t : ℝ, t ∉ tsupport ψ → ψ t = 0 := by
    intro t ht
    by_contra hne
    exact ht (subset_tsupport ψ (Function.mem_support.mpr hne))
  -- `ψ` vanishes outside a slightly smaller closed interval `[A, B]`
  have ha_not : a ∉ tsupport ψ := fun h => absurd (hsupp h).1 (lt_irrefl a)
  have hnb_a : (tsupport ψ)ᶜ ∈ nhds a := (isClosed_tsupport ψ).isOpen_compl.mem_nhds ha_not
  obtain ⟨εa, hεa, hεasub⟩ := Metric.mem_nhds_iff.mp hnb_a
  have hb_not : b ∉ tsupport ψ := fun h => absurd (hsupp h).2 (lt_irrefl b)
  have hnb_b : (tsupport ψ)ᶜ ∈ nhds b := (isClosed_tsupport ψ).isOpen_compl.mem_nhds hb_not
  obtain ⟨εb, hεb, hεbsub⟩ := Metric.mem_nhds_iff.mp hnb_b
  set A : ℝ := a + εa / 2 with hAdef
  set B : ℝ := b - εb / 2 with hBdef
  have hAle : a ≤ A := by rw [hAdef]; linarith
  have hA : a < A := by rw [hAdef]; linarith
  have hBle : B ≤ b := by rw [hBdef]; linarith
  have hB : B < b := by rw [hBdef]; linarith
  have hψzero_le_A : ∀ t : ℝ, t ≤ A → ψ t = 0 := by
    intro t ht
    rcases le_or_gt t a with h | h
    · by_contra hne
      exact absurd (hsupp_sub (Function.mem_support.mpr hne)).1 (not_lt.mpr h)
    · refine hzts t (hεasub ?_)
      rw [Metric.mem_ball, Real.dist_eq, abs_of_pos (sub_pos.mpr h)]
      have ht' : t ≤ a + εa / 2 := by rw [hAdef] at ht; exact ht
      linarith
  have hψzero_ge_B : ∀ t : ℝ, B ≤ t → ψ t = 0 := by
    intro t ht
    rcases le_or_gt b t with h | h
    · by_contra hne
      exact absurd (hsupp_sub (Function.mem_support.mpr hne)).2 (not_lt.mpr h)
    · refine hzts t (hεbsub ?_)
      rw [Metric.mem_ball, Real.dist_eq, abs_of_neg (sub_neg.mpr h)]
      have ht' : b - εb / 2 ≤ t := by rw [hBdef] at ht; exact ht
      linarith
  have hψzero : ∀ t : ℝ, t ≤ A ∨ B ≤ t → ψ t = 0 :=
    fun t ht => ht.elim (hψzero_le_A t) (hψzero_ge_B t)
  -- the first antiderivative `Ψ`
  let Ψ : ℝ → ℝ := fun t => ∫ s in a..t, ψ s
  have hΨderiv' : ∀ t : ℝ, HasDerivAt Ψ (ψ t) t := fun t =>
    intervalIntegral.integral_hasDerivAt_right (f := ψ) (a := a) (b := t)
      (hψcont.intervalIntegrable a t)
      (hψcont.stronglyMeasurableAtFilter volume (nhds t)) hψcont.continuousAt
  have hΨderiv : deriv Ψ = ψ := funext fun t => (hΨderiv' t).deriv
  have hΨdiff : Differentiable ℝ Ψ := fun t => (hΨderiv' t).differentiableAt
  have hΨinf : ContDiff ℝ ∞ Ψ := by
    rw [contDiff_infty_iff_deriv]
    exact ⟨hΨdiff, by rw [hΨderiv]; exact contDiff_infty.mpr hψ⟩
  have hΨcont : Continuous Ψ := (contDiff_infty.mp hΨinf 0).continuous
  have hΨzero_le_A : ∀ t : ℝ, t ≤ A → Ψ t = 0 := by
    intro t ht
    show (∫ s in a..t, ψ s) = 0
    exact intervalIntegral_eq_zero_of_forall_mem_uIcc
      (fun x hx => hψzero_le_A x (uIcc_subset_Iic hAle ht hx))
  have hΨzero_ge_B : ∀ t : ℝ, B ≤ t → Ψ t = 0 := by
    intro t ht
    have hadj := intervalIntegral.integral_add_adjacent_intervals (μ := volume) (f := ψ)
      (a := a) (b := b) (c := t) (hψcont.intervalIntegrable a b) (hψcont.intervalIntegrable b t)
    show (∫ s in a..t, ψ s) = 0
    rw [← hadj, h1]
    have hb' : (∫ x in b..t, ψ x) = 0 :=
      intervalIntegral_eq_zero_of_forall_mem_uIcc
        (fun x hx => hψzero_ge_B x (uIcc_subset_Ici hBle ht hx))
    rw [hb', add_zero]
  have hΨzero : ∀ t : ℝ, t ≤ A ∨ B ≤ t → Ψ t = 0 :=
    fun t ht => ht.elim (hΨzero_le_A t) (hΨzero_ge_B t)
  have hΨa : Ψ a = 0 := hΨzero_le_A a hAle
  have hΨb : Ψ b = 0 := hΨzero_ge_B b hBle
  have hR : (∫ x in a..b, ψ x * x) = 0 := by
    rw [← h2]
    apply intervalIntegral.integral_congr
    intro x _
    ring
  -- the two moment conditions give `∫ Ψ = 0` by integration by parts
  have hΨint : (∫ s in a..b, Ψ s) = 0 := by
    have hIBP := intervalIntegral.integral_mul_deriv_eq_deriv_mul (u := Ψ)
      (v := fun x : ℝ => x) (u' := ψ) (v' := fun _ => (1 : ℝ)) (a := a) (b := b)
      (fun x _ => hΨderiv' x) (fun x _ => hasDerivAt_id x)
      (hψcont.intervalIntegrable a b) (continuous_const.intervalIntegrable a b)
    have hL : (∫ x in a..b, Ψ x * (fun _ => (1 : ℝ)) x) = ∫ x in a..b, Ψ x := by
      apply intervalIntegral.integral_congr
      intro x _
      simp
    rw [hL, hΨb, hΨa, hR] at hIBP
    simpa using hIBP
  -- the second antiderivative `ρ`
  let ρ : ℝ → ℝ := fun t => ∫ s in a..t, Ψ s
  have hρderiv' : ∀ t : ℝ, HasDerivAt ρ (Ψ t) t := fun t =>
    intervalIntegral.integral_hasDerivAt_right (f := Ψ) (a := a) (b := t)
      (hΨcont.intervalIntegrable a t)
      (hΨcont.stronglyMeasurableAtFilter volume (nhds t)) hΨcont.continuousAt
  have hρderiv : deriv ρ = Ψ := funext fun t => (hρderiv' t).deriv
  have hρdiff : Differentiable ℝ ρ := fun t => (hρderiv' t).differentiableAt
  have hρinf : ContDiff ℝ ∞ ρ := by
    rw [contDiff_infty_iff_deriv]
    exact ⟨hρdiff, by rw [hρderiv]; exact hΨinf⟩
  have hρzero_le_A : ∀ t : ℝ, t ≤ A → ρ t = 0 := by
    intro t ht
    show (∫ s in a..t, Ψ s) = 0
    exact intervalIntegral_eq_zero_of_forall_mem_uIcc
      (fun x hx => hΨzero_le_A x (uIcc_subset_Iic hAle ht hx))
  have hρzero_ge_B : ∀ t : ℝ, B ≤ t → ρ t = 0 := by
    intro t ht
    have hadj := intervalIntegral.integral_add_adjacent_intervals (μ := volume) (f := Ψ)
      (a := a) (b := b) (c := t) (hΨcont.intervalIntegrable a b) (hΨcont.intervalIntegrable b t)
    show (∫ s in a..t, Ψ s) = 0
    rw [← hadj, hΨint]
    have hb' : (∫ x in b..t, Ψ x) = 0 :=
      intervalIntegral_eq_zero_of_forall_mem_uIcc
        (fun x hx => hΨzero_ge_B x (uIcc_subset_Ici hBle ht hx))
    rw [hb', add_zero]
  -- `ρ` is supported in `(A, B)`, hence in `(a, b)`
  have hsuppρ : Function.support ρ ⊆ Set.Ioo A B := by
    intro t ht
    have ht' : ρ t ≠ 0 := Function.mem_support.mp ht
    by_contra hcon
    rw [Set.mem_Ioo, not_and_or, not_lt, not_lt] at hcon
    rcases hcon with h | h
    · exact ht' (hρzero_le_A t h)
    · exact ht' (hρzero_ge_B t h)
  have htsp : tsupport ρ ⊆ Set.Ioo a b := by
    intro x hx
    have hx' : x ∈ closure (Set.Ioo A B) := closure_mono hsuppρ hx
    have hx'' : x ∈ Set.Icc A B :=
      (closure_minimal (Set.Ioo_subset_Icc_self : Set.Ioo A B ⊆ Set.Icc A B) isClosed_Icc :
        closure (Set.Ioo A B) ⊆ Set.Icc A B) hx'
    exact ⟨lt_of_lt_of_le hA hx''.1, lt_of_le_of_lt hx''.2 hB⟩
  have hcomp : HasCompactSupport ρ :=
    (isCompact_Icc (a := a) (b := b)).of_isClosed_subset (isClosed_tsupport ρ)
      (fun x hx => Set.Ioo_subset_Icc_self (htsp hx))
  exact ⟨ρ, fun n => contDiff_infty.mp hρinf n, hcomp, htsp, fun t => by
    rw [hρderiv]
    exact congrFun hΨderiv t⟩

end Work.FTS.StrongEps.EComparison
