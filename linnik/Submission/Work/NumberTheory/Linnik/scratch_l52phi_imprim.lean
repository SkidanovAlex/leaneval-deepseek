import Mathlib
import Submission.Work.NumberTheory.Linnik.scratch_l52phi_free
import Submission.Commons.NumberTheory.Linnik.Ksum_imprimitive_diff
import Submission.Commons.NumberTheory.Linnik.smoothed_vonMangoldt_tsum_re
import Submission.Commons.NumberTheory.Linnik.lemma5_2_sigma_ge_one
import Submission.Commons.Analysis.Asymptotics.le_mul_exp_sqrt_log_eventually

open Complex DirichletCharacter Metric Filter Set Topology MeasureTheory
open scoped Real Topology BigOperators

set_option autoImplicit false
set_option maxHeartbeats 4000000

namespace Commons.NumberTheory.Linnik

/-- **HB Lemma 5.2, parametric window radius, imprimitive characters.**

Let `χ` be a non-principal character mod `q` and let `χ*` be the primitive character inducing it.
Then, with `L = log q`, the weighted von Mangoldt sum for `χ` is bounded by
`-L Σ_{|1+it-ρ|≤δ} Re F((s-ρ)L) + f(0)(1/6+ε)L`, provided the log-derivative hypothesis (Lemma 3.1
in the form used by §5) holds for `χ*`, the window radius `δ ∈ (0,1)` is fixed, and `q` is large
enough (the threshold may depend on `f, ε, δ`). -/
theorem lemma5_2_of_logDeriv_bound_phi_imprim (x₀ B : ℝ) (c : ℝ) (hx₀ : 0 < x₀) (hB : 0 ≤ B) :
    ∀ {f : ℝ → ℝ} (hcont : ContinuousOn f (Set.Ici 0)) (hsupp : ∀ t : ℝ, x₀ ≤ t → f t = 0)
      (hf2 : ContDiffOn ℝ 2 f (Set.Ioo 0 x₀))
      (hBnd : ∀ t ∈ Set.Ioo (0:ℝ) x₀, ‖iteratedDeriv 2 f t‖ ≤ B) (hf0 : 0 < f 0)
      {ε : ℝ} (hε : 0 < ε) {δ : ℝ} (hδ0 : 0 < δ) (hδ1 : δ < 1),
      ∃ q₀ : ℕ, ∀ {q : ℕ} [NeZero q], q₀ ≤ q →
      ∀ (χ : DirichletCharacter ℂ q) [NeZero χ.conductor] (hχ : χ ≠ 1),
        (∀ s : ℂ, 1 + 1 / (Real.log (q : ℝ) * Real.log (Real.log (q : ℝ))) ≤ s.re →
            s.re ≤ 1 + Real.log (Real.log (q : ℝ)) / Real.log (q : ℝ) →
            |s.im| ≤ 10 * Real.log (q : ℝ) →
          (-logDeriv (DirichletCharacter.LFunction χ.primitiveCharacter) s).re
            + (∑ᶠ u : ℂ, ((MeromorphicOn.divisor (DirichletCharacter.completedLFunction χ.primitiveCharacter) (Metric.closedBall 0 (|s.im| + 2))) u : ℤ) *
                (if ‖(1:ℂ) + (s.im : ℂ) * Complex.I - u‖ ≤ δ then ((1/(s-u)).re) else 0))
            ≤ (c + ε/4) * Real.log (q : ℝ)) →
        ∀ s : ℂ, |s.re - 1| ≤ Real.sqrt (Real.log (Real.log (q : ℝ))) / Real.log (q : ℝ) →
          |s.im| ≤ 10 * Real.log (q : ℝ) →
          1 - Real.sqrt (Real.log (Real.log (q : ℝ))) / Real.log (q : ℝ) ≤ s.re →
          (∑' n : ℕ, (ArithmeticFunction.vonMangoldt n : ℝ) *
              ((χ (n : ZMod q) / (n : ℂ) ^ s).re) * f (Real.log n / Real.log q))
            ≤ -(Real.log q) * (∑ᶠ u : ℂ, ((MeromorphicOn.divisor (DirichletCharacter.completedLFunction χ.primitiveCharacter) (Metric.closedBall 0 (|s.im| + 2))) u : ℤ) *
                (if ‖(1:ℂ) + (s.im : ℂ) * Complex.I - u‖ ≤ δ then
                  ((∫ t in (0:ℝ)..x₀, Complex.exp (-(((s - u) * (Real.log q)) * (t : ℂ))) * ((f t : ℝ) : ℂ)).re) else 0))
            + f 0 * (c + ε) * Real.log q := by
  intro f hcont hsupp hf2 hBnd hf0 ε hε δ hδ0 hδ1
  classical
  obtain ⟨Kf, hKf⟩ : ∃ Kf : ℝ, ∀ t ∈ Set.Icc 0 x₀, ‖f t‖ ≤ Kf :=
    isCompact_Icc.exists_bound_of_continuousOn (hcont.mono (fun t ht => ht.1))
  have hKfnn : 0 ≤ Kf := le_trans (norm_nonneg _) (hKf 0 (by constructor <;> linarith))
  obtain ⟨L₀free, hfree⟩ := (lemma5_2_of_logDeriv_bound_phi_free x₀ B c hx₀ hB)
    hcont hsupp hf2 hBnd hf0 (show (0:ℝ) < ε / 2 by linarith) hδ0 hδ1
  obtain ⟨C, hCpos, q₀i, himp⟩ := Ksum_imprimitive_diff x₀ hx₀
  obtain ⟨L₀ab, hL₀ab1, hab⟩ :=
    Commons.Analysis.Asymptotics.le_mul_exp_sqrt_log_eventually
      (P := C * Kf) (x₀ := 1) (δ := f 0 * (ε / 4)) (by positivity)
  refine ⟨max q₀i (⌈Real.exp (max (max L₀free L₀ab) 5)⌉₊ + 6), ?_⟩
  intro q _inst hq χ _instc hχ hH s hsre hsim hs1
  set L : ℝ := Real.log (q : ℝ) with hLdef
  have hqpos : 0 < q := Nat.pos_of_ne_zero (NeZero.ne q)
  have hq3 : 3 ≤ q := three_le_modulus_of_char_ne_one χ hχ
  -- thresholds
  have hq_ge_exp : Real.exp (max (max L₀free L₀ab) 5) ≤ (q : ℝ) := by
    have h1 : Real.exp (max (max L₀free L₀ab) 5) ≤ (⌈Real.exp (max (max L₀free L₀ab) 5)⌉₊ : ℝ) :=
      Nat.le_ceil _
    have h2 : (⌈Real.exp (max (max L₀free L₀ab) 5)⌉₊ : ℝ)
        ≤ ((max q₀i (⌈Real.exp (max (max L₀free L₀ab) 5)⌉₊ + 6) : ℕ) : ℝ) := by
      have h3 : (⌈Real.exp (max (max L₀free L₀ab) 5)⌉₊ : ℝ)
          ≤ ((⌈Real.exp (max (max L₀free L₀ab) 5)⌉₊ + 6 : ℕ) : ℝ) := by
        push_cast; linarith
      exact h3.trans (by exact_mod_cast Nat.le_max_right _ _)
    have h4 : ((max q₀i (⌈Real.exp (max (max L₀free L₀ab) 5)⌉₊ + 6) : ℕ) : ℝ) ≤ (q : ℝ) := by
      exact_mod_cast hq
    linarith
  have hLe : max (max L₀free L₀ab) 5 ≤ L := by
    rw [hLdef, ← Real.log_exp (max (max L₀free L₀ab) 5)]
    exact Real.log_le_log (Real.exp_pos _) hq_ge_exp
  have hL5 : 5 ≤ L := le_trans (le_max_right _ _) hLe
  have hLe_free : L₀free ≤ L := le_trans (le_max_left _ _) (le_trans (le_max_left _ _) hLe)
  have hLe_ab : L₀ab ≤ L := le_trans (le_max_right _ _) (le_trans (le_max_left _ _) hLe)
  have hLpos : 0 < L := by linarith
  have hL1 : 1 ≤ L := by linarith
  have hlogLge1 : 1 ≤ Real.log L := by
    have h5 : (1:ℝ) ≤ Real.log 5 := by
      have h := Real.log_le_log (Real.exp_pos 1) (by linarith [Real.exp_one_lt_three] : Real.exp 1 ≤ 5)
      rwa [Real.log_exp] at h
    have h := Real.log_le_log (by norm_num : (0:ℝ) < 5) hL5
    linarith only [h5, h]
  -- the primitive character
  have hχ' : χ.primitiveCharacter ≠ 1 := by
    intro h
    apply hχ
    rw [← DirichletCharacter.changeLevel_primitiveCharacter χ, h]
    exact DirichletCharacter.changeLevel_one χ.conductor_dvd_level
  have hNL : Real.log ((χ.conductor : ℕ) : ℝ) ≤ L := by
    have hcd : χ.conductor ∣ q := χ.conductor_dvd_level
    have hcle : χ.conductor ≤ q := Nat.le_of_dvd hqpos hcd
    have hcpos : (0 : ℝ) < (χ.conductor : ℝ) := by
      have h := Nat.pos_of_ne_zero χ.conductor_ne_zero
      exact_mod_cast h
    rw [hLdef]
    exact Real.log_le_log hcpos (by exact_mod_cast hcle)
  -- the hypothesis in the shape used by the free lemma (instantiated at `ε/2`)
  have hH' : ∀ s : ℂ, 1 + 1 / (L * Real.log L) ≤ s.re → s.re ≤ 1 + Real.log L / L →
      |s.im| ≤ 10 * L →
      ((-logDeriv (DirichletCharacter.LFunction χ.primitiveCharacter) s).re
        + (∑ᶠ u : ℂ, ((MeromorphicOn.divisor (DirichletCharacter.completedLFunction χ.primitiveCharacter) (Metric.closedBall 0 (|s.im| + 2))) u : ℤ) *
            (if ‖(1:ℂ) + (s.im : ℂ) * Complex.I - u‖ ≤ δ then ((1/(s-u)).re) else 0)))
        ≤ (c + ε / 2 / 2) * L := by
    intro s h1 h2 h3
    have h := hH s h1 h2 h3
    convert h using 1
    ring
  -- the free (primitive) bound at the primitive character
  have hprim := hfree χ.primitiveCharacter hχ' χ.primitiveCharacter_isPrimitive
    hLe_free hNL hH' s hsre hsim
  -- the range conditions for the imprimitive correction
  have hsq_le1 : Real.sqrt (Real.log L) / L ≤ 1 := by
    have h1 : Real.log L ≤ L * L := by
      have h2 : Real.log L ≤ L - 1 := Real.log_le_sub_one_of_pos hLpos
      nlinarith only [h2, hL1]
    refine (div_le_one hLpos).mpr ?_
    calc Real.sqrt (Real.log L) ≤ Real.sqrt (L * L) := Real.sqrt_le_sqrt h1
      _ = L := by rw [Real.sqrt_mul_self hLpos.le]
  have hsre_le : s.re ≤ 2 := by
    have h := (abs_le.mp hsre).2
    linarith only [h, hsq_le1]
  have hcorr := himp (q := q) (le_trans (le_max_left _ _) hq) χ hχ hcont hsupp hKf hs1 hsre_le
  -- the two twisted sums
  set Tχ : ℂ := ∑' n : ℕ, (ArithmeticFunction.vonMangoldt n : ℂ) * (χ (n : ZMod q) : ℂ) /
      (n : ℂ) ^ s * ((f (Real.log n / L) : ℝ) : ℂ) with hTχdef
  set Tχ' : ℂ := ∑' n : ℕ, (ArithmeticFunction.vonMangoldt n : ℂ) *
      (χ.primitiveCharacter (n : ZMod χ.conductor) : ℂ) /
      (n : ℂ) ^ s * ((f (Real.log n / L) : ℝ) : ℂ) with hTχ'def
  have hsummχ : Summable (fun n : ℕ => (ArithmeticFunction.vonMangoldt n : ℂ) * (χ (n : ZMod q) : ℂ) /
      (n : ℂ) ^ s * ((f (Real.log n / L) : ℝ) : ℂ)) :=
    (smoothed_vonMangoldt_tsum_re hx₀ χ hsupp hLpos s).1
  have hsummχ' : Summable (fun n : ℕ => (ArithmeticFunction.vonMangoldt n : ℂ) *
      (χ.primitiveCharacter (n : ZMod χ.conductor) : ℂ) /
      (n : ℂ) ^ s * ((f (Real.log n / L) : ℝ) : ℂ)) :=
    (smoothed_vonMangoldt_tsum_re hx₀ χ.primitiveCharacter hsupp hLpos s).1
  have hKχ : Tχ.re = ∑' n : ℕ, (ArithmeticFunction.vonMangoldt n : ℝ) *
      ((χ (n : ZMod q) / (n : ℂ) ^ s).re) * f (Real.log n / L) := by
    rw [hTχdef]
    exact (smoothed_vonMangoldt_tsum_re hx₀ χ hsupp hLpos s).2
  have hKχ' : Tχ'.re = ∑' n : ℕ, (ArithmeticFunction.vonMangoldt n : ℝ) *
      ((χ.primitiveCharacter (n : ZMod χ.conductor) / (n : ℂ) ^ s).re) * f (Real.log n / L) := by
    rw [hTχ'def]
    exact (smoothed_vonMangoldt_tsum_re hx₀ χ.primitiveCharacter hsupp hLpos s).2
  have hTsub : Tχ - Tχ' = ∑' n : ℕ, (ArithmeticFunction.vonMangoldt n : ℂ) *
      ((χ (n : ZMod q) : ℂ) - (χ.primitiveCharacter (n : ZMod χ.conductor) : ℂ)) /
      (n : ℂ) ^ s * ((f (Real.log n / L) : ℝ) : ℂ) := by
    rw [hTχdef, hTχ'def, ← hsummχ.tsum_sub hsummχ']
    refine tsum_congr (fun n => ?_)
    simp only [div_eq_mul_inv]
    ring
  have hdiff : ‖Tχ - Tχ'‖ ≤ C * Kf * Real.exp (Real.sqrt (Real.log L)) * (Real.log L + 2) ^ 2 := by
    rw [hTsub]
    simpa only [hLdef] using hcorr
  have hKdiff : Tχ.re - Tχ'.re ≤ C * Kf * Real.exp (Real.sqrt (Real.log L)) * (Real.log L + 2) ^ 2 := by
    have h1 : Tχ.re - Tχ'.re = (Tχ - Tχ').re := by simp
    rw [h1]
    exact le_trans (Complex.re_le_norm _) hdiff
  have habs : C * Kf * Real.exp (Real.sqrt (Real.log L)) * (Real.log L + 2) ^ 2 ≤ f 0 * (ε / 4) * L := by
    have h1 := hab L hLe_ab
    have h2 : Real.exp (1 * Real.sqrt (Real.log L)) = Real.exp (Real.sqrt (Real.log L)) := by ring_nf
    rw [h2] at h1
    have h3 : (Real.log L + 2) ^ 2 ≤ (1 + Real.log L) ^ 5 := by
      have ha : Real.log L + 2 ≤ (1 + Real.log L) ^ 2 := by
        nlinarith only [hlogLge1, sq_nonneg (Real.log L)]
      have ha2 : (0:ℝ) ≤ Real.log L + 2 := by linarith only [hlogLge1]
      have hb : (1:ℝ) ≤ 1 + Real.log L := by linarith only [hlogLge1]
      calc (Real.log L + 2) ^ 2 ≤ ((1 + Real.log L) ^ 2) ^ 2 := pow_le_pow_left₀ ha2 ha 2
        _ = (1 + Real.log L) ^ 4 := by ring
        _ ≤ (1 + Real.log L) ^ 5 := pow_le_pow_right₀ hb (by norm_num)
    have h4 : 0 ≤ C * Kf * Real.exp (Real.sqrt (Real.log L)) :=
      mul_nonneg (mul_nonneg hCpos.le hKfnn) (Real.exp_nonneg _)
    calc C * Kf * Real.exp (Real.sqrt (Real.log L)) * (Real.log L + 2) ^ 2
        ≤ C * Kf * Real.exp (Real.sqrt (Real.log L)) * (1 + Real.log L) ^ 5 :=
          mul_le_mul_of_nonneg_left h3 h4
      _ ≤ f 0 * (ε / 4) * L := h1
  -- final assembly
  have hfin : ∑' n : ℕ, (ArithmeticFunction.vonMangoldt n : ℝ) *
      ((χ (n : ZMod q) / (n : ℂ) ^ s).re) * f (Real.log n / L)
      ≤ -L * (∑ᶠ u : ℂ, ((MeromorphicOn.divisor (DirichletCharacter.completedLFunction χ.primitiveCharacter) (Metric.closedBall 0 (|s.im| + 2))) u : ℤ) *
          (if ‖(1:ℂ) + (s.im : ℂ) * Complex.I - u‖ ≤ δ then
            ((∫ t in (0:ℝ)..x₀, Complex.exp (-(((s - u) * L) * (t : ℂ))) * ((f t : ℝ) : ℂ)).re) else 0))
        + f 0 * (c + ε) * L := by
    have h := hprim
    set S : ℝ := ∑ᶠ u : ℂ, ((MeromorphicOn.divisor (DirichletCharacter.completedLFunction χ.primitiveCharacter) (Metric.closedBall 0 (|s.im| + 2))) u : ℤ) *
          (if ‖(1:ℂ) + (s.im : ℂ) * Complex.I - u‖ ≤ δ then
            ((∫ t in (0:ℝ)..x₀, Complex.exp (-(((s - u) * L) * (t : ℂ))) * ((f t : ℝ) : ℂ)).re) else 0) with hSdef
    have h2 : Tχ'.re ≤ -L * S + f 0 * (c + ε/2) * L := by
      rw [hKχ']; exact h
    have key : f 0 * (c + ε/2) * L + f 0 * (ε/4) * L ≤ f 0 * (c + ε) * L := by
      have h1 : f 0 * (c + ε/2) * L + f 0 * (ε/4) * L
          = f 0 * ((c + ε/2) + ε/4) * L := by ring
      rw [h1]
      refine mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left ?_ hf0.le) hLpos.le
      linarith only [hε]
    rw [hSdef] at h2 ⊢
    calc (∑' n : ℕ, (ArithmeticFunction.vonMangoldt n : ℝ) *
          ((χ (n : ZMod q) / (n : ℂ) ^ s).re) * f (Real.log n / L))
        = Tχ.re := hKχ.symm
      _ ≤ Tχ'.re + (C * Kf * Real.exp (Real.sqrt (Real.log L)) * (Real.log L + 2) ^ 2) := by
          linarith only [hKdiff]
      _ ≤ Tχ'.re + f 0 * (ε/4) * L := add_le_add (le_refl _) habs
      _ ≤ ((-L * S) + f 0 * (c + ε/2) * L) + f 0 * (ε/4) * L :=
          add_le_add h2 (le_refl _)
      _ ≤ (-L * S) + f 0 * (c + ε) * L := by
          rw [show ((-L * S) + f 0 * (c + ε/2) * L) + f 0 * (ε/4) * L
                = (-L * S) + (f 0 * (c + ε/2) * L + f 0 * (ε/4) * L) from by ring]
          exact add_le_add (le_refl _) key
  simpa only [hLdef] using hfin

end Commons.NumberTheory.Linnik
