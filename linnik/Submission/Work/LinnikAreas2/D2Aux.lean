/-
# LinnikContract2 — Area 4, `(D2)` auxiliary layer

Auxiliary lemmas for the round-2 `(D2)` assembly (HB Lemma 12.1 ⟹ Table 13):
positivity/monotonicity of the Laplace transform for the §7 test function, the enumeration of the
characters carrying a box zero, the logarithmic thresholds, and the two `K`-sum identifications.
-/
import Mathlib
import Submission.Work.LinnikContract2.Contract
import Submission.Work.LinnikContract2.Bridge
import Submission.Work.LinnikAreas.Density4.hb_lemma12_1
import Submission.Work.LinnikAreas.Density4.Kbound_discharge
import Submission.Work.LinnikAreas.Density4.fTregular
import Submission.Work.LinnikAreas.Density4.fTcond2
import Submission.Work.LinnikAreas.Density4.testfun_basic
import Submission.Work.LinnikAreas.Density4.Parent
import Submission.Work.LinnikAreas.Density4.table13_cert
import Submission.Commons.NumberTheory.Linnik.Ksum_principal_le
import Submission.Work.NumberTheory.Linnik.scratch_l62app_phi
import Submission.Work.LinnikAreas.l31free.lemma3_1_free_gen

open DirichletCharacter Complex
open scoped Classical BigOperators
noncomputable section
set_option linter.unusedVariables false
set_option linter.style.haveILetI false

namespace Work.LinnikAreas2

open Work.LinnikAreas.Density4

/-! ## 1. The Laplace transform of the test function -/

/-- `FT` is `Lapl`, definitionally. -/
theorem FT_eq_Lapl (theta lam z : ℝ) : FT theta lam z = Lapl (2 * gammaT theta lam) (fT theta lam) z :=
  rfl

/-- The Laplace transform at a shifted real argument is strictly positive for a non-negative,
continuous, not-identically-zero test function on `[0,x₀]`. -/
theorem lapl_neg_arg_pos {x0 : ℝ} (hx0 : 0 < x0) {f : ℝ → ℝ}
    (hcont : ContinuousOn f (Set.Ici 0)) (hnn : ∀ t, 0 ≤ f t) (hf0 : 0 < f 0) (z : ℝ) :
    0 < Lapl x0 f (-z) := by
  rw [Lapl]
  refine intervalIntegral.integral_pos hx0 ?_ ?_ ?_
  · exact (by fun_prop : Continuous fun t : ℝ => Real.exp (-(-z * t))).continuousOn.mul
      (hcont.mono Set.Icc_subset_Ici_self)
  · intro t _
    exact mul_nonneg (Real.exp_pos _).le (hnn t)
  · exact ⟨0, ⟨le_rfl, hx0.le⟩, by simp only [mul_zero, neg_zero, Real.exp_zero, one_mul]; exact hf0⟩

/-- Antitonicity of `Lapl x₀ f` in the exponent, for a non-negative continuous `f`. -/
theorem lapl_antitone_on {x0 : ℝ} (hx0 : 0 ≤ x0) {f : ℝ → ℝ} (hcont : ContinuousOn f (Set.Ici 0))
    (hnn : ∀ t, 0 ≤ f t) {a b : ℝ} (hab : a ≤ b) : Lapl x0 f b ≤ Lapl x0 f a := by
  rw [Lapl, Lapl]
  have hca : ContinuousOn (fun t : ℝ => Real.exp (-(a * t)) * f t) (Set.Icc 0 x0) :=
    (by fun_prop : Continuous fun t : ℝ => Real.exp (-(a * t))).continuousOn.mul
      (hcont.mono Set.Icc_subset_Ici_self)
  have hcb : ContinuousOn (fun t : ℝ => Real.exp (-(b * t)) * f t) (Set.Icc 0 x0) :=
    (by fun_prop : Continuous fun t : ℝ => Real.exp (-(b * t))).continuousOn.mul
      (hcont.mono Set.Icc_subset_Ici_self)
  refine intervalIntegral.integral_mono_on hx0 ?_ ?_ ?_
  · exact (show ContinuousOn (fun t : ℝ => Real.exp (-(b * t)) * f t) (Set.uIcc 0 x0) from by
      rw [Set.uIcc_of_le hx0]; exact hcb).intervalIntegrable
  · exact (show ContinuousOn (fun t : ℝ => Real.exp (-(a * t)) * f t) (Set.uIcc 0 x0) from by
      rw [Set.uIcc_of_le hx0]; exact hca).intervalIntegrable
  intro t ht
  have h1 : Real.exp (-(b * t)) ≤ Real.exp (-(a * t)) :=
    Real.exp_le_exp.mpr (by nlinarith [ht.1, hab])
  exact mul_le_mul_of_nonneg_right h1 (hnn t)

/-- `∫₀^{x₀} e^{z t} f t = Lapl x₀ f (-z)`. -/
theorem integral_exp_mul_eq_lapl (x0 z : ℝ) (f : ℝ → ℝ) :
    (∫ t in (0:ℝ)..x0, Real.exp (z * t) * f t) = Lapl x0 f (-z) := by
  rw [Lapl]
  refine intervalIntegral.integral_congr (fun t _ => ?_)
  rw [neg_mul, neg_neg]

/-! ## 2. `Kgen` identifications -/

/-- `Kgen` at real point `β` and the principal character, in the shape used by HB Lemma 5.3. -/
theorem Kgen_real_eq {q : ℕ} [NeZero q] (L β : ℝ) (f : ℝ → ℝ) :
    Kgen q L β 0 f (1 : DirichletCharacter ℂ q)
      = ∑' n : ℕ, (ArithmeticFunction.vonMangoldt n : ℝ) *
          (((1 : DirichletCharacter ℂ q) (n : ZMod q) / (n : ℂ) ^ (β : ℂ)).re)
          * f (Real.log n / L) := by
  rw [Kgen]
  refine tsum_congr (fun n => ?_)
  rcases eq_or_ne n 0 with rfl | hn
  · simp
  · rw [show (-(β : ℂ) - (((0:ℝ) : ℂ)) * Complex.I) = -(β : ℂ) by simp, Complex.cpow_neg]
    rfl

/-- `Kgen` at the complex point `β + i t` in the shape used by HB Lemma 5.2. -/
theorem Kgen_complex_eq {q : ℕ} [NeZero q] (L β t : ℝ) (f : ℝ → ℝ) (chi : DirichletCharacter ℂ q) :
    Kgen q L β t f chi
      = ∑' n : ℕ, (ArithmeticFunction.vonMangoldt n : ℝ) *
          ((chi (n : ZMod q) / (n : ℂ) ^ ((β : ℂ) + (t : ℂ) * Complex.I)).re)
          * f (Real.log n / L) := by
  rw [Kgen]
  refine tsum_congr (fun n => ?_)
  rcases eq_or_ne n 0 with rfl | hn
  · simp
  · rw [show (-(β : ℂ) - (t : ℂ) * Complex.I) = -((β : ℂ) + (t : ℂ) * Complex.I) by ring,
      Complex.cpow_neg]
    rfl

/-! ## 3. Enumeration of the characters carrying a box zero -/

/-- The units of `ZMod N` for `N ≤ 2` form a subsingleton. -/
theorem subsingleton_units_zmod_of_le_two {N : ℕ} (hN1 : 1 ≤ N) (hN : N ≤ 2) :
    Subsingleton (ZMod N)ˣ := by
  interval_cases N <;> infer_instance

/-- A non-principal character mod `N` has level at least `3`. -/
theorem three_le_conductor {q : ℕ} [NeZero q] (chi : DirichletCharacter ℂ q) (hchi : chi ≠ 1) :
    3 ≤ chi.conductor := by
  haveI : NeZero chi.conductor := ⟨chi.conductor_ne_zero⟩
  have hchi' : chi.primitiveCharacter ≠ 1 := by
    intro h
    apply hchi
    rw [← DirichletCharacter.changeLevel_primitiveCharacter chi, h]
    exact DirichletCharacter.changeLevel_one chi.conductor_dvd_level
  by_contra hcon
  have hN2 : chi.conductor ≤ 2 := by omega
  have hN1 : 1 ≤ chi.conductor := Nat.one_le_iff_ne_zero.mpr chi.conductor_ne_zero
  have hs : Subsingleton (ZMod chi.conductor)ˣ := subsingleton_units_zmod_of_le_two hN1 hN2
  have hne : ¬ (∀ a : (ZMod chi.conductor)ˣ, chi.primitiveCharacter ↑a
      = (1 : DirichletCharacter ℂ chi.conductor) ↑a) := by
    intro hh
    exact hchi' (MulChar.ext hh)
  push Not at hne
  obtain ⟨a, hne⟩ := hne
  have ha : a = 1 := Subsingleton.elim a 1
  subst ha
  simp at hne

/-- **Enumeration.**  A finset of characters each carrying a working-region zero with `λ ≤ lam`
admits an injective `Fin S.card`-indexing, together with chosen zeros. -/
theorem exists_enum {q : ℕ} [NeZero q] (lam : ℝ) (S : Finset (DirichletCharacter ℂ q))
    (hS : ∀ chi ∈ S, ∃ rho, Work.LinnikContract2.IsZ chi rho ∧
      Work.LinnikContract2.lamOf q rho ≤ lam) :
    ∃ (chi : Fin S.card → DirichletCharacter ℂ q) (rho : Fin S.card → ℂ),
      Function.Injective chi ∧ (∀ j, Work.LinnikContract2.IsZ (chi j) (rho j)) ∧
      (∀ j, Work.LinnikContract2.lamOf q (rho j) ≤ lam) := by
  classical
  have hlen : S.toList.length = S.card := by
    rw [Finset.toList]
    exact Multiset.length_toList _
  let e : Fin S.toList.length ≃ {x // x ∈ S.toList} := List.Nodup.getEquiv S.toList (Finset.nodup_toList S)
  let chi : Fin S.card → DirichletCharacter ℂ q := fun j => (e (Fin.cast hlen.symm j)).1
  have hchi_mem : ∀ j, chi j ∈ S :=
    fun j => Finset.mem_toList.mp (e (Fin.cast hlen.symm j)).2
  have hchi_inj : Function.Injective chi := by
    intro j k hjk
    have h1 : e (Fin.cast hlen.symm j) = e (Fin.cast hlen.symm k) := Subtype.ext hjk
    have h2 : Fin.cast hlen.symm j = Fin.cast hlen.symm k := e.injective h1
    exact Fin.cast_injective hlen.symm h2
  let rho : Fin S.card → ℂ := fun j => Classical.choose (hS (chi j) (hchi_mem j))
  refine ⟨chi, rho, hchi_inj, fun j => (Classical.choose_spec (hS (chi j) (hchi_mem j))).1,
    fun j => (Classical.choose_spec (hS (chi j) (hchi_mem j))).2⟩

/-! ## 4. Logarithmic thresholds -/

/-- For large `q`, `λ ≤ lamMax q`. -/
theorem exists_threshold_lamMax (lam : ℝ) (hlam : 0 ≤ lam) :
    ∃ Q : ℕ, ∀ q : ℕ, Q ≤ q → lam ≤ Work.LinnikContract2.lamMax q := by
  refine ⟨Nat.ceil (Real.exp (Real.exp (Real.exp (3 * lam)))) + 1, ?_⟩
  intro q hq
  have hq1 : (1 : ℝ) ≤ (q : ℝ) := by
    have : 1 ≤ q := by omega
    exact_mod_cast this
  have hq0 : (0 : ℝ) < (q : ℝ) := by linarith
  have hceil : Real.exp (Real.exp (Real.exp (3 * lam))) ≤ (q : ℝ) := by
    have h1 : Real.exp (Real.exp (Real.exp (3 * lam)))
        ≤ (Nat.ceil (Real.exp (Real.exp (Real.exp (3 * lam)))) : ℝ) := Nat.le_ceil _
    have h2 : (Nat.ceil (Real.exp (Real.exp (Real.exp (3 * lam)))) : ℝ) ≤ (q : ℝ) := by
      have : Nat.ceil (Real.exp (Real.exp (Real.exp (3 * lam)))) ≤ q := by omega
      exact_mod_cast this
    linarith
  have hA : Real.exp (Real.exp (3 * lam)) ≤ Real.log (q : ℝ) := by
    calc Real.exp (Real.exp (3 * lam)) = Real.log (Real.exp (Real.exp (Real.exp (3 * lam)))) :=
          (Real.log_exp _).symm
      _ ≤ Real.log (q : ℝ) := Real.log_le_log (Real.exp_pos _) hceil
  have hApos : 0 < Real.exp (Real.exp (3 * lam)) := Real.exp_pos _
  have hB : Real.exp (3 * lam) ≤ Real.log (Real.log (q : ℝ)) := by
    calc Real.exp (3 * lam) = Real.log (Real.exp (Real.exp (3 * lam))) := (Real.log_exp _).symm
      _ ≤ Real.log (Real.log (q : ℝ)) := Real.log_le_log hApos hA
  have hC : 3 * lam ≤ Real.log (Real.log (Real.log (q : ℝ))) := by
    calc 3 * lam = Real.log (Real.exp (3 * lam)) := (Real.log_exp _).symm
      _ ≤ Real.log (Real.log (Real.log (q : ℝ))) := Real.log_le_log (Real.exp_pos _) hB
  rw [Work.LinnikContract2.lamMax]
  linarith

/-- For large `q`, `1 ≤ log log q`. -/
theorem exists_threshold_loglog : ∃ Q : ℕ, ∀ q : ℕ, Q ≤ q → 1 ≤ Real.log (Real.log (q : ℝ)) := by
  refine ⟨Nat.ceil (Real.exp (Real.exp 1)) + 1, ?_⟩
  intro q hq
  have hq0 : (0 : ℝ) < (q : ℝ) := by
    have : 1 ≤ q := by omega
    exact_mod_cast (by omega : 0 < q)
  have hceil : Real.exp (Real.exp 1) ≤ (q : ℝ) := by
    have h1 : Real.exp (Real.exp 1) ≤ (Nat.ceil (Real.exp (Real.exp 1)) : ℝ) := Nat.le_ceil _
    have h2 : (Nat.ceil (Real.exp (Real.exp 1)) : ℝ) ≤ (q : ℝ) := by
      have : Nat.ceil (Real.exp (Real.exp 1)) ≤ q := by omega
      exact_mod_cast this
    linarith
  have hA : Real.exp 1 ≤ Real.log (q : ℝ) := by
    calc Real.exp 1 = Real.log (Real.exp (Real.exp 1)) := (Real.log_exp _).symm
      _ ≤ Real.log (q : ℝ) := Real.log_le_log (Real.exp_pos _) hceil
  calc (1:ℝ) = Real.log (Real.exp 1) := (Real.log_exp 1).symm
    _ ≤ Real.log (Real.log (q : ℝ)) := Real.log_le_log (Real.exp_pos 1) hA

end Work.LinnikAreas2
