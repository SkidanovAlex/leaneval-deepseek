/-
# ZeroFreeTables/HB94/L52supply — the analytic inputs of Lemma 9.4, `sorry`-free

This file rebuilds the Area-1 chain (Burgess ⇒ HB Lemma 2.5 with `φ = 1/3` ⇒ HB Lemma 3.1 in the
window form `L52Hyp χ (1/6) ε δ`) **without** the two `sorry`-tainted links of the workspace:

* `Work.LinnikBurgess.localFactor_bound_small` (the `e ≥ 13` regime of the small-prime local factor)
  is replaced by the `sorry`-free re-emission `Work.ZeroFreeTables.P9F.localFactor_bound_small_aux`;
* the counting Theorem F (`frame_count`) is taken from `Work.LinnikBurgess.frame_count` instead of
  the stub `Work.ZeroFreeTables.P9F.frame_stub_aux`.

Everything else is a verbatim copy of the assemblies in `Work.ZeroFreeTables.P9F.Chain.*`
(`Work.LinnikAreas.area1` for the `φ = 1/3` step), with the constant bookkeeping of
`Work.ZeroFreeTables.P9F.Chain.supply` adjusted so that the conclusion is *exactly*
`L52Hyp χ (1/6) (1/1000000) δ` — the form consumed by the Lemma-9.2/9.3 engines.
-/
import Mathlib
import Submission.Work.ZeroFreeTables.P9F.Chain.ssa
import Submission.Work.ZeroFreeTables.P9F.Chain.burg
import Submission.Work.ZeroFreeTables.P9F.localFactor_bound_small_aux
import Submission.Work.LinnikBurgess.frame_count
import Submission.Work.LinnikContract.Areas
import Submission.Commons.NumberTheory.DirichletCharacter.burgess_moment_cubefree_r3
import Submission.Commons.NumberTheory.DirichletCharacter.burgess_charSum_uniform_of_moment_eps23
import Submission.Commons.NumberTheory.DirichletCharacter.LFunction_bound_third_of_burgess
import Submission.Work.LinnikAreas.l31free.lemma3_1_free_gen
import Submission.Work.NumberTheory.Linnik.scratch_l62app_phi

open DirichletCharacter
open scoped BigOperators
noncomputable section

namespace Work.ZeroFreeTables.HB94

open Commons.NumberTheory.DirichletCharacter
open Work.P9Chain
open Work.LinnikBurgess

/-- **U13**, with the `sorry`-free local-factor input: the singleton-pair sixth-moment bound, from
the `_aux` assembly `Work.P9Chain.singleton_sum_all_aux` fed with
`Work.ZeroFreeTables.P9F.localFactor_bound_small_aux` (`p ≤ 3`) and `Work.LinnikBurgess.frame_count`. -/
theorem singleton_sum_all_clean {ε : ℝ} (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ {q : ℕ} [NeZero q], ∀ (χ : DirichletCharacter ℂ q), χ.IsPrimitive →
      χ ≠ 1 → ∀ H : ℕ,
        ∑ f : Fin 3 → Fin H, ∑ g : Fin 3 → Fin H,
          (if IsSingleton6 (f, g) then ‖corr6 q χ f g‖ else 0)
        ≤ C * (q : ℝ) ^ ε * ((q : ℝ) * (H : ℝ) ^ 3 + (H : ℝ) ^ 6 * Real.sqrt (q : ℝ)) :=
  Work.P9Chain.singleton_sum_all_aux
    (fun p _ χ hχ a b i => local_prime_powOne_bound χ hχ a b i)
    (fun {p e} _ hp5 he χ hχ a b i hi => localFactor_bound_ge5 hp5 he χ hχ a b i hi)
    (fun {p e} _ hp3 he χ hχ a b i hi =>
      Work.ZeroFreeTables.P9F.localFactor_bound_small_aux hp3 he χ hχ a b i hi)
    (fun {H} i {m d g} hm hmd hmg hd hg =>
      Work.LinnikBurgess.frame_count (H := H) i hm hmd hmg hd hg)
    (fun q i v => sqrtGcdW_prod_le_sqfreePart q i v)
    (fun {q} hq => sqrt_prod_factorization hq)
    (fun {q d g} hq h => divisors_card_pow_le hq h)
    (fun {q} hq σ hσ => sqfreePart_frame_hyp hq σ hσ)
    (fun {q} hq {d} hd => divisor_bounds_high hq hd)
    (fun {q H} => sqrt_mul_sum_le (q := q) (H := H))
    hε

/-- **The sixth moment of Burgess for moduli divisible by a cube**, from the `sorry`-free
singleton bound above. -/
theorem burgess_r3_noncubefree_clean {ε : ℝ} (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ {q : ℕ} [NeZero q], (∃ p : ℕ, p.Prime ∧ p ^ 3 ∣ q) →
      ∀ (χ : DirichletCharacter ℂ q), χ.IsPrimitive → χ ≠ 1 → ∀ H : ℕ, H ^ 6 ≤ q →
        ∑ m ∈ Finset.range q, ‖∑ h ∈ Finset.Ioc m (m + H), χ (h : ZMod q)‖ ^ 6
          ≤ C * (q : ℝ) ^ ε * ((q : ℝ) * (H : ℝ) ^ 3 + (H : ℝ) ^ 6 * Real.sqrt (q : ℝ)) := by
  obtain ⟨C, hC, h⟩ := singleton_sum_all_clean hε
  refine Work.P9Chain.burgess_r3_noncubefree_of_singleton hε ⟨C, hC, ?_⟩
  intro q _ hcube χ hprim hne H hH
  exact h χ hprim hne H

/-- The sixth moment of Burgess for **every** modulus. -/
theorem cubic_moment_all_clean (ε : ℝ) (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q),
      χ.IsPrimitive → χ ≠ 1 → ∀ H : ℕ, H ^ 6 ≤ q →
        ∑ m ∈ Finset.range q, ‖∑ h ∈ Finset.Ioc m (m + H), χ (h : ZMod q)‖ ^ 6
          ≤ C * (q : ℝ) ^ ε * ((q : ℝ) * (H : ℝ) ^ 3 + (H : ℝ) ^ 6 * Real.sqrt (q : ℝ)) := by
  obtain ⟨C₁, hC₁, h₁⟩ := burgess_moment_cubefree_r3 hε
  obtain ⟨C₂, hC₂, h₂⟩ := burgess_r3_noncubefree_clean hε
  refine ⟨max C₁ C₂, lt_max_of_lt_left hC₁, ?_⟩
  intro q _inst χ hp hχ H hH
  have hqε : (0 : ℝ) ≤ (q : ℝ) ^ ε := Real.rpow_nonneg (Nat.cast_nonneg q) _
  have hX : (0 : ℝ) ≤ (q : ℝ) * (H : ℝ) ^ 3 + (H : ℝ) ^ 6 * Real.sqrt (q : ℝ) := by positivity
  by_cases hcube : ∃ p : ℕ, p.Prime ∧ p ^ 3 ∣ q
  · refine (h₂ hcube χ hp hχ H hH).trans ?_
    exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right (le_max_right C₁ C₂) hqε) hX
  · have hcf : ∀ p : ℕ, p.Prime → ¬ p ^ 3 ∣ q := fun p hp hp3 => hcube ⟨p, hp, hp3⟩
    refine (h₁ hcf χ hp hχ H hH).trans ?_
    exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right (le_max_left C₁ C₂) hqε) hX

/-- Uniform Burgess character sum with `k = 3`. -/
theorem charSum_three_uniform_clean (ε : ℝ) (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q),
      χ.IsPrimitive → χ ≠ 1 → ∀ {N H : ℕ}, 1 ≤ N → 1 ≤ H → H ≤ q →
        ‖∑ n ∈ Finset.Ioc N (N + H), χ n‖ ≤
          C * (q : ℝ) ^ ((1 : ℝ) / 9 + ε) * (H : ℝ) ^ ((2 : ℝ) / 3) := by
  obtain ⟨C, hC, h⟩ :=
    burgess_charSum_uniform_of_moment_single_eps 3 (Or.inr rfl)
      (fun ε' hε' => cubic_moment_all_clean ε' hε') hε
  refine ⟨C, hC, ?_⟩
  intro q _inst χ hp hχ N H hN hH hHq
  have hhexp : ((((3 : ℕ) : ℝ) + 1) / (4 * (((3 : ℕ) : ℝ)) ^ 2)) + ε = (1 : ℝ) / 9 + ε := by
    norm_num
  have hhexp2 : (1 : ℝ) - 1 / (((3 : ℕ) : ℝ)) = (2 : ℝ) / 3 := by norm_num
  refine (h χ hp hχ hN hH hHq).trans (le_of_eq ?_)
  rw [hhexp, hhexp2]

/-- **HB Lemma 2.5 with `φ = 1/3`** (the first conjunct of Area 1), `sorry`-free. -/
theorem LBound13_clean : Work.LinnikContract.LBound13 := by
  intro k hk ε' hε'
  have hε4 : (0 : ℝ) < ε' / 4 := by positivity
  have hε2 : (0 : ℝ) < ε' / 2 := by positivity
  obtain ⟨C₃, hC₃, h₃⟩ := charSum_three_uniform_clean (ε' / 4) hε4
  have hB : ∀ {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q), χ.IsPrimitive → χ ≠ 1 →
      ∀ {N H : ℕ}, 1 ≤ N → 1 ≤ H → H ≤ q →
        ‖∑ n ∈ Finset.Ioc N (N + H), χ n‖
          ≤ C₃ * (q : ℝ) ^ ((1 : ℝ) / 9 + ε' / 2) * (H : ℝ) ^ ((2 : ℝ) / 3) := by
    intro q _inst χ hp hχ N H hN hH hHq
    have hq1 : (1 : ℝ) ≤ (q : ℝ) := by exact_mod_cast Nat.one_le_iff_ne_zero.mpr (NeZero.ne q)
    have hstep : (q : ℝ) ^ ((1 : ℝ) / 9 + ε' / 4) ≤ (q : ℝ) ^ ((1 : ℝ) / 9 + ε' / 2) :=
      Real.rpow_le_rpow_of_exponent_le hq1 (by linarith)
    refine (h₃ χ hp hχ hN hH hHq).trans ?_
    exact mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_left hstep (le_of_lt hC₃)) (by positivity)
  obtain ⟨C, hC, hbound⟩ := LFunction_bound_third_of_burgess (ε := ε' / 2) hε2 k hk hC₃ hB
  refine ⟨C, hC, ?_⟩
  intro N _inst χ hχ σ t hσ hσle
  have hN1 : (1 : ℝ) ≤ (N : ℝ) := by exact_mod_cast Nat.one_le_iff_ne_zero.mpr (NeZero.ne N)
  have hstep : (N : ℝ) ^ (((1 : ℝ) / 3) * (1 - σ) * (1 + 1 / (k : ℝ)) + ε' / 2)
      ≤ (N : ℝ) ^ (((1 : ℝ) / 3) * (1 - σ) * (1 + 1 / (k : ℝ)) + ε') :=
    Real.rpow_le_rpow_of_exponent_le hN1 (by linarith)
  refine (hbound χ hχ σ t hσ hσle).trans ?_
  exact mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_left hstep (le_of_lt hC)) (by positivity)

/-- **HB Lemma 3.1 in the window form with the constant `c = 1/6`.**

`L52Hyp χ (1/6) (1/1000000) δ` is the bound `(1/6 + 1/4000000) log q`, which is exactly the
conclusion of HB's Lemma 3.1 at `φ = 1/3`, `ε = 1/4000000`. -/
theorem L52supply16 :
    ∃ δ : ℝ, 0 < δ ∧ δ < 1 ∧ ∃ q₀ : ℕ, ∀ q : ℕ, q₀ ≤ q →
      ∀ [NeZero q] (χ : DirichletCharacter ℂ q) [NeZero χ.conductor], χ ≠ 1 →
        Commons.NumberTheory.Linnik.L52Hyp χ ((1:ℝ)/6) (1/1000000) δ := by
  obtain ⟨L₀, δ, hδpos, hδ1, hmain⟩ :=
    Work.LinnikAreas.l31free.lemma3_1_free_gen (φ := (1 : ℝ)/3) (by norm_num)
      (ε := 1/4000000) (by norm_num) LBound13_clean
  refine ⟨δ, hδpos, hδ1, ⌈Real.exp L₀⌉₊ + 3, ?_⟩
  intro q hq _inst χ _instc hχ s hsre1 hsre2 hsim
  have hqpos : 0 < q := Nat.pos_of_ne_zero (NeZero.ne q)
  have hexp_le : Real.exp L₀ ≤ (q : ℝ) := by
    have h1 : Real.exp L₀ ≤ (⌈Real.exp L₀⌉₊ : ℝ) := Nat.le_ceil _
    have h2 : (⌈Real.exp L₀⌉₊ : ℝ) ≤ ((⌈Real.exp L₀⌉₊ + 3 : ℕ) : ℝ) := by push_cast; linarith
    have h3 : ((⌈Real.exp L₀⌉₊ + 3 : ℕ) : ℝ) ≤ (q : ℝ) := by exact_mod_cast hq
    linarith
  have hL₀le : L₀ ≤ Real.log (q : ℝ) := by
    rw [← Real.log_exp L₀]
    exact Real.log_le_log (Real.exp_pos L₀) hexp_le
  have hχ' : χ.primitiveCharacter ≠ 1 := by
    intro h
    apply hχ
    rw [← DirichletCharacter.changeLevel_primitiveCharacter χ, h]
    exact DirichletCharacter.changeLevel_one χ.conductor_dvd_level
  have hcon : 3 ≤ χ.conductor := by
    have h := Work.LinnikAreas.l31free.three_le_of_char_ne_one χ.primitiveCharacter hχ'
    exact_mod_cast h
  have hconle : χ.conductor ≤ q := Nat.le_of_dvd hqpos χ.conductor_dvd_level
  have hNL : Real.log ((χ.conductor : ℕ) : ℝ) ≤ Real.log (q : ℝ) := by
    apply Real.log_le_log
    · exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne χ.conductor)
    · exact_mod_cast hconle
  have h1 := hmain (N := χ.conductor) hcon χ.primitiveCharacter hχ'
    (DirichletCharacter.primitiveCharacter_isPrimitive χ) (L := Real.log (q : ℝ))
    hL₀le hNL s hsre1 hsre2 hsim
  have hlogq : 0 ≤ Real.log (q : ℝ) := by
    refine Real.log_nonneg ?_
    have hq1 : 1 ≤ q := Nat.one_le_iff_ne_zero.mpr (NeZero.ne q)
    exact_mod_cast hq1
  refine le_trans h1 ?_
  have hc : (1 : ℝ)/3/2 + 1/4000000 ≤ (1:ℝ)/6 + (1/1000000)/4 := by norm_num
  exact mul_le_mul_of_nonneg_right hc hlogq

end Work.ZeroFreeTables.HB94
