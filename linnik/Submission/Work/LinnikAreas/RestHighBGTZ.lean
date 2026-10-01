import Mathlib
import Submission.Work.LinnikAreas.BGTZ
import Submission.Work.LinnikAreas.SiegelBase
import Submission.Work.LinnikAreas.pairCountHeight_le_famCount
import Submission.Work.LinnikAreas.sum_mul_exp_neg_le_of_count
import Submission.Work.LinnikAreas.siegelRestHigh
import Submission.Work.LinnikAreas.pairCountHeight_dom
import Submission.Work.LinnikAreas.windowMassFloor
import Submission.Work.LinnikAreas.highFinsetBoundFree
import Submission.Work.LinnikAreas.lamOfEps200

namespace Work.LinnikAreas
open DirichletCharacter Complex
open scoped Classical BigOperators
noncomputable section
open Work.LinnikContract
set_option linter.unusedVariables false

/-! ## The two auxiliary lemmas proved locally (the `BGTZ` repulsion floor and the elementary
`(24u)^{12/(5u)}` bound). -/

theorem algPow_own {u A : ℝ} (hu : 4 / 3 + 1 / 100 ≤ u) :
    Real.exp (-(12 / 5) * ((A - Real.log (24 * u)) / u))
      ≤ Real.exp 58 * (Real.exp (-A)) ^ (12 / (5 * u)) := by
  have hu0 : 0 < u := by linarith
  have h24 : 0 < 24 * u := by positivity
  have hsplit : Real.exp (-(12 / 5) * ((A - Real.log (24 * u)) / u))
      = Real.exp (-(12 / (5 * u) * A)) * Real.exp (12 / (5 * u) * Real.log (24 * u)) := by
    rw [← Real.exp_add]
    congr 1
    field_simp
    ring
  have h3 : Real.exp (-(12 / (5 * u) * A)) = (Real.exp (-A)) ^ (12 / (5 * u)) := by
    rw [Real.rpow_def_of_pos (Real.exp_pos _), Real.log_exp]
    congr 1
    ring
  have h4 : Real.exp (12 / (5 * u) * Real.log (24 * u)) ≤ Real.exp 58 := by
    rw [Real.exp_le_exp]
    have h5 : Real.log (24 * u) ≤ 24 * u := by
      have h6 := Real.log_le_sub_one_of_pos h24
      linarith
    have h7 : 0 ≤ 12 / (5 * u) := by positivity
    have h8 := mul_le_mul_of_nonneg_left h5 h7
    have h9 : 12 / (5 * u) * (24 * u) = 288 / 5 := by field_simp; ring
    linarith
  calc Real.exp (-(12 / 5) * ((A - Real.log (24 * u)) / u))
      = (Real.exp (-A)) ^ (12 / (5 * u)) * Real.exp (12 / (5 * u) * Real.log (24 * u)) := by
        rw [hsplit, h3]
    _ ≤ (Real.exp (-A)) ^ (12 / (5 * u)) * Real.exp 58 :=
        mul_le_mul_of_nonneg_left h4 (Real.rpow_nonneg (Real.exp_pos _).le _)
    _ = Real.exp 58 * (Real.exp (-A)) ^ (12 / (5 * u)) := by ring

theorem repulsionFloorHi_own {q : ℕ} [NeZero q] (χ₁ : DirichletCharacter ℂ q) (β₁ : ℝ) {H : ℝ}
    (hH : 1 ≤ H)
    (hrep : ∀ (χ : DirichletCharacter ℂ q) (ρ : ℂ), zeroMult χ ρ ≠ 0 →
      ¬(χ = χ₁ ∧ ρ = (β₁ : ℂ)) →
      (Real.log (1 / lamOf q (β₁ : ℂ))
          - Real.log (24 * ((4 / 3 + 1 / 100 : ℝ)
              + (2 / 3 + 1 / 100 : ℝ) * (Real.log (5 + |ρ.im|) / Real.log q))))
        / ((4 / 3 + 1 / 100 : ℝ)
            + (2 / 3 + 1 / 100 : ℝ) * (Real.log (5 + |ρ.im|) / Real.log q))
        ≤ lamOf q ρ)
    (hfloor0 : 24 * ((4 / 3 + 1 / 100 : ℝ)
        + (2 / 3 + 1 / 100 : ℝ) * (Real.log (5 + H) / Real.log q))
        ≤ 1 / lamOf q (β₁ : ℂ))
    (hq1 : 1 < q) {χ : DirichletCharacter ℂ q} {ρ : ℂ}
    (hzm : zeroMult χ ρ ≠ 0) (him : |ρ.im| ≤ H)
    (hne : ¬(χ = χ₁ ∧ ρ = (β₁ : ℂ))) :
    (Real.log (1 / lamOf q (β₁ : ℂ))
        - Real.log (24 * ((4 / 3 + 1 / 100 : ℝ)
            + (2 / 3 + 1 / 100 : ℝ) * (Real.log (5 + H) / Real.log q))))
      / ((4 / 3 + 1 / 100 : ℝ)
          + (2 / 3 + 1 / 100 : ℝ) * (Real.log (5 + H) / Real.log q))
      ≤ lamOf q ρ := by
  set U : ℝ := (4 / 3 + 1 / 100 : ℝ)
      + (2 / 3 + 1 / 100 : ℝ) * (Real.log (5 + H) / Real.log q) with hUdef
  set Uρ : ℝ := (4 / 3 + 1 / 100 : ℝ)
      + (2 / 3 + 1 / 100 : ℝ) * (Real.log (5 + |ρ.im|) / Real.log q) with hUρdef
  have hc2 : (0 : ℝ) ≤ 2 / 3 + 1 / 100 := by norm_num
  have hc1 : (0 : ℝ) < 4 / 3 + 1 / 100 := by norm_num
  have him5 : (0 : ℝ) < 5 + |ρ.im| := by positivity
  have hH5 : (0 : ℝ) < 5 + H := by linarith
  have hlogρ : Real.log (5 + |ρ.im|) ≤ Real.log (5 + H) := Real.log_le_log him5 (by linarith)
  have hlogq_pos : 0 < Real.log (q : ℝ) := Real.log_pos (by exact_mod_cast hq1)
  have hUρleU : Uρ ≤ U := by
    rw [hUdef, hUρdef]
    have h := mul_le_mul_of_nonneg_left (div_le_div_of_nonneg_right hlogρ hlogq_pos.le) hc2
    linarith
  have hUρpos : 0 < Uρ := by
    rw [hUρdef]
    have h1 : (1 : ℝ) ≤ 5 + |ρ.im| := by have := abs_nonneg ρ.im; linarith
    have h2 : 0 ≤ Real.log (5 + |ρ.im|) := Real.log_nonneg h1
    have h3 : 0 ≤ Real.log (5 + |ρ.im|) / Real.log (q : ℝ) := div_nonneg h2 hlogq_pos.le
    have h4 : (0 : ℝ) ≤ (2 / 3 + 1 / 100) * (Real.log (5 + |ρ.im|) / Real.log (q : ℝ)) :=
      mul_nonneg hc2 h3
    linarith
  have hUpos : 0 < U := lt_of_lt_of_le hUρpos hUρleU
  have hlampos : 0 < lamOf q (β₁ : ℂ) := by
    have h1 : 0 < 1 / lamOf q (β₁ : ℂ) :=
      lt_of_lt_of_le (by linarith [hUpos] : (0 : ℝ) < 24 * U) hfloor0
    exact one_div_pos.mp h1
  set A : ℝ := Real.log (1 / lamOf q (β₁ : ℂ)) with hAdef
  have h24U : Real.log (24 * U) ≤ A := by
    rw [hAdef]
    rw [Real.log_le_iff_le_exp (by positivity), Real.exp_log (by positivity)]
    exact hfloor0
  have hrepρ := hrep χ ρ hzm hne
  have hmono : (A - Real.log (24 * U)) / U ≤ (A - Real.log (24 * Uρ)) / Uρ := by
    rw [div_le_div_iff₀ hUpos hUρpos]
    have h1 : Real.log (24 * Uρ) ≤ Real.log (24 * U) :=
      Real.log_le_log (by positivity) (by linarith)
    calc (A - Real.log (24 * U)) * Uρ ≤ (A - Real.log (24 * U)) * U :=
          mul_le_mul_of_nonneg_left hUρleU (by linarith)
      _ ≤ (A - Real.log (24 * Uρ)) * U :=
          mul_le_mul_of_nonneg_right (by linarith) hUpos.le
  rw [hUdef, hUρdef] at hmono
  rw [hAdef] at hmono
  exact hmono.trans hrepρ


private noncomputable def jjF {q : ℕ} (z : DirichletCharacter ℂ q × ℂ) : ℕ :=
  Nat.log 2 (Nat.floor |z.2.im|)

private lemma dyadic_key_free (j : ℕ) :
    ((2 : ℝ) ^ (j + 1)) ^ (3 / 2 : ℝ) * ((4 : ℝ) ^ j)⁻¹
      = (2 : ℝ) ^ (3 / 2 : ℝ) * ((2 : ℝ) ^ (-(1 / 2) : ℝ)) ^ j := by
  have h4 : ((4 : ℝ) ^ j)⁻¹ = (2 : ℝ) ^ (-(2 * (j : ℝ))) := by
    rw [show (4 : ℝ) ^ j = (2 : ℝ) ^ (2 * (j : ℝ)) by
          rw [show (4 : ℝ) = (2 : ℝ) ^ 2 by norm_num, ← pow_mul,
            ← Real.rpow_natCast 2 (2 * j)]
          push_cast; ring]
    rw [← Real.rpow_neg (by norm_num : (0 : ℝ) ≤ 2)]
  have h2 : ((2 : ℝ) ^ (j + 1)) ^ (3 / 2 : ℝ)
      = (2 : ℝ) ^ ((3 / 2 : ℝ) * (1 + (j : ℝ))) := by
    rw [← Real.rpow_natCast (2 : ℝ) (j + 1), ← Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 2)]
    congr 1
    push_cast
    ring
  calc ((2 : ℝ) ^ (j + 1)) ^ (3 / 2 : ℝ) * ((4 : ℝ) ^ j)⁻¹
      = (2 : ℝ) ^ ((3 / 2 : ℝ) * (1 + (j : ℝ))) * (2 : ℝ) ^ (-(2 * (j : ℝ))) := by
        rw [h2, h4]
    _ = (2 : ℝ) ^ ((3 / 2 : ℝ) * (1 + (j : ℝ)) + -(2 * (j : ℝ))) := by
        rw [Real.rpow_add (by norm_num : (0 : ℝ) < 2)]
    _ = (2 : ℝ) ^ ((3 / 2 : ℝ) + (j : ℝ) * (-(1 / 2))) := by
        congr 1; ring
    _ = (2 : ℝ) ^ (3 / 2 : ℝ) * (2 : ℝ) ^ ((j : ℝ) * (-(1 / 2))) := by
        rw [Real.rpow_add (by norm_num : (0 : ℝ) < 2)]
    _ = (2 : ℝ) ^ (3 / 2 : ℝ) * ((2 : ℝ) ^ (-(1 / 2) : ℝ)) ^ j := by
        congr 1
        rw [← Real.rpow_natCast ((2 : ℝ) ^ (-(1 / 2) : ℝ)) j,
          ← Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 2)]
        congr 1
        push_cast
        ring

/-- Termwise kernel bound with the dyadic height index. -/
private lemma kernel_le {q : ℕ} [NeZero q] (hq : 1 < q) (z : DirichletCharacter ℂ q × ℂ)
    (hzm : zeroMult z.1 z.2 ≠ 0) (hhigh : 1 < |z.2.im|) :
    (zeroMult z.1 z.2 : ℝ) * ‖Hk (11 / 2) (3 / 10) ((1 - z.2) * (Real.log q : ℂ))‖
      ≤ 4 / ((4 : ℝ) ^ (jjF z) * (Real.log (q : ℝ)) ^ 2)
        * ((zeroMult z.1 z.2 : ℝ) * Real.exp (-(49 / 10) * lamOf q z.2)) := by
  have hlog : 0 < Real.log (q : ℝ) := Real.log_pos (by exact_mod_cast hq)
  have hker := high_kernel_le hq z hzm hhigh
  have himpos : 0 < |z.2.im| := by linarith
  have h4 : (4 : ℝ) ^ (jjF z) ≤ |z.2.im| ^ 2 := by
    have hle : (2 : ℝ) ^ (jjF z) ≤ |z.2.im| := by
      have hn1 : 1 ≤ Nat.floor |z.2.im| := Nat.floor_pos.mpr hhigh.le
      have hn : Nat.floor |z.2.im| ≠ 0 := by omega
      have hh := Nat.pow_log_le_self 2 hn
      have h1 : (2 : ℝ) ^ (jjF z) ≤ (Nat.floor |z.2.im| : ℝ) := by
        have h2 : (((2 : ℕ) ^ (Nat.log 2 (Nat.floor |z.2.im|)) : ℕ) : ℝ)
            ≤ (Nat.floor |z.2.im| : ℝ) := Nat.cast_le.mpr hh
        push_cast at h2
        simpa [jjF] using h2
      have h3 : (Nat.floor |z.2.im| : ℝ) ≤ |z.2.im| := Nat.floor_le (abs_nonneg _)
      linarith
    have h3 : (4 : ℝ) ^ (jjF z) = ((2 : ℝ) ^ (jjF z)) ^ 2 := by
      rw [show (4 : ℝ) = (2 : ℝ) ^ 2 by norm_num]
      exact (pow_mul (2 : ℝ) 2 (jjF z)).symm.trans (pow_mul' (2 : ℝ) 2 (jjF z))
    rw [h3]
    exact pow_le_pow_left₀ (by positivity) hle 2
  have hpos : 0 < (4 : ℝ) ^ (jjF z) * (Real.log (q : ℝ)) ^ 2 := by positivity
  have hle2 : (4 : ℝ) ^ (jjF z) * (Real.log (q : ℝ)) ^ 2
      ≤ |z.2.im| ^ 2 * (Real.log (q : ℝ)) ^ 2 :=
    mul_le_mul_of_nonneg_right h4 (by positivity)
  calc (zeroMult z.1 z.2 : ℝ) * ‖Hk (11 / 2) (3 / 10) ((1 - z.2) * (Real.log q : ℂ))‖
      ≤ 4 * ((zeroMult z.1 z.2 : ℝ) * Real.exp (-(49 / 10) * lamOf q z.2))
          / (|z.2.im| * Real.log (q : ℝ)) ^ 2 := hker
    _ = 4 * ((zeroMult z.1 z.2 : ℝ) * Real.exp (-(49 / 10) * lamOf q z.2))
          / (|z.2.im| ^ 2 * (Real.log (q : ℝ)) ^ 2) := by rw [mul_pow]
    _ ≤ 4 * ((zeroMult z.1 z.2 : ℝ) * Real.exp (-(49 / 10) * lamOf q z.2))
          / ((4 : ℝ) ^ (jjF z) * (Real.log (q : ℝ)) ^ 2) :=
        div_le_div_of_nonneg_left (by positivity) hpos hle2
    _ = 4 / ((4 : ℝ) ^ (jjF z) * (Real.log (q : ℝ)) ^ 2)
          * ((zeroMult z.1 z.2 : ℝ) * Real.exp (-(49 / 10) * lamOf q z.2)) := by field_simp

/-- The `λ₁`-free per-window mass bound (with the minimum of the window's `λ`'s as floor). -/
lemma windowMassFree {q : ℕ} [NeZero q] (hq : 1 < q) (χ₁ : DirichletCharacter ℂ q) (β₁ : ℂ)
    {C₂ H : ℝ} (hC₂ : 0 < C₂) (hH : 0 < H)
    (hcnt : ∀ t : ℝ, 0 < t → t ≤ Real.log (q : ℝ) →
      Siegel.pairCountHeight χ₁ β₁ t (H * Real.log (q : ℝ))
        ≤ C₂ * Real.exp ((5 / 2) * t) * H ^ (3 / 2 : ℝ))
    (S : Finset (DirichletCharacter ℂ q × ℂ))
    (hzm : ∀ z ∈ S, zeroMult z.1 z.2 ≠ 0)
    (hexc : ∀ z ∈ S, ¬(z.1 = χ₁ ∧ z.2 = β₁))
    (him : ∀ z ∈ S, |z.2.im| * Real.log (q : ℝ) ≤ H * Real.log (q : ℝ)) :
    (∑ z ∈ S, (zeroMult z.1 z.2 : ℝ) * Real.exp (-(49 / 10) * lamOf q z.2))
      ≤ C₂ * H ^ (3 / 2 : ℝ) * Real.exp (5 / 2) / (1 - Real.exp (-(12 / 5))) := by
  have hlog : 0 < Real.log (q : ℝ) := Real.log_pos (by exact_mod_cast hq)
  rcases S.eq_empty_or_nonempty with hS | hne
  · subst hS
    simp only [Finset.sum_empty]
    exact div_nonneg (by positivity) (by
      have : Real.exp (-(12 / 5)) < 1 := Real.exp_lt_one_iff.mpr (by norm_num)
      linarith)
  · have hSpos : ∀ z ∈ S, 0 < lamOf q z.2 := fun z hz => by
      have h1 : z.2.re < 1 := boxMaxZeroAux.zeroMult_re_lt_one z.1 (hzm z hz)
      rw [lamOf]; exact mul_pos (by linarith) hlog
    set Λ : ℝ := S.inf' hne (fun z => lamOf q z.2) with hΛdef
    have hΛpos : 0 < Λ := by
      obtain ⟨z, hz, heq⟩ := Finset.exists_mem_eq_inf' hne (fun z => lamOf q z.2)
      rw [hΛdef, heq]; exact hSpos z hz
    have hΛle : ∀ z ∈ S, Λ ≤ lamOf q z.2 := by
      intro z hz
      rw [hΛdef]
      exact Finset.inf'_le (s := S) (fun z => lamOf q z.2) hz
    have hcount : ∀ t : ℝ, Λ ≤ t → t ≤ Real.log (q : ℝ) →
        (∑ z ∈ S.filter (fun z => lamOf q z.2 ≤ t), (zeroMult z.1 z.2 : ℝ))
          ≤ C₂ * H ^ (3 / 2 : ℝ) * Real.exp ((5 / 2) * t) := by
      intro t hΛt htL
      have htpos : 0 < t := lt_of_lt_of_le hΛpos hΛt
      calc (∑ z ∈ S.filter (fun z => lamOf q z.2 ≤ t), (zeroMult z.1 z.2 : ℝ))
          ≤ Siegel.pairCountHeight χ₁ β₁ t (H * Real.log (q : ℝ)) :=
            pairCountHeight_dom hq χ₁ β₁ _ (fun z hz => hzm z (Finset.mem_filter.mp hz).1)
              (fun z hz => (Finset.mem_filter.mp hz).2)
              (fun z hz => him z (Finset.mem_filter.mp hz).1)
              (fun z hz => hexc z (Finset.mem_filter.mp hz).1)
        _ ≤ C₂ * Real.exp ((5 / 2) * t) * H ^ (3 / 2 : ℝ) := hcnt t htpos htL
        _ = C₂ * H ^ (3 / 2 : ℝ) * Real.exp ((5 / 2) * t) := by ring
    have hlamL : ∀ z ∈ S, lamOf q z.2 ≤ Real.log (q : ℝ) := by
      intro z hz
      have h1 : 0 < z.2.re := zeroMult_re_pos z.1 (hzm z hz)
      rw [lamOf]
      nlinarith [hlog]
    have hmain := sum_mul_exp_neg_le_of_count (S := S)
      (m := fun z : DirichletCharacter ℂ q × ℂ => (zeroMult z.1 z.2 : ℝ))
      (lam := fun z : DirichletCharacter ℂ q × ℂ => lamOf q z.2)
      (a₀ := 49 / 10) (Λ := Λ) (L := Real.log (q : ℝ)) (D := C₂)
      (lam₁ := H ^ (3 / 2 : ℝ)) (c := 5 / 2)
      (by norm_num) (by norm_num) (by norm_num) hC₂ hΛpos
      (Real.rpow_pos_of_pos hH _) (fun z _ => Nat.cast_nonneg _) hΛle hlamL hcount
    refine hmain.trans ?_
    rw [show (5 : ℝ) / 2 - 49 / 10 = -(12 / 5) by norm_num]
    have hden : 0 < 1 - Real.exp (-(12 / 5)) := by
      have : Real.exp (-(12 / 5)) < 1 := Real.exp_lt_one_iff.mpr (by norm_num)
      linarith
    have hexp_le : Real.exp (-(12 / 5) * Λ) ≤ 1 := by
      rw [Real.exp_le_one_iff]; nlinarith [hΛpos]
    have hnum : 0 ≤ C₂ * H ^ (3 / 2 : ℝ) * Real.exp (5 / 2) := by positivity
    calc C₂ * H ^ (3 / 2 : ℝ) * Real.exp (5 / 2) * Real.exp (-(12 / 5) * Λ)
            / (1 - Real.exp (-(12 / 5)))
        ≤ C₂ * H ^ (3 / 2 : ℝ) * Real.exp (5 / 2) * 1 / (1 - Real.exp (-(12 / 5))) := by
          refine div_le_div_of_nonneg_right ?_ hden.le
          exact mul_le_mul_of_nonneg_left hexp_le hnum
      _ = C₂ * H ^ (3 / 2 : ℝ) * Real.exp (5 / 2) / (1 - Real.exp (-(12 / 5))) := by ring

set_option maxHeartbeats 2000000 in
private theorem highMassRep {q : ℕ} [NeZero q] (hq : 1 < q) (χ₁ : DirichletCharacter ℂ q) (β₁ : ℝ)
    {C₂ : ℝ} (hC₂ : 0 < C₂) (q₀f : ℕ) (hqf : q₀f ≤ q)
    (hfam : ∀ (σ T : ℝ), 0 ≤ σ → σ ≤ 1 → 1 ≤ T →
      Work.ZeroDensity.famCount q σ T
        ≤ C₂ * Real.exp ((5 / 2) * ((1 - σ) * Real.log (q : ℝ))) * T ^ (3 / 2 : ℝ))
    (hrepq : ∀ (χ : DirichletCharacter ℂ q) (ρ : ℂ), zeroMult χ ρ ≠ 0 →
      ¬(χ = χ₁ ∧ ρ = (β₁ : ℂ)) →
      (Real.log (1 / lamOf q (β₁ : ℂ))
          - Real.log (24 * ((4 / 3 + 1 / 100 : ℝ)
              + (2 / 3 + 1 / 100 : ℝ) * (Real.log (5 + |ρ.im|) / Real.log q))))
        / ((4 / 3 + 1 / 100 : ℝ)
            + (2 / 3 + 1 / 100 : ℝ) * (Real.log (5 + |ρ.im|) / Real.log q))
        ≤ lamOf q ρ)
    (hlam1pos : 0 < lamOf q (β₁ : ℂ)) (hsmall : lamOf q (β₁ : ℂ) ≤ 1 / 1000)
    (hαhalf : Real.log (1 / lamOf q (β₁ : ℂ)) ≤ Real.log (q : ℝ) / 2)
    (h𝓛big : 20 ≤ Real.log (q : ℝ))
    (S : Finset (DirichletCharacter ℂ q × ℂ))
    (hzm : ∀ z ∈ S, zeroMult z.1 z.2 ≠ 0) (hhigh : ∀ z ∈ S, 1 < |z.2.im|)
    (hexc : ∀ z ∈ S, ¬(z.1 = χ₁ ∧ z.2 = (β₁ : ℂ))) :
    (∑ z ∈ S, (zeroMult z.1 z.2 : ℝ)
        * ‖Hk (11 / 2) (3 / 10) ((1 - z.2) * (Real.log q : ℂ))‖)
      ≤ 4 * C₂ * (Real.exp (5 / 2) / (1 - Real.exp (-(12 / 5)))) * 4
        * ((1 - (2 : ℝ) ^ (-(1 / 2) : ℝ))⁻¹) * (2 * Real.exp 58 + 1)
        * (Real.log (q : ℝ)) ^ (-2 : ℝ) * lamOf q (β₁ : ℂ) := by
  classical
  have hlog : 0 < Real.log (q : ℝ) := lt_of_lt_of_le (by norm_num) h𝓛big
  have hlog2pos : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hlog2 : (1 / 2 : ℝ) ≤ Real.log 2 := by
    have := Real.log_two_gt_d9; linarith
  have hq1 : (1 : ℝ) ≤ (q : ℝ) := by exact_mod_cast (le_of_lt hq)
  set lam1 : ℝ := lamOf q (β₁ : ℂ) with hlam1def
  have hlam1pos' : 0 < lam1 := hlam1pos
  have hlam1lt1 : lam1 < 1 := by rw [hlam1def]; linarith
  have hlam1le : lam1 ≤ 1 / 1000 := hsmall
  set α : ℝ := Real.log (1 / lam1) with hαdef
  have hαpos : 0 < α := by
    rw [hαdef]
    refine Real.log_pos ?_
    rw [lt_div_iff₀ hlam1pos']
    simpa using hlam1lt1
  have hexp_neg : Real.exp (-α) = lam1 := by
    rw [hαdef, Real.exp_neg, Real.exp_log (by positivity), one_div, inv_inv]
  have hαle : α ≤ Real.log (q : ℝ) / 2 := by rw [hαdef, hlam1def]; exact hαhalf
  have hlam1rpow : lam1 ^ (1 / 2 : ℝ) = Real.exp (-(α / 2)) := by
    rw [Real.rpow_def_of_pos hlam1pos']
    congr 1
    have h : Real.log lam1 = -α := by
      rw [hαdef, one_div, Real.log_inv]; ring
    rw [h]; ring
  set J : ℕ := Nat.ceil (2 * Real.log (q : ℝ) / Real.log 2) with hJdef
  set J₁ : ℕ := Nat.ceil (Real.log (q : ℝ) / Real.log 2) with hJ₁def
  set m : ℕ := min J J₁ with hmdef
  have hx0 : (0 : ℝ) ≤ Real.log (q : ℝ) / Real.log 2 := div_nonneg hlog.le hlog2pos.le
  have hmJ : (m : ℝ) = min (J : ℝ) (J₁ : ℝ) := by
    rw [hmdef, Nat.cast_min]
  have hJge : 2 * Real.log (q : ℝ) / Real.log 2 ≤ (J : ℝ) := Nat.le_ceil _
  have hJ₁ge : Real.log (q : ℝ) / Real.log 2 ≤ (J₁ : ℝ) := Nat.le_ceil _
  have hJ₁lt : (J₁ : ℝ) < Real.log (q : ℝ) / Real.log 2 + 1 := Nat.ceil_lt_add_one hx0
  have hJlt : (J : ℝ) < 2 * Real.log (q : ℝ) / Real.log 2 + 1 :=
    Nat.ceil_lt_add_one (by positivity)
  have hmle_J : m ≤ J := min_le_left _ _
  have hmle_J₁ : m ≤ J₁ := min_le_right _ _
  have hmge : Real.log (q : ℝ) / Real.log 2 ≤ (m : ℝ) := by
    rw [hmJ]
    refine le_min ?_ hJ₁ge
    calc Real.log (q : ℝ) / Real.log 2 ≤ 2 * Real.log (q : ℝ) / Real.log 2 := by
          rw [div_le_div_iff₀ hlog2pos hlog2pos]
          nlinarith [hlog, hlog2pos]
      _ ≤ (J : ℝ) := hJge
  have hm_α : α / Real.log 2 ≤ (m : ℝ) := by
    have h1 : α ≤ Real.log (q : ℝ) := by linarith [hαle, hlog]
    have h2 : α / Real.log 2 ≤ Real.log (q : ℝ) / Real.log 2 :=
      div_le_div_of_nonneg_right h1 hlog2pos.le
    linarith [hmge, h2]
  have hm_tail : (2 : ℝ) ^ (-((m : ℝ) / 2)) ≤ lam1 ^ (1 / 2 : ℝ) := by
    have h1 : α / 2 ≤ ((m : ℝ) / 2) * Real.log 2 := by
      have h2 : α / Real.log 2 * Real.log 2 = α := by field_simp
      nlinarith [hm_α, hlog2pos, hlog2]
    have h3 : (2 : ℝ) ^ (-((m : ℝ) / 2))
        = Real.exp (-(((m : ℝ) / 2) * Real.log 2)) := by
      rw [Real.rpow_neg (by norm_num : (0 : ℝ) ≤ 2),
        Real.rpow_def_of_pos (by norm_num : (0 : ℝ) < 2), ← Real.exp_neg]
      congr 1
      ring
    rw [h3]
    calc Real.exp (-(((m : ℝ) / 2) * Real.log 2)) ≤ Real.exp (-(α / 2)) :=
          Real.exp_le_exp.mpr (by linarith [h1])
      _ = lam1 ^ (1 / 2 : ℝ) := hlam1rpow.symm
  have hJ_tail : (2 : ℝ) ^ (-((J : ℝ) / 2)) ≤ lam1 := by
    have h1 : α ≤ ((J : ℝ) / 2) * Real.log 2 := by
      have h2 : 2 * Real.log (q : ℝ) / Real.log 2 * Real.log 2 = 2 * Real.log (q : ℝ) := by
        field_simp
      nlinarith [hJge, hlog2pos, hlog2, hαle]
    have h3 : (2 : ℝ) ^ (-((J : ℝ) / 2))
        = Real.exp (-(((J : ℝ) / 2) * Real.log 2)) := by
      rw [Real.rpow_neg (by norm_num : (0 : ℝ) ≤ 2),
        Real.rpow_def_of_pos (by norm_num : (0 : ℝ) < 2), ← Real.exp_neg]
      congr 1
      ring
    rw [h3]
    calc Real.exp (-(((J : ℝ) / 2) * Real.log 2)) ≤ Real.exp (-α) :=
          Real.exp_le_exp.mpr (by linarith [h1])
      _ = lam1 := hexp_neg
  have hlog2le : Real.log 2 ≤ 1 := by
    have := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 2)
    linarith
  set U : ℕ → ℝ := fun j =>
    (4 / 3 + 1 / 100 : ℝ)
      + (2 / 3 + 1 / 100 : ℝ) * (Real.log (5 + (2 : ℝ) ^ (j + 1)) / Real.log (q : ℝ)) with hUdef
  set Lf : ℕ → ℝ := fun j => (α - Real.log (24 * U j)) / U j with hLdef
  have hUpos : ∀ j, 0 < U j := by
    intro j
    rw [hUdef]
    have h1 : (1 : ℝ) < 5 + (2 : ℝ) ^ (j + 1) := by
      have : (0 : ℝ) ≤ (2 : ℝ) ^ (j + 1) := by positivity
      linarith
    have h2 : 0 < Real.log (5 + (2 : ℝ) ^ (j + 1)) := Real.log_pos h1
    have h3 : 0 ≤ Real.log (5 + (2 : ℝ) ^ (j + 1)) / Real.log (q : ℝ) :=
      div_nonneg h2.le hlog.le
    have h4 : (0 : ℝ) < 2 / 3 + 1 / 100 := by norm_num
    nlinarith [mul_nonneg h4.le h3]
  have hUmono : ∀ {j j' : ℕ}, j ≤ j' → U j ≤ U j' := by
    intro j j' hjj
    rw [hUdef]
    have h1 : (2 : ℝ) ^ (j + 1) ≤ (2 : ℝ) ^ (j' + 1) :=
      pow_le_pow_right₀ (by norm_num) (by omega)
    have h2 : 0 < 5 + (2 : ℝ) ^ (j + 1) := by positivity
    have h3 : Real.log (5 + (2 : ℝ) ^ (j + 1)) ≤ Real.log (5 + (2 : ℝ) ^ (j' + 1)) :=
      Real.log_le_log h2 (by linarith)
    have h4 : (0 : ℝ) < 2 / 3 + 1 / 100 := by norm_num
    have h5 := mul_le_mul_of_nonneg_left (div_le_div_of_nonneg_right h3 hlog.le) h4.le
    linarith
  have hlog9 : Real.log 9 ≤ 4 := by
    have h12 : Real.log 9 = 2 * Real.log 3 := by
      rw [show (9 : ℝ) = 3 * 3 by norm_num, Real.log_mul (by norm_num) (by norm_num)]
      ring
    have h13 : Real.log 3 ≤ 2 := by
      have := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 3)
      linarith
    linarith
  have hlogpow : ∀ j : ℕ, Real.log (5 + (2 : ℝ) ^ (j + 1))
      ≤ Real.log 9 + ((j : ℝ) + 1) * Real.log 2 := by
    intro j
    have h4 : (5 : ℝ) + (2 : ℝ) ^ (j + 1) ≤ 9 * (2 : ℝ) ^ (j + 1) := by
      have h5 : (1 : ℝ) ≤ (2 : ℝ) ^ (j + 1) := one_le_pow₀ (by norm_num)
      linarith
    calc Real.log (5 + (2 : ℝ) ^ (j + 1)) ≤ Real.log (9 * (2 : ℝ) ^ (j + 1)) :=
          Real.log_le_log (by positivity) h4
      _ = Real.log 9 + ((j : ℝ) + 1) * Real.log 2 := by
          rw [Real.log_mul (by norm_num) (by positivity), Real.log_pow]
          push_cast; ring
  have hU_J : ∀ j, j ≤ J → U j ≤ 3 := by
    intro j hj
    have h1 : U j ≤ U J := hUmono hj
    rw [hUdef] at h1 ⊢
    have h6 : ((J : ℝ) + 1) * Real.log 2 ≤ 2 * Real.log (q : ℝ) + 2 := by
      have h7 : (J : ℝ) + 1 < 2 * Real.log (q : ℝ) / Real.log 2 + 2 := by linarith [hJlt]
      have h8 : ((J : ℝ) + 1) * Real.log 2
          < (2 * Real.log (q : ℝ) / Real.log 2 + 2) * Real.log 2 :=
        mul_lt_mul_of_pos_right h7 hlog2pos
      have h9 : (2 * Real.log (q : ℝ) / Real.log 2 + 2) * Real.log 2
          = 2 * Real.log (q : ℝ) + 2 * Real.log 2 := by
        rw [add_mul, div_mul_cancel₀ _ (ne_of_gt hlog2pos)]
      have h10 : 2 * Real.log 2 ≤ 2 := by linarith [hlog2le]
      linarith
    have h7 : Real.log (5 + (2 : ℝ) ^ (J + 1)) ≤ Real.log 9 + 2 * Real.log (q : ℝ) + 2 := by
      linarith [hlogpow J, h6]
    have h8 : (Real.log 9 + 2 * Real.log (q : ℝ) + 2) / Real.log (q : ℝ)
        = (Real.log 9 + 2) / Real.log (q : ℝ) + 2 := by
      rw [add_div, add_div, mul_div_cancel_right₀ _ (ne_of_gt hlog)]
      ring
    have h9 : (Real.log 9 + 2) / Real.log (q : ℝ) ≤ 6 / 20 := by
      rw [div_le_div_iff₀ hlog (by norm_num : (0 : ℝ) < 20)]
      nlinarith [hlog9, h𝓛big]
    have h10 : (0 : ℝ) < 2 / 3 + 1 / 100 := by norm_num
    have h11 : (2 / 3 + 1 / 100 : ℝ)
          * (Real.log (5 + (2 : ℝ) ^ (J + 1)) / Real.log (q : ℝ))
        ≤ (2 / 3 + 1 / 100 : ℝ) * ((Real.log 9 + 2) / Real.log (q : ℝ) + 2) := by
      have h12 : Real.log (5 + (2 : ℝ) ^ (J + 1)) / Real.log (q : ℝ)
          ≤ (Real.log 9 + 2) / Real.log (q : ℝ) + 2 := by
        rw [← h8]
        exact div_le_div_of_nonneg_right h7 hlog.le
      exact mul_le_mul_of_nonneg_left h12 h10.le
    have h13 : (2 / 3 + 1 / 100 : ℝ) * (6 / 20 + 2) ≤ 3 - (4 / 3 + 1 / 100 : ℝ) := by
      norm_num
    have h14 : (2 / 3 + 1 / 100 : ℝ) * ((Real.log 9 + 2) / Real.log (q : ℝ) + 2)
        ≤ (2 / 3 + 1 / 100 : ℝ) * (6 / 20 + 2) :=
      mul_le_mul_of_nonneg_left (by linarith [h9]) h10.le
    linarith
  have hU_m : ∀ j, j ≤ m → U j ≤ 12 / 5 := by
    intro j hj
    have h1 : U j ≤ U m := hUmono hj
    rw [hUdef] at h1 ⊢
    have h6 : ((m : ℝ) + 1) * Real.log 2 ≤ Real.log (q : ℝ) + 2 := by
      have h7 : (m : ℝ) + 1 < Real.log (q : ℝ) / Real.log 2 + 2 := by
        have h2 : (m : ℝ) ≤ (J₁ : ℝ) := by exact_mod_cast hmle_J₁
        linarith [hJ₁lt]
      have h8 : ((m : ℝ) + 1) * Real.log 2
          < (Real.log (q : ℝ) / Real.log 2 + 2) * Real.log 2 :=
        mul_lt_mul_of_pos_right h7 hlog2pos
      have h9 : (Real.log (q : ℝ) / Real.log 2 + 2) * Real.log 2
          = Real.log (q : ℝ) + 2 * Real.log 2 := by
        rw [add_mul, div_mul_cancel₀ _ (ne_of_gt hlog2pos)]
      have h10 : 2 * Real.log 2 ≤ 2 := by linarith [hlog2le]
      linarith
    have h7 : Real.log (5 + (2 : ℝ) ^ (m + 1)) ≤ Real.log 9 + Real.log (q : ℝ) + 2 := by
      linarith [hlogpow m, h6]
    have h8 : (Real.log 9 + Real.log (q : ℝ) + 2) / Real.log (q : ℝ)
        = (Real.log 9 + 2) / Real.log (q : ℝ) + 1 := by
      rw [add_div, add_div, div_self (ne_of_gt hlog)]
      ring
    have h9 : (Real.log 9 + 2) / Real.log (q : ℝ) ≤ 6 / 20 := by
      rw [div_le_div_iff₀ hlog (by norm_num : (0 : ℝ) < 20)]
      nlinarith [hlog9, h𝓛big]
    have h10 : (0 : ℝ) < 2 / 3 + 1 / 100 := by norm_num
    have h11 : (2 / 3 + 1 / 100 : ℝ)
          * (Real.log (5 + (2 : ℝ) ^ (m + 1)) / Real.log (q : ℝ))
        ≤ (2 / 3 + 1 / 100 : ℝ) * ((Real.log 9 + 2) / Real.log (q : ℝ) + 1) := by
      have h12 : Real.log (5 + (2 : ℝ) ^ (m + 1)) / Real.log (q : ℝ)
          ≤ (Real.log 9 + 2) / Real.log (q : ℝ) + 1 := by
        rw [← h8]
        exact div_le_div_of_nonneg_right h7 hlog.le
      exact mul_le_mul_of_nonneg_left h12 h10.le
    have h13 : (2 / 3 + 1 / 100 : ℝ) * (6 / 20 + 1) ≤ 12 / 5 - (4 / 3 + 1 / 100 : ℝ) := by
      norm_num
    have h14 : (2 / 3 + 1 / 100 : ℝ) * ((Real.log 9 + 2) / Real.log (q : ℝ) + 1)
        ≤ (2 / 3 + 1 / 100 : ℝ) * (6 / 20 + 1) :=
      mul_le_mul_of_nonneg_left (by linarith [h9]) h10.le
    linarith
  have hU24_J : ∀ j, j ≤ J → 24 * U j < Real.exp α := by
    intro j hj
    have h1 : 24 * U j ≤ 72 := by linarith [hU_J j hj]
    have h3 : Real.exp α = 1 / lam1 := by rw [hαdef, Real.exp_log (by positivity)]
    have h2 : (1000 : ℝ) ≤ Real.exp α := by
      rw [h3, le_div_iff₀ hlam1pos']
      linarith [hlam1le]
    linarith
  have hLpos : ∀ j, j ≤ J → 0 < Lf j := by
    intro j hj
    rw [hLdef]
    refine div_pos ?_ (hUpos j)
    rw [sub_pos]
    have h5 : Real.log (24 * U j) < Real.log (Real.exp α) :=
      Real.log_lt_log (mul_pos (by norm_num : (0 : ℝ) < 24) (hUpos j)) (hU24_J j hj)
    rwa [Real.log_exp] at h5
  have hfloorpos_J : ∀ j, j ≤ J → 24 * U j ≤ 1 / lam1 := by
    intro j hj
    have h3 : Real.exp α = 1 / lam1 := by rw [hαdef, Real.exp_log (by positivity)]
    rw [← h3]
    linarith [hU24_J j hj]
  have hcnt : ∀ (H : ℝ), 1 ≤ H → ∀ t : ℝ, 0 < t → t ≤ Real.log (q : ℝ) →
      Siegel.pairCountHeight χ₁ β₁ t (H * Real.log (q : ℝ))
        ≤ C₂ * Real.exp ((5 / 2) * t) * H ^ (3 / 2 : ℝ) := by
    intro H hH t ht htL
    have hσ1 : 0 ≤ 1 - t / Real.log (q : ℝ) := by
      have h1 : t / Real.log (q : ℝ) ≤ 1 := (div_le_one hlog).mpr htL
      linarith
    have hσ2 : 1 - t / Real.log (q : ℝ) ≤ 1 := by
      have h1 : 0 ≤ t / Real.log (q : ℝ) := div_nonneg ht.le hlog.le
      linarith
    calc Siegel.pairCountHeight χ₁ β₁ t (H * Real.log (q : ℝ))
        ≤ Work.ZeroDensity.famCount q (1 - t / Real.log (q : ℝ))
            ((H * Real.log (q : ℝ)) / Real.log (q : ℝ)) :=
          pairCountHeight_le_famCount hq χ₁ β₁
      _ = Work.ZeroDensity.famCount q (1 - t / Real.log (q : ℝ)) H := by
          rw [mul_div_cancel_right₀ _ (ne_of_gt hlog)]
      _ ≤ C₂ * Real.exp ((5 / 2) * ((1 - (1 - t / Real.log (q : ℝ))) * Real.log (q : ℝ)))
            * H ^ (3 / 2 : ℝ) := hfam _ _ hσ1 hσ2 hH
      _ = C₂ * Real.exp ((5 / 2) * t) * H ^ (3 / 2 : ℝ) := by
          rw [show (1 - (1 - t / Real.log (q : ℝ))) * Real.log (q : ℝ) = t by
            field_simp; ring]
  have hfib_le : ∀ (j : ℕ) (hjJ : j ≤ J) (hjT : j ∈ S.image jjF),
      (∑ z ∈ S.filter (fun z => jjF z = j), (zeroMult z.1 z.2 : ℝ)
          * ‖Hk (11 / 2) (3 / 10) ((1 - z.2) * (Real.log q : ℂ))‖)
        ≤ 4 / ((4 : ℝ) ^ j * (Real.log (q : ℝ)) ^ 2)
          * (C₂ * ((2 : ℝ) ^ (j + 1)) ^ (3 / 2 : ℝ) * Real.exp (5 / 2)
              * Real.exp (-(12 / 5) * Lf j) / (1 - Real.exp (-(12 / 5)))) := by
    intro j hjJ hjT
    set F := S.filter (fun z => jjF z = j) with hFdef
    have hzmF : ∀ z ∈ F, zeroMult z.1 z.2 ≠ 0 := fun z hz => hzm z (Finset.mem_filter.mp hz).1
    have hhighF : ∀ z ∈ F, 1 < |z.2.im| := fun z hz => hhigh z (Finset.mem_filter.mp hz).1
    have hexcF : ∀ z ∈ F, ¬(z.1 = χ₁ ∧ z.2 = (β₁ : ℂ)) :=
      fun z hz => hexc z (Finset.mem_filter.mp hz).1
    have him_le : ∀ z ∈ F, |z.2.im| ≤ (2 : ℝ) ^ (j + 1) := by
      intro z hz
      have hjj : jjF z = j := (Finset.mem_filter.mp hz).2
      have h1 : Nat.floor |z.2.im| < 2 ^ (Nat.log 2 (Nat.floor |z.2.im|) + 1) :=
        Nat.lt_pow_succ_log_self (by norm_num : 1 < 2) _
      rw [show Nat.log 2 (Nat.floor |z.2.im|) = j from hjj] at h1
      have h2 : (Nat.floor |z.2.im| : ℝ) + 1 ≤ (2 : ℝ) ^ (j + 1) := by
        exact_mod_cast h1
      have h3 : |z.2.im| < (Nat.floor |z.2.im| : ℝ) + 1 := Nat.lt_floor_add_one _
      linarith
    have himF : ∀ z ∈ F, |z.2.im| * Real.log (q : ℝ) ≤ ((2 : ℝ) ^ (j + 1)) * Real.log (q : ℝ) :=
      fun z hz => mul_le_mul_of_nonneg_right (him_le z hz) hlog.le
    have hfloorF : ∀ z ∈ F, Lf j ≤ lamOf q z.2 := by
      intro z hz
      have hrep_apply := repulsionFloorHi_own χ₁ β₁ (H := (2 : ℝ) ^ (j + 1))
        (by exact one_le_pow₀ (by norm_num : (1 : ℝ) ≤ 2)) hrepq
        (by have h := hfloorpos_J j hjJ; rw [hUdef] at h; exact h) hq
        (hzmF z hz) (him_le z hz) (hexcF z hz)
      rw [hLdef, hUdef]
      exact hrep_apply
    have hmass := windowMassFloor hq χ₁ β₁ hC₂ (by positivity) (hLpos j hjJ)
      (hcnt ((2 : ℝ) ^ (j + 1)) (by exact one_le_pow₀ (by norm_num : (1 : ℝ) ≤ 2)))
      F hzmF hexcF himF hfloorF
    have hstep1 : (∑ z ∈ F, (zeroMult z.1 z.2 : ℝ)
          * ‖Hk (11 / 2) (3 / 10) ((1 - z.2) * (Real.log q : ℂ))‖)
        ≤ ∑ z ∈ F, 4 / ((4 : ℝ) ^ (jjF z) * (Real.log (q : ℝ)) ^ 2)
            * ((zeroMult z.1 z.2 : ℝ) * Real.exp (-(49 / 10) * lamOf q z.2)) :=
      Finset.sum_le_sum (fun z hz => kernel_le hq z (hzmF z hz) (hhighF z hz))
    have hstep2 : (∑ z ∈ F, 4 / ((4 : ℝ) ^ (jjF z) * (Real.log (q : ℝ)) ^ 2)
            * ((zeroMult z.1 z.2 : ℝ) * Real.exp (-(49 / 10) * lamOf q z.2)))
        = 4 / ((4 : ℝ) ^ j * (Real.log (q : ℝ)) ^ 2)
            * (∑ z ∈ F, (zeroMult z.1 z.2 : ℝ) * Real.exp (-(49 / 10) * lamOf q z.2)) := by
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl (fun z hz => ?_)
      rw [(Finset.mem_filter.mp hz).2]
    calc (∑ z ∈ F, (zeroMult z.1 z.2 : ℝ)
          * ‖Hk (11 / 2) (3 / 10) ((1 - z.2) * (Real.log q : ℂ))‖)
        ≤ 4 / ((4 : ℝ) ^ j * (Real.log (q : ℝ)) ^ 2)
            * (∑ z ∈ F, (zeroMult z.1 z.2 : ℝ) * Real.exp (-(49 / 10) * lamOf q z.2)) :=
          le_trans hstep1 hstep2.le
      _ ≤ 4 / ((4 : ℝ) ^ j * (Real.log (q : ℝ)) ^ 2)
            * (C₂ * ((2 : ℝ) ^ (j + 1)) ^ (3 / 2 : ℝ) * Real.exp (5 / 2)
                * Real.exp (-(12 / 5) * Lf j) / (1 - Real.exp (-(12 / 5)))) := by
          refine mul_le_mul_of_nonneg_left hmass ?_
          positivity
  have hrm : (2 : ℝ) ^ (-(1 / 2) : ℝ) < 1 := by
    rw [Real.rpow_neg (by norm_num : (0 : ℝ) ≤ 2)]
    exact inv_lt_one_of_one_lt₀ (Real.one_lt_rpow (by norm_num) (by norm_num))
  have hrm0 : 0 ≤ (2 : ℝ) ^ (-(1 / 2) : ℝ) := Real.rpow_nonneg (by norm_num) _
  set Ga : ℝ := (1 - (2 : ℝ) ^ (-(1 / 2) : ℝ))⁻¹ with hGadef
  have hGapos : 0 < Ga := by
    rw [hGadef]
    have : (2 : ℝ) ^ (-(1 / 2) : ℝ) < 1 := hrm
    positivity
  have hden : 0 < 1 - Real.exp (-(12 / 5)) := by
    have h : Real.exp (-(12 / 5)) < 1 := Real.exp_lt_one_iff.mpr (by norm_num)
    linarith
  have hG_all : ∀ Y : Finset ℕ, (∑ j ∈ Y, ((2 : ℝ) ^ (-(1 / 2) : ℝ)) ^ j) ≤ Ga := by
    intro Y
    rw [hGadef, ← tsum_geometric_of_lt_one hrm0 hrm]
    exact Summable.sum_le_tsum Y (fun i _ => by positivity)
      (summable_geometric_of_lt_one hrm0 hrm)
  have hrpow : ((Real.log (q : ℝ)) ^ 2)⁻¹ = (Real.log (q : ℝ)) ^ (-2 : ℝ) := by
    rw [show (Real.log (q : ℝ)) ^ 2 = (Real.log (q : ℝ)) ^ ((2 : ℕ) : ℝ) by
      rw [Real.rpow_natCast]]
    rw [← Real.rpow_neg hlog.le]
    norm_num
  have hrpow2 : ∀ j : ℕ, 4 / ((4 : ℝ) ^ j * (Real.log (q : ℝ)) ^ 2)
      = 4 * (Real.log (q : ℝ)) ^ (-2 : ℝ) * ((4 : ℝ) ^ j)⁻¹ := by
    intro j
    rw [div_eq_mul_inv, mul_inv_rev, hrpow]
    ring
  have htailpow : ∀ (M : ℕ), ((2 : ℝ) ^ (-(1 / 2) : ℝ)) ^ (M + 1)
      ≤ (2 : ℝ) ^ (-((M : ℝ) / 2)) := by
    intro M
    calc ((2 : ℝ) ^ (-(1 / 2) : ℝ)) ^ (M + 1)
        = (2 : ℝ) ^ (-((M : ℝ) + 1) / 2) := by
          rw [← Real.rpow_natCast ((2 : ℝ) ^ (-(1 / 2) : ℝ)) (M + 1),
            ← Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 2)]
          congr 1
          push_cast
          ring
      _ ≤ (2 : ℝ) ^ (-((M : ℝ) / 2)) :=
          Real.rpow_le_rpow_of_exponent_le (by norm_num) (by linarith)
  have hG_tail : ∀ (M : ℕ), ∀ Y : Finset ℕ, (∀ j ∈ Y, M < j) →
      (∑ j ∈ Y, ((2 : ℝ) ^ (-(1 / 2) : ℝ)) ^ j) ≤ Ga * (2 : ℝ) ^ (-((M : ℝ) / 2)) := by
    intro M Y hY
    have hsub : Y ⊆ Finset.Ico (M + 1) (Y.sup id + 1) := by
      intro j hj
      refine Finset.mem_Ico.mpr ⟨?_, ?_⟩
      · have := hY j hj; omega
      · exact Nat.lt_succ_of_le (Finset.le_sup (f := id) hj)
    have h1 : (∑ j ∈ Y, ((2 : ℝ) ^ (-(1 / 2) : ℝ)) ^ j)
        ≤ ((2 : ℝ) ^ (-(1 / 2) : ℝ)) ^ (M + 1)
            / (1 - (2 : ℝ) ^ (-(1 / 2) : ℝ)) :=
      le_trans (Finset.sum_le_sum_of_subset_of_nonneg hsub (fun j _ _ => by positivity))
        (geom_sum_Ico_le_of_lt_one hrm0 hrm)
    calc (∑ j ∈ Y, ((2 : ℝ) ^ (-(1 / 2) : ℝ)) ^ j)
        ≤ ((2 : ℝ) ^ (-(1 / 2) : ℝ)) ^ (M + 1)
            / (1 - (2 : ℝ) ^ (-(1 / 2) : ℝ)) := h1
      _ ≤ (2 : ℝ) ^ (-((M : ℝ) / 2)) / (1 - (2 : ℝ) ^ (-(1 / 2) : ℝ)) := by
          refine div_le_div_of_nonneg_right (htailpow M) ?_
          have : (2 : ℝ) ^ (-(1 / 2) : ℝ) < 1 := hrm
          linarith
      _ = Ga * (2 : ℝ) ^ (-((M : ℝ) / 2)) := by rw [hGadef]; ring
  have hconst_nonneg : ∀ c : ℝ, 0 ≤ c →
      0 ≤ 4 * (Real.log (q : ℝ)) ^ (-2 : ℝ) * C₂
        * (Real.exp (5 / 2) / (1 - Real.exp (-(12 / 5)))) * c := by
    intro c hc
    have h1 : 0 < Real.exp (5 / 2) / (1 - Real.exp (-(12 / 5))) :=
      div_pos (by positivity) hden
    have h2 : 0 ≤ (Real.log (q : ℝ)) ^ (-2 : ℝ) := Real.rpow_nonneg hlog.le _
    positivity
  have hdyad : ∀ j : ℕ, ((4 : ℝ) ^ j)⁻¹ * ((2 : ℝ) ^ (j + 1)) ^ (3 / 2 : ℝ)
      ≤ 4 * ((2 : ℝ) ^ (-(1 / 2) : ℝ)) ^ j := by
    intro j
    rw [mul_comm, dyadic_key_free]
    have h1 : (2 : ℝ) ^ (3 / 2 : ℝ) ≤ 4 := by
      have h2 : (2 : ℝ) ^ (3 / 2 : ℝ) ≤ (2 : ℝ) ^ (2 : ℝ) :=
        Real.rpow_le_rpow_of_exponent_le (by norm_num) (by norm_num)
      have h3 : (2 : ℝ) ^ (2 : ℝ) = 4 := by
        rw [Real.rpow_two]
        norm_num
      linarith
    exact mul_le_mul_of_nonneg_right h1 (by positivity)
  have htermA : ∀ (c : ℝ) (j : ℕ),
      4 / ((4 : ℝ) ^ j * (Real.log (q : ℝ)) ^ 2)
        * (C₂ * ((2 : ℝ) ^ (j + 1)) ^ (3 / 2 : ℝ) * Real.exp (5 / 2) * c
            / (1 - Real.exp (-(12 / 5))))
      = (4 * (Real.log (q : ℝ)) ^ (-2 : ℝ) * C₂
          * (Real.exp (5 / 2) / (1 - Real.exp (-(12 / 5)))) * c)
        * (((4 : ℝ) ^ j)⁻¹ * ((2 : ℝ) ^ (j + 1)) ^ (3 / 2 : ℝ)) := by
    intro c j
    rw [hrpow2 j]
    ring
  have hfac : ∀ (c : ℝ) (A : Finset ℕ), 0 ≤ c →
      (∑ j ∈ A, 4 / ((4 : ℝ) ^ j * (Real.log (q : ℝ)) ^ 2)
        * (C₂ * ((2 : ℝ) ^ (j + 1)) ^ (3 / 2 : ℝ) * Real.exp (5 / 2) * c
            / (1 - Real.exp (-(12 / 5)))))
      ≤ (4 * (Real.log (q : ℝ)) ^ (-2 : ℝ) * C₂
          * (Real.exp (5 / 2) / (1 - Real.exp (-(12 / 5)))) * c)
        * (4 * ∑ j ∈ A, ((2 : ℝ) ^ (-(1 / 2) : ℝ)) ^ j) := by
    intro c A hc
    have heq : (∑ j ∈ A, 4 / ((4 : ℝ) ^ j * (Real.log (q : ℝ)) ^ 2)
        * (C₂ * ((2 : ℝ) ^ (j + 1)) ^ (3 / 2 : ℝ) * Real.exp (5 / 2) * c
            / (1 - Real.exp (-(12 / 5)))))
        = (4 * (Real.log (q : ℝ)) ^ (-2 : ℝ) * C₂
            * (Real.exp (5 / 2) / (1 - Real.exp (-(12 / 5)))) * c)
          * (∑ j ∈ A, ((4 : ℝ) ^ j)⁻¹ * ((2 : ℝ) ^ (j + 1)) ^ (3 / 2 : ℝ)) := by
      rw [Finset.sum_congr rfl (fun j _ => htermA c j)]
      rw [← Finset.mul_sum]
    rw [heq]
    refine mul_le_mul_of_nonneg_left ?_ (hconst_nonneg c hc)
    refine (Finset.sum_le_sum (fun j _ => hdyad j)).trans (le_of_eq ?_)
    rw [Finset.mul_sum]
  set Gs : ℕ → ℝ := fun j => ∑ z ∈ S.filter (fun z => jjF z = j),
      (zeroMult z.1 z.2 : ℝ) * ‖Hk (11 / 2) (3 / 10) ((1 - z.2) * (Real.log q : ℂ))‖ with hGs
  have hpow_le : ∀ j, j ≤ m → Real.exp (-(12 / 5) * Lf j) ≤ Real.exp 58 * lam1 := by
    intro j hj
    have hjJ : j ≤ J := le_trans hj hmle_J
    have hUj1 : (4 / 3 + 1 / 100 : ℝ) ≤ U j := by
      rw [hUdef]
      have h3 : 0 ≤ (2 / 3 + 1 / 100 : ℝ)
          * (Real.log (5 + (2 : ℝ) ^ (j + 1)) / Real.log (q : ℝ)) := by
        refine mul_nonneg (by norm_num) ?_
        refine div_nonneg ?_ hlog.le
        refine Real.log_nonneg ?_
        have : (0 : ℝ) ≤ (2 : ℝ) ^ (j + 1) := by positivity
        linarith
      linarith
    have halg := algPow_own (u := U j) (A := α) hUj1
    have hLf_eq : Lf j = (α - Real.log (24 * U j)) / U j := by rw [hLdef]
    rw [hLf_eq]
    refine halg.trans ?_
    rw [hexp_neg]
    have hUj : U j ≤ 12 / 5 := hU_m j hj
    have hexp1 : (1 : ℝ) ≤ 12 / (5 * U j) := by
      rw [le_div_iff₀ (by positivity : (0 : ℝ) < 5 * U j)]
      linarith
    calc Real.exp 58 * lam1 ^ (12 / (5 * U j)) ≤ Real.exp 58 * lam1 ^ (1 : ℝ) := by
          refine mul_le_mul_of_nonneg_left ?_ (by positivity)
          exact Real.rpow_le_rpow_of_exponent_ge hlam1pos' hlam1lt1.le hexp1
      _ = Real.exp 58 * lam1 := by rw [Real.rpow_one]
  have hpow_le_half : ∀ j, j ≤ J → Real.exp (-(12 / 5) * Lf j) ≤ Real.exp 58 * lam1 ^ (1 / 2 : ℝ) := by
    intro j hj
    have hUj1 : (4 / 3 + 1 / 100 : ℝ) ≤ U j := by
      rw [hUdef]
      have h3 : 0 ≤ (2 / 3 + 1 / 100 : ℝ)
          * (Real.log (5 + (2 : ℝ) ^ (j + 1)) / Real.log (q : ℝ)) := by
        refine mul_nonneg (by norm_num) ?_
        refine div_nonneg ?_ hlog.le
        refine Real.log_nonneg ?_
        have : (0 : ℝ) ≤ (2 : ℝ) ^ (j + 1) := by positivity
        linarith
      linarith
    have halg := algPow_own (u := U j) (A := α) hUj1
    have hLf_eq : Lf j = (α - Real.log (24 * U j)) / U j := by rw [hLdef]
    rw [hLf_eq]
    refine halg.trans ?_
    rw [hexp_neg]
    have hUj : U j ≤ 3 := hU_J j hj
    have hexp1 : (1 / 2 : ℝ) ≤ 12 / (5 * U j) := by
      rw [le_div_iff₀ (by positivity : (0 : ℝ) < 5 * U j)]
      linarith
    calc Real.exp 58 * lam1 ^ (12 / (5 * U j)) ≤ Real.exp 58 * lam1 ^ (1 / 2 : ℝ) := by
          refine mul_le_mul_of_nonneg_left ?_ (by positivity)
          exact Real.rpow_le_rpow_of_exponent_ge hlam1pos' hlam1lt1.le hexp1
      _ = Real.exp 58 * lam1 ^ (1 / 2 : ℝ) := rfl
  have hA : (∑ j ∈ (S.image jjF).filter (fun j => j ≤ m), Gs j)
      ≤ 4 * C₂ * (Real.exp (5 / 2) / (1 - Real.exp (-(12 / 5)))) * 4 * Ga
          * Real.exp 58 * (Real.log (q : ℝ)) ^ (-2 : ℝ) * lam1 := by
    have hper : ∀ j ∈ (S.image jjF).filter (fun j => j ≤ m),
        Gs j ≤ 4 / ((4 : ℝ) ^ j * (Real.log (q : ℝ)) ^ 2)
          * (C₂ * ((2 : ℝ) ^ (j + 1)) ^ (3 / 2 : ℝ) * Real.exp (5 / 2)
              * (Real.exp 58 * lam1) / (1 - Real.exp (-(12 / 5)))) := by
      intro j hj
      have hjm : j ≤ m := (Finset.mem_filter.mp hj).2
      have hjT : j ∈ S.image jjF := (Finset.mem_filter.mp hj).1
      have hjJ : j ≤ J := le_trans hjm hmle_J
      rw [hGs]
      refine (hfib_le j hjJ hjT).trans ?_
      refine mul_le_mul_of_nonneg_left ?_ (by positivity)
      refine div_le_div_of_nonneg_right ?_ hden.le
      exact mul_le_mul_of_nonneg_left (hpow_le j hjm) (by positivity)
    calc (∑ j ∈ (S.image jjF).filter (fun j => j ≤ m), Gs j)
        ≤ ∑ j ∈ (S.image jjF).filter (fun j => j ≤ m),
            4 / ((4 : ℝ) ^ j * (Real.log (q : ℝ)) ^ 2)
              * (C₂ * ((2 : ℝ) ^ (j + 1)) ^ (3 / 2 : ℝ) * Real.exp (5 / 2)
                  * (Real.exp 58 * lam1) / (1 - Real.exp (-(12 / 5)))) := Finset.sum_le_sum hper
      _ ≤ (4 * (Real.log (q : ℝ)) ^ (-2 : ℝ) * C₂
            * (Real.exp (5 / 2) / (1 - Real.exp (-(12 / 5)))) * (Real.exp 58 * lam1))
            * (4 * Ga) := by
          refine (hfac (Real.exp 58 * lam1) ((S.image jjF).filter (fun j => j ≤ m))
            (by positivity)).trans ?_
          refine mul_le_mul_of_nonneg_left ?_ (hconst_nonneg _ (by positivity))
          exact mul_le_mul_of_nonneg_left (hG_all _) (by norm_num)
      _ = 4 * C₂ * (Real.exp (5 / 2) / (1 - Real.exp (-(12 / 5)))) * 4 * Ga
            * Real.exp 58 * (Real.log (q : ℝ)) ^ (-2 : ℝ) * lam1 := by ring
  have hB1 : (∑ j ∈ ((S.image jjF).filter (fun j => ¬ j ≤ m)).filter (fun j => j ≤ J), Gs j)
      ≤ 4 * C₂ * (Real.exp (5 / 2) / (1 - Real.exp (-(12 / 5)))) * 4 * Ga
          * Real.exp 58 * (Real.log (q : ℝ)) ^ (-2 : ℝ) * lam1 := by
    have hper : ∀ j ∈ ((S.image jjF).filter (fun j => ¬ j ≤ m)).filter (fun j => j ≤ J),
        Gs j ≤ 4 / ((4 : ℝ) ^ j * (Real.log (q : ℝ)) ^ 2)
          * (C₂ * ((2 : ℝ) ^ (j + 1)) ^ (3 / 2 : ℝ) * Real.exp (5 / 2)
              * (Real.exp 58 * lam1 ^ (1 / 2 : ℝ)) / (1 - Real.exp (-(12 / 5)))) := by
      intro j hj
      have hjJ : j ≤ J := (Finset.mem_filter.mp hj).2
      have hjT : j ∈ S.image jjF := (Finset.mem_filter.mp (Finset.mem_filter.mp hj).1).1
      rw [hGs]
      refine (hfib_le j hjJ hjT).trans ?_
      refine mul_le_mul_of_nonneg_left ?_ (by positivity)
      refine div_le_div_of_nonneg_right ?_ hden.le
      exact mul_le_mul_of_nonneg_left (hpow_le_half j hjJ) (by positivity)
    have hgt : ∀ j ∈ ((S.image jjF).filter (fun j => ¬ j ≤ m)).filter (fun j => j ≤ J), m < j := by
      intro j hj
      have := (Finset.mem_filter.mp (Finset.mem_filter.mp hj).1).2
      omega
    have hprod : lam1 ^ (1 / 2 : ℝ) * lam1 ^ (1 / 2 : ℝ) = lam1 := by
      rw [← Real.rpow_add hlam1pos']
      norm_num
    calc (∑ j ∈ ((S.image jjF).filter (fun j => ¬ j ≤ m)).filter (fun j => j ≤ J), Gs j)
        ≤ ∑ j ∈ ((S.image jjF).filter (fun j => ¬ j ≤ m)).filter (fun j => j ≤ J),
            4 / ((4 : ℝ) ^ j * (Real.log (q : ℝ)) ^ 2)
              * (C₂ * ((2 : ℝ) ^ (j + 1)) ^ (3 / 2 : ℝ) * Real.exp (5 / 2)
                  * (Real.exp 58 * lam1 ^ (1 / 2 : ℝ)) / (1 - Real.exp (-(12 / 5)))) :=
          Finset.sum_le_sum hper
      _ ≤ (4 * (Real.log (q : ℝ)) ^ (-2 : ℝ) * C₂
            * (Real.exp (5 / 2) / (1 - Real.exp (-(12 / 5)))) * (Real.exp 58 * lam1 ^ (1 / 2 : ℝ)))
            * (4 * (Ga * (2 : ℝ) ^ (-((m : ℝ) / 2)))) := by
          refine (hfac (Real.exp 58 * lam1 ^ (1 / 2 : ℝ))
            (((S.image jjF).filter (fun j => ¬ j ≤ m)).filter (fun j => j ≤ J))
            (by positivity)).trans ?_
          refine mul_le_mul_of_nonneg_left ?_ (hconst_nonneg _ (by positivity))
          exact mul_le_mul_of_nonneg_left (hG_tail m _ hgt) (by norm_num)
      _ ≤ (4 * (Real.log (q : ℝ)) ^ (-2 : ℝ) * C₂
            * (Real.exp (5 / 2) / (1 - Real.exp (-(12 / 5)))) * (Real.exp 58 * lam1 ^ (1 / 2 : ℝ)))
            * (4 * (Ga * lam1 ^ (1 / 2 : ℝ))) := by
          refine mul_le_mul_of_nonneg_left ?_ (hconst_nonneg _ (by positivity))
          exact mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hm_tail (by positivity))
            (by norm_num)
      _ = 4 * C₂ * (Real.exp (5 / 2) / (1 - Real.exp (-(12 / 5)))) * 4 * Ga
            * Real.exp 58 * (Real.log (q : ℝ)) ^ (-2 : ℝ)
            * (lam1 ^ (1 / 2 : ℝ) * lam1 ^ (1 / 2 : ℝ)) := by ring
      _ = 4 * C₂ * (Real.exp (5 / 2) / (1 - Real.exp (-(12 / 5)))) * 4 * Ga
            * Real.exp 58 * (Real.log (q : ℝ)) ^ (-2 : ℝ) * lam1 := by rw [hprod]
  have hB2 : (∑ j ∈ ((S.image jjF).filter (fun j => ¬ j ≤ m)).filter (fun j => ¬ j ≤ J), Gs j)
      ≤ 4 * C₂ * (Real.exp (5 / 2) / (1 - Real.exp (-(12 / 5)))) * 4 * Ga
          * (Real.log (q : ℝ)) ^ (-2 : ℝ) * lam1 := by
    have hper : ∀ j ∈ ((S.image jjF).filter (fun j => ¬ j ≤ m)).filter (fun j => ¬ j ≤ J),
        Gs j ≤ 4 / ((4 : ℝ) ^ j * (Real.log (q : ℝ)) ^ 2)
          * (C₂ * ((2 : ℝ) ^ (j + 1)) ^ (3 / 2 : ℝ) * Real.exp (5 / 2) * 1
              / (1 - Real.exp (-(12 / 5)))) := by
      intro j hj
      set F := S.filter (fun z => jjF z = j) with hFdef
      have hzmF : ∀ z ∈ F, zeroMult z.1 z.2 ≠ 0 := fun z hz => hzm z (Finset.mem_filter.mp hz).1
      have hhighF : ∀ z ∈ F, 1 < |z.2.im| := fun z hz => hhigh z (Finset.mem_filter.mp hz).1
      have hexcF : ∀ z ∈ F, ¬(z.1 = χ₁ ∧ z.2 = (β₁ : ℂ)) :=
        fun z hz => hexc z (Finset.mem_filter.mp hz).1
      have him_le : ∀ z ∈ F, |z.2.im| ≤ (2 : ℝ) ^ (j + 1) := by
        intro z hz
        have hjj : jjF z = j := (Finset.mem_filter.mp hz).2
        have h1 : Nat.floor |z.2.im| < 2 ^ (Nat.log 2 (Nat.floor |z.2.im|) + 1) :=
          Nat.lt_pow_succ_log_self (by norm_num : 1 < 2) _
        rw [show Nat.log 2 (Nat.floor |z.2.im|) = j from hjj] at h1
        have h2 : (Nat.floor |z.2.im| : ℝ) + 1 ≤ (2 : ℝ) ^ (j + 1) := by exact_mod_cast h1
        have h3 : |z.2.im| < (Nat.floor |z.2.im| : ℝ) + 1 := Nat.lt_floor_add_one _
        linarith
      have himF : ∀ z ∈ F, |z.2.im| * Real.log (q : ℝ)
          ≤ ((2 : ℝ) ^ (j + 1)) * Real.log (q : ℝ) :=
        fun z hz => mul_le_mul_of_nonneg_right (him_le z hz) hlog.le
      have hmass := windowMassFree hq χ₁ β₁ hC₂ (by positivity)
        (hcnt ((2 : ℝ) ^ (j + 1)) (by exact one_le_pow₀ (by norm_num : (1 : ℝ) ≤ 2)))
        F hzmF hexcF himF
      have hmass' : (∑ z ∈ F, (zeroMult z.1 z.2 : ℝ)
            * Real.exp (-(49 / 10) * lamOf q z.2))
          ≤ C₂ * ((2 : ℝ) ^ (j + 1)) ^ (3 / 2 : ℝ) * Real.exp (5 / 2) * 1
              / (1 - Real.exp (-(12 / 5))) := by
        simpa using hmass
      have hstep1 : (∑ z ∈ F, (zeroMult z.1 z.2 : ℝ)
            * ‖Hk (11 / 2) (3 / 10) ((1 - z.2) * (Real.log q : ℂ))‖)
          ≤ ∑ z ∈ F, 4 / ((4 : ℝ) ^ (jjF z) * (Real.log (q : ℝ)) ^ 2)
              * ((zeroMult z.1 z.2 : ℝ) * Real.exp (-(49 / 10) * lamOf q z.2)) :=
        Finset.sum_le_sum (fun z hz => kernel_le hq z (hzmF z hz) (hhighF z hz))
      have hstep2 : (∑ z ∈ F, 4 / ((4 : ℝ) ^ (jjF z) * (Real.log (q : ℝ)) ^ 2)
              * ((zeroMult z.1 z.2 : ℝ) * Real.exp (-(49 / 10) * lamOf q z.2)))
          = 4 / ((4 : ℝ) ^ j * (Real.log (q : ℝ)) ^ 2)
              * (∑ z ∈ F, (zeroMult z.1 z.2 : ℝ) * Real.exp (-(49 / 10) * lamOf q z.2)) := by
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl (fun z hz => ?_)
        rw [(Finset.mem_filter.mp hz).2]
      rw [hGs]
      calc (∑ z ∈ F, (zeroMult z.1 z.2 : ℝ)
            * ‖Hk (11 / 2) (3 / 10) ((1 - z.2) * (Real.log q : ℂ))‖)
          ≤ 4 / ((4 : ℝ) ^ j * (Real.log (q : ℝ)) ^ 2)
              * (∑ z ∈ F, (zeroMult z.1 z.2 : ℝ) * Real.exp (-(49 / 10) * lamOf q z.2)) :=
            le_trans hstep1 hstep2.le
        _ ≤ 4 / ((4 : ℝ) ^ j * (Real.log (q : ℝ)) ^ 2)
              * (C₂ * ((2 : ℝ) ^ (j + 1)) ^ (3 / 2 : ℝ) * Real.exp (5 / 2) * 1
                  / (1 - Real.exp (-(12 / 5)))) := by
            refine mul_le_mul_of_nonneg_left hmass' ?_
            positivity
    have hgt : ∀ j ∈ ((S.image jjF).filter (fun j => ¬ j ≤ m)).filter (fun j => ¬ j ≤ J), J < j := by
      intro j hj
      simp only [Finset.mem_filter] at hj
      omega
    calc (∑ j ∈ ((S.image jjF).filter (fun j => ¬ j ≤ m)).filter (fun j => ¬ j ≤ J), Gs j)
        ≤ ∑ j ∈ ((S.image jjF).filter (fun j => ¬ j ≤ m)).filter (fun j => ¬ j ≤ J),
            4 / ((4 : ℝ) ^ j * (Real.log (q : ℝ)) ^ 2)
              * (C₂ * ((2 : ℝ) ^ (j + 1)) ^ (3 / 2 : ℝ) * Real.exp (5 / 2) * 1
                  / (1 - Real.exp (-(12 / 5)))) := Finset.sum_le_sum hper
      _ ≤ (4 * (Real.log (q : ℝ)) ^ (-2 : ℝ) * C₂
            * (Real.exp (5 / 2) / (1 - Real.exp (-(12 / 5)))) * 1)
            * (4 * (Ga * (2 : ℝ) ^ (-((J : ℝ) / 2)))) := by
          refine (hfac 1 (((S.image jjF).filter (fun j => ¬ j ≤ m)).filter
            (fun j => ¬ j ≤ J)) (by norm_num)).trans ?_
          refine mul_le_mul_of_nonneg_left ?_ (hconst_nonneg _ (by norm_num))
          exact mul_le_mul_of_nonneg_left (hG_tail J _ hgt) (by norm_num)
      _ ≤ (4 * (Real.log (q : ℝ)) ^ (-2 : ℝ) * C₂
            * (Real.exp (5 / 2) / (1 - Real.exp (-(12 / 5)))) * 1)
            * (4 * (Ga * lam1)) := by
          refine mul_le_mul_of_nonneg_left ?_ (hconst_nonneg _ (by norm_num))
          exact mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hJ_tail (by positivity))
            (by norm_num)
      _ = 4 * C₂ * (Real.exp (5 / 2) / (1 - Real.exp (-(12 / 5)))) * 4 * Ga
            * (Real.log (q : ℝ)) ^ (-2 : ℝ) * lam1 := by ring
  have hGeq : (∑ z ∈ S, (zeroMult z.1 z.2 : ℝ)
        * ‖Hk (11 / 2) (3 / 10) ((1 - z.2) * (Real.log q : ℂ))‖) = ∑ j ∈ S.image jjF, Gs j := by
    rw [hGs]
    exact (Finset.sum_fiberwise_of_maps_to (fun z hz => Finset.mem_image_of_mem jjF hz)
      (fun z => (zeroMult z.1 z.2 : ℝ)
        * ‖Hk (11 / 2) (3 / 10) ((1 - z.2) * (Real.log q : ℂ))‖)).symm
  rw [hGeq]
  have hsplit : (∑ j ∈ S.image jjF, Gs j)
      = (∑ j ∈ (S.image jjF).filter (fun j => j ≤ m), Gs j)
        + (∑ j ∈ ((S.image jjF).filter (fun j => ¬ j ≤ m)).filter (fun j => j ≤ J), Gs j)
        + (∑ j ∈ ((S.image jjF).filter (fun j => ¬ j ≤ m)).filter (fun j => ¬ j ≤ J), Gs j) := by
    rw [← Finset.sum_filter_add_sum_filter_not (S.image jjF) (fun j => j ≤ m) Gs]
    rw [← Finset.sum_filter_add_sum_filter_not ((S.image jjF).filter (fun j => ¬ j ≤ m))
      (fun j => j ≤ J) Gs]
    ring
  rw [hsplit]
  refine le_trans (add_le_add (add_le_add hA hB1) hB2) ?_
  rw [show 4 * C₂ * (Real.exp (5 / 2) / (1 - Real.exp (-(12 / 5)))) * 4 * Ga
        * Real.exp 58 * (Real.log (q : ℝ)) ^ (-2 : ℝ) * lam1
      + 4 * C₂ * (Real.exp (5 / 2) / (1 - Real.exp (-(12 / 5)))) * 4 * Ga
        * Real.exp 58 * (Real.log (q : ℝ)) ^ (-2 : ℝ) * lam1
      + 4 * C₂ * (Real.exp (5 / 2) / (1 - Real.exp (-(12 / 5)))) * 4 * Ga
        * (Real.log (q : ℝ)) ^ (-2 : ℝ) * lam1
      = 4 * C₂ * (Real.exp (5 / 2) / (1 - Real.exp (-(12 / 5)))) * 4 * Ga
        * (2 * Real.exp 58 + 1) * (Real.log (q : ℝ)) ^ (-2 : ℝ) * lam1 from by ring]


/-- **The `λ₁`-saving high-zero bound from the BGTZ repulsion** (assembled route: the `λ₁`-free
dyadic height bound for `λ₁ ≥ 1/1000`, and the BGTZ repulsion + dyadic height bound for
`λ₁ < 1/1000`). -/
theorem RestHighBGTZ (hrep : Work.LinnikAreas.Siegel.RepulsionBGTZ)
    (hfam : Work.ZeroDensity.LogFreeFamHeight (5 / 2) (3 / 2)) :
    Work.LinnikAreas.Siegel.RestHighBGTZSpec (-3 / 2) := by
  obtain ⟨Kf, hKfpos, q₀f, hKf⟩ := highFinsetBoundFree hfam
  obtain ⟨C₂, hC₂, q₀fam, hfam'⟩ := hfam
  obtain ⟨Cₛ, hCₛpos, hCₛ⟩ := lamOfEps200
  obtain ⟨Csi, hCsipos, hCsi⟩ := Siegel.lamOf_lower_bound
  obtain ⟨q₀rep, hrepall⟩ := hrep
  set K₂ : ℝ := 4 * C₂ * (Real.exp (5 / 2) / (1 - Real.exp (-(12 / 5)))) * 4
      * ((1 - (2 : ℝ) ^ (-(1 / 2) : ℝ))⁻¹) * (2 * Real.exp 58 + 1) with hK₂def
  have hK₂pos : 0 < K₂ := by
    rw [hK₂def]
    have h1 : Real.exp (-(12 / 5)) < 1 := Real.exp_lt_one_iff.mpr (by norm_num)
    have h3 : (2 : ℝ) ^ (-(1 / 2) : ℝ) < 1 := by
      rw [Real.rpow_neg (by norm_num : (0 : ℝ) ≤ 2)]
      exact inv_lt_one_of_one_lt₀ (Real.one_lt_rpow (by norm_num) (by norm_num))
    positivity
  set R : ℝ := 20 + 1 / Csi + 1 / Real.sqrt Cₛ with hRdef
  refine ⟨max (Kf * 1000) K₂, lt_max_of_lt_left (by positivity),
    max q₀f (max (max q₀rep q₀fam) (Nat.ceil (Real.exp R))), ?_⟩
  intro q hq hNq χ₁ β₁ hχ hsq hβ hz hlam10
  have hq₀f : q₀f ≤ q := le_trans (le_max_left _ _) hq
  have hq₀rep : q₀rep ≤ q :=
    le_trans (le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) (le_max_right _ _)) hq
  have hq₀fam : q₀fam ≤ q :=
    le_trans (le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) (le_max_right _ _)) hq
  have hqR : Nat.ceil (Real.exp R) ≤ q :=
    le_trans (le_max_right _ _) (le_trans (le_max_right _ _) hq)
  have hq2 : 1 < q := by
    have h1 : 2 ≤ Nat.ceil (Real.exp R) := by
      have h2 : (2 : ℝ) ≤ Real.exp R := by
        rw [← Real.exp_log (by norm_num : (0 : ℝ) < 2)]
        refine Real.exp_le_exp.mpr ?_
        have h5 : Real.log 2 ≤ 20 := by
          have h6 := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 2)
          linarith
        rw [hRdef]
        have h3 : 0 < 1 / Real.sqrt Cₛ := by positivity
        have h4 : 0 ≤ 1 / Csi := by positivity
        linarith
      have h3 : (2 : ℝ) ≤ (Nat.ceil (Real.exp R) : ℝ) := le_trans h2 (Nat.le_ceil _)
      exact_mod_cast h3
    have h4 : Nat.ceil (Real.exp R) ≤ q := hqR
    omega
  have hlog : 0 < Real.log (q : ℝ) := Real.log_pos (by exact_mod_cast hq2)
  have h𝓛R : R ≤ Real.log (q : ℝ) := by
    have h1 : Real.exp R ≤ (q : ℝ) := by
      have h2 : Real.exp R ≤ (Nat.ceil (Real.exp R) : ℝ) := Nat.le_ceil _
      exact le_trans h2 (by exact_mod_cast hqR)
    have h3 : Real.log (Real.exp R) ≤ Real.log (q : ℝ) :=
      Real.log_le_log (by positivity) h1
    rwa [Real.log_exp] at h3
  have h𝓛20 : 20 ≤ Real.log (q : ℝ) := by
    have h1 : 20 ≤ R := by
      rw [hRdef]
      have h2 : 0 < 1 / Real.sqrt Cₛ := by positivity
      have h3 : 0 ≤ 1 / Csi := by positivity
      linarith
    linarith
  have hCsilog : (1 : ℝ) ≤ Csi * Real.log (q : ℝ) := by
    have h1 : 1 / Csi ≤ Real.log (q : ℝ) := by
      have h2 : 1 / Csi ≤ R := by
        rw [hRdef]
        have h3 : 0 < 1 / Real.sqrt Cₛ := by positivity
        linarith
      linarith
    rw [div_le_iff₀ hCsipos] at h1
    linarith [h1]
  have hCsL2 : (1 : ℝ) ≤ Cₛ * Real.log (q : ℝ) ^ 2 := by
    have h1 : 1 / Real.sqrt Cₛ ≤ Real.log (q : ℝ) := by
      have h2 : 1 / Real.sqrt Cₛ ≤ R := by
        rw [hRdef]
        have h3 : 0 ≤ 1 / Csi := by positivity
        linarith
      linarith
    have h3 : Real.sqrt Cₛ * (1 / Real.sqrt Cₛ) = 1 := by
      field_simp [ne_of_gt (Real.sqrt_pos.mpr hCₛpos)]
    have h4 : (1 : ℝ) ≤ Real.sqrt Cₛ * Real.log (q : ℝ) := by nlinarith [h1, hCₛpos, h3, Real.sqrt_pos.mpr hCₛpos]
    nlinarith [h4, Real.sq_sqrt hCₛpos.le, sq_nonneg (Real.log (q : ℝ))]
  have hlampos : 0 < lamOf q (β₁ : ℂ) := Siegel.lamOf_pos hχ hβ hz
  have hCsi_app : Csi * Real.log (q : ℝ) / Real.sqrt (q : ℝ) ≤ lamOf q (β₁ : ℂ) :=
    hCsi q (by omega) χ₁ β₁ hχ hsq hβ hz
  have hCₛ_app : Cₛ * Real.log (q : ℝ) / (q : ℝ) ^ (1 / 200 : ℝ) ≤ lamOf q (β₁ : ℂ) :=
    hCₛ q (by omega) χ₁ β₁ hχ hsq hβ hz
  have hαhalf : Real.log (1 / lamOf q (β₁ : ℂ)) ≤ Real.log (q : ℝ) / 2 := by
    have h3 : 1 / lamOf q (β₁ : ℂ) ≤ Real.sqrt (q : ℝ) / (Csi * Real.log (q : ℝ)) := by
      rw [div_le_div_iff₀ hlampos (mul_pos hCsipos hlog)]
      have h4 : Csi * Real.log (q : ℝ) ≤ lamOf q (β₁ : ℂ) * Real.sqrt (q : ℝ) := by
        rw [div_le_iff₀ (Real.sqrt_pos.mpr (by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne q)))] at hCsi_app
        linarith [hCsi_app]
      linarith [h4]
    calc Real.log (1 / lamOf q (β₁ : ℂ))
        ≤ Real.log (Real.sqrt (q : ℝ) / (Csi * Real.log (q : ℝ))) :=
          Real.log_le_log (by positivity) h3
      _ = Real.log (q : ℝ) / 2 - Real.log (Csi * Real.log (q : ℝ)) := by
          have h1 : Real.log (Real.sqrt (q : ℝ) / (Csi * Real.log (q : ℝ)))
              = Real.log (Real.sqrt (q : ℝ)) - Real.log (Csi * Real.log (q : ℝ)) :=
            Real.log_div (ne_of_gt (Real.sqrt_pos.mpr (by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne q))))
              (ne_of_gt (mul_pos hCsipos hlog))
          have h2 : Real.log (Real.sqrt (q : ℝ)) = Real.log (q : ℝ) / 2 :=
            Real.log_sqrt (by positivity)
          rw [h1, h2]
      _ ≤ Real.log (q : ℝ) / 2 := by
          have h5 : 0 ≤ Real.log (Csi * Real.log (q : ℝ)) := Real.log_nonneg hCsilog
          linarith
  have hhy : 1 / ((q : ℝ) ^ (1 / 100 : ℝ) * Real.log (q : ℝ)) < lamOf q (β₁ : ℂ) := by
    have h1 : 1 / ((q : ℝ) ^ (1 / 100 : ℝ) * Real.log (q : ℝ))
        < Cₛ * Real.log (q : ℝ) / (q : ℝ) ^ (1 / 200 : ℝ) := by
      rw [div_lt_div_iff₀ (by positivity : (0 : ℝ) < (q : ℝ) ^ (1 / 100 : ℝ) * Real.log (q : ℝ))
        (by positivity : (0 : ℝ) < (q : ℝ) ^ (1 / 200 : ℝ))]
      have h2 : (q : ℝ) ^ (1 / 200 : ℝ) < (q : ℝ) ^ (1 / 100 : ℝ) :=
        Real.rpow_lt_rpow_of_exponent_lt (by exact_mod_cast hq2) (by norm_num)
      have h3 : (q : ℝ) ^ (1 / 100 : ℝ)
          ≤ (q : ℝ) ^ (1 / 100 : ℝ) * (Cₛ * Real.log (q : ℝ) ^ 2) :=
        le_mul_of_one_le_right (Real.rpow_nonneg (by positivity) _) hCsL2
      calc (1 : ℝ) * (q : ℝ) ^ (1 / 200 : ℝ) < (q : ℝ) ^ (1 / 100 : ℝ) := by simpa using h2
        _ ≤ (q : ℝ) ^ (1 / 100 : ℝ) * (Cₛ * Real.log (q : ℝ) ^ 2) := h3
        _ = (Cₛ * Real.log (q : ℝ)) * ((q : ℝ) ^ (1 / 100 : ℝ) * Real.log (q : ℝ)) := by ring
    linarith [hCₛ_app]
  have hrepq : ∀ (χ : DirichletCharacter ℂ q) (ρ : ℂ), zeroMult χ ρ ≠ 0 →
      ¬(χ = χ₁ ∧ ρ = (β₁ : ℂ)) →
      (Real.log (1 / lamOf q (β₁ : ℂ))
          - Real.log (24 * ((4 / 3 + 1 / 100 : ℝ)
              + (2 / 3 + 1 / 100 : ℝ) * (Real.log (5 + |ρ.im|) / Real.log q))))
        / ((4 / 3 + 1 / 100 : ℝ)
            + (2 / 3 + 1 / 100 : ℝ) * (Real.log (5 + |ρ.im|) / Real.log q))
        ≤ lamOf q ρ :=
    fun χ ρ hzm' hne => hrepall q hq₀rep χ₁ β₁ hχ hsq hβ hz hhy hlam10 χ ρ hzm' hne
  let p : DirichletCharacter ℂ q × ℂ → Prop := fun z =>
    zeroMult z.1 z.2 ≠ 0 ∧ 1 < |z.2.im| ∧ ¬(z.1 = χ₁ ∧ z.2 = (β₁ : ℂ))
  let F : DirichletCharacter ℂ q × ℂ → ℝ := fun z =>
    if p z then (zeroMult z.1 z.2 : ℝ)
      * ‖Hk (11 / 2) (3 / 10) ((1 - z.2) * (Real.log q : ℂ))‖ else 0
  have hFnn : 0 ≤ F := fun z => by
    simp only [F]
    split_ifs with hp
    · exact mul_nonneg (Nat.cast_nonneg _) (norm_nonneg _)
    · exact le_refl 0
  have hbound : ∀ u : Finset (DirichletCharacter ℂ q × ℂ),
      ∑ z ∈ u, F z ≤ max (Kf * 1000) K₂ * (Real.log (q : ℝ)) ^ (-2 : ℝ) * lamOf q (β₁ : ℂ) := by
    intro u
    have hsum_eq : ∑ z ∈ u, F z = ∑ z ∈ u.filter p, F z := by
      refine (Finset.sum_subset (Finset.filter_subset _ _) ?_).symm
      intro z hz hnotin
      have hp : ¬ p z := fun hpp => hnotin (Finset.mem_filter.mpr ⟨hz, hpp⟩)
      simp only [F]; rw [if_neg hp]
    have hSF : ∑ z ∈ u.filter p, F z = ∑ z ∈ u.filter p, (zeroMult z.1 z.2 : ℝ)
        * ‖Hk (11 / 2) (3 / 10) ((1 - z.2) * (Real.log q : ℂ))‖ := by
      refine Finset.sum_congr rfl (fun z hz => ?_)
      have hp : p z := (Finset.mem_filter.mp hz).2
      simp only [F]; rw [if_pos hp]
    rw [hsum_eq, hSF]
    by_cases hbig : (1 / 1000 : ℝ) ≤ lamOf q (β₁ : ℂ)
    · have h1 : (∑ z ∈ u.filter p, (zeroMult z.1 z.2 : ℝ)
            * ‖Hk (11 / 2) (3 / 10) ((1 - z.2) * (Real.log q : ℂ))‖)
          ≤ Kf * (Real.log (q : ℝ)) ^ (-2 : ℝ) :=
        hKf hq₀f hq2 χ₁ β₁ (u.filter p)
          (fun z hz => (Finset.mem_filter.mp hz).2.1)
          (fun z hz => (Finset.mem_filter.mp hz).2.2.1)
          (fun z hz => (Finset.mem_filter.mp hz).2.2.2)
      have h1000 : (1 : ℝ) ≤ 1000 * lamOf q (β₁ : ℂ) := by linarith [hbig]
      have h1' : 0 ≤ Kf * (Real.log (q : ℝ)) ^ (-2 : ℝ) :=
        mul_nonneg hKfpos.le (Real.rpow_nonneg hlog.le _)
      calc (∑ z ∈ u.filter p, (zeroMult z.1 z.2 : ℝ)
            * ‖Hk (11 / 2) (3 / 10) ((1 - z.2) * (Real.log q : ℂ))‖)
          ≤ Kf * (Real.log (q : ℝ)) ^ (-2 : ℝ) := h1
        _ ≤ Kf * (Real.log (q : ℝ)) ^ (-2 : ℝ) * (1000 * lamOf q (β₁ : ℂ)) :=
            le_mul_of_one_le_right h1' h1000
        _ = (Kf * 1000) * (Real.log (q : ℝ)) ^ (-2 : ℝ) * lamOf q (β₁ : ℂ) := by ring
        _ ≤ max (Kf * 1000) K₂ * (Real.log (q : ℝ)) ^ (-2 : ℝ) * lamOf q (β₁ : ℂ) := by
            refine mul_le_mul_of_nonneg_right ?_ hlampos.le
            exact mul_le_mul_of_nonneg_right (le_max_left _ _) (Real.rpow_nonneg hlog.le _)
    · have hsmall : lamOf q (β₁ : ℂ) ≤ 1 / 1000 := le_of_lt (not_le.mp hbig)
      have h2 : (∑ z ∈ u.filter p, (zeroMult z.1 z.2 : ℝ)
            * ‖Hk (11 / 2) (3 / 10) ((1 - z.2) * (Real.log q : ℂ))‖)
          ≤ K₂ * (Real.log (q : ℝ)) ^ (-2 : ℝ) * lamOf q (β₁ : ℂ) := by
        have h3 := highMassRep hq2 χ₁ β₁ hC₂ q₀fam hq₀fam (hfam' q hq₀fam) hrepq hlampos hsmall hαhalf h𝓛20
          (u.filter p)
          (fun z hz => (Finset.mem_filter.mp hz).2.1)
          (fun z hz => (Finset.mem_filter.mp hz).2.2.1)
          (fun z hz => (Finset.mem_filter.mp hz).2.2.2)
        rw [← hK₂def] at h3
        exact h3
      calc (∑ z ∈ u.filter p, (zeroMult z.1 z.2 : ℝ)
            * ‖Hk (11 / 2) (3 / 10) ((1 - z.2) * (Real.log q : ℂ))‖)
          ≤ K₂ * (Real.log (q : ℝ)) ^ (-2 : ℝ) * lamOf q (β₁ : ℂ) := h2
        _ ≤ max (Kf * 1000) K₂ * (Real.log (q : ℝ)) ^ (-2 : ℝ) * lamOf q (β₁ : ℂ) := by
            refine mul_le_mul_of_nonneg_right ?_ hlampos.le
            exact mul_le_mul_of_nonneg_right (le_max_right _ _) (Real.rpow_nonneg hlog.le _)
  have hsumm : Summable F := summable_of_sum_le hFnn hbound
  have htsum : ∑' z : DirichletCharacter ℂ q × ℂ, F z
      ≤ max (Kf * 1000) K₂ * (Real.log (q : ℝ)) ^ (-2 : ℝ) * lamOf q (β₁ : ℂ) :=
    Real.tsum_le_of_sum_le hFnn hbound
  rw [Summable.tsum_prod hsumm] at htsum
  rw [tsum_fintype] at htsum
  have hEq : Siegel.restHighZeroSum χ₁ (β₁ : ℂ) (11 / 2) (3 / 10)
      = ∑ χ : DirichletCharacter ℂ q, ∑' ρ : ℂ, F (χ, ρ) := rfl
  rw [hEq]
  have hpow : (Real.log (q : ℝ)) ^ (-2 : ℝ)
      = (Real.log (q : ℝ)) ^ (-(1 / 2) : ℝ) * (Real.log (q : ℝ)) ^ (-(3 / 2) : ℝ) := by
    rw [← Real.rpow_add hlog]
    norm_num
  have hhalf : (Real.log (q : ℝ)) ^ (-(1 / 2) : ℝ) ≤ 1 := by
    rw [Real.rpow_neg hlog.le, inv_le_one₀ (Real.rpow_pos_of_pos hlog _)]
    have h1 : (1 : ℝ) ≤ Real.log (q : ℝ) := by linarith
    calc (1 : ℝ) = (1 : ℝ) ^ (1 / 2 : ℝ) := by norm_num
      _ ≤ (Real.log (q : ℝ)) ^ (1 / 2 : ℝ) :=
          Real.rpow_le_rpow (by norm_num) h1 (by norm_num)
  calc (∑ χ : DirichletCharacter ℂ q, ∑' ρ : ℂ, F (χ, ρ))
      ≤ max (Kf * 1000) K₂ * (Real.log (q : ℝ)) ^ (-2 : ℝ) * lamOf q (β₁ : ℂ) := htsum
    _ = max (Kf * 1000) K₂
          * ((Real.log (q : ℝ)) ^ (-(1 / 2) : ℝ) * (Real.log (q : ℝ)) ^ (-(3 / 2) : ℝ))
          * lamOf q (β₁ : ℂ) := by rw [hpow]
    _ ≤ max (Kf * 1000) K₂ * (1 * (Real.log (q : ℝ)) ^ (-(3 / 2) : ℝ)) * lamOf q (β₁ : ℂ) := by
        refine mul_le_mul_of_nonneg_right ?_ hlampos.le
        refine mul_le_mul_of_nonneg_left ?_ (le_of_lt (lt_max_of_lt_left (by positivity)))
        exact mul_le_mul_of_nonneg_right hhalf (Real.rpow_nonneg hlog.le _)
    _ = max (Kf * 1000) K₂ * lamOf q (β₁ : ℂ) * (Real.log (q : ℝ)) ^ (-3 / 2 : ℝ) := by
        rw [show (-(3 / 2) : ℝ) = -3 / 2 by norm_num]
        ring

end
end Work.LinnikAreas
