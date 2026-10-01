import Mathlib
import Submission.Work.LinnikAreas.sum_mul_exp_neg_le_of_count
import Submission.Work.LinnikAreas.pairCountHeight_dom
import Submission.Work.LinnikAreas.RestHighBGTZ
import Submission.Work.LinnikAreas.SiegelBase
import Submission.Work.SiegelAbsorb.windowMassRegion
import Submission.Work.SiegelAbsorb.windowMassHigh

/-!
# `Work.SiegelAbsorb.windowMassFree2`

The `λ₁`-free mass of a finite set `S` of zero-pairs of level `q`, cut at the height
`θ·𝓛` (`𝓛 = log q`): below the cut only the count `pairCountHeight ≤ C₂·e^{(5/2)t}·H^{3/2}`
is used, above it the count `pairCountHeight ≤ C₃·e^{(9/2)t}·H^{3/2}` is used, and the two
windows contribute

`C₂·H^{3/2}·e^{5/2}/(1 - e^{-12/5})`  and
`C₃·H^{3/2}·e^{9/2}·e^{-(2/5)θ𝓛}/(1 - e^{-2/5})`.

The two windows are handled by `Work.SiegelAbsorb.windowMassLow` (proved here) and
`Work.SiegelAbsorb.windowMassHigh`, both of which are direct consequences of the Abel
summation lemma `Work.SiegelAbsorb.windowMassRegion`.

On a zero of `zeroMult`, `λ = (1 - Re ρ)·𝓛` lies in `(0, 𝓛)`
(`Work.LinnikAreas.zeroMult_re_pos`, `Work.LinnikAreas.boxMaxZeroAux.zeroMult_re_lt_one`),
which is what makes the per-window floor `Λ > 0` available without any hypothesis on `S`.
-/

namespace Work.SiegelAbsorb

open scoped Classical BigOperators

/-- **The mass of the `λ ≤ θ𝓛` window.**  Same statement as the delegated
`Work.SiegelAbsorb.windowMassLow`, proved here on top of `windowMassRegion`: the floor is the
minimum of `λ` over `S`, which is positive because every `λ` is, and it is then dropped from
the numerator via `e^{-(12/5)Λ} ≤ 1`. -/
private lemma windowMassLowAux {q : ℕ} [NeZero q] (hq : 1 < q) (χ₁ : DirichletCharacter ℂ q)
    (β₁ : ℂ) {C₂ H L₀ : ℝ} (hC₂ : 0 < C₂) (hH : 0 < H)
    (hcnt : ∀ t : ℝ, 0 < t → t ≤ L₀ →
      Work.LinnikAreas.Siegel.pairCountHeight χ₁ β₁ t (H * Real.log (q : ℝ))
        ≤ C₂ * Real.exp ((5 / 2) * t) * H ^ (3 / 2 : ℝ))
    (S : Finset (DirichletCharacter ℂ q × ℂ))
    (hzm : ∀ z ∈ S, Work.LinnikContract.zeroMult z.1 z.2 ≠ 0)
    (hexc : ∀ z ∈ S, ¬(z.1 = χ₁ ∧ z.2 = β₁))
    (him : ∀ z ∈ S, |z.2.im| * Real.log (q : ℝ) ≤ H * Real.log (q : ℝ))
    (hlamL : ∀ z ∈ S, Work.LinnikContract.lamOf q z.2 ≤ L₀)
    (hpos : ∀ z ∈ S, 0 < Work.LinnikContract.lamOf q z.2) :
    (∑ z ∈ S, (Work.LinnikContract.zeroMult z.1 z.2 : ℝ)
        * Real.exp (-(49 / 10) * Work.LinnikContract.lamOf q z.2))
      ≤ C₂ * H ^ (3 / 2 : ℝ) * Real.exp (5 / 2) / (1 - Real.exp (-(12 / 5))) := by
  have hden : 0 < 1 - Real.exp (-(12 / 5)) := by
    have h : Real.exp (-(12 / 5)) < 1 := Real.exp_lt_one_iff.mpr (by norm_num)
    linarith
  rcases S.eq_empty_or_nonempty with hS | hne
  · subst hS
    simp only [Finset.sum_empty]
    exact div_nonneg (by positivity) hden.le
  · set Λ : ℝ := S.inf' hne (fun z => Work.LinnikContract.lamOf q z.2) with hΛdef
    have hΛpos : 0 < Λ := by
      obtain ⟨z, hz, heq⟩ :=
        Finset.exists_mem_eq_inf' hne (fun z => Work.LinnikContract.lamOf q z.2)
      rw [hΛdef, heq]; exact hpos z hz
    have hΛle : ∀ z ∈ S, Λ ≤ Work.LinnikContract.lamOf q z.2 := fun z hz =>
      Finset.inf'_le (s := S) (fun z => Work.LinnikContract.lamOf q z.2) hz
    have hmain := windowMassRegion (q := q) hq χ₁ β₁ (C := C₂) (H := H)
      (a₀ := 49 / 10) (c := 5 / 2) (Λ := Λ) (L := L₀)
      hC₂ hH (by norm_num) (by norm_num) (by norm_num) hΛpos hcnt S hzm hexc him hΛle hlamL
    rw [show (5 / 2 : ℝ) - 49 / 10 = -(12 / 5) by norm_num] at hmain
    refine hmain.trans ?_
    have hexp_le : Real.exp (-(12 / 5) * Λ) ≤ 1 := by
      rw [Real.exp_le_one_iff]; nlinarith [hΛpos]
    have hnum : 0 ≤ C₂ * H ^ (3 / 2 : ℝ) * Real.exp (5 / 2) := by positivity
    calc C₂ * H ^ (3 / 2 : ℝ) * Real.exp (5 / 2) * Real.exp (-(12 / 5) * Λ)
            / (1 - Real.exp (-(12 / 5)))
        ≤ C₂ * H ^ (3 / 2 : ℝ) * Real.exp (5 / 2) * 1 / (1 - Real.exp (-(12 / 5))) :=
          div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hexp_le hnum) hden.le
      _ = C₂ * H ^ (3 / 2 : ℝ) * Real.exp (5 / 2) / (1 - Real.exp (-(12 / 5))) := by ring

lemma windowMassFree2 {q : ℕ} [NeZero q] (hq : 1 < q) (χ₁ : DirichletCharacter ℂ q) (β₁ : ℂ)
    {C₂ C₃ H θ : ℝ} (hC₂ : 0 < C₂) (hC₃ : 0 < C₃) (hH : 0 < H) (hθ : 0 < θ)
    (hcnt₁ : ∀ t : ℝ, 0 < t → t ≤ θ * Real.log (q : ℝ) →
      Work.LinnikAreas.Siegel.pairCountHeight χ₁ β₁ t (H * Real.log (q : ℝ))
        ≤ C₂ * Real.exp ((5 / 2) * t) * H ^ (3 / 2 : ℝ))
    (hcnt₂ : ∀ t : ℝ, 0 < t → t ≤ Real.log (q : ℝ) →
      Work.LinnikAreas.Siegel.pairCountHeight χ₁ β₁ t (H * Real.log (q : ℝ))
        ≤ C₃ * Real.exp ((9 / 2) * t) * H ^ (3 / 2 : ℝ))
    (S : Finset (DirichletCharacter ℂ q × ℂ))
    (hzm : ∀ z ∈ S, Work.LinnikContract.zeroMult z.1 z.2 ≠ 0)
    (hexc : ∀ z ∈ S, ¬(z.1 = χ₁ ∧ z.2 = β₁))
    (him : ∀ z ∈ S, |z.2.im| * Real.log (q : ℝ) ≤ H * Real.log (q : ℝ)) :
    (∑ z ∈ S, (Work.LinnikContract.zeroMult z.1 z.2 : ℝ)
        * Real.exp (-(49 / 10) * Work.LinnikContract.lamOf q z.2))
      ≤ C₂ * H ^ (3 / 2 : ℝ) * Real.exp (5 / 2) / (1 - Real.exp (-(12 / 5)))
        + C₃ * H ^ (3 / 2 : ℝ) * Real.exp (9 / 2) * Real.exp (-(2 / 5) * (θ * Real.log (q : ℝ)))
            / (1 - Real.exp (-(2 / 5))) := by
  have hlog : 0 < Real.log (q : ℝ) := Real.log_pos (by exact_mod_cast hq)
  -- every `λ` of a counted zero is positive, and at most `𝓛`
  have hpos : ∀ z ∈ S, 0 < Work.LinnikContract.lamOf q z.2 := by
    intro z hz
    have h1 : z.2.re < 1 :=
      Work.LinnikAreas.boxMaxZeroAux.zeroMult_re_lt_one z.1 (hzm z hz)
    rw [Work.LinnikContract.lamOf]
    exact mul_pos (by linarith) hlog
  have hlt : ∀ z ∈ S, Work.LinnikContract.lamOf q z.2 ≤ Real.log (q : ℝ) := by
    intro z hz
    have h1 : 0 < z.2.re := Work.LinnikAreas.zeroMult_re_pos z.1 (hzm z hz)
    rw [Work.LinnikContract.lamOf]
    nlinarith [hlog]
  set p : DirichletCharacter ℂ q × ℂ → Prop :=
    fun z => Work.LinnikContract.lamOf q z.2 ≤ θ * Real.log (q : ℝ) with hpdef
  -- the low window (below the cut)
  have hlow : (∑ z ∈ S.filter p, (Work.LinnikContract.zeroMult z.1 z.2 : ℝ)
        * Real.exp (-(49 / 10) * Work.LinnikContract.lamOf q z.2))
      ≤ C₂ * H ^ (3 / 2 : ℝ) * Real.exp (5 / 2) / (1 - Real.exp (-(12 / 5))) :=
    windowMassLowAux (q := q) hq χ₁ β₁ (C₂ := C₂) (H := H) (L₀ := θ * Real.log (q : ℝ))
      hC₂ hH hcnt₁ (S.filter p)
      (fun z hz => hzm z (Finset.mem_filter.mp hz).1)
      (fun z hz => hexc z (Finset.mem_filter.mp hz).1)
      (fun z hz => him z (Finset.mem_filter.mp hz).1)
      (fun z hz => (Finset.mem_filter.mp hz).2)
      (fun z hz => hpos z (Finset.mem_filter.mp hz).1)
  -- the high window (above the cut)
  have hhigh : (∑ z ∈ S.filter (fun z => ¬ p z), (Work.LinnikContract.zeroMult z.1 z.2 : ℝ)
        * Real.exp (-(49 / 10) * Work.LinnikContract.lamOf q z.2))
      ≤ C₃ * H ^ (3 / 2 : ℝ) * Real.exp (9 / 2)
          * Real.exp (-(2 / 5) * (θ * Real.log (q : ℝ))) / (1 - Real.exp (-(2 / 5))) :=
    windowMassHigh (q := q) hq χ₁ β₁ (C₃ := C₃) (H := H) (θ := θ)
      hC₃ hH hθ hcnt₂ (S.filter (fun z => ¬ p z))
      (fun z hz => hzm z (Finset.mem_filter.mp hz).1)
      (fun z hz => hexc z (Finset.mem_filter.mp hz).1)
      (fun z hz => him z (Finset.mem_filter.mp hz).1)
      (fun z hz => not_le.mp (Finset.mem_filter.mp hz).2)
      (fun z hz => hlt z (Finset.mem_filter.mp hz).1)
  have hsplit := Finset.sum_filter_add_sum_filter_not S p
    (fun z => (Work.LinnikContract.zeroMult z.1 z.2 : ℝ)
      * Real.exp (-(49 / 10) * Work.LinnikContract.lamOf q z.2))
  rw [← hsplit]
  linarith

end Work.SiegelAbsorb
