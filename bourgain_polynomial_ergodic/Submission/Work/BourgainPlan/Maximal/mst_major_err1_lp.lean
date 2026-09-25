import Mathlib
import Submission.Work.BourgainPlan.Maximal.mst_major_err1_l2
import Submission.Work.BourgainPlan.Maximal.mst_major_err1_triv
import Submission.Work.BourgainPlan.Maximal.mst_majErr_interp
import Submission.Work.BourgainPlan.Maximal.mst_interp_arithmetic
import Submission.Work.BourgainPlan.Maximal.mst_minor_per_n

/-!
# The `ℓᵖ` form of the first major-arc error (MST §4.2, eq. (73))

Combines the two endpoints of the first major-arc error — the `ℓ²` gain `2^{−n/2}`
(`mst_major_err1_l2`) and the trivial `ℓʳ` bound `exp(n^{1/10})` (`mst_major_err1_triv`) — by
Riesz–Thorin at a fixed level (`opMulFinsuppLM_interp`) and the arithmetic of the interpolation
(`mst_interp_arithmetic`), to produce the `ℓᵖ` bound with exponential gain `2^{−cn}` for every
`p ∈ (1,2)`, which is the hypothesis `herr1` of the §6 assembly.
-/

open MeasureTheory Finset
open scoped BigOperators ENNReal

set_option autoImplicit false

namespace Work.BourgainPlan.Maximal

open Work.BourgainPlan.IonescuWainger

noncomputable section

local notation "haarT" => (AddCircle.haarAddCircle (T := 1))

/-- **The first major-arc error in `ℓᵖ`** (MST §4.2 eq. (73)): for every `p ∈ (1,2)` there are
`C > 0` and `c > 0` such that for all large `n` the multiplier `m_{2^n}Ξ_n − ν_{2^n}` satisfies the
`ℓᵖ` bound with gain `C 2^{−cn}`, uniformly in the finitely supported input. -/
theorem mst_major_err1_lp (P : Polynomial ℤ) (hd : 2 ≤ P.natDegree) (hc : 0 < P.leadingCoeff)
    {χ : ℝ} (hχ0 : 0 < χ) (hχ1 : χ < 1 / 10) (η : ℝ → ℂ) (M : ℝ) (hM : 0 < M)
    (hηbd : ∀ x : ℝ, ‖η x‖ ≤ M)
    (hη1 : ∀ x : ℝ, |x| ≤ 1 / 4 → η x = 1) (hη2 : ∀ x : ℝ, 1 / 2 < |x| → η x = 0)
    (l : ℕ) (hl : 1 ≤ l)
    (A : ℝ) (hA : 0 < A)
    (hcd : ∀ n : ℕ, ContDiff ℝ 2 (Work.BourgainPlan.Thm52.circleLift
      (mstEta P.natDegree χ η n)))
    (hbdd : ∀ (n : ℕ) (x : ℝ), ‖Work.BourgainPlan.Thm52.circleLift
      (mstEta P.natDegree χ η n) x‖ ≤ A)
    (hder : ∀ (n : ℕ) (x : ℝ), |x| * ‖deriv (Work.BourgainPlan.Thm52.circleLift
      (mstEta P.natDegree χ η n)) x‖ ≤ A)
    (hder2 : ∀ (n : ℕ) (x : ℝ), |x| ^ 2 * ‖iteratedDeriv 2 (Work.BourgainPlan.Thm52.circleLift
      (mstEta P.natDegree χ η n)) x‖ ≤ A)
    (hrep : ∃ N₀ : ℕ, ∀ n : ℕ, N₀ ≤ n → ∀ β ∈ mstU l n, ∃ (q : ℕ) (a : ℤ),
      0 < q ∧ 0 ≤ a ∧ a < q ∧ Work.BourgainPlan.IonescuWainger.arcPt q a = β ∧
        mstG P β = polyWeight P q a ∧
        (q : ℝ) ≤ Real.exp (((n : ℝ) ^ l) ^ (mstRho l)))
    (hηml : ∀ n : ℕ, MeasureTheory.MemLp (mstEta P.natDegree χ η n) ⊤ haarT)
    (hνml : ∀ n : ℕ, MeasureTheory.MemLp (mstNu P l P.natDegree χ η n) ⊤ haarT)
    {p : ℝ} (hp : 1 < p) (hp2 : p < 2) :
    ∃ C c : ℝ, 0 < C ∧ 0 < c ∧ ∃ N₁ : ℕ, ∀ n : ℕ, N₁ ≤ n → ∀ g : ℤ →₀ ℂ,
      MeasureTheory.eLpNorm (Work.BourgainPlan.IonescuWainger.opMul
          (mstMajErr1Cls P l P.natDegree χ η n (hηml n) (hνml n)) (⇑g)
          (Work.BourgainPlan.IonescuWainger.memℓp_finsupp g))
          (ENNReal.ofReal p) MeasureTheory.Measure.count
        ≤ ENNReal.ofReal (C * (2 : ℝ) ^ (-(c * (n : ℝ))))
          * MeasureTheory.eLpNorm (⇑g) (ENNReal.ofReal p) MeasureTheory.Measure.count := by
  set r : ℝ := (1 + p) / 2 with hrdef
  have hr1 : 1 < r := by rw [hrdef]; linarith
  have hrp : r < p := by rw [hrdef]; linarith
  have hp0 : (0 : ℝ) < p := lt_trans zero_lt_one hp
  set θ : ℝ := (1 / r - 1 / p) / (1 / r - 1 / 2) with hθdef
  have hden : 0 < 1 / r - 1 / 2 := by
    have h : (1 : ℝ) / 2 < 1 / r := one_div_lt_one_div_of_lt (by linarith) (by linarith)
    linarith
  have hnum : 0 < 1 / r - 1 / p := by
    have h : (1 : ℝ) / p < 1 / r := one_div_lt_one_div_of_lt (by linarith) hrp
    linarith
  have hθ0 : 0 < θ := div_pos hnum hden
  have hθ1 : θ < 1 := by
    rw [hθdef, div_lt_one hden]
    have h : (1 : ℝ) / 2 < 1 / p := one_div_lt_one_div_of_lt hp0 hp2
    linarith
  obtain ⟨C₂, hC₂, N₂, h2⟩ :=
    mst_major_err1_l2 P hd hc hχ0 hχ1 η M hM.le hηbd hη1 hη2 l hl hrep hηml hνml
  obtain ⟨C₁, hC₁, h1⟩ :=
    mst_major_err1_triv P hd hc hχ0 hχ1 η M hM.le hηbd hη1 hη2 l hl hr1 A hA hcd hbdd hder
      hder2 hηml hνml
  obtain ⟨Ca, ca, hCa, hca, harith⟩ :=
    mst_interp_arithmetic (θ := 1 - θ) (C₁ := C₁) (C₂ := C₂) (by linarith) (by linarith) hC₁ hC₂
  refine ⟨Ca, ca, hCa, hca, max N₂ 0, fun n hn g => ?_⟩
  have hn₂ : N₂ ≤ n := le_trans (le_max_left _ _) hn
  set Φ : Lp ℂ ⊤ haarT := mstMajErr1Cls P l P.natDegree χ η n (hηml n) (hνml n) with hΦ
  -- the two endpoint bounds in the `opMulFinsuppLM` form
  have h2' : ∀ f : ℤ →₀ ℂ, MeasureTheory.eLpNorm (opMulFinsuppLM Φ f)
      (ENNReal.ofReal 2) MeasureTheory.Measure.count
      ≤ ENNReal.ofReal (C₂ * (2 : ℝ) ^ (-((n : ℝ) / 2)))
        * MeasureTheory.eLpNorm (⇑f) (ENNReal.ofReal 2) MeasureTheory.Measure.count := by
    intro f
    rw [opMulFinsuppLM_apply]
    exact h2 n hn₂ (⇑f) (memℓp_finsupp f)
  have h1' : ∀ f : ℤ →₀ ℂ, MeasureTheory.eLpNorm (opMulFinsuppLM Φ f)
      (ENNReal.ofReal r) MeasureTheory.Measure.count
      ≤ ENNReal.ofReal (C₁ * Real.exp (((n : ℝ) ^ l) ^ (mstRho l)))
        * MeasureTheory.eLpNorm (⇑f) (ENNReal.ofReal r) MeasureTheory.Measure.count := by
    intro f
    rw [opMulFinsuppLM_apply]
    exact h1 n (⇑f) (memℓp_finsupp f)
  -- the exponent identity `(n^l)^{ρ} = n^{1/10}`
  have hpow : (((n : ℝ) ^ l) ^ (mstRho l)) = (n : ℝ) ^ (1 / 10 : ℝ) := by
    rw [mstRho, ← Real.rpow_natCast (n : ℝ) l, ← Real.rpow_mul (Nat.cast_nonneg n)]
    congr 1
    have hl0 : (0 : ℝ) < (l : ℝ) := by exact_mod_cast hl
    field_simp
  -- Riesz–Thorin at this level
  have hB : 0 < C₂ * (2 : ℝ) ^ (-((n : ℝ) / 2)) :=
    mul_pos hC₂ (Real.rpow_pos_of_pos (by norm_num) _)
  have hbase := opMulFinsuppLM_interp Φ (r := r) (p := p)
    (A := C₁ * Real.exp (((n : ℝ) ^ l) ^ (mstRho l))) (B := C₂ * (2 : ℝ) ^ (-((n : ℝ) / 2)))
    hr1 hrp hp2 (mul_pos hC₁ (Real.exp_pos _)) hB h1' h2' g
  rw [← hθdef] at hbase
  rw [hpow] at hbase
  -- the arithmetic of the interpolation
  have hAB : (C₁ * Real.exp ((n : ℝ) ^ (1 / 10 : ℝ))) ^ (1 - θ)
      * (C₂ * (2 : ℝ) ^ (-((n : ℝ) / 2))) ^ θ ≤ Ca * (2 : ℝ) ^ (-(ca * (n : ℝ))) := by
    have h := harith n
    rw [pow_one, show (1 : ℝ) - (1 - θ) = θ by ring] at h
    calc (C₁ * Real.exp ((n : ℝ) ^ (1 / 10 : ℝ))) ^ (1 - θ)
          * (C₂ * (2 : ℝ) ^ (-((n : ℝ) / 2))) ^ θ
        = (C₂ * (2 : ℝ) ^ (-((n : ℝ) / 2))) ^ θ
          * (C₁ * Real.exp ((n : ℝ) ^ (1 / 10 : ℝ))) ^ (1 - θ) := by ring
      _ ≤ Ca * (2 : ℝ) ^ (-(ca * (n : ℝ))) := h
  refine hbase.trans ?_
  exact mul_le_mul_of_nonneg_right (ENNReal.ofReal_le_ofReal hAB) (by simp)

end

end Work.BourgainPlan.Maximal
