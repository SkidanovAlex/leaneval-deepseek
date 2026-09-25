import Mathlib
import Submission.Work.BourgainPlan.Maximal.mst_major_err2_l2
import Submission.Work.BourgainPlan.Maximal.mst_major_err2_triv
import Submission.Work.BourgainPlan.Maximal.mst_majErr_interp
import Submission.Work.BourgainPlan.Maximal.mst_interp_arithmetic_exp

namespace Work.BourgainPlan.Maximal

open MeasureTheory Finset
open scoped BigOperators ENNReal

set_option autoImplicit false

noncomputable section

local notation "haarT" => (AddCircle.haarAddCircle (T := 1))

open Work.BourgainPlan.IonescuWainger in
/-- **Interpolation of the two endpoints of a major-arc error, abstractly.**

For an *arbitrary* family `Φ : ℕ → Lp ℂ ⊤ haarT` of symbols, an `ℓ²` bound with gain
`C₂ 2^{−c₂ n}` (`h2`) and an `ℓ^r` bound with the loss `C₁ exp((n^l)^{ρ_l})` for `r = (1+p)/2`
(`h1`) interpolate (Riesz–Thorin at the fixed level `n`, `opMulFinsuppLM_interp`) into an `ℓᵖ` bound
with gain `C 2^{−cn}` for some `C, c > 0`, uniformly in the finitely supported input.

Keeping `Φ` an opaque variable is essential: the actual symbols `mstMajErr2Cls …` are `Finset.sum`s
of `Lp` values with dependent `MemLp` proof arguments, and unfolding them inside `eLpNorm`/
`opMulFinsuppLM` goals makes elaboration diverge. -/
theorem opMul_family_interp_exp (Φ : ℕ → Lp ℂ ⊤ haarT) {p : ℝ} (hp : 1 < p) (hp2 : p < 2)
    {C₂ c₂ : ℝ} (hC₂ : 0 < C₂) (hc₂ : 0 < c₂) {N₂ : ℕ}
    (h2 : ∀ n : ℕ, N₂ ≤ n → ∀ (f : ℤ → ℂ) (hf : Memℓp f 2),
      MeasureTheory.eLpNorm (opMul (Φ n) f hf) (ENNReal.ofReal 2) MeasureTheory.Measure.count
        ≤ ENNReal.ofReal (C₂ * (2 : ℝ) ^ (-(c₂ * (n : ℝ))))
          * MeasureTheory.eLpNorm f (ENNReal.ofReal 2) MeasureTheory.Measure.count)
    {C₁ : ℝ} (hC₁ : 0 < C₁) {l : ℕ} (hl : 1 ≤ l)
    (h1 : ∀ n : ℕ, ∀ (f : ℤ → ℂ) (hf : Memℓp f 2),
      MeasureTheory.eLpNorm (opMul (Φ n) f hf) (ENNReal.ofReal ((1 + p) / 2))
          MeasureTheory.Measure.count
        ≤ ENNReal.ofReal (C₁ * Real.exp (((n : ℝ) ^ l) ^ (mstRho l)))
          * MeasureTheory.eLpNorm f (ENNReal.ofReal ((1 + p) / 2))
              MeasureTheory.Measure.count) :
    ∃ C c : ℝ, 0 < C ∧ 0 < c ∧ ∃ N₁ : ℕ, ∀ n : ℕ, N₁ ≤ n → ∀ g : ℤ →₀ ℂ,
      MeasureTheory.eLpNorm (opMul (Φ n) (⇑g) (memℓp_finsupp g))
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
  obtain ⟨Ca, ca, hCa, hca, harith⟩ :=
    mst_interp_arithmetic_exp (θ := 1 - θ) (C₁ := C₁) (C₂ := C₂) (c₂ := c₂)
      (by linarith) (by linarith) hC₁ hC₂ hc₂
  refine ⟨Ca, ca, hCa, hca, max N₂ 0, fun n hn g => ?_⟩
  have hn₂ : N₂ ≤ n := le_trans (le_max_left _ _) hn
  -- the two endpoint bounds in the `opMulFinsuppLM` form
  have h2' : ∀ f : ℤ →₀ ℂ, MeasureTheory.eLpNorm (opMulFinsuppLM (Φ n) f)
      (ENNReal.ofReal 2) MeasureTheory.Measure.count
      ≤ ENNReal.ofReal (C₂ * (2 : ℝ) ^ (-(c₂ * (n : ℝ))))
        * MeasureTheory.eLpNorm (⇑f) (ENNReal.ofReal 2) MeasureTheory.Measure.count := by
    intro f
    rw [opMulFinsuppLM_apply]
    exact h2 n hn₂ (⇑f) (memℓp_finsupp f)
  have h1' : ∀ f : ℤ →₀ ℂ, MeasureTheory.eLpNorm (opMulFinsuppLM (Φ n) f)
      (ENNReal.ofReal r) MeasureTheory.Measure.count
      ≤ ENNReal.ofReal (C₁ * Real.exp (((n : ℝ) ^ l) ^ (mstRho l)))
        * MeasureTheory.eLpNorm (⇑f) (ENNReal.ofReal r) MeasureTheory.Measure.count := by
    intro f
    rw [opMulFinsuppLM_apply]
    exact h1 n (⇑f) (memℓp_finsupp f)
  -- the exponent identity `(n^l)^{ρ_l} = n^{1/10}`
  have hpow : (((n : ℝ) ^ l) ^ (mstRho l)) = (n : ℝ) ^ (1 / 10 : ℝ) := by
    rw [mstRho, ← Real.rpow_natCast (n : ℝ) l, ← Real.rpow_mul (Nat.cast_nonneg n)]
    congr 1
    have hl0 : (0 : ℝ) < (l : ℝ) := by exact_mod_cast hl
    field_simp
  -- Riesz–Thorin at this level
  have hB : 0 < C₂ * (2 : ℝ) ^ (-(c₂ * (n : ℝ))) :=
    mul_pos hC₂ (Real.rpow_pos_of_pos (by norm_num) _)
  have hbase := opMulFinsuppLM_interp (Φ n) (r := r) (p := p)
    (A := C₁ * Real.exp (((n : ℝ) ^ l) ^ (mstRho l)))
    (B := C₂ * (2 : ℝ) ^ (-(c₂ * (n : ℝ))))
    hr1 hrp hp2 (mul_pos hC₁ (Real.exp_pos _)) hB h1' h2' g
  rw [← hθdef] at hbase
  rw [hpow] at hbase
  -- the arithmetic of the interpolation
  have hAB : (C₁ * Real.exp ((n : ℝ) ^ (1 / 10 : ℝ))) ^ (1 - θ)
      * (C₂ * (2 : ℝ) ^ (-(c₂ * (n : ℝ)))) ^ θ ≤ Ca * (2 : ℝ) ^ (-(ca * (n : ℝ))) := by
    have h := harith n
    rw [pow_one, show (1 : ℝ) - (1 - θ) = θ by ring] at h
    calc (C₁ * Real.exp ((n : ℝ) ^ (1 / 10 : ℝ))) ^ (1 - θ)
          * (C₂ * (2 : ℝ) ^ (-(c₂ * (n : ℝ)))) ^ θ
        = (C₂ * (2 : ℝ) ^ (-(c₂ * (n : ℝ)))) ^ θ
          * (C₁ * Real.exp ((n : ℝ) ^ (1 / 10 : ℝ))) ^ (1 - θ) := by ring
      _ ≤ Ca * (2 : ℝ) ^ (-(ca * (n : ℝ))) := h
  rw [opMulFinsuppLM_apply] at hbase
  exact hbase.trans (mul_le_mul_of_nonneg_right (ENNReal.ofReal_le_ofReal hAB) (by simp))

/-- The second major-arc error in `ℓᵖ` (MST §4.2 eq. (80)): for every `p ∈ (1,2)` there are `C > 0` and `c > 0` such that for all large `n` the multiplier `ν_{2^n} − Σ_{s<n} ν^s_{2^n}` satisfies the `ℓᵖ` bound with gain `C 2^{−cn}`, uniformly in the finitely supported input.

This is the exact analogue of `mst_major_err1_lp` (already proved, `Maximal/mst_major_err1_lp.lean`; use it as the template for both the statement and the argument) with the two proved endpoints of the second error — `mst_major_err2_l2` (the `ℓ²` gain `C₂ 2^{−c₂n}`) and `mst_major_err2_triv` (the trivial `ℓʳ` bound `C₁ exp(n^{1/10})`) — Riesz–Thorin at a fixed level (`opMulFinsuppLM_interp`, with `r := (1+p)/2`) and the arithmetic `mst_interp_arithmetic_exp` (the `2^{−c₂n}` version of `mst_interp_arithmetic`).  The only differences from `mst_major_err1_lp`: `C₂ 2^{−c₂n}` in place of `C₂ 2^{−n/2}` (hence `mst_interp_arithmetic_exp`), and no `hrep`/`hηml` hypotheses (`mstMajErr2Cls` takes only `hνml`/`hνsml`).

**Implementation warning (do not repeat the requester's dead end).** Writing `set Φ : Lp ℂ ⊤ (AddCircle.haarAddCircle (T := 1)) := mstMajErr2Cls P l P.natDegree χ η n (hνml n) (hνsml n)` and then rewriting with `opMulFinsuppLM_apply` makes Lean time out in `whnf` even at 8M heartbeats, because `mstMajErr2Cls` expands to a `Finset.sum` (`mstNuSumCls`) of `Lp` values with dependent `MemLp` proof arguments.  Work instead by *abstracting the class family*: prove a general interpolation result for an arbitrary `Φ : ℕ → Lp ℂ ⊤ haarT` (only the `eLpNorm`-`opMulFinsuppLM` endpoint bounds, no `mstNuS`/`mstMajErr2Cls` in sight) and instantiate it, or otherwise keep the class term opaque. -/
theorem mst_major_err2_lp (P : Polynomial ℤ) (hd : 2 ≤ P.natDegree) (hc : 0 < P.leadingCoeff)
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
    (hνml : ∀ n : ℕ, MeasureTheory.MemLp (mstNu P l P.natDegree χ η n) ⊤
      (AddCircle.haarAddCircle (T := 1)))
    (hνsml : ∀ n s : ℕ, MeasureTheory.MemLp (mstNuS P l P.natDegree χ η n s) ⊤
      (AddCircle.haarAddCircle (T := 1)))
    {p : ℝ} (hp : 1 < p) (hp2 : p < 2) :
    ∃ C c : ℝ, 0 < C ∧ 0 < c ∧ ∃ N₁ : ℕ, ∀ n : ℕ, N₁ ≤ n → ∀ g : ℤ →₀ ℂ,
      MeasureTheory.eLpNorm (Work.BourgainPlan.IonescuWainger.opMul
          (mstMajErr2Cls P l P.natDegree χ η n (hνml n) (hνsml n)) (⇑g)
          (Work.BourgainPlan.IonescuWainger.memℓp_finsupp g))
          (ENNReal.ofReal p) MeasureTheory.Measure.count
        ≤ ENNReal.ofReal (C * (2 : ℝ) ^ (-(c * (n : ℝ))))
          * MeasureTheory.eLpNorm (⇑g) (ENNReal.ofReal p) MeasureTheory.Measure.count := by
  obtain ⟨C₂, hC₂, c₂, hc₂, N₂, h2⟩ :=
    mst_major_err2_l2 P hd hc hχ0 hχ1 η M hM.le hηbd hη1 hη2 l hl hνml hνsml
  obtain ⟨C₁, hC₁, h1⟩ :=
    mst_major_err2_triv P hd hc hχ0 hχ1 η M hM.le hηbd hη1 hη2 l hl
      (show (1 : ℝ) < (1 + p) / 2 by linarith) A hA hcd hbdd hder hder2 hνml hνsml
  exact opMul_family_interp_exp
    (fun n => mstMajErr2Cls P l P.natDegree χ η n (hνml n) (hνsml n))
    hp hp2 hC₂ hc₂ h2 hC₁ hl h1

end

end Work.BourgainPlan.Maximal
