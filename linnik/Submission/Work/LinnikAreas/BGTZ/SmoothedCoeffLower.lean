/-
# `Work.LinnikAreas.BGTZ.SmoothedCoeffLower`

The **smoothed coefficient lower bound** consumed by the BGTZ zero detector: for a real
(quadratic) Dirichlet character `χ₁` mod `q` (`χ₁ ^ 2 = 1`, `χ₁ ≠ 1`) with an exceptional real
zero `β₁ ∈ (1 - 1/(10 log q), 1)` and Hypothesis A, one has

`S(R) = Σ_{n ≤ R} a(n) n^{-β₁} (1 - n/R)  ≥  ‖L(1,χ₁)‖ · R^{1-β₁}/((1-β₁)(2-β₁)) · (1 - C A e^{(log q)^{3/4}} q^θ / R^{1/2})`

for an absolute constant `C > 0` (BGTZ Lemma 4.1 in the smoothed form in which its proof produces
it; `a(n) = Σ_{d | n} χ₁(d) ≥ 0` is Graham's function).

## Route

* `SsmC_sub_res_eq_critIntegral` / `Ssm_ge_res_sub_J` (`BGTZ.CoeffSum.ShiftAux`) turn the
  critical-line shift of the triangle-kernel Perron integral into
  `Re L(1,χ₁) x^{1-β₁}/((1-β₁)(2-β₁)) - J ≤ Ssm χ₁ β₁ x`, `J` the critical-line integral.
* `critLineIntegralHypA_self` bounds `J ≤ CJ · A q^θ e^{(log q)^{3/4}} x^{1/2-β₁}` (Hypothesis A for
  the primitive character inducing `χ₁`; the Euler factors at `p | q` are absorbed by
  `exp((log q)^{3/4})`).
* `ratio_of_convex_bound` gives `Re L(1,χ₁) ≥ c (1 - β₁)`; with `im_LFunction_one_eq_zero`
  (`L(1,χ₁)` is real, hence positive here) this identifies `‖L(1,χ₁)‖` with `Re L(1,χ₁)`.
* The contour machinery requires a *non-integral* smoothing parameter; the natural `x = R` is
  recovered by applying it at `x = R + 1/k` and letting `k → ∞` (`Ssm_ge_res_sub_J_nat`), using the
  continuity of `x ↦ Ssm χ₁ β₁ x` from the right at `R`.

The constant is `C := max 1 (2 CJ / c + 1)`.
-/
import Mathlib
import Submission.Work.LinnikAreas.BGTZSetup
import Submission.Work.LinnikAreas.BGTZ.CoeffSum.CritLineSelf
import Submission.Work.LinnikAreas.BGTZ.CoeffSum.HorizSelf
import Submission.Work.LinnikAreas.BGTZ.CoeffSum.ShiftAux
import Submission.Work.LinnikAreas.perrErr_tendsto_zero
import Submission.Work.LinnikAreas.ratio_of_convex_bound
import Submission.Work.LinnikAreas.LFunction_eq_zero_of_zeroMult
import Submission.Work.LinnikAreas.lamRealNonneg

open DirichletCharacter Complex
open scoped Classical BigOperators
noncomputable section

namespace Work.LinnikAreas.BGTZ

set_option maxHeartbeats 1000000

/-- **The smoothed lower bound at an integral smoothing parameter.**

`Ssm_ge_res_sub_J` is available only for non-integral `x`; applying it at `x = R + 1/k` for every
`k ≥ 2` and letting `k → ∞` gives the same inequality at `x = R`, because `x ↦ Ssm ψ β x` is
continuous from the right at `R` (the summation range is constant on `[R, R+1)`) while the residue
and error terms are continuous in `x`.

`hmach` collects the analytic hypotheses of `Ssm_ge_res_sub_J` for every non-integral `x > R`,
with a *uniform* bound `K` for the critical-line integral. -/
private lemma Ssm_ge_res_sub_J_nat {N : ℕ} [NeZero N] (ψ : DirichletCharacter ℂ N)
    (hψ : ψ ≠ 1) (hψ2 : ψ ^ 2 = 1) {β K : ℝ} (hβ : 1 / 2 < β) (hβ1 : β < 1)
    (hReL : 0 ≤ (DirichletCharacter.LFunction ψ (1 : ℂ)).re) {R : ℕ} (hR : 200 ≤ R)
    (hL0 : DirichletCharacter.LFunction ψ (β : ℂ) = 0)
    (hmach : ∀ x : ℝ, (R : ℝ) < x → (∀ n : ℕ, (n : ℝ) ≠ x) →
      MeasureTheory.Integrable
          (fun y : ℝ => Work.LinnikAreas.triFun ψ β x (((1 / 2 - β : ℝ)) + (y : ℂ) * Complex.I)) ∧
      Filter.Tendsto (fun T : ℝ => Work.LinnikAreas.perrErr ψ β x T) Filter.atTop (nhds 0) ∧
      Filter.Tendsto (fun T : ℝ => (1 / (2 * Real.pi * Complex.I)) *
        ((∫ u in ((1 / 2 - β : ℝ))..1, Work.LinnikAreas.triFun ψ β x ((u : ℂ) + T * Complex.I))
         - (∫ u in ((1 / 2 - β : ℝ))..1, Work.LinnikAreas.triFun ψ β x ((u : ℂ) - T * Complex.I))))
        Filter.atTop (nhds 0) ∧
      ‖(1 / (2 * Real.pi)) *
          (∫ y : ℝ, Work.LinnikAreas.triFun ψ β x (((1 / 2 - β : ℝ)) + (y : ℂ) * Complex.I))‖ ≤ K) :
    (DirichletCharacter.LFunction ψ (1 : ℂ)).re * ((R : ℝ) ^ (1 - β) / ((1 - β) * (2 - β))) - K
      ≤ Work.LinnikAreas.Ssm ψ β (R : ℝ) := by
  have hR200 : (200 : ℝ) ≤ (R : ℝ) := by exact_mod_cast hR
  have hRpos : (0 : ℝ) < (R : ℝ) := by linarith
  -- the smoothed sum as a function of `t = x - R`
  set F : ℝ → ℝ := fun t : ℝ => ∑ n ∈ Finset.Icc 1 R,
    Work.LinnikAreas.lamR ψ n * (n : ℝ) ^ (-β) * (1 - (n : ℝ) / ((R : ℝ) + t)) with hFdef
  have hSsmR : Work.LinnikAreas.Ssm ψ β (R : ℝ) = F 0 := by
    rw [hFdef, Work.LinnikAreas.Ssm_apply, Nat.floor_natCast]
    simp
  -- continuity of `F` at `0`
  have hFlim : Filter.Tendsto F (nhds 0) (nhds (F 0)) := by
    rw [hFdef]
    apply tendsto_finsetSum
    intro n _
    have hden : ((R : ℝ) + 0) ≠ 0 := by positivity
    have h1 : Filter.Tendsto (fun t : ℝ => (R : ℝ) + t) (nhds 0) (nhds ((R : ℝ) + 0)) := by
      simpa using (tendsto_const_nhds.add Filter.tendsto_id :
        Filter.Tendsto (fun t : ℝ => (R : ℝ) + t) (nhds 0) (nhds ((R : ℝ) + 0)))
    have h2 : Filter.Tendsto (fun t : ℝ => 1 - (n : ℝ) / ((R : ℝ) + t)) (nhds 0)
        (nhds (1 - (n : ℝ) / ((R : ℝ) + 0))) :=
      tendsto_const_nhds.sub (tendsto_const_nhds.div h1 hden)
    exact (tendsto_const_nhds.mul tendsto_const_nhds).mul h2
  -- the sequence `x_k = R + 1/k` tends to `R`
  have h1k : Filter.Tendsto (fun k : ℕ => (1 : ℝ) / (k : ℝ)) Filter.atTop (nhds 0) :=
    tendsto_one_div_atTop_nhds_zero_nat
  have hcomp := hFlim.comp h1k
  have hlimF : Filter.Tendsto (fun k : ℕ => Work.LinnikAreas.Ssm ψ β ((R : ℝ) + 1 / (k : ℝ)))
      Filter.atTop (nhds (Work.LinnikAreas.Ssm ψ β (R : ℝ))) := by
    rw [hSsmR]
    refine hcomp.congr' ?_
    filter_upwards [Filter.eventually_ge_atTop (2 : ℕ)] with k hk
    have hkpos : (0 : ℝ) < (k : ℝ) := by positivity
    have hk2 : (1 : ℝ) / (k : ℝ) < 1 := by
      rw [div_lt_one hkpos]
      exact_mod_cast (by omega : 1 < k)
    have hfloor : ⌊(R : ℝ) + 1 / (k : ℝ)⌋₊ = R := by
      rw [Nat.floor_eq_iff (a := (R : ℝ) + 1 / (k : ℝ)) (n := R) (by positivity)]
      constructor
      · have : (0:ℝ) ≤ 1 / (k : ℝ) := by positivity
        push_cast
        linarith
      · push_cast
        linarith
    simp only [Function.comp_apply, hFdef, Work.LinnikAreas.Ssm_apply, hfloor]
  -- the inequality at each non-integral `x_k`
  have hseq : ∀ k : ℕ, 2 ≤ k →
      (DirichletCharacter.LFunction ψ (1 : ℂ)).re
          * (((R : ℝ) + 1 / (k : ℝ)) ^ (1 - β) / ((1 - β) * (2 - β))) - K
        ≤ Work.LinnikAreas.Ssm ψ β ((R : ℝ) + 1 / (k : ℝ)) := by
    intro k hk
    have hkpos : (0 : ℝ) < (k : ℝ) := by positivity
    have hk2 : (1 : ℝ) / (k : ℝ) < 1 := by
      rw [div_lt_one hkpos]
      exact_mod_cast (by omega : 1 < k)
    have hxR : (R : ℝ) < (R : ℝ) + 1 / (k : ℝ) := by
      have : (0 : ℝ) < 1 / (k : ℝ) := by positivity
      linarith
    have hxnn : ∀ n : ℕ, (n : ℝ) ≠ (R : ℝ) + 1 / (k : ℝ) := by
      intro n hn
      have hlt : (R : ℝ) < (n : ℝ) := by rw [hn]; exact hxR
      have hge : R + 1 ≤ n := by
        have : R < n := by exact_mod_cast hlt
        omega
      have h2 : ((R + 1 : ℕ) : ℝ) ≤ (n : ℝ) := by exact_mod_cast hge
      have h3 : (R : ℝ) + 1 / (k : ℝ) < (R : ℝ) + 1 := by linarith
      rw [hn] at h2
      push_cast at h2
      linarith
    obtain ⟨hint, hperr, hH, hJb⟩ := hmach _ hxR hxnn
    have hx1 : 1 < (R : ℝ) + 1 / (k : ℝ) := by linarith
    have hm := Work.LinnikAreas.BGTZ.CoeffSum.Ssm_ge_res_sub_J ψ hψ hψ2 hβ hβ1 hx1 hxnn hL0
      hint hperr hH (K := ‖(1 / (2 * Real.pi)) *
        (∫ y : ℝ, Work.LinnikAreas.triFun ψ β ((R : ℝ) + 1 / (k : ℝ))
          (((1 / 2 - β : ℝ)) + (y : ℂ) * Complex.I))‖) le_rfl
    have hstep : (DirichletCharacter.LFunction ψ (1 : ℂ)).re
          * (((R : ℝ) + 1 / (k : ℝ)) ^ (1 - β) / ((1 - β) * (2 - β))) - K
        ≤ (DirichletCharacter.LFunction ψ (1 : ℂ)).re
          * (((R : ℝ) + 1 / (k : ℝ)) ^ (1 - β) / ((1 - β) * (2 - β)))
        - ‖(1 / (2 * Real.pi)) *
          (∫ y : ℝ, Work.LinnikAreas.triFun ψ β ((R : ℝ) + 1 / (k : ℝ))
            (((1 / 2 - β : ℝ)) + (y : ℂ) * Complex.I))‖ := by
      linarith [hJb]
    exact le_trans hstep hm
  -- pass to the limit
  refine ge_of_tendsto hlimF ?_
  filter_upwards [Filter.eventually_ge_atTop (2 : ℕ)] with k hk
  refine le_trans ?_ (hseq k hk)
  have hstep : (DirichletCharacter.LFunction ψ (1 : ℂ)).re
      * ((R : ℝ) ^ (1 - β) / ((1 - β) * (2 - β)))
      ≤ (DirichletCharacter.LFunction ψ (1 : ℂ)).re
        * (((R : ℝ) + 1 / (k : ℝ)) ^ (1 - β) / ((1 - β) * (2 - β))) := by
    have hD : 0 < (1 - β) * (2 - β) := by nlinarith
    have hpow : (R : ℝ) ^ (1 - β) ≤ ((R : ℝ) + 1 / (k : ℝ)) ^ (1 - β) := by
      apply Real.rpow_le_rpow hRpos.le _ (by linarith)
      have : (0 : ℝ) < 1 / (k : ℝ) := by positivity
      linarith
    rw [div_eq_mul_inv, div_eq_mul_inv]
    exact mul_le_mul_of_nonneg_left
      (mul_le_mul_of_nonneg_right hpow (inv_nonneg.mpr hD.le)) hReL
  linarith [hstep]


/-- **`Work.LinnikAreas.BGTZ.SmoothedCoeffLower`** (BGTZ Lemma 4.1, smoothed form). -/
theorem SmoothedCoeffLower :
    ∃ C : ℝ, 0 < C ∧ ∀ (q : ℕ) [NeZero q], 400000 < q → ∀ (χ₁ : DirichletCharacter ℂ q),
      χ₁ ^ 2 = 1 → χ₁ ≠ 1 → ∀ {β₁ : ℝ}, β₁ < 1 → Work.LinnikContract.zeroMult χ₁ (β₁ : ℂ) ≠ 0 →
      1 - 1 / (10 * Real.log q) < β₁ →
      ∀ {A θ Cz : ℝ}, HypA A θ → HypZeta Cz → ∀ {R : ℕ}, 200 ≤ R →
      ‖DirichletCharacter.LFunction χ₁ (1 : ℂ)‖ * (R : ℝ) ^ (1 - β₁) / ((1 - β₁) * (2 - β₁))
        * (1 - C * A * Real.exp ((Real.log q) ^ (3 / 4 : ℝ)) * (q : ℝ) ^ θ
            / (R : ℝ) ^ (1 / 2 : ℝ))
        ≤ ∑ n ∈ Finset.Icc 1 R, aCoeff χ₁ n * (n : ℝ) ^ (-β₁) * (1 - (n : ℝ) / (R : ℝ)) := by
  obtain ⟨CJ, hCJpos, hJ⟩ := Work.LinnikAreas.BGTZ.CoeffSum.critLineIntegralHypA_self
  obtain ⟨C6, hC6pos, hC6⟩ := Work.LinnikAreas.BGTZ.CoeffSum.critLineIntegralConvex_self
  have hJconv : ∀ (q : ℕ) [NeZero q], 3 ≤ q → ∀ (χ : DirichletCharacter ℂ q), χ ≠ 1 →
      ∀ {β x : ℝ}, 3 / 4 ≤ β → β < 1 → 1 ≤ x →
      MeasureTheory.Integrable
          (fun y : ℝ => Work.LinnikAreas.triFun χ β x (((1 / 2 - β : ℝ)) + (y : ℂ) * Complex.I)) ∧
      ‖(1 / (2 * Real.pi)) *
          (∫ y : ℝ, Work.LinnikAreas.triFun χ β x (((1 / 2 - β : ℝ)) + (y : ℂ) * Complex.I))‖
        ≤ C6 * (q : ℝ) ^ ((1 : ℝ) / 3) * Real.log (2 * (q : ℝ) + 2) * x ^ (1 / 2 - β) :=
    fun q _ hq3 χ hχ => hC6 q χ hχ hq3
  have hperr : ∀ (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q), χ ^ 2 = 1 →
      ∀ {β x : ℝ}, 0 < β → 0 < x → (∀ n : ℕ, (n : ℝ) ≠ x) →
      Filter.Tendsto (fun T : ℝ => Work.LinnikAreas.perrErr χ β x T) Filter.atTop (nhds 0) :=
    fun q _ χ hχ2 => Work.LinnikAreas.perrErr_tendsto_zero (N := q) χ hχ2
  have hH : ∀ (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q), χ ≠ 1 →
      ∀ {β x : ℝ}, 1 / 2 < β → β < 1 → 0 < x →
      Filter.Tendsto (fun T : ℝ => (1 / (2 * Real.pi * Complex.I)) *
        ((∫ u in ((1 / 2 - β : ℝ))..1, Work.LinnikAreas.triFun χ β x ((u : ℂ) + T * Complex.I))
         - (∫ u in ((1 / 2 - β : ℝ))..1, Work.LinnikAreas.triFun χ β x ((u : ℂ) - T * Complex.I))))
        Filter.atTop (nhds 0) :=
    fun q _ χ hχ => Work.LinnikAreas.BGTZ.CoeffSum.horizSegTendstoZero (N := q) χ hχ
  obtain ⟨c, hcpos, hratio⟩ := Work.LinnikAreas.ratio_of_convex_bound C6 hC6pos hJconv hperr hH
  refine ⟨max 1 (2 * CJ / c + 1), lt_of_lt_of_le zero_lt_one (le_max_left _ _), ?_⟩
  intro q _inst hq χ₁ hχ₁2 hχ₁ne β₁ hβ₁ hzm hβ₁' A θ Cz hA hZeta R hR
  set E : ℝ := Real.exp ((Real.log q) ^ (3 / 4 : ℝ)) with hEdef
  have hEpos : 0 < E := by rw [hEdef]; exact Real.exp_pos _
  have hq3 : 3 ≤ q := by omega
  have hqpos : (0 : ℝ) < (q : ℝ) := by exact_mod_cast (by omega : 0 < q)
  have hApos : 0 < A := hA.1
  have hθpos : 0 < θ := hA.2.1
  -- `log q ≥ 2`
  have hlogq2 : 2 ≤ Real.log (q : ℝ) := by
    have h1 : Real.log 8 ≤ Real.log (q : ℝ) :=
      Real.log_le_log (by norm_num) (by exact_mod_cast (by omega : 8 ≤ q))
    have h2 : (2 : ℝ) ≤ Real.log 8 := by
      have h := Real.log_two_gt_d9
      rw [show (8 : ℝ) = 2 ^ 3 by norm_num, Real.log_pow]
      push_cast
      linarith
    linarith
  have hlogqpos : 0 < Real.log (q : ℝ) := by linarith
  have hβ34 : (3 : ℝ) / 4 ≤ β₁ := by
    have h2 : 1 / (10 * Real.log (q : ℝ)) ≤ 1 / 4 := by
      rw [div_le_div_iff₀ (by positivity) (by norm_num)]
      linarith
    linarith
  have hβhalf : (1 : ℝ) / 2 < β₁ := by linarith
  have hβpos : 0 < β₁ := by linarith
  have h1mβpos : 0 < 1 - β₁ := by linarith
  have h2mβpos : 0 < 2 - β₁ := by linarith
  have hDpos : 0 < (1 - β₁) * (2 - β₁) := by nlinarith
  have hR200 : (200 : ℝ) ≤ (R : ℝ) := by exact_mod_cast hR
  have hRpos : (0 : ℝ) < (R : ℝ) := by linarith
  -- the Hecke lower bound for `Re L(1,χ₁)`, and `L(1,χ₁) ∈ ℝ`
  have hratio' := hratio q hq χ₁ hχ₁2 hχ₁ne hβ₁ hzm hβ₁'
  have hLpos : 0 < (DirichletCharacter.LFunction χ₁ (1 : ℂ)).re :=
    lt_of_lt_of_le (mul_pos hcpos h1mβpos) hratio'
  have hnorm : ‖DirichletCharacter.LFunction χ₁ (1 : ℂ)‖
      = (DirichletCharacter.LFunction χ₁ (1 : ℂ)).re := by
    have him := Work.LinnikAreas.BGTZ.CoeffSum.im_LFunction_one_eq_zero χ₁ hχ₁ne hχ₁2
    have hz : DirichletCharacter.LFunction χ₁ (1 : ℂ)
        = (((DirichletCharacter.LFunction χ₁ (1 : ℂ)).re : ℝ) : ℂ) :=
      Complex.ext rfl (by simpa using him)
    rw [hz, Complex.norm_def, Complex.normSq_ofReal, Real.sqrt_mul_self hLpos.le]
    rfl
  -- the target sum is `Ssm χ₁ β₁ R`
  have hsum : (∑ n ∈ Finset.Icc 1 R, aCoeff χ₁ n * (n : ℝ) ^ (-β₁) * (1 - (n : ℝ) / (R : ℝ)))
      = Work.LinnikAreas.Ssm χ₁ β₁ (R : ℝ) := by
    rw [Work.LinnikAreas.Ssm_apply, Nat.floor_natCast]
    exact Finset.sum_congr rfl (fun n _ => by
      rw [Work.LinnikAreas.BGTZ.CoeffSum.aCoeff_eq_lamR])
  rw [hnorm, hsum]
  -- the contour machinery at every non-integral `x > R`, with the uniform bound `K`
  have hL0 : DirichletCharacter.LFunction χ₁ (β₁ : ℂ) = 0 :=
    Work.LinnikAreas.LFunction_eq_zero_of_zeroMult χ₁ hχ₁ne hβpos hβ₁ hzm
  have hmach : ∀ x : ℝ, (R : ℝ) < x → (∀ n : ℕ, (n : ℝ) ≠ x) →
      MeasureTheory.Integrable
          (fun y : ℝ => Work.LinnikAreas.triFun χ₁ β₁ x (((1 / 2 - β₁ : ℝ)) + (y : ℂ) * Complex.I)) ∧
      Filter.Tendsto (fun T : ℝ => Work.LinnikAreas.perrErr χ₁ β₁ x T) Filter.atTop (nhds 0) ∧
      Filter.Tendsto (fun T : ℝ => (1 / (2 * Real.pi * Complex.I)) *
        ((∫ u in ((1 / 2 - β₁ : ℝ))..1, Work.LinnikAreas.triFun χ₁ β₁ x ((u : ℂ) + T * Complex.I))
         - (∫ u in ((1 / 2 - β₁ : ℝ))..1, Work.LinnikAreas.triFun χ₁ β₁ x ((u : ℂ) - T * Complex.I))))
        Filter.atTop (nhds 0) ∧
      ‖(1 / (2 * Real.pi)) *
          (∫ y : ℝ, Work.LinnikAreas.triFun χ₁ β₁ x (((1 / 2 - β₁ : ℝ)) + (y : ℂ) * Complex.I))‖
        ≤ CJ * A * E * (q : ℝ) ^ θ * (R : ℝ) ^ (1 / 2 - β₁) := by
    intro x hxR hxnn
    have hx1 : 1 < x := by linarith
    have hxpos : 0 < x := by linarith
    obtain ⟨hint, hJb⟩ := hJ q χ₁ hχ₁ne hq3 hA hβ34 hβ₁ (le_of_lt hx1)
    refine ⟨hint, ?_, ?_, ?_⟩
    · exact Work.LinnikAreas.perrErr_tendsto_zero (N := q) χ₁ hχ₁2 hβpos hxpos hxnn
    · exact Work.LinnikAreas.BGTZ.CoeffSum.horizSegTendstoZero (N := q) χ₁ hχ₁ne hβhalf hβ₁ hxpos
    · have hpow : x ^ (1 / 2 - β₁) ≤ (R : ℝ) ^ (1 / 2 - β₁) :=
        Real.rpow_le_rpow_of_nonpos hRpos hxR.le (by linarith)
      have hnn : 0 ≤ CJ * A * (q : ℝ) ^ θ * E :=
        mul_nonneg (mul_nonneg (mul_nonneg hCJpos.le hApos.le)
          (Real.rpow_nonneg hqpos.le θ)) hEpos.le
      calc ‖(1 / (2 * Real.pi)) *
            (∫ y : ℝ, Work.LinnikAreas.triFun χ₁ β₁ x
              (((1 / 2 - β₁ : ℝ)) + (y : ℂ) * Complex.I))‖
          ≤ CJ * A * (q : ℝ) ^ θ * E * x ^ (1 / 2 - β₁) := hJb
        _ = (CJ * A * (q : ℝ) ^ θ * E) * x ^ (1 / 2 - β₁) := by ring
        _ ≤ (CJ * A * (q : ℝ) ^ θ * E) * (R : ℝ) ^ (1 / 2 - β₁) :=
            mul_le_mul_of_nonneg_left hpow hnn
        _ = CJ * A * E * (q : ℝ) ^ θ * (R : ℝ) ^ (1 / 2 - β₁) := by ring
  have hmain := Ssm_ge_res_sub_J_nat χ₁ hχ₁ne hχ₁2 hβhalf hβ₁ hLpos.le hR hL0 hmach
  -- the constant comparison
  have hkey : CJ * A * E * (q : ℝ) ^ θ * (R : ℝ) ^ (1 / 2 - β₁)
      ≤ (DirichletCharacter.LFunction χ₁ (1 : ℂ)).re * ((R : ℝ) ^ (1 - β₁) / ((1 - β₁) * (2 - β₁)))
        * (max 1 (2 * CJ / c + 1) * A * E * (q : ℝ) ^ θ / (R : ℝ) ^ ((1 : ℝ) / 2)) := by
    have hC₀nn : (0 : ℝ) ≤ max 1 (2 * CJ / c + 1) := le_trans zero_le_one (le_max_left _ _)
    have h3 : 2 * CJ ≤ c * max 1 (2 * CJ / c + 1) := by
      have h4 : 2 * CJ / c ≤ max 1 (2 * CJ / c + 1) := by
        linarith [le_max_right (1 : ℝ) (2 * CJ / c + 1)]
      calc 2 * CJ = c * (2 * CJ / c) := by field_simp
        _ ≤ c * max 1 (2 * CJ / c + 1) := mul_le_mul_of_nonneg_left h4 hcpos.le
    have hCD : CJ ≤ (DirichletCharacter.LFunction χ₁ (1 : ℂ)).re * max 1 (2 * CJ / c + 1)
        / ((1 - β₁) * (2 - β₁)) := by
      have h5 : c * max 1 (2 * CJ / c + 1) / (2 - β₁)
          ≤ (DirichletCharacter.LFunction χ₁ (1 : ℂ)).re * max 1 (2 * CJ / c + 1)
            / ((1 - β₁) * (2 - β₁)) := by
        rw [div_le_div_iff₀ h2mβpos hDpos]
        have h5' : c * (1 - β₁) * (max 1 (2 * CJ / c + 1) * (2 - β₁))
            ≤ (DirichletCharacter.LFunction χ₁ (1 : ℂ)).re
              * (max 1 (2 * CJ / c + 1) * (2 - β₁)) :=
          mul_le_mul_of_nonneg_right hratio' (mul_nonneg hC₀nn h2mβpos.le)
        linarith [h5']
      have h6 : CJ ≤ c * max 1 (2 * CJ / c + 1) / (2 - β₁) := by
        rw [le_div_iff₀ h2mβpos]
        nlinarith [h3, hCJpos]
      linarith
    have hAq : 0 ≤ A * E * (q : ℝ) ^ θ * (R : ℝ) ^ (1 / 2 - β₁) :=
      mul_nonneg (mul_nonneg (mul_nonneg hApos.le hEpos.le)
        (Real.rpow_nonneg hqpos.le θ)) (Real.rpow_nonneg hRpos.le _)
    have hRm : (R : ℝ) ^ (1 - β₁) = (R : ℝ) ^ (1 / 2 - β₁) * (R : ℝ) ^ ((1 : ℝ) / 2) := by
      have h := Real.rpow_add hRpos ((1 : ℝ) / 2 - β₁) ((1 : ℝ) / 2)
      rw [show (1 : ℝ) / 2 - β₁ + 1 / 2 = 1 - β₁ by ring] at h
      exact h
    calc CJ * A * E * (q : ℝ) ^ θ * (R : ℝ) ^ (1 / 2 - β₁)
        = CJ * (A * E * (q : ℝ) ^ θ * (R : ℝ) ^ (1 / 2 - β₁)) := by ring
      _ ≤ ((DirichletCharacter.LFunction χ₁ (1 : ℂ)).re * max 1 (2 * CJ / c + 1)
            / ((1 - β₁) * (2 - β₁))) * (A * E * (q : ℝ) ^ θ * (R : ℝ) ^ (1 / 2 - β₁)) :=
          mul_le_mul_of_nonneg_right hCD hAq
      _ = (DirichletCharacter.LFunction χ₁ (1 : ℂ)).re * ((R : ℝ) ^ (1 - β₁) / ((1 - β₁) * (2 - β₁)))
            * (max 1 (2 * CJ / c + 1) * A * E * (q : ℝ) ^ θ / (R : ℝ) ^ ((1 : ℝ) / 2)) := by
          rw [hRm]
          field_simp
  -- conclusion
  calc (DirichletCharacter.LFunction χ₁ (1 : ℂ)).re * (R : ℝ) ^ (1 - β₁) / ((1 - β₁) * (2 - β₁))
        * (1 - max 1 (2 * CJ / c + 1) * A * E * (q : ℝ) ^ θ / (R : ℝ) ^ ((1 : ℝ) / 2))
      = (DirichletCharacter.LFunction χ₁ (1 : ℂ)).re * ((R : ℝ) ^ (1 - β₁) / ((1 - β₁) * (2 - β₁)))
        - (DirichletCharacter.LFunction χ₁ (1 : ℂ)).re * ((R : ℝ) ^ (1 - β₁) / ((1 - β₁) * (2 - β₁)))
          * (max 1 (2 * CJ / c + 1) * A * E * (q : ℝ) ^ θ / (R : ℝ) ^ ((1 : ℝ) / 2)) := by ring
    _ ≤ (DirichletCharacter.LFunction χ₁ (1 : ℂ)).re * ((R : ℝ) ^ (1 - β₁) / ((1 - β₁) * (2 - β₁)))
        - CJ * A * E * (q : ℝ) ^ θ * (R : ℝ) ^ (1 / 2 - β₁) := by linarith [hkey]
    _ ≤ Work.LinnikAreas.Ssm χ₁ β₁ (R : ℝ) := hmain

end Work.LinnikAreas.BGTZ
