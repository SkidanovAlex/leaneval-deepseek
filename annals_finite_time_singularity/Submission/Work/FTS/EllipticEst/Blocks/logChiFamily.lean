import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Analysis.SpecialFunctions.SmoothTransition
import Submission.Work.FTS.EllipticEst.TT.logCutDefs
import Submission.Work.FTS.EllipticEst.TT.logChi_contDiffOn

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.EllipticEst.Blocks

open scoped Real Topology
open Set Filter

/-! ## Helper lemmas for the family `logChi`

Everything below is proved with the explicit formula
`logChi n z = Work.ChiExplicit.chi (Real.log z / Real.log ((n:ℝ)+2))`, where
`Work.ChiExplicit.chi t = Real.smoothTransition (2 - |t|)`. -/

/-- The explicit cut-off `Work.ChiExplicit.chi` is continuous (it is `smoothTransition`
composed with `t ↦ 2 - |t|`). -/
theorem chi_continuous_explicit : Continuous Work.ChiExplicit.chi :=
  (Real.smoothTransition.continuous.comp (continuous_const.sub continuous_abs)).congr
    (fun x => (Work.ChiExplicit.chi_apply_abs x).symm)

/-- **The derivative of the explicit cut-off is globally bounded**: `deriv chi` is continuous
(`chi` is `C^∞`), it vanishes strictly outside `[-2,2]` (where `chi` is locally `0`), and on the
compact interval `[-2,2]` it attains a maximum of `|·|`. -/
theorem exists_bound_deriv_chi :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ t : ℝ, |deriv Work.ChiExplicit.chi t| ≤ K := by
  have hcd : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) Work.ChiExplicit.chi :=
    Work.ChiExplicit.chi_contDiff ⊤
  have hcont : Continuous (fun t : ℝ => |deriv Work.ChiExplicit.chi t|) :=
    (hcd.continuous_deriv (by simp)).abs
  -- `deriv chi` vanishes strictly outside `[-2,2]`, since `chi` is locally `0` there.
  have hzero_deriv : ∀ t : ℝ, 2 < |t| → deriv Work.ChiExplicit.chi t = 0 := by
    intro t ht
    have hopen : IsOpen {s : ℝ | (2 : ℝ) < |s|} := isOpen_lt continuous_const continuous_abs
    have hev : Work.ChiExplicit.chi =ᶠ[𝓝 t] (fun _ => (0 : ℝ)) := by
      filter_upwards [hopen.mem_nhds ht] with s hs
      exact Work.ChiExplicit.chi_eq_zero hs.le
    rw [hev.deriv_eq, deriv_const]
  -- A point of `[-2,2]` maximizing `|deriv chi|`.
  obtain ⟨x₀, -, hmax⟩ :=
    (isCompact_Icc (a := (-2 : ℝ)) (b := 2)).exists_isMaxOn
      (⟨(-2 : ℝ), by norm_num⟩ : (Set.Icc (-2 : ℝ) 2).Nonempty)
      (f := fun t : ℝ => |deriv Work.ChiExplicit.chi t|) hcont.continuousOn
  have hmax' : ∀ t ∈ Set.Icc (-2 : ℝ) 2,
      |deriv Work.ChiExplicit.chi t| ≤ |deriv Work.ChiExplicit.chi x₀| :=
    isMaxOn_iff.mp hmax
  refine ⟨|deriv Work.ChiExplicit.chi x₀|, abs_nonneg _, ?_⟩
  intro t
  by_cases ht : |t| ≤ 2
  · exact hmax' t (Set.mem_Icc.mpr (abs_le.mp ht))
  · rw [hzero_deriv t (lt_of_not_ge ht)]
    simp

/-- **The chain rule for the logarithmic cut-off**: for `z > 0`,
`(logChi n)'(z) = chi'(log z / log ((n:ℝ)+2)) · 1/(z · log ((n:ℝ)+2))`. -/
theorem deriv_logChi_eq (n : ℕ) {z : ℝ} (hz : 0 < z) :
    deriv (Work.FTS.EllipticEst.TT.logChi n) z =
      deriv Work.ChiExplicit.chi (Real.log z / Real.log ((n : ℝ) + 2)) *
        (1 / (z * Real.log ((n : ℝ) + 2))) := by
  have hc : 0 < Real.log ((n : ℝ) + 2) := Work.FTS.EllipticEst.TT.log_two_add_natCast_pos n
  have hgdiff : DifferentiableAt ℝ (fun w : ℝ => Real.log w / Real.log ((n : ℝ) + 2)) z :=
    (Real.differentiableAt_log (ne_of_gt hz)).div_const _
  have hchidiff : DifferentiableAt ℝ Work.ChiExplicit.chi
      (Real.log z / Real.log ((n : ℝ) + 2)) :=
    ((Work.ChiExplicit.chi_contDiff ⊤).differentiable (by simp)).differentiableAt
  have hderiv_g : deriv (fun w : ℝ => Real.log w / Real.log ((n : ℝ) + 2)) z =
      1 / (z * Real.log ((n : ℝ) + 2)) := by
    rw [deriv_div_const, Real.deriv_log]
    field_simp
  have hcomp : Work.FTS.EllipticEst.TT.logChi n =
      Work.ChiExplicit.chi ∘ (fun w : ℝ => Real.log w / Real.log ((n : ℝ) + 2)) := rfl
  rw [hcomp, deriv_comp z hchidiff hgdiff, hderiv_g]

/-- **The uniform-in-`n` commutator bound**: if `K` bounds `|chi'|` then `|z (logChi n)'(z)| ≤ K/log 2`
for every `n` and every `z > 0` (the factor `1/log ((n:ℝ)+2) ≤ 1/log 2` is what makes the bound
uniform). -/
theorem abs_mul_deriv_logChi_le {K : ℝ} (hK : 0 ≤ K)
    (hK' : ∀ t : ℝ, |deriv Work.ChiExplicit.chi t| ≤ K) (n : ℕ) {z : ℝ} (hz : 0 < z) :
    |z * deriv (Work.FTS.EllipticEst.TT.logChi n) z| ≤ K / Real.log 2 := by
  have hc : 0 < Real.log ((n : ℝ) + 2) := Work.FTS.EllipticEst.TT.log_two_add_natCast_pos n
  have h2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  set t := Real.log z / Real.log ((n : ℝ) + 2) with ht
  have heq : z * (deriv Work.ChiExplicit.chi t * (1 / (z * Real.log ((n : ℝ) + 2)))) =
      deriv Work.ChiExplicit.chi t / Real.log ((n : ℝ) + 2) := by
    field_simp
  rw [deriv_logChi_eq n hz, heq, abs_div, abs_of_pos hc]
  calc |deriv Work.ChiExplicit.chi t| / Real.log ((n : ℝ) + 2)
      ≤ K / Real.log ((n : ℝ) + 2) := div_le_div_of_nonneg_right (hK' t) hc.le
    _ ≤ K / Real.log 2 :=
        div_le_div_of_nonneg_left hK h2 (Work.FTS.EllipticEst.TT.log_two_le_log n)

/-- **Monotonicity in `n`**: `logChi n ≤ logChi (n+1)` pointwise on `(0,∞)`.  The denominator
`log ((n:ℝ)+2)` grows with `n`, so the argument `log z / log ((n:ℝ)+2)` shrinks in absolute value,
and `chi t = smoothTransition (2 - |t|)` increases as `|t|` shrinks. -/
theorem logChi_mono_succ (n : ℕ) (z : ℝ) :
    Work.FTS.EllipticEst.TT.logChi n z ≤ Work.FTS.EllipticEst.TT.logChi (n + 1) z := by
  have hc2 : 0 < Real.log ((n : ℝ) + 2) := Work.FTS.EllipticEst.TT.log_two_add_natCast_pos n
  have hc3 : 0 < Real.log (((n + 1 : ℕ) : ℝ) + 2) :=
    Work.FTS.EllipticEst.TT.log_two_add_natCast_pos (n + 1)
  have hle : Real.log ((n : ℝ) + 2) ≤ Real.log (((n + 1 : ℕ) : ℝ) + 2) := by
    apply Real.log_le_log (lt_trans one_pos (Work.FTS.EllipticEst.TT.one_lt_two_add_natCast n))
    push_cast
    linarith
  have ha : |Real.log z / Real.log (((n + 1 : ℕ) : ℝ) + 2)| ≤
      |Real.log z / Real.log ((n : ℝ) + 2)| := by
    rw [abs_div, abs_div, abs_of_pos hc2, abs_of_pos hc3]
    exact div_le_div_of_nonneg_left (abs_nonneg _) hc2 hle
  rw [Work.FTS.EllipticEst.TT.logChi_apply, Work.FTS.EllipticEst.TT.logChi_apply,
    Work.ChiExplicit.chi_apply_abs, Work.ChiExplicit.chi_apply_abs]
  exact Real.smoothTransition.monotone (sub_le_sub_left ha 2)

/-- **Pointwise convergence to `1`**: for `z > 0` the rescaled logarithm
`log z / log ((n:ℝ)+2)` tends to `0`, and `chi` is continuous at `0` with `chi 0 = 1`. -/
theorem logChi_tendsto_one (z : ℝ) (_hz : 0 < z) :
    Tendsto (fun n : ℕ => Work.FTS.EllipticEst.TT.logChi n z) atTop (nhds 1) := by
  have hden : Tendsto (fun n : ℕ => Real.log ((n : ℝ) + 2)) atTop atTop :=
    Real.tendsto_log_atTop.comp
      (Filter.tendsto_atTop_mono (fun n : ℕ => by
        have h : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg n
        linarith) tendsto_natCast_atTop_atTop)
  have h0 : Tendsto (fun n : ℕ => Real.log z / Real.log ((n : ℝ) + 2)) atTop (nhds 0) :=
    tendsto_const_nhds.div_atTop hden
  have h1 : Tendsto
      (fun n : ℕ => Work.ChiExplicit.chi (Real.log z / Real.log ((n : ℝ) + 2)))
      atTop (nhds 1) := by
    have h := chi_continuous_explicit.continuousAt.tendsto.comp h0
    rwa [Work.ChiExplicit.chi_zero] at h
  exact h1.congr (fun n => (Work.FTS.EllipticEst.TT.logChi_apply n z).symm)

/-- **The logarithmic cut-off family `logChi` has a uniform `|z χ'|`-bound, is monotone in `n`,
and converges pointwise to `1` on `(0,∞)`.**

`Work.FTS.EllipticEst.TT.logChi n z = Work.ChiExplicit.chi (Real.log z / Real.log ((n:ℝ)+2))`
with `chi t = Real.smoothTransition (2 - |t|)` the explicit smooth bump (`= 1` on `[-1,1]`,
`= 0` off `(-2,2)`, values in `[0,1]`).  Everything else about this family is already proved in
`Submission/Work/FTS/EllipticEst/TT/logCutDefs.lean` (`logChi_mem_Icc`, `logChi_eq_zero_of_le`,
`logChi_eq_zero_of_ge`); this statement adds the four remaining facts needed to run a monotone
convergence argument:

* `C^∞` on `(0,∞)` (composition of the globally `C^∞` `chi` with `z ↦ log z / log((n:ℝ)+2)`,
  which is `C^∞` on `(0,∞)` because `log ((n:ℝ)+2) > 0`);
* a **uniform-in-`n`** commutator bound `|z χ_n'(z)| ≤ K` (`= |χ'(log z/log((n:ℝ)+2))| /
  log((n:ℝ)+2) ≤ K₀/log 2` with `K₀` a bound for `|χ'|`);
* **monotonicity in `n`**: `χ_n ≤ χ_{n+1}` pointwise on `(0,∞)`
  (`log((n:ℝ)+3) ≥ log((n:ℝ)+2)`, so `|log z|/log((n:ℝ)+3) ≤ |log z|/log((n:ℝ)+2)`, and
  `chi` is antitone in `|·|` — `Work.ChiExplicit.chi_antitoneOn : AntitoneOn chi (Ici 0)`);
* **pointwise convergence** `χ_n z → 1` for `z > 0`
  (`log z/log((n:ℝ)+2) → 0`, `chi` continuous at `0` with `chi 0 = 1`). -/
theorem logChiFamily : ∃ K : ℝ, 0 ≤ K ∧
    (∀ n : ℕ,
      ContDiffOn ℝ Work.Stability.smoothOrder (Work.FTS.EllipticEst.TT.logChi n) (Set.Ioi (0 : ℝ))) ∧
    (∀ n : ℕ, ∀ z : ℝ, 0 < z → |z * deriv (Work.FTS.EllipticEst.TT.logChi n) z| ≤ K) ∧
    (∀ n : ℕ, ∀ z : ℝ, 0 < z →
      Work.FTS.EllipticEst.TT.logChi n z ≤ Work.FTS.EllipticEst.TT.logChi (n + 1) z) ∧
    (∀ z : ℝ, 0 < z →
      Filter.Tendsto (fun n : ℕ => Work.FTS.EllipticEst.TT.logChi n z) Filter.atTop (nhds 1)) := by
  obtain ⟨K₀, hK₀0, hK₀⟩ := exists_bound_deriv_chi
  refine ⟨K₀ / Real.log 2, div_nonneg hK₀0 (Real.log_pos (by norm_num)).le, ?_, ?_, ?_, ?_⟩
  · intro n
    exact Work.FTS.EllipticEst.TT.logChi_contDiffOn n
  · intro n z hz
    exact abs_mul_deriv_logChi_le hK₀0 hK₀ n hz
  · intro n z _
    exact logChi_mono_succ n z
  · intro z hz
    exact logChi_tendsto_one z hz

end Work.FTS.EllipticEst.Blocks
