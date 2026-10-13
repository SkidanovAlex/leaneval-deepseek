import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Submission.Work.FTS.StrongEps.EpsE4Thr.sq_integral_interval_le

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.StrongEps.EpsE4Thr.FstarJepsSmoothAux

open MeasureTheory

/-- **One-dimensional Gagliardo–Nirenberg / Agmon inequality.** If `g` is differentiable on
`[c,d]` with derivative `g'` continuous there, then for every `z ∈ [c,d]`,
`|g z| ≤ ‖g‖₂/√(d-c) + √(d-c)·‖g'‖₂`, where `‖·‖₂` denotes the `L²` norm on `[c,d]`.

The proof integrates the pointwise bound `|g z| ≤ |g y| + ∫_c^d |g'|` (valid for every
`y ∈ [c,d]`, obtained from the fundamental theorem of calculus together with
`|∫_y^z g'| ≤ ∫_c^d |g'|`) over `y ∈ [c,d]` and divides by `d - c`; the two `L²` norms are
then estimated by Cauchy–Schwarz (`sq_integral_interval_le`, the square form of
`(∫ f)² ≤ (b-a) ∫ f²`). -/
theorem abs_le_sqrt_interval_integral {c d : ℝ} (hcd : c < d) {g g' : ℝ → ℝ}
    (hder : ∀ x ∈ Set.Icc c d, HasDerivAt g (g' x) x)
    (hg'cont : ContinuousOn g' (Set.Icc c d)) :
    ∀ z ∈ Set.Icc c d,
      |g z| ≤ Real.sqrt (∫ x in c..d, (g x) ^ 2) / Real.sqrt (d - c)
        + Real.sqrt (d - c) * Real.sqrt (∫ x in c..d, (g' x) ^ 2) := by
  intro z hz
  have hcdle : c ≤ d := hcd.le
  have hdpos : 0 < d - c := sub_pos.mpr hcd
  have hdne : d - c ≠ 0 := ne_of_gt hdpos
  set T : ℝ := Real.sqrt (d - c) with hTdef
  set S : ℝ := Real.sqrt (∫ x in c..d, (g x) ^ 2) with hSdef
  set U : ℝ := Real.sqrt (∫ x in c..d, (g' x) ^ 2) with hUdef
  have hgcont : ContinuousOn g (Set.Icc c d) :=
    fun x hx => (hder x hx).continuousAt.continuousWithinAt
  have habsg_cont : ContinuousOn (fun x => |g x|) (Set.Icc c d) := hgcont.abs
  have habsg'_cont : ContinuousOn (fun x => |g' x|) (Set.Icc c d) := hg'cont.abs
  set A : ℝ := ∫ x in c..d, |g x| with hA
  set B : ℝ := ∫ x in c..d, |g' x| with hB
  have hAnn : 0 ≤ ∫ x in c..d, |g x| :=
    intervalIntegral.integral_nonneg hcdle (fun x _ => abs_nonneg _)
  have hBnn : 0 ≤ ∫ x in c..d, |g' x| :=
    intervalIntegral.integral_nonneg hcdle (fun x _ => abs_nonneg _)
  have hAnnA : 0 ≤ A := by rw [hA]; exact hAnn
  have hBnnB : 0 ≤ B := by rw [hB]; exact hBnn
  have hInt_absg : IntervalIntegrable (fun y => |g y|) volume c d :=
    ContinuousOn.intervalIntegrable_of_Icc hcdle habsg_cont
  have hInt_absg' : IntervalIntegrable (fun y => |g' y|) volume c d :=
    ContinuousOn.intervalIntegrable_of_Icc hcdle habsg'_cont
  -- the pointwise bound: `|g z| ≤ |g y| + B` for every `y ∈ [c,d]`
  have key : ∀ y ∈ Set.Icc c d, |g z| ≤ |g y| + B := by
    intro y hy
    have hsubIcc : Set.uIcc y z ⊆ Set.Icc c d := by
      intro t ht
      rw [Set.mem_uIcc] at ht
      rcases ht with ⟨h1, h2⟩ | ⟨h1, h2⟩
      · exact ⟨le_trans hy.1 h1, le_trans h2 hz.2⟩
      · exact ⟨le_trans hz.1 h1, le_trans h2 hy.2⟩
    have hsubIoc : Set.uIoc y z ⊆ Set.uIoc c d := by
      intro t ht
      rw [Set.mem_uIoc] at ht
      rw [Set.uIoc_of_le hcdle]
      rcases ht with ⟨h1, h2⟩ | ⟨h1, h2⟩
      · exact ⟨lt_of_le_of_lt hy.1 h1, le_trans h2 hz.2⟩
      · exact ⟨lt_of_le_of_lt hz.1 h1, le_trans h2 hy.2⟩
    have hFTC : ∫ t in y..z, g' t = g z - g y :=
      intervalIntegral.integral_eq_sub_of_hasDerivAt
        (fun t ht => hder t (hsubIcc ht))
        (ContinuousOn.intervalIntegrable (hg'cont.mono hsubIcc))
    have h1 : |∫ t in Set.uIoc y z, g' t| ≤ ∫ t in Set.uIoc y z, |g' t| := by
      simpa only [Real.norm_eq_abs] using
        MeasureTheory.norm_integral_le_integral_norm
          (μ := volume.restrict (Set.uIoc y z)) (f := g')
    have hfi : IntegrableOn (fun t => |g' t|) (Set.uIoc c d) volume := by
      rw [Set.uIoc_of_le hcdle]; exact hInt_absg'.1
    have h2 : ∫ t in Set.uIoc y z, |g' t| ≤ ∫ t in Set.uIoc c d, |g' t| :=
      MeasureTheory.setIntegral_mono_set hfi
        (Filter.Eventually.of_forall (fun t => abs_nonneg (g' t)))
        (Filter.Eventually.of_forall hsubIoc)
    have huIocB : ∫ t in Set.uIoc c d, |g' t| = B := by
      rw [hB, Set.uIoc_of_le hcdle, ← intervalIntegral.integral_of_le hcdle]
    have hEq : |∫ t in y..z, g' t| = |∫ t in Set.uIoc y z, g' t| :=
      intervalIntegral.abs_integral_eq_abs_integral_uIoc g'
    have hstep : |∫ t in y..z, g' t| ≤ B := by
      rw [hEq]
      exact h1.trans (h2.trans (le_of_eq huIocB))
    have hsum : g y + (g z - g y) = g z := by ring
    calc |g z| = |g y + (g z - g y)| := by rw [hsum]
      _ ≤ |g y| + |g z - g y| := abs_add_le _ _
      _ = |g y| + |∫ t in y..z, g' t| := by rw [← hFTC]
      _ ≤ |g y| + B := by linarith [hstep]
  -- integrate the pointwise bound over `y ∈ [c,d]`
  have hInt_const : IntervalIntegrable (fun _ : ℝ => |g z|) volume c d := intervalIntegrable_const
  have hInt_sum : IntervalIntegrable (fun y => |g y| + B) volume c d :=
    hInt_absg.add intervalIntegrable_const
  have hmono := intervalIntegral.integral_mono_on hcdle hInt_const hInt_sum key
  have e1 : ∫ y in c..d, |g z| = (d - c) * |g z| := by
    rw [intervalIntegral.integral_const]; simp [smul_eq_mul]
  have e2 : ∫ y in c..d, (|g y| + B) = A + (d - c) * B := by
    rw [intervalIntegral.integral_add hInt_absg intervalIntegrable_const, ← hA,
      intervalIntegral.integral_const]
    simp [smul_eq_mul]
  rw [e1, e2] at hmono
  have hmain : |g z| ≤ A / (d - c) + B := by
    have h1 : (d - c) * |g z| / (d - c) ≤ (A + (d - c) * B) / (d - c) :=
      div_le_div_of_nonneg_right hmono hdpos.le
    have h2 : (d - c) * |g z| / (d - c) = |g z| := by
      rw [div_eq_iff hdne]; ring
    have h3 : (A + (d - c) * B) / (d - c) = A / (d - c) + B := by
      have hmul : (d - c) * B / (d - c) = B := by rw [div_eq_iff hdne]; ring
      rw [add_div, hmul]
    linarith [h1, h2, h3]
  -- Cauchy–Schwarz for `A` and `B`
  have hAcs : A ≤ T * S := by
    have hi : IntervalIntegrable (fun x : ℝ => |g x| ^ 2) volume c d :=
      ContinuousOn.intervalIntegrable_of_Icc hcdle (habsg_cont.pow 2)
    have hsq : ∫ x in c..d, |g x| ^ 2 = ∫ x in c..d, (g x) ^ 2 :=
      intervalIntegral.integral_congr (fun x _ => sq_abs (g x))
    have hcs : (∫ x in c..d, |g x|) ^ 2 ≤ (d - c) * ∫ x in c..d, (g x) ^ 2 := by
      have h := sq_integral_interval_le (f := fun x => |g x|) hcdle hi
      rwa [hsq] at h
    calc A = Real.sqrt (A ^ 2) := (Real.sqrt_sq hAnnA).symm
      _ = Real.sqrt ((∫ x in c..d, |g x|) ^ 2) := by rw [hA]
      _ ≤ Real.sqrt ((d - c) * ∫ x in c..d, (g x) ^ 2) := Real.sqrt_le_sqrt hcs
      _ = T * S := by rw [hTdef, hSdef, Real.sqrt_mul hdpos.le]
  have hBcs : B ≤ T * U := by
    have hi : IntervalIntegrable (fun x : ℝ => |g' x| ^ 2) volume c d :=
      ContinuousOn.intervalIntegrable_of_Icc hcdle (habsg'_cont.pow 2)
    have hsq : ∫ x in c..d, |g' x| ^ 2 = ∫ x in c..d, (g' x) ^ 2 :=
      intervalIntegral.integral_congr (fun x _ => sq_abs (g' x))
    have hcs : (∫ x in c..d, |g' x|) ^ 2 ≤ (d - c) * ∫ x in c..d, (g' x) ^ 2 := by
      have h := sq_integral_interval_le (f := fun x => |g' x|) hcdle hi
      rwa [hsq] at h
    calc B = Real.sqrt (B ^ 2) := (Real.sqrt_sq hBnnB).symm
      _ = Real.sqrt ((∫ x in c..d, |g' x|) ^ 2) := by rw [hB]
      _ ≤ Real.sqrt ((d - c) * ∫ x in c..d, (g' x) ^ 2) := Real.sqrt_le_sqrt hcs
      _ = T * U := by rw [hTdef, hUdef, Real.sqrt_mul hdpos.le]
  have hT : 0 < T := by rw [hTdef]; exact Real.sqrt_pos.mpr hdpos
  have hT2 : T * T = d - c := by rw [hTdef, ← pow_two, Real.sq_sqrt hdpos.le]
  have hAratio : A / (d - c) ≤ S / T := by
    rw [div_le_div_iff₀ hdpos hT]
    calc A * T ≤ (T * S) * T := mul_le_mul_of_nonneg_right hAcs hT.le
      _ = S * (T * T) := by ring
      _ = S * (d - c) := by rw [hT2]
  linarith [hmain, hAratio, hBcs]

end Work.FTS.StrongEps.EpsE4Thr.FstarJepsSmoothAux
