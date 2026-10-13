import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.RingTheory.Etale.Weakly
import Mathlib.RingTheory.Flat.TorsionFree
import Mathlib.RingTheory.TotallySplit
import Mathlib.Topology.Separation.CompletelyRegular
import Submission.Work.FTS.EllipticEst.StraightDefs
import Submission.Work.RemovLog.exists_lt_log_combination
import Submission.Work.RemovSign.exists_sign_mul_eq_abs_of_abs_lower_bound

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

open MeasureTheory intervalIntegral

namespace Work.FTS.EllipticEst.remov

/-- Local version of the fundamental-theorem-of-calculus tail bound for a function whose
`abs` is known to be integrable. -/
theorem abs_sub_le_tail_of_primitive_local {T b θ t : ℝ} (hTb : T < b)
    {Q q : ℝ → ℝ} (hQ : ∀ x ∈ Set.Ioo T b, HasDerivAt Q (q x) x)
    (hq : MeasureTheory.IntegrableOn (fun x => |q x|) (Set.Ioc T b))
    (hθ : θ ∈ Set.Ioo T b) (ht : t ∈ Set.Ioo θ b) :
    |Q t - Q θ| ≤ ∫ x in Set.Ioc θ b, |q x| := by
  have hθt : θ ≤ t := le_of_lt ht.1
  have hsub1 : Set.Ioc θ t ⊆ Set.Ioc T b := fun x hx =>
    ⟨lt_trans hθ.1 hx.1, le_of_lt (lt_of_le_of_lt hx.2 ht.2)⟩
  have hsub2 : Set.Ioc θ b ⊆ Set.Ioc T b := fun x hx => ⟨lt_trans hθ.1 hx.1, hx.2⟩
  have hint1 : MeasureTheory.IntegrableOn (fun x => |q x|) (Set.Ioc θ t) := hq.mono_set hsub1
  have hint2 : MeasureTheory.IntegrableOn (fun x => |q x|) (Set.Icc θ t) :=
    (integrableOn_Icc_iff_integrableOn_Ioc).mpr hint1
  have hmem : ∀ x ∈ Set.Icc θ t, x ∈ Set.Ioo T b := fun x hx =>
    ⟨lt_of_lt_of_le hθ.1 hx.1, lt_of_le_of_lt hx.2 ht.2⟩
  have hcont : ContinuousOn Q (Set.Icc θ t) := fun x hx =>
    (hQ x (hmem x hx)).continuousAt.continuousWithinAt
  have h1 : Q t - Q θ ≤ ∫ y in θ..t, |q y| :=
    intervalIntegral.sub_le_integral_of_hasDeriv_right_of_le hθt hcont
      (fun x hx => (hQ x (hmem x ⟨le_of_lt hx.1, le_of_lt hx.2⟩)).hasDerivWithinAt)
      hint2 (fun x hx => le_abs_self _)
  have h2 : Q θ - Q t ≤ ∫ y in θ..t, |q y| := by
    have hh := intervalIntegral.sub_le_integral_of_hasDeriv_right_of_le hθt hcont.neg
      (fun x hx => (hQ x (hmem x ⟨le_of_lt hx.1, le_of_lt hx.2⟩)).neg.hasDerivWithinAt)
      hint2 (fun x hx => neg_le_abs _)
    simp only [Pi.neg_apply] at hh
    linarith [hh]
  have h3 : |Q t - Q θ| ≤ ∫ y in θ..t, |q y| := abs_sub_le_iff.mpr ⟨h1, h2⟩
  have h4 : (∫ y in θ..t, |q y|) = ∫ y in Set.Ioc θ t, |q y| := integral_of_le hθt
  have h5 : (∫ y in Set.Ioc θ t, |q y|) ≤ ∫ y in Set.Ioc θ b, |q y| :=
    MeasureTheory.setIntegral_mono_set (hq.mono_set hsub2)
      (Filter.Eventually.of_forall (fun x => abs_nonneg _))
      (Filter.Eventually.of_forall (fun x hx => ⟨hx.1, le_of_lt (lt_of_le_of_lt hx.2 ht.2)⟩))
  linarith [h3, h4, h5]

lemma hasDerivAt_log_const_sub {b y : ℝ} (hy : y < b) :
    HasDerivAt (fun z : ℝ => Real.log (b - z)) (-(b - y)⁻¹) y := by
  have h1 : HasDerivAt (fun z : ℝ => b - z) (-1) y := (hasDerivAt_id y).const_sub b
  exact (h1.log (ne_of_gt (sub_pos.mpr hy))).congr_deriv (by simp only [one_div, neg_div])

lemma hasDerivAt_inv_const_sub {b y : ℝ} (hy : y < b) :
    HasDerivAt (fun z : ℝ => (b - z)⁻¹) ((b - y) ^ 2)⁻¹ y := by
  have h0 := ((hasDerivAt_id y).const_sub b).inv (ne_of_gt (sub_pos.mpr hy))
  exact h0.congr_deriv (by simp only [id_eq, one_div, neg_div, neg_neg])

/-- **A bounded function with a "good quotient" second derivative has vanishing quotient.**

Let `T < b`, `2 ≤ p`, `Q, q, F` with `Q' = q` on `(T,b)`, `F` twice differentiable on `(T,b)`
with `F'' = Q / cos^p` there, and `|F| ≤ K` on `[T,b)`. Suppose `cos t > 0` and `cos t ≤ b - t`
on `[T,b)`. Then for every `θ ∈ (T,b)`, `|Q θ| ≤ ∫_{t ∈ (θ,b]} |q t|`.

Proof (contrapositive): if `A := ∫_{θ₀}^b |q| < |Q θ₀|` then (FTC for `Q`) `Q` keeps its sign
`s` on `(θ₀,b)` with `|Q t| ≥ μ := |Q θ₀| - A > 0` there.  Hence `s F'' = |Q|/cos^p ≥
μ (b-t)^{-p}` is positive, so `s F'` is monotone increasing with
`s F'(t) - s F'(θ₀) = ∫_{θ₀}^t s F'' ≥ μ((b-t)^{1-p} - (b-θ₀)^{1-p})/(p-1) =: w t → ∞`, and for
`t` close enough to `b` one has `w t ≥ 2|F' θ₀|`, so on `(t₁,b)` the function `F'` has constant
sign and `|F'| ≥ w/2 ≥ (μ/2)(b-t)^{-1-p...}`; since `∫_{t₁}^b (b-u)^{-p} du = ∞` (as `p ≥ 2`),
`|F(t) - F(t₁)| = ∫_{t₁}^t |F'| → ∞`, contradicting `|F| ≤ K`.  (Integrability of `F'' = Q/cos^p`
on subintervals `[θ, c]`, `c < b`, follows from the bound `|Q| ≤ |Q θ₀| + A` there.) -/
theorem abs_le_tail_of_bounded_double_primitive
    {T b K p : ℝ} (hTb : T < b) (hp : 2 ≤ p)
    (hcos_pos : ∀ t ∈ Set.Ico T b, 0 < Real.cos t)
    (hcos_le : ∀ t ∈ Set.Ico T b, Real.cos t ≤ b - t)
    {Q q F : ℝ → ℝ}
    (hQ : ∀ t ∈ Set.Ioo T b, HasDerivAt Q (q t) t)
    (hq : MeasureTheory.IntegrableOn (fun t => |q t|) (Set.Ioc T b))
    (hF1 : ∀ t ∈ Set.Ioo T b, HasDerivAt F (deriv F t) t)
    (hF2 : ∀ t ∈ Set.Ioo T b, HasDerivAt (deriv F) (deriv (deriv F) t) t)
    (hF2eq : ∀ t ∈ Set.Ioo T b, deriv (deriv F) t = Q t / (Real.cos t) ^ p)
    (hFbd : ∀ t ∈ Set.Ico T b, |F t| ≤ K) :
    ∀ θ ∈ Set.Ioo T b, |Q θ| ≤ ∫ t in Set.Ioc θ b, |q t| := by
  intro θ hθ
  by_contra hcon
  have hAsmall : (∫ t in Set.Ioc θ b, |q t|) < |Q θ| := not_le.mp hcon
  have hTθ : T < θ := hθ.1
  have hθb : θ < b := hθ.2
  set A : ℝ := ∫ t in Set.Ioc θ b, |q t| with hA
  have hμ : 0 < |Q θ| - A := by rw [hA]; linarith
  -- (1) tail bound
  have htail : ∀ t ∈ Set.Ioo θ b, |Q θ| - A ≤ |Q t| := by
    intro t ht
    have h1 : |Q t - Q θ| ≤ A := by
      rw [hA]
      exact abs_sub_le_tail_of_primitive_local hTb hQ hq hθ ht
    have h2 : |Q θ| ≤ |Q θ - Q t| + |Q t| := by
      have h := abs_add_le (Q θ - Q t) (Q t)
      simpa using h
    have h3 : |Q θ - Q t| = |Q t - Q θ| := abs_sub_comm _ _
    linarith
  -- (2) sign
  obtain ⟨s, hs, hsQ⟩ := Work.RemovSign.exists_sign_mul_eq_abs_of_abs_lower_bound hTb
      (fun x hx => (hQ x hx).differentiableAt) hθ hμ htail
  -- (3) choose a
  set a : ℝ := (max θ (b - 1/2) + b) / 2 with ha
  have hθa : θ < a := by
    rw [ha]
    have h : θ ≤ max θ (b - 1/2) := le_max_left _ _
    linarith
  have hab : a < b := by
    rw [ha]
    have h : max θ (b - 1/2) < b := max_lt hθb (by linarith)
    linarith
  have hba : b - a ≤ 1/4 := by
    rw [ha]
    have h : b - 1/2 ≤ max θ (b - 1/2) := le_max_right _ _
    linarith
  -- (4) W and G
  set W : ℝ → ℝ := fun y => s * F y + (|Q θ| - A) * Real.log (b - y) with hW
  set G : ℝ → ℝ := fun y => s * deriv F y - (|Q θ| - A) * (b - y)⁻¹ with hG
  have hWd : ∀ y ∈ Set.Ioo T b, DifferentiableAt ℝ W y := by
    intro y hy
    have h1 : DifferentiableAt ℝ (fun z : ℝ => s * F z) y := ((hF1 y hy).differentiableAt).const_mul s
    have h2 : DifferentiableAt ℝ (fun z : ℝ => (|Q θ| - A) * Real.log (b - z)) y :=
      (hasDerivAt_log_const_sub hy.2).differentiableAt.const_mul (|Q θ| - A)
    rw [hW]
    exact h1.add h2
  have hWderiv : ∀ y ∈ Set.Ioo T b, deriv W y = G y := by
    intro y hy
    have h1 : HasDerivAt (fun z : ℝ => s * F z) (s * deriv F y) y := (hF1 y hy).const_mul s
    have h2 : HasDerivAt (fun z : ℝ => (|Q θ| - A) * Real.log (b - z))
        ((|Q θ| - A) * (-(b - y)⁻¹)) y := (hasDerivAt_log_const_sub hy.2).const_mul (|Q θ| - A)
    have h3 := (h1.add h2).deriv
    rw [hW, hG]
    rw [show (fun z : ℝ => s * F z + (|Q θ| - A) * Real.log (b - z))
        = ((fun z : ℝ => s * F z) + fun z : ℝ => (|Q θ| - A) * Real.log (b - z)) from rfl]
    rw [h3]
    ring
  have hGd : ∀ y ∈ Set.Ioo T b, DifferentiableAt ℝ G y := by
    intro y hy
    have h1 : DifferentiableAt ℝ (fun z : ℝ => s * deriv F z) y :=
      ((hF2 y hy).differentiableAt).const_mul s
    have h2 : DifferentiableAt ℝ (fun z : ℝ => (b - z)⁻¹) y :=
      (hasDerivAt_inv_const_sub hy.2).differentiableAt
    rw [hG]
    exact h1.sub (h2.const_mul (|Q θ| - A))
  have hGderiv : ∀ y ∈ Set.Ioo T b, deriv G y
      = s * deriv (deriv F) y - (|Q θ| - A) * ((b - y) ^ 2)⁻¹ := by
    intro y hy
    have h1 : HasDerivAt (fun z : ℝ => s * deriv F z) (s * deriv (deriv F) y) y :=
      (hF2 y hy).const_mul s
    have h3 : HasDerivAt (fun z : ℝ => (|Q θ| - A) * (b - z)⁻¹)
        ((|Q θ| - A) * ((b - y) ^ 2)⁻¹) y :=
      (hasDerivAt_inv_const_sub hy.2).const_mul (|Q θ| - A)
    have h4 := (h1.sub h3).deriv
    rw [hG]
    rw [show (fun z : ℝ => s * deriv F z - (|Q θ| - A) * (b - z)⁻¹)
        = ((fun z : ℝ => s * deriv F z) - fun z : ℝ => (|Q θ| - A) * (b - z)⁻¹) from rfl]
    rw [h4]
  -- (5) the key pointwise bound
  have hbound : ∀ y ∈ Set.Ioo a b, (|Q θ| - A) * ((b - y) ^ 2)⁻¹ ≤ s * deriv (deriv F) y := by
    intro y hy
    have hyθ : y ∈ Set.Ioo θ b := ⟨lt_trans hθa hy.1, hy.2⟩
    have hyT : y ∈ Set.Ioo T b := ⟨lt_trans hTθ hyθ.1, hyθ.2⟩
    have hyIco : y ∈ Set.Ico T b := ⟨le_of_lt hyT.1, hyT.2⟩
    have hby : 0 < b - y := by linarith [hyθ.2]
    have hkey : s * deriv (deriv F) y = |Q y| / (Real.cos y) ^ p := by
      rw [hF2eq y hyT, mul_div_assoc', hsQ y hyθ]
    have hcosy : 0 < Real.cos y := hcos_pos y hyIco
    have hcosle : Real.cos y ≤ b - y := hcos_le y hyIco
    have hcosp : (Real.cos y) ^ p ≤ (b - y) ^ p :=
      Real.rpow_le_rpow (le_of_lt hcosy) hcosle (by linarith)
    have hcosp2 : (Real.cos y) ^ p ≤ (b - y) ^ 2 := by
      have hbyle : b - y ≤ 1 := by linarith [hy.1, hy.2, hba]
      have h2r : (b - y) ^ p ≤ (b - y) ^ (2:ℝ) :=
        Real.rpow_le_rpow_of_exponent_ge hby hbyle hp
      rw [Real.rpow_two] at h2r
      exact le_trans hcosp h2r
    have hpos : 0 < (Real.cos y) ^ p := Real.rpow_pos_of_pos hcosy p
    have hmuQ : |Q θ| - A ≤ |Q y| := htail y hyθ
    have hxnonneg : 0 ≤ |Q θ| - A := le_of_lt hμ
    calc (|Q θ| - A) * ((b - y) ^ 2)⁻¹
        = (|Q θ| - A) / (b - y) ^ 2 := by rw [div_eq_mul_inv]
      _ ≤ (|Q θ| - A) / (Real.cos y) ^ p :=
            div_le_div_of_nonneg_left hxnonneg hpos hcosp2
      _ ≤ |Q y| / (Real.cos y) ^ p :=
            div_le_div_of_nonneg_right hmuQ (le_of_lt hpos)
      _ = s * deriv (deriv F) y := hkey.symm
  -- (6) monotonicity
  have hGdiff : DifferentiableOn ℝ G (Set.Ioo a b) := by
    intro y hy
    exact (hGd y ⟨lt_trans hTθ (lt_trans hθa hy.1), hy.2⟩).differentiableWithinAt
  have hmono : MonotoneOn G (Set.Ioo a b) := by
    refine monotoneOn_of_deriv_nonneg (convex_Ioo a b) hGdiff.continuousOn ?_ ?_
    · rw [interior_Ioo]; exact hGdiff
    · intro y hy
      rw [interior_Ioo] at hy
      rw [hGderiv y ⟨lt_trans hTθ (lt_trans hθa hy.1), hy.2⟩]
      linarith [hbound y hy]
  -- (7) auxiliary point a2 in (a,b)
  set a2 : ℝ := (a + b) / 2 with ha2
  have haa2 : a < a2 := by rw [ha2]; linarith
  have ha2b : a2 < b := by rw [ha2]; linarith
  obtain ⟨t, htIoo, htlt⟩ := Work.RemovLog.exists_lt_log_combination (a := a2) (b := b) (K := K)
      (μ := |Q θ| - A) (M := W a2 - |G a2| * (b - a2)) ha2b hμ
  have hmid : W a2 - |G a2| * (b - a2) ≤ W a2 + G a2 * (t - a2) := by
    have ht1 : t - a2 ≤ b - a2 := by linarith [htIoo.2]
    rcases lt_or_ge (G a2) 0 with hg | hg
    · have h1 : G a2 * (t - a2) ≥ G a2 * (b - a2) := by nlinarith [ht1, hg]
      have h2 : G a2 * (b - a2) = -|G a2| * (b - a2) := by rw [abs_of_neg hg]; ring
      linarith
    · have h1 : 0 ≤ G a2 * (t - a2) := mul_nonneg hg (by linarith [htIoo.1])
      have h2 : -|G a2| * (b - a2) ≤ 0 := by
        nlinarith [abs_nonneg (G a2), htIoo.1, htIoo.2]
      linarith
  -- (8) MVT on [a2, t]
  have hcontW : ContinuousOn W (Set.Icc a2 t) := by
    refine continuousOn_of_forall_continuousAt (fun x hx => ?_)
    exact (hWd x ⟨lt_of_lt_of_le (lt_trans hTθ (lt_trans hθa haa2)) hx.1,
      lt_of_le_of_lt hx.2 htIoo.2⟩).continuousAt
  have hdiffW : DifferentiableOn ℝ W (Set.Ioo a2 t) := by
    intro x hx
    exact (hWd x ⟨lt_of_lt_of_le (lt_trans hTθ (lt_trans hθa haa2)) (le_of_lt hx.1),
      lt_of_lt_of_le hx.2 (le_of_lt htIoo.2)⟩).differentiableWithinAt
  obtain ⟨c, hcIoo, hcder⟩ := exists_deriv_eq_slope' W htIoo.1 hcontW hdiffW
  have hcT : c ∈ Set.Ioo T b :=
    ⟨lt_trans hTθ (lt_trans hθa (lt_trans haa2 hcIoo.1)), lt_trans hcIoo.2 htIoo.2⟩
  have hcG : G c = (W t - W a2) / (t - a2) := by
    rw [← hWderiv c hcT, hcder, slope_def_field]
  have hGaGc : G a2 ≤ G c :=
    hmono ⟨haa2, ha2b⟩ ⟨lt_trans haa2 hcIoo.1, lt_trans hcIoo.2 htIoo.2⟩ (le_of_lt hcIoo.1)
  have htangent : W a2 + G a2 * (t - a2) ≤ W t := by
    have h1 : G a2 ≤ (W t - W a2) / (t - a2) := by rw [← hcG]; exact hGaGc
    have htpos : 0 < t - a2 := by linarith [htIoo.1]
    have h2 := (le_div_iff₀ htpos).mp h1
    linarith
  -- (9) W is bounded above
  have hWt : W t ≤ K + (|Q θ| - A) * Real.log (b - t) := by
    rw [hW]
    have hsF : s * F t ≤ |F t| := by
      rcases hs with h | h
      · rw [h]; simpa using le_abs_self (F t)
      · rw [h]; simpa using neg_le_abs (F t)
    have hbdt : |F t| ≤ K :=
      hFbd t ⟨le_of_lt (lt_trans hTθ (lt_trans hθa (lt_trans haa2 htIoo.1))), htIoo.2⟩
    linarith
  linarith


end Work.FTS.EllipticEst.remov
