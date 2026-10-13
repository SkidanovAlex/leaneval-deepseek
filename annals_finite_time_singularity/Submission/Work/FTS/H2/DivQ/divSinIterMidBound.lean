import Mathlib.Algebra.Order.Chebyshev
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
import Mathlib.Tactic.IntervalCases
import Mathlib.Topology.Algebra.Module.ModuleTopology
import Mathlib.Topology.GDelta.MetrizableSpace
import Submission.Work.Elliptic.DivSinDefs
import Submission.Work.FTS.EllipticEst.remov.SliceTopAux.Dth1IterMulEqOn
import Submission.Work.FTS.EllipticEst.remov.SliceTopAux.Dth1IterSubEqOn
import Submission.Work.FTS.EllipticEst.remov.SliceTopAux.Dth1IterBddOfPeriodicSmooth
import Submission.Work.FTS.EllipticEst.TT.Dth1Iter_eventuallyEq

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.H2.DivQ

open scoped Real Topology
open MeasureTheory Set Filter

noncomputable section

/-! ## Elementary facts about the angular operator

The whole estimate lives on the middle region `[π/8, 3π/8]`, where `sin(2θ) ∈ [1/√2, 1]`.
The only calculus input is the recursion for the iterates of `D_θ` applied to the quotient
`h / sin 2θ`, which holds on the open interval `(0, π/2)`. -/

/-- The `θ`-coefficient function `2 cos 2θ` of the quotient recursion. -/
private def cfun : ℝ → ℝ := fun θ => 2 * Real.cos (2 * θ)

private lemma cfun_analytic : ContDiff ℝ (⊤ : WithTop ℕ∞) cfun := by
  show ContDiff ℝ (⊤ : WithTop ℕ∞) (fun θ : ℝ => 2 * Real.cos (2 * θ))
  fun_prop

private lemma cfun_periodic : Function.Periodic cfun Real.pi := by
  intro x
  show 2 * Real.cos (2 * (x + Real.pi)) = 2 * Real.cos (2 * x)
  rw [show 2 * (x + Real.pi) = 2 * x + 2 * Real.pi by ring, Real.cos_periodic]

private lemma cfun_contDiffOn (n : ℕ) :
    ContDiffOn ℝ (n : WithTop ℕ∞) cfun (Set.Ioo 0 (Real.pi / 2)) := by
  show ContDiffOn ℝ (n : WithTop ℕ∞) (fun θ : ℝ => 2 * Real.cos (2 * θ)) _
  fun_prop

/-- `Dth1Iter (n+1) f = Dth1Iter n (Dth1 f)`. -/
private lemma Dth1Iter_succ_eq (n : ℕ) (f : ℝ → ℝ) :
    Work.Elliptic.Dth1Iter (n + 1) f = Work.Elliptic.Dth1Iter n (Work.Elliptic.Dth1 f) := by
  induction n with
  | zero => rfl
  | succ n ih =>
      show Work.Elliptic.Dth1 (Work.Elliptic.Dth1Iter (n + 1) f)
        = Work.Elliptic.Dth1 (Work.Elliptic.Dth1Iter n (Work.Elliptic.Dth1 f))
      rw [ih]

private lemma deriv_sin_two (θ : ℝ) :
    deriv (fun θ' : ℝ => Real.sin (2 * θ')) θ = 2 * Real.cos (2 * θ) := by
  have h1 : HasDerivAt (fun θ' : ℝ => (2 : ℝ) * θ') 2 θ := by
    simpa using (hasDerivAt_id θ).const_mul (2 : ℝ)
  have h2 : deriv (fun θ' : ℝ => Real.sin (2 * θ')) θ = Real.cos (2 * θ) * 2 := by
    have h3 := (Real.hasDerivAt_sin (2 * θ)).comp θ h1
    simpa [Function.comp_def] using h3.deriv
  rw [h2]; ring

/-- A function smooth on the open angular interval is `C^n` there for every finite `n`. -/
private lemma contDiffOn_finite {h : ℝ → ℝ} (n : ℕ)
    (hsm : ContDiffOn ℝ (((⊤ : ℕ∞) : WithTop ℕ∞)) h (Set.Ioo 0 (Real.pi / 2))) :
    ContDiffOn ℝ (n : WithTop ℕ∞) h (Set.Ioo 0 (Real.pi / 2)) :=
  hsm.of_le (WithTop.coe_le_coe.mpr le_top)

/-- The derivative of a function smooth on the open angular interval is `C^n` there. -/
private lemma contDiffOn_deriv {h : ℝ → ℝ} (n : ℕ)
    (hsm : ContDiffOn ℝ (((⊤ : ℕ∞) : WithTop ℕ∞)) h (Set.Ioo 0 (Real.pi / 2))) :
    ContDiffOn ℝ (n : WithTop ℕ∞) (deriv h) (Set.Ioo 0 (Real.pi / 2)) :=
  (contDiffOn_finite (n + 1) hsm).deriv_of_isOpen isOpen_Ioo (le_of_eq (by norm_cast))

/-- The angular quotient of a function smooth on the open angular interval is `C^n` there. -/
private lemma contDiffOn_SinQ {h : ℝ → ℝ} (n : ℕ)
    (hsm : ContDiffOn ℝ (((⊤ : ℕ∞) : WithTop ℕ∞)) h (Set.Ioo 0 (Real.pi / 2))) :
    ContDiffOn ℝ (n : WithTop ℕ∞) (Work.Elliptic.SinQ h) (Set.Ioo 0 (Real.pi / 2)) := by
  show ContDiffOn ℝ (n : WithTop ℕ∞) (fun θ => h θ / Real.sin (2 * θ)) _
  have hs : ContDiffOn ℝ (n : WithTop ℕ∞) (fun θ : ℝ => Real.sin (2 * θ))
      (Set.Ioo 0 (Real.pi / 2)) := by fun_prop
  refine (contDiffOn_finite n hsm).div hs ?_
  intro x hx
  exact ne_of_gt (Real.sin_pos_of_pos_of_lt_pi (by linarith [hx.1])
    (by linarith [hx.2, Real.pi_pos]))

/-- `D_θ (h / sin 2θ) = ∂_θ h - 2 cos 2θ · (h / sin 2θ)` on `(0, π/2)`. -/
private lemma Dth1_SinQ_eqOn {h : ℝ → ℝ}
    (hsm : ContDiffOn ℝ (((⊤ : ℕ∞) : WithTop ℕ∞)) h (Set.Ioo 0 (Real.pi / 2))) :
    Set.EqOn (Work.Elliptic.Dth1 (Work.Elliptic.SinQ h))
      (fun θ => deriv h θ - cfun θ * Work.Elliptic.SinQ h θ)
      (Set.Ioo 0 (Real.pi / 2)) := by
  intro θ hθ
  have hU : IsOpen (Set.Ioo (0 : ℝ) (Real.pi / 2)) := isOpen_Ioo
  have hsinU : ContDiffOn ℝ (((⊤ : ℕ∞) : WithTop ℕ∞)) (fun x : ℝ => Real.sin (2 * x))
      (Set.Ioo 0 (Real.pi / 2)) := by fun_prop
  have hne : ∀ x ∈ Set.Ioo (0 : ℝ) (Real.pi / 2), Real.sin (2 * x) ≠ 0 := fun x hx =>
    ne_of_gt (Real.sin_pos_of_pos_of_lt_pi (by linarith [hx.1])
      (by linarith [hx.2, Real.pi_pos]))
  have hgU : ContDiffOn ℝ (((⊤ : ℕ∞) : WithTop ℕ∞)) (Work.Elliptic.SinQ h)
      (Set.Ioo 0 (Real.pi / 2)) := by
    show ContDiffOn ℝ (((⊤ : ℕ∞) : WithTop ℕ∞))
      (fun x => h x / Real.sin (2 * x)) _
    exact hsm.div hsinU hne
  have hneθ : ∀ᶠ x in 𝓝 θ, Real.sin (2 * x) ≠ 0 := by
    have hc : ContinuousAt (fun x : ℝ => Real.sin (2 * x)) θ := by fun_prop
    exact hc.eventually_ne (hne θ hθ)
  have heq : (fun x : ℝ => Real.sin (2 * x) * Work.Elliptic.SinQ h x) =ᶠ[𝓝 θ] h := by
    filter_upwards [hneθ] with x hx
    simp only [Work.Elliptic.SinQ]
    rw [mul_comm, div_mul_cancel₀ _ hx]
  have hdeq : deriv (fun x : ℝ => Real.sin (2 * x) * Work.Elliptic.SinQ h x) θ
      = deriv h θ := heq.deriv_eq
  have dsin : DifferentiableAt ℝ (fun x : ℝ => Real.sin (2 * x)) θ := by fun_prop
  have dg : DifferentiableAt ℝ (Work.Elliptic.SinQ h) θ :=
    (hgU.contDiffAt (hU.mem_nhds hθ)).differentiableAt (by simp)
  have hprod : deriv (fun x : ℝ => Real.sin (2 * x) * Work.Elliptic.SinQ h x) θ
      = deriv (fun x : ℝ => Real.sin (2 * x)) θ * Work.Elliptic.SinQ h θ
        + Real.sin (2 * θ) * deriv (Work.Elliptic.SinQ h) θ :=
    deriv_mul dsin dg
  rw [deriv_sin_two θ] at hprod
  show Real.sin (2 * θ) * deriv (Work.Elliptic.SinQ h) θ
    = deriv h θ - cfun θ * Work.Elliptic.SinQ h θ
  rw [← hdeq, hprod]
  simp only [cfun]
  ring

/-- **The recursion for the iterates of the angular quotient.**  On the open interval
`(0, π/2)`,

  `D_θ^i (h/sin 2θ) = D_θ^{i-1}(∂_θh) - ∑_{k<i} C(i-1,k)·D_θ^k(2cos 2θ)·D_θ^{i-1-k}(h/sin2θ)`,

for `h` smooth on `(0, π/2)` and `i ≥ 1`.  This is the `C^∞`-on-the-open-interval
version of `Work.Elliptic.DivSinRec` (which asks for analyticity on a neighbourhood of the
closed interval); the proof only ever uses finite smoothness on `(0, π/2)`. -/
private theorem divSinRecOpen {h : ℝ → ℝ}
    (hsm : ContDiffOn ℝ (((⊤ : ℕ∞) : WithTop ℕ∞)) h (Set.Ioo 0 (Real.pi / 2)))
    (i : ℕ) (hi : 1 ≤ i) :
    ∀ θ ∈ Set.Ioo 0 (Real.pi / 2),
      Work.Elliptic.Dth1Iter i (Work.Elliptic.SinQ h) θ =
        Work.Elliptic.Dth1Iter (i - 1) (deriv h) θ -
          ∑ a ∈ Finset.range i, (Nat.choose (i - 1) a : ℝ) *
            (Work.Elliptic.Dth1Iter a cfun θ
              * Work.Elliptic.Dth1Iter (i - 1 - a) (Work.Elliptic.SinQ h) θ) := by
  obtain ⟨j, rfl⟩ : ∃ j, i = j + 1 := ⟨i - 1, by omega⟩
  intro θ hθ
  simp only [Nat.add_sub_cancel]
  have hU : IsOpen (Set.Ioo (0 : ℝ) (Real.pi / 2)) := isOpen_Ioo
  have hder : ContDiffOn ℝ (j : WithTop ℕ∞) (deriv h) (Set.Ioo 0 (Real.pi / 2)) :=
    contDiffOn_deriv j hsm
  have hSinQ : ContDiffOn ℝ (j : WithTop ℕ∞) (Work.Elliptic.SinQ h)
      (Set.Ioo 0 (Real.pi / 2)) := contDiffOn_SinQ j hsm
  have hc : ContDiffOn ℝ (j : WithTop ℕ∞) cfun (Set.Ioo 0 (Real.pi / 2)) :=
    cfun_contDiffOn j
  have hcV : ContDiffOn ℝ (j : WithTop ℕ∞)
      (fun x => cfun x * Work.Elliptic.SinQ h x) (Set.Ioo 0 (Real.pi / 2)) := hc.mul hSinQ
  have hev : Work.Elliptic.Dth1 (Work.Elliptic.SinQ h) =ᶠ[𝓝 θ]
      (fun x => deriv h x - cfun x * Work.Elliptic.SinQ h x) := by
    filter_upwards [hU.mem_nhds hθ] with x hx
    exact Dth1_SinQ_eqOn hsm hx
  calc Work.Elliptic.Dth1Iter (j + 1) (Work.Elliptic.SinQ h) θ
      = Work.Elliptic.Dth1Iter j (Work.Elliptic.Dth1 (Work.Elliptic.SinQ h)) θ := by
        rw [Dth1Iter_succ_eq]
    _ = Work.Elliptic.Dth1Iter j
          (fun x => deriv h x - cfun x * Work.Elliptic.SinQ h x) θ :=
        Work.FTS.EllipticEst.TT.Dth1Iter_eventuallyEq j hev
    _ = Work.Elliptic.Dth1Iter j (deriv h) θ
          - Work.Elliptic.Dth1Iter j (fun x => cfun x * Work.Elliptic.SinQ h x) θ :=
        (Work.FTS.EllipticEst.remov.SliceTopAux.Dth1IterSubEqOn j hder hcV) hθ
    _ = Work.Elliptic.Dth1Iter j (deriv h) θ
          - ∑ a ∈ Finset.range (j + 1), (Nat.choose j a : ℝ) *
              (Work.Elliptic.Dth1Iter a cfun θ
                * Work.Elliptic.Dth1Iter (j - a) (Work.Elliptic.SinQ h) θ) := by
        rw [Work.FTS.EllipticEst.remov.SliceTopAux.Dth1IterMulEqOn j hc hSinQ hθ]

/-! ## A universal bound for the coefficients `D_θ^k (2 cos 2θ)`, `k ≤ 3` -/

/-- There is a universal constant bounding `|D_θ^k (2 cos 2θ)|` for `k ≤ 3` on all of `ℝ`.
The function `2 cos 2θ` is `π`-periodic and smooth, so each iterate is too, and a continuous
periodic function is bounded. -/
private lemma coeffBound :
    ∃ cw : ℝ, 0 ≤ cw ∧ ∀ m : ℕ, m ≤ 3 → ∀ θ : ℝ,
      |Work.Elliptic.Dth1Iter m cfun θ| ≤ cw := by
  obtain ⟨c0, h0, hb0⟩ :=
    Work.FTS.EllipticEst.remov.SliceTopAux.Dth1IterBddOfPeriodicSmooth
      cfun_analytic cfun_periodic 0
  obtain ⟨c1, h1, hb1⟩ :=
    Work.FTS.EllipticEst.remov.SliceTopAux.Dth1IterBddOfPeriodicSmooth
      cfun_analytic cfun_periodic 1
  obtain ⟨c2, h2, hb2⟩ :=
    Work.FTS.EllipticEst.remov.SliceTopAux.Dth1IterBddOfPeriodicSmooth
      cfun_analytic cfun_periodic 2
  obtain ⟨c3, h3, hb3⟩ :=
    Work.FTS.EllipticEst.remov.SliceTopAux.Dth1IterBddOfPeriodicSmooth
      cfun_analytic cfun_periodic 3
  refine ⟨max (max c0 c1) (max c2 c3), ?_, ?_⟩
  · exact le_trans h0 (le_max_of_le_left (le_max_left c0 c1))
  · intro m hm θ
    interval_cases m
    · exact le_trans (hb0 θ) (le_trans (le_max_left c0 c1)
        (le_max_left (max c0 c1) (max c2 c3)))
    · exact le_trans (hb1 θ) (le_trans (le_max_right c0 c1)
        (le_max_left (max c0 c1) (max c2 c3)))
    · exact le_trans (hb2 θ) (le_trans (le_max_left c2 c3)
        (le_max_right (max c0 c1) (max c2 c3)))
    · exact le_trans (hb3 θ) (le_trans (le_max_right c2 c3)
        (le_max_right (max c0 c1) (max c2 c3)))

/-! ## The sequence of constants

`Kacc cw j` is the "table" of constants for the levels `≤ j`, and `Kf cw j = Kacc cw j j` is
the constant at level `j`.  The recursion `Kf cw (j+1) = 1 + cw ∑_{a≤j} C(j,a) Kf cw (j-a)`
is exactly what the strong induction produces. -/

private def Kacc (cw : ℝ) : ℕ → ℕ → ℝ
  | 0, _ => 1
  | (j + 1), l =>
      if l = j + 1 then 1 + cw * ∑ a ∈ Finset.range (j + 1),
        ((j.choose a : ℝ) * Kacc cw j (j - a))
      else Kacc cw j l

private def Kf (cw : ℝ) (j : ℕ) : ℝ := Kacc cw j j

private lemma Kacc_eq_Kf (cw : ℝ) : ∀ j l : ℕ, l ≤ j → Kacc cw j l = Kf cw l := by
  intro j
  induction j with
  | zero =>
      intro l hl
      interval_cases l
      rfl
  | succ j ih =>
      intro l hl
      rcases eq_or_lt_of_le hl with rfl | hlt
      · rfl
      · have hne : l ≠ j + 1 := by omega
        rw [show Kacc cw (j + 1) l = Kacc cw j l from by
          simp only [Kacc]
          rw [ite_eq_right hne]]
        exact ih l (by omega)

private lemma Kf_succ (cw : ℝ) (j : ℕ) :
    Kf cw (j + 1) = 1 + cw * ∑ a ∈ Finset.range (j + 1),
      (j.choose a : ℝ) * Kf cw (j - a) := by
  have hunf : Kf cw (j + 1) = 1 + cw * ∑ a ∈ Finset.range (j + 1),
      (j.choose a : ℝ) * Kacc cw j (j - a) := by
    show Kacc cw (j + 1) (j + 1) = _
    simp only [Kacc, ite_true]
  rw [hunf]
  have hs : (∑ a ∈ Finset.range (j + 1), (j.choose a : ℝ) * Kacc cw j (j - a))
      = ∑ a ∈ Finset.range (j + 1), (j.choose a : ℝ) * Kf cw (j - a) := by
    apply Finset.sum_congr rfl
    intro a _
    rw [Kacc_eq_Kf cw j (j - a) (Nat.sub_le j a)]
  rw [hs]

private lemma Kf_nonneg {cw : ℝ} (hcw : 0 ≤ cw) : ∀ l : ℕ, 0 ≤ Kf cw l := by
  intro l
  induction l using Nat.strong_induction_on with
  | h l ih =>
      rcases Nat.eq_zero_or_pos l with h0 | hpos
      · rw [h0]
        norm_num [Kf, Kacc]
      · obtain ⟨j, rfl⟩ : ∃ j, l = j + 1 := ⟨l - 1, by omega⟩
        rw [Kf_succ]
        have hs : 0 ≤ ∑ a ∈ Finset.range (j + 1), (j.choose a : ℝ) * Kf cw (j - a) :=
          Finset.sum_nonneg (fun a _ => mul_nonneg (Nat.cast_nonneg _) (ih (j - a) (by omega)))
        have := mul_nonneg hcw hs
        linarith

/-! ## The comparison quantity `|V| + ∑_{m<j} |U_m|` and its monotonicity -/

private def Abound (h : ℝ → ℝ) (θ : ℝ) (j : ℕ) : ℝ :=
  |Work.Elliptic.SinQ h θ| + ∑ m ∈ Finset.range j, |Work.Elliptic.Dth1Iter m (deriv h) θ|

private lemma Abound_nonneg (h : ℝ → ℝ) (θ : ℝ) (j : ℕ) : 0 ≤ Abound h θ j :=
  add_nonneg (abs_nonneg _) (Finset.sum_nonneg fun _ _ => abs_nonneg _)

private lemma Abound_mono {h : ℝ → ℝ} {θ : ℝ} {l j : ℕ} (hlj : l ≤ j) :
    Abound h θ l ≤ Abound h θ j := by
  show |Work.Elliptic.SinQ h θ| + ∑ i ∈ Finset.range l,
      |Work.Elliptic.Dth1Iter i (deriv h) θ| ≤
    |Work.Elliptic.SinQ h θ| + ∑ i ∈ Finset.range j,
      |Work.Elliptic.Dth1Iter i (deriv h) θ|
  exact add_le_add le_rfl
    (Finset.sum_le_sum_of_subset_of_nonneg (Finset.range_subset_range.mpr hlj)
      (fun i _ _ => abs_nonneg _))

private lemma Abound_term_le {h : ℝ → ℝ} {θ : ℝ} {m j : ℕ} (hm : m < j) :
    |Work.Elliptic.Dth1Iter m (deriv h) θ| ≤ Abound h θ j := by
  show |Work.Elliptic.Dth1Iter m (deriv h) θ| ≤
    |Work.Elliptic.SinQ h θ| + ∑ i ∈ Finset.range j, |Work.Elliptic.Dth1Iter i (deriv h) θ|
  refine le_trans (Finset.single_le_sum
    (f := fun i => |Work.Elliptic.Dth1Iter i (deriv h) θ|)
    (fun _ _ => abs_nonneg _) (Finset.mem_range.mpr hm)) ?_
  exact le_add_of_nonneg_left (abs_nonneg _)

private lemma abs_sub_le_abs_add_abs (A B : ℝ) : |A - B| ≤ |A| + |B| := by
  rw [abs_le]
  constructor <;> linarith [neg_abs_le A, neg_abs_le B, le_abs_self A, le_abs_self B]

/-- **The strong induction.**  For a slice `h` smooth on `(0, π/2)` and a constant `cw`
bounding `|D_θ^k (2 cos 2θ)|` for `k ≤ 3`, the iterate `D_θ^j (h/sin 2θ)` is bounded by
`Kf cw j · (|h/sin 2θ| + ∑_{m<j} |D_θ^m(∂_θh)|)` on `(0, π/2)`, for every `j ≤ 4`. -/
private lemma iterBound_aux {h : ℝ → ℝ}
    (hsm : ContDiffOn ℝ (((⊤ : ℕ∞) : WithTop ℕ∞)) h (Set.Ioo 0 (Real.pi / 2)))
    {cw : ℝ} (hcw0 : 0 ≤ cw)
    (hcwb : ∀ m : ℕ, m ≤ 3 → ∀ θ : ℝ, |Work.Elliptic.Dth1Iter m cfun θ| ≤ cw) :
    ∀ j : ℕ, j ≤ 4 → ∀ θ ∈ Set.Ioo 0 (Real.pi / 2),
      |Work.Elliptic.Dth1Iter j (Work.Elliptic.SinQ h) θ| ≤ Kf cw j * Abound h θ j := by
  intro j
  induction j using Nat.strong_induction_on with
  | h j ih =>
    intro hj4 θ hθ
    rcases Nat.eq_zero_or_pos j with h0 | hpos
    · rw [h0]
      simp only [Work.Elliptic.Dth1Iter_zero, Abound, Finset.range_zero, Finset.sum_empty,
        add_zero]
      rw [show Kf cw 0 = 1 from by simp only [Kf, Kacc], one_mul]
    · have hrec := divSinRecOpen hsm j hpos θ hθ
      have htri : |Work.Elliptic.Dth1Iter j (Work.Elliptic.SinQ h) θ| ≤
          |Work.Elliptic.Dth1Iter (j - 1) (deriv h) θ| +
            |∑ a ∈ Finset.range j, (Nat.choose (j - 1) a : ℝ) *
              (Work.Elliptic.Dth1Iter a cfun θ
                * Work.Elliptic.Dth1Iter (j - 1 - a) (Work.Elliptic.SinQ h) θ)| := by
        rw [hrec]
        exact abs_sub_le_abs_add_abs _ _
      have habs : |∑ a ∈ Finset.range j, (Nat.choose (j - 1) a : ℝ) *
            (Work.Elliptic.Dth1Iter a cfun θ
              * Work.Elliptic.Dth1Iter (j - 1 - a) (Work.Elliptic.SinQ h) θ)|
          ≤ ∑ a ∈ Finset.range j, (Nat.choose (j - 1) a : ℝ) * cw *
              (Kf cw (j - 1 - a) * Abound h θ j) := by
        refine le_trans (Finset.abs_sum_le_sum_abs _ _) ?_
        apply Finset.sum_le_sum
        intro a ha
        have haj : a < j := Finset.mem_range.mp ha
        have ha3 : a ≤ 3 := by omega
        have hca : |Work.Elliptic.Dth1Iter a cfun θ| ≤ cw := hcwb a ha3 θ
        have hIHa : |Work.Elliptic.Dth1Iter (j - 1 - a) (Work.Elliptic.SinQ h) θ|
            ≤ Kf cw (j - 1 - a) * Abound h θ (j - 1 - a) :=
          ih (j - 1 - a) (by omega) (by omega) θ hθ
        have hKf0 : 0 ≤ Kf cw (j - 1 - a) := Kf_nonneg hcw0 _
        have hAmono : Abound h θ (j - 1 - a) ≤ Abound h θ j := Abound_mono (by omega)
        calc |(Nat.choose (j - 1) a : ℝ) * (Work.Elliptic.Dth1Iter a cfun θ
                * Work.Elliptic.Dth1Iter (j - 1 - a) (Work.Elliptic.SinQ h) θ)|
            = (Nat.choose (j - 1) a : ℝ) * |Work.Elliptic.Dth1Iter a cfun θ| *
                |Work.Elliptic.Dth1Iter (j - 1 - a) (Work.Elliptic.SinQ h) θ| := by
              rw [abs_mul, abs_mul, abs_of_nonneg (Nat.cast_nonneg _)]
              ring
          _ ≤ (Nat.choose (j - 1) a : ℝ) * cw *
                |Work.Elliptic.Dth1Iter (j - 1 - a) (Work.Elliptic.SinQ h) θ| := by
              exact mul_le_mul_of_nonneg_right
                (mul_le_mul_of_nonneg_left hca (Nat.cast_nonneg _)) (abs_nonneg _)
          _ ≤ (Nat.choose (j - 1) a : ℝ) * cw *
                (Kf cw (j - 1 - a) * Abound h θ j) := by
              refine mul_le_mul_of_nonneg_left ?_ (mul_nonneg (Nat.cast_nonneg _) hcw0)
              exact le_trans hIHa (mul_le_mul_of_nonneg_left hAmono hKf0)
      have hsum_eq : ∑ a ∈ Finset.range j, (Nat.choose (j - 1) a : ℝ) * cw *
            (Kf cw (j - 1 - a) * Abound h θ j)
          = (cw * ∑ a ∈ Finset.range j, (Nat.choose (j - 1) a : ℝ) * Kf cw (j - 1 - a))
              * Abound h θ j := by
        rw [show (∑ a ∈ Finset.range j, (Nat.choose (j - 1) a : ℝ) * cw *
              (Kf cw (j - 1 - a) * Abound h θ j))
            = ∑ a ∈ Finset.range j, ((Nat.choose (j - 1) a : ℝ) * cw * Kf cw (j - 1 - a))
                * Abound h θ j
          from Finset.sum_congr rfl (fun a _ => by ring)]
        rw [← Finset.sum_mul]
        congr 1
        rw [Finset.mul_sum]
        exact Finset.sum_congr rfl (fun a _ => by ring)
      have hKfrec : Kf cw j = 1 + cw * ∑ a ∈ Finset.range j,
          (Nat.choose (j - 1) a : ℝ) * Kf cw (j - 1 - a) := by
        have h := Kf_succ cw (j - 1)
        rw [show j - 1 + 1 = j from by omega] at h
        exact h
      have hUle : |Work.Elliptic.Dth1Iter (j - 1) (deriv h) θ| ≤ Abound h θ j :=
        Abound_term_le (by omega)
      calc |Work.Elliptic.Dth1Iter j (Work.Elliptic.SinQ h) θ|
          ≤ |Work.Elliptic.Dth1Iter (j - 1) (deriv h) θ| +
            |∑ a ∈ Finset.range j, (Nat.choose (j - 1) a : ℝ) *
              (Work.Elliptic.Dth1Iter a cfun θ
                * Work.Elliptic.Dth1Iter (j - 1 - a) (Work.Elliptic.SinQ h) θ)| := htri
        _ ≤ Abound h θ j + ∑ a ∈ Finset.range j, (Nat.choose (j - 1) a : ℝ) * cw *
              (Kf cw (j - 1 - a) * Abound h θ j) := add_le_add hUle habs
        _ = (1 + cw * ∑ a ∈ Finset.range j,
              (Nat.choose (j - 1) a : ℝ) * Kf cw (j - 1 - a)) * Abound h θ j := by
              rw [hsum_eq]; ring
        _ = Kf cw j * Abound h θ j := by rw [hKfrec]

/-! ## The passage from the absolute-value bound to the squared bound -/

private lemma Abound_sq_le (h : ℝ → ℝ) (θ : ℝ) (i : ℕ) :
    (Abound h θ i) ^ 2 ≤ ((i : ℝ) + 1) *
      ((Work.Elliptic.SinQ h θ) ^ 2
        + ∑ m ∈ Finset.range i, (Work.Elliptic.Dth1Iter m (deriv h) θ) ^ 2) := by
  classical
  let G : ℕ → ℝ := fun m =>
    if m = 0 then |Work.Elliptic.SinQ h θ| else |Work.Elliptic.Dth1Iter (m - 1) (deriv h) θ|
  have hG0 : G 0 = |Work.Elliptic.SinQ h θ| := by simp only [G, ite_true]
  have hGs : ∀ m : ℕ, G (m + 1) = |Work.Elliptic.Dth1Iter m (deriv h) θ| := by
    intro m
    show (if m + 1 = 0 then |Work.Elliptic.SinQ h θ|
      else |Work.Elliptic.Dth1Iter (m + 1 - 1) (deriv h) θ|) = _
    rw [ite_eq_right (Nat.succ_ne_zero m), Nat.add_sub_cancel]
  have hsum : Abound h θ i = ∑ m ∈ Finset.range (i + 1), G m := by
    rw [Finset.sum_range_succ']
    simp only [hG0, hGs, Abound]
    ring
  have hsum2 : ∑ m ∈ Finset.range (i + 1), (G m) ^ 2
      = (Work.Elliptic.SinQ h θ) ^ 2
        + ∑ m ∈ Finset.range i, (Work.Elliptic.Dth1Iter m (deriv h) θ) ^ 2 := by
    rw [Finset.sum_range_succ']
    simp only [hG0, hGs, sq_abs]
    ring
  have hsq : (∑ m ∈ Finset.range (i + 1), G m) ^ 2
      ≤ ((i : ℝ) + 1) * ∑ m ∈ Finset.range (i + 1), (G m) ^ 2 := by
    have h := sq_sum_le_card_mul_sum_sq (s := Finset.range (i + 1)) (f := G)
    rw [Finset.card_range] at h
    push_cast at h
    exact h
  calc (Abound h θ i) ^ 2 = (∑ m ∈ Finset.range (i + 1), G m) ^ 2 := by rw [hsum]
    _ ≤ ((i : ℝ) + 1) * ∑ m ∈ Finset.range (i + 1), (G m) ^ 2 := hsq
    _ = ((i : ℝ) + 1) * ((Work.Elliptic.SinQ h θ) ^ 2
          + ∑ m ∈ Finset.range i, (Work.Elliptic.Dth1Iter m (deriv h) θ) ^ 2) := by
        rw [hsum2]

/-- **The pointwise iterate bound on the middle region.**  For every slice `h` smooth on
`(0, π/2)` there is a universal constant `K` with: for every `1 ≤ i ≤ 4` and every
`θ ∈ [π/8, 3π/8]`,

  `(D_θ^i (h / sin 2θ)(θ))² ≤ K · ( (h θ / sin 2θ)² + ∑_{m < i} (D_θ^m (∂_θ h)(θ))² )`,

where `D_θ = sin(2θ) ∂_θ` (`Work.Elliptic.Dth1Iter`).

Route.  On the open interval `(0, π/2)` one has `D_θ (h/sin 2θ) = ∂_θh − 2cos 2θ·(h/sin 2θ)`
(quotient rule), so writing `V = h/sin 2θ`, `U_m = D_θ^m(∂_θh)`, `c_k = D_θ^k(2cos 2θ)`, the
`D_θ`-Leibniz rule (`Dth1IterMulEqOn`) and additivity (`Dth1IterSubEqOn`) give, for `i ≥ 1`,

  `D_θ^i V = U_{i-1} − ∑_{k<i} C(i-1,k)·c_k·D_θ^{i-1-k}V`

on `(0, π/2)`.  With `|c_k| ≤ Cw` for `k ≤ 3` (`Dth1IterBddOfPeriodicSmooth` applied to the
`π`-periodic smooth `θ ↦ 2cos 2θ`), a strong induction gives
`|D_θ^j V| ≤ K_j (|V| + ∑_{m<j} |U_m|)` for `j ≤ 4` with universal constants `K_j`, and
`(A + B)² ≤ (j+1)(A² + B²)` for the finite sum converts this to the stated squared bound. -/
theorem divSinIterMidBound :
    ∃ K : ℝ, 0 < K ∧ ∀ (h : ℝ → ℝ),
      ContDiffOn ℝ (⊤ : ℕ∞) h (Set.Ioo 0 (Real.pi / 2)) →
      ∀ i : ℕ, i ∈ Finset.Icc 1 4 → ∀ θ : ℝ,
        θ ∈ Set.Icc (Real.pi / 8) (3 * Real.pi / 8) →
        (Work.Elliptic.Dth1Iter i (fun η => h η / Real.sin (2 * η)) θ) ^ 2
          ≤ K * ((h θ / Real.sin (2 * θ)) ^ 2
              + ∑ m ∈ Finset.range i, (Work.Elliptic.Dth1Iter m (deriv h) θ) ^ 2) := by
  obtain ⟨cw, hcw0, hcwb⟩ := coeffBound
  refine ⟨(∑ j ∈ Finset.range 5, (Kf cw j) ^ 2 * ((j : ℝ) + 1)) + 1, ?_, ?_⟩
  · have : 0 ≤ ∑ j ∈ Finset.range 5, (Kf cw j) ^ 2 * ((j : ℝ) + 1) :=
      Finset.sum_nonneg (fun j _ => mul_nonneg (sq_nonneg _) (by positivity))
    linarith
  · intro h hsm i hi θ hθ
    have hi1 : 1 ≤ i := (Finset.mem_Icc.mp hi).1
    have hi4 : i ≤ 4 := (Finset.mem_Icc.mp hi).2
    have hθIoo : θ ∈ Set.Ioo 0 (Real.pi / 2) := by
      have hp := Real.pi_pos
      constructor <;> linarith [hθ.1, hθ.2]
    have hbnd := iterBound_aux hsm hcw0 hcwb i hi4 θ hθIoo
    have hKi0 : 0 ≤ Kf cw i := Kf_nonneg hcw0 i
    have hAb0 : 0 ≤ Abound h θ i := Abound_nonneg h θ i
    have hS0 : 0 ≤ (Work.Elliptic.SinQ h θ) ^ 2
        + ∑ m ∈ Finset.range i, (Work.Elliptic.Dth1Iter m (deriv h) θ) ^ 2 :=
      add_nonneg (sq_nonneg _) (Finset.sum_nonneg fun _ _ => sq_nonneg _)
    have hA := Abound_sq_le h θ i
    have hstep1 : (Work.Elliptic.Dth1Iter i (Work.Elliptic.SinQ h) θ) ^ 2
        ≤ (Kf cw i * Abound h θ i) ^ 2 := by
      have h1 : |Work.Elliptic.Dth1Iter i (Work.Elliptic.SinQ h) θ| ≤ Kf cw i * Abound h θ i :=
        hbnd
      have h3 : |Work.Elliptic.Dth1Iter i (Work.Elliptic.SinQ h) θ| ^ 2
          ≤ (Kf cw i * Abound h θ i) ^ 2 :=
        pow_le_pow_left₀ (abs_nonneg _) h1 2
      rwa [sq_abs] at h3
    have hstep2 : (Kf cw i * Abound h θ i) ^ 2
        ≤ (Kf cw i) ^ 2 * (((i : ℝ) + 1) * ((Work.Elliptic.SinQ h θ) ^ 2
            + ∑ m ∈ Finset.range i, (Work.Elliptic.Dth1Iter m (deriv h) θ) ^ 2)) := by
      rw [mul_pow]
      exact mul_le_mul_of_nonneg_left hA (sq_nonneg _)
    have hterm : (Kf cw i) ^ 2 * ((i : ℝ) + 1)
        ≤ ∑ j ∈ Finset.range 5, (Kf cw j) ^ 2 * ((j : ℝ) + 1) :=
      Finset.single_le_sum (f := fun j => (Kf cw j) ^ 2 * ((j : ℝ) + 1))
        (fun j _ => mul_nonneg (sq_nonneg _) (by positivity))
        (Finset.mem_range.mpr (by omega))
    have hstep3 : (Kf cw i) ^ 2 * (((i : ℝ) + 1) * ((Work.Elliptic.SinQ h θ) ^ 2
          + ∑ m ∈ Finset.range i, (Work.Elliptic.Dth1Iter m (deriv h) θ) ^ 2))
        ≤ ((∑ j ∈ Finset.range 5, (Kf cw j) ^ 2 * ((j : ℝ) + 1)) + 1)
            * ((Work.Elliptic.SinQ h θ) ^ 2
              + ∑ m ∈ Finset.range i, (Work.Elliptic.Dth1Iter m (deriv h) θ) ^ 2) := by
      have hle : (Kf cw i) ^ 2 * ((i : ℝ) + 1)
          ≤ (∑ j ∈ Finset.range 5, (Kf cw j) ^ 2 * ((j : ℝ) + 1)) + 1 := by
        have h1 : 0 ≤ ∑ j ∈ Finset.range 5, (Kf cw j) ^ 2 * ((j : ℝ) + 1) :=
          Finset.sum_nonneg (fun j _ => mul_nonneg (sq_nonneg _) (by positivity))
        linarith [hterm]
      have := mul_le_mul_of_nonneg_right hle hS0
      calc (Kf cw i) ^ 2 * (((i : ℝ) + 1) * ((Work.Elliptic.SinQ h θ) ^ 2
              + ∑ m ∈ Finset.range i, (Work.Elliptic.Dth1Iter m (deriv h) θ) ^ 2))
          = ((Kf cw i) ^ 2 * ((i : ℝ) + 1)) * ((Work.Elliptic.SinQ h θ) ^ 2
              + ∑ m ∈ Finset.range i, (Work.Elliptic.Dth1Iter m (deriv h) θ) ^ 2) := by ring
        _ ≤ _ := this
    exact le_trans hstep1 (le_trans hstep2 hstep3)

end

end Work.FTS.H2.DivQ
