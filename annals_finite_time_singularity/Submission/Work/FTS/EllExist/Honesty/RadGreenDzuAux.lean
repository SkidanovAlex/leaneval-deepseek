/-
# `Work.FTS.EllExist.Honesty.RadGreenDzuAux` — the pointwise `D_z`-expansion of `radGreen`

`radGreen α m c = K (Φ + Ψ)` on `(0,∞)` (`Work.FTS.PhiStar.RadialWAux.radGreen_eq_rescaled`), where
`Φ = radPhi`, `Ψ = radPsi` satisfy the first-order relations

  `z Φ' = -(radQ α m) Φ + c`,     `z Ψ' = (radP α m) Ψ - c`.

The recursion `Work.FTS.EllExist.Honesty.dzu_recursion` therefore gives, for every `i`,

  `D_z^i radGreen = K [ (-(radQ))^i Φ + (radP)^i Ψ
                        + ∑_{t<i} (((-(radQ))^(i-1-t) - (radP)^(i-1-t)) D_z^t c ]`

on `(0,∞)`, which is `dzu_radGreen_val` below (`rgsBracket` is the bracket).  This file also
contains the linearity lemmas for `Dzu` used in the induction, and the differentiability of the
iterates `Dzu j radPhi`, `Dzu j radPsi` (from the two first-order relations and
`dzu_differentiableAt`).
-/
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Mathlib.Topology.Algebra.Module.ModuleTopology
import Submission.Work.FTS.EllExist.Honesty.RadGreenDzuDefs
import Submission.Work.FTS.EllExist.Honesty.dzu_differentiableAt
import Submission.Work.FTS.PhiStar.RadialWAux.Defs
import Submission.Work.FTS.PhiStar.RadialWAux.radGreen_eq_rescaled
import Submission.Work.FTS.EllExist.Honesty.dzu_recursion

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section
open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.EllExist.Honesty

set_option autoImplicit false

/-! ## Linearity of `Dzu` -/

theorem Dzu_congr {f g : ℝ → ℝ} (h : ∀ z ∈ Set.Ioi 0, f z = g z) :
    ∀ (i : ℕ) (z : ℝ), z ∈ Set.Ioi 0 → Dzu i f z = Dzu i g z := by
  intro i
  induction i using Nat.strong_induction_on with
  | _ n ih =>
    intro z hz
    match n with
    | 0 => exact h z hz
    | (m + 1) =>
      have heq : Dzu m f =ᶠ[𝓝 z] Dzu m g := by
        filter_upwards [isOpen_Ioi.mem_nhds hz] with w hw
        exact ih m (by omega) w hw
      simp only [Dzu_succ]
      rw [heq.deriv_eq]

theorem Dzu_add {A B : ℝ → ℝ} {i : ℕ}
    (hA : ∀ j < i, ∀ z : ℝ, 0 < z → DifferentiableAt ℝ (Dzu j A) z)
    (hB : ∀ j < i, ∀ z : ℝ, 0 < z → DifferentiableAt ℝ (Dzu j B) z) :
    ∀ z : ℝ, 0 < z → Dzu i (fun z => A z + B z) z = Dzu i A z + Dzu i B z := by
  revert hA hB
  induction i using Nat.strong_induction_on with
  | _ n ih =>
    intro hA hB z hz
    match n with
    | 0 => rfl
    | (m + 1) =>
      have heq : Dzu m (fun z => A z + B z) =ᶠ[𝓝 z]
          fun w => Dzu m A w + Dzu m B w := by
        filter_upwards [isOpen_Ioi.mem_nhds hz] with w hw
        exact ih m (by omega) (fun j hj => hA j (by omega)) (fun j hj => hB j (by omega)) w hw
      have hda : deriv (fun w => Dzu m A w + Dzu m B w) z
          = deriv (Dzu m A) z + deriv (Dzu m B) z :=
        deriv_add (hA m (by omega) z hz) (hB m (by omega) z hz)
      simp only [Dzu_succ]
      rw [heq.deriv_eq, hda]
      ring

theorem Dzu_const_mul (a : ℝ) {g : ℝ → ℝ} {i : ℕ}
    (hg : ∀ j < i, ∀ z : ℝ, 0 < z → DifferentiableAt ℝ (Dzu j g) z) :
    ∀ z : ℝ, 0 < z → Dzu i (fun z => a * g z) z = a * Dzu i g z := by
  revert hg
  induction i using Nat.strong_induction_on with
  | _ n ih =>
    intro hg z hz
    match n with
    | 0 => rfl
    | (m + 1) =>
      have heq : Dzu m (fun z => a * g z) =ᶠ[𝓝 z] fun w => a * Dzu m g w := by
        filter_upwards [isOpen_Ioi.mem_nhds hz] with w hw
        exact ih m (by omega) (fun j hj => hg j (by omega)) w hw
      have hdc : deriv (fun w => a * Dzu m g w) z = a * deriv (Dzu m g) z :=
        deriv_const_mul a (hg m (by omega) z hz)
      simp only [Dzu_succ]
      rw [heq.deriv_eq, hdc]
      ring

theorem Dzu_neg {g : ℝ → ℝ} {i : ℕ}
    (hg : ∀ j < i, ∀ z : ℝ, 0 < z → DifferentiableAt ℝ (Dzu j g) z) :
    ∀ z : ℝ, 0 < z → Dzu i (fun z => -g z) z = -Dzu i g z := by
  intro z hz
  have h := Dzu_const_mul (-1) hg z hz
  simpa using h

/-! ## Differentiability of the iterates of `radPhi` and `radPsi` -/

theorem dzu_radPhi_diff {α : ℝ} (hα : 0 < α) (hα4 : α ≤ 1 / 4) (m : ℕ) (hm : 1 ≤ m)
    {c : ℝ → ℝ} {k : ℕ} (hc : ContDiffOn ℝ (k + 1) c (Set.Ioi 0))
    (hΦ : ∀ z : ℝ, 0 < z →
      HasDerivAt (Work.FTS.PhiStar.RadialWAux.radPhi α m c)
        ((-(Work.FTS.PhiStar.RadialWAux.radQ α m)
            * Work.FTS.PhiStar.RadialWAux.radPhi α m c z + c z) / z) z) :
    ∀ j ≤ k, ∀ z : ℝ, 0 < z →
      DifferentiableAt ℝ (Dzu j (Work.FTS.PhiStar.RadialWAux.radPhi α m c)) z := by
  have hA : ∀ t ≤ k, ∀ z : ℝ, 0 < z → DifferentiableAt ℝ (Dzu t c) z :=
    fun t ht z hz => dzu_differentiableAt c k hc t ht z hz
  intro j
  induction j using Nat.strong_induction_on with
  | _ n ih =>
    intro hn z hz
    match n with
    | 0 => exact (hΦ z hz).differentiableAt
    | (m' + 1) =>
      have hrec := dzu_recursion (f := Work.FTS.PhiStar.RadialWAux.radPhi α m c)
        (A := c) (lam := -(Work.FTS.PhiStar.RadialWAux.radQ α m)) (n := k) hΦ hA (m' + 1) hn
      have heq : Dzu (m' + 1) (Work.FTS.PhiStar.RadialWAux.radPhi α m c) =ᶠ[𝓝 z]
          ((fun w => (-(Work.FTS.PhiStar.RadialWAux.radQ α m)) ^ (m' + 1)
              * Work.FTS.PhiStar.RadialWAux.radPhi α m c w)
            + ∑ t ∈ Finset.range (m' + 1),
                fun w => (-(Work.FTS.PhiStar.RadialWAux.radQ α m)) ^ (m' + 1 - 1 - t)
                  * Dzu t c w) := by
        filter_upwards [isOpen_Ioi.mem_nhds hz] with w hw
        rw [hrec w hw]
        simp only [Pi.add_apply, Finset.sum_apply]
      refine DifferentiableAt.congr_of_eventuallyEq ?_ heq
      refine DifferentiableAt.add ((hΦ z hz).differentiableAt.const_mul _) ?_
      refine DifferentiableAt.sum (fun t ht => ?_)
      have ht' : t ≤ k := by
        have := Finset.mem_range.mp ht
        omega
      exact (hA t ht' z hz).const_mul _

theorem dzu_radPsi_diff {α : ℝ} (hα : 0 < α) (hα4 : α ≤ 1 / 4) (m : ℕ) (hm : 1 ≤ m)
    {c : ℝ → ℝ} {k : ℕ} (hc : ContDiffOn ℝ (k + 1) c (Set.Ioi 0))
    (hΨ : ∀ z : ℝ, 0 < z →
      HasDerivAt (Work.FTS.PhiStar.RadialWAux.radPsi α m c)
        ((Work.FTS.PhiStar.RadialWAux.radP α m
            * Work.FTS.PhiStar.RadialWAux.radPsi α m c z - c z) / z) z) :
    ∀ j ≤ k, ∀ z : ℝ, 0 < z →
      DifferentiableAt ℝ (Dzu j (Work.FTS.PhiStar.RadialWAux.radPsi α m c)) z := by
  have hA : ∀ t ≤ k, ∀ z : ℝ, 0 < z → DifferentiableAt ℝ (Dzu t c) z :=
    fun t ht z hz => dzu_differentiableAt c k hc t ht z hz
  have hAneg : ∀ t ≤ k, ∀ z : ℝ, 0 < z →
      DifferentiableAt ℝ (Dzu t (fun z => -c z)) z := by
    intro t ht z hz
    have h1 : Dzu t (fun z => -c z) =ᶠ[𝓝 z] fun w => -Dzu t c w := by
      filter_upwards [isOpen_Ioi.mem_nhds hz] with w hw
      exact Dzu_neg (fun j hj z' hz' => hA j (by omega) z' hz') w hw
    exact DifferentiableAt.congr_of_eventuallyEq (hA t ht z hz).neg h1
  intro j
  induction j using Nat.strong_induction_on with
  | _ n ih =>
    intro hn z hz
    match n with
    | 0 => exact (hΨ z hz).differentiableAt
    | (m' + 1) =>
      have hrec := dzu_recursion (f := Work.FTS.PhiStar.RadialWAux.radPsi α m c)
        (A := fun z => -c z) (lam := Work.FTS.PhiStar.RadialWAux.radP α m) (n := k)
        hΨ hAneg (m' + 1) hn
      have heq : Dzu (m' + 1) (Work.FTS.PhiStar.RadialWAux.radPsi α m c) =ᶠ[𝓝 z]
          ((fun w => (Work.FTS.PhiStar.RadialWAux.radP α m) ^ (m' + 1)
              * Work.FTS.PhiStar.RadialWAux.radPsi α m c w)
            + ∑ t ∈ Finset.range (m' + 1),
                fun w => (Work.FTS.PhiStar.RadialWAux.radP α m) ^ (m' + 1 - 1 - t)
                  * Dzu t (fun z => -c z) w) := by
        filter_upwards [isOpen_Ioi.mem_nhds hz] with w hw
        rw [hrec w hw]
        simp only [Pi.add_apply, Finset.sum_apply]
      refine DifferentiableAt.congr_of_eventuallyEq ?_ heq
      refine DifferentiableAt.add ((hΨ z hz).differentiableAt.const_mul _) ?_
      refine DifferentiableAt.sum (fun t ht => ?_)
      have ht' : t ≤ k := by
        have := Finset.mem_range.mp ht
        omega
      exact (hAneg t ht' z hz).const_mul _

/-! ## The pointwise formula for `Dzu i (radGreen α m c)` -/

/-- The coefficient of `Dzu t c` in the bracket of the pointwise formula. -/
def rgsCoef (α : ℝ) (m : ℕ) (i t : ℕ) : ℝ :=
  (-(Work.FTS.PhiStar.RadialWAux.radQ α m)) ^ (i - 1 - t)
    - (Work.FTS.PhiStar.RadialWAux.radP α m) ^ (i - 1 - t)

/-- The bracket of the pointwise formula. -/
def rgsBracket (α : ℝ) (m : ℕ) (c : ℝ → ℝ) (i : ℕ) (z : ℝ) : ℝ :=
  (-(Work.FTS.PhiStar.RadialWAux.radQ α m)) ^ i
      * Work.FTS.PhiStar.RadialWAux.radPhi α m c z
    + (Work.FTS.PhiStar.RadialWAux.radP α m) ^ i
      * Work.FTS.PhiStar.RadialWAux.radPsi α m c z
    + ∑ t ∈ Finset.range i, rgsCoef α m i t * Dzu t c z

theorem dzu_radGreen_val {α : ℝ} (hα : 0 < α) (hα4 : α ≤ 1 / 4) (m : ℕ) (hm : 1 ≤ m)
    {c : ℝ → ℝ} {k : ℕ} (hc : ContDiffOn ℝ (k + 1) c (Set.Ioi 0))
    (hΦ : ∀ z : ℝ, 0 < z →
      HasDerivAt (Work.FTS.PhiStar.RadialWAux.radPhi α m c)
        ((-(Work.FTS.PhiStar.RadialWAux.radQ α m)
            * Work.FTS.PhiStar.RadialWAux.radPhi α m c z + c z) / z) z)
    (hΨ : ∀ z : ℝ, 0 < z →
      HasDerivAt (Work.FTS.PhiStar.RadialWAux.radPsi α m c)
        ((Work.FTS.PhiStar.RadialWAux.radP α m
            * Work.FTS.PhiStar.RadialWAux.radPsi α m c z - c z) / z) z) :
    ∀ i ≤ k, ∀ z : ℝ, 0 < z →
      Dzu i (Work.FTS.PhiStar.Radial.radGreen α m c) z
        = Work.FTS.PhiStar.RadialWAux.radK α m * rgsBracket α m c i z := by
  have hA : ∀ t ≤ k, ∀ z : ℝ, 0 < z → DifferentiableAt ℝ (Dzu t c) z :=
    fun t ht z hz => dzu_differentiableAt c k hc t ht z hz
  have hΦd := dzu_radPhi_diff hα hα4 m hm hc hΦ
  have hΨd := dzu_radPsi_diff hα hα4 m hm hc hΨ
  have hAneg : ∀ t ≤ k, ∀ z : ℝ, 0 < z →
      DifferentiableAt ℝ (Dzu t (fun z => -c z)) z := by
    intro t ht z hz
    have h1 : Dzu t (fun z => -c z) =ᶠ[𝓝 z] fun w => -Dzu t c w := by
      filter_upwards [isOpen_Ioi.mem_nhds hz] with w hw
      exact Dzu_neg (fun j hj z' hz' => hA j (by omega) z' hz') w hw
    exact DifferentiableAt.congr_of_eventuallyEq (hA t ht z hz).neg h1
  intro i hi z hz
  have hR : ∀ w ∈ Set.Ioi 0, Work.FTS.PhiStar.Radial.radGreen α m c w
      = Work.FTS.PhiStar.RadialWAux.radK α m
        * (Work.FTS.PhiStar.RadialWAux.radPhi α m c w
          + Work.FTS.PhiStar.RadialWAux.radPsi α m c w) :=
    fun w hw => Work.FTS.PhiStar.RadialWAux.radGreen_eq_rescaled hα m c w hw
  have hsum : ∀ j < i, ∀ z : ℝ, 0 < z →
      DifferentiableAt ℝ (Dzu j (fun w => Work.FTS.PhiStar.RadialWAux.radPhi α m c w
        + Work.FTS.PhiStar.RadialWAux.radPsi α m c w)) z := by
    intro j hj z hz
    have h1 : Dzu j (fun w => Work.FTS.PhiStar.RadialWAux.radPhi α m c w
        + Work.FTS.PhiStar.RadialWAux.radPsi α m c w) =ᶠ[𝓝 z]
        fun w => Dzu j (Work.FTS.PhiStar.RadialWAux.radPhi α m c) w
          + Dzu j (Work.FTS.PhiStar.RadialWAux.radPsi α m c) w := by
      filter_upwards [isOpen_Ioi.mem_nhds hz] with w hw
      exact Dzu_add (fun l hl z' hz' => hΦd l (by omega) z' hz')
        (fun l hl z' hz' => hΨd l (by omega) z' hz') w hw
    exact DifferentiableAt.congr_of_eventuallyEq
      ((hΦd j (by omega) z hz).add (hΨd j (by omega) z hz)) h1
  have hsos : ∀ a b c : ℝ, (a + b + c) ^ 2 ≤ 3 * (a ^ 2 + b ^ 2 + c ^ 2) := by
    intro a b c
    nlinarith [sq_nonneg (a - b), sq_nonneg (b - c), sq_nonneg (a - c)]
  have hBracketEq : (∑ t ∈ Finset.range i,
        (-(Work.FTS.PhiStar.RadialWAux.radQ α m)) ^ (i - 1 - t) * Dzu t c z)
      - ∑ t ∈ Finset.range i,
        (Work.FTS.PhiStar.RadialWAux.radP α m) ^ (i - 1 - t) * Dzu t c z
      = ∑ t ∈ Finset.range i, rgsCoef α m i t * Dzu t c z := by
    rw [← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl (fun t ht => ?_)
    simp only [rgsCoef]
    ring
  calc Dzu i (Work.FTS.PhiStar.Radial.radGreen α m c) z
      = Dzu i (fun w => Work.FTS.PhiStar.RadialWAux.radK α m
          * (Work.FTS.PhiStar.RadialWAux.radPhi α m c w
            + Work.FTS.PhiStar.RadialWAux.radPsi α m c w)) z :=
        Dzu_congr hR i z hz
    _ = Work.FTS.PhiStar.RadialWAux.radK α m
          * Dzu i (fun w => Work.FTS.PhiStar.RadialWAux.radPhi α m c w
            + Work.FTS.PhiStar.RadialWAux.radPsi α m c w) z :=
        Dzu_const_mul (a := Work.FTS.PhiStar.RadialWAux.radK α m) (i := i) hsum z hz
    _ = Work.FTS.PhiStar.RadialWAux.radK α m
          * (Dzu i (Work.FTS.PhiStar.RadialWAux.radPhi α m c) z
            + Dzu i (Work.FTS.PhiStar.RadialWAux.radPsi α m c) z) := by
        have hDzuAdd : Dzu i (fun w => Work.FTS.PhiStar.RadialWAux.radPhi α m c w
            + Work.FTS.PhiStar.RadialWAux.radPsi α m c w) z
            = Dzu i (Work.FTS.PhiStar.RadialWAux.radPhi α m c) z
              + Dzu i (Work.FTS.PhiStar.RadialWAux.radPsi α m c) z :=
          Dzu_add (A := Work.FTS.PhiStar.RadialWAux.radPhi α m c)
            (B := Work.FTS.PhiStar.RadialWAux.radPsi α m c)
            (fun l hl => hΦd l (by omega)) (fun l hl => hΨd l (by omega)) z hz
        rw [hDzuAdd]
    _ = Work.FTS.PhiStar.RadialWAux.radK α m * rgsBracket α m c i z := by
        have h1 := dzu_recursion (f := Work.FTS.PhiStar.RadialWAux.radPhi α m c) (A := c)
          (lam := -(Work.FTS.PhiStar.RadialWAux.radQ α m)) (n := k) hΦ hA i hi z hz
        have h2 := dzu_recursion (f := Work.FTS.PhiStar.RadialWAux.radPsi α m c)
          (A := fun z => -c z) (lam := Work.FTS.PhiStar.RadialWAux.radP α m) (n := k)
          hΨ hAneg i hi z hz
        have h3 : (∑ t ∈ Finset.range i,
              (Work.FTS.PhiStar.RadialWAux.radP α m) ^ (i - 1 - t)
                * Dzu t (fun z => -c z) z)
            = -∑ t ∈ Finset.range i,
              (Work.FTS.PhiStar.RadialWAux.radP α m) ^ (i - 1 - t) * Dzu t c z := by
          rw [← Finset.sum_neg_distrib]
          refine Finset.sum_congr rfl (fun t ht => ?_)
          have htk : t ≤ k := by
            have := Finset.mem_range.mp ht
            omega
          rw [Dzu_neg (fun j hj z' hz' => hA j (by omega) z' hz') z hz]
          ring
        rw [h1, h2, h3]
        simp only [rgsBracket]
        rw [← hBracketEq]
        ring

end Work.FTS.EllExist.Honesty
