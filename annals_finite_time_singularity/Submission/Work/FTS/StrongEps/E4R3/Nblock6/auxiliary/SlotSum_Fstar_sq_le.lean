/-
# `SlotSum_Fstar_sq_le`

**PORTABLE TWIN.**  The requested declaration

  `Work.FTS.StrongEps.E4R3.Nblock6.aux.SlotSum_Fstar_sq_le`

was assigned to `Submission/Work/FTS/StrongEps/E4R3/Nblock6/aux/SlotSum_Fstar_sq_le.lean`.
That module can never be built: Lean's `checkModuleNamePortability` rejects *any* module whose
name has a component equal to the reserved file name `aux` (case-insensitively), and the error
is raised before elaboration, from the module name in Lake's `setup.json`.  This file is the
portable twin: it carries the same namespace (`Work.FTS.StrongEps.E4R3.Nblock6.aux`) and the
same declaration name and statement, with a complete proof (no placeholders).  Consumers should

  `import Submission.Work.FTS.StrongEps.E4R3.Nblock6.auxiliary.SlotSum_Fstar_sq_le`

and then use `Work.FTS.StrongEps.E4R3.Nblock6.aux.SlotSum_Fstar_sq_le`.

## The mathematics

`Work.FTS.StrongPersist.SlotSum B z = ∑_{q<7} (D_z^q (z' ↦ B z'))(z)² · w(z)²` collects the
radial (`z`-only) slots of the `ℋ⁶`-integrand of the `z`-only profile `B`.  Here
`B z = α² · F_*(z)²`, the squared angular factor of the fundamental model
(`F_* z = 2z/(1+z)²`).

The lemma bounds `∫_0^∞ SlotSum (α²F_*²)` by `C · K⁴ · α⁴`, where

  `K` dominates the jets of `F_*`: `|D_z^b F_*| ≤ K · F_*` on `(0,∞)` for `b ≤ 6`.

* **The `K⁴` is the point.**  `D_z^q (F_*²)` is a *two-factor* Leibniz sum
  (`Work.FTS.StrongPersist.H6Aux.DzdIter_mul_of_diff`), so from `|D_z^b F_*| ≤ K F_*` each of the
  two factors costs one `K` and `|D_z^q (F_*²)| ≤ 2^q K² F_*²`; squaring in the slot sum turns
  the `K²` into `K⁴`.  Concretely we use the generous bound `448 = 7 · 2⁶` (the Leibniz sum has
  `q + 1 ≤ 7` terms with binomial coefficient `q.choose b ≤ 2^q ≤ 2⁶`).
* **The `α⁴ = (α²)²`** is the square of the coefficient `α²` of the profile.
* **The `z`-integral.**  `F_*⁴ w² = 16/(1+z)⁴` exactly, and `∫_0^∞ (1+z)^{-4} dz = 1/3`
  (the antiderivative `-(1/3)(1+z)^{-3}` tends to `0` at `+∞`).  Hence
  `∫ SlotSum ≤ 7 · 448² · 16/3 · K⁴ α⁴ = 22478848/3 · K⁴ α⁴ ≤ 10⁷ K⁴ α⁴`, and one can take
  `C = 10⁷` — universal, independent of `α`, `K`, the profile and the datum.

Everything rests on `[propext, Classical.choice, Quot.sound]`.
-/
import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Algebra.Ring.IsFormallyReal
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import Submission.Work.FM.Core
import Submission.Work.FTS.StrongPersist.L6Aux.LinMem6Aux
import Submission.Work.FTS.StrongPersist.H6Pair6Aux.SepMem6Local
import Submission.Work.FTS.StrongPersist.H6Aux.DzdIter_mul_of_diff
import Submission.Work.Elliptic.L12Aux

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open MeasureTheory Set Filter
open scoped ContDiff Topology

namespace Work.FTS.StrongEps.E4R3.Nblock6.aux

set_option autoImplicit false
set_option maxHeartbeats 1600000

/-! ## §1 The iterated operator `D_z = z ∂_z` on `z`-only profiles -/

/-- `DzdIter` is linear over multiplication by a constant.  (`deriv` of a constant multiple is
the constant multiple of the `deriv` also at the points where the function is not
differentiable, `Work.Spaces.deriv_const_mul'`.) -/
theorem DzdIter_const_mul (c : ℝ) (u : ℝ → ℝ) (k : ℕ) :
    Work.Elliptic.DzdIter k (fun z => c * u z) = fun z => c * Work.Elliptic.DzdIter k u z := by
  induction k with
  | zero => rfl
  | succ k ih =>
      funext z
      show z * deriv (fun z' => Work.Elliptic.DzdIter k (fun z => c * u z) z') z
        = c * (z * deriv (fun z' => Work.Elliptic.DzdIter k u z') z)
      rw [ih, Work.Spaces.deriv_const_mul']
      ring

/-- If `r` is `C^n` on `(0,∞)` for every `n`, then so is every iterate `DzdIter b r`. -/
theorem contDiffOn_DzdIter (r : ℝ → ℝ) (hr : ∀ n : ℕ, ContDiffOn ℝ (n : ℕ∞ω) r (Set.Ioi 0)) :
    ∀ b (n : ℕ), ContDiffOn ℝ (n : ℕ∞ω) (Work.Elliptic.DzdIter b r) (Set.Ioi 0) := by
  intro b
  induction b with
  | zero => intro n; exact hr n
  | succ b ih =>
      intro n
      have hder : ContDiffOn ℝ (n : ℕ∞ω) (deriv (Work.Elliptic.DzdIter b r)) (Set.Ioi 0) :=
        (ih (n + 1)).deriv_of_isOpen isOpen_Ioi (m := (n : ℕ∞ω))
          (n := ((n + 1 : ℕ) : ℕ∞ω)) le_rfl
      have hid : ContDiffOn ℝ (n : ℕ∞ω) (fun z : ℝ => z) (Set.Ioi 0) := contDiffOn_id
      exact hid.mul hder

/-- `F_* = 2z/(1+z)²` is `C^n` on `(0,∞)` for every `n` (rational, with denominator `(1+z)²`
nonvanishing there). -/
theorem contDiffOn_Fstar (n : ℕ) : ContDiffOn ℝ (n : ℕ∞ω) Work.FM.Fstar (Set.Ioi 0) := by
  have hnum : ContDiffOn ℝ (n : ℕ∞ω) (fun z : ℝ => 2 * z) (Set.Ioi 0) :=
    contDiffOn_const.mul contDiffOn_id
  have hden : ContDiffOn ℝ (n : ℕ∞ω) (fun z : ℝ => (1 + z) ^ 2) (Set.Ioi 0) :=
    (contDiffOn_const.add contDiffOn_id).pow 2
  have hne : ∀ z ∈ Set.Ioi (0 : ℝ), (1 + z) ^ 2 ≠ 0 := by
    intro z hz
    have hz0 : 0 < z := hz
    exact pow_ne_zero 2 (by linarith : (1 : ℝ) + z ≠ 0)
  exact hnum.div hden hne

/-- The iterates of `F_*` up to order five are differentiable on `(0,∞)` (this is what the
Leibniz rule `DzdIter_mul_of_diff` at order six needs). -/
theorem differentiableOn_DzdIter_Fstar (b : ℕ) (hb : b ≤ 5) :
    DifferentiableOn ℝ (Work.Elliptic.DzdIter b Work.FM.Fstar) (Set.Ioi 0) :=
  (contDiffOn_DzdIter Work.FM.Fstar contDiffOn_Fstar b 1).differentiableOn (by norm_num)

/-! ## §2 The Leibniz bound for the jets of `F_*²` -/

/-- **The Leibniz bound.**  If the jets of `F_*` are dominated by `K · F_*` up to order six,
then the jets of `F_*²` are dominated by `448 · K² · F_*²`.

(`448 = 7 · 2⁶`: the Leibniz sum has `q + 1 ≤ 7` terms, each with binomial coefficient
`q.choose b ≤ 2^q ≤ 2⁶`, and each of the two factors costs one `K F_*`.) -/
theorem DzdIter_Fstar_mul_Fstar_le {K : ℝ} (hKpos : 0 < K)
    (hK : ∀ b : ℕ, b ≤ 6 → ∀ z : ℝ, 0 < z →
      |Work.Elliptic.DzdIter b Work.FM.Fstar z| ≤ K * Work.FM.Fstar z) :
    ∀ q ≤ 6, ∀ z : ℝ, 0 < z →
      |Work.Elliptic.DzdIter q (fun z => Work.FM.Fstar z * Work.FM.Fstar z) z|
        ≤ 448 * K ^ 2 * (Work.FM.Fstar z) ^ 2 := by
  intro q hq z hz
  have hz0 : 0 < z := hz
  have hFnn : 0 ≤ Work.FM.Fstar z := by
    rw [Work.FM.Fstar]; positivity
  have hexp := Work.FTS.StrongPersist.H6Aux.DzdIter_mul_of_diff q Work.FM.Fstar Work.FM.Fstar
    (fun b _ => differentiableOn_DzdIter_Fstar b (by omega))
    (fun b _ => differentiableOn_DzdIter_Fstar b (by omega))
    z (Set.mem_Ioi.mpr hz0)
  rw [hexp]
  have hterm : ∀ b ∈ Finset.range (q + 1),
      |(q.choose b : ℝ) * (Work.Elliptic.DzdIter b Work.FM.Fstar z
        * Work.Elliptic.DzdIter (q - b) Work.FM.Fstar z)|
        ≤ 64 * (K ^ 2 * (Work.FM.Fstar z) ^ 2) := by
    intro b hb
    have hbq : b ≤ q := Nat.lt_succ_iff.mp (Finset.mem_range.mp hb)
    have h1 : |Work.Elliptic.DzdIter b Work.FM.Fstar z| ≤ K * Work.FM.Fstar z :=
      hK b (by omega) z hz0
    have h2 : |Work.Elliptic.DzdIter (q - b) Work.FM.Fstar z| ≤ K * Work.FM.Fstar z :=
      hK (q - b) (by omega) z hz0
    have hch : (q.choose b : ℝ) ≤ 64 := by
      have h1 : q.choose b ≤ 2 ^ q := Nat.choose_le_two_pow q b
      have h2 : (2 : ℕ) ^ q ≤ 2 ^ 6 := Nat.pow_le_pow_right (by norm_num) hq
      have h3 : q.choose b ≤ 64 := by omega
      exact_mod_cast h3
    rw [abs_mul, abs_mul, abs_of_nonneg (Nat.cast_nonneg (q.choose b))]
    have hprod : |Work.Elliptic.DzdIter b Work.FM.Fstar z|
          * |Work.Elliptic.DzdIter (q - b) Work.FM.Fstar z|
        ≤ K ^ 2 * (Work.FM.Fstar z) ^ 2 := by
      have hmul := mul_le_mul h1 h2 (abs_nonneg _) (mul_nonneg (le_of_lt hKpos) hFnn)
      calc |Work.Elliptic.DzdIter b Work.FM.Fstar z|
              * |Work.Elliptic.DzdIter (q - b) Work.FM.Fstar z|
          ≤ (K * Work.FM.Fstar z) * (K * Work.FM.Fstar z) := hmul
        _ = K ^ 2 * (Work.FM.Fstar z) ^ 2 := by ring
    exact mul_le_mul hch hprod (mul_nonneg (abs_nonneg _) (abs_nonneg _)) (by norm_num)
  calc |∑ b ∈ Finset.range (q + 1), (q.choose b : ℝ)
          * (Work.Elliptic.DzdIter b Work.FM.Fstar z
            * Work.Elliptic.DzdIter (q - b) Work.FM.Fstar z)|
      ≤ ∑ b ∈ Finset.range (q + 1), |(q.choose b : ℝ)
          * (Work.Elliptic.DzdIter b Work.FM.Fstar z
            * Work.Elliptic.DzdIter (q - b) Work.FM.Fstar z)| :=
        Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _b ∈ Finset.range (q + 1), (64 * (K ^ 2 * (Work.FM.Fstar z) ^ 2)) :=
        Finset.sum_le_sum hterm
    _ = ((q + 1 : ℕ) : ℝ) * (64 * (K ^ 2 * (Work.FM.Fstar z) ^ 2)) := by
        rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
    _ ≤ 7 * (64 * (K ^ 2 * (Work.FM.Fstar z) ^ 2)) := by
        refine mul_le_mul_of_nonneg_right ?_ (by positivity)
        exact_mod_cast (by omega : q + 1 ≤ 7)
    _ = 448 * K ^ 2 * (Work.FM.Fstar z) ^ 2 := by ring

/-! ## §3 The exact radial weight identity and the `z`-integral -/

/-- `F_*⁴ · w² = 16/(1+z)⁴`: with `F_* z = 2z/(1+z)²` and `w z = (1+z)²/z²` the `z`-powers
cancel exactly. -/
theorem Fstar_pow_four_mul_w_sq (z : ℝ) (hz : 0 < z) :
    (Work.FM.Fstar z) ^ 4 * (Work.Spaces.w z) ^ 2 = 16 * (1 + z) ^ (-4 : ℝ) := by
  have hrw : (1 + z) ^ (-4 : ℝ) = 1 / (1 + z) ^ 4 := by
    rw [Real.rpow_neg (by linarith : (0 : ℝ) ≤ 1 + z),
      show (4 : ℝ) = ((4 : ℕ) : ℝ) by norm_num, Real.rpow_natCast, one_div]
  rw [Work.FM.Fstar, Work.Spaces.w, hrw]
  field_simp
  ring_nf

/-- `(1+z)^{-4}` is integrable on `(0,∞)` (it is `(z+1)^a` with `a = -4 < -1`). -/
theorem integrableOn_one_add_rpow_neg_four :
    IntegrableOn (fun z : ℝ => (1 + z) ^ (-4 : ℝ)) (Set.Ioi 0) := by
  have h := integrableOn_add_rpow_Ioi_of_lt (a := (-4 : ℝ)) (c := (0 : ℝ)) (m := (1 : ℝ))
    (by norm_num) (by norm_num)
  simpa [add_comm] using h

/-- `∫_0^∞ (1+z)^{-4} dz = 1/3`, by the fundamental theorem with the antiderivative
`-(1/3)(1+z)^{-3} → 0` at `+∞`. -/
theorem integral_one_add_rpow_neg_four :
    (∫ z in Set.Ioi (0 : ℝ), (1 + z) ^ (-4 : ℝ)) = 1 / 3 := by
  have hderiv : ∀ x ∈ Set.Ici (0 : ℝ),
      HasDerivAt (fun t : ℝ => (-(1 / 3)) * (1 + t) ^ (-3 : ℝ)) ((1 + x) ^ (-4 : ℝ)) x := by
    intro x hx
    have hx0 : (0 : ℝ) ≤ x := hx
    have h1 : (1 : ℝ) + x ≠ 0 := by linarith
    have h2 : HasDerivAt (fun t : ℝ => (1 : ℝ) + t) 1 x := Work.FM.hasDerivAt_add_const 1 x
    have h3 := (h2.rpow_const (p := (-3 : ℝ)) (Or.inl h1)).const_mul (-(1 / 3))
    have h4 : (1 * (-3 : ℝ) * (1 + x) ^ ((-3 : ℝ) - 1)) = ((-3 : ℝ)) * (1 + x) ^ (-4 : ℝ) := by
      rw [show (-3 : ℝ) - 1 = -4 by norm_num]; ring
    have h5 : -(1 / 3) * (((-3 : ℝ)) * (1 + x) ^ (-4 : ℝ)) = (1 + x) ^ (-4 : ℝ) := by ring
    rw [h4, h5] at h3
    exact h3
  have htend : Tendsto (fun t : ℝ => (-(1 / 3)) * (1 + t) ^ (-3 : ℝ)) atTop (𝓝 0) := by
    have h : Tendsto (fun t : ℝ => (1 + t)) atTop atTop := by
      simpa [add_comm] using Filter.tendsto_atTop_add_const_right Filter.atTop (1 : ℝ)
        (tendsto_id : Tendsto (fun t : ℝ => t) atTop atTop)
    have h2 : Tendsto (fun t : ℝ => (1 + t) ^ (-3 : ℝ)) atTop (𝓝 0) :=
      (tendsto_rpow_neg_atTop (by norm_num : (0 : ℝ) < 3)).comp h
    have h3 := h2.const_mul (-(1 / 3))
    rw [mul_zero] at h3
    exact h3
  have hmain := MeasureTheory.integral_Ioi_of_hasDerivAt_of_tendsto' hderiv
    integrableOn_one_add_rpow_neg_four htend
  simpa using hmain

/-! ## §4 The main theorem -/

/-- **The radial slot sum of `α² F_*²` is `O(K⁴ α⁴)`.**

The `z`-integral of the slot sum of the profile `z ↦ α² F_*(z)²` is bounded by `C K⁴ α⁴`
whenever `K` dominates the jets of `F_* = 2z/(1+z)²` up to order six; `C = 10⁷` is universal.
The exponent `4` is exactly the square of the two `K`'s of the two-factor Leibniz expansion of
`D_z^q (F_*²)`; the `α⁴` is `(α²)²`. -/
theorem SlotSum_Fstar_sq_le : ∃ C : ℝ, 0 < C ∧ ∀ K : ℝ, 0 < K →
    (∀ b : ℕ, b ≤ 6 → ∀ z : ℝ, 0 < z → |Work.Elliptic.DzdIter b Work.FM.Fstar z| ≤ K * Work.FM.Fstar z) →
    ∀ α ∈ Set.Ioc (0 : ℝ) 1,
    MeasureTheory.IntegrableOn (Work.FTS.StrongPersist.SlotSum (fun z => α ^ 2 * (Work.FM.Fstar z) ^ 2)) Work.Spaces.Iz ∧
    (∫ z in Work.Spaces.Iz, Work.FTS.StrongPersist.SlotSum (fun z => α ^ 2 * (Work.FM.Fstar z) ^ 2) z) ≤ C * K ^ 4 * α ^ 4 := by
  refine ⟨10000000, by norm_num, ?_⟩
  intro K hKpos hK α hα
  have hα0 : 0 < α := hα.1
  -- the unfolding of `SlotSum` into the `DzdIter`-sum
  have hEq : Work.FTS.StrongPersist.SlotSum (fun z => α ^ 2 * (Work.FM.Fstar z) ^ 2)
      = fun z => ∑ q ∈ Finset.range 7,
          (Work.Elliptic.DzdIter q (fun z => α ^ 2 * (Work.FM.Fstar z) ^ 2) z) ^ 2
            * (Work.Spaces.w z) ^ 2 := by
    funext z
    rw [Work.FTS.StrongPersist.SlotSum]
    exact Finset.sum_congr rfl fun q _ => by rw [Work.Elliptic.DzIter_rad]
  -- the pointwise bound on the slots
  have hslot : ∀ z : ℝ, 0 < z → ∀ q ∈ Finset.range 7,
      (Work.Elliptic.DzdIter q (fun z => α ^ 2 * (Work.FM.Fstar z) ^ 2) z) ^ 2
          * (Work.Spaces.w z) ^ 2
        ≤ α ^ 4 * K ^ 4 * (3211264 * (1 + z) ^ (-4 : ℝ)) := by
    intro z hz0 q hq
    have hq6 : q ≤ 6 := Nat.le_of_lt_succ (Finset.mem_range.mp hq)
    have hlin : Work.Elliptic.DzdIter q (fun z => α ^ 2 * (Work.FM.Fstar z) ^ 2) z
        = α ^ 2 * Work.Elliptic.DzdIter q
            (fun z => Work.FM.Fstar z * Work.FM.Fstar z) z := by
      have h1 : (fun z' : ℝ => α ^ 2 * (Work.FM.Fstar z') ^ 2)
          = fun z' => α ^ 2 * (Work.FM.Fstar z' * Work.FM.Fstar z') := by
        funext z'; ring
      rw [h1,
        congrFun (DzdIter_const_mul (α ^ 2)
          (fun z' => Work.FM.Fstar z' * Work.FM.Fstar z') q) z]
    rw [hlin]
    have hb := DzdIter_Fstar_mul_Fstar_le hKpos hK q hq6 z hz0
    have hXs : (Work.Elliptic.DzdIter q (fun z => Work.FM.Fstar z * Work.FM.Fstar z) z) ^ 2
        ≤ (448 * K ^ 2 * (Work.FM.Fstar z) ^ 2) ^ 2 := by
      rw [← sq_abs]
      exact pow_le_pow_left₀ (abs_nonneg _) hb 2
    calc (α ^ 2 * Work.Elliptic.DzdIter q (fun z => Work.FM.Fstar z * Work.FM.Fstar z) z) ^ 2
            * (Work.Spaces.w z) ^ 2
        = α ^ 4 * (Work.Elliptic.DzdIter q (fun z => Work.FM.Fstar z * Work.FM.Fstar z) z) ^ 2
            * (Work.Spaces.w z) ^ 2 := by ring
      _ ≤ α ^ 4 * (448 * K ^ 2 * (Work.FM.Fstar z) ^ 2) ^ 2 * (Work.Spaces.w z) ^ 2 := by
          refine mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hXs (by positivity))
            (by positivity)
      _ = α ^ 4 * K ^ 4 * (200704 * ((Work.FM.Fstar z) ^ 4 * (Work.Spaces.w z) ^ 2)) := by ring
      _ = α ^ 4 * K ^ 4 * (3211264 * (1 + z) ^ (-4 : ℝ)) := by
          rw [Fstar_pow_four_mul_w_sq z hz0]; ring
  have hpt : ∀ z : ℝ, 0 < z →
      Work.FTS.StrongPersist.SlotSum (fun z => α ^ 2 * (Work.FM.Fstar z) ^ 2) z
        ≤ α ^ 4 * K ^ 4 * (22478848 * (1 + z) ^ (-4 : ℝ)) := by
    intro z hz0
    rw [hEq]
    calc ∑ q ∈ Finset.range 7,
          (Work.Elliptic.DzdIter q (fun z => α ^ 2 * (Work.FM.Fstar z) ^ 2) z) ^ 2
            * (Work.Spaces.w z) ^ 2
        ≤ ∑ _q ∈ Finset.range 7, α ^ 4 * K ^ 4 * (3211264 * (1 + z) ^ (-4 : ℝ)) :=
          Finset.sum_le_sum (hslot z hz0)
      _ = 7 * (α ^ 4 * K ^ 4 * (3211264 * (1 + z) ^ (-4 : ℝ))) := by
          rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]; norm_num
      _ = α ^ 4 * K ^ 4 * (22478848 * (1 + z) ^ (-4 : ℝ)) := by ring
  -- measurability of the slot sum
  have hBsm : ∀ n : ℕ, ContDiffOn ℝ (n : ℕ∞ω)
      (fun z : ℝ => α ^ 2 * (Work.FM.Fstar z) ^ 2) (Set.Ioi 0) :=
    fun n => contDiffOn_const.mul ((contDiffOn_Fstar n).pow 2)
  have hcont_q : ∀ q : ℕ, ContinuousOn
      (fun z : ℝ => (Work.Elliptic.DzdIter q (fun z => α ^ 2 * (Work.FM.Fstar z) ^ 2) z) ^ 2)
      (Set.Ioi 0) :=
    fun q => (contDiffOn_DzdIter _ hBsm q 1).continuousOn.pow 2
  have hcont_w : ContinuousOn (fun z : ℝ => (Work.Spaces.w z) ^ 2) (Set.Ioi 0) := by
    have hnum : ContinuousOn (fun z : ℝ => (1 + z) ^ 2) (Set.Ioi 0) :=
      (continuousOn_const.add continuousOn_id).pow 2
    have hden : ContinuousOn (fun z : ℝ => z ^ 2) (Set.Ioi 0) := continuousOn_id.pow 2
    have hw : ContinuousOn (fun z : ℝ => Work.Spaces.w z) (Set.Ioi 0) := by
      convert hnum.div hden (fun z hz => by
        have hz0 : 0 < z := hz
        exact pow_ne_zero 2 (ne_of_gt hz0)) using 1
      funext z
      rw [Work.Spaces.w, Pi.div_apply]
    exact hw.pow 2
  have hmeas : AEStronglyMeasurable
      (Work.FTS.StrongPersist.SlotSum (fun z => α ^ 2 * (Work.FM.Fstar z) ^ 2))
      (volume.restrict (Set.Ioi 0)) := by
    rw [hEq]
    exact (continuousOn_finsetSum (Finset.range 7)
      (fun q _ => (hcont_q q).mul hcont_w)).aestronglyMeasurable measurableSet_Ioi
  -- the dominator
  have hdom_int : IntegrableOn
      (fun z : ℝ => α ^ 4 * K ^ 4 * (22478848 * (1 + z) ^ (-4 : ℝ))) (Set.Ioi 0) :=
    MeasureTheory.Integrable.const_mul
      (MeasureTheory.Integrable.const_mul integrableOn_one_add_rpow_neg_four 22478848)
      (α ^ 4 * K ^ 4)
  have hint_ioi : IntegrableOn
      (Work.FTS.StrongPersist.SlotSum (fun z => α ^ 2 * (Work.FM.Fstar z) ^ 2))
      (Set.Ioi 0) := by
    refine hdom_int.mono' hmeas ?_
    filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Ioi] with z hz
    rw [Real.norm_eq_abs, abs_of_nonneg (Work.FTS.StrongPersist.SlotSum_nonneg _ z)]
    exact hpt z hz
  -- transfer from `(0,∞)` to `[0,∞) = Iz`
  have hmes_eq : volume.restrict (Set.Ioi (0 : ℝ)) = volume.restrict (Set.Ici (0 : ℝ)) :=
    MeasureTheory.Measure.restrict_congr_set MeasureTheory.Ioi_ae_eq_Ici
  have hint : IntegrableOn
      (Work.FTS.StrongPersist.SlotSum (fun z => α ^ 2 * (Work.FM.Fstar z) ^ 2))
      Work.Spaces.Iz := by
    show Integrable (Work.FTS.StrongPersist.SlotSum (fun z => α ^ 2 * (Work.FM.Fstar z) ^ 2))
      (volume.restrict (Set.Ici (0 : ℝ)))
    rw [← hmes_eq]
    exact hint_ioi
  refine ⟨hint, ?_⟩
  have hIntEq : (∫ z in Work.Spaces.Iz,
        Work.FTS.StrongPersist.SlotSum (fun z => α ^ 2 * (Work.FM.Fstar z) ^ 2) z)
      = ∫ z in Set.Ioi (0 : ℝ),
        Work.FTS.StrongPersist.SlotSum (fun z => α ^ 2 * (Work.FM.Fstar z) ^ 2) z := by
    show (∫ z in Set.Ici (0 : ℝ),
        Work.FTS.StrongPersist.SlotSum (fun z => α ^ 2 * (Work.FM.Fstar z) ^ 2) z) = _
    exact MeasureTheory.integral_Ici_eq_integral_Ioi
  rw [hIntEq]
  have hae : ∀ᵐ z ∂(volume.restrict (Set.Ioi (0 : ℝ))),
      Work.FTS.StrongPersist.SlotSum (fun z => α ^ 2 * (Work.FM.Fstar z) ^ 2) z
        ≤ α ^ 4 * K ^ 4 * (22478848 * (1 + z) ^ (-4 : ℝ)) := by
    filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Ioi] with z hz
    exact hpt z hz
  calc ∫ z in Set.Ioi (0 : ℝ),
        Work.FTS.StrongPersist.SlotSum (fun z => α ^ 2 * (Work.FM.Fstar z) ^ 2) z
      ≤ ∫ z in Set.Ioi (0 : ℝ), α ^ 4 * K ^ 4 * (22478848 * (1 + z) ^ (-4 : ℝ)) :=
        MeasureTheory.integral_mono_ae hint_ioi hdom_int hae
    _ = α ^ 4 * K ^ 4 * (22478848 * (∫ z in Set.Ioi (0 : ℝ), (1 + z) ^ (-4 : ℝ))) := by
        simp only [MeasureTheory.integral_const_mul]
    _ = α ^ 4 * K ^ 4 * (22478848 * (1 / 3)) := by rw [integral_one_add_rpow_neg_four]
    _ ≤ α ^ 4 * K ^ 4 * 10000000 :=
        mul_le_mul_of_nonneg_left (by norm_num) (by positivity)
    _ = 10000000 * K ^ 4 * α ^ 4 := by ring

end Work.FTS.StrongEps.E4R3.Nblock6.aux
