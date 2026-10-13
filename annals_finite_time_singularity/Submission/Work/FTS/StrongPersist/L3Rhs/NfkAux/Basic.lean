/-
# `Submission/Work/FTS/StrongPersist/L3Rhs/NfkAux/Basic.lean`

Auxiliary facts for the `NFkSum` block (`Work.FTS.StrongPersist.L3Rhs.L3RhsNfkBlock`):

* `FK f = 3 · F_*(f)` (the elliptic angular moment), and the resulting finite-order smoothness of
  `z ↦ FK f z` on `(0,∞)` in the honest class `SmoothOpen f` + `HkMem α 6 f`;
* `HkMem α 3 (D_θ f)` for `SmoothOpen f` + `HkMem α 4 f` (the finite-order form of the
  `D_θ`-descent, via a pointwise majorant);
* the two *star*-terms `N₄^{sg}`, `N₅^{sg}` of the block (the `F_*`-coefficient times `D_θ f` resp.
  `sin²θ·f`) are honest in `ℋ³` with the norm bound, via the `z`-multiplier estimate
  `L3Aux.HkIntegrand_zmul_le` applied to the explicit multiplier `z ↦ 2z/(1+z)²`.

Everything rests on `[propext, Classical.choice, Quot.sound]`.
-/
import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Integral.IntegrableOn
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Mathlib.Order.CompletePartialOrder
import Submission.Work.FTS.StrongPersist.L3Rhs.Defs
import Submission.Work.FTS.StrongPersist.L3Rhs.Assembly
import Submission.Work.FTS.StrongPersist.L3Aux.HkIntegrand_zmul_le
import Submission.Work.FTS.StrongPersist.L6Aux.ZslotSupBound6
import Submission.Work.FTS.OpenPkg.fkH_field
import Submission.Work.FTS.OpenPkg.C4Factors
import Submission.Work.FTS.EllipticEst.UopHk.slot_algebra
import Submission.Work.FTS.CoercivityStep.Norm.HkSq_Dth_le
import Submission.Work.FTS.Nonlinear.FstarPkgAll
import Submission.Work.Blocks.HkMul_ang_le
import Submission.Work.FTS.FinalClock.HkIntegrandMulDthSmooth
import Submission.Work.FTS.LocData.HkMem_of_majorant
import Submission.Work.Coercivity.HkMem_dth
import Submission.Work.FTS.EllipticEst.ScaleAPI
import Submission.Work.FTS.CoercivityFix.Transfer.E2pkg.FinCalc

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.StrongPersist.L3Rhs.NfkAux

set_option autoImplicit false
set_option linter.unusedVariables false
set_option maxHeartbeats 1600000

/-! ## The angular moment `FK` is three times the elliptic `F_*` -/

/-- `FK f = 3·F_*(f)`: both are `∫_θ f(z,θ)·3 sinθ cos²θ dθ`. -/
theorem fk_eq_three_Fstar (f : ℝ → ℝ → ℝ) :
    (fun z => Work.Construction.FK f z) = fun z => 3 * Work.Elliptic.Fstar f z := by
  funext z
  rw [← Work.FTS.OpenPkg.Qang_zero_eq_FK f, Work.Elliptic.Qang, Work.Elliptic.Fstar,
    Work.Spaces.DzIter_zero]
  have hpt : (fun θ : ℝ => Work.Elliptic.Ktheta θ * f z θ)
      = fun θ : ℝ => 3 * (f z θ * Work.Elliptic.sinCos2 θ) := by
    funext θ
    simp only [Work.Elliptic.Ktheta, Work.Elliptic.sinCos2]
    ring
  rw [hpt, MeasureTheory.integral_const_mul]

/-- **Finite-order smoothness of the angular moment** `z ↦ FK f z` on `(0,∞)`, in the honest
class (`SmoothOpen f`, `HkMem α 6 f`). -/
theorem contDiffOn_FK {α : ℝ} (hα : 0 < α) (hα1 : α ≤ 1) {f : ℝ → ℝ → ℝ}
    (hsm : Work.FTS.EllipticEst.SmoothOpen f) (hmem : Work.Spaces.HkMem α 6 f) :
    ∀ (n : ℕ), n ≤ 5 → ContDiffOn ℝ n (fun z => Work.Construction.FK f z) (Set.Ioi (0 : ℝ)) := by
  have hFstar : ContDiffOn ℝ 5 (Work.Elliptic.Fstar f) (Set.Ioi (0 : ℝ)) := by
    have h := Work.FTS.EllipticEst.UopHk.contDiffOn_Fstar_of_smoothOpen_Hk α 6 f hsm hmem
      (by norm_num)
    exact h
  intro n hn
  have h3 : ContDiffOn ℝ n (fun z => 3 * Work.Elliptic.Fstar f z) (Set.Ioi (0 : ℝ)) := by
    have hle : (((n : ℕ) : WithTop ℕ∞)) ≤ (((5 : ℕ) : WithTop ℕ∞)) := by exact_mod_cast hn
    have h' := (hFstar.const_smul (3 : ℝ)).of_le hle
    simpa only [Pi.smul_apply, smul_eq_mul] using h'
  rw [fk_eq_three_Fstar f]
  exact h3

/-! ## `HkMem α 3 (D_θ f)` in the honest class -/

/-- **The `D_θ`-descent at level three.**  For `f` smooth on the open quadrant and honest in
`ℋ⁴`, `D_θ f` is honest in `ℋ³`.  This is the finite-order form of `Coercivity.HkMem_dth`
(which asks for `SmoothNbhd`), proved here by the pointwise majorant
`HkIntegrand α 3 (D_θ f) ≤ HkIntegrand α 4 f`. -/
theorem hkMem_dth_three {α : ℝ} (hα : 0 < α) {f : ℝ → ℝ → ℝ}
    (hsm : Work.FTS.EllipticEst.SmoothOpen f) (hmem4 : Work.Spaces.HkMem α 4 f) :
    Work.Spaces.HkMem α 3 (Work.Spaces.Dth f) := by
  have hsmD : ContDiffOn ℝ 3 (Function.uncurry (Work.Spaces.Dth f))
      Work.FTS.EllipticEst.Q0 := hsm.Dth.forall 3
  refine Work.FTS.LocData.HkMem_of_majorant α 3
    (Work.FTS.OpenPkg.continuousOn_HkIntegrand_of_contDiffOn α (n := 3) (k := 3) le_rfl hsmD)
    (fun z hz => hmem4.1 z hz) hmem4.2 ?_
  intro z hz θ hθ
  exact Work.Coercivity.HkIntegrand_Dth_le α hα 3 f z θ hz hθ

/-! ## Two small bookkeeping lemmas -/

/-- `D_θ^i(D_θ f) = D_θ^{i+1} f`. -/
theorem DthIter_Dth (i : ℕ) (f : ℝ → ℝ → ℝ) :
    Work.Spaces.DthIter i (Work.Spaces.Dth f) = Work.Spaces.DthIter (i + 1) f := by
  induction i with
  | zero => rfl
  | succ n ih => exact congrArg Work.Spaces.Dth ih

/-- `D_z^a(c·r) = c·D_z^a r` for the iterated radial operator. -/
theorem DzdIter_const_mul (a : ℕ) (c : ℝ) (r : ℝ → ℝ) :
    Work.Elliptic.DzdIter a (fun z => c * r z)
      = fun z => c * Work.Elliptic.DzdIter a r z := by
  rw [Work.FTS.CoercivityFix.Transfer.E2pkg.DzdIter_eq_Zop_iter a (fun z => c * r z),
    Work.FTS.CoercivityFix.Transfer.E2pkg.DzdIter_eq_Zop_iter a r,
    Work.FTS.CoercivityFix.Transfer.E2pkg.Zop_iter_const_mul]

/-- The value form of `DzdIter_const_mul`. -/
theorem DzdIter_const_mul_apply (a : ℕ) (c : ℝ) (r : ℝ → ℝ) (z : ℝ) :
    Work.Elliptic.DzdIter a (fun z => c * r z) z = c * Work.Elliptic.DzdIter a r z :=
  congrFun (DzdIter_const_mul a c r) z

/-- The angular multiple `sin²θ·f` of a `SmoothOpen` datum is `SmoothOpen`. -/
theorem smoothOpen_sin_sq_mul {f : ℝ → ℝ → ℝ}
    (hsm : Work.FTS.EllipticEst.SmoothOpen f) :
    Work.FTS.EllipticEst.SmoothOpen (fun z θ => Real.sin θ ^ 2 * f z θ) := by
  have h1 : ContDiffOn ℝ Work.Stability.smoothOrder (fun p : ℝ × ℝ => Real.sin p.2 ^ 2)
      Work.FTS.EllipticEst.Q0 :=
    ((Real.contDiff_sin.comp contDiff_snd).pow 2).contDiffOn
  exact h1.mul hsm

/-! ## The explicit radial multiplier `z ↦ 2z/(1+z)²` -/

/-- The explicit radial multiplier `z ↦ 2z/(1+z)²` of the two star-terms. -/
def twoZ (z : ℝ) : ℝ := 2 * z / (1 + z) ^ 2

/-- The `Zop`-iterates of `c·twoZ` are uniformly bounded for `|c| ≤ 1`. -/
theorem zop_bound_mult : ∃ K : ℝ, 0 < K ∧ ∀ (c : ℝ), |c| ≤ 1 → ∀ b ≤ 3,
    ∀ z ∈ Set.Ioi (0 : ℝ),
      |Work.Spaces.Zop^[b] (fun z => c * twoZ z) z| ≤ K := by
  obtain ⟨K, hKpos, hK⟩ := Work.FTS.StrongPersist.L6Aux.ZslotSupBound6
  have hKfun : ∀ b ≤ 3, ∀ z ∈ Set.Ioi (0 : ℝ),
      |Work.Spaces.Zop^[b] twoZ z| ≤ K := by
    intro b hb z hz
    have hZop : Work.Spaces.Zop^[b] twoZ
        = fun z => Work.Spaces.DzIter b (fun z (_ : ℝ) => twoZ z) z 0 :=
      (Work.Spaces.Zop_slice b (fun z (_ : ℝ) => twoZ z) 0).symm
    have hsame : (fun z (_ : ℝ) => twoZ z) = fun z (_ : ℝ) => 2 * z / (1 + z) ^ 2 := by
      funext z _
      simp only [twoZ]
    rw [hZop, hsame]
    exact hK b (by omega) z (Set.mem_Ici.mpr (le_of_lt hz)) (0 : ℝ) Work.Spaces.zero_mem_Iθ
  refine ⟨K, hKpos, ?_⟩
  intro c hc b hb z hz
  have hslice : Work.Spaces.Zop^[b] (fun z => c * twoZ z)
      = fun z => c * Work.Spaces.Zop^[b] twoZ z :=
    Work.FTS.CoercivityFix.Transfer.E2pkg.Zop_iter_const_mul b c twoZ
  rw [hslice]
  calc |c * Work.Spaces.Zop^[b] twoZ z| = |c| * |Work.Spaces.Zop^[b] twoZ z| := abs_mul c _
    _ ≤ 1 * K := mul_le_mul hc (hKfun b hb z hz) (abs_nonneg _) (by norm_num)
    _ = K := one_mul K

/-- `twoZ` is `C^∞` on `(-1,∞)`. -/
theorem contDiffOn_twoZ : ContDiffOn ℝ Work.Stability.smoothOrder twoZ (Set.Ioi (-1 : ℝ)) := by
  have hfun : twoZ = fun z : ℝ => 2 * z / (1 + z) ^ 2 := by funext z; rfl
  rw [hfun]
  exact (Work.FTS.StrongPersist.L3Aux.contDiffOn_two_z_div).of_le le_top

/-- The `C^∞`-on-`(-1,∞)` multiplier `c·twoZ`. -/
theorem contDiffOn_twoZ_const_mul (c : ℝ) :
    ContDiffOn ℝ Work.Stability.smoothOrder (fun z => c * twoZ z) (Set.Ioi (-1 : ℝ)) := by
  have h := contDiffOn_twoZ.const_smul c
  simpa only [Pi.smul_apply, smul_eq_mul] using h

/-! ## The two star-terms `N₄^{sg}`, `N₅^{sg}` -/

/-- `N₄^{sg} = -(1/2)·FK(F_*)·D_θ f = -(α/2)·twoZ·D_θ f`. -/
theorem N4sg_eq (α : ℝ) (hα : 0 < α) (hα1 : α ≤ 1) (f : ℝ → ℝ → ℝ) :
    Work.FTS.Nonlin.N4sg α f
      = fun z θ => (fun z => -(α / 2) * twoZ z) z * Work.Spaces.Dth f z θ := by
  funext z θ
  simp only [Work.FTS.Nonlin.N4sg, Work.FTS.Nonlin.FK_Fstar hα hα1, twoZ]
  ring

/-- `N₅^{sg} = -sin²θ·FK(F_*)·f = ((-α)·twoZ)·(sin²θ·f)`. -/
theorem N5sg_eq (α : ℝ) (hα : 0 < α) (hα1 : α ≤ 1) (f : ℝ → ℝ → ℝ) :
    Work.FTS.Nonlin.N5sg α f
      = fun z θ => (fun z => (-α) * twoZ z) z * (Real.sin θ ^ 2 * f z θ) := by
  funext z θ
  simp only [Work.FTS.Nonlin.N5sg, Work.FTS.Nonlin.FK_Fstar hα hα1, twoZ]
  ring

/-- The constant of `HkIntegrand_zmul_le 3`. -/
theorem zmul3 : ∃ C : ℝ, 0 < C ∧ ∀ (α : ℝ) (φ : ℝ → ℝ) (K : ℝ), 0 ≤ K →
    (∀ b ≤ 3, ∀ z ∈ Set.Ioi (0 : ℝ), |Work.Spaces.Zop^[b] φ z| ≤ K) →
    ContDiffOn ℝ Work.Stability.smoothOrder φ (Set.Ioi (-1)) →
    ∀ g : ℝ → ℝ → ℝ, Work.FTS.EllipticEst.SmoothOpen g →
      (∀ z ∈ Work.Spaces.Iz, ∀ θ ∈ Work.Spaces.Iθ,
        Work.Spaces.HkIntegrand α 3 (fun z θ => φ z * g z θ) z θ
          ≤ C * (1 + K) ^ 2 * Work.Spaces.HkIntegrand α 3 g z θ) ∧
      (Work.Spaces.HkMem α 3 g →
        Work.Spaces.HkMem α 3 (fun z θ => φ z * g z θ) ∧
        Work.Spaces.HkSq α 3 (fun z θ => φ z * g z θ)
          ≤ C * (1 + K) ^ 2 * Work.Spaces.HkSq α 3 g) :=
  Work.FTS.StrongPersist.L3Aux.HkIntegrand_zmul_le 3

/-- **The `N₄^{sg}`-term is honest in `ℋ³` and bounded by `C·|f|²_{ℋ⁴}`.** -/
theorem N4sg_mem : ∃ C : ℝ, 0 < C ∧ ∀ (α : ℝ), α ∈ Set.Ioc 0 1 → ∀ (f : ℝ → ℝ → ℝ),
    Work.FTS.EllipticEst.SmoothOpen f → Work.Spaces.HkMem α 4 f →
    Work.Spaces.HkMem α 3 (Work.FTS.Nonlin.N4sg α f) ∧
      Work.Spaces.HkSq α 3 (Work.FTS.Nonlin.N4sg α f) ≤ C * Work.Spaces.HkSq α 4 f := by
  obtain ⟨C, hCpos, hC⟩ := zmul3
  obtain ⟨Kz, hKzpos, hKz⟩ := zop_bound_mult
  refine ⟨C * (1 + Kz) ^ 2, by positivity, ?_⟩
  intro α hαIoc f hsm hmem4
  obtain ⟨hα, hα1⟩ := Set.mem_Ioc.mp hαIoc
  have hc5 : |(-(α / 2))| ≤ 1 := by
    rw [abs_neg, abs_div, abs_of_pos hα, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 2),
      div_le_one (by norm_num)]
    linarith
  have hZop : ∀ b ≤ 3, ∀ z ∈ Set.Ioi (0 : ℝ),
      |Work.Spaces.Zop^[b] (fun z => (-(α / 2)) * twoZ z) z| ≤ Kz := hKz _ hc5
  have hsl := contDiffOn_twoZ_const_mul (-(α / 2))
  have hg : Work.FTS.EllipticEst.SmoothOpen (Work.Spaces.Dth f) := hsm.Dth
  have hmemD : Work.Spaces.HkMem α 3 (Work.Spaces.Dth f) := hkMem_dth_three hα hsm hmem4
  obtain ⟨hmem', hbnd⟩ := (hC α (fun z => (-(α / 2)) * twoZ z) Kz hKzpos.le hZop hsl
    (Work.Spaces.Dth f) hg).2 hmemD
  rw [N4sg_eq α hα hα1 f]
  refine ⟨hmem', ?_⟩
  have h2 : Work.Spaces.HkSq α 3 (Work.Spaces.Dth f) ≤ Work.Spaces.HkSq α 4 f :=
    Work.FTS.CoercivityStep.Norm.HkSq_Dth_le α hα 3 hmem4
  calc Work.Spaces.HkSq α 3
        (fun z θ => (fun z => (-(α / 2)) * twoZ z) z * Work.Spaces.Dth f z θ)
      ≤ C * (1 + Kz) ^ 2 * Work.Spaces.HkSq α 3 (Work.Spaces.Dth f) := hbnd
    _ ≤ C * (1 + Kz) ^ 2 * Work.Spaces.HkSq α 4 f :=
        mul_le_mul_of_nonneg_left h2 (by positivity)

/-- **The `N₅^{sg}`-term is honest in `ℋ³` and bounded.** -/
theorem N5sg_mem : ∃ C : ℝ, 0 < C ∧ ∀ (α : ℝ), α ∈ Set.Ioc 0 1 → ∀ (f : ℝ → ℝ → ℝ),
    Work.FTS.EllipticEst.SmoothOpen f → Work.Spaces.HkMem α 4 f →
    Work.Spaces.HkMem α 3 (Work.FTS.Nonlin.N5sg α f) ∧
      Work.Spaces.HkSq α 3 (Work.FTS.Nonlin.N5sg α f) ≤ C * Work.Spaces.HkSq α 4 f := by
  obtain ⟨C, hCpos, hC⟩ := zmul3
  obtain ⟨Kz, hKzpos, hKz⟩ := zop_bound_mult
  obtain ⟨Cang, hCangpos, hCang⟩ := Work.Blocks.HkMul_ang_le 3
  refine ⟨C * (1 + Kz) ^ 2 * Cang, by positivity, ?_⟩
  intro α hαIoc f hsm hmem4
  obtain ⟨hα, hα1⟩ := Set.mem_Ioc.mp hαIoc
  have hc5 : |(-α)| ≤ 1 := by rw [abs_neg, abs_of_pos hα]; exact hα1
  have hZop : ∀ b ≤ 3, ∀ z ∈ Set.Ioi (0 : ℝ),
      |Work.Spaces.Zop^[b] (fun z => (-α) * twoZ z) z| ≤ Kz := hKz _ hc5
  have hsl := contDiffOn_twoZ_const_mul (-α)
  have hg : Work.FTS.EllipticEst.SmoothOpen (fun z θ => Real.sin θ ^ 2 * f z θ) := by
    have h1 : ContDiffOn ℝ Work.Stability.smoothOrder (fun p : ℝ × ℝ => Real.sin p.2 ^ 2)
        Work.FTS.EllipticEst.Q0 :=
      ((Real.contDiff_sin.comp contDiff_snd).pow 2).contDiffOn
    exact h1.mul hsm
  have hmemf3 : Work.Spaces.HkMem α 3 f :=
    Work.FTS.OpenPkg.HkMem_mono_open hsm 3 (by norm_num) hmem4
  have htri := hCang α f hα hα1 hsm
  have hmem_g : Work.Spaces.HkMem α 3 (fun z θ => Real.sin θ ^ 2 * f z θ) :=
    (htri.2.2 hmemf3).2.2.1
  have hsq_g : Work.Spaces.HkSq α 3 (fun z θ => Real.sin θ ^ 2 * f z θ)
      ≤ Cang * Work.Spaces.HkSq α 3 f := (htri.2.2 hmemf3).2.2.2
  obtain ⟨hmem', hbnd⟩ := (hC α (fun z => (-α) * twoZ z) Kz hKzpos.le hZop hsl
    (fun z θ => Real.sin θ ^ 2 * f z θ) hg).2 hmem_g
  rw [N5sg_eq α hα hα1 f]
  refine ⟨hmem', ?_⟩
  have h2 : Work.Spaces.HkSq α 3 f ≤ Work.Spaces.HkSq α 4 f :=
    Work.FTS.CoercivityStep.Norm.HkSq_mono_le α (by norm_num) hmem4
  calc Work.Spaces.HkSq α 3
        (fun z θ => (fun z => (-α) * twoZ z) z * (Real.sin θ ^ 2 * f z θ))
      ≤ C * (1 + Kz) ^ 2 * Work.Spaces.HkSq α 3 (fun z θ => Real.sin θ ^ 2 * f z θ) := hbnd
    _ ≤ C * (1 + Kz) ^ 2 * (Cang * Work.Spaces.HkSq α 3 f) :=
        mul_le_mul_of_nonneg_left hsq_g (by positivity)
    _ ≤ C * (1 + Kz) ^ 2 * (Cang * Work.Spaces.HkSq α 4 f) :=
        mul_le_mul_of_nonneg_left
          (mul_le_mul_of_nonneg_left h2 hCangpos.le) (by positivity)
    _ = C * (1 + Kz) ^ 2 * Cang * Work.Spaces.HkSq α 4 f := by ring

end Work.FTS.StrongPersist.L3Rhs.NfkAux
