import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Integral.IntegrableOn
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Mathlib.Order.CompletePartialOrder
import Submission.Work.Coercivity.slice_ibp_eta
import Submission.Work.FTS.CoercivityFix.Transfer.E2pkg.FinCalc
import Submission.Work.FTS.EllipticEst.OpenFTC.absFtcLeIntegralAbsDeriv
import Submission.Work.FTS.FinalClock.HkIntegrandMulDthSmooth
import Submission.Work.FTS.LocData.bumpZ_eq_zero_of_notMem_Icc
import Submission.Work.FTS.Nonlinear.FstarPkgAll
import Submission.Work.FTS.OpenPkg.C4Factors
import Submission.Work.FTS.StrongEps.SupPort.classC_sup_le
import Submission.Work.FTS.StrongPersist.L3Aux.HkIntegrand_zmul_le
import Submission.Work.FTS.StrongPersist.L3Aux.ZmulBound
import Submission.Work.FTS.StrongPersist.L3Rhs.Defs
import Submission.Work.FTS.StrongPersist.L3Rhs.NfkAux.ProdRadSup
import Submission.Work.FTS.StrongPersist.L6Aux.ZslotSupBound6
import Submission.Work.FTS.StrongPersist.SupZ.swap_abs
import Submission.Work.FTS_EllLimOK.Decay.DecayTools
import Submission.Work.FTS_RegExport.RXT.Sys.L12FKaux.hasDerivAt_integral_Itheta_K
import Submission.Work.H2.T1Q.T1EasyContQ
import Submission.Work.Spaces.mixed_mul_le
-- ===== merged: Submission.Work.FTS.StrongPersist.L3Rhs.NfkAux.Basic =====
section

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
end
end
-- ===== merged: Submission.Work.FTS.StrongPersist.L3Rhs.NfkAux.ProdRadSupO =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

open scoped Real

namespace Work.FTS.StrongPersist.L3Rhs.NfkAux

set_option maxHeartbeats 1600000

/-- The elementary comparison `(1 + √M)² ≤ 4(1 + M)` for `M ≥ 0`. -/
private theorem sq_one_add_sqrt_le' (M : ℝ) (hM : 0 ≤ M) :
    (1 + Real.sqrt M) ^ 2 ≤ 4 * (1 + M) := by
  nlinarith [Real.sq_sqrt hM, Real.sqrt_nonneg M, sq_nonneg (Real.sqrt M - 1 / 3)]

/-- A pointwise domination of the `ℋᵏ`-integrand on the closed quadrant, with the integrand of
`f` integrable, transfers to `HkSq` (both sides being iterated integrals). -/
private theorem hkSq_le_of_integrand_le' (α : ℝ) (k : ℕ) {f g : ℝ → ℝ → ℝ} (C : ℝ)
    (hmf : Work.Spaces.HkMem α k f)
    (hpt : ∀ z ∈ Work.Spaces.Iz, ∀ θ ∈ Work.Spaces.Iθ,
      Work.Spaces.HkIntegrand α k g z θ ≤ C * Work.Spaces.HkIntegrand α k f z θ) :
    Work.Spaces.HkSq α k g ≤ C * Work.Spaces.HkSq α k f := by
  have hinner : ∀ z ∈ Work.Spaces.Iz,
      (∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α k g z θ)
        ≤ C * (∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α k f z θ) := by
    intro z hz
    have h1 : (∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α k g z θ)
        ≤ ∫ θ in Work.Spaces.Iθ, C * Work.Spaces.HkIntegrand α k f z θ :=
      MeasureTheory.integral_mono_of_nonneg
        (μ := MeasureTheory.volume.restrict Work.Spaces.Iθ)
        (f := fun θ => Work.Spaces.HkIntegrand α k g z θ)
        (g := fun θ => C * Work.Spaces.HkIntegrand α k f z θ)
        (Filter.Eventually.of_forall fun θ => Work.Spaces.HkIntegrand_nonneg α k g z θ)
        ((hmf.1 z hz).const_mul C)
        (MeasureTheory.ae_restrict_of_forall_mem measurableSet_Icc fun θ hθ => hpt z hz θ hθ)
    rwa [MeasureTheory.integral_const_mul] at h1
  rw [Work.Spaces.HkSq, Work.Spaces.HkSq]
  have h2 : (∫ z in Work.Spaces.Iz, ∫ θ in Work.Spaces.Iθ,
        Work.Spaces.HkIntegrand α k g z θ)
      ≤ ∫ z in Work.Spaces.Iz, C * (∫ θ in Work.Spaces.Iθ,
        Work.Spaces.HkIntegrand α k f z θ) :=
    MeasureTheory.integral_mono_of_nonneg
      (μ := MeasureTheory.volume.restrict Work.Spaces.Iz)
      (f := fun z => ∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α k g z θ)
      (g := fun z => C * (∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α k f z θ))
      (Filter.Eventually.of_forall fun z =>
        MeasureTheory.integral_nonneg fun θ => Work.Spaces.HkIntegrand_nonneg α k g z θ)
      (hmf.2.const_mul C)
      (MeasureTheory.ae_restrict_of_forall_mem measurableSet_Ici fun z hz => hinner z hz)
  rwa [MeasureTheory.integral_const_mul] at h2

/-- **Multiplication of an `ℋᵏ`-datum by a radial factor with bounded `D_z`-iterates**, with the
regularity hypotheses imposed only for the *angles* `θ ∈ (0,π/2)` that occur in the domain
`ℋᵏ`-norm.

For every order `k ≥ 1` there are constants `C > 0`, `Cpow ≥ 0` such that for every `α > 0`,
every `r : ℝ → ℝ` whose iterates `D_z^a r = (z∂_z)^a r`, `a ≤ k`, are bounded by `√M` on
`(0,∞)` (and `C^a` there), and every `h` with the finite-order regularity needed by the Leibniz
rules *on the open angle interval*,
```
      r·h ∈ ℋᵏ   and   |r·h|²_{ℋᵏ} ≤ C·α^{-Cpow}·(1+M)·|h|²_{ℋᵏ}.
```
The proof is the multiplier estimate of `Work.FTS.StrongPersist.L3Aux.zmul_pt`: on the open
quadrant the Leibniz rules `Work.FTS.FinalClock.DzIter_mul_of_contDiffOn` /
`mixed_mul_of_contDiffOn` expand `D_z^i(r·h)` and `D_z^jD_θ^i(r·h)` into the `Zop`-iterates of
`r` times the corresponding derivatives of `h`; the Cauchy–Schwarz step in `zmul_pt` then gives
the pointwise domination of the integrands.  The only angles at which these expansions are
needed are the interior angles `θ ∈ (0,π/2)`, which is exactly the (weaker) hypothesis of the
present version; the boundary angles of `Iθ = [0,π/2]` cost nothing because `sin(2θ) = 0`
there and both weights on the left vanish.  The line `z = 0` is trivial (both integrands vanish
there, `Work.FTS.LocData.HkIntegrand_zero_fst`), and the honesty of the product is transferred
from `h` by `Work.FTS.LocData.HkMem_of_majorant`, using the continuity of the integrand on the
open quadrant (`blocksCont_of_contDiffOn` + `continuousOn_HkIntegrand_of_blocksCont`). -/
theorem ProdRadSupO : ∀ k : ℕ, ∃ C Cpow : ℝ, 0 < C ∧ 0 ≤ Cpow ∧
    ∀ (α : ℝ) (r : ℝ → ℝ) (h : ℝ → ℝ → ℝ) (M : ℝ),
      0 < α → 0 ≤ M → 1 ≤ k →
      (∀ (a : ℕ), a ≤ k → ∀ z ∈ Set.Ioi (0 : ℝ), (Work.Elliptic.DzdIter a r z) ^ 2 ≤ M) →
      (∀ (a : ℕ), a ≤ k → ContDiffOn ℝ a r (Set.Ioi (0 : ℝ))) →
      (∀ (i : ℕ), i ≤ k → ∀ θ ∈ Set.Ioo (0 : ℝ) (π / 2),
        ContDiffOn ℝ i (fun z => h z θ) (Set.Ioi (0 : ℝ))) →
      (∀ (j i : ℕ), 1 ≤ i → i + j ≤ k → ∀ θ ∈ Set.Ioo (0 : ℝ) (π / 2),
        ContDiffOn ℝ j (fun z => Work.Spaces.DthIter i h z θ) (Set.Ioi (0 : ℝ))) →
      ContDiffOn ℝ k (Function.uncurry h) Work.FTS.EllipticEst.Q0 →
      Work.Spaces.HkMem α k h →
      Work.Spaces.HkMem α k (fun z θ => r z * h z θ) ∧
      Work.Spaces.HkSq α k (fun z θ => r z * h z θ)
        ≤ C * α ^ (-Cpow) * (1 + M) * Work.Spaces.HkSq α k h := by
  intro k
  by_cases hk : 1 ≤ k
  · refine ⟨4 * Work.FTS.StrongPersist.L3Aux.zmulConst k, 0, ?_, le_refl 0, ?_⟩
    · have hpos := Work.FTS.StrongPersist.L3Aux.zmulConst_pos k
      linarith
    · intro α r h M hα hM hk1 hDz hra hri hrmi hsh hmem
      -- the bound on the `Zop`-iterates of the radial factor
      have hB : ∀ b ≤ k, ∀ z ∈ Set.Ioi (0 : ℝ), |Work.Spaces.Zop^[b] r z| ≤ Real.sqrt M := by
        intro b hb z hz
        rw [← Work.FTS.CoercivityFix.Transfer.E2pkg.DzdIter_eq_Zop_iter b r]
        calc |Work.Elliptic.DzdIter b r z|
            = Real.sqrt ((Work.Elliptic.DzdIter b r z) ^ 2) := (Real.sqrt_sq_eq_abs _).symm
          _ ≤ Real.sqrt M := Real.sqrt_le_sqrt (hDz b hb z hz)
      -- the pointwise bound at an interior angle (`z > 0`, `0 < θ < π/2`)
      have hpt_open : ∀ z ∈ Set.Ioi (0 : ℝ), ∀ θ ∈ Set.Ioo (0 : ℝ) (Real.pi / 2),
          Work.Spaces.HkIntegrand α k (fun z θ => r z * h z θ) z θ
            ≤ (Work.FTS.StrongPersist.L3Aux.zmulConst k * (1 + Real.sqrt M) ^ 2)
                * Work.Spaces.HkIntegrand α k h z θ := by
        intro z hz θ hθ
        refine Work.FTS.StrongPersist.L3Aux.zmul_pt α k r h (Real.sqrt_nonneg M) ?_ ?_ ?_
        · intro b hb
          exact hB b hb z hz
        · intro i hik
          exact Work.FTS.FinalClock.DzIter_mul_of_contDiffOn i r h isOpen_Ioi
            (hra i hik) (hri i hik θ hθ) z hz
        · intro j i hi hij
          exact Work.FTS.FinalClock.mixed_mul_of_contDiffOn j i r h isOpen_Ioi
            (hra j (by omega)) (hrmi j i hi hij θ hθ) z hz
      -- the pointwise bound on the closed quadrant
      have hpt : ∀ z ∈ Work.Spaces.Iz, ∀ θ ∈ Work.Spaces.Iθ,
          Work.Spaces.HkIntegrand α k (fun z θ => r z * h z θ) z θ
            ≤ (Work.FTS.StrongPersist.L3Aux.zmulConst k * (1 + Real.sqrt M) ^ 2)
                * Work.Spaces.HkIntegrand α k h z θ := by
        intro z hz θ hθ
        have hCnn : 0 ≤ Work.FTS.StrongPersist.L3Aux.zmulConst k * (1 + Real.sqrt M) ^ 2 :=
          mul_nonneg (Work.FTS.StrongPersist.L3Aux.zmulConst_pos k).le (sq_nonneg _)
        rcases eq_or_lt_of_le (show (0 : ℝ) ≤ z from hz) with h0 | hzpos
        · subst h0
          rw [Work.FTS.LocData.HkIntegrand_zero_fst]
          exact mul_nonneg hCnn (Work.Spaces.HkIntegrand_nonneg α k h 0 θ)
        · by_cases hs : Real.sin (2 * θ) = 0
          · -- a boundary angle: the `𝒲`-weight kills the integrand
            rw [Work.Coercivity.HkIntegrand_eq_zero_of_sin_eq_zero α k
              (fun z θ => r z * h z θ) z θ hs]
            exact mul_nonneg hCnn (Work.Spaces.HkIntegrand_nonneg α k h z θ)
          · -- an interior angle: the hypotheses apply
            have hθ' : θ ∈ Set.Ioo (0 : ℝ) (Real.pi / 2) := by
              refine ⟨lt_of_le_of_ne hθ.1 (fun hc => hs (by rw [← hc]; simp)), ?_⟩
              refine lt_of_le_of_ne hθ.2 (fun hc => hs (by
                rw [hc, show 2 * (Real.pi / 2) = Real.pi by ring, Real.sin_pi]))
            exact hpt_open z hzpos θ hθ'
      -- smoothness of the product and continuity of its integrand on the open quadrant
      have hFsm : ContDiffOn ℝ k (Function.uncurry (fun z θ => r z * h z θ))
          Work.FTS.EllipticEst.Q0 := by
        have hfst : ContDiffOn ℝ k (fun p : ℝ × ℝ => r p.1) Work.FTS.EllipticEst.Q0 :=
          (hra k le_rfl).comp contDiffOn_fst
            (fun p hp => (Work.FTS.EllipticEst.mem_Q0.mp hp).1)
        exact hfst.mul hsh
      have hBc : Work.FTS.CoercivityFix.Assembly.BlocksCont k (fun z θ => r z * h z θ) :=
        Work.FTS.CoercivityFix.Transfer.E2pkg.blocksCont_of_contDiffOn hFsm
      have hcont : ContinuousOn
          (fun p : ℝ × ℝ => Work.Spaces.HkIntegrand α k (fun z θ => r z * h z θ) p.1 p.2)
          (Set.Ioi 0 ×ˢ Set.Ioo 0 (Real.pi / 2)) :=
        Work.FTS.CoercivityFix.Transfer.E2pkg.continuousOn_HkIntegrand_of_blocksCont hBc α
      -- membership by domination
      have hmemProd : Work.Spaces.HkMem α k (fun z θ => r z * h z θ) := by
        refine Work.FTS.LocData.HkMem_of_majorant α k hcont ?_ ?_ hpt
        · intro z hz
          exact (hmem.1 z hz).const_mul _
        · have h2 := (hmem.2).const_mul
              (Work.FTS.StrongPersist.L3Aux.zmulConst k * (1 + Real.sqrt M) ^ 2)
          have heq : (fun z : ℝ => ∫ θ in Work.Spaces.Iθ,
                (Work.FTS.StrongPersist.L3Aux.zmulConst k * (1 + Real.sqrt M) ^ 2)
                  * Work.Spaces.HkIntegrand α k h z θ)
              = fun z : ℝ =>
                  (Work.FTS.StrongPersist.L3Aux.zmulConst k * (1 + Real.sqrt M) ^ 2)
                    * ∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α k h z θ := by
            funext z
            rw [MeasureTheory.integral_const_mul]
          rw [heq]
          exact h2
      refine ⟨hmemProd, ?_⟩
      have hsq := hkSq_le_of_integrand_le' α k
        (Work.FTS.StrongPersist.L3Aux.zmulConst k * (1 + Real.sqrt M) ^ 2) hmem hpt
      have harith : (1 + Real.sqrt M) ^ 2 ≤ 4 * (1 + M) := sq_one_add_sqrt_le' M hM
      have hcoef : Work.FTS.StrongPersist.L3Aux.zmulConst k * (1 + Real.sqrt M) ^ 2
          ≤ 4 * Work.FTS.StrongPersist.L3Aux.zmulConst k * (1 + M) := by
        calc Work.FTS.StrongPersist.L3Aux.zmulConst k * (1 + Real.sqrt M) ^ 2
            ≤ Work.FTS.StrongPersist.L3Aux.zmulConst k * (4 * (1 + M)) :=
              mul_le_mul_of_nonneg_left harith
                (Work.FTS.StrongPersist.L3Aux.zmulConst_pos k).le
          _ = 4 * Work.FTS.StrongPersist.L3Aux.zmulConst k * (1 + M) := by ring
      calc Work.Spaces.HkSq α k (fun z θ => r z * h z θ)
          ≤ (Work.FTS.StrongPersist.L3Aux.zmulConst k * (1 + Real.sqrt M) ^ 2)
              * Work.Spaces.HkSq α k h := hsq
        _ ≤ (4 * Work.FTS.StrongPersist.L3Aux.zmulConst k * (1 + M))
              * Work.Spaces.HkSq α k h :=
              mul_le_mul_of_nonneg_right hcoef (Work.Spaces.HkSq_nonneg α k h)
        _ = 4 * Work.FTS.StrongPersist.L3Aux.zmulConst k * α ^ (-(0 : ℝ)) * (1 + M)
              * Work.Spaces.HkSq α k h := by
              rw [neg_zero, Real.rpow_zero]
              ring
  · exact ⟨1, 0, one_pos, le_refl 0, fun α r h M hα hM hk1 => absurd hk1 hk⟩

end Work.FTS.StrongPersist.L3Rhs.NfkAux
end
