import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Integral.IntegrableOn
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Mathlib.Order.CompletePartialOrder
import Submission.Work.FTS.FinalClock.HkIntegrandMulDthSmooth
import Submission.Work.FTS.GalBasis.hk_sq_api
import Submission.Work.FTS.NonlinRows.NAux3
import Submission.Work.FTS.Nonlinear.Pieces.rowsAux
import Submission.Work.FTS.OpenPkg.Pieces4
import Submission.Work.FTS.StrongEps.mixed_Jeps
import Submission.Work.FTS.StrongPersist.L3Aux.ZmulBound
import Submission.Work.FTS.StrongPersist.L3Rhs.Defs
import Submission.Work.FTS_EllLimOK.Decay.DecayTools
import Submission.Work.FTS_RegExport.RXT.Sys.hasDerivAt_mixed_theta
import Submission.Work.PhiStar.Honesty.sqrt_weight_mul_eq_of_mem_Ioo
import Submission.Work.SolutionDelivery.DatumOdd
-- ===== merged: Submission.Work.FTS.StrongPersist.L3Rhs.Assembly =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section
open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.StrongPersist.L3Rhs

open Work.FTS.Galerkin (Fn)
open Work.Spaces (HkMem HkSq HkNorm HkIntegrand)

set_option autoImplicit false
set_option linter.unusedVariables false
set_option maxHeartbeats 1600000

/-! ## Binary additivity at finite order -/

/-- **Binary additivity of `ℋᵏ` for `C^k` data on the open quadrant.**  The two terms are
membership (`HkMem_add_of_contDiffOn_le`) and the norm bound
(`HkSq_add_le_of_pointwise` + the pointwise subadditivity `HkIntegrand_add_le_domain`). -/
theorem HkMem_HkSq_add2 (α : ℝ) {k : ℕ} {f g : Fn}
    (hf : ContDiffOn ℝ k (Function.uncurry f) Work.FTS.EllipticEst.Q0)
    (hg : ContDiffOn ℝ k (Function.uncurry g) Work.FTS.EllipticEst.Q0)
    (hmf : HkMem α k f) (hmg : HkMem α k g) :
    HkMem α k (fun z θ => f z θ + g z θ) ∧
      HkSq α k (fun z θ => f z θ + g z θ) ≤ 2 * HkSq α k f + 2 * HkSq α k g :=
  ⟨Work.FTS.EllipticEst.Cores.AlphaRateEstEllT.HkMem_add_of_contDiffOn_le α k hf hg hmf hmg,
    Work.FTS.EllipticEst.HkSq_add_le_of_pointwise α k hmf hmg
      (Work.FTS.EllipticEst.Cores.AlphaRateEstEllT.HkIntegrand_add_le_domain α k hf hg)⟩

/-! ## Descent in the order -/

/-- **`ℋ^{k'}`-membership descends to `ℋᵏ`** (`k ≤ k'`) as soon as the datum is `C^k` on the
open quadrant: the level-`k` integrand is a sub-sum of the level-`k'` one. -/
theorem HkMem_descend_of_contDiffOn {α : ℝ} {k k' : ℕ} (hkk : k ≤ k') {f : Fn}
    (hs : ContDiffOn ℝ k (Function.uncurry f) Work.FTS.EllipticEst.Q0) (hm : HkMem α k' f) :
    HkMem α k f :=
  Work.FTS.LocData.HkMem_of_majorant α k (f := f) (M := fun z θ => HkIntegrand α k' f z θ)
    (Work.FTS.OpenPkg.continuousOn_HkIntegrand_of_contDiffOn (F := f) α (n := k) (k := k) le_rfl hs)
    hm.1 hm.2 (fun z _ θ _ => Work.FTS.StrongPersist.HkIntegrand_le_of_le α hkk f z θ)

/-- `HkNorm α k f ≤ HkNorm α k' f` for `k ≤ k'` (from the monotonicity of `HkSq`, which needs
the `ℋ^{k'}`-honesty of `f`). -/
theorem HkNorm_descend_le {α : ℝ} {k k' : ℕ} (hkk : k ≤ k') {f : Fn} (hm : HkMem α k' f) :
    HkNorm α k f ≤ HkNorm α k' f :=
  Real.sqrt_le_sqrt (Work.FTS.StrongLWP.HkSq_mono_of_mem (α := α) hkk hm)

/-! ## The split of `N₀` on the open quadrant -/

/-- **The two-way split of `N₀`.**  On the open quadrant, `N₀ α (F_*+f) f` is the sum of its
`F_*`-only part `N0fix α` and the block `N0gSum α f` of the `f`-dependent rows.  The only
content is the additivity of `∂_θ` and of `D_z` on `F = F_* + f`, which holds because both
`F_*` and `f` are `C^∞` on the open quadrant. -/
theorem N0split {α : ℝ} {f : Fn} (hsmf : Work.FTS.EllipticEst.SmoothOpen f)
    {z θ : ℝ} (hz : 0 < z) (hθ : 0 < θ) (hθ2 : θ < π / 2) :
    Work.Construction.N0 α (Work.Construction.Ftot α f) f z θ
      = Work.FTS.Nonlin.N0fix α z θ + N0gSum α f z θ := by
  have hF : Work.FTS.EllipticEst.SmoothOpen (Work.Construction.Fstar α) :=
    Work.FTS.OpenPkg.smoothOpen_of_smoothQuad (Work.FTS.LocData.SmoothQuad_Fstar α)
  have hpth : Work.Spaces.pth (Work.Construction.Ftot α f) z θ
      = Work.Spaces.pth (Work.Construction.Fstar α) z θ + Work.Spaces.pth f z θ :=
    Work.FTS.NonlinRows.Rl1.openSlice_pth_add hF hsmf hz ⟨hθ, hθ2⟩
  have hDz : Work.Spaces.Dz (Work.Construction.Ftot α f) z θ
      = Work.Spaces.Dz (Work.Construction.Fstar α) z θ + Work.Spaces.Dz f z θ :=
    Work.FTS.Nonlinear.Pieces.Dz_add_of_diff
      (Work.FTS.NonlinRows.Rl1.openSlice_pz_add hF hsmf hz ⟨hθ, hθ2⟩)
  simp only [Work.Construction.N0, Work.FTS.Nonlin.N0fix, N0gSum,
    Work.FTS.Nonlin.N03g, Work.FTS.Nonlin.N04aF, Work.FTS.Nonlin.N04bF,
    Work.FTS.Nonlin.N05aF, Work.FTS.Nonlin.N05bF, Work.FTS.Nonlin.N06F,
    Work.Construction.N01, Work.Construction.N02, Work.Construction.N03,
    Work.Construction.N04a, Work.Construction.N04b, Work.Construction.N05a,
    Work.Construction.N05b, Work.Construction.N06]
  rw [hpth, hDz]
  ring

/-! ## Differentiability of `z ↦ L₁₂(f)(z)` -/

/-- **`z ↦ L₁₂(f)(z)` is differentiable on `(0,∞)`** for `H6Adm` data: it is `C⁵`
(`UopHk.GsingFactsInterior.contDiffOn_L12_of_smoothOpen_Hk` with `k = 6`).  This is the
input `NonlinRows.Rl1.splitOpen` asks for. -/
theorem L12_differentiableAt {α : ℝ} {f : Fn}
    (hsm : Work.FTS.EllipticEst.SmoothOpen f) (hmem : HkMem α 6 f) {z : ℝ} (hz : 0 < z) :
    DifferentiableAt ℝ (fun z' => Work.Construction.L12 f z') z := by
  have h := (Work.FTS.EllipticEst.UopHk.contDiffOn_L12_of_smoothOpen_Hk
    α 6 f hsm hmem (by norm_num)).2 z hz
  have hfun : (fun z' => Work.Construction.L12 f z') = Work.Elliptic.L12 f := rfl
  rw [hfun]
  exact h.differentiableAt

/-! ## The `mubar · AK` term -/

/-- **The `μ̄·AK` term is honest in `ℋ³` and bounded by `|μ̄|·|AK|_{ℋ³} ≤ (2 C_L C₀ + 1) C_A`.**

`AK α` is a fixed function of `α` (`HkMem α 4 (AK α)`, `HkNorm α 4 (AK α) ≤ C_A`), and the
scalar `mubar` is priced through the zero-mode bound `hL12` (the conclusion of
`L3Rhs.L3RhsL12zero`): `|μ̄| ≤ C_L(|N₀|_{ℋ⁰} + |N|_{ℋ⁰}) ≤ C_L(|N₀|_{ℋ³} + |N|_{ℋ³}) ≤ 2 C_L C₀`. -/
theorem muAK_mem (α : ℝ) (hα : 0 < α) (hα1 : α ≤ 1) {N0v Nv : Fn} {CL C0 CA : ℝ}
    (hCL : 0 ≤ CL) (hC0 : 0 ≤ C0) (hCA : 0 ≤ CA)
    (hL12 : ∀ u : Fn, HkMem α 0 u → |Work.Construction.L12 u 0| ≤ CL * HkNorm α 0 u)
    (hm0 : HkMem α 0 N0v) (hmv : HkMem α 0 Nv)
    (hN0 : HkMem α 3 N0v) (hNv : HkMem α 3 Nv)
    (hB0 : HkNorm α 3 N0v ≤ C0) (hBv : HkNorm α 3 Nv ≤ C0)
    (hAk : HkMem α 4 (Work.Construction.AK α))
    (hAkB : HkNorm α 4 (Work.Construction.AK α) ≤ CA) :
    HkMem α 3 (fun z θ => Work.Construction.mubar N0v Nv * Work.Construction.AK α z θ) ∧
      HkNorm α 3 (fun z θ => Work.Construction.mubar N0v Nv * Work.Construction.AK α z θ)
        ≤ (2 * CL * C0 + 1) * CA := by
  have hAKc4 : ContDiffOn ℝ 4 (Function.uncurry (Work.Construction.AK α))
      Work.FTS.EllipticEst.Q0 := Work.FTS.OpenPkg.contDiffOn_four_AK α hα hα1
  have hAKc3 : ContDiffOn ℝ 3 (Function.uncurry (Work.Construction.AK α))
      Work.FTS.EllipticEst.Q0 := hAKc4.of_le (by norm_num)
  have hAk3 : HkMem α 3 (Work.Construction.AK α) :=
    HkMem_descend_of_contDiffOn (k := 3) (k' := 4) (by norm_num) hAKc3 hAk
  have h1 : |Work.Construction.L12 N0v 0| ≤ CL * C0 :=
    le_trans (hL12 N0v hm0)
      (mul_le_mul_of_nonneg_left
        (le_trans (HkNorm_descend_le (α := α) (by norm_num : (0 : ℕ) ≤ 3) hN0) hB0) hCL)
  have h2 : |Work.Construction.L12 Nv 0| ≤ CL * C0 :=
    le_trans (hL12 Nv hmv)
      (mul_le_mul_of_nonneg_left
        (le_trans (HkNorm_descend_le (α := α) (by norm_num : (0 : ℕ) ≤ 3) hNv) hBv) hCL)
  have hmu : |Work.Construction.mubar N0v Nv| ≤ 2 * CL * C0 := by
    rw [Work.Construction.mubar]
    calc |Work.Construction.L12 N0v 0 + Work.Construction.L12 Nv 0|
        ≤ |Work.Construction.L12 N0v 0| + |Work.Construction.L12 Nv 0| := abs_add_le _ _
      _ ≤ CL * C0 + CL * C0 := add_le_add h1 h2
      _ = 2 * CL * C0 := by ring
  set c : ℝ := Work.Construction.mubar N0v Nv with hc
  have hcabs : |c| ≤ 2 * CL * C0 := hmu
  have hAK3 : HkNorm α 3 (Work.Construction.AK α) ≤ CA :=
    le_trans (HkNorm_descend_le (α := α) (by norm_num : 3 ≤ 4) hAk) hAkB
  have hmem : HkMem α 3 (fun z θ => c * Work.Construction.AK α z θ) :=
    Work.FTS.Nonlinear.Pieces.Rl1.HkMem_const_mul_of c hAk3
  have hnorm : HkNorm α 3 (fun z θ => c * Work.Construction.AK α z θ)
      = |c| * HkNorm α 3 (Work.Construction.AK α) := by
    rw [Work.Spaces.HkNorm, Work.Spaces.HkNorm,
      Work.FTS.Nonlinear.Pieces.RowsN0Aux.HkSq_const_mul,
      Real.sqrt_mul (by positivity : (0 : ℝ) ≤ c ^ 2), Real.sqrt_sq_eq_abs]
  refine ⟨hmem, ?_⟩
  rw [hnorm]
  have hnn : (0 : ℝ) ≤ HkNorm α 3 (Work.Construction.AK α) := Real.sqrt_nonneg _
  calc |c| * HkNorm α 3 (Work.Construction.AK α)
      ≤ (2 * CL * C0) * CA := mul_le_mul hcabs hAK3 hnn (by positivity)
    _ ≤ (2 * CL * C0 + 1) * CA := by nlinarith [hCA, hCL, hC0]

/-! ## Negation -/

/-- The `ℋ^k`-square is invariant under negation (the integrand of `-g` is that of `g`). -/
theorem HkSq_neg (α : ℝ) (k : ℕ) {g : Fn} :
    HkSq α k (fun z θ => -g z θ) = HkSq α k g := by
  simp only [Work.Spaces.HkSq]
  refine MeasureTheory.setIntegral_congr_fun measurableSet_Ici (fun z _ => ?_)
  exact MeasureTheory.setIntegral_congr_fun measurableSet_Icc
    (fun θ _ => congrFun (congrFun (Work.FTS.GalBasis.hkIntegrand_neg_fun α k g) z) θ)

theorem HkNorm_neg (α : ℝ) (k : ℕ) {g : Fn} :
    HkNorm α k (fun z θ => -g z θ) = HkNorm α k g := by
  rw [Work.Spaces.HkNorm, Work.Spaces.HkNorm, HkSq_neg]

theorem HkMem_neg (α : ℝ) (k : ℕ) {g : Fn} (hg : HkMem α k g) :
    HkMem α k (fun z θ => -g z θ) :=
  Work.FTS.GalBasis.hkMem_neg_open α k hg

end Work.FTS.StrongPersist.L3Rhs
end
end
-- ===== merged: Submission.Work.FTS.StrongPersist.L3Rhs.NfkAux.ProdRadSup =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.StrongPersist.L3Rhs.NfkAux

set_option maxHeartbeats 1600000


/-- A pointwise domination of the `ℋᵏ`-integrand on the closed quadrant, with the integrand of
`f` integrable, transfers to `HkSq` (both sides being iterated integrals). -/
private theorem hkSq_le_of_integrand_le (α : ℝ) (k : ℕ) {f g : ℝ → ℝ → ℝ} (C : ℝ)
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


end Work.FTS.StrongPersist.L3Rhs.NfkAux
end
