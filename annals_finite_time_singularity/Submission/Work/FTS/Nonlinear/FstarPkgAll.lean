import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Basic.Real.Basic
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.FTS.StrongEps.SupPort.HardyThetaOpen
import Submission.Work.FTS.TransportS.SlotT2.supThetaIntOpen
import Submission.Work.FTS.Vocab
import Submission.Work.GalerkinFix.RegQ.HkMem_mono_Q
import Submission.Work.H2.T1Q.SupAbsThOAesm
-- ===== merged: Submission.Work.FTS.CoercivityFix.Assembly.Comm2w =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.CoercivityFix.Assembly

open Work.FTS.Galerkin (Fn)

set_option autoImplicit false

/-- **Block continuity up to order `k`**: every mixed derivative `D_z^bD_θ^a g` with
`a + b ≤ k` is continuous on the open quadrant.  This is the part of `SmoothQuad` that the
transfer defects actually have. -/
def BlocksCont (k : ℕ) (g : Fn) : Prop :=
  ∀ a b : ℕ, a + b ≤ k →
    ContinuousOn (Function.uncurry (Work.Spaces.mixed b a g)) Work.Construction.Qd

/-- **Block additivity up to order `k`**: every mixed derivative of `f₁ + f₂` with
`a + b ≤ k` splits on the open quadrant. -/
def BlocksAdd (k : ℕ) (f₁ f₂ : Fn) : Prop :=
  ∀ a b : ℕ, a + b ≤ k → ∀ z θ : ℝ, (z, θ) ∈ Work.Construction.Qd →
    Work.Spaces.mixed b a (f₁ + f₂) z θ
      = Work.Spaces.mixed b a f₁ z θ + Work.Spaces.mixed b a f₂ z θ



/-- **The weakened algebraic package.**  Same shape as `Assembly.Comm2`, but `add` takes block
continuity, block additivity and `HkMem` instead of `RegQ`. -/
structure Comm2w (α : ℝ) (n : ℕ) (IP : Fn → Fn → ℝ) : Prop where
  /-- congruence in the first argument on the open quadrant, with no membership -/
  congr : ∀ f f' g : Fn,
    (∀ z θ : ℝ, (z, θ) ∈ Work.Construction.Qd → f z θ = f' z θ) → IP f g = IP f' g
  /-- additivity in the first argument, from block continuity/block additivity and `HkMem` -/
  add : ∀ f₁ f₂ g : Fn,
    Work.Spaces.HkMem α n f₁ → Work.Spaces.HkMem α n f₂ → Work.Spaces.HkMem α n g →
    BlocksCont n f₁ → BlocksCont n f₂ → BlocksCont n g → BlocksAdd n f₁ f₂ →
    IP (f₁ + f₂) g = IP f₁ g + IP f₂ g
  /-- `D_θ` commutes with `Lhat` exactly -/
  dthC : ∀ f : Fn, Work.FTS.LocData.SmoothQuad f → ∀ z θ : ℝ,
    (z, θ) ∈ Work.Construction.Qd →
    Work.Spaces.Dth (Work.FTS.CoercivityFix.Lhat f) z θ
      = Work.FTS.CoercivityFix.Lhat (Work.Spaces.Dth f) z θ
  /-- the `D_z` commutator of `Lhat` is the explicit defect `Ê₂` -/
  dzC : ∀ f : Fn, Work.FTS.LocData.SmoothQuad f → ∀ z θ : ℝ,
    (z, θ) ∈ Work.Construction.Qd →
    Work.Spaces.Dz (Work.FTS.CoercivityFix.Lhat f) z θ
      = Work.FTS.CoercivityFix.Lhat (Work.Spaces.Dz f) z θ
        + Work.FTS.CoercivityFix.E2hat f z θ

end Work.FTS.CoercivityFix.Assembly
end
end
-- ===== merged: Submission.Work.FTS.NonlinRows.Rl1.angSupHk =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# The angular sup bound in the open class: `angSupHk`

For `f` of class `C^∞` on the open quadrant with `HkMem α 4 f` (`0 < α ≤ 1`) and for every
`z > 0`, every `θ ∈ (0,π/2)`,

  `f(z,θ)² ≤ C/(γ-1) · ∫_θ HkIntegrand α 4 f z θ'`  (`γ = gam α = 1 + α/10`),

with a universal constant `C`.  The `θ`-integral is taken at the *same* radius `z`; no radial
integration is involved.

The proof is a two-line consequence of the slicewise Agmon inequality
`Work.FTS.TransportS.SlotT2.supOpen_slice_bound` (the `b = 0` instance of the angular
`L^∞`–`L²` estimate of `Work.H2.T1Q.SliceSupOpen`, applied to the slice `θ ↦ f z θ`):

  `f(z,θ)² ≤ supOpenBfun α f 0 z = (4/π) ∫_θ (D_z^0 f)² + (200/(γ-1)) ∫_θ (∂_θ f)² sin(2θ)^{2-γ}`,

and the two block estimates `supOpen_block_z`/`supOpen_block_mixed` of the same file, which say
that each of the two integrals above — after multiplication by `w(z)² ≥ 1` — is dominated by
`∫_θ HkIntegrand α 4 f z θ`.  Since `w(z)² ≥ 1` the multiplication can be dropped, and since
`γ - 1 ≤ 1/10` the prefactor satisfies `4/π + 200/(γ-1) ≤ 201/(γ-1)`.
-/

namespace Work.FTS.NonlinRows.Rl1

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

set_option autoImplicit false
set_option maxHeartbeats 800000

/-- For `z > 0` the radial weight satisfies `w(z)² ≥ 1`. -/
private lemma w_sq_ge_one {z : ℝ} (hz : 0 < z) : 1 ≤ (Work.Spaces.w z) ^ 2 :=
  one_le_pow₀ (Work.FTS.TransportS.SlotT2.supOpen_one_le_w hz)

/-- The `D_z`-block at a fixed radius: the angular `L²`-integral of `(D_z^b f)²` is
dominated by `∫_θ HkIntegrand α 4 f z θ` (the factor `w(z)² ≥ 1` of
`supOpen_block_z` is simply dropped). -/
private lemma integral_DzIter_sq_le_Hk {α : ℝ} {f : ℝ → ℝ → ℝ} {b : ℕ}
    (hmem : Work.Spaces.HkMem α 4 f) (hb : b ≤ 4) {z : ℝ} (hz : 0 < z) :
    (∫ θ in Work.Spaces.Iθ, (Work.Spaces.DzIter b f z θ) ^ 2)
      ≤ ∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α 4 f z θ := by
  have hnn : 0 ≤ ∫ θ in Work.Spaces.Iθ, (Work.Spaces.DzIter b f z θ) ^ 2 :=
    MeasureTheory.setIntegral_nonneg measurableSet_Icc (fun θ _ => sq_nonneg _)
  calc (∫ θ in Work.Spaces.Iθ, (Work.Spaces.DzIter b f z θ) ^ 2)
      ≤ (∫ θ in Work.Spaces.Iθ, (Work.Spaces.DzIter b f z θ) ^ 2) * (Work.Spaces.w z) ^ 2 :=
        le_mul_of_one_le_right hnn (w_sq_ge_one hz)
    _ ≤ ∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α 4 f z θ :=
        Work.FTS.TransportS.SlotT2.supOpen_block_z (α := α) (f := f) (b := b) hmem hb hz

/-- The mixed block at a fixed radius: the angular integral of `(∂_θ D_z^b f)² sin(2θ)^{2-γ}`
is dominated by `∫_θ HkIntegrand α 4 f z θ` (again dropping the factor `w(z)² ≥ 1` of
`supOpen_block_mixed`). -/
private lemma integral_pth_sq_le_Hk {α : ℝ} {f : ℝ → ℝ → ℝ} {b : ℕ}
    (hF : Work.FTS.EllipticEst.SmoothOpen f) (hmem : Work.Spaces.HkMem α 4 f)
    (hα : 0 < α) (hα1 : α ≤ 1) (hb : b ≤ 3) {z : ℝ} (hz : 0 < z) :
    (∫ θ in Work.Spaces.Iθ, (Work.Spaces.pth (Work.Spaces.DzIter b f) z θ) ^ 2
        * Real.sin (2 * θ) ^ (2 - Work.Spaces.gam α))
      ≤ ∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α 4 f z θ := by
  have hnn : 0 ≤ ∫ θ in Work.Spaces.Iθ, (Work.Spaces.pth (Work.Spaces.DzIter b f) z θ) ^ 2
      * Real.sin (2 * θ) ^ (2 - Work.Spaces.gam α) :=
    MeasureTheory.setIntegral_nonneg measurableSet_Icc (fun θ hθ =>
      mul_nonneg (sq_nonneg _) (Real.rpow_nonneg (Work.Spaces.bt_sin_nonneg hθ) _))
  calc (∫ θ in Work.Spaces.Iθ, (Work.Spaces.pth (Work.Spaces.DzIter b f) z θ) ^ 2
        * Real.sin (2 * θ) ^ (2 - Work.Spaces.gam α))
      ≤ (∫ θ in Work.Spaces.Iθ, (Work.Spaces.pth (Work.Spaces.DzIter b f) z θ) ^ 2
          * Real.sin (2 * θ) ^ (2 - Work.Spaces.gam α)) * (Work.Spaces.w z) ^ 2 :=
        le_mul_of_one_le_right hnn (w_sq_ge_one hz)
    _ ≤ ∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α 4 f z θ :=
        Work.FTS.TransportS.SlotT2.supOpen_block_mixed (α := α) (f := f) (b := b)
          hF hmem hα hα1 hb hz

theorem angSupHk : ∃ C : ℝ, 0 < C ∧ ∀ (α : ℝ) (f : Work.FTS.Galerkin.Fn),
    0 < α → α ≤ 1 → Work.FTS.EllipticEst.SmoothOpen f → Work.Spaces.HkMem α 4 f →
    ∀ z θ : ℝ, 0 < z → 0 < θ → θ < Real.pi / 2 →
      (f z θ) ^ 2 ≤ C / (Work.Spaces.gam α - 1) *
        ∫ θ' in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α 4 f z θ' := by
  refine ⟨201, by norm_num, ?_⟩
  intro α f hα hα1 hF hmem z θ hz hθ0 hθ1
  have hθ : θ ∈ Set.Ioo 0 (Real.pi / 2) := ⟨hθ0, hθ1⟩
  -- `γ - 1 = α/10 ∈ (0, 1/10]`
  have hγ : 0 < Work.Spaces.gam α - 1 := by
    rw [Work.Spaces.gam_sub_one]; linarith
  have hγ10 : Work.Spaces.gam α - 1 ≤ 1 / 10 := by
    rw [Work.Spaces.gam_sub_one]; linarith
  -- nonnegativity of the `ℋ⁴`-integral
  have hHknn : 0 ≤ ∫ θ' in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α 4 f z θ' :=
    MeasureTheory.setIntegral_nonneg measurableSet_Icc
      (fun θ' _ => Work.Spaces.HkIntegrand_nonneg α 4 f z θ')
  -- the slicewise Agmon inequality at `b = 0`
  have hslice : (f z θ) ^ 2 ≤ Work.FTS.TransportS.SlotT2.supOpenBfun α f 0 z := by
    simpa using Work.FTS.TransportS.SlotT2.supOpen_slice_bound (α := α) (f := f) (b := 0)
      hF hmem hα hα1 (by norm_num) hz θ hθ
  -- the two block estimates
  have hz1 := integral_DzIter_sq_le_Hk (α := α) (f := f) (b := 0) hmem (by norm_num) hz
  have hz2 := integral_pth_sq_le_Hk (α := α) (f := f) (b := 0) hF hmem hα hα1 (by norm_num) hz
  -- the prefactor comparison `4/π + 200/(γ-1) ≤ 201/(γ-1)`
  have hpre : (4 / Real.pi + 200 / (Work.Spaces.gam α - 1))
      * (∫ θ' in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α 4 f z θ')
      ≤ 201 / (Work.Spaces.gam α - 1)
      * (∫ θ' in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α 4 f z θ') := by
    apply mul_le_mul_of_nonneg_right _ hHknn
    have hinv10 : (10 : ℝ) ≤ 1 / (Work.Spaces.gam α - 1) := by
      rw [le_div_iff₀ hγ]; linarith
    have hpi : 4 / Real.pi ≤ 1 / (Work.Spaces.gam α - 1) := by
      have hp : (4 : ℝ) / Real.pi ≤ 4 / 3 := by
        rw [div_le_div_iff₀ Real.pi_pos (by norm_num : (0 : ℝ) < 3)]
        nlinarith [Real.pi_gt_three]
      linarith
    have h201 : (201 : ℝ) / (Work.Spaces.gam α - 1)
        = 1 / (Work.Spaces.gam α - 1) + 200 / (Work.Spaces.gam α - 1) := by
      rw [← add_div]; norm_num
    rw [h201]
    linarith
  calc (f z θ) ^ 2
      ≤ Work.FTS.TransportS.SlotT2.supOpenBfun α f 0 z := hslice
    _ = (4 / Real.pi) * (∫ θ' in Work.Spaces.Iθ, (Work.Spaces.DzIter 0 f z θ') ^ 2)
          + (200 / (Work.Spaces.gam α - 1))
            * ∫ θ' in Work.Spaces.Iθ, (Work.Spaces.pth (Work.Spaces.DzIter 0 f) z θ') ^ 2
                * Real.sin (2 * θ') ^ (2 - Work.Spaces.gam α) := by
        rw [Work.FTS.TransportS.SlotT2.supOpenBfun]
    _ ≤ (4 / Real.pi) * (∫ θ' in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α 4 f z θ')
          + (200 / (Work.Spaces.gam α - 1))
            * (∫ θ' in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α 4 f z θ') :=
        add_le_add
          (mul_le_mul_of_nonneg_left hz1 (by positivity))
          (mul_le_mul_of_nonneg_left hz2 (div_nonneg (by norm_num) hγ.le))
    _ = (4 / Real.pi + 200 / (Work.Spaces.gam α - 1))
          * (∫ θ' in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α 4 f z θ') := by ring
    _ ≤ 201 / (Work.Spaces.gam α - 1)
          * (∫ θ' in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α 4 f z θ') := hpre

end

end Work.FTS.NonlinRows.Rl1
end
-- ===== merged: Submission.Work.FTS.Nonlinear.FstarPkgAll =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section
open scoped Real Topology

namespace Work.FTS.Nonlin

set_option autoImplicit false
set_option linter.unusedVariables false

/-- `F_* ∈ 𝒲^{4,∞}` with `|F_*|_{𝒲^{4,∞}} ≤ Cα`. -/
theorem Fstar_W :
    ∃ C : ℝ, 0 < C ∧ ∀ α : ℝ, 0 < α → α ≤ 1 →
      Work.Spaces.WlInfMem α 4 (Work.Construction.Fstar α) ∧
      Work.Spaces.WlInf α 4 (Work.Construction.Fstar α) ≤ C * α :=
  Work.FTS.Nonlinear.FstarPkg.Fstar_W

/-- `D_θ F_* ∈ 𝒲^{4,∞}` with `|D_θF_*|_{𝒲^{4,∞}} ≤ Cα²`. -/
theorem DthFstar_W :
    ∃ C : ℝ, 0 < C ∧ ∀ α : ℝ, 0 < α → α ≤ 1 →
      Work.Spaces.WlInfMem α 4 (Work.Spaces.Dth (Work.Construction.Fstar α)) ∧
      Work.Spaces.WlInf α 4 (Work.Spaces.Dth (Work.Construction.Fstar α)) ≤ C * α ^ 2 :=
  Work.FTS.Nonlinear.FstarPkg.DthFstar_W

/-- `D_z F_* ∈ 𝒲^{4,∞}` with `|D_zF_*|_{𝒲^{4,∞}} ≤ Cα`. -/
theorem DzFstar_W :
    ∃ C : ℝ, 0 < C ∧ ∀ α : ℝ, 0 < α → α ≤ 1 →
      Work.Spaces.WlInfMem α 4 (Work.Spaces.Dz (Work.Construction.Fstar α)) ∧
      Work.Spaces.WlInf α 4 (Work.Spaces.Dz (Work.Construction.Fstar α)) ≤ C * α :=
  Work.FTS.Nonlinear.FstarPkg.DzFstar_W


/-- `c2m·L₁₂(F_*) ∈ 𝒲^{4,∞}` with norm `≤ Cα`. -/
theorem c2m_L12Fstar_W :
    ∃ C : ℝ, 0 < C ∧ ∀ α : ℝ, 0 < α → α ≤ 1 →
      Work.Spaces.WlInfMem α 4 (fun z θ => Work.Construction.c2m θ
        * Work.Construction.L12 (Work.Construction.Fstar α) z) ∧
      Work.Spaces.WlInf α 4 (fun z θ => Work.Construction.c2m θ
        * Work.Construction.L12 (Work.Construction.Fstar α) z) ≤ C * α :=
  Work.FTS.Nonlinear.FstarPkg.c2m_L12Fstar_W

/-- The angular moment of `F_*`: `FK(F_*) = α·2z/(1+z)²` exactly. -/
theorem FK_Fstar {α z : ℝ} (hα : 0 < α) (hα1 : α ≤ 1) :
    Work.Construction.FK (Work.Construction.Fstar α) z = α * (2 * z / (1 + z) ^ 2) :=
  Work.FTS.Nonlinear.FstarPkg.FK_Fstar hα hα1

end Work.FTS.Nonlin
end
end
