import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Calculus.ContDiff.Deriv
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.Order.CompletePartialOrder
import Submission.Work.FTS.Nonlinear.Pieces.RNP.GamSharpAux
import Submission.Work.FTS.OpenPkg.ProdOpen.Tools1d
import Submission.Work.FTS.StrongPersist.L3Rhs.N0gAuxDefs
import Submission.Work.FTS.TransportS.Defs
import Submission.Work.H2.T1Q.SliceIntQ
import Submission.Work.Spaces.sin_two_rpow
-- ===== merged: Submission.Work.FTS.StrongPersist.L3Rhs.L12fJetUniform =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.StrongPersist.L3Rhs

open MeasureTheory Set Filter
open scoped Real Topology

set_option autoImplicit false
set_option maxHeartbeats 1600000

/-
Intended namespace: `Work.FTS.StrongPersist.L3Rhs`.
The uniform-in-`z` bound on the `Zop`-jets (`Zop φ z = z ∂_z φ z`) of the radial function
`z ↦ L₁₂(g)(z)` (`Work.Construction.L12`), of order `b ≤ 3`, by the `ℋ⁴`-norm of `g`.
Route: `Work.FTS.OpenPkg.ProdOpen.sob_z_mean` applied to `h := Zop^[b] (fun z => L₁₂ g z)`
gives `h z ^ 2 ≤ 2 (∫_1^2 h^2 + ∫_Iz (x h' x w x)^2)`; the window integral is dominated by
`∫_Iz h^2 w^2` because `1 ≤ w` on `[1,2]`, and `x h' x = Zop^[b+1] φ x`; both weighted slot
integrals are bounded by `C * HkSq α 4 g` by `Work.FTS.StrongPersist.L3Aux.L12f_slot_le`
(which needs `b + 1 ≤ 4`, `SmoothOpen g`, `HkMem α 4 g`, `L12 g 0 = 0`, `α ≤ 1`), and
`z ↦ L₁₂ g z` is `C⁴` on `(0,∞)` by `Work.FTS.EllipticEst.UopHk.contDiffOn_L12_k` with `k = 4`.
(`Work.Spaces.Zop_slice` identifies `Zop^[b] φ z` with `DzIter b (fun z _ => φ z) z 0`.)
-/
theorem L12fJetUniform : ∃ C : ℝ, 0 < C ∧ ∀ (α : ℝ), 0 < α → α ≤ 1 → ∀ g : ℝ → ℝ → ℝ,
    Work.FTS.EllipticEst.SmoothOpen g → Work.Spaces.HkMem α 4 g →
    Work.Construction.L12 g 0 = 0 → ∀ b ≤ 3, ∀ z ∈ Set.Ioi (0 : ℝ),
      |Work.Spaces.Zop^[b] (fun z => Work.Construction.L12 g z) z|
        ≤ C * Work.Spaces.HkNorm α 4 g := by
  obtain ⟨C₁, hC₁pos, hC₁⟩ := Work.FTS.StrongPersist.L3Aux.L12f_slot_le
  obtain ⟨Cz, hCzpos, hCz⟩ := Work.FTS.OpenPkg.ProdOpen.sob_z_mean
  refine ⟨Real.sqrt (2 * Cz * C₁) + 1, ?_, ?_⟩
  · have h0 : 0 ≤ Real.sqrt (2 * Cz * C₁) := Real.sqrt_nonneg _
    linarith
  · intro α hα hα1 g hO hmem hL0 b hb z hz
    have hzpos : 0 < z := hz
    -- ### smoothness of `L₁₂(g)` on `(0,∞)` and of its `Zop`-iterates
    have hCd : ContDiffOn ℝ 4 (Work.Construction.L12 g) (Set.Ioi 0) :=
      Work.FTS.EllipticEst.UopHk.contDiffOn_L12_k α 4 g hα hα1 hO hmem (by norm_num)
    have hCd1 : ContDiffOn ℝ (b + 1) (Work.Construction.L12 g) (Set.Ioi 0) :=
      hCd.of_le (by exact_mod_cast (by omega : b + 1 ≤ 4))
    have hCd_b : ContDiffOn ℝ (4 - b)
        (Work.Spaces.Zop^[b] (fun z => Work.Construction.L12 g z)) (Set.Ioi 0) :=
      Work.FTS.CoercivityFix.Transfer.E1Parts.contDiffOn_Zop_iter' b (4 - b)
        (by
          have h : b + (4 - b) = 4 := by omega
          rw [← Nat.cast_add, h]
          exact hCd)
    have hder : ∀ x : ℝ, 0 < x →
        HasDerivAt (Work.Spaces.Zop^[b] (fun z => Work.Construction.L12 g z))
          (deriv (Work.Spaces.Zop^[b] (fun z => Work.Construction.L12 g z)) x) x :=
      fun x hx => (Work.FTS.CoercivityFix.Transfer.E1Parts.differentiableAt_Zop_iter_of_contDiffOn
        (u := fun z => Work.Construction.L12 g z) (b := b) hCd1 hx).hasDerivAt
    have hcont : ContinuousOn (deriv (Work.Spaces.Zop^[b] (fun z => Work.Construction.L12 g z)))
        (Set.Ioi 0) := by
      have h1 : ((1 : ℕ) : WithTop ℕ∞) ≤ ((4 - b : ℕ) : WithTop ℕ∞) := by
        exact_mod_cast (by omega : 1 ≤ 4 - b)
      exact hCd_b.continuousOn_deriv_of_isOpen isOpen_Ioi h1
    -- ### the two weighted slot bounds, transported from `DzIter` to `Zop`
    have hslotSucc : IntegrableOn
        (fun x => (Work.Spaces.Zop^[b+1] (fun z => Work.Construction.L12 g z) x
          * Work.Spaces.w x) ^ 2) Work.Spaces.Iz ∧
        (∫ x in Work.Spaces.Iz, (Work.Spaces.Zop^[b+1] (fun z => Work.Construction.L12 g z) x
          * Work.Spaces.w x) ^ 2) ≤ C₁ * Work.Spaces.HkSq α 4 g := by
      obtain ⟨hint, hbnd⟩ := hC₁ α hα hα1 g hO hmem hL0 (b+1) (by omega)
      have heq : (fun x => (Work.Spaces.Zop^[b+1] (fun z => Work.Construction.L12 g z) x
            * Work.Spaces.w x) ^ 2)
          = (fun z => (Work.Spaces.DzIter (b+1) (fun z (_ : ℝ) =>
              Work.Construction.L12 g z) z 0) ^ 2 * (Work.Spaces.w z) ^ 2) := by
        funext x
        have h := congrFun (Work.Spaces.Zop_slice (b+1)
          (fun z (_ : ℝ) => Work.Construction.L12 g z) 0) x
        rw [h]
        ring
      rw [heq]
      exact ⟨hint, hbnd⟩
    have hslotB : IntegrableOn
        (fun x => (Work.Spaces.Zop^[b] (fun z => Work.Construction.L12 g z) x
          * Work.Spaces.w x) ^ 2) Work.Spaces.Iz ∧
        (∫ x in Work.Spaces.Iz, (Work.Spaces.Zop^[b] (fun z => Work.Construction.L12 g z) x
          * Work.Spaces.w x) ^ 2) ≤ C₁ * Work.Spaces.HkSq α 4 g := by
      obtain ⟨hint, hbnd⟩ := hC₁ α hα hα1 g hO hmem hL0 b (by omega)
      have heq : (fun x => (Work.Spaces.Zop^[b] (fun z => Work.Construction.L12 g z) x
            * Work.Spaces.w x) ^ 2)
          = (fun z => (Work.Spaces.DzIter b (fun z (_ : ℝ) =>
              Work.Construction.L12 g z) z 0) ^ 2 * (Work.Spaces.w z) ^ 2) := by
        funext x
        have h := congrFun (Work.Spaces.Zop_slice b
          (fun z (_ : ℝ) => Work.Construction.L12 g z) 0) x
        rw [h]
        ring
      rw [heq]
      exact ⟨hint, hbnd⟩
    -- ### `x ∂_z (Zop^[b] φ) x = Zop^[b+1] φ x`, so the integrand of `sob_z_mean` is the slot
    have heq2 : (fun x => (x * deriv (Work.Spaces.Zop^[b]
            (fun z => Work.Construction.L12 g z)) x * Work.Spaces.w x) ^ 2)
        = (fun x => (Work.Spaces.Zop^[b+1] (fun z => Work.Construction.L12 g z) x
          * Work.Spaces.w x) ^ 2) := by
      funext x
      rw [show x * deriv (Work.Spaces.Zop^[b] (fun z => Work.Construction.L12 g z)) x
          = Work.Spaces.Zop^[b+1] (fun z => Work.Construction.L12 g z) x from by
        rw [Function.iterate_succ_apply']; rfl]
    -- ### the radial Sobolev inequality with a mean term
    have hsob := hCz (Work.Spaces.Zop^[b] (fun z => Work.Construction.L12 g z))
      (deriv (Work.Spaces.Zop^[b] (fun z => Work.Construction.L12 g z))) z hzpos hder hcont
      (by rw [heq2]; exact hslotSucc.1)
    rw [heq2] at hsob
    have hHnn : 0 ≤ Work.Spaces.HkSq α 4 g := Work.Spaces.HkSq_nonneg α 4 g
    -- ### the window term, dominated by the weighted slot
    have hwin : (∫ x in (1 : ℝ)..2,
        (Work.Spaces.Zop^[b] (fun z => Work.Construction.L12 g z) x) ^ 2)
        ≤ C₁ * Work.Spaces.HkSq α 4 g :=
      le_trans (window_le_slot hslotB.1) hslotB.2
    have hsq : (Work.Spaces.Zop^[b] (fun z => Work.Construction.L12 g z) z) ^ 2
        ≤ 2 * Cz * C₁ * Work.Spaces.HkSq α 4 g := by
      nlinarith [hsob, hwin, hslotSucc.2, hCzpos.le, hC₁pos.le, hHnn]
    -- ### take square roots
    have hCn : 0 ≤ 2 * Cz * C₁ := by positivity
    have hsqrt : |Work.Spaces.Zop^[b] (fun z => Work.Construction.L12 g z) z|
        ≤ Real.sqrt (2 * Cz * C₁) * Work.Spaces.HkNorm α 4 g := by
      calc |Work.Spaces.Zop^[b] (fun z => Work.Construction.L12 g z) z|
          = Real.sqrt ((Work.Spaces.Zop^[b] (fun z => Work.Construction.L12 g z) z) ^ 2) :=
            (Real.sqrt_sq_eq_abs _).symm
        _ ≤ Real.sqrt (2 * Cz * C₁ * Work.Spaces.HkSq α 4 g) := Real.sqrt_le_sqrt hsq
        _ = Real.sqrt (2 * Cz * C₁) * Real.sqrt (Work.Spaces.HkSq α 4 g) := Real.sqrt_mul hCn _
        _ = Real.sqrt (2 * Cz * C₁) * Work.Spaces.HkNorm α 4 g := rfl
    have hNnn : 0 ≤ Work.Spaces.HkNorm α 4 g := Real.sqrt_nonneg _
    calc |Work.Spaces.Zop^[b] (fun z => Work.Construction.L12 g z) z|
        ≤ Real.sqrt (2 * Cz * C₁) * Work.Spaces.HkNorm α 4 g := hsqrt
      _ ≤ (Real.sqrt (2 * Cz * C₁) + 1) * Work.Spaces.HkNorm α 4 g := by
          nlinarith [Real.sqrt_nonneg (2 * Cz * C₁)]

end Work.FTS.StrongPersist.L3Rhs
end
-- ===== merged: Submission.Work.FTS.StrongPersist.L3Rhs.VfsSep =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.StrongPersist.L3Rhs

/-
Intended namespace: `Work.FTS.StrongPersist.L3Rhs`.
The separation of variables of the star part `Vfs α` of `Bf α f`:
`Vfs α z θ = VfsA1 α θ · VfsRad z + VfsA2 α θ · VfsRadZ z`
where (`N0gAuxDefs`) `Vfs α = fun z θ => (3/(2α)) * sin 2θ * pth (F_* α) z θ
- c₂(θ) * Dz (F_* α) z θ` with `F_* α = Work.Construction.Fstar α`,
`VfsRad z = 2z/(1+z)²`, `VfsRadZ z = Zop VfsRad z = z ∂_z VfsRad z`,
`VfsA1 α θ = (3/2) * dthU (VfsGc α) θ`, `VfsA2 α θ = -α * c₂(θ) * VfsGc α θ`,
`VfsGc α θ = Γ(α,θ)/c(α)`, `dthU ψ θ = sin 2θ * deriv ψ θ`.
Route: `F_* α z θ' = (α * VfsRad z) * VfsGc α θ'` and
`F_* α z' θ = (α * VfsGc α θ) * VfsRad z'` (definition of `Work.Construction.Fstar`), so
`pth (F_* α) z θ = (α * VfsRad z) * deriv (VfsGc α) θ` and
`Dz (F_* α) z θ = (α * VfsGc α θ) * (Zop VfsRad z)` (`deriv_const_mul_field`, definitions of
`pth`, `Dz`, `Zop`); the first summand then is
`(3/(2α)) * sin 2θ * α * VfsRad z * deriv (VfsGc α) θ = (3/2) * VfsRad z * dthU (VfsGc α) θ`
and the second is `-c₂(θ) * α * VfsGc α θ * VfsRadZ z`.  (`α ≠ 0` is available from the
caller as `0 < α ≤ 1`; it is also fine to prove the identity unconditionally.)
-/

/-! ## The two partial derivatives of the profile `F_*`

The profile factors as `F_*(z,θ) = (α·VfsRad z)·VfsGc α θ`; since `VfsRad` does not depend on
`θ` and `VfsGc` does not depend on `z`, both partial derivatives separate.  The identities below
are `deriv_const_mul_field`, valid for every `α` (including `α = 0`, where both sides vanish). -/

/-- The `θ`-derivative of the profile factors through `VfsRad`. -/
theorem pth_Fstar_sep (α z θ : ℝ) :
    Work.Spaces.pth (Work.Construction.Fstar α) z θ
      = (α * VfsRad z) * deriv (VfsGc α) θ := by
  have hfun : (fun θ' : ℝ => Work.Construction.Fstar α z θ')
      = fun θ' => (α * VfsRad z) * VfsGc α θ' := by
    funext θ'
    simp only [Work.Construction.Fstar, VfsGc, VfsRad, Work.FM.Fstar]
    ring
  rw [Work.Spaces.pth, hfun, deriv_const_mul_field]

/-- The `D_z`-derivative of the profile factors through `VfsGc`. -/
theorem Dz_Fstar_sep (α z θ : ℝ) :
    Work.Spaces.Dz (Work.Construction.Fstar α) z θ
      = (α * VfsGc α θ) * VfsRadZ z := by
  have hfun : (fun z' : ℝ => Work.Construction.Fstar α z' θ)
      = fun z' => (α * VfsGc α θ) * VfsRad z' := by
    funext z'
    simp only [Work.Construction.Fstar, VfsGc, VfsRad, Work.FM.Fstar]
  rw [Work.Spaces.Dz, Work.Spaces.pz, hfun, deriv_const_mul_field]
  simp only [VfsRadZ, Work.Spaces.Zop]
  ring

/-- At `α = 0` the angular profile `VfsGc 0 = Γ(0,·)/c(0)` is the constant `1/c(0)`, since
`Γ(0,θ) = (sin θ cos²θ)^0 = 1`; in particular its derivative vanishes. -/
theorem deriv_VfsGc_zero (θ : ℝ) : deriv (VfsGc 0) θ = 0 := by
  have hGc : VfsGc 0 = fun _ : ℝ => 1 / Work.Spaces.c 0 := by
    funext t
    simp [VfsGc, Work.Spaces.Gam]
  rw [hGc, deriv_const]

theorem VfsSep (α : ℝ) (z θ : ℝ) :
    Vfs α z θ = VfsA1 α θ * VfsRad z + VfsA2 α θ * VfsRadZ z := by
  rcases eq_or_ne α 0 with hα | hα
  · subst hα
    rw [Vfs, pth_Fstar_sep, Dz_Fstar_sep, VfsA1, VfsA2, Work.Spaces.dthU, deriv_VfsGc_zero]
    ring
  · rw [Vfs, pth_Fstar_sep, Dz_Fstar_sep, VfsA1, VfsA2, Work.Spaces.dthU,
      Work.Construction.s2]
    field_simp
    ring

end Work.FTS.StrongPersist.L3Rhs
end
