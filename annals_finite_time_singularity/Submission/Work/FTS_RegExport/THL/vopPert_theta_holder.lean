import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Submission.Work.FTS.RegExportIface.Defs
import Submission.Work.FTS_RegExport.THL.theta_holder_of_HkMem
import Submission.Work.FTS_RegExport.RXT.SysAux.pertSlot_tendsto

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS_RegExport.THL

set_option autoImplicit false

/-!
# `THL.vopPert_theta_holder` — the `θ`-Hölder modulus of the perturbation slot `𝒱(Φ̃)`

**Leaf A5v** of `THL.Leaves`.  The perturbation residual of the strong route is
`Φ̃(τ) = PhiTil (pExp α) (g(τ)) (E (g(τ)))`; its slot `𝒱(Φ̃) = Vop Φ̃` obeys a uniform `θ`-Hölder
modulus of exponent `pExp α / 20` on every horizon `[0,S]`, uniformly in the fake time and with
the radial weight `min z 1`.

**Route** (the one announced in `THL.Leaves`): the class-`C` approximants `σₙ = slice (gn n) τ`
of the `LimApprox` clause of `DynOK'` are class `C`, so `hEll` gives `EllPkgGo` for the
`σₙ`-slots, i.e. `SmoothOpen`/`HkMem` of `𝒱(Φ̃ₙ)` with the *uniform* `ℋ⁴`-norm bound
`HkNorm ≤ Ce · Xn σₙ ≤ max Ce 0 · (max C₀ 0 · (pExp α)²)` (the estimate of `v2_velPert`).
The trace-free leaf **A3** `theta_holder_of_HkMem` then converts that per-`n` `ℋ⁴`-membership into
the Hölder bound `C · min z 1 · HkNorm · |Δθ|^{pExp α/20}` (using `gam β - 1 = β/10`), and the
value of the slot passes to the limit `n → ∞` by `SysAux.pertSlot_tendsto` (order-`(0,0)` jet
convergence).  `le_of_tendsto'` closes.
-/

theorem vopPert_theta_holder {α Ce C₀ : ℝ} {Φs : Work.FTS.Galerkin.Fn}
    {E : Work.FTS.Galerkin.Fn →ₗ[ℝ] Work.FTS.Galerkin.Fn}
    (hα : 0 < α) (hα13 : α ≤ 1 / 3)
    (hEll : ∀ u : Work.FTS.Galerkin.Fn, Work.FTS.ClassC.ClassC (Work.FTS.Regularity.pExp α) u →
      Work.FTS.Final.EllPkgGo (Work.FTS.Regularity.pExp α) Ce u (E u) ∧
        Work.FTS.ClassC.EllPkgK (Work.FTS.Regularity.pExp α) 6 Ce u (E u))
    (hEL3 : Work.FTS.FinalV2.EllLimOK3 (Work.FTS.Regularity.pExp α) E)
    {g : Work.FTS.Galerkin.Fam} (hSol : Work.FTS.FinalV2.Sol (Work.FTS.Regularity.pExp α) Φs E g)
    (hOK : Work.FTS.FinalV2.DynOK' (Work.FTS.Regularity.pExp α) C₀ Φs E g) :
    ∀ S > 0, ∃ M : ℝ, 0 ≤ M ∧ ∀ τ ∈ Set.Icc (0:ℝ) S, ∀ z : ℝ, 0 < z →
      ∀ θ ∈ Set.Ioo (0:ℝ) (Real.pi / 2), ∀ θ' ∈ Set.Ioo (0:ℝ) (Real.pi / 2),
        |Work.Construction.Vop
            (Work.Construction.PhiTil (Work.FTS.Regularity.pExp α)
              (Work.FTS.Galerkin.slice g τ) (E (Work.FTS.Galerkin.slice g τ))) z θ
          - Work.Construction.Vop
            (Work.Construction.PhiTil (Work.FTS.Regularity.pExp α)
              (Work.FTS.Galerkin.slice g τ) (E (Work.FTS.Galerkin.slice g τ))) z θ'|
          ≤ M * min z 1 * |θ - θ'| ^ (Work.FTS.Regularity.pExp α / 20) := by
  intro S hS
  have hαG : 0 < Work.FTS.Regularity.pExp α := Work.FTS.Regularity.pExp_pos hα
  have hαG1 : Work.FTS.Regularity.pExp α ≤ 1 := Work.FTS.Regularity.pExp_le_one hα13
  -- **A3**, at the exponent `β = pExp α`
  obtain ⟨C, hC0, hA3⟩ := theta_holder_of_HkMem hαG hαG1
  -- the `ℋ⁴`-norm bound of the perturbation slots
  set Mc : ℝ := max Ce 0 * (max C₀ 0 * (Work.FTS.Regularity.pExp α) ^ 2) with hMc
  have hMc0 : 0 ≤ Mc :=
    mul_nonneg (le_max_right Ce 0) (mul_nonneg (le_max_right C₀ 0) (sq_nonneg _))
  -- the approximating family of the `LimApprox` clause
  obtain ⟨gn, B, L, hApprox, _hLip, hJet, _hμ⟩ := hOK.2 S hS
  refine ⟨C * Mc, mul_nonneg hC0 hMc0, ?_⟩
  intro τ hτ z hz θ hθ θ' hθ'
  -- the exponent of A3 is `pExp α / 20`
  have hexp : (Work.Spaces.gam (Work.FTS.Regularity.pExp α) - 1) / 2
      = Work.FTS.Regularity.pExp α / 20 := by
    rw [Work.Spaces.gam_sub_one]; ring
  -- the per-`n` Hölder bound, uniformly in `n` and `τ`
  have hper : ∀ n : ℕ,
      |Work.Construction.Vop
          (Work.Construction.PhiTil (Work.FTS.Regularity.pExp α)
            (Work.FTS.Galerkin.slice (gn n) τ) (E (Work.FTS.Galerkin.slice (gn n) τ))) z θ
        - Work.Construction.Vop
          (Work.Construction.PhiTil (Work.FTS.Regularity.pExp α)
            (Work.FTS.Galerkin.slice (gn n) τ) (E (Work.FTS.Galerkin.slice (gn n) τ))) z θ'|
      ≤ C * Mc * min z 1 * |θ - θ'| ^ (Work.FTS.Regularity.pExp α / 20) := by
    intro n
    obtain ⟨hCn, hXn, _⟩ := hApprox n τ hτ
    obtain ⟨hGo, _⟩ := hEll _ hCn
    -- the `ℋ⁴`-norm of the slot is at most `Mc`, uniformly in `n` and `τ`
    have hkey : Work.Spaces.HkNorm (Work.FTS.Regularity.pExp α) 4
        (Work.Construction.Vop
          (Work.Construction.PhiTil (Work.FTS.Regularity.pExp α)
            (Work.FTS.Galerkin.slice (gn n) τ) (E (Work.FTS.Galerkin.slice (gn n) τ)))) ≤ Mc := by
      have hXn0 : 0 ≤ Work.FTS.Nonlin.Xn (Work.FTS.Regularity.pExp α)
          (Work.FTS.Galerkin.slice (gn n) τ) := Work.Spaces.HkNorm_nonneg _ _ _
      have h2 : Work.FTS.Nonlin.Xn (Work.FTS.Regularity.pExp α)
          (Work.FTS.Galerkin.slice (gn n) τ) ≤ max C₀ 0 * (Work.FTS.Regularity.pExp α) ^ 2 :=
        le_trans hXn (mul_le_mul_of_nonneg_right (le_max_left C₀ 0) (sq_nonneg _))
      refine le_trans hGo.V.2 ?_
      calc Ce * Work.FTS.Nonlin.Xn (Work.FTS.Regularity.pExp α)
              (Work.FTS.Galerkin.slice (gn n) τ)
          ≤ max Ce 0 * Work.FTS.Nonlin.Xn (Work.FTS.Regularity.pExp α)
              (Work.FTS.Galerkin.slice (gn n) τ) :=
            mul_le_mul_of_nonneg_right (le_max_left Ce 0) hXn0
        _ ≤ Mc := by
            rw [hMc]
            exact mul_le_mul_of_nonneg_left h2 (le_max_right Ce 0)
    -- A3 on the approximant slot
    have h3 := hA3 (Work.Construction.Vop
        (Work.Construction.PhiTil (Work.FTS.Regularity.pExp α)
          (Work.FTS.Galerkin.slice (gn n) τ) (E (Work.FTS.Galerkin.slice (gn n) τ))))
      (hGo.V.1.1.of_le (by norm_num)) hGo.V.1.2 z hz θ hθ θ' hθ'
    rw [hexp] at h3
    have hm0 : 0 ≤ min z 1 := le_min hz.le zero_le_one
    have hrpow : 0 ≤ |θ - θ'| ^ (Work.FTS.Regularity.pExp α / 20) :=
      Real.rpow_nonneg (abs_nonneg _) _
    have hstep : C * min z 1 * Work.Spaces.HkNorm (Work.FTS.Regularity.pExp α) 4
          (Work.Construction.Vop
            (Work.Construction.PhiTil (Work.FTS.Regularity.pExp α)
              (Work.FTS.Galerkin.slice (gn n) τ) (E (Work.FTS.Galerkin.slice (gn n) τ))))
          * |θ - θ'| ^ (Work.FTS.Regularity.pExp α / 20)
        ≤ C * min z 1 * Mc * |θ - θ'| ^ (Work.FTS.Regularity.pExp α / 20) :=
      mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left hkey (mul_nonneg hC0 hm0)) hrpow
    calc _ ≤ C * min z 1 * Work.Spaces.HkNorm (Work.FTS.Regularity.pExp α) 4
            (Work.Construction.Vop
              (Work.Construction.PhiTil (Work.FTS.Regularity.pExp α)
                (Work.FTS.Galerkin.slice (gn n) τ) (E (Work.FTS.Galerkin.slice (gn n) τ))))
            * |θ - θ'| ^ (Work.FTS.Regularity.pExp α / 20) := h3
      _ ≤ C * min z 1 * Mc * |θ - θ'| ^ (Work.FTS.Regularity.pExp α / 20) := hstep
      _ = C * Mc * min z 1 * |θ - θ'| ^ (Work.FTS.Regularity.pExp α / 20) := by ring
  -- the value of the slot converges along `gn` at both angles
  have hcθ := (Work.FTS_RegExport.RXT.SysAux.pertSlot_tendsto (gn := gn) (B := B)
    hα hα13 hEll hEL3 hOK hS hApprox hJet hτ z θ hz hθ.1 hθ.2).2.1
  have hcθ' := (Work.FTS_RegExport.RXT.SysAux.pertSlot_tendsto (gn := gn) (B := B)
    hα hα13 hEll hEL3 hOK hS hApprox hJet hτ z θ' hz hθ'.1 hθ'.2).2.1
  exact le_of_tendsto' ((hcθ.sub hcθ').abs) hper

end Work.FTS_RegExport.THL
