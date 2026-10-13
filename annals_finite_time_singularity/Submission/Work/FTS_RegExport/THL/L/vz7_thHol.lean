import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds
import Mathlib.Order.CompletePartialOrder
import Submission.Work.FTS.RegExportIface.Defs
import Submission.Work.FTS_RegExport.THL.vopStar_theta_holder
import Submission.Work.FTS_RegExport.THL.vopPert_theta_holder
import Submission.Work.FTS_RegExport.THL.ropPert_theta_holder
import Submission.Work.FTS_RegExport.RXT.Sys.L12FK_family_jets
import Submission.Work.FTS_RegExport.RXT.velVanish2Aux
import Submission.Work.FTS.GalFields.RHS.SharpAux.Core
import Submission.Work.FTS_RegExport.RXT.Sys.pert_tilde_contDiffOn

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# `THL.L.vz7_thHol` — the `θ`-Hölder modulus of the transport coefficient `Vz7`

A7 of the leaf plan (`THL/Leaves.lean`), in the namespace of this file.

`Vz7 = (1−μ) + L₁₂(F(τ))·c2m + 2α𝒱(Φ̃(τ))` is a *sum*, so its `θ`-modulus is the sum of the
moduli of the three terms:

* `1−μ` is `θ`-independent;
* the middle term is `L₁₂(F(τ))(z)·(c2m θ − c2m θ')`; `c2m = (3cos 2θ − 1)/2` is `3`-Lipschitz,
  and `|L₁₂ F(τ)(z)| ≤ CL` uniformly on the horizon (`RXT.Sys.L12FK_family_jets`, from the
  `LimApprox` clause of `DynOK'` alone — this is why the middle term needs no `z`-locality);
* the last term splits over `Φ̃(τ) = Φ̃_* + Φ̃_pert` on the open quadrant
  (`RXT.v2_phiTil_split` + `RXT.v2_vop_add_at`), and the two halves are the star/perturbation
  Hölder moduli of leaves **A4v** (`THL.vopStar_theta_holder`, exponent `pExp α/5`) and **A5v**
  (`THL.vopPert_theta_holder`, exponent `pExp α/20`, with the harmless factor `min z 1 ≤ 1`).

The two exponents are unified by the elementary `rpow`-shift lemma `vz7_rpow_shift_le`
(`d^a ≤ (π/2)^{a−β} d^β` for `0 ≤ d ≤ π/2`, `0 < β ≤ a`) at `a = 1` (the `c2m` term) and at
`a = pExp α/5` (the star term).
-/

noncomputable section
open scoped Real Topology
open Set Filter

namespace Work.FTS_RegExport.THL.L

open Work.FTS.Galerkin (Fn Fam slice)

set_option autoImplicit false
set_option maxHeartbeats 1600000
-- the statement's binders `hμ`, `hSol`, `hEll` are intentionally unused by the proof
set_option linter.unusedVariables false

/-! ## §1 Two elementary one-dimensional inputs -/

/-- **The `rpow`-shift.** For a base `d` in `[0, π/2]` and exponents `0 < β ≤ a`, the larger
exponent costs only the constant `(π/2)^{a−β}`. -/
theorem vz7_rpow_shift_le {d β a : ℝ} (hd0 : 0 ≤ d) (hd : d ≤ Real.pi / 2)
    (hβ : 0 < β) (hβa : β ≤ a) :
    d ^ a ≤ (Real.pi / 2) ^ (a - β) * d ^ β := by
  rcases eq_or_lt_of_le hd0 with h | h
  · rw [← h, Real.zero_rpow (by linarith : a ≠ 0), Real.zero_rpow hβ.ne']
    positivity
  · have h1 : d ^ a = d ^ (a - β + β) := by rw [sub_add_cancel]
    rw [h1, Real.rpow_add h]
    exact mul_le_mul_of_nonneg_right (Real.rpow_le_rpow hd0 hd (by linarith))
      (Real.rpow_nonneg hd0 β)

/-- `c2m = (3cos 2θ − 1)/2` is `3`-Lipschitz. -/
theorem vz7_abs_c2m_sub_le (θ θ' : ℝ) :
    |Work.Construction.c2m θ - Work.Construction.c2m θ'| ≤ 3 * |θ - θ'| := by
  have h1 : |Real.cos (2 * θ) - Real.cos (2 * θ')| ≤ 2 * |θ - θ'| := by
    have h := Real.lipschitzWith_cos.dist_le_mul (2 * θ) (2 * θ')
    rw [Real.dist_eq, Real.dist_eq, NNReal.coe_one, one_mul] at h
    rw [show (2 : ℝ) * θ - 2 * θ' = 2 * (θ - θ') from by ring, abs_mul,
      abs_of_pos (by norm_num : (0 : ℝ) < 2)] at h
    linarith
  have h2 : Work.Construction.c2m θ - Work.Construction.c2m θ'
      = (3 / 2) * (Real.cos (2 * θ) - Real.cos (2 * θ')) := by
    rw [Work.Construction.c2m_eq_half, Work.Construction.c2m_eq_half]
    ring
  rw [h2, abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 3 / 2)]
  calc (3 / 2) * |Real.cos (2 * θ) - Real.cos (2 * θ')| ≤ (3 / 2) * (2 * |θ - θ'|) :=
        mul_le_mul_of_nonneg_left h1 (by norm_num)
    _ = 3 * |θ - θ'| := by ring

/-! ## §2 The `𝒱`-slot of `Φ̃(τ)` splits over star + perturbation -/

theorem vz7_vop_phiTil_split {α C₀ Cs : ℝ} {Φs : Fn} {E : Fn →ₗ[ℝ] Fn} {g : Fam}
    (hα : 0 < α) (hα13 : α ≤ 1 / 3)
    (hEL3 : Work.FTS.FinalV2.EllLimOK3 (Work.FTS.Regularity.pExp α) E)
    (hStar : Work.FTS.Final.StarPkgo2 (Work.FTS.Regularity.pExp α) Cs Φs)
    (hOK : Work.FTS.FinalV2.DynOK' (Work.FTS.Regularity.pExp α) C₀ Φs E g)
    {τ : ℝ} (hτ : 0 ≤ τ) :
    ∀ z θ, 0 < z → 0 < θ → θ < Real.pi / 2 →
      Work.Construction.Vop
        (Work.FTS.RegExportIface.phiTil (Work.FTS.Regularity.pExp α)
          (Work.FTS.RegExportIface.RXT.GR α g)
          (Work.FTS.RegExportIface.RXT.ΦR α Φs E g) τ) z θ
      = Work.Construction.Vop (Work.Construction.PhiTil (Work.FTS.Regularity.pExp α)
          (Work.Construction.Fstar (Work.FTS.Regularity.pExp α)) Φs) z θ
        + Work.Construction.Vop (Work.Construction.PhiTil (Work.FTS.Regularity.pExp α)
          (slice g τ) (E (slice g τ))) z θ := by
  have hαG : 0 < Work.FTS.Regularity.pExp α := Work.FTS.Regularity.pExp_pos hα
  have hαG1 : Work.FTS.Regularity.pExp α ≤ 1 := Work.FTS.Regularity.pExp_le_one hα13
  intro z θ hz hθ hθ2
  have hq : (z, θ) ∈ Work.FTS.EllipticEst.Q0 :=
    Work.FTS.EllipticEst.mem_Q0.mpr ⟨hz, hθ, hθ2⟩
  -- the pointwise split on the open quadrant
  have hpt : ∀ z' θ', 0 < z' → 0 < θ' → θ' < Real.pi / 2 →
      Work.FTS.RegExportIface.phiTil (Work.FTS.Regularity.pExp α)
          (Work.FTS.RegExportIface.RXT.GR α g)
          (Work.FTS.RegExportIface.RXT.ΦR α Φs E g) τ z' θ'
        = Work.Construction.PhiTil (Work.FTS.Regularity.pExp α)
            (Work.Construction.Fstar (Work.FTS.Regularity.pExp α)) Φs z' θ'
          + Work.Construction.PhiTil (Work.FTS.Regularity.pExp α) (slice g τ)
            (E (slice g τ)) z' θ' := by
    intro z' θ' hz' hθ' hθ'2
    exact Work.FTS_RegExport.RXT.v2_phiTil_split (C₀ := C₀) hα hα13 hOK hτ z' θ'
      (Work.FTS.EllipticEst.mem_Q0.mpr ⟨hz', hθ', hθ'2⟩)
  -- the two pieces are smooth enough to add the slots
  have h1 : ContDiffOn ℝ 1
      (Function.uncurry (Work.Construction.PhiTil (Work.FTS.Regularity.pExp α)
        (Work.Construction.Fstar (Work.FTS.Regularity.pExp α)) Φs))
      Work.FTS.EllipticEst.Q0 :=
    (Work.FTS.GalFields.RHS.Sharp.smoothOpen_PhiTil_star hαG hαG1 hStar).forall 1
  have h2 : ContDiffOn ℝ 1
      (Function.uncurry (fun z θ =>
        Work.Construction.PhiTil (Work.FTS.Regularity.pExp α) (slice g τ)
          (E (slice g τ)) z θ)) Work.FTS.EllipticEst.Q0 :=
    (Work.FTS_RegExport.RXT.Sys.pert_tilde_contDiffOn (α := α) (C₀ := C₀) hα hα13 hEL3 hOK τ
      hτ).of_le (by norm_num)
  rw [Work.FTS.GalFields.RHS.Sharp.Vop_congr_Q0 hpt z θ hz hθ hθ2,
    Work.FTS_RegExport.RXT.v2_vop_add_at h1 h2 hq]

/-! ## §3 The target -/

theorem vz7_thHol {α Ce C₀ Cs : ℝ} {Φs : Work.FTS.Galerkin.Fn}
    {E : Work.FTS.Galerkin.Fn →ₗ[ℝ] Work.FTS.Galerkin.Fn}
    (hα : 0 < α) (hα13 : α ≤ 1 / 3)
    (hEll : ∀ u : Work.FTS.Galerkin.Fn, Work.FTS.ClassC.ClassC (Work.FTS.Regularity.pExp α) u →
      Work.FTS.Final.EllPkgGo (Work.FTS.Regularity.pExp α) Ce u (E u) ∧
        Work.FTS.ClassC.EllPkgK (Work.FTS.Regularity.pExp α) 6 Ce u (E u))
    (hEL3 : Work.FTS.FinalV2.EllLimOK3 (Work.FTS.Regularity.pExp α) E)
    (hStar : Work.FTS.Final.StarPkgo2 (Work.FTS.Regularity.pExp α) Cs Φs)
    {g : Work.FTS.Galerkin.Fam} (hSol : Work.FTS.FinalV2.Sol (Work.FTS.Regularity.pExp α) Φs E g)
    (hOK : Work.FTS.FinalV2.DynOK' (Work.FTS.Regularity.pExp α) C₀ Φs E g)
    (hμ : Work.FTS.RegExportIface.ClockBd α Φs E g) :
    ∀ S > 0, Work.FTS.RegExportIface.ThHol
      (Work.FTS.RegExportIface.Vz7 (Work.FTS.Regularity.pExp α)
        (Work.FTS.Final.maxMu (Work.FTS.Regularity.pExp α) (Work.FTS.Nonlin.PsiCan Φs E g) g)
        (Work.FTS.FinalV2.gS α (Work.FTS.FinalV2.tauExt g))
        (Work.FTS.RegExportIface.psiR α Φs E (Work.FTS.FinalV2.tauExt g)))
      S (Work.FTS.Regularity.pExp α / 20) := by
  have hαG : 0 < Work.FTS.Regularity.pExp α := Work.FTS.Regularity.pExp_pos hα
  have hαG1 : Work.FTS.Regularity.pExp α ≤ 1 := Work.FTS.Regularity.pExp_le_one hα13
  have hpi : (0 : ℝ) < Real.pi / 2 := by linarith [Real.pi_pos]
  -- the star modulus (A4v)
  obtain ⟨Cv, hCv0, hA4v⟩ :=
    Work.FTS_RegExport.THL.vopStar_theta_holder (αG := Work.FTS.Regularity.pExp α) hαG hαG1 hStar
  -- the abbreviations of the interface
  have hGR : Work.FTS.FinalV2.gS α (Work.FTS.FinalV2.tauExt g)
      = Work.FTS.RegExportIface.RXT.GR α g := rfl
  have hΦR : Work.FTS.RegExportIface.psiR α Φs E (Work.FTS.FinalV2.tauExt g)
      = Work.FTS.RegExportIface.RXT.ΦR α Φs E g := rfl
  have hμR : Work.FTS.Final.maxMu (Work.FTS.Regularity.pExp α) (Work.FTS.Nonlin.PsiCan Φs E g) g
      = Work.FTS.RegExportIface.RXT.μR α Φs E g := rfl
  intro S hS
  -- the perturbation modulus (A5v) and the `L₁₂`-bound at the horizon `S`
  obtain ⟨Mp, hMp0, hA5v⟩ :=
    Work.FTS_RegExport.THL.vopPert_theta_holder hα hα13 hEll hEL3 hSol hOK S hS
  obtain ⟨CL, hCL0, -, hL12bd, -, -⟩ :=
    Work.FTS_RegExport.RXT.Sys.L12FK_family_jets (α := α) (C₀ := C₀) hα hα13 hOK.2 S hS
  -- the Hölder exponent
  set β : ℝ := Work.FTS.Regularity.pExp α / 20 with hβdef
  have hβ : 0 < β := by rw [hβdef]; linarith
  have hβ1 : β ≤ 1 := by rw [hβdef]; linarith
  have h520 : β ≤ Work.FTS.Regularity.pExp α / 5 := by rw [hβdef]; linarith
  intro z₀ hz₀
  refine ⟨CL * (3 * (Real.pi / 2) ^ (1 - β))
      + 2 * Work.FTS.Regularity.pExp α
        * (Cv * (Real.pi / 2) ^ (Work.FTS.Regularity.pExp α / 5 - β) + Mp),
    ?_, 1, one_pos, ?_⟩
  · -- nonnegativity of the constant
    exact add_nonneg
      (mul_nonneg hCL0 (mul_nonneg (by norm_num) (Real.rpow_nonneg hpi.le _)))
      (mul_nonneg (by linarith)
        (add_nonneg (mul_nonneg hCv0 (Real.rpow_nonneg hpi.le _)) hMp0))
  · intro τ hτ z hz _hzd θ hθ θ' hθ'
    have hτ0 : 0 ≤ τ := hτ.1
    rw [hGR, hΦR, hμR]
    -- the angle control
    have hΔ : |θ - θ'| ≤ Real.pi / 2 := by
      rw [abs_le]; constructor <;> linarith [hθ.1, hθ.2, hθ'.1, hθ'.2]
    have hrnn : 0 ≤ |θ - θ'| ^ β := Real.rpow_nonneg (abs_nonneg _) β
    -- the `rpow` shifts
    have hshift1 : |θ - θ'| ≤ (Real.pi / 2) ^ (1 - β) * |θ - θ'| ^ β := by
      simpa using vz7_rpow_shift_le (d := |θ - θ'|) (β := β) (a := 1) (abs_nonneg _) hΔ hβ hβ1
    have hshift5 : |θ - θ'| ^ (Work.FTS.Regularity.pExp α / 5)
        ≤ (Real.pi / 2) ^ (Work.FTS.Regularity.pExp α / 5 - β) * |θ - θ'| ^ β :=
      vz7_rpow_shift_le (abs_nonneg _) hΔ hβ h520
    -- the `c2m` factor
    have hc2m : |Work.Construction.c2m θ - Work.Construction.c2m θ'|
        ≤ 3 * ((Real.pi / 2) ^ (1 - β) * |θ - θ'| ^ β) := by
      calc |Work.Construction.c2m θ - Work.Construction.c2m θ'| ≤ 3 * |θ - θ'| :=
            vz7_abs_c2m_sub_le θ θ'
        _ ≤ 3 * ((Real.pi / 2) ^ (1 - β) * |θ - θ'| ^ β) :=
            mul_le_mul_of_nonneg_left hshift1 (by norm_num)
    -- the split of the `𝒱`-slot at the two angles
    have hsp := vz7_vop_phiTil_split (C₀ := C₀) (Cs := Cs) hα hα13 hEL3 hStar hOK hτ0
      z θ hz hθ.1 hθ.2
    have hsp' := vz7_vop_phiTil_split (C₀ := C₀) (Cs := Cs) hα hα13 hEL3 hStar hOK hτ0
      z θ' hz hθ'.1 hθ'.2
    -- the two halves of the `𝒱`-difference
    have hA := hA4v z hz θ hθ θ' hθ'
    have hB := hA5v τ hτ z hz θ hθ θ' hθ'
    have hstar : |Work.Construction.Vop (Work.Construction.PhiTil (Work.FTS.Regularity.pExp α)
            (Work.Construction.Fstar (Work.FTS.Regularity.pExp α)) Φs) z θ
          - Work.Construction.Vop (Work.Construction.PhiTil (Work.FTS.Regularity.pExp α)
            (Work.Construction.Fstar (Work.FTS.Regularity.pExp α)) Φs) z θ'|
        ≤ Cv * ((Real.pi / 2) ^ (Work.FTS.Regularity.pExp α / 5 - β) * |θ - θ'| ^ β) :=
      hA.trans (mul_le_mul_of_nonneg_left hshift5 hCv0)
    have hpert : |Work.Construction.Vop (Work.Construction.PhiTil (Work.FTS.Regularity.pExp α)
            (slice g τ) (E (slice g τ))) z θ
          - Work.Construction.Vop (Work.Construction.PhiTil (Work.FTS.Regularity.pExp α)
            (slice g τ) (E (slice g τ))) z θ'| ≤ Mp * |θ - θ'| ^ β := by
      calc _ ≤ Mp * min z 1 * |θ - θ'| ^ β := hB
        _ ≤ Mp * 1 * |θ - θ'| ^ β :=
            mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left (min_le_right _ _) hMp0) hrnn
        _ = Mp * |θ - θ'| ^ β := by ring
    have hvop : |Work.Construction.Vop
            (Work.FTS.RegExportIface.phiTil (Work.FTS.Regularity.pExp α)
              (Work.FTS.RegExportIface.RXT.GR α g)
              (Work.FTS.RegExportIface.RXT.ΦR α Φs E g) τ) z θ
          - Work.Construction.Vop
            (Work.FTS.RegExportIface.phiTil (Work.FTS.Regularity.pExp α)
              (Work.FTS.RegExportIface.RXT.GR α g)
              (Work.FTS.RegExportIface.RXT.ΦR α Φs E g) τ) z θ'|
        ≤ Cv * ((Real.pi / 2) ^ (Work.FTS.Regularity.pExp α / 5 - β) * |θ - θ'| ^ β)
          + Mp * |θ - θ'| ^ β := by
      rw [hsp, hsp']
      have heq : (Work.Construction.Vop (Work.Construction.PhiTil (Work.FTS.Regularity.pExp α)
              (Work.Construction.Fstar (Work.FTS.Regularity.pExp α)) Φs) z θ
            + Work.Construction.Vop (Work.Construction.PhiTil (Work.FTS.Regularity.pExp α)
              (slice g τ) (E (slice g τ))) z θ)
          - (Work.Construction.Vop (Work.Construction.PhiTil (Work.FTS.Regularity.pExp α)
              (Work.Construction.Fstar (Work.FTS.Regularity.pExp α)) Φs) z θ'
            + Work.Construction.Vop (Work.Construction.PhiTil (Work.FTS.Regularity.pExp α)
              (slice g τ) (E (slice g τ))) z θ')
          = (Work.Construction.Vop (Work.Construction.PhiTil (Work.FTS.Regularity.pExp α)
              (Work.Construction.Fstar (Work.FTS.Regularity.pExp α)) Φs) z θ
            - Work.Construction.Vop (Work.Construction.PhiTil (Work.FTS.Regularity.pExp α)
              (Work.Construction.Fstar (Work.FTS.Regularity.pExp α)) Φs) z θ')
            + (Work.Construction.Vop (Work.Construction.PhiTil (Work.FTS.Regularity.pExp α)
              (slice g τ) (E (slice g τ))) z θ
            - Work.Construction.Vop (Work.Construction.PhiTil (Work.FTS.Regularity.pExp α)
              (slice g τ) (E (slice g τ))) z θ') := by ring
      rw [heq]
      exact (abs_add_le _ _).trans (add_le_add hstar hpert)
    -- the two terms of `Vz7`
    have hL12 := hL12bd τ hτ z hz
    have hterm1 : |Work.Construction.L12
            (Work.Construction.Ftau (Work.FTS.Regularity.pExp α)
              (Work.FTS.RegExportIface.RXT.GR α g) τ) z
          * (Work.Construction.c2m θ - Work.Construction.c2m θ')|
        ≤ CL * (3 * ((Real.pi / 2) ^ (1 - β) * |θ - θ'| ^ β)) := by
      rw [abs_mul]
      exact mul_le_mul hL12 hc2m (abs_nonneg _) hCL0
    have hterm2 : |2 * Work.FTS.Regularity.pExp α
          * (Work.Construction.Vop
              (Work.FTS.RegExportIface.phiTil (Work.FTS.Regularity.pExp α)
                (Work.FTS.RegExportIface.RXT.GR α g)
                (Work.FTS.RegExportIface.RXT.ΦR α Φs E g) τ) z θ
            - Work.Construction.Vop
              (Work.FTS.RegExportIface.phiTil (Work.FTS.Regularity.pExp α)
                (Work.FTS.RegExportIface.RXT.GR α g)
                (Work.FTS.RegExportIface.RXT.ΦR α Φs E g) τ) z θ')|
        ≤ 2 * Work.FTS.Regularity.pExp α
          * (Cv * ((Real.pi / 2) ^ (Work.FTS.Regularity.pExp α / 5 - β) * |θ - θ'| ^ β)
            + Mp * |θ - θ'| ^ β) := by
      rw [abs_mul, abs_of_pos (by linarith : (0 : ℝ) < 2 * Work.FTS.Regularity.pExp α)]
      exact mul_le_mul_of_nonneg_left hvop (by linarith)
    -- assemble
    have hdiff : Work.FTS.RegExportIface.Vz7 (Work.FTS.Regularity.pExp α)
          (Work.FTS.RegExportIface.RXT.μR α Φs E g)
          (Work.FTS.RegExportIface.RXT.GR α g)
          (Work.FTS.RegExportIface.RXT.ΦR α Φs E g) z θ τ
        - Work.FTS.RegExportIface.Vz7 (Work.FTS.Regularity.pExp α)
          (Work.FTS.RegExportIface.RXT.μR α Φs E g)
          (Work.FTS.RegExportIface.RXT.GR α g)
          (Work.FTS.RegExportIface.RXT.ΦR α Φs E g) z θ' τ
        = Work.Construction.L12 (Work.Construction.Ftau (Work.FTS.Regularity.pExp α)
              (Work.FTS.RegExportIface.RXT.GR α g) τ) z
            * (Work.Construction.c2m θ - Work.Construction.c2m θ')
          + 2 * Work.FTS.Regularity.pExp α
            * (Work.Construction.Vop
                (Work.FTS.RegExportIface.phiTil (Work.FTS.Regularity.pExp α)
                  (Work.FTS.RegExportIface.RXT.GR α g)
                  (Work.FTS.RegExportIface.RXT.ΦR α Φs E g) τ) z θ
              - Work.Construction.Vop
                (Work.FTS.RegExportIface.phiTil (Work.FTS.Regularity.pExp α)
                  (Work.FTS.RegExportIface.RXT.GR α g)
                  (Work.FTS.RegExportIface.RXT.ΦR α Φs E g) τ) z θ') := by
      simp only [Work.FTS.RegExportIface.Vz7]
      ring
    rw [hdiff]
    calc |Work.Construction.L12 (Work.Construction.Ftau (Work.FTS.Regularity.pExp α)
              (Work.FTS.RegExportIface.RXT.GR α g) τ) z
            * (Work.Construction.c2m θ - Work.Construction.c2m θ')
          + 2 * Work.FTS.Regularity.pExp α
            * (Work.Construction.Vop
                (Work.FTS.RegExportIface.phiTil (Work.FTS.Regularity.pExp α)
                  (Work.FTS.RegExportIface.RXT.GR α g)
                  (Work.FTS.RegExportIface.RXT.ΦR α Φs E g) τ) z θ
              - Work.Construction.Vop
                (Work.FTS.RegExportIface.phiTil (Work.FTS.Regularity.pExp α)
                  (Work.FTS.RegExportIface.RXT.GR α g)
                  (Work.FTS.RegExportIface.RXT.ΦR α Φs E g) τ) z θ')|
        ≤ |Work.Construction.L12 (Work.Construction.Ftau (Work.FTS.Regularity.pExp α)
              (Work.FTS.RegExportIface.RXT.GR α g) τ) z
            * (Work.Construction.c2m θ - Work.Construction.c2m θ')|
          + |2 * Work.FTS.Regularity.pExp α
            * (Work.Construction.Vop
                (Work.FTS.RegExportIface.phiTil (Work.FTS.Regularity.pExp α)
                  (Work.FTS.RegExportIface.RXT.GR α g)
                  (Work.FTS.RegExportIface.RXT.ΦR α Φs E g) τ) z θ
              - Work.Construction.Vop
                (Work.FTS.RegExportIface.phiTil (Work.FTS.Regularity.pExp α)
                  (Work.FTS.RegExportIface.RXT.GR α g)
                  (Work.FTS.RegExportIface.RXT.ΦR α Φs E g) τ) z θ')| := abs_add_le _ _
      _ ≤ CL * (3 * ((Real.pi / 2) ^ (1 - β) * |θ - θ'| ^ β))
          + 2 * Work.FTS.Regularity.pExp α
            * (Cv * ((Real.pi / 2) ^ (Work.FTS.Regularity.pExp α / 5 - β) * |θ - θ'| ^ β)
              + Mp * |θ - θ'| ^ β) := add_le_add hterm1 hterm2
      _ = (CL * (3 * (Real.pi / 2) ^ (1 - β))
            + 2 * Work.FTS.Regularity.pExp α
              * (Cv * (Real.pi / 2) ^ (Work.FTS.Regularity.pExp α / 5 - β) + Mp))
          * |θ - θ'| ^ β := by ring

end Work.FTS_RegExport.THL.L
