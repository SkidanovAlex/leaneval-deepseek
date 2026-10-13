import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Submission.Work.FTS.StrongPersist.H6Pair6Aux.T6Coef.Defs
import Submission.Work.FTS.StrongPersist.SupOpenH2
import Submission.Work.FTS.StrongPersist.Clauses
import Submission.Work.FTS.StrongLWP.Basic
import Submission.Work.FTS.IPGen.OpenBasic

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.StrongPersist.H6Pair6Aux.T6Coef

open scoped Real Topology

set_option autoImplicit false

/-- `x ≤ (1+x)^3` for `x ≥ 0`. -/
theorem cP_le_one_add_cube {x : ℝ} (hx : 0 ≤ x) : x ≤ (1 + x) ^ 3 := by
  have hb : (1 : ℝ) ≤ 1 + x := by linarith
  calc x ≤ 1 + x := by linarith
    _ = (1 + x) ^ 1 := by ring
    _ ≤ (1 + x) ^ 3 := pow_le_pow_right₀ hb (by norm_num)

/-- `α^{-1/2} ≤ α^{-10}` for `0 < α ≤ 1`. -/
theorem cP_rpow_half_le {α : ℝ} (hα : 0 < α) (hα1 : α ≤ 1) :
    α ^ (-(1 / 2 : ℝ)) ≤ α ^ (-(10 : ℝ)) :=
  Real.rpow_le_rpow_of_exponent_ge hα hα1 (by norm_num)

/-- **The `CoefData` of the three perturbed residual fields, uniformly in the modulation.**

`EllPkgGo` prices the residual at level four and `EllPkgK α 6` at level six; the level-four
pricing `Xn α A ≤ Ce · Xn α f ≤ |Ce| M` is turned into the *pointwise* bound on the open
quadrant by the Agmon estimate `SupOpenH2`, and the two `HkNorm`/`HkMem` levels are read off
the two packages (`HkMem α 6` gives `HkMem α 4`-level honesty only through the packages, so
both are used). -/
theorem coefData_pert : ∃ K : ℝ, 0 < K ∧ ∀ α ∈ Set.Ioc 0 1,
    ∀ (Ce M : ℝ) (f Φg : Work.FTS.Galerkin.Fn),
      Work.FTS.VocabO.HQo α 4 f → Work.FTS.Nonlin.Xn α f ≤ M →
      Work.FTS.VocabO.EllPkgGo α Ce f Φg → Work.FTS.StrongPersist.EllPkgK α 6 Ce f Φg →
      Work.FTS.StrongPersist.H6Pair6Aux.T6Coef.CoefData α
          (Work.Construction.Rop α (Work.Construction.PhiTil α f Φg))
          (K * (1 + |Ce|) ^ 3 * α ^ (-(10 : ℝ)) * (1 + M) ^ 3) (|Ce| * M)
          (|Ce| * Work.Spaces.HkNorm α 6 f) ∧
      Work.FTS.StrongPersist.H6Pair6Aux.T6Coef.CoefData α
          (Work.Construction.Vop (Work.Construction.PhiTil α f Φg))
          (K * (1 + |Ce|) ^ 3 * α ^ (-(10 : ℝ)) * (1 + M) ^ 3) (|Ce| * M)
          (|Ce| * Work.Spaces.HkNorm α 6 f) ∧
      Work.FTS.StrongPersist.H6Pair6Aux.T6Coef.CoefData α
          (fun z θ => Work.Construction.Uop α (Work.Construction.PhiTil α f Φg) z θ
            / Work.Construction.s2 θ)
          (K * (1 + |Ce|) ^ 3 * α ^ (-(10 : ℝ)) * (1 + M) ^ 3) (|Ce| * M)
          (|Ce| * Work.Spaces.HkNorm α 6 f) := by
  obtain ⟨C, hCpos, hsup⟩ := Work.FTS.StrongPersist.SupOpenH2
  refine ⟨C + 1, by linarith, ?_⟩
  intro α hαI Ce M f Φg hHQ hXM hGo hK
  have hα : 0 < α := hαI.1
  have hα1 : α ≤ 1 := hαI.2
  have hMnn : 0 ≤ M := le_trans (Work.Spaces.HkNorm_nonneg α 4 f) hXM
  have hr : 0 ≤ α ^ (-(1 / 2 : ℝ)) := Real.rpow_nonneg hα.le _
  have hr10 : 0 ≤ α ^ (-(10 : ℝ)) := Real.rpow_nonneg hα.le _
  have hexp : α ^ (-(1 / 2 : ℝ)) ≤ α ^ (-(10 : ℝ)) := cP_rpow_half_le hα hα1
  have hZnn : 0 ≤ (1 + |Ce|) ^ 3 * (1 + M) ^ 3 := by positivity
  have hCeM : |Ce| * M ≤ (1 + |Ce|) ^ 3 * (1 + M) ^ 3 :=
    mul_le_mul (cP_le_one_add_cube (abs_nonneg Ce)) (cP_le_one_add_cube hMnn) hMnn
      (by positivity)
  -- the pointwise (Agmon) pricing of any level-four `HQo` field whose `Xn` is `≤ |Ce| M`
  have keyval : ∀ (g : Work.FTS.Galerkin.Fn), Work.FTS.VocabO.HQo α 4 g →
      Work.FTS.Nonlin.Xn α g ≤ |Ce| * M →
      ∀ z θ : ℝ, 0 < z → 0 < θ → θ < Real.pi / 2 →
        |g z θ| ≤ (C + 1) * (1 + |Ce|) ^ 3 * α ^ (-(10 : ℝ)) * (1 + M) ^ 3 := by
    intro g hQ4 hbd z θ hz hθ0 hθ1
    obtain ⟨hsm, hm4⟩ := hQ4
    have hm2 : Work.Spaces.HkMem α 2 g :=
      Work.FTS.OpenPkg.HkMem_mono_open hsm 2 (by norm_num) hm4
    have hmem : (z, θ) ∈ Work.FTS.EllipticEst.Q0 := ⟨hz, hθ0, hθ1⟩
    have hs := hsup α hα hα1 g ⟨hsm, hm2⟩ z θ hmem
    have hmono : Work.Spaces.HkNorm α 2 g ≤ Work.Spaces.HkNorm α 4 g :=
      Work.FTS.StrongLWP.HkNorm_mono_of_mem (by norm_num) hm4
    have hC1 : 0 ≤ C * α ^ (-(1 / 2 : ℝ)) := mul_nonneg hCpos.le hr
    have e1 : C * α ^ (-(1 / 2 : ℝ)) * Work.Spaces.HkNorm α 2 g
        ≤ C * α ^ (-(1 / 2 : ℝ)) * (|Ce| * M) :=
      mul_le_mul_of_nonneg_left (le_trans hmono hbd) hC1
    have e2 : C * α ^ (-(1 / 2 : ℝ)) * (|Ce| * M)
        ≤ C * α ^ (-(1 / 2 : ℝ)) * ((1 + |Ce|) ^ 3 * (1 + M) ^ 3) :=
      mul_le_mul_of_nonneg_left hCeM hC1
    have e3 : C * α ^ (-(1 / 2 : ℝ)) * ((1 + |Ce|) ^ 3 * (1 + M) ^ 3)
        ≤ C * α ^ (-(10 : ℝ)) * ((1 + |Ce|) ^ 3 * (1 + M) ^ 3) := by
      calc C * α ^ (-(1 / 2 : ℝ)) * ((1 + |Ce|) ^ 3 * (1 + M) ^ 3)
          = C * (α ^ (-(1 / 2 : ℝ)) * ((1 + |Ce|) ^ 3 * (1 + M) ^ 3)) := by ring
        _ ≤ C * (α ^ (-(10 : ℝ)) * ((1 + |Ce|) ^ 3 * (1 + M) ^ 3)) :=
              mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hexp hZnn) hCpos.le
        _ = C * α ^ (-(10 : ℝ)) * ((1 + |Ce|) ^ 3 * (1 + M) ^ 3) := by ring
    have e4 : C * α ^ (-(10 : ℝ)) * ((1 + |Ce|) ^ 3 * (1 + M) ^ 3)
        ≤ (C + 1) * α ^ (-(10 : ℝ)) * ((1 + |Ce|) ^ 3 * (1 + M) ^ 3) := by
      have h0 : 0 ≤ α ^ (-(10 : ℝ)) * ((1 + |Ce|) ^ 3 * (1 + M) ^ 3) :=
        mul_nonneg hr10 hZnn
      calc C * α ^ (-(10 : ℝ)) * ((1 + |Ce|) ^ 3 * (1 + M) ^ 3)
          = C * (α ^ (-(10 : ℝ)) * ((1 + |Ce|) ^ 3 * (1 + M) ^ 3)) := by ring
        _ ≤ (C + 1) * (α ^ (-(10 : ℝ)) * ((1 + |Ce|) ^ 3 * (1 + M) ^ 3)) :=
              mul_le_mul_of_nonneg_right (by linarith) h0
        _ = (C + 1) * α ^ (-(10 : ℝ)) * ((1 + |Ce|) ^ 3 * (1 + M) ^ 3) := by ring
    calc |g z θ| ≤ C * α ^ (-(1 / 2 : ℝ)) * Work.Spaces.HkNorm α 2 g := hs
      _ ≤ C * α ^ (-(1 / 2 : ℝ)) * (|Ce| * M) := e1
      _ ≤ C * α ^ (-(1 / 2 : ℝ)) * ((1 + |Ce|) ^ 3 * (1 + M) ^ 3) := e2
      _ ≤ C * α ^ (-(10 : ℝ)) * ((1 + |Ce|) ^ 3 * (1 + M) ^ 3) := e3
      _ ≤ (C + 1) * α ^ (-(10 : ℝ)) * ((1 + |Ce|) ^ 3 * (1 + M) ^ 3) := e4
      _ = (C + 1) * (1 + |Ce|) ^ 3 * α ^ (-(10 : ℝ)) * (1 + M) ^ 3 := by ring
  -- the level-four pricing `Xn α A ≤ |Ce| M`, from `EllPkgGo`
  have hXnR : Work.FTS.Nonlin.Xn α (Work.Construction.Rop α (Work.Construction.PhiTil α f Φg))
      ≤ |Ce| * M := by
    have hXfnn : 0 ≤ Work.FTS.Nonlin.Xn α f := Work.Spaces.HkNorm_nonneg α 4 f
    calc Work.FTS.Nonlin.Xn α (Work.Construction.Rop α (Work.Construction.PhiTil α f Φg))
        ≤ Ce * Work.FTS.Nonlin.Xn α f := hGo.R.2
      _ ≤ |Ce| * Work.FTS.Nonlin.Xn α f :=
            mul_le_mul_of_nonneg_right (le_abs_self Ce) hXfnn
      _ ≤ |Ce| * M := mul_le_mul_of_nonneg_left hXM (abs_nonneg Ce)
  have hXnU : Work.FTS.Nonlin.Xn α
      (fun z θ => Work.Construction.Uop α (Work.Construction.PhiTil α f Φg) z θ
        / Work.Construction.s2 θ) ≤ |Ce| * M := by
    have hXfnn : 0 ≤ Work.FTS.Nonlin.Xn α f := Work.Spaces.HkNorm_nonneg α 4 f
    calc Work.FTS.Nonlin.Xn α
          (fun z θ => Work.Construction.Uop α (Work.Construction.PhiTil α f Φg) z θ
            / Work.Construction.s2 θ)
        ≤ Ce * Work.FTS.Nonlin.Xn α f := hGo.U.2
      _ ≤ |Ce| * Work.FTS.Nonlin.Xn α f :=
            mul_le_mul_of_nonneg_right (le_abs_self Ce) hXfnn
      _ ≤ |Ce| * M := mul_le_mul_of_nonneg_left hXM (abs_nonneg Ce)
  have hXnV : Work.FTS.Nonlin.Xn α (Work.Construction.Vop (Work.Construction.PhiTil α f Φg))
      ≤ |Ce| * M := by
    have hXfnn : 0 ≤ Work.FTS.Nonlin.Xn α f := Work.Spaces.HkNorm_nonneg α 4 f
    calc Work.FTS.Nonlin.Xn α (Work.Construction.Vop (Work.Construction.PhiTil α f Φg))
        ≤ Ce * Work.FTS.Nonlin.Xn α f := hGo.V.2
      _ ≤ |Ce| * Work.FTS.Nonlin.Xn α f :=
            mul_le_mul_of_nonneg_right (le_abs_self Ce) hXfnn
      _ ≤ |Ce| * M := mul_le_mul_of_nonneg_left hXM (abs_nonneg Ce)
  -- the level-six pricing `HkNorm α 6 A ≤ |Ce| HkNorm α 6 f`, from `EllPkgK`
  have hN6R : Work.Spaces.HkNorm α 6 (Work.Construction.Rop α (Work.Construction.PhiTil α f Φg))
      ≤ |Ce| * Work.Spaces.HkNorm α 6 f := by
    have h6nn : 0 ≤ Work.Spaces.HkNorm α 6 f := Work.Spaces.HkNorm_nonneg α 6 f
    calc Work.Spaces.HkNorm α 6 (Work.Construction.Rop α (Work.Construction.PhiTil α f Φg))
        ≤ Ce * Work.Spaces.HkNorm α 6 f := hK.R.2
      _ ≤ |Ce| * Work.Spaces.HkNorm α 6 f :=
            mul_le_mul_of_nonneg_right (le_abs_self Ce) h6nn
  have hN6U : Work.Spaces.HkNorm α 6
      (fun z θ => Work.Construction.Uop α (Work.Construction.PhiTil α f Φg) z θ
        / Work.Construction.s2 θ) ≤ |Ce| * Work.Spaces.HkNorm α 6 f := by
    have h6nn : 0 ≤ Work.Spaces.HkNorm α 6 f := Work.Spaces.HkNorm_nonneg α 6 f
    calc Work.Spaces.HkNorm α 6
          (fun z θ => Work.Construction.Uop α (Work.Construction.PhiTil α f Φg) z θ
            / Work.Construction.s2 θ)
        ≤ Ce * Work.Spaces.HkNorm α 6 f := hK.U.2
      _ ≤ |Ce| * Work.Spaces.HkNorm α 6 f :=
            mul_le_mul_of_nonneg_right (le_abs_self Ce) h6nn
  have hN6V : Work.Spaces.HkNorm α 6 (Work.Construction.Vop (Work.Construction.PhiTil α f Φg))
      ≤ |Ce| * Work.Spaces.HkNorm α 6 f := by
    have h6nn : 0 ≤ Work.Spaces.HkNorm α 6 f := Work.Spaces.HkNorm_nonneg α 6 f
    calc Work.Spaces.HkNorm α 6 (Work.Construction.Vop (Work.Construction.PhiTil α f Φg))
        ≤ Ce * Work.Spaces.HkNorm α 6 f := hK.V.2
      _ ≤ |Ce| * Work.Spaces.HkNorm α 6 f :=
            mul_le_mul_of_nonneg_right (le_abs_self Ce) h6nn
  exact
    ⟨⟨hGo.R.1.1, hGo.R.1.2, hK.R.1.2, keyval _ hGo.R.1 hXnR, hXnR, hN6R⟩,
     ⟨hGo.V.1.1, hGo.V.1.2, hK.V.1.2, keyval _ hGo.V.1 hXnV, hXnV, hN6V⟩,
     ⟨hGo.U.1.1, hGo.U.1.2, hK.U.1.2, keyval _ hGo.U.1 hXnU, hXnU, hN6U⟩⟩

end Work.FTS.StrongPersist.H6Pair6Aux.T6Coef
