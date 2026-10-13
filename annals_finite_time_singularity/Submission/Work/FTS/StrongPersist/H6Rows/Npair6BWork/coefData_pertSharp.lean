import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Submission.Work.FTS.StrongPersist.Clauses
import Submission.Work.FTS.StrongPersist.SupOpenH2
import Submission.Work.FTS.StrongPersist.H6Pair6Aux.T6Coef.Defs
import Submission.Work.FTS.StrongPersist.H6Pair6Aux.T6Coef.coefData_pert
import Submission.Work.Construction.Defs

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# `coefData_pertSharp` — the `CoefData` of the perturbed residual, sharp pointwise price

`T6Coef.coefData_pert` prices the three perturbed residual fields `Rop(Φ̃_f)`,
`Uop(Φ̃_f)/sin 2θ`, `Vop(Φ̃_f)` pointwise by the *inflated* constant
`K (1+|Ce|)³ α^{-10} (1+M)³` (the losses `(1+|Ce|)³(1+M)³ ≥ |Ce| M` and `α^{-10} ≥ α^{-1/2}`
are conveniences of that lemma).  Here the pointwise slot is kept at its sharp value
`K α^{-1/2} |Ce| M`: the open-quadrant Agmon bound `SupOpenH2` gives
`|A z θ| ≤ C α^{-1/2} HkNorm α 2 A`, and the two monotonicities
`HkNorm α 2 A ≤ HkNorm α 4 A = Xn α A ≤ Ce · Xn α f ≤ |Ce| M` finish it, while the `ℋ⁶`-pricing
of `EllPkgK α 6` is transported verbatim (`HkNorm α 6 A ≤ Ce HkNorm α 6 f ≤ |Ce| HkNorm α 6 f`).
No hypothesis is used beyond what is stated.
-/

namespace Work.FTS.StrongPersist.H6Rows.Npair6BWork

theorem coefData_pertSharp : ∃ K : ℝ, 0 < K ∧ ∀ α ∈ Set.Ioc 0 1,
    ∀ (Ce M : ℝ) (f Φg : Work.FTS.Galerkin.Fn),
      Work.FTS.VocabO.HQo α 4 f → Work.FTS.Nonlin.Xn α f ≤ M →
      Work.FTS.VocabO.EllPkgGo α Ce f Φg → Work.FTS.StrongPersist.EllPkgK α 6 Ce f Φg →
      Work.FTS.StrongPersist.H6Pair6Aux.T6Coef.CoefData α
          (Work.Construction.Rop α (Work.Construction.PhiTil α f Φg))
          (K * α ^ (-(1 / 2 : ℝ)) * |Ce| * M) (|Ce| * M)
          (|Ce| * Work.Spaces.HkNorm α 6 f) ∧
      Work.FTS.StrongPersist.H6Pair6Aux.T6Coef.CoefData α
          (fun z θ => Work.Construction.Uop α (Work.Construction.PhiTil α f Φg) z θ
            / Work.Construction.s2 θ)
          (K * α ^ (-(1 / 2 : ℝ)) * |Ce| * M) (|Ce| * M)
          (|Ce| * Work.Spaces.HkNorm α 6 f) ∧
      Work.FTS.StrongPersist.H6Pair6Aux.T6Coef.CoefData α
          (Work.Construction.Vop (Work.Construction.PhiTil α f Φg))
          (K * α ^ (-(1 / 2 : ℝ)) * |Ce| * M) (|Ce| * M)
          (|Ce| * Work.Spaces.HkNorm α 6 f) := by
  obtain ⟨C, hCpos, hsup⟩ := Work.FTS.StrongPersist.SupOpenH2
  refine ⟨C + 1, by linarith, ?_⟩
  intro α hαI Ce M f Φg hHQ hXM hGo hK
  have hα : 0 < α := hαI.1
  have hα1 : α ≤ 1 := hαI.2
  have hMnn : 0 ≤ M := le_trans (Work.Spaces.HkNorm_nonneg α 4 f) hXM
  have hr : 0 ≤ α ^ (-(1 / 2 : ℝ)) := Real.rpow_nonneg hα.le _
  have hCeabs : 0 ≤ |Ce| := abs_nonneg Ce
  have hrCeM : 0 ≤ α ^ (-(1 / 2 : ℝ)) * |Ce| * M :=
    mul_nonneg (mul_nonneg hr hCeabs) hMnn
  -- the pointwise (Agmon) pricing of any level-four field whose `Xn` is `≤ |Ce| M`
  have keyval : ∀ (g : Work.FTS.Galerkin.Fn), Work.FTS.VocabO.HQo α 4 g →
      Work.FTS.Nonlin.Xn α g ≤ |Ce| * M →
      ∀ z θ : ℝ, 0 < z → 0 < θ → θ < Real.pi / 2 →
        |g z θ| ≤ (C + 1) * α ^ (-(1 / 2 : ℝ)) * |Ce| * M := by
    intro g hQ4 hbd z θ hz hθ0 hθ1
    obtain ⟨hsm, hm4⟩ := hQ4
    have hm2 : Work.Spaces.HkMem α 2 g :=
      Work.FTS.OpenPkg.HkMem_mono_open hsm 2 (by norm_num) hm4
    have hmem : (z, θ) ∈ Work.FTS.EllipticEst.Q0 :=
      Work.FTS.EllipticEst.mem_Q0.mpr ⟨hz, hθ0, hθ1⟩
    have hs := hsup α hα hα1 g ⟨hsm, hm2⟩ z θ hmem
    have hmono : Work.Spaces.HkNorm α 2 g ≤ Work.Spaces.HkNorm α 4 g :=
      Work.FTS.StrongLWP.HkNorm_mono_of_mem (by norm_num) hm4
    have hCf : 0 ≤ C * α ^ (-(1 / 2 : ℝ)) := mul_nonneg hCpos.le hr
    have h1 : C * α ^ (-(1 / 2 : ℝ)) * Work.Spaces.HkNorm α 2 g
        ≤ C * α ^ (-(1 / 2 : ℝ)) * (|Ce| * M) :=
      mul_le_mul_of_nonneg_left (le_trans hmono hbd) hCf
    have h2 : C * α ^ (-(1 / 2 : ℝ)) * (|Ce| * M)
        ≤ (C + 1) * α ^ (-(1 / 2 : ℝ)) * |Ce| * M := by
      have hstep : C * (α ^ (-(1 / 2 : ℝ)) * |Ce| * M)
          ≤ (C + 1) * (α ^ (-(1 / 2 : ℝ)) * |Ce| * M) :=
        mul_le_mul_of_nonneg_right (by linarith) hrCeM
      calc C * α ^ (-(1 / 2 : ℝ)) * (|Ce| * M)
          = C * (α ^ (-(1 / 2 : ℝ)) * |Ce| * M) := by ring
        _ ≤ (C + 1) * (α ^ (-(1 / 2 : ℝ)) * |Ce| * M) := hstep
        _ = (C + 1) * α ^ (-(1 / 2 : ℝ)) * |Ce| * M := by ring
    linarith [hs, h1, h2]
  -- the level-four pricing `Xn α A ≤ |Ce| M`, from `EllPkgGo`
  have hXnR : Work.FTS.Nonlin.Xn α (Work.Construction.Rop α (Work.Construction.PhiTil α f Φg))
      ≤ |Ce| * M := by
    have hXfnn : 0 ≤ Work.FTS.Nonlin.Xn α f := Work.Spaces.HkNorm_nonneg α 4 f
    calc Work.FTS.Nonlin.Xn α (Work.Construction.Rop α (Work.Construction.PhiTil α f Φg))
        ≤ Ce * Work.FTS.Nonlin.Xn α f := hGo.R.2
      _ ≤ |Ce| * Work.FTS.Nonlin.Xn α f :=
            mul_le_mul_of_nonneg_right (le_abs_self Ce) hXfnn
      _ ≤ |Ce| * M := mul_le_mul_of_nonneg_left hXM hCeabs
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
      _ ≤ |Ce| * M := mul_le_mul_of_nonneg_left hXM hCeabs
  have hXnV : Work.FTS.Nonlin.Xn α (Work.Construction.Vop (Work.Construction.PhiTil α f Φg))
      ≤ |Ce| * M := by
    have hXfnn : 0 ≤ Work.FTS.Nonlin.Xn α f := Work.Spaces.HkNorm_nonneg α 4 f
    calc Work.FTS.Nonlin.Xn α (Work.Construction.Vop (Work.Construction.PhiTil α f Φg))
        ≤ Ce * Work.FTS.Nonlin.Xn α f := hGo.V.2
      _ ≤ |Ce| * Work.FTS.Nonlin.Xn α f :=
            mul_le_mul_of_nonneg_right (le_abs_self Ce) hXfnn
      _ ≤ |Ce| * M := mul_le_mul_of_nonneg_left hXM hCeabs
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
     ⟨hGo.U.1.1, hGo.U.1.2, hK.U.1.2, keyval _ hGo.U.1 hXnU, hXnU, hN6U⟩,
     ⟨hGo.V.1.1, hGo.V.1.2, hK.V.1.2, keyval _ hGo.V.1 hXnV, hXnV, hN6V⟩⟩

end Work.FTS.StrongPersist.H6Rows.Npair6BWork
