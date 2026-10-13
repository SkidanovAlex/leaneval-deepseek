import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.InnerProductSpace.Basic
import Submission.Work.FTS.StrongPersist.Clauses
import Submission.Work.FTS.StrongPersist.H6Row6.nsum_split6
import Submission.Work.FTS.StrongPersist.H6Rows.Npair6BWork.nsumData
import Submission.Work.FTS.StrongEps.E4R3.Apriori4Defs

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.StrongEps.E4R3.Apriori4Proofs

open scoped Real Topology

/-- **The static level-six `N`-row is `C⁶` on the open quadrant and honest in `ℋ⁶`.**

This is the `τ`-free form of `H6Rows.Npair6BWork.nsumData`: the twenty-piece splitting
`nsplit6_pt` writes `N α (F_*+f) (Φs+Ef)` on `Qd` as the sum `nsum α f Ef Φs` of the twenty
pieces `pcs α f Ef Φs k`; each piece is `C⁶` on `Q0` and honest in `ℋ⁶` (`NS6.pieces`), and
both properties are stable under finite sums (`NS6.hkMem_sum_range`) and under a change of
values on the open quadrant (`cd6_congr` / `HkMem_congr_Qd`).

The only non-hypothesis inputs of the bundle `NS6.Data` — the `ℋ⁶`-membership of the angular
moment `FK f` and the `ℋ⁶ × ℋ⁶` product rule on the open-quadrant class — are the `α`-free
lemmas `Npair6BWork.fk_hkMem` and `Npair6BWork.hkMem_mul_of6`, so the threshold `α₂` can be
taken to be `1`. -/
theorem nMem6_of_parts {α Ce Cs : ℝ} {f Ef Φs : Work.FTS.Galerkin.Fn}
    (hα : 0 < α) (hα1 : α ≤ 1)
    (hadm : Work.FTS.StrongPersist.H6Adm α f)
    (h7 : Work.Spaces.HkMem α 7 f)
    (hEf : Work.FTS.EllipticEst.SmoothOpen Ef)
    (hΦs : Work.FTS.EllipticEst.SmoothOpen Φs)
    (hell : Work.FTS.StrongPersist.EllPkgK α 6 Ce f Ef)
    (hstar6 : Work.FTS.StrongPersist.StarPkg6 α Cs Φs) :
    ContDiffOn ℝ 6 (Function.uncurry (Work.Construction.N α (Work.Construction.Ftot α f)
      (fun z θ => Φs z θ + Ef z θ))) Work.FTS.EllipticEst.Q0 ∧
    Work.Spaces.HkMem α 6 (Work.Construction.N α (Work.Construction.Ftot α f)
      (fun z θ => Φs z θ + Ef z θ)) := by
  have hαIoc : α ∈ Set.Ioc 0 1 := ⟨hα, hα1⟩
  have hkfm : Work.Spaces.HkMem α 6 (fun z (_ : ℝ) => Work.Construction.FK f z) :=
    Work.FTS.StrongPersist.H6Rows.Npair6BWork.fk_hkMem α hαIoc f hadm.reg.1 hadm.reg.2
  have hmulSm : ∀ (u v : Work.FTS.Galerkin.Fn),
      Work.FTS.EllipticEst.SmoothOpen u → Work.Spaces.HkMem α 6 u →
      Work.FTS.EllipticEst.SmoothOpen v → Work.Spaces.HkMem α 6 v →
      Work.Spaces.HkMem α 6 (fun z θ => u z θ * v z θ) :=
    fun u v hus hum hvs hvm =>
      Work.FTS.StrongPersist.H6Rows.Npair6BWork.hkMem_mul_of6 hα hα1 ⟨hus, hum⟩ ⟨hvs, hvm⟩
  have D : Work.FTS.StrongPersist.H6Row6.NS6.Data α Ce Cs f Ef Φs :=
    { hα := hα
      hα1 := hα1
      fsm := hadm.reg.1
      fm := hadm.reg.2
      f7 := h7
      Efsm := hEf
      Φssm := hΦs
      l12 := hadm.l12
      star := hstar6
      ell := hell
      kfm := hkfm
      hadm := hadm
      mulSm := hmulSm }
  have hpcs := Work.FTS.StrongPersist.H6Row6.NS6.pieces D
  have hsum := Work.FTS.StrongPersist.H6Row6.NS6.hkMem_sum_range 20
    (Work.FTS.StrongPersist.H6Row6.pcs α f Ef Φs)
    (fun k hk => (hpcs k hk).1) (fun k hk => (hpcs k hk).2)
  -- the pointwise splitting of `N` into the twenty pieces, on the open quadrant
  have hpt : ∀ z θ : ℝ, (z, θ) ∈ Work.Construction.Qd →
      Work.Construction.N α (Work.Construction.Ftot α f)
          (fun z θ => Φs z θ + Ef z θ) z θ
        = Work.FTS.StrongPersist.H6Rows.Npair6SupAux.nsum α f Ef Φs z θ :=
    fun z θ hzθ =>
      Work.FTS.StrongPersist.H6Rows.Npair6SupAux.nsplit6_pt hα hα1 hadm hEf hΦs z θ hzθ
  refine ⟨?_, ?_⟩
  · refine hsum.1.congr (fun p hp => ?_)
    obtain ⟨z, θ⟩ := p
    show Work.Construction.N α (Work.Construction.Ftot α f)
        (fun z θ => Φs z θ + Ef z θ) z θ
      = ∑ k ∈ Finset.range 20, Work.FTS.StrongPersist.H6Row6.pcs α f Ef Φs k z θ
    rw [hpt z θ hp, Work.FTS.StrongPersist.H6Row6.pcs_sum]
    simp only [Finset.sum_apply]
  · refine Work.FTS.StrongPersist.H6Pair6Aux.HkMem_congr_Qd
      (fun z θ hzθ => (hpt z θ hzθ).symm) ?_
    rw [Work.FTS.StrongPersist.H6Row6.pcs_sum]
    exact hsum.2

theorem NMem6Parts :
    ∀ Ce : ℝ, ∃ α₂ : ℝ, 0 < α₂ ∧ α₂ ≤ 1 ∧ ∀ α ∈ Set.Ioc 0 α₂,
    ∀ {f Ef Φs : Work.FTS.Galerkin.Fn} {Cs : ℝ},
    Work.FTS.StrongPersist.H6Adm α f →
    Work.Spaces.HkMem α 7 f →
    Work.FTS.EllipticEst.SmoothOpen Ef →
    Work.FTS.EllipticEst.SmoothOpen Φs →
    Work.FTS.StrongPersist.EllPkgK α 6 Ce f Ef →
    Work.FTS.StrongPersist.StarPkg6 α Cs Φs →
    ContDiffOn ℝ 6 (Function.uncurry (Work.Construction.N α (Work.Construction.Ftot α f)
      (fun z θ => Φs z θ + Ef z θ))) Work.FTS.EllipticEst.Q0 ∧
    Work.Spaces.HkMem α 6 (Work.Construction.N α (Work.Construction.Ftot α f)
      (fun z θ => Φs z θ + Ef z θ)) := by
  intro Ce
  refine ⟨1, one_pos, le_rfl, ?_⟩
  intro α hαIoc f Ef Φs Cs hadm h7 hEf hΦs hell hstar6
  exact nMem6_of_parts hαIoc.1 hαIoc.2 hadm h7 hEf hΦs hell hstar6

end Work.FTS.StrongEps.E4R3.Apriori4Proofs
