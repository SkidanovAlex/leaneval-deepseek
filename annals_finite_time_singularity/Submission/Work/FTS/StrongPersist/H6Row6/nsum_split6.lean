/-
# `H6Row6/nsum_split6` — the twenty-piece splitting of the level-six `N`-row

`Work.FTS.StrongPersist.H6Rows.Npair6SupAux.NSplit6` proves the *pointwise* splitting of the
nonlinear term of the modulated equation, `N α (F_* + f) (Φ̃_* + Ef) = nsum α f Ef Φ̃_*` on the
open quadrant, and `H6Row6/Pieces` regroups the twenty summands as the `ℕ`-indexed family
`pcs`.  This file records, for every datum of the level-six context `L6Ctx`, the four rows the
assembly of the row consumes:

* the `C⁶`-regularity of each of the twenty pieces on the open quadrant;
* the `ℋ⁶`-membership of each piece (`NS6.pieces`, proved in `H6Row6/NS6/Pieces.lean`);
* the `ℋ⁶`-membership of the full nonlinear term `N α (Ftau α g τ) (slice Φ τ)`, transported
  from `nsum` along the pointwise splitting identity and the `ℋ⁶`-closure of `Finset.range` sums
  (`NS6.hkMem_sum_range`);
* the **pairing identity** `IP6 α (nsum …) f = ∑_{k<20} IP6 α (pcs … k) f`, obtained from
  `pcs_sum` (`IP6_congr`) and the finite-order additivity `IP6AddFin` iterated over
  `Finset.range 20`.

The only existential constant is the one of `N6_fkH` (which supplies the `ℋ⁶`-membership of the
angular moment `FK f`); it is absorbed into the stated `∃ α₂`.
-/
import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Submission.Work.FTS.StrongPersist.H6Row6.NS6.Pieces
import Submission.Work.FTS.StrongPersist.N6_fkH
import Submission.Work.FTS.StrongPersist.N6_prod

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section
open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.StrongPersist.H6Row6

open Work.FTS.Galerkin (Fn Fam slice)

set_option autoImplicit false
set_option linter.unusedVariables false
set_option maxHeartbeats 1600000

theorem nsum_split6 (Ce : ℝ) (hCe : 0 < Ce) : ∃ α₂ : ℝ, 0 < α₂ ∧ α₂ ≤ 1 ∧
    ∀ α ∈ Set.Ioc 0 α₂, ∀ (g Φ : Work.FTS.Galerkin.Fam) (τ M Cs : ℝ)
      (E : Work.FTS.Galerkin.Fn → Work.FTS.Galerkin.Fn) (Φs : Work.FTS.Galerkin.Fn),
      0 ≤ τ →
      Work.FTS.StrongPersist.L6Ctx (Work.FTS.StrongPersist.IP6 1 1 1 1 1 1 1 1 1 1)
        α M Ce Cs E Φs g Φ τ →
      (∀ k : ℕ, k < 20 → ContDiffOn ℝ 6 (Function.uncurry
          (Work.FTS.StrongPersist.H6Row6.pcs α (Work.FTS.Galerkin.slice g τ)
            (E (Work.FTS.Galerkin.slice g τ)) Φs k)) Work.FTS.EllipticEst.Q0) ∧
      (∀ k : ℕ, k < 20 → Work.Spaces.HkMem α 6
          (Work.FTS.StrongPersist.H6Row6.pcs α (Work.FTS.Galerkin.slice g τ)
            (E (Work.FTS.Galerkin.slice g τ)) Φs k)) ∧
      Work.Spaces.HkMem α 6 (Work.Construction.N α (Work.Construction.Ftau α g τ)
          (Work.FTS.Galerkin.slice Φ τ)) ∧
      Work.FTS.StrongPersist.IP6 1 1 1 1 1 1 1 1 1 1 α
          (Work.FTS.StrongPersist.H6Rows.Npair6SupAux.nsum α (Work.FTS.Galerkin.slice g τ)
            (E (Work.FTS.Galerkin.slice g τ)) Φs) (Work.FTS.Galerkin.slice g τ)
        = ∑ k ∈ Finset.range 20, Work.FTS.StrongPersist.IP6 1 1 1 1 1 1 1 1 1 1 α
            (Work.FTS.StrongPersist.H6Row6.pcs α (Work.FTS.Galerkin.slice g τ)
              (E (Work.FTS.Galerkin.slice g τ)) Φs k) (Work.FTS.Galerkin.slice g τ) := by
  obtain ⟨Xi, Cpow, α₂fk, hXi, hCpow, hα₂fk, hfkH⟩ := Work.FTS.StrongPersist.N6_fkH
  obtain ⟨Xi2, Cpow2, α₂pr, hXi2, hCpow2, hα₂pr, hpr⟩ := Work.FTS.StrongPersist.N6_prod
  refine ⟨min 1 (min α₂fk α₂pr), lt_min one_pos (lt_min hα₂fk hα₂pr), min_le_left _ _, ?_⟩
  intro α hαIoc g Φ τ M Cs E Φs hτ hctx
  obtain ⟨hα, hαle⟩ := Set.mem_Ioc.mp hαIoc
  have hα1 : α ≤ 1 := le_trans hαle (min_le_left _ _)
  have hαpr : α ∈ Set.Ioc 0 α₂pr :=
    ⟨hα, le_trans hαle (le_trans (min_le_right _ _) (min_le_right _ _))⟩
  have hαfk : α ∈ Set.Ioc 0 α₂fk :=
    ⟨hα, le_trans hαle (le_trans (min_le_right _ _) (min_le_left _ _))⟩
  set f : Fn := slice g τ with hf
  set Ef : Fn := E (slice g τ) with hEf
  have hadm : Work.FTS.StrongPersist.H6Adm α f := hctx.hreg
  have h7 : Work.Spaces.HkMem α 7 f := hctx.h7
  have hell : Work.FTS.StrongPersist.Ell6Ctx α Ce Cs E Φs f (slice Φ τ) := hctx.hell
  have hstar6 : Work.FTS.StrongPersist.StarPkg6 α Cs Φs := hctx.hstar6
  have hkfm : Work.Spaces.HkMem α 6 (fun z (_ : ℝ) => Work.Construction.FK f z) :=
    (hfkH α hαfk f ⟨hadm.reg.1, hadm.reg.2⟩ hadm.l12).1
  have D : NS6.Data α Ce Cs f Ef Φs :=
    ⟨hα, hα1, hadm.reg.1, hadm.reg.2, h7, (hell.hell).smooth, hell.hstar.smooth,
      hadm.l12, hstar6, hell.hell, hkfm, hadm,
      fun u v hus hum hvs hvm => (hpr α hαpr u v ⟨hus, hum⟩ ⟨hvs, hvm⟩).1⟩
  have hpcs : ∀ k : ℕ, k < 20 →
      ContDiffOn ℝ 6 (Function.uncurry (pcs α f Ef Φs k)) Work.FTS.EllipticEst.Q0
      ∧ Work.Spaces.HkMem α 6 (pcs α f Ef Φs k) := NS6.pieces D
  -- ### the `ℋ⁶`-membership of `N`
  have hNpt : ∀ z θ, (z, θ) ∈ Work.Construction.Qd →
      Work.Construction.N α (Work.Construction.Ftau α g τ) (slice Φ τ) z θ
        = Work.FTS.StrongPersist.H6Rows.Npair6SupAux.nsum α f Ef Φs z θ := by
    intro z θ hzθ
    have hp := Work.FTS.StrongPersist.H6Rows.Npair6SupAux.nsplit6_pt hα hα1 hadm
      (hell.hell).smooth hell.hstar.smooth z θ hzθ
    rw [show Work.Construction.Ftau α g τ
        = fun z θ => Work.Construction.Fstar α z θ + f z θ from rfl, hell.hsum]
    exact hp
  have hNmem : Work.Spaces.HkMem α 6
      (Work.Construction.N α (Work.Construction.Ftau α g τ) (slice Φ τ)) := by
    refine Work.FTS.StrongPersist.H6Pair6Aux.HkMem_congr_Qd
      (fun z θ hzθ => (hNpt z θ hzθ).symm) ?_
    rw [pcs_sum]
    exact (NS6.hkMem_sum_range 20 (pcs α f Ef Φs)
      (fun k hk => (hpcs k hk).1) (fun k hk => (hpcs k hk).2)).2
  -- ### the pairing identity
  have hIP : ∀ N : ℕ, 1 ≤ N → N ≤ 20 →
      Work.FTS.StrongPersist.IP6 1 1 1 1 1 1 1 1 1 1 α
          (fun z θ => ∑ k ∈ Finset.range N, pcs α f Ef Φs k z θ) f
        = ∑ k ∈ Finset.range N, Work.FTS.StrongPersist.IP6 1 1 1 1 1 1 1 1 1 1 α
            (pcs α f Ef Φs k) f := by
    intro N hN1 hN20
    obtain ⟨n, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : N ≠ 0)
    induction n with
    | zero =>
        have hfun : (fun z θ => ∑ k ∈ Finset.range (Nat.succ 0), pcs α f Ef Φs k z θ)
            = pcs α f Ef Φs 0 := by
          funext z θ
          simp
        rw [hfun]
        simp
    | succ m ih =>
        have hsplit : (fun z θ => ∑ k ∈ Finset.range ((m + 1) + 1), pcs α f Ef Φs k z θ)
            = fun z θ => (∑ k ∈ Finset.range (m + 1), pcs α f Ef Φs k z θ)
              + pcs α f Ef Φs (m + 1) z θ := by
          funext z θ; rw [Finset.sum_range_succ]
        rw [hsplit]
        have hp20 : m + 1 ≤ 20 := Nat.le_of_succ_le hN20
        have hlt : m + 1 < 20 := Nat.lt_of_succ_le hN20
        have hpartial := NS6.hkMem_sum_range (m + 1) (pcs α f Ef Φs)
          (fun k hk => (hpcs k (lt_of_lt_of_le hk hp20)).1)
          (fun k hk => (hpcs k (lt_of_lt_of_le hk hp20)).2)
        rw [Work.FTS.StrongPersist.IP6AddFin (α := α) hα hpartial.1 (hpcs (m + 1) hlt).1
          (NS6.Data.hfcd D) hpartial.2 (hpcs (m + 1) hlt).2 D.fm]
        rw [ih (by omega) hp20]
        rw [show (∑ k ∈ Finset.range (Nat.succ (m + 1)),
              Work.FTS.StrongPersist.IP6 1 1 1 1 1 1 1 1 1 1 α (pcs α f Ef Φs k) f)
            = (∑ k ∈ Finset.range (m + 1),
                Work.FTS.StrongPersist.IP6 1 1 1 1 1 1 1 1 1 1 α (pcs α f Ef Φs k) f)
              + Work.FTS.StrongPersist.IP6 1 1 1 1 1 1 1 1 1 1 α
                  (pcs α f Ef Φs (m + 1)) f
            from Finset.sum_range_succ _ _]
  have hcongr : Work.FTS.StrongPersist.IP6 1 1 1 1 1 1 1 1 1 1 α
      (Work.FTS.StrongPersist.H6Rows.Npair6SupAux.nsum α f Ef Φs) f
      = Work.FTS.StrongPersist.IP6 1 1 1 1 1 1 1 1 1 1 α
          (fun z θ => ∑ k ∈ Finset.range 20, pcs α f Ef Φs k z θ) f :=
    Work.FTS.StrongPersist.IP6_congr 1 1 1 1 1 1 1 1 1 1 α hα
      (fun z θ _ => by rw [pcs_sum]; simp [Finset.sum_apply])
  exact ⟨fun k hk => (hpcs k hk).1, fun k hk => (hpcs k hk).2, hNmem,
    by rw [hcongr]; exact hIP 20 (by norm_num) le_rfl⟩

end Work.FTS.StrongPersist.H6Row6
