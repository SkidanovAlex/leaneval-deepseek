/-
# SeedDyn — the dynamical Böttcher homeomorphism at a parameter of the mandelbar

This module fixes the vocabulary of the area `Work.SeedDyn` (the design note is
`Submission/Work/NOTES_LEAD_mandelbar_seed.md` §1 and §2) and proves the bottom layer on which
every other module of the area builds.

## The objects

* `Work.SeedDyn.esc c` — the **escaping set** of `T_c(z) = z̄² + c`, i.e. the complement of the
  filled Julia set (`Work.ParamRays.escapingSet c`, definitionally `(filledJulia c)ᶜ`).  This is
  the `U` of the design note; it is the domain of the dynamical Böttcher coordinate.
* `Work.Landing.Tsq c = (Tantibar c)^[2]` — the holomorphic second iterate of `T_c`,
  `z ↦ (z² + c̄)² + c`; it is the map under which the Böttcher functional equation becomes
  holomorphic.
* `Work.Bottcher.varphiCrit c` — the canonical critical Böttcher coordinate of `T_c`
  (`Work.ParamRays.IsCritBottcher c`).  For `c ∈ M*` its restriction to `esc c` is the genuine
  dynamical Böttcher coordinate `Work.ParamRays.dynPhi c`, and it is the `φ` of the design note's
  D-table.

## Main definitions

* `Work.SeedDyn.esc`.

## Main results (the D-table of the design note, bottom layer)

* `Work.SeedDyn.esc_eq_compl`, `Work.SeedDyn.isOpen_esc`, `Work.SeedDyn.Tsq_mem_esc` — the
  elementary topology of the domain.
* `Work.SeedDyn.critDomain_eq_escapingSet` (**D1**): for `c ∈ M*` the critical domain
  `{G_c > G_c 0}` is the whole escaping set.
* `Work.SeedDyn.analyticOnNhd_varphiCrit_esc`,
  `Work.SeedDyn.norm_varphiCrit_esc`, `Work.SeedDyn.one_lt_norm_varphiCrit_esc` (**D3**) — the
  analyticity of `φ` on the basin, its modulus `‖φ z‖ = exp (G_c z)` and the resulting
  `1 < ‖φ z‖` there.
* `Work.SeedDyn.dynPhiOf_eq_varphiCrit` (**D2**): on the escaping set the canonical Böttcher
  coordinate `dynPhiOf c` agrees with `varphiCrit c`.
-/
import Mathlib
import Submission.Work.ParamRays.DynBottcher
import Submission.Work.ParamRays.Interface
import Submission.Work.ParamRays.isClosed_filledJulia
import Submission.Work.Bottcher.CritBottcherExists
import Submission.Work.Bottcher.CritBasic
import Submission.Work.Landing.Core
import Submission.Work.ELPull.Defs

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


open scoped Topology ComplexConjugate
open Classical Filter

namespace Work.SeedDyn

open LeanEval.ComplexAnalysis (Tantibar Mandelbar)

noncomputable section

/-! ## The domain: the escaping set -/

/-- The **escaping set** of `T_c`, i.e. the complement of the filled Julia set.  This is the
domain `U` of the design note: the open set on which the dynamical Böttcher coordinate is a
homeomorphism onto the exterior disc. -/
abbrev esc (c : ℂ) : Set ℂ := Work.ParamRays.escapingSet c

@[simp] theorem mem_esc {c z : ℂ} : z ∈ esc c ↔ Work.ParamRays.Escaping c z := Iff.rfl

/-- The escaping set is the complement of the filled Julia set. -/
theorem esc_eq_compl_filledJulia (c : ℂ) : esc c = (Work.ParamRays.filledJulia c)ᶜ :=
  (Work.ParamRays.compl_filledJulia c).symm

/-- The escaping set is open. -/
theorem isOpen_esc (c : ℂ) : IsOpen (esc c) := by
  rw [esc_eq_compl_filledJulia]
  exact (Work.ParamRays.isClosed_filledJulia c).isOpen_compl

/-- The escaping set is forward invariant under `T_c`. -/
theorem Tantibar_mem_esc {c z : ℂ} (hz : z ∈ esc c) : Tantibar c z ∈ esc c := by
  have h := hz.iterate 1
  simpa [Work.ParamRays.orbit] using h

/-- The escaping set is forward invariant under the holomorphic second iterate `Tsq c`. -/
theorem Tsq_mem_esc {c z : ℂ} (hz : z ∈ esc c) : Work.Landing.Tsq c z ∈ esc c := by
  have h : Work.ParamRays.Escaping c ((Tantibar c)^[2] z) := by
    simpa [Work.ParamRays.orbit] using hz.iterate 2
  rwa [Work.ELPull.Tsq_eq_iterate]

/-! ## The critical domain is the escaping set for `c ∈ M*` (D1) -/

/-- The parameter potential vanishes on the mandelbar. -/
theorem paramPotential_eq_zero {c : ℂ} (hc : c ∈ Mandelbar) :
    Work.ParamRays.paramPotential c = 0 :=
  Work.ParamRays.greenFun_eq_zero_of_bounded c 0
    (by simpa [LeanEval.ComplexAnalysis.Mandelbar, Work.ParamRays.BoundedOrbit, Work.ParamRays.orbit] using hc)

/-- **D1.**  For a parameter `c` of the mandelbar the critical domain `{G_c > G_c 0}` of the
parameter-plane Böttcher theory is the whole escaping set `{G_c > 0}`.

Indeed the Green function is nonnegative and vanishes exactly on the filled Julia set
(`greenFun_eq_zero_iff`), and for `c ∈ M*` the critical point does not escape, so
`G_c 0 = 0`. -/
theorem critDomain_eq_escapingSet {c : ℂ} (hc : c ∈ Mandelbar) :
    Work.ParamRays.critDomain c = Work.ParamRays.escapingSet c := by
  have h0 : Work.ParamRays.paramPotential c = 0 := paramPotential_eq_zero hc
  ext z
  rw [Work.ParamRays.mem_critDomain, h0, Work.ParamRays.mem_escapingSet,
    Work.ParamRays.escaping_iff_not_bounded]
  constructor
  · intro h hb
    have hz0 : Work.ParamRays.greenFun c z = 0 :=
      (Work.ParamRays.greenFun_eq_zero_iff c z).mpr hb
    linarith
  · intro h
    have hnn : 0 ≤ Work.ParamRays.greenFun c z := Work.ParamRays.greenFun_nonneg c z
    rcases lt_or_eq_of_le hnn with hlt | heq
    · exact hlt
    · exact absurd ((Work.ParamRays.greenFun_eq_zero_iff c z).mp heq.symm) h

/-! ## Analyticity and modulus of the canonical Böttcher coordinate (D3) -/

/-- **D3(a).**  For `c ∈ M*` the canonical critical Böttcher coordinate is analytic on the whole
escaping set. -/
theorem analyticOnNhd_varphiCrit_esc {c : ℂ} (hc : c ∈ Mandelbar) :
    AnalyticOnNhd ℂ (Work.Bottcher.varphiCrit c) (esc c) := by
  have h := Work.Bottcher.analyticOnNhd_varphiCrit c
  rwa [critDomain_eq_escapingSet hc] at h

/-- **D3(b).**  On the escaping set the modulus of the Böttcher coordinate is
`exp (G_c z)`. -/
theorem norm_varphiCrit_esc {c z : ℂ} (hc : c ∈ Mandelbar) (hz : z ∈ esc c) :
    ‖Work.Bottcher.varphiCrit c z‖ = Real.exp (Work.ParamRays.greenFun c z) := by
  have hz' : z ∈ Work.ParamRays.critDomain c := by
    rw [critDomain_eq_escapingSet hc]; exact hz
  rw [Work.Bottcher.norm_varphiCrit hz', Work.Bottcher.CritBasic.green_eq]

/-- **D3(c).**  On the escaping set the Böttcher coordinate has modulus bigger than `1`. -/
theorem one_lt_norm_varphiCrit_esc {c z : ℂ} (hc : c ∈ Mandelbar) (hz : z ∈ esc c) :
    1 < ‖Work.Bottcher.varphiCrit c z‖ := by
  rw [norm_varphiCrit_esc hc hz, ← Real.exp_zero]
  refine Real.exp_lt_exp.mpr ?_
  have hnn : 0 ≤ Work.ParamRays.greenFun c z := Work.ParamRays.greenFun_nonneg c z
  have hne : Work.ParamRays.greenFun c z ≠ 0 := by
    intro h
    exact ((Work.ParamRays.escaping_iff_not_bounded c z).mp hz)
      ((Work.ParamRays.greenFun_eq_zero_iff c z).mp h)
  exact lt_of_le_of_ne hnn (Ne.symm hne)

/-! ## The two Böttcher coordinates agree on the escaping set (D2) -/

/-- **D2.**  For `c ∈ M*` the canonical dynamical Böttcher coordinate `dynPhiOf c` agrees with
`Work.Bottcher.varphiCrit c` on the escaping set.

Both functions are Böttcher coordinates of `T_c` on `critDomain c = esc c` (`IsDynBottcher` and
`IsCritBottcher` agree once D1 is used), and a Böttcher coordinate on the critical domain is
unique (`Work.ParamRays.isCritBottcher_unique`). -/
theorem dynPhiOf_eq_varphiCrit {c z : ℂ} (hc : c ∈ Mandelbar) (hz : z ∈ esc c) :
    Work.ParamRays.dynPhiOf c z = Work.Bottcher.varphiCrit c z := by
  have hex : Work.ParamRays.DynBottcherExists c :=
    Work.Bottcher.exists_isDynBottcher_of_mem_mandelbar c hc
  have hb : Work.ParamRays.IsDynBottcher c (Work.ParamRays.dynPhiOf c) :=
    Work.ParamRays.isDynBottcher_dynPhiOf hex
  have hcd : Work.ParamRays.critDomain c = Work.ParamRays.escapingSet c :=
    critDomain_eq_escapingSet hc
  have hc' : Work.ParamRays.IsCritBottcher c (Work.ParamRays.dynPhiOf c) := by
    refine ⟨?_, ?_, ?_⟩
    · rw [hcd]; exact hb.1
    · intro w hw
      rw [hcd] at hw
      exact hb.2.1 w hw
    · exact hb.2.2
  have hz' : z ∈ Work.ParamRays.critDomain c := by rw [hcd]; exact hz
  exact (Work.Bottcher.varphiCrit_unique hc' hz').symm

end

end Work.SeedDyn
