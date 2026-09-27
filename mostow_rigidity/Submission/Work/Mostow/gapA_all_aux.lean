/-
# Helper module for `Work.Mostow.gapA_all`

Collects the hypothesis `Prop`s of the GAP-A chains in every dimension `k ≥ 2`:

* `POActionProp k`       (`Work.Mostow.poAction_ge1`)
* `HypIsometryProp k`    (`Work.Mostow.hypIsometryAll`, valid in every dimension)
* `MargulisCuspProp k`   (`Work.Mostow.margulisCusp`)
* `PairStabProp k`       (re-proved below from `Work.Mostow.pairStabDefs`)
* `MargulisLoxProp k`    (`Work.Mostow.margulisLox`, from `PairStabProp k`)
* `ClassifyProp k`       (`Work.Mostow.classify_ge2`)
* `MultThickProp Λ`      (`Work.Mostow.geomFiniteMultThick`, for lattices `Λ`)
* `CovolLB k`            (`Work.Mostow.KMcovol`, from all of the above)

**Two traps this module is built around.**

1.  The name `Work.Mostow.pairStab` is declared twice in this workspace: as the area *theorem*
    "stabiliser of two boundary points" (`pairStab.lean`) and as the *definition* "subgroup
    fixing `ξ` and `η`" (`pairStabCocycleDiscrete.lean`).  Lean's import merge only accepts a
    duplicated name when both copies are theorems with identical types, so no module may import
    both `pairStab.lean` and the `gapA_*` chain (which pulls `pairStabCocycleDiscrete`).
    `PairStabProp` is therefore re-proved below from `pairStabDefs` (the same short argument as
    `Work.Mostow.pairStab`, under a different name).
2.  This module deliberately does not import the `gapA_*` chain either, so that it stays
    usable (the chain re-declares `pairStab` and lives under the same clash as (1)).
-/

import Mathlib
import Submission.Mostow.GapADefs
import Submission.Work.Mostow.poAction_ge1
import Submission.Work.Mostow.hypIsometry
import Submission.Work.Mostow.margulisCusp
import Submission.Work.Mostow.pairStabDefs
import Submission.Work.Mostow.margulisLox
import Submission.Work.Mostow.classify_ge2
import Submission.Work.Mostow.geomFiniteMultThick
import Submission.Work.Mostow.KMcovol

namespace Work.Mostow

open Submission.Mostow LeanEval.Geometry.MostowRigidity MeasureTheory

noncomputable section

/-- `POActionProp` in every dimension `k ≥ 2`. -/
lemma poAction_all (k : ℕ) (hk : 2 ≤ k) : POActionProp k := poAction_ge1 k (by omega)

/-- `HypIsometryProp` in every dimension `k ≥ 2`. -/
lemma hypIsometry_all (k : ℕ) (hk : 2 ≤ k) : HypIsometryProp k :=
  hypIsometryAll k (poAction_all k hk)

/-- `MargulisCuspProp` in every dimension `k ≥ 2`. -/
lemma margulisCusp_all (k : ℕ) (hk : 2 ≤ k) : MargulisCuspProp k :=
  fun R => margulisCusp k hk (poAction_all k hk) (hypIsometry_all k hk) R

/-- `PairStabProp` in every dimension `k ≥ 2`.

(The proof of `Work.Mostow.pairStab`, carried out here because `pairStab.lean` cannot be
co-imported with the `gapA_*` chain; it only uses lemmas of `pairStabDefs`.) -/
lemma pairStab_all (k : ℕ) (hk : 2 ≤ k) : PairStabProp k := by
  intro ξ η hξ hη hne
  refine ⟨pairPoint ξ η, ?_⟩
  intro g hgξ hgη
  obtain ⟨lam, hlamne, hlam⟩ := emat_eigen_of_bd g hξ hgξ
  obtain ⟨μ, hμne, hμ⟩ := emat_eigen_of_bd g hη hgη
  have hlamμ : lam * μ = 1 := eigen_mul_eq_one g hξ hη hne hlam hμ
  obtain ⟨hlev, hlampos, hbus⟩ := lev_emat_eigen g hξ hlam
  refine ⟨?_, ?_⟩
  · rw [hdist_pairPoint g ξ η hξ hη hne hlam hμ hlamμ hlampos, hbus, abs_neg]
  · intro ζ hζ hζξ hζη hgζ
    obtain ⟨ρ, hρne, hρ⟩ := emat_eigen_of_bd g hζ hgζ
    have hlamμeq : lam = μ := eigen_eq_of_third g hξ hη hζ hζξ hζη hlam hμ hρ
    have hsq : lam ^ 2 = 1 := by
      have h : lam * lam = 1 := by
        rw [← hlamμeq] at hlamμ
        exact hlamμ
      rwa [pow_two]
    have hlam1 : lam = 1 := by
      rcases sq_eq_one_iff.1 hsq with h | h
      · exact h
      · rw [h] at hlampos; norm_num at hlampos
    rw [hbus, hlam1, Real.log_one, neg_zero]

/-- `MargulisLoxProp` in every dimension `k ≥ 2`. -/
lemma margulisLox_all (k : ℕ) (hk : 2 ≤ k) : MargulisLoxProp k :=
  margulisLox k hk (poAction_all k hk) (hypIsometry_all k hk) (pairStab_all k hk)

/-- `ClassifyProp` in every dimension `k ≥ 2`. -/
lemma classify_all (k : ℕ) (hk : 2 ≤ k) : ClassifyProp k :=
  classify_ge2 k hk (poAction_all k hk) (hypIsometry_all k hk)

/-- `MultThickProp` for every lattice in every dimension `k ≥ 2`. -/
lemma multThick_all (k : ℕ) (hk : 2 ≤ k) (Λ : Subgroup (PO k 1)) (hΛ : HypLattice Λ) :
    MultThickProp Λ :=
  geomFiniteMultThick k (by omega) (poAction_all k hk) (hypIsometry_all k hk) Λ hΛ

/-- Kazhdan–Margulis covolume bound in every dimension `k ≥ 2`. -/
lemma covolLB_all (k : ℕ) (hk : 2 ≤ k) : CovolLB k :=
  KMcovol k hk (poAction_all k hk) (hypIsometry_all k hk) (margulisCusp_all k hk)
    (margulisLox_all k hk) (pairStab_all k hk) (classify_all k hk) (multThick_all k hk)

end

end Work.Mostow
