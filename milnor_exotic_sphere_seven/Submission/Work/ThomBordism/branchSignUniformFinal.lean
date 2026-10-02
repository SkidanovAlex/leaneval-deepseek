import Mathlib
import Submission.Work.ThomBordism.branchSign_uniform_of_fibreGen
import Submission.Work.ThomBordism.fibreRes_gtdU_canonical
import Submission.Work.ThomBordism.nfGen_span
import Submission.Work.ThomBordism.nfRelCohIso

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 400000

/-!
# THOM: the final assembly of the branch sign

`Work.ThomBordism.branchSign_uniform_of_fibreGen` (PROVED) turns the two *sharp* fibre comparisons
(F1 with an existential uniform `s`, F2 with no sign) into the class-level uniformity

    `gtdU E ND G hgm = s • U`  for every local-degree class `U` that generates.

Its F2 hypothesis is the *sharp* form `nfRes U = nfGen hk E ND x`, which the delegates showed is not
derivable (nor refutable) from the API, because the reference `nfGen` is built from a
`Classical.choice` and only its *uniformity over the data* is a mathematical statement.  The usable
input is therefore the **uniform** form (dispatched as
`ThomBordism/fibreRes_localDegreeClass_eq_nfGen_uniform`)

    `∃ t, (t = 1 ∨ t = -1) ∧ ∀ (data) (U) (IsLocalDegreeClass … U) (x),
        nfRes E x k U = t • nfGen hk E ND x`,

which pins the local-degree class's fibre orientation against the *same* reference up to one global
sign.  This file performs the assembly for that form, using the public linear-algebra core
`Work.ThomBordism.branchSign_core` and F1 (`fibreRes_gtdU_canonical`, PROVED), `nfGen_span` (PROVED)
and `nfRelCohIso` (PROVED): with `gN := t • nfGen hk E ND x` the two fibre comparisons become
`L (gtdU …) = (s·t) • gN` and `L U = gN`, so `branchSign_core` gives `gtdU … = (s·t) • U`.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1600000
set_option linter.unusedVariables false

open CategoryTheory Limits
open scoped Topology

namespace Work.ThomBordism

/-- **The uniformity of the branch sign, from the *uniform* F2.** -/
theorem branchSign_uniform_of_F2uniform (k : ℕ) (hk : 1 ≤ k)
    (hF2u : ∃ t : ℤ, (t = 1 ∨ t = -1) ∧
      ∀ {V : Work.ThomBordism.Man8} [ConnectedSpace V.pt]
        (E : Work.ThomBordism.PontryaginThom.EmbeddingData V (8 + k))
        (ND : Work.ThomBordism.PontryaginThom.NormalData V k E.e)
        {ε : ℝ} (C : Work.Tubular.TubeChart E ε) (q : Work.Tubular.NormalSphSub E ε)
        (hU : IsCompact C.U) {R : ℝ} (hR : 0 ≤ R)
        (hbox : ∀ y ∈ C.U, ∀ j : Fin (8 + k), |y j| < R)
        (g : C(OnePoint (Work.Tubular.Euc (8 + k)), OnePoint (Work.Tubular.NormalTotal E)))
        (hg : ∀ y, y ∉ C.openTube → g (OnePoint.some y) = OnePoint.infty)
        (hg2 : ∀ y, y ∈ C.openTube →
          g (OnePoint.some y) = OnePoint.some (Work.Tubular.normalBlowUp E ε (C.inv y)))
        (U : Work.Thom.RelCoh ℤ k (TopCat.of (Work.Tubular.NormalTotal E))
          (Work.Tubular.normalNonzero E)),
        Work.ThomBordism.IsLocalDegreeClass C g hg hR hbox U →
        ∀ x : V.pt, nfRes E x k U = t • nfGen hk E ND x) :
    ∃ s : ℤ, (s = 1 ∨ s = -1) ∧
      ∀ {V : Work.ThomBordism.Man8} [ConnectedSpace V.pt]
        (E : Work.ThomBordism.PontryaginThom.EmbeddingData V (8 + k))
        (ND : Work.ThomBordism.PontryaginThom.NormalData V k E.e)
        (G : C((Work.Tubular.normalBundle E ND).TotalSpace,
          (Work.ThomBordism.Grassmann.tautologicalBundle k 10).TotalSpace))
        (hgm : ∀ p ∈ Work.Thom.zeroComplement (Work.Tubular.normalBundle E ND),
          G p ∈ Work.Thom.zeroComplement (Work.ThomBordism.Grassmann.tautologicalBundle k 10))
        (hbp : ∀ p, (Work.ThomBordism.Grassmann.tautologicalBundle k 10).proj (G p)
          = Work.ThomBordism.Grassmann.padGaussFun E ND p.1)
        (hvec : ∀ p, Work.ThomBordism.Grassmann.evalVec (G p)
          = Work.PTGeometric.padEuc k 10 (by norm_num)
              (Work.Tubular.NormalTotal.vec (Work.Tubular.bundleToNormal E ND p)))
        {ε : ℝ} (C : Work.Tubular.TubeChart E ε) (q : Work.Tubular.NormalSphSub E ε)
        (hU : IsCompact C.U) {R : ℝ} (hR : 0 ≤ R)
        (hbox : ∀ y ∈ C.U, ∀ j : Fin (8 + k), |y j| < R)
        (g : C(OnePoint (Work.Tubular.Euc (8 + k)), OnePoint (Work.Tubular.NormalTotal E)))
        (hg : ∀ y, y ∉ C.openTube → g (OnePoint.some y) = OnePoint.infty)
        (hg2 : ∀ y, y ∈ C.openTube →
          g (OnePoint.some y) = OnePoint.some (Work.Tubular.normalBlowUp E ε (C.inv y)))
        (U : Work.Thom.RelCoh ℤ k (TopCat.of (Work.Tubular.NormalTotal E))
          (Work.Tubular.normalNonzero E)),
        Work.ThomBordism.IsLocalDegreeClass C g hg hR hbox U →
        Submodule.span ℤ ({U} : Set (Work.Thom.RelCoh ℤ k
          (TopCat.of (Work.Tubular.NormalTotal E)) (Work.Tubular.normalNonzero E))) = ⊤ →
        Work.ThomBordism.gtdU E ND G hgm = s • U := by
  obtain ⟨t, htm, hF2t⟩ := hF2u
  obtain ⟨s₀, hs₀m, hF1⟩ := fibreRes_gtdU_canonical k hk
  refine ⟨s₀ * t, ?_, ?_⟩
  · rcases hs₀m with h | h <;> rcases htm with h' | h' <;> rw [h, h'] <;> norm_num
  · intro V hV E ND G hgm hbp hvec eps C q hU R hR hbox g hg hg2 U hld hspan
    obtain ⟨x⟩ := hV.toNonempty
    refine branchSign_core (nfRes E x k) U (Work.ThomBordism.gtdU E ND G hgm)
      (t • nfGen hk E ND x) (s₀ * t) hspan (nfRelCohIso (V := V) hk E ND x) ?_ ?_ ?_
    · -- the reference `t • nfGen` generates
      have hg : nfGen hk E ND x ∈ Submodule.span ℤ
          ({t • nfGen hk E ND x} : Set (Work.Thom.RelCoh ℤ k ↥(nfSet E x)
            (nfPunct E x))) := by
        rcases htm with h | h
        · rw [h]; simp
        · rw [h]
          have hmem : (-1 : ℤ) • nfGen hk E ND x ∈ (Submodule.span ℤ
              ({(-1 : ℤ) • nfGen hk E ND x} : Set (Work.Thom.RelCoh ℤ k ↥(nfSet E x)
                (nfPunct E x)))) := Submodule.subset_span (Set.mem_singleton _)
          simpa using (Submodule.neg_mem _ hmem)
      rw [eq_top_iff]
      refine le_trans (le_of_eq (nfGen_span hk E ND x).symm) ?_
      exact Submodule.span_le.mpr (fun y hy => by
        rw [Set.mem_singleton_iff] at hy
        subst hy
        exact hg)
    · -- `L (gtdU) = (s₀ * t) • (t • nfGen)`
      rw [hF1 E ND G hgm hbp hvec x]
      rcases htm with h | h
      · rw [h]; simp
      · rw [h]; simp
    · -- `L U = t • nfGen`
      exact hF2t E ND C q hU hR hbox g hg hg2 U hld x

end Work.ThomBordism
