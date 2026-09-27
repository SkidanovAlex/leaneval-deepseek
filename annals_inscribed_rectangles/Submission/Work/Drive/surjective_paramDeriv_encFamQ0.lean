import Mathlib
import Submission.Work.Drive.surjective_paramDeriv_encFamQ0_caseI
import Submission.Work.Drive.surjective_paramDeriv_encFamQ0_caseII

/-!
# `hrich` for the corrected ends-clause family `encFamQ0`: the `betaG` split

`NOTES_LEAD_hodd_faces.md` §1 splits the richness of the parametrised Sard for the corrected
ends-clause family `Work.Drive.encFamQ0` into two cases according to the block-`0` **time** coordinate
`s := (bPartC 0 y) 2`:

* **Case I** (`betaG s ≠ 0`, i.e. `s ∈ (0,1)`): the class perturbation `p` is alive, so block `0`'s
  reach is the whole class chart; `PairReg` alone supplies the coset condition.  Proved:
  `Work.Drive.surjective_paramDeriv_encFamQ0_caseI`.
* **Case II** (`betaG s = 0`, i.e. `s ≤ 0` or `s ≥ 1`): block `0` is frozen and its reach is
  `lift0 W₀` with `W₀` the charted image of `range (mfderiv F (shear q₀ u₀))` for
  `F := H (0,·)` (resp. `H (1,·)`); the coset condition comes from `PairReg` **and** `EndTripleReg`.
  Proved: `Work.Drive.surjective_paramDeriv_encFamQ0_caseII`.

`betaG s = expNegInvGlue s · expNegInvGlue (1-s)` vanishes exactly on `ℝ ∖ (0,1)`, so the two cases are
exhaustive.  This file is the dispatch: together with the two case lemmas it gives the **pointwise
surjectivity** that `Work.Drive.localSard_family_in_open`'s `hrich` demands for `encFamQ0`.
-/

namespace Work.Drive

open scoped Manifold ContDiff Topology

noncomputable section

/-- **`hrich` for `encFamQ0`** (the pointwise form): at every parameter `t` and every zero `y` of the
charted triple-difference map inside the chart, the parameter derivative is surjective.  Split on
`betaG ((bPartC 0 y) 2)` into the two proved cases. -/
theorem surjective_paramDeriv_encFamQ0
    (H : ℝ × EuclideanSpace ℝ (Fin 2) → Projectivization ℝ (Eucl 3))
    (A B : EuclideanSpace ℝ (Fin 2) → Projectivization ℝ (Eucl 3))
    (c₀ : ℝ) (hc₀0 : 0 < c₀) (hc₀1 : c₀ < 1) :
    letI : ChartedSpace (EuclideanSpace ℝ (Fin 3)) (Projectivization ℝ (Eucl 3)) :=
      Work.Drive.projCharted 3
    letI : IsManifold (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 3)))
      ((⊤ : ℕ∞) : WithTop ℕ∞) (Projectivization ℝ (Eucl 3)) :=
      Work.Drive.isManifold_projCharted 3
    letI : ChartedSpace (EuclideanSpace ℝ (Fin 4)) (Projectivization ℝ (Eucl 3) × ℝ) :=
      Work.Drive.projTimesLineCharted
    letI : IsManifold (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 4)))
      ((⊤ : ℕ∞) : WithTop ℕ∞) (Projectivization ℝ (Eucl 3) × ℝ) :=
      Work.Drive.isManifold_projTimesLineCharted
    ContMDiff (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 3)))
      (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 3))) ((⊤ : ℕ∞) : WithTop ℕ∞)
      (fun x : EuclideanSpace ℝ (Fin 3) => H (x 2, mk2 (x 0) (x 1))) →
    ContMDiff (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 2)))
      (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 3))) ((⊤ : ℕ∞) : WithTop ℕ∞) A →
    ContMDiff (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 2)))
      (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 3))) ((⊤ : ℕ∞) : WithTop ℕ∞) B →
    Work.Drive.FoldFlat A → Work.Drive.FoldFlat B →
    Work.Drive.FoldFlat (fun y : EuclideanSpace ℝ (Fin 2) => H (0, y)) →
    Work.Drive.FoldFlat (fun y : EuclideanSpace ℝ (Fin 2) => H (1, y)) →
    (∀ (s : ℝ), s ≤ 0 → ∀ y : EuclideanSpace ℝ (Fin 2), H (s, y) = H (0, y)) →
    (∀ (s : ℝ), 1 ≤ s → ∀ y : EuclideanSpace ℝ (Fin 2), H (s, y) = H (1, y)) →
    Work.Drive.PairReg A B →
    Work.Drive.EndTripleReg (fun y : EuclideanSpace ℝ (Fin 2) => H (0, y)) A B →
    Work.Drive.EndTripleReg (fun y : EuclideanSpace ℝ (Fin 2) => H (1, y)) A B →
    ∀ (p : Projectivization ℝ (Eucl 3) × ℝ) (t : Work.Drive.EncParQ0)
      (y : EuclideanSpace ℝ (Fin 9)),
      (∀ k : Fin 3, Work.Drive.encFamQ0 H A B c₀ t k (Work.Drive.TParity.bPartC k y)
        ∈ (Work.Drive.chr p).source) →
      Work.Drive.TParity.chartDiff3 p (Work.Drive.encFamQ0 H A B c₀ t) y = 0 →
      Function.Surjective
        (fderiv ℝ (fun t' => Work.Drive.TParity.chartDiff3 p
          (Work.Drive.encFamQ0 H A B c₀ t') y) t) := by
  intro hH hA hB hfoldA hfoldB hfold0 hfold1 hH0 hH1 hpair hend0 hend1 p t y hreg hz
  by_cases hβ : Work.Drive.betaG ((Work.Drive.TParity.bPartC 0 y) 2) = 0
  · exact Work.Drive.surjective_paramDeriv_encFamQ0_caseII H A B c₀ hc₀0 hc₀1
      hH hA hB hfoldA hfoldB hfold0 hfold1 hH0 hH1 hpair hend0 hend1 p t y hreg hz hβ
  · exact Work.Drive.surjective_paramDeriv_encFamQ0_caseI H A B c₀ hc₀0 hc₀1
      hH hA hB hfoldA hfoldB hpair p t y hreg hz hβ

end

end Work.Drive
