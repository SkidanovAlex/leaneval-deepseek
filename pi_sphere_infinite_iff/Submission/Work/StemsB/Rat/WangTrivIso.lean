import Mathlib
import Submission.Work.StemsB.Rat.WangDerivDefs
import Submission.Work.StemsB.Rat.PairDeltaRelComplexMap
import Submission.Work.StemsB.FibrewiseTrivRel
import Submission.Work.Cohomology.homotopyEquiv
import Submission.Work.Cohomology.isIso_homologyMap_tau1

/-!
# The trivialisation comparison is an isomorphism on relative cohomology

`Work.StemsB.Rat.wangTriv` is the map `H^*(E|_G, E|_C) → H^*(Q, C_Q)` induced by the trivialisation
`Ψ_G`, i.e. the pullback along the map of pairs `(Q, C_Q) → (E|_G, E|_C)`.  Here we prove that it
is an isomorphism in every degree.

The proof is the five lemma applied to the morphism of short exact sequences of the pair, whose
other two components are (i) the pullback `Ψ_G^*` on the absolute cohomology of the total spaces
(a homotopy equivalence, with homotopy inverse `Φ_G`), and (ii) the pullback on the absolute
cohomology of the relative parts, which is a homotopy equivalence of pairs
(`Work.StemsB.relΨA`, `Work.StemsB.relΦA`).
-/

open CategoryTheory CategoryTheory.Limits
open scoped Topology unitInterval

set_option autoImplicit false
set_option linter.unusedVariables false
set_option maxHeartbeats 16000000
set_option backward.isDefEq.respectTransparency false

namespace Work.StemsB.Rat

noncomputable section

variable {E : Type} [TopologicalSpace E]

/-- **The morphism of short exact sequences of a pair induced by a map of pairs**: the three
components are the pullbacks on the relative complexes, on the absolute total spaces and on the
absolute relative parts. -/
noncomputable def pairShortMap {X1 X2 : TopCat} (A1 : Set X1) (A2 : Set X2) (f : X1 ⟶ X2)
    (h : ∀ x ∈ A1, f x ∈ A2) :
    Work.Cohomology.pairShort ℚ X2 A2 ⟶ Work.Cohomology.pairShort ℚ X1 A1 :=
  ShortComplex.homMk (Work.Cohomology.relComplexMap ℚ A1 A2 f h)
    (Work.Cohomology.dualChainMap ℚ X1 X2 f)
    (Work.Cohomology.dualChainMap ℚ (TopCat.of A1) (TopCat.of A2)
      (Work.Cohomology.relMapSub A1 A2 f h))
    (relComplexMap_relIncl A1 A2 f h) (Work.Cohomology.dualChainMap_restr_comp ℚ A1 A2 f h)

/-- The pullback `Ψ_G^*` on the absolute cohomology of the total spaces is an isomorphism. -/
theorem isIso_fibTrivΨCoh (b : ℕ) (p : C(E, SphModel b)) (d_G : ↥(sphLoopBig b))
    (hT_G : FibrewiseTrivial p (sphLoopBig b) d_G) (k : ℕ) :
    CategoryTheory.IsIso (Work.Cohomology.singularCohomologyMap ℚ
      (TopCat.of (↥(sphLoopBig b) × wangFY b p d_G)) (wangEG b p)
      (TopCat.ofHom (fibTrivΨ p (sphLoopBig b) d_G hT_G)) k) := by
  refine Work.Cohomology.homotopyEquiv ℚ (TopCat.of (↥(sphLoopBig b) × wangFY b p d_G))
    (wangEG b p) (TopCat.ofHom (fibTrivΨ p (sphLoopBig b) d_G hT_G))
    (TopCat.ofHom (fibTrivΦ p (sphLoopBig b) d_G hT_G)) ?_ ?_ k
  · exact topCatHomotopyOf (X := TopCat.of (↥(sphLoopBig b) × wangFY b p d_G))
      (f := TopCat.ofHom (fibTrivΨ p (sphLoopBig b) d_G hT_G))
      (g := TopCat.ofHom (fibTrivΦ p (sphLoopBig b) d_G hT_G))
      (fibTrivK p (sphLoopBig b) d_G hT_G)
      (fibTrivK_zero p (sphLoopBig b) d_G hT_G)
      (fun y => fibTrivK_one p (sphLoopBig b) d_G hT_G y)
  · exact topCatHomotopyOf (X := wangEG b p)
      (f := TopCat.ofHom (fibTrivΦ p (sphLoopBig b) d_G hT_G))
      (g := TopCat.ofHom (fibTrivΨ p (sphLoopBig b) d_G hT_G))
      (fibTrivH p (sphLoopBig b) d_G hT_G)
      (fibTrivH_zero p (sphLoopBig b) d_G hT_G)
      (fun x => fibTrivH_one p (sphLoopBig b) d_G hT_G x)

/-- **`wangTriv` is an isomorphism on relative cohomology**: the five lemma applied to the
morphism of short exact sequences of the pairs. -/
theorem wangTriv_isIso (b : ℕ) (hb : 1 ≤ b) (E : Type) [TopologicalSpace E]
    (p : C(E, SphModel b)) (d_G : ↥(sphLoopBig b))
    (hT_G : FibrewiseTrivial p (sphLoopBig b) d_G) (k : ℕ) :
    CategoryTheory.IsIso (wangTriv b p d_G hT_G k) := by
  set φ := pairShortMap (X1 := TopCat.of (↥(sphLoopBig b) × wangFY b p d_G)) (X2 := wangEG b p)
    (wangCQ b p d_G) (wangA1 b p)
    (TopCat.ofHom (fibTrivΨ p (sphLoopBig b) d_G hT_G)) (wangTrivMap_mem b p d_G hT_G)
    with hφ
  have h₂ : ∀ n, CategoryTheory.IsIso (HomologicalComplex.homologyMap φ.τ₂ n) := by
    rw [hφ]
    intro n
    exact isIso_fibTrivΨCoh b p d_G hT_G n
  have h₃ : ∀ n, CategoryTheory.IsIso (HomologicalComplex.homologyMap φ.τ₃ n) := by
    rw [hφ]
    intro n
    exact Work.Cohomology.homotopyEquiv ℚ
      (TopCat.of (relB p (sphLoopBig b) d_G (sphLoopCollar b)))
      (TopCat.of (relA p (sphLoopBig b) (sphLoopCollar b)))
      (relΨA p (sphLoopBig b) d_G (sphLoopCollar b) hT_G)
      (relΦA p (sphLoopBig b) d_G (sphLoopCollar b) hT_G)
      (relHomotopyΨΦ p (sphLoopBig b) d_G (sphLoopCollar b) hT_G)
      (relHomotopyΦΨ p (sphLoopBig b) d_G (sphLoopCollar b) hT_G) n
  have hmain := Work.Cohomology.isIso_homologyMap_tau1 ℚ φ
    (Work.Cohomology.pairShort_shortExact ℚ (wangEG b p) (wangA1 b p))
    (Work.Cohomology.pairShort_shortExact ℚ (TopCat.of (↥(sphLoopBig b) × wangFY b p d_G))
      (wangCQ b p d_G)) h₂ h₃ k
  rw [hφ] at hmain
  exact hmain

end

end Work.StemsB.Rat
