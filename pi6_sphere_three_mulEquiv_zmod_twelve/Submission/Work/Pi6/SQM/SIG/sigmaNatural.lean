import Mathlib
import Submission.Work.Pi6.SQM.SIG.sigmaNaturalDefs
import Submission.Work.Pi6.SQM.SIG.rhoNatural
import Submission.Work.Pi6.SQM.SIG.qStarNatural
import Submission.Work.Pi6.SQM.SIG.fibreSquare
import Submission.Work.Pi6.SQM.SIG.pairDeltaNatural
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false  -- v435port
set_option backward.isDefEq.respectTransparency.types false  -- v435port

set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 4000000
set_option linter.style.haveILetI false

open CategoryTheory Limits AlgebraicTopology Work.Cohomology
open scoped Simplicial

namespace Work.Pi6.SQM.SIG

noncomputable section

/-- **Naturality of `δ⁻¹`** (the inverse of the connecting map of the path–loop pair).
`δ` is natural in the map of pairs `(PK K, fibre K) → (PK L, fibre L)` induced by `h`
(`pairDeltaNatural`), and the identification `H^*(fibre) ≅ H^*(ΩK)` is compatible with `Ωh`
(`fibreSquare`). -/
theorem deltaNatural (K L : Type) [TopologicalSpace K] [TopologicalSpace L] (k₀ : K) (h : C(K, L))
    (Ωh : C(Path k₀ k₀, Path (h k₀) (h k₀))) (hΩh : ∀ γ t, Ωh γ t = h (γ t)) (n : ℕ) :
    CategoryTheory.CategoryStruct.comp
        (HomologicalComplex.homologyMap (pathPairMap K L k₀ h) (n + 2)) (deltaInv K k₀ n)
      = CategoryTheory.CategoryStruct.comp (deltaInv L (h k₀) n)
        (Work.Pi6.cmap Work.Pi6.SQ.F2 Ωh (n + 1)) := by
  have hE := pairDeltaNatural K L k₀ h n
  have hD := fibreSquare K L k₀ h Ωh hΩh (n+1)
  haveI hK : IsIso (pairδ Work.Pi6.SQ.F2 (TopCat.of (PK K k₀)) (fibreSet K k₀) (n + 1)) :=
    isIso_pairδ K k₀ n
  haveI hL : IsIso (pairδ Work.Pi6.SQ.F2 (TopCat.of (PK L (h k₀))) (fibreSet L (h k₀)) (n + 1)) :=
    isIso_pairδ L (h k₀) n
  have hE' : CategoryTheory.CategoryStruct.comp
        (asIso (pairδ Work.Pi6.SQ.F2 (TopCat.of (PK L (h k₀))) (fibreSet L (h k₀)) (n+1))).hom
        (HomologicalComplex.homologyMap (pathPairMap K L k₀ h) (n + 2))
      = CategoryTheory.CategoryStruct.comp
        (HomologicalComplex.homologyMap (Work.Cohomology.dualChainMap Work.Pi6.SQ.F2
          (TopCat.of ↥(fibreSet K k₀)) (TopCat.of ↥(fibreSet L (h k₀))) (fibreMap K L k₀ h)) (n + 1))
        (asIso (pairδ Work.Pi6.SQ.F2 (TopCat.of (PK K k₀)) (fibreSet K k₀) (n+1))).hom := by
    simpa only [asIso_hom] using hE
  have h2 : CategoryTheory.CategoryStruct.comp
        (HomologicalComplex.homologyMap (pathPairMap K L k₀ h) (n + 2))
        (asIso (pairδ Work.Pi6.SQ.F2 (TopCat.of (PK K k₀)) (fibreSet K k₀) (n+1))).inv
      = CategoryTheory.CategoryStruct.comp
        (asIso (pairδ Work.Pi6.SQ.F2 (TopCat.of (PK L (h k₀))) (fibreSet L (h k₀)) (n+1))).inv
        (HomologicalComplex.homologyMap (Work.Cohomology.dualChainMap Work.Pi6.SQ.F2
          (TopCat.of ↥(fibreSet K k₀)) (TopCat.of ↥(fibreSet L (h k₀))) (fibreMap K L k₀ h)) (n + 1)) := by
    rw [Iso.comp_inv_eq]
    rw [Category.assoc, ← hE', Iso.inv_hom_id_assoc]
  have hD' : CategoryTheory.CategoryStruct.comp
        (HomologicalComplex.homologyMap (Work.Cohomology.dualChainMap Work.Pi6.SQ.F2
          (TopCat.of ↥(fibreSet K k₀)) (TopCat.of ↥(fibreSet L (h k₀))) (fibreMap K L k₀ h)) (n + 1))
        ((fibreCohIso K k₀ (n + 1)).inv)
      = CategoryTheory.CategoryStruct.comp ((fibreCohIso L (h k₀) (n + 1)).inv)
        (Work.Pi6.cmap Work.Pi6.SQ.F2 Ωh (n + 1)) := hD
  calc CategoryTheory.CategoryStruct.comp
        (HomologicalComplex.homologyMap (pathPairMap K L k₀ h) (n + 2)) (deltaInv K k₀ n)
      = CategoryTheory.CategoryStruct.comp
          (CategoryTheory.CategoryStruct.comp
            (HomologicalComplex.homologyMap (pathPairMap K L k₀ h) (n + 2))
            (asIso (pairδ Work.Pi6.SQ.F2 (TopCat.of (PK K k₀)) (fibreSet K k₀) (n+1))).inv)
          ((fibreCohIso K k₀ (n + 1)).inv) := by
        rw [deltaInv]
        rw [← Category.assoc]
    _ = CategoryTheory.CategoryStruct.comp
          (CategoryTheory.CategoryStruct.comp
            (asIso (pairδ Work.Pi6.SQ.F2 (TopCat.of (PK L (h k₀))) (fibreSet L (h k₀)) (n+1))).inv
            (HomologicalComplex.homologyMap (Work.Cohomology.dualChainMap Work.Pi6.SQ.F2
              (TopCat.of ↥(fibreSet K k₀)) (TopCat.of ↥(fibreSet L (h k₀))) (fibreMap K L k₀ h)) (n + 1)))
          ((fibreCohIso K k₀ (n + 1)).inv) := by rw [h2]
    _ = CategoryTheory.CategoryStruct.comp
          (asIso (pairδ Work.Pi6.SQ.F2 (TopCat.of (PK L (h k₀))) (fibreSet L (h k₀)) (n+1))).inv
          (CategoryTheory.CategoryStruct.comp
            (HomologicalComplex.homologyMap (Work.Cohomology.dualChainMap Work.Pi6.SQ.F2
              (TopCat.of ↥(fibreSet K k₀)) (TopCat.of ↥(fibreSet L (h k₀))) (fibreMap K L k₀ h)) (n + 1))
            ((fibreCohIso K k₀ (n + 1)).inv)) := by rw [Category.assoc]
    _ = CategoryTheory.CategoryStruct.comp
          (asIso (pairδ Work.Pi6.SQ.F2 (TopCat.of (PK L (h k₀))) (fibreSet L (h k₀)) (n+1))).inv
          (CategoryTheory.CategoryStruct.comp ((fibreCohIso L (h k₀) (n + 1)).inv)
            (Work.Pi6.cmap Work.Pi6.SQ.F2 Ωh (n + 1))) := by rw [hD']
    _ = CategoryTheory.CategoryStruct.comp (deltaInv L (h k₀) n)
          (Work.Pi6.cmap Work.Pi6.SQ.F2 Ωh (n + 1)) := by
        rw [deltaInv]
        rw [Category.assoc]

/-- Naturality of the cohomology suspension.  `σ = δ⁻¹ ∘ q* ∘ ρ` is natural because `ρ` is the
inverse of `relIncl*` (naturality of `relIncl` + functoriality of `relComplexMap`), `q*` is the map
of pairs induced by `h` (`relComplexMap` functoriality), and `δ` is natural (`pairδ` naturality);
the fibre identification is the homeomorphism `fibre ≃ Path • •`, compatible with `Ωh` by
hypothesis. -/
theorem sigmaNatural (h1 : Work.Pi6.SQM.Cup1Cob) (h2 : Work.Pi6.SQM.Cup2Cob)
    (h3 : Work.Pi6.SQM.Cup3Cob) (hN : Work.Pi6.SQM.CupINatural)
    (K L : Type) [TopologicalSpace K] [TopologicalSpace L] (k₀ : K) (h : C(K, L))
    (Ωh : C(Path k₀ k₀, Path (h k₀) (h k₀)))
    (hΩh : ∀ γ t, Ωh γ t = h (γ t)) (n : ℕ) (z : Work.Pi6.Coh Work.Pi6.SQ.F2 L (n + 1)) :
    Work.Pi6.SQM.SIG.sigma K k₀ n (Work.Pi6.cmap Work.Pi6.SQ.F2 h (n + 1) z) =
      Work.Pi6.cmap Work.Pi6.SQ.F2 Ωh n (Work.Pi6.SQM.SIG.sigma L (h k₀) n z) := by
  match n with
  | 0 => simp [sigma]
  | (m + 1) =>
    have hmain : CategoryTheory.CategoryStruct.comp (Work.Pi6.cmap Work.Pi6.SQ.F2 h (m + 2))
        (rhoLM K k₀ m ≫ qStarLM K k₀ (m + 2) ≫ deltaInv K k₀ m)
        = CategoryTheory.CategoryStruct.comp
          (rhoLM L (h k₀) m ≫ qStarLM L (h k₀) (m + 2) ≫ deltaInv L (h k₀) m)
          (Work.Pi6.cmap Work.Pi6.SQ.F2 Ωh (m + 1)) := by
      calc CategoryTheory.CategoryStruct.comp (Work.Pi6.cmap Work.Pi6.SQ.F2 h (m + 2))
            (rhoLM K k₀ m ≫ qStarLM K k₀ (m + 2) ≫ deltaInv K k₀ m)
          = CategoryTheory.CategoryStruct.comp
              (CategoryTheory.CategoryStruct.comp (Work.Pi6.cmap Work.Pi6.SQ.F2 h (m + 2)) (rhoLM K k₀ m))
              (qStarLM K k₀ (m + 2) ≫ deltaInv K k₀ m) := by
              rw [Category.assoc]
        _ = CategoryTheory.CategoryStruct.comp
              (CategoryTheory.CategoryStruct.comp (rhoLM L (h k₀) m)
                (HomologicalComplex.homologyMap (basePairMap K L k₀ h) (m + 2)))
              (qStarLM K k₀ (m + 2) ≫ deltaInv K k₀ m) := by rw [rhoNatural K L k₀ h m]
        _ = CategoryTheory.CategoryStruct.comp (rhoLM L (h k₀) m)
              (CategoryTheory.CategoryStruct.comp
                (CategoryTheory.CategoryStruct.comp
                  (HomologicalComplex.homologyMap (basePairMap K L k₀ h) (m + 2))
                  (qStarLM K k₀ (m + 2)))
                (deltaInv K k₀ m)) := by simp only [Category.assoc]
        _ = CategoryTheory.CategoryStruct.comp (rhoLM L (h k₀) m)
              (CategoryTheory.CategoryStruct.comp
                (CategoryTheory.CategoryStruct.comp (qStarLM L (h k₀) (m + 2))
                  (HomologicalComplex.homologyMap (pathPairMap K L k₀ h) (m + 2)))
                (deltaInv K k₀ m)) := by rw [qStarNatural K L k₀ h m]
        _ = CategoryTheory.CategoryStruct.comp
              (CategoryTheory.CategoryStruct.comp (rhoLM L (h k₀) m) (qStarLM L (h k₀) (m + 2)))
              (CategoryTheory.CategoryStruct.comp
                (HomologicalComplex.homologyMap (pathPairMap K L k₀ h) (m + 2))
                (deltaInv K k₀ m)) := by simp only [Category.assoc]
        _ = CategoryTheory.CategoryStruct.comp
              (CategoryTheory.CategoryStruct.comp (rhoLM L (h k₀) m) (qStarLM L (h k₀) (m + 2)))
              (CategoryTheory.CategoryStruct.comp (deltaInv L (h k₀) m)
                (Work.Pi6.cmap Work.Pi6.SQ.F2 Ωh (m + 1))) := by
              rw [deltaNatural K L k₀ h Ωh hΩh m]
        _ = CategoryTheory.CategoryStruct.comp
              (rhoLM L (h k₀) m ≫ qStarLM L (h k₀) (m + 2) ≫ deltaInv L (h k₀) m)
              (Work.Pi6.cmap Work.Pi6.SQ.F2 Ωh (m + 1)) := by simp only [Category.assoc]
    have hz := LinearMap.congr_fun (congrArg ModuleCat.Hom.hom hmain) z
    simpa only [ModuleCat.hom_comp, LinearMap.comp_apply, sigma] using hz

end

end Work.Pi6.SQM.SIG
