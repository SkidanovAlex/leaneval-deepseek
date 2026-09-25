import Mathlib
import Submission.Work.CFT.ClassFormation.Defs
import Submission.Work.CFT.ClassFormation.Schur.DualityDefs
import Submission.Work.CFT.ClassFormation.Schur.finrank_homology_dualMap
import Submission.Work.CFT.ClassFormation.Schur.finrank_homology_add_finrank_range

/-!
# Field duality for group (co)homology

For a finite group `G` and a field `k`, the `k`-dimension of `Hⁿ(G, k)` equals that of
`Hₙ(G, k)` with trivial coefficients.  Both are computed from the bar resolution of the trivial
module `k`: the cochain complex `inhomogeneousCochains` is the `k`-linear dual of the chain
complex `inhomogeneousChains` (degreewise `(Fin n → G) → k` is the `k`-dual of
`(Fin n → G) →₀ k`), the differentials are transposes of each other (`psi_dCo`), and dualising
preserves the dimension count.
-/

open CategoryTheory

namespace Work.CFT.ClassFormation.Schur

noncomputable section

variable (k : Type) [Field k] (G : Type) [Group G] [Fintype G]

/-- The short complex `Cₙ₊₁ → Cₙ → Cₙ₋₁` of the inhomogeneous chains, computing `Hₙ`. -/
noncomputable abbrev Sc (n : ℕ) : ShortComplex (ModuleCat k) := (chainCx k G).sc' (n+1) n (n-1)

/-- The short complex `Cⁿ⁻¹ → Cⁿ → Cⁿ⁺¹` of the inhomogeneous cochains, computing `Hⁿ`. -/
noncomputable abbrev ScC (n : ℕ) : ShortComplex (ModuleCat k) := (cochainCx k G).sc' (n-1) n (n+1)

lemma Sc_f (n : ℕ) : (Sc k G n).f = (chainCx k G).d (n+1) n := rfl
lemma Sc_g (n : ℕ) : (Sc k G n).g = (chainCx k G).d n (n-1) := rfl
lemma ScC_f (n : ℕ) : (ScC k G n).f = (cochainCx k G).d (n-1) n := rfl
lemma ScC_g (n : ℕ) : (ScC k G n).g = (cochainCx k G).d n (n+1) := rfl

lemma Sc_f_hom (n : ℕ) : (Sc k G n).f.hom = dCh k G n := by
  rw [Sc_f, groupHomology.inhomogeneousChains.d_def]; rfl

lemma ScC_g_hom (n : ℕ) : (ScC k G n).g.hom = dCo k G n := by
  rw [ScC_g, groupCohomology.inhomogeneousCochains.d_def]; rfl

/-- `finrank` is preserved by an isomorphism in `ModuleCat`. -/
lemma finrank_iso {X Y : ModuleCat k} (e : X ≅ Y) :
    Module.finrank k ↥X = Module.finrank k ↥Y :=
  LinearEquiv.finrank_eq e.toLinearEquiv

/-- The homology of the inhomogeneous chain complex in degree `n` is the homology of the
concrete short complex `Cₙ₊₁ → Cₙ → Cₙ₋₁`. -/
lemma finrank_groupHomology_eq (n : ℕ) :
    Module.finrank k ↥(groupHomology (Rep.trivial k G k) n) =
      Module.finrank k ↥((Sc k G n).homology) :=
  finrank_iso k (ShortComplex.homologyMapIso
    (HomologicalComplex.isoSc' (chainCx k G) (n+1) n (n-1) (down_prev n) (down_next n)))

/-- The cohomology of the inhomogeneous cochain complex in degree `n` is the homology of the
concrete short complex `Cⁿ⁻¹ → Cⁿ → Cⁿ⁺¹`. -/
lemma finrank_groupCohomology_eq (n : ℕ) :
    Module.finrank k ↥(groupCohomology (Rep.trivial k G k) n) =
      Module.finrank k ↥((ScC k G n).homology) :=
  finrank_iso k (ShortComplex.homologyMapIso
    (HomologicalComplex.isoSc' (cochainCx k G) (n-1) n (n+1) (up_prev n) (up_next n)))

omit [Fintype G] in
/-- `Cⁿ` and `Cₙ` have the same `k`-dimension, both being `k^(#G)^n`. -/
lemma hdim (n : ℕ) :
    Module.finrank k ↥((cochainCx k G).X n) = Module.finrank k ↥((chainCx k G).X n) := by
  show Module.finrank k ((Fin n → G) → k) = Module.finrank k ((Fin n → G) →₀ k)
  rw [(psi k (Fin n → G)).finrank_eq, Subspace.dual_finrank_eq]

omit [Group G] [Fintype G] in
lemma finrank_range_zero {M N : Type} [AddCommGroup M] [Module k M]
    [AddCommGroup N] [Module k N] :
    Module.finrank k ↥(LinearMap.range (0 : M →ₗ[k] N)) = 0 := by
  rw [LinearMap.range_zero, Submodule.finrank_eq_zero]

/-- The cochain differential `d ⁿ` and the chain differential `∂ₙ₊₁` have images of the same
dimension (they are transposes of each other). -/
lemma finrank_range_dCo_eq (N : ℕ) :
    Module.finrank k ↥(LinearMap.range (dCo k G N)) =
      Module.finrank k ↥(LinearMap.range (dCh k G N)) := by
  have h : (psi k (Fin (N+1) → G)).toLinearMap.comp (dCo k G N)
      = (dCh k G N).dualMap.comp (psi k (Fin N → G)).toLinearMap := LinearMap.ext (psi_dCo k G N)
  have hrange : Submodule.map (psi k (Fin (N+1) → G)).toLinearMap (LinearMap.range (dCo k G N))
      = LinearMap.range (dCh k G N).dualMap := by
    rw [← LinearMap.range_comp, h, LinearMap.range_comp,
      LinearMap.range_eq_top.mpr (psi k (Fin N → G)).surjective, Submodule.map_top]
  have h1 : Module.finrank k ↥(LinearMap.range (dCo k G N)) =
      Module.finrank k ↥(Submodule.map (psi k (Fin (N+1) → G)).toLinearMap
        (LinearMap.range (dCo k G N))) :=
    LinearEquiv.finrank_eq ((psi k (Fin (N+1) → G)).submoduleMap (LinearMap.range (dCo k G N)))
  rw [h1, hrange, LinearMap.finrank_range_dualMap_eq_finrank_range]

/-- The cochain differential `d ⁿ⁻¹` and the chain differential `∂ₙ` have images of the same
dimension. -/
lemma finrank_range_prev (N : ℕ) :
    Module.finrank k ↥(LinearMap.range (((cochainCx k G).d (N-1) N).hom)) =
      Module.finrank k ↥(LinearMap.range (((chainCx k G).d N (N-1)).hom)) := by
  rcases N with _ | n
  · rw [show ((cochainCx k G).d ((0:ℕ)-1) 0) = 0 by
          rw [HomologicalComplex.shape _ _ _ (by simp [ComplexShape.up])]]
    rw [show ((chainCx k G).d 0 ((0:ℕ)-1)) = 0 by
          rw [HomologicalComplex.shape _ _ _ (by simp [ComplexShape.down])]]
    simp only [ModuleCat.hom_zero]
    rw [finrank_range_zero, finrank_range_zero]
  · have e1 : ((cochainCx k G).d n (n+1)).hom = dCo k G n := by
      rw [groupCohomology.inhomogeneousCochains.d_def]
    have e2 : ((chainCx k G).d (n+1) n).hom = dCh k G n := by
      rw [groupHomology.inhomogeneousChains.d_def]
    change Module.finrank k ↥(LinearMap.range (ModuleCat.Hom.hom ((cochainCx k G).d n (n+1)))) =
      Module.finrank k ↥(LinearMap.range (ModuleCat.Hom.hom ((chainCx k G).d (n+1) n)))
    rw [e1, e2, finrank_range_dCo_eq]

lemma range_Sc_f_eq (n : ℕ) :
    Module.finrank k ↥(LinearMap.range (Sc k G n).f.hom) =
      Module.finrank k ↥(LinearMap.range (ScC k G n).g.hom) := by
  rw [Sc_f_hom, ScC_g_hom]
  exact (finrank_range_dCo_eq k G n).symm

lemma range_Sc_g_eq (n : ℕ) :
    Module.finrank k ↥(LinearMap.range (Sc k G n).g.hom) =
      Module.finrank k ↥(LinearMap.range (ScC k G n).f.hom) := by
  rw [Sc_g, ScC_f]
  exact (finrank_range_prev k G n).symm

/-- The short complex `Cₙ₊₁ → Cₙ → Cₙ₋₁` is `moduleCatMk` of its two differentials. -/
noncomputable def mkScIso (n : ℕ) :
    ShortComplex.moduleCatMk (Sc k G n).f.hom (Sc k G n).g.hom
        (by have h := (Sc k G n).zero; rwa [ModuleCat.hom_ext_iff] at h) ≅ Sc k G n :=
  ShortComplex.isoMk (Iso.refl _) (Iso.refl _) (Iso.refl _) (by ext x; rfl) (by ext x; rfl)

noncomputable def mkScCIso (n : ℕ) :
    ShortComplex.moduleCatMk (ScC k G n).f.hom (ScC k G n).g.hom
        (by have h := (ScC k G n).zero; rwa [ModuleCat.hom_ext_iff] at h) ≅ ScC k G n :=
  ShortComplex.isoMk (Iso.refl _) (Iso.refl _) (Iso.refl _) (by ext x; rfl) (by ext x; rfl)

lemma Sc_add (n : ℕ) :
    Module.finrank k ↥((Sc k G n).homology) + Module.finrank k ↥(LinearMap.range (Sc k G n).f.hom)
      = Module.finrank k ↥(LinearMap.ker (Sc k G n).g.hom) := by
  haveI h1 : Module.Finite k ↥(Sc k G n).X₁ := by
    change Module.Finite k ((Fin (n+1) → G) →₀ k); infer_instance
  haveI h2 : Module.Finite k ↥(Sc k G n).X₂ := by
    change Module.Finite k ((Fin n → G) →₀ k); infer_instance
  have h := finrank_homology_add_finrank_range (Sc k G n).f.hom (Sc k G n).g.hom
    (by have hh := (Sc k G n).zero; rwa [ModuleCat.hom_ext_iff] at hh)
  rw [LinearEquiv.finrank_eq (ShortComplex.homologyMapIso (mkScIso k G n)).toLinearEquiv] at h
  exact h

lemma ScC_add (n : ℕ) :
    Module.finrank k ↥((ScC k G n).homology) +
      Module.finrank k ↥(LinearMap.range (ScC k G n).f.hom)
      = Module.finrank k ↥(LinearMap.ker (ScC k G n).g.hom) := by
  haveI h1 : Module.Finite k ↥(ScC k G n).X₁ := by
    change Module.Finite k ((Fin (n-1) → G) → k); infer_instance
  haveI h2 : Module.Finite k ↥(ScC k G n).X₂ := by
    change Module.Finite k ((Fin n → G) → k); infer_instance
  have h := finrank_homology_add_finrank_range (ScC k G n).f.hom (ScC k G n).g.hom
    (by have hh := (ScC k G n).zero; rwa [ModuleCat.hom_ext_iff] at hh)
  rw [LinearEquiv.finrank_eq (ShortComplex.homologyMapIso (mkScCIso k G n)).toLinearEquiv] at h
  exact h

lemma Sc_ker_add (n : ℕ) :
    Module.finrank k ↥(LinearMap.ker (Sc k G n).g.hom) +
      Module.finrank k ↥(LinearMap.range (Sc k G n).g.hom)
      = Module.finrank k ↥((chainCx k G).X n) := by
  haveI : FiniteDimensional k ↥(Sc k G n).X₂ := by
    change FiniteDimensional k ((Fin n → G) →₀ k); infer_instance
  rw [add_comm]
  exact LinearMap.finrank_range_add_finrank_ker (Sc k G n).g.hom

lemma ScC_ker_add (n : ℕ) :
    Module.finrank k ↥(LinearMap.ker (ScC k G n).g.hom) +
      Module.finrank k ↥(LinearMap.range (ScC k G n).g.hom)
      = Module.finrank k ↥((cochainCx k G).X n) := by
  haveI : FiniteDimensional k ↥(ScC k G n).X₂ := by
    change FiniteDimensional k ((Fin n → G) → k); infer_instance
  rw [add_comm]
  exact LinearMap.finrank_range_add_finrank_ker (ScC k G n).g.hom

end

/-- **Field duality for group (co)homology.**  For a finite group `G` and a field `k`, the
`k`-dimension of the `n`-th group cohomology with trivial coefficients `k` equals that of the
`n`-th group homology.  Both are computed from the bar resolution of the trivial module `k`; over
a field the complex of inhomogeneous cochains `inhomogeneousCochains (Rep.trivial k G k)` is the
`k`-linear dual of the complex of inhomogeneous chains
`inhomogeneousChains (Rep.trivial k G k)` (degreewise `(Fin n → G) → k` is the `k`-dual of
`(Fin n → G) →₀ k`), and dualising a complex of finite-dimensional `k`-vector spaces preserves
homology dimensions.  Suggested route: exhibit the degreewise `k`-linear equivalence
`((Fin n → G) →₀ k) →ₗ[k] k ≃ₗ[k] ((Fin n → G) → k)`, check it intertwines the two differentials
(up to sign), then use that for a complex `C` of finite-dimensional spaces
`finrank k (H^n(Hom_k(C,k))) = finrank k (H_n(C))`. -/
theorem finrank_groupCohomology_eq_finrank_groupHomology
    (k : Type) [Field k] (G : Type) [Group G] [Fintype G] (n : ℕ) :
    Module.finrank k (groupCohomology (Rep.trivial k G k) n) =
    Module.finrank k (groupHomology (Rep.trivial k G k) n) := by
  rw [finrank_groupCohomology_eq, finrank_groupHomology_eq]
  have e1 : Module.finrank k ↥((Sc k G n).homology)
      + Module.finrank k ↥(LinearMap.range (Sc k G n).f.hom)
      + Module.finrank k ↥(LinearMap.range (Sc k G n).g.hom)
      = Module.finrank k ↥((chainCx k G).X n) := by
    rw [Sc_add k G n, Sc_ker_add k G n]
  have e2 : Module.finrank k ↥((ScC k G n).homology)
      + Module.finrank k ↥(LinearMap.range (ScC k G n).f.hom)
      + Module.finrank k ↥(LinearMap.range (ScC k G n).g.hom)
      = Module.finrank k ↥((chainCx k G).X n) := by
    rw [ScC_add k G n, ScC_ker_add k G n, hdim k G n]
  rw [← range_Sc_g_eq k G n, ← range_Sc_f_eq k G n] at e2
  omega

end Work.CFT.ClassFormation.Schur
