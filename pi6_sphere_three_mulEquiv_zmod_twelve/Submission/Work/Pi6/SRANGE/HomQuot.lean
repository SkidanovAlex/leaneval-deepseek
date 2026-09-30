import Mathlib
import Submission.Work.Pi6.SRANGE.Defs
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false  -- v435port
set_option backward.isDefEq.respectTransparency.types false  -- v435port

/-!
# The concrete model `Zᵢ ⧸ Bᵢ` of the homology of a chain complex of `R`-modules

This file defines the concrete quotient of cycles by boundaries that models the homology of a
chain complex `K` of `R`-modules, together with the map induced on it by a chain map.
-/

set_option backward.isDefEq.respectTransparency false

open CategoryTheory CategoryTheory.Limits HomologicalComplex
open scoped TensorProduct

namespace Work.Pi6.SRANGE

noncomputable section

/-- The concrete quotient of cycles by boundaries modelling `H_i(K)` for a chain complex of
`R`-modules.  `homQuot R K i` is `ker (d i (i-1))` modulo the preimage in it of the boundaries. -/
abbrev homQuot (R : Type) [CommRing R] (K : ChainComplex (ModuleCat.{0} R) ℕ) (i : ℕ) : Type :=
  ↥(LinearMap.ker (K.d i (i-1)).hom) ⧸
    (LinearMap.range (K.d (i+1) i).hom).comap (LinearMap.ker (K.d i (i-1)).hom).subtype

/-- The map on the concrete quotients induced by a chain map. -/
noncomputable def homQuotMap (R : Type) [CommRing R] {K L : ChainComplex (ModuleCat.{0} R) ℕ}
    (h : K ⟶ L) (i : ℕ) : homQuot R K i →ₗ[R] homQuot R L i :=
  Submodule.mapQ _ _
    (LinearMap.restrict (h.f i).hom (p := LinearMap.ker (K.d i (i-1)).hom)
      (q := LinearMap.ker (L.d i (i-1)).hom)
      (by
        intro x hx
        simp only [LinearMap.mem_ker] at hx ⊢
        have hc := congrArg (fun (g : K.X i ⟶ L.X (i-1)) => g.hom x) (h.comm i (i-1))
        simp only [ModuleCat.hom_comp, LinearMap.comp_apply] at hc
        rw [hc, hx, map_zero]))
    (by
      intro y hy
      obtain ⟨w, hw⟩ := LinearMap.mem_range.mp (Submodule.mem_comap.mp hy)
      refine Submodule.mem_comap.mpr (LinearMap.mem_range.mpr ⟨(h.f (i+1)).hom w, ?_⟩)
      have hc := congrArg (fun (g : K.X (i+1) ⟶ L.X i) => g.hom w) (h.comm (i+1) i)
      simp only [ModuleCat.hom_comp, LinearMap.comp_apply] at hc
      show (ModuleCat.Hom.hom (L.d (i+1) i)) ((ModuleCat.Hom.hom (h.f (i+1))) w)
        = (ModuleCat.Hom.hom (h.f i)) (↑y : K.X i)
      have hy' : (↑y : K.X i) = (K.d (i+1) i).hom w := hw.symm
      rw [hy', hc])

end

end Work.Pi6.SRANGE
