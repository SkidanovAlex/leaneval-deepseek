import Submission.Work.Cohomology.dualComplex_acyclic_of_acyclic
import Submission.Work.Serre.Engine

/-!
# The universal coefficient theorem over a field, in one degree

Let `k` be a field and `C` a chain complex of `k`-vector spaces whose homology vanishes in a
*single* degree `n`.  Then the cohomology of the dual cochain complex `Hom_k(C, k)` vanishes in
degree `n` as well.

This is the one-degree form of `Work.Cohomology.dualComplex_acyclic_of_acyclic` (`Work.Cohomology`
proves the all-degrees form); the proof only ever uses the hypothesis in the degree in question, so
the single-degree form is the same argument with the hypothesis instantiated.

Why it matters here: the engine of subproject SERRE produces *homological* vanishing (for instance
`Work.Serre.SerreE0Range`: `πᵢ = 0` for `i ≤ N` gives `H̃ᵢ(-;ℚ) = 0` for `i ≤ N`), whereas the
computations of the `K(ℤ,n)` layer (`C2`, and the lead's corrected `E4`) are phrased in
*cohomology*; over `ℚ` the two are interchangeable degree by degree, and this is the direction that
turns homology vanishing into cohomology vanishing.  For `Work.Serre.ratCoh` this reads
`Work.Stems.Engine.isZero_ratCoh_of_isZero_ratH` below.
-/

namespace Work.Stems.Engine

noncomputable section

open CategoryTheory CategoryTheory.Limits
open Work.Cohomology

/-- **One-degree dual universal coefficient theorem over a field.**  If `Hₙ(C) = 0` for a chain
complex of `k`-vector spaces then `Hⁿ(Hom_k(C,k)) = 0`. -/
theorem isZero_dualComplex_homology_of_isZero_homology (k : Type) [Field k]
    (C : ChainComplex (ModuleCat k) ℕ) (n : ℕ)
    (hn : IsZero (C.homology n)) :
    IsZero ((Work.Cohomology.dualComplex k C).homology n) := by
  rw [← HomologicalComplex.exactAt_iff_isZero_homology]
  rcases n with _ | m
  · -- degree `0`: the outgoing differential of `C` is onto, so its transpose is injective
    have hEx0 : C.ExactAt 0 :=
      (HomologicalComplex.exactAt_iff_isZero_homology C 0).mpr hn
    rw [C.exactAt_iff' 1 0 0
      (ComplexShape.prev_eq' _ (show (ComplexShape.down ℕ).Rel 1 0 from rfl))
      (ComplexShape.next_eq_self' _ 0 (fun j h => by
        have h' : j + 1 = 0 := h
        omega))] at hEx0
    have hg0 : (C.sc' 1 0 0).g = 0 := by
      rw [show (C.sc' 1 0 0).g = C.d 0 0 from rfl]
      exact HomologicalComplex.shape C 0 0 (fun h => by
        have h' : 0 + 1 = 0 := h
        omega)
    have hepi : Epi (C.sc' 1 0 0).f := (ShortComplex.exact_iff_epi _ hg0).mp hEx0
    have hsurj : Function.Surjective (ModuleCat.Hom.hom (C.d 1 0)) := by
      have h := (ModuleCat.epi_iff_surjective ((C.sc' 1 0 0).f)).mp hepi
      rw [show (C.sc' 1 0 0).f = C.d 1 0 from rfl] at h
      exact h
    rw [HomologicalComplex.exactAt_iff' (dualComplex k C) 0 0 1
      (ComplexShape.prev_eq_self' _ 0 (fun j h => by
        have h' : j + 1 = 0 := h
        omega))
      (ComplexShape.next_eq' _ (show (ComplexShape.up ℕ).Rel 0 1 from rfl))]
    have hf0 : ((dualComplex k C).sc' 0 0 1).f = 0 := by
      rw [show ((dualComplex k C).sc' 0 0 1).f = (dualComplex k C).d 0 0 from rfl]
      exact dualComplex_d_zero k C
    refine (ShortComplex.exact_iff_mono _ hf0).mpr ?_
    have hg : ((dualComplex k C).sc' 0 0 1).g = dualDiff k C 0 := by
      rw [show ((dualComplex k C).sc' 0 0 1).g = (dualComplex k C).d 0 1 from rfl]
      exact dualComplex_d_succ k C 0
    rw [hg]
    have hinj : Function.Injective (ModuleCat.Hom.hom (dualDiff k C 0)) := by
      rw [dualDiff_hom k C 0]
      exact LinearMap.dualMap_injective_of_surjective hsurj
    exact (ModuleCat.mono_iff_injective _).mpr hinj
  · -- degree `m+1`: dualise the exact sequence `C_{m+2} → C_{m+1} → C_m`
    have hEx : C.ExactAt (m+1) :=
      (HomologicalComplex.exactAt_iff_isZero_homology C (m+1)).mpr hn
    rw [C.exactAt_iff' (m+2) (m+1) m
      (ComplexShape.prev_eq' _ (show (ComplexShape.down ℕ).Rel (m+2) (m+1) from rfl))
      (ComplexShape.next_eq' _ (show (ComplexShape.down ℕ).Rel (m+1) m from rfl))] at hEx
    have hker : LinearMap.range (ModuleCat.Hom.hom (C.d (m+2) (m+1)))
        = LinearMap.ker (ModuleCat.Hom.hom (C.d (m+1) m)) :=
      (ShortComplex.moduleCat_exact_iff_range_eq_ker (C.sc' (m+2) (m+1) m)).mp hEx
    have hdual : LinearMap.range (dualDiff k C m).hom
        = LinearMap.ker (dualDiff k C (m+1)).hom := by
      have h := range_dualMap_of_range_eq_ker k hker
      rw [← dualDiff_hom k C m, ← dualDiff_hom k C (m+1)] at h
      exact h
    rw [HomologicalComplex.exactAt_iff' (dualComplex k C) m (m+1) (m+2)
      (ComplexShape.prev_eq' _ (show (ComplexShape.up ℕ).Rel m (m+1) from rfl))
      (ComplexShape.next_eq' _ (show (ComplexShape.up ℕ).Rel (m+1) (m+2) from rfl))]
    have hf : ((dualComplex k C).sc' m (m+1) (m+2)).f = dualDiff k C m := by
      rw [show ((dualComplex k C).sc' m (m+1) (m+2)).f = (dualComplex k C).d m (m+1) from rfl]
      exact dualComplex_d_succ k C m
    have hg : ((dualComplex k C).sc' m (m+1) (m+2)).g = dualDiff k C (m+1) := by
      rw [show ((dualComplex k C).sc' m (m+1) (m+2)).g = (dualComplex k C).d (m+1) (m+2)
        from rfl]
      exact dualComplex_d_succ k C (m+1)
    refine (ShortComplex.moduleCat_exact_iff_range_eq_ker
      ((dualComplex k C).sc' m (m+1) (m+2))).mpr ?_
    rw [hf, hg]
    exact hdual
/-- **Vanishing of rational singular homology transfers to `Work.Serre.ratCoh`.**  The rational
singular cohomology of `X` is the cohomology of the dual of the rational singular chain complex
(`Work.Cohomology.dualComplex_singularChains`), so the one-degree dual universal coefficient
theorem applies. -/
theorem isZero_ratCoh_of_isZero_ratH (X : TopCat) (n : ℕ)
    (h : IsZero ((Work.Cohomology.singularChains ℚ X).homology n)) :
    IsZero (Work.Serre.ratCoh X n) :=
  isZero_dualComplex_homology_of_isZero_homology ℚ (Work.Cohomology.singularChains ℚ X) n h

/-! ## The reflected (faithful) direction -/

/-- **Dual exactness over a field, reflected.**  For linear maps `f : U → V`, `g : V → W` with
`g ∘ f = 0`: if the transposed pair is exact (`range gᵀ = ker fᵀ`), then the original pair is exact
(`range f = ker g`).  Over a field `Hom_k(-,k)` is *faithful* as well as exact: a vector not in the
range of `f` is separated from it by a functional, and every functional vanishing on `range f` comes
from `range gᵀ = ker fᵀ`, hence kills everything in `ker g`. -/
theorem range_eq_ker_of_range_dualMap_eq_ker_dualMap (k : Type) [Field k]
    {U V W : Type*} [AddCommGroup U] [Module k U] [AddCommGroup V] [Module k V]
    [AddCommGroup W] [Module k W] (f : U →ₗ[k] V) (g : V →ₗ[k] W) (hfg : g.comp f = 0)
    (h : LinearMap.range g.dualMap = LinearMap.ker f.dualMap) :
    LinearMap.range f = LinearMap.ker g := by
  refine le_antisymm ?_ ?_
  · rintro _ ⟨u, rfl⟩
    exact LinearMap.mem_ker.mpr (by
      have h2 := congrArg (fun (l : U →ₗ[k] W) => l u) hfg
      simpa using h2)
  · intro z hz
    -- every functional vanishing on `range f` also vanishes on `span {z}`
    have hann : (LinearMap.range f ⊔ Submodule.span k {z}).dualAnnihilator
        = (LinearMap.range f).dualAnnihilator := by
      refine le_antisymm ?_ ?_
      · exact Submodule.dualAnnihilator_anti le_sup_left
      · intro φ hφ
        rw [Submodule.mem_dualAnnihilator] at hφ ⊢
        have hgz : g z = 0 := LinearMap.mem_ker.mp hz
        have hφ' : φ ∈ LinearMap.ker f.dualMap := by
          rw [LinearMap.ker_dualMap_eq_dualAnnihilator_range, Submodule.mem_dualAnnihilator]
          exact hφ
        rw [← h] at hφ'
        obtain ⟨ψ, hψ⟩ := hφ'
        intro w hw
        have hle : LinearMap.range f ⊔ Submodule.span k {z} ≤ LinearMap.ker φ := by
          refine sup_le ?_ ?_
          · intro u hu
            exact LinearMap.mem_ker.mpr (hφ u hu)
          · intro v hv
            rw [Submodule.mem_span_singleton] at hv
            obtain ⟨a, rfl⟩ := hv
            refine LinearMap.mem_ker.mpr ?_
            calc φ (a • z) = (g.dualMap ψ) (a • z) := by rw [hψ]
              _ = ψ (g (a • z)) := rfl
              _ = ψ (a • g z) := by rw [map_smul]
              _ = 0 := by rw [hgz, smul_zero, map_zero]
        exact hle hw
    have hEq : LinearMap.range f ⊔ Submodule.span k {z} = LinearMap.range f :=
      Subspace.dualAnnihilator_inj.mp hann
    have hz' : z ∈ LinearMap.range f ⊔ Submodule.span k {z} :=
      Submodule.mem_sup_right (Submodule.mem_span_singleton_self z)
    rw [hEq] at hz'
    exact hz'

/-- **One-degree dual universal coefficient theorem over a field, converse direction.**  If the
cohomology of the dual complex vanishes in degree `n ≥ 1` then so does the homology of `C` in that
degree.  (The case `n = 0` is the statement that over a field the transpose of a linear map is
injective iff the map is surjective; it is not needed below, where the homology in degree `0` of the
spaces involved is known from connectivity.) -/
theorem isZero_homology_of_isZero_dualComplex_homology (k : Type) [Field k]
    (C : ChainComplex (ModuleCat k) ℕ) (n : ℕ) (hn : 1 ≤ n)
    (h : IsZero ((Work.Cohomology.dualComplex k C).homology n)) :
    IsZero (C.homology n) := by
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
  rw [← HomologicalComplex.exactAt_iff_isZero_homology]
  -- exactness of the dual in degree `m+1` is the exactness of the transposed pair
  have hEx : (Work.Cohomology.dualComplex k C).ExactAt (m+1) :=
    (HomologicalComplex.exactAt_iff_isZero_homology (Work.Cohomology.dualComplex k C) (m+1)).mpr h
  rw [HomologicalComplex.exactAt_iff' (Work.Cohomology.dualComplex k C) m (m+1) (m+2)
    (ComplexShape.prev_eq' _ (show (ComplexShape.up ℕ).Rel m (m+1) from rfl))
    (ComplexShape.next_eq' _ (show (ComplexShape.up ℕ).Rel (m+1) (m+2) from rfl))] at hEx
  have hf : ((Work.Cohomology.dualComplex k C).sc' m (m+1) (m+2)).f
      = Work.Cohomology.dualDiff k C m := by
    rw [show ((Work.Cohomology.dualComplex k C).sc' m (m+1) (m+2)).f
      = (Work.Cohomology.dualComplex k C).d m (m+1) from rfl]
    exact Work.Cohomology.dualComplex_d_succ k C m
  have hg : ((Work.Cohomology.dualComplex k C).sc' m (m+1) (m+2)).g
      = Work.Cohomology.dualDiff k C (m+1) := by
    rw [show ((Work.Cohomology.dualComplex k C).sc' m (m+1) (m+2)).g
      = (Work.Cohomology.dualComplex k C).d (m+1) (m+2) from rfl]
    exact Work.Cohomology.dualComplex_d_succ k C (m+1)
  have hrange : LinearMap.range (ModuleCat.Hom.hom (Work.Cohomology.dualDiff k C m))
      = LinearMap.ker (ModuleCat.Hom.hom (Work.Cohomology.dualDiff k C (m+1))) := by
    have h' := (ShortComplex.moduleCat_exact_iff_range_eq_ker
      ((Work.Cohomology.dualComplex k C).sc' m (m+1) (m+2))).mp hEx
    rw [hf, hg] at h'
    exact h'
  -- rewrite the transposed differentials as transposes of the differentials of `C`
  rw [Work.Cohomology.dualDiff_hom k C m,
    Work.Cohomology.dualDiff_hom k C (m+1)] at hrange
  -- the differentials of `C` compose to zero
  have hfg : (ModuleCat.Hom.hom (C.d (m+1) m)).comp
      (ModuleCat.Hom.hom (C.d (m+2) (m+1))) = 0 := by
    have h := congrArg ModuleCat.Hom.hom (HomologicalComplex.d_comp_d C (m+2) (m+1) m)
    simpa only [ModuleCat.hom_comp, ModuleCat.hom_zero] using h
  have hker : LinearMap.range (ModuleCat.Hom.hom (C.d (m+2) (m+1)))
      = LinearMap.ker (ModuleCat.Hom.hom (C.d (m+1) m)) :=
    range_eq_ker_of_range_dualMap_eq_ker_dualMap k _ _ hfg hrange
  rw [C.exactAt_iff' (m+2) (m+1) m
    (ComplexShape.prev_eq' _ (show (ComplexShape.down ℕ).Rel (m+2) (m+1) from rfl))
    (ComplexShape.next_eq' _ (show (ComplexShape.down ℕ).Rel (m+1) m from rfl))]
  exact (ShortComplex.moduleCat_exact_iff_range_eq_ker (C.sc' (m+2) (m+1) m)).mpr hker

/-- **`Work.Serre.ratCoh` vanishing gives homology vanishing** in positive degrees (the converse of
`isZero_ratCoh_of_isZero_ratH`), for the same reason: the rational cochains are the dual of the
rational chains over the field `ℚ`. -/
theorem isZero_ratH_of_isZero_ratCoh (X : TopCat) (n : ℕ) (hn : 1 ≤ n)
    (h : IsZero (Work.Serre.ratCoh X n)) :
    IsZero ((Work.Cohomology.singularChains ℚ X).homology n) :=
  isZero_homology_of_isZero_dualComplex_homology ℚ (Work.Cohomology.singularChains ℚ X) n hn h

end

end Work.Stems.Engine
