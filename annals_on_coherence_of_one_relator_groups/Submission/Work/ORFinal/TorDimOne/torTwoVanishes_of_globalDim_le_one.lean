import Mathlib
import Submission.Work.ORCoherence.Main
import Submission.Work.ORCoherence.Presentation
import Submission.Work.ORCoherence.Tensor.balanced_map_comp

/-!
# `Tor₂^R(S, -) = 0` for `R` of global dimension at most one

If `R` has (left) global dimension at most one, then every left `R`-module has projective
dimension at most one, so `Tor₂^R(S, M) = 0` for every left `R`-module `M` and every ring
homomorphism `f : R →+* S`.  In the concrete form in which the vanishing is used
(`Work.ORCoherence.TorTwoVanishes`), this says: for every exact sequence
`0 → P₂ → P₁ → P₀ → M → 0` of left `R`-modules with `P₂`, `P₁`, `P₀` projective, the induced
map `S ⊗[R] P₂ → S ⊗[R] P₁` is injective.

The proof is the hereditary-ring argument.  Since every module has projective dimension at most
one, the syzygy `im(d₁) = ker(π)` of the epimorphism `P₀ ↠ M` out of the projective module `P₀`
is itself projective: this is `ShortComplex.ShortExact.hasProjectiveDimensionLT_X₁` applied to
the short exact sequence `0 → ker π → P₀ → M → 0`, using Mathlib's equality between
"projective dimension `≤ 0`" and `Projective`.  Consequently the short exact sequence

`0 → P₂ --d₂--> P₁ --> im(d₁) → 0`

has projective third term, so it splits (`ShortComplex.ShortExact.splittingOfProjective`), and
the retraction `r` of `d₂` produced by the splitting tensors to a left inverse of
`S ⊗[R] d₂ = Balanced.map f d₂` (`Work.ORCoherence.Tensor.balanced_map_comp`), which is
therefore injective.

This is the `gl.dim R ≤ 1` case of the vanishing hypothesis of the coherence criterion of
Jaikin-Zapirain–Linton (Corollary 3.3 there uses `gl.dim R ≤ 2`).
-/

set_option autoImplicit false
set_option maxHeartbeats 800000

open CategoryTheory Limits
open scoped TensorProduct

namespace Work.ORFinal.TorDimOne

theorem torTwoVanishes_of_globalDim_le_one {R : Type*} [Ring R] {S : Type*} [Ring S]
    (f : R →+* S) (h : Work.ORCoherence.globalDim R ≤ (1 : WithBot ℕ∞)) :
    Work.ORCoherence.TorTwoVanishes f := by
  intro M P₂ P₁ P₀ _ _ _ d₂ d₁ π hd hd' hm he he' hπ
  -- Every left `R`-module has projective dimension at most one.
  have hgl : ∀ N : ModuleCat R, CategoryTheory.HasProjectiveDimensionLE N 1 :=
    (Work.ORCoherence.globalDim_le_iff' R 1).mp h
  -- Exactness of the two given short complexes, read on the underlying linear maps.
  have hker₂ : LinearMap.range d₂.hom = LinearMap.ker d₁.hom := by
    have h := (ShortComplex.moduleCat_exact_iff_range_eq_ker (ShortComplex.mk d₂ d₁ hd)).mp he
    simpa using h
  have hker₁ : LinearMap.range d₁.hom = LinearMap.ker π.hom := by
    have h := (ShortComplex.moduleCat_exact_iff_range_eq_ker (ShortComplex.mk d₁ π hd')).mp he'
    simpa using h
  have hsurjπ : Function.Surjective π.hom := (ModuleCat.epi_iff_surjective π).mp hπ
  -- The syzygy `ker π` of the epimorphism `P₀ ↠ M` is projective, `P₀` being projective and
  -- `M` having projective dimension at most one.
  have hprojker : Projective (ModuleCat.of R ↥(LinearMap.ker π.hom)) := by
    have hS := LinearMap.shortExact_shortComplexKer hsurjπ (f := π.hom)
    have h₂ : CategoryTheory.HasProjectiveDimensionLT (π.hom.shortComplexKer).X₂ 1 := inferInstance
    have h₃ : CategoryTheory.HasProjectiveDimensionLT (π.hom.shortComplexKer).X₃ 2 := hgl M
    exact CategoryTheory.projective_iff_hasProjectiveDimensionLT_one.mpr
      (hS.hasProjectiveDimensionLT_X₁ 1 h₂ h₃)
  -- The projection `P₁ ↠ ker π` (the codomain restriction of `d₁`), whose kernel is `im d₂`.
  let q : P₁ →ₗ[R] ↥(LinearMap.ker π.hom) :=
    d₁.hom.codRestrict _ (fun x => hker₁ ▸ LinearMap.mem_range_self d₁.hom x)
  have hkerq : LinearMap.ker q = LinearMap.ker d₁.hom := LinearMap.ker_codRestrict _ _ _
  have hrange : LinearMap.range d₂.hom = LinearMap.ker q := by rw [hker₂, hkerq]
  have hsurjq : Function.Surjective q := by
    intro y
    have hy : y.1 ∈ LinearMap.range d₁.hom := hker₁.symm ▸ y.2
    rw [LinearMap.mem_range] at hy
    obtain ⟨x, hx⟩ := hy
    exact ⟨x, Subtype.ext hx⟩
  -- The short exact sequence `0 → P₂ --d₂--> P₁ --q--> ker π → 0`.
  let S : ShortComplex (ModuleCat R) :=
    ShortComplex.moduleCatMkOfKerLERange d₂ (ModuleCat.ofHom q)
      (by rw [hrange, ModuleCat.hom_ofHom])
  have hSex : S.Exact := by
    refine (ShortComplex.moduleCat_exact_iff_range_eq_ker S).mpr ?_
    show LinearMap.range d₂.hom = LinearMap.ker q
    exact hrange
  have hS : S.ShortExact := ShortComplex.ShortExact.mk' hSex (by show Mono d₂; exact hm) (by
    show Epi (ModuleCat.ofHom q)
    exact (ModuleCat.epi_iff_surjective _).mpr (by simpa [ModuleCat.hom_ofHom] using hsurjq))
  -- It splits, because its third term is projective: this is a retraction `r` of `d₂`.
  haveI : Projective S.X₃ := hprojker
  let s : S.Splitting := hS.splittingOfProjective
  let r : P₁ ⟶ P₂ := s.r
  have hfr : d₂ ≫ r = 𝟙 P₂ := s.f_r
  have hr : r.hom ∘ₗ d₂.hom = LinearMap.id := by
    have h := congrArg ModuleCat.Hom.hom hfr
    show ModuleCat.Hom.hom (d₂ ≫ r) = ModuleCat.Hom.hom (𝟙 P₂)
    exact h
  -- Tensoring the retraction gives a left inverse of `S ⊗[R] d₂`, which is therefore injective.
  have hcomp : Work.ORCoherence.Balanced.map f r.hom ∘ₗ Work.ORCoherence.Balanced.map f d₂.hom
      = LinearMap.id := by
    have h1 := Work.ORCoherence.Tensor.balanced_map_comp f d₂.hom r.hom
    rw [hr, Work.ORCoherence.Balanced.map_id] at h1
    exact h1.symm
  have hleft : ∀ z, Work.ORCoherence.Balanced.map f r.hom
      (Work.ORCoherence.Balanced.map f d₂.hom z) = z := by
    intro z
    have hc := DFunLike.congr_fun hcomp z
    simpa only [LinearMap.comp_apply, LinearMap.id_apply] using hc
  intro x y hxy
  rw [← hleft x, ← hleft y, hxy]

end Work.ORFinal.TorDimOne
