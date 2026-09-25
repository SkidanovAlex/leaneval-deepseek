import Mathlib
import Submission.Commons.RepresentationTheory.TateCohomology.tateCohomology_neg_one_iso

set_option linter.style.haveILetI false

namespace NK.GlobalCFTdeep

open CategoryTheory

/-- **Tate cohomology in degree `-1` for a finite cyclic group, in kernel form.**  For a `ℤ[G]`-module
`V`, if `Ĥ⁻¹(G, V) = 0` then `ker(N) ⊆ (g₀ - 1)V` for any generator `g₀` of `G`: every element `x`
killed by the norm map is a coboundary `ρ g₀ w - w`.

Route: `Commons.RepresentationTheory.TateCohomology.tateCohomology_neg_one_iso` (in
`Submission/Commons/RepresentationTheory/TateCohomology/tateCohomology_neg_one_iso.lean`) identifies
`Ĥ⁻¹(G,V)` with `ker(ρ.norm) ⧸ comap (ker ρ.norm).subtype (Coinvariants.ker ρ)` (Mathlib's
`Representation.Coinvariants.ker` is by definition the span of the elements `ρ g v - v`), so the
hypothesis gives `∀ x ∈ ker (ρ.norm), x ∈ Coinvariants.ker ρ`; then
`Representation.FiniteCyclicGroup.coinvariantsKer_eq_range` turns `Coinvariants.ker ρ` into the
range of `ρ g₀ - LinearMap.id` because `g₀` generates. -/
theorem exists_sub_smul_eq_of_subsingleton_tateCohomology_neg_one {G V : Type} [Group G]
    [Fintype G] [AddCommGroup V] [Module ℤ V] (ρ : Representation ℤ G V)
    (h : Subsingleton (tateCohomology (Rep.of ρ) (-1))) (g₀ : G)
    (hg : Subgroup.zpowers g₀ = ⊤) {x : V} (hx : ρ.norm x = 0) :
    ∃ w : V, ρ g₀ w - w = x := by
  letI : Module ℤ ↥(LinearMap.ker (Representation.norm ρ)) :=
    (LinearMap.ker (Representation.norm ρ)).module
  obtain ⟨e⟩ := Commons.RepresentationTheory.TateCohomology.tateCohomology_neg_one_iso ρ
  haveI hsub : Subsingleton (tateCohomology (Rep.of ρ) (-1)) := h
  haveI : Subsingleton
      ((LinearMap.ker (Representation.norm ρ)) ⧸
        (Submodule.comap (LinearMap.ker (Representation.norm ρ)).subtype
          (Submodule.span ℤ (Set.range fun p : G × V => ρ p.1 p.2 - p.2)))) :=
    e.symm.injective.subsingleton
  have htop : (Submodule.comap (LinearMap.ker (Representation.norm ρ)).subtype
        (Submodule.span ℤ (Set.range fun p : G × V => ρ p.1 p.2 - p.2))) = ⊤ :=
    Submodule.Quotient.subsingleton_iff.mp ‹Subsingleton _›
  have hxker : x ∈ Representation.Coinvariants.ker ρ := by
    have hmem : (⟨x, hx⟩ : LinearMap.ker (Representation.norm ρ)) ∈
        (Submodule.comap (LinearMap.ker (Representation.norm ρ)).subtype
          (Submodule.span ℤ (Set.range fun p : G × V => ρ p.1 p.2 - p.2))) := by
      rw [htop]; exact Submodule.mem_top
    simpa [Representation.Coinvariants.ker] using hmem
  rw [Representation.FiniteCyclicGroup.coinvariantsKer_eq_range ρ g₀ (fun γ => by simp [hg])]
    at hxker
  obtain ⟨w, hw⟩ := hxker
  exact ⟨w, by simpa using hw⟩

end NK.GlobalCFTdeep
