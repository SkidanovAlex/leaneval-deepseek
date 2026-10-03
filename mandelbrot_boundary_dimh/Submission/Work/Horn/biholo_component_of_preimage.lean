import Mathlib
import Submission.Work.Interfaces.Parabolic
import Submission.Work.Horn.pushdown_covering

set_option linter.style.haveILetI false
set_option linter.unusedVariables false

namespace Work.Horn

open Set

/-!
# A component of the preimage of a simply connected set is mapped onto it

Let `G : ℂ → ℂ` be a covering map over an open set `U` (in the sense that the restriction
`↥D → ℂ`, `z ↦ G z`, is a covering map on `U`).  If `V ⊆ U` is open and `SimplyConnectedSpace V`,
then for every `x ∈ D ∩ G ⁻¹' V` the connected component of `x` in `D ∩ G ⁻¹' V` is mapped onto
`V` by `G`.

The proof is the usual one: since `↥V` is simply connected and locally path connected, the
inclusion `↥V ↪ ℂ` lifts along the covering to a continuous section `F : ↥V → ↥D` with `G ∘ F = id`
and `F ⟨G x⟩ = x`.  The image of `F` (pushed into `ℂ`) is preconnected, contained in
`D ∩ G ⁻¹' V` and contains `x`, so it lies in the connected component of `x`; every `y ∈ V` is the
image under `G` of the point `F ⟨y, ·⟩ ∈ D ∩ G ⁻¹' V` of that component.  The converse inclusion is
immediate from `connectedComponentIn_subset`.

Note that no regularity of `D` (openness, local path connectedness) is needed: the section lives
in the preimage of the *open* set `V`, where the covering property supplies all the local
structure used.
-/

theorem biholo_component_of_preimage {G : ℂ → ℂ} {D U V : Set ℂ} {x : ℂ}
    (hG : DifferentiableOn ℂ G D)
    (hcov : IsCoveringMapOn (fun z : ↥D => G z) U)
    (hVU : V ⊆ U) (hVopen : IsOpen V) (hVconn : IsConnected V)
    (hVsc : SimplyConnectedSpace V)
    (hx : x ∈ D ∩ G ⁻¹' V) :
    G '' connectedComponentIn (D ∩ G ⁻¹' V) x = V := by
  haveI : SimplyConnectedSpace ↥V := hVsc
  haveI : LocallyPathConnectedSpace ↥V := hVopen.locallyPathConnectedSpace
  set a₀ : ↥V := ⟨G x, hx.2⟩ with ha₀
  set e₀ : ↥D := ⟨x, hx.1⟩ with he₀
  -- the section of the covering over the simply connected base `V` through `x`
  obtain ⟨F, hF₁, hF₂⟩ := ((hcov.mono hVU).existsUnique_continuousMap_lifts
    (f := (⟨Subtype.val, continuous_subtype_val⟩ : C(↥V, ℂ)))
    (a₀ := a₀) (e₀ := e₀) rfl (fun a => a.2)).exists
  have hF₂' : ∀ a : ↥V, G ((F a : ↥D) : ℂ) = (a : ℂ) := fun a => congr_fun hF₂ a
  -- the image of the section, as a subset of `ℂ`
  have hcont : Continuous (fun a : ↥V => ((F a : ↥D) : ℂ)) :=
    continuous_subtype_val.comp F.continuous
  have hpreconn : IsPreconnected (Set.range (fun a : ↥V => ((F a : ↥D) : ℂ))) :=
    isPreconnected_range hcont
  have hsub : Set.range (fun a : ↥V => ((F a : ↥D) : ℂ)) ⊆ D ∩ G ⁻¹' V := by
    rintro y ⟨a, rfl⟩
    refine ⟨(F a).2, ?_⟩
    show G ((F a : ↥D) : ℂ) ∈ V
    rw [hF₂' a]
    exact a.2
  have hxS : x ∈ Set.range (fun a : ↥V => ((F a : ↥D) : ℂ)) :=
    ⟨a₀, by show ((F a₀ : ↥D) : ℂ) = x; rw [hF₁, he₀]⟩
  have hC := hpreconn.subset_connectedComponentIn hxS hsub
  refine Set.Subset.antisymm ?_ ?_
  · rintro y ⟨z, hz, rfl⟩
    exact (connectedComponentIn_subset (D ∩ G ⁻¹' V) x hz).2
  · intro y hy
    exact ⟨((F (⟨y, hy⟩ : ↥V) : ↥D) : ℂ), hC ⟨⟨y, hy⟩, rfl⟩, (hF₂' ⟨y, hy⟩)⟩

end Work.Horn
