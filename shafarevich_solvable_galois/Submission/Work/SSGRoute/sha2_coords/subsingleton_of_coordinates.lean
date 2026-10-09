import Mathlib
import Submission.Work.SSGRoute.sha2_defs
import Submission.Work.SSGRoute.ShaCocycles
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Ш²(k,M) = 0` for coefficients with trivial `Gal(K/k)`-action: the coordinate reduction

The arithmetic input of the `Ш²(k,M) = 0` route is stated for the coefficient module
`Triv p = 𝔽_p`: every locally trivial continuous `2`-cocycle with values in `𝔽_p` is a global
coboundary (`hZ`, the Hasse-principle input).  Since an arbitrary finite `𝔽_p`-module `M` on
which `Gal(K/k)` acts trivially is a direct sum of copies of `𝔽_p`, `Ш²(k,M) = 0` follows by
working in coordinates.

Concretely, if `c` is a locally trivial `2`-cocycle with values in such an `M`, then for a
`𝔽_p`-basis `bs` of `M` each coordinate `g h ↦ bs.coord i (c g h)` is again a locally trivial
`2`-cocycle with values in `𝔽_p` (push-forward of cocycles along the `G`-equivariant linear
map `bs.coord i`, which is `G`-equivariant precisely because the action on `M` is trivial), so
by `hZ` it has a locally constant primitive `bfun i`.  Assembling the coordinates,
`b g = e.symm (fun i => bfun i g)` — where `e = bs.equivFun` — is a locally constant primitive
of `c`.

## Main result

* `Work.SSGRoute.sha2_coords.subsingleton_of_coordinates`: `Ш²(k,M)` is a subsingleton.
-/

set_option linter.ambiguousOpen false

namespace Work.SSGRoute.sha2_coords

/-- `𝔽_p` carries the trivial action of any group with a unit: `g • x = x`. -/
theorem triv_smul_eq (p : ℕ) (Γ : Type) [One Γ] (g : Γ) (x : Work.SSGRoute.Triv p) :
    g • x = x := rfl

/-- A finite product of locally constant functions is locally constant. -/
theorem isLocConstOn_pi {ι Γ M : Type} [Finite ι] [Group Γ] [TopologicalSpace Γ]
    {H : Subgroup Γ} {b : ι → Γ → M} (h : ∀ i, SSGRoute.IsLocConstOn H (b i)) :
    SSGRoute.IsLocConstOn H (fun g => fun i => b i g) := by
  classical
  choose U hU hb using h
  refine ⟨⨅ i, U i, ?_, ?_⟩
  · rw [Subgroup.coe_iInf]
    exact isOpen_iInter_of_finite fun i => hU i
  · intro g hg u hu huH
    funext i
    exact hb i g hg u (Subgroup.mem_iInf.mp hu i) huH

theorem subsingleton_of_coordinates (p : ℕ) [Fact p.Prime] (k Ω : Type) [Field k] [NumberField k]
    [Field Ω] [Algebra k Ω] [IsAlgClosure k Ω] (K : IntermediateField k Ω) [FiniteDimensional k K]
    [IsGalois k K]
    (hZ : ∀ c : (Ω ≃ₐ[k] Ω) → (Ω ≃ₐ[k] Ω) → Work.SSGRoute.Triv p,
      c ∈ Work.SSGRoute.Z2loc p k Ω K (Work.SSGRoute.Triv p) →
        SSGRoute.IsCoboundary2On (SSGRoute.res k K) ⊤ c)
    (M : Type) [AddCommGroup M] [Module (ZMod p) M] [DistribMulAction (K ≃ₐ[k] K) M]
    [SMulCommClass (K ≃ₐ[k] K) (ZMod p) M] [Finite M]
    (htriv : ∀ (g : K ≃ₐ[k] K) (m : M), g • m = m) :
    Subsingleton (Work.SSGRoute.Sha2 p k Ω K M) := by
  -- `Ш²(k,M)` is a quotient of `Z²_loc` by the global coboundaries; it is a subsingleton as soon
  -- as every locally trivial cocycle is a global coboundary.
  rw [Submodule.Quotient.subsingleton_iff, Submodule.eq_top_iff']
  intro x
  rw [Submodule.mem_comap]
  classical
  -- `M` is a finite dimensional `𝔽_p`-vector space; fix a basis and the coordinate isomorphism.
  haveI hfinM : Module.Finite (ZMod p) M := Module.Finite.of_finite
  haveI hfreeM : Module.Free (ZMod p) M := inferInstance
  let bs := Module.finBasis (ZMod p) M
  let e : M ≃ₗ[ZMod p] (Fin (Module.finrank (ZMod p) M) → ZMod p) := bs.equivFun
  -- The coordinate functionals are `G`-equivariant because `M` carries the trivial action.
  have hfe : ∀ i : Fin (Module.finrank (ZMod p) M), ∀ (g : K ≃ₐ[k] K) (m : M),
      bs.coord i (g • m) = g • bs.coord i m := by
    intro i g m
    rw [htriv g m]
    rfl
  -- Hence the coordinate `2`-cocycles are again locally trivial continuous `2`-cocycles.
  have hcoord : ∀ i : Fin (Module.finrank (ZMod p) M),
      (fun g h => bs.coord i (x.1 g h)) ∈ Z2loc p k Ω K (Triv p) := fun i =>
    Z2loc_pushC2_mem p k Ω K M (Triv p) (bs.coord i) (hfe i) x.1 x.2
  -- By the arithmetic input, each coordinate has a locally constant primitive.
  choose bfun hbfun using fun i => hZ (fun g h => bs.coord i (x.1 g h)) (hcoord i)
  let B : (Ω ≃ₐ[k] Ω) → (Fin (Module.finrank (ZMod p) M) → Triv p) := fun g i => bfun i g
  have hB_loc : SSGRoute.IsLocConstOn ⊤ B :=
    isLocConstOn_pi (fun i => (hbfun i).1)
  -- Reassemble the coordinates into a primitive with values in `M`.
  let b : (Ω ≃ₐ[k] Ω) → M := fun g => e.symm (B g)
  have hb_loc : SSGRoute.IsLocConstOn ⊤ b := by
    obtain ⟨U, hU, hBU⟩ := hB_loc
    exact ⟨U, hU, fun g hg u hu huH => by
      show e.symm (B (g * u)) = e.symm (B g)
      rw [hBU g hg u hu huH]⟩
  -- `B` is the coboundary of `e ∘ c`.
  have key2 : ∀ g h, e (x.1 g h) = (SSGRoute.res k K) g • B h - B (g * h) + B g := by
    intro g h
    funext i
    have hi := (hbfun i).2 g trivial h trivial
    show bs.coord i (x.1 g h) = ((SSGRoute.res k K) g • B h - B (g * h) + B g) i
    rw [show bs.coord i (x.1 g h) = (fun g h => bs.coord i (x.1 g h)) g h from rfl, hi]
    simp [B, triv_smul_eq]
  -- Since `e` is injective, `b` is a primitive of `c`.
  refine ⟨b, hb_loc, fun g _ h _ => ?_⟩
  apply e.injective
  change e (x.1 g h) = e ((SSGRoute.res k K) g • b h - b (g * h) + b g)
  rw [key2 g h]
  funext i
  simp [b, B, htriv, triv_smul_eq, map_add, map_sub]

end Work.SSGRoute.sha2_coords
