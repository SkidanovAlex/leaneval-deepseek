import Mathlib.FieldTheory.KrullTopology
import Mathlib.RingTheory.Henselian
import Mathlib.Algebra.Field.ZMod
import Mathlib.NumberTheory.NumberField.Basic
import Mathlib.RingTheory.Flat.TorsionFree
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
import Submission.Work.SSGRoute.HSRow.exists_primitive
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace Work.SSGRoute.HSRow

/-- **A linear choice of primitives.**  If `H²_loc(I,M') = 0` for all finite `M'` (`hvan`) and
`I ≤ D`, there is an `𝔽_p`-*linear* map assigning to every locally constant `2`-cocycle `c` on `D` a
locally constant `1`-cochain `κ c` on `I` whose coboundary is `c|_I` (`d¹ (κ c) (n,m) = c n m` for
`n,m ∈ I`).  Construction: the map `δ : lcOneCoins I →ₗ Fun (G×G) M`, `f ↦ d¹f`, has image
contained in `lcCocycles2 I` and is onto it, because `hvan` (instantiated at `M`) says every element
of `lcCocycles2 I` is a `2`-coboundary on `I`; take a linear right inverse of the resulting
surjection `lcOneCoins I →ₗ ↥(lcCocycles2 I)` over the field `𝔽_p`
(`LinearMap.exists_rightInverse_of_surjective`; alternatively split
`lcOneCoins I = ker δ ⊕ W` with `Submodule.exists_isCompl`), and compose with the restriction
`lcCocycles2 D →ₗ lcCocycles2 I` (`lcCocycles2_mono`). -/
theorem exists_linear_primitive
    (p : ℕ) [Fact p.Prime] (k Ω : Type) [Field k] [NumberField k] [Field Ω] [Algebra k Ω]
    [IsAlgClosure k Ω] (K : IntermediateField k Ω) [FiniteDimensional k K] [IsGalois k K]
    (M : Type) [AddCommGroup M] [Module (ZMod p) M] [DistribMulAction (K ≃ₐ[k] K) M]
    [SMulCommClass (K ≃ₐ[k] K) (ZMod p) M] [Finite M]
    (D I : Subgroup (Ω ≃ₐ[k] Ω)) (hI : I ≤ D)
    (hvan : ∀ (M' : Type) [AddCommGroup M'] [Module (ZMod p) M']
        [DistribMulAction (K ≃ₐ[k] K) M'] [SMulCommClass (K ≃ₐ[k] K) (ZMod p) M'] [Finite M'],
        Subsingleton (Work.SSGRoute.H2loc p k Ω K M' I)) :
    ∃ κ : ↥(Work.SSGRoute.lcCocycles2 p k Ω K M D) →ₗ[ZMod p] ↥(lcOneCoins p k Ω K M I),
      ∀ (c : ↥(Work.SSGRoute.lcCocycles2 p k Ω K M D)) (n m : Ω ≃ₐ[k] Ω), n ∈ I → m ∈ I →
        SSGRoute.res k K n • (κ c).1 m - (κ c).1 (n * m) + (κ c).1 n = c.1 n m := by
  classical
  -- The construction: `δ` is the coboundary `d¹` of a locally constant `1`-cochain on `I`,
  -- regarded as a map `lcOneCoins I →ₗ (I → I → M)` (its two variables restricted to `I`; the
  -- `↥(lcCocycles2 I)`-valued version of the docstring above is not used, because two elements of
  -- `lcCocycles2 I` that agree on `I × I` may differ off `I × I`).
  -- `hvan` shows `range ρ ⊆ range δ`, so `δ` restricts to a surjection onto its range and a
  -- linear right inverse `s` of it exists (`LinearMap.exists_rightInverse_of_surjective`, over the
  -- field `𝔽_p`); composing `s` with `ρ` (the restriction `c ↦ c|_{I × I}`, well defined on
  -- `lcCocycles2 D` by `lcCocycles2_mono`) gives the required `κ`.
  let δ : ↥(lcOneCoins p k Ω K M I) →ₗ[ZMod p] (↥I → ↥I → M) :=
    { toFun := fun b n m =>
        SSGRoute.res k K ((n : ↥I) : Ω ≃ₐ[k] Ω) • b.1 ((m : ↥I) : Ω ≃ₐ[k] Ω)
          - b.1 (((n : ↥I) : Ω ≃ₐ[k] Ω) * ((m : ↥I) : Ω ≃ₐ[k] Ω))
          + b.1 ((n : ↥I) : Ω ≃ₐ[k] Ω)
      map_add' := by
        intro f g
        ext n m
        simp only [Submodule.coe_add, Pi.add_apply, smul_add]
        abel
      map_smul' := by
        intro a f
        ext n m
        simp only [Submodule.coe_smul, Pi.smul_apply, smul_sub, smul_add, RingHom.id_apply]
        rw [smul_comm] }
  let ρ : ↥(Work.SSGRoute.lcCocycles2 p k Ω K M D) →ₗ[ZMod p] (↥I → ↥I → M) :=
    { toFun := fun c n m => c.1 ((n : ↥I) : Ω ≃ₐ[k] Ω) ((m : ↥I) : Ω ≃ₐ[k] Ω)
      map_add' := by intro f g; ext n m; simp
      map_smul' := by intro a f; ext n m; simp }
  have hle : ∀ c : ↥(Work.SSGRoute.lcCocycles2 p k Ω K M D), ρ c ∈ LinearMap.range δ := by
    intro c
    have hmemI : c.1 ∈ Work.SSGRoute.lcCocycles2 p k Ω K M I :=
      lcCocycles2_mono p k Ω K M hI c.2
    have hsub : Subsingleton (Work.SSGRoute.H2loc p k Ω K M I) := hvan M
    have hzero : (Submodule.Quotient.mk (p := Submodule.comap
        (Work.SSGRoute.lcCocycles2 p k Ω K M I).subtype
        (Work.SSGRoute.coboundaries2 p k Ω K M I)) (⟨c.1, hmemI⟩) :
          Work.SSGRoute.H2loc p k Ω K M I) = 0 := @Subsingleton.elim _ hsub _ _
    have hcob : c.1 ∈ Work.SSGRoute.coboundaries2 p k Ω K M I := by
      have h := Submodule.mem_comap.mp (Submodule.Quotient.mk_eq_zero _ |>.mp hzero)
      simpa using h
    obtain ⟨b, hbloc, hbeq⟩ := hcob
    refine ⟨⟨b, hbloc⟩, ?_⟩
    ext n m
    exact (hbeq ((n : ↥I) : Ω ≃ₐ[k] Ω) n.2 ((m : ↥I) : Ω ≃ₐ[k] Ω) m.2).symm
  have hsurj : (δ.codRestrict δ.range (fun x => LinearMap.mem_range_self δ x)).range = ⊤ := by
    rw [LinearMap.range_codRestrict, Submodule.comap_subtype_self]
  haveI hfree : Module.Free (ZMod p) ↥(LinearMap.range δ) :=
    Module.Free.of_divisionRing (ZMod p) ↥(LinearMap.range δ)
  haveI hproj : Module.Projective (ZMod p) ↥(LinearMap.range δ) := Module.Projective.of_free
  obtain ⟨s, hs⟩ := LinearMap.exists_rightInverse_of_surjective
    (δ.codRestrict δ.range (fun x => LinearMap.mem_range_self δ x)) hsurj
  have hs_apply : ∀ x : ↥(LinearMap.range δ), δ (s x) = (x : ↥I → ↥I → M) := by
    intro x
    have h := congrArg Subtype.val (LinearMap.ext_iff.mp hs x)
    rw [LinearMap.comp_apply, LinearMap.codRestrict_apply, LinearMap.id_apply] at h
    exact h
  let ρ' : ↥(Work.SSGRoute.lcCocycles2 p k Ω K M D) →ₗ[ZMod p] ↥(LinearMap.range δ) :=
    ρ.codRestrict (LinearMap.range δ) (fun c => hle c)
  refine ⟨s.comp ρ', ?_⟩
  intro c n m hn hm
  have key : δ ((s.comp ρ') c) ⟨n, hn⟩ ⟨m, hm⟩ = c.1 n m := by
    rw [LinearMap.comp_apply, hs_apply]
    rfl
  exact key


end Work.SSGRoute.HSRow
