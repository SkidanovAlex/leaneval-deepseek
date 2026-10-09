import Mathlib
import Submission.Work.SSGRoute.PTDefs
import Submission.Work.SSGRoute.decompK_restrict_exists
import Submission.Work.SSGRoute.localUnitsMap_exists
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace Work.SSGRoute

open CategoryTheory SSGRoute.PTExt

-- `hg` is part of the requested statement but is not needed for this particular consequence.
set_option linter.unusedVariables false in
/-- **The Kummer coefficient class at a higher level, and injectivity of the local units map.**
Let `k ⊆ K ⊆ L` be number fields with `L/k` finite Galois, `w' ∣ w` places, `g` the restriction of
the decomposition groups and `ι : K_wˣ → L_{w'}ˣ` the canonical local embedding of unit groups.  For
`p` prime and a nonzero `D_w`-map `z : 𝔽_p ⟶ K_wˣ`:
* `ι` is injective (it is a field embedding of local fields), and
* there is a nonzero `D_{w'}`-map `z' : 𝔽_p ⟶ L_{w'}ˣ` with `z' a = ι (z a)` for every `a : 𝔽_p`.

Hints from the reviewers: for `z'` take `trivRes g (ZMod p) ≫ Rep.res g z ≫ ι`, whose pointwise
clause `z'.hom a = ι.hom (z.hom a)` then holds definitionally; `z' ≠ 0` follows from `z ≠ 0` and
injectivity of `ι`.  For the injectivity: `hι` determines `ι.hom` (every element is
`Additive.ofMul u`, `Additive.ofMul.surjective`), reducing to injectivity of
`NK.GlobalCFT.Place.localAlgebraMapUnits`, which is
`NK.GlobalCFT.Inclusion.globalCFT_localAlgebraMapUnits_injective` (in
`Submission/NK/GlobalCFT/Inclusion/globalCFT_ideleClassGroup_inclusion_injective.lean`) — its
definition is by cases on the kinds of the two places, using the `LiesOver` instance when available;
the repo already has `RingHom.injective completionMap` and `Commons...adicCompletionMap_injective`. -/
theorem localLevel_zetaCoeff {k K L : Type} [Field k] [NumberField k] [Field K] [NumberField K]
    [Field L] [NumberField L] [Algebra k K] [Algebra k L] [Algebra K L] [IsScalarTower k K L]
    [FiniteDimensional k K] [IsGalois k K] [FiniteDimensional k L] [IsGalois k L]
    (p : ℕ) [Fact p.Prime] (w : NK.GlobalCFT.Place K) (w' : NK.GlobalCFT.Place L)
    (hw' : NK.GlobalCFT.Place.LiesOver w' w)
    (g : MulAction.stabilizer (L ≃ₐ[k] L) w' →* SSGRoute.PTExt.decompK (k := k) w)
    (hg : ∀ σ, ((g σ : SSGRoute.PTExt.decompK (k := k) w) : K ≃ₐ[k] K)
      = SSGRoute.PTExt.galRes k K L (σ : L ≃ₐ[k] L))
    (ι : Rep.res g (SSGRoute.PTExt.localUnitsK (k := k) w)
      ⟶ NK.HassePrinciple.localUnitsRep k L w')
    (hι : ∀ u : (NK.GlobalCFT.Place.localField K w)ˣ,
      ι.hom (Additive.ofMul u)
        = Additive.ofMul (NK.GlobalCFT.Place.localAlgebraMapUnits w' w hw' u))
    (z : Rep.trivial SSGRoute.PTExt.Coeff (SSGRoute.PTExt.decompK (k := k) w) (ZMod p)
      ⟶ SSGRoute.PTExt.localUnitsK (k := k) w)
    (hz : z ≠ 0) :
    Function.Injective ι.hom ∧
      ∃ z' : Rep.trivial SSGRoute.PTExt.Coeff (SSGRoute.PTExt.decompK (k := k) w') (ZMod p)
          ⟶ NK.HassePrinciple.localUnitsRep k L w',
        z' ≠ 0 ∧ ∀ a : ZMod p, z'.hom a = ι.hom (z.hom a) := by
  -- The local units map is injective: on `Additive.ofMul u` it is the local algebra map of
  -- completions, which is `Units.map` of an injective ring homomorphism of fields.
  have hinj : Function.Injective ι.hom := by
    intro x y hxy
    obtain ⟨u, rfl⟩ := Additive.ofMul.surjective x
    obtain ⟨v, rfl⟩ := Additive.ofMul.surjective y
    rw [hι u, hι v] at hxy
    exact congrArg Additive.ofMul
      (NK.GlobalCFT.Inclusion.globalCFT_localAlgebraMapUnits_injective hw'
        (Additive.ofMul.injective hxy))
  refine ⟨hinj, trivRes g (ZMod p) ≫ Rep.resMap g z ≫ ι, ?_, fun a => rfl⟩
  -- `z' = 0` would force `ι ∘ z = 0`, hence `z = 0` by injectivity of `ι`.
  intro hz'
  have hzero : ι.hom (0 : Additive (NK.GlobalCFT.Place.localField K w)ˣ) = 0 := map_zero _
  apply hz
  apply Rep.hom_ext
  apply Representation.IntertwiningMap.ext
  apply LinearMap.ext
  intro a
  have h2 : (trivRes g (ZMod p) ≫ Rep.resMap g z ≫ ι).hom a = ι.hom (z.hom a) := rfl
  have h4 : ι.hom (z.hom a) = ι.hom (0 : Additive (NK.GlobalCFT.Place.localField K w)ˣ) := by
    rw [hzero, ← h2, hz']
    simp
  have h5 : z.hom a = 0 := hinj h4
  simpa [Rep.zero_hom] using h5

end Work.SSGRoute
