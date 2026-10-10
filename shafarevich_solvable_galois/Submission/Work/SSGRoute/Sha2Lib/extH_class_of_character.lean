import Mathlib.GroupTheory.Nilpotent
import Mathlib.Algebra.Field.ZMod
import Mathlib.NumberTheory.NumberField.Basic
import Mathlib.RepresentationTheory.Homological.GroupCohomology.LowDegree
import Mathlib.RingTheory.DedekindDomain.Ideal.Lemmas
import Mathlib.Algebra.Homology.DerivedCategory.Ext.Basic
import Submission.Work.SSGRoute.Interfaces
import Submission.Work.SSGRoute.Sha2Lib.H1pi_character_ne_zero
import Submission.Work.SSGRoute.e9_caseB_cocycle
import Submission.Work.SSGRoute.extH_groupCohomology_iso
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace Work.SSGRoute.Sha2Lib

/-- **An additive character `f : Additive Gal(L/k) →+ 𝔽_p` killing the inertia of `q'` and
non-trivial on the decomposition group of `q'` yields a class in `H¹(Gal(L/k), res 𝔽_p)` which is
unramified at `q'`, and whose restriction to the decomposition group `D_{q'}` is non-zero.**

Recall that in this workspace `H¹(G, A)` is spelled `SSGRoute.PTExt.extH A 1` (`Ext`-core) and that
`𝔽_p = Rep.trivial Coeff (K ≃ₐ[k] K) (ZMod p)` is the trivial `Gal(K/k)`-module, restricted to
`Gal(L/k)` along `galRes`.  The conclusion is the pair of statements

* `SSGRoute.PTExt.IsUnramifiedClassAt q' h`: `h`, restricted to any subgroup of the inertia group of
  the finite place `q'`, vanishes;
* `SSGRoute.PTExt.extHRestrict D h ≠ 0` for `D = decompK (Place.ofFinite q')`: `h` is non-zero after
  restriction to the decomposition group of the place of `q'`.

These are exactly the two properties the consumer
`Work.SSGRoute.Sha2Lib.unramifiedDetector_trivial` needs of its detecting class (together with
`φ ≠ 0`, the Yoneda pairing is then non-degenerate).

Suggested route.  Build the `1`-cocycle
`c := ⟨f ∘ Additive.ofMul, groupCohomology.mem_cocycles₁_of_addMonoidHom _ f⟩` in
`groupCohomology.cocycles₁ (Rep.trivial Coeff (L ≃ₐ[k] L) (ZMod p))` (trivial coefficients, so the
cocycle condition is additivity of `f`; cf. `Work.SSGRoute.Sha2Lib.H1pi_character_ne_zero`, which
uses the same cocycle and `groupCohomology.H1IsoOfIsTrivial` to show that the class of a non-zero
character is non-zero).  Then `h := e 1 (L ≃ₐ[k] L) _ (groupCohomology.H1π _ c)` for the isomorphism
`e` supplied by `Work.SSGRoute.extH_groupCohomology_iso` (an existential statement: `obtain` it at
the start); the two representations `Rep.res (galRes k K L) (Rep.trivial Coeff (K≃ₐ[k]K) (ZMod p))`
and `Rep.trivial Coeff (L ≃ₐ[k] L) (ZMod p)` agree by `rfl` (verified), so no transport is needed.

For any subgroup `D' ≤ Gal(L/k)` the naturality clause of the bridge computes
`extHRestrict D' h = e 1 D' (Rep.res D'.subtype _) ((groupCohomology.map D'.subtype (𝟙 _) 1).hom
(H1π _ c))`, and `Work.SSGRoute.resNatTrans_H1π_subtype` identifies the argument with
`H1π (Rep.res D'.subtype _) (resCocycle₁ D' _ c)`, i.e. the class of the naively restricted cocycle,
whose value at `σ : D'` is `f (Additive.ofMul σ.1)`.  Since `e` is injective and for trivial
coefficients the `1`-coboundaries vanish identically, `groupCohomology.H1π_eq_zero_iff` gives:
the restricted class vanishes iff the restricted cocycle is the zero function.  Hence
`hf` (the cocycle is zero on any subgroup of the inertia group) yields unramifiedness, and `hfne`
(the cocycle is a non-zero function on `D_{q'}`) yields the non-vanishing of the restriction to
`D_{q'}`. -/
theorem extH_class_of_character {k K L : Type} [Field k] [NumberField k] [Field K]
    [NumberField K] [Field L] [NumberField L] [Algebra k K] [Algebra K L] [Algebra k L]
    [IsScalarTower k K L] [FiniteDimensional k K] [IsGalois k K] [FiniteDimensional k L]
    [IsGalois k L]
    (p : ℕ) [Fact p.Prime]
    (q' : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers L))
    (f : Additive (L ≃ₐ[k] L) →+ ZMod p)
    (hf : ∀ σ : L ≃ₐ[k] L, SSGRoute.PTExt.IsInertiaAt q' σ → f (Additive.ofMul σ) = 0)
    (hfne : ∃ σ : L ≃ₐ[k] L,
      σ ∈ SSGRoute.PTExt.decompK (NK.GlobalCFT.Place.ofFinite q') ∧
        f (Additive.ofMul σ) ≠ 0) :
    ∃ h : SSGRoute.PTExt.extH
        (Rep.res (SSGRoute.PTExt.galRes k K L)
          (Rep.trivial SSGRoute.PTExt.Coeff (K ≃ₐ[k] K) (ZMod p))) 1,
      SSGRoute.PTExt.IsUnramifiedClassAt q' h ∧
      SSGRoute.PTExt.extHRestrict
        (SSGRoute.PTExt.decompK (k := k) (K := L) (NK.GlobalCFT.Place.ofFinite q')) h ≠ 0 := by
  classical
  -- The trivial `Gal(L/k)`-module `𝔽_p` together with the `1`-cocycle of the character `f`.
  let A : Rep.{0} SSGRoute.PTExt.Coeff (L ≃ₐ[k] L) :=
    Rep.trivial SSGRoute.PTExt.Coeff (L ≃ₐ[k] L) (ZMod p)
  let z : groupCohomology.cocycles₁ A :=
    ⟨f ∘ Additive.ofMul,
      groupCohomology.mem_cocycles₁_of_addMonoidHom (A := A) f⟩
  -- The `1`-coboundaries of a trivial module vanish.
  have hcb : ∀ (m : ZMod p) (d : L ≃ₐ[k] L), A.ρ d m - m = 0 := by
    intro m d
    have hmem : (fun e : L ≃ₐ[k] L => A.ρ e m - m) ∈ groupCohomology.coboundaries₁ A :=
      (Work.SSGRoute.mem_coboundaries₁_iff A (fun e : L ≃ₐ[k] L => A.ρ e m - m)).mpr
        ⟨m, fun e => rfl⟩
    rw [groupCohomology.coboundaries₁_eq_bot_of_isTrivial] at hmem
    have h0 : (fun e : L ≃ₐ[k] L => A.ρ e m - m) = 0 := by simpa using hmem
    simpa using congrFun h0 d
  refine ⟨SSGRoute.PTExt.eCoh 1 (L ≃ₐ[k] L) A ((groupCohomology.H1π A).hom z), ?_, ?_⟩
  · -- unramified at `q'`: the cocycle kills the inertia group, so the restriction is a coboundary
    intro D hD
    refine (Work.SSGRoute.e9_caseB_cocycle A D z).mpr ⟨0, ?_⟩
    intro d hd
    rw [hcb 0 d]
    show f (Additive.ofMul d) = 0
    exact hf d (hD d hd)
  · -- nontrivial on `D_{q'}`: a vanishing restriction would force `f` to kill a `σ ∈ D_{q'}` on
    -- which it is nonzero
    intro h0
    obtain ⟨m, hm⟩ := (Work.SSGRoute.e9_caseB_cocycle A
      (SSGRoute.PTExt.decompK (k := k) (K := L)
        (NK.GlobalCFT.Place.ofFinite q')) z).mp h0
    obtain ⟨σ, hσD, hσne⟩ := hfne
    have h1 := hm σ hσD
    rw [hcb m σ] at h1
    exact hσne (show f (Additive.ofMul σ) = 0 from h1)

end Work.SSGRoute.Sha2Lib
