import Mathlib
import Submission.Work.SSGRoute.PTDefs
import Submission.Work.SSGRoute.E9c.TransportDefs
import Submission.Work.SSGRoute.e7comega_defs
import Submission.Work.SSGRoute.localUnitsMap_exists
import Submission.Work.SSGRoute.localUnitsEquiv_fixed_iff_ringEquiv_fixed
import Submission.Work.SSGRoute.decompK_restrict_exists
import Submission.NK.GlobalCFT.Galois.globalCFT_localFixed_infinite
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

set_option maxHeartbeats 2000000

namespace Work.SSGRoute.PT

open CategoryTheory SSGRoute.PTExt

/-- **The decomposition-group action on the local units only depends on the underlying
`k`-algebra automorphism.**  If `σ : Gal(L/K)` is viewed as an element of `Gal(L/k)` by
restriction of scalars (`AlgEquiv.restrictScalars k σ`), then the two resulting automorphisms
`L_uˣ → L_uˣ` (one for the `D_u(K)`-action, one for the `D_u(k)`-action) agree.

This is the bookkeeping that lets fixity under the *larger* `k`-stabiliser of `u` be tested
through the `localUnitsEquiv`-action of the smaller `K`-stabiliser.  The two `localAut`s agree
because `Place.localRingEquiv` only sees the underlying function of `σ`, and continuous ring
automorphisms of a local field agreeing on the image of `L` are equal
(`NK.HassePrinciple.localRingEquiv_ext_of_algebraMap`). -/
theorem localUnitsEquiv_restrictScalars_apply {k K L : Type} [Field k] [NumberField k] [Field K]
    [NumberField K] [Field L] [NumberField L] [Algebra k K] [Algebra k L] [Algebra K L]
    [IsScalarTower k K L] [FiniteDimensional k L] [IsGalois k L] [FiniteDimensional K L]
    [IsGalois K L]
    (u : NK.GlobalCFT.Place L) (σ : L ≃ₐ[K] L) (hσ : σ • u = u)
    (hσ' : AlgEquiv.restrictScalars k σ • u = u)
    (a : (NK.GlobalCFT.Place.localField L u)ˣ) :
    NK.HassePrinciple.localUnitsEquiv (K := k) u ⟨AlgEquiv.restrictScalars k σ, hσ'⟩ a
      = NK.HassePrinciple.localUnitsEquiv (K := K) u ⟨σ, hσ⟩ a := by
  have haux : NK.HassePrinciple.localAut (K := k) u ⟨AlgEquiv.restrictScalars k σ, hσ'⟩
      = NK.HassePrinciple.localAut (K := K) u ⟨σ, hσ⟩ := by
    apply NK.HassePrinciple.localRingEquiv_ext_of_algebraMap
    · exact NK.HassePrinciple.localAut_continuous u _
    · exact NK.HassePrinciple.localAut_continuous u _
    · intro x
      rw [NK.HassePrinciple.localAut_algebraMap, NK.HassePrinciple.localAut_algebraMap]
      rfl
  apply Units.ext
  rw [NK.HassePrinciple.coe_localUnitsEquiv, NK.HassePrinciple.coe_localUnitsEquiv]
  show NK.HassePrinciple.localAut (K := k) u ⟨AlgEquiv.restrictScalars k σ, hσ'⟩ ↑a
      = NK.HassePrinciple.localAut (K := K) u ⟨σ, hσ⟩ ↑a
  rw [haux]

/-- **The `D_u`-invariants of `L_uˣ` lie in the image of `K_wˣ`** (the local-invariants input, in
the `Rep` form needed by `levelTransport_fp_injective`): for a tower `k ⊆ K ⊆ L` of number fields
with `K/k`, `L/k` finite Galois, an infinite place `w` of `K` and a place `u | w` of `L`, every
element `b` of `L_uˣ` fixed by the whole `D_u`-action is in the image of the local units map.

Route (both reviewers confirmed; it is the archimedean counterpart of the already-proved finite-place
analogue `fixed_localUnit_mem_range_finite`, same shape and same recipe): fixity under the `k`-
stabiliser of `u` (which is `↥(decompK (k := k) u)`) implies fixity under
`D_u(K) = Gal(L/K) ∩ D_u`, which is the hypothesis of
`NK.GlobalCFT.Galois.globalCFT_localFixed_infinite`
(`Submission/NK/GlobalCFT/Galois/globalCFT_localFixed_infinite.lean`); use
`NK.HassePrinciple.localUnitsEquiv`/`localUnitsEquiv_fixed_iff_ringEquiv_fixed` to translate the
`Rep`-action of `NK.HassePrinciple.localUnitsRep k ↥L u` into the `Units.map (localRingEquiv σ _)`
action, and `IsGalois.tower_top_of_isGalois` (+ `FiniteDimensional.right`) for `IsGalois ↥K ↥L`.
The conclusion of `globalCFT_localFixed_infinite` gives `a` with
`localAlgebraMapUnits … a = b`, and `Work.SSGRoute.localUnitsMap_spec` identifies that with
`(localUnitsMap …) (Additive.ofMul a)`. -/
theorem localUnitsMap_invariants {k Ω : Type} [Field k] [NumberField k] [Field Ω] [Algebra k Ω]
    [IsAlgClosure k Ω] {K L : IntermediateField k Ω} [FiniteDimensional k K] [IsGalois k K]
    [NumberField ↥K] [FiniteDimensional k L] [IsGalois k L] [NumberField ↥L]
    [Algebra ↥K ↥L] [IsScalarTower k ↥K ↥L] [IsScalarTower ↥K ↥L Ω]
    (w : NK.GlobalCFT.Place ↥K)
    (hw : ∀ q : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers ↥K),
      w ≠ NK.GlobalCFT.Place.ofFinite q)
    (u : NK.GlobalCFT.Place ↥L) (hu : NK.GlobalCFT.Place.LiesOver u w) :
    ∀ b : (NK.HassePrinciple.localUnitsRep k ↥L u).V,
      (∀ σ : ↥(SSGRoute.PTExt.decompK (k := k) u),
        (NK.HassePrinciple.localUnitsRep k ↥L u).ρ σ b = b) →
      ∃ a : (SSGRoute.PTExt.localUnitsK (k := k) (K := ↥K) w).V,
        (Work.SSGRoute.localUnitsMap k ↥K ↥L w u hu).hom a = b := by
  intro b hb
  -- The extension `↥K ⊆ ↥L` is again finite Galois.
  haveI : FiniteDimensional ↥K ↥L := FiniteDimensional.right k ↥K ↥L
  haveI : IsGalois ↥K ↥L := IsGalois.tower_top_of_isGalois k ↥K ↥L
  -- The place `w` is infinite (it is not a finite place), and `u | w` forces `u` infinite too.
  rcases w with w₀ | q
  · rcases u with u₀ | q'
    · -- Both places are infinite: `u = ofInfinite u₀`, `w = ofInfinite w₀`.
      have hlies : u₀.LiesOver w₀ := by
        obtain ⟨v', hv', hL⟩ :=
          (Work.SSGRoute.place_liesOver_ofInfinite_iff u₀ (NK.GlobalCFT.Place.ofInfinite w₀)).mp hu
        rw [NK.GlobalCFT.Place.ofInfinite_inj] at hv'
        rw [← hv'] at hL
        exact hL
      -- Restriction of scalars does not change the induced place-action.
      have hsmul : ∀ (σ : ↥L ≃ₐ[↥K] ↥L),
          AlgEquiv.restrictScalars k σ • (NK.GlobalCFT.Place.ofInfinite u₀)
            = σ • (NK.GlobalCFT.Place.ofInfinite u₀) := by
        intro σ
        rw [NK.GlobalCFT.Place.smul_ofInfinite, NK.GlobalCFT.Place.smul_ofInfinite]
        rfl
      -- Fixity of `b` under the `k`-stabiliser of `u`.
      have hfixk : ∀ σ : MulAction.stabilizer (↥L ≃ₐ[k] ↥L) (Sum.inl u₀),
          NK.HassePrinciple.localUnitsEquiv (K := k) (Sum.inl u₀) σ
            (Additive.toMul (b : (NK.HassePrinciple.localUnitsRep k ↥L (Sum.inl u₀)).V))
            = Additive.toMul (b : (NK.HassePrinciple.localUnitsRep k ↥L (Sum.inl u₀)).V) := by
        intro σ
        exact Additive.ofMul.injective (hb σ)
      -- Hence fixity under the smaller `K`-stabiliser, using the action comparison.
      have hfixK : ∀ σ : MulAction.stabilizer (↥L ≃ₐ[↥K] ↥L) (Sum.inl u₀),
          NK.HassePrinciple.localUnitsEquiv (K := ↥K) (Sum.inl u₀) σ
            (Additive.toMul (b : (NK.HassePrinciple.localUnitsRep k ↥L (Sum.inl u₀)).V))
            = Additive.toMul (b : (NK.HassePrinciple.localUnitsRep k ↥L (Sum.inl u₀)).V) := by
        intro σ
        rw [← localUnitsEquiv_restrictScalars_apply (k := k) (K := ↥K) (L := ↥L) (Sum.inl u₀)
          σ.1 σ.2 (by rw [hsmul]; exact σ.2)]
        exact hfixk ⟨AlgEquiv.restrictScalars k σ.1, by
          rw [MulAction.mem_stabilizer_iff, hsmul]; exact σ.2⟩
      -- Translate to the `localRingEquiv` form required by the local fixed point lemma.
      have hy : ∀ (σ : ↥L ≃ₐ[↥K] ↥L)
          (hσ : σ • NK.GlobalCFT.Place.ofInfinite u₀ = NK.GlobalCFT.Place.ofInfinite u₀),
          Units.map (NK.GlobalCFT.Place.localRingEquiv σ
              (NK.GlobalCFT.Place.ofInfinite u₀)).toMonoidHom
              (Additive.toMul (b : (NK.HassePrinciple.localUnitsRep k ↥L (Sum.inl u₀)).V))
            = hσ.symm ▸ (Additive.toMul (b : (NK.HassePrinciple.localUnitsRep k ↥L (Sum.inl u₀)).V)) :=
        (Work.SSGRoute.localUnitsEquiv_fixed_iff_ringEquiv_fixed_general
          (k := ↥K) (K := ↥L) (NK.GlobalCFT.Place.ofInfinite u₀)
          (Additive.toMul (b : (NK.HassePrinciple.localUnitsRep k ↥L (Sum.inl u₀)).V))).mp hfixK
      -- The archimedean local fixed point lemma.
      obtain ⟨a, ha⟩ := NK.GlobalCFT.Galois.globalCFT_localFixed_infinite
        (K := ↥K) (L := ↥L) hlies
        (Additive.toMul (b : (NK.HassePrinciple.localUnitsRep k ↥L (Sum.inl u₀)).V)) hy
      refine ⟨Additive.ofMul a, ?_⟩
      rw [Work.SSGRoute.localUnitsMap_spec (k := k) (K := ↥K) (L := ↥L)
        (u := (Sum.inl w₀)) (w := (Sum.inl u₀)) (hw := hu) a]
      have hpr : NK.GlobalCFT.Place.localAlgebraMapUnits (Sum.inl u₀) (Sum.inl w₀) hu
          = NK.GlobalCFT.Place.localAlgebraMapUnits (Sum.inl u₀) (Sum.inl w₀)
              (NK.GlobalCFT.Place.liesOver_ofInfinite hlies) := rfl
      rw [hpr, ha]
      rfl
    · -- `u` finite cannot lie over the infinite place `w`.
      exfalso
      obtain ⟨Q, hQ, _⟩ :=
        (Work.SSGRoute.place_liesOver_ofFinite_iff q' (NK.GlobalCFT.Place.ofInfinite w₀)).mp hu
      exact Sum.inl_ne_inr hQ
  · -- `w` a finite place contradicts `hw`.
    exact absurd rfl (hw q)

end Work.SSGRoute.PT
