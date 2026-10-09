import Mathlib
import Submission.Work.SSGRoute.PTDefsOmega
import Submission.Work.SSGRoute.Phi0Aux
import Submission.Work.SSGRoute.hbn_ext_units
import Submission.Work.SSGRoute.Phi0Kummer
import Submission.Work.SSGRoute.classIncl_inflation_injective
import Submission.Work.SSGRoute.e6_util
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-! Guidance from the project lead (the requester):

ROUTE: read Submission/Work/SSGRoute/DESIGN_FIX.md, section on the E4Ω replacement route (R1/R2/R3). Definitions: PTDefs.lean + PTDefsOmega.lean (do NOT edit). NK has Hasse–Brauer–Noether (hbnUnits, Submission/NK/HassePrinciple/*) and local |Br| = degree.

**R1 `phi0_family_vanish_of_local`** (new file; elaborated OK)
- `κ_L(h)` locally trivial everywhere implies `lam L h = 0`.
- Proof: `hbnUnits` (via E0b) gives `κ_L h = 0`. Kummer theory plus Hilbert 90 over `L` then give a
  level `L' ⊇ L` where `inflTrivIn h = 0`: `h` comes from `H¹(G, Lˣ/μ_p)`, and one adjoins the
  corresponding `p`-th root. Finally `hcompat` and injectivity of `inflC` (Commons + H1All).
- Size 0.5–1k.

**R2 `zeta_idele_class_pairing`** (new file; elaborated OK)
- For a `G`-invariant `a : Place K → ZMod p`, the class `c₀` of the idèle `(ζ^{a w})_w` pairs with
  `h` as the image in `C_L` of an idèle class whose `w'`-component is `a w • loc_{w'}(κ h)`.
- Proof: `(ζ^{a w})` is an idèle, since its components are units. The class is `G`-invariant and
  `p`-torsion. The local components come from naturality of the Yoneda product:
  `ideleToLocalUnits ∘ incl = unitsToLocalUnits` on `ζ`.
- Size 0.8–1.2k.

**R3 = `phi0_trivial_epi_in`** (the existing statement; now the assembly)
1. **`lam` factors through `Loc`.** By R1, `lam` factors through
   `Loc(κ(·)) ∈ ⊕_v Br(k_v)[p]` on the direct limit over `Ω`-levels.
2. **Extend.** Extend the factored functional to all of `⊕_v Br(k_v)[p]` (linear algebra, using
   `addHom_extend_of_exponent`).
3. **Read off `a_v`.** Each component is `a_v · ι_v`, because:
   - `Br(k_v)[p]` is cyclic of order `p` (NK `natCard_groupCohomology_two_units_local_eq_finrank`);
   - `ι_v` is injective (E8′), hence an isomorphism onto `A[p]`.
4. **Realise.** R2 with this `a` gives `c₀`.
5. **Compare.** The image in `C_L` of `y` is `Σ_w ι_w(y_w)`. This is Shapiro, E2 at level `L`: the
   localisations determine `y`. Hence `φ⁰(c₀) = lam`.

   Size 1–1.5k.

**Consumers.** None change. E5s consumes only the E4Ω statement. E3Ω, E7cΩ and E9 do not use E4.

**E4Ω total.** 2.3–3.7k, replacing 1.5–2.5k. Risk: medium. The heavy parts are the Kummer
"dies at a higher level" step in R1 and the local cyclicity and E8′ bookkeeping in R3. No
research-scale gap: every input is Hasse–Brauer–Noether (proved), local `|Br| = degree` (proved),
E8′ (a route from proved HR), E0b and E2.
-/

namespace Work.SSGRoute

open SSGRoute.PTExt CategoryTheory

/-- The E0b bridge `eBridge` intertwines the level inflation `inflC` of `PTDefs` with the
group-cohomology map `groupCohomology.map (galRes k F L) (classIncl k F L)`. -/
lemma inflC_eq_eBridge_map (k F L : Type) [Field k] [NumberField k] [Field F] [NumberField F]
    [Field L] [NumberField L] [Algebra k F] [Algebra F L] [Algebra k L] [IsScalarTower k F L]
    [FiniteDimensional k F] [IsGalois k F] [FiniteDimensional k L] [IsGalois k L]
    (y : extH (classesK k F) 2) :
    inflC (k := k) (K := F) (L := L) y
      = E0bGroupCoeff.eBridge 2 (L ≃ₐ[k] L) (classesK k L)
          ((groupCohomology.map (galRes k F L) (classIncl k F L) 2).hom
            ((E0bGroupCoeff.eBridge 2 (F ≃ₐ[k] F) (classesK k F)).symm y)) := by
  have hnat := hbnAux_eBridge_natural (galRes k F L) (classIncl k F L) 2
    ((E0bGroupCoeff.eBridge 2 (F ≃ₐ[k] F) (classesK k F)).symm y)
  rw [AddEquiv.apply_symm_apply] at hnat
  rw [hnat]
  rfl

/-- **Injectivity of the level inflation on `H²(·, C_·)`**, transported from the
group-cohomology statement `classIncl_inflation_injective` across the E0b bridge. -/
lemma inflC_injective_aux (k F L : Type) [Field k] [NumberField k] [Field F] [NumberField F]
    [Field L] [NumberField L] [Algebra k F] [Algebra F L] [Algebra k L] [IsScalarTower k F L]
    [FiniteDimensional k F] [IsGalois k F] [FiniteDimensional k L] [IsGalois k L] :
    Function.Injective (fun y : extH (classesK k F) 2 => inflC (k := k) (K := F) (L := L) y) := by
  intro y y' hyy'
  have hg := classIncl_inflation_injective k F L
  have hyy'b : inflC (k := k) (K := F) (L := L) y
      = inflC (k := k) (K := F) (L := L) y' := hyy'
  have h1 : (groupCohomology.map (galRes k F L) (classIncl k F L) 2).hom
        ((E0bGroupCoeff.eBridge 2 (F ≃ₐ[k] F) (classesK k F)).symm y)
      = (groupCohomology.map (galRes k F L) (classIncl k F L) 2).hom
        ((E0bGroupCoeff.eBridge 2 (F ≃ₐ[k] F) (classesK k F)).symm y') := by
    apply (E0bGroupCoeff.eBridge 2 (L ≃ₐ[k] L) (classesK k L)).injective
    exact (inflC_eq_eBridge_map k F L y).symm.trans
      (hyy'b.trans (inflC_eq_eBridge_map k F L y'))
  exact (E0bGroupCoeff.eBridge 2 (F ≃ₐ[k] F) (classesK k F)).symm.injective (hg h1)

/-- **Injectivity of the level inflation `inflCIn` on `H²(·, C_·)`.** -/
lemma inflCIn_injective (k K : Type) [Field k] [NumberField k] [Field K] [NumberField K]
    [Algebra k K] (Ω : Type) [Field Ω] [Algebra K Ω] [Algebra k Ω] [IsScalarTower k K Ω]
    (L L' : IntermediateField K Ω) [NumberField L] [NumberField L']
    [FiniteDimensional k L] [IsGalois k L] [FiniteDimensional k L'] [IsGalois k L']
    (hLL : L ≤ L') :
    Function.Injective (fun y : extH (classesK k L) 2 => inflCIn (k := k) hLL y) := by
  letI : Algebra ↥L ↥L' := (IntermediateField.inclusion hLL).toAlgebra
  haveI : IsScalarTower k ↥L ↥L' := IsScalarTower.of_algebraMap_eq (fun _ => rfl)
  exact inflC_injective_aux k ↥L ↥L'

/-- **E4Ω-R1 (Kummer + Hasse–Brauer–Noether).** Let `lam` be a compatible `p`-torsion family of
functionals `H²(Gal(L/k), 𝔽_p) → H²(Gal(L/k), C_L)` over the levels `K ≤ L ≤ Ω`, with `μ_p ⊆ k`.
If the Brauer class `κ(h) ∈ H²(Gal(L/k), Lˣ)` of `h` (push along `𝔽_p ≅ μ_p ⊆ Lˣ`, `1 ↦ ζ`) is
locally trivial at every place of `L`, then `lam L h = 0`. -/
theorem phi0_family_vanish_of_local (p : ℕ) [Fact p.Prime] (k K : Type) [Field k] [NumberField k] [Field K] [NumberField K] [Algebra k K]
    [FiniteDimensional k K] [IsGalois k K] (Ω : Type) [Field Ω] [IsAlgClosed Ω] [Algebra K Ω]
    [Algebra k Ω] [IsScalarTower k K Ω]
    (ζ : k) (hζ : IsPrimitiveRoot ζ p)
    (lam : ∀ (L : IntermediateField K Ω) [NumberField L] [FiniteDimensional k L] [IsGalois k L],
      extH (Rep.trivial Coeff (L ≃ₐ[k] L) (ZMod p)) 2 →+ extH (classesK k L) 2)
    (hp : ∀ (L : IntermediateField K Ω) [NumberField L] [FiniteDimensional k L] [IsGalois k L]
      (h : extH (Rep.trivial Coeff (L ≃ₐ[k] L) (ZMod p)) 2), p • lam L h = 0)
    (hcompat : ∀ (L : IntermediateField K Ω) [NumberField L] [FiniteDimensional k L] [IsGalois k L] (L' : IntermediateField K Ω) [NumberField L'] [FiniteDimensional k L'] [IsGalois k L'] (hLL : L ≤ L')
      (h : extH (Rep.trivial Coeff (L ≃ₐ[k] L) (ZMod p)) 2),
      inflCIn (k := k) hLL (lam L h) = lam L' (inflTrivIn (k := k) hLL (ZMod p) h))
    (L : IntermediateField K Ω) [NumberField L] [FiniteDimensional k L] [IsGalois k L]
    (z : Rep.trivial Coeff (L ≃ₐ[k] L) (ZMod p) ⟶ unitsK k L)
    (hz : ((Additive.toMul (z.hom (1 : ZMod p)) : Lˣ) : L) = algebraMap k L ζ)
    (h : extH (Rep.trivial Coeff (L ≃ₐ[k] L) (ZMod p)) 2)
    (hloc : ∀ w : NK.GlobalCFT.Place L,
      (extHRestrict (MulAction.stabilizer (L ≃ₐ[k] L) w)
          (h.comp (Abelian.Ext.mk₀ z) (add_zero 2))).comp
        (Abelian.Ext.mk₀ (NK.HassePrinciple.unitsToLocalUnits k L w)) (add_zero 2) = 0) :
    lam L h = 0 := by
  -- **Step 1 (Hasse–Brauer–Noether, in `Ext` form).**  The Kummer push `κ(h) = h.comp (mk₀ z)`
  -- is locally trivial at every place of `L`, hence zero.
  have hk : h.comp (Abelian.Ext.mk₀ z) (add_zero 2) = 0 :=
    hbn_ext_units k L _ hloc
  -- **Step 2 (Kummer theory).**  A class killed by the Kummer map dies at a bigger level.
  obtain ⟨L', hNF, hfd, hgal, hLL, hzero⟩ :=
    Phi0Kummer.kummer_dies_at_higher_level p k K Ω ζ hζ L z hz h hk
  letI : NumberField L' := hNF
  letI : FiniteDimensional k L' := hfd
  letI : IsGalois k L' := hgal
  letI : Algebra L L' := (IntermediateField.inclusion hLL).toAlgebra
  haveI : IsScalarTower k L L' := IsScalarTower.of_algebraMap_eq (fun _ => rfl)
  -- **Step 3 (compatibility of the family).**
  have hcomp : inflCIn (k := k) hLL (lam L h) = 0 := by
    rw [hcompat L L' hLL h, hzero, map_zero]
  -- **Step 4 (inflation is injective on `H²(·, C_·)`).**  The group-cohomology statement
  -- `classIncl_inflation_injective` is transported across the E0b bridge `eBridge`, which is
  -- natural under a change of group and coefficients (`hbnAux_eBridge_natural`).
  have hinj : Function.Injective (fun y : extH (classesK k L) 2 => inflCIn (k := k) hLL y) :=
    inflCIn_injective k K Ω L L' hLL
  have h0 : inflCIn (k := k) hLL (0 : extH (classesK k L) 2) = 0 :=
    E6Util.extHMap_zero (galRes k ↥L ↥L') (classIncl k ↥L ↥L')
  exact hinj (hcomp.trans h0.symm)

end Work.SSGRoute
