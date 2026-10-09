import Mathlib
import Submission.Work.SSGRoute.PTDefsOmega
import Submission.Work.SSGRoute.e7comega_defs
import Submission.Work.SSGRoute.E9c.TransportDefs
import Submission.Work.SSGRoute.localUnitsMap_exists
import Submission.Work.SSGRoute.e9c_transport_zero
import Submission.Work.SSGRoute.eq_zero_of_isUnramifiedExt_of_unramified
import Submission.Work.SSGRoute.E7cOmega.exists_level_p_dvd_decomp
import Submission.Work.SSGRoute.local_duality_ext_detect_h
import Submission.Work.SSGRoute.ssg_levelNorm_valuation
import Submission.NK.HassePrinciple.localUnits_h2_injective
import Submission.Work.SSGRoute.ValuationSES.C4.gen.valHom_localUnitsMap
import Submission.Work.SSGRoute.E7cOmega.exists_level_unramified_detecting_class
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace Work.SSGRoute

open CategoryTheory SSGRoute.PTExt Representation
open NK.GlobalCFT (Place)
open scoped NumberField

/-! ## The valuation criterion for `IsUnramifiedExt` (node C1 of the E7cΩ route)

The unramified subgroup of `Ext¹_{D_w}(M, K_wˣ)` is the kernel of the valuation push
`Ext¹_{D_w}(M, K_wˣ) → Ext¹_{D_w}(M, ℤ)`, by the long exact `Ext`-sequence of the short exact
sequence of `D_w`-modules `0 → 𝒪_wˣ → K_wˣ --v--> ℤ → 0`
(`NK.HassePrinciple.localUnitsShortComplex_shortExact`). -/

/-- **The valuation criterion.** A class `y ∈ Ext¹_{D_q}(M, K_qˣ)` is unramified at `q` if and only
if its push along the valuation vanishes. -/
theorem isUnramifiedExt_iff_valPush_eq_zero {k K : Type} [Field k] [NumberField k] [Field K]
    [NumberField K] [Algebra k K] [FiniteDimensional k K] [IsGalois k K]
    (q : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K))
    {M : Rep Coeff (decompK (k := k) (K := K) (Place.ofFinite q))}
    (y : Abelian.Ext M (localUnitsK (k := k) (K := K) (Place.ofFinite q)) 1) :
    IsUnramifiedExt (k := k) (K := K) (Place.ofFinite q) y ↔
      y.comp (Abelian.Ext.mk₀ (NK.HassePrinciple.localUnitsValHom (K := k) (L := K) q))
        (add_zero 1) = 0 := by
  constructor
  · rintro ⟨z, rfl⟩
    rw [CategoryTheory.Abelian.Ext.comp_assoc_of_second_deg_zero z
      (CategoryTheory.Abelian.Ext.mk₀ (NK.HassePrinciple.localUnitsIncl (K := k) (L := K)
        (Place.ofFinite q)))
      (CategoryTheory.Abelian.Ext.mk₀ (NK.HassePrinciple.localUnitsValHom (K := k) (L := K) q))
      (add_zero 1)]
    rw [CategoryTheory.Abelian.Ext.mk₀_comp_mk₀,
      NK.HassePrinciple.localUnitsIncl_comp_valHom (K := k) (L := K) q,
      CategoryTheory.Abelian.Ext.mk₀_zero]
    exact CategoryTheory.Abelian.Ext.comp_zero _ _ _ _ _
  · intro hy
    obtain ⟨z, hz⟩ := CategoryTheory.Abelian.Ext.covariant_sequence_exact₂ M
      (NK.HassePrinciple.localUnitsShortComplex_shortExact (K := k) (L := K) q) y hy
    exact ⟨z, hz.symm⟩

/-! ## Bilinearity of the level pairing, for the assembly of the target

The assembly pushes the level pairing along the valuation `K_qˣ → L_{q'}ˣ ≅ e·v_q`, so it needs the
`ℕ`-linearity of `levelPair` in both the coefficient morphism and the `Ext`-variable. -/

/-- The `Ext`-composition of a scalar multiple is the scalar multiple of the composition. -/
theorem nsmul_comp_coeff {G : Type} [Group G] {X Y Z : Rep.{0} Coeff G}
    {r s t : ℕ} (n : ℕ) (x : Abelian.Ext.{0} X Y r) (β : Abelian.Ext.{0} Y Z s)
    (h : r + s = t) : (n • x).comp β h = n • (x.comp β h) := by
  induction n with
  | zero => rw [zero_nsmul, Abelian.Ext.zero_comp, zero_nsmul]
  | succ k ih => rw [succ_nsmul, Abelian.Ext.add_comp, ih, succ_nsmul]

/-- **The level pairing is additive in the coefficient morphism.** -/
theorem levelPair_add_coeff {G H : Type} [Group G] [Group H] (f : H →* G)
    {M A : Rep.{0} Coeff G} {B : Rep.{0} Coeff H}
    (ι ι' : Rep.res f A ⟶ B) {r s : ℕ} (x : Abelian.Ext.{0} M A r)
    (h : extH (Rep.res f M) s) :
    levelPair f (ι + ι') x h = levelPair f ι x h + levelPair f ι' x h := by
  simp only [levelPair, Abelian.Ext.mk₀_add, Abelian.Ext.comp_add]

/-- **The level pairing is `ℕ`-linear in the coefficient morphism.** -/
theorem levelPair_nsmul_coeff {G H : Type} [Group G] [Group H] (f : H →* G)
    {M A : Rep.{0} Coeff G} {B : Rep.{0} Coeff H}
    (n : ℕ) (ι : Rep.res f A ⟶ B) {r s : ℕ} (x : Abelian.Ext.{0} M A r)
    (h : extH (Rep.res f M) s) :
    levelPair f (n • ι) x h = n • levelPair f ι x h := by
  induction n with
  | zero =>
      rw [zero_nsmul, zero_nsmul]
      simp only [levelPair, Abelian.Ext.mk₀_zero, Abelian.Ext.comp_zero]
  | succ k ih =>
      rw [succ_nsmul, levelPair_add_coeff, ih, succ_nsmul]

/-- **The level pairing is `ℕ`-linear in the `Ext`-variable.** -/
theorem levelPair_nsmul_x {G H : Type} [Group G] [Group H] (f : H →* G)
    {M A : Rep.{0} Coeff G} {B : Rep.{0} Coeff H}
    (ι : Rep.res f A ⟶ B) {r s : ℕ} (n : ℕ) (x : Abelian.Ext.{0} M A r)
    (h : extH (Rep.res f M) s) :
    levelPair f ι (n • x) h = n • levelPair f ι x h := by
  induction n with
  | zero =>
      rw [zero_nsmul, zero_nsmul]
      exact levelPair_zero f ι h
  | succ k ih =>
      rw [succ_nsmul, levelPair_add, ih, succ_nsmul]

theorem localUnitsMap_comp_valHom_mor (k K L : Type) [Field k] [NumberField k]
    [Field K] [NumberField K] [Algebra k K] [FiniteDimensional k K] [IsGalois k K]
    [Field L] [NumberField L] [Algebra k L] [Algebra K L] [IsScalarTower k K L]
    [FiniteDimensional k L] [IsGalois k L]
    (Q : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K))
    (q' : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers L))
    (hq' : NK.GlobalCFT.Place.LiesOver (NK.GlobalCFT.Place.ofFinite q')
      (NK.GlobalCFT.Place.ofFinite Q)) :
    (Work.SSGRoute.localUnitsMap k K L (NK.GlobalCFT.Place.ofFinite Q)
        (NK.GlobalCFT.Place.ofFinite q') hq'
      ≫ NK.HassePrinciple.localUnitsValHom (K := k) (L := L) q')
      = (q'.asIdeal.ramificationIdx (NumberField.RingOfIntegers K)) •
        (Rep.resMap (Work.SSGRoute.decompKRestrict k K L (NK.GlobalCFT.Place.ofFinite Q)
            (NK.GlobalCFT.Place.ofFinite q') hq')
          (NK.HassePrinciple.localUnitsValHom (K := k) (L := K) Q)) := by
  apply Rep.hom_ext
  apply Representation.IntertwiningMap.ext
  apply LinearMap.ext
  intro a
  obtain ⟨u, hu⟩ : ∃ u : (NK.GlobalCFT.Place.localField K
      (NK.GlobalCFT.Place.ofFinite Q))ˣ, Additive.ofMul u = a :=
    ⟨Additive.toMul
        (show Additive ((NK.GlobalCFT.Place.localField K
          (NK.GlobalCFT.Place.ofFinite Q))ˣ) from a),
      Equiv.apply_symm_apply Additive.ofMul
        (show Additive ((NK.GlobalCFT.Place.localField K
          (NK.GlobalCFT.Place.ofFinite Q))ˣ) from a)⟩
  rw [← hu]
  change (Rep.Hom.hom (Work.SSGRoute.localUnitsMap k K L (NK.GlobalCFT.Place.ofFinite Q)
        (NK.GlobalCFT.Place.ofFinite q') hq'
      ≫ NK.HassePrinciple.localUnitsValHom (K := k) (L := L) q')) (Additive.ofMul u)
      = (Rep.Hom.hom ((q'.asIdeal.ramificationIdx (NumberField.RingOfIntegers K)) •
          Rep.resMap (Work.SSGRoute.decompKRestrict k K L (NK.GlobalCFT.Place.ofFinite Q)
            (NK.GlobalCFT.Place.ofFinite q') hq')
            (NK.HassePrinciple.localUnitsValHom (K := k) (L := K) Q))) (Additive.ofMul u)
  set_option backward.isDefEq.respectTransparency false in
  rw [Rep.comp_apply, Rep.nsmul_hom, Representation.IntertwiningMap.coe_nsmul, Pi.smul_apply,
    Rep.resMap_hom_apply]
  exact Work.SSGRoute.ValuationSES.C4.gen.valHom_localUnitsMap k K L Q q' hq' u

theorem levelPair_comp_valHom_general (k K L : Type) [Field k] [NumberField k]
    [Field K] [NumberField K] [Algebra k K] [FiniteDimensional k K] [IsGalois k K]
    [Field L] [NumberField L] [Algebra k L] [Algebra K L] [IsScalarTower k K L]
    [FiniteDimensional k L] [IsGalois k L]
    (M : Rep SSGRoute.PTExt.Coeff (K ≃ₐ[k] K)) [Finite M]
    (Q : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K))
    (q' : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers L))
    (hq' : NK.GlobalCFT.Place.LiesOver (NK.GlobalCFT.Place.ofFinite q')
      (NK.GlobalCFT.Place.ofFinite Q))
    (y : CategoryTheory.Abelian.Ext
      (Rep.res (SSGRoute.PTExt.decompK (k := k) (K := K)
        (NK.GlobalCFT.Place.ofFinite Q)).subtype M)
      (SSGRoute.PTExt.localUnitsK (k := k) (K := K) (NK.GlobalCFT.Place.ofFinite Q)) 1)
    (h : SSGRoute.PTExt.extH (Rep.res (SSGRoute.PTExt.galRes k K L) M) 1) :
    (SSGRoute.PTExt.levelPair
        (Work.SSGRoute.decompKRestrict k K L (NK.GlobalCFT.Place.ofFinite Q)
          (NK.GlobalCFT.Place.ofFinite q') hq')
        (Work.SSGRoute.localUnitsMap k K L (NK.GlobalCFT.Place.ofFinite Q)
          (NK.GlobalCFT.Place.ofFinite q') hq') y
        (SSGRoute.PTExt.extHRestrict
          (SSGRoute.PTExt.decompK (k := k) (K := L) (NK.GlobalCFT.Place.ofFinite q')) h)).comp
      (CategoryTheory.Abelian.Ext.mk₀
        (NK.HassePrinciple.localUnitsValHom (K := k) (L := L) q')) (add_zero 2)
    = (q'.asIdeal.ramificationIdx (NumberField.RingOfIntegers K)) •
      (SSGRoute.PTExt.levelPair
        (Work.SSGRoute.decompKRestrict k K L (NK.GlobalCFT.Place.ofFinite Q)
          (NK.GlobalCFT.Place.ofFinite q') hq')
        (SSGRoute.PTExt.trivResInv
          (Work.SSGRoute.decompKRestrict k K L (NK.GlobalCFT.Place.ofFinite Q)
            (NK.GlobalCFT.Place.ofFinite q') hq') SSGRoute.PTExt.Coeff)
        (y.comp (CategoryTheory.Abelian.Ext.mk₀
          (NK.HassePrinciple.localUnitsValHom (K := k) (L := K) Q)) (add_zero 1))
        (SSGRoute.PTExt.extHRestrict
          (SSGRoute.PTExt.decompK (k := k) (K := L) (NK.GlobalCFT.Place.ofFinite q')) h)) := by
  let rh : SSGRoute.PTExt.extH (Rep.res (Work.SSGRoute.decompKRestrict k K L
      (NK.GlobalCFT.Place.ofFinite Q) (NK.GlobalCFT.Place.ofFinite q') hq')
      (Rep.res (SSGRoute.PTExt.decompK (k := k) (K := K)
        (NK.GlobalCFT.Place.ofFinite Q)).subtype M)) 1 :=
    SSGRoute.PTExt.extHRestrict (SSGRoute.PTExt.decompK (k := k) (K := L)
      (NK.GlobalCFT.Place.ofFinite q')) h
  have hcomp := Work.SSGRoute.levelPair_comp
    (Work.SSGRoute.decompKRestrict k K L (NK.GlobalCFT.Place.ofFinite Q)
      (NK.GlobalCFT.Place.ofFinite q') hq')
    (Work.SSGRoute.localUnitsMap k K L (NK.GlobalCFT.Place.ofFinite Q)
      (NK.GlobalCFT.Place.ofFinite q') hq')
    (NK.HassePrinciple.localUnitsValHom (K := k) (L := L) q') y rh
  have hmap := localUnitsMap_comp_valHom_mor k K L Q q' hq'
  have hlin := Work.SSGRoute.levelPair_nsmul_coeff
    (f := Work.SSGRoute.decompKRestrict k K L (NK.GlobalCFT.Place.ofFinite Q)
      (NK.GlobalCFT.Place.ofFinite q') hq')
    (M := Rep.res (SSGRoute.PTExt.decompK (k := k) (K := K)
      (NK.GlobalCFT.Place.ofFinite Q)).subtype M)
    (A := SSGRoute.PTExt.localUnitsK (k := k) (K := K) (NK.GlobalCFT.Place.ofFinite Q))
    (B := SSGRoute.PTExt.unitRep (SSGRoute.PTExt.decompK (k := k) (K := L)
      (NK.GlobalCFT.Place.ofFinite q')))
    (n := q'.asIdeal.ramificationIdx (NumberField.RingOfIntegers K))
    (ι := Rep.resMap (Work.SSGRoute.decompKRestrict k K L (NK.GlobalCFT.Place.ofFinite Q)
      (NK.GlobalCFT.Place.ofFinite q') hq')
      (NK.HassePrinciple.localUnitsValHom (K := k) (L := K) Q))
    (x := y) (h := rh)
  have hcomp_id : Rep.resMap (Work.SSGRoute.decompKRestrict k K L
        (NK.GlobalCFT.Place.ofFinite Q) (NK.GlobalCFT.Place.ofFinite q') hq')
      (NK.HassePrinciple.localUnitsValHom (K := k) (L := K) Q)
      ≫ SSGRoute.PTExt.trivResInv (Work.SSGRoute.decompKRestrict k K L
        (NK.GlobalCFT.Place.ofFinite Q) (NK.GlobalCFT.Place.ofFinite q') hq')
        SSGRoute.PTExt.Coeff
      = Rep.resMap (Work.SSGRoute.decompKRestrict k K L
        (NK.GlobalCFT.Place.ofFinite Q) (NK.GlobalCFT.Place.ofFinite q') hq')
        (NK.HassePrinciple.localUnitsValHom (K := k) (L := K) Q) := by
    rfl
  have hident : SSGRoute.PTExt.levelPair
        (Work.SSGRoute.decompKRestrict k K L (NK.GlobalCFT.Place.ofFinite Q)
          (NK.GlobalCFT.Place.ofFinite q') hq')
        (Rep.resMap (Work.SSGRoute.decompKRestrict k K L (NK.GlobalCFT.Place.ofFinite Q)
          (NK.GlobalCFT.Place.ofFinite q') hq')
          (NK.HassePrinciple.localUnitsValHom (K := k) (L := K) Q)) y rh
      = SSGRoute.PTExt.levelPair
        (Work.SSGRoute.decompKRestrict k K L (NK.GlobalCFT.Place.ofFinite Q)
          (NK.GlobalCFT.Place.ofFinite q') hq')
        (SSGRoute.PTExt.trivResInv (Work.SSGRoute.decompKRestrict k K L
          (NK.GlobalCFT.Place.ofFinite Q) (NK.GlobalCFT.Place.ofFinite q') hq')
          SSGRoute.PTExt.Coeff)
        (y.comp (CategoryTheory.Abelian.Ext.mk₀
          (NK.HassePrinciple.localUnitsValHom (K := k) (L := K) Q)) (add_zero 1))
        rh := by
    have hext : SSGRoute.PTExt.extRes (Work.SSGRoute.decompKRestrict k K L
          (NK.GlobalCFT.Place.ofFinite Q) (NK.GlobalCFT.Place.ofFinite q') hq')
          (y.comp (CategoryTheory.Abelian.Ext.mk₀
            (NK.HassePrinciple.localUnitsValHom (K := k) (L := K) Q)) (add_zero 1))
        = (SSGRoute.PTExt.extRes (Work.SSGRoute.decompKRestrict k K L
            (NK.GlobalCFT.Place.ofFinite Q) (NK.GlobalCFT.Place.ofFinite q') hq') y).comp
          (CategoryTheory.Abelian.Ext.mk₀ (Rep.resMap (Work.SSGRoute.decompKRestrict k K L
            (NK.GlobalCFT.Place.ofFinite Q) (NK.GlobalCFT.Place.ofFinite q') hq')
            (NK.HassePrinciple.localUnitsValHom (K := k) (L := K) Q))) (add_zero 1) := by
      simp only [SSGRoute.PTExt.extRes, CategoryTheory.Abelian.Ext.mapExactFunctor_comp,
        CategoryTheory.Abelian.Ext.mapExactFunctor_mk₀]
    rw [SSGRoute.PTExt.levelPair, SSGRoute.PTExt.levelPair, hext,
      CategoryTheory.Abelian.Ext.comp_assoc, CategoryTheory.Abelian.Ext.mk₀_comp_mk₀, hcomp_id]
    all_goals rfl
  refine hcomp.symm.trans ?_
  refine hmap ▸ ?_
  exact hlin.trans (congrArg (fun z =>
    (q'.asIdeal.ramificationIdx (NumberField.RingOfIntegers K)) • z) hident)

/-- **The unramified half of local Tate duality, in class-formation form.**  (The one remaining node
of `Work.SSGRoute.local_phi_realization_in`; every other part of that file is proved, and this exact
statement appears there as `Work.SSGRoute.isUnramifiedExt_of_levelPair_unramified_aux` with the single
`sorry` of the file.  When this node lands, that `sorry` is replaced by it.)

Let `k ⊆ K` be number fields with `K/k` finite Galois, `Ω` algebraically closed over `K`, `M` a finite
`p`-torsion `Gal(K/k)`-module, `w = Place.ofFinite q` a finite place of `K` with `p ∉ q`, and suppose
the inertia group of `q` acts trivially on `M`.  Let `y ∈ Ext¹_{D_w}(M, K_wˣ)`.  If `y` pairs to zero,
at every `Ω`-level `L ⊇ K` and every place `q'` of `L` above `q`, with every class `h ∈
H¹(Gal(L/k), res M)` unramified at `q'`, then `y` is unramified at `w` (lies in the image of
`Ext¹_{D_w}(M, 𝒪_wˣ) → Ext¹_{D_w}(M, K_wˣ)`).

Mathematically: the unramified subgroups of `H¹` and `Ext¹` are exact annihilators (Milne, ADT I.2).

**Route** (designed by the project lead; read `Submission/Work/SSGRoute/E7cOmega/lead_notes/E7COMEGA.md`
§2–3, 7 nodes C1–C7, ~2k lines; no dévissage over `M` is needed): C1 the valuation criterion
`IsUnramifiedExt w y ↔ y ≫ mk₀ valRep = 0` from `0 → 𝒪_wˣ → K_wˣ →v ℤ → 0` (build that short exact
sequence of `D_w`-modules — `NK.HassePrinciple.localUnitsSubRep` is its first term, the valuation on
`(q.adicCompletion K)ˣ` is `Valued.v`, cf. `NK.GlobalCFT.Place.mem_localUnits_ofFinite_iff_valued_eq_one`
— and use exactness of the covariant `Ext` sequence together with `Hom_{D_w}(M,ℤ) = 0` for finite `M`);
C2 `p ∣ e(w/v)` ⟹ every class is unramified (free win); C3 the level with `e(q'/q) = 1`, `p ∣ f(q'/q)`
(`Work.SSGRoute.E7cOmega.exists_level_unramified_p_dvd_inertiaDeg`, on disk with one `sorry`);
C4 naturality of `levelPair` pushed along the valuation; C5 nonvanishing of the cup product of a nonzero
valuation class with an unramified class with nonzero value at Frobenius; C6 the global unramified
detector (Kummer character via CRT, corestricted `K → k`, Mackey) — **riskiest; test on `M = 𝔽_p`
first**; C7 assembly (the `hy` shape is unchanged).  Proved inputs that are already on disk:
`Work.SSGRoute.levelPair_trivial_eq_zero_iff_norm`,
`Work.SSGRoute.E7cOmega.exists_val_pow_of_isLocalNorm_unramified`,
`Work.SSGRoute.SSG.levelNorm_valuation` (a port with the sibling file's compile errors fixed),
`Work.SSGRoute.e9c_unram_pairing` (easy direction: integral classes pair to unramified values),
`Work.SSGRoute.eq_zero_of_isUnramifiedExt_of_unramified` (an unramified `H²`-class vanishes when
`e = 1`), `Work.SSGRoute.levelPair_coeff_naturality`,
`Work.SSGRoute.levelPair_extLoc_eq_push`. -/
theorem isUnramifiedExt_of_levelPair_unramified (p : ℕ) [Fact p.Prime] (k K : Type) [Field k]
    [NumberField k] [Field K] [NumberField K] [Algebra k K] [FiniteDimensional k K] [IsGalois k K]
    (Ω : Type) [Field Ω] [IsAlgClosed Ω] [Algebra K Ω] [Algebra k Ω] [IsScalarTower k K Ω]
    (M : Rep SSGRoute.PTExt.Coeff (K ≃ₐ[k] K)) [Finite M] (hM : ∀ m : M, p • m = 0)
    (w : NK.GlobalCFT.Place K)
    (q : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K))
    (hwq : w = NK.GlobalCFT.Place.ofFinite q)
    (hpq : ((p : NumberField.RingOfIntegers K) ∉ q.asIdeal))
    (hI : ∀ σ : K ≃ₐ[k] K, SSGRoute.PTExt.IsInertiaAt q σ → ∀ m : M, M.ρ σ m = m)
    (y : CategoryTheory.Abelian.Ext
      (Rep.res (SSGRoute.PTExt.decompK (k := k) (K := K) w).subtype M)
      (SSGRoute.PTExt.localUnitsK (k := k) w) 1)
    (hy : ∀ (L : IntermediateField K Ω) [NumberField L] [FiniteDimensional k L] [IsGalois k L]
      (q' : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers L))
      (hq' : NK.GlobalCFT.Place.LiesOver (NK.GlobalCFT.Place.ofFinite q') w)
      (h : SSGRoute.PTExt.extH (Rep.res (SSGRoute.PTExt.galRes k K L) M) 1),
      SSGRoute.PTExt.IsUnramifiedClassAt q' h →
        SSGRoute.PTExt.levelPair
          (Work.SSGRoute.decompKRestrict k K L w (NK.GlobalCFT.Place.ofFinite q') hq')
          (Work.SSGRoute.localUnitsMap k K L w (NK.GlobalCFT.Place.ofFinite q') hq') y
          (SSGRoute.PTExt.extHRestrict
            (SSGRoute.PTExt.decompK (k := k) (K := ↥L) (NK.GlobalCFT.Place.ofFinite q')) h) = 0) :
    SSGRoute.PTExt.IsUnramifiedExt w y := by
  classical
  subst hwq
  by_contra hy'
  set φ : CategoryTheory.Abelian.Ext
      (Rep.res (SSGRoute.PTExt.decompK (k := k) (K := K)
        (NK.GlobalCFT.Place.ofFinite q)).subtype M)
      (SSGRoute.PTExt.unitRep (SSGRoute.PTExt.decompK (k := k) (K := K)
        (NK.GlobalCFT.Place.ofFinite q))) 1 :=
    y.comp (CategoryTheory.Abelian.Ext.mk₀
      (NK.HassePrinciple.localUnitsValHom (K := k) (L := K) q)) (add_zero 1) with hφdef
  have hφ : φ ≠ 0 := by
    intro h0
    exact hy' ((isUnramifiedExt_iff_valPush_eq_zero (k := k) (K := K) q y).mpr
      (hφdef ▸ h0))
  obtain ⟨L, hLnf, hLfd, hLgal, q', hq', h, hunr, hcop, hkey⟩ :=
    E7cOmega.exists_level_unramified_detecting_class p k K Ω M hM
      (NK.GlobalCFT.Place.ofFinite q) q rfl hpq hI φ hφ
  let rh : SSGRoute.PTExt.extH (Rep.res (Work.SSGRoute.decompKRestrict k K ↥L
      (NK.GlobalCFT.Place.ofFinite q) (NK.GlobalCFT.Place.ofFinite q') hq')
      (Rep.res (SSGRoute.PTExt.decompK (k := k) (K := K)
        (NK.GlobalCFT.Place.ofFinite q)).subtype M)) 1 :=
    SSGRoute.PTExt.extHRestrict (SSGRoute.PTExt.decompK (k := k) (K := ↥L)
      (NK.GlobalCFT.Place.ofFinite q')) h
  have hzero : SSGRoute.PTExt.levelPair
      (Work.SSGRoute.decompKRestrict k K ↥L (NK.GlobalCFT.Place.ofFinite q)
        (NK.GlobalCFT.Place.ofFinite q') hq')
      (Work.SSGRoute.localUnitsMap k K ↥L (NK.GlobalCFT.Place.ofFinite q)
        (NK.GlobalCFT.Place.ofFinite q') hq') y rh = 0 :=
    hy L q' hq' h hunr
  have hkey' : SSGRoute.PTExt.levelPair
      (Work.SSGRoute.decompKRestrict k K ↥L (NK.GlobalCFT.Place.ofFinite q)
        (NK.GlobalCFT.Place.ofFinite q') hq')
      (SSGRoute.PTExt.trivResInv (Work.SSGRoute.decompKRestrict k K ↥L
        (NK.GlobalCFT.Place.ofFinite q) (NK.GlobalCFT.Place.ofFinite q') hq')
        SSGRoute.PTExt.Coeff) φ rh ≠ 0 := hkey
  have hpush' : (SSGRoute.PTExt.levelPair
        (Work.SSGRoute.decompKRestrict k K ↥L (NK.GlobalCFT.Place.ofFinite q)
          (NK.GlobalCFT.Place.ofFinite q') hq')
        (Work.SSGRoute.localUnitsMap k K ↥L (NK.GlobalCFT.Place.ofFinite q)
          (NK.GlobalCFT.Place.ofFinite q') hq') y rh).comp
      (CategoryTheory.Abelian.Ext.mk₀
        (NK.HassePrinciple.localUnitsValHom (K := k) (L := ↥L) q')) (add_zero 2)
      = (q'.asIdeal.ramificationIdx (NumberField.RingOfIntegers K)) •
        (SSGRoute.PTExt.levelPair
          (Work.SSGRoute.decompKRestrict k K ↥L (NK.GlobalCFT.Place.ofFinite q)
            (NK.GlobalCFT.Place.ofFinite q') hq')
          (SSGRoute.PTExt.trivResInv (Work.SSGRoute.decompKRestrict k K ↥L
            (NK.GlobalCFT.Place.ofFinite q) (NK.GlobalCFT.Place.ofFinite q') hq')
            SSGRoute.PTExt.Coeff) φ rh) := by
    rw [levelPair_comp_valHom_general k K ↥L M q q' hq' y h, hφdef]
  have hVe : (q'.asIdeal.ramificationIdx (NumberField.RingOfIntegers K)) •
      (SSGRoute.PTExt.levelPair
        (Work.SSGRoute.decompKRestrict k K ↥L (NK.GlobalCFT.Place.ofFinite q)
          (NK.GlobalCFT.Place.ofFinite q') hq')
        (SSGRoute.PTExt.trivResInv (Work.SSGRoute.decompKRestrict k K ↥L
          (NK.GlobalCFT.Place.ofFinite q) (NK.GlobalCFT.Place.ofFinite q') hq')
          SSGRoute.PTExt.Coeff) φ rh) = 0 := by
    rw [← hpush', hzero]
    exact CategoryTheory.Abelian.Ext.zero_comp _ _ _ _ _
  have hpφ : p • φ = 0 := by
    rw [hφdef, ← nsmul_comp_coeff p y
      (CategoryTheory.Abelian.Ext.mk₀ (NK.HassePrinciple.localUnitsValHom (K := k) (L := K) q))
      (add_zero 1)]
    rw [ext_nsmul_p_torsion_left
      (X := Rep.res (SSGRoute.PTExt.decompK (k := k) (K := K)
        (NK.GlobalCFT.Place.ofFinite q)).subtype M)
      (Y := SSGRoute.PTExt.localUnitsK (k := k) (K := K) (NK.GlobalCFT.Place.ofFinite q))
      p (fun m => hM m) y, CategoryTheory.Abelian.Ext.zero_comp]
  have hVp : p •
      (SSGRoute.PTExt.levelPair
        (Work.SSGRoute.decompKRestrict k K ↥L (NK.GlobalCFT.Place.ofFinite q)
          (NK.GlobalCFT.Place.ofFinite q') hq')
        (SSGRoute.PTExt.trivResInv (Work.SSGRoute.decompKRestrict k K ↥L
          (NK.GlobalCFT.Place.ofFinite q) (NK.GlobalCFT.Place.ofFinite q') hq')
          SSGRoute.PTExt.Coeff) φ rh) = 0 := by
    rw [← levelPair_nsmul_x
      (f := Work.SSGRoute.decompKRestrict k K ↥L (NK.GlobalCFT.Place.ofFinite q)
        (NK.GlobalCFT.Place.ofFinite q') hq')
      (M := Rep.res (SSGRoute.PTExt.decompK (k := k) (K := K)
        (NK.GlobalCFT.Place.ofFinite q)).subtype M)
      (A := SSGRoute.PTExt.unitRep (SSGRoute.PTExt.decompK (k := k) (K := K)
        (NK.GlobalCFT.Place.ofFinite q)))
      (B := SSGRoute.PTExt.unitRep (SSGRoute.PTExt.decompK (k := k) (K := ↥L)
        (NK.GlobalCFT.Place.ofFinite q')))
      (ι := SSGRoute.PTExt.trivResInv (Work.SSGRoute.decompKRestrict k K ↥L
        (NK.GlobalCFT.Place.ofFinite q) (NK.GlobalCFT.Place.ofFinite q') hq')
        SSGRoute.PTExt.Coeff) (n := p) (x := φ) (h := rh)]
    rw [hpφ]
    exact levelPair_zero
      (f := Work.SSGRoute.decompKRestrict k K ↥L (NK.GlobalCFT.Place.ofFinite q)
        (NK.GlobalCFT.Place.ofFinite q') hq')
      (M := Rep.res (SSGRoute.PTExt.decompK (k := k) (K := K)
        (NK.GlobalCFT.Place.ofFinite q)).subtype M)
      (A := SSGRoute.PTExt.unitRep (SSGRoute.PTExt.decompK (k := k) (K := K)
        (NK.GlobalCFT.Place.ofFinite q)))
      (B := SSGRoute.PTExt.unitRep (SSGRoute.PTExt.decompK (k := k) (K := ↥L)
        (NK.GlobalCFT.Place.ofFinite q')))
      (ι := SSGRoute.PTExt.trivResInv (Work.SSGRoute.decompKRestrict k K ↥L
        (NK.GlobalCFT.Place.ofFinite q) (NK.GlobalCFT.Place.ofFinite q') hq')
        SSGRoute.PTExt.Coeff) rh
  have hdvd : addOrderOf (SSGRoute.PTExt.levelPair
        (Work.SSGRoute.decompKRestrict k K ↥L (NK.GlobalCFT.Place.ofFinite q)
          (NK.GlobalCFT.Place.ofFinite q') hq')
        (SSGRoute.PTExt.trivResInv (Work.SSGRoute.decompKRestrict k K ↥L
          (NK.GlobalCFT.Place.ofFinite q) (NK.GlobalCFT.Place.ofFinite q') hq')
          SSGRoute.PTExt.Coeff) φ rh) ∣ 1 := by
    have hg : addOrderOf (SSGRoute.PTExt.levelPair
        (Work.SSGRoute.decompKRestrict k K ↥L (NK.GlobalCFT.Place.ofFinite q)
          (NK.GlobalCFT.Place.ofFinite q') hq')
        (SSGRoute.PTExt.trivResInv (Work.SSGRoute.decompKRestrict k K ↥L
          (NK.GlobalCFT.Place.ofFinite q) (NK.GlobalCFT.Place.ofFinite q') hq')
          SSGRoute.PTExt.Coeff) φ rh) ∣
        Nat.gcd (q'.asIdeal.ramificationIdx (NumberField.RingOfIntegers K)) p :=
      Nat.dvd_gcd (addOrderOf_dvd_iff_nsmul_eq_zero.mpr hVe)
        (addOrderOf_dvd_iff_nsmul_eq_zero.mpr hVp)
    rwa [show Nat.gcd (q'.asIdeal.ramificationIdx (NumberField.RingOfIntegers K)) p = 1
      from hcop] at hg
  exact hkey' (AddMonoid.addOrderOf_eq_one_iff.mp (Nat.dvd_one.mp hdvd))

end Work.SSGRoute
