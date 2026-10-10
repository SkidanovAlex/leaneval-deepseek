import Mathlib.FieldTheory.KrullTopology
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.DedekindDomain.AdicValuation
import Mathlib.RingTheory.Flat.TorsionFree
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.NumberTheory.NumberField.Completion.InfinitePlace
import Mathlib.NumberTheory.NumberField.InfinitePlace.TotallyRealComplex
import Submission.Work.GrunwaldEscapeCore.exists_pow_eq_localImageAt_of_kummerChar_eq_on_decomp
import Submission.Work.GrunwaldEscapeCore.mk_onePlace_mem_normClassSubgroup_of_isSplitIn
import Submission.Work.GrunwaldEscapeCore.onePlace_mem_gesU_of_kummerChar_eq_zero_on_inertia
import Submission.Work.GrunwaldEscapeCore.prod_localFactor_eq_one_of_comm
import Submission.Work.SSGRoute.GrunwaldEscapeCore.gesCorrectionFromPrime
import Submission.Work.SSGRoute.ZDataMup.KummerSurjectivity.kummerCharZMod_surjective_levelK
import Submission.Work.SSGRoute.n4_char_separation
import Submission.Work.SSGRoute.step4_y_escape_v2.GesUFacts
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# The orthogonality of the Grünwald escape, in the specialisation `L₂ := K`

`Work.SSGRoute.GrunwaldEscapeCore.orthogonality_L2K` is the **only** new mathematical input needed
by the self-contained route to `Work.SSGRoute.GrunwaldEscapeCore.escape_realisation_core` (see
`NOTE_escape_selfcontained_route.md` in this directory for why the route through
`GrunwaldEscapeCore/grunwald_escape_correction.lean` is blocked: that statement is FALSE as frozen,
`Submission/Work/SSGRoute/COUNTEREXAMPLE_N2_grunwald_escape_relative.md`).

The proof is the elementary one of
`NOTE_orthogonality_L2K_assembly.md` (session 5): with `κ := ↥K`,

* `mk (fracIdele 𝔡)` for `𝔡 = tFreePart T' a` is the inverse of the class of the local product
  along `T'` of the principal idèle `(a)ᵥ` (`idele_decomposition_tFreePart`);
* the Kummer element `b` of the locally constant datum `g` exists by Kummer surjectivity;
* at every `𝔭 ∈ T'` the `a`-term and the `b`-term have the same value under a character `χ` killing
  `U' ⊔ N_{N'/↥K}C_{N'}`: either `A` (the element of `T` below `𝔭`) splits completely in `N`, and
  both terms are norm classes, or `h A ≡ 0` on the decomposition group and the two local images
  differ by a `p`-th power (`exists_pow_eq_localImageAt_of_kummerChar_eq_on_decomp`);
* the product of the `b`-terms over `T'` is `1` by the reciprocity product formula for `b` and the
  Kummer field `M(ζ)` over `↥K` (`prod_localFactor_eq_one_of_comm`), because every place outside
  `T'` contributes `1`: at a split place the local norm subgroup is everything, at a non-split place
  `hgram` makes the Kummer character vanish on the inertia so that the term lies in `U'`
  (`onePlace_mem_gesU_of_kummerChar_eq_zero_on_inertia`), and at an infinite place `↥K` is totally
  complex (`isTotallyComplex_of_primitiveRoot`).
-/

open _root_.SSGRoute
open scoped Pointwise
open NumberField IsDedekindDomain
open NK.GlobalCFT

namespace Work.SSGRoute.GrunwaldEscapeCore

set_option linter.unusedSectionVars false
set_option linter.style.haveILetI false
set_option maxHeartbeats 1600000
set_option synthInstance.maxHeartbeats 800000

/-- **The orthogonality of the Grünwald escape at `L₂ := K`.** -/
theorem orthogonality_L2K (p : ℕ) [Fact p.Prime] (hp : p ≠ 2) (k Ω : Type) [Field k]
    [NumberField k] [Field Ω] [Algebra k Ω] [IsAlgClosure k Ω] [IsAlgClosed Ω]
    (K : IntermediateField k Ω) [FiniteDimensional k K] [IsGalois k K]
    (ζ : ↥K) (hζ : IsPrimitiveRoot ζ p)
    (hKimag : p = 2 → ∀ c ∈ K.fixingSubgroup, c ^ 2 = 1 → c = 1)
    (N : IntermediateField k Ω) [FiniteDimensional k N] [IsGalois k N] (hKN : K ≤ N)
    (T : Finset (ValuationSubring Ω)) (hTfin : ∀ A ∈ T, SSGRoute.IsFinPlace k A)
    (hTdisj : ∀ A ∈ T, ∀ B ∈ T, Work.SSGRoute.gesKConj K A B → A = B)
    (hTcov : ∀ B : ValuationSubring Ω, SSGRoute.IsFinPlace k B →
      (B.valuation (p : Ω) < 1 ∨
        (∃ σ ∈ K.fixingSubgroup, SSGRoute.IsInertia k B σ ∧ σ ∉ N.fixingSubgroup)) →
      ∃ A ∈ T, Work.SSGRoute.gesKConj K A B)
    (g : (Ω ≃ₐ[k] Ω) → ZMod p)
    (hg : ∀ x ∈ K.fixingSubgroup, ∀ y ∈ K.fixingSubgroup, g (x * y) = g x + g y)
    (hgc : SSGRoute.IsLocConstOn K.fixingSubgroup g)
    (hgram : ∀ B : ValuationSubring Ω, SSGRoute.IsFinPlace k B →
      (∀ A ∈ T, ¬ Work.SSGRoute.gesKConj K A B) → ¬ SSGRoute.IsSplitIn k N B →
      ∀ σ ∈ K.fixingSubgroup, SSGRoute.IsInertia k B σ → g σ = 0)
    (h : ValuationSubring Ω → (Ω ≃ₐ[k] Ω) → ZMod p)
    (hh : ∀ A ∈ T, ∀ x ∈ SSGRoute.decomp k A ⊓ K.fixingSubgroup,
      ∀ y ∈ SSGRoute.decomp k A ⊓ K.fixingSubgroup, h A (x * y) = h A x + h A y)
    (hhc : ∀ A ∈ T, ∃ U : Subgroup (Ω ≃ₐ[k] Ω), IsOpen (U : Set (Ω ≃ₐ[k] Ω)) ∧
      ∀ x ∈ U, x ∈ SSGRoute.decomp k A ⊓ K.fixingSubgroup → h A x = 0)
    (horth : ∀ A ∈ T,
      (∀ σ ∈ SSGRoute.decomp k A ⊓ K.fixingSubgroup, h A σ = 0) ∨
      SSGRoute.IsSplitIn k N A)
    (T' : Finset (NK.Chebotarev.PrimeIdeal ↥K))
    (hTbelow : ∀ A ∈ T, ∃ 𝔭 ∈ T', A.comap (algebraMap ↥K Ω) =
      IsDedekindDomain.HeightOneSpectrum.valuationSubringAtPrime ↥K 𝔭)
    (hT'above : ∀ 𝔭 ∈ T', ∃ A ∈ T, A.comap (algebraMap ↥K Ω) =
      IsDedekindDomain.HeightOneSpectrum.valuationSubringAtPrime ↥K 𝔭)
    (M : IntermediateField ↥K Ω) [FiniteDimensional ↥K M] [IsGalois ↥K M] [NumberField ↥M]
    (hMnorm : Idele.normClassSubgroup ↥K ↥M =
      Work.SSGRoute.GrunwaldEscapeCore.gesU ↥K p T' ⊔
        Work.SSGRoute.EscapeCoreLib.pPowSubgroup p (IdeleClassGroup ↥K))
    (N' : IntermediateField ↥K Ω) [FiniteDimensional ↥K N'] [IsGalois ↥K N'] [NumberField ↥N']
    (hNN' : (N' : Set Ω) = (N : Set Ω))
    (a : (↥K)ˣ)
    (ha : ∀ A ∈ T, ∀ σ : ↥(SSGRoute.decomp k A ⊓ K.fixingSubgroup),
      g (σ : Ω ≃ₐ[k] Ω) + h A (σ : Ω ≃ₐ[k] Ω) =
        Work.SSGRoute.kummerCharZMod (K := ↥K) (Ω := Ω) p (ζ := ζ) hζ a
          (Work.SSGRoute.gesLocalToGalK K σ)) :
    IdeleClassGroup.mk ↥K (NK.NUV2.RouteB.RayModulus.fracIdele
        (Work.SSGRoute.tFreePart (K := ↥K) T' a)) ∈
      Idele.normClassSubgroup ↥K ↥M ⊔ Idele.normClassSubgroup ↥K ↥N' := by
  classical
  haveI hNumK : NumberField ↥K := NumberField.of_module_finite k ↥K
  haveI hAlgCl : IsAlgClosure ↥K Ω :=
    (isAlgClosure_iff (k := ↥K) Ω).mpr ⟨IsAlgClosure.isAlgClosed k, inferInstance⟩
  -- the subgroups `U' = gesU ⊔ C^p` and `W = N_{N'/↥K}C_{N'}`
  let U' : Subgroup (IdeleClassGroup ↥K) :=
    Work.SSGRoute.GrunwaldEscapeCore.gesU ↥K p T' ⊔
      Work.SSGRoute.EscapeCoreLib.pPowSubgroup p (IdeleClassGroup ↥K)
  let W : Subgroup (IdeleClassGroup ↥K) := Idele.normClassSubgroup ↥K ↥N'
  haveI hUfin : U'.FiniteIndex :=
    Work.SSGRoute.step4_y_escape_v2.finiteIndex_gesU_sup_pPow (p := p) (K := ↥K) T'
  haveI hfin : (U' ⊔ W).FiniteIndex :=
    Subgroup.finiteIndex_of_le (le_sup_left : U' ≤ U' ⊔ W)
  set 𝔡 : FractionalIdeal (nonZeroDivisors (NumberField.RingOfIntegers ↥K)) ↥K := Work.SSGRoute.tFreePart (K := ↥K) T' a
    with h𝔡
  set x : IdeleClassGroup ↥K := IdeleClassGroup.mk ↥K (NK.NUV2.RouteB.RayModulus.fracIdele 𝔡)
    with hx
  have hgoal : x ∈ U' ⊔ W := by
    refine (Work.SSGRoute.charSeparation_exponent_p (p := p) U' W
      (le_sup_right : Work.SSGRoute.EscapeCoreLib.pPowSubgroup p (IdeleClassGroup ↥K) ≤ U')
      x).mpr ?_
    intro χ hχ
    have hpPow_le : Work.SSGRoute.EscapeCoreLib.pPowSubgroup p (IdeleClassGroup ↥K) ≤ U' :=
      le_sup_right
    -- ## 1. the Kummer element `b` of the locally constant datum `g`
    let z : (Ω ≃ₐ[k] Ω) → ZMod p := fun σ => if h : σ ∈ K.fixingSubgroup then g σ else 0
    have hz : ∀ x' ∈ K.fixingSubgroup, ∀ y' ∈ K.fixingSubgroup, z (x' * y') = z x' + z y' := by
      intro x' hx' y' hy'
      have hxy : x' * y' ∈ K.fixingSubgroup := K.fixingSubgroup.mul_mem hx' hy'
      simp only [z, dif_pos hx', dif_pos hy', dif_pos hxy]
      exact hg x' hx' y' hy'
    have hzc : SSGRoute.IsLocConstOn K.fixingSubgroup z := by
      obtain ⟨V, hVopen, hV⟩ := hgc
      refine ⟨V, hVopen, ?_⟩
      intro x' hx' u hu huH
      have hxu : x' * u ∈ K.fixingSubgroup := K.fixingSubgroup.mul_mem hx' huH
      simp only [z, dif_pos hx', dif_pos hxu]
      exact hV x' hx' u hu huH
    obtain ⟨b, hb⟩ := Work.SSGRoute.ZDataMup.KummerSurjectivity.kummerCharZMod_surjective_levelK
      p k Ω K ζ hζ z hz hzc
    -- ## 2. the idèle decomposition of the principal idèle `(a)ᵥ`
    set P : Idele ↥K := ∏ 𝔭 ∈ T', NK.HassePrinciple.onePlace (Place.ofFinite 𝔭)
        (NK.CFTLib.IdeleHasse.localImageAt (K := ↥K) (Place.ofFinite 𝔭) a) with hP
    set Qb : Idele ↥K := ∏ 𝔭 ∈ T', NK.HassePrinciple.onePlace (Place.ofFinite 𝔭)
        (NK.CFTLib.IdeleHasse.localImageAt (K := ↥K) (Place.ofFinite 𝔭) b) with hQb
    obtain ⟨u, hu, hdec⟩ :=
      Work.GrunwaldEscapeCore.L1Korth.idele_decomposition_tFreePart p ↥K T' a
    rw [← hP] at hdec
    have hχu : χ (IdeleClassGroup.mk ↥K u) = 1 := by
      refine hχ _ (Subgroup.mem_sup_left (Subgroup.mem_sup_left ?_))
      exact Subgroup.mem_map.mpr ⟨u, Subgroup.mem_sup_right hu, rfl⟩
    have hprinEq : IdeleClassGroup.mk ↥K (Idele.principalIdele ↥K a) = 1 := by
      rw [← MonoidHom.mem_ker, Work.SSGRoute.ker_mk_eq_principal]
      exact Idele.mem_principalSubgroup.mpr ⟨a, rfl⟩
    have hχprin : χ (IdeleClassGroup.mk ↥K (Idele.principalIdele ↥K a)) = 1 := by
      rw [hprinEq, map_one]
    suffices hχP : χ (IdeleClassGroup.mk ↥K P) = 1 by
      have hdecC : IdeleClassGroup.mk ↥K (Idele.principalIdele ↥K a) =
          IdeleClassGroup.mk ↥K P * x * IdeleClassGroup.mk ↥K u := by
        rw [hdec, map_mul, map_mul, ← h𝔡, ← hx]
      have hcong := congrArg χ hdecC
      simp only [map_mul] at hcong
      rw [hχprin, hχu, mul_one, hχP, one_mul] at hcong
      exact hcong.symm
    -- ## 3. `χ` kills the product over `T'`: each factor is the corresponding `b`-factor
    have hterm : ∀ 𝔭 ∈ T',
        χ (IdeleClassGroup.mk ↥K (NK.HassePrinciple.onePlace (Place.ofFinite 𝔭)
          (NK.CFTLib.IdeleHasse.localImageAt (K := ↥K) (Place.ofFinite 𝔭) a))) =
        χ (IdeleClassGroup.mk ↥K (NK.HassePrinciple.onePlace (Place.ofFinite 𝔭)
          (NK.CFTLib.IdeleHasse.localImageAt (K := ↥K) (Place.ofFinite 𝔭) b))) := by
      intro 𝔭 h𝔭
      obtain ⟨A, hA, hA𝔭⟩ := hT'above 𝔭 h𝔭
      rcases horth A hA with hzero | hsplit
      · -- `h A ≡ 0` on `D_A`: the two local images differ by a `p`-th power
        have hchar : ∀ τ : Ω ≃ₐ[↥K] Ω, τ ∈ SSGRoute.decomp ↥K A →
            Work.SSGRoute.kummerCharZMod (K := ↥K) (Ω := Ω) p (ζ := ζ) hζ a τ =
              Work.SSGRoute.kummerCharZMod (K := ↥K) (Ω := Ω) p (ζ := ζ) hζ b τ := by
          intro τ hτ
          let σu : ↥(K.fixingSubgroup) := (IntermediateField.fixingSubgroupEquiv K).symm τ
          have hfix : (IntermediateField.fixingSubgroupEquiv K) σu = τ :=
            (IntermediateField.fixingSubgroupEquiv K).apply_symm_apply τ
          have hσdec : (σu : Ω ≃ₐ[k] Ω) ∈ SSGRoute.decomp k A :=
            (Work.SSGRoute.fixingSubgroupEquiv_mem_decomp k Ω K A (σu : Ω ≃ₐ[k] Ω) σu.2).mp
              (by rw [hfix]; exact hτ)
          have hσinf : (σu : Ω ≃ₐ[k] Ω) ∈ SSGRoute.decomp k A ⊓ K.fixingSubgroup :=
            ⟨hσdec, σu.2⟩
          have haa := ha A hA ⟨(σu : Ω ≃ₐ[k] Ω), hσinf⟩
          have hto : Work.SSGRoute.gesLocalToGalK K ⟨(σu : Ω ≃ₐ[k] Ω), hσinf⟩ = τ := by
            change (IntermediateField.fixingSubgroupEquiv K)
              (⟨(σu : Ω ≃ₐ[k] Ω), (Subgroup.mem_inf.mp hσinf).2⟩ : ↥(K.fixingSubgroup)) = τ
            rw [show (⟨(σu : Ω ≃ₐ[k] Ω), (Subgroup.mem_inf.mp hσinf).2⟩
                : ↥(K.fixingSubgroup)) = σu from rfl, hfix]
          rw [hto] at haa
          have hzσ : z (σu : Ω ≃ₐ[k] Ω) = g (σu : Ω ≃ₐ[k] Ω) := dif_pos σu.2
          have hbσ := hb (σu : Ω ≃ₐ[k] Ω) σu.2
          rw [show (⟨(σu : Ω ≃ₐ[k] Ω), σu.2⟩ : ↥(K.fixingSubgroup)) = σu from rfl, hfix] at hbσ
          rw [hzσ] at hbσ
          rw [← haa, hzero (σu : Ω ≃ₐ[k] Ω) hσinf, add_zero]
          exact hbσ
        obtain ⟨ww, hw⟩ :=
          Work.GrunwaldEscapeCore.exists_pow_eq_localImageAt_of_kummerChar_eq_on_decomp p K ζ hζ A
            (hTfin A hA) 𝔭 hA𝔭 a b hchar
        have hone : NK.HassePrinciple.onePlace (Place.ofFinite 𝔭)
            (NK.CFTLib.IdeleHasse.localImageAt (K := ↥K) (Place.ofFinite 𝔭) a) =
            NK.HassePrinciple.onePlace (Place.ofFinite 𝔭)
              (NK.CFTLib.IdeleHasse.localImageAt (K := ↥K) (Place.ofFinite 𝔭) b) *
            (NK.HassePrinciple.onePlace (Place.ofFinite 𝔭) ww) ^ p := by
          rw [hw, NK.CFTLib.IdeleHasse.onePlace_mul, Work.GrunwaldEscapeCore.onePlace_pow_local]
        rw [hone, map_mul, map_pow, map_mul, map_pow]
        have hpow : (χ (IdeleClassGroup.mk ↥K
            (NK.HassePrinciple.onePlace (Place.ofFinite 𝔭) ww))) ^ p = 1 := by
          rw [← map_pow]
          exact hχ _ (Subgroup.mem_sup_left
            (hpPow_le (Work.SSGRoute.EscapeCoreLib.pow_mem_pPowSubgroup _)))
        rw [hpow, mul_one]
      · -- `A` splits completely in `N`: both terms are norm classes
        have hA' : IdeleClassGroup.mk ↥K (NK.HassePrinciple.onePlace (Place.ofFinite 𝔭)
            (NK.CFTLib.IdeleHasse.localImageAt (K := ↥K) (Place.ofFinite 𝔭) a)) ∈ W :=
          Work.GrunwaldEscapeCore.mk_onePlace_mem_normClassSubgroup_of_isSplitIn p K A (hTfin A hA)
            𝔭 hA𝔭 N N' hNN' hsplit a
        have hB' : IdeleClassGroup.mk ↥K (NK.HassePrinciple.onePlace (Place.ofFinite 𝔭)
            (NK.CFTLib.IdeleHasse.localImageAt (K := ↥K) (Place.ofFinite 𝔭) b)) ∈ W :=
          Work.GrunwaldEscapeCore.mk_onePlace_mem_normClassSubgroup_of_isSplitIn p K A (hTfin A hA)
            𝔭 hA𝔭 N N' hNN' hsplit b
        rw [hχ _ (Subgroup.mem_sup_right hA'), hχ _ (Subgroup.mem_sup_right hB')]
    -- ## 4. the product of the `b`-terms over `T'` is `1`, by the reciprocity product formula
    have hbprod : (∏ 𝔭 ∈ T', χ (IdeleClassGroup.mk ↥K
        (NK.HassePrinciple.onePlace (Place.ofFinite 𝔭)
          (NK.CFTLib.IdeleHasse.localImageAt (K := ↥K) (Place.ofFinite 𝔭) b)))) = 1 := by
      let Ψ : Idele ↥K →* Multiplicative (ZMod p) := χ.comp (IdeleClassGroup.mk ↥K)
      have hprin : ∀ y : (↥K)ˣ, Ψ (Idele.principalIdele ↥K y) = 1 := by
        intro y
        show χ (IdeleClassGroup.mk ↥K (Idele.principalIdele ↥K y)) = 1
        rw [show IdeleClassGroup.mk ↥K (Idele.principalIdele ↥K y) = 1 from by
          rw [← MonoidHom.mem_ker, Work.SSGRoute.ker_mk_eq_principal]
          exact Idele.mem_principalSubgroup.mpr ⟨y, rfl⟩]
        exact map_one χ
      have hnorm : ∀ y : Idele ↥M, Ψ (Idele.normIdeleHom ↥K ↥M y) = 1 := by
        intro y
        refine hχ _ (Subgroup.mem_sup_left ?_)
        rw [show U' = Idele.normClassSubgroup ↥K ↥M from hMnorm.symm]
        exact Subgroup.mem_map.mpr ⟨_, Idele.mem_normImage.mpr ⟨y, fun v => rfl⟩, rfl⟩
      have hs : ∀ v : Place ↥K, v ∉ T'.image Place.ofFinite →
          Ψ (NK.HassePrinciple.onePlace v
            (NK.CFTLib.IdeleHasse.localImageAt (K := ↥K) v b)) = 1 := by
        intro v hv
        rcases v with w | 𝔮
        · -- an archimedean place: `↥K` is totally complex, so the local norm subgroup is everything
          have hp3 : 3 ≤ p := by
            have h2 : 2 ≤ p := (Fact.out : p.Prime).two_le
            omega
          have htc : NumberField.IsTotallyComplex ↥K :=
            NK.CFTLib.IdeleHasse.isTotallyComplex_of_primitiveRoot hp3 ζ hζ
          have htop : NK.CFTLib.IdeleHasse.localNormSubgroup (K := ↥K) (L := ↥M)
              (Place.ofInfinite w) = ⊤ :=
            NK.CFTLib.HR.localNormSubgroup_ofInfinite_eq_top_of_isTotallyComplex
              (M := ↥K) (E := ↥M) htc w
          have hmem : NK.CFTLib.IdeleHasse.localImageAt (K := ↥K) (Place.ofInfinite w) b ∈
              NK.CFTLib.IdeleHasse.localNormSubgroup (K := ↥K) (L := ↥M)
                (Place.ofInfinite w) := by
            rw [htop]
            exact Subgroup.mem_top _
          have hnormimg : NK.HassePrinciple.onePlace (Place.ofInfinite w)
              (NK.CFTLib.IdeleHasse.localImageAt (K := ↥K) (Place.ofInfinite w) b) ∈
              Idele.normImage ↥K ↥M :=
            (NK.CFTLib.IdeleHasse.onePlace_ofInfinite_mem_normImage_iff (K := ↥K) (L := ↥M)
              w _).mpr hmem
          obtain ⟨y, hy⟩ := Idele.mem_normImage.mp hnormimg
          rw [show NK.HassePrinciple.onePlace (Place.ofInfinite w)
                (NK.CFTLib.IdeleHasse.localImageAt (K := ↥K) (Place.ofInfinite w) b) =
              Idele.normIdeleHom ↥K ↥M y from Idele.ext (fun v => hy v)]
          exact hnorm y
        · -- a finite place `𝔮 ∉ T'`
          have h𝔮T : 𝔮 ∉ T' := fun h => hv (Finset.mem_image_of_mem _ h)
          obtain ⟨B, hBcomap⟩ := Commons.RingTheory.Valuation.exists_valuationSubring_comap_eq
            (K := ↥K) (L := Ω) (IsDedekindDomain.HeightOneSpectrum.valuationSubringAtPrime ↥K 𝔮)
          have hBK : SSGRoute.IsFinPlace ↥K B := by
            rw [SSGRoute.IsFinPlace, hBcomap]
            exact Commons.RingTheory.Valuation.valuationSubringAtPrime_ne_top 𝔮
          have hBfin : SSGRoute.IsFinPlace k B :=
            (Work.SSGRoute.isFinPlace_baseChange k Ω K B).mp hBK
          -- `p` is a unit at `B`, since the places over `p` lie in the classes of `T`
          have hpval : ¬ B.valuation (p : Ω) < 1 := by
            intro hlt
            obtain ⟨A, hA, hconj⟩ := hTcov B hBfin (Or.inl hlt)
            obtain ⟨τ, hτ, hτA⟩ := hconj
            obtain ⟨𝔭, h𝔭T', h𝔭A⟩ := hTbelow A hA
            have hB𝔭 : B.comap (algebraMap ↥K Ω) =
                IsDedekindDomain.HeightOneSpectrum.valuationSubringAtPrime ↥K 𝔭 := by
              rw [← hτA, ← h𝔭A]
              have hcoe : ⇑((IntermediateField.fixingSubgroupEquiv K) ⟨τ, hτ⟩) = ⇑τ :=
                funext fun _ => rfl
              rw [(gesSmulEqOfCoeEq K hcoe A).symm]
              exact Commons.NumberTheory.NumberField.Valuation.comap_smul_algebraMap A _
            rw [hBcomap] at hB𝔭
            exact h𝔮T (Commons.RingTheory.Valuation.valuationSubringAtPrime_injective (K := ↥K)
              hB𝔭 ▸ h𝔭T')
          by_cases hsplit : SSGRoute.IsSplitIn k N B
          · have hmem : IdeleClassGroup.mk ↥K (NK.HassePrinciple.onePlace (Place.ofFinite 𝔮)
                (NK.CFTLib.IdeleHasse.localImageAt (K := ↥K) (Place.ofFinite 𝔮) b)) ∈ W :=
              Work.GrunwaldEscapeCore.mk_onePlace_mem_normClassSubgroup_of_isSplitIn p K B hBfin
                𝔮 hBcomap N N' hNN' hsplit b
            exact hχ _ (Subgroup.mem_sup_right hmem)
          · -- the inertia criterion: `p ∣ v_𝔮(b)`, so the term lies in `U'`
            have hnotT : ∀ A ∈ T, ¬ Work.SSGRoute.gesKConj K A B := by
              intro A hA hconj
              obtain ⟨τ, hτ, hτA⟩ := hconj
              obtain ⟨𝔭, h𝔭T', h𝔭A⟩ := hTbelow A hA
              have hB𝔭 : B.comap (algebraMap ↥K Ω) =
                  IsDedekindDomain.HeightOneSpectrum.valuationSubringAtPrime ↥K 𝔭 := by
                rw [← hτA, ← h𝔭A]
                have hcoe : ⇑((IntermediateField.fixingSubgroupEquiv K) ⟨τ, hτ⟩) = ⇑τ :=
                  funext fun _ => rfl
                rw [(gesSmulEqOfCoeEq K hcoe A).symm]
                exact Commons.NumberTheory.NumberField.Valuation.comap_smul_algebraMap A _
              rw [hBcomap] at hB𝔭
              exact h𝔮T (Commons.RingTheory.Valuation.valuationSubringAtPrime_injective (K := ↥K)
                hB𝔭 ▸ h𝔭T')
            have hb0 : ∀ σ : Ω ≃ₐ[↥K] Ω, SSGRoute.IsInertia (k := ↥K) B σ →
                Work.SSGRoute.kummerCharZMod (K := ↥K) (Ω := Ω) p (ζ := ζ) hζ b σ = 0 := by
              intro σ hσ
              let τu : ↥(K.fixingSubgroup) := (IntermediateField.fixingSubgroupEquiv K).symm σ
              have hfix : (IntermediateField.fixingSubgroupEquiv K) τu = σ :=
                (IntermediateField.fixingSubgroupEquiv K).apply_symm_apply σ
              have hτI : SSGRoute.IsInertia k B (τu : Ω ≃ₐ[k] Ω) :=
                (Work.SSGRoute.isInertia_baseChange k Ω K B (τu : Ω ≃ₐ[k] Ω) τu.2).mp
                  (by rw [hfix]; exact hσ)
              have hg0 : g (τu : Ω ≃ₐ[k] Ω) = 0 := hgram B hBfin hnotT hsplit _ τu.2 hτI
              have hbτ := hb (τu : Ω ≃ₐ[k] Ω) τu.2
              rw [show (⟨(τu : Ω ≃ₐ[k] Ω), τu.2⟩ : ↥(K.fixingSubgroup)) = τu from rfl, hfix]
                at hbτ
              rw [show z (τu : Ω ≃ₐ[k] Ω) = g (τu : Ω ≃ₐ[k] Ω) from dif_pos τu.2] at hbτ
              rw [← hbτ, hg0]
            have hmem : IdeleClassGroup.mk ↥K (NK.HassePrinciple.onePlace (Place.ofFinite 𝔮)
                (NK.CFTLib.IdeleHasse.localImageAt (K := ↥K) (Place.ofFinite 𝔮) b)) ∈ U' :=
              Work.GrunwaldEscapeCore.onePlace_mem_gesU_of_kummerChar_eq_zero_on_inertia p ζ hζ T'
                B hBK 𝔮 hBcomap h𝔮T hpval b hb0
            exact hχ _ (Subgroup.mem_sup_left hmem)
      have hmain :=
        Work.GrunwaldEscapeCore.prod_localFactor_eq_one_of_comm (p := p) (K := ↥K) (L := ↥M)
          Ψ hprin hnorm b (T'.image Place.ofFinite) hs
      rwa [Finset.prod_image (f := fun v : Place ↥K => Ψ (NK.HassePrinciple.onePlace v
            (NK.CFTLib.IdeleHasse.localImageAt (K := ↥K) v b)))
          (s := T') (g := Place.ofFinite)
          (fun x _ y _ hxy => Place.ofFinite_inj.mp hxy)] at hmain
    rw [hP, map_prod, map_prod]
    rw [show (∏ 𝔭 ∈ T', χ (IdeleClassGroup.mk ↥K (NK.HassePrinciple.onePlace (Place.ofFinite 𝔭)
          (NK.CFTLib.IdeleHasse.localImageAt (K := ↥K) (Place.ofFinite 𝔭) a)))) =
        ∏ 𝔭 ∈ T', χ (IdeleClassGroup.mk ↥K (NK.HassePrinciple.onePlace (Place.ofFinite 𝔭)
          (NK.CFTLib.IdeleHasse.localImageAt (K := ↥K) (Place.ofFinite 𝔭) b))) from
      Finset.prod_congr rfl (fun 𝔭 h𝔭 => hterm 𝔭 h𝔭)]
    exact hbprod
  rw [hMnorm]
  show x ∈ U' ⊔ W
  exact hgoal

end Work.SSGRoute.GrunwaldEscapeCore
