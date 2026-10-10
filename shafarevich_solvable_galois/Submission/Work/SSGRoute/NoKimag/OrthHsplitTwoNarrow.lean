import Mathlib.FieldTheory.KrullTopology
import Mathlib.Order.CompletePartialOrder
import Mathlib.RingTheory.Henselian
import Mathlib.Algebra.Field.ZMod
import Mathlib.FieldTheory.Galois.GaloisClosure
import Mathlib.RingTheory.DedekindDomain.AdicValuation
import Mathlib.RingTheory.Flat.TorsionFree
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.NumberTheory.NumberField.InfinitePlace.Basic
import Submission.Work.H9Narrow.orthogonality_narrow_L2K
import Submission.Work.SSGRoute.NoKimag.HeartLocalSumNarrow
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace Work.SSGRoute.NoKimag

open scoped Pointwise IntermediateField
open NumberField IsDedekindDomain
open NK.GlobalCFT

set_option linter.style.haveILetI false
set_option maxHeartbeats 1600000

/-! The `p = 2` two-field narrow orthogonality (see `ACTION_p2_twoFieldRealisation.md` §3). -/

theorem OrthHsplitTwoNarrow (k Ω : Type) [Field k] [NumberField k] [Field Ω]
    [Algebra k Ω] [IsAlgClosure k Ω] [IsAlgClosed Ω]
    (K : IntermediateField k Ω) [FiniteDimensional k K] [IsGalois k K]
    (ζ : ↥K) (hζ : IsPrimitiveRoot ζ 2)
    (L₁ L₂ : IntermediateField k Ω) [FiniteDimensional k L₁] [IsGalois k L₁]
    [FiniteDimensional k L₂] [IsGalois k L₂] (hKL₁ : K ≤ L₁) (hKL₂ : K ≤ L₂)
    (T : Finset (ValuationSubring Ω)) (hTfin : ∀ A ∈ T, SSGRoute.IsFinPlace k A)
    (hTdisj : ∀ A ∈ T, ∀ B ∈ T, Work.SSGRoute.gesKConj K A B → A = B)
    (hTcov : ∀ B : ValuationSubring Ω, SSGRoute.IsFinPlace k B →
      (B.valuation (2 : Ω) < 1 ∨
        (∃ σ ∈ K.fixingSubgroup, SSGRoute.IsInertia k B σ ∧ σ ∉ L₁.fixingSubgroup) ∨
        (∃ σ ∈ K.fixingSubgroup, SSGRoute.IsInertia k B σ ∧ σ ∉ L₂.fixingSubgroup)) →
      ∃ A ∈ T, Work.SSGRoute.gesKConj K A B)
    (g : (Ω ≃ₐ[k] Ω) → ZMod 2)
    (hg : ∀ x ∈ K.fixingSubgroup, ∀ y ∈ K.fixingSubgroup, g (x * y) = g x + g y)
    (hgc : SSGRoute.IsLocConstOn K.fixingSubgroup g)
    (hgram : ∀ B : ValuationSubring Ω, SSGRoute.IsFinPlace k B →
      (∀ A ∈ T, ¬ Work.SSGRoute.gesKConj K A B) → ¬ SSGRoute.IsSplitIn k L₁ B →
      ∀ σ ∈ K.fixingSubgroup, SSGRoute.IsInertia k B σ → g σ = 0)
    (hginf : ∀ c ∈ K.fixingSubgroup, c ^ 2 = 1 → g c = 0)
    (h : ValuationSubring Ω → (Ω ≃ₐ[k] Ω) → ZMod 2)
    (hh : ∀ A ∈ T, ∀ x ∈ SSGRoute.decomp k A ⊓ K.fixingSubgroup,
      ∀ y ∈ SSGRoute.decomp k A ⊓ K.fixingSubgroup, h A (x * y) = h A x + h A y)
    (hhc : ∀ A ∈ T, ∃ U : Subgroup (Ω ≃ₐ[k] Ω), IsOpen (U : Set (Ω ≃ₐ[k] Ω)) ∧
      ∀ x ∈ U, x ∈ SSGRoute.decomp k A ⊓ K.fixingSubgroup → h A x = 0)
    (horth₁ : ∀ A ∈ T,
      (∀ σ ∈ SSGRoute.decomp k A ⊓ K.fixingSubgroup, h A σ = 0) ∨
      (∀ χ : (Ω ≃ₐ[k] Ω) → ZMod 2,
        (∀ x ∈ K.fixingSubgroup, ∀ y ∈ K.fixingSubgroup, χ (x * y) = χ x + χ y) →
        (∀ σ ∈ L₁.fixingSubgroup, χ σ = 0) →
        ∀ σ ∈ SSGRoute.decomp k A ⊓ K.fixingSubgroup, χ σ = 0) ∨
      ((∀ σ ∈ K.fixingSubgroup, SSGRoute.IsInertia k A σ → h A σ = 0) ∧
        ∀ χ : (Ω ≃ₐ[k] Ω) → ZMod 2,
          (∀ x ∈ K.fixingSubgroup, ∀ y ∈ K.fixingSubgroup, χ (x * y) = χ x + χ y) →
          (∀ σ ∈ L₁.fixingSubgroup, χ σ = 0) →
          ∀ σ ∈ K.fixingSubgroup, SSGRoute.IsInertia k A σ → χ σ = 0))
    (horth₂ : ∀ A ∈ T,
      (∀ σ ∈ SSGRoute.decomp k A ⊓ K.fixingSubgroup, g σ + h A σ = 0) ∨
      (∀ χ : (Ω ≃ₐ[k] Ω) → ZMod 2,
        (∀ x ∈ K.fixingSubgroup, ∀ y ∈ K.fixingSubgroup, χ (x * y) = χ x + χ y) →
        (∀ σ ∈ L₂.fixingSubgroup, χ σ = 0) →
        ∀ σ ∈ SSGRoute.decomp k A ⊓ K.fixingSubgroup, χ σ = 0) ∨
      ((∀ σ ∈ K.fixingSubgroup, SSGRoute.IsInertia k A σ → g σ + h A σ = 0) ∧
        ∀ χ : (Ω ≃ₐ[k] Ω) → ZMod 2,
          (∀ x ∈ K.fixingSubgroup, ∀ y ∈ K.fixingSubgroup, χ (x * y) = χ x + χ y) →
          (∀ σ ∈ L₂.fixingSubgroup, χ σ = 0) →
          ∀ σ ∈ K.fixingSubgroup, SSGRoute.IsInertia k A σ → χ σ = 0))
    (hsplit : ∀ χ : (Ω ≃ₐ[k] Ω) → ZMod 2,
      (∀ x ∈ K.fixingSubgroup, ∀ y ∈ K.fixingSubgroup, χ (x * y) = χ x + χ y) →
      (∀ σ ∈ (L₁ ⊔ L₂ : IntermediateField k Ω).fixingSubgroup, χ σ = 0) →
      ∃ χ₁ χ₂ : (Ω ≃ₐ[k] Ω) → ZMod 2,
        (∀ x ∈ K.fixingSubgroup, ∀ y ∈ K.fixingSubgroup, χ₁ (x * y) = χ₁ x + χ₁ y) ∧
        (∀ σ ∈ L₁.fixingSubgroup, χ₁ σ = 0) ∧
        (∀ x ∈ K.fixingSubgroup, ∀ y ∈ K.fixingSubgroup, χ₂ (x * y) = χ₂ x + χ₂ y) ∧
        (∀ σ ∈ L₂.fixingSubgroup, χ₂ σ = 0) ∧
        ∀ σ ∈ K.fixingSubgroup, χ σ = χ₁ σ + χ₂ σ)
    (T' : Finset (NK.Chebotarev.PrimeIdeal ↥K))
    (hTbelow : ∀ A ∈ T, ∃ 𝔭 ∈ T', A.comap (algebraMap ↥K Ω) =
      IsDedekindDomain.HeightOneSpectrum.valuationSubringAtPrime ↥K 𝔭)
    (hT'above : ∀ 𝔭 ∈ T', ∃ A ∈ T, A.comap (algebraMap ↥K Ω) =
      IsDedekindDomain.HeightOneSpectrum.valuationSubringAtPrime ↥K 𝔭)
    (N : IntermediateField ↥K Ω) [FiniteDimensional ↥K N] [IsGalois ↥K N] [NumberField ↥N]
    (hN : (N : Set Ω) = ((L₁ ⊔ L₂ : IntermediateField k Ω) : Set Ω))
    (a : (↥K)ˣ)
    (ha : ∀ A ∈ T, ∀ σ : ↥(SSGRoute.decomp k A ⊓ K.fixingSubgroup),
      g (σ : Ω ≃ₐ[k] Ω) + h A (σ : Ω ≃ₐ[k] Ω) =
        Work.SSGRoute.kummerCharZMod (K := ↥K) (Ω := Ω) 2 (ζ := ζ) hζ a
          (Work.SSGRoute.gesLocalToGalK K σ))
    (hapos : ∀ (c : Ω ≃ₐ[k] Ω) (hc : c ∈ K.fixingSubgroup), c ^ 2 = 1 →
      Work.SSGRoute.kummerCharZMod (K := ↥K) (Ω := Ω) 2 (ζ := ζ) hζ a
        (Work.SSGRoute.gesGalKOfFixing K c hc) = 0) :
    NK.GlobalCFT.IdeleClassGroup.mk ↥K
        (NK.NUV2.RouteB.RayModulus.fracIdele (Work.SSGRoute.tFreePart T' a)) ∈
      (Work.SSGRoute.H9.narrowGesU ↥K 2 T' ⊔
          Work.SSGRoute.EscapeCoreLib.pPowSubgroup 2 (NK.GlobalCFT.IdeleClassGroup ↥K))
        ⊔ NK.GlobalCFT.Idele.normClassSubgroup ↥K ↥N
  := by
  classical
  haveI hNumK : NumberField ↥K := NumberField.of_module_finite k ↥K
  -- ## the level field `F` inside `N`, with `N_{F/↥K}C_F` the subgroup of the statement
  obtain ⟨F, hFfd, hFgal, hFnf, hFcomm, hFleN, hFnorm⟩ :=
    Work.H9Narrow.narrow_levelField 2 k Ω K L₁ L₂ hKL₁ hKL₂ T' N hN
  haveI hFfdI : FiniteDimensional ↥K F := hFfd
  haveI hFgalI : IsGalois ↥K F := hFgal
  haveI hFnfI : NumberField ↥F := hFnf
  haveI hFcommI : IsMulCommutative (↥F ≃ₐ[↥K] ↥F) := hFcomm
  -- ## the idèlic Artin map of `F/↥K`, with all the clauses
  obtain ⟨Φ, hΦker, hΦloc, hΦfrob, hΦprod, hΦdecomp, hΦinertia⟩ :=
    Work.SSGRoute.N2v2.exists_artinMap_fullClauses (K := K) F
  -- ## `F/↥K` is unramified outside `T'`
  have hFunr : ∀ 𝔮 : NK.Chebotarev.PrimeIdeal ↥K, 𝔮 ∉ T' →
      NK.HeckeL.IsUnramifiedIn (K := ↥K) (L := ↥F) 𝔮 := by
    intro 𝔮 h𝔮
    refine Work.H9Narrow.isUnramifiedIn_of_narrowUnitIdeles_le_normClassSubgroup 2 k Ω K T' F ?_ 𝔮 h𝔮
    rw [hFnorm]
    exact le_trans le_sup_left le_sup_left
  -- ## `Gal(F/↥K)` has exponent `p`
  have hexpF : ∀ σ : ↥F ≃ₐ[↥K] ↥F, σ ^ 2 = 1 := by
    refine Work.SSGRoute.N2v2.galExp_of_pPowSubgroup_le 2 K F ?_ Φ hΦker hΦfrob
    rw [hFnorm]
    exact le_trans le_sup_right le_sup_left
  -- ## characters of `Gal(F/↥K)` separate the points, so it suffices to kill the Artin symbol
  have hPhi : Φ (NK.NUV2.RouteB.RayModulus.fracIdele (Work.SSGRoute.tFreePart (K := ↥K) T' a))
      = 1 := by
    have h1 : Φ (NK.NUV2.RouteB.RayModulus.fracIdele (Work.SSGRoute.tFreePart (K := ↥K) T' a))
        ∈ (⊥ : Subgroup (↥F ≃ₐ[↥K] ↥F)) := by
      letI hFcg : CommGroup (↥F ≃ₐ[↥K] ↥F) := { mul_comm := fun a b => mul_comm' a b }
      refine Work.SSGRoute.N2v2.mem_of_forall_monoidHom_eq_one (p := 2) hexpF ⊥ ?_
      intro χ _
      -- realise the character as a Kummer character at level `F`
      obtain ⟨c, hcF, hχ⟩ :=
        Work.SSGRoute.N2v2.kummer_level_realisation 2 k Ω K ζ hζ F χ
      have harchA : ∀ w : NumberField.InfinitePlace ↥K,
          NK.CFTLib.IdeleHasse.localImageAt (K := ↥K) (NK.GlobalCFT.Place.ofInfinite w) a ∈
            NK.CFTLib.IdeleHasse.localNormSubgroup (K := ↥K) (L := ↥F)
              (NK.GlobalCFT.Place.ofInfinite w) :=
        Work.SSGRoute.ZDataTwo.hapos_arch_localNorm_aux k Ω K ζ hζ a F hapos
      refine Work.SSGRoute.ZDataTwo.artinFixes_localFactors_two_aux K ζ hζ F c hcF χ hχ
        a T' hFunr Φ ?_ ?_ ?_ ?_
      · -- the principal idèles are killed (kernel clause)
        intro x
        rw [← MonoidHom.mem_ker, hΦker]
        exact Subgroup.mem_sup_right (Idele.mem_principalSubgroup.mpr ⟨x, rfl⟩)
      · -- the norm idèles are killed (kernel clause)
        intro y
        rw [← MonoidHom.mem_ker, hΦker]
        exact Subgroup.mem_sup_left (Idele.mem_normImage.mpr ⟨y, fun v => rfl⟩)
      · -- the archimedean components of `a` are local norms
        exact harchA
      · -- ## the per-place product: the heart of the orthogonality
        classical
        -- ### the Kummer element representing the datum `g`
        obtain ⟨bg, hbg⟩ :=
          Work.SSGRoute.ZDataMup.KummerSurjectivity.kummerCharZMod_surjective_levelK
            2 k Ω K ζ hζ g hg hgc
        -- ### the split of `c` along `hsplit` (at the `k`-level `L₁ ⊔ L₂`)
        have hKE : K ≤ (L₁ ⊔ L₂ : IntermediateField k Ω) := hKL₁.trans le_sup_left
        have hcbC : NK.LocalAnabelian.kummerField (K' := Ω) 2 c ≤
            Work.SSGRoute.EscapeCoreLib.baseChange K (L₁ ⊔ L₂) hKE := by
          rw [Work.SSGRoute.EscapeCoreLib.le_baseChange_iff]
          intro x hx
          exact hN ▸ hFleN (hcF hx)
        have hEfix : (L₁ ⊔ L₂ : IntermediateField k Ω).fixingSubgroup ≤
            (L₁.fixingSubgroup ⊓ L₂.fixingSubgroup) ⊔
              (Work.SSGRoute.N2v2.commPow ↥(K.fixingSubgroup) 2).map
                K.fixingSubgroup.subtype := by
          rw [IntermediateField.fixingSubgroup_sup]
          exact le_sup_left
        obtain ⟨c₁, c₂, hc₁L', hc₂L', hsplitc⟩ :=
          Work.SSGRoute.N2v2.kummerSplit_of_hsplit 2 k Ω K ζ hζ L₁ L₂ hKL₁ hKL₂ hsplit
            (L₁ ⊔ L₂) hKE subset_rfl hEfix c hcbC
        have hc₁L : NK.LocalAnabelian.kummerField (K' := Ω) 2 c₁ ≤
            Work.SSGRoute.EscapeCoreLib.baseChange K L₁ hKL₁ := le_trans hc₁L' inf_le_right
        have hc₂L : NK.LocalAnabelian.kummerField (K' := Ω) 2 c₂ ≤
            Work.SSGRoute.EscapeCoreLib.baseChange K L₂ hKL₂ := le_trans hc₂L' inf_le_right
        -- ### the instances of the four Kummer fields
        have hFa := Work.SSGRoute.N2v2.kummerField_data 2 K ζ hζ a
        haveI hFa_fd : FiniteDimensional ↥K
            (NK.LocalAnabelian.kummerField (K' := Ω) 2 a) := hFa.1
        haveI hFa_gal : IsGalois ↥K (NK.LocalAnabelian.kummerField (K' := Ω) 2 a) := hFa.2.1
        haveI hFa_nf : NumberField ↥(NK.LocalAnabelian.kummerField (K' := Ω) 2 a) := hFa.2.2.1
        haveI hFa_cm : IsMulCommutative (↥(NK.LocalAnabelian.kummerField (K' := Ω) 2 a) ≃ₐ[↥K]
          ↥(NK.LocalAnabelian.kummerField (K' := Ω) 2 a)) := hFa.2.2.2.1
        have hFa_exp : ∀ σ : ↥(NK.LocalAnabelian.kummerField (K' := Ω) 2 a) ≃ₐ[↥K]
            ↥(NK.LocalAnabelian.kummerField (K' := Ω) 2 a), σ ^ 2 = 1 := hFa.2.2.2.2
        have hFc₁ := Work.SSGRoute.N2v2.kummerField_data 2 K ζ hζ c₁
        haveI hFc₁_fd : FiniteDimensional ↥K
            (NK.LocalAnabelian.kummerField (K' := Ω) 2 c₁) := hFc₁.1
        haveI hFc₁_gal : IsGalois ↥K (NK.LocalAnabelian.kummerField (K' := Ω) 2 c₁) := hFc₁.2.1
        haveI hFc₁_nf : NumberField ↥(NK.LocalAnabelian.kummerField (K' := Ω) 2 c₁) :=
          hFc₁.2.2.1
        haveI hFc₁_cm : IsMulCommutative (↥(NK.LocalAnabelian.kummerField (K' := Ω) 2 c₁) ≃ₐ[↥K]
          ↥(NK.LocalAnabelian.kummerField (K' := Ω) 2 c₁)) := hFc₁.2.2.2.1
        have hFc₁_exp : ∀ σ : ↥(NK.LocalAnabelian.kummerField (K' := Ω) 2 c₁) ≃ₐ[↥K]
            ↥(NK.LocalAnabelian.kummerField (K' := Ω) 2 c₁), σ ^ 2 = 1 := hFc₁.2.2.2.2
        have hFc₂ := Work.SSGRoute.N2v2.kummerField_data 2 K ζ hζ c₂
        haveI hFc₂_fd : FiniteDimensional ↥K
            (NK.LocalAnabelian.kummerField (K' := Ω) 2 c₂) := hFc₂.1
        haveI hFc₂_gal : IsGalois ↥K (NK.LocalAnabelian.kummerField (K' := Ω) 2 c₂) := hFc₂.2.1
        haveI hFc₂_nf : NumberField ↥(NK.LocalAnabelian.kummerField (K' := Ω) 2 c₂) :=
          hFc₂.2.2.1
        haveI hFc₂_cm : IsMulCommutative (↥(NK.LocalAnabelian.kummerField (K' := Ω) 2 c₂) ≃ₐ[↥K]
          ↥(NK.LocalAnabelian.kummerField (K' := Ω) 2 c₂)) := hFc₂.2.2.2.1
        have hFc₂_exp : ∀ σ : ↥(NK.LocalAnabelian.kummerField (K' := Ω) 2 c₂) ≃ₐ[↥K]
            ↥(NK.LocalAnabelian.kummerField (K' := Ω) 2 c₂), σ ^ 2 = 1 := hFc₂.2.2.2.2
        have hFbg := Work.SSGRoute.N2v2.kummerField_data 2 K ζ hζ bg
        haveI hFbg_fd : FiniteDimensional ↥K
            (NK.LocalAnabelian.kummerField (K' := Ω) 2 bg) := hFbg.1
        haveI hFbg_gal : IsGalois ↥K (NK.LocalAnabelian.kummerField (K' := Ω) 2 bg) := hFbg.2.1
        haveI hFbg_nf : NumberField ↥(NK.LocalAnabelian.kummerField (K' := Ω) 2 bg) :=
          hFbg.2.2.1
        haveI hFbg_cm : IsMulCommutative (↥(NK.LocalAnabelian.kummerField (K' := Ω) 2 bg) ≃ₐ[↥K]
          ↥(NK.LocalAnabelian.kummerField (K' := Ω) 2 bg)) := hFbg.2.2.2.1
        have hFbg_exp : ∀ σ : ↥(NK.LocalAnabelian.kummerField (K' := Ω) 2 bg) ≃ₐ[↥K]
            ↥(NK.LocalAnabelian.kummerField (K' := Ω) 2 bg), σ ^ 2 = 1 := hFbg.2.2.2.2
        -- ### the big level `E = F ⊔ ↥K⟮a^{1/p}⟯ ⊔ ↥K⟮c₁^{1/p}⟯ ⊔ ↥K⟮c₂^{1/p}⟯ ⊔ ↥K⟮bg^{1/p}⟯`
        obtain ⟨E, hEfd, hEgal, hEcomm, hEnf, hFE, hFaE, hc₁E, hc₂E, hbgE, hexpE⟩ :=
          Work.SSGRoute.N2v2.sup5_abelian_expP (k := k) (Ω := Ω) 2 K F
            (NK.LocalAnabelian.kummerField (K' := Ω) 2 a)
            (NK.LocalAnabelian.kummerField (K' := Ω) 2 c₁)
            (NK.LocalAnabelian.kummerField (K' := Ω) 2 c₂)
            (NK.LocalAnabelian.kummerField (K' := Ω) 2 bg)
            hexpF hFa_exp hFc₁_exp hFc₂_exp hFbg_exp
        haveI hEfdI : FiniteDimensional ↥K E := hEfd
        haveI hEgalI : IsGalois ↥K E := hEgal
        haveI hEcommI : IsMulCommutative (↥E ≃ₐ[↥K] ↥E) := hEcomm
        haveI hEnfI : NumberField ↥E := hEnf
        haveI hEft : Fintype (↥E ≃ₐ[↥K] ↥E) := AlgEquiv.fintype ↥K ↥E
        -- ### the Artin map of `E` and its local factors
        obtain ⟨Φ_E, hΦkerE, hΦlocE, hΦfrobE, hΦprodE, hΦdecompE, hΦinertiaE⟩ :=
          Work.SSGRoute.N2v2.exists_artinMap_fullClauses (K := K) E
        let θ : (v : NK.GlobalCFT.Place ↥K) →
            (NK.GlobalCFT.Place.localField ↥K v)ˣ →* (↥E ≃ₐ[↥K] ↥E) :=
          fun v => Φ_E.comp (NK.CFTLib.IdeleHasse.onePlaceHom (K := ↥K) v)
        have hθker : ∀ v : NK.GlobalCFT.Place ↥K,
            (θ v).ker = NK.CFTLib.IdeleHasse.localNormSubgroup (K := ↥K) (L := ↥E) v := by
          intro v
          ext u
          rw [MonoidHom.mem_ker]
          exact hΦlocE v u
        have hθprod : ∀ (x : (↥K)ˣ) (s : Finset (NK.GlobalCFT.Place ↥K)),
            (∀ v, v ∉ s → θ v (NK.CFTLib.IdeleHasse.localImageAt (K := ↥K) v x) = 1) →
            NK.CFTLib.IdeleHasse.cprod (fun a b => mul_comm' a b) s
              (fun v => θ v (NK.CFTLib.IdeleHasse.localImageAt (K := ↥K) v x)) = 1 :=
          fun x s hs => hΦprodE x s (fun v hv => hs v hv)
        have hbginf : ∀ (c' : Ω ≃ₐ[k] Ω) (hc' : c' ∈ K.fixingSubgroup), c' ^ 2 = 1 →
            Work.SSGRoute.kummerCharZMod (K := ↥K) (Ω := Ω) 2 (ζ := ζ) hζ bg
              (Work.SSGRoute.gesGalKOfFixing K c' hc') = 0 := by
          intro c' hc' hc'2
          have h1 : Work.SSGRoute.kummerCharZMod (K := ↥K) (Ω := Ω) 2 (ζ := ζ) hζ bg
              (Work.SSGRoute.gesGalKOfFixing K c' hc') = g c' := (hbg c' hc').symm
          rw [h1]
          exact hginf c' hc' hc'2
        have harchbg : ∀ w : NumberField.InfinitePlace ↥K,
            NK.CFTLib.IdeleHasse.localImageAt (K := ↥K) (NK.GlobalCFT.Place.ofInfinite w) bg ∈
              NK.CFTLib.IdeleHasse.localNormSubgroup (K := ↥K) (L := ↥E)
                (NK.GlobalCFT.Place.ofInfinite w) :=
          Work.SSGRoute.ZDataTwo.arch_localNorm_of_involution_condition k Ω K ζ hζ bg E hbginf
        have hlift : ∀ (A : ValuationSubring Ω) (_hA : _root_.SSGRoute.IsFinPlace k A)
            (𝔭 : NK.Chebotarev.PrimeIdeal ↥K),
            A.comap (algebraMap ↥K Ω) =
              IsDedekindDomain.HeightOneSpectrum.valuationSubringAtPrime ↥K 𝔭 →
            ∀ x : (↥K)ˣ, ∃ σ : Ω ≃ₐ[↥K] Ω, σ ∈ _root_.SSGRoute.decomp (k := ↥K) A ∧
              AlgEquiv.restrictNormalHom (F := ↥K) (K₁ := Ω) E σ =
                θ (NK.GlobalCFT.Place.ofFinite 𝔭)
                  (NK.CFTLib.IdeleHasse.localImageAt (K := ↥K)
                    (NK.GlobalCFT.Place.ofFinite 𝔭) x) :=
          fun A hA 𝔭 h𝔭 x => hΦdecompE A hA 𝔭 h𝔭 x
        have hunith : ∀ (A : ValuationSubring Ω) (_hA : _root_.SSGRoute.IsFinPlace k A)
            (𝔭 : NK.Chebotarev.PrimeIdeal ↥K),
            A.comap (algebraMap ↥K Ω) =
              IsDedekindDomain.HeightOneSpectrum.valuationSubringAtPrime ↥K 𝔭 →
            ∀ u : (NK.GlobalCFT.Place.localField ↥K (NK.GlobalCFT.Place.ofFinite 𝔭))ˣ,
              u ∈ NK.GlobalCFT.Place.localUnits ↥K (NK.GlobalCFT.Place.ofFinite 𝔭) →
              ∃ σ : Ω ≃ₐ[↥K] Ω, _root_.SSGRoute.IsInertia k A (σ.restrictScalars k) ∧
                AlgEquiv.restrictNormalHom (F := ↥K) (K₁ := Ω) E σ =
                  θ (NK.GlobalCFT.Place.ofFinite 𝔭) u :=
          fun A hA 𝔭 h𝔭 u hu => hΦinertiaE A hA 𝔭 h𝔭 u hu
        -- ### the twisted diagonal (the `p = 2` correction included)
        have hdiagLift : ∀ 𝔭 ∈ T', ∃ σ₀ : Ω ≃ₐ[↥K] Ω,
            ∀ (y : (↥K)ˣ), NK.LocalAnabelian.kummerField (K' := Ω) 2 y ≤ E →
            ∀ τ : Ω ≃ₐ[↥K] Ω,
              AlgEquiv.restrictNormalHom (F := ↥K) (K₁ := Ω) E τ =
                θ (NK.GlobalCFT.Place.ofFinite 𝔭)
                  (NK.CFTLib.IdeleHasse.localImageAt (K := ↥K)
                    (NK.GlobalCFT.Place.ofFinite 𝔭) y) →
              Work.SSGRoute.kummerCharZMod (K := ↥K) (Ω := Ω) 2 (ζ := ζ) hζ y τ =
                Work.SSGRoute.kummerCharZMod (K := ↥K) (Ω := Ω) 2 (ζ := ζ) hζ y σ₀ :=
          fun 𝔭 _h𝔭 => Work.SSGRoute.N2v2.hdiag_E 2 K ζ hζ E Φ_E 𝔭
            (fun c hcE => Work.SSGRoute.N2v2.hdata_of_kummerField_le 2 K ζ hζ E Φ_E
              hΦkerE hΦfrobE 𝔭 c hcE)
        -- ### `g` vanishes on the fixing subgroup of `E`
        have hgE : ∀ σ : Ω ≃ₐ[↥K] Ω, σ ∈ E.fixingSubgroup → g (σ.restrictScalars k) = 0 := by
          intro σ hσE
          have hσK : σ.restrictScalars k ∈ K.fixingSubgroup := by
            rw [IntermediateField.mem_fixingSubgroup_iff]
            intro x hx
            exact σ.commutes ⟨x, hx⟩
          rw [hbg (σ.restrictScalars k) hσK,
            Work.SSGRoute.N2v2.fixingSubgroupEquiv_restrictScalars K σ]
          exact Work.SSGRoute.N2v2.kummerCharZMod_eq_zero_of_kummerField_le 2 k Ω K ζ hζ bg E
            hbgE σ hσE
        -- ### the character at level `E` and the level-`F` character of `c`
        have hcE : NK.LocalAnabelian.kummerField (K' := Ω) 2 c ≤ E := hcF.trans hFE
        obtain ⟨χE, hχE⟩ :=
          Work.SSGRoute.N2v2.exists_kummerChar_level 2 k Ω K ζ hζ E c hcE
        -- ### the heart
        have hsum := Work.SSGRoute.N2v2.HeartLocalSumNarrow k Ω K ζ hζ L₁ L₂
          hKL₁ hKL₂ T hTfin T' hTbelow hT'above
          (fun B hB h => hTcov B hB h) g hg hgc hginf
          (fun B hB h1 h2 σ hσ hI => hgram B hB (fun A hA => by
            rintro ⟨τ, hτ, hτA⟩
            exact h1 A hA τ hτ hτA) h2 σ hσ hI)
          h hh horth₁ horth₂ a ha E hexpE θ hθker hθprod hlift hunith
          hdiagLift hgE hFaE c hcE c₁ c₂ hc₁E hc₂E hc₁L hc₂L hsplitc χE hχE
        -- ### reading the heart back at the level `F`
        have hsumF : ∑ 𝔭 ∈ T',
            (χ (Φ (NK.HassePrinciple.onePlace (NK.GlobalCFT.Place.ofFinite 𝔭)
              (NK.CFTLib.IdeleHasse.localImageAt (K := ↥K)
                (NK.GlobalCFT.Place.ofFinite 𝔭) a)))).toAdd = 0 := by
          rw [← hsum]
          refine Finset.sum_congr rfl (fun 𝔭 h𝔭 => ?_)
          obtain ⟨A, hAT, hAcomap⟩ := hT'above 𝔭 h𝔭
          obtain ⟨σ, _hσdec, hσeq⟩ := hΦdecompE A (hTfin A hAT) 𝔭 hAcomap a
          have h1 : (χE (θ (NK.GlobalCFT.Place.ofFinite 𝔭)
              (NK.CFTLib.IdeleHasse.localImageAt (K := ↥K)
                (NK.GlobalCFT.Place.ofFinite 𝔭) a))).toAdd =
              Work.SSGRoute.kummerCharZMod (K := ↥K) (Ω := Ω) 2 (ζ := ζ) hζ c σ := by
            have hθeq : θ (NK.GlobalCFT.Place.ofFinite 𝔭)
                (NK.CFTLib.IdeleHasse.localImageAt (K := ↥K)
                  (NK.GlobalCFT.Place.ofFinite 𝔭) a) =
                Φ_E (NK.HassePrinciple.onePlace (NK.GlobalCFT.Place.ofFinite 𝔭)
                  (NK.CFTLib.IdeleHasse.localImageAt (K := ↥K)
                    (NK.GlobalCFT.Place.ofFinite 𝔭) a)) := rfl
            rw [hθeq, ← hσeq, hχE σ]
            rfl
          have h2 : (χ (Φ (NK.HassePrinciple.onePlace (NK.GlobalCFT.Place.ofFinite 𝔭)
              (NK.CFTLib.IdeleHasse.localImageAt (K := ↥K)
                (NK.GlobalCFT.Place.ofFinite 𝔭) a)))).toAdd =
              Work.SSGRoute.kummerCharZMod (K := ↥K) (Ω := Ω) 2 (ζ := ζ) hζ c σ := by
            have htrans := Work.SSGRoute.N2v2.restrictNormalHom_artinMap_eq_of_le 2 K F E hFE
              Φ hΦker hΦfrob Φ_E hΦkerE hΦfrobE σ
              (NK.HassePrinciple.onePlace (NK.GlobalCFT.Place.ofFinite 𝔭)
                (NK.CFTLib.IdeleHasse.localImageAt (K := ↥K)
                  (NK.GlobalCFT.Place.ofFinite 𝔭) a)) hσeq
            rw [← htrans, hχ σ]
            rfl
          rw [h1, h2]
        have hinj : Function.Injective
            (Multiplicative.toAdd : Multiplicative (ZMod 2) → ZMod 2) := fun _ _ h => h
        refine hinj ?_
        rw [Work.SSGRoute.GrunwaldEscapeCore.toAdd_prod_eq_sum 2 T', hsumF]
        rfl
    simpa using h1
  -- ## the Artin symbol of `𝔡` is a norm idèle class
  have hmem : NK.NUV2.RouteB.RayModulus.fracIdele (Work.SSGRoute.tFreePart (K := ↥K) T' a)
      ∈ Φ.ker := MonoidHom.mem_ker.mpr hPhi
  rw [hΦker] at hmem
  have hmap : (Idele.normImage ↥K ↥F ⊔ Idele.principalSubgroup ↥K).map
        (IdeleClassGroup.mk ↥K) = Idele.normClassSubgroup ↥K ↥F := by
    rw [Subgroup.map_sup]
    have h1 : (Idele.principalSubgroup ↥K).map (IdeleClassGroup.mk ↥K) = ⊥ := by
      rw [Subgroup.map_eq_bot_iff, Work.SSGRoute.ker_mk_eq_principal]
    rw [h1, sup_bot_eq]
    rfl
  have hmk : IdeleClassGroup.mk ↥K
      (NK.NUV2.RouteB.RayModulus.fracIdele (Work.SSGRoute.tFreePart (K := ↥K) T' a))
      ∈ Idele.normClassSubgroup ↥K ↥F := by
    rw [← hmap]
    exact Subgroup.mem_map.mpr ⟨_, hmem, rfl⟩
  rw [← hFnorm]
  exact hmk



end Work.SSGRoute.NoKimag
