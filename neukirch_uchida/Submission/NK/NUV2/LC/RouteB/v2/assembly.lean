import Mathlib
import Submission.NK.NUV2.LC.RouteB.level_kills_aux
import Submission.NK.NUV2.LC.RouteB.kummerMap_locUnits
import Submission.NK.NUV2.LC.RouteB.muLift
import Submission.NK.NUV2.LC.RouteB.unitsLift_kummerLevel
import Submission.NK.NUV2.LC.RouteB.locUnits_ofInfinite_eq_zero
import Submission.NK.NUV2.LC.RouteB.isComplex_of_isPrimitiveRoot_odd
import Submission.NK.NUV2.LC.RouteB.exists_level_fixingSubgroup_le
import Submission.NK.NUV2.LC.RouteB.liesOver_placeOf_v2
import Submission.NK.NUV2.LC.RouteB.RouteBDeps
import Submission.NK.HasseTwist.Obstruction
import Submission.NK.NUV2.LC.units_finite_support
import Submission.NK.GlobalCFTdeep.HasseNormTheorem
import Submission.NK.NUV2.ABHN.h2Twist_muColim_equiv
import Submission.NK.HassePrinciple.MuColimit
import Submission.NK.HassePrinciple.kummerLevel_naturality
import Submission.NK.HassePrinciple.muLevelMap_comp
import Submission.NK.HassePrinciple.kummerColim_injective
import Submission.NeukirchUchida.Local.PlaceFromValuation
import Submission.NK.LocalCFT.Brauer.Transport

set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 1000000
set_option linter.unusedSectionVars false

namespace NK.NUV2.LC.RouteB.v2

open Filter
open CategoryTheory
open scoped NumberField Topology

variable {K K' : Type} [Field K] [NumberField K] [Field K'] [Algebra K K'] [IsSepClosure K K']

/-- **A number field containing a primitive `p`-th root of unity for odd `p` has no real place**,
for the base field of an enlarged level. -/
theorem isComplex_levelBase (p : ℕ) (hp : p.Prime) (hp2 : p ≠ 2) (ζ : K')
    (hζ : IsPrimitiveRoot ζ p) (V : Subgroup Gal(K'/K)) (hV : V ≤ rootFix (K := K) ζ)
    (L : FiniteGaloisIntermediateField K K') (hfix : L.fixingSubgroup ≤ V) :
    ∀ v : NumberField.InfinitePlace ↥(levelBase (K := K) V L), v.IsComplex := by
  have hζfix : ζ ∈ IntermediateField.fixedField V :=
    ((IntermediateField.le_iff_le (K := IntermediateField.adjoin K ({ζ} : Set K')) (H := V)).mpr
        hV) (IntermediateField.mem_adjoin_simple_self K ζ)
  have hζL : ζ ∈ (L : IntermediateField K K') := by
    have h1 : IntermediateField.fixedField V ≤ IntermediateField.fixedField (L.fixingSubgroup) :=
      IntermediateField.fixedField_le hfix
    rw [InfiniteGalois.fixedField_fixingSubgroup (k := K) (K := K') L] at h1
    exact h1 hζfix
  have hζbase_mem : (⟨ζ, hζL⟩ : ↥L.toIntermediateField) ∈
      (levelBase (K := K) V L : IntermediateField K ↥L.toIntermediateField) := by
    rw [IntermediateField.mem_fixedField_iff]
    intro σ hσ
    obtain ⟨v, hv, rfl⟩ := hσ
    apply Subtype.ext
    have hcomm := AlgEquiv.restrictNormal_commutes (E := (L : IntermediateField K K')) v
      (⟨ζ, hζL⟩ : ↥L.toIntermediateField)
    have hvz : v ζ = ζ := by
      have h := hζfix
      rw [IntermediateField.mem_fixedField_iff] at h
      exact h v hv
    have hval : v (algebraMap ↥L.toIntermediateField K' (⟨ζ, hζL⟩ : ↥L.toIntermediateField)) = ζ := by
      rw [IntermediateField.algebraMap_apply]
      simpa using hvz
    calc ((NK.HassePrinciple.levelRestrict L v) (⟨ζ, hζL⟩ : ↥L.toIntermediateField) : K')
        = algebraMap ↥L.toIntermediateField K'
            (NK.HassePrinciple.levelRestrict L v (⟨ζ, hζL⟩ : ↥L.toIntermediateField)) :=
          (IntermediateField.algebraMap_apply _ _).symm
      _ = v (algebraMap ↥L.toIntermediateField K' (⟨ζ, hζL⟩ : ↥L.toIntermediateField)) := hcomm
      _ = ζ := hval
  have hζbase : IsPrimitiveRoot
      (⟨⟨ζ, hζL⟩, hζbase_mem⟩ : ↥(levelBase (K := K) V L)) p := by
    have hinjL : Function.Injective (algebraMap ↥L.toIntermediateField K') := by
      intro a b hab
      exact Subtype.ext hab
    have hinjB : Function.Injective
        (algebraMap ↥(levelBase (K := K) V L) ↥L.toIntermediateField) := by
      intro a b hab
      exact Subtype.ext hab
    have h2 : IsPrimitiveRoot (⟨ζ, hζL⟩ : ↥L.toIntermediateField) p := by
      refine IsPrimitiveRoot.of_map_of_injective (f := algebraMap ↥L.toIntermediateField K')
        ?_ hinjL
      simpa [IntermediateField.algebraMap_apply] using hζ
    refine IsPrimitiveRoot.of_map_of_injective
      (f := algebraMap ↥(levelBase (K := K) V L) ↥L.toIntermediateField) ?_ hinjB
    simpa [IntermediateField.algebraMap_apply] using h2
  exact isComplex_of_isPrimitiveRoot_odd p hp hp2 _ hζbase

/-- **Every place of a finite Galois level `M` lies over some place of a smaller level `L`**,
for the `LiesOver` relation along the canonical inclusion `↥L → ↥M`. -/
theorem exists_place_liesOver (L M : FiniteGaloisIntermediateField K K') (hLM : L ≤ M) :
    ∀ w' : NK.GlobalCFT.Place ↥(M : IntermediateField K K'),
      ∃ w : NK.GlobalCFT.Place ↥(L : IntermediateField K K'),
        @NK.GlobalCFT.Place.LiesOver ↥(L : IntermediateField K K') _ _ ↥(M : IntermediateField K K') _ _
          ((IntermediateField.inclusion hLM).toAlgebra) w' w := by
  letI : Algebra ↥(L : IntermediateField K K') ↥(M : IntermediateField K K') :=
    (IntermediateField.inclusion hLM).toAlgebra
  intro w'
  cases w' with
  | inl v' =>
    exact ⟨NK.GlobalCFT.Place.ofInfinite (v'.comap (algebraMap ↥(L : IntermediateField K K')
        ↥(M : IntermediateField K K'))),
      NK.GlobalCFT.Place.liesOver_ofInfinite (by exact ⟨rfl⟩)⟩
  | inr q' =>
    refine ⟨NK.GlobalCFT.Place.ofFinite
      ⟨q'.asIdeal.under (𝓞 ↥(L : IntermediateField K K')), inferInstance,
        Ideal.under_ne_bot _ q'.ne_bot⟩, ?_⟩
    exact NK.GlobalCFT.Place.liesOver_ofFinite (Ideal.LiesOver.mk rfl)

/-- The three interface pieces, packaged (propagation, fibre, dictionary). -/
structure Pieces (p : ℕ) (ζ : K') (V : Subgroup Gal(K'/K)) where
  /-- propagation of the `locL`-vanishing under inflation -/
  prop : ∀ (L M : FiniteGaloisIntermediateField K K') (hLM : L ≤ M) (hF : L.fixingSubgroup ≤ V)
      (b : NK.HassePrinciple.UnitsLevelH2 (K := K) (K' := K') V L)
      {w : NK.GlobalCFT.Place ↥(L : IntermediateField K K')}
      {w' : NK.GlobalCFT.Place ↥(M : IntermediateField K K')},
      @NK.GlobalCFT.Place.LiesOver ↥(L : IntermediateField K K') _ _ ↥(M : IntermediateField K K') _ _
        ((IntermediateField.inclusion hLM).toAlgebra) w' w →
      NK.NUV2.LC.RouteB.locL (K := K) (K' := K') V L w b = 0 →
      NK.NUV2.LC.RouteB.locL (K := K) (K' := K') V M w'
        ((NK.HassePrinciple.unitsLevelMap (K := K) (K' := K') V hLM).hom b) = 0
  /-- fibre independence over a common place of the smaller level -/
  fib : ∀ (L M : FiniteGaloisIntermediateField K K') (hLM : L ≤ M) (hF : L.fixingSubgroup ≤ V)
      (b : NK.HassePrinciple.UnitsLevelH2 (K := K) (K' := K') V L)
      {w : NK.GlobalCFT.Place ↥(L : IntermediateField K K')}
      {w₁ w₂ : NK.GlobalCFT.Place ↥(M : IntermediateField K K')},
      @NK.GlobalCFT.Place.LiesOver ↥(L : IntermediateField K K') _ _ ↥(M : IntermediateField K K') _ _
        ((IntermediateField.inclusion hLM).toAlgebra) w₁ w →
      @NK.GlobalCFT.Place.LiesOver ↥(L : IntermediateField K K') _ _ ↥(M : IntermediateField K K') _ _
        ((IntermediateField.inclusion hLM).toAlgebra) w₂ w →
      (NK.NUV2.LC.RouteB.locL (K := K) (K' := K') V M w₁
          ((NK.HassePrinciple.unitsLevelMap (K := K) (K' := K') V hLM).hom b) = 0 ↔
        NK.NUV2.LC.RouteB.locL (K := K) (K' := K') V M w₂
          ((NK.HassePrinciple.unitsLevelMap (K := K) (K' := K') V hLM).hom b) = 0)
  /-- the fine-local-level versus `locL` dictionary -/
  dict : ∀ (L : FiniteGaloisIntermediateField K K') (hF : L.fixingSubgroup ≤ V)
      (c : NK.HassePrinciple.MuLevelH2 (K := K) (K' := K') p V L)
      (A : NK.BrauerTwist.OverFinitePrime K K')
      (q : IsDedekindDomain.HeightOneSpectrum
        (NumberField.RingOfIntegers ↥(L : IntermediateField K K'))),
      A.1.comap (algebraMap ↥(L : IntermediateField K K') K') =
        IsDedekindDomain.HeightOneSpectrum.valuationSubringAtPrime
          ↥(L : IntermediateField K K') q →
      NK.BrauerTwist.locLevel p V A.1 L
        ((NK.NUV2.ABHN.levelCompare (K := K) (K' := K') p V L) c) = 0 →
      NK.NUV2.LC.RouteB.locL (K := K) (K' := K') V L (NK.GlobalCFT.Place.ofFinite q)
        ((NK.HassePrinciple.kummerLevel (K := K) (K' := K') p V L).hom c) = 0

/-- **The `μ_p`-form of the Hasse principle at an open level**, assembled from the three interface
pieces (`Pieces`): for an odd prime `p`, `ζ` a primitive `p`-th root of unity in `K'`, `V ≤ Gal(K'/K)`
open with `V ≤ rootFix ζ`, a level `L` and a class `c : MuLevelH2 p V L` whose colimit
localisations vanish at every place of `K'` over a finite prime of `K`, there is `M ≥ L` with
`muLevelMap p V (L ≤ M) c = 0`. -/
theorem muLevel_dies_of_loc_eq_zero_assembly (p : ℕ) (hp : p.Prime) (hp2 : p ≠ 2)
    (ζ : K') (hζ : IsPrimitiveRoot ζ p)
    (V : Subgroup Gal(K'/K)) (hV : NK.NUV2.LC.RouteB.IsMuOpen (K := K) (K' := K') ζ V)
    (P : Pieces (K := K) (K' := K') p ζ V)
    (L : FiniteGaloisIntermediateField K K')
    (c : NK.HassePrinciple.MuLevelH2 (K := K) (K' := K') p V L)
    (h : ∀ A : NK.BrauerTwist.OverFinitePrime K K',
      NK.BrauerTwist.H2Twist.loc p V
        (NK.BrauerTwist.H2Twist.ofLevel p V L
          (NK.NUV2.ABHN.levelCompare p V L c)) A = 0) :
    ∃ (M : FiniteGaloisIntermediateField K K') (hLM : L ≤ M),
      NK.HassePrinciple.muLevelMap (K := K) (K' := K') p V
        ((FiniteGaloisIntermediateField.le_iff L M).mp hLM) c = 0 := by
  classical
  -- ===== Step 0: enlarge `L` to a level containing `F' = K'^V`
  have hVcl : IsClosed (V : Set Gal(K'/K)) := Subgroup.isClosed_of_isOpen V hV.1
  have hVnhds : (V : Set Gal(K'/K)) ∈ 𝓝 1 := IsOpen.mem_nhds hV.1 V.one_mem
  obtain ⟨E, hEfin, hEsub⟩ := (krullTopology_mem_nhds_one_iff K K' (V : Set Gal(K'/K))).mp hVnhds
  haveI : FiniteDimensional K ↥E := hEfin
  have hfixed_le : IntermediateField.fixedField V ≤ E := by
    rw [← InfiniteGalois.fixedField_fixingSubgroup (k := K) (K := K') E]
    exact IntermediateField.fixedField_le hEsub
  have hfin : FiniteDimensional K ↥(IntermediateField.fixedField V) :=
    FiniteDimensional.of_injective (IntermediateField.inclusion hfixed_le).toLinearMap
      (IntermediateField.inclusion hfixed_le).injective
  obtain ⟨L₁, hLL₁, hfixL₁⟩ :=
    NK.NUV2.LC.RouteB.exists_level_fixingSubgroup_le (K := K) (K' := K') V L hVcl hfin
  letI instLL₁ : Algebra ↥(L : IntermediateField K K') ↥(L₁ : IntermediateField K K') :=
    (IntermediateField.inclusion hLL₁).toAlgebra
  -- ===== Step 1: transfer the class
  have hLL₁' : (L : IntermediateField K K') ≤ (L₁ : IntermediateField K K') := hLL₁
  set c₁ : NK.HassePrinciple.MuLevelH2 (K := K) (K' := K') p V L₁ :=
    (NK.HassePrinciple.muLevelMap (K := K) (K' := K') p V hLL₁').hom c with hc₁
  have h₁ : ∀ A : NK.BrauerTwist.OverFinitePrime K K',
      NK.BrauerTwist.H2Twist.loc p V
        (NK.BrauerTwist.H2Twist.ofLevel p V L₁
          (NK.NUV2.ABHN.levelCompare p V L₁ c₁)) A = 0 := by
    intro A
    have hnat : NK.NUV2.ABHN.levelCompare p V L₁ c₁ =
        NK.BrauerTwist.levelMap p V hLL₁' (NK.NUV2.ABHN.levelCompare p V L c) :=
      NK.NUV2.ABHN.levelCompare_nat (K := K) (K' := K') p V hLL₁' c
    have heq : NK.BrauerTwist.H2Twist.ofLevel p V L₁
        (NK.NUV2.ABHN.levelCompare p V L₁ c₁) =
        NK.BrauerTwist.H2Twist.ofLevel p V L
          (NK.NUV2.ABHN.levelCompare p V L c) := by
      rw [hnat]
      exact NK.BrauerTwist.H2Twist.ofLevel_levelMap (K := K) (K' := K') p V hLL₁' _
    rw [heq]
    exact h A
  -- ===== Step 2: the units class at level `L₁` and its bad places
  set b₁ : NK.HassePrinciple.UnitsLevelH2 (K := K) (K' := K') V L₁ :=
    (NK.HassePrinciple.kummerLevel p V L₁).hom c₁ with hb₁
  have hSfin : ({w : NK.GlobalCFT.Place ↥(L₁ : IntermediateField K K') |
      NK.NUV2.LC.RouteB.locL (K := K) (K' := K') V L₁ w b₁ ≠ 0} : Set _).Finite := by
    simpa only [NK.NUV2.LC.RouteB.locL, hb₁] using
      (NK.NUV2.LC.units_finite_support (K := ↥(levelBase (K := K) V L₁))
        (L := ↥(L₁ : IntermediateField K K'))
        ((unitsLift (K := K) (K' := K') V L₁) b₁))
  have hSplace : ∀ w ∈ ({w : NK.GlobalCFT.Place ↥(L₁ : IntermediateField K K') |
      NK.NUV2.LC.RouteB.locL (K := K) (K' := K') V L₁ w b₁ ≠ 0} : Set _),
      ∃ q : IsDedekindDomain.HeightOneSpectrum
          (NumberField.RingOfIntegers ↥(L₁ : IntermediateField K K')),
        w = NK.GlobalCFT.Place.ofFinite q := by
    intro w hw
    cases w with
    | inl v =>
      exact absurd (by
        rw [NK.NUV2.LC.RouteB.locL]
        exact NK.NUV2.LC.RouteB.locUnits_ofInfinite_eq_zero
          (isComplex_levelBase (K := K) (K' := K') p hp hp2 ζ hζ V hV.2 L₁ hfixL₁) v
          ((unitsLift (K := K) (K' := K') V L₁) b₁)) hw
    | inr q => exact ⟨q, rfl⟩
  -- ===== Step 3: for each bad place, an extension and a dying level
  have hchoice : ∀ w : ↥(hSfin.toFinset),
      ∃ (N : FiniteGaloisIntermediateField K K') (hN : L₁ ≤ N)
        (A : NK.BrauerTwist.OverFinitePrime K K')
        (q : IsDedekindDomain.HeightOneSpectrum
          (NumberField.RingOfIntegers ↥(L₁ : IntermediateField K K'))),
        (A.1.comap (algebraMap ↥(L₁ : IntermediateField K K') K') =
          IsDedekindDomain.HeightOneSpectrum.valuationSubringAtPrime
            ↥(L₁ : IntermediateField K K') q) ∧
        (w.1 = NK.GlobalCFT.Place.ofFinite q) ∧
        (NK.BrauerTwist.locLevel p V A.1 N
          (NK.BrauerTwist.levelMap p V hN
            ((NK.NUV2.ABHN.levelCompare p V L₁) c₁))) = 0 := by
    intro w
    obtain ⟨q, hq⟩ := hSplace w.1 (hSfin.mem_toFinset.mp w.2)
    obtain ⟨A, hA⟩ := Commons.RingTheory.Valuation.exists_valuationSubring_comap_eq
      (K := ↥(L₁ : IntermediateField K K')) (L := K')
      (IsDedekindDomain.HeightOneSpectrum.valuationSubringAtPrime
        ↥(L₁ : IntermediateField K K') q)
    have hAne : A.comap (algebraMap K K') ≠ ⊤ := by
      intro htop
      have hAtop : A = ⊤ :=
        Commons.RingTheory.Valuation.ValuationSubring.eq_top_of_comap_algebraMap_eq_top
          A (inferInstance) htop
      rw [hAtop] at hA
      have htop' : (⊤ : ValuationSubring K').comap
          (algebraMap ↥(L₁ : IntermediateField K K') K') = ⊤ := by
        ext x; simp
      exact Commons.RingTheory.Valuation.valuationSubringAtPrime_ne_top
        (K := ↥(L₁ : IntermediateField K K')) q (by rw [← hA, htop'])
    obtain ⟨N, hN, hN0⟩ := (NK.HasseTwist.loc_ofLevel_eq_zero_iff p ⟨A, hAne⟩ L₁
      ((NK.NUV2.ABHN.levelCompare p V L₁) c₁)).mp (h₁ ⟨A, hAne⟩)
    exact ⟨N, hN, ⟨A, hAne⟩, q, hA, hq, by
      rw [NK.BrauerTwist.levelMap_locLevel_apply]
      exact hN0⟩
  choose N hNle A q hprops using hchoice
  -- ===== Step 4: the sup level
  set M : FiniteGaloisIntermediateField K K' :=
    L₁ ⊔ Finset.sup (hSfin.toFinset.attach) (fun w => N w) with hMdef
  letI instL₁M : Algebra ↥(L₁ : IntermediateField K K') ↥(M : IntermediateField K K') :=
    (IntermediateField.inclusion le_sup_left).toAlgebra
  have hL₁M : L₁ ≤ M := le_sup_left
  have hNM : ∀ w : ↥(hSfin.toFinset), N w ≤ M := fun w =>
    le_trans (Finset.le_sup (f := fun w => N w) (Finset.mem_attach _ w)) le_sup_right
  have hvan : ∀ w : ↥(hSfin.toFinset),
      (NK.BrauerTwist.locLevel p V (A w).1 M
        (NK.BrauerTwist.levelMap p V hL₁M
          ((NK.NUV2.ABHN.levelCompare p V L₁) c₁))) = 0 := by
    intro w
    exact NK.NUV2.LC.RouteB.locLevel_eq_zero_of_le p V (A w) L₁
      ((NK.NUV2.ABHN.levelCompare p V L₁) c₁) (hNle w) hL₁M (hNM w) (hprops w).2.2
  have hcrux : ∀ w : ↥(hSfin.toFinset),
      NK.NUV2.LC.RouteB.locL (K := K) (K' := K') V M
        (NK.GlobalCFT.Place.ofFinite (Submission.NeukirchUchida.Local.placeOf
          (NK.HasseTwist.primeUnder (A w)) (A w).1 (NK.HasseTwist.primeUnder_spec (A w))
          (M : IntermediateField K K')))
        ((NK.HassePrinciple.kummerLevel p V M).hom
          ((NK.HassePrinciple.muLevelMap p V hL₁M).hom c₁)) = 0 := by
    intro w
    have hfixM : M.fixingSubgroup ≤ V :=
      le_trans (IntermediateField.fixingSubgroup_le hL₁M) hfixL₁
    refine P.dict M hfixM ((NK.HassePrinciple.muLevelMap p V hL₁M).hom c₁) (A w) _ ?_ ?_
    · exact Submission.NeukirchUchida.Local.comap_eq_valuationSubringAtPrime_placeOf
        (NK.HasseTwist.primeUnder (A w)) (A w).1 (NK.HasseTwist.primeUnder_spec (A w))
        (M : IntermediateField K K')
    · rw [NK.NUV2.ABHN.levelCompare_nat (K := K) (K' := K') p V hL₁M c₁]
      exact hvan w
  have hnatKL : ((NK.HassePrinciple.kummerLevel p V M).hom
        ((NK.HassePrinciple.muLevelMap p V hL₁M).hom c₁)) =
      (NK.HassePrinciple.unitsLevelMap (K := K) (K' := K') V hL₁M).hom b₁ := by
    have hnat := congrArg (fun (f : NK.HassePrinciple.MuLevelH2 (K := K) (K' := K') p V L₁ ⟶
        NK.HassePrinciple.UnitsLevelH2 (K := K) (K' := K') V M) => f.hom c₁)
      (NK.HassePrinciple.kummerLevel_naturality (K := K) (K' := K') p V hL₁M)
    simp only [CategoryTheory.comp_apply] at hnat
    rw [← hnat, hb₁]
  -- ===== Step 5: all `locL`-localisations vanish at level `M`
  have hall : ∀ w' : NK.GlobalCFT.Place ↥(M : IntermediateField K K'),
      NK.NUV2.LC.RouteB.locL (K := K) (K' := K') V M w'
        ((NK.HassePrinciple.kummerLevel p V M).hom
          ((NK.HassePrinciple.muLevelMap p V hL₁M).hom c₁)) = 0 := by
    intro w'
    rw [hnatKL]
    by_cases hbad : ∃ w : ↥(hSfin.toFinset),
        @NK.GlobalCFT.Place.LiesOver ↥(L₁ : IntermediateField K K') _ _ ↥(M : IntermediateField K K') _ _
          ((IntermediateField.inclusion hL₁M).toAlgebra) w' w.1
    · obtain ⟨w, hw⟩ := hbad
      have hlies := NK.NUV2.LC.RouteB.liesOver_placeOf_v2 (K := K) (K' := K') L₁ M hL₁M
        (A w) (q w) (hprops w).1
      rw [(hprops w).2.1] at hw
      exact (P.fib L₁ M hL₁M hfixL₁ b₁ hlies hw).mp (by rw [← hnatKL]; exact hcrux w)
    · obtain ⟨w₀, hw₀⟩ := exists_place_liesOver (K := K) (K' := K') L₁ M hL₁M w'
      have hnotmem : w₀ ∉ ({w : NK.GlobalCFT.Place ↥(L₁ : IntermediateField K K') |
          NK.NUV2.LC.RouteB.locL (K := K) (K' := K') V L₁ w b₁ ≠ 0} : Set _) := by
        intro hmem
        exact hbad ⟨⟨w₀, hSfin.mem_toFinset.mpr hmem⟩, hw₀⟩
      exact P.prop L₁ M hL₁M hfixL₁ b₁ hw₀ (by simpa using hnotmem)
  -- ===== Step 6: the units class vanishes at level `M`
  have hbM : ((NK.HassePrinciple.kummerLevel p V M).hom
      ((NK.HassePrinciple.muLevelMap p V hL₁M).hom c₁)) = 0 :=
    NK.NUV2.LC.RouteB.unitsLevelH2_eq_zero_of_locL_eq_zero V M _ hall
  -- ===== Step 7: the `μ_p` class dies
  obtain ⟨M', hMM', hM'⟩ := NK.HassePrinciple.kummerLevel_kernel_dies p hp V M
    ((NK.HassePrinciple.muLevelMap p V hL₁M).hom c₁) hbM
  have hstep : (NK.HassePrinciple.muLevelMap p V (hL₁M.trans hMM')).hom c₁ = 0 := by
    have hcomp := NK.HassePrinciple.muLevelMap_comp (K := K) (K' := K') p V hL₁M hMM'
    have h2 := congrArg (fun (f : NK.HassePrinciple.MuLevelH2 (K := K) (K' := K') p V L₁ ⟶
        NK.HassePrinciple.MuLevelH2 (K := K) (K' := K') p V M') => f.hom c₁) hcomp
    simp only [CategoryTheory.comp_apply] at h2
    first
      | exact h2.trans hM'
      | exact h2.symm.trans hM'
  have hfinal : (NK.HassePrinciple.muLevelMap p V
      ((FiniteGaloisIntermediateField.le_iff L M').mp (hLL₁.trans (hL₁M.trans hMM')))).hom c = 0 := by
    have hcomp := NK.HassePrinciple.muLevelMap_comp (K := K) (K' := K') p V hLL₁'
      (hL₁M.trans hMM')
    have h2 := congrArg (fun (f : NK.HassePrinciple.MuLevelH2 (K := K) (K' := K') p V L ⟶
        NK.HassePrinciple.MuLevelH2 (K := K) (K' := K') p V M') => f.hom c) hcomp
    simp only [CategoryTheory.comp_apply] at h2
    have h3 : (NK.HassePrinciple.muLevelMap p V (hL₁M.trans hMM')).hom
        ((NK.HassePrinciple.muLevelMap p V hLL₁').hom c) = 0 := by
      rw [← hc₁]
      exact hstep
    first
      | exact h2.trans h3
      | exact h2.symm.trans h3
  exact ⟨M', hLL₁.trans (hL₁M.trans hMM'), hfinal⟩

end NK.NUV2.LC.RouteB.v2

