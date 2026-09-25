import Mathlib
import Submission.NK.NUV2.ABHN.LocalBrauerAux
import Submission.NK.HassePrinciple.MuColimit
import Submission.NK.HassePrinciple.kummerColim_injective
import Submission.NK.HassePrinciple.finite_levelGroup
import Submission.NK.HassePrinciple.unitsLevelMap_comp
import Submission.NK.HassePrinciple.muLevelMap_comp

set_option autoImplicit false
set_option maxHeartbeats 3200000
set_option synthInstance.maxHeartbeats 1600000
set_option linter.unusedSectionVars false
set_option linter.style.haveILetI false

universe u

namespace NK.NUV2.ABHN

open NK.HassePrinciple
open NK.BrauerHasse

variable {K K' : Type u} [Field K] [CharZero K] [Field K'] [Algebra K K'] [IsSepClosure K K']

/-! ## The units level system, in projection form -/

/-- The level objects of the units level system, in the projection form used by the `LevelSystem`
API, carry the `AddCommGroup`-structure of `UnitsLevelH2 V L` (they are definitionally equal, but
type class search does not unfold the `def` `unitsLevelSystem`). -/
noncomputable instance instAddCommGroupUnitsLevelObj (V : Subgroup Gal(K'/K))
    (L : FiniteGaloisIntermediateField K K') :
    AddCommGroup ((unitsLevelSystem V).obj L) :=
  inferInstanceAs (AddCommGroup (UnitsLevelH2 V L))

lemma unitsLevelSystem_map_add (V : Subgroup Gal(K'/K))
    {L L' : FiniteGaloisIntermediateField K K'} (h : L ≤ L')
    (x y : (unitsLevelSystem V).obj L) :
    (unitsLevelSystem V).map h (x + y) =
      (unitsLevelSystem V).map h x + (unitsLevelSystem V).map h y := map_add _ x y

lemma unitsLevelSystem_map_zero (V : Subgroup Gal(K'/K))
    {L L' : FiniteGaloisIntermediateField K K'} (h : L ≤ L') :
    (unitsLevelSystem V).map h (0 : (unitsLevelSystem V).obj L) = 0 := map_zero _

lemma unitsLevelSystem_map_nsmul (V : Subgroup Gal(K'/K))
    {L L' : FiniteGaloisIntermediateField K K'} (h : L ≤ L') (n : ℕ)
    (x : (unitsLevelSystem V).obj L) :
    (unitsLevelSystem V).map h (n • x) = n • (unitsLevelSystem V).map h x := map_nsmul _ n x

lemma unitsLevelSystem_ofLevel_add (V : Subgroup Gal(K'/K))
    (L : FiniteGaloisIntermediateField K K') (a b : (unitsLevelSystem V).obj L) :
    (unitsLevelSystem V).ofLevel L (a + b) =
      (unitsLevelSystem V).ofLevel L a + (unitsLevelSystem V).ofLevel L b :=
  H2Units.ofLevel_add V L a b

lemma unitsLevelSystem_ofLevel_zero (V : Subgroup Gal(K'/K))
    (L : FiniteGaloisIntermediateField K K') :
    (unitsLevelSystem V).ofLevel L (0 : (unitsLevelSystem V).obj L) = 0 := by
  have h := unitsLevelSystem_ofLevel_add V L (0 : (unitsLevelSystem V).obj L) 0
  rw [add_zero] at h
  have h1 : (unitsLevelSystem V).ofLevel L (0 : (unitsLevelSystem V).obj L) + 0 =
      (unitsLevelSystem V).ofLevel L (0 : (unitsLevelSystem V).obj L) +
        (unitsLevelSystem V).ofLevel L (0 : (unitsLevelSystem V).obj L) := by
    rw [add_zero]
    exact h
  exact (add_left_cancel h1).symm

lemma unitsLevelSystem_ofLevel_nsmul (V : Subgroup Gal(K'/K))
    (L : FiniteGaloisIntermediateField K K') (n : ℕ) (a : (unitsLevelSystem V).obj L) :
    (unitsLevelSystem V).ofLevel L (n • a) = n • (unitsLevelSystem V).ofLevel L a := by
  induction n with
  | zero => rw [zero_nsmul, zero_nsmul, unitsLevelSystem_ofLevel_zero]
  | succ k ih => rw [succ_nsmul, succ_nsmul, unitsLevelSystem_ofLevel_add, ih]

/-- **Moving a class of the units colimit that is killed by `p` to a level where its `p`-multiple
vanishes.** -/
theorem exists_level_representative_nsmul_eq_zero (V : Subgroup Gal(K'/K)) (p : ℕ)
    (x : H2Units V) (hx : p • x = 0) :
    ∃ (M : FiniteGaloisIntermediateField K K') (y : UnitsLevelH2 V M),
      H2Units.ofLevel V M y = x ∧ p • y = 0 := by
  obtain ⟨M₀, y₀, hy₀⟩ := (unitsLevelSystem V).ofLevel_surjective x
  have hzero : (unitsLevelSystem V).ofLevel M₀ (p • y₀) =
      (unitsLevelSystem V).ofLevel M₀ (0 : (unitsLevelSystem V).obj M₀) := by
    rw [unitsLevelSystem_ofLevel_nsmul, hy₀, hx, unitsLevelSystem_ofLevel_zero]
  obtain ⟨M, h₁, h₂, he⟩ :=
    ((unitsLevelSystem V).ofLevel_eq_iff (p • y₀) (0 : (unitsLevelSystem V).obj M₀)).mp hzero
  refine ⟨M, (unitsLevelSystem V).map h₁ y₀, ?_, ?_⟩
  · exact ((unitsLevelSystem V).ofLevel_map h₁ y₀).trans hy₀
  · have hmap : (unitsLevelSystem V).map h₁ (p • y₀) = 0 := by
      rw [he]
      exact map_zero _
    have h2 := unitsLevelSystem_map_nsmul V h₁ p y₀
    rw [h2] at hmap
    exact hmap

/-! ## The compatibility of the level restriction with the coefficient inclusion -/

/-- **The restriction action is compatible with the coefficient inclusion.**  For a level
inclusion `M ≤ L`, an element `g` of the level group of `L` and a unit `y` of `M`, the action of
the restriction of `g` to `M` on `y`, transported into `L`, is the action of `g` on the transport
of `y`. -/
lemma unitsLevelRestrictCompat (V : Subgroup Gal(K'/K))
    {M L : FiniteGaloisIntermediateField K K'} (h : M ≤ L)
    (g : LevelGroup V L) (y : (↥M)ˣ) :
    Units.map (IntermediateField.inclusion h).toMonoidHom
        (((levelGroupRestrictHom V M (levelQuotHom (U := V) h g) : ↥M ≃ₐ[K] ↥M)) • y)
      = ((levelGroupRestrictHom V L g : ↥L ≃ₐ[K] ↥L)) •
          (Units.map (IntermediateField.inclusion h).toMonoidHom y) := by
  rw [AlgEquiv.smul_units_def, AlgEquiv.smul_units_def]
  induction g using QuotientGroup.induction_on with
  | H v =>
    rw [levelGroupRestrictHom_mk]
    rw [show (levelQuotHom (U := V) h) (QuotientGroup.mk v) = QuotientGroup.mk v from rfl,
      levelGroupRestrictHom_mk]
    refine Units.ext (Subtype.ext ?_)
    simp only [Units.coe_map, MonoidHom.coe_coe]
    exact (IntermediateField.coe_inclusion h
          (((levelRestrict M (v : Gal(K'/K))) ((y : (↥M)ˣ) : ↥M)))).trans
      ((AlgEquiv.restrictNormalHom_apply (L := (M : IntermediateField K K'))
          (v : Gal(K'/K)) ((y : (↥M)ˣ) : ↥M)).trans
      ((congrArg (fun z : K' => (v : Gal(K'/K)) z)
          (IntermediateField.coe_inclusion h ((y : (↥M)ˣ) : ↥M)).symm).trans
      ((AlgEquiv.restrictNormalHom_apply (L := (L : IntermediateField K K'))
          (v : Gal(K'/K)) ((IntermediateField.inclusion h) ((y : (↥M)ˣ) : ↥M))).symm)))

/-! ## Injectivity of the inclusion `μ_p(L) ↪ Lˣ` -/

lemma muToUnitsLinearMap_injective (p : ℕ) (L : FiniteGaloisIntermediateField K K') :
    Function.Injective (muToUnitsLinearMap.{u, u} p L) := by
  intro x y hxy
  have h2 := congrArg (fun w : Additive (↥L)ˣ => Additive.toMul w) hxy
  rw [muToUnitsLinearMap_apply.{u, u}, muToUnitsLinearMap_apply.{u, u}, toMul_ofMul,
    toMul_ofMul] at h2
  exact Additive.toMul.injective (Subtype.ext h2)

lemma muToUnits_injective (p : ℕ) (V : Subgroup Gal(K'/K))
    (L : FiniteGaloisIntermediateField K K') :
    Function.Injective (muToUnits p V L).hom := by
  intro x y hxy
  refine muToUnitsLinearMap_injective p L ?_
  rw [← muToUnits_apply.{u, u, u} p V L x, ← muToUnits_apply.{u, u, u} p V L y]
  exact hxy

/-! ## A `μ_p`-valued cocycle underlying a units cocycle with `p`-th power `1` -/

/-- **A units-valued `2`-cocycle whose values are `p`-th roots of unity comes from a
`μ_p`-valued `2`-cocycle.** -/
lemma exists_muCocycle_of_unitsCocycle (p : ℕ) (V : Subgroup Gal(K'/K))
    (L : FiniteGaloisIntermediateField K K')
    (z : ↥(groupCohomology.cocycles₂ (unitsLevelRep V L)))
    (hz : ∀ gh : LevelGroup V L × LevelGroup V L,
      ∃ u : (↥L)ˣ, z gh = Additive.ofMul u ∧ u ^ p = 1) :
    ∃ w : ↥(groupCohomology.cocycles₂ (muLevelRep p V L)),
      groupCohomology.mapCocycles₂ (MonoidHom.id (LevelGroup V L)) (muToUnits p V L) w = z := by
  classical
  choose u hu using hz
  have hueq : ∀ gh, z gh = Additive.ofMul (u gh) := fun gh => (hu gh).1
  have hupow : ∀ gh, (u gh) ^ p = 1 := fun gh => (hu gh).2
  let wfun : LevelGroup V L × LevelGroup V L → (muLevelRep p V L).V :=
    fun gh => Additive.ofMul
      (⟨u gh, (mem_rootsOfUnity p (u gh)).mpr (hupow gh)⟩ : rootsOfUnity p ↥L)
  have hval : ∀ gh, (muToUnits p V L).hom (wfun gh) = z gh := by
    intro gh
    rw [show (muToUnits p V L).hom (wfun gh) =
        muToUnitsLinearMap.{u, u} p L (wfun gh) from muToUnits_apply.{u, u, u} p V L (wfun gh)]
    show Additive.ofMul (u gh) = z gh
    rw [hueq gh]
  have hwmem : wfun ∈ groupCohomology.cocycles₂ (muLevelRep p V L) := by
    rw [groupCohomology.mem_cocycles₂_def]
    intro g h j
    refine muToUnits_injective p V L ?_
    rw [map_zero, map_sub, map_add, map_sub]
    rw [show (muToUnits p V L).hom ((muLevelRep p V L).ρ g (wfun (h, j)))
        = (unitsLevelRep V L).ρ g ((muToUnits p V L).hom (wfun (h, j))) from
      Rep.hom_comm_apply (muToUnits p V L) g (wfun (h, j))]
    rw [hval (h, j), hval (g * h, j), hval (g, h * j), hval (g, h)]
    exact (groupCohomology.mem_cocycles₂_def (A := unitsLevelRep V L) ⇑z).mp z.2 g h j
  refine ⟨⟨wfun, hwmem⟩, ?_⟩
  apply Subtype.ext
  funext gh
  obtain ⟨g, h⟩ := gh
  show (muToUnits p V L).hom (wfun (g, h)) = z (g, h)
  exact hval (g, h)

/-! ## The main level-wise construction -/

/-- **Surjectivity of the level-wise Kummer map onto the `p`-torsion, after enlarging the level.**

Let `y` be a class of `H²(LevelGroup ⊤ M, Mˣ)` killed by `p`.  Then there are a finite Galois level
`L ≥ M` and a class `w` of `H²(LevelGroup ⊤ L, μ_p(L))` whose Kummer image is the inflation of
`y` to `L`.

Proof: `y = H2π c` for a `2`-cocycle `c`, and `p • c = d₁₂ β` for a `1`-cochain `β` with values in
`Mˣ` (because `p • y = 0`).  Adjoin `p`-th roots `a_g` of the values `β g` to `M` to obtain `L`;
the cochain `g ↦ a_{π g}` on `LevelGroup ⊤ L` then has `p`-th power of its `d₁₂` equal to that of
`c ∘ π`, so the difference is a `μ_p(L)`-valued cocycle `w` whose Kummer image is the class of
`c ∘ π`, i.e. the inflation of `y`. -/
lemma exists_muClass_kummerLevel_eq (p : ℕ) (hp : p.Prime)
    (M : FiniteGaloisIntermediateField K K')
    (y : UnitsLevelH2 (⊤ : Subgroup Gal(K'/K)) M) (hpy : p • y = 0) :
    ∃ (L : FiniteGaloisIntermediateField K K') (hML : M ≤ L)
      (w : (muLevelSystem p (⊤ : Subgroup Gal(K'/K))).obj L),
      (kummerLevel p ⊤ L) w = (unitsLevelSystem ⊤).map hML y := by
  classical
  -- ## Step 1: a cocycle `c` representing `y` and a cochain `βm` with `d₁₂ βm = p • c`
  obtain ⟨c, hc⟩ := (ModuleCat.epi_iff_surjective
      (groupCohomology.H2π (unitsLevelRep (⊤ : Subgroup Gal(K'/K)) M))).1 inferInstance y
  have hpc : (groupCohomology.H2π (unitsLevelRep (⊤ : Subgroup Gal(K'/K)) M)) (p • c) = 0 := by
    rw [map_nsmul, hc]
    exact hpy
  obtain ⟨βm, hβm⟩ :=
    exists_mul_cochain_of_H2π_eq_zero (⊤ : Subgroup Gal(K'/K)) M (p • c) hpc
  let cfun : LevelGroup (⊤ : Subgroup Gal(K'/K)) M × LevelGroup (⊤ : Subgroup Gal(K'/K)) M →
      Additive (↥M)ˣ := fun gh => c gh
  -- multiplicative form of the relation `d₁₂ βm = p • c`
  have hrel : ∀ g h : LevelGroup (⊤ : Subgroup Gal(K'/K)) M,
      (levelGroupRestrictHom (⊤ : Subgroup Gal(K'/K)) M g) • βm h / βm (g * h) * βm g
        = (cfun (g, h)).toMul ^ p := by
    intro g h
    have h2 : (groupCohomology.d₁₂ (unitsLevelRep (⊤ : Subgroup Gal(K'/K)) M)).hom
          (fun g => Additive.ofMul (βm g)) (g, h) = (p • c) (g, h) := congrFun hβm (g, h)
    have h3 : Additive.ofMul
        ((levelGroupRestrictHom (⊤ : Subgroup Gal(K'/K)) M g) • βm h / βm (g * h) * βm g)
        = (p • c) (g, h) := by
      rw [← h2]
      rfl
    have h4 : (p • c) (g, h) = Additive.ofMul ((cfun (g, h)).toMul ^ p) :=
      (show (p • c) (g, h) = p • cfun (g, h) from rfl).trans
        (ofMul_pow p ((cfun (g, h)).toMul)).symm
    exact Additive.ofMul.injective (h3.trans h4)
  -- ## Step 2: `p`-th roots of the values of `βm` in the separably closed `K'`
  haveI : IsSepClosed K' := IsSepClosure.sep_closed K
  haveI hNe : NeZero (p : K') := ⟨by
    intro h0
    have h1 : algebraMap K K' (p : K) = 0 := by rw [map_natCast, h0]
    have h2 : (p : K) = 0 := (algebraMap K K').injective (by simpa using h1)
    exact (Nat.cast_ne_zero.mpr hp.ne_zero) h2⟩
  choose root hroot using fun g : LevelGroup (⊤ : Subgroup Gal(K'/K)) M =>
    IsSepClosed.exists_pow_nat_eq (k := K')
      (((βm g : (↥M)ˣ) : ↥M) : K') p
  have hroot_ne : ∀ g : LevelGroup (⊤ : Subgroup Gal(K'/K)) M, root g ≠ 0 := by
    intro g h0
    have h1 : (((βm g : (↥M)ˣ) : ↥M) : K') = 0 := by
      rw [← hroot g, h0, zero_pow hp.ne_zero]
    exact Units.ne_zero (βm g) (Subtype.ext h1)
  let uroot : LevelGroup (⊤ : Subgroup Gal(K'/K)) M → K'ˣ :=
    fun g => Units.mk0 (root g) (hroot_ne g)
  have huroot_pow : ∀ g, uroot g ^ p
      = Units.map (IntermediateField.val (K := K) (L := K') M).toMonoidHom (βm g) := by
    intro g
    refine Units.ext ?_
    rw [Units.val_pow_eq_pow_val, Units.val_mk0]
    exact hroot g
  -- ## Step 3: the level `L` generated by `M` and the chosen `p`-th roots
  let a' : LevelGroup (⊤ : Subgroup Gal(K'/K)) M → K' := fun g => ((uroot g : K'ˣ) : K')
  haveI hfin : Finite (Set.range a') := Set.finite_range a'
  let L : FiniteGaloisIntermediateField K K' :=
    FiniteGaloisIntermediateField.adjoin K (Set.range a') ⊔ M
  have hML : M ≤ L := le_sup_right
  have hmemL : ∀ g, a' g ∈ (L : IntermediateField K K') := by
    intro g
    have h1 : a' g ∈ (FiniteGaloisIntermediateField.adjoin K (Set.range a') :
        IntermediateField K K') :=
      FiniteGaloisIntermediateField.subset_adjoin K (Set.range a') ⟨g, rfl⟩
    exact (show (FiniteGaloisIntermediateField.adjoin K (Set.range a') :
        IntermediateField K K') ≤ (L : IntermediateField K K') from le_sup_left) h1
  -- ## Step 4: the cochain `g ↦ a_{π g}` on the bigger level
  let π : LevelGroup (⊤ : Subgroup Gal(K'/K)) L →* LevelGroup (⊤ : Subgroup Gal(K'/K)) M :=
    levelQuotHom (U := ⊤) hML
  let aL : LevelGroup (⊤ : Subgroup Gal(K'/K)) L → (↥L)ˣ := fun g =>
    Units.mk0 ⟨a' (π g), hmemL (π g)⟩ (by
      intro h0
      exact hroot_ne (π g) (congrArg Subtype.val h0))
  let inclL : (↥L)ˣ →* K'ˣ :=
    Units.map (IntermediateField.val (K := K) (L := K') L).toMonoidHom
  have hvalL : ∀ g, inclL (aL g) = uroot (π g) := by
    intro g
    refine Units.ext ?_
    rfl
  have hinclL_inj : Function.Injective inclL := by
    intro u v huv
    refine Units.ext (Subtype.ext ?_)
    exact congrArg (fun w : K'ˣ => (w : K')) huv
  have haL_pow : ∀ g, aL g ^ p
      = Units.map (IntermediateField.inclusion hML).toMonoidHom (βm (π g)) := by
    intro g
    refine hinclL_inj ?_
    calc inclL (aL g ^ p) = inclL (aL g) ^ p := map_pow inclL (aL g) p
      _ = uroot (π g) ^ p := by rw [hvalL g]
      _ = Units.map (IntermediateField.val (K := K) (L := K') M).toMonoidHom (βm (π g)) :=
            huroot_pow (π g)
      _ = inclL (Units.map (IntermediateField.inclusion hML).toMonoidHom (βm (π g))) := by
            refine Units.ext ?_
            rfl
  have haL_smul_pow : ∀ g h : LevelGroup (⊤ : Subgroup Gal(K'/K)) L,
      (((levelGroupRestrictHom (⊤ : Subgroup Gal(K'/K)) L g : ↥L ≃ₐ[K] ↥L)) • aL h) ^ p
        = Units.map (IntermediateField.inclusion hML).toMonoidHom
            (((levelGroupRestrictHom (⊤ : Subgroup Gal(K'/K)) M (π g) : ↥M ≃ₐ[K] ↥M))
              • βm (π h)) := by
    intro g h
    have hcompat := unitsLevelRestrictCompat (⊤ : Subgroup Gal(K'/K)) hML g (βm (π h))
    rw [AlgEquiv.smul_units_def, AlgEquiv.smul_units_def] at hcompat
    rw [AlgEquiv.smul_units_def, ← map_pow, haL_pow h]
    exact hcompat.symm
  -- ## Step 5: the difference of the two cocycles
  let z₁ : ↥(groupCohomology.cocycles₂ (unitsLevelRep (⊤ : Subgroup Gal(K'/K)) L)) :=
    groupCohomology.mapCocycles₂ π (unitsLevelMapCoeff (⊤ : Subgroup Gal(K'/K)) hML) c
  let dβ : LevelGroup (⊤ : Subgroup Gal(K'/K)) L × LevelGroup (⊤ : Subgroup Gal(K'/K)) L →
      Additive (↥L)ˣ :=
    (groupCohomology.d₁₂ (unitsLevelRep (⊤ : Subgroup Gal(K'/K)) L)).hom
      (fun g => Additive.ofMul (aL g))
  have hdβ_mem : dβ ∈ groupCohomology.cocycles₂ (unitsLevelRep (⊤ : Subgroup Gal(K'/K)) L) :=
    groupCohomology.coboundaries₂_le_cocycles₂ _
      (show dβ ∈ groupCohomology.coboundaries₂ (unitsLevelRep (⊤ : Subgroup Gal(K'/K)) L) from
        ⟨(fun g => Additive.ofMul (aL g)), rfl⟩)
  let z₂ : ↥(groupCohomology.cocycles₂ (unitsLevelRep (⊤ : Subgroup Gal(K'/K)) L)) :=
    ⟨dβ, hdβ_mem⟩
  let zz : ↥(groupCohomology.cocycles₂ (unitsLevelRep (⊤ : Subgroup Gal(K'/K)) L)) := z₁ - z₂
  let z₁fun : LevelGroup (⊤ : Subgroup Gal(K'/K)) L × LevelGroup (⊤ : Subgroup Gal(K'/K)) L →
      Additive (↥L)ˣ := fun gh => z₁ gh
  let zzfun : LevelGroup (⊤ : Subgroup Gal(K'/K)) L × LevelGroup (⊤ : Subgroup Gal(K'/K)) L →
      Additive (↥L)ˣ := fun gh => zz gh
  have hz₁_val : ∀ g h, z₁ (g, h) = Additive.ofMul
      (Units.map (IntermediateField.inclusion hML).toMonoidHom ((cfun (π g, π h)).toMul)) := by
    intro g h
    show (unitsLevelMapCoeff (⊤ : Subgroup Gal(K'/K)) hML) (cfun (π g, π h))
      = Additive.ofMul (Units.map (IntermediateField.inclusion hML).toMonoidHom
          ((cfun (π g, π h)).toMul))
    rfl
  have hdβ_val : ∀ g h, dβ (g, h) = Additive.ofMul
      (((levelGroupRestrictHom (⊤ : Subgroup Gal(K'/K)) L g : ↥L ≃ₐ[K] ↥L)) • aL h
        / aL (g * h) * aL g) := fun g h => rfl
  have hzz_val : ∀ g h, zzfun (g, h) = z₁fun (g, h) - dβ (g, h) := by
    intro g h
    show (z₁ - z₂) (g, h) = z₁fun (g, h) - dβ (g, h)
    rfl
  have hzz_pow : ∀ g h, (zzfun (g, h)).toMul ^ p = 1 := by
    intro g h
    have h1 : (zzfun (g, h)).toMul = (z₁fun (g, h)).toMul / (dβ (g, h)).toMul := by
      rw [hzz_val]
      exact toMul_sub _ _
    have hz1p : (z₁fun (g, h)).toMul ^ p
        = Units.map (IntermediateField.inclusion hML).toMonoidHom
            ((cfun (π g, π h)).toMul ^ p) := by
      rw [show z₁fun (g, h) = z₁ (g, h) from rfl, hz₁_val g h, toMul_ofMul, map_pow]
    have hdβp : (dβ (g, h)).toMul ^ p
        = Units.map (IntermediateField.inclusion hML).toMonoidHom
            ((cfun (π g, π h)).toMul ^ p) := by
      rw [hdβ_val g h, toMul_ofMul, mul_pow, div_pow, haL_smul_pow g h, haL_pow (g * h),
        haL_pow g, ← map_div, ← map_mul, map_mul π g h, hrel (π g) (π h)]
    rw [h1, div_pow, hdβp, hz1p]
    simp
  -- ## Step 6: the `μ_p`-valued cocycle and its Kummer class
  have hzz_exists : ∀ gh : LevelGroup (⊤ : Subgroup Gal(K'/K)) L ×
      LevelGroup (⊤ : Subgroup Gal(K'/K)) L,
      ∃ u : (↥L)ˣ, zz gh = Additive.ofMul u ∧ u ^ p = 1 := by
    intro gh
    obtain ⟨g, h⟩ := gh
    exact ⟨(zzfun (g, h)).toMul, (ofMul_toMul (zzfun (g, h))).symm, hzz_pow g h⟩
  obtain ⟨w₀, hw⟩ := exists_muCocycle_of_unitsCocycle p (⊤ : Subgroup Gal(K'/K)) L zz hzz_exists
  refine ⟨L, hML, (groupCohomology.H2π (muLevelRep p (⊤ : Subgroup Gal(K'/K)) L)) w₀, ?_⟩
  have hz₂_zero : (groupCohomology.H2π (unitsLevelRep (⊤ : Subgroup Gal(K'/K)) L)) z₂ = 0 :=
    (groupCohomology.H2π_eq_zero_iff z₂).mpr ⟨(fun g => Additive.ofMul (aL g)), rfl⟩
  have hz₁_class : (groupCohomology.H2π (unitsLevelRep (⊤ : Subgroup Gal(K'/K)) L)) z₁
      = (unitsLevelMap (⊤ : Subgroup Gal(K'/K)) hML) y := by
    refine (groupCohomology.H2π_comp_map_apply π
      (unitsLevelMapCoeff (⊤ : Subgroup Gal(K'/K)) hML) c).symm.trans ?_
    rw [hc]
    rfl
  rw [show (kummerLevel p (⊤ : Subgroup Gal(K'/K)) L)
      = groupCohomology.map (MonoidHom.id (LevelGroup (⊤ : Subgroup Gal(K'/K)) L))
          (muToUnits p (⊤ : Subgroup Gal(K'/K)) L) 2 from rfl,
    groupCohomology.H2π_comp_map_apply, hw,
    show zz = z₁ - z₂ from rfl, map_sub, hz₁_class, hz₂_zero, sub_zero]
  rfl

/-- **The image of the Kummer map on the colimits is exactly the `p`-torsion of the units colimit.**

Let `K` be a field of characteristic `0`, `K'` a separable closure of `K`, and `p` a prime.  An
element `x` of the units colimit `H2Units ⊤ = colim_L H²(Gal(L/K), Lˣ)` (over the finite Galois
levels `L` of `K'/K`) that is killed by `p` is the image of a class of the `μ_p`-colimit
`MuColim p ⊤ = colim_L H²(Gal(L/K), μ_p(L))` under the Kummer map `kummerColim p ⊤`.

This is the exactness of the Kummer sequence `1 → μ_p → K̄ˣ → K̄ˣ → 1` (exact because `K'ˣ` is
`p`-divisible in characteristic `0`) *in the limit*: the image of `H²(K, μ_p) → H²(K, K̄ˣ)` is the
`p`-torsion of `Br(K) = H²(K, K̄ˣ)`.

Proof route (cochain level, no Tate duality needed).  Let `x` be represented at a level `M` by a
class `y` with `p • y = 0` (first move the representative to the level where its `p`-multiple
vanishes, using `LevelSystem.ofLevel_eq_iff`).  Choose a `2`-cocycle `c` on `LevelGroup ⊤ M` with
`H2π c = y` and a `1`-cochain `b` with `d₁₂ b = p • c` (in multiplicative notation `b g ^ p = d c`,
which exists since `p • y = 0`).  For each `g` choose a `p`-th root `a g : K'ˣ` of the value `b g`
(`IsSepClosed.exists_pow_nat_eq`), and let `L` be the join of `M` with the finitely many finite
Galois levels `adjoin K {a g}`.  The `1`-cochain `b_L : g ↦ (a (π g))` on `LevelGroup ⊤ L`
satisfies `(d₁₂ b_L (g,h)) ^ p = (c (π g, π h)) ^ p`, so `ε := (d₁₂ b_L) - (c ∘ π)` takes values
in `μ_p(L)` and is a `2`-cocycle.  Hence, in the units of `L`, `c ∘ π = (d₁₂ b_L) - ε` is
cohomologous to `ε⁻¹`, and the Kummer map at the level `L` of the class of `ε` is the class of
`c ∘ π`, i.e. the image of `x` in `H2Units ⊤`. -/
theorem kummerColim_surjective_pTorsion {K K' : Type} [Field K] [CharZero K] [Field K']
    [Algebra K K'] [IsSepClosure K K'] (p : ℕ) (hp : p.Prime)
    (x : NK.HassePrinciple.H2Units (K := K) (K' := K') (⊤ : Subgroup Gal(K'/K)))
    (hx : p • x = 0) :
    ∃ y : NK.HassePrinciple.MuColim (K := K) (K' := K') p ⊤,
      NK.HassePrinciple.kummerColim (K := K) (K' := K') p ⊤ y = x := by
  obtain ⟨M, y, hyM, hpy⟩ :=
    exists_level_representative_nsmul_eq_zero (⊤ : Subgroup Gal(K'/K)) p x hx
  obtain ⟨L, hML, w, hw⟩ := exists_muClass_kummerLevel_eq p hp M y hpy
  refine ⟨MuColim.ofLevel p ⊤ L w, ?_⟩
  have hgoal : kummerColim p ⊤ (MuColim.ofLevel p ⊤ L w)
      = (unitsLevelSystem (⊤ : Subgroup Gal(K'/K))).ofLevel L ((kummerLevel p ⊤ L) w) :=
    kummerColim_ofLevel p ⊤ L w
  rw [hgoal, hw]
  exact ((unitsLevelSystem (⊤ : Subgroup Gal(K'/K))).ofLevel_map hML y).trans hyM

end NK.NUV2.ABHN
