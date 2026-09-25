import Mathlib
import Submission.NK.NUV2.ABHN.LocalBrauerAux
import Submission.NK.NUV2.ABHN.unitsLevelMap_injective
import Submission.NK.NUV2.LC.RouteB.Defs
import Submission.NK.NUV2.LC.nonempty_addEquiv_unitsLevelH2_level
import Submission.NK.NUV2.RouteC.map_powHom_eq_zero_iff_of_isCyclic
import Submission.NK.NUV2.LC.finiteSupportTwistDefs
import Submission.NK.NUV2.RouteE.levelSymbol

set_option linter.style.haveILetI false
set_option linter.unusedVariables false

namespace NK.NUV2.LC.RouteB

open CategoryTheory

/-! ## The route

The cyclic algebra class `cls b` of `b : Fˣ` for the cyclic extension `E/F` is RouteC's class
`b ∪ δχ` (`NK.NUV2.RouteC.powHom b (deltaHomChar _ χ)`) with `χ` a faithful character of
`Gal(E/F)`; RouteC's criterion (`NK.NUV2.RouteC.map_powHom_eq_zero_iff_of_isCyclic`) says
`cls b = 0 ↔ b ∈ N_{E/F} Eˣ`.  To lift it to the units colimit `H2Units ⊤ = colim_L H²(Gal(L/F), Lˣ)`
one needs the two colimit facts

* `nonempty_addEquiv_unitsLevelH2_top`: at a finite Galois level `L` the level cohomology
  `H²(LevelGroup ⊤ L, Lˣ)` is `H²(Gal(L/F), Lˣ)` — the level dictionary together with the
  coefficient-ring transfer `CoeffInt = ULift ℤ → ℤ`
  (`NK.NUV2.LC.nonempty_addEquiv_groupCohomology_res_mulEquiv`,
  `..._two_coeffTransfer`);
* `H2Units_ofLevel_injective_top`: the structure maps of the units colimit are injective, so the
  vanishing of the level-`E` class is detected in the colimit — this is Hilbert 90 (the transition
  maps, i.e. the inflations `H²(Gal(L/F), Lˣ) → H²(Gal(L'/F), L'ˣ)`, are injective,
  `NK.NUV2.ABHN.unitsLevelMap_injective`),

and the additivity of the structure maps (`NK.NUV2.ABHN.H2Units.ofLevel_add`) together with the
multiplicativity of the cup product in its `H⁰`-slot (`NK.NUV2.RouteC.powHom_mul`,
`NK.NUV2.RouteE.map_add_apply`). -/

/-- **A faithful `ℚ/ℤ`-valued character of a finite cyclic group**: for a finite cyclic group `G`
there is an additive character `Additive G →+ ℚ/ℤ` of additive order `Nat.card G`. -/
lemma exists_faithful_character_of_isCyclic' {G : Type} [Group G] [Finite G] (h : IsCyclic G) :
    ∃ χ : Additive G →+ NK.NUV2.RouteC.qmodZ, addOrderOf χ = Nat.card G := by
  obtain ⟨g, hg⟩ := IsCyclic.exists_zpow_surjective (G := G)
  have hgen : ∀ x : G, x ∈ Subgroup.zpowers g := fun x => by
    obtain ⟨k, hk⟩ := hg x
    exact Subgroup.mem_zpowers_iff.mpr ⟨k, hk⟩
  have hcomm : ∀ a b : G, a * b = b * a := by
    intro a b
    obtain ⟨m, hm⟩ := hgen a
    obtain ⟨n, hn⟩ := hgen b
    rw [← hm, ← hn, ← zpow_add, add_comm, zpow_add]
  letI : CommGroup G := { (inferInstance : Group G) with mul_comm := hcomm }
  have hgord : orderOf g = Nat.card G := orderOf_eq_card_of_forall_mem_zpowers hgen
  have hcard : Nat.card (Additive G) = Nat.card G :=
    Nat.card_congr (Equiv.ofBijective Additive.toMul
      ⟨Additive.toMul.injective, Additive.toMul.surjective⟩)
  have hord : addOrderOf (Additive.ofMul g) = Nat.card (Additive G) := by
    rw [addOrderOf_ofMul_eq_orderOf, hgord, hcard]
  refine ⟨NK.NUV2.RouteC.invariantOf (Additive.ofMul g) hord, ?_⟩
  rw [NK.NUV2.RouteC.addOrderOf_addMonoidHom_eq_of_generator g hgen,
    NK.NUV2.RouteC.invariantOf_generator, ← NK.NUV2.RouteC.zmodToQmodZ_one,
    NK.NUV2.RouteC.addOrderOf_zmodToQmodZ (n := Nat.card (Additive G))
      (Nat.card_ne_zero.mpr ⟨inferInstance, inferInstance⟩),
    ZMod.addOrderOf_one]
  exact hcard

/-- **The level dictionary for the units coefficients at a finite Galois level**: the level
cohomology `H²(LevelGroup ⊤ L, Lˣ)` of the units level system is the group cohomology
`H²(Gal(L/F), Lˣ)` of the Galois group of the level. -/
theorem nonempty_addEquiv_unitsLevelH2_top {F : Type} [Field F] {F' : Type} [Field F']
    [Algebra F F'] [IsSepClosure F F'] (L : FiniteGaloisIntermediateField F F') :
    Nonempty (NK.HassePrinciple.UnitsLevelH2 (K := F) (K' := F') (⊤ : Subgroup Gal(F'/F)) L ≃+
      groupCohomology (Rep.ofAlgebraAutOnUnits F ↥L) 2) := by
  classical
  have hsurj : Function.Surjective
      (NK.HassePrinciple.levelRestrictHom (K := F) (K' := F') (⊤ : Subgroup Gal(F'/F)) L) := by
    intro y
    obtain ⟨x, hx⟩ := AlgEquiv.restrictNormalHom_surjective (F := F) (K₁ := ↥L) (E := F') y
    exact ⟨⟨x, Subgroup.mem_top x⟩, hx⟩
  let e := QuotientGroup.liftEquiv (L.fixingSubgroup.subgroupOf (⊤ : Subgroup Gal(F'/F))) hsurj
    (NK.HassePrinciple.levelRestrictHom_ker (K := F) (K' := F') (⊤ : Subgroup Gal(F'/F)) L).symm
  obtain ⟨φ₁⟩ := NK.NUV2.LC.nonempty_addEquiv_groupCohomology_res_mulEquiv
    (A := NK.HassePrinciple.unitsRep F ↥L) e 2
  obtain ⟨φ₂⟩ := NK.NUV2.LC.nonempty_addEquiv_groupCohomology_two_coeffTransfer
    (k := NK.HassePrinciple.CoeffInt) (k' := ℤ) (G := ↥L ≃ₐ[F] ↥L) (V := Additive (↥L)ˣ)
  exact ⟨φ₁.trans φ₂⟩

/-- **The structure maps of the units colimit are injective** (Hilbert 90): a level class which
dies after inflation to some larger level is already zero.

The transition maps of the level system are the inflations `H²(Gal(L/F), Lˣ) → H²(Gal(L'/F), L'ˣ)`
and they are injective (`NK.NUV2.ABHN.unitsLevelMap_injective`, from Hilbert 90 for `F̄ˣ`); the
colimit structure relation identifies exactly the classes with a common inflation
(`NK.BrauerTwist.LevelSystem.ofLevel_eq_iff`). -/
lemma H2Units_ofLevel_injective_top {F : Type} [Field F] {F' : Type} [Field F']
    [Algebra F F'] [IsSepClosure F F'] (L : FiniteGaloisIntermediateField F F') :
    Function.Injective (NK.HassePrinciple.H2Units.ofLevel (K := F) (K' := F')
      (⊤ : Subgroup Gal(F'/F)) L) := by
  intro a b hab
  obtain ⟨M, h₁, h₂, hM⟩ := (NK.BrauerTwist.LevelSystem.ofLevel_eq_iff
    (NK.HassePrinciple.unitsLevelSystem (⊤ : Subgroup Gal(F'/F))) a b).mp hab
  have hmap : (NK.HassePrinciple.unitsLevelSystem (⊤ : Subgroup Gal(F'/F))).map h₁ =
      (NK.HassePrinciple.unitsLevelSystem (⊤ : Subgroup Gal(F'/F))).map h₂ :=
    NK.BrauerTwist.LevelSystem.map_congr
  rw [hmap] at hM
  exact NK.NUV2.ABHN.unitsLevelMap_injective h₁ hM

/-- The zero of the units colimit is the class of the zero of any level: the structure maps of the
colimit are additive (`NK.NUV2.ABHN.H2Units.ofLevel_add`). -/
lemma H2Units_ofLevel_zero {F : Type} [Field F] {F' : Type} [Field F'] [Algebra F F']
    [IsSepClosure F F'] (L : FiniteGaloisIntermediateField F F') :
    NK.HassePrinciple.H2Units.ofLevel (K := F) (K' := F') (⊤ : Subgroup Gal(F'/F)) L
      (0 : NK.HassePrinciple.UnitsLevelH2 (K := F) (K' := F') (⊤ : Subgroup Gal(F'/F)) L) = 0 := by
  set x := NK.HassePrinciple.H2Units.ofLevel (K := F) (K' := F') (⊤ : Subgroup Gal(F'/F)) L
    (0 : NK.HassePrinciple.UnitsLevelH2 (K := F) (K' := F') (⊤ : Subgroup Gal(F'/F)) L) with hx
  have h : x = x + x := by
    rw [hx]
    have h0 := NK.NUV2.ABHN.H2Units.ofLevel_add (K := F) (K' := F')
      (⊤ : Subgroup Gal(F'/F)) L
      (0 : NK.HassePrinciple.UnitsLevelH2 (K := F) (K' := F') (⊤ : Subgroup Gal(F'/F)) L) 0
    simpa using h0
  have h2 := congrArg (fun y => y - x) h
  simpa using h2.symm

/-- **The cyclic-algebra class in the units colimit.** For `E/F` a finite Galois extension of
number fields with `Gal(E/F)` cyclic (so that RouteC's cyclic criterion applies), there is an
*additive* map `γ : Fˣ → H2Units ⊤` (the units-coefficient profinite cohomology
`colim_L H²(Gal(L/F), Lˣ)`) whose vanishing is exactly the norm condition: `γ b = 0` iff `b` is a
norm from `E`.  Classically `γ b` is the class of the cyclic algebra `(E/F, σ, b)`. -/
theorem exists_unitsClass_of_isCyclic (p : ℕ) (hp : p.Prime)
    {F : Type} [Field F] [NumberField F] (F' : Type) [Field F'] [Algebra F F']
    [IsSepClosure F F'] (E : IntermediateField F F') [FiniteDimensional F E] [IsGalois F E]
    [NumberField ↥E] (hdeg : Module.finrank F E = p) (hcyc : IsCyclic (↥E ≃ₐ[F] ↥E)) :
    ∃ γ : Fˣ → NK.HassePrinciple.H2Units (K := F) (K' := F') (⊤ : Subgroup Gal(F'/F)),
      (∀ b₁ b₂ : Fˣ, γ (b₁ * b₂) = γ b₁ + γ b₂) ∧
      (∀ b : Fˣ, γ b = 0 ↔ b ∈ MonoidHom.range (Units.map (Algebra.norm F : ↥E →* F))) := by
  classical
  -- the faithful character of the (cyclic) Galois group of `E/F`
  obtain ⟨χ, hχ⟩ := exists_faithful_character_of_isCyclic' (G := ↥E ≃ₐ[F] ↥E) hcyc
  -- the level dictionary `UnitsLevelH2 ⊤ E ≃+ H²(Gal(E/F), Eˣ)`
  obtain ⟨Φ⟩ := nonempty_addEquiv_unitsLevelH2_top (F := F) (F' := F')
    (⟨E⟩ : FiniteGaloisIntermediateField F F')
  -- the class of the cyclic algebra `(E/F, σ, b)`, in the units coefficients
  let cls : Fˣ → groupCohomology (Rep.ofAlgebraAutOnUnits F ↥E) 2 := fun b =>
    (groupCohomology.map (MonoidHom.id (↥E ≃ₐ[F] ↥E))
      (NK.NUV2.RouteC.powHom (F := F) (E := ↥E) b) 2)
      (NK.NUV2.RouteC.deltaHomChar (↥E ≃ₐ[F] ↥E) χ)
  -- the cup product is additive in its `H⁰`-slot
  have hcls : ∀ b₁ b₂ : Fˣ, cls (b₁ * b₂) = cls b₁ + cls b₂ := by
    intro b₁ b₂
    show (groupCohomology.map (MonoidHom.id (↥E ≃ₐ[F] ↥E))
        (NK.NUV2.RouteC.powHom (F := F) (E := ↥E) (b₁ * b₂)) 2)
        (NK.NUV2.RouteC.deltaHomChar (↥E ≃ₐ[F] ↥E) χ) =
      (groupCohomology.map (MonoidHom.id (↥E ≃ₐ[F] ↥E))
        (NK.NUV2.RouteC.powHom (F := F) (E := ↥E) b₁) 2)
        (NK.NUV2.RouteC.deltaHomChar (↥E ≃ₐ[F] ↥E) χ) +
      (groupCohomology.map (MonoidHom.id (↥E ≃ₐ[F] ↥E))
        (NK.NUV2.RouteC.powHom (F := F) (E := ↥E) b₂) 2)
        (NK.NUV2.RouteC.deltaHomChar (↥E ≃ₐ[F] ↥E) χ)
    rw [NK.NUV2.RouteC.powHom_mul]
    exact NK.NUV2.RouteE.map_add_apply _ _ _ _
  refine ⟨fun b => NK.HassePrinciple.H2Units.ofLevel (⊤ : Subgroup Gal(F'/F)) ⟨E⟩ (Φ.symm (cls b)),
    ?_, ?_⟩
  · -- additivity of `γ`, from the additivity of `cls`, of `Φ` and of `ofLevel`
    intro b₁ b₂
    show NK.HassePrinciple.H2Units.ofLevel (⊤ : Subgroup Gal(F'/F)) ⟨E⟩ (Φ.symm (cls (b₁ * b₂))) =
      NK.HassePrinciple.H2Units.ofLevel (⊤ : Subgroup Gal(F'/F)) ⟨E⟩ (Φ.symm (cls b₁)) +
      NK.HassePrinciple.H2Units.ofLevel (⊤ : Subgroup Gal(F'/F)) ⟨E⟩ (Φ.symm (cls b₂))
    rw [hcls b₁ b₂, map_add, NK.NUV2.ABHN.H2Units.ofLevel_add]
  · -- the vanishing criterion
    intro b
    have h1 : NK.HassePrinciple.H2Units.ofLevel (⊤ : Subgroup Gal(F'/F)) ⟨E⟩ (Φ.symm (cls b)) = 0 ↔
        cls b = 0 := by
      constructor
      · intro h
        have h2 : Φ.symm (cls b) = 0 :=
          H2Units_ofLevel_injective_top ⟨E⟩ (by rw [h, H2Units_ofLevel_zero ⟨E⟩])
        exact Φ.symm.injective (by rw [h2, map_zero])
      · intro h
        rw [h, map_zero, H2Units_ofLevel_zero ⟨E⟩]
    have h2 : cls b = 0 ↔
        b ∈ MonoidHom.range (Units.map (Algebra.norm F : ↥E →* F)) :=
      NK.NUV2.RouteC.map_powHom_eq_zero_iff_of_isCyclic (F := F) (E := ↥E) hcyc χ hχ b
    exact h1.trans h2

end NK.NUV2.LC.RouteB
