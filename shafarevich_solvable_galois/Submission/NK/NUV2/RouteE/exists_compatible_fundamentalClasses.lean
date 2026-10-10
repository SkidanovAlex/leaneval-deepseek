import Mathlib.CategoryTheory.CofilteredSystem
import Mathlib.RingTheory.Henselian
import Mathlib.Tactic.Have
import Mathlib.Algebra.Lie.OfAssociative
import Mathlib.Combinatorics.Quiver.ReflQuiver
import Mathlib.FieldTheory.Galois.GaloisClosure
import Mathlib.RingTheory.Flat.TorsionFree
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.NumberTheory.NumberField.Completion.FinitePlace
import Mathlib.RepresentationTheory.Homological.GroupCohomology.Functoriality
import Submission.NK.NUV2.RouteD.LevelTransition
import Submission.NK.NUV2.RouteE.levelCoherent
import Submission.NK.NUV2.RouteE.levelH2

/-!
# A compatible family of fundamental classes (Route E, step L3)

For `F = Q.adicCompletion K` and `F^{ab} = maxAbelianSubext F F'` (`F'` the separable closure),
the second cohomology `H²(Gal(L/F), Lˣ)` of the units is cyclic of order `[L : F]` at every finite
Galois level `L` of `F^{ab}`.  This file constructs a *compatible* family of generators: a choice of
fundamental class `u_L` at every level such that the level inflation maps send `u_L` to `[E:L]·u_E`
for `L ≤ E`.  This is the arithmetic input of the local reciprocity law in its compatible form
(`KernelCondition`).

The construction is König's lemma (`nonempty_sections_of_finite_inverse_system`) applied to the
inverse system of the finite non-empty sets `lvlGen L` of fundamental classes, with transition maps
`lvlTrans L E h u = ` the unique `v` with `Inf_{L→E} v = [E:L] · u`.
-/

set_option maxHeartbeats 8000000
set_option synthInstance.maxHeartbeats 800000
set_option linter.unusedSectionVars false
set_option linter.style.haveILetI false

open CategoryTheory

namespace NK.NUV2.RouteE

variable {K : Type} [Field K] [NumberField K]
variable (Q : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K))

/-- The poset of finite Galois levels of `F^{ab}/F`, `F = Q.adicCompletion K`. -/
noncomputable abbrev Lvl := FiniteGaloisIntermediateField (Q.adicCompletion K)
    (NK.LocalReciprocity.maxAbelianSubext (Q.adicCompletion K) (SeparableClosure (Q.adicCompletion K)))

/-- The ambient field `F^{ab}`. -/
noncomputable abbrev lvlTop :=
  NK.LocalReciprocity.maxAbelianSubext (Q.adicCompletion K) (SeparableClosure (Q.adicCompletion K))

/-- The second cohomology of the units at a level. -/
noncomputable abbrev lvlCoh (L : Lvl Q) : ModuleCat ℤ :=
  groupCohomology (Rep.ofAlgebraAutOnUnits (Q.adicCompletion K) ↥L) 2

/-- The generators of `H²(Gal(L/F), Lˣ)`: the fundamental classes at the level `L`. -/
noncomputable abbrev lvlGen (L : Lvl Q) : Type :=
  {u : lvlCoh Q L // addOrderOf u = Nat.card (lvlCoh Q L)}

/-- The degree `[L : F]` as the cardinality of the Galois group. -/
noncomputable abbrev lvlDeg (L : Lvl Q) : ℕ := Nat.card (↥L ≃ₐ[(Q.adicCompletion K)] ↥L)

/-- The index `[E : L]`. -/
noncomputable abbrev lvlRatio (L E : Lvl Q) : ℕ := lvlDeg Q E / lvlDeg Q L

/-- Every finite Galois level of `F^{ab}` is abelian over `F`. -/
lemma lvlComm (L : Lvl Q) : ∀ σ τ : ↥L ≃ₐ[(Q.adicCompletion K)] ↥L, σ * τ = τ * σ :=
  NK.LocalCFT.Reduction.commutative_level (F := Q.adicCompletion K)
    (F' := SeparableClosure (Q.adicCompletion K)) (L : IntermediateField _ _)

/-- **`L1` at a level**: `H²(Gal(L/F), Lˣ)` is finite, of cardinality `[L : F]`, and has a
generator. -/
lemma lvlData (L : Lvl Q) : Nat.card (lvlCoh Q L) = lvlDeg Q L ∧
    Nonempty (lvlGen Q L) ∧ Finite (lvlCoh Q L) := by
  have hc := lvlComm Q L
  have h1 : Nat.card (lvlCoh Q L) ≤ Module.finrank (Q.adicCompletion K) ↥L :=
    Commons.NumberTheory.NumberField.Completion.natCard_groupCohomology_two_units_le_finrank_of_abelian
      (Q := Q) (B := Q.adicCompletion K) (E := ↥L) hc
  have h2 : Module.finrank (Q.adicCompletion K) ↥L ≤ Nat.card (lvlCoh Q L) :=
    Commons.NumberTheory.NumberField.Completion.groupCohomology_two_units_ge_finrank
      (Q := Q) (F := Q.adicCompletion K) (E := ↥L)
  have hdeg : lvlDeg Q L = Module.finrank (Q.adicCompletion K) ↥L :=
    IsGalois.card_aut_eq_finrank (Q.adicCompletion K) ↥L
  have hcard : Nat.card (lvlCoh Q L) = lvlDeg Q L := by
    rw [hdeg]; exact le_antisymm h1 h2
  obtain ⟨α, hα⟩ :=
    Commons.NumberTheory.NumberField.Completion.ArtinMap.exists_addOrderOf_eq_finrank_groupCohomology_two_units_aux
      (Q := Q) (F := Q.adicCompletion K) (E := ↥L)
  have hfin : Finite (lvlCoh Q L) :=
    Commons.NumberTheory.NumberField.Completion.finite_groupCohomology_two_units_of_solvable (Q := Q)
      (F := Q.adicCompletion K) (E := ↥L) (Group.isSolvable_of_comm hc)
  exact ⟨hcard, ⟨⟨α, by rw [hcard, hdeg]; exact hα⟩⟩, hfin⟩

/-- **The transition map on fundamental classes**: for `L ≤ E` and a fundamental class `u` at `E`,
there is a fundamental class `v` at `L` whose inflation is `[E:L] • u`. -/
lemma lvlExists (L E : Lvl Q) (h : L ≤ E) (u : lvlGen Q E) :
    ∃ v : lvlCoh Q L, addOrderOf v = Nat.card (lvlCoh Q L) ∧
      (NK.NUV2.RouteE.levelInfHom L E h) v
        = ((lvlRatio Q L E : ℕ) : ℤ) • (u : lvlCoh Q E) := by
  letI : Algebra ↥L ↥E :=
    RingHom.toAlgebra (Subsemiring.inclusion ((FiniteGaloisIntermediateField.le_iff L E).mp h))
  letI : SMul ↥L ↥E := Algebra.toSMul
  letI : IsScalarTower (Q.adicCompletion K) ↥L ↥E :=
    IsScalarTower.of_algebraMap_eq (R := Q.adicCompletion K) (S := ↥L) (A := ↥E) (fun _ => rfl)
  obtain ⟨v, hv, hmap⟩ := NK.NUV2.RouteD.exists_transition
    (F := Q.adicCompletion K) (A := lvlTop Q)
    (h := (FiniteGaloisIntermediateField.le_iff L E).mp h)
    (fun x => rfl)
    ((AlgEquiv.restrictNormalHom (K₁ := ↥E) (E := ↥L)).ker)
    (NK.NUV2.RouteD.fixedField_restrictKernel _ (fun x => rfl))
    ((lvlData Q E).2.2)
    ((lvlData Q E).1)
    ((lvlData Q L).1)
    (u : lvlCoh Q E) u.2
  exact ⟨v, hv, hmap⟩

/-- The transition on fundamental classes (a *function*, by uniqueness of the preimage). -/
noncomputable def lvlTrans (L E : Lvl Q) (h : L ≤ E) (u : lvlGen Q E) : lvlGen Q L := by
  classical
  exact if h' : L = E then h'.symm ▸ u
    else ⟨Classical.choose (lvlExists Q L E h u),
      (Classical.choose_spec (lvlExists Q L E h u)).1⟩

/-- The characterizing property of the transition at a strict level. -/
lemma lvlTrans_spec (L E : Lvl Q) (h : L ≤ E) (hne : L ≠ E) (u : lvlGen Q E) :
    (NK.NUV2.RouteE.levelInfHom L E h) (lvlTrans Q L E h u : lvlCoh Q L)
      = ((lvlRatio Q L E : ℕ) : ℤ) • (u : lvlCoh Q E) := by
  unfold lvlTrans
  split_ifs with h'
  · exact absurd h' hne
  · exact (Classical.choose_spec (lvlExists Q L E h u)).2

/-- The transition at a level with itself is the identity. -/
lemma lvlTrans_self (L : Lvl Q) (h : L ≤ L) (u : lvlGen Q L) :
    lvlTrans Q L L h u = u := by
  rw [lvlTrans, dif_pos (show L = L from rfl)]

/-- **Injectivity of the level inflation** (Hilbert 90) in the `levelInfHom` vocabulary. -/
lemma levelInfHom_injective (L E : Lvl Q) (h : L ≤ E) :
    Function.Injective (NK.NUV2.RouteE.levelInfHom L E h) := by
  letI : Algebra ↥L ↥E :=
    RingHom.toAlgebra (Subsemiring.inclusion ((FiniteGaloisIntermediateField.le_iff L E).mp h))
  letI : SMul ↥L ↥E := Algebra.toSMul
  letI : IsScalarTower (Q.adicCompletion K) ↥L ↥E :=
    IsScalarTower.of_algebraMap_eq (R := Q.adicCompletion K) (S := ↥L) (A := ↥E) (fun _ => rfl)
  intro x y hxy
  exact NK.NUV2.RouteD.levelInfMap_injective_of_le (F := Q.adicCompletion K) (A := lvlTop Q)
    ((FiniteGaloisIntermediateField.le_iff L E).mp h) (fun _ => rfl) hxy

/-- **Functoriality of the level inflations** in the `levelInfHom` vocabulary. -/
lemma levelInfHom_comp (R E P : Lvl Q) (hRE : R ≤ E) (hEP : E ≤ P) :
    (NK.NUV2.RouteE.levelInfHom R P (le_trans hRE hEP))
      = (NK.NUV2.RouteE.levelInfHom E P hEP).comp (NK.NUV2.RouteE.levelInfHom R E hRE) := by
  letI : Algebra ↥R ↥E := RingHom.toAlgebra (Subsemiring.inclusion ((FiniteGaloisIntermediateField.le_iff R E).mp hRE))
  letI : SMul ↥R ↥E := Algebra.toSMul
  letI : Algebra ↥E ↥P := RingHom.toAlgebra (Subsemiring.inclusion ((FiniteGaloisIntermediateField.le_iff E P).mp hEP))
  letI : SMul ↥E ↥P := Algebra.toSMul
  letI : Algebra ↥R ↥P := RingHom.toAlgebra (Subsemiring.inclusion ((FiniteGaloisIntermediateField.le_iff R P).mp (le_trans hRE hEP)))
  letI : SMul ↥R ↥P := Algebra.toSMul
  haveI : IsScalarTower (Q.adicCompletion K) ↥R ↥E := IsScalarTower.of_algebraMap_eq (R := Q.adicCompletion K) (S := ↥R) (A := ↥E) (fun _ => rfl)
  haveI : IsScalarTower (Q.adicCompletion K) ↥E ↥P := IsScalarTower.of_algebraMap_eq (R := Q.adicCompletion K) (S := ↥E) (A := ↥P) (fun _ => rfl)
  haveI : IsScalarTower (Q.adicCompletion K) ↥R ↥P := IsScalarTower.of_algebraMap_eq (R := Q.adicCompletion K) (S := ↥R) (A := ↥P) (fun _ => rfl)
  haveI : IsScalarTower ↥R ↥E ↥P := IsScalarTower.of_algebraMap_eq (R := ↥R) (S := ↥E) (A := ↥P) (fun _ => rfl)
  refine AddMonoidHom.ext fun x => ?_
  show (NK.NUV2.RouteD.levelInfMap (F := Q.adicCompletion K) (M := ↥R) (L := ↥P)).hom x
    = (NK.NUV2.RouteD.levelInfMap (F := Q.adicCompletion K) (M := ↥E) (L := ↥P)).hom
        ((NK.NUV2.RouteD.levelInfMap (F := Q.adicCompletion K) (M := ↥R) (L := ↥E)).hom x)
  rw [← ModuleCat.comp_apply]
  rw [← NK.NUV2.RouteD.levelInfMap_comp (F := Q.adicCompletion K) (M := ↥R) (L := ↥E) (N := ↥P)]

/-- The degree of a level is positive. -/
lemma lvlDeg_pos (L : Lvl Q) : 0 < lvlDeg Q L := by
  rw [show lvlDeg Q L = Module.finrank (Q.adicCompletion K) ↥L from IsGalois.card_aut_eq_finrank _ _]
  exact Module.finrank_pos

/-- The degree of a lower level divides that of a higher one. -/
lemma lvlDeg_dvd (L E : Lvl Q) (h : L ≤ E) : lvlDeg Q L ∣ lvlDeg Q E := by
  letI : Algebra ↥L ↥E :=
    RingHom.toAlgebra (Subsemiring.inclusion ((FiniteGaloisIntermediateField.le_iff L E).mp h))
  letI : SMul ↥L ↥E := Algebra.toSMul
  letI : IsScalarTower (Q.adicCompletion K) ↥L ↥E :=
    IsScalarTower.of_algebraMap_eq (R := Q.adicCompletion K) (S := ↥L) (A := ↥E) (fun _ => rfl)
  have hL : lvlDeg Q L = Module.finrank (Q.adicCompletion K) ↥L := IsGalois.card_aut_eq_finrank _ _
  have hE : lvlDeg Q E = Module.finrank (Q.adicCompletion K) ↥E := IsGalois.card_aut_eq_finrank _ _
  rw [hL, hE, ← Module.finrank_mul_finrank (Q.adicCompletion K) ↥L ↥E]
  exact dvd_mul_right _ _

/-- Multiplicativity of the index. -/
lemma lvlRatio_mul (L E P : Lvl Q) (hLE : L ≤ E) (hEP : E ≤ P) :
    lvlRatio Q L P = lvlRatio Q L E * lvlRatio Q E P := by
  have hdLE := lvlDeg_dvd Q L E hLE
  have hdEP := lvlDeg_dvd Q E P hEP
  have hpos : 0 < lvlDeg Q E := lvlDeg_pos Q E
  simp only [lvlRatio]
  rw [Nat.div_mul_div_comm hdLE hdEP]
  rw [show lvlDeg Q L * lvlDeg Q E = lvlDeg Q E * lvlDeg Q L from mul_comm _ _]
  exact (Nat.mul_div_mul_left (m := lvlDeg Q E) (lvlDeg Q P) (lvlDeg Q L) hpos).symm

set_option maxHeartbeats 8000000 in
/-- **Transitivity of the transition**: `t_{L≤M} = t_{L≤E} ∘ t_{E≤M}`. -/
lemma lvlTrans_comp (R E P : Lvl Q) (hRE : R ≤ E) (hEP : E ≤ P) (u : lvlGen Q P) :
    lvlTrans Q R P (le_trans hRE hEP) u
      = lvlTrans Q R E hRE (lvlTrans Q E P hEP u) := by
  by_cases hRE' : R = E
  · subst hRE'
    rw [lvlTrans_self]
  · by_cases hEP' : E = P
    · subst hEP'
      rw [lvlTrans_self]
    · have hRPne : R ≠ P := by
        intro h
        exact hRE' (le_antisymm hRE (h.symm ▸ hEP))
      have h1 : (NK.NUV2.RouteE.levelInfHom R P (le_trans hRE hEP))
          ((lvlTrans Q R P (le_trans hRE hEP) u : lvlGen Q R) : lvlCoh Q R)
            = ((lvlRatio Q R P : ℕ) : ℤ) • (u : lvlCoh Q P) :=
        lvlTrans_spec Q R P (le_trans hRE hEP) hRPne u
      have h5 : (NK.NUV2.RouteE.levelInfHom R P (le_trans hRE hEP))
          (((lvlTrans Q R E hRE (lvlTrans Q E P hEP u)) : lvlGen Q R) : lvlCoh Q R)
            = ((lvlRatio Q R P : ℕ) : ℤ) • (u : lvlCoh Q P) := by
        rw [levelInfHom_comp Q R E P hRE hEP, AddMonoidHom.comp_apply,
          lvlTrans_spec Q R E hRE hRE' (lvlTrans Q E P hEP u), map_zsmul,
          lvlTrans_spec Q E P hEP hEP' u,
          lvlRatio_mul Q R E P hRE hEP, Nat.cast_mul, mul_zsmul]
      exact Subtype.ext (levelInfHom_injective Q R P (le_trans hRE hEP) (h1.trans h5.symm))

/-- **The level inflation is the identity at a single level.**  (The `H²` of the units of `L` maps
to itself by the identity: the restriction `Gal(L/F) → Gal(L/F)` is the identity and the units
inclusion `Lˣ → Lˣ` is the identity, the only subtlety being that the algebra structure on `↥L`
over itself is the inclusion rather than the canonical one.) -/
lemma levelInfHom_self (L : Lvl Q) (h : L ≤ L) (x : lvlCoh Q L) :
    (NK.NUV2.RouteE.levelInfHom L L h) x = x := by
  let algMm : Algebra ↥L ↥L :=
    RingHom.toAlgebra (Subsemiring.inclusion ((FiniteGaloisIntermediateField.le_iff L L).mp h))
  letI : Algebra ↥L ↥L := algMm
  let st : IsScalarTower (Q.adicCompletion K) ↥L ↥L :=
    IsScalarTower.of_algebraMap_eq (R := Q.adicCompletion K) (S := ↥L) (A := ↥L) (congrFun rfl)
  letI : IsScalarTower (Q.adicCompletion K) ↥L ↥L := st
  have h1 : @AlgEquiv.restrictNormalHom (Q.adicCompletion K) _ ↥L _ _ (↥L) _ _ algMm st inferInstance
      = MonoidHom.id (↥L ≃ₐ[Q.adicCompletion K] ↥L) := by
    apply AlgEquiv.restrictNormalHom_id
  have h2a : (@NK.NUV2.RouteD.unitsInclCoeff (Q.adicCompletion K) ↥L ↥L _ _ _ _ _ algMm st
      inferInstance).hom.toLinearMap
      = (LinearMap.id : Additive (↥L)ˣ →ₗ[ℤ] Additive (↥L)ˣ) := by
    ext y
    rfl
  have h2b : ((𝟙 (Rep.ofAlgebraAutOnUnits (Q.adicCompletion K) ↥L) :
      Rep.ofAlgebraAutOnUnits (Q.adicCompletion K) ↥L ⟶
        Rep.ofAlgebraAutOnUnits (Q.adicCompletion K) ↥L)).hom.toLinearMap
      = (LinearMap.id : Additive (↥L)ˣ →ₗ[ℤ] Additive (↥L)ˣ) := by
    ext y
    rfl
  have hmain : (@NK.NUV2.RouteD.levelInfMap (Q.adicCompletion K) ↥L ↥L _ _ _ _ _ algMm st
      inferInstance) = 𝟙 (lvlCoh Q L) :=
    (groupCohomology.map_congr
      (f := @AlgEquiv.restrictNormalHom (Q.adicCompletion K) _ ↥L _ _ (↥L) _ _ algMm st inferInstance)
      (g := MonoidHom.id (↥L ≃ₐ[Q.adicCompletion K] ↥L))
      (φ := @NK.NUV2.RouteD.unitsInclCoeff (Q.adicCompletion K) ↥L ↥L _ _ _ _ _ algMm st
        inferInstance)
      (ψ := 𝟙 (Rep.ofAlgebraAutOnUnits (Q.adicCompletion K) ↥L)) h1 (h2a.trans h2b.symm) 2).trans
      (groupCohomology.map_id 2)
  show (@NK.NUV2.RouteD.levelInfMap (Q.adicCompletion K) ↥L ↥L _ _ _ _ _ algMm st
      inferInstance).hom x = x
  rw [hmain]
  rfl

/-- The inverse system of fundamental classes: at the level `L` the fibre is the set of generators
of `H²(Gal(L/F), Lˣ)`, and the transition along `L ≤ E` is the unique preimage of `[E:L] · u`. -/
noncomputable abbrev lvlFiber (X : (Lvl Q)ᵒᵖ) : Type := lvlGen Q X.unop

set_option maxHeartbeats 8000000 in
noncomputable def lvlFunctor : (Lvl Q)ᵒᵖ ⥤ Type :=
  { obj := lvlFiber (K := K) Q
    map := fun {X Y} f => TypeCat.ofHom (fun u => lvlTrans Q Y.unop X.unop (leOfHom f.unop) u)
    map_id := fun X => by
      ext u
      exact congrArg Subtype.val (lvlTrans_self Q X.unop (leOfHom (𝟙 X).unop) u)
    map_comp := fun {X Y Z} f g => by
      ext u
      exact congrArg Subtype.val
        (lvlTrans_comp Q Z.unop Y.unop X.unop (leOfHom g.unop) (leOfHom f.unop) u) }

theorem exists_compatible_fundamentalClasses {K : Type} [Field K] [NumberField K]
    (Q : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K)) :
    ∃ (u : (L : FiniteGaloisIntermediateField (Q.adicCompletion K)
            (NK.LocalReciprocity.maxAbelianSubext (Q.adicCompletion K)
              (SeparableClosure (Q.adicCompletion K)))) →
          groupCohomology (Rep.ofAlgebraAutOnUnits (Q.adicCompletion K) ↥L) 2)
      (_hu : ∀ L, addOrderOf (u L) = Nat.card (groupCohomology
        (Rep.ofAlgebraAutOnUnits (Q.adicCompletion K) ↥L) 2)),
      ∀ (L E : FiniteGaloisIntermediateField (Q.adicCompletion K)
          (NK.LocalReciprocity.maxAbelianSubext (Q.adicCompletion K)
            (SeparableClosure (Q.adicCompletion K)))) (h : L ≤ E),
        (NK.NUV2.RouteE.levelInfHom L E h) (u L)
          = ((Nat.card (↥E ≃ₐ[(Q.adicCompletion K)] ↥E)
              / Nat.card (↥L ≃ₐ[(Q.adicCompletion K)] ↥L) : ℕ) : ℤ) • (u E) := by
  classical
  haveI hfin : ∀ X : (Lvl Q)ᵒᵖ, Finite ((lvlFunctor (K := K) Q).obj X) := fun X => by
    show Finite (lvlGen Q X.unop)
    haveI := (lvlData Q X.unop).2.2
    infer_instance
  haveI hne : ∀ X : (Lvl Q)ᵒᵖ, Nonempty ((lvlFunctor (K := K) Q).obj X) := fun X => by
    show Nonempty (lvlGen Q X.unop)
    exact (lvlData Q X.unop).2.1
  obtain ⟨s, hs⟩ := nonempty_sections_of_finite_inverse_system (lvlFunctor (K := K) Q)
  refine ⟨fun L => (s (Opposite.op L)).1, fun L => (s (Opposite.op L)).2, ?_⟩
  intro L E h
  by_cases hLE : L = E
  · subst hLE
    rw [Nat.div_self (lvlDeg_pos Q L), Nat.cast_one, one_zsmul]
    exact levelInfHom_self (K := K) Q L h (s (Opposite.op L)).1
  · have hs' : lvlTrans Q L E h (s (Opposite.op E)) = s (Opposite.op L) :=
      hs (j := Opposite.op E) (j' := Opposite.op L) (homOfLE h).op
    have hspec := lvlTrans_spec (K := K) Q L E h hLE (s (Opposite.op E))
    rw [hs'] at hspec
    exact hspec

end NK.NUV2.RouteE
