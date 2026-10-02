import Mathlib
import Submission.Work.Serre.bijective_mixedCup_of_openCover_zero
import Submission.Work.StemsB.AToolsR
import Submission.Work.RatHurewicz.isZero_relCoh_of_isEmpty

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 400000

set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1600000
set_option linter.unusedVariables false
set_option linter.style.haveILetI false

open CategoryTheory CategoryTheory.Limits

/-!
# Degree-zero bijectivity of the cup map over a *disjoint* open cover

Let `X` be a topological space, `A ⊆ X`, and let `U, V` be **disjoint** open sets with
`U ∪ V = X` (so `X` is the disjoint union of the two clopen pieces `U` and `V`).  For a class
`U₀ ∈ H^{n₀}(X, A; ℚ)` with `n₀ ≥ 1`, suppose that the cup map

`x ↦ x ⌣ U₀ : H⁰(·; ℚ) ⟶ H^{n₀}(·, · ∩ A; ℚ)`

is bijective over `U` and over `V`.  Then it is bijective over `X`:

`Work.RatHurewicz.zero_bijective_mixedCup_of_disjoint_pair`.

This is the degree-zero case of the gluing argument for the cup map, but with the overlap
`U ∩ V = ∅`, which makes two of the hypotheses of the general statement
(`Work.Serre.bijective_mixedCup_of_openCover_zero`) *automatic*:

* the overlap term of the relative Mayer–Vietoris sequence vanishes in every degree, because
  `↥(U ∩ V)` is empty (`Work.RatHurewicz.isZero_relCoh_of_isEmpty`); this is exactly the vanishing
  hypothesis that `Work.Serre.ker_mvF_eq_bot` needs in order to make the restriction map
  `H^{n₀}(X,A) → H^{n₀}(U,U∩A) ⊞ H^{n₀}(V,V∩A)` injective;
* the compatibility condition "the two local solutions agree on `U ∩ V`" is automatic, since
  `H⁰(↥(U ∩ V); ℚ)` is a subsingleton.

So the proof is the positive-degree branch of the Mayer–Vietoris argument, cut down to the
disjoint case: a class of `H⁰(X;ℚ)` is determined by its restrictions to `U` and to `V`
(separation, `Work.Serre.h0_restrict_eq_zero_of_cover`), the restrictions of a `0`-class of `U`
and of `V` with the same `U ∩ V`-restriction are glued by a `0`-class of `X`
(`Work.Serre.exists_glue_coh_zero`), and the mixed cup product is natural
(`Work.StemsB.mixedCupC_pairNaturalR`).
-/

namespace Work.RatHurewicz

noncomputable section

open CategoryTheory CategoryTheory.Limits

theorem zero_bijective_mixedCup_of_disjoint_pair {X : Type} [TopologicalSpace X]
    (A U V : Set X) (hU : IsOpen U) (hV : IsOpen V) (hcov : U ∪ V = Set.univ)
    (hdisj : Disjoint U V) (n₀ : ℕ) (hn₀ : 0 < n₀) (U₀ : Work.Thom.RelCoh ℚ n₀ X A)
    (hlocU : Function.Bijective (fun x : Work.Thom.Coh ℚ 0 ↥U =>
      (Work.Thom.mixedCupC ℚ {y : ↥U | (y : X) ∈ A} 0 n₀) x
        ((Work.Thom.relCohMap (⟨Subtype.val, continuous_subtype_val⟩ : C(↥U, X))
          {y : ↥U | (y : X) ∈ A} A (fun _ hy => hy) ℚ n₀).hom U₀)))
    (hlocV : Function.Bijective (fun x : Work.Thom.Coh ℚ 0 ↥V =>
      (Work.Thom.mixedCupC ℚ {y : ↥V | (y : X) ∈ A} 0 n₀) x
        ((Work.Thom.relCohMap (⟨Subtype.val, continuous_subtype_val⟩ : C(↥V, X))
          {y : ↥V | (y : X) ∈ A} A (fun _ hy => hy) ℚ n₀).hom U₀))) :
    Function.Bijective (fun x : Work.Thom.Coh ℚ 0 X =>
      (Work.Thom.mixedCupC ℚ A 0 n₀) x U₀) := by
  classical
  have hn0 : 0 < 0 + n₀ := by omega
  -- ## the two pieces are disjoint, so the overlap is empty
  haveI hEmptyUV : IsEmpty ↥(U ∩ V) :=
    ⟨fun x => (hdisj inf_le_left inf_le_right : (U ∩ V : Set X) ≤ (⊥ : Set X)) x.2⟩
  haveI hsubCohUV : Subsingleton (Work.Thom.Coh ℚ 0 ↥(U ∩ V)) :=
    ModuleCat.subsingleton_of_isZero (Work.Serre.isZero_coh_of_isEmpty_space (Y := ↥(U ∩ V)) 0)
  haveI hsubRelUV : Subsingleton (Work.Serre.mvCohUV (TopCat.of X) A U V ((0 + n₀) - 1)) :=
    ModuleCat.subsingleton_of_isZero
      (Work.RatHurewicz.isZero_relCoh_of_isEmpty (S := U ∩ V) hEmptyUV
        {x : ↥(U ∩ V) | (x : X) ∈ A} ((0 + n₀) - 1))
  -- ## the notation
  let SU : Set ↥U := {y : ↥U | (y : X) ∈ A}
  let SV : Set ↥V := {y : ↥V | (y : X) ∈ A}
  let SUV : Set ↥(U ∩ V) := {y : ↥(U ∩ V) | (y : X) ∈ A}
  let ιU : C(↥U, X) := ⟨Subtype.val, continuous_subtype_val⟩
  let ιV : C(↥V, X) := ⟨Subtype.val, continuous_subtype_val⟩
  let ιUVU : C(↥(U ∩ V), ↥U) := ⟨fun x => ⟨x.1, x.2.1⟩, by continuity⟩
  let ιUVV : C(↥(U ∩ V), ↥V) := ⟨fun x => ⟨x.1, x.2.2⟩, by continuity⟩
  let hfU : ∀ x ∈ SU, ιU x ∈ A := fun _ hy => hy
  let hfV : ∀ x ∈ SV, ιV x ∈ A := fun _ hy => hy
  let hfUVU : ∀ x ∈ SUV, ιUVU x ∈ SU := fun _ hy => hy
  let hfUVV : ∀ x ∈ SUV, ιUVV x ∈ SV := fun _ hy => hy
  let rU : Work.Thom.Coh ℚ 0 X ⟶ Work.Thom.Coh ℚ 0 ↥U := Work.Thom.CohMap ιU ℚ 0
  let rV : Work.Thom.Coh ℚ 0 X ⟶ Work.Thom.Coh ℚ 0 ↥V := Work.Thom.CohMap ιV ℚ 0
  let rUVU : Work.Thom.Coh ℚ 0 ↥U ⟶ Work.Thom.Coh ℚ 0 ↥(U ∩ V) :=
    Work.Thom.CohMap ιUVU ℚ 0
  let rUVV : Work.Thom.Coh ℚ 0 ↥V ⟶ Work.Thom.Coh ℚ 0 ↥(U ∩ V) :=
    Work.Thom.CohMap ιUVV ℚ 0
  let mU : Work.Thom.RelCoh ℚ n₀ X A ⟶ Work.Thom.RelCoh ℚ n₀ ↥U SU :=
    Work.Thom.relCohMap ιU SU A hfU ℚ n₀
  let mV : Work.Thom.RelCoh ℚ n₀ X A ⟶ Work.Thom.RelCoh ℚ n₀ ↥V SV :=
    Work.Thom.relCohMap ιV SV A hfV ℚ n₀
  let mvRU : Work.Thom.RelCoh ℚ (0 + n₀) X A ⟶ Work.Thom.RelCoh ℚ (0 + n₀) ↥U SU :=
    Work.Serre.mvRestrU (TopCat.of X) A U (0 + n₀)
  let mvRV : Work.Thom.RelCoh ℚ (0 + n₀) X A ⟶ Work.Thom.RelCoh ℚ (0 + n₀) ↥V SV :=
    Work.Serre.mvRestrV (TopCat.of X) A V (0 + n₀)
  let φX : Work.Thom.Coh ℚ 0 X → Work.Thom.RelCoh ℚ (0 + n₀) X A :=
    fun x => (Work.Thom.mixedCupC ℚ A 0 n₀) x U₀
  let φU : Work.Thom.Coh ℚ 0 ↥U → Work.Thom.RelCoh ℚ (0 + n₀) ↥U SU :=
    fun x => (Work.Thom.mixedCupC ℚ SU 0 n₀) x (mU.hom U₀)
  let φV : Work.Thom.Coh ℚ 0 ↥V → Work.Thom.RelCoh ℚ (0 + n₀) ↥V SV :=
    fun x => (Work.Thom.mixedCupC ℚ SV 0 n₀) x (mV.hom U₀)
  have hlocU' : Function.Bijective φU := hlocU
  have hlocV' : Function.Bijective φV := hlocV
  -- ## naturality of the cup map
  have natU : ∀ z : Work.Thom.Coh ℚ 0 X, mvRU.hom (φX z) = φU (rU.hom z) :=
    fun z => Work.StemsB.mixedCupC_pairNaturalR ℚ ιU SU A hfU 0 n₀ z U₀
  have natV : ∀ z : Work.Thom.Coh ℚ 0 X, mvRV.hom (φX z) = φV (rV.hom z) :=
    fun z => Work.StemsB.mixedCupC_pairNaturalR ℚ ιV SV A hfV 0 n₀ z U₀
  -- ## injectivity
  have hinj : Function.Injective φX := by
    intro x y hxy
    have hU1 : φU (rU.hom x) = φU (rU.hom y) := by rw [← natU x, ← natU y, hxy]
    have hV1 : φV (rV.hom x) = φV (rV.hom y) := by rw [← natV x, ← natV y, hxy]
    have hxU : rU.hom x = rU.hom y := hlocU'.1 hU1
    have hxV : rV.hom x = rV.hom y := hlocV'.1 hV1
    have hzero : x - y = 0 := by
      refine Work.Serre.h0_restrict_eq_zero_of_cover hcov (x - y) ?_ ?_
      · rw [map_sub, hxU, sub_self]
      · rw [map_sub, hxV, sub_self]
    exact sub_eq_zero.mp hzero
  -- ## surjectivity
  have hsurj : Function.Surjective φX := by
    intro z
    obtain ⟨a, ha⟩ := hlocU'.2 (mvRU.hom z)
    obtain ⟨b, hb⟩ := hlocV'.2 (mvRV.hom z)
    -- the two local solutions are automatically compatible on the empty overlap
    have hcompat : rUVU.hom a = rUVV.hom b := Subsingleton.elim _ _
    obtain ⟨x, hx1, hx2⟩ := Work.Serre.exists_glue_coh_zero U V hU hV hcov a b hcompat
    refine ⟨x, ?_⟩
    have hz1 : mvRU.hom (φX x) = mvRU.hom z := by rw [natU x, hx1, ha]
    have hz2 : mvRV.hom (φX x) = mvRV.hom z := by rw [natV x, hx2, hb]
    have hlift : Work.Serre.mvF (TopCat.of X) A U V (0 + n₀) ≫
        (biprod.fst : Work.Thom.RelCoh ℚ (0 + n₀) ↥U SU ⊞
          Work.Thom.RelCoh ℚ (0 + n₀) ↥V SV ⟶ Work.Thom.RelCoh ℚ (0 + n₀) ↥U SU) = mvRU := by
      show biprod.lift (Work.Serre.mvRestrU (TopCat.of X) A U (0 + n₀))
          (Work.Serre.mvRestrV (TopCat.of X) A V (0 + n₀)) ≫ biprod.fst = mvRU
      rw [biprod.lift_fst]
    have hlift' : Work.Serre.mvF (TopCat.of X) A U V (0 + n₀) ≫
        (biprod.snd : Work.Thom.RelCoh ℚ (0 + n₀) ↥U SU ⊞
          Work.Thom.RelCoh ℚ (0 + n₀) ↥V SV ⟶ Work.Thom.RelCoh ℚ (0 + n₀) ↥V SV) = mvRV := by
      show biprod.lift (Work.Serre.mvRestrU (TopCat.of X) A U (0 + n₀))
          (Work.Serre.mvRestrV (TopCat.of X) A V (0 + n₀)) ≫ biprod.snd = mvRV
      rw [biprod.lift_snd]
    have hinjF : Function.Injective (Work.Serre.mvF (TopCat.of X) A U V (0 + n₀)).hom :=
      LinearMap.ker_eq_bot.mp
        (Work.Serre.ker_mvF_eq_bot A U V hU hV hcov (0 + n₀) hn0 hsubRelUV)
    have hsub : φX x - z = 0 := by
      refine hinjF ?_
      rw [map_zero]
      refine Work.Serre.biprod_eq_zero_of_fst_snd _ ?_ ?_
      · rw [← Work.Serre.comp_hom_apply (Work.Serre.mvF (TopCat.of X) A U V (0 + n₀))
            (biprod.fst : Work.Thom.RelCoh ℚ (0 + n₀) ↥U SU ⊞
              Work.Thom.RelCoh ℚ (0 + n₀) ↥V SV ⟶ Work.Thom.RelCoh ℚ (0 + n₀) ↥U SU)
            (φX x - z), hlift]
        rw [map_sub, hz1, sub_self]
      · rw [← Work.Serre.comp_hom_apply (Work.Serre.mvF (TopCat.of X) A U V (0 + n₀))
            (biprod.snd : Work.Thom.RelCoh ℚ (0 + n₀) ↥U SU ⊞
              Work.Thom.RelCoh ℚ (0 + n₀) ↥V SV ⟶ Work.Thom.RelCoh ℚ (0 + n₀) ↥V SV)
            (φX x - z), hlift']
        rw [map_sub, hz2, sub_self]
    exact sub_eq_zero.mp hsub
  exact ⟨hinj, hsurj⟩

end

end Work.RatHurewicz
