import Mathlib
import Submission.Work.Transgression.Reductions
import Submission.Work.Cohomology.exists_smul_oneH
import Submission.Work.Cohomology.CupRing

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 400000

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2000000
set_option linter.style.haveILetI false
set_option linter.unusedSectionVars false

/-!
# SUBPROJECT TRANSGRESSION: the Gysin reduction of the Euler-class statement

The Gysin sequence of the rank-`4` bundle `E = clutchBundle a b` over `S⁴` reads, in degrees
`0 → 4`,

  `H⁰(S⁴) --∪e--> H⁴(S⁴) --π_S^*--> H⁴(S(E)) --δ--> H¹(S⁴)`,

and in the model of `Submission/Work/Thom/Gysin.lean` the exactness statements are
`gysin_exact_at_base`, `gysin_exact_at_sphere` and the identification `gysinEuler_eq_cupEuler`.

This module uses them to prove that **the Euler class of `clutchBundle a b` is determined up to
sign by `H⁴` of the punctured total space**:

* `Work.Transgression.span_singleton_eq_top_iff'` — the "spanning" criterion for a `ℤ`-module,
  stated with the `zsmul` that `Work.Cohomology.exists_smul_oneH` produces (the two available
  `ℤ`-actions are identified by `int_smul_eq_zsmul`);
* `Work.Transgression.range_gysinEuler_span` — `range (∪e) = ℤ·e`;
* `Work.Transgression.subsingleton_openThom_five`, `Work.Transgression.surjective_gysinπ`;
* `Work.Transgression.PuncturedGysin` — `H⁴(S⁴)/⟨e⟩` is cyclic of order `|a+b|`;
* `Work.Transgression.EulerClutch_of_puncturedCoh` — the deliverable's item (3), modulo the single
  topological input `PuncturedCoh`.
-/

namespace Work.Transgression

open Work.TangentClasses CategoryTheory

noncomputable section

/-- The bundle of the chapter: `clutchBundle a b` over `S⁴ = OnePoint ℝ⁴`. -/
abbrev Zb (a b : ℤ) : RealBundle Work.Agree.S4 (EuclideanSpace ℝ (Fin 4)) Bool :=
  Work.Agree.clutchBundle a b

/-- The unit class of `H⁰(S⁴;ℤ)`, in the degree-`0` absolute cohomology of the base. -/
abbrev oneH4 : ↥(Work.Thom.Coh ℤ 0 Work.Agree.S4) :=
  Work.Cohomology.oneH ℤ (TopCat.toSSet.obj (TopCat.of Work.Agree.S4))

/-- **A `ℤ`-module is spanned by a single element iff every element is an integer multiple of it**
(with the `zsmul` that `Work.Cohomology.exists_smul_oneH` produces; the two available `ℤ`-scalar
multiplications on an abelian group are identified by `int_smul_eq_zsmul`). -/
lemma span_singleton_eq_top_iff' {M : Type*} [AddCommGroup M] [Module ℤ M] (x : M) :
    Submodule.span ℤ {x} = ⊤ ↔ ∀ z : M, ∃ a : ℤ, z = a • x := by
  have bridge : ∀ (a : ℤ), (LinearMap.toSpanSingleton ℤ M x) a = (a • x : M) := by
    intro a
    rw [LinearMap.toSpanSingleton_apply]
    exact int_smul_eq_zsmul (inferInstance : Module ℤ M) a x
  constructor
  · intro h z
    have hmem : z ∈ Submodule.span ℤ {x} := by rw [h]; trivial
    obtain ⟨a, ha⟩ := (Submodule.mem_span_singleton).mp hmem
    have ha' : (LinearMap.toSpanSingleton ℤ M x) a = z := by
      rw [LinearMap.toSpanSingleton_apply]; exact ha
    exact ⟨a, by rw [← ha', bridge]⟩
  · intro h
    rw [Submodule.eq_top_iff']
    intro z
    obtain ⟨a, ha⟩ := h z
    rw [ha, ← bridge a]
    exact Submodule.smul_mem _ a (Submodule.subset_span (Set.mem_singleton x))

/-- **The range of `∪e` is `ℤ·e`.**  `gysinEuler T 0` is multiplication by the Euler class on
`H⁰(S⁴;ℤ) = ℤ · oneH` (`Work.Cohomology.exists_smul_oneH`), and `oneH ⌣ e = e`. -/
theorem range_gysinEuler_span (a b : ℤ)
    (T : Work.Thom.ThomClass (Zb a b) 4) :
    LinearMap.range (Work.Thom.gysinEuler T 0) = Submodule.span ℤ {T.eulerClass} := by
  have hone : Work.Thom.gysinEuler T 0 oneH4 = T.eulerClass :=
    (Work.Thom.gysinEuler_eq_cupEuler T 0 oneH4).trans (by
      simpa using (Work.Cohomology.cupH'_one_left (R := ℤ)
        (X := TopCat.toSSet.obj (TopCat.of Work.Agree.S4)) 4 T.eulerClass))
  have htop : Submodule.span ℤ {oneH4} = ⊤ :=
    (span_singleton_eq_top_iff' oneH4).mpr (fun z => by
      obtain ⟨m, hm⟩ := Work.Cohomology.exists_smul_oneH (TopCat.of Work.Agree.S4) z
      exact ⟨m, hm⟩)
  have hmap : Submodule.map (Work.Thom.gysinEuler T 0) (Submodule.span ℤ {oneH4})
      = Submodule.span ℤ {T.eulerClass} := by
    rw [Submodule.map_span, Set.image_singleton, hone]
  calc LinearMap.range (Work.Thom.gysinEuler T 0)
      = Submodule.map (Work.Thom.gysinEuler T 0) ⊤ := (Submodule.map_top _).symm
    _ = Submodule.map (Work.Thom.gysinEuler T 0) (Submodule.span ℤ {oneH4}) := by rw [htop]
    _ = Submodule.span ℤ {T.eulerClass} := hmap

/-- `H⁵` of the Thom pair of `clutchBundle a b` vanishes: by the Thom isomorphism it is `H¹(S⁴;ℤ)`,
which vanishes (`Work.Agree.subsingleton_cohomology_S4_one`). -/
theorem subsingleton_openThom_five (a b : ℤ) (T : Work.Thom.ThomClass (Zb a b) 4) :
    Subsingleton ↥(Work.Thom.OpenThom (Zb a b) 5) := by
  haveI := Work.Agree.subsingleton_cohomology_S4_one
  exact Function.Surjective.subsingleton (T.thomEquiv 1).surjective

/-- **`π_S^*` is onto.**  Its cokernel is the kernel of the connecting map
`pairδC (zeroComplement Z) 4 : H⁴(S(E)) → H⁵(E,E∖0) = OpenThom Z 5 = 0`, which is therefore
zero. -/
theorem surjective_gysinπ (a b : ℤ) (T : Work.Thom.ThomClass (Zb a b) 4) :
    Function.Surjective (Work.Thom.gysinπ (Zb a b) 4) := by
  haveI := subsingleton_openThom_five a b T
  have hδ : (Work.Thom.pairδC (Work.Thom.zeroComplement (Zb a b)) 4).hom = 0 :=
    LinearMap.ext (fun z => Subsingleton.elim _ _)
  have hrange : Set.range (Work.Thom.gysinπ (Zb a b) 4) = Set.univ := by
    rw [Work.Thom.gysin_exact_at_sphere T 0]
    ext z
    simp [hδ]
  intro y
  have : y ∈ Set.range (Work.Thom.gysinπ (Zb a b) 4) := by
    rw [hrange]; exact Set.mem_univ y
  exact this

/-- `PuncturedCoh` implies its cardinality form. -/
theorem PuncturedCohCard_of_PuncturedCoh {a b : ℤ} (h : PuncturedCoh a b) :
    PuncturedCohCard a b := by
  obtain ⟨h⟩ := h
  rw [PuncturedCohCard, Nat.card_congr h.toEquiv, Nat.card_zmod]

/-- **THE GYSIN CHAIN.**  The quotient of `H⁴(S⁴;ℤ)` by the subgroup generated by the Euler class
of a Thom class `T` has the same number of elements as `H⁴` of the punctured total space (the
Gysin sequence: exactness at the base and the vanishing of `H⁵` of the Thom pair). -/
theorem card_quot_span_euler_eq_punctured (a b : ℤ) (T : Work.Thom.ThomClass (Zb a b) 4) :
    Nat.card (↥(Work.Thom.Coh ℤ 4 Work.Agree.S4) ⧸ Submodule.span ℤ {T.eulerClass})
      = Nat.card ↥(Work.Thom.Coh ℤ 4 ↥(Work.Thom.zeroComplement (Zb a b))) := by
  have h2 : LinearMap.ker (Work.Thom.gysinπ (Zb a b) 4)
      = LinearMap.range (Work.Thom.gysinEuler T 0) := by
    have hmem : ∀ z, z ∈ Set.range (⇑(Work.Thom.gysinEuler T 0))
        ↔ (Work.Thom.gysinπ (Zb a b) 4) z = 0 := by
      intro z
      rw [Work.Thom.gysin_exact_at_base T 0]
      exact Iff.rfl
    ext x
    simp only [LinearMap.mem_ker, LinearMap.mem_range]
    exact (hmem x).symm
  have hker : LinearMap.ker (Work.Thom.gysinπ (Zb a b) 4)
      = Submodule.span ℤ {T.eulerClass} := by
    rw [h2, range_gysinEuler_span a b T]
  have hsurj : Function.Surjective (Work.Thom.gysinπ (Zb a b) 4) := surjective_gysinπ a b T
  have hrange : LinearMap.range (Work.Thom.gysinπ (Zb a b) 4) = ⊤ :=
    LinearMap.range_eq_top.mpr hsurj
  have hchain : Nat.card (↥(Work.Thom.Coh ℤ 4 Work.Agree.S4)
        ⧸ Submodule.span ℤ {T.eulerClass})
      = Nat.card ↥(Work.Thom.Coh ℤ 4 ↥(Work.Thom.zeroComplement (Zb a b))) := by
    have h1 := Nat.card_congr (Submodule.quotEquivOfEq (Submodule.span ℤ {T.eulerClass})
      (LinearMap.ker (Work.Thom.gysinπ (Zb a b) 4)) hker.symm).toEquiv
    have h2' := Nat.card_congr
      (LinearMap.quotKerEquivRange (Work.Thom.gysinπ (Zb a b) 4)).toEquiv
    have h3 := Nat.card_congr (LinearEquiv.ofEq
      (LinearMap.range (Work.Thom.gysinπ (Zb a b) 4)) ⊤ hrange).toEquiv
    have h4 := Nat.card_congr (Submodule.topEquiv (R := ℤ)
      (M := ↥(Work.Thom.Coh ℤ 4 ↥(Work.Thom.zeroComplement (Zb a b))))).toEquiv
    exact h1.trans (h2'.trans (h3.trans h4))
  exact hchain

/-- **THE GYSIN REDUCTION.**  If `H⁴` of the punctured total space of `clutchBundle a b` is cyclic
of order `|a + b|` (`Work.Transgression.PuncturedCoh`), then for every Thom class `T` the quotient
of `H⁴(S⁴;ℤ)` by the subgroup generated by the Euler class has `|a + b|` elements. -/
theorem PuncturedGysin (a b : ℤ) (h : PuncturedCoh a b)
    (T : Work.Thom.ThomClass (Zb a b) 4) :
    Nat.card (↥(Work.Thom.Coh ℤ 4 Work.Agree.S4) ⧸ Submodule.span ℤ {T.eulerClass})
      = Int.natAbs (a + b) :=
  (card_quot_span_euler_eq_punctured a b T).trans (PuncturedCohCard_of_PuncturedCoh h)

/-- **The Gysin reduction, cardinality form.**  It is enough to know the *number of elements* of
`H⁴` of the punctured total space (no group-structure statement is needed). -/
theorem PuncturedGysinCard (a b : ℤ) (h : PuncturedCohCard a b)
    (T : Work.Thom.ThomClass (Zb a b) 4) :
    Nat.card (↥(Work.Thom.Coh ℤ 4 Work.Agree.S4) ⧸ Submodule.span ℤ {T.eulerClass})
      = Int.natAbs (a + b) :=
  (card_quot_span_euler_eq_punctured a b T).trans h

/-! ## The assembly: the deliverable modulo the topological input -/

/-- The signed value of `|n|` in `ℤ`. -/
lemma natAbs_cast_eq (n : ℤ) : ((n.natAbs : ℤ) = n) ∨ ((n.natAbs : ℤ) = -n) := by
  rcases Int.natAbs_eq n with h | h
  · exact Or.inl h.symm
  · exact Or.inr (by rw [h, Int.natAbs_neg, Int.natAbs_natCast, neg_neg])

/-- **The Euler-class statement in generator form**, from the punctured-cohomology input (in its
cardinality form): for every `a b` and every Thom class `T` of `clutchBundle a b`,
`T.eulerClass = ± (a+b) · G4`. -/
theorem EulerClutchGen_of_puncturedCohCard (H : ∀ a b, PuncturedCohCard a b) : EulerClutchGen := by
  intro a b T
  have hcard := PuncturedGysinCard a b (H a b) T
  have hcases := QuotSpanCard H4S4Iso.toLinearEquiv T.eulerClass (Int.natAbs (a + b)) hcard
  have h1 : T.eulerClass = (H4S4Iso.toLinearEquiv T.eulerClass) • G4 := by
    show T.eulerClass = (ModuleCat.Hom.hom H4S4Iso.hom T.eulerClass) • G4
    exact smul_G4 T.eulerClass
  have hcase : (H4S4Iso.toLinearEquiv T.eulerClass = (a + b)) ∨
      (H4S4Iso.toLinearEquiv T.eulerClass = -(a + b)) := by
    rcases hcases with hc | hc <;> rcases natAbs_cast_eq (a + b) with hab | hab
    · exact Or.inl (by rw [hc, hab])
    · exact Or.inr (by rw [hc, hab])
    · exact Or.inr (by rw [hc, hab])
    · exact Or.inl (by rw [hc, hab, neg_neg])
  rcases hcase with hc | hc
  · left;  rw [h1, hc]
  · right; rw [h1, hc, neg_zsmul]

/-- **The generator form from the topological input** (the group-structure form). -/
theorem EulerClutchGen_of_puncturedCoh (H : ∀ a b, PuncturedCoh a b) : EulerClutchGen :=
  EulerClutchGen_of_puncturedCohCard fun a b => PuncturedCohCard_of_PuncturedCoh (H a b)

/-- **The generator form implies the deliverable.**  `Work.Agree.EulerClutch` is the pullback of
`EulerClutchGen` along the bundle projection `π = discProj`: `EulerClutchGen` says
`T.eulerClass = ± (a+b) · G4`, and `π^*(G4) = ± tauD` (`Work.Transgression.PiStarGen`). -/
theorem EulerClutch_of_EulerClutchGen (hgen : EulerClutchGen) : Work.Agree.EulerClutch := by
  have hgen4 : ∀ z : Work.Thom.Coh ℤ 4 Work.Agree.S4, ∃ c : ℤ, z = c • G4 :=
    fun z => ⟨H4S4Iso.toLinearEquiv z, smul_G4 z⟩
  have hpull := PiStarGen G4 hgen4
  intro a b T
  rcases hgen a b T with h | h <;> rcases hpull with hp | hp
  · left
    calc (Work.TangentClasses.HMap Work.TangentClasses.discProj 4).hom T.eulerClass
        = (Work.TangentClasses.HMap Work.TangentClasses.discProj 4).hom ((a + b) • G4) := by rw [h]
      _ = (a + b) • ((Work.TangentClasses.HMap Work.TangentClasses.discProj 4).hom G4) :=
          by rw [map_zsmul]
      _ = (a + b) • Work.Milnor.tauD := by rw [hp]
  · right
    calc (Work.TangentClasses.HMap Work.TangentClasses.discProj 4).hom T.eulerClass
        = (Work.TangentClasses.HMap Work.TangentClasses.discProj 4).hom ((a + b) • G4) := by rw [h]
      _ = (a + b) • ((Work.TangentClasses.HMap Work.TangentClasses.discProj 4).hom G4) :=
          by rw [map_zsmul]
      _ = (a + b) • (-Work.Milnor.tauD) := by rw [hp]
      _ = -((a + b) • Work.Milnor.tauD) := by rw [zsmul_neg]
  · right
    calc (Work.TangentClasses.HMap Work.TangentClasses.discProj 4).hom T.eulerClass
        = (Work.TangentClasses.HMap Work.TangentClasses.discProj 4).hom (-((a + b) • G4)) :=
          by rw [h]
      _ = -((Work.TangentClasses.HMap Work.TangentClasses.discProj 4).hom ((a + b) • G4)) :=
          by rw [map_neg]
      _ = -((a + b) • ((Work.TangentClasses.HMap Work.TangentClasses.discProj 4).hom G4)) :=
          by rw [map_zsmul]
      _ = -((a + b) • Work.Milnor.tauD) := by rw [hp]
  · left
    calc (Work.TangentClasses.HMap Work.TangentClasses.discProj 4).hom T.eulerClass
        = (Work.TangentClasses.HMap Work.TangentClasses.discProj 4).hom (-((a + b) • G4)) :=
          by rw [h]
      _ = -((Work.TangentClasses.HMap Work.TangentClasses.discProj 4).hom ((a + b) • G4)) :=
          by rw [map_neg]
      _ = -((a + b) • ((Work.TangentClasses.HMap Work.TangentClasses.discProj 4).hom G4)) :=
          by rw [map_zsmul]
      _ = -((a + b) • (-Work.Milnor.tauD)) := by rw [hp]
      _ = (a + b) • Work.Milnor.tauD := by rw [zsmul_neg, neg_neg]

/-- **THE DELIVERABLE, modulo the single topological input.**  `Work.Agree.EulerClutch` follows
from `PuncturedCoh` (the Mayer–Vietoris computation of `H⁴` of the punctured total space of
`clutchBundle a b`), through the Gysin sequence and the pullback of a generator along the bundle
projection. -/
theorem EulerClutch_of_puncturedCoh (H : ∀ a b, PuncturedCoh a b) : Work.Agree.EulerClutch :=
  EulerClutch_of_EulerClutchGen (EulerClutchGen_of_puncturedCoh H)

/-- **THE DELIVERABLE FROM THE CARDINALITY FORM OF THE TOPOLOGICAL INPUT.** -/
theorem EulerClutch_of_puncturedCohCard (H : ∀ a b, PuncturedCohCard a b) :
    Work.Agree.EulerClutch :=
  EulerClutch_of_EulerClutchGen (EulerClutchGen_of_puncturedCohCard H)

end

end Work.Transgression
