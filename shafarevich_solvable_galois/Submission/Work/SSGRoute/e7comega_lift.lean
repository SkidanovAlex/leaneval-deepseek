import Mathlib.Combinatorics.Quiver.ReflQuiver
import Mathlib.RepresentationTheory.Rep.Res
import Mathlib.NumberTheory.NumberField.InfinitePlace.Basic
import Mathlib.RingTheory.DedekindDomain.Ideal.Lemmas
import Mathlib.Algebra.Homology.DerivedCategory.Ext.ExactSequences
import Mathlib.Algebra.Homology.DerivedCategory.Ext.Map
import Submission.Work.SSGRoute.classLocIncl_injective_clean
import Submission.Work.SSGRoute.exists_orbit_supported_inclusion
import Submission.Work.SSGRoute.extH_classesK_two_card
import Submission.Work.SSGRoute.extToIdeles_eq_zero_iff_extLoc
import Submission.Work.SSGRoute.natCard_extH_orbitSupportedRep_inf
import Submission.Work.SSGRoute.ptorsion_mem_of_card
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# Orbit-supported lifts of `p`-torsion classes of `H²(Gal(L/k), C_L)` — self-contained copy

This is a verbatim port of `Submission/Work/SSGRoute/exists_classLoc_lift_ptorsion.lean` and
`.../exists_classLoc_lift_ptorsion_any.lean` into one module that avoids the import of
`Submission.Work.SSGRoute.classLocIncl_injective` (whose dependency
`Submission.Work.SSGRoute.localField_subfield_place_compat` is currently unbuildable).  The only
change is the use of `Work.SSGRoute.classLocIncl_extLoc_extToIdeles_eq` from the clean module
`Submission.Work.SSGRoute.classLocIncl_injective_clean`.
-/

namespace Work.SSGRoute.SSG

open SSGRoute.PTExt CategoryTheory

set_option maxHeartbeats 1600000
open SSGRoute.PTExt CategoryTheory

set_option maxHeartbeats 1600000

/-! ## Helpers for the assembly -/

/-- Postcomposition with `mk₀ H` is an additive map on `Ext`-cohomology. -/
noncomputable def extPostComp {G : Type} [Group G] {A B : Rep.{0} Coeff G} {n : ℕ}
    (H : A ⟶ B) : extH A n →+ extH B n where
  toFun y := y.comp (Abelian.Ext.mk₀ H) (add_zero n)
  map_zero' := Abelian.Ext.zero_comp _ _ _ _ (add_zero n)
  map_add' y y' := Abelian.Ext.add_comp y y' (Abelian.Ext.mk₀ H) (add_zero n)

@[simp] theorem extPostComp_apply {G : Type} [Group G] {A B : Rep.{0} Coeff G} {n : ℕ}
    (H : A ⟶ B) (y : extH A n) :
    extPostComp H y = y.comp (Abelian.Ext.mk₀ H) (add_zero n) := rfl

/-- **A class of `H²(Gal(L/k), 𝕀_L)` supported away from the orbit of `w₀` and killed by the
push-forward to the idèle class group is zero** (Hasse–Brauer–Noether at a single place, plus the
exactness of the class formation `0 → Lˣ → 𝕀_L → C_L → 0`). -/
theorem extToClasses_eq_zero_of_locTrivial (k L : Type) [Field k] [NumberField k] [Field L]
    [NumberField L] [Algebra k L] [FiniteDimensional k L] [IsGalois k L]
    (w₀ : NK.GlobalCFT.Place L) (q : extH (idelesK k L) 2)
    (hq : ∀ w : NK.GlobalCFT.Place L, (∀ σ : L ≃ₐ[k] L, σ • w₀ ≠ w) → extLoc w q = 0)
    (h : q.comp (Abelian.Ext.mk₀ (NK.HassePrinciple.classGroupMap k L)) (add_zero 2) = 0) :
    q = 0 := by
  have hS : (sesK k L).ShortExact := NK.HassePrinciple.ideleShortComplex_shortExact k L
  have hex : ∃ a : extH (unitsK k L) 2, extToIdeles (k := k) a = q := by
    obtain ⟨a, ha⟩ := Abelian.Ext.covariant_sequence_exact₂ (unitRep (L ≃ₐ[k] L)) hS q h
    exact ⟨a, ha⟩
  obtain ⟨a, ha⟩ := hex
  have ha0 : a = 0 := by
    refine ext_units_single_place k L a w₀ (fun w hw => ?_)
    rw [← classLocIncl_extLoc_extToIdeles_eq (k := k) (L := L) a w, ha]
    exact hq w hw
  rw [← ha, ha0]
  simp [extToIdeles]

/-- Postcomposition with `mk₀` of a morphism having a left inverse is injective. -/
theorem extPostComp_injective {G : Type} [Group G] {A B : Rep.{0} Coeff G} {n : ℕ}
    (H : A ⟶ B) (r : B ⟶ A) (hr : H ≫ r = 𝟙 A) :
    Function.Injective (extPostComp H : extH A n → extH B n) := by
  intro y y' hyy
  have key : ∀ z : extH A n, z = (extPostComp H z).comp (Abelian.Ext.mk₀ r) (add_zero n) := by
    intro z
    have h1 : (extPostComp H z).comp (Abelian.Ext.mk₀ r) (add_zero n) = z := by
      rw [extPostComp_apply, Abelian.Ext.comp_assoc_of_second_deg_zero z (Abelian.Ext.mk₀ H)
        (Abelian.Ext.mk₀ r) (add_zero n), Abelian.Ext.mk₀_comp_mk₀, hr,
        Abelian.Ext.comp_mk₀_id]
    exact h1.symm
  calc y = (extPostComp H y).comp (Abelian.Ext.mk₀ r) (add_zero n) := key y
    _ = (extPostComp H y').comp (Abelian.Ext.mk₀ r) (add_zero n) := by rw [hyy]
    _ = y' := (key y').symm


theorem exists_classLoc_lift_ptorsion (p : ℕ) [Fact p.Prime] (k L : Type) [Field k] [NumberField k]
    [Field L] [NumberField L] [Algebra k L] [FiniteDimensional k L] [IsGalois k L]
    (ŵ₀ : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers L))
    (hp : p ∣ Nat.card (MulAction.stabilizer (L ≃ₐ[k] L) (NK.GlobalCFT.Place.ofFinite ŵ₀)))
    (x : extH (classesK k L) 2) (hx : p • x = 0) :
    ∃ q : extH (idelesK k L) 2, p • q = 0 ∧
      (∀ w : NK.GlobalCFT.Place L,
        (∀ σ : L ≃ₐ[k] L, σ • NK.GlobalCFT.Place.ofFinite ŵ₀ ≠ w) →
          extLoc (k := k) (K := L) w q = 0) ∧
      q.comp (Abelian.Ext.mk₀ (NK.HassePrinciple.classGroupMap k L)) (add_zero 2) = x := by
  classical
  -- **Step 1.** the orbit-supported inclusion of the idèles, with its left inverse
  have hIncl := exists_orbit_supported_inclusion k L (NK.GlobalCFT.Place.ofFinite ŵ₀)
  unfold HasOrbitSupportedInclusion at hIncl
  obtain ⟨H, hHsupp, r, hr⟩ := hIncl
  -- **Step 2.** the order of the second `Ext` of the orbit-supported module
  have hcard := natCard_extH_orbitSupportedRep k L ŵ₀
  unfold CardOrbitSupportedRep at hcard
  -- **Step 3.** the two maps `Θ` and `Ψ = ρ ∘ Θ`
  set Ψ : extH (orbitSupportedRep k L (NK.GlobalCFT.Place.ofFinite ŵ₀)) 2 →+
      extH (classesK k L) 2 :=
    (extPostComp (NK.HassePrinciple.classGroupMap k L)).comp (extPostComp H) with hΨ
  have hΘinj : Function.Injective (extPostComp H : extH
      (orbitSupportedRep k L (NK.GlobalCFT.Place.ofFinite ŵ₀)) 2 → extH (idelesK k L) 2) :=
    extPostComp_injective H r hr
  -- **Step 4.** the localisation of `Θ z` vanishes away from the orbit of `w₀`
  have hsupp : ∀ (z : extH (orbitSupportedRep k L (NK.GlobalCFT.Place.ofFinite ŵ₀)) 2)
      (w : NK.GlobalCFT.Place L),
      (∀ σ : L ≃ₐ[k] L, σ • NK.GlobalCFT.Place.ofFinite ŵ₀ ≠ w) →
      extLoc (k := k) (K := L) w (extPostComp H z) = 0 := by
    intro z w hw
    have hsup := hHsupp w hw
    rw [extPostComp_apply]
    show (extRes (decompK (k := k) (K := L) w).subtype
        (z.comp (Abelian.Ext.mk₀ H) (add_zero 2))).comp
      (Abelian.Ext.mk₀ (NK.HassePrinciple.ideleToLocalUnits k L w)) (add_zero 2) = 0
    rw [extRes, Abelian.Ext.mapExactFunctor_comp, Abelian.Ext.mapExactFunctor_mk₀]
    rw [Abelian.Ext.comp_assoc_of_second_deg_zero, Abelian.Ext.mk₀_comp_mk₀, hsup,
      Abelian.Ext.mk₀_zero, Abelian.Ext.comp_zero]
  -- **Step 5.** `Ψ` is injective: its kernel consists of classes supported off the orbit and
  -- killed by the push-forward to the class group, which are zero by Hasse–Brauer–Noether
  have hker : ∀ z : extH (orbitSupportedRep k L (NK.GlobalCFT.Place.ofFinite ŵ₀)) 2,
      Ψ z = 0 → z = 0 := by
    intro z hz
    have h1 : (extPostComp H z).comp
        (Abelian.Ext.mk₀ (NK.HassePrinciple.classGroupMap k L)) (add_zero 2) = 0 := by
      have h2 : (extPostComp H z).comp
          (Abelian.Ext.mk₀ (NK.HassePrinciple.classGroupMap k L)) (add_zero 2)
          = (extPostComp (NK.HassePrinciple.classGroupMap k L)) (extPostComp H z) :=
        (extPostComp_apply (NK.HassePrinciple.classGroupMap k L) (extPostComp H z)).symm
      rw [h2, ← AddMonoidHom.comp_apply, ← hΨ]
      exact hz
    have hq0 : extPostComp H z = 0 :=
      extToClasses_eq_zero_of_locTrivial k L (NK.GlobalCFT.Place.ofFinite ŵ₀) (extPostComp H z)
        (fun w hw => hsupp z w hw) h1
    exact hΘinj (by rw [map_zero, hq0])
  have hΨinj : Function.Injective Ψ := by
    intro y y' hyy
    have h0 : Ψ (y - y') = 0 := by rw [map_sub, hyy, sub_self]
    exact sub_eq_zero.mp (hker (y - y') h0)
  -- **Step 6.** the `p`-torsion of the cyclic group `H²(Gal(L/k), C_L)` lies in the image of `Ψ`
  obtain ⟨u, hu⟩ := extH_classesK_two_fundamental k L
  have hB : Nat.card (extH (classesK k L) 2) = Nat.card (L ≃ₐ[k] L) := extH_classesK_two_card k L
  have hu' : addOrderOf u = Nat.card (extH (classesK k L) 2) := by rw [hB]; exact hu
  have hrange : Nat.card Ψ.range = Nat.card (extH
      (orbitSupportedRep k L (NK.GlobalCFT.Place.ofFinite ŵ₀)) 2) := by
    show Nat.card (Set.range Ψ) = _
    exact (Nat.card_congr (Equiv.ofInjective Ψ hΨinj)).symm
  have hH : Nat.card Ψ.range
      = Nat.card (MulAction.stabilizer (L ≃ₐ[k] L) (NK.GlobalCFT.Place.ofFinite ŵ₀)) := by
    rw [hrange, hcard]
  have hdvd : Nat.card (MulAction.stabilizer (L ≃ₐ[k] L) (NK.GlobalCFT.Place.ofFinite ŵ₀))
      ∣ Nat.card (extH (classesK k L) 2) := by
    rw [hB]
    exact Subgroup.card_subgroup_dvd_card _
  haveI : Finite (extH (classesK k L) 2) :=
    Nat.finite_of_card_ne_zero (by rw [hB]; exact Nat.card_ne_zero.mpr ⟨⟨1⟩, inferInstance⟩)
  have hxmem : x ∈ Ψ.range := ptorsion_mem_of_card u hu' Ψ.range hH hdvd hp x hx
  obtain ⟨y, hy⟩ := (AddMonoidHom.mem_range).mp hxmem
  -- **Step 7.** the lift
  refine ⟨extPostComp H y, ?_, ?_, ?_⟩
  · have hy0 : p • y = 0 := by
      apply hΨinj
      rw [map_nsmul, hy, hx, map_zero]
    rw [← map_nsmul, hy0, map_zero]
  · intro w hw
    exact hsupp y w hw
  · have h2 : (extPostComp (NK.HassePrinciple.classGroupMap k L)) (extPostComp H y) = x := by
      rw [← AddMonoidHom.comp_apply, ← hΨ]
      exact hy
    rw [← extPostComp_apply]
    exact h2


open SSGRoute.PTExt CategoryTheory

set_option maxHeartbeats 1600000

/-- **The assembly, for an arbitrary place `w₀` of `L`, given the order of
`H²(Gal(L/k), W)` for `W = orbitSupportedRep k L w₀`.**

Same argument as `Work.SSGRoute.exists_classLoc_lift_ptorsion`, with the single place-dependent
input `Nat.card (extH W 2) = Nat.card (Stab w₀)` kept as a hypothesis. -/
theorem exists_classLoc_lift_ptorsion_of_card (p : ℕ) [Fact p.Prime] (k L : Type) [Field k]
    [NumberField k] [Field L] [NumberField L] [Algebra k L] [FiniteDimensional k L]
    [IsGalois k L] (w₀ : NK.GlobalCFT.Place L)
    (hcard : Nat.card (extH (orbitSupportedRep k L w₀) 2)
      = Nat.card (MulAction.stabilizer (L ≃ₐ[k] L) w₀))
    (hp : p ∣ Nat.card (MulAction.stabilizer (L ≃ₐ[k] L) w₀))
    (x : extH (classesK k L) 2) (hx : p • x = 0) :
    ∃ q : extH (idelesK k L) 2, p • q = 0 ∧
      (∀ w : NK.GlobalCFT.Place L,
        (∀ σ : L ≃ₐ[k] L, σ • w₀ ≠ w) →
          extLoc (k := k) (K := L) w q = 0) ∧
      q.comp (Abelian.Ext.mk₀ (NK.HassePrinciple.classGroupMap k L)) (add_zero 2) = x := by
  classical
  -- **Step 1.** the orbit-supported inclusion of the idèles, with its left inverse
  have hIncl := exists_orbit_supported_inclusion k L w₀
  unfold HasOrbitSupportedInclusion at hIncl
  obtain ⟨H, hHsupp, r, hr⟩ := hIncl
  -- **Step 3.** the two maps `Θ` and `Ψ = ρ ∘ Θ`
  set Ψ : extH (orbitSupportedRep k L w₀) 2 →+
      extH (classesK k L) 2 :=
    (extPostComp (NK.HassePrinciple.classGroupMap k L)).comp (extPostComp H) with hΨ
  have hΘinj : Function.Injective (extPostComp H : extH
      (orbitSupportedRep k L w₀) 2 → extH (idelesK k L) 2) :=
    extPostComp_injective H r hr
  -- **Step 4.** the localisation of `Θ z` vanishes away from the orbit of `w₀`
  have hsupp : ∀ (z : extH (orbitSupportedRep k L w₀) 2)
      (w : NK.GlobalCFT.Place L),
      (∀ σ : L ≃ₐ[k] L, σ • w₀ ≠ w) →
      extLoc (k := k) (K := L) w (extPostComp H z) = 0 := by
    intro z w hw
    have hsup := hHsupp w hw
    rw [extPostComp_apply]
    show (extRes (decompK (k := k) (K := L) w).subtype
        (z.comp (Abelian.Ext.mk₀ H) (add_zero 2))).comp
      (Abelian.Ext.mk₀ (NK.HassePrinciple.ideleToLocalUnits k L w)) (add_zero 2) = 0
    rw [extRes, Abelian.Ext.mapExactFunctor_comp, Abelian.Ext.mapExactFunctor_mk₀]
    rw [Abelian.Ext.comp_assoc_of_second_deg_zero, Abelian.Ext.mk₀_comp_mk₀, hsup,
      Abelian.Ext.mk₀_zero, Abelian.Ext.comp_zero]
  -- **Step 5.** `Ψ` is injective: its kernel consists of classes supported off the orbit and
  -- killed by the push-forward to the class group, which are zero by Hasse–Brauer–Noether
  have hker : ∀ z : extH (orbitSupportedRep k L w₀) 2,
      Ψ z = 0 → z = 0 := by
    intro z hz
    have h1 : (extPostComp H z).comp
        (Abelian.Ext.mk₀ (NK.HassePrinciple.classGroupMap k L)) (add_zero 2) = 0 := by
      have h2 : (extPostComp H z).comp
          (Abelian.Ext.mk₀ (NK.HassePrinciple.classGroupMap k L)) (add_zero 2)
          = (extPostComp (NK.HassePrinciple.classGroupMap k L)) (extPostComp H z) :=
        (extPostComp_apply (NK.HassePrinciple.classGroupMap k L) (extPostComp H z)).symm
      rw [h2, ← AddMonoidHom.comp_apply, ← hΨ]
      exact hz
    have hq0 : extPostComp H z = 0 :=
      extToClasses_eq_zero_of_locTrivial k L w₀ (extPostComp H z)
        (fun w hw => hsupp z w hw) h1
    exact hΘinj (by rw [map_zero, hq0])
  have hΨinj : Function.Injective Ψ := by
    intro y y' hyy
    have h0 : Ψ (y - y') = 0 := by rw [map_sub, hyy, sub_self]
    exact sub_eq_zero.mp (hker (y - y') h0)
  -- **Step 6.** the `p`-torsion of the cyclic group `H²(Gal(L/k), C_L)` lies in the image of `Ψ`
  obtain ⟨u, hu⟩ := extH_classesK_two_fundamental k L
  have hB : Nat.card (extH (classesK k L) 2) = Nat.card (L ≃ₐ[k] L) := extH_classesK_two_card k L
  have hu' : addOrderOf u = Nat.card (extH (classesK k L) 2) := by rw [hB]; exact hu
  have hrange : Nat.card Ψ.range = Nat.card (extH
      (orbitSupportedRep k L w₀) 2) := by
    show Nat.card (Set.range Ψ) = _
    exact (Nat.card_congr (Equiv.ofInjective Ψ hΨinj)).symm
  have hH : Nat.card Ψ.range
      = Nat.card (MulAction.stabilizer (L ≃ₐ[k] L) w₀) := by
    rw [hrange, hcard]
  have hdvd : Nat.card (MulAction.stabilizer (L ≃ₐ[k] L) w₀)
      ∣ Nat.card (extH (classesK k L) 2) := by
    rw [hB]
    exact Subgroup.card_subgroup_dvd_card _
  haveI : Finite (extH (classesK k L) 2) :=
    Nat.finite_of_card_ne_zero (by rw [hB]; exact Nat.card_ne_zero.mpr ⟨⟨1⟩, inferInstance⟩)
  have hxmem : x ∈ Ψ.range := ptorsion_mem_of_card u hu' Ψ.range hH hdvd hp x hx
  obtain ⟨y, hy⟩ := (AddMonoidHom.mem_range).mp hxmem
  -- **Step 7.** the lift
  refine ⟨extPostComp H y, ?_, ?_, ?_⟩
  · have hy0 : p • y = 0 := by
      apply hΨinj
      rw [map_nsmul, hy, hx, map_zero]
    rw [← map_nsmul, hy0, map_zero]
  · intro w hw
    exact hsupp y w hw
  · have h2 : (extPostComp (NK.HassePrinciple.classGroupMap k L)) (extPostComp H y) = x := by
      rw [← AddMonoidHom.comp_apply, ← hΨ]
      exact hy
    rw [← extPostComp_apply]
    exact h2

/-- **Shafarevich's local-to-global step, at an arbitrary place of `L`.**

Let `L/k` be a finite Galois extension of number fields, let `w₀` be any place of `L` (finite or
archimedean) whose decomposition group `Stab_{Gal(L/k)}(w₀)` has order divisible by the prime `p`.
Then every `p`-torsion class `x ∈ H²(Gal(L/k), C_L)` lifts to a class `q ∈ H²(Gal(L/k), 𝕀_L)`
which is `p`-torsion and whose localisation at every place outside the `Gal(L/k)`-orbit of `w₀`
vanishes.  The place-dependent input is the order of `H²(Gal(L/k), W)` for the orbit-supported
idèles `W`, which is `#Stab(w₀)` at a finite place (`natCard_extH_orbitSupportedRep`) and at an
infinite place (`natCard_extH_orbitSupportedRep_inf`). -/
theorem classLocLift_ptorsion_clean (p : ℕ) [Fact p.Prime] (k L : Type) [Field k]
    [NumberField k] [Field L] [NumberField L] [Algebra k L] [FiniteDimensional k L]
    [IsGalois k L] (w₀ : NK.GlobalCFT.Place L)
    (hp : p ∣ Nat.card (MulAction.stabilizer (L ≃ₐ[k] L) w₀))
    (x : SSGRoute.PTExt.extH (SSGRoute.PTExt.classesK k L) 2) (hx : p • x = 0) :
    ∃ q : SSGRoute.PTExt.extH (SSGRoute.PTExt.idelesK k L) 2, p • q = 0 ∧
      (∀ v : NK.GlobalCFT.Place L, (∀ σ : L ≃ₐ[k] L, σ • w₀ ≠ v) →
        SSGRoute.PTExt.extLoc (k := k) (K := L) v q = 0) ∧
      q.comp (CategoryTheory.Abelian.Ext.mk₀ (NK.HassePrinciple.classGroupMap k L)) (add_zero 2)
        = x := by
  rcases w₀ with w | ŵ
  · exact exists_classLoc_lift_ptorsion_of_card p k L (NK.GlobalCFT.Place.ofInfinite w)
      (natCard_extH_orbitSupportedRep_inf k L w) hp x hx
  · exact exists_classLoc_lift_ptorsion_of_card p k L (NK.GlobalCFT.Place.ofFinite ŵ)
      (by simpa [CardOrbitSupportedRep] using natCard_extH_orbitSupportedRep k L ŵ) hp x hx

end Work.SSGRoute.SSG
