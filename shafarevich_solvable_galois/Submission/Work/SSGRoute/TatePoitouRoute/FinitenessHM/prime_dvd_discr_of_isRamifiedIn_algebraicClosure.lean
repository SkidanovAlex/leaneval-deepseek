import Mathlib
import Submission.Work.SSGRoute.TatePoitouRoute.FinitenessHM.placePrime_dvd_discr_of_isRamifiedIn
import Submission.Work.SSGRoute.TatePoitouRoute.FinitenessHM.isRamifiedIn_comap_algEquiv_proved
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace Work.SSGRoute.TatePoitouRoute.FinitenessHM

set_option linter.style.haveILetI false

/-- **The rational prime below a finite place at which a finite subfield ramifies divides the discriminant of that subfield** — the algebraic-closure level form of `placePrime_dvd_discr_of_isRamifiedIn` (which is stated for `SSGRoute.QBar = AlgebraicClosure ℚ`).

Route: take `σ : Ω ≃ₐ[ℚ] SSGRoute.QBar` (`IsAlgClosure.equiv ℚ Ω SSGRoute.QBar`), put `B' := B.comap (σ.symm : SSGRoute.QBar →+* Ω)`, use `isRamifiedIn_comap_algEquiv_proved` to get `IsRamifiedIn ℚ (Λ.map σ.toAlgHom) B'`, apply the `QBar` lemma `placePrime_dvd_discr_of_isRamifiedIn`, transport `NumberField.discr (Λ.map σ.toAlgHom) = NumberField.discr Λ` with `NumberField.discr_eq_discr_of_algEquiv (IntermediateField.equivMap Λ σ.toAlgHom)`, and transport the valuation inequality `B'.valuation (p : QBar) < 1` (from `placePrime_val_lt_one`) to `B.valuation (p : Ω) < 1` using `comap_valuation_lt_one_iff'` / `Work.SSGRoute.comap_valuation_lt_one_iff` and `map_natCast`. -/
theorem prime_dvd_discr_of_isRamifiedIn_algebraicClosure
    (Ω : Type) [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω] [CharZero Ω]
    (Λ : IntermediateField ℚ Ω) [FiniteDimensional ℚ Λ]
    (B : ValuationSubring Ω) (hB : SSGRoute.IsFinPlace ℚ B)
    (h : SSGRoute.IsRamifiedIn ℚ Λ B) :
    ∃ p : ℕ, p.Prime ∧ B.valuation (p : Ω) < 1 ∧ p ∣ (NumberField.discr Λ).natAbs := by
  -- a `ℚ`-algebra isomorphism between `Ω` and the chosen algebraic closure `ℚ̄ = SSGRoute.QBar`
  obtain ⟨σ⟩ : Nonempty (Ω ≃ₐ[ℚ] SSGRoute.QBar) := ⟨IsAlgClosure.equiv ℚ Ω SSGRoute.QBar⟩
  -- the image `Λ' = σ Λ` of `Λ` inside `ℚ̄`
  have hmem : ∀ x : ↥Λ, (σ : Ω → SSGRoute.QBar) x ∈ Λ.map σ.toAlgHom := by
    intro x
    rw [IntermediateField.mem_map]
    exact ⟨(x : Ω), x.2, rfl⟩
  -- the ring isomorphism `Λ ≃+* σ Λ` (built by hand: `IntermediateField.equivMap` is unusable here,
  -- because `Ω` carries an *arbitrary* `Algebra ℚ Ω` structure, not the canonical one)
  let ψ : ↥Λ →+* ↥(Λ.map σ.toAlgHom) :=
    { toFun := fun x => ⟨σ x, hmem x⟩
      map_one' := Subtype.ext (by simp)
      map_mul' := fun x y => Subtype.ext (by simp)
      map_zero' := Subtype.ext (by simp)
      map_add' := fun x y => Subtype.ext (by simp) }
  have hinj : Function.Injective ψ := by
    intro x y hxy
    have h1 : (σ (x : Ω)) = σ (y : Ω) :=
      congrArg (fun z : ↥(Λ.map σ.toAlgHom) => (z : SSGRoute.QBar)) hxy
    exact Subtype.ext (σ.injective h1)
  have hsurj : Function.Surjective ψ := by
    intro y
    have hy := y.2
    rw [IntermediateField.mem_map] at hy
    obtain ⟨x, hx, hxy⟩ := hy
    exact ⟨⟨x, hx⟩, Subtype.ext hxy⟩
  let ψe : ↥Λ ≃+* ↥(Λ.map σ.toAlgHom) := RingEquiv.ofBijective ψ ⟨hinj, hsurj⟩
  -- `σ Λ` is a number field, with the same discriminant as `Λ`
  haveI : NumberField ↥(Λ.map σ.toAlgHom) := NumberField.of_ringEquiv ↥Λ ↥(Λ.map σ.toAlgHom) ψe
  have hdiscZ : NumberField.discr ↥(Λ.map σ.toAlgHom) = NumberField.discr ↥Λ :=
    (NumberField.discr_eq_discr_of_ringEquiv (K := ↥Λ) (L := ↥(Λ.map σ.toAlgHom)) ψe).symm
  have hnat : (NumberField.discr ↥(Λ.map σ.toAlgHom)).natAbs = (NumberField.discr ↥Λ).natAbs := by
    rw [hdiscZ]
  -- the place of `ℚ̄` obtained by pulling back `B`
  set B' : ValuationSubring SSGRoute.QBar := B.comap (σ.symm : SSGRoute.QBar →+* Ω) with hB'def
  have hB'fin : SSGRoute.IsFinPlace ℚ B' := by
    rw [SSGRoute.IsFinPlace, hB'def, ValuationSubring.comap_comap]
    have hcomp : (σ.symm : SSGRoute.QBar →+* Ω).comp (algebraMap ℚ SSGRoute.QBar) = algebraMap ℚ Ω := by
      ext r; exact σ.symm.commutes r
    rw [hcomp]
    exact hB
  have hcomp' : (σ.symm : SSGRoute.QBar →+* Ω).comp (σ : Ω →+* SSGRoute.QBar) = RingHom.id Ω := by
    ext x; simp
  have hcomap : B'.comap (σ : Ω →+* SSGRoute.QBar) = B := by
    rw [hB'def, ValuationSubring.comap_comap, hcomp']
    ext x; simp [ValuationSubring.mem_comap]
  have hram : SSGRoute.IsRamifiedIn ℚ (Λ.map σ.toAlgHom) B' := by
    refine (isRamifiedIn_comap_algEquiv_proved Ω σ Λ B').mp ?_
    rw [hcomap]
    exact h
  -- the `ℚ̄`-level statement
  have hdvd := placePrime_dvd_discr_of_isRamifiedIn (Λ.map σ.toAlgHom) B' hB'fin hram
  refine ⟨(Work.SSGRoute.placePrime B' hB'fin).1, (Work.SSGRoute.placePrime B' hB'fin).2, ?_, ?_⟩
  · -- transport the valuation inequality from `ℚ̄` to `Ω` along `σ.symm`
    have h1 : (B.comap (σ.symm : SSGRoute.QBar →+* Ω)).valuation
        ((Work.SSGRoute.placePrime B' hB'fin).1 : SSGRoute.QBar) < 1 := by
      rw [← hB'def]
      exact Work.SSGRoute.placePrime_val_lt_one B' hB'fin
    have h2 := (comap_valuation_lt_one_iff_ringHom B (σ.symm : SSGRoute.QBar →+* Ω)
      ((Work.SSGRoute.placePrime B' hB'fin).1 : SSGRoute.QBar)).mp h1
    rwa [map_natCast] at h2
  · -- transport the divisibility of the discriminant along `ψe`
    rw [← hnat]
    exact hdvd

end Work.SSGRoute.TatePoitouRoute.FinitenessHM
