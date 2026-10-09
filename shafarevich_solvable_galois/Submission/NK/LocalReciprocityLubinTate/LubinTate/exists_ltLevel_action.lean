import Mathlib
import Submission.NK.LocalReciprocityLubinTate.LubinTate.exists_autLTLevel_mulEquiv_apply_smulDiv
import Submission.NK.LocalReciprocityLubinTate.Eval.smulDiv_algEquiv
import Submission.NK.LocalReciprocityLubinTate.Eval.smulDiv_smul2
import Submission.NK.LocalReciprocityLubinTate.Eval.ltLevelIsSimple_of_fibre
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace NK.LocalReciprocityLubinTate.LubinTate

/-! ### Plan

`exists_autLTLevel_mulEquiv_apply_smulDiv` provides, after choosing a *primitive* division point
`y ∈ Λ_n ∖ Λ_{n-1}`, an isomorphism `e : (𝒪[F]/𝔪[F]^n)ˣ ≃* Gal(K_n/F)` normalised at `y` by
`e(u)(y) = [u](y)` (`Eval.smulDiv`).

The statement proved here is the version on the *whole* unit group `𝒪[F]ˣ`: composing `e` with the
reduction `𝒪[F]ˣ →* (𝒪[F]/𝔪[F]^n)ˣ` gives a surjective homomorphism `Ψ` with kernel `U^n`, and the
normalisation at `y` upgrades to *every* division point `z ∈ Λ_n`, because `Λ_n = {a · y}` is the
`𝒪[F]`-orbit of the primitive point (`Eval.range_smulDiv_eq_LTdivisionSet`) and an automorphism of
the level commutes with the `𝒪[F]`-action (`Eval.smulDiv_algEquiv`). -/

universe u

set_option maxHeartbeats 2000000

theorem exists_ltLevel_action {F : Type u} [Field F] [CharZero F] [ValuativeRel F]
    [TopologicalSpace F] [IsNonarchimedeanLocalField F]
    (P : ↥(ValuativeRel.valuation F).integer) (hP : Irreducible P) (n : ℕ) (hn : 1 ≤ n)
    (M : NK.LocalReciprocityLubinTate.LubinTateModule ↥(ValuativeRel.valuation F).integer P
      (NK.LocalReciprocityLubinTate.residueCard F))
    (hpi : M.toLaw.piEndo = NK.LocalReciprocityLubinTate.piXAddXq P
      (NK.LocalReciprocityLubinTate.residueCard F)) :
    ∃ Ψ : (↥(ValuativeRel.valuation F).integer)ˣ →*
          (↥(NK.LocalReciprocityLubinTate.LTLevel F (P : F)
              (NK.LocalReciprocityLubinTate.residueCard F) n) ≃ₐ[F]
            ↥(NK.LocalReciprocityLubinTate.LTLevel F (P : F)
              (NK.LocalReciprocityLubinTate.residueCard F) n)),
      (∀ (u : (↥(ValuativeRel.valuation F).integer)ˣ) (z : AlgebraicClosure F)
          (hz : z ∈ NK.LocalReciprocityLubinTate.LTdivisionSet F (P : F)
            (NK.LocalReciprocityLubinTate.residueCard F) n),
          ((Ψ u) ⟨z, NK.LocalReciprocityLubinTate.LTdivisionSet_subset_LTLevel F (P : F)
              (NK.LocalReciprocityLubinTate.residueCard F) n hz⟩ : AlgebraicClosure F)
            = NK.LocalReciprocityLubinTate.Eval.smulDiv P hP
              (NK.LocalReciprocityLubinTate.residueCard F) n
              (NK.LocalReciprocityLubinTate.two_le_residueCard F) M hz
              (u : ↥(ValuativeRel.valuation F).integer)) ∧
      Function.Surjective Ψ ∧
      MonoidHom.ker Ψ = NK.LocalReciprocityLubinTate.principalUnits F n := by
  classical
  have hq : 2 ≤ NK.LocalReciprocityLubinTate.residueCard F :=
    NK.LocalReciprocityLubinTate.two_le_residueCard F
  let O := ↥(ValuativeRel.valuation F).integer
  let I : Ideal O := (IsLocalRing.maximalIdeal O) ^ n
  let L := NK.LocalReciprocityLubinTate.LTLevel F (P : F)
    (NK.LocalReciprocityLubinTate.residueCard F) n
  -- a primitive division point, and the canonical isomorphism normalised at it
  obtain ⟨y, hy, hyp⟩ := exists_primitive_LTdivisionSet P hP n hn
  obtain ⟨e, he⟩ := exists_autLTLevel_mulEquiv_apply_smulDiv P hP n hn M hpi y hy hyp
  let mkI : O →* (O ⧸ I) := (Ideal.Quotient.mk I).toMonoidHom
  -- the homomorphism of the statement: reduce units modulo `𝔪[F]^n`, then apply `e`
  let Ψ : Oˣ →* (↥L ≃ₐ[F] ↥L) := e.toMonoidHom.comp (Units.map mkI)
  have hΨ : ∀ u : Oˣ, Ψ u = e (Units.map mkI u) := fun _ => rfl
  -- an automorphism of the level, read on a division point of the closure
  have hlift : ∀ (σ : ↥L ≃ₐ[F] ↥L) (z : AlgebraicClosure F)
      (hz : z ∈ NK.LocalReciprocityLubinTate.LTdivisionSet F (P : F)
        (NK.LocalReciprocityLubinTate.residueCard F) n),
      ((σ ⟨z, NK.LocalReciprocityLubinTate.LTdivisionSet_subset_LTLevel F (P : F)
          (NK.LocalReciprocityLubinTate.residueCard F) n hz⟩ : ↥L) : AlgebraicClosure F)
        = σ.liftNormal (AlgebraicClosure F) z := by
    intro σ z hz
    exact (AlgEquiv.liftNormal_commutes σ (AlgebraicClosure F)
      ⟨z, NK.LocalReciprocityLubinTate.LTdivisionSet_subset_LTLevel F (P : F)
        (NK.LocalReciprocityLubinTate.residueCard F) n hz⟩).symm
  -- the normalisation of `e` at `y`, transported to a unit of `𝒪[F]`
  have he_u : ∀ u : Oˣ,
      ((e (Units.map mkI u)) ⟨y, NK.LocalReciprocityLubinTate.LTdivisionSet_subset_LTLevel F
          (P : F) (NK.LocalReciprocityLubinTate.residueCard F) n hy⟩ : AlgebraicClosure F)
        = NK.LocalReciprocityLubinTate.Eval.smulDiv P hP
            (NK.LocalReciprocityLubinTate.residueCard F) n hq M hy (u : O) := by
    intro u
    have hisU : IsUnit (Ideal.Quotient.mk I (u : O)) := (Units.map mkI u).isUnit
    have hunit : hisU.unit = Units.map mkI u := by
      apply Units.ext
      show (hisU.unit : O ⧸ I) = (Ideal.Quotient.mk I) (u : O)
      rw [IsUnit.unit_spec]
    have h := he (u : O) hisU
    rw [show e hisU.unit = e (Units.map mkI u) from congrArg e hunit] at h
    exact h
  -- the action on every division point
  have haction : ∀ (u : Oˣ) (z : AlgebraicClosure F)
      (hz : z ∈ NK.LocalReciprocityLubinTate.LTdivisionSet F (P : F)
        (NK.LocalReciprocityLubinTate.residueCard F) n),
      ((Ψ u) ⟨z, NK.LocalReciprocityLubinTate.LTdivisionSet_subset_LTLevel F (P : F)
          (NK.LocalReciprocityLubinTate.residueCard F) n hz⟩ : AlgebraicClosure F)
        = NK.LocalReciprocityLubinTate.Eval.smulDiv P hP
            (NK.LocalReciprocityLubinTate.residueCard F) n hq M hz (u : O) := by
    intro u z hz
    have hσy : (e (Units.map mkI u)).liftNormal (AlgebraicClosure F) y
        = NK.LocalReciprocityLubinTate.Eval.smulDiv P hP
            (NK.LocalReciprocityLubinTate.residueCard F) n hq M hy (u : O) :=
      ((hlift (e (Units.map mkI u)) y hy).symm).trans (he_u u)
    have hmemσ : (e (Units.map mkI u)).liftNormal (AlgebraicClosure F) y
        ∈ NK.LocalReciprocityLubinTate.LTdivisionSet F (P : F)
            (NK.LocalReciprocityLubinTate.residueCard F) n :=
      (mem_LTdivisionSet_algEquiv_iff (P : F) (NK.LocalReciprocityLubinTate.residueCard F) n hq
        ((e (Units.map mkI u)).liftNormal (AlgebraicClosure F)) y).mpr hy
    -- `Λ_n` is the `𝒪[F]`-orbit of `y`
    obtain ⟨a, ha⟩ : z ∈ Set.range (fun a : O =>
        NK.LocalReciprocityLubinTate.Eval.smulDiv P hP
          (NK.LocalReciprocityLubinTate.residueCard F) n hq M hy a) := by
      rw [Eval.range_smulDiv_eq_LTdivisionSet P hP
        (NK.LocalReciprocityLubinTate.residueCard F) n hq hn rfl M hpi hy hyp]
      exact hz
    rw [hΨ u, hlift (e (Units.map mkI u)) z hz]
    calc (e (Units.map mkI u)).liftNormal (AlgebraicClosure F) z
        = (e (Units.map mkI u)).liftNormal (AlgebraicClosure F)
            (NK.LocalReciprocityLubinTate.Eval.smulDiv P hP
              (NK.LocalReciprocityLubinTate.residueCard F) n hq M hy a) := by rw [← ha]
      _ = NK.LocalReciprocityLubinTate.Eval.smulDiv P hP
            (NK.LocalReciprocityLubinTate.residueCard F) n hq M hmemσ a :=
          Eval.smulDiv_algEquiv P hP (NK.LocalReciprocityLubinTate.residueCard F) n hq M y hy
            ((e (Units.map mkI u)).liftNormal (AlgebraicClosure F)) hmemσ a
      _ = NK.LocalReciprocityLubinTate.Eval.smulDiv P hP
            (NK.LocalReciprocityLubinTate.residueCard F) n hq M
            (Eval.smulDiv_mem P hP (NK.LocalReciprocityLubinTate.residueCard F) n hq M hpi
              y hy (u : O)) a :=
          Eval.smulDiv_congr P hP (NK.LocalReciprocityLubinTate.residueCard F) n hq M hmemσ
            (Eval.smulDiv_mem P hP (NK.LocalReciprocityLubinTate.residueCard F) n hq M hpi
              y hy (u : O)) hσy a
      _ = NK.LocalReciprocityLubinTate.Eval.smulDiv P hP
            (NK.LocalReciprocityLubinTate.residueCard F) n hq M hy (a * (u : O)) :=
          Eval.smulDiv_smul2 P hP (NK.LocalReciprocityLubinTate.residueCard F) n hq M hpi
            y hy a (u : O)
      _ = NK.LocalReciprocityLubinTate.Eval.smulDiv P hP
            (NK.LocalReciprocityLubinTate.residueCard F) n hq M hy ((u : O) * a) := by
          rw [mul_comm]
      _ = NK.LocalReciprocityLubinTate.Eval.smulDiv P hP
            (NK.LocalReciprocityLubinTate.residueCard F) n hq M
            (Eval.smulDiv_mem P hP (NK.LocalReciprocityLubinTate.residueCard F) n hq M hpi
              y hy a) (u : O) :=
          (Eval.smulDiv_smul2 P hP (NK.LocalReciprocityLubinTate.residueCard F) n hq M hpi
            y hy (u : O) a).symm
      _ = NK.LocalReciprocityLubinTate.Eval.smulDiv P hP
            (NK.LocalReciprocityLubinTate.residueCard F) n hq M hz (u : O) :=
          Eval.smulDiv_congr P hP (NK.LocalReciprocityLubinTate.residueCard F) n hq M
            (Eval.smulDiv_mem P hP (NK.LocalReciprocityLubinTate.residueCard F) n hq M hpi
              y hy a) hz ha (u : O)
  -- the reduction `𝒪[F]ˣ → (𝒪[F]/𝔪[F]^n)ˣ` is surjective
  have hsurjMk : Function.Surjective (Units.map mkI) := by
    intro w
    obtain ⟨a, ha⟩ := Ideal.Quotient.mk_surjective (I := I) (w : O ⧸ I)
    have hua : IsUnit a := by
      have h1 : IsUnit (Ideal.Quotient.mk I a) := by rw [ha]; exact w.isUnit
      have h1' : IsUnit (Ideal.Quotient.mk ((IsLocalRing.maximalIdeal O) ^ n) a) := h1
      have h2 : a ∉ IsLocalRing.maximalIdeal O :=
        (Ideal.Quotient.isUnit_mk_pow_iff_notMem (IsLocalRing.maximalIdeal O)
          (by omega : n ≠ 0)).mp h1'
      exact IsLocalRing.notMem_maximalIdeal.mp h2
    obtain ⟨u, hu⟩ := hua
    refine ⟨u, Units.ext ?_⟩
    show (Ideal.Quotient.mk I) (u : O) = (w : O ⧸ I)
    rw [hu]
    exact ha
  have hsurj : Function.Surjective Ψ := by
    intro σ
    obtain ⟨u, hu⟩ := hsurjMk (e.symm σ)
    exact ⟨u, by rw [hΨ u, hu, MulEquiv.apply_symm_apply]⟩
  -- the kernel is the group of higher principal units
  have hker : MonoidHom.ker Ψ = NK.LocalReciprocityLubinTate.principalUnits F n := by
    ext u
    rw [MonoidHom.mem_ker, NK.LocalReciprocityLubinTate.mem_principalUnits_iff]
    show (Ψ u = 1) ↔ ((u : O) - 1) ∈ I
    rw [hΨ u, MulEquiv.map_eq_one_iff, Units.ext_iff]
    simp only [Units.coe_map, Units.val_one, ← map_one (Ideal.Quotient.mk I), mkI]
    exact Ideal.Quotient.eq
  exact ⟨Ψ, haction, hsurj, hker⟩

end NK.LocalReciprocityLubinTate.LubinTate
