import Mathlib
import Submission.Work.BG.ThmABCCharDefs
import Submission.Work.BG.S02
import Submission.Work.BG.H0Conj
import Submission.Work.BG.CharBridge
import Submission.Work.BG.s02_lemma22Sq
import Submission.Work.BG.classMult
import Submission.Work.BG.s02_involutionPair
import Submission.Work.BG.lemma22Gen
import Submission.Work.BG.invJCard
import Submission.Work.BG.sconjLam
import Submission.Work.BG.conjByH_basic
import Submission.Work.BG.lambda_mul_irreducible
import Submission.Work.BG.lemma22EvalWAux
import Submission.Work.BG.lamCF_fixed_eq_neg_one
import Submission.Work.BG.invJ_sum_conjClasses

namespace Work.BG

open OddOrder.RepresentationTheory Work.GW2 Work.BG Work.GW2.C16 in
theorem lemma22EvalW {G : Type} [Group G] [Finite G] [Fintype G] [Invertible (Nat.card G : ℂ)]
    (D : Work.GW2.BGData G) (C : Work.BG.Sec2Ctx G) [Invertible (Nat.card ↥C.P.H0 : ℂ)]
    [Fintype ↥C.P.H] [Invertible (Nat.card ↥C.P.H : ℂ)]
    [Invertible (Nat.card ↥(Work.BG.H0in C.P) : ℂ)]
    [Fintype (OddOrder.RepresentationTheory.IrreducibleCharacter ↥C.P.H)] :
    Work.GW2.C16.Lemma22EvalProp D C := by
  intro hC κ β hκirr hκ1 hκinv hκS0 hdisj
  haveI : Fintype ↥C.P.H0 := Fintype.ofFinite _
  haveI : Fintype ↥(H0in C.P) := Fintype.ofFinite _
  -- `H0in C.P` is normal of index two
  have h2 : (H0in C.P).index = 2 := by
    rw [← Subgroup.relIndex]; exact C.P.H0_relIndex
  have hs : C.s ∉ H0in C.P := fun h => C.s_not_mem_H0 (Subgroup.mem_subgroupOf.mp h)
  -- the two representatives as elements of `↥C.P.H`
  set t1 : ↥C.P.H := ⟨D.t1, hC.H_eq.symm ▸ S_le_H D D.t1_mem⟩ with ht1def
  set t2 : ↥C.P.H := ⟨D.t2, hC.H_eq.symm ▸ S_le_H D D.t2_mem⟩ with ht2def
  have ht1 : (t1 : G) = D.t1 := rfl
  have ht2 : (t2 : G) = D.t2 := rfl
  set k1 : ℕ := (Subgroup.centralizer ({D.t1} : Set G)).relIndex D.H with hk1def
  set k2 : ℕ := (Subgroup.centralizer ({D.t2} : Set G)).relIndex D.H with hk2def
  -- `κ'` and `ν'`, the same class functions transported to `↥(H0in C.P)`
  set κ' : ClassFunction ↥(H0in C.P) ℂ :=
    ClassFunction.compHom (H0inEquiv C.P).toMonoidHom κ with hκ'def
  set ν' : ClassFunction ↥(H0in C.P) ℂ :=
    ClassFunction.compHom (H0inEquiv C.P).toMonoidHom (lamCF C β * κ) with hν'def
  -- injectivity of the transport along the (surjective) `H0inEquiv`
  have hcompHom_inj : ∀ {φ ψ : ClassFunction ↥C.P.H0 ℂ},
      ClassFunction.compHom (H0inEquiv C.P).toMonoidHom φ =
        ClassFunction.compHom (H0inEquiv C.P).toMonoidHom ψ → φ = ψ := by
    intro φ ψ h
    ext x
    obtain ⟨y, rfl⟩ := (H0inEquiv C.P).surjective x
    have hh := congrFun (congrArg (fun f : ClassFunction ↥(H0in C.P) ℂ => (f : ↥(H0in C.P) → ℂ)) h) y
    simpa [ClassFunction.compHom_apply] using hh
  -- ## Step 1: the left-hand side is `Σ_{x,y ∈ invJ C} dcf C (κ - λκ) (xy)`
  have hX : ∀ g x : ↥C.P.H, x ∈ invJ C → g * x * g⁻¹ ∈ invJ C := by
    intro g x hx
    rw [invJ_eq_XH C] at hx ⊢
    exact l22c1_XH_conj C g x hx
  have hXN : ∀ x ∈ invJ C, x ∉ H0in C.P := by
    intro x hx
    rw [mem_invJ] at hx
    intro hmem
    exact hx.2.2 (Subgroup.mem_subgroupOf.mp hmem)
  have hstep1 :
      (∑ θ : IrreducibleCharacter ↥C.P.H,
          (∑ x ∈ invJ C, (θ : ClassFunction ↥C.P.H ℂ) x) ^ 2 /
              (θ : ClassFunction ↥C.P.H ℂ) 1 *
            ClassFunction.inner
              (indH C κ - indH C (lamCF C β * κ)) (θ : ClassFunction ↥C.P.H ℂ))
        = ∑ x ∈ invJ C, ∑ y ∈ invJ C, dcf C (κ - lamCF C β * κ) (x * y) := by
    have h := classSum_expansion (K := ↥C.P.H) (X := invJ C) hX (dcf C (κ - lamCF C β * κ))
    rw [← h]
    refine Finset.sum_congr rfl fun θ _ => ?_
    rw [indH_sub_eq_dcf C κ (lamCF C β * κ)]
  rw [hstep1, l22c1_dcf_sub C κ (lamCF C β * κ)]
  have hsplit :
      (∑ x ∈ invJ C, ∑ y ∈ invJ C, (dcf C κ - dcf C (lamCF C β * κ)) (x * y))
        = (∑ x ∈ invJ C, ∑ y ∈ invJ C, dcf C κ (x * y))
          - (∑ x ∈ invJ C, ∑ y ∈ invJ C, dcf C (lamCF C β * κ) (x * y)) := by
    simp only [ClassFunction.sub_apply, Finset.sum_sub_distrib]
  rw [hsplit]
  -- ## The `κ`-part
  have hκ'irr : IsIrreducibleCharacter κ' := by
    rw [hκ'def]
    exact IsIrreducibleCharacter.compHom_of_surjective (H0inEquiv C.P).surjective hκirr
  have hκ'1 : κ' 1 = 1 := by
    rw [hκ'def, ClassFunction.compHom_apply, map_one]; exact hκ1
  have hκ'inv : ClassFunction.conjBy (H := H0in C.P) C.s κ' = κ' := by
    have h := conjByH_transport C.P C.s κ
    have h' : conjByH C.P C.s κ = κ := hκinv
    rw [h'] at h
    rw [hκ'def]
    exact h.symm
  obtain ⟨χ, hχ⟩ := exists_linear_extension h2 C.s hs κ' hκ'irr hκ'1 hκ'inv
  have hψχ : ∀ g x : ↥C.P.H, (χ (g * x * g⁻¹) : ℂ) = (χ x : ℂ) := by
    intro g x
    have h0 : (χ (g * x * g⁻¹) : ℂˣ) = χ x := by
      rw [map_mul, map_mul, map_inv, mul_comm (χ g) (χ x), mul_assoc, mul_inv_cancel, mul_one]
    rw [h0]
  have hpart1 : (∑ x ∈ invJ C, ∑ y ∈ invJ C, dcf C κ (x * y))
      = 2 * (∑ x ∈ invJ C, (χ x : ℂ)) ^ 2 := by
    have hmain := sum_induce_eq_two_mul_sq (K := ↥C.P.H) (N := H0in C.P) h2 C.s hs κ' hκ'inv
      χ hχ (invJ C) hXN
    rw [← hmain]
    rfl
  have hχsum := invJ_sum_conjClasses D C hC t1 t2 ht1 ht2 (fun x => (χ x : ℂ)) hψχ
  have ht1sq : t1 * t1 = 1 := by
    apply Subtype.ext
    rw [Subgroup.coe_mul, ht1, show D.t1 * D.t1 = 1 from by rw [← pow_two]; exact t1_sq D,
      Subgroup.coe_one]
  have hχt1sq : (χ t1 : ℂ) ^ 2 = 1 := by
    have h2' : ((χ t1 : ℂˣ) * (χ t1 : ℂˣ) : ℂˣ) = 1 := by rw [← map_mul, ht1sq, map_one]
    have h3 := congrArg (fun u : ℂˣ => (u : ℂ)) h2'
    simpa [Units.val_mul, pow_two] using h3
  have hmemS0 : D.t1 * D.t2 ∈ D.S0 := D.gen ▸ Subgroup.mem_zpowers _
  have hmemH0 : D.t1 * D.t2 ∈ C.P.H0 :=
    hC.H0_eq.symm ▸ ((le_sup_right : D.S0 ≤ D.U ⊔ D.S0) hmemS0)
  set g12 : ↥C.P.H0 := ⟨D.t1 * D.t2, hmemH0⟩ with hg12def
  have hg12 : (g12 : G) = D.t1 * D.t2 := rfl
  have hκ12 : κ g12 = 1 := hκS0 g12 hmemS0
  have hmem12 : (t1 * t2 : ↥C.P.H) ∈ H0in C.P := by
    rw [Subgroup.mem_subgroupOf, Subgroup.coe_mul, ht1, ht2]
    exact hmemH0
  have hH0in_eq : (H0inEquiv C.P).toMonoidHom ⟨t1 * t2, hmem12⟩ = g12 := by
    rw [show (H0inEquiv C.P).toMonoidHom ⟨t1 * t2, hmem12⟩
        = H0inEquiv C.P ⟨t1 * t2, hmem12⟩ from rfl]
    apply Subtype.ext
    rw [show (H0inEquiv C.P) ⟨t1 * t2, hmem12⟩
        = Subgroup.subgroupOfEquivOfLe C.P.H0_le_H ⟨t1 * t2, hmem12⟩ from rfl,
      Subgroup.subgroupOfEquivOfLe_apply_coe]
    show ((t1 * t2 : ↥C.P.H) : G) = D.t1 * D.t2
    rw [Subgroup.coe_mul, ht1, ht2]
  have hχt2eq : (χ t2 : ℂ) = (χ t1 : ℂ) := by
    have hχ12 : (χ (t1 * t2) : ℂ) = 1 := by
      have h1 := hχ ⟨t1 * t2, hmem12⟩
      rw [h1, hκ'def, ClassFunction.compHom_apply, hH0in_eq, hκ12]
    have hmul : (χ t1 : ℂ) * (χ t2 : ℂ) = 1 := by
      have h2' : ((χ t1 * χ t2 : ℂˣ) : ℂ) = 1 := by
        rw [← map_mul]
        exact hχ12
      simpa [Units.val_mul] using h2'
    have hsq1 : (χ t1 : ℂ) * (χ t1 : ℂ) = 1 := by rw [← pow_two]; exact hχt1sq
    have hinv : ((χ t1 : ℂ))⁻¹ = (χ t1 : ℂ) := inv_eq_of_mul_eq_one_right hsq1
    have hne : (χ t1 : ℂ) ≠ 0 := by
      intro h0; rw [h0] at hsq1; norm_num at hsq1
    have hc : ((χ t1 : ℂ))⁻¹ * ((χ t1 : ℂ) * (χ t2 : ℂ)) = (χ t2 : ℂ) := by
      rw [← mul_assoc, inv_mul_cancel₀ hne, one_mul]
    calc (χ t2 : ℂ) = ((χ t1 : ℂ))⁻¹ * ((χ t1 : ℂ) * (χ t2 : ℂ)) := hc.symm
      _ = ((χ t1 : ℂ))⁻¹ * 1 := by rw [hmul]
      _ = ((χ t1 : ℂ))⁻¹ := mul_one _
      _ = (χ t1 : ℂ) := hinv
  have hweights : (∑ x ∈ invJ C, (χ x : ℂ)) = (k1 : ℂ) * (χ t1 : ℂ) + (k2 : ℂ) * (χ t2 : ℂ) := by
    rw [hχsum, ← hk1def, ← hk2def]
  have hpart1' : (∑ x ∈ invJ C, ∑ y ∈ invJ C, dcf C κ (x * y))
      = 2 * ((k1 : ℂ) + (k2 : ℂ)) ^ 2 := by
    rw [hpart1, hweights, hχt2eq,
      show (k1 : ℂ) * (χ t1 : ℂ) + (k2 : ℂ) * (χ t1 : ℂ)
        = ((k1 : ℂ) + (k2 : ℂ)) * (χ t1 : ℂ) by ring,
      mul_pow, hχt1sq, mul_one]
  -- ## The `λκ`-part
  have hνirr : IsIrreducibleCharacter (lamCF C β * κ) :=
    lambda_mul_irreducible C.P ⟨β, rfl⟩ hκirr
  have hν'irr : IsIrreducibleCharacter ν' := by
    rw [hν'def]
    exact IsIrreducibleCharacter.compHom_of_surjective (H0inEquiv C.P).surjective hνirr
  have hν'1 : ν' 1 = 1 := by
    rw [hν'def, ClassFunction.compHom_apply, map_one, lamCF, ClassFunction.mul_apply,
      ClassFunction.compHom_apply, linearClassFunction_apply, hκ1, mul_one]
    simp
  have hA2 : (∑ x ∈ invJ C, ∑ y ∈ invJ C, dcf C (lamCF C β * κ) (x * y)) = 0 := by
    by_cases hA : sconj C (lamCF C β * κ) ≠ lamCF C β * κ
    · -- case A: `(λκ)^s ≠ λκ`, so `Ind λκ` is irreducible and vanishes on `invJ C`
      have hν'ne : ClassFunction.conjBy (H := H0in C.P) C.s ν' ≠ ν' := by
        intro hc
        refine hA ?_
        have h := conjByH_transport C.P C.s (lamCF C β * κ)
        have hc' : ClassFunction.conjBy C.s
            (ClassFunction.compHom (H0inEquiv C.P).toMonoidHom (lamCF C β * κ))
            = ClassFunction.compHom (H0inEquiv C.P).toMonoidHom (lamCF C β * κ) := by
          rw [← hν'def]; exact hc
        have h2' : ClassFunction.compHom (H0inEquiv C.P).toMonoidHom
              (conjByH C.P C.s (lamCF C β * κ))
            = ClassFunction.compHom (H0inEquiv C.P).toMonoidHom (lamCF C β * κ) := by
          rw [h, hc']
        exact hcompHom_inj h2'
      have hmain := sum_induce_eq_zero (K := ↥C.P.H) (N := H0in C.P) h2 C.s hs ν' hν'irr hν'ne
        (invJ C) hX hXN
      rw [← hmain]
      rfl
    · -- case B: `(λκ)^s = λκ`
      have hAeq : conjByH C.P C.s (lamCF C β * κ) = lamCF C β * κ := not_ne_iff.mp hA
      have hB := hdisj.resolve_left hA
      have hν'inv : ClassFunction.conjBy (H := H0in C.P) C.s ν' = ν' := by
        have h := conjByH_transport C.P C.s (lamCF C β * κ)
        have h2' : ClassFunction.compHom (H0inEquiv C.P).toMonoidHom
              (conjByH C.P C.s (lamCF C β * κ))
            = ClassFunction.compHom (H0inEquiv C.P).toMonoidHom (lamCF C β * κ) := by
          rw [hAeq]
        rw [hν'def, ← h]
        exact h2'
      obtain ⟨χν, hχν⟩ := exists_linear_extension h2 C.s hs ν' hν'irr hν'1 hν'inv
      have hψχν : ∀ g x : ↥C.P.H, (χν (g * x * g⁻¹) : ℂ) = (χν x : ℂ) := by
        intro g x
        have h0 : (χν (g * x * g⁻¹) : ℂˣ) = χν x := by
          rw [map_mul, map_mul, map_inv, mul_comm (χν g) (χν x), mul_assoc, mul_inv_cancel,
            mul_one]
        rw [h0]
      have hχνsum := invJ_sum_conjClasses D C hC t1 t2 ht1 ht2 (fun x => (χν x : ℂ)) hψχν
      have hk12 : k1 = k2 := hB.2.2
      have hν12 : (χν (t1 * t2) : ℂ) = -1 := by
        have h1 := hχν ⟨t1 * t2, hmem12⟩
        rw [h1, hν'def, ClassFunction.compHom_apply, hH0in_eq, ClassFunction.mul_apply, hκ12,
          mul_one]
        exact lamCF_fixed_eq_neg_one D C hC β hB.1 hB.2.1 g12 hg12
      have hχνt1sq : (χν t1 : ℂ) ^ 2 = 1 := by
        have h2' : ((χν t1 : ℂˣ) * (χν t1 : ℂˣ) : ℂˣ) = 1 := by rw [← map_mul, ht1sq, map_one]
        have h3 := congrArg (fun u : ℂˣ => (u : ℂ)) h2'
        simpa [Units.val_mul, pow_two] using h3
      have hχνt2 : (χν t2 : ℂ) = -(χν t1 : ℂ) := by
        have hmul : (χν t1 : ℂ) * (χν t2 : ℂ) = -1 := by
          have h2' : ((χν t1 * χν t2 : ℂˣ) : ℂ) = -1 := by
            rw [← map_mul]; exact hν12
          simpa [Units.val_mul] using h2'
        calc (χν t2 : ℂ) = (χν t1 : ℂ) ^ 2 * (χν t2 : ℂ) := by rw [hχνt1sq, one_mul]
          _ = (χν t1 : ℂ) * ((χν t1 : ℂ) * (χν t2 : ℂ)) := by ring
          _ = (χν t1 : ℂ) * (-1) := by rw [hmul]
          _ = -(χν t1 : ℂ) := by ring
      have hmain := sum_induce_eq_two_mul_sq (K := ↥C.P.H) (N := H0in C.P) h2 C.s hs ν' hν'inv
        χν hχν (invJ C) hXN
      change ∑ x ∈ invJ C, ∑ y ∈ invJ C, ClassFunction.induce (H0in C.P) ν' (x * y) = 0
      rw [hmain, hχνsum, ← hk1def, ← hk2def, hk12, hχνt2]
      ring
  -- ## Assembly
  have hcard : ((invJ C).card : ℂ) = (k1 : ℂ) + (k2 : ℂ) := by
    rw [invJCard D C hC]
    show (((Subgroup.centralizer ({D.t1} : Set G)).relIndex D.H
        + (Subgroup.centralizer ({D.t2} : Set G)).relIndex D.H : ℕ) : ℂ) = (k1 : ℂ) + (k2 : ℂ)
    rw [hk1def, hk2def]
    push_cast
    ring
  rw [hpart1', hA2, hcard]
  ring

end Work.BG
