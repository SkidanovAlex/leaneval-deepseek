import Mathlib
import Submission.Work.BG.c3vbDefs
import Submission.Work.BG.HatInjDefs
import Submission.Work.BG.S02
import Submission.Work.BG.ThmABCCharDefs
import Submission.Work.BG.CliffordLib
import Submission.Work.BG.ConjByTwoConstituents

namespace Work.BG

set_option linter.style.haveILetI false

open OddOrder.RepresentationTheory Work.GW2 Work.GW2.C16

/-- **Constituents permute.**  If an automorphism `φ` of a finite group `U` maps the sum
`A + A₂` of two distinct irreducible characters to itself, then it permutes the two
constituents: `φ·A = A` or `φ·A = A₂`.  (Orthonormality of irreducible characters.) -/
theorem compHom_mem_pair {U : Type} [Group U] [Finite U] [Fintype U]
    [Invertible (Nat.card U : ℂ)] (φ : U ≃* U) {A A₂ : ClassFunction U ℂ}
    (hA : IsIrreducibleCharacter A) (hA₂ : IsIrreducibleCharacter A₂) (hne : A₂ ≠ A)
    (h : ClassFunction.compHom φ.toMonoidHom (A + A₂) = A + A₂) :
    ClassFunction.compHom φ.toMonoidHom A = A ∨ ClassFunction.compHom φ.toMonoidHom A = A₂ := by
  have hφA : IsIrreducibleCharacter (ClassFunction.compHom φ.toMonoidHom A) :=
    hA.compHom_of_surjective φ.surjective
  have hφA₂ : IsIrreducibleCharacter (ClassFunction.compHom φ.toMonoidHom A₂) :=
    hA₂.compHom_of_surjective φ.surjective
  rw [ClassFunction.compHom_add] at h
  set X₁ : IrreducibleCharacter U := ⟨ClassFunction.compHom φ.toMonoidHom A, hφA⟩ with hX₁
  set W : IrreducibleCharacter U := ⟨ClassFunction.compHom φ.toMonoidHom A₂, hφA₂⟩ with hW
  set Y : IrreducibleCharacter U := ⟨A, hA⟩ with hY
  set Z : IrreducibleCharacter U := ⟨A₂, hA₂⟩ with hZ
  have hXW : X₁ ≠ W := by
    intro hh
    apply hne
    have h2 : ClassFunction.compHom φ.toMonoidHom A = ClassFunction.compHom φ.toMonoidHom A₂ := by
      have hval := congrArg Subtype.val hh
      simpa [hX₁, hW] using hval
    apply ClassFunction.ext
    intro u
    have hpt := congrFun (congrArg (fun f : ClassFunction U ℂ => (f : U → ℂ)) h2) (φ.symm u)
    simpa [ClassFunction.compHom_apply] using hpt.symm
  have hbase : ClassFunction.inner (X₁ : ClassFunction U ℂ) (X₁ : ClassFunction U ℂ)
      + ClassFunction.inner (X₁ : ClassFunction U ℂ) (W : ClassFunction U ℂ)
      = ClassFunction.inner (X₁ : ClassFunction U ℂ) (Y : ClassFunction U ℂ)
        + ClassFunction.inner (X₁ : ClassFunction U ℂ) (Z : ClassFunction U ℂ) := by
    rw [← ClassFunction.inner_add_right, ← ClassFunction.inner_add_right]
    exact congrArg _ h
  have hdiag : ClassFunction.inner (X₁ : ClassFunction U ℂ) (X₁ : ClassFunction U ℂ) = 1 := by
    rw [irreducibleCharacter_inner_eq_ite]; exact if_pos rfl
  have hoff : ClassFunction.inner (X₁ : ClassFunction U ℂ) (W : ClassFunction U ℂ) = 0 := by
    rw [irreducibleCharacter_inner_eq_ite]; exact if_neg hXW
  rw [hdiag, hoff, irreducibleCharacter_inner_eq_ite, irreducibleCharacter_inner_eq_ite] at hbase
  simp only [add_zero] at hbase
  by_cases hXY : X₁ = Y
  · left
    have hval := congrArg Subtype.val hXY
    simpa [hX₁, hY] using hval
  · right
    rw [if_neg hXY, zero_add] at hbase
    have hXZ : X₁ = Z := by
      by_contra hc
      rw [if_neg hc] at hbase
      exact one_ne_zero hbase
    have hval := congrArg Subtype.val hXZ
    simpa [hX₁, hZ] using hval

theorem c3vbConstituentFixed {G : Type} [Group G] [Finite G] [Fintype G]
    [Invertible (Nat.card G : ℂ)] (D : Work.GW2.BGData G) (C : Work.BG.Sec2Ctx G)
    [Invertible (Nat.card ↥C.P.H0 : ℂ)]
    (hC : Work.GW2.C16.Compat D C) (hSec3 : Work.GW2.C16.Sec3Hyp D)
    {ν : OddOrder.RepresentationTheory.ClassFunction ↥C.P.H0 ℂ}
    (hν : OddOrder.RepresentationTheory.IsIrreducibleCharacter ν)
    (A A₂ : OddOrder.RepresentationTheory.ClassFunction ↥C.P.U ℂ)
    (hA : OddOrder.RepresentationTheory.IsIrreducibleCharacter A)
    (hA₂ : OddOrder.RepresentationTheory.IsIrreducibleCharacter A₂) (hne : A₂ ≠ A)
    (hres : Work.BG.restrictU C ν = A + A₂)
    (hσ : ∀ u : ↥C.P.U, Work.BG.restrictU C ν (Work.BG.sigmaU C u) = Work.BG.restrictU C ν u) :
    (∀ u : ↥C.P.U, A (Work.BG.sigmaU C u) = A u) ∨
      (∀ u : ↥C.P.U, A (Work.BG.tauU D C hC u) = A u) := by
  classical
  haveI : Fintype ↥C.P.H0 := Fintype.ofFinite _
  haveI : Fintype ↥C.P.U := Fintype.ofFinite _
  haveI hInvU : Invertible (Nat.card ↥C.P.U : ℂ) :=
    invertibleOfNonzero (Nat.cast_ne_zero.mpr Nat.card_pos.ne')
  haveI : Fintype ↥(Uin C) := Fintype.ofFinite _
  haveI hInvUin : Invertible (Nat.card ↥(Uin C) : ℂ) :=
    invertibleOfNonzero (Nat.cast_ne_zero.mpr Nat.card_pos.ne')
  haveI hNorm : (Uin C).Normal := C.instUNormal
  -- `y = t₁t₂` as an element of `H₀`
  have hy_mem : D.t1 * D.t2 ∈ C.P.H0 := by
    rw [hC.H0_eq]
    exact Subgroup.mem_sup_right (by rw [D.gen]; exact Subgroup.mem_zpowers _)
  let y : ↥C.P.H0 := ⟨D.t1 * D.t2, hy_mem⟩
  -- the covering hypothesis `H₀ = U·⟨y⟩`, carried inside `↥C.P.H0`
  have hUle : D.U ≤ C.P.H0 := by rw [hC.H0_eq]; exact le_sup_left
  have hSle : D.S0 ≤ C.P.H0 := by rw [hC.H0_eq]; exact le_sup_right
  have hsup_eq : Uin C ⊔ D.S0.subgroupOf C.P.H0 = ⊤ := by
    rw [show Uin C = C.P.U.subgroupOf C.P.H0 from rfl, hC.U_eq]
    rw [← Subgroup.subgroupOf_sup hUle hSle]
    rw [show D.U ⊔ D.S0 = H1 D from rfl, ← hC.H0_eq]
    exact Subgroup.subgroupOf_self C.P.H0
  have hcov : ∀ x : ↥C.P.H0, ∃ n ∈ Uin C, ∃ k : ℤ, x = n * y ^ k := by
    intro x
    have hx : x ∈ (⊤ : Subgroup ↥C.P.H0) := Subgroup.mem_top x
    rw [← hsup_eq] at hx
    obtain ⟨n, hn, s, hs, hns⟩ :=
      (Subgroup.mem_sup_of_normal_left (s := Uin C) (t := D.S0.subgroupOf C.P.H0)).mp hx
    have hs' : (s : G) ∈ D.S0 := Subgroup.mem_subgroupOf.mp hs
    obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp (by rw [← D.gen]; exact hs')
    refine ⟨n, hn, k, ?_⟩
    rw [← hns]
    congr 1
    apply Subtype.ext
    show ((s : ↥C.P.H0) : G) = (((y ^ k : ↥C.P.H0) : G))
    have hyk : ((y ^ k : ↥C.P.H0) : G) = (D.t1 * D.t2) ^ k := by
      rw [Subgroup.coe_zpow]
    rw [hyk]
    exact hk.symm
  -- transport `A`, `A₂` to characters of `↥(Uin C)` along `e : ↥(Uin C) ≃* ↥C.P.U`
  let e : ↥(Uin C) ≃* ↥C.P.U := Subgroup.subgroupOfEquivOfLe C.P.U_le_H0
  let A' : ClassFunction ↥(Uin C) ℂ := ClassFunction.compHom e.toMonoidHom A
  let A₂' : ClassFunction ↥(Uin C) ℂ := ClassFunction.compHom e.toMonoidHom A₂
  have hA' : IsIrreducibleCharacter A' := hA.compHom_of_surjective e.surjective
  have hA₂' : IsIrreducibleCharacter A₂' := hA₂.compHom_of_surjective e.surjective
  have hne' : A₂' ≠ A' := by
    intro hh
    apply hne
    have h2 : ClassFunction.compHom e.toMonoidHom A = ClassFunction.compHom e.toMonoidHom A₂ := by
      have hval : A' = A₂' := hh.symm
      simpa [A', A₂'] using hval
    apply ClassFunction.ext
    intro w
    have hpt := congrFun (congrArg (fun f : ClassFunction ↥(Uin C) ℂ => (f : ↥(Uin C) → ℂ)) h2)
      (e.symm w)
    simpa [ClassFunction.compHom_apply] using hpt.symm
  have hres' : ClassFunction.restrict (Uin C) ν = A' + A₂' := by
    ext u
    rw [ClassFunction.restrict_apply, ClassFunction.add_apply]
    have h1 : restrictU C ν (e u) = A (e u) + A₂ (e u) := by
      rw [hres]; rfl
    have h2 : restrictU C ν (e u)
        = ν (⟨((e u : ↥C.P.U) : G), C.P.U_le_H0 (e u).2⟩ : ↥C.P.H0) := rfl
    rw [h2] at h1
    have h3 : (⟨((e u : ↥C.P.U) : G), C.P.U_le_H0 (e u).2⟩ : ↥C.P.H0) = u := by
      apply Subtype.ext
      rfl
    rw [h3] at h1
    simpa [A', A₂'] using h1
  -- the abstract Clifford input: `A` is not fixed by conjugation by `y`
  have habs : ClassFunction.conjBy (G := ↥C.P.H0) (H := Uin C) y A' ≠ A' :=
    ConjByTwoConstituents (Uin C) hν hA' hA₂' hne' hres' hcov
  -- transport back: `conjBy y A' = compHom e (compHom υ A)`
  have htrans : ClassFunction.conjBy (G := ↥C.P.H0) (H := Uin C) y A'
      = ClassFunction.compHom e.toMonoidHom
          (ClassFunction.compHom (yU D C hC).toMonoidHom A) := by
    ext u
    rw [ClassFunction.conjBy_apply, ClassFunction.compHom_apply, ClassFunction.compHom_apply]
    congr 1
  have hυ_ne : ClassFunction.compHom (yU D C hC).toMonoidHom A ≠ A := by
    intro hh
    exact habs (by rw [htrans, hh])
  -- `σ`-invariance and `υ`-invariance of `restrictU C ν`
  have hσ_perm : ClassFunction.compHom (sigmaU C).toMonoidHom (A + A₂) = A + A₂ := by
    rw [← hres]
    ext u
    rw [ClassFunction.compHom_apply]
    exact hσ u
  have hυfix : ClassFunction.compHom (yU D C hC).toMonoidHom (restrictU C ν) = restrictU C ν := by
    ext u
    rw [ClassFunction.compHom_apply, restrictU_apply, restrictU_apply]
    exact ν.conj_eq (⟨(u : G), C.P.U_le_H0 u.2⟩ : ↥C.P.H0)
      (⟨D.t1 * D.t2, hy_mem⟩ : ↥C.P.H0)
  have hυ_perm : ClassFunction.compHom (yU D C hC).toMonoidHom (A + A₂) = A + A₂ := by
    rw [← hres, hυfix, hres]
  -- the two permutation facts
  have hσ_cases := compHom_mem_pair (sigmaU C) hA hA₂ hne hσ_perm
  have hυ_cases := compHom_mem_pair (yU D C hC) hA hA₂ hne hυ_perm
  by_cases hσfix : ClassFunction.compHom (sigmaU C).toMonoidHom A = A
  · left
    intro u
    have hpt := congrFun (congrArg (fun f : ClassFunction ↥C.P.U ℂ => (f : ↥C.P.U → ℂ)) hσfix) u
    simpa [ClassFunction.compHom_apply] using hpt
  · right
    have hσA₂ : ClassFunction.compHom (sigmaU C).toMonoidHom A = A₂ := by
      rcases hσ_cases with hh | hh
      · exact absurd hh hσfix
      · exact hh
    have hυA₂eq : ClassFunction.compHom (yU D C hC).toMonoidHom A = A₂ := by
      rcases hυ_cases with hh | hh
      · exact absurd hh hυ_ne
      · exact hh
    have hcomp : ClassFunction.compHom (yU D C hC * yU D C hC).toMonoidHom A
        = ClassFunction.compHom (yU D C hC).toMonoidHom
            (ClassFunction.compHom (yU D C hC).toMonoidHom A) := by
      ext u
      rw [ClassFunction.compHom_apply, ClassFunction.compHom_apply]
      rfl
    have hυυ : ClassFunction.compHom (yU D C hC * yU D C hC).toMonoidHom A = A := by
      rw [yU_mul_self D C hC hSec3]
      ext u
      rw [ClassFunction.compHom_apply]
      rfl
    have hυA₂ : ClassFunction.compHom (yU D C hC).toMonoidHom A₂ = A := by
      rw [← hυA₂eq, ← hcomp, hυυ]
    have hτeq : ClassFunction.compHom (tauU D C hC).toMonoidHom A
        = ClassFunction.compHom (yU D C hC).toMonoidHom
            (ClassFunction.compHom (sigmaU C).toMonoidHom A) := by
      ext u
      rw [ClassFunction.compHom_apply, ClassFunction.compHom_apply, tauU_eq D C hC]
      rfl
    have hτfix : ClassFunction.compHom (tauU D C hC).toMonoidHom A = A := by
      rw [hτeq, hσA₂, hυA₂]
    intro u
    have hpt := congrFun (congrArg (fun f : ClassFunction ↥C.P.U ℂ => (f : ↥C.P.U → ℂ)) hτfix) u
    simpa [ClassFunction.compHom_apply] using hpt

end Work.BG
