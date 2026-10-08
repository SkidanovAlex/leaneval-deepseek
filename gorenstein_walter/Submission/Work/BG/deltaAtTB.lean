import Mathlib
import Submission.Work.BG.Thm43Defs
import Submission.Work.BG.ThmABCCharDefs
import Submission.Work.BG.S02
import Submission.Work.BG.s02_bsValueT
import Submission.Work.BG.H0Conj
import Submission.Work.BG.centralValue
import Submission.Work.BG.rem31IndexUin
import Submission.Work.BG.lemma17_iii_dualC2
import Submission.Work.BG.sconjLam
import Submission.Work.BG.lambda_mul_irreducible
import Submission.Work.BG.lemma17_ii_aux

namespace Work.BG

open OddOrder.RepresentationTheory

/-- If `z` is central in `H` and `ν ∈ Irr(H)` satisfies `ν z = ν 1`, then `z` lies in the
kernel of `ν`: `ν (z * h) = ν h` for all `h`.  (Schur: a central element acts as a scalar.) -/
theorem irrMulCentralAux {H : Type} [Group H] [Finite H] {z : H}
    (hz : z ∈ Subgroup.center H) {ν : ClassFunction H ℂ}
    (hν : IsIrreducibleCharacter ν) (hz1 : ν z = ν 1) :
    ∀ h : H, ν (z * h) = ν h := by
  classical
  obtain ⟨V, _, _, _, ρ, hirr, hchar⟩ := hν
  haveI : Representation.IsIrreducible ρ := hirr
  haveI : Nontrivial V := nontrivial_of_isIrreducible ρ
  obtain ⟨c, hc⟩ := center_isScalar ρ hz
  have hch1 : ν 1 = (Module.finrank ℂ V : ℂ) := by
    rw [show ν 1 = (ν : H → ℂ) 1 from rfl, congrFun hchar 1, ρ.char_one]
  have hcht : ν z = (Module.finrank ℂ V : ℂ) * c := by
    rw [show ν z = (ν : H → ℂ) z from rfl, congrFun hchar z]
    change LinearMap.trace ℂ V (ρ z) = _
    rw [hc, map_smul, LinearMap.trace_id]
    simp [smul_eq_mul, mul_comm]
  have hc1 : c = 1 := by
    have hn : (Module.finrank ℂ V : ℂ) ≠ 0 :=
      Nat.cast_ne_zero.mpr (ne_of_gt Module.finrank_pos)
    refine mul_left_cancel₀ hn ?_
    rw [mul_one, ← hcht, hz1, hch1]
  intro h
  have hop : ρ (z * h) = ρ h := by
    have hz1' : ρ z = 1 := by
      rw [hc, hc1]
      exact one_smul ℂ (LinearMap.id : Module.End ℂ V)
    rw [map_mul, hz1', one_mul]
  rw [show ν (z * h) = (ν : H → ℂ) (z * h) from rfl,
    show ν h = (ν : H → ℂ) h from rfl,
    congrFun hchar (z * h), congrFun hchar h]
  change LinearMap.trace ℂ V (ρ (z * h)) = LinearMap.trace ℂ V (ρ h)
  rw [hop]

/-- `D.B = C_{U}(t₁) ∩ C_{U}(t₂) ≤ D.U`. -/
theorem BGData.B_le_U {G : Type} [Group G] [Finite G] (D : Work.GW2.BGData G) :
    D.B ≤ D.U :=
  (inf_le_left.trans inf_le_left : D.B ≤ D.U)

/-- `|H₀/U| = 2` in the case `|S| = 4` (`D.n = 2`). -/
theorem dTB_quotGroup_card_two {G : Type} [Group G] [Finite G] (D : Work.GW2.BGData G)
    (C : Sec2Ctx G) (hc : Work.GW2.C16.Compat D C) (hn : D.n = 2) :
    Nat.card (quotGroup C.P) = 2 := by
  rw [← Subgroup.index_eq_card (Work.GW2.C16.Uin C)]
  rw [rem31IndexUin D C hc, hn]

/-- `λ₂(t) = -1`. -/
theorem dTB_lamCF_two_apply_t {G : Type} [Group G] [Finite G] (C : Sec2Ctx G)
    {β₂ : quotGroup C.P →* ℂˣ}
    (h2 : Nat.card (quotGroup C.P) = 2) (hβ : β₂ ≠ 1) :
    lamCF C β₂ C.t = -1 :=
  lambda_apply_eq_neg_one_of_card_two C.P h2 hβ C.t_sq
    (fun h => C.t_not_mem_U (Subgroup.mem_subgroupOf.mp h))

/-- Every element of `H₀/U` is an involution when `|H₀/U| = 2`. -/
theorem dTB_quotGroup_sq_eq_one {G : Type} [Group G] [Finite G] (C : Sec2Ctx G)
    (h2 : Nat.card (quotGroup C.P) = 2) (x : quotGroup C.P) : x ^ 2 = 1 := by
  obtain ⟨a, -, ha2, huniv⟩ := exists_unique_ne_one_of_natCard_eq_two h2
  rcases huniv x with hx | hx
  · rw [hx, one_pow]
  · rw [hx, ha2]

/-- `λ₂` is its own inverse (every element of `H₀/U` has order two, so `λ₂` takes values
in `{±1}`, where inverse and value agree). -/
theorem dTB_lamCF_two_inv_eq {G : Type} [Group G] [Finite G] (C : Sec2Ctx G)
    {β₂ : quotGroup C.P →* ℂˣ}
    (h2 : Nat.card (quotGroup C.P) = 2) (hβ : β₂ ≠ 1) :
    lamCF C β₂⁻¹ = lamCF C β₂ := by
  refine ClassFunction.ext fun h => ?_
  have hy : (β₂ (quotMk C.P h))⁻¹ = β₂ (quotMk C.P h) := by
    have hsq : (β₂ (quotMk C.P h)) ^ 2 = 1 := by
      rw [← map_pow, dTB_quotGroup_sq_eq_one C h2 (quotMk C.P h), map_one]
    rcases units_sq_eq_one_eq_one_or_eq_neg_one (β₂ (quotMk C.P h)) hsq with h1 | h1
    · rw [h1, inv_one]
    · rw [h1, inv_neg, inv_one]
  simp only [lamCF, ClassFunction.compHom_apply, linearClassFunction_apply]
  rw [MonoidHom.inv_apply, hy]

/-- `lamCF C β` is multiplicative. -/
theorem lamCF_mul_apply {G : Type} [Group G] [Finite G] (C : Sec2Ctx G)
    (β : quotGroup C.P →* ℂˣ) (x y : ↥C.P.H0) :
    lamCF C β (x * y) = lamCF C β x * lamCF C β y := by
  simp only [lamCF, ClassFunction.compHom_apply, linearClassFunction_apply, map_mul,
    Units.val_mul]

/-- `λ₂(t·h) = -λ₂(h)` in the `|S| = 4` case. -/
theorem dTB_lamCF_two_t_mul {G : Type} [Group G] [Finite G] (C : Sec2Ctx G)
    {β₂ : quotGroup C.P →* ℂˣ}
    (h2 : Nat.card (quotGroup C.P) = 2) (hβ : β₂ ≠ 1) (h : ↥C.P.H0) :
    lamCF C β₂ (C.t * h) = -(lamCF C β₂ h) := by
  rw [lamCF_mul_apply C β₂ C.t h, dTB_lamCF_two_apply_t C h2 hβ]
  ring

/-- **Key value.**  For `ν ∈ Irr(H₀)` with `ν(t) = ν(1)`, the virtual character
`ν - λ₂ν` takes at `t·h` (`h ∈ U`) the value `2ν(h)`. -/
theorem sub_lam_two_mul_apply_t {G : Type} [Group G] [Finite G] (C : Sec2Ctx G)
    {β₂ : quotGroup C.P →* ℂˣ}
    (h2 : Nat.card (quotGroup C.P) = 2) (hβ : β₂ ≠ 1)
    {ν : ClassFunction ↥C.P.H0 ℂ} (hν : IsIrreducibleCharacter ν) (ht : ν C.t = ν 1)
    {h : ↥C.P.H0} (hhU : h ∈ C.P.U.subgroupOf C.P.H0) :
    (ν - lamCF C β₂ * ν) (C.t * h) = 2 * ν h := by
  have hth : ν (C.t * h) = ν h :=
    irrMulCentralAux (Sec2Ctx.t_mem_center C) hν ht h
  have hlam : lamCF C β₂ (C.t * h) = -1 := by
    have hB : lamCF C β₂ h = 1 :=
      Lambda.apply_eq_one_of_mem_U (P := C.P) (δ := lamCF C β₂) ⟨β₂, rfl⟩ hhU
    have hA : lamCF C β₂ (C.t * h) = -(lamCF C β₂ h) := dTB_lamCF_two_t_mul C h2 hβ h
    rw [hA, hB]
  simp only [ClassFunction.sub_apply, ClassFunction.mul_apply]
  rw [hth, hlam]
  ring

/-- `ν - λ₂ν` is `s`-invariant for `s`-invariant `ν` in the `|S| = 4` case. -/
theorem sconj_sub_lam_two_mul {G : Type} [Group G] [Finite G] (C : Sec2Ctx G)
    {β₂ : quotGroup C.P →* ℂˣ}
    (h2 : Nat.card (quotGroup C.P) = 2) (hβ : β₂ ≠ 1)
    {ν : ClassFunction ↥C.P.H0 ℂ} (hs : sconj C ν = ν) :
    sconj C (ν - lamCF C β₂ * ν) = ν - lamCF C β₂ * ν := by
  have h1 : sconj C (ν - lamCF C β₂ * ν) = sconj C ν - sconj C (lamCF C β₂ * ν) := by
    simp only [sconj, conjByH, ClassFunction.compHom_sub]
  have hslam : sconj C (lamCF C β₂ * ν) = lamCF C β₂ * sconj C ν := by
    rw [sconjLam C β₂ ν, dTB_lamCF_two_inv_eq C h2 hβ]
  rw [h1, hslam, hs]

open OddOrder.RepresentationTheory Work.GW2 Work.BG Work.GW2.C16 Work.GW2.C23 in
theorem deltaAtTB {G : Type} [Group G] [Finite G] [Fintype G] [Invertible (Nat.card G : ℂ)]
    (D : Work.GW2.BGData G) (C : Work.BG.Sec2Ctx G) [Invertible (Nat.card ↥C.P.H0 : ℂ)] :
    Work.GW2.C23.DeltaAtTBProp D C := by
  intro hc hn β₂ hβ ν hνS h hB
  obtain ⟨hν, hνs, hνt⟩ := hνS
  have h2 : Nat.card (quotGroup C.P) = 2 := dTB_quotGroup_card_two D C hc hn
  have hhU : (h : G) ∈ C.P.U :=
    hc.U_eq.symm ▸ BGData.B_le_U D hB
  have hhU' : h ∈ C.P.U.subgroupOf C.P.H0 := Subgroup.mem_subgroupOf.mpr hhU
  have hgU : C.t * h ∉ C.P.U.subgroupOf C.P.H0 := by
    intro hmem
    have hmem' : ((C.t * h : ↥C.P.H0) : G) ∈ C.P.U :=
      Subgroup.mem_subgroupOf.mp hmem
    have h1 : ((C.t * h : ↥C.P.H0) : G) * (h : G)⁻¹ ∈ C.P.U :=
      C.P.U.mul_mem hmem' (C.P.U.inv_mem hhU)
    have h2' : (C.t : G) ∈ C.P.U := by
      rw [show ((C.t * h : ↥C.P.H0) : G) = (C.t : G) * (h : G) from rfl, mul_assoc,
        mul_inv_cancel, mul_one] at h1
      exact h1
    exact C.t_not_mem_U h2'
  have hLirr : IsIrreducibleCharacter (lamCF C β₂ * ν) :=
    lambda_mul_irreducible C.P (lambdaInf_mem C.P β₂) hν
  have hbs := s02_bsValueT C ν (lamCF C β₂ * ν) hν hLirr ⟨β₂, rfl⟩ (C.t * h) hgU
  have hval : (ν - lamCF C β₂ * ν) (C.t * h) = 2 * ν h :=
    sub_lam_two_mul_apply_t C h2 hβ hν hνt hhU'
  have hterm2 : (ν - lamCF C β₂ * ν) (conjMulEquiv C.P C.s (C.t * h)) = 2 * ν h := by
    have hrfl : (ν - lamCF C β₂ * ν) (conjMulEquiv C.P C.s (C.t * h))
        = sconj C (ν - lamCF C β₂ * ν) (C.t * h) := rfl
    rw [hrfl, sconj_sub_lam_two_mul C h2 hβ hνs, hval]
  show ind C (ν - lamCF C β₂ * ν) ((C.t * h : ↥C.P.H0) : G) = 4 * ν h
  rw [hbs, hval, hterm2]
  ring

end Work.BG
