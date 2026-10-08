import Mathlib
import Submission.Work.Higman.MSA.l8_local
import Submission.Work.Higman.MSA.l8_BV
import Submission.Work.Higman.MSA.l8_betaV
import Submission.Work.Higman.MSA.l8_triv
import Submission.Work.Higman.powSub_C_eq_of_cover

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.style.haveILetI false

open scoped commutatorElement

namespace Work.Higman.MSA.L8

variable {P : Type} [Group P] [Finite P]

/-- `2 * 2 ^ (n - 1) = 2 ^ n` for `1 ≤ n`. -/
theorem two_mul_two_pow_sub_one {n : ℕ} (hn : 1 ≤ n) : 2 * 2 ^ (n - 1) = 2 ^ n := by
  rw [← pow_succ', show n - 1 + 1 = n from by omega]

/-- `(α * δ * β) ^ 2 ^ (e-1) = (α * β) ^ 2 ^ (e-1)` when `δ ∈ A ^ 2` and `α, β ∈ A`. -/
theorem pow_mul_mem_powSub_two {h : IsSuzuki2Grp P} {A C : Subgroup P} [hAn : A.Normal]
    (S : D h A C) {δ : P} (hδ : δ ∈ powSub A 2) {α β : P} (hα : α ∈ A) (hβ : β ∈ A) :
    (α * δ * β) ^ 2 ^ (S.e - 1) = (α * β) ^ 2 ^ (S.e - 1) := by
  have hδA : δ ∈ A := powSub_le (by norm_num) hδ
  have hc1 : Commute α δ := S.hA.abelian α hα δ hδA
  have hc2 : Commute δ β := S.hA.abelian δ hδA β hβ
  have hc3 : Commute α β := S.hA.abelian α hα β hβ
  have hc23 : Commute β δ := hc2.symm
  have hmove : (α * δ) * β = (α * β) * δ := by rw [mul_assoc, hc2, ← mul_assoc]
  rw [show α * δ * β = (α * δ) * β from rfl, hmove,
    Commute.mul_pow (Commute.mul_left hc1 hc23) (2 ^ (S.e - 1)),
    pow_two_pow_sub_one_eq_one_of_mem_powSub_two S hδ, mul_one]

/-- `⁅X⁻¹, Y⁆ ≡ ⁅Y, X⁆` modulo `A ^ 2` (for `X, Y ∈ C`). -/
theorem commutator_inv_eq_mod {h : IsSuzuki2Grp P} {A C : Subgroup P} [hAn : A.Normal]
    (S : D h A C) {X : P} (hX : X ∈ C) {Y : P} (hY : Y ∈ C) :
    ⁅X⁻¹, Y⁆ * ⁅Y, X⁆⁻¹ ∈ powSub A 2 := by
  have hYX : ⁅Y, X⁆ ∈ A := by
    have hmem : ⁅Y, X⁆ ∈ ⁅C, C⁆ := Subgroup.commutator_mem_commutator hY hX
    rwa [S.hCd] at hmem
  have hδ : ⁅⁅Y, X⁆⁻¹, X⁻¹⁆ ∈ powSub A 2 := by
    have hmem : ⁅⁅Y, X⁆⁻¹, X⁻¹⁆ ∈ ⁅A, C⁆ :=
      Subgroup.commutator_mem_commutator (A.inv_mem hYX) (C.inv_mem hX)
    rwa [commutator_A_C_eq S] at hmem
  have heq : ⁅X⁻¹, Y⁆ = ⁅Y, X⁆ * ⁅⁅Y, X⁆⁻¹, X⁻¹⁆ := by
    rw [commutatorElement_def, commutatorElement_def, commutatorElement_def]; group
  have hcomm : ⁅Y, X⁆ * ⁅⁅Y, X⁆⁻¹, X⁻¹⁆ = ⁅⁅Y, X⁆⁻¹, X⁻¹⁆ * ⁅Y, X⁆ :=
    S.hA.abelian _ hYX _ (powSub_le (by norm_num) hδ)
  rw [heq, hcomm, mul_assoc, mul_inv_cancel, mul_one]
  exact hδ

/-- `A = A ^ (2)` forces `A = ⊥` (in a finite `2`-group). -/
theorem eq_bot_of_powSub_two_eq_self {h : IsSuzuki2Grp P} {A C : Subgroup P} [hAn : A.Normal]
    (S : D h A C) (h2 : powSub A 2 = A) : A = ⊥ := by
  have hiter : ∀ k, A = powSub A (2 ^ k) := by
    intro k
    induction k with
    | zero => rw [pow_zero, powSub_one_eq]
    | succ k ih => rw [pow_succ, ← powSub_powSub S.hA.abelian, ← ih, h2]
  obtain ⟨n, hn⟩ := (IsPGroup.iff_card).mp (h.isPGroup.to_subgroup A)
  rw [hiter n]
  refine powSub_eq_bot_of_exp S.hA.abelian le_rfl fun x hx => ?_
  haveI : Fintype ↥A := Fintype.ofFinite _
  have hxA : orderOf (⟨x, hx⟩ : ↥A) ∣ 2 ^ n := by
    have hh := orderOf_dvd_card (x := (⟨x, hx⟩ : ↥A))
    rwa [← Nat.card_eq_fintype_card, hn] at hh
  have h1 : (⟨x, hx⟩ : ↥A) ^ 2 ^ n = 1 := orderOf_dvd_iff_pow_eq_one.mp hxA
  simpa [Subgroup.coe_pow] using congrArg (fun t : ↥A => (t : P)) h1

/-- **Higman's Lemma 8, the power map `sV`.**  The map `C/A → Ω₁(P)`, `uA ↦ u ^ (2 ^ e)`,
is `ξ`-equivariant with polar form `BV`, and it is a bijection (`hcard` supplies `|C/A| = |Ω₁|`). -/
theorem l8_sV {h : IsSuzuki2Grp P} {A C : Subgroup P} [hAn : A.Normal] (S : D h A C)
    (hcard : Nat.card (↥C ⧸ (A.subgroupOf C)) = Nat.card ↥(omega1 P)) :
    Function.Injective (sV S) ∧ Function.Surjective (sV S) ∧
    (sV S 1 = 1) ∧
    (∀ x : ↥C ⧸ (A.subgroupOf C),
      xiZ h (sV S x) = sV S (xiQuot h S.hA.map_eq S.hCinv x)) ∧
    (∀ x y : ↥C ⧸ (A.subgroupOf C), sV S (x * y) = sV S x * sV S y * BV S x y) := by
  have hs1 : sV S 1 = 1 := by
    apply Subtype.ext
    rw [show (1 : ↥C ⧸ (A.subgroupOf C)) = QuotientGroup.mk (1 : ↥C) from rfl, sV_mk]
    simp
  have hseq : ∀ x : ↥C ⧸ (A.subgroupOf C),
      xiZ h (sV S x) = sV S (xiQuot h S.hA.map_eq S.hCinv x) := by
    intro x
    obtain ⟨u, rfl⟩ := QuotientGroup.mk_surjective x
    apply Subtype.ext
    rw [xiZ_apply, sV_mk, xiQuot_mk, sV_mk, map_pow]
    simp only [xiSubAut_apply]
  have hseqpow : ∀ (k : ℕ) (x : ↥C ⧸ (A.subgroupOf C)),
      (xiZ h ^ k) (sV S x) = sV S ((xiQuot h S.hA.map_eq S.hCinv ^ k) x) := by
    intro k
    induction k with
    | zero => intro x; simp
    | succ k ih =>
        intro x
        rw [pow_succ', MulAut.mul_apply, ih, hseq]
        congr 1
        rw [pow_succ', MulAut.mul_apply]
  have hpol : ∀ x y : ↥C ⧸ (A.subgroupOf C),
      sV S (x * y) = sV S x * sV S y * BV S x y := by
    intro x y
    obtain ⟨u, rfl⟩ := QuotientGroup.mk_surjective x
    obtain ⟨v, rfl⟩ := QuotientGroup.mk_surjective y
    rw [← QuotientGroup.mk_mul]
    apply Subtype.ext
    rw [Subgroup.coe_mul, Subgroup.coe_mul, sV_mk, sV_mk, sV_mk,
      BV_rep S (QuotientGroup.mk u) (QuotientGroup.mk v) u v rfl rfl]
    simp only [Subgroup.coe_mul]
    have he : 1 ≤ S.e := S.he
    set X : P := ((u : ↥C) : P) with hXdef
    set Y : P := ((v : ↥C) : P) with hYdef
    have hXu : X ∈ C := u.2
    have hYv : Y ∈ C := v.2
    have hYXA : ⁅Y, X⁆ ∈ A := by
      have hmem : ⁅Y, X⁆ ∈ ⁅C, C⁆ := Subgroup.commutator_mem_commutator hYv hXu
      rwa [S.hCd] at hmem
    have hδ : ⁅⁅Y, X⁆⁻¹, X⁆ ∈ powSub A 2 := by
      have hmem : ⁅⁅Y, X⁆⁻¹, X⁆ ∈ ⁅A, C⁆ :=
        Subgroup.commutator_mem_commutator (A.inv_mem hYXA) hXu
      rwa [commutator_A_C_eq S] at hmem
    have hP : X * ⁅Y, X⁆ * X⁻¹ ∈ A := S.hA.normal.conj_mem ⁅Y, X⁆ hYXA X
    have hQ : X * X ∈ A := S.hC2 (by simpa [pow_two] using pow_mem_powSub (A := C) (n := 2) hXu)
    have hR : Y * Y ∈ A := S.hC2 (by simpa [pow_two] using pow_mem_powSub (A := C) (n := 2) hYv)
    have hXYA : ⁅X⁻¹, Y⁆ ∈ A := by
      have hmem : ⁅X⁻¹, Y⁆ ∈ ⁅C, C⁆ :=
        Subgroup.commutator_mem_commutator (C.inv_mem hXu) hYv
      rwa [S.hCd] at hmem
    have hmemX : X ^ 2 ^ S.e ∈ omega1 P :=
      pow_two_pow_mem_omega1 h S.hA S.hC2 S.he1 S.he hXu
    have hmemY : Y ^ 2 ^ S.e ∈ omega1 P :=
      pow_two_pow_mem_omega1 h S.hA S.hC2 S.he1 S.he hYv
    have hmemB : (⁅X⁻¹, Y⁆) ^ 2 ^ (S.e - 1) ∈ omega1 P :=
      mem_omega1_pow_two_pow_sub_one h S.hA S.he1 S.he hXYA
    have hm1 : ((X * ⁅Y, X⁆ * X⁻¹) * (X * X) * (Y * Y)) ^ 2 ^ (S.e - 1)
        = (X * ⁅Y, X⁆ * X⁻¹) ^ 2 ^ (S.e - 1) * (X * X) ^ 2 ^ (S.e - 1)
          * (Y * Y) ^ 2 ^ (S.e - 1) := by
      rw [Commute.mul_pow (Commute.mul_left
            (S.hA.abelian (X * ⁅Y, X⁆ * X⁻¹) hP (Y * Y) hR)
            (S.hA.abelian (X * X) hQ (Y * Y) hR)) (2 ^ (S.e - 1)),
        Commute.mul_pow (S.hA.abelian (X * ⁅Y, X⁆ * X⁻¹) hP (X * X) hQ) (2 ^ (S.e - 1))]
    have hm2 : (X * ⁅Y, X⁆ * X⁻¹) ^ 2 ^ (S.e - 1) = (⁅Y, X⁆) ^ 2 ^ (S.e - 1) := by
      rw [mul_commutator_inv_eq X ⁅Y, X⁆,
        Commute.mul_pow (S.hA.abelian ⁅Y, X⁆ hYXA _ (powSub_le (by norm_num) hδ))
          (2 ^ (S.e - 1)),
        pow_two_pow_sub_one_eq_one_of_mem_powSub_two S hδ, mul_one]
    have hm3 : (⁅Y, X⁆) ^ 2 ^ (S.e - 1) = (⁅X⁻¹, Y⁆) ^ 2 ^ (S.e - 1) :=
      (pow_eq_of_mul_inv_mem_powSub_two S hXYA hYXA (commutator_inv_eq_mod S hXu hYv)).symm
    have hm4 : (X * X) ^ 2 ^ (S.e - 1) = X ^ 2 ^ S.e := by
      rw [show X * X = X ^ 2 from (pow_two X).symm, ← pow_mul, two_mul_two_pow_sub_one he]
    have hm5 : (Y * Y) ^ 2 ^ (S.e - 1) = Y ^ 2 ^ S.e := by
      rw [show Y * Y = Y ^ 2 from (pow_two Y).symm, ← pow_mul, two_mul_two_pow_sub_one he]
    have hsq : (X * Y) ^ 2 = (X * ⁅Y, X⁆ * X⁻¹) * (X * X) * (Y * Y) := by
      rw [commutatorElement_def]; rw [pow_two]; group
    show (X * Y) ^ 2 ^ (S.e) = X ^ 2 ^ S.e * Y ^ 2 ^ S.e * (⁅X⁻¹, Y⁆) ^ 2 ^ (S.e - 1)
    rw [show (X * Y) ^ 2 ^ (S.e) = ((X * Y) ^ 2) ^ 2 ^ (S.e - 1) from by
          rw [← pow_mul, two_mul_two_pow_sub_one he],
      hsq, hm1, hm2, hm3, hm4, hm5,
      h.omega1_comm hmemB hmemX, mul_assoc, h.omega1_comm hmemB hmemY, ← mul_assoc]
  have hex : ∃ x : ↥C ⧸ (A.subgroupOf C), sV S x ≠ 1 := by
    by_contra hc
    push_neg at hc
    have hC2A2 : powSub C 2 ≤ powSub A 2 := by
      rw [powSub, Subgroup.closure_le]
      rintro z ⟨u, hu, rfl⟩
      have h1 : sV S (QuotientGroup.mk (⟨u, hu⟩ : ↥C)) = 1 := hc _
      have h2 := congrArg (fun t : ↥(omega1 P) => (t : P)) h1
      rw [sV_mk] at h2
      have h3 : (u : P) ^ 2 ∈ A := S.hC2 (pow_mem_powSub (A := C) hu)
      refine (S.hkey _ h3).mpr ?_
      rw [← pow_mul, two_mul_two_pow_sub_one S.he]
      exact h2
    rw [powSub_C_eq_of_cover h S.hA S.hCn S.hCinv S.hAC S.hCA S.hcover S.hC2 S.hCd S.hAne]
      at hC2A2
    exact S.hAne (eq_bot_of_powSub_two_eq_self S (le_antisymm (powSub_le (by norm_num)) hC2A2))
  have honto : Function.Surjective (sV S) := by
    intro w
    by_cases hw1 : w = 1
    · exact ⟨1, by rw [hs1, hw1]⟩
    · obtain ⟨x0, hx0⟩ := hex
      obtain ⟨k, hk⟩ := xi_trans_omega1 h (sV S x0).2 w.2
        (fun hh => hx0 (Subtype.ext hh)) (fun hh => hw1 (Subtype.ext hh))
      exact ⟨(xiQuot h S.hA.map_eq S.hCinv ^ k) x0, by
        apply Subtype.ext
        rw [← hseqpow k x0, xiZ_pow_coe, hk]⟩
  have hinj : Function.Injective (sV S) := by
    haveI : Fintype (↥C ⧸ (A.subgroupOf C)) := Fintype.ofFinite _
    haveI : Fintype ↥(omega1 P) := Fintype.ofFinite _
    exact (Fintype.bijective_iff_surjective_and_card (sV S)).mpr
      ⟨honto, by rw [← Nat.card_eq_fintype_card, ← Nat.card_eq_fintype_card]; exact hcard⟩ |>.1
  exact ⟨hinj, honto, hs1, hseq, hpol⟩

end Work.Higman.MSA.L8
