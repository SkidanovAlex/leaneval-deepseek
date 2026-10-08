import Mathlib
import Submission.Work.Higman.MSA.l8_local
import Submission.Work.Higman.MSA.l8_step1
import Submission.Work.Higman.MSA.l8_sV
import Submission.Work.Higman.MSA.l8_triv
import Submission.Work.Higman.H8.card_pow_of_irreducible
import Submission.Work.Higman.xi_pow_triv_omega1_iff
import Submission.Work.Higman.Fq_structure
import Submission.Work.Higman.powSub_C_eq_of_cover
import Submission.Work.Higman.SZ.model

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

/-! ## The power map `sV` is surjective (no cardinality input) -/

theorem sV_one {h : IsSuzuki2Grp P} {A C : Subgroup P} [hAn : A.Normal] (S : D h A C) :
    sV S 1 = 1 := by
  apply Subtype.ext
  rw [show (1 : ↥C ⧸ (A.subgroupOf C)) = QuotientGroup.mk (1 : ↥C) from rfl, sV_mk]
  simp

theorem sV_xi {h : IsSuzuki2Grp P} {A C : Subgroup P} [hAn : A.Normal] (S : D h A C)
    (x : ↥C ⧸ (A.subgroupOf C)) :
    xiZ h (sV S x) = sV S (xiQuot h S.hA.map_eq S.hCinv x) := by
  obtain ⟨u, rfl⟩ := QuotientGroup.mk_surjective x
  apply Subtype.ext
  rw [xiZ_apply, sV_mk, xiQuot_mk, sV_mk, map_pow]
  simp only [xiSubAut_apply]

theorem sV_xi_pow {h : IsSuzuki2Grp P} {A C : Subgroup P} [hAn : A.Normal] (S : D h A C)
    (k : ℕ) (x : ↥C ⧸ (A.subgroupOf C)) :
    (xiZ h ^ k) (sV S x) = sV S ((xiQuot h S.hA.map_eq S.hCinv ^ k) x) := by
  induction k with
  | zero => simp
  | succ k ih =>
      rw [pow_succ', MulAut.mul_apply, ih, sV_xi, pow_succ', MulAut.mul_apply]

/-- `sV` is onto: its (non-trivial) image is `ξ`-invariant, hence all of `Ω₁(P)`. -/
theorem sV_surjective {h : IsSuzuki2Grp P} {A C : Subgroup P} [hAn : A.Normal] (S : D h A C) :
    Function.Surjective (sV S) := by
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
  intro w
  by_cases hw1 : w = 1
  · exact ⟨1, by rw [sV_one, hw1]⟩
  · obtain ⟨x0, hx0⟩ := hex
    obtain ⟨k, hk⟩ := xi_trans_omega1 h (sV S x0).2 w.2
      (fun hh => hx0 (Subtype.ext hh)) (fun hh => hw1 (Subtype.ext hh))
    exact ⟨(xiQuot h S.hA.map_eq S.hCinv ^ k) x0, by
      apply Subtype.ext
      rw [← sV_xi_pow S k x0, xiZ_pow_coe, hk]⟩

/-! ## The order of `ξ` on `Ω₁(P)` -/

/-- The order of the induced automorphism of `Ω₁(P)` is `|Ω₁(P)| - 1`. -/
theorem orderOf_xiZ_eq (h : IsSuzuki2Grp P) :
    orderOf (xiZ h) = Nat.card ↥(omega1 P) - 1 := by
  have hpow : (xiZ h) ^ (Nat.card ↥(omega1 P) - 1) = 1 := by
    refine MulEquiv.ext (fun z => ?_)
    apply Subtype.ext
    show (((xiZ h) ^ (Nat.card ↥(omega1 P) - 1)) z : P) = (z : P)
    rw [xiZ_pow_coe]
    exact (xi_pow_triv_omega1_iff h (Nat.card ↥(omega1 P) - 1)).mpr dvd_rfl z z.2
  refine Nat.dvd_antisymm (orderOf_dvd_iff_pow_eq_one.mpr hpow) ?_
  refine (xi_pow_triv_omega1_iff h (orderOf (xiZ h))).mp ?_
  intro z hz
  have h2 : (((xiZ h) ^ (orderOf (xiZ h))) ⟨z, hz⟩ : P) = z := by
    rw [pow_orderOf_eq_one]
    rfl
  rw [xiZ_pow_coe] at h2
  exact h2

/-! ## The order of `ξ` on `V = C/A` -/

/-- The iterated form of `xiQuot` on a representative. -/
theorem xiQuot_pow_mk {h : IsSuzuki2Grp P} {A C : Subgroup P} [hAn : A.Normal]
    (S : D h A C) (k : ℕ) (u : ↥C) :
    ((xiQuot h S.hA.map_eq S.hCinv) ^ k) (QuotientGroup.mk u)
      = QuotientGroup.mk (((xiSubAut h S.hCinv) ^ k) u) := by
  induction k with
  | zero => simp
  | succ k ih =>
      rw [pow_succ', MulAut.mul_apply, ih, xiQuot_mk, pow_succ', MulAut.mul_apply]

/-- `ξ ^ k` acts trivially on `C/A` when it does so elementwise. -/
theorem xiQuot_pow_eq_one_of_triv {h : IsSuzuki2Grp P} {A C : Subgroup P} [hAn : A.Normal]
    (S : D h A C) {k : ℕ}
    (hk : ∀ x ∈ C, (h.xi ^ k) x * x⁻¹ ∈ A) :
    (xiQuot h S.hA.map_eq S.hCinv) ^ k = 1 := by
  refine MulEquiv.ext (fun y => ?_)
  obtain ⟨u, rfl⟩ := QuotientGroup.mk_surjective y
  rw [xiQuot_pow_mk S k u]
  show QuotientGroup.mk (((xiSubAut h S.hCinv) ^ k) u) = QuotientGroup.mk u
  rw [QuotientGroup.eq, Subgroup.mem_subgroupOf]
  have hb : (u : P) * ((h.xi ^ k) (u : P))⁻¹ ∈ A := by
    have h1 := hk (u : P) u.2
    have h2 : ((h.xi ^ k) (u : P) * (u : P)⁻¹)⁻¹ ∈ A := A.inv_mem h1
    rwa [mul_inv_rev, inv_inv] at h2
  have hconj := Subgroup.Normal.conj_mem hAn _ hb (((h.xi ^ k) (u : P))⁻¹)
  have hgoal : ((h.xi ^ k) (u : P))⁻¹ * (u : P) ∈ A := by
    have h3 : ((h.xi ^ k) (u : P))⁻¹ * ((u : P) * ((h.xi ^ k) (u : P))⁻¹) * ((h.xi ^ k) (u : P))⁻¹⁻¹
        = ((h.xi ^ k) (u : P))⁻¹ * (u : P) := by group
    rwa [h3] at hconj
  have hcoe : (((((xiSubAut h S.hCinv) ^ k) u)⁻¹ * u : ↥C) : P)
      = ((h.xi ^ k) (u : P))⁻¹ * (u : P) := by
    simp only [Subgroup.coe_mul, Subgroup.coe_inv]
    rw [xiSubAut_pow_apply]
  rw [hcoe]
  exact hgoal

/-- `orderOf ξV` divides `k` whenever `ξ ^ k` acts trivially on `C/A`. -/
theorem orderOf_xiQuot_dvd {h : IsSuzuki2Grp P} {A C : Subgroup P} [hAn : A.Normal]
    (S : D h A C) {k : ℕ} (hk : ∀ x ∈ C, (h.xi ^ k) x * x⁻¹ ∈ A) :
    orderOf (xiQuot h S.hA.map_eq S.hCinv) ∣ k :=
  orderOf_dvd_iff_pow_eq_one.mpr (xiQuot_pow_eq_one_of_triv S hk)

/-- `|Ω₁(P)| - 1` divides `orderOf ξV` (reverse divisibility, via surjectivity of `sV`). -/
theorem card_sub_one_dvd_orderOf_xiQuot {h : IsSuzuki2Grp P} {A C : Subgroup P}
    [hAn : A.Normal] (S : D h A C) :
    (Nat.card ↥(omega1 P) - 1) ∣ orderOf (xiQuot h S.hA.map_eq S.hCinv) := by
  set k : ℕ := orderOf (xiQuot h S.hA.map_eq S.hCinv) with hk
  have hpow : (xiZ h) ^ k = 1 := by
    refine MulEquiv.ext (fun w => ?_)
    obtain ⟨x, rfl⟩ := sV_surjective S w
    rw [sV_xi_pow S k x]
    have h1 : (xiQuot h S.hA.map_eq S.hCinv) ^ k = 1 := by
      rw [hk]; exact pow_orderOf_eq_one _
    rw [h1]
    rfl
  rw [← orderOf_xiZ_eq h]
  exact orderOf_dvd_iff_pow_eq_one.mpr hpow

/-- The order of the induced automorphism of `C/A` is `2 ^ n - 1`. -/
theorem orderOf_xiQuot_eq {h : IsSuzuki2Grp P} {A C : Subgroup P} [hAn : A.Normal]
    (S : D h A C) {n : ℕ} (hn : Nat.card ↥(omega1 P) = 2 ^ n)
    (hk : ∀ x ∈ C, (h.xi ^ (Nat.card ↥(omega1 P) - 1)) x * x⁻¹ ∈ A) :
    orderOf (xiQuot h S.hA.map_eq S.hCinv) = 2 ^ n - 1 := by
  have h1 : orderOf (xiQuot h S.hA.map_eq S.hCinv) ∣ Nat.card ↥(omega1 P) - 1 :=
    orderOf_xiQuot_dvd S hk
  have h2 : (Nat.card ↥(omega1 P) - 1) ∣ orderOf (xiQuot h S.hA.map_eq S.hCinv) :=
    card_sub_one_dvd_orderOf_xiQuot S
  have heq : orderOf (xiQuot h S.hA.map_eq S.hCinv) = Nat.card ↥(omega1 P) - 1 :=
    Nat.dvd_antisymm h1 h2
  rw [heq, hn]

/-- **The `m = n` count**: `|C/A| = 2 ^ n`. -/
theorem card_quot_eq {h : IsSuzuki2Grp P} {A C : Subgroup P} [hAn : A.Normal]
    (S : D h A C) {n : ℕ} (hn : Nat.card ↥(omega1 P) = 2 ^ n) (hn2 : 2 ≤ n)
    (hk : ∀ x ∈ C, (h.xi ^ (Nat.card ↥(omega1 P) - 1)) x * x⁻¹ ∈ A) :
    Nat.card (↥C ⧸ (A.subgroupOf C)) = 2 ^ n := by
  letI hCG : CommGroup (↥C ⧸ (A.subgroupOf C)) :=
    { (inferInstance : Group (↥C ⧸ (A.subgroupOf C))) with mul_comm := quot_comm S.hCd }
  letI hMod : Module (ZMod 2) (Additive (↥C ⧸ (A.subgroupOf C))) :=
    Work.Higman.SZ.module_zmod2_of_sq_one (quot_sq_one S.hC2)
  haveI hNtr : Nontrivial (↥C ⧸ (A.subgroupOf C)) := by
    obtain ⟨x, hx⟩ : ∃ x : ↥C, (x : P) ∉ A := by
      by_contra hcon
      push_neg at hcon
      exact S.hCA (le_antisymm S.hAC (fun y hy => hcon ⟨y, hy⟩))
    refine ⟨⟨QuotientGroup.mk x, (1 : ↥C ⧸ (A.subgroupOf C)), ?_⟩⟩
    intro hcon
    apply hx
    rw [← QuotientGroup.mk_one (A.subgroupOf C)] at hcon
    have h1 : (x)⁻¹ * 1 ∈ A.subgroupOf C := QuotientGroup.eq.mp hcon
    rw [Subgroup.mem_subgroupOf] at h1
    have h2 : ((x : P))⁻¹ ∈ A := by simpa using h1
    simpa using A.inv_mem h2
  haveI : Finite (Additive (↥C ⧸ (A.subgroupOf C))) := inferInstance
  haveI : Nontrivial (Additive (↥C ⧸ (A.subgroupOf C))) := inferInstance
  have hξ : orderOf (xiQuot h S.hA.map_eq S.hCinv) = 2 ^ n - 1 := orderOf_xiQuot_eq S hn hk
  let ζV : Additive (↥C ⧸ (A.subgroupOf C)) ≃ₗ[ZMod 2]
      Additive (↥C ⧸ (A.subgroupOf C)) :=
    (xiQuot h S.hA.map_eq S.hCinv).toAdditive.toLinearEquiv (by
      intro c x
      fin_cases c
      · show (xiQuot h S.hA.map_eq S.hCinv).toAdditive ((0 : ZMod 2) • x)
            = (0 : ZMod 2) • (xiQuot h S.hA.map_eq S.hCinv).toAdditive x
        simp
      · show (xiQuot h S.hA.map_eq S.hCinv).toAdditive ((1 : ZMod 2) • x)
            = (1 : ZMod 2) • (xiQuot h S.hA.map_eq S.hCinv).toAdditive x
        simp)
  have hζVapply : ∀ x : Additive (↥C ⧸ (A.subgroupOf C)),
      ζV x = Additive.ofMul (xiQuot h S.hA.map_eq S.hCinv (Additive.toMul x)) := fun _ => rfl
  have hζVpow : ∀ (k : ℕ) (x : Additive (↥C ⧸ (A.subgroupOf C))),
      (ζV ^ k) x = Additive.ofMul ((xiQuot h S.hA.map_eq S.hCinv ^ k) (Additive.toMul x)) := by
    intro k
    induction k with
    | zero => intro x; rfl
    | succ k ih =>
        intro x
        rw [pow_succ, LinearEquiv.mul_apply, ih, hζVapply, toMul_ofMul, pow_succ]
        rfl
  have hdcmp : ∀ (k : ℕ), ζV ^ k = 1 ↔ (xiQuot h S.hA.map_eq S.hCinv) ^ k = 1 := by
    intro k
    constructor
    · intro h1
      refine MulEquiv.ext (fun v => ?_)
      have h2 : (ζV ^ k) (Additive.ofMul v) = Additive.ofMul v := by
        rw [h1]; rfl
      rw [hζVpow] at h2
      exact Additive.ofMul.injective h2
    · intro h1
      refine LinearEquiv.ext (fun x => ?_)
      rw [hζVpow, h1]
      rfl
  have horder : orderOf ζV = 2 ^ n - 1 := by
    have h2 : orderOf ζV = orderOf (xiQuot h S.hA.map_eq S.hCinv) :=
      Nat.dvd_antisymm (orderOf_dvd_iff_pow_eq_one.mpr ((hdcmp _).mpr (pow_orderOf_eq_one _)))
        (orderOf_dvd_iff_pow_eq_one.mpr ((hdcmp _).mp (pow_orderOf_eq_one _)))
    rw [h2, hξ]
  refine H8.card_pow_of_irreducible (V := Additive (↥C ⧸ (A.subgroupOf C)))
    (by omega : 1 ≤ n) ζV horder ?_
  intro U hU
  let E : Subgroup ↥C :=
    { carrier := {u : ↥C | Additive.ofMul (QuotientGroup.mk u) ∈ U}
      one_mem' := by
        show Additive.ofMul (QuotientGroup.mk (1 : ↥C)) ∈ U
        rw [QuotientGroup.mk_one]
        exact U.zero_mem
      mul_mem' := by
        intro a b ha hb
        show Additive.ofMul (QuotientGroup.mk (a * b)) ∈ U
        rw [QuotientGroup.mk_mul, ofMul_mul]
        exact U.add_mem ha hb
      inv_mem' := by
        intro a ha
        show Additive.ofMul (QuotientGroup.mk (s := A.subgroupOf C) a⁻¹) ∈ U
        have h2 : QuotientGroup.mk (s := A.subgroupOf C) a⁻¹
            = QuotientGroup.mk (s := A.subgroupOf C) a := by
          rw [QuotientGroup.mk_inv]
          exact inv_eq_of_mul_eq_one_right
            (quot_sq_one S.hC2 (QuotientGroup.mk (s := A.subgroupOf C) a))
        rwa [h2] }
  have hEinv_le : E.map (xiSubAut h S.hCinv) ≤ E := by
    rintro x ⟨u, hu, rfl⟩
    show Additive.ofMul (QuotientGroup.mk ((xiSubAut h S.hCinv) u)) ∈ U
    rw [(xiQuot_mk S.hA.map_eq S.hCinv u).symm]
    have h1 : ζV (Additive.ofMul (QuotientGroup.mk u))
        = Additive.ofMul (xiQuot h S.hA.map_eq S.hCinv (QuotientGroup.mk u)) := by
      rw [hζVapply]; rfl
    rw [← h1]
    exact hU _ hu
  have hEinv : E.map (xiSubAut h S.hCinv) = E := by
    refine Subgroup.eq_of_le_of_card_ge hEinv_le ?_
    rw [Subgroup.card_map_of_injective (xiSubAut h S.hCinv).injective]
  let D : Subgroup P := E.map (Subgroup.subtype C)
  have hAD : A ≤ D := by
    intro a ha
    refine Subgroup.mem_map.mpr ⟨⟨a, S.hAC ha⟩, ?_, rfl⟩
    show Additive.ofMul (QuotientGroup.mk (⟨a, S.hAC ha⟩ : ↥C)) ∈ U
    have h1 : (QuotientGroup.mk (⟨a, S.hAC ha⟩ : ↥C) : ↥C ⧸ (A.subgroupOf C)) = 1 := by
      rw [← QuotientGroup.mk_one (A.subgroupOf C), QuotientGroup.eq, Subgroup.mem_subgroupOf]
      simpa using A.inv_mem ha
    rw [h1]
    exact U.zero_mem
  have hDC : D ≤ C := by
    rintro x ⟨u, -, rfl⟩
    exact u.2
  have hDinv : D.map (h.xi : MulAut P).toMonoidHom = D := by
    have hcomp : (h.xi : MulAut P).toMonoidHom.comp (Subgroup.subtype C)
        = (Subgroup.subtype C).comp ((xiSubAut h S.hCinv : ↥C ≃* ↥C) : ↥C →* ↥C) := by
      ext u
      rfl
    calc D.map (h.xi : MulAut P).toMonoidHom
        = (E.map (Subgroup.subtype C)).map (h.xi : MulAut P).toMonoidHom := rfl
      _ = E.map ((h.xi : MulAut P).toMonoidHom.comp (Subgroup.subtype C)) := by
          rw [Subgroup.map_map]
      _ = E.map ((Subgroup.subtype C).comp ((xiSubAut h S.hCinv : ↥C ≃* ↥C) : ↥C →* ↥C)) := by
          rw [hcomp]
      _ = (E.map (xiSubAut h S.hCinv)).map (Subgroup.subtype C) := by rw [Subgroup.map_map]
      _ = E.map (Subgroup.subtype C) := by rw [hEinv]
      _ = D := rfl
  have hPC : ⁅(⊤ : Subgroup P), C⁆ ≤ A :=
    commutator_top_C_le h S.hA S.hCn S.hCinv S.hAC S.hCA S.hcover S.hC2 S.hCd S.hAne
  have hDnorm : D.Normal := normal_of_le_of_contains hPC hAD hDC
  rcases S.hcover D hDnorm hDinv hAD hDC with hDA | hDC'
  · left
    refine le_antisymm ?_ bot_le
    intro v hv
    rw [Submodule.mem_bot]
    obtain ⟨u, hu⟩ := QuotientGroup.mk_surjective v
    have huE : u ∈ E := by
      show Additive.ofMul (QuotientGroup.mk u) ∈ U
      rw [hu]
      exact hv
    have hmemD : (u : P) ∈ D := Subgroup.mem_map.mpr ⟨u, huE, rfl⟩
    rw [hDA] at hmemD
    have h1 : (QuotientGroup.mk u : ↥C ⧸ (A.subgroupOf C)) = 1 := by
      rw [← QuotientGroup.mk_one (A.subgroupOf C), QuotientGroup.eq, Subgroup.mem_subgroupOf]
      simpa using hmemD
    rw [← hu, h1]
    rfl
  · right
    refine le_antisymm le_top ?_
    intro v _
    obtain ⟨u, hu⟩ := QuotientGroup.mk_surjective v
    have hmemD : (u : P) ∈ D := by
      rw [hDC']; exact u.2
    obtain ⟨u', hu'E, hu'eq⟩ := Subgroup.mem_map.mp hmemD
    have huE : u ∈ E := by
      have h2 : u' = u := Subtype.ext hu'eq
      rwa [← h2]
    have h3 : Additive.ofMul (QuotientGroup.mk u) ∈ U := huE
    rw [hu] at h3
    exact h3



/-- **The `m = n` count of Higman's Lemma 8**: `|C/A| = |Ω₁(P)|`. -/
theorem l8_quot_card {h : IsSuzuki2Grp P} {A C : Subgroup P} [hAn : A.Normal]
    (S : D h A C) {n : ℕ} (hn : Nat.card ↥(omega1 P) = 2 ^ n) (hn2 : 2 ≤ n)
    (htriv : ∀ x ∈ C, (h.xi ^ (Nat.card ↥(omega1 P) - 1)) x * x⁻¹ ∈ A) :
    Nat.card (↥C ⧸ (A.subgroupOf C)) = Nat.card ↥(omega1 P) := by
  rw [card_quot_eq S hn hn2 htriv, hn]

end Work.Higman.MSA.L8
