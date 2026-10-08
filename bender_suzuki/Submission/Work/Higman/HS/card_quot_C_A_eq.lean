import Mathlib
import Submission.Work.Higman.HS.xi_pow_triv_quot_C_A
import Submission.Work.Higman.Q3.finrank_dvd_of_irreducible_pow_sub_one
import Submission.Work.Higman.H8.card_pow_of_irreducible
import Submission.Work.Higman.H8.card_sub_one_dvd_xi
import Submission.Work.Higman.NSM.redcase
import Submission.Work.Higman.MSA.l8_local
import Submission.Work.Higman.MSA.l8_quot_irred
import Submission.Work.Higman.SZ.model

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

open scoped commutatorElement

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.style.haveILetI false

namespace Work.Higman.HS

variable {P : Type} [Group P] [Finite P]

/-! ## Two structural facts about the quotient `C/A`

Throughout, `A ≤ C` are subgroups of a Suzuki 2-group `P` with `[P,P] = A`, so that every
subgroup lying between `A` and `C` is automatically normal. -/

/-- **`C/A` is abelian** when `[P,P] = A`: `[C,C] ≤ [P,P] = A`. -/
theorem quot_comm_of_commutator_top_eq (h : IsSuzuki2Grp P) {A C : Subgroup P} [hAn : A.Normal]
    (hGs : ⁅(⊤ : Subgroup P), ⊤⁆ = A) :
    ∀ x y : ↥C ⧸ (A.subgroupOf C), x * y = y * x := by
  have hCC : ⁅C, C⁆ ≤ A :=
    (Subgroup.commutator_mono (le_top : C ≤ ⊤) (le_top : C ≤ ⊤)).trans (le_of_eq hGs)
  intro x y
  induction x using QuotientGroup.induction_on with
  | _ a =>
    induction y using QuotientGroup.induction_on with
    | _ b =>
      rw [← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul, QuotientGroup.eq]
      rw [Subgroup.mem_subgroupOf]
      have key : (((a * b)⁻¹ * (b * a) : ↥C) : P) = ⁅(b : P)⁻¹, (a : P)⁻¹⁆ := by
        simp only [Subgroup.coe_mul, Subgroup.coe_inv, commutatorElement_def]
        group
      rw [key]
      exact hCC (Subgroup.commutator_mem_commutator (C.inv_mem b.2) (C.inv_mem a.2))

/-- **Irreducibility of `C/A`** under the induced `ξ`-action, when `[P,P] = A` and the only
`ξ`-invariant normal subgroups between `A` and `C` are `A` and `C`: the only `ξ`-invariant
subgroups of the quotient `C/A` are `⊥` and `⊤`.

This is `Work.Higman.MSA.l8_quot_irred` with the normality of the intermediate subgroups
supplied by `[P,P] = A` (instead of by `[C,C] = A`). -/
theorem quot_irred_of_commutator_top_eq {P : Type} [Group P] [Finite P]
    {h : IsSuzuki2Grp P} {A C : Subgroup P} [hAn : A.Normal]
    (hAinv : A.map (h.xi : MulAut P).toMonoidHom = A)
    (hCinv : C.map (h.xi : MulAut P).toMonoidHom = C)
    (hAC : A ≤ C) (hGs : ⁅(⊤ : Subgroup P), ⊤⁆ = A)
    (hcover : ∀ D : Subgroup P, D.Normal → D.map (h.xi : MulAut P).toMonoidHom = D →
      A ≤ D → D ≤ C → D = A ∨ D = C)
    {K : Subgroup (↥C ⧸ (A.subgroupOf C))}
    (hK : K.map (Work.Higman.MSA.L8.xiQuot h hAinv hCinv).toMonoidHom = K) :
    K = ⊥ ∨ K = ⊤ := by
  have hW : ∀ v ∈ K, Work.Higman.MSA.L8.xiQuot h hAinv hCinv v ∈ K := by
    intro v hv
    have h1 := Subgroup.mem_map_of_mem (Work.Higman.MSA.L8.xiQuot h hAinv hCinv).toMonoidHom hv
    rwa [hK] at h1
  set D : Subgroup ↥C := K.comap (QuotientGroup.mk' (A.subgroupOf C)) with hD
  have hmemD : ∀ u : ↥C, u ∈ D ↔ QuotientGroup.mk' (A.subgroupOf C) u ∈ K := fun u => Iff.rfl
  set Dp : Subgroup P := D.map C.subtype with hDp
  have hAD : (A.subgroupOf C) ≤ D := by
    intro x hx
    rw [hmemD]
    have hx1 : QuotientGroup.mk' (A.subgroupOf C) x = 1 := by
      rw [QuotientGroup.mk'_apply]
      exact (QuotientGroup.eq_one_iff x).mpr hx
    rw [hx1]
    exact K.one_mem
  have hADp : A ≤ Dp := by
    intro a ha
    rw [hDp]
    exact Subgroup.mem_map.mpr ⟨⟨a, hAC ha⟩, hAD (Subgroup.mem_subgroupOf.mpr ha), rfl⟩
  have hDpC : Dp ≤ C := by
    rw [hDp]
    exact Subgroup.map_subtype_le D
  have hDpinv_le : Dp.map (h.xi : MulAut P).toMonoidHom ≤ Dp := by
    rw [Subgroup.map_le_iff_le_comap]
    intro x hx
    obtain ⟨d, hd, rfl⟩ := Subgroup.mem_map.mp hx
    rw [hDp]
    refine Subgroup.mem_map.mpr ⟨(Work.Higman.MSA.L8.xiSubAut h hCinv d : ↥C), ?_, rfl⟩
    rw [hmemD] at hd ⊢
    have h1 : Work.Higman.MSA.L8.xiQuot h hAinv hCinv
        (QuotientGroup.mk' (A.subgroupOf C) d) ∈ K := hW _ hd
    simpa [QuotientGroup.mk'_apply, Work.Higman.MSA.l8_xiQuot_mk] using h1
  have hDpinv : Dp.map (h.xi : MulAut P).toMonoidHom = Dp :=
    Subgroup.eq_of_le_of_card_ge hDpinv_le
      (le_of_eq (Subgroup.card_map_of_injective (h.xi : MulAut P).injective).symm)
  have hKD : K = D.map (QuotientGroup.mk' (A.subgroupOf C)) := by
    ext v
    constructor
    · intro hv
      obtain ⟨u, rfl⟩ := QuotientGroup.mk'_surjective (A.subgroupOf C) v
      exact ⟨u, (hmemD u).mpr hv, rfl⟩
    · rintro ⟨u, hu, rfl⟩
      exact (hmemD u).mp hu
  have hDpn : Dp.Normal := by
    refine Subgroup.Normal.of_commutator_le P ?_
    rw [show _root_.commutator P = ⁅(⊤ : Subgroup P), ⊤⁆ from rfl, hGs]
    exact hADp
  rcases hcover Dp hDpn hDpinv hADp hDpC with hh | hh
  · left
    have hmap : D.map C.subtype = (A.subgroupOf C).map C.subtype := by
      rw [← hDp, hh, Subgroup.map_subgroupOf_eq_of_le hAC]
    have hDA : D = A.subgroupOf C := Subgroup.map_injective C.subtype_injective hmap
    rw [hKD, hDA, Subgroup.map_eq_bot_iff]
    intro x hx
    rw [QuotientGroup.ker_mk']
    exact hx
  · right
    have hDtop : D = ⊤ := by
      rw [Subgroup.eq_top_iff']
      intro x
      have hx : C.subtype x ∈ Dp := by rw [hh]; exact x.2
      rw [hDp] at hx
      obtain ⟨d, hd, hdx⟩ := Subgroup.mem_map.mp hx
      rwa [C.subtype_injective hdx] at hd
    rw [hKD, hDtop, Subgroup.map_top]
    exact MonoidHom.range_eq_top.mpr (QuotientGroup.mk'_surjective (A.subgroupOf C))

/-- **The easy half of the `m = n` count.**  With `A ≤ C`, `[P,P] = A`, `C² ≤ A`, `C/A` a
minimal normal `ξ`-section and `ξ ^ (|Ω₁(P)| - 1)` trivial on `C/A`, the cardinality of `C/A`
divides `|Ω₁(P)|`.

`C/A` is an elementary abelian `𝔽₂`-module which is irreducible for the induced action of `ξ`,
and `ξ` acts on it with order dividing `|Ω₁(P)| - 1 = 2ⁿ - 1`; hence `finrank 𝔽₂ (C/A) ∣ n`, so
`|C/A| = 2 ^ finrank` divides `2ⁿ = |Ω₁(P)|`. -/
theorem card_quot_dvd_omega1_aux (h : IsSuzuki2Grp P) {A C : Subgroup P} [hAn : A.Normal]
    (hAinv : A.map (h.xi : MulAut P).toMonoidHom = A)
    (hCinv : C.map (h.xi : MulAut P).toMonoidHom = C)
    (hAC : A ≤ C) (hCA : A ≠ C)
    (hGs : ⁅(⊤ : Subgroup P), ⊤⁆ = A)
    (hcover : ∀ D : Subgroup P, D.Normal → D.map (h.xi : MulAut P).toMonoidHom = D →
      A ≤ D → D ≤ C → D = A ∨ D = C)
    (hC2 : Work.Higman.powSub C 2 ≤ A)
    (hstep : ∀ x ∈ C, (h.xi ^ (Nat.card ↥(Work.Higman.omega1 P) - 1)) x * x⁻¹ ∈ A) :
    Nat.card (↥C ⧸ (A.subgroupOf C)) ∣ Nat.card ↥(Work.Higman.omega1 P) := by
  classical
  -- the abelian group structure of `C/A` and its `𝔽₂`-module structure
  letI : CommGroup (↥C ⧸ (A.subgroupOf C)) :=
    { (inferInstance : Group (↥C ⧸ (A.subgroupOf C))) with
      mul_comm := quot_comm_of_commutator_top_eq h hGs }
  have hV2 : ∀ x : ↥C ⧸ (A.subgroupOf C), x * x = 1 :=
    fun x => Work.Higman.MSA.L8.quot_sq_one (A := A) (C := C) hC2 x
  letI : Module (ZMod 2) (Additive (↥C ⧸ (A.subgroupOf C))) :=
    Work.Higman.SZ.module_zmod2_of_sq_one (G := ↥C ⧸ (A.subgroupOf C)) hV2
  -- `C/A` is non-trivial
  have hex : ∃ y : ↥C ⧸ (A.subgroupOf C), y ≠ 1 := by
    obtain ⟨x, hxC, hxA⟩ : ∃ x ∈ C, x ∉ A := by
      by_contra hcon
      push Not at hcon
      exact hCA (le_antisymm hAC hcon)
    refine ⟨QuotientGroup.mk (⟨x, hxC⟩ : ↥C), ?_⟩
    intro h1
    rw [QuotientGroup.eq_one_iff] at h1
    exact hxA (Subgroup.mem_subgroupOf.mp h1)
  haveI : Nontrivial (↥C ⧸ (A.subgroupOf C)) := ⟨⟨_, 1, hex.choose_spec⟩⟩
  haveI : Nontrivial (Additive (↥C ⧸ (A.subgroupOf C))) :=
    ⟨⟨Additive.ofMul hex.choose, 0, by
      intro hh
      exact hex.choose_spec (by simpa using congrArg Additive.toMul hh)⟩⟩
  -- `|Ω₁(P)| = 2 ^ n`
  obtain ⟨n, hn⟩ := h.exists_card_omega1_eq_two_pow
  have hn1 : 1 ≤ n := by
    have h4 : 4 ≤ 2 ^ n := by rw [← hn]; exact h.omega1_card_ge_four
    by_contra hc
    push Not at hc
    interval_cases n <;> norm_num at h4
  -- the induced linear automorphism of `C/A`
  set xiQ := Work.Higman.MSA.L8.xiQuot h hAinv hCinv with hxiQ
  let ξV : Additive (↥C ⧸ (A.subgroupOf C)) ≃ₗ[ZMod 2] Additive (↥C ⧸ (A.subgroupOf C)) :=
    xiQ.toAdditive.toLinearEquiv (by
      intro c x
      fin_cases c
      · show xiQ.toAdditive ((0 : ZMod 2) • x) = (0 : ZMod 2) • xiQ.toAdditive x
        simp
      · show xiQ.toAdditive ((1 : ZMod 2) • x) = (1 : ZMod 2) • xiQ.toAdditive x
        simp)
  have hξV : ∀ x : Additive (↥C ⧸ (A.subgroupOf C)),
      ξV x = Additive.ofMul (xiQ (Additive.toMul x)) := fun x => rfl
  have hξVpow : ∀ (k : ℕ) (x : Additive (↥C ⧸ (A.subgroupOf C))),
      (ξV ^ k) x = Additive.ofMul ((xiQ ^ k) (Additive.toMul x)) := by
    intro k
    induction k with
    | zero => intro x; simp
    | succ k ih =>
        intro x
        rw [pow_succ', pow_succ', LinearEquiv.mul_apply, ih x,
          hξV (Additive.ofMul ((xiQ ^ k) (Additive.toMul x))), toMul_ofMul]
        congr 1
  have hp : ξV ^ (2 ^ n - 1) = 1 := by
    have hord : orderOf xiQ ∣ Nat.card ↥(Work.Higman.omega1 P) - 1 :=
      Work.Higman.HS.orderOf_xiQuot_dvd hAinv hCinv hstep
    have h1 : xiQ ^ (Nat.card ↥(Work.Higman.omega1 P) - 1) = 1 :=
      orderOf_dvd_iff_pow_eq_one.mp hord
    ext x
    rw [← hn, hξVpow, h1]
    rfl
  -- irreducibility of `C/A`
  have hirr : ∀ U : Submodule (ZMod 2) (Additive (↥C ⧸ (A.subgroupOf C))),
      (∀ x ∈ U, ξV x ∈ U) → U = ⊥ ∨ U = ⊤ := by
    intro U hU
    set Usub : Subgroup (↥C ⧸ (A.subgroupOf C)) :=
      { carrier := {y | Additive.ofMul y ∈ U}
        mul_mem' := by
          intro a b ha hb
          have h1 : Additive.ofMul a + Additive.ofMul b ∈ U := U.add_mem ha hb
          rwa [show Additive.ofMul a + Additive.ofMul b = Additive.ofMul (a * b) from rfl] at h1
        one_mem' := by
          show (0 : Additive (↥C ⧸ (A.subgroupOf C))) ∈ U
          exact U.zero_mem
        inv_mem' := by
          intro a ha
          have h1 : -Additive.ofMul a ∈ U := U.neg_mem ha
          rwa [show -Additive.ofMul a = Additive.ofMul a⁻¹ from rfl] at h1 } with hUsub
    have hmem : ∀ y : ↥C ⧸ (A.subgroupOf C), y ∈ Usub ↔ Additive.ofMul y ∈ U := by
      intro y
      rw [hUsub]
      exact Iff.rfl
    have hpowU : ∀ k : ℕ, ∀ x : Additive (↥C ⧸ (A.subgroupOf C)), x ∈ U → (ξV ^ k) x ∈ U := by
      intro k
      induction k with
      | zero => intro x hx; simpa using hx
      | succ k ih =>
          intro x hx
          rw [pow_succ', LinearEquiv.mul_apply]
          exact hU _ (ih x hx)
    have hUsub_inv : Usub.map xiQ.toMonoidHom = Usub := by
      apply le_antisymm
      · intro y hy
        obtain ⟨v, hv, hvx⟩ := Subgroup.mem_map.mp hy
        rw [MulEquiv.coe_toMonoidHom] at hvx
        have h2 : Additive.ofMul (xiQ v) ∈ U := by
          have h3 : ξV (Additive.ofMul v) ∈ U := hU _ hv
          rwa [hξV (Additive.ofMul v), toMul_ofMul] at h3
        exact (hmem y).mpr (by rwa [hvx] at h2)
      · intro y hy
        rw [hmem] at hy
        refine Subgroup.mem_map.mpr ⟨(xiQ ^ (orderOf xiQ - 1)) y, ?_, ?_⟩
        · rw [hmem]
          have h1 : (ξV ^ (orderOf xiQ - 1)) (Additive.ofMul y) ∈ U := hpowU _ _ hy
          rwa [hξVpow, toMul_ofMul] at h1
        · have h5 : xiQ ((xiQ ^ (orderOf xiQ - 1)) y) = y := by
            rw [← MulAut.mul_apply, ← pow_succ', Nat.sub_add_cancel (orderOf_pos xiQ),
              pow_orderOf_eq_one, MulAut.one_apply]
          rw [MulEquiv.coe_toMonoidHom]
          exact h5
    rw [hxiQ] at hUsub_inv
    rcases quot_irred_of_commutator_top_eq hAinv hCinv hAC hGs hcover hUsub_inv with hbot | htop
    · left
      rw [Submodule.eq_bot_iff]
      intro x hx
      have h1 : Additive.toMul x ∈ Usub := (hmem _).mpr (ofMul_toMul x ▸ hx)
      rw [hbot, Subgroup.mem_bot] at h1
      rw [← ofMul_toMul x, h1]
      exact ofMul_eq_zero.mpr rfl
    · right
      rw [Submodule.eq_top_iff']
      intro x
      have h1 : Additive.toMul x ∈ Usub := by rw [htop]; exact Subgroup.mem_top _
      have h2 := (hmem _).mp h1
      rwa [ofMul_toMul] at h2
  -- the finrank divides `n`
  have hdvd : Module.finrank (ZMod 2) (Additive (↥C ⧸ (A.subgroupOf C))) ∣ n :=
    Work.Higman.Q3.finrank_dvd_of_irreducible_pow_sub_one ξV hn1 hp hirr
  have hcardV : Nat.card (↥C ⧸ (A.subgroupOf C))
      = 2 ^ Module.finrank (ZMod 2) (Additive (↥C ⧸ (A.subgroupOf C))) := by
    have h1 : Nat.card (Additive (↥C ⧸ (A.subgroupOf C)))
        = Nat.card (ZMod 2) ^ Module.finrank (ZMod 2) (Additive (↥C ⧸ (A.subgroupOf C))) :=
      Module.natCard_eq_pow_finrank
    rw [Nat.card_zmod] at h1
    rw [← h1]
    exact (Nat.card_congr Additive.ofMul).symm
  have hdpos : 0 < Module.finrank (ZMod 2) (Additive (↥C ⧸ (A.subgroupOf C))) := by
    by_contra hc
    push Not at hc
    have h0 : Module.finrank (ZMod 2) (Additive (↥C ⧸ (A.subgroupOf C))) = 0 := by omega
    rw [h0, pow_zero] at hcardV
    have hsub : Subsingleton (↥C ⧸ (A.subgroupOf C)) := (Nat.card_eq_one_iff_unique.mp hcardV).1
    exact hex.choose_spec (Subsingleton.elim hex.choose 1)
  calc Nat.card (↥C ⧸ (A.subgroupOf C))
      = 2 ^ Module.finrank (ZMod 2) (Additive (↥C ⧸ (A.subgroupOf C))) := hcardV
    _ ∣ 2 ^ n := Nat.pow_dvd_pow 2 (Nat.le_of_dvd (by omega) hdvd)
    _ = Nat.card ↥(Work.Higman.omega1 P) := hn.symm

theorem card_quot_C_A_eq {P : Type} [Group P] [Finite P] (h : Work.Higman.IsSuzuki2Grp P)
    {A C : Subgroup P} [hAn : A.Normal]
    (hAxi : A.map (h.xi : MulAut P).toMonoidHom = A)
    (hAab : ∀ x ∈ A, ∀ y ∈ A, x * y = y * x)
    (hNA : Work.Higman.omega1 P ≤ A)
    (hGs : ⁅(⊤ : Subgroup P), ⊤⁆ = A)
    (hsq : ∀ x : P, x ^ 2 ∈ A)
    (hA4 : Work.Higman.powSub A 4 = ⊥)
    (htop : Work.Higman.powSub A 2 = Work.Higman.omega1 P)
    (hcard : Nat.card ↥A = (Nat.card ↥(Work.Higman.omega1 P)) ^ 2)
    (hCn : C.Normal) (hCinv : C.map (h.xi : MulAut P).toMonoidHom = C)
    (hAC : A ≤ C) (hCA : A ≠ C)
    (hcover : ∀ D : Subgroup P, D.Normal → D.map (h.xi : MulAut P).toMonoidHom = D →
      A ≤ D → D ≤ C → D = A ∨ D = C)
    (hC2 : Work.Higman.powSub C 2 ≤ A)
    (hCAd : ⁅C, A⁆ = Work.Higman.powSub A 2)
    (hstep : ∀ x ∈ C, (h.xi ^ (Nat.card ↥(Work.Higman.omega1 P) - 1)) x * x⁻¹ ∈ A) :
    Nat.card (↥C ⧸ (A.subgroupOf C)) = Nat.card ↥(Work.Higman.omega1 P) := by
  classical
  -- `|Ω₁(P)| = 2 ^ n`
  obtain ⟨n, hn⟩ := h.exists_card_omega1_eq_two_pow
  have hn1 : 1 ≤ n := by
    have h4 : 4 ≤ 2 ^ n := by rw [← hn]; exact h.omega1_card_ge_four
    by_contra hc
    push Not at hc
    interval_cases n <;> norm_num at h4
  -- the `𝔽₂`-module structure of `V = C/A`
  letI : CommGroup (↥C ⧸ (A.subgroupOf C)) :=
    { (inferInstance : Group (↥C ⧸ (A.subgroupOf C))) with
      mul_comm := quot_comm_of_commutator_top_eq h hGs }
  have hV2 : ∀ x : ↥C ⧸ (A.subgroupOf C), x * x = 1 :=
    fun x => Work.Higman.MSA.L8.quot_sq_one (A := A) (C := C) hC2 x
  letI : Module (ZMod 2) (Additive (↥C ⧸ (A.subgroupOf C))) :=
    Work.Higman.SZ.module_zmod2_of_sq_one (G := ↥C ⧸ (A.subgroupOf C)) hV2
  have hex : ∃ y : ↥C ⧸ (A.subgroupOf C), y ≠ 1 := by
    obtain ⟨x, hxC, hxA⟩ : ∃ x ∈ C, x ∉ A := by
      by_contra hcon
      push Not at hcon
      exact hCA (le_antisymm hAC hcon)
    refine ⟨QuotientGroup.mk (⟨x, hxC⟩ : ↥C), ?_⟩
    intro h1
    rw [QuotientGroup.eq_one_iff] at h1
    exact hxA (Subgroup.mem_subgroupOf.mp h1)
  set d := Module.finrank (ZMod 2) (Additive (↥C ⧸ (A.subgroupOf C))) with hd
  have hVcard : Nat.card (↥C ⧸ (A.subgroupOf C)) = 2 ^ d := by
    have h1 : Nat.card (Additive (↥C ⧸ (A.subgroupOf C)))
        = 2 ^ Module.finrank (ZMod 2) (Additive (↥C ⧸ (A.subgroupOf C))) := by
      have h2 : Nat.card (Additive (↥C ⧸ (A.subgroupOf C)))
          = Nat.card (ZMod 2) ^ Module.finrank (ZMod 2) (Additive (↥C ⧸ (A.subgroupOf C))) :=
        Module.natCard_eq_pow_finrank
      rwa [Nat.card_zmod] at h2
    rw [hd, ← h1]
    exact (Nat.card_congr Additive.ofMul).symm
  -- the upper bound: `|C/A| ∣ |Ω₁(P)|`
  have hVdvd : Nat.card (↥C ⧸ (A.subgroupOf C)) ∣ Nat.card ↥(Work.Higman.omega1 P) :=
    card_quot_dvd_omega1_aux h hAxi hCinv hAC hCA hGs hcover hC2 hstep
  have hdle : d ≤ n := by
    have h1 : 2 ^ d ∣ 2 ^ n := by rw [← hVcard, ← hn]; exact hVdvd
    exact (Nat.pow_le_pow_iff_right (by norm_num)).mp (Nat.le_of_dvd (by positivity) h1)
  -- the orbit count on `C`
  have hCdiv : Nat.card ↥(Work.Higman.omega1 P) - 1 ∣ Nat.card ↥C - 1 :=
    Work.Higman.H8.card_sub_one_dvd_of_xi_invariant_xi h hCinv
  -- `|C| = |C/A| * |A| = 2 ^ (d + 2 * n)`
  have hCcard : Nat.card ↥C = 2 ^ (d + 2 * n) := by
    have h1 : Nat.card ↥C = Nat.card (↥C ⧸ (A.subgroupOf C)) * Nat.card ↥(A.subgroupOf C) :=
      Subgroup.card_eq_card_quotient_mul_card_subgroup (A.subgroupOf C)
    have h2 : Nat.card ↥(A.subgroupOf C) = Nat.card ↥A :=
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe hAC)
    rw [h2, hcard, hVcard, hn] at h1
    rw [h1, ← pow_mul, ← pow_add]
    congr 1
    ring
  -- the lower bound: `n ∣ d`
  have hnd : n ∣ d := by
    have h1 : 2 ^ n - 1 ∣ 2 ^ (d + 2 * n) - 1 := by
      rw [← hn, ← hCcard]
      exact hCdiv
    have h2 : n ∣ d + 2 * n :=
      (Work.Higman.Q3.pow_sub_one_dvd_pow_sub_one_iff (x := 2) (m := n) (k := d + 2 * n)
        (by norm_num) (by omega)).mp h1
    have h3 : n ∣ 2 * n := ⟨2, by ring⟩
    have h4 : n ∣ d + 2 * n - 2 * n := Nat.dvd_sub h2 h3
    simpa using h4
  -- `d = n`
  have hdpos : 0 < d := by
    by_contra hc
    push Not at hc
    have h0 : d = 0 := by omega
    have h1 : Nat.card (↥C ⧸ (A.subgroupOf C)) = 1 := by rw [hVcard, h0]; norm_num
    have hsub : Subsingleton (↥C ⧸ (A.subgroupOf C)) := (Nat.card_eq_one_iff_unique.mp h1).1
    exact hex.choose_spec (Subsingleton.elim hex.choose 1)
  have hdn : d = n := le_antisymm hdle (Nat.le_of_dvd (by omega) hnd)
  rw [hVcard, hdn, hn]

end Work.Higman.HS
