import Mathlib
import Submission.Work.Higman.H8.c4_sq_a2_aux
import Submission.Work.Higman.H8.c4_sq_a2_orbit
import Submission.Work.Higman.MSA.l8_card_le
import Submission.Work.Higman.MSA.l8_quot_irred
import Submission.Work.Higman.MSA.l8_triv
import Submission.Work.Higman.SZ.model
import Submission.Work.Higman.H8.quot_irred_of_cover

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.style.haveILetI false

namespace Work.Higman.H8

open scoped commutatorElement

variable {P : Type} [Group P] [Finite P]

/-! ## Auxiliary facts -/

/-- `(L8.xiQuot h hAinv hDinv) ^ k` on a representative. -/
theorem xiQuot_pow_mk {h : Work.Higman.IsSuzuki2Grp P} {A D : Subgroup P} [A.Normal]
    (hAinv : Subgroup.map (MulEquiv.toMonoidHom h.xi) A = A)
    (hDinv : Subgroup.map (MulEquiv.toMonoidHom h.xi) D = D) (k : ℕ) (u : ↥D) :
    ((Work.Higman.MSA.L8.xiQuot h hAinv hDinv) ^ k) (QuotientGroup.mk u)
      = QuotientGroup.mk ((Work.Higman.MSA.L8.xiSubAut h hDinv ^ k) u) := by
  induction k with
  | zero => simp
  | succ k ih =>
      have h1 : ((Work.Higman.MSA.L8.xiQuot h hAinv hDinv) ^ (k + 1)) (QuotientGroup.mk u)
          = Work.Higman.MSA.L8.xiQuot h hAinv hDinv
              (((Work.Higman.MSA.L8.xiQuot h hAinv hDinv) ^ k) (QuotientGroup.mk u)) := by
        rw [pow_succ', MulAut.mul_apply]
      rw [h1, ih, Work.Higman.MSA.l8_xiQuot_mk]
      congr 1
      rw [pow_succ', MulAut.mul_apply]

/-- Cardinality of `A.subgroupOf D` as a subgroup of `D`. -/
theorem card_subgroupOf_eq (A D : Subgroup P) (hAD : A ≤ D) :
    Nat.card ↥(A.subgroupOf D) = Nat.card ↥A := by
  refine Nat.card_congr ?_
  exact { toFun := fun x => ⟨((x : ↥D) : P), x.2⟩
          invFun := fun a => ⟨⟨(a : P), hAD a.2⟩, a.2⟩
          left_inv := fun x => Subtype.ext (Subtype.ext rfl)
          right_inv := fun a => Subtype.ext rfl }

/-- Pure arithmetic: from `a ∣ k - 1` and `a ∣ m * k - 1` with `1 ≤ m`, `1 ≤ k` deduce
`a ∣ m - 1`. -/
theorem dvd_sub_one_of_dvd_mul_sub_one {a m k : ℕ} (hm : 1 ≤ m) (hk : 1 ≤ k)
    (h1 : a ∣ k - 1) (h2 : a ∣ m * k - 1) : a ∣ m - 1 := by
  have hid : m * k - 1 = m * (k - 1) + (m - 1) := by
    have hmul : m * k = m * (k - 1) + m := by
      conv_lhs => rw [← Nat.sub_add_cancel hk]
      rw [Nat.mul_succ]
    rw [hmul]
    omega
  have h3 : a ∣ m * (k - 1) := Dvd.dvd.mul_left h1 m
  rw [hid] at h2
  exact (Nat.dvd_add_iff_right h3).mpr h2

/-! ## The main count -/

/-- **The `m = n` count for `D`.**  In the `C₄` setting with `C_P(A) = A`, `[A,D] = A²` and
`D ⊴ P` as in `c4_sq_a2`, the quotient `D/A` has order `|Ω₁(P)|`.

Upper bound: `D/A` is an abelian group of exponent two (`[D,D] = A² ≤ A`, `D² ⊆ A²`), the
`ξ`-action on it is irreducible (hcover; every `E` with `A ≤ E ≤ D` is automatically normal since
`[P,E] ≤ [P,P] = A ≤ E`) and `ξ^(q-1)` acts trivially on it
(`Work.Higman.H8.c4_sq_a2_xi_pow_sub_one_triv`, imported from `H8/c4_sq_a2_aux`), so
`Work.Higman.MSA.l8_card_le` gives `|D/A| ≤ 2^n = q`.

Lower bound: `Work.Higman.card_sub_one_dvd_of_xi_invariant` applied to the `ξ`-invariant
subgroups `A` and `D` gives `(q-1) ∣ |A| - 1` and `(q-1) ∣ |D| - 1`, hence `(q-1) ∣ |D/A| - 1`;
with `D ≠ A` this gives `|D/A| ≥ q`. -/
theorem c4_sq_a2_card_quot {P : Type} [Group P] [Finite P] (h : Work.Higman.IsSuzuki2Grp P)
    {A D : Subgroup P} (hA : Work.Higman.IsXiAbelNormal h A)
    (hGs : ⁅(⊤ : Subgroup P), ⊤⁆ = A) (hNA : Work.Higman.omega1 P ≤ A)
    (htop : Work.Higman.powSub A 2 = Work.Higman.omega1 P)
    (hcent : Subgroup.centralizer (A : Set P) = A)
    (hDn : D.Normal) (hDinv : D.map (h.xi : MulAut P).toMonoidHom = D)
    (hAD : A ≤ D) (hADne : D ≠ A)
    (hDd : ⁅D, D⁆ = Work.Higman.powSub A 2)
    (hPhi : Work.Higman.powSub D 2 ⊔ ⁅D, D⁆ = Work.Higman.powSub A 2)
    (hcover : ∀ E : Subgroup P, E.Normal → E.map (h.xi : MulAut P).toMonoidHom = E →
      A ≤ E → E ≤ D → E = A ∨ E = D)
    (hAD2 : ⁅A, D⁆ = Work.Higman.powSub A 2) :
    Nat.card (↥D ⧸ (A.subgroupOf D)) = Nat.card ↥(Work.Higman.omega1 P) := by
  classical
  haveI hAn : A.Normal := hA.normal
  haveI : Fintype P := Fintype.ofFinite P
  -- elementary containments
  have hA2le : Work.Higman.powSub A 2 ≤ A := Work.Higman.powSub_le (n := 2) (by norm_num)
  have hD2le : Work.Higman.powSub D 2 ≤ A := by
    calc Work.Higman.powSub D 2 ≤ Work.Higman.powSub D 2 ⊔ ⁅D, D⁆ := le_sup_left
      _ = Work.Higman.powSub A 2 := hPhi
      _ ≤ A := hA2le
  -- `[⊤, D] ≤ A`
  have hPC : ⁅(⊤ : Subgroup P), D⁆ ≤ A := by
    calc ⁅(⊤ : Subgroup P), D⁆ ≤ ⁅(⊤ : Subgroup P), ⊤⁆ :=
          Subgroup.commutator_mono le_rfl le_top
      _ = A := hGs
  -- `ξ ^ (q-1)` is trivial on `D/A`
  have htriv : ∀ x ∈ D, (h.xi ^ (Nat.card ↥(Work.Higman.omega1 P) - 1)) x * x⁻¹ ∈ A :=
    c4_sq_a2_xi_pow_sub_one_triv h hA htop hcent hAD2
  -- ## The quotient `D/A` is abelian
  have hcomm_le : ⁅(⊤ : Subgroup ↥D), ⊤⁆ ≤ A.subgroupOf D := by
    rw [Subgroup.commutator_le]
    intro x _ y _
    rw [Subgroup.mem_subgroupOf]
    have hmem : ⁅(x : P), (y : P)⁆ ∈ (⁅D, D⁆ : Subgroup P) :=
      Subgroup.commutator_mem_commutator x.2 y.2
    rw [hDd] at hmem
    have hcoe : ((⁅x, y⁆ : ↥D) : P) = ⁅(x : P), (y : P)⁆ := by
      simp only [commutatorElement_def, Subgroup.coe_mul, Subgroup.coe_inv]
    rw [hcoe]
    exact hA2le hmem
  letI : CommGroup (↥D ⧸ (A.subgroupOf D)) :=
    Work.Higman.SZ.commGroup_quot_of_commutator_le (A.subgroupOf D) hcomm_le
  -- ## The upper bound `|D/A| ≤ q`
  obtain ⟨n, hn⟩ := h.exists_card_omega1_eq_two_pow
  have hn1 : 1 ≤ n := by
    by_contra hc
    have hn0 : n = 0 := by omega
    have h4 := h.omega1_card_ge_four
    rw [hn, hn0] at h4
    norm_num at h4
  have hxi : (Work.Higman.MSA.L8.xiQuot h hA.map_eq hDinv) ^ (2 ^ n - 1) = 1 := by
    have h2n : 2 ^ n - 1 = Nat.card ↥(Work.Higman.omega1 P) - 1 := by rw [hn]
    rw [h2n]
    apply MulEquiv.ext
    intro z
    obtain ⟨u, rfl⟩ := QuotientGroup.mk_surjective z
    show ((Work.Higman.MSA.L8.xiQuot h hA.map_eq hDinv) ^ (Nat.card ↥(Work.Higman.omega1 P) - 1))
        (QuotientGroup.mk u) = QuotientGroup.mk u
    rw [xiQuot_pow_mk (h := h) (hAinv := hA.map_eq) (hDinv := hDinv)]
    rw [QuotientGroup.eq, Subgroup.mem_subgroupOf]
    simp only [Subgroup.coe_mul, Subgroup.coe_inv]
    rw [Work.Higman.MSA.L8.xiSubAut_pow_apply h hDinv]
    obtain ⟨y, hy, hmem⟩ : ∃ y : P,
        y = (h.xi ^ (Nat.card ↥(Work.Higman.omega1 P) - 1)) (u : P)
          ∧ y * (u : P)⁻¹ ∈ A := ⟨_, rfl, htriv u u.2⟩
    rw [← hy]
    have hid : y⁻¹ * (u : P) = y⁻¹ * (y * (u : P)⁻¹)⁻¹ * (y⁻¹)⁻¹ := by group
    rw [hid]
    exact hAn.conj_mem _ (A.inv_mem hmem) y⁻¹
  have hirr : ∀ K : Subgroup (↥D ⧸ (A.subgroupOf D)),
      K.map (Work.Higman.MSA.L8.xiQuot h hA.map_eq hDinv).toMonoidHom = K →
      K = ⊥ ∨ K = ⊤ :=
    fun K hK => quot_irred_of_cover hA.map_eq hDinv hAD hPC hcover K hK
  have hle : Nat.card (↥D ⧸ (A.subgroupOf D)) ≤ 2 ^ n :=
    Work.Higman.MSA.l8_card_le (V := ↥D ⧸ (A.subgroupOf D))
      (fun v => Work.Higman.MSA.L8.quot_sq_one (A := A) (C := D) hD2le v)
      (Work.Higman.MSA.L8.xiQuot h hA.map_eq hDinv) hn1 hxi hirr
  rw [← hn] at hle
  -- ## The lower bound `q ≤ |D/A|`
  have hqA : Nat.card ↥(Work.Higman.omega1 P) - 1 ∣ Nat.card ↥A - 1 :=
    xi_invariant_card_sub_one_dvd h hA.map_eq
  have hqD : Nat.card ↥(Work.Higman.omega1 P) - 1 ∣ Nat.card ↥D - 1 :=
    xi_invariant_card_sub_one_dvd h hDinv
  have hDcard : Nat.card ↥D
      = Nat.card (↥D ⧸ (A.subgroupOf D)) * Nat.card ↥A := by
    rw [Subgroup.card_eq_card_quotient_mul_card_subgroup (A.subgroupOf D),
      card_subgroupOf_eq A D hAD]
  have hkey : Nat.card ↥(Work.Higman.omega1 P) - 1
      ∣ Nat.card (↥D ⧸ (A.subgroupOf D)) - 1 := by
    refine dvd_sub_one_of_dvd_mul_sub_one (k := Nat.card ↥A)
      (Nat.card_pos (α := ↥D ⧸ (A.subgroupOf D))) (Nat.card_pos (α := ↥A)) hqA ?_
    rw [← hDcard]
    exact hqD
  have hmne : Nat.card (↥D ⧸ (A.subgroupOf D)) ≠ 1 := by
    intro hm1
    apply hADne
    have hcard : Nat.card ↥D = Nat.card ↥A := by rw [hDcard, hm1, one_mul]
    exact (Subgroup.eq_of_le_of_card_ge hAD (le_of_eq hcard)).symm
  have hge : Nat.card ↥(Work.Higman.omega1 P) ≤ Nat.card (↥D ⧸ (A.subgroupOf D)) := by
    have h1le : 1 ≤ Nat.card (↥D ⧸ (A.subgroupOf D)) := Nat.card_pos
    have h2 : 2 ≤ Nat.card (↥D ⧸ (A.subgroupOf D)) := by omega
    have hq1le : Nat.card ↥(Work.Higman.omega1 P) - 1
        ≤ Nat.card (↥D ⧸ (A.subgroupOf D)) - 1 :=
      Nat.le_of_dvd (by omega) hkey
    have h4 := h.omega1_card_ge_four
    omega
  exact le_antisymm hle hge

end Work.Higman.H8
