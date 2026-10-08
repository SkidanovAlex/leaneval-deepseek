import Mathlib
import Submission.Work.LocalPrelim.Defs
import Submission.Work.LocalPrelim.ft8_3
import Submission.Work.PGroup.Basic
import Submission.Work.PGroup.Omega1
import Submission.Work.PGroup.omega_one_eq_omega1
import Submission.Work.PGroup.omega_conj
import Submission.Work.PGroup.centralizer_eq_of_maximal_normal_abelian
import Submission.Work.PGroup.rank_eq_log_card_of_isElementaryAbelian
import Submission.Work.LocalPrelim.card_omega_one_eq_pow_rank
import Submission.Work.LocalPrelim.card_le_mul_card_inf_centralizer_of_isElementaryAbelian

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

set_option linter.unusedVariables false
set_option linter.style.haveILetI false

open scoped Classical Pointwise commutatorElement
open Subgroup

noncomputable section

namespace Work.LocalPrelim

/-- **Feit--Thompson Lemma 8.4 (i)**, elementary-abelian form.

Let `X` be a finite `p`-group with `p` odd and suppose that `X` has no `SCN_3`-subgroup
(no `A ∈ SCN(X)` with `m(A) ≥ 3`).  Then `X` has no elementary abelian subgroup `E` with
`p ^ 3 ≤ |E|`.

The proof follows FT: choose `A₀ ∈ SCN(X)` of maximal rank; by hypothesis `Group.rank A₀ ≤ 2`,
so `V := Ω₁(A₀)` is elementary abelian of order `≤ p ^ 2`.  FT 8.3
(`Work.LocalPrelim.ft8_3`) gives `Ω₁(C_X(V)) = V`.  An elementary abelian `E` with
`p ^ 3 ≤ |E|` satisfies `|E| ≤ p · |E ∩ C_X(V)|` (conjugation embeds `E/C_E(V)` into the
`p`-group `Aut V`, whose `p`-part has order at most `p` when `|V| ≤ p ^ 2`), so
`E ∩ C_X(V)` has order `≥ p ^ 2`; by FT 8.3 it lies in `V`, hence equals `V`, and then
`E ≤ C_X(V)` and `E ≤ Ω₁(C_X(V)) = V` has order `≤ p ^ 2 < p ^ 3`, a contradiction. -/
theorem no_elementary_of_no_scn3 {X : Type*} [Group X] [Finite X] {p : ℕ}
    (hp : p.Prime) (hpodd : Odd p) (hX : IsPGroup p X)
    (h : ∀ B : Subgroup X, ¬ IsSCN_m 3 (⊤ : Subgroup X) B) :
    ¬ ∃ E : Subgroup X, Work.PGroup.IsElementaryAbelian p E ∧ p ^ 3 ≤ Nat.card E := by
  classical
  haveI : Fact p.Prime := ⟨hp⟩
  ---------------------------------------------------------------
  -- Step 1: a maximal normal abelian subgroup, and an `SCN`-subgroup of maximal rank
  ---------------------------------------------------------------
  have hex : ∃ A : Subgroup X, A.Normal ∧ IsMulCommutative ↥A ∧
      (∀ B : Subgroup X, B.Normal → IsMulCommutative ↥B → A ≤ B → B = A) := by
    set S : Set ℕ := {n : ℕ | ∃ B : Subgroup X, B.Normal ∧ IsMulCommutative ↥B ∧
      Nat.card B = n} with hS
    have hne : S.Nonempty := ⟨1, ⊥, inferInstance,
      IsMulCommutative.of_comm (fun a b => Subsingleton.elim _ _), Subgroup.card_bot⟩
    have hbdd : BddAbove S := ⟨Nat.card X, by
      rintro n ⟨B, -, -, rfl⟩
      exact Subgroup.card_le_card_group B⟩
    obtain ⟨A, hAn, hAab, hAcard⟩ := Nat.sSup_mem hne hbdd
    refine ⟨A, hAn, hAab, ?_⟩
    intro B hBn hBab hAB
    have h1 : Nat.card B ≤ Nat.card A := by
      rw [hAcard]
      exact le_csSup hbdd (show Nat.card B ∈ S from ⟨B, hBn, hBab, rfl⟩)
    exact (Subgroup.eq_of_le_of_card_ge (H := A) (K := B) hAB h1).symm
  obtain ⟨A₁, hA₁n, hA₁ab, hA₁max⟩ := hex
  haveI hA₁inst : A₁.Normal := hA₁n
  haveI hnil : Group.IsNilpotent X := hX.isNilpotent
  have hcent₁ : Subgroup.centralizer (A₁ : Set X) = A₁ :=
    Work.PGroup.centralizer_eq_of_maximal_normal_abelian hA₁ab hA₁max
  have hSCN₁ : IsSCN (⊤ : Subgroup X) A₁ := by
    refine ⟨le_top, ?_, hA₁ab, ?_⟩
    · rw [Subgroup.subgroupOf]
      exact Subgroup.Normal.comap hA₁n (⊤ : Subgroup X).subtype
    · rw [inf_top_eq]
      exact le_of_eq hcent₁
  -- among the `SCN`-subgroups, take one of maximal rank
  set S2 : Set ℕ := {n : ℕ | ∃ B : Subgroup X, IsSCN (⊤ : Subgroup X) B ∧
    Group.rank B = n} with hS2
  have hne2 : S2.Nonempty := ⟨Group.rank A₁, A₁, hSCN₁, rfl⟩
  have hbdd2 : BddAbove S2 := ⟨Nat.card X, by
    rintro n ⟨B, -, rfl⟩
    haveI : Fintype ↥B := Fintype.ofFinite _
    calc Group.rank B ≤ (Finset.univ : Finset ↥B).card := Group.rank_le (by simp)
      _ = Nat.card B := by rw [Finset.card_univ, Nat.card_eq_fintype_card]
      _ ≤ Nat.card X := Subgroup.card_le_card_group B⟩
  obtain ⟨A₀, hA₀scn, hA₀rank⟩ := Nat.sSup_mem hne2 hbdd2
  have hmax : ∀ B : Subgroup X, IsSCN (⊤ : Subgroup X) B → Group.rank B ≤ Group.rank A₀ := by
    intro B hB
    rw [hA₀rank]
    exact le_csSup hbdd2 ⟨B, hB, rfl⟩
  have hA₀ab : IsMulCommutative ↥A₀ := hA₀scn.2.2.1
  have hrankA₀ : Group.rank A₀ ≤ 2 := by
    by_contra hcon
    exact h A₀ ⟨hA₀scn, by omega⟩
  have hA₀n : A₀.Normal := by
    have h1 : (A₀.subgroupOf ⊤).Normal := hA₀scn.2.1
    rw [show A₀ = (A₀.subgroupOf ⊤).map (⊤ : Subgroup X).subtype from ?_]
    · exact Subgroup.Normal.map h1 _ (fun x => ⟨⟨x, Subgroup.mem_top x⟩, rfl⟩)
    · rw [Subgroup.subgroupOf]
      exact (Subgroup.map_comap_eq_self (f := (⊤ : Subgroup X).subtype) (H := A₀)
        (by rw [Subgroup.range_subtype]; exact le_top)).symm
  haveI hA₀inst : A₀.Normal := hA₀n
  have hA₀p : IsPGroup p A₀ := hX.to_subgroup A₀
  ---------------------------------------------------------------
  -- Step 2: `V := Ω₁(A₀)` is elementary abelian of order `≤ p ^ 2`
  ---------------------------------------------------------------
  set V : Subgroup X := Work.PGroup.omega p 1 A₀ with hVdef
  have hVel : Work.PGroup.IsElementaryAbelian p V := by
    rw [hVdef, Work.PGroup.omega_one_eq_omega1]
    exact ⟨Work.PGroup.omega1_isMulCommutative hA₀ab,
      fun x => Subtype.ext (by simpa using Work.PGroup.omega1_pow_eq_one hA₀ab x.2)⟩
  have hVcard : Nat.card ↥V ≤ p ^ 2 := by
    rw [hVdef, Work.LocalPrelim.card_omega_one_eq_pow_rank hp hA₀ab hA₀p]
    exact Nat.pow_le_pow_right hp.pos hrankA₀
  have hVn : V.Normal := by
    rw [hVdef]
    exact omega_normal_of_normal p 1 hA₀n
  ---------------------------------------------------------------
  -- Step 3: Feit--Thompson 8.3 for `A₀`
  ---------------------------------------------------------------
  have h83 : Work.PGroup.omega p 1 (Subgroup.centralizer (V : Set X)) = V := by
    rw [hVdef]
    exact Work.LocalPrelim.ft8_3 hp hpodd hX hA₀scn hmax
  ---------------------------------------------------------------
  -- Step 4: no elementary abelian subgroup of order `≥ p ^ 3`
  ---------------------------------------------------------------
  rintro ⟨E, hEel, hEcard⟩
  set E₁ : Subgroup X := E ⊓ Subgroup.centralizer (V : Set X) with hE₁def
  have hE₁le : E₁ ≤ E := inf_le_left
  have hcardE : Nat.card ↥E ≤ p * Nat.card ↥E₁ := by
    rw [hE₁def]
    exact Work.LocalPrelim.card_le_mul_card_inf_centralizer_of_isElementaryAbelian
      hp hVn hVel hVcard hEel
  have hE₁leV : E₁ ≤ V := by
    intro x hx
    have hxE : x ∈ E := hx.1
    have hxC : x ∈ Subgroup.centralizer (V : Set X) := hx.2
    have hxp : x ^ p = 1 := by simpa using hEel.2 ⟨x, hxE⟩
    have h1 : x ∈ Work.PGroup.omega p 1 (Subgroup.centralizer (V : Set X)) :=
      Subgroup.subset_closure ⟨hxC, by simpa using hxp⟩
    rwa [h83] at h1
  have hE₁card : p ^ 2 ≤ Nat.card ↥E₁ := by
    have hp2 : 0 < p ^ 2 := pow_pos hp.pos 2
    nlinarith [hcardE, hEcard, Nat.card_pos (α := ↥E₁)]
  have hVE₁ : V = E₁ := by
    refine (Subgroup.eq_of_le_of_card_ge (H := E₁) (K := V) hE₁leV ?_).symm
    have h1 : Nat.card ↥E₁ ≤ Nat.card ↥V := Subgroup.card_le_of_le hE₁leV
    omega
  have hEcent : E ≤ Subgroup.centralizer (V : Set X) := by
    rw [Subgroup.le_centralizer_iff]
    intro v hv e he
    have hvE : v ∈ E := hE₁le (hVE₁ ▸ hv)
    exact (isMulCommutative_iff_of_setLike.mp hEel.1 v hvE e he).symm
  have hEV : E ≤ V := by
    intro x hx
    have hxp : x ^ p = 1 := by simpa using hEel.2 ⟨x, hx⟩
    have h1 : x ∈ Work.PGroup.omega p 1 (Subgroup.centralizer (V : Set X)) :=
      Subgroup.subset_closure ⟨hEcent hx, by simpa using hxp⟩
    rwa [h83] at h1
  have h1 : Nat.card ↥E ≤ Nat.card ↥V := Subgroup.card_le_of_le hEV
  have hp23 : p ^ 2 < p ^ 3 := Nat.pow_lt_pow_right hp.one_lt (by norm_num)
  omega

theorem ft8_4_i {X : Type*} [Group X] [Finite X] {p : ℕ} (hp : p.Prime) (hpodd : Odd p)
    (hX : IsPGroup p X) (h : ∀ A : Subgroup X, ¬ IsSCN_m 3 (⊤ : Subgroup X) A) :
    ∀ A : Subgroup X, IsMulCommutative ↥A → Group.rank A ≤ 2 := by
  intro B hBab
  by_contra hle
  have hge : 3 ≤ Group.rank B := by omega
  have hBp : IsPGroup p B := hX.to_subgroup B
  have hEel : Work.PGroup.IsElementaryAbelian p (Work.PGroup.omega p 1 B) := by
    rw [Work.PGroup.omega_one_eq_omega1]
    exact ⟨Work.PGroup.omega1_isMulCommutative hBab,
      fun x => Subtype.ext (by simpa using Work.PGroup.omega1_pow_eq_one hBab x.2)⟩
  have hEcard : p ^ 3 ≤ Nat.card ↥(Work.PGroup.omega p 1 B) := by
    rw [Work.LocalPrelim.card_omega_one_eq_pow_rank hp hBab hBp]
    exact Nat.pow_le_pow_right hp.pos hge
  exact no_elementary_of_no_scn3 hp hpodd hX h ⟨_, hEel, hEcard⟩

end Work.LocalPrelim
