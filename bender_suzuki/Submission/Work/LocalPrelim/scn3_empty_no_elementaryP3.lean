/-
# `𝒮𝒞𝒩₃(P) = ∅` implies `P` has no elementary abelian subgroup of order `p ^ 3`

Feit--Thompson Lemma 8.4 (i), in the form consumed by the local analysis: if `P` is a `p`-group
(`p` an odd prime) with no `SCN₃`-subgroup, then `P` contains no elementary abelian subgroup of
order `p ^ 3`.  The file also records the ambient-group form used by the caller: for a subgroup
`P ≤ G` with `𝒮𝒞𝒩₃(P) = ∅` (computed in `G`), the group `↥P` has no elementary abelian subgroup
of order `p ^ 3` (`Work.SmallRank.NoElementaryP3 p ↥P`).

The auxiliary theorem `no_elemAbelian_p3_of_no_scn3_aux` is the same statement as
`Work.LocalPrelim.no_isElementaryAbelian_card_p3_of_no_scn3` (which is stated with the temporary
stub `ft8_3_omega_stub`); here FT 8.3 is cited in its unconditional form
`Work.LocalPrelim.ft8_3`.
-/
import Mathlib
import Submission.Work.LocalPrelim.Defs
import Submission.Work.PGroup.Basic
import Submission.Work.PGroup.Omega1
import Submission.Work.PGroup.omega_one_eq_omega1
import Submission.Work.PGroup.omega_conj
import Submission.Work.PGroup.centralizer_eq_of_maximal_normal_abelian
import Submission.Work.PGroup.rank_eq_log_card_of_isElementaryAbelian
import Submission.Work.LocalPrelim.rank_le_of_commutative_subgroup
import Submission.Work.LocalPrelim.card_omega_one_eq_pow_rank
import Submission.Work.LocalPrelim.card_le_mul_card_inf_centralizer_of_isElementaryAbelian
import Submission.Work.SmallRank.Defs
import Submission.Work.LocalPrelim.ft8_3
import Submission.Work.Transitivity.Basic.exists_isSCN_m_top_iff

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

set_option linter.style.haveILetI false
set_option linter.unusedVariables false

open scoped Classical Pointwise commutatorElement
open Subgroup

namespace Work.LocalPrelim
theorem no_elemAbelian_p3_of_no_scn3_aux {X : Type*} [Group X] [Finite X] {p : ℕ}
    (hp : p.Prime) (hpodd : Odd p) (hX : IsPGroup p X)
    (h : ∀ B : Subgroup X, ¬ IsSCN_m 3 (⊤ : Subgroup X) B) :
    ¬ ∃ E : Subgroup X, Work.PGroup.IsElementaryAbelian p E ∧ p ^ 3 ≤ Nat.card E := by
  classical
  haveI : Fact p.Prime := ⟨hp⟩
  ---------------------------------------------------------------
  -- ## Step 1: a maximal normal abelian subgroup, and an `SCN`-subgroup of maximal rank
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
  obtain ⟨A₀, hA₀n, hA₀ab, hA₀max⟩ := hex
  haveI hA₀inst : A₀.Normal := hA₀n
  haveI hnil : Group.IsNilpotent X := hX.isNilpotent
  have hcent₀ : Subgroup.centralizer (A₀ : Set X) = A₀ :=
    Work.PGroup.centralizer_eq_of_maximal_normal_abelian hA₀ab hA₀max
  have hSCN₀ : IsSCN (⊤ : Subgroup X) A₀ := by
    refine ⟨le_top, ?_, hA₀ab, ?_⟩
    · rw [Subgroup.subgroupOf]
      exact Subgroup.Normal.comap hA₀n (⊤ : Subgroup X).subtype
    · rw [inf_top_eq]
      exact le_of_eq hcent₀
  -- among the `SCN`-subgroups, take one of maximal rank
  set S2 : Set ℕ := {n : ℕ | ∃ B : Subgroup X, IsSCN (⊤ : Subgroup X) B ∧
    Group.rank B = n} with hS2
  have hne2 : S2.Nonempty := ⟨Group.rank A₀, A₀, hSCN₀, rfl⟩
  have hbdd2 : BddAbove S2 := ⟨Nat.card X, by
    rintro n ⟨B, -, rfl⟩
    haveI : Fintype ↥B := Fintype.ofFinite _
    calc Group.rank B ≤ (Finset.univ : Finset ↥B).card := Group.rank_le (by simp)
      _ = Nat.card B := by rw [Finset.card_univ, Nat.card_eq_fintype_card]
      _ ≤ Nat.card X := Subgroup.card_le_card_group B⟩
  obtain ⟨A, hAscn, hArank⟩ := Nat.sSup_mem hne2 hbdd2
  have hmax : ∀ B : Subgroup X, IsSCN (⊤ : Subgroup X) B → Group.rank B ≤ Group.rank A := by
    intro B hB
    rw [hArank]
    exact le_csSup hbdd2 ⟨B, hB, rfl⟩
  have hAab : IsMulCommutative ↥A := hAscn.2.2.1
  have hrankA : Group.rank A ≤ 2 := by
    by_contra hcon
    exact h A ⟨hAscn, by omega⟩
  have hAn : A.Normal := by
    have h1 : (A.subgroupOf ⊤).Normal := hAscn.2.1
    have h2 : A = (A.subgroupOf ⊤).map (⊤ : Subgroup X).subtype := by
      rw [Subgroup.subgroupOf]
      exact (Subgroup.map_comap_eq_self (f := (⊤ : Subgroup X).subtype) (H := A)
        (by rw [Subgroup.range_subtype]; exact le_top)).symm
    rw [h2]
    exact Subgroup.Normal.map h1 _ (fun x => ⟨⟨x, Subgroup.mem_top x⟩, rfl⟩)
  haveI hAninst : A.Normal := hAn
  have hAp : IsPGroup p A := hX.to_subgroup A
  ---------------------------------------------------------------
  -- ## Step 2: `V := Ω₁(A)` is elementary abelian of order `≤ p ^ 2`
  ---------------------------------------------------------------
  set V : Subgroup X := Work.PGroup.omega p 1 A with hVdef
  have hVel : Work.PGroup.IsElementaryAbelian p V := by
    rw [hVdef, Work.PGroup.omega_one_eq_omega1]
    exact ⟨Work.PGroup.omega1_isMulCommutative hAab,
      fun x => Subtype.ext (by simpa using Work.PGroup.omega1_pow_eq_one hAab x.2)⟩
  have hVcard : Nat.card ↥V ≤ p ^ 2 := by
    rw [hVdef, Work.LocalPrelim.card_omega_one_eq_pow_rank hp hAab hAp]
    exact Nat.pow_le_pow_right hp.pos hrankA
  have hconj : ∀ g : X, Work.PGroup.conjBy g (Work.PGroup.omega p 1 A) =
      Work.PGroup.omega p 1 A := fun g =>
    Work.PGroup.omega_conj p 1 A g
      (Subgroup.normalizer_eq_top_iff.mpr hAn ▸ Subgroup.mem_top g)
  have hVn : V.Normal := by
    rw [hVdef]
    refine Subgroup.Normal.mk (fun v hv g => ?_)
    have h1 : MulAut.conj g • v ∈ Work.PGroup.conjBy g (Work.PGroup.omega p 1 A) :=
      ⟨v, hv, rfl⟩
    rw [hconj g] at h1
    simpa [Work.PGroup.conjBy, MulAut.conj_apply] using h1
  ---------------------------------------------------------------
  -- ## Step 3: Feit--Thompson 8.3 for `A`
  ---------------------------------------------------------------
  have h83 : Work.PGroup.omega p 1 (Subgroup.centralizer (V : Set X)) = V := by
    -- TODO: `Work.LocalPrelim.ft8_3_omega hp hpodd hX hAscn hmax`
    have h83' := Work.LocalPrelim.ft8_3 hp hpodd hX hAscn hmax
    rw [hVdef]
    exact h83'
  ---------------------------------------------------------------
  -- ## Step 4: no elementary abelian subgroup of order `≥ p ^ 3`
  ---------------------------------------------------------------
  rintro ⟨E, hEel, hEcard⟩
  set E₁ : Subgroup X := E ⊓ Subgroup.centralizer (V : Set X) with hE₁def
  -- `E₁` has index at most `p` in `E`
  have hE₁le : E₁ ≤ E := inf_le_left
  have hcardE : Nat.card ↥E ≤ p * Nat.card ↥E₁ := by
    rw [hE₁def]
    exact Work.LocalPrelim.card_le_mul_card_inf_centralizer_of_isElementaryAbelian
      hp hVn hVel hVcard hEel
  -- and it lies in `V` by 8.3
  have hE₁leV : E₁ ≤ V := by
    intro x hx
    have hxE : x ∈ E := hx.1
    have hxC : x ∈ Subgroup.centralizer (V : Set X) := hx.2
    have hxp : x ^ p = 1 := by simpa using hEel.2 ⟨x, hxE⟩
    have h1 : x ∈ Work.PGroup.omega p 1 (Subgroup.centralizer (V : Set X)) :=
      Subgroup.subset_closure ⟨hxC, by simpa using hxp⟩
    rwa [h83] at h1
  -- hence `|E₁| ≥ p ^ 2 = |V|`, so `E₁ = V`
  have hE₁card : p ^ 2 ≤ Nat.card ↥E₁ := by
    have := hEcard
    have hp2 : 0 < p ^ 2 := pow_pos hp.pos 2
    nlinarith [hcardE, hEcard, Nat.card_pos (α := ↥E₁)]
  have hVE₁ : V = E₁ := by
    refine (Subgroup.eq_of_le_of_card_ge (H := E₁) (K := V) hE₁leV ?_).symm
    have h1 : Nat.card ↥E₁ ≤ Nat.card ↥V := Subgroup.card_le_of_le hE₁leV
    omega
  -- so `E ≤ C_X(V)` and `E ≤ Ω₁(C_X(V)) = V`
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
  -- contradiction
  have h1 : Nat.card ↥E ≤ Nat.card ↥V := Subgroup.card_le_of_le hEV
  have hp23 : p ^ 2 < p ^ 3 := Nat.pow_lt_pow_right hp.one_lt (by norm_num)
  omega


/-- **FT 8.4 (i), ambient form**: if a subgroup `P` of a finite group `G` is a `p`-group (`p` an
odd prime) with `𝒮𝒞𝒩₃(P) = ∅`, then `P` has no elementary abelian subgroup of order `p ^ 3`.
The hypothesis is transported to the abstract group `↥P` (where `𝒮𝒞𝒩₃` and `p ^ 3 ≤ |E|` are the
forms in which FT 8.4 (i) is stated), and then `p ^ 3 ≤ |E|` is weakened to `|E| = p ^ 3`. -/
theorem scn3_empty_no_elementaryP3 {G : Type*} [Group G] [Finite G] {p : ℕ}
    (hp : p.Prime) (hpodd : Odd p) {P : Subgroup G} (hP : IsPGroup p P)
    (h : ∀ A : Subgroup G, ¬ IsSCN_m 3 P A) :
    Work.SmallRank.NoElementaryP3 p ↥P := by
  -- FT 8.4 (i) is stated for an abstract finite `p`-group; transport the hypothesis `h`.
  have h' : ∀ B : Subgroup ↥P, ¬ IsSCN_m 3 (⊤ : Subgroup ↥P) B := by
    intro B hB
    exact h (B.map P.subtype)
      ((Work.Transitivity.Basic.isSCN_m_top_iff_map_subtype 3 P B).mp hB)
  have hno : ¬ ∃ E : Subgroup ↥P,
      Work.PGroup.IsElementaryAbelian p E ∧ p ^ 3 ≤ Nat.card E :=
    no_elemAbelian_p3_of_no_scn3_aux (X := ↥P) hp hpodd hP h'
  -- weaken `p ^ 3 ≤ |E|` to `|E| = p ^ 3`.
  rintro ⟨E, hEel, hEcard⟩
  exact hno ⟨E, hEel, by rw [hEcard]⟩

end Work.LocalPrelim
