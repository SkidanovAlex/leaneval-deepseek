import Mathlib
import Submission.Work.Higman.Defs
import Submission.Work.Higman.PowSub
import Submission.Work.Higman.SuzukiMaximal
import Submission.Work.Higman.Basic
import Submission.Work.Higman.H8.cw_cube_bound
import Submission.Work.Higman.OmegaAux
import Submission.Work.Higman.homogeneous_structure
import Submission.Work.Higman.lemma9_maximal_abelian
import Submission.Work.Higman.center_eq_omega1_new
import Submission.Work.Higman.H8.nsm_irreducible_clean

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

namespace Work.Higman.H8

open scoped commutatorElement

variable {P : Type} [Group P] [Finite P]

/-- The derived subgroup of a Suzuki 2-group is `ξ`-invariant (it is characteristic). -/
private theorem map_commutator_top_xi (h : Work.Higman.IsSuzuki2Grp P) :
    (⁅(⊤ : Subgroup P), ⊤⁆ : Subgroup P).map (h.xi : MulAut P).toMonoidHom
      = ⁅(⊤ : Subgroup P), ⊤⁆ := by
  rw [Subgroup.map_commutator,
    Subgroup.map_top_of_surjective _ (h.xi : MulAut P).surjective]

/-- If `[P,P] ≤ Ω₁(P)` in a Suzuki 2-group then every square lies in `Ω₁(P)`: the group has
class two, so `⁅x ^ 2, z⁆ = ⁅x,z⁆² = 1` because `⁅x,z⁆ ∈ Ω₁(P)` is an involution, and
`Z(P) = Ω₁(P)`. -/
private theorem powSub_top_two_le_omega1_of_comm_le (h : Work.Higman.IsSuzuki2Grp P)
    (hcomm : ⁅(⊤ : Subgroup P), ⊤⁆ ≤ Work.Higman.omega1 P) :
    Work.Higman.powSub (⊤ : Subgroup P) 2 ≤ Work.Higman.omega1 P := by
  have hZ : Subgroup.center P = Work.Higman.omega1 P := Work.Higman.center_eq_omega1_new h
  have hcl2 : ⁅(⊤ : Subgroup P), ⊤⁆ ≤ Subgroup.center P := hcomm.trans h.omega1_le_center
  rw [Work.Higman.powSub, Subgroup.closure_le]
  rintro y ⟨x, -, rfl⟩
  have hx2 : x ^ 2 ∈ Subgroup.center P := by
    rw [Subgroup.mem_center_iff]
    intro z
    refine (commutatorElement_eq_one_iff_mul_comm.mp ?_).symm
    rw [← Work.Higman.loc_cz_commutator_sq_eq hcl2 x z]
    exact h.mem_omega1.mp (hcomm (Subgroup.commutator_mem_commutator
      (Subgroup.mem_top x) (Subgroup.mem_top z)))
  rwa [hZ] at hx2

/-- **The class-two Chevalley–Warning bound.**  If `[P,P] ≤ Ω₁(P)` in a Suzuki 2-group then
`|P| ≤ |Ω₁(P)|³` (Chevalley–Warning applied to the anisotropic squaring form `P/Z(P) → Z(P)`). -/
private theorem card_le_cube_of_comm_le (h : Work.Higman.IsSuzuki2Grp P)
    (hcomm : ⁅(⊤ : Subgroup P), ⊤⁆ ≤ Work.Higman.omega1 P) :
    Nat.card P ≤ (Nat.card ↥(Work.Higman.omega1 P)) ^ 3 := by
  have hmain := card_le_cube_of_sq_le_omega1 h (M := ⊤) le_top
    (powSub_top_two_le_omega1_of_comm_le h hcomm) hcomm
  rwa [Subgroup.card_top] at hmain

/-- PLACEHOLDER (temporary, to be replaced by the imported `c4_reducible_small`). -/
private theorem c4_reducible_small_placeholder {P : Type} [Group P] [Finite P]
    (h : Work.Higman.IsSuzuki2Grp P) {A : Subgroup P} (hA : Work.Higman.IsXiAbelNormal h A)
    (hmax : ∀ B : Subgroup P, Work.Higman.IsXiAbelNormal h B → A ≤ B → B = A)
    (hNA : Work.Higman.omega1 P ≤ A)
    (hGs : ⁅(⊤ : Subgroup P), ⊤⁆ = A)
    (hsq : ∀ x : P, x ^ 2 ∈ A)
    (hA4 : Work.Higman.powSub A 4 = ⊥)
    (htop : Work.Higman.powSub A 2 = Work.Higman.omega1 P)
    (hcard : Nat.card ↥A = (Nat.card ↥(Work.Higman.omega1 P)) ^ 2)
    (hred : ∃ D : Subgroup P, D.Normal ∧ D.map (h.xi : MulAut P).toMonoidHom = D ∧ A < D ∧ D < ⊤)
    (hsmall : ∀ (Q : Type) [Group Q] [Finite Q], Work.Higman.IsSuzuki2Grp Q →
      Nat.card Q < Nat.card P → Nat.card Q ≤ (Nat.card ↥(Work.Higman.omega1 Q)) ^ 3) : False := by
  sorry

/-- **Higman's order bound, inductive step.**  If every Suzuki 2-group of smaller order
satisfies `|R| ≤ |Ω₁(R)|³`, then so does `P`.

By Higman's Lemma 9 there is a maximal `ξ`-invariant abelian normal subgroup `A ≥ Ω₁(P)` with
`[P,P] ≤ A`, all squares of `P` in `A` and `A⁴ = 1`; by Higman's Lemma 1
(`homogeneous_structure`) `|A| = |Ω₁(P)| ^ e` with `e ≤ 2`, and the `ξ`-invariant subgroups of `A`
are the power subgroups `A ^ (2 ^ i)`.

* If `e = 1` then `A = Ω₁(P)`, so `[P,P] ≤ Ω₁(P)`: the class-two Chevalley–Warning argument
  `card_le_cube_of_comm_le` gives the bound.
* If `e = 2` then `A² = Ω₁(P)`, and `[P,P] = A ^ (2 ^ s)`.  For `s ≥ 1` we get
  `[P,P] ≤ A² = Ω₁(P)` and the bound follows as before.  For `s = 0`, i.e. `[P,P] = A`, we are in
  the `C₄` shape of Higman's Lemma 8, which is impossible: if `P/A` is irreducible this is
  `nsm_irreducible_clean`; if `P/A` is reducible it is `c4_reducible_small`, whose hypothesis
  `hsmall` is exactly the induction hypothesis. -/
private theorem card_le_cube_step (h : Work.Higman.IsSuzuki2Grp P)
    (hsmall : ∀ (R : Type) [Group R] [Finite R], Work.Higman.IsSuzuki2Grp R →
      Nat.card R < Nat.card P → Nat.card R ≤ (Nat.card ↥(Work.Higman.omega1 R)) ^ 3) :
    Nat.card P ≤ (Nat.card ↥(Work.Higman.omega1 P)) ^ 3 := by
  classical
  obtain ⟨A, hAn, hAxi, hAab, hAmax, hNA, hDA, hsq, hA4⟩ := Work.Higman.lemma9_maximal_abelian h
  obtain ⟨e, hexp, hcpow, htop, hsub⟩ := Work.Higman.homogeneous_structure h hAab hAxi
  have hAinf : A ⊓ Work.Higman.omega1 P = Work.Higman.omega1 P := inf_eq_right.mpr hNA
  have htop' : Work.Higman.powSub A (2 ^ (e - 1)) = Work.Higman.omega1 P := by
    rw [htop, hAinf]
  have hq4 : 4 ≤ Nat.card ↥(Work.Higman.omega1 P) := h.omega1_card_ge_four
  -- `1 ≤ e`: otherwise `A = ⊥` and `Ω₁(P) = 1`.
  have he1 : 1 ≤ e := by
    rcases Nat.eq_zero_or_pos e with h0 | hpos
    · exfalso
      have hA : A = ⊥ := by
        rw [Subgroup.eq_bot_iff_forall]
        intro x hx
        have h1 := hexp x hx
        rw [h0] at h1
        simpa using h1
      have h1 : Work.Higman.omega1 P ≤ (⊥ : Subgroup P) := hA ▸ hNA
      have h2 : Nat.card ↥(Work.Higman.omega1 P) = 1 := by
        rw [le_bot_iff.mp h1]
        simp
      omega
    · exact hpos
  -- `e ≤ 2`: `A⁴ = 1` while `|A^(2^2)| = |Ω₁(P)|^(e-2)` for `e ≥ 2`.
  have he2 : e ≤ 2 := by
    rcases Nat.lt_or_ge e 2 with hlt | hge
    · omega
    · have hc := hcpow 2 hge
      rw [show (2 : ℕ) ^ 2 = 4 by norm_num, hA4, hAinf, Subgroup.card_bot] at hc
      have hq1 : Nat.card ↥(Work.Higman.omega1 P) ≠ 1 := by omega
      have hz : e - 2 = 0 := (Nat.pow_eq_one.mp hc.symm).resolve_left hq1
      omega
  -- `|A| = |Ω₁(P)| ^ e`
  have hAcard : Nat.card ↥A = (Nat.card ↥(Work.Higman.omega1 P)) ^ e := by
    have h0 := hcpow 0 (Nat.zero_le e)
    rw [pow_zero, Work.Higman.powSub_one_eq, hAinf, Nat.sub_zero] at h0
    exact h0
  rcases (show e = 1 ∨ e = 2 by omega) with he | he
  · -- ## `e = 1`: `A = Ω₁(P)`
    have hAeq : A = Work.Higman.omega1 P := by
      rw [he] at htop'
      rwa [show (2 : ℕ) ^ (1 - 1) = 1 by norm_num, Work.Higman.powSub_one_eq] at htop'
    exact card_le_cube_of_comm_le h (hDA.trans (le_of_eq hAeq))
  · -- ## `e = 2`: `A² = Ω₁(P)`
    have hA2 : Work.Higman.powSub A 2 = Work.Higman.omega1 P := by
      rw [he] at htop'
      simpa using htop'
    have hAcard2 : Nat.card ↥A = (Nat.card ↥(Work.Higman.omega1 P)) ^ 2 := by
      rw [hAcard, he]
    obtain ⟨s, hs⟩ := hsub ⁅(⊤ : Subgroup P), ⊤⁆ hDA (map_commutator_top_xi h)
    rcases Nat.eq_zero_or_pos s with hs0 | hspos
    · -- ## the `C₄` shape `[P,P] = A`
      have hGs : ⁅(⊤ : Subgroup P), ⊤⁆ = A := by
        rw [hs, hs0, show (2 : ℕ) ^ 0 = 1 by norm_num, Work.Higman.powSub_one_eq]
      by_cases hirr : ∀ D : Subgroup P, D.Normal →
          D.map (h.xi : MulAut P).toMonoidHom = D → A ≤ D → D = A ∨ D = ⊤
      · exact False.elim (nsm_irreducible_clean h hAxi hAab hNA hGs hsq hA4 hA2 hAcard2 hirr)
      · -- `P/A` is reducible: the reducible case of Higman's Lemma 8, with the induction
        -- hypothesis available for smaller Suzuki 2-groups.
        have hAmax' : ∀ B : Subgroup P, Work.Higman.IsXiAbelNormal h B → A ≤ B → B = A :=
          fun B hB hAB => hAmax B hB.1 hB.2.1 hB.2.2 hAB
        push_neg at hirr
        obtain ⟨D, hDn, hDxi, hAD, hDAne, hDtop⟩ := hirr
        have hdata : ∃ E : Subgroup P, E.Normal ∧ E.map (h.xi : MulAut P).toMonoidHom = E ∧
            A < E ∧ E < ⊤ :=
          ⟨D, hDn, hDxi, lt_of_le_of_ne hAD (Ne.symm hDAne), lt_of_le_of_ne le_top hDtop⟩
        exact False.elim (c4_reducible_small_placeholder h ⟨hAn, hAxi, hAab⟩ hAmax' hNA hGs hsq
          hA4 hA2 hAcard2 hdata hsmall)
    · -- ## `[P,P] ≤ A² = Ω₁(P)`
      have hle : ⁅(⊤ : Subgroup P), ⊤⁆ ≤ Work.Higman.omega1 P := by
        rw [hs, ← hA2]
        exact Work.Higman.powSub_le_of_dvd hAab (by simpa using Nat.pow_dvd_pow 2 hspos)
      exact card_le_cube_of_comm_le h hle

/-- **Higman's order bound: `|P| ≤ |Ω₁(P)| ^ 3`** for a Suzuki 2-group.

(This workspace contains a sorried statement of this bound as `Work.Higman.H8.c4_card_le`; this is
a fresh copy so that the proof can be developed without touching that file.)

Mathematically this is the numerical half of Higman (1963), Theorem 1: a Suzuki 2-group has order
`q ^ 2` or `q ^ 3` with `q = |Ω₁(P)|`, and `Ω₁(P) = Z(P) = Φ(P) = P'`.

Proof: strong induction on `|P|` (`card_le_cube_step`), using Higman's Lemmas 1 and 9, the
class-two Chevalley–Warning bound `card_le_cube_of_comm_le`, and the `C₄` exclusion
(Higman's Lemma 8) in the two available forms `nsm_irreducible_clean` (irreducible case) and
`c4_reducible_small` (reducible case). -/
theorem card_le_cube_suzuki {P : Type} [Group P] [Finite P] (h : Work.Higman.IsSuzuki2Grp P) :
    Nat.card P ≤ (Nat.card ↥(Work.Higman.omega1 P)) ^ 3 := by
  have key : ∀ (m : ℕ), ∀ (Q : Type) [Group Q] [Finite Q], Nat.card Q = m →
      Work.Higman.IsSuzuki2Grp Q → Nat.card Q ≤ (Nat.card ↥(Work.Higman.omega1 Q)) ^ 3 := by
    intro m
    refine Nat.strong_induction_on m (fun m ih => ?_)
    intro Q _ _ hQm hQ
    exact card_le_cube_step hQ (fun R _ _ hR hlt =>
      ih (Nat.card R) (by rw [← hQm]; exact hlt) R rfl hR)
  exact key (Nat.card P) P rfl h

end Work.Higman.H8
