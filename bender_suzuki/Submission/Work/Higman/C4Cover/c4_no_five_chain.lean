/-
# The `C₄` shape produces a `ξ`-chain of length 5

In the `C₄` setting (`A ⊴ P` abelian `ξ`-invariant, `Ω₁(P) ≤ A`, `⁅P,P⁆ = A`,
`∀x, x² ∈ A`, `A² = Ω₁(P)`, `|A| = |Ω₁(P)|²`, and a minimal `ξ`-invariant normal cover
`C > A` with `⁅C,C⁆ = A²`) the four subgroups

`⊥ < A² = Ω₁(P) < A < C < ⊤`

form a strictly increasing chain of `ξ`-invariant subgroups.  Hence any theorem excluding such a
chain (i.e. `ξ`-length `≤ 3`, Higman's Lemma 13) excludes the `C₄` shape:

`c4_false_of_no_five_chain`.
-/
import Mathlib
import Submission.Work.Higman.C4Cover.c4_cover_card_eq_cube

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

namespace Work.Higman.C4Cover

variable {P : Type} [Group P] [Finite P]

/-- In the `C₄` setting the minimal cover `C` is a proper subgroup (else
`A = ⁅⊤,⊤⁆ = ⁅C,C⁆ = A²`, contradicting `|A| = |Ω₁(P)|² ≠ |Ω₁(P)|`). -/
theorem c4_C_ne_top (h : Work.Higman.IsSuzuki2Grp P) {A C : Subgroup P}
    (hGs : ⁅(⊤ : Subgroup P), ⊤⁆ = A)
    (htop : Work.Higman.powSub A 2 = Work.Higman.omega1 P)
    (hcard : Nat.card ↥A = (Nat.card ↥(Work.Higman.omega1 P)) ^ 2)
    (hCd : ⁅C, C⁆ = Work.Higman.powSub A 2) : C ≠ ⊤ := by
  intro htop'
  have h1 : A = Work.Higman.powSub A 2 := by rw [← hCd, htop', hGs]
  have h2 : Nat.card ↥A = Nat.card ↥(Work.Higman.powSub A 2) :=
    congrArg (fun S : Subgroup P => Nat.card ↥S) h1
  rw [hcard, htop] at h2
  have h4 := h.omega1_card_ge_four
  nlinarith [h2, h4]

/-- **The `C₄` shape is excluded by `ξ`-length `≤ 3`** (no chain of `5` `ξ`-invariant subgroups,
Higman's Lemma 13): the `C₄` shape itself produces the chain `⊥ < A² < A < C < ⊤`. -/
theorem c4_false_of_no_five_chain (h : Work.Higman.IsSuzuki2Grp P) {A C : Subgroup P}
    (hGs : ⁅(⊤ : Subgroup P), ⊤⁆ = A)
    (htop : Work.Higman.powSub A 2 = Work.Higman.omega1 P)
    (hcard : Nat.card ↥A = (Nat.card ↥(Work.Higman.omega1 P)) ^ 2)
    (hCinv : C.map (h.xi : MulAut P).toMonoidHom = C)
    (hAC : A ≤ C) (hCA : A ≠ C)
    (hCd : ⁅C, C⁆ = Work.Higman.powSub A 2)
    (hlen : ¬ ∃ B : Fin 5 → Subgroup P,
      (∀ i : Fin 5, (B i).map (h.xi : MulAut P).toMonoidHom = B i) ∧ StrictMono B) :
    False := by
  have hAxi : A.map (h.xi : MulAut P).toMonoidHom = A := map_xi_of_eq_commutator h hGs
  have hq4 := h.omega1_card_ge_four
  -- the four strict inclusions
  have h01 : (⊥ : Subgroup P) < Work.Higman.powSub A 2 := by
    refine bot_lt_iff_ne_bot.mpr ?_
    intro hbot
    have h1 : Nat.card ↥(Work.Higman.omega1 P) = 1 := by rw [← htop, hbot]; simp
    omega
  have h12 : Work.Higman.powSub A 2 < A := by
    refine lt_of_le_of_ne (Work.Higman.powSub_le (A := A) (by norm_num)) (Ne.symm ?_)
    intro hA
    have h1 : Nat.card ↥(Work.Higman.powSub A 2) = Nat.card ↥A :=
      congrArg (fun S : Subgroup P => Nat.card ↥S) hA.symm
    rw [htop, hcard] at h1
    nlinarith [h1, hq4]
  have h23 : A < C := lt_of_le_of_ne hAC hCA
  have h34 : C < ⊤ := lt_top_iff_ne_top.mpr (c4_C_ne_top h hGs htop hcard hCd)
  -- the chain
  have h02 : (⊥ : Subgroup P) < A := h01.trans h12
  have h03 : (⊥ : Subgroup P) < C := h02.trans h23
  have h04 : (⊥ : Subgroup P) < ⊤ := h03.trans h34
  have h13 : Work.Higman.powSub A 2 < C := h12.trans h23
  have h14 : Work.Higman.powSub A 2 < ⊤ := h13.trans h34
  have h24 : A < ⊤ := h23.trans h34
  refine hlen ⟨![⊥, Work.Higman.powSub A 2, A, C, ⊤], ?_, ?_⟩
  · intro i
    fin_cases i
    · simpa using Subgroup.map_bot (h.xi : MulAut P).toMonoidHom
    · simpa using Work.Higman.map_powSub h.xi hAxi 2
    · simpa using hAxi
    · simpa using hCinv
    · simpa using Subgroup.map_top_of_surjective (h.xi : MulAut P).toMonoidHom
        (h.xi : MulAut P).surjective
  · intro i j hij
    fin_cases i <;> fin_cases j <;> simp only [Fin.isValue, Matrix.cons_val_zero,
      Matrix.cons_val_one, Matrix.head_cons] <;>
      first
        | exact h01 | exact h02 | exact h03 | exact h04
        | exact h12 | exact h13 | exact h14 | exact h23 | exact h24 | exact h34
        | exact absurd hij (by decide)

end Work.Higman.C4Cover
