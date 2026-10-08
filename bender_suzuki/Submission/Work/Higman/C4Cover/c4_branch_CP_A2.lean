import Mathlib
import Submission.Work.Higman.Defs
import Submission.Work.Higman.Basic
import Submission.Work.Higman.PowSub
import Submission.Work.Higman.RedAux.setup
import Submission.Work.Higman.no_cent_elt_outside_maximal

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

set_option autoImplicit false
set_option linter.unusedVariables false

namespace Work.Higman.C4Cover

open scoped commutatorElement

/-- **The `A ^ (2)` branch of the `C₄` cover is empty.**

Let `P` be a Suzuki 2-group, `A = [P,P]` abelian normal with `A ^ (4) = 1`,
`A ^ (2) = Ω₁(P)` and `|A| = |Ω₁(P)|²` (so `A` has exponent exactly `4` and
`|A : A²| = |A²|`), `C_P(A) = A`, and let `C` be a `ξ`-invariant normal subgroup with
`A ≤ C`, `A ≠ C` and `[C,P] = A ^ (2)`.  Then all squares of `P` lie in `A ^ (2)`, whence
`A = [P,P] ≤ A ^ (2)`, contradicting `|A| = |Ω₁(P)|²` with `|Ω₁(P)| ≥ 4`. -/
theorem c4_branch_CP_A2 {P : Type} [Group P] [Finite P] (h : Work.Higman.IsSuzuki2Grp P)
    {A C : Subgroup P}
    (hAn : A.Normal)
    (hAab : ∀ x ∈ A, ∀ y ∈ A, x * y = y * x)
    (hGs : Bracket.bracket (⊤ : Subgroup P) (⊤ : Subgroup P) = A)
    (hsq : ∀ x : P, x ^ 2 ∈ A)
    (hA4 : Work.Higman.powSub A 4 = ⊥)
    (htop : Work.Higman.powSub A 2 = Work.Higman.omega1 P)
    (hcard : Nat.card ↥A = (Nat.card ↥(Work.Higman.omega1 P)) ^ 2)
    (hcent : Subgroup.centralizer (A : Set P) = A)
    (hCn : C.Normal) (hCinv : C.map (h.xi : MulAut P).toMonoidHom = C)
    (hAC : A ≤ C) (hCA : A ≠ C)
    (hCP : Bracket.bracket C (⊤ : Subgroup P) = Work.Higman.powSub A 2) :
    False := by
  classical
  -- ## `A` is `ξ`-invariant, hence an element of the standard family.
  have hAxi : A.map (h.xi : MulAut P).toMonoidHom = A := by
    rw [← hGs, Subgroup.map_commutator,
      Subgroup.map_top_of_surjective _ (h.xi : MulAut P).surjective]
  have hA : Work.Higman.IsXiAbelNormal h A := ⟨hAn, hAxi, hAab⟩
  -- ## Elementary consequences of the hypotheses.
  have hA2leA : Work.Higman.powSub A 2 ≤ A := Work.Higman.powSub_le (by norm_num)
  have hA2Z : Work.Higman.powSub A 2 ≤ Subgroup.center P := by
    rw [htop]; exact h.omega1_le_center
  have hA2ne : Work.Higman.powSub A 2 ≠ ⊥ := by
    intro hb
    have h1 : Nat.card ↥(Work.Higman.omega1 P) = 1 := by rw [← htop, hb]; simp
    have h2 := h.omega1_card_ge_four
    omega
  -- ## The centre of `C` (computed in `P`) is `A ^ (2)`.
  have hZeq : C ⊓ Subgroup.centralizer (C : Set P) = Work.Higman.powSub A 2 := by
    have hZleA : C ⊓ Subgroup.centralizer (C : Set P) ≤ A :=
      le_trans inf_le_right
        (le_trans (Subgroup.centralizer_le (fun x hx => hAC hx)) (le_of_eq hcent))
    have hZinv : (C ⊓ Subgroup.centralizer (C : Set P)).map (h.xi : MulAut P).toMonoidHom
        = C ⊓ Subgroup.centralizer (C : Set P) :=
      Work.Higman.map_inf_centralizer_eq (h.xi : MulAut P) hCinv
    have hA2leZ : Work.Higman.powSub A 2 ≤ C ⊓ Subgroup.centralizer (C : Set P) :=
      le_inf (hA2leA.trans hAC) (hA2Z.trans (Subgroup.center_le_centralizer (C : Set P)))
    rcases Work.Higman.RedAux.red_trichotomy h A (C ⊓ Subgroup.centralizer (C : Set P))
        hA hA4 hZleA hZinv with h1 | h1 | h1
    · exact absurd (le_bot_iff.mp (h1 ▸ hA2leZ)) hA2ne
    · exact h1
    · -- `Z(C) = A` forces `C ≤ C_P(A) = A`, contradicting `A ≠ C`.
      exfalso
      apply hCA
      refine le_antisymm hAC ?_
      have hAleCpC : A ≤ Subgroup.centralizer (C : Set P) := by
        intro a ha
        have haZ : a ∈ C ⊓ Subgroup.centralizer (C : Set P) := by rw [h1]; exact ha
        exact haZ.2
      have hCleCpA : C ≤ Subgroup.centralizer (A : Set P) := by
        intro c hc
        exact Subgroup.mem_centralizer_iff.mpr (fun a ha =>
          (Subgroup.mem_centralizer_iff.mp (hAleCpC ha) c hc).symm)
      rwa [hcent] at hCleCpA
  -- ## Every square of `P` lies in `A ^ (2)`.
  have hsq2 : ∀ v : P, v ^ 2 ∈ Work.Higman.powSub A 2 := by
    intro v
    have hvZ : v ^ 2 ∈ C ⊓ Subgroup.centralizer (C : Set P) := by
      refine ⟨hAC (hsq v), ?_⟩
      refine Subgroup.mem_centralizer_iff.mpr (fun c hc => ?_)
      -- `[c⁻¹,v] ∈ [C,P] = A² ≤ Z(P)` is an involution, and `c⁻¹vc = [c⁻¹,v]·v`.
      have hcv : ⁅c⁻¹, v⁆ ∈ Work.Higman.powSub A 2 := by
        have hm : ⁅c⁻¹, v⁆ ∈ ⁅C, (⊤ : Subgroup P)⁆ :=
          Subgroup.commutator_mem_commutator (C.inv_mem hc) (Subgroup.mem_top v)
        rwa [hCP] at hm
      have hdZ : ⁅c⁻¹, v⁆ ∈ Subgroup.center P := hA2Z hcv
      have hd2 : ⁅c⁻¹, v⁆ ^ 2 = 1 := h.mem_omega1.mp (by rw [← htop]; exact hcv)
      have hdv : c⁻¹ * v * c = ⁅c⁻¹, v⁆ * v := by
        rw [commutatorElement_def]; group
      have hw : v * ⁅c⁻¹, v⁆ = ⁅c⁻¹, v⁆ * v := Subgroup.mem_center_iff.mp hdZ v
      have hsqv : c⁻¹ * (v * v) * c = v * v := by
        rw [show c⁻¹ * (v * v) * c = (c⁻¹ * v * c) * (c⁻¹ * v * c) by group, hdv]
        calc ⁅c⁻¹, v⁆ * v * (⁅c⁻¹, v⁆ * v)
            = ⁅c⁻¹, v⁆ * (v * ⁅c⁻¹, v⁆) * v := by group
          _ = ⁅c⁻¹, v⁆ * (⁅c⁻¹, v⁆ * v) * v := by rw [hw]
          _ = ⁅c⁻¹, v⁆ ^ 2 * (v * v) := by rw [pow_two]; group
          _ = v * v := by rw [hd2, one_mul]
      show c * v ^ 2 = v ^ 2 * c
      rw [pow_two]
      have h3 : c * (c⁻¹ * (v * v) * c) = v * v * c := by group
      have hcon := congrArg (fun t => c * t) hsqv
      rw [h3] at hcon
      exact hcon.symm
    rwa [hZeq] at hvZ
  -- ## Consequently `[P,P] ⊆ A ^ (2)`, so `A = A ^ (2)`.
  have hPP : ⁅(⊤ : Subgroup P), (⊤ : Subgroup P)⁆ ≤ Work.Higman.powSub A 2 := by
    rw [Subgroup.commutator_le]
    intro x _ y _
    have h1 : (x * y) * (x * y) ∈ Work.Higman.powSub A 2 := by
      simpa [pow_two] using hsq2 (x * y)
    have h2 : (y⁻¹ * x⁻¹ * y) * (y⁻¹ * x⁻¹ * y) ∈ Work.Higman.powSub A 2 := by
      simpa [pow_two] using hsq2 (y⁻¹ * x⁻¹ * y)
    have h3 : y⁻¹ * y⁻¹ ∈ Work.Higman.powSub A 2 := by
      simpa [pow_two] using hsq2 y⁻¹
    rw [show ⁅x, y⁆
          = (x * y) * (x * y) * ((y⁻¹ * x⁻¹ * y) * (y⁻¹ * x⁻¹ * y)) * (y⁻¹ * y⁻¹)
        from by rw [commutatorElement_def]; group]
    exact Subgroup.mul_mem _ (Subgroup.mul_mem _ h1 h2) h3
  have hAle2 : A ≤ Work.Higman.powSub A 2 := by
    have hh := hPP
    rwa [hGs] at hh
  have hAeq : A = Work.Higman.powSub A 2 := le_antisymm hAle2 hA2leA
  -- ## Cardinality contradiction.
  have hc : Nat.card ↥(Work.Higman.omega1 P) = (Nat.card ↥(Work.Higman.omega1 P)) ^ 2 := by
    have hh := hcard
    rwa [hAeq, htop] at hh
  have h4 := h.omega1_card_ge_four
  nlinarith [hc, h4]

end Work.Higman.C4Cover
