import Mathlib
import Submission.Work.Higman.Defs
import Submission.Work.Higman.Basic
import Submission.Work.Higman.PowSub
import Submission.Work.Higman.SuzukiMaximal
import Submission.Work.Higman.OmegaAux
import Submission.Work.Higman.homogeneous_structure
import Submission.Work.Higman.suzuki_unipotence

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

open scoped commutatorElement

namespace Work.Higman.RedAux

variable {P : Type} [Group P] [Finite P]

/-- `⁅x,y⁆` is a product of squares, so it lies in `powSub ⊤ 2`. -/
theorem commutator_mem_powSub_top' (x y : P) : ⁅x, y⁆ ∈ powSub (⊤ : Subgroup P) 2 := by
  have h1 : (x * y) * (x * y) ∈ powSub (⊤ : Subgroup P) 2 := by
    simpa [pow_two] using
      pow_mem_powSub (A := (⊤ : Subgroup P)) (n := 2) (x := x * y) (Subgroup.mem_top (x * y))
  have h2 : (y⁻¹ * x⁻¹ * y) * (y⁻¹ * x⁻¹ * y) ∈ powSub (⊤ : Subgroup P) 2 := by
    simpa [pow_two] using
      pow_mem_powSub (A := (⊤ : Subgroup P)) (n := 2) (x := y⁻¹ * x⁻¹ * y) (Subgroup.mem_top _)
  have h3 : y⁻¹ * y⁻¹ ∈ powSub (⊤ : Subgroup P) 2 := by
    simpa [pow_two] using
      pow_mem_powSub (A := (⊤ : Subgroup P)) (n := 2) (x := y⁻¹) (Subgroup.mem_top _)
  have hmem := Subgroup.mul_mem _ (Subgroup.mul_mem _ h1 h2) h3
  rw [show ⁅x, y⁆ = (x * y) * (x * y) * ((y⁻¹ * x⁻¹ * y) * (y⁻¹ * x⁻¹ * y)) * (y⁻¹ * y⁻¹)
    from by rw [commutatorElement_def]; group]
  exact hmem

/-- The `ξ`-invariant subgroups of `A` are `⊥`, `A^(2)`, `A`. -/
theorem red_trichotomy (h : IsSuzuki2Grp P) (A : Subgroup P) (B : Subgroup P)
    (hA : IsXiAbelNormal h A) (hA4 : powSub A 4 = ⊥) (hBA : B ≤ A)
    (hBin : B.map (h.xi : MulAut P).toMonoidHom = B) :
    B = ⊥ ∨ B = powSub A 2 ∨ B = A := by
  obtain ⟨e, -, -, -, hsub⟩ := homogeneous_structure h hA.abelian hA.map_eq
  obtain ⟨i, hi⟩ := hsub B hBA hBin
  rcases Nat.eq_zero_or_pos i with h0 | hpos
  · exact Or.inr (Or.inr (by rw [hi, h0, pow_zero, powSub_one_eq]))
  · rcases Nat.lt_or_ge i 2 with hlt | hge
    · exact Or.inr (Or.inl (by rw [hi, show i = 1 by omega]; norm_num))
    · refine Or.inl ?_
      rw [hi]
      have hdvd : 4 ∣ 2 ^ i := ⟨2 ^ (i - 2), by
        rw [show (4 : ℕ) = 2 ^ 2 by norm_num, ← pow_add]
        congr 1; omega⟩
      exact le_bot_iff.mp ((powSub_le_of_dvd hA.abelian hdvd).trans hA4.le)

/-- `A ≠ A²` under the `C₄` hypotheses (`|A| = |Ω₁(P)|²`, `A² = Ω₁(P)`, `4 ≤ |Ω₁(P)|`). -/
theorem ne_powSub_two_of_card (h : IsSuzuki2Grp P) {A : Subgroup P}
    (htop : powSub A 2 = omega1 P)
    (hcard : Nat.card ↥A = (Nat.card ↥(omega1 P)) ^ 2) : A ≠ powSub A 2 := by
  intro heq
  rw [heq, htop] at hcard
  have h2 : 4 ≤ Nat.card ↥(omega1 P) := h.omega1_card_ge_four
  nlinarith [hcard, h2]

theorem commutator_eq_powSub_two_or_self (h : IsSuzuki2Grp P) (A : Subgroup P)
    (hA : IsXiAbelNormal h A) (hA4 : powSub A 4 = ⊥) :
    ⁅A, (⊤ : Subgroup P)⁆ = ⊥ ∨ ⁅A, (⊤ : Subgroup P)⁆ = powSub A 2
      ∨ ⁅A, (⊤ : Subgroup P)⁆ = A := by
  have hle : ⁅A, (⊤ : Subgroup P)⁆ ≤ powSub A 2 := by
    rw [Subgroup.commutator_le]
    intro a ha x _
    have h1 : ⁅x, a⁆ ∈ powSub A 2 := commutator_mem_powSub_two h hA x a ha
    rw [show ⁅a, x⁆ = ⁅x, a⁆⁻¹ from by
      rw [commutatorElement_def, commutatorElement_def]; group]
    exact Subgroup.inv_mem _ h1
  have hinv : (⁅A, (⊤ : Subgroup P)⁆).map (h.xi : MulAut P).toMonoidHom
      = ⁅A, (⊤ : Subgroup P)⁆ := by
    rw [Subgroup.map_commutator, hA.map_eq,
      Subgroup.map_top_of_surjective _ (h.xi : MulAut P).surjective]
  exact red_trichotomy h A (⁅A, (⊤ : Subgroup P)⁆) hA hA4
      (hle.trans (powSub_le (by norm_num)) : ⁅A, (⊤ : Subgroup P)⁆ ≤ A) hinv

end Work.Higman.RedAux
