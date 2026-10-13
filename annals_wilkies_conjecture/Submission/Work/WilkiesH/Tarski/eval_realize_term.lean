/-
# Terms of the language of rings over polynomial functions

Every term of the language of rings (with function symbols `+`, `*`, `-`, `0`, `1`) whose free
variables are interpreted by polynomials `ρ b ∈ ℝ[X]` evaluates, under an assignment `v` of the
coordinates, to a polynomial *function*: there is a single polynomial `P` with

`Term.realize (fun b => eval v (ρ b)) t = eval v P`  for every `v`.

This is the `Term` case of the Tarski–Seidenberg bridge
(`Work.WilkiesH.Tarski.definable_iff_polynomialSignSet`): the polynomial functions of the
coordinates are closed under the ring operations, proven by induction on the term.
-/
import Mathlib
import Submission.Work.WilkiesI.Basic

namespace Work.WilkiesH.Tarski

open FirstOrder FirstOrder.Language

theorem eval_realize_term {β ι : Type*} (ρ : β → MvPolynomial ι ℝ)
    (t : FirstOrder.Language.ring.Term β) :
    ∃ P : MvPolynomial ι ℝ, ∀ v : ι → ℝ,
      FirstOrder.Language.Term.realize (fun b => MvPolynomial.eval v (ρ b)) t = MvPolynomial.eval v P := by
  induction t with
  | var b => exact ⟨ρ b, fun v => rfl⟩
  | func f ts ih =>
    cases f with
    | add =>
      obtain ⟨P₀, h₀⟩ := ih 0
      obtain ⟨P₁, h₁⟩ := ih 1
      refine ⟨P₀ + P₁, fun v => ?_⟩
      simp only [Term.realize, Ring.CompatibleRing.funMap_add]
      rw [h₀ v, h₁ v]
      simp
    | mul =>
      obtain ⟨P₀, h₀⟩ := ih 0
      obtain ⟨P₁, h₁⟩ := ih 1
      refine ⟨P₀ * P₁, fun v => ?_⟩
      simp only [Term.realize, Ring.CompatibleRing.funMap_mul]
      rw [h₀ v, h₁ v]
      simp
    | neg =>
      obtain ⟨P₀, h₀⟩ := ih 0
      refine ⟨-P₀, fun v => ?_⟩
      simp only [Term.realize, Ring.CompatibleRing.funMap_neg]
      rw [h₀ v]
      simp
    | zero =>
      refine ⟨0, fun v => ?_⟩
      simp only [Term.realize, Ring.CompatibleRing.funMap_zero]
      simp
    | one =>
      refine ⟨1, fun v => ?_⟩
      simp only [Term.realize, Ring.CompatibleRing.funMap_one]
      simp

end Work.WilkiesH.Tarski
