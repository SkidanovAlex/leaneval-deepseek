import Submission.Work.EKLNonExc.DinjAux.Basic

/-!
# The "bad" sets for `Dinj`

`Wset δ = (V δ)⁻¹ * V δ` is the set of displacements `h⁻¹ g` of two points `g, h ∈ V δ`, and
`Lbad δ` is the set of `k : SL₃(ℝ)` for which some `k γ k⁻¹` (`γ ∈ Γ₃`, `γ ≠ 1`) lies in `Wset δ`.
The complement of `Dinj δ` is the image of `Lbad δ` under the quotient map `mkX`.
-/

open scoped Pointwise
set_option backward.isDefEq.respectTransparency false
set_option linter.unusedVariables false

namespace Work.EKLNonExc
namespace DinjAux

open Work.EKLContract Filter Topology

noncomputable section

/-- `V δ` is open for every `δ`. -/
lemma V_open (δ : ℝ) : IsOpen (V δ) := by
  rcases le_or_gt δ 0 with h | h
  · have : V δ = ∅ := by
      ext g
      simp only [Set.mem_empty_iff_false, iff_false]
      intro hg
      have h00 := hg 0 0
      have h0 := abs_nonneg (g 0 0 - (1 : M3) 0 0)
      linarith
    rw [this]
    exact isOpen_empty
  · exact (Work.EKLContract.Lemmas.V_open_one δ h).1

/-- Displacements of two points of `V δ`. -/
def Wset (δ : ℝ) : Set SL3 := (V δ)⁻¹ * V δ

lemma Wset_open (δ : ℝ) : IsOpen (Wset δ) := by
  rw [Wset]
  exact IsOpen.mul_right ((V_open δ).inv)

lemma mem_Wset {δ : ℝ} {x : SL3} :
    x ∈ Wset δ ↔ ∃ a ∈ (V δ)⁻¹, ∃ b ∈ V δ, x = a * b := by
  rw [Wset, Set.mem_mul]
  constructor
  · rintro ⟨a, ha, b, hb, heq⟩; exact ⟨a, ha, b, hb, heq.symm⟩
  · rintro ⟨a, ha, b, hb, heq⟩; exact ⟨a, ha, b, hb, heq.symm⟩

/-- The "bad" set of group elements: conjugates `k γ k⁻¹` of nontrivial `γ ∈ Γ₃` that lie in
`Wset δ`. -/
def Lbad (δ : ℝ) : Set SL3 :=
  ⋃ (γ : Γ3) (_ : γ ≠ 1), {k : SL3 | k * (γ : SL3) * k⁻¹ ∈ Wset δ}

lemma mem_Lbad {δ : ℝ} {k : SL3} :
    k ∈ Lbad δ ↔ ∃ γ : Γ3, γ ≠ 1 ∧ k * (γ : SL3) * k⁻¹ ∈ Wset δ := by
  simp [Lbad]

lemma isOpen_Lbad (δ : ℝ) : IsOpen (Lbad δ) := by
  rw [Lbad]
  refine isOpen_iUnion (fun γ => ?_)
  refine isOpen_iUnion (fun _ : γ ≠ 1 => ?_)
  exact (Wset_open δ).preimage (by fun_prop)

end

end DinjAux
end Work.EKLNonExc
