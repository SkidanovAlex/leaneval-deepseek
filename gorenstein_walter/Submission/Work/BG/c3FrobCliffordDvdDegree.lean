import Mathlib
import Submission.Work.BG._c3frob_probe

namespace Work.BG

/-- **Clifford: the degree of an irreducible character is a multiple of the degree of any
constituent of its restriction to a normal subgroup.**

For `H ⊴ Y`, `χ ∈ Irr Y` lying over `θ ∈ Irr H`, Clifford's degree formula
(`apply_one_eq_restrictionMultiplicity_mul_index_inertia`) gives
`χ(1) = ⟨Res_H χ, θ⟩ · [Y : I_Y(θ)] · θ(1)`, the first factor being a natural number
(`restrictionMultiplicity_natCast`) and the second a natural number.  Hence `θ(1) ∣ χ(1)`, and
divisibility of `θ(1)` by `c` transfers to `χ(1)`. -/
theorem c3FrobCliffordDvdDegree {Y : Type} [Group Y] [Finite Y] [Fintype Y]
    [Invertible (Nat.card Y : ℂ)] (H : Subgroup Y) [H.Normal]
    [Fintype ↥H] [Invertible (Nat.card ↥H : ℂ)]
    (χ : OddOrder.RepresentationTheory.IrreducibleCharacter Y)
    (θ : OddOrder.RepresentationTheory.IrreducibleCharacter ↥H)
    (hover : OddOrder.RepresentationTheory.IrreducibleCharacter.LiesOver H χ θ) (c : ℕ)
    (hc : ∃ d : ℕ, (θ : OddOrder.RepresentationTheory.ClassFunction ↥H ℂ) 1 = (d : ℂ) ∧ c ∣ d) :
    ∃ e : ℕ, (χ : OddOrder.RepresentationTheory.ClassFunction Y ℂ) 1 = (e : ℂ) ∧ c ∣ e := by
  obtain ⟨d, hd, hcd⟩ := hc
  haveI : Finite (OddOrder.RepresentationTheory.IrreducibleCharacter ↥H) :=
    OddOrder.RepresentationTheory.finite_irreducibleCharacter
  obtain ⟨k, hk⟩ :=
    OddOrder.RepresentationTheory.IrreducibleCharacter.restrictionMultiplicity_natCast H χ θ
  have hformula :=
    OddOrder.RepresentationTheory.apply_one_eq_restrictionMultiplicity_mul_index_inertia χ θ hover
  refine ⟨k * (OddOrder.RepresentationTheory.IrreducibleCharacter.inertia (G := Y) (H := H) θ).index
      * d, ?_, ?_⟩
  · rw [hformula, hk, hd]
    push_cast
    ring
  · exact dvd_mul_of_dvd_right hcd (k *
      (OddOrder.RepresentationTheory.IrreducibleCharacter.inertia (G := Y) (H := H) θ).index)

end Work.BG
