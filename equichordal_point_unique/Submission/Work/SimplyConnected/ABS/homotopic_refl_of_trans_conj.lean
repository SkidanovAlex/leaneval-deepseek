import Mathlib

namespace Work.SimplyConnected.ABS

/-- Conjugation in the fundamental groupoid: if the loop `ρ⁻¹ ⬝ γ ⬝ ρ` at `p`
is null-homotopic, then so is `γ` at `x`. -/
theorem homotopic_refl_of_trans_conj {X : Type*} [TopologicalSpace X] {x p : X}
    (ρ : Path x p) {γ : Path x x}
    (h : Path.Homotopic ((ρ.symm.trans γ).trans ρ) (Path.refl p)) :
    Path.Homotopic γ (Path.refl x) := by
  have hA : Path.Homotopic.Quotient.mk ((ρ.symm.trans γ).trans ρ) =
      Path.Homotopic.Quotient.refl p :=
    Path.Homotopic.Quotient.eq.mpr h
  apply Path.Homotopic.Quotient.eq.mp
  calc Path.Homotopic.Quotient.mk γ
      = ((Path.Homotopic.Quotient.mk ρ).trans
            (Path.Homotopic.Quotient.mk ((ρ.symm.trans γ).trans ρ))).trans
          ((Path.Homotopic.Quotient.mk ρ).symm) := by
          simp only [Path.Homotopic.Quotient.mk_trans, Path.Homotopic.Quotient.mk_symm]
          rw [← Path.Homotopic.Quotient.trans_assoc, ← Path.Homotopic.Quotient.trans_assoc,
              Path.Homotopic.Quotient.trans_symm, Path.Homotopic.Quotient.refl_trans,
              Path.Homotopic.Quotient.trans_assoc, Path.Homotopic.Quotient.trans_symm,
              Path.Homotopic.Quotient.trans_refl]
    _ = ((Path.Homotopic.Quotient.mk ρ).trans (Path.Homotopic.Quotient.refl p)).trans
          ((Path.Homotopic.Quotient.mk ρ).symm) := by rw [hA]
    _ = Path.Homotopic.Quotient.refl x := by
          rw [Path.Homotopic.Quotient.trans_refl, Path.Homotopic.Quotient.trans_symm]

end Work.SimplyConnected.ABS
