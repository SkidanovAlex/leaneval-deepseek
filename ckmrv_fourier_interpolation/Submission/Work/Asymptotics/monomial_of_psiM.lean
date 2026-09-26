import Mathlib
import Submission.Work.Asymptotics.psiOdd

namespace Work.Asymptotics

open Work.Kernels
open Work.Modular.PresGroup (FP Cyc C2 C3 gC2 gC3 ofFree)
open scoped MonoidAlgebra MatrixGroups

noncomputable section

/-!
## `psiM` is a monomial on the group generators of `R = ℂ[SL(2,ℤ)]`

The map `ψ : ℂ[ℤ/2 ∗ ℤ/3] → ℂ[SL(2,ℤ)]` used in the residue computation sends each
group element `γ` of the free product to a single monomial: writing `z = -I`,
`e₋ = 2⁻¹(1 - z)`, we show

`psiM (single γ 1) = c • (single w 1 * eMinus)` with `c ≠ 0` and `ofFree γ = toGamma w`.

The proof rests on the three facts
* `psiM (single x 1) = I • (single S 1 * eMinus)`, `psiM (single y 1) = -1 • (single (ST) 1 * eMinus)`
  and `psiM (single y² 1) = 1 • (single (ST)² 1 * eMinus)`,
* `(c • (single w 1 * eMinus)) * (d • (single v 1 * eMinus)) = (cd) • (single (wv) 1 * eMinus)`
  (`e₋` is an idempotent, so odd monomials multiply like monomials),
* every element of `ℤ/2 ∗ ℤ/3` is a product of the letters `1, x, y, y²`.
-/

/-- `ψ` applied to a group element: `ψ(of γ) = φ(γ)`. -/
lemma psi_of_of (γ : FP) : psi (MonoidAlgebra.of ℂ FP γ) = phiFP γ :=
  MonoidAlgebra.lift_of phiFP γ

/-- `psiM` on a group element, in terms of the monoid homomorphism `phiFP`. -/
lemma psiM_of_of (γ : FP) : psiM (MonoidAlgebra.of ℂ FP γ) = phiFP γ * eMinus := by
  rw [psiM, psi_of_of]

/-- Odd monomials multiply: `(c • (m e₋)) * (d • (m' e₋)) = (c d) • ((m m') e₋)`. -/
lemma smul_single_mul_smul_single (c d : ℂ) (w v : Matrix.SpecialLinearGroup (Fin 2) ℤ) :
    (c • (MonoidAlgebra.single w 1 * eMinus)) * (d • (MonoidAlgebra.single v 1 * eMinus))
      = (c * d) • (MonoidAlgebra.single (w * v) 1 * eMinus) := by
  rw [smul_mul_smul, mul_eMinus_mul, MonoidAlgebra.single_mul_single, mul_one]

/-- The invariant: `γ` is carried by `psiM` to a nonzero monomial `single w 1 * eMinus`,
where `w` is a lift of `ofFree γ`. -/
def Motive (γ : FP) : Prop :=
  ∃ (c : ℂ) (_ : c ≠ 0) (w : Matrix.SpecialLinearGroup (Fin 2) ℤ),
    ofFree γ = Work.Residues.toGamma w ∧
      psiM (MonoidAlgebra.of ℂ FP γ)
        = c • (MonoidAlgebra.single w (1 : ℂ) * eMinus)

lemma motive_one : Motive 1 := by
  refine ⟨1, one_ne_zero, 1, ?_, ?_⟩
  · rw [map_one, map_one]
  · rw [show MonoidAlgebra.of ℂ FP (1 : FP) = 1 from map_one (MonoidAlgebra.of ℂ FP), psiM_one,
      ← MonoidAlgebra.one_def, one_mul, one_smul]

lemma motive_mul {a b : FP} (ha : Motive a) (hb : Motive b) : Motive (a * b) := by
  obtain ⟨c, hc, w, hw1, hw2⟩ := ha
  obtain ⟨d, hd, v, hv1, hv2⟩ := hb
  refine ⟨c * d, mul_ne_zero hc hd, w * v, ?_, ?_⟩
  · rw [map_mul, hw1, hv1, map_mul]
  · rw [map_mul, psiM_mul, hw2, hv2, smul_single_mul_smul_single]

lemma motive_x : Motive Work.FreeProduct.x := by
  refine ⟨Complex.I, Complex.I_ne_zero, ModularGroup.S, ?_, ?_⟩
  · rw [ofFree_x, Work.Residues.toGamma_S]
  · simpa using psiM_of_x

lemma motive_y : Motive Work.FreeProduct.y := by
  refine ⟨-1, neg_ne_zero.mpr one_ne_zero, ModularGroup.S * ModularGroup.T, ?_, ?_⟩
  · rw [ofFree_y, map_mul, Work.Residues.toGamma_S, Work.Residues.toGamma_T]
  · simpa using psiM_of_y

lemma motive_y2 : Motive Work.FreeProduct.y2 := by
  refine ⟨1, one_ne_zero, (ModularGroup.S * ModularGroup.T) ^ 2, ?_, ?_⟩
  · rw [ofFree_y2, map_pow, map_mul, Work.Residues.toGamma_S, Work.Residues.toGamma_T]
  · simpa using psiM_of_y2

lemma motive_of_C2 (m : C2) : Motive (Monoid.CoprodI.of (i := false) m) := by
  by_cases hm : m = 1
  · rw [hm, map_one]
    exact motive_one
  · rw [of_of_C2 m hm]
    exact motive_x

lemma motive_of_C3 (m : C3) : Motive (Monoid.CoprodI.of (i := true) m) := by
  by_cases hm : m = 1
  · rw [hm, map_one]
    exact motive_one
  · rcases of_of_C3 m hm with h | h
    · rw [h]; exact motive_y
    · rw [h]; exact motive_y2

lemma motive_of (i : Bool) (m : Cyc i) : Motive (Monoid.CoprodI.of (i := i) m) := by
  cases i
  · exact motive_of_C2 m
  · exact motive_of_C3 m

theorem monomial_of_psiM (γ : Work.Modular.PresGroup.FP) :
    ∃ (c : ℂ) (_ : c ≠ 0) (w : Matrix.SpecialLinearGroup (Fin 2) ℤ),
      Work.Modular.PresGroup.ofFree γ = Work.Residues.toGamma w ∧
        Work.Asymptotics.psiM (MonoidAlgebra.of ℂ Work.Modular.PresGroup.FP γ)
          = c • (MonoidAlgebra.single w (1 : ℂ) * Work.Asymptotics.eMinus) := by
  have h : Motive γ :=
    Monoid.CoprodI.induction_left (motive := Motive) γ motive_one
      (fun {i} m x ih => motive_mul (motive_of i m) ih)
  exact h

end

end Work.Asymptotics
