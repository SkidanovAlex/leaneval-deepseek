import Mathlib
import Submission.Work.Diff.Alg.Pinch.inPIC2_metric_basic
import Submission.Work.Diff.Alg.PA.Defs

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

namespace Work.Diff.Alg.Pinch

open Finset Submission.Diff.Alg

set_option linter.unusedVariables false

/-- **The cone `PIC2` meets the hyperplane `Ric = 0` only at the origin.**

If an algebraic curvature tensor `R` has nonnegative complex sectional curvature (`InPIC2`, i.e.
`R ∈ Ĉ`) and vanishing Ricci tensor, then `R = 0`.

The argument uses only the *real* form of `InPIC2` together with the trace identity relating the
Ricci quadratic form to the sectional curvatures of an orthonormal frame:

* `InPIC2 R` at `(x, 0, z, 0)` gives `secK R x z = R4 R x z x z ≥ 0`;
* `ricForm_eq` writes the Ricci quadratic form `∑ᵢⱼ ric R i j vᵢ vⱼ` as the sum
  `∑ₖ R4 R eₖ v eₖ v = ∑ₖ secK R eₖ v` over the standard frame `eₖ`; since `ric R = 0` and each
  term is nonnegative, *every* basis sectional curvature `secK R eₖ v` vanishes;
* evaluating the defining quartic form at `(eᵢ, ±eⱼ, eₖ, e_l)` bounds `±Rᵢⱼₖₗ` by
  `½(Rᵢₖᵢₖ + Rᵢₗᵢₗ + Rⱼₖⱼₖ + Rⱼₗⱼₗ)`, and the four diagonal components are `secK` of standard
  basis pairs, hence `0`; so every component `Rᵢⱼₖₗ` vanishes. -/
theorem inPIC2_ric_eq_zero (n : ℕ) {R : Submission.Diff.Alg.Curv4 n}
    (hR : Submission.Diff.Alg.IsAlgCurv R) (hP : Submission.Diff.Alg.InPIC2 R)
    (hric : ∀ i j, Work.Diff.Alg.Pinch.ric R i j = 0) : R = 0 := by
  -- (1) `InPIC2` implies nonnegative sectional curvature (`y = w = 0`).
  have hsec : ∀ u v : Fin n → ℝ, 0 ≤ secK R u v := fun u v => by
    simpa [secK] using inPIC2_R4_nonneg R hP u v
  -- (2) the Ricci quadratic form is the frame sum of the sectional curvatures `secK eₖ v`.
  have hsum : ∀ v : Fin n → ℝ, (∑ k, secK R (Pi.single k 1) v) = 0 := by
    intro v
    have h : (∑ i, ∑ j, ric R i j * v i * v j) = ∑ k, secK R (Pi.single k 1) v := by
      simpa [ric, secK] using ricForm_eq R v
    rw [← h]
    simp [hric]
  -- (3) hence every sectional curvature of a plane spanned by a basis vector vanishes.
  have hdiag : ∀ k : Fin n, ∀ v : Fin n → ℝ, secK R (Pi.single k 1) v = 0 := by
    intro k v
    have hle : secK R (Pi.single k 1) v ≤ ∑ j, secK R (Pi.single j 1) v :=
      Finset.single_le_sum (fun j _ => hsec (Pi.single j 1) v) (Finset.mem_univ k)
    rw [hsum v] at hle
    exact le_antisymm hle (hsec _ v)
  -- (4) the diagonal components `R a b a b` all vanish.
  have hd : ∀ a b : Fin n, R a b a b = 0 := by
    intro a b
    have h := hdiag a (Pi.single b 1)
    rw [secK, R4_basis] at h
    exact h
  -- (5) `InPIC2` at `(eᵢ, ±eⱼ, eₖ, e_l)` squeezes each component to zero.
  funext i j k l
  have hb1 : R i j k l ≤ 0 := by
    have h := hP (Pi.single i 1) (Pi.single j 1) (Pi.single k 1) (Pi.single l 1)
    simp only [R4_basis] at h
    rw [hd i k, hd i l, hd j k, hd j l] at h
    linarith
  have hb2 : 0 ≤ R i j k l := by
    have h := hP (Pi.single i 1) ((-1 : ℝ) • Pi.single j 1) (Pi.single k 1) (Pi.single l 1)
    simp only [Work.Diff.Alg.PA.R4_smul₁, Work.Diff.Alg.PA.R4_smul₂,
      Work.Diff.Alg.PA.R4_smul₃, R4_basis] at h
    rw [hd i k, hd i l, hd j k, hd j l] at h
    linarith
  simp only [Pi.zero_apply]
  linarith

end Work.Diff.Alg.Pinch
