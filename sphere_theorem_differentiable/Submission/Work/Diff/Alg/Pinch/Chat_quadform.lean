import Mathlib
import Submission.Work.Diff.Alg.Pinch.ChatDefs
import Submission.Work.Diff.Alg.Pinch.inPIC2_cone_basic
import Submission.Work.Diff.Alg.PA.R4_bianchi
import Submission.Work.Diff.Alg.PA.Defs
import Submission.Work.Diff.Alg.Pinch.Phi_wedge

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

namespace Work.Diff.Alg.Pinch

open Finset Submission.Diff.Alg

variable {n : ℕ}

/-!
## The real-coordinate dictionary for `Phi` on a decomposable form

The identity `Phi_wedge` (`Diff/Alg/Pinch/Phi_wedge`) computes the ℂ-bilinear pairing `Phi`
(`Diff/Alg/Pinch/Qop`) of the decomposable complex `2`-form `ζ ∧ η` with its conjugate:

`Phi D (ζ ∧ η) (conj (ζ ∧ η)) = 4 · (EFun D (Re ζ) (Im ζ) (Re η) (Im η) : ℂ)`.

The three lemmas below translate this complex statement into the real coordinates used by `qfA`
and `qfB` (`Diff/Alg/Pinch/ChatDefs`): the components of `ζ ∧ η` are `qfA + i · qfB`
(`wedgeF_ofRealI`), componentwise conjugation negates the imaginary part (`bar_apply` + the same
lemma), and the real part of a single summand `Dᵢⱼₖₗ (a₁ + i b₁)(a₂ - i b₂)` is
`Dᵢⱼₖₗ (a₁a₂ + b₁b₂)` (`re_mul_star`), which is exactly the integrand of the Hermitian form in
`Chat_quadform`.
-/

/-- Real part of a single term of the Hermitian pairing: for real `D` and reals `a₁ b₁ a₂ b₂`,
`Re (D · (a₁ + i b₁) · conj (a₂ + i b₂)) = D (a₁a₂ + b₁b₂)`. -/
private theorem re_mul_star (D a₁ b₁ a₂ b₂ : ℝ) :
    ((D : ℂ) * ((a₁ : ℂ) + (b₁ : ℂ) * Complex.I)
        * star ((a₂ : ℂ) + (b₂ : ℂ) * Complex.I)).re = D * (a₁ * a₂ + b₁ * b₂) := by
  simp only [Complex.mul_re, Complex.add_re, Complex.add_im, Complex.mul_im, Complex.ofReal_re,
    Complex.ofReal_im, Complex.I_re, Complex.I_im, Complex.star_def, Complex.conj_re,
    Complex.conj_im]
  ring

/-- The real coordinates of the decomposable complex `2`-form `(x + iy) ∧ (z + iw)`: its `(a,b)`
component is `qfA x y z w a b + i · qfB x y z w a b`. -/
private theorem wedgeF_ofRealI (x y z w : Fin n → ℝ) (a b : Fin n) :
    wedgeF (fun i => (x i : ℂ) + (y i : ℂ) * Complex.I)
        (fun i => (z i : ℂ) + (w i : ℂ) * Complex.I) (a, b)
      = (qfA x y z w a b : ℂ) + (qfB x y z w a b : ℂ) * Complex.I := by
  simp only [wedgeF, qfA, qfB]
  apply Complex.ext <;>
    simp only [Complex.add_re, Complex.sub_re, Complex.mul_re, Complex.mul_im, Complex.ofReal_re,
      Complex.ofReal_im, Complex.I_re, Complex.I_im, Complex.add_im, Complex.sub_im] <;>
    ring

/-- One summand of `Phi D (ζ ∧ η) (conj (ζ ∧ η))` in real coordinates. -/
private theorem term_eq (D : Curv4 n) (x y z w : Fin n → ℝ) (a b c d : Fin n) :
    (((D a b c d : ℂ) *
        wedgeF (fun i => (x i : ℂ) + (y i : ℂ) * Complex.I)
          (fun i => (z i : ℂ) + (w i : ℂ) * Complex.I) (a, b) *
        bar (wedgeF (fun i => (x i : ℂ) + (y i : ℂ) * Complex.I)
          (fun i => (z i : ℂ) + (w i : ℂ) * Complex.I)) (c, d)).re)
      = D a b c d * (qfA x y z w a b * qfA x y z w c d
        + qfB x y z w a b * qfB x y z w c d) := by
  rw [bar_apply, wedgeF_ofRealI x y z w c d, wedgeF_ofRealI x y z w a b]
  exact re_mul_star _ _ _ _ _

/-- For an algebraic curvature tensor `D`, the quartic form `Cone.EF D` (whose nonnegativity is `InPIC2 D`) is a Hermitian form on the decomposable complex `2`-form `ζ ∧ η` (`ζ = x + iy`, `η = z + iw`), written out in real coordinates through `qfA`, `qfB` (defined in `Diff/Alg/Pinch/ChatDefs`: they are the real and imaginary parts of `ζᵢηⱼ - ζⱼηᵢ`).

Route: first prove `4 * R4 D a b c d = ∑ᵢⱼₖₗ Dᵢⱼₖₗ σ(a,b)ᵢⱼ σ(c,d)ₖₗ` where `σ(a,b)ᵢⱼ = aᵢbⱼ - aⱼbᵢ` (uses antisymmetry in the first two slots plus pair symmetry of `D`).  Then use the first Bianchi identity in the form `R4 D x y z w = R4 D x z y w - R4 D x w y z` (from `R4_bianchi` of `Submission.Work.Diff.Alg.PA.R4_bianchi` together with antisymmetry and pair symmetry).  Finally use the reindexing `∑ Dᵢⱼₖₗ Xᵢⱼ Yₖₗ = ∑ Dᵢⱼₖₗ Yᵢⱼ Xₖₗ` (pair symmetry + `sum4_swap12`/`sum4_swap34` from `PA.Defs`) to recognise the cross terms as the squares of `qfA = σ(x,z) - σ(y,w)` and `qfB = σ(x,w) + σ(y,z)`. -/
theorem Chat_quadform {n : ℕ} {D : Submission.Diff.Alg.Curv4 n}
    (hD : Submission.Diff.Alg.IsAlgCurv D) (x y z w : Fin n → ℝ) :
    4 * Work.Diff.Alg.Pinch.Cone.EF D x y z w
      = ∑ i, ∑ j, ∑ k, ∑ l,
          D i j k l * (Work.Diff.Alg.Pinch.qfA x y z w i j
              * Work.Diff.Alg.Pinch.qfA x y z w k l
            + Work.Diff.Alg.Pinch.qfB x y z w i j
              * Work.Diff.Alg.Pinch.qfB x y z w k l) := by
  -- `Phi` of the decomposable form against its conjugate is `4 · EF D`
  have hre : (Phi D
      (wedgeF (fun i => (x i : ℂ) + (y i : ℂ) * Complex.I)
        (fun i => (z i : ℂ) + (w i : ℂ) * Complex.I))
      (bar (wedgeF (fun i => (x i : ℂ) + (y i : ℂ) * Complex.I)
        (fun i => (z i : ℂ) + (w i : ℂ) * Complex.I)))).re
      = 4 * Cone.EF D x y z w := by
    rw [Phi_wedge n D hD]
    simp only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im]
    have h1 : Q2P.cRe (fun i => (x i : ℂ) + (y i : ℂ) * Complex.I) = x := by
      ext i; simp [Q2P.cRe]
    have h2 : Q2P.cIm (fun i => (x i : ℂ) + (y i : ℂ) * Complex.I) = y := by
      ext i; simp [Q2P.cIm]
    have h3 : Q2P.cRe (fun i => (z i : ℂ) + (w i : ℂ) * Complex.I) = z := by
      ext i; simp [Q2P.cRe]
    have h4 : Q2P.cIm (fun i => (z i : ℂ) + (w i : ℂ) * Complex.I) = w := by
      ext i; simp [Q2P.cIm]
    rw [h1, h2, h3, h4]
    norm_num
    rfl
  -- the real part of that pairing is the sum of the `qfA`- and `qfB`-squares
  have hPhi : (Phi D
      (wedgeF (fun i => (x i : ℂ) + (y i : ℂ) * Complex.I)
        (fun i => (z i : ℂ) + (w i : ℂ) * Complex.I))
      (bar (wedgeF (fun i => (x i : ℂ) + (y i : ℂ) * Complex.I)
        (fun i => (z i : ℂ) + (w i : ℂ) * Complex.I)))).re
      = ∑ i, ∑ j, ∑ k, ∑ l,
          D i j k l * (Work.Diff.Alg.Pinch.qfA x y z w i j
              * Work.Diff.Alg.Pinch.qfA x y z w k l
            + Work.Diff.Alg.Pinch.qfB x y z w i j
              * Work.Diff.Alg.Pinch.qfB x y z w k l) := by
    rw [Phi_quad]
    simp only [Complex.re_sum]
    refine Finset.sum_congr rfl (fun a _ => ?_)
    refine Finset.sum_congr rfl (fun b _ => ?_)
    refine Finset.sum_congr rfl (fun c _ => ?_)
    refine Finset.sum_congr rfl (fun d _ => ?_)
    exact term_eq D x y z w a b c d
  rw [← hre, hPhi]

end Work.Diff.Alg.Pinch
