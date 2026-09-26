import Mathlib
import Submission.Work.PTCert.GlueDefs
import Submission.Work.PTCert.twistedFourierCriterion

namespace Work.PTCert.Klein

open Submission.PTCert

/-- `(ℤ/2)^m` has exponent two. -/
private lemma zmod2_add_self {m : ℕ} (a : Fin m → ZMod 2) : a + a = 0 := by
  funext i; exact CharTwo.add_self_eq_zero (a i)

/-- **Symmetry of the Fourier block.**  For a symmetric (`M.transpose = M`) matrix `M` invariant
under the `(ℤ/2)^m`-action `act`, the twisted Fourier block `fourierW act M S` is symmetric: the
involution `act a` and the symmetry of `M` give `M x (act a y) = M y (act a x)` for every `a`. -/
theorem wSymm {m : ℕ} {ι : Type} (act : (Fin m → ZMod 2) → ι → ι) (M : Matrix ι ι ℝ)
    (S : Finset (Fin m)) (hMsym : M.transpose = M)
    (hact : ∀ a b x, act (a + b) x = act a (act b x)) (hact0 : ∀ x, act 0 x = x)
    (hMinv : ∀ a x y, M (act a x) (act a y) = M x y) (x y : ι) :
    Submission.PTCert.fourierW act M S y x = Submission.PTCert.fourierW act M S x y := by
  simp only [Submission.PTCert.fourierW]
  apply Finset.sum_congr rfl
  intro a _
  have haa : act a (act a y) = y := by
    rw [← hact a a y, zmod2_add_self, hact0 y]
  have key : M x (act a y) = M y (act a x) := by
    have h1 : M (act a x) y = M x (act a y) := by
      have h := hMinv a x (act a y)
      rwa [haa] at h
    have h2 : M (act a x) y = M y (act a x) := by
      have h := congr_fun (congr_fun hMsym (act a x)) y
      simp only [Matrix.transpose_apply] at h
      exact h.symm
    exact h1.symm.trans h2
  rw [key]

end Work.PTCert.Klein
