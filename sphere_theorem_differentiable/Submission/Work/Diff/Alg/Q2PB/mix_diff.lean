import Mathlib
import Submission.Work.Diff.Alg.q2p_defs
import Submission.Work.Diff.Alg.Q2PB.Defs

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

/-!
# The mixed second difference of the quartic form `R4 R u v u v`

`Work.Diff.Alg.Q2PB.mixDiff R a b c d` is the alternating sum of `R4 R (a ± b) (c ± d) (a ± b) (c ± d)`
over the four sign choices.  Since `(u, v) ↦ R4 R u v u v` is a quadratic (hence polarizable) form in
each variable separately, this mixed second difference equals `8 * (R4 R a c b d + R4 R a d b c)`,
as used in Berger's inequality (`Work.Diff.Alg.q2p_berger`).
-/

namespace Work.Diff.Alg.Q2PB

open Submission.Diff.Alg Work.Diff.Alg.Q2P

variable {n : ℕ}

/-! ## Negation / subtraction in the four slots of `R4` -/

theorem R4_neg₂ (R : Curv4 n) (a b c d : Fin n → ℝ) : R4 R a (-b) c d = - R4 R a b c d := by
  have h := R4_smul₂ R (-1) a b c d
  rw [show ((-1 : ℝ) • b) = -b from by ext i; simp] at h
  simpa using h

theorem R4_neg₃ (R : Curv4 n) (a b c d : Fin n → ℝ) : R4 R a b (-c) d = - R4 R a b c d := by
  have h := R4_smul₃ R (-1) a b c d
  rw [show ((-1 : ℝ) • c) = -c from by ext i; simp] at h
  simpa using h

theorem R4_neg₄ (R : Curv4 n) (a b c d : Fin n → ℝ) : R4 R a b c (-d) = - R4 R a b c d := by
  have h := R4_smul₄ R (-1) a b c d
  rw [show ((-1 : ℝ) • d) = -d from by ext i; simp] at h
  simpa using h

theorem R4_sub₁ (R : Curv4 n) (a a' b c d : Fin n → ℝ) :
    R4 R (a - a') b c d = R4 R a b c d - R4 R a' b c d := by
  rw [sub_eq_add_neg, R4_add₁, R4_neg₁]; ring

theorem R4_sub₂ (R : Curv4 n) (a b b' c d : Fin n → ℝ) :
    R4 R a (b - b') c d = R4 R a b c d - R4 R a b' c d := by
  rw [sub_eq_add_neg, R4_add₂, R4_neg₂]; ring

theorem R4_sub₃ (R : Curv4 n) (a b c c' d : Fin n → ℝ) :
    R4 R a b (c - c') d = R4 R a b c d - R4 R a b c' d := by
  rw [sub_eq_add_neg, R4_add₃, R4_neg₃]; ring

theorem R4_sub₄ (R : Curv4 n) (a b c d d' : Fin n → ℝ) :
    R4 R a b c (d - d') = R4 R a b c d - R4 R a b c d' := by
  rw [sub_eq_add_neg, R4_add₄, R4_neg₄]; ring

/-! ## The two polarized differences -/

/-- Second difference of `v ↦ R4 R u v u v` in the second variable: the polar form is
`4 * R4 R u v u w`. -/
theorem R4_secondDiff₂ (R : Curv4 n) (hR : IsAlgCurv R) (u v w : Fin n → ℝ) :
    R4 R u (v + w) u (v + w) - R4 R u (v - w) u (v - w) = 4 * R4 R u v u w := by
  have hsym : R4 R u w u v = R4 R u v u w := R4_pair_symm R hR u v u w
  simp only [R4_add₂, R4_add₄, R4_sub₂, R4_sub₄, hsym]
  ring

/-- Second difference of the polar form `u ↦ R4 R u c u d` in the first variable. -/
theorem R4_secondDiff₁ (R : Curv4 n) (hR : IsAlgCurv R) (a b c d : Fin n → ℝ) :
    R4 R (a + b) c (a + b) d - R4 R (a - b) c (a - b) d
      = 2 * R4 R a c b d + 2 * R4 R a d b c := by
  have hsym : R4 R b c a d = R4 R a d b c := R4_pair_symm R hR a d b c
  simp only [R4_add₁, R4_add₃, R4_sub₁, R4_sub₃, hsym]
  ring

/-- The mixed second difference of `R4 R u v u v`. -/
theorem mix_diff {n : ℕ} (R : Submission.Diff.Alg.Curv4 n) (hR : Submission.Diff.Alg.IsAlgCurv R)
    (a b c d : Fin n → ℝ) :
    Work.Diff.Alg.Q2PB.mixDiff R a b c d
      = 8 * (Submission.Diff.Alg.R4 R a c b d + Submission.Diff.Alg.R4 R a d b c) := by
  calc Work.Diff.Alg.Q2PB.mixDiff R a b c d
      = (R4 R (a + b) (c + d) (a + b) (c + d) - R4 R (a + b) (c - d) (a + b) (c - d))
        - (R4 R (a - b) (c + d) (a - b) (c + d)
            - R4 R (a - b) (c - d) (a - b) (c - d)) := by
          simp only [mixDiff]; ring
    _ = 4 * R4 R (a + b) c (a + b) d - 4 * R4 R (a - b) c (a - b) d := by
          rw [R4_secondDiff₂ R hR (a + b) c d, R4_secondDiff₂ R hR (a - b) c d]
    _ = 4 * (R4 R (a + b) c (a + b) d - R4 R (a - b) c (a - b) d) := by ring
    _ = 4 * (2 * R4 R a c b d + 2 * R4 R a d b c) := by rw [R4_secondDiff₁ R hR a b c d]
    _ = 8 * (R4 R a c b d + R4 R a d b c) := by ring

end Work.Diff.Alg.Q2PB
