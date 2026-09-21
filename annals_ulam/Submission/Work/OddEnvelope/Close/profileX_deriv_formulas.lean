import Mathlib
import Submission.Work.OddEnvelope.Defs

namespace Work.OddEnvelope.Close

open Work.OddEnvelope

noncomputable section

/-- The semicircle chord-endpoint function `profileX` written with `Real.rpow`,
`gp s = (1 + s²)^(-1/2)`.  All the differential identities are proved for `gp` and then
transported back along `profileX = gp`. -/
private def gp (s : ℝ) : ℝ := (1 + s ^ 2) ^ (-(1 / 2 : ℝ))

private lemma profileX_eq_gp : profileX = gp := by
  funext s
  show 1 / Real.sqrt (1 + s ^ 2) = (1 + s ^ 2) ^ (-(1 / 2 : ℝ))
  rw [Real.rpow_neg (show (0 : ℝ) ≤ 1 + s ^ 2 by positivity) (1 / 2)]
  rw [← Real.sqrt_eq_rpow]
  rw [one_div]

/-- The basic relation `gp s ^ n = (1 + s²)^(-n/2)`, by induction using `Real.rpow_add`. -/
private lemma gp_pow (s : ℝ) (n : ℕ) : gp s ^ n = (1 + s ^ 2) ^ (-((n : ℝ) / 2)) := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [pow_succ, ih]
    show (1 + s ^ 2) ^ (-((n : ℝ) / 2)) * (1 + s ^ 2) ^ (-(1 / 2 : ℝ)) =
      (1 + s ^ 2) ^ (-(((n + 1 : ℕ) : ℝ) / 2))
    rw [← Real.rpow_add (show (0 : ℝ) < 1 + s ^ 2 by positivity)]
    congr 1
    push_cast
    ring

private lemma gp_sq (s : ℝ) : gp s ^ 2 = (1 + s ^ 2)⁻¹ := by
  rw [gp_pow s 2, show -(((2 : ℕ) : ℝ) / 2) = -1 by norm_num, Real.rpow_neg_one]

private lemma gp_pow3 (s : ℝ) : gp s ^ 3 = (1 + s ^ 2) ^ (-(3 / 2 : ℝ)) := by
  rw [gp_pow s 3, show -(((3 : ℕ) : ℝ) / 2) = -(3 / 2) by norm_num]

private lemma gp_pow5 (s : ℝ) : gp s ^ 5 = (1 + s ^ 2) ^ (-(5 / 2 : ℝ)) := by
  rw [gp_pow s 5, show -(((5 : ℕ) : ℝ) / 2) = -(5 / 2) by norm_num]

/-- First derivative of `gp`. -/
private lemma hasDerivAt_gp (s : ℝ) : HasDerivAt gp (-s * gp s ^ 3) s := by
  have hinner : HasDerivAt (fun t : ℝ => 1 + t ^ 2) (2 * s) s := by
    simpa using ((hasDerivAt_id (s : ℝ)).pow 2).const_add 1
  have houter : HasDerivAt (fun x : ℝ => x ^ (-(1 / 2 : ℝ)))
      ((-(1 / 2 : ℝ)) * (1 + s ^ 2) ^ ((-(1 / 2 : ℝ)) - 1)) (1 + s ^ 2) :=
    Real.hasDerivAt_rpow_const (Or.inl (by positivity))
  have hcomp := houter.comp s hinner
  have key : (-s * gp s ^ 3) =
      ((-(1 / 2 : ℝ)) * (1 + s ^ 2) ^ ((-(1 / 2 : ℝ)) - 1)) * (2 * s) := by
    rw [gp_pow3, show ((-(1 / 2 : ℝ)) - 1) = (-(3 / 2 : ℝ)) by norm_num]
    ring
  rw [key]
  exact hcomp

private lemma deriv_gp_formula : deriv gp = fun s => -s * gp s ^ 3 :=
  deriv_eq (fun s => hasDerivAt_gp s)

/-- `deriv gp` in explicit `rpow` form. -/
private lemma deriv_gp_eq : deriv gp = fun s => -s * (1 + s ^ 2) ^ (-(3 / 2 : ℝ)) := by
  rw [deriv_gp_formula]
  funext s
  rw [gp_pow3]

private lemma rpow_3halves (s : ℝ) :
    (1 + s ^ 2) ^ (-(3 / 2 : ℝ)) = (1 + s ^ 2) ^ (-(5 / 2 : ℝ)) * (1 + s ^ 2) := by
  rw [show (-(3 / 2 : ℝ)) = -(5 / 2) + 1 by norm_num,
    Real.rpow_add (show (0 : ℝ) < 1 + s ^ 2 by positivity), Real.rpow_one]

/-- The derivative value produced by `HasDerivAt.mul` for `deriv gp`, rewritten. -/
private lemma deriv_deriv_val (s : ℝ) :
    (-1 * (1 + s ^ 2) ^ (-(3 / 2 : ℝ)) +
        (-s) * (((-(3 / 2 : ℝ)) * (1 + s ^ 2) ^ ((-(3 / 2 : ℝ)) - 1)) * (2 * s)))
      = (2 * s ^ 2 - 1) * gp s ^ 5 := by
  rw [show ((-(3 / 2 : ℝ)) - 1) = (-(5 / 2 : ℝ)) by norm_num, gp_pow5, rpow_3halves]
  ring

/-- Second derivative of `gp`. -/
private lemma hasDerivAt_deriv_gp (s : ℝ) :
    HasDerivAt (deriv gp) ((2 * s ^ 2 - 1) * gp s ^ 5) s := by
  rw [deriv_gp_eq]
  have hinner : HasDerivAt (fun t : ℝ => 1 + t ^ 2) (2 * s) s := by
    simpa using ((hasDerivAt_id (s : ℝ)).pow 2).const_add 1
  have houter : HasDerivAt (fun x : ℝ => x ^ (-(3 / 2 : ℝ)))
      ((-(3 / 2 : ℝ)) * (1 + s ^ 2) ^ ((-(3 / 2 : ℝ)) - 1)) (1 + s ^ 2) :=
    Real.hasDerivAt_rpow_const (Or.inl (by positivity))
  have hcomp : HasDerivAt (fun t : ℝ => (1 + t ^ 2) ^ (-(3 / 2 : ℝ)))
      (((-(3 / 2 : ℝ)) * (1 + s ^ 2) ^ ((-(3 / 2 : ℝ)) - 1)) * (2 * s)) s := by
    exact houter.comp s hinner
  have hneg : HasDerivAt (fun t : ℝ => -t) (-1) s := by
    exact (hasDerivAt_id (s : ℝ)).neg
  have hmul : HasDerivAt (fun t : ℝ => -t * (1 + t ^ 2) ^ (-(3 / 2 : ℝ)))
      ((-1) * (1 + s ^ 2) ^ (-(3 / 2 : ℝ)) +
        (-s) * (((-(3 / 2 : ℝ)) * (1 + s ^ 2) ^ ((-(3 / 2 : ℝ)) - 1)) * (2 * s))) s := by
    exact hneg.mul hcomp
  rw [← deriv_deriv_val s]
  exact hmul

theorem profileX_deriv_formulas (s : ℝ) :
    deriv Work.OddEnvelope.profileX s = -s * Work.OddEnvelope.profileX s ^ 3 ∧
    deriv (deriv Work.OddEnvelope.profileX) s =
      (2 * s ^ 2 - 1) * Work.OddEnvelope.profileX s ^ 5 ∧
    Work.OddEnvelope.profileX s + s * deriv Work.OddEnvelope.profileX s =
      Work.OddEnvelope.profileX s ^ 3 ∧
    2 * (deriv Work.OddEnvelope.profileX s) ^ 2 -
      Work.OddEnvelope.profileX s * deriv (deriv Work.OddEnvelope.profileX) s =
        Work.OddEnvelope.profileX s ^ 6 := by
  have hA : deriv profileX = fun s => -s * profileX s ^ 3 := by
    rw [profileX_eq_gp]
    exact deriv_gp_formula
  have hB : deriv (deriv profileX) = fun s => (2 * s ^ 2 - 1) * profileX s ^ 5 := by
    rw [profileX_eq_gp]
    exact deriv_eq (fun s => hasDerivAt_deriv_gp s)
  refine ⟨?_, ?_, ?_, ?_⟩
  · exact congrFun hA s
  · exact congrFun hB s
  · rw [show deriv profileX s = -s * profileX s ^ 3 from congrFun hA s]
    have hsq : profileX s ^ 2 * (1 + s ^ 2) = 1 := by
      rw [profileX_eq_gp, gp_sq]
      exact inv_mul_cancel₀ (by positivity : (1 : ℝ) + s ^ 2 ≠ 0)
    have h2 : s ^ 2 * profileX s ^ 2 + profileX s ^ 2 = 1 := by nlinarith [hsq]
    have hkey : profileX s + s * (-s * profileX s ^ 3) - profileX s ^ 3 = 0 := by
      have e : profileX s + s * (-s * profileX s ^ 3) - profileX s ^ 3 =
          profileX s * (1 - (s ^ 2 * profileX s ^ 2 + profileX s ^ 2)) := by ring
      rw [e, h2]; ring
    linarith
  · rw [show deriv profileX s = -s * profileX s ^ 3 from congrFun hA s,
        show deriv (deriv profileX) s = (2 * s ^ 2 - 1) * profileX s ^ 5 from congrFun hB s]
    ring

end

end Work.OddEnvelope.Close
