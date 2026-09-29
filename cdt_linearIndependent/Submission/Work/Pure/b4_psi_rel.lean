import Mathlib
import Submission.Work.Pure.b4_theta_defs

/-!
# The first-order relations satisfied by `Ψ = Li₂(x) - Li₂(φ(x))`

Calegari--Dimitrov--Tang, arXiv:2408.15403, §`sec:lindep`.  With `φ = x/(x-1) = sympPhi`,
`L = b4L = log(1-x)`, `Ψ = b4Psi = Li₂(x) - Li₂(φ(x))` and `b4Theta = (x-φ)·Ψ = sympW·Ψ`,
this module proves the two "cleared" identities

* `X·(X-1)·Ψ' = b4L·(2-X)`,
* `(X-1)·sympW·Ψ' = (4-sympY)·b4L`,

which are what the `Θ`-bridge needs.  Everything is proved by the chain rule
`PowerSeries.derivative_subst` together with `X·b4Li₂' = -b4L` (`b4Li2_deriv`),
`b4L∘φ = -b4L` (`b4L_subst_sympPhi`), `φ·(X-1) = X` (`sympPhi_mul_sub_one`),
`(X-1)²·φ' = -1` (from `derivative_sympPhi`), and `sympW·(2-X) = X·(4-sympY)`
(`sympW_mul_two_sub_X`); no division is needed.
-/

namespace Work.Pure

open PowerSeries

noncomputable section

lemma subst_neg_sympPhi (f : PowerSeries ℚ) :
    PowerSeries.subst Submission.CDT.sympPhi (-f)
      = -PowerSeries.subst Submission.CDT.sympPhi f := by
  rw [← PowerSeries.coe_substAlgHom Submission.CDT.sympPhi_hasSubst]
  exact map_neg _ f

lemma subst_zero_sympPhi :
    PowerSeries.subst Submission.CDT.sympPhi (0 : PowerSeries ℚ) = 0 := by
  rw [← PowerSeries.coe_substAlgHom Submission.CDT.sympPhi_hasSubst]
  exact map_zero _

/-- the chain rule, in the form used below -/
lemma b4Psi_deriv : (PowerSeries.derivative (R := ℚ)) b4Psi
    = (PowerSeries.derivative (R := ℚ)) b4Li2
      - PowerSeries.subst Submission.CDT.sympPhi ((PowerSeries.derivative (R := ℚ)) b4Li2)
        * (PowerSeries.derivative (R := ℚ)) Submission.CDT.sympPhi := by
  rw [b4Psi, map_sub, PowerSeries.derivative_subst Submission.CDT.sympPhi_hasSubst]

/-- `φ·(b4Li₂'∘φ) = b4L`, obtained by substituting `X·b4Li₂' = -b4L` along `φ`. -/
lemma sympPhi_mul_subst_dLi :
    Submission.CDT.sympPhi
        * PowerSeries.subst Submission.CDT.sympPhi ((PowerSeries.derivative (R := ℚ)) b4Li2)
      = b4L := by
  have hφ := Submission.CDT.sympPhi_hasSubst
  have h : (X : PowerSeries ℚ) * (PowerSeries.derivative (R := ℚ)) b4Li2 + b4L = 0 := by
    rw [b4Li2_deriv]; ring
  have h2 := congrArg (PowerSeries.subst Submission.CDT.sympPhi) h
  rw [PowerSeries.subst_add hφ, PowerSeries.subst_mul hφ, PowerSeries.subst_X hφ,
      b4L_subst_sympPhi, subst_zero_sympPhi] at h2
  simpa using (neg_eq_of_add_eq_zero_left h2).symm

/-- `X·(b4Li₂'∘φ) = (X-1)·b4L` -/
lemma X_mul_subst_dLi :
    (X : PowerSeries ℚ)
        * PowerSeries.subst Submission.CDT.sympPhi ((PowerSeries.derivative (R := ℚ)) b4Li2)
      = ((X : PowerSeries ℚ) - 1) * b4L := by
  calc (X : PowerSeries ℚ)
        * PowerSeries.subst Submission.CDT.sympPhi ((PowerSeries.derivative (R := ℚ)) b4Li2)
      = (Submission.CDT.sympPhi * ((X : PowerSeries ℚ) - 1))
          * PowerSeries.subst Submission.CDT.sympPhi ((PowerSeries.derivative (R := ℚ)) b4Li2) := by
          rw [Submission.CDT.sympPhi_mul_sub_one]
    _ = ((X : PowerSeries ℚ) - 1)
          * (Submission.CDT.sympPhi
              * PowerSeries.subst Submission.CDT.sympPhi ((PowerSeries.derivative (R := ℚ)) b4Li2)) := by
          ring
    _ = ((X : PowerSeries ℚ) - 1) * b4L := by rw [sympPhi_mul_subst_dLi]

/-- `(X-1)²·φ' = -1` -/
lemma XsubOne_sq_mul_deriv_sympPhi :
    ((X : PowerSeries ℚ) - 1) ^ 2 * (PowerSeries.derivative (R := ℚ)) Submission.CDT.sympPhi = -1 := by
  rw [derivative_sympPhi]
  linear_combination (-(((X : PowerSeries ℚ) - 1) * b4Unit + 1)) * mul_b4Unit

/-- **first relation**: `X(X-1)·Ψ' = b4L·(2-X)`. -/
lemma b4Psi_rel_one :
    PowerSeries.X * ((X : PowerSeries ℚ) - 1) * (PowerSeries.derivative (R := ℚ)) b4Psi
      = b4L * (2 - PowerSeries.X) := by
  have hB : PowerSeries.X * ((X : PowerSeries ℚ) - 1) * (PowerSeries.derivative (R := ℚ)) b4Li2
      = -(((X : PowerSeries ℚ) - 1) * b4L) := by
    have h := b4Li2_deriv
    calc PowerSeries.X * ((X : PowerSeries ℚ) - 1) * (PowerSeries.derivative (R := ℚ)) b4Li2
        = ((X : PowerSeries ℚ) - 1)
            * (PowerSeries.X * (PowerSeries.derivative (R := ℚ)) b4Li2) := by ring
      _ = ((X : PowerSeries ℚ) - 1) * (-b4L) := by rw [h]
      _ = -(((X : PowerSeries ℚ) - 1) * b4L) := by ring
  have hD : PowerSeries.X * ((X : PowerSeries ℚ) - 1)
      * (PowerSeries.subst Submission.CDT.sympPhi ((PowerSeries.derivative (R := ℚ)) b4Li2)
          * (PowerSeries.derivative (R := ℚ)) Submission.CDT.sympPhi) = -b4L := by
    calc PowerSeries.X * ((X : PowerSeries ℚ) - 1)
          * (PowerSeries.subst Submission.CDT.sympPhi ((PowerSeries.derivative (R := ℚ)) b4Li2)
              * (PowerSeries.derivative (R := ℚ)) Submission.CDT.sympPhi)
        = (PowerSeries.X
              * PowerSeries.subst Submission.CDT.sympPhi ((PowerSeries.derivative (R := ℚ)) b4Li2))
            * (((X : PowerSeries ℚ) - 1) * (PowerSeries.derivative (R := ℚ)) Submission.CDT.sympPhi) := by
            ring
      _ = (((X : PowerSeries ℚ) - 1) * b4L)
            * (((X : PowerSeries ℚ) - 1) * (PowerSeries.derivative (R := ℚ)) Submission.CDT.sympPhi) := by
            rw [X_mul_subst_dLi]
      _ = b4L * (((X : PowerSeries ℚ) - 1) ^ 2
            * (PowerSeries.derivative (R := ℚ)) Submission.CDT.sympPhi) := by ring
      _ = b4L * (-1) := by rw [XsubOne_sq_mul_deriv_sympPhi]
      _ = -b4L := by ring
  rw [b4Psi_deriv]
  linear_combination hB - hD

/-- **second relation**: `(X-1)·sympW·Ψ' = (4-sympY)·b4L`. -/
lemma b4Psi_rel_two :
    ((X : PowerSeries ℚ) - 1) * Submission.CDT.sympW * (PowerSeries.derivative (R := ℚ)) b4Psi
      = (4 - Submission.CDT.sympY) * b4L := by
  have h1 := b4Psi_rel_one
  have key : PowerSeries.X
      * (((X : PowerSeries ℚ) - 1) * Submission.CDT.sympW * (PowerSeries.derivative (R := ℚ)) b4Psi
          - (4 - Submission.CDT.sympY) * b4L) = 0 := by
    rw [show PowerSeries.X
          * (((X : PowerSeries ℚ) - 1) * Submission.CDT.sympW
              * (PowerSeries.derivative (R := ℚ)) b4Psi - (4 - Submission.CDT.sympY) * b4L)
        = Submission.CDT.sympW
            * (PowerSeries.X * ((X : PowerSeries ℚ) - 1)
                * (PowerSeries.derivative (R := ℚ)) b4Psi)
          - PowerSeries.X * ((4 - Submission.CDT.sympY) * b4L) by ring]
    rw [h1]
    rw [show Submission.CDT.sympW * (b4L * (2 - PowerSeries.X))
          = (Submission.CDT.sympW * (2 - PowerSeries.X)) * b4L by ring]
    rw [sympW_mul_two_sub_X]
    ring
  exact sub_eq_zero.mp ((mul_eq_zero.mp key).resolve_left PowerSeries.X_ne_zero)

/-- The two first-order relations of `Ψ`, in cleared form. -/
theorem b4_psi_rel :
    (PowerSeries.X * ((X : PowerSeries ℚ) - 1) * PowerSeries.derivative (R := ℚ) b4Psi
        = b4L * (2 - PowerSeries.X)) ∧
    (((X : PowerSeries ℚ) - 1) * Submission.CDT.sympW * PowerSeries.derivative (R := ℚ) b4Psi
        = (4 - Submission.CDT.sympY) * b4L) :=
  ⟨b4Psi_rel_one, b4Psi_rel_two⟩

end

end Work.Pure
