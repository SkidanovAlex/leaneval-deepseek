/-
Copyright: none.  Part of the `Newlander-Nirenberg` formalisation project.

# Difference (Lipschitz) estimates for the flat solvers

The contraction of the fixed-point argument needs the solvers to be *Lipschitz* with the constants
of their estimates.  Since `T1` and `T2` are required to be *linear* in the interface, this is
immediate from the `k = 0` estimates of `FlatOne`/`FlatTwo` together with the linearity of the
interface and the subtraction lemmas of `Proj.lean`.
-/
import Mathlib
import Submission.Work.NN.Final.Proj

noncomputable section

open scoped NNReal ENNReal ContDiff
open Set

namespace Work.NN.Final

open Work.CR.Flat

variable {n : ℕ}

/-- **The difference estimate for `T1`.**  Linearity of `T1` plus the `k = 0` estimate. -/
lemma T1_diff {ρ : Fin n → ℝ} {α : ℝ} (F : FlatOne n α ρ)
    {f f' : Fin n → (Fin n → ℂ) → ℂ}
    (hf : ∀ j, ContDiffOn ℝ 1 (f j) (pd n ρ 4))
    (hf' : ∀ j, ContDiffOn ℝ 1 (f' j) (pd n ρ 4))
    (hcl : Clos1 n ρ 4 f) (hcl' : Clos1 n ρ 4 f') :
    holderNorm 1 α (F.T1 f - F.T1 f') (pd n ρ 2)
      ≤ ENNReal.ofReal (F.C1 0) * ∑ j, holderNorm 0 α (f j - f' j) (pd n ρ 4) := by
  have hsub : F.T1 f - F.T1 f' = F.T1 (f - f') := by
    rw [← map_sub]
  rw [hsub]
  exact F.T1_est 0 (f - f') (fun j => (hf j).sub (hf' j))
    (Clos1_sub hcl hcl' (fun j => (hf j)) (fun j => (hf' j)))

/-- **The difference estimate for `T2`.** -/
lemma T2_diff {ρ : Fin n → ℝ} {α : ℝ} (F : FlatTwo n α ρ)
    {f f' : Fin n → Fin n → (Fin n → ℂ) → ℂ}
    (hf : ∀ j l, ContDiffOn ℝ 1 (f j l) (pd n ρ 4))
    (hf' : ∀ j l, ContDiffOn ℝ 1 (f' j l) (pd n ρ 4))
    (hanti : ∀ j l : Fin n, ∀ z : Fin n → ℂ, f j l z = - f l j z)
    (hanti' : ∀ j l : Fin n, ∀ z : Fin n → ℂ, f' j l z = - f' l j z)
    (hcl : Clos2 n ρ 4 f) (hcl' : Clos2 n ρ 4 f') :
    ∀ j, holderNorm 1 α ((F.T2 f) j - (F.T2 f') j) (pd n ρ 2)
      ≤ ENNReal.ofReal (F.C2 0) * ∑ j, ∑ l, holderNorm 0 α (f j l - f' j l) (pd n ρ 4) := by
  intro j
  have hsub : (F.T2 f) j - (F.T2 f') j = (F.T2 (f - f')) j :=
    (congrFun (map_sub F.T2 f f') j).symm
  rw [hsub]
  refine F.T2_est 0 (f - f') (fun j l => (hf j l).sub (hf' j l)) ?_ ?_ j
  · intro j l z
    simp only [Pi.sub_apply]
    rw [hanti j l z, hanti' l j z]
    ring
  · intro j l m z hz
    have hd : ∀ p q : Fin n, DifferentiableAt ℝ (f p q) z := fun p q =>
      ((hf p q).contDiffAt ((isOpen_pd ρ 4).mem_nhds hz)).differentiableAt (by simp)
    have hd' : ∀ p q : Fin n, DifferentiableAt ℝ (f' p q) z := fun p q =>
      ((hf' p q).contDiffAt ((isOpen_pd ρ 4).mem_nhds hz)).differentiableAt (by simp)
    simp only [Pi.sub_apply]
    have eta : ∀ a b : (Fin n → ℂ) → ℂ, (a - b) = fun y => a y - b y := fun a b => rfl
    rw [eta (f l m) (f' l m), eta (f j m) (f' j m), eta (f j l) (f' j l),
      dbarCoord_sub_diff (hd l m) (hd' l m) j, dbarCoord_sub_diff (hd j m) (hd' j m) l,
      dbarCoord_sub_diff (hd j l) (hd' j l) m]
    linear_combination (hcl j l m z hz) - (hcl' j l m z hz)

end Work.NN.Final
