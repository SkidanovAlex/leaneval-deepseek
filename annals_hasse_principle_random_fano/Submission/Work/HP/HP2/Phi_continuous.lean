import Mathlib
import Submission.Work.HP.Defs
import Submission.Work.HP.tau_basic
import Submission.Work.HP.HP2.veronese_sup

/-!
# Continuity of the archimedean `Φ`

For a form `f_a` of degree `d` in `n+1` variables and a parameter `α > 0`, the paper considers
the supremum over the Euclidean unit ball of the function
`x ↦ |4 α² f_a(x)² − ‖ν(x)‖²|`, where `ν = ν_{d,n}` is the Veronese map.

The set `{x | rNorm x ≤ 1}` is compact (the Euclidean unit ball of a finite-dimensional space),
`(p, x) ↦ |4 p.2² ⟨ν(x), p.1⟩² − ‖ν(x)‖²|` is continuous on the product, and the supremum over a
compact set of a jointly continuous function is continuous
(`IsCompact.continuous_sSup`).  This gives `Work.HP.HP2.Phi_continuous`.
-/

set_option autoImplicit false

noncomputable section

namespace Work.HP.HP2

open Finset

/-! ## Continuity of the building blocks -/

/-- The Veronese map `x ↦ (x^μ)_μ` is continuous. -/
theorem continuous_veronese (d n : ℕ) :
    Continuous (veronese d n : (Fin (n + 1) → ℝ) → (Mon d n → ℝ)) := by
  apply continuous_pi
  intro m
  simp only [veronese]
  exact continuous_finsetProd _ fun i _ => (continuous_apply i).pow _

/-- The real inner product `dotR` is continuous on the product of two vector spaces. -/
theorem continuous_dotR_pair {ι : Type*} [Fintype ι] :
    Continuous (fun p : (ι → ℝ) × (ι → ℝ) => dotR p.1 p.2) := by
  unfold dotR
  apply continuous_finsetSum
  intro i _
  exact ((continuous_apply i).comp continuous_fst).mul
    ((continuous_apply i).comp continuous_snd)

/-- The Euclidean norm `rNorm` is continuous (for the product topology on `ι → ℝ`). -/
theorem continuous_rNorm_pi {ι : Type*} [Fintype ι] :
    Continuous (fun w : ι → ℝ => rNorm w) := by
  unfold rNorm
  exact Real.continuous_sqrt.comp
    (continuous_finsetSum _ fun i _ => (continuous_apply i).pow 2)

/-! ## Compactness of the Euclidean unit ball -/

/-- The closed Euclidean unit ball `{x : Fin (n+1) → ℝ | rNorm x ≤ 1}` is compact. -/
theorem isCompact_rNorm_le_one (n : ℕ) :
    IsCompact {x : Fin (n + 1) → ℝ | rNorm x ≤ 1} := by
  refine (isCompact_closedBall (0 : Fin (n + 1) → ℝ) (1 : ℝ)).of_isClosed_subset ?_ ?_
  · exact isClosed_le (continuous_rNorm_pi (ι := Fin (n + 1))) continuous_const
  · intro x hx
    simp only [Metric.mem_closedBall, dist_eq_norm, sub_zero]
    exact le_trans (norm_le_rNorm x) hx

/-! ## The main statement -/

theorem Phi_continuous (d n : ℕ) :
    Continuous (fun p : (Mon d n → ℝ) × ℝ =>
      sSup ((fun x : Fin (n + 1) → ℝ =>
        |4 * p.2 ^ 2 * (dotR (veronese d n x) p.1) ^ 2 -
          (rNorm (veronese d n x)) ^ 2|) '' {x : Fin (n + 1) → ℝ | rNorm x ≤ 1})) := by
  have hver : Continuous (veronese d n : (Fin (n + 1) → ℝ) → (Mon d n → ℝ)) :=
    continuous_veronese d n
  have hdot : Continuous (fun q : ((Mon d n → ℝ) × ℝ) × (Fin (n + 1) → ℝ) =>
      dotR (veronese d n q.2) q.1.1) :=
    continuous_dotR_pair.comp ((hver.comp continuous_snd).prodMk continuous_fst.fst)
  have hrn : Continuous (fun q : ((Mon d n → ℝ) × ℝ) × (Fin (n + 1) → ℝ) =>
      rNorm (veronese d n q.2)) :=
    continuous_rNorm_pi.comp (hver.comp continuous_snd)
  have hα : Continuous (fun q : ((Mon d n → ℝ) × ℝ) × (Fin (n + 1) → ℝ) => q.1.2) :=
    continuous_fst.snd
  have hcont : Continuous (fun q : ((Mon d n → ℝ) × ℝ) × (Fin (n + 1) → ℝ) =>
      |4 * q.1.2 ^ 2 * (dotR (veronese d n q.2) q.1.1) ^ 2 -
        (rNorm (veronese d n q.2)) ^ 2|) :=
    Continuous.abs (Continuous.sub
      (Continuous.mul (continuous_const.mul (hα.pow 2)) (hdot.pow 2))
      (hrn.pow 2))
  exact IsCompact.continuous_sSup
    (f := fun p : (Mon d n → ℝ) × ℝ => fun x : Fin (n + 1) → ℝ =>
      |4 * p.2 ^ 2 * (dotR (veronese d n x) p.1) ^ 2 - (rNorm (veronese d n x)) ^ 2|)
    (K := {x : Fin (n + 1) → ℝ | rNorm x ≤ 1})
    (isCompact_rNorm_le_one n) hcont

end Work.HP.HP2
