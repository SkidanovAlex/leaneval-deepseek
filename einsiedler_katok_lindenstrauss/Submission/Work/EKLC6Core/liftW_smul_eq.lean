import Mathlib
import Submission.Work.EKLC6Core.CellWDefs
import Submission.Work.EKLC6Core.margin_of_uncrossed

namespace Work.EKLC6Core

open Work.EKLContract

variable {μ : MeasureTheory.Measure X3} {U : Subgroup SL3}

/-- The canonical lift `liftW S k y` of a point of a cell is `v * S.g k` with `v ∈ V (S.δ k / 2)`
and `v • mkX (S.g k) = y`. -/
lemma liftW_spec (S : CellW μ U) {k : ℕ} {y : X3} (hy : y ∈ S.Q k) :
    ∃ v ∈ V (S.δ k / 2), liftW S k y = v * S.g k ∧ v • mkX (S.g k) = y := by
  classical
  have h := Classical.choose_spec (S.hsub k hy)
  exact ⟨Classical.choose (S.hsub k hy), h.1, by simp [liftW, dif_pos hy], h.2⟩

/-- **Local `U`-equivariance of the canonical lift.**  If `u ∈ V ε` with `ε ≤ 2 * S.δ k` and the
perturbed point `u • y` still lies in the same cell `S.Q k`, then the canonical lift of `u • y` is
`u` times the canonical lift of `y`. -/
theorem liftW_smul_eq {μ : MeasureTheory.Measure Work.EKLContract.X3}
    {U : Subgroup Work.EKLContract.SL3} (S : Work.EKLC6Core.CellW μ U)
    {k : ℕ} {y : Work.EKLContract.X3} (hy : y ∈ S.Q k) {u : Work.EKLContract.SL3} {ε : ℝ}
    (hu : u ∈ Work.EKLContract.V ε) (hε : ε ≤ 2 * S.δ k) (hyu : u • y ∈ S.Q k) :
    Work.EKLC6Core.liftW S k (u • y) = u * Work.EKLC6Core.liftW S k y := by
  obtain ⟨v, hv, hlift, hvk⟩ := liftW_spec S hy
  obtain ⟨v', hv', hlift', hv'k⟩ := liftW_spec S hyu
  have hδpos : 0 < S.δ k := S.hδpos k
  have hεpos : 0 < ε := lt_of_le_of_lt (abs_nonneg _) (hu ⟨0, by decide⟩ ⟨0, by decide⟩)
  have hbpos : 0 < S.δ k / 2 := by linarith
  have hw4 : u * v ∈ V (4 * S.δ k) := by
    intro z w
    have key := abs_mul_sub_one_lt (A := (u : Matrix (Fin 3) (Fin 3) ℝ))
      (B := (v : Matrix (Fin 3) (Fin 3) ℝ)) z w (sA := ε) (sB := S.δ k / 2)
      (fun p q => hu p q) (fun p q => hv p q) (le_of_lt hεpos) (le_of_lt hbpos)
    have hcoe : ((u * v : SL3) : Matrix (Fin 3) (Fin 3) ℝ)
        = (u : Matrix (Fin 3) (Fin 3) ℝ) * (v : Matrix (Fin 3) (Fin 3) ℝ) :=
      Matrix.SpecialLinearGroup.coe_mul u v
    have hδle : S.δ k ≤ 1 / 16 := S.hδsmall k
    have hbound : ε + S.δ k / 2 + 3 * ε * (S.δ k / 2) ≤ 4 * S.δ k := by nlinarith
    rw [hcoe]
    linarith
  have hsame : u * v = v' := by
    refine S.hinj k (u * v) v' hw4 (V_mono' (by linarith) hv') ?_
    calc (u * v) • mkX (S.g k) = u • (v • mkX (S.g k)) := by rw [mul_smul]
      _ = u • y := by rw [hvk]
      _ = v' • mkX (S.g k) := hv'k.symm
  rw [hlift', ← hsame, hlift]
  group

end Work.EKLC6Core
