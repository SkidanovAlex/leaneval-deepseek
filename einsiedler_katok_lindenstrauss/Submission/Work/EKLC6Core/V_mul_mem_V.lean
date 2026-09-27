import Mathlib
import Submission.Work.EKLContract.Defs

/-!
# `Work.EKLC6Core.V_mul_mem_V`

The displacement neighbourhoods `V δ = {g : SL₃(ℝ) | |g i j - 1 i j| < δ ∀ i j}` form a
neighbourhood basis of the identity: for every `a ∈ V R` there is `δ > 0` with `V δ · a ⊆ V R`.

The proof is an explicit entrywise estimate.  Write
`(v · a) i j = a i j + ∑_k (v i k - 1 i k) a k j`.  Since `a ∈ V R`, every entry of `a` is bounded
by `1 + R`, while `|a i j - 1 i j|` is bounded by the maximum `M` of the nine deviations, and
`M < R`.  Taking `δ = (R - M) / (10 (1 + R))` gives
`|(v·a) i j - 1 i j| ≤ M + 3 δ (1 + R) = M + 3(R-M)/10 < R` for every `v ∈ V δ`.
-/

namespace Work.EKLC6Core

open Work.EKLContract

theorem V_mul_mem_V {R : ℝ} (hR : 0 < R) {a : Work.EKLContract.SL3}
    (ha : a ∈ Work.EKLContract.V R) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ v : Work.EKLContract.SL3,
      v ∈ Work.EKLContract.V δ → v * a ∈ Work.EKLContract.V R := by
  classical
  -- Every entry of `a` is bounded by `1 + R`.
  have ha_bd : ∀ i j : Fin 3, |(a : Matrix (Fin 3) (Fin 3) ℝ) i j| ≤ 1 + R := by
    intro i j
    have h1 : |(1 : Matrix (Fin 3) (Fin 3) ℝ) i j| ≤ 1 := by
      rw [Matrix.one_apply]; split <;> simp
    calc |(a : Matrix (Fin 3) (Fin 3) ℝ) i j|
        = |((a : Matrix (Fin 3) (Fin 3) ℝ) i j - (1 : Matrix (Fin 3) (Fin 3) ℝ) i j)
            + (1 : Matrix (Fin 3) (Fin 3) ℝ) i j| := by ring_nf
      _ ≤ |(a : Matrix (Fin 3) (Fin 3) ℝ) i j - (1 : Matrix (Fin 3) (Fin 3) ℝ) i j|
            + |(1 : Matrix (Fin 3) (Fin 3) ℝ) i j| := abs_add_le _ _
      _ ≤ R + 1 := add_le_add (le_of_lt (ha i j)) h1
      _ = 1 + R := by ring
  -- `M` = maximum over all entries of the deviation from the identity; `M < R`.
  set M : ℝ := (Finset.univ : Finset (Fin 3 × Fin 3)).sup'
      (Finset.univ_nonempty (α := Fin 3 × Fin 3))
      (fun p : Fin 3 × Fin 3 => |(a : Matrix (Fin 3) (Fin 3) ℝ) p.1 p.2
        - (1 : Matrix (Fin 3) (Fin 3) ℝ) p.1 p.2|) with hM
  have hMlt : M < R := by
    rw [hM, Finset.sup'_lt_iff]
    intro p _
    exact ha p.1 p.2
  have hMge : ∀ i j : Fin 3,
      |(a : Matrix (Fin 3) (Fin 3) ℝ) i j - (1 : Matrix (Fin 3) (Fin 3) ℝ) i j| ≤ M := by
    intro i j
    rw [hM]
    exact Finset.le_sup' (f := fun p : Fin 3 × Fin 3 => |(a : Matrix (Fin 3) (Fin 3) ℝ) p.1 p.2
        - (1 : Matrix (Fin 3) (Fin 3) ℝ) p.1 p.2|) (Finset.mem_univ (i, j))
  set δ : ℝ := (R - M) / (10 * (1 + R)) with hδ
  have hδpos : 0 < δ := by
    rw [hδ]; exact div_pos (by linarith) (by linarith)
  refine ⟨δ, hδpos, ?_⟩
  intro v hv i j
  -- arithmetic identity `δ * (3 (1+R)) = 3 (R-M)/10`
  have hkey : δ * (3 * (1 + R)) = 3 * (R - M) / 10 := by
    rw [hδ]
    have hne : (10 * (1 + R)) ≠ 0 := by positivity
    field_simp
  -- split the entry of `v * a`
  have hdecomp : ((v : Matrix (Fin 3) (Fin 3) ℝ) * (a : Matrix (Fin 3) (Fin 3) ℝ)) i j
      - (1 : Matrix (Fin 3) (Fin 3) ℝ) i j
      = (∑ k : Fin 3, ((v : Matrix (Fin 3) (Fin 3) ℝ) i k
            - (1 : Matrix (Fin 3) (Fin 3) ℝ) i k) * (a : Matrix (Fin 3) (Fin 3) ℝ) k j)
        + ((a : Matrix (Fin 3) (Fin 3) ℝ) i j - (1 : Matrix (Fin 3) (Fin 3) ℝ) i j) := by
    have hstep : ((v : Matrix (Fin 3) (Fin 3) ℝ) * (a : Matrix (Fin 3) (Fin 3) ℝ)) i j
        - (a : Matrix (Fin 3) (Fin 3) ℝ) i j
        = ∑ k : Fin 3, ((v : Matrix (Fin 3) (Fin 3) ℝ) i k
            - (1 : Matrix (Fin 3) (Fin 3) ℝ) i k) * (a : Matrix (Fin 3) (Fin 3) ℝ) k j := by
      rw [Matrix.mul_apply]
      have hone : (∑ k : Fin 3, (1 : Matrix (Fin 3) (Fin 3) ℝ) i k
            * (a : Matrix (Fin 3) (Fin 3) ℝ) k j)
          = (a : Matrix (Fin 3) (Fin 3) ℝ) i j := by
        rw [← Matrix.mul_apply, Matrix.one_mul]
      rw [← hone, ← Finset.sum_sub_distrib]
      exact Finset.sum_congr rfl (fun k _ => by ring)
    linarith
  -- the correction term is bounded by `δ * 3 * (1 + R)`
  have hsum : |∑ k : Fin 3, ((v : Matrix (Fin 3) (Fin 3) ℝ) i k
        - (1 : Matrix (Fin 3) (Fin 3) ℝ) i k) * (a : Matrix (Fin 3) (Fin 3) ℝ) k j|
      ≤ δ * (3 * (1 + R)) := by
    calc |∑ k : Fin 3, ((v : Matrix (Fin 3) (Fin 3) ℝ) i k
            - (1 : Matrix (Fin 3) (Fin 3) ℝ) i k) * (a : Matrix (Fin 3) (Fin 3) ℝ) k j|
        ≤ ∑ k : Fin 3, |((v : Matrix (Fin 3) (Fin 3) ℝ) i k
            - (1 : Matrix (Fin 3) (Fin 3) ℝ) i k) * (a : Matrix (Fin 3) (Fin 3) ℝ) k j| :=
          Finset.abs_sum_le_sum_abs _ _
      _ = ∑ k : Fin 3, |(v : Matrix (Fin 3) (Fin 3) ℝ) i k
            - (1 : Matrix (Fin 3) (Fin 3) ℝ) i k| * |(a : Matrix (Fin 3) (Fin 3) ℝ) k j| := by
          simp [abs_mul]
      _ ≤ ∑ k : Fin 3, δ * (1 + R) := by
          refine Finset.sum_le_sum (fun k _ => ?_)
          exact mul_le_mul (le_of_lt (hv i k)) (ha_bd k j) (abs_nonneg _) (le_of_lt hδpos)
      _ = δ * (3 * (1 + R)) := by
          rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
          ring
  have hbound : |(∑ k : Fin 3, ((v : Matrix (Fin 3) (Fin 3) ℝ) i k
        - (1 : Matrix (Fin 3) (Fin 3) ℝ) i k) * (a : Matrix (Fin 3) (Fin 3) ℝ) k j)
      + ((a : Matrix (Fin 3) (Fin 3) ℝ) i j - (1 : Matrix (Fin 3) (Fin 3) ℝ) i j)|
      < R := by
    have h1 : |(∑ k : Fin 3, ((v : Matrix (Fin 3) (Fin 3) ℝ) i k
          - (1 : Matrix (Fin 3) (Fin 3) ℝ) i k) * (a : Matrix (Fin 3) (Fin 3) ℝ) k j)
        + ((a : Matrix (Fin 3) (Fin 3) ℝ) i j - (1 : Matrix (Fin 3) (Fin 3) ℝ) i j)|
        ≤ M + δ * (3 * (1 + R)) := by
      have habs : |(∑ k : Fin 3, ((v : Matrix (Fin 3) (Fin 3) ℝ) i k
            - (1 : Matrix (Fin 3) (Fin 3) ℝ) i k) * (a : Matrix (Fin 3) (Fin 3) ℝ) k j)
          + ((a : Matrix (Fin 3) (Fin 3) ℝ) i j - (1 : Matrix (Fin 3) (Fin 3) ℝ) i j)|
          ≤ |(∑ k : Fin 3, ((v : Matrix (Fin 3) (Fin 3) ℝ) i k
              - (1 : Matrix (Fin 3) (Fin 3) ℝ) i k) * (a : Matrix (Fin 3) (Fin 3) ℝ) k j)|
            + |(a : Matrix (Fin 3) (Fin 3) ℝ) i j - (1 : Matrix (Fin 3) (Fin 3) ℝ) i j| :=
          abs_add_le _ _
      linarith [habs, hsum, hMge i j]
    rw [hkey] at h1
    nlinarith [hMlt]
  have hcoe : ((v * a : Work.EKLContract.SL3) : Matrix (Fin 3) (Fin 3) ℝ) i j
      = ((v : Matrix (Fin 3) (Fin 3) ℝ) * (a : Matrix (Fin 3) (Fin 3) ℝ)) i j := by
    rw [Matrix.SpecialLinearGroup.coe_mul]
  rw [hcoe, hdecomp]
  exact hbound

end Work.EKLC6Core
