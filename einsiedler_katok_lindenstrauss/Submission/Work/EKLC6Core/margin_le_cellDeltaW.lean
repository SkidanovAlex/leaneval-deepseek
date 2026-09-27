import Mathlib
import Submission.Work.EKLC6Core.CellWDefs
import Submission.Work.EKLC6Core.margin_of_uncrossed

namespace Work.EKLC6Core

open Work.EKLContract

/-- **If no `V ε`-perturbation moves `y ∈ S.Q k` out of its cell, then `ε ≤ 2 * S.δ k`.**

This is the `CellW` analogue of `margin_le_cellDelta`: the proof only uses the cells, their
radii, the containment `hsub` in the lifted half-ball and the injectivity `hinj`, which
`CellW` carries verbatim from `CellSys`. -/
theorem margin_le_cellDeltaW {μ : MeasureTheory.Measure Work.EKLContract.X3}
    {U : Subgroup Work.EKLContract.SL3} (S : Work.EKLC6Core.CellW μ U)
    {k : ℕ} {y : Work.EKLContract.X3} (hy : y ∈ S.Q k) {ε : ℝ}
    (h : ∀ v : Work.EKLContract.SL3, v ∈ Work.EKLContract.V ε → v • y ∈ S.Q k) :
    ε ≤ 2 * S.δ k := by
  by_contra hcon
  rw [not_le] at hcon
  obtain ⟨v, hv, hvy⟩ := S.hsub k hy
  have hvy : v • mkX (S.g k) = y := hvy
  have hδpos : 0 < S.δ k := S.hδpos k
  have hδ16 : S.δ k ≤ 1 / 16 := S.hδsmall k
  have hδ2 : (S.δ k) ^ 2 ≤ S.δ k / 16 := by nlinarith [hδpos, hδ16]
  have hεpos : 0 < ε := by linarith
  obtain ⟨i, j, hij⟩ : ∃ i j : Fin 3, i ≠ j := ⟨0, 1, by decide⟩
  set A : Matrix (Fin 3) (Fin 3) ℝ := (v : Matrix (Fin 3) (Fin 3) ℝ) - 1 with hAdef
  have hAb : ∀ p q : Fin 3, |A p q| < S.δ k / 2 := by
    intro p q
    have hpq := hv p q
    simpa [hAdef, Matrix.sub_apply] using hpq
  have hden_pos : 0 < 1 + A j j := by
    have h := abs_lt.mp (hAb j j)
    linarith [h.1, hδ16]
  have hnum : |S.δ k / 2 - A i j| < S.δ k := by
    have h := abs_lt.mp (hAb i j)
    rw [abs_lt]
    constructor <;> linarith [h.1, h.2, hδpos]
  set c : ℝ := (S.δ k / 2 - A i j) / (1 + A j j) with hcdef
  have hc_abs : |c| < 2 * S.δ k := by
    rw [hcdef, abs_div, abs_of_pos hden_pos, div_lt_iff₀ hden_pos]
    have h := abs_lt.mp (hAb j j)
    nlinarith [hnum, h.1, hδpos, hδ2]
  have hc_lt : |c| < ε := by linarith
  have huV : uij hij c ∈ V ε := uij_mem_V hij hc_lt hεpos
  have hmemQ : (uij hij c) • y ∈ S.Q k := h _ huV
  obtain ⟨v', hv', hv'eq⟩ := S.hsub k hmemQ
  have hcoe_uv : ((uij hij c * v : SL3) : Matrix (Fin 3) (Fin 3) ℝ)
      = (uij hij c : Matrix (Fin 3) (Fin 3) ℝ) * (v : Matrix (Fin 3) (Fin 3) ℝ) :=
    Matrix.SpecialLinearGroup.coe_mul _ _
  have huc : ∀ p q : Fin 3, |(uij hij c : Matrix (Fin 3) (Fin 3) ℝ) p q
      - (1 : Matrix (Fin 3) (Fin 3) ℝ) p q| < 2 * S.δ k := by
    intro p q
    exact uij_mem_V hij hc_abs (by linarith [hδpos]) p q
  have hw4 : uij hij c * v ∈ V (4 * S.δ k) := by
    intro z w
    have key := abs_mul_sub_one_lt (A := (uij hij c : Matrix (Fin 3) (Fin 3) ℝ))
      (B := (v : Matrix (Fin 3) (Fin 3) ℝ)) z w (sA := 2 * S.δ k) (sB := S.δ k / 2)
      (fun p q => huc p q) (fun p q => hv p q) (by linarith [hδpos]) (by linarith [hδpos])
    rw [hcoe_uv]
    have hb : 2 * S.δ k + S.δ k / 2 + 3 * (2 * S.δ k) * (S.δ k / 2) ≤ 4 * S.δ k := by
      nlinarith [hδpos, hδ2]
    linarith
  have hventry : (v : Matrix (Fin 3) (Fin 3) ℝ) i j = A i j := by
    rw [hAdef, Matrix.sub_apply, Matrix.one_apply_ne hij, sub_zero]
  have hvjentry : (v : Matrix (Fin 3) (Fin 3) ℝ) j j = A j j + 1 := by
    rw [hAdef, Matrix.sub_apply, Matrix.one_apply_eq]
    ring
  have hsingle : (uij hij c : Matrix (Fin 3) (Fin 3) ℝ) = 1 + Matrix.single i j c := by
    rw [show (uij hij c : Matrix (Fin 3) (Fin 3) ℝ) = toMat (uij hij c) from rfl, Work.EKLContract.Lemmas.toMat_uij]
  have hwentry : (uij hij c * v) i j = S.δ k / 2 := by
    have h1 : ((uij hij c * v : SL3) : Matrix (Fin 3) (Fin 3) ℝ) i j
        = (v : Matrix (Fin 3) (Fin 3) ℝ) i j
          + c * (v : Matrix (Fin 3) (Fin 3) ℝ) j j := by
      rw [hcoe_uv, hsingle, add_mul, one_mul, Matrix.add_apply, single_mul_apply']
      simp
    have h2 : ((uij hij c * v : SL3) : Matrix (Fin 3) (Fin 3) ℝ) i j = S.δ k / 2 := by
      rw [h1, hventry, hvjentry, hcdef]
      have hden : (1 + A j j) ≠ 0 := ne_of_gt hden_pos
      have hcancel : (S.δ k / 2 - A i j) / (1 + A j j) * (1 + A j j) = S.δ k / 2 - A i j :=
        div_mul_cancel₀ _ hden
      have hcomm : A j j + 1 = 1 + A j j := by ring
      rw [hcomm, hcancel]
      ring
    simpa using h2
  have hv'4 : v' ∈ V (4 * S.δ k) := V_mono' (by linarith [hδpos]) hv'
  have heq : uij hij c * v = v' :=
    S.hinj k _ _ hw4 hv'4 (by rw [mul_smul, hvy]; exact hv'eq.symm)
  have hv'entry : |v' i j| < S.δ k / 2 := by
    have h1 := hv' i j
    rw [Matrix.one_apply_ne hij, sub_zero] at h1
    exact h1
  rw [heq] at hwentry
  rw [hwentry] at hv'entry
  rw [abs_of_pos (by linarith [hδpos] : (0 : ℝ) < S.δ k / 2)] at hv'entry
  exact absurd hv'entry (lt_irrefl (S.δ k / 2))

end Work.EKLC6Core
