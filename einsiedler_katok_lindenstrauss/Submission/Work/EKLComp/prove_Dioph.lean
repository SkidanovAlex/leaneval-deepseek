import Mathlib
import Submission.Work.EKLContract.Interfaces
import Submission.Work.EKLComp.dioph_coord_bound
import Submission.Work.EKLComp.dioph_lower_bound
import Submission.Work.EKLContract.Lemmas.mkX_mul
import Submission.Work.EKLContract.Lemmas.mkX_one_short

/-! Guidance from the project lead (the requester):

CONTEXT (project lead). This is one component of the FROZEN EKL contract (Submission/Work/EKLContract/Defs.lean; the composition
ekl_of_components and the glue are PROVED, so proving all components closes the problem). Read first:
* Submission/Work/EKLPlan/ROUTE_LEAD.md: your component section, with its source (EKL / Pisa notes / Venkatesh), proof sketch and hardest step;
* EKLContract/NOTES.md (statement changes) and REPORT.md;
* REFS/ (EKL TeX, the Pisa notes, the feasibility audit).
Other components are available as hypotheses only where your Prop takes them. Do not assume anything else. Reuse
EKLContract/Lemmas/* and Mathlib. Parallelise: request independent pieces at once.

YOUR COMPONENT: C1a Diophantine reduction.
-/

open MeasureTheory Filter Topology
open scoped ENNReal
open LeanEval.Dynamics.EinsiedlerKatokLindenstrauss

set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
set_option linter.style.haveILetI false

noncomputable section

namespace Work.EKLComp

open Work.EKLContract

/-! ## Elementary matrix computations for `τ_{u,v}` and `a(r,s)` -/

/-- `1 ≠ 0` in `Fin 3`, as an `abbrev` so that it unfolds definitionally. -/
abbrev H10 : (1 : Fin 3) ≠ 0 := by decide

/-- `2 ≠ 0` in `Fin 3`. -/
abbrev H20 : (2 : Fin 3) ≠ 0 := by decide

/-- The underlying matrix of `aPlus r s = a(r,s) = diag(e^{-r-s}, e^r, e^s)`. -/
theorem toMat_aPlus (r s : ℝ) :
    toMat (aPlus r s) = Matrix.diagonal ![Real.exp (-r - s), Real.exp r, Real.exp s] := by
  rw [aPlus, toMat_aDiag]
  congr 1
  ext i
  fin_cases i <;> simp [Fin.sum_univ_three] <;> ring_nf

/-- The underlying matrix of the root-group part of `τ_{u,v}`, namely
`[[1,0,0],[u,1,0],[v,0,1]]`. -/
theorem toMat_tauMat (u v : ℝ) :
    toMat (uij H10 u * uij H20 v) = !![1, 0, 0; u, 1, 0; v, 0, 1] := by
  have h1 : toMat (uij H10 u) = Matrix.transvection (1 : Fin 3) 0 u := rfl
  have h2 : toMat (uij H20 v) = Matrix.transvection (2 : Fin 3) 0 v := rfl
  rw [toMat_mul, h1, h2]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.transvection, Matrix.mul_apply, Matrix.single_apply, Fin.sum_univ_three,
      Matrix.one_apply]

/-- **The coordinates of `a(r,s) τ_{u,v} · k`**: for an integer vector `k`,
the vector `a(r,s)·τ_{u,v}·k` has coordinates `(e^{-r-s}k₀, e^r(u k₀+k₁), e^s(v k₀+k₂))`. -/
theorem mulVec_aPlus_tau (u v r s : ℝ) (k : Fin 3 → ℤ) :
    Matrix.mulVec (toMat (aPlus r s * (uij H10 u * uij H20 v))) (fun j => (k j : ℝ))
      = ![Real.exp (-r - s) * (k 0 : ℝ),
          Real.exp r * (u * (k 0 : ℝ) + (k 1 : ℝ)),
          Real.exp s * (v * (k 0 : ℝ) + (k 2 : ℝ))] := by
  rw [toMat_mul, toMat_aPlus, toMat_tauMat]
  rw [← Matrix.mulVec_mulVec]
  funext i
  fin_cases i <;>
    simp [Matrix.mulVec_apply_eq_sum, Matrix.diagonal_apply, Fin.sum_univ_three,
      Matrix.vecHead, Matrix.vecTail]


/-! ## The Diophantine core: an integral vector of the lattice has no short coordinate -/

/-- **No short vector.**  If `k ≠ 0` is an integral vector, the vector `a(r,s)·τ_{u,v}·k` has a
coordinate of absolute value `≥ ρ`, under the Diophantine lower bound `δ` (for all `n ≥ 1`)
together with `ρ³ ≤ δ` and `ρ ≤ 1`.  This is step 2 of EKL Prop. 11.1 in the coordinates of
`mulVec_aPlus_tau`. -/
theorem no_short_vec (u v ρ δ : ℝ) (hρ : 0 < ρ) (hρ1 : ρ ≤ 1) (hρδ : ρ ^ 3 ≤ δ)
    (hδ : ∀ n : ℕ, 1 ≤ n →
      δ ≤ (n : ℝ) * distToNearestInt (n * u) * distToNearestInt (n * v))
    (r s : ℝ) (hr : 0 ≤ r) (hs : 0 ≤ s) (k : Fin 3 → ℤ) (hk : k ≠ 0) :
    ∃ i : Fin 3, ρ ≤ |Matrix.mulVec (toMat (aPlus r s * (uij H10 u * uij H20 v)))
      (fun j => (k j : ℝ)) i| := by
  by_contra hcon
  simp only [not_exists, not_le] at hcon
  rw [mulVec_aPlus_tau] at hcon
  refine dioph_coord_bound u v ρ δ hρ hρ1 hρδ hδ r s hr hs k hk ?_ ?_ ?_
  · have := hcon 0; simpa [Matrix.vecHead] using this
  · have := hcon 1; simpa [Matrix.vecHead, Matrix.vecTail] using this
  · have := hcon 2; simpa [Matrix.vecHead, Matrix.vecTail] using this

/-- **C1a, Diophantine reduction** (EKL Prop. 11.1, `⇐` half; Pisa 12.5/12.8).  Every point of
the Littlewood exceptional set `Xi` has an `A⁺`-orbit staying in a fixed `Thick ρ`. -/
theorem prove_Dioph : Work.EKLContract.P_Dioph := by
  rintro ⟨u, v⟩ hp
  obtain ⟨δ, hδpos, hδ⟩ := dioph_lower_bound u v hp
  set ρ : ℝ := min (1 / 2) δ with hρdef
  have hρ : 0 < ρ := by rw [hρdef]; exact lt_min (by norm_num) hδpos
  have hρ1 : ρ ≤ 1 := by rw [hρdef]; exact le_trans (min_le_left _ _) (by norm_num)
  have hρδ : ρ ^ 3 ≤ δ := by
    have h1 : ρ ≤ δ := by rw [hρdef]; exact min_le_right _ _
    have h2 : ρ ^ 3 ≤ ρ := by
      nlinarith [hρ, hρ1, sq_nonneg (ρ - 1), sq_nonneg ρ]
    linarith
  refine ⟨ρ, hρ, ?_⟩
  rw [Drho]
  intro r s hr hs
  simp only [Thick]
  rintro ⟨g, hg, m, hm, hshort⟩
  set Y : SL3 := aPlus r s * (uij H10 u * uij H20 v) with hYdef
  have hY : mkX g = mkX Y := by
    rw [hg, hYdef]
    exact (Work.EKLContract.Lemmas.mkX_mul (aPlus r s) (uij H10 u * uij H20 v)).symm
  have hγ : g⁻¹ * Y ∈ Γ3 := QuotientGroup.eq.mp hY
  have hγi : (g⁻¹ * Y)⁻¹ ∈ Γ3 := Subgroup.inv_mem _ hγ
  obtain ⟨A, hA⟩ := Work.EKLContract.Lemmas.exists_intSL3_of_mem_Γ3 hγi
  set k : Fin 3 → ℤ := Matrix.mulVec (A : Matrix (Fin 3) (Fin 3) ℤ) m with hkdef
  have hk : k ≠ 0 := by
    rw [hkdef]
    exact Work.EKLContract.Lemmas.mulVec_int_ne_zero A hm
  have hge : g = Y * (g⁻¹ * Y)⁻¹ := by group
  have hgA : toMat g = toMat Y * ((A : SL3) : Matrix (Fin 3) (Fin 3) ℝ) := by
    rw [hge, toMat_mul]
    congr 1
    rw [← hA]
  have hvec : ∀ i, Matrix.mulVec (toMat g) (fun j => (m j : ℝ)) i
      = Matrix.mulVec (toMat Y) (fun j => (k j : ℝ)) i := by
    intro i
    have h1 : Matrix.mulVec (toMat g) (fun j => (m j : ℝ))
        = Matrix.mulVec (toMat Y) (fun j => (k j : ℝ)) := by
      rw [hgA, ← Matrix.mulVec_mulVec]
      congr 1
      ext j
      rw [Work.EKLContract.Lemmas.mulVec_coe_int A m j, ← hkdef]
    exact congrFun h1 i
  have hkey : ∀ i, |Matrix.mulVec (toMat Y) (fun j => (k j : ℝ)) i| < ρ := by
    intro i
    rw [← hvec i]
    exact hshort i
  obtain ⟨i, hi⟩ := no_short_vec u v ρ δ hρ hρ1 hρδ hδ r s hr hs k hk
  rw [← hYdef] at hi
  exact absurd hi (not_le.mpr (hkey i))

end Work.EKLComp
