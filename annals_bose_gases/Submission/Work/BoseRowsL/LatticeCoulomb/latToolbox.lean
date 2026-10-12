import Mathlib.Analysis.InnerProductSpace.PiL2
import Submission.Work.BoseRowsL.LatticeCoulomb.kernelDefs
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Work.BoseRowsL.LatticeCoulomb.latToolbox`

Shared vocabulary for the `telescopeV` chapter: the lattice basis vector `latE j`, the
coordinate form of `nvec`, and the reflection symmetry of the lattice ball `T` given by

  `h1 : ∀ n ∈ T, n ≠ 0`, `h2 : ∀ n ∈ T, ‖nvec n‖ ≤ R`,
  `h4 : ∀ n ≠ 0, ‖nvec n‖ ≤ R → n ∈ T`

(which together say `T = {n ≠ 0 : ‖nvec n‖ ≤ R}`; in particular `T = −T`).

It also fixes the notation of the telescoped sum of `telescopeV`: `PhiK` (the combined kernel
`Φ`), `shiftSet` (the index set `T ∪ T_+ ∪ T_-`), `latPhase`, `deepSet` (`T ∩ T_+ ∩ T_-`) and the
majorant `deepKernel`.

## The two lattice estimates consumed by `telescopeV`

* `Work.BoseRowsL.LatticeCoulomb.deepLatticeSumBound` — the deep (absolutely convergent) part;
* `Work.BoseRowsL.LatticeCoulomb.stripSumBound` — the boundary (strip) part.

Both are stated for the set `T` and the two shifted sets `T ± e_j`; see `FINDING_telescopeV.md`.
-/

noncomputable section

open scoped Real BigOperators Topology
open MeasureTheory Metric

namespace Work.BoseRowsL.LatticeCoulomb

set_option autoImplicit false

/-- The lattice basis vector `e_j`. -/
def latE (j : Fin 3) : Fin 3 → ℤ := fun i => if i = j then 1 else 0

@[simp] lemma latE_self (j : Fin 3) : latE j j = 1 := by simp [latE]

lemma latE_ne {i j : Fin 3} (h : i ≠ j) : latE j i = 0 := by simp [latE, h]

lemma nvec_add (n m : Fin 3 → ℤ) : nvec (n + m) = nvec n + nvec m := by
  ext i
  simp [nvec, PiLp.toLp_apply]

lemma nvec_sub (n m : Fin 3 → ℤ) : nvec (n - m) = nvec n - nvec m := by
  ext i
  simp [nvec, PiLp.toLp_apply]

lemma nvec_neg (n : Fin 3 → ℤ) : nvec (-n) = -nvec n := by
  ext i
  simp [nvec, PiLp.toLp_apply]

lemma norm_nvec_neg (n : Fin 3 → ℤ) : ‖nvec (-n)‖ = ‖nvec n‖ := by
  rw [nvec_neg, norm_neg]

lemma nvec_latE_self (j : Fin 3) : (nvec (latE j)).ofLp j = 1 := by
  rw [nvec_apply, latE_self]; norm_num

lemma nvec_latE_ne {i j : Fin 3} (h : i ≠ j) : (nvec (latE j)).ofLp i = 0 := by
  rw [nvec_apply, latE_ne h]; norm_num

/-- The coordinate form of the inner product. -/
lemma inner_nvec_eq_sum (n : Fin 3 → ℤ) (z : E3) :
    inner ℝ (nvec n) z = ∑ i : Fin 3, (n i : ℝ) * z.ofLp i := by
  rw [PiLp.inner_apply]
  exact Finset.sum_congr rfl (fun i _ => by
    rw [Real.inner_apply, nvec_apply])

lemma inner_nvec_add_latE (n : Fin 3 → ℤ) (j : Fin 3) (z : E3) :
    inner ℝ (nvec (n + latE j)) z = inner ℝ (nvec n) z + z.ofLp j := by
  rw [inner_nvec_eq_sum, inner_nvec_eq_sum]
  conv_lhs => rw [show ∑ i : Fin 3, ((n + latE j) i : ℝ) * z.ofLp i
      = ∑ i : Fin 3, ((n i : ℝ) * z.ofLp i + (((latE j) i : ℤ) : ℝ) * z.ofLp i) from
    Finset.sum_congr rfl (fun i _ => by
      have h : (((n + latE j) i : ℤ) : ℝ) = (n i : ℝ) + (((latE j) i : ℤ) : ℝ) := by simp
      rw [h]; ring)]
  rw [Finset.sum_add_distrib]
  congr 1
  rw [Finset.sum_eq_single j]
  · simp [latE_self]
  · intro i _ hi; simp [latE_ne hi]
  · intro hj; exact absurd (Finset.mem_univ j) hj

lemma inner_nvec_sub_latE (n : Fin 3 → ℤ) (j : Fin 3) (z : E3) :
    inner ℝ (nvec (n - latE j)) z = inner ℝ (nvec n) z - z.ofLp j := by
  rw [inner_nvec_eq_sum, inner_nvec_eq_sum]
  conv_lhs => rw [show ∑ i : Fin 3, ((n - latE j) i : ℝ) * z.ofLp i
      = ∑ i : Fin 3, ((n i : ℝ) * z.ofLp i - (((latE j) i : ℤ) : ℝ) * z.ofLp i) from
    Finset.sum_congr rfl (fun i _ => by
      have h : (((n - latE j) i : ℤ) : ℝ) = (n i : ℝ) - (((latE j) i : ℤ) : ℝ) := by simp
      rw [h]; ring)]
  rw [Finset.sum_sub_distrib]
  congr 1
  rw [Finset.sum_eq_single j]
  · simp [latE_self]
  · intro i _ hi; simp [latE_ne hi]
  · intro hj; exact absurd (Finset.mem_univ j) hj

/-- `nvec (n + latE j) − nvec (latE j) = nvec n`. -/
lemma nvec_add_latE_sub_latE (n : Fin 3 → ℤ) (j : Fin 3) :
    nvec (n + latE j) - nvec (latE j) = nvec n := by
  rw [nvec_add, add_sub_cancel_right]

lemma nvec_sub_latE_add_latE (n : Fin 3 → ℤ) (j : Fin 3) :
    nvec (n - latE j) + nvec (latE j) = nvec n := by
  rw [nvec_sub, sub_add_cancel]

lemma latE_ne_zero (j : Fin 3) : latE j ≠ 0 := by
  intro h
  have := latE_self j
  rw [h] at this
  simp at this

lemma neg_latE_ne_zero (j : Fin 3) : -latE j ≠ 0 := neg_ne_zero.mpr (latE_ne_zero j)

/-- The lattice ball `T` is symmetric under `n ↦ -n`. -/
lemma neg_mem_iff {R : ℝ} {T : Finset (Fin 3 → ℤ)} (h1 : ∀ n ∈ T, n ≠ 0)
    (h2 : ∀ n ∈ T, ‖nvec n‖ ≤ R)
    (h4 : ∀ n : Fin 3 → ℤ, n ≠ 0 → ‖nvec n‖ ≤ R → n ∈ T) {n : Fin 3 → ℤ} :
    (-n) ∈ T ↔ n ∈ T := by
  constructor
  · intro h
    by_cases hn : n = 0
    · subst hn
      exact absurd h (by simpa using h1 0)
    · have h' : ‖nvec (-n)‖ ≤ R := h2 (-n) h
      rw [norm_nvec_neg] at h'
      exact h4 n hn h'
  · intro h
    by_cases hn : n = 0
    · subst hn
      exact absurd h (by simpa using h1 0)
    · have h' : ‖nvec n‖ ≤ R := h2 n h
      rw [← norm_nvec_neg] at h'
      exact h4 (-n) (neg_ne_zero.mpr hn) h'

/-- Sums over `T` are invariant under `n ↦ -n`. -/
lemma sum_neg_eq_sum {R : ℝ} {T : Finset (Fin 3 → ℤ)} (h1 : ∀ n ∈ T, n ≠ 0)
    (h2 : ∀ n ∈ T, ‖nvec n‖ ≤ R)
    (h4 : ∀ n : Fin 3 → ℤ, n ≠ 0 → ‖nvec n‖ ≤ R → n ∈ T) (f : (Fin 3 → ℤ) → ℝ) :
    ∑ n ∈ T, f (-n) = ∑ n ∈ T, f n := by
  refine Finset.sum_bij (fun n _ => -n) ?_ ?_ ?_ ?_
  · intro n hn
    exact (neg_mem_iff h1 h2 h4).mpr hn
  · intro a _ b _ hab
    simpa using hab
  · intro b hb
    exact ⟨-b, (neg_mem_iff h1 h2 h4).mpr hb, by simp⟩
  · intro a _
    simp

/-- `A_n = 2π⟪nvec n,z⟫`: the phase of the lattice summand. -/
def latPhase (z : E3) (n : Fin 3 → ℤ) : ℝ := 2 * Real.pi * inner ℝ (nvec n) z

/-- The index set of the telescoped sum: `T ∪ (T+e_j) ∪ (T−e_j)`. -/
def shiftSet (T : Finset (Fin 3 → ℤ)) (j : Fin 3) : Finset (Fin 3 → ℤ) :=
  T ∪ T.image (fun n => n + latE j) ∪ T.image (fun n => n - latE j)

/-- The deep set `T ∩ (T+e_j) ∩ (T−e_j)`. -/
def deepSet (T : Finset (Fin 3 → ℤ)) (j : Fin 3) : Finset (Fin 3 → ℤ) :=
  T.filter (fun m => m + latE j ∈ T ∧ m - latE j ∈ T)

/-- The combined kernel of the telescoped sum, over the index set `T ∪ T_+ ∪ T_-`:

`Φ(m) = 1_T(m)(−2m_j/‖m‖⁴) + (1/2)·1_{T_+}(m)/‖m−e_j‖² − (1/2)·1_{T_-}(m)/‖m+e_j‖²`. -/
def PhiK (T : Finset (Fin 3 → ℤ)) (j : Fin 3) (m : Fin 3 → ℤ) : ℝ :=
  (if m ∈ T then -2 * (nvec m).ofLp j / ‖nvec m‖ ^ 4 else 0)
    + (if m - latE j ∈ T then 1 / (2 * ‖nvec m - nvec (latE j)‖ ^ 2) else 0)
    - (if m + latE j ∈ T then 1 / (2 * ‖nvec m + nvec (latE j)‖ ^ 2) else 0)

/-- The pointwise majorant of the deep part `Φ(m) = 2m_j(1/u − 1/a²)` on `T°`
(`a = ‖nvec m‖²`, `u = ‖m−e_j‖²‖m+e_j‖² = (a+1)² − 4m_j² ≥ max(1,(a−1)²)` there):

`2|m_j|·|4m_j² − 2a − 1| / (a²·max((a−1)²,1))`. -/
def deepKernel (j : Fin 3) (m : Fin 3 → ℤ) : ℝ :=
  2 * |(nvec m).ofLp j| * |4 * (nvec m).ofLp j ^ 2 - 2 * ‖nvec m‖ ^ 2 - 1|
    / (‖nvec m‖ ^ 4 * max ((‖nvec m‖ ^ 2 - 1) ^ 2) 1)

/-- The deep part of the telescoped kernel: the exact second-order cancellation on `T°`. -/
def PhiDeep (T : Finset (Fin 3 → ℤ)) (j : Fin 3) (m : Fin 3 → ℤ) : ℝ :=
  if m ∈ deepSet T j then
    2 * (nvec m).ofLp j
      * (1 / ((‖nvec m - nvec (latE j)‖ ^ 2) * (‖nvec m + nvec (latE j)‖ ^ 2))
          - 1 / ‖nvec m‖ ^ 4)
  else 0

/-- The boundary part of the telescoped kernel: `Φ − Φdeep`. -/
def PhiBound (T : Finset (Fin 3 → ℤ)) (j : Fin 3) (m : Fin 3 → ℤ) : ℝ :=
  PhiK T j m - PhiDeep T j m

end Work.BoseRowsL.LatticeCoulomb
