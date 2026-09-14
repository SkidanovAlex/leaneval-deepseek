import Submission.NBody.Jacobi
import Submission.NBody.Potential
import Mathlib

/-!
# The a priori bound `U ≥ c / √I`

The classical first ingredient of the asymptotic theory of collisions in the `N`-body problem
(Sperner, Wintner) is the *a priori bound* relating the Newtonian potential to the moment of
inertia `I = ∑ᵢ mᵢ‖xᵢ‖²`:

    `U(x) ≥ c / √(I(x))`

for a collision-free configuration and a constant `c > 0` depending only on the masses.  It follows
from the elementary estimate `rᵢⱼ ≤ 2 √(I/κ)` (where `κ = min m`), which in turn is
`‖xᵢ - xⱼ‖ ≤ ‖xᵢ‖ + ‖xⱼ‖` together with `mᵢ‖xᵢ‖² ≤ I`.

Together with the Lagrange–Jacobi identity `I'' = 4E + 2U`
(`Submission.NBody.iteratedDeriv_two_inertia`) this yields the classical lower bound
`I(t) ≥ c' |t - t₀|^{4/3}` near a collision — the first step of Marchal's theorem.
-/

open ViscositySolutions
open Filter Gradient Real Set
open scoped BigOperators Topology ENNReal
open MeasureTheory

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 1000000

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
variable [Nontrivial E]
variable {N : ℕ}

namespace Submission.NBody

/-- **The a priori bound.**  For `2 ≤ N` there is `c > 0`, depending only on the masses, with
`c / √(∑ᵢ mᵢ‖xᵢ‖²) ≤ U m x` for every collision-free configuration `x`. -/
theorem exists_const_div_sqrt_inertia_le_U {m : Fin N → ℝ} (hm : ∀ i, 0 < m i) (hN : 2 ≤ N) :
    ∃ c : ℝ, 0 < c ∧ ∀ x : EN E N, WithoutCollisions x →
      c / Real.sqrt (∑ i, m i * ‖x i‖ ^ 2) ≤ U m x := by
  classical
  -- a positive lower bound for the masses
  obtain ⟨κ, hκpos, hκ⟩ : ∃ c : ℝ, 0 < c ∧ ∀ i, c ≤ m i := by
    obtain ⟨i₀, -, hi₀⟩ := Finset.exists_min_image (Finset.univ : Finset (Fin N)) m
      ⟨⟨0, by omega⟩, Finset.mem_univ _⟩
    exact ⟨m i₀, hm i₀, fun i => hi₀ i (Finset.mem_univ i)⟩
  obtain ⟨i₁, j₁, hij₁⟩ : ∃ i j : Fin N, i ≠ j :=
    ⟨⟨0, by omega⟩, ⟨1, by omega⟩, by simp⟩
  have hpairpos : 0 < m i₁ * m j₁ := mul_pos (hm i₁) (hm j₁)
  set c : ℝ := m i₁ * m j₁ * Real.sqrt κ / 2 with hcdef
  have hcpos : 0 < c := by
    rw [hcdef]
    have : (0:ℝ) < Real.sqrt κ := Real.sqrt_pos.mpr hκpos
    positivity
  refine ⟨c, hcpos, fun x hx => ?_⟩
  set I : ℝ := ∑ i, m i * ‖x i‖ ^ 2 with hIdef
  have hInn : 0 ≤ I := Finset.sum_nonneg fun i _ => mul_nonneg (hm i).le (sq_nonneg _)
  -- `I > 0` because there is at least one pair of distinct bodies
  have hdist_pos : ∀ i j : Fin N, i ≠ j → 0 < dist (x i) (x j) :=
    fun i j hij => dist_pos.mpr fun heq => hx i j hij (by rw [r, dist_eq_zero]; exact heq)
  have hIpos : 0 < I := by
    have h1 : m i₁ * ‖x i₁‖ ^ 2 + m j₁ * ‖x j₁‖ ^ 2 ≤ I := by
      rw [hIdef]
      have h := Finset.sum_le_sum_of_subset_of_nonneg
        (f := fun k : Fin N => m k * ‖x k‖ ^ 2)
        (Finset.subset_univ ({i₁, j₁} : Finset (Fin N)))
        (fun k _ _ => mul_nonneg (hm k).le (sq_nonneg _))
      rwa [Finset.sum_pair hij₁] at h
    have h2 : 0 < ‖x i₁‖ ^ 2 + ‖x j₁‖ ^ 2 := by
      have h3 : (0:ℝ) < ‖x i₁ - x j₁‖ := by
        have h4 := hdist_pos i₁ j₁ hij₁
        rwa [dist_eq_norm] at h4
      nlinarith [norm_nonneg (x i₁ - x j₁), norm_nonneg (x i₁), norm_nonneg (x j₁),
        norm_sub_le (x i₁) (x j₁), sq_nonneg (‖x i₁‖ - ‖x j₁‖)]
    have h5 : κ * (‖x i₁‖ ^ 2 + ‖x j₁‖ ^ 2) ≤ m i₁ * ‖x i₁‖ ^ 2 + m j₁ * ‖x j₁‖ ^ 2 := by
      nlinarith [hκ i₁, hκ j₁, sq_nonneg (‖x i₁‖), sq_nonneg (‖x j₁‖)]
    nlinarith [h1, h2, h5, hκpos]
  -- `‖x i‖² ≤ I / κ`
  have hcoord : ∀ i : Fin N, ‖x i‖ ^ 2 ≤ I / κ := by
    intro i
    have h1 : m i * ‖x i‖ ^ 2 ≤ I := by
      rw [hIdef]
      exact Finset.single_le_sum (f := fun k : Fin N => m k * ‖x k‖ ^ 2)
        (fun k _ => mul_nonneg (hm k).le (sq_nonneg _)) (Finset.mem_univ i)
    rw [le_div_iff₀ hκpos]
    calc ‖x i‖ ^ 2 * κ ≤ ‖x i‖ ^ 2 * m i := mul_le_mul_of_nonneg_left (hκ i) (sq_nonneg _)
      _ = m i * ‖x i‖ ^ 2 := by ring
      _ ≤ I := h1
  -- `dist (x i) (x j) ≤ 2 √(I/κ)`
  have hdist : ∀ i j : Fin N, dist (x i) (x j) ≤ 2 * Real.sqrt (I / κ) := by
    intro i j
    have h1 : ‖x i - x j‖ ≤ ‖x i‖ + ‖x j‖ := norm_sub_le _ _
    have h2 : ‖x i‖ ≤ Real.sqrt (I / κ) := by
      rw [← Real.sqrt_sq (norm_nonneg _)]
      exact Real.sqrt_le_sqrt (hcoord i)
    have h3 : ‖x j‖ ≤ Real.sqrt (I / κ) := by
      rw [← Real.sqrt_sq (norm_nonneg _)]
      exact Real.sqrt_le_sqrt (hcoord j)
    rw [dist_eq_norm]
    linarith
  -- consequence for the reciprocal
  have hinv : ∀ i j : Fin N, i ≠ j →
      Real.sqrt κ / (2 * Real.sqrt I) ≤ (dist (x i) (x j))⁻¹ := by
    intro i j hij
    have hpos := hdist_pos i j hij
    have h2 : dist (x i) (x j) ≤ 2 * Real.sqrt I / Real.sqrt κ := by
      have h3 : 2 * Real.sqrt (I / κ) = 2 * Real.sqrt I / Real.sqrt κ := by
        rw [Real.sqrt_div (x := I) hInn κ, mul_div_assoc]
      rw [← h3]
      exact hdist i j
    have hBpos : 0 < 2 * Real.sqrt I / Real.sqrt κ := by
      have h1 : 0 < Real.sqrt I := Real.sqrt_pos.mpr hIpos
      have h2 : 0 < Real.sqrt κ := Real.sqrt_pos.mpr hκpos
      positivity
    have h4 : (2 * Real.sqrt I / Real.sqrt κ)⁻¹ ≤ (dist (x i) (x j))⁻¹ :=
      (inv_le_inv₀ hBpos hpos).mpr h2
    have h5 : (2 * Real.sqrt I / Real.sqrt κ)⁻¹ = Real.sqrt κ / (2 * Real.sqrt I) := by
      rw [inv_div]
    rwa [h5] at h4
  -- a positive constant times the reciprocal is at most `U`
  have hterm : ∀ i j : Fin N, i ≠ j →
      m i * m j * (Real.sqrt κ / (2 * Real.sqrt I)) ≤ m i * m j * (dist (x i) (x j))⁻¹ :=
    fun i j hij => mul_le_mul_of_nonneg_left (hinv i j hij) (mul_nonneg (hm i).le (hm j).le)
  have hsum : ∀ p : Fin N × Fin N,
      0 ≤ m p.1 * m p.2 * (r x p.1 p.2)⁻¹ :=
    fun p => mul_nonneg (mul_nonneg (hm p.1).le (hm p.2).le) (inv_nonneg.mpr dist_nonneg)
  have hU : m i₁ * m j₁ * (Real.sqrt κ / (2 * Real.sqrt I)) ≤ U m x := by
    rw [U_eq_pairFinset]
    rcases lt_or_gt_of_ne hij₁ with hlt | hgt
    · have hmem : (i₁, j₁) ∈ pairFinset N := by
        rw [pairFinset, Finset.mem_filter]; exact ⟨Finset.mem_univ _, hlt⟩
      have h := Finset.single_le_sum (s := pairFinset N)
        (f := fun p : Fin N × Fin N => m p.1 * m p.2 * (r x p.1 p.2)⁻¹)
        (fun p _ => hsum p) hmem
      exact le_trans (hterm i₁ j₁ hij₁) h
    · have hmem : (j₁, i₁) ∈ pairFinset N := by
        rw [pairFinset, Finset.mem_filter]; exact ⟨Finset.mem_univ _, hgt⟩
      have h := Finset.single_le_sum (s := pairFinset N)
        (f := fun p : Fin N × Fin N => m p.1 * m p.2 * (r x p.1 p.2)⁻¹)
        (fun p _ => hsum p) hmem
      refine le_trans ?_ h
      calc m i₁ * m j₁ * (Real.sqrt κ / (2 * Real.sqrt I))
          = m j₁ * m i₁ * (Real.sqrt κ / (2 * Real.sqrt I)) := by ring
        _ ≤ m j₁ * m i₁ * (dist (x j₁) (x i₁))⁻¹ := hterm j₁ i₁ (Ne.symm hij₁)
        _ = m j₁ * m i₁ * (r x j₁ i₁)⁻¹ := by rw [r]
  have hgoal : c / Real.sqrt I = m i₁ * m j₁ * (Real.sqrt κ / (2 * Real.sqrt I)) := by
    rw [hcdef]; ring
  rw [hgoal]
  exact hU

end Submission.NBody
