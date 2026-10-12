import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.Real.Pi.Bounds
import Submission.Work.BoseBoxFock.chiTailDefs
import Submission.Work.BoseK15.ChiReg_corpus
import Submission.Work.BoseK15.sum_inv_one_add_norm_tail
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Work.BoseBoxFock.hatChiSq_cubeCompl_tail`

The *tail* of the lattice sum of `χ̂²` over the lattice points **outside** the cube
`[-N,N]³`, decaying faster than any power of `N`.

This is the `χ̂²`-counterpart of the K15 chapter's `tail_hatChiSq`, in the form used by the
`χ`-row truncation device of `Submission/Work/BoseBoxFock/chiTailDefs.lean`: the truncation
error of the mode sums in `Work.BoseBoxFock.chiTail` / `thetaTail` is controlled by exactly
this sum, and `PotChiLin_exists` takes `Nmin` so that it is far below every polynomial slot of
`errKafz`.

## The argument

`∑'_{m ∉ cube N} |χ̂²(vec m)| ≤ C/(N+1)^K` in three steps:

* **decay** (`Work.BoseK15.ChiReg_corpus`): the corpus `χ` is `C^∞` with compact support, so
  `|χ̂²(p)| ≤ C₂ · (1 + ‖p‖²)^{-(K+3)}` for every momentum `p`;
* **geometry** (`norm_vec_ge_of_not_cubeCompl`): `m ∉ [-N,N]³` has a coordinate of modulus
  `≥ N+1`, so `‖vec m‖ ≥ 2π(N+1) ≥ 1`;
* **lattice tail** (`Work.BoseK15.sum_inv_one_add_norm_tail`): with all momenta outside the
  ball of radius `R = 2π(N+1) ≥ 1` and the exponent `K+3` satisfying `K+3 ≤ 2(K+3)`, the
  finite lattice sums of `(1+‖p‖²)^{-(K+3)}` are `≤ 128/R^K`, whence `≤ 128/(N+1)^K`
  since `2π ≥ 1`.

The infinite sum is reduced to the finite ones by `Real.tsum_le_of_sum_le`, the finite sets of
the complement subtype being pushed into `ℤ³` through the injection `Subtype.val`.
-/

noncomputable section

open scoped BigOperators

namespace Work.BoseBoxFock

/-- **The geometry of the cube complement.**  A lattice point outside `[-N,N]³` has a
coordinate of modulus at least `N+1`, hence its momentum `vec m = 2π m` has norm at least
`2π(N+1)`. -/
theorem norm_vec_ge_of_not_cubeCompl {N : ℕ} {m : Fin 3 → ℤ}
    (hm : ¬ (∀ i : Fin 3, -(N : ℤ) ≤ m i ∧ m i ≤ (N : ℤ))) :
    2 * Real.pi * ((N : ℝ) + 1) ≤ ‖Work.BoseB4.vec m‖ := by
  rw [not_forall] at hm
  obtain ⟨j, hj⟩ := hm
  have hcase : ((N : ℤ) + 1) ≤ |m j| := by
    rcases not_and_or.mp hj with h | h
    · have hlt : m j < -(N : ℤ) := not_le.mp h
      have hneg : m j < 0 := by omega
      rw [abs_of_neg hneg]; omega
    · have hpos : 0 < m j := by omega
      rw [abs_of_pos hpos]; omega
  have hcast : ((N : ℝ) + 1) ≤ |((m j : ℤ) : ℝ)| := by
    rw [← Int.cast_abs]; exact_mod_cast hcase
  have hcomp : |(Work.BoseB4.vec m) j| ≤ ‖Work.BoseB4.vec m‖ :=
    PiLp.norm_apply_le (Work.BoseB4.vec m) j
  have hval : (Work.BoseB4.vec m) j = 2 * Real.pi * ((m j : ℤ) : ℝ) := by
    simp [Work.BoseB4.vec]
  rw [hval, abs_mul, abs_of_pos (by positivity : (0 : ℝ) < 2 * Real.pi)] at hcomp
  calc 2 * Real.pi * ((N : ℝ) + 1) ≤ 2 * Real.pi * |((m j : ℤ) : ℝ)| :=
        mul_le_mul_of_nonneg_left hcast (by positivity)
    _ ≤ ‖Work.BoseB4.vec m‖ := hcomp

/-- **The `χ̂²` lattice tail outside the cube.**  For every decay order `K` there is `C ≥ 0`
with `∑'_{m ∉ [-N,N]³} |χ̂²(vec m)| ≤ C·(N+1)^{-K}` for all `N`. -/
theorem hatChiSq_cubeCompl_tail (K : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ N : ℕ,
      (∑' m : {m : Fin 3 → ℤ // ¬ (∀ i : Fin 3, -(N : ℤ) ≤ m i ∧ m i ≤ (N : ℤ))},
        |Work.BoseK15.corpusBox.hatChiSq (Work.BoseB4.vec m)|)
        ≤ C / ((N : ℝ) + 1) ^ K := by
  -- the two analytic inputs: `χ̂²`-decay at order `K+3`, and the lattice tail at exponent `K`
  obtain ⟨C₂, hC₂nn, hC₂⟩ := Work.BoseK15.ChiReg_corpus (K + 3)
  obtain ⟨C₃, hC₃nn, hC₃⟩ :=
    Work.BoseK15.sum_inv_one_add_norm_tail (K + 3) K (by omega)
  refine ⟨C₂ * C₃, mul_nonneg hC₂nn hC₃nn, fun N => ?_⟩
  -- reduce the infinite sum to its finite partial sums (all summands are nonnegative)
  refine Real.tsum_le_of_sum_le (fun x => abs_nonneg _) fun u => ?_
  have hR1 : (1 : ℝ) ≤ 2 * Real.pi * ((N : ℝ) + 1) := by
    have h1 : (1 : ℝ) ≤ (N : ℝ) + 1 := by
      have : (0 : ℝ) ≤ (N : ℝ) := Nat.cast_nonneg N; linarith
    have h2 : (1 : ℝ) ≤ 2 * Real.pi := by linarith [Real.pi_gt_three]
    calc (1 : ℝ) = 1 * 1 := by ring
      _ ≤ (2 * Real.pi) * ((N : ℝ) + 1) := mul_le_mul h2 h1 (by norm_num) (by linarith)
  have hmem : ∀ n ∈ u.image Subtype.val,
      2 * Real.pi * ((N : ℝ) + 1) ≤ ‖Work.BoseB4.vec n‖ := by
    intro n hn
    rw [Finset.mem_image] at hn
    obtain ⟨x, _hx, rfl⟩ := hn
    exact norm_vec_ge_of_not_cubeCompl x.2
  have hstep := hC₃ (2 * Real.pi * ((N : ℝ) + 1)) (u.image Subtype.val) hR1 hmem
  have hper : ∀ x : {m : Fin 3 → ℤ // ¬ (∀ i : Fin 3, -(N : ℤ) ≤ m i ∧ m i ≤ (N : ℤ))},
      |Work.BoseK15.corpusBox.hatChiSq (Work.BoseB4.vec x)|
        ≤ C₂ * (((1 : ℝ) + ‖Work.BoseB4.vec x‖ ^ 2) ^ (K + 3))⁻¹ := by
    intro x
    have h := (hC₂.2) (Work.BoseB4.vec x)
    have hpos : (0 : ℝ) < (1 + ‖Work.BoseB4.vec x‖ ^ 2) ^ (K + 3) := by positivity
    rw [le_mul_inv_iff₀ hpos]
    linarith [h]
  calc (∑ x ∈ u, |Work.BoseK15.corpusBox.hatChiSq (Work.BoseB4.vec x)|)
      ≤ ∑ x ∈ u, C₂ * (((1 : ℝ) + ‖Work.BoseB4.vec x‖ ^ 2) ^ (K + 3))⁻¹ :=
        Finset.sum_le_sum (fun x _ => hper x)
    _ = C₂ * ∑ x ∈ u, (((1 : ℝ) + ‖Work.BoseB4.vec x‖ ^ 2) ^ (K + 3))⁻¹ := by
        rw [Finset.mul_sum]
    _ = C₂ * ∑ y ∈ u.image Subtype.val,
          (((1 : ℝ) + ‖Work.BoseB4.vec y‖ ^ 2) ^ (K + 3))⁻¹ := by
        rw [Finset.sum_image]
        intro a _ b _ h
        exact Subtype.ext h
    _ ≤ C₂ * (C₃ / (2 * Real.pi * ((N : ℝ) + 1)) ^ K) :=
        mul_le_mul_of_nonneg_left hstep hC₂nn
    _ ≤ C₂ * C₃ / ((N : ℝ) + 1) ^ K := by
        have hN : (0 : ℝ) < (N : ℝ) + 1 := by positivity
        have hle : ((N : ℝ) + 1) ^ K ≤ (2 * Real.pi * ((N : ℝ) + 1)) ^ K := by
          apply pow_le_pow_left₀ (le_of_lt hN)
          calc ((N : ℝ) + 1) = 1 * ((N : ℝ) + 1) := by ring
            _ ≤ (2 * Real.pi) * ((N : ℝ) + 1) :=
                mul_le_mul_of_nonneg_right (by linarith [Real.pi_gt_three]) (le_of_lt hN)
        have h1 : C₃ / (2 * Real.pi * ((N : ℝ) + 1)) ^ K ≤ C₃ / ((N : ℝ) + 1) ^ K :=
          div_le_div_of_nonneg_left hC₃nn (pow_pos hN K) hle
        calc C₂ * (C₃ / (2 * Real.pi * ((N : ℝ) + 1)) ^ K) ≤ C₂ * (C₃ / ((N : ℝ) + 1) ^ K) :=
              mul_le_mul_of_nonneg_left h1 hC₂nn
          _ = C₂ * C₃ / ((N : ℝ) + 1) ^ K := by ring

end Work.BoseBoxFock
