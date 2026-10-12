import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Real.Pi.Bounds
import Submission.Work.BoseRowQ2.chiHatSq_cubeCompl_shift_le
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Work.BoseBoxFock.chiHat_sq_cubeCompl_tail` — the Schwartz tail of `χ̂²` outside the cube

The corpus bump `χ = Submission.BoseGases.chi` is `C^∞` with compact support, so its cosine
transform `χ̂(p) = ∫ χ(x) cos⟪p,x⟫ dx` (`Work.BoseB4.BoxData.hatChi`) decays faster than any
polynomial (`Work.BoseK15.ChiReg_corpus`, FS `lem:DecaychiHat`).  This module records the
consequence used by the low-momentum sums of the `BoseBoxFock` chapter: for **every** power
`K` there is a constant `C ≥ 0` with

    `∑'_{n ∉ cube N} χ̂(2πn)² ≤ C / (N+1)^K`      for all `N`,

where `cube N = [-N,N]³ ∩ ℤ³` (`Work.BoseRowQ2.cube`) and `vec n = 2πn`.

The proof has two ingredients.

* **Geometry.**  A lattice point outside the cube has `‖vec n‖ ≥ 2π(N+1)`
  (`Work.BoseRowQ2.norm_vec_ge_of_notMem_cube`), so the complement of the cube sits inside the
  exterior of the ball of radius `R = 2π(N+1)`.
* **Analysis.**  At decay order `K+1`, `|χ̂(p)|(1+‖p‖²)^{K+1} ≤ Cchi` gives
  `χ̂(vec n)² ≤ Cchi²(1+‖vec n‖²)^{-2(K+1)}`, and the dyadic lattice tail estimate
  `Work.BoseK15.sum_inv_one_add_norm_tail (2(K+1)) K` (legal since `K+3 ≤ 4(K+1)`) bounds
  `∑ (1+‖vec n‖²)^{-2(K+1)}` by `Ctail/R^K`.

The finite-set bound is upgraded to the `tsum` over the complement of the cube by the standard
nonnegativity argument on the `ℝ≥0∞` side (`ENNReal.tsum_eq_iSup_sum`), and `R = 2π(N+1) ≥ N+1`
converts `R^{-K}` into `(N+1)^{-K}`.
-/

namespace Work.BoseBoxFock

open scoped BigOperators

/-- **From a finite lattice bound to the `tsum` outside the cube.**  If a nonnegative summand
`f : ℤ³ → ℝ` satisfies, for every `R ≥ 1`, the bound `∑_{n ∈ S} f n ≤ C/R^K` on every finite set
`S` of lattice indices with `‖vec n‖ ≥ R`, then the same bound holds for the `tsum` over the
lattice points outside the cube, with `R` replaced by `N+1`.

The cube complement is contained in the exterior of the ball of radius `2π(N+1)`, and the
`R = 2π(N+1) ≥ N+1` bookkeeping is elementary. -/
theorem tsum_cubeCompl_le_of_finset {K : ℕ} {f : (Fin 3 → ℤ) → ℝ} (hnn : ∀ n, 0 ≤ f n)
    {C : ℝ} (hC0 : 0 ≤ C)
    (hC : ∀ (R : ℝ) (S : Finset (Fin 3 → ℤ)), 1 ≤ R →
      (∀ n ∈ S, R ≤ ‖Work.BoseB4.vec n‖) → (∑ n ∈ S, f n) ≤ C / R ^ K)
    (N : ℕ) :
    (∑' n : {n : Fin 3 → ℤ // n ∉ Work.BoseRowQ2.cube N}, f n.val)
      ≤ C / ((N : ℝ) + 1) ^ K := by
  set R : ℝ := 2 * Real.pi * ((N : ℝ) + 1) with hRdef
  have hRpos : 0 < R := by
    rw [hRdef]
    have hπ : (0 : ℝ) < 2 * Real.pi := by linarith [Real.pi_gt_three]
    have hN : (0 : ℝ) < (N : ℝ) + 1 := by
      have : (0 : ℝ) ≤ (N : ℝ) := Nat.cast_nonneg N
      linarith
    positivity
  have hR1 : 1 ≤ R := by
    rw [hRdef]
    have h1 : (1 : ℝ) ≤ 2 * Real.pi := by linarith [Real.pi_gt_three]
    have h2 : (1 : ℝ) ≤ (N : ℝ) + 1 := by
      have : (0 : ℝ) ≤ (N : ℝ) := Nat.cast_nonneg N
      linarith
    calc (1 : ℝ) = 1 * 1 := by ring
      _ ≤ 2 * Real.pi * ((N : ℝ) + 1) := mul_le_mul h1 h2 (by norm_num) (by linarith)
  -- every finite partial sum over the complement obeys the bound
  have hfinite : ∀ s : Finset {n : Fin 3 → ℤ // n ∉ Work.BoseRowQ2.cube N},
      ∑ x ∈ s, f x.val ≤ C / R ^ K := by
    intro s
    have hS : ∀ n ∈ s.map (Function.Embedding.subtype
        (fun n : Fin 3 → ℤ => n ∉ Work.BoseRowQ2.cube N)), R ≤ ‖Work.BoseB4.vec n‖ := by
      intro n hn
      rw [Finset.mem_map] at hn
      obtain ⟨x, _hx, rfl⟩ := hn
      exact Work.BoseRowQ2.norm_vec_ge_of_notMem_cube x.2
    have h1 := hC R (s.map (Function.Embedding.subtype
      (fun n : Fin 3 → ℤ => n ∉ Work.BoseRowQ2.cube N))) hR1 hS
    rwa [Finset.sum_map] at h1
  have hB : 0 ≤ C / R ^ K := div_nonneg hC0 (pow_nonneg hRpos.le K)
  -- the `ℝ≥0∞` version: `tsum` is the supremum of the finite partial sums
  have hENN : (∑' x : {n : Fin 3 → ℤ // n ∉ Work.BoseRowQ2.cube N},
        ENNReal.ofReal (f x.val))
      ≤ ENNReal.ofReal (C / R ^ K) := by
    rw [ENNReal.tsum_eq_iSup_sum]
    refine iSup_le fun s => ?_
    rw [← ENNReal.ofReal_sum_of_nonneg (fun x _ => hnn x.val)]
    exact ENNReal.ofReal_le_ofReal (hfinite s)
  have hsummand : ∀ x : {n : Fin 3 → ℤ // n ∉ Work.BoseRowQ2.cube N},
      ENNReal.ofReal (f x.val) ≠ ⊤ := fun _ => ENNReal.ofReal_ne_top
  have hne : (∑' x : {n : Fin 3 → ℤ // n ∉ Work.BoseRowQ2.cube N},
      ENNReal.ofReal (f x.val)) ≠ ⊤ :=
    ne_top_of_le_ne_top ENNReal.ofReal_ne_top hENN
  -- back to `ℝ`
  have htoReal : (∑' x : {n : Fin 3 → ℤ // n ∉ Work.BoseRowQ2.cube N},
        ENNReal.ofReal (f x.val)).toReal
      = ∑' x : {n : Fin 3 → ℤ // n ∉ Work.BoseRowQ2.cube N}, f x.val := by
    rw [ENNReal.tsum_toReal_eq hsummand]
    exact tsum_congr fun x => ENNReal.toReal_ofReal (hnn x.val)
  have htsum : (∑' x : {n : Fin 3 → ℤ // n ∉ Work.BoseRowQ2.cube N}, f x.val)
      ≤ C / R ^ K := by
    calc (∑' x : {n : Fin 3 → ℤ // n ∉ Work.BoseRowQ2.cube N}, f x.val)
        = (∑' x : {n : Fin 3 → ℤ // n ∉ Work.BoseRowQ2.cube N},
            ENNReal.ofReal (f x.val)).toReal := htoReal.symm
      _ ≤ (ENNReal.ofReal (C / R ^ K)).toReal :=
          ENNReal.toReal_mono ENNReal.ofReal_ne_top hENN
      _ = C / R ^ K := ENNReal.toReal_ofReal hB
  -- `R = 2π(N+1) ≥ N+1` converts `R^{-K}` into `(N+1)^{-K}`
  have hbase : (0 : ℝ) ≤ (N : ℝ) + 1 := by
    have : (0 : ℝ) ≤ (N : ℝ) := Nat.cast_nonneg N
    linarith
  have hmono : ((N : ℝ) + 1) ^ K ≤ R ^ K :=
    pow_le_pow_left₀ hbase (by rw [hRdef]; nlinarith [Real.pi_gt_three]) K
  calc (∑' x : {n : Fin 3 → ℤ // n ∉ Work.BoseRowQ2.cube N}, f x.val)
      ≤ C / R ^ K := htsum
    _ ≤ C / ((N : ℝ) + 1) ^ K :=
        div_le_div_of_nonneg_left hC0 (by positivity) hmono

/-- **The `χ̂²`-tail outside the cube.**  For every power `K` there is `C ≥ 0` with

    `∑'_{n ∉ cube N} χ̂(2πn)² ≤ C/(N+1)^K`      for all `N : ℕ`.

The constant produced here is `Cchi²·Ctail`, from the decay order `K+1` of
`Work.BoseK15.ChiReg_corpus` and the lattice tail estimate
`Work.BoseK15.sum_inv_one_add_norm_tail (2(K+1)) K`. -/
theorem chiHat_sq_cubeCompl_tail (K : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ N : ℕ,
      (∑' n : {n : Fin 3 → ℤ // n ∉ Work.BoseRowQ2.cube N},
          (Work.BoseK15.corpusBox.hatChi (Work.BoseB4.vec n.val)) ^ 2)
        ≤ C / ((N : ℝ) + 1) ^ K := by
  -- the `χ̂`-decay at order `K+1` and the lattice tail estimate at `(2(K+1), K)`
  obtain ⟨Cchi, hCchi_nn, hChi, _⟩ := Work.BoseK15.ChiReg_corpus (K + 1)
  obtain ⟨Ctail, _hCtail_nn, hCtail⟩ :=
    Work.BoseK15.sum_inv_one_add_norm_tail (2 * (K + 1)) K (by omega)
  refine ⟨Cchi ^ 2 * Ctail, by positivity, fun N => ?_⟩
  refine tsum_cubeCompl_le_of_finset (K := K)
    (f := fun n : Fin 3 → ℤ => (Work.BoseK15.corpusBox.hatChi (Work.BoseB4.vec n)) ^ 2)
    (C := Cchi ^ 2 * Ctail) (fun n => sq_nonneg _) (by positivity) ?_ N
  intro R S hR hS
  -- the pointwise decay `χ̂(vec n)² ≤ Cchi²(1+‖vec n‖²)^{-2(K+1)}`
  have hpoint : ∀ n ∈ S, (Work.BoseK15.corpusBox.hatChi (Work.BoseB4.vec n)) ^ 2
      ≤ Cchi ^ 2 * (((1 : ℝ) + ‖Work.BoseB4.vec n‖ ^ 2) ^ (2 * (K + 1)))⁻¹ := by
    intro n _hn
    have hD : (0 : ℝ) < (1 + ‖Work.BoseB4.vec n‖ ^ 2) ^ (K + 1) := by positivity
    have hle : |Work.BoseK15.corpusBox.hatChi (Work.BoseB4.vec n)|
        ≤ Cchi / (1 + ‖Work.BoseB4.vec n‖ ^ 2) ^ (K + 1) := by
      rw [le_div_iff₀ hD]
      exact hChi (Work.BoseB4.vec n)
    have hK' : 0 ≤ Cchi / (1 + ‖Work.BoseB4.vec n‖ ^ 2) ^ (K + 1) :=
      div_nonneg hCchi_nn hD.le
    have hpow : (((1 : ℝ) + ‖Work.BoseB4.vec n‖ ^ 2) ^ (K + 1)) ^ 2
        = ((1 : ℝ) + ‖Work.BoseB4.vec n‖ ^ 2) ^ (2 * (K + 1)) := by
      rw [← pow_mul]
      ring_nf
    calc (Work.BoseK15.corpusBox.hatChi (Work.BoseB4.vec n)) ^ 2
        ≤ (Cchi / (1 + ‖Work.BoseB4.vec n‖ ^ 2) ^ (K + 1)) ^ 2 := by
          rw [sq_le_sq, abs_of_nonneg hK']; exact hle
      _ = Cchi ^ 2 * (((1 : ℝ) + ‖Work.BoseB4.vec n‖ ^ 2) ^ (2 * (K + 1)))⁻¹ := by
          rw [div_pow, div_eq_mul_inv, hpow]
  calc (∑ n ∈ S, (Work.BoseK15.corpusBox.hatChi (Work.BoseB4.vec n)) ^ 2)
      ≤ ∑ n ∈ S, Cchi ^ 2 * (((1 : ℝ) + ‖Work.BoseB4.vec n‖ ^ 2) ^ (2 * (K + 1)))⁻¹ :=
        Finset.sum_le_sum hpoint
    _ = Cchi ^ 2 * ∑ n ∈ S, (((1 : ℝ) + ‖Work.BoseB4.vec n‖ ^ 2) ^ (2 * (K + 1)))⁻¹ := by
        rw [Finset.mul_sum]
    _ ≤ Cchi ^ 2 * (Ctail / R ^ K) :=
        mul_le_mul_of_nonneg_left (hCtail R S hR hS) (by positivity)
    _ = (Cchi ^ 2 * Ctail) / R ^ K := by ring

end Work.BoseBoxFock
