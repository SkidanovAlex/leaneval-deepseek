import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Real.Pi.Bounds
import Submission.Work.BoseRowQ2.chiHat_cubeCompl_shift_le
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Work.BoseBoxFock.chiHat_abs_cubeCompl_tail` — the `|χ̂|`-sum outside the cube at *arbitrary* decay

The sibling `Work.BoseRowQ2.chiHat_cubeCompl_shift_le` bounds the shifted `|χ̂|`-tail outside
the lattice cube `cube N = [-N,N]³ ∩ ℤ³` at the **fixed** rate `rad N L ^ (-101)`.  The row
that consumes it (FS l.3253) needs the rate to be *arbitrary*: the target here is

    `∑'_{n ∉ cube N} |χ̂(vec n)| ≤ C / (N+1)^K`      for every `K`,

with `C` allowed to depend on `K`.

The mathematics is unchanged — the corpus bump `χ` is `C^∞` with compact support, so
`lem:DecaychiHat` (`Work.BoseK15.ChiReg_corpus`) holds at **every** order `s`, and the dyadic
lattice count `Work.BoseK15.sum_inv_one_add_norm_tail s M` converts order `s` into the rate
`M` as soon as `M + 3 ≤ 2s`.  Taking `s = K + 3` therefore produces the rate `K` (the case
`K ≤ 101` is also covered, with a larger constant).

Two bricks are proved here, both transcribed from
`Work.BoseRowQ2/chiHat_cubeCompl_shift_le.lean` with `101` replaced by a parameter `M`:

* `chiHat_abs_finset_tail_sum_gen M` — the *finite-set* tail bound at rate `M`
  (`ChiReg_corpus (M+3)` + `sum_inv_one_add_norm_tail (M+3) M`);
* `tsum_compl_le_of_finset` — the passage from the finite-set bound to the `tsum` over the
  subtype `{m // m ∉ cube N}`, via the standard nonnegativity argument in `ℝ≥0∞`, together with
  the geometric input `rad_le_norm_vec_sub` (a lattice point outside `cube N` shifted by
  `‖vec i‖ ≤ L` has momentum at least `rad N L = 2π(N+1) − L`).

The target then follows with `L = 0`, `i = 0`: `rad N 0 = 2π(N+1) ≥ N+1`, and the rate-`M`
bound only improves when the base is enlarged from `2π(N+1)` to `N+1`.
-/

noncomputable section

open scoped BigOperators

namespace Work.BoseBoxFock

local notation "Z3" => Fin 3 → ℤ

/-! ## 1. The finite-set `|χ̂|`-tail at an arbitrary rate -/

/-- **The finite-set `|χ̂|`-tail of the corpus bump, at an arbitrary rate `M`.**  There is a
constant `C ≥ 0` such that for every `R ≥ 1` and every finite set `S` of lattice indices whose
momenta `vec n = 2πn` all have norm at least `R`, the sum of `|χ̂(vec n)|` over `S` is at most
`C/R^M`.

Proof: `ChiReg_corpus (M+3)` gives `|χ̂(p)|·(1+‖p‖²)^(M+3) ≤ Cchi` (its *first* conjunct), i.e.
`|χ̂(vec n)| ≤ Cchi·(1+‖vec n‖²)^{-(M+3)}`; summing over `S` and applying the lattice tail
estimate `sum_inv_one_add_norm_tail (M+3) M` (legal since `M + 3 ≤ 2·(M+3)`) gives the claim
with `C = Cchi·Ctail`. -/
theorem chiHat_abs_finset_tail_sum_gen (M : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (R : ℝ) (S : Finset Z3), 1 ≤ R →
      (∀ n ∈ S, R ≤ ‖Work.BoseB4.vec n‖) →
      (∑ n ∈ S, |Work.BoseRowQ2.chiHat (Work.BoseB4.vec n)|) ≤ C / R ^ M := by
  obtain ⟨Cchi, hCchi_nn, hChi, _⟩ := Work.BoseK15.ChiReg_corpus (M + 3)
  obtain ⟨Ctail, _hCtail_nn, hCtail⟩ :=
    Work.BoseK15.sum_inv_one_add_norm_tail (M + 3) M (by omega)
  refine ⟨Cchi * Ctail, by positivity, ?_⟩
  intro R S hR hS
  have hpoint : ∀ n ∈ S, |Work.BoseRowQ2.chiHat (Work.BoseB4.vec n)|
      ≤ Cchi * (((1 : ℝ) + ‖Work.BoseB4.vec n‖ ^ 2) ^ (M + 3))⁻¹ := by
    intro n _hn
    have hD : (0 : ℝ) < (1 + ‖Work.BoseB4.vec n‖ ^ 2) ^ (M + 3) := by positivity
    have hle : |Work.BoseRowQ2.chiHat (Work.BoseB4.vec n)|
        ≤ Cchi / (1 + ‖Work.BoseB4.vec n‖ ^ 2) ^ (M + 3) := by
      rw [le_div_iff₀ hD]
      simpa only [Work.BoseRowQ2.chiHat] using hChi (Work.BoseB4.vec n)
    simpa only [div_eq_mul_inv] using hle
  calc (∑ n ∈ S, |Work.BoseRowQ2.chiHat (Work.BoseB4.vec n)|)
      ≤ ∑ n ∈ S, Cchi * (((1 : ℝ) + ‖Work.BoseB4.vec n‖ ^ 2) ^ (M + 3))⁻¹ :=
        Finset.sum_le_sum hpoint
    _ = Cchi * ∑ n ∈ S, (((1 : ℝ) + ‖Work.BoseB4.vec n‖ ^ 2) ^ (M + 3))⁻¹ := by
        rw [Finset.mul_sum]
    _ ≤ Cchi * (Ctail / R ^ M) :=
        mul_le_mul_of_nonneg_left (hCtail R S hR hS) hCchi_nn
    _ = (Cchi * Ctail) / R ^ M := by ring

/-! ## 2. From the finite-set bound to the `tsum` over the cube complement -/

/-- **The `tsum` passage at an arbitrary rate.**  If a *nonnegative* summand `f : ℤ³ → ℝ`
satisfies the finite-set tail bound `∑_S f ≤ C/R^M` for every finite set `S` of lattice
indices whose momenta all have norm at least `R ≥ 1`, then the shifted `tsum` over the cube
complement obeys the same bound with `R = rad N L`:

    `∑'_{m ∉ cube N} f (m − i) ≤ C / rad N L ^ M`       whenever `‖vec i‖ ≤ L`.

The shift is free because `m ∉ cube N` and `‖vec i‖ ≤ L` give
`rad N L ≤ ‖vec (m − i)‖` (`Work.BoseRowQ2.rad_le_norm_vec_sub`).  The passage to the subtype
`tsum` is the standard nonnegativity argument in `ℝ≥0∞` (the template is
`Submission/Work/BoseRowQ2/chiHatSq_tsum_le.lean`). -/
theorem tsum_compl_le_of_finset (M : ℕ) {f : Z3 → ℝ} (hnn : ∀ n, 0 ≤ f n) {C : ℝ}
    (hC0 : 0 ≤ C)
    (hC : ∀ (R : ℝ) (S : Finset Z3), 1 ≤ R →
      (∀ n ∈ S, R ≤ ‖Work.BoseB4.vec n‖) → (∑ n ∈ S, f n) ≤ C / R ^ M)
    (N : ℕ) (L : ℝ) (i : Z3) (hR : 1 ≤ Work.BoseRowQ2.rad N L)
    (hi : ‖Work.BoseB4.vec i‖ ≤ L) :
    (∑' m : {m : Z3 // m ∉ Work.BoseRowQ2.cube N}, f (m.val - i))
      ≤ C / Work.BoseRowQ2.rad N L ^ M := by
  have hRpos : 0 < Work.BoseRowQ2.rad N L := lt_of_lt_of_le zero_lt_one hR
  have hB : 0 ≤ C / Work.BoseRowQ2.rad N L ^ M := div_nonneg hC0 (pow_pos hRpos M).le
  -- every finite partial sum of the subtype `tsum` obeys the finite-set tail bound
  have hfin : ∀ s : Finset {m : Z3 // m ∉ Work.BoseRowQ2.cube N},
      ∑ m ∈ s, f (m.val - i) ≤ C / Work.BoseRowQ2.rad N L ^ M := by
    intro s
    have hinj : ∀ x ∈ s, ∀ y ∈ s, x.val - i = y.val - i → x = y := by
      intro x _hx y _hy hxy
      refine Subtype.ext (funext fun j => ?_)
      have h : x.val j - i j = y.val j - i j := congrFun hxy j
      omega
    have hsum : ∑ m ∈ s, f (m.val - i)
        = ∑ n ∈ s.image (fun m : {m : Z3 // m ∉ Work.BoseRowQ2.cube N} => m.val - i), f n := by
      rw [Finset.sum_image hinj]
    rw [hsum]
    refine hC (Work.BoseRowQ2.rad N L) _ hR ?_
    intro n hn
    obtain ⟨m, _hm, rfl⟩ := Finset.mem_image.mp hn
    exact Work.BoseRowQ2.rad_le_norm_vec_sub m.2 hi
  -- pass to the `ℝ≥0∞` `tsum`: it is the supremum of the finite partial sums
  have hENN : (∑' m : {m : Z3 // m ∉ Work.BoseRowQ2.cube N},
        ENNReal.ofReal (f (m.val - i)))
      ≤ ENNReal.ofReal (C / Work.BoseRowQ2.rad N L ^ M) := by
    rw [ENNReal.tsum_eq_iSup_sum]
    refine iSup_le fun s => ?_
    rw [← ENNReal.ofReal_sum_of_nonneg (fun m _ => hnn _)]
    exact ENNReal.ofReal_le_ofReal (hfin s)
  have hne : (∑' m : {m : Z3 // m ∉ Work.BoseRowQ2.cube N},
      ENNReal.ofReal (f (m.val - i))) ≠ ⊤ :=
    ne_top_of_le_ne_top ENNReal.ofReal_ne_top hENN
  have htoReal : (∑' m : {m : Z3 // m ∉ Work.BoseRowQ2.cube N},
        ENNReal.ofReal (f (m.val - i))).toReal
      = ∑' m : {m : Z3 // m ∉ Work.BoseRowQ2.cube N}, f (m.val - i) := by
    rw [ENNReal.tsum_toReal_eq (fun m => ENNReal.ofReal_ne_top)]
    exact tsum_congr fun m => ENNReal.toReal_ofReal (hnn _)
  calc (∑' m : {m : Z3 // m ∉ Work.BoseRowQ2.cube N}, f (m.val - i))
      = (∑' m : {m : Z3 // m ∉ Work.BoseRowQ2.cube N},
          ENNReal.ofReal (f (m.val - i))).toReal := htoReal.symm
    _ ≤ (ENNReal.ofReal (C / Work.BoseRowQ2.rad N L ^ M)).toReal :=
        ENNReal.toReal_mono ENNReal.ofReal_ne_top hENN
    _ = C / Work.BoseRowQ2.rad N L ^ M := ENNReal.toReal_ofReal hB

/-! ## 3. The target -/

/-- **The `|χ̂|`-sum outside the lattice cube decays at every rate.**  For every `K : ℕ` there
is `C ≥ 0` with

    `∑'_{n ∉ cube N} |χ̂(vec n)| ≤ C / (N+1)^K`      for all `N`.

Take `M = K` in `chiHat_abs_finset_tail_sum_gen` and apply `tsum_compl_le_of_finset` with
`L = i = 0` (so `rad N 0 = 2π(N+1) ≥ 1`); since `2π(N+1) ≥ N+1` the bound only improves when
the base is replaced by `N+1`. -/
theorem chiHat_abs_cubeCompl_tail (K : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ N : ℕ,
      (∑' n : {n : Fin 3 → ℤ // n ∉ Work.BoseRowQ2.cube N},
          |Work.BoseK15.corpusBox.hatChi (Work.BoseB4.vec n.val)|)
        ≤ C / ((N : ℝ) + 1) ^ K := by
  obtain ⟨C, hC0, hC⟩ := chiHat_abs_finset_tail_sum_gen K
  refine ⟨C, hC0, fun N => ?_⟩
  -- `rad N 0 = 2π(N+1) ≥ 1`, so the passage lemma applies with `L = i = 0`
  have hrad1 : 1 ≤ Work.BoseRowQ2.rad N 0 := by
    rw [show Work.BoseRowQ2.rad N 0 = 2 * Real.pi * ((N : ℝ) + 1) by
      simp [Work.BoseRowQ2.rad]]
    have hN : (1 : ℝ) ≤ (N : ℝ) + 1 := by
      have h : (0 : ℝ) ≤ (N : ℝ) := Nat.cast_nonneg N
      linarith
    nlinarith [Real.pi_gt_three]
  have hi : ‖Work.BoseB4.vec (0 : Z3)‖ ≤ (0 : ℝ) := by
    have hv : Work.BoseB4.vec (0 : Z3) = 0 := by ext i; simp [Work.BoseB4.vec]
    rw [hv]; simp
  have hmain := tsum_compl_le_of_finset K (f := fun n : Z3 =>
      |Work.BoseRowQ2.chiHat (Work.BoseB4.vec n)|) (fun n => abs_nonneg _) hC0 hC
    N 0 0 hrad1 hi
  -- identify the two `tsum`s (`chiHat` *is* the corpus `χ̂`, and `m − 0 = m`)
  have heq : (∑' n : {n : Z3 // n ∉ Work.BoseRowQ2.cube N},
        |Work.BoseK15.corpusBox.hatChi (Work.BoseB4.vec n.val)|)
      = (∑' m : {m : Z3 // m ∉ Work.BoseRowQ2.cube N},
          |Work.BoseRowQ2.chiHat (Work.BoseB4.vec (m.val - 0))|) := by
    refine tsum_congr fun n => ?_
    simp [Work.BoseRowQ2.chiHat]
  rw [heq]
  -- replace the base `2π(N+1)` by `N+1`
  refine le_trans hmain ?_
  rw [show Work.BoseRowQ2.rad N 0 = 2 * Real.pi * ((N : ℝ) + 1) by
    simp [Work.BoseRowQ2.rad]]
  have h1 : (0 : ℝ) < (N : ℝ) + 1 := by positivity
  have hge : ((N : ℝ) + 1) ≤ 2 * Real.pi * ((N : ℝ) + 1) := by
    have h2 : (1 : ℝ) ≤ 2 * Real.pi := by linarith [Real.pi_gt_three]
    nlinarith
  rw [div_eq_mul_inv, div_eq_mul_inv]
  refine mul_le_mul_of_nonneg_left ?_ hC0
  simpa [one_div] using one_div_le_one_div_of_le (pow_pos h1 K)
    (pow_le_pow_left₀ h1.le hge K)

end Work.BoseBoxFock
