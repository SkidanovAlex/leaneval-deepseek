import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Algebra.Order.Star.Real
import Submission.Work.BoseRowQ2.chatTail_eq_highMode
import Submission.Work.BoseRowQ2.chiHatSq_cubeCompl_shift_le
import Submission.Work.BoseRowQ2.chiHat_cubeCompl_shift_le
import Submission.Work.BoseRowQ2.highErr_sq_sum_le_nu_sq
import Submission.Work.BoseRowQ2.highMode_eq_ideal_sub_err
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Work.BoseRowQ2.chatTail_quad_le` — the quadratic form of the lattice-tail matrix `Tail`

The mask row of FS l.3253 needs the quadratic form of the *lattice-tail* matrix

    `Tail N i j = Mc N i j − ∑_k Chat N k i · Chat N k j`

on the vector `c = Chat w` (`c k = ∑_i χ̂(vec (K k − K i)) w i`) to be small — of the order
`card / R^101` with `R = 2π(N+1) − L`, `L` a bound for the momenta in the support of `w`:

    `∑_{k,j} c k c j · Tail N k j ≤ D · card (Lab N) / R^101 · ∑_i w i²`.

## The proof

Three ingredients, each proved in the sibling modules:

1. **the high-mode identity** (`Work.BoseRowQ2.chatTail_eq_highMode`): the quadratic form equals
   `∑_{m ∉ cube N} (highMode N w m)²`, where `highMode N w m = ∑_k c k χ̂(vec (m − K k))` is the
   `m`-th Fourier coefficient of `χ·(low part of χW)`;
2. **the coefficient decomposition** (`Work.BoseRowQ2.highMode_eq_ideal_sub_err`):
   `highMode = highIdeal − highErr`, where `highIdeal N w m = ∑_i w i χ̂²(vec (m − K i))` is the
   ideal coefficient `(χ²W)^m` and `highErr` is the truncation error (the part of the lattice
   sum over the modes *outside* the cube);
3. **the two tails** (`Work.BoseRowQ2.highIdeal_sq_tail_le`, `…nu_sq_le`,
   `…highErr_sq_sum_le_nu_sq`): `highIdeal` is bounded by the shifted `χ̂²`-tail, and `highErr`
   by the square of the `ℓ¹`-mass `nu`, which is bounded by the shifted `|χ̂|`-tail — both of
   which decay like `R^{-101}` (Schwartz decay of `χ̂` at order 52 and the lattice sums of
   `Work.BoseK15`).

The arithmetic of the assembly is the elementary `(a − b)² ≤ 2a² + 2b²`, the summability of the
three lattice families (Parseval-type, from `Work.BoseRowQ2.summable_highIdeal_sq`,
`…summable_highMode_sq` and the decomposition), and the two tail constants.
-/

noncomputable section

open scoped BigOperators

namespace Work.BoseRowQ2

open Work.BoseBoxFock

local notation "Z3" => Fin 3 → ℤ

theorem chatTail_quad_le :
    ∃ D : ℝ, 0 ≤ D ∧ ∀ (N : ℕ) (L : ℝ), 0 ≤ L →
      1 ≤ 2 * Real.pi * ((N : ℝ) + 1) - L →
      ∀ (w : Work.BoseBoxFock.Lab N → ℝ),
        (∀ i, w i ≠ 0 → ‖Work.BoseB4.vec (Work.BoseBoxFock.labVec N i)‖ ≤ L) →
      (∑ k : Work.BoseBoxFock.Lab N, ∑ j : Work.BoseBoxFock.Lab N,
          (∑ i : Work.BoseBoxFock.Lab N, Work.BoseRowQ2.Chat N k i * w i)
            * (∑ i : Work.BoseBoxFock.Lab N, Work.BoseRowQ2.Chat N j i * w i)
            * Work.BoseRowQ2.Tail N k j)
        ≤ D * (Fintype.card (Work.BoseBoxFock.Lab N) : ℝ)
            / (2 * Real.pi * ((N : ℝ) + 1) - L) ^ 101 * ∑ i : Work.BoseBoxFock.Lab N, w i ^ 2 := by
  obtain ⟨C₁, hC₁, hTail⟩ := chiHatSq_cubeCompl_shift_le
  obtain ⟨C₂, hC₂, hAbs⟩ := chiHat_cubeCompl_shift_le
  refine ⟨2 * C₁ + 2 * C₂ ^ 2, by positivity, ?_⟩
  intro N L hL hR w hw
  have hR' : 1 ≤ rad N L := hR
  change (∑ k : Work.BoseBoxFock.Lab N, ∑ j : Work.BoseBoxFock.Lab N,
        ChatW N w k * ChatW N w j * Tail N k j)
      ≤ (2 * C₁ + 2 * C₂ ^ 2) * (Fintype.card (Work.BoseBoxFock.Lab N) : ℝ)
          / rad N L ^ 101 * ∑ i : Work.BoseBoxFock.Lab N, w i ^ 2
  rw [chatTail_eq_highMode N w]
  -- the pointwise decomposition and the `(a − b)² ≤ 2a² + 2b²` split
  have hdecomp : ∀ m : {m : Z3 // m ∉ cube N},
      highMode N w m.val = highIdeal N w m.val - highErr N w m.val :=
    fun m => highMode_eq_ideal_sub_err N w m.val
  have hsum_fa : Summable (fun m : {m : Z3 // m ∉ cube N} => highIdeal N w m.val ^ 2) :=
    summable_highIdeal_sq N w
  have hsum_fm : Summable (fun m : {m : Z3 // m ∉ cube N} => highMode N w m.val ^ 2) :=
    summable_highMode_sq N w
  have hsum_fb : Summable (fun m : {m : Z3 // m ∉ cube N} => highErr N w m.val ^ 2) := by
    refine Summable.of_nonneg_of_le (fun m => sq_nonneg _) (fun m => ?_)
      ((hsum_fa.mul_left 2).add (hsum_fm.mul_left 2))
    have h := hdecomp m
    have heq : highErr N w m.val = highIdeal N w m.val - highMode N w m.val := by linarith [h]
    rw [heq]
    nlinarith [sq_nonneg (highIdeal N w m.val + highMode N w m.val)]
  have hpt : ∀ m : {m : Z3 // m ∉ cube N}, highMode N w m.val ^ 2
      ≤ 2 * highIdeal N w m.val ^ 2 + 2 * highErr N w m.val ^ 2 := by
    intro m
    rw [hdecomp m]
    nlinarith [sq_nonneg (highIdeal N w m.val + highErr N w m.val)]
  have hsplit : (∑' m : {m : Z3 // m ∉ cube N}, highMode N w m.val ^ 2)
      ≤ 2 * (∑' m : {m : Z3 // m ∉ cube N}, highIdeal N w m.val ^ 2)
        + 2 * (∑' m : {m : Z3 // m ∉ cube N}, highErr N w m.val ^ 2) := by
    have h1 : (∑' m : {m : Z3 // m ∉ cube N}, highMode N w m.val ^ 2)
        ≤ ∑' m : {m : Z3 // m ∉ cube N},
            (2 * highIdeal N w m.val ^ 2 + 2 * highErr N w m.val ^ 2) :=
      Summable.tsum_le_tsum hpt hsum_fm ((hsum_fa.mul_left 2).add (hsum_fb.mul_left 2))
    rw [Summable.tsum_add (hsum_fa.mul_left 2) (hsum_fb.mul_left 2), tsum_mul_left,
      tsum_mul_left] at h1
    linarith
  -- the two tail bounds
  have hA := highIdeal_sq_tail_le hC₁ hTail N L w hL hR' hw
  have hB := nu_sq_le hC₂ hAbs N L w hL hR' hw
  have hCerr := highErr_sq_sum_le_nu_sq N w
  calc (∑' m : {m : Z3 // m ∉ cube N}, highMode N w m.val ^ 2)
      ≤ 2 * (∑' m : {m : Z3 // m ∉ cube N}, highIdeal N w m.val ^ 2)
        + 2 * (∑' m : {m : Z3 // m ∉ cube N}, highErr N w m.val ^ 2) := hsplit
    _ ≤ 2 * (C₁ * (Fintype.card (Work.BoseBoxFock.Lab N) : ℝ) / rad N L ^ 101
          * ∑ i : Work.BoseBoxFock.Lab N, w i ^ 2)
        + 2 * (C₂ ^ 2 * (Fintype.card (Work.BoseBoxFock.Lab N) : ℝ) / rad N L ^ 101
          * ∑ i : Work.BoseBoxFock.Lab N, w i ^ 2) := by
        refine add_le_add (mul_le_mul_of_nonneg_left hA (by norm_num))
          (mul_le_mul_of_nonneg_left (le_trans hCerr hB) (by norm_num))
    _ = (2 * C₁ + 2 * C₂ ^ 2) * (Fintype.card (Work.BoseBoxFock.Lab N) : ℝ)
          / rad N L ^ 101 * ∑ i : Work.BoseBoxFock.Lab N, w i ^ 2 := by ring

end Work.BoseRowQ2
