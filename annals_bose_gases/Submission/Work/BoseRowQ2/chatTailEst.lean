import Mathlib.Algebra.Order.Chebyshev
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Algebra.Order.Star.Real
import Submission.Work.BoseRowQ2.chatTailAux
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Work.BoseRowQ2.chatTailEst` — the two halves of the `Tail`-quadratic-form estimate

This module proves the estimates that turn the *high-mode identity*
(`Work.BoseRowQ2.chatTail_eq_highMode`)

    `∑_{k,j} (Chat w) k (Chat w) j · Tail N k j = ∑_{m ∉ cube N} highMode N w m ^ 2`

and the *coefficient decomposition* (`Work.BoseRowQ2.highMode_eq_ideal_sub_err`)

    `highMode N w m = highIdeal N w m − highErr N w m`

into the target bound.  The two halves are

* `highIdeal` (the ideal high-mode coefficient `(χ²W)^m`) — bounded by the shifted `χ̂²`-tail
  (`Work.BoseRowQ2.chiHatSq_cubeCompl_shift_le`, quantified here as the hypothesis `hTail`);
* `highErr` (the truncation error) — bounded by `Work.BoseRowQ2.highErr_sq_sum_le_nu_sq`, whose
  right side is the `ℓ¹`-mass `nu` of the high part of `F̂`, bounded here by the shifted
  `|χ̂|`-tail (`Work.BoseRowQ2.chiHat_cubeCompl_shift_le`, the hypothesis `hAbs`).

The mathematical content of the two estimates is Cauchy–Schwarz — restricted to the support of
`w` in the case of `highIdeal`, so that the *shifted* tail bound (which needs `‖vec (K i)‖ ≤ L`
for every contributing `i`) applies — plus the Parseval-type summability of the lattice
families, which is obtained from the Schwartz decay `ChiReg_corpus` and the lattice sums of
`Work.BoseK15.sum_inv_one_add_norm_le` via `summable_of_sum_le`.
-/

noncomputable section

open scoped BigOperators

namespace Work.BoseRowQ2

open Work.BoseBoxFock

local notation "Z3" => Fin 3 → ℤ

/-! ## 0. Summability of the lattice families -/

/-- The lattice majorant `((1 + ‖vec n‖²)^s)^{-1}` is summable for `3 < 2s`. -/
theorem summable_inv_pow (s : ℕ) (hs : 3 < 2 * s) :
    Summable (fun n : Z3 => (((1 : ℝ) + ‖Work.BoseB4.vec n‖ ^ 2) ^ s)⁻¹) := by
  obtain ⟨C, _hC, hsum⟩ := Work.BoseK15.sum_inv_one_add_norm_le s hs
  exact summable_of_sum_le (fun n => by positivity) (fun S => hsum S)

/-- A lattice family dominated by a Schwartz majorant of order `s` is summable. -/
theorem summable_of_decay {f : Z3 → ℝ} {s : ℕ} (hs : 3 < 2 * s) {K : ℝ} (hK : 0 ≤ K)
    (h : ∀ n : Z3, |f n| ≤ K * (((1 : ℝ) + ‖Work.BoseB4.vec n‖ ^ 2) ^ s)⁻¹) :
    Summable f := by
  refine Summable.of_norm ?_
  refine Summable.of_nonneg_of_le (fun n => norm_nonneg _) (fun n => ?_)
    ((summable_inv_pow s hs).mul_left K)
  rw [Real.norm_eq_abs]
  exact h n

/-- The scalar core of the two decay lemmas: `(K/(1+‖p‖²)^52)² = K²·((1+‖p‖²)^104)^{-1}`. -/
private theorem sq_decay (K : ℝ) (p : EuclideanSpace ℝ (Fin 3)) :
    (K / (1 + ‖p‖ ^ 2) ^ 52) ^ 2 = K ^ 2 * (((1 : ℝ) + ‖p‖ ^ 2) ^ 104)⁻¹ := by
  rw [div_pow, div_eq_mul_inv, ← pow_mul]

/-- The lattice family `χ̂(vec n)²` is summable (χ̂ = the cosine transform of the corpus `χ`). -/
theorem summable_chiHat_sq : Summable (fun n : Z3 => chiHat (Work.BoseB4.vec n) ^ 2) := by
  obtain ⟨K, hK, hdec, _⟩ := Work.BoseK15.ChiReg_corpus 52
  refine summable_of_decay (s := 104) (by norm_num) (K := K ^ 2) (by positivity) fun n => ?_
  have hden : (0 : ℝ) < (1 + ‖Work.BoseB4.vec n‖ ^ 2) ^ 52 := by positivity
  have hle : |chiHat (Work.BoseB4.vec n)| ≤ K / (1 + ‖Work.BoseB4.vec n‖ ^ 2) ^ 52 := by
    rw [le_div_iff₀ hden]
    simpa [chiHat] using hdec (Work.BoseB4.vec n)
  calc |chiHat (Work.BoseB4.vec n) ^ 2| = |chiHat (Work.BoseB4.vec n)| ^ 2 := by
        rw [abs_of_nonneg (sq_nonneg _), sq_abs]
    _ ≤ (K / (1 + ‖Work.BoseB4.vec n‖ ^ 2) ^ 52) ^ 2 := by
        rw [sq_le_sq, abs_abs, abs_of_nonneg (div_nonneg hK hden.le)]
        exact hle
    _ = K ^ 2 * (((1 : ℝ) + ‖Work.BoseB4.vec n‖ ^ 2) ^ 104)⁻¹ := sq_decay K _

/-- The lattice family `χ̂²(vec n)²` is summable (χ̂² = the cosine transform of `χ²`). -/
theorem summable_chiHatSq_sq : Summable (fun n : Z3 => chiHatSq (Work.BoseB4.vec n) ^ 2) := by
  obtain ⟨K, hK, _, hdec⟩ := Work.BoseK15.ChiReg_corpus 52
  refine summable_of_decay (s := 104) (by norm_num) (K := K ^ 2) (by positivity) fun n => ?_
  have hden : (0 : ℝ) < (1 + ‖Work.BoseB4.vec n‖ ^ 2) ^ 52 := by positivity
  have hle : |chiHatSq (Work.BoseB4.vec n)| ≤ K / (1 + ‖Work.BoseB4.vec n‖ ^ 2) ^ 52 := by
    rw [le_div_iff₀ hden]
    simpa [chiHatSq] using hdec (Work.BoseB4.vec n)
  calc |chiHatSq (Work.BoseB4.vec n) ^ 2| = |chiHatSq (Work.BoseB4.vec n)| ^ 2 := by
        rw [abs_of_nonneg (sq_nonneg _), sq_abs]
    _ ≤ (K / (1 + ‖Work.BoseB4.vec n‖ ^ 2) ^ 52) ^ 2 := by
        rw [sq_le_sq, abs_abs, abs_of_nonneg (div_nonneg hK hden.le)]
        exact hle
    _ = K ^ 2 * (((1 : ℝ) + ‖Work.BoseB4.vec n‖ ^ 2) ^ 104)⁻¹ := sq_decay K _

/-- The lattice family `|χ̂(vec n)|` is summable. -/
theorem summable_chiHat_abs : Summable (fun n : Z3 => |chiHat (Work.BoseB4.vec n)|) := by
  obtain ⟨K, hK, hdec, _⟩ := Work.BoseK15.ChiReg_corpus 52
  refine summable_of_decay (s := 52) (by norm_num) (K := K) hK fun n => ?_
  have hden : (0 : ℝ) < (1 + ‖Work.BoseB4.vec n‖ ^ 2) ^ 52 := by positivity
  have hle : |chiHat (Work.BoseB4.vec n)| ≤ K / (1 + ‖Work.BoseB4.vec n‖ ^ 2) ^ 52 := by
    rw [le_div_iff₀ hden]
    simpa [chiHat] using hdec (Work.BoseB4.vec n)
  rw [abs_abs]
  simpa [div_eq_mul_inv] using hle

/-- Shifted summability: `m ↦ χ̂²(vec (m − k))²` is summable. -/
theorem summable_chiHatSq_sq_shift (k : Z3) :
    Summable (fun m : Z3 => chiHatSq (Work.BoseB4.vec (m - k)) ^ 2) :=
  (Equiv.summable_iff (f := fun n : Z3 => chiHatSq (Work.BoseB4.vec n) ^ 2)
    (Equiv.subRight k)).mpr summable_chiHatSq_sq

/-- Shifted summability: `m ↦ χ̂(vec (m − k))²` is summable. -/
theorem summable_chiHat_sq_shift (k : Z3) :
    Summable (fun m : Z3 => chiHat (Work.BoseB4.vec (m - k)) ^ 2) :=
  (Equiv.summable_iff (f := fun n : Z3 => chiHat (Work.BoseB4.vec n) ^ 2)
    (Equiv.subRight k)).mpr summable_chiHat_sq

/-- Shifted summability: `m ↦ |χ̂(vec (m − k))|` is summable. -/
theorem summable_chiHat_abs_shift (k : Z3) :
    Summable (fun m : Z3 => |chiHat (Work.BoseB4.vec (m - k))|) :=
  (Equiv.summable_iff (f := fun n : Z3 => |chiHat (Work.BoseB4.vec n)|)
    (Equiv.subRight k)).mpr summable_chiHat_abs

/-! ## 1. The `highIdeal` half -/

/-- **The pointwise Cauchy–Schwarz bound behind `highIdeal_sq_tail_le`**, restricted to the
support of `w` (so that the shifted tail bounds apply to every contributing label). -/
theorem highIdeal_sq_le (N : ℕ) (w : Lab N → ℝ) (m : {m : Z3 // m ∉ cube N}) :
    highIdeal N w m.val ^ 2 ≤ (∑ i : Lab N, w i ^ 2)
      * ∑ i ∈ suppW N w, chiHatSq (Work.BoseB4.vec (m.val - labVec N i)) ^ 2 := by
  have hSmem : ∀ i : Lab N, i ∈ suppW N w ↔ w i ≠ 0 := by
    intro i
    rw [suppW, Finset.mem_filter]
    simp
  have hsub : (∑ i : Lab N, w i * chiHatSq (Work.BoseB4.vec (m.val - labVec N i)))
      = ∑ i ∈ suppW N w, w i * chiHatSq (Work.BoseB4.vec (m.val - labVec N i)) := by
    refine (Finset.sum_subset (Finset.filter_subset _ _) ?_).symm
    intro i _ hi
    have hwi : w i = 0 := by
      by_contra hne
      exact hi ((hSmem i).mpr hne)
    rw [hwi, zero_mul]
  have hcs := Finset.sum_mul_sq_le_sq_mul_sq (suppW N w) w
    (fun i => chiHatSq (Work.BoseB4.vec (m.val - labVec N i)))
  have hwle : (∑ i ∈ suppW N w, w i ^ 2) ≤ ∑ i : Lab N, w i ^ 2 :=
    Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
      (fun i _ _ => sq_nonneg _)
  rw [highIdeal, hsub]
  exact le_trans hcs (mul_le_mul_of_nonneg_right hwle (by positivity))

/-- `m ↦ highIdeal N w m ^ 2` is summable. -/
theorem summable_highIdeal_sq (N : ℕ) (w : Lab N → ℝ) :
    Summable (fun m : {m : Z3 // m ∉ cube N} => highIdeal N w m.val ^ 2) := by
  have hSumA : ∀ i : Lab N, Summable (fun m : {m : Z3 // m ∉ cube N} =>
      chiHatSq (Work.BoseB4.vec (m.val - labVec N i)) ^ 2) :=
    fun i => (summable_chiHatSq_sq_shift (labVec N i)).subtype _
  have hSumg : Summable (fun m : {m : Z3 // m ∉ cube N} =>
      ∑ i ∈ suppW N w, chiHatSq (Work.BoseB4.vec (m.val - labVec N i)) ^ 2) :=
    summable_sum (fun i _ => hSumA i)
  exact Summable.of_nonneg_of_le (fun m => sq_nonneg _)
    (fun m => highIdeal_sq_le N w m) (hSumg.mul_left _)

/-- **The pointwise Cauchy–Schwarz bound for `highMode`**: `highMode N w m` is the finite sum
`∑_k ChatW N w k · χ̂(vec (m − K k))`, so its square is bounded by
`(∑_k (ChatW N w k)²)·(∑_k χ̂(vec (m − K k))²)`. -/
theorem highMode_sq_le (N : ℕ) (w : Lab N → ℝ) (m : {m : Z3 // m ∉ cube N}) :
    highMode N w m.val ^ 2 ≤ (∑ k : Lab N, ChatW N w k ^ 2)
      * ∑ k : Lab N, chiHat (Work.BoseB4.vec (m.val - labVec N k)) ^ 2 := by
  have hcs := Finset.sum_mul_sq_le_sq_mul_sq (Finset.univ : Finset (Lab N))
    (fun k => ChatW N w k) (fun k => chiHat (Work.BoseB4.vec (m.val - labVec N k)))
  simpa only [highMode] using hcs

/-- `m ↦ highMode N w m ^ 2` is summable. -/
theorem summable_highMode_sq (N : ℕ) (w : Lab N → ℝ) :
    Summable (fun m : {m : Z3 // m ∉ cube N} => highMode N w m.val ^ 2) := by
  have hSumA : ∀ k : Lab N, Summable (fun m : {m : Z3 // m ∉ cube N} =>
      chiHat (Work.BoseB4.vec (m.val - labVec N k)) ^ 2) :=
    fun k => (summable_chiHat_sq_shift (labVec N k)).subtype _
  have hSumg : Summable (fun m : {m : Z3 // m ∉ cube N} =>
      ∑ k : Lab N, chiHat (Work.BoseB4.vec (m.val - labVec N k)) ^ 2) :=
    summable_sum (fun k _ => hSumA k)
  exact Summable.of_nonneg_of_le (fun m => sq_nonneg _)
    (fun m => highMode_sq_le N w m) (hSumg.mul_left _)

/-- **The `highIdeal` tail estimate.**  If the shifted `χ̂²`-tail obeys the Schwartz bound with
constant `C` (hypothesis `hTail`), then

    `∑_{m ∉ cube N} (highIdeal N w m)² ≤ C · card (Lab N) / R^101 · ∑_i w i²`,

`R = rad N L`, for every `w` supported in the ball of radius `L`.  Cauchy–Schwarz is applied
*inside the support of `w`* (this is what makes the shifted tail bound — which needs
`‖vec (K i)‖ ≤ L` — applicable to every contributing `i`). -/
theorem highIdeal_sq_tail_le {C : ℝ} (hC : 0 ≤ C)
    (hTail : ∀ (N : ℕ) (L : ℝ) (i : Z3), 0 ≤ L → 1 ≤ rad N L →
      ‖Work.BoseB4.vec i‖ ≤ L →
      (∑' m : {m : Z3 // m ∉ cube N}, chiHatSq (Work.BoseB4.vec (m.val - i)) ^ 2)
        ≤ C / rad N L ^ 101) :
    ∀ (N : ℕ) (L : ℝ) (w : Lab N → ℝ), 0 ≤ L → 1 ≤ rad N L →
      (∀ i, w i ≠ 0 → ‖Work.BoseB4.vec (labVec N i)‖ ≤ L) →
      (∑' m : {m : Z3 // m ∉ cube N}, highIdeal N w m.val ^ 2)
        ≤ C * (Fintype.card (Lab N) : ℝ) / rad N L ^ 101 * ∑ i : Lab N, w i ^ 2 := by
  intro N L w hL hR hw
  set S : Finset (Lab N) := Finset.univ.filter (fun i => w i ≠ 0) with hSdef
  have hSmem : ∀ i : Lab N, i ∈ S ↔ w i ≠ 0 := by
    intro i
    rw [hSdef, Finset.mem_filter]
    simp
  -- summability of the summands
  have hSumA : ∀ i : Lab N, Summable (fun m : {m : Z3 // m ∉ cube N} =>
      chiHatSq (Work.BoseB4.vec (m.val - labVec N i)) ^ 2) :=
    fun i => (summable_chiHatSq_sq_shift (labVec N i)).subtype _
  have hSumg : Summable (fun m : {m : Z3 // m ∉ cube N} =>
      ∑ i ∈ S, chiHatSq (Work.BoseB4.vec (m.val - labVec N i)) ^ 2) :=
    summable_sum (fun i _ => hSumA i)
  have hSumRhs : Summable (fun m : {m : Z3 // m ∉ cube N} =>
      (∑ i : Lab N, w i ^ 2) * ∑ i ∈ S, chiHatSq (Work.BoseB4.vec (m.val - labVec N i)) ^ 2) :=
    hSumg.mul_left _
  have hpoint : ∀ m : {m : Z3 // m ∉ cube N}, highIdeal N w m.val ^ 2
      ≤ (∑ i : Lab N, w i ^ 2)
        * ∑ i ∈ S, chiHatSq (Work.BoseB4.vec (m.val - labVec N i)) ^ 2 := by
    intro m
    have hS : suppW N w = S := rfl
    simpa only [hS] using highIdeal_sq_le N w m
  have hSumf : Summable (fun m : {m : Z3 // m ∉ cube N} => highIdeal N w m.val ^ 2) :=
    summable_highIdeal_sq N w
  have hstep : (∑' m : {m : Z3 // m ∉ cube N}, highIdeal N w m.val ^ 2)
      ≤ ∑' m : {m : Z3 // m ∉ cube N},
          (∑ i : Lab N, w i ^ 2)
            * ∑ i ∈ S, chiHatSq (Work.BoseB4.vec (m.val - labVec N i)) ^ 2 :=
    Summable.tsum_le_tsum hpoint hSumf hSumRhs
  -- the interchange of the finite support sum with the lattice sum
  have hswap : (∑' m : {m : Z3 // m ∉ cube N},
        ∑ i ∈ S, chiHatSq (Work.BoseB4.vec (m.val - labVec N i)) ^ 2)
      = ∑ i ∈ S, ∑' m : {m : Z3 // m ∉ cube N},
          chiHatSq (Work.BoseB4.vec (m.val - labVec N i)) ^ 2 :=
    (hasSum_sum (s := S)
      (f := fun i (m : {m : Z3 // m ∉ cube N}) =>
        chiHatSq (Work.BoseB4.vec (m.val - labVec N i)) ^ 2)
      (a := fun i => ∑' m : {m : Z3 // m ∉ cube N},
        chiHatSq (Work.BoseB4.vec (m.val - labVec N i)) ^ 2)
      (fun i _ => (hSumA i).hasSum)).tsum_eq
  have hbound : (∑ i ∈ S, ∑' m : {m : Z3 // m ∉ cube N},
        chiHatSq (Work.BoseB4.vec (m.val - labVec N i)) ^ 2)
      ≤ S.card * (C / rad N L ^ 101) := by
    calc (∑ i ∈ S, ∑' m : {m : Z3 // m ∉ cube N},
          chiHatSq (Work.BoseB4.vec (m.val - labVec N i)) ^ 2)
        ≤ ∑ _i ∈ S, (C / rad N L ^ 101) :=
          Finset.sum_le_sum fun i hi =>
            hTail N L (labVec N i) hL hR (hw i ((hSmem i).mp hi))
      _ = S.card * (C / rad N L ^ 101) := by
          rw [Finset.sum_const, nsmul_eq_mul]
  have hcard : (S.card : ℝ) ≤ (Fintype.card (Lab N) : ℝ) := by
    exact_mod_cast Finset.card_le_univ S
  calc (∑' m : {m : Z3 // m ∉ cube N}, highIdeal N w m.val ^ 2)
      ≤ ∑' m : {m : Z3 // m ∉ cube N},
          (∑ i : Lab N, w i ^ 2)
            * ∑ i ∈ S, chiHatSq (Work.BoseB4.vec (m.val - labVec N i)) ^ 2 := hstep
    _ = (∑ i : Lab N, w i ^ 2) * (∑ i ∈ S, ∑' m : {m : Z3 // m ∉ cube N},
          chiHatSq (Work.BoseB4.vec (m.val - labVec N i)) ^ 2) := by
        rw [tsum_mul_left, hswap]
    _ ≤ (∑ i : Lab N, w i ^ 2) * ((Fintype.card (Lab N) : ℝ) * (C / rad N L ^ 101)) := by
        refine mul_le_mul_of_nonneg_left ?_ (by positivity)
        exact le_trans hbound
          (mul_le_mul_of_nonneg_right hcard (by positivity))
    _ = C * (Fintype.card (Lab N) : ℝ) / rad N L ^ 101 * ∑ i : Lab N, w i ^ 2 := by ring

/-! ## 2. The `nu`-bound -/

/-- The `ℓ¹`-mass of the high part of `F̂` is controlled by the shifted `|χ̂|`-tail: if
`Σ'_{m ∉ cube} |χ̂(vec (m−k))| ≤ C/R^101` for every `‖vec k‖ ≤ L` (hypothesis `hAbs`), then
`nu N w ≤ (∑_i |w i|)·C/R^101`, whence `nu N w ^ 2 ≤ C^2 · card / R^101 · ∑ w i²`. -/
theorem nu_sq_le {C : ℝ} (hC : 0 ≤ C)
    (hAbs : ∀ (N : ℕ) (L : ℝ) (k : Z3), 0 ≤ L → 1 ≤ rad N L → ‖Work.BoseB4.vec k‖ ≤ L →
      (∑' m : {m : Z3 // m ∉ cube N}, |chiHat (Work.BoseB4.vec (m.val - k))|)
        ≤ C / rad N L ^ 101) :
    ∀ (N : ℕ) (L : ℝ) (w : Lab N → ℝ), 0 ≤ L → 1 ≤ rad N L →
      (∀ i, w i ≠ 0 → ‖Work.BoseB4.vec (labVec N i)‖ ≤ L) →
      nu N w ^ 2
        ≤ C ^ 2 * (Fintype.card (Lab N) : ℝ) / rad N L ^ 101 * ∑ i : Lab N, w i ^ 2 := by
  intro N L w hL hR hw
  set S : Finset (Lab N) := Finset.univ.filter (fun i => w i ≠ 0) with hSdef
  have hSmem : ∀ i : Lab N, i ∈ S ↔ w i ≠ 0 := by
    intro i
    rw [hSdef, Finset.mem_filter]
    simp
  have hSumAbs : ∀ i : Lab N, Summable (fun k : {k : Z3 // k ∉ cube N} =>
      |chiHat (Work.BoseB4.vec (k.val - labVec N i))|) :=
    fun i => (summable_chiHat_abs_shift (labVec N i)).subtype _
  -- pointwise domination of `|F̂(k)|`
  have hpoint : ∀ k : {k : Z3 // k ∉ cube N}, |Fhat N w k.val|
      ≤ ∑ i ∈ S, |w i| * |chiHat (Work.BoseB4.vec (k.val - labVec N i))| := by
    intro k
    have hsub : (∑ i : Lab N, w i * chiHat (Work.BoseB4.vec (k.val - labVec N i)))
        = ∑ i ∈ S, w i * chiHat (Work.BoseB4.vec (k.val - labVec N i)) := by
      refine (Finset.sum_subset (Finset.filter_subset _ _) ?_).symm
      intro i _ hi
      have hwi : w i = 0 := by
        by_contra hne
        exact hi ((hSmem i).mpr hne)
      rw [hwi, zero_mul]
    calc |Fhat N w k.val|
        = |∑ i ∈ S, w i * chiHat (Work.BoseB4.vec (k.val - labVec N i))| := by
          rw [Fhat, ← hsub]
      _ ≤ ∑ i ∈ S, |w i * chiHat (Work.BoseB4.vec (k.val - labVec N i))| :=
          Finset.abs_sum_le_sum_abs _ _
      _ = ∑ i ∈ S, |w i| * |chiHat (Work.BoseB4.vec (k.val - labVec N i))| := by
          refine Finset.sum_congr rfl fun i _ => ?_
          rw [abs_mul]
  have hsum_le : nu N w ≤ ∑ i ∈ S, ∑' k : {k : Z3 // k ∉ cube N},
      |w i| * |chiHat (Work.BoseB4.vec (k.val - labVec N i))| := by
    show (∑' k : {k : Z3 // k ∉ cube N}, |Fhat N w k.val|) ≤ _
    have hsumg : Summable (fun k : {k : Z3 // k ∉ cube N} =>
        ∑ i ∈ S, |w i| * |chiHat (Work.BoseB4.vec (k.val - labVec N i))|) :=
      summable_sum (fun i _ => (hSumAbs i).mul_left _)
    have hsumf : Summable (fun k : {k : Z3 // k ∉ cube N} => |Fhat N w k.val|) :=
      Summable.of_nonneg_of_le (fun k => abs_nonneg _) hpoint hsumg
    have h1 : (∑' k : {k : Z3 // k ∉ cube N}, |Fhat N w k.val|)
        ≤ ∑' k : {k : Z3 // k ∉ cube N},
            ∑ i ∈ S, |w i| * |chiHat (Work.BoseB4.vec (k.val - labVec N i))| :=
      Summable.tsum_le_tsum hpoint hsumf hsumg
    have h2 : (∑' k : {k : Z3 // k ∉ cube N},
          ∑ i ∈ S, |w i| * |chiHat (Work.BoseB4.vec (k.val - labVec N i))|)
        = ∑ i ∈ S, ∑' k : {k : Z3 // k ∉ cube N},
            |w i| * |chiHat (Work.BoseB4.vec (k.val - labVec N i))| :=
      (hasSum_sum (s := S)
        (f := fun i (k : {k : Z3 // k ∉ cube N}) =>
          |w i| * |chiHat (Work.BoseB4.vec (k.val - labVec N i))|)
        (a := fun i => ∑' k : {k : Z3 // k ∉ cube N},
          |w i| * |chiHat (Work.BoseB4.vec (k.val - labVec N i))|)
        (fun i _ => ((hSumAbs i).mul_left (|w i|)).hasSum)).tsum_eq
    rw [h2] at h1
    exact h1
  have hTailSum : (∑ i ∈ S, ∑' k : {k : Z3 // k ∉ cube N},
      |w i| * |chiHat (Work.BoseB4.vec (k.val - labVec N i))|)
      ≤ ∑ i ∈ S, |w i| * (C / rad N L ^ 101) := by
    refine Finset.sum_le_sum fun i hi => ?_
    rw [tsum_mul_left]
    exact mul_le_mul_of_nonneg_left (hAbs N L (labVec N i) hL hR (hw i ((hSmem i).mp hi)))
      (abs_nonneg _)
  have hcard : (S.card : ℝ) ≤ (Fintype.card (Lab N) : ℝ) := by
    exact_mod_cast Finset.card_le_univ S
  have hw1 : (∑ i ∈ S, |w i|) ^ 2 ≤ (Fintype.card (Lab N) : ℝ) * ∑ i : Lab N, w i ^ 2 := by
    have h1 : (∑ i ∈ S, |w i|) ^ 2 ≤ (S.card : ℝ) * ∑ i ∈ S, |w i| ^ 2 :=
      sq_sum_le_card_mul_sum_sq
    have h2 : (∑ i ∈ S, |w i| ^ 2) ≤ ∑ i : Lab N, w i ^ 2 := by
      refine le_trans (Finset.sum_le_sum fun i _ => ?_)
        (Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
          (fun i _ _ => sq_nonneg _))
      rw [sq_abs]
    calc (∑ i ∈ S, |w i|) ^ 2 ≤ (S.card : ℝ) * ∑ i ∈ S, |w i| ^ 2 := h1
      _ ≤ (Fintype.card (Lab N) : ℝ) * ∑ i : Lab N, w i ^ 2 := by
          refine mul_le_mul hcard h2 (by positivity) (by positivity)
  have hnu : nu N w ≤ (∑ i ∈ S, |w i|) * (C / rad N L ^ 101) := by
    refine le_trans hsum_le (le_trans hTailSum ?_)
    rw [Finset.sum_mul]
  have hnu0 : 0 ≤ nu N w := tsum_nonneg fun k => abs_nonneg _
  have h1 : nu N w ^ 2 ≤ ((∑ i ∈ S, |w i|) * (C / rad N L ^ 101)) ^ 2 := by
    rw [sq_le_sq, abs_of_nonneg hnu0,
      abs_of_nonneg (mul_nonneg (Finset.sum_nonneg fun i _ => abs_nonneg _)
        (div_nonneg hC (by positivity)))]
    exact hnu
  have h2 : ((∑ i ∈ S, |w i|) * (C / rad N L ^ 101)) ^ 2
      ≤ C ^ 2 * (Fintype.card (Lab N) : ℝ) / rad N L ^ 101 * ∑ i : Lab N, w i ^ 2 := by
    have hsquare : (C / rad N L ^ 101) ^ 2 ≤ C ^ 2 / rad N L ^ 101 := by
      rw [div_pow]
      refine div_le_div_of_nonneg_left (by positivity) (by positivity) ?_
      nlinarith [one_le_pow₀ hR (n := 101), pow_nonneg (le_trans zero_le_one hR) 101]
    rw [mul_pow, div_eq_mul_inv]
    calc (∑ i ∈ S, |w i|) ^ 2 * (C / rad N L ^ 101) ^ 2
        ≤ ((Fintype.card (Lab N) : ℝ) * ∑ i : Lab N, w i ^ 2) * (C ^ 2 / rad N L ^ 101) :=
          mul_le_mul hw1 hsquare (by positivity) (by positivity)
      _ = C ^ 2 * (Fintype.card (Lab N) : ℝ) / rad N L ^ 101 * ∑ i : Lab N, w i ^ 2 := by ring
  exact le_trans h1 h2

end Work.BoseRowQ2
