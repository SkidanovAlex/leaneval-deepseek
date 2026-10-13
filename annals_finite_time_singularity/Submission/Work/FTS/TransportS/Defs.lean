/-
Copyright: work module for the Elgindi finite-time singularity project.

# `Submission/Work/FTS/TransportS/`: the transport replacements `T2S`, `T3S_Dz`

This is the interface chapter of the subproject `TransportS` (the transport replacements
`T2S`/`T3S_Dz` of `Submission/Work/FTS/ELL_H2_LEAD.md` §B2–B3, plus the per-slot `IP4`
transport facts).  The design document is `Submission/Work/FTS/ELL_H2_LEAD.md`; the
statements are frozen in `Submission/Work/FTS/ELL_H2_STATEMENTS.lean.txt` and the vocabulary
(`CoefTh`, `CoefThMem`, `T2Clause`, `T3Clause`, `HQo`, `WDp`, …) in
`Submission/Work/FTS/VocabO.lean`.

## What this file contains

* `slotW α a`: the angular weight of a slot `(a,b)` of the flat `ℋ⁴`-pairing, i.e. of the
  corresponding summand of `HkIntegrand α 4`: `(Whz)² = w² sin(2θ)^{-η}` for the `D_z`-only
  slots (`a = 0`) and `(Wm)² = w² sin(2θ)^{-γ}` for the slots carrying a `θ`-derivative
  (`a ≥ 1`).  Every slot of `H4Pair`/`HkIntegrand` is `slotW α a` times the square of its
  `D`-derivative, and every leaf of the unfolding of the coercive `IP4`
  (`Work.FTS.CoercivityStep.IP4`) carries a weight `ρ` with `0 ≤ ρ ≤ slotW α a` for its slot.
* the elementary API of the *flat angular coefficient norm* `CoefTh l f`
  (`VocabO.CoefTh`) and of its honesty companion `CoefThMem l f`: nonnegativity,
  domination of every single `supAbsO` occurring in the sum, and the passage from explicit
  sup bounds to `CoefThMem` and back.

The analytic content of the chapter (the σ-gain `flat_mixed_le`, the sup bounds for a
`CoefThMem`-datum, the easy/hard parts of `T2S` and the mismatch bound of `T3S_Dz`) lives in
the sibling modules of this directory.
-/
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Submission.Work.FTS.VocabO
import Submission.Work.FTS.H2.Defs
import Submission.Work.FTS.H2.HeasyBlocksId
import Submission.Work.FTS.H2.RegQDefs
import Submission.Work.FTS.H2.STEasyId

set_option synthInstance.maxHeartbeats 400000 -- v435-synth

noncomputable section
open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.TransportS

open Work.FTS.Galerkin (Fn)

set_option autoImplicit false

/-! ## The slot weight of the flat `ℋ⁴`-pairing -/

/-- The angular weight of the slot `(a,b)` of the flat `ℋ⁴`-pairing: `(Whz)²` for the
`D_z`-only slots (`a = 0`) and `(Wm)²` for the slots with a `θ`-derivative (`a ≥ 1`).

On the open quadrant (`sin (2θ) > 0`) this is `w(z)² sin(2θ)^{-η}` resp.
`w(z)² sin(2θ)^{-γ}` (`hbi_Whz_sq`, `hbi_Wm_sq` of `Submission/Work/FTS/H2/HeasyBlocksId.lean`). -/
def slotW (α : ℝ) (a : ℕ) : ℝ → ℝ → ℝ :=
  if a = 0 then fun z θ => (Work.FTS.H2.Whz z θ) ^ 2
  else fun z θ => (Work.FTS.H2.Wm α z θ) ^ 2

@[simp] theorem slotW_zero (α : ℝ) :
    slotW α 0 = fun z θ => (Work.FTS.H2.Whz z θ) ^ 2 := rfl

theorem slotW_of_ne (α : ℝ) {a : ℕ} (ha : a ≠ 0) :
    slotW α a = fun z θ => (Work.FTS.H2.Wm α z θ) ^ 2 := by
  simp only [slotW, if_neg ha]

theorem slotW_of_pos' (α : ℝ) {a : ℕ} (ha : 1 ≤ a) :
    slotW α a = fun z θ => (Work.FTS.H2.Wm α z θ) ^ 2 :=
  slotW_of_ne α (by omega)

/-- The slot weight is nonnegative (it is a square, uniformly in `α` and `a`). -/
theorem slotW_nonneg (α : ℝ) (a : ℕ) (z θ : ℝ) : 0 ≤ slotW α a z θ := by
  unfold slotW
  split_ifs <;> exact sq_nonneg _

/-- On the open quadrant the slot weight of a `D_z`-only slot is `w² sin(2θ)^{-η}`. -/
theorem slotW_zero_eq (α : ℝ) {z θ : ℝ} (hθ : θ ∈ Set.Ioo (0 : ℝ) (π / 2)) :
    slotW α 0 z θ = (Work.Spaces.w z) ^ 2 * (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta)) := by
  have hs : 0 ≤ Real.sin (2 * θ) :=
    Real.sin_nonneg_of_mem_Icc ⟨by linarith [hθ.1], by linarith [hθ.2, Real.pi_pos]⟩
  simp only [slotW, if_pos rfl]
  exact Work.FTS.H2.hbi_Whz_sq z θ hs

/-- On the open quadrant the slot weight of a slot with a `θ`-derivative is
`w² sin(2θ)^{-γ}`. -/
theorem slotW_of_pos_eq (α : ℝ) {a : ℕ} (ha : 1 ≤ a) {z θ : ℝ}
    (hθ : θ ∈ Set.Ioo (0 : ℝ) (π / 2)) :
    slotW α a z θ = (Work.Spaces.w z) ^ 2 * (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α)) := by
  have hs : 0 ≤ Real.sin (2 * θ) :=
    Real.sin_nonneg_of_mem_Icc ⟨by linarith [hθ.1], by linarith [hθ.2, Real.pi_pos]⟩
  rw [slotW_of_pos' α ha]
  exact Work.FTS.H2.hbi_Wm_sq α z θ hs

/-- The `D_z`-only slot weight is dominated by the mixed one on the open quadrant
(`sin(2θ)^{-η} ≤ sin(2θ)^{-γ}` since `η ≤ γ`). -/
theorem slotW_zero_le (α : ℝ) (hα : 0 < α) {z θ : ℝ}
    (hθ : θ ∈ Set.Ioo (0 : ℝ) (π / 2)) : slotW α 0 z θ ≤ slotW α 1 z θ := by
  have hs := Work.FTS.H2.rpow_eta_le_gam hα ⟨le_of_lt hθ.1, le_of_lt hθ.2⟩
  rw [slotW_zero_eq α hθ, slotW_of_pos_eq α (le_refl 1) hθ]
  exact mul_le_mul_of_nonneg_left hs (sq_nonneg _)

/-! ## The slot decomposition of the flat `ℋ⁴`-pairing

`H4PairInt α u v z θ` is the sum, over the slots `(a,b)`, of
`slotW α a z θ * mixed b a u z θ * mixed b a v z θ` (with the `D_z`-only slots indexed by
`b = a`).  The lemma below records this identification, the algebraic input of every
`IP4`-slot reduction. -/

/-- `H4PairInt` as a sum of slot products, with the slot weights `slotW α a`. -/
theorem H4PairInt_eq_slot_sum (α : ℝ) (u v : ℝ → ℝ → ℝ) (z θ : ℝ) :
    Work.FTS.H2.H4PairInt α u v z θ
      = (∑ i ∈ Finset.range 5, slotW α 0 z θ * Work.Spaces.DzIter i u z θ
            * Work.Spaces.DzIter i v z θ)
        + ∑ i ∈ Finset.range 5, ∑ j ∈ Finset.range 5,
            (if 1 ≤ i ∧ i + j ≤ 4 then
              slotW α i z θ * Work.Spaces.mixed j i u z θ * Work.Spaces.mixed j i v z θ
            else 0) := by
  unfold Work.FTS.H2.H4PairInt
  congr 1
  · refine Finset.sum_congr rfl fun i _ => ?_
    simp only [Work.FTS.H2.Whz, slotW, if_pos rfl, ↓reduceIte]
    ring
  · refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
    by_cases h : 1 ≤ i ∧ i + j ≤ 4
    · rw [if_pos h, if_pos h, slotW_of_pos' α h.1]
      simp only [Work.FTS.H2.Wm]
      ring
    · rw [if_neg h, if_neg h]

/-- The `D_z`-only slot of `HkIntegrand α 4 f` is `slotW α 0` times the square of `D_z^i f`. -/
theorem HkIntegrand_z_slot_eq (α : ℝ) (k : ℕ) (f : ℝ → ℝ → ℝ) (i : ℕ) (z θ : ℝ) :
    (Work.Spaces.DzIter i f z θ * Work.FTS.H2.Whz z θ) ^ 2
      = slotW α 0 z θ * (Work.Spaces.DzIter i f z θ) ^ 2 := by
  rw [slotW_zero α]
  ring

/-- The mixed slot of `HkIntegrand α 4 f` is `slotW α i` times the square of `D_z^jD_θ^i f`. -/
theorem HkIntegrand_m_slot_eq (α : ℝ) (k : ℕ) (f : ℝ → ℝ → ℝ) (i j : ℕ) (hi : 1 ≤ i)
    (z θ : ℝ) :
    (Work.Spaces.mixed j i f z θ * Work.FTS.H2.Wm α z θ) ^ 2
      = slotW α i z θ * (Work.Spaces.mixed j i f z θ) ^ 2 := by
  rw [slotW_of_pos' α hi]
  ring

/-! ## The API of the flat angular coefficient norm `CoefTh`

`CoefTh l f = ∑_{b < l+1} ∑_{i < l+1} [b + i ≤ l] supAbsO (D_z^b D_θ^i ∂_θ f)`, where
`supAbsO` is the supremum over the **open** quadrant `(0,∞) × (0,π/2)`.  Since `supAbsO` of
an unbounded function is Lean's junk value `0`, the companion honesty predicate
`CoefThMem l f` (every one of the finitely many functions is bounded on the open quadrant)
is needed for every *lower* bound on `CoefTh`; the lemmas below make that explicit. -/

/-- `supAbsO` is nonnegative. -/
theorem supAbsO_nonneg (g : ℝ → ℝ → ℝ) : 0 ≤ Work.FTS.H2.supAbsO g := by
  have hπ : (1 : ℝ) < π / 2 := by have := Real.pi_gt_three; linarith
  have hmem : |g 1 1| ∈ {y : ℝ | ∃ z : ℝ, 0 < z ∧ ∃ θ : ℝ, 0 < θ ∧ θ < π / 2 ∧
      y = |g z θ|} := ⟨1, one_pos, 1, one_pos, hπ, rfl⟩
  by_cases hb : BddAbove {y : ℝ | ∃ z : ℝ, 0 < z ∧ ∃ θ : ℝ, 0 < θ ∧ θ < π / 2 ∧
      y = |g z θ|}
  · exact le_trans (abs_nonneg _) (le_csSup hb hmem)
  · rw [Work.FTS.H2.supAbsO, Real.sSup_def, dif_neg (fun h => hb h.2)]

/-- `supAbsO g ≤ K` as soon as `|g| ≤ K` on the open quadrant. -/
theorem supAbsO_le' (g : ℝ → ℝ → ℝ) {K : ℝ}
    (h : ∀ z θ : ℝ, 0 < z → 0 < θ → θ < π / 2 → |g z θ| ≤ K) :
    Work.FTS.H2.supAbsO g ≤ K :=
  Work.FTS.H2.supAbsO_le h

/-- `CoefTh l f` is a sum of nonnegative terms, hence nonnegative. -/
theorem coefTh_nonneg (l : ℕ) (f : ℝ → ℝ → ℝ) : 0 ≤ Work.FTS.VocabO.CoefTh l f := by
  unfold Work.FTS.VocabO.CoefTh
  refine Finset.sum_nonneg fun b _ => Finset.sum_nonneg fun i _ => ?_
  split_ifs
  · exact supAbsO_nonneg _
  · exact le_refl 0

/-- Explicit sup bounds on the constituents of `CoefTh` give a bound on `CoefTh`. -/
theorem coefTh_le_of_supAbsO_le {l : ℕ} {f : ℝ → ℝ → ℝ} {K : ℝ}
    (h : ∀ b i : ℕ, b + i ≤ l →
      Work.FTS.H2.supAbsO (Work.Spaces.mixed b i (Work.Spaces.pth f)) ≤ K) :
    Work.FTS.VocabO.CoefTh l f ≤ (((l : ℝ) + 1) * ((l : ℝ) + 1)) * K := by
  have hK : 0 ≤ K := le_trans (supAbsO_nonneg _) (h 0 0 (by omega))
  have hterm : ∀ b i : ℕ,
      (if b + i ≤ l then
        Work.FTS.H2.supAbsO (Work.Spaces.mixed b i (Work.Spaces.pth f)) else 0) ≤ K := by
    intro b i
    by_cases hbi : b + i ≤ l
    · rw [if_pos hbi]; exact h b i hbi
    · rw [if_neg hbi]; exact hK
  have hcard : ((Finset.range (l + 1)).card : ℝ) = (l : ℝ) + 1 := by simp
  have hinner : ∀ b : ℕ,
      (∑ i ∈ Finset.range (l + 1),
        (if b + i ≤ l then
          Work.FTS.H2.supAbsO (Work.Spaces.mixed b i (Work.Spaces.pth f)) else 0))
        ≤ ((l : ℝ) + 1) * K := by
    intro b
    have h1 : (∑ i ∈ Finset.range (l + 1),
        (if b + i ≤ l then
          Work.FTS.H2.supAbsO (Work.Spaces.mixed b i (Work.Spaces.pth f)) else 0))
        ≤ ∑ _i ∈ Finset.range (l + 1), K :=
      Finset.sum_le_sum fun i _ => hterm b i
    rwa [Finset.sum_const, nsmul_eq_mul, hcard] at h1
  have h2 : (∑ b ∈ Finset.range (l + 1), ∑ i ∈ Finset.range (l + 1),
        (if b + i ≤ l then
          Work.FTS.H2.supAbsO (Work.Spaces.mixed b i (Work.Spaces.pth f)) else 0))
      ≤ ∑ _b ∈ Finset.range (l + 1), ((l : ℝ) + 1) * K :=
    Finset.sum_le_sum fun b _ => hinner b
  rw [Finset.sum_const, nsmul_eq_mul, hcard] at h2
  unfold Work.FTS.VocabO.CoefTh
  refine le_trans h2 ?_
  exact le_of_eq (mul_assoc ((l : ℝ) + 1) ((l : ℝ) + 1) K).symm

/-- **Every single `supAbsO` occurring in `CoefTh` is dominated by `CoefTh`.**  (No honesty
hypothesis is needed: the other terms are nonnegative.) -/
theorem supAbsO_le_coefTh {l : ℕ} {f : ℝ → ℝ → ℝ} {b i : ℕ} (hbi : b + i ≤ l) :
    Work.FTS.H2.supAbsO (Work.Spaces.mixed b i (Work.Spaces.pth f))
      ≤ Work.FTS.VocabO.CoefTh l f := by
  have hmem : b ∈ Finset.range (l + 1) := Finset.mem_range.mpr (by omega)
  have hmem' : i ∈ Finset.range (l + 1) := Finset.mem_range.mpr (by omega)
  have houter : ∀ b' ∈ Finset.range (l + 1),
      0 ≤ ∑ i' ∈ Finset.range (l + 1),
        (if b' + i' ≤ l then
          Work.FTS.H2.supAbsO (Work.Spaces.mixed b' i' (Work.Spaces.pth f)) else 0) := by
    intro b' _
    refine Finset.sum_nonneg fun i' _ => ?_
    by_cases h : b' + i' ≤ l
    · rw [if_pos h]; exact supAbsO_nonneg _
    · simp [if_neg h]
  have hsingle : (∑ i' ∈ Finset.range (l + 1),
        (if b + i' ≤ l then
          Work.FTS.H2.supAbsO (Work.Spaces.mixed b i' (Work.Spaces.pth f)) else 0))
      ≤ ∑ b' ∈ Finset.range (l + 1), ∑ i' ∈ Finset.range (l + 1),
        (if b' + i' ≤ l then
          Work.FTS.H2.supAbsO (Work.Spaces.mixed b' i' (Work.Spaces.pth f)) else 0) :=
    Finset.single_le_sum (f := fun (b' : ℕ) => ∑ i' ∈ Finset.range (l + 1),
        (if b' + i' ≤ l then
          Work.FTS.H2.supAbsO (Work.Spaces.mixed b' i' (Work.Spaces.pth f)) else 0))
      houter hmem
  have hinner : Work.FTS.H2.supAbsO (Work.Spaces.mixed b i (Work.Spaces.pth f))
      ≤ ∑ i' ∈ Finset.range (l + 1),
        (if b + i' ≤ l then
          Work.FTS.H2.supAbsO (Work.Spaces.mixed b i' (Work.Spaces.pth f)) else 0) := by
    have h0 : ∀ i' ∈ Finset.range (l + 1),
        0 ≤ (if b + i' ≤ l then
          Work.FTS.H2.supAbsO (Work.Spaces.mixed b i' (Work.Spaces.pth f)) else 0) := by
      intro i' _
      by_cases hbi' : b + i' ≤ l
      · rw [if_pos hbi']; exact supAbsO_nonneg _
      · simp [if_neg hbi']
    have h1 := Finset.single_le_sum (f := fun (i' : ℕ) => (if b + i' ≤ l then
        Work.FTS.H2.supAbsO (Work.Spaces.mixed b i' (Work.Spaces.pth f)) else 0)) h0 hmem'
    rwa [if_pos hbi] at h1
  unfold Work.FTS.VocabO.CoefTh
  exact le_trans hinner hsingle

/-- `CoefThMem` is monotone in the order. -/
theorem coefThMem_mono {l l' : ℕ} (hl : l ≤ l') {f : ℝ → ℝ → ℝ}
    (h : Work.FTS.VocabO.CoefThMem l' f) : Work.FTS.VocabO.CoefThMem l f :=
  fun b i hbi => h b i (le_trans hbi hl)

/-- `CoefThMem` is exactly the statement that each of the finitely many constituents of
`CoefTh` is bounded on the open quadrant (i.e. that the summands of `CoefTh` are not junk). -/
theorem coefThMem_iff {l : ℕ} {f : ℝ → ℝ → ℝ} :
    Work.FTS.VocabO.CoefThMem l f ↔
      ∀ b i : ℕ, b + i ≤ l → ∃ K : ℝ, ∀ z θ : ℝ, 0 < z → 0 < θ → θ < π / 2 →
        |Work.Spaces.mixed b i (Work.Spaces.pth f) z θ| ≤ K :=
  Iff.rfl

end Work.FTS.TransportS
