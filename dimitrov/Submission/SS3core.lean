import Mathlib
import Submission.ChebGrowth
import Submission.ChebGeom

/-!
# Isolated task: SS3core -- uniform growth of polynomials from a segment to
its ε-neighbourhood (the fattening lift, single-spike form)

Self-contained definitions.  Prove ONLY the declarations below; the file must be fully proved (add helpers freely).

WHY: SS3 (`polyDecay_fat_of_star`) needs: if monic `p_j` (degree `j`) are
bounded by `C·θ^j` on the hedgehog `star S`, then for some fixed small
`ε > 0` they are bounded by `C'·θ'^j` on `FatStar S ε` with `θ' < 1`.
Per-spike reduction: a point of `FatStar S ε` is within `ε` of one spike
segment `[0, w]`; normalizing the segment to `[0,1]` (rotate/dilate by
`w`), we need a bound on a degree-`n` polynomial known to be `≤ M` on the
real segment `[0,1]`, at complex points `z` within distance `δ` of
`[0,1]`, of the form `|q(z)| ≤ M · β(δ)^n · poly(n)` with `β(δ) → 1` as
`δ → 0` (so `θ·β < 1` for `θ < 1` and small `ε`).

MAIN THEOREM (`segment_growth`), NORMALIZED FORM: let `q : ℂ[X]` with
`q.natDegree ≤ n`, `0 ≤ M`, and `∀ t ∈ Icc 0 1, ‖q.eval (t : ℂ)‖ ≤ M`
(`q` bounded by `M` on `[0,1]`).  For `δ ∈ (0, 1]` and `z : ℂ` with
`∃ t ∈ Icc 0 1, ‖z - (t : ℂ)‖ ≤ δ`:

    ‖q.eval z‖ ≤ M * ((1 + 2 * Real.sqrt δ + 4 * δ) ^ n) * (2 * n + 1)

PROOF ROUTE (two delegated sub-lemmas, both PROVED):

* `Submission.ChebGrowth.cheb_growth` (ChebGrowth.lean): a degree-≤-n
  complex polynomial bounded by `M` on the real segment `[-1,1]` is, at
  every Joukowski point `(ζ + ζ⁻¹)/2` with `1 ≤ ‖ζ‖`, bounded by
  `M·‖ζ‖^n`  (companion polynomial + maximum modulus on the unit disk).

* `Submission.ChebGeom.exists_zeta_le` (ChebGeom.lean): a point `w`
  within distance `2δ` of `[-1,1]` has a Joukowski preimage `ζ` with
  `(ζ + ζ⁻¹)/2 = w` and `1 ≤ ‖ζ‖ ≤ 1 + 2√δ + 4δ`.

Assembly here: normalize `q` to the segment `[-1,1]` via the affine map
`x ↦ (x+1)/2` (i.e. `P := q.comp (C (1/2) * X + C (1/2))`), scale `z` by
`w := 2z - 1` (then `P.eval w = q.eval z`), apply the two sub-lemmas, and
compare bases (`M ≥ 0`, `1 ≤ 2n+1`).
-/

noncomputable section

open scoped Real Polynomial Topology BigOperators

namespace Submission.SS3core

open Polynomial
open Submission.ChebGrowth
open Submission.ChebGeom

/-- The affine map `x ↦ (x+1)/2` (as a complex polynomial), sending
`[-1,1]` onto `[0,1]`. -/
def chebAff : ℂ[X] := C ((1 / 2 : ℂ)) * X + C ((1 / 2 : ℂ))

/-- `q` re-based from the segment `[0,1]` to `[-1,1]`:
`(shiftPoly q).eval (2x-1) = q.eval x`. -/
def shiftPoly (q : ℂ[X]) : ℂ[X] := q.comp chebAff

lemma chebAff_eval (x : ℂ) : chebAff.eval x = (x + 1) / 2 := by
  simp [chebAff, div_eq_mul_inv]
  ring

lemma shiftPoly_eval (q : ℂ[X]) (x : ℂ) : (shiftPoly q).eval x = q.eval ((x + 1) / 2) := by
  rw [shiftPoly, Polynomial.eval_comp, chebAff_eval]

lemma chebAff_natDegree : chebAff.natDegree = 1 := by
  rw [chebAff, natDegree_add_eq_left_of_natDegree_lt]
  · rw [natDegree_C_mul (by norm_num : (1 / 2 : ℂ) ≠ 0), natDegree_X]
  · simp

lemma shiftPoly_natDegree_le {q : ℂ[X]} {n : ℕ} (hdeg : q.natDegree ≤ n) :
    (shiftPoly q).natDegree ≤ n := by
  calc
    (shiftPoly q).natDegree = (q.comp chebAff).natDegree := rfl
    _ ≤ q.natDegree * chebAff.natDegree := natDegree_comp_le
    _ ≤ n * 1 := Nat.mul_le_mul hdeg (by simp [chebAff_natDegree])
    _ = n := by rw [mul_one]

/-- A real `t ∈ [-1,1]` is mapped by `x ↦ (x+1)/2` into `[0,1]`. -/
lemma half_mem_Icc01 {t : ℝ} (ht : t ∈ Set.Icc (-1 : ℝ) 1) :
    (t + 1) / 2 ∈ Set.Icc (0 : ℝ) 1 := by
  constructor <;> nlinarith [ht.1, ht.2]

/-- If `q` is bounded by `M` on `[0,1]`, then `shiftPoly q` is bounded by
`M` on `[-1,1]`. -/
lemma shiftPoly_bound {q : ℂ[X]} {M : ℝ}
    (hq : ∀ t : ℝ, t ∈ Set.Icc (0 : ℝ) 1 → ‖q.eval (t : ℂ)‖ ≤ M)
    {t : ℝ} (ht : t ∈ Set.Icc (-1 : ℝ) 1) : ‖(shiftPoly q).eval (t : ℂ)‖ ≤ M := by
  rw [shiftPoly_eval]
  have hev : ((t : ℂ) + 1) / 2 = (((t + 1) / 2 : ℝ) : ℂ) := by
    norm_num
  rw [hev]
  exact hq ((t + 1) / 2) (half_mem_Icc01 ht)

/-- **Segment growth.**  A polynomial of degree `≤ n` bounded by `M` on the
real segment `[0,1]` grows on the `δ`-neighbourhood of `[0,1]` by at most
`(1 + 2√δ + 4δ)^n · (2n + 1)`. -/
theorem segment_growth {n : ℕ} (hn : 1 ≤ n) {q : ℂ[X]}
    (hdeg : q.natDegree ≤ n) {M : ℝ} (hM : 0 ≤ M)
    (hq : ∀ t : ℝ, t ∈ Set.Icc (0 : ℝ) 1 → ‖q.eval (t : ℂ)‖ ≤ M)
    {δ : ℝ} (hδ0 : 0 < δ) (_hδ1 : δ ≤ 1) {z : ℂ}
    (hz : ∃ t : ℝ, t ∈ Set.Icc (0 : ℝ) 1 ∧ ‖z - (t : ℂ)‖ ≤ δ) :
    ‖q.eval z‖ ≤ M * ((1 + 2 * Real.sqrt δ + 4 * δ) ^ n) * (2 * n + 1) := by
  rcases hz with ⟨t0, ht0m, hzδ⟩
  let w : ℂ := (2 : ℂ) * z - 1
  -- w is within 2δ of [-1,1] (witness: 2*t0 - 1)
  have hdist : ∃ s : ℝ, s ∈ Set.Icc (-1 : ℝ) 1 ∧ ‖w - (s : ℂ)‖ ≤ 2 * δ := by
    refine ⟨2 * t0 - 1, ?_, ?_⟩
    · constructor <;> nlinarith [ht0m.1, ht0m.2]
    · have hw : w - ((2 * t0 - 1 : ℝ) : ℂ) = (2 : ℂ) * (z - (t0 : ℂ)) := by
        dsimp [w]
        norm_num
        ring
      calc
        ‖w - ((2 * t0 - 1 : ℝ) : ℂ)‖ = ‖(2 : ℂ) * (z - (t0 : ℂ))‖ := by rw [hw]
        _ = (2 : ℝ) * ‖z - (t0 : ℂ)‖ := by simp
        _ ≤ 2 * δ := by
          exact mul_le_mul_of_nonneg_left hzδ (by norm_num : (0 : ℝ) ≤ 2)
  -- Joukowski preimage
  rcases exists_zeta_le hδ0.le hdist with ⟨ζ, hζw, hζ1, hζle⟩
  -- growth of the re-based polynomial at ζ
  have hb := cheb_growth (n := n) (P := shiftPoly q) (shiftPoly_natDegree_le hdeg) hM
    (fun t ht => shiftPoly_bound hq ht) ζ hζ1
  -- connect q.eval z = (shiftPoly q).eval ((ζ+ζ⁻¹)/2)
  have hzP : q.eval z = (shiftPoly q).eval ((ζ + ζ⁻¹) / 2) := by
    calc
      q.eval z = q.eval ((w + 1) / 2) := by
        congr 1
        dsimp [w]
        ring
      _ = (shiftPoly q).eval w := by
        rw [shiftPoly_eval]
      _ = (shiftPoly q).eval ((ζ + ζ⁻¹) / 2) := by rw [hζw]
  have hmain : ‖q.eval z‖ ≤ M * ‖ζ‖ ^ n := by
    rw [hzP]
    exact hb
  -- base comparison: ‖ζ‖ ≤ 1 + 2√δ + 4δ, so ‖ζ‖^n ≤ base^n
  have hpow : ‖ζ‖ ^ n ≤ (1 + 2 * Real.sqrt δ + 4 * δ) ^ n :=
    pow_le_pow_left₀ (norm_nonneg ζ) hζle n
  have hMpow : M * ‖ζ‖ ^ n ≤ M * (1 + 2 * Real.sqrt δ + 4 * δ) ^ n :=
    mul_le_mul_of_nonneg_left hpow hM
  -- multiply by (2n+1) ≥ 1
  have hbase0 : 0 ≤ 1 + 2 * Real.sqrt δ + 4 * δ := by
    nlinarith [Real.sqrt_nonneg δ]
  have hnonneg : 0 ≤ M * (1 + 2 * Real.sqrt δ + 4 * δ) ^ n :=
    mul_nonneg hM (pow_nonneg hbase0 n)
  have hone : (1 : ℝ) ≤ (2 * (n : ℝ) + 1) := by
    have hn' : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
    nlinarith
  calc
    ‖q.eval z‖ ≤ M * ‖ζ‖ ^ n := hmain
    _ ≤ M * (1 + 2 * Real.sqrt δ + 4 * δ) ^ n := hMpow
    _ ≤ M * (1 + 2 * Real.sqrt δ + 4 * δ) ^ n * (2 * (n : ℝ) + 1) := by
      nlinarith [hnonneg, hone]
    _ = M * (1 + 2 * Real.sqrt δ + 4 * δ) ^ n * (2 * n + 1) := by norm_num

end Submission.SS3core

end
