import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Algebra.Order.Star.Real
import Submission.Work.BoseK15.Derive
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Work.BoseK15.hatChiSq_form_upper` — the Schur upper bound of FS §10's kernel form

The `hatChiSq_form` row of the `Q3Kernel` interface (`Work.BoseB7A.Defs`) is the
pair: the quadratic form

    `Σ_{s,s'∈S} c s · c s' · χ̂²(s'-s) · ⟨v s', v s⟩`

is **nonnegative** (`hatChiSq_double_sum_nonneg`) and **bounded above** by
`K₀ · Σ_s c s² ⟨v s, v s⟩`.  This file supplies the *upper bound*, i.e. the
`K15Input`-derived half, which is a Schur test:

* the kernel `χ̂²` is read at the dual-lattice momenta `ℓ • kmom (s' - s) = vec n`;
  the decay of `χ̂²` (`ChiReg`, order `decayOrder = 26`) and the dual-lattice
  injectivity of `kmom` (`K15Input.hlat`) make every *row* of the kernel
  absolutely summable with the lattice constant `Cchi * Csum`
  (`hatChiSq_row_sum_le`);
* Cauchy–Schwarz for the Fock form (`Work.BoseB7.bp_cauchy_abs`) together with
  AM–GM gives the pointwise bound `|c s c s' K ⟨v s',v s⟩| ≤ |K|(c s²⟨v s,v s⟩ +
  c s'²⟨v s',v s'⟩)/2` (`bp_mul_abs_le`);
* a weighted row-sum (Schur) lemma (`double_sum_row_bound`) turns the row bound
  into the quadratic-form bound.

The row constant `Cchi * Csum` is dominated by `K₀` (`K15Input.K₀_sum`), which
closes the estimate with the *chapter* constant.

## Contents

* `hatChiSq_row_sum_le` — the lattice row bound `Σ_{s'} |χ̂²(s'-s)| ≤ Cchi·Csum`;
* `bp_mul_abs_le` — the pointwise Cauchy–Schwarz + AM–GM bound;
* `double_sum_row_bound` — the abstract Schur row-sum lemma;
* `hatChiSq_form_upper` — the target.
-/

noncomputable section

open scoped BigOperators
open MeasureTheory Classical

namespace Work.BoseK15

local notation "ℝ³" => EuclideanSpace ℝ (Fin 3)

/-! ## 1. The lattice row bound on `χ̂²` -/

/-- **Each row of the `χ̂²`-kernel is absolutely summable.**  The mode labels
`s' ↦ kmom (s' - s)` are *distinct* dual-lattice points (`K15Input.hlat` is
injective), and `χ̂²(ℓ • kmom k) = χ̂²(vec (lift k))` decays at order
`decayOrder` (`K15Input.hatChiSq_abs_le`), so every finite row sum is bounded by
the lattice constant `Cchi * Csum` (`K15Input.sum_geom`). -/
theorem hatChiSq_row_sum_le {Mode : Type*} [AddCommGroup Mode] [Fintype Mode] [DecidableEq Mode]
    {F : Work.BoseB7.FockData Mode} {T : Work.BoseB7A.TildeData F} {E : Work.BoseB7.Q3Env Mode}
    {K₀ : ℝ} (h : Work.BoseK15.K15Input K₀ F T E) (s : Mode) (S : Finset Mode) :
    ∑ s' ∈ S, |E.hatChiSq (s' - s)| ≤ h.Cchi * h.Csum := by
  have hterm : ∀ s' : Mode,
      |E.hatChiSq (s' - s)| ≤ h.Cchi *
        (((1 : ℝ) + ‖Work.BoseB4.vec (h.hlat.lift (s' - s))‖ ^ 2) ^ decayOrder)⁻¹ := by
    intro s'
    rw [h.hatChiSq_eq (s' - s)]
    have hsm : E.ell • h.kmom (s' - s) = Work.BoseB4.vec (h.hlat.lift (s' - s)) := by
      rw [← h.ell_eq_E, h.hlat.lift_spec (s' - s), smul_inv_smul₀ (ne_of_gt h.ell_pos)]
    rw [hsm]
    exact h.hatChiSq_abs_le _
  have hinj : Set.InjOn (fun s' => h.hlat.lift (s' - s)) ↑S := by
    intro x hx y hy hxy
    exact sub_left_inj.mp (h.hlat.lift_injective hxy)
  calc ∑ s' ∈ S, |E.hatChiSq (s' - s)|
      ≤ ∑ s' ∈ S, h.Cchi *
          (((1 : ℝ) + ‖Work.BoseB4.vec (h.hlat.lift (s' - s))‖ ^ 2) ^ decayOrder)⁻¹ :=
        Finset.sum_le_sum fun s' _ => hterm s'
    _ = h.Cchi * ∑ s' ∈ S,
          (((1 : ℝ) + ‖Work.BoseB4.vec (h.hlat.lift (s' - s))‖ ^ 2) ^ decayOrder)⁻¹ := by
        rw [Finset.mul_sum]
    _ = h.Cchi * ∑ n ∈ S.image (fun s' => h.hlat.lift (s' - s)),
          (((1 : ℝ) + ‖Work.BoseB4.vec n‖ ^ 2) ^ decayOrder)⁻¹ := by
        rw [Finset.sum_image hinj]
    _ ≤ h.Cchi * h.Csum := mul_le_mul_of_nonneg_left (h.sum_geom _) h.Cchi_nonneg

/-- **The transposed row bound.**  `χ̂²` is even (`K15Input.hatChiSq_even`), so the
row bound of `hatChiSq_row_sum_le` holds with the summation index in the *first*
slot of the difference as well. -/
theorem hatChiSq_row_sum_le_swap {Mode : Type*} [AddCommGroup Mode] [Fintype Mode]
    [DecidableEq Mode]
    {F : Work.BoseB7.FockData Mode} {T : Work.BoseB7A.TildeData F} {E : Work.BoseB7.Q3Env Mode}
    {K₀ : ℝ} (h : Work.BoseK15.K15Input K₀ F T E) (s : Mode) (S : Finset Mode) :
    ∑ s' ∈ S, |E.hatChiSq (s - s')| ≤ h.Cchi * h.Csum := by
  have heven : ∀ x : Mode, |E.hatChiSq (s - x)| = |E.hatChiSq (x - s)| := by
    intro x
    have h1 : E.hatChiSq (s - x) = E.hatChiSq (x - s) := by
      rw [← h.hatChiSq_even_holds (x - s), neg_sub]
    rw [h1]
  calc ∑ x ∈ S, |E.hatChiSq (s - x)| = ∑ x ∈ S, |E.hatChiSq (x - s)| :=
        Finset.sum_congr rfl fun x _ => heven x
    _ ≤ h.Cchi * h.Csum := hatChiSq_row_sum_le h s S

/-! ## 2. The pointwise Cauchy–Schwarz + AM–GM bound -/

/-- **Pointwise bound of the kernel form.**  For every pair of modes `s, s'`, any
coefficients `c` and vectors `v`, and any scalar `K`,

`|c s · c s' · K · ⟨v s', v s⟩| ≤ |K| · (c s²⟨v s,v s⟩ + c s'²⟨v s',v s'⟩)/2`.

`Work.BoseB7.bp_cauchy_abs` bounds `|⟨v s', v s⟩|` by `√⟨v s',v s'⟩·√⟨v s,v s⟩`
and AM–GM (`two_mul_le_add_sq`) closes it. -/
theorem bp_mul_abs_le {Mode : Type*} [AddCommGroup Mode] [Fintype Mode]
    (F : Work.BoseB7.FockData Mode) (c : Mode → ℝ) (v : Mode → F.H)
    (s s' : Mode) (Kfun : ℝ) :
    |c s * c s' * Kfun * F.bp (v s') (v s)|
      ≤ |Kfun| * ((c s) ^ 2 * F.bp (v s) (v s) + (c s') ^ 2 * F.bp (v s') (v s')) / 2 := by
  have hA : 0 ≤ F.bp (v s) (v s) := F.bp_nonneg _
  have hA' : 0 ≤ F.bp (v s') (v s') := F.bp_nonneg _
  have hcs := Work.BoseB7.bp_cauchy_abs F (v s') (v s)
  have hAM : 2 * (|c s| * Real.sqrt (F.bp (v s) (v s))) *
      (|c s'| * Real.sqrt (F.bp (v s') (v s')))
      ≤ (c s) ^ 2 * F.bp (v s) (v s) + (c s') ^ 2 * F.bp (v s') (v s') := by
    have h := two_mul_le_add_sq (|c s| * Real.sqrt (F.bp (v s) (v s)))
      (|c s'| * Real.sqrt (F.bp (v s') (v s')))
    simpa [mul_pow, sq_abs, Real.sq_sqrt hA, Real.sq_sqrt hA'] using h
  have h1 : |c s * c s' * Kfun * F.bp (v s') (v s)|
      ≤ |Kfun| * ((|c s| * Real.sqrt (F.bp (v s) (v s))) *
          (|c s'| * Real.sqrt (F.bp (v s') (v s')))) := by
    rw [abs_mul, abs_mul, abs_mul]
    calc |c s| * |c s'| * |Kfun| * |F.bp (v s') (v s)|
        ≤ |c s| * |c s'| * |Kfun| *
            (Real.sqrt (F.bp (v s') (v s')) * Real.sqrt (F.bp (v s) (v s))) :=
          mul_le_mul_of_nonneg_left hcs (by positivity)
      _ = |Kfun| * ((|c s| * Real.sqrt (F.bp (v s) (v s))) *
            (|c s'| * Real.sqrt (F.bp (v s') (v s')))) := by ring
  have h2 : |Kfun| * ((|c s| * Real.sqrt (F.bp (v s) (v s))) *
        (|c s'| * Real.sqrt (F.bp (v s') (v s'))))
      ≤ |Kfun| * ((c s) ^ 2 * F.bp (v s) (v s) + (c s') ^ 2 * F.bp (v s') (v s')) / 2 := by
    have hK := mul_le_mul_of_nonneg_left hAM (abs_nonneg Kfun)
    linarith
  exact le_trans h1 h2

/-! ## 3. The abstract Schur row-sum lemma -/

/-- **Weighted row-sum (Schur) bound.**  If every row of `K` over `S` is bounded
by `D` and `w ≥ 0` on `S`, then the weighted double sum is bounded by
`D · Σ w`. -/
theorem double_sum_row_bound {ι : Type*} (S : Finset ι) (K : ι → ι → ℝ) (w : ι → ℝ)
    (D : ℝ) (hD : ∀ s ∈ S, ∑ s' ∈ S, K s s' ≤ D) (hw : ∀ s ∈ S, 0 ≤ w s) :
    ∑ s ∈ S, ∑ s' ∈ S, K s s' * w s ≤ D * ∑ s ∈ S, w s := by
  calc ∑ s ∈ S, ∑ s' ∈ S, K s s' * w s
      = ∑ s ∈ S, w s * (∑ s' ∈ S, K s s') := by
        refine Finset.sum_congr rfl fun s _ => ?_
        rw [Finset.mul_sum]
        exact Finset.sum_congr rfl fun s' _ => by ring
    _ ≤ ∑ s ∈ S, w s * D :=
        Finset.sum_le_sum fun s hs => mul_le_mul_of_nonneg_left (hD s hs) (hw s hs)
    _ = D * ∑ s ∈ S, w s := by rw [← Finset.sum_mul]; ring

/-! ## 4. The target -/

theorem hatChiSq_form_upper {Mode : Type*} [AddCommGroup Mode] [Fintype Mode] [DecidableEq Mode]
    {F : Work.BoseB7.FockData Mode} {T : Work.BoseB7A.TildeData F} {E : Work.BoseB7.Q3Env Mode}
    {K₀ : ℝ} (h : Work.BoseK15.K15Input K₀ F T E) :
    ∀ (S : Finset Mode) (c : Mode → ℝ) (v : Mode → F.H),
      (∑ s ∈ S, ∑ s' ∈ S, c s * c s' * E.hatChiSq (s' - s) * F.bp (v s') (v s))
        ≤ K₀ * ∑ s ∈ S, c s ^ 2 * F.bp (v s) (v s) := by
  intro S c v
  -- the row constant is dominated by the chapter constant
  have hD : h.Cchi * h.Csum ≤ K₀ := by
    have h1 : h.Cchi * h.Csum ≤ h.Cchi * (h.Csum + h.Ctail) :=
      mul_le_mul_of_nonneg_left (le_add_of_nonneg_right h.Ctail_nonneg) h.Cchi_nonneg
    linarith [h.K₀_sum]
  -- the pointwise bound
  have hpt : ∀ s s' : Mode,
      c s * c s' * E.hatChiSq (s' - s) * F.bp (v s') (v s)
      ≤ |E.hatChiSq (s' - s)| *
          (c s ^ 2 * F.bp (v s) (v s) + c s' ^ 2 * F.bp (v s') (v s')) / 2 := fun s s' =>
    le_trans (le_abs_self _) (bp_mul_abs_le F c v s s' _)
  -- the weighted double sum, via the two halves of the pointwise bound
  have hsum : (∑ s ∈ S, ∑ s' ∈ S, |E.hatChiSq (s' - s)| *
        (c s ^ 2 * F.bp (v s) (v s) + c s' ^ 2 * F.bp (v s') (v s')) / 2)
      ≤ (h.Cchi * h.Csum) * ∑ s ∈ S, c s ^ 2 * F.bp (v s) (v s) := by
    have hsplit : (∑ s ∈ S, ∑ s' ∈ S, |E.hatChiSq (s' - s)| *
          (c s ^ 2 * F.bp (v s) (v s) + c s' ^ 2 * F.bp (v s') (v s')) / 2)
        = (∑ s ∈ S, ∑ s' ∈ S, |E.hatChiSq (s' - s)| * (c s ^ 2 * F.bp (v s) (v s) / 2))
          + (∑ s ∈ S, ∑ s' ∈ S,
              |E.hatChiSq (s' - s)| * (c s' ^ 2 * F.bp (v s') (v s') / 2)) := by
      rw [← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl fun s _ => ?_
      rw [← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl fun s' _ => ?_
      ring
    rw [hsplit]
    have h1 : (∑ s ∈ S, ∑ s' ∈ S, |E.hatChiSq (s' - s)| * (c s ^ 2 * F.bp (v s) (v s) / 2))
        ≤ (h.Cchi * h.Csum) * (∑ s ∈ S, c s ^ 2 * F.bp (v s) (v s) / 2) :=
      double_sum_row_bound S (fun s s' => |E.hatChiSq (s' - s)|)
        (fun s => c s ^ 2 * F.bp (v s) (v s) / 2) (h.Cchi * h.Csum)
        (fun s _ => hatChiSq_row_sum_le h s S)
        (fun s _ => div_nonneg (mul_nonneg (sq_nonneg (c s)) (F.bp_nonneg (v s))) (by norm_num))
    have h2 : (∑ s ∈ S, ∑ s' ∈ S,
          |E.hatChiSq (s' - s)| * (c s' ^ 2 * F.bp (v s') (v s') / 2))
        ≤ (h.Cchi * h.Csum) * (∑ s ∈ S, c s ^ 2 * F.bp (v s) (v s) / 2) := by
      rw [Finset.sum_comm]
      exact double_sum_row_bound S (fun s' s => |E.hatChiSq (s' - s)|)
        (fun s' => c s' ^ 2 * F.bp (v s') (v s') / 2) (h.Cchi * h.Csum)
        (fun s' _ => hatChiSq_row_sum_le_swap h s' S)
        (fun s' _ => div_nonneg (mul_nonneg (sq_nonneg (c s')) (F.bp_nonneg (v s'))) (by norm_num))
    have h3 : (h.Cchi * h.Csum) * (∑ s ∈ S, c s ^ 2 * F.bp (v s) (v s) / 2)
        + (h.Cchi * h.Csum) * (∑ s ∈ S, c s ^ 2 * F.bp (v s) (v s) / 2)
        = (h.Cchi * h.Csum) * ∑ s ∈ S, c s ^ 2 * F.bp (v s) (v s) := by
      rw [← Finset.sum_div]
      ring
    linarith [h1, h2, h3]
  calc (∑ s ∈ S, ∑ s' ∈ S, c s * c s' * E.hatChiSq (s' - s) * F.bp (v s') (v s))
      ≤ (∑ s ∈ S, ∑ s' ∈ S, |E.hatChiSq (s' - s)| *
          (c s ^ 2 * F.bp (v s) (v s) + c s' ^ 2 * F.bp (v s') (v s')) / 2) :=
        Finset.sum_le_sum fun s _ => Finset.sum_le_sum fun s' _ => hpt s s'
    _ ≤ (h.Cchi * h.Csum) * ∑ s ∈ S, c s ^ 2 * F.bp (v s) (v s) := hsum
    _ ≤ K₀ * ∑ s ∈ S, c s ^ 2 * F.bp (v s) (v s) :=
        mul_le_mul_of_nonneg_right hD
          (Finset.sum_nonneg fun s _ =>
            mul_nonneg (sq_nonneg (c s)) (F.bp_nonneg (v s)))

end Work.BoseK15
