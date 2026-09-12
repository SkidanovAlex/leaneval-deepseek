import Mathlib
import Submission.Work.Lattice.TopBlockIndex
import Submission.Work.Lattice.FlowRate

/-!
# The time-asymptotic flow rate of a wedge is its top-block eigenvalue

`Submission.FlowRate` pinches the norm of the flowed wedge `⋀^k a_t w` between the top-block
eigenvalue times the top-block norm and `(k+1)` times the top-block eigenvalue times `‖w‖`.  The
gap is the *constant*: the lower bound involves `‖blockElem w u'‖`, which may be much smaller
than `‖w‖`.  This module shows that the gap disappears as `t → ∞`:

**`eventually_norm_map_le_topBlock`**: for every `k`-vector `w ≠ 0` whose top block is `u'`,
there is `T` with, for all `t ≥ T`,

    ‖⋀^k a_t w‖ ≤ 2 · exp (t·σ_{u'}) · ‖blockElem w u'‖,

where `σ_u = -(k-u)/ℓ + u/(d-ℓ)` (`a_t = scaleMap (twoScale (e^{-t/ℓ}) (e^{t/(d-ℓ)}) ℓ)`).
Together with the one-sided lower bound of `Submission.FlowRate` this says that the exponential
growth rate of `t ↦ ‖⋀^k a_t w‖` is exactly the top-block eigenvalue: the *position*
`r = dim(realSpan w ⊓ L)` of a rank-`j` subgroup (`j - r = u'` by
`Submission.TopBlockIndex.isTopBlock_iMulti`) is the asymptotic flow invariant.

The proof splits the block expansion of `⋀^k a_t w`, discards the blocks above `u'` (they
vanish), factors out `exp (t·σ_{u'})` and observes that the remaining blocks contribute
`exp (t(σ_v - σ_{u'}))·‖block_v w‖`, whose exponents are strictly negative (the eigenvalues
decrease by `(1/ℓ + 1/(d-ℓ))` per unit of the block index) — so the rescaled block expansion
converges to `‖blockElem w u'‖ > 0`.
-/

noncomputable section

open Module exteriorPower InnerProductGeometry Real
open scoped BigOperators
set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 4000000

open Submission.ExteriorCoordinates
open Submission.DiagonalFlow
open Submission.WedgeBlocks
open Submission.FlowRate

namespace Submission.FlowRateAsymptotic

variable {d : ℕ}

/-- The common eigenvalue gap per unit of block index: `1/ℓ + 1/(d-ℓ)`. -/
def slope (ℓ : ℕ) : ℝ := 1 / (ℓ : ℝ) + 1 / ((d : ℝ) - (ℓ : ℝ))

/-- The log-eigenvalue of the block with `u` complement directions, in "slope form":
`σ_u = -k/ℓ + u·(1/ℓ + 1/(d-ℓ))`. -/
def sig (k ℓ : ℕ) (u : ℕ) : ℝ := -((k : ℝ) / ↑ℓ) + (u : ℝ) * slope (d := d) ℓ

lemma sig_sub_sig {k ℓ : ℕ} {v u : ℕ} (hvu : v ≤ u) :
    sig (d := d) k ℓ u - sig (d := d) k ℓ v = ((u - v : ℕ) : ℝ) * slope (d := d) ℓ := by
  have hcast : ((u - v : ℕ) : ℝ) = (u : ℝ) - (v : ℝ) := Nat.cast_sub hvu
  rw [sig, sig, hcast]
  ring

lemma slope_pos {ℓ : ℕ} (hℓ0 : 0 < ℓ) (hℓd : ℓ < d) : 0 < slope (d := d) ℓ := by
  have h1 : (0 : ℝ) < (ℓ : ℝ) := by exact_mod_cast hℓ0
  have h2 : (0 : ℝ) < (d : ℝ) - (ℓ : ℝ) := by
    have := (by exact_mod_cast hℓd : (ℓ : ℝ) < (d : ℝ)); linarith
  rw [slope]
  exact add_pos (by positivity) (by positivity)

lemma sig_strict {k ℓ : ℕ} (hℓ0 : 0 < ℓ) (hℓd : ℓ < d) {v u : ℕ} (hvu : v < u) (_huk : u ≤ k) :
    sig (d := d) k ℓ v < sig (d := d) k ℓ u := by
  have hgap := sig_sub_sig (d := d) (k := k) (ℓ := ℓ) (le_of_lt hvu)
  have hpos : 0 < ((u - v : ℕ) : ℝ) * slope (d := d) ℓ :=
    mul_pos (by exact_mod_cast Nat.sub_pos_of_lt hvu) (slope_pos hℓ0 hℓd)
  linarith [hgap]

/-- The "eigenvalue" form of `sig`, matching `Submission.FlowRate.eigen_exp`. -/
lemma sig_eq_eigen {k ℓ u : ℕ} (hℓ0 : 0 < ℓ) (hℓd : ℓ < d) (huk : u ≤ k) :
    sig (d := d) k ℓ u = -(((k - u : ℕ) : ℝ) / ↑ℓ) + ((u : ℝ) / ↑(d - ℓ)) := by
  have hℓne : (ℓ : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.pos_iff_ne_zero.mp hℓ0)
  have hdne : ((d : ℝ) - (ℓ : ℝ)) ≠ 0 := by
    have := (by exact_mod_cast hℓd : (ℓ : ℝ) < (d : ℝ)); linarith
  have hcast : ((k - u : ℕ) : ℝ) = (k : ℝ) - (u : ℝ) := Nat.cast_sub huk
  have hdm : ((d - ℓ : ℕ) : ℝ) = (d : ℝ) - (ℓ : ℝ) := Nat.cast_sub (le_of_lt hℓd)
  rw [sig, slope, hcast, hdm, div_eq_mul_inv, mul_add]
  rw [div_eq_mul_inv]
  field_simp
  ring

/-! ## Convergence of the block expansion -/

/-- Finite sums of convergent families converge (non-deprecated form). -/
lemma tendsto_finset_sum' {ι : Type*} {M : Type*} [AddCommMonoid M] [TopologicalSpace M]
    [ContinuousAdd M] {α : Type*} {s : Finset ι} {f : ι → α → M} {a : ι → M} {l : Filter α}
    (h : ∀ i ∈ s, Filter.Tendsto (f i) l (nhds (a i))) :
    Filter.Tendsto (fun x => ∑ i ∈ s, f i x) l (nhds (∑ i ∈ s, a i)) := by
  classical
  induction s using Finset.induction with
  | empty => simpa using tendsto_const_nhds
  | insert i s hi ih =>
      simp only [Finset.sum_insert hi]
      exact (h i (Finset.mem_insert_self i s)).add
        (ih (fun j hj => h j (Finset.mem_insert_of_mem hj)))

/-- `exp (t·c)·D → 0` as `t → +∞` for `c < 0`. -/
lemma tendsto_exp_mul_const_zero {c D : ℝ} (hc : c < 0) :
    Filter.Tendsto (fun t : ℝ => Real.exp (t * c) * D) Filter.atTop (nhds 0) := by
  have h1 : Filter.Tendsto (fun t : ℝ => t * (-c)) Filter.atTop Filter.atTop :=
    Filter.Tendsto.atTop_mul_const (neg_pos.mpr hc) Filter.tendsto_id
  have h2 : Filter.Tendsto (fun t : ℝ => Real.exp (-(t * (-c)))) Filter.atTop (nhds 0) :=
    Real.tendsto_exp_neg_atTop_nhds_zero.comp h1
  have h2' : Filter.Tendsto (fun t : ℝ => Real.exp (t * c)) Filter.atTop (nhds 0) := by
    refine h2.congr' ?_
    filter_upwards with t
    congr 1
    ring
  simpa using h2'.mul tendsto_const_nhds

/-! ## The asymptotic upper bound -/

/-- The block expansion of the flowed wedge, with each block-eigenvalue written as
`exp (t·σ_v)`. -/
lemma norm_map_le_block_sum {k ℓ : ℕ} (hℓ0 : 0 < ℓ) (hℓd : ℓ < d) (w : WK d k) {t : ℝ}
    (_ht : 0 ≤ t) :
    ‖exteriorPower.map k
        (scaleMap (twoScale (Real.exp (-t / ↑ℓ)) (Real.exp (t / ↑(d - ℓ))) ℓ)) w‖ ≤
      (Finset.range (k + 1)).sum (fun v =>
        Real.exp (t * sig (d := d) k ℓ v) *
          ‖blockElem (d := d) (k := k) (ℓ := ℓ) w v‖) := by
  have h := norm_map_le_sum_eigen (d := d) (k := k) (ℓ := ℓ)
    (Real.exp (-t / ↑ℓ)) (Real.exp (t / ↑(d - ℓ)))
    (le_of_lt (Real.exp_pos _)) (le_of_lt (Real.exp_pos _)) w
  refine h.trans ?_
  refine Finset.sum_le_sum (fun v hv => ?_)
  have hvk : v ≤ k := Nat.lt_succ_iff.mp (Finset.mem_range.mp hv)
  rw [eigen_exp (d := d) (k := k) (u := v) (ℓ := ℓ) hℓ0 hℓd t,
    sig_eq_eigen (d := d) hℓ0 hℓd hvk]

/-- The block expansion only involves the blocks up to the top block `u'`. -/
lemma block_sum_eq_top {k ℓ : ℕ} (w : WK d k) {u' : ℕ} (hu' : u' ≤ k)
    (htop : IsTopBlock (d := d) (ℓ := ℓ) w u') (t : ℝ) :
    (Finset.range (k + 1)).sum (fun v =>
        Real.exp (t * sig (d := d) k ℓ v) *
          ‖blockElem (d := d) (k := k) (ℓ := ℓ) w v‖) =
      (Finset.range (u' + 1)).sum (fun v =>
        Real.exp (t * sig (d := d) k ℓ v) *
          ‖blockElem (d := d) (k := k) (ℓ := ℓ) w v‖) := by
  refine (Finset.sum_subset ?_ ?_).symm
  · intro v hv
    simp only [Finset.mem_range] at hv ⊢
    omega
  · intro v hv hvnot
    simp only [Finset.mem_range] at hv hvnot
    rw [htop.2 v (by omega) (Nat.lt_succ_iff.mp hv), norm_zero, mul_zero]

/-- Factoring out the top-block eigenvalue from the block expansion. -/
lemma block_sum_factor {k ℓ : ℕ} (w : WK d k) (u' : ℕ) (t : ℝ) :
    (Finset.range (u' + 1)).sum (fun v =>
        Real.exp (t * sig (d := d) k ℓ v) *
          ‖blockElem (d := d) (k := k) (ℓ := ℓ) w v‖) =
      Real.exp (t * sig (d := d) k ℓ u') *
        (Finset.range (u' + 1)).sum (fun v =>
          Real.exp (t * (sig (d := d) k ℓ v - sig (d := d) k ℓ u')) *
            ‖blockElem (d := d) (k := k) (ℓ := ℓ) w v‖) := by
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl (fun v _ => ?_)
  have hfac : Real.exp (t * sig (d := d) k ℓ v) =
      Real.exp (t * sig (d := d) k ℓ u') *
        Real.exp (t * (sig (d := d) k ℓ v - sig (d := d) k ℓ u')) := by
    rw [← Real.exp_add]
    congr 1
    ring
  rw [hfac]
  ring

/-- **The rescaled block expansion converges to the top-block norm.** -/
lemma tendsto_rescaled {k ℓ : ℕ} (hℓ0 : 0 < ℓ) (hℓd : ℓ < d) (w : WK d k) {u' : ℕ}
    (hu' : u' ≤ k) :
    Filter.Tendsto (fun t : ℝ => (Finset.range (u' + 1)).sum (fun v =>
        Real.exp (t * (sig (d := d) k ℓ v - sig (d := d) k ℓ u')) *
          ‖blockElem (d := d) (k := k) (ℓ := ℓ) w v‖)) Filter.atTop
      (nhds ‖blockElem (d := d) (k := k) (ℓ := ℓ) w u'‖) := by
  classical
  have hsingle : ∀ v ∈ Finset.range (u' + 1),
      Filter.Tendsto (fun t : ℝ =>
          Real.exp (t * (sig (d := d) k ℓ v - sig (d := d) k ℓ u')) *
            ‖blockElem (d := d) (k := k) (ℓ := ℓ) w v‖) Filter.atTop
        (nhds (if v = u' then ‖blockElem (d := d) (k := k) (ℓ := ℓ) w u'‖ else 0)) := by
    intro v hv
    by_cases hv' : v = u'
    · subst hv'
      simp only [sub_self, mul_zero, Real.exp_zero, one_mul]
      exact tendsto_const_nhds
    · have hvu : v < u' := by
        simp only [Finset.mem_range] at hv
        omega
      have hsig : sig (d := d) k ℓ v - sig (d := d) k ℓ u' < 0 := by
        have := sig_strict (d := d) hℓ0 hℓd hvu hu'
        linarith
      have h := tendsto_exp_mul_const_zero
        (c := sig (d := d) k ℓ v - sig (d := d) k ℓ u')
        (D := ‖blockElem (d := d) (k := k) (ℓ := ℓ) w v‖) hsig
      simpa [if_neg hv'] using h
  have hsum := tendsto_finset_sum' (s := Finset.range (u' + 1)) hsingle
  have hval : (∑ v ∈ Finset.range (u' + 1),
      (if v = u' then ‖blockElem (d := d) (k := k) (ℓ := ℓ) w u'‖ else 0)) =
      ‖blockElem (d := d) (k := k) (ℓ := ℓ) w u'‖ := by
    rw [Finset.sum_ite_eq' (Finset.range (u' + 1)) u'
      (fun _ => ‖blockElem (d := d) (k := k) (ℓ := ℓ) w u'‖)]
    simp
  rwa [hval] at hsum

/-- **Asymptotic flow rate**: the flowed norm of a wedge is eventually at most twice the
top-block eigenvalue times the top-block norm. -/
theorem eventually_norm_map_le_topBlock {k ℓ : ℕ} (hℓ0 : 0 < ℓ) (hℓd : ℓ < d) (w : WK d k)
    {u' : ℕ} (hu' : u' ≤ k) (htop : IsTopBlock (d := d) (ℓ := ℓ) w u') :
    ∃ T : ℝ, ∀ t : ℝ, T ≤ t →
      ‖exteriorPower.map k
          (scaleMap (twoScale (Real.exp (-t / ↑ℓ)) (Real.exp (t / ↑(d - ℓ))) ℓ)) w‖ ≤
        2 * Real.exp (t * sig (d := d) k ℓ u') *
          ‖blockElem (d := d) (k := k) (ℓ := ℓ) w u'‖ := by
  classical
  have hβu_pos : 0 < ‖blockElem (d := d) (k := k) (ℓ := ℓ) w u'‖ :=
    norm_pos_iff.mpr htop.1
  have htend := tendsto_rescaled (d := d) (k := k) (ℓ := ℓ) hℓ0 hℓd w hu'
  have hev : ∀ᶠ t : ℝ in Filter.atTop,
      (Finset.range (u' + 1)).sum (fun v =>
          Real.exp (t * (sig (d := d) k ℓ v - sig (d := d) k ℓ u')) *
            ‖blockElem (d := d) (k := k) (ℓ := ℓ) w v‖) ≤
        2 * ‖blockElem (d := d) (k := k) (ℓ := ℓ) w u'‖ := by
    have h1 : ∀ᶠ t : ℝ in Filter.atTop,
        (Finset.range (u' + 1)).sum (fun v =>
            Real.exp (t * (sig (d := d) k ℓ v - sig (d := d) k ℓ u')) *
              ‖blockElem (d := d) (k := k) (ℓ := ℓ) w v‖) <
          2 * ‖blockElem (d := d) (k := k) (ℓ := ℓ) w u'‖ :=
      htend.eventually_lt_const (by linarith)
    exact h1.mono (fun x hx => le_of_lt hx)
  obtain ⟨T₀, hT₀⟩ := Filter.eventually_atTop.mp hev
  refine ⟨max T₀ 0, fun t ht => ?_⟩
  have ht0 : 0 ≤ t := le_trans (le_max_right _ _) ht
  have htT₀ : T₀ ≤ t := le_trans (le_max_left _ _) ht
  have hb := norm_map_le_block_sum (d := d) hℓ0 hℓd w ht0
  calc ‖exteriorPower.map k
        (scaleMap (twoScale (Real.exp (-t / ↑ℓ)) (Real.exp (t / ↑(d - ℓ))) ℓ)) w‖
      ≤ (Finset.range (k + 1)).sum (fun v =>
          Real.exp (t * sig (d := d) k ℓ v) *
            ‖blockElem (d := d) (k := k) (ℓ := ℓ) w v‖) := hb
    _ = (Finset.range (u' + 1)).sum (fun v =>
          Real.exp (t * sig (d := d) k ℓ v) *
            ‖blockElem (d := d) (k := k) (ℓ := ℓ) w v‖) :=
        block_sum_eq_top w hu' htop t
    _ = Real.exp (t * sig (d := d) k ℓ u') *
        (Finset.range (u' + 1)).sum (fun v =>
          Real.exp (t * (sig (d := d) k ℓ v - sig (d := d) k ℓ u')) *
            ‖blockElem (d := d) (k := k) (ℓ := ℓ) w v‖) :=
        block_sum_factor w u' t
    _ ≤ Real.exp (t * sig (d := d) k ℓ u') *
        (2 * ‖blockElem (d := d) (k := k) (ℓ := ℓ) w u'‖) :=
        mul_le_mul_of_nonneg_left (hT₀ t htT₀) (le_of_lt (Real.exp_pos _))
    _ = 2 * Real.exp (t * sig (d := d) k ℓ u') *
        ‖blockElem (d := d) (k := k) (ℓ := ℓ) w u'‖ := by ring

end Submission.FlowRateAsymptotic
