import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.FTS.EllipticEst.TT.WeakDefs
import Submission.Work.FTS.EllipticEst.TT.SliceDatum
import Submission.Work.FTS.EllipticEst.TT.HkMem_descend_open
import Submission.Work.FTS.EllipticEst.TT.bslOp_DzIter_eq
import Submission.Work.FTS.CoercivityStep.Norm.HkSq_mono_le
import Submission.Work.Spaces.HkSq_terms
import Submission.Work.Spaces.mixed_comm
import Submission.Work.Spaces.DzDthIterCommOn

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# Auxiliary definitions and pointwise bookkeeping for `EllEstUnif_step`

The induction step of Elgindi's Proposition `prop:Hk` is split here into

* the **exact recursion** of the two halves of `HkIntegrand` in the index `k`
  (`Zsum_succ`, `Msum_succ`): at level `k` the integrand is its level-`(k-1)` value, plus the
  *top diagonal* `i + j = k` of the mixed slots, plus the top radial slot;
* the **coarse pointwise comparison** `HkIntegrand_step_le` against the *shifted* integrand
  `HkIntegrand α (k-1) (D_z f)` — every slot of the top diagonal except the angular one
  `(mixed 0 k f · Wt)²` is a slot of the shifted integrand, and each single slot is dominated by
  the whole integrand (`Work.Spaces.sq_le_HkIntegrand_z`, `..._mixed`);
* the **reverse comparison** `HkIntegrand_shift_le`, expressing that shifting by `D_z` only
  removes slots.

Consequently the level-`k` norm is at most the level-`(k-1)` norm of `f`, the level-`(k-1)` norm
of `D_z f` and the single *top angular slot* `Tk α k f` — and it is precisely that last slot which
is the content of the paper's §"General ℋ^k case".
-/

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.EllipticEst.remov

set_option autoImplicit false

namespace Step

/-- The open quadrant, the domain on which the smoothness of the weak class is assumed. -/
def Qd : Set (ℝ × ℝ) := Set.Ioi 0 ×ˢ Set.Ioo 0 (Real.pi / 2)

theorem isOpen_Qd : IsOpen Qd := isOpen_Ioi.prod isOpen_Ioo

/-! ## The two halves of `HkIntegrand` and their recursion in `k` -/

/-- The weight `w(z)/sin(2θ)^{η/2}` of the pure `D_z`-slots of `HkIntegrand`. -/
def Zu (z θ : ℝ) : ℝ := Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2)

/-- The pure radial part `∑_{i ≤ k} (D_z^i f · Zu)²` of `HkIntegrand α k f`. -/
def Zsum (k : ℕ) (f : ℝ → ℝ → ℝ) (z θ : ℝ) : ℝ :=
  ∑ i ∈ Finset.range (k + 1), (Work.Spaces.DzIter i f z θ * Zu z θ) ^ 2

/-- The mixed part `∑_{1 ≤ i, i+j ≤ k} (D_z^j D_θ^i f · Wt)²` of `HkIntegrand α k f`. -/
def Msum (α : ℝ) (k : ℕ) (f : ℝ → ℝ → ℝ) (z θ : ℝ) : ℝ :=
  ∑ i ∈ Finset.range (k + 1), ∑ j ∈ Finset.range (k + 1),
    (if 1 ≤ i ∧ i + j ≤ k then (Work.Spaces.mixed j i f z θ * Work.Spaces.Wt α z θ) ^ 2 else 0)

/-- **The top angular slot at level `k`**: the single term of `HkIntegrand α k f` that involves
`k` angular derivatives and no radial derivative.  This is the quantity the paper's
§"General `ℋ^k` case" has to estimate. -/
def Tk (α : ℝ) (k : ℕ) (f : ℝ → ℝ → ℝ) : ℝ :=
  ∫ z in Work.Spaces.Iz, ∫ θ in Work.Spaces.Iθ,
    (Work.Spaces.mixed 0 k f z θ * Work.Spaces.Wt α z θ) ^ 2

/-- The top angular slot is nonnegative. -/
theorem Tk_nonneg (α : ℝ) (k : ℕ) (f : ℝ → ℝ → ℝ) : 0 ≤ Tk α k f :=
  integral_nonneg fun _ => integral_nonneg fun _ => sq_nonneg _

/-- `HkIntegrand` is the sum of its radial and its mixed half. -/
theorem HkIntegrand_eq (α : ℝ) (k : ℕ) (f : ℝ → ℝ → ℝ) (z θ : ℝ) :
    Work.Spaces.HkIntegrand α k f z θ = Zsum k f z θ + Msum α k f z θ := rfl

/-- **The pure radial part recurses in `k`** by adding the top slot `i = k`. -/
theorem Zsum_succ {k : ℕ} (hk : 1 ≤ k) (f : ℝ → ℝ → ℝ) (z θ : ℝ) :
    Zsum k f z θ = Zsum (k - 1) f z θ
      + (Work.Spaces.DzIter k f z θ * Zu z θ) ^ 2 := by
  have hk1 : k - 1 + 1 = k := by omega
  unfold Zsum
  rw [Finset.sum_range_succ]
  have hcongr : (∑ i ∈ Finset.range k,
        (Work.Spaces.DzIter i f z θ * Zu z θ) ^ 2)
      = ∑ i ∈ Finset.range (k - 1 + 1),
        (Work.Spaces.DzIter i f z θ * Zu z θ) ^ 2 :=
    Finset.sum_congr (by rw [hk1]) (fun _ _ => rfl)
  rw [hcongr]

/-- **The mixed part as a sum of rows**: the inner `j`-sum may be truncated at `k - i`
(the skipped slots carry the value `0`). -/
theorem Msum_eq_rows (α : ℝ) (k : ℕ) (f : ℝ → ℝ → ℝ) (z θ : ℝ) :
    Msum α k f z θ = ∑ i ∈ Finset.range (k + 1),
      ∑ j ∈ Finset.range (k + 1 - i),
        (if 1 ≤ i then (Work.Spaces.mixed j i f z θ * Work.Spaces.Wt α z θ) ^ 2 else 0) := by
  unfold Msum
  refine Finset.sum_congr rfl (fun i _ => ?_)
  have hsub : Finset.range (k + 1 - i) ⊆ Finset.range (k + 1) := by
    intro x hx
    exact Finset.mem_range.mpr (by have h := Finset.mem_range.mp hx; omega)
  have hzero : ∀ x ∈ Finset.range (k + 1), x ∉ Finset.range (k + 1 - i) →
      (if 1 ≤ i ∧ i + x ≤ k then
        (Work.Spaces.mixed x i f z θ * Work.Spaces.Wt α z θ) ^ 2 else 0) = 0 := by
    intro x _ hx'
    have hxk : ¬ (x < k + 1 - i) := fun h => hx' (Finset.mem_range.mpr h)
    rw [if_neg]
    intro hcon
    exact hxk (by omega)
  rw [← Finset.sum_subset hsub hzero]
  refine Finset.sum_congr rfl (fun j hj => ?_)
  have hjlt : j < k + 1 - i := Finset.mem_range.mp hj
  have hijk : i + j ≤ k := by omega
  by_cases hi' : 1 ≤ i
  · rw [if_pos ⟨hi', hijk⟩, if_pos hi']
  · rw [if_neg (fun h => hi' h.1), if_neg hi']

/-- **The mixed part recurses in `k`**: the `k - 1` mixed part, plus the top slot
`(i, j) = (k, 0)`, plus the diagonal `i + j = k` with `j ≥ 1`. -/
theorem Msum_succ {k : ℕ} (hk : 1 ≤ k) (α : ℝ) (f : ℝ → ℝ → ℝ) (z θ : ℝ) :
    Msum α k f z θ = Msum α (k - 1) f z θ
      + (Work.Spaces.mixed 0 k f z θ * Work.Spaces.Wt α z θ) ^ 2
      + ∑ i ∈ Finset.range k,
          (if 1 ≤ i then (Work.Spaces.mixed (k - i) i f z θ * Work.Spaces.Wt α z θ) ^ 2
            else 0) := by
  rw [Msum_eq_rows, Finset.sum_range_succ]
  have hkrow : (∑ j ∈ Finset.range (k + 1 - k),
        (if 1 ≤ k then (Work.Spaces.mixed j k f z θ * Work.Spaces.Wt α z θ) ^ 2 else 0))
      = (Work.Spaces.mixed 0 k f z θ * Work.Spaces.Wt α z θ) ^ 2 := by
    have h1 : k + 1 - k = 1 := by omega
    rw [h1, Finset.sum_range_one, if_pos hk]
  have hrows : ∀ i ∈ Finset.range k,
      (∑ j ∈ Finset.range (k + 1 - i),
        (if 1 ≤ i then (Work.Spaces.mixed j i f z θ * Work.Spaces.Wt α z θ) ^ 2 else 0))
      = (∑ j ∈ Finset.range (k - 1 + 1 - i),
          (if 1 ≤ i then (Work.Spaces.mixed j i f z θ * Work.Spaces.Wt α z θ) ^ 2 else 0))
        + (if 1 ≤ i then (Work.Spaces.mixed (k - i) i f z θ * Work.Spaces.Wt α z θ) ^ 2
            else 0) := by
    intro i hi
    have hik : i < k := Finset.mem_range.mp hi
    have h1 : k + 1 - i = (k - i) + 1 := by omega
    have h2 : k - 1 + 1 - i = k - i := by
      rw [show k - 1 + 1 = k from by omega]
    rw [h1, h2, Finset.sum_range_succ]
  rw [Finset.sum_congr rfl hrows, Finset.sum_add_distrib, hkrow]
  have hfirst : (∑ i ∈ Finset.range k,
        (∑ j ∈ Finset.range (k - 1 + 1 - i),
          (if 1 ≤ i then (Work.Spaces.mixed j i f z θ * Work.Spaces.Wt α z θ) ^ 2 else 0)))
      = Msum α (k - 1) f z θ := by
    rw [Msum_eq_rows]
    exact Finset.sum_congr (by rw [show k - 1 + 1 = k from by omega])
      (fun i _ => rfl)
  rw [hfirst]
  ring

/-! ## Iterated `D_z`, congruence on an open set, and the diagonal slots -/

/-- `D_z^n (D_z g) = D_z^{n+1} g`. -/
theorem DzIter_Dz (n : ℕ) (g : ℝ → ℝ → ℝ) :
    Work.Spaces.DzIter n (Work.Spaces.Dz g) = Work.Spaces.DzIter (n + 1) g := by
  induction n with
  | zero => rfl
  | succ m ih =>
      rw [Work.Spaces.DzIter_succ (n := m) (f := Work.Spaces.Dz g), ih]
      rfl

/-- `D_z^k f = D_z^{k-1}(D_z f)`. -/
theorem DzIter_eq_DzIter_Dz {k : ℕ} (hk : 1 ≤ k) (f : ℝ → ℝ → ℝ) :
    Work.Spaces.DzIter k f = Work.Spaces.DzIter (k - 1) (Work.Spaces.Dz f) := by
  have h := DzIter_Dz (k - 1) f
  have h1 : k - 1 + 1 = k := by omega
  rw [h1] at h
  exact h.symm

/-- Functions that agree on an open set have the same iterated `D_z` there. -/
theorem DzIter_congr_of_isOpen {g g' : ℝ → ℝ → ℝ} {V : Set (ℝ × ℝ)} (hV : IsOpen V)
    (h : Set.EqOn (Function.uncurry g) (Function.uncurry g') V) (j : ℕ) :
    Set.EqOn (Function.uncurry (Work.Spaces.DzIter j g))
      (Function.uncurry (Work.Spaces.DzIter j g')) V := by
  induction j with
  | zero => exact h
  | succ j ih =>
      intro y hy
      show y.1 * Work.Spaces.pz (Work.Spaces.DzIter j g) y.1 y.2
        = y.1 * Work.Spaces.pz (Work.Spaces.DzIter j g') y.1 y.2
      rw [Work.Spaces.pz_congr_of_isOpen hV ih hy]

/-- **The diagonal slots shift**: for `1 ≤ i` and `i ≤ k - 1` the slot `D_z^{k-i}D_θ^i f` of
level `k` is the slot `D_z^{k-1-i}D_θ^i (D_z f)` of the shifted integrand *at the same angular
index*. -/
theorem mixed_diag_apply {k i : ℕ} (hi : 1 ≤ i) (hik : i ≤ k - 1) (f : ℝ → ℝ → ℝ)
    {z θ : ℝ} (hz : 0 < z) (hθ : θ ∈ Set.Ioo 0 (Real.pi / 2))
    (hcd : ContDiffOn ℝ ⊤ (Function.uncurry f) Qd) :
    Work.Spaces.mixed (k - i) i f z θ
      = Work.Spaces.mixed (k - 1 - i) i (Work.Spaces.Dz f) z θ := by
  have h1 : k - i = k - 1 - i + 1 := by omega
  have hcomm : Set.EqOn (Function.uncurry (Work.Spaces.Dz (Work.Spaces.DthIter i f)))
      (Function.uncurry (Work.Spaces.DthIter i (Work.Spaces.Dz f))) Qd :=
    Work.Spaces.DzDthIterCommOn (V := Qd) isOpen_Qd hcd i
  have hpt : (z, θ) ∈ Qd := ⟨hz, hθ⟩
  show Work.Spaces.DzIter (k - i) (Work.Spaces.DthIter i f) z θ
    = Work.Spaces.DzIter (k - 1 - i) (Work.Spaces.DthIter i (Work.Spaces.Dz f)) z θ
  rw [h1, ← DzIter_Dz (k - 1 - i) (Work.Spaces.DthIter i f)]
  exact DzIter_congr_of_isOpen isOpen_Qd hcomm (k - 1 - i) hpt

/-! ## The coarse pointwise comparisons -/

/-- **The pointwise step**: the level-`k` integrand is bounded by the level-`(k-1)` integrand,
the `k`-fold shifted integrand and the single top angular slot. -/
theorem HkIntegrand_step_le {k : ℕ} (hk : 1 ≤ k) (α : ℝ) (f : ℝ → ℝ → ℝ)
    {z θ : ℝ} (hz : 0 < z) (hθ : θ ∈ Set.Ioo 0 (Real.pi / 2))
    (hcd : ContDiffOn ℝ ⊤ (Function.uncurry f) Qd) :
    Work.Spaces.HkIntegrand α k f z θ ≤
      Work.Spaces.HkIntegrand α (k - 1) f z θ
        + ((k : ℝ) + 1) * Work.Spaces.HkIntegrand α (k - 1) (Work.Spaces.Dz f) z θ
        + (Work.Spaces.mixed 0 k f z θ * Work.Spaces.Wt α z θ) ^ 2 := by
  have hHnn : 0 ≤ Work.Spaces.HkIntegrand α (k - 1) (Work.Spaces.Dz f) z θ :=
    Work.Spaces.HkIntegrand_nonneg α (k - 1) (Work.Spaces.Dz f) z θ
  have hzterm : (Work.Spaces.DzIter k f z θ * Zu z θ) ^ 2
      ≤ Work.Spaces.HkIntegrand α (k - 1) (Work.Spaces.Dz f) z θ := by
    rw [DzIter_eq_DzIter_Dz hk f]
    exact Work.Spaces.sq_le_HkIntegrand_z α (k - 1) (Work.Spaces.Dz f) z θ (k - 1) le_rfl
  have hD : (∑ i ∈ Finset.range k,
        (if 1 ≤ i then (Work.Spaces.mixed (k - i) i f z θ * Work.Spaces.Wt α z θ) ^ 2
          else 0))
      ≤ (k : ℝ) * Work.Spaces.HkIntegrand α (k - 1) (Work.Spaces.Dz f) z θ := by
    have hterm : ∀ i ∈ Finset.range k,
        (if 1 ≤ i then (Work.Spaces.mixed (k - i) i f z θ * Work.Spaces.Wt α z θ) ^ 2
          else 0)
          ≤ Work.Spaces.HkIntegrand α (k - 1) (Work.Spaces.Dz f) z θ := by
      intro i hi
      have hik : i ≤ k - 1 := by
        have := Finset.mem_range.mp hi
        omega
      by_cases hi1 : 1 ≤ i
      · rw [if_pos hi1]
        rw [mixed_diag_apply hi1 hik f hz hθ hcd]
        exact Work.Spaces.sq_le_HkIntegrand_mixed α (k - 1) (Work.Spaces.Dz f) z θ i
          (k - 1 - i) hi1 (by omega)
      · rw [if_neg hi1]
        exact hHnn
    refine le_trans (Finset.sum_le_sum hterm) ?_
    rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
  have hkey : (Work.Spaces.DzIter k f z θ * Zu z θ) ^ 2
      + (∑ i ∈ Finset.range k,
          (if 1 ≤ i then (Work.Spaces.mixed (k - i) i f z θ * Work.Spaces.Wt α z θ) ^ 2
            else 0))
      ≤ ((k : ℝ) + 1) * Work.Spaces.HkIntegrand α (k - 1) (Work.Spaces.Dz f) z θ := by
    nlinarith [hzterm, hD, hHnn]
  rw [HkIntegrand_eq α k f, HkIntegrand_eq α (k - 1) f,
    Zsum_succ hk f z θ, Msum_succ hk α f z θ]
  linarith [hkey]

/-- The shifted mixed slots: `D_z^j D_θ^i (D_z f) = D_z^{j+1}D_θ^i f`. -/
theorem mixed_shift_apply {j i : ℕ} (hi : 1 ≤ i) (f : ℝ → ℝ → ℝ)
    {z θ : ℝ} (hz : 0 < z) (hθ : θ ∈ Set.Ioo 0 (Real.pi / 2))
    (hcd : ContDiffOn ℝ ⊤ (Function.uncurry f) Qd) :
    Work.Spaces.mixed j i (Work.Spaces.Dz f) z θ = Work.Spaces.mixed (j + 1) i f z θ := by
  have hcomm : Set.EqOn (Function.uncurry (Work.Spaces.Dz (Work.Spaces.DthIter i f)))
      (Function.uncurry (Work.Spaces.DthIter i (Work.Spaces.Dz f))) Qd :=
    Work.Spaces.DzDthIterCommOn (V := Qd) isOpen_Qd hcd i
  have hpt : (z, θ) ∈ Qd := ⟨hz, hθ⟩
  have hcongr : Work.Spaces.DzIter j (Work.Spaces.DthIter i (Work.Spaces.Dz f)) z θ
      = Work.Spaces.DzIter j (Work.Spaces.Dz (Work.Spaces.DthIter i f)) z θ :=
    DzIter_congr_of_isOpen isOpen_Qd hcomm.symm j hpt
  show Work.Spaces.DzIter j (Work.Spaces.DthIter i (Work.Spaces.Dz f)) z θ
    = Work.Spaces.DzIter (j + 1) (Work.Spaces.DthIter i f) z θ
  rw [hcongr, DzIter_Dz j (Work.Spaces.DthIter i f)]



/-- **The shifted integrand is dominated by the level-`k` integrand** (coarse form: every
slot of the shifted integrand is a slot of the level-`k` integrand, and each single slot is
dominated by the whole integrand). -/
theorem HkIntegrand_shift_le (α : ℝ) {k : ℕ} (hk : 1 ≤ k) (f : ℝ → ℝ → ℝ)
    {z θ : ℝ} (hz : 0 < z) (hθ : θ ∈ Set.Ioo 0 (Real.pi / 2))
    (hcd : ContDiffOn ℝ ⊤ (Function.uncurry f) Qd) :
    Work.Spaces.HkIntegrand α (k - 1) (Work.Spaces.Dz f) z θ
      ≤ ((k : ℝ) + (k : ℝ) * (k : ℝ)) * Work.Spaces.HkIntegrand α k f z θ := by
  have hHnn : 0 ≤ Work.Spaces.HkIntegrand α k f z θ :=
    Work.Spaces.HkIntegrand_nonneg α k f z θ
  have hZ : Zsum (k - 1) (Work.Spaces.Dz f) z θ
      ≤ (k : ℝ) * Work.Spaces.HkIntegrand α k f z θ := by
    have hterm : ∀ i ∈ Finset.range k,
        (Work.Spaces.DzIter i (Work.Spaces.Dz f) z θ * Zu z θ) ^ 2
          ≤ Work.Spaces.HkIntegrand α k f z θ := by
      intro i hi
      have hik : i + 1 ≤ k := by
        have := Finset.mem_range.mp hi
        omega
      rw [DzIter_Dz i f]
      exact Work.Spaces.sq_le_HkIntegrand_z α k f z θ (i + 1) hik
    have h1 : Zsum (k - 1) (Work.Spaces.Dz f) z θ
        = ∑ i ∈ Finset.range k,
            (Work.Spaces.DzIter i (Work.Spaces.Dz f) z θ * Zu z θ) ^ 2 := by
      unfold Zsum
      exact Finset.sum_congr (by rw [show k - 1 + 1 = k from by omega])
        (fun i _ => rfl)
    rw [h1]
    calc (∑ i ∈ Finset.range k,
          (Work.Spaces.DzIter i (Work.Spaces.Dz f) z θ * Zu z θ) ^ 2)
        ≤ ∑ _i ∈ Finset.range k, Work.Spaces.HkIntegrand α k f z θ :=
          Finset.sum_le_sum hterm
      _ = (k : ℝ) * Work.Spaces.HkIntegrand α k f z θ := by
          rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
  have hM : Msum α (k - 1) (Work.Spaces.Dz f) z θ
      ≤ ((k : ℝ) * (k : ℝ)) * Work.Spaces.HkIntegrand α k f z θ := by
    rw [Msum_eq_rows, show k - 1 + 1 = k from by omega]
    have hterm : ∀ i ∈ Finset.range k,
        (∑ j ∈ Finset.range (k - i),
          (if 1 ≤ i then (Work.Spaces.mixed j i (Work.Spaces.Dz f) z θ
            * Work.Spaces.Wt α z θ) ^ 2 else 0))
          ≤ (k : ℝ) * Work.Spaces.HkIntegrand α k f z θ := by
      intro i hi
      have hstep : (∑ j ∈ Finset.range (k - i),
          (if 1 ≤ i then (Work.Spaces.mixed j i (Work.Spaces.Dz f) z θ
            * Work.Spaces.Wt α z θ) ^ 2 else 0))
          ≤ ∑ _j ∈ Finset.range (k - i), Work.Spaces.HkIntegrand α k f z θ := by
        refine Finset.sum_le_sum (fun j hj => ?_)
        by_cases hi1 : 1 ≤ i
        · rw [if_pos hi1]
          rw [mixed_shift_apply hi1 f hz hθ hcd]
          have hj' : i + (j + 1) ≤ k := by
            have := Finset.mem_range.mp hj
            omega
          exact Work.Spaces.sq_le_HkIntegrand_mixed α k f z θ i (j + 1) hi1 hj'
        · rw [if_neg hi1]
          exact hHnn
      refine le_trans hstep ?_
      rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
      have hcast : ((k - i : ℕ) : ℝ) ≤ (k : ℝ) := by
        have : k - i ≤ k := by omega
        exact_mod_cast this
      have hci : (0 : ℝ) ≤ ((k - i : ℕ) : ℝ) := by positivity
      nlinarith [hHnn, hcast, hci]
    refine le_trans (Finset.sum_le_sum hterm) ?_
    have hsum : (∑ _i ∈ Finset.range k, (k : ℝ) * Work.Spaces.HkIntegrand α k f z θ)
        = ((k : ℝ) * (k : ℝ)) * Work.Spaces.HkIntegrand α k f z θ := by
      rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
      ring
    exact hsum.le
  rw [HkIntegrand_eq α k f z θ] at hZ hM ⊢
  rw [HkIntegrand_eq α (k - 1) (Work.Spaces.Dz f) z θ]
  have hnn : 0 ≤ Zsum k f z θ + Msum α k f z θ := Work.Spaces.HkIntegrand_nonneg α k f z θ
  nlinarith [hZ, hM, hnn]

end Step

end Work.FTS.EllipticEst.remov
