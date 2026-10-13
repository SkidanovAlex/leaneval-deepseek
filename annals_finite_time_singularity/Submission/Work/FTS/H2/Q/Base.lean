/-
Copyright: work module for the Elgindi finite-time singularity project.

# The base layer of `WtoHQ`: the calculus of `D_z` and `D_θ` in the genuine smooth order

`Work.Elliptic.WtoH` (Proposition `WtoH` of Elgindi, tex 1237) is proved for functions which
are *analytic* on a neighbourhood of the closed quadrant (`Work.Spaces.SmoothNbhd`, i.e.
`ContDiffOn ℝ ⊤` where `⊤ : WithTop ℕ∞` is the analytic order).  The objects of the actual
construction are only `C^∞` on the *open* quadrant (`Work.FTS.LocData.SmoothQuad`, the genuine
smooth order `Work.Stability.smoothOrder`), so none of the `⊤`-lemmas apply to them.

This file re-proves the *calculus* layer of the `WtoH` proof at the genuine smooth order:

* the Leibniz rules for `∂_z^k` (`pzIter_mul_local_sm`, and the two polynomial instances
  `pzIter_sq_mul_sm`, `pzIter_three_mul_sm` used in the substitution `f = z² k`);
* the Stirling expansion `D_z^n h = ∑_k S(n,k) z^k ∂_z^k h` and its consequence
  `|w(z) D_z^i h| ≤ 100 M` from `|w(z) z^k ∂_z^k h| ≤ M` (`DzIter_eq_sum_scoef_sm`,
  `abs_w_DzIter_le_sm`);
* the triangular estimate `tri_bound_sm` (the exact analogue of `Work.Elliptic.tri_bound`);
* the smoothness of the `z`-slices of `divZ2 f = f/z²` and of its `D_θ`-iterates on the open
  quadrant, together with the two Leibniz expansions `∂_z^m f = z²∂_z^m k + …`
  (`pzIter_divZ2_expansion_aux_sm`, `expand_aux_sm`).

All statements are on the **open** quadrant `(0,∞) × (0,π/2)` for the angular variable: the
boundary lines `θ = 0, π/2` carry no regularity hypothesis in `SmoothQuad`.
-/
import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Algebra.Ring.IsFormallyReal
import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.Analysis.Calculus.IteratedDeriv.Lemmas
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Submission.Work.FTS.H2.Qd
import Submission.Work.FTS.Vocab
import Submission.Work.FTS.H2.Defs
import Submission.Work.FTS.LocData.SmoothChain
import Submission.Work.Elliptic.WtoHAux

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.H2.Q

open Work.Spaces


set_option autoImplicit false
set_option maxHeartbeats 1600000

/-! ## Two order bookkeeping helpers -/

/-- Transport of `ContDiffAt` from the analytic order `⊤` down to the genuine smooth order. -/
theorem contDiffAt_sm_of_top {f : ℝ → ℝ} {x : ℝ}
    (h : ContDiffAt ℝ (⊤ : WithTop ℕ∞) f x) :
    ContDiffAt ℝ Work.Stability.smoothOrder f x :=
  h.of_le (by simp [Work.Stability.smoothOrder])

/-- Transport of `ContDiffOn` from the analytic order `⊤` down to the genuine smooth order. -/
theorem contDiffOn_sm_of_top {f : ℝ → ℝ} {s : Set ℝ}
    (h : ContDiffOn ℝ (⊤ : WithTop ℕ∞) f s) :
    ContDiffOn ℝ Work.Stability.smoothOrder f s :=
  h.of_le (by simp [Work.Stability.smoothOrder])

/-- `deriv` preserves `C^∞`-smoothness on an open set, at the genuine smooth order. -/
theorem contDiffOn_deriv_sm {u : ℝ → ℝ} {s : Set ℝ}
    (h : ContDiffOn ℝ Work.Stability.smoothOrder u s) (hs : IsOpen s) :
    ContDiffOn ℝ Work.Stability.smoothOrder (deriv u) s :=
  h.deriv_of_isOpen hs (by simp [Work.Stability.smoothOrder])

/-! ## Leibniz rules at the genuine smooth order -/

/-- Leibniz rule for `∂_z^k` of a product, at a point where both `z`-slices are `C^∞` in the
genuine smooth order.  (The `⊤`-version is `Work.Elliptic.pzIter_mul_local`.) -/
theorem pzIter_mul_local_sm (k : ℕ) {u v : ℝ → ℝ → ℝ} {z θ : ℝ}
    (hu : ContDiffAt ℝ Work.Stability.smoothOrder (fun z' => u z' θ) z)
    (hv : ContDiffAt ℝ Work.Stability.smoothOrder (fun z' => v z' θ) z) :
    pzIter k (fun z θ => u z θ * v z θ) z θ
      = ∑ c ∈ Finset.range (k + 1),
          (k.choose c : ℝ) * (pzIter c u z θ * pzIter (k - c) v z θ) := by
  rw [pzIter_eq_iteratedDeriv k (fun z θ => u z θ * v z θ) z θ]
  have hfun : (fun z' => (fun z θ => u z θ * v z θ) z' θ)
      = (fun z' => u z' θ) * (fun z' => v z' θ) := rfl
  rw [hfun, iteratedDeriv_mul (hu.of_le (by simp [Work.Stability.smoothOrder]))
    (hv.of_le (by simp [Work.Stability.smoothOrder]))]
  refine Finset.sum_congr rfl fun c _ => ?_
  rw [← pzIter_eq_iteratedDeriv c u z θ, ← pzIter_eq_iteratedDeriv (k - c) v z θ]
  ring

/-- `∂_z^m (z² κ) = z² ∂_z^m κ + 2m z ∂_z^{m-1} κ + m(m-1) ∂_z^{m-2} κ` for `m ≤ 4`, at a
point where the `z`-slice of `κ` is `C^∞`.  (The `⊤`-version is
`Work.Elliptic.pzIter_sq_mul`.) -/
theorem pzIter_sq_mul_sm (m : ℕ) (hm : m ≤ 4) {κ : ℝ → ℝ → ℝ} {z θ : ℝ}
    (hκ : ContDiffAt ℝ Work.Stability.smoothOrder (fun z' => κ z' θ) z) :
    pzIter m (fun z θ => z ^ 2 * κ z θ) z θ
      = z ^ 2 * pzIter m κ z θ + (2 * (m : ℝ)) * z * pzIter (m - 1) κ z θ
        + ((m : ℝ) * ((m : ℝ) - 1)) * pzIter (m - 2) κ z θ := by
  have hu : ContDiffAt ℝ Work.Stability.smoothOrder (fun z' : ℝ => z' ^ 2) z :=
    contDiffAt_sm_of_top (contDiffAt_id.pow 2)
  have h := pzIter_mul_local_sm (u := fun z _ => z ^ 2) (v := κ) m hu hκ
  rcases m with _ | _ | _ | _ | _ | m
  · rw [h, Finset.sum_range_one]
    simp
  · rw [h, Finset.sum_range_succ, Finset.sum_range_one]
    simp only [pzIter_zero, Work.Elliptic.pzIter_one_sq, Work.Elliptic.pzIter_two_sq]
    norm_num [Nat.choose]
  · rw [h, Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_one]
    simp only [pzIter_zero, Work.Elliptic.pzIter_one_sq, Work.Elliptic.pzIter_two_sq,
      Work.Elliptic.pzIter_three_sq]
    norm_num [Nat.choose]
    ring
  · rw [h, Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_succ,
      Finset.sum_range_one]
    simp only [pzIter_zero, Work.Elliptic.pzIter_one_sq, Work.Elliptic.pzIter_two_sq,
      Work.Elliptic.pzIter_three_sq, Work.Elliptic.pzIter_four_sq]
    norm_num [Nat.choose]
    ring
  · rw [h, Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_succ,
      Finset.sum_range_succ, Finset.sum_range_one]
    simp only [pzIter_zero, Work.Elliptic.pzIter_one_sq, Work.Elliptic.pzIter_two_sq,
      Work.Elliptic.pzIter_three_sq, Work.Elliptic.pzIter_four_sq]
    norm_num [Nat.choose]
    ring
  · omega

/-- `∂_z^m ((1+z)³ κ) = (1+z)³∂_z^mκ + 3m(1+z)²∂_z^{m-1}κ + 3m(m-1)(1+z)∂_z^{m-2}κ
+ m(m-1)(m-2)∂_z^{m-3}κ` for `m ≤ 4`, at a point where the `z`-slice of `κ` is `C^∞`.  (The
`⊤`-version is `Work.Elliptic.pzIter_three_mul`.) -/
theorem pzIter_three_mul_sm (m : ℕ) (hm : m ≤ 4) {κ : ℝ → ℝ → ℝ} {z θ : ℝ}
    (hκ : ContDiffAt ℝ Work.Stability.smoothOrder (fun z' => κ z' θ) z) :
    pzIter m (fun z θ => (z + 1) ^ 3 * κ z θ) z θ
      = (z + 1) ^ 3 * pzIter m κ z θ
        + (3 * (m : ℝ)) * (z + 1) ^ 2 * pzIter (m - 1) κ z θ
        + (3 * (m : ℝ) * ((m : ℝ) - 1)) * (z + 1) * pzIter (m - 2) κ z θ
        + ((m : ℝ) * ((m : ℝ) - 1) * ((m : ℝ) - 2)) * pzIter (m - 3) κ z θ := by
  have hu : ContDiffAt ℝ Work.Stability.smoothOrder (fun z' : ℝ => (z' + 1) ^ 3) z :=
    contDiffAt_sm_of_top ((contDiffAt_id.add contDiffAt_const).pow 3)
  have h := pzIter_mul_local_sm (u := fun z _ => (z + 1) ^ 3) (v := κ) m hu hκ
  rcases m with _ | _ | _ | _ | _ | m
  · rw [h, Finset.sum_range_one]
    simp
  · rw [h, Finset.sum_range_succ, Finset.sum_range_one]
    simp only [pzIter_zero, Work.Elliptic.pzIter_one_cube, Work.Elliptic.pzIter_two_cube]
    norm_num [Nat.choose]
  · rw [h, Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_one]
    simp only [pzIter_zero, Work.Elliptic.pzIter_one_cube, Work.Elliptic.pzIter_two_cube,
      Work.Elliptic.pzIter_three_cube]
    norm_num [Nat.choose]
    ring
  · rw [h, Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_succ,
      Finset.sum_range_one]
    simp only [pzIter_zero, Work.Elliptic.pzIter_one_cube, Work.Elliptic.pzIter_two_cube,
      Work.Elliptic.pzIter_three_cube, Work.Elliptic.pzIter_four_cube]
    norm_num [Nat.choose]
    ring
  · rw [h, Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_succ,
      Finset.sum_range_succ, Finset.sum_range_one]
    simp only [pzIter_zero, Work.Elliptic.pzIter_one_cube, Work.Elliptic.pzIter_two_cube,
      Work.Elliptic.pzIter_three_cube, Work.Elliptic.pzIter_four_cube]
    norm_num [Nat.choose]
    ring
  · omega

/-! ## The Stirling expansion of `D_z^n`, in the genuine smooth order -/

/-- If the `z`-slice `z ↦ h z θ` is `C^∞` on `(-1,∞)`, then so is each of its iterated
`z`-derivatives.  (The `⊤`-version is `Work.Spaces.pzIter_slice_contDiff`.) -/
theorem pzIter_slice_contDiff_sm {h : ℝ → ℝ → ℝ} {θ : ℝ}
    (hsmooth : ContDiffOn ℝ Work.Stability.smoothOrder (fun z => h z θ) (Set.Ioi (-1))) :
    ∀ k : ℕ, ContDiffOn ℝ Work.Stability.smoothOrder (fun z' => pzIter k h z' θ)
      (Set.Ioi (-1)) := by
  intro k
  induction k with
  | zero => simpa using hsmooth
  | succ n ih =>
    have h : ContDiffOn ℝ Work.Stability.smoothOrder
        (deriv (fun z' => pzIter n h z' θ)) (Set.Ioi (-1)) :=
      contDiffOn_deriv_sm ih isOpen_Ioi
    simpa [pzIter_succ, pz] using h

/-- Differentiability at an interior point of the `z`-slices of the iterated `z`-derivatives
of `h`, at the genuine smooth order. -/
theorem differentiableAt_pzIter_slice_sm {h : ℝ → ℝ → ℝ} {θ : ℝ}
    (hsmooth : ContDiffOn ℝ Work.Stability.smoothOrder (fun z => h z θ) (Set.Ioi (-1)))
    (k : ℕ) {z : ℝ} (hz : z ∈ Set.Ioi (-1)) :
    DifferentiableAt ℝ (fun z' => pzIter k h z' θ) z :=
  ((pzIter_slice_contDiff_sm hsmooth k).contDiffAt (isOpen_Ioi.mem_nhds hz)).differentiableAt
    Work.FTS.LocData.smoothOrder_ne_zero

/-! Three elementary `z`-calculus facts (private in `Work.Spaces.DzIter_le_of_pzIter`, hence
copied here). -/

private theorem deriv_zpow_sm (k : ℕ) (z : ℝ) :
    deriv (fun z' : ℝ => z' ^ k) z = (k : ℝ) * z ^ (k - 1) := by
  have h := deriv_pow (f := fun z' : ℝ => z') (x := z) differentiableAt_id k
  rw [show (fun z' : ℝ => z') ^ k = (fun z' : ℝ => z' ^ k) from rfl] at h
  have h1 : deriv (fun z' : ℝ => z') z = 1 := deriv_id z
  rw [h, h1]
  ring

private theorem deriv_pzIter_slice_sm (k : ℕ) (h : ℝ → ℝ → ℝ) (z θ : ℝ) :
    deriv (fun z' => pzIter k h z' θ) z = pzIter (k + 1) h z θ := rfl

private theorem z_mul_term_sm (k : ℕ) (z A B : ℝ) :
    z * ((k : ℝ) * z ^ (k - 1) * A + z ^ k * B)
      = (k : ℝ) * z ^ k * A + z ^ (k + 1) * B := by
  rcases k with _ | m
  · ring
  · rw [pow_succ]; push_cast; ring

/-- **The expansion of `D_z = z ∂_z` in terms of the Stirling numbers**, at the genuine smooth
order: for a function whose `z`-slices are `C^∞` on `(-1,∞)`,
`D_z^n h = ∑_{k≤n} S(n,k) z^k ∂_z^k h` on `(-1,∞) × ℝ`.  (The `⊤`-version is
`Work.Spaces.DzIter_eq_sum_scoef`.) -/
theorem DzIter_eq_sum_scoef_sm {h : ℝ → ℝ → ℝ} {θ : ℝ}
    (hsmooth : ContDiffOn ℝ Work.Stability.smoothOrder (fun z => h z θ) (Set.Ioi (-1))) :
    ∀ n : ℕ, ∀ z ∈ Set.Ioi (-1),
      DzIter n h z θ = ∑ k ∈ Finset.range (n + 1),
        (scoef n k : ℝ) * (z ^ k * pzIter k h z θ) := by
  intro n
  induction n with
  | zero =>
    intro z hz
    simp [DzIter, scoef]
  | succ n ih =>
    intro z hz
    have hdiff : ∀ k : ℕ, DifferentiableAt ℝ (fun z' => pzIter k h z' θ) z := fun k =>
      differentiableAt_pzIter_slice_sm hsmooth k hz
    have hd1 : ∀ k : ℕ, DifferentiableAt ℝ (fun z' : ℝ => z' ^ k) z := fun k =>
      differentiableAt_pow k
    have hd3 : ∀ k : ℕ, DifferentiableAt ℝ (fun z' : ℝ => z' ^ k * pzIter k h z' θ) z :=
      fun k => (hd1 k).mul (hdiff k)
    have hev : (fun z' => DzIter n h z' θ)
        =ᶠ[𝓝 z] (fun z' => ∑ k ∈ Finset.range (n + 1),
            (scoef n k : ℝ) * (z' ^ k * pzIter k h z' θ)) := by
      filter_upwards [isOpen_Ioi.mem_nhds hz] with z' hz'
      exact ih z' hz'
    have hterm : ∀ k : ℕ, deriv (fun z' : ℝ => (scoef n k : ℝ) * (z' ^ k * pzIter k h z' θ)) z
        = (scoef n k : ℝ) * ((k : ℝ) * z ^ (k - 1) * pzIter k h z θ
            + z ^ k * pzIter (k + 1) h z θ) := by
      intro k
      rw [deriv_const_mul (d := fun z' : ℝ => z' ^ k * pzIter k h z' θ)
        (scoef n k : ℝ) (hd3 k)]
      congr 1
      have hmul := deriv_mul (c := fun z' : ℝ => z' ^ k)
        (d := fun z' : ℝ => pzIter k h z' θ) (hd1 k) (hdiff k)
      have hmul' : deriv (fun z' : ℝ => z' ^ k * pzIter k h z' θ) z
          = deriv (fun z' : ℝ => z' ^ k) z * pzIter k h z θ
            + z ^ k * deriv (fun z' : ℝ => pzIter k h z' θ) z := hmul
      rw [hmul', deriv_zpow_sm, deriv_pzIter_slice_sm]
    have hderiv : deriv (fun z' => DzIter n h z' θ) z
        = ∑ k ∈ Finset.range (n + 1),
            (scoef n k : ℝ) * ((k : ℝ) * z ^ (k - 1) * pzIter k h z θ
              + z ^ k * pzIter (k + 1) h z θ) := by
      rw [Filter.EventuallyEq.deriv_eq hev]
      have hsumfun : (fun z' => ∑ k ∈ Finset.range (n + 1),
            (scoef n k : ℝ) * (z' ^ k * pzIter k h z' θ))
          = (∑ k ∈ Finset.range (n + 1),
              fun z' => (scoef n k : ℝ) * (z' ^ k * pzIter k h z' θ)) := by
        funext z'
        simp [Finset.sum_apply]
      rw [hsumfun, deriv_sum (fun k hk => (hd3 k).const_mul (scoef n k : ℝ))]
      exact Finset.sum_congr rfl fun k hk => hterm k
    calc DzIter (n + 1) h z θ
        = z * deriv (fun z' => DzIter n h z' θ) z := by simp [DzIter_succ, Dz, pz]
      _ = z * (∑ k ∈ Finset.range (n + 1),
            (scoef n k : ℝ) * ((k : ℝ) * z ^ (k - 1) * pzIter k h z θ
              + z ^ k * pzIter (k + 1) h z θ)) := by rw [hderiv]
      _ = ∑ k ∈ Finset.range (n + 1),
            (scoef n k : ℝ) * ((k : ℝ) * z ^ k * pzIter k h z θ
              + z ^ (k + 1) * pzIter (k + 1) h z θ) := by
          rw [Finset.mul_sum]
          refine Finset.sum_congr rfl fun k hk => ?_
          have h1 : z * ((scoef n k : ℝ) * ((k : ℝ) * z ^ (k - 1) * pzIter k h z θ
                + z ^ k * pzIter (k + 1) h z θ))
              = (scoef n k : ℝ) * (z * ((k : ℝ) * z ^ (k - 1) * pzIter k h z θ
                + z ^ k * pzIter (k + 1) h z θ)) := by ring
          rw [h1, z_mul_term_sm]
      _ = ∑ j ∈ Finset.range (n + 2), (scoef (n + 1) j : ℝ) * (z ^ j * pzIter j h z θ) :=
          Work.Spaces.scoef_sum_shift n (fun k => pzIter k h z θ) z

/-- **`D_z`-derivatives are bounded by the `z^j ∂_z^j`-bounds**, at the genuine smooth order:
if `|w(z)·z^j ∂_z^j h| ≤ M` for `j ≤ i ≤ 4` at `(z,θ)`, then `|w(z)·D_z^i h| ≤ 100 M`.  (The
`⊤`-version is `Work.Elliptic.abs_w_DzIter_le`.) -/
theorem abs_w_DzIter_le_sm {h : ℝ → ℝ → ℝ} {z θ M : ℝ} {i : ℕ}
    (hsmooth : ContDiffOn ℝ Work.Stability.smoothOrder (fun z => h z θ) (Set.Ioi (-1)))
    (hz : z ∈ Set.Ioi (-1)) (hM : 0 ≤ M) (hi : i ≤ 4)
    (hbound : ∀ k ≤ i, |w z * (z ^ k * pzIter k h z θ)| ≤ M) :
    |w z * DzIter i h z θ| ≤ 100 * M := by
  have h1 : w z * DzIter i h z θ
      = ∑ k ∈ Finset.range (i + 1),
          (scoef i k : ℝ) * (w z * (z ^ k * pzIter k h z θ)) := by
    rw [DzIter_eq_sum_scoef_sm hsmooth i z hz, Finset.mul_sum]
    refine Finset.sum_congr rfl fun k _ => ?_
    ring
  rw [h1]
  calc |∑ k ∈ Finset.range (i + 1), (scoef i k : ℝ) * (w z * (z ^ k * pzIter k h z θ))|
      ≤ (bell i : ℝ) * M :=
        abs_sum_scoef_mul_le i M _ (fun k hk => hbound k hk)
    _ ≤ 100 * M := mul_le_mul_of_nonneg_right (by exact_mod_cast bell_le i hi) hM

/-! ## The triangular estimate at the genuine smooth order -/

/-- **The triangular estimate**, at the genuine smooth order (the exact analogue of
`Work.Elliptic.tri_bound`, whose hypothesis on `κ` is analyticity).  If
`G = (z+1)³ κ` and `|(z+1)^j ∂_z^j G| ≤ Λ` for `j ≤ J` (`J ≤ 4`) at a point with `z > 0`, then
`|(z+1)^{j+3} ∂_z^j κ| ≤ 6000 Λ` for `j ≤ J`. -/
theorem tri_bound_sm {G κ : ℝ → ℝ → ℝ} (hG : G = fun z θ => (z + 1) ^ 3 * κ z θ)
    {z θ Λ : ℝ} {J : ℕ} (hJ : J ≤ 4) (hz : 0 < z)
    (hκ : ContDiffAt ℝ Work.Stability.smoothOrder (fun z' => κ z' θ) z)
    (hbound : ∀ j ≤ J, |(z + 1) ^ j * pzIter j G z θ| ≤ Λ) :
    ∀ j ≤ J, |(z + 1) ^ (j + 3) * pzIter j κ z θ| ≤ 6000 * Λ := by
  have hΛ : 0 ≤ Λ := le_trans (abs_nonneg _) (hbound 0 (Nat.zero_le J))
  set B : ℕ → ℝ := fun k => (z + 1) ^ (k + 3) * pzIter k κ z θ with hB
  set Gv : ℕ → ℝ := fun k => (z + 1) ^ k * pzIter k G z θ with hGv
  have hid0 : Gv 0 = B 0 := by
    have h := pzIter_three_mul_sm (κ := κ) 0 (by norm_num) hκ
    simp only [hGv, hG, hB, h]
    ring
  have hid1 : Gv 1 = B 1 + 3 * B 0 := by
    have h := pzIter_three_mul_sm (κ := κ) 1 (by norm_num) hκ
    simp only [hGv, hG, hB, h]
    ring
  have hid2 : Gv 2 = B 2 + 6 * B 1 + 6 * B 0 := by
    have h := pzIter_three_mul_sm (κ := κ) 2 (by norm_num) hκ
    simp only [hGv, hG, hB, h]
    ring
  have hid3 : Gv 3 = B 3 + 9 * B 2 + 18 * B 1 + 6 * B 0 := by
    have h := pzIter_three_mul_sm (κ := κ) 3 (by norm_num) hκ
    simp only [hGv, hG, hB, h]
    ring
  have hid4 : Gv 4 = B 4 + 12 * B 3 + 36 * B 2 + 24 * B 1 := by
    have h := pzIter_three_mul_sm (κ := κ) 4 (by norm_num) hκ
    simp only [hGv, hG, hB, h]
    ring
  have hGk : ∀ k ≤ J, |Gv k| ≤ Λ := by
    intro k hk
    rw [hGv]
    simpa using hbound k hk
  have b0 : |B 0| ≤ Λ := by rw [← hid0]; exact hGk 0 (Nat.zero_le J)
  have b1 (hJ1 : 1 ≤ J) : |B 1| ≤ 4 * Λ := by
    have h1 : B 1 = Gv 1 - 3 * B 0 := by linarith [hid1]
    have hA : |3 * B 0| = 3 * |B 0| := by rw [abs_mul, abs_of_nonneg (by norm_num)]
    calc |B 1| = |Gv 1 - 3 * B 0| := by rw [h1]
      _ ≤ |Gv 1| + |3 * B 0| := abs_sub _ _
      _ = |Gv 1| + 3 * |B 0| := by rw [hA]
      _ ≤ Λ + 3 * Λ := add_le_add (hGk 1 hJ1) (by linarith [b0])
      _ = 4 * Λ := by ring
  have b2 (hJ2 : 2 ≤ J) : |B 2| ≤ 31 * Λ := by
    have h2 : B 2 = Gv 2 - 6 * B 1 - 6 * B 0 := by linarith [hid2]
    have hA : |6 * B 1| = 6 * |B 1| := by rw [abs_mul, abs_of_nonneg (by norm_num)]
    have hB' : |6 * B 0| = 6 * |B 0| := by rw [abs_mul, abs_of_nonneg (by norm_num)]
    calc |B 2| = |Gv 2 - 6 * B 1 - 6 * B 0| := by rw [h2]
      _ ≤ |Gv 2| + 6 * |B 1| + 6 * |B 0| := by
          refine le_trans (Work.Elliptic.abs_three_le _ _ _) ?_
          rw [hA, hB']
      _ ≤ Λ + 6 * (4 * Λ) + 6 * Λ := by
          refine add_le_add (add_le_add (hGk 2 hJ2) ?_) ?_
          · linarith [b1 (by omega)]
          · linarith [b0]
      _ = 31 * Λ := by ring
  have b3 (hJ3 : 3 ≤ J) : |B 3| ≤ 358 * Λ := by
    have h3 : B 3 = Gv 3 - 9 * B 2 - 18 * B 1 - 6 * B 0 := by linarith [hid3]
    have hA : |9 * B 2| = 9 * |B 2| := by rw [abs_mul, abs_of_nonneg (by norm_num)]
    have hB' : |18 * B 1| = 18 * |B 1| := by rw [abs_mul, abs_of_nonneg (by norm_num)]
    have hC : |6 * B 0| = 6 * |B 0| := by rw [abs_mul, abs_of_nonneg (by norm_num)]
    calc |B 3| = |Gv 3 - 9 * B 2 - 18 * B 1 - 6 * B 0| := by rw [h3]
      _ ≤ |Gv 3| + 9 * |B 2| + 18 * |B 1| + 6 * |B 0| := by
          refine le_trans (Work.Elliptic.abs_four_le _ _ _ _) ?_
          rw [hA, hB', hC]
      _ ≤ Λ + 9 * (31 * Λ) + 18 * (4 * Λ) + 6 * Λ := by
          refine add_le_add (add_le_add (add_le_add (hGk 3 hJ3) ?_) ?_) ?_
          · linarith [b2 (by omega)]
          · linarith [b1 (by omega)]
          · linarith [b0]
      _ = 358 * Λ := by ring
  have b4 (hJ4 : 4 ≤ J) : |B 4| ≤ 5509 * Λ := by
    have h4 : B 4 = Gv 4 - 12 * B 3 - 36 * B 2 - 24 * B 1 := by linarith [hid4]
    have hA : |12 * B 3| = 12 * |B 3| := by rw [abs_mul, abs_of_nonneg (by norm_num)]
    have hB' : |36 * B 2| = 36 * |B 2| := by rw [abs_mul, abs_of_nonneg (by norm_num)]
    have hC : |24 * B 1| = 24 * |B 1| := by rw [abs_mul, abs_of_nonneg (by norm_num)]
    calc |B 4| = |Gv 4 - 12 * B 3 - 36 * B 2 - 24 * B 1| := by rw [h4]
      _ ≤ |Gv 4| + 12 * |B 3| + 36 * |B 2| + 24 * |B 1| := by
          refine le_trans (Work.Elliptic.abs_four_le _ _ _ _) ?_
          rw [hA, hB', hC]
      _ ≤ Λ + 12 * (358 * Λ) + 36 * (31 * Λ) + 24 * (4 * Λ) := by
          refine add_le_add (add_le_add (add_le_add (hGk 4 hJ4) ?_) ?_) ?_
          · linarith [b3 (by omega)]
          · linarith [b2 (by omega)]
          · linarith [b1 (by omega)]
      _ = 5509 * Λ := by ring
  intro j hj
  rcases j with _ | _ | _ | _ | _ | j
  · show |B 0| ≤ 6000 * Λ
    exact le_trans b0 (by nlinarith [hΛ])
  · show |B 1| ≤ 6000 * Λ
    exact le_trans (b1 hj) (by nlinarith [hΛ])
  · show |B 2| ≤ 6000 * Λ
    exact le_trans (b2 hj) (by nlinarith [hΛ])
  · show |B 3| ≤ 6000 * Λ
    exact le_trans (b3 hj) (by nlinarith [hΛ])
  · show |B 4| ≤ 6000 * Λ
    exact le_trans (b4 hj) (by nlinarith [hΛ])
  · omega

/-! ## Smoothness of `divZ2 f` on the open quadrant -/

/-- `divZ2 f = f/z²` is `C^∞` (genuine smooth order) on the open quadrant, for `SmoothQuad f`. -/
theorem contDiffOn_divZ2_Qd {f : ℝ → ℝ → ℝ} (hsm : Work.FTS.LocData.SmoothQuad f) :
    ContDiffOn ℝ Work.Stability.smoothOrder (Function.uncurry (Work.Elliptic.divZ2 f)) Qd := by
  have hf : ContDiffOn ℝ Work.Stability.smoothOrder (Function.uncurry f)
      (Set.Ioi (-1) ×ˢ Set.Ioo 0 (π / 2)) := hsm
  have hsub : Qd ⊆ Set.Ioi (-1) ×ˢ Set.Ioo 0 (π / 2) := fun p hp =>
    ⟨Set.mem_Ioi.mpr (by linarith [Set.mem_Ioi.mp hp.1]), hp.2⟩
  have hden : ContDiffOn ℝ Work.Stability.smoothOrder
      (fun p : ℝ × ℝ => p.1 ^ 2) Qd := contDiffOn_fst.pow 2
  have hdiv := (hf.mono hsub).div hden (fun p hp => pow_ne_zero 2 (ne_of_gt hp.1))
  refine hdiv.congr fun p hp => ?_
  rfl

/-- The `z`-slices of `divZ2 f` are `C^∞` (genuine smooth order) at every `z > 0`, for
`SmoothQuad f` and `θ ∈ (0,π/2)`. -/
theorem contDiffOn_divZ2_zslice_sm {f : ℝ → ℝ → ℝ} (hsm : Work.FTS.LocData.SmoothQuad f)
    {θ : ℝ} (hθ : θ ∈ Set.Ioo 0 (π / 2)) :
    ContDiffOn ℝ Work.Stability.smoothOrder (fun z' => Work.Elliptic.divZ2 f z' θ)
      (Set.Ioi 0) :=
  Work.FTS.LocData.contDiffOn_slice_z (contDiffOn_divZ2_Qd hsm) hθ

/-- The `z`-slices of `divZ2 f` are `C^∞` (genuine smooth order) at every `z > 0`. -/
theorem contDiffAt_divZ2_zslice_sm {f : ℝ → ℝ → ℝ} (hsm : Work.FTS.LocData.SmoothQuad f)
    {θ : ℝ} (hθ : θ ∈ Set.Ioo 0 (π / 2)) :
    ∀ z : ℝ, 0 < z →
      ContDiffAt ℝ Work.Stability.smoothOrder (fun z' => Work.Elliptic.divZ2 f z' θ) z :=
  fun z hz => (contDiffOn_divZ2_zslice_sm hsm hθ).contDiffAt
    (isOpen_Ioi.mem_nhds hz)

/-- The `z`-slices of the `D_θ`-iterates of `divZ2 f` are `C^∞` (genuine smooth order) on
`(0,∞)`, for `SmoothQuad f` and `θ ∈ (0,π/2)`. -/
theorem contDiffOn_DthIter_divZ2_zslice_sm {f : ℝ → ℝ → ℝ}
    (hsm : Work.FTS.LocData.SmoothQuad f) (i : ℕ) {θ : ℝ} (hθ : θ ∈ Set.Ioo 0 (π / 2)) :
    ContDiffOn ℝ Work.Stability.smoothOrder
      (fun z' => DthIter i (Work.Elliptic.divZ2 f) z' θ) (Set.Ioi 0) :=
  Work.FTS.LocData.contDiffOn_slice_z
    (Work.FTS.LocData.contDiffOn_DthIter isOpen_Qd (contDiffOn_divZ2_Qd hsm) i) hθ

/-- The `z`-slices of the `D_θ`-iterates of `divZ2 f` are `C^∞` at every `z > 0`. -/
theorem contDiffAt_DthIter_divZ2_zslice_sm {f : ℝ → ℝ → ℝ}
    (hsm : Work.FTS.LocData.SmoothQuad f) (i : ℕ) {θ : ℝ} (hθ : θ ∈ Set.Ioo 0 (π / 2)) :
    ∀ z : ℝ, 0 < z → ContDiffAt ℝ Work.Stability.smoothOrder
      (fun z' => DthIter i (Work.Elliptic.divZ2 f) z' θ) z :=
  fun z hz => (contDiffOn_DthIter_divZ2_zslice_sm hsm i hθ).contDiffAt
    (isOpen_Ioi.mem_nhds hz)

/-! ## The Leibniz expansions of `∂_z^m f` through `f = z²·divZ2 f` -/

/-- `∂_z^m f = z² ∂_z^m κ + 2m z ∂_z^{m-1} κ + m(m-1) ∂_z^{m-2} κ` with
`κ = divZ2 f`, for `SmoothQuad f`, `z > 0` and `θ ∈ (0,π/2)`.  (The `SmoothNbhd`-version is
`Work.Elliptic.pzIter_divZ2_expansion_aux`.) -/
theorem pzIter_divZ2_expansion_aux_sm {f : ℝ → ℝ → ℝ} (hsm : Work.FTS.LocData.SmoothQuad f)
    {m : ℕ} (hm : m ≤ 4) {z θ : ℝ} (hz : 0 < z) (hθ : θ ∈ Set.Ioo 0 (π / 2)) :
    pzIter m f z θ = z ^ 2 * pzIter m (Work.Elliptic.divZ2 f) z θ
      + (2 * (m : ℝ)) * z * pzIter (m - 1) (Work.Elliptic.divZ2 f) z θ
      + ((m : ℝ) * ((m : ℝ) - 1)) * pzIter (m - 2) (Work.Elliptic.divZ2 f) z θ := by
  have hκ : ContDiffAt ℝ Work.Stability.smoothOrder
      (fun z' => Work.Elliptic.divZ2 f z' θ) z :=
    contDiffAt_divZ2_zslice_sm hsm hθ z hz
  have hcongr : pzIter m f z θ
      = pzIter m (fun z θ => z ^ 2 * Work.Elliptic.divZ2 f z θ) z θ := by
    refine Work.Elliptic.pzIter_congr_nhds m ?_
    filter_upwards [IsOpen.mem_nhds isOpen_Ioi hz] with z' hz'
    exact Work.Elliptic.divZ2_eq_mul (ne_of_gt hz')
  rw [hcongr, pzIter_sq_mul_sm m hm hκ]

/-- `∂_z^l D_θ^i f = z² ∂_z^l κ + 2l z ∂_z^{l-1}κ + l(l-1) ∂_z^{l-2}κ` with
`κ = D_θ^i (divZ2 f)`, for `SmoothQuad f`, `z > 0`, `θ ∈ (0,π/2)` and `l ≤ 4`.  (The
`SmoothNbhd`-version is `Work.Elliptic.expand_aux`.) -/
theorem expand_aux_sm {f : ℝ → ℝ → ℝ} (hsm : Work.FTS.LocData.SmoothQuad f) (i l : ℕ)
    (hl : l ≤ 4) {z : ℝ} (hz : 0 < z) {θ : ℝ} (hθ : θ ∈ Set.Ioo 0 (π / 2)) :
    pzIter l (DthIter i f) z θ
      = z ^ 2 * pzIter l (DthIter i (Work.Elliptic.divZ2 f)) z θ
        + (2 * (l : ℝ)) * z * pzIter (l - 1) (DthIter i (Work.Elliptic.divZ2 f)) z θ
        + ((l : ℝ) * ((l : ℝ) - 1))
            * pzIter (l - 2) (DthIter i (Work.Elliptic.divZ2 f)) z θ := by
  have hκ : ContDiffAt ℝ Work.Stability.smoothOrder
      (fun z' => DthIter i (Work.Elliptic.divZ2 f) z' θ) z :=
    contDiffAt_DthIter_divZ2_zslice_sm hsm i hθ z hz
  have hmemIoi : Set.Ioi (0 : ℝ) ∈ 𝓝 z :=
    isOpen_Ioi.mem_nhds (by simp only [Set.mem_Ioi]; exact hz)
  have hev : ∀ᶠ z' in 𝓝 z, ∀ θ' : ℝ,
      DthIter i f z' θ' = z' ^ 2 * DthIter i (Work.Elliptic.divZ2 f) z' θ' := by
    filter_upwards [hmemIoi] with z' hz' θ'
    exact Work.Elliptic.DthIter_divZ2_eq i (ne_of_gt hz')
  rw [Work.Elliptic.pzIter_congr_of_eventually (u := DthIter i f)
    (v := fun z θ => z ^ 2 * DthIter i (Work.Elliptic.divZ2 f) z θ) (z := z) (θ := θ) l hev]
  exact pzIter_sq_mul_sm l hl hκ

end Work.FTS.H2.Q
