/-
Copyright: work module for the Elgindi finite-time singularity project.

# The `σ`-gain of the angular commutator, in the interior class

For a datum `G` which is `C^∞` on the open quadrant `Q0 = (0,∞) × (0,π/2)`
(`Work.FTS.EllipticEst.SmoothOpen`) and a fixed number `j` of radial derivatives, the
`D_θ`-commutator estimate of Elgindi's Proposition `SpecialTransport` reads

  `sin(2θ)·|D_z^j D_θ^r(∂_θ G)| ≤ C · Σ_{1 ≤ m ≤ r+1} |D_z^j D_θ^m G|`   (`r ≤ 4`),

i.e. the operator `sin(2θ)∂_θ` applied to `∂_θ G` costs exactly one extra angular slot.  This
is the `SmoothOpen` (interior) analogue of the two `σ`-bound lemmas already in the tree,
`Work.FTS.H2.sigma_z_bound` (`SmoothNbhd`, analytic on a neighbourhood of the closed
quadrant) and `Work.FTS.H2.STQ.sigma_z_bound_Q` (`SmoothQuad`, `i ≤ 3`); the present file
covers `r ≤ 4` in the class in which the elliptic estimates of the chapter are actually
stated.

## The mechanism

Write `D_θ = sin(2θ)·∂_θ`.  Since `D_θ^{i+1}G = D_θ^i(D_θG)` and `D_θG = sin(2·)·∂_θG`, the
iterated Leibniz rule for `D_θ^i` applied to the product `sin(2·)·∂_θG` gives

  `D_θ^{i+1}G = Σ_{a ≤ i} C(i,a)·D_θ^a(sin 2·)·D_θ^{i-a}(∂_θG)`,

and splitting off `a = 0` yields

  `sin(2θ)·D_θ^i(∂_θG) = D_θ^{i+1}G − Σ_{r<i} C(i,r+1)·L^{r+1}(sin 2·)·D_θ^{i-1-r}(∂_θG)`,

where `L u = sin(2θ)u'` and `LopIter r (sin 2·)` is exactly `D_θ^r(sin 2·)`
(`Work.FTS.TransportS.DthIter_Sfun_eq_LopIter`).  Every iterate of `L` applied to `sin(2·)`
is again divisible by `sin(2·)` (`Work.FTS.EllipticEst.Lop_iter_sin_bound`; the explicit
constants `Asin r` are in `Work.FTS.H2.STFacts`), so an induction on `i ≤ 4` multiplying by
`Σ_{1 ≤ m ≤ i+1}|D_z^jD_θ^m G|` closes.

All declarations here are complete (no placeholder) and rest on
`[propext, Classical.choice, Quot.sound]`.
-/
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Tactic.IntervalCases
import Submission.Work.Spaces.Defs
import Submission.Work.FTS.EllipticEst.OpenQDefs
import Submission.Work.FTS.H2.STFacts
import Submission.Work.FTS.TransportS.flat_mixed_le
import Submission.Work.FTS.NonlinRows.mixed_succ_expansion_open

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.NonlinRows

open scoped Real Topology
open MeasureTheory Set Filter

set_option autoImplicit false
set_option maxHeartbeats 2000000

/-! ## The constant of the `σ`-gain -/

/-- The constant `C_r` of the estimate `sin(2θ)·|D_z^jD_θ^r(∂_θG)| ≤ C_r·Σ_{1≤m≤r+1}|…|`:

`C_0 = 1` (the case `r = 0` is the exact identity `sin(2θ)·∂_θG = D_θG`), and for `1 ≤ r ≤ 4`
the recursion `C_r = 1 + Σ_{a<r} C(r,a+1)·A_{a+1}·C_{r-a-1}`, with `A_k = Asin k` the
constants of `|D_θ^k(sin 2·)| ≤ A_k·sin(2θ)`.  The values are
`C_1 = 3`, `C_2 = 17`, `C_3 = 187`, `C_4 = 2865`. -/
def B4 : ℕ → ℝ
  | 0 => 1
  | 1 => 3
  | 2 => 17
  | 3 => 187
  | _ => 2865

theorem B4_pos (n : ℕ) : 0 < B4 n := by
  rcases n with _ | _ | _ | _ | _ <;> norm_num [B4]

theorem B4_nonneg (n : ℕ) : 0 ≤ B4 n := (B4_pos n).le

/-- The recursion satisfied by the constants: for `1 ≤ n ≤ 4`,
`C_n = 1 + Σ_{a<n} C(n,a+1)·A_{a+1}·C_{n-a-1}`. -/
theorem B4_rec (n : ℕ) (hn : n ≤ 4) (hn1 : 1 ≤ n) :
    B4 n = 1 + ∑ r ∈ Finset.range n,
      ((n.choose (r + 1) : ℝ) * Work.FTS.H2.Asin (r + 1) * B4 (n - (r + 1))) := by
  interval_cases n <;>
    simp [B4, Work.FTS.H2.Asin, Finset.sum_range_succ] <;> norm_num [Nat.choose]

/-- The triangle inequality `|x - y| ≤ |x| + |y|`, in the form used below. -/
theorem abs_sub_le_abs_add_loc (x y : ℝ) : |x - y| ≤ |x| + |y| :=
  abs_le.mpr ⟨by linarith [neg_abs_le x, le_abs_self y],
    by linarith [le_abs_self x, neg_abs_le y]⟩

/-- `D_θ^r(sin 2·) = L^r(sin 2·)` is `O(sin 2θ)`, with the explicit constant `Asin r`. -/
theorem abs_LopIter_sin_le (r : ℕ) (hr : r ≤ 4) (θ : ℝ) (hθ : θ ∈ Set.Ioo 0 (Real.pi / 2)) :
    |Work.FTS.EllipticEst.LopIter r (fun t : ℝ => Real.sin (2 * t)) θ|
      ≤ Work.FTS.H2.Asin r * Real.sin (2 * θ) := by
  rw [← Work.FTS.TransportS.DthIter_Sfun_eq_LopIter r 0 θ]
  exact Work.FTS.H2.abs_DthIter_Sfun_le r hr 0 ⟨hθ.1.le, hθ.2.le⟩

/-! ## The commutator expansion

The pointwise input of the induction below — the expansion of `D_z^jD_θ^{i+1}G` in terms of
`∂_θG`, for `G` of class `SmoothOpen` — is proved in the sibling module
`Submission.Work.FTS.NonlinRows.mixed_succ_expansion_open` (namespace `Work.FTS.NonlinRows`)
as `mixed_succ_expansion_open`:

  `D_z^jD_θ^{i+1}G = sin(2θ)·D_z^jD_θ^i(∂_θG)
      + Σ_{r<i} C(i,r+1)·L^{r+1}(sin 2·)(θ)·D_z^jD_θ^{i-1-r}(∂_θG)`. -/

/-! ## The `σ`-gain, by induction on the number of angular slots -/

/-- **The `σ`-gain of the angular commutator, `r ≤ 4`.**  For `G` smooth on the open quadrant
and `1 ≤ r ≤ 4`,

  `sin(2θ)·|D_z^jD_θ^r(∂_θG)| ≤ C_r·Σ_{1 ≤ m ≤ r+1}|D_z^jD_θ^m G|`

with the explicit constants `C_r = B4 r`. -/
theorem sigma_bound_open (g : ℝ → ℝ → ℝ) (hg : Work.FTS.EllipticEst.SmoothOpen g)
    (n : ℕ) (hn : n ≤ 4) (j : ℕ) (z θ : ℝ) (hz : 0 < z)
    (hθ : θ ∈ Set.Ioo 0 (Real.pi / 2)) :
    Real.sin (2 * θ) * |Work.Spaces.mixed j n (Work.Spaces.pth g) z θ|
      ≤ B4 n * ∑ m ∈ Finset.Icc 1 (n + 1), |Work.Spaces.mixed j m g z θ| := by
  have hmain : ∀ n, n ≤ 4 → ∀ j z θ, 0 < z → θ ∈ Set.Ioo 0 (Real.pi / 2) →
      Real.sin (2 * θ) * |Work.Spaces.mixed j n (Work.Spaces.pth g) z θ|
        ≤ B4 n * ∑ m ∈ Finset.Icc 1 (n + 1), |Work.Spaces.mixed j m g z θ| := by
    intro n
    refine Nat.strong_induction_on n ?_
    intro n ih hn j z θ hz hθ
    have hS : 0 ≤ Real.sin (2 * θ) := Work.FTS.TransportS.sin_two_nonneg_of_Ioo hθ
    rcases Nat.eq_zero_or_pos n with h0 | hpos
    · -- `n = 0`: the exact identity `sin(2θ)·∂_θG = D_θG`
      subst h0
      have h1 : Real.sin (2 * θ) * |Work.Spaces.mixed j 0 (Work.Spaces.pth g) z θ|
          = |Work.Spaces.mixed j 1 g z θ| := by
        have h2 : Real.sin (2 * θ) * Work.Spaces.mixed j 0 (Work.Spaces.pth g) z θ
            = Work.Spaces.mixed j 1 g z θ := Work.FTS.H2.sin_mul_dzIter_pth g j z θ
        calc Real.sin (2 * θ) * |Work.Spaces.mixed j 0 (Work.Spaces.pth g) z θ|
            = |Real.sin (2 * θ) * Work.Spaces.mixed j 0 (Work.Spaces.pth g) z θ| := by
              rw [abs_mul, abs_of_nonneg hS]
          _ = |Work.Spaces.mixed j 1 g z θ| := by rw [h2]
      rw [h1]
      have hT1 : (∑ m ∈ Finset.Icc 1 ((0 : ℕ) + 1), |Work.Spaces.mixed j m g z θ|)
          = |Work.Spaces.mixed j 1 g z θ| := by
        rw [show Finset.Icc 1 ((0 : ℕ) + 1) = {1} from rfl, Finset.sum_singleton]
      rw [hT1]
      simp [B4]
    · -- `1 ≤ n ≤ 4`: solve for the leading slot with the expansion and bound the remainder
      set T : ℝ := ∑ m ∈ Finset.Icc 1 (n + 1), |Work.Spaces.mixed j m g z θ| with hT
      have hTnn : 0 ≤ T := Finset.sum_nonneg fun m _ => abs_nonneg _
      have hexp := mixed_succ_expansion_open g hg n j hz hθ
      have hrearr : Real.sin (2 * θ) * Work.Spaces.mixed j n (Work.Spaces.pth g) z θ
          = Work.Spaces.mixed j (n + 1) g z θ
            - ∑ r ∈ Finset.range n,
                (((n.choose (r + 1) : ℝ)
                    * Work.FTS.EllipticEst.LopIter (r + 1) (fun t : ℝ => Real.sin (2 * t)) θ)
                  * Work.Spaces.mixed j (n - (r + 1)) (Work.Spaces.pth g) z θ) := by
        rw [hexp]; ring
      have hstep1 : Real.sin (2 * θ) * |Work.Spaces.mixed j n (Work.Spaces.pth g) z θ|
          ≤ |Work.Spaces.mixed j (n + 1) g z θ|
            + |∑ r ∈ Finset.range n,
                (((n.choose (r + 1) : ℝ)
                    * Work.FTS.EllipticEst.LopIter (r + 1) (fun t : ℝ => Real.sin (2 * t)) θ)
                  * Work.Spaces.mixed j (n - (r + 1)) (Work.Spaces.pth g) z θ)| := by
        have habs : Real.sin (2 * θ) * |Work.Spaces.mixed j n (Work.Spaces.pth g) z θ|
            = |Real.sin (2 * θ) * Work.Spaces.mixed j n (Work.Spaces.pth g) z θ| := by
          rw [abs_mul, abs_of_nonneg hS]
        rw [habs, hrearr]
        exact abs_sub_le_abs_add_loc _ _
      refine le_trans hstep1 ?_
      have hterm : ∀ r ∈ Finset.range n,
          |(((n.choose (r + 1) : ℝ)
              * Work.FTS.EllipticEst.LopIter (r + 1) (fun t : ℝ => Real.sin (2 * t)) θ)
            * Work.Spaces.mixed j (n - (r + 1)) (Work.Spaces.pth g) z θ)|
            ≤ ((n.choose (r + 1) : ℝ) * Work.FTS.H2.Asin (r + 1) * B4 (n - (r + 1))) * T := by
        intro r hr
        simp only [Finset.mem_range] at hr
        have hrle : r + 1 ≤ 4 := by omega
        have hlt : n - (r + 1) < n := by omega
        have hAs := abs_LopIter_sin_le (r + 1) hrle θ hθ
        have hCnn : (0 : ℝ) ≤ (n.choose (r + 1) : ℝ) := Nat.cast_nonneg _
        have hIHr := ih (n - (r + 1)) hlt (by omega) j z θ hz hθ
        have hsub : Finset.Icc 1 (n - (r + 1) + 1) ⊆ Finset.Icc 1 (n + 1) := by
          intro m hm
          simp only [Finset.mem_Icc] at hm ⊢
          omega
        have hTle : (∑ m ∈ Finset.Icc 1 (n - (r + 1) + 1),
              |Work.Spaces.mixed j m g z θ|) ≤ T := by
          rw [hT]
          exact Finset.sum_le_sum_of_subset_of_nonneg
            (f := fun m => |Work.Spaces.mixed j m g z θ|) hsub (fun m _ _ => abs_nonneg _)
        rw [abs_mul, abs_mul, abs_of_nonneg hCnn]
        calc (n.choose (r + 1) : ℝ)
              * |Work.FTS.EllipticEst.LopIter (r + 1) (fun t : ℝ => Real.sin (2 * t)) θ|
              * |Work.Spaces.mixed j (n - (r + 1)) (Work.Spaces.pth g) z θ|
            ≤ (n.choose (r + 1) : ℝ) * (Work.FTS.H2.Asin (r + 1) * Real.sin (2 * θ))
              * |Work.Spaces.mixed j (n - (r + 1)) (Work.Spaces.pth g) z θ| := by
              refine mul_le_mul_of_nonneg_right ?_ (abs_nonneg _)
              exact mul_le_mul_of_nonneg_left hAs hCnn
          _ = ((n.choose (r + 1) : ℝ) * Work.FTS.H2.Asin (r + 1))
              * (Real.sin (2 * θ)
                * |Work.Spaces.mixed j (n - (r + 1)) (Work.Spaces.pth g) z θ|) := by
              ring
          _ ≤ ((n.choose (r + 1) : ℝ) * Work.FTS.H2.Asin (r + 1))
              * (B4 (n - (r + 1)) * T) :=
              mul_le_mul_of_nonneg_left
                (le_trans hIHr (mul_le_mul_of_nonneg_left hTle (B4_nonneg _)))
                (mul_nonneg (Nat.cast_nonneg _) (Work.FTS.H2.Asin_pos _).le)
          _ = ((n.choose (r + 1) : ℝ) * Work.FTS.H2.Asin (r + 1) * B4 (n - (r + 1))) * T := by
              ring
      have hsumabs : |∑ r ∈ Finset.range n,
            (((n.choose (r + 1) : ℝ)
                * Work.FTS.EllipticEst.LopIter (r + 1) (fun t : ℝ => Real.sin (2 * t)) θ)
              * Work.Spaces.mixed j (n - (r + 1)) (Work.Spaces.pth g) z θ)|
          ≤ ∑ r ∈ Finset.range n,
              ((n.choose (r + 1) : ℝ) * Work.FTS.H2.Asin (r + 1) * B4 (n - (r + 1))) * T :=
        le_trans (Finset.abs_sum_le_sum_abs _ _) (Finset.sum_le_sum hterm)
      have hw1 : |Work.Spaces.mixed j (n + 1) g z θ| ≤ T := by
        have hm : n + 1 ∈ Finset.Icc 1 (n + 1) := by simp
        rw [hT]
        exact Finset.single_le_sum (f := fun m => |Work.Spaces.mixed j m g z θ|)
          (fun m _ => abs_nonneg _) hm
      have hfin : T + ∑ r ∈ Finset.range n,
            ((n.choose (r + 1) : ℝ) * Work.FTS.H2.Asin (r + 1) * B4 (n - (r + 1))) * T
          = B4 n * T := by
        rw [B4_rec n hn hpos, add_mul, one_mul, Finset.sum_mul]
      calc |Work.Spaces.mixed j (n + 1) g z θ|
            + |∑ r ∈ Finset.range n,
                (((n.choose (r + 1) : ℝ)
                    * Work.FTS.EllipticEst.LopIter (r + 1) (fun t : ℝ => Real.sin (2 * t)) θ)
                  * Work.Spaces.mixed j (n - (r + 1)) (Work.Spaces.pth g) z θ)|
          ≤ T + ∑ r ∈ Finset.range n,
              ((n.choose (r + 1) : ℝ) * Work.FTS.H2.Asin (r + 1) * B4 (n - (r + 1))) * T :=
            add_le_add hw1 hsumabs
        _ = B4 n * T := hfin
  exact hmain n hn j z θ hz hθ

/-! ## The target -/

theorem sin_mul_mixed_pth_le (r : ℕ) (hr : r ≤ 4) :
    ∃ C : ℝ, 0 < C ∧ ∀ (G : ℝ → ℝ → ℝ), Work.FTS.EllipticEst.SmoothOpen G →
      ∀ (c : ℕ) (z : ℝ) (θ : ℝ), 0 < z → θ ∈ Set.Ioo 0 (Real.pi / 2) →
      |Real.sin (2 * θ) * Work.Spaces.mixed c r (Work.Spaces.pth G) z θ|
        ≤ C * ∑ m ∈ Finset.Icc 1 (r + 1), |Work.Spaces.mixed c m G z θ| := by
  refine ⟨B4 r, B4_pos r, ?_⟩
  intro G hG c z θ hz hθ
  have hS : 0 ≤ Real.sin (2 * θ) := Work.FTS.TransportS.sin_two_nonneg_of_Ioo hθ
  have h := sigma_bound_open G hG r hr c z θ hz hθ
  have habs : |Real.sin (2 * θ) * Work.Spaces.mixed c r (Work.Spaces.pth G) z θ|
      = Real.sin (2 * θ) * |Work.Spaces.mixed c r (Work.Spaces.pth G) z θ| := by
    rw [abs_mul, abs_of_nonneg hS]
  rw [habs]
  exact h

end Work.FTS.NonlinRows
