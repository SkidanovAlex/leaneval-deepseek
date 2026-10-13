import Mathlib.Analysis.Calculus.IteratedDeriv.Defs
import Mathlib.Analysis.Calculus.SmoothSeries
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Mathlib.Order.CompletePartialOrder
import Mathlib.Topology.Algebra.Module.ModuleTopology

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.PhiStar.FlatWAux.Fam2Diff

open Set Filter

/-- **Termwise differentiation of a series in one variable.**  Let `c : ℕ → ℝ` and let
`q : ℕ → ℝ → ℝ` be a family of functions which are `C^k` on the open interval `(a,b)`, whose
`r`-th iterated derivatives are bounded on `(a,b)` by `B m` for every `0 ≤ r ≤ k`, with
`∑ m, |c m| * B m` summable.  Then `y ↦ ∑' m, c m * q m y` is `C^k` on `(a,b)` and each of its
iterated derivatives is the sum of the termwise iterated derivatives.

The proof is the one-dimensional Weierstrass `M`-test applied to every derivative order at once:
all the bounds are uniform on the whole interval, hence in particular on compacta, so the series
of `r`-th derivatives converges (locally uniformly) with summable majorant `m ↦ |c m| * B m`, and
`contDiffOn_of_continuousOn_differentiableOn_deriv` assembles the conclusion from the continuity
and the differentiability of the `r`-th derivative series. -/
theorem TsumContDiff {k : ℕ} {c : ℕ → ℝ} {q : ℕ → ℝ → ℝ} {B : ℕ → ℝ} {a b : ℝ} (hab : a < b)
    (hB : ∀ m : ℕ, 0 ≤ B m) (hcB : Summable fun m : ℕ => |c m| * B m)
    (hq : ∀ m : ℕ, ContDiffOn ℝ k (q m) (Set.Ioo a b))
    (hqb : ∀ (m r : ℕ), r ≤ k → ∀ y : ℝ, y ∈ Set.Ioo a b →
      |iteratedDeriv r (q m) y| ≤ B m) :
    ContDiffOn ℝ k (fun y : ℝ => ∑' m : ℕ, c m * q m y) (Set.Ioo a b) ∧
      (∀ r : ℕ, r ≤ k → ∀ y : ℝ, y ∈ Set.Ioo a b →
        iteratedDeriv r (fun y : ℝ => ∑' m : ℕ, c m * q m y) y
          = ∑' m : ℕ, c m * iteratedDeriv r (q m) y) := by
  classical
  have hs : IsOpen (Set.Ioo a b) := isOpen_Ioo
  have hud : UniqueDiffOn ℝ (Set.Ioo a b) := isOpen_Ioo.uniqueDiffOn
  -- a point of the interval
  obtain ⟨y₀, hy₀⟩ : ∃ y : ℝ, y ∈ Set.Ioo a b :=
    ⟨(a + b) / 2, ⟨by linarith, by linarith⟩⟩
  -- (A) the majorant bound for every summand
  have hbound : ∀ (m r : ℕ), r ≤ k → ∀ y : ℝ, y ∈ Set.Ioo a b →
      ‖c m * iteratedDeriv r (q m) y‖ ≤ |c m| * B m := by
    intro m r hr y hy
    have hBm : 0 ≤ B m := hB m
    have hxa : |iteratedDeriv r (q m) y| ≤ |B m| := by
      rw [abs_of_nonneg hBm]; exact hqb m r hr y hy
    calc ‖c m * iteratedDeriv r (q m) y‖ = |c m| * |iteratedDeriv r (q m) y| := by
          rw [Real.norm_eq_abs, abs_mul]
      _ ≤ |c m| * |B m| := mul_le_mul_of_nonneg_left hxa (abs_nonneg _)
      _ = |c m| * B m := by rw [abs_of_nonneg hBm]
  -- (B) pointwise summability of every derivative series
  have hsumm : ∀ (r : ℕ), r ≤ k → ∀ y : ℝ, y ∈ Set.Ioo a b →
      Summable (fun m : ℕ => c m * iteratedDeriv r (q m) y) := by
    intro r hr y hy
    exact Summable.of_norm_bounded hcB (fun m => hbound m r hr y hy)
  -- (C) one summand is differentiable, with derivative the next summand
  have hterm : ∀ (r : ℕ), r + 1 ≤ k → ∀ (m : ℕ) (y : ℝ), y ∈ Set.Ioo a b →
      HasDerivAt (fun z => c m * iteratedDeriv r (q m) z)
        (c m * iteratedDeriv (r + 1) (q m) y) y := by
    intro r hr m y hy
    have hcr : ContDiffOn ℝ (r + 1) (q m) (Set.Ioo a b) :=
      (hq m).of_le (by exact_mod_cast (show r + 1 ≤ k by omega))
    have hnat := (contDiffOn_nat_iff_continuousOn_differentiableOn_deriv
        (𝕜 := ℝ) (n := r + 1) (f := q m) hud).mp hcr
    have hdOn : DifferentiableOn ℝ (iteratedDeriv r (q m)) (Set.Ioo a b) :=
      (hnat.2 r (by omega)).congr
        (fun z hz => (iteratedDerivWithin_of_isOpen (n := r) isOpen_Ioo hz).symm)
    have hd : DifferentiableAt ℝ (iteratedDeriv r (q m)) y :=
      hdOn.differentiableAt (hs.mem_nhds hy)
    have h1 : HasDerivAt (iteratedDeriv r (q m)) (iteratedDeriv (r + 1) (q m) y) y := by
      simpa only [iteratedDeriv_succ] using hd.hasDerivAt
    exact h1.const_mul (c m)
  -- (D) the derivative series is the derivative of the series
  have hser : ∀ (r : ℕ), r + 1 ≤ k → ∀ y : ℝ, y ∈ Set.Ioo a b →
      HasDerivAt (fun z => ∑' m : ℕ, c m * iteratedDeriv r (q m) z)
        (∑' m : ℕ, c m * iteratedDeriv (r + 1) (q m) y) y := by
    intro r hr y hy
    exact hasDerivAt_tsum_of_isPreconnected (u := fun m : ℕ => |c m| * B m)
      (g := fun m z => c m * iteratedDeriv r (q m) z)
      (g' := fun m z => c m * iteratedDeriv (r + 1) (q m) z)
      hcB isOpen_Ioo isPreconnected_Ioo (fun m z hz => hterm r hr m z hz)
      (fun m z hz => hbound m (r + 1) hr z hz) hy₀ (hsumm r (by omega) y₀ hy₀) hy
  -- (E) continuity of each derivative series
  have hcont : ∀ (r : ℕ), r ≤ k → ContinuousOn
      (fun z => ∑' m : ℕ, c m * iteratedDeriv r (q m) z) (Set.Ioo a b) := by
    intro r hr
    refine continuousOn_tsum (f := fun m z => c m * iteratedDeriv r (q m) z)
      (s := Set.Ioo a b) (u := fun m : ℕ => |c m| * B m) (fun m => ?_) hcB
      (fun m z hz => hbound m r hr z hz)
    have hcr : ContDiffOn ℝ r (q m) (Set.Ioo a b) := (hq m).of_le (by exact_mod_cast hr)
    have hc : ContinuousOn (iteratedDerivWithin r (q m) (Set.Ioo a b)) (Set.Ioo a b) :=
      ((contDiffOn_nat_iff_continuousOn_differentiableOn_deriv
        (𝕜 := ℝ) (n := r) (f := q m) hud).mp hcr).1 r le_rfl
    exact (hc.congr
      (fun z hz => (iteratedDerivWithin_of_isOpen (n := r) isOpen_Ioo hz).symm)).const_mul (c m)
  -- (F) the iterated derivatives of the series
  have hEq : ∀ (r : ℕ), r ≤ k → ∀ y : ℝ, y ∈ Set.Ioo a b →
      iteratedDeriv r (fun y : ℝ => ∑' m : ℕ, c m * q m y) y
        = ∑' m : ℕ, c m * iteratedDeriv r (q m) y := by
    intro r
    induction r with
    | zero =>
      intro _ y _
      simp
    | succ r ih =>
      intro hr y hy
      have hrk : r ≤ k := by omega
      have hev : ∀ᶠ z in nhds y,
          iteratedDeriv r (fun w : ℝ => ∑' m : ℕ, c m * q m w) z
            = ∑' m : ℕ, c m * iteratedDeriv r (q m) z := by
        filter_upwards [hs.mem_nhds hy] with z hz
        exact ih hrk z hz
      calc iteratedDeriv (r + 1) (fun y : ℝ => ∑' m : ℕ, c m * q m y) y
          = deriv (fun z => iteratedDeriv r (fun y : ℝ => ∑' m : ℕ, c m * q m y) z) y := by
            rw [iteratedDeriv_succ]
        _ = deriv (fun z => ∑' m : ℕ, c m * iteratedDeriv r (q m) z) y :=
              Filter.EventuallyEq.deriv_eq hev
        _ = ∑' m : ℕ, c m * iteratedDeriv (r + 1) (q m) y := (hser r hr y hy).deriv
  refine ⟨?_, fun r hr y hy => hEq r hr y hy⟩
  refine contDiffOn_of_continuousOn_differentiableOn_deriv
    (𝕜 := ℝ) (f := fun y : ℝ => ∑' m : ℕ, c m * q m y) (s := Set.Ioo a b) (n := (k : ℕ∞)) ?_ ?_
  · intro m hm
    have hmk : m ≤ k := by exact_mod_cast hm
    refine (hcont m hmk).congr ?_
    intro y hy
    have h1 : iteratedDerivWithin m (fun w : ℝ => ∑' n : ℕ, c n * q n w) (Set.Ioo a b) y
        = iteratedDeriv m (fun w : ℝ => ∑' n : ℕ, c n * q n w) y :=
      (iteratedDerivWithin_of_isOpen (n := m) isOpen_Ioo) hy
    exact h1.trans (hEq m hmk y hy)
  · intro m hm
    have hmk : m < k := by exact_mod_cast hm
    have hd : DifferentiableOn ℝ
        (fun z => ∑' n : ℕ, c n * iteratedDeriv m (q n) z) (Set.Ioo a b) :=
      fun y hy => (hser m (by omega) y hy).differentiableAt.differentiableWithinAt
    refine hd.congr ?_
    intro y hy
    have h1 : iteratedDerivWithin m (fun w : ℝ => ∑' n : ℕ, c n * q n w) (Set.Ioo a b) y
        = iteratedDeriv m (fun w : ℝ => ∑' n : ℕ, c n * q n w) y :=
      (iteratedDerivWithin_of_isOpen (n := m) isOpen_Ioo) hy
    exact h1.trans (hEq m (le_of_lt hmk) y hy)

end Work.FTS.PhiStar.FlatWAux.Fam2Diff
