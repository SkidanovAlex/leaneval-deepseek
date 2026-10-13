/-
Copyright: work module for the Elgindi finite-time singularity project.

# The four `cosBar` identities

With `φ = u / cos θ` on `(0, π/2)`, the angular operator
`Lzero1 = -∂_θθ + ∂_θ(tan θ ·) - 6` and the derivatives of `u` are explicit linear
combinations of `φ` and its derivatives:

* `Lzero1 u = -cos θ · φ'' + 3 sin θ · φ' - 4 cos θ · φ`,
* `u''      =  sin θ · φ' - 5 cos θ · φ - Lzero1 u`,
* `u'''     =  sin θ · φ'' - 4 cos θ · φ' + 5 sin θ · φ - (Lzero1 u)'`,
* `u''''    =  sin θ · φ''' - 3 cos θ · φ'' + 9 sin θ · φ' + 5 cos θ · φ - (Lzero1 u)''`.

The proof: `u = cos θ · φ` in a neighbourhood of each point of `(0, π/2)`, so the iterated
derivatives of `u` are obtained from the Leibniz rule (`iteratedDeriv_mul`) applied to
`cos · φ`, and the identities reduce to elementary trigonometry.

`Work.FTS.EllipticEst.remov.cosBarIdents` is the statement requested by the elliptic-estimate
part of the development.
-/
import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.ArctanDeriv
import Mathlib.Order.CompletePartialOrder
import Submission.Work.FTS.EllipticEst.StraightDefs

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.EllipticEst.remov

set_option autoImplicit false

/-! ### Elementary facts about iterated derivatives -/

/-- A `C^n` function has a `C^{n-k}` `k`-th derivative. -/
lemma contDiffAt_iteratedDeriv {f : ℝ → ℝ} {x : ℝ} {n k : ℕ}
    (h : ContDiffAt ℝ (n : WithTop ℕ∞) f x) (hk : k ≤ n) :
    ContDiffAt ℝ ((n - k : ℕ) : WithTop ℕ∞) (iteratedDeriv k f) x := by
  induction k with
  | zero => simpa using h
  | succ k ih =>
      have hk' : k ≤ n := le_trans (Nat.le_succ k) hk
      have h1 : n - k - 1 + 1 = n - k := by omega
      have hle : ((n - k - 1 : ℕ) : WithTop ℕ∞) + 1 ≤ ((n - k : ℕ) : WithTop ℕ∞) := by
        rw [show ((n - k - 1 : ℕ) : WithTop ℕ∞) + 1 = (((n - k - 1) + 1 : ℕ) : WithTop ℕ∞) from by
          push_cast; ring, h1]
      have hstep : ContDiffAt ℝ ((n - k - 1 : ℕ) : WithTop ℕ∞) (deriv (iteratedDeriv k f)) x :=
        (ih hk').derivWithin (m := ((n - k - 1 : ℕ) : WithTop ℕ∞)) hle
      convert hstep using 2
      exact iteratedDeriv_succ

/-- The second `iteratedDeriv` is the second `deriv`. -/
lemma itd_two (f : ℝ → ℝ) : iteratedDeriv 2 f = deriv (deriv f) := by
  rw [show (2 : ℕ) = 1 + 1 from rfl, iteratedDeriv_succ, iteratedDeriv_one]

/-- The third `iteratedDeriv` is the third `deriv`. -/
lemma itd_three (f : ℝ → ℝ) : iteratedDeriv 3 f = deriv (deriv (deriv f)) := by
  rw [show (3 : ℕ) = 2 + 1 from rfl, iteratedDeriv_succ, itd_two]

/-- The fourth `iteratedDeriv` is the fourth `deriv`. -/
lemma itd_four (f : ℝ → ℝ) : iteratedDeriv 4 f = deriv (deriv (deriv (deriv f))) := by
  rw [show (4 : ℕ) = 3 + 1 from rfl, iteratedDeriv_succ, itd_three]

lemma itd_one_val (f : ℝ → ℝ) (x : ℝ) : iteratedDeriv 1 f x = deriv f x := by
  rw [iteratedDeriv_one]

lemma itd_two_val (f : ℝ → ℝ) (x : ℝ) : iteratedDeriv 2 f x = deriv (deriv f) x := by
  rw [itd_two]

lemma itd_three_val (f : ℝ → ℝ) (x : ℝ) :
    iteratedDeriv 3 f x = deriv (deriv (deriv f)) x := by rw [itd_three]

lemma itd_four_val (f : ℝ → ℝ) (x : ℝ) :
    iteratedDeriv 4 f x = deriv (deriv (deriv (deriv f))) x := by rw [itd_four]

/-- One `deriv` on top of a `k`-th `iteratedDeriv` is the `(k+1)`-st one. -/
lemma itd_comp_one (n : ℕ) (f : ℝ → ℝ) :
    iteratedDeriv 1 (iteratedDeriv n f) = iteratedDeriv (n + 1) f := by
  rw [show (iteratedDeriv n f : ℝ → ℝ) = fun t => iteratedDeriv n f t from rfl,
    iteratedDeriv_one, ← iteratedDeriv_succ]

/-- Two `deriv`s on top of a `k`-th `iteratedDeriv` is the `(k+2)`-nd one. -/
lemma itd_comp_two (n : ℕ) (f : ℝ → ℝ) :
    iteratedDeriv 2 (iteratedDeriv n f) = iteratedDeriv (n + 2) f := by
  rw [itd_two, ← iteratedDeriv_one (f := iteratedDeriv n f), itd_comp_one,
    ← iteratedDeriv_succ]

lemma itd_comp_one_val (n : ℕ) (f : ℝ → ℝ) (x : ℝ) :
    iteratedDeriv 1 (iteratedDeriv n f) x = iteratedDeriv (n + 1) f x := by
  rw [itd_comp_one]

lemma itd_comp_two_val (n : ℕ) (f : ℝ → ℝ) (x : ℝ) :
    iteratedDeriv 2 (iteratedDeriv n f) x = iteratedDeriv (n + 2) f x := by
  rw [itd_comp_two]

/-! ### Leibniz expansions of `cos · g` and `sin · g` -/

lemma itd_cos_one (g : ℝ → ℝ) (x : ℝ) (hg : ContDiffAt ℝ 1 g x) :
    iteratedDeriv 1 (fun t => Real.cos t * g t) x
      = -Real.sin x * g x + Real.cos x * iteratedDeriv 1 g x := by
  rw [show (fun t => Real.cos t * g t) = Real.cos * g from rfl, iteratedDeriv_mul]
  · rw [Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_zero]
    simp [Nat.choose]; ring
  · exact Real.contDiff_cos.contDiffAt
  · exact hg

lemma itd_cos_two (g : ℝ → ℝ) (x : ℝ) (hg : ContDiffAt ℝ 2 g x) :
    iteratedDeriv 2 (fun t => Real.cos t * g t) x
      = -Real.cos x * g x - 2 * Real.sin x * iteratedDeriv 1 g x
        + Real.cos x * iteratedDeriv 2 g x := by
  rw [show (fun t => Real.cos t * g t) = Real.cos * g from rfl, iteratedDeriv_mul]
  · rw [Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_zero]
    simp [Nat.choose]; ring
  · exact Real.contDiff_cos.contDiffAt
  · exact hg

lemma itd_cos_three (g : ℝ → ℝ) (x : ℝ) (hg : ContDiffAt ℝ 3 g x) :
    iteratedDeriv 3 (fun t => Real.cos t * g t) x
      = Real.sin x * g x - 3 * Real.cos x * iteratedDeriv 1 g x
        - 3 * Real.sin x * iteratedDeriv 2 g x + Real.cos x * iteratedDeriv 3 g x := by
  rw [show (fun t => Real.cos t * g t) = Real.cos * g from rfl, iteratedDeriv_mul]
  · rw [Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_succ,
      Finset.sum_range_zero]
    simp [Nat.choose]; ring
  · exact Real.contDiff_cos.contDiffAt
  · exact hg

lemma itd_cos_four (g : ℝ → ℝ) (x : ℝ) (hg : ContDiffAt ℝ 4 g x) :
    iteratedDeriv 4 (fun t => Real.cos t * g t) x
      = Real.cos x * g x + 4 * Real.sin x * iteratedDeriv 1 g x
        - 6 * Real.cos x * iteratedDeriv 2 g x - 4 * Real.sin x * iteratedDeriv 3 g x
        + Real.cos x * iteratedDeriv 4 g x := by
  rw [show (fun t => Real.cos t * g t) = Real.cos * g from rfl, iteratedDeriv_mul]
  · rw [Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_succ,
      Finset.sum_range_succ, Finset.sum_range_zero]
    simp [Nat.choose]; ring
  · exact Real.contDiff_cos.contDiffAt
  · exact hg

lemma itd_sin_one (g : ℝ → ℝ) (x : ℝ) (hg : ContDiffAt ℝ 1 g x) :
    iteratedDeriv 1 (fun t => Real.sin t * g t) x
      = Real.cos x * g x + Real.sin x * iteratedDeriv 1 g x := by
  rw [show (fun t => Real.sin t * g t) = Real.sin * g from rfl, iteratedDeriv_mul]
  · rw [Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_zero]
    simp [Nat.choose]; ring
  · exact Real.contDiff_sin.contDiffAt
  · exact hg

lemma itd_sin_two (g : ℝ → ℝ) (x : ℝ) (hg : ContDiffAt ℝ 2 g x) :
    iteratedDeriv 2 (fun t => Real.sin t * g t) x
      = -Real.sin x * g x + 2 * Real.cos x * iteratedDeriv 1 g x
        + Real.sin x * iteratedDeriv 2 g x := by
  rw [show (fun t => Real.sin t * g t) = Real.sin * g from rfl, iteratedDeriv_mul]
  · rw [Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_zero]
    simp [Nat.choose]; ring
  · exact Real.contDiff_sin.contDiffAt
  · exact hg

lemma itd_sin_three (g : ℝ → ℝ) (x : ℝ) (hg : ContDiffAt ℝ 3 g x) :
    iteratedDeriv 3 (fun t => Real.sin t * g t) x
      = -Real.cos x * g x - 3 * Real.sin x * iteratedDeriv 1 g x
        + 3 * Real.cos x * iteratedDeriv 2 g x + Real.sin x * iteratedDeriv 3 g x := by
  rw [show (fun t => Real.sin t * g t) = Real.sin * g from rfl, iteratedDeriv_mul]
  · rw [Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_succ,
      Finset.sum_range_zero]
    simp [Nat.choose]; ring
  · exact Real.contDiff_sin.contDiffAt
  · exact hg

/-! ### The four identities -/

theorem cosBarIdents {u : ℝ → ℝ} (hu : ContDiffOn ℝ 4 u (Set.Ioo 0 (Real.pi / 2))) :
    ∀ θ ∈ Set.Ioo 0 (Real.pi / 2),
      (Work.FTS.EllipticEst.Lzero1 u θ
          = - Real.cos θ * deriv (deriv (fun θ' => u θ' / Real.cos θ')) θ
            + 3 * Real.sin θ * deriv (fun θ' => u θ' / Real.cos θ') θ
            - 4 * Real.cos θ * (u θ / Real.cos θ)) ∧
      (deriv (deriv u) θ
          = Real.sin θ * deriv (fun θ' => u θ' / Real.cos θ') θ
            - 5 * Real.cos θ * (u θ / Real.cos θ) - Work.FTS.EllipticEst.Lzero1 u θ) ∧
      (deriv (deriv (deriv u)) θ
          = Real.sin θ * deriv (deriv (fun θ' => u θ' / Real.cos θ')) θ
            - 4 * Real.cos θ * deriv (fun θ' => u θ' / Real.cos θ') θ
            + 5 * Real.sin θ * (u θ / Real.cos θ)
            - deriv (Work.FTS.EllipticEst.Lzero1 u) θ) ∧
      (deriv (deriv (deriv (deriv u))) θ
          = Real.sin θ * deriv (deriv (deriv (fun θ' => u θ' / Real.cos θ'))) θ
            - 3 * Real.cos θ * deriv (deriv (fun θ' => u θ' / Real.cos θ')) θ
            + 9 * Real.sin θ * deriv (fun θ' => u θ' / Real.cos θ') θ
            + 5 * Real.cos θ * (u θ / Real.cos θ)
            - deriv (deriv (Work.FTS.EllipticEst.Lzero1 u)) θ) := by
  intro θ hθ
  have hIoo : Set.Ioo (0 : ℝ) (Real.pi / 2) ∈ 𝓝 θ := isOpen_Ioo.mem_nhds hθ
  set ψ : ℝ → ℝ := fun t => u t / Real.cos t with hψdef
  have hcos_ne : ∀ t ∈ Set.Ioo (0 : ℝ) (Real.pi / 2), Real.cos t ≠ 0 := by
    intro t ht
    exact ne_of_gt (Real.cos_pos_of_mem_Ioo
      ⟨by linarith [ht.1, Real.pi_pos], by linarith [ht.2, Real.pi_pos]⟩)
  have hcosθ : Real.cos θ ≠ 0 := hcos_ne θ hθ
  have hψC : ContDiffOn ℝ 4 ψ (Set.Ioo (0 : ℝ) (Real.pi / 2)) :=
    hu.div Real.contDiff_cos.contDiffOn hcos_ne
  have hψAt : ContDiffAt ℝ 4 ψ θ := hψC.contDiffAt hIoo
  have hψOf : ∀ t ∈ Set.Ioo (0 : ℝ) (Real.pi / 2), ContDiffAt ℝ 4 ψ t :=
    fun t ht => hψC.contDiffAt (isOpen_Ioo.mem_nhds ht)
  -- smoothness of the other functions involved
  have huC1 : ContDiffAt ℝ 1 u θ := (hu.contDiffAt hIoo).of_le (by norm_num)
  have huC2 : ContDiffAt ℝ 2 u θ := (hu.contDiffAt hIoo).of_le (by norm_num)
  have huC3 : ContDiffAt ℝ 3 u θ := (hu.contDiffAt hIoo).of_le (by norm_num)
  have htanC2 : ContDiffAt ℝ 2 Real.tan θ := Real.contDiffAt_tan.mpr hcosθ
  have htanC3 : ContDiffAt ℝ 3 Real.tan θ := Real.contDiffAt_tan.mpr hcosθ
  have htuC2 : ContDiffAt ℝ 2 (fun s => Real.tan s * u s) θ := htanC2.mul huC2
  have htuC3 : ContDiffAt ℝ 3 (fun s => Real.tan s * u s) θ := htanC3.mul huC3
  -- `u = cos · ψ` near every point of the interval
  have hu_eq : ∀ t ∈ Set.Ioo (0 : ℝ) (Real.pi / 2), u =ᶠ[𝓝 t] fun s => Real.cos s * ψ s := by
    intro t ht
    filter_upwards [isOpen_Ioo.mem_nhds ht] with s hs
    have hc : Real.cos s ≠ 0 := hcos_ne s hs
    show u s = Real.cos s * ψ s
    rw [hψdef, ← mul_div_assoc, mul_div_cancel_left₀ (u s) hc]
  -- `tan · u = sin · ψ` near every point of the interval
  have htan_eq : ∀ t ∈ Set.Ioo (0 : ℝ) (Real.pi / 2),
      (fun s => Real.tan s * u s) =ᶠ[𝓝 t] fun s => Real.sin s * ψ s := by
    intro t ht
    filter_upwards [isOpen_Ioo.mem_nhds ht] with s hs
    have hc : Real.cos s ≠ 0 := hcos_ne s hs
    show Real.tan s * u s = Real.sin s * ψ s
    rw [Real.tan_eq_sin_div_cos, hψdef, div_mul_eq_mul_div, mul_div_assoc]
  -- expansions of the derivatives of `u`
  have hu1 : ∀ t ∈ Set.Ioo (0 : ℝ) (Real.pi / 2),
      iteratedDeriv 1 u t = -Real.sin t * ψ t + Real.cos t * iteratedDeriv 1 ψ t := by
    intro t ht
    rw [Filter.EventuallyEq.iteratedDeriv_eq 1 (hu_eq t ht)]
    exact itd_cos_one ψ t ((hψOf t ht).of_le (by norm_num))
  have hu2 : ∀ t ∈ Set.Ioo (0 : ℝ) (Real.pi / 2),
      iteratedDeriv 2 u t = -Real.cos t * ψ t - 2 * Real.sin t * iteratedDeriv 1 ψ t
        + Real.cos t * iteratedDeriv 2 ψ t := by
    intro t ht
    rw [Filter.EventuallyEq.iteratedDeriv_eq 2 (hu_eq t ht)]
    exact itd_cos_two ψ t ((hψOf t ht).of_le (by norm_num))
  have hu3 : ∀ t ∈ Set.Ioo (0 : ℝ) (Real.pi / 2),
      iteratedDeriv 3 u t = Real.sin t * ψ t - 3 * Real.cos t * iteratedDeriv 1 ψ t
        - 3 * Real.sin t * iteratedDeriv 2 ψ t + Real.cos t * iteratedDeriv 3 ψ t := by
    intro t ht
    rw [Filter.EventuallyEq.iteratedDeriv_eq 3 (hu_eq t ht)]
    exact itd_cos_three ψ t ((hψOf t ht).of_le (by norm_num))
  have hu4 : ∀ t ∈ Set.Ioo (0 : ℝ) (Real.pi / 2),
      iteratedDeriv 4 u t = Real.cos t * ψ t + 4 * Real.sin t * iteratedDeriv 1 ψ t
        - 6 * Real.cos t * iteratedDeriv 2 ψ t - 4 * Real.sin t * iteratedDeriv 3 ψ t
        + Real.cos t * iteratedDeriv 4 ψ t := by
    intro t ht
    rw [Filter.EventuallyEq.iteratedDeriv_eq 4 (hu_eq t ht)]
    exact itd_cos_four ψ t ((hψOf t ht).of_le (by norm_num))
  -- expansions of the derivatives of `tan θ · u`
  have htu1 : ∀ t ∈ Set.Ioo (0 : ℝ) (Real.pi / 2),
      iteratedDeriv 1 (fun s => Real.tan s * u s) t
        = Real.cos t * ψ t + Real.sin t * iteratedDeriv 1 ψ t := by
    intro t ht
    rw [Filter.EventuallyEq.iteratedDeriv_eq 1 (htan_eq t ht)]
    exact itd_sin_one ψ t ((hψOf t ht).of_le (by norm_num))
  have htu2 : ∀ t ∈ Set.Ioo (0 : ℝ) (Real.pi / 2),
      iteratedDeriv 2 (fun s => Real.tan s * u s) t
        = -Real.sin t * ψ t + 2 * Real.cos t * iteratedDeriv 1 ψ t
          + Real.sin t * iteratedDeriv 2 ψ t := by
    intro t ht
    rw [Filter.EventuallyEq.iteratedDeriv_eq 2 (htan_eq t ht)]
    exact itd_sin_two ψ t ((hψOf t ht).of_le (by norm_num))
  have htu3 : ∀ t ∈ Set.Ioo (0 : ℝ) (Real.pi / 2),
      iteratedDeriv 3 (fun s => Real.tan s * u s) t
        = -Real.cos t * ψ t - 3 * Real.sin t * iteratedDeriv 1 ψ t
          + 3 * Real.cos t * iteratedDeriv 2 ψ t + Real.sin t * iteratedDeriv 3 ψ t := by
    intro t ht
    rw [Filter.EventuallyEq.iteratedDeriv_eq 3 (htan_eq t ht)]
    exact itd_sin_three ψ t ((hψOf t ht).of_le (by norm_num))
  -- the value of `Lzero1 u`
  have hLval : ∀ t ∈ Set.Ioo (0 : ℝ) (Real.pi / 2),
      Lzero1 u t = -4 * Real.cos t * ψ t + 3 * Real.sin t * iteratedDeriv 1 ψ t
        - Real.cos t * iteratedDeriv 2 ψ t := by
    intro t ht
    have h0 : u t = Real.cos t * ψ t := (hu_eq t ht).self_of_nhds
    have hd2 : deriv (fun s => deriv u s) t = iteratedDeriv 2 u t := by
      rw [show (2 : ℕ) = 1 + 1 from rfl, iteratedDeriv_succ, iteratedDeriv_one]
    have hd1 : deriv (fun s => Real.tan s * u s) t
        = iteratedDeriv 1 (fun s => Real.tan s * u s) t := by rw [iteratedDeriv_one]
    unfold Lzero1
    rw [hd2, hd1, hu2 t ht, htu1 t ht, h0]
    ring
  -- `Lzero1 u` as a function
  have hL_eq : Lzero1 u = -(iteratedDeriv 2 u) + iteratedDeriv 1 (fun s => Real.tan s * u s)
      - (fun t => 6 * u t) := by
    funext t
    have hd2 : deriv (fun s => deriv u s) t = iteratedDeriv 2 u t := by
      rw [show (2 : ℕ) = 1 + 1 from rfl, iteratedDeriv_succ, iteratedDeriv_one]
    have hd1 : deriv (fun s => Real.tan s * u s) t
        = iteratedDeriv 1 (fun s => Real.tan s * u s) t := by rw [iteratedDeriv_one]
    unfold Lzero1
    rw [hd2, hd1]
    simp only [Pi.neg_apply, Pi.add_apply, Pi.sub_apply]
  -- smoothness of the two pieces of `hL_eq`
  have hu2C2 : ContDiffAt ℝ 2 (iteratedDeriv 2 u) θ :=
    contDiffAt_iteratedDeriv (f := u) (n := 4) (k := 2) (hu.contDiffAt hIoo) (by norm_num)
  have hu2C1 : ContDiffAt ℝ 1 (iteratedDeriv 2 u) θ := hu2C2.of_le (by norm_num)
  have htu1C1 : ContDiffAt ℝ 1 (iteratedDeriv 1 (fun s => Real.tan s * u s)) θ :=
    contDiffAt_iteratedDeriv (f := fun s => Real.tan s * u s) (n := 2) (k := 1) htuC2 (by norm_num)
  have htu1C2 : ContDiffAt ℝ 2 (iteratedDeriv 1 (fun s => Real.tan s * u s)) θ :=
    contDiffAt_iteratedDeriv (f := fun s => Real.tan s * u s) (n := 3) (k := 1) htuC3 (by norm_num)
  -- first derivative of `Lzero1 u`
  have hL1 : iteratedDeriv 1 (Lzero1 u) θ
      = -iteratedDeriv 3 u θ + iteratedDeriv 2 (fun s => Real.tan s * u s) θ
        - 6 * iteratedDeriv 1 u θ := by
    rw [hL_eq]
    have hA : ContDiffAt ℝ 1
        (-(iteratedDeriv 2 u) + iteratedDeriv 1 (fun s => Real.tan s * u s)) θ :=
      (ContDiffAt.neg hu2C1).add htu1C1
    have hB : ContDiffAt ℝ 1 (fun t => 6 * u t) θ := contDiffAt_const.mul huC1
    rw [iteratedDeriv_sub hA hB]
    have hA1 : ContDiffAt ℝ 1 (-(iteratedDeriv 2 u)) θ := ContDiffAt.neg hu2C1
    have hA2 : ContDiffAt ℝ 1 (iteratedDeriv 1 (fun s => Real.tan s * u s)) θ := htu1C1
    rw [iteratedDeriv_add hA1 hA2, iteratedDeriv_neg,
      iteratedDeriv_const_mul (6 : ℝ) huC1]
    rw [itd_comp_one_val 2 u θ, itd_comp_one_val 1 (fun s => Real.tan s * u s) θ]
  -- second derivative of `Lzero1 u`
  have hL2 : iteratedDeriv 2 (Lzero1 u) θ
      = -iteratedDeriv 4 u θ + iteratedDeriv 3 (fun s => Real.tan s * u s) θ
        - 6 * iteratedDeriv 2 u θ := by
    rw [hL_eq]
    have hA : ContDiffAt ℝ 2
        (-(iteratedDeriv 2 u) + iteratedDeriv 1 (fun s => Real.tan s * u s)) θ :=
      (ContDiffAt.neg hu2C2).add htu1C2
    have hB : ContDiffAt ℝ 2 (fun t => 6 * u t) θ := contDiffAt_const.mul huC2
    rw [iteratedDeriv_sub hA hB]
    have hA1 : ContDiffAt ℝ 2 (-(iteratedDeriv 2 u)) θ := ContDiffAt.neg hu2C2
    have hA2 : ContDiffAt ℝ 2 (iteratedDeriv 1 (fun s => Real.tan s * u s)) θ := htu1C2
    rw [iteratedDeriv_add hA1 hA2, iteratedDeriv_neg,
      iteratedDeriv_const_mul (6 : ℝ) huC2]
    rw [itd_comp_two_val 2 u θ, itd_comp_two_val 1 (fun s => Real.tan s * u s) θ]
  refine ⟨?_, ?_, ?_, ?_⟩
  · -- identity 1
    rw [hLval θ hθ, itd_one_val, itd_two_val]
    ring
  · -- identity 2
    rw [← itd_two_val u θ, hu2 θ hθ, hLval θ hθ, itd_one_val, itd_two_val]
    ring
  · -- identity 3
    rw [← itd_three_val u θ, ← itd_one_val (Lzero1 u) θ, hL1, hu3 θ hθ, htu2 θ hθ,
      hu1 θ hθ, itd_one_val, itd_two_val]
    ring
  · -- identity 4
    rw [← itd_four_val u θ, ← itd_two_val (Lzero1 u) θ, hL2, hu4 θ hθ, htu3 θ hθ,
      hu2 θ hθ, itd_one_val, itd_two_val, itd_three_val]
    ring

end Work.FTS.EllipticEst.remov
