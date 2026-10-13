/-
Copyright: work module for the Elgindi finite-time singularity project.

# Pointwise domination of `2 |h · ∂_θh| w²` by the `ℋ⁴`-integrand

For a datum `f` which is `C^∞` on the open quadrant (`Work.FTS.EllipticEst.SmoothOpen`), a
mixed slot `h = D_z^jD_θ^i f` with `1 ≤ i` and `i + j ≤ 3` and its **plain** angular
derivative satisfy the pointwise bound

  `2 · |h · ∂_θh| · w(z)²  ≤  HkIntegrand α 4 f z θ`      (`z > 0`, `0 < θ < π/2`).

The route is a one-line consequence of the shift identity `D_θ^{i+1}f = sin(2θ)·∂_θ(D_θ^if)`
(`Work.FTS.TransportS.T2SupB2.sin_mul_pth_mixed`), i.e. `∂_θh = (D_z^jD_θ^{i+1}f)/sin(2θ)`:

* the exact weights cancel, `w² = (Wt α z θ)² · sin(2θ)^{gam α}`, so
  `2 |h ∂_θh| w² = 2 |h·Wt| · |h₁·Wt| · sin(2θ)^{gam α - 1}` where `h₁ = D_z^jD_θ^{i+1}f`;
* `gam α - 1 = α/10 ≥ 0` and `sin(2θ) ≤ 1`, so the last factor is `≤ 1`;
* `2|A||B| ≤ A² + B²` (AM–GM) for `A = h·Wt`, `B = h₁·Wt`;
* both slots `(j,i)` and `(j,i+1)` — of order `i + j ≤ 3` resp. `i + 1 + j ≤ 4` — are
  summands of the *same* double sum in `HkIntegrand α 4 f`, which is the sharp form needed
  (bounding each square separately would only give the factor `2`).

Everything here is `sorry`-free and rests on `[propext, Classical.choice, Quot.sound]`.
-/
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Submission.Work.Spaces.Defs
import Submission.Work.FTS.EllipticEst.OpenQDefs
import Submission.Work.FTS.TransportS.T2SupB2.mixed_pointwise_le_Xn
import Submission.Work.H2.T1Q.PwBdQ

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology

namespace Work.FTS.StrongEps.E4R3.NauxAux.ZSliceAux

set_option autoImplicit false

/-! ## The elementary AM–GM with the `sin(2θ)^(gam α - 1) ≤ 1` slack -/

/-- For `0 < s ≤ 1`, `γ ≥ 1`, `h,h₁,w ∈ ℝ`:
`2 |h| |h₁| w² / s ≤ (h·(w·s^{-γ/2}))² + (h₁·(w·s^{-γ/2}))²`.

Multiplying by `s > 0` this is `2|h||h₁|w² ≤ (h² + h₁²)·w²·s^{1-γ}`, which follows from the
AM–GM `2|h||h₁| ≤ h² + h₁²` in the first factor and from `1 ≤ s^{1-γ}` (as `s ≤ 1` and the
exponent `1 - γ` is nonpositive) in the second. -/
theorem two_abs_mul_div_le (h h₁ s γ w : ℝ) (hs : 0 < s) (hs1 : s ≤ 1) (hγ : 1 ≤ γ) :
    2 * (|h| * |h₁| / s) * w ^ 2
      ≤ (h * (w * s ^ (-(γ / 2)))) ^ 2 + (h₁ * (w * s ^ (-(γ / 2)))) ^ 2 := by
  have hw2 : 0 ≤ w ^ 2 := sq_nonneg w
  have hhalf : (s ^ (-(γ / 2))) ^ 2 = s ^ (-γ) := by
    rw [sq, ← Real.rpow_add hs]; congr 1; ring
  have hWsq : ∀ A : ℝ, (A * (w * s ^ (-(γ / 2)))) ^ 2 = A ^ 2 * w ^ 2 * s ^ (-γ) := by
    intro A
    rw [mul_pow, mul_pow, hhalf]; ring
  rw [hWsq h, hWsq h₁]
  have hle : 1 ≤ s ^ (1 - γ) := by
    rw [show (1 : ℝ) - γ = -(γ - 1) by ring]
    exact Work.H2.T1Q.one_le_rpow_neg hs hs1 (by linarith)
  have hab : 2 * |h| * |h₁| ≤ h ^ 2 + h₁ ^ 2 := by
    nlinarith [sq_nonneg (|h| - |h₁|), sq_abs h, sq_abs h₁]
  have hmul : s * (2 * (|h| * |h₁| / s) * w ^ 2)
      ≤ s * (h ^ 2 * w ^ 2 * s ^ (-γ) + h₁ ^ 2 * w ^ 2 * s ^ (-γ)) := by
    have e1 : s * (2 * (|h| * |h₁| / s) * w ^ 2) = 2 * |h| * |h₁| * w ^ 2 := by
      field_simp
    have e2 : s * (h ^ 2 * w ^ 2 * s ^ (-γ) + h₁ ^ 2 * w ^ 2 * s ^ (-γ))
        = (h ^ 2 + h₁ ^ 2) * w ^ 2 * s ^ (1 - γ) := by
      rw [show (1 : ℝ) - γ = 1 + (-γ) by ring, Real.rpow_add hs, Real.rpow_one]
      ring
    rw [e1, e2]
    calc 2 * |h| * |h₁| * w ^ 2 ≤ (h ^ 2 + h₁ ^ 2) * w ^ 2 :=
          mul_le_mul_of_nonneg_right hab hw2
      _ ≤ (h ^ 2 + h₁ ^ 2) * w ^ 2 * s ^ (1 - γ) :=
          le_mul_of_one_le_right (mul_nonneg (by positivity) hw2) hle
  exact le_of_mul_le_mul_left hmul hs

/-! ## The two adjacent mixed slots inside one `HkIntegrand` -/

/-- The two specific mixed slots `(j,i)` and `(j,i+1)` with the weight `Wt`, for `1 ≤ i` and
`i + j ≤ 3`, are simultaneously dominated by the `ℋ⁴`-integrand of `f`: this is the sharp
form (`2|A||B| ≤ A² + B²` applies to the *sum*, not to each square separately). -/
theorem two_mixed_sq_le_HkIntegrand (α : ℝ) (f : ℝ → ℝ → ℝ) (z θ : ℝ) (j i : ℕ)
    (hi : 1 ≤ i) (hij : i + j ≤ 3) :
    (Work.Spaces.mixed j i f z θ * Work.Spaces.Wt α z θ) ^ 2
      + (Work.Spaces.mixed j (i + 1) f z θ * Work.Spaces.Wt α z θ) ^ 2
      ≤ Work.Spaces.HkIntegrand α 4 f z θ := by
  set G : ℕ → ℝ := fun a => ∑ b ∈ Finset.range 5,
      (if 1 ≤ a ∧ a + b ≤ 4 then (Work.Spaces.mixed b a f z θ * Work.Spaces.Wt α z θ) ^ 2
        else 0) with hGdef
  have hGnn : ∀ a ∈ Finset.range 5, 0 ≤ G a := by
    intro a _
    rw [hGdef]
    exact Finset.sum_nonneg fun b _ => by split_ifs with h <;> simp [sq_nonneg]
  have hpair : G i + G (i + 1) ≤ ∑ a ∈ Finset.range 5, G a := by
    have hsub : ({i, i + 1} : Finset ℕ) ⊆ Finset.range 5 := by
      intro a ha
      simp only [Finset.mem_insert, Finset.mem_singleton] at ha
      rcases ha with rfl | rfl <;> simp only [Finset.mem_range] <;> omega
    have h1 := Finset.sum_le_sum_of_subset_of_nonneg hsub (fun a ha _ => hGnn a ha)
    rwa [Finset.sum_pair (by omega : i ≠ i + 1)] at h1
  have hZi : (Work.Spaces.mixed j i f z θ * Work.Spaces.Wt α z θ) ^ 2 ≤ G i := by
    have hmemj : j ∈ Finset.range 5 := by simp only [Finset.mem_range]; omega
    have h2 := Finset.single_le_sum (f := fun b => (if 1 ≤ i ∧ i + b ≤ 4 then
        (Work.Spaces.mixed b i f z θ * Work.Spaces.Wt α z θ) ^ 2 else 0))
      (fun b _ => by split_ifs with h <;> simp [sq_nonneg]) hmemj
    rw [ite_eq_left ⟨hi, by omega⟩] at h2
    rw [hGdef]
    exact h2
  have hZi1 : (Work.Spaces.mixed j (i + 1) f z θ * Work.Spaces.Wt α z θ) ^ 2 ≤ G (i + 1) := by
    have hmemj : j ∈ Finset.range 5 := by simp only [Finset.mem_range]; omega
    have h2 := Finset.single_le_sum (f := fun b => (if 1 ≤ i + 1 ∧ i + 1 + b ≤ 4 then
        (Work.Spaces.mixed b (i + 1) f z θ * Work.Spaces.Wt α z θ) ^ 2 else 0))
      (fun b _ => by split_ifs with h <;> simp [sq_nonneg]) hmemj
    rw [ite_eq_left ⟨by omega, by omega⟩] at h2
    rw [hGdef]
    exact h2
  have hZ : 0 ≤ ∑ i ∈ Finset.range 5,
      (Work.Spaces.DzIter i f z θ * (Work.Spaces.w z
        / Real.sin (2 * θ) ^ (Work.Spaces.eta / 2))) ^ 2 :=
    Work.Spaces.hkZSum_nonneg α 4 f z θ
  have hstep : (Work.Spaces.mixed j i f z θ * Work.Spaces.Wt α z θ) ^ 2
      + (Work.Spaces.mixed j (i + 1) f z θ * Work.Spaces.Wt α z θ) ^ 2
      ≤ (∑ i ∈ Finset.range 5,
          (Work.Spaces.DzIter i f z θ * (Work.Spaces.w z
            / Real.sin (2 * θ) ^ (Work.Spaces.eta / 2))) ^ 2)
        + ∑ a ∈ Finset.range 5, G a :=
    le_trans (add_le_add hZi hZi1) (le_trans hpair (le_add_of_nonneg_left hZ))
  rw [Work.Spaces.HkIntegrand]
  exact hstep

/-! ## The target -/

/-- The pointwise `z`-slice bound of the window device: for a slot `h = D_z^jD_θ^i f` of order
`≤ 3` with `i ≥ 1`, the pairing `2 h · ∂_θh · w²` is dominated by the `ℋ⁴`-integrand. -/
theorem absPairMulWLeHkIntegrand {α : ℝ} {f : ℝ → ℝ → ℝ} (hα : 0 < α)
    (hF : Work.FTS.EllipticEst.SmoothOpen f) (j i : ℕ) (hi : 1 ≤ i) (hij : i + j ≤ 3)
    {z θ : ℝ} (hz : z ∈ Work.Spaces.Iz) (hθ : θ ∈ Set.Ioo 0 (Real.pi / 2)) :
    2 * |Work.Spaces.mixed j i f z θ * Work.Spaces.pth (Work.Spaces.mixed j i f) z θ|
        * (Work.Spaces.w z) ^ 2 ≤ Work.Spaces.HkIntegrand α 4 f z θ := by
  have hzig : (0 : ℝ) ≤ z := hz
  rcases eq_or_lt_of_le hzig with hz0 | hzpos
  · -- `z = 0`: the weight `w` vanishes.
    subst hz0
    have hzz : (Work.Spaces.w (0 : ℝ)) ^ 2 = 0 := by
      rw [Work.Spaces.w]; norm_num
    have hnn : 0 ≤ Work.Spaces.HkIntegrand α 4 f 0 θ := by
      rw [Work.Spaces.HkIntegrand]
      exact add_nonneg (Work.Spaces.hkZSum_nonneg α 4 f 0 θ)
        (Work.Spaces.hkMixedSum_nonneg α 4 f 0 θ)
    rw [hzz, mul_zero]
    exact hnn
  · -- `z > 0`: the shift identity `∂_θh = D_z^jD_θ^{i+1}f / sin(2θ)`.
    have hs : 0 < Real.sin (2 * θ) :=
      Real.sin_pos_of_pos_of_lt_pi (by linarith [hθ.1]) (by linarith [hθ.2, Real.pi_pos])
    have hs1 : Real.sin (2 * θ) ≤ 1 := Real.sin_le_one _
    have hγ : 1 ≤ Work.Spaces.gam α := by rw [Work.Spaces.gam]; linarith
    have hmul := Work.FTS.TransportS.T2SupB2.sin_mul_pth_mixed hF j i hzpos hθ
    have hpth : Work.Spaces.pth (Work.Spaces.mixed j i f) z θ
        = Work.Spaces.mixed j (i + 1) f z θ / Real.sin (2 * θ) := by
      rw [eq_div_iff (ne_of_gt hs), mul_comm]
      exact hmul
    have hkey : 2 * |Work.Spaces.mixed j i f z θ
          * Work.Spaces.pth (Work.Spaces.mixed j i f) z θ| * (Work.Spaces.w z) ^ 2
        = 2 * (|Work.Spaces.mixed j i f z θ| * |Work.Spaces.mixed j (i + 1) f z θ|
            / Real.sin (2 * θ)) * (Work.Spaces.w z) ^ 2 := by
      rw [hpth, abs_mul, abs_div, abs_of_pos hs]
      ring
    rw [hkey]
    refine le_trans (two_abs_mul_div_le (Work.Spaces.mixed j i f z θ)
      (Work.Spaces.mixed j (i + 1) f z θ) (Real.sin (2 * θ)) (Work.Spaces.gam α)
      (Work.Spaces.w z) hs hs1 hγ) ?_
    exact two_mixed_sq_le_HkIntegrand α f z θ j i hi hij

end Work.FTS.StrongEps.E4R3.NauxAux.ZSliceAux
