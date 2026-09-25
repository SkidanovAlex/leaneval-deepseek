import Mathlib
import Submission.Work.Beltrami.Cauchy
import Submission.Work.Beltrami.beurling_bounded
import Submission.Work.Beltrami.beurling_sub
import Submission.Work.Beltrami.beurling_holder_uniform
import Submission.Work.Beltrami.norm_diffQuot_iterate_le
import Submission.Work.Beltrami.contDiff_of_diffQuot_L2
import Submission.Work.Beltrami.beurling_isometry_L2

/-!
# Regularity of the fixed point of `u = f + μ · beurling u`

Target: `Work.Beltrami.smooth_of_beurling_fixed` (statement at the bottom of this file).

## The mathematical route

`beurling` is the regularised Calderón–Zygmund operator `B f z = -(1/π) ∫ (f ζ - χ(ζ-z) f z)
(ζ-z)⁻² dA(ζ)` (`Submission/Work/Beltrami/Cauchy.lean`); `B = ∂ T` up to a constant, and the
equation `u = f + μ · B u` is the integral form of the Beltrami equation `∂̄ (T u) = μ ∂ (T u) + f`.
The proof of smoothness is the elliptic bootstrap, organised through **difference quotients**:

* `beurling_comp_add`, `beurling_diffQuot`, `beurling_diffQuot_iterate`: `B` is a convolution
  operator, hence commutes with translations and with forward differences:
  `Δ_h^N (B u) = B (Δ_h^N u)`.
* `diffQuot_iterate_bounds`: `Δ_h^N u` is bounded by `2^N M`, `α`-Hölder with constant `2^N K`,
  and supported in the ball of radius `R' + N ‖h‖`.
* `iterate_diffQuot_mul` (proved separately, `Submission/Work/Beltrami/iterate_diffQuot_mul.lean`):
  the Leibniz rule for iterated forward differences.
* **Source identity.**  If `u = f + μ · B u` then
  `Δ_h^N u = bSource h N μ f (B u) + μ · B (Δ_h^N u)`, where
  `bSource h N μ f Bu = Δ_h^N f + Σ_{i=1}^{N} C(N,i) (Δ_h^i μ) (Δ_h^{N-i} Bu)(· + i h)`.
  This is the crucial structural fact: *the difference quotients of `u` solve the same equation*,
  with a source built from `Δ_h^N f` and from difference quotients of `μ` and of `B u`.
* **The gain of one derivative.**  Suppose `B u ∈ C^{p,α}`.  For `N := p+2` and `|h| ≤ 1`,
  `Δ_h^N u` is supported in the fixed ball of radius `R' + N` and its source is `≲ |h|^{p+1+α}`.
  Solving the equation by the Neumann series (only the *first* application of `μ B` has to be
  estimated on the big ball; every later term is supported in the fixed set `supp μ`, so the
  contraction factor is `δ · C(α) (1 + R_μ)` uniformly in `N`, `p`), one gets
  `‖Δ_h^N u‖_∞ ≤ C (1+N) |h|^{p+1+α}`.  Feeding this into the Zygmund/Besov extraction lemma
  (`Submission/Work/Beltrami/holder_of_diffQuot_bound.lean`) gives `u ∈ C^{p+1,γ}` for every
  `γ < α`.
* **Assembly.**  Since `u ∈ C^{p,α}` implies `B u ∈ C^{p,α}` (`beurling_maps_holder`), the gain
  iterates: `u ∈ C^{0,α}` (given) ⟹ `B u ∈ C^{0,α}` ⟹ (`p = 0`) `u ∈ C^{1,α'}` ⟹
  `B u ∈ C^{1,α'}` ⟹ (`p = 1`) `u ∈ C^{2,α''}` ⟹ …, so `u ∈ C^{m,α_m}` for all `m` with
  `α_m > 0`, hence `ContDiff ℝ ∞ u`.

## Delegated lemmas (paths relative to the workspace root)

* `Beltrami/beurling_holder_uniform` — uniform (in `f`, `M`, `K`, `R`) Schauder estimate for `B`
  on `C^{0,α}`; needs the explicit constants of `beurling_bounded` and of the (in progress)
  `beurling_holder_difference`.
* `Beltrami/beurling_maps_holder` — `B` preserves `C^{p,α}` with bounds.
* `Beltrami/holder_of_diffQuot_bound` — the Zygmund/Besov extraction (restated with the necessary
  hypothesis `Continuous u`: without it the statement is *false*, because all differences of
  order `≥ 2` of a discontinuous additive function vanish).
* `Beltrami/iterate_diffQuot_mul` — the Leibniz rule (proved; note this module imports *this*
  file, so it can be used by further delegates but not imported back here).

## State of the formalisation

Proved in this file: `beurling_comp_add`, `beurling_comp_add'`, `beurling_diffQuot`,
`diffQuot_iterate_bounds`, `beurling_diffQuot_iterate`, `diffQuot_add`, `iterate_diffQuot_add`,
`diffQuot_iterate_shift`, `iterate_diffQuot_mul'` (this is the Leibniz rule, duplicated here
because the module `Beltrami/iterate_diffQuot_mul` imports *this* file) and the **source
identity** `diffQuot_iterate_eq_bSource`.

Delegated and proved: `Beltrami/beurling_holder_uniform` (uniform Schauder estimate for `B`;
imported above).
Delegated and in progress: `Beltrami/beurling_maps_holder` (`B` preserves `C^{p,α}`),
`Beltrami/holder_of_diffQuot_bound` (Zygmund extraction, restated with `Continuous u`).

## TODO (remaining formalisation)

1. **Source bounds.**  From `B u ∈ C^{p,α}` (hypothesis of the gain step) and the explicit
   difference-quotient bounds of a `C^{p,α}` function, bound `bSource h N μ f (B u)` in the
   `C^{0,α}`/sup norm by `C (1+N) |h|^{p+1+α}` for `N = p+2`, `|h| ≤ 1`.  (Use the Leibniz
   bounds of `iterate_diffQuot_mul'`, `diffQuot_iterate_bounds`, and the fact that
   `Δ^i μ` is `O(|h|)` in `C^{0,α}` for `i ≥ 1`.)
2. **Solution estimate / Neumann series.**  For `v = G + μ · B v` with `v` bounded, `α`-Hölder and
   supported in `ball R`, and `μ` supported in `ball S`:
   `‖v‖_∞ + θ [v]_α ≤ C (‖G‖_∞ + θ [G]_α)` for a small `δ` and a suitable weight `θ`.
   Only the *first* application of `μ B` has to be estimated with the big support radius `R`; all
   subsequent terms are supported in `ball S`, so the contraction factor is `δ C(α)(1+S)`
   *uniformly in `N` and `p`* (this is what makes the single `δ` of the theorem work).
   Use `beurling_holder_uniform`.
3. **Gain of one derivative.**  Combine 1, 2 and `holder_of_diffQuot_bound` to get: if
   `B u ∈ C^{p,α}` and `u = f + μ B u` (bounded, compactly supported, `‖μ‖ ≤ δ`) then
   `u ∈ C^{p+1,γ}` for every `γ < α`.  (Feed the bounds on `Δ_h^{p+2} u` to the extraction lemma;
   `Continuous u` is available since `u` is `α`-Hölder.)
4. **Assembly.**  Iterate step 3 using `beurling_maps_holder` (`u ∈ C^{p,γ} ⟹ B u ∈ C^{p,γ}`),
   starting from `u ∈ C^{0,α}` (given).  Conclusion: `u ∈ C^{m,α_m}` for all `m` with
   `α_m > 0`, hence `ContDiff ℝ ∞ u`, and then conclude `smooth_of_beurling_fixed` (choose `δ`
   small enough for step 2; the hypothesis `R' < ‖z‖ → u z = 0` gives the compact support).
-/
namespace Work.Beltrami

open MeasureTheory Filter
open scoped ContDiff Topology
open Work.Beltrami

noncomputable section

/-- Translation invariance of `beurling`: the Beurling transform is a convolution operator. -/
lemma beurling_comp_add (f : ℂ → ℂ) (a z : ℂ) :
    beurling (fun w => f (a + w)) z = beurling f (a + z) := by
  rw [beurling_eq_translate, beurling_eq_translate]
  congr 1
  apply integral_congr_ae
  filter_upwards with w
  simp only [add_assoc]

/-- The forward difference quotient `Δ_h f = f (· + h) - f`. -/
def diffQuot (h : ℂ) (f : ℂ → ℂ) : ℂ → ℂ := fun x => f (x + h) - f x

@[simp] lemma diffQuot_apply (h : ℂ) (f : ℂ → ℂ) (x : ℂ) :
    diffQuot h f x = f (x + h) - f x := rfl

/-- The Beurling transform commutes with translations (reverse form). -/
lemma beurling_comp_add' (f : ℂ → ℂ) (h : ℂ) :
    beurling (fun w => f (w + h)) = fun z => beurling f (z + h) := by
  funext z
  rw [show (fun w : ℂ => f (w + h)) = (fun w : ℂ => f (h + w)) from by
    funext w; rw [add_comm]]
  rw [beurling_comp_add f h z, add_comm]

/-- **The Beurling transform commutes with difference quotients.** -/
lemma beurling_diffQuot {α M K R : ℝ} (hα : 0 < α) (hα1 : α < 1) (hR : 0 ≤ R)
    {u : ℂ → ℂ} (hM : ∀ z, ‖u z‖ ≤ M) (hK : ∀ x y : ℂ, ‖u x - u y‖ ≤ K * ‖x - y‖ ^ α)
    (hsupp : ∀ z, R < ‖z‖ → u z = 0) (h : ℂ) :
    diffQuot h (beurling u) = beurling (diffQuot h u) := by
  have hR' : (0 : ℝ) ≤ R + ‖h‖ := by positivity
  have hM' : ∀ z, ‖(fun w => u (w + h)) z‖ ≤ M := fun z => hM (z + h)
  have hK' : ∀ x y : ℂ, ‖(fun w => u (w + h)) x - (fun w => u (w + h)) y‖ ≤ K * ‖x - y‖ ^ α := by
    intro x y
    have h2 := hK (x + h) (y + h)
    rw [show x + h - (y + h) = x - y from by ring] at h2
    exact h2
  have hsupp' : ∀ z, R + ‖h‖ < ‖z‖ → (fun w => u (w + h)) z = 0 := by
    intro z hz
    refine hsupp (z + h) ?_
    have h1 : ‖z‖ ≤ ‖z + h‖ + ‖h‖ := by
      have h2 : (z + h) + (-h) = z := by ring
      calc ‖z‖ = ‖(z + h) + (-h)‖ := by rw [h2]
        _ ≤ ‖z + h‖ + ‖-h‖ := norm_add_le _ _
        _ = ‖z + h‖ + ‖h‖ := by rw [norm_neg]
    linarith
  have hlin := beurling_sub α hα hα1 (fun w => u (w + h)) u M K (R + ‖h‖) hR' hM' hM hK' hK
    hsupp' (fun z hz => hsupp z (by have hh : (0:ℝ) ≤ ‖h‖ := norm_nonneg h; linarith))
  have hkey : beurling (fun w => u (w + h) - u w)
      = fun z => beurling u (z + h) - beurling u z := by
    rw [show (fun w => u (w + h) - u w) = ((fun w => u (w + h)) - u) from rfl, hlin]
    funext z
    simp only [Pi.sub_apply]
    rw [show beurling (fun w => u (w + h)) z = beurling u (z + h) from
      congrFun (beurling_comp_add' u h) z]
  have hdq : diffQuot h u = fun w => u (w + h) - u w := rfl
  rw [hdq, hkey]
  funext z
  simp [diffQuot_apply]

/-- The `N`-th forward difference of a bounded, Hölder, compactly supported function is bounded
by `2^N M`, `α`-Hölder with constant `2^N K`, and supported in the ball of radius `R + N ‖h‖`. -/
lemma diffQuot_iterate_bounds {α M K R : ℝ} {u : ℂ → ℂ}
    (hM : ∀ z, ‖u z‖ ≤ M) (hK : ∀ x y : ℂ, ‖u x - u y‖ ≤ K * ‖x - y‖ ^ α)
    (hsupp : ∀ z, R < ‖z‖ → u z = 0) (h : ℂ) :
    ∀ N : ℕ, (∀ z, ‖((diffQuot h)^[N]) u z‖ ≤ (2:ℝ)^N * M) ∧
      (∀ x y : ℂ, ‖((diffQuot h)^[N]) u x - ((diffQuot h)^[N]) u y‖
        ≤ (2:ℝ)^N * K * ‖x - y‖ ^ α) ∧
      (∀ z, R + N * ‖h‖ < ‖z‖ → ((diffQuot h)^[N]) u z = 0) := by
  intro N
  induction N with
  | zero =>
      simp only [Function.iterate_zero, id_eq, pow_zero, one_mul, Nat.cast_zero, zero_mul,
        add_zero]
      exact ⟨hM, hK, hsupp⟩
  | succ n ih =>
      obtain ⟨ihM, ihK, ihsupp⟩ := ih
      set v : ℂ → ℂ := ((diffQuot h)^[n]) u with hv
      have hvM : ∀ z, ‖v z‖ ≤ (2:ℝ)^n * M := ihM
      have hvK : ∀ x y : ℂ, ‖v x - v y‖ ≤ (2:ℝ)^n * K * ‖x - y‖ ^ α := ihK
      have hvsupp : ∀ z, R + n * ‖h‖ < ‖z‖ → v z = 0 := ihsupp
      have hvv : ((diffQuot h)^[n+1]) u = diffQuot h v := by
        rw [Function.iterate_succ_apply']
      rw [hvv]
      have hh0 : (0:ℝ) ≤ ‖h‖ := norm_nonneg h
      constructor
      · intro z
        have h1 : ‖diffQuot h v z‖ ≤ ‖v (z + h)‖ + ‖v z‖ := by
          rw [diffQuot_apply]; exact norm_sub_le _ _
        calc ‖diffQuot h v z‖ ≤ ‖v (z + h)‖ + ‖v z‖ := h1
          _ ≤ (2:ℝ)^n * M + (2:ℝ)^n * M := add_le_add (hvM _) (hvM _)
          _ = (2:ℝ)^(n+1) * M := by ring
      constructor
      · intro x y
        have h1 : ‖diffQuot h v x - diffQuot h v y‖
            ≤ ‖v (x + h) - v (y + h)‖ + ‖v x - v y‖ := by
          rw [diffQuot_apply, diffQuot_apply]
          have hsplit : v (x + h) - v x - (v (y + h) - v y)
              = (v (x + h) - v (y + h)) - (v x - v y) := by ring
          rw [hsplit]
          exact norm_sub_le _ _
        have hx : ‖v (x + h) - v (y + h)‖ ≤ (2:ℝ)^n * K * ‖x - y‖ ^ α := by
          have h2 := hvK (x + h) (y + h)
          rwa [show x + h - (y + h) = x - y from by ring] at h2
        calc ‖diffQuot h v x - diffQuot h v y‖
            ≤ ‖v (x + h) - v (y + h)‖ + ‖v x - v y‖ := h1
          _ ≤ (2:ℝ)^n * K * ‖x - y‖ ^ α + (2:ℝ)^n * K * ‖x - y‖ ^ α :=
              add_le_add hx (hvK x y)
          _ = (2:ℝ)^(n+1) * K * ‖x - y‖ ^ α := by ring
      · intro z hz
        rw [diffQuot_apply]
        have hz' : R + (n:ℝ) * ‖h‖ < ‖z‖ := by
          have hc : (((n+1 : ℕ)):ℝ) = (n:ℝ) + 1 := by push_cast; ring
          rw [hc] at hz
          nlinarith
        have h1 : R + (n:ℝ) * ‖h‖ < ‖z + h‖ := by
          have h4 : ‖z‖ ≤ ‖z + h‖ + ‖h‖ := by
            have h5 : (z + h) + (-h) = z := by ring
            calc ‖z‖ = ‖(z + h) + (-h)‖ := by rw [h5]
              _ ≤ ‖z + h‖ + ‖-h‖ := norm_add_le _ _
              _ = ‖z + h‖ + ‖h‖ := by rw [norm_neg]
          have hc : (((n+1 : ℕ)):ℝ) = (n:ℝ) + 1 := by push_cast; ring
          rw [hc] at hz
          linarith
        rw [hvsupp (z + h) h1, hvsupp z hz', sub_zero]

/-- The iterated difference quotient commutes with the Beurling transform. -/
lemma beurling_diffQuot_iterate {α M K R : ℝ} (hα : 0 < α) (hα1 : α < 1) (hR : 0 ≤ R)
    {u : ℂ → ℂ} (hM : ∀ z, ‖u z‖ ≤ M) (hK : ∀ x y : ℂ, ‖u x - u y‖ ≤ K * ‖x - y‖ ^ α)
    (hsupp : ∀ z, R < ‖z‖ → u z = 0) (h : ℂ) :
    ∀ N : ℕ, ((diffQuot h)^[N]) (beurling u) = beurling (((diffQuot h)^[N]) u) := by
  intro N
  induction N with
  | zero => simp
  | succ n ih =>
      obtain ⟨hMn, hKn, hsuppn⟩ := diffQuot_iterate_bounds hM hK hsupp h n
      have hR' : (0:ℝ) ≤ R + n * ‖h‖ := add_nonneg hR (mul_nonneg (Nat.cast_nonneg n) (norm_nonneg h))
      have hkey := beurling_diffQuot hα hα1 hR' hMn hKn hsuppn h
      have hstep : ((diffQuot h)^[n+1]) u = diffQuot h (((diffQuot h)^[n]) u) := by
        rw [Function.iterate_succ_apply']
      calc ((diffQuot h)^[n+1]) (beurling u)
          = diffQuot h (((diffQuot h)^[n]) (beurling u)) := by
            rw [Function.iterate_succ_apply']
        _ = diffQuot h (beurling (((diffQuot h)^[n]) u)) := by rw [ih]
        _ = beurling (diffQuot h (((diffQuot h)^[n]) u)) := hkey
        _ = beurling (((diffQuot h)^[n+1]) u) := by rw [hstep]

/-- The source of the equation satisfied by the `N`-th difference quotient of `u`: the terms of
the Leibniz expansion of `Δ_h^N (μ · B u)` with `i ≥ 1`. -/
def bSource (h : ℂ) (N : ℕ) (μ f Bu : ℂ → ℂ) : ℂ → ℂ :=
  fun x => ((diffQuot h)^[N]) f x
    + ∑ i ∈ Finset.range N, ((N.choose (i+1) : ℕ) : ℂ) *
        (((diffQuot h)^[i+1]) μ x) * (((diffQuot h)^[N-(i+1)]) Bu (x + ((i+1:ℕ):ℂ) * h))

/-- The forward difference is additive. -/
lemma diffQuot_add (h : ℂ) (F G : ℂ → ℂ) :
    diffQuot h (F + G) = diffQuot h F + diffQuot h G := by
  funext x
  simp only [diffQuot_apply, Pi.add_apply]
  ring

/-- The iterated difference quotient is additive. -/
lemma iterate_diffQuot_add (h : ℂ) (N : ℕ) (F G : ℂ → ℂ) :
    ((diffQuot h)^[N]) (F + G) = ((diffQuot h)^[N]) F + ((diffQuot h)^[N]) G := by
  induction N with
  | zero => rfl
  | succ n ih =>
      have h1 : ((diffQuot h)^[n+1]) (F + G) = diffQuot h (((diffQuot h)^[n]) (F + G)) := by
        rw [Function.iterate_succ_apply']
      have h2 : ((diffQuot h)^[n+1]) F = diffQuot h (((diffQuot h)^[n]) F) := by
        rw [Function.iterate_succ_apply']
      have h3 : ((diffQuot h)^[n+1]) G = diffQuot h (((diffQuot h)^[n]) G) := by
        rw [Function.iterate_succ_apply']
      rw [h1, h2, h3, ih, diffQuot_add]

/-- The forward difference shifts along `+h`: `Δ_h^n f (y+h) = Δ_h^n f y + Δ_h^{n+1} f y`. -/
lemma diffQuot_iterate_shift (h : ℂ) (W : ℂ → ℂ) (n : ℕ) (y : ℂ) :
    (((diffQuot h)^[n]) W) (y + h) = (((diffQuot h)^[n]) W) y + (((diffQuot h)^[n+1]) W) y := by
  rw [Function.iterate_succ_apply', diffQuot_apply]; ring

/-- **Leibniz rule for iterated forward differences.** -/
theorem iterate_diffQuot_mul' (h : ℂ) (F G : ℂ → ℂ) (N : ℕ) (x : ℂ) :
    ((diffQuot h)^[N]) (F * G) x
      = ∑ i ∈ Finset.range (N + 1), ((N.choose i : ℕ) : ℂ) *
          (((diffQuot h)^[i]) F x) * (((diffQuot h)^[N - i]) G (x + (i : ℂ) * h)) := by
  suffices H : ∀ N x, ((diffQuot h)^[N]) (F * G) x
      = ∑ i ∈ Finset.range (N + 1), ((N.choose i : ℕ) : ℂ) *
          (((diffQuot h)^[i]) F x) * (((diffQuot h)^[N - i]) G (x + (i : ℂ) * h)) by
    exact H N x
  have hsummand : ∀ (N i : ℕ), i ≤ N → ∀ x : ℂ,
      ((N.choose i : ℕ):ℂ) * (((diffQuot h)^[i]) F (x+h)) * (((diffQuot h)^[N-i]) G (x+h+(i:ℂ)*h))
      - ((N.choose i : ℕ):ℂ) * (((diffQuot h)^[i]) F x) * (((diffQuot h)^[N-i]) G (x+(i:ℂ)*h))
      = ((N.choose i : ℕ):ℂ) * (((diffQuot h)^[i]) F x) * (((diffQuot h)^[N+1-i]) G (x+(i:ℂ)*h))
      + ((N.choose i : ℕ):ℂ) * (((diffQuot h)^[i+1]) F x) * (((diffQuot h)^[N-i]) G (x+((i+1:ℕ):ℂ)*h)) := by
    intro N i _ x
    rw [diffQuot_iterate_shift h F i x]
    rw [show x + h + (i:ℂ)*h = (x + (i:ℂ)*h) + h from by ring]
    rw [diffQuot_iterate_shift h G (N-i) (x + (i:ℂ)*h)]
    rw [show N - i + 1 = N + 1 - i from by omega]
    rw [show x + ((i+1:ℕ):ℂ)*h = (x + (i:ℂ)*h) + h from by push_cast; ring]
    rw [diffQuot_iterate_shift h G (N-i) (x + (i:ℂ)*h)]
    rw [show N - i + 1 = N + 1 - i from by omega]
    ring
  have hsum : ∀ N x,
      (∑ i ∈ Finset.range (N+1), ((N.choose i : ℕ):ℂ) * (((diffQuot h)^[i]) F x) * (((diffQuot h)^[N+1-i]) G (x+(i:ℂ)*h)))
    + (∑ i ∈ Finset.range (N+1), ((N.choose i : ℕ):ℂ) * (((diffQuot h)^[i+1]) F x) * (((diffQuot h)^[N-i]) G (x+((i+1:ℕ):ℂ)*h)))
    = ∑ i ∈ Finset.range (N+2), (((N+1).choose i : ℕ):ℂ) * (((diffQuot h)^[i]) F x) * (((diffQuot h)^[N+1-i]) G (x+(i:ℂ)*h)) := by
    intro N x
    rw [Finset.sum_range_succ' (fun i => ((N.choose i : ℕ):ℂ) * (((diffQuot h)^[i]) F x) * (((diffQuot h)^[N+1-i]) G (x+(i:ℂ)*h))) N]
    rw [Finset.sum_range_succ (fun i => ((N.choose i : ℕ):ℂ) * (((diffQuot h)^[i+1]) F x) * (((diffQuot h)^[N-i]) G (x+((i+1:ℕ):ℂ)*h))) N]
    rw [Finset.sum_range_succ (fun i => (((N+1).choose i : ℕ):ℂ) * (((diffQuot h)^[i]) F x) * (((diffQuot h)^[N+1-i]) G (x+(i:ℂ)*h))) (N+1)]
    rw [Finset.sum_range_succ' (fun i => (((N+1).choose i : ℕ):ℂ) * (((diffQuot h)^[i]) F x) * (((diffQuot h)^[N+1-i]) G (x+(i:ℂ)*h))) N]
    have hA : (∑ k ∈ Finset.range N, ((N.choose (k+1) : ℕ):ℂ) * (((diffQuot h)^[k+1]) F x) * (((diffQuot h)^[N+1-(k+1)]) G (x+((k+1:ℕ):ℂ)*h)))
        = ∑ k ∈ Finset.range N, ((((N+1).choose (k+1) : ℕ):ℂ) * (((diffQuot h)^[k+1]) F x) * (((diffQuot h)^[N+1-(k+1)]) G (x+((k+1:ℕ):ℂ)*h))
            - (((N.choose k : ℕ):ℂ) * (((diffQuot h)^[k+1]) F x) * (((diffQuot h)^[N-k]) G (x+((k+1:ℕ):ℂ)*h)))) := by
      apply Finset.sum_congr rfl
      intro k hk
      have _ : k < N := Finset.mem_range.mp hk
      rw [show N + 1 - (k+1) = N - k from by omega]
      rw [Nat.choose_succ_succ]
      push_cast
      ring
    rw [hA]
    rw [Finset.sum_sub_distrib]
    simp only [Nat.choose_zero_right, Nat.choose_self, Nat.cast_one, one_mul, Nat.sub_zero, Nat.sub_self]
    ring
  intro N
  induction N with
  | zero => intro x; simp
  | succ N ih =>
    intro x
    rw [Function.iterate_succ_apply', diffQuot_apply]
    rw [ih (x+h), ih x]
    rw [← Finset.sum_sub_distrib]
    trans ∑ i ∈ Finset.range (N+1), (((N.choose i : ℕ) : ℂ) * (((diffQuot h)^[i]) F x) * (((diffQuot h)^[N+1-i]) G (x+(i:ℂ)*h)) + ((N.choose i : ℕ) : ℂ) * (((diffQuot h)^[i+1]) F x) * (((diffQuot h)^[N-i]) G (x+((i+1:ℕ):ℂ)*h)))
    · apply Finset.sum_congr rfl
      intro i hi
      exact hsummand N i (by simpa using Finset.mem_range.mp hi) x
    · rw [Finset.sum_add_distrib]
      exact hsum N x

/-- **The source identity.**  If `u = f + μ · beurling u` then the `N`-th forward difference of `u`
solves the same integral equation, with source `bSource`:
`Δ_h^N u = bSource h N μ f (beurling u) + μ · beurling (Δ_h^N u)`. -/
lemma diffQuot_iterate_eq_bSource {α M K R' : ℝ} {μ f u : ℂ → ℂ} {h : ℂ} {N : ℕ}
    (hα : 0 < α) (hα1 : α < 1) (hR' : 0 ≤ R')
    (hM : ∀ z, ‖u z‖ ≤ M) (hK : ∀ x y : ℂ, ‖u x - u y‖ ≤ K * ‖x - y‖ ^ α)
    (hsupp : ∀ z, R' < ‖z‖ → u z = 0)
    (heq : ∀ z, u z = f z + μ z * beurling u z) :
    ∀ z, ((diffQuot h)^[N]) u z
      = bSource h N μ f (beurling u) z + μ z * beurling (((diffQuot h)^[N]) u) z := by
  have heq' : u = f + μ * beurling u := by funext w; rw [heq w]; rfl
  intro z
  have h1 : ((diffQuot h)^[N]) u = ((diffQuot h)^[N]) (f + μ * beurling u) :=
    congrArg (fun w => ((diffQuot h)^[N]) w) heq'
  have hadd : ((diffQuot h)^[N]) u z
      = ((diffQuot h)^[N]) f z + ((diffQuot h)^[N]) (μ * beurling u) z := by
    rw [h1, iterate_diffQuot_add]
    rfl
  have hleib := iterate_diffQuot_mul' h μ (beurling u) N z
  rw [hadd, hleib]
  simp only [bSource]
  simp_rw [beurling_diffQuot_iterate hα hα1 hR' hM hK hsupp h]
  rw [Finset.sum_range_succ']
  simp only [Function.iterate_zero, id_eq, Nat.choose_zero_right, Nat.cast_one, one_mul,
    Nat.sub_zero, Nat.cast_zero, zero_mul, add_zero]
  abel


/-! ## Auxiliary estimates for the `L²` bootstrap

The bootstrap is carried out in `L²` (rather than in a Hölder norm) because the Beurling transform
is bounded on `L²` with a constant independent of the function; this makes the equation
`Δ_h^N u = bSource h N μ f (beurling u) + μ · beurling (Δ_h^N u)` solvable by a Neumann series
whose contraction factor `δ * ‖B‖_{L²→L²}` is uniform in `N`. -/

/-- The square of the `L²` norm of `g`, written as an integral. -/
noncomputable def L2s (g : ℂ → ℂ) : ℝ := ∫ z, ‖g z‖ ^ 2 ∂volume

lemma L2s_nonneg (g : ℂ → ℂ) : 0 ≤ L2s g := integral_nonneg fun _ => by positivity

lemma integral_indicator_one_closedBall (r : ℝ) (hr : 0 ≤ r) :
    ∫ z : ℂ, (Metric.closedBall (0 : ℂ) r).indicator (fun _ => (1 : ℝ)) z ∂volume
      = Real.pi * r ^ 2 := by
  rw [integral_indicator_const (1 : ℝ) measurableSet_closedBall, smul_eq_mul, mul_one, Measure.real,
    Complex.volume_closedBall, ENNReal.toReal_mul, ENNReal.toReal_pow, ENNReal.toReal_ofReal hr,
    ENNReal.coe_toReal, NNReal.coe_real_pi]
  ring

/-- `L²`-square bound for a function bounded by `M` and vanishing outside the closed ball of
radius `r`. -/
lemma L2s_le_of_bound {g : ℂ → ℂ} {M r : ℝ} (hr : 0 ≤ r) (hM : ∀ z, ‖g z‖ ≤ M)
    (hsupp : ∀ z, r < ‖z‖ → g z = 0) : L2s g ≤ M ^ 2 * (Real.pi * r ^ 2) := by
  have hM0 : 0 ≤ M := le_trans (norm_nonneg (g 0)) (hM 0)
  set s : Set ℂ := Metric.closedBall (0 : ℂ) r with hs
  have hms : MeasurableSet s := measurableSet_closedBall
  have hne : (volume : Measure ℂ) s ≠ ⊤ := by
    rw [hs, Complex.volume_closedBall]
    exact ENNReal.mul_ne_top (ENNReal.pow_ne_top ENNReal.ofReal_ne_top) (by simp)
  have hInt : Integrable (fun z : ℂ => M ^ 2 * s.indicator (fun _ => (1 : ℝ)) z) :=
    (((integrableOn_const (C := (1 : ℝ)) hne (by simp)).integrable_indicator hms)).const_mul (M ^ 2)
  have hpt : ∀ z : ℂ, ‖g z‖ ^ 2 ≤ M ^ 2 * s.indicator (fun _ => (1 : ℝ)) z := by
    intro z
    by_cases hz : z ∈ s
    · rw [Set.indicator_of_mem hz, mul_one]
      exact pow_le_pow_left₀ (norm_nonneg (g z)) (hM z) 2
    · have hz' : r < ‖z‖ := by
        rw [hs, Metric.mem_closedBall, not_le, dist_zero_right] at hz
        exact hz
      rw [Set.indicator_of_notMem hz, mul_zero, hsupp z hz', norm_zero]
      norm_num
  calc L2s g = ∫ z : ℂ, ‖g z‖ ^ 2 ∂volume := rfl
    _ ≤ ∫ z : ℂ, M ^ 2 * s.indicator (fun _ => (1 : ℝ)) z ∂volume :=
        integral_mono_of_nonneg (Filter.Eventually.of_forall fun z => by positivity) hInt
          (Filter.Eventually.of_forall hpt)
    _ = M ^ 2 * ∫ z : ℂ, s.indicator (fun _ => (1 : ℝ)) z ∂volume := integral_const_mul _ _
    _ = M ^ 2 * (Real.pi * r ^ 2) := by rw [hs, integral_indicator_one_closedBall r hr]

lemma L2s_le_of_bound_sq {g : ℂ → ℂ} {M r : ℝ} (hr : 0 ≤ r) (hM : ∀ z, ‖g z‖ ≤ M)
    (hsupp : ∀ z, r < ‖z‖ → g z = 0) : L2s g ≤ (M * Real.sqrt Real.pi * r) ^ 2 := by
  refine le_trans (L2s_le_of_bound hr hM hsupp) (le_of_eq ?_)
  rw [mul_pow, mul_pow, Real.sq_sqrt Real.pi_pos.le]
  ring

/-- The crude pointwise bound for iterated forward differences. -/
lemma norm_iterate_diffQuot_le_two_pow {φ : ℂ → ℂ} {M : ℝ} (hM : ∀ z, ‖φ z‖ ≤ M) (N : ℕ) :
    ∀ (h x : ℂ), ‖((fun f : ℂ → ℂ => (fun x => f (x + h) - f x))^[N] φ) x‖ ≤ (2 : ℝ) ^ N * M := by
  intro h
  induction N with
  | zero => intro x; simpa using hM x
  | succ n ih =>
      intro x
      rw [Function.iterate_succ_apply']
      calc ‖_ - _‖ ≤ ‖((fun f : ℂ → ℂ => (fun x => f (x + h) - f x))^[n]) φ (x + h)‖
              + ‖((fun f : ℂ → ℂ => (fun x => f (x + h) - f x))^[n]) φ x‖ := norm_sub_le _ _
        _ ≤ (2:ℝ)^n * M + (2:ℝ)^n * M := add_le_add (ih (x+h)) (ih x)
        _ = (2:ℝ)^(n+1) * M := by ring

/-- The support of an iterated forward difference. -/
lemma iterate_diffQuot_eq_zero_of_far {φ : ℂ → ℂ} {R : ℝ} (hR : ∀ z, R < ‖z‖ → φ z = 0)
    (N : ℕ) :
    ∀ (h z : ℂ), R + N * ‖h‖ < ‖z‖ → ((fun f : ℂ → ℂ => (fun x => f (x + h) - f x))^[N] φ) z = 0 := by
  intro h
  induction N with
  | zero => intro z hz; simpa using hR z (by simpa using hz)
  | succ n ih =>
      intro z hz
      rw [Function.iterate_succ_apply']
      have hc : (((n+1 : ℕ)) : ℝ) * ‖h‖ = (n:ℝ) * ‖h‖ + ‖h‖ := by push_cast; ring
      have hz' : R + (n:ℝ) * ‖h‖ < ‖z‖ := by linarith [hz, hc, norm_nonneg h]
      have hz'' : R + (n:ℝ) * ‖h‖ < ‖z + h‖ := by
        have h4 : ‖z‖ ≤ ‖z + h‖ + ‖h‖ := by
          have h5 : (z + h) + (-h) = z := by ring
          calc ‖z‖ = ‖(z + h) + (-h)‖ := by rw [h5]
            _ ≤ ‖z + h‖ + ‖-h‖ := norm_add_le _ _
            _ = ‖z + h‖ + ‖h‖ := by rw [norm_neg]
        linarith [hz, hc, h4, norm_nonneg h]
      rw [ih (z + h) hz'', ih z hz', sub_zero]


/-- Continuity of an iterated forward difference. -/
lemma iterate_diffQuot_continuous {φ : ℂ → ℂ} (hφ : Continuous φ) (h : ℂ) (N : ℕ) :
    Continuous (((fun f : ℂ → ℂ => (fun x => f (x + h) - f x))^[N]) φ) := by
  induction N with
  | zero => simpa using hφ
  | succ n ih =>
      rw [Function.iterate_succ_apply']
      exact (ih.comp (continuous_id.add continuous_const)).sub ih

/-- The indicator of a closed ball, times a constant, is integrable. -/
lemma integrable_const_mul_indicator_closedBall (c r : ℝ) :
    Integrable (fun z : ℂ => c * (Metric.closedBall (0 : ℂ) r).indicator (fun _ => (1 : ℝ)) z) := by
  have hne : (volume : Measure ℂ) (Metric.closedBall (0 : ℂ) r) ≠ ⊤ := by
    rw [Complex.volume_closedBall]
    exact ENNReal.mul_ne_top (ENNReal.pow_ne_top ENNReal.ofReal_ne_top) (by simp)
  exact ((integrableOn_const (C := (1 : ℝ)) hne (by simp)).integrable_indicator
    measurableSet_closedBall).const_mul c

/-- Pointwise Cauchy–Schwarz for a sum, in the form needed for the source bound. -/
lemma norm_add_sum_sq_le {a : ℝ} {s : Finset ℕ} {b : ℕ → ℝ} :
    ‖a + ∑ i ∈ s, b i‖ ^ 2 ≤ 2 * (s.card + 1) * (‖a‖ ^ 2 + ∑ i ∈ s, ‖b i‖ ^ 2) := by
  have h1 : ‖a + ∑ i ∈ s, b i‖ ≤ ‖a‖ + ∑ i ∈ s, ‖b i‖ :=
    le_trans (norm_add_le _ _) (add_le_add le_rfl (norm_sum_le _ _))
  have h2 : (‖a‖ + ∑ i ∈ s, ‖b i‖) ^ 2 ≤ 2 * (‖a‖ ^ 2 + (∑ i ∈ s, ‖b i‖) ^ 2) := by
    nlinarith [sq_nonneg (‖a‖ - ∑ i ∈ s, ‖b i‖)]
  have h3 : (∑ i ∈ s, ‖b i‖) ^ 2 ≤ (s.card : ℝ) * ∑ i ∈ s, ‖b i‖ ^ 2 := sq_sum_le_card_mul_sum_sq
  have h4 : (0:ℝ) ≤ ∑ i ∈ s, ‖b i‖ ^ 2 := Finset.sum_nonneg fun i _ => by positivity
  have h5 : (0:ℝ) ≤ (s.card : ℝ) := Nat.cast_nonneg _
  have h6 : (2:ℝ) * (‖a‖ ^ 2 + (∑ i ∈ s, ‖b i‖) ^ 2)
      ≤ 2 * (s.card + 1) * (‖a‖ ^ 2 + ∑ i ∈ s, ‖b i‖ ^ 2) := by
    nlinarith [h3, h4, h5, sq_nonneg ‖a‖]
  calc ‖a + ∑ i ∈ s, b i‖ ^ 2 ≤ (‖a‖ + ∑ i ∈ s, ‖b i‖) ^ 2 := pow_le_pow_left₀ (norm_nonneg _) h1 2
    _ ≤ 2 * (‖a‖ ^ 2 + (∑ i ∈ s, ‖b i‖) ^ 2) := h2
    _ ≤ 2 * (s.card + 1) * (‖a‖ ^ 2 + ∑ i ∈ s, ‖b i‖ ^ 2) := h6

/-- `L²` bound for a sum from pointwise majorants. -/
lemma L2s_add_sum_le' {a A : ℂ → ℂ} {s : Finset ℕ} {b B : ℕ → ℂ → ℂ}
    (ha : ∀ z : ℂ, ‖a z‖ ≤ ‖A z‖) (hb : ∀ (i : ℕ) (z : ℂ), ‖b i z‖ ≤ ‖B i z‖)
    (hA : Integrable (fun z : ℂ => ‖A z‖ ^ 2))
    (hB : ∀ i : ℕ, Integrable (fun z : ℂ => ‖B i z‖ ^ 2)) :
    L2s (fun z => a z + ∑ i ∈ s, b i z) ≤ 2 * (s.card + 1) * (L2s A + ∑ i ∈ s, L2s (B i)) := by
  have hsum : Integrable (fun z : ℂ => ∑ i ∈ s, ‖B i z‖ ^ 2) :=
    integrable_finsetSum s fun i _ => hB i
  have hmaj : Integrable (fun z : ℂ => 2 * ((s.card : ℝ) + 1) * (‖A z‖ ^ 2 + ∑ i ∈ s, ‖B i z‖ ^ 2)) :=
    (hA.add hsum).const_mul _
  have hpt : ∀ z : ℂ, ‖a z + ∑ i ∈ s, b i z‖ ^ 2
      ≤ 2 * ((s.card : ℝ) + 1) * (‖A z‖ ^ 2 + ∑ i ∈ s, ‖B i z‖ ^ 2) := by
    intro z
    have h1 : ‖a z + ∑ i ∈ s, b i z‖ ≤ ‖A z‖ + ∑ i ∈ s, ‖B i z‖ := by
      refine le_trans (norm_add_le _ _) (add_le_add (ha z) ?_)
      exact le_trans (norm_sum_le _ _) (Finset.sum_le_sum fun i _ => hb i z)
    have h2 : ‖a z + ∑ i ∈ s, b i z‖ ^ 2
        ≤ (‖A z‖ + ∑ i ∈ s, ‖B i z‖) ^ 2 := pow_le_pow_left₀ (norm_nonneg _) h1 2
    have h3 : (‖A z‖ + ∑ i ∈ s, ‖B i z‖) ^ 2
        ≤ 2 * ((s.card : ℝ) + 1) * (‖A z‖ ^ 2 + ∑ i ∈ s, ‖B i z‖ ^ 2) := by
      have hsum0 : (0:ℝ) ≤ ∑ i ∈ s, ‖B i z‖ := Finset.sum_nonneg fun i _ => norm_nonneg _
      have h4 := norm_add_sum_sq_le (a := ‖A z‖) (s := s) (b := fun i => ‖B i z‖)
      rw [Real.norm_of_nonneg (add_nonneg (norm_nonneg _) hsum0)] at h4
      simp only [Real.norm_eq_abs, abs_of_nonneg (norm_nonneg _)] at h4
      exact h4
    linarith [h2, h3]
  have h2 := integral_mono_of_nonneg (Filter.Eventually.of_forall fun z => by positivity) hmaj
    (Filter.Eventually.of_forall hpt)
  have h3 : ∫ z : ℂ, 2 * ((s.card : ℝ) + 1) * (‖A z‖ ^ 2 + ∑ i ∈ s, ‖B i z‖ ^ 2) ∂volume
      = 2 * ((s.card : ℝ) + 1) * (L2s A + ∑ i ∈ s, L2s (B i)) := by
    rw [integral_const_mul, integral_add hA hsum, integral_finsetSum s (fun i _ => hB i)]
    rfl
  rw [h3] at h2
  exact h2

/-- **The `L²` bootstrap for the iterated differences of the fixed point.**  Under the hypotheses of
`smooth_of_beurling_fixed` (with the `L²` bound for the Beurling transform supplied as `hB` and the
mean-value bound for iterated differences as `hF`), the iterated forward differences of `u` satisfy
the sharp bound `‖Δ_h^N u‖_{L²} ≤ D N * ‖h‖^N`.

The proof is the induction described in the module header: the source identity
`Δ_h^N u = bSource h N μ f (beurling u) + μ · beurling (Δ_h^N u)` shows that `Δ_h^N u` is the fixed
point of the contraction `v ↦ S + μ·B v` with contraction factor `2 δ² CB² ≤ 1/2`, so
`L2s (Δ_h^N u) ≤ 4 · L2s (bSource ...)`; and the source is `O(|h|^N)` in `L²` because `Δ^{i+1}μ` is
`O(|h|^{i+1})`, `Δ_h^{N-i-1} (B u)` is `O(|h|^{N-i-1})` by the induction hypothesis, and `Δ_h^N f`
is `O(|h|^N)`. -/
theorem exists_L2s_iterate_diffQuot_le
    {α R K R' Rf CB δ : ℝ} {μ f u : ℂ → ℂ} {Bf Bm : ℕ → ℝ}
    (hα : 0 < α) (hα1 : α < 1) (hR : 0 ≤ R) (hRf : 0 ≤ Rf) (hR' : 0 ≤ R')
    (hδCB : 2 * δ ^ 2 * CB ^ 2 ≤ 1 / 2) (hCB : 0 ≤ CB)
    (hBf : ∀ (M : ℕ) (z : ℂ), ‖iteratedFDeriv ℝ M f z‖ ≤ Bf M)
    (hBm : ∀ (M : ℕ) (z : ℂ), ‖iteratedFDeriv ℝ M μ z‖ ≤ Bm M)
    (hRfsupp : ∀ z : ℂ, Rf < ‖z‖ → f z = 0)
    (hμ : ContDiff ℝ ∞ μ) (hμb : ∀ z, ‖μ z‖ ≤ δ)
    (hf : ContDiff ℝ ∞ f) (hfb : ∀ z, ‖f z‖ ≤ R)
    (hu : Continuous u) (hub : ∀ z, ‖u z‖ ≤ R)
    (hK : ∀ x y : ℂ, ‖u x - u y‖ ≤ K * ‖x - y‖ ^ α)
    (hsupp : ∀ z, R' < ‖z‖ → u z = 0)
    (heq : ∀ z, u z = f z + μ z * beurling u z)
    (hB : ∀ {g : ℂ → ℂ} {M K' r : ℝ}, Continuous g → (∀ z, ‖g z‖ ≤ M) →
        (∀ x y : ℂ, ‖g x - g y‖ ≤ K' * ‖x - y‖ ^ α) → (∀ z, r < ‖z‖ → g z = 0) →
        MemLp (beurling g) 2 volume ∧ L2s (beurling g) ≤ CB ^ 2 * L2s g)
    (hF : ∀ {N : ℕ} {φ : ℂ → ℂ} {B : ℝ}, ContDiff ℝ N φ → (∀ x, ‖iteratedFDeriv ℝ N φ x‖ ≤ B) →
        ∀ h x, ‖((fun f : ℂ → ℂ => (fun x => f (x + h) - f x))^[N] φ) x‖ ≤ ‖h‖ ^ N * B) :
    ∃ D : ℕ → ℝ, ∀ (N : ℕ) (h : ℂ),
      L2s (((fun f : ℂ → ℂ => (fun x => f (x + h) - f x))^[N]) u) ≤ (D N * ‖h‖ ^ N) ^ 2 := by
  classical
  have key : ∀ N : ℕ, ∃ D : ℝ, 0 ≤ D ∧ ∀ h : ℂ,
      L2s (((fun f : ℂ → ℂ => (fun x => f (x + h) - f x))^[N]) u) ≤ (D * ‖h‖ ^ N) ^ 2 := by
    intro N
    induction N using Nat.strong_induction_on with
    | _ N ih =>
      rcases Nat.eq_zero_or_pos N with hN0 | hNpos
      · subst hN0
        refine ⟨Real.sqrt (L2s u) + 1, by positivity, ?_⟩
        intro h
        simp only [Function.iterate_zero, id_eq, pow_zero, mul_one]
        have h2 := Real.sq_sqrt (L2s_nonneg u)
        nlinarith [Real.sqrt_nonneg (L2s u), L2s_nonneg u]
      · have hN1 : 1 ≤ N := hNpos
        -- the bounds for the earlier orders
        set D' : ℕ → ℝ := fun m => if hm : m < N then Classical.choose (ih m hm) else 0 with hD'def
        have hD'val : ∀ m (hm : m < N), D' m = Classical.choose (ih m hm) := by
          intro m hm
          rw [hD'def]
          simp only [dif_pos hm]
        have hD' : ∀ m (hm : m < N), 0 ≤ D' m ∧ ∀ h : ℂ,
            L2s (((fun f : ℂ → ℂ => (fun x => f (x + h) - f x))^[m]) u) ≤ (D' m * ‖h‖ ^ m) ^ 2 := by
          intro m hm
          rw [hD'val m hm]
          exact Classical.choose_spec (ih m hm)
        have hD'nonneg : ∀ m, 0 ≤ D' m := by
          intro m
          by_cases hm : m < N
          · rw [hD'val m hm]; exact (Classical.choose_spec (ih m hm)).1
          · rw [hD'def]; simp only [dif_neg hm]; exact le_refl 0
        -- the constant attached to the `f` term
        set Af : ℝ := Real.sqrt Real.pi * (Rf + N) * max (Bf N) ((2:ℝ)^N * R) with hAfdef
        have hBf0 : 0 ≤ Bf N := le_trans (norm_nonneg _) (hBf N 0)
        have hBm0 : ∀ M : ℕ, 0 ≤ Bm M := fun M => le_trans (norm_nonneg _) (hBm M 0)
        have hAf0 : 0 ≤ Af := by
          rw [hAfdef]
          exact mul_nonneg (mul_nonneg (Real.sqrt_nonneg _) (by positivity)) (le_max_of_le_left hBf0)
        set Ct : ℕ → ℝ := fun i => (N.choose (i+1) : ℝ) * Bm (i+1) * D' (N - (i+1)) * CB with hCtdef
        have hCt0 : ∀ i, 0 ≤ Ct i := by
          intro i
          rw [hCtdef]
          exact mul_nonneg (mul_nonneg (mul_nonneg (by positivity) (le_trans (norm_nonneg _) (hBm (i+1) 0)))
            (hD'nonneg _)) hCB
        -- the source bound
        have hsource : ∀ h : ℂ,
            L2s (bSource h N μ f (beurling u)) ≤
              (Real.sqrt (2 * ((N:ℝ) + 1)) * Real.sqrt (Af ^ 2 + ∑ i ∈ Finset.range N, (Ct i) ^ 2)
                * ‖h‖ ^ N) ^ 2 := by
          intro h
          set s : ℕ → ℂ := fun i => ((i+1:ℕ):ℂ) * h with hs
          set c : ℕ → ℝ := fun i => (N.choose (i+1) : ℝ) * Bm (i+1) * ‖h‖ ^ (i+1) with hc
          set g : ℕ → ℂ → ℂ := fun i => ((fun f : ℂ → ℂ => (fun x => f (x + h) - f x))^[N-(i+1)]) u
            with hg
          set T : ℕ → ℂ → ℂ := fun i z => (((N.choose (i+1) : ℕ) : ℂ)
            * (((fun f : ℂ → ℂ => (fun x => f (x + h) - f x))^[i+1]) μ z)
            * (((fun f : ℂ → ℂ => (fun x => f (x + h) - f x))^[N-(i+1)]) (beurling u) (z + s i)))
            with hT
          have hbSrc : bSource h N μ f (beurling u)
              = fun z => (((fun f : ℂ → ℂ => (fun x => f (x + h) - f x))^[N]) f) z
                + ∑ i ∈ Finset.range N, T i z := by
            funext z
            simp only [bSource, hT, hs]
            rfl
          have hset : ∀ i : ℕ, ∀ z : ℂ,
              T i z = ((N.choose (i+1) : ℕ) : ℂ)
                * (((fun f : ℂ → ℂ => (fun x => f (x + h) - f x))^[i+1]) μ z)
                * (((fun f : ℂ → ℂ => (fun x => f (x + h) - f x))^[N-(i+1)]) (beurling u) (z + s i)) :=
            fun i z => rfl
          have hcomm : ∀ i : ℕ, (((fun f : ℂ → ℂ => (fun x => f (x + h) - f x))^[N-(i+1)]) (beurling u))
              = beurling (g i) := by
            intro i
            rw [hg]
            exact beurling_diffQuot_iterate hα hα1 hR' hub hK hsupp h (N - (i+1))
          -- per-summand pointwise bound
          have hptB : ∀ (i : ℕ) (z : ℂ), ‖T i z‖
              ≤ ‖(c i : ℂ) * ((‖beurling (g i) (z + s i)‖ : ℝ) : ℂ)‖ := by
            intro i z
            have hTz : T i z = ((N.choose (i+1) : ℕ) : ℂ)
                * (((fun f : ℂ → ℂ => (fun x => f (x + h) - f x))^[i+1]) μ) z
                * beurling (g i) (z + s i) := by
              rw [hset i z, hcomm i]
            have hn : ‖(((N.choose (i+1) : ℕ) : ℂ))‖ = ((N.choose (i+1) : ℕ) : ℝ) := Complex.norm_natCast _
            have h2 : ‖(((fun f : ℂ → ℂ => (fun x => f (x + h) - f x))^[i+1]) μ) z‖
                ≤ Bm (i+1) * ‖h‖ ^ (i+1) := by
              have h3 := hF (hμ.of_le (by exact_mod_cast le_top)) (hBm (i+1)) h z
              rw [mul_comm] at h3
              exact h3
            have h3 : (0:ℝ) ≤ ((N.choose (i+1) : ℕ) : ℝ) := by positivity
            have h4 : ‖(c i : ℂ) * ((‖beurling (g i) (z + s i)‖ : ℝ) : ℂ)‖
                = c i * ‖beurling (g i) (z + s i)‖ := by
              rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (by rw [hc]; exact mul_nonneg (mul_nonneg (by positivity) (hBm0 (i+1))) (by positivity)),
                Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (norm_nonneg _)]
            rw [hTz, h4, hc]
            simp only []
            calc ‖(((N.choose (i+1) : ℕ) : ℂ) * (((fun f : ℂ → ℂ => (fun x => f (x + h) - f x))^[i+1]) μ) z
                  * beurling (g i) (z + s i))‖
                = ((N.choose (i+1) : ℕ) : ℝ)
                  * ‖(((fun f : ℂ → ℂ => (fun x => f (x + h) - f x))^[i+1]) μ) z‖
                  * ‖beurling (g i) (z + s i)‖ := by rw [norm_mul, norm_mul, hn]
              _ ≤ (N.choose (i+1) : ℝ) * (Bm (i+1) * ‖h‖ ^ (i+1)) * ‖beurling (g i) (z + s i)‖ :=
                  mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left h2 h3) (norm_nonneg _)
              _ = (N.choose (i+1) : ℝ) * Bm (i+1) * ‖h‖ ^ (i+1) * ‖beurling (g i) (z + s i)‖ := by
                  ring
          have hpt : ∀ z : ℂ, ‖bSource h N μ f (beurling u) z‖
              ≤ ‖(((fun f : ℂ → ℂ => (fun x => f (x + h) - f x))^[N]) f) z‖
                + ∑ i ∈ Finset.range N, ‖((c i : ℂ) * ((‖beurling (g i) (z + s i)‖ : ℝ) : ℂ))‖ := by
            intro z
            refine le_trans ?_ (add_le_add le_rfl (Finset.sum_le_sum fun i _ => hptB i z))
            rw [hbSrc]
            exact le_trans (norm_add_le _ _) (add_le_add le_rfl (norm_sum_le _ _))
          -- integrability of the majorants
          have hIntA : Integrable (fun z : ℂ =>
              ‖(((fun f : ℂ → ℂ => (fun x => f (x + h) - f x))^[N]) f) z‖ ^ 2) := by
            have hcont : Continuous (((fun f : ℂ → ℂ => (fun x => f (x + h) - f x))^[N]) f) :=
              iterate_diffQuot_continuous hf.continuous h N
            refine Integrable.mono' (integrable_const_mul_indicator_closedBall (((2:ℝ)^N * R) ^ 2) (Rf + N * ‖h‖))
              (hcont.norm.pow 2).aestronglyMeasurable (Filter.Eventually.of_forall fun z => ?_)
            rw [Real.norm_of_nonneg (by positivity)]
            by_cases hz : z ∈ Metric.closedBall (0:ℂ) (Rf + N * ‖h‖)
            · rw [Set.indicator_of_mem hz, mul_one]
              have h1 : ‖(((fun f : ℂ → ℂ => (fun x => f (x + h) - f x))^[N]) f) z‖ ≤ (2:ℝ)^N * R :=
                norm_iterate_diffQuot_le_two_pow hfb N h z
              exact pow_le_pow_left₀ (norm_nonneg _) h1 2
            · have hz' : Rf + N * ‖h‖ < ‖z‖ := by
                rw [Metric.mem_closedBall, not_le, dist_zero_right] at hz; exact hz
              rw [Set.indicator_of_notMem hz, mul_zero,
                iterate_diffQuot_eq_zero_of_far hRfsupp N h z hz', norm_zero]
              norm_num
          have hIntB : ∀ i : ℕ, Integrable (fun z : ℂ =>
              ‖((c i : ℂ) * ((‖beurling (g i) (z + s i)‖ : ℝ) : ℂ))‖ ^ 2) := by
            intro i
            have hbase : Integrable (fun z : ℂ => ‖beurling (g i) z‖ ^ 2) := by
              have hM : N - (i+1) < N := by omega
              have hgc : Continuous (g i) := by rw [hg]; exact iterate_diffQuot_continuous hu h (N-(i+1))
              have hgb : ∀ z : ℂ, ‖g i z‖ ≤ (2:ℝ)^(N-(i+1)) * R := by
                intro z; rw [hg]
                exact (diffQuot_iterate_bounds (hM := hub) (hK := hK) (hsupp := hsupp) h
                  (N - (i+1))).1 z
              have hgK : ∀ x y : ℂ, ‖g i x - g i y‖ ≤ (2:ℝ)^(N-(i+1)) * K * ‖x - y‖ ^ α := by
                intro x y; rw [hg]
                exact (diffQuot_iterate_bounds (hM := hub) (hK := hK) (hsupp := hsupp) h
                  (N - (i+1))).2.1 x y
              have hgsupp : ∀ z : ℂ, R' + ↑(N - (i+1)) * ‖h‖ < ‖z‖ → g i z = 0 := by
                intro z hz
                rw [hg]
                exact (diffQuot_iterate_bounds (hM := hub) (hK := hK) (hsupp := hsupp) h
                  (N - (i+1))).2.2 z hz
              exact (hB hgc hgb hgK hgsupp).1.norm.integrable_sq
            have h1 : Integrable (fun z : ℂ => ‖beurling (g i) (z + s i)‖ ^ 2) :=
              hbase.comp_add_right (s i)
            have hEq : ∀ z : ℂ, ‖((c i : ℂ) * ((‖beurling (g i) (z + s i)‖ : ℝ) : ℂ))‖ ^ 2
                = (c i) ^ 2 * ‖beurling (g i) (z + s i)‖ ^ 2 := by
              intro z
              rw [norm_mul, Complex.norm_real, Real.norm_eq_abs,
                abs_of_nonneg (by rw [hc]; exact mul_nonneg (mul_nonneg (by positivity) (hBm0 (i+1))) (by positivity)), Complex.norm_real, Real.norm_eq_abs,
                abs_of_nonneg (norm_nonneg _), mul_pow]
            exact (h1.const_mul ((c i) ^ 2)).congr
              (Filter.Eventually.of_forall fun z => (hEq z).symm)
          -- apply the sum estimate
          have hsum := L2s_add_sum_le'
            (s := Finset.range N)
            (a := ((fun f : ℂ → ℂ => (fun x => f (x + h) - f x))^[N]) f)
            (A := ((fun f : ℂ → ℂ => (fun x => f (x + h) - f x))^[N]) f)
            (b := T) (B := fun i z => (c i : ℂ) * ((‖beurling (g i) (z + s i)‖ : ℝ) : ℂ))
            (fun z => le_rfl) hptB hIntA hIntB
          -- bound for the `f` term
          have hfbound : L2s (((fun f : ℂ → ℂ => (fun x => f (x + h) - f x))^[N]) f)
              ≤ (Af * ‖h‖ ^ N) ^ 2 := by
            -- for `‖h‖ ≤ 1`: the mean-value bound `‖Δ_h^N f‖ ≤ ‖h‖^N * Bf N` together with the
            -- support radius `Rf + N‖h‖`; for `‖h‖ ≥ 1`: the crude bound `2^N * R`
            set P : ℂ → ℂ := ((fun f : ℂ → ℂ => (fun x => f (x + h) - f x))^[N]) f with hP
            have hPsupp : ∀ z : ℂ, Rf + N * ‖h‖ < ‖z‖ → P z = 0 := by
              intro z hz
              rw [hP]
              exact iterate_diffQuot_eq_zero_of_far hRfsupp N h z hz
            have hr0 : (0 : ℝ) ≤ Rf + N * ‖h‖ :=
              add_nonneg hRf (mul_nonneg (Nat.cast_nonneg N) (norm_nonneg h))
            have hmax0 : (0 : ℝ) ≤ max (Bf N) ((2:ℝ)^N * R) :=
              le_trans (mul_nonneg (pow_nonneg (by norm_num) N) hR) (le_max_right _ _)
            have hNN : (0 : ℝ) ≤ (N:ℝ) := Nat.cast_nonneg N
            by_cases hh : ‖h‖ ≤ 1
            · have hMv : ∀ z : ℂ, ‖P z‖ ≤ ‖h‖ ^ N * Bf N := by
                intro z
                rw [hP]
                exact hF (hf.of_le (by exact_mod_cast le_top)) (hBf N) h z
              refine le_trans (L2s_le_of_bound_sq hr0 hMv hPsupp) ?_
              rw [hAfdef]
              have hRd : Rf + N * ‖h‖ ≤ Rf + N := by
                have h1 : (N:ℝ) * ‖h‖ ≤ (N:ℝ) * 1 := mul_le_mul_of_nonneg_left hh hNN
                linarith
              have hkey1 : Bf N * (Rf + N * ‖h‖)
                  ≤ max (Bf N) ((2:ℝ)^N * R) * (Rf + N) :=
                mul_le_mul (le_max_left _ _) hRd hr0 hmax0
              have hXY : ‖h‖ ^ N * Bf N * Real.sqrt Real.pi * (Rf + N * ‖h‖)
                  ≤ Real.sqrt Real.pi * (Rf + N) * max (Bf N) ((2:ℝ)^N * R) * ‖h‖ ^ N := by
                calc ‖h‖ ^ N * Bf N * Real.sqrt Real.pi * (Rf + N * ‖h‖)
                    = Real.sqrt Real.pi * (‖h‖ ^ N * (Bf N * (Rf + N * ‖h‖))) := by ring
                  _ ≤ Real.sqrt Real.pi
                        * (‖h‖ ^ N * (max (Bf N) ((2:ℝ)^N * R) * (Rf + N))) :=
                      mul_le_mul_of_nonneg_left
                        (mul_le_mul_of_nonneg_left hkey1 (pow_nonneg (norm_nonneg h) N))
                        (Real.sqrt_nonneg _)
                  _ = Real.sqrt Real.pi * (Rf + N) * max (Bf N) ((2:ℝ)^N * R) * ‖h‖ ^ N := by
                      ring
              exact pow_le_pow_left₀
                (mul_nonneg (mul_nonneg (mul_nonneg (pow_nonneg (norm_nonneg h) N) hBf0)
                  (Real.sqrt_nonneg _)) hr0) hXY 2
            · have h1h : (1 : ℝ) ≤ ‖h‖ := le_of_lt (not_le.mp hh)
              have hMv : ∀ z : ℂ, ‖P z‖ ≤ (2:ℝ)^N * R := by
                intro z
                rw [hP]
                exact norm_iterate_diffQuot_le_two_pow hfb N h z
              refine le_trans (L2s_le_of_bound_sq hr0 hMv hPsupp) ?_
              rw [hAfdef]
              have hpow1 : (1 : ℝ) ≤ ‖h‖ ^ N := one_le_pow₀ h1h
              have hhN : ‖h‖ ≤ ‖h‖ ^ N := by
                have h1 := pow_le_pow_right₀ h1h hN1
                simpa using h1
              have hRd : Rf + N * ‖h‖ ≤ (Rf + N) * ‖h‖ ^ N := by
                have h1 : Rf ≤ Rf * ‖h‖ ^ N := by
                  simpa using mul_le_mul_of_nonneg_left hpow1 hRf
                have h2 : (N:ℝ) * ‖h‖ ≤ (N:ℝ) * ‖h‖ ^ N :=
                  mul_le_mul_of_nonneg_left hhN hNN
                calc Rf + N * ‖h‖ ≤ Rf * ‖h‖ ^ N + (N:ℝ) * ‖h‖ ^ N := add_le_add h1 h2
                  _ = (Rf + N) * ‖h‖ ^ N := by ring
              have hkey1 : (2:ℝ)^N * R * (Rf + N * ‖h‖)
                  ≤ max (Bf N) ((2:ℝ)^N * R) * (Rf + N) * ‖h‖ ^ N := by
                have h1 := mul_le_mul (le_max_right (Bf N) ((2:ℝ)^N * R)) hRd hr0 hmax0
                calc (2:ℝ)^N * R * (Rf + N * ‖h‖)
                    ≤ max (Bf N) ((2:ℝ)^N * R) * ((Rf + N) * ‖h‖ ^ N) := h1
                  _ = max (Bf N) ((2:ℝ)^N * R) * (Rf + N) * ‖h‖ ^ N := by ring
              have hXY : (2:ℝ)^N * R * Real.sqrt Real.pi * (Rf + N * ‖h‖)
                  ≤ Real.sqrt Real.pi * (Rf + N) * max (Bf N) ((2:ℝ)^N * R) * ‖h‖ ^ N := by
                calc (2:ℝ)^N * R * Real.sqrt Real.pi * (Rf + N * ‖h‖)
                    = Real.sqrt Real.pi * ((2:ℝ)^N * R * (Rf + N * ‖h‖)) := by ring
                  _ ≤ Real.sqrt Real.pi
                        * (max (Bf N) ((2:ℝ)^N * R) * (Rf + N) * ‖h‖ ^ N) :=
                      mul_le_mul_of_nonneg_left hkey1 (Real.sqrt_nonneg _)
                  _ = Real.sqrt Real.pi * (Rf + N) * max (Bf N) ((2:ℝ)^N * R) * ‖h‖ ^ N := by
                      ring
              exact pow_le_pow_left₀
                (mul_nonneg (mul_nonneg (mul_nonneg (pow_nonneg (by norm_num) N) hR)
                  (Real.sqrt_nonneg _)) hr0) hXY 2
          -- bounds for the summands
          have hBbound : ∀ (i : ℕ), i < N →
              L2s (fun z : ℂ => (c i : ℂ) * ((‖beurling (g i) (z + s i)‖ : ℝ) : ℂ))
              ≤ (Ct i * ‖h‖ ^ N) ^ 2 := by
            intro i hi
            have hM : N - (i+1) < N := by omega
            have hgc : Continuous (g i) := by rw [hg]; exact iterate_diffQuot_continuous hu h (N-(i+1))
            have hgb : ∀ z : ℂ, ‖g i z‖ ≤ (2:ℝ)^(N-(i+1)) * R := by
              intro z; rw [hg]
              exact (diffQuot_iterate_bounds (hM := hub) (hK := hK) (hsupp := hsupp) h
                (N - (i+1))).1 z
            have hgK : ∀ x y : ℂ, ‖g i x - g i y‖ ≤ (2:ℝ)^(N-(i+1)) * K * ‖x - y‖ ^ α := by
              intro x y; rw [hg]
              exact (diffQuot_iterate_bounds (hM := hub) (hK := hK) (hsupp := hsupp) h
                (N - (i+1))).2.1 x y
            have hgsupp : ∀ z : ℂ, R' + (N-(i+1)) * ‖h‖ < ‖z‖ → g i z = 0 := by
              intro z hz
              have hz' : R' + ↑(N - (i+1)) * ‖h‖ < ‖z‖ := by
                have hc' : (↑(N - (i+1)) : ℝ) = ↑N - (↑i + 1) := by
                  rw [Nat.cast_sub (by omega : i + 1 ≤ N)]; push_cast; ring
                rw [hc']; exact hz
              rw [hg]
              exact (diffQuot_iterate_bounds (hM := hub) (hK := hK) (hsupp := hsupp) h
                (N - (i+1))).2.2 z hz'
            have hBu := hB hgc hgb hgK hgsupp
            have hshift : L2s (fun z : ℂ => (c i : ℂ) * ((‖beurling (g i) (z + s i)‖ : ℝ) : ℂ))
                = (c i) ^ 2 * L2s (beurling (g i)) := by
              have hEq : ∀ z : ℂ, ‖(c i : ℂ) * ((‖beurling (g i) (z + s i)‖ : ℝ) : ℂ)‖ ^ 2
                  = (c i) ^ 2 * ‖beurling (g i) (z + s i)‖ ^ 2 := by
                intro z
                rw [norm_mul, Complex.norm_real, Real.norm_eq_abs,
                  abs_of_nonneg (by rw [hc]; exact mul_nonneg (mul_nonneg (by positivity) (hBm0 (i+1))) (by positivity)), Complex.norm_real, Real.norm_eq_abs,
                  abs_of_nonneg (norm_nonneg _), mul_pow]
              rw [L2s, L2s, show (∫ z : ℂ, ‖(c i : ℂ) * ((‖beurling (g i) (z + s i)‖ : ℝ) : ℂ)‖ ^ 2)
                    = ∫ z : ℂ, (c i) ^ 2 * ‖beurling (g i) (z + s i)‖ ^ 2 from by
                  apply integral_congr_ae
                  filter_upwards with z
                  exact hEq z]
              rw [integral_const_mul]
              congr 1
              exact integral_add_right_eq_self (μ := (volume : Measure ℂ))
                (fun z : ℂ => ‖beurling (g i) z‖ ^ 2) (s i)
            have hdiff : L2s (beurling (g i)) ≤ (CB * (D' (N - (i+1)) * ‖h‖ ^ (N-(i+1)))) ^ 2 := by
              refine le_trans hBu.2 ?_
              have h1 := (hD' (N - (i+1)) hM).2 h
              nlinarith [h1, hCB, hD'nonneg (N - (i+1)), L2s_nonneg (g i)]
            have hci : c i = (N.choose (i+1) : ℝ) * Bm (i+1) * ‖h‖ ^ (i+1) := rfl
            have hpow : ‖h‖ ^ (i+1) * ‖h‖ ^ (N-(i+1)) = ‖h‖ ^ N := by
              rw [← pow_add]; congr 1; omega
            calc L2s (fun z : ℂ => (c i : ℂ) * ((‖beurling (g i) (z + s i)‖ : ℝ) : ℂ))
                = (c i) ^ 2 * L2s (beurling (g i)) := hshift
              _ ≤ (c i) ^ 2 * (CB * (D' (N - (i+1)) * ‖h‖ ^ (N-(i+1)))) ^ 2 :=
                  mul_le_mul_of_nonneg_left hdiff (by positivity)
              _ = (((N.choose (i+1) : ℕ) : ℝ) * Bm (i+1) * D' (N - (i+1)) * CB * ‖h‖ ^ N) ^ 2 := by
                  -- combine `‖h‖^(i+1) * ‖h‖^(N-(i+1)) = ‖h‖^N` with `c i = C(N,i+1) Bm (i+1) ‖h‖^(i+1)`
                  rw [hci]
                  have h2 : (‖h‖ ^ (i+1)) ^ 2 * (‖h‖ ^ (N - (i+1))) ^ 2 = (‖h‖ ^ N) ^ 2 := by
                    rw [← mul_pow, hpow]
                  rw [show ((N.choose (i+1) : ℝ) * Bm (i+1) * ‖h‖ ^ (i+1)) ^ 2
                        * (CB * (D' (N - (i+1)) * ‖h‖ ^ (N - (i+1)))) ^ 2
                      = ((N.choose (i+1) : ℝ) * Bm (i+1) * D' (N - (i+1)) * CB) ^ 2
                        * ((‖h‖ ^ (i+1)) ^ 2 * (‖h‖ ^ (N - (i+1))) ^ 2) from by ring]
                  rw [h2]
                  ring
          -- assemble
          have hfeq : L2s (bSource h N μ f (beurling u))
              = L2s (fun z => (((fun f : ℂ → ℂ => (fun x => f (x + h) - f x))^[N]) f) z
                  + ∑ i ∈ Finset.range N, T i z) := by rw [hbSrc]
          have hsum' : L2s (fun z => (((fun f : ℂ → ℂ => (fun x => f (x + h) - f x))^[N]) f) z
                  + ∑ i ∈ Finset.range N, T i z)
              ≤ 2 * (((Finset.range N).card : ℝ) + 1)
                * (L2s (((fun f : ℂ → ℂ => (fun x => f (x + h) - f x))^[N]) f)
                  + ∑ i ∈ Finset.range N,
                      L2s (fun z : ℂ => (c i : ℂ) * ((‖beurling (g i) (z + s i)‖ : ℝ) : ℂ))) := hsum
          have hcard : 2 * (((Finset.range N).card : ℝ) + 1) = 2 * ((N:ℝ) + 1) := by simp
          rw [hcard] at hsum'
          have h4 : ∑ i ∈ Finset.range N,
                L2s (fun z : ℂ => (c i : ℂ) * ((‖beurling (g i) (z + s i)‖ : ℝ) : ℂ))
              ≤ ∑ i ∈ Finset.range N, (Ct i * ‖h‖ ^ N) ^ 2 :=
            Finset.sum_le_sum fun i hi => hBbound i (Finset.mem_range.mp hi)
          have h5 : L2s (bSource h N μ f (beurling u))
              ≤ 2 * ((N:ℝ) + 1) * ((Af * ‖h‖ ^ N) ^ 2 + ∑ i ∈ Finset.range N, (Ct i * ‖h‖ ^ N) ^ 2) := by
            rw [hfeq]
            refine le_trans hsum' ?_
            refine mul_le_mul_of_nonneg_left (add_le_add hfbound h4) (by positivity)
          have h6 : 2 * ((N:ℝ) + 1) * ((Af * ‖h‖ ^ N) ^ 2 + ∑ i ∈ Finset.range N, (Ct i * ‖h‖ ^ N) ^ 2)
              = (Real.sqrt (2 * ((N:ℝ) + 1)) * Real.sqrt (Af ^ 2 + ∑ i ∈ Finset.range N, (Ct i) ^ 2)
                  * ‖h‖ ^ N) ^ 2 := by
            have h7 : ∑ i ∈ Finset.range N, (Ct i * ‖h‖ ^ N) ^ 2
                = (∑ i ∈ Finset.range N, (Ct i) ^ 2) * (‖h‖ ^ N) ^ 2 := by
              rw [Finset.sum_mul]
              exact Finset.sum_congr rfl fun i _ => by ring
            have h8 : (Af * ‖h‖ ^ N) ^ 2 = Af ^ 2 * (‖h‖ ^ N) ^ 2 := by ring
            have h9 : (0:ℝ) ≤ 2 * ((N:ℝ) + 1) := by positivity
            have h10 : (0:ℝ) ≤ Af ^ 2 + ∑ i ∈ Finset.range N, (Ct i) ^ 2 :=
              add_nonneg (by positivity) (Finset.sum_nonneg fun i _ => by positivity)
            rw [h7, h8]
            rw [show (Real.sqrt (2 * ((N:ℝ) + 1))
                * Real.sqrt (Af ^ 2 + ∑ i ∈ Finset.range N, (Ct i) ^ 2) * ‖h‖ ^ N) ^ 2
              = 2 * ((N:ℝ) + 1) * (Af ^ 2 + ∑ i ∈ Finset.range N, (Ct i) ^ 2) * (‖h‖ ^ N) ^ 2 from by
                rw [mul_pow, mul_pow, Real.sq_sqrt h9, Real.sq_sqrt h10]]
            ring
          linarith [h5, h6]
        refine ⟨2 * (Real.sqrt (2 * ((N:ℝ) + 1))
            * Real.sqrt (Af ^ 2 + ∑ i ∈ Finset.range N, (Ct i) ^ 2)),
          by positivity, fun h => ?_⟩
        have hcontr : L2s (((fun f : ℂ → ℂ => (fun x => f (x + h) - f x))^[N]) u)
            ≤ 2 * L2s (bSource h N μ f (beurling u))
              + 2 * δ ^ 2 * CB ^ 2 * L2s (((fun f : ℂ → ℂ => (fun x => f (x + h) - f x))^[N]) u) := by
          set X : ℂ → ℂ := ((fun f : ℂ → ℂ => (fun x => f (x + h) - f x))^[N]) u with hX
          set S : ℂ → ℂ := bSource h N μ f (beurling u) with hS
          set BX : ℂ → ℂ := beurling X with hBX
          have hpt : ∀ z : ℂ, X z = S z + μ z * BX z := by
            intro z
            rw [hX, hS, hBX]
            exact diffQuot_iterate_eq_bSource hα hα1 hR' hub hK hsupp heq z
          have hδ0 : 0 ≤ δ := le_trans (norm_nonneg _) (hμb 0)
          -- the class hypotheses for `X`
          have hXbounds := diffQuot_iterate_bounds (hM := hub) (hK := hK) (hsupp := hsupp) h N
          have hXcont : Continuous X := by rw [hX]; exact iterate_diffQuot_continuous hu h N
          have hXb : ∀ z : ℂ, ‖X z‖ ≤ (2:ℝ)^N * R := by rw [hX]; exact hXbounds.1
          have hXK : ∀ x y : ℂ, ‖X x - X y‖ ≤ (2:ℝ)^N * K * ‖x - y‖ ^ α := by
            rw [hX]; exact hXbounds.2.1
          have hXsupp : ∀ z : ℂ, R' + N * ‖h‖ < ‖z‖ → X z = 0 := by
            rw [hX]; exact hXbounds.2.2
          have hBeur := hB hXcont hXb hXK hXsupp
          have hBXint : Integrable (fun z : ℂ => ‖BX z‖ ^ 2) := by
            rw [hBX]
            exact hBeur.1.norm.integrable_sq
          -- integrability of `‖X‖²`
          have hXint : Integrable (fun z : ℂ => ‖X z‖ ^ 2) := by
            set M₀ : ℝ := (2:ℝ)^N * R with hM₀
            have hM₀0 : 0 ≤ M₀ := by rw [hM₀]; positivity
            have hbound : ∀ z : ℂ, ‖‖X z‖ ^ 2‖
                ≤ M₀ ^ 2 * (Metric.closedBall (0:ℂ) (R' + N * ‖h‖)).indicator (fun _ => (1:ℝ)) z := by
              intro z
              rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
              by_cases hz : z ∈ Metric.closedBall (0:ℂ) (R' + N * ‖h‖)
              · rw [Set.indicator_of_mem hz, mul_one]
                have h1 := hXb z
                rw [hM₀]
                exact pow_le_pow_left₀ (norm_nonneg _) h1 2
              · have hz' : R' + N * ‖h‖ < ‖z‖ := by
                  rw [Metric.mem_closedBall, not_le, dist_zero_right] at hz
                  exact hz
                rw [Set.indicator_of_notMem hz, mul_zero, hXsupp z hz', norm_zero]
                simp
            refine Integrable.mono' ?_ (hXcont.norm.pow 2).aestronglyMeasurable
              (Filter.Eventually.of_forall hbound)
            exact integrable_const_mul_indicator_closedBall _ _
          -- integrability of `‖S‖²`
          have hSint : Integrable (fun z : ℂ => ‖S z‖ ^ 2) := by
            have hSeq : S = fun z : ℂ => X z - μ z * BX z := by
              funext z
              have h1 := hpt z
              rw [h1]; ring
            have hbound : ∀ z : ℂ, ‖‖S z‖ ^ 2‖ ≤ 2 * ‖X z‖ ^ 2 + 2 * δ ^ 2 * ‖BX z‖ ^ 2 := by
              intro z
              have h2 : ‖S z‖ ≤ ‖X z‖ + δ * ‖BX z‖ := by
                rw [hSeq]
                refine le_trans (norm_sub_le _ _) ?_
                exact add_le_add le_rfl (le_trans (norm_mul_le _ _)
                  (mul_le_mul_of_nonneg_right (hμb z) (norm_nonneg _)))
              have h3 : ‖S z‖ ^ 2 ≤ (‖X z‖ + δ * ‖BX z‖) ^ 2 :=
                pow_le_pow_left₀ (norm_nonneg _) h2 2
              have h4 : (‖X z‖ + δ * ‖BX z‖) ^ 2 ≤ 2 * ‖X z‖ ^ 2 + 2 * δ ^ 2 * ‖BX z‖ ^ 2 := by
                nlinarith [sq_nonneg (‖X z‖ - δ * ‖BX z‖), norm_nonneg (X z), norm_nonneg (BX z),
                  sq_nonneg (δ * ‖BX z‖)]
              rw [Real.norm_of_nonneg (by positivity)]
              linarith [h3, h4]
            have hSmeas : AEStronglyMeasurable S volume := by
              rw [hSeq]
              exact (hXcont.aemeasurable.sub (hμ.continuous.aemeasurable.mul hBeur.1.aemeasurable)).aestronglyMeasurable
            exact Integrable.mono' ((hXint.const_mul 2).add (hBXint.const_mul (2 * δ ^ 2)))
              (hSmeas.norm.pow 2) (Filter.Eventually.of_forall hbound)
          -- integrate the pointwise inequality
          have hmaj : Integrable (fun z : ℂ => 2 * ‖S z‖ ^ 2 + 2 * δ ^ 2 * ‖BX z‖ ^ 2) :=
            (hSint.const_mul 2).add (hBXint.const_mul (2 * δ ^ 2))
          have hpt2 : ∀ z : ℂ, ‖X z‖ ^ 2 ≤ 2 * ‖S z‖ ^ 2 + 2 * δ ^ 2 * ‖BX z‖ ^ 2 := by
            intro z
            have h1 : X z = S z + μ z * BX z := hpt z
            have h2 : ‖S z + μ z * BX z‖ ≤ ‖S z‖ + δ * ‖BX z‖ := by
              refine le_trans (norm_add_le _ _) ?_
              exact add_le_add le_rfl (le_trans (norm_mul_le _ _)
                (mul_le_mul_of_nonneg_right (hμb z) (norm_nonneg _)))
            rw [h1]
            have h3 : ‖S z + μ z * BX z‖ ^ 2 ≤ (‖S z‖ + δ * ‖BX z‖) ^ 2 :=
              pow_le_pow_left₀ (norm_nonneg _) h2 2
            have h4 : (‖S z‖ + δ * ‖BX z‖) ^ 2 ≤ 2 * ‖S z‖ ^ 2 + 2 * δ ^ 2 * ‖BX z‖ ^ 2 := by
              nlinarith [sq_nonneg (‖S z‖ - δ * ‖BX z‖), norm_nonneg (S z), norm_nonneg (BX z)]
            linarith [h3, h4]
          have hInt1 : L2s X ≤ 2 * L2s S + 2 * δ ^ 2 * L2s BX := by
            have h := integral_mono_of_nonneg (Filter.Eventually.of_forall fun z => by positivity)
              hmaj (Filter.Eventually.of_forall hpt2)
            have e1 : ∫ z : ℂ, (2 * ‖S z‖ ^ 2 + 2 * δ ^ 2 * ‖BX z‖ ^ 2) ∂volume
                = 2 * L2s S + 2 * δ ^ 2 * L2s BX := by
              rw [integral_add (hSint.const_mul 2) (hBXint.const_mul (2 * δ ^ 2)),
                integral_const_mul, integral_const_mul]
              rfl
            rw [e1] at h
            exact h
          have hBeur2 : L2s BX ≤ CB ^ 2 * L2s X := by rw [hBX]; exact hBeur.2
          calc L2s X ≤ 2 * L2s S + 2 * δ ^ 2 * L2s BX := hInt1
            _ ≤ 2 * L2s S + 2 * δ ^ 2 * (CB ^ 2 * L2s X) := by
                have := L2s_nonneg X
                nlinarith [hBeur2, L2s_nonneg BX, L2s_nonneg X, L2s_nonneg S, hδ0]
            _ = 2 * L2s S + 2 * δ ^ 2 * CB ^ 2 * L2s X := by ring
        have hS0 : 0 ≤ L2s (bSource h N μ f (beurling u)) := L2s_nonneg _
        have hU0 : 0 ≤ L2s (((fun f : ℂ → ℂ => (fun x => f (x + h) - f x))^[N]) u) := L2s_nonneg _
        have hmain : L2s (((fun f : ℂ → ℂ => (fun x => f (x + h) - f x))^[N]) u)
            ≤ 4 * L2s (bSource h N μ f (beurling u)) := by nlinarith [hcontr, hδCB, hS0, hU0]
        have hsrc := hsource h
        have hfin : L2s (((fun f : ℂ → ℂ => (fun x => f (x + h) - f x))^[N]) u)
            ≤ (2 * (Real.sqrt (2 * ((N:ℝ) + 1))
                * Real.sqrt (Af ^ 2 + ∑ i ∈ Finset.range N, (Ct i) ^ 2) * ‖h‖ ^ N)) ^ 2 := by
          have hs2 : (Real.sqrt (2 * ((N:ℝ) + 1))) ^ 2 = 2 * ((N:ℝ) + 1) :=
            Real.sq_sqrt (by positivity)
          nlinarith [hmain, hsrc, hs2]
        simpa only [mul_assoc] using hfin
  choose D hD using key
  exact ⟨D, fun N h => (hD N).2 h⟩

/-! ### `L²` plumbing: `L2s` versus `eLpNorm` -/

/-- `‖z‖ₑ ^ (2 : ℝ)` is the `ENNReal.ofReal` of the square of `‖z‖`. -/
lemma enorm_rpow_two_eq_ofReal (z : ℂ) : ‖z‖ₑ ^ (2:ℝ) = ENNReal.ofReal (‖z‖ ^ 2) := by
  rw [enorm_eq_nnnorm, ← ENNReal.coe_rpow_of_nonneg ‖z‖₊ (by norm_num), NNReal.rpow_two,
    ENNReal.coe_pow, ENNReal.ofReal_pow (norm_nonneg z) 2,
    ← ENNReal.ofReal_coe_nnreal (p := ‖z‖₊), coe_nnnorm]

/-- The `L²` seminorm of a complex-valued function as an `ENNReal` integral. -/
lemma eLpNorm_two_eq_lintegral {g : ℂ → ℂ} (hg : AEStronglyMeasurable g volume) :
    eLpNorm g 2 volume = (∫⁻ z : ℂ, ENNReal.ofReal (‖g z‖ ^ 2) ∂volume) ^ (1/2 : ℝ) := by
  rw [eLpNorm_eq_lintegral_rpow_enorm (by norm_num) (by norm_num) hg]
  simp only [ENNReal.toReal_ofNat]
  congr 1
  exact lintegral_congr fun z => enorm_rpow_two_eq_ofReal (g z)

/-- `L2s g` is the square of the real-valued `L²` norm of `g`. -/
lemma L2s_eq_toReal_eLpNorm_sq {g : ℂ → ℂ} (hg : AEStronglyMeasurable g volume) :
    L2s g = (ENNReal.toReal (eLpNorm g 2 volume)) ^ 2 := by
  set X : ENNReal := ∫⁻ z : ℂ, ENNReal.ofReal (‖g z‖ ^ 2) ∂volume with hX
  have h1 : L2s g = X.toReal :=
    integral_eq_lintegral_of_nonneg_ae (Filter.Eventually.of_forall fun z => by positivity)
      (hg.norm.pow 2)
  have hX0 : 0 ≤ X.toReal := ENNReal.toReal_nonneg
  calc L2s g = X.toReal := h1
    _ = (X.toReal ^ (1/2:ℝ)) ^ 2 := by
        rw [← Real.sqrt_eq_rpow]
        exact (Real.sq_sqrt hX0).symm
    _ = (ENNReal.toReal (eLpNorm g 2 volume)) ^ 2 := by
        rw [eLpNorm_two_eq_lintegral hg, ENNReal.toReal_rpow]

/-- The `L²` bound `L2s g ≤ c ^ 2` upgrades to the `eLpNorm` bound, for an `L²` function. -/
lemma eLpNorm_two_le_of_L2s {g : ℂ → ℂ} (hg : MemLp g 2 volume) {c : ℝ} (hc : 0 ≤ c)
    (h : L2s g ≤ c ^ 2) : eLpNorm g 2 volume ≤ ENNReal.ofReal c := by
  set X : ENNReal := ∫⁻ z : ℂ, ENNReal.ofReal (‖g z‖ ^ 2) ∂volume with hX
  have h1 : L2s g = X.toReal :=
    integral_eq_lintegral_of_nonneg_ae (Filter.Eventually.of_forall fun z => by positivity)
      (hg.aestronglyMeasurable.norm.pow 2)
  have hXtop : X ≠ ⊤ := by
    have h3 : eLpNorm g 2 volume < ⊤ := hg
    rw [eLpNorm_two_eq_lintegral hg.aestronglyMeasurable] at h3
    rw [← hX] at h3
    by_contra hc'
    rw [hc'] at h3
    rw [ENNReal.top_rpow_of_pos (by norm_num : (0:ℝ) < 1/2)] at h3
    exact lt_irrefl _ h3
  have hXle : X ≤ ENNReal.ofReal (c ^ 2) := by
    rw [← ENNReal.ofReal_toReal hXtop]
    refine ENNReal.ofReal_le_ofReal ?_
    rw [h1] at h
    exact h
  calc eLpNorm g 2 volume = X ^ (1/2:ℝ) := eLpNorm_two_eq_lintegral hg.aestronglyMeasurable
    _ ≤ (ENNReal.ofReal (c ^ 2)) ^ (1/2:ℝ) := ENNReal.rpow_le_rpow hXle (by norm_num)
    _ = ENNReal.ofReal c := by
        rw [ENNReal.ofReal_rpow_of_nonneg (by positivity) (by norm_num)]
        congr 1
        rw [← Real.sqrt_eq_rpow, Real.sqrt_sq hc]

/-- An `eLpNorm` bound transfers to the squared integral `L2s`. -/
lemma L2s_le_of_eLpNorm_le {g g' : ℂ → ℂ} (hg : MemLp g 2 volume) (hg' : MemLp g' 2 volume)
    {C : ℝ} (hC : 0 ≤ C) (h : eLpNorm g' 2 volume ≤ ENNReal.ofReal C * eLpNorm g 2 volume) :
    L2s g' ≤ C ^ 2 * L2s g := by
  rw [L2s_eq_toReal_eLpNorm_sq hg'.aestronglyMeasurable,
    L2s_eq_toReal_eLpNorm_sq hg.aestronglyMeasurable]
  have h1 : ENNReal.toReal (eLpNorm g' 2 volume)
      ≤ ENNReal.toReal (ENNReal.ofReal C * eLpNorm g 2 volume) :=
    ENNReal.toReal_mono (ENNReal.mul_ne_top ENNReal.ofReal_ne_top (ne_of_lt hg)) h
  rw [ENNReal.toReal_mul, ENNReal.toReal_ofReal hC] at h1
  have h2 : (ENNReal.toReal (eLpNorm g' 2 volume)) ^ 2
      ≤ (C * ENNReal.toReal (eLpNorm g 2 volume)) ^ 2 :=
    pow_le_pow_left₀ ENNReal.toReal_nonneg h1 2
  rwa [mul_pow] at h2

/-- A bounded function vanishing outside a ball is in `L²`. -/
lemma memLp_two_of_bound_support {g : ℂ → ℂ} (hga : AEStronglyMeasurable g volume)
    {M r : ℝ} (hr : 0 ≤ r) (hM : ∀ z, ‖g z‖ ≤ M) (hsupp : ∀ z, r < ‖z‖ → g z = 0) :
    MemLp g 2 volume := by
  have hM0 : 0 ≤ M := le_trans (norm_nonneg (g 0)) (hM 0)
  set s : Set ℂ := Metric.closedBall (0:ℂ) r with hs
  have hpt : ∀ z : ℂ, ENNReal.ofReal (‖g z‖ ^ 2)
      ≤ ENNReal.ofReal (M ^ 2) * s.indicator (fun _ => (1:ENNReal)) z := by
    intro z
    by_cases hz : z ∈ s
    · rw [Set.indicator_of_mem hz, mul_one]
      exact ENNReal.ofReal_le_ofReal (pow_le_pow_left₀ (norm_nonneg _) (hM z) 2)
    · have hz' : r < ‖z‖ := by
        rw [hs, Metric.mem_closedBall, not_le, dist_zero_right] at hz; exact hz
      rw [Set.indicator_of_notMem hz, mul_zero, hsupp z hz', norm_zero]
      simp
  have hX : (∫⁻ z : ℂ, ENNReal.ofReal (‖g z‖ ^ 2) ∂volume)
      ≤ ENNReal.ofReal (M ^ 2 * (Real.pi * r ^ 2)) := by
    refine le_trans (lintegral_mono hpt) ?_
    rw [lintegral_const_mul _ (measurable_const.indicator measurableSet_closedBall),
      lintegral_indicator_const measurableSet_closedBall, one_mul]
    rw [Complex.volume_closedBall, ENNReal.ofReal_mul (by positivity : (0:ℝ) ≤ M^2),
      ENNReal.ofReal_mul (by positivity : (0:ℝ) ≤ Real.pi), ← ENNReal.ofReal_pow hr,
      ← ENNReal.ofReal_coe_nnreal (p := NNReal.pi), NNReal.coe_real_pi]
    rw [mul_comm (ENNReal.ofReal (r ^ 2)) (ENNReal.ofReal Real.pi)]
  calc eLpNorm g 2 volume
      = (∫⁻ z : ℂ, ENNReal.ofReal (‖g z‖ ^ 2) ∂volume) ^ (1/2:ℝ) :=
        eLpNorm_two_eq_lintegral hga
    _ ≤ (ENNReal.ofReal (M ^ 2 * (Real.pi * r ^ 2))) ^ (1/2:ℝ) :=
        ENNReal.rpow_le_rpow hX (by norm_num)
    _ = ENNReal.ofReal ((M ^ 2 * (Real.pi * r ^ 2)) ^ (1/2:ℝ)) :=
        ENNReal.ofReal_rpow_of_nonneg (by positivity) (by norm_num)
    _ < ⊤ := ENNReal.ofReal_lt_top

/-! ### Elementary consequences of the standing hypotheses -/

/-- A global `α`-Hölder bound with `α > 0` gives continuity. -/
lemma continuous_of_holder_bound {u : ℂ → ℂ} {α K : ℝ} (hα : 0 < α)
    (h : ∀ x y : ℂ, ‖u x - u y‖ ≤ K * ‖x - y‖ ^ α) : Continuous u := by
  rw [continuous_iff_continuousAt]
  intro x
  rw [ContinuousAt, tendsto_iff_norm_sub_tendsto_zero]
  set K' : ℝ := max K 0 with hK'
  have hbound : ∀ y : ℂ, ‖u y - u x‖ ≤ K' * ‖y - x‖ ^ α := by
    intro y
    have h2 : ‖u y - u x‖ ≤ K * ‖y - x‖ ^ α := h y x
    have h1 : K * ‖y - x‖ ^ α ≤ K' * ‖y - x‖ ^ α :=
      mul_le_mul_of_nonneg_right (le_max_left K 0) (Real.rpow_nonneg (norm_nonneg _) α)
    linarith
  have hg : Tendsto (fun y : ℂ => K' * ‖y - x‖ ^ α) (𝓝 x) (𝓝 0) := by
    have h1 : Tendsto (fun y : ℂ => ‖y - x‖) (𝓝 x) (𝓝 0) := by
      have h2 : Tendsto (fun y : ℂ => y - x) (𝓝 x) (𝓝 ((0:ℂ))) := by
        have h3 : Tendsto (fun y : ℂ => y - x) (𝓝 x) (𝓝 (x - x)) :=
          tendsto_id.sub tendsto_const_nhds
        simpa using h3
      simpa using h2.norm
    have h2 : Tendsto (fun y : ℂ => ‖y - x‖ ^ α) (𝓝 x) (𝓝 0) := by
      have h3 : Tendsto (fun y : ℂ => ‖y - x‖ ^ α) (𝓝 x) (𝓝 ((0:ℝ) ^ α)) :=
        ((Real.continuous_rpow_const hα.le).tendsto 0).comp h1
      rwa [Real.zero_rpow hα.ne'] at h3
    simpa using h2.const_mul K'
  exact squeeze_zero (fun y => norm_nonneg _) hbound hg

/-- A compactly supported function vanishes outside a ball of computable radius. -/
lemma exists_support_radius {f : ℂ → ℂ} (hc : HasCompactSupport f) :
    ∃ Rf : ℝ, 0 ≤ Rf ∧ ∀ z : ℂ, Rf < ‖z‖ → f z = 0 := by
  have hb : Bornology.IsBounded (tsupport f) := hc.isCompact.isBounded
  rw [Metric.isBounded_iff_subset_closedBall (0 : ℂ)] at hb
  obtain ⟨r, hr⟩ := hb
  refine ⟨max r 0, le_max_right _ _, fun z hz => ?_⟩
  refine image_eq_zero_of_notMem_tsupport fun hmem => ?_
  have h1 : z ∈ Metric.closedBall (0:ℂ) r := hr hmem
  rw [Metric.mem_closedBall, dist_zero_right] at h1
  have h3 : ‖z‖ ≤ max r 0 := le_trans h1 (le_max_left _ _)
  linarith

/-- The iterated derivatives of a smooth compactly supported function are uniformly bounded. -/
lemma exists_iteratedFDeriv_bound {f : ℂ → ℂ} (hf : ContDiff ℝ ∞ f) (hc : HasCompactSupport f) :
    ∃ B : ℕ → ℝ, ∀ (M : ℕ) (z : ℂ), ‖iteratedFDeriv ℝ M f z‖ ≤ B M := by
  have h : ∀ M : ℕ, ∃ C : ℝ, ∀ z : ℂ, ‖iteratedFDeriv ℝ M f z‖ ≤ C := by
    intro M
    have hcM : HasCompactSupport (iteratedFDeriv ℝ M f) := hc.iteratedFDeriv M
    exact (hf.continuous_iteratedFDeriv (by exact_mod_cast le_top)).bounded_above_of_compact_support hcM
  choose B hB using h
  exact ⟨B, hB⟩

/-- **Assembly of `smooth_of_beurling_fixed`.**  This is the target statement, with the `L²`
boundedness of the Beurling transform on continuous bounded Hölder functions (which is proved
separately, `Work.Beltrami.beurling_isometry_L2`) taken as a hypothesis. -/
theorem smooth_of_beurling_fixed_aux
    (hBext : ∃ CB : ℝ, 0 < CB ∧ ∀ {α M K r : ℝ} {g : ℂ → ℂ}, 0 < α → α < 1 → Continuous g →
      (∀ z, ‖g z‖ ≤ M) → (∀ x y : ℂ, ‖g x - g y‖ ≤ K * ‖x - y‖ ^ α) →
      (∀ z, r < ‖z‖ → g z = 0) →
      MemLp (beurling g) 2 volume ∧
        eLpNorm (beurling g) 2 volume ≤ ENNReal.ofReal CB * eLpNorm g 2 volume) :
    ∀ R α K R' : ℝ, 0 < α → α < 1 → ∃ δ : ℝ, 0 < δ ∧ ∀ (μ f u : ℂ → ℂ),
      ContDiff ℝ ∞ μ → HasCompactSupport μ → (∀ z, ‖μ z‖ ≤ δ) →
      ContDiff ℝ ∞ f → HasCompactSupport f → (∀ z, ‖f z‖ ≤ R) → (∀ z, ‖u z‖ ≤ R) →
      (∀ x y : ℂ, ‖u x - u y‖ ≤ K * ‖x - y‖ ^ α) → (∀ z, R' < ‖z‖ → u z = 0) →
      (∀ z, u z = f z + μ z * beurling u z) → ContDiff ℝ ∞ u := by
  intro R α K R' hα hα1
  obtain ⟨CB, hCBpos, hBeur⟩ := hBext
  have hCB : 0 ≤ CB := le_of_lt hCBpos
  refine ⟨1 / (2 * max CB 1), by positivity, ?_⟩
  intro μ f u hμc hμs hμb hfc hfs hfb hub hKu hsupp heq
  -- the smallness condition on `δ`
  have hδCB : 2 * (1 / (2 * max CB 1)) ^ 2 * CB ^ 2 ≤ 1 / 2 := by
    have hCBle : CB ≤ max CB 1 := le_max_left CB 1
    have hδ0 : 0 ≤ 1 / (2 * max CB 1) := by positivity
    have h1 : (1 / (2 * max CB 1)) * CB ≤ 1 / 2 := by
      rw [div_mul_eq_mul_div, one_mul, div_le_iff₀ (by positivity)]
      nlinarith [hCBle]
    have h2 : ((1 / (2 * max CB 1)) * CB) ^ 2 ≤ (1 / 2) ^ 2 :=
      pow_le_pow_left₀ (mul_nonneg hδ0 hCB) h1 2
    nlinarith [h2]
  -- `R ≥ 0` (otherwise the hypotheses on `f` are contradictory)
  have hR : 0 ≤ R := by
    by_contra hR
    have h0 := hfb 0
    have h1 := norm_nonneg (f 0)
    linarith
  -- `u` is continuous
  have hucont : Continuous u := continuous_of_holder_bound hα hKu
  -- the uniform derivative bounds and the support radius
  obtain ⟨Bf, hBf⟩ := exists_iteratedFDeriv_bound hfc hfs
  obtain ⟨Bm, hBm⟩ := exists_iteratedFDeriv_bound hμc hμs
  obtain ⟨Rf, hRf0, hRfsupp⟩ := exists_support_radius hfs
  have hR'0 : 0 ≤ max R' 0 := le_max_right _ _
  have hsupp' : ∀ z : ℂ, max R' 0 < ‖z‖ → u z = 0 := by
    intro z hz
    exact hsupp z (lt_of_le_of_lt (le_max_left R' 0) hz)
  -- the `L²` boundedness of the Beurling transform in the form needed by the bootstrap
  have hB : ∀ {g : ℂ → ℂ} {M K' r : ℝ}, Continuous g → (∀ z, ‖g z‖ ≤ M) →
      (∀ x y : ℂ, ‖g x - g y‖ ≤ K' * ‖x - y‖ ^ α) → (∀ z, r < ‖z‖ → g z = 0) →
      MemLp (beurling g) 2 volume ∧ L2s (beurling g) ≤ CB ^ 2 * L2s g := by
    intro g M K' r hgc hgb hgK hgs
    have hgmem : MemLp g 2 volume :=
      memLp_two_of_bound_support hgc.aestronglyMeasurable (le_max_right r 0) hgb
        (fun z hz => hgs z (lt_of_le_of_lt (le_max_left r 0) hz))
    obtain ⟨hmem, hle⟩ := hBeur hα hα1 hgc hgb hgK hgs
    exact ⟨hmem, L2s_le_of_eLpNorm_le hgmem hmem hCB hle⟩
  -- the mean value bound for iterated differences
  have hF : ∀ {N : ℕ} {φ : ℂ → ℂ} {B : ℝ}, ContDiff ℝ N φ →
      (∀ x, ‖iteratedFDeriv ℝ N φ x‖ ≤ B) →
      ∀ h x, ‖((fun f : ℂ → ℂ => (fun x => f (x + h) - f x))^[N] φ) x‖ ≤ ‖h‖ ^ N * B :=
    fun hφ hB => norm_diffQuot_iterate_le hφ hB
  -- the `L²` bootstrap
  obtain ⟨D, hD⟩ := exists_L2s_iterate_diffQuot_le (α := α) (R := R) (K := K) (R' := max R' 0)
    (Rf := Rf) (CB := CB) (δ := 1 / (2 * max CB 1)) (Bf := Bf) (Bm := Bm)
    hα hα1 hR hRf0 hR'0 hδCB hCB hBf hBm hRfsupp hμc hμb hfc hfb hucont hub hKu hsupp' heq
    hB hF
  -- transfer the `L²` bounds to `eLpNorm` bounds and conclude
  refine contDiff_of_diffQuot_L2 hucont (fun N => |D N|) (fun N h => ?_)
  set P : ℂ → ℂ := ((fun f : ℂ → ℂ => (fun x => f (x + h) - f x))^[N]) u with hP
  have hPc : Continuous P := by rw [hP]; exact iterate_diffQuot_continuous hucont h N
  have hPb : ∀ z, ‖P z‖ ≤ (2:ℝ) ^ N * R := by
    intro z; rw [hP]; exact norm_iterate_diffQuot_le_two_pow hub N h z
  have hPs : ∀ z : ℂ, max R' 0 + N * ‖h‖ < ‖z‖ → P z = 0 := by
    intro z hz; rw [hP]; exact iterate_diffQuot_eq_zero_of_far hsupp' N h z hz
  have hPmem : MemLp P 2 volume :=
    memLp_two_of_bound_support hPc.aestronglyMeasurable
      (add_nonneg hR'0 (mul_nonneg (Nat.cast_nonneg N) (norm_nonneg h))) hPb hPs
  refine eLpNorm_two_le_of_L2s hPmem (by positivity) ?_
  have hD' := hD N h
  rw [← hP] at hD'
  have h4 : (D N * ‖h‖ ^ N) ^ 2 = (|D N| * ‖h‖ ^ N) ^ 2 := by
    rw [← sq_abs (D N * ‖h‖ ^ N), abs_mul,
      abs_of_nonneg (pow_nonneg (norm_nonneg h) N)]
  rw [h4] at hD'
  exact hD'

theorem smooth_of_beurling_fixed :
    ∀ R α K R' : ℝ, 0 < α → α < 1 → ∃ δ : ℝ, 0 < δ ∧ ∀ (μ f u : ℂ → ℂ),
      ContDiff ℝ ∞ μ → HasCompactSupport μ → (∀ z, ‖μ z‖ ≤ δ) →
      ContDiff ℝ ∞ f → HasCompactSupport f → (∀ z, ‖f z‖ ≤ R) → (∀ z, ‖u z‖ ≤ R) →
      (∀ x y : ℂ, ‖u x - u y‖ ≤ K * ‖x - y‖ ^ α) → (∀ z, R' < ‖z‖ → u z = 0) →
      (∀ z, u z = f z + μ z * beurling u z) → ContDiff ℝ ∞ u := by
  obtain ⟨C, hCpos, hE⟩ := beurling_isometry_L2
  refine smooth_of_beurling_fixed_aux ⟨C, hCpos, ?_⟩
  intro α M K r g hα hα1 hgc hgb hgK hgs
  exact hE (R := max r 0) hα hα1 (le_max_right r 0) hgc hgb hgK
    (fun z hz => hgs z (lt_of_le_of_lt (le_max_left r 0) hz))

end

end Work.Beltrami
