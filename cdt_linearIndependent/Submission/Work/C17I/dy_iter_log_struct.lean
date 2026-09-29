import Mathlib
import Submission.Work.C17.seventeen_defs
import Submission.Work.C17I.dy_log_struct

namespace Work.C17I

open Complex Filter
open scoped Topology

/-- `DyIter (k+1) f = Dy (DyIter k f)`: the `(k+1)`-fold iterate is `D_y` applied to the `k`-fold
iterate. -/
theorem DyIter_succ (k : ℕ) (f : ℂ → ℂ) :
    Work.C17.DyIter (k + 1) f = Work.C17.Dy (Work.C17.DyIter k f) := by
  have := Function.iterate_succ_apply' Work.C17.Dy k f
  simp only [Work.C17.DyIter] at this ⊢
  exact this

/-- The factor `(z-1)²/(z²-2z)` of `D_y` is holomorphic on `ball (s:ℂ) δ` as soon as `0` and `2`
are not in that ball. -/
theorem dy_factor_diffOn {s δ : ℝ}
    (hz0 : ∀ z ∈ Metric.ball (s : ℂ) δ, z ≠ 0)
    (hz2 : ∀ z ∈ Metric.ball (s : ℂ) δ, z ≠ 2) :
    DifferentiableOn ℂ (fun z : ℂ => (z - 1) ^ 2 / (z ^ 2 - 2 * z)) (Metric.ball (s : ℂ) δ) := by
  refine DifferentiableOn.div ((differentiableOn_id.sub (differentiableOn_const 1)).pow 2)
    ((differentiableOn_id.pow 2).sub ((differentiableOn_const 2).mul differentiableOn_id)) ?_
  intro z hz
  rw [show z ^ 2 - 2 * z = z * (z - 2) by ring]
  exact mul_ne_zero (hz0 z hz) (sub_ne_zero.mpr (hz2 z hz))

/-- `D_y` preserves holomorphy on `ball (s:ℂ) δ` when `0` and `2` are outside that ball. -/
theorem dy_diffOn {s δ : ℝ} {A : ℂ → ℂ}
    (hz0 : ∀ z ∈ Metric.ball (s : ℂ) δ, z ≠ 0)
    (hz2 : ∀ z ∈ Metric.ball (s : ℂ) δ, z ≠ 2)
    (hA : DifferentiableOn ℂ A (Metric.ball (s : ℂ) δ)) :
    ∀ k : ℕ, DifferentiableOn ℂ (Work.C17.DyIter k A) (Metric.ball (s : ℂ) δ) := by
  intro k
  induction k with
  | zero =>
      rw [Work.C17.DyIter, Function.iterate_zero]
      simpa using hA
  | succ k ih =>
      rw [DyIter_succ]
      have hfun : Work.C17.Dy (Work.C17.DyIter k A)
          = fun z : ℂ => deriv (Work.C17.DyIter k A) z * ((z - 1) ^ 2 / (z ^ 2 - 2 * z)) := by
        funext z
        simp only [Work.C17.Dy]
        rw [mul_div_assoc]
      rw [hfun]
      exact (ih.deriv Metric.isOpen_ball).mul (dy_factor_diffOn hz0 hz2)

/-- **One step of `D_y`.**  Suppose `A`, `G` are holomorphic on the ball `ball (s:ℂ) δ` and, on the
lens `ball (s:ℂ) δ ∩ ball 0 ρ` (with `ρ ≤ s`), `F` agrees with `A · log (s - ·) + G/(· - s)^m`.
Then `D_y F` agrees on that same lens with `(D_y A) · log (s - ·) + G'/(· - s)^(m+1)` with `G'`
holomorphic on the ball.

(The proof never uses any differentiability of `F` beyond the pointwise identity: the value of
`deriv F z` at `z` in the lens is forced by the identity in a neighbourhood of `z`.) -/
theorem dy_step {s δ ρ : ℝ} (hρ : ρ ≤ s) {m : ℕ} {F A G : ℂ → ℂ}
    (hz0 : ∀ z ∈ Metric.ball (s : ℂ) δ, z ≠ 0)
    (hz2 : ∀ z ∈ Metric.ball (s : ℂ) δ, z ≠ 2)
    (hA : DifferentiableOn ℂ A (Metric.ball (s : ℂ) δ))
    (hG : DifferentiableOn ℂ G (Metric.ball (s : ℂ) δ))
    (h : ∀ z ∈ Metric.ball (s : ℂ) δ ∩ Metric.ball (0 : ℂ) ρ,
      F z = A z * Complex.log (s - z) + G z / (z - s) ^ m) :
    ∃ G' : ℂ → ℂ, DifferentiableOn ℂ G' (Metric.ball (s : ℂ) δ) ∧
      ∀ z ∈ Metric.ball (s : ℂ) δ ∩ Metric.ball (0 : ℂ) ρ,
        Work.C17.Dy F z = Work.C17.Dy A z * Complex.log (s - z)
          + G' z / (z - s) ^ (m + 1) := by
  classical
  have hUopen : IsOpen (Metric.ball (s : ℂ) δ) := Metric.isOpen_ball
  refine ⟨fun z => ((z - 1) ^ 2 / (z ^ 2 - 2 * z)) *
      (A z * (z - s) ^ m + deriv G z * (z - s) - (m : ℂ) * G z), ?_, ?_⟩
  · refine (dy_factor_diffOn hz0 hz2).mul ?_
    exact ((hA.mul ((differentiableOn_id.sub (differentiableOn_const (s : ℂ))).pow m)).add
      (((hG.deriv hUopen).mul (differentiableOn_id.sub (differentiableOn_const (s : ℂ)))))).sub
      ((differentiableOn_const (m : ℂ)).mul hG)
  · intro z hz
    obtain ⟨hzU, hzB⟩ := hz
    -- the lens is contained in the ball `ball 0 s` because `ρ ≤ s`
    have hzn : ‖z‖ < s := by
      have h1 := hzB
      rw [Metric.mem_ball, Complex.dist_eq, sub_zero] at h1
      linarith
    have hre : 0 < (s - z).re := by
      have h3 : z.re ≤ ‖z‖ := Complex.re_le_norm z
      rw [Complex.sub_re, Complex.ofReal_re]
      linarith
    have hsr : s - z ≠ 0 := by
      intro h0
      have : (s - z).re = 0 := by rw [h0]; simp
      linarith
    have hDne : z - s ≠ 0 := by
      intro h0
      exact hsr (by rw [show s - z = -(z - s) by ring, h0]; simp)
    have hden2 : z ^ 2 - 2 * z ≠ 0 := by
      rw [show z ^ 2 - 2 * z = z * (z - 2) by ring]
      exact mul_ne_zero (hz0 z hzU) (sub_ne_zero.mpr (hz2 z hzU))
    -- `F` agrees with the model function near `z`, hence the derivatives agree
    have hLmem : Metric.ball (s : ℂ) δ ∩ Metric.ball (0 : ℂ) ρ ∈ 𝓝 z :=
      (Metric.isOpen_ball.inter Metric.isOpen_ball).mem_nhds ⟨hzU, hzB⟩
    have heq : F =ᶠ[𝓝 z] (fun w : ℂ => A w * Complex.log (s - w) + G w / (w - s) ^ m) :=
      Filter.eventually_of_mem hLmem h
    have hderivF : deriv F z
        = deriv (fun w : ℂ => A w * Complex.log (s - w) + G w / (w - s) ^ m) z :=
      heq.deriv_eq
    have hAat : HasDerivAt A (deriv A z) z :=
      (hA.differentiableAt (hUopen.mem_nhds hzU)).hasDerivAt
    have hGat : HasDerivAt G (deriv G z) z :=
      (hG.differentiableAt (hUopen.mem_nhds hzU)).hasDerivAt
    -- `(log (s - ·))' = 1/(· - s)` on the lens
    have hlog : HasDerivAt (fun w : ℂ => Complex.log (s - w)) (1 / (z - s)) z := by
      have hinner : HasDerivAt (fun w : ℂ => (s : ℂ) - w) (-1) z :=
        (hasDerivAt_id' z).const_sub (s : ℂ)
      have hsl : (s - z) ∈ Complex.slitPlane := Complex.mem_slitPlane_iff.mpr (Or.inl hre)
      have hh := (Complex.hasDerivAt_log hsl).comp z hinner
      have hval : (s - z)⁻¹ * (-1) = 1 / (z - s) := by
        rw [one_div, show z - s = -(s - z) by ring, inv_neg]
        ring
      rwa [hval] at hh
    have hLogp : HasDerivAt (fun w : ℂ => A w * Complex.log (s - w))
        (deriv A z * Complex.log (s - z) + A z * (1 / (z - s))) z :=
      hAat.mul hlog
    -- the polar part: `(G/(·-s)^m)' = Gd/(·-s)^m - mG/(·-s)^(m+1)`
    have hGp : HasDerivAt (fun w : ℂ => G w / (w - s) ^ m)
        (deriv G z / (z - s) ^ m - (m : ℂ) * G z / (z - s) ^ (m + 1)) z := by
      have hp : HasDerivAt (fun w : ℂ => (w - s) ^ (-(m : ℤ)))
          (((-(m : ℤ) : ℤ) : ℂ) * (z - s) ^ (-(m : ℤ) - 1)) z := by
        have hh := (hasDerivAt_zpow (-(m : ℤ)) (z - s) (Or.inl hDne)).comp z
          ((hasDerivAt_id' z).sub_const (s : ℂ))
        simpa only [Function.comp_def, mul_one] using hh
      have hmul := hGat.mul hp
      have hdval : deriv G z * (z - s) ^ (-(m : ℤ))
            + G z * (((-(m : ℤ) : ℤ) : ℂ) * (z - s) ^ (-(m : ℤ) - 1))
          = deriv G z / (z - s) ^ m - (m : ℂ) * G z / (z - s) ^ (m + 1) := by
        rw [zpow_neg, zpow_natCast,
          show (-(m : ℤ) - 1) = -((m + 1 : ℕ) : ℤ) by push_cast; ring, zpow_neg,
          zpow_natCast]
        push_cast
        ring
      have hfun : (G * fun w : ℂ => (w - s) ^ (-(m : ℤ))) = fun w : ℂ => G w / (w - s) ^ m := by
        funext w
        simp only [Pi.mul_apply]
        rw [zpow_neg, zpow_natCast]
        rfl
      rw [hfun] at hmul
      rw [hdval] at hmul
      exact hmul
    have hH : HasDerivAt (fun w : ℂ => A w * Complex.log (s - w) + G w / (w - s) ^ m)
        (deriv A z * Complex.log (s - z) + A z * (1 / (z - s))
          + (deriv G z / (z - s) ^ m - (m : ℂ) * G z / (z - s) ^ (m + 1))) z :=
      hLogp.add hGp
    -- the algebraic rearrangement, with `(z-s)^(m+1) = (z-s)^m·(z-s)`
    have hfinal : (deriv A z * Complex.log (s - z) + A z * (1 / (z - s))
          + (deriv G z / (z - s) ^ m - (m : ℂ) * G z / (z - s) ^ (m + 1)))
            * (z - 1) ^ 2 / (z ^ 2 - 2 * z)
        = deriv A z * (z - 1) ^ 2 / (z ^ 2 - 2 * z) * Complex.log (s - z)
          + ((z - 1) ^ 2 / (z ^ 2 - 2 * z))
              * (A z * (z - s) ^ m + deriv G z * (z - s) - (m : ℂ) * G z)
            / (z - s) ^ (m + 1) := by
      rw [pow_succ]
      field_simp
      ring
    rw [Work.C17.Dy, Work.C17.Dy, hderivF, hH.deriv]
    exact hfinal

theorem dy_iter_log_struct {s δ ρ : ℝ} (hδ : 0 < δ) (hs : 0 < s) (hρ : ρ < s)
    (hne : (Metric.ball (s : ℂ) δ ∩ Metric.ball (0 : ℂ) ρ).Nonempty)
    (hz0 : ∀ z ∈ Metric.ball (s : ℂ) δ, z ≠ 0)
    (hz2 : ∀ z ∈ Metric.ball (s : ℂ) δ, z ≠ 2)
    {F A G : ℂ → ℂ}
    (hF : DifferentiableOn ℂ F (Metric.ball (s : ℂ) δ ∩ Metric.ball (0 : ℂ) ρ))
    (hA : DifferentiableOn ℂ A (Metric.ball (s : ℂ) δ))
    (hG : DifferentiableOn ℂ G (Metric.ball (s : ℂ) δ))
    (h : ∀ z ∈ Metric.ball (s : ℂ) δ ∩ Metric.ball (0 : ℂ) ρ,
      F z = A z * Complex.log (s - z) + G z) :
    ∀ k : ℕ, ∃ Gk : ℂ → ℂ, DifferentiableOn ℂ Gk (Metric.ball (s : ℂ) δ) ∧
      ∀ z ∈ Metric.ball (s : ℂ) δ ∩ Metric.ball (0 : ℂ) ρ,
        Work.C17.DyIter k F z = Work.C17.DyIter k A z * Complex.log (s - z)
          + Gk z / (z - s) ^ k := by
  classical
  have _ := hδ
  have _ := hs
  have _ := hne
  have _ := hF
  -- `D_y^k A` stays holomorphic on the ball
  have hAk := dy_diffOn (s := s) (δ := δ) hz0 hz2 hA
  have hmain : ∀ k : ℕ, ∃ Gk : ℂ → ℂ, DifferentiableOn ℂ Gk (Metric.ball (s : ℂ) δ) ∧
      ∀ z ∈ Metric.ball (s : ℂ) δ ∩ Metric.ball (0 : ℂ) ρ,
        Work.C17.DyIter k F z = Work.C17.DyIter k A z * Complex.log (s - z)
          + Gk z / (z - s) ^ k := by
    intro k
    induction k with
    | zero =>
        refine ⟨G, hG, ?_⟩
        intro z hz
        simpa [Work.C17.DyIter, Function.iterate_zero_apply] using h z hz
    | succ k ih =>
        obtain ⟨Gk, hGk, hval⟩ := ih
        obtain ⟨G', hG', hval'⟩ :=
          dy_step (s := s) (δ := δ) (ρ := ρ) hρ.le (m := k)
            (F := Work.C17.DyIter k F) (A := Work.C17.DyIter k A) (G := Gk)
            hz0 hz2 (hAk k) hGk hval
        refine ⟨G', hG', ?_⟩
        intro z hz
        rw [DyIter_succ, DyIter_succ]
        exact hval' z hz
  exact hmain

end Work.C17I
