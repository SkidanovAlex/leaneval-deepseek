import Mathlib
import Submission.Work.OddCurve.LowSlope.RadialLogDefs

/-!
# Smoothness of the normalised inverse `radInv n`

`RadialLogDefs` defines `radH n x = x ^ (radTh n) - (1 - x) ^ (radTh n)`, a strictly increasing
continuous bijection of `(0,1)` onto `(-1,1)`, and `radInv n` its (set-theoretic) inverse,
extended by `1/2` outside `(-1,1)`.

Here we show that `radInv n` is `C^∞` on `(-3/5, 3/5) ⊂ (-1,1)`.  The proof is the one-dimensional
inverse function theorem: for `w ∈ (-1,1)` the point `x = radInv n w` lies in `(0,1)`, on which
`radH n` is `C^∞` with strictly positive derivative
(`radTh n = (2n+1)/(2n+2) ∈ (0,1)` and both `x ^ (θ-1)`, `(1-x) ^ (θ-1)` are positive).  Hence
`radH n` has a `C^∞` local inverse `g` at `w`, and `g` agrees with `radInv n` near `w` because
both are points of `(0,1)` mapping to the same value under the injective map `radH n`.

The explicit shape of the derivative (`c = θ x ^ (θ-1) + θ (1-x) ^ (θ-1)`) is recorded in
`radH_hasStrictDerivAt`; it is not needed to *state* smoothness, but is what makes the
non-vanishing hypothesis of the inverse function theorem available.
-/

noncomputable section

open Set Filter
open scoped Topology ContDiff

namespace Work.OddCurve.LowSlope

/-- `radH n` is `C^∞` at every point of `(0,1)`. -/
lemma contDiffAt_radH {n : ℕ} {x : ℝ} (hx : x ∈ Set.Ioo (0 : ℝ) 1) :
    ContDiffAt ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (radH n) x := by
  have h1 : ContDiffAt ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun y : ℝ => y ^ (radTh n)) x :=
    Real.contDiffAt_rpow_const_of_ne (ne_of_gt hx.1)
  have h2 : ContDiffAt ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun y : ℝ => (1 - y) ^ (radTh n)) x :=
    (contDiffAt_const.sub contDiffAt_id).rpow_const_of_ne (by linarith [hx.2] : (1 : ℝ) - x ≠ 0)
  exact h1.sub h2

/-- At every point of `(0,1)` the map `radH n` has a nonzero strict derivative, namely
`radTh n * x ^ (radTh n - 1) + radTh n * (1 - x) ^ (radTh n - 1)`. -/
lemma radH_hasStrictDerivAt {n : ℕ} {x : ℝ} (hx : x ∈ Set.Ioo (0 : ℝ) 1) :
    ∃ c : ℝ, c ≠ 0 ∧ HasStrictDerivAt (radH n) c x := by
  have hθ := radTh_pos n
  refine ⟨radTh n * x ^ (radTh n - 1) + radTh n * (1 - x) ^ (radTh n - 1), ?_, ?_⟩
  · have h1 : 0 < x ^ (radTh n - 1) := Real.rpow_pos_of_pos hx.1 _
    have h2 : 0 < (1 - x) ^ (radTh n - 1) := Real.rpow_pos_of_pos (by linarith [hx.2]) _
    nlinarith
  · have h1 : HasStrictDerivAt (fun y : ℝ => y ^ (radTh n)) (radTh n * x ^ (radTh n - 1)) x :=
      Real.hasStrictDerivAt_rpow_const_of_ne (ne_of_gt hx.1) _
    have h2 : HasStrictDerivAt (fun y : ℝ => 1 - y) (-1) x := by
      have h := (hasStrictDerivAt_const (x := x) (1 : ℝ)).sub (hasStrictDerivAt_id x)
      rw [show ((fun _ : ℝ => (1 : ℝ)) - id : ℝ → ℝ) = fun y => 1 - y from rfl] at h
      simpa using h
    have h3 : HasStrictDerivAt (fun y : ℝ => (1 - y) ^ (radTh n))
        (radTh n * (1 - x) ^ (radTh n - 1) * (-1)) x :=
      (Real.hasStrictDerivAt_rpow_const_of_ne (by linarith [hx.2] : (1 : ℝ) - x ≠ 0) _).comp x h2
    have h := h1.sub h3
    have hde : radTh n * x ^ (radTh n - 1) + radTh n * (1 - x) ^ (radTh n - 1)
        = radTh n * x ^ (radTh n - 1) - radTh n * (1 - x) ^ (radTh n - 1) * (-1) := by ring
    rw [hde,
      show radH n = ((fun y : ℝ => y ^ (radTh n)) - fun y => (1 - y) ^ (radTh n)) from rfl]
    exact h

/-- `radInv n` is `C^∞` at every point of `(-1,1)`. -/
lemma contDiffAt_radInv {n : ℕ} {w : ℝ} (hw : |w| < 1) :
    ContDiffAt ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (radInv n) w := by
  have hx1 : radInv n w ∈ Set.Ioo (0 : ℝ) 1 := radInv_mem hw
  have hxw : radH n (radInv n w) = w := radH_radInv hw
  obtain ⟨c, hc0, hsd⟩ := radH_hasStrictDerivAt hx1
  let f' : ℝ ≃L[ℝ] ℝ := ContinuousLinearEquiv.unitsEquivAut ℝ (Units.mk0 c hc0)
  have hsfd : HasStrictFDerivAt (radH n) (f' : ℝ →L[ℝ] ℝ) (radInv n w) :=
    hsd.hasStrictFDerivAt_equiv hc0
  have hn0 : ((⊤ : ℕ∞) : WithTop ℕ∞) ≠ 0 := by simp
  have hcont : ContDiffAt ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (radH n) (radInv n w) := contDiffAt_radH hx1
  -- the local inverse of `radH n` at `radInv n w`, produced by the inverse function theorem
  have hp : HasStrictFDerivAt (radH n) (f' : ℝ →L[ℝ] ℝ) (radInv n w) :=
    hcont.hasStrictFDerivAt' hsfd.hasFDerivAt hn0
  let g : ℝ → ℝ := hp.localInverse (radH n) f' (radInv n w)
  have hg_cont : ContDiffAt ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) g (radH n (radInv n w)) :=
    ContDiffAt.to_localInverse hcont hsfd.hasFDerivAt hn0
  rw [hxw] at hg_cont
  -- `g` agrees with `radInv n` near `w`
  have hg0 : g (radH n (radInv n w)) = radInv n w := hp.localInverse_apply_image
  have hcontg : ContinuousAt g (radH n (radInv n w)) := hp.localInverse_continuousAt
  have hmem : g (radH n (radInv n w)) ∈ Set.Ioo (0 : ℝ) 1 := by rw [hg0]; exact hx1
  have hev1 : ∀ᶠ y in 𝓝 (radH n (radInv n w)), g y ∈ Set.Ioo (0 : ℝ) 1 :=
    hcontg.tendsto.eventually (IsOpen.mem_nhds isOpen_Ioo hmem)
  have hev2 : ∀ᶠ y in 𝓝 (radH n (radInv n w)), radH n (g y) = y := hp.eventually_right_inverse
  rw [hxw] at hev1 hev2
  have hev3 : ∀ᶠ y in 𝓝 w, |y| < 1 := by
    filter_upwards [IsOpen.mem_nhds isOpen_Ioo (abs_lt.mp hw)] with y hy
    exact abs_lt.mpr hy
  have hev : g =ᶠ[𝓝 w] radInv n :=
    ((hev1.and hev2).and hev3).mono fun y hy => radInv_eq_of hy.2 hy.1.1 hy.1.2
  exact hg_cont.congr_of_eventuallyEq hev.symm

set_option linter.unusedVariables false in
/-- The requested statement: `radInv n` is `C^∞` on `(-3/5, 3/5)`.
(The hypothesis `1 ≤ n` is not needed: smoothness holds for every `n`.) -/
theorem radInv_contDiffOn (n : ℕ) (hn : 1 ≤ n) :
    ContDiffOn ℝ (((⊤ : ℕ∞) : WithTop ℕ∞)) (Work.OddCurve.LowSlope.radInv n)
      (Set.Ioo (-3 / 5) (3 / 5)) := by
  refine (isOpen_Ioo.contDiffOn_iff).mpr fun w hw => contDiffAt_radInv ?_
  rw [abs_lt]
  exact ⟨by linarith [hw.1], by linarith [hw.2]⟩

end Work.OddCurve.LowSlope
