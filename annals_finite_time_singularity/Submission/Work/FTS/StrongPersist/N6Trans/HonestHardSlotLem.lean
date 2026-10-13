import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Integral.IntegrableOn
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.FTS.StrongPersist.N6Trans.HonestSupMixed
import Submission.Work.FTS.StrongPersist.N6Trans.HardSlotAux.IbpSliceBound
import Submission.Work.FTS.StrongPersist.N6Trans.HardSlotAux.SlotIntegrableHonest

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.StrongPersist.N6Trans

open scoped Real Topology
open MeasureTheory Set Filter

set_option autoImplicit false
set_option maxHeartbeats 800000

/-- **The honest-class angular integration-by-parts bound for a single order-five `g`-block**
(the "hard slot" of the `D_θ`-transport estimate), with the `ℋ⁴`-norm of `f` measuring the
coefficient.

For `f`, `g` of class `C^∞` on the *open* quadrant, `f`, `g` honestly in `ℋ⁴` and `g` with the
order-four decay `DecayAll 4 g`, and for the angular exponent `q` of one of the three weights
`0`, `η`, `γ` occurring in the unfolding of the coercive inner product, the pairing

  `∫_θ w(z)² · sin(2θ)^{-q} · f(z,θ) · D_θ(D_z^bD_θ^a g)(z,θ) · D_z^bD_θ^a g(z,θ)`

(`a + b = 4`, `q = η` when `a = 0` and `q ∈ {0, η, γ}` when `a ≥ 1`) is bounded in absolute
value by `C/√(γ-1)·|f|_{ℋ⁴}·w(z)²·∫_θ (D_z^bD_θ^a g)²·sin(2θ)^{-q}`, uniformly in `z ∈ Iz`.

Route: the pointwise `L^∞`-bounds `|f| ≤ Kf`, `|D_θf| ≤ Kf` with
`Kf = C₁/√(γ-1)·|f|_{ℋ⁴}` come from `HonestSupMixed`; the angular integration by parts
`HardSlotAux.IbpSliceBound` (cut-off near the two endpoints, `Work.H2.T1Q.IbpCutoff` for an
arbitrary real exponent, then the limit `ζ → 0⁺` by dominated convergence) converts the pairing
into `∫_θ (v²)·(D_θf/2 + (1-q)cos(2θ)f)·sin(2θ)^{-q}`, whose absolute value is at most
`(3/2)·Kf` times the slot integral; the slot itself is integrable by
`HardSlotAux.SlotIntegrableHonest` (it is a summand of the `ℋ⁴`-integrand of `g`). -/
theorem HonestHardSlotLem : ∃ C : ℝ, 0 < C ∧ ∀ (α : ℝ) (f g : ℝ → ℝ → ℝ) (q : ℝ),
    0 < α → α ≤ 1 →
    Work.FTS.EllipticEst.SmoothOpen f → Work.Spaces.HkMem α 4 f →
    Work.FTS.EllipticEst.SmoothOpen g → Work.Spaces.HkMem α 4 g →
    Work.Spaces.DecayAll 4 g →
    ∀ (a b : ℕ), a + b = 4 → (1 ≤ a → q = 0 ∨ q = Work.Spaces.eta ∨ q = Work.Spaces.gam α) →
      (a = 0 → q = Work.Spaces.eta) → ∀ z ∈ Work.Spaces.Iz,
      |∫ θ in Work.Spaces.Iθ, (Work.Spaces.w z) ^ 2 * (Real.sin (2 * θ)) ^ (-q) * f z θ
          * Work.Spaces.Dth (Work.Spaces.mixed b a g) z θ * Work.Spaces.mixed b a g z θ|
        ≤ C / Real.sqrt (Work.Spaces.gam α - 1) * Work.Spaces.HkNorm α 4 f
            * ((Work.Spaces.w z) ^ 2 * ∫ θ in Work.Spaces.Iθ,
                (Work.Spaces.mixed b a g z θ) ^ 2 * (Real.sin (2 * θ)) ^ (-q)) := by
  obtain ⟨C₁, hC₁pos, hC₁⟩ := Work.FTS.StrongPersist.N6Trans.HonestSupMixed
  obtain ⟨B, hBpos, hB⟩ := Work.FTS.StrongPersist.N6Trans.HardSlotAux.IbpSliceBound
  refine ⟨C₁ * (3 / 2 + B / 2), by positivity, ?_⟩
  intro α f g q hα hα1 hfsm hfmem hgsm hgmem hgdec a b hab hqa hq0 z hz
  set Kf : ℝ := C₁ / Real.sqrt (Work.Spaces.gam α - 1) * Work.Spaces.HkNorm α 4 f with hKf
  have hKf0 : 0 ≤ Kf := by
    rw [hKf]
    exact mul_nonneg (div_nonneg hC₁pos.le (Real.sqrt_nonneg _))
      (Work.Spaces.HkNorm_nonneg α 4 f)
  -- the only two facts about `q` used below
  have hqabs : |1 - q| ≤ 1 := by
    rcases Nat.eq_zero_or_pos a with ha0 | hapos
    · rw [hq0 ha0]
      norm_num [Work.Spaces.eta]
    · rcases hqa hapos with h | h | h
      · subst h; norm_num
      · subst h; norm_num [Work.Spaces.eta]
      · subst h
        rw [Work.Spaces.gam]
        have h2 : (1 : ℝ) - (1 + α / 10) = -(α / 10) := by ring
        rw [h2, abs_neg, abs_of_nonneg (by linarith)]
        linarith
  rcases eq_or_lt_of_le (Set.mem_Ici.mp hz) with hz0 | hzpos
  · -- the degenerate slice `z = 0`: the radial weight vanishes, so both sides are `0`
    subst hz0
    have hw0 : Work.Spaces.w 0 = 0 := by norm_num [Work.Spaces.w]
    have h0 : (fun θ : ℝ => (Work.Spaces.w 0) ^ 2 * (Real.sin (2 * θ)) ^ (-q) * f 0 θ
        * Work.Spaces.Dth (Work.Spaces.mixed b a g) 0 θ * Work.Spaces.mixed b a g 0 θ)
        = fun _ => (0 : ℝ) := by
      funext θ
      rw [hw0]
      ring
    rw [h0, MeasureTheory.integral_zero, abs_zero, hw0]
    simp
  · -- the genuine slice `z > 0`: strip the (constant) radial factor `w(z)²`, reduce to the
    -- angular slices `F`, `V` and apply the integration-by-parts bound
    set F : ℝ → ℝ := fun θ => f z θ with hF
    set V : ℝ → ℝ := fun θ => Work.Spaces.mixed b a g z θ with hV
    have hF1 : ContDiffOn ℝ 1 F (Set.Ioo 0 (π / 2)) := by
      rw [hF]
      exact (hfsm.curry_θ hzpos).of_le (by simp [Work.Stability.smoothOrder])
    have hV1 : ContDiffOn ℝ 1 V (Set.Ioo 0 (π / 2)) := by
      rw [hV]
      exact ((hgsm.mixed b a).curry_θ hzpos).of_le
        (by simp [Work.Stability.smoothOrder])
    have hFb : ∀ θ ∈ Set.Ioo 0 (π / 2), |F θ| ≤ Kf := by
      intro θ hθ
      have h := hC₁ α f hα hα1 hfsm hfmem 0 0 (by norm_num) z θ hzpos hθ.1 hθ.2
      have h' : |f z θ| ≤ C₁ / Real.sqrt (Work.Spaces.gam α - 1) * Work.Spaces.HkNorm α 4 f := h
      simpa only [hF, hKf] using h'
    have hFd : ∀ θ ∈ Set.Ioo 0 (π / 2), |Real.sin (2 * θ) * deriv F θ| ≤ Kf := by
      intro θ hθ
      have h := hC₁ α f hα hα1 hfsm hfmem 0 1 (by norm_num) z θ hzpos hθ.1 hθ.2
      have h' : |Work.Spaces.Dth f z θ| ≤ C₁ / Real.sqrt (Work.Spaces.gam α - 1)
          * Work.Spaces.HkNorm α 4 f := h
      simpa only [hF, hKf, Work.Spaces.Dth, Work.Spaces.pth] using h'
    have hint : MeasureTheory.IntegrableOn
        (fun θ => (V θ) ^ 2 * (Real.sin (2 * θ)) ^ (-q)) Work.Spaces.Iθ := by
      have h := Work.FTS.StrongPersist.N6Trans.HardSlotAux.SlotIntegrableHonest
        α g a b q hα hgsm hgmem hab hqa hq0 hzpos
      simpa only [hV] using h
    have hslice := hB q Kf F V hKf0 hqabs hF1 hV1 hFb hFd hint
    have hcongr : (fun θ : ℝ => (Work.Spaces.w z) ^ 2 * (Real.sin (2 * θ)) ^ (-q) * f z θ
          * Work.Spaces.Dth (Work.Spaces.mixed b a g) z θ * Work.Spaces.mixed b a g z θ)
        = fun θ : ℝ => (Work.Spaces.w z) ^ 2 * ((Real.sin (2 * θ)) ^ (-q) * F θ
            * (Real.sin (2 * θ) * deriv V θ) * V θ) := by
      funext θ
      simp only [hF, hV, Work.Spaces.Dth, Work.Spaces.pth]
      ring
    calc |∫ θ in Work.Spaces.Iθ, (Work.Spaces.w z) ^ 2 * (Real.sin (2 * θ)) ^ (-q) * f z θ
          * Work.Spaces.Dth (Work.Spaces.mixed b a g) z θ * Work.Spaces.mixed b a g z θ|
        = (Work.Spaces.w z) ^ 2 * |∫ θ in Work.Spaces.Iθ, (Real.sin (2 * θ)) ^ (-q) * F θ
            * (Real.sin (2 * θ) * deriv V θ) * V θ| := by
          rw [hcongr, MeasureTheory.integral_const_mul, abs_mul,
            abs_of_nonneg (sq_nonneg (Work.Spaces.w z))]
      _ ≤ (Work.Spaces.w z) ^ 2 * ((3 / 2 + B / 2) * Kf
            * ∫ θ in Work.Spaces.Iθ, (V θ) ^ 2 * (Real.sin (2 * θ)) ^ (-q)) :=
          mul_le_mul_of_nonneg_left hslice (sq_nonneg _)
      _ = C₁ * (3 / 2 + B / 2) / Real.sqrt (Work.Spaces.gam α - 1)
            * Work.Spaces.HkNorm α 4 f
            * ((Work.Spaces.w z) ^ 2 * ∫ θ in Work.Spaces.Iθ,
                (V θ) ^ 2 * (Real.sin (2 * θ)) ^ (-q)) := by
          rw [hKf]; ring
      _ = C₁ * (3 / 2 + B / 2) / Real.sqrt (Work.Spaces.gam α - 1)
            * Work.Spaces.HkNorm α 4 f
            * ((Work.Spaces.w z) ^ 2 * ∫ θ in Work.Spaces.Iθ,
                (Work.Spaces.mixed b a g z θ) ^ 2 * (Real.sin (2 * θ)) ^ (-q)) := by
          simp only [hV]

end Work.FTS.StrongPersist.N6Trans
