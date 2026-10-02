/-
# The analytic Böttcher coordinate of the tricorn is injective on the escape set

For `c` in the mandelbar `M*` and `φ : ℂ → ℂ` analytic on the escape set `E = {z | G_c z > 0}`
with

* `φ (p_c z) = φ(z)^4` on `E` (`p_c = T_c ∘ T_c` is the holomorphic quartic),
* `‖φ z‖ = exp (G_c z)` on `E`,
* `φ z ≠ 0` on `E`,
* `φ z / z → 1` at infinity,

we prove that `φ` is **injective** on `E`.

This is "Step E" of the construction of the inverse Böttcher coordinate
(`Inverse/NOTES.md`): the Böttcher coordinate of the quartic `p_c` is a bijection
`E → {|w| > 1}`, and its injectivity is what makes the inverse well defined.

## Structure of the proof

1. **Reflection / symmetry** (`BottcherReflect.lean`): `T_c` and `p_c` are even, `G_c` is even,
   the product formula `bottcher c` is odd, and the far region `{‖z‖ ≥ escapeRadius c}` is
   escaping.
2. **Oddness of `φ`** (`eq_neg_of_green_pos`): on the far region `φ = bottcher c`
   (`Core.eq_bottcher_of_analytic`), hence `φ(-z) + φ(z) = 0` there; the sum is analytic on the
   (preconnected) escape set, so it vanishes identically.
3. **The antiholomorphic Böttcher relation** (`φ_comm_Tantibar`): from the holomorphic equation
   one derives `φ (T_c z) = conj (φ z)^2` (`bottcher_comm_Tantibar_of_pMap_eq`).
4. **One-step descent** (`pMap_eq_imp_eq`, delegated): if `u, v ∈ E` with `p_c u = p_c v` and
   `φ u = φ v` then `u = v`.  The factorisation `p_c u - p_c v = (u-v)(u+v)(u²+v²+2c̄)` leaves
   the cases `v = -u` (oddness) and `u² + v² = -2c̄` (apply `T_c` to reach the first case).
5. **Assembly**: two points `z₁, z₂ ∈ E` with `φ z₁ = φ z₂` have `φ (p_c^k z_i) = (φ z₁)^(4^k)`,
   so for `k` large both iterates lie in the far region, where `φ` is injective
   (`injOn_far`); hence `p_c^k z₁ = p_c^k z₂`, and the descent (4) gives `z₁ = z₂`.
-/
import Mathlib
import Submission.Work.Bottcher.Defs
import Submission.Work.Bottcher.Green.green_comm
import Submission.Work.Bottcher.Green.green_pos_iff
import Submission.Work.Bottcher.Core.analyticAt_bottcher
import Submission.Work.Bottcher.Core.eq_bottcher_of_analytic
import Submission.Work.Bottcher.Inverse.bottcher_comm_Tantibar_of_pMap_eq
import Submission.Work.Bottcher.Contraction.isPreconnected_escapeSet
import Submission.Work.Bottcher.Inverse.BottcherReflect
import Submission.Work.Bottcher.Inverse.injOn_far
import Submission.Work.Bottcher.Inverse.pMap_eq_imp_eq

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


open Filter Function
open scoped Topology ComplexConjugate

namespace Work.Bottcher.Inverse

open LeanEval.ComplexAnalysis (Tantibar Mandelbar)

noncomputable section

/-! ## Oddness of an analytic Böttcher coordinate -/

/-- **An analytic Böttcher coordinate of `p_c` is odd.**  `φ(-z) = -φ(z)` for every escaping `z`.
On the far region `φ` coincides with the product formula `bottcher c`
(`Core.eq_bottcher_of_analytic`), which is odd; the analytic function `z ↦ φ(-z) + φ(z)` then
vanishes on a neighbourhood of a far point, so it vanishes on the whole (preconnected) escape
set. -/
theorem eq_neg_of_green_pos (c : ℂ) (φ : ℂ → ℂ)
    (han : AnalyticOnNhd ℂ φ {z : ℂ | 0 < Work.Bottcher.green c z})
    (hfe : ∀ z : ℂ, 0 < Work.Bottcher.green c z → φ (Work.Bottcher.pMap c z) = (φ z) ^ 4)
    (hmod : ∀ z : ℂ, 0 < Work.Bottcher.green c z →
      ‖φ z‖ = Real.exp (Work.Bottcher.green c z))
    (has : Filter.Tendsto (fun z : ℂ => φ z / z) (Filter.cocompact ℂ) (nhds (1 : ℂ))) :
    ∀ z : ℂ, 0 < Work.Bottcher.green c z → φ (-z) = -φ z := by
  set E : Set ℂ := {z : ℂ | 0 < Work.Bottcher.green c z} with hE
  have hneg : AnalyticOnNhd ℂ (fun z : ℂ => -z) E := by
    have h : AnalyticOnNhd ℂ (- fun z : ℂ => z) E := analyticOnNhd_id.neg
    convert h using 1
  have hst : Set.MapsTo (fun z : ℂ => -z) E E := by
    intro z hz
    show 0 < Work.Bottcher.green c (-z)
    rw [green_neg]
    exact hz
  have hψ : AnalyticOnNhd ℂ (fun z : ℂ => φ (-z) + φ z) E :=
    (han.comp hneg hst).add han
  -- on the far region `φ` is the product formula, which is odd
  have hbot : ∀ z : ℂ, Work.Bottcher.escapeRadius c ≤ ‖z‖ →
      φ z = Work.Bottcher.bottcher c z :=
    fun z hz => Work.Bottcher.Core.eq_bottcher_of_analytic c φ
      (han.mono (fun w hw => green_pos_of_escapeRadius_le c w hw))
      (fun w hw => hfe w (green_pos_of_escapeRadius_le c w hw))
      (fun w hw => hmod w (green_pos_of_escapeRadius_le c w hw)) has hz
  have hfar_zero : ∀ z : ℂ, Work.Bottcher.escapeRadius c ≤ ‖z‖ → φ (-z) + φ z = 0 := by
    intro z hz
    have hz' : Work.Bottcher.escapeRadius c ≤ ‖-z‖ := by rwa [norm_neg]
    rw [hbot (-z) hz', hbot z hz, bottcher_neg]
    ring
  -- a point in the interior of the far region
  set z₀ : ℂ := ((Work.Bottcher.escapeRadius c + 1 : ℝ) : ℂ) with hz₀
  have hz₀norm : ‖z₀‖ = Work.Bottcher.escapeRadius c + 1 := by
    rw [hz₀, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg (by linarith [(Work.Bottcher.Core.escapeRadius_pos c).le])]
  have hz₀lt : Work.Bottcher.escapeRadius c < ‖z₀‖ := by rw [hz₀norm]; linarith
  have hz₀E : z₀ ∈ E := by
    show 0 < Work.Bottcher.green c z₀
    exact green_pos_of_escapeRadius_le c z₀ (le_of_lt hz₀lt)
  have hev : (fun z : ℂ => φ (-z) + φ z) =ᶠ[𝓝 z₀] 0 := by
    have hopen : {z : ℂ | Work.Bottcher.escapeRadius c < ‖z‖} ∈ 𝓝 z₀ :=
      (isOpen_lt continuous_const continuous_norm).mem_nhds hz₀lt
    filter_upwards [hopen] with z hz
    exact hfar_zero z hz.le
  have hpre : IsPreconnected E := Work.Bottcher.Contraction.isPreconnected_escapeSet c
  have hzero : Set.EqOn (fun z : ℂ => φ (-z) + φ z) 0 E :=
    AnalyticOnNhd.eqOn_zero_of_preconnected_of_eventuallyEq_zero hψ hpre hz₀E hev
  intro z hz
  exact eq_neg_of_add_eq_zero_left (hzero hz)

/-! ## The antiholomorphic Böttcher relation -/

/-- **The antiholomorphic Böttcher equation for an analytic Böttcher coordinate of `p_c`.**
`φ (T_c z) = conj (φ z)^2` for every escaping `z`.  This is
`bottcher_comm_Tantibar_of_pMap_eq` with its tangency hypothesis extracted from `φ z / z → 1`. -/
theorem φ_comm_Tantibar (c : ℂ) (φ : ℂ → ℂ)
    (han : AnalyticOnNhd ℂ φ {z : ℂ | 0 < Work.Bottcher.green c z})
    (hfe : ∀ z : ℂ, 0 < Work.Bottcher.green c z → φ (Work.Bottcher.pMap c z) = (φ z) ^ 4)
    (hmod : ∀ z : ℂ, 0 < Work.Bottcher.green c z →
      ‖φ z‖ = Real.exp (Work.Bottcher.green c z))
    (hZne : ∀ z : ℂ, 0 < Work.Bottcher.green c z → φ z ≠ 0)
    (has : Filter.Tendsto (fun z : ℂ => φ z / z) (Filter.cocompact ℂ) (nhds (1 : ℂ))) :
    ∀ z : ℂ, 0 < Work.Bottcher.green c z →
      φ (Tantibar c z) = (starRingEnd ℂ) (φ z) ^ 2 := by
  have hcont : ContinuousOn φ (Work.Bottcher.EscapeSet c) := by
    show ContinuousOn φ {z : ℂ | 0 < Work.Bottcher.green c z}
    exact han.continuousOn
  have has2 : ∀ ε : ℝ, 0 < ε →
      ∀ᶠ z : ℂ in Filter.cocompact ℂ, ‖φ z - z‖ ≤ ε * ‖z‖ := by
    intro ε hε
    have h1 : ∀ᶠ z : ℂ in Filter.cocompact ℂ, ‖φ z / z - 1‖ < ε := by
      have h := Metric.tendsto_nhds.mp has ε hε
      filter_upwards [h] with z hz
      rwa [dist_eq_norm] at hz
    have h2 : ∀ᶠ z : ℂ in Filter.cocompact ℂ, z ≠ 0 :=
      (isCompact_singleton (x := (0 : ℂ))).compl_mem_cocompact
    filter_upwards [h1, h2] with z hz hz0
    have hzpos : 0 < ‖z‖ := norm_pos_iff.mpr hz0
    have heq : φ z - z = z * (φ z / z - 1) := by
      field_simp
    rw [heq, norm_mul]
    have hlt := mul_lt_mul_of_pos_left hz hzpos
    rw [mul_comm ‖z‖ ε] at hlt
    exact le_of_lt hlt
  have hesc : ∀ᶠ z : ℂ in Filter.cocompact ℂ, 0 < Work.Bottcher.green c z := by
    have h := (tendsto_norm_cocompact_atTop (E := ℂ)).eventually
      (eventually_ge_atTop (Work.Bottcher.escapeRadius c))
    filter_upwards [h] with z hz
    exact green_pos_of_escapeRadius_le c z hz
  exact bottcher_comm_Tantibar_of_pMap_eq c φ hcont hfe hmod hZne has2 hesc

/-! ## The main theorem -/

theorem injOn_analyticBottcher (c : ℂ) (hc : c ∈ LeanEval.ComplexAnalysis.Mandelbar) (φ : ℂ → ℂ)
    (han : AnalyticOnNhd ℂ φ {z : ℂ | 0 < Work.Bottcher.green c z})
    (hfe : ∀ z : ℂ, 0 < Work.Bottcher.green c z → φ (Work.Bottcher.pMap c z) = (φ z) ^ 4)
    (hmod : ∀ z : ℂ, 0 < Work.Bottcher.green c z → ‖φ z‖ = Real.exp (Work.Bottcher.green c z))
    (hZne : ∀ z : ℂ, 0 < Work.Bottcher.green c z → φ z ≠ 0)
    (has : Filter.Tendsto (fun z : ℂ => φ z / z) (Filter.cocompact ℂ) (nhds (1 : ℂ))) :
    Set.InjOn φ {z : ℂ | 0 < Work.Bottcher.green c z} := by
  have _ : c ∈ LeanEval.ComplexAnalysis.Mandelbar := hc
  have hodd := eq_neg_of_green_pos c φ han hfe hmod has
  have hT := φ_comm_Tantibar c φ han hfe hmod hZne has
  intro z₁ hz₁ z₂ hz₂ hφ
  -- the iterates and their `φ`-values
  set u : ℕ → ℂ := fun k => (Work.Bottcher.pMap c)^[k] z₁ with hu
  set v : ℕ → ℂ := fun k => (Work.Bottcher.pMap c)^[k] z₂ with hv
  set W : ℂ := φ z₁ with hW
  have hu_succ : ∀ k, u (k + 1) = Work.Bottcher.pMap c (u k) := by
    intro k
    simp only [hu]
    exact Function.iterate_succ_apply' (Work.Bottcher.pMap c) k z₁
  have hv_succ : ∀ k, v (k + 1) = Work.Bottcher.pMap c (v k) := by
    intro k
    simp only [hv]
    exact Function.iterate_succ_apply' (Work.Bottcher.pMap c) k z₂
  have hgreenu : ∀ k, 0 < Work.Bottcher.green c (u k) := by
    intro k
    have h : Work.Bottcher.green c (u k) = 4 ^ k * Work.Bottcher.green c z₁ := by
      simp only [hu]
      exact green_pMap_iterate c z₁ k
    rw [h]
    exact mul_pos (by positivity) hz₁
  have hgreenv : ∀ k, 0 < Work.Bottcher.green c (v k) := by
    intro k
    have h : Work.Bottcher.green c (v k) = 4 ^ k * Work.Bottcher.green c z₂ := by
      simp only [hv]
      exact green_pMap_iterate c z₂ k
    rw [h]
    exact mul_pos (by positivity) hz₂
  have hφu : ∀ k, φ (u k) = W ^ (4 ^ k) := by
    intro k
    induction k with
    | zero => simp only [hu, Function.iterate_zero_apply, pow_zero, pow_one]; exact hW.symm
    | succ k ih =>
        rw [hu_succ k, hfe (u k) (hgreenu k), ih, ← pow_mul, pow_succ]
  have hφv : ∀ k, φ (v k) = W ^ (4 ^ k) := by
    intro k
    induction k with
    | zero => simp only [hv, Function.iterate_zero_apply, pow_zero, pow_one]; exact hφ.symm
    | succ k ih =>
        rw [hv_succ k, hfe (v k) (hgreenv k), ih, ← pow_mul, pow_succ]
  -- both orbits reach the far region
  have hu_tend : Tendsto u atTop (cocompact ℂ) := tendsto_iterate_pMap_cocompact c hz₁
  have hv_tend : Tendsto v atTop (cocompact ℂ) := tendsto_iterate_pMap_cocompact c hz₂
  have hnrmu : Tendsto (fun k => ‖u k‖) atTop atTop :=
    (tendsto_norm_cocompact_atTop (E := ℂ)).comp hu_tend
  have hnrmv : Tendsto (fun k => ‖v k‖) atTop atTop :=
    (tendsto_norm_cocompact_atTop (E := ℂ)).comp hv_tend
  have hev : ∀ᶠ k : ℕ in atTop, farR c ≤ ‖u k‖ ∧ farR c ≤ ‖v k‖ := by
    filter_upwards [hnrmu.eventually (eventually_ge_atTop (farR c)),
      hnrmv.eventually (eventually_ge_atTop (farR c))] with k hk1 hk2
    exact ⟨hk1, hk2⟩
  obtain ⟨N, hN⟩ := Filter.eventually_atTop.mp hev
  have hkN := hN N le_rfl
  have hfar_eq : u N = v N :=
    injOn_far c φ han hfe hmod has hkN.1 hkN.2 (by rw [hφu N, hφv N])
  -- descend from `u N = v N` to `z₁ = z₂`
  have hdescend : ∀ k, u k = v k → z₁ = z₂ := by
    intro k
    induction k with
    | zero => intro h; exact h
    | succ k ih =>
        intro h
        have h1 : Work.Bottcher.pMap c (u k) = Work.Bottcher.pMap c (v k) := by
          rw [← hu_succ k, ← hv_succ k]
          exact h
        have h2 : φ (u k) = φ (v k) := by rw [hφu k, hφv k]
        exact ih (pMap_eq_imp_eq c φ hodd hT hZne (hgreenu k) (hgreenv k) h1 h2)
  exact hdescend N hfar_eq

end

end Work.Bottcher.Inverse
