/-
# Area A5: the assembly

The minor-arc input (B) of §4 for the concrete projections `kmtPj ρ`, from area A1
(the Ionescu--Wainger multiplier theorem) and `ImprovKMT` (area A4), by interpolation.

## The argument

Fix `P`, `p₁, p₂ ∈ (1, ∞)` with `p₁⁻¹ + p₂⁻¹ ≤ 1`, put `x_i = (p_i).toReal` and
`pr = (1/x₁ + 1/x₂)⁻¹`.  The `thetaSetup` lemma produces `θ ∈ (0,1)` and `V₁, V₂, V₃ > 0` with
`1/V_i = (1/x_i - (1-θ)/2)/θ`, `1/V₃ = 1/V₁ + 1/V₂` and `1/pr = (1-θ) + θ/V₃`.

For each scale `N`, with `L = heightScale C₀ ⌊N⌋`, `K = -Log⌊N⌋ + L` and
`K₂ = -d·Log⌊N⌋ + d·L` (`d = P.natDegree`), the two minor-arc parts
`minorArc₁ = Ã_N(f - Π_{≤L,≤K}f, g)` and `minorArc₂ = Ã_N(Π_{≤L,≤K}f, g - Π_{≤L,≤K₂}g)`
satisfy

* the **gain** estimate `ℓ² × ℓ² → ℓ¹` with weight `improvWeight c ρ L ⌊N⌋ = 2^{-c(L-1)} +
  (Log⌊N⌋)^{-c/ρ}` (`ImprovKMT` via `kmtProj_sub_comp_eq_zero`, `gainEndpoint_explicit`);
* the **loss** estimate `ℓ^{V₁} × ℓ^{V₂} → ℓ^{V₃}` with constant `⟨L⟩` (`iw-prop`(i) via A1 and
  Hölder, `lossEndpoint₁/₂`), valid whenever `(L,K)`, `(L,K₂)` have good major arcs.

Stein interpolation between the two endpoints (`interpBound` for `pr > 1`, `interpBoundOne` for
the degenerate `pr = 1`) gives the estimate at `(x₁,x₂,pr)` for finitely supported inputs; the
extension to all inputs with finite `ℒ^p` seminorm is `extendToAllBdd`, and the trivial endpoint
`endpoint_trivial` removes the finiteness hypotheses.  The weight
`(improvWeight c ρ L ⌊N⌋)^{1-θ}⟨L⟩²` is absorbed by `⟨Log N⟩^{-10}` through
`absorbWeightStrict` + `gainLoss_combine_sq`, in the regime `10 < c C₀ (1-θ)`, `10ρ < c(1-θ)`.

For the finitely many small scales `⌊N⌋ < n₀` (where the good-major-arc condition may fail) one
uses the trivial Hölder endpoint at `(x₁,x₂,pr)` directly (`lossEndpoint₁/₂` with the crude
projection bounds `kmtProj_crude_lp`); the weight `heightWeight 10 ⌊N⌋` is comparable to
`heightWeight 10 N` (`heightWeight_floor_le`).

The good-major-arc threshold `n₀` is `goodMajorArcs_eventually` (which needs `ρ C₀ < 1`), and the
hierarchy of constants is `C₀min = 10/(c(1-θ))` first, then
`ρ₀ = min(1, c(1-θ)/11, 1/(2C₀))`.
-/
import Mathlib
import Submission.Work.KMTAreas.A5.thetaSetup
import Submission.Work.KMTAreas.A5.kmtProj_sub_comp_eq_zero
import Submission.Work.KMTAreas.A5.kmtProj_crude_lp
import Submission.Work.KMTAreas.A5.interpBound
import Submission.Work.KMTAreas.A5.interpBoundOne
import Submission.Work.KMTAreas.A5.extendToAllBdd
import Submission.Work.KMTAreas.A5.absorbWeightStrict
import Submission.Work.KMTAreas.A5.minorArc_tendsto_truncZ
import Submission.Work.KMTAreas.A5.goodMajorArcs_eventually
import Submission.Work.KMTAreas.A5.gainEndpoint_explicit
import Submission.Work.KMTAreas.A5.heightWeight_floor_le
import Submission.Work.KMTAreas.A5.gainLoss_combine_sq

set_option autoImplicit false
set_option maxHeartbeats 4000000

namespace Work.KMTAreas.A5

noncomputable section

open MeasureTheory Polynomial Finset Filter Topology
open scoped ENNReal NNReal BigOperators
open Work.KMTContract
open Work.Analysis.EndVar
open Work.Analysis.IonescuWainger
open Work.Analysis.IWMultiplier
open Submission.PointwiseErgodicTheorems

/-! ## Elementary helpers -/

/-- The weight `heightWeight c N` is positive. -/
theorem heightWeight_pos (c : ℝ) (N : ℝ≥0) : 0 < Work.Analysis.EndVar.heightWeight c N := by
  rw [← NNReal.coe_pos, Work.Analysis.EndVar.coe_heightWeight]
  exact Real.rpow_pos_of_pos (lt_of_lt_of_le zero_lt_one (le_max_left (1 : ℝ) _)) _

/-- A finitely supported function on `ℤ` is a simple function all of whose level sets are
finite; this is the bridge from the interpolation conclusion (`interpBound`) to the
hypothesis of `extendToAllBdd`. -/
theorem exists_simpleFunc_eq_of_finite_support {f : ℤ → ℂ}
    (hf : (Function.support f).Finite) :
    ∃ F : SimpleFunc ℤ ℂ, (F : ℤ → ℂ) = f ∧
      ∀ c ∈ F.range, c ≠ 0 → Measure.count (F ⁻¹' {c}) < ⊤ := by
  have hrange : (Set.range f).Finite := by
    have him : (f '' (Function.support f)).Finite := hf.image f
    have hU : (f '' (Function.support f) ∪ ({0} : Set ℂ)).Finite :=
      him.union (Set.finite_singleton 0)
    refine hU.subset ?_
    rintro y ⟨x, rfl⟩
    by_cases hx : f x = 0
    · exact Or.inr (by simpa using hx)
    · exact Or.inl ⟨x, hx, rfl⟩
  refine ⟨SimpleFunc.mk f (fun c => (measurable_of_countable f)
    (measurableSet_singleton c)) hrange, rfl, ?_⟩
  intro c hc hcne
  refine Measure.count_apply_lt_top.mpr ?_
  refine hf.subset ?_
  intro x hx
  have hxc : f x = c := hx
  simpa [hxc] using hcne

/-- **Transport of an interpolation estimate from simple functions to finitely supported
functions.** -/
theorem extend_interp {T : (ℤ → ℂ) → (ℤ → ℂ) → (ℤ → ℂ)} {x₁ x₂ pr : ℝ} {M : ℝ≥0∞}
    (hinterp : ∀ f g : SimpleFunc ℤ ℂ,
      (∀ c ∈ f.range, c ≠ 0 → Measure.count (f ⁻¹' {c}) < ⊤) →
      (∀ c ∈ g.range, c ≠ 0 → Measure.count (g ⁻¹' {c}) < ⊤) →
      eLpNorm (T (f : ℤ → ℂ) (g : ℤ → ℂ)) (ENNReal.ofReal pr) Measure.count
        ≤ M * eLpNorm (f : ℤ → ℂ) (ENNReal.ofReal x₁) Measure.count
            * eLpNorm (g : ℤ → ℂ) (ENNReal.ofReal x₂) Measure.count) :
    ∀ f g : ℤ → ℂ, (Function.support f).Finite → (Function.support g).Finite →
      eLpNorm (T f g) (ENNReal.ofReal pr) Measure.count
        ≤ M * eLpNorm f (ENNReal.ofReal x₁) Measure.count
            * eLpNorm g (ENNReal.ofReal x₂) Measure.count := by
  intro f g hf hg
  obtain ⟨F, hF, hFL⟩ := exists_simpleFunc_eq_of_finite_support hf
  obtain ⟨G, hG, hGL⟩ := exists_simpleFunc_eq_of_finite_support hg
  rw [← hF, ← hG]
  exact hinterp F G hFL hGL

/-- **Stein interpolation plus extension, non-degenerate case.** -/
theorem interp_step_nd {T : (ℤ → ℂ) → (ℤ → ℂ) → (ℤ → ℂ)}
    (hlin₁ : ∀ (u u' v : ℤ → ℂ) (c : ℂ), BoundedZ u → BoundedZ u' → BoundedZ v →
      T (u + c • u') v = T u v + c • T u' v)
    (hlin₂ : ∀ (u v v' : ℤ → ℂ) (c : ℂ), BoundedZ u → BoundedZ v → BoundedZ v' →
      T u (v + c • v') = T u v + c • T u v')
    (htend : ∀ f g : ℤ → ℂ, BoundedZ f → BoundedZ g → ∀ x : ℤ,
      Filter.Tendsto (fun K' : ℕ => T (truncZ K' f) (truncZ K' g) x)
        Filter.atTop (nhds (T f g x)))
    {x₁ x₂ pr θ V₁ V₂ V₃ : ℝ} (hx₁ : 1 < x₁) (hx₂ : 1 < x₂)
    (hV₁ : 1 < V₁) (hV₂ : 1 < V₂) (hV₃ : 1 < V₃) (hpr : 1 < pr)
    (hθ₀ : 0 < θ) (hθ₁ : θ < 1)
    (hx₁rel : 1 / x₁ = (1 - θ) / 2 + θ / V₁)
    (hx₂rel : 1 / x₂ = (1 - θ) / 2 + θ / V₂)
    (hrθ : 1 / pr = 1 - θ / (V₃ / (V₃ - 1)))
    {M₀ M₁ : ℝ≥0}
    (hgain : ∀ u v : ℤ → ℂ, eLpNorm (T u v) 1 Measure.count
      ≤ (M₀ : ℝ≥0∞) * eLpNorm u 2 Measure.count * eLpNorm v 2 Measure.count)
    (hloss : ∀ u v : ℤ → ℂ, eLpNorm (T u v) (ENNReal.ofReal V₃) Measure.count
      ≤ (M₁ : ℝ≥0∞) * eLpNorm u (ENNReal.ofReal V₁) Measure.count
          * eLpNorm v (ENNReal.ofReal V₂) Measure.count) :
    ∀ f g : ℤ → ℂ, MemLp f (ENNReal.ofReal x₁) Measure.count →
      MemLp g (ENNReal.ofReal x₂) Measure.count →
      eLpNorm (T f g) (ENNReal.ofReal pr) Measure.count
        ≤ (M₀ : ℝ≥0∞) ^ (1 - θ) * (M₁ : ℝ≥0∞) ^ θ
          * eLpNorm f (ENNReal.ofReal x₁) Measure.count
          * eLpNorm g (ENNReal.ofReal x₂) Measure.count := by
  have hx₁pos : 0 < x₁ := lt_trans one_pos hx₁
  have hx₂pos : 0 < x₂ := lt_trans one_pos hx₂
  have hr₁ : 1 < V₃ / (V₃ - 1) := by
    rw [lt_div_iff₀ (by linarith)]
    linarith
  have h2eq : (2 : ℝ≥0∞) = ENNReal.ofReal (2 : ℝ) := (ENNReal.ofReal_ofNat 2).symm
  have hgain' : ∀ u v : ℤ → ℂ, eLpNorm (T u v) 1 Measure.count
      ≤ (M₀ : ℝ≥0∞) * eLpNorm u (ENNReal.ofReal 2) Measure.count
          * eLpNorm v (ENNReal.ofReal 2) Measure.count := by
    intro u v
    have h := hgain u v
    rw [h2eq] at h
    exact h
  have hV₃id : V₃ / (V₃ - 1) / (V₃ / (V₃ - 1) - 1) = V₃ := by
    have h1 : V₃ - 1 ≠ 0 := by intro h; linarith
    have h2 : V₃ / (V₃ - 1) - 1 ≠ 0 := by
      intro h
      have : V₃ / (V₃ - 1) = 1 := by linarith
      rw [div_eq_iff h1] at this
      linarith
    field_simp <;> ring
  have hloss' : ∀ u v : ℤ → ℂ,
      eLpNorm (T u v) (ENNReal.ofReal (V₃ / (V₃ - 1) / (V₃ / (V₃ - 1) - 1))) Measure.count
        ≤ (M₁ : ℝ≥0∞) * eLpNorm u (ENNReal.ofReal V₁) Measure.count
            * eLpNorm v (ENNReal.ofReal V₂) Measure.count := by
    intro u v
    rw [hV₃id]
    exact hloss u v
  have hsimple : ∀ f g : ℤ → ℂ, (Function.support f).Finite → (Function.support g).Finite →
      eLpNorm (T f g) (ENNReal.ofReal pr) Measure.count
        ≤ (M₀ : ℝ≥0∞) ^ (1 - θ) * (M₁ : ℝ≥0∞) ^ θ
          * eLpNorm f (ENNReal.ofReal x₁) Measure.count
          * eLpNorm g (ENNReal.ofReal x₂) Measure.count :=
    extend_interp (interpBound (p₀ := 2) (p₁ := V₁) (q₀ := 2) (q₁ := V₂)
      (r₁ := V₃ / (V₃ - 1)) (p := x₁) (q := x₂) (r := pr) (θ := θ)
      T hlin₁ hlin₂ (by norm_num) (lt_trans zero_lt_one hV₁) (by norm_num)
      (lt_trans zero_lt_one hV₂) hr₁ hx₁pos hx₂pos hpr
      hθ₀ hθ₁ hx₁rel hx₂rel hrθ hgain' hloss')
  intro f g hf hg
  exact extendToAllBdd T htend hsimple f g
    (boundedZ_of_memLp (ENNReal.one_lt_ofReal.mpr hx₁) hf)
    (boundedZ_of_memLp (ENNReal.one_lt_ofReal.mpr hx₂) hg) hf hg

/-- **Stein interpolation plus extension, degenerate case `pr = 1`.** -/
theorem interp_step_deg {T : (ℤ → ℂ) → (ℤ → ℂ) → (ℤ → ℂ)}
    (hlin₁ : ∀ (u u' v : ℤ → ℂ) (c : ℂ), BoundedZ u → BoundedZ u' → BoundedZ v →
      T (u + c • u') v = T u v + c • T u' v)
    (hlin₂ : ∀ (u v v' : ℤ → ℂ) (c : ℂ), BoundedZ u → BoundedZ v → BoundedZ v' →
      T u (v + c • v') = T u v + c • T u v')
    (htend : ∀ f g : ℤ → ℂ, BoundedZ f → BoundedZ g → ∀ x : ℤ,
      Filter.Tendsto (fun K' : ℕ => T (truncZ K' f) (truncZ K' g) x)
        Filter.atTop (nhds (T f g x)))
    {x₁ x₂ pr θ V₁ V₂ : ℝ} (hx₁ : 1 < x₁) (hx₂ : 1 < x₂)
    (hV₁ : 1 < V₁) (hV₂ : 1 < V₂) (hpr1 : pr = 1)
    (hθ₀ : 0 < θ) (hθ₁ : θ < 1)
    (hx₁rel : 1 / x₁ = (1 - θ) / 2 + θ / V₁)
    (hx₂rel : 1 / x₂ = (1 - θ) / 2 + θ / V₂)
    {M₀ M₁ : ℝ≥0}
    (hgain : ∀ u v : ℤ → ℂ, eLpNorm (T u v) 1 Measure.count
      ≤ (M₀ : ℝ≥0∞) * eLpNorm u 2 Measure.count * eLpNorm v 2 Measure.count)
    (hloss : ∀ u v : ℤ → ℂ, eLpNorm (T u v) 1 Measure.count
      ≤ (M₁ : ℝ≥0∞) * eLpNorm u (ENNReal.ofReal V₁) Measure.count
          * eLpNorm v (ENNReal.ofReal V₂) Measure.count) :
    ∀ f g : ℤ → ℂ, MemLp f (ENNReal.ofReal x₁) Measure.count →
      MemLp g (ENNReal.ofReal x₂) Measure.count →
      eLpNorm (T f g) (ENNReal.ofReal pr) Measure.count
        ≤ (M₀ : ℝ≥0∞) ^ (1 - θ) * (M₁ : ℝ≥0∞) ^ θ
          * eLpNorm f (ENNReal.ofReal x₁) Measure.count
          * eLpNorm g (ENNReal.ofReal x₂) Measure.count := by
  have hx₁pos : 0 < x₁ := lt_trans one_pos hx₁
  have hx₂pos : 0 < x₂ := lt_trans one_pos hx₂
  have h2eq : (2 : ℝ≥0∞) = ENNReal.ofReal (2 : ℝ) := (ENNReal.ofReal_ofNat 2).symm
  have hgain' : ∀ u v : ℤ → ℂ, eLpNorm (T u v) 1 Measure.count
      ≤ (M₀ : ℝ≥0∞) * eLpNorm u (ENNReal.ofReal 2) Measure.count
          * eLpNorm v (ENNReal.ofReal 2) Measure.count := by
    intro u v
    have h := hgain u v
    rw [h2eq] at h
    exact h
  have hsimple : ∀ f g : ℤ → ℂ, (Function.support f).Finite → (Function.support g).Finite →
      eLpNorm (T f g) (ENNReal.ofReal pr) Measure.count
        ≤ (M₀ : ℝ≥0∞) ^ (1 - θ) * (M₁ : ℝ≥0∞) ^ θ
          * eLpNorm f (ENNReal.ofReal x₁) Measure.count
          * eLpNorm g (ENNReal.ofReal x₂) Measure.count := by
    intro f g hf hg
    rw [hpr1, ENNReal.ofReal_one]
    exact interpBoundOne (p₀ := 2) (p₁ := V₁) (q₀ := 2) (q₁ := V₂) (p := x₁) (q := x₂)
      (θ := θ) T hlin₁ hlin₂ (by norm_num) (lt_trans zero_lt_one hV₁) (by norm_num)
      (lt_trans zero_lt_one hV₂) hx₁pos hx₂pos hθ₀ hθ₁
      hx₁rel hx₂rel hgain' hloss f g hf hg
  intro f g hf hg
  exact extendToAllBdd T htend hsimple f g
    (boundedZ_of_memLp (ENNReal.one_lt_ofReal.mpr hx₁) hf)
    (boundedZ_of_memLp (ENNReal.one_lt_ofReal.mpr hx₂) hg) hf hg

/-- **The weight absorption of the interpolated constant.** -/
theorem weight_chain {θ : ℝ} (hθ₀ : 0 < θ) (hθ₁ : θ < 1)
    {L : ℕ} {A Ca : ℝ≥0} (hA : 1 ≤ A) {Cg M₁ w : ℝ≥0} {H : ℝ≥0∞}
    (hCg : Cg ≤ A * angleBracket L ^ 2) (hM₁ : M₁ ≤ A * angleBracket L ^ 2)
    (habs : (w : ℝ≥0∞) ^ (1 - θ) * ((angleBracket L : ℝ≥0) : ℝ≥0∞) ^ 2
      ≤ (Ca : ℝ≥0∞) * H) :
    (Cg * w : ℝ≥0∞) ^ (1 - θ) * (M₁ : ℝ≥0∞) ^ θ ≤ ((A * Ca : ℝ≥0) : ℝ≥0∞) * H := by
  calc (Cg * w : ℝ≥0∞) ^ (1 - θ) * (M₁ : ℝ≥0∞) ^ θ
      ≤ (A : ℝ≥0∞) * (w : ℝ≥0∞) ^ (1 - θ)
          * ((angleBracket L : ℝ≥0) : ℝ≥0∞) ^ 2 :=
        gainLoss_combine_sq (A := A) hθ₀ hθ₁ hA hCg hM₁
    _ = (A : ℝ≥0∞) * ((w : ℝ≥0∞) ^ (1 - θ)
          * ((angleBracket L : ℝ≥0) : ℝ≥0∞) ^ 2) := by ring
    _ ≤ (A : ℝ≥0∞) * ((Ca : ℝ≥0∞) * H) := mul_le_mul_of_nonneg_left habs (by positivity)
    _ = ((A * Ca : ℝ≥0) : ℝ≥0∞) * H := by rw [ENNReal.coe_mul]; ring

/-! ## Linearity of the minor-arc parts on bounded functions -/

theorem minorArc₁_linear_left (ρ : ℝ) (L : ℕ) (K : ℤ) (N : ℝ≥0) (P : Polynomial ℤ)
    (u u' v : ℤ → ℂ) (c : ℂ) (hu : BoundedZ u) (hu' : BoundedZ u') (hv : BoundedZ v) :
    minorArc₁ ρ L K N P (u + c • u') v
      = minorArc₁ ρ L K N P u v + c • minorArc₁ ρ L K N P u' v := by
  have hproj : kmtProj ρ L K (u + c • u')
      = kmtProj ρ L K u + c • kmtProj ρ L K u' := by
    rw [kmtProj_add_bounded ρ L K hu (boundedZ_smul c hu'), kmtProj_smul_bounded ρ L K c hu']
  have hsub : (u + c • u') - kmtProj ρ L K (u + c • u')
      = (u - kmtProj ρ L K u) + c • (u' - kmtProj ρ L K u') := by
    rw [hproj]
    funext x
    simp only [Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
    ring
  simp only [minorArc₁, hsub]
  rw [AhalfR_add_left', AhalfR_smul_left']

theorem minorArc₁_linear_right (ρ : ℝ) (L : ℕ) (K : ℤ) (N : ℝ≥0) (P : Polynomial ℤ)
    (u v v' : ℤ → ℂ) (c : ℂ) (hu : BoundedZ u) (hv : BoundedZ v) (hv' : BoundedZ v') :
    minorArc₁ ρ L K N P u (v + c • v')
      = minorArc₁ ρ L K N P u v + c • minorArc₁ ρ L K N P u v' := by
  simp only [minorArc₁]
  rw [AhalfR_add_right', AhalfR_smul_right']

theorem minorArc₂_linear_left (ρ : ℝ) (L : ℕ) (K K₂ : ℤ) (N : ℝ≥0) (P : Polynomial ℤ)
    (u u' v : ℤ → ℂ) (c : ℂ) (hu : BoundedZ u) (hu' : BoundedZ u') (hv : BoundedZ v) :
    minorArc₂ ρ L K K₂ N P (u + c • u') v
      = minorArc₂ ρ L K K₂ N P u v + c • minorArc₂ ρ L K K₂ N P u' v := by
  have hproj : kmtProj ρ L K (u + c • u')
      = kmtProj ρ L K u + c • kmtProj ρ L K u' := by
    rw [kmtProj_add_bounded ρ L K hu (boundedZ_smul c hu'), kmtProj_smul_bounded ρ L K c hu']
  simp only [minorArc₂, hproj]
  rw [AhalfR_add_left', AhalfR_smul_left']

theorem minorArc₂_linear_right (ρ : ℝ) (L : ℕ) (K K₂ : ℤ) (N : ℝ≥0) (P : Polynomial ℤ)
    (u v v' : ℤ → ℂ) (c : ℂ) (hu : BoundedZ u) (hv : BoundedZ v) (hv' : BoundedZ v') :
    minorArc₂ ρ L K K₂ N P u (v + c • v')
      = minorArc₂ ρ L K K₂ N P u v + c • minorArc₂ ρ L K K₂ N P u v' := by
  have hproj : kmtProj ρ L K₂ (v + c • v')
      = kmtProj ρ L K₂ v + c • kmtProj ρ L K₂ v' := by
    rw [kmtProj_add_bounded ρ L K₂ hv (boundedZ_smul c hv'),
      kmtProj_smul_bounded ρ L K₂ c hv']
  have hsub : (v + c • v') - kmtProj ρ L K₂ (v + c • v')
      = (v - kmtProj ρ L K₂ v) + c • (v' - kmtProj ρ L K₂ v') := by
    rw [hproj]
    funext x
    simp only [Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
    ring
  simp only [minorArc₂, hsub]
  rw [AhalfR_add_right', AhalfR_smul_right']

/-! ## Pointwise convergence of the truncations -/

theorem minorArc₁_tendsto (ρ : ℝ) (L : ℕ) (K : ℤ) (N : ℝ≥0) (P : Polynomial ℤ) :
    ∀ f g : ℤ → ℂ, BoundedZ f → BoundedZ g → ∀ x : ℤ,
      Filter.Tendsto (fun K' : ℕ => minorArc₁ ρ L K N P (truncZ K' f) (truncZ K' g) x)
        Filter.atTop (nhds (minorArc₁ ρ L K N P f g x)) :=
  fun f g hf hg x => (minorArc_tendsto_truncZ ρ L K K N P hf hg x).2.2.1

theorem minorArc₂_tendsto (ρ : ℝ) (L : ℕ) (K K₂ : ℤ) (N : ℝ≥0) (P : Polynomial ℤ) :
    ∀ f g : ℤ → ℂ, BoundedZ f → BoundedZ g → ∀ x : ℤ,
      Filter.Tendsto (fun K' : ℕ => minorArc₂ ρ L K K₂ N P (truncZ K' f) (truncZ K' g) x)
        Filter.atTop (nhds (minorArc₂ ρ L K K₂ N P f g x)) :=
  fun f g hf hg x => (minorArc_tendsto_truncZ ρ L K K₂ N P hf hg x).2.2.2

/-! ## Rewriting the `ofReal` constants produced by the projection bounds -/

theorem ofReal_coe_mul_angleBracket (C : ℝ≥0) (l : ℕ) :
    ENNReal.ofReal (C : ℝ) * ENNReal.ofReal (angleBracket l : ℝ)
      = ((C * angleBracket l : ℝ≥0) : ℝ≥0∞) := by
  rw [ENNReal.ofReal_coe_nnreal, ENNReal.ofReal_coe_nnreal, ← ENNReal.coe_mul]

/-- The `2`-exponent conversion for the count measure. -/
theorem ofReal_two : ENNReal.ofReal (2 : ℝ) = (2 : ℝ≥0∞) := ENNReal.ofReal_ofNat 2

/-! ## `NNReal` arithmetic for the constants -/

theorem one_add_mul_le_mul_one_add (c B : ℝ≥0) (hB : 1 ≤ B) : 1 + c * B ≤ (1 + c) * B := by
  rw [← NNReal.coe_le_coe]
  push_cast
  nlinarith [show (1 : ℝ) ≤ (B : ℝ) from by exact_mod_cast hB]

theorem le_sq_of_one_le (B : ℝ≥0) (hB : 1 ≤ B) : B ≤ B ^ 2 := by
  rw [← NNReal.coe_le_coe]
  push_cast
  nlinarith [show (1 : ℝ) ≤ (B : ℝ) from by exact_mod_cast hB]

theorem mul_le_mul_sq (c B : ℝ≥0) (hB : 1 ≤ B) : c * B ≤ c * B ^ 2 :=
  mul_le_mul_of_nonneg_left (le_sq_of_one_le B hB) bot_le

theorem mul_sq_le_mul_sq (c d B : ℝ≥0) (h : c ≤ d) : c * B ^ 2 ≤ d * B ^ 2 :=
  mul_le_mul_of_nonneg_right h (by positivity)

/-! ## The main theorem -/

/-- **Area A5**: the minor-arc input (B) of §4 for the concrete projections `kmtPj ρ`, from
area A1 and `ImprovKMT`. -/
theorem areaA5_aux : Work.KMTContract.AreaA5 := by
  intro P p₁ p₂ hdeg hp₁ hp₁top hp₂ hp₂top hsum hA1 hImp
  obtain ⟨cImp, hcImp, hCrhoImp⟩ := hImp
  set x₁ : ℝ := p₁.toReal with hx₁def
  set x₂ : ℝ := p₂.toReal with hx₂def
  have hp₁ne : p₁ ≠ ⊤ := ne_of_lt hp₁top
  have hp₂ne : p₂ ≠ ⊤ := ne_of_lt hp₂top
  have hp₁eq : ENNReal.ofReal x₁ = p₁ := by rw [hx₁def]; exact ENNReal.ofReal_toReal hp₁ne
  have hp₂eq : ENNReal.ofReal x₂ = p₂ := by rw [hx₂def]; exact ENNReal.ofReal_toReal hp₂ne
  have hp₁pos0 : 0 < p₁ := lt_trans one_pos hp₁
  have hp₂pos0 : 0 < p₂ := lt_trans one_pos hp₂
  have hx₁ : 1 < x₁ := by
    rw [hx₁def, ← ENNReal.toReal_one]
    exact (ENNReal.toReal_lt_toReal ENNReal.one_ne_top hp₁ne).mpr hp₁
  have hx₂ : 1 < x₂ := by
    rw [hx₂def, ← ENNReal.toReal_one]
    exact (ENNReal.toReal_lt_toReal ENNReal.one_ne_top hp₂ne).mpr hp₂
  have hx₁pos : 0 < x₁ := lt_trans one_pos hx₁
  have hx₂pos : 0 < x₂ := lt_trans one_pos hx₂
  have hsum' : 1 / x₁ + 1 / x₂ ≤ 1 := by
    have h1 : (p₁⁻¹ + p₂⁻¹).toReal ≤ (1 : ENNReal).toReal :=
      ENNReal.toReal_mono ENNReal.one_ne_top hsum
    rw [ENNReal.toReal_one] at h1
    have h2 : (p₁⁻¹ + p₂⁻¹).toReal = x₁⁻¹ + x₂⁻¹ := by
      rw [ENNReal.toReal_add (ENNReal.inv_ne_top.mpr hp₁pos0.ne')
            (ENNReal.inv_ne_top.mpr hp₂pos0.ne'),
        ENNReal.toReal_inv, ENNReal.toReal_inv, ← hx₁def, ← hx₂def]
    rw [h2] at h1
    rw [one_div, one_div]
    exact h1
  obtain ⟨θ, V₁, V₂, V₃, hθ0, hθ1, hV₁, hV₂, hV₃pos, hV₁inv, hV₂inv, hV₃inv,
    hVrel, hx₁rel, hx₂rel, hsumrel, hθV₃⟩ := thetaSetup hx₁ hx₂ hsum'
  have hV₁pos : 0 < V₁ := lt_trans zero_lt_one hV₁
  have hV₂pos : 0 < V₂ := lt_trans zero_lt_one hV₂
  set pr : ℝ := (1 / x₁ + 1 / x₂)⁻¹ with hprdef
  have hprpos : 0 < pr := by rw [hprdef]; exact inv_pos.mpr (by positivity)
  have hprinv : 1 / pr = 1 / x₁ + 1 / x₂ := by rw [hprdef, one_div, inv_inv]
  have hpr1 : 1 ≤ pr := by
    rw [hprdef]
    exact (one_le_inv₀ (by positivity)).mpr hsum'
  have hexp : (p₁⁻¹ + p₂⁻¹)⁻¹ = ENNReal.ofReal pr := by
    have h1 : p₁⁻¹ = ENNReal.ofReal x₁⁻¹ := by
      rw [← hp₁eq, ENNReal.ofReal_inv_of_pos hx₁pos]
    have h2 : p₂⁻¹ = ENNReal.ofReal x₂⁻¹ := by
      rw [← hp₂eq, ENNReal.ofReal_inv_of_pos hx₂pos]
    have h3 : 0 < x₁⁻¹ + x₂⁻¹ := by positivity
    rw [h1, h2, ← ENNReal.ofReal_add (by positivity) (by positivity),
      ← ENNReal.ofReal_inv_of_pos h3, ENNReal.ofReal_eq_ofReal_iff (by positivity) (by positivity)]
    rw [hprdef]
    congr 1
    ring
  have hdenpos : 0 < cImp * (1 - θ) := mul_pos hcImp (by linarith)
  refine ⟨max 1 (Nat.ceil (10 / (cImp * (1 - θ))) + 1), ?_⟩
  intro C₀ hC₀
  have hC₀1 : 1 ≤ C₀ := le_trans (le_max_left _ _) hC₀
  have hC₀pos : (0 : ℝ) < C₀ := by exact_mod_cast (lt_of_lt_of_le zero_lt_one hC₀1)
  have hC₀big : 10 < cImp * (C₀ : ℝ) * (1 - θ) := by
    have h1 : Nat.ceil (10 / (cImp * (1 - θ))) < C₀ := by
      have := le_trans (le_max_right (1:ℕ) (Nat.ceil (10 / (cImp * (1 - θ))) + 1)) hC₀
      omega
    have h2 : (10 : ℝ) / (cImp * (1 - θ)) < (C₀ : ℝ) := by
      refine lt_of_le_of_lt (Nat.le_ceil _) ?_
      exact_mod_cast h1
    have := (div_lt_iff₀ hdenpos).mp h2
    nlinarith
  refine ⟨min 1 (min (cImp * (1 - θ) / 11) (1 / (2 * (C₀ : ℝ)))), ?_, ?_⟩
  · positivity
  intro ρ hρ0 hρρ₀
  have hρ1 : ρ ≤ 1 := le_trans hρρ₀ (min_le_left _ _)
  have hρsmall : 10 * ρ < cImp * (1 - θ) := by
    have h2 : ρ ≤ cImp * (1 - θ) / 11 :=
      le_trans hρρ₀ (le_trans (min_le_right _ _) (min_le_left _ _))
    linarith
  have hρC₀ : ρ * (C₀ : ℝ) < 1 := by
    have h2 : ρ ≤ 1 / (2 * (C₀ : ℝ)) :=
      le_trans hρρ₀ (le_trans (min_le_right _ _) (min_le_right _ _))
    have h3 : ρ * (C₀ : ℝ) ≤ (1 / (2 * (C₀ : ℝ))) * (C₀ : ℝ) :=
      mul_le_mul_of_nonneg_right h2 hC₀pos.le
    have h4 : (1 / (2 * (C₀ : ℝ))) * (C₀ : ℝ) = 1 / 2 := by field_simp
    linarith
  -- the constants
  obtain ⟨Cimp, hbound⟩ := hCrhoImp ρ hρ0 hρ1
  obtain ⟨Cρ2, hCρ2pos, C2₀, hC2₀pos, hb2⟩ :=
    kmtProj_lp_bound_A1 hA1 hρ0 hρ1 (p := 2) (by norm_num)
  obtain ⟨CρV1, hCρV1pos, CV1₀, hCV1₀pos, hbV1⟩ :=
    kmtProj_lp_bound_A1 hA1 hρ0 hρ1 (p := V₁) hV₁
  obtain ⟨CρV2, hCρV2pos, CV2₀, hCV2₀pos, hbV2⟩ :=
    kmtProj_lp_bound_A1 hA1 hρ0 hρ1 (p := V₂) hV₂
  obtain ⟨CρNA, hCρNApos, hNA⟩ := iwNonAliasing_of_goodMajorArcsConstant hρ0
  set Cρ : ℝ := max (max (max Cρ2 CρV1) CρV2) CρNA with hCρdef
  have hCρpos : 0 < Cρ :=
    lt_of_lt_of_le hCρ2pos
      (le_trans (le_max_left _ _) (le_trans (le_max_left _ _) (le_max_left _ _)))
  have hgc2 : ∀ l k, GoodMajorArcs ρ Cρ l k → GoodMajorArcs ρ Cρ2 l k :=
    fun l k h => goodMajorArcs_mono
      (le_trans (le_max_left _ _) (le_trans (le_max_left _ _) (le_max_left _ _))) h
  have hgcV1 : ∀ l k, GoodMajorArcs ρ Cρ l k → GoodMajorArcs ρ CρV1 l k :=
    fun l k h => goodMajorArcs_mono
      (le_trans (le_max_right _ _) (le_trans (le_max_left _ _) (le_max_left _ _))) h
  have hgcV2 : ∀ l k, GoodMajorArcs ρ Cρ l k → GoodMajorArcs ρ CρV2 l k :=
    fun l k h => goodMajorArcs_mono (le_trans (le_max_right _ _) (le_max_left _ _)) h
  have hgcNA : ∀ l k, GoodMajorArcs ρ Cρ l k → NonAliasing k (iwArithFreqs ρ l) :=
    fun l k h => hNA l k (goodMajorArcs_mono (le_max_right _ _) h)
  obtain ⟨n₀, hn₀1, hn₀⟩ := goodMajorArcs_eventually hC₀1 hρ0 hCρpos hρC₀
  obtain ⟨Cc₁, hCc₁⟩ := kmtProj_crude_lp (ρ := ρ) hx₁ C₀ n₀ P.natDegree
  obtain ⟨Cc₂, hCc₂⟩ := kmtProj_crude_lp (ρ := ρ) hx₂ C₀ n₀ P.natDegree
  obtain ⟨Kw, hKwpos, hKw⟩ := heightWeight_floor_le
  set cw : ℝ≥0 := heightWeight 10 (n₀ : ℝ≥0) with hcwdef
  have hcwpos : 0 < cw := by rw [hcwdef]; exact heightWeight_pos 10 _
  obtain ⟨Ca, hCa⟩ := absorbWeightStrict hcImp hθ0 hθ1 hρ0 (P := (2 : ℝ)) (by norm_num)
    hC₀big hρsmall
  set A1c : ℝ≥0 := (Cimp + 1) * (1 + C2₀) with hA1c
  set A2c : ℝ≥0 := C2₀ * ((Cimp + 1) * (1 + C2₀)) with hA2c
  set A5c : ℝ≥0 := max (1 + CV1₀) (CV1₀ * (1 + CV2₀)) with hA5c
  set Acomb : ℝ≥0 := max 1 (max A1c (max A2c A5c)) with hAcombdef
  have hAcomb1 : 1 ≤ Acomb := le_max_left _ _
  have hA1cle : A1c ≤ Acomb :=
    le_trans (le_max_left A1c (max A2c A5c)) (le_max_right 1 (max A1c (max A2c A5c)))
  have hA2cle : A2c ≤ Acomb :=
    le_trans (le_max_left A2c A5c) (le_trans (le_max_right A1c (max A2c A5c))
      (le_max_right 1 (max A1c (max A2c A5c))))
  have hA5cle : A5c ≤ Acomb :=
    le_trans (le_max_right A2c A5c) (le_trans (le_max_right A1c (max A2c A5c))
      (le_max_right 1 (max A1c (max A2c A5c))))
  set Csmall : ℝ≥0 :=
    max ((1 : ℝ≥0) + (Cc₁ + 1)) ((Cc₁ + 1) * ((1 : ℝ≥0) + (Cc₂ + 1))) with hCsmalldef
  set Clarge : ℝ≥0 := Acomb * (Ca * Kw) with hClargedef
  set Cf : ℝ≥0 := max 1 (max Clarge (Csmall * Kw * cw⁻¹)) with hCfdef
  have hCfpos : 0 < Cf := lt_of_lt_of_le zero_lt_one (le_max_left _ _)
  have hClargele : Clarge ≤ Cf := le_trans (le_max_left _ _) (le_max_right _ _)
  have hCsmallle : Csmall * Kw * cw⁻¹ ≤ Cf := le_trans (le_max_right _ _) (le_max_right _ _)
  -- scale-independent facts
  have hV₃le : (1 : ℝ) ≤ V₃ := by
    have hnum : 1 / x₁ + 1 / x₂ - (1 - θ) ≤ θ := by linarith
    have h1 : 1 / V₃ ≤ 1 := by
      rw [hV₃inv, div_le_one hθ0]
      exact hnum
    have := (div_le_iff₀ hV₃pos).mp h1
    simpa using this
  have hrelV : (ENNReal.ofReal V₁)⁻¹ + (ENNReal.ofReal V₂)⁻¹ = (ENNReal.ofReal V₃)⁻¹ := by
    rw [← ENNReal.ofReal_inv_of_pos hV₁pos, ← ENNReal.ofReal_inv_of_pos hV₂pos,
      ← ENNReal.ofReal_inv_of_pos hV₃pos,
      ← ENNReal.ofReal_add (by positivity) (by positivity),
      ENNReal.ofReal_eq_ofReal_iff (by positivity) (by positivity)]
    simpa only [one_div] using hVrel.symm
  -- the per-scale estimate for each of the two minor arc parts
  have key₁ : ∀ (N : ℝ≥0) (f g : ℤ → ℂ), 1 ≤ N →
      eLpNorm (minorArc₁ ρ (heightScale C₀ (Nat.floor N))
        (-(logN (Nat.floor N)) + (heightScale C₀ (Nat.floor N) : ℤ)) N P f g)
        (ENNReal.ofReal pr) Measure.count
        ≤ (Cf : ℝ≥0∞) * (heightWeight 10 N : ℝ≥0∞) * eLpNorm f p₁ Measure.count * eLpNorm g p₂ Measure.count := by
    intro N f g hN
    set n : ℕ := Nat.floor N with hndef
    set L : ℕ := heightScale C₀ n with hLdef
    set K : ℤ := -(logN n) + (L : ℤ) with hKdef
    set K₂ : ℤ := -((P.natDegree : ℤ) * logN n) + (P.natDegree : ℤ) * (L : ℤ) with hK₂def
    have hNn : 1 ≤ n := by
      rw [hndef]
      exact Nat.le_floor (by exact_mod_cast hN : ((1 : ℕ) : ℝ≥0) ≤ N)
    have hL1 : 1 ≤ L := by
      rw [hLdef]
      exact Nat.succ_le_of_lt (Nat.mul_pos (lt_of_lt_of_le zero_lt_one hC₀1)
        (Work.Analysis.EndVar.logLogN_pos n))
    have hMne : (Cf : ℝ≥0∞) * (heightWeight 10 N : ℝ≥0∞) ≠ 0 :=
      mul_ne_zero (ENNReal.coe_ne_zero.mpr hCfpos.ne')
        (ENNReal.coe_ne_zero.mpr (heightWeight_pos 10 N).ne')
    refine (endpoint_trivial (fun u v => minorArc₁ ρ L K N P u v) hMne hp₁pos0.ne'
      hp₂pos0.ne' (fun v => minorArc₁_zero_left ρ L K N P v)
      (fun u => minorArc₁_zero_right ρ L K N P u) ?_) f g
    · intro u v hu hv
      rw [← hp₁eq, ← hp₂eq] at ⊢
      rw [← hp₁eq] at hu
      rw [← hp₂eq] at hv
      have hum : MemLp u (ENNReal.ofReal x₁) Measure.count :=
        MeasureTheory.memLp_iff.mpr hu
      have hvm : MemLp v (ENNReal.ofReal x₂) Measure.count :=
        MeasureTheory.memLp_iff.mpr hv
      by_cases hsl : n < n₀
      · -- small scale
        have hnle : n ≤ n₀ := le_of_lt hsl
        have hcr1 := hCc₁ n hnle
        have hcr2 := hCc₂ n hnle
        have hprojx₁K : ∀ w : ℤ → ℂ,
            eLpNorm (kmtProj ρ L K w) (ENNReal.ofReal x₁) Measure.count
              ≤ ((Cc₁ + 1 : ℝ≥0) : ℝ≥0∞) * eLpNorm w (ENNReal.ofReal x₁) Measure.count := by
          intro w
          have h := (hcr1 w).1
          rw [← hLdef, ← hKdef] at h
          exact h.trans (mul_le_mul'
            (ENNReal.coe_le_coe.mpr (le_add_of_nonneg_right bot_le)) le_rfl)
        have hkey : x₁⁻¹ + x₂⁻¹ = pr⁻¹ := by
          have h := hprinv
          simp only [one_div] at h
          exact h.symm
        have hrelx : (ENNReal.ofReal x₁)⁻¹ + (ENNReal.ofReal x₂)⁻¹
            = (ENNReal.ofReal pr)⁻¹ := by
          rw [← ENNReal.ofReal_inv_of_pos hx₁pos, ← ENNReal.ofReal_inv_of_pos hx₂pos,
            ← ENNReal.ofReal_inv_of_pos hprpos,
            ← ENNReal.ofReal_add (by positivity) (by positivity),
            ENNReal.ofReal_eq_ofReal_iff (by positivity) (by positivity)]
          exact hkey
        have hloss1 := lossEndpoint₁ (ρ := ρ) (L := L) (K := K) (N := N) (P := P)
          (V₁ := x₁) (V₂ := x₂) (V₃ := pr) hx₁ hx₂ hpr1 hrelx hprojx₁K
        have hcwle : (cw : ℝ≥0) ≤ heightWeight 10 (Nat.floor N : ℝ≥0) := by
          rw [hcwdef]
          exact heightWeight_antitone 10 (by norm_num)
            (by exact_mod_cast (Nat.le_of_lt hsl))
        have hcwh : (cw : ℝ≥0) ≤ Kw * heightWeight 10 N :=
          hcwle.trans (hKw N (by exact_mod_cast hN : 1 ≤ N))
        have hKh : (Csmall : ℝ≥0) ≤ Cf * heightWeight 10 N := by
          have h1 : Csmall * Kw ≤ Cf * cw := by
            have h := mul_le_mul_of_nonneg_right hCsmallle hcwpos.le
            rwa [mul_assoc, inv_mul_cancel₀ hcwpos.ne', mul_one] at h
          have h2 : Cf * cw ≤ Cf * (heightWeight 10 N * Kw) :=
            mul_le_mul_of_nonneg_left (by rw [mul_comm]; exact hcwh) bot_le
          have h3 : Cf * (heightWeight 10 N * Kw) = (Cf * heightWeight 10 N) * Kw := by
            rw [mul_assoc]
          exact le_of_mul_le_mul_right (h1.trans (h3 ▸ h2)) hKwpos
        have hconst : ((1 : ℝ≥0) + (Cc₁ + 1) : ℝ≥0∞)
            ≤ (Cf : ℝ≥0∞) * (heightWeight 10 N : ℝ≥0∞) :=
          ENNReal.coe_le_coe.mpr ((le_max_left _ _).trans hKh)
        exact (hloss1 u v).trans (mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_right hconst (by positivity)) (by positivity))
      · -- large scale
        have hlge : n₀ ≤ n := le_of_not_gt hsl
        have hgoodK : GoodMajorArcs ρ Cρ L K := by
          show ((K : ℤ) : ℝ) ≤ -Cρ * (2 : ℝ) ^ (ρ * ((L : ℕ) : ℝ))
          rw [hKdef, hLdef]
          have h := hn₀ n hlge
          push_cast
          linarith
        have hKle : K ≤ -1 := by
          rw [hKdef, hLdef]
          have h := hn₀ n hlge
          have hpos : (0 : ℝ) ≤ Cρ * (2 : ℝ) ^ (ρ * ((heightScale C₀ n : ℕ) : ℝ)) := by
            have hp := Real.rpow_pos_of_pos (by norm_num : (0 : ℝ) < 2)
              (ρ * ((heightScale C₀ n : ℕ) : ℝ))
            positivity
          have h2 : (((-(logN n) + ((heightScale C₀ n : ℕ) : ℤ)) : ℤ) : ℝ) ≤ -1 := by
            push_cast
            linarith
          exact_mod_cast h2
        have hK₂le : K₂ ≤ -1 := by
          have hd1 : (1 : ℤ) ≤ (P.natDegree : ℤ) := by
            have := hdeg
            omega
          have hEq : K₂ = (P.natDegree : ℤ) * K := by rw [hK₂def, hKdef]; ring
          rw [hEq]
          calc (P.natDegree : ℤ) * K ≤ 1 * K := mul_le_mul_of_nonpos_right hd1 (by omega : K ≤ 0)
            _ = K := one_mul K
            _ ≤ -1 := hKle
        have hgoodK₂ : GoodMajorArcs ρ Cρ L K₂ := by
          show ((K₂ : ℤ) : ℝ) ≤ -Cρ * (2 : ℝ) ^ (ρ * ((L : ℕ) : ℝ))
          have hEq : K₂ = (P.natDegree : ℤ) * K := by rw [hK₂def, hKdef]; ring
          rw [hEq]
          push_cast
          have hK0 : ((K : ℤ) : ℝ) ≤ 0 := by
            have h : ((K : ℤ) : ℝ) ≤ -Cρ * (2 : ℝ) ^ (ρ * ((L : ℕ) : ℝ)) := hgoodK
            have h2 : -Cρ * (2 : ℝ) ^ (ρ * ((L : ℕ) : ℝ)) ≤ 0 := by
              have := Real.rpow_pos_of_pos (by norm_num : (0 : ℝ) < 2) (ρ * ((L : ℕ) : ℝ))
              nlinarith [hCρpos, this]
            linarith
          have hd1 : (1 : ℝ) ≤ (P.natDegree : ℝ) := by
            have := hdeg
            exact_mod_cast (show 1 ≤ P.natDegree by omega)
          calc ((P.natDegree : ℤ) : ℝ) * ((K : ℤ) : ℝ) ≤ 1 * ((K : ℤ) : ℝ) :=
                mul_le_mul_of_nonpos_right hd1 hK0
            _ = ((K : ℤ) : ℝ) := one_mul _
            _ ≤ -Cρ * (2 : ℝ) ^ (ρ * ((L : ℕ) : ℝ)) := hgoodK
        have hC₂₂ : ∀ w : ℤ → ℂ, eLpNorm (kmtProj ρ L K w) 2 Measure.count
            ≤ ((C2₀ * angleBracket L : ℝ≥0) : ℝ≥0∞) * eLpNorm w 2 Measure.count := by
          intro w
          have h := hb2 L K (hgc2 L K hgoodK) w
          rwa [ofReal_coe_mul_angleBracket, ofReal_two] at h
        have hC₂₃ : ∀ w : ℤ → ℂ, eLpNorm (kmtProj ρ L K₂ w) 2 Measure.count
            ≤ ((C2₀ * angleBracket L : ℝ≥0) : ℝ≥0∞) * eLpNorm w 2 Measure.count := by
          intro w
          have h := hb2 L K₂ (hgc2 L K₂ hgoodK₂) w
          rwa [ofReal_coe_mul_angleBracket, ofReal_two] at h
        have hCV₁ : ∀ w : ℤ → ℂ, eLpNorm (kmtProj ρ L K w) (ENNReal.ofReal V₁) Measure.count
            ≤ ((CV1₀ * angleBracket L : ℝ≥0) : ℝ≥0∞)
                * eLpNorm w (ENNReal.ofReal V₁) Measure.count := by
          intro w
          have h := hbV1 L K (hgcV1 L K hgoodK) w
          rwa [ofReal_coe_mul_angleBracket] at h
        have hcomp₁ : ∀ w : ℤ → ℂ, BoundedZ w →
            kmtProj ρ (L - 1) (K - 1) (w - kmtProj ρ L K w) = 0 :=
          fun w hw => kmtProj_sub_comp_eq_zero ρ hρ0 hρ1 (Nat.sub_le L 1) (by omega) hKle
            (hgcNA L K hgoodK) hw
        have hcomp₂ : ∀ w : ℤ → ℂ, BoundedZ w →
            kmtProj ρ (L - 1) (K₂ - (P.natDegree : ℤ)) (w - kmtProj ρ L K₂ w) = 0 :=
          fun w hw => kmtProj_sub_comp_eq_zero ρ hρ0 hρ1 (Nat.sub_le L 1) (by omega) hK₂le
            (hgcNA L K₂ hgoodK₂) hw
        obtain ⟨hgain₁, _⟩ := gainEndpoint_explicit (P := P) (ρ := ρ) (c := cImp) hcImp
          (Cimp := Cimp) hbound (N := n) hNn (L := L) hL1 (K := K) (K₂ := K₂)
          hKdef hK₂def hcomp₁ hcomp₂ hC₂₂ hC₂₃
        have hone : ∀ c : ℝ≥0, 1 + c * angleBracket L ≤ (1 + c) * angleBracket L :=
          fun c => one_add_mul_le_mul_one_add c (angleBracket L) (one_le_angleBracket L)
        have hCg₁le : (Cimp + 1) * (1 + C2₀ * angleBracket L) ≤ Acomb * angleBracket L ^ 2 := by
          calc (Cimp + 1) * (1 + C2₀ * angleBracket L)
              ≤ (Cimp + 1) * ((1 + C2₀) * angleBracket L) :=
                mul_le_mul_of_nonneg_left (hone C2₀) (by positivity)
            _ = A1c * angleBracket L := by rw [hA1c]; ring
            _ ≤ A1c * angleBracket L ^ 2 := mul_le_mul_sq A1c (angleBracket L) (one_le_angleBracket L)
            _ ≤ Acomb * angleBracket L ^ 2 := mul_sq_le_mul_sq A1c Acomb (angleBracket L) hA1cle
        have hM₁le : max ((1 : ℝ≥0) + CV1₀ * angleBracket L)
            ((CV1₀ * angleBracket L) * (1 + CV2₀ * angleBracket L))
            ≤ Acomb * angleBracket L ^ 2 := by
          refine max_le ?_ ?_
          · calc (1 : ℝ≥0) + CV1₀ * angleBracket L ≤ (1 + CV1₀) * angleBracket L :=
                  one_add_mul_le_mul_one_add CV1₀ (angleBracket L) (one_le_angleBracket L)
              _ ≤ (1 + CV1₀) * angleBracket L ^ 2 :=
                  mul_le_mul_sq (1 + CV1₀) (angleBracket L) (one_le_angleBracket L)
              _ ≤ A5c * angleBracket L ^ 2 := mul_sq_le_mul_sq _ A5c _ (le_max_left _ _)
              _ ≤ Acomb * angleBracket L ^ 2 := mul_sq_le_mul_sq _ Acomb _ hA5cle
          · calc (CV1₀ * angleBracket L) * (1 + CV2₀ * angleBracket L)
                ≤ (CV1₀ * angleBracket L) * ((1 + CV2₀) * angleBracket L) :=
                  mul_le_mul_of_nonneg_left (hone CV2₀) (by positivity)
              _ = (CV1₀ * (1 + CV2₀)) * angleBracket L ^ 2 := by ring
              _ ≤ A5c * angleBracket L ^ 2 := mul_sq_le_mul_sq _ A5c _ (le_max_right _ _)
              _ ≤ Acomb * angleBracket L ^ 2 := mul_sq_le_mul_sq _ Acomb _ hA5cle
        have habs : (improvWeight cImp ρ L n : ℝ≥0∞) ^ (1 - θ)
              * ((angleBracket L : ℝ≥0) : ℝ≥0∞) ^ 2
            ≤ ((Ca * Kw : ℝ≥0) : ℝ≥0∞) * (heightWeight 10 N : ℝ≥0∞) := by
          rw [← ENNReal.rpow_natCast ((angleBracket L : ℝ≥0) : ℝ≥0∞) 2, hLdef]
          refine (hCa n hNn).trans ?_
          have hfl := hKw N (by exact_mod_cast hN : 1 ≤ N)
          rw [← hndef] at hfl
          calc (Ca : ℝ≥0∞) * (heightWeight 10 (n : ℝ≥0) : ℝ≥0∞)
              ≤ (Ca : ℝ≥0∞) * ((Kw * heightWeight 10 N : ℝ≥0) : ℝ≥0∞) :=
                mul_le_mul_of_nonneg_left (ENNReal.coe_le_coe.mpr hfl) (by positivity)
            _ = ((Ca * Kw : ℝ≥0) : ℝ≥0∞) * (heightWeight 10 N : ℝ≥0∞) := by
                rw [ENNReal.coe_mul, ENNReal.coe_mul, mul_assoc]
        have hlossV : ∀ w w' : ℤ → ℂ,
            eLpNorm (minorArc₁ ρ L K (n : ℝ≥0) P w w') (ENNReal.ofReal V₃) Measure.count
              ≤ ((max ((1 : ℝ≥0) + CV1₀ * angleBracket L)
                    ((CV1₀ * angleBracket L) * (1 + CV2₀ * angleBracket L)) : ℝ≥0) : ℝ≥0∞)
                  * eLpNorm w (ENNReal.ofReal V₁) Measure.count
                  * eLpNorm w' (ENNReal.ofReal V₂) Measure.count := by
          intro w w'
          refine (lossEndpoint₁ (ρ := ρ) (L := L) (K := K) (N := (n : ℝ≥0)) (P := P)
            (V₁ := V₁) (V₂ := V₂) (V₃ := V₃) hV₁ hV₂ hV₃le hrelV hCV₁ w w').trans ?_
          exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right
            (ENNReal.coe_le_coe.mpr (le_max_left _ _)) (by positivity)) (by positivity)
        have hgainV : ∀ w w' : ℤ → ℂ,
            eLpNorm (minorArc₁ ρ L K (n : ℝ≥0) P w w') 1 Measure.count
              ≤ ((((Cimp + 1) * (1 + C2₀ * angleBracket L)) * improvWeight cImp ρ L n : ℝ≥0)
                  : ℝ≥0∞) * eLpNorm w 2 Measure.count * eLpNorm w' 2 Measure.count := by
          intro w w'
          have h := hgain₁ w w'
          rwa [← ENNReal.coe_mul] at h
        have hMN : minorArc₁ ρ L K N P u v = minorArc₁ ρ L K (n : ℝ≥0) P u v := by
          simp only [minorArc₁]
          rw [← AhalfR_coe_nat_floor N X P, ← hndef]
        rw [hMN]
        rcases eq_or_lt_of_le hpr1 with hpr1eq | hprlt1
        · -- degenerate case `pr = 1` (equivalently `V₃ = 1`)
          have hsum1 : 1 / x₁ + 1 / x₂ = 1 := by
            rw [← hprinv, hpr1eq.symm]
            norm_num
          have hV₃1 : V₃ = 1 := by
            have h : 1 / V₃ = 1 := by
              rw [hV₃inv, hsum1]
              field_simp <;> ring
            exact ((div_eq_one_iff_eq hV₃pos.ne').mp h).symm
          have hloss1 : ∀ w w' : ℤ → ℂ,
              eLpNorm (minorArc₁ ρ L K (n : ℝ≥0) P w w') 1 Measure.count
                ≤ ((max ((1 : ℝ≥0) + CV1₀ * angleBracket L)
                      ((CV1₀ * angleBracket L) * (1 + CV2₀ * angleBracket L)) : ℝ≥0) : ℝ≥0∞)
                    * eLpNorm w (ENNReal.ofReal V₁) Measure.count
                    * eLpNorm w' (ENNReal.ofReal V₂) Measure.count := by
            intro w w'
            rw [hV₃1, ENNReal.ofReal_one] at hlossV
            exact hlossV w w'
          have hint := interp_step_deg (T := minorArc₁ ρ L K (n : ℝ≥0) P)
            (minorArc₁_linear_left ρ L K (n : ℝ≥0) P)
            (minorArc₁_linear_right ρ L K (n : ℝ≥0) P)
            (minorArc₁_tendsto ρ L K (n : ℝ≥0) P)
            hx₁ hx₂ hV₁ hV₂ hpr1eq.symm hθ0 hθ1 hx₁rel hx₂rel hgainV hloss1
          have hweight := weight_chain hθ0 hθ1 hAcomb1 hCg₁le hM₁le habs
          exact (hint u v hum hvm).trans (by
            calc ((((Cimp + 1) * (1 + C2₀ * angleBracket L)) * improvWeight cImp ρ L n : ℝ≥0)
                    : ℝ≥0∞) ^ (1 - θ)
                  * ((max ((1 : ℝ≥0) + CV1₀ * angleBracket L)
                      ((CV1₀ * angleBracket L) * (1 + CV2₀ * angleBracket L)) : ℝ≥0) : ℝ≥0∞) ^ θ
                  * eLpNorm u (ENNReal.ofReal x₁) Measure.count
                  * eLpNorm v (ENNReal.ofReal x₂) Measure.count
                ≤ ((Clarge : ℝ≥0∞) * (heightWeight 10 N : ℝ≥0∞))
                  * eLpNorm u (ENNReal.ofReal x₁) Measure.count
                  * eLpNorm v (ENNReal.ofReal x₂) Measure.count :=
                  mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hweight (by positivity))
                    (by positivity)
              _ ≤ ((Cf : ℝ≥0∞) * (heightWeight 10 N : ℝ≥0∞))
                  * eLpNorm u (ENNReal.ofReal x₁) Measure.count
                  * eLpNorm v (ENNReal.ofReal x₂) Measure.count :=
                  mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right
                    (mul_le_mul_of_nonneg_right (ENNReal.coe_le_coe.mpr hClargele) (by positivity))
                    (by positivity)) (by positivity)
              _ = (Cf : ℝ≥0∞) * (heightWeight 10 N : ℝ≥0∞)
                    * eLpNorm u (ENNReal.ofReal x₁) Measure.count
                    * eLpNorm v (ENNReal.ofReal x₂) Measure.count := by ring)
        · -- non-degenerate case `1 < pr`
          have hsumlt : 1 / x₁ + 1 / x₂ < 1 := by
            rw [← hprinv]
            exact (div_lt_one hprpos).mpr hprlt1
          have hV₃gt1 : 1 < V₃ := by
            have h2 : (1 / x₁ + 1 / x₂ - (1 - θ)) / θ < 1 := by
              rw [div_lt_one hθ0]
              linarith
            have h3 : 1 / V₃ < 1 := by rw [hV₃inv]; exact h2
            rwa [div_lt_one hV₃pos] at h3
          have hrθ : 1 / pr = 1 - θ / (V₃ / (V₃ - 1)) := by
            have h1 : θ / (V₃ / (V₃ - 1)) = θ * (V₃ - 1) / V₃ := by
              have h2 : V₃ - 1 ≠ 0 := by intro h; linarith
              field_simp <;> ring
            have h2 : 1 - θ * (V₃ - 1) / V₃ = (1 - θ) + θ / V₃ := by
              field_simp <;> ring
            rw [h1, h2, ← hsumrel, ← hprinv]
          have hint := interp_step_nd (T := minorArc₁ ρ L K (n : ℝ≥0) P)
            (minorArc₁_linear_left ρ L K (n : ℝ≥0) P)
            (minorArc₁_linear_right ρ L K (n : ℝ≥0) P)
            (minorArc₁_tendsto ρ L K (n : ℝ≥0) P)
            hx₁ hx₂ hV₁ hV₂ hV₃gt1 hprlt1 hθ0 hθ1 hx₁rel hx₂rel hrθ hgainV hlossV
          have hweight := weight_chain hθ0 hθ1 hAcomb1 hCg₁le hM₁le habs
          exact (hint u v hum hvm).trans (by
            calc ((((Cimp + 1) * (1 + C2₀ * angleBracket L)) * improvWeight cImp ρ L n : ℝ≥0)
                    : ℝ≥0∞) ^ (1 - θ)
                  * ((max ((1 : ℝ≥0) + CV1₀ * angleBracket L)
                      ((CV1₀ * angleBracket L) * (1 + CV2₀ * angleBracket L)) : ℝ≥0) : ℝ≥0∞) ^ θ
                  * eLpNorm u (ENNReal.ofReal x₁) Measure.count
                  * eLpNorm v (ENNReal.ofReal x₂) Measure.count
                ≤ ((Clarge : ℝ≥0∞) * (heightWeight 10 N : ℝ≥0∞))
                  * eLpNorm u (ENNReal.ofReal x₁) Measure.count
                  * eLpNorm v (ENNReal.ofReal x₂) Measure.count :=
                  mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hweight (by positivity))
                    (by positivity)
              _ ≤ ((Cf : ℝ≥0∞) * (heightWeight 10 N : ℝ≥0∞))
                  * eLpNorm u (ENNReal.ofReal x₁) Measure.count
                  * eLpNorm v (ENNReal.ofReal x₂) Measure.count :=
                  mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right
                    (mul_le_mul_of_nonneg_right (ENNReal.coe_le_coe.mpr hClargele) (by positivity))
                    (by positivity)) (by positivity)
              _ = (Cf : ℝ≥0∞) * (heightWeight 10 N : ℝ≥0∞)
                    * eLpNorm u (ENNReal.ofReal x₁) Measure.count
                    * eLpNorm v (ENNReal.ofReal x₂) Measure.count := by ring)

  have key₂ : ∀ (N : ℝ≥0) (f g : ℤ → ℂ), 1 ≤ N →
      eLpNorm (minorArc₂ ρ (heightScale C₀ (Nat.floor N))
        (-(logN (Nat.floor N)) + (heightScale C₀ (Nat.floor N) : ℤ))
        (-((P.natDegree : ℤ) * logN (Nat.floor N))
          + (P.natDegree : ℤ) * (heightScale C₀ (Nat.floor N) : ℤ)) N P f g)
        (ENNReal.ofReal pr) Measure.count
        ≤ (Cf : ℝ≥0∞) * (heightWeight 10 N : ℝ≥0∞) * eLpNorm f p₁ Measure.count * eLpNorm g p₂ Measure.count := by
    intro N f g hN
    set n : ℕ := Nat.floor N with hndef
    set L : ℕ := heightScale C₀ n with hLdef
    set K : ℤ := -(logN n) + (L : ℤ) with hKdef
    set K₂ : ℤ := -((P.natDegree : ℤ) * logN n) + (P.natDegree : ℤ) * (L : ℤ) with hK₂def
    have hNn : 1 ≤ n := by
      rw [hndef]
      exact Nat.le_floor (by exact_mod_cast hN : ((1 : ℕ) : ℝ≥0) ≤ N)
    have hL1 : 1 ≤ L := by
      rw [hLdef]
      exact Nat.succ_le_of_lt (Nat.mul_pos (lt_of_lt_of_le zero_lt_one hC₀1)
        (Work.Analysis.EndVar.logLogN_pos n))
    have hMne : (Cf : ℝ≥0∞) * (heightWeight 10 N : ℝ≥0∞) ≠ 0 :=
      mul_ne_zero (ENNReal.coe_ne_zero.mpr hCfpos.ne')
        (ENNReal.coe_ne_zero.mpr (heightWeight_pos 10 N).ne')
    refine (endpoint_trivial (fun u v => minorArc₂ ρ L K K₂ N P u v) hMne hp₁pos0.ne'
      hp₂pos0.ne' (fun v => minorArc₂_zero_left ρ L K K₂ N P v)
      (fun u => minorArc₂_zero_right ρ L K K₂ N P u) ?_) f g
    · intro u v hu hv
      rw [← hp₁eq, ← hp₂eq] at ⊢
      rw [← hp₁eq] at hu
      rw [← hp₂eq] at hv
      have hum : MemLp u (ENNReal.ofReal x₁) Measure.count :=
        MeasureTheory.memLp_iff.mpr hu
      have hvm : MemLp v (ENNReal.ofReal x₂) Measure.count :=
        MeasureTheory.memLp_iff.mpr hv
      by_cases hsl : n < n₀
      · -- small scale
        have hnle : n ≤ n₀ := le_of_lt hsl
        have hcr1 := hCc₁ n hnle
        have hcr2 := hCc₂ n hnle
        have hprojx₁K : ∀ w : ℤ → ℂ,
            eLpNorm (kmtProj ρ L K w) (ENNReal.ofReal x₁) Measure.count
              ≤ ((Cc₁ + 1 : ℝ≥0) : ℝ≥0∞) * eLpNorm w (ENNReal.ofReal x₁) Measure.count := by
          intro w
          have h := (hcr1 w).1
          rw [← hLdef, ← hKdef] at h
          exact h.trans (mul_le_mul'
            (ENNReal.coe_le_coe.mpr (le_add_of_nonneg_right bot_le)) le_rfl)
        have hkey : x₁⁻¹ + x₂⁻¹ = pr⁻¹ := by
          have h := hprinv
          simp only [one_div] at h
          exact h.symm
        have hprojx₂K₂ : ∀ w : ℤ → ℂ,
            eLpNorm (kmtProj ρ L K₂ w) (ENNReal.ofReal x₂) Measure.count
              ≤ ((Cc₂ + 1 : ℝ≥0) : ℝ≥0∞) * eLpNorm w (ENNReal.ofReal x₂) Measure.count := by
          intro w
          have h := (hcr2 w).2
          rw [← hLdef, ← hK₂def] at h
          exact h.trans (mul_le_mul'
            (ENNReal.coe_le_coe.mpr (le_add_of_nonneg_right bot_le)) le_rfl)
        have hrelx : (ENNReal.ofReal x₁)⁻¹ + (ENNReal.ofReal x₂)⁻¹
            = (ENNReal.ofReal pr)⁻¹ := by
          rw [← ENNReal.ofReal_inv_of_pos hx₁pos, ← ENNReal.ofReal_inv_of_pos hx₂pos,
            ← ENNReal.ofReal_inv_of_pos hprpos,
            ← ENNReal.ofReal_add (by positivity) (by positivity),
            ENNReal.ofReal_eq_ofReal_iff (by positivity) (by positivity)]
          exact hkey
        have hloss1 := lossEndpoint₂ (ρ := ρ) (L := L) (K := K) (K₂ := K₂) (N := N) (P := P)
          (V₁ := x₁) (V₂ := x₂) (V₃ := pr) hx₁ hx₂ hpr1 hrelx
          (by positivity : (0:ℝ≥0) < (Cc₁ + 1)) hprojx₁K hprojx₂K₂
        have hcwle : (cw : ℝ≥0) ≤ heightWeight 10 (Nat.floor N : ℝ≥0) := by
          rw [hcwdef]
          exact heightWeight_antitone 10 (by norm_num)
            (by exact_mod_cast (Nat.le_of_lt hsl))
        have hcwh : (cw : ℝ≥0) ≤ Kw * heightWeight 10 N :=
          hcwle.trans (hKw N (by exact_mod_cast hN : 1 ≤ N))
        have hKh : (Csmall : ℝ≥0) ≤ Cf * heightWeight 10 N := by
          have h1 : Csmall * Kw ≤ Cf * cw := by
            have h := mul_le_mul_of_nonneg_right hCsmallle hcwpos.le
            rwa [mul_assoc, inv_mul_cancel₀ hcwpos.ne', mul_one] at h
          have h2 : Cf * cw ≤ Cf * (heightWeight 10 N * Kw) :=
            mul_le_mul_of_nonneg_left (by rw [mul_comm]; exact hcwh) bot_le
          have h3 : Cf * (heightWeight 10 N * Kw) = (Cf * heightWeight 10 N) * Kw := by
            rw [mul_assoc]
          exact le_of_mul_le_mul_right (h1.trans (h3 ▸ h2)) hKwpos
        have hconst : (((Cc₁ + 1) * ((1 : ℝ≥0) + (Cc₂ + 1))) : ℝ≥0∞)
            ≤ (Cf : ℝ≥0∞) * (heightWeight 10 N : ℝ≥0∞) :=
          ENNReal.coe_le_coe.mpr ((le_max_right _ _).trans hKh)
        exact (hloss1 u v).trans (mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_right hconst (by positivity)) (by positivity))
      · -- large scale
        have hlge : n₀ ≤ n := le_of_not_gt hsl
        have hgoodK : GoodMajorArcs ρ Cρ L K := by
          show ((K : ℤ) : ℝ) ≤ -Cρ * (2 : ℝ) ^ (ρ * ((L : ℕ) : ℝ))
          rw [hKdef, hLdef]
          have h := hn₀ n hlge
          push_cast
          linarith
        have hKle : K ≤ -1 := by
          rw [hKdef, hLdef]
          have h := hn₀ n hlge
          have hpos : (0 : ℝ) ≤ Cρ * (2 : ℝ) ^ (ρ * ((heightScale C₀ n : ℕ) : ℝ)) := by
            have hp := Real.rpow_pos_of_pos (by norm_num : (0 : ℝ) < 2)
              (ρ * ((heightScale C₀ n : ℕ) : ℝ))
            positivity
          have h2 : (((-(logN n) + ((heightScale C₀ n : ℕ) : ℤ)) : ℤ) : ℝ) ≤ -1 := by
            push_cast
            linarith
          exact_mod_cast h2
        have hK₂le : K₂ ≤ -1 := by
          have hd1 : (1 : ℤ) ≤ (P.natDegree : ℤ) := by
            have := hdeg
            omega
          have hEq : K₂ = (P.natDegree : ℤ) * K := by rw [hK₂def, hKdef]; ring
          rw [hEq]
          calc (P.natDegree : ℤ) * K ≤ 1 * K := mul_le_mul_of_nonpos_right hd1 (by omega : K ≤ 0)
            _ = K := one_mul K
            _ ≤ -1 := hKle
        have hgoodK₂ : GoodMajorArcs ρ Cρ L K₂ := by
          show ((K₂ : ℤ) : ℝ) ≤ -Cρ * (2 : ℝ) ^ (ρ * ((L : ℕ) : ℝ))
          have hEq : K₂ = (P.natDegree : ℤ) * K := by rw [hK₂def, hKdef]; ring
          rw [hEq]
          push_cast
          have hK0 : ((K : ℤ) : ℝ) ≤ 0 := by
            have h : ((K : ℤ) : ℝ) ≤ -Cρ * (2 : ℝ) ^ (ρ * ((L : ℕ) : ℝ)) := hgoodK
            have h2 : -Cρ * (2 : ℝ) ^ (ρ * ((L : ℕ) : ℝ)) ≤ 0 := by
              have := Real.rpow_pos_of_pos (by norm_num : (0 : ℝ) < 2) (ρ * ((L : ℕ) : ℝ))
              nlinarith [hCρpos, this]
            linarith
          have hd1 : (1 : ℝ) ≤ (P.natDegree : ℝ) := by
            have := hdeg
            exact_mod_cast (show 1 ≤ P.natDegree by omega)
          calc ((P.natDegree : ℤ) : ℝ) * ((K : ℤ) : ℝ) ≤ 1 * ((K : ℤ) : ℝ) :=
                mul_le_mul_of_nonpos_right hd1 hK0
            _ = ((K : ℤ) : ℝ) := one_mul _
            _ ≤ -Cρ * (2 : ℝ) ^ (ρ * ((L : ℕ) : ℝ)) := hgoodK
        have hC₂₂ : ∀ w : ℤ → ℂ, eLpNorm (kmtProj ρ L K w) 2 Measure.count
            ≤ ((C2₀ * angleBracket L : ℝ≥0) : ℝ≥0∞) * eLpNorm w 2 Measure.count := by
          intro w
          have h := hb2 L K (hgc2 L K hgoodK) w
          rwa [ofReal_coe_mul_angleBracket, ofReal_two] at h
        have hC₂₃ : ∀ w : ℤ → ℂ, eLpNorm (kmtProj ρ L K₂ w) 2 Measure.count
            ≤ ((C2₀ * angleBracket L : ℝ≥0) : ℝ≥0∞) * eLpNorm w 2 Measure.count := by
          intro w
          have h := hb2 L K₂ (hgc2 L K₂ hgoodK₂) w
          rwa [ofReal_coe_mul_angleBracket, ofReal_two] at h
        have hCV₁ : ∀ w : ℤ → ℂ, eLpNorm (kmtProj ρ L K w) (ENNReal.ofReal V₁) Measure.count
            ≤ ((CV1₀ * angleBracket L : ℝ≥0) : ℝ≥0∞)
                * eLpNorm w (ENNReal.ofReal V₁) Measure.count := by
          intro w
          have h := hbV1 L K (hgcV1 L K hgoodK) w
          rwa [ofReal_coe_mul_angleBracket] at h
        have hcomp₁ : ∀ w : ℤ → ℂ, BoundedZ w →
            kmtProj ρ (L - 1) (K - 1) (w - kmtProj ρ L K w) = 0 :=
          fun w hw => kmtProj_sub_comp_eq_zero ρ hρ0 hρ1 (Nat.sub_le L 1) (by omega) hKle
            (hgcNA L K hgoodK) hw
        have hcomp₂ : ∀ w : ℤ → ℂ, BoundedZ w →
            kmtProj ρ (L - 1) (K₂ - (P.natDegree : ℤ)) (w - kmtProj ρ L K₂ w) = 0 :=
          fun w hw => kmtProj_sub_comp_eq_zero ρ hρ0 hρ1 (Nat.sub_le L 1) (by omega) hK₂le
            (hgcNA L K₂ hgoodK₂) hw
        obtain ⟨_, hgain₂⟩ := gainEndpoint_explicit (P := P) (ρ := ρ) (c := cImp) hcImp
          (Cimp := Cimp) hbound (N := n) hNn (L := L) hL1 (K := K) (K₂ := K₂)
          hKdef hK₂def hcomp₁ hcomp₂ hC₂₂ hC₂₃
        have hone : ∀ c : ℝ≥0, 1 + c * angleBracket L ≤ (1 + c) * angleBracket L :=
          fun c => one_add_mul_le_mul_one_add c (angleBracket L) (one_le_angleBracket L)
        have hCg₁le : (Cimp + 1) * (1 + C2₀ * angleBracket L) ≤ Acomb * angleBracket L ^ 2 := by
          calc (Cimp + 1) * (1 + C2₀ * angleBracket L)
              ≤ (Cimp + 1) * ((1 + C2₀) * angleBracket L) :=
                mul_le_mul_of_nonneg_left (hone C2₀) (by positivity)
            _ = A1c * angleBracket L := by rw [hA1c]; ring
            _ ≤ A1c * angleBracket L ^ 2 := mul_le_mul_sq A1c (angleBracket L) (one_le_angleBracket L)
            _ ≤ Acomb * angleBracket L ^ 2 := mul_sq_le_mul_sq A1c Acomb (angleBracket L) hA1cle
        have hCV₂ : ∀ w : ℤ → ℂ, eLpNorm (kmtProj ρ L K₂ w) (ENNReal.ofReal V₂) Measure.count
            ≤ ((CV2₀ * angleBracket L : ℝ≥0) : ℝ≥0∞)
                * eLpNorm w (ENNReal.ofReal V₂) Measure.count := by
          intro w
          have h := hbV2 L K₂ (hgcV2 L K₂ hgoodK₂) w
          rwa [ofReal_coe_mul_angleBracket] at h
        have hCg₂le : C2₀ * angleBracket L * ((Cimp + 1) * (1 + C2₀ * angleBracket L))
            ≤ Acomb * angleBracket L ^ 2 := by
          calc C2₀ * angleBracket L * ((Cimp + 1) * (1 + C2₀ * angleBracket L))
              ≤ C2₀ * angleBracket L * ((Cimp + 1) * ((1 + C2₀) * angleBracket L)) := by
                refine mul_le_mul_of_nonneg_left ?_ (by positivity)
                exact mul_le_mul_of_nonneg_left (hone C2₀) (by positivity)
            _ = A2c * angleBracket L ^ 2 := by rw [hA2c]; ring
            _ ≤ Acomb * angleBracket L ^ 2 := mul_sq_le_mul_sq A2c Acomb (angleBracket L) hA2cle
        have hM₁le : max ((1 : ℝ≥0) + CV1₀ * angleBracket L)
            ((CV1₀ * angleBracket L) * (1 + CV2₀ * angleBracket L))
            ≤ Acomb * angleBracket L ^ 2 := by
          refine max_le ?_ ?_
          · calc (1 : ℝ≥0) + CV1₀ * angleBracket L ≤ (1 + CV1₀) * angleBracket L :=
                  one_add_mul_le_mul_one_add CV1₀ (angleBracket L) (one_le_angleBracket L)
              _ ≤ (1 + CV1₀) * angleBracket L ^ 2 :=
                  mul_le_mul_sq (1 + CV1₀) (angleBracket L) (one_le_angleBracket L)
              _ ≤ A5c * angleBracket L ^ 2 := mul_sq_le_mul_sq _ A5c _ (le_max_left _ _)
              _ ≤ Acomb * angleBracket L ^ 2 := mul_sq_le_mul_sq _ Acomb _ hA5cle
          · calc (CV1₀ * angleBracket L) * (1 + CV2₀ * angleBracket L)
                ≤ (CV1₀ * angleBracket L) * ((1 + CV2₀) * angleBracket L) :=
                  mul_le_mul_of_nonneg_left (hone CV2₀) (by positivity)
              _ = (CV1₀ * (1 + CV2₀)) * angleBracket L ^ 2 := by ring
              _ ≤ A5c * angleBracket L ^ 2 := mul_sq_le_mul_sq _ A5c _ (le_max_right _ _)
              _ ≤ Acomb * angleBracket L ^ 2 := mul_sq_le_mul_sq _ Acomb _ hA5cle
        have habs : (improvWeight cImp ρ L n : ℝ≥0∞) ^ (1 - θ)
              * ((angleBracket L : ℝ≥0) : ℝ≥0∞) ^ 2
            ≤ ((Ca * Kw : ℝ≥0) : ℝ≥0∞) * (heightWeight 10 N : ℝ≥0∞) := by
          rw [← ENNReal.rpow_natCast ((angleBracket L : ℝ≥0) : ℝ≥0∞) 2, hLdef]
          refine (hCa n hNn).trans ?_
          have hfl := hKw N (by exact_mod_cast hN : 1 ≤ N)
          rw [← hndef] at hfl
          calc (Ca : ℝ≥0∞) * (heightWeight 10 (n : ℝ≥0) : ℝ≥0∞)
              ≤ (Ca : ℝ≥0∞) * ((Kw * heightWeight 10 N : ℝ≥0) : ℝ≥0∞) :=
                mul_le_mul_of_nonneg_left (ENNReal.coe_le_coe.mpr hfl) (by positivity)
            _ = ((Ca * Kw : ℝ≥0) : ℝ≥0∞) * (heightWeight 10 N : ℝ≥0∞) := by
                rw [ENNReal.coe_mul, ENNReal.coe_mul, mul_assoc]
        have hlossV : ∀ w w' : ℤ → ℂ,
            eLpNorm (minorArc₂ ρ L K K₂ (n : ℝ≥0) P w w') (ENNReal.ofReal V₃) Measure.count
              ≤ ((max ((1 : ℝ≥0) + CV1₀ * angleBracket L)
                    ((CV1₀ * angleBracket L) * (1 + CV2₀ * angleBracket L)) : ℝ≥0) : ℝ≥0∞)
                  * eLpNorm w (ENNReal.ofReal V₁) Measure.count
                  * eLpNorm w' (ENNReal.ofReal V₂) Measure.count := by
          intro w w'
          refine (lossEndpoint₂ (ρ := ρ) (L := L) (K := K) (K₂ := K₂) (N := (n : ℝ≥0)) (P := P)
            (V₁ := V₁) (V₂ := V₂) (V₃ := V₃) hV₁ hV₂ hV₃le hrelV
            (mul_pos hCV1₀pos (angleBracket_pos L)) hCV₁ hCV₂ w w').trans ?_
          exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right
            (ENNReal.coe_le_coe.mpr (le_max_right _ _)) (by positivity)) (by positivity)
        have hgainV : ∀ w w' : ℤ → ℂ,
            eLpNorm (minorArc₂ ρ L K K₂ (n : ℝ≥0) P w w') 1 Measure.count
              ≤ (((C2₀ * angleBracket L * ((Cimp + 1) * (1 + C2₀ * angleBracket L)))
                    * improvWeight cImp ρ L n : ℝ≥0)
                  : ℝ≥0∞) * eLpNorm w 2 Measure.count * eLpNorm w' 2 Measure.count := by
          intro w w'
          have h := hgain₂ w w'
          rwa [← ENNReal.coe_mul] at h
        have hMN : minorArc₂ ρ L K K₂ N P u v = minorArc₂ ρ L K K₂ (n : ℝ≥0) P u v := by
          simp only [minorArc₂]
          rw [← AhalfR_coe_nat_floor N X P, ← hndef]
        rw [hMN]
        rcases eq_or_lt_of_le hpr1 with hpr1eq | hprlt1
        · -- degenerate case `pr = 1` (equivalently `V₃ = 1`)
          have hsum1 : 1 / x₁ + 1 / x₂ = 1 := by
            rw [← hprinv, hpr1eq.symm]
            norm_num
          have hV₃1 : V₃ = 1 := by
            have h : 1 / V₃ = 1 := by
              rw [hV₃inv, hsum1]
              field_simp <;> ring
            exact ((div_eq_one_iff_eq hV₃pos.ne').mp h).symm
          have hloss1 : ∀ w w' : ℤ → ℂ,
              eLpNorm (minorArc₂ ρ L K K₂ (n : ℝ≥0) P w w') 1 Measure.count
                ≤ ((max ((1 : ℝ≥0) + CV1₀ * angleBracket L)
                      ((CV1₀ * angleBracket L) * (1 + CV2₀ * angleBracket L)) : ℝ≥0) : ℝ≥0∞)
                    * eLpNorm w (ENNReal.ofReal V₁) Measure.count
                    * eLpNorm w' (ENNReal.ofReal V₂) Measure.count := by
            intro w w'
            rw [hV₃1, ENNReal.ofReal_one] at hlossV
            exact hlossV w w'
          have hint := interp_step_deg (T := minorArc₂ ρ L K K₂ (n : ℝ≥0) P)
            (minorArc₂_linear_left ρ L K K₂ (n : ℝ≥0) P)
            (minorArc₂_linear_right ρ L K K₂ (n : ℝ≥0) P)
            (minorArc₂_tendsto ρ L K K₂ (n : ℝ≥0) P)
            hx₁ hx₂ hV₁ hV₂ hpr1eq.symm hθ0 hθ1 hx₁rel hx₂rel hgainV hloss1
          have hweight := weight_chain hθ0 hθ1 hAcomb1 hCg₂le hM₁le habs
          exact (hint u v hum hvm).trans (by
            calc (((C2₀ * angleBracket L * ((Cimp + 1) * (1 + C2₀ * angleBracket L)))
                      * improvWeight cImp ρ L n : ℝ≥0)
                    : ℝ≥0∞) ^ (1 - θ)
                  * ((max ((1 : ℝ≥0) + CV1₀ * angleBracket L)
                      ((CV1₀ * angleBracket L) * (1 + CV2₀ * angleBracket L)) : ℝ≥0) : ℝ≥0∞) ^ θ
                  * eLpNorm u (ENNReal.ofReal x₁) Measure.count
                  * eLpNorm v (ENNReal.ofReal x₂) Measure.count
                ≤ ((Clarge : ℝ≥0∞) * (heightWeight 10 N : ℝ≥0∞))
                  * eLpNorm u (ENNReal.ofReal x₁) Measure.count
                  * eLpNorm v (ENNReal.ofReal x₂) Measure.count :=
                  mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hweight (by positivity))
                    (by positivity)
              _ ≤ ((Cf : ℝ≥0∞) * (heightWeight 10 N : ℝ≥0∞))
                  * eLpNorm u (ENNReal.ofReal x₁) Measure.count
                  * eLpNorm v (ENNReal.ofReal x₂) Measure.count :=
                  mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right
                    (mul_le_mul_of_nonneg_right (ENNReal.coe_le_coe.mpr hClargele) (by positivity))
                    (by positivity)) (by positivity)
              _ = (Cf : ℝ≥0∞) * (heightWeight 10 N : ℝ≥0∞)
                    * eLpNorm u (ENNReal.ofReal x₁) Measure.count
                    * eLpNorm v (ENNReal.ofReal x₂) Measure.count := by ring)
        · -- non-degenerate case `1 < pr`
          have hsumlt : 1 / x₁ + 1 / x₂ < 1 := by
            rw [← hprinv]
            exact (div_lt_one hprpos).mpr hprlt1
          have hV₃gt1 : 1 < V₃ := by
            have h2 : (1 / x₁ + 1 / x₂ - (1 - θ)) / θ < 1 := by
              rw [div_lt_one hθ0]
              linarith
            have h3 : 1 / V₃ < 1 := by rw [hV₃inv]; exact h2
            rwa [div_lt_one hV₃pos] at h3
          have hrθ : 1 / pr = 1 - θ / (V₃ / (V₃ - 1)) := by
            have h1 : θ / (V₃ / (V₃ - 1)) = θ * (V₃ - 1) / V₃ := by
              have h2 : V₃ - 1 ≠ 0 := by intro h; linarith
              field_simp <;> ring
            have h2 : 1 - θ * (V₃ - 1) / V₃ = (1 - θ) + θ / V₃ := by
              field_simp <;> ring
            rw [h1, h2, ← hsumrel, ← hprinv]
          have hint := interp_step_nd (T := minorArc₂ ρ L K K₂ (n : ℝ≥0) P)
            (minorArc₂_linear_left ρ L K K₂ (n : ℝ≥0) P)
            (minorArc₂_linear_right ρ L K K₂ (n : ℝ≥0) P)
            (minorArc₂_tendsto ρ L K K₂ (n : ℝ≥0) P)
            hx₁ hx₂ hV₁ hV₂ hV₃gt1 hprlt1 hθ0 hθ1 hx₁rel hx₂rel hrθ hgainV hlossV
          have hweight := weight_chain hθ0 hθ1 hAcomb1 hCg₂le hM₁le habs
          exact (hint u v hum hvm).trans (by
            calc (((C2₀ * angleBracket L * ((Cimp + 1) * (1 + C2₀ * angleBracket L)))
                      * improvWeight cImp ρ L n : ℝ≥0)
                    : ℝ≥0∞) ^ (1 - θ)
                  * ((max ((1 : ℝ≥0) + CV1₀ * angleBracket L)
                      ((CV1₀ * angleBracket L) * (1 + CV2₀ * angleBracket L)) : ℝ≥0) : ℝ≥0∞) ^ θ
                  * eLpNorm u (ENNReal.ofReal x₁) Measure.count
                  * eLpNorm v (ENNReal.ofReal x₂) Measure.count
                ≤ ((Clarge : ℝ≥0∞) * (heightWeight 10 N : ℝ≥0∞))
                  * eLpNorm u (ENNReal.ofReal x₁) Measure.count
                  * eLpNorm v (ENNReal.ofReal x₂) Measure.count :=
                  mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hweight (by positivity))
                    (by positivity)
              _ ≤ ((Cf : ℝ≥0∞) * (heightWeight 10 N : ℝ≥0∞))
                  * eLpNorm u (ENNReal.ofReal x₁) Measure.count
                  * eLpNorm v (ENNReal.ofReal x₂) Measure.count :=
                  mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right
                    (mul_le_mul_of_nonneg_right (ENNReal.coe_le_coe.mpr hClargele) (by positivity))
                    (by positivity)) (by positivity)
              _ = (Cf : ℝ≥0∞) * (heightWeight 10 N : ℝ≥0∞)
                    * eLpNorm u (ENNReal.ofReal x₁) Measure.count
                    * eLpNorm v (ENNReal.ofReal x₂) Measure.count := by ring)


  refine ⟨Cf, ?_⟩
  intro N f g hN
  rw [hexp]
  refine ⟨?_, ?_⟩
  · show eLpNorm (minorArc₁ ρ (heightScale C₀ (Nat.floor N))
        (-(logN (Nat.floor N)) + (heightScale C₀ (Nat.floor N) : ℤ)) N P f g)
        (ENNReal.ofReal pr) Measure.count
        ≤ (Cf : ℝ≥0∞) * (heightWeight 10 N : ℝ≥0∞) * eLpNorm f p₁ Measure.count
            * eLpNorm g p₂ Measure.count
    exact key₁ N f g hN
  · show eLpNorm (minorArc₂ ρ (heightScale C₀ (Nat.floor N))
        (-(logN (Nat.floor N)) + (heightScale C₀ (Nat.floor N) : ℤ))
        (-((P.natDegree : ℤ) * logN (Nat.floor N))
          + (P.natDegree : ℤ) * (heightScale C₀ (Nat.floor N) : ℤ)) N P f g)
        (ENNReal.ofReal pr) Measure.count
        ≤ (Cf : ℝ≥0∞) * (heightWeight 10 N : ℝ≥0∞) * eLpNorm f p₁ Measure.count
            * eLpNorm g p₂ Measure.count
    exact key₂ N f g hN

end

end Work.KMTAreas.A5
