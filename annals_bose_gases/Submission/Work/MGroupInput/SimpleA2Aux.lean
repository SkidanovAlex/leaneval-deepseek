import ChallengeDeps
import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.Algebra.Order.Star.Real
import Submission.Work.MGroupInput.bog_zero_point_gap_simple
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Work.MGroupInput.SimpleA2Aux` — the sharp (`hsharp`-based) kernel facts for `SimpleA2`

The corpus proves all its pairing/fibre bounds under the structural hypothesis
`R ≤ ℓ·chiR0` (`hRs`), which is NOT implied by the pointwise/a.e. hypothesis

  `hsharp : ∀ᵐ x, wScaled s (g0 v h) x ≤ (1+δ) · g0 v h x`

that `Work.MGroupInput.diagW_simpleA2` carries.  This module records the
`hsharp`-based replacements of the corpus facts that only ever needed `hRs`
through the pointwise bound `|wScaled ℓ h z| ≤ 2|h z|`
(`KernelMean.wScaled_abs_le_two`):

* `wScaled_g0_abs_le_of_sharp` — `|wScaled s (g0 v h) x| ≤ (1+δ)|g0 v h x|` a.e.;
* `integrable_wScaled_g0_of_sharp` — `Integrable (wScaled s (g0 v h))`;
* `abs_pairW_wScaled_g0_le_sharp` — `|pairW W₁ q| ≤ 8π(1+δ)(a v)` (better than
  the corpus's `16π a v`, which uses `2|g0|`);
* `measurable_d1Bcoef_sharp` — `Measurable (d1Bcoef W₁)`.
-/

noncomputable section

open MeasureTheory Metric Filter
open scoped ContDiff Topology Real BigOperators ENNReal

namespace Work.MGroupInput

open Submission BoseGases

local notation "ℝ³" => EuclideanSpace ℝ (Fin 3)

set_option autoImplicit false
set_option linter.unusedVariables false

/-- **The sharp a.e. kernel bound.**  From `hsharp` and the a.e. nonnegativity of
`g₀ = v(1-w₀)` we get `|wScaled s (g0 v h) x| ≤ (1+δ)|g0 v h x|` a.e.  (Where
`(χ⋆χ)(x/s) = 0` Lean's division convention gives `wScaled = 0`.) -/
lemma wScaled_g0_abs_le_of_sharp {s δ : ℝ} (hs : 0 < s)
    {v : ℝ³ → ℝ} {R : ℝ} (hR : 0 < R) (hv_nonneg : 0 ≤ v) (hvrad : IsRadial v)
    (hv_supp : tsupport v ⊆ ball (0 : ℝ³) R)
    (h : ∃ w : ℝ³ → ℝ, IsRadial w ∧ IsScatteringSolution w v)
    (hδ : 0 ≤ δ)
    (hsharp : ∀ᵐ x : ℝ³, wScaled s (g0 v h) x ≤ (1 + δ) * g0 v h x) :
    ∀ᵐ x : ℝ³, |wScaled s (g0 v h) x| ≤ (1 + δ) * |g0 v h x| := by
  have hg0 := g0_nonneg_ae hR hv_nonneg hvrad hv_supp h
  filter_upwards [hsharp, hg0] with x hx hg
  have hw0 : 0 ≤ wScaled s (g0 v h) x := by
    rw [wScaled]
    exact div_nonneg hg (convScale_nonneg s x)
  rw [abs_of_nonneg hw0, abs_of_nonneg hg]
  exact hx

/-- **Integrability of the sharp kernel.**  `Integrable (wScaled s (g0 v h))` from
`hsharp` (a.e. domination by `(1+δ)|g₀|` on top of `g0_integrable`). -/
lemma integrable_wScaled_g0_of_sharp {s δ : ℝ} (hs : 0 < s)
    {v : ℝ³ → ℝ} {R : ℝ} (hR : 0 < R) (hv_nonneg : 0 ≤ v) (hvrad : IsRadial v)
    (hv_supp : tsupport v ⊆ ball (0 : ℝ³) R)
    (h : ∃ w : ℝ³ → ℝ, IsRadial w ∧ IsScatteringSolution w v)
    (hδ : 0 ≤ δ)
    (hsharp : ∀ᵐ x : ℝ³, wScaled s (g0 v h) x ≤ (1 + δ) * g0 v h x) :
    Integrable (wScaled s (g0 v h)) := by
  have hi : Integrable (g0 v h) := g0_integrable hR hv_supp h
  have hWm : AEStronglyMeasurable (wScaled s (g0 v h)) := by
    have hinvmeas : Measurable (fun z : ℝ³ => (convScale s z)⁻¹) := by
      have hinv : Measurable fun t : ℝ => t⁻¹ := by fun_prop
      exact hinv.comp (convScale_continuous s).measurable
    have hEq : wScaled s (g0 v h) = fun z : ℝ³ => g0 v h z * (convScale s z)⁻¹ := by
      funext z
      dsimp [wScaled]
      rw [div_eq_mul_inv]
    rw [hEq]
    exact hi.aestronglyMeasurable.mul hinvmeas.aestronglyMeasurable
  refine Integrable.mono' (hi.abs.const_mul (1 + δ)) hWm ?_
  exact wScaled_g0_abs_le_of_sharp hs hR hv_nonneg hvrad hv_supp h hδ hsharp

/-- **The `(1+δ)·8π(av)` Fourier bound.**  `|pairW W₁ q| ≤ ∫|W₁| ≤ 8π(1+δ)(a v)`,
the `hsharp`-sharpening of the corpus's `abs_pairW_wScaled_g0_le` (`16π a v`). -/
lemma abs_pairW_wScaled_g0_le_sharp {s δ : ℝ} (hs : 0 < s)
    {v : ℝ³ → ℝ} {R : ℝ} (hR : 0 < R) (hv_nonneg : 0 ≤ v) (hvrad : IsRadial v)
    (hv_supp : tsupport v ⊆ ball (0 : ℝ³) R)
    (h : ∃ w : ℝ³ → ℝ, IsRadial w ∧ IsScatteringSolution w v)
    (hδ : 0 ≤ δ)
    (hsharp : ∀ᵐ x : ℝ³, wScaled s (g0 v h) x ≤ (1 + δ) * g0 v h x) (q : ℝ³) :
    |pairW (wScaled s (g0 v h)) q| ≤ 8 * Real.pi * (1 + δ) * (a v) := by
  refine le_trans (abs_pairW_le_integral_abs q) ?_
  have hwi : Integrable (wScaled s (g0 v h)) :=
    integrable_wScaled_g0_of_sharp hs hR hv_nonneg hvrad hv_supp h hδ hsharp
  have hi : Integrable (g0 v h) := g0_integrable hR hv_supp h
  have habs := wScaled_g0_abs_le_of_sharp hs hR hv_nonneg hvrad hv_supp h hδ hsharp
  have hmaj : Integrable (fun x : ℝ³ => (1 + δ) * |g0 v h x|) := hi.abs.const_mul (1 + δ)
  have h1 : (∫ x : ℝ³, |wScaled s (g0 v h) x|) ≤ ∫ x : ℝ³, (1 + δ) * |g0 v h x| :=
    integral_mono_ae hwi.abs hmaj habs
  rw [MeasureTheory.integral_const_mul] at h1
  have h2 : (∫ x : ℝ³, |g0 v h x|) = 8 * Real.pi * (a v) :=
    g0_abs_integral hR hv_nonneg hvrad hv_supp h
  rw [h2] at h1
  nlinarith [h1]

/-- **Measurability of the D1 weight** `d1Bcoef W₁ = ℜ 𝓕W₁((2π)⁻¹•q)`. -/
lemma measurable_d1Bcoef_sharp {s δ : ℝ} (hs : 0 < s)
    {v : ℝ³ → ℝ} {R : ℝ} (hR : 0 < R) (hv_nonneg : 0 ≤ v) (hvrad : IsRadial v)
    (hv_supp : tsupport v ⊆ ball (0 : ℝ³) R)
    (h : ∃ w : ℝ³ → ℝ, IsRadial w ∧ IsScatteringSolution w v)
    (hδ : 0 ≤ δ)
    (hsharp : ∀ᵐ x : ℝ³, wScaled s (g0 v h) x ≤ (1 + δ) * g0 v h x) :
    Measurable (d1Bcoef (wScaled s (g0 v h))) := by
  have hwi : Integrable (wScaled s (g0 v h)) :=
    integrable_wScaled_g0_of_sharp hs hR hv_nonneg hvrad hv_supp h hδ hsharp
  unfold d1Bcoef pairW
  exact (Complex.continuous_re.comp
    ((continuous_cfourier hwi).comp (continuous_const_smul _))).measurable

/-! ## 2  The Bogoliubov coefficient with a free constant `K_s`

FS's simple Bogoliubov bound (`eq:simpleaprioribog`) needs `K_s` LARGE (FS:
*"for the simple bound we may choose `K_s` large depending on `ε`"*), so that the
Fock half-regime `|ℬ| ≤ (ε/2)𝒜` holds for EVERY momentum and the coarse
zero-point bound may be used globally (no quartic/log refining terms).  The
corpus fixes `K_s = d1Ks = 16π`; here we keep it as a parameter. -/

/-- FS's faithful Bogoliubov `𝒜`-coefficient `s³·[‖q‖−c₀]₊²/(M+1) + 2K_s·a v`
with a free constant `K_s`. -/
noncomputable def diagAFK (Ks s c0 av M : ℝ) (q : ℝ³) : ℝ :=
  s ^ 3 * fsKinCoeff c0 ‖q‖ / (M + 1) + 2 * Ks * av

/-- The sharp Bogoliubov coefficient `(𝒜 − √(𝒜²−ℬ²))/2` at `𝒜 = diagAFK`. -/
noncomputable def diagKFK (Ks s c0 av M : ℝ) (W : ℝ³ → ℝ) (q : ℝ³) : ℝ :=
  (diagAFK Ks s c0 av M q
    - Real.sqrt ((diagAFK Ks s c0 av M q) ^ 2 - (d1Bcoef W q) ^ 2)) / 2

lemma diagAFK_ge_floor {Ks s c0 av M : ℝ} (hs : 0 < s) (hM : 0 ≤ M)
    (hKs : 0 ≤ Ks) (hav : 0 ≤ av) (q : ℝ³) :
    2 * Ks * av ≤ diagAFK Ks s c0 av M q := by
  have h1 : 0 ≤ s ^ 3 * fsKinCoeff c0 ‖q‖ / (M + 1) :=
    div_nonneg (mul_nonneg (by positivity) (fsKinCoeff_nonneg c0 ‖q‖)) (by linarith)
  unfold diagAFK
  linarith

lemma diagAFK_pos {Ks s c0 av M : ℝ} (hs : 0 < s) (hM : 0 ≤ M) (hKs : 0 < Ks)
    (hav : 0 < av) (q : ℝ³) : 0 < diagAFK Ks s c0 av M q := by
  have h := diagAFK_ge_floor (Ks := Ks) (c0 := c0) hs hM (le_of_lt hKs) (le_of_lt hav) q
  have h2 : 0 < 2 * Ks * av := by positivity
  linarith

lemma abs_d1Bcoef_le_diagAFK {Ks s c0 av M : ℝ} (hs : 0 < s) (hM : 0 ≤ M) (hKs : 0 < Ks)
    (hav : 0 < av) {W : ℝ³ → ℝ} (hWb : ∀ q : ℝ³, |d1Bcoef W q| ≤ 2 * Ks * av) (q : ℝ³) :
    |d1Bcoef W q| ≤ diagAFK Ks s c0 av M q :=
  le_trans (hWb q) (diagAFK_ge_floor (Ks := Ks) (c0 := c0) hs hM (le_of_lt hKs)
    (le_of_lt hav) q)

lemma diagKFK_nonneg {Ks s c0 av M : ℝ} (hs : 0 < s) (hM : 0 ≤ M) (hKs : 0 < Ks)
    (hav : 0 < av) {W : ℝ³ → ℝ} (hWb : ∀ q : ℝ³, |d1Bcoef W q| ≤ 2 * Ks * av) (q : ℝ³) :
    0 ≤ diagKFK Ks s c0 av M W q := by
  have hA := diagAFK_pos (Ks := Ks) (c0 := c0) hs hM hKs hav q
  have hB := abs_d1Bcoef_le_diagAFK (Ks := Ks) (c0 := c0) hs hM hKs hav hWb q
  have hB2 : (d1Bcoef W q) ^ 2 ≤ (diagAFK Ks s c0 av M q) ^ 2 := by
    rw [← sq_abs]; exact pow_le_pow_left₀ (abs_nonneg _) hB 2
  have hs' : Real.sqrt ((diagAFK Ks s c0 av M q) ^ 2 - (d1Bcoef W q) ^ 2)
      ≤ diagAFK Ks s c0 av M q := by
    rw [Real.sqrt_le_left hA.le]; linarith [sq_nonneg (d1Bcoef W q)]
  unfold diagKFK
  linarith

/-- **The sharp coefficient bound** `K(𝒜,ℬ) ≤ ℬ²/(4𝒜) + ℬ⁴/(4𝒜³)`. -/
lemma diagKFK_le_sharp {Ks s c0 av M : ℝ} (hs : 0 < s) (hM : 0 ≤ M) (hKs : 0 < Ks)
    (hav : 0 < av) {W : ℝ³ → ℝ} (hWb : ∀ q : ℝ³, |d1Bcoef W q| ≤ 2 * Ks * av) (q : ℝ³) :
    diagKFK Ks s c0 av M W q
      ≤ (d1Bcoef W q) ^ 2 / (4 * diagAFK Ks s c0 av M q)
        + (d1Bcoef W q) ^ 4 / (4 * (diagAFK Ks s c0 av M q) ^ 3) := by
  have hA := diagAFK_pos (Ks := Ks) (c0 := c0) hs hM hKs hav q
  have hB := abs_d1Bcoef_le_diagAFK (Ks := Ks) (c0 := c0) hs hM hKs hav hWb q
  have hB2 : (d1Bcoef W q) ^ 2 ≤ (diagAFK Ks s c0 av M q) ^ 2 := by
    rw [← sq_abs]; exact pow_le_pow_left₀ (abs_nonneg _) hB 2
  exact Commons.Analysis.Real.bogoliubov_coeff_sharp hA hB2

/-- **The COARSE zero-point bound at a free `K_s`.**  In the Fock half-regime
`|ℬ(q)| ≤ (ε/2)·𝒜(q)`,

  `diagKFK ≤ (1+ε/2)·ℬ²/(4𝒜)`,

i.e. FS's `h(p) ≥ −(1/2)(1+ε/2)ℬ²/𝒜·n|B|⁻¹∫χ²` with the sharp `1/2`
(`bog_zero_point_gap_simple`). -/
lemma diagKFK_le_coarse {ε Ks s c0 av M : ℝ} (hs : 0 < s) (hM : 0 ≤ M) (hKs : 0 < Ks)
    (hav : 0 < av) (hε0 : 0 < ε) (hε1 : ε ≤ 1) {W : ℝ³ → ℝ}
    (hF : ∀ q : ℝ³, |d1Bcoef W q| ≤ ε / 2 * diagAFK Ks s c0 av M q) (q : ℝ³) :
    diagKFK Ks s c0 av M W q
      ≤ (1 + ε / 2) * (d1Bcoef W q) ^ 2 / (4 * diagAFK Ks s c0 av M q) := by
  have hA := diagAFK_pos (Ks := Ks) (c0 := c0) hs hM hKs hav q
  have hle := bog_zero_point_gap_simple (A := diagAFK Ks s c0 av M q) (B := d1Bcoef W q)
    hA hε0 hε1 (hF q)
  have hdef : diagKFK Ks s c0 av M W q
      = (diagAFK Ks s c0 av M q - bogS (diagAFK Ks s c0 av M q) (d1Bcoef W q)) / 2 := rfl
  have hhalf : (1 / 2 : ℝ) * (1 / 2 * (1 + ε / 2) * (d1Bcoef W q) ^ 2
        / diagAFK Ks s c0 av M q)
      = (1 + ε / 2) * (d1Bcoef W q) ^ 2 / (4 * diagAFK Ks s c0 av M q) := by ring_nf
  rw [hdef, ← hhalf]
  linarith [hle]

/-- **The coarse bound combined with the `2K_s·a v` floor**:
`diagKFK ≤ (1+ε/2)ℬ²/(8K_s·a v)`, valid at every momentum. -/
lemma diagKFK_le_floor {ε Ks s c0 av M : ℝ} (hs : 0 < s) (hM : 0 ≤ M) (hKs : 0 < Ks)
    (hav : 0 < av) (hε0 : 0 < ε) (hε1 : ε ≤ 1) {W : ℝ³ → ℝ}
    (hF : ∀ q : ℝ³, |d1Bcoef W q| ≤ ε / 2 * diagAFK Ks s c0 av M q) (q : ℝ³) :
    diagKFK Ks s c0 av M W q ≤ (1 + ε / 2) * (d1Bcoef W q) ^ 2 / (8 * Ks * av) := by
  have h1 := diagKFK_le_coarse (ε := ε) (Ks := Ks) (c0 := c0) hs hM hKs hav hε0 hε1 hF q
  have hA := diagAFK_ge_floor (Ks := Ks) (c0 := c0) hs hM (le_of_lt hKs) (le_of_lt hav) q
  have h2 : 0 < diagAFK Ks s c0 av M q := diagAFK_pos hs hM hKs hav q
  have h3 : 0 < 8 * Ks * av := by positivity
  have h4 : 0 ≤ (1 + ε / 2) * (d1Bcoef W q) ^ 2 := by positivity
  have h5 : (1 + ε / 2) * (d1Bcoef W q) ^ 2 / (4 * diagAFK Ks s c0 av M q)
      ≤ (1 + ε / 2) * (d1Bcoef W q) ^ 2 / (8 * Ks * av) :=
    div_le_div_of_nonneg_left h4 (by positivity) (by linarith)
  linarith

end Work.MGroupInput
