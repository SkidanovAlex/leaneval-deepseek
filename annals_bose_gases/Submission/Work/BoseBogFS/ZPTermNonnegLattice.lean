import ChallengeDeps
import Mathlib.Algebra.Order.Star.Real
import Submission.Work.BoseBogFS.ZPLatticeAux
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Work.BoseBogFS.ZPTermNonnegLattice`

**The pointwise nonnegativity of the zero-point summand** `½·𝒵(τ_k + ρŴ₁(k), ρŴ₁(k))`
on the lattice `k ∈ ℓ⁻¹ℤ³`, uniformly in the chemical potential on the admissible
region and in the state (the state does not enter `zpTerm` at all).

The whole content is the pointwise inequality

`0 ≤ τ(k) + ρ·Ŵ₁(k)`   for every `k`,

because `𝒵(A,B) = A − √(A²−B²) ≥ 0` as soon as `A ≥ 0` (no sign of `B` is needed:
`√(A²−B²) ≤ √(A²) = A`); this is `zpBogZeroPoint_nonneg`, a strict weakening of
`Work.BoseB6.bogZeroPoint_nonneg` in the direction that matters here.

That inequality is proved by splitting at the momentum scale `1/R`:

* `R‖k‖ ≤ 1`: `Ŵ₁(k) ≥ (∫W₁)(1 − R²‖k‖²/2) ≥ (∫W₁)/2 > 0` by the support-localised
  quadratic Fourier bound `chat_le_mass_sub_ae` (whose inputs — a.e.-nonnegativity,
  integrability and a.e.-support in `ball 0 R` of `W₁ = g₀/(χ⋆χ)(·/ℓ)` — are the
  elementary `wScaled_g0_*` rows) together with the strict positivity of the mass
  `∫W₁` (`W1fun_mass_pos`).  Since also `τ ≥ 0`, the sum is `≥ 0`.
* `R‖k‖ > 1`: the *kink* domination `τ(k) ≥ (1−ε_T)(‖k‖ − (sℓ)⁻¹)₊²`
  (`tauSm_ge_kink`) gives `τ(k) ≥ 1/(8R²)` once `sℓ ≥ 2R` — which holds on the
  admissible region by `exists_adm_s_mul_ell_ge`, since `sℓ = a(μa³)^{−162/323} → ∞` —
  while the uniform FS bound `|Ŵ₁| ≤ 16πa` (`W1hat_abs_le`) together with `ρ ≤ 2μ`
  gives `ρ|Ŵ₁(k)| ≤ 32πμa ≤ 1/(8R²)`.  The two bounds cancel exactly.

All threshold requirements are of the form "the diluteness `μa³` is small"
(`∃ ε₀ > 0`), which is exactly what the target's `∃ ε₀` asks for; the threshold is an
explicit finite minimum, one factor of which is the closed-form bound
`(1/2)^{1292/23}` making `ε_T ≤ 1/2` (so that the kink bound is not degraded).
-/

noncomputable section

open scoped Real Topology BigOperators

open MeasureTheory Filter Metric

namespace Work.BoseBogFS

open _root_.BoseGases Submission.BoseGases Work.UBB Work.UBBInputs3 Work.BoseBox
open Work.BoseBoxFix Work.BoseFixR

set_option autoImplicit false
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

/-! ## 1. The elementary pointwise layer -/

/-- **`𝒵(A,B) = A − √(A²−B²) ≥ 0` whenever `A ≥ 0`.**  No hypothesis on the sign of
`B` is needed (`√(A²−B²) ≤ √(A²) = A`).  This strictly weakens
`Work.BoseB6.bogZeroPoint_nonneg` for the purpose of a *lower* bound. -/
lemma zpBogZeroPoint_nonneg {A B : ℝ} (hA : 0 ≤ A) :
    0 ≤ Work.BoseB6.bogZeroPoint A B := by
  have h1 : Real.sqrt (A ^ 2 - B ^ 2) ≤ Real.sqrt (A ^ 2) :=
    Real.sqrt_le_sqrt (by nlinarith [sq_nonneg B])
  have h2 : Real.sqrt (A ^ 2) = A := Real.sqrt_sq hA
  unfold Work.BoseB6.bogZeroPoint
  linarith [Real.sqrt_nonneg (A ^ 2 - B ^ 2)]

/-- **`Ŵ₁ ≥ 0` for `R‖k‖ ≤ 1`.**  The support-localised quadratic Fourier bound
`chat_le_mass_sub_ae` at `W₁ = wScaled ℓ (g₀ v h)`, whose mass is strictly positive
(`W1fun_mass_pos`), gives

`Ŵ₁(k) ≥ (∫W₁)·(1 − R²‖k‖²/2) ≥ (∫W₁)/2 > 0`. -/
lemma chat_W1fun_nonneg_small {v : EuclideanSpace ℝ (Fin 3) → ℝ} {h : Work.UBB.ScatSol v}
    {R ℓ : ℝ} (hR : 0 < R) (hv : ∀ x, 0 ≤ v x) (hvrad : _root_.BoseGases.IsRadial v)
    (hv_supp : tsupport v ⊆ Metric.ball 0 R) (hav : 0 < _root_.BoseGases.a v)
    (hRℓ : R ≤ ℓ * Submission.BoseGases.chiR0) (hℓ : 0 < ℓ)
    (k : EuclideanSpace ℝ (Fin 3)) (hk : R * ‖k‖ ≤ 1) :
    0 ≤ Work.BoseFixR.chat (Work.BoseFixR.W1fun v h ℓ) k := by
  -- the three a.e./integrability inputs on `W₁`
  have hWint : MeasureTheory.Integrable (Work.BoseFixR.W1fun v h ℓ) :=
    Submission.BoseGases.wScaled_g0_integrable hR hv_supp h hℓ hRℓ
  have hWnn : ∀ᵐ z : EuclideanSpace ℝ (Fin 3),
      0 ≤ Work.BoseFixR.W1fun v h ℓ z :=
    Submission.BoseGases.wScaled_g0_nonneg_ae hR hv hvrad hv_supp h
  have hWsupp : ∀ᵐ x : EuclideanSpace ℝ (Fin 3),
      R < ‖x‖ → Work.BoseFixR.W1fun v h ℓ x = 0 := by
    refine ae_of_all _ (fun x hx => ?_)
    have h0 : Submission.BoseGases.g0 v h x = 0 :=
      Submission.BoseGases.g0_zero_of_norm_ge hv_supp hx.le h
    simp [Work.BoseFixR.W1fun, Submission.BoseGases.wScaled, h0]
  -- the mass is strictly positive, and the quadratic bound at `R‖k‖ ≤ 1` keeps half of it
  have hmass : 0 < ∫ y : EuclideanSpace ℝ (Fin 3), Work.BoseFixR.W1fun v h ℓ y :=
    W1fun_mass_pos v h hR hv hvrad hv_supp hav hRℓ hℓ
  have hquad := chat_le_mass_sub_ae hWint hR.le hWnn hWsupp k
  have hkey : (1 : ℝ) / 2 ≤ 1 - R ^ 2 * ‖k‖ ^ 2 / 2 := by
    have hx : 0 ≤ R * ‖k‖ := by positivity
    have h2 : R ^ 2 * ‖k‖ ^ 2 ≤ 1 := by nlinarith [hx, hk, sq_nonneg (R * ‖k‖ - 1)]
    nlinarith [h2]
  have hhalf : (0 : ℝ) < (∫ y : EuclideanSpace ℝ (Fin 3), Work.BoseFixR.W1fun v h ℓ y) / 2 := by
    linarith
  refine le_of_lt (lt_of_lt_of_le hhalf ?_)
  calc (∫ y : EuclideanSpace ℝ (Fin 3), Work.BoseFixR.W1fun v h ℓ y) / 2
      = (∫ y : EuclideanSpace ℝ (Fin 3), Work.BoseFixR.W1fun v h ℓ y) * (1 / 2) := by ring
    _ ≤ (∫ y : EuclideanSpace ℝ (Fin 3), Work.BoseFixR.W1fun v h ℓ y)
          * (1 - R ^ 2 * ‖k‖ ^ 2 / 2) :=
        mul_le_mul_of_nonneg_left hkey hmass.le
    _ ≤ Work.BoseFixR.chat (Work.BoseFixR.W1fun v h ℓ) k := hquad

/-! ## 2. The parameter arithmetic -/

/-- **`s·ℓ = a(μa³)^{−162/323}`**, the closed form of the small-box scale product:
`s = (μa³)^{1/323}` and `ℓ = a(μa³)^{−163/323}`. -/
lemma s_mul_ell_eq {v : EuclideanSpace ℝ (Fin 3) → ℝ} {μ : ℝ}
    (hav : 0 < _root_.BoseGases.a v) (hμ : 0 < μ) :
    (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).s * Work.BoseFixR.ell v μ
      = _root_.BoseGases.a v * (μ * (_root_.BoseGases.a v) ^ 3) ^ (-(162 / 323 : ℝ)) := by
  have ht0 : 0 < μ * (_root_.BoseGases.a v) ^ 3 := mul_pos hμ (pow_pos hav 3)
  have hs : (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).s
      = (μ * (_root_.BoseGases.a v) ^ 3) ^ (1 / 323 : ℝ) := by
    simp [Work.BoseBox.paramsAt, Work.BoseBox.fsParams, Work.BoseBox.fsXp]
  have hell : Work.BoseFixR.ell v μ
      = _root_.BoseGases.a v * (μ * (_root_.BoseGases.a v) ^ 3) ^ (-(163 / 323 : ℝ)) := by
    rw [Work.BoseFixR.ell_eq, Work.BoseBox.sideAt_eq_rpow hav hμ]
  rw [hs, hell]
  have hmul : (μ * _root_.BoseGases.a v ^ 3) ^ (1 / 323 : ℝ)
      * (μ * _root_.BoseGases.a v ^ 3) ^ (-(163 / 323) : ℝ)
      = (μ * _root_.BoseGases.a v ^ 3) ^ (-(162 / 323 : ℝ)) := by
    rw [← Real.rpow_add ht0]
    norm_num
  calc (μ * _root_.BoseGases.a v ^ 3) ^ (1 / 323 : ℝ)
        * (_root_.BoseGases.a v * (μ * _root_.BoseGases.a v ^ 3) ^ (-(163 / 323) : ℝ))
      = _root_.BoseGases.a v * ((μ * _root_.BoseGases.a v ^ 3) ^ (1 / 323 : ℝ)
          * (μ * _root_.BoseGases.a v ^ 3) ^ (-(163 / 323) : ℝ)) := by ring
    _ = _root_.BoseGases.a v * (μ * (_root_.BoseGases.a v) ^ 3) ^ (-(162 / 323 : ℝ)) := by
        rw [hmul]

/-- **The small-box scale product `s·ℓ` exceeds any prescribed bound on the admissible
region.**  Since `s·ℓ = a(μa³)^{−162/323}` blows up as the diluteness tends to `0`, the
diluteness threshold `ε₀ = min 1 (M/a)^{−323/162}` works. -/
theorem exists_adm_s_mul_ell_ge {v : EuclideanSpace ℝ (Fin 3) → ℝ}
    (hav : 0 < _root_.BoseGases.a v) {M : ℝ} (hM : 0 < M) :
    ∃ ε₀ : ℝ, 0 < ε₀ ∧ ∀ μ : ℝ, Work.BoseBoxFix.Adm v ε₀ μ →
      M ≤ (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).s * Work.BoseFixR.ell v μ := by
  have hMa : 0 < M / _root_.BoseGases.a v := div_pos hM hav
  refine ⟨min 1 ((M / _root_.BoseGases.a v) ^ (-(323 / 162 : ℝ))),
    lt_min one_pos (Real.rpow_pos_of_pos hMa _), ?_⟩
  intro μ hμ
  have hμpos : 0 < μ := hμ.1
  have ht0 : 0 < μ * (_root_.BoseGases.a v) ^ 3 := mul_pos hμpos (pow_pos hav 3)
  have ht : μ * (_root_.BoseGases.a v) ^ 3 ≤ (M / _root_.BoseGases.a v) ^ (-(323 / 162 : ℝ)) :=
    le_trans hμ.2.1 (min_le_right _ _)
  rw [s_mul_ell_eq hav hμpos]
  have h1 : M / _root_.BoseGases.a v
      ≤ (μ * (_root_.BoseGases.a v) ^ 3) ^ (-(162 / 323 : ℝ)) := by
    have h2 : ((M / _root_.BoseGases.a v) ^ (-(323 / 162 : ℝ))) ^ (-(162 / 323 : ℝ))
        ≤ (μ * (_root_.BoseGases.a v) ^ 3) ^ (-(162 / 323 : ℝ)) :=
      Real.rpow_le_rpow_of_nonpos ht0 ht (by norm_num)
    have h3 : ((M / _root_.BoseGases.a v) ^ (-(323 / 162 : ℝ))) ^ (-(162 / 323 : ℝ))
        = M / _root_.BoseGases.a v := by
      have hmul := Real.rpow_mul (x := M / _root_.BoseGases.a v) hMa.le
        (-(323 / 162 : ℝ)) (-(162 / 323 : ℝ))
      rw [← hmul]
      norm_num
    rwa [h3] at h2
  have h4 := mul_le_mul_of_nonneg_left h1 hav.le
  have h5 : _root_.BoseGases.a v * (M / _root_.BoseGases.a v) = M := by
    field_simp
  linarith [h4, h5]

/-- **`ε_T ≤ 1/2` on a small-diluteness region**: `ε_T = (μa³)^{23/1292}`, so
`μa³ ≤ (1/2)^{1292/23}` suffices. -/
lemma eT_le_half_of_dilute {v : EuclideanSpace ℝ (Fin 3) → ℝ} {μ : ℝ}
    (hav : 0 < _root_.BoseGases.a v) (hμ : 0 < μ)
    (ht : μ * (_root_.BoseGases.a v) ^ 3 ≤ (1 / 2 : ℝ) ^ (1292 / 23 : ℝ)) :
    (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).eT ≤ 1 / 2 := by
  have ht0 : 0 < μ * (_root_.BoseGases.a v) ^ 3 := mul_pos hμ (pow_pos hav 3)
  have he : (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).eT
      = (μ * (_root_.BoseGases.a v) ^ 3) ^ ((23 / 4) / 323 : ℝ) := by
    simp [Work.BoseBox.paramsAt, Work.BoseBox.fsParams, Work.BoseBox.fsXp]
  rw [he]
  have h := Real.rpow_le_rpow ht0.le ht (by norm_num : (0 : ℝ) ≤ (23 / 4) / 323)
  have h2 : ((1 / 2 : ℝ) ^ (1292 / 23 : ℝ)) ^ ((23 / 4) / 323 : ℝ) = 1 / 2 := by
    have hmul := Real.rpow_mul (x := (1 / 2 : ℝ)) (by norm_num) (1292 / 23 : ℝ)
      ((23 / 4) / 323 : ℝ)
    rw [← hmul]
    norm_num
  rw [h2] at h
  exact h

/-- **The pure-real arithmetic of the two-momentum-regime split.**  If the kinetic symbol
dominates its kink, `ρ` is nonnegative and at most `2μ`, the diluteness bound
`μA ≤ 1/(256πR²)` holds, `|W| ≤ 16πA` and `W ≥ 0` on `R‖k‖ ≤ 1`, and `2R ≤ sL`, then
`0 ≤ τ + ρW`.  The constants `256 = 32·8` make `τ ≥ 1/(8R²)` and `ρW ≥ −1/(8R²)` meet
exactly. -/
theorem zpNonnegArith {τ ρ μ A R sL eT W : ℝ} {k : EuclideanSpace ℝ (Fin 3)}
    (hA : 0 < A) (hR : 0 < R) (hsL : 0 < sL) (heT0 : 0 ≤ eT) (heT1 : eT ≤ 1 / 2)
    (hτ : (1 - eT) * (max 0 (‖k‖ - sL⁻¹)) ^ 2 ≤ τ)
    (hρ0 : 0 ≤ ρ) (hρ2 : ρ ≤ 2 * μ)
    (hμA : μ * A ≤ 1 / (256 * Real.pi * R ^ 2))
    (hWglob : |W| ≤ 16 * Real.pi * A)
    (hWpos : R * ‖k‖ ≤ 1 → 0 ≤ W)
    (hsl : 2 * R ≤ sL) :
    0 ≤ τ + ρ * W := by
  -- the `ρW` bound is regime-independent
  have hρW : -(32 * Real.pi * μ * A) ≤ ρ * W := by
    have hWge : -(16 * Real.pi * A) ≤ W := (abs_le.mp hWglob).1
    have h1 := mul_le_mul_of_nonneg_left hWge hρ0
    have h2 : ρ * (16 * Real.pi * A) ≤ (2 * μ) * (16 * Real.pi * A) :=
      mul_le_mul_of_nonneg_right hρ2 (by positivity)
    linarith
  have hμA' : 32 * Real.pi * μ * A ≤ 1 / (8 * R ^ 2) := by
    have h1 := mul_le_mul_of_nonneg_left hμA (by positivity : (0 : ℝ) ≤ 32 * Real.pi)
    have h2 : 32 * Real.pi * (1 / (256 * Real.pi * R ^ 2)) = 1 / (8 * R ^ 2) := by
      field_simp
      norm_num
    linarith [h1, h2]
  rcases le_or_gt (R * ‖k‖) 1 with hk | hk
  · -- small momentum: `W ≥ 0` and `τ ≥ 0`
    have hW : 0 ≤ W := hWpos hk
    have hτ0 : 0 ≤ τ := by
      have h1 : 0 ≤ 1 - eT := by linarith
      have h2 : 0 ≤ (max 0 (‖k‖ - sL⁻¹)) ^ 2 := sq_nonneg _
      nlinarith [mul_nonneg h1 h2]
    nlinarith [mul_nonneg hρ0 hW]
  · -- large momentum: `τ ≳ 1/(8R²)` beats `ρ|W| ≤ 1/(8R²)`
    have hk1 : 1 / R < ‖k‖ := by
      rw [div_lt_iff₀ hR]
      linarith
    have hsLinv : sL⁻¹ ≤ 1 / (2 * R) := by
      have h := one_div_le_one_div_of_le (by positivity : (0 : ℝ) < 2 * R) hsl
      simpa [one_div] using h
    have hp : (0 : ℝ) < 1 / (2 * R) := by positivity
    have h2R : 1 / R = 2 * (1 / (2 * R)) := by field_simp
    have hhalf : 1 / (2 * R) ≤ ‖k‖ - sL⁻¹ := by
      have h1 : 1 / (2 * R) < ‖k‖ := by linarith [hk1, h2R, hp]
      linarith [hsLinv, h1]
    have hmax : 1 / (2 * R) ≤ max 0 (‖k‖ - sL⁻¹) := by
      have h0 : 0 ≤ ‖k‖ - sL⁻¹ := by linarith [hhalf, hp]
      rw [max_eq_right h0]
      exact hhalf
    have hτlb : 1 / (8 * R ^ 2) ≤ τ := by
      have h1 : (1 : ℝ) / 2 ≤ 1 - eT := by linarith
      have h2 : (1 / (2 * R)) ^ 2 ≤ (max 0 (‖k‖ - sL⁻¹)) ^ 2 :=
        pow_le_pow_left₀ (le_of_lt hp) hmax 2
      have h3 : (1 / 2 : ℝ) * (1 / (2 * R)) ^ 2 = 1 / (8 * R ^ 2) := by
        field_simp
        norm_num
      have h4 : (1 / 2 : ℝ) * (1 / (2 * R)) ^ 2
          ≤ (1 - eT) * (max 0 (‖k‖ - sL⁻¹)) ^ 2 :=
        mul_le_mul h1 h2 (sq_nonneg _) (by linarith)
      linarith [h4, h3]
    linarith [hτlb, hρW, hμA']

/-! ## 3. The target -/

theorem ZPTermNonnegLattice :
    ∀ {v : EuclideanSpace ℝ (Fin 3) → ℝ} {h : Work.UBB.ScatSol v} {R : ℝ},
      0 < R → (∀ x, 0 ≤ v x) → _root_.BoseGases.IsRadial v →
      tsupport v ⊆ Metric.ball 0 R → 0 < _root_.BoseGases.a v →
      ∃ ε₀ : ℝ, 0 < ε₀ ∧ ∀ μ : ℝ, Work.BoseBoxFix.Adm v ε₀ μ → ∀ ρ : ℝ,
        Work.BoseBoxFock.CloseCondFS v μ ρ →
        ∀ n : Fin 3 → ℤ, 0 ≤ Work.BoseBogFS.zpTerm v h ρ μ n := by
  intro v h R hR hv hvrad hv_supp hav
  have hχpos : 0 < Submission.BoseGases.chiR0 := Submission.BoseGases.chiR0_pos
  -- the two regime thresholds for the box side and for the scale product `s·ℓ`
  obtain ⟨ε₁, hε₁pos, hε₁⟩ :=
    exists_adm_ell_ge (v := v) hav (M := R / Submission.BoseGases.chiR0) (div_pos hR hχpos)
  obtain ⟨ε₂, hε₂pos, hε₂⟩ :=
    exists_adm_s_mul_ell_ge (v := v) hav (M := 2 * R) (by linarith)
  have hcpos : 0 < (_root_.BoseGases.a v) ^ 2 / (256 * Real.pi * R ^ 2) := by positivity
  refine ⟨min (min ε₁ ε₂)
      (min ((1 / 2 : ℝ) ^ (1292 / 23 : ℝ))
        (min 1 ((_root_.BoseGases.a v) ^ 2 / (256 * Real.pi * R ^ 2)))), ?_, ?_⟩
  · refine lt_min (lt_min hε₁pos hε₂pos)
      (lt_min (Real.rpow_pos_of_pos (by norm_num) _) (lt_min one_pos hcpos))
  · intro μ hAdm ρ hclose n
    rw [zpTerm]
    set k := kAt v μ n with hk_def
    have hμ : 0 < μ := hAdm.1
    -- the diluteness thresholds in the target's nested-minimum form
    have ht1 : μ * (_root_.BoseGases.a v) ^ 3 ≤ ε₁ :=
      le_trans hAdm.2.1 (le_trans (min_le_left _ _) (min_le_left _ _))
    have ht2 : μ * (_root_.BoseGases.a v) ^ 3 ≤ ε₂ :=
      le_trans hAdm.2.1 (le_trans (min_le_left _ _) (min_le_right _ _))
    have ht3 : μ * (_root_.BoseGases.a v) ^ 3 ≤ (1 / 2 : ℝ) ^ (1292 / 23 : ℝ) :=
      le_trans hAdm.2.1 (le_trans (min_le_right _ _) (min_le_left _ _))
    have ht4 : μ * (_root_.BoseGases.a v) ^ 3
        ≤ (_root_.BoseGases.a v) ^ 2 / (256 * Real.pi * R ^ 2) :=
      le_trans hAdm.2.1
        (le_trans (min_le_right _ _) (le_trans (min_le_right _ _) (min_le_right _ _)))
    -- `Adm` at the two individual thresholds
    have hadm₁ : Work.BoseBoxFix.Adm v ε₁ μ := ⟨hμ, ht1, hAdm.2.2⟩
    have hadm₂ : Work.BoseBoxFix.Adm v ε₂ μ := ⟨hμ, ht2, hAdm.2.2⟩
    have hε₀1 : min (min ε₁ ε₂)
        (min ((1 / 2 : ℝ) ^ (1292 / 23 : ℝ))
          (min 1 ((_root_.BoseGases.a v) ^ 2 / (256 * Real.pi * R ^ 2)))) ≤ 1 :=
      le_trans (min_le_right _ _) (le_trans (min_le_right _ _) (min_le_left _ _))
    have hRℓ : R ≤ Work.BoseFixR.ell v μ * Submission.BoseGases.chiR0 := by
      have h0 : R / Submission.BoseGases.chiR0 ≤ Work.BoseFixR.ell v μ := hε₁ μ hadm₁
      rw [div_le_iff₀ hχpos] at h0
      linarith
    have hsl : 2 * R
        ≤ (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).s * Work.BoseFixR.ell v μ :=
      hε₂ μ hadm₂
    have heT1 : (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).eT ≤ 1 / 2 :=
      eT_le_half_of_dilute hav hμ ht3
    have hspos : 0 < (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).s := by
      have := Work.BoseBox.fsXp_pos (t := μ * (_root_.BoseGases.a v) ^ 3) (c := 1)
        (mul_pos hμ (pow_pos hav 3))
      simpa [Work.BoseBox.paramsAt, Work.BoseBox.fsParams, Work.BoseBox.fsXp] using this
    have hdpos : 0 < (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).d := by
      have := Work.BoseBox.fsXp_pos (t := μ * (_root_.BoseGases.a v) ^ 3) (c := 6)
        (mul_pos hμ (pow_pos hav 3))
      simpa [Work.BoseBox.paramsAt, Work.BoseBox.fsParams, Work.BoseBox.fsXp] using this
    have heT0 : 0 ≤ (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).eT := by
      have := Work.BoseBox.fsXp_pos (t := μ * (_root_.BoseGases.a v) ^ 3) (c := 23 / 4)
        (mul_pos hμ (pow_pos hav 3))
      simpa [Work.BoseBox.paramsAt, Work.BoseBox.fsParams, Work.BoseBox.fsXp] using this.le
    have hℓ : 0 < Work.BoseFixR.ell v μ := by
      have h0 : 0 < R / Submission.BoseGases.chiR0 := div_pos hR hχpos
      have h1 : R / Submission.BoseGases.chiR0 ≤ Work.BoseFixR.ell v μ := by
        rw [div_le_iff₀ hχpos]
        linarith [hRℓ]
      linarith
    have hμA : μ * _root_.BoseGases.a v ≤ 1 / (256 * Real.pi * R ^ 2) := by
      have ha2 : 0 < (_root_.BoseGases.a v) ^ 2 := pow_pos hav 2
      have h1 : μ * _root_.BoseGases.a v
          = (μ * (_root_.BoseGases.a v) ^ 3) / (_root_.BoseGases.a v) ^ 2 := by
        field_simp
      have h2 : (μ * (_root_.BoseGases.a v) ^ 3) / (_root_.BoseGases.a v) ^ 2
          ≤ ((_root_.BoseGases.a v) ^ 2 / (256 * Real.pi * R ^ 2))
            / (_root_.BoseGases.a v) ^ 2 :=
        div_le_div_of_nonneg_right ht4 ha2.le
      have h3 : ((_root_.BoseGases.a v) ^ 2 / (256 * Real.pi * R ^ 2))
            / (_root_.BoseGases.a v) ^ 2 = 1 / (256 * Real.pi * R ^ 2) := by
        field_simp
      rw [h1]
      rw [h3] at h2
      exact h2
    -- the two pointwise rows at the lattice momentum
    have hWglob : |Work.BoseFixR.chat (Work.BoseFixR.W1fun v h (Work.BoseFixR.ell v μ)) k|
        ≤ 16 * Real.pi * _root_.BoseGases.a v :=
      Work.BoseB7AK.W1rows.W1hat_abs_le hR hℓ hv hvrad hv_supp h hRℓ k
    have hτ : (1 - (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).eT)
        * (max 0 (‖k‖ - ((Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).s
            * Work.BoseFixR.ell v μ)⁻¹)) ^ 2
        ≤ tauAt v μ k :=
      tauSm_ge_kink heT0 (le_trans heT1 (by norm_num)) hspos hdpos hℓ k
    have hsum : 0 ≤ tauAt v μ k + cAt v h ρ μ k := by
      have hA := zpNonnegArith (τ := tauAt v μ k) (ρ := ρ) (μ := μ)
        (A := _root_.BoseGases.a v) (R := R)
        (sL := (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).s * Work.BoseFixR.ell v μ)
        (eT := (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).eT)
        (W := Work.BoseFixR.chat (Work.BoseFixR.W1fun v h (Work.BoseFixR.ell v μ)) k)
        hav hR (mul_pos hspos hℓ) heT0 heT1 hτ
        (rho_pos_of_close v hε₀1 hav hAdm hclose).le
        (rho_le_two_of_close v hε₀1 hav hAdm hclose) hμA hWglob
        (fun hk => chat_W1fun_nonneg_small hR hv hvrad hv_supp hav hRℓ hℓ k hk) hsl
      simpa [cAt, W1At] using hA
    exact mul_nonneg (by norm_num) (zpBogZeroPoint_nonneg hsum)

end Work.BoseBogFS
