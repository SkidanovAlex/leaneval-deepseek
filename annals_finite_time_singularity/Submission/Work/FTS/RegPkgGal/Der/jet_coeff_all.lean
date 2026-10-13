import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Submission.Work.FTS.Regularity.Defs
import Submission.Work.FTS.RegPkgGal.Der.rhs_jet_aux
import Submission.Work.FTS.RegPkgGal.Der.Lib.holder_of_lipschitz_of_bounded
import Submission.Work.Spaces.Gam_bounds
import Submission.Work.Spaces.c_bounds

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# `Work.FTS.RegPkgGal.Der.jet_coeff_all`

The six explicit coefficient functions of the fake-time right-hand side of the modulation
(`Work.FTS.RegPkgGal.Der.rhs_jet_of_parts`) are `Jet`s on the strip `z ≥ 0`, `θ ∈ Iθ`,
`τ ∈ [0,S]`:

* `z ↦ 2z/(1+z)²` and `θ ↦ Γ(θ)/c` — the two factors of the profile `F_*`;
* `z ↦ 2/(1+z)`, `z ↦ 3/(1+z)` — the two radial factors of `L₁₂(F_*)` and of `N₀`;
* the products `2z Γ(θ)/(c(1+z)²)` and `AK = (Γ(θ)/c)·2z²/(1+z)³`.

None of the six depends on `τ`, so the only content is that each is *bounded* on
`[0,∞) × Iθ` and `α`-Hölder there for the metric `|Δz| + |Δθ|`; the `τ`-modulus is the trivial
one (the exponent `α ∈ (0,1]` is monotone).

The proof is a single general principle, `jet_of_zθ`: a function `A z θ` of `(z,θ)` alone which
is bounded by `M` and `α`-Hölder with constant `K` for `|Δz| + |Δθ|` is a `Jet` with any constant
`N ≥ K` and `N ≥ 2M` — because two points at distance `≥ 1` in the metric are handled by the sup
bound and two points at distance `≤ 1` by the Hölder bound.  The explicit functions are then
bounded and Hölder by elementary calculus: three rational functions of `z`
(`jca_z_facts`), the angular factor `Γ/c` (`jca_gam_div_c_bdd` + the already available
`rhsJet_gam_div_c_holder`), and the two products (`jca_zgam_facts`, `rhsJet_ak_bounds`).

All constants are the displayed ones (generous, but explicit).
-/

namespace Work.FTS.RegPkgGal.Der

open scoped Real Topology
open Set Filter

set_option autoImplicit false
set_option linter.unusedVariables false

/-! ## The general `Jet`-closure principle -/

/-- **A function of `(z,θ)` alone which is bounded and `α`-Hölder is a `Jet`.**  If
`|A z θ| ≤ M` on `z ≥ 0`, `θ ∈ Iθ` and `|A z θ - A z' θ'| ≤ K (|Δz| + |Δθ|)^α`, then
`(z,θ,τ) ↦ A z θ` is a `Jet` with any constant `N ≥ K`, `N ≥ 2M`. -/
theorem jet_of_zθ {α S N M K : ℝ} {A : ℝ → ℝ → ℝ} (hα : 0 < α)
    (hM : 0 ≤ M) (hK : 0 ≤ K) (hN : 0 ≤ N) (hKN : K ≤ N) (hMN : 2 * M ≤ N)
    (hbdd : ∀ z : ℝ, 0 ≤ z → ∀ θ ∈ Work.Spaces.Iθ, |A z θ| ≤ M)
    (hhld : ∀ z z' : ℝ, 0 ≤ z → 0 ≤ z' → ∀ θ ∈ Work.Spaces.Iθ, ∀ θ' ∈ Work.Spaces.Iθ,
      |A z θ - A z' θ'| ≤ K * (|z - z'| + |θ - θ'|) ^ α) :
    Work.FTS.Regularity.Jet α S N (fun z θ _ => A z θ) := by
  have hMN' : M ≤ N := by linarith
  refine ⟨hN, ?_, ?_⟩
  · intro z θ τ hz hθ hτ
    exact le_trans (hbdd z hz θ hθ) hMN'
  · intro z z' θ θ' τ τ' hz hz' hθ hθ' hτ hτ'
    have he : (0 : ℝ) ≤ |z - z'| + |θ - θ'| := by positivity
    have hd : (0 : ℝ) ≤ |z - z'| + |θ - θ'| + |τ - τ'| := by positivity
    have hmono : (|z - z'| + |θ - θ'|) ^ α ≤ (|z - z'| + |θ - θ'| + |τ - τ'|) ^ α :=
      Real.rpow_le_rpow he (by linarith [abs_nonneg (τ - τ')]) hα.le
    have h0 : (0 : ℝ) ≤ (|z - z'| + |θ - θ'| + |τ - τ'|) ^ α := Real.rpow_nonneg hd α
    calc |A z θ - A z' θ'| ≤ K * (|z - z'| + |θ - θ'|) ^ α := hhld z z' hz hz' θ hθ θ' hθ'
      _ ≤ K * (|z - z'| + |θ - θ'| + |τ - τ'|) ^ α := mul_le_mul_of_nonneg_left hmono hK
      _ ≤ N * (|z - z'| + |θ - θ'| + |τ - τ'|) ^ α := mul_le_mul_of_nonneg_right hKN h0

/-- The radial special case of `jet_of_zθ`: a function of `z` alone. -/
theorem jet_of_z {α S N M K : ℝ} {f : ℝ → ℝ} (hα : 0 < α)
    (hM : 0 ≤ M) (hK : 0 ≤ K) (hN : 0 ≤ N) (hKN : K ≤ N) (hMN : 2 * M ≤ N)
    (hbdd : ∀ z : ℝ, 0 ≤ z → |f z| ≤ M)
    (hhld : ∀ z z' : ℝ, 0 ≤ z → 0 ≤ z' → |f z - f z'| ≤ K * |z - z'| ^ α) :
    Work.FTS.Regularity.Jet α S N (fun z _ _ => f z) := by
  refine jet_of_zθ (A := fun z _ => f z) hα hM hK hN hKN hMN ?_ ?_
  · intro z hz θ hθ
    exact hbdd z hz
  · intro z z' hz hz' θ hθ θ' hθ'
    refine le_trans (hhld z z' hz hz') (mul_le_mul_of_nonneg_left ?_ hK)
    exact Real.rpow_le_rpow (abs_nonneg _) (by linarith [abs_nonneg (θ - θ')]) hα.le

/-- The angular special case of `jet_of_zθ`: a function of `θ` alone. -/
theorem jet_of_θ {α S N M K : ℝ} {g : ℝ → ℝ} (hα : 0 < α)
    (hM : 0 ≤ M) (hK : 0 ≤ K) (hN : 0 ≤ N) (hKN : K ≤ N) (hMN : 2 * M ≤ N)
    (hbdd : ∀ θ ∈ Work.Spaces.Iθ, |g θ| ≤ M)
    (hhld : ∀ θ ∈ Work.Spaces.Iθ, ∀ θ' ∈ Work.Spaces.Iθ, |g θ - g θ'| ≤ K * |θ - θ'| ^ α) :
    Work.FTS.Regularity.Jet α S N (fun _ θ _ => g θ) := by
  refine jet_of_zθ (A := fun _ θ => g θ) hα hM hK hN hKN hMN ?_ ?_
  · intro z hz θ hθ
    exact hbdd θ hθ
  · intro z z' hz hz' θ hθ θ' hθ'
    refine le_trans (hhld θ hθ θ' hθ') (mul_le_mul_of_nonneg_left ?_ hK)
    exact Real.rpow_le_rpow (abs_nonneg _) (by linarith [abs_nonneg (z - z')]) hα.le

/-! ## The three radial coefficients -/

/-- Bounds and Lipschitz constants of the three rational coefficients
`2z/(1+z)²`, `2/(1+z)`, `3/(1+z)` on `[0,∞)`.  (The parameters `α ≤ 1` are the ambient ones of
the `Jet`-conversion; they are not used here.) -/
theorem jca_z_facts {α : ℝ} (hα : 0 < α) (hα1 : α ≤ 1) :
    (∀ z : ℝ, 0 ≤ z → |2 * z / (1 + z) ^ 2| ≤ 1) ∧
    (∀ z : ℝ, 0 ≤ z → |2 / (1 + z)| ≤ 2) ∧
    (∀ z : ℝ, 0 ≤ z → |3 / (1 + z)| ≤ 3) ∧
    (∀ z z' : ℝ, 0 ≤ z → 0 ≤ z' →
      |2 * z / (1 + z) ^ 2 - 2 * z' / (1 + z') ^ 2| ≤ 2 * |z - z'|) ∧
    (∀ z z' : ℝ, 0 ≤ z → 0 ≤ z' → |2 / (1 + z) - 2 / (1 + z')| ≤ 2 * |z - z'|) ∧
    (∀ z z' : ℝ, 0 ≤ z → 0 ≤ z' → |3 / (1 + z) - 3 / (1 + z')| ≤ 3 * |z - z'|) := by
  have hb1 : ∀ z : ℝ, 0 ≤ z → |2 * z / (1 + z) ^ 2| ≤ 1 := by
    intro z hz
    have h1 : (0 : ℝ) < (1 + z) ^ 2 := by positivity
    have h2 : (0 : ℝ) ≤ 2 * z := by positivity
    rw [abs_of_nonneg (div_nonneg h2 h1.le), div_le_iff₀ h1]
    nlinarith [hz, sq_nonneg z]
  have hb2 : ∀ z : ℝ, 0 ≤ z → |2 / (1 + z)| ≤ 2 := by
    intro z hz
    have h1 : (0 : ℝ) < 1 + z := by linarith
    rw [abs_of_nonneg (div_nonneg (by norm_num) h1.le), div_le_iff₀ h1]
    linarith
  have hb3 : ∀ z : ℝ, 0 ≤ z → |3 / (1 + z)| ≤ 3 := by
    intro z hz
    have h1 : (0 : ℝ) < 1 + z := by linarith
    rw [abs_of_nonneg (div_nonneg (by norm_num) h1.le), div_le_iff₀ h1]
    linarith
  have hlip1 : ∀ z z' : ℝ, 0 ≤ z → 0 ≤ z' →
      |2 * z / (1 + z) ^ 2 - 2 * z' / (1 + z') ^ 2| ≤ 2 * |z - z'| := by
    intro z z' hz hz'
    have h1 : (0 : ℝ) < (1 + z) ^ 2 := by positivity
    have h2 : (0 : ℝ) < (1 + z') ^ 2 := by positivity
    have hden : (0 : ℝ) < (1 + z) ^ 2 * (1 + z') ^ 2 := mul_pos h1 h2
    have hfac : 2 * z / (1 + z) ^ 2 - 2 * z' / (1 + z') ^ 2
        = 2 * (z - z') * (1 - z * z') / ((1 + z) ^ 2 * (1 + z') ^ 2) := by
      field_simp
      ring
    have hb : |1 - z * z'| ≤ (1 + z) * (1 + z') := by
      rw [abs_le]
      constructor <;> nlinarith [hz, hz', mul_nonneg hz hz']
    have hb2 : (1 + z) * (1 + z') ≤ (1 + z) ^ 2 * (1 + z') ^ 2 := by
      nlinarith [hz, hz', sq_nonneg z, sq_nonneg z']
    rw [hfac, abs_div, abs_of_pos hden, div_le_iff₀ hden]
    have h2n : (0 : ℝ) ≤ 2 * |z - z'| := by positivity
    calc |2 * (z - z') * (1 - z * z')|
        = 2 * |z - z'| * |1 - z * z'| := by
          rw [abs_mul, abs_mul, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 2)]
      _ ≤ 2 * |z - z'| * ((1 + z) * (1 + z')) := mul_le_mul_of_nonneg_left hb h2n
      _ ≤ 2 * |z - z'| * ((1 + z) ^ 2 * (1 + z') ^ 2) := mul_le_mul_of_nonneg_left hb2 h2n
  have hlip2 : ∀ z z' : ℝ, 0 ≤ z → 0 ≤ z' → |2 / (1 + z) - 2 / (1 + z')| ≤ 2 * |z - z'| := by
    intro z z' hz hz'
    have h1 : (0 : ℝ) < 1 + z := by linarith
    have h2 : (0 : ℝ) < 1 + z' := by linarith
    have hden : (0 : ℝ) < (1 + z) * (1 + z') := mul_pos h1 h2
    have hfac : 2 / (1 + z) - 2 / (1 + z') = 2 * (z' - z) / ((1 + z) * (1 + z')) := by
      field_simp
      ring
    have hge : (1 : ℝ) ≤ (1 + z) * (1 + z') := by nlinarith [hz, hz']
    rw [hfac, abs_div, abs_of_pos hden, div_le_iff₀ hden, abs_mul,
      abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 2), abs_sub_comm z' z]
    have h2n : (0 : ℝ) ≤ 2 * |z - z'| := by positivity
    calc 2 * |z - z'| = 2 * |z - z'| * 1 := by ring
      _ ≤ 2 * |z - z'| * ((1 + z) * (1 + z')) := mul_le_mul_of_nonneg_left hge h2n
  have hlip3 : ∀ z z' : ℝ, 0 ≤ z → 0 ≤ z' → |3 / (1 + z) - 3 / (1 + z')| ≤ 3 * |z - z'| := by
    intro z z' hz hz'
    have h1 : (0 : ℝ) < 1 + z := by linarith
    have h2 : (0 : ℝ) < 1 + z' := by linarith
    have hden : (0 : ℝ) < (1 + z) * (1 + z') := mul_pos h1 h2
    have hfac : 3 / (1 + z) - 3 / (1 + z') = 3 * (z' - z) / ((1 + z) * (1 + z')) := by
      field_simp
      ring
    have hge : (1 : ℝ) ≤ (1 + z) * (1 + z') := by nlinarith [hz, hz']
    rw [hfac, abs_div, abs_of_pos hden, div_le_iff₀ hden, abs_mul,
      abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 3), abs_sub_comm z' z]
    have h2n : (0 : ℝ) ≤ 3 * |z - z'| := by positivity
    calc 3 * |z - z'| = 3 * |z - z'| * 1 := by ring
      _ ≤ 3 * |z - z'| * ((1 + z) * (1 + z')) := mul_le_mul_of_nonneg_left hge h2n
  exact ⟨hb1, hb2, hb3, hlip1, hlip2, hlip3⟩

/-! ## The angular coefficient `Γ/c` -/

/-- The bound `|Γ(θ)/c| ≤ 10` on `Iθ`: `Γ ≤ 1` and `c ≥ 1/10`. -/
theorem jca_gam_div_c_bdd {α : ℝ} (hα : 0 < α) (hα13 : α ≤ 1 / 3) :
    ∀ θ ∈ Work.Spaces.Iθ,
      |Work.Spaces.Gam (Work.FTS.Regularity.pExp α) θ
        / Work.Spaces.c (Work.FTS.Regularity.pExp α)| ≤ 10 := by
  have hP : 0 < Work.FTS.Regularity.pExp α := Work.FTS.Regularity.pExp_pos hα
  have hP1 : Work.FTS.Regularity.pExp α ≤ 1 := Work.FTS.Regularity.pExp_le_one hα13
  obtain ⟨hc1, hc10⟩ := Work.Spaces.c_bounds (Work.FTS.Regularity.pExp α) hP hP1
  have hcpos : 0 < Work.Spaces.c (Work.FTS.Regularity.pExp α) := by linarith
  intro θ hθ
  obtain ⟨hG0, hG1⟩ := Work.Spaces.Gam_bounds (Work.FTS.Regularity.pExp α) θ hP hθ
  rw [abs_of_nonneg (div_nonneg hG0 hcpos.le), div_le_iff₀ hcpos]
  nlinarith [hG1, hc1]

/-- The `α`-Hölder modulus `40` of `Γ/c` on `Iθ` (from `rhsJet_gam_div_c_holder`). -/
theorem jca_gam_div_c_holder {α : ℝ} (hα : 0 < α) (hα13 : α ≤ 1 / 3) :
    ∀ θ ∈ Work.Spaces.Iθ, ∀ θ' ∈ Work.Spaces.Iθ,
      |Work.Spaces.Gam (Work.FTS.Regularity.pExp α) θ
          / Work.Spaces.c (Work.FTS.Regularity.pExp α)
        - Work.Spaces.Gam (Work.FTS.Regularity.pExp α) θ'
          / Work.Spaces.c (Work.FTS.Regularity.pExp α)| ≤ 40 * |θ - θ'| ^ α :=
  fun θ hθ θ' hθ' => rhsJet_gam_div_c_holder hα hα13 hθ hθ'

/-! ## The product `2z Γ(θ)/(c(1+z)²)` -/

/-- Bounds and `α`-Hölder modulus of `(z,θ) ↦ 2z Γ(θ)/(c(1+z)²)`: bounded by `10` and
`α`-Hölder with constant `60` for the metric `|Δz| + |Δθ|`. -/
theorem jca_zgam_facts {α : ℝ} (hα : 0 < α) (hα13 : α ≤ 1 / 3) :
    (∀ z : ℝ, 0 ≤ z → ∀ θ ∈ Work.Spaces.Iθ,
      |2 * z * Work.Spaces.Gam (Work.FTS.Regularity.pExp α) θ
        / (Work.Spaces.c (Work.FTS.Regularity.pExp α) * (1 + z) ^ 2)| ≤ 10) ∧
    (∀ z z' : ℝ, 0 ≤ z → 0 ≤ z' → ∀ θ ∈ Work.Spaces.Iθ, ∀ θ' ∈ Work.Spaces.Iθ,
      |2 * z * Work.Spaces.Gam (Work.FTS.Regularity.pExp α) θ
          / (Work.Spaces.c (Work.FTS.Regularity.pExp α) * (1 + z) ^ 2)
        - 2 * z' * Work.Spaces.Gam (Work.FTS.Regularity.pExp α) θ'
          / (Work.Spaces.c (Work.FTS.Regularity.pExp α) * (1 + z') ^ 2)|
      ≤ 60 * (|z - z'| + |θ - θ'|) ^ α) := by
  have hα1 : α ≤ 1 := by linarith
  obtain ⟨hb1, -, -, hlip1, -, -⟩ := jca_z_facts hα hα1
  have hh1 : ∀ z z' : ℝ, 0 ≤ z → 0 ≤ z' →
      |2 * z / (1 + z) ^ 2 - 2 * z' / (1 + z') ^ 2| ≤ 2 * |z - z'| ^ α := by
    intro z z' hz hz'
    have h := Lib.holder_of_lipschitz_of_bounded (f := fun w : ℝ => 2 * w / (1 + w) ^ 2)
      hα hα1 (by norm_num) (by norm_num) hlip1 hb1 z z' hz hz'
    have hmax : max (2 : ℝ) (2 * 1) = 2 := by norm_num
    rwa [hmax] at h
  have hFb := jca_gam_div_c_bdd hα hα13
  have hFh := jca_gam_div_c_holder hα hα13
  constructor
  · intro z hz θ hθ
    have heq : 2 * z * Work.Spaces.Gam (Work.FTS.Regularity.pExp α) θ
          / (Work.Spaces.c (Work.FTS.Regularity.pExp α) * (1 + z) ^ 2)
        = (2 * z / (1 + z) ^ 2) * (Work.Spaces.Gam (Work.FTS.Regularity.pExp α) θ
            / Work.Spaces.c (Work.FTS.Regularity.pExp α)) := by
      field_simp
    rw [heq, abs_mul]
    calc |2 * z / (1 + z) ^ 2| * |Work.Spaces.Gam (Work.FTS.Regularity.pExp α) θ
            / Work.Spaces.c (Work.FTS.Regularity.pExp α)|
        ≤ 1 * 10 := mul_le_mul (hb1 z hz) (hFb θ hθ) (abs_nonneg _) (by norm_num)
      _ = 10 := by norm_num
  · intro z z' hz hz' θ hθ θ' hθ'
    have heq : 2 * z * Work.Spaces.Gam (Work.FTS.Regularity.pExp α) θ
            / (Work.Spaces.c (Work.FTS.Regularity.pExp α) * (1 + z) ^ 2)
          - 2 * z' * Work.Spaces.Gam (Work.FTS.Regularity.pExp α) θ'
            / (Work.Spaces.c (Work.FTS.Regularity.pExp α) * (1 + z') ^ 2)
        = (2 * z / (1 + z) ^ 2) * (Work.Spaces.Gam (Work.FTS.Regularity.pExp α) θ
              / Work.Spaces.c (Work.FTS.Regularity.pExp α))
          - (2 * z' / (1 + z') ^ 2) * (Work.Spaces.Gam (Work.FTS.Regularity.pExp α) θ'
              / Work.Spaces.c (Work.FTS.Regularity.pExp α)) := by
      field_simp
    have hsplit : (2 * z / (1 + z) ^ 2) * (Work.Spaces.Gam (Work.FTS.Regularity.pExp α) θ
              / Work.Spaces.c (Work.FTS.Regularity.pExp α))
          - (2 * z' / (1 + z') ^ 2) * (Work.Spaces.Gam (Work.FTS.Regularity.pExp α) θ'
              / Work.Spaces.c (Work.FTS.Regularity.pExp α))
        = (2 * z / (1 + z) ^ 2) * (Work.Spaces.Gam (Work.FTS.Regularity.pExp α) θ
              / Work.Spaces.c (Work.FTS.Regularity.pExp α)
            - Work.Spaces.Gam (Work.FTS.Regularity.pExp α) θ'
              / Work.Spaces.c (Work.FTS.Regularity.pExp α))
          + (2 * z / (1 + z) ^ 2 - 2 * z' / (1 + z') ^ 2)
            * (Work.Spaces.Gam (Work.FTS.Regularity.pExp α) θ'
              / Work.Spaces.c (Work.FTS.Regularity.pExp α)) := by
      ring
    rw [heq, hsplit]
    have hA : |(2 * z / (1 + z) ^ 2) * (Work.Spaces.Gam (Work.FTS.Regularity.pExp α) θ
            / Work.Spaces.c (Work.FTS.Regularity.pExp α)
          - Work.Spaces.Gam (Work.FTS.Regularity.pExp α) θ'
            / Work.Spaces.c (Work.FTS.Regularity.pExp α))| ≤ 1 * (40 * |θ - θ'| ^ α) := by
      rw [abs_mul]
      exact mul_le_mul (hb1 z hz) (hFh θ hθ θ' hθ') (abs_nonneg _) (by norm_num)
    have hB : |(2 * z / (1 + z) ^ 2 - 2 * z' / (1 + z') ^ 2)
          * (Work.Spaces.Gam (Work.FTS.Regularity.pExp α) θ'
            / Work.Spaces.c (Work.FTS.Regularity.pExp α))| ≤ (2 * |z - z'| ^ α) * 10 := by
      rw [abs_mul]
      exact mul_le_mul (hh1 z z' hz hz') (hFb θ' hθ') (abs_nonneg _) (by positivity)
    have hd0 : (0 : ℝ) ≤ |z - z'| + |θ - θ'| := by positivity
    have hzd : |z - z'| ^ α ≤ (|z - z'| + |θ - θ'|) ^ α :=
      Real.rpow_le_rpow (abs_nonneg _) (by linarith [abs_nonneg (θ - θ')]) hα.le
    have hθd : |θ - θ'| ^ α ≤ (|z - z'| + |θ - θ'|) ^ α :=
      Real.rpow_le_rpow (abs_nonneg _) (by linarith [abs_nonneg (z - z')]) hα.le
    calc |(2 * z / (1 + z) ^ 2) * (Work.Spaces.Gam (Work.FTS.Regularity.pExp α) θ
              / Work.Spaces.c (Work.FTS.Regularity.pExp α)
            - Work.Spaces.Gam (Work.FTS.Regularity.pExp α) θ'
              / Work.Spaces.c (Work.FTS.Regularity.pExp α))
          + (2 * z / (1 + z) ^ 2 - 2 * z' / (1 + z') ^ 2)
            * (Work.Spaces.Gam (Work.FTS.Regularity.pExp α) θ'
              / Work.Spaces.c (Work.FTS.Regularity.pExp α))|
        ≤ |(2 * z / (1 + z) ^ 2) * (Work.Spaces.Gam (Work.FTS.Regularity.pExp α) θ
              / Work.Spaces.c (Work.FTS.Regularity.pExp α)
            - Work.Spaces.Gam (Work.FTS.Regularity.pExp α) θ'
              / Work.Spaces.c (Work.FTS.Regularity.pExp α))|
          + |(2 * z / (1 + z) ^ 2 - 2 * z' / (1 + z') ^ 2)
            * (Work.Spaces.Gam (Work.FTS.Regularity.pExp α) θ'
              / Work.Spaces.c (Work.FTS.Regularity.pExp α))| := abs_add_le _ _
      _ ≤ 1 * (40 * |θ - θ'| ^ α) + (2 * |z - z'| ^ α) * 10 := add_le_add hA hB
      _ = 40 * |θ - θ'| ^ α + 20 * |z - z'| ^ α := by ring
      _ ≤ 40 * (|z - z'| + |θ - θ'|) ^ α + 20 * (|z - z'| + |θ - θ'|) ^ α :=
          add_le_add (mul_le_mul_of_nonneg_left hθd (by norm_num))
            (mul_le_mul_of_nonneg_left hzd (by norm_num))
      _ = 60 * (|z - z'| + |θ - θ'|) ^ α := by ring

/-! ## The main statement -/

theorem jet_coeff_all {α S : ℝ} (hα : 0 < α) (hα13 : α ≤ 1 / 3) :
    Work.FTS.Regularity.Jet α S 2 (fun z θ _ => 2 * z / (1 + z) ^ 2) ∧
    Work.FTS.Regularity.Jet α S 4 (fun z θ _ => 2 / (1 + z)) ∧
    Work.FTS.Regularity.Jet α S 6 (fun z θ _ => 3 / (1 + z)) ∧
    Work.FTS.Regularity.Jet α S 40
      (fun z θ _ => Work.Spaces.Gam (Work.FTS.Regularity.pExp α) θ
        / Work.Spaces.c (Work.FTS.Regularity.pExp α)) ∧
    Work.FTS.Regularity.Jet α S 160
      (fun z θ _ => 2 * z * Work.Spaces.Gam (Work.FTS.Regularity.pExp α) θ
        / (Work.Spaces.c (Work.FTS.Regularity.pExp α) * (1 + z) ^ 2)) ∧
    Work.FTS.Regularity.Jet α S 100
      (fun z θ _ => Work.Construction.AK (Work.FTS.Regularity.pExp α) z θ) := by
  have hα1 : α ≤ 1 := by linarith
  obtain ⟨hb1, hb2, hb3, hlip1, hlip2, hlip3⟩ := jca_z_facts hα hα1
  -- the three radial coefficients, converted to `α`-Hölder
  have hh1 : ∀ z z' : ℝ, 0 ≤ z → 0 ≤ z' →
      |2 * z / (1 + z) ^ 2 - 2 * z' / (1 + z') ^ 2| ≤ 2 * |z - z'| ^ α := by
    intro z z' hz hz'
    have h := Lib.holder_of_lipschitz_of_bounded (f := fun w : ℝ => 2 * w / (1 + w) ^ 2)
      hα hα1 (by norm_num) (by norm_num) hlip1 hb1 z z' hz hz'
    have hmax : max (2 : ℝ) (2 * 1) = 2 := by norm_num
    rwa [hmax] at h
  have hh2 : ∀ z z' : ℝ, 0 ≤ z → 0 ≤ z' →
      |2 / (1 + z) - 2 / (1 + z')| ≤ 4 * |z - z'| ^ α := by
    intro z z' hz hz'
    have h := Lib.holder_of_lipschitz_of_bounded (f := fun w : ℝ => 2 / (1 + w))
      hα hα1 (by norm_num) (by norm_num) hlip2 hb2 z z' hz hz'
    have hmax : max (2 : ℝ) (2 * 2) = 4 := by norm_num
    rwa [hmax] at h
  have hh3 : ∀ z z' : ℝ, 0 ≤ z → 0 ≤ z' →
      |3 / (1 + z) - 3 / (1 + z')| ≤ 6 * |z - z'| ^ α := by
    intro z z' hz hz'
    have h := Lib.holder_of_lipschitz_of_bounded (f := fun w : ℝ => 3 / (1 + w))
      hα hα1 (by norm_num) (by norm_num) hlip3 hb3 z z' hz hz'
    have hmax : max (3 : ℝ) (2 * 3) = 6 := by norm_num
    rwa [hmax] at h
  have hFb := jca_gam_div_c_bdd hα hα13
  have hFh := jca_gam_div_c_holder hα hα13
  obtain ⟨hAb, hAh⟩ := jca_zgam_facts hα hα13
  obtain ⟨hAKb, hAKh⟩ := rhsJet_ak_bounds hα hα13
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact jet_of_z (f := fun z : ℝ => 2 * z / (1 + z) ^ 2) (N := 2) (M := 1) (K := 2)
      hα (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) hb1 hh1
  · exact jet_of_z (f := fun z : ℝ => 2 / (1 + z)) (N := 4) (M := 2) (K := 4)
      hα (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) hb2 hh2
  · exact jet_of_z (f := fun z : ℝ => 3 / (1 + z)) (N := 6) (M := 3) (K := 6)
      hα (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) hb3 hh3
  · exact jet_of_θ (g := fun θ : ℝ => Work.Spaces.Gam (Work.FTS.Regularity.pExp α) θ
        / Work.Spaces.c (Work.FTS.Regularity.pExp α)) (N := 40) (M := 10) (K := 40)
      hα (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) hFb hFh
  · exact jet_of_zθ (A := fun z θ => 2 * z * Work.Spaces.Gam (Work.FTS.Regularity.pExp α) θ
        / (Work.Spaces.c (Work.FTS.Regularity.pExp α) * (1 + z) ^ 2))
      (N := 160) (M := 10) (K := 60)
      hα (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) hAb hAh
  · exact jet_of_zθ (A := fun z θ => Work.Construction.AK (Work.FTS.Regularity.pExp α) z θ)
      (N := 100) (M := 10) (K := 100)
      hα (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) hAKb hAKh

end Work.FTS.RegPkgGal.Der
