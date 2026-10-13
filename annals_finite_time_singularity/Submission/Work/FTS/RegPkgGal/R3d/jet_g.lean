import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Submission.Work.FTS.RegPkgGal.Defs
import Submission.Work.FTS.RegPkgGal.Basic
import Submission.Work.FTS.RegPkgGal.RVocab

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.RegPkgGal.R3d

/-! ## The `α`-Hölder upgrade to a `Jet`

`Work.FTS.Regularity.Jet α S N h` bundles a *uniform bound* by `N` on the domain
`z ≥ 0`, `θ ∈ Iθ`, `τ ∈ [0,S]` together with a *joint* `α`-Hölder modulus for the metric
`|Δz| + |Δθ| + |Δτ|`, again with the constant `N`.  The data available in the `R3d` hypotheses are
*one-variable* `α`-Hölder bounds in `z`, `θ`, `τ` (with constants `Lz`, `Lθ`, `Lt`) plus
pointwise bounds by `M`.  The two lemmas below perform the (elementary) upgrade.  Since all three
moduli carry the **same** exponent `α`, the passage to the sum metric is a direct application of
`Real.rpow_le_rpow` (`|Δz| ≤ d` and `0 ≤ α` give `|Δz|^α ≤ d^α`): no `d ≤ 1` / `d ≥ 1`
dichotomy is needed, unlike in the Lipschitz-to-Hölder upgrade `R3b.jet_of_bounded_lipschitz`
(where `Lz * |Δz|` has to be compared with `d^α`, forcing a case split and paying `2M`). -/

/-- `|a + b + c| ≤ |a| + |b| + |c|`. -/
theorem abs_add_three_le (a b c : ℝ) : |a + b + c| ≤ |a| + |b| + |c| := by
  calc |a + b + c| ≤ |a + b| + |c| := abs_add_le _ _
    _ ≤ (|a| + |b|) + |c| := by linarith [abs_add_le a b]
    _ = |a| + |b| + |c| := by ring

/-- **The `α`-Hölder-to-`Jet` upgrade.**  A family `h` bounded by `M` on
`[0,∞) × Iθ × [0,S]`, `α`-Hölder in each of the three variables at fixed values of the other
variables (same exponent `α`, constants `Lz, Lθ, Lt`), is a `Jet` with the constant
`Lz + Lθ + Lt + M`. -/
theorem jet_of_bounded_holder {α S M Lz Lθ Lt : ℝ} (hα : 0 < α)
    (hM : 0 ≤ M) (hLz : 0 ≤ Lz) (hLθ : 0 ≤ Lθ) (hLt : 0 ≤ Lt)
    {h : ℝ → ℝ → ℝ → ℝ}
    (hsup : ∀ τ ∈ Set.Icc 0 S, ∀ z θ : ℝ, 0 ≤ z → θ ∈ Work.Spaces.Iθ → |h z θ τ| ≤ M)
    (hhz : ∀ τ ∈ Set.Icc 0 S, ∀ z z' : ℝ, 0 ≤ z → 0 ≤ z' → ∀ θ ∈ Work.Spaces.Iθ,
      |h z θ τ - h z' θ τ| ≤ Lz * |z - z'| ^ α)
    (hhθ : ∀ τ ∈ Set.Icc 0 S, ∀ z : ℝ, 0 ≤ z → ∀ θ ∈ Work.Spaces.Iθ,
      ∀ θ' ∈ Work.Spaces.Iθ, |h z θ τ - h z θ' τ| ≤ Lθ * |θ - θ'| ^ α)
    (hhτ : ∀ τ ∈ Set.Icc 0 S, ∀ τ' ∈ Set.Icc 0 S, ∀ z : ℝ, 0 ≤ z →
      ∀ θ ∈ Work.Spaces.Iθ, |h z θ τ - h z θ τ'| ≤ Lt * |τ - τ'| ^ α) :
    ∃ N : ℝ, Work.FTS.Regularity.Jet α S N h := by
  refine ⟨Lz + Lθ + Lt + M, by linarith, ?_, ?_⟩
  · intro z θ τ hz hθ hτ
    have h1 := hsup τ hτ z θ hz hθ
    linarith
  · intro z z' θ θ' τ τ' hz hz' hθ hθ' hτ hτ'
    have h1 := hhz τ hτ z z' hz hz' θ hθ
    have h2 := hhθ τ hτ z' hz' θ hθ θ' hθ'
    have h3 := hhτ τ hτ τ' hτ' z' hz' θ' hθ'
    have htri : |h z θ τ - h z' θ' τ'|
        ≤ |h z θ τ - h z' θ τ| + |h z' θ τ - h z' θ' τ| + |h z' θ' τ - h z' θ' τ'| := by
      have e : h z θ τ - h z' θ' τ'
          = (h z θ τ - h z' θ τ) + (h z' θ τ - h z' θ' τ)
            + (h z' θ' τ - h z' θ' τ') := by ring
      rw [e]
      exact abs_add_three_le _ _ _
    have hkey : |h z θ τ - h z' θ' τ'|
        ≤ Lz * |z - z'| ^ α + Lθ * |θ - θ'| ^ α + Lt * |τ - τ'| ^ α := by linarith
    have hd0 : (0 : ℝ) ≤ |z - z'| + |θ - θ'| + |τ - τ'| := by
      linarith [abs_nonneg (z - z'), abs_nonneg (θ - θ'), abs_nonneg (τ - τ')]
    have hrp : (0 : ℝ) ≤ (|z - z'| + |θ - θ'| + |τ - τ'|) ^ α := Real.rpow_nonneg hd0 α
    have hAz : |z - z'| ^ α ≤ (|z - z'| + |θ - θ'| + |τ - τ'|) ^ α :=
      Real.rpow_le_rpow (abs_nonneg _)
        (by linarith [abs_nonneg (θ - θ'), abs_nonneg (τ - τ')]) hα.le
    have hAθ : |θ - θ'| ^ α ≤ (|z - z'| + |θ - θ'| + |τ - τ'|) ^ α :=
      Real.rpow_le_rpow (abs_nonneg _)
        (by linarith [abs_nonneg (z - z'), abs_nonneg (τ - τ')]) hα.le
    have hAτ : |τ - τ'| ^ α ≤ (|z - z'| + |θ - θ'| + |τ - τ'|) ^ α :=
      Real.rpow_le_rpow (abs_nonneg _)
        (by linarith [abs_nonneg (z - z'), abs_nonneg (θ - θ')]) hα.le
    have hstep : Lz * |z - z'| ^ α + Lθ * |θ - θ'| ^ α + Lt * |τ - τ'| ^ α
        ≤ (Lz + Lθ + Lt + M) * (|z - z'| + |θ - θ'| + |τ - τ'|) ^ α := by
      have hz' := mul_le_mul_of_nonneg_left hAz hLz
      have hθ' := mul_le_mul_of_nonneg_left hAθ hLθ
      have hτ' := mul_le_mul_of_nonneg_left hAτ hLt
      nlinarith [mul_nonneg hM hrp]
    linarith

theorem jet_g {α S M Lz Lθ Lt Nz Nθ Nt : ℝ} (hα : 0 < α) (hα1 : α ≤ 1) (hS : 0 < S)
    (hM : 0 ≤ M) (hLz : 0 ≤ Lz) (hLθ : 0 ≤ Lθ) (hLt : 0 ≤ Lt)
    (hNz : 0 ≤ Nz) (hNθ : 0 ≤ Nθ) (hNt : 0 ≤ Nt)
    {g : ℝ → ℝ → ℝ → ℝ}
    (hsup : ∀ τ ∈ Set.Icc 0 S, ∀ z θ : ℝ, 0 ≤ z → θ ∈ Work.Spaces.Iθ →
      |g z θ τ| ≤ M ∧ |Work.Spaces.pz (Work.FTS.Regularity.gSlice g τ) z θ| ≤ M)
    (hhz : ∀ τ ∈ Set.Icc 0 S, ∀ z z' : ℝ, 0 ≤ z → 0 ≤ z' →
      ∀ θ ∈ Work.Spaces.Iθ, |g z θ τ - g z' θ τ| ≤ Lz * |z - z'| ^ α)
    (hhθ : ∀ τ ∈ Set.Icc 0 S, ∀ z : ℝ, 0 ≤ z → ∀ θ ∈ Work.Spaces.Iθ,
      ∀ θ' ∈ Work.Spaces.Iθ, |g z θ τ - g z θ' τ| ≤ Lθ * |θ - θ'| ^ α)
    (hhτ : ∀ τ ∈ Set.Icc 0 S, ∀ τ' ∈ Set.Icc 0 S, ∀ z : ℝ, 0 ≤ z →
      ∀ θ ∈ Work.Spaces.Iθ, |g z θ τ - g z θ τ'| ≤ Lt * |τ - τ'| ^ α)
    (hhzp : ∀ τ ∈ Set.Icc 0 S, ∀ z z' : ℝ, 0 ≤ z → 0 ≤ z' → ∀ θ ∈ Work.Spaces.Iθ,
      |Work.Spaces.pz (Work.FTS.Regularity.gSlice g τ) z θ
        - Work.Spaces.pz (Work.FTS.Regularity.gSlice g τ) z' θ| ≤ Nz * |z - z'| ^ α)
    (hhθp : ∀ τ ∈ Set.Icc 0 S, ∀ z : ℝ, 0 ≤ z → ∀ θ ∈ Work.Spaces.Iθ,
      ∀ θ' ∈ Work.Spaces.Iθ,
      |Work.Spaces.pz (Work.FTS.Regularity.gSlice g τ) z θ
        - Work.Spaces.pz (Work.FTS.Regularity.gSlice g τ) z θ'| ≤ Nθ * |θ - θ'| ^ α)
    (hhτp : ∀ τ ∈ Set.Icc 0 S, ∀ τ' ∈ Set.Icc 0 S, ∀ z : ℝ, 0 ≤ z →
      ∀ θ ∈ Work.Spaces.Iθ,
      |Work.Spaces.pz (Work.FTS.Regularity.gSlice g τ) z θ
        - Work.Spaces.pz (Work.FTS.Regularity.gSlice g τ') z θ| ≤ Nt * |τ - τ'| ^ α) :
    (∃ N : ℝ, Work.FTS.Regularity.Jet α S N g) ∧
    (∃ N : ℝ, Work.FTS.Regularity.Jet α S N
      (fun z θ τ => Work.Spaces.pz (Work.FTS.Regularity.gSlice g τ) z θ)) := by
  refine ⟨?_, ?_⟩
  · exact jet_of_bounded_holder hα hM hLz hLθ hLt
      (fun τ hτ z θ hz hθ => (hsup τ hτ z θ hz hθ).1) hhz hhθ hhτ
  · exact jet_of_bounded_holder hα hM hNz hNθ hNt
      (fun τ hτ z θ hz hθ => (hsup τ hτ z θ hz hθ).2) hhzp hhθp hhτp

end Work.FTS.RegPkgGal.R3d
