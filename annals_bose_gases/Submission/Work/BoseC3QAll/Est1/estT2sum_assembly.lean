import Mathlib.Algebra.Algebra.Basic
import Mathlib.Algebra.Order.Archimedean.Real.Basic
import Submission.Work.BoseC3QAll.Est1.estT2sum_split
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Submission.Work.BoseC3QAll.Est1.estT2sum_assembly` — piece **B** from its two halves

The assembly of `Est1.estT2sum` from

* `Est1.estT2sum_split` (proved): `bp (Y_kΦ) (Y_kΦ) = Z²(T2ComF k Φ + T2OpF k Φ)`,
  `Z = z/ℓ³`;
* `Est1.estT2sum_comZ` (the `χ̂²` half, FS `eq:EstimT2comm`);
* `Est1.estT2sum_opZ` (the normal-ordered half, FS `eq:T2opprime`),

each carrying the physical normalisation `Z²·Σ_k c_k⁻¹`.

## The bookkeeping

Both halves are bounded by the same shape

  `Σ_k Z²c_k⁻¹(·) ≤ [2ρ_zŴ₁ω(0)⟨G Φ⟩] + C·e1A‖Φ‖² + (b/400)⟨gap Φ⟩ + (𝓁²/8)⟨R_{P_H^q}Φ⟩`,

and the two `(b/400)` gap shares and the two `(𝓁²/8)` reserve shares add up to the
`(b/200)` and `(𝓁²/4)` of `Est1.estT2sum`; the two error brackets add.  The linear
identity `Σ_k c_k⁻¹ Z²(Com + Op) = Σ_kZ²c_k⁻¹Com + Σ_kZ²c_k⁻¹Op` is the only
bookkeeping.
-/

noncomputable section

open scoped BigOperators

namespace Work.BoseC3QAll

namespace Est1

open Work.BoseB7

set_option linter.unusedVariables false

universe u v

theorem estT2sum_of_pieces (K₀ b₀ : ℝ) (hb₀ : 0 < b₀)
    (hC : ∃ C t₀ : ℝ, 0 ≤ C ∧ 0 < t₀ ∧
      ∀ {Mode : Type u} [AddCommGroup Mode] [Fintype Mode] [DecidableEq Mode]
        (F : FockData.{u, v} Mode) (T : Work.BoseB7A.TildeData.{u, v} F) (E : Q3Env.{u} Mode)
        (hv : FSParamsView E),
        hv.t ≤ t₀ → b₀ ≤ E.b → Q3KernelFSAll K₀ F T E →
        ∀ Φ : F.H, T.NWindow E.bigM Φ →
          ∑ k ∈ F.PHset E, (E.z / E.ell ^ 3) ^ 2 * (cD E k)⁻¹ * T2ComF F T E k Φ
            ≤ 2 * E.rho * E.W1omega0 * F.qw Φ (T.Gop E)
              + C * e1A E * F.normSq Φ
              + (E.b / 400) * F.qw Φ (T.gapOpT E)
              + (E.lille ^ 2 / 8) * F.qw Φ (F.dNumOpR E (F.PHq E.KH E.aScat)))
    (hO : ∃ C t₀ : ℝ, 0 ≤ C ∧ 0 < t₀ ∧
      ∀ {Mode : Type u} [AddCommGroup Mode] [Fintype Mode] [DecidableEq Mode]
        (F : FockData.{u, v} Mode) (T : Work.BoseB7A.TildeData.{u, v} F) (E : Q3Env.{u} Mode)
        (hv : FSParamsView E),
        hv.t ≤ t₀ → b₀ ≤ E.b → Q3KernelFSAll K₀ F T E →
        ∀ Φ : F.H, T.NWindow E.bigM Φ →
          ∑ k ∈ F.PHset E, (E.z / E.ell ^ 3) ^ 2 * (cD E k)⁻¹ * T2OpF F T E k Φ
            ≤ C * e1A E * F.normSq Φ
              + (E.b / 400) * F.qw Φ (T.gapOpT E)
              + (E.lille ^ 2 / 8) * F.qw Φ (F.dNumOpR E (F.PHq E.KH E.aScat))) :
    ∃ C t₀ : ℝ, 0 ≤ C ∧ 0 < t₀ ∧
      ∀ {Mode : Type u} [AddCommGroup Mode] [Fintype Mode] [DecidableEq Mode]
        (F : Work.BoseB7.FockData.{u, v} Mode) (T : Work.BoseB7A.TildeData.{u, v} F)
        (E : Work.BoseB7.Q3Env.{u} Mode) (hv : Work.BoseB7.FSParamsView E),
        hv.t ≤ t₀ → b₀ ≤ E.b → Work.BoseC3QAll.Q3KernelFSAll K₀ F T E →
        ∀ Φ : F.H, T.NWindow E.bigM Φ →
          ∑ k ∈ F.PHset E, (Work.BoseC3QAll.Est1.cD E k)⁻¹ *
              F.bp (Work.BoseC3QAll.Est1.shift F T E k Φ) (Work.BoseC3QAll.Est1.shift F T E k Φ)
            ≤ (E.lille ^ 2 / 4) * F.qw Φ (F.dNumOpR E (F.PHq E.KH E.aScat))
              + 2 * E.rho * E.W1omega0 * F.qw Φ (T.Gop E)
              + C * Work.BoseC3QAll.e1A E * F.normSq Φ
              + (E.b / 200) * F.qw Φ (T.gapOpT E) := by
  obtain ⟨CC, tC, hCC, htC, HC⟩ := hC
  obtain ⟨CO, tO, hCO, htO, HO⟩ := hO
  refine ⟨CC + CO, min tC tO, add_nonneg hCC hCO, lt_min htC htO, ?_⟩
  intro Mode instAC instF instD F T E hv hle hb hK Φ hΦ
  have htC' : hv.t ≤ tC := le_trans hle (min_le_left _ _)
  have htO' : hv.t ≤ tO := le_trans hle (min_le_right _ _)
  have hcom := HC F T E hv htC' hb hK Φ hΦ
  have hop := HO F T E hv htO' hb hK Φ hΦ
  -- the split, termwise
  have hLHS : (∑ k ∈ F.PHset E,
        (cD E k)⁻¹ * F.bp (shift F T E k Φ) (shift F T E k Φ))
      = (∑ k ∈ F.PHset E, (E.z / E.ell ^ 3) ^ 2 * (cD E k)⁻¹ * T2ComF F T E k Φ)
        + (∑ k ∈ F.PHset E, (E.z / E.ell ^ 3) ^ 2 * (cD E k)⁻¹ * T2OpF F T E k Φ) := by
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun k hk => ?_
    rw [estT2sum_split hK k hk Φ]
    ring
  -- the two RHS's add up to the target RHS
  have htarget : (2 * E.rho * E.W1omega0 * F.qw Φ (T.Gop E)
        + CC * e1A E * F.normSq Φ
        + (E.b / 400) * F.qw Φ (T.gapOpT E)
        + (E.lille ^ 2 / 8) * F.qw Φ (F.dNumOpR E (F.PHq E.KH E.aScat)))
      + (CO * e1A E * F.normSq Φ
        + (E.b / 400) * F.qw Φ (T.gapOpT E)
        + (E.lille ^ 2 / 8) * F.qw Φ (F.dNumOpR E (F.PHq E.KH E.aScat)))
      = (E.lille ^ 2 / 4) * F.qw Φ (F.dNumOpR E (F.PHq E.KH E.aScat))
        + 2 * E.rho * E.W1omega0 * F.qw Φ (T.Gop E)
        + (CC + CO) * e1A E * F.normSq Φ
        + (E.b / 200) * F.qw Φ (T.gapOpT E) := by
    ring
  rw [hLHS]
  have hsum := add_le_add hcom hop
  rw [htarget] at hsum
  exact hsum

end Est1

end Work.BoseC3QAll
