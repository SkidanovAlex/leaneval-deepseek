import Submission.NBody.LYZObs
import Submission.Commons.Topology.Order.exists_last_crossing
import Mathlib

/-!
# Applying the geometric observation at the dyadic scales

Liu--Yan--Zhou's Lemma 5.1 is applied at each dyadic scale `S = 2^{i+1}`, with the curve
restricted to `[0, σ_{i+1}]`, the point `τ₁ = σ_i` (where the curve crosses the sphere of radius
`S/2` for the last time) and `τ₂` the last time at which the curve is equidistant from `x*` and
`γ (σ_{i+1})`.  This module packages the two resulting estimates (`hmid` and `hray` of the
induction) so that they can be fed to the dyadic induction.
-/

open ViscositySolutions
open Filter Gradient Real Set Metric
open scoped BigOperators Topology ENNReal
open MeasureTheory

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 1000000

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
variable {N : ℕ}

namespace Submission.NBody

section Abstract

variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℝ F]

/-- The hypotheses shared by the two halves of Liu--Yan--Zhou's Lemma 5.1 at the dyadic scales. -/
structure LYZObsData (Γ : ℝ → F) (len : ℝ → ℝ → ℝ) (xS : F) (Ψ : ℝ → ℝ)
    (σ τhat : ℕ → ℝ) (n₀ n : ℕ) (τ : ℝ) : Prop where
  hlen_add : ∀ a b c, 0 ≤ a → a ≤ b → b ≤ c → c ≤ τ → len a c = len a b + len b c
  hlen_chord : ∀ a b, 0 ≤ a → a ≤ b → b ≤ τ → ‖Γ b - Γ a‖ ≤ len a b
  hlen_bound : ∀ t ∈ Set.Icc 0 τ, len 0 t ≤ ‖Γ t - xS‖ + Ψ (‖Γ t - xS‖)
  hσval : ∀ i, n₀ ≤ i → i ≤ n → ‖Γ (σ i) - xS‖ = (2:ℝ) ^ i
  hσmem : ∀ i, n₀ ≤ i → i ≤ n → σ i ∈ Set.Icc 0 τ
  hτhat_mem : ∀ i, n₀ ≤ i → i < n → τhat i ∈ Set.Icc 0 τ
  hτhat_val : ∀ i, n₀ ≤ i → i < n → ‖Γ (τhat i) - xS‖ = ‖Γ (τhat i) - Γ (σ (i + 1))‖
  hτhat_ge : ∀ i, n₀ ≤ i → i < n → (2:ℝ) ^ i ≤ ‖Γ (τhat i) - xS‖
  hτhat_le : ∀ i, n₀ ≤ i → i < n → σ i ≤ τhat i
  hτhat_τ : ∀ i, n₀ ≤ i → i < n → τhat i ≤ σ (i + 1)
  hx0 : ∀ i, n₀ ≤ i → i < n → ‖Γ 0 - xS‖ ≤ Ψ ((2:ℝ) ^ (i + 1))
  hΨpos : ∀ i, n₀ ≤ i → i < n → 0 ≤ Ψ ((2:ℝ) ^ (i + 1))
  hΨhalf : ∀ i, n₀ ≤ i → i < n → Ψ ((2:ℝ) ^ (i + 1)) ≤ (2:ℝ) ^ (i + 1) / 2
  hσmono : ∀ i, n₀ ≤ i → i < n → σ i ≤ σ (i + 1)

/-- **The midpoint estimate at the dyadic scales** (Liu--Yan--Zhou, Lemma 5.1, first part). -/
theorem lyz_mid_of_data {Γ : ℝ → F} {len : ℝ → ℝ → ℝ} {xS : F} {Ψ : ℝ → ℝ}
    {σ τhat : ℕ → ℝ} {n₀ n : ℕ} {τ : ℝ} (h : LYZObsData Γ len xS Ψ σ τhat n₀ n τ) :
    ∀ i, n₀ ≤ i → i < n →
      ‖Γ (σ i) - (xS + ((1:ℝ) / 2) • (Γ (σ (i + 1)) - xS))‖
        ≤ 4 * Real.sqrt ((2:ℝ) ^ (i + 1) * Ψ ((2:ℝ) ^ (i + 1))) := by
  intro i hi hin
  have hi1 : n₀ ≤ i + 1 := le_trans hi (Nat.le_succ i)
  have hi1n : i + 1 ≤ n := Nat.succ_le_of_lt hin
  have hinle : i ≤ n := le_of_lt hin
  have hS : (0:ℝ) < (2:ℝ) ^ (i + 1) := by positivity
  have hy : ‖Γ (σ (i + 1)) - xS‖ = (2:ℝ) ^ (i + 1) := h.hσval (i + 1) hi1 hi1n
  have hq : ‖Γ (σ i) - xS‖ = (2:ℝ) ^ (i + 1) / 2 := by
    rw [h.hσval i hi hinle]
    have h2 : ((2:ℝ) ^ (i + 1)) = 2 * (2:ℝ) ^ i := by rw [pow_succ]; ring
    rw [h2]; ring
  have htotal : len 0 (σ (i + 1)) ≤ (2:ℝ) ^ (i + 1) + Ψ ((2:ℝ) ^ (i + 1)) := by
    have := h.hlen_bound (σ (i + 1)) (h.hσmem (i + 1) hi1 hi1n)
    rwa [hy] at this
  exact lyz_obs_midpoint (F := F) (γ := Γ) (len := len) (xstar := xS)
    (S := (2:ℝ) ^ (i + 1)) (Ψ := Ψ ((2:ℝ) ^ (i + 1))) (τ := σ (i + 1)) (τ₁ := σ i)
    (τ₂ := τhat i) hS (h.hΨpos i hi hin) (h.hΨhalf i hi hin)
    (h.hσmem i hi hinle).1 (h.hσmono i hi hin) (h.hτhat_le i hi hin)
    (h.hτhat_τ i hi hin)
    (fun a b c h0 hab hbc hc => h.hlen_add a b c h0 hab hbc (hc.trans (h.hσmem (i+1) hi1 hi1n).2))
    (fun a b h0 hab hb => h.hlen_chord a b h0 hab (hb.trans (h.hσmem (i+1) hi1 hi1n).2))
    htotal (h.hx0 i hi hin) hy hq (h.hτhat_val i hi hin)
    (by rw [show (2:ℝ) ^ (i + 1) / 2 = (2:ℝ) ^ i from by rw [pow_succ]; ring]
        exact h.hτhat_ge i hi hin)

/-- **The ray estimate at the dyadic scales** (Liu--Yan--Zhou, Lemma 5.1, second part). -/
theorem lyz_ray_of_data {Γ : ℝ → F} {len : ℝ → ℝ → ℝ} {xS : F} {Ψ : ℝ → ℝ}
    {σ τhat : ℕ → ℝ} {n₀ n : ℕ} {τ : ℝ} (h : LYZObsData Γ len xS Ψ σ τhat n₀ n τ) :
    ∀ i, n₀ ≤ i → i < n → ∀ t ∈ Set.Icc (σ i) (σ (i + 1)),
      ∃ c : ℝ, 0 ≤ c ∧
        ‖Γ t - (xS + c • (Γ (σ (i + 1)) - xS))‖
          ≤ 6 * Real.sqrt ((2:ℝ) ^ (i + 1) * Ψ ((2:ℝ) ^ (i + 1))) := by
  intro i hi hin t ht
  have hi1 : n₀ ≤ i + 1 := le_trans hi (Nat.le_succ i)
  have hi1n : i + 1 ≤ n := Nat.succ_le_of_lt hin
  have hinle : i ≤ n := le_of_lt hin
  have hS : (0:ℝ) < (2:ℝ) ^ (i + 1) := by positivity
  have hy : ‖Γ (σ (i + 1)) - xS‖ = (2:ℝ) ^ (i + 1) := h.hσval (i + 1) hi1 hi1n
  have hq : ‖Γ (σ i) - xS‖ = (2:ℝ) ^ (i + 1) / 2 := by
    rw [h.hσval i hi hinle]
    have h2 : ((2:ℝ) ^ (i + 1)) = 2 * (2:ℝ) ^ i := by rw [pow_succ]; ring
    rw [h2]; ring
  have htotal : len 0 (σ (i + 1)) ≤ (2:ℝ) ^ (i + 1) + Ψ ((2:ℝ) ^ (i + 1)) := by
    have := h.hlen_bound (σ (i + 1)) (h.hσmem (i + 1) hi1 hi1n)
    rwa [hy] at this
  exact lyz_obs_ray (F := F) (γ := Γ) (len := len) (xstar := xS)
    (S := (2:ℝ) ^ (i + 1)) (Ψ := Ψ ((2:ℝ) ^ (i + 1))) (τ := σ (i + 1)) (τ₁ := σ i)
    (τ₂ := τhat i) hS (h.hΨpos i hi hin) (h.hΨhalf i hi hin)
    (h.hσmem i hi hinle).1 (h.hσmono i hi hin) (h.hτhat_le i hi hin)
    (h.hτhat_τ i hi hin) ht.1 ht.2
    (fun a b c h0 hab hbc hc => h.hlen_add a b c h0 hab hbc (hc.trans (h.hσmem (i+1) hi1 hi1n).2))
    (fun a b h0 hab hb => h.hlen_chord a b h0 hab (hb.trans (h.hσmem (i+1) hi1 hi1n).2))
    htotal (h.hx0 i hi hin) hy hq (h.hτhat_val i hi hin)
    (by rw [show (2:ℝ) ^ (i + 1) / 2 = (2:ℝ) ^ i from by rw [pow_succ]; ring]
        exact h.hτhat_ge i hi hin)

/-- **The last time at which `‖Γ - xS‖` equals `r`**, provided `‖Γ 0 - xS‖ < r < ‖Γ τ - xS‖`
and `Γ` is continuous. -/
theorem exists_last_crossing_norm {Γ : ℝ → F} {xS : F} {τ r : ℝ} (hτ : 0 ≤ τ)
    (hcont : ContinuousOn Γ (Set.Icc 0 τ)) (h0 : ‖Γ 0 - xS‖ < r) (hτ' : r < ‖Γ τ - xS‖) :
    ∃ s ∈ Set.Icc 0 τ, ‖Γ s - xS‖ = r ∧ ∀ t ∈ Set.Icc s τ, r ≤ ‖Γ t - xS‖ := by
  have hc : ContinuousOn (fun t : ℝ => ‖Γ t - xS‖) (Set.Icc 0 τ) :=
    (hcont.sub continuousOn_const).norm
  obtain ⟨s, hs, hsv, hsm⟩ :=
    Commons.Topology.Order.exists_last_crossing hτ hc h0 hτ'
  exact ⟨s, hs, hsv, hsm⟩

end Abstract

end Submission.NBody
