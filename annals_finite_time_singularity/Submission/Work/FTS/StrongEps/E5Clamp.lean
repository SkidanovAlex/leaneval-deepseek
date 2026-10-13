/-
Copyright: work module for the Elgindi finite-time singularity project.

# `Submission/Work/FTS/StrongEps/E5Clamp.lean` — the quadrant clamp of a limit family

`EpsLimPkg.init` asks `g z θ 0 = g₀ z θ` for **every** `(z,θ)`, while the extraction only
determines the limit curve `F` on the **open quadrant** `Qd = (0,∞) × (0,π/2)`.  The angular
clamp `EpsE5Facts.clampFam` fixes the values on the two angular boundary lines but leaves
`z ≤ 0` equal to `F τ`; the *quadrant* clamp

  `clampQ F g₀ z θ τ = if z ∈ Ioi 0 then (if θ ∈ Ioo 0 (π/2) then F τ z θ else g₀ z θ) else g₀ z θ`

fixes all of them at once: outside the open quadrant it is the datum, so `init` and `vanish` hold
by construction given that the limit agrees with the datum on `Qd` at `τ = 0`.

Every other clause of `EpsLimPkg` is a statement about the open quadrant (`law`, `eqT`, `c4`,
`c1`, `cont`, `dbd`, `limApprox`) or an integral/a.e. statement (`mem4`, `bd4`, `bd6`) — the
clamp changes the profile only outside `Qd`, which is null in `Iz ×ˢ Iθ`, so all of them
transport (`HkSq_congr_open`, `Cert.GbarSin.HkMem_congr_Q0`).

Nothing here is analytic.
-/
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Submission.Work.FTS.StrongEps.EpsE5Facts

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section
open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.StrongEps

open Work.FTS.Galerkin (Fn Fam slice)

set_option autoImplicit false

/-- **The quadrant clamp**: the limit profile `F τ` on the open quadrant, the datum elsewhere. -/
def clampQ (F : ℝ → Fn) (g₀ : Fn) : Fam := fun z θ τ =>
  if z ∈ Set.Ioi 0 then (if θ ∈ Set.Ioo 0 (π / 2) then F τ z θ else g₀ z θ) else g₀ z θ

theorem clampQ_of_mem {F : ℝ → Fn} {g₀ : Fn} {z θ τ : ℝ}
    (hz : z ∈ Set.Ioi (0 : ℝ)) (hθ : θ ∈ Set.Ioo (0 : ℝ) (π / 2)) :
    clampQ F g₀ z θ τ = F τ z θ := by
  rw [clampQ, if_pos hz, if_pos hθ]

theorem clampQ_of_not_mem_z {F : ℝ → Fn} {g₀ : Fn} {z θ τ : ℝ}
    (hz : z ∉ Set.Ioi (0 : ℝ)) : clampQ F g₀ z θ τ = g₀ z θ := by
  rw [clampQ, if_neg hz]

theorem clampQ_of_not_mem_θ {F : ℝ → Fn} {g₀ : Fn} {z θ τ : ℝ}
    (hz : z ∈ Set.Ioi (0 : ℝ)) (hθ : θ ∉ Set.Ioo (0 : ℝ) (π / 2)) :
    clampQ F g₀ z θ τ = g₀ z θ := by
  rw [clampQ, if_pos hz, if_neg hθ]

/-- The clamp agrees with the limit profile on the open quadrant. -/
theorem clampQ_agreeOnQ (F : ℝ → Fn) (g₀ : Fn) (τ : ℝ) :
    Work.FTS.EllipticEst.AgreeOnQ (slice (clampQ F g₀) τ) (F τ) :=
  fun z θ hz hθ hθ2 => clampQ_of_mem hz ⟨hθ, hθ2⟩

/-- The `ℋᵏ`-square is unchanged by the clamp. -/
theorem clampQ_hkSq (α : ℝ) (k : ℕ) (F : ℝ → Fn) (g₀ : Fn) (τ : ℝ) :
    Work.Spaces.HkSq α k (slice (clampQ F g₀) τ) = Work.Spaces.HkSq α k (F τ) :=
  Work.FTS.EllipticEst.HkSq_congr_open α k
    (fun z θ hz hθ hθ2 => clampQ_of_mem hz ⟨hθ, hθ2⟩)

/-- The `ℋᵏ`-norm is unchanged by the clamp. -/
theorem clampQ_hkNorm (α : ℝ) (k : ℕ) (F : ℝ → Fn) (g₀ : Fn) (τ : ℝ) :
    Work.Spaces.HkNorm α k (slice (clampQ F g₀) τ) = Work.Spaces.HkNorm α k (F τ) := by
  rw [Work.Spaces.HkNorm, Work.Spaces.HkNorm, clampQ_hkSq]

/-- The `ℋᵏ`-membership is unchanged by the clamp. -/
theorem clampQ_hkMem (α : ℝ) (k : ℕ) {F : ℝ → Fn} {g₀ : Fn} {τ : ℝ}
    (h : Work.Spaces.HkMem α k (F τ)) : Work.Spaces.HkMem α k (slice (clampQ F g₀) τ) :=
  Work.FTS.EllipticEst.Cert.GbarSin.HkMem_congr_Q0 α k h
    (fun z hz θ hθ => (clampQ_of_mem hz hθ).symm)

/-- **`init` for the quadrant clamp.** -/
theorem clampQ_init {F : ℝ → Fn} {g₀ : Fn}
    (hF : ∀ z θ, z ∈ Set.Ioi (0 : ℝ) → θ ∈ Set.Ioo (0 : ℝ) (π / 2) →
      F 0 z θ = g₀ z θ) :
    ∀ z θ, clampQ F g₀ z θ 0 = g₀ z θ := by
  intro z θ
  by_cases hz : z ∈ Set.Ioi (0 : ℝ)
  · by_cases hθ : θ ∈ Set.Ioo (0 : ℝ) (π / 2)
    · rw [clampQ_of_mem hz hθ]; exact hF z θ hz hθ
    · rw [clampQ_of_not_mem_θ hz hθ]
  · rw [clampQ_of_not_mem_z hz]

/-- **`vanish` for the quadrant clamp**, from the datum's angular vanishing. -/
theorem clampQ_vanish {F : ℝ → Fn} {g₀ : Fn}
    (h0 : ∀ z, 0 ≤ z → g₀ z 0 = 0 ∧ g₀ z (π / 2) = 0) :
    ∀ τ z, 0 ≤ z → clampQ F g₀ z 0 τ = 0 ∧ clampQ F g₀ z (π / 2) τ = 0 := by
  intro τ z hz
  rcases eq_or_lt_of_le hz with h | h
  · subst h
    have hzn : (0 : ℝ) ∉ Set.Ioi (0 : ℝ) := by simp
    refine ⟨?_, ?_⟩
    · rw [clampQ_of_not_mem_z hzn]; exact (h0 0 le_rfl).1
    · rw [clampQ_of_not_mem_z hzn]; exact (h0 0 le_rfl).2
  · have hzi : z ∈ Set.Ioi (0 : ℝ) := h
    have h0n : (0 : ℝ) ∉ Set.Ioo (0 : ℝ) (π / 2) := by simp
    have h1n : (π / 2 : ℝ) ∉ Set.Ioo (0 : ℝ) (π / 2) := by simp [Set.mem_Ioo]
    rw [clampQ_of_not_mem_θ hzi h0n, clampQ_of_not_mem_θ hzi h1n]
    exact h0 z hz

/-- The clamp is `C^n` in space wherever the limit profile is. -/
theorem clampQ_contDiffOn {n : ℕ} {F : ℝ → Fn} {g₀ : Fn} {τ : ℝ}
    (h : ContDiffOn ℝ n (Function.uncurry (F τ)) Work.FTS.EllipticEst.Q0) :
    ContDiffOn ℝ n (Function.uncurry (slice (clampQ F g₀) τ)) Work.FTS.EllipticEst.Q0 :=
  h.congr (fun p hp => clampQ_of_mem hp.1 ⟨hp.2.1, hp.2.2⟩)

/-- The clamp is jointly `C¹` wherever the limit family is. -/
theorem clampQ_contDiffOn_one {F : ℝ → Fn} {g₀ : Fn}
    (h : ContDiffOn ℝ 1 (fun p : ℝ × ℝ × ℝ => F p.2.2 p.1 p.2.1)
      (Set.Ioi 0 ×ˢ Set.Ioo 0 (π / 2) ×ˢ Set.Ioi 0)) :
    ContDiffOn ℝ 1 (fun p : ℝ × ℝ × ℝ => clampQ F g₀ p.1 p.2.1 p.2.2)
      (Set.Ioi 0 ×ˢ Set.Ioo 0 (π / 2) ×ˢ Set.Ioi 0) :=
  h.congr (fun p hp => clampQ_of_mem hp.1 ⟨hp.2.1.1, hp.2.1.2⟩)

/-- Continuity in the fake time transports to the clamp on the open quadrant. -/
theorem clampQ_continuousOn {F : ℝ → Fn} {g₀ : Fn} {z θ : ℝ} {T : ℝ}
    (hz : z ∈ Set.Ioi (0 : ℝ)) (hθ : θ ∈ Set.Ioo (0 : ℝ) (π / 2))
    (h : ContinuousOn (fun τ => F τ z θ) (Set.Icc 0 T)) :
    ContinuousOn (fun τ => clampQ F g₀ z θ τ) (Set.Icc 0 T) :=
  h.congr (fun τ _ => clampQ_of_mem hz hθ)

end Work.FTS.StrongEps
