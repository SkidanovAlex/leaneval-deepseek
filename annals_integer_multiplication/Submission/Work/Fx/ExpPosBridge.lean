import Mathlib
import Submission.Work.Fx.ExpPosDefs
import Submission.Work.Fx.ExpPosZData

/-!
# Bridging `ExpPosZData` to the operational definitions

The delegated lemma `ExpPosZData` is stated with the mathematical definitions
(`epX`, `epAl`, `epT`, `epTau`, `epK0`, `epZ`); the program works with the operational
ones (`epXw`, `epAlw`, `epTw`, `epTauw`, `epK0w`, `epZw`).  This file performs the (entirely
definitional) translation once and for all, in a clean context.
-/

set_option autoImplicit false
set_option maxHeartbeats 1000000

namespace Work.Fx
open HvdH

theorem epXw_eq_epX (j k : ℕ) (P : ℤ) : epXw j k P = epX P j k := by
  simp only [epXw, epX]
  congr 1
  ring

/-- Operational form of the conclusions of `ExpPosZData`. -/
theorem ExpPosZDataOp (p j k σ : ℕ) (P L : ℤ)
    (hp : 100 ≤ p) (hk : 1 ≤ k)
    (he : Real.exp (Real.pi * (j : ℝ) / (k : ℝ)) ≤ (2 : ℝ) ^ σ)
    (hσ : (σ : ℝ) ≤ 2 * (p : ℝ))
    (hP : |(P : ℝ) - (2 : ℝ) ^ (epQ p) * Real.pi| ≤ 1)
    (hL : |(L : ℝ) - (2 : ℝ) ^ (epQ p) * Real.log 2| ≤ 1) :
    |((epZw p σ j k P L : ℤ) : ℝ)| ≤ 32 * (2 : ℝ) ^ (epQ p) ∧
    Real.exp (((epZw p σ j k P L : ℤ) : ℝ) / (2 : ℝ) ^ (epQ p)) + 4 / (2 : ℝ) ^ (epQ p)
        ≤ (2 : ℝ) ^ (epTauw σ j k P L) ∧
    (2 : ℝ) ^ p * |(2 : ℝ) ^ (-(epTauw σ j k P L)) *
        Real.exp (((epZw p σ j k P L : ℤ) : ℝ) / (2 : ℝ) ^ (epQ p)) -
        (2 : ℝ) ^ (-(σ : ℤ)) * Real.exp (Real.pi * (j : ℝ) / (k : ℝ))| ≤ 1 / 2 := by
  have h := ExpPosZData p j k σ P L (epXw j k P) hp hk he hσ hP hL (epXw_eq_epX j k P)
  have harg : (epAl σ L (epXw j k P) + L - 1) = (epAlw σ j k P L + (L - 1)) := by
    simp only [epAl, epAlw]
    ring
  have hTeq : (epTau (epAl σ L (epXw j k P)) L : ℤ) = epTauw σ j k P L := by
    have hstep : Int.tdiv (epAl σ L (epXw j k P) + L - 1) L
        = Int.tdiv (epAlw σ j k P L + (L - 1)) L := by rw [harg]
    simp only [epTau, epTauw, epTw, epT, hstep]
    exact Int.max_comm _ _
  have hZeq : (epZ p σ (epXw j k P) L (epAl σ L (epXw j k P)) : ℤ) = epZw p σ j k P L := by
    have hT : (epTau (epAl σ L (epXw j k P)) L : ℤ) = epTauw σ j k P L := hTeq
    simp only [epZ, epZw, epE, epA, epK0, epK0w]
    rw [hT]
    ring
  obtain ⟨h1, h2, h3⟩ := h
  rw [hZeq] at h1 h2 h3
  rw [hTeq] at h2 h3
  exact ⟨h1, h2, h3⟩

end Work.Fx
