/-
# Injectivity of the polygon parametrization

`cycParam D R` is injective on the fundamental domain `[0,1)`: the parametrization runs through
the blocks `k = 0, -1, …, 1-m` and the blocks are simple and pairwise disjoint
(`CycLift.cycBlock_injOn`).
-/
import Mathlib
import Submission.Work.ELTop.PolyCurve.Defs
import Submission.Work.ELTop.PolyCurve.Blocks

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


open Classical Filter Set
open scoped Topology

noncomputable section

namespace Work.ELTop

variable {c : ℂ} {φ : ℂ → ℂ} {hN : Work.EL.DynB c φ}

/-- The integer part of `m s` for `s ∈ [0,1)` lies in `[0,m)`. -/
theorem floor_mem_Ico {m : ℕ} (hm : 0 < m) {s : ℝ} (hs : s ∈ Set.Ico 0 1) :
    ⌊(m : ℝ) * s⌋ ∈ Set.Ico (0 : ℤ) (m : ℤ) := by
  have hm' : (0 : ℝ) < (m : ℝ) := by exact_mod_cast hm
  constructor
  · by_contra h
    have h1 : ⌊(m : ℝ) * s⌋ ≤ -1 := by omega
    have h2 : (m : ℝ) * s < 0 := by
      have := (Int.floor_le_iff.mp h1)
      simpa using this
    nlinarith [hs.1]
  · by_contra h
    have h1 : (m : ℤ) ≤ ⌊(m : ℝ) * s⌋ := by omega
    have h2 : ((m : ℤ) : ℝ) ≤ (m : ℝ) * s :=
      le_trans (by exact_mod_cast h1) (Int.floor_le _)
    have h3 : (1 : ℝ) ≤ s := by
      have : (m : ℝ) * 1 ≤ (m : ℝ) * s := by simpa using h2
      exact le_of_mul_le_mul_left this hm'
    linarith [hs.2]

/-- The fractional part of `m s` for `s ∈ ℝ` lies in `[0,1)`. -/
theorem fract_mem_Ico (m : ℕ) (s : ℝ) : (m : ℝ) * s - ⌊(m : ℝ) * s⌋ ∈ Set.Ico 0 1 := by
  constructor
  · have h := Int.fract_nonneg ((m : ℝ) * s)
    have h' := Int.fract_add_floor ((m : ℝ) * s)
    linarith
  · have h := Int.fract_lt_one ((m : ℝ) * s)
    have h' := Int.fract_add_floor ((m : ℝ) * s)
    linarith

/-- **The parametrization is injective on `[0,1)`.** -/
theorem CycLift.injOn_cycParam (D : CycLift hN) {R : ℝ} (hR : 1 < R) :
    Set.InjOn (cycParam D R) (Set.Ico 0 1) := by
  intro s hs s' hs' h
  have hm : (0 : ℝ) < (D.m : ℝ) := by exact_mod_cast D.hm
  have hfl := floor_mem_Ico D.hm hs
  have hfl' := floor_mem_Ico D.hm hs'
  have hfr := fract_mem_Ico D.m s
  have hfr' := fract_mem_Ico D.m s'
  have hk1 : 1 - (D.m : ℤ) ≤ -⌊(D.m : ℝ) * s⌋ := by
    have := hfl.2
    omega
  have hk2 : -⌊(D.m : ℝ) * s⌋ ≤ 0 := by
    have := hfl.1
    omega
  have hk1' : 1 - (D.m : ℤ) ≤ -⌊(D.m : ℝ) * s'⌋ := by
    have := hfl'.2
    omega
  have hk2' : -⌊(D.m : ℝ) * s'⌋ ≤ 0 := by
    have := hfl'.1
    omega
  have hmain := D.cycBlock_injOn hR hk1 hk2 hk1' hk2' hfr hfr' h
  obtain ⟨hk, hσ⟩ := hmain
  have h1 : (D.m : ℝ) * s = (D.m : ℝ) * s' := by
    have h2 : ⌊(D.m : ℝ) * s⌋ = ⌊(D.m : ℝ) * s'⌋ := by omega
    have h3 : ((⌊(D.m : ℝ) * s⌋ : ℤ) : ℝ) = ((⌊(D.m : ℝ) * s'⌋ : ℤ) : ℝ) := by rw [h2]
    linarith
  exact mul_left_cancel₀ (ne_of_gt hm) h1

end Work.ELTop
