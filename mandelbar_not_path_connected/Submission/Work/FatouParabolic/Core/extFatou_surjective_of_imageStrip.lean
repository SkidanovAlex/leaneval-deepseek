import Mathlib
import Submission.Work.FatouParabolic.Core.Defs
import Submission.Work.FatouParabolic.Core.extFatou_independent
import Submission.Work.FatouParabolic.Core.extFatou_abel
import Submission.Work.FatouParabolic.Basin.preimage_mem_puncturedBasin

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


namespace Work.FatouParabolic.Core

/-!
# Surjectivity of the extended Fatou coordinate from the petal image strip

`Work.FatouParabolic.extFatou fl` is a Fatou coordinate on the whole punctured basin:
`extFatou fl (F z) = extFatou fl z + 1` (`extFatou_abel`).  Its image is therefore closed under
integer translations, and is exactly the set of `φa`-values of points of the petal (through
`extFatou_eq_φa_of_mem_Pa`).  The petal image hypothesis `PetalImageStrip` says that the image of
the petal under `φa` contains the tail of every horizontal strip of `ℂ`; translating that tail
into place by an integer and using the invariance of the image of `extFatou` under integer
translations gives surjectivity onto all of `ℂ`.

The hypotheses `hfix`, `hsurj` enter only through the two facts that the punctured basin is
forward invariant and that *every* point of the punctured basin has a preimage in it: this is
what makes the image of `extFatou` closed under `v ↦ v - 1`.
-/

open Filter
open scoped Topology

/-- The (wide) petal `fl.Pa` is contained in the punctured basin: its orbits converge to `z₀`
(`fl.tendsto_Pa`) and never attain `z₀` (a point of `fl.Pa` has all its iterates in `fl.Pa`,
which does not contain `z₀`). -/
theorem Pa_subset_puncturedBasin {F g : ℂ → ℂ} {z₀ : ℂ}
    (fl : Work.FatouCoordFix.ParabolicFlowerFix F g z₀) :
    fl.Pa ⊆ Work.FatouParabolic.puncturedBasin F z₀ := by
  intro w hw
  rw [Work.FatouParabolic.mem_puncturedBasin]
  refine ⟨?_, fl.tendsto_Pa w hw⟩
  intro n hcon
  have hmem : (F^[n]) w ∈ fl.Pa :=
    Work.FatouCoord.mapsTo_iterate_of_mapsTo fl.mapsTo_Pa n hw
  rw [hcon] at hmem
  exact fl.z₀_not_mem hmem

/-- On the petal, the extended Fatou coordinate agrees with the petal coordinate: the tap time
`entryTime` can be replaced by the time `0`, since both `F^[0] w = w` and `F^[entryTime] w` lie
in the petal (`extFatou_independent`). -/
theorem extFatou_eq_φa_of_mem_Pa {F g : ℂ → ℂ} {z₀ : ℂ}
    (fl : Work.FatouCoordFix.ParabolicFlowerFix F g z₀) {w : ℂ} (hw : w ∈ fl.Pa) :
    Work.FatouParabolic.extFatou fl w = fl.φa w := by
  have hwB : w ∈ Work.FatouParabolic.puncturedBasin F z₀ := Pa_subset_puncturedBasin fl hw
  rw [Work.FatouParabolic.extFatou_eq fl hwB]
  have h := extFatou_independent fl hwB (n := 0)
    (m := Work.FatouParabolic.entryTime fl w hwB) (by simpa using hw)
    (Work.FatouParabolic.entryTime_spec fl w hwB)
  simpa using h.symm

theorem extFatou_surjective_of_imageStrip {F g : ℂ → ℂ} {z₀ : ℂ} (hfix : F z₀ = z₀)
    (hsurj : Function.Surjective F) (fl : Work.FatouCoordFix.ParabolicFlowerFix F g z₀)
    (hstrip : Work.FatouParabolic.PetalImageStrip fl.toParabolicFlower) :
    ∀ τ : ℂ, ∃ z ∈ Work.FatouParabolic.puncturedBasin F z₀,
      Work.FatouParabolic.extFatou fl z = τ := by
  intro τ
  -- Unfold the petal image strip and apply it with `B = |τ.im|`.
  rw [Work.FatouParabolic.PetalImageStrip] at hstrip
  obtain ⟨C, hC⟩ := hstrip |τ.im| (abs_nonneg _)
  -- Shift `τ` to the right by a large natural number `m` so that it lies in the strip.
  obtain ⟨m, hm⟩ := exists_nat_gt (C - τ.re)
  have hre : C < (τ + (m : ℂ)).re := by
    rw [Complex.add_re]
    have hmm : ((m : ℂ)).re = (m : ℝ) := by simp
    rw [hmm]
    linarith
  have him : |(τ + (m : ℂ)).im| ≤ |τ.im| := by simp
  obtain ⟨w, hwPa, hwφa⟩ := hC (τ + (m : ℂ)) hre him
  -- `w` is in the punctured basin and realises the value `τ + m`.
  have hwB : w ∈ Work.FatouParabolic.puncturedBasin F z₀ :=
    Pa_subset_puncturedBasin fl hwPa
  have hwext : Work.FatouParabolic.extFatou fl w = τ + (m : ℂ) := by
    rw [extFatou_eq_φa_of_mem_Pa fl hwPa]
    exact hwφa
  -- `extFatou (F z) = extFatou z + 1`, and every point of the basin has a preimage in it:
  -- the value attained by `extFatou` is therefore closed under `v ↦ v - 1`.
  have key : ∀ k : ℕ, ∃ z ∈ Work.FatouParabolic.puncturedBasin F z₀,
      Work.FatouParabolic.extFatou fl z = τ + (m : ℂ) - (k : ℂ) := by
    intro k
    induction k with
    | zero => exact ⟨w, hwB, by simpa using hwext⟩
    | succ k ih =>
      obtain ⟨z, hz, hzval⟩ := ih
      obtain ⟨w', hw'⟩ := hsurj z
      have hw'B : w' ∈ Work.FatouParabolic.puncturedBasin F z₀ :=
        Work.FatouParabolic.Basin.preimage_mem_puncturedBasin hfix hz hw'
      refine ⟨w', hw'B, ?_⟩
      have hab := extFatou_abel hfix fl hw'B
      rw [hw'] at hab
      rw [hzval] at hab
      have hthis : Work.FatouParabolic.extFatou fl w' = τ + (m : ℂ) - (k : ℂ) - 1 := by
        linear_combination -hab
      rw [hthis]
      push_cast
      ring
  -- Now `key m` produces the required preimage of `τ`.
  obtain ⟨z, hz, hzval⟩ := key m
  exact ⟨z, hz, by rw [hzval]; push_cast; ring⟩

end Work.FatouParabolic.Core
