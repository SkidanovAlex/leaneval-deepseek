import Mathlib
import Submission.Work.SeedSimple2.Defs
import Submission.Work.SeedSimple2.Invariance
import Submission.Work.SeedSimple2.Rotation.arcBound_of_sidePreserve

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


set_option maxHeartbeats 1000000

namespace Work.SeedSimple2.COP

open LeanEval.ComplexAnalysis (Tantibar)

/-- **The angle set `A` is closed under `T^[10n]`** (`COP/NOTES_COP.md` §4): the `n`-th iterate `Int.fract (1024^n θ)` (the representative in `[0,1)`) of a landing angle is again a landing angle.  Used by `L9 angleMono_proved` to know that the triple `(θₙ, α₁, θₙ₊₁)` consists of landing angles.

Proof: `Work.SeedSimple2.landsN_T_iterate d (10*n)` gives `LandsN ((T^[10n]) θ) z₁` (with `(Tantibar c)^[10n] z₁ = z₁` from `d.per_half`), `Work.ELRig.T_iterate_eq_add_int θ (10*n)` writes `(T^[10n]) θ = (1024)^n θ + m`, and `Work.SeedSimple2.landsN_add_int d (-(⌊(1024)^n θ⌋))` gives `LandsN (Int.fract ((1024)^n θ)) z₁` from `1024^n θ = Int.fract (1024^n θ) + ⌊1024^n θ⌋`.  The pattern to copy is `hland_pow` inside `Submission/Work/SeedSimple2/Rotation/arcBound_of_sidePreserve.lean`. -/
theorem landsN_pow {c : ℂ} (d : Work.EL.RootParabolic c) {θ : ℝ}
    (hθ : θ ∈ Work.SeedSimple2.LandAngles d.hN d.z₁) (n : ℕ) :
    Int.fract ((1024 : ℝ) ^ n * θ) ∈ Work.SeedSimple2.LandAngles d.hN d.z₁ := by
  obtain ⟨hθIco, hθland⟩ := hθ
  -- `z₁` is fixed by every iterate of `T_c^[5]`, hence by `T_c^[10 * n]`
  have hfix5 : ∀ m : ℕ, ((Tantibar c)^[5])^[m] d.z₁ = d.z₁ := by
    intro m
    induction m with
    | zero => simp
    | succ m ih => rw [Function.iterate_succ_apply', ih, d.per_half]
  -- the `10 * n`-th iterate of the ray of angle `θ` lands at `z₁`
  have h1 : Work.EL.LandsN d.hN ((Work.EL.T^[10 * n]) θ) d.z₁ := by
    have h := Work.SeedSimple2.landsN_T_iterate d (10 * n) hθland
    rw [show (Tantibar c)^[10 * n] d.z₁ = ((Tantibar c)^[5])^[2 * n] d.z₁ by
      rw [show 10 * n = 5 * (2 * n) by ring, Function.iterate_mul], hfix5 (2 * n)] at h
    exact h
  -- the iterate of the angle map equals `1024^n θ` up to an integer
  obtain ⟨m, hm⟩ := Work.ELRig.T_iterate_eq_add_int θ (10 * n)
  have hm' : (Work.EL.T^[10 * n]) θ = (1024 : ℝ) ^ n * θ + (m : ℝ) := by
    rw [hm]
    congr 1
    rw [show ((-2 : ℝ)) ^ (10 * n) = (1024 : ℝ) ^ n by rw [pow_mul]; norm_num]
  have hpow : Work.EL.LandsN d.hN ((1024 : ℝ) ^ n * θ) d.z₁ :=
    (Work.SeedSimple2.landsN_add_int d m).mp (hm' ▸ h1)
  -- normalise the angle modulo `1`
  refine ⟨⟨Int.fract_nonneg _, Int.fract_lt_one _⟩, ?_⟩
  have h : Int.fract ((1024 : ℝ) ^ n * θ)
      = (1024 : ℝ) ^ n * θ + (↑(-⌊(1024 : ℝ) ^ n * θ⌋) : ℝ) := by
    have h2 := Int.fract_add_floor ((1024 : ℝ) ^ n * θ)
    push_cast
    linarith
  rw [h]
  exact (Work.SeedSimple2.landsN_add_int d (-⌊(1024 : ℝ) ^ n * θ⌋)).mpr hpow

end Work.SeedSimple2.COP
