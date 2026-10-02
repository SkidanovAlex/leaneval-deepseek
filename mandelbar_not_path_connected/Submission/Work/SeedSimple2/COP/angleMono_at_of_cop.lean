import Mathlib
import Submission.Work.SeedSimple2.Defs
import Submission.Work.SeedSimple2.COP.landsN_pow
import Submission.Work.SeedSimple2.Rotation.rotationZero_of_step
import Submission.Work.SeedSimple2.Mono.fract_sub_alpha1_ne
import Submission.Work.SeedSimple2.Rotation.arcBound_of_sidePreserve
import Submission.Work.SeedSimple2.TwoRays

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


namespace Work.SeedSimple2.COP

/-- **`L9` with the conclusion of `L7` and the `L3` consequences as explicit hypotheses** (`NOTES_LEAD_mandelbar_rn0.md` §2, `L9`; `COP/NOTES_COP.md` §4).

`hcop` is the conclusion of `Work.SeedSimple2.COP.cop_angles d hJ` (cyclic-order preservation, angle form) and `hiter` is `Work.SeedSimple2.COP.theta_iterate_ne`.  The wrapper `Work.SeedSimple2.COP.angleMono_proved` instantiates both.

Proof design.  Let `θ ∈ A` with `Int.fract (1024 * θ) ≠ θ`, put `θₙ := Int.fract ((1024:ℝ)^n * θ)` and `wₙ := Int.fract ((1024:ℝ)^n * θ - α₁)`.  By `Work.SeedSimple2.COP.landsN_pow` (and `d.per_half` for the iterates of `z₁`), `θₙ ∈ A`;  `α₁ ∈ A` from `d.rays.1` via `Work.SeedSimple2.landsN_iff_landsAt`;  `hiter` at `θ` supplies `θₙ ≠ θₙ₊₁`, `θₙ ≠ α₁`, `θₙ ≠ 0`.  Apply `hcop` to `(x, a, e) = (θₙ, α₁, θₙ₊₁)`;  since `Int.fract (1024 * θₙ) = θₙ₊₁`, `Int.fract (1024 * α₁) = α₁` (`Work.SeedSimple2.Rotation.mul_alpha1`) and `Int.fract (1024 * θₙ₊₁) = θₙ₊₂`, this is `Work.EL.InArc θₙ α₁ θₙ₊₁ ↔ Work.EL.InArc θₙ₊₁ α₁ θₙ₊₂`, i.e. `(wₙ < wₙ₊₁) ↔ (wₙ₊₁ < wₙ₊₂)` (unfold `Work.EL.InArc`, `Work.EL.arcLen`;  `wₙ > 0` by `θₙ ≠ α₁`).  So `(wₙ < wₙ₊₁) ↔ (w₀ < w₁)` for every `n`.  Finally `wₙ ≠ wₙ₊₁` by `Work.SeedSimple2.Mono.fract_sub_alpha1_ne` applied to `θₙ ≠ θₙ₊₁` (both in `Set.Ico 0 1`), so either all `wₙ < wₙ₊₁` or all `wₙ₊₁ < wₙ`. -/
theorem angleMono_at_of_cop {c : ℂ} (d : Work.EL.RootParabolic c)
    (hcop : ∀ {x a e : ℝ}, x ∈ Work.SeedSimple2.LandAngles d.hN d.z₁ →
      a ∈ Work.SeedSimple2.LandAngles d.hN d.z₁ →
      e ∈ Work.SeedSimple2.LandAngles d.hN d.z₁ →
      a ≠ 0 → e ≠ 0 → x ≠ a → x ≠ e → a ≠ e →
      (Work.EL.InArc x a e ↔
        Work.EL.InArc (Int.fract (1024 * x)) (Int.fract (1024 * a)) (Int.fract (1024 * e))))
    (hiter : ∀ {θ : ℝ}, θ ∈ Work.SeedSimple2.LandAngles d.hN d.z₁ →
      Int.fract (1024 * θ) ≠ θ →
      (∀ n : ℕ, Int.fract ((1024:ℝ)^n * θ) ≠ Int.fract ((1024:ℝ)^(n+1) * θ)) ∧
      (∀ n : ℕ, Int.fract ((1024:ℝ)^n * θ) ≠ Work.EL.alpha1) ∧
      (∀ n : ℕ, Int.fract ((1024:ℝ)^n * θ) ≠ 0)) :
    Work.SeedSimple2.Rotation.AngleMonoAt d := by
  -- ## Elementary facts about `Int.fract`
  -- `fract` is unchanged by subtracting the integer part first: `fract (fract y - a) = fract (y - a)`.
  have hffs : ∀ y a : ℝ, Int.fract (Int.fract y - a) = Int.fract (y - a) := by
    intro y a
    have h : Int.fract y - a = (y - a) - ((⌊y⌋ : ℤ) : ℝ) := by
      have := Int.fract_add_floor y
      linarith
    rw [h, Int.fract_sub_intCast]
  -- An integer multiple of a fractional part has the fractional part of the multiple
  -- of the number itself; for the multiplier `1024` this raises the exponent by one.
  have hmul : ∀ (y : ℝ) (m : ℕ),
      Int.fract (1024 * Int.fract ((1024:ℝ)^m * y)) = Int.fract ((1024:ℝ)^(m+1) * y) := by
    intro y m
    have h : Int.fract ((1024:ℝ)^m * y)
        = (1024:ℝ)^m * y - ((⌊(1024:ℝ)^m * y⌋ : ℤ) : ℝ) := by
      have := Int.fract_add_floor ((1024:ℝ)^m * y)
      linarith
    rw [h]
    rw [show (1024:ℝ) * ((1024:ℝ)^m * y - ((⌊(1024:ℝ)^m * y⌋ : ℤ) : ℝ))
        = (1024:ℝ) * ((1024:ℝ)^m * y) - (((1024 : ℤ) * ⌊(1024:ℝ)^m * y⌋ : ℤ) : ℝ) by
      push_cast
      ring]
    rw [Int.fract_sub_intCast]
    congr 1
    rw [pow_succ]
    ring
  -- `α₁` is a fixed point of the angle map `θ ↦ fract (1024 θ)`.
  have halpha1 : Int.fract (1024 * Work.EL.alpha1) = Work.EL.alpha1 := by
    rw [Work.SeedSimple2.Rotation.mul_alpha1]
    rw [show (371:ℝ) + Work.EL.alpha1 = Work.EL.alpha1 + ((371:ℤ):ℝ) by push_cast; ring]
    rw [Int.fract_add_intCast, Int.fract_eq_self]
    exact ⟨by norm_num [Work.EL.alpha1], by norm_num [Work.EL.alpha1]⟩
  -- An element of `[0,1)` different from `α₁` has a strictly positive `α₁`-shifted
  -- fractional part.
  have hpos : ∀ {x : ℝ}, x ∈ Set.Ico 0 1 → x ≠ Work.EL.alpha1 →
      0 < Int.fract (x - Work.EL.alpha1) := by
    intro x hx hxne
    have hne0 : Int.fract (x - Work.EL.alpha1) ≠ 0 := by
      intro h0
      obtain ⟨z, hz⟩ := Set.mem_range.mp (Int.fract_eq_zero_iff.mp h0)
      have hzlt : (z:ℝ) < 1 := by
        linarith [hx.2, hz, (by norm_num [Work.EL.alpha1] : (0:ℝ) < Work.EL.alpha1)]
      have hzgt : (-1:ℝ) < (z:ℝ) := by
        linarith [hx.1, hz, (by norm_num [Work.EL.alpha1] : Work.EL.alpha1 < 1)]
      have hz0 : z = 0 := by
        have h1 : z < 1 := by exact_mod_cast hzlt
        have h2 : -1 < z := by exact_mod_cast hzgt
        omega
      have hzero : x - Work.EL.alpha1 = 0 := by
        rw [← hz, hz0]
        norm_num
      exact hxne (by linarith)
    exact lt_of_le_of_ne (Int.fract_nonneg _) (Ne.symm hne0)
  -- ## `α₁` is a landing angle
  have hα1mem : Work.EL.alpha1 ∈ Work.SeedSimple2.LandAngles d.hN d.z₁ :=
    ⟨⟨by norm_num [Work.EL.alpha1], by norm_num [Work.EL.alpha1]⟩,
      (Work.ELTop.landsN_iff_landsAt d.hN d.bottcher Work.EL.alpha1 d.z₁).mpr d.rays.1⟩
  have hα1ne0 : Work.EL.alpha1 ≠ 0 := by norm_num [Work.EL.alpha1]
  -- ## The orbit of a non-fixed landing angle
  intro θ hθ hne
  obtain ⟨hiter1, hiter2, hiter3⟩ := hiter hθ hne
  let t : ℕ → ℝ := fun n => Int.fract ((1024:ℝ)^n * θ)
  let w : ℕ → ℝ := fun n => Int.fract ((1024:ℝ)^n * θ - Work.EL.alpha1)
  have htIco : ∀ n : ℕ, t n ∈ Set.Ico 0 1 := fun n => ⟨Int.fract_nonneg _, Int.fract_lt_one _⟩
  have htA : ∀ n : ℕ, t n ∈ Work.SeedSimple2.LandAngles d.hN d.z₁ := fun n => landsN_pow d hθ n
  have htne : ∀ n : ℕ, t n ≠ t (n+1) := fun n => hiter1 n
  have htnalpha : ∀ n : ℕ, t n ≠ Work.EL.alpha1 := fun n => hiter2 n
  have htzero : ∀ n : ℕ, t n ≠ 0 := fun n => hiter3 n
  have htstep : ∀ n : ℕ, Int.fract (1024 * t n) = t (n+1) := by
    intro n
    show Int.fract (1024 * Int.fract ((1024:ℝ)^n * θ)) = Int.fract ((1024:ℝ)^(n+1) * θ)
    exact hmul θ n
  have hwt : ∀ n : ℕ, Int.fract (t n - Work.EL.alpha1) = w n := by
    intro n
    show Int.fract (Int.fract ((1024:ℝ)^n * θ) - Work.EL.alpha1)
      = Int.fract ((1024:ℝ)^n * θ - Work.EL.alpha1)
    exact hffs _ _
  have hwne : ∀ n : ℕ, w n ≠ w (n+1) := by
    intro n
    have h := Work.SeedSimple2.Mono.fract_sub_alpha1_ne (htIco n) (htIco (n+1)) (htne n)
    rw [hwt n, hwt (n+1)] at h
    exact h.symm
  -- The arc membership of `t n` in `(α₁, t (n+1))` is exactly `w n < w (n+1)`.
  have hInArc : ∀ n : ℕ, Work.EL.InArc (t n) Work.EL.alpha1 (t (n+1)) ↔ (w n < w (n+1)) := by
    intro n
    have hp : 0 < w n := by
      rw [← hwt n]
      exact hpos (htIco n) (htnalpha n)
    rw [Work.EL.InArc, Work.EL.arcLen, hwt n, hwt (n+1)]
    exact ⟨fun h => h.2, fun h => ⟨hp, h⟩⟩
  -- The cyclic-order preservation `hcop`, read on the sequence `w`.
  have hstep : ∀ n : ℕ, (w n < w (n+1)) ↔ (w (n+1) < w (n+2)) := by
    intro n
    have hc := hcop (x := t n) (a := Work.EL.alpha1) (e := t (n+1))
      (htA n) hα1mem (htA (n+1)) hα1ne0 (htzero (n+1)) (htnalpha n) (htne n)
      (htnalpha (n+1)).symm
    rw [htstep n, htstep (n+1), halpha1] at hc
    exact (hInArc n).symm.trans (hc.trans (hInArc (n+1)))
  have hall : ∀ n : ℕ, (w n < w (n+1)) ↔ (w 0 < w 1) := by
    intro n
    induction n with
    | zero => exact Iff.rfl
    | succ k ih => exact ((hstep k).symm).trans ih
  -- Either the whole sequence is increasing or the whole sequence is decreasing.
  by_cases h0 : w 0 < w 1
  · left
    intro n
    show w n < w (n+1)
    exact (hall n).mpr h0
  · right
    intro n
    show w (n+1) < w n
    have h1 : ¬ (w n < w (n+1)) := fun hh => h0 ((hall n).mp hh)
    exact lt_of_le_of_ne (not_lt.mp h1) (hwne n).symm

end Work.SeedSimple2.COP
