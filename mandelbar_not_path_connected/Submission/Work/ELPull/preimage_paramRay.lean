/-
# Preimages of a dynamical parameter ray under `Tantibar c`

`Tantibar c z = (conj z)^2 + c` acts on the dynamical rays of its Böttcher coordinate `φ` by
angle doubling: `φ (T_c z) = conj (φ z)^2` sends the ray of angle `θ` into the ray of angle
`T θ = -2θ mod 1` (`Work.ELPull.rayPt_Tantibar`, `landsN_image`).  The present file proves the
converse *one-step* statement: the preimage of any point of the ray at angle `θ` lies on one of
the two rays of the half angle, namely those at the angles

  `fract (-θ/2)`  and  `fract (-θ/2 + 1/2)`.

## The argument

Suppose `y = T_c z` lies on the ray of angle `θ`: `y ∉ K_c` and `φ y = rayPoint θ t` with `t > 1`.
Since the filled Julia set is backward invariant, `z ∉ K_c`, so the Böttcher equation applies at
`z`:

  `conj (φ z)^2 = φ (T_c z) = rayPoint θ t`,  hence  `φ z ^ 2 = rayPoint (-θ) t`.

The two square roots of `rayPoint (-θ) t` are exactly
`rayPoint (fract (-θ/2)) (√t)` and `rayPoint (fract (-θ/2 + 1/2)) (√t)` — the square of the first
is `rayPoint (-θ) t` (`rayPoint_half_sq`, the arithmetic of `2·fract(a/2) ≡ a (mod 1)`), and the
second is its negative (`rayPoint_fract_half_neg`, from `rayPoint (a + 1/2) s = - rayPoint a s`,
i.e. `exp (π i) = -1`).  Since `√t > 1`, whichever of the two equals `φ z` exhibits `z` as a
point of the corresponding ray.

## Main results

* `Work.ELPull.rayPoint_add_half`, `rayPoint_half_sq`, `rayPoint_fract_half_neg`,
  `sq_eq_rayPoint_half_or` : the angle arithmetic of the two half-angle square roots.
* `Work.ELPull.preimage_paramRay` : the preimage of the dynamical ray of angle `θ` is contained in
  the union of the two dynamical rays of the half angles.
-/
import Mathlib
import Submission.Work.ELPull.Defs
import Submission.Work.ELPull.landsN_image

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


open Classical Set Function Filter
open scoped Topology ComplexConjugate

namespace Work.ELPull

open LeanEval.ComplexAnalysis (Tantibar Mandelbar)

/-! ## Angle arithmetic of the half-angle square roots -/

/-- Shifting the angle by `1/2` negates the ray point: `rayPoint (a + 1/2) s = - rayPoint a s`
(because `exp (2πi(a + 1/2)) = - exp (2πi a)`). -/
theorem rayPoint_add_half (a s : ℝ) :
    Work.Top.NakaneData.rayPoint (a + 1/2) s = - Work.Top.NakaneData.rayPoint a s := by
  rw [Work.Top.NakaneData.rayPoint, Work.Top.NakaneData.rayPoint]
  rw [show (2:ℂ) * ↑Real.pi * ((a + 1/2 : ℝ) : ℂ) * Complex.I
      = 2 * ↑Real.pi * (a:ℂ) * Complex.I + (↑Real.pi * Complex.I) by push_cast; ring]
  rw [Complex.exp_add, Complex.exp_pi_mul_I]
  ring

/-- `rayPoint (fract (a/2)) (√t)` is a square root of `rayPoint a t`: this is the arithmetic
`2 · fract (a/2) ≡ a (mod 1)` together with `rayPoint a u ^ 2 = rayPoint (2a) (u^2)`. -/
theorem rayPoint_half_sq (a t : ℝ) (ht : 0 ≤ t) :
    (Work.Top.NakaneData.rayPoint (Int.fract (a / 2)) (Real.sqrt t)) ^ 2
      = Work.Top.NakaneData.rayPoint a t := by
  rw [rayPoint_sq, Real.sq_sqrt ht]
  have h : (2:ℝ) * Int.fract (a/2) = a + ((-2 * ⌊a/2⌋ : ℤ) : ℝ) := by
    rw [Int.fract]; push_cast; ring
  rw [h, rayPoint_periodic]

/-- The second half-angle ray point is the negative of the first:
`- rayPoint (fract (a/2)) s = rayPoint (fract (a/2 + 1/2)) s`. -/
theorem rayPoint_fract_half_neg (a s : ℝ) :
    - Work.Top.NakaneData.rayPoint (Int.fract (a / 2)) s
      = Work.Top.NakaneData.rayPoint (Int.fract (a / 2 + 1 / 2)) s := by
  rw [← rayPoint_mod_one (a / 2 + 1 / 2) s, rayPoint_add_half (a / 2) s,
    ← rayPoint_mod_one (a / 2) s]

/-- **The two square roots of `rayPoint a t`.**  If `w ^ 2 = rayPoint a t` with `t ≥ 0`, then `w`
is one of `rayPoint (fract (a/2)) (√t)` and `rayPoint (fract (a/2 + 1/2)) (√t)`. -/
theorem sq_eq_rayPoint_half_or {a t : ℝ} (ht : 0 ≤ t) {w : ℂ}
    (h : w ^ 2 = Work.Top.NakaneData.rayPoint a t) :
    w = Work.Top.NakaneData.rayPoint (Int.fract (a / 2)) (Real.sqrt t) ∨
      w = Work.Top.NakaneData.rayPoint (Int.fract (a / 2 + 1 / 2)) (Real.sqrt t) := by
  have hu := rayPoint_half_sq a t ht
  rcases sq_eq_sq_iff_eq_or_eq_neg.mp (hu.trans h.symm) with h1 | h1
  · exact Or.inl h1.symm
  · refine Or.inr ?_
    rw [show w = - Work.Top.NakaneData.rayPoint (Int.fract (a / 2)) (Real.sqrt t) by
      rw [h1, neg_neg]]
    exact rayPoint_fract_half_neg a (Real.sqrt t)

/-! ## The preimage of a ray lies on the two half-angle rays -/

/-- **One-step preimages of a dynamical ray.**  A preimage under `Tantibar c` of a point of the
dynamical ray of angle `θ` lies on the ray of angle `fract (-θ/2)` or on the ray of angle
`fract (-θ/2 + 1/2)`.  (The level of the preimage ray is the square root of the level of `θ`.) -/
theorem preimage_paramRay {c : ℂ} (hN : DynB c)
    (hφ : Work.ParamRays.IsDynBottcher c (Work.ParamRays.dynPhiOf c)) (θ : ℝ) :
    {z : ℂ | LeanEval.ComplexAnalysis.Tantibar c z ∈ hN.paramRay θ}
      ⊆ hN.paramRay (Int.fract (-θ / 2)) ∪ hN.paramRay (Int.fract (-θ / 2 + 1 / 2)) := by
  intro z hz
  simp only [Set.mem_ofPred_eq] at hz
  rw [Work.Top.NakaneData.mem_paramRay_iff] at hz
  obtain ⟨hyK, t, ht1, hyt⟩ := hz
  -- the filled Julia set is backward invariant, so `z` escapes as well
  have hyK' : Tantibar c z ∉ Work.ParamRays.filledJulia c := hyK
  have hzesc : Work.ParamRays.Escaping c z := by
    rw [Work.ParamRays.escaping_iff_not_bounded]
    intro hb
    obtain ⟨M, hM⟩ := hb
    exact hyK' ⟨M, fun n => by
      rw [← Work.ParamRays.orbit_one_add c z n]; exact hM (n+1)⟩
  have hzK : z ∉ Work.ParamRays.filledJulia c :=
    (Work.ParamRays.escaping_iff_not_bounded c z).mp hzesc
  -- the Böttcher equation at `z`, and the resulting square-root equation
  have hfe := dynPhi_Tantibar hφ hzK
  have hconj : (starRingEnd ℂ) (Work.ParamRays.dynPhi c z) ^ 2
      = Work.Top.NakaneData.rayPoint θ t := by
    rw [← hfe, hyt]
  have hw2 : (Work.ParamRays.dynPhi c z) ^ 2 = Work.Top.NakaneData.rayPoint (-θ) t := by
    have h1 : (starRingEnd ℂ) ((starRingEnd ℂ) (Work.ParamRays.dynPhi c z) ^ 2)
        = (Work.ParamRays.dynPhi c z) ^ 2 := by
      rw [map_pow, Complex.conj_conj]
    rw [← h1, hconj, rayPoint_neg_conj]
  have ht0 : 0 ≤ t := le_of_lt (lt_trans zero_lt_one ht1)
  have hsqrt : 1 < Real.sqrt t := (Real.lt_sqrt zero_le_one).mpr (by simpa using ht1)
  rw [Set.mem_union]
  rcases sq_eq_rayPoint_half_or ht0 hw2 with hw | hw
  · left
    rw [Work.Top.NakaneData.mem_paramRay_iff]
    exact ⟨hzK, Real.sqrt t, hsqrt, hw⟩
  · right
    rw [Work.Top.NakaneData.mem_paramRay_iff]
    exact ⟨hzK, Real.sqrt t, hsqrt, hw⟩

end Work.ELPull
