/-
# `Submission.Work.FIArea3.JointCount.card_jointPieceLat_le`

The joint count of the polar box inside a Gaussian-divisor piece `w ℤ[i]` cut by the
congruence `e ∣ Δ(z₁, ·)`:

  `#{z ∈ polarBoxFinset Pa φ : w ∣ z ∧ e ∣ Δ(z₁,z)} ≤ πu²/c + 80u/√(|w|²) + 1`,
  `u = θ√N`, `c = index (jointPieceLat z₁ w e)`.

The lattice of the counted set, `Λ := {z : w ∣ z ∧ e ∣ Δ(z₁,z)}`, is the image under
`y ↦ y·w` of the congruence lattice `yLat (re s) (im s) e`, `s = star z₁ * w` — the
*transpose* of the lattice underlying `jointPieceLat z₁ w e` (see `countDefs.lean`); the two
have the same index because `gcd` is symmetric.  By `jointPieceBoxLat_basis` the lattice `Λ`
has a two-element `ℤ`-basis `g₁, g₂` with `|det (g₁,g₂)| = c` and
`√|g₁|² + √|g₂|² ≤ 5c/√(|w|²)`, so the sharp Blichfeldt count `polarBox_lattice_count_sharp`
gives `#· ≤ πu²/c + 16u(√|g₁|²+√|g₂|²)/c + 1 ≤ πu²/c + 80u/√(|w|²) + 1`.
-/
import Mathlib
import Submission.Work.FIArea3.JointCount.countDefs
import Submission.Work.FIArea3.JointCount.polarBox_lattice_count_sharp
import Submission.Work.FIArea3.JointCount.jointPieceLat_basis
import Submission.Work.FIArea3.JointCount.index_jointPieceLat
import Submission.Work.FIArea3.JointCount.jointPieceBoxLat_basis

namespace Work.FIArea3.JointCount

open Finset Work.FIPlan

noncomputable section

attribute [local instance] Classical.propDecidable

/-- The index of `jointPieceLat z₁ w e` is positive. -/
lemma one_le_index_jointPieceLat (z₁ w : GaussianInt) (e : ℕ) (hw : w ≠ 0) (he : 1 ≤ e) :
    1 ≤ (jointPieceLat z₁ w e).index := by
  rw [index_jointPieceLat z₁ w e he hw]
  have hgw : 1 ≤ gnorm w := by
    refine Nat.one_le_iff_ne_zero.mpr ?_
    intro h
    exact hw ((jpl_gnorm_eq_zero_iff w).mp h)
  have hgcd : 0 < Nat.gcd e (Nat.gcd (star z₁ * w).im.natAbs (star z₁ * w).re.natAbs) :=
    Nat.gcd_pos_of_pos_left _ (by omega)
  have hdiv : 1 ≤ e / Nat.gcd e (Nat.gcd (star z₁ * w).im.natAbs (star z₁ * w).re.natAbs) := by
    have := Nat.div_pos (Nat.gcd_le_left _ (by omega : 0 < e)) hgcd
    omega
  simpa using Nat.mul_le_mul hgw hdiv

theorem card_jointPieceLat_le (Pa : Work.FITop.Params) (φ : ℝ) (z₁ w : GaussianInt) (e : ℕ)
    (hw : w ≠ 0) (he : 1 ≤ e) :
    ((Work.FIArea3.JointCount.jointPieceBoxFinset Pa φ z₁ w e).card : ℝ)
      ≤ Real.pi * (Pa.θ * Real.sqrt Pa.N) ^ 2
          / ((Work.FIArea3.JointCount.jointPieceLat z₁ w e).index : ℝ)
        + 80 * (Pa.θ * Real.sqrt Pa.N) / Real.sqrt ((Work.FIPlan.gnorm w : ℝ))
        + 1 := by
  have hBasis : ∃ g₁ g₂ : GaussianInt,
      (g₁.re * g₂.im - g₁.im * g₂.re).natAbs = (jointPieceLat z₁ w e).index
      ∧ ((yLat (star z₁ * w).re (star z₁ * w).im e).map (AddMonoidHom.mulRight w)).carrier
          = {z : GaussianInt | ∃ a b : ℤ, z = (a : GaussianInt) * g₁ + (b : GaussianInt) * g₂}
      ∧ Real.sqrt ((gnorm g₁ : ℝ)) + Real.sqrt ((gnorm g₂ : ℝ))
          ≤ ((jointPieceLat z₁ w e).index : ℝ) * (5 / Real.sqrt ((gnorm w : ℝ))) :=
    jointPieceBoxLat_basis z₁ w e hw he
  -- The lattice of the counted set: `z` lies in `(yLat (re s) (im s) e).map (mulRight w)`,
  -- `s = star z₁ * w`, iff `w ∣ z` and `e ∣ Δ(z₁,z)`.
  have hMem : ∀ z : GaussianInt,
      z ∈ (yLat (star z₁ * w).re (star z₁ * w).im e).map (AddMonoidHom.mulRight w)
        ↔ w ∣ z ∧ e ∣ absDelta z₁ z := by
    have key : ∀ n : ℤ, (e ∣ n.natAbs) ↔ (e : ℤ) ∣ n := by
      intro n
      have h := Int.natAbs_dvd_natAbs (a := (e : ℤ)) (b := n)
      simpa using h
    have hprod : ∀ a y w : GaussianInt,
        (a * (y * w)).im = (a * w).re * y.im + (a * w).im * y.re := by
      intro a y w
      rw [← mul_assoc]
      simp only [Zsqrtd.im_mul, Zsqrtd.re_mul]
      ring
    intro z
    rw [AddSubgroup.mem_map]
    constructor
    · rintro ⟨y, hy, hyz⟩
      have hyw : y * w = z := hyz
      refine ⟨⟨y, ?_⟩, ?_⟩
      · rw [← hyw, mul_comm]
      · rw [absDelta, Delta, ← hyw, hprod]
        exact (key _).mpr hy
    · rintro ⟨⟨y, hyz⟩, hdvd⟩
      have hyw : y * w = z := by rw [hyz, mul_comm]
      rw [absDelta, Delta, ← hyw, hprod] at hdvd
      exact ⟨y, (key _).mp hdvd, hyw⟩
  classical
  obtain ⟨g₁, g₂, hdet, hcarrier, hlen⟩ := hBasis
  have hidx1 : 1 ≤ (jointPieceLat z₁ w e).index := one_le_index_jointPieceLat z₁ w e hw he
  have hsub : (↑(jointPieceBoxFinset Pa φ z₁ w e) : Set GaussianInt) ⊆
      {z : GaussianInt | z ∈ Work.FIArea3.polarBoxFinset Pa φ ∧
        ∃ a b : ℤ, z - (0 : GaussianInt) = (a : GaussianInt) * g₁ + (b : GaussianInt) * g₂} := by
    intro z hz
    have hz' : z ∈ jointPieceBoxFinset Pa φ z₁ w e := hz
    rw [jointPieceBoxFinset, Finset.mem_filter] at hz'
    refine ⟨hz'.1, ?_⟩
    have hmemL : z ∈ (yLat (star z₁ * w).re (star z₁ * w).im e).map
        (AddMonoidHom.mulRight w) := (hMem z).mpr ⟨hz'.2.1, hz'.2.2⟩
    have hsp : z ∈ {z : GaussianInt | ∃ a b : ℤ,
        z = (a : GaussianInt) * g₁ + (b : GaussianInt) * g₂} := by
      rw [← hcarrier]
      exact hmemL
    obtain ⟨a, b, hab⟩ := hsp
    exact ⟨a, b, by simpa using hab⟩
  have hfinite : ({z : GaussianInt | z ∈ Work.FIArea3.polarBoxFinset Pa φ ∧
      ∃ a b : ℤ, z - (0 : GaussianInt) = (a : GaussianInt) * g₁ + (b : GaussianInt) * g₂}).Finite :=
    (Finset.finite_toSet (Work.FIArea3.polarBoxFinset Pa φ)).subset (fun z hz => hz.1)
  have hcard_le : ((jointPieceBoxFinset Pa φ z₁ w e).card : ℝ) ≤
      (({z : GaussianInt | z ∈ Work.FIArea3.polarBoxFinset Pa φ ∧
        ∃ a b : ℤ, z - (0 : GaussianInt) = (a : GaussianInt) * g₁ + (b : GaussianInt) * g₂}).ncard : ℝ) := by
    rw [← Set.ncard_coe_finset]
    exact_mod_cast Set.ncard_le_ncard hsub hfinite
  have hsharp := polarBox_lattice_count_sharp Pa φ (0 : GaussianInt) g₁ g₂
      ((jointPieceLat z₁ w e).index) hdet hidx1
  have hstep : 16 * (Pa.θ * Real.sqrt Pa.N)
        * (Real.sqrt ((gnorm g₁ : ℝ)) + Real.sqrt ((gnorm g₂ : ℝ)))
        / ((jointPieceLat z₁ w e).index : ℝ)
      ≤ 80 * (Pa.θ * Real.sqrt Pa.N) / Real.sqrt ((gnorm w : ℝ)) := by
    have hu : 0 ≤ Pa.θ * Real.sqrt Pa.N := mul_nonneg Pa.hθ0.le (Real.sqrt_nonneg _)
    have hc : (0 : ℝ) < ((jointPieceLat z₁ w e).index : ℝ) := by
      have : 0 < (jointPieceLat z₁ w e).index := by omega
      exact_mod_cast this
    have hgw : 0 < (gnorm w : ℝ) := by
      have : 0 < gnorm w := jpl_gnorm_pos hw
      exact_mod_cast this
    have hswn : Real.sqrt ((gnorm w : ℝ)) ≠ 0 := ne_of_gt (Real.sqrt_pos.mpr hgw)
    have hmul : 16 * (Pa.θ * Real.sqrt Pa.N)
          * (Real.sqrt ((gnorm g₁ : ℝ)) + Real.sqrt ((gnorm g₂ : ℝ)))
        ≤ 16 * (Pa.θ * Real.sqrt Pa.N)
          * (((jointPieceLat z₁ w e).index : ℝ) * (5 / Real.sqrt ((gnorm w : ℝ)))) :=
      mul_le_mul_of_nonneg_left hlen (by linarith)
    calc 16 * (Pa.θ * Real.sqrt Pa.N)
          * (Real.sqrt ((gnorm g₁ : ℝ)) + Real.sqrt ((gnorm g₂ : ℝ)))
          / ((jointPieceLat z₁ w e).index : ℝ)
        ≤ 16 * (Pa.θ * Real.sqrt Pa.N)
          * (((jointPieceLat z₁ w e).index : ℝ) * (5 / Real.sqrt ((gnorm w : ℝ))))
          / ((jointPieceLat z₁ w e).index : ℝ) := div_le_div_of_nonneg_right hmul hc.le
      _ = 80 * (Pa.θ * Real.sqrt Pa.N) / Real.sqrt ((gnorm w : ℝ)) := by
          field_simp
          ring
  linarith [hcard_le, hsharp, hstep]

end

end Work.FIArea3.JointCount
