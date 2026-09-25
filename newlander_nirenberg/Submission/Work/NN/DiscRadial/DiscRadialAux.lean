/-
Copyright: none.  Part of the `Newlander-Nirenberg` formalisation project.

# Auxiliary definitions for the radial (one-sided) disc extension

The radial Seeley extension `Work.NN.Final.discExt` of `DiscRadialDefs` extends a function
from the unit disc to the disc of radius `c > 1` by the sum

  `discSum k a b g p = ∑_{m ≤ k} a m • (χ (b m * (‖p.2‖ - 1)) • g (p.1, discRefl (b m) p.2))`

on the annulus `1 < ‖p.2‖ < c`.  This file collects the small objects attached to a single
term of that sum, so that the estimates for them can be stated and delegated separately.
-/
import Mathlib
import Submission.Work.NN.Final.DiscRadialDefs
import Submission.Work.NN.Final.HolderCongr
import Submission.Work.CR.Flat.Holder.holderNorm_comp_le_of_contDiffOn
import Submission.Work.CR.Flat.Holder.holderNorm_mul_le
import Submission.Work.CR.Flat.Holder.holderNorm_smul
import Submission.Work.CR.Flat.Holder.holderNorm_add_le

noncomputable section

open scoped NNReal ENNReal ContDiff
open Set Metric

namespace Work.NN.DiscRadial

open Work.NN.Final Work.CR.Flat

variable {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]

/-- The radial region `1 < ‖z‖ < 1 + 2/b` on which the `m`-th term of the radial Seeley
sum (with scale `b`) lives: there `χ (b * (‖z‖ - 1)) ≠ 0` and the reflected point
`discRefl b z` lies strictly inside the unit disc. -/
def annR (b : ℝ) : Set ℂ := {z : ℂ | 1 < ‖z‖ ∧ ‖z‖ < 1 + 2 / b}

/-- The reflection map `p ↦ (p.1, discRefl b p.2)`, as a map of `X × ℂ` to itself. -/
def reflMap (b : ℝ) (p : X × ℂ) : X × ℂ := (p.1, discRefl b p.2)

/-- The cutoff factor `p ↦ (χ (b * (‖p.2‖ - 1)) : ℂ)` of the `m`-th term of the radial
Seeley sum, extended to all of `X × ℂ`. -/
def cutFun (b : ℝ) (p : X × ℂ) : ℂ := ((seeleyCut (b * (‖p.2‖ - 1)) : ℝ) : ℂ)

/-- The `m`-th term of the radial Seeley sum, written with the two factors separated. -/
lemma discTerm_eq (a b : ℕ → ℝ) (g : X × ℂ → ℂ) (m : ℕ) (p : X × ℂ) :
    discTerm a b g m p = (a m : ℂ) * (cutFun (b m) p * g (reflMap (b m) p)) := by
  rw [discTerm, cutFun, reflMap, Complex.real_smul, Complex.real_smul]

/-- The reflected point lies strictly inside the unit disc on `annR b` (for `b > 0`). -/
lemma norm_reflMap_snd_lt_one {b : ℝ} (hb : 0 < b) {p : X × ℂ} (hp : p.2 ∈ annR b) :
    ‖(reflMap b p).2‖ < 1 := by
  obtain ⟨h1, h2⟩ := hp
  have hz0 : p.2 ≠ 0 := by intro h; rw [h] at h1; simp at h1; linarith
  rw [reflMap, norm_discRefl b hz0]
  have hpos : 0 < b * (‖p.2‖ - 1) := mul_pos hb (by linarith)
  have hlt : b * (‖p.2‖ - 1) < 2 := by
    have hb2 : b * (1 + 2 / b) = b + 2 := by field_simp
    nlinarith [h2, hb, hb2]
  rw [abs_lt]
  constructor <;> linarith

end Work.NN.DiscRadial
