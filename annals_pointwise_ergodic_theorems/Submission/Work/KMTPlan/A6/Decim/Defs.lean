/-
# Shared vocabulary for the KMSZ (6.22) decimation identity for the low-pass Ionescu--Wainger walk

Target: `Work.KMTPlan.A6.kmtProj_deep_eq_decimComp`, i.e. the factorisation

`kmtProj ρ l₁ (-(m₀+n)) = D_{Φ_{m₀+n}} ∘ kmtProj ρ l₁ (-(m₀))`

where `D_{Φ_L} h y = Σ'_j decimatedKernel Q Φ_L (y-j) · h j` is the `Q`-decimated kernel family,
`Q = iwQl ρ l₁`, and `Φ_L = etaCut kmtEta (-(L:ℤ))`.

This file fixes the two objects in terms of which the whole development is phrased:

* `circPt Q a = a/Q ∈ ℝ/ℤ`, and `torsFinset Q = {a/Q : a < Q}` — the `Q`-torsion subgroup of the
  circle, as a `Finset` (the "coarse arc set" `Φ` of the KMSZ (6.22) weight factor);
* `bump L = periodize (etaCut kmtEta (-(L:ℤ)))` — the circle symbol `ξ ↦ η (2^L ξ)` at dyadic
  level `L`, i.e. a bump of radius `2^{-L}` around the origin of `ℝ/ℤ` (which is `1` on the
  sub-arc of radius `2^{-L-1}`).

Everything about these objects (`bump_geometry`, `torsion_basic`, ...) is proved in the sibling
files of this directory.
-/
import Mathlib
import Submission.Work.BourgainPlan.Thm52.decimatedKernel_lp
import Submission.Work.KMTContract.Defs

set_option autoImplicit false

namespace Work.KMTPlan.A6.Decim

open Work.Analysis.IonescuWainger

noncomputable section

/-- The point `a / Q` of the circle `ℝ/ℤ` (the `AddCircle 1`-image of the real number `a/Q`). -/
def circPt (Q : ℕ) (a : ℤ) : Work.Analysis.IonescuWainger.Circle :=
  (((a : ℝ) / (Q : ℝ) : ℝ) : Work.Analysis.IonescuWainger.Circle)

/-- The `Q`-torsion points `{a/Q : a < Q}` of the circle `ℝ/ℤ`, as a `Finset`.  This is the coarse
arc set over which the KMSZ (6.22) weight factor is periodised. -/
def torsFinset (Q : ℕ) : Finset Work.Analysis.IonescuWainger.Circle :=
  (Finset.range Q).image (fun a : ℕ => circPt Q (a : ℤ))

/-- The dyadic circle bump at level `L`: the periodisation of the cut-off `η_{≤-L}`, i.e. the
symbol `ξ ↦ η (2^L ξ)` read on `ℝ/ℤ`.  It is supported in the arc of radius `2^{-L}` around `0`
and equal to `1` on the arc of radius `2^{-L-1}`. -/
def bump (L : ℕ) : Work.Analysis.IonescuWainger.Circle → ℂ := periodize (etaCut Work.KMTContract.kmtEta (-(L : ℤ)))

@[simp] lemma bump_apply (L : ℕ) (ξ : Work.Analysis.IonescuWainger.Circle) :
    bump L ξ = periodize (etaCut Work.KMTContract.kmtEta (-(L : ℤ))) ξ := rfl

/-! ## Elementary arithmetic of `2^{-L}` -/

/-- `2^{-L}` as an inverse power. -/
lemma two_zpow_neg_eq_inv (L : ℕ) : (2 : ℝ) ^ (-(L : ℤ)) = ((2 : ℝ) ^ L)⁻¹ := by
  rw [zpow_neg, zpow_natCast]

lemma two_zpow_neg_pos (L : ℕ) : (0 : ℝ) < (2 : ℝ) ^ (-(L : ℤ)) :=
  zpow_pos (by norm_num) _

/-- `2^{-L}` decreases in `L`. -/
lemma two_zpow_neg_antitone {L M : ℕ} (h : M ≤ L) :
    (2 : ℝ) ^ (-(L : ℤ)) ≤ (2 : ℝ) ^ (-(M : ℤ)) :=
  zpow_le_zpow_right₀ (by norm_num) (by omega)

/-- `2 · 2^{-M} = 2^{-M+1}`. -/
lemma two_mul_two_zpow_neg (M : ℕ) : 2 * (2 : ℝ) ^ (-(M : ℤ)) = (2 : ℝ) ^ (-(M : ℤ) + 1) := by
  rw [show (-(M : ℤ) + 1) = 1 + (-(M : ℤ)) by ring,
    zpow_add₀ (by norm_num : (2 : ℝ) ≠ 0), zpow_one]

/-- **The key numerical consequence of `Q² < 2^{M-1}`**: `2^{-M+1} Q < 1`. -/
lemma two_zpow_neg_add_one_mul_lt_one {M Q : ℕ}
    (h : (Q : ℝ) ^ 2 < (2 : ℝ) ^ ((M : ℤ) - 1)) :
    (2 : ℝ) ^ (-(M : ℤ) + 1) * (Q : ℝ) < 1 := by
  have hQ0 : (0 : ℝ) ≤ (Q : ℝ) := by positivity
  have hQ1 : (Q : ℝ) ≤ (Q : ℝ) ^ 2 := by
    rcases Nat.eq_zero_or_pos Q with h0 | hpos
    · simp [h0]
    · have h1 : (1 : ℝ) ≤ (Q : ℝ) := by exact_mod_cast hpos
      nlinarith
  have hpos : (0 : ℝ) < (2 : ℝ) ^ (-(M : ℤ) + 1) := zpow_pos (by norm_num) _
  calc (2 : ℝ) ^ (-(M : ℤ) + 1) * (Q : ℝ)
      ≤ (2 : ℝ) ^ (-(M : ℤ) + 1) * (Q : ℝ) ^ 2 := mul_le_mul_of_nonneg_left hQ1 hpos.le
    _ < (2 : ℝ) ^ (-(M : ℤ) + 1) * (2 : ℝ) ^ ((M : ℤ) - 1) :=
        mul_lt_mul_of_pos_left h hpos
    _ = (2 : ℝ) ^ ((-(M : ℤ) + 1) + ((M : ℤ) - 1)) :=
        (zpow_add₀ (by norm_num : (2 : ℝ) ≠ 0) (-(M : ℤ) + 1) ((M : ℤ) - 1)).symm
    _ = 1 := by
        rw [show (-(M : ℤ) + 1) + ((M : ℤ) - 1) = 0 from by ring, zpow_zero]

end

end Work.KMTPlan.A6.Decim
