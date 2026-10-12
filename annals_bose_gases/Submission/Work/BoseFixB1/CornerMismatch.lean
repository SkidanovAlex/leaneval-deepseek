import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.Analysis.Calculus.BumpFunction.FiniteDimension
import Submission.Work.UBBInputs8.Defs
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Work.BoseFixB1.CornerMismatch` — the corner-box cutoff mismatch

**Why this file exists.**  The target `Work.BoseFixB1.fibreLossPaidThick` couples two
*different* cutoffs at the sliding box `B(u) = dlBox ℓ d u`:

* the localised fibre loss (`Work.BoseFixB1S.fibLoss`, `Work.BoseFixB1.chiBCount`) is weighted
  by `chiSmallB M ℓ d u = chiScale ℓ · chiSmall M ((ℓd)⁻¹ • · − u)` — the *ball* factor
  `χ(·/ℓ)` times the explicit *cosine* factor;
* the spectral kinetic slot (`Work.UBBInputs8.tBwordKinInd`) is windowed by
  `chiB ℓ d u = chiScale ℓ · chiScale (ℓd) (· − (ℓd) • u)` — the *ball* factor times a
  *second ball* factor.

The two windows do **not** have the same support.  `supp (chiB ℓ d u) =
ball (0, ℓ/2) ∩ ball ((ℓd)•u, ℓd/2)` while `supp (chiSmallB ℓ d u) =
ball (0, ℓ/2) ∩ ((ℓd)•u + acube (ℓd))`.  So whenever the two *balls* are disjoint
(`‖(ℓd)•u‖ ≥ ℓ/2 + ℓd/2`) — which is compatible with the sliding box `dlBox ℓ d u` being
non-empty (it is then a corner piece of the small cube, of side `ℓd`) — one has

    chiB ℓ d u ≡ 0   while   chiSmallB ℓ d u ≢ 0  on  B(u) ∩ ball (0, ℓ/2) .

Since `tBamp χ p Ψ i x = ∫_z (χ z : ℂ) e^{−i⟪p,z⟫} (Ψ (x_{i←z}) : ℂ) dz` has the window `χ` as
a *factor*, the kinetic slot of the target vanishes **identically** on such boxes,
for every state and every sliding parameter, while the fibre loss does not.

This file machine-checks the structural half of that statement:

* the corpus bump `χ` is non-zero exactly inside the open ball of radius `1/2`
  (`chi_ne_zero_iff_norm_lt_half`), hence `chiScale s ·` is non-zero exactly inside the ball of
  radius `s/2` (`chiScale_ne_zero_iff`);
* on the corner configuration `chiB ℓ d u ≡ 0` (`chiB_eq_zero_of_ball_disjoint`);
* hence the target's kinetic slot vanishes *identically* there
  (`tBwordKinInd_eq_zero_of_window`), for all states, windows of length `c` and symbols `F`.

**Is this a defect of the target?  No** — see
`Submission/Work/BoseFixB1/FINDING_fibreLossPaidThick_analysis.md` §2: the corner configurations
are *payable* by the target's own `K`-slot and allowance, because the corpus bump is flat at its
own support boundary in the provable form `chi z ≤ C_N (1/2 − ‖z‖)^N`
(`Submission/Work/BoseFixB1/chi_boundary_taylor`, delegated), while the `d`-dependence of the
remaining quantities is only polynomial (`V ≍ d^{−471/323}`, `μ ≍ d^{53.83}`).  What the mismatch
does show is that any proof (or restatement) of the target must handle the corner configurations
explicitly: they are inside FS's `goodSet`, and they are not the corpus's empty/far boxes.
-/

noncomputable section

open MeasureTheory Metric Filter
open scoped Real Topology BigOperators ENNReal

namespace Work.BoseFixB1

local notation "ℝ³" => EuclideanSpace ℝ (Fin 3)

open Submission.BoseGases

/-! ## 1.  The support of the corpus bump -/

/-- **The corpus bump is non-zero exactly inside the open ball of radius `1/2`.**  This is the
`support` field of `ContDiffBumpBase`, transported through `chiBase x = base 2 (4 • x)`. -/
lemma chiBase_ne_zero_iff_norm_lt_half (x : ℝ³) : chiBase x ≠ 0 ↔ ‖x‖ < 1 / 2 := by
  have hbase : chiBase x = (someContDiffBumpBase ℝ³).toFun 2 ((4 : ℝ) • x) := by
    rw [chiBase, ContDiffBump.apply]
    norm_num [chiBump]
  have hsupp := (someContDiffBumpBase ℝ³).support 2 (by norm_num : (1 : ℝ) < 2)
  rw [hbase, ← Function.mem_support, hsupp, Metric.mem_ball, dist_zero_right,
    norm_smul, Real.norm_ofNat]
  constructor <;> intro h <;> linarith

/-- **The corpus bump `chi` is non-zero exactly inside the open ball of radius `1/2`.** -/
lemma chi_ne_zero_iff_norm_lt_half (x : ℝ³) : chi x ≠ 0 ↔ ‖x‖ < 1 / 2 := by
  rw [chi, div_ne_zero_iff]
  constructor
  · rintro ⟨h1, _⟩
    exact (chiBase_ne_zero_iff_norm_lt_half x).1 h1
  · intro hx
    exact ⟨(chiBase_ne_zero_iff_norm_lt_half x).2 hx, chi_sqrt_ne_zero⟩

/-- `chiScale s ·` is non-zero exactly inside the open ball of radius `s/2`
(for `0 < s`). -/
lemma chiScale_ne_zero_iff {s : ℝ} (hs : 0 < s) (x : ℝ³) :
    chiScale s x ≠ 0 ↔ ‖x‖ < s / 2 := by
  have hiff : s⁻¹ * ‖x‖ < 1 / 2 ↔ ‖x‖ < s / 2 := by
    constructor
    · intro h
      have h2 : s * (s⁻¹ * ‖x‖) < s * (1 / 2) := mul_lt_mul_of_pos_left h hs
      have h3 : s * (s⁻¹ * ‖x‖) = ‖x‖ := by
        rw [← mul_assoc, mul_inv_cancel₀ (ne_of_gt hs), one_mul]
      rw [h3] at h2
      linarith
    · intro h
      have h2 : s⁻¹ * ‖x‖ < s⁻¹ * (s / 2) := mul_lt_mul_of_pos_left h (inv_pos.mpr hs)
      have h3 : s⁻¹ * (s / 2) = 1 / 2 := by
        rw [show s⁻¹ * (s / 2) = (s * s⁻¹) / 2 by ring, mul_inv_cancel₀ (ne_of_gt hs),
          one_div]
      linarith
  rw [chiScale, chi_ne_zero_iff_norm_lt_half, norm_smul, Real.norm_eq_abs,
    abs_of_pos (inv_pos.mpr hs)]
  exact hiff

/-- `chiScale s ·` vanishes outside the closed ball of radius `s/2`. -/
lemma chiScale_eq_zero_of_half_le_norm {s : ℝ} (hs : 0 < s) {x : ℝ³}
    (hx : s / 2 ≤ ‖x‖) : chiScale s x = 0 := by
  by_contra h
  exact absurd ((chiScale_ne_zero_iff hs x).1 h) (not_lt.mpr hx)

/-- **The corner configuration kills the window**: if the two ball-factors of `chiB ℓ d u` have
disjoint supports (`‖(ℓd) • u‖ ≥ ℓ/2 + ℓd/2`), then `chiB ℓ d u` vanishes identically. -/
lemma chiB_eq_zero_of_ball_disjoint {ℓ d : ℝ} (hℓ : 0 < ℓ) (hd : 0 < d) {u : ℝ³}
    (h : ℓ / 2 + ℓ * d / 2 ≤ ‖(ℓ * d) • u‖) (x : ℝ³) : chiB ℓ d u x = 0 := by
  rw [chiB]
  by_contra hne
  have h1 : chiScale ℓ x ≠ 0 := fun h1 => hne (by rw [h1, zero_mul])
  have h2 : chiScale (ℓ * d) (x - (ℓ * d) • u) ≠ 0 := fun h2 => hne (by rw [h2, mul_zero])
  have hx1 : ‖x‖ < ℓ / 2 := (chiScale_ne_zero_iff hℓ x).1 h1
  have hx2 : ‖x - (ℓ * d) • u‖ < ℓ * d / 2 := (chiScale_ne_zero_iff (mul_pos hℓ hd) _).1 h2
  have hkey : ‖(ℓ * d) • u‖ < ℓ / 2 + ℓ * d / 2 := by
    have h₁ : (ℓ * d) • u = x - (x - (ℓ * d) • u) :=
      (sub_sub_cancel x ((ℓ * d) • u)).symm
    calc ‖(ℓ * d) • u‖ = ‖x - (x - (ℓ * d) • u)‖ := congrArg Norm.norm h₁
      _ ≤ ‖x‖ + ‖x - (ℓ * d) • u‖ := norm_sub_le x _
      _ < ℓ / 2 + ℓ * d / 2 := add_lt_add hx1 hx2
  linarith

/-! ## 2.  The kinetic slot dies with the window -/

/-- `tBamp` carries the window as a factor, so a vanishing window gives a vanishing amplitude. -/
lemma tBamp_eq_zero_of_window {χ : ℝ³ → ℝ} (hχ : ∀ z : ℝ³, χ z = 0) (p : ℝ³) {N : ℕ}
    (Ψ : Submission.BoseGases.X N → ℝ) (i : Fin N) (x : Submission.BoseGases.X N) :
    Work.SmallBoxTBWord.tBamp χ p Ψ i x = 0 := by
  simp only [Work.SmallBoxTBWord.tBamp]
  refine integral_eq_zero_of_ae ?_
  filter_upwards with z
  simp [hχ z]

/-- The `p`-diagonal kinetic form vanishes when the window vanishes. -/
lemma tBdiagFormInd_eq_zero_of_window {χ : ℝ³ → ℝ} (hχ : ∀ z : ℝ³, χ z = 0)
    (a : ℝ) (A : Set ℝ³) (volA : ℝ) (F : ℝ → ℝ) {N : ℕ} (Ψ : Submission.BoseGases.X N → ℝ) :
    Work.UBBInputs8.tBdiagFormInd a A volA χ F Ψ = 0 := by
  simp only [Work.UBBInputs8.tBdiagFormInd]
  refine Finset.sum_eq_zero fun i _ => ?_
  have hinner : ∀ p : ℝ³, (∫ x in Submission.BoseGases.abox N a,
      ‖Work.SmallBoxTBWord.tBamp χ p (Work.UBBInputs8.boxQInd volA A i Ψ) i x‖ ^ 2) = 0 := by
    intro p
    refine integral_eq_zero_of_ae ?_
    filter_upwards with x
    rw [tBamp_eq_zero_of_window hχ]
    simp
  have hzero : (∫ p : ℝ³, F ‖p‖ *
      ((a ^ 3)⁻¹ * ∫ x in Submission.BoseGases.abox N a,
        ‖Work.SmallBoxTBWord.tBamp χ p (Work.UBBInputs8.boxQInd volA A i Ψ) i x‖ ^ 2)) = 0 := by
    simp only [hinner]
    simp
  rw [hzero, mul_zero]

/-- **The target's spectral kinetic slot vanishes identically on the corner configurations.** -/
lemma tBwordKinInd_eq_zero_of_window {χ : ℝ³ → ℝ} (hχ : ∀ z : ℝ³, χ z = 0)
    (a : ℝ) (A : Set ℝ³) (volA : ℝ) (c : ℝ) {N : ℕ} (Ψ : Submission.BoseGases.X N → ℝ) :
    Work.UBBInputs8.tBwordKinInd a A volA χ c Ψ = 0 :=
  tBdiagFormInd_eq_zero_of_window hχ a A volA _ Ψ

/-- The target's kinetic slot on the corner configuration (all four parameters instantiated
at the sliding box). -/
lemma corner_tBwordKinInd_eq_zero {ℓ d : ℝ} (hℓ : 0 < ℓ) (hd : 0 < d) {u : ℝ³}
    (h : ℓ / 2 + ℓ * d / 2 ≤ ‖(ℓ * d) • u‖) (c : ℝ) {N : ℕ}
    (Ψ : Submission.BoseGases.X N → ℝ) :
    Work.UBBInputs8.tBwordKinInd ℓ (Submission.BoseGases.dlBox ℓ d u)
      (Work.SmallBoxSliding.boxMass ℓ d u) (chiB ℓ d u) c Ψ = 0 :=
  tBwordKinInd_eq_zero_of_window (fun z => chiB_eq_zero_of_ball_disjoint hℓ hd h z) _ _ _ _ _

end Work.BoseFixB1
