import Mathlib
import Submission.Work.Drive.CappingSpace
import Submission.Work.Drive.omegaChainInterface
import Submission.Work.Drive.capSection

/-!
# `orbitXH`: the rotation-invariant data of the capping space, and `CapInterior`

This file carries the **vocabulary** of the lead's CapSection plan
(`Submission/Work/Drive/NOTES_LEAD_capSection.md`, 2026-09-26 01:25), which replaced the (refuted)
cap-cone route:

* the rotation `Work.Drive.rotCapping` acts *freely* on `CappingSpace`, and the map

  > `orbitXH (r, d, eta) = (r d, -r^2 (1 - |d|^2))`    (configuration piece)
  > `orbitXH (r, theta, d) = (r d,  r^2 (1 - |d|^2))`  (cap piece)

  (the two formulas agree on the glued torus, where `|d| = 1`) is **rotation invariant** and its
  fibres are exactly the rotation orbits.  Hence `CapSection Q` follows from the injectivity of
  `orbitXH o Q` on the inner disk -- which is what the construction establishes;
* `CapInterior Q`: the *open* inner disk of the chart lands in the **interior** of the cap solid
  torus.  With `CapSection` this is exactly what the whole-plane disjointness consumes (the mixed
  strip/cap case: a strict cap-interior class is never a configuration class, and a seam point is a
  band point), cf. `Work.Drive.disjoint_chartDisk_rotCapping_of_capSection`.
-/

namespace Work.Drive

open Manifold
open scoped Manifold ContDiff Topology

attribute [local instance] Work.Drive.cappingCharted Work.Drive.isManifold_cappingCharted
  Work.Drive.t2Space_cappingSpace Work.Drive.projCharted

noncomputable section

/-- The formula of `orbitXH` on the disjoint union of the two pieces. -/
def orbitXHRaw (q : ConfigPiece ⊕ CapPiece) : ℂ × ℝ :=
  match q with
  | Sum.inl c => (((c.1.1 : ℝ) : ℂ) * c.1.2.1, - (c.1.1 ^ 2 * (1 - ‖c.1.2.1‖ ^ 2)))
  | Sum.inr c => (((c.1.1 : ℝ) : ℂ) * c.1.2.2, c.1.1 ^ 2 * (1 - ‖c.1.2.2‖ ^ 2))

/-- **The rotation-invariant data of a capping-space point.**  On the configuration piece
`(r, d, eta)` it is `(r*d, -r^2*(1-|d|^2))`, on the cap piece `(r, theta, d)` it is
`(r*d, r^2*(1-|d|^2))`; the two agree on the glued torus (`|d| = 1`, where both second coordinates
vanish), so the map descends to `CappingSpace`. -/
def orbitXH (p : CappingSpace) : ℂ × ℝ :=
  Quotient.lift (s := cappingSetoid) orbitXHRaw (by
    intro a b h
    change cappingRel a b at h
    rcases h with h | ⟨r, hr, θ, φ, h | h⟩
    · rw [h]
    · obtain ⟨ha, hb⟩ := h
      subst ha
      subst hb
      simp only [orbitXHRaw, confBdy_val, capBdy_val, norm_circleOf, one_pow, sub_self, mul_zero,
        neg_zero]
    · obtain ⟨hb, ha⟩ := h
      subst ha
      subst hb
      simp only [orbitXHRaw, confBdy_val, capBdy_val, norm_circleOf, one_pow, sub_self, mul_zero,
        neg_zero]) p

@[simp] lemma orbitXH_mk_inl (c : ConfigPiece) :
    orbitXH (Quotient.mk'' (Sum.inl c))
      = (((c.1.1 : ℝ) : ℂ) * c.1.2.1, - (c.1.1 ^ 2 * (1 - ‖c.1.2.1‖ ^ 2))) := by
  simp [orbitXH, orbitXHRaw]

@[simp] lemma orbitXH_mk_inr (c : CapPiece) :
    orbitXH (Quotient.mk'' (Sum.inr c))
      = (((c.1.1 : ℝ) : ℂ) * c.1.2.2, c.1.1 ^ 2 * (1 - ‖c.1.2.2‖ ^ 2)) := by
  simp [orbitXH, orbitXHRaw]

/-- **`orbitXH` is invariant under the rotation.** -/
theorem orbitXH_rotCapping (w : UnitAddCircle) (p : CappingSpace) :
    orbitXH (rotCapping w p) = orbitXH p := by
  induction p using Quotient.inductionOn with
  | h a => cases a <;> simp [rotConfig, rotCap]

/-- **The rotation acts freely**: a capping-space point fixed by `rotCapping w` forces `w = 0`. -/
theorem rotCapping_eq_self {w : UnitAddCircle} {p : CappingSpace} (h : rotCapping w p = p) :
    w = 0 := by
  induction p using Quotient.inductionOn with
  | h a =>
    cases a with
    | inl c =>
      have h1 : rotConfig w c = c := mk_inl_inj.mp h
      have h3 : c.1.2.2 + w = c.1.2.2 := congrArg (fun x : ConfigPiece => x.1.2.2) h1
      have h4 : c.1.2.2 + w = c.1.2.2 + 0 := by simpa using h3
      exact add_left_cancel h4
    | inr c =>
      have h1 : rotCap w c = c := cappingRel_inr_inr.mp (Quotient.exact h)
      have h3 : c.1.2.1 + w = c.1.2.1 := congrArg (fun x : CapPiece => x.1.2.1) h1
      have h4 : c.1.2.1 + w = c.1.2.1 + 0 := by simpa using h3
      exact add_left_cancel h4

/-- **`CapSection` from the injectivity of `orbitXH o Q` on the closed inner disk.** -/
theorem capSection_of_orbitXH {Q : ℂ → CappingSpace}
    (hinj : Set.InjOn (fun z : ℂ => orbitXH (Q z)) (Metric.closedBall (0 : ℂ) (1 / 2))) :
    CapSection Q := by
  intro z z' w hz hz' heq
  have hz1 : z ∈ Metric.closedBall (0 : ℂ) (1 / 2) := by
    simpa [Metric.mem_closedBall, dist_zero_right] using hz
  have hz2 : z' ∈ Metric.closedBall (0 : ℂ) (1 / 2) := by
    simpa [Metric.mem_closedBall, dist_zero_right] using hz'
  have h1 : orbitXH (Q z) = orbitXH (Q z') := by
    rw [heq, orbitXH_rotCapping]
  have h2 : z = z' := hinj hz1 hz2 h1
  rw [h2] at heq
  exact rotCapping_eq_self heq.symm

/-- **`CapInterior Q`**: the chart's *open* inner disk lands in the interior of the cap solid torus.
This is what the mixed strip/cap case of the whole-plane disjointness consumes (together with
`CapSection`), cf. `Work.Drive.disjoint_chartDisk_rotCapping_of_capSection`. -/
def CapInterior (Q : ℂ → CappingSpace) : Prop :=
  ∀ z : ℂ, ‖z‖ < 1 / 2 → ∀ c : CapPiece,
    Q z = Quotient.mk'' (Sum.inr c) → ‖c.1.2.2‖ < 1

end

end Work.Drive
