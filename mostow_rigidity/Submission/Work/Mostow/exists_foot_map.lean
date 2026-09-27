import Mathlib
import Submission.Work.Mostow.cosh_hdist_fermi
import Submission.Work.Mostow.fermi_inv

namespace Work.Mostow

open Submission.Mostow LeanEval.Geometry.MostowRigidity

/-! An element `g` of `PO (k+m) 1` which preserves the standard stratum
`stdTG k m = range (coordEmb k m)` setwise induces a hyperbolic isometry `h` of `E k` on the foot:
`g • coordEmb k m v = coordEmb k m (h • v)`.

Guidance.  `hg : g ∈ SetStabStd k m` is `∀ u, u ∈ stdTG k m ↔ g • u ∈ stdTG k m`; since
`stdTG k m = Set.range (coordEmb k m)` and `coordEmb k m v ∈ stdTG k m`, each `g • coordEmb k m v`
equals `coordEmb k m v'` for some `v'` (use `Classical.choose` of that existence).
Then the chosen map `φ` is an `hdist`-isometry:
`hdist (φ a) (φ b) = hdist (coordEmb k m (φ a)) (coordEmb k m (φ b))` by
`Work.Mostow.hdist_coordEmb` (prove it privately if needed — zero padding preserves norm and inner
product), `= hdist (g • coordEmb k m a) (g • coordEmb k m b)` by the choice property,
`= hdist (coordEmb k m a) (coordEmb k m b)` by the isometry clause of `HypIsometryProp (k + m)`,
`= hdist a b` again by `hdist_coordEmb`.
Clause 8 of `HypIsometryProp k` then gives `h : PO k 1` with `φ v = h • v`; combine with the choice
property to conclude `g • coordEmb k m v = coordEmb k m (h • v)`. -/

/-! ### The zero padding `coordEmb` is an `hdist`-isometry

`coordEmb k m v` is the Fermi point with foot `v` and zero normal vector, so this is a computation
with the explicit Fermi formulas (`fermi_inv`/`cosh_hdist_fermi`). -/

/-- `coordEmb k m v` is the Fermi point with foot `v` and zero normal coordinate. -/
private lemma fermi_zero_eq_coordEmb (k m : ℕ) (v : E k) :
    fermi k m v 0 = coordEmb k m v := by
  ext j
  simp only [fermi, coordEmb, WithLp.ofLp_toLp]
  refine Fin.addCases (fun i => ?_) (fun i => ?_) j <;> simp [sinhc]

/-- `coordEmb` preserves the time coordinate. -/
private lemma tpart_coordEmb (k m : ℕ) (v : E k) :
    tpart (coordEmb k m v) = tpart v := by
  rw [← fermi_zero_eq_coordEmb k m v, tpart_fermi]
  simp

/-- `coordEmb` preserves the Euclidean inner product. -/
private lemma inner_coordEmb (k m : ℕ) (a b : E k) :
    inner ℝ (coordEmb k m a) (coordEmb k m b) = inner ℝ a b := by
  rw [← fermi_zero_eq_coordEmb k m a, ← fermi_zero_eq_coordEmb k m b, inner_fermi]
  simp [sinhc]

/-- `coordEmb k m` is an isometry for `hdist`. -/
private lemma hdist_coordEmb (k m : ℕ) (a b : E k) :
    hdist (coordEmb k m a) (coordEmb k m b) = hdist a b := by
  rw [hdist, hdist, tpart_coordEmb, tpart_coordEmb, inner_coordEmb]

theorem exists_foot_map (k m : ℕ) (hAk : Submission.Mostow.POActionProp k)
    (hIk : Submission.Mostow.HypIsometryProp k) (hA : Submission.Mostow.POActionProp (k + m))
    (hI : Submission.Mostow.HypIsometryProp (k + m))
    (g : LeanEval.Geometry.MostowRigidity.PO (k + m) 1) (hg : g ∈ Submission.Mostow.SetStabStd k m) :
    ∃ h : LeanEval.Geometry.MostowRigidity.PO k 1,
      ∀ v : Submission.Mostow.E k,
        g • Submission.Mostow.coordEmb k m v = Submission.Mostow.coordEmb k m (h • v) := by
  classical
  -- each `g • coordEmb k m v` lies in the stratum, so it is `coordEmb k m (φ v)` for a
  -- (classically) chosen `φ v`.
  have hstep : ∀ v : E k, ∃ w : E k, coordEmb k m w = g • coordEmb k m v := by
    intro v
    have h1 : coordEmb k m v ∈ stdTG k m := Set.mem_range_self v
    have h2 : g • coordEmb k m v ∈ stdTG k m := (hg (coordEmb k m v)).mp h1
    exact Set.mem_range.mp h2
  let φ : E k → E k := fun v => Classical.choose (hstep v)
  have hφ : ∀ v, coordEmb k m (φ v) = g • coordEmb k m v :=
    fun v => Classical.choose_spec (hstep v)
  -- `φ` is an isometry of `E k`.
  have hiso : ∀ a b, hdist (φ a) (φ b) = hdist a b := by
    intro a b
    rw [(hdist_coordEmb k m (φ a) (φ b)).symm, hφ a, hφ b,
        hI.2.2.2.2.2.2.1 g (coordEmb k m a) (coordEmb k m b), hdist_coordEmb k m a b]
  -- clause 8 of `HypIsometryProp k` realises `φ` as the action of an element `h : PO k 1`.
  obtain ⟨h, hh⟩ := hIk.2.2.2.2.2.2.2.1 φ hiso
  exact ⟨h, fun v => by rw [← hφ v, hh v]⟩

end Work.Mostow
