import Mathlib
import Submission.Commons.RingTheory.Henselian.kummer_root_lift
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace Commons.RingTheory.Henselian

/-- **Lifting `n`-th roots of units through a Henselian local ring.**

If `n` is a unit of a Henselian local ring `R` (equivalently the residue
characteristic does not divide `n`) and the residue of a unit `u : Rˣ` is an
`n`-th power in the residue field, then `u` itself is an `n`-th power in `Rˣ`. -/
theorem units_mem_pow_of_residue_mem_pow {R : Type*} [CommRing R] [IsLocalRing R]
    [HenselianLocalRing R] (n : ℕ) [NeZero n] (hn : IsUnit (n : R)) (u : Rˣ)
    (h : Units.map (IsLocalRing.residue R).toMonoidHom u ∈ (powMonoidHom n).range) :
    u ∈ (powMonoidHom n).range := by
  rw [MonoidHom.mem_range] at h ⊢
  obtain ⟨w, hw⟩ := h
  -- Read off the equality in the residue field from the equality in the units.
  have hβ : (w : IsLocalRing.ResidueField R) ^ n = IsLocalRing.residue R (u : R) := by
    have hw' := congrArg (fun v : (IsLocalRing.ResidueField R)ˣ =>
      (v : IsLocalRing.ResidueField R)) hw
    simpa [powMonoidHom_apply, Units.coe_map] using hw'
  -- Lift the `n`-th root of the residue to a genuine `n`-th root.
  obtain ⟨b, hbpow, hbres⟩ :=
    kummer_root_lift n u.isUnit hn (w : IsLocalRing.ResidueField R) hβ
  -- `b` reduces to a unit, hence is itself a unit.
  have hbunit : IsUnit b := by
    rw [← IsLocalRing.residue_ne_zero_iff_isUnit]
    rw [hbres]
    exact w.ne_zero
  refine ⟨hbunit.unit, ?_⟩
  apply Units.ext
  rw [powMonoidHom_apply, Units.val_pow_eq_pow_val, IsUnit.unit_spec, hbpow]

end Commons.RingTheory.Henselian
