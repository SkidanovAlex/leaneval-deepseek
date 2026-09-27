import Mathlib
import Submission.Work.Mostow.stab_eq_blk

namespace Work.Mostow

open Submission.Mostow LeanEval.Geometry.MostowRigidity

/-! ### Local ingredients (no import of `tubeIneq`, which sits above this file in the
dependency graph because `count_hits` builds on `centralizer_acts_fermi`). -/

/-- `fermi j m v 0 = coordEmb j m v`: the stratum is the zero normal vector. -/
private lemma caf_fermi_zero (j m : ℕ) (v : E j) : fermi j m v 0 = coordEmb j m v := by
  simp [fermi, coordEmb]

/-- The fixed set of the pure block `blk j m 1 R`, with `R` having trivial fixed space, is
exactly the standard stratum `stdTG j m`. -/
private lemma caf_fixSet_blk (j m : ℕ) (hAj : POActionProp j) (hIj : HypIsometryProp j)
    (hA : POActionProp (j + m)) (hI : HypIsometryProp (j + m))
    (R : E m ≃ₗᵢ[ℝ] E m) (hR : ∀ w : E m, R w = w → w = 0) :
    fixSet (blk j m 1 R) = stdTG j m := by
  ext u
  constructor
  · intro hu
    obtain ⟨v, w, rfl⟩ : ∃ v w, u = fermi j m v w := ⟨_, _, ((fermi_inv j m).2.1 u).symm⟩
    change (blk j m 1 R) • fermi j m v w = fermi j m v w at hu
    rw [blk_smul_fermi j m hAj hIj hA hI 1 R v w, hAj.2.2.2.1 v] at hu
    have h3 := congrArg (fermiInv j m) hu
    rw [(fermi_inv j m).1 v (R w), (fermi_inv j m).1 v w] at h3
    have h2 : R w = w := (Prod.ext_iff.mp h3).2
    have hw : w = 0 := hR w h2
    subst hw
    exact ⟨v, (caf_fermi_zero j m v).symm⟩
  · rintro ⟨v, rfl⟩
    change (blk j m 1 R) • coordEmb j m v = coordEmb j m v
    rw [← caf_fermi_zero j m v]
    rw [blk_smul_fermi j m hAj hIj hA hI 1 R v 0, hAj.2.2.2.1 v, R.map_zero]

/-- An isometry `c` commuting with `b := blk j m 1 R` preserves the fixed stratum `stdTG j m`. -/
private lemma caf_centralizer_mem_SetStabStd (j m : ℕ) (hAj : POActionProp j)
    (hIj : HypIsometryProp j) (hA : POActionProp (j + m)) (hI : HypIsometryProp (j + m))
    (R : E m ≃ₗᵢ[ℝ] E m) (hR : ∀ w : E m, R w = w → w = 0) (c : PO (j + m) 1)
    (hc : c ∈ Subgroup.centralizer ({blk j m 1 R} : Set (PO (j + m) 1))) :
    c ∈ SetStabStd j m := by
  set b : PO (j + m) 1 := blk j m 1 R with hb
  have hmul : ∀ (g h : PO (j + m) 1) (u : E (j + m)), (g * h) • u = g • (h • u) :=
    hA.2.2.2.2.1
  have hcomm : b * c = c * b := by
    have h := (Subgroup.mem_centralizer_iff.mp hc) (blk j m 1 R) (Set.mem_singleton _)
    rw [← hb] at h
    exact h
  have hcomm' : b * c⁻¹ = c⁻¹ * b := by
    have h2 : c⁻¹ * (b * c) * c⁻¹ = c⁻¹ * (c * b) * c⁻¹ := by rw [hcomm]
    have hl : c⁻¹ * (b * c) * c⁻¹ = c⁻¹ * b := by group
    have hr : c⁻¹ * (c * b) * c⁻¹ = b * c⁻¹ := by group
    rw [hl, hr] at h2
    exact h2.symm
  have key : ∀ x : E (j + m), b • (c • x) = c • (b • x) := by
    intro x
    calc b • (c • x) = (b * c) • x := (hmul b c x).symm
      _ = (c * b) • x := by rw [hcomm]
      _ = c • (b • x) := hmul c b x
  have key2 : ∀ x : E (j + m), b • (c⁻¹ • x) = c⁻¹ • (b • x) := by
    intro x
    calc b • (c⁻¹ • x) = (b * c⁻¹) • x := (hmul b c⁻¹ x).symm
      _ = (c⁻¹ * b) • x := by rw [hcomm']
      _ = c⁻¹ • (b • x) := hmul c⁻¹ b x
  have hcc : ∀ u : E (j + m), c⁻¹ • (c • u) = u := by
    intro u
    calc c⁻¹ • (c • u) = (c⁻¹ * c) • u := (hmul c⁻¹ c u).symm
      _ = (1 : PO (j + m) 1) • u := by rw [inv_mul_cancel]
      _ = u := hA.2.2.2.1 u
  have hfix1 : ∀ u : E (j + m), u ∈ fixSet b → c • u ∈ fixSet b := by
    intro u hu
    change b • (c • u) = c • u
    rw [key u, hu]
  have hfix2 : ∀ u : E (j + m), c • u ∈ fixSet b → u ∈ fixSet b := by
    intro u hu
    change b • u = u
    have hu' : b • (c • u) = c • u := hu
    have h2 : c⁻¹ • (b • (c • u)) = c⁻¹ • (c • u) := by rw [hu']
    rw [← key2 (c • u), hcc] at h2
    exact h2
  have hstd : stdTG j m = fixSet b := by
    rw [hb, ← caf_fixSet_blk j m hAj hIj hA hI R hR]
  rw [SetStabStd]
  intro u
  rw [hstd]
  exact ⟨hfix1 u, hfix2 u⟩

/-- A centraliser element `k` of `blk j m 1 R` (with `R` having zero fixed space) preserves every
Fermi coordinate separately: the stratum stabiliser of `stdTG j m` acts blockwise on the foot and
on the normal vector. -/
theorem centralizer_acts_fermi (j m : ℕ) (hAj : Submission.Mostow.POActionProp j) (hIj : Submission.Mostow.HypIsometryProp j)
    (hA : Submission.Mostow.POActionProp (j + m)) (hI : Submission.Mostow.HypIsometryProp (j + m))
    (R : Submission.Mostow.E m ≃ₗᵢ[ℝ] Submission.Mostow.E m) (hR : ∀ w : Submission.Mostow.E m, R w = w → w = 0)
    (k : LeanEval.Geometry.MostowRigidity.PO (j + m) 1)
    (hk : k ∈ Subgroup.centralizer ({Submission.Mostow.blk j m 1 R} : Set (LeanEval.Geometry.MostowRigidity.PO (j + m) 1)))
    (v : Submission.Mostow.E j) (w : Submission.Mostow.E m) :
    k • Submission.Mostow.fermi j m v w =
      Submission.Mostow.fermi j m (Submission.Mostow.resStd j m k • v) (Submission.Mostow.nrmStd j m k w) := by
  have hc : k ∈ SetStabStd j m := caf_centralizer_mem_SetStabStd j m hAj hIj hA hI R hR k hk
  conv_lhs => rw [stab_eq_blk j m hAj hIj hA hI k hc]
  rw [blk_smul_fermi j m hAj hIj hA hI (resStd j m k) (nrmStd j m k) v w]

end Work.Mostow
