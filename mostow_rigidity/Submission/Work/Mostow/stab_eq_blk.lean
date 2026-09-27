import Mathlib
import Submission.Mostow.GapADefs
import Submission.Work.Mostow.cosh_hdist_fermi
import Submission.Work.Mostow.fermi_inv
import Submission.Work.Mostow.blk_smul_fermi
import Submission.Work.Mostow.blkMap_linBlk
import Submission.Work.Mostow.hdist_linBlk
import Submission.Work.Mostow.hdist_coordEmb
import Submission.Work.Mostow.stab_fermi_foot
import Submission.Work.Mostow.stab_fermi_normal_indep
import Submission.Work.Mostow.stab_normal_inner
import Submission.Work.Mostow.linear_isometry_of_inner
import Submission.Work.Mostow.exists_foot_map

/-! Guidance from the project lead (the requester):

# Block decomposition of the stratum stabiliser (lead's design; F5/F6 of NOTES_LEAD_strata_KM.md)
# blk k m h R is choice-defined; its meaning is Work.Mostow.blk_smul_fermi (PROVED):
#   blk k m h R • fermi k m v w = fermi k m (h • v) (R w).
# stab_eq_blk: given `g ∈ SetStabStd k m`,
#   (1) `v ↦ tanC-part of g • coordEmb k m v` is an hdist-isometry of `E k` (coordEmb is an
#       isometric embedding: `cosh_hdist_fermi` with `w = w' = 0`, and `fermi v 0 = coordEmb v`),
#       so it is `v ↦ h • v` for some `h` (clause 8 of `HypIsometryProp k`) — this is
#       `Work.Mostow.exists_foot_map`.
#   (2) `g' := (blk k m h 1)⁻¹ * g` fixes `stdTG k m` pointwise.
#   (3) `g'` acts in Fermi coordinates by the identity on the foot (`Work.Mostow.stab_fermi_foot`),
#       the normal part being independent of the foot (`Work.Mostow.stab_fermi_normal_indep`), so
#       it is given by a single `R : E m → E m` on the normal fibre; `R` preserves the Euclidean
#       inner product and is surjective (`Work.Mostow.stab_normal_inner`), hence is a linear
#       isometry equivalence (`Work.Mostow.linear_isometry_of_inner`), and `g' = blk k m 1 R` by
#       faithfulness (`POActionProp` clause 6).
#   (4) Hence `g = blk k m h 1 * blk k m 1 R = blk k m h R`, so `∃ p, g = blk p.1 p.2`, and
#       `resStd`/`nrmStd` unfold (`dite_pos` on a chosen witness) to give
#       `g = blk (resStd g) (nrmStd g)`.
# Never use `λ` as a variable name.
-/

namespace Work.Mostow

open Submission.Mostow LeanEval.Geometry.MostowRigidity MeasureTheory

/-! ### Elementary consequences of the action axioms -/

section Helpers

variable {n : ℕ}

private lemma po_smul_one (hA : POActionProp n) (u : E n) : (1 : PO n 1) • u = u := hA.2.2.2.1 u

private lemma po_smul_mul (hA : POActionProp n) (g h : PO n 1) (u : E n) :
    (g * h) • u = g • (h • u) := hA.2.2.2.2.1 g h u

private lemma po_inv_smul_smul (hA : POActionProp n) (g : PO n 1) (u : E n) : g⁻¹ • (g • u) = u := by
  rw [← po_smul_mul hA g⁻¹ g u, inv_mul_cancel, po_smul_one hA]

/-- Faithfulness (clause 6 of `POActionProp`): an element acting trivially is trivial. -/
private lemma po_eq_of_smul_eq (hA : POActionProp n) {g h : PO n 1}
    (H : ∀ u : E n, g • u = h • u) : g = h := by
  have h1 : g⁻¹ * h = 1 := hA.2.2.2.2.2.1 (g⁻¹ * h) (fun u => by
    rw [po_smul_mul hA, ← H u, po_inv_smul_smul hA])
  have h2 : g * (g⁻¹ * h) = g * 1 := by rw [h1]
  rw [← mul_assoc, mul_inv_cancel, one_mul, mul_one] at h2
  exact h2.symm

end Helpers

/-- `coordEmb k m v` is the Fermi point with foot `v` and zero normal coordinate. -/
private lemma fermi_zero_coordEmb (k m : ℕ) (v : E k) : fermi k m v 0 = coordEmb k m v := by
  simp [fermi, coordEmb]

/-- The block element acts on the stratum by `h`. -/
private lemma blk_smul_coordEmb (k m : ℕ) (hAk : POActionProp k) (hIk : HypIsometryProp k)
    (hA : POActionProp (k + m)) (hI : HypIsometryProp (k + m))
    (h : PO k 1) (R : E m ≃ₗᵢ[ℝ] E m) (v : E k) :
    blk k m h R • coordEmb k m v = coordEmb k m (h • v) := by
  rw [← fermi_zero_coordEmb k m v, blk_smul_fermi k m hAk hIk hA hI h R v 0, map_zero,
    fermi_zero_coordEmb k m (h • v)]

/-! ### The block decomposition of the stratum stabiliser -/

theorem stab_eq_blk (k m : ℕ) (hAk : POActionProp k) (hIk : HypIsometryProp k)
    (hA : POActionProp (k + m)) (hI : HypIsometryProp (k + m)) :
    ∀ g : PO (k + m) 1, g ∈ SetStabStd k m → g = blk k m (resStd k m g) (nrmStd k m g) := by
  intro g hg
  obtain ⟨h, hh⟩ := exists_foot_map k m hAk hIk hA hI g hg
  set g' : PO (k + m) 1 := (blk k m h 1)⁻¹ * g with hg'def
  -- `g'` fixes the standard stratum pointwise
  have hg'pt : ∀ v : E k, g' • coordEmb k m v = coordEmb k m v := by
    intro v
    have hb : blk k m h 1 • coordEmb k m v = coordEmb k m (h • v) :=
      blk_smul_coordEmb k m hAk hIk hA hI h 1 v
    rw [hg'def, po_smul_mul hA, hh v, ← hb, po_inv_smul_smul hA]
  -- structure of the action of `g'` in Fermi coordinates
  have hfoot : ∀ (v : E k) (w : E m),
      (fermiInv k m (g' • fermi k m v w)).1 = v ∧
        ‖(fermiInv k m (g' • fermi k m v w)).2‖ = ‖w‖ :=
    fun v w => stab_fermi_foot k m hA hI g' hg'pt v w
  have hindep : ∀ (v : E k) (w : E m),
      (fermiInv k m (g' • fermi k m v w)).2 = (fermiInv k m (g' • fermi k m 0 w)).2 :=
    fun v w => stab_fermi_normal_indep k m hA hI g' hg'pt v w
  have hform : ∀ (v : E k) (w : E m),
      g' • fermi k m v w = fermi k m v ((fermiInv k m (g' • fermi k m 0 w)).2) := by
    intro v w
    rw [← (fermi_inv k m).2.1 (g' • fermi k m v w), (hfoot v w).1, hindep v w]
  obtain ⟨hinner, hsurj⟩ := stab_normal_inner k m hA hI g' hg'pt
  obtain ⟨R, hR⟩ := linear_isometry_of_inner m
    (fun w : E m => (fermiInv k m (g' • fermi k m 0 w)).2) hinner hsurj
  -- `g'` is the pure normal block
  have hg'blk : g' = blk k m 1 R := by
    apply po_eq_of_smul_eq hA
    intro u
    rw [← (fermi_inv k m).2.1 u, hform (fermiInv k m u).1 (fermiInv k m u).2,
      ← hR ((fermiInv k m u).2),
      blk_smul_fermi k m hAk hIk hA hI 1 R (fermiInv k m u).1 (fermiInv k m u).2,
      po_smul_one hAk]
  -- `g` is the block `h, R`
  have hgr : g = blk k m h R := by
    have h1 : g = blk k m h 1 * g' := by
      rw [hg'def]
      group
    rw [h1, hg'blk]
    apply po_eq_of_smul_eq hA
    intro u
    rw [po_smul_mul hA, ← (fermi_inv k m).2.1 u,
      blk_smul_fermi k m hAk hIk hA hI 1 R (fermiInv k m u).1 (fermiInv k m u).2,
      po_smul_one hAk,
      blk_smul_fermi k m hAk hIk hA hI h (1 : E m ≃ₗᵢ[ℝ] E m)
        (fermiInv k m u).1 (R (fermiInv k m u).2),
      blk_smul_fermi k m hAk hIk hA hI h R (fermiInv k m u).1 (fermiInv k m u).2]
    simp only [LinearIsometryEquiv.coe_one, id_eq]
  -- finish: `resStd`/`nrmStd` return a witness of the block decomposition
  have hex : ∃ p : PO k 1 × (E m ≃ₗᵢ[ℝ] E m), g = blk k m p.1 p.2 := ⟨(h, R), hgr⟩
  have hres : resStd k m g = hex.choose.1 := by
    unfold resStd
    exact dite_eq_left hex
  have hnrm : nrmStd k m g = hex.choose.2 := by
    unfold nrmStd
    exact dite_eq_left hex
  rw [hres, hnrm]
  exact hex.choose_spec

end Work.Mostow
