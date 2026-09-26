import Mathlib
import Submission.Work.Drive.Final.dentOut_hgen
import Submission.Work.Drive.Final.AnyEventDefs
import Submission.Work.Drive.Mono.SweepGeom3
import Submission.Work.Drive.Mono.hdir_of_htrans

/-!
# L6b at an event, consumed through the trace of the deformed level

`Work.Drive.Final.dentOut_hgen_geometric` reduces the union-form genericity at the level `lam*` of a
dent to two alternatives for a point `z` of the surface in the closed box and the closed slab at the
level: either `z ∈ closure Ω₁` already, or `z` lies on the box sphere (`boxNorm c σ z = s`).

`Work.Drive.Final.dentOut_hgen` disposes of the second alternative by *assuming* a family of curves
covering the whole box sphere.  The present module instead consumes the family carried by the trace
of the **deformed** level,

  `carrier ∩ frontier (D.deform ⁻¹' tiltedLevelRemoved s c σ u v h ℓ (ℓ D.centre))`,

which is the family `DentOutResolved` already produces.  The only new input is therefore the
membership of the box-sphere level points in that frontier:

* the dent never lowers the level functional (`dent_deform_wall_le`) and preserves the open box
  (`dent_deform_mem_PBox`); hence every point of the open box with level `≥ lam*` is mapped into the
  removed set (`dent_deform_mem_tiltedLevelRemoved`);
* at a point of the box sphere in the closed slab the box-norm functional and the sweep height have
  independent non-vanishing differentials (`GammaTransverse`, a clause of `GoodSweepData3`), so
  `Work.Drive.Mono.hdir_of_htrans` produces, arbitrarily close to `z`, points of the *open* box whose
  level is at least `lam*`.  These are pulled into the removed set by the previous bullet, so
  `z ∈ closure (D.deform ⁻¹' tiltedLevelRemoved …)`;
* `z` is not in the interior of that preimage: were it so, `z` would lie in `Ω₁` and hence in its
  closure, which is the case excluded here.

Hence `z ∈ frontier (D.deform ⁻¹' …)` and `hcov` covers it.
-/

open LeanEval.KnotTheory.PardonDistortion Set
open scoped Topology

namespace Work.Drive.Final

noncomputable section

variable {ψ : Submission.Diffeo} {K : Knot} {s u h R : ℝ} {c v : R3} {σ : Equiv.Perm (Fin 3)}
  {ℓ : R3 →L[ℝ] ℝ} {U : Set R3}

/-- The dent never lowers the level functional (`χ ≥ 0`, `a' > 0`, `ℓ d > 0`). -/
private theorem dent_deform_wall_le (D : AnyDentDatum ψ K s c σ u v h R ℓ U) (z : R3) :
    ℓ z ≤ ℓ (D.deform z) := by
  have h : ℓ (D.deform z) = ℓ z + (D.a' * D.χ (‖z - D.centre‖ / D.r)) * ℓ D.d := by
    simp only [AnyDentDatum.deform, dentDeform, map_add, map_smul, smul_eq_mul]
  rw [h]
  have hnn : 0 ≤ (D.a' * D.χ (‖z - D.centre‖ / D.r)) * ℓ D.d :=
    mul_nonneg (mul_nonneg (le_of_lt D.a'_pos) (D.χ_nonneg _)) (le_of_lt D.push_pos)
  linarith

/-- The dent preserves the open box: inside its ball this is the datum's `box_pres`, outside the
deformation is the identity. -/
private theorem dent_deform_mem_PBox (D : AnyDentDatum ψ K s c σ u v h R ℓ U) {y : R3}
    (hy : y ∈ Submission.PBox s c σ) : D.deform y ∈ Submission.PBox s c σ := by
  by_cases hb : ‖y - D.centre‖ ≤ D.r
  · exact (D.box_pres y hb).mp hy
  · rw [not_le] at hb
    have hχ : D.χ (‖y - D.centre‖ / D.r) = 0 := by
      apply D.χ_eq_zero
      rw [one_le_div D.r_pos]
      exact le_of_lt hb
    have hself : D.deform y = y := by
      simp only [AnyDentDatum.deform, dentDeform, hχ, mul_zero, zero_smul, add_zero]
    rw [hself]
    exact hy

/-- A point of the open box whose level is at least `lam` is mapped by the dent into the removed set
of the level `lam`. -/
private theorem dent_deform_mem_tiltedLevelRemoved (D : AnyDentDatum ψ K s c σ u v h R ℓ U)
    {lam : ℝ} {y : R3} (hy : y ∈ Submission.PBox s c σ) (hyl : lam ≤ ℓ y) :
    D.deform y ∈ Work.Drive.Mono.tiltedLevelRemoved s c σ u v h ℓ lam := by
  rw [Work.Drive.Mono.tiltedLevelRemoved, Set.mem_sdiff, Set.mem_inter_iff, Set.mem_ofPred_eq]
  refine ⟨dent_deform_mem_PBox D hy, ?_⟩
  rintro ⟨-, hlt⟩
  exact absurd (lt_of_le_of_lt (dent_deform_wall_le D y) hlt) (not_lt.mpr hyl)

theorem dentOut_hgen_of_trace
    {ψ : Submission.Diffeo} {K : LeanEval.KnotTheory.PardonDistortion.Knot} {s u h R : ℝ}
    {c v : LeanEval.KnotTheory.PardonDistortion.R3} {σ : Equiv.Perm (Fin 3)}
    {ℓ : LeanEval.KnotTheory.PardonDistortion.R3 →L[ℝ] ℝ} {exc : Finset ℝ} {lam0 lam1 : ℝ}
    {U : Set LeanEval.KnotTheory.PardonDistortion.R3}
    (hG : Work.Drive.Final.GoodSweepData3 ψ K s c σ u v h R ℓ exc lam0 lam1)
    (D : Work.Drive.Final.AnyDentDatum ψ K s c σ u v h R ℓ U)
    {n : ℕ} {cs : Fin n → Work.CoreTopology.ClosedCurve (Work.Drive.EpsSphere.torusOf ψ)}
    (hcov : (Work.Drive.EpsSphere.torusOf ψ).carrier ∩
        frontier (D.deform ⁻¹' Work.Drive.Mono.tiltedLevelRemoved s c σ u v h ℓ (ℓ D.centre)) ⊆
      ⋃ i, Set.range (cs i).γ)
    {z : LeanEval.KnotTheory.PardonDistortion.R3}
    (hzc : z ∈ (Work.Drive.EpsSphere.torusOf ψ).carrier)
    (hzbox : z ∈ closure (Submission.PBox s c σ))
    (hzslab : |Work.Drive.Final.slabFn c u v z| ≤ h)
    (hzℓ : ℓ z = ℓ D.centre) :
    z ∈ closure (Work.Drive.Final.dentOutRegion ψ s c σ u v h R ℓ D) ∪ ⋃ i, Set.range (cs i).γ := by
  classical
  -- the bundle: `GammaTransverse` and the positivity of `s`
  have hG' := hG
  obtain ⟨hDP2, hEF, hSIB, hSBCR, hGT, hFRC, hcorner, hoffK, hone, hSCA⟩ := hG'
  have hDP2' := hDP2
  obtain ⟨hGD, hBoxGen, hsingle, hevFace, hfaceDeg, htriple⟩ := hDP2'
  have hGD' := hGD
  obtain ⟨hTD, hAbove, hBelow, hoffK2, hknotGP⟩ := hGD'
  have hTD' := hTD
  obtain ⟨hTG, hvn, hℓne, hℓv, hsize, hh, hRPBox, hlow, hhigh, hl01, hexc⟩ := hTD'
  have hs : 0 < s := by
    obtain ⟨y₀, hy₀, -⟩ := hAbove
    have h1 := (Submission.mem_PBox (r := s) (c := c) (σ := σ) (y := y₀)).mp hy₀ 0
    rw [Submission.boxSide_zero, one_mul] at h1
    exact lt_of_le_of_lt (abs_nonneg _) h1
  rcases dentOut_hgen_geometric hG D hzc hzbox hzslab hzℓ with hgeo | hbox
  · exact Or.inl hgeo
  by_cases hcl : z ∈ closure (dentOutRegion ψ s c σ u v h R ℓ D)
  · exact Or.inl hcl
  -- `z` is on the box sphere and not in the closure of the region: put it in the trace
  refine Or.inr (hcov ⟨hzc, ?_⟩)
  rw [(closure_sdiff_interior _).symm, Set.mem_sdiff]
  refine ⟨?_, ?_⟩
  · -- `z` is a limit of points of the preimage of the removed set
    rw [Metric.mem_closure_iff]
    intro ε hε
    obtain ⟨x, y, hxy⟩ := (Work.CoreTopology.ParamTorus.mem_carrier_iff _ z).mp hzc
    set p : ℝ × ℝ := (x, y) with hpdef
    have hp : Work.BoxShrink.Pinch.par ψ p = z := hxy
    have hboxp : Submission.boxNorm c σ (Work.BoxShrink.Pinch.par ψ p) = s := by
      rw [hp]; exact hbox
    have hslabp : |slabFn c u v (Work.BoxShrink.Pinch.par ψ p)| ≤ h := by
      rw [hp]; exact hzslab
    obtain ⟨hD, htrans⟩ := hGT p hboxp hslabp
    obtain ⟨δ, hδpos, hdir⟩ :=
      Work.Drive.Mono.hdir_of_htrans (u := u) (v := v) (h := h) (lam := ℓ D.centre)
        (z := z) (p := p) hs hℓne hbox hzℓ hp hD htrans
    obtain ⟨y', hy'd, hy'b, hy'l⟩ := hdir z (by rw [dist_self]; exact hδpos) hbox hzℓ ε hε
    exact ⟨y', dent_deform_mem_tiltedLevelRemoved D
      ((Submission.mem_PBox_iff s c σ y').mpr hy'b) hy'l, by rw [dist_comm]; exact hy'd⟩
  · -- `z` is not an interior point of the preimage
    intro hzint
    exact hcl (subset_closure (show z ∈ dentOutRegion ψ s c σ u v h R ℓ D from ⟨hzc, hzint⟩))

end

end Work.Drive.Final
