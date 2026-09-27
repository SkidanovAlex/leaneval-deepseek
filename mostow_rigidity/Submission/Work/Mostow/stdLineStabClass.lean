import Mathlib
import Submission.Work.Mostow.fermiTwoDefs
import Submission.Work.Mostow.Hyper
import Submission.Work.Mostow.hdistBasic
import Submission.Work.Mostow.hdistLineStd
import Submission.Work.Mostow.affineIsometryReal
import Submission.Work.Mostow.fermiTwoCoord
import Submission.Work.Mostow.jorthRow1Structure

/-!
# The setwise stabiliser of the standard geodesic of `ℍ²` acts affinely in Fermi coordinates

Let `lineStd s = sinh s • axis` be the standard unit-speed geodesic of the hyperbolic plane
`ℍ² = E 2` and let `stdFermi (s, r) = cosh r • lineStd s + sinh r • axisPerp` be its Fermi chart
(`lineStd s` is the foot, `r` the signed distance to the line).

If `g : PO 2 1` maps the line to itself (`∀ s, ∃ s', g • lineStd s = lineStd s'`), then in Fermi
coordinates `g` is affine: there are signs `ε, δ ∈ {±1}` and a translation `c` with
`g • stdFermi (s, r) = stdFermi (ε s + c, δ r)`.

The proof is matrix-level.  Write `A = rep g` and read the identity `hlift (g • u) =
tsign A • mat A *ᵥ hlift u` at the points `lineStd s`:

* the `inl 1` component of `hlift (lineStd s)` vanishes, and `hlift (lineStd s)` is
  `sinh s • e₀ + cosh s • e₂`, so `mat A (inl 1) (inl 0) * sinh s + mat A (inl 1) (inr 0) * cosh s
  = 0` for all `s`; evaluating at `s = 0` and `s = 1` gives `mat A (inl 1) (inl 0) = 0` and
  `mat A (inl 1) (inr 0) = 0`;
* `jorthRow1Structure` then turns this into `mat A (inl 0) (inl 1) = mat A (inr 0) (inl 1) = 0`
  and `mat A (inl 1) (inl 1) = ±1`, i.e. `mat A` is block diagonal with the middle coordinate
  scaled by the sign `δ = tsign A * mat A (inl 1) (inl 1)`;
* the `inl 0` component of the same identity reads `tsign A * (mat A (inl 0) (inl 0) * sinh s +
  mat A (inl 0) (inr 0) * cosh s) = sinh (φ s)` for the induced map `φ` of the line; since `g` is
  an isometry and `hdist (lineStd a) (lineStd b) = |a - b|` (`hdistLineStd`), `φ` preserves
  distances, so `affineIsometryReal` gives `φ s = ε s + c`.

Evaluating the two spatial coordinates of `hlift (g • stdFermi (s, r))` with the above structure
produces exactly the two coordinates of `stdFermi (ε s + c, δ r)`.
-/

namespace Work.Mostow

open Submission.Mostow LeanEval.Geometry.MostowRigidity MeasureTheory

/-! ## Coordinates of the standard line and of the standard Fermi chart -/

/-- `tpart` of the standard line. -/
private lemma tpart_lineStd (s : ℝ) : tpart (FermiTwo.lineStd s) = Real.cosh s :=
  fermiTwoCoord.1 s

/-- First coordinate of the standard line. -/
private lemma coord_lineStd_0 (s : ℝ) : (FermiTwo.lineStd s) 0 = Real.sinh s :=
  fermiTwoCoord.2.2.2.2.1 s

/-- Second coordinate of the standard line. -/
private lemma coord_lineStd_1 (s : ℝ) : (FermiTwo.lineStd s) 1 = 0 :=
  fermiTwoCoord.2.2.2.2.2.1 s

/-- First coordinate of the standard Fermi chart. -/
private lemma coord_stdFermi_0 (s r : ℝ) :
    (FermiTwo.stdFermi (s, r)) 0 = Real.cosh r * Real.sinh s :=
  fermiTwoCoord.2.1 s r

/-- Second coordinate of the standard Fermi chart. -/
private lemma coord_stdFermi_1 (s r : ℝ) : (FermiTwo.stdFermi (s, r)) 1 = Real.sinh r :=
  fermiTwoCoord.2.2.1 s r

/-- `tpart` of the standard Fermi chart. -/
private lemma tpart_stdFermi (s r : ℝ) :
    tpart (FermiTwo.stdFermi (s, r)) = Real.cosh r * Real.cosh s :=
  fermiTwoCoord.2.2.2.1 s r

/-- The hyperboloid lift of the standard line has coordinates `(sinh s, 0, cosh s)`. -/
private lemma hlift_lineStd_inl (s : ℝ) (i : Fin 2) :
    hlift (FermiTwo.lineStd s) (Sum.inl i) = (FermiTwo.lineStd s) i := by
  simp [hlift]

private lemma hlift_lineStd_inr (s : ℝ) :
    hlift (FermiTwo.lineStd s) (Sum.inr 0) = Real.cosh s := by
  simp [hlift, tpart_lineStd]

/-- The hyperboloid lift of `stdFermi (s, r)` has coordinates
`(cosh r * sinh s, sinh r, cosh r * cosh s)`. -/
private lemma hlift_stdFermi_inl (s r : ℝ) (i : Fin 2) :
    hlift (FermiTwo.stdFermi (s, r)) (Sum.inl i) = (FermiTwo.stdFermi (s, r)) i := by
  simp [hlift]

private lemma hlift_stdFermi_inr (s r : ℝ) :
    hlift (FermiTwo.stdFermi (s, r)) (Sum.inr 0) = Real.cosh r * Real.cosh s := by
  simp [hlift, tpart_stdFermi]

/-! ## Entries of `mat A *ᵥ hlift` on the standard line and Fermi chart -/

private lemma mulVec_hlift_lineStd_inl0 (A : O1 2) (s : ℝ) :
    ((mat A).mulVec (hlift (FermiTwo.lineStd s))) (Sum.inl 0)
      = (mat A) (Sum.inl 0) (Sum.inl 0) * Real.sinh s
        + (mat A) (Sum.inl 0) (Sum.inr 0) * Real.cosh s := by
  rw [Matrix.mulVec, dotProduct, Fintype.sum_sum_type, Fin.sum_univ_two, Fin.sum_univ_one]
  rw [hlift_lineStd_inl, hlift_lineStd_inl, hlift_lineStd_inr, coord_lineStd_0, coord_lineStd_1]
  ring

private lemma mulVec_hlift_lineStd_inl1 (A : O1 2) (s : ℝ) :
    ((mat A).mulVec (hlift (FermiTwo.lineStd s))) (Sum.inl 1)
      = (mat A) (Sum.inl 1) (Sum.inl 0) * Real.sinh s
        + (mat A) (Sum.inl 1) (Sum.inr 0) * Real.cosh s := by
  rw [Matrix.mulVec, dotProduct, Fintype.sum_sum_type, Fin.sum_univ_two, Fin.sum_univ_one]
  rw [hlift_lineStd_inl, hlift_lineStd_inl, hlift_lineStd_inr, coord_lineStd_0, coord_lineStd_1]
  ring

private lemma mulVec_hlift_stdFermi_inl0 (A : O1 2) (s r : ℝ) :
    ((mat A).mulVec (hlift (FermiTwo.stdFermi (s, r)))) (Sum.inl 0)
      = (mat A) (Sum.inl 0) (Sum.inl 0) * (Real.cosh r * Real.sinh s)
        + (mat A) (Sum.inl 0) (Sum.inl 1) * Real.sinh r
        + (mat A) (Sum.inl 0) (Sum.inr 0) * (Real.cosh r * Real.cosh s) := by
  rw [Matrix.mulVec, dotProduct, Fintype.sum_sum_type, Fin.sum_univ_two, Fin.sum_univ_one]
  rw [hlift_stdFermi_inl, hlift_stdFermi_inl, hlift_stdFermi_inr, coord_stdFermi_0, coord_stdFermi_1]

private lemma mulVec_hlift_stdFermi_inl1 (A : O1 2) (s r : ℝ) :
    ((mat A).mulVec (hlift (FermiTwo.stdFermi (s, r)))) (Sum.inl 1)
      = (mat A) (Sum.inl 1) (Sum.inl 0) * (Real.cosh r * Real.sinh s)
        + (mat A) (Sum.inl 1) (Sum.inl 1) * Real.sinh r
        + (mat A) (Sum.inl 1) (Sum.inr 0) * (Real.cosh r * Real.cosh s) := by
  rw [Matrix.mulVec, dotProduct, Fintype.sum_sum_type, Fin.sum_univ_two, Fin.sum_univ_one]
  rw [hlift_stdFermi_inl, hlift_stdFermi_inl, hlift_stdFermi_inr, coord_stdFermi_0, coord_stdFermi_1]

/-- The action of a group representative on the chart: the `i`-th coordinate is the
`i`-th spatial entry of `tsign A • mat A *ᵥ hlift u`. -/
private lemma coord_actO (A : O1 2) (u : E 2) (i : Fin 2) :
    (actO A u) i = tsign A * ((mat A).mulVec (hlift u)) (Sum.inl i) := rfl

theorem stdLineStabClass (hA : Submission.Mostow.POActionProp 2)
    (hI : Submission.Mostow.HypIsometryProp 2)
    (g : LeanEval.Geometry.MostowRigidity.PO 2 1)
    (h : ∀ s : ℝ, ∃ s' : ℝ, g • Work.Mostow.FermiTwo.lineStd s = Work.Mostow.FermiTwo.lineStd s') :
    ∃ ε δ c : ℝ, (ε = 1 ∨ ε = -1) ∧ (δ = 1 ∨ δ = -1) ∧
      ∀ s r : ℝ, g • Work.Mostow.FermiTwo.stdFermi (s, r) = Work.Mostow.FermiTwo.stdFermi (ε * s + c, δ * r) := by
  classical
  have hId := HypIsoData.ofProp hI
  -- the `•`-action of the chosen representative `rep g` is the matrix action `actO (rep g)`
  have hg_act : ∀ u : E 2, g • u = actO (rep g) u := by
    intro u
    have h3 : ((rep g : O1 2) : PO 2 1) • u = g • u := by
      rw [show ((rep g : O1 2) : PO 2 1) = g from Quotient.out_eq g]
    rw [← h3]
    exact hA.2.1 (rep g) u
  -- the induced self-map of the standard line
  choose φ hφ using h
  have hφiso : ∀ s t : ℝ, |φ s - φ t| = |s - t| := by
    intro s t
    rw [← hdistLineStd (φ s) (φ t), ← hdistLineStd s t, ← hφ s, ← hφ t]
    exact hId.isom_smul g (FermiTwo.lineStd s) (FermiTwo.lineStd t)
  obtain ⟨ε, c, hε, hφaff⟩ := affineIsometryReal φ hφiso
  -- the lift identity `hlift (g • lineStd s) = tsign A • mat A *ᵥ hlift (lineStd s)`
  have hcomp : ∀ s : ℝ, hlift (FermiTwo.lineStd (φ s))
      = tsign (rep g) • (mat (rep g)).mulVec (hlift (FermiTwo.lineStd s)) := by
    intro s
    rw [← hφ s, hg_act]
    exact Hyper.hlift_actO (rep g) (FermiTwo.lineStd s)
  -- the vanishing of the `(inl 1)` row of `mat A` off the middle column
  have hZ : ∀ s : ℝ, (mat (rep g)) (Sum.inl 1) (Sum.inl 0) * Real.sinh s
        + (mat (rep g)) (Sum.inl 1) (Sum.inr 0) * Real.cosh s = 0 := by
    intro s
    have hc := congrArg (fun v : Fin 2 ⊕ Fin 1 → ℝ => v (Sum.inl 1)) (hcomp s)
    simp only [Pi.smul_apply, smul_eq_mul] at hc
    have hL : hlift (FermiTwo.lineStd (φ s)) (Sum.inl 1) = 0 := by
      rw [hlift_lineStd_inl]; exact coord_lineStd_1 (φ s)
    rw [hL, mulVec_hlift_lineStd_inl1] at hc
    have hts : tsign (rep g) ≠ 0 := by
      rcases Hyper.tsign_eq_one_or (rep g) with hh | hh <;> rw [hh] <;> norm_num
    exact (mul_eq_zero.mp hc.symm).resolve_left hts
  have hY : (mat (rep g)) (Sum.inl 1) (Sum.inr 0) = 0 := by
    have h0 := hZ 0
    simpa using h0
  have hX : (mat (rep g)) (Sum.inl 1) (Sum.inl 0) = 0 := by
    have h1 := hZ 1
    simp only [hY, zero_mul, add_zero] at h1
    have hsinh : Real.sinh 1 ≠ 0 := ne_of_gt (Real.sinh_pos_iff.mpr one_pos)
    exact (mul_eq_zero.mp h1).resolve_right hsinh
  -- `mat A` is block diagonal: the middle coordinate is scaled by `±1`
  obtain ⟨h01, h21, h11⟩ := jorthRow1Structure (rep g) hX hY
  have hδ : (tsign (rep g) * (mat (rep g)) (Sum.inl 1) (Sum.inl 1) = 1 ∨
             tsign (rep g) * (mat (rep g)) (Sum.inl 1) (Sum.inl 1) = -1) := by
    rcases Hyper.tsign_eq_one_or (rep g) with ht | ht <;> rcases h11 with hh | hh <;>
      rw [ht, hh] <;> norm_num
  -- the `(inl 0)` component of the lift identity describes `sinh` of the induced map
  have hsinh : ∀ s : ℝ, tsign (rep g) * ((mat (rep g)) (Sum.inl 0) (Sum.inl 0) * Real.sinh s
      + (mat (rep g)) (Sum.inl 0) (Sum.inr 0) * Real.cosh s) = Real.sinh (φ s) := by
    intro s
    have hc := congrArg (fun v : Fin 2 ⊕ Fin 1 → ℝ => v (Sum.inl 0)) (hcomp s)
    simp only [Pi.smul_apply, smul_eq_mul] at hc
    have hL : hlift (FermiTwo.lineStd (φ s)) (Sum.inl 0) = Real.sinh (φ s) := by
      rw [hlift_lineStd_inl]; exact coord_lineStd_0 (φ s)
    rw [hL, mulVec_hlift_lineStd_inl0] at hc
    exact hc.symm
  refine ⟨ε, tsign (rep g) * (mat (rep g)) (Sum.inl 1) (Sum.inl 1), c, hε, hδ, ?_⟩
  intro s r
  have hcoshδ : Real.cosh ((tsign (rep g) * (mat (rep g)) (Sum.inl 1) (Sum.inl 1)) * r)
      = Real.cosh r := by
    rcases hδ with hh | hh <;> rw [hh] <;> simp [Real.cosh_neg]
  have hsinhδ : Real.sinh ((tsign (rep g) * (mat (rep g)) (Sum.inl 1) (Sum.inl 1)) * r)
      = (tsign (rep g) * (mat (rep g)) (Sum.inl 1) (Sum.inl 1)) * Real.sinh r := by
    rcases hδ with hh | hh <;> rw [hh] <;> simp [Real.sinh_neg]
  have key0 : (g • FermiTwo.stdFermi (s, r)) (0 : Fin 2)
      = (FermiTwo.stdFermi (ε * s + c,
          tsign (rep g) * (mat (rep g)) (Sum.inl 1) (Sum.inl 1) * r)) (0 : Fin 2) := by
    rw [hg_act, coord_actO, mulVec_hlift_stdFermi_inl0, coord_stdFermi_0, hcoshδ]
    simp only [h01, zero_mul, add_zero]
    rw [← hφaff s, ← hsinh s]
    ring
  have key1 : (g • FermiTwo.stdFermi (s, r)) (1 : Fin 2)
      = (FermiTwo.stdFermi (ε * s + c,
          tsign (rep g) * (mat (rep g)) (Sum.inl 1) (Sum.inl 1) * r)) (1 : Fin 2) := by
    rw [hg_act, coord_actO, mulVec_hlift_stdFermi_inl1, coord_stdFermi_1]
    simp only [hX, hY, zero_mul, add_zero]
    rw [hsinhδ]
    ring
  refine PiLp.ext (fun i => ?_)
  fin_cases i
  · exact key0
  · exact key1

end Work.Mostow
