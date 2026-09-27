import Mathlib
import Submission.Work.EKLC6Core.cutHDefs
import Submission.Work.EKLC6Core.atom_gen_cut
import Submission.Work.EKLContract.Lemmas.mkX_mul

namespace Work.EKLC6Core

open MeasureTheory Set Topology
open Work.EKLContract

/-- **The shape of the cut σ-algebra at a point of a cell.**  Let `S` be the cut data
(`CutData μ U ε`), `O` a countable family of open sets whose `U`-saturations cover `SL₃(ℝ)`
(`hvis`) and separate points up to left `U`-cosets (`hsep`), and let `M = MCut S O` be the cut
σ-algebra.  For `y ∈ S.cell i` at which the `U`-action is *free*, the shape of `M` at `y` is

`{u ∈ U | u • y ∈ cell i, u * lift i y ∈ V (10 ρ) · g i}`,

i.e. exactly the elements of `U` that keep `y` inside its own cell and whose action on the lift
stays in the lift ball of `cell i`.

The forward inclusion uses the atom computation `atom_gen_cut` (the atom of `y` consists of the
points of `cell i` whose lift is left-`U`-related to `lift i y`) plus the freeness of `y` to
sharpen the `U`-relation to the identity, and the *uniqueness* of the lift to identify
`u * lift i y` with `lift i (u • y)`; the backward inclusion is the same uniqueness statement
together with `atom_gen_cut`. -/
theorem cutHShapeCell {μ : MeasureTheory.Measure Work.EKLContract.X3}
    {U : Subgroup Work.EKLContract.SL3} {ε : ℝ}
    (S : Work.EKLC6Core.CutData μ U ε) (O : ℕ → Set Work.EKLContract.SL3)
    (hOopen : ∀ m, IsOpen (O m))
    (hvis : ∀ z : Work.EKLContract.SL3, ∃ m, z ∈ Work.EKLC6Core.sat U (O m))
    (hsep : ∀ z w : Work.EKLContract.SL3,
      (∀ m, (z ∈ Work.EKLC6Core.sat U (O m) ↔ w ∈ Work.EKLC6Core.sat U (O m))) →
      w ∈ Work.EKLC6Core.sat U ({z} : Set Work.EKLContract.SL3))
    {i : Fin S.N} {y : Work.EKLContract.X3} (hy : y ∈ S.cell i)
    (hfree : y ∈ Work.EKLC6Core.cutFree U) :
    Work.EKLContract.shape (Work.EKLC6Core.MCut S O) U y =
      {u : Work.EKLContract.SL3 | u ∈ U ∧ u • y ∈ S.cell i ∧
        u * S.lift i y ∈ Work.EKLC6Core.shift (Work.EKLContract.V (10 * S.ρ)) (S.g i)} := by
  classical
  have hatom : atom (MCut S O) y =
      {w : X3 | w ∈ S.cell i ∧
        ∃ u ∈ (U : Set SL3), S.lift i w = u * S.lift i y} :=
    atom_gen_cut S O hOopen hvis hsep i y hy
  ext u
  constructor
  · intro hu
    obtain ⟨huU, huatom⟩ := hu
    rw [hatom] at huatom
    obtain ⟨hcell, u', hu'U, hlift⟩ := huatom
    have hmk : u • y = u' • y := by
      have h := congrArg mkX hlift
      rwa [S.lift_mk i (u • y) hcell, Work.EKLContract.Lemmas.mkX_mul,
        S.lift_mk i y hy] at h
    have hunit : u'⁻¹ * u = 1 := by
      refine hfree (u'⁻¹ * u) (U.mul_mem (U.inv_mem hu'U) huU) ?_
      rw [mul_smul, hmk, inv_smul_smul]
    have huu' : u = u' := by
      calc u = u' * (u'⁻¹ * u) := by group
        _ = u' * 1 := by rw [hunit]
        _ = u' := by simp
    refine ⟨huU, hcell, ?_⟩
    rw [huu', ← hlift]
    exact S.lift_bdd i (u • y) hcell
  · rintro ⟨huU, hcell, h2⟩
    refine ⟨huU, ?_⟩
    rw [hatom]
    refine ⟨hcell, u, huU, ?_⟩
    exact (S.lift_uniq i (u • y) hcell (u * S.lift i y) (by
      rw [Work.EKLContract.Lemmas.mkX_mul, S.lift_mk i y hy]) h2).symm

end Work.EKLC6Core
