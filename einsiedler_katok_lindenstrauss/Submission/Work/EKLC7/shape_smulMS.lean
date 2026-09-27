import Mathlib
import Submission.Work.EKLC7.SmulMS
import Submission.Work.EKLC7.atom_smulMS
import Submission.Work.EKLC7.Defs

/-!
# `Work.EKLC7.shape_smulMS` — translating a shape along the action

The shape of a σ-algebra `m` at `x` in a subgroup `U` is
`shape m U x = {u ∈ U : u • x ∈ [x]_m}` (`Work.EKLContract.Defs`).  The device
`smulMS u m = comap (fun y ↦ u⁻¹ • y) m` translates `m` along the point transformation
`R_u : y ↦ u • y`, so that the atoms are translated (`Work.EKLC7.atom_smulMS`):
`[u • x]_{R_u m} = u • [x]_m`.

The main lemma below computes the shape of the translated algebra at the translated point:
for `u ∈ U`,
`shape (smulMS u m) U (u • x) = (R_u ∘ conj_u) '' shape m U x`,
where `conj_u (g) = u * g * u⁻¹`; the reason is that
`g • (u • x) = u • ((u⁻¹ * g * u) • x)`, so the translated shape at `u • x` is the
`conj_u`-pullback of `shape m U x`, and since `u ∈ U`, conjugation by `u` preserves `U`.

The two elementary set-theoretic ingredients are isolated as `smul_mem_smulSt_iff` and
`conjImage_eq_setOf`.
-/

open MeasureTheory Topology Filter
open scoped ENNReal

set_option linter.unusedVariables false

noncomputable section

namespace Work.EKLC7

open Work.EKLContract

/-! ## Two elementary set identities -/

/-- **Membership in a translate of a set.**  For the point transformation `y ↦ u • y`,
`g • (u • x) ∈ smulSt u S` exactly when the conjugate `(u⁻¹ * g * u) • x` lies in `S`. -/
theorem smul_mem_smulSt_iff (u g : SL3) (x : X3) (S : Set X3) :
    g • (u • x) ∈ smulSt u S ↔ (u⁻¹ * g * u) • x ∈ S := by
  rw [smulSt_mem]
  have h : u⁻¹ • (g • (u • x)) = (u⁻¹ * g * u) • x := by
    rw [mul_smul, mul_smul]
  rw [h]

/-- **Conjugation image.**  The image of a set under the conjugacy `g ↦ u * g * u⁻¹` is the set
of `g` whose conjugate `u⁻¹ * g * u` lies in the set. -/
theorem conjImage_eq_setOf (u : SL3) (S : Set SL3) :
    (fun g : SL3 => u * g * u⁻¹) '' S = {g : SL3 | u⁻¹ * g * u ∈ S} := by
  ext g
  constructor
  · rintro ⟨h, hh, rfl⟩
    show u⁻¹ * (u * h * u⁻¹) * u ∈ S
    have heq : u⁻¹ * (u * h * u⁻¹) * u = h := by group
    rw [heq]
    exact hh
  · intro hg
    refine ⟨u⁻¹ * g * u, hg, ?_⟩
    show u * (u⁻¹ * g * u) * u⁻¹ = g
    group

/-- Membership in the subgroup `U` is preserved by conjugation by an element of `U`. -/
theorem mem_conj_iff_mem {U : Subgroup SL3} {u : SL3} (hu : u ∈ U) (g : SL3) :
    g ∈ U ↔ u⁻¹ * g * u ∈ U := by
  constructor
  · intro hg
    exact U.mul_mem (U.mul_mem (U.inv_mem hu) hg) hu
  · intro hg
    have hmem : u * (u⁻¹ * g * u) * u⁻¹ ∈ U :=
      U.mul_mem (U.mul_mem hu hg) (U.inv_mem hu)
    have heq : u * (u⁻¹ * g * u) * u⁻¹ = g := by group
    rwa [heq] at hmem

/-! ## The main lemma -/

theorem shape_smulMS {U : Subgroup Work.EKLContract.SL3} {m : MeasurableSpace Work.EKLContract.X3}
    {u : Work.EKLContract.SL3} (hu : u ∈ U) (x : Work.EKLContract.X3) :
    Work.EKLContract.shape (Work.EKLC7.smulMS u m) U (u • x)
      = (fun g : Work.EKLContract.SL3 => u * g * u⁻¹) '' Work.EKLContract.shape m U x := by
  ext g
  simp only [shape, Set.mem_ofPred_eq, conjImage_eq_setOf, atom_smulMS u m x,
    smul_mem_smulSt_iff, mem_conj_iff_mem hu g]

end Work.EKLC7
