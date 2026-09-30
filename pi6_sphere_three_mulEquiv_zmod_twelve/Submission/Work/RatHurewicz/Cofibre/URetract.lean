import Mathlib
import Submission.Work.RatHurewicz.Cofibre.GluingRestricted
import Submission.Work.RatHurewicz.Cofibre.RelClass

/-!
# The classes of the gluing relation on the preimage of `cofibreU ι`

`cofibreU ι = {h < 1/2}` meets **both** summands of `E ⊕ Cone F` (unlike `cofibreV ι`, which meets
only `Sum.inr`), so the `Sum.inl` branch of the retraction `cofibreU ι → E` is `id`, not a constant.
Accordingly the well-definedness of that retraction is *not* a consequence of
`sumElim_const_cone_eq_of_eqvGen`, and needs the same **two-claim** structure as in `RelClass.lean`:

* **Claim A′** (`cofibreEqvGen_mem_U`): membership in `q ⁻¹' cofibreU ι` is invariant under the
  gluing relation.  (This is *cleaner* than the `pos`-invariance of `RelClass.lean`: the step
  `Sum.inl (ι z) ~ Sum.inr (coneIncl z)` has height `0 < 1/2` on **both** sides, and the apex steps
  have height `1 ≮ 1/2` on both sides.)
* **Claim B′** (to come): the retraction is constant on the classes, A′ supplying the middle point's
  membership in `trans` and the flipped argument's membership in `symm`.
-/

open scoped Topology unitInterval

namespace Work.RatHurewicz

noncomputable section

variable {E F : Type} [TopologicalSpace E] [TopologicalSpace F]

/-- **Claim A′.**  Membership in the preimage of `cofibreU ι` is invariant under the gluing
relation. -/
theorem cofibreEqvGen_mem_U (ι : C(F, E)) {x y : E ⊕ Work.Stems.Cone F}
    (h : Relation.EqvGen (cofibreRel ι) x y) :
    (x ∈ (Quotient.mk'' : E ⊕ Work.Stems.Cone F → cofibre ι) ⁻¹' cofibreU ι ↔
      y ∈ (Quotient.mk'' : E ⊕ Work.Stems.Cone F → cofibre ι) ⁻¹' cofibreU ι) := by
  induction h with
  | rel a b hab =>
    obtain ⟨z, rfl, rfl⟩ := hab
    simp only [Set.mem_preimage, mem_cofibreU_iff, cofibreHeight, cofibreHeightFun,
      Quotient.lift_mk, Sum.elim_inl, Sum.elim_inr, coneHeight, Work.Stems.coneIncl]
  | refl a => rfl
  | symm a b _ ih => exact ih.symm
  | trans a b c _ _ ihab ihbc => exact ihab.trans ihbc

/-- The computation rule of `coneBaseLtHalf` at the base of the cone. -/
theorem coneBaseLtHalf_coneIncl (ι : C(F, E)) (z : F)
    (h : coneHeight (Work.Stems.coneIncl z) < cofibreHalf) :
    coneBaseLtHalf ι ⟨Work.Stems.coneIncl z, h⟩ = ι z :=
  coneBaseLtHalf_coneMk ι (z, 0) h

/-- The raw retraction `cofibreU ι → E`, on the preimage of `cofibreU ι`: the identity on the `E`
summand and the collapse of the half-open cone on the other. -/
def uRetractFun (ι : C(F, E)) (e₀ : E) : E ⊕ Work.Stems.Cone F → E :=
  Sum.elim (fun e : E => e)
    (fun y : Work.Stems.Cone F =>
      if h : coneHeight y < cofibreHalf then coneBaseLtHalf ι ⟨y, h⟩ else e₀)

/-- **Claim B′.**  The raw retraction is constant on the gluing classes inside the preimage of
`cofibreU ι`.  `cofibreEqvGen_mem_U` supplies the middle point's membership in `trans` and the
flipped argument's membership in `symm`. -/
theorem uRetractFun_eq_of_eqvGen (ι : C(F, E)) (e₀ : E) {x y : E ⊕ Work.Stems.Cone F}
    (h : Relation.EqvGen (cofibreRel ι) x y)
    (hx : x ∈ (Quotient.mk'' : E ⊕ Work.Stems.Cone F → cofibre ι) ⁻¹' cofibreU ι)
    (hy : y ∈ (Quotient.mk'' : E ⊕ Work.Stems.Cone F → cofibre ι) ⁻¹' cofibreU ι) :
    uRetractFun ι e₀ x = uRetractFun ι e₀ y := by
  induction h with
  | rel a b hab =>
    obtain ⟨z, rfl, rfl⟩ := hab
    show (ι z : E) = (if h : coneHeight (Work.Stems.coneIncl z) < cofibreHalf then
      coneBaseLtHalf ι ⟨Work.Stems.coneIncl z, h⟩ else e₀)
    rw [dif_pos (by rw [coneHeight_coneIncl]; exact cofibreHalf_pos)]
    exact (coneBaseLtHalf_coneIncl ι z _).symm
  | refl a => rfl
  | symm a b hab ih =>
    have ha : a ∈ (Quotient.mk'' : E ⊕ Work.Stems.Cone F → cofibre ι) ⁻¹' cofibreU ι :=
      (cofibreEqvGen_mem_U ι hab).mpr hx
    exact (ih ha hx).symm
  | trans a b c hab hbc ihab ihbc =>
    have hb : b ∈ (Quotient.mk'' : E ⊕ Work.Stems.Cone F → cofibre ι) ⁻¹' cofibreU ι :=
      (cofibreEqvGen_mem_U ι hab).mp hx
    exact (ihab hx hb).trans (ihbc hb hy)

end

end Work.RatHurewicz
