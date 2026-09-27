import Mathlib
import Submission.Work.KT.Defs
import Submission.Work.KT.Basic

/-!
# `Work.KT.K0Shim` — a `Fund.Basic`-free supply of the elementary `K₀` lemmas

Several files in this workspace carry independent copies of the elementary calculus of the
idempotent model of `K₀`.  Two of them (`Submission.Work.KT.Fund.Basic` and
`Submission.Work.KT.Psi.Basic`) declare a constant `Work.KT.sphKTshim_K0_map_cls` with *different*
signatures, so no module can import both.  The node `Work.KT.sphere_K` needs the `Psi` side
(for `ψ²`, `ψ³`) and the product decomposition `K₀(A × B) ≅ K₀(A) × K₀(B)` of
`Work.KT.K0_prod`, whose proof had been written against `Fund.Basic`.

This file re-supplies the handful of `Fund.Basic` lemmas that `Work.KT.K0_prod` uses, on top of
`Submission.Work.KT.Basic`, with the *same* names and statements, so that `K0_prod.lean` can
import this file instead.  Nothing here is new mathematics.
-/

namespace Work.KT

open Matrix

noncomputable section

variable {R S : Type} [Ring R] [Ring S]

section Aux

/-- Matrix multiplication commutes with entrywise application of a ring map. -/
lemma sphKTshim_map_mul' {α β : Type} [Ring α] [Ring β] (φ : α →+* β)
    {l m n : Type} [Fintype m] (M : Matrix l m α) (N : Matrix m n α) :
    M.map φ * N.map φ = (M * N).map φ := by
  ext i j
  simp [Matrix.mul_apply, map_sum, map_mul]

end Aux

variable {R S : Type} [Ring R] [Ring S]

/-- Non-idempotent generators are zero. -/
lemma sphKTshim_cls_eq_zero_of_not_idem (p : Mat R) (hp : ¬ p.IsIdem) : cls p = 0 := by
  rw [show cls p = QuotientAddGroup.mk (FreeAbelianGroup.of p) from rfl,
    QuotientAddGroup.eq_zero_iff]
  exact AddSubgroup.subset_closure (Or.inr ⟨p, hp, rfl⟩)

/-- Murray–von Neumann equivalent idempotents have the same class. -/
lemma sphKTshim_cls_eq_of_mvn {p q : Mat R} (hp : p.IsIdem) (hq : q.IsIdem) (h : p.MvN q) :
    cls p = cls q := by
  have hmem : FreeAbelianGroup.of p - FreeAbelianGroup.of q ∈ K0Rel R :=
    AddSubgroup.subset_closure (Or.inl (Or.inr ⟨p, q, hp, hq, h, rfl⟩))
  have hzero : (cls p - cls q : K0 R) = 0 := by
    unfold cls
    rw [← QuotientAddGroup.mk_sub, QuotientAddGroup.eq_zero_iff]
    exact hmem
  rwa [sub_eq_zero] at hzero

/-- The block sum of two idempotents is idempotent. -/
lemma sphKTshim_sum_isIdem {p q : Mat R} (hp : p.IsIdem) (hq : q.IsIdem) : (p.sum q).IsIdem :=
  Mat.sum_idem hp hq

lemma sphKTshim_mvN_refl {p : Mat R} (hp : p.IsIdem) : p.MvN p := ⟨p.2, p.2, hp, hp⟩

lemma sphKTshim_isIdem_map {p : Mat R} (φ : R →+* S) (hp : p.IsIdem) : (p.map φ).IsIdem := by
  have hp' : p.2 * p.2 = p.2 := hp
  show p.2.map φ * p.2.map φ = p.2.map φ
  rw [sphKTshim_map_mul' φ p.2 p.2, hp']

lemma sphKTshim_mapCls_of_idem (φ : R →+* S) {p : Mat R} (hp : p.IsIdem) :
    mapCls φ p = cls (p.map φ) := by
  unfold mapCls
  rw [if_pos hp]

lemma sphKTshim_K0_map_cls' (φ : R →+* S) (p : Mat R) : K0.map φ (cls p) = mapCls φ p := by
  unfold cls K0.map
  rw [QuotientAddGroup.lift_mk, FreeAbelianGroup.lift_apply_of]

/-- `K0.map` on the class of an idempotent matrix. -/
lemma sphKTshim_K0_map_cls (φ : R →+* S) {p : Mat R} (hp : p.IsIdem) :
    K0.map φ (cls p) = cls (p.map φ) := by
  rw [sphKTshim_K0_map_cls', sphKTshim_mapCls_of_idem φ hp]

/-- Two homomorphisms out of `K₀` agreeing on generators agree. -/
lemma sphKTshim_addHom_ext {M : Type} [AddCommGroup M] {f g : K0 R →+ M}
    (h : ∀ p : Mat R, f (cls p) = g (cls p)) : f = g := by
  refine AddMonoidHom.ext (fun x => ?_)
  induction x using QuotientAddGroup.induction_on with
  | _ z =>
    induction z using FreeAbelianGroup.induction_on with
    | zero =>
      rw [show ((0 : FreeAbelianGroup (Mat R)) : K0 R) = 0 from rfl, map_zero, map_zero]
    | of p => change f (cls p) = g (cls p); exact h p
    | neg p ih =>
      rw [QuotientAddGroup.mk_neg, map_neg]
      simp only [map_neg, ih]
    | add p q ihp ihq =>
      rw [QuotientAddGroup.mk_add, map_add]
      simp only [map_add, ihp, ihq]

end

end Work.KT
