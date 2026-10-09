import Submission.Work.SSGRoute.E1aClean.BaseChangeExtCongr
import Submission.Work.SSGRoute.E1aClean.Transport
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-! # The `Ext`-side transport `Ext_G → Ext_{Gal(K/L)}`

**§2n correction.**  The right-congruence of the transport must be *explicit*:
`Work.SSGRoute.ext_congr_right` is a `Nonempty`, and `Classical.choice` of a `Nonempty` is an axiom
with no computation rule — so a factor defined from it has no describable value and admits no
`mk₀`-rule, which is why the level-change square was not provable as first formalised.  Here the
right-congruence is `extPostIsoHom` (`E1aClean/Transport.lean`), the explicit `mk₀`-postcomposition,
whose computation rule is `rfl`; the `Classical.choice` version is kept only as a statement about
existence. -/

namespace Work.SSGRoute.E1aClean

open CategoryTheory SSGRoute.PTExt

noncomputable section

variable {G : Type} [Group G]

/-- **The right-congruence of `Ext` as a named additive equivalence** — *existence only*.  Do **not**
use this inside a map whose value a later proof computes with (§2n): use `extCongrRightExplicit`. -/
noncomputable def extCongrRightEquiv {M N N' : Rep.{0} SSGRoute.PTExt.Coeff G} (e : N ≅ N')
    (n : ℕ) : Abelian.Ext M N n ≃+ Abelian.Ext M N' n :=
  Classical.choice (Work.SSGRoute.ext_congr_right (M := M) e n)

/-- The existence-only version as an additive map (kept for statement use only; see §2n). -/
noncomputable def extCongrRight {M N N' : Rep.{0} SSGRoute.PTExt.Coeff G} (e : N ≅ N') (n : ℕ) :
    Abelian.Ext M N n →+ Abelian.Ext M N' n :=
  (extCongrRightEquiv e n).toAddMonoidHom

/-- **The explicit right-congruence**: postcomposition with `mk₀ e.hom`, i.e. `extPostIsoHom`.
This is the one to use in computations (its value is its formula, so it has computation rules). -/
noncomputable def extCongrRightExplicit {M N N' : Rep.{0} SSGRoute.PTExt.Coeff G} (e : N ≅ N')
    (n : ℕ) : Abelian.Ext M N n →+ Abelian.Ext M N' n :=
  extPostIsoHom e M n

/-- Computation rule of the explicit right-congruence (`rfl`). -/
theorem extCongrRightExplicit_apply {M N N' : Rep.{0} SSGRoute.PTExt.Coeff G} (e : N ≅ N')
    (n : ℕ) (x : Abelian.Ext M N n) :
    extCongrRightExplicit e n x = Abelian.Ext.comp x (Abelian.Ext.mk₀ e.hom) (add_zero n) := rfl

/-- **The missing `mk₀`-rule of §2n's wiring list** (the one the `Classical.choice` version could
never have). -/
theorem extCongrRightExplicit_mk₀ {M N : Rep.{0} SSGRoute.PTExt.Coeff G} (f : M ⟶ N) :
    extCongrRightExplicit (CategoryTheory.Iso.refl N) 0 (Abelian.Ext.mk₀ f)
      = Abelian.Ext.mk₀ f := by
  rw [extCongrRightExplicit_apply]
  simp only [CategoryTheory.Iso.refl_hom, CategoryTheory.Abelian.Ext.comp_mk₀_id]

end

section Transport

variable {k : Type} [Field k] {Ω : Type} [Field Ω] [Algebra k Ω]
variable {K : IntermediateField k Ω}

/-- **The `Ext`-side transport of the level-change square**, with the *explicit* right-congruence
(§2n).  It is "restrict to `L.fixingSubgroup`, then transport to the base-changed group along
`galKMulEquiv L`", with the two `res_res_eq`-identifications absorbed by the left/right-congruences. -/
noncomputable def extTransport (L : IntermediateField k K)
    (M : Rep.{0} SSGRoute.PTExt.Coeff (K ≃ₐ[k] K)) (n : ℕ) :
    Abelian.Ext (Rep.res (L.fixingSubgroup).subtype M)
        (Rep.res (L.fixingSubgroup).subtype (SSGRoute.PTExt.unitsK k K)) n →+
      Abelian.Ext (Rep.res (galKIncl L) M)
        (Rep.res (galKIncl L) (SSGRoute.PTExt.unitsK k K)) n :=
  ((Work.SSGRoute.ExtChain.resMulEquiv (galKMulEquiv L) (Rep.res (galKIncl L) M)
      (Rep.res (galKIncl L) (SSGRoute.PTExt.unitsK k K)) n).toAddMonoidHom).comp
    ((extCongrRightExplicit (eqToIso (res_res_eq L (SSGRoute.PTExt.unitsK k K))) n).comp
      (extCongrLeft (eqToIso (res_res_eq L M)) n))


/-- **Regression guard for §2n.**  This `rfl`-level computation rule records that `extTransport`'s
value *is* its formula, built from the explicit right-congruence.  If anyone ever redefines
`extTransport` with a `Classical.choice`-based factor (as it was before §2n), this lemma can no
longer be proved and *this file breaks* — so the defect cannot silently return. -/
theorem extTransport_def (L : IntermediateField k K)
    (M : Rep.{0} SSGRoute.PTExt.Coeff (K ≃ₐ[k] K)) (n : ℕ) :
    extTransport L M n
      = ((Work.SSGRoute.ExtChain.resMulEquiv (galKMulEquiv L) (Rep.res (galKIncl L) M)
          (Rep.res (galKIncl L) (SSGRoute.PTExt.unitsK k K)) n).toAddMonoidHom).comp
        ((extCongrRightExplicit (eqToIso (res_res_eq L (SSGRoute.PTExt.unitsK k K))) n).comp
          (extCongrLeft (eqToIso (res_res_eq L M)) n)) := rfl

end Transport

end Work.SSGRoute.E1aClean
