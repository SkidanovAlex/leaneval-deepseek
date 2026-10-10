import Mathlib.GroupTheory.Nilpotent
import Mathlib.Algebra.Algebra.ZMod
import Mathlib.Algebra.Field.ZMod
import Mathlib.LinearAlgebra.FiniteDimensional.Basic
import Mathlib.LinearAlgebra.Matrix.FiniteDimensional
import Mathlib.RingTheory.Coalgebra.IsFrobenius
import Mathlib.RingTheory.HopfAlgebra.Basic
import Submission.Work.SSGRoute.TateDual.finrank_coindShift_eq_finrank_dual_coindUp
import Submission.Work.SSGRoute.TateDual.pairLin_equiv
import Submission.Work.SSGRoute.TateDual.pairLin_ker
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace Work.SSGRoute.TateDual

/-!
**Duality of the shift sequence**: the dual of the `I_G`-twist `coindUp G (M^∨)` is the shift
`coindShift G M = Coind(M)/M`, `G`-equivariantly.

Mathematics.  Let `M` be a finite `𝔽_p[G]`-module and put `A := M^∨ = Work.SSGRoute.DualMod p M`
(`Hom(M, 𝔽_p)` with the dual action `(g • φ) m = φ (g⁻¹ • m)`).  On the coinduced modules
`Coind(M) = (G → M)` and `Coind(A) = (G → A)` consider the pairing `⟨f, g⟩ = ∑ x, (g x) (f x)`;
it is `G`-invariant (`(γ • h) x = h (x * γ)` on both factors, cf. `Work.Tate.coind_smul_eq`).
Its left kernel is the diagonal `Work.Tate.coindDiag G M = {(x ↦ x • m)}` and its right kernel is
`Work.Tate.coindUp G A = ker (Work.Tate.coindAug G A)`, where `coindAug g = ∑ x, x⁻¹ • g x`:

* if `f = (x ↦ x • m)` then `⟨f, g⟩ = ∑ x, (g x) (x • m) = ∑ x, (x⁻¹ • g x) m = (coindAug g) m`,
  which vanishes for `g ∈ coindUp G A`;
* conversely, if `⟨f, ·⟩` vanishes on `coindUp G A`, test against the two-point functions `g`
  supported on `{a, b}` with `g a = a • ψ`, `g b = - b • ψ` (`ψ ∈ A`, `a ≠ b`): these lie in
  `coindUp G A` because `a⁻¹ • (a • ψ) + b⁻¹ • (-(b • ψ)) = 0`, and `⟨f, g⟩ = 0` for them says
  `ψ (a⁻¹ • f a) = ψ (b⁻¹ • f b)` for all `ψ`, i.e. `f` is of the shape `x ↦ x • m`.  So
  `(coindUp G A)^⊥ = coindDiag G M`.

Hence the pairing induces a linear equivalence `Coind(M)/coindDiag ≅ Dual(coindUp G A)`.  Here the
finiteness hypothesis `[Finite M]` is used: both sides are finite dimensional over the field `𝔽_p`
and have the same finrank (`|G|·d - d` with `d = finrank M` and `|G| = card G`), using
`Work.Tate.coindAug_surjective`, `Subspace.dual_finrank_eq` and
`Finsupp.linearEquivFunOnFinite`; alternatively use surjectivity of the restriction of functionals
to a subspace.  Since the pairing is `G`-invariant, this equivalence is `G`-equivariant; it is
exactly the dual of the shift sequence `0 → M → Coind(M) → A^♯ → 0` underlying
`Work.Tate.dimensionShiftH1H0`.

The statement below is the resulting equivariant additive isomorphism.  The `𝔽_p`-module structure
on `↥(Work.Tate.coindUp G (Work.SSGRoute.DualMod p M))` and on `Work.Tate.coindShift G M`
(needed for `Work.SSGRoute.DualMod p ↥…` to make sense, and for running finrank arguments) is
provided by `Submission.Work.SSGRoute.TateDual.Basic`, together with `Module.Finite`,
`FiniteDimensional` and `Finite` instances in the finite case.
-/

theorem dual_coindUp_coindShift (p : ℕ) [Fact p.Prime] (G : Type) [Group G] [Fintype G]
    (M : Type) [AddCommGroup M] [Module (ZMod p) M] [DistribMulAction G M]
    [SMulCommClass G (ZMod p) M] [Finite M] :
    ∃ e : (Work.SSGRoute.DualMod p ↥(Work.Tate.coindUp G (Work.SSGRoute.DualMod p M))) ≃+
        Work.Tate.coindShift G M,
      ∀ (γ : G)
        (x : Work.SSGRoute.DualMod p ↥(Work.Tate.coindUp G (Work.SSGRoute.DualMod p M))),
        e (γ • x) = γ • e x := by
  classical
  -- The pairing `Φ = pairLin`; its kernel is the diagonal `coindDiagSub`.
  let Φ : (G → M) →ₗ[ZMod p] DualMod p ↥(Work.Tate.coindUp G (DualMod p M)) :=
    pairLin p G M
  have hker : Φ.ker = coindDiagSub p G M := pairLin_ker p G M
  -- It descends to an injective map on the quotient `coindShift G M = Coind(M)/M`.
  let Φbar : ((G → M) ⧸ coindDiagSub p G M) →ₗ[ZMod p]
      DualMod p ↥(Work.Tate.coindUp G (DualMod p M)) :=
    (coindDiagSub p G M).liftQ Φ hker.symm.le
  have hkerbar : Φbar.ker = ⊥ :=
    Submodule.ker_liftQ_eq_bot' (coindDiagSub p G M) Φ hker.symm
  have hinj : Function.Injective Φbar := LinearMap.ker_eq_bot.mp hkerbar
  -- Both sides have the same `𝔽_p`-dimension `|G|·d - d`.
  have hfr : Module.finrank (ZMod p) ((G → M) ⧸ coindDiagSub p G M)
      = Module.finrank (ZMod p) (DualMod p ↥(Work.Tate.coindUp G (DualMod p M))) :=
    finrank_coindShift_eq_finrank_dual_coindUp p G M
  -- Hence it is surjective as well, and so an equivalence.
  have hrange : Φbar.range = ⊤ := by
    apply Submodule.eq_top_of_finrank_eq
    rw [LinearMap.finrank_range_of_inj hinj]
    exact hfr
  have hsurj : Function.Surjective Φbar := LinearMap.range_eq_top.mp hrange
  let φ : ((G → M) ⧸ coindDiagSub p G M) ≃ₗ[ZMod p]
      DualMod p ↥(Work.Tate.coindUp G (DualMod p M)) :=
    LinearEquiv.ofBijective Φbar ⟨hinj, hsurj⟩
  have hφbar_apply : ∀ f : G → M, φ (Submodule.Quotient.mk f) = Φ f := by
    intro f
    show Φbar (Submodule.Quotient.mk f) = Φ f
    exact Submodule.liftQ_apply (p := coindDiagSub p G M) Φ (h := hker.symm.le) f
  -- The pairing is `G`-equivariant, so `φ` is.
  have hφ : ∀ (γ : G) (v : (G → M) ⧸ coindDiagSub p G M), φ (γ • v) = γ • φ v := by
    intro γ v
    induction v using Submodule.Quotient.induction_on with
    | _ f =>
      rw [show γ • (Submodule.Quotient.mk f : (G → M) ⧸ coindDiagSub p G M)
            = Submodule.Quotient.mk (γ • f) from rfl]
      rw [hφbar_apply, hφbar_apply, pairLin_equiv]
  refine ⟨φ.symm.toAddEquiv, ?_⟩
  intro γ x
  show φ.symm (γ • x) = γ • φ.symm x
  have h := hφ γ (φ.symm x)
  rw [LinearEquiv.apply_symm_apply] at h
  exact φ.injective (by rw [h, LinearEquiv.apply_symm_apply])

end Work.SSGRoute.TateDual
