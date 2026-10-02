import Mathlib
import Submission.Work.Kunneth.TensorCo
import Submission.Work.Kunneth.CrossSum
import Submission.Work.Kunneth.Basic
import Submission.Work.Kunneth.ctens_dual_tpC
import Submission.Work.Kunneth.homology_ctens
import Submission.Work.Kunneth.homology_dual_tpC_ezaw
import Submission.Work.Kunneth.homology_dual_tpC_homSum
import Submission.Work.Cohomology.uctDual

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 400000

/-!
# The Künneth theorem for cohomology

For a simplicial set `Y` whose homology is free of finite rank in each degree (equivalently, by
`Work.Cohomology.uctDual`, whose cohomology is free of finite rank), and an **arbitrary** simplicial
set `X`, the cohomology of the product is the tensor product of the cohomologies:

`Hⁿ(X ⊗ Y; ℤ) ≅ ⨁_{p+q=n} Hᵖ(X;ℤ) ⊗ H^q(Y;ℤ)`.

The route is the chain of lemmas

* `Work.Kunneth.homology_dual_tpC_ezaw` — dualising Eilenberg–Zilber,
* `Work.Kunneth.homology_dual_tpC_homSum` — replacing `C(Y)` by its homology complex,
* `Work.Kunneth.ctens_dual_tpC` — the dual of a tensor product is a `ctens`,
* `Work.Kunneth.homology_ctens` — the cohomology of `ctens` is the tensor product of the
  cohomologies (flatness),
* `Work.Cohomology.uctDual` — `H^q(Y) ≅ Hom(H_q(Y), ℤ)`.
-/

set_option autoImplicit false
set_option maxHeartbeats 1600000

open CategoryTheory CategoryTheory.Limits HomologicalComplex
open scoped MonoidalCategory TensorProduct

namespace Work.Kunneth

noncomputable section

attribute [-instance] AddCommGroup.toIntModule

/-- The `ℤ`-dual of a free finite-rank module is free. -/
theorem free_homDual (M : ModuleCat ℤ) [Module.Free ℤ ↥M] [Module.Finite ℤ ↥M] :
    Module.Free ℤ ↥(homDual (fun _ => M) 0) :=
  Module.Free.of_basis (Module.finBasis ℤ ↥M).dualBasis

/-- **The Künneth theorem for cohomology**: for `Y` with free finite-rank homology,
`Hⁿ(X ⊗ Y) ≅ ⨁_{p+q=n} Hᵖ(X) ⊗ H^q(Y)` for every `X`. -/
theorem kunneth_cohomology (X Y : SSet) (n : ℕ)
    (hYt : ∀ q, Module.Projective ℤ ↥((Work.Kunneth.sChain Y).X q))
    (hYf : ∀ q, Module.Free ℤ ↥((Work.Kunneth.sChain Y).homology q))
    (hYn : ∀ q, Module.Finite ℤ ↥((Work.Kunneth.sChain Y).homology q)) :
    Nonempty (CategoryTheory.Iso
      ((Work.Cohomology.cochainC ℤ (Work.Kunneth.sProd X Y)).homology n)
      (Work.Kunneth.kunnethTarget X Y n)) := by
  have hYp : ∀ q, Module.Projective ℤ ↥((Work.Kunneth.sChain Y).homology q) := fun q => by
    haveI := hYf q
    exact Module.Projective.of_free
  have hT : ∀ q, Module.Flat ℤ ↥(homDual (fun q => (sChain Y).homology q) q) := fun q => by
    haveI := hYf q
    haveI := hYn q
    haveI : Module.Free ℤ ↥(homDual (fun q => (sChain Y).homology q) q) :=
      Module.Free.of_basis (Module.finBasis ℤ ↥((sChain Y).homology q)).dualBasis
    exact Module.Flat.of_free
  obtain ⟨e₁⟩ := homology_dual_tpC_ezaw X Y n
  obtain ⟨e₂⟩ := homology_dual_tpC_homSum (sChain X) (sChain Y) hYt hYp n
  obtain ⟨e₃⟩ := ctens_dual_tpC (sChain X) (fun q => (sChain Y).homology q) hYf hYn
  let F := HomologicalComplex.homologyFunctor (ModuleCat ℤ) (ComplexShape.up ℕ) n
  obtain ⟨e₄⟩ := homology_ctens (Work.Cohomology.dualComplex ℤ (sChain X))
    (homDual (fun q => (sChain Y).homology q)) hT n
  have hYcoh : ∀ q, CategoryTheory.Iso ((Work.Cohomology.cochainC ℤ Y).homology q)
      (homDual (fun q => (sChain Y).homology q) q) := fun q =>
    Classical.choice (Work.Cohomology.uctDual (sChain Y) hYt hYf q)
  have hstep : CategoryTheory.Iso (ctensH (Work.Cohomology.dualComplex ℤ (sChain X))
      (homDual (fun q => (sChain Y).homology q)) n) (kunnethTarget X Y n) :=
    (LinearEquiv.piCongrRight (fun pq : tpIdx n => TensorProduct.congr
      (CategoryTheory.Iso.toLinearEquiv (CategoryTheory.Iso.refl
        ((Work.Cohomology.cochainC ℤ X).homology pq.1.1)))
      (CategoryTheory.Iso.toLinearEquiv (hYcoh pq.1.2).symm))).toModuleIso
  exact ⟨e₁ ≪≫ e₂ ≪≫ (F.mapIso e₃) ≪≫ e₄ ≪≫ hstep⟩

end

end Work.Kunneth
