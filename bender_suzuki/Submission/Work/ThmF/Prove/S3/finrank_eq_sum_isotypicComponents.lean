import Mathlib
import Submission.Work.ThmF.Prove.S3.clifford_setup

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

noncomputable section

open scoped MonoidAlgebra
open DirectSum

namespace Work.ThmF.Prove.S3

/-! ## Additivity of the `finrank` over an independent spanning family of submodules

If a finite-dimensional `K`-vector space `V` is the sup of an independent family of subspaces
`p i` (in the sense of `iSupIndep`, i.e. `V` is the *internal* direct sum of the `p i`), then
the dimension of `V` is the sum of the dimensions of the `p i`. -/
theorem finrank_eq_sum_of_iSupIndep {K V : Type*} [Field K] [AddCommGroup V] [Module K V]
    [FiniteDimensional K V] {ι : Type*} [Fintype ι] (p : ι → Submodule K V)
    (hind : iSupIndep p) (htop : ⨆ i, p i = ⊤) :
    Module.finrank K V = ∑ i, Module.finrank K (p i) := by
  classical
  haveI : ∀ i, Module.Finite K (p i) := fun i =>
    Submodule.finiteDimensional_of_le (S₁ := p i) (S₂ := ⊤) le_top
  rw [← LinearEquiv.finrank_eq (hind.linearEquiv htop)]
  exact Module.finrank_directSum K (fun i => (p i : Type _))

/-! ## Restriction of scalars preserves disjointness of submodules -/

/-- Restricting scalars along a compatible semiring action preserves disjointness of
submodules: it is a complete lattice homomorphism, hence preserves `⊓` and `⊥`. -/
lemma disjoint_restrictScalars {S R M : Type*} [Semiring R] [Semiring S] [AddCommMonoid M]
    [Module S M] [Module R M] [SMul S R] [IsScalarTower S R M] {s t : Submodule R M}
    (h : Disjoint s t) : Disjoint (s.restrictScalars S) (t.restrictScalars S) := by
  rw [disjoint_iff] at h ⊢
  rw [← Submodule.restrictScalars_inf, h, Submodule.restrictScalars_bot]

/-- The `F`-dimension of a finite-dimensional representation is the sum of the `F`-dimensions of
the isotypic components of its restriction to a subgroup `K`, when that restriction is semisimple.

This is the dimension count underlying the decomposition of a `K`-module into its isotypic
components: the latter form an independent family of submodules spanning the whole space, so the
dimensions add up. -/
theorem finrank_eq_sum_isotypicComponents {L : Type*} [Group L] {F : Type*} [Field F]
    {K : Subgroup L} {V : Type*} [AddCommGroup V] [Module F V] [FiniteDimensional F V]
    (ρ : Representation F L V)
    [IsSemisimpleModule (MonoidAlgebra F K) (resRep (K := K) ρ).asModule]
    [Fintype (isotypicComponents (MonoidAlgebra F K) (resRep (K := K) ρ).asModule)] :
    Module.finrank F V = ∑ C : (isotypicComponents (MonoidAlgebra F K) (resRep (K := K) ρ).asModule),
      Module.finrank F ↥(C : Submodule (MonoidAlgebra F K) (resRep (K := K) ρ).asModule) := by
  classical
  -- The isotypic components form an independent family of `F[K]`-submodules spanning the space.
  have hind : iSupIndep ((↑) : isotypicComponents (MonoidAlgebra F K) (resRep (K := K) ρ).asModule →
      Submodule (MonoidAlgebra F K) (resRep (K := K) ρ).asModule) :=
    (sSupIndep_iff _).mp (sSupIndep_isotypicComponents _ _)
  have htop : ⨆ i : isotypicComponents (MonoidAlgebra F K) (resRep (K := K) ρ).asModule,
      (i : Submodule (MonoidAlgebra F K) (resRep (K := K) ρ).asModule) = ⊤ :=
    (sSup_eq_iSup' _).symm.trans (sSup_isotypicComponents _ _)
  -- Forget the `F[K]`-action: this yields an independent spanning family of `F`-subspaces.
  let q : isotypicComponents (MonoidAlgebra F K) (resRep (K := K) ρ).asModule →
      Submodule F (resRep (K := K) ρ).asModule :=
    fun C => (C : Submodule (MonoidAlgebra F K) (resRep (K := K) ρ).asModule).restrictScalars F
  have hq : iSupIndep q := by
    rw [iSupIndep_def] at hind ⊢
    intro i
    have h := hind i
    dsimp only [q]
    have h2 : (⨆ (j) (_ : j ≠ i),
        (j : Submodule (MonoidAlgebra F K) (resRep (K := K) ρ).asModule)).restrictScalars F
        = ⨆ (j) (_ : j ≠ i),
        ((j : Submodule (MonoidAlgebra F K) (resRep (K := K) ρ).asModule).restrictScalars F) := by
      simp only [Submodule.restrictScalars_iSup]
    rw [← h2]
    exact disjoint_restrictScalars h
  have hqtop : ⨆ C, q C = ⊤ := by
    change (⨆ C : isotypicComponents (MonoidAlgebra F K) (resRep (K := K) ρ).asModule,
        (C : Submodule (MonoidAlgebra F K) (resRep (K := K) ρ).asModule).restrictScalars F) = ⊤
    rw [← Submodule.restrictScalars_iSup, htop, Submodule.restrictScalars_top]
  exact finrank_eq_sum_of_iSupIndep q hq hqtop

end Work.ThmF.Prove.S3
