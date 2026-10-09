import Mathlib
import Submission.Work.SSGRoute.PT.alphaTwo_base_case
import Submission.Work.SSGRoute.PT.resH2
import Submission.Work.AbsoluteKummer.SES.ConnectingH2
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `corH2 ∘ resH2 = [G : U]` for the continuous `2`-cohomology

For a topological group `G`, an open finite-index subgroup `U ≤ G` and a discrete `G`-module `C`,
the **corestriction** `corH2 U hUo C`
(`Submission/Work/SSGRoute/PT/alphaTwo_base_case.lean`, `cor = mapH2 (trace) ∘ Shapiro⁻¹`) composed
with the **restriction** `resH2 U` (`Submission/Work/SSGRoute/PT/resH2.lean`) is multiplication by
the index `[G : U]`:

  `corH2 U hUo C (resH2 U y) = U.index • y`   for all `y ∈ H²(G, C)`.

This is the classical double-coset/transfer identity `cor ∘ res = [G : U]`, and it is what makes
the non-degeneracy of the corestriction on `p`-torsion *free* when `p ∤ [G : U]` (the `(β)` half of
the Shapiro/cup square, see the discussion in
`Submission/Work/SSGRoute/PT/alphaTwo_base_case.lean`).

## Proof

The point is the `G`-equivariant additive section of the evaluation at `1`

  `coindMu : C →+ Coind^G_U C`,  `coindMu c = (g ↦ g⁻¹ • c)`,

which satisfies

* `coindEv ∘ coindMu = id`   (`coindEv_coindMu`), and
* `trace ∘ coindMu = [G : U]` (`trace_coindMu`).

Since `shapiroEquiv` is built from evaluation at `1` (`phiC`), the class `mapH2 coindMu y` is
exactly the Shapiro preimage of `resH2 U y` (`shapiroEquiv_mapH2_coindMu`), and then the two
computation rules give the result.
-/

set_option linter.unusedSectionVars false

namespace Work.SSGRoute.PT

open Classical

noncomputable section

universe u

variable {G : Type u} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
variable {C : Type u} [AddCommGroup C] [DistribMulAction G C]

/-- The `G`-equivariant additive section `C →+ Coind^G_U C` of evaluation at `1`,
`c ↦ (g ↦ g⁻¹ • c)`. -/
def coindMu (U : Subgroup G) : C →+ Coind G U C where
  toFun c := ⟨fun g => g⁻¹ • c, fun g u => by
    show (g * (u : G))⁻¹ • c = u⁻¹ • (g⁻¹ • c)
    rw [mul_inv_rev]
    simp only [mul_smul, Subgroup.smul_def, Subgroup.coe_inv]⟩
  map_zero' := by apply Subtype.ext; funext g; simp
  map_add' c c' := by apply Subtype.ext; funext g; simp [smul_add]

/-- `coindMu` is `G`-equivariant. -/
theorem isEquivariant_coindMu (U : Subgroup G) :
    Work.GroupCohomology.IsEquivariant G (coindMu (C := C) U) := by
  intro g c
  apply Subtype.ext; funext x
  show x⁻¹ • (g • c) = (g⁻¹ * x)⁻¹ • c
  rw [mul_inv_rev, mul_smul, inv_inv]

/-- `coindMu` is a section of `coindEv`. -/
theorem coindEv_coindMu (U : Subgroup G) (c : C) :
    coindEv U C (coindMu U c) = c := by
  show (coindMu (C := C) U c) 1 = c
  show (1 : G)⁻¹ • c = c
  simp

/-- The trace of `coindMu c` is `[G : U] • c`. -/
theorem trace_coindMu (U : Subgroup G) [U.FiniteIndex] [Fintype (G ⧸ U)] (c : C) :
    trace U C (coindMu U c) = U.index • c := by
  rw [trace_apply]
  have hterm : ∀ C' : G ⧸ U, secC U C' • (coindMu U c) (secC U C') = c := by
    intro C'
    show secC U C' • ((secC U C')⁻¹ • c) = c
    rw [smul_smul, mul_inv_cancel, one_smul]
  rw [Finset.sum_congr rfl (fun C' _ => hterm C')]
  rw [Finset.sum_const, Finset.card_univ]
  rw [Subgroup.index_eq_card, Nat.card_eq_fintype_card]

/-- **The Shapiro preimage of a restriction**: `mapH2 coindMu y` is carried to `resH2 U y` by the
Shapiro isomorphism `H²(G, Coind^G_U C) ≃+ H²(U, C)` (which is evaluation at `1` on `2`-cocycles). -/
theorem shapiroEquiv_mapH2_coindMu (U : Subgroup G) [U.FiniteIndex] [Fintype (G ⧸ U)]
    (hUo : IsOpen (U : Set G)) (y : Work.AbsoluteKummer.H2 G C) :
    shapiroEquiv U hUo (Work.AbsoluteKummer.mapH2 (coindMu (C := C) U)
        (isEquivariant_coindMu U) y) = resH2 U y := by
  obtain ⟨c, hc⟩ := QuotientAddGroup.mk'_surjective
    ((Work.AbsoluteKummer.B2 G C).comap (Work.AbsoluteKummer.Z2 G C).subtype) y
  rw [show y = Work.AbsoluteKummer.H2π G C c from hc.symm]
  rw [Work.AbsoluteKummer.mapH2_H2π, shapiroEquiv_H2π, resH2_H2π]
  congr 1
  apply Subtype.ext
  funext p
  obtain ⟨u, v⟩ := p
  show phiC U C ((Work.AbsoluteKummer.mapZ2 (coindMu (C := C) U) (isEquivariant_coindMu U) c :
      Work.AbsoluteKummer.Z2 G (Coind G U C)) : G × G → Coind G U C) (u, v)
      = (c : G × G → C) ((u : G), (v : G))
  rw [phiC_apply, Work.AbsoluteKummer.mapZ2_apply]
  exact coindEv_coindMu U ((c : G × G → C) ((u : G), (v : G)))

/-- **The trace calculation**: `mapH2 (trace) ∘ mapH2 (coindMu)` is multiplication by `[G : U]`. -/
theorem mapH2_trace_mapH2_coindMu (U : Subgroup G) [U.FiniteIndex] [Fintype (G ⧸ U)]
    (y : Work.AbsoluteKummer.H2 G C) :
    Work.AbsoluteKummer.mapH2 (trace U C) (isEquivariant_trace U C)
      (Work.AbsoluteKummer.mapH2 (coindMu (C := C) U) (isEquivariant_coindMu U) y)
      = U.index • y := by
  obtain ⟨c, hc⟩ := QuotientAddGroup.mk'_surjective
    ((Work.AbsoluteKummer.B2 G C).comap (Work.AbsoluteKummer.Z2 G C).subtype) y
  rw [show y = Work.AbsoluteKummer.H2π G C c from hc.symm]
  rw [Work.AbsoluteKummer.mapH2_H2π, Work.AbsoluteKummer.mapH2_H2π]
  have hmap : Work.AbsoluteKummer.mapZ2 (trace U C) (isEquivariant_trace U C)
      (Work.AbsoluteKummer.mapZ2 (coindMu (C := C) U) (isEquivariant_coindMu U) c)
      = U.index • c := by
    apply Subtype.ext; funext p
    rw [Work.AbsoluteKummer.mapZ2_apply, Work.AbsoluteKummer.mapZ2_apply]
    exact trace_coindMu U ((c : G × G → C) p)
  rw [hmap, map_nsmul]

theorem corH2_resH2_eq_index
    {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    (U : Subgroup G) (hUo : IsOpen (U : Set G)) [U.FiniteIndex] [Fintype (G ⧸ U)]
    {C : Type} [AddCommGroup C] [DistribMulAction G C]
    (y : Work.AbsoluteKummer.H2 G C) :
    Work.SSGRoute.PT.corH2 U hUo C (Work.SSGRoute.PT.resH2 U y) = U.index • y := by
  have hA : shapiroEquiv U hUo (Work.AbsoluteKummer.mapH2 (coindMu (C := C) U)
        (isEquivariant_coindMu U) y) = resH2 U y :=
    shapiroEquiv_mapH2_coindMu U hUo y
  have hsymm : (shapiroEquiv U hUo (M := C)).symm (resH2 U y)
      = Work.AbsoluteKummer.mapH2 (coindMu (C := C) U) (isEquivariant_coindMu U) y := by
    rw [← hA, AddEquiv.symm_apply_apply]
  rw [corH2_apply, hsymm]
  exact mapH2_trace_mapH2_coindMu U y

end

end Work.SSGRoute.PT
