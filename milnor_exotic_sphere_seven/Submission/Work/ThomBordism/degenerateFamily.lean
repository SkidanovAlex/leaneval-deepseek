import Submission.Work.ThomBordism.familyAssembly
import Submission.Work.Cohomology.euclidean_top_homology_vanishing
import Submission.Work.ThomBordism.PontryaginThom.HurewiczAdditive

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 400000

/-!
# Degenerate pieces of a family: empty manifolds contribute nothing

`Work.ThomBordism.Man8` carries **no nonemptiness hypothesis** (the field `c_fund` is a `∀ x : pt, …`
and the manifold structure is constructible on an empty type), so the family form of the chapter's
inputs (`FamilyTubeData`, `TransversalityCoreFamily`, `CollarRealisation`, and PTGEOMETRIC's
`GenuineTubeGeometry`) does quantify over families with empty members — and the assembly of
`Work.ThomBordism.assembly` **does** produce such families (the degenerate pieces of a
`Work.Drive.Smooth8`, i.e. those whose fundamental class vanishes, are replaced by `Man8.empty`).

This file records that the empty case is *free* for the tubular data:

* `Man8.c_eq_zero_of_isEmpty` — an empty `Man8` has vanishing fundamental class (its degree-`8`
  homology is a subsingleton);
* `Man8.nonempty_of_c_ne_zero` — contrapositively, a `Man8` with non-vanishing class is nonempty
  (this is what makes the pieces of the assembly that are *not* replaced by `Man8.empty` nonempty);
* all three numbers (`σ`, `p₁²`, `p₂`) vanish for an empty `Man8`;
* `tubeThomRep_of_c_eq_zero` — the Pontryagin–Thom data of a manifold with vanishing fundamental
  class is inhabited with the *constant* collapse loop (both Hurewicz pairings are `0 = 0`); this is
  `Work.Tubular.TubeThomRep`, hence `FamilyTubeData`;
* `FamilyTubeData.of_nonempty` — to prove the tubular data of a family it suffices to prove it at the
  **nonempty** members.

Consequently the empty members of a family never obstruct the tubular data; the same is *not* true of
PTGEOMETRIC's `GenuineTubeGeometry`, which carries a total `TubeChart.inv : Euc (8+k) → NormalTotal E`
(both `Work.Tubular.exists_collapse_genLoop` and `Work.Tubular.hasTubularNeighbourhood` are stated
with `[Nonempty V.pt]`); see `CRITICAL_PATH.md` §8.
-/

set_option autoImplicit false
set_option maxHeartbeats 1600000
set_option linter.unusedVariables false

open scoped Manifold ContDiff

namespace Work.ThomBordism

open Work.ThomBordism.PontryaginThom

noncomputable section

/-! ## The degenerate `Man8`s -/

/-- **An empty `Man8` has vanishing fundamental class**: the singular chains of an empty space
vanish in every degree, so its degree-`8` homology is a subsingleton. -/
theorem Man8.c_eq_zero_of_isEmpty (V : Man8) [IsEmpty V.pt] : V.c = 0 := by
  have hz : CategoryTheory.Limits.IsZero
      ((Work.Cohomology.chainC ℤ (TopCat.toSSet.obj V.X)).homology 8) :=
    Work.Cohomology.isZero_homology_of_isEmpty_aux (TopCat.of V.pt) 8
  haveI : Subsingleton ↑((Work.Cohomology.chainC ℤ (TopCat.toSSet.obj V.X)).homology 8) :=
    ModuleCat.subsingleton_of_isZero hz
  exact Subsingleton.elim _ _

/-- **A `Man8` with non-vanishing fundamental class is nonempty** (the contrapositive of
`Man8.c_eq_zero_of_isEmpty`).  This is the reason the pieces of the assembly
`Work.ThomBordism.thomRational_of_transversalityCore` other than `Man8.empty` are nonempty. -/
theorem Man8.nonempty_of_c_ne_zero (V : Man8) (h : V.c ≠ 0) : Nonempty V.pt := by
  by_contra hne
  haveI : IsEmpty V.pt := not_nonempty_iff.mp hne
  exact h (V.c_eq_zero_of_isEmpty)

/-- **The numbers of an empty `Man8` vanish.**  (Stated for `σ`; the two Pontryagin numbers are
`Man8.p1Sq_eq_zero_of_isEmpty`, `Man8.p2Num_eq_zero_of_isEmpty`.) -/
theorem Man8.sigma_eq_zero_of_isEmpty (V : Man8) [IsEmpty V.pt] : V.sigma = 0 := by
  rw [show V.sigma = Work.SignatureBordism.sigma 4 (TopCat.toSSet.obj V.X) V.c from rfl,
    V.c_eq_zero_of_isEmpty, sigma_zero_fundamental]

/-- The `p₁²`-number of an empty `Man8` vanishes. -/
theorem Man8.p1Sq_eq_zero_of_isEmpty (V : Man8) [IsEmpty V.pt] : V.p1Sq = 0 := by
  rw [show V.p1Sq = Work.SignatureBordism.p₁SqNumber (TopCat.toSSet.obj V.X) V.c V.p1 from rfl,
    V.c_eq_zero_of_isEmpty, p₁SqNumber_zero_fundamental]

/-- The `p₂`-number of an empty `Man8` vanishes. -/
theorem Man8.p2Num_eq_zero_of_isEmpty (V : Man8) [IsEmpty V.pt] : V.p2Num = 0 := by
  rw [show V.p2Num = Work.SignatureBordism.p₂Number (TopCat.toSSet.obj V.X) V.c V.p2 from rfl,
    V.c_eq_zero_of_isEmpty, p₂Number_zero_fundamental]

/-- **The normal numbers of a manifold with vanishing fundamental class vanish.** -/
theorem NormalBundlData.normalP1Sq_eq_zero_of_c_eq_zero {V : Man8} (h : V.c = 0)
    (N : NormalBundlData V) : N.normalP1Sq = 0 := by
  rw [NormalBundlData.normalP1Sq, h]
  exact map_zero _

/-- **The normal numbers of a manifold with vanishing fundamental class vanish.** -/
theorem NormalBundlData.normalP2_eq_zero_of_c_eq_zero {V : Man8} (h : V.c = 0)
    (N : NormalBundlData V) : N.normalP2 = 0 := by
  rw [NormalBundlData.normalP2, h]
  exact map_zero _

/-! ## The Pontryagin–Thom data of a degenerate piece -/

/-- **The Hurewicz class of the constant loop vanishes** (the constant loop represents the unit of
the homotopy group). -/
theorem hurewiczClassOf_genLoop_const (k : ℕ) (D : ThomTarget k) :
    hurewiczClassOf (k + 8) (one_le_add_eight k) D.t₀
      (Quotient.mk _ (GenLoop.const : GenLoop (Fin (k + 8)) D.T D.t₀)) = 0 := by
  change hurewiczClassOf (k + 8) (one_le_add_eight k) D.t₀
    (1 : HomotopyGroup (Fin (k + 8)) D.T D.t₀) = 0
  exact hurewiczClassOf_one (one_le_add_eight k)

/-- **The Pontryagin–Thom data of a manifold with vanishing fundamental class is free**: the
constant loop has vanishing Hurewicz pairings and the *normal* numbers vanish, so both pairing
equalities are `0 = 0`.

This is the empty case of the tubular data: it is why `FamilyTubeData` (and hence
`Work.ThomBordism.PaddedTubeData`, obligation 2 of the chapter) is not refuted by the empty members of
a family.  The *tangent* numbers of such a manifold also vanish, but that is not needed here. -/
theorem tubeThomRep_of_c_eq_zero (k : ℕ) (D : ThomTarget k) {V : Man8} (hc : V.c = 0)
    (N : NormalBundlData V) : Nonempty (Work.Tubular.TubeThomRep k D V N) := by
  refine ⟨GenLoop.const, ?_, ?_⟩
  · rw [hurewiczClassOf_genLoop_const k D, NormalBundlData.normalP1Sq_eq_zero_of_c_eq_zero hc N]
    exact map_zero _
  · rw [hurewiczClassOf_genLoop_const k D, NormalBundlData.normalP2_eq_zero_of_c_eq_zero hc N]
    exact map_zero _

/-- The same for an empty manifold (`c = 0` by `Man8.c_eq_zero_of_isEmpty`). -/
theorem tubeThomRep_of_isEmpty (k : ℕ) (D : ThomTarget k) (V : Man8) [IsEmpty V.pt]
    (N : NormalBundlData V) : Nonempty (Work.Tubular.TubeThomRep k D V N) :=
  tubeThomRep_of_c_eq_zero k D V.c_eq_zero_of_isEmpty N

/-- **To prove the tubular data of a family it suffices to prove it at the nonempty members**: the
empty members carry the constant loop (`tubeThomRep_of_isEmpty`).

This is the form in which the tubular data (`FamilyTubeData`, or `PaddedTubeData`) should be proved:
the producer never has to produce a tubular neighbourhood of an empty manifold, while the *statement*
consumed by the chapter's assembly (which does contain empty pieces) is the unrestricted one. -/
theorem FamilyTubeData.of_nonempty {ι : Type} [Fintype ι] {F : ι → Man8} {k : ℕ} {D : ThomTarget k}
    (h : ∀ (i : ι) (N : NormalBundlData (F i)), Nonempty (F i).pt →
      Nonempty (Work.Tubular.TubeThomRep k D (F i) N)) :
    FamilyTubeData k D ι F := by
  intro i N
  by_cases hne : Nonempty (F i).pt
  · exact h i N hne
  · haveI : IsEmpty (F i).pt := not_nonempty_iff.mp hne
    exact tubeThomRep_of_isEmpty k D (F i) N

end

end Work.ThomBordism

namespace Work.ThomBordism

/-! ## Sums over the nonempty members of a family

The `Finset` bookkeeping used by every "drop the empty pieces" argument in this area. -/

/-- **A sum over the elements of a finite type that avoid a predicate equals the sum over the whole
type, provided the excluded terms vanish.**  (Wrapper around `Finset.sum_subtype` and
`Finset.sum_subset` for the case of `Finset.univ`.) -/
theorem Finset.sum_subtype_eq_sum_of_eq_zero {ι : Type} [Fintype ι] (P : ι → Prop) [DecidablePred P]
    {M : Type*} [AddCommMonoid M] (f : ι → M) (h : ∀ i, ¬ P i → f i = 0) :
    (∑ i : {i // P i}, f i.1) = ∑ i, f i := by
  rw [← Finset.sum_subtype (s := Finset.univ.filter P) (p := P) (by intro x; simp) f]
  exact Finset.sum_subset (Finset.filter_subset _ _) (fun x _ hx => h x (by simpa using hx))

/-- The same for a product index `Fin N × ι`. -/
theorem Finset.sum_prod_subtype_eq_sum_of_eq_zero {ι : Type} [Fintype ι] (P : ι → Prop)
    [DecidablePred P] (N : ℕ) {M : Type*} [AddCommMonoid M] (f : Fin N × ι → M)
    (h : ∀ i, ¬ P i.2 → f i = 0) :
    (∑ i : Fin N × {i : ι // P i}, f ⟨i.1, i.2.1⟩) = ∑ i : Fin N × ι, f i := by
  rw [Fintype.sum_prod_type, Fintype.sum_prod_type]
  refine Finset.sum_congr rfl fun n _ => ?_
  rw [← Finset.sum_subtype (s := Finset.univ.filter P) (p := P) (by intro x; simp)
    (fun i => f (n, i))]
  exact Finset.sum_subset (Finset.filter_subset _ _) (fun x _ hx => h (n, x) (by simpa using hx))

end Work.ThomBordism
