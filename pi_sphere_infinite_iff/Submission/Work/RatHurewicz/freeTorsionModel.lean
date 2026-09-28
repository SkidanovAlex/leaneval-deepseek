import Mathlib
import Submission.Work.RatHurewicz.fin_prod_ratH_vanishing_rat
import Submission.Work.RatHurewicz.product_ratH_vanishing_rat
import Submission.Work.Serre.Models
import Submission.Work.Stems.Engine.EMVanFree
import Submission.Work.RatHurewicz.isEMSpaceUpTo_pi_fin

/-!
# The free-times-torsion product model of `K(ℤ^r ⊕ F, k)`

This is the `(Fin r → L) × T` case of the finitely generated case `hfg` of
`Work.RatHurewicz.RangeModelRatAcyclic`: for `A ≅ ℤ^r ⊕ F` with `F` finite, a range model of
`K(A,k)` through degree `N` is realised as the product of `r` copies of a range model `L` of
`K(ℤ,k)` and a range model `T` of `K(F,k)`.

* `isEMSpaceUpTo_freeTorsion` — the product **is** a range model: it is
  `isEMSpaceUpTo_pi_fin` (the `Fin r`-fold product, `Fin r → L`) combined with
  `isEMSpaceUpTo_prod` (the product with `T`) and `isEMSpaceUpTo_of_addEquiv` (carrying the
  coefficient identification `A ≃+ (Fin r → ℤ) × F` across).
* `ratH_freeTorsion_vanishing` — its rational homology vanishes in degrees `k < j ≤ 2k-1`, which is
  `Work.Stems.prod_acyclic_ratH_vanishing` (Künneth plus the stable-range Serre exact
  sequence `Work.Serre.SerreExactRangeCorrected`), the C2 input being the vanishing conjunct for `L`
  and the C3 input the rational acyclicity of `T`.

The two inputs `hC2`/`hC3` are exactly the vanishing conjuncts of `Work.StemsB.C2RatSphere` and
`Work.StemsB.C3Finite`; the coefficient identification `A ≃+ (Fin r → ℤ) × F` is the structure
theorem for finitely generated abelian groups (`AddCommGroup.equiv_free_prod_directSum_zmod`).
-/

open CategoryTheory Limits
open scoped DirectSum

namespace Work.RatHurewicz

noncomputable section

/-- **The free-times-torsion product model is a range model.**  If `L` is a range model of
`K(ℤ,k)` and `T` a range model of `K(F,k)` (both through degree `N ≥ 2k-1`), then for every
additive isomorphism `A ≃+ (Fin r → ℤ) × F` the product `(Fin r → L) × T` is a range model of
`K(A,k)` through degree `N`. -/
theorem isEMSpaceUpTo_freeTorsion {A F : Type} [AddCommGroup A] [AddCommGroup F]
    (k N : ℕ) (hk : 2 ≤ k) (hN : 2 * k - 1 ≤ N) (r : ℕ)
    {L T : Type} [TopologicalSpace L] [TopologicalSpace T] (l₀ : L) (t₀ : T)
    (e : A ≃+ ((Fin r → ℤ) × F))
    (hL : Work.Serre.IsEMSpaceUpTo ℤ k (by omega) N L l₀)
    (hT : Work.Serre.IsEMSpaceUpTo F k (by omega) N T t₀) :
    Work.Serre.IsEMSpaceUpTo A k (by omega) N ((Fin r → L) × T) ((fun _ => l₀), t₀) := by
  have hk0 : 0 < k := by omega
  have hprod : Work.Serre.IsEMSpaceUpTo ((Fin r → ℤ) × F) k hk0 N
      ((Fin r → L) × T) ((fun _ => l₀), t₀) :=
    isEMSpaceUpTo_prod hk0 (fun _ => l₀) t₀
      (isEMSpaceUpTo_pi_fin hk0 r l₀ hL) hT
  exact isEMSpaceUpTo_of_addEquiv hk0 _ hprod e.symm

/-- **The rational homology of the free-times-torsion product model vanishes below `2k`.**  With the
C2 vanishing hypothesis for `L` (`H_j(L;ℚ) = 0` for `k < j ≤ 2k-1`) and the C3 hypothesis for `T`
(`H_j(T;ℚ) = 0` for `k < j ≤ 2k-1`), the product `(Fin r → L) × T` has `H_j = 0` for `k < j ≤ 2k-1`.

Both hypotheses are **ranged** (not `∀ 0 < j`): for a *range* model of `K(F,k)` the rational
acyclicity is known only up to the model's range `N`, and the range `k < j ≤ 2k-1 ≤ N` is exactly
what the two Künneth steps need.  (Do not re-route this through
`Work.Stems.prod_acyclic_ratH_vanishing`: that one asks `T` to be rationally acyclic in *all*
positive degrees, which no range model satisfies.) -/
theorem ratH_freeTorsion_vanishing (hSerre : Work.Serre.SerreExactRangeCorrected)
    {F : Type} [AddCommGroup F]
    (k N : ℕ) (hk : 2 ≤ k) (hN : 2 * k - 1 ≤ N) (r : ℕ)
    {L T : Type} [TopologicalSpace L] [TopologicalSpace T] (l₀ : L) (t₀ : T)
    (hL : Work.Serre.IsEMSpaceUpTo ℤ k (by omega) N L l₀)
    (hT : Work.Serre.IsEMSpaceUpTo F k (by omega) N T t₀)
    (hC2 : ∀ j : ℕ, k < j → j ≤ 2 * k - 1 → IsZero (Work.Serre.ratH (TopCat.of L) j))
    (hC3 : ∀ j : ℕ, k < j → j ≤ 2 * k - 1 → IsZero (Work.Serre.ratH (TopCat.of T) j)) :
    ∀ j : ℕ, k < j → j ≤ 2 * k - 1 →
      IsZero (Work.Serre.ratH (TopCat.of ((Fin r → L) × T)) j) := by
  -- both hypotheses are ranged (this is what makes the statement usable for *range* models of
  -- `K(F,k)`: for them the rational acyclicity is known only up to `N`), and the two Künneth steps
  -- `Work.Stems.fin_prod_ratH_vanishing` and `Work.Stems.product_ratH_vanishing` are ranged too.
  have hLc : Work.Serre.Conn L l₀ k := fun i hi => hL.2 i (by omega) (Or.inl hi)
  have hTc : Work.Serre.Conn T t₀ k := fun i hi => hT.2 i (by omega) (Or.inl hi)
  have hFL : ∀ j : ℕ, k < j → j ≤ 2 * k - 1 →
      IsZero (Work.Serre.ratH (TopCat.of (Fin r → L)) j) :=
    Work.Stems.fin_prod_ratH_vanishing k hk r l₀ hLc hC2 hSerre
  have hFLc : Work.Serre.Conn (Fin r → L) (fun _ => l₀) k :=
    Work.Stems.conn_fin_prod k r l₀ hLc
  exact Work.Stems.product_ratH_vanishing k hk (fun _ => l₀) t₀ hFLc hTc hFL hC3 hSerre

/-- **`ratH_freeTorsion_vanishing` with the integral Serre exact sequence dropped.**

The two Künneth steps are supplied by their rational forms
`Work.RatHurewicz.fin_prod_ratH_vanishing_rat` and `Work.RatHurewicz.product_ratH_vanishing_rat`
(both reduced to the *proved* rational pair comparison `Work.RatHurewicz.RatPairComparison`), so
the statement carries **no** `Work.Serre.SerreExactRangeCorrected` hypothesis. -/
theorem ratH_freeTorsion_vanishing' {F : Type} [AddCommGroup F]
    (k N : ℕ) (hk : 2 ≤ k) (hN : 2 * k - 1 ≤ N) (r : ℕ)
    {L T : Type} [TopologicalSpace L] [TopologicalSpace T] (l₀ : L) (t₀ : T)
    (hL : Work.Serre.IsEMSpaceUpTo ℤ k (by omega) N L l₀)
    (hT : Work.Serre.IsEMSpaceUpTo F k (by omega) N T t₀)
    (hC2 : ∀ j : ℕ, k < j → j ≤ 2 * k - 1 → IsZero (Work.Serre.ratH (TopCat.of L) j))
    (hC3 : ∀ j : ℕ, k < j → j ≤ 2 * k - 1 → IsZero (Work.Serre.ratH (TopCat.of T) j)) :
    ∀ j : ℕ, k < j → j ≤ 2 * k - 1 →
      IsZero (Work.Serre.ratH (TopCat.of ((Fin r → L) × T)) j) := by
  have hLc : Work.Serre.Conn L l₀ k := fun i hi => hL.2 i (by omega) (Or.inl hi)
  have hTc : Work.Serre.Conn T t₀ k := fun i hi => hT.2 i (by omega) (Or.inl hi)
  have hFL : ∀ j : ℕ, k < j → j ≤ 2 * k - 1 →
      IsZero (Work.Serre.ratH (TopCat.of (Fin r → L)) j) :=
    Work.RatHurewicz.fin_prod_ratH_vanishing_rat k hk r l₀ hLc hC2
  have hFLc : Work.Serre.Conn (Fin r → L) (fun _ => l₀) k :=
    Work.Stems.conn_fin_prod k r l₀ hLc
  exact Work.RatHurewicz.product_ratH_vanishing_rat k hk (fun _ => l₀) t₀ hFLc hTc hFL hC3

/-- `(Fin r →₀ ℤ) ≃+ (Fin r → ℤ)`: the finitely supported functions on a finite type are the
functions.  (Mathlib's `Finsupp.equivFunOnFinite` is only an `Equiv`.) -/
def finsuppAddEquivFun (r : ℕ) : ((Fin r →₀ ℤ) ≃+ (Fin r → ℤ)) where
  toFun := Finsupp.equivFunOnFinite
  invFun := Finsupp.equivFunOnFinite.symm
  left_inv := Finsupp.equivFunOnFinite.left_inv
  right_inv := Finsupp.equivFunOnFinite.right_inv
  map_add' _ _ := rfl

/-- **The structure theorem for finitely generated abelian groups, in the shape of
`isEMSpaceUpTo_freeTorsion`.**  Every finitely generated abelian group `A` is `ℤ^r × F`
(`AddCommGroup.equiv_free_prod_directSum_zmod` composed with `(Fin r →₀ ℤ) ≃+ (Fin r → ℤ)`); the
second factor is a finite direct sum of `ZMod (p i ^ e i)`, so it is finite
(`DirectSum.addEquivProd` into the finite product `∀ i, ZMod (p i ^ e i)`, since this Mathlib has
**no** `Fintype`/`Finite` instance for `DirectSum` itself) — and `Finite F` is what
`Work.StemsB.C3Finite` consumes. -/
theorem exists_addEquiv_free_prod_finite {A : Type} [AddCommGroup A] [Module.Finite ℤ A] :
    ∃ (r : ℕ) (F : Type) (_ : AddCommGroup F), Finite F ∧
      Nonempty (A ≃+ ((Fin r → ℤ) × F)) := by
  classical
  haveI hfg : AddGroup.FG A := Module.Finite.iff_addGroup_fg.mp ‹_›
  obtain ⟨n, ι, hι, p, hp, e, ⟨f⟩⟩ := AddCommGroup.equiv_free_prod_directSum_zmod A
  letI : Fintype ι := hι
  haveI : ∀ i : ι, NeZero (p i ^ e i) := fun i => ⟨pow_ne_zero _ (hp i).ne_zero⟩
  -- `⨁ i, ZMod (p i ^ e i)` is finite: it is the finite product `∀ i, ZMod (p i ^ e i)`
  haveI : Fintype (⨁ i : ι, ZMod (p i ^ e i)) :=
    Fintype.ofEquiv ((i : ι) → ZMod (p i ^ e i))
      (DirectSum.addEquivProd (ι := ι) (G := fun i => ZMod (p i ^ e i))).symm
  refine ⟨n, (⨁ i : ι, ZMod (p i ^ e i)), inferInstance, ?_, ⟨?_⟩⟩
  · exact (inferInstance : Finite (⨁ i : ι, ZMod (p i ^ e i)))
  · exact f.trans ((finsuppAddEquivFun n).prodCongr (AddEquiv.refl _))

end

end Work.RatHurewicz
