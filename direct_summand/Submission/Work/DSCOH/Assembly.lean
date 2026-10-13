/-
Area DSCOH (curric-46) — the assembly of `DSMap.area_COH`.

`Work.DSCOH.area_COH_of_comparison` is the frozen conclusion of `DSMap.area_COH` derived from the
two inputs that the area itself cannot supply:

* the comparison isomorphism of the challenge's Čech model with the chart Čech complex of the
  graded module attached to the closed immersion `X ⊆ ℙ^{n-1}_A` (the geometric bridge), and
* the area's own theorem `Work.DSCOH.chartCech_finite_vanishing`.

Together with a sorry-free Čech model of `RΓ` (frozen area F1) this is all that `Main.lean`
needs; see `DESIGN.md` for the exact state of the three inputs.
-/
import Submission.Work.DSCOH.chartCech_finite_vanishing
import Submission.Work.DSCOH.RG_homology_isZero_of_neg

set_option linter.style.haveILetI false

open CategoryTheory AlgebraicGeometry Limits

namespace Work.DSCOH

universe a b c

/-- A module with a single element is finitely generated (it is the span of the empty set). -/
private lemma module_finite_of_subsingleton {R M : Type*} [Semiring R] [AddCommMonoid M]
    [Module R M] [Subsingleton M] : Module.Finite R M := by
  rw [Module.finite_def]
  refine ⟨∅, ?_⟩
  rw [Finset.coe_empty, Submodule.span_empty]
  refine le_antisymm bot_le fun x _ => ?_
  rw [Submodule.mem_bot]
  exact Subsingleton.elim x 0

/-- **The conclusion of `DSMap.area_COH`, from the Čech comparison.**

The hypothesis `h` is the geometric bridge: for every `q` the `q`-th cohomology of the challenge's
`RΓ(X, O_X)` is the `q`-th cohomology of the chart Čech complex of a finitely generated graded
module over `A[X₀,…,X_{n-1}]`.  With `h` and `Work.DSCOH.chartCech_finite_vanishing` this yields
the frozen conclusion `∃ N, ∀ i, Module.Finite A (H^i) ∧ (N < i → IsZero (H^i))` (take `N = n`).

Note the universes: the graded module must live in the same universe as `A` (so that
`chartCech`'s cohomology is a `ModuleCat.{a} A`, as in the frozen statement). -/
theorem area_COH_of_comparison (A : Type a) [CommRing A] [IsNoetherianRing A]
    [HasDerivedCategory.{b} (ModuleCat.{a} A)] (X : Scheme.{a}) (f : X ⟶ Spec (.of A))
    [HasDerivedCategory.{c} (SheafOfModules X.ringCatSheaf)]
    [EnoughInjectives (SheafOfModules X.ringCatSheaf)]
    {n : ℕ} {M : Type a} [AddCommGroup M] [Module A M] [Module (Poly A n) M]
    [IsScalarTower A (Poly A n) M] {ℳ : ℕ → Submodule A M} [DirectSum.Decomposition ℳ]
    [SetLike.GradedSMul (homSub A n) ℳ] [Module.Finite (Poly A n) M]
    (h : ∀ q : ℕ, Nonempty ((DerivedCategory.homologyFunctor (ModuleCat.{a} A) (q : ℤ)).obj
      (DerivedCategory.Plus.ι.obj (DSMap.RG A X f)) ≅
        (chartCech (A := A) (n := n) (M := M) ℳ).homology q)) :
    ∃ N : ℤ, ∀ i : ℤ,
      Module.Finite A ((DerivedCategory.homologyFunctor (ModuleCat.{a} A) i).obj
        (DerivedCategory.Plus.ι.obj (DSMap.RG A X f))) ∧
      (N < i → IsZero ((DerivedCategory.homologyFunctor (ModuleCat.{a} A) i).obj
        (DerivedCategory.Plus.ι.obj (DSMap.RG A X f)))) := by
  obtain ⟨hfin, hvan⟩ := chartCech_finite_vanishing (A := A) (n := n) (M := M) ℳ
  refine ⟨(n : ℤ), fun i => ⟨?_, ?_⟩⟩
  · by_cases hi : 0 ≤ i
    · have hq : ((i.toNat : ℕ) : ℤ) = i := Int.toNat_of_nonneg hi
      rw [← hq]
      obtain ⟨e⟩ := h i.toNat
      exact Module.Finite.of_surjective e.inv.hom
        ((ModuleCat.epi_iff_surjective e.inv).mp inferInstance)
    · haveI : Subsingleton ((DerivedCategory.homologyFunctor (ModuleCat.{a} A) i).obj
          (DerivedCategory.Plus.ι.obj (DSMap.RG A X f))) :=
        (ModuleCat.isZero_iff_subsingleton).mp (RG_homology_isZero_of_neg A X f i (by omega))
      exact module_finite_of_subsingleton
  · intro hi
    have hi0 : 0 ≤ i := by omega
    have hq : ((i.toNat : ℕ) : ℤ) = i := Int.toNat_of_nonneg hi0
    have : n < i.toNat := by omega
    rw [← hq]
    obtain ⟨e⟩ := h i.toNat
    exact IsZero.of_iso (hvan i.toNat this) e

end Work.DSCOH
