import Mathlib
import Submission.Work.StemsB.WangSequenceShiftedR

/-!
# The odd step of the `C2` layer: the vanishing of the Wang total space from the two spots

*(Area STEMS.  See `Submission/Work/Stems/C2ODD_PLAN.md` for the role of this file in the
`K(ℤ,n)` computation and `Submission/Work/StemsB/E4_CORRECTION.md` for the statement of E4.)*

The blueprint (`Submission/Work/Drive/SERRE_BLUEPRINT.md` §2, "odd step") proves that the
`n`-connected cover `Eₙ` of `Sⁿ` is rationally acyclic by running the **Wang sequence** of the
fibration `Eₙ → Sⁿ` (whose fibre is `ΩLₙ ≅_ℚ K(ℤ,n-1)`) and using that the transgression is a
derivation on the polynomial algebra `H^*(ΩLₙ;ℚ) = ℚ[x]`.

This file isolates the part of that argument which is **formal** once the Wang sequence is exact,
and which therefore needs no multiplicativity input at all.  In the shifted Wang sequence

  `H^{n+b}(X) --α--> H^{n+b}(F) --θ--> H^{n+1}(F) --β--> H^{n+b+1}(X)`,

`H^{n+b+1}(X)` is an extension of `ker θ_{n}` by `coker θ_{n}`, so it vanishes as soon as `θ_n` is
both surjective and injective:

* `θ_n` surjective  ⟹ `β_n = 0`  (`Work.StemsB.wangCohShiftExact₃R`: `ker β_n = im θ_n`);
* `θ_{n+1}` injective ⟹ `α_{n+b+1} = 0`  (`Work.StemsB.wangCohShiftExact₂R` at `n+1`).

The two statements are recorded below (`Work.Stems.isZero_wangTotal_of_zeroMaps`); for a fibre which
is a rational sphere below degree `2b-2` (`b ≥ 2`) both hypotheses are *automatic*, which gives the
bounded form `Work.Stems.isZero_wangTotal` used by the `C2` odd step in range.  The degrees beyond
`2b-2` are where the fibre's second non-vanishing degree (`x²`, of degree `2(b-1)`) appears; there
`θ` is multiplication by a non-zero scalar on a one-dimensional space, and the two hypotheses are
exactly the multiplicativity `θ(x^k) = k x^{k-1} θ(x)` — see `C2ODD_PLAN.md` §3.
-/

open CategoryTheory CategoryTheory.Limits

namespace Work.Stems

noncomputable section

variable {R : Type} [CommRing R]

/-! ## The third exactness spot of the Wang sequence -/

/-- **Exactness of the shifted Wang sequence at the total space.**  Together with
`Work.StemsB.wangCohShiftExact₂R` (exactness at `H^{n+b}(F)`) and
`Work.StemsB.wangCohShiftExact₃R` (exactness at `H^{n+1}(F)`) this is the third, and last, spot of
the long exact Wang sequence.

`Work.StemsB.wangCohShiftExact₁R` proves the corresponding statement for the *unshifted*
identification `τ : H^{n+m}(X,A) ≅ H^n(F)`; the identification used below is the shifted one
`τS : H^{(n-1)+m+1}(X,A) ≅ H^n(F)`, which is the one the geometric data of
`Work.StemsB.wangSphereE4Rat` provides.  The proof is the same: exactness at `H^{n+m}(X)` is
`Work.Cohomology.pair_exact₂`, transported along the two isomorphisms by the coefficient-generic
`Work.StemsB.functionExact_conj_R`. -/
theorem wangCohShiftExactTotal (X : TopCat) (A : Set X) (Fsp : TopCat) (m : ℕ)
    (γ : ∀ k : ℕ, Work.Cohomology.singularCohomology R k (TopCat.of A) ≅
      Work.Cohomology.singularCohomology R k Fsp)
    (τS : ∀ n : ℕ, (Work.Cohomology.relComplex R X A).homology (n + m + 1) ≅
      Work.Cohomology.singularCohomology R (n + 1) Fsp) (n : ℕ) :
    Function.Exact (Work.StemsB.wangCohShiftβSR R X A Fsp m τS n)
      (Work.StemsB.wangCohShiftαR R X A Fsp m γ (n + m + 1)) := by
  have h := (ShortComplex.ShortExact.moduleCat_exact_iff_function_exact _).mp
    (Work.Cohomology.pair_exact₂ R X A (n + m + 1))
  exact Work.StemsB.functionExact_conj_R R _ _ (τS n) (Iso.refl _) (γ (n + m + 1)) h

/-! ## The vanishing of the total space from the two spots -/

/-- **A module squeezed between two vanishing maps vanishes.**  If `f : M ⟶ N`, `g : N ⟶ P` are
exact (`Set.range f = {y | g y = 0}`), the range of `f` is a subsingleton and `g` is the zero map,
then `N` is a subsingleton: the exactness gives `N = Set.range f` (because `g = 0`). -/
theorem subsingleton_of_exact_of_range {M N P : ModuleCat R} (f : M ⟶ N) (g : N ⟶ P)
    (h : Function.Exact f g) (hf : Subsingleton (Set.range ⇑f)) (hg : ∀ x, g x = 0) :
    Subsingleton N := by
  refine ⟨fun x y => ?_⟩
  have hx : x ∈ Set.range ⇑f := (h x).mp (hg x)
  have hy : y ∈ Set.range ⇑f := (h y).mp (hg y)
  exact congrArg Subtype.val (Subsingleton.elim (⟨x, hx⟩ : Set.range ⇑f) ⟨y, hy⟩)

/-- The range of a map whose source is a subsingleton is a subsingleton. -/
theorem subsingleton_range {M N : ModuleCat R} (f : M ⟶ N) (hM : Subsingleton M) :
    Subsingleton (Set.range ⇑f) := by
  refine Subsingleton.intro fun x y => Subtype.ext ?_
  obtain ⟨a, ha⟩ := x.2
  obtain ⟨b, hb⟩ := y.2
  rw [← ha, ← hb, Subsingleton.elim a b]

/-- **The odd step of the `C2` layer, from the two spots of the Wang sequence.**  If at the degree
`n` the two maps of the shifted Wang sequence adjacent to the total space are zero
(`β_n = 0`, `α_{n+b+1} = 0`), then `H^{n+b+1}(X) = 0`.

The two hypotheses are exactly what the multiplicativity of the transgression provides: `β_n = 0`
is `θ_n` surjective (exactness `Work.StemsB.wangCohShiftExact₃R`, its kernel is `im θ_n`), and
`α_{n+b+1} = 0` is `θ_{n+1}` injective (exactness `Work.StemsB.wangCohShiftExact₂R` at `n+1`). -/
theorem isZero_wangTotal_of_zeroMaps (X : TopCat) (A : Set X) (Fsp : TopCat) (b : ℕ)
    (γ : ∀ k : ℕ, Work.Cohomology.singularCohomology R k (TopCat.of A) ≅
      Work.Cohomology.singularCohomology R k Fsp)
    (τS : ∀ n : ℕ, (Work.Cohomology.relComplex R X A).homology (n + b + 1) ≅
      Work.Cohomology.singularCohomology R (n + 1) Fsp)
    (n : ℕ)
    (hβ : ∀ c, (Work.StemsB.wangCohShiftβSR R X A Fsp b τS n) c = 0)
    (hα : ∀ x, (Work.StemsB.wangCohShiftαR R X A Fsp b γ (n + b + 1)) x = 0) :
    Subsingleton (Work.Cohomology.singularCohomology R (n + b + 1) X) := by
  have hαβ : Function.Exact (Work.StemsB.wangCohShiftβSR R X A Fsp b τS n)
      (Work.StemsB.wangCohShiftαR R X A Fsp b γ (n + b + 1)) :=
    wangCohShiftExactTotal X A Fsp b γ τS n
  refine subsingleton_of_exact_of_range _ _ hαβ ?_ hα
  refine Subsingleton.intro fun x y => Subtype.ext ?_
  obtain ⟨a, ha⟩ := x.2
  obtain ⟨c, hc⟩ := y.2
  rw [← ha, ← hc, hβ a, hβ c]

/-- **The vanishing of the total space of the Wang sequence in the range covered by exactness
alone.**  For `b ≥ 2`, if the fibre `Fsp` has vanishing cohomology in degrees `0 < t ≤ T` with
`t ≠ b-1`, then the total space `X` has vanishing cohomology in degrees
`b+1 ≤ t ≤ min T (2b-2)`.

For `t` in that range the two maps adjacent to `H^t(X)` have a *vanishing* module at their far end:
the source of `β_{t-b-1}` is `H^{t-b}(F)` and the target of `α_t` is `H^t(F)`, and both degrees are
`≤ T` and `≠ b-1` (here `b-1 ∤ t` holds because `t ≤ 2b-2` and `t ≥ b+1`).  This is the "odd step"
of the blueprint's `C2` below the degrees where the fibre's second non-vanishing degree (`x²`)
appears; see the module docstring. -/
theorem isZero_wangTotal (X : TopCat) (A : Set X) (Fsp : TopCat) (b T : ℕ) (hb : 2 ≤ b)
    (γ : ∀ k : ℕ, Work.Cohomology.singularCohomology R k (TopCat.of A) ≅
      Work.Cohomology.singularCohomology R k Fsp)
    (τS : ∀ n : ℕ, (Work.Cohomology.relComplex R X A).homology (n + b + 1) ≅
      Work.Cohomology.singularCohomology R (n + 1) Fsp)
    (hfib : ∀ t : ℕ, 0 < t → t ≤ T → t ≠ b - 1 →
      Subsingleton (Work.Cohomology.singularCohomology R t Fsp)) :
    ∀ t : ℕ, b + 1 ≤ t → t ≤ T → t ≤ 2 * b - 2 →
      Subsingleton (Work.Cohomology.singularCohomology R t X) := by
  intro t ht1 htT ht2
  -- the two vanishing modules of the fibre, at the degrees of the two neighbouring terms
  have hM : Subsingleton (Work.Cohomology.singularCohomology R ((t - b - 1) + 1) Fsp) :=
    hfib ((t - b - 1) + 1) (by omega) (by omega) (by omega)
  have hP : Subsingleton (Work.Cohomology.singularCohomology R ((t - b - 1) + b + 1) Fsp) :=
    hfib ((t - b - 1) + b + 1) (by omega) (by omega) (by omega)
  have key : (t - b - 1) + b + 1 = t := by omega
  rw [← key]
  exact isZero_wangTotal_of_zeroMaps X A Fsp b γ τS (t - b - 1)
    (fun c => by rw [Subsingleton.elim c 0, map_zero])
    (fun x => Subsingleton.elim _ _)

end

end Work.Stems
