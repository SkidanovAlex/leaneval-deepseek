import Mathlib
import Submission.Lib.Unif2.Work.Mori.torsionFree_abelianization_planeDomain
import Submission.Lib.Unif2.Work.Mori.torsionFree_abelianization_riemannSurface

/-!
# Torsion-freeness of `H₁` from a torsion-free exhaustion

The single *bookkeeping* step of the "abelian half of Johansson/Stallings": if a topological space
`X` is exhausted by an increasing sequence of subsets `K : ℕ → Set X` whose interiors cover `X`, and
each piece `↥(K n)` has torsion-free `H₁ = π₁ᵃᵇ` (at the base point `x`), then `H₁(X)` is
torsion-free.

This is the general form of the assembly performed (for the polyomino exhaustion of a plane domain)
in `Submission/Work/Mori/torsionFree_abelianization_planeDomain.lean`, but stated for an *abstract*
exhaustion: the geometric content is isolated in the two hypotheses

* the exhaustion itself: `Monotone K`, `⋃ n, interior (K n) = univ`, `x ∈ K n` for all `n`;
* the piece hypothesis: `∀ n, IsMulTorsionFree (Abelianization (FundamentalGroup ↥(K n) ⟨x, _⟩))`.

The two ingredients used are

* `Work.Mori.exists_forall_mem_of_exhaustion` (cofinality of the exhaustion: every continuous map
  from a compact space into `X` lands in a single member — applied to loops and to homotopies of
  loops);
* `Work.Mori.isMulTorsionFree_abelianization_of_directedColimit'` (torsion-freeness passes to
  filtered colimits of groups, with the element-wise cofinality hypothesis).

Both are proved and sorry-free.  Consequently the whole mathematical content of the torsion-freeness
of `H₁` of a connected non-compact Riemann surface is concentrated in the *existence* of such an
exhaustion (for which the disc tiling `Commons.Topology.Surface.exists_locallyFinite_disk_tiling`
supplies the candidate pieces).

## Elaboration note

The types are written out concretely (`FundamentalGroup ↥(K n) ⟨x, hx n⟩`) rather than through a
`let`-bound abbreviation `H n`.  This is *not* cosmetic: `FundamentalGroup X x` is
`@[reducible] def … := CategoryTheory.End _`, so with an abstract `H` the instance search for
`Monoid (H n)` can land on `CategoryTheory.End.monoid` in one place and on the `Group`-derived
`Monoid` in another; the resulting definitional-equality check on `MonoidHom` structures made the
final application of the colimit lemma time out (`whnf` heartbeat exhaustion).  Writing the concrete
type expression everywhere makes the instance search deterministic.
-/

set_option maxHeartbeats 800000

open scoped unitInterval

namespace Work.Mori

open Set

universe u

/-- Torsion-freeness is transported along a multiplicative equivalence. -/
theorem isMulTorsionFree_of_mulEquiv {M N : Type*} [Monoid M] [Monoid N] (e : M ≃* N)
    (h : IsMulTorsionFree M) : IsMulTorsionFree N := by
  refine ⟨fun n hn => ?_⟩
  intro a b hab
  have hab' : e.symm a ^ n = e.symm b ^ n := by
    have h1 := congrArg e.symm hab
    simpa using h1
  exact e.symm.injective (IsMulTorsionFree.pow_left_injective hn hab')

/-- The class of a lifted loop under the inclusion of a set into the ambient space. -/
theorem mapOfEq_mk_lift_univ {X : Type*} [TopologicalSpace X] (K : Set X) {x : X} (hxK : x ∈ K)
    (γ : Path (⟨x, hxK⟩ : ↥K) ⟨x, hxK⟩) (γ₀ : Path x x)
    (hγ : ∀ t, ((γ t : ↥K) : X) = γ₀ t) :
    FundamentalGroup.mapOfEq
        (⟨Subtype.val, continuous_subtype_val⟩ : C(↥K, X)) (rfl : (⟨x, hxK⟩ : ↥K).1 = x)
        (Path.Homotopic.Quotient.mk γ) = Path.Homotopic.Quotient.mk γ₀ := by
  rw [FundamentalGroup.mapOfEq_apply, Path.Homotopic.Quotient.cast_rfl_rfl,
    ← Path.Homotopic.Quotient.mk_map]
  congr 1
  exact Path.ext (funext fun t => hγ t)

/-- **Torsion-freeness of `H₁` passes from the members of an exhaustion to the whole space.** -/
theorem isMulTorsionFree_abelianization_of_exhaustion {X : Type u} [TopologicalSpace X]
    (x : X) (K : ℕ → Set X) (hmono : Monotone K)
    (hint : ⋃ n, interior (K n) = Set.univ) (hx : ∀ n, x ∈ K n)
    (htf : ∀ n, IsMulTorsionFree (Abelianization (FundamentalGroup ↥(K n) ⟨x, hx n⟩))) :
    IsMulTorsionFree (Abelianization (FundamentalGroup X x)) := by
  classical
  let incKL : (k l : ℕ) → k ≤ l → C(↥(K k), ↥(K l)) := fun k l hkl =>
    ⟨fun y => ⟨y.1, hmono hkl y.2⟩, continuous_subtype_val.subtype_mk _⟩
  let incKX : (k : ℕ) → C(↥(K k), X) := fun _ =>
    ⟨Subtype.val, continuous_subtype_val⟩
  let psi : (k l : ℕ) → k ≤ l →
      FundamentalGroup ↥(K k) ⟨x, hx k⟩ →* FundamentalGroup ↥(K l) ⟨x, hx l⟩ :=
    fun k l hkl => FundamentalGroup.mapOfEq (incKL k l hkl) (Subtype.ext rfl)
  let phi : (k : ℕ) → FundamentalGroup ↥(K k) ⟨x, hx k⟩ →* FundamentalGroup X x :=
    fun k => FundamentalGroup.mapOfEq (incKX k) rfl
  have hphipsi : ∀ {k l : ℕ} (hkl : k ≤ l), (phi l).comp (psi k l hkl) = phi k := by
    intro k l hkl
    dsimp only [psi, phi, incKL, incKX]
    rw [mapOfEq_comp']
    refine mapOfEq_congr_map ?_ rfl rfl
    ext y
    rfl
  have hpsi : ∀ {k m l : ℕ} (hkm : k ≤ m) (hml : m ≤ l),
      (psi m l hml).comp (psi k m hkm) = psi k l (hkm.trans hml) := by
    intro k m l hkm hml
    dsimp only [psi, incKL]
    rw [mapOfEq_comp']
    refine mapOfEq_congr_map ?_ (Subtype.ext rfl) (Subtype.ext rfl)
    ext y
    rfl
  have hsurj : ∀ g : FundamentalGroup X x,
      ∃ k, ∃ y : FundamentalGroup ↥(K k) ⟨x, hx k⟩, phi k y = g := by
    intro g
    obtain ⟨γ, hγ⟩ := Quotient.exists_rep g
    obtain ⟨k, hk⟩ := exists_forall_mem_of_exhaustion (X := X) (Y := Set.Icc (0 : ℝ) 1)
      K hmono hint γ
    let γ' : Path (⟨x, hx k⟩ : ↥(K k)) ⟨x, hx k⟩ :=
      { toFun := fun t => ⟨γ t, hk t⟩
        continuous_toFun := γ.continuous.subtype_mk _
        source' := by
          apply Subtype.ext
          show (γ 0 : X) = x
          rw [γ.source]
        target' := by
          apply Subtype.ext
          show (γ 1 : X) = x
          rw [γ.target] }
    refine ⟨k, Path.Homotopic.Quotient.mk γ', ?_⟩
    have hkey := mapOfEq_mk_lift_univ (X := X) (K := K k) (hxK := hx k) (x := x) γ' γ
      (fun t => rfl)
    exact hkey.trans hγ
  have hker : ∀ (k : ℕ) (y : FundamentalGroup ↥(K k) ⟨x, hx k⟩), phi k y = 1 →
      ∃ l, ∃ hkl : k ≤ l, psi k l hkl y = 1 := by
    intro k y hy
    obtain ⟨γ, rfl⟩ := Quotient.exists_rep y
    have h1 : FundamentalGroup.map (incKX k) ⟨x, hx k⟩
        (Path.Homotopic.Quotient.mk γ : FundamentalGroup ↥(K k) ⟨x, hx k⟩) = 1 :=
      (mapOfEq_eq_one_iff (incKX k) rfl _).mp hy
    have hhom : (γ.map (f := fun z => (incKX k) z) (incKX k).continuous).Homotopic
        (Path.refl x) := by
      have h1b : (Path.Homotopic.Quotient.mk γ : FundamentalGroup ↥(K k) ⟨x, hx k⟩).map
          (incKX k) = (1 : FundamentalGroup X x) := by
        rw [← FundamentalGroup.map_apply]
        exact h1
      have h3 : Path.Homotopic.Quotient.mk (γ.map (f := fun z => (incKX k) z)
            (incKX k).continuous) = Path.Homotopic.Quotient.mk (Path.refl x) := by
        rw [Path.Homotopic.Quotient.mk_map]
        exact h1b
      exact (Path.Homotopic.Quotient.eq).mp h3
    set F := hhom.some with hFdef
    obtain ⟨m, hm⟩ := exists_forall_mem_of_exhaustion (X := X)
      (Y := Set.Icc (0 : ℝ) 1 × Set.Icc (0 : ℝ) 1) K hmono hint F
    set l : ℕ := max k m with hl
    have hkl : k ≤ l := le_max_left _ _
    have hml : m ≤ l := le_max_right _ _
    have hmemF : ∀ q : Set.Icc (0 : ℝ) 1 × Set.Icc (0 : ℝ) 1, F q ∈ K l :=
      fun q => hmono hml (hm q)
    have hlift : Path.Homotopic.Quotient.mk (γ.map (f := fun y => (incKL k l hkl) y)
          (incKL k l hkl).continuous)
        = Path.Homotopic.Quotient.mk (Path.refl ((incKL k l hkl) ⟨x, hx k⟩)) := by
      refine (Path.Homotopic.Quotient.eq).mpr ?_
      refine ⟨{ toFun := fun q => ⟨F q, hmemF q⟩
                continuous_toFun := F.continuous.subtype_mk _
                map_zero_left := ?_
                map_one_left := ?_
                prop' := ?_ }⟩
      · intro t
        apply Subtype.ext
        show (F (0, t) : X) = ((γ t : ↥(K k)) : X)
        exact F.map_zero_left t
      · intro t
        apply Subtype.ext
        show (F (1, t) : X) = x
        exact F.map_one_left t
      · intro s t ht
        rcases ht with rfl | rfl
        · simp
          exact Subtype.ext rfl
        · simp
          exact Subtype.ext rfl
    refine ⟨l, hkl, ?_⟩
    refine (mapOfEq_eq_one_iff (incKL k l hkl) (Subtype.ext rfl)
      (Path.Homotopic.Quotient.mk γ : FundamentalGroup ↥(K k) ⟨x, hx k⟩)).mpr ?_
    have hgoal : (Path.Homotopic.Quotient.mk γ : FundamentalGroup ↥(K k) ⟨x, hx k⟩).map
        (incKL k l hkl) = Path.Homotopic.Quotient.mk
          (Path.refl ((incKL k l hkl) ⟨x, hx k⟩)) := by
      rw [← Path.Homotopic.Quotient.mk_map]
      exact hlift
    exact hgoal
  exact isMulTorsionFree_abelianization_of_directedColimit'
    (G := FundamentalGroup X x)
    (H := fun n => FundamentalGroup ↥(K n) ⟨x, hx n⟩)
    psi phi hphipsi hpsi hsurj hker htf

end Work.Mori
