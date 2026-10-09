import Mathlib
import Submission.NK.GlobalCFTdeep.Basic
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# Herbrand's lemma for a finite cyclic group: `|Ĥ⁰| = |Ĥ¹|`

For a finite cyclic group `G` and a *finite* `ℤ[G]`-module `M`, the two Tate cohomology
groups `Ĥ⁰(G, M)` and `Ĥ¹(G, M)` have the same order.  This is the classical statement that
the Herbrand quotient of a finite module is `1`.

Writing `σ` for a generator of `G`, `N = ∑_{g : G} ρ(g)` for the norm and `d = ρ(σ) - 1`
for the difference map, the two groups are

* `Ĥ⁰(G, M) = M^G ⧸ N(M) = ker d ⧸ im N`,
* `Ĥ¹(G, M) = ker N ⧸ im d`   (via `H¹(G, M) ≅ ker N ⧸ im d` for a cyclic group, which is the
  odd case of the two-periodicity of group cohomology),

and the equality of orders is the cancellation

`|ker d| · |im d| = |M| = |ker N| · |im N|`.

Everything is first proved for an arbitrary commutative base ring `k`, to avoid the diamond
between the two `ℤ`-module structures on `M.V` occurring for `k = ℤ`
(`Rep.hV2` versus `AddCommGroup.toIntModule`); the statement over `ℤ` is then obtained by
specialisation, where no `LinearMap` bookkeeping is elaborated anymore.
-/

namespace NK.GlobalCFTdeep.Herbrand

open CategoryTheory

section Helpers

variable {k : Type*} [Ring k] {M : Type*} [AddCommGroup M] [Module k M]

/-- Transporting a quotient `p ⧸ (r ∩ p)` along an equality `p = p'` of submodules. -/
lemma quotientEquivOfSubmoduleEq {p p' : Submodule k M} (h : p = p') (r : Submodule k M) :
    Nonempty ((p ⧸ r.comap p.subtype) ≃ₗ[k] (p' ⧸ r.comap p'.subtype)) :=
  ⟨Submodule.Quotient.equiv _ _ (LinearEquiv.ofEq p p' h) (by subst h; simp)⟩

/-- The homology of a short complex of modules is the kernel of `g` modulo the image of `f`. -/
lemma shortComplex_H_iso (S : ShortComplex (ModuleCat k)) :
    Nonempty (S.moduleCatLeftHomologyData.H ≃ₗ[k]
      (LinearMap.ker S.g.hom ⧸ (LinearMap.range S.f.hom).comap (LinearMap.ker S.g.hom).subtype)) := by
  have h : LinearMap.range S.moduleCatToCycles
      = (LinearMap.range S.f.hom).comap (LinearMap.ker S.g.hom).subtype :=
    LinearMap.range_codRestrict _ _ _
  exact ⟨Submodule.quotEquivOfEq _ _ h⟩

end Helpers

/-- **Herbrand's lemma, linear-algebra form.**  For a finite module `V` over a commutative ring
`k` and endomorphisms `d, N` with `N ∘ d = 0` and `d ∘ N = 0`, the quotients `ker d ⧸ im N`
and `ker N ⧸ im d` have the same cardinality. -/
theorem natCard_ker_quot_range_eq {k : Type*} [CommRing k] {V : Type*} [AddCommGroup V]
    [Module k V] [Finite V] (d N : V →ₗ[k] V) (hdN : N.comp d = 0) (hNd : d.comp N = 0) :
    Nat.card (LinearMap.ker d ⧸ (LinearMap.range N).comap (LinearMap.ker d).subtype) =
      Nat.card (LinearMap.ker N ⧸ (LinearMap.range d).comap (LinearMap.ker N).subtype) := by
  have hRN : LinearMap.range N ≤ LinearMap.ker d := by
    rintro x ⟨y, rfl⟩
    rw [LinearMap.mem_ker, ← LinearMap.comp_apply, hNd]
    rfl
  have hRd : LinearMap.range d ≤ LinearMap.ker N := by
    rintro x ⟨y, rfl⟩
    rw [LinearMap.mem_ker, ← LinearMap.comp_apply, hdN]
    rfl
  have hcardN : Nat.card ↥((LinearMap.range N).comap (LinearMap.ker d).subtype)
      = Nat.card ↥(LinearMap.range N) :=
    Nat.card_congr (Submodule.comapSubtypeEquivOfLe hRN).toEquiv
  have hcardd : Nat.card ↥((LinearMap.range d).comap (LinearMap.ker N).subtype)
      = Nat.card ↥(LinearMap.range d) :=
    Nat.card_congr (Submodule.comapSubtypeEquivOfLe hRd).toEquiv
  have hVd : Nat.card V = Nat.card ↥(LinearMap.ker d) * Nat.card ↥(LinearMap.range d) := by
    have h := Submodule.card_eq_card_quotient_mul_card (LinearMap.ker d)
    rw [Nat.card_congr (LinearMap.quotKerEquivRange d).toEquiv] at h
    exact h
  have hVN : Nat.card V = Nat.card ↥(LinearMap.ker N) * Nat.card ↥(LinearMap.range N) := by
    have h := Submodule.card_eq_card_quotient_mul_card (LinearMap.ker N)
    rw [Nat.card_congr (LinearMap.quotKerEquivRange N).toEquiv] at h
    exact h
  have hI1 : Nat.card ↥(LinearMap.ker d) =
      Nat.card (LinearMap.ker d ⧸ (LinearMap.range N).comap (LinearMap.ker d).subtype)
        * Nat.card ↥(LinearMap.range N) := by
    have h := Submodule.card_eq_card_quotient_mul_card
      ((LinearMap.range N).comap (LinearMap.ker d).subtype)
    rw [hcardN] at h
    exact h.trans (Nat.mul_comm _ _)
  have hI2 : Nat.card ↥(LinearMap.ker N) =
      Nat.card (LinearMap.ker N ⧸ (LinearMap.range d).comap (LinearMap.ker N).subtype)
        * Nat.card ↥(LinearMap.range d) := by
    have h := Submodule.card_eq_card_quotient_mul_card
      ((LinearMap.range d).comap (LinearMap.ker N).subtype)
    rw [hcardd] at h
    exact h.trans (Nat.mul_comm _ _)
  have hEpos : 0 < Nat.card ↥(LinearMap.range N) := Nat.card_pos
  have hBpos : 0 < Nat.card ↥(LinearMap.range d) := Nat.card_pos
  have hpos : 0 < Nat.card ↥(LinearMap.range N) * Nat.card ↥(LinearMap.range d) :=
    Nat.mul_pos hEpos hBpos
  have key :
      Nat.card (LinearMap.ker d ⧸ (LinearMap.range N).comap (LinearMap.ker d).subtype) *
          (Nat.card ↥(LinearMap.range N) * Nat.card ↥(LinearMap.range d)) =
      Nat.card (LinearMap.ker N ⧸ (LinearMap.range d).comap (LinearMap.ker N).subtype) *
          (Nat.card ↥(LinearMap.range N) * Nat.card ↥(LinearMap.range d)) := by
    calc
      Nat.card (LinearMap.ker d ⧸ (LinearMap.range N).comap (LinearMap.ker d).subtype) *
          (Nat.card ↥(LinearMap.range N) * Nat.card ↥(LinearMap.range d))
          = (Nat.card (LinearMap.ker d ⧸ (LinearMap.range N).comap (LinearMap.ker d).subtype)
              * Nat.card ↥(LinearMap.range N)) * Nat.card ↥(LinearMap.range d) :=
            (Nat.mul_assoc _ _ _).symm
      _ = Nat.card ↥(LinearMap.ker d) * Nat.card ↥(LinearMap.range d) := by rw [← hI1]
      _ = Nat.card V := by rw [← hVd]
      _ = Nat.card ↥(LinearMap.ker N) * Nat.card ↥(LinearMap.range N) := hVN
      _ = (Nat.card (LinearMap.ker N ⧸ (LinearMap.range d).comap (LinearMap.ker N).subtype)
              * Nat.card ↥(LinearMap.range d)) * Nat.card ↥(LinearMap.range N) := by rw [← hI2]
      _ = Nat.card (LinearMap.ker N ⧸ (LinearMap.range d).comap (LinearMap.ker N).subtype) *
              (Nat.card ↥(LinearMap.range d) * Nat.card ↥(LinearMap.range N)) := Nat.mul_assoc _ _ _
      _ = Nat.card (LinearMap.ker N ⧸ (LinearMap.range d).comap (LinearMap.ker N).subtype) *
              (Nat.card ↥(LinearMap.range N) * Nat.card ↥(LinearMap.range d)) := by
            rw [Nat.mul_comm (Nat.card ↥(LinearMap.range d)) (Nat.card ↥(LinearMap.range N))]
  exact Nat.mul_right_cancel hpos key

/-- **Degree zero.**  For a finite cyclic group generated by `g`, the zeroth Tate cohomology of
`A` is `ker (ρ(g) - 1) ⧸ im N`, the quotient of the invariants by the image of the norm. -/
theorem natCard_tateCohomology_zero_eq {k G : Type} [CommRing k] [Group G] [Fintype G]
    (A : Rep k G) [Finite A.V] (g : G) (hg : ∀ x, x ∈ Subgroup.zpowers g) :
    Nat.card (tateCohomology A 0) =
      Nat.card (LinearMap.ker (A.ρ g - 1) ⧸
        (LinearMap.range A.ρ.norm).comap (LinearMap.ker (A.ρ g - 1)).subtype) := by
  obtain ⟨e⟩ := Commons.RepresentationTheory.GroupCohomology.tateCohomology_zero_iso_general
    (G := G) (V := A.V) A.ρ
  have hker : A.ρ.invariants = LinearMap.ker (A.ρ g - 1) := by
    ext x
    rw [LinearMap.mem_ker]
    rw [show (A.ρ g - 1) x = (A.ρ g) x - x from rfl]
    rw [sub_eq_zero]
    exact (Representation.mem_invariants_iff_of_forall_mem_zpowers A.ρ g hg x)
  obtain ⟨e2⟩ := quotientEquivOfSubmoduleEq hker (LinearMap.range A.ρ.norm)
  exact Nat.card_congr (e.toEquiv.trans e2.toEquiv)

/-- **Degree one.**  For a finite cyclic group generated by `g`, the first Tate cohomology of `A`
has the cardinality of `ker N ⧸ im (ρ(g) - 1)`.  This is the odd case of the usual
two-periodicity `H¹(G, A) ≅ ker N ⧸ im (ρ(g) - 1)` for a cyclic group, combined with
`Ĥ¹ ≅ H¹`. -/
theorem natCard_tateCohomology_one_eq {k G : Type} [CommRing k] [CommGroup G] [Fintype G]
    (A : Rep k G) [Finite A.V] (g : G) (hg : ∀ x, x ∈ Subgroup.zpowers g) :
    Nat.card (tateCohomology A 1) =
      Nat.card (LinearMap.ker A.ρ.norm ⧸
        (LinearMap.range (A.ρ g - 1)).comap (LinearMap.ker A.ρ.norm).subtype) := by
  have e1 := (TateCohomology.isoGroupCohomology (R := k) (G := G) 1).app A
  have e2 := Rep.FiniteCyclicGroup.groupCohomologyIsoOdd A g hg 1 (by norm_num)
  have e3 := ShortComplex.moduleCatHomologyIso (Rep.FiniteCyclicGroup.subCompNormHom A g)
  obtain ⟨e4⟩ := shortComplex_H_iso (Rep.FiniteCyclicGroup.subCompNormHom A g)
  have h1 : Nat.card (tateCohomology A 1) = Nat.card (groupCohomology A 1) :=
    Nat.card_congr e1.toLinearEquiv.toEquiv
  have h2 : Nat.card (groupCohomology A 1)
      = Nat.card ((Rep.FiniteCyclicGroup.subCompNormHom A g).moduleCatLeftHomologyData.H) :=
    Nat.card_congr (e2.toLinearEquiv.trans e3.toLinearEquiv).toEquiv
  have h3 : Nat.card ((Rep.FiniteCyclicGroup.subCompNormHom A g).moduleCatLeftHomologyData.H) =
      Nat.card (LinearMap.ker A.ρ.norm ⧸
        (LinearMap.range (A.ρ g - 1)).comap (LinearMap.ker A.ρ.norm).subtype) :=
    Nat.card_congr e4.toEquiv
  exact h1.trans (h2.trans h3)

/-- Herbrand's lemma for a finite cyclic group and an arbitrary commutative base ring. -/
theorem hZero_eq_hOne_rep {k G : Type} [CommRing k] [CommGroup G] [Fintype G]
    (A : Rep k G) [Finite A.V] (g : G) (hg : ∀ x, x ∈ Subgroup.zpowers g) :
    Nat.card (tateCohomology A 0) = Nat.card (tateCohomology A 1) := by
  have hdN : (A.ρ.norm).comp (A.ρ g - 1) = 0 := by
    ext v
    simp only [LinearMap.comp_apply, LinearMap.sub_apply, Module.End.one_apply, map_sub,
      Representation.norm_self_apply, sub_self, LinearMap.zero_apply]
  have hNd : (A.ρ g - 1).comp (A.ρ.norm) = 0 := by
    ext v
    simp only [LinearMap.comp_apply, LinearMap.sub_apply, Module.End.one_apply,
      Representation.self_norm_apply, sub_self, LinearMap.zero_apply]
  have h0 := natCard_tateCohomology_zero_eq (A := A) g hg
  have h1 := natCard_tateCohomology_one_eq (A := A) g hg
  have hH := natCard_ker_quot_range_eq (k := k) (V := A.V) (A.ρ g - 1) A.ρ.norm hdN hNd
  rw [h0, h1]
  exact hH

/-- **Herbrand's lemma.**  For a finite cyclic group `G` and a finite `ℤ[G]`-module `M` the two
Tate cohomology groups `Ĥ⁰(G, M)` and `Ĥ¹(G, M)` have the same order. -/
theorem hZero_eq_hOne_of_finite {G : Type} [CommGroup G] [Fintype G] [IsCyclic G]
    (M : Rep ℤ G) [Finite M.V] :
    Nat.card (tateCohomology M 0) = Nat.card (tateCohomology M 1) := by
  obtain ⟨g, hg⟩ := IsCyclic.exists_generator (α := G)
  exact hZero_eq_hOne_rep (k := ℤ) (A := M) g hg

end NK.GlobalCFTdeep.Herbrand
