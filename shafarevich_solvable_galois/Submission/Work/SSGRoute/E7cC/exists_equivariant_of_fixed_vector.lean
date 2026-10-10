import Mathlib.Algebra.Field.ZMod
import Mathlib.NumberTheory.NumberField.InfinitePlace.Basic
import Mathlib.RingTheory.DedekindDomain.Ideal.Lemmas
import Submission.Work.SSGRoute.Sha2Lib.indLevelDatum
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Hom_{G₀}(Ind_{D_w}^{G₀} 𝔽_p, V) ≅ V^{D_w}`: the fixed vector furnishes the equivariant map

`Ind_{D_w}^{G₀} 𝔽_p` (`G₀ = Gal(K/k)`, `D_w = decompK w ≤ G₀`) is realised in
`Work.SSGRoute.E7cC.indDatum` as the `𝔽_p`-valued functions on `G₀` that are invariant under
*right* multiplication by `D_w`, with the left-translation action `Work.SSGRoute.Sha2Lib.indDatumSmul`
and the basis vector `Work.SSGRoute.E7cC.indDatumBase` (the indicator of `D_w`).

The general (purely group-theoretic) statement proved here as
`Work.SSGRoute.E7cC.exists_equivariant_generic` is the *induction adjunction* in the easy
direction: for a finite group `G`, a subgroup `D ≤ G`, a commutative ring `R`, an `R`-module `V`,
a representation `ρ : G →* V →ₗ[R] V` and a vector `v ∈ V` fixed by `D`, there is an additive
map `Φ` out of the functions `G → R` which is `G`-equivariant on the `D`-right-invariant functions
and sends the indicator of `D` to `v`.  It is given by the explicit coset sum

    `Φ F = ∑_{x : G ⧸ D} F (Quotient.out x) • ρ (Quotient.out x) v`,

which is well defined on the `D`-right-invariant functions (a change of representative by
`δ ∈ D` changes `ρ (out x) v` by `ρ δ v = v`), `G`-equivariant (reindexing the coset space by
`x ↦ σ • x`), and sends the indicator of `D` to `v` (only the trivial coset contributes, and its
representative lies in `D`).  No normality of `D` is needed — precisely the point recorded in the
convention note of `Submission/Work/SSGRoute/E7cC/inducedLevelDatum.lean`.

Specialising `G = Gal(K/k)`, `D = decompK w`, `R = 𝔽_p` and restricting to the submodule
`↥(indDatum p k K w)` yields the target `exists_equivariant_of_fixed_vector`: every vector fixed
by the decomposition group `D_w` is the image of the basis vector `indDatumBase` under a
`Gal(K/k)`-equivariant additive map `Ind_{D_w}^{G₀} 𝔽_p → V`.
-/

open scoped BigOperators

namespace Work.SSGRoute.E7cC

/-- **Induction adjunction, easy direction.**  For a finite group `G`, a subgroup `D ≤ G`, a
commutative ring `R`, an `R`-module `V`, a representation `ρ : G →* V →ₗ[R] V` and a `D`-fixed
vector `v ∈ V`, there is an additive map `Φ : (G → R) →+ V` which is `G`-equivariant on the
functions invariant under right multiplication by `D` (with the left-translation action
`F ↦ (γ ↦ F (σ⁻¹ γ))`) and which sends the indicator of `D` to `v`.

The map is the explicit coset sum `Φ F = ∑_{x : G ⧸ D} F (out x) • ρ (out x) v` over a set of
representatives of the left cosets `γ • D`. -/
theorem exists_equivariant_generic
    (G : Type) [Group G] [Fintype G] (D : Subgroup G)
    (R V : Type) [CommRing R] [AddCommGroup V] [Module R V]
    (ρ : G →* (V →ₗ[R] V)) (v : V)
    (hv : ∀ δ ∈ D, ρ δ v = v) :
    ∃ Φ : (G → R) →+ V,
      (∀ (σ : G) (F : G → R), (∀ δ ∈ D, ∀ γ, F (γ * δ) = F γ) →
        Φ (fun γ => F (σ⁻¹ * γ)) = ρ σ (Φ F)) ∧
      Φ (Set.indicator (D : Set G) (fun _ => 1)) = v := by
  classical
  -- two elements of the same coset differ by right multiplication by an element of `D`
  have hrel : ∀ {a b : G}, (QuotientGroup.mk a : G ⧸ D) = QuotientGroup.mk b →
      ∃ δ ∈ D, b = a * δ := by
    intro a b h
    exact ⟨a⁻¹ * b, QuotientGroup.leftRel_apply.mp (Quotient.exact' h), by group⟩
  -- a right-`D`-invariant function is constant on cosets
  have hFval : ∀ {F : G → R}, (∀ δ ∈ D, ∀ γ, F (γ * δ) = F γ) →
      ∀ {a b : G}, (QuotientGroup.mk a : G ⧸ D) = QuotientGroup.mk b → F a = F b := by
    intro F hF a b h
    obtain ⟨δ, hδ, hb⟩ := hrel h
    rw [hb, hF δ hδ]
  -- likewise `ρ (·) v` is constant on cosets
  have hρval : ∀ {a b : G}, (QuotientGroup.mk a : G ⧸ D) = QuotientGroup.mk b →
      ρ a v = ρ b v := by
    intro a b h
    obtain ⟨δ, hδ, hb⟩ := hrel h
    rw [hb, map_mul, Module.End.mul_apply, hv δ hδ]
  have hout : ∀ x : G ⧸ D, (QuotientGroup.mk (Quotient.out x) : G ⧸ D) = x :=
    fun x => QuotientGroup.out_eq' x
  have hmk_smul : ∀ (σ : G) (x : G ⧸ D),
      (QuotientGroup.mk (σ * Quotient.out x) : G ⧸ D) = σ • x := by
    intro σ x
    exact MulAction.Quotient.mk_smul_out (H := D) σ x
  have hout_inv : ∀ (σ : G) (x : G ⧸ D),
      (QuotientGroup.mk (σ⁻¹ * Quotient.out (σ • x)) : G ⧸ D) = x := by
    intro σ x
    rw [hmk_smul σ⁻¹ (σ • x)]
    simp
  let Φ : (G → R) →+ V :=
    { toFun := fun F => ∑ x : G ⧸ D, F (Quotient.out x) • ρ (Quotient.out x) v
      map_zero' := by simp
      map_add' := by
        intro F F'
        simp only [Pi.add_apply, add_smul, Finset.sum_add_distrib] }
  refine ⟨Φ, ?_, ?_⟩
  · intro σ F hF
    show (∑ x : G ⧸ D, F (σ⁻¹ * Quotient.out x) • ρ (Quotient.out x) v)
        = (ρ σ) (∑ x : G ⧸ D, F (Quotient.out x) • ρ (Quotient.out x) v)
    -- reindex the coset space by `x ↦ σ • x`
    have step1 : (∑ x : G ⧸ D, F (σ⁻¹ * Quotient.out x) • ρ (Quotient.out x) v)
        = ∑ x : G ⧸ D,
            F (σ⁻¹ * Quotient.out (σ • x)) • ρ (Quotient.out (σ • x)) v := by
      have h := (Equiv.sum_comp (MulAction.toPerm σ : Equiv.Perm (G ⧸ D))
        (fun y => F (σ⁻¹ * Quotient.out y) • ρ (Quotient.out y) v)).symm
      simpa only [MulAction.toPerm_apply] using h
    trans (∑ x : G ⧸ D, F (σ⁻¹ * Quotient.out (σ • x)) • ρ (Quotient.out (σ • x)) v)
    · exact step1
    trans (∑ x : G ⧸ D, F (Quotient.out x) • ρ (σ * Quotient.out x) v)
    · refine Finset.sum_congr rfl fun x _ => ?_
      rw [hFval (F := F) hF (a := σ⁻¹ * Quotient.out (σ • x)) (b := Quotient.out x)
          ((hout_inv σ x).trans (hout x).symm),
        hρval (a := Quotient.out (σ • x)) (b := σ * Quotient.out x)
          ((hout (σ • x)).trans (hmk_smul σ x).symm)]
    · rw [map_sum]
      refine (Finset.sum_congr rfl fun x _ => ?_).symm
      rw [map_smul, ← Module.End.mul_apply, ← map_mul]
  · show (∑ x : G ⧸ D,
      (Set.indicator (D : Set G) (fun _ => (1 : R))) (Quotient.out x) • ρ (Quotient.out x) v) = v
    -- only the coset of `1` contributes, and its representative lies in `D`
    let x₀ : G ⧸ D := QuotientGroup.mk 1
    have hx₀ : Quotient.out x₀ ∈ D := by
      have h1 : (Quotient.out x₀)⁻¹ * (1 : G) ∈ D :=
        QuotientGroup.leftRel_apply.mp (Quotient.exact' (QuotientGroup.out_eq' x₀))
      simpa using D.inv_mem h1
    have hsingle : ∀ b ∈ (Finset.univ : Finset (G ⧸ D)), b ≠ x₀ →
        (Set.indicator (D : Set G) (fun _ => (1 : R))) (Quotient.out b)
          • ρ (Quotient.out b) v = 0 := by
      intro b _ hb
      have hbD : Quotient.out b ∉ D := by
        intro hmem
        have h1 : (QuotientGroup.mk (Quotient.out b) : G ⧸ D) = QuotientGroup.mk (1 : G) := by
          rw [QuotientGroup.eq]
          simpa using hmem
        exact hb (by rw [← QuotientGroup.out_eq' b]; exact h1)
      rw [Set.indicator_of_notMem hbD, zero_smul]
    have key : (∑ x : G ⧸ D,
        (Set.indicator (D : Set G) (fun _ => (1 : R))) (Quotient.out x)
          • ρ (Quotient.out x) v)
        = (Set.indicator (D : Set G) (fun _ => (1 : R))) (Quotient.out x₀)
            • ρ (Quotient.out x₀) v :=
      Finset.sum_eq_single (s := (Finset.univ : Finset (G ⧸ D)))
        (f := fun x => (Set.indicator (D : Set G) (fun _ => (1 : R))) (Quotient.out x)
          • ρ (Quotient.out x) v) x₀ hsingle (fun h => absurd (Finset.mem_univ x₀) h)
    rw [key, Set.indicator_of_mem hx₀, one_smul]
    exact hv _ hx₀

/-- **The fixed vector of the decomposition group is the image of the basis vector of the induced
module.**  A vector `v` of a `𝔽_p`-module `V` on which the decomposition group
`SSGRoute.PTExt.decompK w` of the place `w` acts trivially extends to a `Gal(K/k)`-equivariant
additive map `Ind_{D_w}^{G₀} 𝔽_p → V` (`G₀ = Gal(K/k)`) sending the basis vector `indDatumBase`
(the indicator of `D_w`) to `v`.

This is `exists_equivariant_generic` for `G = Gal(K/k)`, `D = decompK w`, `R = 𝔽_p`, restricted to
the submodule `↥(indDatum p k K w)` of `D_w`-right-invariant functions. -/
theorem exists_equivariant_of_fixed_vector
    (p : ℕ) [Fact p.Prime] (k K : Type) [Field k] [NumberField k] [Field K] [NumberField K]
    [Algebra k K] [FiniteDimensional k K] [IsGalois k K]
    (w : NK.GlobalCFT.Place K)
    (V : Type) [AddCommGroup V] [Module (ZMod p) V]
    (ρ : (K ≃ₐ[k] K) →* (V →ₗ[ZMod p] V))
    (v : V)
    (hv : ∀ δ : K ≃ₐ[k] K, δ ∈ SSGRoute.PTExt.decompK (k := k) (K := K) w → ρ δ v = v) :
    ∃ φ : ↥(Work.SSGRoute.E7cC.indDatum p k K w) →+ V,
      (∀ (σ : K ≃ₐ[k] K) (f : ↥(Work.SSGRoute.E7cC.indDatum p k K w)),
        φ (Work.SSGRoute.Sha2Lib.indDatumSmul p k K w σ f) = ρ σ (φ f)) ∧
      φ (Work.SSGRoute.E7cC.indDatumBase p k K w) = v := by
  classical
  obtain ⟨Φ, hΦeq, hΦbase⟩ := exists_equivariant_generic (G := K ≃ₐ[k] K)
    (SSGRoute.PTExt.decompK (k := k) (K := K) w) (ZMod p) V ρ v hv
  refine ⟨Φ.comp (Work.SSGRoute.E7cC.indDatum p k K w).subtype, ?_, ?_⟩
  · -- equivariance: `indDatumSmul` is the left-translation action
    intro σ f
    have h1 : ((Work.SSGRoute.Sha2Lib.indDatumSmul p k K w σ f :
            ↥(Work.SSGRoute.E7cC.indDatum p k K w)) : (K ≃ₐ[k] K) → ZMod p)
        = fun γ => (f : (K ≃ₐ[k] K) → ZMod p) (σ⁻¹ * γ) :=
      Work.SSGRoute.Sha2Lib.indDatumSmul_coe p k K w σ f
    simp only [AddMonoidHom.comp_apply, AddSubgroup.subtype_apply]
    rw [h1]
    exact hΦeq σ (f : (K ≃ₐ[k] K) → ZMod p) f.2
  · -- the basis vector `indDatumBase` is literally the indicator of `decompK w`
    have h2 : ((Work.SSGRoute.E7cC.indDatumBase p k K w :
            ↥(Work.SSGRoute.E7cC.indDatum p k K w)) : (K ≃ₐ[k] K) → ZMod p)
        = Set.indicator ((SSGRoute.PTExt.decompK (k := k) (K := K) w :
            Subgroup (K ≃ₐ[k] K)) : Set (K ≃ₐ[k] K)) (fun _ => (1 : ZMod p)) := by
      funext γ
      change (if γ ∈ SSGRoute.PTExt.decompK (k := k) (K := K) w then (1 : ZMod p) else 0)
        = Set.indicator ((SSGRoute.PTExt.decompK (k := k) (K := K) w :
            Subgroup (K ≃ₐ[k] K)) : Set (K ≃ₐ[k] K)) (fun _ => (1 : ZMod p)) γ
      rw [Set.indicator_apply]
      by_cases h : γ ∈ SSGRoute.PTExt.decompK (k := k) (K := K) w
      · rw [if_pos h]
        exact (if_pos h).symm
      · rw [if_neg h]
        exact (if_neg h).symm
    simp only [AddMonoidHom.comp_apply, AddSubgroup.subtype_apply]
    rw [h2]
    exact hΦbase

end Work.SSGRoute.E7cC
