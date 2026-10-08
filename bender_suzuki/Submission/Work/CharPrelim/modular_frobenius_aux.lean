import Mathlib

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

/-!
# The modular form of Feit--Thompson 3.16 (iii)

`Work.CharPrelim.modular_frobenius_finrank` states the "modular form of Feit--Thompson 3.16 (iii)"
used in the proof of FT 4.6: if `G = K ⋊ E` is a Frobenius group whose kernel `K` contains the
centralizer of each of its non-identity elements, `p` is a prime not dividing `|G|`, and `ρ` is a
representation of `G` over `ZMod p` whose restriction to `K` is non-trivial, then for every
`E₀ ≤ E` the fixed space of `E₀` on the representation space has `ZMod p`-dimension at least
`[E : E₀]`.

The proof follows the classical argument, transported to characteristic `p`:

* it suffices to treat the case of an irreducible representation over an algebraically closed
  field, into which everything base changes (`finrank` of fixed spaces is preserved);
* for an irreducible representation `V` with `V^K = 0`, an irreducible `K`-submodule `U ≤ V` is
  chosen; the key point is that no conjugate `gU` (`g ∈ E`) is isomorphic to `U` — this is the
  "fixed point free" form of 3.16 (iii), proved by the trace argument of
  `no_isFixedPointFree_semilinear_bijective` (Burnside's density theorem, the vanishing of
  `∑_{k ∈ K} ρ k` on a representation with `V^K = 0`, and non-degeneracy of the trace pairing);
* hence the `|E|` submodules `gU` (`g ∈ E`) are pairwise non-isomorphic simple `K`-modules, so
  `V = ⨁_{g ∈ E} gU`; the group `E` permutes these summands regularly, which gives
  `dim V^{E₀} = [E : E₀] · dim U ≥ [E : E₀]`.
-/

set_option linter.style.haveILetI false
set_option maxHeartbeats 1000000

noncomputable section

open Classical
open scoped MonoidAlgebra Pointwise

namespace Work.CharPrelim

/-! ### Non-degeneracy of the trace pairing -/

/-- The trace pairing `(X, Y) ↦ tr (X * Y)` on the endomorphism algebra of a finite-dimensional
vector space over a field is non-degenerate. -/
theorem trace_form_nondegenerate {K : Type*} [Field K] {V : Type*} [AddCommGroup V] [Module K V]
    [FiniteDimensional K V] {B : V →ₗ[K] V}
    (h : ∀ X : V →ₗ[K] V, LinearMap.trace K V (X * B) = 0) : B = 0 := by
  classical
  let b := Module.finBasis K V
  have hM : ∀ x : Matrix (Fin (Module.finrank K V)) (Fin (Module.finrank K V)) K,
      (x * LinearMap.toMatrix b b B).trace = 0 := by
    intro x
    have hx : x = LinearMap.toMatrix b b (Matrix.toLin b b x) :=
      (LinearMap.toMatrix_toLin b b x).symm
    rw [hx, ← LinearMap.toMatrix_mul, ← LinearMap.trace_eq_matrix_trace K b]
    exact h _
  have hzero : LinearMap.toMatrix b b B = 0 := by
    rw [Matrix.ext_iff_trace_mul_left]
    intro x
    rw [hM x]; simp
  exact (LinearMap.toMatrix b b).injective (by simp [hzero])

/-! ### Burnside's density theorem over an algebraically closed field -/

/-- Burnside/Jacobson density: for an irreducible finite-dimensional representation of a finite
group over an algebraically closed field, the linear span of the operators `ρ g` is the whole
endomorphism algebra. -/
theorem span_range_eq_top_of_isIrreducible {K G V : Type*} [Field K] [IsAlgClosed K] [Group G]
    [Fintype G] [AddCommGroup V] [Module K V] [FiniteDimensional K V]
    (ρ : Representation K G V) [ρ.IsIrreducible] :
    Submodule.span K (Set.range (fun g : G => (ρ g : V →ₗ[K] V))) = ⊤ := by
  have hbij : Function.Bijective (algebraMap K (Module.End K[G] ρ.asModule)) :=
    IsSimpleModule.algebraMap_end_bijective_of_isAlgClosed K
  have hfinD : Module.Finite (Module.End K[G] ρ.asModule) ρ.asModule := by
    obtain ⟨S, hS⟩ := (Module.Finite.fg_top (R := K) (M := ρ.asModule))
    refine ⟨S, ?_⟩
    apply SetLike.coe_injective
    rw [Submodule.coe_span_eq_span_of_surjective (R := K) (A := Module.End K[G] ρ.asModule)
      hbij.surjective (↑S : Set ρ.asModule), hS]
    rfl
  have hsurjMod : Function.Surjective
      (Module.toModuleEnd K (S := K[G]) ρ.asModule) := by
    have hsurjD : Function.Surjective
        (Module.toModuleEnd (Module.End K[G] ρ.asModule) (S := K[G]) ρ.asModule) :=
      Module.Finite.toModuleEnd_moduleEnd_surjective
    intro T
    let f : Module.End (Module.End K[G] ρ.asModule) ρ.asModule :=
      { toFun := ⇑T
        map_add' := T.map_add
        map_smul' := by
          intro d m
          obtain ⟨c, rfl⟩ := hbij.surjective d
          simp only [algebraMap_smul]
          exact T.map_smul c m }
    obtain ⟨r, hr⟩ := hsurjD f
    refine ⟨r, ?_⟩
    apply LinearMap.ext
    intro m
    have h1 : ((Module.toModuleEnd (Module.End K[G] ρ.asModule) ρ.asModule) r) m = T m := by
      rw [hr]; rfl
    simpa [Module.toModuleEnd_apply, DistribSMul.toLinearMap_apply] using h1
  have hsurj : Function.Surjective (ρ.asAlgebraHom) := by
    intro T
    let e := ρ.asModuleEquiv
    let S : Module.End K ρ.asModule := e.symm.toLinearMap.comp (T.comp e.toLinearMap)
    obtain ⟨r, hr⟩ := hsurjMod S
    refine ⟨r, ?_⟩
    apply LinearMap.ext
    intro v
    have h1 : (r • (e.symm v) : ρ.asModule) = e.symm (T v) := by
      have h2 := congrArg (fun f : Module.End K ρ.asModule => f (e.symm v)) hr
      simp only [Module.toModuleEnd_apply, DistribSMul.toLinearMap_apply, S, LinearMap.comp_apply,
        LinearEquiv.coe_coe, LinearEquiv.apply_symm_apply] at h2
      exact h2
    have h3 : e (r • e.symm v) = T v := by
      rw [h1, LinearEquiv.apply_symm_apply]
    have key : (ρ.asAlgebraHom r) v = e (r • e.symm v) := by
      rw [Representation.asModuleEquiv_map_smul ρ r (e.symm v), LinearEquiv.apply_symm_apply]
    rw [key, h3]
  have hspan_of : Submodule.span K (Set.range (fun g : G => MonoidAlgebra.of K G g)) = ⊤ := by
    refine le_antisymm le_top ?_
    intro f _
    exact Submodule.span_mono (Set.image_subset_range _ _) (MonoidAlgebra.mem_span_support_coeff f)
  refine le_antisymm le_top ?_
  intro T _
  obtain ⟨r, hr⟩ := hsurj T
  rw [← hr]
  have hr' : r ∈ Submodule.span K (Set.range fun g : G => MonoidAlgebra.of K G g) := by
    rw [hspan_of]; trivial
  have hQ : Set.range (fun g : G => MonoidAlgebra.of K G g) ⊆
      Submodule.comap (ρ.asAlgebraHom).toLinearMap
        (Submodule.span K (Set.range (fun g : G => ρ g))) := by
    rintro x ⟨g, rfl⟩
    exact Submodule.subset_span ⟨g, (Representation.asAlgebraHom_of ρ g).symm⟩
  exact (Submodule.span_le.mpr hQ) hr'

/-! ### The key step of 3.16 (iii) -/

/-- **The modular form of the key step of Feit--Thompson 3.16 (iii).**  Over an algebraically
closed field `K` of prime characteristic `p` not dividing `|H|`, an irreducible representation
of a finite group `H` without nonzero fixed vector admits no bijective semilinear endomorphism
twisted by a fixed-point-free automorphism `σ` of `H`. -/
theorem no_isFixedPointFree_semilinear_bijective {K : Type*} [Field K] [IsAlgClosed K] {p : ℕ}
    [Fact p.Prime] [CharP K p] {H U : Type*} [Group H] [Fintype H] [AddCommGroup U] [Module K U]
    [FiniteDimensional K U] (ρ : Representation K H U) [ρ.IsIrreducible]
    (hnt : ρ.invariants = ⊥) (hcop : ¬ p ∣ Nat.card H) (σ : H ≃* H)
    (hfpf : ∀ h : H, σ h = h → h = 1) (ψ : U →ₗ[K] U) (hψ : Function.Bijective ψ)
    (hψσ : ∀ (h : H) (u : U), ψ (ρ h u) = ρ (σ h) (ψ u)) : False := by
  classical
  have hsum_mem : ∀ u : U, (∑ h : H, (ρ h : U →ₗ[K] U)) u ∈ ρ.invariants := by
    intro u
    rw [Representation.mem_invariants]
    intro h₀
    have hmul : (ρ h₀ : U →ₗ[K] U) * (∑ h : H, (ρ h : U →ₗ[K] U))
        = ∑ h : H, (ρ h : U →ₗ[K] U) := by
      rw [Finset.mul_sum]
      trans ∑ h : H, (ρ (h₀ * h) : U →ₗ[K] U)
      · exact Finset.sum_congr rfl (fun h _ => by rw [← map_mul])
      · exact Equiv.sum_comp (Equiv.mulLeft h₀) (fun h : H => (ρ h : U →ₗ[K] U))
    simpa only [Module.End.mul_apply] using congrArg (fun f : U →ₗ[K] U => f u) hmul
  have hS : (∑ h : H, (ρ h : U →ₗ[K] U)) = 0 := by
    apply LinearMap.ext
    intro u
    have h := hsum_mem u
    rw [hnt, Submodule.mem_bot] at h
    simpa using h
  have hinj : Function.Injective (fun h : H => h * (σ h)⁻¹) := by
    intro a b hab
    have hab' : a * (σ a)⁻¹ = b * (σ b)⁻¹ := hab
    have h2 : b⁻¹ * (a * (σ a)⁻¹) = (σ b)⁻¹ := by
      calc b⁻¹ * (a * (σ a)⁻¹) = b⁻¹ * (b * (σ b)⁻¹) := by rw [hab']
        _ = (σ b)⁻¹ := by group
    rw [← mul_assoc] at h2
    have h3 : b⁻¹ * a = (σ b)⁻¹ * σ a := by
      calc b⁻¹ * a = b⁻¹ * a * ((σ a)⁻¹ * σ a) := by group
        _ = (b⁻¹ * a * (σ a)⁻¹) * σ a := by group
        _ = (σ b)⁻¹ * σ a := by rw [h2]
    have h1 : b⁻¹ * a = σ (b⁻¹ * a) := by
      refine h3.trans ?_
      exact ((map_mul σ b⁻¹ a).trans (by rw [MulEquiv.map_inv])).symm
    have h1' : b⁻¹ * a = 1 := hfpf (b⁻¹ * a) h1.symm
    calc a = b * (b⁻¹ * a) := by group
      _ = b * 1 := by rw [h1']
      _ = b := by rw [mul_one]
  have hop : ∀ h : H, ψ * (ρ h) = (ρ (σ h)) * ψ := fun h => LinearMap.ext (hψσ h)
  have htr : ∀ y : H, LinearMap.trace K U ((ρ y) * ψ) = LinearMap.trace K U ψ := by
    intro y
    obtain ⟨g, hg⟩ := Finite.surjective_of_injective hinj y
    rw [← hg]
    change LinearMap.trace K U ((ρ (g * (σ g)⁻¹)) * ψ) = LinearMap.trace K U ψ
    have h1 : ψ * (ρ g⁻¹) = (ρ ((σ g)⁻¹)) * ψ := by
      have h := hop g⁻¹
      rwa [MulEquiv.map_inv] at h
    have hconj : (ρ g) * (ψ * (ρ g⁻¹)) = (ρ (g * (σ g)⁻¹)) * ψ := by
      calc (ρ g) * (ψ * (ρ g⁻¹)) = (ρ g) * ((ρ ((σ g)⁻¹)) * ψ) := by rw [h1]
        _ = ((ρ g) * (ρ ((σ g)⁻¹))) * ψ := by rw [mul_assoc]
        _ = (ρ (g * (σ g)⁻¹)) * ψ := by rw [← map_mul]
    have htr1 : LinearMap.trace K U ((ρ g) * (ψ * (ρ g⁻¹)))
        = LinearMap.trace K U (ψ * (ρ g⁻¹) * (ρ g)) := LinearMap.trace_mul_comm K _ _
    have htr2 : LinearMap.trace K U (ψ * (ρ g⁻¹) * (ρ g)) = LinearMap.trace K U ψ := by
      rw [mul_assoc, ← map_mul, inv_mul_cancel, map_one, mul_one]
    rw [hconj] at htr1
    exact htr1.trans htr2
  let W : Submodule K (U →ₗ[K] U) :=
    Submodule.span K (Set.range (fun h : H => ((ρ h : U →ₗ[K] U) - 1)))
  have hcard : (Fintype.card H : K) ≠ 0 := by
    rw [← Nat.card_eq_fintype_card]
    exact fun h0 => hcop ((CharP.cast_eq_zero_iff K p (Nat.card H)).mp h0)
  have h1W : (1 : U →ₗ[K] U) ∈ W := by
    have hsum : (∑ h : H, ((ρ h : U →ₗ[K] U) - 1))
        = -((Fintype.card H : K) • (1 : U →ₗ[K] U)) := by
      rw [Finset.sum_sub_distrib, hS, Finset.sum_const, Finset.card_univ,
        ← Nat.cast_smul_eq_nsmul K, zero_sub]
    have hmem : (∑ h : H, ((ρ h : U →ₗ[K] U) - 1)) ∈ W :=
      Submodule.sum_mem _ (fun h _ => Submodule.subset_span ⟨h, rfl⟩)
    have hsm : ((-(Fintype.card H : K))⁻¹) • (∑ h : H, ((ρ h : U →ₗ[K] U) - 1)) ∈ W :=
      W.smul_mem _ hmem
    have hval : ((-(Fintype.card H : K))⁻¹) • (∑ h : H, ((ρ h : U →ₗ[K] U) - 1))
        = (1 : U →ₗ[K] U) := by
      rw [hsum, smul_neg, smul_smul, inv_neg, neg_mul, neg_smul, inv_mul_cancel₀ hcard,
        one_smul, neg_neg]
    rw [hval] at hsm
    exact hsm
  have hWtop : W = ⊤ := by
    have hspan : Submodule.span K (Set.range (fun h : H => (ρ h : U →ₗ[K] U))) = ⊤ :=
      span_range_eq_top_of_isIrreducible ρ
    refine le_antisymm le_top ?_
    rw [← hspan, Submodule.span_le]
    rintro _ ⟨h, rfl⟩
    change (ρ h : U →ₗ[K] U) ∈ W
    have hdecomp : (ρ h : U →ₗ[K] U) = ((ρ h : U →ₗ[K] U) - 1) + 1 := by abel
    rw [hdecomp]
    exact Submodule.add_mem W (Submodule.subset_span ⟨h, rfl⟩) h1W
  have htr0 : ∀ h : H, LinearMap.trace K U ((((ρ h : U →ₗ[K] U) - 1)).comp ψ) = 0 := by
    intro h
    rw [← Module.End.mul_eq_comp, sub_mul, one_mul, map_sub, htr h, sub_self]
  let Lfun : (U →ₗ[K] U) →ₗ[K] K :=
    { toFun := fun X => LinearMap.trace K U (X.comp ψ)
      map_add' := fun X Y => by rw [LinearMap.add_comp, map_add]
      map_smul' := fun c X => by
        show LinearMap.trace K U ((c • X).comp ψ) = c • LinearMap.trace K U (X.comp ψ)
        rw [LinearMap.smul_comp, map_smul] }
  have hzero : ∀ X : U →ₗ[K] U, LinearMap.trace K U (X * ψ) = 0 := by
    have hW : W ≤ LinearMap.ker Lfun := by
      rw [Submodule.span_le]
      rintro z ⟨h, rfl⟩
      change LinearMap.trace K U (((ρ h : U →ₗ[K] U) - 1).comp ψ) = 0
      exact htr0 h
    intro X
    have hmem : X ∈ LinearMap.ker Lfun := hW (by rw [hWtop]; trivial)
    have hmem' : LinearMap.trace K U (X.comp ψ) = 0 := hmem
    rwa [Module.End.mul_eq_comp]
  have hψ0 : ψ = 0 := trace_form_nondegenerate hzero
  have hne : ψ ≠ 0 := by
    intro h0
    haveI : IsSimpleModule K[H] ρ.asModule := inferInstance
    have hnt' : Nontrivial U := IsSimpleModule.nontrivial K[H] ρ.asModule
    obtain ⟨u, hu⟩ := exists_ne (0 : U)
    have : ψ u = 0 := by rw [h0]; rfl
    refine hu (hψ.1 ?_)
    rw [this, map_zero]
  exact hne hψ0


section BaseChange

open scoped TensorProduct

variable {F L : Type*} [Field F] [Field L] [Algebra F L]

namespace Representation

/-- Base change of a representation along a field extension: `g` acts by `id ⊗ ρ g`. -/
noncomputable def baseChange {G V : Type*} [Group G] [AddCommGroup V] [Module F V]
    (ρ : Representation F G V) : Representation L G (L ⊗[F] V) where
  toFun g := (LinearMap.baseChange L (ρ g) : (L ⊗[F] V) →ₗ[L] (L ⊗[F] V))
  map_one' := by simpa using LinearMap.baseChange_id (R := F) (A := L) (M := V)
  map_mul' g h := by
    rw [map_mul, Module.End.mul_eq_comp, LinearMap.baseChange_comp, Module.End.mul_eq_comp]

theorem baseChange_apply {G V : Type*} [Group G] [AddCommGroup V] [Module F V]
    (ρ : Representation F G V) (g : G) :
    baseChange (L := L) ρ g = (LinearMap.baseChange L (ρ g) : (L ⊗[F] V) →ₗ[L] (L ⊗[F] V)) := rfl

end Representation

end BaseChange

end Work.CharPrelim
