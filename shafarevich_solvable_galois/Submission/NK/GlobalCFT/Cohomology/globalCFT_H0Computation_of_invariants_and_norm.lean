import Mathlib
import Submission.NK.GlobalCFT.Cohomology
import Submission.NK.GlobalCFT.Cohomology.globalCFT_H0Computation_of_invariants
import Submission.NK.GlobalCFT.NormGroup.Basic
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace NK.GlobalCFT.Cohomology

/-!
# The `H⁰`-computation from the invariants and the norm

`H0Computation K L` asks for an isomorphism
`C_K ⧸ N_{L/K} C_L ≅ (C_L)^G ⧸ N_{L/K} C_L`.
The companion file `globalCFT_H0Computation_of_invariants` reduces this to the existence of a
multiplicative isomorphism `C_K ≅ (C_L)^G` which carries the norm subgroup `N_{L/K} C_L` onto the
norm subgroup of the invariants.

Here we produce such an isomorphism from the concrete data of *a* map `ψ : C_K →* C_L` which is
injective with image the Galois invariants (`hinv`), and which intertwines the norm on idèle class
groups with the product of the Galois conjugates (`hnorm`).  This is the form in which the
`H⁰`-computation is available from the Galois module structure of `C_L`.
-/

variable {K L : Type*} [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]

/-- The Galois-invariants of `C_L`, read through the representation `IdeleClassGroup.rep`, are
exactly the classes fixed by the Galois action. -/
lemma mem_rep_invariants_iff {q : C[L]} :
    Additive.ofMul q ∈ (IdeleClassGroup.rep K L).ρ.invariants ↔
      ∀ σ : L ≃ₐ[K] L, σ • q = q := by
  change Additive.ofMul q ∈
    (Representation.ofMulDistribMulAction (L ≃ₐ[K] L) (IdeleClassGroup L)).invariants ↔ _
  rw [Representation.mem_invariants]
  constructor
  · intro h σ
    have hσ := h σ
    rwa [Representation.ofMulDistribMulAction_apply_apply, toMul_ofMul] at hσ
  · intro h σ
    rw [Representation.ofMulDistribMulAction_apply_apply, toMul_ofMul, h σ]

/-- The norm of the multiplicity representation `Representation.ofMulDistribMulAction` is the
product of the conjugates.  (A universe-polymorphic restatement of
`Representation.norm_ofMulDistribMulAction_eq`, which is proved for small types.) -/
lemma toMul_norm_ofMulDistribMulAction {G M : Type*} [Group G] [Fintype G] [CommGroup M]
    [MulDistribMulAction G M] (x : Additive M) :
    Additive.toMul ((Representation.ofMulDistribMulAction G M).norm x) =
      ∏ g : G, g • Additive.toMul x := by
  simp [Representation.norm]

variable [FiniteDimensional K L]

/-- The norm of the representation `IdeleClassGroup.rep` is the product of the Galois
conjugates. -/
lemma toMul_rep_norm (w : (IdeleClassGroup.rep K L).V) :
    Additive.toMul ((IdeleClassGroup.rep K L).ρ.norm w) =
      ∏ σ : L ≃ₐ[K] L, σ • (Additive.toMul w : C[L]) :=
  toMul_norm_ofMulDistribMulAction (G := L ≃ₐ[K] L) (M := IdeleClassGroup L) w

/-- The norm of a `Gal(L/K)`-fixed element of `C_L`. -/
lemma rep_norm_ofMul (s : C[L]) :
    (IdeleClassGroup.rep K L).ρ.norm (Additive.ofMul s) =
      Additive.ofMul (∏ σ : L ≃ₐ[K] L, σ • s) := by
  change (Representation.ofMulDistribMulAction (L ≃ₐ[K] L) (IdeleClassGroup L)).norm
      (Additive.ofMul s) = Additive.ofMul (∏ σ : L ≃ₐ[K] L, σ • s)
  simp [Representation.norm]

variable [IsGalois K L]

/-- The map `C_K →* (C_L)^G` obtained from an injective `ψ : C_K →* C_L` whose range is the
Galois invariants. -/
noncomputable def psiToInvariants (ψ : C[K] →* C[L])
    (hinv : ∀ q : C[L], (∀ σ : L ≃ₐ[K] L, σ • q = q) ↔ q ∈ ψ.range) :
    C[K] →* Multiplicative ↥((IdeleClassGroup.rep K L).ρ.invariants) where
  toFun x := Multiplicative.ofAdd ⟨Additive.ofMul (ψ x),
    (mem_rep_invariants_iff (K := K) (L := L)).mpr ((hinv (ψ x)).mpr ⟨x, rfl⟩)⟩
  map_one' := by
    apply Multiplicative.ext
    apply Subtype.ext
    show Additive.ofMul (ψ 1) = 0
    rw [map_one, ofMul_one]
  map_mul' x y := by
    apply Multiplicative.ext
    apply Subtype.ext
    show Additive.ofMul (ψ (x * y)) = Additive.ofMul (ψ x) + Additive.ofMul (ψ y)
    rw [map_mul, ofMul_mul]

/-- An injective `ψ : C_K →* C_L` with range the Galois invariants is an isomorphism
`C_K ≃* (C_L)^G`. -/
noncomputable def psiInvEquiv (ψ : C[K] →* C[L]) (hinj : Function.Injective ψ)
    (hinv : ∀ q : C[L], (∀ σ : L ≃ₐ[K] L, σ • q = q) ↔ q ∈ ψ.range) :
    C[K] ≃* Multiplicative ↥((IdeleClassGroup.rep K L).ρ.invariants) :=
  MulEquiv.ofBijective (psiToInvariants ψ hinv) ⟨fun x y hxy => by
    have h : (psiToInvariants ψ hinv x).toAdd = (psiToInvariants ψ hinv y).toAdd := by
      rw [hxy]
    have h2 : Additive.ofMul (ψ x) = Additive.ofMul (ψ y) :=
      congrArg (Subtype.val :
        ↥((IdeleClassGroup.rep K L).ρ.invariants) → (IdeleClassGroup.rep K L).V) h
    exact hinj (Additive.ofMul.injective h2), fun y => by
    have hfix : ∀ σ : L ≃ₐ[K] L,
        σ • (Additive.toMul (y.toAdd : (IdeleClassGroup.rep K L).V) : C[L]) =
          (Additive.toMul (y.toAdd : (IdeleClassGroup.rep K L).V) : C[L]) :=
      (mem_rep_invariants_iff (K := K) (L := L)).mp (y.toAdd).property
    obtain ⟨x, hx⟩ := (hinv _).mp hfix
    refine ⟨x, ?_⟩
    apply Multiplicative.ext
    apply Subtype.ext
    show Additive.ofMul (ψ x) = (y.toAdd : (IdeleClassGroup.rep K L).V)
    rw [hx]
    exact ofMul_toMul _⟩

/-- Under `hnorm`, an element `ψ q` of the invariants lies in the range of the norm of `C_L` if
and only if `q` lies in the norm subgroup `N_{L/K} C_L`. -/
lemma ofMul_mem_range_norm_iff (ψ : C[K] →* C[L]) (hinj : Function.Injective ψ)
    (hnorm : ∀ y : C[L], ψ (IdeleClassGroup.normClassHom K L y) = ∏ σ : L ≃ₐ[K] L, σ • y)
    (q : C[K]) :
    Additive.ofMul (ψ q) ∈ LinearMap.range ((IdeleClassGroup.rep K L).ρ.norm) ↔
      q ∈ Idele.normClassSubgroup K L := by
  constructor
  · rintro ⟨w, hw⟩
    rw [Idele.mem_normClassSubgroup]
    refine ⟨Additive.toMul w, hinj ?_⟩
    have h2 : (∏ σ : L ≃ₐ[K] L, σ • (Additive.toMul w : C[L])) = ψ q := by
      rw [← toMul_rep_norm (K := K) (L := L) w]
      exact (congrArg (Additive.toMul (α := C[L])) hw).trans (toMul_ofMul (ψ q))
    rw [hnorm (Additive.toMul w), h2]
  · rintro hq
    obtain ⟨y, hy⟩ := Idele.mem_normClassSubgroup.mp hq
    refine ⟨Additive.ofMul y, ?_⟩
    rw [rep_norm_ofMul (K := K) (L := L) y, ← hy, hnorm y]

theorem globalCFT_H0Computation_of_invariants_and_norm {K L : Type*} [Field K] [NumberField K]
    [Field L] [NumberField L] [Algebra K L] [FiniteDimensional K L] [IsGalois K L]
    (ψ : C[K] →* C[L])
    (hinj : Function.Injective ψ)
    (hinv : ∀ q : C[L], (∀ σ : L ≃ₐ[K] L, σ • q = q) ↔ q ∈ ψ.range)
    (hnorm : ∀ y : C[L], ψ (IdeleClassGroup.normClassHom K L y) =
      ∏ σ : L ≃ₐ[K] L, σ • y) :
    H0Computation K L := by
  refine globalCFT_H0Computation_of_invariants (psiInvEquiv ψ hinj hinv) ?_
  intro q
  change Additive.ofMul (ψ q) ∈ LinearMap.range ((IdeleClassGroup.rep K L).ρ.norm) ↔
    q ∈ Idele.normClassSubgroup K L
  exact ofMul_mem_range_norm_iff ψ hinj hnorm q

end NK.GlobalCFT.Cohomology
