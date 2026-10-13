import Mathlib

set_option linter.style.haveILetI false

/-!
# Finiteness of a quotient from coordinate data

Let `Φ : P ≃ₗ[A] (∀ i, Q i)` be an `A`-linear isomorphism, and let `K ⊆ P` be a
submodule which is, through `Φ`, the product `∏ i, Kj i` of submodules `Kj i ⊆ Q i`.
Let `I ⊆ P` be a submodule which, on `K`, is cut out by the coordinate conditions
`Ij i ⊆ Q i`, i.e. for `x ∈ K`, `x ∈ I ↔ ∀ i, (Φ x) i ∈ Ij i`.

If every coordinate quotient `Kj i ⧸ Ij i` is a finite `A`-module, then the quotient
`K ⧸ (K ⊓ I)` is a finite `A`-module.

The proof exhibits the surjective `A`-linear map
`f : K →ₗ ∏ i, (Kj i ⧸ Ij i)`, `x ↦ ((Φ x) i mod Ij i)_i`, computes
`ker f = K ⊓ I`, and applies the first isomorphism theorem. Surjectivity uses that
`K` surjects onto `∏ i, Kj i` via `Φ` (which is exactly the hypothesis `hKiff`).
-/

namespace Work.DSCOH

theorem finite_quot_of_data {A : Type*} [CommRing A] {ι : Type*} [Fintype ι]
    {P : Type*} [AddCommGroup P] [Module A P]
    {Q : ι → Type*} [∀ i, AddCommGroup (Q i)] [∀ i, Module A (Q i)]
    (Φ : P ≃ₗ[A] (∀ i, Q i))
    (K : Submodule A P) (Kj : ∀ i, Submodule A (Q i))
    (I : Submodule A P) (Ij : ∀ i, Submodule A (Q i))
    (hKiff : ∀ x, x ∈ K ↔ Φ x ∈ Submodule.pi Set.univ Kj)
    (hIiff : ∀ x ∈ K, Φ x ∈ Submodule.pi Set.univ Ij ↔ x ∈ I)
    (hfin : ∀ i, Module.Finite A (↥(Kj i) ⧸ Submodule.comap (Kj i).subtype (Ij i))) :
    Module.Finite A (↥K ⧸ Submodule.comap K.subtype I) := by
  -- The `i`-th coordinate of `x : ↥K` lies in `Kj i`, because `Φ x ∈ ∏ i, Kj i`.
  let projF : ∀ i, ↥K → ↥(Kj i) := fun i x =>
    ⟨(Φ (x : P)) i, (Submodule.mem_pi.mp ((hKiff (x : P)).mp x.2)) i (Set.mem_univ i)⟩
  have projF_add : ∀ i, ∀ x y : ↥K, projF i (x + y) = projF i x + projF i y := by
    intro i x y; ext; simp [projF]
  have projF_smul : ∀ i, ∀ (a : A) (x : ↥K), projF i (a • x) = a • projF i x := by
    intro i a x; ext; simp [projF]
  let proj : ∀ i, (↥K) →ₗ[A] (↥(Kj i)) := fun i =>
    { toFun := projF i, map_add' := projF_add i, map_smul' := projF_smul i }
  -- The map whose kernel is `K ⊓ I`: the tuple of coordinates of `Φ x` modulo `Ij`.
  let f : (↥K) →ₗ[A] (∀ i, (↥(Kj i) ⧸ Submodule.comap (Kj i).subtype (Ij i))) :=
    LinearMap.pi (fun i => (Submodule.mkQ (Submodule.comap (Kj i).subtype (Ij i))).comp (proj i))
  -- The `i`-th component of `f x` vanishes exactly when the `i`-th coordinate of `Φ x`
  -- lies in `Ij i`.
  have key : ∀ (x : ↥K) (i : ι), f x i = 0 ↔ (Φ (x : P)) i ∈ Ij i := by
    intro x i
    rw [LinearMap.pi_apply, LinearMap.comp_apply, Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero,
      Submodule.mem_comap]
    rfl
  have hker : LinearMap.ker f = Submodule.comap K.subtype I := by
    ext x
    rw [LinearMap.mem_ker]
    change (f x = 0) ↔ ((x : P) ∈ I)
    constructor
    · intro h
      rw [← hIiff (x : P) x.2, Submodule.mem_pi]
      intro i _
      exact (key x i).mp (by simpa using congrFun h i)
    · intro hx
      funext i
      exact (key x i).mpr ((Submodule.mem_pi.mp ((hIiff (x : P) x.2).mpr hx)) i (Set.mem_univ i))
  -- Surjectivity: `Φ` identifies `K` with `∏ i, Kj i`, and `mkQ` is surjective.
  have hsurj : Function.Surjective f := by
    intro y
    classical
    choose w hw using fun i => Submodule.mkQ_surjective (Submodule.comap (Kj i).subtype (Ij i)) (y i)
    let v : (∀ i, Q i) := fun i => (w i : Q i)
    have hv : v ∈ Submodule.pi Set.univ Kj := Submodule.mem_pi.mpr (fun i _ => (w i).2)
    have hxK : Φ.symm v ∈ K := by rw [hKiff]; simpa using hv
    refine ⟨⟨Φ.symm v, hxK⟩, ?_⟩
    funext i
    rw [LinearMap.pi_apply, LinearMap.comp_apply, Submodule.mkQ_apply]
    have hΦ : Φ (Φ.symm v) = v := Φ.apply_symm_apply v
    have hwi : (proj i ⟨Φ.symm v, hxK⟩ : ↥(Kj i)) = w i := by
      change projF i ⟨Φ.symm v, hxK⟩ = w i
      ext
      simp only [projF]
      rw [hΦ]
    rw [hwi]
    simpa [Submodule.mkQ_apply] using hw i
  -- The target of `f` is finite, being a finite product of finite modules.
  haveI : ∀ i, Module.Finite A (↥(Kj i) ⧸ Submodule.comap (Kj i).subtype (Ij i)) := hfin
  haveI : Module.Finite A (∀ i, (↥(Kj i) ⧸ Submodule.comap (Kj i).subtype (Ij i))) :=
    Module.Finite.pi
  -- First isomorphism theorem.
  have e : (↥K ⧸ Submodule.comap K.subtype I) ≃ₗ[A]
      (∀ i, (↥(Kj i) ⧸ Submodule.comap (Kj i).subtype (Ij i))) :=
    (Submodule.quotEquivOfEq _ _ hker.symm).trans (f.quotKerEquivOfSurjective hsurj)
  exact Module.Finite.equiv e.symm

end Work.DSCOH
