import Mathlib
import Submission.Work.DSAMR.Defs

/-!
# Auxiliary lemmas for the almost-null-homotopy argument (`Work.DSAMR.exists_coaug_lift`)

This file collects the elementary interface lemmas used by the constructions in
`Submission/Work/DSAMR/exists_coaug_lift.lean`:

* `Work.DSAMR.smulLin` — multiplication by an element of `W` as an `A`-linear map (the `A`-structure
  coming from `ψ`),
* `Work.DSAMR.linmem` — if an `A`-linear map takes every element of a basis into a `W`-submodule,
  then it maps everything into it,
* `Work.DSAMR.rho_comm_apply`, `Work.DSAMR.d_d_apply` — elementwise forms of the chain-map and
  differential-square-zero conditions,
* `Work.DSAMR.clause3Z` — clause (3) of `AlmostAcycZ` (stated for `ℤ`-degrees, which is the form in
  which the descending induction consumes it).
-/

open CategoryTheory Limits

namespace Work.DSAMR

universe u

/-! ## Multiplication by an element of `W` -/

section SmulLin

variable {A W M : Type*} [CommRing A] [CommRing W] [AddCommMonoid M] [Module W M] [Module A M]

/-- Multiplication by `c : W` is `A`-linear, provided the `A`-action on `M` factors through `ψ`
(which is the case for `M` in the image of `ModuleCat.restrictScalars ψ`). -/
def smulLin (ψ : A →+* W) (hψ : ∀ (a : A) (m : M), a • m = ψ a • m) (c : W) : M →ₗ[A] M where
  toFun m := c • m
  map_add' m n := smul_add c m n
  map_smul' a m := by
    show c • (a • m) = a • (c • m)
    rw [hψ a m, hψ a (c • m), smul_smul, smul_smul, mul_comm]

@[simp]
theorem smulLin_apply (ψ : A →+* W) (hψ : ∀ (a : A) (m : M), a • m = ψ a • m) (c : W) (m : M) :
    smulLin ψ hψ c m = c • m := rfl

end SmulLin

/-! ## Linearity on the basis -/

/-- If `f : M →ₗ[A] N` maps every element of a basis of `M` into a `W`-submodule `s ⊆ N`, and the
`A`-action on `N` factors through `ψ`, then `f` maps all of `M` into `s`. -/
theorem linmem {A W M N : Type*} [CommRing A] [CommRing W] (ψ : A →+* W)
    [AddCommMonoid M] [Module A M] [AddCommMonoid N] [Module A N] [Module W N]
    (hsmul : ∀ (a : A) (n : N), a • n = ψ a • n)
    {ι : Type*} (b : Module.Basis ι A M) (s : Submodule W N) (f : M →ₗ[A] N)
    (h : ∀ i, f (b i) ∈ s) (x : M) : f x ∈ s := by
  have key : ∀ v : ι →₀ A, f ((Finsupp.linearCombination A b) v) ∈ s := by
    intro v
    refine Finsupp.induction_linear v ?_ ?_ ?_
    · simp
    · intro v w hv hw
      rw [map_add, map_add]
      exact s.add_mem hv hw
    · intro i c
      rw [Finsupp.linearCombination_single, map_smul, hsmul c (f (b i))]
      exact s.smul_mem _ (h i)
  rw [← b.linearCombination_repr x]
  exact key (b.repr x)

/-! ## Elementwise complex identities -/

/-- In a degree in which `P` vanishes, the defining relation of the homotopy holds for any choice
of the map. -/
theorem rel_of_subsingleton {A W : Type u} [CommRing A] [CommRing W] (ψ : A →+* W) (ϖ : ℕ → W)
    {K : CochainComplex (ModuleCat.{u} W) ℤ} {P : CochainComplex (ModuleCat.{u} A) ℤ}
    (ρ : P ⟶ ((ModuleCat.restrictScalars ψ).mapHomologicalComplex
      (ComplexShape.up ℤ)).obj K) (I : Ideal W) {u v : ℤ} (hs : Subsingleton (P.X u))
    (h : P.X u ⟶ (ModuleCat.restrictScalars ψ).obj (K.X v)) (t m : ℕ) (y : P.X u) :
    ϖ t ^ m • (show K.X u from (ρ.f u) y) - (K.d v u).hom (show K.X v from h y)
      ∈ I • (⊤ : Submodule W (K.X u)) := by
  have hy : y = 0 := hs.elim y 0
  subst hy
  have h1 : (show K.X u from (ρ.f u) (0 : P.X u)) = (0 : K.X u) := map_zero _
  have h2 : (show K.X v from h (0 : P.X u)) = (0 : K.X v) := map_zero _
  rw [h1, h2]
  have h3 : (K.d v u).hom (0 : K.X v) = (0 : K.X u) := map_zero _
  rw [h3]
  have h4 : ϖ t ^ m • (0 : K.X u) = (0 : K.X u) := smul_zero _
  rw [h4, sub_zero]
  exact Submodule.zero_mem _

/-- Elementwise form of `HomologicalComplex.Hom.comm` for a chain map into a restricted complex. -/
theorem rho_comm_apply {A W : Type u} [CommRing A] [CommRing W] (ψ : A →+* W)
    {K : CochainComplex (ModuleCat.{u} W) ℤ} {P : CochainComplex (ModuleCat.{u} A) ℤ}
    (ρ : P ⟶ ((ModuleCat.restrictScalars ψ).mapHomologicalComplex
      (ComplexShape.up ℤ)).obj K) (i : ℤ) (x : P.X i) :
    (K.d i (i + 1)).hom (show K.X i from (ρ.f i) x) =
      (show K.X (i + 1) from (ρ.f (i + 1)) ((P.d i (i + 1)).hom x)) := by
  have h := HomologicalComplex.Hom.comm ρ i (i + 1)
  have h2 := congrFun (congrArg (fun f => f.hom)
    (congrArg (fun g => (g : P.X i ⟶ _)) h)) x
  exact h2

/-- Elementwise form of `HomologicalComplex.Hom.comm` in degrees `0 → 1` (the exact index forms
appearing in the degree-`0` endgame of `Work.DSAMR.exists_coaug_lift`). -/
theorem rho_comm_apply_zero {A W : Type u} [CommRing A] [CommRing W] (ψ : A →+* W)
    {K : CochainComplex (ModuleCat.{u} W) ℤ} {P : CochainComplex (ModuleCat.{u} A) ℤ}
    (ρ : P ⟶ ((ModuleCat.restrictScalars ψ).mapHomologicalComplex
      (ComplexShape.up ℤ)).obj K) (x : P.X 0) :
    (K.d 0 1).hom (show K.X 0 from (ρ.f 0) x) =
      (show K.X 1 from (ρ.f 1) ((P.d 0 1).hom x)) :=
  rho_comm_apply ψ ρ 0 x

/-- Elementwise form of `d ∘ d = 0` on `P`. -/
theorem d_d_apply {A : Type u} [CommRing A] (P : CochainComplex (ModuleCat.{u} A) ℤ) (i : ℤ)
    (x : P.X i) : (P.d (i + 1) (i + 2)).hom ((P.d i (i + 1)).hom x) = 0 := by
  have h : (P.d i (i + 1) ≫ P.d (i + 1) (i + 2)) = 0 :=
    HomologicalComplex.d_comp_d P i (i + 1) (i + 2)
  have h2 := congrFun (congrArg (fun f => f.hom) h) x
  exact h2

/-! ## A rewriting identity for the accumulated loss -/

/-- The elementary identity behind the accumulation of one factor of `c` per degree. -/
theorem pow_succ_smul_sub_sub {W M : Type*} [CommRing W] [AddCommGroup M] [Module W M]
    (c : W) (n : ℕ) (x y z : M) :
    c ^ (n + 1) • x - y - c • z = c • (c ^ n • x - z) - y := by
  rw [pow_succ', ← smul_smul, smul_sub]
  abel

/-! ## Clause (3) of `AlmostAcycZ` in `ℤ`-degree form -/

/-- Clause (3) of `Work.DSAMR.AlmostAcycZ`, re-indexed to `ℤ`-degrees: an element of `K^q` (`q ≥ 1`)
whose differential lands in `I·K^{q+1}` becomes an `I·K^q`-coboundary after multiplying by `ϖ k`. -/
theorem clause3Z {W : Type u} [CommRing W] (ϖ : ℕ → W) (I : Ideal W)
    (K : CochainComplex (ModuleCat.{u} W) ℤ)
    (h3 : ∀ (q : ℕ) (z : K.X ((q : ℤ) + 1)),
      (K.d ((q : ℤ) + 1) ((q : ℤ) + 2)).hom z ∈ I • (⊤ : Submodule W (K.X ((q : ℤ) + 2))) →
      ∀ k, ∃ y : K.X (q : ℤ),
        ϖ k • z - (K.d (q : ℤ) ((q : ℤ) + 1)).hom y ∈
          I • (⊤ : Submodule W (K.X ((q : ℤ) + 1)))) :
    ∀ (q : ℤ) (z : K.X q), 1 ≤ q →
      (K.d q (q + 1)).hom z ∈ I • (⊤ : Submodule W (K.X (q + 1))) →
      ∀ k, ∃ y : K.X (q - 1),
        ϖ k • z - (K.d (q - 1) q).hom y ∈ I • (⊤ : Submodule W (K.X q)) := by
  intro q z hq hdz k
  obtain ⟨q₀, hq₀⟩ : ∃ q₀ : ℕ, q = (q₀ : ℤ) + 1 :=
    ⟨(q - 1).toNat, by
      have h : (((q - 1).toNat : ℤ)) = q - 1 := Int.toNat_of_nonneg (by omega)
      omega⟩
  subst hq₀
  have hidx : ((q₀ : ℤ) + 1) - 1 = (q₀ : ℤ) := by ring
  rw [hidx]
  exact h3 q₀ z hdz k

end Work.DSAMR
