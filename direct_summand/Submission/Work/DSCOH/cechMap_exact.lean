import Mathlib
import Submission.Work.DSCOH.Cech
import Submission.Work.DSCOH.degZero_exact

namespace Work.DSCOH

/-!
## Exactness of the map of chart Čech complexes

Given a degreewise left-exact sequence of graded `A[X₀,…,X_{n-1}]`-modules

  `ℳ --f--> ℳ' --g--> ℳ''`

(`f` injective, `ℳ''_d = g(ℳ'_d)`, `ker g ⊓ ℳ'_d ⊆ f(ℳ_d)`), the induced map of chart Čech
complexes `cechMap f` is injective, its image is the kernel of `cechMap g`, and `cechMap g` is
surjective.

All of this is *componentwise*: the `q`-th term `CechTerm ℳ q` is the product, over the
`(q+1)`-element subsets `S` of the index set, of the degree-zero parts `degZero ℳ S`, and the
`S`-component of `cechMap f` is the map on `degZero ℳ S` induced by `f`.  The componentwise
statement is exactly `Work.DSCOH.degZero_exact`; the only extra input needed is that the maps
`locMapOf` on the chart localizations are functorial (this is `IsLocalizedModule.map_comp'`),
so that `cechMap g ∘ cechMap f = cechMap (g ∘ f) = 0`.
-/

variable {A : Type*} [CommRing A] {n : ℕ}

/-- The `S`-component of `cechMap φ q x`, as an element of the chart localization: it is
`locMapOf φ S` applied to the `S`-component of `x`. -/
private lemma cechMap_apply_val {M : Type*} [AddCommGroup M] [Module A M]
    [Module (Poly A n) M] [IsScalarTower A (Poly A n) M]
    {N : Type*} [AddCommGroup N] [Module A N] [Module (Poly A n) N]
    [IsScalarTower A (Poly A n) N]
    (ℳ : ℕ → Submodule A M) (𝒩 : ℕ → Submodule A N)
    (φ : M →ₗ[Poly A n] N) (hφ : ∀ d, Submodule.map (φ.restrictScalars A) (ℳ d) ≤ 𝒩 d)
    (q : ℕ) (x : CechTerm (A := A) (n := n) (M := M) ℳ q)
    (S : {S : Finset (Fin n) // S.card = q + 1}) :
    ((cechMap (A := A) (n := n) ℳ 𝒩 φ hφ q x) S).1 =
      locMapOf (A := A) (M := M) φ S.1 (x S).1 := by
  simp only [cechMap, LinearMap.pi_apply, LinearMap.comp_apply, LinearMap.proj_apply]
  rfl

/-- Functoriality of the maps induced by a linear map on the chart localizations: localizing a
composite is the composite of the localizations (`IsLocalizedModule.map_comp'`). -/
private lemma locMapOf_comp {M : Type*} [AddCommGroup M] [Module A M] [Module (Poly A n) M]
    [IsScalarTower A (Poly A n) M]
    {N : Type*} [AddCommGroup N] [Module A N] [Module (Poly A n) N]
    [IsScalarTower A (Poly A n) N]
    {P : Type*} [AddCommGroup P] [Module A P] [Module (Poly A n) P]
    [IsScalarTower A (Poly A n) P]
    (φ : M →ₗ[Poly A n] N) (ψ : N →ₗ[Poly A n] P) (S : Finset (Fin n)) :
    (locMapOf (A := A) (M := N) ψ S).comp (locMapOf (A := A) (M := M) φ S) =
      locMapOf (A := A) (M := M) (ψ.comp φ) S :=
  (IsLocalizedModule.map_comp' (subS (A := A) S)
    (LocalizedModule.mkLinearMap (subS (A := A) S) M)
    (LocalizedModule.mkLinearMap (subS (A := A) S) N)
    (LocalizedModule.mkLinearMap (subS (A := A) S) P) φ ψ).symm

/-- The value form of `locMapOf_comp`. -/
private lemma locMapOf_comp_apply {M : Type*} [AddCommGroup M] [Module A M]
    [Module (Poly A n) M] [IsScalarTower A (Poly A n) M]
    {N : Type*} [AddCommGroup N] [Module A N] [Module (Poly A n) N]
    [IsScalarTower A (Poly A n) N]
    {P : Type*} [AddCommGroup P] [Module A P] [Module (Poly A n) P]
    [IsScalarTower A (Poly A n) P]
    (φ : M →ₗ[Poly A n] N) (ψ : N →ₗ[Poly A n] P) (S : Finset (Fin n))
    (x : locAt (A := A) (M := M) S) :
    locMapOf (A := A) (M := N) ψ S (locMapOf (A := A) (M := M) φ S x) =
      locMapOf (A := A) (M := M) (ψ.comp φ) S x := by
  rw [← LinearMap.comp_apply, locMapOf_comp]

/-- The localization of the zero map is zero. -/
private lemma locMapOf_zero {M : Type*} [AddCommGroup M] [Module A M] [Module (Poly A n) M]
    [IsScalarTower A (Poly A n) M]
    {N : Type*} [AddCommGroup N] [Module A N] [Module (Poly A n) N]
    [IsScalarTower A (Poly A n) N]
    (S : Finset (Fin n)) :
    locMapOf (A := A) (M := M) (N := N) (0 : M →ₗ[Poly A n] N) S = 0 := by
  ext x
  obtain ⟨⟨y, s⟩, rfl⟩ := IsLocalizedModule.mk'_surjective (subS (A := A) S)
    (LocalizedModule.mkLinearMap (subS (A := A) S) M) x
  simp [locMapOf]

/-- The value form of `locMapOf_zero`. -/
private lemma locMapOf_zero_apply {M : Type*} [AddCommGroup M] [Module A M]
    [Module (Poly A n) M] [IsScalarTower A (Poly A n) M]
    {N : Type*} [AddCommGroup N] [Module A N] [Module (Poly A n) N]
    [IsScalarTower A (Poly A n) N]
    (S : Finset (Fin n)) (x : locAt (A := A) (M := M) S) :
    locMapOf (A := A) (M := M) (N := N) (0 : M →ₗ[Poly A n] N) S x = 0 := by
  rw [locMapOf_zero, LinearMap.zero_apply]

theorem cechMap_exact {A : Type*} [CommRing A] {n : ℕ}
    {M M' M'' : Type*}
    [AddCommGroup M] [Module A M] [Module (Poly A n) M] [IsScalarTower A (Poly A n) M]
    [AddCommGroup M'] [Module A M'] [Module (Poly A n) M'] [IsScalarTower A (Poly A n) M']
    [AddCommGroup M''] [Module A M''] [Module (Poly A n) M''] [IsScalarTower A (Poly A n) M'']
    {ℳ : ℕ → Submodule A M} {ℳ' : ℕ → Submodule A M'} [SetLike.GradedSMul (homSub A n) ℳ']
    {ℳ'' : ℕ → Submodule A M''}
    (f : M →ₗ[Poly A n] M') (g : M' →ₗ[Poly A n] M'')
    (hinj : Function.Injective f) (hex : Function.Exact f g)
    (hgr1 : ∀ d, Submodule.map (f.restrictScalars A) (ℳ d) ≤ ℳ' d)
    (hgr2 : ∀ d, Submodule.map (g.restrictScalars A) (ℳ' d) = ℳ'' d)
    (hker : ∀ d, ℳ' d ⊓ LinearMap.ker (g.restrictScalars A) ≤
      Submodule.map (f.restrictScalars A) (ℳ d))
    (q : ℕ) :
    Function.Injective (cechMap (A := A) (n := n) ℳ ℳ' f hgr1 q) ∧
      Function.Exact (cechMap (A := A) (n := n) ℳ ℳ' f hgr1 q)
        (cechMap (A := A) (n := n) ℳ' ℳ'' g (fun d => le_of_eq (hgr2 d)) q) ∧
      Function.Surjective (cechMap (A := A) (n := n) ℳ' ℳ'' g (fun d => le_of_eq (hgr2 d)) q) := by
  -- the componentwise statement, at every chart `S`
  have H := fun S : Finset (Fin n) =>
    degZero_exact (A := A) (n := n) (ℳ := ℳ) (ℳ' := ℳ') (ℳ'' := ℳ'')
      f g hinj hgr1 hgr2 hker S
  -- exactness of `f` and `g` forces `g ∘ f = 0`
  have hcomp : g.comp f = 0 := LinearMap.ext fun m => (hex (f m)).mpr ⟨m, rfl⟩
  refine ⟨?_, ?_, ?_⟩
  · -- injectivity, componentwise
    intro x y hxy
    have hzero : x - y = 0 := by
      funext S
      apply Subtype.ext
      have h1 : locMapOf (A := A) (M := M) f S.1 ((x - y) S).1 = 0 := by
        rw [← cechMap_apply_val (A := A) (n := n) ℳ ℳ' f hgr1 q (x - y) S,
          show cechMap (A := A) (n := n) ℳ ℳ' f hgr1 q (x - y) = 0 by
            rw [map_sub, hxy, sub_self]]
        rfl
      exact (H S.1).2.2.1 ((x - y) S).1 ((x - y) S).2 h1
    exact sub_eq_zero.mp hzero
  · -- exactness in the middle, componentwise
    refine LinearMap.exact_iff.mpr (le_antisymm ?_ ?_)
    · -- `ker g ⊆ range f`
      intro x hx
      rw [LinearMap.mem_ker] at hx
      have hS : ∀ S : {S : Finset (Fin n) // S.card = q + 1},
          ∃ y : locAt (A := A) (M := M) S.1, y ∈ degZero (A := A) ℳ S.1 ∧
            locMapOf (A := A) (M := M) f S.1 y = (x S).1 := by
        intro S
        have hxS : locMapOf (A := A) (M := M') g S.1 (x S).1 = 0 := by
          rw [← cechMap_apply_val (A := A) (n := n) ℳ' ℳ'' g (fun d => le_of_eq (hgr2 d)) q x S,
            hx]
          rfl
        exact (H S.1).2.2.2.1 (x S).1 (x S).2 hxS
      choose y hy hyf using hS
      refine LinearMap.mem_range.mpr ⟨fun S => ⟨y S, hy S⟩, ?_⟩
      funext S
      apply Subtype.ext
      rw [cechMap_apply_val (A := A) (n := n) ℳ ℳ' f hgr1 q (fun S => ⟨y S, hy S⟩) S]
      exact hyf S
    · -- `range f ⊆ ker g`
      intro x hx
      rw [LinearMap.mem_range] at hx
      obtain ⟨y, rfl⟩ := hx
      rw [LinearMap.mem_ker]
      funext S
      apply Subtype.ext
      rw [cechMap_apply_val (A := A) (n := n) ℳ' ℳ'' g (fun d => le_of_eq (hgr2 d)) q
          (cechMap (A := A) (n := n) ℳ ℳ' f hgr1 q y) S]
      rw [cechMap_apply_val (A := A) (n := n) ℳ ℳ' f hgr1 q y S]
      rw [locMapOf_comp_apply, hcomp, locMapOf_zero_apply]
      rfl
  · -- surjectivity, componentwise
    intro z
    have hS : ∀ S : {S : Finset (Fin n) // S.card = q + 1},
        ∃ y : locAt (A := A) (M := M') S.1, y ∈ degZero (A := A) ℳ' S.1 ∧
          locMapOf (A := A) (M := M') g S.1 y = (z S).1 :=
      fun S => (H S.1).2.2.2.2 (z S).1 (z S).2
    choose y hy hz using hS
    refine ⟨fun S => ⟨y S, hy S⟩, ?_⟩
    funext S
    apply Subtype.ext
    rw [cechMap_apply_val (A := A) (n := n) ℳ' ℳ'' g (fun d => le_of_eq (hgr2 d)) q
      (fun S => ⟨y S, hy S⟩) S]
    exact hz S

end Work.DSCOH
