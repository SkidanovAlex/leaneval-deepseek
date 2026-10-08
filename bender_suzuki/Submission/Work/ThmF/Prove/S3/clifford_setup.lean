import Mathlib
import Submission.Work.CharPrelim.modular_frobenius_general

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

noncomputable section

set_option linter.unusedSectionVars false

open scoped MonoidAlgebra
open Classical

namespace Work.ThmF.Prove.S3

/-! ## Setup: restricting a representation to a subgroup -/

/-- The restriction of a representation `ρ` of `L` to a subgroup `K ≤ L`. -/
abbrev resRep {L : Type*} [Group L] {F : Type*} [Field F] {K : Subgroup L} {V : Type*}
    [AddCommGroup V] [Module F V] (ρ : Representation F L V) : Representation F K V :=
  ρ.comp K.subtype

/-! ## The characteristic hypothesis gives invertibility of `|K|` -/

section CharHyp

variable {F : Type*} [Field F]

/-- If `n ≠ 0` and no prime `q` with `(q : F) = 0` divides `n`, then the image of `n` in `F` is
nonzero. -/
lemma neZero_natCast_of_char {n : ℕ} (hn : n ≠ 0)
    (hchar : ∀ q : ℕ, q.Prime → (q : F) = 0 → ¬ q ∣ n) : NeZero (n : F) := by
  refine ⟨fun h0 => ?_⟩
  have hdvd : ringChar F ∣ n := (ringChar.spec F n).mp h0
  rcases CharP.char_is_prime_or_zero F (ringChar F) with hp | h0r
  · exact hchar _ hp ((ringChar.spec F (ringChar F)).mpr dvd_rfl) hdvd
  · rw [h0r] at hdvd
    exact hn (Nat.zero_dvd.mp hdvd)

end CharHyp

/-! ## The conjugation action of `L` on the `K`-invariant subspaces -/

section ConjRep

variable {L : Type*} [Group L] {F : Type*} [Field F] {K : Subgroup L} {V : Type*}
  [AddCommGroup V] [Module F V] (hKn : K.Normal) (ρ : Representation F L V)

/-- For `e : L`, the image of a `K`-invariant subspace under `ρ e` is again `K`-invariant,
because `K` is normal.  This is the action of `L` on the lattice of subrepresentations of the
restriction of `ρ` to `K`. -/
def conjRep (e : L) (σ : Subrepresentation (resRep (K := K) ρ)) :
    Subrepresentation (resRep (K := K) ρ) where
  toSubmodule := σ.toSubmodule.map (ρ e)
  apply_mem_toSubmodule k v hv := by
    obtain ⟨w, hw, rfl⟩ := Submodule.mem_map.mp hv
    refine Submodule.mem_map.mpr ⟨ρ (e⁻¹ * (k : L) * e) w, ?_, ?_⟩
    · exact σ.apply_mem_toSubmodule ⟨e⁻¹ * (k : L) * e,
        by simpa using hKn.conj_mem (k : L) k.2 e⁻¹⟩ hw
    · show ((ρ e) * (ρ (e⁻¹ * (k : L) * e))) w = ((ρ k) * (ρ e)) w
      rw [← map_mul, ← map_mul]
      congr 1
      group

@[simp]
theorem conjRep_toSubmodule (e : L) (σ : Subrepresentation (resRep (K := K) ρ)) :
    (conjRep hKn ρ e σ).toSubmodule = σ.toSubmodule.map (ρ e) := rfl

theorem conjRep_mul (e f : L) (σ : Subrepresentation (resRep (K := K) ρ)) :
    conjRep hKn ρ e (conjRep hKn ρ f σ) = conjRep hKn ρ (e * f) σ := by
  apply Subrepresentation.toSubmodule_injective
  rw [conjRep_toSubmodule, conjRep_toSubmodule, conjRep_toSubmodule, ← Submodule.map_comp]
  congr 1
  ext v
  simp [map_mul]

@[simp]
theorem conjRep_one (σ : Subrepresentation (resRep (K := K) ρ)) :
    conjRep hKn ρ 1 σ = σ := by
  apply Subrepresentation.toSubmodule_injective
  ext v
  simp only [conjRep_toSubmodule, Submodule.mem_map]
  constructor
  · rintro ⟨w, hw, hwv⟩
    rw [← hwv]
    simpa using hw
  · intro hv
    exact ⟨v, hv, by simp⟩

theorem conjRep_inv_cancel (e : L) (σ : Subrepresentation (resRep (K := K) ρ)) :
    conjRep hKn ρ e⁻¹ (conjRep hKn ρ e σ) = σ := by
  rw [conjRep_mul, inv_mul_cancel, conjRep_one]

theorem conjRep_inv_cancel' (e : L) (σ : Subrepresentation (resRep (K := K) ρ)) :
    conjRep hKn ρ e (conjRep hKn ρ e⁻¹ σ) = σ := by
  rw [conjRep_mul, mul_inv_cancel, conjRep_one]

/-- The order isomorphism of the lattice of `K`-invariant subspaces induced by `ρ e`. -/
def conjRepIso (e : L) : Subrepresentation (resRep (K := K) ρ) ≃o
    Subrepresentation (resRep (K := K) ρ) where
  toFun := conjRep hKn ρ e
  invFun := conjRep hKn ρ e⁻¹
  left_inv := conjRep_inv_cancel hKn ρ e
  right_inv := conjRep_inv_cancel' hKn ρ e
  map_rel_iff' {a b} := by
    constructor
    · intro h
      have h' : (conjRep hKn ρ e a).toSubmodule ≤ (conjRep hKn ρ e b).toSubmodule := h
      have h2 : (conjRep hKn ρ e⁻¹ (conjRep hKn ρ e a)).toSubmodule ≤
          (conjRep hKn ρ e⁻¹ (conjRep hKn ρ e b)).toSubmodule :=
        Submodule.map_mono (f := ρ e⁻¹) h'
      rwa [conjRep_inv_cancel, conjRep_inv_cancel] at h2
    · intro h
      exact Submodule.map_mono (f := ρ e) h

end ConjRep

/-! ## The same action, seen on the `F[K]`-module `ρ.asModule` -/

section ModuleWorld

variable {L : Type*} [Group L] {F : Type*} [Field F] {K : Subgroup L} {V : Type*}
  [AddCommGroup V] [Module F V]

/-- The `F`-linear automorphism `x ↦ ρ e x` of `ρ.asModule` (where `ρ` is the restriction of
the original representation to `K`). -/
noncomputable def Te (ρ : Representation F L V) (e : L) :
    (resRep (K := K) ρ).asModule ≃ₗ[F] (resRep (K := K) ρ).asModule :=
  LinearEquiv.ofBijective (ρ e) (Representation.apply_bijective ρ e)

@[simp] theorem Te_apply (ρ : Representation F L V) (e : L)
    (x : (resRep (K := K) ρ).asModule) : Te (K := K) ρ e x = ρ e x := rfl

/-- The order automorphism of the lattice of `F[K]`-submodules of `ρ.asModule` induced by the
conjugation action of `e`. -/
noncomputable def conjModIso (hKn : K.Normal) (ρ : Representation F L V) (e : L) :
    Submodule (MonoidAlgebra F K) (resRep (K := K) ρ).asModule ≃o
      Submodule (MonoidAlgebra F K) (resRep (K := K) ρ).asModule :=
  ((Subrepresentation.subrepresentationSubmoduleOrderIso (ρ := resRep (K := K) ρ)).symm.trans
    (conjRepIso hKn ρ e)).trans
  (Subrepresentation.subrepresentationSubmoduleOrderIso (ρ := resRep (K := K) ρ))

/-- The conjugation action of `e` on `F[K]`-submodules of `ρ.asModule`. -/
noncomputable def conjMod (hKn : K.Normal) (ρ : Representation F L V) (e : L)
    (N : Submodule (MonoidAlgebra F K) (resRep (K := K) ρ).asModule) :
    Submodule (MonoidAlgebra F K) (resRep (K := K) ρ).asModule := conjModIso hKn ρ e N

theorem ofSubmodule'_conjMod (hKn : K.Normal) (ρ : Representation F L V) (e : L)
    (N : Submodule (MonoidAlgebra F K) (resRep (K := K) ρ).asModule) :
    Subrepresentation.ofSubmodule' (conjMod hKn ρ e N) =
      conjRep hKn ρ e (Subrepresentation.ofSubmodule' N) := rfl

@[simp] theorem ofSubmodule'_toSubmodule (ρ : Representation F L V)
    (N : Submodule (MonoidAlgebra F K) (resRep (K := K) ρ).asModule) :
    (Subrepresentation.ofSubmodule' N).toSubmodule = N.restrictScalars F := rfl

theorem ofSubmodule'_injective (ρ : Representation F L V) :
    Function.Injective (Subrepresentation.ofSubmodule' (A := F) (G := K)
      (ρ := resRep (K := K) ρ)) :=
  (Subrepresentation.subrepresentationSubmoduleOrderIso (ρ := resRep (K := K) ρ)).symm.injective

theorem conjMod_mul (hKn : K.Normal) (ρ : Representation F L V) (e f : L)
    (N : Submodule (MonoidAlgebra F K) (resRep (K := K) ρ).asModule) :
    conjMod hKn ρ e (conjMod hKn ρ f N) = conjMod hKn ρ (e * f) N := by
  apply ofSubmodule'_injective (K := K) ρ
  rw [ofSubmodule'_conjMod, ofSubmodule'_conjMod, ofSubmodule'_conjMod]
  exact conjRep_mul hKn ρ e f (Subrepresentation.ofSubmodule' N)

@[simp] theorem conjMod_one (hKn : K.Normal) (ρ : Representation F L V)
    (N : Submodule (MonoidAlgebra F K) (resRep (K := K) ρ).asModule) :
    conjMod hKn ρ 1 N = N := by
  apply ofSubmodule'_injective (K := K) ρ
  rw [ofSubmodule'_conjMod, conjRep_one]

/-- The underlying `F`-subspace of `conjMod e N` is the image of that of `N` under `x ↦ ρ e x`. -/
theorem conjMod_restrictScalars (hKn : K.Normal) (ρ : Representation F L V) (e : L)
    (N : Submodule (MonoidAlgebra F K) (resRep (K := K) ρ).asModule) :
    (conjMod hKn ρ e N).restrictScalars F =
      ((Subrepresentation.ofSubmodule' N).toSubmodule).map (ρ e : V →ₗ[F] V) := by
  rw [← ofSubmodule'_toSubmodule (K := K) ρ (conjMod hKn ρ e N), ofSubmodule'_conjMod,
    conjRep_toSubmodule]

set_option backward.isDefEq.respectTransparency false in
/-- Characterization of the conjugation action on `F[K]`-submodules: the submodule `conjMod e N`
is the image of `N` under `x ↦ ρ e x`. -/
theorem mem_conjMod_iff (hKn : K.Normal) (ρ : Representation F L V) (e : L)
    (N : Submodule (MonoidAlgebra F K) (resRep (K := K) ρ).asModule)
    (x : (resRep (K := K) ρ).asModule) :
    x ∈ conjMod hKn ρ e N ↔ ∃ y ∈ N, ρ e y = x := by
  rw [← Submodule.restrictScalars_mem F (conjMod hKn ρ e N) x,
    conjMod_restrictScalars hKn ρ e N, Submodule.mem_map]
  constructor
  · rintro ⟨y, hy, hyx⟩
    rw [ofSubmodule'_toSubmodule (K := K) ρ N, Submodule.restrictScalars_mem F N y] at hy
    exact ⟨y, hy, hyx⟩
  · rintro ⟨y, hy, hyx⟩
    refine ⟨y, ?_, hyx⟩
    rw [ofSubmodule'_toSubmodule (K := K) ρ N, Submodule.restrictScalars_mem F N y]
    exact hy

set_option backward.isDefEq.respectTransparency false in
/-- The conjugation action preserves the `F`-dimension of a submodule. -/
theorem finrank_conjMod_eq (hKn : K.Normal) (ρ : Representation F L V) (e : L)
    (N : Submodule (MonoidAlgebra F K) (resRep (K := K) ρ).asModule) :
    Module.finrank F ↥(conjMod hKn ρ e N) = Module.finrank F ↥N := by
  have e1 : Module.finrank F ↥(conjMod hKn ρ e N) =
      Module.finrank F ↥((conjMod hKn ρ e N).restrictScalars F) := rfl
  have e2 : Module.finrank F ↥((conjMod hKn ρ e N).restrictScalars F) =
      Module.finrank F ↥(((Subrepresentation.ofSubmodule' N).toSubmodule).map (ρ e : V →ₗ[F] V)) := by
    rw [conjMod_restrictScalars hKn ρ e N]
    rfl
  have e3 : Module.finrank F ↥(((Subrepresentation.ofSubmodule' N).toSubmodule).map (ρ e : V →ₗ[F] V)) =
      Module.finrank F ↥((Subrepresentation.ofSubmodule' N).toSubmodule) :=
    (LinearEquiv.finrank_eq (Submodule.equivMapOfInjective (ρ e)
      (Representation.apply_bijective ρ e).injective
      (Subrepresentation.ofSubmodule' N).toSubmodule)).symm
  have e4 : Module.finrank F ↥((Subrepresentation.ofSubmodule' N).toSubmodule) =
      Module.finrank F ↥N := rfl
  exact e1.trans (e2.trans (e3.trans e4))

end ModuleWorld

end Work.ThmF.Prove.S3
