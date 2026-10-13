import Mathlib

set_option maxHeartbeats 2000000

/-!
# `Work.DSG4a.FreeResDefs`: the syzygy tower and the free resolution of a finitely generated
module over a Noetherian ring

This file contains the definitions (and the elementary lemmas about them) used to prove
`Work.DSG4a.exists_freeResolution_above`: for a finitely generated module `M` over a
Noetherian ring `A` there is a cochain complex `F` of finitely generated free `A`-modules
supported in degrees `≤ 0`, together with a quasi-isomorphism `F ⟶ M[0]`.

The construction is the usual iterated syzygy tower.  At level `k` we have a submodule
`Z k ⊆ (Fin (n k) → A)` (the `k`-th syzygy, which is finitely generated because `A` is
Noetherian) together with a surjection `(Fin (n (k+1)) → A) ↠ Z k`, and the differential
`phi k : (Fin (n (k+1)) → A) →ₗ (Fin (n k) → A)` is the composite of that surjection with
the inclusion `Z k ↪ (Fin (n k) → A)`.  By construction
`LinearMap.range (phi (k+1)) = LinearMap.ker (phi k)` for all `k`, which is exactly the
statement that the tower is exact.
-/

open CategoryTheory Limits

universe u

namespace Work.DSG4a

variable {A : Type u} [CommRing A]

/-- **The syzygy step.**  For a submodule `Z` of `Fin n → A` that is finitely generated,
this is a number `m` together with a linear map `(Fin m → A) →ₗ (Fin n → A)` whose
range is exactly `Z`. -/
noncomputable def stepMap (n : ℕ) (Z : Submodule A (Fin n → A)) [Module.Finite A ↥Z] :
    Σ (m : ℕ), {f : (Fin m → A) →ₗ[A] (Fin n → A) // LinearMap.range f = Z} :=
  let h := Module.Finite.exists_fin' A ↥Z
  ⟨h.choose, (Submodule.subtype Z).comp h.choose_spec.choose, by
    rw [LinearMap.range_comp, LinearMap.range_eq_top.mpr h.choose_spec.choose_spec,
      Submodule.map_top, Submodule.range_subtype]⟩

/-- The state of the syzygy tower: a linear map `f : (Fin n → A) →ₗ (Fin m → A)` whose
range is the current syzygy. -/
structure St (A : Type u) [CommRing A] where
  m : ℕ
  n : ℕ
  f : (Fin n → A) →ₗ[A] (Fin m → A)

variable [IsNoetherianRing A]

/-- One step of the syzygy tower: from `s : St A` whose range is the current syzygy, we
produce the next level, a map `(Fin t → A) →ₗ (Fin s.n → A)` whose range is `ker s.f`. -/
noncomputable def stepState (s : St A) : St A :=
  letI : Module.Finite A ↥(LinearMap.ker s.f) := by
    haveI : IsNoetherian A (Fin s.n → A) := isNoetherian_of_isNoetherianRing_of_finite A _
    exact Module.Finite.of_fg (IsNoetherian.noetherian _)
  let t := stepMap s.n (LinearMap.ker s.f)
  ⟨s.n, t.1, t.2.1⟩

/-- The defining property of `stepState`. -/
lemma range_stepState (s : St A) : LinearMap.range (stepState s).f = LinearMap.ker s.f := by
  show LinearMap.range (stepMap s.n (LinearMap.ker s.f)).2.1 = LinearMap.ker s.f
  exact (stepMap s.n (LinearMap.ker s.f)).2.2

/-- A finite surjection onto a finitely generated module. -/
noncomputable def augment (M : Type u) [AddCommGroup M] [Module A M] [Module.Finite A M] :
    Σ (n : ℕ), {f : (Fin n → A) →ₗ[A] M // Function.Surjective f} :=
  let h := Module.Finite.exists_fin' A M
  ⟨h.choose, h.choose_spec.choose, h.choose_spec.choose_spec⟩

variable (M : Type u) [AddCommGroup M] [Module A M] [Module.Finite A M]

/-- The number of generators of `M` used by the augmentation. -/
noncomputable def n0 : ℕ := (augment (A:=A) M).1

/-- The augmentation `(Fin (n0) → A) ↠ M`. -/
noncomputable def phi0 : (Fin (n0 (A:=A) M) → A) →ₗ[A] M := (augment (A:=A) M).2.1

lemma phi0_surj : Function.Surjective (phi0 (A:=A) M) := (augment (A:=A) M).2.2

/-- The zeroth level of the tower: the syzygy of the augmentation. -/
noncomputable def base : St A :=
  letI : Module.Finite A ↥(LinearMap.ker (phi0 (A:=A) M)) := by
    haveI : IsNoetherian A (Fin (n0 (A:=A) M) → A) :=
      isNoetherian_of_isNoetherianRing_of_finite A _
    exact Module.Finite.of_fg (IsNoetherian.noetherian _)
  let t := stepMap (n0 (A:=A) M) (LinearMap.ker (phi0 (A:=A) M))
  ⟨n0 (A:=A) M, t.1, t.2.1⟩

lemma range_base : LinearMap.range (base (A:=A) M).f = LinearMap.ker (phi0 (A:=A) M) := by
  show LinearMap.range (stepMap (n0 (A:=A) M) (LinearMap.ker (phi0 (A:=A) M))).2.1
    = LinearMap.ker (phi0 (A:=A) M)
  exact (stepMap (n0 (A:=A) M) (LinearMap.ker (phi0 (A:=A) M))).2.2

/-- The sequence of states of the syzygy tower. -/
noncomputable def stateSeq : ℕ → St A :=
  Nat.rec (base (A:=A) M) (fun _ s => stepState s)

/-- The `k`-th term of the free resolution: `(Fin (stateSeq k).m → A)`. -/
noncomputable def term (k : ℕ) : ModuleCat.{u} A :=
  ModuleCat.of A (Fin ((stateSeq (A:=A) M k).m) → A)

/-- The resolution of `M`, as an `ℕ`-indexed chain complex: the `k`-th differential is
`(stateSeq k).f`. -/
noncomputable def Kcc : ChainComplex (ModuleCat.{u} A) ℕ :=
  ChainComplex.of (fun k => term (A:=A) M k) (fun k => ModuleCat.ofHom ((stateSeq (A:=A) M k).f))
    (fun k => by
      apply ModuleCat.hom_ext
      apply LinearMap.ext
      intro x
      have hx := LinearMap.mem_range_self ((stateSeq (A:=A) M (k+1)).f) x
      have hstep : LinearMap.range ((stateSeq (A:=A) M (k+1)).f)
          = LinearMap.ker ((stateSeq (A:=A) M k).f) :=
        range_stepState (stateSeq (A:=A) M k)
      rw [hstep] at hx
      exact hx)

lemma Kcc_d (k : ℕ) :
    (Kcc (A:=A) M).d (k+1) k = ModuleCat.ofHom ((stateSeq (A:=A) M k).f) :=
  ChainComplex.of_d (fun k => term (A:=A) M k)
    (fun k => ModuleCat.ofHom ((stateSeq (A:=A) M k).f)) k

/-- The complex `Kcc` is exact in every positive degree. -/
lemma Kcc_exactAt (k : ℕ) : (Kcc (A:=A) M).ExactAt (k+1) := by
  have hp : (ComplexShape.down ℕ).prev (k+1) = k+1+1 :=
    ComplexShape.prev_eq' _ (by simp [ComplexShape.down])
  have hn : (ComplexShape.down ℕ).next (k+1) = k :=
    ComplexShape.next_eq' _ (by simp [ComplexShape.down])
  rw [HomologicalComplex.exactAt_iff' _ (k+1+1) (k+1) k hp hn]
  rw [ShortComplex.moduleCat_exact_iff_range_eq_ker]
  simp only [HomologicalComplex.shortComplexFunctor'_obj_f, HomologicalComplex.shortComplexFunctor'_obj_g,
    Kcc_d, ModuleCat.hom_ofHom]
  exact range_stepState (stateSeq (A:=A) M k)

/-- The embedding of the shape of the resolution into the cochain world: `n ↦ -n`. -/
noncomputable def emb : ComplexShape.Embedding (ComplexShape.down ℕ) (ComplexShape.up ℤ) :=
  ComplexShape.embeddingUpIntLE (0 : ℤ)

/-- The cochain complex of finitely generated free modules supported in degrees `≤ 0`
associated with the resolution. -/
noncomputable def F : CochainComplex (ModuleCat.{u} A) ℤ := (Kcc (A:=A) M).extend (emb)

lemma F_isStrictlyLE : (F (A:=A) M).IsStrictlyLE 0 := by
  unfold F emb
  infer_instance

/-- The comparison map from the resolution to `M` concentrated in degree `0`. -/
noncomputable def qdown : (Kcc (A:=A) M) ⟶
    (ChainComplex.single₀ (ModuleCat.{u} A)).obj (ModuleCat.of A M) :=
  (ChainComplex.toSingle₀Equiv (Kcc (A:=A) M) (ModuleCat.of A M)).symm
    ⟨ModuleCat.ofHom (phi0 (A:=A) M), by
      apply ModuleCat.hom_ext
      apply LinearMap.ext
      intro x
      have hx := LinearMap.mem_range_self (base (A:=A) M).f x
      have hstep : LinearMap.range (base (A:=A) M).f = LinearMap.ker (phi0 (A:=A) M) :=
        range_base (A:=A) M
      rw [hstep] at hx
      exact hx⟩

lemma qdown_f_zero : (qdown (A:=A) M).f 0 = ModuleCat.ofHom (phi0 (A:=A) M) :=
  ChainComplex.toSingle₀Equiv_symm_apply_f_zero _ _

end Work.DSG4a
