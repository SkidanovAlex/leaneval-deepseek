import Mathlib
import Submission.Work.KT.Defs
import Submission.Work.KT.Fund.Basic
import Submission.Work.KT.Cone.Setup
import Submission.Work.KT.Cone.Milnor

/-!
# `Work.KT.Cone.Assembly` — assembly of `Work.KT.cone_exact` from Milnor exactness

Given `f : S_V → T`, the mapping cone algebra `A = coneAlg f` is the pull-back
`C(T) ×_{C(S_V)} C(D_V)`.  This file derives the three assertions of `Work.KT.cone_exact`
from the three parts of `Work.KT.k0_exact`:

1. middle exactness of `K₀(U) → K₀(C_f) → K₀(C(T))`, where `U = ℂ·1 + ker (coneToT f)` is the
   range of `relToCone` and hence isomorphic to `Kpair V`;
2. the Mayer–Vietoris (patching) property of the Milnor square `A → C(T)`, `C(D_V) → C(S_V)`;
3. injectivity of `K₀(U)_red → K₀(A)`, which needs (and is stated with) the stable lifting of
   invertible matrices over `C(T)` along `coneToT f`.

The passage from `K₀(U)` to `K₀(Kpair V)` is factored through the generic lemmas
`transport_mid`/`transport_inj`, which live in an abstract setting (`A`, `C`, `D` arbitrary rings
and `S ⊆ C` an arbitrary subalgebra): the concrete algebra `U` is a `Subalgebra` of a `Subalgebra`
of a product of `C*-algebras`, and elaborating instance arguments of such a nested type is
expensive, so it is done as little as possible.
-/

namespace Work.KT.Cone

open _root_.Matrix

noncomputable section

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000

variable {V : Type} [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]
variable {T : Type} [TopologicalSpace T] [CompactSpace T] [T2Space T] [Nonempty T]

/-! ## `K0.mapA` with explicit ring arguments -/

lemma mapA_comp' {A B C : Type} [Ring A] [Ring B] [Ring C]
    [Algebra ℂ A] [Algebra ℂ B] [Algebra ℂ C] (φ : B →ₐ[ℂ] C) (ψ : A →ₐ[ℂ] B) :
    K0.mapA (A := A) (B := C) (φ.comp ψ)
      = (K0.mapA (A := B) (B := C) φ).comp (K0.mapA (A := A) (B := B) ψ) :=
  K0.map_comp ψ.toRingHom φ.toRingHom

lemma mapA_id' {A : Type} [Ring A] [Algebra ℂ A] :
    K0.mapA (A := A) (B := A) (AlgHom.id ℂ A) = AddMonoidHom.id (K0 A) :=
  K0.map_id

lemma map_eq_mapA {A B : Type} [Ring A] [Ring B] [Algebra ℂ A] [Algebra ℂ B] (φ : A →ₐ[ℂ] B) :
    K0.map φ.toRingHom = K0.mapA (A := A) (B := B) φ := rfl

/-! ## Generic transport of exactness across an isomorphism of algebras -/

section Generic

variable {A C D : Type} [Ring A] [Algebra ℂ A] [Ring C] [Algebra ℂ C] [Ring D] [Algebra ℂ D]

/-- `(e ∘ σ) ∘ σ⁻¹ = e`. -/
lemma algHom_comp_symm_cancel (S : Subalgebra ℂ C) (σ : A ≃ₐ[ℂ] S) (e : S →ₐ[ℂ] ℂ) :
    (e.comp σ.toAlgHom).comp σ.symm.toAlgHom = e := by
  rw [AlgHom.comp_assoc, AlgEquiv.comp_symm, AlgHom.comp_id]

/-- `(S.val ∘ σ) ∘ σ⁻¹ = S.val`. -/
lemma val_comp_symm_cancel (S : Subalgebra ℂ C) (σ : A ≃ₐ[ℂ] S) :
    (S.val.comp σ.toAlgHom).comp σ.symm.toAlgHom = S.val := by
  rw [AlgHom.comp_assoc, AlgEquiv.comp_symm, AlgHom.comp_id]

/-- Transport of middle exactness of an ideal sequence along `σ : A ≃ₐ[ℂ] S ⊆ C`. -/
lemma transport_mid (S : Subalgebra ℂ C) (σ : A ≃ₐ[ℂ] S) (g : C →ₐ[ℂ] D) (e : S →ₐ[ℂ] ℂ)
    (e' : A →ₐ[ℂ] ℂ) (he : e.comp σ.toAlgHom = e') (g' : A →ₐ[ℂ] C)
    (hg : S.val.comp σ.toAlgHom = g')
    (H : ∀ z : K0 C, K0.mapA (A := C) (B := D) g z = 0 →
      ∃ w : K0 S, K0.mapA (A := S) (B := ℂ) e w = 0 ∧ K0.mapA (A := S) (B := C) S.val w = z) :
    ∀ z : K0 C, K0.mapA (A := C) (B := D) g z = 0 →
      ∃ w : K0 A, K0.mapA (A := A) (B := ℂ) e' w = 0 ∧ K0.mapA (A := A) (B := C) g' w = z := by
  intro z hz
  obtain ⟨w, hw1, hw2⟩ := H z hz
  refine ⟨K0.mapA (A := S) (B := A) σ.symm.toAlgHom w, ?_, ?_⟩
  · have key : K0.mapA (A := A) (B := ℂ) e' (K0.mapA (A := S) (B := A) σ.symm.toAlgHom w)
        = K0.mapA (A := S) (B := ℂ) e w := by
      rw [← AddMonoidHom.comp_apply, ← mapA_comp',
        show e'.comp σ.symm.toAlgHom = e from by
          rw [← he]; exact algHom_comp_symm_cancel S σ e]
    rw [key]; exact hw1
  · have key : K0.mapA (A := A) (B := C) g' (K0.mapA (A := S) (B := A) σ.symm.toAlgHom w)
        = K0.mapA (A := S) (B := C) S.val w := by
      rw [← AddMonoidHom.comp_apply, ← mapA_comp',
        show g'.comp σ.symm.toAlgHom = S.val from by
          rw [← hg]; exact val_comp_symm_cancel S σ]
    rw [key]; exact hw2

/-- Transport of injectivity of the reduced part along `σ : A ≃ₐ[ℂ] S ⊆ C`. -/
lemma transport_inj (S : Subalgebra ℂ C) (σ : A ≃ₐ[ℂ] S) (e : S →ₐ[ℂ] ℂ) (e' : A →ₐ[ℂ] ℂ)
    (he : e.comp σ.toAlgHom = e') (g' : A →ₐ[ℂ] C) (hg : S.val.comp σ.toAlgHom = g')
    (H : ∀ w : K0 S, K0.mapA (A := S) (B := ℂ) e w = 0 →
      K0.mapA (A := S) (B := C) S.val w = 0 → w = 0) :
    ∀ w : K0 A, K0.mapA (A := A) (B := ℂ) e' w = 0 →
      K0.mapA (A := A) (B := C) g' w = 0 → w = 0 := by
  intro w hw1 hw2
  have h1 : K0.mapA (A := S) (B := ℂ) e (K0.mapA (A := A) (B := S) σ.toAlgHom w) = 0 := by
    rw [← AddMonoidHom.comp_apply, ← mapA_comp', he]
    exact hw1
  have h2 : K0.mapA (A := S) (B := C) S.val (K0.mapA (A := A) (B := S) σ.toAlgHom w) = 0 := by
    rw [← AddMonoidHom.comp_apply, ← mapA_comp', hg]
    exact hw2
  have hkey := H (K0.mapA (A := A) (B := S) σ.toAlgHom w) h1 h2
  have hback : K0.mapA (A := S) (B := A) σ.symm.toAlgHom
      (K0.mapA (A := A) (B := S) σ.toAlgHom w) = w := by
    rw [← AddMonoidHom.comp_apply, ← mapA_comp', AlgEquiv.symm_comp, mapA_id']
    rfl
  rw [← hback, hkey, map_zero]

end Generic

/-! ## The concrete maps -/

section Main

variable (f : C(Sph V, T))

/-- The second projection `C(C_f) → C(D_V)`. -/
def coneToD : coneAlg f →ₐ[ℂ] C(Ball V, ℂ) :=
  (AlgHom.snd ℂ C(T, ℂ) C(Ball V, ℂ)).comp (coneAlg f).val

@[simp] lemma coneToD_apply (a : coneAlg f) :
    coneToD f a = (a : C(T, ℂ) × C(Ball V, ℂ)).2 := rfl

/-- **The pull-back property** of the Milnor square `C(C_f) → C(T)`, `C(D_V) → C(S_V)`. -/
lemma milnor_pullback : ∀ x₁ x₂, (pullAlg f).toRingHom x₁ = (restrictSph (V := V)).toRingHom x₂ →
    ∃! x : coneAlg f, (coneToT f).toRingHom x = x₁ ∧ (coneToD f).toRingHom x = x₂ := by
  intro x₁ x₂ h
  have h' : (pullAlg f) x₁ = (restrictSph (V := V)) x₂ := h
  have hpoint : ∀ (y : Ball V) (hy : ‖(y : V)‖ = 1),
      x₂ y = x₁ (f ⟨(y : V), mem_sphere_one_iff.mpr hy⟩) := by
    intro y hy
    have := congrFun (congrArg (fun m : C(Sph V, ℂ) => (m : Sph V → ℂ)) h')
      (⟨(y : V), mem_sphere_one_iff.mpr hy⟩ : Sph V)
    simpa [pullAlg, restrictSph, sphIncl] using this.symm
  refine ⟨⟨(x₁, x₂), hpoint⟩, ⟨rfl, rfl⟩, ?_⟩
  rintro y ⟨hy1, hy2⟩
  exact Subtype.ext (Prod.ext hy1 hy2)

section

variable (y0 : Ball V) (hy0 : y0 ∈ bdry V)

/-- Part (1): middle exactness of `K₀(U) → K₀(C_f) → K₀(C(T))`. -/
theorem cone_exact_mid (t0 : T) :
    ∀ z : K0 (coneAlg f), K0.mapA (A := coneAlg f) (B := C(T, ℂ)) (coneToT f) z = 0 →
      ∃ w : K0 (Kpair V),
        K0.mapA (A := Kpair V) (B := ℂ) (augPair V y0) w = 0 ∧
        K0.mapA (A := Kpair V) (B := coneAlg f) (relToCone f y0 hy0) w = z := by
  exact transport_mid (U f y0 hy0) (sigma f y0 hy0) (coneToT f) (eps f y0 hy0 t0)
    (augPair V y0) (eps_comp_sigma f y0 hy0 t0) (relToCone f y0 hy0) (val_comp_sigma f y0 hy0)
    (milnor_mid (coneToT f) (coneToT_surjective f) (U f y0 hy0) (mem_U_iff f y0 hy0)
      (eps f y0 hy0 t0) (fun u => coneToT_val_eq_ofId_eps f y0 hy0 t0 u))

/-- Part (3): injectivity of `K₀(U)_red → K₀(C_f)`, given stable lifting of invertible matrices
over `C(T)` along `coneToT f`. -/
theorem cone_exact_inj (t0 : T)
    (hlift : ∀ (n : ℕ) (u : Matrix (Fin n) (Fin n) C(T, ℂ)), IsUnit u →
      ∃ (k : ℕ) (v : Matrix (Fin (n + k)) (Fin (n + k)) (coneAlg f)), IsUnit v ∧
        v.map (coneToT f) = Matrix.reindex finSumFinEquiv finSumFinEquiv
          (Matrix.fromBlocks u 0 0 1)) :
    ∀ w : K0 (Kpair V), K0.mapA (A := Kpair V) (B := ℂ) (augPair V y0) w = 0 →
      K0.mapA (A := Kpair V) (B := coneAlg f) (relToCone f y0 hy0) w = 0 → w = 0 := by
  exact transport_inj (U f y0 hy0) (sigma f y0 hy0) (eps f y0 hy0 t0) (augPair V y0)
    (eps_comp_sigma f y0 hy0 t0) (relToCone f y0 hy0) (val_comp_sigma f y0 hy0)
    (milnor_inj (coneToT f) (coneToT_surjective f) (U f y0 hy0) (mem_U_iff f y0 hy0)
      (eps f y0 hy0 t0) (fun u => coneToT_val_eq_ofId_eps f y0 hy0 t0 u) hlift)

end

/-- Part (2): classes of `C(T)` whose pull-back along `f` is constant extend to the cone. -/
theorem cone_exact_lift :
    ∀ (z : K0 C(T, ℂ)) (c : K0 ℂ),
      K0.mapA (A := C(T, ℂ)) (B := C(Sph V, ℂ)) (pullAlg f) z
        = K0.mapA (A := ℂ) (B := C(Sph V, ℂ)) (Algebra.ofId ℂ C(Sph V, ℂ)) c →
        ∃ a : K0 (coneAlg f),
          K0.mapA (A := coneAlg f) (B := C(T, ℂ)) (coneToT f) a = z := by
  intro z c hc
  have hconst : (restrictSph (V := V)).comp (Algebra.ofId ℂ C(Ball V, ℂ))
      = Algebra.ofId ℂ C(Sph V, ℂ) :=
    AlgHom.ext fun x => ContinuousMap.ext fun _ => rfl
  have hcomp : K0.map (pullAlg f).toRingHom z
      = K0.map (restrictSph (V := V)).toRingHom
          (K0.mapA (A := ℂ) (B := C(Ball V, ℂ)) (Algebra.ofId ℂ C(Ball V, ℂ)) c) := by
    have h2 : K0.map (restrictSph (V := V)).toRingHom
          (K0.mapA (A := ℂ) (B := C(Ball V, ℂ)) (Algebra.ofId ℂ C(Ball V, ℂ)) c)
        = K0.mapA (A := C(T, ℂ)) (B := C(Sph V, ℂ)) (pullAlg f) z := by
      rw [map_eq_mapA (restrictSph (V := V)), ← AddMonoidHom.comp_apply, ← mapA_comp', hconst]
      exact hc.symm
    rw [h2]
  obtain ⟨a, ha1, _ha2⟩ := milnor_square (coneAlg f) C(T, ℂ) C(Ball V, ℂ) C(Sph V, ℂ)
    (coneToT f).toRingHom (coneToD f).toRingHom (pullAlg f).toRingHom
    (restrictSph (V := V)).toRingHom (restrictSph_surjective (V := V))
    (by
      apply RingHom.ext
      intro x
      apply ContinuousMap.ext
      intro y
      have hy' : ‖((sphIncl V y : Ball V) : V)‖ = 1 := by
        rw [sphIncl_coe]
        exact mem_sphere_one_iff.mp y.2
      have h := x.2 (sphIncl V y) hy'
      have h' : (x : C(T, ℂ) × C(Ball V, ℂ)).2 (sphIncl V y)
          = (x : C(T, ℂ) × C(Ball V, ℂ)).1 (f y) := by
        have hy'' : (⟨((sphIncl V y : Ball V) : V),
            mem_sphere_zero_iff_norm.mpr hy'⟩ : Sph V) = y := Subtype.ext rfl
        rw [h, hy'']
      simp only [RingHom.comp_apply, AlgHom.toRingHom_eq_coe, AlgHom.coe_toRingHom,
        StarAlgHom.coe_toAlgHom, ContinuousMap.compStarAlgHom'_apply, ContinuousMap.comp_apply,
        pullAlg]
      have hC1 : (coneToT f) x = (x : C(T, ℂ) × C(Ball V, ℂ)).1 := by
        simp only [coneToT, AlgHom.comp_apply, AlgHom.fst_apply, Subalgebra.coe_val]
      have hC2 : (coneToD f) x = (x : C(T, ℂ) × C(Ball V, ℂ)).2 := by
        simp only [coneToD, AlgHom.comp_apply, AlgHom.snd_apply, Subalgebra.coe_val]
      have hR : (restrictSph (V := V)) ((coneToD f) x) = ((coneToD f) x).comp (sphIncl V) := by
        simp only [restrictSph, pullAlg, StarAlgHom.coe_toAlgHom,
          ContinuousMap.compStarAlgHom'_apply]
      rw [hR, ContinuousMap.comp_apply, hC1, hC2, ← h'])
    (milnor_pullback f) z (K0.mapA (A := ℂ) (B := C(Ball V, ℂ))
      (Algebra.ofId ℂ C(Ball V, ℂ)) c) hcomp
  exact ⟨a, ha1⟩

section

variable (y0 : Ball V) (hy0 : y0 ∈ bdry V)

end

end Main

end

end Work.KT.Cone
