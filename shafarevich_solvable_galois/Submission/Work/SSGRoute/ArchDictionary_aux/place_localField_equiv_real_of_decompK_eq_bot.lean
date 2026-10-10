import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.Flat.TorsionFree
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.NumberTheory.NumberField.Completion.InfinitePlace
import Submission.Work.SSGRoute.DualMod.Main
import Submission.Work.SSGRoute.Interfaces
import Submission.Work.SSGRoute.PTDefs
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# The completion at a linked archimedean place with trivial decomposition group is `ℝ`

Let `k` be a number field, `Ω` an algebraic closure of `k`, `K/k` a finite Galois extension inside
`Ω`, and `c ∈ Gal(Ω/k)` a nontrivial involution which is the complex conjugation for some embedding
`φ : Ω →+* ℂ`, i.e. `φ (c x) = conj (φ x)` for all `x ∈ Ω`.  Let `w` be the infinite place of `K`
induced by `φ ∘ (K ↪ Ω)`.  If the decomposition group of `w` is trivial, then `K_w ≅ ℝ` and the
isomorphism is compatible with `φ`.

The point is that `res c ∈ Gal(K/k)` always stabilises that place `w`: the involution `c` acts on
`K` as the complex conjugation for `φ|_K`, hence fixes the infinite place defined by `φ|_K`.  If
`w` has trivial decomposition group, the restriction of `c` to `K` is therefore `1`, so `c` fixes
every element of `K`; applying `φ` we get `φ|_K = conj ∘ φ|_K`, i.e. `φ|_K` is real valued and the
place `w` is a *real* place.  The completion of `K` at a real place is `ℝ`
(`NumberField.InfinitePlace.Completion.ringEquivRealOfIsReal`), with the desired compatibility.

Note the hypothesis `hc1 : c ≠ 1` is not needed for this implication (it is part of the interface
of the linked-place construction, where it guarantees that `φ` is not real valued on `Ω`).
-/

namespace Work.SSGRoute.ArchDictionary_aux

open NumberField

theorem place_localField_equiv_real_of_decompK_eq_bot (p : ℕ) [Fact p.Prime] (k Ω : Type) [Field k]
    [NumberField k] [Field Ω] [Algebra k Ω] [IsAlgClosure k Ω] (K : IntermediateField k Ω)
    [FiniteDimensional k K] [IsGalois k K] [NumberField ↥K]
    (c : Ω ≃ₐ[k] Ω) (hc2 : c ^ 2 = 1) (hc1 : c ≠ 1) (φ : Ω →+* ℂ)
    (hlink : ∀ x : Ω, φ (c x) = starRingEnd ℂ (φ x))
    (w : NK.GlobalCFT.Place ↥K)
    (hw : w = NK.GlobalCFT.Place.ofInfinite (NumberField.InfinitePlace.mk (φ.comp (algebraMap ↥K Ω))))
    (hbot : SSGRoute.PTExt.decompK (k := k) w = ⊥) :
    ∃ e : NK.GlobalCFT.Place.localField ↥K w ≃+* ℝ,
      ∀ x : ↥K, e (algebraMap ↥K (NK.GlobalCFT.Place.localField ↥K w) x) = φ (algebraMap ↥K Ω x) := by
  classical
  -- The embedding and the infinite place defining `w` (`set` also folds them in `hw`).
  set ψ : ↥K →+* ℂ := φ.comp (algebraMap ↥K Ω) with hψ
  set v : NumberField.InfinitePlace ↥K := NumberField.InfinitePlace.mk ψ with hv
  -- `res c` is an involution of `Gal(K/k)`.
  have hcmul : c * c = 1 := by rw [← pow_two]; exact hc2
  have hresmul : SSGRoute.res k K c * SSGRoute.res k K c = 1 := by
    rw [← map_mul, hcmul, map_one]
  have hressymm : (SSGRoute.res k K c).symm = SSGRoute.res k K c :=
    inv_eq_of_mul_eq_one_left hresmul
  -- `res c` acts on `K ⊆ Ω` as `c`.
  have hres_apply : ∀ y : ↥K,
      (algebraMap ↥K Ω) ((SSGRoute.res k K c) y) = c ((algebraMap ↥K Ω) y) := by
    intro y
    simpa [SSGRoute.res] using AlgEquiv.restrictNormalHom_apply (F := k) K c y
  -- Hence it is the complex conjugation for `ψ`.
  have hconj : ψ.comp ((SSGRoute.res k K c : ↥K ≃ₐ[k] ↥K) : ↥K →+* ↥K) =
      NumberField.ComplexEmbedding.conjugate ψ := by
    ext y
    show φ ((algebraMap ↥K Ω) ((SSGRoute.res k K c) y)) = starRingEnd ℂ (φ ((algebraMap ↥K Ω) y))
    rw [hres_apply y, hlink]
  -- So `res c` stabilises the infinite place `v`, hence the place `w = ofInfinite v`.
  have hstabv : (SSGRoute.res k K c) • v = v := by
    rw [hv, NumberField.InfinitePlace.smul_mk, hressymm, hconj,
      NumberField.InfinitePlace.mk_conjugate_eq]
  have hstab : SSGRoute.res k K c ∈ SSGRoute.PTExt.decompK (k := k) w := by
    rw [show SSGRoute.PTExt.decompK (k := k) w =
        MulAction.stabilizer (↥K ≃ₐ[k] ↥K) w from rfl, MulAction.mem_stabilizer_iff]
    rw [hw, NK.GlobalCFT.Place.smul_ofInfinite, NK.GlobalCFT.Place.ofInfinite_inj]
    exact hstabv
  -- The decomposition group of `w` is trivial, so `res c = 1`.
  have hres1 : SSGRoute.res k K c = 1 := by
    have hmem : SSGRoute.res k K c ∈ (⊥ : Subgroup (↥K ≃ₐ[k] ↥K)) := by
      rw [← hbot]
      exact hstab
    simpa using hmem
  -- Therefore `c` fixes `K ⊆ Ω` pointwise and `ψ` is real valued.
  have hfixK : ∀ y : ↥K, c ((algebraMap ↥K Ω) y) = (algebraMap ↥K Ω) y := by
    intro y
    rw [← hres_apply y, hres1]
    rfl
  have hψreal : NumberField.ComplexEmbedding.IsReal ψ := by
    rw [NumberField.ComplexEmbedding.isReal_iff]
    ext y
    simp only [NumberField.ComplexEmbedding.conjugate_coe_eq, RingHom.comp_apply, hψ]
    rw [← hlink ((algebraMap ↥K Ω) y), hfixK y]
  -- The place `w` is real, and its completion is `ℝ`.
  have hvreal : v.IsReal := ⟨ψ, hψreal, hv.symm⟩
  have hvemb : v.embedding = ψ := by
    rw [hv]
    exact NumberField.InfinitePlace.embedding_mk_eq_of_isReal hψreal
  rw [hw]
  refine ⟨NumberField.InfinitePlace.Completion.ringEquivRealOfIsReal hvreal, ?_⟩
  intro x
  simp only [NumberField.InfinitePlace.Completion.ringEquivRealOfIsReal_apply,
    NumberField.InfinitePlace.Completion.extensionEmbeddingOfIsReal_apply]
  -- The embedding `K →+* ℝ` given by the completion is `φ` on `K`.
  rw [show NumberField.InfinitePlace.Completion.extensionEmbedding v
      (algebraMap ↥K (NK.GlobalCFT.Place.localField ↥K (NK.GlobalCFT.Place.ofInfinite v)) x)
      = v.embedding x from by
    simp [NumberField.InfinitePlace.Completion.algebraMap_apply,
      NumberField.InfinitePlace.Completion.extensionEmbedding_coe]]
  rw [hvemb, hψ]
  rfl

end Work.SSGRoute.ArchDictionary_aux
