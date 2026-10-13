import Mathlib
import Submission.Work.DSFFP.Defs

open TensorProduct

namespace Work.DSFFP

universe u

/-- The hypothesis `h1` of the local flatness criterion (`I ⊗[S] T → T` injective) is equivalent
to the injectivity of `I ⊗[S] T → S ⊗[S] T`: the two are intertwined by `S ⊗[S] T ≃ₗ[S] T`. -/
lemma injective_rTensor_subtype_of_idxInj {S : Type u} [CommRing S] (I : Ideal S) (T : Type u)
    [AddCommGroup T] [Module S T] (h1 : IdxInj I T) :
    Function.Injective (I.subtype.rTensor T) := by
  have hL : (TensorProduct.lid S T).toLinearMap ∘ₗ (I.subtype.rTensor T)
      = TensorProduct.lift ((LinearMap.lsmul S T).comp I.subtype) := by
    apply TensorProduct.ext'
    intro i t
    simp [TensorProduct.lid_tmul, LinearMap.lsmul_apply, LinearMap.rTensor_tmul]
  intro x y hxy
  apply h1
  have key : ∀ z, (TensorProduct.lid S T).toLinearMap ((I.subtype.rTensor T) z)
      = TensorProduct.lift ((LinearMap.lsmul S T).comp I.subtype) z :=
    fun z => LinearMap.congr_fun hL z
  rw [← key x, ← key y, hxy]

/-- **Base case of the local flatness criterion (Stacks 10.99.8, tag 051C)**: if the cokernel `Q ⧸ A` of `A` in `Q` is the quotient `S ⧸ I` (witnessed by a surjective `φ : Q →ₗ[S] S ⧸ I` with `ker φ = A`), and if the canonical map `I ⊗[S] T → T` is injective (`h1`), then the inclusion `A ↪ Q` stays injective after `⊗[S] T`.

PLAN for the prover.  Pull back `Q ↠ Q ⧸ A ≅ S ⧸ I` along `S ↠ S ⧸ I`: set `P := {p : Q × S // φ p.1 = Ideal.Quotient.mk I p.2} ⊆ Q × S`.  Then `0 → A → P → S → 0` and `0 → I → P → Q → 0` are exact (kernels by construction; both surjective since `φ` and `S → S ⧸ I` are).  The first sequence splits: choose `p₀ = (q₀, 1) ∈ P`; then `(q,s) ↦ (q - s • q₀, 0) + s • p₀` shows `P = A ⊕ S • p₀`, so the inclusion `A ↪ P` is a split inclusion and `TPure T (A ↪ P)` follows from `TPure.of_retract` (retraction `(q,s) ↦ q - s • q₀`).  Now let `z ∈ A ⊗ T` have image `0` in `Q ⊗ T`.  Its image `y ∈ P ⊗ T` lies in `ker (P ⊗ T → Q ⊗ T) = range (I ⊗ T → P ⊗ T)` by right exactness of `⊗`.  The composite `A → P → S` is zero, so `y` maps to `0` in `S ⊗ T`; the composite `I ⊗ T → P ⊗ T → S ⊗ T ≅ T` is exactly the map `I ⊗ T → T` of `h1`, which is injective, so the preimage of `y` in `I ⊗ T` is `0` and hence `y = 0`.  Since `A ↪ P` is `T`-pure, `z = 0`.

PROOF AS FORMALISED.  Instead of the submodule `P ⊆ Q × S` we use the linearly isomorphic
`A × S` (the isomorphism sends `(a,s)` to `(a + s • q₀, s)` with `q₀` a lift of `1 ∈ S ⧸ I`), which
makes all structure maps explicit:

* `ιA : A →ₗ A × S`, `a ↦ (a, 0)` (the inclusion);
* `πQ : A × S →ₗ Q`, `(a, s) ↦ a + s • q₀` (kernel `{(-s • q₀, s) : s ∈ I}`);
* `ιI : I →ₗ A × S`, `s ↦ (-s • q₀, s)`;
* `πS : A × S →ₗ S`, `(a, s) ↦ s`; `ρ : A × S →ₗ A`, `(a, s) ↦ a`.

Then `πQ ∘ ιA = A.subtype`, `πS ∘ ιA = 0`, `πS ∘ ιI = I.subtype`, `ρ ∘ ιA = id` and the sequence
`I → A × S → Q` is exact with `πQ` surjective, so by right exactness of `⊗[S] T` the sequence
`I ⊗ T → (A × S) ⊗ T → Q ⊗ T` is exact.  The rest is the argument above. -/
theorem tpure_of_coker_quot {S : Type _} [CommRing S] (I : Ideal S) {Q : Type _} [AddCommGroup Q]
    [Module S Q] (A : Submodule S Q) (φ : Q →ₗ[S] (S ⧸ I)) (hφ : LinearMap.ker φ = A)
    (hφs : Function.Surjective φ) (T : Type _) [AddCommGroup T] [Module S T]
    (h1 : Work.DSFFP.IdxInj I T) : Work.DSFFP.TPure T A.subtype := by
  have h1' : Function.Injective (I.subtype.rTensor T) :=
    injective_rTensor_subtype_of_idxInj I T h1
  obtain ⟨q₀, hq₀⟩ : ∃ q : Q, φ q = 1 := hφs 1
  have h1q : Submodule.mkQ I (1 : S) = (1 : S ⧸ I) := by simp
  have hmk : ∀ s : S, Submodule.mkQ I s = s • (1 : S ⧸ I) := by
    intro s
    have h : Submodule.mkQ I s = Submodule.mkQ I (s • (1 : S)) := by simp
    rw [h, map_smul, h1q]
  have hκmem : ∀ i : I, (LinearMap.toSpanSingleton S Q (-q₀)).comp I.subtype i ∈ A := by
    intro i
    rw [← hφ, LinearMap.mem_ker, LinearMap.comp_apply, LinearMap.toSpanSingleton_apply,
      map_smul, map_neg, hq₀, smul_neg, neg_eq_zero, Submodule.subtype_apply,
      ← hmk (i : S), Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero]
    exact i.2
  let κ : I →ₗ[S] A :=
    LinearMap.codRestrict A ((LinearMap.toSpanSingleton S Q (-q₀)).comp I.subtype) hκmem
  let ιA : A →ₗ[S] A × S := LinearMap.inl S A S
  let ιI : I →ₗ[S] A × S := LinearMap.prod κ I.subtype
  let πQ : A × S →ₗ[S] Q := LinearMap.coprod A.subtype (LinearMap.toSpanSingleton S Q q₀)
  let πS : A × S →ₗ[S] S := LinearMap.snd S A S
  let ρ : A × S →ₗ[S] A := LinearMap.fst S A S
  have hκ_apply : ∀ i : I, (κ i : Q) = -((i : S) • q₀) := by
    intro i
    have h1 : ((κ i : A) : Q) = (LinearMap.toSpanSingleton S Q (-q₀)).comp I.subtype i :=
      LinearMap.codRestrict_apply A _ i
    rw [h1, LinearMap.comp_apply, LinearMap.toSpanSingleton_apply, Submodule.subtype_apply]
    simp
  have hπQ_apply : ∀ x : A × S, πQ x = (x.1 : Q) + x.2 • q₀ := by
    intro x
    simp only [πQ, LinearMap.coprod_apply, LinearMap.toSpanSingleton_apply, Submodule.subtype_apply]
  have hιI_apply : ∀ i : I, ιI i = (κ i, (i : S)) := by
    intro i
    simp only [ιI, LinearMap.prod_apply, Function.prod, Submodule.subtype_apply]
  have hιA_apply : ∀ a : A, ιA a = (a, 0) := by
    intro a; simp only [ιA, LinearMap.inl_apply]
  have hsurj : Function.Surjective πQ := by
    intro q
    obtain ⟨s, hs⟩ := Submodule.mkQ_surjective I (φ q)
    refine ⟨(⟨q - s • q₀, ?_⟩, s), ?_⟩
    · rw [← hφ, LinearMap.mem_ker, map_sub, map_smul, hq₀, ← hmk s, hs, sub_self]
    · rw [hπQ_apply]; simp
  have hker : πQ.ker = ιI.range := by
    apply le_antisymm
    · intro x hx
      rw [LinearMap.mem_ker] at hx
      rw [LinearMap.mem_range]
      have hx0 : (x.1 : Q) + x.2 • q₀ = 0 := by rw [← hπQ_apply]; exact hx
      have hx1 : (x.1 : Q) = -(x.2 • q₀) := eq_neg_iff_add_eq_zero.mpr hx0
      have hmem : x.2 ∈ I := by
        have hφx1 : φ (x.1 : Q) = 0 := by
          have : (x.1 : Q) ∈ LinearMap.ker φ := by rw [hφ]; exact x.1.2
          exact LinearMap.mem_ker.mp this
        have h2 : φ (-(x.2 • q₀)) = 0 := by rw [← hx1]; exact hφx1
        have h3 : x.2 • (1 : S ⧸ I) = 0 := by
          rw [map_neg, map_smul, hq₀] at h2
          exact neg_eq_zero.mp h2
        rw [← Submodule.Quotient.mk_eq_zero, ← Submodule.mkQ_apply, hmk x.2]
        exact h3
      refine ⟨⟨x.2, hmem⟩, ?_⟩
      have hκx : κ ⟨x.2, hmem⟩ = x.1 := Subtype.ext (by rw [hκ_apply, hx1])
      rw [hιI_apply, hκx]
    · intro x hx
      rw [LinearMap.mem_range] at hx
      obtain ⟨i, rfl⟩ := hx
      rw [LinearMap.mem_ker, hπQ_apply, hιI_apply]
      simp [hκ_apply]
  have hexact : Function.Exact ιI πQ := LinearMap.exact_iff.mpr hker
  have hπQιA : πQ ∘ₗ ιA = A.subtype := by
    ext a
    rw [LinearMap.comp_apply, hιA_apply, hπQ_apply]
    simp
  have hπSιA : πS ∘ₗ ιA = 0 := by
    ext a; simp [πS, ιA]
  have hπSιI : πS ∘ₗ ιI = I.subtype := by
    ext i; simp [πS, hιI_apply]
  have hρ : ρ ∘ₗ ιA = LinearMap.id := by
    simp only [ρ, ιA]; exact LinearMap.fst_comp_inl S A S
  have hpure : Work.DSFFP.TPure T ιA := Work.DSFFP.TPure.of_retract hρ
  rw [Work.DSFFP.TPure, ← LinearMap.ker_eq_bot, Submodule.eq_bot_iff]
  intro z hz
  have hz0 : A.subtype.rTensor T z = 0 := LinearMap.mem_ker.mp hz
  have hmem2 : ιA.rTensor T z ∈ LinearMap.ker (πQ.rTensor T) := by
    rw [LinearMap.mem_ker]
    change ((LinearMap.rTensor T πQ) ∘ₗ (LinearMap.rTensor T ιA)) z = 0
    rw [← LinearMap.rTensor_comp, hπQιA, hz0]
  rw [Function.Exact.linearMap_ker_eq (rTensor_exact T hexact hsurj), LinearMap.mem_range] at hmem2
  obtain ⟨w, hw⟩ := hmem2
  have key : I.subtype.rTensor T w = 0 := by
    have hA : πS.rTensor T (ιA.rTensor T z) = 0 := by
      change ((LinearMap.rTensor T πS) ∘ₗ (LinearMap.rTensor T ιA)) z = 0
      rw [← LinearMap.rTensor_comp, hπSιA]
      simp
    have hI : πS.rTensor T (ιI.rTensor T w) = I.subtype.rTensor T w := by
      change ((LinearMap.rTensor T πS) ∘ₗ (LinearMap.rTensor T ιI)) w
        = (LinearMap.rTensor T I.subtype) w
      rw [← LinearMap.rTensor_comp, hπSιI]
    rw [← hI, hw, hA]
  have hw0 : w = 0 := h1' key
  have hy0 : ιA.rTensor T z = 0 := by rw [← hw, hw0, map_zero]
  exact hpure (by rw [hy0, map_zero])

end Work.DSFFP
