import Mathlib

namespace Work.ANALYTIC.CechPt

/-- All `ℤ`-module structures on an additive commutative group are equal, so freeness can be
transported between them.  This is used to compare the canonical `AddCommGroup.toIntModule`
structure (which is what type class search produces for a subtype such as a kernel) with the
structure inherited from a submodule (`Submodule.module`). -/
theorem moduleFree_of_module_int_eq {M : Type*} [AddCommGroup M]
    (I₁ I₂ : Module ℤ M) (h : I₁ = I₂) (hf : @Module.Free ℤ M _ _ I₁) :
    @Module.Free ℤ M _ _ I₂ :=
  h ▸ hf

/-- Contraction data for a bounded-below exact complex of `ℤ`-modules whose kernels are free.

Given `0 → ℤ --aug--> A 0 --d 0--> A 1 --d 1--> ⋯` exact (`range = ker`, with `aug` injective) and
each kernel `LinearMap.ker (d p)` free, there are linear maps `h p : A (p+1) →ₗ[ℤ] A p` and
`h0 : A 0 →ₗ[ℤ] ℤ` satisfying the chain-contraction identities of the augmented complex.

Construction: with `Z p = ker (d p) = range (d (p-1))`, choose a section `s p : Z (p+1) → A p` of
`d p` (exists because `Z (p+1)` is free: prescribe it on a basis); then `A p = Z p ⊕ im (s p)`
via `a ↦ (a - s p (d p a), d p a)`, and one sets `h p = s p ∘ proj` with `proj : A (p+1) → Z (p+1)`
the projection of the decomposition, `h 0 = ` the inverse of the isomorphism `aug : ℤ ≅ Z 0`, and
`h0 = ` the retraction of `aug` onto the `Z 0`-summand of `A 0 = Z 0 ⊕ im (s 0)`. -/
theorem contraction_of_exact (A : ℕ → Type*) [∀ p, AddCommGroup (A p)] [∀ p, Module ℤ (A p)]
    (d : ∀ p, A p →ₗ[ℤ] A (p + 1)) (aug : ℤ →ₗ[ℤ] A 0)
    (haug : Function.Injective aug)
    (hex0 : LinearMap.range aug = LinearMap.ker (d 0))
    (hex : ∀ p : ℕ, LinearMap.range (d p) = LinearMap.ker (d (p + 1)))
    (hfree : ∀ p : ℕ, Module.Free ℤ (LinearMap.ker (d p))) :
    ∃ (h : ∀ p : ℕ, A (p + 1) →ₗ[ℤ] A p) (h0 : A 0 →ₗ[ℤ] ℤ),
      (h0.comp aug = LinearMap.id) ∧
      ((h 0).comp (d 0) + aug.comp h0 = LinearMap.id) ∧
      (∀ p : ℕ, (h (p + 1)).comp (d (p + 1)) + (d p).comp (h p) = LinearMap.id) := by
  classical
  -- All the kernels carry the `ℤ`-module structure inherited from `A p`; this is the structure
  -- which `LinearMap.codRestrict` produces, so we fix it once and for all.
  letI Zmod : ∀ p : ℕ, Module ℤ ↥(LinearMap.ker (d p)) :=
    fun p => Submodule.module (LinearMap.ker (d p))
  -- Freeness transported to that structure.
  have hfreeZ : ∀ p : ℕ, @Module.Free ℤ ↥(LinearMap.ker (d p)) _ _ (Zmod p) :=
    fun p => moduleFree_of_module_int_eq _ _ (Subsingleton.elim _ _) (hfree p)
  haveI : ∀ p : ℕ, Module.Free ℤ ↥(LinearMap.ker (d p)) := hfreeZ
  -- Exactness, in the two directions we need.
  have hrange_le_ker : ∀ p : ℕ, LinearMap.range (d p) ≤ LinearMap.ker (d (p + 1)) :=
    fun p => le_of_eq (hex p)
  have hker_le_range : ∀ p : ℕ, LinearMap.ker (d (p + 1)) ≤ LinearMap.range (d p) :=
    fun p => le_of_eq (hex p).symm
  have hmem_ker : ∀ (p : ℕ) (a : A p), d p a ∈ LinearMap.ker (d (p + 1)) :=
    fun p a => hrange_le_ker p (LinearMap.mem_range.mpr ⟨a, rfl⟩)
  -- ### Step 1: sections of `d p` onto `ker (d (p+1))`
  have hs : ∀ p : ℕ, ∃ s : ↥(LinearMap.ker (d (p + 1))) →ₗ[ℤ] A p,
      ∀ x : ↥(LinearMap.ker (d (p + 1))), d p (s x) = (x : A (p + 1)) := by
    intro p
    haveI : Module.Projective ℤ ↥(LinearMap.ker (d (p + 1))) := Module.Projective.of_free
    let f : A p →ₗ[ℤ] ↥(LinearMap.ker (d (p + 1))) :=
      (d p).codRestrict (LinearMap.ker (d (p + 1))) (fun a => hmem_ker p a)
    have hsurj : LinearMap.range f = ⊤ := by
      rw [LinearMap.range_eq_top]
      intro x
      obtain ⟨a, ha⟩ := LinearMap.mem_range.mp (hker_le_range p x.2)
      exact ⟨a, Subtype.ext (by simpa only [f, LinearMap.codRestrict_apply] using ha)⟩
    obtain ⟨s, hs'⟩ := LinearMap.exists_rightInverse_of_surjective f hsurj
    refine ⟨s, fun x => ?_⟩
    have h1 : f (s x) = x := by
      have h2 := congrArg
        (fun g : ↥(LinearMap.ker (d (p + 1))) →ₗ[ℤ] ↥(LinearMap.ker (d (p + 1))) => g x) hs'
      simpa only [LinearMap.comp_apply, LinearMap.id_apply] using h2
    have h3 : (f (s x) : A (p + 1)) = (x : A (p + 1)) :=
      congrArg (fun y : ↥(LinearMap.ker (d (p + 1))) => (y : A (p + 1))) h1
    simpa only [f, LinearMap.codRestrict_apply] using h3
  choose sec hsec using hs
  -- ### Step 2: `D p`, the differential viewed as a map into the kernel
  have hDex : ∀ p : ℕ, ∃ D : A p →ₗ[ℤ] ↥(LinearMap.ker (d (p + 1))),
      ∀ a : A p, (D a : A (p + 1)) = d p a :=
    fun p => ⟨(d p).codRestrict (LinearMap.ker (d (p + 1))) (fun a => hmem_ker p a),
      fun a => rfl⟩
  choose D hD using hDex
  -- ### Step 3: the projection onto the kernel, along the chosen section
  have hPex : ∀ p : ℕ, ∃ P : A p →ₗ[ℤ] ↥(LinearMap.ker (d p)),
      ∀ a : A p, (P a : A p) = a - sec p (D p a) := by
    intro p
    refine ⟨LinearMap.codRestrict (LinearMap.ker (d p))
      ((LinearMap.id : A p →ₗ[ℤ] A p) - (sec p).comp (D p)) (fun a => ?_), fun a => ?_⟩
    · rw [LinearMap.mem_ker]
      have h1 : d p (((LinearMap.id : A p →ₗ[ℤ] A p) - (sec p).comp (D p)) a)
          = d p a - (D p a : A (p + 1)) := by
        rw [LinearMap.sub_apply, LinearMap.id_apply, LinearMap.comp_apply, map_sub,
          hsec p (D p a)]
      rw [h1, hD p a, sub_self]
    · simp only [LinearMap.codRestrict_apply, LinearMap.sub_apply, LinearMap.id_apply,
        LinearMap.comp_apply]
  choose P hP using hPex
  -- ### Step 4: the augmentation, as an isomorphism onto `ker (d 0)`
  have haugmem : ∀ z : ℤ, aug z ∈ LinearMap.ker (d 0) := by
    intro z
    rw [← hex0]
    exact LinearMap.mem_range.mpr ⟨z, rfl⟩
  let e : ℤ ≃ₗ[ℤ] ↥(LinearMap.ker (d 0)) :=
    (LinearEquiv.ofInjective aug haug).trans
      (LinearEquiv.ofEq (LinearMap.range aug) (LinearMap.ker (d 0)) hex0)
  have he : ∀ z : ℤ, (e z : A 0) = aug z := by
    intro z
    simp only [e, LinearEquiv.trans_apply, LinearEquiv.coe_ofEq_apply,
      LinearEquiv.ofInjective_apply]
  have he_symm : ∀ y : ↥(LinearMap.ker (d 0)), aug (e.symm y) = (y : A 0) := by
    intro y
    rw [← he (e.symm y), LinearEquiv.apply_symm_apply]
  -- ### Step 5: `h` and `h0`
  have h0ex : ∃ h0 : A 0 →ₗ[ℤ] ℤ, ∀ a : A 0, h0 a = e.symm (P 0 a) :=
    ⟨e.symm.comp (P 0), fun a => rfl⟩
  choose h0 hh0 using h0ex
  have hhex : ∃ h : ∀ p : ℕ, A (p + 1) →ₗ[ℤ] A p,
      ∀ p : ℕ, h p = (sec p).comp (P (p + 1)) :=
    ⟨fun p => (sec p).comp (P (p + 1)), fun p => rfl⟩
  choose h hh using hhex
  -- ### The key computation: the projection of a differential lands in the previous kernel
  have hPd : ∀ (q : ℕ) (a : A q), P (q + 1) (d q a) = D q a := by
    intro q a
    apply Subtype.ext
    rw [hP (q + 1) (d q a)]
    have hDzero : D (q + 1) (d q a) = 0 := by
      apply Subtype.ext
      rw [hD (q + 1) (d q a), LinearMap.mem_ker.mp (hmem_ker q a)]
      simp
    rw [hDzero, map_zero, sub_zero, hD q a]
  -- ### The three contraction identities
  have h0aug : h0.comp aug = LinearMap.id := by
    apply LinearMap.ext
    intro z
    rw [LinearMap.comp_apply, LinearMap.id_apply, hh0]
    have hPe : P 0 (aug z) = e z := by
      apply Subtype.ext
      have hDzero : D 0 (aug z) = 0 := by
        apply Subtype.ext
        rw [hD 0 (aug z), LinearMap.mem_ker.mp (haugmem z)]
        simp
      rw [hP 0 (aug z), hDzero, map_zero, sub_zero]
      exact (he z).symm
    rw [hPe, LinearEquiv.symm_apply_apply]
  have hbase : (h 0).comp (d 0) + aug.comp h0 = LinearMap.id := by
    apply LinearMap.ext
    intro a
    rw [LinearMap.add_apply, LinearMap.comp_apply, LinearMap.comp_apply, hh 0,
      LinearMap.comp_apply, hPd 0 a, hh0, he_symm (P 0 a), hP 0 a, LinearMap.id_apply]
    exact add_sub_cancel _ _
  have hchain : ∀ p : ℕ, (h (p + 1)).comp (d (p + 1)) + (d p).comp (h p) = LinearMap.id := by
    intro p
    apply LinearMap.ext
    intro a
    rw [LinearMap.add_apply, LinearMap.comp_apply, LinearMap.comp_apply, hh (p + 1),
      LinearMap.comp_apply, hPd (p + 1) a, hh p, LinearMap.comp_apply, hsec p (P (p + 1) a),
      hP (p + 1) a, LinearMap.id_apply]
    exact add_sub_cancel _ _
  exact ⟨h, h0, h0aug, hbase, hchain⟩

end Work.ANALYTIC.CechPt
