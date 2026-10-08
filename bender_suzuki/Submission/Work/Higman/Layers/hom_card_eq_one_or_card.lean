import Mathlib
import Submission.Work.Higman.Layers.Defs

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.style.haveILetI false

noncomputable section

namespace Work.Higman.Layers

variable {V : Type*} [AddCommGroup V] [Module (ZMod 2) V]

/-! ## Basic facts about `restrictInv` and `cycSpan` -/

private theorem restrictInv_apply {σ : V →ₗ[ZMod 2] V} {C : Submodule (ZMod 2) V}
    (hC : IsInv σ C) (y : C) : ((restrictInv σ C hC y : C) : V) = σ y.1 := rfl

private theorem restrictInv_pow_apply {σ : V →ₗ[ZMod 2] V} {C : Submodule (ZMod 2) V}
    (hC : IsInv σ C) (k : ℕ) (y : C) : (((restrictInv σ C hC) ^ k) y : V) = (σ ^ k) y.1 := by
  induction k with
  | zero => simp
  | succ k ih =>
      rw [pow_succ', pow_succ', Module.End.mul_apply, Module.End.mul_apply, restrictInv_apply, ih]

private theorem inv_pow_mem {σ : V →ₗ[ZMod 2] V} {U : Submodule (ZMod 2) V} (hU : IsInv σ U) :
    ∀ k : ℕ, ∀ x : V, x ∈ U → (σ ^ k) x ∈ U := by
  intro k
  induction k with
  | zero => intro x hx; simpa using hx
  | succ k ih =>
      intro x hx
      rw [pow_succ', Module.End.mul_apply]
      exact hU _ (ih x hx)

private theorem isInv_cycSpan (σ : V →ₗ[ZMod 2] V) (v : V) : IsInv σ (cycSpan σ v) := by
  intro x hx
  have hmap : Submodule.map σ (cycSpan σ v) ≤ cycSpan σ v := by
    rw [cycSpan, Submodule.map_span]
    refine Submodule.span_le.mpr ?_
    rintro y ⟨z, ⟨k, rfl⟩, rfl⟩
    refine Submodule.subset_span ⟨k + 1, ?_⟩
    change (σ ^ (k + 1)) v = σ ((σ ^ k) v)
    rw [pow_succ', Module.End.mul_apply]
  exact hmap (Submodule.mem_map_of_mem hx)

/-- A non-zero vector of a `σ`-simple submodule generates it. -/
private theorem cycSpan_eq_of_simple {σ : V →ₗ[ZMod 2] V} {C : Submodule (ZMod 2) V}
    (hC : IsSimpleMod σ C) {v : C} (hv : v ≠ 0) : cycSpan σ (v : V) = C := by
  obtain ⟨hinv, -, hmin⟩ := hC
  have hle : cycSpan σ (v : V) ≤ C := by
    rw [cycSpan]
    refine Submodule.span_le.mpr ?_
    rintro x ⟨k, rfl⟩
    exact inv_pow_mem hinv k (v : V) v.2
  have hne : cycSpan σ (v : V) ≠ ⊥ := by
    intro h
    have hmem : (v : V) ∈ (⊥ : Submodule (ZMod 2) V) := by
      rw [← h]
      exact Submodule.subset_span ⟨0, by simp⟩
    exact hv (Subtype.ext (by simpa using hmem))
  rcases hmin _ hle (isInv_cycSpan σ (v : V)) with h | h
  · exact absurd h hne
  · exact h

/-! ## Equivariant maps agreeing on a generating vector -/

private theorem eq_of_apply_eq_of_gen {σ : V →ₗ[ZMod 2] V} {C D : Submodule (ZMod 2) V}
    (hC : IsInv σ C) (hD : IsInv σ D) {v : C} (hgen : cycSpan σ (v : V) = C)
    {φ ψ : C →ₗ[ZMod 2] D}
    (hφ : ∀ y : C, φ (restrictInv σ C hC y) = restrictInv σ D hD (φ y))
    (hψ : ∀ y : C, ψ (restrictInv σ C hC y) = restrictInv σ D hD (ψ y))
    (h : φ v = ψ v) : φ = ψ := by
  have hKinv : IsInv σ ((LinearMap.ker (φ - ψ)).map C.subtype) := by
    intro x hx
    rw [Submodule.mem_map] at hx ⊢
    obtain ⟨s, hs, rfl⟩ := hx
    refine ⟨restrictInv σ C hC s, ?_, restrictInv_apply hC s⟩
    rw [LinearMap.mem_ker] at hs ⊢
    rw [LinearMap.sub_apply, sub_eq_zero] at hs
    rw [LinearMap.sub_apply, sub_eq_zero, hφ s, hψ s, hs]
  have hvK : (v : V) ∈ (LinearMap.ker (φ - ψ)).map C.subtype := by
    rw [Submodule.mem_map]
    refine ⟨v, ?_, rfl⟩
    rw [LinearMap.mem_ker, LinearMap.sub_apply, sub_eq_zero]
    exact h
  have hle : cycSpan σ (v : V) ≤ (LinearMap.ker (φ - ψ)).map C.subtype := by
    rw [cycSpan]
    refine Submodule.span_le.mpr ?_
    rintro x ⟨k, rfl⟩
    exact inv_pow_mem hKinv k (v : V) hvK
  have hKC : (LinearMap.ker (φ - ψ)).map C.subtype = C :=
    le_antisymm (Submodule.map_subtype_le C _) ((le_of_eq hgen.symm).trans hle)
  refine LinearMap.ext fun s => ?_
  have hs : (s : V) ∈ (LinearMap.ker (φ - ψ)).map C.subtype := by
    rw [hKC]; exact s.2
  rw [Submodule.mem_map] at hs
  obtain ⟨t, ht, htval⟩ := hs
  have htt : t = s := Subtype.ext htval
  rw [← htt]
  rw [LinearMap.mem_ker, LinearMap.sub_apply, sub_eq_zero] at ht
  exact ht

/-! ## The space of equivariant maps as a submodule -/

/-- The `σ`-equivariant linear maps `C₂ → C₁`, as a submodule of the space of linear maps.
Its underlying type is definitionally `HomInv σ C₂ C₁ hC₂ hC₁`. -/
private def HomInvSub (σ : V →ₗ[ZMod 2] V) (C₂ C₁ : Submodule (ZMod 2) V)
    (hC₂ : IsInv σ C₂) (hC₁ : IsInv σ C₁) : Submodule (ZMod 2) (C₂ →ₗ[ZMod 2] C₁) where
  carrier := {φ | ∀ y : C₂, φ (restrictInv σ C₂ hC₂ y) = restrictInv σ C₁ hC₁ (φ y)}
  zero_mem' := by intro y; simp
  add_mem' := by
    intro φ ψ hφ hψ y
    simp only [Set.mem_ofPred_eq, LinearMap.add_apply] at hφ hψ ⊢
    rw [hφ, hψ, map_add]
  smul_mem' := by
    intro c φ hφ y
    simp only [Set.mem_ofPred_eq, LinearMap.smul_apply] at hφ ⊢
    rw [hφ, map_smul]

/-- Invariance of the image of the kernel under `σ`. -/
private theorem isInv_map_ker {σ : V →ₗ[ZMod 2] V} {C D : Submodule (ZMod 2) V}
    (hC : IsInv σ C) (hD : IsInv σ D) {φ : C →ₗ[ZMod 2] D}
    (hφ : ∀ y : C, φ (restrictInv σ C hC y) = restrictInv σ D hD (φ y)) :
    IsInv σ ((LinearMap.ker φ).map C.subtype) := by
  intro x hx
  rw [Submodule.mem_map] at hx ⊢
  obtain ⟨s, hs, rfl⟩ := hx
  refine ⟨restrictInv σ C hC s, ?_, restrictInv_apply hC s⟩
  rw [LinearMap.mem_ker] at hs ⊢
  rw [hφ s, hs, map_zero]

/-- Invariance of the image of the range under `σ`. -/
private theorem isInv_map_range {σ : V →ₗ[ZMod 2] V} {C D : Submodule (ZMod 2) V}
    (hC : IsInv σ C) (hD : IsInv σ D) {φ : C →ₗ[ZMod 2] D}
    (hφ : ∀ y : C, φ (restrictInv σ C hC y) = restrictInv σ D hD (φ y)) :
    IsInv σ ((LinearMap.range φ).map D.subtype) := by
  intro x hx
  rw [Submodule.mem_map] at hx ⊢
  obtain ⟨s, hs, rfl⟩ := hx
  obtain ⟨y, hy⟩ := (LinearMap.mem_range.mp hs)
  refine ⟨restrictInv σ D hD s, ?_, restrictInv_apply hD s⟩
  rw [LinearMap.mem_range]
  exact ⟨restrictInv σ C hC y, by rw [hφ y, hy]⟩

/-! ## The dichotomy -/

theorem hom_card_eq_one_or_card {V : Type*} [AddCommGroup V] [Module (ZMod 2) V] [Finite V]
    {σ : V →ₗ[ZMod 2] V} {C₁ C₂ : Submodule (ZMod 2) V}
    (h1 : Work.Higman.Layers.IsSimpleMod σ C₁) (h2 : Work.Higman.Layers.IsSimpleMod σ C₂) :
    Nat.card (Work.Higman.Layers.HomInv σ C₂ C₁ h2.1 h1.1) = 1 ∨
      Nat.card (Work.Higman.Layers.HomInv σ C₂ C₁ h2.1 h1.1) = Nat.card C₂ := by
  classical
  have key : Nat.card (HomInvSub σ C₂ C₁ h2.1 h1.1) = 1 ∨
      Nat.card (HomInvSub σ C₂ C₁ h2.1 h1.1) = Nat.card C₂ := by
    by_cases htriv : ∀ φ : HomInvSub σ C₂ C₁ h2.1 h1.1, (φ : C₂ →ₗ[ZMod 2] C₁) = 0
    · left
      haveI : Subsingleton (HomInvSub σ C₂ C₁ h2.1 h1.1) :=
        ⟨fun a b => Subtype.ext (by rw [htriv a, htriv b])⟩
      haveI : Nonempty (HomInvSub σ C₂ C₁ h2.1 h1.1) := ⟨0⟩
      exact Nat.card_eq_one_iff_unique.mpr ⟨inferInstance, inferInstance⟩
    · right
      push_neg at htriv
      obtain ⟨φ₀, hφ₀⟩ := htriv
      obtain ⟨v, hv⟩ : ∃ v : C₂, φ₀.1 v ≠ 0 := by
        by_contra hcon
        push_neg at hcon
        exact hφ₀ (LinearMap.ext hcon)
      have hv0 : v ≠ 0 := fun h => hv (by rw [h, map_zero])
      have hgen : cycSpan σ (v : V) = C₂ := cycSpan_eq_of_simple h2 hv0
      -- `φ₀` is injective
      have hker_bot : LinearMap.ker φ₀.1 = ⊥ := by
        rcases h2.2.2 ((LinearMap.ker φ₀.1).map C₂.subtype)
            (Submodule.map_subtype_le C₂ _) (isInv_map_ker h2.1 h1.1 φ₀.2) with h | h
        · refine (Submodule.eq_bot_iff _).mpr fun x hx => Subtype.ext ?_
          have hmem : (x : V) ∈ (⊥ : Submodule (ZMod 2) V) :=
            h.le (Submodule.mem_map_of_mem hx)
          simpa using hmem
        · exfalso
          apply hφ₀
          refine LinearMap.ext fun x => ?_
          have hx : (x : V) ∈ (LinearMap.ker φ₀.1).map C₂.subtype := h.ge x.2
          rw [Submodule.mem_map] at hx
          obtain ⟨t, ht, htval⟩ := hx
          have htt : t = x := Subtype.ext htval
          rw [← htt]
          exact LinearMap.mem_ker.mp ht
      have hinj : Function.Injective φ₀.1 := LinearMap.ker_eq_bot.mp hker_bot
      -- `φ₀` is surjective
      have hrange_top : LinearMap.range φ₀.1 = ⊤ := by
        rcases h1.2.2 ((LinearMap.range φ₀.1).map C₁.subtype)
            (Submodule.map_subtype_le C₁ _) (isInv_map_range h2.1 h1.1 φ₀.2) with h | h
        · exfalso
          have hmem : ((φ₀.1 v : C₁) : V) ∈ (⊥ : Submodule (ZMod 2) V) :=
            h.le (Submodule.mem_map_of_mem (LinearMap.mem_range_self φ₀.1 v))
          exact hv (Subtype.ext (by simpa using hmem))
        · refine Submodule.eq_top_iff'.mpr fun x => ?_
          have hx : (x : V) ∈ (LinearMap.range φ₀.1).map C₁.subtype := h.ge x.2
          rw [Submodule.mem_map] at hx
          obtain ⟨t, ht, htval⟩ := hx
          have htt : t = x := Subtype.ext htval
          rw [← htt]; exact ht
      have hsurj : Function.Surjective φ₀.1 := LinearMap.range_eq_top.mp hrange_top
      have heq : Nat.card C₂ = Nat.card C₁ :=
        Nat.card_congr (LinearEquiv.ofBijective φ₀.1 ⟨hinj, hsurj⟩).toEquiv
      -- the evaluation map at the generator `v`
      let Θ : HomInvSub σ C₂ C₁ h2.1 h1.1 →ₗ[ZMod 2] C₁ :=
        { toFun := fun φ => φ.1 v
          map_add' := fun a b => LinearMap.add_apply a.1 b.1 v
          map_smul' := fun c a => LinearMap.smul_apply c a.1 v }
      have hΘinj : Function.Injective Θ := by
        intro a b hab
        have h0 : (a : C₂ →ₗ[ZMod 2] C₁) = (b : C₂ →ₗ[ZMod 2] C₁) :=
          eq_of_apply_eq_of_gen (φ := a.1) (ψ := b.1) h2.1 h1.1 hgen a.2 b.2 (by
            show a.1 v = b.1 v
            have h' := hab
            change a.1 v = b.1 v at h'
            exact h')
        exact Subtype.ext h0
      have hΘrange : LinearMap.range Θ = ⊤ := by
        have hle : (LinearMap.range Θ).map C₁.subtype ≤ C₁ := Submodule.map_subtype_le C₁ _
        have hinv : IsInv σ ((LinearMap.range Θ).map C₁.subtype) := by
          intro x hx
          rw [Submodule.mem_map] at hx ⊢
          obtain ⟨s, hs, rfl⟩ := hx
          obtain ⟨φ, hφ⟩ := (LinearMap.mem_range.mp hs)
          refine ⟨restrictInv σ C₁ h1.1 s, ?_, restrictInv_apply h1.1 s⟩
          rw [LinearMap.mem_range]
          refine ⟨⟨φ.1.comp (restrictInv σ C₂ h2.1), ?_⟩, ?_⟩
          · intro y
            rw [LinearMap.comp_apply, LinearMap.comp_apply]
            exact φ.2 (restrictInv σ C₂ h2.1 y)
          · show (φ.1.comp (restrictInv σ C₂ h2.1)) v = (restrictInv σ C₁ h1.1) s
            rw [LinearMap.comp_apply]
            have hval : φ.1 v = s := by
              have h' := hφ
              change φ.1 v = s at h'
              exact h'
            rw [φ.2 v, hval]
        rcases h1.2.2 ((LinearMap.range Θ).map C₁.subtype) hle hinv with h | h
        · exfalso
          have hmem : ((Θ φ₀ : C₁) : V) ∈ (⊥ : Submodule (ZMod 2) V) :=
            h.le (Submodule.mem_map_of_mem (LinearMap.mem_range_self Θ φ₀))
          apply hv
          show Θ φ₀ = 0
          exact Subtype.ext (by simpa using hmem)
        · refine Submodule.eq_top_iff'.mpr fun x => ?_
          have hx : (x : V) ∈ (LinearMap.range Θ).map C₁.subtype := h.ge x.2
          rw [Submodule.mem_map] at hx
          obtain ⟨t, ht, htval⟩ := hx
          have htt : t = x := Subtype.ext htval
          rw [← htt]; exact ht
      have hΘsurj : Function.Surjective Θ := LinearMap.range_eq_top.mp hΘrange
      have hcard : Nat.card (HomInvSub σ C₂ C₁ h2.1 h1.1) = Nat.card C₁ :=
        Nat.card_congr (Equiv.ofBijective Θ ⟨hΘinj, hΘsurj⟩)
      exact hcard.trans heq.symm
  exact key

end Work.Higman.Layers
