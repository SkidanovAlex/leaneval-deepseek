import Mathlib
import Submission.Work.Higman.Layers.Defs
import Submission.Work.Higman.Layers.count_eq_one_add_hom_aux

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.style.haveILetI false
set_option maxHeartbeats 1000000

noncomputable section

namespace Work.Higman.Layers

variable {V : Type*} [AddCommGroup V] [Module (ZMod 2) V]

/-- A projection onto a `σ`-invariant summand along a complementary `σ`-invariant summand is
`σ`-equivariant. -/
theorem projectionOnto_sigma_eq_aux {σ : V →ₗ[ZMod 2] V} {P Q : Submodule (ZMod 2) V}
    (hc : IsCompl P Q) (hP : IsInv σ P) (hQ : IsInv σ Q) (v : V) :
    ((P.projectionOnto Q hc) (σ v) : V) = σ ((P.projectionOnto Q hc) v : V) := by
  rw [Submodule.coe_projectionOnto_apply, Submodule.coe_projectionOnto_apply]
  have hv : v = P.projection Q hc v + Q.projection P hc.symm v :=
    (Submodule.projection_add_projection_eq_self hc v).symm
  conv_lhs => rw [hv]
  simp only [map_add]
  rw [Submodule.projection_apply_of_mem_left hc (hP _ (Submodule.projection_apply_mem hc v)),
    Submodule.projection_apply_of_mem_right hc (hQ _ (Submodule.projection_apply_mem hc.symm v)),
    add_zero]

section Graph

/-- The graph of an equivariant map is invariant. -/
theorem graphOf_isInv {σ : V →ₗ[ZMod 2] V} {C₁ C₂ : Submodule (ZMod 2) V}
    (h1 : IsInv σ C₁) (h2 : IsInv σ C₂) (φ : HomInv σ C₂ C₁ h2 h1) :
    IsInv σ (graphOf h1 h2 φ) := by
  intro x hx
  rw [mem_graphOf] at hx ⊢
  obtain ⟨y, rfl⟩ := hx
  refine ⟨restrictInv σ C₂ h2 y, ?_⟩
  have h1v : ((φ.1 (restrictInv σ C₂ h2 y) : C₁) : V) = σ ((φ.1 y : C₁) : V) := by
    rw [show φ.1 (restrictInv σ C₂ h2 y) = restrictInv σ C₁ h1 (φ.1 y) from φ.2 y]
    rfl
  have h2v : ((restrictInv σ C₂ h2 y : C₂) : V) = σ (y : V) := rfl
  rw [h1v, h2v, map_add]

/-- The graph of an equivariant map is isomorphic to its domain, hence has the same dimension. -/
theorem graphOf_finrank {σ : V →ₗ[ZMod 2] V} {C₁ C₂ : Submodule (ZMod 2) V}
    (h1 : IsInv σ C₁) (h2 : IsInv σ C₂) (hdisj : C₁ ⊓ C₂ = ⊥) (φ : HomInv σ C₂ C₁ h2 h1) :
    Module.finrank (ZMod 2) (graphOf h1 h2 φ) = Module.finrank (ZMod 2) C₂ := by
  classical
  let g : C₂ →ₗ[ZMod 2] V := (C₁.subtype.comp φ.1) + C₂.subtype
  have hg : g.range = graphOf h1 h2 φ := rfl
  have hinj : Function.Injective g := by
    intro y z hyz
    have h : (φ.1 y : V) + (y : V) = (φ.1 z : V) + (z : V) := hyz
    have hkey : (y : V) - (z : V) = (φ.1 z : V) - (φ.1 y : V) := by
      rw [sub_eq_sub_iff_add_eq_add, add_comm (y : V) (φ.1 y : V)]
      exact h
    have hmem1 : (y : V) - (z : V) ∈ C₂ := Submodule.sub_mem _ y.2 z.2
    have hmem2 : (y : V) - (z : V) ∈ C₁ := by
      rw [hkey]
      exact Submodule.sub_mem _ (φ.1 z).2 (φ.1 y).2
    have hmem : (y : V) - (z : V) ∈ C₁ ⊓ C₂ := ⟨hmem2, hmem1⟩
    rw [hdisj, Submodule.mem_bot] at hmem
    exact Subtype.ext (sub_eq_zero.mp hmem)
  rw [← hg]
  exact ((LinearEquiv.ofInjective g hinj).finrank_eq).symm

/-- Distinct equivariant maps have distinct graphs. -/
theorem graphOf_injective {σ : V →ₗ[ZMod 2] V} {C₁ C₂ : Submodule (ZMod 2) V}
    (h1 : IsInv σ C₁) (h2 : IsInv σ C₂) (hc : IsCompl C₁ C₂) :
    Function.Injective (graphOf (σ := σ) (C₁ := C₁) (C₂ := C₂) h1 h2) := by
  intro φ ψ hφψ
  refine Subtype.ext (LinearMap.ext fun y => Subtype.ext ?_)
  have hmem : (φ.1 y : V) + (y : V) ∈ graphOf h1 h2 ψ := by
    rw [← hφψ]
    exact (mem_graphOf h1 h2 φ _).mpr ⟨y, rfl⟩
  obtain ⟨z, hz⟩ := (mem_graphOf h1 h2 ψ _).mp hmem
  have hsub : (z : V) - (y : V) = (φ.1 y : V) - (ψ.1 z : V) := by
    rw [sub_eq_sub_iff_add_eq_add, add_comm (z : V) ((ψ.1 z : C₁) : V)]
    exact hz
  have hdisj : C₁ ⊓ C₂ = ⊥ := disjoint_iff.mp hc.1
  have hmem1 : (z : V) - (y : V) ∈ C₂ := Submodule.sub_mem _ z.2 y.2
  have hmem2 : (z : V) - (y : V) ∈ C₁ := by
    rw [hsub]
    exact Submodule.sub_mem _ (φ.1 y).2 (ψ.1 z).2
  have hmem3 : (z : V) - (y : V) ∈ C₁ ⊓ C₂ := ⟨hmem2, hmem1⟩
  rw [hdisj, Submodule.mem_bot] at hmem3
  have hyz : z = y := Subtype.ext (sub_eq_zero.mp hmem3)
  rw [hyz] at hz
  exact (add_right_cancel hz).symm

/-- A graph is never equal to `C₁` (when `C₂ ≠ ⊥` and the summands are disjoint). -/
theorem graphOf_ne_C1 {σ : V →ₗ[ZMod 2] V} {C₁ C₂ : Submodule (ZMod 2) V}
    (h1 : IsInv σ C₁) (h2 : IsInv σ C₂) (hdisj : C₁ ⊓ C₂ = ⊥) (h2ne : C₂ ≠ ⊥)
    (φ : HomInv σ C₂ C₁ h2 h1) : graphOf h1 h2 φ ≠ C₁ := by
  intro hcontra
  obtain ⟨y, hy, hyne⟩ := (Submodule.ne_bot_iff C₂).mp h2ne
  have hmem : (φ.1 ⟨y, hy⟩ : V) + (y : V) ∈ graphOf h1 h2 φ :=
    (mem_graphOf h1 h2 φ _).mpr ⟨⟨y, hy⟩, rfl⟩
  rw [hcontra] at hmem
  have hyC1 : y ∈ C₁ := by
    have h := Submodule.sub_mem C₁ hmem (φ.1 ⟨y, hy⟩).2
    simpa using h
  have h1' : y ∈ C₁ ⊓ C₂ := ⟨hyC1, hy⟩
  rw [hdisj, Submodule.mem_bot] at h1'
  exact hyne h1'

end Graph

section Extract

/-- Any `σ`-invariant subspace of dimension `n`, other than `C₁`, is the graph of a
`σ`-equivariant map `C₂ → C₁`. -/
theorem exists_graphOf_of_ne [Finite V] {σ : V →ₗ[ZMod 2] V} {n : ℕ}
    {C₁ C₂ : Submodule (ZMod 2) V} (h1 : IsSimpleMod σ C₁) (h2 : IsSimpleMod σ C₂)
    (hdisj : C₁ ⊓ C₂ = ⊥) (hsup : C₁ ⊔ C₂ = ⊤)
    (hfr1 : Module.finrank (ZMod 2) C₁ = n) (hfr2 : Module.finrank (ZMod 2) C₂ = n)
    (U : Submodule (ZMod 2) V) (hUinv : IsInv σ U) (hUfr : Module.finrank (ZMod 2) U = n)
    (hU : U ≠ C₁) :
    ∃ φ : HomInv σ C₂ C₁ h2.1 h1.1, graphOf h1.1 h2.1 φ = U := by
  classical
  obtain ⟨hC₁, hC₁ne, hC₁simple⟩ := h1
  obtain ⟨hC₂, hC₂ne, hC₂simple⟩ := h2
  have hc : IsCompl C₁ C₂ := ⟨disjoint_iff.mpr hdisj, codisjoint_iff.mpr hsup⟩
  have hUbot : U ⊓ C₁ = ⊥ := by
    rcases hC₁simple (U ⊓ C₁) inf_le_right (fun x hx => ⟨hUinv x hx.1, hC₁ x hx.2⟩) with h | h
    · exact h
    · exfalso
      exact hU (Submodule.eq_of_le_of_finrank_eq (S₁ := C₁) (S₂ := U)
        ((le_of_eq h.symm).trans inf_le_left) (by rw [hfr1, hUfr])).symm
  let π₂ : V →ₗ[ZMod 2] C₂ := C₂.projectionOnto C₁ hc.symm
  let π₁ : V →ₗ[ZMod 2] C₁ := C₁.projectionOnto C₂ hc
  have hsum : ∀ v : V, (π₁ v : V) + (π₂ v : V) = v := fun v => by
    have h := LinearMap.congr_fun (Submodule.subtype_comp_projectionOnto_add_eq_id hc) v
    simpa [π₁, π₂] using h
  let q : U →ₗ[ZMod 2] C₂ := π₂.comp U.subtype
  have hq_inj : Function.Injective q := by
    rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
    intro u hu
    have hmem : (u : V) ∈ C₁ :=
      (Submodule.projectionOnto_apply_eq_zero_iff hc.symm).mp (by simpa [q, π₂] using hu)
    have h2' : (u : V) ∈ U ⊓ C₁ := ⟨u.2, hmem⟩
    rw [hUbot, Submodule.mem_bot] at h2'
    exact Subtype.ext h2'
  have hfr_eq : Module.finrank (ZMod 2) U = Module.finrank (ZMod 2) C₂ := by rw [hUfr, hfr2]
  have hq_surj : Function.Surjective q :=
    (LinearMap.injective_iff_surjective_of_finrank_eq_finrank hfr_eq).mp hq_inj
  let e : U ≃ₗ[ZMod 2] C₂ := LinearEquiv.ofBijective q ⟨hq_inj, hq_surj⟩
  have he_apply : ∀ u : U, e u = q u := fun u => rfl
  have hq_equi : ∀ u : U, q (restrictInv σ U hUinv u) = restrictInv σ C₂ hC₂ (q u) := by
    intro u
    refine Subtype.ext ?_
    show ((C₂.projectionOnto C₁ hc.symm) (σ (u : V)) : V) =
      σ ((C₂.projectionOnto C₁ hc.symm) (u : V) : V)
    exact projectionOnto_sigma_eq_aux hc.symm hC₂ hC₁ (u : V)
  have he_equiv : ∀ u : U, e (restrictInv σ U hUinv u) = restrictInv σ C₂ hC₂ (e u) := by
    intro u
    rw [he_apply, he_apply]
    exact hq_equi u
  have he_symm_equiv : ∀ y : C₂, e.symm (restrictInv σ C₂ hC₂ y)
      = restrictInv σ U hUinv (e.symm y) := by
    intro y
    apply e.injective
    conv_lhs => rw [LinearEquiv.apply_symm_apply]
    rw [he_equiv, LinearEquiv.apply_symm_apply]
  have he_spec : ∀ y : C₂, q (e.symm y) = y := by
    intro y
    have h := he_apply (e.symm y)
    rw [LinearEquiv.apply_symm_apply] at h
    exact h.symm
  let φ₀ : C₂ →ₗ[ZMod 2] C₁ := π₁.comp (U.subtype.comp (e.symm : C₂ →ₗ[ZMod 2] U))
  have hφ₀_val : ∀ y : C₂, (φ₀ y : V) = (π₁ ((e.symm y : U) : V) : V) := fun _ => rfl
  have hφ₀_equi : ∀ y : C₂, φ₀ (restrictInv σ C₂ hC₂ y) = restrictInv σ C₁ hC₁ (φ₀ y) := by
    intro y
    refine Subtype.ext ?_
    rw [hφ₀_val (restrictInv σ C₂ hC₂ y), he_symm_equiv]
    show (π₁ (σ ((e.symm y : U) : V)) : V) = σ (π₁ ((e.symm y : U) : V) : V)
    exact projectionOnto_sigma_eq_aux hc hC₁ hC₂ ((e.symm y : U) : V)
  have hgraph : ((C₁.subtype.comp φ₀) + C₂.subtype).range = U := by
    apply le_antisymm
    · intro x hx
      rw [LinearMap.mem_range] at hx
      obtain ⟨y, hy⟩ := hx
      rw [← hy]
      show (φ₀ y : V) + (y : V) ∈ U
      have hyv : (y : V) = ((π₂ ((e.symm y : U) : V) : C₂) : V) :=
        (congrArg Subtype.val (he_spec y)).symm
      have hx₁ : (φ₀ y : V) = (π₁ ((e.symm y : U) : V) : V) := hφ₀_val y
      rw [hx₁, hyv, hsum ((e.symm y : U) : V)]
      exact (e.symm y).2
    · intro x hx
      rw [LinearMap.mem_range]
      refine ⟨q ⟨x, hx⟩, ?_⟩
      show (φ₀ (q ⟨x, hx⟩) : V) + ((q ⟨x, hx⟩ : C₂) : V) = x
      have hqval : ((q ⟨x, hx⟩ : C₂) : V) = (π₂ (x : V) : V) := rfl
      have hesymm : e.symm (q ⟨x, hx⟩) = ⟨x, hx⟩ := by
        apply e.injective
        rw [LinearEquiv.apply_symm_apply, ← he_apply ⟨x, hx⟩]
      have hx₂ : (φ₀ (q ⟨x, hx⟩) : V) = (π₁ (x : V) : V) := by
        rw [hφ₀_val, hesymm]
      rw [hx₂, hqval, hsum (x : V)]
  exact ⟨⟨φ₀, hφ₀_equi⟩, hgraph⟩

end Extract

/-- **Counting the `σ`-invariant subspaces of dimension `n`.**  If `V = C₁ ⊕ C₂` is a direct sum of
two `σ`-simple subspaces of dimension `n`, the invariant `n`-dimensional subspaces are `C₁` and the
graphs of the equivariant maps `C₂ → C₁`. -/
theorem count_eq_one_add_hom {V : Type*} [AddCommGroup V] [Module (ZMod 2) V] [Finite V]
    {σ : V →ₗ[ZMod 2] V} {n : ℕ} {C₁ C₂ : Submodule (ZMod 2) V}
    (h1 : Work.Higman.Layers.IsSimpleMod σ C₁) (h2 : Work.Higman.Layers.IsSimpleMod σ C₂)
    (hdisj : C₁ ⊓ C₂ = ⊥) (hsup : C₁ ⊔ C₂ = ⊤)
    (hfr1 : Module.finrank (ZMod 2) C₁ = n) (hfr2 : Module.finrank (ZMod 2) C₂ = n) :
    Nat.card (Work.Higman.Layers.InvSubspaces σ n)
      = 1 + Nat.card (Work.Higman.Layers.HomInv σ C₂ C₁ h2.1 h1.1) := by
  classical
  have hC₁ : IsInv σ C₁ := h1.1
  have hC₂ : IsInv σ C₂ := h2.1
  have hC₂ne : C₂ ≠ ⊥ := h2.2.1
  have hc : IsCompl C₁ C₂ := ⟨disjoint_iff.mpr hdisj, codisjoint_iff.mpr hsup⟩
  haveI : Finite (C₂ →ₗ[ZMod 2] C₁) := Finite.of_injective (fun f : C₂ →ₗ[ZMod 2] C₁ => (f : C₂ → C₁))
    (fun _ _ hab => LinearMap.ext (congrFun hab))
  haveI : Finite (HomInv σ C₂ C₁ hC₂ hC₁) := Finite.of_injective _ Subtype.coe_injective
  have key : ∀ U : InvSubspaces σ n,
      U.1 = C₁ ∨ ∃ φ : HomInv σ C₂ C₁ hC₂ hC₁, graphOf hC₁ hC₂ φ = U.1 := by
    intro U
    by_cases hUC : U.1 = C₁
    · exact Or.inl hUC
    · exact Or.inr (exists_graphOf_of_ne h1 h2 hdisj hsup hfr1 hfr2 U.1 U.2.1 U.2.2 hUC)
  let Φ : Unit ⊕ HomInv σ C₂ C₁ hC₂ hC₁ → InvSubspaces σ n := fun x =>
    match x with
    | Sum.inl _ => ⟨C₁, hC₁, hfr1⟩
    | Sum.inr φ => ⟨graphOf hC₁ hC₂ φ, graphOf_isInv hC₁ hC₂ φ,
        by rw [graphOf_finrank hC₁ hC₂ hdisj φ, hfr2]⟩
  have hΦ : Function.Bijective Φ := by
    constructor
    · intro x y hxy
      rcases x with _ | φ <;> rcases y with _ | ψ
      · rfl
      · exact absurd (congrArg Subtype.val hxy).symm (graphOf_ne_C1 hC₁ hC₂ hdisj hC₂ne ψ)
      · exact absurd (congrArg Subtype.val hxy) (graphOf_ne_C1 hC₁ hC₂ hdisj hC₂ne φ)
      · exact congrArg Sum.inr (graphOf_injective hC₁ hC₂ hc (Subtype.ext_iff.mp hxy))
    · rintro ⟨U, hUinv, hUfr⟩
      rcases key ⟨U, hUinv, hUfr⟩ with h | ⟨φ, hφ⟩
      · exact ⟨Sum.inl (), Subtype.ext h.symm⟩
      · exact ⟨Sum.inr φ, Subtype.ext hφ⟩
  have hcard : Nat.card (Unit ⊕ HomInv σ C₂ C₁ hC₂ hC₁) = Nat.card (InvSubspaces σ n) :=
    Nat.card_congr (Equiv.ofBijective Φ hΦ)
  have hunit : Nat.card Unit = 1 := by simp
  rw [← hcard, Nat.card_sum, hunit]

end Work.Higman.Layers
