/-
Copyright (c) 2024. All rights reserved.

# Counting the invariant `n`-subspaces: the graph bijection

If `V = C₁ ⊕ C₂` with both summands `σ`-invariant `σ`-simple of the same dimension `n`, then the
`σ`-invariant `n`-dimensional subspaces of `V` are the subspace `C₁` itself together with the
graphs of the `σ`-equivariant maps `C₂ → C₁`.  Hence

  `Nat.card (InvSubspaces σ n) = 1 + Nat.card (HomInv σ C₂ C₁)`.

Together with `Work.Higman.Layers.hom_card_eq_one_or_card` this gives the dichotomy
`2` or `2 ^ n + 1`.
-/

import Mathlib
import Submission.Work.Higman.Layers.count_eq_one_add_hom_aux

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option maxHeartbeats 800000

noncomputable section

namespace Work.Higman.LayersAlt

open Work.Higman.Layers

variable {V : Type*} [AddCommGroup V] [Module (ZMod 2) V] [Finite V]

/-! ## Coordinates in a complementary decomposition -/

section Coordinates

variable {C₁ C₂ : Submodule (ZMod 2) V} (hcompl : IsCompl C₁ C₂)

/-- The `C₂`-coordinate of `x` in the decomposition `V = C₁ ⊕ C₂`. -/
def sndProj : V →ₗ[ZMod 2] C₂ :=
  (LinearMap.snd (ZMod 2) C₁ C₂).comp
    ((Submodule.prodEquivOfIsCompl C₁ C₂ hcompl).symm : V →ₗ[ZMod 2] C₁ × C₂)

/-- The `C₁`-coordinate of `x` in the decomposition `V = C₁ ⊕ C₂`. -/
def fstProj : V →ₗ[ZMod 2] C₁ :=
  (LinearMap.fst (ZMod 2) C₁ C₂).comp
    ((Submodule.prodEquivOfIsCompl C₁ C₂ hcompl).symm : V →ₗ[ZMod 2] C₁ × C₂)

theorem sndProj_apply (x : V) :
    sndProj hcompl x =
      ((Submodule.prodEquivOfIsCompl C₁ C₂ hcompl).symm x).2 := rfl

theorem fstProj_apply (x : V) :
    fstProj hcompl x =
      ((Submodule.prodEquivOfIsCompl C₁ C₂ hcompl).symm x).1 := rfl

/-- The coordinates reconstruct the vector. -/
theorem fstProj_add_sndProj (x : V) :
    ((fstProj hcompl x : C₁) : V) + ((sndProj hcompl x : C₂) : V) = x := by
  have h := Submodule.coe_prodEquivOfIsCompl' C₁ C₂ hcompl
    ((Submodule.prodEquivOfIsCompl C₁ C₂ hcompl).symm x)
  rw [LinearEquiv.apply_symm_apply] at h
  rw [fstProj_apply, sndProj_apply]
  exact h.symm

/-- The coordinates of `a + b` are `a` and `b`. -/
theorem sndProj_add (a : C₁) (b : C₂) : sndProj hcompl ((a : V) + (b : V)) = b := by
  have h : (Submodule.prodEquivOfIsCompl C₁ C₂ hcompl).symm ((a : V) + (b : V)) = (a, b) := by
    rw [LinearEquiv.symm_apply_eq, Submodule.coe_prodEquivOfIsCompl' C₁ C₂ hcompl]
  rw [sndProj_apply, h]

theorem fstProj_add (a : C₁) (b : C₂) : fstProj hcompl ((a : V) + (b : V)) = a := by
  have h : (Submodule.prodEquivOfIsCompl C₁ C₂ hcompl).symm ((a : V) + (b : V)) = (a, b) := by
    rw [LinearEquiv.symm_apply_eq, Submodule.coe_prodEquivOfIsCompl' C₁ C₂ hcompl]
  rw [fstProj_apply, h]

theorem sndProj_eq_zero_of_mem {x : V} (hx : x ∈ C₁) : sndProj hcompl x = 0 := by
  have h := sndProj_add hcompl (⟨x, hx⟩ : C₁) 0
  simpa using h

theorem fstProj_eq_zero_of_mem {x : V} (hx : x ∈ C₂) : fstProj hcompl x = 0 := by
  have h := fstProj_add hcompl 0 (⟨x, hx⟩ : C₂)
  simpa using h

theorem sndProj_eq_self (y : C₂) : sndProj hcompl ((y : C₂) : V) = y := by
  have h := sndProj_add hcompl (0 : C₁) y
  simpa using h

/-- If the `C₂`-coordinate of `x` vanishes then `x ∈ C₁`. -/
theorem mem_C₁_of_sndProj_eq_zero {x : V} (hx : sndProj hcompl x = 0) : x ∈ C₁ := by
  have h2 : ((fstProj hcompl x : C₁) : V) = x := by
    have h := fstProj_add_sndProj hcompl x
    rw [hx] at h
    simpa using h
  rw [← h2]
  exact (fstProj hcompl x).2

/-- A normal form for elements of `V`. -/
theorem exists_decomp (hcompl : IsCompl C₁ C₂) (x : V) :
    ∃ (a : C₁) (b : C₂), x = (a : V) + (b : V) := by
  obtain ⟨a, ha, b, hb, hab⟩ := (Submodule.sup_eq_top_iff C₁ C₂).mp hcompl.sup_eq_top x
  exact ⟨⟨a, ha⟩, ⟨b, hb⟩, hab⟩

variable {σ : V →ₗ[ZMod 2] V} (hC₁ : IsInv σ C₁) (hC₂ : IsInv σ C₂)

/-- The `C₂`-coordinate is `σ`-equivariant. -/
theorem sndProj_restrict (hC₁ : IsInv σ C₁) (hC₂ : IsInv σ C₂) (x : V) :
    restrictInv σ C₂ hC₂ (sndProj hcompl x) = sndProj hcompl (σ x) := by
  obtain ⟨a, b, hx⟩ := exists_decomp hcompl x
  have h1 : sndProj hcompl x = b := by rw [hx]; exact sndProj_add hcompl a b
  have h2 : sndProj hcompl (σ x) = ⟨σ (b : V), hC₂ (b : V) b.2⟩ := by
    rw [hx, map_add]
    exact sndProj_add hcompl ⟨σ (a : V), hC₁ (a : V) a.2⟩ ⟨σ (b : V), hC₂ (b : V) b.2⟩
  rw [h1, h2]
  exact Subtype.ext rfl

/-- The `C₁`-coordinate is `σ`-equivariant. -/
theorem fstProj_restrict (hC₁ : IsInv σ C₁) (hC₂ : IsInv σ C₂) (x : V) :
    restrictInv σ C₁ hC₁ (fstProj hcompl x) = fstProj hcompl (σ x) := by
  obtain ⟨a, b, hx⟩ := exists_decomp hcompl x
  have h1 : fstProj hcompl x = a := by rw [hx]; exact fstProj_add hcompl a b
  have h2 : fstProj hcompl (σ x) = ⟨σ (a : V), hC₁ (a : V) a.2⟩ := by
    rw [hx, map_add]
    exact fstProj_add hcompl ⟨σ (a : V), hC₁ (a : V) a.2⟩ ⟨σ (b : V), hC₂ (b : V) b.2⟩
  rw [h1, h2]
  exact Subtype.ext rfl

end Coordinates

/-! ## Graphs of equivariant maps -/

section Graph

variable {σ : V →ₗ[ZMod 2] V} {C₁ C₂ : Submodule (ZMod 2) V}
variable (hC₁ : IsInv σ C₁) (hC₂ : IsInv σ C₂) (hdisj : C₁ ⊓ C₂ = ⊥)

/-- The graph of a linear map `C₂ → C₁` (no equivariance needed). -/
def rawGraph (hC₁ : IsInv σ C₁) (hC₂ : IsInv σ C₂) (φ : C₂ →ₗ[ZMod 2] C₁) :
    Submodule (ZMod 2) V :=
  ((C₁.subtype.comp φ) + C₂.subtype).range

theorem mem_rawGraph (φ : C₂ →ₗ[ZMod 2] C₁) (x : V) :
    x ∈ rawGraph hC₁ hC₂ φ ↔ ∃ y : C₂, (φ y : V) + (y : V) = x := by
  simp only [rawGraph, LinearMap.mem_range, LinearMap.add_apply, LinearMap.comp_apply,
    Submodule.subtype_apply]

theorem rawGraph_eq_graphOf (φ : C₂ →ₗ[ZMod 2] C₁)
    (hφ : ∀ y : C₂, φ (restrictInv σ C₂ hC₂ y) = restrictInv σ C₁ hC₁ (φ y)) :
    rawGraph hC₁ hC₂ φ = graphOf hC₁ hC₂ ⟨φ, hφ⟩ := rfl

/-- The graph of an equivariant map is invariant. -/
theorem isInv_graphOf (hdisj : C₁ ⊓ C₂ = ⊥) (φ : HomInv σ C₂ C₁ hC₂ hC₁) :
    IsInv σ (graphOf hC₁ hC₂ φ) := by
  intro x hx
  rw [mem_graphOf] at hx ⊢
  obtain ⟨y, rfl⟩ := hx
  refine ⟨restrictInv σ C₂ hC₂ y, ?_⟩
  rw [map_add]
  rw [show ((φ.1 (restrictInv σ C₂ hC₂ y) : C₁) : V) = σ ((φ.1 y : C₁) : V) from
    congrArg Subtype.val (φ.2 y)]
  rfl

/-- The graph of `φ` is isomorphic to `C₂`, hence has the same dimension. -/
theorem finrank_graphOf (hdisj : C₁ ⊓ C₂ = ⊥) (φ : HomInv σ C₂ C₁ hC₂ hC₁) :
    Module.finrank (ZMod 2) (graphOf hC₁ hC₂ φ) = Module.finrank (ZMod 2) C₂ := by
  classical
  have hG : ((C₁.subtype.comp φ.1) + C₂.subtype : C₂ →ₗ[ZMod 2] V).range = graphOf hC₁ hC₂ φ :=
    rfl
  let g : C₂ →ₗ[ZMod 2] graphOf hC₁ hC₂ φ :=
    ((C₁.subtype.comp φ.1) + C₂.subtype).codRestrict (graphOf hC₁ hC₂ φ)
      (fun y => by rw [← hG]; exact LinearMap.mem_range_self _ y)
  have hg_val : ∀ y : C₂, ((g y : graphOf hC₁ hC₂ φ) : V) = (φ.1 y : V) + (y : V) := fun _ => rfl
  have hinj : Function.Injective g := by
    intro y z hyz
    have h : (φ.1 y : V) + (y : V) = (φ.1 z : V) + (z : V) := by
      rw [← hg_val y, ← hg_val z, hyz]
    have h2 : (y : V) + (φ.1 y : V) = (z : V) + (φ.1 z : V) := by
      rw [add_comm (y : V), add_comm (z : V)]
      exact h
    have h3 : (y : V) - (z : V) = (φ.1 z : V) - (φ.1 y : V) := by
      rw [sub_eq_sub_iff_add_eq_add]
      rw [h2]
      abel
    have h4 : (y : V) - (z : V) ∈ C₂ := Submodule.sub_mem _ y.2 z.2
    have h5 : (y : V) - (z : V) ∈ C₁ := by
      rw [h3]
      exact Submodule.sub_mem _ (φ.1 z).2 (φ.1 y).2
    have h6 : (y : V) - (z : V) ∈ C₁ ⊓ C₂ := ⟨h5, h4⟩
    rw [hdisj, Submodule.mem_bot] at h6
    exact Subtype.ext (sub_eq_zero.mp h6)
  have hsurj : Function.Surjective g := by
    rintro ⟨x, hx⟩
    rw [mem_graphOf] at hx
    obtain ⟨y, hy⟩ := hx
    exact ⟨y, Subtype.ext (by rw [hg_val]; exact hy)⟩
  exact (LinearEquiv.ofBijective g ⟨hinj, hsurj⟩).finrank_eq.symm

/-- Distinct equivariant maps have distinct graphs. -/
theorem graphOf_injective (hdisj : C₁ ⊓ C₂ = ⊥) :
    Function.Injective fun φ : HomInv σ C₂ C₁ hC₂ hC₁ => graphOf hC₁ hC₂ φ := by
  intro φ ψ hφψ
  refine Subtype.ext (LinearMap.ext fun y => Subtype.ext ?_)
  have hφψ' : graphOf hC₁ hC₂ φ = graphOf hC₁ hC₂ ψ := hφψ
  have hmem : (φ.1 y : V) + (y : V) ∈ graphOf hC₁ hC₂ ψ := by
    rw [← hφψ']
    exact (mem_graphOf hC₁ hC₂ φ _).mpr ⟨y, rfl⟩
  obtain ⟨z, hz⟩ := (mem_graphOf hC₁ hC₂ ψ _).mp hmem
  have h2 : (y : V) + (φ.1 y : V) = (z : V) + (ψ.1 z : V) := by
    rw [add_comm (y : V), add_comm (z : V)]
    exact hz.symm
  have h3 : (y : V) - (z : V) = (ψ.1 z : V) - (φ.1 y : V) := by
    rw [sub_eq_sub_iff_add_eq_add]
    rw [h2]
    abel
  have h4 : (y : V) - (z : V) ∈ C₂ := Submodule.sub_mem _ y.2 z.2
  have h5 : (y : V) - (z : V) ∈ C₁ := by
    rw [h3]
    exact Submodule.sub_mem _ (ψ.1 z).2 (φ.1 y).2
  have h6 : (y : V) - (z : V) ∈ C₁ ⊓ C₂ := ⟨h5, h4⟩
  rw [hdisj, Submodule.mem_bot] at h6
  have hyz : z = y := Subtype.ext (sub_eq_zero.mp h6).symm
  rw [hyz] at hz
  exact (add_right_cancel hz).symm

end Graph

/-! ## The count -/

theorem count_eq_one_add_hom {σ : V →ₗ[ZMod 2] V} {n : ℕ} {C₁ C₂ : Submodule (ZMod 2) V}
    (h1 : IsSimpleMod σ C₁) (h2 : IsSimpleMod σ C₂)
    (hdisj : C₁ ⊓ C₂ = ⊥) (hsup : C₁ ⊔ C₂ = ⊤)
    (hfr1 : Module.finrank (ZMod 2) C₁ = n) (hfr2 : Module.finrank (ZMod 2) C₂ = n) :
    Nat.card (InvSubspaces σ n)
      = 1 + Nat.card (HomInv σ C₂ C₁ h2.1 h1.1) := by
  classical
  have hC₁ : IsInv σ C₁ := h1.1
  have hC₂ : IsInv σ C₂ := h2.1
  have hC₂ne : C₂ ≠ ⊥ := h2.2.1
  have hcompl : IsCompl C₁ C₂ := ⟨disjoint_iff.mpr hdisj, codisjoint_iff.mpr hsup⟩
  -- ## classification of the invariant `n`-subspaces
  have key : ∀ U : Submodule (ZMod 2) V, IsInv σ U → Module.finrank (ZMod 2) U = n →
      U = C₁ ∨ ∃ φ : HomInv σ C₂ C₁ hC₂ hC₁, U = graphOf hC₁ hC₂ φ := by
    intro U hU hfrU
    by_cases hUC₁ : U = C₁
    · exact Or.inl hUC₁
    · right
      have hUC₁bot : U ⊓ C₁ = ⊥ := by
        rcases h1.2.2 (U ⊓ C₁) inf_le_right (fun x hx => ⟨hU x hx.1, hC₁ x hx.2⟩) with h | h
        · exact h
        · refine absurd (Submodule.eq_of_le_of_finrank_eq
            ((le_of_eq h.symm).trans inf_le_left) ?_).symm hUC₁
          rw [hfr1, ← hfrU]
      set projV : V →ₗ[ZMod 2] V := C₂.subtype.comp (sndProj hcompl) with hprojV
      have hprojV_apply : ∀ x : V, projV x = ((sndProj hcompl x : C₂) : V) := fun _ => rfl
      have hWle : U.map projV ≤ C₂ := by
        intro x hx
        obtain ⟨y, -, rfl⟩ := Submodule.mem_map.mp hx
        exact (sndProj hcompl y).2
      have hWinv : IsInv σ (U.map projV) := by
        intro x hx
        obtain ⟨y, hy, rfl⟩ := Submodule.mem_map.mp hx
        refine Submodule.mem_map.mpr ⟨σ y, hU y hy, ?_⟩
        rw [hprojV_apply, hprojV_apply]
        exact congrArg Subtype.val (sndProj_restrict hcompl hC₁ hC₂ y).symm
      rcases h2.2.2 (U.map projV) hWle hWinv with hWbot | hWtop
      · -- `U ≤ C₁`, contradicting `U ≠ C₁`
        refine absurd ?_ hUC₁
        refine Submodule.eq_of_le_of_finrank_eq ?_ (by rw [hfrU, hfr1])
        intro x hx
        refine mem_C₁_of_sndProj_eq_zero hcompl ?_
        have hmem : projV x ∈ U.map projV := Submodule.mem_map.mpr ⟨x, hx, rfl⟩
        rw [hWbot, Submodule.mem_bot] at hmem
        rw [hprojV_apply] at hmem
        exact Subtype.ext hmem
      · -- the graph case
        set πU : U →ₗ[ZMod 2] C₂ := (sndProj hcompl).comp U.subtype with hπUdef
        have hπU_apply : ∀ u : U, πU u = sndProj hcompl (u : V) := fun _ => rfl
        have hsurj : Function.Surjective πU := by
          intro y
          have hy : ((y : C₂) : V) ∈ U.map projV := by
            rw [hWtop]
            exact y.2
          obtain ⟨x, hx, hxy⟩ := Submodule.mem_map.mp hy
          refine ⟨⟨x, hx⟩, ?_⟩
          show πU ⟨x, hx⟩ = y
          rw [hπU_apply]
          refine Subtype.ext ?_
          rw [← hprojV_apply x]
          exact hxy
        have hinj : Function.Injective πU := by
          intro u v huv
          have h1' : πU (u - v) = 0 := by rw [map_sub, huv, sub_self]
          have h2' : ((u - v : U) : V) ∈ C₁ := by
            refine mem_C₁_of_sndProj_eq_zero hcompl ?_
            rw [← hπU_apply (u - v)]
            exact h1'
          have h3' : ((u - v : U) : V) ∈ U ⊓ C₁ := ⟨(u - v).2, h2'⟩
          rw [hUC₁bot, Submodule.mem_bot] at h3'
          exact sub_eq_zero.mp (Subtype.ext h3')
        have hbij : Function.Bijective πU := ⟨hinj, hsurj⟩
        let e : C₂ ≃ₗ[ZMod 2] U := (LinearEquiv.ofBijective πU hbij).symm
        have he_spec : ∀ y : C₂, πU (e y) = y := fun y =>
          LinearEquiv.apply_symm_apply (LinearEquiv.ofBijective πU hbij) y
        let φ₀ : C₂ →ₗ[ZMod 2] C₁ := (fstProj hcompl).comp (U.subtype.comp (e : C₂ →ₗ[ZMod 2] U))
        have hφ₀_val : ∀ y : C₂, ((φ₀ y : C₁) : V) = fstProj hcompl ((e y : U) : V) := fun _ => rfl
        have he_val : ∀ y : C₂, ((e y : U) : V) = (φ₀ y : V) + (y : V) := by
          intro y
          have h := fstProj_add_sndProj hcompl ((e y : U) : V)
          rw [show sndProj hcompl ((e y : U) : V) = y from he_spec y] at h
          rw [← h, hφ₀_val y]
        have hgraph : rawGraph hC₁ hC₂ φ₀ = U := by
          refine le_antisymm ?_ ?_
          · intro x hx
            obtain ⟨y, rfl⟩ := (mem_rawGraph hC₁ hC₂ φ₀ _).mp hx
            rw [← he_val y]
            exact (e y).2
          · intro x hx
            have hy : (e (sndProj hcompl x) : U) = ⟨x, hx⟩ := by
              refine hinj ?_
              rw [he_spec, hπU_apply]
            have h3 : (φ₀ (sndProj hcompl x) : V) = ((fstProj hcompl x : C₁) : V) := by
              rw [hφ₀_val, hy]
            rw [← fstProj_add_sndProj hcompl x]
            rw [show ((fstProj hcompl x : C₁) : V) + ((sndProj hcompl x : C₂) : V)
                = (φ₀ (sndProj hcompl x) : V) + ((sndProj hcompl x : C₂) : V) from by rw [h3]]
            exact (mem_rawGraph hC₁ hC₂ φ₀ _).mpr ⟨sndProj hcompl x, rfl⟩
        -- equivariance of `φ₀` from the invariance of `U = rawGraph φ₀`
        have hL : ∀ y : C₂, sndProj hcompl (σ ((φ₀ y : V) + (y : V)))
            = restrictInv σ C₂ hC₂ y := by
          intro y
          rw [map_add, map_add, sndProj_eq_zero_of_mem hcompl (hC₁ (φ₀ y : V) (φ₀ y).2),
            zero_add, ← sndProj_restrict hcompl hC₁ hC₂ y, sndProj_eq_self hcompl y]
        have hφ₀_equi : ∀ y : C₂,
            φ₀ (restrictInv σ C₂ hC₂ y) = restrictInv σ C₁ hC₁ (φ₀ y) := by
          intro y
          obtain ⟨z, hz⟩ := (mem_rawGraph hC₁ hC₂ φ₀ _).mp (by
            rw [hgraph]
            exact hU _ (by
              rw [← hgraph]
              exact (mem_rawGraph hC₁ hC₂ φ₀ _).mpr ⟨y, rfl⟩))
          have hz1 : z = restrictInv σ C₂ hC₂ y := by
            have h2' : sndProj hcompl (σ ((φ₀ y : V) + (y : V)))
                = sndProj hcompl ((φ₀ z : V) + (z : V)) := by rw [← hz]
            rw [hL y] at h2'
            rw [sndProj_add hcompl (φ₀ z) z] at h2'
            exact h2'.symm
          have hz5 : ((φ₀ z : C₁) : V) = σ ((φ₀ y : C₁) : V) := by
            have h' : ((φ₀ z : C₁) : V) + ((z : C₂) : V)
                = σ ((φ₀ y : C₁) : V) + σ ((y : C₂) : V) := by
              have h := hz
              rw [map_add] at h
              exact h
            have hzval : ((z : C₂) : V) = σ ((y : C₂) : V) := by rw [hz1]; rfl
            rw [hzval] at h'
            exact add_right_cancel h'
          rw [hz1] at hz5
          exact Subtype.ext hz5
        exact ⟨⟨φ₀, hφ₀_equi⟩, by rw [← rawGraph_eq_graphOf hC₁ hC₂ φ₀ hφ₀_equi, hgraph]⟩
  -- ## the bijection with `PUnit ⊕ HomInv`
  let Φ : Unit ⊕ HomInv σ C₂ C₁ hC₂ hC₁ → InvSubspaces σ n := fun x =>
    match x with
    | Sum.inl _ => ⟨C₁, hC₁, hfr1⟩
    | Sum.inr φ => ⟨graphOf hC₁ hC₂ φ, isInv_graphOf hC₁ hC₂ hdisj φ,
        by rw [finrank_graphOf hC₁ hC₂ hdisj φ, hfr2]⟩
  have hC₂_nz : ∃ y : C₂, y ≠ 0 := by
    obtain ⟨x, hx, hxne⟩ := (Submodule.ne_bot_iff C₂).mp hC₂ne
    exact ⟨⟨x, hx⟩, fun h => hxne (by simpa using congrArg Subtype.val h)⟩
  have hgraph_ne : ∀ φ : HomInv σ C₂ C₁ hC₂ hC₁, graphOf hC₁ hC₂ φ ≠ C₁ := by
    intro φ hφ
    obtain ⟨y, hy⟩ := hC₂_nz
    have hmem1 : (φ.1 y : V) + (y : V) ∈ graphOf hC₁ hC₂ φ :=
      (mem_graphOf hC₁ hC₂ φ _).mpr ⟨y, rfl⟩
    have hmem : (φ.1 y : V) + (y : V) ∈ C₁ := by rw [hφ] at hmem1; exact hmem1
    have hyC₁ : ((y : C₂) : V) ∈ C₁ := by
      have h := sub_mem hmem (φ.1 y).2
      simpa using h
    have h1' : ((y : C₂) : V) ∈ C₁ ⊓ C₂ := ⟨hyC₁, y.2⟩
    rw [hdisj, Submodule.mem_bot] at h1'
    exact hy (Subtype.ext h1')
  have hΦ : Function.Bijective Φ := by
    constructor
    · intro x y hxy
      rcases x with ⟨⟩ | φ <;> rcases y with ⟨⟩ | ψ
      · rfl
      · exact absurd (congrArg Subtype.val hxy).symm (hgraph_ne ψ)
      · exact absurd (congrArg Subtype.val hxy) (hgraph_ne φ)
      · exact congrArg Sum.inr (graphOf_injective hC₁ hC₂ hdisj (Subtype.ext_iff.mp hxy))
    · rintro ⟨U, hU, hfrU⟩
      rcases key U hU hfrU with h | ⟨φ, hφ⟩
      · exact ⟨Sum.inl (), Subtype.ext h.symm⟩
      · exact ⟨Sum.inr φ, Subtype.ext hφ.symm⟩
  have hcard : Nat.card (InvSubspaces σ n)
      = Nat.card (Unit ⊕ HomInv σ C₂ C₁ hC₂ hC₁) :=
    (Nat.card_congr (Equiv.ofBijective Φ hΦ)).symm
  have hpunit : Nat.card Unit = 1 := Nat.card_eq_one_iff_unique.mpr ⟨inferInstance, inferInstance⟩
  haveI : Finite (C₂ →ₗ[ZMod 2] C₁) := Finite.of_injective _
    (fun f g h => LinearMap.ext (fun x => congrFun h x))
  haveI : Finite (HomInv σ C₂ C₁ hC₂ hC₁) := Finite.of_injective _ Subtype.coe_injective
  rw [hcard, Nat.card_sum, hpunit]

end Work.Higman.LayersAlt
