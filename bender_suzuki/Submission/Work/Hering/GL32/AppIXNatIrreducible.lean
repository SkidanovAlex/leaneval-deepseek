import Mathlib
import Submission.Work.Hering.GL32.AppIXDefs

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

/-!
# The natural `GL(3,2)`-module `F₂³` is irreducible

`GL(3,2)` acts transitively on the `7` nonzero vectors of `F₂³`.  We exhibit five explicit
involutions of `F₂³` (coordinate swaps and elementary shears) and, for each nonzero vector `w`,
a product `g` of those with `g w = e₀`.

Since a nonzero invariant subspace contains some `0 ≠ w`, hence the whole orbit of `w`, hence
`e₀, e₁, e₂`, this gives the irreducibility of the natural module (`nat_irreducible`).
-/

set_option autoImplicit false

namespace Work.Hering.GL32

/-- The natural `G`-module `F₂³`. -/
abbrev F2v : Type := Fin 3 → ZMod 2

/-- The standard basis vectors. -/
def e₀ : F2v := ![1, 0, 0]
def e₁ : F2v := ![0, 1, 0]
def e₂ : F2v := ![0, 0, 1]

/-- Swap the coordinates `0` and `1`. -/
noncomputable def sw01 : GL32 where
  toFun v := ![v 1, v 0, v 2]
  invFun v := ![v 1, v 0, v 2]
  left_inv := by intro v; funext i; fin_cases i <;> revert v <;> decide
  right_inv := by intro v; funext i; fin_cases i <;> revert v <;> decide
  map_add' := by intro v w; funext i; fin_cases i <;> simp [Pi.add_apply] <;> ring_nf
  map_smul' := by intro c v; funext i; fin_cases i <;> simp

/-- Swap the coordinates `0` and `2`. -/
noncomputable def sw02 : GL32 where
  toFun v := ![v 2, v 1, v 0]
  invFun v := ![v 2, v 1, v 0]
  left_inv := by intro v; funext i; fin_cases i <;> revert v <;> decide
  right_inv := by intro v; funext i; fin_cases i <;> revert v <;> decide
  map_add' := by intro v w; funext i; fin_cases i <;> simp [Pi.add_apply] <;> ring_nf
  map_smul' := by intro c v; funext i; fin_cases i <;> simp

/-- Add the coordinate `0` to the coordinate `1`: `v ↦ (v₀, v₀+v₁, v₂)`. -/
noncomputable def sh01 : GL32 where
  toFun v := ![v 0, v 0 + v 1, v 2]
  invFun v := ![v 0, v 0 + v 1, v 2]
  left_inv := by intro v; funext i; fin_cases i <;> revert v <;> decide
  right_inv := by intro v; funext i; fin_cases i <;> revert v <;> decide
  map_add' := by intro v w; funext i; fin_cases i <;> simp [Pi.add_apply] <;> ring_nf
  map_smul' := by intro c v; funext i; fin_cases i <;> simp [Pi.smul_apply] <;> ring

/-- Add the coordinate `0` to the coordinate `2`: `v ↦ (v₀, v₁, v₀+v₂)`. -/
noncomputable def sh02 : GL32 where
  toFun v := ![v 0, v 1, v 0 + v 2]
  invFun v := ![v 0, v 1, v 0 + v 2]
  left_inv := by intro v; funext i; fin_cases i <;> revert v <;> decide
  right_inv := by intro v; funext i; fin_cases i <;> revert v <;> decide
  map_add' := by intro v w; funext i; fin_cases i <;> simp [Pi.add_apply] <;> ring_nf
  map_smul' := by intro c v; funext i; fin_cases i <;> simp [Pi.smul_apply] <;> ring

/-- Add the coordinate `1` to the coordinate `2`: `v ↦ (v₀, v₁, v₁+v₂)`. -/
noncomputable def sh12 : GL32 where
  toFun v := ![v 0, v 1, v 1 + v 2]
  invFun v := ![v 0, v 1, v 1 + v 2]
  left_inv := by intro v; funext i; fin_cases i <;> revert v <;> decide
  right_inv := by intro v; funext i; fin_cases i <;> revert v <;> decide
  map_add' := by intro v w; funext i; fin_cases i <;> simp [Pi.add_apply] <;> ring_nf
  map_smul' := by intro c v; funext i; fin_cases i <;> simp [Pi.smul_apply] <;> ring

/-- **Transitivity.**  Every nonzero vector of `F₂³` can be sent to `e₀` by an element of
`GL(3,2)`, explicitly by one of the swaps/shears above. -/
theorem exists_maps_to_e₀ (w : F2v) (hw : w ≠ 0) : ∃ g : GL32, (g : F2v → F2v) w = e₀ := by
  have h0 : w 0 = 0 ∨ w 0 = 1 := by revert w; decide
  have h1 : w 1 = 0 ∨ w 1 = 1 := by revert w; decide
  have h2 : w 2 = 0 ∨ w 2 = 1 := by revert w; decide
  rcases h0 with h0 | h0
  · rcases h1 with h1 | h1
    · rcases h2 with h2 | h2
      · exact absurd (by funext i; fin_cases i <;> simp [h0, h1, h2]) hw
      · exact ⟨sw02, by funext i; fin_cases i <;> simp [sw02, e₀, h0, h1, h2] <;> decide⟩
    · rcases h2 with h2 | h2
      · exact ⟨sw01, by funext i; fin_cases i <;> simp [sw01, e₀, h0, h1, h2] <;> decide⟩
      · exact ⟨sw01 * sh12, by funext i; fin_cases i <;> simp [sw01, sh12, e₀, h0, h1, h2] <;> decide⟩
  · rcases h1 with h1 | h1
    · rcases h2 with h2 | h2
      · exact ⟨1, by funext i; fin_cases i <;> simp [e₀, h0, h1, h2] <;> decide⟩
      · exact ⟨sh02, by funext i; fin_cases i <;> simp [sh02, e₀, h0, h1, h2] <;> decide⟩
    · rcases h2 with h2 | h2
      · exact ⟨sh01, by funext i; fin_cases i <;> simp [sh01, e₀, h0, h1, h2] <;> decide⟩
      · exact ⟨sh01 * sh12, by funext i; fin_cases i <;> simp [sh01, sh12, e₀, h0, h1, h2] <;> decide⟩

/-- **Irreducibility of the natural `GL(3,2)`-module.** -/
theorem nat_irreducible (W : Submodule (ZMod 2) F2v)
    (hW : ∀ (g : GL32) (w : F2v), w ∈ W → g w ∈ W) : W = ⊥ ∨ W = ⊤ := by
  by_cases h : W = ⊥
  · exact Or.inl h
  right
  have hex : ∃ w ∈ W, w ≠ 0 := by
    by_contra hcon
    refine h (Submodule.eq_bot_iff W |>.mpr fun x hx => ?_)
    by_contra hx0
    exact hcon ⟨x, hx, hx0⟩
  obtain ⟨w, hwW, hw0⟩ := hex
  rw [eq_top_iff]
  intro v _
  rcases eq_or_ne v 0 with rfl | hv0
  · exact W.zero_mem
  · obtain ⟨g₁, hg₁⟩ := exists_maps_to_e₀ w hw0
    obtain ⟨g₂, hg₂⟩ := exists_maps_to_e₀ v hv0
    have hkey : (g₂⁻¹ * g₁ : GL32) w = v := by
      show (g₂⁻¹ : GL32) ((g₁ : GL32) w) = v
      rw [show (g₁ : GL32) w = e₀ from hg₁, ← hg₂]
      simp
    rw [← hkey]
    exact hW (g₂⁻¹ * g₁) w hwW

/-- Invariance of `W ≤ Dual F₂³` under the dual action, written as invariance under
`f ↦ f ∘ g` for all `g : GL32` (equivalent, since `g` ranges over the group). -/
def DualInvariant (W : Submodule (ZMod 2) (Module.Dual (ZMod 2) F2v)) : Prop :=
  ∀ (g : GL32) (f : Module.Dual (ZMod 2) F2v), f ∈ W → (g : GL32).dualMap f ∈ W

/-- **Irreducibility of the dual of the natural `GL(3,2)`-module**, by annihilator duality.

Recipe (API verified against this Mathlib revision):
* `A := W.dualCoannihilator` (`Submodule.dualCoannihilator`, `Submodule.mem_dualCoannihilator`)
  is `GL32`-invariant: for `v ∈ A`, `g` and `f ∈ W`, the functional `f ∘ g` equals
  `LinearMap.dualMap ((g⁻¹).symm) f ∈ W` (`LinearMap.dualMap_apply`), so `f (g v) = 0`.
* `nat_irreducible A` gives `A = ⊥` or `A = ⊤`.
* `A = ⊤` ⟹ `W = ⊥`: every `f ∈ W` vanishes on all of `F₂³`.
* `A = ⊥` ⟹ `W = ⊤`: use `Subspace.dualCoannihilator_dualAnnihilator_eq`
  (`W = dualCoannihilator W.dualAnnihilator`) and show `W.dualAnnihilator = ⊥` via reflexivity
  `Module.evalEquiv : F₂³ ≃ₗ Dual (Dual F₂³)` (needs `Module.IsReflexive`, available through
  `Module.instIsReflexiveOfFiniteOfProjective`); then `Submodule.dualCoannihilator_bot`.
-/
theorem dual_irreducible (W : Submodule (ZMod 2) (Module.Dual (ZMod 2) F2v))
    (hW : DualInvariant W) : W = ⊥ ∨ W = ⊤ := by
  -- The annihilator of `W` is `GL32`-invariant in `F₂³`.
  have hann : ∀ (g : GL32) (v : F2v),
      v ∈ W.dualCoannihilator → g v ∈ W.dualCoannihilator := by
    intro g v hv
    rw [Submodule.mem_dualCoannihilator] at hv ⊢
    intro f hf
    have h1 : (g : GL32).dualMap f ∈ W := hW g f hf
    have h2 : ((g : GL32).dualMap f) v = 0 := hv _ h1
    rwa [LinearEquiv.dualMap_apply] at h2
  rcases nat_irreducible W.dualCoannihilator hann with hA | hA
  · -- annihilator `⊥` ⟹ `W = ⊤`
    right
    have hannbot : W.dualAnnihilator = ⊥ := by
      rw [Submodule.eq_bot_iff]
      intro g hg
      rw [Submodule.mem_dualAnnihilator] at hg
      have hv : (Module.evalEquiv (ZMod 2) F2v).symm g ∈ W.dualCoannihilator := by
        rw [Submodule.mem_dualCoannihilator]
        intro f hf
        have h := hg f hf
        rw [Module.apply_evalEquiv_symm_apply]
        exact h
      rw [hA] at hv
      simp only [Submodule.mem_bot] at hv
      rw [← LinearEquiv.apply_symm_apply (Module.evalEquiv (ZMod 2) F2v) g, hv, map_zero]
    rw [← Subspace.dualAnnihilator_dualCoannihilator_eq (W := W), hannbot]
    exact Submodule.dualCoannihilator_bot
  · -- annihilator `⊤` ⟹ `W = ⊥`
    left
    rw [Submodule.eq_bot_iff]
    intro f hf
    apply LinearMap.ext
    intro v
    have hv : v ∈ W.dualCoannihilator := by rw [hA]; exact Submodule.mem_top
    rw [Submodule.mem_dualCoannihilator] at hv
    simpa using hv f hf

end Work.Hering.GL32
