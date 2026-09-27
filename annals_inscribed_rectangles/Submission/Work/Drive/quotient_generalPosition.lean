import Mathlib

/-!
# General position of three projective planes: the quotient form

`MANIFOLD_PARITY_ENCODING.md` §4 replaces the bottoms of the radial sweeps by three **linear**
projective planes of one level, i.e. by three `3`-dimensional subspaces `U 0, U 1, U 2 ⊆ ℝ⁴` in general
position — in particular meeting in a line `L` (`Work.Drive.projective_planes_meet_oddly` is the
statement that such a triple meets in exactly one *point* of `ℝP³`).

The tangent plane of the projective plane `ℝP² = ℙ(U i)` at the common point `ℙ(L)` is the quotient
`U i / L` inside the `3`-dimensional space `ℝ⁴ / L`.  This file proves the elementary linear algebra
that makes the genericity hypothesis `hV` of the chain route automatic for that model:

> `U 0 / L ⊓ U 1 / L ⊓ U 2 / L = ⊥`  whenever `U 0 ⊓ U 1 ⊓ U 2 = L`.

(The content is that `Submodule.map (mkQ L)` preserves *binary* infima of submodules containing `L`;
the `3`-fold case is then immediate because `L / L = ⊥`.)
-/

namespace Work.Drive

set_option maxHeartbeats 2000000

variable {W : Type*} [AddCommGroup W] [Module ℝ W]

/-- **`Submodule.map (mkQ L)` preserves binary infima of submodules containing `L`.** -/
theorem map_mkQ_inf (L U V : Submodule ℝ W) (hLU : L ≤ U) (hLV : L ≤ V) :
    U.map (Submodule.mkQ L) ⊓ V.map (Submodule.mkQ L) = (U ⊓ V).map (Submodule.mkQ L) := by
  refine le_antisymm ?_ ?_
  · rintro z ⟨hzu, hzv⟩
    obtain ⟨u, huU, huz⟩ := (Submodule.mem_map (f := Submodule.mkQ L) (p := U)).mp hzu
    obtain ⟨v, hvV, hvz⟩ := (Submodule.mem_map (f := Submodule.mkQ L) (p := V)).mp hzv
    have hker : u - v ∈ L := by
      have h1 : L.mkQ (u - v) = 0 := by rw [map_sub, huz, hvz, sub_self]
      rw [Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero] at h1
      exact h1
    have huV : u ∈ V := by
      have hvu : v + (u - v) = u := by abel
      rw [← hvu]
      exact V.add_mem hvV (hLV hker)
    exact ⟨u, ⟨huU, huV⟩, huz⟩
  · exact le_inf (Submodule.map_mono (f := Submodule.mkQ L) inf_le_left)
      (Submodule.map_mono (f := Submodule.mkQ L) inf_le_right)

/-- **The three tangent planes of three projective planes in general position meet in `⊥`.** -/
theorem quotient_generalPosition (L U₀ U₁ U₂ : Submodule ℝ W)
    (h₀ : L ≤ U₀) (h₁ : L ≤ U₁) (h₂ : L ≤ U₂) (htriple : U₀ ⊓ U₁ ⊓ U₂ = L) :
    U₀.map (Submodule.mkQ L) ⊓ U₁.map (Submodule.mkQ L) ⊓ U₂.map (Submodule.mkQ L) = ⊥ := by
  have hbot : Submodule.map (Submodule.mkQ L) L = ⊥ := by
    rw [Submodule.eq_bot_iff]
    rintro z hz
    obtain ⟨w, hw, hwz⟩ := (Submodule.mem_map (f := Submodule.mkQ L) (p := L)).mp hz
    rw [← hwz, Submodule.mkQ_apply]
    exact (Submodule.Quotient.mk_eq_zero L).mpr hw
  rw [map_mkQ_inf L U₀ U₁ h₀ h₁, map_mkQ_inf L (U₀ ⊓ U₁) U₂ (le_inf h₀ h₁) h₂,
    htriple, hbot]

end Work.Drive
