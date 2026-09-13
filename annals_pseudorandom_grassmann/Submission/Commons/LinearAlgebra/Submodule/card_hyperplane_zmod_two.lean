import Mathlib.Algebra.Order.Ring.Star
import Mathlib.FieldTheory.Finiteness
import Submission.Commons.LinearAlgebra.Submodule.card_submodule_finrank_dual_zmod_two_of_le

namespace Commons.LinearAlgebra.Submodule

set_option linter.style.haveILetI false

open Module

/-- In `𝔽₂`, the only nonzero element is `1`. -/
lemma zmod_two_eq_one {a : ZMod 2} (h : a ≠ 0) : a = 1 := by
  have hv : a.val < 2 := ZMod.val_lt a
  have h0 : a.val ≠ 0 := fun h' => h ((ZMod.val_eq_zero a).mp h')
  exact (ZMod.val_eq_one (n := 2) (by norm_num) a).mp (by omega)

/-- The number of `1`-dimensional subspaces of a finite `𝔽₂`-vector space `V` equals the
number of nonzero vectors, `2 ^ finrank V - 1`: a nonzero vector `x` spans the line
`{0, x}`, and over `𝔽₂` distinct nonzero vectors span distinct lines. -/
theorem card_oneDim_zmod_two {V : Type*} [AddCommGroup V] [Module (ZMod 2) V] [Finite V] :
    Nat.card {W : Submodule (ZMod 2) V // Module.finrank (ZMod 2) W = 1} =
      2 ^ Module.finrank (ZMod 2) V - 1 := by
  classical
  haveI : Fintype V := Fintype.ofFinite V
  haveI : Module.Finite (ZMod 2) V := Module.Finite.of_finite
  -- Bijection between nonzero vectors and `1`-dimensional subspaces.
  have hbij : Function.Bijective
      (fun x : {x : V // x ≠ 0} =>
        (⟨ZMod 2 ∙ x.1, finrank_span_singleton x.2⟩ :
          {W : Submodule (ZMod 2) V // Module.finrank (ZMod 2) W = 1})) := by
    refine ⟨?_, ?_⟩
    · intro x y hxy
      have hspan : ZMod 2 ∙ x.1 = ZMod 2 ∙ y.1 := congrArg Subtype.val hxy
      have hxmem : x.1 ∈ ZMod 2 ∙ y.1 := by
        rw [← hspan]; exact Submodule.mem_span_singleton_self x.1
      obtain ⟨a, ha⟩ := Submodule.mem_span_singleton.mp hxmem
      have hane : a ≠ 0 := by
        intro h; rw [h, zero_smul] at ha; exact x.2 ha.symm
      apply Subtype.ext
      rw [← ha, zmod_two_eq_one hane, one_smul]
    · intro W
      have hWne : W.1 ≠ ⊥ := by
        intro hb
        have h0 : Module.finrank (ZMod 2) W.1 = 0 := by rw [hb]; exact finrank_bot (ZMod 2) V
        omega
      obtain ⟨x, hxW, hx0⟩ := (Submodule.ne_bot_iff W.1).mp hWne
      refine ⟨⟨x, hx0⟩, ?_⟩
      apply Subtype.ext
      exact Submodule.eq_of_le_of_finrank_eq
        (Submodule.span_singleton_le_iff_mem x W.1 |>.mpr hxW)
        (by rw [finrank_span_singleton hx0, W.2])
  have hVcard : Nat.card V = 2 ^ Module.finrank (ZMod 2) V := by
    rw [Module.natCard_eq_pow_finrank (K := ZMod 2) (V := V), Nat.card_zmod]
  have hne : Nat.card {x : V // x ≠ 0} = Nat.card V - 1 := by
    rw [Nat.card_eq_fintype_card (α := {x : V // x ≠ 0}),
        Nat.card_eq_fintype_card (α := V)]
    exact Set.card_ne_eq (0 : V)
  rw [← Nat.card_eq_of_bijective _ hbij, hne, hVcard]

/-- **The number of hyperplanes in a finite `𝔽₂`-vector space.**  A finite-dimensional
vector space `V` over `𝔽₂` with `finrank V = n` has exactly `2 ^ n - 1` codimension-one
subspaces.

Proof: by Grassmann duality over `𝔽₂` the codimension-one subspaces of `V` are in bijection
with the one-dimensional subspaces, and those are in bijection with the nonzero vectors of
`V` (a nonzero vector spans the line `{0, x}`, and over `𝔽₂` a line has a single nonzero
element).  There are `2 ^ n - 1` nonzero vectors. -/
theorem card_hyperplane_zmod_two {V : Type*} [AddCommGroup V] [Module (ZMod 2) V] [Finite V]
    (hV : 1 ≤ Module.finrank (ZMod 2) V) :
    Nat.card {H : Submodule (ZMod 2) V // Module.finrank (ZMod 2) H =
      Module.finrank (ZMod 2) V - 1} = 2 ^ Module.finrank (ZMod 2) V - 1 := by
  rw [← card_submodule_finrank_dual_zmod_two_of_le (V := V) 1 hV]
  exact card_oneDim_zmod_two

end Commons.LinearAlgebra.Submodule