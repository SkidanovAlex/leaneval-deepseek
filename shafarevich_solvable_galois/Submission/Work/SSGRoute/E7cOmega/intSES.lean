import Mathlib
import Submission.Work.SSGRoute.PTDefs
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# The trivial-coefficient short exact sequence `0 → ℤ --p--> ℤ --> ℤ/p → 0`

For a group `G` and a natural number `p ≠ 0`, the sequence of trivial `G`-modules
`0 → ℤ → ℤ → ℤ/p → 0` (with the first map multiplication by `p` and the second the reduction)
is short exact in `Rep Coeff G` (`Coeff = ULift ℤ`).

This is the coefficient sequence whose connecting map computes the Yoneda pairing
`Ext¹_G(ℤ/p, ℤ) × H¹(G, ℤ/p) → H²(G, ℤ)`: for the tautological class
`φ₀ = (intSES p).extClass ∈ Ext¹_G(ℤ/p, ℤ)`, the pairing with `h ∈ H¹(G, ℤ/p)` is
`h.comp φ₀`, which is the image of `h` under the connecting map `δ_h : H¹(G,ℤ/p) → H²(G,ℤ)` of
the covariant long exact sequence.
-/

open CategoryTheory SSGRoute.PTExt

attribute [local instance 10000] Rep.hV2 Rep.hV1 Submodule.module

namespace Work.SSGRoute.E7cOmega

variable {G : Type} [Group G]

/-- The reduction `Coeff = ULift ℤ → ZMod p`, as a `Coeff`-linear map. -/
noncomputable def redLin (p : ℕ) : Coeff →ₗ[Coeff] ZMod p where
  toFun c := ((ULift.down c : ℤ) : ZMod p)
  map_add' := by intro a b; simp
  map_smul' := by intro r a; simp

/-- Multiplication by `p` on `Coeff`, as a `Coeff`-linear map. -/
noncomputable def mulpLin (p : ℕ) : Coeff →ₗ[Coeff] Coeff where
  toFun c := p • c
  map_add' := by intro a b; simp [smul_add]
  map_smul' := by
    intro r a
    show (p • (r • a) : Coeff) = r • (p • a)
    show (ULift.up (p * (r * a).down) : Coeff) = ULift.up (r.down * (p * a.down))
    simp [mul_assoc, mul_comm]

/-- The reduction as a morphism of trivial `G`-representations. -/
noncomputable def redHom (p : ℕ) : unitRep G ⟶ Rep.trivial Coeff G (ZMod p) :=
  Rep.ofHom { toLinearMap := redLin p, isIntertwining' := fun _ => rfl }

/-- Multiplication by `p` as a morphism of trivial `G`-representations. -/
noncomputable def mulpHom (p : ℕ) : unitRep G ⟶ unitRep G :=
  Rep.ofHom { toLinearMap := mulpLin p, isIntertwining' := fun _ => rfl }

/-- **The trivial-coefficient short complex** `ℤ --p--> ℤ --> ℤ/p` in `Rep Coeff G`. -/
noncomputable def intSES (p : ℕ) : ShortComplex (Rep Coeff G) :=
  ShortComplex.mk (mulpHom (G := G) p) (redHom (G := G) p) (by
    apply Rep.hom_ext
    apply Representation.IntertwiningMap.ext
    apply LinearMap.ext
    intro c
    rw [Rep.hom_comp]
    show (redLin p) ((mulpLin p) c) = (0 : ZMod p)
    show (((p • c : Coeff)).down : ZMod p) = 0
    rw [show (p • c : Coeff) = ULift.up (p * c.down) from rfl]
    simp)

/-- **The trivial-coefficient sequence is short exact** (for `p ≠ 0`). -/
theorem intSES_shortExact (p : ℕ) (hp : p ≠ 0) :
    (intSES (G := G) p).ShortExact where
  exact :=
    (forget₂ (Rep Coeff G) (ModuleCat Coeff)).reflects_exact_of_faithful _
      ((ShortComplex.moduleCat_exact_iff _).2 fun x hx => by
        -- `x : Coeff` with `red x = 0`; then `p ∣ x.down`
        have hx' : ((ULift.down x : ℤ) : ZMod p) = 0 := hx
        obtain ⟨k, hk⟩ := (ZMod.intCast_zmod_eq_zero_iff_dvd (ULift.down x) p).mp hx'
        refine ⟨ULift.up k, ?_⟩
        show p • (ULift.up k : Coeff) = x
        have hxy : (p • (ULift.up k : Coeff)).down = x.down := by
          show (p * k : ℤ) = x.down
          omega
        exact ULift.down_inj.mp hxy)
  mono_f := (Rep.mono_iff_injective _).2 (fun x y h => by
    have h' : (p • x : Coeff) = p • y := h
    have h2 : ((p • x : Coeff)).down = ((p • y : Coeff)).down := congrArg ULift.down h'
    change (p * x.down : ℤ) = p * y.down at h2
    have hpne : (p : ℤ) ≠ 0 := by exact_mod_cast hp
    exact ULift.down_inj.mp (mul_left_cancel₀ hpne h2))
  epi_g := (Rep.epi_iff_surjective _).2 (fun z => by
    have : NeZero p := ⟨hp⟩
    refine ⟨ULift.up (z.val : ℤ), ?_⟩
    change (redLin p) (ULift.up (z.val : ℤ)) = z
    show ((((z.val : ℤ)) : ZMod p)) = z
    simpa using ZMod.natCast_zmod_val z)

end Work.SSGRoute.E7cOmega
