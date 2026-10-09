import Mathlib
import Submission.Work.SSGRoute.ZDataTwo.ArchKummer
import Submission.Work.SSGRoute.LTDArch.Defs
import Submission.Work.SSGRoute.DualMod.Main
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace Work.SSGRoute.ZDataTwo

open scoped TensorProduct

/-- The archimedean pairing `Ach.archPair` at `p = 2` computes the product of the Kummer
characters: `(g c) (f c ⊗ t₀) = f c * ((g c) (1 ⊗ t₀))`. -/
lemma archPair_two_eq_mul
    {k Ω : Type} [Field k] [NumberField k] [Field Ω] [Algebra k Ω] [IsAlgClosure k Ω]
    [IsAlgClosed Ω]
    (c : Ω ≃ₐ[k] Ω) (hT : Module.finrank (ZMod 2) (ZMod 2) = 1)
    (f : (Ω ≃ₐ[k] Ω) → ZMod 2)
    (g : (Ω ≃ₐ[k] Ω) → Work.SSGRoute.DualMod 2 (ZMod 2 ⊗[ZMod 2] ZMod 2)) :
    Work.SSGRoute.Ach.archPair 2 (Ω ≃ₐ[k] Ω) (ZMod 2) (ZMod 2) hT c f g =
      f c * ((g c) ((1 : ZMod 2) ⊗ₜ[ZMod 2] Work.SSGRoute.Ach.t0 2 (ZMod 2) hT)) := by
  rw [Work.SSGRoute.Ach.archPair_apply_of_eq_two 2 (Ω ≃ₐ[k] Ω) (ZMod 2) (ZMod 2)
    (h := hT) rfl c f g]
  have htensor : f c ⊗ₜ[ZMod 2] Work.SSGRoute.Ach.t0 2 (ZMod 2) hT
      = (f c) • ((1 : ZMod 2) ⊗ₜ[ZMod 2] Work.SSGRoute.Ach.t0 2 (ZMod 2) hT) := by
    conv_lhs => rw [show f c = f c • (1 : ZMod 2) by simp]
    rw [TensorProduct.smul_tmul, TensorProduct.tmul_smul]
  rw [htensor, map_smul, smul_eq_mul]

/-- **The archimedean local Tate pairing at `p = 2` is the real Hilbert symbol.**  Let `c ∈ G_k` be an
involution — equivalently (Artin–Schreier) the conjugation at a real place of `K` — and let `f`, `g`
be cochains which agree on `K.fixingSubgroup` with the Kummer cochains of `α, β ∈ (↥K)ˣ`.  Then the
explicit archimedean pairing `Ach.archPair` (at `p = 2`, `E = T = 𝔽₂`) vanishes exactly when one of
the two classes is positive at that real place — i.e. when `α` or `β` is a square in the fixed field
`Ω^c`:

  `(α, β)_ℝ = 1  ⟺  α > 0 or β > 0`.

This is the arithmetic identification of the archimedean half of the reciprocity clause: with it and
Hilbert reciprocity (`Work.HilbertSymbolGeneral.hilbertReciprocityTwo`) the archimedean contribution
to `E7Arch.glue_of_finiteHalf`'s `hrecJoint` becomes a statement about local Hilbert symbols.  It is
the composition of the two-line value computation `archPair … = f c * ((g c) (1 ⊗ t₀))` with the
dictionary `Work.SSGRoute.nodeKummerCochar_eq_zero_iff_exists_sqrt_fixed` (and `x * y = 0 ↔ x = 0 ∨
y = 0` in the field `𝔽₂`); the `nodeKummerCochar` unfolding may need a raised `maxHeartbeats`. -/
theorem archPair_two_kummer_eq_zero_iff
    {k Ω : Type} [Field k] [NumberField k] [Field Ω] [Algebra k Ω] [IsAlgClosure k Ω]
    [IsAlgClosed Ω]
    (K : IntermediateField k Ω) [FiniteDimensional k K] [IsGalois k K]
    (ζ : Ω) (hζK : ζ ∈ K) (hζ : IsPrimitiveRoot ζ 2)
    (α β : (↥K)ˣ) (c : Ω ≃ₐ[k] Ω) (hc : c ∈ K.fixingSubgroup) (hc2 : c ^ 2 = 1)
    (hT : Module.finrank (ZMod 2) (ZMod 2) = 1)
    (f : (Ω ≃ₐ[k] Ω) → ZMod 2)
    (g : (Ω ≃ₐ[k] Ω) → Work.SSGRoute.DualMod 2 (ZMod 2 ⊗[ZMod 2] ZMod 2))
    (hf : ∀ σ ∈ K.fixingSubgroup, f σ = Work.SSGRoute.nodeKummerCochar K ζ hζK hζ α σ)
    (hg : ∀ σ ∈ K.fixingSubgroup,
      (g σ) ((1 : ZMod 2) ⊗ₜ[ZMod 2] Work.SSGRoute.Ach.t0 2 (ZMod 2) hT)
        = Work.SSGRoute.nodeKummerCochar K ζ hζK hζ β σ) :
    Work.SSGRoute.Ach.archPair 2 (Ω ≃ₐ[k] Ω) (ZMod 2) (ZMod 2) hT c f g = 0 ↔
      (∃ y : Ω, ((IntermediateField.fixingSubgroupEquiv K) ⟨c, hc⟩ : Ω ≃ₐ[↥K] Ω) y = y ∧
          y ^ 2 = algebraMap ↥K Ω (α : ↥K)) ∨
      (∃ y : Ω, ((IntermediateField.fixingSubgroupEquiv K) ⟨c, hc⟩ : Ω ≃ₐ[↥K] Ω) y = y ∧
          y ^ 2 = algebraMap ↥K Ω (β : ↥K)) := by
  have hα := Work.SSGRoute.nodeKummerCochar_eq_zero_iff_exists_sqrt_fixed K ζ hζK hζ α c hc
  have hβ := Work.SSGRoute.nodeKummerCochar_eq_zero_iff_exists_sqrt_fixed K ζ hζK hζ β c hc
  rw [archPair_two_eq_mul c hT f g, hf c hc, hg c hc, mul_eq_zero, hα, hβ]

end Work.SSGRoute.ZDataTwo
