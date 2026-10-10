import Mathlib.RingTheory.Henselian
import Mathlib.Algebra.Field.ZMod
import Mathlib.NumberTheory.NumberField.Basic
import Mathlib.RingTheory.Flat.TorsionFree
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
import Submission.Work.SSGRoute.HSRow.CokerZr2
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# The `2`-cochain `Fz` attached to a `Zr`-valued crossed homomorphism

`Fz Φ` is the `M`-valued `2`-cochain on `D = decomp k A`
`F(g,h) = res (p g) • Φ (p h) ((p g)⁻¹ q g (p g))`, where `p`, `q` are the `C`- and
`I`-coordinates of `HS.proj`/`HS.ip` and `Φ` takes values in the module `Zr` of locally constant
`1`-cocycles on `↥I`.  Its normal form and its slice at `σ` are computed below.
-/

open scoped Pointwise
open Classical

namespace Work.SSGRoute.HSRow

noncomputable section

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option maxHeartbeats 1000000

variable (p : ℕ) [Fact p.Prime] (k Ω : Type) [Field k] [NumberField k] [Field Ω] [Algebra k Ω]
  [IsAlgClosure k Ω] (K : IntermediateField k Ω) [FiniteDimensional k K] [IsGalois k K]

/-- The `2`-cochain attached to a `Zr`-valued function `Φ` on `C`. -/
def Fz (M : Type) [AddCommGroup M] [Module (ZMod p) M]
    [DistribMulAction (K ≃ₐ[k] K) M] [SMulCommClass (K ≃ₐ[k] K) (ZMod p) M]
    (I : Subgroup (Ω ≃ₐ[k] Ω)) (σ : Ω ≃ₐ[k] Ω) (H : Hcx k Ω I σ)
    (Φ : ↥(Ccl k Ω σ) → ↥(Zr p k Ω K M I))
    (g h : ↥(SSGRoute.decomp k H.A)) : M :=
  SSGRoute.res k K (Work.SSGRoute.PT.PP k Ω H.A I σ H.hI H.hnorm H.hσ H.hsup g)
    • ((Φ (PPC p k Ω K M I σ H h) : ↥I → M)
        ⟨Wg p k Ω K M I σ H g, Wg_mem p k Ω K M I σ H g⟩)

@[simp] lemma Fz_apply (M : Type) [AddCommGroup M] [Module (ZMod p) M]
    [DistribMulAction (K ≃ₐ[k] K) M] [SMulCommClass (K ≃ₐ[k] K) (ZMod p) M]
    (I : Subgroup (Ω ≃ₐ[k] Ω)) (σ : Ω ≃ₐ[k] Ω) (H : Hcx k Ω I σ)
    (Φ : ↥(Ccl k Ω σ) → ↥(Zr p k Ω K M I))
    (g h : ↥(SSGRoute.decomp k H.A)) :
    Fz p k Ω K M I σ H Φ g h
      = SSGRoute.res k K (Work.SSGRoute.PT.PP k Ω H.A I σ H.hI H.hnorm H.hσ H.hsup g)
        • ((Φ (PPC p k Ω K M I σ H h) : ↥I → M)
            ⟨Wg p k Ω K M I σ H g, Wg_mem p k Ω K M I σ H g⟩) := rfl

/-- **Normal form**: `Fz Φ` vanishes in the second variable on `I`. -/
lemma Fz_normal (M : Type) [AddCommGroup M] [Module (ZMod p) M]
    [DistribMulAction (K ≃ₐ[k] K) M] [SMulCommClass (K ≃ₐ[k] K) (ZMod p) M]
    (I : Subgroup (Ω ≃ₐ[k] Ω)) (σ : Ω ≃ₐ[k] Ω) (H : Hcx k Ω I σ)
    (Φ : ↥(Ccl k Ω σ) → ↥(Zr p k Ω K M I)) (hΦ1 : Φ 1 = 0)
    (g : ↥(SSGRoute.decomp k H.A)) {n : Ω ≃ₐ[k] Ω} (hn : n ∈ I) :
    Fz p k Ω K M I σ H Φ g ⟨n, H.hI hn⟩ = 0 := by
  rw [Fz, PPC_eq_one p k Ω K M I σ H hn, hΦ1]
  simp

/-- **The slice at `σ`** is the value of `Φ σ`. -/
lemma Fz_slice (M : Type) [AddCommGroup M] [Module (ZMod p) M]
    [DistribMulAction (K ≃ₐ[k] K) M] [SMulCommClass (K ≃ₐ[k] K) (ZMod p) M]
    (I : Subgroup (Ω ≃ₐ[k] Ω)) (σ : Ω ≃ₐ[k] Ω) (H : Hcx k Ω I σ)
    (Φ : ↥(Ccl k Ω σ) → ↥(Zr p k Ω K M I)) {n : Ω ≃ₐ[k] Ω} (hn : n ∈ I) :
    Fz p k Ω K M I σ H Φ ⟨n, H.hI hn⟩ ⟨σ, H.hσ⟩
      = (Φ (sigC k Ω σ) : ↥I → M) ⟨n, hn⟩ := by
  have hW : (⟨Wg p k Ω K M I σ H ⟨n, H.hI hn⟩,
      Wg_mem p k Ω K M I σ H ⟨n, H.hI hn⟩⟩ : ↥I) = ⟨n, hn⟩ :=
    Subtype.ext (Wg_eq_of_mem_I p k Ω K M I σ H hn)
  rw [Fz, PPC_sigC p k Ω K M I σ H,
    Work.SSGRoute.PT.PP_mem_I_coe k Ω H.A I σ H.hI H.hnorm H.hσ H.hsup H.hinf hn, map_one,
    one_smul, hW]

end

end Work.SSGRoute.HSRow
