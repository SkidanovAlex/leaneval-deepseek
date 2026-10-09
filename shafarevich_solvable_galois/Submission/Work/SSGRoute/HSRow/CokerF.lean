import Mathlib
import Submission.Work.SSGRoute.HSRow.CokerDefs
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# The `2`-cochain attached to a crossed homomorphism `C → Z1`

For a function `Φ : C → Z1` we define the `M`-valued `2`-cochain
`F(g,h) = res (p g) • Φ (p h) ((p g)⁻¹ q g (p g))` on `D = decomp k A`, where `q`, `p` are the
`I`- and `C`-coordinates of `HS.ip`/`HS.proj`.  If `Φ` is a crossed homomorphism (for the
conjugation action on `Z1`) satisfying `Φ 1 = 0` and vanishing on an open subgroup, then `F` is a
locally constant `2`-cocycle in normal form relative to `I` whose slice at `σ` is `Φ σ`.
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

/-- `p g` as an element of `C = closure (zpowers σ)`. -/
def PPC (M : Type) [AddCommGroup M] [Module (ZMod p) M]
    [DistribMulAction (K ≃ₐ[k] K) M] [SMulCommClass (K ≃ₐ[k] K) (ZMod p) M]
    (I : Subgroup (Ω ≃ₐ[k] Ω)) (σ : Ω ≃ₐ[k] Ω) (H : Hcx k Ω I σ)
    (g : ↥(SSGRoute.decomp k H.A)) : ↥(Ccl k Ω σ) :=
  ⟨Work.SSGRoute.PT.PP k Ω H.A I σ H.hI H.hnorm H.hσ H.hsup g,
    Work.SSGRoute.PT.PP_mem k Ω H.A I σ H.hI H.hnorm H.hσ H.hsup g⟩

@[simp] lemma PPC_coe (M : Type) [AddCommGroup M] [Module (ZMod p) M]
    [DistribMulAction (K ≃ₐ[k] K) M] [SMulCommClass (K ≃ₐ[k] K) (ZMod p) M]
    (I : Subgroup (Ω ≃ₐ[k] Ω)) (σ : Ω ≃ₐ[k] Ω) (H : Hcx k Ω I σ)
    (g : ↥(SSGRoute.decomp k H.A)) :
    ((PPC p k Ω K M I σ H g : ↥(Ccl k Ω σ)) : Ω ≃ₐ[k] Ω)
      = Work.SSGRoute.PT.PP k Ω H.A I σ H.hI H.hnorm H.hσ H.hsup g := rfl

/-- The `I`-coordinate of `g`, conjugated into the second variable, is the argument of `Φ`:
`(p g)⁻¹ q g (p g)`. -/
def Wg (M : Type) [AddCommGroup M] [Module (ZMod p) M]
    [DistribMulAction (K ≃ₐ[k] K) M] [SMulCommClass (K ≃ₐ[k] K) (ZMod p) M]
    (I : Subgroup (Ω ≃ₐ[k] Ω)) (σ : Ω ≃ₐ[k] Ω) (H : Hcx k Ω I σ)
    (g : ↥(SSGRoute.decomp k H.A)) : Ω ≃ₐ[k] Ω :=
  (Work.SSGRoute.PT.PP k Ω H.A I σ H.hI H.hnorm H.hσ H.hsup g)⁻¹ *
    (Work.SSGRoute.PT.Q k Ω H.A I σ H.hI H.hnorm H.hσ H.hsup g) *
    (Work.SSGRoute.PT.PP k Ω H.A I σ H.hI H.hnorm H.hσ H.hsup g)

lemma Wg_mem (M : Type) [AddCommGroup M] [Module (ZMod p) M]
    [DistribMulAction (K ≃ₐ[k] K) M] [SMulCommClass (K ≃ₐ[k] K) (ZMod p) M]
    (I : Subgroup (Ω ≃ₐ[k] Ω)) (σ : Ω ≃ₐ[k] Ω) (H : Hcx k Ω I σ)
    (g : ↥(SSGRoute.decomp k H.A)) : Wg p k Ω K M I σ H g ∈ I := by
  have hP : Work.SSGRoute.PT.PP k Ω H.A I σ H.hI H.hnorm H.hσ H.hsup g
      ∈ SSGRoute.decomp k H.A :=
    Work.SSGRoute.PT.PP_mem_D k Ω H.A I σ H.hI H.hnorm H.hσ H.hsup g
  have h1 : (Work.SSGRoute.PT.PP k Ω H.A I σ H.hI H.hnorm H.hσ H.hsup g)⁻¹ ∈
      SSGRoute.decomp k H.A := (SSGRoute.decomp k H.A).inv_mem hP
  have h2 := H.hnorm (Work.SSGRoute.PT.PP k Ω H.A I σ H.hI H.hnorm H.hσ H.hsup g)⁻¹ h1
    (Work.SSGRoute.PT.Q k Ω H.A I σ H.hI H.hnorm H.hσ H.hsup g)
    (Work.SSGRoute.PT.Q_mem k Ω H.A I σ H.hI H.hnorm H.hσ H.hsup g)
  simpa [Wg] using h2

/-- The `2`-cochain attached to `Φ`. -/
def Fof (M : Type) [AddCommGroup M] [Module (ZMod p) M]
    [DistribMulAction (K ≃ₐ[k] K) M] [SMulCommClass (K ≃ₐ[k] K) (ZMod p) M]
    (I : Subgroup (Ω ≃ₐ[k] Ω)) (σ : Ω ≃ₐ[k] Ω) (H : Hcx k Ω I σ)
    (Φ : ↥(Ccl k Ω σ) → ↥(Z1 p k Ω K M I))
    (g h : ↥(SSGRoute.decomp k H.A)) : M :=
  SSGRoute.res k K (Work.SSGRoute.PT.PP k Ω H.A I σ H.hI H.hnorm H.hσ H.hsup g)
    • ((Φ (PPC p k Ω K M I σ H h) : (Ω ≃ₐ[k] Ω) → M) (Wg p k Ω K M I σ H g))

@[simp] lemma Fof_apply (M : Type) [AddCommGroup M] [Module (ZMod p) M]
    [DistribMulAction (K ≃ₐ[k] K) M] [SMulCommClass (K ≃ₐ[k] K) (ZMod p) M]
    (I : Subgroup (Ω ≃ₐ[k] Ω)) (σ : Ω ≃ₐ[k] Ω) (H : Hcx k Ω I σ)
    (Φ : ↥(Ccl k Ω σ) → ↥(Z1 p k Ω K M I))
    (g h : ↥(SSGRoute.decomp k H.A)) :
    Fof p k Ω K M I σ H Φ g h
      = SSGRoute.res k K (Work.SSGRoute.PT.PP k Ω H.A I σ H.hI H.hnorm H.hσ H.hsup g)
        • ((Φ (PPC p k Ω K M I σ H h) : (Ω ≃ₐ[k] Ω) → M) (Wg p k Ω K M I σ H g)) := rfl

lemma PPC_eq_one (M : Type) [AddCommGroup M] [Module (ZMod p) M]
    [DistribMulAction (K ≃ₐ[k] K) M] [SMulCommClass (K ≃ₐ[k] K) (ZMod p) M]
    (I : Subgroup (Ω ≃ₐ[k] Ω)) (σ : Ω ≃ₐ[k] Ω) (H : Hcx k Ω I σ)
    {n : Ω ≃ₐ[k] Ω} (hn : n ∈ I) :
    PPC p k Ω K M I σ H ⟨n, H.hI hn⟩ = 1 := by
  refine Subtype.ext ?_
  rw [PPC_coe, Subgroup.coe_one]
  exact Work.SSGRoute.PT.PP_mem_I_coe k Ω H.A I σ H.hI H.hnorm H.hσ H.hsup H.hinf hn

lemma Wg_eq_of_mem_I (M : Type) [AddCommGroup M] [Module (ZMod p) M]
    [DistribMulAction (K ≃ₐ[k] K) M] [SMulCommClass (K ≃ₐ[k] K) (ZMod p) M]
    (I : Subgroup (Ω ≃ₐ[k] Ω)) (σ : Ω ≃ₐ[k] Ω) (H : Hcx k Ω I σ)
    {n : Ω ≃ₐ[k] Ω} (hn : n ∈ I) :
    Wg p k Ω K M I σ H ⟨n, H.hI hn⟩ = n := by
  rw [Wg, Work.SSGRoute.PT.PP_mem_I_coe k Ω H.A I σ H.hI H.hnorm H.hσ H.hsup H.hinf hn,
    Work.SSGRoute.PT.Q_eq_of_mem_I k Ω H.A I σ H.hI H.hnorm H.hσ H.hsup H.hinf hn]
  group

lemma PPC_sigC (M : Type) [AddCommGroup M] [Module (ZMod p) M]
    [DistribMulAction (K ≃ₐ[k] K) M] [SMulCommClass (K ≃ₐ[k] K) (ZMod p) M]
    (I : Subgroup (Ω ≃ₐ[k] Ω)) (σ : Ω ≃ₐ[k] Ω) (H : Hcx k Ω I σ) :
    PPC p k Ω K M I σ H ⟨σ, H.hσ⟩ = sigC k Ω σ := by
  refine Subtype.ext ?_
  rw [PPC_coe]
  exact Work.SSGRoute.PT.PP_eq_of_mem_C k Ω H.A I σ H.hI H.hnorm H.hσ H.hsup H.hinf
    (Subgroup.le_topologicalClosure _ (Subgroup.mem_zpowers σ))

lemma Wg_sigC_eq_one (M : Type) [AddCommGroup M] [Module (ZMod p) M]
    [DistribMulAction (K ≃ₐ[k] K) M] [SMulCommClass (K ≃ₐ[k] K) (ZMod p) M]
    (I : Subgroup (Ω ≃ₐ[k] Ω)) (σ : Ω ≃ₐ[k] Ω) (H : Hcx k Ω I σ) :
    Wg p k Ω K M I σ H ⟨σ, H.hσ⟩ = 1 := by
  rw [Wg,
    Work.SSGRoute.PT.PP_eq_of_mem_C k Ω H.A I σ H.hI H.hnorm H.hσ H.hsup H.hinf
      (Subgroup.le_topologicalClosure _ (Subgroup.mem_zpowers σ)),
    Work.SSGRoute.PT.Q_eq_one_of_mem_C k Ω H.A I σ H.hI H.hnorm H.hσ H.hsup H.hinf
      (Subgroup.le_topologicalClosure _ (Subgroup.mem_zpowers σ))]
  group

/-- **The normal form**: `F` vanishes in the second variable on `I`. -/
lemma Fof_normal (M : Type) [AddCommGroup M] [Module (ZMod p) M]
    [DistribMulAction (K ≃ₐ[k] K) M] [SMulCommClass (K ≃ₐ[k] K) (ZMod p) M]
    (I : Subgroup (Ω ≃ₐ[k] Ω)) (σ : Ω ≃ₐ[k] Ω) (H : Hcx k Ω I σ)
    (Φ : ↥(Ccl k Ω σ) → ↥(Z1 p k Ω K M I)) (hΦ1 : Φ 1 = 0)
    (g : ↥(SSGRoute.decomp k H.A)) {n : Ω ≃ₐ[k] Ω} (hn : n ∈ I) :
    Fof p k Ω K M I σ H Φ g ⟨n, H.hI hn⟩ = 0 := by
  rw [Fof, PPC_eq_one p k Ω K M I σ H hn, hΦ1]
  simp

/-- **The slice at `σ`**. -/
lemma Fof_slice (M : Type) [AddCommGroup M] [Module (ZMod p) M]
    [DistribMulAction (K ≃ₐ[k] K) M] [SMulCommClass (K ≃ₐ[k] K) (ZMod p) M]
    (I : Subgroup (Ω ≃ₐ[k] Ω)) (σ : Ω ≃ₐ[k] Ω) (H : Hcx k Ω I σ)
    (Φ : ↥(Ccl k Ω σ) → ↥(Z1 p k Ω K M I)) {n : Ω ≃ₐ[k] Ω} (hn : n ∈ I) :
    Fof p k Ω K M I σ H Φ ⟨n, H.hI hn⟩ ⟨σ, H.hσ⟩
      = (Φ (sigC k Ω σ) : (Ω ≃ₐ[k] Ω) → M) n := by
  rw [Fof, PPC_sigC p k Ω K M I σ H, Wg_eq_of_mem_I p k Ω K M I σ H hn,
    Work.SSGRoute.PT.PP_mem_I_coe k Ω H.A I σ H.hI H.hnorm H.hσ H.hsup H.hinf hn, map_one,
    one_smul]

end

end Work.SSGRoute.HSRow
