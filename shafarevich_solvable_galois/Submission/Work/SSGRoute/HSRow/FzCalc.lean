import Mathlib.FieldTheory.KrullTopology
import Mathlib.RingTheory.Henselian
import Mathlib.Algebra.Field.ZMod
import Mathlib.NumberTheory.NumberField.Basic
import Mathlib.RingTheory.Flat.TorsionFree
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
import Submission.Work.SSGRoute.HSRow.NormalFormDefs
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# The coordinate calculus for the normal form `Fz Φ`

Setting: `D = decomp k A = I ⋊ C` with `C = closure (zpowers σ)` (the two coordinates `q`, `p`
of `d = q d * p d` are `PT.Q`, `PT.PP`), `M` an `𝔽_p`-module with a `Gal(K/k)`-action,
`Zr = Z¹_loc(I,M)` the module of locally constant `1`-cocycles on `I`.

This file collects the elementary calculus used by the two halves (`2`-cocycle identity, local
constancy) of the statement that the normal form
`Fz Φ g h = ρ(p g) • Φ(p h)((p g)⁻¹ q g (p g))` of a crossed homomorphism `Φ : C → Zr` is a
locally constant `2`-cocycle on `D`:

* the abbreviations `Qq`, `Pp`, `Ppc`, `WgI` (the coordinates as elements of `Gal(Ω/k)`, of
  `C`, and of `↥I`);
* multiplicativity of the coordinates (`Pp_mul`, `Ppc_mul`, `WgI_mul_coe`, `WgI_mul`);
* the two rewriting identities `Pp_mul_WgI`, `g_mul_Pp` behind the cancellation in the `2`-cocycle
  identity;
* the `1`-cocycle law `Zr_cocycle` and the normalisation `Zr_one` of the values of `Φ`.
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

/-- The `I`-coordinate `q g` of `g ∈ D`, as an element of `Gal(Ω/k)`. -/
abbrev Qq (I : Subgroup (Ω ≃ₐ[k] Ω)) (σ : Ω ≃ₐ[k] Ω) (H : Hcx k Ω I σ)
    (g : ↥(SSGRoute.decomp k H.A)) : Ω ≃ₐ[k] Ω :=
  Work.SSGRoute.PT.Q k Ω H.A I σ H.hI H.hnorm H.hσ H.hsup g

/-- The `C`-coordinate `p g` of `g ∈ D`, as an element of `Gal(Ω/k)`. -/
abbrev Pp (I : Subgroup (Ω ≃ₐ[k] Ω)) (σ : Ω ≃ₐ[k] Ω) (H : Hcx k Ω I σ)
    (g : ↥(SSGRoute.decomp k H.A)) : Ω ≃ₐ[k] Ω :=
  Work.SSGRoute.PT.PP k Ω H.A I σ H.hI H.hnorm H.hσ H.hsup g

/-- The `C`-coordinate `p g` of `g ∈ D`, as an element of `C = closure (zpowers σ)`. -/
abbrev Ppc (M : Type) [AddCommGroup M] [Module (ZMod p) M]
    [DistribMulAction (K ≃ₐ[k] K) M] [SMulCommClass (K ≃ₐ[k] K) (ZMod p) M]
    (I : Subgroup (Ω ≃ₐ[k] Ω)) (σ : Ω ≃ₐ[k] Ω) (H : Hcx k Ω I σ)
    (g : ↥(SSGRoute.decomp k H.A)) : ↥(Ccl k Ω σ) :=
  PPC p k Ω K M I σ H g

/-- `Wg g = (p g)⁻¹ q g (p g) = (p g)⁻¹ g`, as an element of `↥I`. -/
abbrev WgI (M : Type) [AddCommGroup M] [Module (ZMod p) M]
    [DistribMulAction (K ≃ₐ[k] K) M] [SMulCommClass (K ≃ₐ[k] K) (ZMod p) M]
    (I : Subgroup (Ω ≃ₐ[k] Ω)) (σ : Ω ≃ₐ[k] Ω) (H : Hcx k Ω I σ)
    (g : ↥(SSGRoute.decomp k H.A)) : ↥I :=
  ⟨Wg p k Ω K M I σ H g, Wg_mem p k Ω K M I σ H g⟩

/-- The factorisation `q g * p g = g`. -/
lemma Qq_mul_Pp (I : Subgroup (Ω ≃ₐ[k] Ω)) (σ : Ω ≃ₐ[k] Ω) (H : Hcx k Ω I σ)
    (g : ↥(SSGRoute.decomp k H.A)) :
    Qq k Ω I σ H g * Pp k Ω I σ H g = (g : Ω ≃ₐ[k] Ω) :=
  Work.SSGRoute.PT.Q_mul_PP k Ω H.A I σ H.hI H.hnorm H.hσ H.hsup g

/-- The `I`-coordinate lies in `I`. -/
lemma Qq_mem (I : Subgroup (Ω ≃ₐ[k] Ω)) (σ : Ω ≃ₐ[k] Ω) (H : Hcx k Ω I σ)
    (g : ↥(SSGRoute.decomp k H.A)) : Qq k Ω I σ H g ∈ I :=
  Work.SSGRoute.PT.Q_mem k Ω H.A I σ H.hI H.hnorm H.hσ H.hsup g

/-- The `C`-coordinate lies in `C`. -/
lemma Pp_mem_C (I : Subgroup (Ω ≃ₐ[k] Ω)) (σ : Ω ≃ₐ[k] Ω) (H : Hcx k Ω I σ)
    (g : ↥(SSGRoute.decomp k H.A)) : Pp k Ω I σ H g ∈ Ccl k Ω σ :=
  Work.SSGRoute.PT.PP_mem k Ω H.A I σ H.hI H.hnorm H.hσ H.hsup g

/-- The `C`-coordinate lies in `D`. -/
lemma Pp_mem_D (I : Subgroup (Ω ≃ₐ[k] Ω)) (σ : Ω ≃ₐ[k] Ω) (H : Hcx k Ω I σ)
    (g : ↥(SSGRoute.decomp k H.A)) : Pp k Ω I σ H g ∈ SSGRoute.decomp k H.A :=
  Work.SSGRoute.PT.PP_mem_D k Ω H.A I σ H.hI H.hnorm H.hσ H.hsup g

/-- The `C`-coordinate is multiplicative. -/
lemma Pp_mul (I : Subgroup (Ω ≃ₐ[k] Ω)) (σ : Ω ≃ₐ[k] Ω) (H : Hcx k Ω I σ)
    (g h : ↥(SSGRoute.decomp k H.A)) :
    Pp k Ω I σ H (g * h) = Pp k Ω I σ H g * Pp k Ω I σ H h :=
  congrArg Subtype.val (Work.SSGRoute.HS.proj_mul H.A I σ H.hI H.hnorm
    (Work.SSGRoute.HS.CC_le_DD H.A σ H.hσ) H.hsup H.hinf g h)

/-- The `C`-coordinate is multiplicative, as an equality in `↥C`. -/
lemma Ppc_mul (M : Type) [AddCommGroup M] [Module (ZMod p) M]
    [DistribMulAction (K ≃ₐ[k] K) M] [SMulCommClass (K ≃ₐ[k] K) (ZMod p) M]
    (I : Subgroup (Ω ≃ₐ[k] Ω)) (σ : Ω ≃ₐ[k] Ω) (H : Hcx k Ω I σ)
    (g h : ↥(SSGRoute.decomp k H.A)) :
    Ppc p k Ω K M I σ H (g * h) = Ppc p k Ω K M I σ H g * Ppc p k Ω K M I σ H h :=
  Subtype.ext (Pp_mul k Ω I σ H g h)

/-- `(p g)⁻¹ q g (p g) = (p g)⁻¹ g`. -/
@[simp] lemma WgI_coe (M : Type) [AddCommGroup M] [Module (ZMod p) M]
    [DistribMulAction (K ≃ₐ[k] K) M] [SMulCommClass (K ≃ₐ[k] K) (ZMod p) M]
    (I : Subgroup (Ω ≃ₐ[k] Ω)) (σ : Ω ≃ₐ[k] Ω) (H : Hcx k Ω I σ)
    (g : ↥(SSGRoute.decomp k H.A)) :
    ((WgI p k Ω K M I σ H g : ↥I) : Ω ≃ₐ[k] Ω) = (Pp k Ω I σ H g)⁻¹ * (g : Ω ≃ₐ[k] Ω) := by
  rw [show ((WgI p k Ω K M I σ H g : ↥I) : Ω ≃ₐ[k] Ω)
      = (Pp k Ω I σ H g)⁻¹ * Qq k Ω I σ H g * Pp k Ω I σ H g from rfl,
    mul_assoc, Qq_mul_Pp]

/-- `Wg` of a product, on the level of `Gal(Ω/k)`:
`(p h)⁻¹ (p g)⁻¹ (g h) = ((p h)⁻¹ Wg g (p h)) · Wg h`. -/
lemma WgI_mul_coe (M : Type) [AddCommGroup M] [Module (ZMod p) M]
    [DistribMulAction (K ≃ₐ[k] K) M] [SMulCommClass (K ≃ₐ[k] K) (ZMod p) M]
    (I : Subgroup (Ω ≃ₐ[k] Ω)) (σ : Ω ≃ₐ[k] Ω) (H : Hcx k Ω I σ)
    (g h : ↥(SSGRoute.decomp k H.A)) :
    ((WgI p k Ω K M I σ H (g * h) : ↥I) : Ω ≃ₐ[k] Ω)
      = (Pp k Ω I σ H h)⁻¹ * ((WgI p k Ω K M I σ H g : ↥I) : Ω ≃ₐ[k] Ω)
          * (Pp k Ω I σ H h)
          * ((WgI p k Ω K M I σ H h : ↥I) : Ω ≃ₐ[k] Ω) := by
  rw [WgI_coe, WgI_coe, WgI_coe,
    show ((g * h : ↥(SSGRoute.decomp k H.A)) : Ω ≃ₐ[k] Ω)
      = (g : Ω ≃ₐ[k] Ω) * (h : Ω ≃ₐ[k] Ω) from rfl,
    Pp_mul k Ω I σ H g h,
    ← Qq_mul_Pp k Ω I σ H g, ← Qq_mul_Pp k Ω I σ H h]
  group

/-- `Wg` of a product, as an equality in `↥I`:
`Wg (g h) = (p h)⁻¹ Wg g (p h) · Wg h = conjI (p h) (Wg g) * Wg h`. -/
lemma WgI_mul (M : Type) [AddCommGroup M] [Module (ZMod p) M]
    [DistribMulAction (K ≃ₐ[k] K) M] [SMulCommClass (K ≃ₐ[k] K) (ZMod p) M]
    (I : Subgroup (Ω ≃ₐ[k] Ω)) (σ : Ω ≃ₐ[k] Ω) (H : Hcx k Ω I σ)
    (g h : ↥(SSGRoute.decomp k H.A)) :
    WgI p k Ω K M I σ H (g * h)
      = conjI p k Ω K M I σ H (Ppc p k Ω K M I σ H h) (WgI p k Ω K M I σ H g)
        * WgI p k Ω K M I σ H h := by
  refine Subtype.ext ?_
  show ((WgI p k Ω K M I σ H (g * h) : ↥I) : Ω ≃ₐ[k] Ω)
      = (Pp k Ω I σ H h)⁻¹ * ((WgI p k Ω K M I σ H g : ↥I) : Ω ≃ₐ[k] Ω)
          * (Pp k Ω I σ H h)
          * ((WgI p k Ω K M I σ H h : ↥I) : Ω ≃ₐ[k] Ω)
  exact WgI_mul_coe p k Ω K M I σ H g h

/-- `p 1 = 1`. -/
@[simp] lemma Pp_one (I : Subgroup (Ω ≃ₐ[k] Ω)) (σ : Ω ≃ₐ[k] Ω) (H : Hcx k Ω I σ) :
    Pp k Ω I σ H 1 = 1 :=
  Work.SSGRoute.PT.PP_mem_I_coe k Ω H.A I σ H.hI H.hnorm H.hσ H.hsup H.hinf
    (d := (1 : ↥(SSGRoute.decomp k H.A))) I.one_mem

/-- `q 1 = 1`. -/
@[simp] lemma Qq_one (I : Subgroup (Ω ≃ₐ[k] Ω)) (σ : Ω ≃ₐ[k] Ω) (H : Hcx k Ω I σ) :
    Qq k Ω I σ H 1 = 1 :=
  Work.SSGRoute.PT.Q_eq_of_mem_I k Ω H.A I σ H.hI H.hnorm H.hσ H.hsup H.hinf
    (d := (1 : ↥(SSGRoute.decomp k H.A))) I.one_mem

/-- `p 1 = 1` in `↥C`. -/
@[simp] lemma Ppc_one (M : Type) [AddCommGroup M] [Module (ZMod p) M]
    [DistribMulAction (K ≃ₐ[k] K) M] [SMulCommClass (K ≃ₐ[k] K) (ZMod p) M]
    (I : Subgroup (Ω ≃ₐ[k] Ω)) (σ : Ω ≃ₐ[k] Ω) (H : Hcx k Ω I σ) :
    Ppc p k Ω K M I σ H 1 = 1 :=
  Subtype.ext (Pp_one k Ω I σ H)

/-- `Wg 1 = 1`. -/
@[simp] lemma WgI_one (M : Type) [AddCommGroup M] [Module (ZMod p) M]
    [DistribMulAction (K ≃ₐ[k] K) M] [SMulCommClass (K ≃ₐ[k] K) (ZMod p) M]
    (I : Subgroup (Ω ≃ₐ[k] Ω)) (σ : Ω ≃ₐ[k] Ω) (H : Hcx k Ω I σ) :
    WgI p k Ω K M I σ H 1 = 1 := by
  refine Subtype.ext ?_
  show Wg p k Ω K M I σ H 1 = (1 : Ω ≃ₐ[k] Ω)
  rw [show Wg p k Ω K M I σ H 1
      = (Pp k Ω I σ H 1)⁻¹ * Qq k Ω I σ H 1 * Pp k Ω I σ H 1 from rfl,
    show Pp k Ω I σ H 1 = 1 from
      Work.SSGRoute.PT.PP_mem_I_coe k Ω H.A I σ H.hI H.hnorm H.hσ H.hsup H.hinf
        (d := (1 : ↥(SSGRoute.decomp k H.A))) I.one_mem,
    show Qq k Ω I σ H 1 = 1 from
      Work.SSGRoute.PT.Q_eq_of_mem_I k Ω H.A I σ H.hI H.hnorm H.hσ H.hsup H.hinf
        (d := (1 : ↥(SSGRoute.decomp k H.A))) I.one_mem]
  group

/-- The `res`-argument identity behind the cancellation of the `(l,·)`-terms in the `2`-cocycle
identity: `p (g h) · ((p h)⁻¹ Wg g (p h)) = g · p h`. -/
lemma Pp_mul_WgI (M : Type) [AddCommGroup M] [Module (ZMod p) M]
    [DistribMulAction (K ≃ₐ[k] K) M] [SMulCommClass (K ≃ₐ[k] K) (ZMod p) M]
    (I : Subgroup (Ω ≃ₐ[k] Ω)) (σ : Ω ≃ₐ[k] Ω) (H : Hcx k Ω I σ)
    (g h : ↥(SSGRoute.decomp k H.A)) :
    Pp k Ω I σ H (g * h)
        * ((Pp k Ω I σ H h)⁻¹ * ((WgI p k Ω K M I σ H g : ↥I) : Ω ≃ₐ[k] Ω) * Pp k Ω I σ H h)
      = (g : Ω ≃ₐ[k] Ω) * Pp k Ω I σ H h := by
  rw [WgI_coe, Pp_mul k Ω I σ H g h]
  group

/-- The `res`-argument identity `g · p h = q g · p (g h)`. -/
lemma g_mul_Pp (I : Subgroup (Ω ≃ₐ[k] Ω)) (σ : Ω ≃ₐ[k] Ω) (H : Hcx k Ω I σ)
    (g h : ↥(SSGRoute.decomp k H.A)) :
    (g : Ω ≃ₐ[k] Ω) * Pp k Ω I σ H h = Qq k Ω I σ H g * Pp k Ω I σ H (g * h) := by
  rw [Pp_mul k Ω I σ H g h, ← Qq_mul_Pp k Ω I σ H g]
  group

/-- A value `V ∈ Zr` is a `1`-cocycle on `I`. -/
lemma Zr_cocycle (M : Type) [AddCommGroup M] [Module (ZMod p) M]
    [DistribMulAction (K ≃ₐ[k] K) M] [SMulCommClass (K ≃ₐ[k] K) (ZMod p) M]
    (I : Subgroup (Ω ≃ₐ[k] Ω)) (V : ↥(Zr p k Ω K M I)) (x y : ↥I) :
    (V : ↥I → M) (x * y)
      = (V : ↥I → M) x + SSGRoute.res k K (x : Ω ≃ₐ[k] Ω) • (V : ↥I → M) y :=
  V.2.1 x y

/-- A value `V ∈ Zr` vanishes at `1`. -/
lemma Zr_one (M : Type) [AddCommGroup M] [Module (ZMod p) M]
    [DistribMulAction (K ≃ₐ[k] K) M] [SMulCommClass (K ≃ₐ[k] K) (ZMod p) M]
    (I : Subgroup (Ω ≃ₐ[k] Ω)) (V : ↥(Zr p k Ω K M I)) :
    (V : ↥I → M) 1 = 0 := by
  have h := V.2.1 1 1
  simp only [mul_one, Subgroup.coe_one, map_one, one_smul] at h
  exact add_left_cancel (h.symm.trans (add_zero _).symm)

end

end Work.SSGRoute.HSRow
