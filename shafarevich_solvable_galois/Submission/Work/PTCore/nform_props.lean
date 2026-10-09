import Mathlib
import Submission.Work.PTCore.TransgressionDefs
import Submission.Work.PTCore.corrE_step
import Submission.Work.PTCore.corrE_isLocConstOn
import Submission.Work.PTCore.betaG_isLocConstOn
import Submission.Work.PTCore.chiExt_isLocConstOn
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# Properties of the normal form `nform`

This file collects the basic cohomological properties of the normal form

`nform S c β χ = c₀ - d¹(corrE c₀) - d¹(chiExt χ)`,  `c₀ = c - d¹(betaG β)`,

of a locally constant `2`-cocycle `c` on the decomposition group `D = I ⋊ C`:

* `nform` is again a locally constant `2`-cocycle on `D`;
* it vanishes on `D × I` (`nform g n = 0` for `n ∈ I`), and hence is constant along the
  right `I`-cosets in the second variable;
* it vanishes on `C × C`;
* `c - nform = d¹(β̃ + corrE c₀ + χ̃)` is a locally constant coboundary.
-/

open scoped Pointwise
open Classical

namespace Work.PTCore

section Generic

variable {k Ω : Type} [Field k] [NumberField k] [Field Ω] [Algebra k Ω] [IsAlgClosure k Ω]
variable {p : ℕ} [Fact p.Prime] {K : IntermediateField k Ω} [FiniteDimensional k K] [IsGalois k K]
variable {M : Type} [AddCommGroup M] [Module (ZMod p) M]
variable [DistribMulAction (K ≃ₐ[k] K) M] [SMulCommClass (K ≃ₐ[k] K) (ZMod p) M]

/-- `d¹` is additive in the cochain. -/
theorem d1c_add (b b' : (Ω ≃ₐ[k] Ω) → M) :
    d1c (p:=p) (K:=K) M (b + b') = d1c (p:=p) (K:=K) M b + d1c (p:=p) (K:=K) M b' := by
  funext g h
  simp only [d1c_apply, Pi.add_apply, smul_add]
  abel

/-- The coboundary `d¹b` of any cochain is a `2`-cocycle. -/
theorem d1c_isCocycle2On (H : Subgroup (Ω ≃ₐ[k] Ω)) (b : (Ω ≃ₐ[k] Ω) → M) :
    SSGRoute.IsCocycle2On p k Ω K M H (d1c (p:=p) (K:=K) M b) := by
  intro g hg h hh l hl
  simp only [d1c_apply, map_mul, mul_smul, smul_add, smul_sub, mul_assoc]
  abel

/-- `2`-cocycles on `H` are closed under subtraction. -/
theorem isCocycle2On_sub (H : Subgroup (Ω ≃ₐ[k] Ω))
    (a b : (Ω ≃ₐ[k] Ω) → (Ω ≃ₐ[k] Ω) → M)
    (h1 : SSGRoute.IsCocycle2On p k Ω K M H a)
    (h2 : SSGRoute.IsCocycle2On p k Ω K M H b) :
    SSGRoute.IsCocycle2On p k Ω K M H (a - b) := by
  intro g hg h hh l hl
  have e1 := h1 g hg h hh l hl
  have e2 := h2 g hg h hh l hl
  have key : SSGRoute.res k K g • (a - b) h l - (a - b) (g * h) l + (a - b) g (h * l)
        - (a - b) g h
      = (SSGRoute.res k K g • a h l - a (g * h) l + a g (h * l) - a g h)
        - (SSGRoute.res k K g • b h l - b (g * h) l + b g (h * l) - b g h) := by
    simp only [Pi.sub_apply, smul_sub]
    abel
  rw [key, e1, e2, sub_zero]

/-- `IsLocConstOn` is closed under addition. -/
theorem isLocConstOn_add (H : Subgroup (Ω ≃ₐ[k] Ω)) (f g : (Ω ≃ₐ[k] Ω) → M)
    (hf : SSGRoute.IsLocConstOn H f) (hg : SSGRoute.IsLocConstOn H g) :
    SSGRoute.IsLocConstOn H (f + g) := by
  obtain ⟨U1, ho1, h1⟩ := hf
  obtain ⟨U2, ho2, h2⟩ := hg
  refine ⟨U1 ⊓ U2, ?_, ?_⟩
  · rw [Subgroup.coe_inf]; exact ho1.inter ho2
  · intro a ha u hu huH
    rw [Pi.add_apply, Pi.add_apply, h1 a ha u (Subgroup.mem_inf.mp hu).1 huH,
      h2 a ha u (Subgroup.mem_inf.mp hu).2 huH]

/-- Locally constant `2`-cochains on `H` are closed under subtraction. -/
theorem isLocConst2On_sub (H : Subgroup (Ω ≃ₐ[k] Ω))
    (a b : (Ω ≃ₐ[k] Ω) → (Ω ≃ₐ[k] Ω) → M)
    (h1 : SSGRoute.IsLocConst2On p k Ω K M H a)
    (h2 : SSGRoute.IsLocConst2On p k Ω K M H b) :
    SSGRoute.IsLocConst2On p k Ω K M H (a - b) := by
  obtain ⟨U1, ho1, hU1⟩ := h1
  obtain ⟨U2, ho2, hU2⟩ := h2
  refine ⟨U1 ⊓ U2, ?_, ?_⟩
  · rw [Subgroup.coe_inf]; exact ho1.inter ho2
  · intro g hg h hh u hu v hv huH hvH
    have h1u : u ∈ U1 := (Subgroup.mem_inf.mp hu).1
    have h1v : v ∈ U1 := (Subgroup.mem_inf.mp hv).1
    have h2u : u ∈ U2 := (Subgroup.mem_inf.mp hu).2
    have h2v : v ∈ U2 := (Subgroup.mem_inf.mp hv).2
    simp only [Pi.sub_apply, hU1 g hg h hh u h1u v h1v huH hvH,
      hU2 g hg h hh u h2u v h2v huH hvH]

/-- The `1`-coboundary of a locally constant cochain is a locally constant `2`-cocycle. -/
theorem isLocConst2On_d1c (H : Subgroup (Ω ≃ₐ[k] Ω)) (b : (Ω ≃ₐ[k] Ω) → M)
    (hb : SSGRoute.IsLocConstOn H b) :
    SSGRoute.IsLocConst2On p k Ω K M H (d1c (p:=p) (K:=K) M b) := by
  obtain ⟨U, hUo, hU⟩ := hb
  have hUnorm : (U.normalCore).Normal := Subgroup.normalCore_normal U
  have hUle : U.normalCore ≤ U := Subgroup.normalCore_le U
  let W : Subgroup (Ω ≃ₐ[k] Ω) := U.normalCore ⊓ K.fixingSubgroup
  have hWres : ∀ u ∈ W, SSGRoute.res k K u = 1 := by
    intro u hu
    rw [← MonoidHom.mem_ker]
    rw [show (SSGRoute.res k K).ker = K.fixingSubgroup from
      IntermediateField.restrictNormalHom_ker (E := K)]
    exact (Subgroup.mem_inf.mp hu).2
  have hWopen : IsOpen (W : Set (Ω ≃ₐ[k] Ω)) := by
    have hUfin : U.FiniteIndex := by
      rw [Subgroup.finiteIndex_iff_finite_quotient]
      haveI : DiscreteTopology ((Ω ≃ₐ[k] Ω) ⧸ U) := QuotientGroup.discreteTopology_iff.mpr hUo
      exact finite_of_compact_of_discrete
    have hc : IsClosed ((U.normalCore : Subgroup (Ω ≃ₐ[k] Ω)) : Set (Ω ≃ₐ[k] Ω)) :=
      Subgroup.normalCore_isClosed U (Subgroup.isClosed_of_isOpen U hUo)
    rw [Subgroup.coe_inf]
    exact (Subgroup.isOpen_of_isClosed_of_finiteIndex _ hc).inter K.fixingSubgroup_isOpen
  refine ⟨W, hWopen, ?_⟩
  intro g hg h hh u hu v hv huH hvH
  have huNC : u ∈ U.normalCore := (Subgroup.mem_inf.mp hu).1
  have hvNC : v ∈ U.normalCore := (Subgroup.mem_inf.mp hv).1
  have hbv : b (h * v) = b h := hU h hh v (hUle hvNC) hvH
  have hbu : b (g * u) = b g := hU g hg u (hUle huNC) huH
  have hwNC : h⁻¹ * u * h ∈ U.normalCore := hUnorm.conj_mem u huNC h⁻¹
  have hwH : h⁻¹ * u * h ∈ H :=
    Subgroup.mul_mem _ (Subgroup.mul_mem _ (Subgroup.inv_mem _ hh) huH) hh
  have hwvNC : (h⁻¹ * u * h) * v ∈ U.normalCore := Subgroup.mul_mem _ hwNC hvNC
  have hwvH : (h⁻¹ * u * h) * v ∈ H := Subgroup.mul_mem _ hwH hvH
  have hgughv : b (g * u * (h * v)) = b (g * h) := by
    have he : g * u * (h * v) = (g * h) * ((h⁻¹ * u * h) * v) := by group
    rw [he]
    exact hU (g * h) (Subgroup.mul_mem _ hg hh) ((h⁻¹ * u * h) * v) (hUle hwvNC) hwvH
  rw [d1c_apply, d1c_apply, map_mul, hWres u hu, mul_one, hbv, hbu, hgughv]

end Generic

/-- On the normal subgroup `I`, the cochain `c₀ - d¹(corrE c₀)` vanishes. -/
theorem corrE_sub_eq_zero_on_I {k Ω : Type} [Field k] [NumberField k] [Field Ω] [Algebra k Ω]
    [IsAlgClosure k Ω]
    (S : DCtx k Ω) (p : ℕ) [Fact p.Prime] (K : IntermediateField k Ω)
    [FiniteDimensional k K] [IsGalois k K] (M : Type) [AddCommGroup M] [Module (ZMod p) M]
    [DistribMulAction (K ≃ₐ[k] K) M] [SMulCommClass (K ≃ₐ[k] K) (ZMod p) M]
    (c₀ : (Ω ≃ₐ[k] Ω) → (Ω ≃ₐ[k] Ω) → M)
    (hcoc : SSGRoute.IsCocycle2On p k Ω K M (SSGRoute.decomp k S.A) c₀)
    (hzero : ∀ n ∈ S.I, ∀ m ∈ S.I, c₀ n m = 0)
    {g n : Ω ≃ₐ[k] Ω} (hg : g ∈ SSGRoute.decomp k S.A) (hn : n ∈ S.I) :
    c₀ g n - d1c (p:=p) (K:=K) M (corrE (M:=M) S c₀) g n = 0 := by
  have hnD : n ∈ SSGRoute.decomp k S.A := S.hI hn
  rw [d1c_apply, corrE_step S p K M c₀ hcoc hzero hg hn, corrE_of_mem S c₀ hnD,
    projG_eq_one_of_mem_I S hn, coorG_eq_self_of_mem_I S hn, hzero 1 S.I.one_mem n hn]
  simp only [neg_zero, smul_zero]
  abel

/-- On the procyclic subgroup `C`, the coboundary of `corrE c₀` equals `-c₀ γ 1`. -/
theorem d1c_corrE_eq_neg_on_C {k Ω : Type} [Field k] [NumberField k] [Field Ω] [Algebra k Ω]
    [IsAlgClosure k Ω]
    (S : DCtx k Ω) (p : ℕ) [Fact p.Prime] (K : IntermediateField k Ω)
    [FiniteDimensional k K] [IsGalois k K] (M : Type) [AddCommGroup M] [Module (ZMod p) M]
    [DistribMulAction (K ≃ₐ[k] K) M] [SMulCommClass (K ≃ₐ[k] K) (ZMod p) M]
    (c₀ : (Ω ≃ₐ[k] Ω) → (Ω ≃ₐ[k] Ω) → M)
    (hcoc : SSGRoute.IsCocycle2On p k Ω K M (SSGRoute.decomp k S.A) c₀)
    {γ δ : Ω ≃ₐ[k] Ω}
    (hγ : γ ∈ Subgroup.topologicalClosure (Subgroup.zpowers S.σ))
    (hδ : δ ∈ Subgroup.topologicalClosure (Subgroup.zpowers S.σ)) :
    d1c (p:=p) (K:=K) M (corrE (M:=M) S c₀) γ δ = - c₀ γ 1 := by
  have hγD : γ ∈ SSGRoute.decomp k S.A := Work.SSGRoute.HS.CC_le_DD S.A S.σ S.hσ hγ
  have hδD : δ ∈ SSGRoute.decomp k S.A := Work.SSGRoute.HS.CC_le_DD S.A S.σ S.hσ hδ
  have hγδD : γ * δ ∈ SSGRoute.decomp k S.A := mul_mem hγD hδD
  have hγδC : γ * δ ∈ Subgroup.topologicalClosure (Subgroup.zpowers S.σ) :=
    Subgroup.mul_mem _ hγ hδ
  rw [d1c_apply, corrE_of_mem S c₀ hδD, corrE_of_mem S c₀ hγδD, corrE_of_mem S c₀ hγD,
    projG_eq_self_of_mem_C S hδ, coorG_eq_one_of_mem_C S hδ,
    projG_eq_self_of_mem_C S hγδC, coorG_eq_one_of_mem_C S hγδC,
    projG_eq_self_of_mem_C S hγ, coorG_eq_one_of_mem_C S hγ]
  have hc := hcoc γ hγD δ hδD 1 (S.hI S.I.one_mem)
  simp only [mul_one] at hc
  have hkey : SSGRoute.res k K γ • c₀ δ 1 = c₀ (γ * δ) 1 := by
    have hAB : SSGRoute.res k K γ • c₀ δ 1 - c₀ (γ * δ) 1 = 0 := by
      have h := hc
      rw [show (SSGRoute.res k K γ • c₀ δ 1 - c₀ (γ * δ) 1 + c₀ γ δ) - c₀ γ δ
          = SSGRoute.res k K γ • c₀ δ 1 - c₀ (γ * δ) 1 from by abel] at h
      exact h
    exact sub_eq_zero.mp hAB
  rw [smul_neg, hkey]
  abel

/-- On the normal subgroup `I`, the coboundary of `chiExt χ` vanishes (when `χ 1 = 0`). -/
theorem d1c_chiExt_eq_zero_on_I {k Ω : Type} [Field k] [NumberField k] [Field Ω] [Algebra k Ω]
    [IsAlgClosure k Ω]
    (S : DCtx k Ω) (p : ℕ) [Fact p.Prime] (K : IntermediateField k Ω)
    [FiniteDimensional k K] [IsGalois k K] (M : Type) [AddCommGroup M] [Module (ZMod p) M]
    [DistribMulAction (K ≃ₐ[k] K) M] [SMulCommClass (K ≃ₐ[k] K) (ZMod p) M]
    (χ : (Ω ≃ₐ[k] Ω) → M) (hchi1 : χ 1 = 0)
    {g n : Ω ≃ₐ[k] Ω} (hg : g ∈ SSGRoute.decomp k S.A) (hn : n ∈ S.I) :
    d1c (p:=p) (K:=K) M (chiExt (M:=M) S χ) g n = 0 := by
  have hnD : n ∈ SSGRoute.decomp k S.A := S.hI hn
  have hgnD : g * n ∈ SSGRoute.decomp k S.A := mul_mem hg hnD
  rw [d1c_apply, chiExt_of_mem S χ hnD, projG_eq_one_of_mem_I S hn, hchi1, smul_zero]
  rw [chiExt_of_mem S χ hgnD, projG_mul S hg hnD, projG_eq_one_of_mem_I S hn, mul_one,
    chiExt_of_mem S χ hg]
  abel

/-- `c - nform = d¹(β̃ + corrE c₀ + χ̃)`. -/
theorem c_sub_nform_eq_d1c {k Ω : Type} [Field k] [NumberField k] [Field Ω] [Algebra k Ω]
    [IsAlgClosure k Ω]
    (S : DCtx k Ω) (p : ℕ) [Fact p.Prime] (K : IntermediateField k Ω)
    [FiniteDimensional k K] [IsGalois k K] (M : Type) [AddCommGroup M] [Module (ZMod p) M]
    [DistribMulAction (K ≃ₐ[k] K) M] [SMulCommClass (K ≃ₐ[k] K) (ZMod p) M]
    (c : (Ω ≃ₐ[k] Ω) → (Ω ≃ₐ[k] Ω) → M) (β χ : (Ω ≃ₐ[k] Ω) → M) :
    c - nform (p:=p) (K:=K) S M c β χ
      = d1c (p:=p) (K:=K) M (betaG (M:=M) S β
          + corrE (M:=M) S (corrC (p:=p) (K:=K) S M c β) + chiExt (M:=M) S χ) := by
  funext g h
  rw [d1c_add, d1c_add]
  simp only [nform, corrC, Pi.sub_apply, Pi.add_apply]
  abel

theorem nform_props {k Ω : Type} [Field k] [NumberField k] [Field Ω] [Algebra k Ω]
    [IsAlgClosure k Ω]
    (S : Work.PTCore.DCtx k Ω) (p : ℕ) [Fact p.Prime] (K : IntermediateField k Ω)
    [FiniteDimensional k K] [IsGalois k K] (M : Type) [AddCommGroup M] [Module (ZMod p) M]
    [DistribMulAction (K ≃ₐ[k] K) M] [SMulCommClass (K ≃ₐ[k] K) (ZMod p) M]
    (c : (Ω ≃ₐ[k] Ω) → (Ω ≃ₐ[k] Ω) → M) (β χ : (Ω ≃ₐ[k] Ω) → M)
    (hcoc : SSGRoute.IsCocycle2On p k Ω K M (SSGRoute.decomp k S.A) c)
    (hlc : SSGRoute.IsLocConst2On p k Ω K M (SSGRoute.decomp k S.A) c)
    (hβ : SSGRoute.IsLocConstOn S.I β)
    (hβcob : ∀ n ∈ S.I, ∀ m ∈ S.I,
      c n m = SSGRoute.res k K n • β m - β (n * m) + β n)
    (hχ : SSGRoute.IsLocConstOn (Subgroup.topologicalClosure (Subgroup.zpowers S.σ)) χ)
    (hχcob : ∀ γ ∈ Subgroup.topologicalClosure (Subgroup.zpowers S.σ),
      ∀ δ ∈ Subgroup.topologicalClosure (Subgroup.zpowers S.σ),
      Work.PTCore.corrC (p := p) (K := K) S M c β γ δ
        = SSGRoute.res k K γ • χ δ - χ (γ * δ) + χ γ) :
    SSGRoute.IsCocycle2On p k Ω K M (SSGRoute.decomp k S.A)
        (Work.PTCore.nform (p := p) (K := K) S M c β χ) ∧
      SSGRoute.IsLocConst2On p k Ω K M (SSGRoute.decomp k S.A)
        (Work.PTCore.nform (p := p) (K := K) S M c β χ) ∧
      (∀ g ∈ SSGRoute.decomp k S.A, ∀ n ∈ S.I,
        Work.PTCore.nform (p := p) (K := K) S M c β χ g n = 0) ∧
      (∀ g ∈ SSGRoute.decomp k S.A, ∀ h ∈ SSGRoute.decomp k S.A, ∀ n ∈ S.I,
        Work.PTCore.nform (p := p) (K := K) S M c β χ g (h * n)
          = Work.PTCore.nform (p := p) (K := K) S M c β χ g h) ∧
      (∀ g ∈ SSGRoute.decomp k S.A, Work.PTCore.nform (p := p) (K := K) S M c β χ g 1 = 0) ∧
      (∀ γ ∈ Subgroup.topologicalClosure (Subgroup.zpowers S.σ),
        ∀ δ ∈ Subgroup.topologicalClosure (Subgroup.zpowers S.σ),
        Work.PTCore.nform (p := p) (K := K) S M c β χ γ δ = 0) ∧
      (SSGRoute.IsCoboundary2On (SSGRoute.res k K) (SSGRoute.decomp k S.A)
        (c - Work.PTCore.nform (p := p) (K := K) S M c β χ)) := by
  classical
  have hbGlc : SSGRoute.IsLocConstOn (SSGRoute.decomp k S.A) (betaG (M:=M) S β) :=
    betaG_isLocConstOn S β hβ
  have hbGcoc : SSGRoute.IsCocycle2On p k Ω K M (SSGRoute.decomp k S.A)
      (d1c (p:=p) (K:=K) M (betaG (M:=M) S β)) :=
    d1c_isCocycle2On (SSGRoute.decomp k S.A) (betaG (M:=M) S β)
  have hbGlc2 : SSGRoute.IsLocConst2On p k Ω K M (SSGRoute.decomp k S.A)
      (d1c (p:=p) (K:=K) M (betaG (M:=M) S β)) :=
    isLocConst2On_d1c (SSGRoute.decomp k S.A) (betaG (M:=M) S β) hbGlc
  have hc0coc : SSGRoute.IsCocycle2On p k Ω K M (SSGRoute.decomp k S.A)
      (corrC (p:=p) (K:=K) S M c β) :=
    isCocycle2On_sub _ _ _ hcoc hbGcoc
  have hc0lc : SSGRoute.IsLocConst2On p k Ω K M (SSGRoute.decomp k S.A)
      (corrC (p:=p) (K:=K) S M c β) :=
    isLocConst2On_sub _ _ _ hlc hbGlc2
  have hc0zero : ∀ n ∈ S.I, ∀ m ∈ S.I, corrC (p:=p) (K:=K) S M c β n m = 0 := by
    intro n hn m hm
    have hnm : n * m ∈ S.I := Subgroup.mul_mem _ hn hm
    simp only [corrC, Pi.sub_apply, d1c_apply, betaG_eq_of_mem_I S β hn,
      betaG_eq_of_mem_I S β hm, betaG_eq_of_mem_I S β hnm]
    rw [hβcob n hn m hm]
    abel
  have hchi1 : χ 1 = 0 := by
    have h11 := hχcob 1 (Subgroup.one_mem _) 1 (Subgroup.one_mem _)
    rw [hc0zero 1 S.I.one_mem 1 S.I.one_mem] at h11
    simpa using h11.symm
  have hElc : SSGRoute.IsLocConstOn (SSGRoute.decomp k S.A)
      (corrE (M:=M) S (corrC (p:=p) (K:=K) S M c β)) :=
    corrE_isLocConstOn S p K M (corrC (p:=p) (K:=K) S M c β) hc0lc
  have hXlc : SSGRoute.IsLocConstOn (SSGRoute.decomp k S.A) (chiExt (M:=M) S χ) :=
    chiExt_isLocConstOn S χ hχ
  have hEcoc : SSGRoute.IsCocycle2On p k Ω K M (SSGRoute.decomp k S.A)
      (d1c (p:=p) (K:=K) M (corrE (M:=M) S (corrC (p:=p) (K:=K) S M c β))) :=
    d1c_isCocycle2On _ _
  have hElc2 : SSGRoute.IsLocConst2On p k Ω K M (SSGRoute.decomp k S.A)
      (d1c (p:=p) (K:=K) M (corrE (M:=M) S (corrC (p:=p) (K:=K) S M c β))) :=
    isLocConst2On_d1c _ _ hElc
  have hXcoc : SSGRoute.IsCocycle2On p k Ω K M (SSGRoute.decomp k S.A)
      (d1c (p:=p) (K:=K) M (chiExt (M:=M) S χ)) :=
    d1c_isCocycle2On _ _
  have hXlc2 : SSGRoute.IsLocConst2On p k Ω K M (SSGRoute.decomp k S.A)
      (d1c (p:=p) (K:=K) M (chiExt (M:=M) S χ)) :=
    isLocConst2On_d1c _ _ hXlc
  have hnformcoc : SSGRoute.IsCocycle2On p k Ω K M (SSGRoute.decomp k S.A)
      (nform (p:=p) (K:=K) S M c β χ) :=
    isCocycle2On_sub _ _ _ (isCocycle2On_sub _ _ _ hc0coc hEcoc) hXcoc
  have hnformlc : SSGRoute.IsLocConst2On p k Ω K M (SSGRoute.decomp k S.A)
      (nform (p:=p) (K:=K) S M c β χ) :=
    isLocConst2On_sub _ _ _ (isLocConst2On_sub _ _ _ hc0lc hElc2) hXlc2
  have hzeroI : ∀ g ∈ SSGRoute.decomp k S.A, ∀ n ∈ S.I,
      nform (p:=p) (K:=K) S M c β χ g n = 0 := by
    intro g hg n hn
    have h1 : corrC (p:=p) (K:=K) S M c β g n
        - d1c (p:=p) (K:=K) M (corrE (M:=M) S (corrC (p:=p) (K:=K) S M c β)) g n = 0 :=
      corrE_sub_eq_zero_on_I S p K M (corrC (p:=p) (K:=K) S M c β) hc0coc hc0zero hg hn
    have h2 : d1c (p:=p) (K:=K) M (chiExt (M:=M) S χ) g n = 0 :=
      d1c_chiExt_eq_zero_on_I S p K M χ hchi1 hg hn
    rw [nform]
    simp only [Pi.sub_apply]
    rw [h1, h2]
    simp
  have hCvan : ∀ γ ∈ Subgroup.topologicalClosure (Subgroup.zpowers S.σ),
      ∀ δ ∈ Subgroup.topologicalClosure (Subgroup.zpowers S.σ),
      nform (p:=p) (K:=K) S M c β χ γ δ = 0 := by
    intro γ hγ δ hδ
    have hγD : γ ∈ SSGRoute.decomp k S.A := Work.SSGRoute.HS.CC_le_DD S.A S.σ S.hσ hγ
    have hδD : δ ∈ SSGRoute.decomp k S.A := Work.SSGRoute.HS.CC_le_DD S.A S.σ S.hσ hδ
    have hγδD : γ * δ ∈ SSGRoute.decomp k S.A := mul_mem hγD hδD
    have hcorr1 : corrC (p:=p) (K:=K) S M c β γ 1 = SSGRoute.res k K γ • χ 1 := by
      have h := hχcob γ hγ 1 (Subgroup.one_mem _)
      simpa using h
    have hdX : d1c (p:=p) (K:=K) M (chiExt (M:=M) S χ) γ δ
        = corrC (p:=p) (K:=K) S M c β γ δ := by
      rw [d1c_apply, chiExt_of_mem S χ hδD, chiExt_of_mem S χ hγδD, chiExt_of_mem S χ hγD,
        projG_mul S hγD hδD, projG_eq_self_of_mem_C S hγ, projG_eq_self_of_mem_C S hδ]
      exact (hχcob γ hγ δ hδ).symm
    have hdE : d1c (p:=p) (K:=K) M (corrE (M:=M) S (corrC (p:=p) (K:=K) S M c β)) γ δ
        = - corrC (p:=p) (K:=K) S M c β γ 1 :=
      d1c_corrE_eq_neg_on_C S p K M (corrC (p:=p) (K:=K) S M c β) hc0coc hγ hδ
    have hfin : corrC (p:=p) (K:=K) S M c β γ δ
        - d1c (p:=p) (K:=K) M (corrE (M:=M) S (corrC (p:=p) (K:=K) S M c β)) γ δ
        - d1c (p:=p) (K:=K) M (chiExt (M:=M) S χ) γ δ = 0 := by
      rw [hdE, hdX, hcorr1, hchi1]
      simp
    rw [nform]
    simp only [Pi.sub_apply]
    exact hfin
  refine ⟨hnformcoc, hnformlc, hzeroI, ?_, ?_, hCvan, ?_⟩
  · intro g hg h hh n hn
    have hnD : n ∈ SSGRoute.decomp k S.A := S.hI hn
    have hc := hnformcoc g hg h hh n hnD
    have h1 : nform (p:=p) (K:=K) S M c β χ h n = 0 := hzeroI h hh n hn
    have h2 : nform (p:=p) (K:=K) S M c β χ (g * h) n = 0 :=
      hzeroI (g * h) (mul_mem hg hh) n hn
    simp only [h1, h2, smul_zero, zero_sub, neg_zero, zero_add] at hc
    exact sub_eq_zero.mp hc
  · intro g hg
    exact hzeroI g hg 1 S.I.one_mem
  · refine ⟨betaG (M:=M) S β + corrE (M:=M) S (corrC (p:=p) (K:=K) S M c β)
        + chiExt (M:=M) S χ, ?_, ?_⟩
    · exact isLocConstOn_add (SSGRoute.decomp k S.A)
        (betaG (M:=M) S β + corrE (M:=M) S (corrC (p:=p) (K:=K) S M c β))
        (chiExt (M:=M) S χ)
        (isLocConstOn_add (SSGRoute.decomp k S.A) (betaG (M:=M) S β)
          (corrE (M:=M) S (corrC (p:=p) (K:=K) S M c β)) hbGlc hElc) hXlc
    · intro g hg h hh
      have hkey : (c - nform (p:=p) (K:=K) S M c β χ) g h
          = d1c (p:=p) (K:=K) M (betaG (M:=M) S β
              + corrE (M:=M) S (corrC (p:=p) (K:=K) S M c β) + chiExt (M:=M) S χ) g h := by
        rw [c_sub_nform_eq_d1c]
      rw [hkey, d1c_apply]

end Work.PTCore
