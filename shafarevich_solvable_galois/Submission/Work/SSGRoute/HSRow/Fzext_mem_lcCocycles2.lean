import Mathlib
import Submission.Work.SSGRoute.HSRow.NormalFormDefs
import Submission.Work.SSGRoute.HSRow.CokerFz
import Submission.Work.SSGRoute.HSRow.CokerZr2
import Submission.Work.SSGRoute.HSRow.Coords
import Submission.Work.SSGRoute.HSRow.FzCalc
import Submission.Work.SSGRoute.HSRow.exists_openSubgroup_kill_values
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Fz Φ` is a locally constant `2`-cocycle on the decomposition group

Setting: `D = decomp k A = I ⋊ C`, `C = closure (zpowers σ)`, `M` an `𝔽_p`-module with a
`Gal(K/k)`-action, `Zr = Z¹_loc(I,M)` the module of locally constant `1`-cocycles on `I`, with the
conjugation action `twR` of `C`.

For a crossed homomorphism `Φ : C → Zr` (for `twR`) with `Φ 1 = 0` which is locally constant, the
normal form

  `F(g,h) = ρ(p g) • Φ(p h)((p g)⁻¹ q g (p g))`

is a locally constant `2`-cocycle on `D` (the representative of the inverse transgression).

Here we prove the **local constancy** half: the `2`-cocycle identity is
`Work.SSGRoute.HSRow.Fzext_isCocycle2On`.

Local constancy.  Let `W ≤ C` be an open subgroup with `Φ (γ * u) = Φ γ` for `u ∈ W`.  Choose an
open normal `Q ≤ Gal(Ω/k)` killing every value of `Φ` (`exists_openSubgroup_kill_values`), let
`W₁ = normalCore W` and let `U ≤ Gal(Ω/k)` be an open subgroup so small that
`U ∩ D ⊆ {u : q u ∈ Q, p u ∈ W₁}` (the trace of an open subgroup of `D`, obtained from the Krull
topology).  Then for `u, v ∈ U ∩ D`:

* `Φ (p (h v)) = Φ (p h)` because `p v ∈ W₁ ⊆ W` and `Φ` is right-`W`-invariant;
* `Wg (g u) = (p u)⁻¹ Wg g (p u) · Wg u`, and `Φ (p h)` vanishes at `Wg u` because
  `Wg u = (p u)⁻¹ (q u) (p u) ∈ Q` (normality of `Q`);
* finally `res (p u) • Φ (p h) (conjI (p u) (Wg g)) = Φ (p h) (Wg g)` because
  `twR (p u) (Φ (p h)) = Φ (p u * p h) - Φ (p u) = Φ (p h)`, using `Φ (p h * w) = Φ (p h)` for the
  conjugate `w = (p h)⁻¹ (p u) (p h) ∈ W₁`.

This is the local-constancy input of `Work.SSGRoute.HSRow.coker_injects_H2loc` /
`transgression_injective`.
-/

open scoped Pointwise Topology
open Classical

namespace Work.SSGRoute.HSRow

noncomputable section

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option maxHeartbeats 1000000

variable (p : ℕ) [Fact p.Prime] (k Ω : Type) [Field k] [NumberField k] [Field Ω] [Algebra k Ω]
  [IsAlgClosure k Ω] (K : IntermediateField k Ω) [FiniteDimensional k K] [IsGalois k K]

/-- **Local constancy of the normal form `Fzext Φ` on the decomposition group.**

For `u, v` in a sufficiently small open subgroup of `D = decomp k H.A`, the value
`Fzext Φ (g * u) (h * v)` does not depend on `u, v`. -/
theorem Fzext_isLocConst2On
    (M : Type) [AddCommGroup M] [Module (ZMod p) M] [DistribMulAction (K ≃ₐ[k] K) M]
    [SMulCommClass (K ≃ₐ[k] K) (ZMod p) M]
    (I : Subgroup (Ω ≃ₐ[k] Ω)) (σ : Ω ≃ₐ[k] Ω)
    (hIclosed : IsClosed (I : Set (Ω ≃ₐ[k] Ω))) (H : Hcx k Ω I σ)
    (Φ : ↥(Ccl k Ω σ) → ↥(Zr p k Ω K M I))
    (hΦ1 : Φ 1 = 0)
    (hΦc : ∀ γ δ : ↥(Ccl k Ω σ), Φ (γ * δ) = Φ γ + twR p k Ω K M I σ H γ (Φ δ))
    (hΦlc : ∃ W : Subgroup ↥(Ccl k Ω σ), IsOpen (W : Set ↥(Ccl k Ω σ)) ∧
      ∀ γ : ↥(Ccl k Ω σ), ∀ u ∈ W, Φ (γ * u) = Φ γ) :
    SSGRoute.IsLocConst2On p k Ω K M (SSGRoute.decomp k H.A) (Fzext p k Ω K M I σ H Φ) := by
  classical
  obtain ⟨W0, hW0o, hW0⟩ := hΦlc
  -- `Φ` vanishes on the open subgroup `W0`
  have hΦW0 : ∀ w ∈ W0, Φ w = 0 := by
    intro w hw
    rw [← one_mul w, hW0 1 w hw, hΦ1]
  -- the open normal subgroup `W1 ≤ C` on which `Φ` is right-invariant
  let W1 : Subgroup ↥(Ccl k Ω σ) := Subgroup.normalCore W0
  have hW1le : W1 ≤ W0 := Subgroup.normalCore_le W0
  have hW1norm : W1.Normal := Subgroup.normalCore_normal W0
  haveI : CompactSpace ↥(Ccl k Ω σ) :=
    isCompact_iff_compactSpace.mp (Subgroup.isClosed_topologicalClosure _).isCompact
  haveI : W0.FiniteIndex := by
    rw [Subgroup.finiteIndex_iff_finite_quotient]
    exact Subgroup.quotient_finite_of_isOpen W0 hW0o
  have hW1o : IsOpen (W1 : Set ↥(Ccl k Ω σ)) := by
    have hc : IsClosed ((W1 : Subgroup ↥(Ccl k Ω σ)) : Set ↥(Ccl k Ω σ)) :=
      Subgroup.normalCore_isClosed W0 (Subgroup.isClosed_of_isOpen W0 hW0o)
    exact Subgroup.isOpen_of_isClosed_of_finiteIndex W1 hc
  -- an open normal subgroup `Q` of `Gal(Ω/k)` killing every value of `Φ`
  obtain ⟨Q, hQo, hQnorm, hQkill⟩ :=
    exists_openSubgroup_kill_values p k Ω K M I σ Φ ⟨W0, hW0o, hW0⟩
  -- the two coordinates are continuous
  have hqcont : Continuous (fun u : ↥(SSGRoute.decomp k H.A) => Qq k Ω I σ H u) :=
    continuous_subtype_val.comp
      (continuous_ip k Ω H.A I σ H.hI H.hnorm H.hσ H.hsup H.hinf hIclosed)
  have hpcont : Continuous (fun u : ↥(SSGRoute.decomp k H.A) => Pp k Ω I σ H u) :=
    continuous_subtype_val.comp
      (continuous_proj k Ω H.A I σ H.hI H.hnorm H.hσ H.hsup H.hinf hIclosed)
  -- the open subset of `D` where the two conditions hold
  have hqo : IsOpen {u : ↥(SSGRoute.decomp k H.A) | Qq k Ω I σ H u ∈ Q} :=
    hQo.preimage hqcont
  have hpo : IsOpen {u : ↥(SSGRoute.decomp k H.A) | Ppc p k Ω K M I σ H u ∈ W1} := by
    obtain ⟨Vp, hVpo, hVp⟩ := isOpen_induced_iff.mp hW1o
    have hset : {u : ↥(SSGRoute.decomp k H.A) | Ppc p k Ω K M I σ H u ∈ W1}
        = (fun u : ↥(SSGRoute.decomp k H.A) => Pp k Ω I σ H u) ⁻¹' Vp := by
      ext u
      show Ppc p k Ω K M I σ H u ∈ (W1 : Set ↥(Ccl k Ω σ)) ↔ Pp k Ω I σ H u ∈ Vp
      rw [← hVp]
      rfl
    rw [hset]
    exact hVpo.preimage hpcont
  -- a neighbourhood of `1` in `D`, which is the trace of an open set of `Gal(Ω/k)`
  have hmem1q : (1 : ↥(SSGRoute.decomp k H.A)) ∈ {u | Qq k Ω I σ H u ∈ Q} := by
    show Qq k Ω I σ H 1 ∈ Q
    rw [Qq_one]
    exact Q.one_mem
  have hmem1p : (1 : ↥(SSGRoute.decomp k H.A)) ∈ {u | Ppc p k Ω K M I σ H u ∈ W1} := by
    show Ppc p k Ω K M I σ H 1 ∈ W1
    rw [Ppc_one]
    exact W1.one_mem
  obtain ⟨V, hVo, hV⟩ := isOpen_induced_iff.mp (hqo.inter hpo)
  have hV1 : (1 : Ω ≃ₐ[k] Ω) ∈ V := by
    have h1 : (1 : ↥(SSGRoute.decomp k H.A)) ∈ (Subtype.val ⁻¹' V : Set ↥(SSGRoute.decomp k H.A)) := by
      rw [hV]; exact ⟨hmem1q, hmem1p⟩
    simpa using h1
  obtain ⟨E, hEfin, hEsub⟩ := (krullTopology_mem_nhds_one_iff k Ω V).mp (hVo.mem_nhds hV1)
  haveI : FiniteDimensional k E := hEfin
  refine ⟨E.fixingSubgroup, E.fixingSubgroup_isOpen, ?_⟩
  intro g hg h hh u hu v hv huD hvD
  -- the two conditions for `u` and `v`
  have huV : u ∈ V := hEsub hu
  have hvV : v ∈ V := hEsub hv
  have humem : Qq k Ω I σ H ⟨u, huD⟩ ∈ Q ∧ Ppc p k Ω K M I σ H ⟨u, huD⟩ ∈ W1 := by
    have h : (⟨u, huD⟩ : ↥(SSGRoute.decomp k H.A)) ∈ (Subtype.val ⁻¹' V :
        Set ↥(SSGRoute.decomp k H.A)) := huV
    rw [hV] at h
    exact h
  have hvmem : Qq k Ω I σ H ⟨v, hvD⟩ ∈ Q ∧ Ppc p k Ω K M I σ H ⟨v, hvD⟩ ∈ W1 := by
    have h : (⟨v, hvD⟩ : ↥(SSGRoute.decomp k H.A)) ∈ (Subtype.val ⁻¹' V :
        Set ↥(SSGRoute.decomp k H.A)) := hvV
    rw [hV] at h
    exact h
  have hpu : Ppc p k Ω K M I σ H ⟨u, huD⟩ ∈ W1 := humem.2
  have hpv : Ppc p k Ω K M I σ H ⟨v, hvD⟩ ∈ W1 := hvmem.2
  have hqu : Qq k Ω I σ H ⟨u, huD⟩ ∈ Q := humem.1
  -- reduce `Fzext` to `Fz` on the decomposition group
  rw [Fzext_apply_of_mem p k Ω K M I σ H Φ ⟨g * u, mul_mem hg huD⟩ ⟨h * v, mul_mem hh hvD⟩,
    Fzext_apply_of_mem p k Ω K M I σ H Φ ⟨g, hg⟩ ⟨h, hh⟩]
  have hgu : (⟨g * u, mul_mem hg huD⟩ : ↥(SSGRoute.decomp k H.A))
      = ⟨g, hg⟩ * ⟨u, huD⟩ := Subtype.ext rfl
  have hhv : (⟨h * v, mul_mem hh hvD⟩ : ↥(SSGRoute.decomp k H.A))
      = ⟨h, hh⟩ * ⟨v, hvD⟩ := Subtype.ext rfl
  rw [hgu, hhv]
  -- the value of `Φ` only depends on `p h`
  have hΦhv : Φ (Ppc p k Ω K M I σ H (⟨h, hh⟩ * ⟨v, hvD⟩))
      = Φ (Ppc p k Ω K M I σ H ⟨h, hh⟩) := by
    rw [Ppc_mul p k Ω K M I σ H ⟨h, hh⟩ ⟨v, hvD⟩]
    exact hW0 (Ppc p k Ω K M I σ H ⟨h, hh⟩) (Ppc p k Ω K M I σ H ⟨v, hvD⟩) (hW1le hpv)
  -- `Wg u` lies in `Q`, so every value of `Φ` vanishes there
  have hWu : ((WgI p k Ω K M I σ H ⟨u, huD⟩ : ↥I) : Ω ≃ₐ[k] Ω) ∈ Q := by
    have hconj := hQnorm.conj_mem (Qq k Ω I σ H ⟨u, huD⟩) hqu ((Pp k Ω I σ H ⟨u, huD⟩)⁻¹)
    rw [inv_inv] at hconj
    rw [WgI_coe, ← Qq_mul_Pp k Ω I σ H ⟨u, huD⟩]
    simpa [mul_assoc] using hconj
  have hZerou : (Φ (Ppc p k Ω K M I σ H ⟨h, hh⟩) : ↥I → M) (WgI p k Ω K M I σ H ⟨u, huD⟩) = 0 :=
    hQkill (WgI p k Ω K M I σ H ⟨u, huD⟩) hWu (Φ (Ppc p k Ω K M I σ H ⟨h, hh⟩))
      ⟨Ppc p k Ω K M I σ H ⟨h, hh⟩, rfl⟩
  -- `twR (p u)` fixes `Φ (p h)`
  have htwinv : twR p k Ω K M I σ H (Ppc p k Ω K M I σ H ⟨u, huD⟩)
      (Φ (Ppc p k Ω K M I σ H ⟨h, hh⟩)) = Φ (Ppc p k Ω K M I σ H ⟨h, hh⟩) := by
    have hkey : Φ (Ppc p k Ω K M I σ H ⟨u, huD⟩ * Ppc p k Ω K M I σ H ⟨h, hh⟩)
        = Φ (Ppc p k Ω K M I σ H ⟨h, hh⟩) := by
      have hmem : (Ppc p k Ω K M I σ H ⟨h, hh⟩)⁻¹ * Ppc p k Ω K M I σ H ⟨u, huD⟩
          * Ppc p k Ω K M I σ H ⟨h, hh⟩ ∈ W0 :=
        hW1le (by
          simpa using hW1norm.conj_mem (Ppc p k Ω K M I σ H ⟨u, huD⟩) hpu
            (Ppc p k Ω K M I σ H ⟨h, hh⟩)⁻¹)
      have heq : Ppc p k Ω K M I σ H ⟨u, huD⟩ * Ppc p k Ω K M I σ H ⟨h, hh⟩
          = Ppc p k Ω K M I σ H ⟨h, hh⟩
            * ((Ppc p k Ω K M I σ H ⟨h, hh⟩)⁻¹ * Ppc p k Ω K M I σ H ⟨u, huD⟩
                * Ppc p k Ω K M I σ H ⟨h, hh⟩) := by
        group
      rw [heq]
      exact hW0 (Ppc p k Ω K M I σ H ⟨h, hh⟩) _ hmem
    have h1 : twR p k Ω K M I σ H (Ppc p k Ω K M I σ H ⟨u, huD⟩)
          (Φ (Ppc p k Ω K M I σ H ⟨h, hh⟩))
        = Φ (Ppc p k Ω K M I σ H ⟨u, huD⟩ * Ppc p k Ω K M I σ H ⟨h, hh⟩)
          - Φ (Ppc p k Ω K M I σ H ⟨u, huD⟩) := by
      rw [hΦc (Ppc p k Ω K M I σ H ⟨u, huD⟩) (Ppc p k Ω K M I σ H ⟨h, hh⟩)]
      abel
    rw [h1, hkey, hΦW0 (Ppc p k Ω K M I σ H ⟨u, huD⟩) (hW1le hpu), sub_zero]
  -- the computation, with every term written in the abbreviations `Pp`, `Ppc`, `WgI`
  show SSGRoute.res k K (Pp k Ω I σ H (⟨g, hg⟩ * ⟨u, huD⟩))
        • ((Φ (Ppc p k Ω K M I σ H (⟨h, hh⟩ * ⟨v, hvD⟩)) : ↥I → M)
            (WgI p k Ω K M I σ H (⟨g, hg⟩ * ⟨u, huD⟩)))
      = SSGRoute.res k K (Pp k Ω I σ H ⟨g, hg⟩)
        • ((Φ (Ppc p k Ω K M I σ H ⟨h, hh⟩) : ↥I → M) (WgI p k Ω K M I σ H ⟨g, hg⟩))
  rw [Pp_mul k Ω I σ H ⟨g, hg⟩ ⟨u, huD⟩, hΦhv,
    WgI_mul p k Ω K M I σ H ⟨g, hg⟩ ⟨u, huD⟩, Zr_cocycle]
  have key : SSGRoute.res k K (Pp k Ω I σ H ⟨u, huD⟩)
        • ((Φ (Ppc p k Ω K M I σ H ⟨h, hh⟩) : ↥I → M)
            (conjI p k Ω K M I σ H (Ppc p k Ω K M I σ H ⟨u, huD⟩)
              (WgI p k Ω K M I σ H ⟨g, hg⟩)))
      = ((Φ (Ppc p k Ω K M I σ H ⟨h, hh⟩) : ↥I → M) (WgI p k Ω K M I σ H ⟨g, hg⟩)) := by
    have h := twR_apply p k Ω K M I σ H (Ppc p k Ω K M I σ H ⟨u, huD⟩)
      (Φ (Ppc p k Ω K M I σ H ⟨h, hh⟩)) (WgI p k Ω K M I σ H ⟨g, hg⟩)
    exact h.symm.trans
      (congrFun (congrArg Subtype.val htwinv) (WgI p k Ω K M I σ H ⟨g, hg⟩))
  rw [hZerou, smul_zero, add_zero, map_mul, mul_smul, key]

/-- **The `2`-cocycle identity for the normal form `Fz Φ`, at the level of the decomposition
group.**  This is the telescoping computation: with `g = q g * p g`, `Wg g = (p g)⁻¹ g`,
`Wg (g h) = (p h)⁻¹ Wg g (p h) · Wg h` and `p (g h) = p g * p h`, the four terms cancel. -/
theorem Fz_cocycle_triple
    (M : Type) [AddCommGroup M] [Module (ZMod p) M] [DistribMulAction (K ≃ₐ[k] K) M]
    [SMulCommClass (K ≃ₐ[k] K) (ZMod p) M]
    (I : Subgroup (Ω ≃ₐ[k] Ω)) (σ : Ω ≃ₐ[k] Ω) (H : Hcx k Ω I σ)
    (Φ : ↥(Ccl k Ω σ) → ↥(Zr p k Ω K M I))
    (hΦ1 : Φ 1 = 0)
    (hΦc : ∀ γ δ : ↥(Ccl k Ω σ), Φ (γ * δ) = Φ γ + twR p k Ω K M I σ H γ (Φ δ))
    (g h l : ↥(SSGRoute.decomp k H.A)) :
    SSGRoute.res k K (g : Ω ≃ₐ[k] Ω) • Fz p k Ω K M I σ H Φ h l
      - Fz p k Ω K M I σ H Φ (g * h) l
      + Fz p k Ω K M I σ H Φ g (h * l)
      - Fz p k Ω K M I σ H Φ g h = 0 := by
  show SSGRoute.res k K (g : Ω ≃ₐ[k] Ω)
        • (SSGRoute.res k K (Pp k Ω I σ H h)
            • ((Φ (Ppc p k Ω K M I σ H l) : ↥I → M) (WgI p k Ω K M I σ H h)))
      - (SSGRoute.res k K (Pp k Ω I σ H (g * h))
            • ((Φ (Ppc p k Ω K M I σ H l) : ↥I → M) (WgI p k Ω K M I σ H (g * h))))
      + (SSGRoute.res k K (Pp k Ω I σ H g)
            • ((Φ (Ppc p k Ω K M I σ H (h * l)) : ↥I → M) (WgI p k Ω K M I σ H g)))
      - (SSGRoute.res k K (Pp k Ω I σ H g)
            • ((Φ (Ppc p k Ω K M I σ H h) : ↥I → M) (WgI p k Ω K M I σ H g))) = 0
  simp only [Pp_mul, WgI_mul, Ppc_mul, hΦc, Submodule.coe_add, Pi.add_apply, twR_apply,
    Zr_cocycle]
  -- the three scalar identities
  have hBC : (Pp k Ω I σ H g * Pp k Ω I σ H h)
      * ((conjI p k Ω K M I σ H (Ppc p k Ω K M I σ H h) (WgI p k Ω K M I σ H g) : ↥I) :
          Ω ≃ₐ[k] Ω)
      = Qq k Ω I σ H g * Pp k Ω I σ H (g * h) := by
    have h1 : ((conjI p k Ω K M I σ H (Ppc p k Ω K M I σ H h) (WgI p k Ω K M I σ H g) : ↥I) :
          Ω ≃ₐ[k] Ω)
        = (Pp k Ω I σ H h)⁻¹ * ((WgI p k Ω K M I σ H g : ↥I) : Ω ≃ₐ[k] Ω) * Pp k Ω I σ H h := by
      rw [conjI_coe]
      rfl
    rw [h1, ← Pp_mul k Ω I σ H g h, Pp_mul_WgI p k Ω K M I σ H g h, g_mul_Pp k Ω I σ H g h]
  have hA : SSGRoute.res k K (g : Ω ≃ₐ[k] Ω)
        • (SSGRoute.res k K (Pp k Ω I σ H h)
            • ((Φ (Ppc p k Ω K M I σ H l) : ↥I → M) (WgI p k Ω K M I σ H h)))
      = SSGRoute.res k K (Qq k Ω I σ H g * Pp k Ω I σ H (g * h))
        • ((Φ (Ppc p k Ω K M I σ H l) : ↥I → M) (WgI p k Ω K M I σ H h)) := by
    rw [← mul_smul, ← map_mul, g_mul_Pp k Ω I σ H g h]
  have hB : SSGRoute.res k K (Pp k Ω I σ H g * Pp k Ω I σ H h)
        • (SSGRoute.res k K
            ((conjI p k Ω K M I σ H (Ppc p k Ω K M I σ H h) (WgI p k Ω K M I σ H g) : ↥I) :
              Ω ≃ₐ[k] Ω)
            • ((Φ (Ppc p k Ω K M I σ H l) : ↥I → M) (WgI p k Ω K M I σ H h)))
      = SSGRoute.res k K (Qq k Ω I σ H g * Pp k Ω I σ H (g * h))
        • ((Φ (Ppc p k Ω K M I σ H l) : ↥I → M) (WgI p k Ω K M I σ H h)) := by
    rw [← mul_smul, ← map_mul, hBC]
  have hC : SSGRoute.res k K (Pp k Ω I σ H g)
        • (SSGRoute.res k K ((Ppc p k Ω K M I σ H h : ↥(Ccl k Ω σ)) : Ω ≃ₐ[k] Ω)
            • ((Φ (Ppc p k Ω K M I σ H l) : ↥I → M)
                (conjI p k Ω K M I σ H (Ppc p k Ω K M I σ H h) (WgI p k Ω K M I σ H g))))
      = SSGRoute.res k K (Pp k Ω I σ H g * Pp k Ω I σ H h)
        • ((Φ (Ppc p k Ω K M I σ H l) : ↥I → M)
            (conjI p k Ω K M I σ H (Ppc p k Ω K M I σ H h) (WgI p k Ω K M I σ H g))) := by
    rw [← mul_smul, ← map_mul]
    rfl
  rw [smul_add, smul_add, hA, hB, hC]
  abel

end

/-- **`Fzext Φ` is a locally constant `2`-cocycle on the decomposition group `D = decomp k H.A`.**

`Fzext Φ` is the normal form `F(g,h) = ρ(p g) • Φ(p h)((p g)⁻¹ q g (p g))` of a crossed
homomorphism `Φ : C → Zr` (for the conjugation action `twR`) which is locally constant and
satisfies `Φ 1 = 0`. -/
theorem Fzext_mem_lcCocycles2
    (p : ℕ) [Fact p.Prime] (k Ω : Type) [Field k] [NumberField k] [Field Ω] [Algebra k Ω]
    [IsAlgClosure k Ω] (K : IntermediateField k Ω) [FiniteDimensional k K] [IsGalois k K]
    (M : Type) [AddCommGroup M] [Module (ZMod p) M] [DistribMulAction (K ≃ₐ[k] K) M]
    [SMulCommClass (K ≃ₐ[k] K) (ZMod p) M]
    (I : Subgroup (Ω ≃ₐ[k] Ω)) (σ : Ω ≃ₐ[k] Ω)
    (hIclosed : IsClosed (I : Set (Ω ≃ₐ[k] Ω))) (H : Work.SSGRoute.HSRow.Hcx k Ω I σ)
    (Φ : ↥(Work.SSGRoute.HSRow.Ccl k Ω σ) → ↥(Work.SSGRoute.HSRow.Zr p k Ω K M I))
    (hΦ1 : Φ 1 = 0)
    (hΦc : ∀ γ δ : ↥(Work.SSGRoute.HSRow.Ccl k Ω σ),
      Φ (γ * δ) = Φ γ + Work.SSGRoute.HSRow.twR p k Ω K M I σ H γ (Φ δ))
    (hΦlc : ∃ W : Subgroup ↥(Work.SSGRoute.HSRow.Ccl k Ω σ),
      IsOpen (W : Set ↥(Work.SSGRoute.HSRow.Ccl k Ω σ)) ∧
      ∀ γ : ↥(Work.SSGRoute.HSRow.Ccl k Ω σ), ∀ u ∈ W, Φ (γ * u) = Φ γ)
    : Work.SSGRoute.HSRow.Fzext p k Ω K M I σ H Φ
        ∈ Work.SSGRoute.lcCocycles2 p k Ω K M (SSGRoute.decomp k H.A) := by
  refine ⟨?_, Fzext_isLocConst2On p k Ω K M I σ hIclosed H Φ hΦ1 hΦc hΦlc⟩
  -- the `2`-cocycle identity, reduced to the group-theoretic telescoping `Fz_cocycle_triple`
  intro g hg h hh l hl
  rw [Fzext_apply_of_mem p k Ω K M I σ H Φ ⟨h, hh⟩ ⟨l, hl⟩,
    Fzext_apply_of_mem p k Ω K M I σ H Φ ⟨g * h, mul_mem hg hh⟩ ⟨l, hl⟩,
    Fzext_apply_of_mem p k Ω K M I σ H Φ ⟨g, hg⟩ ⟨h * l, mul_mem hh hl⟩,
    Fzext_apply_of_mem p k Ω K M I σ H Φ ⟨g, hg⟩ ⟨h, hh⟩]
  exact Fz_cocycle_triple p k Ω K M I σ H Φ hΦ1 hΦc ⟨g, hg⟩ ⟨h, hh⟩ ⟨l, hl⟩

end Work.SSGRoute.HSRow
