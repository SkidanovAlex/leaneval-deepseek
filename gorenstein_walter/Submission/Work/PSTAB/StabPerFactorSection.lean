/-
Copyright (c) 2026 gorenstein_walter team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: PSTAB area (fundmath3-gorenstein_walter)
-/
import Mathlib
import Submission.Work.PSTAB.Defs
import Submission.Work.PSTAB.Deps
import Submission.Work.PSTAB.BadSectionQuotient
import Submission.Work.PSTAB.MinimalNormalElemAb
import Submission.Work.PSTAB.ConjNormalQuadratic
import Submission.Work.PSTAB.QuadraticLinear

set_option autoImplicit false

open scoped commutatorElement IsMulCommutative
open Additive

/-!
# AREA PSTAB — per-chief-factor `p`-stability, section-strength variant

`Work.PSTAB.StabPerFactorSection`: the same statement as `Work.PSTAB.StabPerFactor`, but proved
from the *section-strength* quadratic-pair lemma `Work.PSTAB.QuadPairIrrSectionProp` (design pass
11 §4 fallback) together with `Work.PSTAB.BadSectionOfQuotientProp`, instead of from the
subgroup-strength `Work.PSTAB.QuadPairIrrProp`.

`Work.PSTAB.StabPerFactor`: if `K ⊴ M` is a `p`-group (`p` odd), `A ≤ M` is a `p`-subgroup with
`[K, A, A] = 1`, and the ambient group `M` has no section that is a noncyclic `2`-group with a
unique involution, then `A` centralizes every chief factor of `M` inside `K`, i.e.
`[Vᵢ, A] ≤ Vᵢ₊₁` for the chief series `Vᵢ = chiefSeriesInside K i`.

The proof is the standard `p`-stability argument, run through the two hypotheses of this area
instead of through solvability and odd order:

* `Vᵢ/Vᵢ₊₁` is an elementary abelian `p`-group (a minimal normal subgroup that is a `p`-group),
  hence an `𝔽_p`-vector space, and `M` acts on it by conjugation, with kernel the chief-factor
  centralizer `C = C_M(Vᵢ/Vᵢ₊₁)`;
* the resulting representation `ρ : M ⧸ C → GL(Vᵢ/Vᵢ₊₁)` is faithful and irreducible;
* an element `a ∈ A` acts quadratically on every chief factor (`[Vᵢ, a, a] ≤ [K, a, a] = 1`);
* so if some `a ∈ A` did not act trivially, `Work.PSTAB.QuadPairIrrProp` would produce a noncyclic
  `2`-subgroup of `M ⧸ C` with a unique involution, i.e. a bad section of `M`, contradicting
  `Work.PSTAB.NoBadSection M`.
-/

namespace Work.PSTAB

open OddOrder.GroupTheory

/-- **Per-chief-factor `p`-stability** (Glauberman L6.3 / Gorenstein 6.5.3 steps 1–3, in the
`p`-group-without-p-stability form used by the PSTAB area).

`K ⊴ M` a `p`-group, `A ≤ M` a `p`-subgroup with `[K, A, A] = 1`, `M` without bad sections:
then `A` centralizes every chief factor of `M` inside `K`. -/
theorem StabPerFactorSection {M : Type} [Group M] [Finite M] {p : ℕ} [Fact p.Prime]
    (hp2 : p ≠ 2)
    (hQS : Work.PSTAB.QuadPairIrrSectionProp.{0, 0})
    (hBQ : Work.PSTAB.BadSectionOfQuotientProp.{0})
    (hM : Work.PSTAB.NoBadSection M)
    {K : Subgroup M} [K.Normal] (hK : IsPGroup p K)
    {A : Subgroup M} (hA : IsPGroup p A)
    (hKAA : ⁅⁅K, A⁆, A⁆ = (⊥ : Subgroup M)) (i : ℕ) :
    ⁅OddOrder.GroupTheory.chiefSeriesInside K i, A⁆ ≤
      OddOrder.GroupTheory.chiefSeriesInside K (i + 1) := by
  classical
  set U : Subgroup M := OddOrder.GroupTheory.chiefSeriesInside K i with hUdef
  set V : Subgroup M := OddOrder.GroupTheory.chiefSeriesInside K (i + 1) with hVdef
  -- It suffices that `A ≤ C_M(U/V)`.
  suffices hAC : A ≤ chiefFactorCentralizer U V from
    chiefFactorCentralizer.commutator_le_of_le hAC
  by_contra hAle
  obtain ⟨a, ha, haC⟩ : ∃ a ∈ A, a ∉ chiefFactorCentralizer U V := by
    by_contra h
    push_neg at h
    exact hAle fun x hx => h x hx
  have hUK : U ≤ K := by rw [hUdef]; exact chiefSeriesInside_le K i
  -- `U ≠ ⊥`, since otherwise every subgroup centralizes `U/V`.
  have hU0 : U ≠ ⊥ := by
    rintro hbot
    refine haC ((chiefFactorCentralizer.le_of_commutator_le (H := A) ?_ ha))
    rw [hbot, Subgroup.commutator_bot_left]
    exact bot_le
  -- So `U/V` is a chief factor.
  have hchief : IsChiefFactor U V := by
    rw [hUdef, hVdef]
    exact isChiefFactor_chiefSeriesInside (K := K) (n := i) (by rw [← hUdef]; exact hU0)
  have hUn : U.Normal := hchief.normal_top
  have hVn : V.Normal := hchief.normal_bot
  haveI : U.Normal := hUn
  haveI : V.Normal := hVn
  -- `W := U/V`, viewed as a (minimal) normal subgroup of `M ⧸ V`.
  set W : Subgroup (M ⧸ V) := U.map (QuotientGroup.mk' V) with hWdef
  have hWn : W.Normal := hUn.map _ (QuotientGroup.mk'_surjective V)
  have hMin : OddOrder.Isaacs.Ch02.IsMinimalNormal W := hchief.isMinimalNormal_map_quotient
  -- `W` is a `p`-group, hence (being minimal normal) elementary abelian of exponent `p`.
  have hUp : IsPGroup p ↥U := hK.to_le hUK
  have hWp : IsPGroup p ↥W := by
    rw [hWdef]
    exact hUp.map (QuotientGroup.mk' V)
  have hElemT : OddOrder.GroupTheory.IsElementaryAbelian p ↥W := MinimalNormalElemAb hMin hWp
  have hWcomm : IsMulCommutative ↥W := ⟨⟨fun x y => hElemT.comm x y⟩⟩
  have hpsmul : ∀ x : Additive ↥W, (p : ℕ) • x = 0 := by
    intro x
    apply Additive.toMul.injective
    rw [toMul_nsmul, toMul_zero]
    exact hElemT.pow_eq_one x.toMul
  have hWmod : Module (ZMod p) (Additive ↥W) := AddCommGroup.zmodModule hpsmul
  have hWfin : Finite ↥W := inferInstance
  -- The conjugation representation `ρ : M → GL(U/V)`.
  set ρ : Representation (ZMod p) M (Additive ↥W) :=
    (OddOrder.BG.Ch1_Preliminary.mulAutToEnd ↥W p).comp
      ((MulAut.conjNormal (H := W)).comp (QuotientGroup.mk' V)) with hρdef
  have hρ_apply : ∀ (g : M) (x : Additive ↥W),
      ρ g x = Additive.ofMul (MulAut.conjNormal (H := W) (QuotientGroup.mk' V g)
        (Additive.toMul x)) := by
    intro g x; rfl
  -- Faithfulness: the kernel of `ρ` is the chief-factor centralizer `C_M(U/V)`.
  have hker : ∀ g : M, ρ g = 1 ↔ g ∈ chiefFactorCentralizer U V := by
    intro g
    rw [chiefFactorCentralizer.mem_iff, Subgroup.mem_centralizer_iff]
    constructor
    · intro hg w hw
      have hx := DFunLike.congr_fun hg (Additive.ofMul (⟨w, hw⟩ : ↥W))
      rw [hρ_apply, Module.End.one_apply] at hx
      have hcoe := congrArg (Subtype.val) (Additive.ofMul.injective hx)
      rw [MulAut.conjNormal_apply] at hcoe
      exact (mul_inv_eq_iff_eq_mul.mp hcoe).symm
    · intro hg
      ext x
      have h : MulAut.conjNormal (H := W) (QuotientGroup.mk' V g) (Additive.toMul x)
          = Additive.toMul x := by
        apply Subtype.ext
        rw [MulAut.conjNormal_apply]
        have hcomm := hg ((Additive.toMul x : ↥W) : M ⧸ V) (Additive.toMul x).2
        exact mul_inv_eq_iff_eq_mul.mpr hcomm.symm
      simp only [hρ_apply, Module.End.one_apply, h, ofMul_toMul]
  -- Descend to the faithful representation `ρbar` of `M ⧸ C`.
  set C : Subgroup M := chiefFactorCentralizer U V with hCdef
  haveI hCn : C.Normal := chiefFactorCentralizer.normal
  have hC_le_ker : C ≤ (ρ : M →* _).ker := fun g hg => (hker g).mpr hg
  set ρbar : Representation (ZMod p) (M ⧸ C) (Additive ↥W) :=
    QuotientGroup.lift C ρ hC_le_ker with hρbardef
  have hρbar_mk : ∀ g : M, ρbar (QuotientGroup.mk' C g) = ρ g := fun g => rfl
  have hρbar_faithful : Function.Injective ρbar := by
    rw [injective_iff_map_eq_one]
    intro x hx
    obtain ⟨g, rfl⟩ := QuotientGroup.mk'_surjective C x
    rw [hρbar_mk] at hx
    exact (QuotientGroup.eq_one_iff g).mpr ((hker g).mp hx)
  -- Every `M ⧸ V`-invariant subgroup of `W = U/V` is trivial or everything (chief factor).
  have hWsub : ∀ (T : Subgroup ↥W),
      (∀ (g : M) (x : ↥W), x ∈ T →
        MulAut.conjNormal (H := W) (QuotientGroup.mk' V g) x ∈ T) →
      T = ⊥ ∨ T = ⊤ := by
    intro T hT
    set N : Subgroup (M ⧸ V) := T.map W.subtype with hNdef
    have hNle : N ≤ W := by rintro _ ⟨x, -, rfl⟩; exact x.2
    have hNnorm : N.Normal := by
      rw [hNdef]
      refine ⟨?_⟩
      rintro _ ⟨x, hx, rfl⟩ gbar
      obtain ⟨g, rfl⟩ := QuotientGroup.mk'_surjective V gbar
      have hconj : (QuotientGroup.mk' V g) * (W.subtype x) * (QuotientGroup.mk' V g)⁻¹ ∈ W :=
        hWn.conj_mem _ x.2 _
      refine ⟨⟨_, hconj⟩, ?_, rfl⟩
      have heq : (⟨_, hconj⟩ : ↥W) = MulAut.conjNormal (H := W) (QuotientGroup.mk' V g) x := by
        apply Subtype.ext
        simp only [MulAut.conjNormal_apply, Subgroup.coe_subtype]
      rw [heq]
      exact hT g x hx
    rcases hMin.2.2 N hNnorm hNle with hNbot | hNtop
    · left
      rw [Subgroup.eq_bot_iff_forall]
      intro x hx
      have hxN : ((x : ↥W) : M ⧸ V) ∈ N := ⟨x, hx, rfl⟩
      rw [hNbot, Subgroup.mem_bot] at hxN
      exact Subtype.coe_inj.mp (by rw [hxN, Subgroup.coe_one])
    · right
      refine le_antisymm le_top ?_
      intro x _
      have hxN : ((x : ↥W) : M ⧸ V) ∈ N := by simp [hNtop]
      rw [hNdef] at hxN
      obtain ⟨y, hy, hyeq⟩ := hxN
      rwa [Subtype.coe_inj.mp hyeq] at hy
  -- `U/V` is irreducible for `M ⧸ C`, being a chief factor.
  have hirr : ∀ (S : Submodule (ZMod p) (Additive ↥W)),
      (∀ g : M ⧸ C, ∀ v ∈ S, ρbar g v ∈ S) → S = ⊥ ∨ S = ⊤ := by
    intro S hS
    set T : Subgroup ↥W := S.toAddSubgroup.toSubgroup' with hTdef
    have hmem : ∀ x : ↥W, x ∈ T ↔ Additive.ofMul x ∈ S := by
      intro x
      rw [hTdef, AddSubgroup.mem_toSubgroup', Submodule.mem_toAddSubgroup]
    have hT : ∀ (g : M) (x : ↥W), x ∈ T →
        MulAut.conjNormal (H := W) (QuotientGroup.mk' V g) x ∈ T := by
      intro g x hx
      rw [hmem] at hx ⊢
      have h := hS (QuotientGroup.mk' C g) (Additive.ofMul x) hx
      rw [hρbar_mk g, hρ_apply g (Additive.ofMul x)] at h
      simpa using h
    rcases hWsub T hT with hTbot | hTtop
    · left
      rw [Submodule.eq_bot_iff]
      intro v hv
      have hvT : Additive.toMul v ∈ T := (hmem _).mpr (by simpa using hv)
      rw [hTbot, Subgroup.mem_bot] at hvT
      rw [← ofMul_toMul v, hvT, ofMul_one]
    · right
      rw [Submodule.eq_top_iff']
      intro v
      have hvT : Additive.toMul v ∈ T := by rw [hTtop]; exact Subgroup.mem_top _
      exact (hmem _).mp hvT
  -- `a` acts quadratically on `U/V`, hence `(ρbar ā - 1)^2 = 0`.
  have hquadZ : ((ρbar (QuotientGroup.mk' C a) : Module.End (ZMod p) (Additive ↥W)) - 1) ^ 2
      = 0 := by
    have hfix : ∀ x : ↥W, MulAut.conjNormal (H := W) (QuotientGroup.mk' V a)
        (MulAut.conjNormal (H := W) (QuotientGroup.mk' V a) x * x⁻¹)
        = MulAut.conjNormal (H := W) (QuotientGroup.mk' V a) x * x⁻¹ := by
      intro x
      exact ConjNormalQuadratic hUK hKAA ha x
    have hρa : ρbar (QuotientGroup.mk' C a) =
        OddOrder.BG.Ch1_Preliminary.mulAutToEnd ↥W p
          (MulAut.conjNormal (H := W) (QuotientGroup.mk' V a)) := by
      rw [hρbar_mk]
      rfl
    rw [hρa]
    exact QuadraticLinear (E := ↥W) p _ hfix
  -- `ā ≠ 1` in `M ⧸ C`, since `a ∉ C`.
  have hne1 : ρbar (QuotientGroup.mk' C a) ≠ 1 := by
    intro h1
    refine haC ?_
    have h : QuotientGroup.mk' C a = 1 := hρbar_faithful (h1.trans (map_one ρbar).symm)
    exact (QuotientGroup.eq_one_iff a).mp h
  have habar_p : IsPGroup p (Subgroup.zpowers (QuotientGroup.mk' C a)) := by
    have hmem : QuotientGroup.mk' C a ∈ A.map (QuotientGroup.mk' C) :=
      Subgroup.mem_map_of_mem _ ha
    exact (hA.map (QuotientGroup.mk' C)).to_le (Subgroup.zpowers_le.mpr hmem)
  -- The section-strength quadratic-pair lemma applied to the faithful irreducible action of
  -- `M ⧸ C` on the chief factor `U/V` yields a bad section of `M ⧸ C`, which pulls back to a bad
  -- section of `M` (`BadSectionOfQuotientProp`), contradicting `hM`.
  exact absurd (hBQ C hM)
    (hQS (L := M ⧸ C) (V := Additive ↥W) (p := p) hp2 ρbar hρbar_faithful hirr
      (QuotientGroup.mk' C a) habar_p hquadZ hne1)

end Work.PSTAB
