import Mathlib
import Submission.Work.MbarHomology.CellAtlas.InsertSetup

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


namespace Work.MbarHomology

open CategoryTheory

noncomputable section

namespace CellAtlas

-- Pin the `ℤ`-module structures on free modules so that they agree with the ones
-- used by Mathlib's own `LinearEquiv` constructions (as in `Core.lean`).
attribute [local instance 2000] Pi.Function.module Finsupp.module
attribute [local instance 100] ZSMul.toSMul
attribute [local instance 100] instMulActionIntOfSubtractionMonoid

variable {K : Work.DeltaHomology.DeltaCx} {P : Work.Subdivision.PolyCW}
  {C : Work.Certificates.FinChainCx}

/-! ## The abstract quotient computation in the free module `ι → ℤ`

For submodules `R = Q ⊔ L`, `Q ⊓ L = ⊥` and `L = ℤ ∙ x` where `x` is a basis
vector `Pi.single i 1` of the free module `ι → ℤ`, the coefficient map
`ℤ → ↥R ⧸ Q`, `1 ↦ [x]`, is bijective. -/

/-- The `spanMap` of an element of a `ℤ`-module is bijective exactly when the
underlying linear map `ℤ → M`, `k ↦ k • x`, is; the source differs from `ℤ` only
by the (bijective) universe lift `ULift.moduleEquiv`. -/
private theorem cPieceCoeff_spanMap_bijective_iff (M : ModuleCat ℤ) (x : M) :
    Function.Bijective (Work.Subdivision.PolyCW.spanMap x) ↔
      Function.Bijective (LinearMap.toSpanSingleton (R := ℤ) (M := ↥M) x) := by
  have hcomp : (⇑(Work.Subdivision.PolyCW.spanMap x) : ULift ℤ → ↥M) =
      ((LinearMap.toSpanSingleton (R := ℤ) (M := ↥M) x) ∘
        (ULift.moduleEquiv (R := ℤ) (M := ℤ) : ULift ℤ → ℤ)) := by
    funext u
    simp only [Work.Subdivision.PolyCW.spanMap, ModuleCat.hom_ofHom, LinearMap.coe_comp,
      Function.comp_apply, LinearEquiv.coe_coe]
  rw [hcomp]
  constructor
  · intro h
    exact (Function.Bijective.of_comp_iff _ (LinearEquiv.bijective _)).mp h
  · intro h
    exact h.comp (LinearEquiv.bijective _)

/-- If `y` generates `M` (as a `ℤ`-module) and is torsion-free
(`k • y = 0 → k = 0`), then the coefficient map `ℤ → M`, `1 ↦ y`, is bijective. -/
private theorem cPieceCoeff_bijective_spanMap_of (M : ModuleCat ℤ) (y : M)
    (hspan : Submodule.span ℤ ({y} : Set (↥M)) = ⊤)
    (htor : ∀ k : ℤ, (LinearMap.toSpanSingleton (R := ℤ) (M := ↥M) y) k = 0 → k = 0) :
    Function.Bijective (Work.Subdivision.PolyCW.spanMap y) := by
  rw [cPieceCoeff_spanMap_bijective_iff (M := M) y]
  refine ⟨?_, ?_⟩
  · intro k l hkl
    have h2 : (LinearMap.toSpanSingleton (R := ℤ) (M := ↥M) y) (k - l) = 0 := by
      rw [map_sub, hkl, sub_self]
    have h3 := htor (k - l) h2
    omega
  · rw [← LinearMap.range_eq_top]
    rw [LinearMap.range_toSpanSingleton]
    exact hspan

/-- **The abstract quotient computation**, in the free module `ι → ℤ`. If
`R = Q ⊔ L` with `Q ⊓ L = ⊥` and `L = ℤ ∙ x` where `x = Pi.single i 1`,
then the coefficient map `ℤ → ↥R ⧸ Q`, `1 ↦ [x]`, is bijective. -/
private theorem cPieceCoeff_bijective_spanMap_quot (ι : Type*) [DecidableEq ι]
    (R Q L : Submodule ℤ (ι → ℤ)) (i : ι)
    (hsup : R = Q ⊔ L) (hinf : Q ⊓ L = ⊥)
    (hL : L = Submodule.span ℤ ({Pi.single i (1:ℤ)} : Set (ι → ℤ)))
    (hx : Pi.single i (1:ℤ) ∈ R) :
    Function.Bijective (Work.Subdivision.PolyCW.spanMap
      (M := ModuleCat.of ℤ (↥R ⧸ Q.comap (Submodule.subtype R)))
      (Submodule.Quotient.mk (p := Q.comap (Submodule.subtype R))
        ⟨Pi.single i (1:ℤ), hx⟩)) := by
  set q : Submodule ℤ ↥R := Q.comap (Submodule.subtype R) with hq
  set gen : ↥R ⧸ q :=
    Submodule.Quotient.mk (p := q) ⟨Pi.single i (1:ℤ), hx⟩ with hgen
  apply cPieceCoeff_bijective_spanMap_of (M := ModuleCat.of ℤ (↥R ⧸ q)) gen
  · -- the class of `x` generates the quotient
    rw [Submodule.eq_top_iff']
    intro m
    induction m using Submodule.Quotient.induction_on with
    | _ v =>
      have hvR : (v : ι → ℤ) ∈ Q ⊔ L := by rw [← hsup]; exact v.2
      obtain ⟨y, hyQ, z, hzL, hyz⟩ := Submodule.mem_sup.mp hvR
      obtain ⟨c, hc⟩ := Submodule.mem_span_singleton.mp (hL ▸ hzL)
      have hv : (v : ι → ℤ) = y + c • Pi.single i (1:ℤ) := by rw [← hyz, ← hc]
      have hq' : (Submodule.Quotient.mk (p := q) v : ↥R ⧸ q) = c • gen := by
        rw [hgen, ← Submodule.Quotient.mk_smul q c (⟨Pi.single i (1:ℤ), hx⟩ : ↥R)]
        rw [Submodule.Quotient.eq]
        rw [Submodule.mem_comap]
        change ((v - c • (⟨Pi.single i (1:ℤ), hx⟩ : ↥R) : ↥R) : ι → ℤ) ∈ Q
        have hcoe : ((v - c • (⟨Pi.single i (1:ℤ), hx⟩ : ↥R) : ↥R) : ι → ℤ)
            = (v : ι → ℤ) - c • Pi.single i (1:ℤ) := by
          rw [Submodule.coe_sub, Submodule.coe_smul]
        rw [hcoe, hv, add_sub_cancel_right]
        exact hyQ
      rw [hq']
      exact Submodule.smul_mem _ _ (Submodule.subset_span (Set.mem_singleton gen))
  · -- the class of `x` is torsion-free
    intro k hk
    have hk' : k • gen = 0 := by rw [← LinearMap.toSpanSingleton_apply]; exact hk
    have hmem : k • Pi.single i (1:ℤ) ∈ Q := by
      have h1 : (Submodule.Quotient.mk (p := q)
          (k • (⟨Pi.single i (1:ℤ), hx⟩ : ↥R)) : ↥R ⧸ q) = 0 := by
        rw [Submodule.Quotient.mk_smul, ← hgen]; exact hk'
      rw [Submodule.Quotient.mk_eq_zero] at h1
      rw [Submodule.mem_comap] at h1
      simpa [Submodule.coe_smul] using h1
    have hmemL : k • Pi.single i (1:ℤ) ∈ L := by
      rw [hL]
      exact Submodule.smul_mem _ _ (Submodule.subset_span (Set.mem_singleton _))
    have hz : (k • Pi.single i (1:ℤ) : ι → ℤ) = 0 := by
      have h2 : k • Pi.single i (1:ℤ) ∈ Q ⊓ L := Submodule.mem_inf.mpr ⟨hmem, hmemL⟩
      rw [hinf] at h2
      simpa using h2
    have hw : (k • Pi.single i (1:ℤ) : ι → ℤ) i = k := by
      simp [Pi.smul_apply]
    have hz' : (k • Pi.single i (1:ℤ) : ι → ℤ) i = 0 := by rw [hz]; rfl
    rw [hw] at hz'
    exact hz'

/-! ## The two submodule identities in degree `n+1` -/

/-- In degree `n+1`, membership in `CMod C n E (n+1)` is a support condition on
the complement of `E`. -/
theorem CMod_succ_apply_eq_zero {n : ℕ} {E : Finset (Fin (C.dim (n + 1)))}
    {x : C.toChainComplex.X (n + 1)} (hx : x ∈ CMod C n E (n + 1))
    {b : Fin (C.dim (n + 1))} (hb : b ∉ E) : x b = 0 :=
  (mem_CMod.mp hx) b (fun hIn => hb ((Insert.inD_succ_iff (E := E) b).mp hIn))

/-- In degree `n+1` the new level is the old one plus the line spanned by the
new generator. -/
theorem CMod_succ_insert_eq_sup (n : ℕ) (E : Finset (Fin (C.dim (n + 1))))
    (f₀ : Fin (C.dim (n + 1))) :
    CMod C n (insert f₀ E) (n + 1) =
      CMod C n E (n + 1) ⊔
        Submodule.span ℤ ({cGen C (n + 1) f₀} : Set (C.toChainComplex.X (n + 1))) := by
  refine le_antisymm ?_ ?_
  · intro x hx
    refine Submodule.mem_sup.mpr
      ⟨x - (x f₀) • cGen C (n + 1) f₀, ?_,
        (x f₀) • cGen C (n + 1) f₀,
        Submodule.smul_mem _ _ (Submodule.subset_span (Set.mem_singleton _)),
        sub_add_cancel _ _⟩
    rw [mem_CMod]
    intro b hb
    have hbE : b ∉ E := fun h => hb ((Insert.inD_succ_iff (E := E) b).mpr h)
    rw [show ((x - (x f₀) • cGen C (n + 1) f₀ : C.toChainComplex.X (n + 1)) :
        Fin (C.dim (n + 1)) → ℤ) b
        = (x : Fin (C.dim (n + 1)) → ℤ) b
          - (x : Fin (C.dim (n + 1)) → ℤ) f₀ *
            (Pi.single f₀ (1:ℤ) : Fin (C.dim (n + 1)) → ℤ) b from rfl]
    by_cases hbf : b = f₀
    · subst hbf
      rw [Pi.single_eq_same, mul_one, sub_self]
    · rw [Pi.single_eq_of_ne hbf, mul_zero, sub_zero]
      exact (mem_CMod.mp hx) b (by
        rw [Insert.inD_succ_iff, Finset.mem_insert]
        exact not_or.mpr ⟨hbf, hbE⟩)
  · refine sup_le ?_ ?_
    · exact CMod_mono (Finset.subset_insert f₀ E) (n + 1)
    · rw [Submodule.span_le]
      rintro y hy
      rw [Set.mem_singleton_iff] at hy
      rw [hy]
      exact Insert.cGen_mem_CMod_insert (C := C) f₀

/-- The line spanned by the new generator meets the old level trivially. -/
theorem CMod_succ_inf_span (n : ℕ) (E : Finset (Fin (C.dim (n + 1))))
    (f₀ : Fin (C.dim (n + 1))) (hf : f₀ ∉ E) :
    CMod C n E (n + 1) ⊓
        Submodule.span ℤ ({cGen C (n + 1) f₀} : Set (C.toChainComplex.X (n + 1))) = ⊥ := by
  refine le_antisymm ?_ bot_le
  intro x hx
  rw [Submodule.mem_bot]
  rw [Submodule.mem_inf] at hx
  obtain ⟨hQ, hL⟩ := hx
  obtain ⟨c, hc⟩ := Submodule.mem_span_singleton.mp hL
  have hxc : x f₀ = c := by
    rw [← hc]
    rw [show ((c • cGen C (n + 1) f₀ : C.toChainComplex.X (n + 1)) :
        Fin (C.dim (n + 1)) → ℤ) f₀
        = c * (Pi.single f₀ (1:ℤ) : Fin (C.dim (n + 1)) → ℤ) f₀ from rfl]
    rw [Pi.single_eq_same, mul_one]
  have hf0 : x f₀ = 0 := CMod_succ_apply_eq_zero hQ hf
  have hc0 : c = 0 := by rw [hxc] at hf0; exact hf0
  rw [← hc, hc0]
  exact zero_smul ℤ _

/-! ## The coefficient map of the cellular piece is a bijection -/

theorem insert_cPieceCoeffF_bijective {K : Work.DeltaHomology.DeltaCx}
    {P : Work.Subdivision.PolyCW} {C : Work.Certificates.FinChainCx}
    (A : Work.MbarHomology.CellAtlas K P C) (n : ℕ)
    (E : Finset (Fin (C.dim (n + 1)))) (f₀ : Fin (C.dim (n + 1))) (hf : f₀ ∉ E) :
    Function.Bijective (Work.MbarHomology.CellAtlas.Insert.cPieceCoeffF A n E f₀) := by
  have key := cPieceCoeff_bijective_spanMap_quot (Fin (C.dim (n + 1)))
    (CMod C n (insert f₀ E) (n + 1)) (CMod C n E (n + 1))
    (Submodule.span ℤ ({cGen C (n + 1) f₀} : Set (C.toChainComplex.X (n + 1))))
    f₀ (CMod_succ_insert_eq_sup (C := C) n E f₀) (CMod_succ_inf_span (C := C) n E f₀ hf)
    rfl (Insert.cGen_mem_CMod_insert (C := C) f₀)
  rw [Insert.cPieceCoeffF]
  exact key

end CellAtlas

end

end Work.MbarHomology
