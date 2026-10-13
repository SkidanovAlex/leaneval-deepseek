import Mathlib
import Submission.Work.DSM7p.Basic
import Submission.Work.DSM7p.BaseChange

/-!
# DSM7p — base change of the value ideal

`Work.DSM7p.valIdeal_map`: for `A → B` flat and `P` bounded-above finite free, the value ideal
over `B` modulo `I · B` is the extension of the value ideal over `A` modulo `I`.
-/

open CategoryTheory
open scoped TensorProduct

set_option linter.style.haveILetI false

namespace Work.DSM7p

universe a

/-! ## The `A`-side splitting functionals -/

section ASide

variable {A : Type a} [CommRing A]

/-- The `A`-side module of splitting functionals
`F_A = {t : P⁰ →ₗ[A] A ⧸ I | t ∘ d⁻¹ = 0}`. -/
noncomputable def splitFun (P : CochainComplex (ModuleCat.{a} A) ℤ) (I : Ideal A) :
    Submodule A (P.X 0 →ₗ[A] A ⧸ I) :=
  LinearMap.ker (LinearMap.lcomp A (A ⧸ I) (P.d (-1) 0).hom)

/-- Evaluation `t ↦ t (ε 1)` on the `A`-side. -/
noncomputable def evalFun (P : CochainComplex (ModuleCat.{a} A) ℤ)
    (ε : ModuleCat.of A A ⟶ P.X 0) (I : Ideal A) :
    (P.X 0 →ₗ[A] A ⧸ I) →ₗ[A] A ⧸ I :=
  LinearMap.applyₗ (M := P.X 0) (M₂ := A ⧸ I) (ε.hom 1)

lemma evalFun_apply (P : CochainComplex (ModuleCat.{a} A) ℤ)
    (ε : ModuleCat.of A A ⟶ P.X 0) (I : Ideal A) (t : P.X 0 →ₗ[A] A ⧸ I) :
    evalFun P ε I t = t (ε.hom 1) := by
  rw [evalFun, LinearMap.applyₗ_apply_apply]

lemma mem_splitFun (P : CochainComplex (ModuleCat.{a} A) ℤ) (I : Ideal A)
    (t : P.X 0 →ₗ[A] A ⧸ I) :
    t ∈ splitFun P I ↔ t.comp (P.d (-1) 0).hom = 0 := by
  have h : (LinearMap.lcomp A (A ⧸ I) (P.d (-1) 0).hom) t = t.comp (P.d (-1) 0).hom := by
    ext x; rw [LinearMap.lcomp_apply, LinearMap.comp_apply]
  change t ∈ LinearMap.ker (LinearMap.lcomp A (A ⧸ I) (P.d (-1) 0).hom) ↔
    t.comp (P.d (-1) 0).hom = 0
  rw [LinearMap.mem_ker, h]

/-- **`F_A` cut out by the value ideal.**  `a : A` lies in the value ideal over `A` modulo `I`
iff its class in `A ⧸ I` is a value of `F_A`. -/
lemma mem_valIdeal_iff_mk_mem (P : CochainComplex (ModuleCat.{a} A) ℤ)
    (ε : ModuleCat.of A A ⟶ P.X 0) (I : Ideal A) (a : A) :
    a ∈ valIdeal P ε (RingHom.id A) I ↔
      Ideal.Quotient.mk I a ∈ Submodule.map (evalFun P ε I) (splitFun P I) := by
  rw [mem_valIdeal, Work.DSAM3.modSplit_iff_ModSplitA]
  unfold Work.DSAM3.ModSplitA
  dsimp only
  constructor
  · rintro ⟨t, ht, hte⟩
    exact Submodule.mem_map.mpr ⟨t, (mem_splitFun P I t).mpr ht, by
      rw [evalFun_apply]; exact hte⟩
  · rintro ⟨t, ht, hte⟩
    exact ⟨t, (mem_splitFun P I t).mp ht, by rw [evalFun_apply] at hte; exact hte⟩

end ASide

/-! ## The main computation

The `A`-module structure on `B ⧸ I · B` that `DSMap.Mix.ModSplit` uses is the one induced by
`(algebraMap A B).toAlgebra`.  Everything on the `B`-side is therefore done inside the scope of a
`letI : Algebra A B := (algebraMap A B).toAlgebra`, so that the instance is syntactically the one
`ModSplit` uses. -/

theorem valIdeal_map_local {A B : Type a} [CommRing A] [CommRing B] [Algebra A B]
    (hB : @Module.Flat A B _ _ (@Algebra.toModule A B _ _ (algebraMap A B).toAlgebra))
    (P : CochainComplex (ModuleCat.{a} A) ℤ) (ε : ModuleCat.of A A ⟶ P.X 0)
    (hP : DSMap.Mix.IsBddFinFree P) (I : Ideal A) :
    valIdeal P ε (algebraMap A B) (I.map (algebraMap A B)) =
      (valIdeal P ε (RingHom.id A) I).map (algebraMap A B) := by
  letI : Algebra A B := (algebraMap A B).toAlgebra
  haveI : Module.Flat A B := hB
  haveI : Module.Finite A (P.X 0) := (hP.1 0).2
  haveI : Module.Free A (P.X 0) := (hP.1 0).1
  haveI : Module.Finite A (P.X (-1)) := (hP.1 (-1)).2
  haveI : Module.Free A (P.X (-1)) := (hP.1 (-1)).1
  let VA : Submodule A (A ⧸ I) := Submodule.map (evalFun P ε I) (splitFun P I)
  let KA : Ideal A := valIdeal P ε (RingHom.id A) I
  let FB : Submodule A (P.X 0 →ₗ[A] B ⧸ (I.map (algebraMap A B))) :=
    LinearMap.ker (LinearMap.lcomp A (B ⧸ (I.map (algebraMap A B))) (P.d (-1) 0).hom)
  let evB : (P.X 0 →ₗ[A] B ⧸ (I.map (algebraMap A B))) →ₗ[A] B ⧸ (I.map (algebraMap A B)) :=
    LinearMap.applyₗ (M := P.X 0) (M₂ := B ⧸ (I.map (algebraMap A B))) (ε.hom 1)
  have memA : ∀ a : A, a ∈ KA ↔ Ideal.Quotient.mk I a ∈ VA := mem_valIdeal_iff_mk_mem P ε I
  have hVA : ∀ v ∈ VA, ∃ a ∈ KA, Ideal.Quotient.mk I a = v := by
    intro v hv
    obtain ⟨a, ha⟩ := Submodule.Quotient.mk_surjective (I : Submodule A A) v
    have ha' : Ideal.Quotient.mk I a = v := (Ideal.Quotient.mk_eq_mk (I := I) a).symm.trans ha
    exact ⟨a, (memA a).mpr (by rw [ha']; exact hv), ha'⟩
  have memB : ∀ c : B, c ∈ valIdeal P ε (algebraMap A B) (I.map (algebraMap A B)) ↔
      Ideal.Quotient.mk (I.map (algebraMap A B)) c ∈ Submodule.map evB FB := by
    intro c
    rw [mem_valIdeal, Work.DSAM3.modSplit_iff_ModSplitA]
    unfold Work.DSAM3.ModSplitA
    dsimp only
    have hFB : ∀ t : P.X 0 →ₗ[A] B ⧸ (I.map (algebraMap A B)),
        t ∈ FB ↔ t.comp (P.d (-1) 0).hom = 0 := by
      intro t
      have h : (LinearMap.lcomp A (B ⧸ (I.map (algebraMap A B))) (P.d (-1) 0).hom) t
          = t.comp (P.d (-1) 0).hom := by
        ext x; rw [LinearMap.lcomp_apply, LinearMap.comp_apply]
      change t ∈ LinearMap.ker (LinearMap.lcomp A (B ⧸ (I.map (algebraMap A B)))
        (P.d (-1) 0).hom) ↔ t.comp (P.d (-1) 0).hom = 0
      rw [LinearMap.mem_ker, h]
    have hevB : ∀ t : P.X 0 →ₗ[A] B ⧸ (I.map (algebraMap A B)), evB t = t (ε.hom 1) := by
      intro t
      change (LinearMap.applyₗ (M := P.X 0) (M₂ := B ⧸ (I.map (algebraMap A B)))
        (ε.hom 1)) t = t (ε.hom 1)
      rw [LinearMap.applyₗ_apply_apply]
    constructor
    · rintro ⟨t, ht, hte⟩
      exact Submodule.mem_map.mpr ⟨t, (hFB t).mpr ht, by rw [hevB]; exact hte⟩
    · rintro ⟨t, ht, hte⟩
      exact ⟨t, (hFB t).mp ht, by rw [hevB] at hte; exact hte⟩
  -- the base change of `F_A` to `F_B`
  have hbc : Submodule.map evB FB =
      LinearMap.range ((quotSMulEquiv (A := A) (B := B) I).toLinearMap ∘ₗ
        (VA.subtype.rTensor B)) := by
    have hk := homBaseChange_map_ker (A := A) (B := B) I (P.d (-1) 0).hom
    have hev := eval_homBaseChange (A := A) (B := B) I (ε.hom 1)
    have hVA' : LinearMap.range (evalFun P ε I ∘ₗ
        (LinearMap.ker (LinearMap.lcomp A (A ⧸ I) (P.d (-1) 0).hom)).subtype) = VA := by
      rw [LinearMap.range_comp, Submodule.range_subtype]
      rfl
    change Submodule.map evB (LinearMap.ker (LinearMap.lcomp A
      (B ⧸ (I.map (algebraMap A B))) (P.d (-1) 0).hom)) = _
    rw [← hk]
    rw [← Submodule.map_comp, ← Submodule.map_comp, Submodule.map_top]
    rw [show evB ∘ₗ (homBaseChange (A := A) (B := B) I (P.X 0)).toLinearMap
        = (quotSMulEquiv (A := A) (B := B) I).toLinearMap ∘ₗ (evalFun P ε I).rTensor B
        from hev]
    rw [LinearMap.comp_assoc, ← LinearMap.rTensor_comp, LinearMap.range_comp,
      LinearMap.rTensor_range, hVA', LinearMap.range_comp]
  -- the range of `κ ∘ VA.subtype.rTensor B` lies in the extension ideal
  have hgen : ∀ z : (VA ⊗[A] B),
      ((quotSMulEquiv (A := A) (B := B) I).toLinearMap ∘ₗ (VA.subtype.rTensor B)) z ∈
        Submodule.map (Submodule.mkQ (I.map (algebraMap A B))) (Ideal.map (algebraMap A B) KA) := by
    intro z
    induction z using TensorProduct.induction_on with
    | zero => rw [map_zero]; exact Submodule.zero_mem _
    | tmul v b =>
      obtain ⟨a, haK, hav⟩ := hVA v v.2
      have hav' : VA.subtype v = Ideal.Quotient.mk I a := hav.symm
      show (quotSMulEquiv (A := A) (B := B) I)
        ((VA.subtype.rTensor B) (v ⊗ₜ[A] b)) ∈
          Submodule.map (Submodule.mkQ (I.map (algebraMap A B))) (Ideal.map (algebraMap A B) KA)
      rw [LinearMap.rTensor_tmul, hav', quotSMulEquiv_mk_tmul]
      refine Submodule.mem_map.mpr ⟨algebraMap A B a * b, ?_, ?_⟩
      · exact (Ideal.map (algebraMap A B) KA).mul_mem_right b
          (Ideal.mem_map_of_mem (algebraMap A B) haK)
      · rw [Submodule.mkQ_apply, Ideal.Quotient.mk_eq_mk, Algebra.smul_def]
    | add x y hx hy => rw [map_add]; exact Submodule.add_mem _ hx hy
  refine le_antisymm ?_ ?_
  · -- hard direction
    intro c hc
    have hc' := (memB c).mp hc
    rw [hbc] at hc'
    obtain ⟨z, hz⟩ := LinearMap.mem_range.mp hc'
    have hmk : Ideal.Quotient.mk (I.map (algebraMap A B)) c ∈
        Submodule.map (Submodule.mkQ (I.map (algebraMap A B)))
          (Ideal.map (algebraMap A B) KA) := by
      rw [← hz]
      exact hgen z
    obtain ⟨y, hyQ, hyw⟩ := Submodule.mem_map.mp hmk
    have hyc : Submodule.Quotient.mk (p := ((I.map (algebraMap A B) : Ideal B) : Submodule B B)) y
        = Submodule.Quotient.mk (p := ((I.map (algebraMap A B) : Ideal B) : Submodule B B)) c := by
      rw [show Submodule.Quotient.mk
            (p := ((I.map (algebraMap A B) : Ideal B) : Submodule B B)) y
          = Submodule.mkQ (I.map (algebraMap A B)) y from (Submodule.mkQ_apply _ y).symm,
        hyw]
      rfl
    have hyJ : y - c ∈ I.map (algebraMap A B) :=
      (Submodule.Quotient.eq _).mp hyc
    have hJQ : I.map (algebraMap A B) ≤ Ideal.map (algebraMap A B) KA :=
      Ideal.map_mono (valIdeal_le_self P ε (RingHom.id A) I)
    have : c ∈ Ideal.map (algebraMap A B) KA := by
      have h1 : y - c ∈ Ideal.map (algebraMap A B) KA := hJQ hyJ
      have hyc' : c = y - (y - c) := by ring
      rw [hyc']
      exact sub_mem hyQ h1
    exact this
  · -- easy direction: extension of scalars
    rw [Ideal.map_le_iff_le_comap]
    intro a ha
    rw [Ideal.mem_comap]
    have h1 : Work.DSAM3.ModSplitA P ε (RingHom.id A) I a :=
      (Work.DSAM3.modSplit_iff_ModSplitA P ε (RingHom.id A) I a).mp
        ((mem_valIdeal P ε (RingHom.id A) I a).mp ha)
    have h2 := Work.DSAM3.modSplitA_baseChange (D := A) (D' := B) (P := P) (ε := ε)
      (RingHom.id A) I a h1
    rw [RingHom.comp_id] at h2
    exact (mem_valIdeal P ε (algebraMap A B) (I.map (algebraMap A B))
      (algebraMap A B a)).mpr
      ((Work.DSAM3.modSplit_iff_ModSplitA P ε (algebraMap A B)
        (I.map (algebraMap A B)) (algebraMap A B a)).mpr h2)

theorem valIdeal_map {A B : Type a} [CommRing A] [CommRing B] [Algebra A B]
    [Module.Flat A B] (P : CochainComplex (ModuleCat.{a} A) ℤ) (ε : ModuleCat.of A A ⟶ P.X 0)
    (hP : DSMap.Mix.IsBddFinFree P) (I : Ideal A) :
    valIdeal P ε (algebraMap A B) (I.map (algebraMap A B)) =
      (valIdeal P ε (RingHom.id A) I).map (algebraMap A B) := by
  have hB : @Module.Flat A B _ _ (@Algebra.toModule A B _ _ (algebraMap A B).toAlgebra) := by
    rw [toAlgebra_algebraMap (R := A) (S := B)]
    exact ‹Module.Flat A B›
  exact valIdeal_map_local hB P ε hP I

end Work.DSM7p
