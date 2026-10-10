import Mathlib.Order.CompletePartialOrder
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.DedekindDomain.AdicValuation
import Mathlib.RingTheory.Norm.Transitivity
import Mathlib.RingTheory.RamificationInertia.Inertia
import Mathlib.RingTheory.RamificationInertia.Ramification
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
import Submission.Commons.FieldTheory.Galois.hilbert90_cyclic
import Submission.Commons.GroupTheory.Cohomology.natCard_ker_sub_quotient_range_norm_eq_natCard_ker_norm_quotient_range_sub
import Submission.Commons.GroupTheory.Subgroup.index_eq_of_ker_le_of_map_eq_zpowers
import Submission.Commons.NumberTheory.NumberField.Completion.finite_quotient_units_range_norm_adicCompletion
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END
open scoped NumberField WithZero BigOperators
open IsDedekindDomain.HeightOneSpectrum
open Commons.NumberTheory.NumberField.Completion
open Commons.FieldTheory.Galois
noncomputable section
namespace Commons.NumberTheory.NumberField.Completion

variable {K L : Type*} [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
  [FiniteDimensional K L] [IsGalois K L]

noncomputable def unitsValLog (F : Type*) [Field F] [Valued F (WithZero (Multiplicative ℤ))] :
    Fˣ →* Multiplicative ℤ where
  toFun u := Multiplicative.ofAdd (WithZero.log (Valued.v (R := F) (Γ₀ := WithZero (Multiplicative ℤ)) (u : F)))
  map_one' := by simp
  map_mul' u v := by
    have hu : Valued.v (R := F) (Γ₀ := WithZero (Multiplicative ℤ)) (u : F) ≠ 0 :=
      (Valuation.ne_zero_iff _).mpr (Units.ne_zero u)
    have hv : Valued.v (R := F) (Γ₀ := WithZero (Multiplicative ℤ)) (v : F) ≠ 0 :=
      (Valuation.ne_zero_iff _).mpr (Units.ne_zero v)
    simp only [Units.val_mul, map_mul, WithZero.log_mul hu hv]
    rfl

@[simp]
lemma unitsValLog_apply (F : Type*) [Field F] [Valued F (WithZero (Multiplicative ℤ))] (u : Fˣ) :
    unitsValLog F u = Multiplicative.ofAdd
      (WithZero.log (Valued.v (R := F) (Γ₀ := WithZero (Multiplicative ℤ)) (u : F))) := rfl

lemma unitsValLog_eq_one_iff {F : Type*} [Field F] [Valued F (WithZero (Multiplicative ℤ))]
    (u : Fˣ) : unitsValLog F u = 1 ↔ Valued.v (R := F) (Γ₀ := WithZero (Multiplicative ℤ)) (u : F) = 1 := by
  rw [unitsValLog_apply]
  have hne : Valued.v (R := F) (Γ₀ := WithZero (Multiplicative ℤ)) (u : F) ≠ 0 :=
    (Valuation.ne_zero_iff _).mpr (Units.ne_zero u)
  constructor
  · intro h
    have h' : WithZero.log (Valued.v (R := F) (Γ₀ := WithZero (Multiplicative ℤ)) (u : F)) = 0 := by
      have := congrArg Multiplicative.toAdd h
      simpa using this
    rw [← WithZero.exp_log hne, h']
    rfl
  · intro h; rw [h]; simp

def adicUnitsVal (K : Type*) [Field K] [NumberField K]
    (v : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K)) :
    Subgroup (v.adicCompletion K)ˣ :=
  (unitsValLog (v.adicCompletion K)).ker

lemma mem_adicUnitsVal (K : Type*) [Field K] [NumberField K]
    (v : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K))
    (u : (v.adicCompletion K)ˣ) :
    u ∈ adicUnitsVal K v ↔
      Valued.v (R := v.adicCompletion K) (Γ₀ := WithZero (Multiplicative ℤ))
        (u : v.adicCompletion K) = 1 := by
  rw [adicUnitsVal, MonoidHom.mem_ker, unitsValLog_eq_one_iff]

lemma adicUnitsVal_eq_unitGroup (K : Type*) [Field K] [NumberField K]
    (v : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K)) :
    adicUnitsVal K v = (v.adicCompletionIntegers K).unitGroup := by
  ext u
  rw [mem_adicUnitsVal]
  exact (Valuation.mem_unitGroup_iff (v.adicCompletion K)
    (Valued.v (R := v.adicCompletion K) (Γ₀ := WithZero (Multiplicative ℤ))) u).symm

section Main

variable (Q : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K))
  (q : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers L))
  (hq : q.asIdeal.LiesOver Q.asIdeal)

lemma unitsValLog_adicCompletion_surjective (K : Type*) [Field K] [NumberField K]
    (v : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K)) :
    Function.Surjective (unitsValLog (v.adicCompletion K)) := by
  intro z
  set π : v.adicCompletion K :=
    ((Commons.RingTheory.Henselian.uniformizer (R := NumberField.RingOfIntegers K) (K := K) v :
      v.adicCompletionIntegers K) : v.adicCompletion K)
  have hπval : Valued.v (R := v.adicCompletion K) (Γ₀ := WithZero (Multiplicative ℤ)) π =
      WithZero.exp (-1 : ℤ) :=
    Commons.RingTheory.Henselian.uniformizer_valuation_eq_exp_neg_one v
  have hπne : π ≠ 0 := by
    intro h; rw [h, map_zero] at hπval; exact WithZero.exp_ne_zero hπval.symm
  have hνπ : unitsValLog (v.adicCompletion K) (Units.mk0 π hπne) =
      Multiplicative.ofAdd (-1 : ℤ) := by
    rw [unitsValLog_apply, Units.val_mk0, hπval, WithZero.log_exp]
  have hone : ((Multiplicative.ofAdd (-1 : ℤ) : Multiplicative ℤ)) ^ (- z.toAdd) = z := by
    rw [← ofAdd_zsmul]; simp
  refine ⟨(Units.mk0 π hπne) ^ (- z.toAdd), ?_⟩
  rw [map_zpow, hνπ, hone]

lemma unitsValLog_smul :
    letI : Algebra (Q.adicCompletion K) (q.adicCompletion L) :=
      RingHom.toAlgebra (Commons.RingTheory.Henselian.adicCompletionMap Q q hq)
    ∀ (σ : q.adicCompletion L ≃ₐ[Q.adicCompletion K] q.adicCompletion L)
      (u : (q.adicCompletion L)ˣ),
      unitsValLog (q.adicCompletion L) (σ • u) = unitsValLog (q.adicCompletion L) u := by
  letI : Algebra (Q.adicCompletion K) (q.adicCompletion L) :=
    RingHom.toAlgebra (Commons.RingTheory.Henselian.adicCompletionMap Q q hq)
  intro σ u
  have hcoe : ((σ • u : (q.adicCompletion L)ˣ) : q.adicCompletion L) =
      σ (u : q.adicCompletion L) := Units.coe_smul σ u
  rw [unitsValLog_apply, unitsValLog_apply, hcoe, val_algEquiv_adicCompletion Q q hq]

lemma unitsValLog_algebraMap :
    letI : Algebra (Q.adicCompletion K) (q.adicCompletion L) :=
      RingHom.toAlgebra (Commons.RingTheory.Henselian.adicCompletionMap Q q hq)
    ∀ (x : (Q.adicCompletion K)ˣ),
    unitsValLog (q.adicCompletion L)
        (Units.map (algebraMap (Q.adicCompletion K) (q.adicCompletion L)).toMonoidHom x) =
      (unitsValLog (Q.adicCompletion K) x) ^ (q.asIdeal.ramificationIdx (NumberField.RingOfIntegers K)) := by
  letI : Algebra (Q.adicCompletion K) (q.adicCompletion L) :=
    RingHom.toAlgebra (Commons.RingTheory.Henselian.adicCompletionMap Q q hq)
  intro x
  rw [unitsValLog_apply, unitsValLog_apply, Units.coe_map]
  change Multiplicative.ofAdd (WithZero.log (Valued.v (R := q.adicCompletion L)
      (Γ₀ := WithZero (Multiplicative ℤ))
      (Commons.RingTheory.Henselian.adicCompletionMap Q q hq (x : Q.adicCompletion K)))) =
    Multiplicative.ofAdd (WithZero.log (Valued.v (R := Q.adicCompletion K)
      (Γ₀ := WithZero (Multiplicative ℤ)) (x : Q.adicCompletion K))) ^
      (q.asIdeal.ramificationIdx (NumberField.RingOfIntegers K))
  rw [val_adicCompletionMap_eq_pow Q q hq, WithZero.log_pow, ofAdd_nsmul]

lemma pow_right_injective_zint {e : ℕ} (he : e ≠ 0) {a b : Multiplicative ℤ}
    (h : a ^ e = b ^ e) : a = b := by
  apply Multiplicative.toAdd.injective
  have h' := congrArg Multiplicative.toAdd h
  simp only [toAdd_pow, nsmul_eq_mul] at h'
  exact mul_left_cancel₀ (Int.ofNat_ne_zero.mpr he) h'

lemma unitsValLog_norm :
    letI : Algebra (Q.adicCompletion K) (q.adicCompletion L) :=
      RingHom.toAlgebra (Commons.RingTheory.Henselian.adicCompletionMap Q q hq)
    ∀ u : (q.adicCompletion L)ˣ,
      unitsValLog (Q.adicCompletion K)
          (Units.map (Algebra.norm (Q.adicCompletion K) : q.adicCompletion L →* Q.adicCompletion K) u) =
        (unitsValLog (q.adicCompletion L) u) ^ (q.asIdeal.inertiaDeg (NumberField.RingOfIntegers K)) := by
  letI : Algebra (Q.adicCompletion K) (q.adicCompletion L) :=
    RingHom.toAlgebra (Commons.RingTheory.Henselian.adicCompletionMap Q q hq)
  haveI hfd : FiniteDimensional (Q.adicCompletion K) (q.adicCompletion L) :=
    Commons.NumberTheory.NumberField.Completion.module_finite_adicCompletion Q q hq
  haveI hgal : IsGalois (Q.adicCompletion K) (q.adicCompletion L) :=
    isGalois_adicCompletion Q q hq
  intro u
  set e := q.asIdeal.ramificationIdx (NumberField.RingOfIntegers K) with he
  set f := q.asIdeal.inertiaDeg (NumberField.RingOfIntegers K) with hf
  have hene : e ≠ 0 := (Ideal.ramificationIdx_pos (q := q.asIdeal) (R := NumberField.RingOfIntegers K)).ne'
  have hfin : Module.finrank (Q.adicCompletion K) (q.adicCompletion L) = e * f :=
    (Commons.NumberTheory.NumberField.finrank_adicCompletion_eq_ramificationIdx_mul_inertiaDeg Q q hq).symm
  have h2 : unitsValLog (q.adicCompletion L)
      (Units.map (algebraMap (Q.adicCompletion K) (q.adicCompletion L)).toMonoidHom
        (Units.map (Algebra.norm (Q.adicCompletion K) : q.adicCompletion L →* Q.adicCompletion K) u)) =
      (unitsValLog (q.adicCompletion L) u) ^ (Module.finrank (Q.adicCompletion K) (q.adicCompletion L)) := by
    have hnorm : (∏ g : (q.adicCompletion L ≃ₐ[Q.adicCompletion K] q.adicCompletion L), g • u) =
        Units.map (algebraMap (Q.adicCompletion K) (q.adicCompletion L)).toMonoidHom
          (Units.map (Algebra.norm (Q.adicCompletion K) : q.adicCompletion L →* Q.adicCompletion K) u) := by
      apply Units.ext
      rw [show (↑(∏ g : (q.adicCompletion L ≃ₐ[Q.adicCompletion K] q.adicCompletion L), g • u) :
          q.adicCompletion L) = ∏ g, (g • (u : q.adicCompletion L)) from
        map_prod (Units.coeHom (q.adicCompletion L)) (fun g => g • u) Finset.univ]
      exact (Algebra.norm_eq_prod_automorphisms (Q.adicCompletion K) (u : q.adicCompletion L)).symm
    rw [← hnorm, map_prod,
      Finset.prod_congr rfl (fun g _ => unitsValLog_smul Q q hq g u), Finset.prod_const, Finset.card_univ]
    congr 1
    rw [← Nat.card_eq_fintype_card]
    exact natCard_algEquiv_adicCompletion_eq_finrank Q q hq
  have key : (unitsValLog (Q.adicCompletion K)
        (Units.map (Algebra.norm (Q.adicCompletion K) : q.adicCompletion L →* Q.adicCompletion K) u)) ^ e
      = (unitsValLog (q.adicCompletion L) u) ^ (e * f) := by
    rw [← unitsValLog_algebraMap Q q hq
      (Units.map (Algebra.norm (Q.adicCompletion K) : q.adicCompletion L →* Q.adicCompletion K) u), h2, hfin]
  refine pow_right_injective_zint hene ?_
  rw [key, mul_comm e f, ← pow_mul]

end Main

set_option linter.style.haveILetI false
set_option maxHeartbeats 1600000

theorem natCard_quotient_units_range_norm_adicCompletion_eq_mul_of_exists_open_subgroup_units_tate_trivial
    {K L : Type*} [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
    [FiniteDimensional K L] [IsGalois K L]
    (Q : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K))
    (q : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers L))
    (hq : q.asIdeal.LiesOver Q.asIdeal) :
    letI : Algebra (Q.adicCompletion K) (q.adicCompletion L) :=
      RingHom.toAlgebra (Commons.RingTheory.Henselian.adicCompletionMap Q q hq)
    ∀ (σgen : q.adicCompletion L ≃ₐ[Q.adicCompletion K] q.adicCompletion L),
      Subgroup.zpowers σgen = ⊤ →
      (∃ W : Subgroup (q.adicCompletion L)ˣ,
        (∀ w ∈ W, Valued.v (R := q.adicCompletion L) (Γ₀ := WithZero (Multiplicative ℤ))
            (w : q.adicCompletion L) = 1) ∧
        (∀ (σ : q.adicCompletion L ≃ₐ[Q.adicCompletion K] q.adicCompletion L)
          (w : (q.adicCompletion L)ˣ), w ∈ W → σ • w ∈ W) ∧
        (∃ M : ℕ, ∀ x : (q.adicCompletionIntegers L)ˣ,
          (x : q.adicCompletionIntegers L) - 1 ∈
              IsLocalRing.maximalIdeal (q.adicCompletionIntegers L) ^ M →
            Units.map (algebraMap (q.adicCompletionIntegers L) (q.adicCompletion L)).toMonoidHom x
              ∈ W) ∧
        (∀ w ∈ W,
          (∀ σ : q.adicCompletion L ≃ₐ[Q.adicCompletion K] q.adicCompletion L, σ • w = w) →
          ∃ v ∈ W, algebraMap (Q.adicCompletion K) (q.adicCompletion L)
              (Algebra.norm (Q.adicCompletion K) (v : q.adicCompletion L)) =
            (w : q.adicCompletion L)) ∧
        (∀ w : (q.adicCompletion L)ˣ, w ∈ W →
          algebraMap (Q.adicCompletion K) (q.adicCompletion L)
              (Algebra.norm (Q.adicCompletion K) (w : q.adicCompletion L)) = 1 →
          ∃ v ∈ W, (w : q.adicCompletion L) =
            σgen (v : q.adicCompletion L) / (v : q.adicCompletion L))) →
      Nat.card ((Q.adicCompletion K)ˣ ⧸
          MonoidHom.range (Units.map (Algebra.norm (Q.adicCompletion K) :
            q.adicCompletion L →* Q.adicCompletion K))) =
        (q.asIdeal.ramificationIdx (NumberField.RingOfIntegers K)) *
          (q.asIdeal.inertiaDeg (NumberField.RingOfIntegers K)) := by
  letI : Algebra (Q.adicCompletion K) (q.adicCompletion L) :=
    RingHom.toAlgebra (Commons.RingTheory.Henselian.adicCompletionMap Q q hq)
  intro σgen hσgen hW
  obtain ⟨W, hWmemB, hWstableB, hWM, hW0B, hW1B⟩ := hW
  let G := q.adicCompletion L ≃ₐ[Q.adicCompletion K] q.adicCompletion L
  let B := (q.adicCompletion L)ˣ
  haveI hfd : FiniteDimensional (Q.adicCompletion K) (q.adicCompletion L) :=
    Commons.NumberTheory.NumberField.Completion.module_finite_adicCompletion Q q hq
  haveI hgal : IsGalois (Q.adicCompletion K) (q.adicCompletion L) :=
    isGalois_adicCompletion Q q hq
  haveI hGcyc : IsCyclic G := isCyclic_iff_exists_zpowers_eq_top.mpr ⟨σgen, hσgen⟩
  set e := q.asIdeal.ramificationIdx (NumberField.RingOfIntegers K) with he
  set f := q.asIdeal.inertiaDeg (NumberField.RingOfIntegers K) with hf
  have hene : e ≠ 0 := (Ideal.ramificationIdx_pos (q := q.asIdeal) (R := NumberField.RingOfIntegers K)).ne'
  have hcardG : Nat.card G = e * f := natCard_algEquiv_adicCompletion_eq_ramificationIdx_mul_inertiaDeg Q q hq
  -- the norm of a product of conjugates
  have norm_prod_eq : ∀ v : B, (∏ g : G, g • v) =
      Units.map (algebraMap (Q.adicCompletion K) (q.adicCompletion L)).toMonoidHom
        (Units.map (Algebra.norm (Q.adicCompletion K) : q.adicCompletion L →* Q.adicCompletion K) v) := by
    intro v
    apply Units.ext
    rw [show (↑(∏ g : G, g • v) : q.adicCompletion L) = ∏ g, (g • (v : q.adicCompletion L)) from
      map_prod (Units.coeHom (q.adicCompletion L)) (fun g => g • v) Finset.univ]
    exact (Algebra.norm_eq_prod_automorphisms (Q.adicCompletion K) (v : q.adicCompletion L)).symm
  let A : Subgroup B := adicUnitsVal L q
  have hAeq : A = (q.adicCompletionIntegers L).unitGroup := adicUnitsVal_eq_unitGroup L q
  have hAstab : ∀ (g : G) (a : A), g • a.1 ∈ A := by
    intro g a
    have hc : ((g • a.1 : B) : q.adicCompletion L) = g (a.1 : q.adicCompletion L) :=
      Units.coe_smul g a.1
    rw [mem_adicUnitsVal L q, hc, val_algEquiv_adicCompletion Q q hq]
    exact (mem_adicUnitsVal L q a.1).mp a.2
  letI : MulDistribMulAction G A :=
    { smul := fun g a => ⟨g • a.1, hAstab g a⟩
      one_smul := fun a => Subtype.ext (one_smul G a.1)
      mul_smul := fun g h a => Subtype.ext (mul_smul g h a.1)
      smul_mul := fun g a b => Subtype.ext (smul_mul' g a.1 b.1)
      smul_one := fun g => Subtype.ext (smul_one g) }
  have hsmul : ∀ (g : G) (a : A), ((g • a : A) : B) = g • a.1 := fun g a => rfl
  let NmA : A →* A :=
  { toFun := fun a => ⟨∏ g : G, g • a.1, Subgroup.prod_mem A (fun g _ => hAstab g a)⟩
    map_one' := by apply Subtype.ext; simp
    map_mul' := by
      intro a b
      apply Subtype.ext
      simp only [Subgroup.coe_mul, Subtype.coe_mk]
      rw [Finset.prod_congr rfl (fun g _ => smul_mul' g a.1 b.1), Finset.prod_mul_distrib] }
  let dA : A →* A :=
  { toFun := fun a => ⟨σgen • a.1 * a.1⁻¹, A.mul_mem (hAstab σgen a) (A.inv_mem a.2)⟩
    map_one' := by apply Subtype.ext; simp
    map_mul' := by
      intro a b
      apply Subtype.ext
      simp only [Subgroup.coe_mul, Subtype.coe_mk, Units.val_mul, map_mul]
      rw [smul_mul', mul_inv_rev]
      ac_rfl }
  have hd : ∀ a : A, dA a = σgen • a * a⁻¹ := by
    intro a
    apply Subtype.ext
    show σgen • a.1 * a.1⁻¹ = (σgen • a * a⁻¹ : A).1
    rw [Subgroup.coe_mul, Subgroup.coe_inv, hsmul]
  have hN : ∀ a : A, NmA a = ∏ g : G, g • a := by
    intro a
    apply Subtype.ext
    show (∏ g : G, g • a.1) = ((∏ g : G, g • a : A) : B)
    rw [show ((∏ g : G, g • a : A) : B) = ∏ g : G, ((g • a : A) : B) from
      map_prod A.subtype (fun g => g • a) Finset.univ]
    exact Finset.prod_congr rfl (fun g _ => hsmul g a)
  have hWleA : W ≤ A := by
    intro w hw
    rw [mem_adicUnitsVal L q]
    exact hWmemB w hw
  let WA : Subgroup A := W.comap A.subtype
  have hWAmem : ∀ a : A, a ∈ WA ↔ a.1 ∈ W := fun a => Iff.rfl
  have hWstab' : ∀ (g : G) (w : A), w ∈ WA → g • w ∈ WA := by
    intro g w hw
    rw [hWAmem] at hw ⊢
    rw [hsmul]
    exact hWstableB g w.1 hw
  have hW0' : ∀ w : A, w ∈ WA → (∀ g : G, g • w = w) → ∃ v ∈ WA, NmA v = w := by
    intro w hw hfix
    rw [hWAmem] at hw
    have hfixB : ∀ g : G, g • w.1 = w.1 := fun g =>
      (hsmul g w).symm.trans (congrArg Subtype.val (hfix g))
    obtain ⟨v, hvW, hv⟩ := hW0B w.1 hw hfixB
    refine ⟨⟨v, hWleA hvW⟩, ?_, ?_⟩
    · rw [hWAmem]; exact hvW
    · apply Subtype.ext
      show (∏ g : G, g • v) = w.1
      rw [norm_prod_eq v]
      apply Units.ext
      simp only [Units.coe_map]
      exact hv
  have hW1' : ∀ w : A, w ∈ WA → NmA w = 1 → ∃ v ∈ WA, w = dA v := by
    intro w hw hNw
    rw [hWAmem] at hw
    have hcoeeq : (algebraMap (Q.adicCompletion K) (q.adicCompletion L)
        (Algebra.norm (Q.adicCompletion K) (w.1 : q.adicCompletion L))) = 1 := by
      have hmap : (((NmA w : A) : B) : q.adicCompletion L) = algebraMap (Q.adicCompletion K) (q.adicCompletion L)
          (Algebra.norm (Q.adicCompletion K) (w.1 : q.adicCompletion L)) := by
        show (((∏ g : G, g • w.1 : B)) : q.adicCompletion L) = algebraMap (Q.adicCompletion K) (q.adicCompletion L)
          (Algebra.norm (Q.adicCompletion K) (w.1 : q.adicCompletion L))
        simp only [norm_prod_eq w.1, Units.coe_map]
        rfl
      rw [← hmap]
      exact congrArg (fun u : A => (u.1 : q.adicCompletion L)) hNw |>.trans (by simp)
    obtain ⟨v, hvW, hv⟩ := hW1B w.1 hw hcoeeq
    refine ⟨⟨v, hWleA hvW⟩, ?_, ?_⟩
    · rw [hWAmem]; exact hvW
    · apply Subtype.ext
      apply Units.ext
      show (w.1 : q.adicCompletion L) = ((dA ⟨v, hWleA hvW⟩).1 : q.adicCompletion L)
      rw [show (dA ⟨v, hWleA hvW⟩).1 = σgen • v * v⁻¹ from rfl]
      have hc : ((σgen • v : B) : q.adicCompletion L) = σgen (v : q.adicCompletion L) :=
        Units.coe_smul σgen v
      rw [Units.val_mul, hc, Units.val_inv_eq_inv_val, hv, div_eq_mul_inv]
  have hηA : ∀ x : (q.adicCompletionIntegers L)ˣ,
      Units.map (algebraMap (q.adicCompletionIntegers L) (q.adicCompletion L)).toMonoidHom x ∈ A := by
    intro x
    rw [hAeq]
    have hx : Units.map (algebraMap (q.adicCompletionIntegers L) (q.adicCompletion L)).toMonoidHom x =
        (((ValuationSubring.unitGroupMulEquiv (q.adicCompletionIntegers L)).symm x : (q.adicCompletionIntegers L).unitGroup) :
          (q.adicCompletion L)ˣ) := by
      apply Units.ext
      rw [Units.coe_map]
      exact ValuationSubring.coe_unitGroupMulEquiv_symm_apply (q.adicCompletionIntegers L) x
    rw [hx]
    exact ((ValuationSubring.unitGroupMulEquiv (q.adicCompletionIntegers L)).symm x).2
  let ηA : (q.adicCompletionIntegers L)ˣ →* A :=
    (Units.map (algebraMap (q.adicCompletionIntegers L) (q.adicCompletion L)).toMonoidHom).codRestrict A hηA
  have hηAsurj : Function.Surjective ηA := by
    intro a
    have ha : (a : B) ∈ (q.adicCompletionIntegers L).unitGroup := by
      rw [← hAeq]; exact a.2
    refine ⟨(ValuationSubring.unitGroupMulEquiv (q.adicCompletionIntegers L)) ⟨a.1, ha⟩, ?_⟩
    apply Subtype.ext
    apply Units.ext
    show (((ValuationSubring.unitGroupMulEquiv (q.adicCompletionIntegers L)) ⟨a.1, ha⟩ :
      (q.adicCompletionIntegers L)ˣ) : q.adicCompletion L) = (a.1 : q.adicCompletion L)
    exact ValuationSubring.coe_unitGroupMulEquiv_apply (q.adicCompletionIntegers L) ⟨a.1, ha⟩
  have hWAfin : WA.FiniteIndex := by
    obtain ⟨M, hM⟩ := hWM
    obtain ⟨U, hUmem, hUfi⟩ := finiteIndex_principalUnits_adicCompletionIntegers (K := L) q M
    have hUleW : U.map ηA ≤ WA := by
      intro y hy
      rw [Subgroup.mem_map] at hy
      obtain ⟨x, hxU, rfl⟩ := hy
      rw [hWAmem]
      exact hM x ((hUmem x).mp hxU)
    have hfin_map : (U.map ηA).FiniteIndex := by
      rw [Subgroup.finiteIndex_iff]
      exact ne_zero_of_dvd_ne_zero hUfi.index_ne_zero (Subgroup.index_map_dvd U hηAsurj)
    exact Subgroup.finiteIndex_of_le hUleW
  haveI : Fintype (A ⧸ WA) := Fintype.ofFinite _
  have hHerb := Commons.GroupTheory.Cohomology.natCard_ker_sub_quotient_range_norm_eq_natCard_ker_norm_quotient_range_sub
    (G := G) σgen hσgen dA NmA hd hN WA hWstab' hW0' hW1'
  -- the "difference" map on B
  let dB : B →* B :=
  { toFun := fun z => σgen • z * z⁻¹
    map_one' := by simp
    map_mul' := by
      intro z z'
      show σgen • (z * z') * (z * z')⁻¹ = (σgen • z * z⁻¹) * (σgen • z' * z'⁻¹)
      rw [smul_mul', mul_inv_rev]
      ac_rfl }
  have hdBapply : ∀ z : B, dB z = σgen • z * z⁻¹ := fun z => rfl
  have hdBker : ∀ z : B, z ∈ dB.ker ↔ ∀ g : G, g • z = z := by
    intro z
    rw [MonoidHom.mem_ker]
    constructor
    · intro h g
      have hs : σgen • z = z := by
        rw [hdBapply, mul_inv_eq_one] at h
        exact h
      have hle : Subgroup.zpowers σgen ≤ MulAction.stabilizer G z :=
        Subgroup.zpowers_le.mpr (MulAction.mem_stabilizer_iff.mpr hs)
      have hg : g ∈ Subgroup.zpowers σgen := by rw [hσgen]; trivial
      exact MulAction.mem_stabilizer_iff.mp (hle hg)
    · intro h
      rw [hdBapply, h σgen, mul_inv_cancel]
  have hfixed_units : ∀ z : B, (∀ g : G, g • z = z) →
      ∃ x : (Q.adicCompletion K)ˣ,
        Units.map (algebraMap (Q.adicCompletion K) (q.adicCompletion L)).toMonoidHom x = z := by
    intro z hz
    have hzL : ∀ g : G, g (z : q.adicCompletion L) = (z : q.adicCompletion L) := by
      intro g
      have h2 := congrArg (fun u : B => (u : q.adicCompletion L)) (hz g)
      have hc : ((g • z : B) : q.adicCompletion L) = g (z : q.adicCompletion L) := Units.coe_smul g z
      rwa [hc] at h2
    obtain ⟨x, hx⟩ := (IsGalois.mem_range_algebraMap_iff_fixed (F := Q.adicCompletion K)
      (E := q.adicCompletion L) (z : q.adicCompletion L)).mpr hzL
    have hxne : x ≠ 0 := by
      intro h0; rw [h0, map_zero] at hx; exact Units.ne_zero z hx.symm
    refine ⟨Units.mk0 x hxne, ?_⟩
    apply Units.ext
    rw [Units.coe_map, Units.val_mk0]
    exact hx
  have pow_mem_zpowers_ofAdd : ∀ (a : Multiplicative ℤ) (n : ℕ),
      a ^ n ∈ Subgroup.zpowers (Multiplicative.ofAdd (n : ℤ)) := by
    intro a n
    rw [Subgroup.mem_zpowers_iff]
    refine ⟨Multiplicative.toAdd a, ?_⟩
    apply Multiplicative.toAdd.injective
    rw [toAdd_zpow, toAdd_pow, toAdd_ofAdd]
    simp only [nsmul_eq_mul]
    ring
  have hmap_νL : Subgroup.map (unitsValLog (q.adicCompletion L)) dB.ker =
      Subgroup.zpowers (Multiplicative.ofAdd (e : ℤ)) := by
    ext y
    constructor
    · intro hy
      rw [Subgroup.mem_map] at hy
      obtain ⟨z, hz, rfl⟩ := hy
      rw [hdBker] at hz
      obtain ⟨x, hx⟩ := hfixed_units z hz
      rw [← hx, unitsValLog_algebraMap Q q hq x]
      exact pow_mem_zpowers_ofAdd _ _
    · intro hy
      rw [Subgroup.mem_zpowers_iff] at hy
      obtain ⟨k, hk⟩ := hy
      obtain ⟨x, hx⟩ := unitsValLog_adicCompletion_surjective K Q (Multiplicative.ofAdd k)
      refine Subgroup.mem_map.mpr ⟨Units.map (algebraMap (Q.adicCompletion K) (q.adicCompletion L)).toMonoidHom x, ?_, ?_⟩
      · rw [hdBker]
        intro g
        apply Units.ext
        show ((g • (Units.map (algebraMap (Q.adicCompletion K) (q.adicCompletion L)).toMonoidHom x) : B) :
            q.adicCompletion L) = ((Units.map (algebraMap (Q.adicCompletion K) (q.adicCompletion L)).toMonoidHom x : B) :
            q.adicCompletion L)
        have hc1 : ((g • (Units.map (algebraMap (Q.adicCompletion K) (q.adicCompletion L)).toMonoidHom x) : B) :
            q.adicCompletion L) =
          g ((Units.map (algebraMap (Q.adicCompletion K) (q.adicCompletion L)).toMonoidHom x : B) :
            q.adicCompletion L) := Units.coe_smul g _
        rw [hc1]
        have hc2 : ((Units.map (algebraMap (Q.adicCompletion K) (q.adicCompletion L)).toMonoidHom x : B) :
            q.adicCompletion L) = algebraMap (Q.adicCompletion K) (q.adicCompletion L) (x : Q.adicCompletion K) :=
          Units.coe_map _ x
        rw [hc2, AlgEquiv.commutes]
      · rw [unitsValLog_algebraMap Q q hq x, hx, ← hk]
        apply Multiplicative.toAdd.injective
        rw [toAdd_zpow, toAdd_pow, toAdd_ofAdd, toAdd_ofAdd]
        simp only [nsmul_eq_mul]
        ring
  have hmapA : Subgroup.map (unitsValLog (q.adicCompletion L)) A = ⊥ := by
    rw [Subgroup.eq_bot_iff_forall]
    intro y hy
    rw [Subgroup.mem_map] at hy
    obtain ⟨z, hz, rfl⟩ := hy
    show unitsValLog (q.adicCompletion L) z = 1
    exact hz
  have hIndex_sup : (A ⊔ dB.ker).index = e := by
    have hsurj := unitsValLog_adicCompletion_surjective L q
    refine Commons.GroupTheory.Subgroup.index_eq_of_ker_le_of_map_eq_zpowers
      (unitsValLog (q.adicCompletion L)) hsurj (A ⊔ dB.ker) e ?_ ?_
    · rw [Subgroup.map_sup, hmapA, hmap_νL]
      simp
    · change (unitsValLog (q.adicCompletion L)).ker ≤ A ⊔ dB.ker
      exact le_sup_left
  have hdArange : dA.range.map A.subtype = A.map dB := by
    ext y
    constructor
    · intro hy
      rw [Subgroup.mem_map] at hy
      obtain ⟨a, ha, rfl⟩ := hy
      obtain ⟨a', rfl⟩ := ha
      rw [Subgroup.mem_map]
      refine ⟨a'.1, a'.2, ?_⟩
      apply Units.ext
      rfl
    · intro hy
      rw [Subgroup.mem_map] at hy
      obtain ⟨z, hz, rfl⟩ := hy
      rw [Subgroup.mem_map]
      refine ⟨dA ⟨z, hz⟩, ⟨⟨z, hz⟩, rfl⟩, ?_⟩
      apply Units.ext
      rfl
  have hkerNA : NmA.ker.map A.subtype = dB.range := by
    ext y
    constructor
    · intro hy
      rw [Subgroup.mem_map] at hy
      obtain ⟨a, ha, rfl⟩ := hy
      have hNa : (NmA a).1 = 1 := by rw [ha]; rfl
      have hnorm : (((NmA a : A) : B) : q.adicCompletion L) = algebraMap (Q.adicCompletion K) (q.adicCompletion L)
          (Algebra.norm (Q.adicCompletion K) (a.1 : q.adicCompletion L)) := by
        show (((∏ g : G, g • a.1 : B)) : q.adicCompletion L) = algebraMap (Q.adicCompletion K) (q.adicCompletion L)
          (Algebra.norm (Q.adicCompletion K) (a.1 : q.adicCompletion L))
        simp only [norm_prod_eq a.1, Units.coe_map]
        rfl
      have hN1 : Algebra.norm (Q.adicCompletion K) (a.1 : q.adicCompletion L) = 1 := by
        apply (algebraMap (Q.adicCompletion K) (q.adicCompletion L)).injective
        rw [map_one, ← hnorm]
        exact congrArg (fun u : A => (u.1 : q.adicCompletion L)) ha |>.trans (by simp)
      obtain ⟨z, hz⟩ := (hilbert90_cyclic σgen hσgen (a.1 : q.adicCompletion L)).mp hN1
      rw [MonoidHom.mem_range]
      refine ⟨z, ?_⟩
      apply Units.ext
      show ((dB z : B) : q.adicCompletion L) = ((a.1 : B) : q.adicCompletion L)
      rw [hdBapply, hz]
      have hc : ((σgen • z : B) : q.adicCompletion L) = σgen (z : q.adicCompletion L) :=
        Units.coe_smul σgen z
      rw [Units.val_mul, hc, Units.val_inv_eq_inv_val, div_eq_mul_inv]
    · intro hy
      rw [MonoidHom.mem_range] at hy
      obtain ⟨z, rfl⟩ := hy
      rw [Subgroup.mem_map]
      have hzA : dB z ∈ A := by
        show unitsValLog (q.adicCompletion L) (dB z) = 1
        rw [hdBapply, map_mul, map_inv, unitsValLog_smul Q q hq σgen z, mul_inv_cancel]
      refine ⟨⟨dB z, hzA⟩, ?_, rfl⟩
      apply Subtype.ext
      show (NmA ⟨dB z, hzA⟩).1 = 1
      show (∏ g : G, g • (dB z)) = 1
      have hcomm2 : ∀ g : G, g • dB z = dB (g • z) := by
        intro g
        change g • (σgen • z * z⁻¹) = σgen • (g • z) * (g • z)⁻¹
        rw [smul_mul', smul_inv', ← mul_smul, ← mul_smul]
        rw [show (g * σgen : G) = σgen * g from by
          obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp (show g ∈ Subgroup.zpowers σgen by rw [hσgen]; trivial)
          rw [← hk]
          exact (Commute.zpow_zpow_self σgen k 1).eq]
      rw [Finset.prod_congr rfl (fun g _ => hcomm2 g), ← map_prod dB (fun g : G => g • z) Finset.univ]
      rw [hdBapply]
      rw [Commons.GroupTheory.Cohomology.herbrand_smul_prod_univ σgen z, mul_inv_cancel]
  have hchain : Nat.card (NmA.ker ⧸ (dA.range.subgroupOf NmA.ker)) = e := by
    rw [← Subgroup.index_eq_card (dA.range.subgroupOf NmA.ker)]
    rw [show (dA.range.subgroupOf NmA.ker).index = dA.range.relIndex NmA.ker from rfl]
    rw [← Subgroup.relIndex_map_map_of_injective (f := A.subtype) dA.range NmA.ker A.subtype_injective]
    rw [hdArange, hkerNA]
    rw [MonoidHom.range_eq_map dB, Subgroup.relIndex_map_map dB A ⊤, top_sup_eq, Subgroup.relIndex_top_right]
    exact hIndex_sup
  set H0 : Subgroup (Q.adicCompletion K)ˣ :=
    MonoidHom.range (Units.map (Algebra.norm (Q.adicCompletion K) : q.adicCompletion L →* Q.adicCompletion K)) with hH0
  set P : Subgroup (Q.adicCompletion K)ˣ := adicUnitsVal K Q with hP
  have hPker : P = (unitsValLog (Q.adicCompletion K)).ker := rfl
  let iota : (Q.adicCompletion K)ˣ →* B :=
    Units.map (algebraMap (Q.adicCompletion K) (q.adicCompletion L)).toMonoidHom
  have hiotainj : Function.Injective iota := by
    intro x y hxy
    apply Units.ext
    apply (algebraMap (Q.adicCompletion K) (q.adicCompletion L)).injective
    have hh := congrArg (fun u : B => (u : q.adicCompletion L)) hxy
    rw [show iota x = Units.map (algebraMap (Q.adicCompletion K) (q.adicCompletion L)).toMonoidHom x from rfl,
        show iota y = Units.map (algebraMap (Q.adicCompletion K) (q.adicCompletion L)).toMonoidHom y from rfl,
        Units.coe_map, Units.coe_map] at hh
    exact hh
  -- identification of the two subgroups
  have hkerA : dA.ker.map A.subtype = P.map iota := by
    ext u
    constructor
    · intro hu
      rw [Subgroup.mem_map] at hu
      obtain ⟨a, ha, rfl⟩ := hu
      have hxa : σgen • a.1 = a.1 := by
        have h1 : dA a = 1 := ha
        have h2 : σgen • a.1 * a.1⁻¹ = 1 := congrArg Subtype.val h1
        rwa [mul_inv_eq_one] at h2
      have hfix : ∀ g : G, g • a.1 = a.1 := by
        intro g
        have hle : Subgroup.zpowers σgen ≤ MulAction.stabilizer G a.1 :=
          Subgroup.zpowers_le.mpr (MulAction.mem_stabilizer_iff.mpr hxa)
        exact MulAction.mem_stabilizer_iff.mp (hle (by rw [hσgen]; trivial))
      obtain ⟨x, hx⟩ := hfixed_units a.1 hfix
      rw [Subgroup.mem_map]
      have hν : unitsValLog (q.adicCompletion L) a.1 = 1 :=
        (unitsValLog_eq_one_iff a.1).mpr ((mem_adicUnitsVal L q a.1).mp a.2)
      rw [← hx, unitsValLog_algebraMap Q q hq x] at hν
      have hν0 : unitsValLog (Q.adicCompletion K) x = 1 := by
        have h2 := congrArg Multiplicative.toAdd hν
        rw [toAdd_pow, toAdd_one, nsmul_eq_mul] at h2
        have h3 : Multiplicative.toAdd (unitsValLog (Q.adicCompletion K) x) = 0 := by
          rcases Int.mul_eq_zero.mp h2 with h4 | h4
          · exact absurd h4 (Int.ofNat_ne_zero.mpr hene)
          · exact h4
        refine Multiplicative.toAdd.injective ?_
        rw [h3, toAdd_one]
      refine ⟨x, ?_, ?_⟩
      · rw [hPker, MonoidHom.mem_ker]; exact hν0
      · rw [show iota x = Units.map (algebraMap (Q.adicCompletion K) (q.adicCompletion L)).toMonoidHom x from rfl]
        exact hx
    · intro hu
      rw [Subgroup.mem_map] at hu
      obtain ⟨x, hxP, rfl⟩ := hu
      rw [Subgroup.mem_map]
      have hx0 : unitsValLog (Q.adicCompletion K) x = 1 := by
        rw [hPker, MonoidHom.mem_ker] at hxP; exact hxP
      have hν : unitsValLog (q.adicCompletion L) (iota x) = 1 := by
        rw [show iota x = Units.map (algebraMap (Q.adicCompletion K) (q.adicCompletion L)).toMonoidHom x from rfl,
          unitsValLog_algebraMap Q q hq x, hx0, one_pow]
      have hmemA : iota x ∈ A := by
        rw [mem_adicUnitsVal L q]
        exact (unitsValLog_eq_one_iff (iota x)).mp hν
      have hfix : ∀ g : G, g • iota x = iota x := by
        intro g
        apply Units.ext
        have hc : ((g • iota x : B) : q.adicCompletion L) = g ((iota x : B) : q.adicCompletion L) :=
          Units.coe_smul g (iota x)
        rw [hc, show ((iota x : B) : q.adicCompletion L) =
            algebraMap (Q.adicCompletion K) (q.adicCompletion L) (x : Q.adicCompletion K) from Units.coe_map _ x]
        rw [AlgEquiv.commutes]
      refine ⟨⟨iota x, hmemA⟩, ?_, rfl⟩
      rw [MonoidHom.mem_ker]
      apply Subtype.ext
      show σgen • (⟨iota x, hmemA⟩ : A).1 * (⟨iota x, hmemA⟩ : A).1⁻¹ = (1 : A).1
      rw [hfix σgen, mul_inv_cancel]
      rfl
  have hNrange : NmA.range.map A.subtype = (H0 ⊓ P).map iota := by
    ext u
    constructor
    · intro hu
      rw [Subgroup.mem_map] at hu
      obtain ⟨a, ha, rfl⟩ := hu
      obtain ⟨a', rfl⟩ := ha
      have hkey : ((NmA a' : A) : B) = iota (Units.map (Algebra.norm (Q.adicCompletion K) :
          q.adicCompletion L →* Q.adicCompletion K) a'.1) := by
        rw [show iota (Units.map (Algebra.norm (Q.adicCompletion K) :
            q.adicCompletion L →* Q.adicCompletion K) a'.1) =
          Units.map (algebraMap (Q.adicCompletion K) (q.adicCompletion L)).toMonoidHom
            (Units.map (Algebra.norm (Q.adicCompletion K) : q.adicCompletion L →* Q.adicCompletion K) a'.1) from rfl]
        exact norm_prod_eq a'.1
      rw [Subgroup.mem_map]
      rw [show (A.subtype (NmA a') : B) = iota (Units.map (Algebra.norm (Q.adicCompletion K) :
          q.adicCompletion L →* Q.adicCompletion K) a'.1) from hkey]
      refine ⟨Units.map (Algebra.norm (Q.adicCompletion K) : q.adicCompletion L →* Q.adicCompletion K) a'.1, ?_, rfl⟩
      rw [Subgroup.mem_inf]
      constructor
      · exact ⟨a'.1, rfl⟩
      · rw [hPker, MonoidHom.mem_ker, unitsValLog_norm Q q hq a'.1]
        have h1 : unitsValLog (q.adicCompletion L) a'.1 = 1 :=
          (unitsValLog_eq_one_iff a'.1).mpr ((mem_adicUnitsVal L q a'.1).mp a'.2)
        rw [h1, one_pow]
    · intro hu
      rw [Subgroup.mem_map] at hu
      obtain ⟨y, hy, rfl⟩ := hu
      rw [Subgroup.mem_inf] at hy
      obtain ⟨hyH, hyP⟩ := hy
      rw [MonoidHom.mem_range] at hyH
      obtain ⟨v, hv⟩ := hyH
      rw [hPker, MonoidHom.mem_ker] at hyP
      have hvA : v ∈ A := by
        rw [mem_adicUnitsVal L q]
        have h2 := congrArg Multiplicative.toAdd (by
          rw [← hv] at hyP; exact hyP : unitsValLog (Q.adicCompletion K)
            (Units.map (Algebra.norm (Q.adicCompletion K) : q.adicCompletion L →* Q.adicCompletion K) v) = 1)
        rw [unitsValLog_norm Q q hq v, toAdd_one, toAdd_pow, nsmul_eq_mul] at h2
        have hfne : f ≠ 0 := (Ideal.inertiaDeg_pos q.asIdeal (NumberField.RingOfIntegers K)).ne'
        have h3 : Multiplicative.toAdd (unitsValLog (q.adicCompletion L) v) = 0 := by
          rcases Int.mul_eq_zero.mp h2 with h4 | h4
          · exact absurd h4 (Int.ofNat_ne_zero.mpr hfne)
          · exact h4
        exact (unitsValLog_eq_one_iff v).mp (Multiplicative.toAdd.injective (by rw [h3, toAdd_one]))
      have hkeyv : ((NmA ⟨v, hvA⟩ : A) : B) = iota (Units.map (Algebra.norm (Q.adicCompletion K) :
          q.adicCompletion L →* Q.adicCompletion K) v) := by
        rw [show iota (Units.map (Algebra.norm (Q.adicCompletion K) :
            q.adicCompletion L →* Q.adicCompletion K) v) =
          Units.map (algebraMap (Q.adicCompletion K) (q.adicCompletion L)).toMonoidHom
            (Units.map (Algebra.norm (Q.adicCompletion K) : q.adicCompletion L →* Q.adicCompletion K) v) from rfl]
        exact norm_prod_eq v
      rw [Subgroup.mem_map]
      refine ⟨NmA ⟨v, hvA⟩, ⟨⟨v, hvA⟩, rfl⟩, ?_⟩
      rw [show (A.subtype (NmA ⟨v, hvA⟩) : B) = iota y from hkeyv.trans (by rw [← hv])]
  have h16 : Nat.card (dA.ker ⧸ NmA.range.subgroupOf dA.ker) =
      Nat.card (P ⧸ (H0 ⊓ P).subgroupOf P) := by
    rw [← Subgroup.index_eq_card (NmA.range.subgroupOf dA.ker),
        ← Subgroup.index_eq_card ((H0 ⊓ P).subgroupOf P)]
    rw [show (NmA.range.subgroupOf dA.ker).index = NmA.range.relIndex dA.ker from rfl,
        show ((H0 ⊓ P).subgroupOf P).index = (H0 ⊓ P).relIndex P from rfl]
    rw [← Subgroup.relIndex_map_map_of_injective (f := A.subtype) NmA.range dA.ker A.subtype_injective]
    rw [← Subgroup.relIndex_map_map_of_injective (f := iota) (H0 ⊓ P) P hiotainj]
    rw [hNrange, hkerA]
  have hmapP : Subgroup.map (unitsValLog (Q.adicCompletion K)) P = ⊥ := by
    rw [hPker, Subgroup.eq_bot_iff_forall]
    intro y hy
    rw [Subgroup.mem_map] at hy
    obtain ⟨z, hz, rfl⟩ := hy
    exact hz
  have hmapH0 : Subgroup.map (unitsValLog (Q.adicCompletion K)) H0 =
      Subgroup.zpowers (Multiplicative.ofAdd (f : ℤ)) := by
    rw [hH0]
    rw [MonoidHom.range_eq_map, Subgroup.map_map]
    ext y
    constructor
    · intro hy
      rw [Subgroup.mem_map] at hy
      obtain ⟨u, -, rfl⟩ := hy
      rw [MonoidHom.comp_apply, unitsValLog_norm Q q hq u]
      exact pow_mem_zpowers_ofAdd _ _
    · intro hy
      rw [Subgroup.mem_zpowers_iff] at hy
      obtain ⟨k, hk⟩ := hy
      obtain ⟨x, hx⟩ := unitsValLog_adicCompletion_surjective L q (Multiplicative.ofAdd k)
      refine Subgroup.mem_map.mpr ⟨x, trivial, ?_⟩
      rw [MonoidHom.comp_apply, unitsValLog_norm Q q hq x, hx, ← hk]
      apply Multiplicative.toAdd.injective
      rw [toAdd_zpow, toAdd_pow, toAdd_ofAdd, toAdd_ofAdd]
      simp only [nsmul_eq_mul]
      ring
  have hIndex_H0P : (H0 ⊔ P).index = f := by
    have hsurj := unitsValLog_adicCompletion_surjective K Q
    refine Commons.GroupTheory.Subgroup.index_eq_of_ker_le_of_map_eq_zpowers
      (unitsValLog (Q.adicCompletion K)) hsurj (H0 ⊔ P) f ?_ ?_
    · rw [Subgroup.map_sup, hmapP, hmapH0]
      simp
    · rw [hPker]
      exact le_sup_right
  have h2nd : H0.relIndex (H0 ⊔ P) = Nat.card (P ⧸ (H0 ⊓ P).subgroupOf P) := by
    show (H0.subgroupOf (H0 ⊔ P)).index = Nat.card (P ⧸ (H0 ⊓ P).subgroupOf P)
    rw [Subgroup.index_eq_card (H0.subgroupOf (H0 ⊔ P))]
    rw [show Nat.card (P ⧸ (H0 ⊓ P).subgroupOf P) =
        Nat.card (↥(P ⊔ H0) ⧸ H0.subgroupOf (P ⊔ H0)) from by
      rw [show (H0 ⊓ P).subgroupOf P = H0.subgroupOf P from by
        ext x; simp [Subgroup.mem_subgroupOf]]
      exact (Nat.card_congr (QuotientGroup.quotientInfEquivProdNormalQuotient P H0).symm.toEquiv).symm]
    rw [sup_comm H0 P]
  have hmain : Nat.card ((Q.adicCompletion K)ˣ ⧸ H0) =
      f * Nat.card (dA.ker ⧸ (NmA.range.subgroupOf dA.ker)) := by
    rw [← Subgroup.index_eq_card H0]
    rw [show H0.index = H0.relIndex (H0 ⊔ P) * (H0 ⊔ P).index from
      (Subgroup.relIndex_mul_index (le_sup_left : H0 ≤ H0 ⊔ P)).symm]
    rw [h2nd, hIndex_H0P, ← h16]
    ring
  rw [hmain, hHerb, hchain]
  ring

end Commons.NumberTheory.NumberField.Completion
