import Mathlib
import Submission.Work.DSTR.l2OddSylowCyclic
import Submission.Work.L2F.Mat2.centralizer_sl2_structure
import Submission.Work.L2F.PSL.trace_lift_ne_zero_and_sq_ne_four
import Submission.Work.L2F.Torus.exists_inverting_conjMat
import Submission.Work.L2F.Torus.mem_centralizer_iff
import Submission.Work.L2F.Torus.ne_conj_negOne_mul
import Submission.Work.L2F.Mat2.sq_eq_one_of_mem_sl

open scoped MatrixGroups
open Matrix

set_option maxHeartbeats 400000

open scoped MatrixGroups
open Matrix

set_option maxHeartbeats 1000000

namespace Work.DSTR.L2CentAux

section Helpers

variable {F : Type*} [Field F]

theorem comap_map_eq_of_ker_le {G H : Type*} [Group G] [Group H] (f : G →* H)
    {C : Subgroup G} (hker : f.ker ≤ C) : Subgroup.comap f (C.map f) = C := by
  rw [Subgroup.comap_map_eq, sup_eq_left]
  exact hker


theorem card_eq_card_map_mul_card_ker {G H : Type*} [Group G] [Group H] (f : G →* H)
    (C : Subgroup G) (hker : f.ker ≤ C) :
    Nat.card C = Nat.card (C.map f) * Nat.card f.ker := by
  have hcard := Subgroup.card_eq_card_quotient_mul_card_subgroup ((f.comp C.subtype).ker)
  have hrange : (f.comp C.subtype).range = C.map f := by
    rw [MonoidHom.range_comp, Subgroup.range_subtype]
  have hquot : Nat.card (↥C ⧸ (f.comp C.subtype).ker) = Nat.card (C.map f) := by
    rw [← hrange]
    exact Nat.card_congr (QuotientGroup.quotientKerEquivRange _).toEquiv
  have hker_eq : Nat.card ((f.comp C.subtype).ker) = Nat.card f.ker := by
    have hcomap : (f.comp C.subtype).ker = Subgroup.comap C.subtype f.ker := by
      ext u
      simp only [MonoidHom.mem_ker, MonoidHom.comp_apply, Subgroup.mem_comap]
    have hmap : Subgroup.map C.subtype (Subgroup.comap C.subtype f.ker) = f.ker := by
      rw [Subgroup.map_comap_eq, Subgroup.range_subtype]
      exact inf_eq_right.mpr hker
    have h := Subgroup.card_map_of_injective (K := Subgroup.comap C.subtype f.ker)
      (f := C.subtype) C.subtype_injective
    rw [hmap] at h
    rw [hcomap]
    exact h.symm
  rw [hquot, hker_eq] at hcard
  exact hcard


theorem comap_normalizer_map_le {G H : Type*} [Group G] [Group H] (f : G →* H)
    (C : Subgroup G) (hker : f.ker ≤ C) :
    Subgroup.comap f (Subgroup.normalizer (C.map f : Set H)) ≤
      Subgroup.normalizer (C : Set G) := by
  intro y hy
  rw [Subgroup.mem_comap] at hy
  rw [Subgroup.mem_normalizer_iff]
  intro c
  have key : f c ∈ C.map f ↔ f y * f c * (f y)⁻¹ ∈ C.map f :=
    Subgroup.mem_normalizer_iff.mp hy (f c)
  have h1 : c ∈ C ↔ f c ∈ C.map f := by
    conv_lhs => rw [← comap_map_eq_of_ker_le f hker]
    exact Subgroup.mem_comap
  have h2 : y * c * y⁻¹ ∈ C ↔ f (y * c * y⁻¹) ∈ C.map f := by
    conv_lhs => rw [← comap_map_eq_of_ker_le f hker]
    exact Subgroup.mem_comap
  rw [h1, h2, show f (y * c * y⁻¹) = f y * f c * (f y)⁻¹ by rw [map_mul, map_mul, map_inv]]
  exact key


theorem normalizer_le_normalizer_centralizer {G : Type*} [Group G] (P : Subgroup G) :
    Subgroup.normalizer (P : Set G) ≤
      Subgroup.normalizer (Subgroup.centralizer (P : Set G) : Set G) := by
  intro g hg
  rw [Subgroup.mem_normalizer_iff] at hg ⊢
  intro x
  rw [Subgroup.mem_centralizer_iff, Subgroup.mem_centralizer_iff]
  constructor
  · intro hx p hp
    have hp' : g⁻¹ * p * g ∈ P := (hg (g⁻¹ * p * g)).mpr (by
      have h : g * (g⁻¹ * p * g) * g⁻¹ = p := by group
      rw [h]; exact hp)
    have h1 : (g⁻¹ * p * g) * x = x * (g⁻¹ * p * g) := hx _ hp'
    calc p * (g * x * g⁻¹) = g * ((g⁻¹ * p * g) * x) * g⁻¹ := by group
      _ = g * (x * (g⁻¹ * p * g)) * g⁻¹ := by rw [h1]
      _ = (g * x * g⁻¹) * p := by group
  · intro hx p hp
    have hp' : g * p * g⁻¹ ∈ P := (hg p).mp hp
    have h1 : (g * p * g⁻¹) * (g * x * g⁻¹) = (g * x * g⁻¹) * (g * p * g⁻¹) := hx _ hp'
    have h2 : g * (p * x) * g⁻¹ = g * (x * p) * g⁻¹ := by
      rwa [show (g * p * g⁻¹) * (g * x * g⁻¹) = g * (p * x) * g⁻¹ by group,
        show (g * x * g⁻¹) * (g * p * g⁻¹) = g * (x * p) * g⁻¹ by group] at h1
    calc p * x = g⁻¹ * (g * (p * x) * g⁻¹) * g := by group
      _ = g⁻¹ * (g * (x * p) * g⁻¹) * g := by rw [h2]
      _ = x * p := by group

/-! ## The map `SL(2,F) → PSL(2,F)` -/

variable {F : Type*} [Field F]


theorem negOne_ne_one (h2 : (2 : F) ≠ 0) : (Work.L2F.negOne F : SL(2, F)) ≠ 1 := by
  intro h
  have h' : (((Work.L2F.negOne F : SL(2, F)) : Matrix (Fin 2) (Fin 2) F)) 0 0 =
      (((1 : SL(2, F)) : Matrix (Fin 2) (Fin 2) F)) 0 0 := by rw [h]
  simp only [Work.L2F.negOne, Matrix.SpecialLinearGroup.coe_one, Matrix.neg_apply,
    Matrix.one_apply_eq] at h'
  have hzero : -(1 : F) + 1 = 0 := neg_add_cancel 1
  rw [h'] at hzero
  have htwo : (2 : F) = 0 := by rw [← one_add_one_eq_two]; exact hzero
  exact h2 htwo


theorem pslMap_ker_eq_zpowers_negOne (h2 : (2 : F) ≠ 0) :
    MonoidHom.ker (Work.PSL2.pslMap F) = Subgroup.zpowers (Work.L2F.negOne F) := by
  apply le_antisymm
  · intro x hx
    rw [MonoidHom.mem_ker] at hx
    rcases (Work.L2F.Mat2.pslMap_eq_one_iff F h2 x).mp hx with h | h
    · rw [h]; exact Subgroup.one_mem _
    · rw [h]; exact Subgroup.mem_zpowers _
  · rw [Subgroup.zpowers_le, MonoidHom.mem_ker]
    exact (Work.L2F.Mat2.pslMap_eq_one_iff F h2 (Work.L2F.negOne F)).mpr (Or.inr rfl)


theorem pslMap_ker_card (h2 : (2 : F) ≠ 0) :
    Nat.card (MonoidHom.ker (Work.PSL2.pslMap F)) = 2 := by
  rw [pslMap_ker_eq_zpowers_negOne h2, Nat.card_zpowers]
  refine orderOf_eq_prime ?_ (negOne_ne_one h2)
  rw [pow_two]
  apply Subtype.ext
  rw [Matrix.SpecialLinearGroup.coe_mul,
    show ((Work.L2F.negOne F : SL(2, F)) : Matrix (Fin 2) (Fin 2) F) = -1 from rfl]
  simp


theorem pslMap_negOne (h2 : (2 : F) ≠ 0) : Work.PSL2.pslMap F (Work.L2F.negOne F) = 1 :=
  (Work.L2F.Mat2.pslMap_eq_one_iff F h2 (Work.L2F.negOne F)).mpr (Or.inr rfl)


theorem ker_le_cent (h2 : (2 : F) ≠ 0) (x : SL(2, F)) :
    MonoidHom.ker (Work.PSL2.pslMap F) ≤ Work.L2F.Torus.cent F x := by
  rw [pslMap_ker_eq_zpowers_negOne h2,
    Work.L2F.Torus.cent_apply]
  rw [Subgroup.zpowers_le]
  exact Subgroup.mem_centralizer_singleton_iff.mpr (by
    apply Subtype.ext
    rw [Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_mul,
      show ((Work.L2F.negOne F : SL(2, F)) : Matrix (Fin 2) (Fin 2) F) = -1 from rfl]
    simp)


theorem pslMap_centralizer_eq (h2 : (2 : F) ≠ 0) (x : SL(2, F))
    (htr : ((x : SL(2, F)) : Matrix (Fin 2) (Fin 2) F).trace ≠ 0) :
    Subgroup.centralizer ({Work.PSL2.pslMap F x} : Set (PSL(2, F))) =
      (Work.L2F.Torus.cent F x).map (Work.PSL2.pslMap F) := by
  apply le_antisymm
  · intro g hg
    obtain ⟨y, hy⟩ := QuotientGroup.mk'_surjective (Subgroup.center (SL(2, F))) g
    have hcomm : Work.PSL2.pslMap F x * g = g * Work.PSL2.pslMap F x :=
      (Subgroup.mem_centralizer_singleton_iff.mp hg).symm
    have hg' : g * Work.PSL2.pslMap F x * g⁻¹ = Work.PSL2.pslMap F x := by
      rw [← hcomm]; group
    have hker : Work.PSL2.pslMap F (y * x * y⁻¹ * x⁻¹) = 1 := by
      have hy' : Work.PSL2.pslMap F y = g := hy
      calc Work.PSL2.pslMap F (y * x * y⁻¹ * x⁻¹)
          = Work.PSL2.pslMap F y * Work.PSL2.pslMap F x * (Work.PSL2.pslMap F y)⁻¹
              * (Work.PSL2.pslMap F x)⁻¹ := by
            rw [map_mul, map_mul, map_mul, map_inv, map_inv]
        _ = g * Work.PSL2.pslMap F x * g⁻¹ * (Work.PSL2.pslMap F x)⁻¹ := by rw [hy']
        _ = Work.PSL2.pslMap F x * (Work.PSL2.pslMap F x)⁻¹ := by rw [hg']
        _ = 1 := mul_inv_cancel _
    rcases (Work.L2F.Mat2.pslMap_eq_one_iff F h2 (y * x * y⁻¹ * x⁻¹)).mp hker with h1 | h1
    · refine Subgroup.mem_map.mpr ⟨y, ?_, hy⟩
      rw [Work.L2F.Torus.cent_apply, Subgroup.mem_centralizer_singleton_iff]
      have h2' : (y * x) * (x * y)⁻¹ = 1 := by
        rw [show (y * x) * (x * y)⁻¹ = y * x * y⁻¹ * x⁻¹ from by group]
        exact h1
      exact mul_inv_eq_one.mp h2'
    · exfalso
      have hconj : y * x * y⁻¹ = Work.L2F.negOne F * x := by
        calc y * x * y⁻¹ = y * x * y⁻¹ * x⁻¹ * x := by group
          _ = Work.L2F.negOne F * x := by rw [h1]
      have htrace : (((y * x * y⁻¹ : SL(2, F)) : Matrix (Fin 2) (Fin 2) F)).trace =
          (((Work.L2F.negOne F * x : SL(2, F)) : Matrix (Fin 2) (Fin 2) F)).trace := by
        rw [hconj]
      rw [Work.L2F.Torus.trace_conj, Work.L2F.Torus.coe_negOne_mul, Matrix.trace_neg] at htrace
      have hsum : ((x : SL(2, F)) : Matrix (Fin 2) (Fin 2) F).trace
          + ((x : SL(2, F)) : Matrix (Fin 2) (Fin 2) F).trace = 0 := by
        nth_rewrite 1 [htrace]
        exact neg_add_cancel _
      have h2t : (2 : F) * ((x : SL(2, F)) : Matrix (Fin 2) (Fin 2) F).trace = 0 := by
        rw [two_mul]; exact hsum
      exact htr ((mul_eq_zero.mp h2t).resolve_left h2)
  · rintro g ⟨c, hc, rfl⟩
    rw [Work.L2F.Torus.cent_apply] at hc
    rw [Subgroup.mem_centralizer_singleton_iff]
    rw [← map_mul, ← map_mul, Subgroup.mem_centralizer_singleton_iff.mp hc]


theorem coe_inv_eq_inv (x : SL(2, F)) :
    (((x⁻¹ : SL(2, F))) : Matrix (Fin 2) (Fin 2) F) =
      (((x : SL(2, F)) : Matrix (Fin 2) (Fin 2) F))⁻¹ := by
  have h : (((x : SL(2, F)) : Matrix (Fin 2) (Fin 2) F))⁻¹ =
      (((x : SL(2, F)) : Matrix (Fin 2) (Fin 2) F)).adjugate :=
    Matrix.inv_eq_right_inv
      (by rw [Matrix.mul_adjugate, Matrix.SpecialLinearGroup.det_coe, one_smul])
  rw [h, Matrix.SpecialLinearGroup.coe_inv]


theorem conj_mem_cent (h2 : (2 : F) ≠ 0) {x u c : SL(2, F)}
    (hD : Work.L2F.Torus.disc F x ≠ 0)
    (hu : Work.L2F.Torus.conjNeg F u (Work.L2F.Torus.conjMat F x))
    (hc : c ∈ Work.L2F.Torus.cent F x) :
    u * c * u⁻¹ ∈ Work.L2F.Torus.cent F x := by
  obtain ⟨a, b, hab, hceq⟩ := (Work.L2F.Torus.mem_centralizer_iff F h2 x c hD).mp hc
  rw [Work.L2F.Torus.mem_centralizer_iff F h2 x (u * c * u⁻¹) hD]
  refine ⟨a, -b, by rw [neg_sq]; exact hab, ?_⟩
  have hcoe : (((u * c * u⁻¹ : SL(2, F))) : Matrix (Fin 2) (Fin 2) F) =
      ((u : SL(2, F)) : Matrix (Fin 2) (Fin 2) F) *
        ((c : SL(2, F)) : Matrix (Fin 2) (Fin 2) F) *
        (((u⁻¹ : SL(2, F))) : Matrix (Fin 2) (Fin 2) F) := by
    rw [Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_mul,
      Matrix.SpecialLinearGroup.coe_inv]
  have h1 : ((u : SL(2, F)) : Matrix (Fin 2) (Fin 2) F) *
      (((u⁻¹ : SL(2, F))) : Matrix (Fin 2) (Fin 2) F) = 1 := by
    rw [← Matrix.SpecialLinearGroup.coe_mul, mul_inv_cancel, Matrix.SpecialLinearGroup.coe_one]
  have h2' : ((u : SL(2, F)) : Matrix (Fin 2) (Fin 2) F) *
      Work.L2F.Torus.conjMat F x *
      (((u⁻¹ : SL(2, F))) : Matrix (Fin 2) (Fin 2) F) = -(Work.L2F.Torus.conjMat F x) := by
    rw [coe_inv_eq_inv]; exact hu
  rw [hcoe, hceq]
  simp only [Matrix.mul_add, Matrix.mul_smul, Matrix.mul_smul, Matrix.mul_one,
    Matrix.add_mul, Matrix.smul_mul, Matrix.smul_mul, h1, h2', smul_neg, neg_smul]


theorem conj_mem_normalizer [Fintype F] (h2 : (2 : F) ≠ 0) {x u : SL(2, F)}
    (hD : Work.L2F.Torus.disc F x ≠ 0)
    (hu : Work.L2F.Torus.conjNeg F u (Work.L2F.Torus.conjMat F x)) :
    u ∈ Subgroup.normalizer (Work.L2F.Torus.cent F x : Set (SL(2, F))) := by
  rw [Subgroup.mem_normalizer_iff_map_conj_eq]
  have hle : Subgroup.map (MulAut.conj u).toMonoidHom (Work.L2F.Torus.cent F x) ≤
      Work.L2F.Torus.cent F x := by
    intro y hy
    obtain ⟨c, hc, rfl⟩ := Subgroup.mem_map.mp hy
    exact conj_mem_cent h2 hD hu hc
  have hcard : Nat.card (Subgroup.map (MulAut.conj u).toMonoidHom
      (Work.L2F.Torus.cent F x)) = Nat.card (Work.L2F.Torus.cent F x) :=
    Subgroup.card_map_of_injective (f := (MulAut.conj u).toMonoidHom) (MulAut.conj u).injective
  exact Subgroup.eq_of_le_of_card_ge hle (le_of_eq hcard.symm)


theorem conjNeg_notMem_cent (h2 : (2 : F) ≠ 0) {x u : SL(2, F)}
    (hD : Work.L2F.Torus.disc F x ≠ 0)
    (hu : Work.L2F.Torus.conjNeg F u (Work.L2F.Torus.conjMat F x)) :
    u ∉ Work.L2F.Torus.cent F x := by
  intro humem
  have hcomm : u * x = x * u := by
    rw [Work.L2F.Torus.cent_apply] at humem
    exact Subgroup.mem_centralizer_singleton_iff.mp humem
  have hMX : ((u : SL(2, F)) : Matrix (Fin 2) (Fin 2) F) *
      ((x : SL(2, F)) : Matrix (Fin 2) (Fin 2) F) =
      ((x : SL(2, F)) : Matrix (Fin 2) (Fin 2) F) *
      ((u : SL(2, F)) : Matrix (Fin 2) (Fin 2) F) := by
    rw [← Matrix.SpecialLinearGroup.coe_mul, ← Matrix.SpecialLinearGroup.coe_mul, hcomm]
  have hcommW : ((u : SL(2, F)) : Matrix (Fin 2) (Fin 2) F) *
      Work.L2F.Torus.conjMat F x =
      Work.L2F.Torus.conjMat F x * ((u : SL(2, F)) : Matrix (Fin 2) (Fin 2) F) := by
    rw [Work.L2F.Torus.conjMat_apply, Matrix.mul_sub, Matrix.mul_smul, Matrix.mul_smul,
      Matrix.mul_one, Matrix.sub_mul, Matrix.smul_mul, Matrix.smul_mul, Matrix.one_mul, hMX]
  have hu' : (((u⁻¹ : SL(2, F))) : Matrix (Fin 2) (Fin 2) F) *
      ((u : SL(2, F)) : Matrix (Fin 2) (Fin 2) F) = 1 := by
    rw [← Matrix.SpecialLinearGroup.coe_mul, inv_mul_cancel, Matrix.SpecialLinearGroup.coe_one]
  have hMW : ((u : SL(2, F)) : Matrix (Fin 2) (Fin 2) F) *
      Work.L2F.Torus.conjMat F x * (((u⁻¹ : SL(2, F))) : Matrix (Fin 2) (Fin 2) F) =
      -(Work.L2F.Torus.conjMat F x) := by
    rw [coe_inv_eq_inv]; exact hu
  have hkey : ((u : SL(2, F)) : Matrix (Fin 2) (Fin 2) F) * Work.L2F.Torus.conjMat F x =
      -(Work.L2F.Torus.conjMat F x * ((u : SL(2, F)) : Matrix (Fin 2) (Fin 2) F)) := by
    calc ((u : SL(2, F)) : Matrix (Fin 2) (Fin 2) F) * Work.L2F.Torus.conjMat F x
        = ((u : SL(2, F)) : Matrix (Fin 2) (Fin 2) F) * Work.L2F.Torus.conjMat F x *
            ((((u⁻¹ : SL(2, F))) : Matrix (Fin 2) (Fin 2) F) *
              ((u : SL(2, F)) : Matrix (Fin 2) (Fin 2) F)) := by rw [hu', Matrix.mul_one]
      _ = (((u : SL(2, F)) : Matrix (Fin 2) (Fin 2) F) * Work.L2F.Torus.conjMat F x *
            (((u⁻¹ : SL(2, F))) : Matrix (Fin 2) (Fin 2) F)) *
              ((u : SL(2, F)) : Matrix (Fin 2) (Fin 2) F) := by noncomm_ring
      _ = (-(Work.L2F.Torus.conjMat F x)) * ((u : SL(2, F)) : Matrix (Fin 2) (Fin 2) F) := by
            rw [hMW]
      _ = -(Work.L2F.Torus.conjMat F x * ((u : SL(2, F)) : Matrix (Fin 2) (Fin 2) F)) := by
            rw [Matrix.neg_mul]
  have hzero : Work.L2F.Torus.conjMat F x * ((u : SL(2, F)) : Matrix (Fin 2) (Fin 2) F) = 0 := by
    have heq : Work.L2F.Torus.conjMat F x * ((u : SL(2, F)) : Matrix (Fin 2) (Fin 2) F) =
        -(Work.L2F.Torus.conjMat F x * ((u : SL(2, F)) : Matrix (Fin 2) (Fin 2) F)) :=
      hcommW.symm.trans hkey
    have hsum : Work.L2F.Torus.conjMat F x * ((u : SL(2, F)) : Matrix (Fin 2) (Fin 2) F) +
        Work.L2F.Torus.conjMat F x * ((u : SL(2, F)) : Matrix (Fin 2) (Fin 2) F) = 0 := by
      nth_rewrite 1 [heq]
      exact neg_add_cancel _
    have h2s : (2 : F) • (Work.L2F.Torus.conjMat F x *
        ((u : SL(2, F)) : Matrix (Fin 2) (Fin 2) F)) = 0 := by
      rw [two_smul]; exact hsum
    exact (smul_eq_zero.mp h2s).resolve_left h2
  refine Work.L2F.Torus.conjMat_ne_zero F x hD ?_
  calc Work.L2F.Torus.conjMat F x
      = Work.L2F.Torus.conjMat F x * 1 := (Matrix.mul_one _).symm
    _ = Work.L2F.Torus.conjMat F x *
          (((u : SL(2, F)) : Matrix (Fin 2) (Fin 2) F) * (((u⁻¹ : SL(2, F))) :
            Matrix (Fin 2) (Fin 2) F)) := by
          rw [← Matrix.SpecialLinearGroup.coe_mul, mul_inv_cancel,
            Matrix.SpecialLinearGroup.coe_one]
    _ = (Work.L2F.Torus.conjMat F x * ((u : SL(2, F)) : Matrix (Fin 2) (Fin 2) F)) *
          (((u⁻¹ : SL(2, F))) : Matrix (Fin 2) (Fin 2) F) := by noncomm_ring
    _ = 0 := by rw [hzero, Matrix.zero_mul]


end Helpers

/-! ## The main theorem -/

/-- Images of normalizers normalize images. -/
theorem map_normalizer_le {G H : Type*} [Group G] [Group H] (f : G →* H) (C : Subgroup G) :
    Subgroup.map f (Subgroup.normalizer (C : Set G)) ≤
      Subgroup.normalizer (C.map f : Set H) := by
  rintro y ⟨c, hc, rfl⟩
  have hc' := Subgroup.mem_normalizer_iff.mp hc
  refine Subgroup.mem_normalizer_iff.mpr ?_
  intro h
  constructor
  · intro hh
    obtain ⟨d, hd, rfl⟩ := Subgroup.mem_map.mp hh
    exact Subgroup.mem_map.mpr ⟨c * d * c⁻¹, (hc' d).mp hd, by rw [map_mul, map_mul, map_inv]⟩
  · intro hh
    obtain ⟨d, hd, hdc⟩ := Subgroup.mem_map.mp hh
    refine Subgroup.mem_map.mpr ⟨c⁻¹ * d * c, (hc' (c⁻¹ * d * c)).mpr ?_, ?_⟩
    · have h : c * (c⁻¹ * d * c) * c⁻¹ = d := by group
      rw [h]; exact hd
    · rw [map_mul, map_mul, map_inv, hdc]; group

/-- The centralizer of `z` and of the subgroup it generates agree. -/
theorem centralizer_zpowers {G : Type*} [Group G] (z : G) :
    Subgroup.centralizer (Subgroup.zpowers z : Set G) =
      Subgroup.centralizer ({z} : Set G) := by
  ext x
  rw [Subgroup.mem_centralizer_iff, Subgroup.mem_centralizer_singleton_iff]
  constructor
  · intro h
    exact (h z (Subgroup.mem_zpowers z)).symm
  · intro h y hy
    obtain ⟨n, rfl⟩ := Subgroup.mem_zpowers_iff.mp hy
    exact (Commute.zpow_right (a := x) (b := z) h n).symm

/-- In a finite cyclic group, subgroups of equal cardinality are equal. -/
theorem cyc_eq_of_card_eq {G : Type*} [Group G] [IsCyclic G] [Finite G]
    {A B : Subgroup G} (h : Nat.card A = Nat.card B) : A = B := by
  obtain ⟨g, hg⟩ := IsCyclic.exists_generator (α := G)
  have hgt : Subgroup.zpowers g = ⊤ := (Subgroup.eq_top_iff' (Subgroup.zpowers g)).mpr hg
  obtain ⟨i, hi⟩ := Subgroup.exists_zpowers_eq_of_zpowers_eq_top hgt A
  obtain ⟨j, hj⟩ := Subgroup.exists_zpowers_eq_of_zpowers_eq_top hgt B
  rw [← hi, ← hj] at h ⊢
  rw [Subgroup.zpowers_eq_zpowers_iff']
  have h1 : Nat.card (Subgroup.zpowers (g ^ i)) * (i.gcd (orderOf g)) = Nat.card G := by
    rw [← Subgroup.index_zpowers_zpow hgt i]
    exact Subgroup.card_mul_index _
  have h2 : Nat.card (Subgroup.zpowers (g ^ j)) * (j.gcd (orderOf g)) = Nat.card G := by
    rw [← Subgroup.index_zpowers_zpow hgt j]
    exact Subgroup.card_mul_index _
  have hpos : 0 < Nat.card (Subgroup.zpowers (g ^ i)) := by
    rw [Nat.card_zpowers]
    exact orderOf_pos _
  apply Nat.mul_left_cancel hpos
  rw [h1, h, h2]

/-- A subgroup has at most the cardinality of an overgroup. -/
theorem natCard_le_of_le {G : Type*} [Group G] [Finite G] {H K : Subgroup G} (h : H ≤ K) :
    Nat.card H ≤ Nat.card K := by
  haveI : Nonempty ↥K := ⟨1, K.one_mem⟩
  exact Nat.le_of_dvd Nat.card_pos (Subgroup.card_dvd_of_le h)

section Main

theorem PSLOddNormalizerCard {p k : ℕ} [Fact p.Prime] (hp : Odd p) (hk : 5 ≤ p ^ k)
    (r : ℕ) [Fact r.Prime] (hr2 : r ≠ 2) (hrp : r ≠ p)
    (P : Subgroup (PSL(2, GaloisField p k))) (hP : IsPGroup r P) (hne : P ≠ ⊥) :
    Nat.card (Subgroup.normalizer (P : Set (PSL(2, GaloisField p k)))) = p ^ k - 1 ∨
      Nat.card (Subgroup.normalizer (P : Set (PSL(2, GaloisField p k)))) = p ^ k + 1 := by
  classical
  have hk0 : k ≠ 0 := by rintro rfl; simp at hk
  haveI : Fintype (GaloisField p k) := Fintype.ofFinite _
  have hcardF : Nat.card (GaloisField p k) = p ^ k := GaloisField.card p k hk0
  have h2 : (2 : GaloisField p k) ≠ 0 := by
    intro h
    have hdiv : p ∣ 2 := (CharP.cast_eq_zero_iff (GaloisField p k) p 2).mp h
    have hle : p ≤ 2 := Nat.le_of_dvd (by norm_num) hdiv
    have hge : 2 ≤ p := (Fact.out : Nat.Prime p).two_le
    have hp2 : p = 2 := le_antisymm hle hge
    rw [hp2] at hp
    exact (by decide : ¬ Odd 2) hp
  -- `P` is cyclic, and `z` generates it
  obtain ⟨Q, hPQ⟩ := IsPGroup.exists_le_sylow hP
  have hcycQ : IsCyclic ↥(Q : Subgroup (PSL(2, GaloisField p k))) :=
    Work.DSTR.l2OddSylowCyclic p k hp hk r hr2 hrp Q
  haveI : IsCyclic ↥(P.subgroupOf (Q : Subgroup (PSL(2, GaloisField p k)))) := inferInstance
  haveI : IsCyclic ↥P :=
    (MulEquiv.isCyclic (Subgroup.subgroupOfEquivOfLe hPQ)).mp inferInstance
  obtain ⟨p0, hp0gen⟩ := IsCyclic.exists_generator (α := ↥P)
  set z : PSL(2, GaloisField p k) := (p0 : PSL(2, GaloisField p k)) with hzdef
  have hp0top : Subgroup.zpowers p0 = ⊤ :=
    (Subgroup.eq_top_iff' (Subgroup.zpowers p0)).mpr hp0gen
  have htop_mp : (⊤ : Subgroup ↥P).map P.subtype = P := by
    rw [← MonoidHom.range_eq_map, Subgroup.range_subtype]
  have hzpow : Subgroup.zpowers z = P := by
    have h1 : Subgroup.zpowers ((p0 : ↥P) : PSL(2, GaloisField p k)) =
        (Subgroup.zpowers p0).map P.subtype := (MonoidHom.map_zpowers P.subtype p0).symm
    rw [hzdef, h1, hp0top, htop_mp]
  have hPz : P = Subgroup.zpowers z := hzpow.symm
  have hz1 : z ≠ 1 := by
    intro h
    refine hne ?_
    rw [hPz, h, Subgroup.zpowers_one_eq_bot]
  -- the order of `z`
  obtain ⟨m, hm⟩ := hP p0
  have hdvd : orderOf z ∣ r ^ m := by
    rw [hzdef, Subgroup.orderOf_coe]
    exact orderOf_dvd_of_pow_eq_one hm
  have hrod : Odd r := (Fact.out : Nat.Prime r).odd_of_ne_two hr2
  have hodd_z : Odd (orderOf z) := Odd.of_dvd_nat (hrod.pow (n := m)) hdvd
  have hcopf : ¬ p ∣ orderOf z := by
    intro hd
    have hpr : p ∣ r := (Fact.out : Nat.Prime p).dvd_of_dvd_pow (dvd_trans hd hdvd)
    exact hrp ((Nat.Prime.dvd_iff_eq (Fact.out : Nat.Prime r)
      (Fact.out : Nat.Prime p).ne_one).mp hpr)
  -- a lift to `SL(2, k)` and the structure of its centralizer
  obtain ⟨x, hx⟩ := QuotientGroup.mk'_surjective (Subgroup.center (SL(2, GaloisField p k))) z
  have hx' : Work.PSL2.pslMap (GaloisField p k) x = z := hx
  obtain ⟨htr0, htr4⟩ :=
    Work.L2F.PSL.trace_lift_ne_zero_and_sq_ne_four hp z hz1 hodd_z hcopf x hx'
  obtain ⟨hcycC, hcardC, hnormle⟩ :=
    Work.L2F.Mat2.centralizer_sl2_structure (GaloisField p k) h2 x htr4
  have hdisc : Work.L2F.Torus.disc (GaloisField p k) x ≠ 0 := by
    rw [Work.L2F.Torus.disc_apply]
    exact sub_ne_zero.mpr htr4
  obtain ⟨w, hw1, hw2⟩ :=
    Work.L2F.Torus.exists_inverting_conjMat (GaloisField p k) h2 x hdisc
  -- transfer to `PSL`
  have hCeq : Subgroup.centralizer ({z} : Set (PSL(2, GaloisField p k))) =
      (Work.L2F.Torus.cent (GaloisField p k) x).map (Work.PSL2.pslMap (GaloisField p k)) := by
    have hset : ({Work.PSL2.pslMap (GaloisField p k) x} : Set (PSL(2, GaloisField p k))) =
        {z} := by rw [hx']
    rw [← hset]
    exact pslMap_centralizer_eq h2 x htr0
  have hker_le := ker_le_cent h2 x
  have hker_card := pslMap_ker_card h2
  have hunit : (Work.PSL2.pslMap (GaloisField p k)).range = ⊤ :=
    MonoidHom.range_eq_top.mpr (QuotientGroup.mk'_surjective _)
  have hcardCent : 2 * Nat.card (Subgroup.centralizer ({z} : Set (PSL(2, GaloisField p k)))) =
      Nat.card (Work.L2F.Torus.cent (GaloisField p k) x) := by
    have h := card_eq_card_map_mul_card_ker (Work.PSL2.pslMap (GaloisField p k))
      (Work.L2F.Torus.cent (GaloisField p k) x) hker_le
    rw [hker_card, ← hCeq] at h
    rw [h]
    ring
  -- `w` normalizes `C_{SL}(x)` but is not in it
  have hwN : w ∈ Subgroup.normalizer (Work.L2F.Torus.cent (GaloisField p k) x :
      Set (SL(2, GaloisField p k))) := conj_mem_normalizer h2 hdisc hw2
  have hwNotC : w ∉ Work.L2F.Torus.cent (GaloisField p k) x :=
    conjNeg_notMem_cent h2 hdisc hw2
  -- `π w` normalizes `C_{PSL}(z)` but is not in it
  have hwMap : Work.PSL2.pslMap (GaloisField p k) w ∈
      Subgroup.normalizer (Subgroup.centralizer ({z} : Set (PSL(2, GaloisField p k))) :
        Set (PSL(2, GaloisField p k))) := by
    rw [hCeq]
    exact map_normalizer_le _ _ (Subgroup.mem_map.mpr ⟨w, hwN, rfl⟩)
  have hwNotCG : Work.PSL2.pslMap (GaloisField p k) w ∉
      Subgroup.centralizer ({z} : Set (PSL(2, GaloisField p k))) := by
    intro hmem
    rw [hCeq] at hmem
    obtain ⟨c, hc, hce⟩ := Subgroup.mem_map.mp hmem
    have hker : w * c⁻¹ ∈ MonoidHom.ker (Work.PSL2.pslMap (GaloisField p k)) := by
      rw [MonoidHom.mem_ker, map_mul, map_inv, hce, mul_inv_cancel]
    have h1 : w * c⁻¹ ∈ Work.L2F.Torus.cent (GaloisField p k) x := hker_le hker
    have h2' : w = (w * c⁻¹) * c := by group
    exact hwNotC (by rw [h2']; exact Subgroup.mul_mem _ h1 hc)
  -- the upper bound on `|N_G(C_G(z))|`
  have hupper : Nat.card (Subgroup.normalizer
      (Subgroup.centralizer ({z} : Set (PSL(2, GaloisField p k))) :
        Set (PSL(2, GaloisField p k)))) ≤ Nat.card (Work.L2F.Torus.cent (GaloisField p k) x) := by
    have hcomap : Subgroup.comap (Work.PSL2.pslMap (GaloisField p k))
        (Subgroup.normalizer (Subgroup.centralizer ({z} : Set (PSL(2, GaloisField p k))) :
          Set (PSL(2, GaloisField p k)))) ≤
        Subgroup.normalizer (Work.L2F.Torus.cent (GaloisField p k) x :
          Set (SL(2, GaloisField p k))) := by
      rw [hCeq]
      exact comap_normalizer_map_le _ _ hker_le
    have hker_leN : MonoidHom.ker (Work.PSL2.pslMap (GaloisField p k)) ≤
        Subgroup.comap (Work.PSL2.pslMap (GaloisField p k))
          (Subgroup.normalizer (Subgroup.centralizer ({z} : Set (PSL(2, GaloisField p k))) :
            Set (PSL(2, GaloisField p k)))) := by
      intro y hy
      rw [Subgroup.mem_comap, MonoidHom.mem_ker] at *
      rw [hy]
      exact Subgroup.one_mem _
    have hmapcomap : Subgroup.map (Work.PSL2.pslMap (GaloisField p k))
        (Subgroup.comap (Work.PSL2.pslMap (GaloisField p k))
          (Subgroup.normalizer (Subgroup.centralizer ({z} : Set (PSL(2, GaloisField p k))) :
            Set (PSL(2, GaloisField p k))))) =
        Subgroup.normalizer (Subgroup.centralizer ({z} : Set (PSL(2, GaloisField p k))) :
          Set (PSL(2, GaloisField p k))) := by
      rw [Subgroup.map_comap_eq, hunit, top_inf_eq]
    have hcard1 : Nat.card (Subgroup.comap (Work.PSL2.pslMap (GaloisField p k))
        (Subgroup.normalizer (Subgroup.centralizer ({z} : Set (PSL(2, GaloisField p k))) :
          Set (PSL(2, GaloisField p k))))) =
        2 * Nat.card (Subgroup.normalizer
          (Subgroup.centralizer ({z} : Set (PSL(2, GaloisField p k))) :
            Set (PSL(2, GaloisField p k)))) := by
      have h := card_eq_card_map_mul_card_ker (Work.PSL2.pslMap (GaloisField p k))
        (Subgroup.comap (Work.PSL2.pslMap (GaloisField p k))
          (Subgroup.normalizer (Subgroup.centralizer ({z} : Set (PSL(2, GaloisField p k))) :
            Set (PSL(2, GaloisField p k))))) hker_leN
      rw [hmapcomap, hker_card] at h
      rw [h]
      ring
    have hmono : 2 * Nat.card (Subgroup.normalizer
        (Subgroup.centralizer ({z} : Set (PSL(2, GaloisField p k))) :
          Set (PSL(2, GaloisField p k)))) ≤
        2 * Nat.card (Work.L2F.Torus.cent (GaloisField p k) x) := by
      rw [← hcard1]
      exact le_trans (natCard_le_of_le hcomap) hnormle
    exact Nat.le_of_mul_le_mul_left hmono (by norm_num)
  -- the lower bound on `|N_G(C_G(z))|`
  have hlower : 2 * Nat.card (Subgroup.centralizer ({z} : Set (PSL(2, GaloisField p k)))) ≤
      Nat.card (Subgroup.normalizer (Subgroup.centralizer ({z} :
        Set (PSL(2, GaloisField p k))) : Set (PSL(2, GaloisField p k)))) := by
    set N1 : Subgroup (PSL(2, GaloisField p k)) := Subgroup.normalizer
      (Subgroup.centralizer ({z} : Set (PSL(2, GaloisField p k))) :
        Set (PSL(2, GaloisField p k))) with hN1
    have hπw_mem : Work.PSL2.pslMap (GaloisField p k) w ∈ N1 := by
      rw [hN1]; exact hwMap
    have hsub_ne_top : (Subgroup.centralizer ({z} : Set (PSL(2, GaloisField p k)))).subgroupOf N1
        ≠ ⊤ := by
      intro htop
      have hmem : (⟨Work.PSL2.pslMap (GaloisField p k) w, hπw_mem⟩ : ↥N1) ∈
          (Subgroup.centralizer ({z} : Set (PSL(2, GaloisField p k)))).subgroupOf N1 := by
        rw [htop]; exact Subgroup.mem_top _
      exact hwNotCG (Subgroup.mem_subgroupOf.mp hmem)
    haveI : Finite (↥N1 ⧸
        (Subgroup.centralizer ({z} : Set (PSL(2, GaloisField p k)))).subgroupOf N1) := inferInstance
    have hidx : 1 < ((Subgroup.centralizer ({z} : Set (PSL(2, GaloisField p k)))).subgroupOf
        N1).index := Subgroup.one_lt_index_of_ne_top hsub_ne_top
    have hcardmul := Subgroup.card_mul_index
      ((Subgroup.centralizer ({z} : Set (PSL(2, GaloisField p k)))).subgroupOf N1)
    have hcardsub : Nat.card
        ((Subgroup.centralizer ({z} : Set (PSL(2, GaloisField p k)))).subgroupOf N1) =
        Nat.card (Subgroup.centralizer ({z} : Set (PSL(2, GaloisField p k)))) :=
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe (Subgroup.le_normalizer)).toEquiv
    rw [hcardsub] at hcardmul
    calc 2 * Nat.card (Subgroup.centralizer ({z} : Set (PSL(2, GaloisField p k))))
        ≤ Nat.card (Subgroup.centralizer ({z} : Set (PSL(2, GaloisField p k)))) *
            ((Subgroup.centralizer ({z} : Set (PSL(2, GaloisField p k)))).subgroupOf N1).index := by
          rw [mul_comm 2]
          exact Nat.mul_le_mul_left _ (Nat.succ_le_of_lt hidx)
      _ = Nat.card N1 := hcardmul
      _ = Nat.card (Subgroup.normalizer (Subgroup.centralizer ({z} :
          Set (PSL(2, GaloisField p k))) : Set (PSL(2, GaloisField p k)))) := by rw [hN1]
  have hNGeq : Nat.card (Subgroup.normalizer (Subgroup.centralizer ({z} :
      Set (PSL(2, GaloisField p k))) : Set (PSL(2, GaloisField p k)))) =
      Nat.card (Work.L2F.Torus.cent (GaloisField p k) x) := by
    refine le_antisymm hupper ?_
    rw [← hcardCent]
    exact hlower
  -- `N_G(P) = N_G(C_G(z))`
  have hNP : Subgroup.normalizer (P : Set (PSL(2, GaloisField p k))) =
      Subgroup.normalizer (Subgroup.centralizer ({z} : Set (PSL(2, GaloisField p k))) :
        Set (PSL(2, GaloisField p k))) := by
    haveI hcycCG : IsCyclic ↥(Subgroup.centralizer ({z} :
        Set (PSL(2, GaloisField p k)))) := by
      rw [hCeq]
      haveI hcycT : IsCyclic ↥(Work.L2F.Torus.cent (GaloisField p k) x) := hcycC
      have hrange : ((Work.PSL2.pslMap (GaloisField p k)).comp
          (Work.L2F.Torus.cent (GaloisField p k) x).subtype).range =
          (Work.L2F.Torus.cent (GaloisField p k) x).map
            (Work.PSL2.pslMap (GaloisField p k)) := by
        rw [MonoidHom.range_comp, Subgroup.range_subtype]
      rw [← hrange]
      exact (MulEquiv.isCyclic (QuotientGroup.quotientKerEquivRange
        ((Work.PSL2.pslMap (GaloisField p k)).comp
          (Work.L2F.Torus.cent (GaloisField p k) x).subtype))).mp
        (isCyclic_of_surjective _ (QuotientGroup.mk'_surjective _))
    apply le_antisymm
    · have h := normalizer_le_normalizer_centralizer P
      rw [hPz] at h
      rw [centralizer_zpowers z] at h
      rw [hPz]
      exact h
    · intro u hu
      rw [Subgroup.mem_normalizer_iff_map_conj_eq]
      set Cg : Subgroup (PSL(2, GaloisField p k)) :=
        Subgroup.centralizer ({z} : Set (PSL(2, GaloisField p k))) with hCg
      have hzmem : z ∈ Cg := Subgroup.mem_centralizer_singleton_iff.mpr rfl
      have huz : u * z * u⁻¹ ∈ Cg := by
        rw [hCg] at hu ⊢
        exact (Subgroup.mem_normalizer_iff.mp hu z).mp hzmem
      have horder : orderOf (⟨u * z * u⁻¹, huz⟩ : ↥Cg) = orderOf (⟨z, hzmem⟩ : ↥Cg) := by
        rw [← Subgroup.orderOf_coe (⟨u * z * u⁻¹, huz⟩ : ↥Cg),
          ← Subgroup.orderOf_coe (⟨z, hzmem⟩ : ↥Cg)]
        exact orderOf_injective (MulAut.conj u).toMonoidHom (MulAut.conj u).injective z
      have heq := cyc_eq_of_card_eq
        (A := Subgroup.zpowers (⟨z, hzmem⟩ : ↥Cg))
        (B := Subgroup.zpowers (⟨u * z * u⁻¹, huz⟩ : ↥Cg))
        (by rw [Nat.card_zpowers, Nat.card_zpowers, horder])
      have hG : Subgroup.zpowers (u * z * u⁻¹) = Subgroup.zpowers z := by
        have h1 : Subgroup.map Cg.subtype (Subgroup.zpowers (⟨u * z * u⁻¹, huz⟩ : ↥Cg)) =
            Subgroup.zpowers (u * z * u⁻¹) := MonoidHom.map_zpowers _ _
        have h2 : Subgroup.map Cg.subtype (Subgroup.zpowers (⟨z, hzmem⟩ : ↥Cg)) =
            Subgroup.zpowers z := MonoidHom.map_zpowers _ _
        rw [← h1, ← h2, heq]
      conv_lhs => rw [hPz]
      rw [MonoidHom.map_zpowers]
      conv_rhs => rw [hPz]
      exact hG
  rw [hNP, hNGeq]
  rcases hcardC with hc | hc
  · left
    rw [← hcardF]; exact hc
  · right
    rw [← hcardF]; exact hc

end Main

end Work.DSTR.L2CentAux
