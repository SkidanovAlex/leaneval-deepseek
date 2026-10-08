import Mathlib
import Submission.Work.L2F.Defs
import Submission.Work.L2F.Mat2.centralizer_sq_neg_one
import Submission.Work.L2F.Mat2.centralizer_sq_neg_one_card
import Submission.Work.L2F.Mat2.exists_conj_z
import Submission.Work.L2F.Mat2.pslMap_eq_one_iff
import Submission.Work.L2F.Conic.circle_card
import Submission.Work.L2F.Conic.circle_eq_hypTorus
import Submission.Work.L2F.Conic.hypTorus_cyclic
import Submission.Work.L2F.Dihedral.mulEquiv_dihedral_of_cyclic_index_two
import Submission.Work.L2F.Involution.mem_normalizer_zpowers
import Submission.Work.L2F.Involution.centralizer_eq_image_normalizer
import Submission.Work.L2F.Involution.inverts_of_conj
import Submission.Work.L2F.Involution.exists_inverting

open scoped MatrixGroups
open Matrix

namespace Work.L2F.PSL

/-! ## Elementary lemmas about `SL(2,F)` in odd characteristic -/

/-- `-1 ≠ 1` in `SL(2,F)` when `(2 : F) ≠ 0`. -/
private lemma negOne_ne_one (F : Type*) [Field F] (h2 : (2 : F) ≠ 0) :
    (Work.L2F.negOne F : Matrix.SpecialLinearGroup (Fin 2) F) ≠ 1 := by
  intro h
  have h1 : (-1 : F) = 1 := by
    have hh := congrArg (fun t : Matrix.SpecialLinearGroup (Fin 2) F =>
      ((t : Matrix (Fin 2) (Fin 2) F)) 0 0) h
    simpa [Work.L2F.negOne] using hh
  have hz : (1 : F) + 1 = 0 := by
    have hh : (-1 : F) + 1 = 0 := by ring
    rwa [h1] at hh
  have h2' : (2 : F) = 0 := by
    rw [← one_add_one_eq_two]
    exact hz
  exact h2 h2'

/-- `x ≠ -x` in `SL(2,F)`, i.e. `x ≠ negOne F * x`, when `(2 : F) ≠ 0`. -/
private lemma ne_negOne_mul (F : Type*) [Field F] (h2 : (2 : F) ≠ 0)
    (x : Matrix.SpecialLinearGroup (Fin 2) F) : x ≠ Work.L2F.negOne F * x := by
  intro h
  have h1 : (1 : Matrix.SpecialLinearGroup (Fin 2) F) = Work.L2F.negOne F := by
    have hh : x * x⁻¹ = (Work.L2F.negOne F * x) * x⁻¹ := congrArg (· * x⁻¹) h
    rw [mul_inv_cancel, mul_assoc, mul_inv_cancel, mul_one] at hh
    exact hh
  exact negOne_ne_one F h2 h1.symm

/-! ## Matrix identities for conjugation by an invertible matrix -/

section Mat

variable {F : Type*} [Field F]

/-- `(P A P⁻¹)(P B P⁻¹) = P (A B) P⁻¹`. -/
private lemma conj_mul_mat (P : Matrix (Fin 2) (Fin 2) F) (hP : IsUnit P.det)
    (A B : Matrix (Fin 2) (Fin 2) F) :
    (P * A * P⁻¹) * (P * B * P⁻¹) = P * (A * B) * P⁻¹ := by
  simp only [Matrix.mul_assoc]
  rw [← Matrix.mul_assoc P⁻¹ P (B * P⁻¹), Matrix.nonsing_inv_mul P hP, Matrix.one_mul,
    ← Matrix.mul_assoc A B P⁻¹]

/-- `(P⁻¹ A P)(P⁻¹ B P) = P⁻¹ (A B) P`. -/
private lemma inv_conj_mul_mat (P : Matrix (Fin 2) (Fin 2) F) (hP : IsUnit P.det)
    (A B : Matrix (Fin 2) (Fin 2) F) :
    (P⁻¹ * A * P) * (P⁻¹ * B * P) = P⁻¹ * (A * B) * P := by
  simp only [Matrix.mul_assoc]
  rw [← Matrix.mul_assoc P P⁻¹ (B * P), Matrix.mul_nonsing_inv P hP, Matrix.one_mul,
    ← Matrix.mul_assoc A B P]

/-- `P⁻¹ (P A P⁻¹) P = A`. -/
private lemma inv_conj_conj (P : Matrix (Fin 2) (Fin 2) F) (hP : IsUnit P.det)
    (A : Matrix (Fin 2) (Fin 2) F) :
    P⁻¹ * (P * A * P⁻¹) * P = A := by
  simp only [Matrix.mul_assoc]
  rw [Matrix.nonsing_inv_mul P hP, Matrix.mul_one, ← Matrix.mul_assoc P⁻¹ P A,
    Matrix.nonsing_inv_mul P hP, Matrix.one_mul]

/-- `P (P⁻¹ A P) P⁻¹ = A`. -/
private lemma conj_inv_conj (P : Matrix (Fin 2) (Fin 2) F) (hP : IsUnit P.det)
    (A : Matrix (Fin 2) (Fin 2) F) :
    P * (P⁻¹ * A * P) * P⁻¹ = A := by
  simp only [Matrix.mul_assoc]
  rw [Matrix.mul_nonsing_inv P hP, Matrix.mul_one, ← Matrix.mul_assoc P P⁻¹ A,
    Matrix.mul_nonsing_inv P hP, Matrix.one_mul]

end Mat

/-! ## Conjugation by an invertible matrix, as a monoid homomorphism of `SL(2,F)` -/

/-- Conjugation `M ↦ P M P⁻¹` by a matrix `P` with `det P ≠ 0`, as a monoid homomorphism of
`SL(2,F)` (the determinant is preserved). -/
private noncomputable def conjSL (F : Type*) [Field F] (P : Matrix (Fin 2) (Fin 2) F)
    (hP : P.det ≠ 0) :
    Matrix.SpecialLinearGroup (Fin 2) F →* Matrix.SpecialLinearGroup (Fin 2) F where
  toFun M := ⟨P * (M : Matrix (Fin 2) (Fin 2) F) * P⁻¹, by
    rw [Matrix.det_mul, Matrix.det_mul, Matrix.SpecialLinearGroup.det_coe, mul_one]
    exact (mul_comm _ _).trans
      (Matrix.det_nonsing_inv_mul_det P (isUnit_iff_ne_zero.mpr hP))⟩
  map_one' := by
    apply Subtype.ext
    show P * (1 : Matrix (Fin 2) (Fin 2) F) * P⁻¹ = (1 : Matrix (Fin 2) (Fin 2) F)
    rw [Matrix.mul_one, Matrix.mul_nonsing_inv P (isUnit_iff_ne_zero.mpr hP)]
  map_mul' M N := by
    apply Subtype.ext
    show P * ((M : Matrix (Fin 2) (Fin 2) F) * (N : Matrix (Fin 2) (Fin 2) F)) * P⁻¹ =
      (P * (M : Matrix (Fin 2) (Fin 2) F) * P⁻¹) * (P * (N : Matrix (Fin 2) (Fin 2) F) * P⁻¹)
    exact (conj_mul_mat P (isUnit_iff_ne_zero.mpr hP) _ _).symm

/-- `conjSL` is injective. -/
private lemma conjSL_injective (F : Type*) [Field F] (P : Matrix (Fin 2) (Fin 2) F)
    (hP : P.det ≠ 0) : Function.Injective (conjSL F P hP) := by
  intro M N h
  have h' : P * (M : Matrix (Fin 2) (Fin 2) F) * P⁻¹ =
      P * (N : Matrix (Fin 2) (Fin 2) F) * P⁻¹ :=
    congrArg (fun t : Matrix.SpecialLinearGroup (Fin 2) F => (t : Matrix (Fin 2) (Fin 2) F)) h
  apply Subtype.ext
  calc (M : Matrix (Fin 2) (Fin 2) F)
      = P⁻¹ * (P * (M : Matrix (Fin 2) (Fin 2) F) * P⁻¹) * P :=
        (inv_conj_conj P (isUnit_iff_ne_zero.mpr hP) _).symm
    _ = P⁻¹ * (P * (N : Matrix (Fin 2) (Fin 2) F) * P⁻¹) * P := by rw [h']
    _ = (N : Matrix (Fin 2) (Fin 2) F) := inv_conj_conj P (isUnit_iff_ne_zero.mpr hP) _

/-! ## The centralizer of `pslMap x` is the image of the normalizer of `⟨x⟩` -/

/-- The centralizer in `PSL(2,F)` of the image of `x` is the image of `N_{SL}(⟨x⟩)`. -/
private theorem centralizer_pslMap_eq_map_normalizer_aux (F : Type*) [Field F]
    (h2 : (2 : F) ≠ 0) (x : Matrix.SpecialLinearGroup (Fin 2) F)
    (hx : (x : Matrix (Fin 2) (Fin 2) F) * (x : Matrix (Fin 2) (Fin 2) F) = -1) :
    Subgroup.centralizer ({Work.PSL2.pslMap F x} :
        Set (Matrix.ProjectiveSpecialLinearGroup (Fin 2) F)) =
      (Subgroup.normalizer (Subgroup.zpowers x)).map (Work.PSL2.pslMap F) := by
  apply le_antisymm
  · intro g hg
    obtain ⟨y, hy⟩ := QuotientGroup.mk'_surjective
      (Subgroup.center (Matrix.SpecialLinearGroup (Fin 2) F)) g
    have hy' : Work.PSL2.pslMap F y = g := hy
    have hcomm' : Work.PSL2.pslMap F y * Work.PSL2.pslMap F x =
        Work.PSL2.pslMap F x * Work.PSL2.pslMap F y := by
      rw [hy']
      exact Subgroup.mem_centralizer_singleton_iff.mp hg
    have hcomm : Work.PSL2.pslMap F (y * x * y⁻¹ * x⁻¹) = 1 := by
      rw [map_mul, map_mul, map_mul, map_inv, map_inv, hcomm']
      group
    rcases (Work.L2F.Mat2.pslMap_eq_one_iff F h2 (y * x * y⁻¹ * x⁻¹)).mp hcomm with h1 | h1
    · refine Subgroup.mem_map.mpr ⟨y, ?_, hy'⟩
      rw [Work.L2F.Involution.mem_normalizer_zpowers F x hx y]
      exact Or.inl (mul_inv_eq_one.mp h1)
    · refine Subgroup.mem_map.mpr ⟨y, ?_, hy'⟩
      rw [Work.L2F.Involution.mem_normalizer_zpowers F x hx y]
      refine Or.inr ?_
      calc y * x * y⁻¹ = (y * x * y⁻¹ * x⁻¹) * x := by group
        _ = Work.L2F.negOne F * x := by rw [h1]
  · rintro g ⟨y, hyN, rfl⟩
    rw [Subgroup.mem_centralizer_singleton_iff]
    rcases (Work.L2F.Involution.mem_normalizer_zpowers F x hx y).mp hyN with h | h
    · have hyx : y * x = x * y := by
        calc y * x = (y * x * y⁻¹) * y := by group
          _ = x * y := by rw [h]
      calc Work.PSL2.pslMap F y * Work.PSL2.pslMap F x
          = Work.PSL2.pslMap F (y * x) := ((Work.PSL2.pslMap F).map_mul y x).symm
        _ = Work.PSL2.pslMap F (x * y) := by rw [hyx]
        _ = Work.PSL2.pslMap F x * Work.PSL2.pslMap F y := (Work.PSL2.pslMap F).map_mul x y
    · have hconj : Work.PSL2.pslMap F y * Work.PSL2.pslMap F x * (Work.PSL2.pslMap F y)⁻¹ =
          Work.PSL2.pslMap F x := by
        have h2' : Work.PSL2.pslMap F (y * x * y⁻¹) = Work.PSL2.pslMap F x := by
          rw [h, map_mul,
            (Work.L2F.Mat2.pslMap_eq_one_iff F h2 (Work.L2F.negOne F)).mpr (Or.inr rfl), one_mul]
        rw [map_mul, map_mul, map_inv] at h2'
        exact h2'
      calc Work.PSL2.pslMap F y * Work.PSL2.pslMap F x
          = (Work.PSL2.pslMap F y * Work.PSL2.pslMap F x * (Work.PSL2.pslMap F y)⁻¹) *
            Work.PSL2.pslMap F y := by group
        _ = Work.PSL2.pslMap F x * Work.PSL2.pslMap F y := by rw [hconj]

/-! ## The image of the centralizer of `x` is cyclic -/

/-- The image in `PSL(2,F)` of `C_{SL(2,F)}(x)` is cyclic. -/
private theorem isCyclic_centralizer_aux (F : Type*) [Field F] [Fintype F] (h2 : (2 : F) ≠ 0)
    (x : Matrix.SpecialLinearGroup (Fin 2) F)
    (hx : (x : Matrix (Fin 2) (Fin 2) F) * (x : Matrix (Fin 2) (Fin 2) F) = -1) :
    IsCyclic ((Subgroup.centralizer ({x} : Set (Matrix.SpecialLinearGroup (Fin 2) F))).map
      (Work.PSL2.pslMap F)) := by
  classical
  obtain ⟨P, hPdet, hP⟩ := Work.L2F.Mat2.exists_conj_z F h2 x hx
  have hPu : IsUnit P.det := isUnit_iff_ne_zero.mpr hPdet
  have hPP : P * P⁻¹ = 1 := Matrix.mul_nonsing_inv P hPu
  have hPP' : P⁻¹ * P = 1 := Matrix.nonsing_inv_mul P hPu
  have hcircle_cyc : IsCyclic ↥(Work.L2F.circle F) := by
    rw [Work.L2F.Conic.circle_eq_hypTorus F]
    exact Work.L2F.Conic.hypTorus_cyclic F h2 (-1)
      (by intro h; exact one_ne_zero (neg_eq_zero.mp h))
  have hfz : conjSL F P hPdet x = Work.L2F.z F := by
    apply Subtype.ext
    show P * (x : Matrix (Fin 2) (Fin 2) F) * P⁻¹ = !![0, 1; -1, 0]
    rw [hP, Matrix.mul_assoc, hPP, Matrix.mul_one]
  have hle : (Subgroup.centralizer ({x} : Set (Matrix.SpecialLinearGroup (Fin 2) F))).map
      (conjSL F P hPdet) ≤ Work.L2F.circle F := by
    rw [Work.L2F.circle]
    intro c hc
    obtain ⟨y, hy, rfl⟩ := Subgroup.mem_map.mp hc
    rw [Subgroup.mem_centralizer_singleton_iff] at hy ⊢
    rw [← hfz]
    calc conjSL F P hPdet y * conjSL F P hPdet x
        = conjSL F P hPdet (y * x) := ((conjSL F P hPdet).map_mul y x).symm
      _ = conjSL F P hPdet (x * y) := by rw [hy]
      _ = conjSL F P hPdet x * conjSL F P hPdet y := (conjSL F P hPdet).map_mul x y
  have hcircle_fin : Finite ↥(Work.L2F.circle F) :=
    Finite.of_injective Subtype.val Subtype.val_injective
  have hmap : (Subgroup.centralizer ({x} : Set (Matrix.SpecialLinearGroup (Fin 2) F))).map
      (conjSL F P hPdet) = Work.L2F.circle F := by
    refine Subgroup.eq_of_le_of_card_ge hle ?_
    rw [Subgroup.card_map_of_injective (conjSL_injective F P hPdet),
      Work.L2F.Mat2.centralizer_sq_neg_one_card F h2 x hx]
  have hCxcyc : IsCyclic ↥(Subgroup.centralizer ({x} : Set (Matrix.SpecialLinearGroup (Fin 2) F))) := by
    have he := Subgroup.equivMapOfInjective
      (Subgroup.centralizer ({x} : Set (Matrix.SpecialLinearGroup (Fin 2) F)))
      (conjSL F P hPdet) (conjSL_injective F P hPdet)
    rw [hmap] at he
    exact (MulEquiv.isCyclic he).mpr inferInstance
  have hCxcyc' := hCxcyc
  let ψ : ↥(Subgroup.centralizer ({x} : Set (Matrix.SpecialLinearGroup (Fin 2) F))) →*
      ↥((Subgroup.centralizer ({x} : Set (Matrix.SpecialLinearGroup (Fin 2) F))).map
        (Work.PSL2.pslMap F)) :=
    { toFun := fun y => ⟨Work.PSL2.pslMap F y, Subgroup.mem_map.mpr ⟨y, y.2, rfl⟩⟩
      map_one' := by
        apply Subtype.ext
        exact map_one (Work.PSL2.pslMap F)
      map_mul' := by
        intro a b
        apply Subtype.ext
        exact map_mul (Work.PSL2.pslMap F)
          (a : Matrix.SpecialLinearGroup (Fin 2) F) (b : Matrix.SpecialLinearGroup (Fin 2) F) }
  exact isCyclic_of_surjective ψ (fun c => by
    obtain ⟨y, hy, hye⟩ := Subgroup.mem_map.mp c.2
    exact ⟨⟨y, hy⟩, Subtype.ext hye⟩)

/-! ## The order of the image of the centralizer of `x` -/

/-- `2 * |π(C_{SL}(x))| = |circle F|`. -/
private theorem two_mul_card_centralizer_aux (F : Type*) [Field F] [Fintype F] (h2 : (2 : F) ≠ 0)
    (x : Matrix.SpecialLinearGroup (Fin 2) F)
    (hx : (x : Matrix (Fin 2) (Fin 2) F) * (x : Matrix (Fin 2) (Fin 2) F) = -1) :
    2 * Nat.card ((Subgroup.centralizer ({x} : Set (Matrix.SpecialLinearGroup (Fin 2) F))).map
      (Work.PSL2.pslMap F)) = Nat.card (Work.L2F.circle F) := by
  classical
  have hmemneg : Work.L2F.negOne F ∈
      Subgroup.centralizer ({x} : Set (Matrix.SpecialLinearGroup (Fin 2) F)) := by
    rw [Subgroup.mem_centralizer_singleton_iff]
    exact Work.L2F.Involution.negOne_mul_comm F x
  let Cx := Subgroup.centralizer ({x} : Set (Matrix.SpecialLinearGroup (Fin 2) F))
  let g : ↥Cx := ⟨Work.L2F.negOne F, hmemneg⟩
  let φ : ↥Cx →* Matrix.ProjectiveSpecialLinearGroup (Fin 2) F :=
    (Work.PSL2.pslMap F).comp Cx.subtype
  have hφ : ∀ y : ↥Cx, φ y = Work.PSL2.pslMap F (y : Matrix.SpecialLinearGroup (Fin 2) F) :=
    fun y => rfl
  have hker : φ.ker = Subgroup.zpowers g := by
    apply le_antisymm
    · intro y hy
      rw [MonoidHom.mem_ker, hφ] at hy
      rcases (Work.L2F.Mat2.pslMap_eq_one_iff F h2
        (y : Matrix.SpecialLinearGroup (Fin 2) F)).mp hy with h | h
      · have hy1 : y = 1 := Subtype.ext h
        rw [hy1]
        exact Subgroup.one_mem _
      · have hyg : y = g := Subtype.ext h
        rw [hyg]
        exact Subgroup.mem_zpowers g
    · rw [Subgroup.zpowers_le, MonoidHom.mem_ker]
      change Work.PSL2.pslMap F (Work.L2F.negOne F) = 1
      exact (Work.L2F.Mat2.pslMap_eq_one_iff F h2 (Work.L2F.negOne F)).mpr (Or.inr rfl)
  have hcard2 : Nat.card φ.ker = 2 := by
    rw [hker, Nat.card_zpowers]
    refine orderOf_eq_prime ?_ ?_
    · rw [pow_two]
      apply Subtype.ext
      show Work.L2F.negOne F * Work.L2F.negOne F = 1
      exact Work.L2F.Involution.negOne_mul_self F
    · intro h
      have h' : (Work.L2F.negOne F : Matrix.SpecialLinearGroup (Fin 2) F) = 1 :=
        congrArg (fun t : ↥Cx => (t : Matrix.SpecialLinearGroup (Fin 2) F)) h
      exact negOne_ne_one F h2 h'
  have hrange : φ.range = Cx.map (Work.PSL2.pslMap F) := by
    change ((Work.PSL2.pslMap F).comp Cx.subtype).range = Subgroup.map (Work.PSL2.pslMap F) Cx
    rw [← MonoidHom.map_range (Work.PSL2.pslMap F) Cx.subtype, Subgroup.range_subtype]
  have hq := Subgroup.card_eq_card_quotient_mul_card_subgroup φ.ker
  have heq : Nat.card (↥Cx ⧸ φ.ker) = Nat.card φ.range :=
    Nat.card_congr (QuotientGroup.quotientKerEquivRange φ).toEquiv
  rw [heq, hcard2, hrange] at hq
  rw [Work.L2F.Mat2.centralizer_sq_neg_one_card F h2 x hx] at hq
  rw [mul_comm]
  exact hq.symm

/-! ## The main theorem -/

/-- The centralizer in `PSL(2,F)` of the image of `x ∈ SL(2,F)` with `x² = -1` (odd characteristic)
is dihedral of order `2n` where `2n = |circle F| = q ∓ 1`.  Proof: it is the image of
`N_{SL}(⟨x⟩)`; `N_{SL}(⟨x⟩) = C(x) ∪ {y : yxy⁻¹ = -x}`; the image `C₀` of `C(x)` is a subgroup of
index two (`|C(x)| = |circle F|`, and the image has half as many elements) and is cyclic (it is the
image of the cyclic group `C(x)`, which is `circle F` up to `GL`-conjugation, and
`circle F = hypTorus F (-1)` is cyclic); an inverting element `w` with `w² = -1` inverts `C(x)`, so
its image is an involution of `C(π(x))` outside `C₀` inverting it.  Now apply
`mulEquiv_dihedral_of_cyclic_index_two`. -/
theorem centralizer_psl_dihedral (F : Type*) [Field F] [Fintype F] (h2 : (2 : F) ≠ 0)
    (x : Matrix.SpecialLinearGroup (Fin 2) F)
    (hx : (x : Matrix (Fin 2) (Fin 2) F) * (x : Matrix (Fin 2) (Fin 2) F) = -1) :
    ∃ n : ℕ, 2 * n = Nat.card (Work.L2F.circle F) ∧
      Nonempty (Subgroup.centralizer ({Work.PSL2.pslMap F x} :
        Set (Matrix.ProjectiveSpecialLinearGroup (Fin 2) F)) ≃* DihedralGroup n) := by
  classical
  have hCx_cyc := isCyclic_centralizer_aux F h2 x hx
  have hcard := two_mul_card_centralizer_aux F h2 x hx
  have hNmap := centralizer_pslMap_eq_map_normalizer_aux F h2 x hx
  have hPSLfin : Finite (Matrix.ProjectiveSpecialLinearGroup (Fin 2) F) :=
    Finite.of_surjective (Work.PSL2.pslMap F)
      (QuotientGroup.mk'_surjective (Subgroup.center (Matrix.SpecialLinearGroup (Fin 2) F)))
  set N : Subgroup (Matrix.ProjectiveSpecialLinearGroup (Fin 2) F) :=
    Subgroup.centralizer ({Work.PSL2.pslMap F x} :
      Set (Matrix.ProjectiveSpecialLinearGroup (Fin 2) F)) with hN
  have hNfin : Finite ↥N := Finite.of_injective Subtype.val Subtype.val_injective
  have hNeq : N = (Subgroup.normalizer (Subgroup.zpowers x)).map (Work.PSL2.pslMap F) := by
    rw [hN]
    exact hNmap
  set Cx := Subgroup.centralizer ({x} : Set (Matrix.SpecialLinearGroup (Fin 2) F)) with hCx
  have hCxNx : Cx ≤ Subgroup.normalizer (Subgroup.zpowers x) := by
    intro y hy
    rw [Work.L2F.Involution.mem_normalizer_zpowers F x hx y]
    refine Or.inl ?_
    have hyx : y * x = x * y := Subgroup.mem_centralizer_singleton_iff.mp hy
    calc y * x * y⁻¹ = (x * y) * y⁻¹ := by rw [hyx]
      _ = x := by group
  have hCxN : Cx.map (Work.PSL2.pslMap F) ≤ N := by
    rw [hNeq]
    exact Subgroup.map_mono hCxNx
  set C : Subgroup ↥N := (Cx.map (Work.PSL2.pslMap F)).subgroupOf N with hC
  have hcyc : IsCyclic ↥C := by
    rw [hC]
    exact (MulEquiv.isCyclic (Subgroup.subgroupOfEquivOfLe hCxN)).mpr hCx_cyc
  -- an element `w₀` with `w₀ x w₀⁻¹ = -x` and `w₀² = -1`
  obtain ⟨w0, hw0conj, hw0sq⟩ := Work.L2F.Involution.exists_inverting F h2 x hx
  have hw0Nx : w0 ∈ Subgroup.normalizer (Subgroup.zpowers x) := by
    rw [Work.L2F.Involution.mem_normalizer_zpowers F x hx w0]
    exact Or.inr hw0conj
  have hw0N : Work.PSL2.pslMap F w0 ∈ N := by
    rw [hNeq]
    exact Subgroup.mem_map.mpr ⟨w0, hw0Nx, rfl⟩
  let w : ↥N := ⟨Work.PSL2.pslMap F w0, hw0N⟩
  have hw_notmem : w ∉ C := by
    intro hwC
    rw [hC, Subgroup.mem_subgroupOf] at hwC
    obtain ⟨c, hc, hce⟩ := Subgroup.mem_map.mp hwC
    have hcx' : c * x * c⁻¹ = x := by
      have hcx : c * x = x * c := Subgroup.mem_centralizer_singleton_iff.mp hc
      calc c * x * c⁻¹ = (x * c) * c⁻¹ := by rw [hcx]
        _ = x := by group
    have hker : Work.PSL2.pslMap F (w0 * c⁻¹) = 1 := by
      rw [map_mul, map_inv, hce]
      exact mul_inv_cancel (Work.PSL2.pslMap F w0)
    rcases (Work.L2F.Mat2.pslMap_eq_one_iff F h2 (w0 * c⁻¹)).mp hker with h1 | h1
    · have hw0c : w0 * x * w0⁻¹ = x := by
        have hwc : w0 = c := by
          calc w0 = (w0 * c⁻¹) * c := by group
            _ = c := by rw [h1, one_mul]
        rw [hwc, hcx']
      exact absurd (hw0conj.symm.trans hw0c).symm (ne_negOne_mul F h2 x)
    · have hw0c : w0 * x * w0⁻¹ = x := by
        have hwc : w0 = Work.L2F.negOne F * c := by
          calc w0 = (w0 * c⁻¹) * c := by group
            _ = Work.L2F.negOne F * c := by rw [h1]
        rw [hwc]
        rw [show (Work.L2F.negOne F * c) * x * (Work.L2F.negOne F * c)⁻¹ =
            Work.L2F.negOne F * (c * x * c⁻¹) * (Work.L2F.negOne F)⁻¹ from by group, hcx']
        rw [show (Work.L2F.negOne F)⁻¹ = Work.L2F.negOne F from by
              rw [inv_eq_iff_mul_eq_one]
              exact Work.L2F.Involution.negOne_mul_self F]
        rw [show Work.L2F.negOne F * x * Work.L2F.negOne F = x from by
              rw [mul_assoc, ← Work.L2F.Involution.negOne_mul_comm F x, ← mul_assoc,
                Work.L2F.Involution.negOne_mul_self, one_mul]]
      exact absurd (hw0conj.symm.trans hw0c).symm (ne_negOne_mul F h2 x)
  have hw_sq : w * w = 1 := by
    apply Subtype.ext
    change Work.PSL2.pslMap F w0 * Work.PSL2.pslMap F w0 = 1
    rw [← map_mul, hw0sq]
    exact (Work.L2F.Mat2.pslMap_eq_one_iff F h2 (Work.L2F.negOne F)).mpr (Or.inr rfl)
  have hw_inv : ∀ c ∈ C, w * c * w⁻¹ = c⁻¹ := by
    intro c hc
    rw [hC, Subgroup.mem_subgroupOf] at hc
    obtain ⟨y, hy, hye⟩ := Subgroup.mem_map.mp hc
    have hiny : w0 * y * w0⁻¹ = y⁻¹ :=
      Work.L2F.Involution.inverts_of_conj F h2 x w0 hx hw0conj y hy
    refine Subtype.ext ?_
    change Work.PSL2.pslMap F w0 * (c : Matrix.ProjectiveSpecialLinearGroup (Fin 2) F) *
        (Work.PSL2.pslMap F w0)⁻¹ = (c : Matrix.ProjectiveSpecialLinearGroup (Fin 2) F)⁻¹
    rw [← hye,
      show Work.PSL2.pslMap F w0 * Work.PSL2.pslMap F y * (Work.PSL2.pslMap F w0)⁻¹ =
        Work.PSL2.pslMap F (w0 * y * w0⁻¹) from by rw [map_mul, map_mul, map_inv],
      hiny, map_inv]
  have hidx : C.index = 2 := by
    rw [Subgroup.index_eq_two_iff_exists_notMem_and]
    refine ⟨w, hw_notmem, ?_⟩
    intro b
    have hb : (b : Matrix.ProjectiveSpecialLinearGroup (Fin 2) F) ∈
        (Subgroup.normalizer (Subgroup.zpowers x)).map (Work.PSL2.pslMap F) := by
      rw [← hNeq]
      exact b.2
    obtain ⟨y, hy, hye⟩ := Subgroup.mem_map.mp hb
    rcases (Work.L2F.Involution.mem_normalizer_zpowers F x hx y).mp hy with hc | hc
    · right
      rw [hC, Subgroup.mem_subgroupOf, Subgroup.mem_map]
      refine ⟨y, ?_, hye⟩
      rw [Subgroup.mem_centralizer_singleton_iff]
      calc y * x = (y * x * y⁻¹) * y := by group
        _ = x * y := by rw [hc]
    · left
      rw [hC, Subgroup.mem_subgroupOf, Subgroup.mem_map]
      refine ⟨y * w0, ?_, ?_⟩
      · rw [Subgroup.mem_centralizer_singleton_iff]
        have hconj : (y * w0) * x * (y * w0)⁻¹ = x := by
          rw [show (y * w0) * x * (y * w0)⁻¹ = y * (w0 * x * w0⁻¹) * y⁻¹ from by group,
            hw0conj,
            show y * (Work.L2F.negOne F * x) * y⁻¹ =
              (y * Work.L2F.negOne F * y⁻¹) * (y * x * y⁻¹) from by group,
            show y * Work.L2F.negOne F * y⁻¹ = Work.L2F.negOne F from by
              rw [← Work.L2F.Involution.negOne_mul_comm F y]; group,
            hc, ← mul_assoc, Work.L2F.Involution.negOne_mul_self, one_mul]
        calc (y * w0) * x = ((y * w0) * x * (y * w0)⁻¹) * (y * w0) := by group
          _ = x * (y * w0) := by rw [hconj]
      · show Work.PSL2.pslMap F (y * w0) =
          (b : Matrix.ProjectiveSpecialLinearGroup (Fin 2) F) * Work.PSL2.pslMap F w0
        rw [map_mul, hye]
  obtain ⟨e⟩ := Work.L2F.Dihedral.mulEquiv_dihedral_of_cyclic_index_two C hcyc hidx
    ⟨w, hw_notmem, hw_sq, hw_inv⟩
  refine ⟨Nat.card ↥C, ?_, ⟨e⟩⟩
  rw [show Nat.card ↥C = Nat.card ↥(Cx.map (Work.PSL2.pslMap F)) from by
    rw [hC]
    exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe hCxN).toEquiv]
  exact hcard

end Work.L2F.PSL
