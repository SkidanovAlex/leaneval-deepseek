import Mathlib
import Submission.Work.L2F.Defs
import Submission.Work.L2F.Torus.Defs
import Submission.Work.L2F.Torus.commute_iff_mem_algSpan
import Submission.Work.L2F.Mat2.centralizer_aux
import Submission.Work.L2F.Torus.conj_eq_inv_of_conjNeg

open scoped MatrixGroups
open Matrix

namespace Work.L2F.Torus

/-- A non-zero traceless matrix is not a scalar (when `2 ≠ 0`). -/
private lemma not_scalar_of_trace_zero {F : Type*} [Field F] (h2 : (2 : F) ≠ 0)
    {W : Matrix (Fin 2) (Fin 2) F} (htr : W.trace = 0) (hne : W ≠ 0) : ∀ c : F, W ≠ c • 1 := by
  intro c hc
  have htrc : W.trace = (2 : F) * c := by
    rw [hc, Matrix.trace_smul, Matrix.trace_one, Fintype.card_fin]
    ring
  rw [htr] at htrc
  have hc0 : c = 0 := (mul_eq_zero.mp htrc.symm).resolve_left h2
  rw [hc0, zero_smul] at hc
  exact hne hc

/-- Conjugation by `c` which maps `x` into `⟨x, -1⟩` maps `⟨x, -1⟩` into itself. -/
private lemma conj_mem_genZ {F : Type*} [Field F] {x c a : Matrix.SpecialLinearGroup (Fin 2) F}
    (hcx : c * x * c⁻¹ ∈ genZ F x) (ha : a ∈ genZ F x) : c * a * c⁻¹ ∈ genZ F x := by
  have hc1 : c * Work.L2F.negOne F * c⁻¹ = Work.L2F.negOne F := by
    rw [← Work.L2F.Involution.negOne_mul_comm F c, mul_assoc, mul_inv_cancel, mul_one]
  let S : Subgroup (Matrix.SpecialLinearGroup (Fin 2) F) :=
    Subgroup.closure ({(x : Matrix.SpecialLinearGroup (Fin 2) F), Work.L2F.negOne F} :
      Set (Matrix.SpecialLinearGroup (Fin 2) F))
  have hcx' : c * x * c⁻¹ ∈ S := hcx
  have ha' : a ∈ S := ha
  have hgoal : c * a * c⁻¹ ∈ S := by
    refine Subgroup.closure_induction (p := fun y _ => c * y * c⁻¹ ∈ S) (fun y hy => ?_) ?_
      (fun y z hy hz ihy ihz => ?_) (fun y hy ihy => ?_) ha'
    · rcases hy with rfl | rfl
      · exact hcx'
      · rw [hc1]; exact Subgroup.subset_closure (by simp)
    · rw [mul_one, mul_inv_cancel]; exact Subgroup.one_mem _
    · have h : c * (y * z) * c⁻¹ = (c * y * c⁻¹) * (c * z * c⁻¹) := by group
      rw [h]; exact Subgroup.mul_mem _ ihy ihz
    · have h : c * y⁻¹ * c⁻¹ = (c * y * c⁻¹)⁻¹ := by group
      rw [h]; exact Subgroup.inv_mem _ ihy
  exact hgoal

/-- If `w ∈ SL(2,F)` conjugates the traceless part of `x` to its negative, then the normalizer of
`⟨x, -1⟩` in `SL(2,F)` is `C_{SL}(x) ⊔ ⟨w⟩`, i.e. `C_{SL}(x) ∪ w·C_{SL}(x)`. -/
theorem normalizer_closure_eq_sup (F : Type*) [Field F] (h2 : (2 : F) ≠ 0)
    (x w : Matrix.SpecialLinearGroup (Fin 2) F) (hD : disc F x ≠ 0)
    (hw : conjNeg F w (conjMat F x)) :
    Subgroup.normalizer (genZ F x : Set (Matrix.SpecialLinearGroup (Fin 2) F)) =
      cent F x ⊔ Subgroup.zpowers w := by
  set W : Matrix (Fin 2) (Fin 2) F := conjMat F x with hW
  have hWtr : W.trace = 0 := by rw [hW]; exact conjMat_trace F x
  have hW2 : W * W = disc F x • 1 := by rw [hW]; exact conjMat_mul_self F x
  have hWns : ∀ c : F, W ≠ c • 1 :=
    not_scalar_of_trace_zero h2 hWtr (by rw [hW]; exact conjMat_ne_zero F x hD)
  have hgenZ_le : genZ F x ≤ cent F x := by
    rw [genZ_apply, Subgroup.closure_le]
    intro a ha
    rcases ha with h | h
    · rw [h]; exact Subgroup.mem_centralizer_singleton_iff.mpr rfl
    · rw [h]; exact Subgroup.mem_centralizer_singleton_iff.mpr
        (Work.L2F.Involution.negOne_mul_comm F x)
  have hwinv_x : w * x * w⁻¹ = x⁻¹ := conj_eq_inv_of_conjNeg F h2 x w hD hw
  have hwinv_x' : w⁻¹ * x * w = x⁻¹ := by
    have h1 : w * x⁻¹ * w⁻¹ = x := by
      have h' := congrArg (fun z : Matrix.SpecialLinearGroup (Fin 2) F => z⁻¹) hwinv_x
      simpa [_root_.mul_inv_rev, mul_assoc] using h'
    conv_lhs => rw [← h1]
    group
  apply le_antisymm
  · intro g hg
    have hZmem : g * x * g⁻¹ ∈ genZ F x :=
      (Subgroup.mem_normalizer_iff.mp hg x).mp (Subgroup.subset_closure (by simp))
    have hZcent : g * x * g⁻¹ ∈ cent F x := hgenZ_le hZmem
    have hZcomm : (g * x * g⁻¹) * x = x * (g * x * g⁻¹) :=
      Subgroup.mem_centralizer_singleton_iff.mp hZcent
    set Z : Matrix (Fin 2) (Fin 2) F :=
      (((g * x * g⁻¹ : Matrix.SpecialLinearGroup (Fin 2) F)) :
        Matrix (Fin 2) (Fin 2) F) with hZ
    set G : Matrix (Fin 2) (Fin 2) F :=
      ((g : Matrix.SpecialLinearGroup (Fin 2) F) : Matrix (Fin 2) (Fin 2) F) with hG
    set X : Matrix (Fin 2) (Fin 2) F :=
      ((x : Matrix.SpecialLinearGroup (Fin 2) F) : Matrix (Fin 2) (Fin 2) F) with hX
    have hGd : IsUnit G.det := by rw [hG, Matrix.SpecialLinearGroup.det_coe]; exact isUnit_one
    have hGG : G⁻¹ * G = 1 := Matrix.nonsing_inv_mul G hGd
    have hZmat : Z = G * X * G⁻¹ := by
      rw [hZ, hG, hX, Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_mul,
        Matrix.SpecialLinearGroup.coe_inv,
        adjugate_eq_inv_of_det_eq_one' G (by rw [hG, Matrix.SpecialLinearGroup.det_coe])]
    have hZX : Z * X = X * Z := by
      have h := congrArg (fun z : Matrix.SpecialLinearGroup (Fin 2) F =>
        ((z : Matrix.SpecialLinearGroup (Fin 2) F) : Matrix (Fin 2) (Fin 2) F)) hZcomm
      simpa only [hZ, hX, Matrix.SpecialLinearGroup.coe_mul] using h
    have hZW : Z * W = W * Z := by
      have h := Work.L2F.Mat2.mul_conjMat_comm h2 x (g * x * g⁻¹)
        (by simpa only [hZ, hX] using hZX)
      simpa only [hW, hZ] using h
    have hZmemA : Z ∈ algSpan F W :=
      (commute_iff_mem_algSpan F h2 W Z (disc F x) hWtr hW2 hD).mp hZW
    have hGWG : G * W * G⁻¹ = (2 : F) • Z - (X.trace) • 1 := by
      rw [hW]
      calc G * conjMat F x * G⁻¹
          = G * ((2 : F) • X - (X.trace) • (1 : Matrix (Fin 2) (Fin 2) F)) * G⁻¹ := by
            rw [conjMat, ← hX]
        _ = (2 : F) • (G * X * G⁻¹) - (X.trace) • 1 := by
            simp only [Matrix.mul_sub, Matrix.sub_mul, conj_smul', conj_one' G hGd]
        _ = (2 : F) • Z - (X.trace) • 1 := by rw [← hZmat]
    have hGWGmem : G * W * G⁻¹ ∈ algSpan F W := by
      rw [hGWG, sub_eq_add_neg, ← neg_smul]
      exact algSpan_add F (algSpan_smul F hZmemA (2 : F))
        (algSpan_smul F (algSpan_one F W) (-(X.trace)))
    obtain ⟨a, b, hGWGeq⟩ := hGWGmem
    have hsq : (G * W * G⁻¹) * (G * W * G⁻¹) = disc F x • 1 := by
      have h1 : (G * W * G⁻¹) * (G * W * G⁻¹) = G * (W * W) * G⁻¹ := by
        calc (G * W * G⁻¹) * (G * W * G⁻¹)
            = G * W * (G⁻¹ * G) * W * G⁻¹ := by noncomm_ring
          _ = G * W * W * G⁻¹ := by rw [hGG, Matrix.mul_one]
          _ = G * (W * W) * G⁻¹ := by noncomm_ring
      rw [h1, hW2, Matrix.mul_smul, Matrix.smul_mul, conj_one' G hGd]
    have hcoeff : (a * a + disc F x * (b * b) - disc F x) • (1 : Matrix (Fin 2) (Fin 2) F)
        + (2 * a * b) • W = 0 := by
      have h1 := Work.L2F.Mat2.smul_one_add_smul_mul hW2 a b a b
      rw [← hGWGeq, hsq] at h1
      have hab2 : a * b + b * a = 2 * a * b := by ring
      rw [hab2] at h1
      rw [sub_smul, h1]
      abel
    obtain ⟨hco1, hco2⟩ := algSpan_eq_zero F hWns (a * a + disc F x * (b * b) - disc F x)
      (2 * a * b) hcoeff
    have hb_ne : b ≠ 0 := by
      intro hb0
      have hWa : W = a • (1 : Matrix (Fin 2) (Fin 2) F) := by
        have hGWGa : G * W * G⁻¹ = a • (1 : Matrix (Fin 2) (Fin 2) F) := by
          rw [hGWGeq, hb0, zero_smul, add_zero]
        have hkey : G⁻¹ * (G * W * G⁻¹) * G = W := by
          calc G⁻¹ * (G * W * G⁻¹) * G
              = (G⁻¹ * G) * W * (G⁻¹ * G) := by noncomm_ring
            _ = W := by rw [hGG, one_mul, mul_one]
        calc W = G⁻¹ * (G * W * G⁻¹) * G := hkey.symm
          _ = a • (1 : Matrix (Fin 2) (Fin 2) F) := by
              rw [hGWGa, Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_one,
                Matrix.nonsing_inv_mul G hGd]
      exact hWns a hWa
    have ha_zero : a = 0 := by
      rcases mul_eq_zero.mp hco2 with h | h
      · rcases mul_eq_zero.mp h with h' | h'
        · exact absurd h' h2
        · exact h'
      · exact absurd h hb_ne
    have hb_sq : b * b = 1 := by
      have h : disc F x * (b * b) = disc F x * 1 := by
        rw [mul_one]
        have h' := hco1
        rw [ha_zero, mul_zero, zero_add] at h'
        exact sub_eq_zero.mp h'
      rcases mul_eq_mul_left_iff.mp h with h' | h'
      · exact h'
      · exact absurd h' hD
    have hb_val : b = 1 ∨ b = -1 := by
      have h : (b - 1) * (b + 1) = 0 := by linear_combination hb_sq
      rcases mul_eq_zero.mp h with h' | h'
      · exact Or.inl (sub_eq_zero.mp h')
      · exact Or.inr (by linear_combination h')
    rcases hb_val with hb1 | hb1
    · have hcommW : G * W = W * G := by
        have h : G * W * G⁻¹ = W := by rw [hGWGeq, ha_zero, hb1]; simp
        calc G * W = (G * W * G⁻¹) * G := by
              simp only [Matrix.mul_assoc, Matrix.nonsing_inv_mul G hGd, Matrix.mul_one]
          _ = W * G := by rw [h]
      have hGmemA : G ∈ algSpan F W :=
        (commute_iff_mem_algSpan F h2 W G (disc F x) hWtr hW2 hD).mp hcommW
      have hGcent : g ∈ cent F x := by
        rw [cent_apply, Subgroup.mem_centralizer_singleton_iff]
        apply Subtype.ext
        obtain ⟨p, q, hpq⟩ := hGmemA
        have hXm : X ∈ algSpan F W := by rw [hW, hX]; exact x_mem_algSpan F h2 x
        obtain ⟨c, e, hce⟩ := hXm
        simp only [Matrix.SpecialLinearGroup.coe_mul, ← hG, ← hX]
        rw [hpq, hce]
        exact Work.L2F.Mat2.smul_one_add_smul_mul_comm (conjMat_mul_self F x) p q c e
      exact Subgroup.mem_sup_left hGcent
    · set Mw : Matrix (Fin 2) (Fin 2) F :=
        ((w : Matrix.SpecialLinearGroup (Fin 2) F) : Matrix (Fin 2) (Fin 2) F) with hMw
      have hM : Mw * W * Mw⁻¹ = -W := by rw [hMw, hW]; exact hw
      have hsig : G * W * G⁻¹ = -W := by rw [hGWGeq, ha_zero, hb1]; simp
      have hGd2 : IsUnit (G * Mw).det := by
        rw [Matrix.det_mul]
        exact hGd.mul (by rw [hMw, Matrix.SpecialLinearGroup.det_coe]; exact isUnit_one)
      have hconj : G * Mw * W * (G * Mw)⁻¹ = W := by
        rw [Matrix.mul_inv_rev]
        calc G * Mw * W * (Mw⁻¹ * G⁻¹) = G * (Mw * W * Mw⁻¹) * G⁻¹ := by noncomm_ring
          _ = G * (-W) * G⁻¹ := by rw [hM]
          _ = -(G * W * G⁻¹) := by noncomm_ring
          _ = -(-W) := by rw [hsig]
          _ = W := neg_neg W
      have hcommW : G * Mw * W = W * (G * Mw) := by
        calc G * Mw * W = (G * Mw * W * (G * Mw)⁻¹) * (G * Mw) := by
              simp only [Matrix.mul_assoc, Matrix.nonsing_inv_mul _ hGd2, Matrix.mul_one]
          _ = W * (G * Mw) := by rw [hconj]
      have hmemA : G * Mw ∈ algSpan F W :=
        (commute_iff_mem_algSpan F h2 W (G * Mw) (disc F x) hWtr hW2 hD).mp hcommW
      have hgw_cent : g * w ∈ cent F x := by
        rw [cent_apply, Subgroup.mem_centralizer_singleton_iff]
        apply Subtype.ext
        obtain ⟨p, q, hpq⟩ := hmemA
        have hXm : X ∈ algSpan F W := by rw [hW, hX]; exact x_mem_algSpan F h2 x
        obtain ⟨c, e, hce⟩ := hXm
        simp only [Matrix.SpecialLinearGroup.coe_mul, ← hG, ← hMw, ← hX]
        rw [hpq, hce]
        exact Work.L2F.Mat2.smul_one_add_smul_mul_comm (conjMat_mul_self F x) p q c e
      have hg_eq : g = (g * w) * w⁻¹ := by group
      rw [hg_eq]
      exact Subgroup.mul_mem _ (Subgroup.mem_sup_left hgw_cent)
        (Subgroup.mem_sup_right (Subgroup.inv_mem _ (Subgroup.mem_zpowers w)))
  · rw [sup_le_iff]
    constructor
    · intro c hc
      have hcomm : c * x = x * c := Subgroup.mem_centralizer_singleton_iff.mp hc
      have hcx : c * x * c⁻¹ ∈ genZ F x := by
        have h : c * x * c⁻¹ = x := by rw [hcomm, mul_assoc, mul_inv_cancel, mul_one]
        rw [h]; exact Subgroup.subset_closure (by simp)
      rw [Subgroup.mem_normalizer_iff]
      intro a
      constructor
      · intro ha
        exact conj_mem_genZ hcx ha
      · intro ha
        have hcomm' : c⁻¹ * x = x * c⁻¹ :=
          Subgroup.mem_centralizer_singleton_iff.mp ((cent F x).inv_mem hc)
        have hcx' : c⁻¹ * x * (c⁻¹)⁻¹ ∈ genZ F x := by
          have h : c⁻¹ * x * (c⁻¹)⁻¹ = x := by
            rw [inv_inv, hcomm', mul_assoc, inv_mul_cancel, mul_one]
          rw [h]; exact Subgroup.subset_closure (by simp)
        have h := conj_mem_genZ hcx' ha
        simp only [inv_inv] at h
        rwa [show c⁻¹ * (c * a * c⁻¹) * c = a from by group] at h
    · refine Subgroup.zpowers_le.mpr ?_
      rw [Subgroup.mem_normalizer_iff]
      intro a
      constructor
      · intro ha
        have hxc : w * x * w⁻¹ ∈ genZ F x := by
          rw [hwinv_x]
          exact Subgroup.inv_mem _ (Subgroup.subset_closure (by simp))
        exact conj_mem_genZ hxc ha
      · intro ha
        have hxc' : w⁻¹ * x * (w⁻¹)⁻¹ ∈ genZ F x := by
          have h : w⁻¹ * x * (w⁻¹)⁻¹ = x⁻¹ := by rw [inv_inv, hwinv_x']
          rw [h]; exact Subgroup.inv_mem _ (Subgroup.subset_closure (by simp))
        have h := conj_mem_genZ hxc' ha
        simp only [inv_inv] at h
        rwa [show w⁻¹ * (w * a * w⁻¹) * w = a from by group] at h

end Work.L2F.Torus
