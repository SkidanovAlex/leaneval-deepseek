import Mathlib
import Submission.Commons.NumberTheory.DiophantineApproximation.BoundedDegree.int_poly_supNorm_one_le
import Submission.Commons.NumberTheory.DiophantineApproximation.BoundedDegree.int_poly_supNorm_C_mul
import Submission.Commons.NumberTheory.DiophantineApproximation.BoundedDegree.int_poly_natDegree_map_eq
import Submission.Commons.NumberTheory.DiophantineApproximation.BoundedDegree.int_poly_supNorm_neg
import Submission.Commons.NumberTheory.DiophantineApproximation.BoundedDegree.int_poly_eval_ne_zero_of_transcendental
import Submission.Commons.NumberTheory.DiophantineApproximation.BoundedDegree.finite_int_polys_bounded_supNorm
import Submission.Commons.NumberTheory.DiophantineApproximation.BoundedDegree.int_poly_content_natAbs_pos
import Submission.Commons.NumberTheory.DiophantineApproximation.BoundedDegree.one_le_int_norm_cast
import Submission.Commons.NumberTheory.DiophantineApproximation.BoundedDegree.exists_pos_small_eval_of_transcendental
import Submission.Commons.NumberTheory.DiophantineApproximation.BoundedDegree.gelfond_supNorm_list_prod

namespace Commons.NumberTheory.DiophantineApproximation.BoundedDegree

open Polynomial
open scoped BigOperators

noncomputable section

private def supN (P : Polynomial ℤ) : ℝ := (P.map (Int.castRingHom ℝ)).supNorm
private def pv (ξ : ℝ) (P : Polynomial ℤ) : ℝ := Polynomial.eval ξ (P.map (Int.castRingHom ℝ))

private lemma supN_nonneg (P : Polynomial ℤ) : 0 ≤ supN P := by
  dsimp [supN]
  exact (Polynomial.supNorm_nonneg (p := P.map (Int.castRingHom ℝ)))

private lemma supN_one_le {P : Polynomial ℤ} (h : P ≠ 0) : 1 ≤ supN P := by
  dsimp [supN]
  exact int_poly_supNorm_one_le P h

private lemma supN_C_mul (c : ℤ) (P : Polynomial ℤ) : supN (C c * P) = ‖(c : ℝ)‖ * supN P := by
  dsimp [supN]
  exact int_poly_supNorm_C_mul c P

private lemma supN_neg (P : Polynomial ℤ) : supN (-P) = supN P := by
  dsimp [supN]
  exact int_poly_supNorm_neg P

private lemma supN_one : supN 1 = 1 := by
  dsimp [supN]
  rw [Polynomial.map_one, ← Polynomial.C_1, Polynomial.supNorm_C]
  norm_num

private lemma supN_eq_zero_iff {P : Polynomial ℤ} : supN P = 0 ↔ P = 0 := by
  dsimp [supN]
  rw [Polynomial.supNorm_eq_zero_iff]
  exact Polynomial.map_eq_zero_iff (Int.cast_injective (α := ℝ))

private lemma pv_ne_zero_of_transcendental {ξ : ℝ} (hξ : Transcendental ℚ ξ) {P : Polynomial ℤ}
    (hP : P ≠ 0) : pv ξ P ≠ 0 := by
  dsimp [pv]
  exact int_poly_eval_ne_zero_of_transcendental ξ hξ P hP

private lemma pv_mul (ξ : ℝ) (A B : Polynomial ℤ) : pv ξ (A * B) = pv ξ A * pv ξ B := by
  dsimp [pv]
  rw [Polynomial.map_mul (Int.castRingHom ℝ), Polynomial.eval_mul]

private lemma pv_C_mul (ξ : ℝ) (c : ℤ) (P : Polynomial ℤ) : pv ξ (C c * P) = (c : ℝ) * pv ξ P := by
  dsimp [pv]
  rw [Polynomial.map_mul (Int.castRingHom ℝ), Polynomial.map_C, Polynomial.eval_C_mul]
  norm_num

private lemma abs_pv_C_mul (ξ : ℝ) (c : ℤ) (P : Polynomial ℤ) :
    |pv ξ (C c * P)| = |(c : ℝ)| * |pv ξ P| := by
  rw [pv_C_mul, abs_mul]

private lemma content_cast_one_le (P : Polynomial ℤ) (h : P ≠ 0) :
    (1 : ℝ) ≤ ‖(P.content : ℝ)‖ := by
  exact one_le_int_norm_cast P.content (by
    intro hc
    exact h (Polynomial.content_eq_zero_iff.mp hc))

private lemma supN_primPart_mul_content (P : Polynomial ℤ) :
    supN P = ‖(P.content : ℝ)‖ * supN P.primPart := by
  rw [← supN_C_mul P.content P.primPart]
  congr 1
  exact (Polynomial.eq_C_content_mul_primPart P)

private lemma abs_pv_content_mul_primPart (ξ : ℝ) (P : Polynomial ℤ) :
    |pv ξ P| = |(P.content : ℝ)| * |pv ξ P.primPart| := by
  rw [← abs_pv_C_mul ξ P.content P.primPart]
  congr 1
  exact congrArg (fun Q : Polynomial ℤ => pv ξ Q) (Polynomial.eq_C_content_mul_primPart P)

/-! ## Elementary lemmas about products over lists of reals -/

private lemma list_prod_nonneg (l : List ℝ) (h : ∀ x ∈ l, 0 ≤ x) : 0 ≤ l.prod := by
  induction l with
  | nil => simp
  | cons a l ih => exact mul_nonneg (h a (by simp)) (ih (fun x hx => h x (by simp [hx])))

private lemma list_prod_map_le_map {α : Type*} (l : List α) (f g : α → ℝ)
    (hf : ∀ a ∈ l, 0 ≤ f a) (hfg : ∀ a ∈ l, f a ≤ g a) : (l.map f).prod ≤ (l.map g).prod := by
  induction l with
  | nil => simp
  | cons a l ih =>
    simp only [List.map_cons, List.prod_cons]
    refine mul_le_mul (hfg a (by simp)) (ih (fun a ha => hf a (by simp [ha])) (fun a ha => hfg a (by simp [ha]))) ?_ ?_
    · exact list_prod_nonneg (l.map f) (by
        intro x hx
        rcases List.mem_map.mp hx with ⟨b, hb, rfl⟩
        exact hf b (by exact List.mem_cons_of_mem a hb))
    · exact le_trans (hf a (by simp)) (hfg a (by simp))

private lemma list_prod_const_mul {α : Type*} (l : List α) (m : ℝ) (f : α → ℝ) :
    (l.map (fun a => m * f a)).prod = m ^ l.length * (l.map f).prod := by
  induction l with
  | nil => simp
  | cons a l ih =>
    simp [List.prod_cons, ih]
    rw [pow_succ]
    ring

private lemma list_prod_rpow (l : List ℝ) (z : ℝ) (h : ∀ x ∈ l, 0 ≤ x) :
    (l.map (fun x => x ^ z)).prod = l.prod ^ z := by
  induction l with
  | nil => simp [Real.one_rpow]
  | cons a l ih =>
    have htail : ∀ x ∈ l, 0 ≤ x := fun x hx => h x (by exact List.mem_cons_of_mem a hx)
    calc
      (List.map (fun x => x ^ z) (a :: l)).prod = a ^ z * (l.map (fun x => x ^ z)).prod := by simp
      _ = a ^ z * l.prod ^ z := by rw [ih htail]
      _ = (a * l.prod) ^ z := (Real.mul_rpow (h a (by simp)) (list_prod_nonneg l htail)).symm

private lemma eval_list_prod {ξ : ℝ} (l : List (Polynomial ℤ)) :
    Polynomial.eval ξ (l.prod.map (Int.castRingHom ℝ)) =
      (l.map (fun w : Polynomial ℤ => Polynomial.eval ξ (w.map (Int.castRingHom ℝ)))).prod := by
  induction l with
  | nil => simp
  | cons a l ih =>
    simp only [List.prod_cons, List.map_cons]
    rw [Polynomial.map_mul (Int.castRingHom ℝ), Polynomial.eval_mul]
    exact congrArg (fun t : ℝ => Polynomial.eval ξ (a.map (Int.castRingHom ℝ)) * t) ih

private lemma norm_list_prod (l : List ℝ) : ‖l.prod‖ = (l.map (fun x : ℝ => ‖x‖)).prod := by
  induction l with
  | nil => simp
  | cons a l ih =>
    simp [List.prod_cons, ih, norm_mul]

private lemma pv_list_prod (ξ : ℝ) (l : List (Polynomial ℤ)) :
    pv ξ l.prod = (l.map (fun w : Polynomial ℤ => pv ξ w)).prod := by
  dsimp [pv]
  exact eval_list_prod l

private lemma norm_pv_list_prod (ξ : ℝ) (l : List (Polynomial ℤ)) :
    ‖pv ξ l.prod‖ = (l.map (fun w : Polynomial ℤ => ‖pv ξ w‖)).prod := by
  rw [pv_list_prod, norm_list_prod]
  simp [List.map_map, Function.comp_def]

private lemma abs_list_prod (l : List ℝ) : |l.prod| = (l.map (fun x : ℝ => |x|)).prod := by
  induction l with
  | nil => simp
  | cons a l ih =>
    simp [List.prod_cons, ih, abs_mul]

private lemma abs_pv_list_prod (ξ : ℝ) (l : List (Polynomial ℤ)) :
    |pv ξ l.prod| = (l.map (fun w : Polynomial ℤ => |pv ξ w|)).prod := by
  rw [pv_list_prod, abs_list_prod]
  simp [List.map_map, Function.comp_def]

private lemma length_le_sum_natDegree (l : List (Polynomial ℤ))
    (h : ∀ w ∈ l, 1 ≤ w.natDegree) : l.length ≤ (l.map (fun w : Polynomial ℤ => w.natDegree)).sum := by
  induction l with
  | nil => simp
  | cons a l ih =>
    have ha : 1 ≤ a.natDegree := h a (by simp)
    have hrest : ∀ w ∈ l, 1 ≤ w.natDegree := fun w hw => h w (by simp [hw])
    have hih := ih hrest
    simp only [List.length_cons, List.map_cons, List.sum_cons]
    omega

private lemma natDegree_list_prod (l : List (Polynomial ℤ)) (h : ∀ w ∈ l, w ≠ 0) :
    l.prod.natDegree = (l.map (fun w : Polynomial ℤ => w.natDegree)).sum := by
  induction l with
  | nil => simp
  | cons a l ih =>
    have ha : a ≠ 0 := h a (by simp)
    have htail : ∀ w ∈ l, w ≠ 0 := fun w hw => h w (by exact List.mem_cons_of_mem a hw)
    have hnot0 : (0 : Polynomial ℤ) ∉ l := by
      intro hz
      exact (h 0 (by exact List.mem_cons_of_mem a hz)) rfl
    have hprod_ne : l.prod ≠ 0 := List.prod_ne_zero (l := l) hnot0
    simp only [List.prod_cons, List.map_cons, List.sum_cons]
    rw [natDegree_mul ha hprod_ne, ih htail]

/-! ## Factorization of a primitive polynomial into irreducibles -/

private lemma isUnit_iff_eq_C_one_or_neg (P : Polynomial ℤ) :
    IsUnit P ↔ P = 1 ∨ P = -1 := by
  constructor
  · intro h
    rcases (Polynomial.isUnit_iff.mp h) with ⟨r, hr_unit, hrC⟩
    rw [← hrC]
    rcases Int.isUnit_iff.mp hr_unit with rfl | rfl <;> simp
  · intro h
    rcases h with rfl | rfl <;> simp

private lemma irreducible_natDegree_pos_of_primitive_dvd {P : Polynomial ℤ} (hprim : P.IsPrimitive)
    {w : Polynomial ℤ} (hw : Irreducible w) (hdvd : w ∣ P) : 1 ≤ w.natDegree := by
  by_contra hlt
  have hdeg0 : w.natDegree = 0 := by omega
  rcases (Polynomial.natDegree_eq_zero.mp hdeg0) with ⟨a, haC⟩
  have hwC : w = C a := haC.symm
  have hdiv : a ∣ P.content := by
    exact (Polynomial.dvd_content_iff_C_dvd (p := P)).mpr (by simpa [hwC] using hdvd)
  have hcontent : P.content = 1 := hprim.content_eq_one
  have hunit : IsUnit a := by
    exact isUnit_iff_dvd_one.mpr (by simpa [hcontent] using hdiv)
  exact hw.not_isUnit (by simpa [hwC] using Polynomial.isUnit_C.mpr hunit)

private lemma primitive_not_unit_of_supN_two_le {P : Polynomial ℤ} (hprim : P.IsPrimitive)
    (hP : 2 ≤ supN P) : ¬ IsUnit P := by
  intro h
  rcases (isUnit_iff_eq_C_one_or_neg P).mp h with h1 | h1
  · rw [h1] at hP
    rw [supN_one] at hP
    norm_num at hP
  · rw [h1] at hP
    rw [supN_neg, supN_one] at hP
    norm_num at hP

private lemma exists_irreducible_list_factorization {n : ℕ} (P0 : Polynomial ℤ) (hP0 : P0 ≠ 0)
    (hprim : P0.IsPrimitive) (hnu : ¬ IsUnit P0) (hdeg : P0.natDegree ≤ n) :
    ∃ ws : List (Polynomial ℤ),
      ws.prod = P0 ∧ ws.length ≤ n ∧
      (∀ w ∈ ws, Irreducible w ∧ 1 ≤ w.natDegree ∧ w.natDegree ≤ n ∧ w ≠ 0) := by
  classical
  obtain ⟨f, hf, hprod, hfne⟩ := (WfDvdMonoid.not_isUnit_iff_exists_factors_eq P0 hP0).mp hnu
  let ws : List (Polynomial ℤ) := f.toList
  have hwsprod : ws.prod = P0 := by
    dsimp [ws]
    rw [Multiset.prod_toList f]
    exact hprod
  have hdeg1 : ∀ w ∈ ws, 1 ≤ w.natDegree := by
    intro w hw
    have hmem : w ∈ f := (Multiset.mem_toList).mp (by simpa [ws] using hw)
    exact irreducible_natDegree_pos_of_primitive_dvd hprim (hf w hmem)
      (by
        rw [← hwsprod]
        exact List.dvd_prod hw)
  have hlen_deg : ws.length ≤ (ws.map (fun w : Polynomial ℤ => w.natDegree)).sum :=
    length_le_sum_natDegree ws hdeg1
  have hne_all : ∀ w ∈ ws, w ≠ 0 := fun w hw => (hf w ((Multiset.mem_toList).mp (by simpa [ws] using hw))).ne_zero
  have hdeg_eq : (ws.map (fun w : Polynomial ℤ => w.natDegree)).sum = ws.prod.natDegree :=
    (natDegree_list_prod ws hne_all).symm
  have hlen_n : ws.length ≤ n := by
    calc
      ws.length ≤ (ws.map (fun w : Polynomial ℤ => w.natDegree)).sum := hlen_deg
      _ = ws.prod.natDegree := hdeg_eq
      _ = P0.natDegree := by rw [hwsprod]
      _ ≤ n := hdeg
  refine ⟨ws, hwsprod, hlen_n, ?_⟩
  intro w hw
  have hmem : w ∈ f := (Multiset.mem_toList).mp (by simpa [ws] using hw)
  refine ⟨hf w hmem, hdeg1 w hw, ?_, (hf w hmem).ne_zero⟩
  have hdvd : w ∣ P0 := by
    rw [← hwsprod]
    exact List.dvd_prod (l := ws) hw
  exact le_trans (Polynomial.natDegree_le_of_dvd hdvd hP0) hdeg

/-! ## Content reduction: primitive solutions at exponent e1 have unbounded norm -/

private lemma content_abs_one_le (P : Polynomial ℤ) (h : P ≠ 0) : (1 : ℝ) ≤ |(P.content : ℝ)| := by
  simpa [Real.norm_eq_abs] using content_cast_one_le P h

/-- If `P` is a solution at exponent `e1`, its primitive part is also a solution at exponent
`e1` (with the same degree bound). -/
private lemma primPart_is_solution (ξ e1 : ℝ) (he1 : 0 < e1) {P : Polynomial ℤ} (hP : P ≠ 0)
    (hsol : ‖pv ξ P‖ ≤ (supN P) ^ (-e1)) :
    ‖pv ξ P.primPart‖ ≤ (supN P.primPart) ^ (-e1) := by
  let c : ℝ := |(P.content : ℝ)|
  have hc_ge1 : 1 ≤ c := by
    dsimp [c]
    exact content_abs_one_le P hP
  have hc_pos : 0 < c := lt_of_lt_of_le zero_lt_one hc_ge1
  have hc_pow_pos : 0 ≤ c ^ (-e1) := Real.rpow_nonneg hc_pos.le (-e1)
  have hsup : supN P = c * supN P.primPart := by
    rw [supN_primPart_mul_content]
    rfl
  have hval : |pv ξ P| = c * |pv ξ P.primPart| := by
    have hc : |pv ξ P| = |pv ξ (C P.content * P.primPart)| := by
      exact congrArg (fun Q : Polynomial ℤ => |pv ξ Q|) (Polynomial.eq_C_content_mul_primPart P)
    rw [pv_C_mul, abs_mul] at hc
    simpa [c] using hc
  have h1 : c * |pv ξ P.primPart| ≤ (c * supN P.primPart) ^ (-e1) := by
    rw [← hval, ← hsup]
    exact hsol
  have h1' : c * |pv ξ P.primPart| ≤ c ^ (-e1) * (supN P.primPart) ^ (-e1) := by
    simpa [Real.mul_rpow hc_pos.le (supN_nonneg P.primPart)] using h1
  have h2 : |pv ξ P.primPart| ≤ (c ^ (-e1) * (supN P.primPart) ^ (-e1)) / c := by
    exact (le_div_iff₀ hc_pos).mpr (by simpa [mul_comm, mul_left_comm, mul_assoc] using h1')
  have hrew : (c ^ (-e1) * (supN P.primPart) ^ (-e1)) / c =
      c ^ (-e1 - 1) * (supN P.primPart) ^ (-e1) := by
    rw [div_eq_mul_inv]
    rw [← Real.rpow_neg_one c]
    calc
      (c ^ (-e1) * (supN P.primPart) ^ (-e1)) * c ^ (-1 : ℝ)
          = c ^ (-e1) * ((supN P.primPart) ^ (-e1) * c ^ (-1 : ℝ)) := by rw [mul_assoc]
      _ = (c ^ (-e1) * c ^ (-1 : ℝ)) * (supN P.primPart) ^ (-e1) := by ring
      _ = c ^ (-e1 + (-1 : ℝ)) * (supN P.primPart) ^ (-e1) := by
          rw [← Real.rpow_add hc_pos]
      _ = c ^ (-e1 - 1) * (supN P.primPart) ^ (-e1) := by congr 1
  have hcneg : c ^ (-e1 - 1) ≤ 1 := by
    exact Real.rpow_le_one_of_one_le_of_nonpos hc_ge1 (by linarith)
  have hnon : 0 ≤ (supN P.primPart) ^ (-e1) := Real.rpow_nonneg (supN_nonneg P.primPart) (-e1)
  calc
    |pv ξ P.primPart| ≤ (c ^ (-e1) * (supN P.primPart) ^ (-e1)) / c := h2
    _ = c ^ (-e1 - 1) * (supN P.primPart) ^ (-e1) := hrew
    _ ≤ (supN P.primPart) ^ (-e1) := by
      simpa using mul_le_of_le_one_left hnon hcneg

/-- If every primitive `e1`-solution is norm-bounded, then `e1`-solutions would be
norm-bounded: contradiction with the hypothesis.  This is the classical content-stripping
argument: write `P = content(P) · primitivePart(P)`. -/
private lemma primitive_solution_unbounded (n : ℕ) (ξ : ℝ) (hξ : Transcendental ℚ ξ)
    (e1 : ℝ) (he1 : 0 < e1)
    (hsol : ∀ H : ℝ, 0 < H → ∃ P : Polynomial ℤ, P ≠ 0 ∧ P.natDegree ≤ n ∧
      H ≤ supN P ∧ ‖pv ξ P‖ ≤ (supN P) ^ (-e1)) :
    ∀ T : ℝ, 0 < T → ∃ P0 : Polynomial ℤ, P0 ≠ 0 ∧ P0.IsPrimitive ∧ P0.natDegree ≤ n ∧
      T ≤ supN P0 ∧ ‖pv ξ P0‖ ≤ (supN P0) ^ (-e1) := by
  intro T hT
  by_contra hnot
  have hbounded : ∀ P0 : Polynomial ℤ, P0 ≠ 0 → P0.IsPrimitive → P0.natDegree ≤ n →
      ‖pv ξ P0‖ ≤ (supN P0) ^ (-e1) → supN P0 < T := by
    intro P0 hP0ne hP0prim hdeg hsol0
    by_contra hlt
    exact hnot ⟨P0, hP0ne, hP0prim, hdeg, le_of_not_gt hlt, hsol0⟩
  rcases exists_pos_small_eval_of_transcendental n T ξ hξ with ⟨m, hm_pos, hm_le1, hm_all⟩
  let K : ℝ := (1 / m) * T
  have hall_bound : ∀ P : Polynomial ℤ, P ≠ 0 → P.natDegree ≤ n →
      ‖pv ξ P‖ ≤ (supN P) ^ (-e1) → supN P ≤ K := by
    intro P hPne hdeg hsolP
    let c : ℝ := |(P.content : ℝ)|
    let P0 : Polynomial ℤ := P.primPart
    have hc_ge1 : 1 ≤ c := by
      dsimp [c]
      exact content_abs_one_le P hPne
    have hc_pos : 0 < c := lt_of_lt_of_le zero_lt_one hc_ge1
    have hP0_ne : P0 ≠ 0 := by
      dsimp [P0]
      exact Polynomial.primPart_ne_zero P
    have hP0_prim : P0.IsPrimitive := by
      dsimp [P0]
      exact Polynomial.isPrimitive_primPart P
    have hdeg0 : P0.natDegree ≤ n := by
      dsimp [P0]
      rwa [Polynomial.natDegree_primPart]
    have hsup : supN P = c * supN P0 := by
      dsimp [P0]
      rw [supN_primPart_mul_content]
      rfl
    have hval : |pv ξ P| = c * |pv ξ P0| := by
      have hc : |pv ξ P| = |pv ξ (C P.content * P0)| := by
        dsimp [P0]
        exact congrArg (fun Q : Polynomial ℤ => |pv ξ Q|) (Polynomial.eq_C_content_mul_primPart P)
      rw [pv_C_mul, abs_mul] at hc
      simpa [c] using hc
    have hP0_sol : |pv ξ P0| ≤ (supN P0) ^ (-e1) := by
      exact primPart_is_solution ξ e1 he1 hPne hsolP
    have hP0_bound : supN P0 < T := hbounded P0 hP0_ne hP0_prim hdeg0 hP0_sol
    have hP0_le : supN P0 ≤ T := le_of_lt hP0_bound
    have hP0ge1 : 1 ≤ supN P0 := supN_one_le hP0_ne
    have hm0 : m ≤ |pv ξ P0| := hm_all P0 hP0_ne hdeg0 hP0_le
    have hcm : c * m ≤ c * |pv ξ P0| := mul_le_mul_of_nonneg_left hm0 hc_pos.le
    have hcm_le : c * |pv ξ P0| ≤ |pv ξ P| := by rw [hval]
    have hcm_le' : c * m ≤ (supN P) ^ (-e1) := by
      exact le_trans (le_trans hcm hcm_le) hsolP
    have hpowneg : (supN P0) ^ (-e1) ≤ 1 := by
      exact Real.rpow_le_one_of_one_le_of_nonpos hP0ge1 (by linarith)
    have hc_pow_pos : 0 ≤ c ^ (-e1) := Real.rpow_nonneg hc_pos.le (-e1)
    have hcm2 : c * m ≤ c ^ (-e1) := by
      calc
        c * m ≤ (supN P) ^ (-e1) := hcm_le'
        _ = (c * supN P0) ^ (-e1) := by rw [hsup]
        _ = c ^ (-e1) * (supN P0) ^ (-e1) := Real.mul_rpow hc_pos.le (supN_nonneg P0)
        _ ≤ c ^ (-e1) * 1 := by
          exact mul_le_mul_of_nonneg_left hpowneg hc_pow_pos
        _ = c ^ (-e1) := by rw [mul_one]
    have hc_pow_pos' : 0 ≤ c ^ e1 := Real.rpow_nonneg hc_pos.le e1
    have hcinv : c ^ e1 * c ^ (-e1) = 1 := by
      rw [← Real.rpow_add hc_pos]
      norm_num
    have hmul : c ^ e1 * (c * m) ≤ c ^ e1 * c ^ (-e1) := by
      exact mul_le_mul_of_nonneg_left hcm2 hc_pow_pos'
    have hc1e1m : c ^ e1 * c * m ≤ 1 := by
      simpa [mul_assoc, hcinv] using hmul
    have hce : c ^ e1 * c = c ^ (e1 + 1) := by
      have h : c ^ e1 * c ^ (1 : ℝ) = c ^ (e1 + 1) := by
        rw [← Real.rpow_add hc_pos]
      simpa using h
    have hcm3 : c ^ (e1 + 1) * m ≤ 1 := by
      rw [← hce]
      simpa [mul_assoc] using hc1e1m
    have hself : c ≤ c ^ (e1 + 1) := by
      exact Real.self_le_rpow_of_one_le hc_ge1 (by linarith)
    have hcm4 : c * m ≤ 1 := by
      calc
        c * m ≤ c ^ (e1 + 1) * m := mul_le_mul_of_nonneg_right hself hm_pos.le
        _ ≤ 1 := hcm3
    have hc_bound : c ≤ 1 / m := by
      exact (le_div_iff₀ hm_pos).mpr hcm4
    calc
      supN P = c * supN P0 := hsup
      _ ≤ (1 / m) * T := by
        exact mul_le_mul hc_bound hP0_le (supN_nonneg P0) (by positivity)
      _ = K := by rfl
  let Hbig : ℝ := K + 1
  have hHbig : 0 < Hbig := by
    dsimp [Hbig, K]
    positivity
  rcases hsol Hbig hHbig with ⟨P, hPne, hdeg, hbig_le, hsolP⟩
  have hb := hall_bound P hPne hdeg hsolP
  dsimp [Hbig, K] at hbig_le
  linarith

/-! ## The core bound: without large irreducible e2-solutions, primitive e1-solutions are bounded -/

private lemma list_prod_ge_one (l : List ℝ) (h : ∀ x ∈ l, 1 ≤ x) : 1 ≤ l.prod := by
  induction l with
  | nil => simp
  | cons a l ih =>
    have ha : 1 ≤ a := h a (by simp)
    have hrest : ∀ x ∈ l, 1 ≤ x := fun x hx => h x (by exact List.mem_cons_of_mem a hx)
    calc
      (1 : ℝ) ≤ a * l.prod := by
        have hm := mul_le_mul ha (ih hrest) (by norm_num) (le_trans zero_le_one ha)
        simpa using hm
      _ = (a :: l).prod := by simp

/-- For every irreducible factor `w` of a primitive solution, `|w(ξ)| ≥ m·‖w‖^{-e}`. -/
private lemma per_factor_lower {n : ℕ} {ξ e e2 H0 : ℝ} {m : ℝ} (hm0 : 0 < m) (hm1 : m ≤ 1)
    (he0 : 0 < e) (he_gt : e2 < e)
    (hno : ∀ P : Polynomial ℤ, P ≠ 0 → Irreducible P → P.natDegree ≤ n →
      |pv ξ P| ≤ (supN P) ^ (-e2) → H0 ≤ supN P → False)
    (hm_all : ∀ P : Polynomial ℤ, P ≠ 0 → P.natDegree ≤ n →
      supN P ≤ H0 → m ≤ |pv ξ P|)
    {w : Polynomial ℤ} (hw_irr : Irreducible w) (hwne : w ≠ 0) (hwdeg : w.natDegree ≤ n) :
    m * (supN w) ^ (-e) ≤ |pv ξ w| := by
  have hwge1 : 1 ≤ supN w := supN_one_le hwne
  have hx : 0 ≤ (supN w) ^ (-e) := Real.rpow_nonneg (supN_nonneg w) (-e)
  by_cases hsmall : supN w < H0
  · have hleH : supN w ≤ H0 := le_of_lt hsmall
    have hbig_m : m ≤ |pv ξ w| := hm_all w hwne hwdeg hleH
    have hx_le1 : (supN w) ^ (-e) ≤ 1 := by
      exact Real.rpow_le_one_of_one_le_of_nonpos hwge1 (by linarith)
    have hmx : m * (supN w) ^ (-e) ≤ m := by
      exact mul_le_of_le_one_right hm0.le hx_le1
    exact le_trans hmx hbig_m
  · have hbig : H0 ≤ supN w := le_of_not_gt hsmall
    have hgt : (supN w) ^ (-e2) < |pv ξ w| := by
      by_contra hle
      exact hno w hwne hw_irr hwdeg (le_of_not_gt hle) hbig
    have hxe : (supN w) ^ (-e) ≤ (supN w) ^ (-e2) := by
      exact Real.rpow_le_rpow_of_exponent_le hwge1 (by linarith)
    have hmx : m * (supN w) ^ (-e) ≤ (supN w) ^ (-e) := by
      exact mul_le_of_le_one_left hx hm1
    exact le_trans hmx (le_trans hxe (le_of_lt hgt))

/-- Under the assumption that no irreducible polynomial satisfies the `e2`-inequality with
norm at least `H0`, every *primitive* `e1`-solution has norm bounded by a constant. -/
private lemma bounded_by_no_irreducible (n : ℕ) (ξ : ℝ) (hξ : Transcendental ℚ ξ)
    (e1 e2 : ℝ) (he1 : 0 < e1) (he2 : e2 < e1) (H0 : ℝ) (hH0 : 1 ≤ H0)
    (hno : ∀ P : Polynomial ℤ, P ≠ 0 → Irreducible P → P.natDegree ≤ n →
      |pv ξ P| ≤ (supN P) ^ (-e2) → supN P < H0) :
    ∃ M0 : ℝ, ∀ P0 : Polynomial ℤ, P0 ≠ 0 → P0.IsPrimitive → P0.natDegree ≤ n →
      |pv ξ P0| ≤ (supN P0) ^ (-e1) → supN P0 ≤ M0 := by
  classical
  rcases gelfond_supNorm_list_prod n with ⟨C, hC1, hC⟩
  have hC0 : 0 < C := lt_of_lt_of_le zero_lt_one hC1
  have hC_nonneg : 0 ≤ C := hC0.le
  rcases exists_pos_small_eval_of_transcendental n H0 ξ hξ with ⟨m, hm0, hm1, hm⟩
  have hm0_le : 0 ≤ m := hm0.le
  let e : ℝ := (e1 + max e2 0) / 2
  have hmaxlt : max e2 0 < e1 := by
    rw [max_lt_iff]
    exact ⟨he2, he1⟩
  have he0 : 0 < e := by
    dsimp [e]
    have hmax0 : 0 ≤ max e2 0 := le_max_right e2 0
    linarith
  have hle_max : e2 ≤ max e2 0 := le_max_left e2 0
  have he_gt_e2 : e2 < e := by
    dsimp [e]
    linarith
  have hneg_e : -e ≤ 0 := by linarith
  have he1e : 0 < e1 - e := by
    dsimp [e]
    linarith
  have hno_contra : ∀ P : Polynomial ℤ, P ≠ 0 → Irreducible P → P.natDegree ≤ n →
      |pv ξ P| ≤ (supN P) ^ (-e2) → H0 ≤ supN P → False := by
    intro P hPne hPirr hdeg hsolP hH
    exact (not_lt_of_ge hH) (hno P hPne hPirr hdeg hsolP)
  let expB : ℝ := (C ^ e * (1 / m) ^ n) ^ (1 / (e1 - e))
  let M0 : ℝ := max expB (H0 + 1)
  refine ⟨M0, ?_⟩
  intro P0 hP0ne hprim hdeg hsolP0
  by_contra hleM
  have hgtM : M0 < supN P0 := lt_of_not_ge hleM
  have hP0_ge2 : 2 ≤ supN P0 := by
    have : H0 + 1 ≤ M0 := le_max_right expB (H0 + 1)
    linarith
  have hnu : ¬ IsUnit P0 := primitive_not_unit_of_supN_two_le hprim hP0_ge2
  rcases exists_irreducible_list_factorization P0 hP0ne hprim hnu hdeg with ⟨ws, hwsprod, hlen, hprops⟩
  have hne_all : ∀ w ∈ ws, w ≠ 0 := fun w hw => (hprops w hw).2.2.2
  have hdeg_all : ∀ w ∈ ws, w.natDegree ≤ n := fun w hw => (hprops w hw).2.2.1
  have hirr_all : ∀ w ∈ ws, Irreducible w := fun w hw => (hprops w hw).1
  have hfac : ∀ w ∈ ws, m * (supN w) ^ (-e) ≤ |pv ξ w| := by
    intro w hw
    exact per_factor_lower (ξ := ξ) (e := e) (e2 := e2) (H0 := H0) (m := m)
      hm0 hm1 he0 he_gt_e2 hno_contra hm (hirr_all w hw) (hne_all w hw) (hdeg_all w hw)
  have hprod1 : |pv ξ P0| = (ws.map (fun w : Polynomial ℤ => |pv ξ w|)).prod := by
    rw [← hwsprod, abs_pv_list_prod]
  have hnonneg_map : ∀ w ∈ ws, 0 ≤ m * (supN w) ^ (-e) := by
    intro w hw
    exact mul_nonneg hm0_le (Real.rpow_nonneg (supN_nonneg w) (-e))
  have hprod2 : (ws.map (fun w : Polynomial ℤ => m * (supN w) ^ (-e))).prod ≤
      (ws.map (fun w : Polynomial ℤ => |pv ξ w|)).prod := by
    exact list_prod_map_le_map ws (fun w : Polynomial ℤ => m * (supN w) ^ (-e))
      (fun w : Polynomial ℤ => |pv ξ w|) hnonneg_map (fun w hw => hfac w hw)
  have hprod3 : (ws.map (fun w : Polynomial ℤ => m * (supN w) ^ (-e))).prod =
      m ^ ws.length * (ws.map (fun w : Polynomial ℤ => (supN w) ^ (-e))).prod := by
    exact list_prod_const_mul ws m (fun w : Polynomial ℤ => (supN w) ^ (-e))
  have hsup_map_nonneg : ∀ x ∈ ws.map supN, 0 ≤ x := by
    intro x hx
    rcases List.mem_map.mp hx with ⟨w, hw, rfl⟩
    exact supN_nonneg w
  have hprod4 : (ws.map (fun w : Polynomial ℤ => (supN w) ^ (-e))).prod =
      ((ws.map supN).prod) ^ (-e) := by
    rw [← list_prod_rpow (ws.map supN) (-e) hsup_map_nonneg]
    simp [List.map_map, Function.comp_def]
  have hsup_map_ge1 : ∀ x ∈ ws.map supN, 1 ≤ x := by
    intro x hx
    rcases List.mem_map.mp hx with ⟨w, hw, rfl⟩
    exact supN_one_le (hne_all w hw)
  have hprod_ge1 : 1 ≤ (ws.map supN).prod := list_prod_ge_one (ws.map supN) hsup_map_ge1
  have hprod_pos : 0 < (ws.map supN).prod := lt_of_lt_of_le zero_lt_one hprod_ge1
  have hpow_mono : m ^ n ≤ m ^ ws.length := by
    have hdiff : m ^ (n - ws.length) ≤ 1 := by
      exact pow_le_one₀ (n := n - ws.length) hm0_le hm1
    have hm_len_nonneg : 0 ≤ m ^ ws.length := pow_nonneg hm0_le ws.length
    calc
      m ^ n = m ^ ws.length * m ^ (n - ws.length) := by
        rw [← pow_add]
        congr 1
        omega
      _ ≤ m ^ ws.length * 1 := by
        exact mul_le_mul_of_nonneg_left hdiff hm_len_nonneg
      _ = m ^ ws.length := by rw [mul_one]
  have hprod5 : m ^ n * ((ws.map supN).prod) ^ (-e) ≤ m ^ ws.length * ((ws.map supN).prod) ^ (-e) := by
    exact mul_le_mul_of_nonneg_right hpow_mono (Real.rpow_nonneg (le_of_lt hprod_pos) (-e))
  have hgelfond : (ws.map supN).prod ≤ C * supN P0 := by
    have hg := hC ws hlen hne_all hdeg_all
    rw [hwsprod] at hg
    exact hg
  have hX_ge : (C * supN P0) ^ (-e) ≤ ((ws.map supN).prod) ^ (-e) := by
    exact Real.rpow_le_rpow_of_nonpos hprod_pos hgelfond hneg_e
  have hX_ge' : (C * supN P0) ^ (-e) = C ^ (-e) * (supN P0) ^ (-e) :=
    Real.mul_rpow hC_nonneg (supN_nonneg P0)
  have hchain1 : m ^ n * (C * supN P0) ^ (-e) ≤ |pv ξ P0| := by
    calc
      m ^ n * (C * supN P0) ^ (-e) ≤ m ^ n * ((ws.map supN).prod) ^ (-e) := by
        exact mul_le_mul_of_nonneg_left hX_ge (pow_nonneg hm0_le n)
      _ ≤ m ^ ws.length * ((ws.map supN).prod) ^ (-e) := hprod5
      _ = m ^ ws.length * (ws.map (fun w : Polynomial ℤ => (supN w) ^ (-e))).prod := by
        rw [← hprod4]
      _ = (ws.map (fun w : Polynomial ℤ => m * (supN w) ^ (-e))).prod := hprod3.symm
      _ ≤ (ws.map (fun w : Polynomial ℤ => |pv ξ w|)).prod := hprod2
      _ = |pv ξ P0| := hprod1.symm
  have hu0 : 0 < supN P0 := by
    have h1 : 1 ≤ supN P0 := supN_one_le hP0ne
    linarith
  have hsol_chain : m ^ n * (C * supN P0) ^ (-e) ≤ (supN P0) ^ (-e1) := by
    exact le_trans hchain1 hsolP0
  have hcomb : m ^ n * (C ^ (-e) * (supN P0) ^ (-e)) ≤ (supN P0) ^ (-e1) := by
    rwa [hX_ge'] at hsol_chain
  have hpow_e1 : 0 ≤ (supN P0) ^ e1 := Real.rpow_nonneg (supN_nonneg P0) e1
  have hmul2 : (m ^ n * (C ^ (-e) * (supN P0) ^ (-e))) * (supN P0) ^ e1 ≤
      (supN P0) ^ (-e1) * (supN P0) ^ e1 := by
    exact mul_le_mul_of_nonneg_right hcomb hpow_e1
  have huu : (supN P0) ^ (-e) * (supN P0) ^ e1 = (supN P0) ^ (e1 - e) := by
    rw [← Real.rpow_add hu0]
    congr 1
    ring
  have hleft : (m ^ n * (C ^ (-e) * (supN P0) ^ (-e))) * (supN P0) ^ e1 =
      m ^ n * C ^ (-e) * (supN P0) ^ (e1 - e) := by
    calc
      (m ^ n * (C ^ (-e) * (supN P0) ^ (-e))) * (supN P0) ^ e1
          = m ^ n * C ^ (-e) * ((supN P0) ^ (-e) * (supN P0) ^ e1) := by ring
      _ = m ^ n * C ^ (-e) * (supN P0) ^ (e1 - e) := by rw [huu]
  have hright : (supN P0) ^ (-e1) * (supN P0) ^ e1 = 1 := by
    rw [← Real.rpow_add hu0]
    have : -e1 + e1 = 0 := by ring
    rw [this, Real.rpow_zero]
  have hineq : m ^ n * C ^ (-e) * (supN P0) ^ (e1 - e) ≤ 1 := by
    simpa [hleft, hright] using hmul2
  have hCC : C ^ (-e) * C ^ e = 1 := by
    rw [← Real.rpow_add hC0]
    have : -e + e = 0 := by ring
    rw [this, Real.rpow_zero]
  have hCpow_nonneg : 0 ≤ C ^ e := Real.rpow_nonneg hC_nonneg e
  have hmulA : m ^ n * C ^ (-e) * (supN P0) ^ (e1 - e) * C ^ e ≤ C ^ e := by
    simpa using (mul_le_mul_of_nonneg_right hineq hCpow_nonneg)
  have hA : m ^ n * (supN P0) ^ (e1 - e) ≤ C ^ e := by
    have hstep : (m ^ n * (C ^ (-e) * (supN P0) ^ (e1 - e))) * C ^ e ≤ C ^ e := by
      simpa [mul_assoc, mul_left_comm, mul_comm] using hmulA
    have hrew : (m ^ n * (C ^ (-e) * (supN P0) ^ (e1 - e))) * C ^ e =
        m ^ n * (supN P0) ^ (e1 - e) := by
      calc
        (m ^ n * (C ^ (-e) * (supN P0) ^ (e1 - e))) * C ^ e
            = m ^ n * ((C ^ (-e) * (supN P0) ^ (e1 - e)) * C ^ e) := by ring
        _ = m ^ n * (C ^ (-e) * C ^ e * (supN P0) ^ (e1 - e)) := by ring
        _ = m ^ n * (supN P0) ^ (e1 - e) := by rw [hCC]; ring
    rwa [hrew] at hstep
  have hm_inv_pow : m ^ n * (1 / m) ^ n = 1 := by
    have hmul : m * (1 / m) = 1 := by field_simp [hm0.ne']
    rw [← mul_pow, hmul, one_pow]
  have hm_inv_nonneg : 0 ≤ (1 / m) ^ n := pow_nonneg (by positivity) n
  have hmulB : m ^ n * (supN P0) ^ (e1 - e) * (1 / m) ^ n ≤ C ^ e * (1 / m) ^ n := by
    exact mul_le_mul_of_nonneg_right hA hm_inv_nonneg
  have hB : (supN P0) ^ (e1 - e) ≤ C ^ e * (1 / m) ^ n := by
    have hrew : m ^ n * (supN P0) ^ (e1 - e) * (1 / m) ^ n =
        (supN P0) ^ (e1 - e) := by
      calc
        m ^ n * (supN P0) ^ (e1 - e) * (1 / m) ^ n
            = (m ^ n * (1 / m) ^ n) * (supN P0) ^ (e1 - e) := by ring
        _ = (supN P0) ^ (e1 - e) := by rw [hm_inv_pow]; ring
    rwa [hrew] at hmulB
  have hM' : supN P0 ≤ (C ^ e * (1 / m) ^ n) ^ (1 / (e1 - e)) := by
    have hd : 0 < 1 / (e1 - e) := by positivity
    have hstep := Real.rpow_le_rpow (Real.rpow_nonneg (supN_nonneg P0) (e1 - e)) hB (le_of_lt hd)
    rw [← Real.rpow_mul (supN_nonneg P0)] at hstep
    have hk : (e1 - e) * (1 / (e1 - e)) = 1 := by field_simp [he1e.ne']
    rw [hk, Real.rpow_one] at hstep
    exact hstep
  have hfin : supN P0 ≤ expB := by
    dsimp [expB]
    exact hM'
  have hfin2 : supN P0 ≤ M0 := by
    exact le_trans hfin (le_max_left expB (H0 + 1))
  exact hleM hfin2

/-! ## The main theorem -/

theorem wirsing_irreducible_solutions (n : ℕ) (hn : 2 ≤ n) (ξ : ℝ)
    (hξ : Transcendental ℚ ξ) (e1 : ℝ) (he1 : 0 < e1)
    (hsol : ∀ H : ℝ, 0 < H → ∃ P : Polynomial ℤ, P ≠ 0 ∧ P.natDegree ≤ n ∧
      H ≤ (P.map (Int.castRingHom ℝ)).supNorm ∧
      ‖Polynomial.eval ξ (P.map (Int.castRingHom ℝ))‖ ≤
        ((P.map (Int.castRingHom ℝ)).supNorm) ^ (-e1)) :
    ∀ e2 : ℝ, e2 < e1 → ∀ H : ℝ, 0 < H → ∃ P : Polynomial ℤ,
      P ≠ 0 ∧ Irreducible P ∧ P.natDegree ≤ n ∧
      H ≤ (P.map (Int.castRingHom ℝ)).supNorm ∧
      ‖Polynomial.eval ξ (P.map (Int.castRingHom ℝ))‖ ≤
        ((P.map (Int.castRingHom ℝ)).supNorm) ^ (-e2) := by
  intro e2 he2 H hH
  let H0 : ℝ := max H 1
  have hH0ge : 1 ≤ H0 := le_max_right H 1
  have hHle : H ≤ H0 := le_max_left H 1
  suffices hs : ∃ P : Polynomial ℤ, P ≠ 0 ∧ Irreducible P ∧ P.natDegree ≤ n ∧
      H0 ≤ (P.map (Int.castRingHom ℝ)).supNorm ∧
      ‖Polynomial.eval ξ (P.map (Int.castRingHom ℝ))‖ ≤
        ((P.map (Int.castRingHom ℝ)).supNorm) ^ (-e2)
  · rcases hs with ⟨P, hPne, hIrr, hdeg, hH0le, hsolP⟩
    refine ⟨P, hPne, hIrr, hdeg, ?_, hsolP⟩
    exact le_trans hHle hH0le
  · by_contra hno
    have hno_std : ∀ P : Polynomial ℤ, P ≠ 0 → Irreducible P → P.natDegree ≤ n →
        |pv ξ P| ≤ (supN P) ^ (-e2) → supN P < H0 := by
      intro P hPne hPirr hdeg hsolP
      by_contra hlt
      exact hno ⟨P, hPne, hPirr, hdeg, le_of_not_gt hlt, hsolP⟩
    rcases bounded_by_no_irreducible n ξ hξ e1 e2 he1 he2 H0 hH0ge hno_std with ⟨M0, hM0⟩
    let T : ℝ := max (M0 + 1) 2
    have hT : 0 < T := by
      dsimp [T]
      positivity
    have hsol' : ∀ H : ℝ, 0 < H → ∃ P : Polynomial ℤ, P ≠ 0 ∧ P.natDegree ≤ n ∧
        H ≤ supN P ∧ ‖pv ξ P‖ ≤ (supN P) ^ (-e1) := by
      simpa [supN, pv] using hsol
    rcases primitive_solution_unbounded n ξ hξ e1 he1 hsol' T hT with
      ⟨P0, hP0ne, hP0prim, hdeg0, hTle, hsol0⟩
    have hM0le := hM0 P0 hP0ne hP0prim hdeg0 hsol0
    have hTle' : M0 + 1 ≤ supN P0 := by
      have : max (M0 + 1) 2 ≤ supN P0 := by simpa [T] using hTle
      exact le_trans (le_max_left (M0 + 1) 2) this
    linarith

end
