import Mathlib
import Submission.Work.A7REC.Defs
import Submission.Work.A7REC.Char.a7TableDefs
import Submission.Work.A7REC.Char.fTuples_complete

/-!
# The A₇ table lemma

The statement `Work.A7REC.A7TableLemmaProp` is a finite arithmetic fact: an index set with the
`A₇` involution-pair data is forced to be the `A₇` character table.  The proof splits it into

* a *computational* verification (`p1Out_all`, `p2Out_C1`, `p2Out_C0`, `p2Out_C2`), checked by
  `decide` on the small enumerations of `a7TableDefs`;
* the corresponding *completeness* lemmas (`enumItems_complete` for the `e = 0` part and
  `p1_complete` for the `e ≠ 0` part), which say that every genuine solution is reached by the
  enumeration;
* the bridge from the `Fin n` formulation of `A7TableLemmaProp` to multisets of `It`.
-/

namespace Work.A7REC.Char

open It

set_option maxRecDepth 100000
set_option maxHeartbeats 0

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
/-- **Phase 1 (computation).**  Every triple produced by the reconstruction is one of the three
candidates. -/
theorem p1Out_all :
    p1Out.all (fun l => decide (l.Perm C0 ∨ l.Perm C1 ∨ l.Perm C2)) = true := by
  decide

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
/-- **Phase 2 (computation), candidate `C1`.**  Every solution of the residual problem is a
permutation of the `A₇` `e = 0` data. -/
theorem p2Out_C1 :
    (p2Out 4 4 0 0 28 2208 1056 628).all (fun l => decide (l.Perm C1T)) = true := by
  decide

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
/-- **Phase 2 (computation), candidate `C0`.**  No solution. -/
theorem p2Out_C0 : p2Out 2 4 (-2) 6 40 2208 912 628 = [] := by decide

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
/-- **Phase 2 (computation), candidate `C2`.**  No solution. -/
theorem p2Out_C2 : p2Out 2 4 (-2) (-50) (-72) 2208 336 628 = [] := by decide

/-! ## Generic facts on the sum functionals -/

theorem sumA2_append (l₁ l₂ : List It) : sumA2 (l₁ ++ l₂) = sumA2 l₁ + sumA2 l₂ := by
  simp [sumA2, List.map_append, List.sum_append]

theorem sumB2_append (l₁ l₂ : List It) : sumB2 (l₁ ++ l₂) = sumB2 l₁ + sumB2 l₂ := by
  simp [sumB2, List.map_append, List.sum_append]

theorem sumAB_append (l₁ l₂ : List It) : sumAB (l₁ ++ l₂) = sumAB l₁ + sumAB l₂ := by
  simp [sumAB, List.map_append, List.sum_append]

theorem sumAF_append (l₁ l₂ : List It) : sumAF (l₁ ++ l₂) = sumAF l₁ + sumAF l₂ := by
  simp [sumAF, List.map_append, List.sum_append]

theorem sumBF_append (l₁ l₂ : List It) : sumBF (l₁ ++ l₂) = sumBF l₁ + sumBF l₂ := by
  simp [sumBF, List.map_append, List.sum_append]

theorem sumF2_append (l₁ l₂ : List It) : sumF2 (l₁ ++ l₂) = sumF2 l₁ + sumF2 l₂ := by
  simp [sumF2, List.map_append, List.sum_append]

theorem sumC3W_append (l₁ l₂ : List It) : sumC3W (l₁ ++ l₂) = sumC3W l₁ + sumC3W l₂ := by
  simp [sumC3W, List.map_append, List.sum_append]

theorem sumC2ABW_append (l₁ l₂ : List It) :
    sumC2ABW (l₁ ++ l₂) = sumC2ABW l₁ + sumC2ABW l₂ := by
  simp [sumC2ABW, List.map_append, List.sum_append]

theorem sumE2_append (l₁ l₂ : List It) : sumE2 (l₁ ++ l₂) = sumE2 l₁ + sumE2 l₂ := by
  simp [sumE2, List.map_append, List.sum_append]

theorem sumEA_append (l₁ l₂ : List It) : sumEA (l₁ ++ l₂) = sumEA l₁ + sumEA l₂ := by
  simp [sumEA, List.map_append, List.sum_append]

theorem sumEB_append (l₁ l₂ : List It) : sumEB (l₁ ++ l₂) = sumEB l₁ + sumEB l₂ := by
  simp [sumEB, List.map_append, List.sum_append]

theorem sumEF_append (l₁ l₂ : List It) : sumEF (l₁ ++ l₂) = sumEF l₁ + sumEF l₂ := by
  simp [sumEF, List.map_append, List.sum_append]

theorem sumC2EW_append (l₁ l₂ : List It) :
    sumC2EW (l₁ ++ l₂) = sumC2EW l₁ + sumC2EW l₂ := by
  simp [sumC2EW, List.map_append, List.sum_append]

/-! ## Multiset/list bridges for the sum functionals -/

theorem sumA2M_coe (l : List It) : sumA2M (↑l) = sumA2 l := by
  simp [sumA2M, sumA2, Multiset.map_coe, Multiset.sum_coe]

theorem sumB2M_coe (l : List It) : sumB2M (↑l) = sumB2 l := by
  simp [sumB2M, sumB2, Multiset.map_coe, Multiset.sum_coe]

theorem sumABM_coe (l : List It) : sumABM (↑l) = sumAB l := by
  simp [sumABM, sumAB, Multiset.map_coe, Multiset.sum_coe]

theorem sumAFM_coe (l : List It) : sumAFM (↑l) = sumAF l := by
  simp [sumAFM, sumAF, Multiset.map_coe, Multiset.sum_coe]

theorem sumBFM_coe (l : List It) : sumBFM (↑l) = sumBF l := by
  simp [sumBFM, sumBF, Multiset.map_coe, Multiset.sum_coe]

theorem sumF2M_coe (l : List It) : sumF2M (↑l) = sumF2 l := by
  simp [sumF2M, sumF2, Multiset.map_coe, Multiset.sum_coe]

theorem sumC2EWM_coe (l : List It) : sumC2EWM (↑l) = sumC2EW l := by
  simp [sumC2EWM, sumC2EW, Multiset.map_coe, Multiset.sum_coe]

theorem sumC3WM_coe (l : List It) : sumC3WM (↑l) = sumC3W l := by
  simp [sumC3WM, sumC3W, Multiset.map_coe, Multiset.sum_coe]

theorem sumC2ABWM_coe (l : List It) : sumC2ABWM (↑l) = sumC2ABW l := by
  simp [sumC2ABWM, sumC2ABW, Multiset.map_coe, Multiset.sum_coe]

theorem sumE2M_coe (l : List It) : sumE2M (↑l) = sumE2 l := by
  simp [sumE2M, sumE2, Multiset.map_coe, Multiset.sum_coe]

theorem sumEAM_coe (l : List It) : sumEAM (↑l) = sumEA l := by
  simp [sumEAM, sumEA, Multiset.map_coe, Multiset.sum_coe]

theorem sumEBM_coe (l : List It) : sumEBM (↑l) = sumEB l := by
  simp [sumEBM, sumEB, Multiset.map_coe, Multiset.sum_coe]

theorem sumEFM_coe (l : List It) : sumEFM (↑l) = sumEF l := by
  simp [sumEFM, sumEF, Multiset.map_coe, Multiset.sum_coe]

/-! ## Per-index bounds -/

theorem a7_bounds (n : ℕ) (f : Fin n → ℕ) (e a b : Fin n → ℤ)
    (hnz : ∀ i, e i ≠ 0 ∨ a i ≠ 0 ∨ b i ≠ 0)
    (hf2 : ∀ i, 2 ≤ f i) (hfdiv : ∀ i, f i ∣ 2520)
    (he2 : ∑ i, (e i) ^ 2 = 3) (ha2 : ∑ i, (a i) ^ 2 = 4) (hb2 : ∑ i, (b i) ^ 2 = 7)
    (hle : 1 + ∑ i, (f i) ^ 2 ≤ 2520)
    (hcong : ∀ i, ((f i : ℤ) + 5 * (b i - 2 * a i) + 2 * e i) % 8 = 0)
    (i : Fin n) : ((⟨e i, a i, b i, f i⟩ : It)).valid := by
  have he3 : (e i) ^ 2 ≤ 3 := by
    have hnn : ∀ j ∈ (Finset.univ : Finset (Fin n)), (0 : ℤ) ≤ (e j) ^ 2 :=
      fun j _ => by positivity
    have h := Finset.single_le_sum hnn (Finset.mem_univ i)
    simpa [he2] using h
  have ha4 : (a i) ^ 2 ≤ 4 := by
    have hnn : ∀ j ∈ (Finset.univ : Finset (Fin n)), (0 : ℤ) ≤ (a j) ^ 2 :=
      fun j _ => by positivity
    have h := Finset.single_le_sum hnn (Finset.mem_univ i)
    simpa [ha2] using h
  have hb7 : (b i) ^ 2 ≤ 7 := by
    have hnn : ∀ j ∈ (Finset.univ : Finset (Fin n)), (0 : ℤ) ≤ (b j) ^ 2 :=
      fun j _ => by positivity
    have h := Finset.single_le_sum hnn (Finset.mem_univ i)
    simpa [hb2] using h
  have hsumf : ∑ j, (f j) ^ 2 ≤ 2519 := by omega
  have hf1 : (f i) ^ 2 ≤ 2519 := by
    have hnn : ∀ j ∈ (Finset.univ : Finset (Fin n)), (0 : ℕ) ≤ (f j) ^ 2 :=
      fun j _ => by positivity
    have h := Finset.single_le_sum hnn (Finset.mem_univ i)
    omega
  have he_le : e i ≤ 1 := by
    by_contra hc
    push_neg at hc
    have h2 : 2 ≤ e i := by omega
    have : 4 ≤ (e i) ^ 2 := by nlinarith
    omega
  have he_ge : -1 ≤ e i := by
    by_contra hc
    push_neg at hc
    have h2 : e i ≤ -2 := by omega
    have : 4 ≤ (e i) ^ 2 := by nlinarith [sq_nonneg (e i + 2)]
    omega
  have ha_le : a i ≤ 2 := by
    by_contra hc
    push_neg at hc
    have h3 : 3 ≤ a i := by omega
    have : 9 ≤ (a i) ^ 2 := by nlinarith
    omega
  have ha_ge : -2 ≤ a i := by
    by_contra hc
    push_neg at hc
    have h3 : a i ≤ -3 := by omega
    have : 9 ≤ (a i) ^ 2 := by nlinarith
    omega
  have hb_le : b i ≤ 2 := by
    by_contra hc
    push_neg at hc
    have h3 : 3 ≤ b i := by omega
    have : 9 ≤ (b i) ^ 2 := by nlinarith
    omega
  have hb_ge : -2 ≤ b i := by
    by_contra hc
    push_neg at hc
    have h3 : b i ≤ -3 := by omega
    have : 9 ≤ (b i) ^ 2 := by nlinarith
    omega
  have hf50 : f i ≤ 50 := by
    by_contra hc
    push_neg at hc
    have h51 : 51 ≤ f i := by omega
    have : 2601 ≤ (f i) ^ 2 := by nlinarith
    omega
  have he_disj : e i = -1 ∨ e i = 0 ∨ e i = 1 := by omega
  exact ⟨he_disj, ⟨⟨ha_ge, ha_le⟩, ⟨hb_ge, hb_le⟩, hf2 i, hf50, hfdiv i, hcong i⟩⟩

/-! ## Permutation invariance of the sum functionals -/

theorem sumA2_perm {l₁ l₂ : List It} (h : l₁.Perm l₂) : sumA2 l₁ = sumA2 l₂ := by
  simp only [sumA2]
  exact (h.map (fun x => x.a ^ 2)).sum_eq

theorem sumB2_perm {l₁ l₂ : List It} (h : l₁.Perm l₂) : sumB2 l₁ = sumB2 l₂ := by
  simp only [sumB2]
  exact (h.map (fun x => x.b ^ 2)).sum_eq

theorem sumAB_perm {l₁ l₂ : List It} (h : l₁.Perm l₂) : sumAB l₁ = sumAB l₂ := by
  simp only [sumAB]
  exact (h.map (fun x => x.a * x.b)).sum_eq

theorem sumAF_perm {l₁ l₂ : List It} (h : l₁.Perm l₂) : sumAF l₁ = sumAF l₂ := by
  simp only [sumAF]
  exact (h.map (fun x => x.a * Int.ofNat x.f)).sum_eq

theorem sumBF_perm {l₁ l₂ : List It} (h : l₁.Perm l₂) : sumBF l₁ = sumBF l₂ := by
  simp only [sumBF]
  exact (h.map (fun x => x.b * Int.ofNat x.f)).sum_eq

theorem sumF2_perm {l₁ l₂ : List It} (h : l₁.Perm l₂) : sumF2 l₁ = sumF2 l₂ := by
  simp only [sumF2]
  exact (h.map (fun x => Int.ofNat x.f ^ 2)).sum_eq

theorem sumC2EW_perm {l₁ l₂ : List It} (h : l₁.Perm l₂) : sumC2EW l₁ = sumC2EW l₂ := by
  simp only [sumC2EW]
  exact (h.map (fun x => x.c ^ 2 * x.e * x.w)).sum_eq

theorem sumC3W_perm {l₁ l₂ : List It} (h : l₁.Perm l₂) : sumC3W l₁ = sumC3W l₂ := by
  simp only [sumC3W]
  exact (h.map (fun x => x.c ^ 3 * x.w)).sum_eq

theorem sumC2ABW_perm {l₁ l₂ : List It} (h : l₁.Perm l₂) : sumC2ABW l₁ = sumC2ABW l₂ := by
  simp only [sumC2ABW]
  exact (h.map (fun x => x.c ^ 2 * (x.a + x.b) * x.w)).sum_eq

/-! ## Basic facts about the item list of one type -/

/-- A list all of whose items have type `t` and `e = 0` is `itemsOf t (its degrees)`. -/
theorem eq_itemsOf_of_forall {t : ℤ × ℤ} {m : List It}
    (h1 : ∀ x ∈ m, x.typ = t) (h2 : ∀ x ∈ m, x.e = 0) :
    m = itemsOf t (m.map (fun x => x.f)) := by
  have hstep : ∀ x ∈ m, (⟨0, t.1, t.2, x.f⟩ : It) = x := by
    intro x hx
    have hx1 : x.a = t.1 := congrArg Prod.fst (h1 x hx)
    have hx2 : x.b = t.2 := congrArg Prod.snd (h1 x hx)
    have hxe : x.e = 0 := h2 x hx
    cases x with
    | mk e a b ff =>
      simp only [It.mk.injEq]
      exact ⟨hxe.symm, hx1.symm, hx2.symm, trivial⟩
  calc m = m.map id := (List.map_id m).symm
    _ = m.map ((fun ff => (⟨0, t.1, t.2, ff⟩ : It)) ∘ fun x : It => x.f) := by
        rw [List.map_inj_left]
        intro x hx
        exact (hstep x hx).symm
    _ = (m.map (fun x : It => x.f)).map (fun ff => (⟨0, t.1, t.2, ff⟩ : It)) :=
        (List.map_map).symm
    _ = itemsOf t (m.map fun x : It => x.f) := rfl

/-! ## Bounds used by the prunings of `enumItems` -/

theorem abs_sum_le_abs_sum (l : List ℤ) : |l.sum| ≤ (l.map abs).sum := by
  induction l with
  | nil => simp
  | cons x xs ih =>
    have h1 : (x :: xs).sum = x + xs.sum := List.sum_cons ..
    have h2 : ((x :: xs).map abs).sum = |x| + (xs.map abs).sum := by
      rw [List.map_cons, List.sum_cons]
    rw [h1, h2]
    calc |x + xs.sum| ≤ |x| + |xs.sum| := abs_add_le x xs.sum
      _ ≤ |x| + (xs.map abs).sum := by linarith

theorem two_mul_mul_le (a b : ℤ) : 2 * (a * b) ≤ a ^ 2 + b ^ 2 := by
  nlinarith [sq_nonneg (a - b)]

theorem neg_two_mul_mul_le (a b : ℤ) : -(2 * (a * b)) ≤ a ^ 2 + b ^ 2 := by
  nlinarith [sq_nonneg (a + b)]

theorem sumAB_upper (l : List It) : 2 * sumAB l ≤ sumA2 l + sumB2 l := by
  induction l with
  | nil => simp [sumAB, sumA2, sumB2]
  | cons x xs ih =>
    have h1 : sumAB (x :: xs) = x.a * x.b + sumAB xs := by simp [sumAB]
    have h2 : sumA2 (x :: xs) = x.a ^ 2 + sumA2 xs := by simp [sumA2]
    have h3 : sumB2 (x :: xs) = x.b ^ 2 + sumB2 xs := by simp [sumB2]
    rw [h1, h2, h3]
    have := two_mul_mul_le x.a x.b
    linarith

theorem sumAB_lower (l : List It) : -(2 * sumAB l) ≤ sumA2 l + sumB2 l := by
  induction l with
  | nil => simp [sumAB, sumA2, sumB2]
  | cons x xs ih =>
    have h1 : sumAB (x :: xs) = x.a * x.b + sumAB xs := by simp [sumAB]
    have h2 : sumA2 (x :: xs) = x.a ^ 2 + sumA2 xs := by simp [sumA2]
    have h3 : sumB2 (x :: xs) = x.b ^ 2 + sumB2 xs := by simp [sumB2]
    rw [h1, h2, h3]
    have := neg_two_mul_mul_le x.a x.b
    linarith

theorem abs_sumAB_le (l : List It) : |sumAB l| ≤ (sumA2 l + sumB2 l) / 2 := by
  rw [abs_le]
  exact ⟨by have h := sumAB_lower l; omega, by have h := sumAB_upper l; omega⟩

theorem abs_mul_le_50_sq (a f : ℤ) (ha : |a| ≤ 2) (hf0 : 0 ≤ f) (hf : f ≤ 24) :
    |a * f| ≤ 50 * a ^ 2 := by
  rcases eq_or_ne a 0 with h | h
  · rw [h]; simp
  · have h4 : 1 ≤ |a| := by
      have := abs_pos.mpr h
      omega
    have h5 : 1 ≤ a ^ 2 := by nlinarith [sq_abs a]
    have h6 : |a * f| = |a| * f := by rw [abs_mul, abs_of_nonneg hf0]
    rw [h6]
    nlinarith

theorem abs_sumAF_le (l : List It) (ha : ∀ x ∈ l, |x.a| ≤ 2) (hf : ∀ x ∈ l, x.f ≤ 24) :
    |sumAF l| ≤ 50 * sumA2 l := by
  have hp : ∀ x ∈ l, |x.a * (x.f : ℤ)| ≤ 50 * x.a ^ 2 :=
    fun x hx => abs_mul_le_50_sq x.a (x.f : ℤ) (ha x hx) (by positivity) (by exact_mod_cast hf x hx)
  have h1 : |sumAF l| = |(l.map (fun x => x.a * (x.f : ℤ))).sum| := rfl
  rw [h1]
  calc |(l.map (fun x => x.a * (x.f : ℤ))).sum|
      ≤ ((l.map (fun x => x.a * (x.f : ℤ))).map abs).sum := abs_sum_le_abs_sum _
    _ = (l.map (fun x => |x.a * (x.f : ℤ)|)).sum := by rw [List.map_map]; rfl
    _ ≤ (l.map (fun x => 50 * x.a ^ 2)).sum := List.sum_le_sum (fun x hx => hp x hx)
    _ = 50 * sumA2 l := by
        rw [sumA2]
        exact List.sum_map_mul_left l (fun x : It => x.a ^ 2) 50

theorem abs_sumBF_le (l : List It) (hb : ∀ x ∈ l, |x.b| ≤ 2) (hf : ∀ x ∈ l, x.f ≤ 24) :
    |sumBF l| ≤ 50 * sumB2 l := by
  have hp : ∀ x ∈ l, |x.b * (x.f : ℤ)| ≤ 50 * x.b ^ 2 :=
    fun x hx => abs_mul_le_50_sq x.b (x.f : ℤ) (hb x hx) (by positivity) (by exact_mod_cast hf x hx)
  have h1 : |sumBF l| = |(l.map (fun x => x.b * (x.f : ℤ))).sum| := rfl
  rw [h1]
  calc |(l.map (fun x => x.b * (x.f : ℤ))).sum|
      ≤ ((l.map (fun x => x.b * (x.f : ℤ))).map abs).sum := abs_sum_le_abs_sum _
    _ = (l.map (fun x => |x.b * (x.f : ℤ)|)).sum := by rw [List.map_map]; rfl
    _ ≤ (l.map (fun x => 50 * x.b ^ 2)).sum := List.sum_le_sum (fun x hx => hp x hx)
    _ = 50 * sumB2 l := by
        rw [sumB2]
        exact List.sum_map_mul_left l (fun x : It => x.b ^ 2) 50

/-! ## Small helper facts -/

theorem sum_map_const {α : Type*} (l : List α) (g : α → ℤ) (c : ℤ)
    (h : ∀ x ∈ l, g x = c) : (l.map g).sum = (l.length : ℤ) * c := by
  induction l with
  | nil => simp
  | cons x xs ih =>
    rw [List.map_cons, List.sum_cons, List.length_cons]
    rw [h x (by simp), ih (fun y hy => h y (by simp [hy]))]
    push_cast
    ring

theorem sumA2_nonneg (l : List It) : 0 ≤ sumA2 l := by
  rw [sumA2]
  exact List.sum_nonneg (fun x hx => by
    obtain ⟨y, _, rfl⟩ := List.mem_map.mp hx
    positivity)

theorem sumB2_nonneg (l : List It) : 0 ≤ sumB2 l := by
  rw [sumB2]
  exact List.sum_nonneg (fun x hx => by
    obtain ⟨y, _, rfl⟩ := List.mem_map.mp hx
    positivity)

theorem sumF2_nonneg (l : List It) : 0 ≤ sumF2 l := by
  rw [sumF2]
  exact List.sum_nonneg (fun x hx => by
    obtain ⟨y, _, rfl⟩ := List.mem_map.mp hx
    positivity)

theorem sumE2_nonneg (l : List It) : 0 ≤ sumE2 l := by
  rw [sumE2]
  exact List.sum_nonneg (fun x hx => by
    obtain ⟨y, _, rfl⟩ := List.mem_map.mp hx
    positivity)

theorem mem_D25_le {f : ℕ} (h : f ∈ D25) : f ≤ 24 := by
  have hall : D25.all (fun f => decide (f ≤ 24)) = true := by decide
  exact of_decide_eq_true (List.all_eq_true.mp hall f h)

theorem mem_D25_dvd {f : ℕ} (h : f ∈ D25) : f ∣ 2520 := by
  have hall : D25.all (fun f => decide (f ∣ 2520)) = true := by decide
  exact of_decide_eq_true (List.all_eq_true.mp hall f h)

theorem mem_D50_dvd {f : ℕ} (h : f ∈ D50) : f ∣ 2520 := by
  have hall : D50.all (fun f => decide (f ∣ 2520)) = true := by decide
  exact of_decide_eq_true (List.all_eq_true.mp hall f h)

theorem mem_D50_pos {f : ℕ} (h : f ∈ D50) : f ≠ 0 := by
  have hall : D50.all (fun f => decide (2 ≤ f)) = true := by decide
  have := of_decide_eq_true (List.all_eq_true.mp hall f h)
  omega

theorem mem_allowedD25_D25 {a b : ℤ} {f : ℕ} (h : f ∈ allowedD25 a b) : f ∈ D25 :=
  (List.mem_filter.mp h).1

theorem mem_allowedD25_le {a b : ℤ} {f : ℕ} (h : f ∈ allowedD25 a b) : f ≤ 24 :=
  mem_D25_le (mem_allowedD25_D25 h)

theorem mem_allowedD25_cong {a b : ℤ} {f : ℕ} (h : f ∈ allowedD25 a b) :
    ((f : ℤ) + 5 * (b - 2 * a)) % 8 = 0 := by
  have h2 := (List.mem_filter.mp h).2
  simpa using h2

theorem abs_fst_typ (x : It) : |x.typ.1| = |x.a| := rfl

theorem abs_snd_typ (x : It) : |x.typ.2| = |x.b| := rfl

theorem sumAF_eq_of (m : List It) (c : ℤ) (h : ∀ x ∈ m, x.a = c) :
    sumAF m = c * fsum (m.map (fun x => x.f)) := by
  induction m with
  | nil => simp [sumAF, fsum]
  | cons x xs ih =>
    have hx : x.a = c := h x (by simp)
    have hih := ih (fun y hy => h y (by simp [hy]))
    simp only [sumAF, fsum, List.map_cons, List.sum_cons] at hih ⊢
    rw [hx, hih]
    ring_nf

theorem sumBF_eq_of (m : List It) (c : ℤ) (h : ∀ x ∈ m, x.b = c) :
    sumBF m = c * fsum (m.map (fun x => x.f)) := by
  induction m with
  | nil => simp [sumBF, fsum]
  | cons x xs ih =>
    have hx : x.b = c := h x (by simp)
    have hih := ih (fun y hy => h y (by simp [hy]))
    simp only [sumBF, fsum, List.map_cons, List.sum_cons] at hih ⊢
    rw [hx, hih]
    ring_nf

theorem sumF2_eq (m : List It) : sumF2 m = fsq (m.map (fun x => x.f)) := by
  induction m with
  | nil => simp [sumF2, fsq]
  | cons x xs ih =>
    simp only [sumF2, fsq, List.map_cons, List.sum_cons] at ih ⊢
    rw [ih]

theorem fst_typ {x : It} {t : ℤ × ℤ} (h : x.typ = t) : x.a = t.1 := by
  have := congrArg Prod.fst h
  simpa [It.typ] using this

theorem snd_typ {x : It} {t : ℤ × ℤ} (h : x.typ = t) : x.b = t.2 := by
  have := congrArg Prod.snd h
  simpa [It.typ] using this

/-! ## Membership in the enumeration -/

theorem mem_enumItems_cons {t : ℤ × ℤ} {ts : List (ℤ × ℤ)} {r1 r2 rab raf rbf rf2 : ℤ}
    {k : ℕ} {fs : List ℕ} {r : List It}
    (hk : k ∈ List.range 5)
    (hc : (k : ℤ) * t.1 ^ 2 ≤ r1 ∧ (k : ℤ) * t.2 ^ 2 ≤ r2 ∧ (t.1 = 0 → r1 = 0))
    (hfs : fs ∈ fTuples (allowedD25 t.1 t.2) k)
    (hd : |rab - t.1 * t.2 * (k : ℤ)| ≤
            ((r1 - (k : ℤ) * t.1 ^ 2) + (r2 - (k : ℤ) * t.2 ^ 2)) / 2 ∧
          |raf - t.1 * fsum fs| ≤ 50 * (r1 - (k : ℤ) * t.1 ^ 2) ∧
          |rbf - t.2 * fsum fs| ≤ 50 * (r2 - (k : ℤ) * t.2 ^ 2) ∧
          fsq fs ≤ rf2)
    (hr : r ∈ enumItems ts (r1 - (k : ℤ) * t.1 ^ 2) (r2 - (k : ℤ) * t.2 ^ 2)
             (rab - t.1 * t.2 * (k : ℤ)) (raf - t.1 * fsum fs)
             (rbf - t.2 * fsum fs) (rf2 - fsq fs)) :
    itemsOf t fs ++ r ∈ enumItems (t :: ts) r1 r2 rab raf rbf rf2 := by
  simp only [enumItems]
  rw [List.mem_flatMap]
  refine ⟨k, hk, ?_⟩
  rw [if_pos hc, List.mem_flatMap]
  refine ⟨fs, hfs, ?_⟩
  rw [if_pos hd, List.mem_map]
  exact ⟨r, hr, rfl⟩


/-! ## Completeness of the enumeration

Every genuine solution is a permutation of an element of `enumItems`. -/

theorem smallTypes_mem {ts : List (ℤ × ℤ)} (h : smallTypes ts) :
    ∀ t ∈ ts, |t.1| ≤ 2 ∧ |t.2| ≤ 2 := by
  induction ts with
  | nil => intro t ht; simp at ht
  | cons s ts ih =>
    simp only [smallTypes] at h
    obtain ⟨h1, h2, h3⟩ := h
    intro t ht
    rw [List.mem_cons] at ht
    rcases ht with hh | hh
    · rw [hh]; exact ⟨h1, h2⟩
    · exact ih h3 t hh

theorem enumItems_complete (ts : List (ℤ × ℤ)) (r1 r2 rab raf rbf rf2 : ℤ) (l : List It)
    (hs : aSorted ts) (hnz : noZero ts) (hsm : smallTypes ts)
    (he : ∀ x ∈ l, x.e = 0) (ht : ∀ x ∈ l, x.typ ∈ ts)
    (hf : ∀ x ∈ l, x.f ∈ allowedD25 x.a x.b)
    (h1 : sumA2 l = r1) (h2 : sumB2 l = r2) (h3 : sumAB l = rab) (h4 : sumAF l = raf)
    (h5 : sumBF l = rbf) (h6 : sumF2 l ≤ rf2) (hr1 : r1 ≤ 4) (hr2 : r2 ≤ 4) :
    ∃ l' ∈ enumItems ts r1 r2 rab raf rbf rf2, l.Perm l' := by
  induction ts generalizing r1 r2 rab raf rbf rf2 l with
  | nil =>
    have hl : l = [] := by
      cases l with
      | nil => rfl
      | cons x xs => exact absurd (ht x (by simp)) (by simp)
    subst hl
    simp only [sumA2, sumB2, sumAB, sumAF, sumBF, List.map_nil, List.sum_nil] at h1 h2 h3 h4 h5
    refine ⟨[], ?_, List.Perm.nil⟩
    simp only [enumItems]
    rw [if_pos ⟨h1.symm, h2.symm, h3.symm, h4.symm, h5.symm⟩]
    exact List.mem_singleton_self []
  | cons t ts ih =>
    simp only [aSorted] at hs
    obtain ⟨hs1, hs2⟩ := hs
    simp only [noZero] at hnz
    obtain ⟨hnz1, hnz2⟩ := hnz
    simp only [smallTypes] at hsm
    obtain ⟨hsmA, hsmB, hsm3⟩ := hsm
    set m : List It := l.filter (fun x => x.typ == t) with hmdef
    set rest : List It := l.filter (fun x => !(x.typ == t)) with hrestdef
    have hperm : (m ++ rest).Perm l := by
      rw [hmdef, hrestdef]; exact List.filter_append_perm _ _
    have hm_in : ∀ x ∈ m, x ∈ l := by
      intro x hx; rw [hmdef] at hx; exact (List.mem_filter.mp hx).1
    have hrest_in : ∀ x ∈ rest, x ∈ l := by
      intro x hx; rw [hrestdef] at hx; exact (List.mem_filter.mp hx).1
    have hm_typ : ∀ x ∈ m, x.typ = t := by
      intro x hx; rw [hmdef] at hx; exact beq_iff_eq.mp (List.mem_filter.mp hx).2
    have hrest_typ : ∀ x ∈ rest, x.typ ∈ ts := by
      intro x hx
      rw [hrestdef] at hx
      obtain ⟨hxl, hxp⟩ := List.mem_filter.mp hx
      have hxt := ht x hxl
      rw [List.mem_cons] at hxt
      rcases hxt with h | h
      · exfalso
        have hb : (x.typ == t) = true := by rw [h]; exact beq_self_eq_true t
        rw [hb] at hxp
        exact absurd hxp (by decide)
      · exact h
    set fs : List ℕ := m.map (fun x => x.f) with hfsdef
    have hm_eq : m = itemsOf t fs := by
      rw [hfsdef]
      exact eq_itemsOf_of_forall hm_typ (fun x hx => he x (hm_in x hx))
    have hfs_mem : ∀ y ∈ fs, y ∈ allowedD25 t.1 t.2 := by
      intro y hy
      rw [hfsdef] at hy
      obtain ⟨x, hxm, rfl⟩ := List.mem_map.mp hy
      have hxt := hm_typ x hxm
      have ha : x.a = t.1 := congrArg Prod.fst hxt
      have hb : x.b = t.2 := congrArg Prod.snd hxt
      have := hf x (hm_in x hxm)
      rwa [ha, hb] at this
    have hfs : fs ∈ fTuples (allowedD25 t.1 t.2) m.length := by
      rw [← List.length_map (f := fun x : It => x.f), ← hfsdef]
      exact fTuples_complete hfs_mem

    -- sums over `m`
    have hA2m : sumA2 m = (m.length : ℤ) * t.1 ^ 2 := by
      rw [sumA2]
      exact sum_map_const m (fun x => x.a ^ 2) (t.1 ^ 2)
        (fun x hx => by rw [fst_typ (hm_typ x hx)])
    have hB2m : sumB2 m = (m.length : ℤ) * t.2 ^ 2 := by
      rw [sumB2]
      exact sum_map_const m (fun x => x.b ^ 2) (t.2 ^ 2)
        (fun x hx => by rw [snd_typ (hm_typ x hx)])
    have hABm : sumAB m = (m.length : ℤ) * (t.1 * t.2) := by
      rw [sumAB]
      exact sum_map_const m (fun x => x.a * x.b) (t.1 * t.2)
        (fun x hx => by rw [fst_typ (hm_typ x hx), snd_typ (hm_typ x hx)])
    have hAFm : sumAF m = t.1 * fsum fs := by
      rw [hfsdef]
      exact sumAF_eq_of m t.1 (fun x hx => fst_typ (hm_typ x hx))
    have hBFm : sumBF m = t.2 * fsum fs := by
      rw [hfsdef]
      exact sumBF_eq_of m t.2 (fun x hx => snd_typ (hm_typ x hx))
    have hF2m : sumF2 m = fsq fs := by
      rw [hfsdef]
      exact sumF2_eq m

    -- residual identities
    have hA2s : sumA2 l = sumA2 m + sumA2 rest := by
      rw [← sumA2_perm hperm, sumA2_append]
    have hB2s : sumB2 l = sumB2 m + sumB2 rest := by
      rw [← sumB2_perm hperm, sumB2_append]
    have hABs : sumAB l = sumAB m + sumAB rest := by
      rw [← sumAB_perm hperm, sumAB_append]
    have hAFs : sumAF l = sumAF m + sumAF rest := by
      rw [← sumAF_perm hperm, sumAF_append]
    have hBFs : sumBF l = sumBF m + sumBF rest := by
      rw [← sumBF_perm hperm, sumBF_append]
    have hF2s : sumF2 l = sumF2 m + sumF2 rest := by
      rw [← sumF2_perm hperm, sumF2_append]
    have hr1' : sumA2 rest = r1 - (m.length : ℤ) * t.1 ^ 2 := by
      rw [← h1, hA2s, hA2m]; ring
    have hr2' : sumB2 rest = r2 - (m.length : ℤ) * t.2 ^ 2 := by
      rw [← h2, hB2s, hB2m]; ring
    have hrab' : sumAB rest = rab - t.1 * t.2 * (m.length : ℤ) := by
      rw [← h3, hABs, hABm]; ring
    have hraf' : sumAF rest = raf - t.1 * fsum fs := by
      rw [← h4, hAFs, hAFm]; ring
    have hrbf' : sumBF rest = rbf - t.2 * fsum fs := by
      rw [← h5, hBFs, hBFm]; ring

    -- pruning conditions
    have hk1 : (m.length : ℤ) * t.1 ^ 2 ≤ r1 := by
      have := sumA2_nonneg rest; rw [hr1'] at this; linarith
    have hk2 : (m.length : ℤ) * t.2 ^ 2 ≤ r2 := by
      have := sumB2_nonneg rest; rw [hr2'] at this; linarith
    have hk3 : t.1 = 0 → r1 = 0 := by
      intro h0
      have hall : ∀ x ∈ l, x.a = 0 := by
        intro x hx
        have hxt := ht x hx
        rw [List.mem_cons] at hxt
        rcases hxt with h | h
        · have h2' : (x.typ).1 = 0 := by rw [h]; exact h0
          simpa [It.typ] using h2'
        · have h2' : (x.typ).1 = 0 := hs1 h0 x.typ h
          simpa [It.typ] using h2'
      have hA2l : sumA2 l = 0 := by
        rw [sumA2]
        rw [sum_map_const l (fun x => x.a ^ 2) 0 (fun x hx => by rw [hall x hx]; ring)]
        ring
      rw [← h1]; exact hA2l
    have hk4 : |rab - t.1 * t.2 * (m.length : ℤ)| ≤
        ((r1 - (m.length : ℤ) * t.1 ^ 2) + (r2 - (m.length : ℤ) * t.2 ^ 2)) / 2 := by
      rw [← hrab', ← hr1', ← hr2']
      exact abs_sumAB_le rest
    have htypes : ∀ s ∈ (t :: ts), |s.1| ≤ 2 ∧ |s.2| ≤ 2 := by
      intro s hst
      rw [List.mem_cons] at hst
      rcases hst with h | h
      · rw [h]; exact ⟨hsmA, hsmB⟩
      · exact smallTypes_mem hsm3 s h
    have hk5 : |raf - t.1 * fsum fs| ≤
        50 * (r1 - (m.length : ℤ) * t.1 ^ 2) := by
      rw [← hraf', ← hr1']
      refine abs_sumAF_le rest (fun x hx => ?_) (fun x hx => ?_)
      · have hh := htypes x.typ (ht x (hrest_in x hx))
        rw [abs_fst_typ x] at hh
        exact hh.1
      · exact mem_allowedD25_le (hf x (hrest_in x hx))
    have hk6 : |rbf - t.2 * fsum fs| ≤
        50 * (r2 - (m.length : ℤ) * t.2 ^ 2) := by
      rw [← hrbf', ← hr2']
      refine abs_sumBF_le rest (fun x hx => ?_) (fun x hx => ?_)
      · have hh := htypes x.typ (ht x (hrest_in x hx))
        rw [abs_snd_typ x] at hh
        exact hh.2
      · exact mem_allowedD25_le (hf x (hrest_in x hx))
    have hk7 : fsq fs ≤ rf2 := by
      have hle : fsq fs ≤ sumF2 l := by
        rw [hF2s, hF2m]
        have := sumF2_nonneg rest
        linarith
      linarith
    have hk8 : (m.length : ℤ) ≤ 4 := by
      have hmlen : (0 : ℤ) ≤ (m.length : ℤ) := by positivity
      rcases eq_or_ne t.1 (0 : ℤ) with h | h
      · have ht2 : t.2 ≠ 0 := by
          intro hc
          exact hnz1 (by rw [Prod.ext_iff]; exact ⟨h, hc⟩)
        have ht2sq : (1 : ℤ) ≤ t.2 ^ 2 := by
          have := abs_pos.mpr ht2
          nlinarith [sq_abs t.2]
        nlinarith only [hk2, hr2, ht2sq, hmlen]
      · have ht1sq : (1 : ℤ) ≤ t.1 ^ 2 := by
          have := abs_pos.mpr h
          nlinarith [sq_abs t.1]
        nlinarith only [hk1, hr1, ht1sq, hmlen]
    have hk9 : m.length ∈ List.range 5 := List.mem_range.mpr (by omega)
    have hk10 : sumF2 rest ≤ rf2 - fsq fs := by
      rw [hF2s, hF2m] at h6
      linarith

    obtain ⟨l₂, hl₂mem, hl₂perm⟩ :=
      ih (r1 - (m.length : ℤ) * t.1 ^ 2) (r2 - (m.length : ℤ) * t.2 ^ 2)
        (rab - t.1 * t.2 * (m.length : ℤ))
        (raf - t.1 * fsum fs)
        (rbf - t.2 * fsum fs)
        (rf2 - fsq fs)
        rest hs2 hnz2 hsm3
        (fun x hx => he x (hrest_in x hx)) hrest_typ
        (fun x hx => hf x (hrest_in x hx))
        hr1' hr2' hrab' hraf' hrbf' hk10
        (by have hnn : (0 : ℤ) ≤ (m.length : ℤ) * t.1 ^ 2 := by positivity
            linarith)
        (by have hnn : (0 : ℤ) ≤ (m.length : ℤ) * t.2 ^ 2 := by positivity
            linarith)
    refine ⟨itemsOf t fs ++ l₂, ?_, ?_⟩
    · exact mem_enumItems_cons hk9 ⟨hk1, hk2, hk3⟩ hfs ⟨hk4, hk5, hk6, hk7⟩ hl₂mem
    · rw [← hm_eq]
      exact hperm.symm.trans (List.Perm.append (List.Perm.refl m) hl₂perm)

/-! ## Phase 1: classification of the indices with `e ≠ 0` -/

theorem sumM_map_const {α : Type*} (s : Multiset α) (g : α → ℤ) (c : ℤ)
    (h : ∀ x ∈ s, g x = c) : (s.map g).sum = (s.card : ℤ) * c := by
  induction s using Multiset.induction with
  | empty => simp
  | cons a s ih =>
    rw [Multiset.map_cons, Multiset.sum_cons, Multiset.card_cons, Nat.cast_add, Nat.cast_one,
      h a (by simp), ih (fun y hy => h y (by simp [hy]))]
    ring

theorem mem_ABQ {a b : ℤ} (ha1 : -2 ≤ a) (ha2 : a ≤ 2) (hb1 : -2 ≤ b) (hb2 : b ≤ 2) :
    (a, b) ∈ ABQ := by
  interval_cases a <;> interval_cases b <;> decide

theorem mem_allowedD {A B sg : ℤ} {f : ℕ} (hf : f ∈ D50)
    (hc : ((f : ℤ) + 5 * (B - 2 * A) + 2 * sg) % 8 = 0) : f ∈ allowedD A B sg := by
  rw [allowedD, List.mem_filter]
  exact ⟨hf, by simpa using hc⟩

theorem mem_L1 {sg : ℤ} {x : It} (he : x.e = sg) (ha1 : -2 ≤ x.a) (ha2 : x.a ≤ 2)
    (hb1 : -2 ≤ x.b) (hb2 : x.b ≤ 2) (hf : x.f ∈ D50)
    (hc : ((x.f : ℤ) + 5 * (x.b - 2 * x.a) + 2 * sg) % 8 = 0) : x ∈ L1 sg := by
  rw [L1, List.mem_flatMap]
  refine ⟨(x.a, x.b), mem_ABQ ha1 ha2 hb1 hb2, ?_⟩
  rw [List.mem_map]
  refine ⟨x.f, mem_allowedD hf hc, ?_⟩
  rw [← he]

theorem mem_p1Out {sg : ℤ} {p q : It} (hsg : sg = 1 ∨ sg = -1) (hp : p ∈ L1 (-sg))
    (hq : q ∈ L1 (-sg)) (hc : chk1 sg p q) : [mkIt sg p q, p, q] ∈ p1Out := by
  simp only [p1Out, List.mem_flatMap, List.mem_cons, List.not_mem_nil, or_false]
  refine ⟨sg, ?_, ?_⟩
  · rcases hsg with h | h <;> simp [h]
  · refine ⟨p, hp, ?_⟩
    refine ⟨q, hq, ?_⟩
    rw [if_pos hc]
    exact List.mem_singleton_self _

theorem p1Out_perm {l : List It} (h : l ∈ p1Out) : l.Perm C0 ∨ l.Perm C1 ∨ l.Perm C2 := by
  have hh := p1Out_all
  rw [List.all_eq_true] at hh
  exact of_decide_eq_true (hh l h)

/-- The arithmetic core of phase 1. -/
theorem phase1_arith (s p q : It) (hs : s.valid) (hp : p.valid) (hq : q.valid)
    (hsne : s.e ≠ 0) (hpe : p.e = -s.e) (hqe : q.e = -s.e)
    (hEA : s.e * s.a + (p.e * p.a + q.e * q.a) = 0)
    (hEB : s.e * s.b + (p.e * p.b + q.e * q.b) = -1)
    (hEF : s.e * Int.ofNat s.f + (p.e * Int.ofNat p.f + q.e * Int.ofNat q.f) = -1)
    (hC2EW : s.c ^ 2 * s.e * s.w + (p.c ^ 2 * p.e * p.w + q.c ^ 2 * q.e * q.w) = -216) :
    chk1 s.e p q := by
  simp only [It.valid] at hs hp hq
  obtain ⟨hes, ⟨hsa1, hsa2⟩, ⟨hsb1, hsb2⟩, hsf2, hsf50, hsfdvd, hscong⟩ := hs
  obtain ⟨hep, ⟨hpa1, hpa2⟩, ⟨hpb1, hpb2⟩, hpf2, hpf50, hpfdvd, hpcong⟩ := hp
  obtain ⟨heq, ⟨hqa1, hqa2⟩, ⟨hqb1, hqb2⟩, hqf2, hqf50, hqfdvd, hqcong⟩ := hq
  have hse : s.e = 1 ∨ s.e = -1 := by
    rcases hes with h | h | h
    · exact Or.inr h
    · exact absurd h hsne
    · exact Or.inl h
  have hEA' : s.e * (s.a - p.a - q.a) = 0 := by
    have h := hEA
    rw [hpe, hqe] at h
    nlinarith [h]
  have hEB' : s.e * (s.b - p.b - q.b + s.e) = 0 := by
    have h := hEB
    rw [hpe, hqe] at h
    rcases hse with h' | h' <;> rw [h'] at h ⊢ <;> nlinarith [h]
  have hEF' : s.e * (Int.ofNat s.f - Int.ofNat p.f - Int.ofNat q.f + s.e) = 0 := by
    have h := hEF
    rw [hpe, hqe] at h
    rcases hse with h' | h' <;> rw [h'] at h ⊢ <;> nlinarith [h]
  have hC2EW' : s.e * (s.c ^ 2 * s.w - p.c ^ 2 * p.w - q.c ^ 2 * q.w + 216 * s.e) = 0 := by
    have h := hC2EW
    rw [hpe, hqe] at h
    rcases hse with h' | h' <;> rw [h'] at h ⊢ <;> nlinarith [h]
  have hsa : s.a = p.a + q.a := by
    rcases mul_eq_zero.mp hEA' with h | h
    · exact absurd h hsne
    · linarith
  have hsb : s.b = p.b + q.b - s.e := by
    rcases mul_eq_zero.mp hEB' with h | h
    · exact absurd h hsne
    · linarith
  have hsf : Int.ofNat s.f = Int.ofNat p.f + Int.ofNat q.f - s.e := by
    rcases mul_eq_zero.mp hEF' with h | h
    · exact absurd h hsne
    · linarith
  have hsc : s.c ^ 2 * s.w = p.c ^ 2 * p.w + q.c ^ 2 * q.w - 216 * s.e := by
    rcases mul_eq_zero.mp hC2EW' with h | h
    · exact absurd h hsne
    · linarith
  have htoNat : Int.toNat (Int.ofNat p.f + Int.ofNat q.f - s.e) = s.f := by
    rw [← hsf]
    simp
  have hcong : ((Int.ofNat p.f + Int.ofNat q.f - s.e) +
      5 * ((p.b + q.b - s.e) - 2 * (p.a + q.a)) + 2 * s.e) % 8 = 0 := by
    have h := hscong
    rw [It.cong] at h
    rw [← hsa, ← hsb, ← hsf]
    simpa using h
  simp only [chk1]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · omega
  · omega
  · omega
  · omega
  · omega
  · omega
  · rw [htoNat]; exact hsfdvd
  · exact hcong
  · rw [← hsa, ← hsb, htoNat]
    simpa [It.c, It.w] using hsc

/-! ## Phase 1: the classification -/

theorem count_map_finset {α β : Type*} [DecidableEq β] (s : Finset α) (g : α → β) (y : β) :
    (s.val.map g).count y = (s.filter (fun a => g a = y)).card := by
  rw [Multiset.count_map, ← Finset.filter_val]
  congr 1
  apply Multiset.filter_congr
  intro a _
  simp [eq_comm]

/-- The phase-1 reconstruction with the sign pattern of the three indices. -/
theorem phase1_case (s p q : It) (hs : s.valid) (hp : p.valid) (hq : q.valid)
    (hse : s.e = 1 ∨ s.e = -1) (hpe : p.e = -s.e) (hqe : q.e = -s.e)
    (hEA : s.e * s.a + (p.e * p.a + q.e * q.a) = 0)
    (hEB : s.e * s.b + (p.e * p.b + q.e * q.b) = -1)
    (hEF : s.e * Int.ofNat s.f + (p.e * Int.ofNat p.f + q.e * Int.ofNat q.f) = -1)
    (hC2EW : s.c ^ 2 * s.e * s.w + (p.c ^ 2 * p.e * p.w + q.c ^ 2 * q.e * q.w) = -216) :
    ({s, p, q} : Multiset It) = ↑C0 ∨ ({s, p, q} : Multiset It) = ↑C1 ∨
      ({s, p, q} : Multiset It) = ↑C2 := by
  have hsne : s.e ≠ 0 := by rcases hse with h | h <;> rw [h] <;> norm_num
  have hchk : chk1 s.e p q := phase1_arith s p q hs hp hq hsne hpe hqe hEA hEB hEF hC2EW
  simp only [It.valid] at hp hq
  obtain ⟨hep, ⟨hpa1, hpa2⟩, ⟨hpb1, hpb2⟩, hpf2, hpf50, hpfdvd, hpcong⟩ := hp
  obtain ⟨heq, ⟨hqa1, hqa2⟩, ⟨hqb1, hqb2⟩, hqf2, hqf50, hqfdvd, hqcong⟩ := hq
  have hpL : p ∈ L1 (-s.e) :=
    mem_L1 hpe hpa1 hpa2 hpb1 hpb2 (mem_D50 hpfdvd hpf2 hpf50) (by rw [← hpe]; exact hpcong)
  have hqL : q ∈ L1 (-s.e) :=
    mem_L1 hqe hqa1 hqa2 hqb1 hqb2 (mem_D50 hqfdvd hqf2 hqf50) (by rw [← hqe]; exact hqcong)
  have hmem : [mkIt s.e p q, p, q] ∈ p1Out := mem_p1Out hse hpL hqL hchk
  have hperm := p1Out_perm hmem
  have hsa : s.a = p.a + q.a := by
    have h := hEA
    rw [hpe, hqe] at h
    rcases hse with h' | h' <;> rw [h'] at h <;> nlinarith [h]
  have hsb : s.b = p.b + q.b - s.e := by
    have h := hEB
    rw [hpe, hqe] at h
    rcases hse with h' | h' <;> rw [h'] at h ⊢ <;> nlinarith [h]
  have hsf : Int.ofNat s.f = Int.ofNat p.f + Int.ofNat q.f - s.e := by
    have h := hEF
    rw [hpe, hqe] at h
    rcases hse with h' | h' <;> rw [h'] at h ⊢ <;> nlinarith [h]
  have hmk : mkIt s.e p q = s := by
    have h1 : mkIt s.e p q = (⟨s.e, p.a + q.a, p.b + q.b - s.e,
        Int.toNat (Int.ofNat p.f + Int.ofNat q.f - s.e)⟩ : It) := rfl
    rw [h1, ← hsa, ← hsb]
    congr 1
    rw [← hsf]
    simp
  have hM : ({s, p, q} : Multiset It) = ({mkIt s.e p q, p, q} : Multiset It) := by
    rw [hmk]
  rw [hM]
  rcases hperm with h | h | h
  · exact Or.inl (Multiset.coe_eq_coe.mpr h)
  · exact Or.inr (Or.inl (Multiset.coe_eq_coe.mpr h))
  · exact Or.inr (Or.inr (Multiset.coe_eq_coe.mpr h))


theorem mem_ABT {a b : ℤ} (ha1 : -2 ≤ a) (ha2 : a ≤ 2) (hb1 : -2 ≤ b) (hb2 : b ≤ 2)
    (h : (a, b) ≠ 0) : (a, b) ∈ ABT := by
  interval_cases a <;> interval_cases b <;> simp_all (config := { decide := true })

theorem trio_swap2 (a b c : It) : ({a, b, c} : Multiset It) = {b, a, c} :=
  Multiset.coe_eq_coe.mpr (List.Perm.swap a b [c]).symm

theorem trio_rot (a b c : It) : ({a, b, c} : Multiset It) = {c, a, b} :=
  Multiset.coe_eq_coe.mpr <|
    ((List.Perm.swap a b [c]).symm.trans (List.Perm.cons b (List.Perm.swap a c [])).symm).trans
      (((List.Perm.swap b c [a]).symm).trans (List.Perm.cons c (List.Perm.swap b a [])).symm)

theorem phase1_classify (M1 : Multiset It) (hcard : M1.card = 3)
    (hvalid : ∀ x ∈ M1, x.valid) (hne : ∀ x ∈ M1, x.e ≠ 0)
    (hEA : sumEAM M1 = 0) (hEB : sumEBM M1 = -1) (hEF : sumEFM M1 = -1)
    (hC2EW : sumC2EWM M1 = -216) :
    M1 = ↑C0 ∨ M1 = ↑C1 ∨ M1 = ↑C2 := by
  obtain ⟨x1, x2, x3, hM⟩ := Multiset.card_eq_three.mp hcard
  subst hM
  have hv1 := hvalid x1 (by simp)
  have hv2 := hvalid x2 (by simp)
  have hv3 := hvalid x3 (by simp)
  have hn1 := hne x1 (by simp)
  have hn2 := hne x2 (by simp)
  have hn3 := hne x3 (by simp)
  simp only [It.valid] at hv1 hv2 hv3
  have hf1 : 2 ≤ x1.f := hv1.2.2.2.1
  have hf2 : 2 ≤ x2.f := hv2.2.2.2.1
  have hf3 : 2 ≤ x3.f := hv3.2.2.2.1
  have he1 : x1.e = 1 ∨ x1.e = -1 := by
    rcases hv1.1 with h | h | h
    · exact Or.inr h
    · exact absurd h hn1
    · exact Or.inl h
  have he2 : x2.e = 1 ∨ x2.e = -1 := by
    rcases hv2.1 with h | h | h
    · exact Or.inr h
    · exact absurd h hn2
    · exact Or.inl h
  have he3 : x3.e = 1 ∨ x3.e = -1 := by
    rcases hv3.1 with h | h | h
    · exact Or.inr h
    · exact absurd h hn3
    · exact Or.inl h
  have hEA' : x1.e * x1.a + (x2.e * x2.a + x3.e * x3.a) = 0 := by
    simpa [sumEAM, Multiset.map_cons, Multiset.sum_cons] using hEA
  have hEB' : x1.e * x1.b + (x2.e * x2.b + x3.e * x3.b) = -1 := by
    simpa [sumEBM, Multiset.map_cons, Multiset.sum_cons] using hEB
  have hEF' : x1.e * Int.ofNat x1.f + (x2.e * Int.ofNat x2.f + x3.e * Int.ofNat x3.f) = -1 := by
    simpa [sumEFM, Multiset.map_cons, Multiset.sum_cons] using hEF
  have hC2EW' : x1.c ^ 2 * x1.e * x1.w + (x2.c ^ 2 * x2.e * x2.w + x3.c ^ 2 * x3.e * x3.w)
      = -216 := by
    simpa [sumC2EWM, Multiset.map_cons, Multiset.sum_cons] using hC2EW
  have hf1i : (2 : ℤ) ≤ Int.ofNat x1.f := Int.ofNat_le.mpr hf1
  have hf2i : (2 : ℤ) ≤ Int.ofNat x2.f := Int.ofNat_le.mpr hf2
  have hf3i : (2 : ℤ) ≤ Int.ofNat x3.f := Int.ofNat_le.mpr hf3
  rcases he1 with h1 | h1 <;> rcases he2 with h2 | h2 <;> rcases he3 with h3 | h3
  · exfalso
    rw [h1, h2, h3] at hEF'
    linarith
  · rw [trio_rot x1 x2 x3]
    exact phase1_case x3 x1 x2 hv3 hv1 hv2 (Or.inr h3) (by rw [h1, h3] <;> norm_num)
      (by rw [h2, h3] <;> norm_num)
      (by rw [h1, h2, h3] at hEA' ⊢ <;> linarith)
      (by rw [h1, h2, h3] at hEB' ⊢ <;> linarith)
      (by rw [h1, h2, h3] at hEF' ⊢ <;> linarith)
      (by rw [h1, h2, h3] at hC2EW' ⊢ <;> linarith)
  · rw [trio_swap2 x1 x2 x3]
    exact phase1_case x2 x1 x3 hv2 hv1 hv3 (Or.inr h2) (by rw [h1, h2] <;> norm_num)
      (by rw [h3, h2] <;> norm_num)
      (by rw [h1, h2, h3] at hEA' ⊢ <;> linarith)
      (by rw [h1, h2, h3] at hEB' ⊢ <;> linarith)
      (by rw [h1, h2, h3] at hEF' ⊢ <;> linarith)
      (by rw [h1, h2, h3] at hC2EW' ⊢ <;> linarith)
  · exact phase1_case x1 x2 x3 hv1 hv2 hv3 (Or.inl h1) (by rw [h2, h1] <;> norm_num)
      (by rw [h3, h1] <;> norm_num)
      (by rw [h1, h2, h3] at hEA' ⊢ <;> linarith)
      (by rw [h1, h2, h3] at hEB' ⊢ <;> linarith)
      (by rw [h1, h2, h3] at hEF' ⊢ <;> linarith)
      (by rw [h1, h2, h3] at hC2EW' ⊢ <;> linarith)
  · exact phase1_case x1 x2 x3 hv1 hv2 hv3 (Or.inr h1) (by rw [h2, h1] <;> norm_num)
      (by rw [h3, h1] <;> norm_num)
      (by rw [h1, h2, h3] at hEA' ⊢ <;> linarith)
      (by rw [h1, h2, h3] at hEB' ⊢ <;> linarith)
      (by rw [h1, h2, h3] at hEF' ⊢ <;> linarith)
      (by rw [h1, h2, h3] at hC2EW' ⊢ <;> linarith)
  · rw [trio_swap2 x1 x2 x3]
    exact phase1_case x2 x1 x3 hv2 hv1 hv3 (Or.inl h2) (by rw [h1, h2] <;> norm_num)
      (by rw [h3, h2] <;> norm_num)
      (by rw [h1, h2, h3] at hEA' ⊢ <;> linarith)
      (by rw [h1, h2, h3] at hEB' ⊢ <;> linarith)
      (by rw [h1, h2, h3] at hEF' ⊢ <;> linarith)
      (by rw [h1, h2, h3] at hC2EW' ⊢ <;> linarith)
  · rw [trio_rot x1 x2 x3]
    exact phase1_case x3 x1 x2 hv3 hv1 hv2 (Or.inl h3) (by rw [h1, h3] <;> norm_num)
      (by rw [h2, h3] <;> norm_num)
      (by rw [h1, h2, h3] at hEA' ⊢ <;> linarith)
      (by rw [h1, h2, h3] at hEB' ⊢ <;> linarith)
      (by rw [h1, h2, h3] at hEF' ⊢ <;> linarith)
      (by rw [h1, h2, h3] at hC2EW' ⊢ <;> linarith)
  · exfalso
    rw [h1, h2, h3] at hEF'
    linarith


/-! ## Phase 2: the `e = 0` part -/

theorem mem_D25_of {f : ℕ} (hdvd : f ∣ 2520) (h2 : 2 ≤ f) (h25 : f ≤ 25) : f ∈ D25 := by
  have hall : (List.range 26).all (fun f => decide (¬ (f ∣ 2520) ∨ (f ≤ 1) ∨ (26 ≤ f) ∨ (f ∈ D25))) = true := by
    decide
  rw [List.all_eq_true] at hall
  have h := hall f (List.mem_range.mpr (by omega))
  simp only [decide_eq_true_eq, Bool.or_eq_true, Bool.not_eq_true'] at h
  rcases h with h | h | h | h
  · omega
  · omega
  · omega
  · exact h

theorem aSorted_of_B {ts : List (ℤ × ℤ)} (h : aSortedB ts = true) : aSorted ts := by
  induction ts with
  | nil => simp [aSorted]
  | cons t ts ih =>
    rw [aSortedB, Bool.and_eq_true] at h
    obtain ⟨hA, hB⟩ := h
    refine ⟨?_, ih hB⟩
    intro h0 s hs
    rw [Bool.or_eq_true] at hA
    rcases hA with h1 | h1
    · exfalso
      have h1' : (t.1 == 0) = false := by simpa using h1
      have hne : t.1 ≠ 0 := by
        intro hc
        rw [beq_iff_eq.mpr hc] at h1'
        exact absurd h1' (by decide)
      exact hne h0
    · rw [List.all_eq_true] at h1
      exact beq_iff_eq.mp (h1 s hs)

theorem noZero_of_B {ts : List (ℤ × ℤ)} (h : noZeroB ts = true) : noZero ts := by
  induction ts with
  | nil => simp [noZero]
  | cons t ts ih =>
    rw [noZeroB, Bool.and_eq_true] at h
    exact ⟨by simpa using h.1, ih h.2⟩

theorem smallTypes_of_B {ts : List (ℤ × ℤ)} (h : smallTypesB ts = true) : smallTypes ts := by
  induction ts with
  | nil => simp [smallTypes]
  | cons t ts ih =>
    rw [smallTypesB, Bool.and_eq_true, Bool.and_eq_true, decide_eq_true_eq,
      decide_eq_true_eq] at h
    exact ⟨h.1.1, h.1.2, ih h.2⟩

theorem aSorted_ABT : aSorted ABT := aSorted_of_B (by decide)

theorem noZero_ABT : noZero ABT := noZero_of_B (by decide)

theorem smallTypes_ABT : smallTypes ABT := smallTypes_of_B (by decide)

theorem mem_allowedD25' {A B : ℤ} {f : ℕ} (hf : f ∈ D25)
    (hc : ((f : ℤ) + 5 * (B - 2 * A)) % 8 = 0) : f ∈ allowedD25 A B := by
  rw [allowedD25, List.mem_filter]
  exact ⟨hf, by simpa using hc⟩

theorem le_sum_of_mem_sq {l : List It} {x : It} (hx : x ∈ l) : ((x.f : ℤ)) ^ 2 ≤ sumF2 l := by
  change Int.ofNat x.f ^ 2 ≤ sumF2 l
  rw [sumF2]
  induction l with
  | nil => simp at hx
  | cons y ys ih =>
    rw [List.map_cons, List.sum_cons]
    rcases List.mem_cons.mp hx with h | h
    · rw [h, ← sumF2]
      exact le_add_of_nonneg_right (sumF2_nonneg ys)
    · have h1 := ih h
      have h2 : (0 : ℤ) ≤ Int.ofNat y.f ^ 2 := sq_nonneg _
      linarith only [h1, h2]

theorem phase2_case (M2 : Multiset It) (hvalid : ∀ x ∈ M2, x.valid) (he0 : ∀ x ∈ M2, x.e = 0)
    (hnz : ∀ x ∈ M2, x.nz)
    (r1 r2 rab raf rbf rc3 rc2ab rf2 : ℤ)
    (hA2 : sumA2M M2 = r1) (hB2 : sumB2M M2 = r2) (hAB : sumABM M2 = rab)
    (hAF : sumAFM M2 = raf) (hBF : sumBFM M2 = rbf) (hC3 : sumC3WM M2 = rc3)
    (hC2AB : sumC2ABWM M2 = rc2ab) (hF2 : sumF2M M2 ≤ rf2) (hrf2 : rf2 ≤ 628)
    (hr1 : r1 ≤ 4) (hr2 : r2 ≤ 4) :
    ∃ l ∈ p2Out r1 r2 rab raf rbf rc3 rc2ab rf2, M2 = ↑l := by
  set l : List It := M2.toList with hl
  have hMl : M2 = ↑l := (Multiset.coe_toList M2).symm
  have hmemM : ∀ x ∈ l, x ∈ M2 := by
    intro x hx
    rw [hMl, Multiset.mem_coe]
    exact hx
  have he : ∀ x ∈ l, x.e = 0 := fun x hx => he0 x (hmemM x hx)
  have hv : ∀ x ∈ l, x.valid := fun x hx => hvalid x (hmemM x hx)
  have hnz' : ∀ x ∈ l, x.nz := fun x hx => hnz x (hmemM x hx)
  have ht : ∀ x ∈ l, x.typ ∈ ABT := by
    intro x hx
    have hx' := hv x hx
    simp only [It.valid] at hx'
    have hx0 : x.e = 0 := he x hx
    have hn : x.nz := hnz' x hx
    simp only [It.nz] at hn
    exact mem_ABT hx'.2.1.1 hx'.2.1.2 hx'.2.2.1.1 hx'.2.2.1.2 (by
      intro hc
      rcases hn with h | h | h
      · exact h hx0
      · exact h (congrArg Prod.fst hc)
      · exact h (congrArg Prod.snd hc))
  have hsum6 : sumF2 l ≤ rf2 := by
    rw [← sumF2M_coe l, ← hMl]
    exact hF2
  have hf : ∀ x ∈ l, x.f ∈ allowedD25 x.a x.b := by
    intro x hx
    have hx' := hv x hx
    simp only [It.valid] at hx'
    have hle : ((x.f : ℤ)) ^ 2 ≤ rf2 := le_trans (le_sum_of_mem_sq hx) hsum6
    have h25 : x.f ≤ 25 := by
      by_contra hc
      push_neg at hc
      have h26 : (26 : ℤ) ≤ (x.f : ℤ) := by
        have : 26 ≤ x.f := by omega
        exact_mod_cast this
      have h2601 : (2601 : ℤ) ≤ ((x.f : ℤ)) ^ 2 := by nlinarith
      have : (2601 : ℤ) ≤ rf2 := le_trans h2601 hle
      omega
    refine mem_allowedD25' (mem_D25_of hx'.2.2.2.2.2.1 hx'.2.2.2.1 (by omega)) ?_
    have hc := hx'.2.2.2.2.2.2
    rw [It.cong] at hc
    rw [he x hx] at hc
    simpa using hc
  have h1 : sumA2 l = r1 := by rw [← sumA2M_coe l, ← hMl]; exact hA2
  have h2 : sumB2 l = r2 := by rw [← sumB2M_coe l, ← hMl]; exact hB2
  have h3 : sumAB l = rab := by rw [← sumABM_coe l, ← hMl]; exact hAB
  have h4 : sumAF l = raf := by rw [← sumAFM_coe l, ← hMl]; exact hAF
  have h5 : sumBF l = rbf := by rw [← sumBFM_coe l, ← hMl]; exact hBF
  have h6 : sumF2 l ≤ rf2 := hsum6
  obtain ⟨l', hl'mem, hl'perm⟩ :=
    enumItems_complete ABT r1 r2 rab raf rbf rf2 l
      aSorted_ABT noZero_ABT smallTypes_ABT he ht hf h1 h2 h3 h4 h5 h6 hr1 hr2
  have hpermM : l'.Perm l := hl'perm.symm
  have hC3' : sumC3W l' = rc3 := by
    rw [sumC3W_perm hpermM, ← sumC3WM_coe l, ← hMl]
    exact hC3
  have hC2AB' : sumC2ABW l' = rc2ab := by
    rw [sumC2ABW_perm hpermM, ← sumC2ABWM_coe l, ← hMl]
    exact hC2AB
  refine ⟨l', ?_, ?_⟩
  · rw [p2Out, List.mem_filter]
    refine ⟨hl'mem, ?_⟩
    rw [chk2b, Bool.and_eq_true, decide_eq_true_eq, decide_eq_true_eq]
    exact ⟨hC3', hC2AB'⟩
  · rw [hMl, Multiset.coe_eq_coe]
    exact hl'perm


/-! ## The sums of the three candidates -/

theorem sums_C0 : sumA2 C0 = 2 ∧ sumB2 C0 = 3 ∧ sumAB C0 = 2 ∧ sumAF C0 = -6 ∧
    sumBF C0 = -41 ∧ sumC3W C0 = -120 ∧ sumC2ABW C0 = 24 ∧ sumF2 C0 = 1891 := by decide

theorem sums_C1 : sumA2 C1 = 0 ∧ sumB2 C1 = 3 ∧ sumAB C1 = 0 ∧ sumAF C1 = 0 ∧
    sumBF C1 = -29 ∧ sumC3W C1 = -120 ∧ sumC2ABW C1 = -120 ∧ sumF2 C1 = 1891 := by decide

theorem sums_C2 : sumA2 C2 = 2 ∧ sumB2 C2 = 3 ∧ sumAB C2 = 2 ∧ sumAF C2 = 50 ∧
    sumBF C2 = 71 ∧ sumC3W C2 = -120 ∧ sumC2ABW C2 = 600 ∧ sumF2 C2 = 1891 := by decide

/-! ## The phase-2 conclusions for each candidate -/

theorem phase2_C1 (M2 : Multiset It) (hvalid : ∀ x ∈ M2, x.valid) (he0 : ∀ x ∈ M2, x.e = 0)
    (hnz : ∀ x ∈ M2, x.nz)
    (hA2 : sumA2M M2 = 4) (hB2 : sumB2M M2 = 4) (hAB : sumABM M2 = 0)
    (hAF : sumAFM M2 = 0) (hBF : sumBFM M2 = 28) (hC3 : sumC3WM M2 = 2208)
    (hC2AB : sumC2ABWM M2 = 1056) (hF2 : sumF2M M2 ≤ 628) : M2 = ↑C1T := by
  obtain ⟨l, hl, hlM⟩ := phase2_case M2 hvalid he0 hnz 4 4 0 0 28 2208 1056 628
    hA2 hB2 hAB hAF hBF hC3 hC2AB hF2 (by norm_num) (by norm_num) (by norm_num)
  have hperm : l.Perm C1T := by
    have h := p2Out_C1
    rw [List.all_eq_true] at h
    exact of_decide_eq_true (h l hl)
  rw [hlM, Multiset.coe_eq_coe]
  exact hperm

theorem phase2_C0 (M2 : Multiset It) (hvalid : ∀ x ∈ M2, x.valid) (he0 : ∀ x ∈ M2, x.e = 0)
    (hnz : ∀ x ∈ M2, x.nz)
    (hA2 : sumA2M M2 = 2) (hB2 : sumB2M M2 = 4) (hAB : sumABM M2 = -2)
    (hAF : sumAFM M2 = 6) (hBF : sumBFM M2 = 40) (hC3 : sumC3WM M2 = 2208)
    (hC2AB : sumC2ABWM M2 = 912) (hF2 : sumF2M M2 ≤ 628) : False := by
  obtain ⟨l, hl, -⟩ := phase2_case M2 hvalid he0 hnz 2 4 (-2) 6 40 2208 912 628
    hA2 hB2 hAB hAF hBF hC3 hC2AB hF2 (by norm_num) (by norm_num) (by norm_num)
  rw [p2Out_C0] at hl
  exact absurd hl (by simp)

theorem phase2_C2 (M2 : Multiset It) (hvalid : ∀ x ∈ M2, x.valid) (he0 : ∀ x ∈ M2, x.e = 0)
    (hnz : ∀ x ∈ M2, x.nz)
    (hA2 : sumA2M M2 = 2) (hB2 : sumB2M M2 = 4) (hAB : sumABM M2 = -2)
    (hAF : sumAFM M2 = -50) (hBF : sumBFM M2 = -72) (hC3 : sumC3WM M2 = 2208)
    (hC2AB : sumC2ABWM M2 = 336) (hF2 : sumF2M M2 ≤ 628) : False := by
  obtain ⟨l, hl, -⟩ := phase2_case M2 hvalid he0 hnz 2 4 (-2) (-50) (-72) 2208 336 628
    hA2 hB2 hAB hAF hBF hC3 hC2AB hF2 (by norm_num) (by norm_num) (by norm_num)
  rw [p2Out_C2] at hl
  exact absurd hl (by simp)

/-! ## The combinatorial core -/

theorem combi (M : Multiset It) (hvalid : ∀ x ∈ M, x.valid) (hnz : ∀ x ∈ M, x.nz)
    (hE2 : sumE2M M = 3) (hA2 : sumA2M M = 4) (hB2 : sumB2M M = 7)
    (hEA : sumEAM M = 0) (hEB : sumEBM M = -1) (hAB : sumABM M = 0)
    (hEF : sumEFM M = -1) (hAF : sumAFM M = 0) (hBF : sumBFM M = -1)
    (hC2EW : sumC2EWM M = -216) (hC3W : sumC3WM M = 2088) (hC2ABW : sumC2ABWM M = 936)
    (hF2 : sumF2M M ≤ 2519) : M = A7M := by
  set M1 : Multiset It := M.filter (fun x => x.e ≠ 0) with hM1
  set M2 : Multiset It := M.filter (fun x => ¬ (x.e ≠ 0)) with hM2
  have hsplit : M = M1 + M2 := by
    rw [hM1, hM2]
    exact (Multiset.filter_add_not (fun x => x.e ≠ 0) M).symm
  have hM1mem : ∀ x ∈ M1, x ∈ M := fun x hx => by
    rw [hsplit]; exact Multiset.mem_add.mpr (Or.inl hx)
  have hM2mem : ∀ x ∈ M2, x ∈ M := fun x hx => by
    rw [hsplit]; exact Multiset.mem_add.mpr (Or.inr hx)
  have hM1e : ∀ x ∈ M1, x.e ≠ 0 := by
    intro x hx
    rw [hM1] at hx
    exact (Multiset.mem_filter.mp hx).2
  have hM2e : ∀ x ∈ M2, x.e = 0 := by
    intro x hx
    rw [hM2] at hx
    have h := (Multiset.mem_filter.mp hx).2
    simpa using h
  have hM1v : ∀ x ∈ M1, x.valid := fun x hx => hvalid x (hM1mem x hx)
  have hM2v : ∀ x ∈ M2, x.valid := fun x hx => hvalid x (hM2mem x hx)
  have hM2nz : ∀ x ∈ M2, x.nz := fun x hx => hnz x (hM2mem x hx)
  have hM1nz : ∀ x ∈ M1, x.nz := fun x hx => hnz x (hM1mem x hx)
  -- splits
  have spE2 : sumE2M M = sumE2M M1 + sumE2M M2 := by
    rw [hsplit]
    simp only [sumE2M, Multiset.map_add, Multiset.sum_add]
  have spA2 : sumA2M M = sumA2M M1 + sumA2M M2 := by
    rw [hsplit]
    simp only [sumA2M, Multiset.map_add, Multiset.sum_add]
  have spB2 : sumB2M M = sumB2M M1 + sumB2M M2 := by
    rw [hsplit]
    simp only [sumB2M, Multiset.map_add, Multiset.sum_add]
  have spEA : sumEAM M = sumEAM M1 + sumEAM M2 := by
    rw [hsplit]
    simp only [sumEAM, Multiset.map_add, Multiset.sum_add]
  have spEB : sumEBM M = sumEBM M1 + sumEBM M2 := by
    rw [hsplit]
    simp only [sumEBM, Multiset.map_add, Multiset.sum_add]
  have spAB : sumABM M = sumABM M1 + sumABM M2 := by
    rw [hsplit]
    simp only [sumABM, Multiset.map_add, Multiset.sum_add]
  have spEF : sumEFM M = sumEFM M1 + sumEFM M2 := by
    rw [hsplit]
    simp only [sumEFM, Multiset.map_add, Multiset.sum_add]
  have spAF : sumAFM M = sumAFM M1 + sumAFM M2 := by
    rw [hsplit]
    simp only [sumAFM, Multiset.map_add, Multiset.sum_add]
  have spBF : sumBFM M = sumBFM M1 + sumBFM M2 := by
    rw [hsplit]
    simp only [sumBFM, Multiset.map_add, Multiset.sum_add]
  have spC2EW : sumC2EWM M = sumC2EWM M1 + sumC2EWM M2 := by
    rw [hsplit]
    simp only [sumC2EWM, Multiset.map_add, Multiset.sum_add]
  have spC3W : sumC3WM M = sumC3WM M1 + sumC3WM M2 := by
    rw [hsplit]
    simp only [sumC3WM, Multiset.map_add, Multiset.sum_add]
  have spC2ABW : sumC2ABWM M = sumC2ABWM M1 + sumC2ABWM M2 := by
    rw [hsplit]
    simp only [sumC2ABWM, Multiset.map_add, Multiset.sum_add]
  have spF2 : sumF2M M = sumF2M M1 + sumF2M M2 := by
    rw [hsplit]
    simp only [sumF2M, Multiset.map_add, Multiset.sum_add]
  -- the values on `M2`: all terms vanish since `e = 0` there
  have zEA : sumEAM M2 = (M2.card : ℤ) * 0 :=
    sumM_map_const M2 (fun x => x.e * x.a) 0 (fun x hx => by rw [hM2e x hx]; ring)
  have zEB : sumEBM M2 = (M2.card : ℤ) * 0 :=
    sumM_map_const M2 (fun x => x.e * x.b) 0 (fun x hx => by rw [hM2e x hx]; ring)
  have zEF : sumEFM M2 = (M2.card : ℤ) * 0 :=
    sumM_map_const M2 (fun x => x.e * Int.ofNat x.f) 0 (fun x hx => by rw [hM2e x hx]; ring)
  have zC2EW : sumC2EWM M2 = (M2.card : ℤ) * 0 :=
    sumM_map_const M2 (fun x => x.c ^ 2 * x.e * x.w) 0 (fun x hx => by rw [hM2e x hx]; ring)
  have zE2 : sumE2M M2 = (M2.card : ℤ) * 0 :=
    sumM_map_const M2 (fun x => x.e ^ 2) 0 (fun x hx => by rw [hM2e x hx]; ring)
  -- the values on `M1`
  have oE2 : sumE2M M1 = (M1.card : ℤ) * 1 :=
    sumM_map_const M1 (fun x => x.e ^ 2) 1 (fun x hx => by
      have hne := hM1e x hx
      have hv := hM1v x hx
      simp only [It.valid] at hv
      rcases hv.1 with h | h | h
      · rw [h]; norm_num
      · exact absurd h hne
      · rw [h]; norm_num)
  have hcard1 : M1.card = 3 := by
    have h := hE2
    rw [spE2, oE2, zE2] at h
    omega
  have hEA1 : sumEAM M1 = 0 := by
    have h := hEA
    rw [spEA, zEA] at h
    linarith
  have hEB1 : sumEBM M1 = -1 := by
    have h := hEB
    rw [spEB, zEB] at h
    linarith
  have hEF1 : sumEFM M1 = -1 := by
    have h := hEF
    rw [spEF, zEF] at h
    linarith
  have hC2EW1 : sumC2EWM M1 = -216 := by
    have h := hC2EW
    rw [spC2EW, zC2EW] at h
    linarith
  have hcase := phase1_classify M1 hcard1 hM1v hM1e hEA1 hEB1 hEF1 hC2EW1
  rcases hcase with hc | hc | hc
  · -- M1 = C0: impossible
    exfalso
    have hr : sumA2M M2 = 2 := by
      have h := hA2; rw [spA2, hc, sumA2M_coe, sums_C0.1] at h; linarith
    have hr2 : sumB2M M2 = 4 := by
      have h := hB2; rw [spB2, hc, sumB2M_coe, sums_C0.2.1] at h; linarith
    have hrab : sumABM M2 = -2 := by
      have h := hAB; rw [spAB, hc, sumABM_coe, sums_C0.2.2.1] at h; linarith
    have hraf : sumAFM M2 = 6 := by
      have h := hAF; rw [spAF, hc, sumAFM_coe, sums_C0.2.2.2.1] at h; linarith
    have hrbf : sumBFM M2 = 40 := by
      have h := hBF; rw [spBF, hc, sumBFM_coe, sums_C0.2.2.2.2.1] at h; linarith
    have hrc3 : sumC3WM M2 = 2208 := by
      have h := hC3W; rw [spC3W, hc, sumC3WM_coe, sums_C0.2.2.2.2.2.1] at h; linarith
    have hrc2 : sumC2ABWM M2 = 912 := by
      have h := hC2ABW; rw [spC2ABW, hc, sumC2ABWM_coe, sums_C0.2.2.2.2.2.2.1] at h; linarith
    have hrf2 : sumF2M M2 ≤ 628 := by
      have h := hF2; rw [spF2, hc, sumF2M_coe, sums_C0.2.2.2.2.2.2.2] at h; omega
    exact phase2_C0 M2 hM2v hM2e hM2nz hr hr2 hrab hraf hrbf hrc3 hrc2 hrf2
  · -- M1 = C1
    have hres : M2 = ↑C1T := by
      refine phase2_C1 M2 hM2v hM2e hM2nz ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_
      · have h := hA2; rw [spA2, hc, sumA2M_coe, sums_C1.1] at h; linarith
      · have h := hB2; rw [spB2, hc, sumB2M_coe, sums_C1.2.1] at h; linarith
      · have h := hAB; rw [spAB, hc, sumABM_coe, sums_C1.2.2.1] at h; linarith
      · have h := hAF; rw [spAF, hc, sumAFM_coe, sums_C1.2.2.2.1] at h; linarith
      · have h := hBF; rw [spBF, hc, sumBFM_coe, sums_C1.2.2.2.2.1] at h; linarith
      · have h := hC3W; rw [spC3W, hc, sumC3WM_coe, sums_C1.2.2.2.2.2.1] at h; linarith
      · have h := hC2ABW; rw [spC2ABW, hc, sumC2ABWM_coe, sums_C1.2.2.2.2.2.2.1] at h; linarith
      · have h := hF2; rw [spF2, hc, sumF2M_coe, sums_C1.2.2.2.2.2.2.2] at h; omega
    rw [hsplit, hc, hres]
    rfl
  · -- M1 = C2: impossible
    exfalso
    have hr : sumA2M M2 = 2 := by
      have h := hA2; rw [spA2, hc, sumA2M_coe, sums_C2.1] at h; linarith
    have hr2 : sumB2M M2 = 4 := by
      have h := hB2; rw [spB2, hc, sumB2M_coe, sums_C2.2.1] at h; linarith
    have hrab : sumABM M2 = -2 := by
      have h := hAB; rw [spAB, hc, sumABM_coe, sums_C2.2.2.1] at h; linarith
    have hraf : sumAFM M2 = -50 := by
      have h := hAF; rw [spAF, hc, sumAFM_coe, sums_C2.2.2.2.1] at h; linarith
    have hrbf : sumBFM M2 = -72 := by
      have h := hBF; rw [spBF, hc, sumBFM_coe, sums_C2.2.2.2.2.1] at h; linarith
    have hrc3 : sumC3WM M2 = 2208 := by
      have h := hC3W; rw [spC3W, hc, sumC3WM_coe, sums_C2.2.2.2.2.2.1] at h; linarith
    have hrc2 : sumC2ABWM M2 = 336 := by
      have h := hC2ABW; rw [spC2ABW, hc, sumC2ABWM_coe, sums_C2.2.2.2.2.2.2.1] at h; linarith
    have hrf2 : sumF2M M2 ≤ 628 := by
      have h := hF2; rw [spF2, hc, sumF2M_coe, sums_C2.2.2.2.2.2.2.2] at h; omega
    exact phase2_C2 M2 hM2v hM2e hM2nz hr hr2 hrab hraf hrbf hrc3 hrc2 hrf2

/-! ## Bridges from the `Fin n` formulation -/

theorem sumA2M_univ (n : ℕ) (f : Fin n → ℕ) (e a b : Fin n → ℤ) :
    sumA2M ((Finset.univ : Finset (Fin n)).val.map (fun i => (⟨e i, a i, b i, f i⟩ : It)))
      = ∑ i, (a i) ^ 2 := by
  rw [sumA2M, Multiset.map_map]
  rw [← Finset.sum_eq_multiset_sum]
  rfl

theorem sumB2M_univ (n : ℕ) (f : Fin n → ℕ) (e a b : Fin n → ℤ) :
    sumB2M ((Finset.univ : Finset (Fin n)).val.map (fun i => (⟨e i, a i, b i, f i⟩ : It)))
      = ∑ i, (b i) ^ 2 := by
  rw [sumB2M, Multiset.map_map]
  rw [← Finset.sum_eq_multiset_sum]
  rfl

theorem sumE2M_univ (n : ℕ) (f : Fin n → ℕ) (e a b : Fin n → ℤ) :
    sumE2M ((Finset.univ : Finset (Fin n)).val.map (fun i => (⟨e i, a i, b i, f i⟩ : It)))
      = ∑ i, (e i) ^ 2 := by
  rw [sumE2M, Multiset.map_map]
  rw [← Finset.sum_eq_multiset_sum]
  rfl

theorem sumEAM_univ (n : ℕ) (f : Fin n → ℕ) (e a b : Fin n → ℤ) :
    sumEAM ((Finset.univ : Finset (Fin n)).val.map (fun i => (⟨e i, a i, b i, f i⟩ : It)))
      = ∑ i, e i * a i := by
  rw [sumEAM, Multiset.map_map]
  rw [← Finset.sum_eq_multiset_sum]
  rfl

theorem sumEBM_univ (n : ℕ) (f : Fin n → ℕ) (e a b : Fin n → ℤ) :
    sumEBM ((Finset.univ : Finset (Fin n)).val.map (fun i => (⟨e i, a i, b i, f i⟩ : It)))
      = ∑ i, e i * b i := by
  rw [sumEBM, Multiset.map_map]
  rw [← Finset.sum_eq_multiset_sum]
  rfl

theorem sumABM_univ (n : ℕ) (f : Fin n → ℕ) (e a b : Fin n → ℤ) :
    sumABM ((Finset.univ : Finset (Fin n)).val.map (fun i => (⟨e i, a i, b i, f i⟩ : It)))
      = ∑ i, a i * b i := by
  rw [sumABM, Multiset.map_map]
  rw [← Finset.sum_eq_multiset_sum]
  rfl

theorem sumEFM_univ (n : ℕ) (f : Fin n → ℕ) (e a b : Fin n → ℤ) :
    sumEFM ((Finset.univ : Finset (Fin n)).val.map (fun i => (⟨e i, a i, b i, f i⟩ : It)))
      = ∑ i, e i * (f i : ℤ) := by
  rw [sumEFM, Multiset.map_map]
  rw [← Finset.sum_eq_multiset_sum]
  rfl

theorem sumAFM_univ (n : ℕ) (f : Fin n → ℕ) (e a b : Fin n → ℤ) :
    sumAFM ((Finset.univ : Finset (Fin n)).val.map (fun i => (⟨e i, a i, b i, f i⟩ : It)))
      = ∑ i, a i * (f i : ℤ) := by
  rw [sumAFM, Multiset.map_map]
  rw [← Finset.sum_eq_multiset_sum]
  rfl

theorem sumBFM_univ (n : ℕ) (f : Fin n → ℕ) (e a b : Fin n → ℤ) :
    sumBFM ((Finset.univ : Finset (Fin n)).val.map (fun i => (⟨e i, a i, b i, f i⟩ : It)))
      = ∑ i, b i * (f i : ℤ) := by
  rw [sumBFM, Multiset.map_map]
  rw [← Finset.sum_eq_multiset_sum]
  rfl

theorem sumF2M_univ (n : ℕ) (f : Fin n → ℕ) (e a b : Fin n → ℤ) :
    sumF2M ((Finset.univ : Finset (Fin n)).val.map (fun i => (⟨e i, a i, b i, f i⟩ : It)))
      = ∑ i, (f i : ℤ) ^ 2 := by
  rw [sumF2M, Multiset.map_map]
  rw [← Finset.sum_eq_multiset_sum]
  rfl

theorem sumC2EWM_univ (n : ℕ) (f : Fin n → ℕ) (e a b : Fin n → ℤ) :
    sumC2EWM ((Finset.univ : Finset (Fin n)).val.map (fun i => (⟨e i, a i, b i, f i⟩ : It)))
      = ∑ i, (b i - 2 * a i) ^ 2 * e i * wOf (f i) := by
  rw [sumC2EWM, Multiset.map_map]
  rw [← Finset.sum_eq_multiset_sum]
  rfl

theorem sumC3WM_univ (n : ℕ) (f : Fin n → ℕ) (e a b : Fin n → ℤ) :
    sumC3WM ((Finset.univ : Finset (Fin n)).val.map (fun i => (⟨e i, a i, b i, f i⟩ : It)))
      = ∑ i, (b i - 2 * a i) ^ 3 * wOf (f i) := by
  rw [sumC3WM, Multiset.map_map]
  rw [← Finset.sum_eq_multiset_sum]
  rfl

theorem sumC2ABWM_univ (n : ℕ) (f : Fin n → ℕ) (e a b : Fin n → ℤ) :
    sumC2ABWM ((Finset.univ : Finset (Fin n)).val.map (fun i => (⟨e i, a i, b i, f i⟩ : It)))
      = ∑ i, (b i - 2 * a i) ^ 2 * (a i + b i) * wOf (f i) := by
  rw [sumC2ABWM, Multiset.map_map]
  rw [← Finset.sum_eq_multiset_sum]
  rfl

theorem rat_to_int (n : ℕ) (f : Fin n → ℕ) (g : Fin n → ℤ) (c : ℚ)
    (hD : ∀ i, f i ∈ D50)
    (h : 1 + ∑ i, (g i : ℚ) / (f i : ℚ) = c) :
    (∑ i, g i * wOf (f i)) = 2520 * c - 2520 := by
  have hterm : ∀ i, ((g i : ℚ) / (f i : ℚ)) = ((g i * wOf (f i) : ℤ) : ℚ) / 2520 := by
    intro i
    have hf : f i ∈ D50 := hD i
    have hne : (f i : ℚ) ≠ 0 := by
      have := mem_D50_pos hf
      exact_mod_cast this
    have hw : ((wOf (f i) : ℤ) : ℚ) = 2520 / (f i : ℚ) := by
      haveI : NeZero (f i) := ⟨mem_D50_pos hf⟩
      rw [wOf_eq hf, Int.cast_natCast]
      rw [Nat.cast_div (mem_D50_dvd hf)]
      · ring
      · exact hne
    calc ((g i : ℚ) / (f i : ℚ))
        = (g i : ℚ) * (2520 / (f i : ℚ)) / 2520 := by field_simp
      _ = (g i : ℚ) * ((wOf (f i) : ℤ) : ℚ) / 2520 := by rw [hw]
      _ = ((g i * wOf (f i) : ℤ) : ℚ) / 2520 := by push_cast; ring
  have hsum : ∑ i, ((g i : ℚ) / (f i : ℚ)) = ((∑ i, g i * wOf (f i) : ℤ) : ℚ) / 2520 := by
    have h1 : ∑ i, ((g i : ℚ) / (f i : ℚ)) = ∑ i, (((g i * wOf (f i) : ℤ) : ℚ) / 2520) := by
      apply Finset.sum_congr rfl
      intro i _
      exact hterm i
    rw [h1, ← Finset.sum_div]
    congr 1
    exact (map_sum (Int.castRingHom ℚ) (fun i => g i * wOf (f i)) Finset.univ).symm
  rw [hsum] at h
  have h3 : ((∑ i, g i * wOf (f i) : ℤ) : ℚ) = 2520 * c - 2520 := by
    have h2 : ((∑ i, g i * wOf (f i) : ℤ) : ℚ) / 2520 = c - 1 := by linarith
    field_simp at h2
    linarith
  exact_mod_cast h3


theorem a7TableLemma : Work.A7REC.A7TableLemmaProp := by
  intro n f e a b hnz hf2 hfdiv he2 ha2 hb2 hea heb hab hef haf hbf hcong hq1 hq2 hq3 hle
  have hvalid : ∀ i, ((⟨e i, a i, b i, f i⟩ : It)).valid :=
    fun i => a7_bounds n f e a b hnz hf2 hfdiv he2 ha2 hb2 hle hcong i
  have hD : ∀ i, f i ∈ D50 := by
    intro i
    have h := hvalid i
    simp only [It.valid] at h
    exact mem_D50 (hfdiv i) (hf2 i) h.2.2.2.2.1
  set M : Multiset It :=
    (Finset.univ : Finset (Fin n)).val.map (fun i => (⟨e i, a i, b i, f i⟩ : It)) with hM
  have hMv : ∀ x ∈ M, x.valid := by
    intro x hx
    rw [hM, Multiset.mem_map] at hx
    obtain ⟨i, -, rfl⟩ := hx
    exact hvalid i
  have hMnz : ∀ x ∈ M, x.nz := by
    intro x hx
    rw [hM, Multiset.mem_map] at hx
    obtain ⟨i, -, rfl⟩ := hx
    rcases hnz i with h | h | h
    · exact Or.inl h
    · exact Or.inr (Or.inl h)
    · exact Or.inr (Or.inr h)
  have hE2 : sumE2M M = 3 := by rw [hM, sumE2M_univ]; exact he2
  have hA2 : sumA2M M = 4 := by rw [hM, sumA2M_univ]; exact ha2
  have hB2 : sumB2M M = 7 := by rw [hM, sumB2M_univ]; exact hb2
  have hEA : sumEAM M = 0 := by rw [hM, sumEAM_univ]; exact hea
  have hEB : sumEBM M = -1 := by rw [hM, sumEBM_univ]; exact heb
  have hAB : sumABM M = 0 := by rw [hM, sumABM_univ]; exact hab
  have hEF : sumEFM M = -1 := by rw [hM, sumEFM_univ]; linarith
  have hAF : sumAFM M = 0 := by rw [hM, sumAFM_univ]; exact haf
  have hBF : sumBFM M = -1 := by rw [hM, sumBFM_univ]; linarith
  have hC2EW : sumC2EWM M = -216 := by
    rw [hM, sumC2EWM_univ]
    have hq1' : 1 + ∑ i, ((((b i - 2 * a i) ^ 2 * e i : ℤ) : ℚ) / ((f i : ℤ) : ℚ))
        = 32 / 35 := by
      have hsum : (∑ i, ((((b i - 2 * a i) ^ 2 * e i : ℤ) : ℚ) / ((f i : ℤ) : ℚ)))
          = ∑ i, ((b i - 2 * a i) ^ 2 * e i : ℚ) / (f i : ℚ) := by
        apply Finset.sum_congr rfl
        intro i _
        push_cast
        ring
      rw [hsum]
      exact hq1
    have h := rat_to_int n f (fun i => (b i - 2 * a i) ^ 2 * e i) (32 / 35) hD hq1'
    norm_num at h
    exact_mod_cast h
  have hC3W : sumC3WM M = 2088 := by
    rw [hM, sumC3WM_univ]
    have hq2' : 1 + ∑ i, ((((b i - 2 * a i) ^ 3 : ℤ) : ℚ) / ((f i : ℤ) : ℚ)) = 64 / 35 := by
      have hsum : (∑ i, ((((b i - 2 * a i) ^ 3 : ℤ) : ℚ) / ((f i : ℤ) : ℚ)))
          = ∑ i, ((b i - 2 * a i) ^ 3 : ℚ) / (f i : ℚ) := by
        apply Finset.sum_congr rfl
        intro i _
        push_cast
        ring
      rw [hsum]
      exact hq2
    have h := rat_to_int n f (fun i => (b i - 2 * a i) ^ 3) (64 / 35) hD hq2'
    norm_num at h
    exact_mod_cast h
  have hC2ABW : sumC2ABWM M = 936 := by
    rw [hM, sumC2ABWM_univ]
    have hq3' : 1 + ∑ i, ((((b i - 2 * a i) ^ 2 * (a i + b i) : ℤ) : ℚ) / ((f i : ℤ) : ℚ))
        = 48 / 35 := by
      have hsum : (∑ i, ((((b i - 2 * a i) ^ 2 * (a i + b i) : ℤ) : ℚ) / ((f i : ℤ) : ℚ)))
          = ∑ i, ((b i - 2 * a i) ^ 2 * (a i + b i) : ℚ) / (f i : ℚ) := by
        apply Finset.sum_congr rfl
        intro i _
        push_cast
        ring
      rw [hsum]
      exact hq3
    have h := rat_to_int n f (fun i => (b i - 2 * a i) ^ 2 * (a i + b i)) (48 / 35) hD hq3'
    norm_num at h
    exact_mod_cast h
  have hF2 : sumF2M M ≤ 2519 := by
    rw [hM, sumF2M_univ]
    have h2 : ((∑ i, (f i) ^ 2 : ℕ) : ℤ) ≤ (2519 : ℤ) := by
      have := hle
      omega
    push_cast at h2
    exact h2
  have hM7 : M = A7M :=
    combi M hMv hMnz hE2 hA2 hB2 hEA hEB hAB hEF hAF hBF hC2EW hC3W hC2ABW hF2
  have hfilt : Multiset.filter (fun x : It => x.f = 6) A7M = ({⟨0, -1, 0, 6⟩} : Multiset It) := by
    decide
  constructor
  · have h1 : (∑ i, (f i) ^ 2) = 2519 := by
      have h2 : ((∑ i, (f i) ^ 2 : ℕ) : ℤ) = 2519 := by
        push_cast
        rw [← sumF2M_univ n f e a b, ← hM, hM7]
        decide
      exact_mod_cast h2
    omega
  · have hcnt : (Finset.univ.filter
        (fun i => (⟨e i, a i, b i, f i⟩ : It) = (⟨0, -1, 0, 6⟩ : It))).card = 1 := by
      have h1 : M.count (⟨0, -1, 0, 6⟩ : It) = (Finset.univ.filter
          (fun i => (⟨e i, a i, b i, f i⟩ : It) = (⟨0, -1, 0, 6⟩ : It))).card := by
        rw [hM]
        exact count_map_finset _ _ _
      rw [← h1, hM7]
      decide
    obtain ⟨i0, hi0⟩ := Finset.card_eq_one.mp hcnt
    have hi0mem : i0 ∈ Finset.univ.filter
        (fun i => (⟨e i, a i, b i, f i⟩ : It) = (⟨0, -1, 0, 6⟩ : It)) := by
      rw [hi0]; exact Finset.mem_singleton_self i0
    have hit : (⟨e i0, a i0, b i0, f i0⟩ : It) = (⟨0, -1, 0, 6⟩ : It) :=
      (Finset.mem_filter.mp hi0mem).2
    refine ⟨i0, ?_, ?_, ?_, ?_, ?_⟩
    · exact congrArg It.f hit
    · exact congrArg It.e hit
    · exact congrArg It.a hit
    · exact congrArg It.b hit
    · intro j hj hf6
      apply hj
      have hxj : (⟨e j, a j, b j, f j⟩ : It) ∈ M := by
        rw [hM, Multiset.mem_map]
        exact ⟨j, Finset.mem_univ j, rfl⟩
      have hx7 : (⟨e j, a j, b j, f j⟩ : It) ∈ A7M := by rwa [hM7] at hxj
      have hx6 : (⟨e j, a j, b j, f j⟩ : It) ∈ Multiset.filter (fun x : It => x.f = 6) A7M := by
        rw [Multiset.mem_filter]
        exact ⟨hx7, hf6⟩
      rw [hfilt] at hx6
      have hje : (⟨e j, a j, b j, f j⟩ : It) = (⟨0, -1, 0, 6⟩ : It) :=
        Multiset.mem_singleton.mp hx6
      have hmem : j ∈ Finset.univ.filter
          (fun i => (⟨e i, a i, b i, f i⟩ : It) = (⟨0, -1, 0, 6⟩ : It)) :=
        Finset.mem_filter.mpr ⟨Finset.mem_univ j, hje⟩
      rw [hi0] at hmem
      exact Finset.mem_singleton.mp hmem

end Work.A7REC.Char