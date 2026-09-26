import Mathlib
import Submission.Work.SG.Data.SepCheck

/-!
# `Work.SGsep.bmats_dvd`

The block matrices `Data.bmats D` of the cohomology certificate describe the values of the
cocycle table `Data.repZ k` modulo `n = (Data.repArith k).n`:

`n ∣ (B[i] · y) − z(i)`  for every `i < n`, where `y` collects the generator coordinates
`z(genIdx g)` of `z = repZ[k]` and `B = Data.bmats (Data.repArith k)`.

This is the `applyB` half of the "cocycle propagation" soundness statement needed by
`mergeList_sound`: the recursion defining `B[i+1]` from `B[parent i]` is exactly the cocycle
relation `z(g·A) ≡ z(g) + g z(A) (mod n)` transported along the BFS parent structure of the
element table, so it propagates from `z(1) = 0` to all elements.

The certificate facts used are the kernel-checked `Data.arithData_chk` and `Data.repZ_chk`.
-/

namespace Work.SGsep

open Work.SG

/-! ## 0. Bridges between `Data.V3` / `Data.M3` and matrices -/

theorem M3_toIMat_add (A B : Data.M3) : (Data.M3.add A B).toIMat = A.toIMat + B.toIMat := by
  ext i j; fin_cases i <;> fin_cases j <;> simp [Data.M3.toIMat, Data.M3.add]

theorem M3_toIMat_sub (A B : Data.M3) : (Data.M3.sub A B).toIMat = A.toIMat - B.toIMat := by
  ext i j; fin_cases i <;> fin_cases j <;> simp [Data.M3.toIMat, Data.M3.sub]

theorem M3_toIMat_mul (A B : Data.M3) : (Data.M3.mul A B).toIMat = A.toIMat * B.toIMat := by
  ext i j; fin_cases i <;> fin_cases j <;>
    simp [Data.M3.toIMat, Data.M3.mul, Matrix.mul_apply, Fin.sum_univ_three]

theorem M3_toIMat_zero : (Data.M3.zero).toIMat = (0 : IMat) := by
  ext i j; fin_cases i <;> fin_cases j <;> simp [Data.M3.toIMat, Data.M3.zero]

theorem M3_toIMat_one : (Data.M3.one).toIMat = 1 := by
  ext i j; fin_cases i <;> fin_cases j <;> simp [Data.M3.toIMat, Data.M3.one]

theorem M3_toIMat_mulV (A : Data.M3) (v : Data.V3) :
    (Data.M3.mulV A v).toFun = A.toIMat.mulVec v.toFun := by
  funext k; fin_cases k <;>
    simp [Data.M3.toIMat, Data.M3.mulV, Data.V3.toFun, Matrix.mulVec, dotProduct,
      Fin.sum_univ_three]

theorem V3_toFun_add (u v : Data.V3) : (Data.V3.add u v).toFun = u.toFun + v.toFun := by
  funext c; fin_cases c <;> rfl

theorem V3_toFun_sub (u v : Data.V3) : (Data.V3.sub u v).toFun = u.toFun - v.toFun := by
  funext c; fin_cases c <;> rfl

theorem V3_toFun_zero : (Data.V3.zero).toFun = 0 := by
  funext c; fin_cases c <;> rfl

theorem V3_toFun_inj : Function.Injective Data.V3.toFun := by
  intro a b h
  have h0 := congrFun h 0
  have h1 := congrFun h 1
  have h2 := congrFun h 2
  simp only [Data.V3.toFun] at h0 h1 h2
  cases a; cases b; simp_all

/-! ## 1. Left folds that append one entry per step -/

/-- Fold `l` into `init`, appending `f acc p` at every step. -/
def foldApp {α β : Type*} (l : List β) (init : List α) (f : List α → β → α) : List α :=
  l.foldl (fun acc p => acc ++ [f acc p]) init

theorem foldApp_nil {α β : Type*} (init : List α) (f : List α → β → α) :
    foldApp [] init f = init := rfl

theorem foldApp_cons {α β : Type*} (p : β) (l : List β) (init : List α) (f : List α → β → α) :
    foldApp (p :: l) init f = foldApp l (init ++ [f init p]) f := by
  simp only [foldApp, List.foldl_cons]

theorem foldApp_append {α β : Type*} (l₁ l₂ : List β) (init : List α) (f : List α → β → α) :
    foldApp (l₁ ++ l₂) init f = foldApp l₂ (foldApp l₁ init f) f := by
  induction l₁ generalizing init with
  | nil => simp [foldApp]
  | cons p l ih => rw [List.cons_append, foldApp_cons, foldApp_cons, ih]

theorem foldApp_length {α β : Type*} (l : List β) (init : List α) (f : List α → β → α) :
    (foldApp l init f).length = init.length + l.length := by
  induction l generalizing init with
  | nil => simp [foldApp]
  | cons p l ih =>
    rw [foldApp_cons, ih]
    simp only [List.length_append, List.length_cons, List.length_nil]
    omega

theorem foldApp_eq_append {α β : Type*} (l : List β) (init : List α) (f : List α → β → α) :
    ∃ t : List α, foldApp l init f = init ++ t := by
  induction l generalizing init with
  | nil => exact ⟨[], by simp [foldApp]⟩
  | cons p l ih =>
    obtain ⟨t, ht⟩ := ih (init ++ [f init p])
    exact ⟨[f init p] ++ t, by rw [foldApp_cons, ht, List.append_assoc]⟩

theorem getD_append_of_lt {α : Type*} (l l' : List α) (d : α) {n : ℕ} (h : n < l.length) :
    (l ++ l').getD n d = l.getD n d := by
  induction l generalizing n with
  | nil => simp at h
  | cons a l ih =>
    match n with
    | 0 => rfl
    | n + 1 =>
      rw [List.cons_append, List.getD_cons_succ, List.getD_cons_succ]
      exact ih (by simpa using h)

theorem getD_append_self {α : Type*} (l : List α) (x d : α) :
    (l ++ [x]).getD l.length d = x := by
  induction l with
  | nil => rfl
  | cons a l ih => rw [List.cons_append, List.length_cons, List.getD_cons_succ]; exact ih

theorem foldApp_getD_lt {α β : Type*} (l : List β) (init : List α) (f : List α → β → α) (d : α)
    {n : ℕ} (hn : n < init.length) : (foldApp l init f).getD n d = init.getD n d := by
  obtain ⟨t, ht⟩ := foldApp_eq_append l init f
  rw [ht]
  exact getD_append_of_lt init t d hn

/-- Entries already produced survive further folding. -/
theorem foldApp_getD_prefix {α β : Type*} (l₁ l₂ : List β) (init : List α)
    (f : List α → β → α) (d : α) {n : ℕ} (hn : n < (foldApp l₁ init f).length) :
    (foldApp (l₁ ++ l₂) init f).getD n d = (foldApp l₁ init f).getD n d := by
  rw [foldApp_append]
  exact foldApp_getD_lt l₂ (foldApp l₁ init f) f d hn

/-- The entry appended in the first step. -/
theorem foldApp_getD_head {α β : Type*} (p : β) (l : List β) (init : List α)
    (f : List α → β → α) (d : α) :
    (foldApp (p :: l) init f).getD init.length d = f init p := by
  rw [foldApp_cons, foldApp_getD_lt l (init ++ [f init p]) f d (by simp)]
  exact getD_append_self init (f init p) d

/-! ## 2. `applyB` as a finite sum -/

/-- `A *ᵥ v` for `A : Data.M3` and `v : Fin 3 → ℤ`. -/
def mvf (A : Data.M3) (v : Fin 3 → ℤ) : Fin 3 → ℤ := A.toIMat.mulVec v

theorem mvf_add_mat (A B : Data.M3) (v : Fin 3 → ℤ) :
    mvf (Data.M3.add A B) v = mvf A v + mvf B v := by
  simp only [mvf, M3_toIMat_add, Matrix.add_mulVec]

theorem mvf_zero_mat (v : Fin 3 → ℤ) : mvf Data.M3.zero v = 0 := by
  simp only [mvf, M3_toIMat_zero, Matrix.zero_mulVec]

theorem mvf_one_mat (v : Fin 3 → ℤ) : mvf Data.M3.one v = v := by
  simp only [mvf, M3_toIMat_one, Matrix.one_mulVec]

theorem mvf_mul_mat (A B : Data.M3) (v : Fin 3 → ℤ) :
    mvf (Data.M3.mul A B) v = mvf A (mvf B v) := by
  simp only [mvf, M3_toIMat_mul, Matrix.mulVec_mulVec]

theorem mvf_add (A : Data.M3) (u v : Fin 3 → ℤ) : mvf A (u + v) = mvf A u + mvf A v :=
  Matrix.mulVec_add A.toIMat u v

theorem mvf_sum {ι : Type*} (A : Data.M3) (s : Finset ι) (g : ι → Fin 3 → ℤ) :
    mvf A (∑ i ∈ s, g i) = ∑ i ∈ s, mvf A (g i) := Matrix.mulVec_sum A.toIMat s g

/-- `Data.applyB` phrased as a sum over the blocks. -/
def appV (k : ℕ) (F : ℕ → Data.M3) (y : List ℤ) : Fin 3 → ℤ :=
  ∑ g ∈ Finset.range k, mvf (F g) ((Data.blocks y).getD g Data.V3.zero).toFun

theorem foldr_add_toFun (l : List Data.V3) :
    (l.foldr Data.V3.add Data.V3.zero).toFun
      = ∑ i ∈ Finset.range l.length, (l.getD i Data.V3.zero).toFun := by
  induction l with
  | nil => simp [V3_toFun_zero]
  | cons a t ih =>
    rw [List.foldr_cons, V3_toFun_add, ih, List.length_cons, Finset.sum_range_succ']
    simp only [List.getD_cons_zero, List.getD_cons_succ]
    exact add_comm _ _

theorem zipWith_getD {α β γ : Type*} (f : α → β → γ) (l₁ : List α) (l₂ : List β)
    (d₁ : α) (d₂ : β) (d : γ) {i : ℕ} (hi : i < (List.zipWith f l₁ l₂).length) :
    (List.zipWith f l₁ l₂).getD i d = f (l₁.getD i d₁) (l₂.getD i d₂) := by
  induction l₁ generalizing l₂ i with
  | nil => simp [List.zipWith] at hi
  | cons a as ih =>
    cases l₂ with
    | nil => simp [List.zipWith] at hi
    | cons b bs =>
      match i with
      | 0 => rfl
      | i + 1 =>
        rw [List.zipWith_cons_cons, List.getD_cons_succ, List.getD_cons_succ, List.getD_cons_succ]
        exact ih bs (by simpa [List.zipWith, List.length_cons] using hi)

theorem applyB_toFun_sum (B : List Data.M3) (y : List ℤ)
    (h : B.length ≤ (Data.blocks y).length) :
    (Data.applyB B y).toFun = appV B.length (fun g => B.getD g Data.M3.zero) y := by
  rw [Data.applyB, foldr_add_toFun]
  have hlen : (List.zipWith Data.M3.mulV B (Data.blocks y)).length = B.length := by
    rw [List.length_zipWith, Nat.min_eq_left h]
  rw [hlen]
  refine Finset.sum_congr rfl fun g hg => ?_
  rw [Finset.mem_range] at hg
  rw [zipWith_getD (f := Data.M3.mulV) B (Data.blocks y) Data.M3.zero Data.V3.zero Data.V3.zero
    (i := g) (by rw [hlen]; exact hg)]
  exact M3_toIMat_mulV _ _

theorem appV_add (k : ℕ) (F G : ℕ → Data.M3) (y : List ℤ) :
    appV k (fun g => Data.M3.add (F g) (G g)) y = appV k F y + appV k G y := by
  simp only [appV]
  rw [← Finset.sum_add_distrib]
  exact Finset.sum_congr rfl fun g _ => mvf_add_mat (F g) (G g) _

theorem appV_mul (k : ℕ) (A : Data.M3) (F : ℕ → Data.M3) (y : List ℤ) :
    appV k (fun g => Data.M3.mul A (F g)) y = mvf A (appV k F y) := by
  simp only [appV]
  rw [mvf_sum]
  exact Finset.sum_congr rfl fun g _ => mvf_mul_mat A (F g) _

theorem appV_single (k g₀ : ℕ) (hg₀ : g₀ < k) (A : Data.M3) (y : List ℤ) :
    appV k (fun g => if g = g₀ then A else Data.M3.zero) y
      = mvf A ((Data.blocks y).getD g₀ Data.V3.zero).toFun := by
  simp only [appV]
  rw [Finset.sum_eq_single g₀]
  · simp
  · intro b _ hb
    simp [hb, mvf_zero_mat]
  · intro h
    exact absurd (Finset.mem_range.mpr hg₀) h

theorem appV_congr (k : ℕ) (F G : ℕ → Data.M3) (y : List ℤ) (hh : ∀ g < k, F g = G g) :
    appV k F y = appV k G y :=
  Finset.sum_congr rfl fun g hg => by rw [hh g (Finset.mem_range.mp hg)]

/-! ## 3. Divisibility of `Data.V3` and congruence modulo `n` -/

theorem dvd_iff_toFun (n : ℤ) (v : Data.V3) : v.dvd n = true ↔ ∀ c, n ∣ v.toFun c := by
  simp only [Data.V3.dvd, Bool.and_eq_true, beq_iff_eq]
  constructor
  · rintro ⟨⟨h1, h2⟩, h3⟩ c
    fin_cases c
    · simpa [Data.V3.toFun] using Int.dvd_iff_emod_eq_zero.mpr h1
    · simpa [Data.V3.toFun] using Int.dvd_iff_emod_eq_zero.mpr h2
    · simpa [Data.V3.toFun] using Int.dvd_iff_emod_eq_zero.mpr h3
  · intro h
    refine ⟨⟨?_, ?_⟩, ?_⟩
    · exact Int.dvd_iff_emod_eq_zero.mp (by simpa [Data.V3.toFun] using h 0)
    · exact Int.dvd_iff_emod_eq_zero.mp (by simpa [Data.V3.toFun] using h 1)
    · exact Int.dvd_iff_emod_eq_zero.mp (by simpa [Data.V3.toFun] using h 2)

theorem V3_sub_self_zero : Data.V3.sub Data.V3.zero Data.V3.zero = Data.V3.zero := rfl

theorem dvd_zero_v3 (n : ℤ) : (Data.V3.zero).dvd n = true :=
  (dvd_iff_toFun n _).mpr fun c => by simp [V3_toFun_zero]

theorem dvd_add_v3 {n : ℤ} {u v : Data.V3} (hu : u.dvd n = true) (hv : v.dvd n = true) :
    (Data.V3.add u v).dvd n = true := by
  rw [dvd_iff_toFun] at hu hv ⊢
  intro c
  rw [V3_toFun_add, Pi.add_apply]
  exact dvd_add (hu c) (hv c)

theorem dvd_sub_v3 {n : ℤ} {u v : Data.V3} (hu : u.dvd n = true) (hv : v.dvd n = true) :
    (Data.V3.sub u v).dvd n = true := by
  rw [dvd_iff_toFun] at hu hv ⊢
  intro c
  rw [V3_toFun_sub, Pi.sub_apply]
  exact dvd_sub (hu c) (hv c)

theorem dvd_sub_iff_neg {n : ℤ} (a b : ℤ) : n ∣ b - a ↔ n ∣ a - b := by
  rw [← neg_sub a b]
  exact dvd_neg

theorem dvd_sub_comm_v3 {n : ℤ} {u v : Data.V3} :
    (Data.V3.sub u v).dvd n = true ↔ (Data.V3.sub v u).dvd n = true := by
  rw [dvd_iff_toFun, dvd_iff_toFun]
  constructor
  · intro h c
    have hc : n ∣ u.toFun c - v.toFun c := by
      simpa only [V3_toFun_sub, Pi.sub_apply] using h c
    have h' : n ∣ v.toFun c - u.toFun c :=
      (dvd_sub_iff_neg (n := n) (v.toFun c) (u.toFun c)).mp hc
    simpa only [V3_toFun_sub, Pi.sub_apply] using h'
  · intro h c
    have hc : n ∣ v.toFun c - u.toFun c := by
      simpa only [V3_toFun_sub, Pi.sub_apply] using h c
    have h' : n ∣ u.toFun c - v.toFun c :=
      (dvd_sub_iff_neg (n := n) (u.toFun c) (v.toFun c)).mp hc
    simpa only [V3_toFun_sub, Pi.sub_apply] using h'

theorem dvd_mulV_v3 {n : ℤ} {v : Data.V3} (A : Data.M3) (hv : v.dvd n = true) :
    (Data.M3.mulV A v).dvd n = true := by
  rw [dvd_iff_toFun] at hv ⊢
  intro c
  rw [M3_toIMat_mulV, Matrix.mulVec, dotProduct]
  exact Finset.dvd_sum fun d _ => dvd_mul_of_dvd_right (hv d) _

theorem mulV_sub (A : Data.M3) (u v : Data.V3) :
    Data.M3.mulV A (Data.V3.sub u v) = Data.V3.sub (Data.M3.mulV A u) (Data.M3.mulV A v) := by
  apply V3_toFun_inj
  simp only [V3_toFun_sub, M3_toIMat_mulV, Matrix.mulVec_sub]

theorem add_sub_add (u u' v v' : Data.V3) :
    Data.V3.sub (Data.V3.add u v) (Data.V3.add u' v')
      = Data.V3.add (Data.V3.sub u u') (Data.V3.sub v v') := by
  apply V3_toFun_inj
  funext c
  simp only [V3_toFun_sub, V3_toFun_add, Pi.sub_apply, Pi.add_apply]
  ring

theorem sub_trans (u v w : Data.V3) :
    Data.V3.sub u w = Data.V3.add (Data.V3.sub u v) (Data.V3.sub v w) := by
  apply V3_toFun_inj
  funext c
  simp only [V3_toFun_sub, V3_toFun_add, Pi.sub_apply, Pi.add_apply]
  ring

/-- `u ≡ v (mod n)` for `Data.V3`: the difference is divisible by `n` componentwise. -/
def ModEq (n : ℤ) (u v : Data.V3) : Prop := (Data.V3.sub u v).dvd n = true

theorem modeq_refl (n : ℤ) (u : Data.V3) : ModEq n u u := by
  rw [ModEq, dvd_iff_toFun]
  intro c
  rw [V3_toFun_sub, Pi.sub_apply, sub_self]
  exact dvd_zero n

theorem modeq_symm {n : ℤ} {u v : Data.V3} (h : ModEq n u v) : ModEq n v u :=
  dvd_sub_comm_v3.mp h

theorem modeq_trans {n : ℤ} {u v w : Data.V3} (h1 : ModEq n u v) (h2 : ModEq n v w) :
    ModEq n u w := by
  rw [ModEq, sub_trans u v w]
  exact dvd_add_v3 h1 h2

theorem modeq_add {n : ℤ} {u u' v v' : Data.V3} (h1 : ModEq n u u') (h2 : ModEq n v v') :
    ModEq n (Data.V3.add u v) (Data.V3.add u' v') := by
  rw [ModEq, add_sub_add]
  exact dvd_add_v3 h1 h2

theorem modeq_mulV {n : ℤ} {v v' : Data.V3} (A : Data.M3) (h : ModEq n v v') :
    ModEq n (Data.M3.mulV A v) (Data.M3.mulV A v') := by
  rw [ModEq] at h ⊢
  rw [← mulV_sub]
  exact dvd_mulV_v3 A h

/-! ## 4. The structure of `Data.bmats` -/

/-- The initial accumulator of `Data.bmats`: the block of the identity. -/
def bmatsInit (D : Data.ArithData) : List (List Data.M3) :=
  [List.replicate D.gens.length Data.M3.zero]

/-- One step of the `Data.bmats` recursion. -/
def bmatsStep (D : Data.ArithData) (acc : List (List Data.M3)) (p : ℕ × ℕ) : List Data.M3 :=
  (List.range D.gens.length).map fun g' =>
    Data.M3.add (if g' = p.1 then Data.M3.one else Data.M3.zero)
      (Data.M3.mul (D.gens.getD p.1 Data.M3.one) ((acc.getD p.2 []).getD g' Data.M3.zero))

theorem bmats_eq_foldApp (D : Data.ArithData) :
    Data.bmats D = foldApp D.par (bmatsInit D) (bmatsStep D) := rfl

/-- The accumulator of the `bmats` recursion after `t` steps. -/
def bmatsAcc (D : Data.ArithData) (t : ℕ) : List (List Data.M3) :=
  foldApp (D.par.take t) (bmatsInit D) (bmatsStep D)

theorem bmatsAcc_length (D : Data.ArithData) (t : ℕ) :
    (bmatsAcc D t).length = 1 + (D.par.take t).length := by
  rw [bmatsAcc, foldApp_length]
  simp [bmatsInit]

theorem bmatsAcc_length_le (D : Data.ArithData) (t : ℕ) (ht : t ≤ D.par.length) :
    (bmatsAcc D t).length = t + 1 := by
  rw [bmatsAcc_length, List.length_take, Nat.min_eq_left ht]
  omega

theorem bmats_length (D : Data.ArithData) (hpar : D.par.length + 1 = D.n) :
    (Data.bmats D).length = D.n := by
  rw [bmats_eq_foldApp, foldApp_length]
  simp only [bmatsInit, List.length_cons, List.length_nil]
  omega

theorem bmats_getD_zero (D : Data.ArithData) :
    (Data.bmats D).getD 0 [] = List.replicate D.gens.length Data.M3.zero := by
  rw [bmats_eq_foldApp,
    foldApp_getD_lt D.par (bmatsInit D) (bmatsStep D) [] (by simp [bmatsInit])]
  simp [bmatsInit]

theorem bmatsAcc_getD_eq (D : Data.ArithData) (t n : ℕ)
    (hn : n < (bmatsAcc D t).length) :
    (bmatsAcc D t).getD n [] = (Data.bmats D).getD n [] := by
  have h := foldApp_getD_prefix (D.par.take t) (D.par.drop t) (bmatsInit D) (bmatsStep D) [] hn
  rw [List.take_append_drop t D.par] at h
  rw [← bmats_eq_foldApp] at h
  exact h.symm

theorem bmats_step_list (D : Data.ArithData) (t : ℕ) (ht : t < D.par.length) :
    (Data.bmats D).getD (t + 1) [] = bmatsStep D (bmatsAcc D t) (D.par.getD t (0, 0)) := by
  have hlen : (bmatsAcc D t).length = t + 1 :=
    bmatsAcc_length_le D t (le_of_lt ht)
  have hdrop : D.par.drop t = D.par.getD t (0,0) :: D.par.drop (t+1) := by
    rw [List.drop_eq_getElem_cons ht, ← List.getD_eq_getElem _ _ ht]
  have hkey := foldApp_getD_head (D.par.getD t (0, 0)) (D.par.drop (t + 1)) (bmatsAcc D t)
    (bmatsStep D) []
  rw [hlen] at hkey
  rw [bmats_eq_foldApp]
  conv_lhs => rw [← List.take_append_drop t D.par]
  rw [foldApp_append, hdrop]
  exact hkey

theorem bmats_step_entry (D : Data.ArithData) (t : ℕ) (ht : t < D.par.length)
    (hle : (D.par.getD t (0, 0)).2 ≤ t) (g' : ℕ) (hg' : g' < D.gens.length) :
    ((Data.bmats D).getD (t + 1) []).getD g' Data.M3.zero =
      Data.M3.add (if g' = (D.par.getD t (0, 0)).1 then Data.M3.one else Data.M3.zero)
        (Data.M3.mul (D.gens.getD (D.par.getD t (0, 0)).1 Data.M3.one)
          (((Data.bmats D).getD (D.par.getD t (0, 0)).2 []).getD g' Data.M3.zero)) := by
  rw [bmats_step_list D t ht, bmatsStep]
  rw [List.getD_eq_getElem _ _ (by rw [List.length_map, List.length_range]; exact hg')]
  rw [List.getElem_map, List.getElem_range]
  have hlen : (D.par.getD t (0, 0)).2 < (bmatsAcc D t).length := by
    rw [bmatsAcc_length_le D t (le_of_lt ht)]; omega
  rw [bmatsAcc_getD_eq D t _ hlen]

theorem bmats_entry_length (D : Data.ArithData) (t : ℕ) (ht : t < D.par.length)
    (_hle : (D.par.getD t (0, 0)).2 ≤ t) :
    ((Data.bmats D).getD (t + 1) []).length = D.gens.length := by
  rw [bmats_step_list D t ht, bmatsStep, List.length_map, List.length_range]

theorem bmats_getD_length (D : Data.ArithData) (hpar : D.par.length + 1 = D.n)
    (hle : ∀ t, t < D.par.length → (D.par.getD t (0, 0)).2 ≤ t)
    (i : ℕ) (hi : i < D.n) : ((Data.bmats D).getD i []).length = D.gens.length := by
  match i with
  | 0 => rw [bmats_getD_zero]; simp
  | t + 1 =>
    have ht : t < D.par.length := by omega
    exact bmats_entry_length D t ht (hle t ht)


/-! ## 5. Certified facts about the arithmetic tables (`Data.arithData_chk`) -/

theorem repClass_lt (k : Fin 230) : Data.repClass k.val < 73 := by
  have h : (List.range 230).all (fun k => decide (Data.repClass k < 73)) = true := by
    decide +kernel
  exact of_decide_eq_true (List.all_eq_true.mp h k.val (List.mem_range.mpr k.isLt))

theorem arith_chk (k : Fin 230) : (Data.repArith k.val).chk (Data.repClass k.val) = true :=
  List.all_eq_true.mp Data.arithData_chk (Data.repClass k.val)
    (List.mem_range.mpr (repClass_lt k))

/-- The facts about the element table of `Data.repArith k` that the certificate
`Data.arithData_chk` provides, in the form used below. -/
theorem arith_facts (k : Fin 230) :
    ((Data.repArith k.val).par.length + 1 = (Data.repArith k.val).n) ∧
    (∀ t, t < (Data.repArith k.val).par.length →
      ((Data.repArith k.val).par.getD t (0, 0)).1 < (Data.repArith k.val).gens.length) ∧
    (∀ t, t < (Data.repArith k.val).par.length →
      ((Data.repArith k.val).par.getD t (0, 0)).2 ≤ t) ∧
    (∀ t, t < (Data.repArith k.val).par.length →
      (Data.repArith k.val).elems.getD (t + 1) Data.M3.one =
        Data.M3.mul
          ((Data.repArith k.val).gens.getD ((Data.repArith k.val).par.getD t (0, 0)).1
            Data.M3.one)
          ((Data.repArith k.val).elems.getD ((Data.repArith k.val).par.getD t (0, 0)).2
            Data.M3.one)) ∧
    ((Data.repArith k.val).elems.length = (Data.repArith k.val).n) ∧
    ((Data.repArith k.val).genIdx.length = (Data.repArith k.val).gens.length) ∧
    (∀ g, g < (Data.repArith k.val).gens.length → ∀ i, i < (Data.repArith k.val).n →
      ((Data.repArith k.val).mulGen.getD g []).getD i 0 < (Data.repArith k.val).n) ∧
    (∀ g, g < (Data.repArith k.val).gens.length → ∀ i, i < (Data.repArith k.val).n →
      (Data.repArith k.val).elems.getD
          (((Data.repArith k.val).mulGen.getD g []).getD i 0) Data.M3.one =
        Data.M3.mul ((Data.repArith k.val).gens.getD g Data.M3.one)
          ((Data.repArith k.val).elems.getD i Data.M3.one)) ∧
    (Data.repArith k.val).elems.Nodup := by
  have h := arith_chk k
  simp only [Data.ArithData.chk, Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq,
    List.all_eq_true, List.mem_range] at h
  rcases h with ⟨⟨⟨⟨⟨⟨⟨⟨⟨_, hlen⟩, _⟩, hparlen⟩, hpar⟩, _⟩, hmul⟩, hgilen⟩, _⟩, hnodup⟩
  refine ⟨hparlen, ?_, ?_, ?_, hlen, hgilen, ?_, ?_, hnodup⟩
  · intro t ht; exact (hpar t (by omega)).1.1
  · intro t ht; exact (hpar t (by omega)).1.2
  · intro t ht; exact (hpar t (by omega)).2
  · intro g hg i hi; exact ((hmul g hg).2 i hi).1
  · intro g hg i hi; exact ((hmul g hg).2 i hi).2

/-- Injectivity of the index of a duplicate-free table. -/
theorem nodup_getD_inj {l : List Data.M3} (h : l.Nodup) {a b : ℕ}
    (ha : a < l.length) (hb : b < l.length)
    (heq : l.getD a Data.M3.one = l.getD b Data.M3.one) : a = b := by
  rw [List.getD_eq_getElem _ _ ha, List.getD_eq_getElem _ _ hb] at heq
  exact h.getElem_inj_iff.mp heq

/-! ## 6. Blocks of a flat vector -/

theorem blocks_unblocks (l : List Data.V3) : Data.blocks (Data.unblocks l) = l := by
  induction l with
  | nil => rfl
  | cons v t ih =>
    cases v with
    | mk x y z =>
      simp only [Data.unblocks, List.flatMap_cons, Data.V3.toList, List.cons_append,
        List.nil_append, Data.blocks] at ih ⊢
      rw [ih]

theorem unblocks_map (l : List ℕ) (z : ℕ → Data.V3) :
    Data.unblocks (l.map z) = l.flatMap (fun g => (z g).toList) := by
  induction l with
  | nil => rfl
  | cons a t ih =>
    rw [List.map_cons]
    show (z a).toList ++ Data.unblocks (List.map z t)
        = (z a).toList ++ List.flatMap (fun g => (z g).toList) t
    rw [ih]

/-- The `g`-th block of a flat vector. -/
def blk (y : List ℤ) (g : ℕ) : Data.V3 := (Data.blocks y).getD g Data.V3.zero

theorem blk_flatMap (l : List ℕ) (z : ℕ → Data.V3) (g : ℕ) (hg : g < l.length) :
    blk (l.flatMap (fun g => (z g).toList)) g = z (l.getD g 0) := by
  rw [blk, ← unblocks_map l z, blocks_unblocks,
    List.getD_eq_getElem _ _ (by simpa using hg), List.getD_eq_getElem _ _ hg, List.getElem_map]

theorem replicate_zero_getD (k g : ℕ) :
    (List.replicate k Data.M3.zero).getD g Data.M3.zero = Data.M3.zero := by
  rcases lt_or_ge g k with h | h
  · exact List.getD_replicate Data.M3.zero h
  · exact List.getD_eq_default _ _ (by simpa using h)

theorem appV_zero (k : ℕ) (y : List ℤ) : appV k (fun _ => Data.M3.zero) y = 0 := by
  simp only [appV]
  exact Finset.sum_eq_zero fun g _ => mvf_zero_mat _

/-! ## 7. Certified facts about the cocycle tables (`Data.repZ_chk`) -/

/-- The value of the cocycle table of representative `k` at element `i`. -/
def zTab (k : Fin 230) (i : ℕ) : Data.V3 := (Data.repZ.getD k.val []).getD i Data.V3.zero

theorem repZ_chk_true (k : Fin 230) : Data.repZChk k.val = true :=
  List.all_eq_true.mp Data.repZ_chk k.val (List.mem_range.mpr k.isLt)

theorem dvd_of_eq_emod {n : ℤ} {u v : Data.V3} (h : u = v.emod n) :
    (Data.V3.sub u v).dvd n = true := by
  rw [dvd_iff_toFun]
  intro c
  have hc : u.toFun c = v.toFun c % n := by
    rw [h]
    fin_cases c <;> rfl
  rw [V3_toFun_sub, Pi.sub_apply, hc]
  refine ⟨-(v.toFun c / n), ?_⟩
  have h1 := Int.mul_ediv_add_emod (v.toFun c) n
  linarith

/-- The cocycle table of `k` starts at `0` and satisfies the cocycle recursion modulo `n`. -/
theorem repZ_facts (k : Fin 230) :
    zTab k 0 = Data.V3.zero ∧
    (∀ g, g < (Data.repArith k.val).gens.length → ∀ i, i < (Data.repArith k.val).n →
      (Data.V3.sub (zTab k (((Data.repArith k.val).mulGen.getD g []).getD i 0))
        (Data.V3.add (zTab k ((Data.repArith k.val).genIdx.getD g 0))
          (Data.M3.mulV ((Data.repArith k.val).gens.getD g Data.M3.one) (zTab k i)))).dvd
        ((Data.repArith k.val).n : ℤ) = true) := by
  have h := repZ_chk_true k
  simp only [Data.repZChk, Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq, List.all_eq_true,
    List.mem_range] at h
  obtain ⟨⟨⟨⟨h1, h2⟩, _⟩, h4⟩, _⟩ := h
  refine ⟨?_, ?_⟩
  · show (Data.repZ.getD k.val []).getD 0 Data.V3.zero = Data.V3.zero
    rcases List.head?_eq_some_iff.mp h2 with ⟨t, ht⟩
    rw [ht]
    rfl
  · intro g hg i hi
    exact dvd_of_eq_emod (h4 g hg i hi)

/-! ## 8. Propagation of the cocycle recursion along the parent structure -/

/-- **The general propagation lemma.**  If `z` is a table on the elements of the arithmetic
class `D` satisfying `z(0) = 0` and the cocycle recursion
`z(g·A) ≡ z(g) + g z(A) (mod n)`, then `applyB` of the parent-recursion block matrix `B[i]`
reproduces `z(i)` modulo `n` for every element `i`. -/
theorem bmats_dvd_general (D : Data.ArithData)
    (hpar : D.par.length + 1 = D.n)
    (hpar1 : ∀ t, t < D.par.length → ((D.par.getD t (0, 0)).1) < D.gens.length)
    (hpar2 : ∀ t, t < D.par.length → ((D.par.getD t (0, 0)).2) ≤ t)
    (hparel : ∀ t, t < D.par.length →
      D.elems.getD (t + 1) Data.M3.one =
        Data.M3.mul (D.gens.getD ((D.par.getD t (0, 0)).1) Data.M3.one)
          (D.elems.getD ((D.par.getD t (0, 0)).2) Data.M3.one))
    (hlen : D.elems.length = D.n)
    (hnodup : D.elems.Nodup)
    (hgilen : D.genIdx.length = D.gens.length)
    (hmulgen_bound : ∀ g, g < D.gens.length → ∀ i, i < D.n →
      ((D.mulGen.getD g []).getD i 0) < D.n)
    (hmulgen_rel : ∀ g, g < D.gens.length → ∀ i, i < D.n →
      D.elems.getD (((D.mulGen.getD g []).getD i 0)) Data.M3.one =
        Data.M3.mul (D.gens.getD g Data.M3.one) (D.elems.getD i Data.M3.one))
    {z : ℕ → Data.V3} (hz0 : z 0 = Data.V3.zero)
    (hzrec : ∀ g, g < D.gens.length → ∀ i, i < D.n →
      (Data.V3.sub (z (((D.mulGen.getD g []).getD i 0)))
        (Data.V3.add (z (D.genIdx.getD g 0))
          (Data.M3.mulV (D.gens.getD g Data.M3.one) (z i)))).dvd (D.n : ℤ) = true) :
    ∀ i, i < D.n →
      (Data.V3.sub
        (Data.applyB ((Data.bmats D).getD i []) (D.genIdx.flatMap (fun g => (z g).toList)))
        (z i)).dvd (D.n : ℤ) = true := by
  set y := D.genIdx.flatMap (fun g => (z g).toList) with hydef
  have hblocks : Data.blocks y = D.genIdx.map z := by
    rw [hydef, ← unblocks_map D.genIdx z, blocks_unblocks]
  have hlenY : (Data.blocks y).length = D.gens.length := by
    rw [hblocks, List.length_map, hgilen]
  intro i
  refine Nat.strong_induction_on i (fun i ih => ?_)
  intro hi
  by_cases h0 : i = 0
  · subst i
    have hlen0 : ((Data.bmats D).getD 0 []).length ≤ (Data.blocks y).length :=
      le_of_eq (by rw [bmats_getD_zero, List.length_replicate, hlenY])
    have hzero : Data.applyB ((Data.bmats D).getD 0 []) y = Data.V3.zero := by
      apply V3_toFun_inj
      rw [applyB_toFun_sum _ _ hlen0]
      rw [appV_congr ((Data.bmats D).getD 0 []).length _ (fun _ => Data.M3.zero) y
        (fun g _ => by rw [bmats_getD_zero]; exact replicate_zero_getD _ _)]
      rw [appV_zero, V3_toFun_zero]
    rw [hzero, hz0, V3_sub_self_zero]
    exact dvd_zero_v3 _
  · obtain ⟨t, rfl⟩ := Nat.exists_eq_succ_of_ne_zero h0
    have ht : t < D.par.length := by omega
    have hg₁ : ((D.par.getD t (0, 0)).1) < D.gens.length := hpar1 t ht
    have hp2le : ((D.par.getD t (0, 0)).2) ≤ t := hpar2 t ht
    have hp2n : ((D.par.getD t (0, 0)).2) < D.n := by omega
    have hidx :
        ((D.mulGen.getD ((D.par.getD t (0, 0)).1) []).getD ((D.par.getD t (0, 0)).2) 0)
          = t + 1 := by
      refine nodup_getD_inj (l := D.elems) hnodup ?_ ?_ ?_
      · rw [hlen]; exact hmulgen_bound _ hg₁ _ hp2n
      · rw [hlen]; omega
      · rw [hmulgen_rel _ hg₁ _ hp2n, hparel t ht]
    have ihp := ih ((D.par.getD t (0, 0)).2) (by omega) hp2n
    have hlenBnew : ((Data.bmats D).getD (t + 1) []).length = D.gens.length :=
      bmats_entry_length D t ht hp2le
    have hlenBp : ((Data.bmats D).getD ((D.par.getD t (0, 0)).2) []).length
        = D.gens.length :=
      bmats_getD_length D hpar hpar2 _ hp2n
    have hblk : (Data.blocks y).getD ((D.par.getD t (0, 0)).1) Data.V3.zero
        = z (D.genIdx.getD ((D.par.getD t (0, 0)).1) 0) := by
      rw [hydef]
      exact blk_flatMap D.genIdx z _ (by rw [hgilen]; exact hg₁)
    have hstep : ∀ g', g' < D.gens.length →
        ((Data.bmats D).getD (t + 1) []).getD g' Data.M3.zero =
          Data.M3.add (if g' = (D.par.getD t (0, 0)).1 then Data.M3.one else Data.M3.zero)
            (Data.M3.mul (D.gens.getD ((D.par.getD t (0, 0)).1) Data.M3.one)
              (((Data.bmats D).getD ((D.par.getD t (0, 0)).2) []).getD g'
                Data.M3.zero)) :=
      fun g' hg' => bmats_step_entry D t ht hp2le g' hg'
    have key : Data.applyB ((Data.bmats D).getD (t + 1) []) y
        = Data.V3.add (z (D.genIdx.getD ((D.par.getD t (0, 0)).1) 0))
            (Data.M3.mulV (D.gens.getD ((D.par.getD t (0, 0)).1) Data.M3.one)
              (Data.applyB ((Data.bmats D).getD ((D.par.getD t (0, 0)).2) []) y)) := by
      apply V3_toFun_inj
      rw [applyB_toFun_sum _ _ (le_of_eq (hlenBnew.trans hlenY.symm)), hlenBnew]
      rw [appV_congr _ _ _ _ hstep, appV_add, appV_single _ _ hg₁ _ _, appV_mul]
      rw [V3_toFun_add, mvf_one_mat, hblk]
      congr 1
      · rw [← hlenBp, ← applyB_toFun_sum _ _ (le_of_eq (hlenBp.trans hlenY.symm))]
        exact (M3_toIMat_mulV _ _).symm
    show ModEq (D.n : ℤ) (Data.applyB ((Data.bmats D).getD (t + 1) []) y) (z (t + 1))
    rw [key]
    refine modeq_trans (modeq_add (modeq_refl _ _) (modeq_mulV _ ihp)) ?_
    rw [← hidx]
    exact modeq_symm (hzrec _ hg₁ _ hp2n)

/-! ## 9. The requested statement -/

theorem bmats_dvd (k : Fin 230) (i : ℕ) (hi : i < (Work.SG.Data.repArith k.val).n) :
    Work.SG.Data.V3.dvd ((Work.SG.Data.repArith k.val).n : ℤ)
      (Work.SG.Data.V3.sub
        (Work.SG.Data.applyB ((Work.SG.Data.bmats (Work.SG.Data.repArith k.val)).getD i [])
          ((Work.SG.Data.repArith k.val).genIdx.flatMap
            (fun g => ((Work.SG.Data.repZ.getD k.val []).getD g Work.SG.Data.V3.zero).toList)))
        ((Work.SG.Data.repZ.getD k.val []).getD i Work.SG.Data.V3.zero)) = true := by
  obtain ⟨hpar, hpar1, hpar2, hparel, hlen, hgilen, hmulgen_bound, hmulgen_rel, hnodup⟩ :=
    arith_facts k
  obtain ⟨hz0, hzrec⟩ := repZ_facts k
  exact bmats_dvd_general (Data.repArith k.val) hpar hpar1 hpar2 hparel hlen hnodup hgilen
    hmulgen_bound hmulgen_rel hz0 hzrec i hi

end Work.SGsep
