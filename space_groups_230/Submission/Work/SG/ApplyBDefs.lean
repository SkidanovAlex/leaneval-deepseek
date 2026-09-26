import Mathlib
import Submission.Work.SG.SGRepDefs

/-!
# Auxiliary vocabulary for `Work.SG.RepCoh_applyB`

`Data.applyB` is a right fold of `Data.V3.add` over `List.zipWith Data.M3.mulV _ (Data.blocks y)`
and `Data.bmats` is a `List.foldl` appending one block per entry of `ArithData.par`.  This file
provides

* the `Fin 3 → ℤ` mirror `mvf` of `Data.M3.mulV` and the `Finset`-sum form `appV` of `Data.applyB`;
* the generic `foldlApp` helper ("fold left, appending one element each step") with the `getD`
  lemmas describing the accumulators it builds;
* elementary algebra of `Data.V3` / `Data.M3`;
* the congruence relation `congV n u v := Data.V3.dvd n (Data.V3.sub u v) = true` and its closure
  properties.

Nothing here is `sorry`ed.
-/

namespace Work.SG

open Work.SG.RC

/-! ## 1. `Data.M3.mulV` in the `Fin 3 → ℤ` picture -/

/-- `A *ᵥ v` for `A : Data.M3` and `v : Fin 3 → ℤ` (the `Matrix`-side mirror of `Data.M3.mulV`). -/
def mvf (A : Data.M3) (v : Fin 3 → ℤ) : Fin 3 → ℤ := A.toIMat.mulVec v

theorem mvf_eq_mulV (A : Data.M3) (v : Data.V3) :
    mvf A v.toFun = (Data.M3.mulV A v).toFun := (CZ.toIMat_mulV A v).symm

theorem toIMat_add (A B : Data.M3) : (Data.M3.add A B).toIMat = A.toIMat + B.toIMat := by
  ext i j; fin_cases i <;> fin_cases j <;> rfl

theorem toIMat_sub (A B : Data.M3) : (Data.M3.sub A B).toIMat = A.toIMat - B.toIMat := by
  ext i j; fin_cases i <;> fin_cases j <;> rfl

theorem toIMat_zero : (Data.M3.zero).toIMat = (0 : IMat) := by
  ext i j; fin_cases i <;> fin_cases j <;> rfl

theorem mvf_add_mat (A B : Data.M3) (v : Fin 3 → ℤ) :
    mvf (Data.M3.add A B) v = mvf A v + mvf B v := by
  simp only [mvf, toIMat_add, Matrix.add_mulVec]

theorem mvf_sub_mat (A B : Data.M3) (v : Fin 3 → ℤ) :
    mvf (Data.M3.sub A B) v = mvf A v - mvf B v := by
  simp only [mvf, toIMat_sub, Matrix.sub_mulVec]

theorem mvf_zero_mat (v : Fin 3 → ℤ) : mvf Data.M3.zero v = 0 := by
  simp only [mvf, toIMat_zero, Matrix.zero_mulVec]

theorem mvf_one_mat (v : Fin 3 → ℤ) : mvf Data.M3.one v = v := by
  simp only [mvf, CZ.toIMat_one, Matrix.one_mulVec]

theorem mvf_mul_mat (A B : Data.M3) (v : Fin 3 → ℤ) :
    mvf (Data.M3.mul A B) v = mvf A (mvf B v) := by
  simp only [mvf, CZ.toIMat_mul, Matrix.mulVec_mulVec]

theorem mvf_add (A : Data.M3) (u v : Fin 3 → ℤ) : mvf A (u + v) = mvf A u + mvf A v := by
  simp only [mvf]; exact Matrix.mulVec_add A.toIMat u v

theorem mvf_sum {ι : Type*} (A : Data.M3) (s : Finset ι) (f : ι → Fin 3 → ℤ) :
    mvf A (∑ i ∈ s, f i) = ∑ i ∈ s, mvf A (f i) := by
  simp only [mvf]; exact Matrix.mulVec_sum A.toIMat s f

theorem mvf_apply_eq (A : Data.M3) (v : Fin 3 → ℤ) (c : Fin 3) :
    mvf A v c = ∑ d : Fin 3, A.toIMat c d * v d := by
  simp only [mvf, Matrix.mulVec, dotProduct]

/-! ## 2. `Data.applyB` as a `Finset` sum -/

/-- `Data.applyB` with the block matrices listed by a function `F` on the first `k` indices. -/
def appV (k : ℕ) (F : ℕ → Data.M3) (y : List ℤ) : Fin 3 → ℤ :=
  ∑ g ∈ Finset.range k, mvf (F g) ((Data.blocks y).getD g Data.V3.zero).toFun

theorem appV_add (k : ℕ) (F G : ℕ → Data.M3) (y : List ℤ) :
    appV k (fun g => Data.M3.add (F g) (G g)) y = appV k F y + appV k G y := by
  simp only [appV]
  rw [← Finset.sum_add_distrib]
  exact Finset.sum_congr rfl fun g _ => by rw [mvf_add_mat]

theorem appV_sub (k : ℕ) (F G : ℕ → Data.M3) (y : List ℤ) :
    appV k (fun g => Data.M3.sub (F g) (G g)) y = appV k F y - appV k G y := by
  simp only [appV]
  rw [← Finset.sum_sub_distrib]
  exact Finset.sum_congr rfl fun g _ => by rw [mvf_sub_mat]

theorem appV_mul (k : ℕ) (A : Data.M3) (F : ℕ → Data.M3) (y : List ℤ) :
    appV k (fun g => Data.M3.mul A (F g)) y = mvf A (appV k F y) := by
  simp only [appV]
  rw [mvf_sum]
  exact Finset.sum_congr rfl fun g _ => mvf_mul_mat A (F g) _

theorem appV_single (k : ℕ) (g₀ : ℕ) (hg₀ : g₀ < k) (A : Data.M3) (y : List ℤ) :
    appV k (fun g => if g = g₀ then A else Data.M3.zero) y
      = mvf A ((Data.blocks y).getD g₀ Data.V3.zero).toFun := by
  simp only [appV]
  rw [Finset.sum_eq_single g₀]
  · simp
  · intro b _ hb
    rw [if_neg hb]
    exact mvf_zero_mat _
  · intro h
    exact absurd (Finset.mem_range.mpr hg₀) h

theorem appV_congr (k : ℕ) (F G : ℕ → Data.M3) (y : List ℤ)
    (h : ∀ g < k, F g = G g) : appV k F y = appV k G y :=
  Finset.sum_congr rfl fun g hg => by rw [h g (Finset.mem_range.mp hg)]


theorem getD_map_lt {α β : Type*} (f : α → β) (l : List α) (d : β) (d' : α) {n : ℕ}
    (h : n < l.length) : (l.map f).getD n d = f (l.getD n d') := by
  rw [List.getD_eq_getElem _ _ (by rwa [List.length_map]), List.getElem_map,
    List.getD_eq_getElem _ _ h]

/-! ## 3. A generic "fold left, appending one element each step" -/

/-- Left fold of `List β` over `List α` that appends `f acc p` at each step. -/
def foldlApp {α β : Type*} (l : List β) (init : List α) (f : List α → β → α) : List α :=
  l.foldl (fun acc p => acc ++ [f acc p]) init

theorem foldlApp_cons {α β : Type*} (p : β) (l : List β) (init : List α)
    (f : List α → β → α) :
    foldlApp (p :: l) init f = foldlApp l (init ++ [f init p]) f := by
  simp only [foldlApp, List.foldl_cons]

theorem getD_concat {α : Type*} (l : List α) (x d : α) :
    (l ++ [x]).getD l.length d = x := by
  rw [List.getD_eq_getElem _ _ (by simp)]
  rw [List.getElem_append_right (le_refl _)]
  simp

theorem foldlApp_length {α β : Type*} (l : List β) (init : List α) (f : List α → β → α) :
    (foldlApp l init f).length = init.length + l.length := by
  induction l generalizing init with
  | nil => simp [foldlApp]
  | cons p l ih =>
    rw [foldlApp_cons, ih (init ++ [f init p])]
    simp only [List.length_append, List.length_cons, List.length_nil, Nat.add_zero]
    omega

theorem foldlApp_getD_lt {α β : Type*} (l : List β) (init : List α) (f : List α → β → α)
    (d : α) {n : ℕ} (hn : n < init.length) :
    (foldlApp l init f).getD n d = init.getD n d := by
  induction l generalizing init with
  | nil => simp [foldlApp]
  | cons p l ih =>
    have hn' : n < (init ++ [f init p]).length := by
      simp only [List.length_append, List.length_cons, List.length_nil, Nat.add_zero]
      omega
    rw [foldlApp_cons, ih _ hn']
    exact List.getD_append init [f init p] d n hn

theorem foldlApp_getD_eq {α β : Type*} (l : List β) (init : List α) (f : List α → β → α)
    (d : α) (d' : β) (t : ℕ) (ht : t < l.length) :
    (foldlApp l init f).getD (init.length + t) d
      = f (foldlApp (l.take t) init f) (l.getD t d') := by
  induction l generalizing init t with
  | nil => simp at ht
  | cons p l ih =>
    match t with
    | 0 =>
      rw [foldlApp_cons, Nat.add_zero]
      have h1 : (foldlApp l (init ++ [f init p]) f).getD init.length d = f init p := by
        rw [foldlApp_getD_lt l (init ++ [f init p]) f d (by simp)]
        exact getD_concat init (f init p) d
      rw [h1]
      simp [foldlApp]
    | t + 1 =>
      have ht' : t < l.length := by simpa using ht
      have hb : init.length + (t + 1) = (init ++ [f init p]).length + t := by
        rw [List.length_append, List.length_cons, List.length_nil]; omega
      rw [foldlApp_cons, hb, ih (init ++ [f init p]) t ht']
      have h1 : foldlApp (l.take t) (init ++ [f init p]) f = foldlApp ((p :: l).take (t + 1)) init f := by
        rw [List.take_succ_cons, foldlApp_cons]
      have h2 : l.getD t d' = (p :: l).getD (t + 1) d' := by simp
      rw [h1, h2]

/-! ## 4. `Data.V3` algebra via the `toFun` embedding -/

theorem toFun_add (a b : Data.V3) : (Data.V3.add a b).toFun = a.toFun + b.toFun := by
  cases a; cases b; funext c; fin_cases c <;> rfl

theorem toFun_sub (a b : Data.V3) : (Data.V3.sub a b).toFun = a.toFun - b.toFun := by
  cases a; cases b; funext c; fin_cases c <;> rfl

theorem toFun_smul (k : ℤ) (a : Data.V3) : (Data.V3.smul k a).toFun = k • a.toFun := by
  cases a; funext c; fin_cases c <;> rfl

theorem toFun_zero : (Data.V3.zero).toFun = 0 := by
  funext c; fin_cases c <;> rfl

theorem V3_add_assoc (a b c : Data.V3) :
    Data.V3.add (Data.V3.add a b) c = Data.V3.add a (Data.V3.add b c) := by
  apply CZ.toFun_inj
  rw [toFun_add, toFun_add, toFun_add, toFun_add]
  exact add_assoc _ _ _

theorem V3_add_comm (a b : Data.V3) : Data.V3.add a b = Data.V3.add b a := by
  apply CZ.toFun_inj
  rw [toFun_add, toFun_add]
  exact add_comm _ _

theorem V3_add_zero (a : Data.V3) : Data.V3.add a Data.V3.zero = a := by
  apply CZ.toFun_inj
  rw [toFun_add, toFun_zero]
  exact add_zero _

theorem V3_zero_add (a : Data.V3) : Data.V3.add Data.V3.zero a = a := by
  apply CZ.toFun_inj
  rw [toFun_add, toFun_zero]
  exact zero_add _

theorem V3_sub_self (a : Data.V3) : Data.V3.sub a a = Data.V3.zero := by
  apply CZ.toFun_inj
  rw [toFun_sub, toFun_zero]
  exact sub_self _

theorem V3_sub_zero (a : Data.V3) : Data.V3.sub a Data.V3.zero = a := by
  apply CZ.toFun_inj
  rw [toFun_sub, toFun_zero]
  exact sub_zero _

/-- `mulV A` is additive. -/
theorem mulV_add (A : Data.M3) (v w : Data.V3) :
    Data.M3.mulV A (Data.V3.add v w) = Data.V3.add (Data.M3.mulV A v) (Data.M3.mulV A w) := by
  apply CZ.toFun_inj
  rw [toFun_add, ← mvf_eq_mulV A (Data.V3.add v w), ← mvf_eq_mulV A v, ← mvf_eq_mulV A w,
    toFun_add, mvf_add]

/-- `mulV A` is additive for subtraction. -/
theorem mulV_sub (A : Data.M3) (v w : Data.V3) :
    Data.M3.mulV A (Data.V3.sub v w) = Data.V3.sub (Data.M3.mulV A v) (Data.M3.mulV A w) := by
  obtain ⟨vx, vy, vz⟩ := v; obtain ⟨wx, wy, wz⟩ := w
  obtain ⟨Aa, Ab, Ac, Ad, Ae, Af, Ag, Ah, Ai⟩ := A
  simp only [Data.V3.sub, Data.V3.add, Data.M3.mulV, Data.V3.mk.injEq]
  refine ⟨?_, ?_, ?_⟩ <;> ring

/-- The telescoping identity used for the cocycle induction. -/
theorem V3_sub_add_cancel (a b : Data.V3) (A : Data.M3) (v w : Data.V3) :
    Data.V3.sub a (Data.V3.add b (Data.M3.mulV A w)) =
      Data.V3.add (Data.V3.sub a (Data.V3.add b (Data.M3.mulV A v)))
        (Data.M3.mulV A (Data.V3.sub v w)) := by
  obtain ⟨ax, ay, az⟩ := a; obtain ⟨bx, byy, bz⟩ := b
  obtain ⟨vx, vy, vz⟩ := v; obtain ⟨wx, wy, wz⟩ := w
  obtain ⟨Aa, Ab, Ac, Ad, Ae, Af, Ag, Ah, Ai⟩ := A
  simp only [Data.V3.sub, Data.V3.add, Data.M3.mulV, Data.V3.mk.injEq]
  refine ⟨?_, ?_, ?_⟩ <;> ring

theorem M3_zero_mulV (v : Data.V3) : Data.M3.mulV Data.M3.zero v = Data.V3.zero := by
  obtain ⟨x, y, z⟩ := v
  simp [Data.M3.mulV, Data.M3.zero, Data.V3.zero]

/-- `applyB` of an all-zero block list vanishes. -/
theorem applyB_replicate_zero (k : ℕ) (l : List Data.V3) :
    Data.applyB (List.replicate k Data.M3.zero) (Data.unblocks l) = Data.V3.zero := by
  induction l generalizing k with
  | nil => rw [Data.applyB, RC.blocks_unblocks]; simp
  | cons v l ih =>
    cases k with
    | zero => rw [Data.applyB]; simp
    | succ k =>
      have ih' := ih k
      rw [Data.applyB, RC.blocks_unblocks] at ih'
      rw [Data.applyB, RC.blocks_unblocks, List.replicate_succ, List.zipWith_cons_cons,
        List.foldr_cons, ih', M3_zero_mulV, V3_zero_add]

/-! ## 5. `Data.V3.dvd` closure properties and the congruence relation `congV` -/

theorem V3_dvd_add {n : ℤ} {u v : Data.V3} (hu : Data.V3.dvd n u = true)
    (hv : Data.V3.dvd n v = true) : Data.V3.dvd n (Data.V3.add u v) = true := by
  rw [RC.dvd_iff_toFun] at hu hv ⊢
  intro c
  rw [toFun_add, Pi.add_apply]
  exact dvd_add (hu c) (hv c)

theorem V3_dvd_zero (n : ℤ) : Data.V3.dvd n Data.V3.zero = true := by
  rw [RC.dvd_iff_toFun]
  intro c
  rw [toFun_zero]
  exact dvd_zero n

theorem V3_dvd_mulV {n : ℤ} {v : Data.V3} (A : Data.M3) (hv : Data.V3.dvd n v = true) :
    Data.V3.dvd n (Data.M3.mulV A v) = true := by
  rw [RC.dvd_iff_toFun] at hv ⊢
  intro c
  rw [← mvf_eq_mulV A v, mvf_apply_eq]
  exact Finset.dvd_sum fun d _ => dvd_mul_of_dvd_right (hv d) _

/-- The congruence relation attached to `Data.V3.dvd`: `u ≡ v (mod n)`. -/
def congV (n : ℤ) (u v : Data.V3) : Prop := Data.V3.dvd n (Data.V3.sub u v) = true

theorem congV_refl (n : ℤ) (u : Data.V3) : congV n u u := by
  rw [congV, V3_sub_self]; exact V3_dvd_zero n

theorem congV_symm {n : ℤ} {u v : Data.V3} (h : congV n u v) : congV n v u := by
  rw [congV] at h ⊢
  rw [RC.dvd_iff_toFun] at h ⊢
  intro c
  have hc : n ∣ u.toFun c - v.toFun c := by simpa [toFun_sub] using h c
  have h3 : n ∣ -(u.toFun c - v.toFun c) := dvd_neg.mpr hc
  simpa [toFun_sub, sub_eq_add_neg, add_comm] using h3

theorem congV_trans {n : ℤ} {u v w : Data.V3} (h1 : congV n u v) (h2 : congV n v w) :
    congV n u w := by
  rw [congV] at h1 h2 ⊢
  rw [RC.dvd_iff_toFun] at h1 h2 ⊢
  intro c
  have hc1 : n ∣ u.toFun c - v.toFun c := by simpa [toFun_sub] using h1 c
  have hc2 : n ∣ v.toFun c - w.toFun c := by simpa [toFun_sub] using h2 c
  have hsum : n ∣ (u.toFun c - v.toFun c) + (v.toFun c - w.toFun c) := dvd_add hc1 hc2
  have he : (u.toFun c - v.toFun c) + (v.toFun c - w.toFun c) = u.toFun c - w.toFun c := by ring
  simpa [toFun_sub, he] using hsum

theorem congV_add {n : ℤ} {u u' v v' : Data.V3} (h1 : congV n u u') (h2 : congV n v v') :
    congV n (Data.V3.add u v) (Data.V3.add u' v') := by
  rw [congV] at h1 h2 ⊢
  rw [RC.dvd_iff_toFun] at h1 h2 ⊢
  intro c
  have hc1 : n ∣ u.toFun c - u'.toFun c := by simpa [toFun_sub] using h1 c
  have hc2 : n ∣ v.toFun c - v'.toFun c := by simpa [toFun_sub] using h2 c
  have hsum : n ∣ (u.toFun c - u'.toFun c) + (v.toFun c - v'.toFun c) := dvd_add hc1 hc2
  have he2 : ((Data.V3.add u v).sub (Data.V3.add u' v')).toFun c
      = (u.toFun c - u'.toFun c) + (v.toFun c - v'.toFun c) := by
    simp only [toFun_sub, toFun_add, Pi.sub_apply, Pi.add_apply]
    ring
  rw [he2]
  exact hsum

theorem congV_mulV {n : ℤ} {u v : Data.V3} (A : Data.M3) (h : congV n u v) :
    congV n (Data.M3.mulV A u) (Data.M3.mulV A v) := by
  rw [congV] at h ⊢
  rw [← mulV_sub]
  exact V3_dvd_mulV A h

theorem congV_zero {n : ℤ} {u : Data.V3} (h : Data.V3.dvd n u = true) :
    congV n u Data.V3.zero := by
  rw [congV, V3_sub_zero]; exact h

theorem congV_dvd {n : ℤ} {u v : Data.V3} (h : congV n u v) (h0 : ∀ c, n ∣ v.toFun c) :
    ∀ c, n ∣ u.toFun c := by
  rw [congV] at h
  rw [RC.dvd_iff_toFun] at h
  intro c
  have hc : n ∣ u.toFun c - v.toFun c := by simpa [toFun_sub] using h c
  have he : u.toFun c = (u.toFun c - v.toFun c) + v.toFun c := by ring
  rw [he]
  exact dvd_add hc (h0 c)

/-! ## 6. Lengths and `getD` bookkeeping -/

theorem blocks_length : ∀ y : List ℤ, (Data.blocks y).length = y.length / 3
  | [] => rfl
  | [x] => by
      show (0 : ℕ) = [x].length / 3
      rw [Nat.div_eq_of_lt (by simp)]
  | [x, y] => by
      show (0 : ℕ) = [x, y].length / 3
      rw [Nat.div_eq_of_lt (by simp)]
  | a :: b :: c :: t => by
      show (Data.blocks t).length + 1 = (t.length + 3) / 3
      rw [blocks_length t]
      omega


theorem foldlApp_getD_of_take {α β : Type*} (l : List β) (init : List α)
    (f : List α → β → α) (d : α) (d' : β) (t s : ℕ) (ht : t < l.length) (hts : t < s)
    (hsl : s ≤ l.length) :
    (foldlApp l init f).getD (init.length + t) d
      = (foldlApp (l.take s) init f).getD (init.length + t) d := by
  rw [foldlApp_getD_eq l init f d d' t ht,
    foldlApp_getD_eq (l.take s) init f d d' t (by simp only [List.length_take]; omega)]
  have h1 : (l.take s).take t = l.take t := by
    rw [List.take_take]
    have : min t s = t := by omega
    rw [this]
  have h3 : (l.take s).getD t d' = l.getD t d' := by
    rw [List.getD_eq_getElem _ _ (by simp only [List.length_take]; omega), List.getElem_take,
      ← List.getD_eq_getElem _ _ ht]
  rw [h1, h3]

theorem foldlApp_rowlen {γ β : Type*} (l : List β) (init : List (List γ))
    (f : List (List γ) → β → List γ) (d : ℕ) (hinit : ∀ a ∈ init, a.length = d)
    (hf : ∀ acc p, (∀ a ∈ acc, a.length = d) → (f acc p).length = d) :
    ∀ a ∈ foldlApp l init f, a.length = d := by
  induction l generalizing init with
  | nil => simpa [foldlApp] using hinit
  | cons p l ih =>
    rw [foldlApp_cons]
    refine ih (init ++ [f init p]) ?_
    intro a ha
    rw [List.mem_append] at ha
    rcases ha with ha | ha
    · exact hinit a ha
    · rw [List.mem_singleton] at ha
      subst ha
      exact hf init p hinit

theorem sum_zipWith (f : ℤ → ℤ → ℤ) (l1 l2 : List ℤ) :
    (List.zipWith f l1 l2).sum
      = ∑ g ∈ Finset.range (min l1.length l2.length), f (l1.getD g 0) (l2.getD g 0) := by
  induction l1 generalizing l2 with
  | nil => simp
  | cons a l1 ih =>
    cases l2 with
    | nil => simp
    | cons b l2 =>
      rw [List.zipWith_cons_cons, List.sum_cons]
      simp only [List.length_cons]
      have hmin : min (l1.length + 1) (l2.length + 1) = min l1.length l2.length + 1 := by omega
      rw [hmin, Finset.sum_range_succ']
      simp only [List.getD_cons_succ, List.getD_cons_zero]
      rw [ih l2]
      ring


theorem foldlApp_append {α β : Type*} (l1 l2 : List β) (init : List α) (f : List α → β → α) :
    foldlApp (l1 ++ l2) init f = foldlApp l2 (foldlApp l1 init f) f := by
  simp only [foldlApp, List.foldl_append]

/-- The value at index `e` of the accumulator is already fixed as soon as the accumulated list is
longer than `e` (there `s` steps suffice, and any later prefix gives the same value). -/
theorem foldlApp_getD_prefix {α β : Type*} (l : List β) (init : List α) (f : List α → β → α)
    (d : α) (s t e : ℕ) (hst : s ≤ t) (ht : t ≤ l.length) (he : e < init.length + s) :
    (foldlApp l init f).getD e d = (foldlApp (l.take t) init f).getD e d := by
  conv_lhs => rw [← List.take_append_drop t l]
  rw [foldlApp_append]
  rw [foldlApp_getD_lt _ _ _ _ (by rw [foldlApp_length, List.length_take]; omega)]

/-! ## 7. The `bmats` recursion as a `foldlApp` -/

/-- One step of `Data.bmats`: the block attached to `par`-entry `p`, given the accumulator. -/
def bvStep (D : Data.ArithData) (acc : List (List Data.M3)) (p : ℕ × ℕ) : List Data.M3 :=
  (List.range D.gens.length).map (fun g' => Data.M3.add
    (if g' = p.1 then Data.M3.one else Data.M3.zero)
    (Data.M3.mul (D.gens.getD p.1 Data.M3.one) ((acc.getD p.2 []).getD g' Data.M3.zero)))

theorem bmats_eq (D : Data.ArithData) :
    Data.bmats D = foldlApp D.par [List.replicate D.gens.length Data.M3.zero] (bvStep D) := rfl

theorem bvStep_length (D : Data.ArithData) (acc : List (List Data.M3)) (p : ℕ × ℕ) :
    (bvStep D acc p).length = D.gens.length := by
  simp [bvStep]

theorem ad_bmats_length (j : Fin 73) : (Data.bmats (RC.Ad j)).length = (RC.Ad j).n := by
  rw [bmats_eq, foldlApp_length]
  simp only [List.length_replicate, List.length_singleton]
  have := RC.Ad_par_len j; omega

theorem ad_bmats_rowlen (j : Fin 73) (i : ℕ) (hi : i < (RC.Ad j).n) :
    ((Data.bmats (RC.Ad j)).getD i []).length = RC.KK j := by
  have hlen := ad_bmats_length j
  have h := foldlApp_rowlen ((RC.Ad j).par) [List.replicate (RC.Ad j).gens.length Data.M3.zero]
      (bvStep (RC.Ad j)) (RC.Ad j).gens.length
      (by intro a ha; rw [List.mem_singleton] at ha; subst ha; simp [RC.KK])
      (by intro acc p _; exact bvStep_length (RC.Ad j) acc p)
  rw [← bmats_eq] at h
  rw [List.getD_eq_getElem _ _ (by rw [hlen]; exact hi)]
  exact h _ (List.getElem_mem _)

theorem ad_bmats_getD_zero (j : Fin 73) :
    (Data.bmats (RC.Ad j)).getD 0 [] = List.replicate (RC.KK j) Data.M3.zero := by
  rw [bmats_eq]
  rw [foldlApp_getD_lt _ _ _ _ (by simp : 0 < ([List.replicate (RC.Ad j).gens.length Data.M3.zero]).length)]
  rfl

theorem eq_range_map_getD {α : Type*} (l : List α) (d : α) :
    (List.range l.length).map (fun i => l.getD i d) = l := by
  apply List.ext_getElem
  · simp
  · intro i h1 h2
    rw [List.getElem_map, List.getElem_range (by simpa using h1)]
    exact List.getD_eq_getElem _ _ h2


/-! ## 8. `Data.ldot` against `Data.applyB` -/

theorem foldr_addV_toFun (l : List Data.V3) (c : Fin 3) :
    (l.foldr Data.V3.add Data.V3.zero).toFun c = (l.map (fun v => v.toFun c)).sum := by
  induction l with
  | nil => simp [toFun_zero]
  | cons a l ih =>
    rw [List.foldr_cons, toFun_add, Pi.add_apply, ih, List.map_cons, List.sum_cons]

theorem unblocks_cons (a : Data.V3) (u : List Data.V3) :
    Data.unblocks (a :: u) = Data.V3.toList a ++ Data.unblocks u := by
  simp [Data.unblocks]

theorem unblocks_nil : Data.unblocks ([] : List Data.V3) = [] := rfl

theorem toList_length (v : Data.V3) : v.toList.length = 3 := by cases v; rfl

theorem dot_toList (a b : Data.V3) :
    (List.zipWith (· * ·) a.toList b.toList).sum = Data.V3.dot a b := by
  cases a; cases b; simp [Data.V3.dot, Data.V3.toList]; ring

theorem ldot_unblocks : ∀ u v : List Data.V3,
    Data.ldot (Data.unblocks u) (Data.unblocks v) = (List.zipWith Data.V3.dot u v).sum
  | [], v => by simp [Data.ldot, unblocks_nil]
  | a :: u, [] => by simp [Data.ldot, unblocks_nil]
  | a :: u, b :: v => by
      rw [unblocks_cons, unblocks_cons, Data.ldot,
        List.zipWith_append (by rw [toList_length, toList_length]), List.sum_append]
      have h := ldot_unblocks u v
      simp only [Data.ldot] at h
      rw [h]
      rw [List.zipWith_cons_cons, List.sum_cons, dot_toList]

theorem dot_rows (A : Data.M3) (v : Data.V3) (r : Fin 3) :
    Data.V3.dot ((Data.M3.rows A).getD r.val Data.V3.zero) v = (Data.M3.mulV A v).toFun r := by
  fin_cases r <;> simp [Data.M3.rows, Data.V3.dot, Data.M3.mulV, Data.V3.toList, Data.V3.toFun]

/-- The `r`-th coordinate of `Data.applyB blk (Data.unblocks l)` is the dot product of the `r`-th
rows of the blocks of `blk` with `l`. -/
theorem ldot_applyB (blk : List Data.M3) (l : List Data.V3) (r : Fin 3) :
    Data.ldot (Data.unblocks (blk.map (fun A => (Data.M3.rows A).getD r.val Data.V3.zero)))
        (Data.unblocks l)
      = (Data.applyB blk (Data.unblocks l)).toFun r := by
  rw [ldot_unblocks, List.zipWith_map_left, Data.applyB, RC.blocks_unblocks,
    foldr_addV_toFun, List.map_zipWith]
  rw [show (fun A v => Data.V3.dot ((Data.M3.rows A).getD r.val Data.V3.zero) v)
      = (fun A (v : Data.V3) => (Data.M3.mulV A v).toFun r) from
    funext fun A => funext fun v => dot_rows A v r]

end Work.SG
