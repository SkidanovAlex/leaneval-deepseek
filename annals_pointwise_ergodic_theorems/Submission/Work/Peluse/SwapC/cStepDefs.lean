import Mathlib
import Submission.Work.Peluse.SwapC.cStPerm
import Submission.Work.Peluse.Holds.ExpPET.Jensen

/-!
# Plumbing for `Work.Peluse.SwapC.cStep`

Auxiliary definitions and lemmas for the one-step increment of the iteration of
`Work.Peluse.SwapC.concatAll` (KKL Proposition 6.2).  Nothing here is specific to the concatenation
step; the file collects

* `avg_equiv` : an average is unchanged by reindexing along an equivalence;
* `avg_pow_le_avg_pow` : the Jensen step `(avg F)^e ≤ avg (F^e)` for `1 ≤ e`;
* `pbox_finCongr` : `pbox` is unchanged by relabelling `Fin d ≃ Fin d'`;
* `envOf` / `envEquiv` / `avg_envOf` : the splitting of an index assignment
  `η : σ → I` into its values at two distinguished points `a`, `a1` and its restriction to the
  complement, with the evaluation lemmas used to compare the coefficients of the slots;
* the coefficient lemmas `cA_subst_a1`, `cB_subst_a1`, `cA_envOf_eq_of_ne_a1`, … that identify the
  coefficients of the two copies `CC.subst a a` / `CC.subst a a1` of a slot touching `a` with the
  two components of the "pair" variable.

The route of `cStep` (KKL Lemma 6.1 as the only analytic input) is described at the target.
-/

set_option autoImplicit false

open scoped BigOperators

namespace Work.Peluse.SwapC

noncomputable section

open Work.Peluse
open Work.Peluse.LadderP.Swap
open CC

/-! ## 0. Averaging plumbing -/

/-- **An average is unchanged by a reindexing along an equivalence.** -/
theorem avg_equiv {α β : Type} [Fintype α] [Fintype β] (e : α ≃ β) (F : α → ℝ) :
    avg (fun b : β => F (e.symm b)) = avg F := by
  rw [avg, avg, ← Fintype.card_congr e,
    Fintype.sum_equiv e.symm (fun b => F (e.symm b)) F (fun _ => rfl)]

/-- **The Jensen (power-mean) step**: for `1 ≤ e` and `F ≥ 0`, the `e`-th power of the average is at
most the average of the `e`-th powers.  Immediate from the power-mean inequality
`Work.Peluse.Holds.ExpPET.pow_mean_avg_le` applied to `y := F^e`. -/
theorem avg_pow_le_avg_pow {ι : Type} [Fintype ι] [Nonempty ι] (F : ι → ℝ)
    (hF : ∀ i, 0 ≤ F i) {e : ℕ} (he : 1 ≤ e) : (avg F) ^ e ≤ avg (fun i => F i ^ e) := by
  have he' : (1 : ℝ) ≤ (e : ℝ) := by exact_mod_cast he
  have hne : (e : ℝ) ≠ 0 := by
    have : (0:ℝ) < e := by exact_mod_cast lt_of_lt_of_le Nat.zero_lt_one he
    exact ne_of_gt this
  have hpow : ∀ i : ι, (F i ^ e : ℝ) ^ (1 / (e : ℝ)) = F i := by
    intro i
    rw [← Real.rpow_natCast (F i) e, ← Real.rpow_mul (hF i) (e : ℝ) (1 / (e : ℝ)),
      mul_one_div_cancel hne, Real.rpow_one]
  have hmain := Work.Peluse.Holds.ExpPET.pow_mean_avg_le (Finset.univ : Finset ι)
    Finset.univ_nonempty he' (fun i => F i ^ e) (fun i _ => pow_nonneg (hF i) e)
  rw [Finset.sum_congr rfl (fun i _ => hpow i)] at hmain
  have h1 : avg F = ((Finset.univ : Finset ι).card : ℝ)⁻¹ * ∑ i ∈ Finset.univ, F i := by
    rw [avg, Finset.card_univ]
  have h2 : avg (fun i => F i ^ e) = ((Finset.univ : Finset ι).card : ℝ)⁻¹ *
      ∑ i ∈ Finset.univ, F i ^ e := by
    rw [avg, Finset.card_univ]
  rw [h1, h2]
  simpa using hmain

/-- **The Jensen step in the form used by `cStep`**: from `0 ≤ F`, `1 ≤ e` and `δ ≤ avg F`, the
`e`-th power of `δ` is at most the average of the `e`-th powers. -/
theorem pow_le_avg_pow_of_avg {ι : Type} [Fintype ι] [Nonempty ι] {F : ι → ℝ}
    (hF : ∀ i, 0 ≤ F i) {e : ℕ} (he : 1 ≤ e) {δ : ℝ} (hδ : 0 ≤ δ) (h : δ ≤ avg F) :
    δ ^ e ≤ avg (fun i => F i ^ e) := by
  have h1 : δ ^ e ≤ (avg F) ^ e := pow_le_pow_left₀ hδ h e
  exact le_trans h1 (avg_pow_le_avg_pow F hF he)

/-- **Relabelling the slot index of `pbox`.**  `pbox d Q₁ Q₂` only sees the index type `Fin d`
through the coefficient families, so an equality `d = d'` may be transported along `finCongr`. -/
theorem pbox_finCongr {d d' : ℕ} (h : d = d') (Q₁ Q₂ : Fin d → ℤ) (M : ℕ) (S : Finset ℤ)
    (F : ℤ → ℂ) :
    pbox d Q₁ Q₂ M S F
      = pbox d' (fun k => Q₁ (Fin.cast h.symm k)) (fun k => Q₂ (Fin.cast h.symm k)) M S F := by
  have he : ∀ k : Fin d', (finCongr h).symm k = Fin.cast h.symm k := by
    intro k
    exact Fin.ext (by simp [finCongr_apply])
  rw [pbox_compEquiv (finCongr h) Q₁ Q₂ M S F]
  simp only [he]

/-! ## 1. The environment split at two points -/

/-- The index assignment obtained by prescribing the values at the two points `a`, `a1` and taking
the remaining values from `rest`. -/
def envOf {σ I : Type} [DecidableEq σ] (a a1 : σ) (rest : {x : σ // x ≠ a ∧ x ≠ a1} → I)
    (i₀ i₁ : I) : σ → I :=
  fun x => if h : x = a then i₀ else if h' : x = a1 then i₁ else rest ⟨x, h, h'⟩

@[simp] lemma envOf_same {σ I : Type} [DecidableEq σ] {a a1 : σ}
    {rest : {x : σ // x ≠ a ∧ x ≠ a1} → I} {i₀ i₁ : I} : envOf a a1 rest i₀ i₁ a = i₀ := by
  simp [envOf]

lemma envOf_second {σ I : Type} [DecidableEq σ] {a a1 : σ} (h : a1 ≠ a)
    {rest : {x : σ // x ≠ a ∧ x ≠ a1} → I} {i₀ i₁ : I} : envOf a a1 rest i₀ i₁ a1 = i₁ := by
  simp [envOf, h]

lemma envOf_other {σ I : Type} [DecidableEq σ] {a a1 x : σ} (hx : x ≠ a) (hx1 : x ≠ a1)
    {rest : {x : σ // x ≠ a ∧ x ≠ a1} → I} {i₀ i₁ : I} :
    envOf a a1 rest i₀ i₁ x = rest ⟨x, hx, hx1⟩ := by
  simp [envOf, hx, hx1]

/-- **The comparison of the two environments used for the two copies of a slot**: evaluating the
*renamed* point `a ↦ a1` in the environment `i₀, i₁` is evaluating the original point in the
environment `i₁, i₁`. -/
lemma envOf_rename {σ I : Type} [DecidableEq σ] {a a1 : σ} (h : a1 ≠ a)
    (rest : {x : σ // x ≠ a ∧ x ≠ a1} → I) (i₀ i₁ : I) (x : σ) :
    envOf a a1 rest i₀ i₁ (if x = a then a1 else x) = envOf a a1 rest i₁ i₁ x := by
  by_cases hx : x = a
  · subst hx; simp [envOf, h]
  · rw [if_neg hx]
    by_cases hx1 : x = a1
    · subst hx1; simp [envOf, h]
    · simp [envOf, hx, hx1]

lemma envOf_congr_a1 {σ I : Type} [DecidableEq σ] {a a1 x : σ} (hx : x ≠ a1)
    (rest : {x : σ // x ≠ a ∧ x ≠ a1} → I) (i₀ i₁ i₁' : I) :
    envOf a a1 rest i₀ i₁ x = envOf a a1 rest i₀ i₁' x := by
  by_cases hxa : x = a
  · subst hxa; simp [envOf]
  · rw [envOf_other hxa hx, envOf_other hxa hx]

lemma envOf_congr_a {σ I : Type} [DecidableEq σ] {a a1 x : σ} (hx : x ≠ a)
    (rest : {x : σ // x ≠ a ∧ x ≠ a1} → I) (i₀ i₀' i₁ : I) :
    envOf a a1 rest i₀ i₁ x = envOf a a1 rest i₀' i₁ x := by
  by_cases hx1 : x = a1
  · subst hx1; rw [envOf_second hx, envOf_second hx]
  · rw [envOf_other hx hx1, envOf_other hx hx1]

lemma envOf_congr_both {σ I : Type} [DecidableEq σ] {a a1 x : σ} (hx : x ≠ a) (hx1 : x ≠ a1)
    (rest : {x : σ // x ≠ a ∧ x ≠ a1} → I) (i₀ i₀' i₁ i₁' : I) :
    envOf a a1 rest i₀ i₁ x = envOf a a1 rest i₀' i₁' x := by
  rw [envOf_other hx hx1, envOf_other hx hx1]

/-- **The split of an index assignment into its values at two distinct points and its restriction
to the complement.** -/
def envEquiv {σ I : Type} [DecidableEq σ] (a a1 : σ) (h : a1 ≠ a) :
    (σ → I) ≃ ({x : σ // x ≠ a ∧ x ≠ a1} → I) × (I × I) where
  toFun η := (fun x => η x.1, (η a, η a1))
  invFun z := envOf a a1 z.1 z.2.1 z.2.2
  left_inv η := by
    funext x
    by_cases hx : x = a
    · subst hx; simp [envOf]
    · by_cases hx1 : x = a1
      · subst hx1; simp [envOf, h]
      · simp [envOf, hx, hx1]
  right_inv z := by
    refine Prod.ext ?_ ?_
    · funext x; simp [envOf, x.2.1, x.2.2]
    · simp only [envOf_same, envOf_second h]

/-- **The average over an index assignment is the iterated average over its two prescribed values
and its restriction to the complement.** -/
theorem avg_envOf {σ I : Type} [Fintype σ] [DecidableEq σ] [Fintype I] {a a1 : σ} (h : a1 ≠ a)
    (Φ : (σ → I) → ℝ) :
    avg Φ = avg (fun z : ({x : σ // x ≠ a ∧ x ≠ a1} → I) × (I × I) =>
      Φ (envOf a a1 z.1 z.2.1 z.2.2)) := by
  rw [← avg_equiv (envEquiv a a1 h) Φ]
  rfl

/-! ## 2. Coefficients of a slot -/

/-- The first coefficient of a raw slot. -/
@[simp] lemma cA_raw {I : Type} {s : ℕ} (q : I → Fin s → ℤ) (η : (Fin s → Bool) → I)
    {j : Fin s} {b : Fin s → Bool} : cA q η (CC.raw j b) = q (η b) j := rfl

/-- The first coefficient of a difference slot. -/
@[simp] lemma cA_dff {I : Type} {s : ℕ} (q : I → Fin s → ℤ) (η : (Fin s → Bool) → I)
    {j : Fin s} {b c : Fin s → Bool} : cA q η (CC.dff j b c) = q (η b) j := rfl

/-- The second coefficient of a raw slot vanishes. -/
@[simp] lemma cB_raw {I : Type} {s : ℕ} (q : I → Fin s → ℤ) (η : (Fin s → Bool) → I)
    {j : Fin s} {b : Fin s → Bool} : cB q η (CC.raw j b) = 0 := rfl

/-- The second coefficient of a difference slot. -/
@[simp] lemma cB_dff {I : Type} {s : ℕ} (q : I → Fin s → ℤ) (η : (Fin s → Bool) → I)
    {j : Fin s} {b c : Fin s → Bool} : cB q η (CC.dff j b c) = q (η c) j := rfl

/-- `CC.subst a a` is the identity. -/
@[simp] lemma CC.subst_self {s : ℕ} (a : Fin s → Bool) (sl : CC s) : CC.subst a a sl = sl := by
  cases sl with
  | raw j b =>
      show CC.raw j (if b = a then a else b) = CC.raw j b
      by_cases hb : b = a
      · rw [if_pos hb, hb]
      · rw [if_neg hb]
  | dff j b c =>
      show CC.dff j (if b = a then a else b) (if c = a then a else c) = CC.dff j b c
      by_cases hb : b = a
      · by_cases hc : c = a
        · rw [if_pos hb, if_pos hc, hb, hc]
        · rw [if_pos hb, if_neg hc, hb]
      · by_cases hc : c = a
        · rw [if_neg hb, if_pos hc, hc]
        · rw [if_neg hb, if_neg hc]

/-- **The coefficients of the second copy.**  Evaluating the slot with `a` renamed to `a1` in the
environment `(i₀, i₁)` is the same as evaluating the original slot in the environment `(i₁, i₁)`. -/
lemma cA_subst_a1 {I : Type} {s : ℕ} (q : I → Fin s → ℤ) {a a1 : Fin s → Bool} {h : a1 ≠ a}
    {rest : {x : Fin s → Bool // x ≠ a ∧ x ≠ a1} → I} {i₀ i₁ : I} (sl : CC s) :
    cA q (envOf a a1 rest i₀ i₁) (CC.subst a a1 sl) = cA q (envOf a a1 rest i₁ i₁) sl := by
  cases sl with
  | raw j b =>
      show q ((envOf a a1 rest i₀ i₁) (if b = a then a1 else b)) j
        = q ((envOf a a1 rest i₁ i₁) b) j
      rw [envOf_rename h]
  | dff j b c =>
      show q ((envOf a a1 rest i₀ i₁) (if b = a then a1 else b)) j
        = q ((envOf a a1 rest i₁ i₁) b) j
      rw [envOf_rename h]

/-- **The coefficients of the second copy** (`cB`-form of `cA_subst_a1`). -/
lemma cB_subst_a1 {I : Type} {s : ℕ} (q : I → Fin s → ℤ) {a a1 : Fin s → Bool} {h : a1 ≠ a}
    {rest : {x : Fin s → Bool // x ≠ a ∧ x ≠ a1} → I} {i₀ i₁ : I} (sl : CC s) :
    cB q (envOf a a1 rest i₀ i₁) (CC.subst a a1 sl) = cB q (envOf a a1 rest i₁ i₁) sl := by
  cases sl with
  | raw j b => simp [CC.subst]
  | dff j b c =>
      show q ((envOf a a1 rest i₀ i₁) (if c = a then a1 else c)) j
        = q ((envOf a a1 rest i₁ i₁) c) j
      rw [envOf_rename h]

/-- A slot avoiding the point `x`. -/
def avoids {s : ℕ} (x : Fin s → Bool) : CC s → Prop
  | .raw _ b => b ≠ x
  | .dff _ b c => b ≠ x ∧ c ≠ x

lemma avoids_iff_touchesb {s : ℕ} (x : Fin s → Bool) (sl : CC s) :
    avoids x sl ↔ CC.touchesb x sl = false := by
  cases sl with
  | raw j b =>
      show (b ≠ x) ↔ (decide (b = x) = false)
      rw [decide_eq_false_iff_not]
  | dff j b c =>
      show (b ≠ x ∧ c ≠ x) ↔ ((decide (b = x) || decide (c = x)) = false)
      rw [Bool.or_eq_false_iff, decide_eq_false_iff_not, decide_eq_false_iff_not]

/-- The first coefficient is unchanged when only the value at `a1` varies, provided the slot avoids
`a1`. -/
lemma cA_envOf_congr_a1 {I : Type} {s : ℕ} (q : I → Fin s → ℤ) {a a1 : Fin s → Bool}
    {rest : {x : Fin s → Bool // x ≠ a ∧ x ≠ a1} → I} {i₀ i₁ i₁' : I} (sl : CC s)
    (h : avoids a1 sl) :
    cA q (envOf a a1 rest i₀ i₁) sl = cA q (envOf a a1 rest i₀ i₁') sl := by
  cases sl with
  | raw j b =>
      show q ((envOf a a1 rest i₀ i₁) b) j = q ((envOf a a1 rest i₀ i₁') b) j
      rw [envOf_congr_a1 h rest i₀ i₁ i₁']
  | dff j b c =>
      show q ((envOf a a1 rest i₀ i₁) b) j = q ((envOf a a1 rest i₀ i₁') b) j
      rw [envOf_congr_a1 h.1 rest i₀ i₁ i₁']

lemma cB_envOf_congr_a1 {I : Type} {s : ℕ} (q : I → Fin s → ℤ) {a a1 : Fin s → Bool}
    {rest : {x : Fin s → Bool // x ≠ a ∧ x ≠ a1} → I} {i₀ i₁ i₁' : I} (sl : CC s)
    (h : avoids a1 sl) :
    cB q (envOf a a1 rest i₀ i₁) sl = cB q (envOf a a1 rest i₀ i₁') sl := by
  cases sl with
  | raw j b => simp
  | dff j b c =>
      show q ((envOf a a1 rest i₀ i₁) c) j = q ((envOf a a1 rest i₀ i₁') c) j
      rw [envOf_congr_a1 h.2 rest i₀ i₁ i₁']

/-- The coefficients are unchanged when only the values at `a`, `a1` vary, provided the slot avoids
both. -/
lemma cA_envOf_congr_both {I : Type} {s : ℕ} (q : I → Fin s → ℤ) {a a1 : Fin s → Bool}
    {rest : {x : Fin s → Bool // x ≠ a ∧ x ≠ a1} → I} {i₀ i₀' i₁ i₁' : I} (sl : CC s)
    (h : avoids a sl) (h1 : avoids a1 sl) :
    cA q (envOf a a1 rest i₀ i₁) sl = cA q (envOf a a1 rest i₀' i₁') sl := by
  cases sl with
  | raw j b =>
      show q ((envOf a a1 rest i₀ i₁) b) j = q ((envOf a a1 rest i₀' i₁') b) j
      rw [envOf_congr_both h h1 rest i₀ i₀' i₁ i₁']
  | dff j b c =>
      show q ((envOf a a1 rest i₀ i₁) b) j = q ((envOf a a1 rest i₀' i₁') b) j
      rw [envOf_congr_both h.1 h1.1 rest i₀ i₀' i₁ i₁']

lemma cB_envOf_congr_both {I : Type} {s : ℕ} (q : I → Fin s → ℤ) {a a1 : Fin s → Bool}
    {rest : {x : Fin s → Bool // x ≠ a ∧ x ≠ a1} → I} {i₀ i₀' i₁ i₁' : I} (sl : CC s)
    (h : avoids a sl) (h1 : avoids a1 sl) :
    cB q (envOf a a1 rest i₀ i₁) sl = cB q (envOf a a1 rest i₀' i₁') sl := by
  cases sl with
  | raw j b => simp
  | dff j b c =>
      show q ((envOf a a1 rest i₀ i₁) c) j = q ((envOf a a1 rest i₀' i₁') c) j
      rw [envOf_congr_both h.2 h1.2 rest i₀ i₀' i₁ i₁']

/-! ## 3. Elementary real/list plumbing -/

/-- The average is linear in the constant factor. -/
theorem avg_const_mul {ι : Type} [Fintype ι] (c : ℝ) (F : ι → ℝ) :
    avg (fun i => c * F i) = c * avg F := by
  have h1 : avg (fun i => c * F i) = ((Fintype.card ι : ℝ))⁻¹ * c * ∑ i, F i := by
    rw [avg, ← Finset.mul_sum]; ring
  have h2 : c * avg F = ((Fintype.card ι : ℝ))⁻¹ * c * ∑ i, F i := by
    rw [avg]; ring
  rw [h1, h2]

/-- An average over a product is unchanged by dropping a variable the function does not use. -/
theorem avg_prod_drop {A B C : Type} [Fintype A] [Nonempty A] [Fintype B] [Nonempty B]
    [Fintype C] [Nonempty C] (F : A → B → ℝ) :
    avg (fun z : A × (B × C) => F z.1 z.2.1) = avg (fun z : A × B => F z.1 z.2) := by
  rw [avg_prod (F := fun z : A × (B × C) => F z.1 z.2.1),
    avg_prod (F := fun z : A × B => F z.1 z.2)]
  congr 1
  funext a
  rw [avg_prod (F := fun bc : B × C => F a bc.1)]
  congr 1
  funext b
  exact avg_const (F a b)

/-- `get` on a concatenation, first block. -/
lemma get_append_left' {α : Type*} {L₁ L₂ : List α} (j : Fin L₁.length) :
    (L₁ ++ L₂).get ⟨j.val, by simp only [List.length_append]; omega⟩ = L₁.get j := by
  rw [List.get_eq_getElem, List.get_eq_getElem]
  simp

/-- `get` on a concatenation, second block. -/
lemma get_append_right' {α : Type*} {L₁ L₂ : List α} (j : Fin L₂.length) :
    (L₁ ++ L₂).get ⟨L₁.length + j.val, by simp only [List.length_append]; omega⟩ = L₂.get j := by
  rw [List.get_eq_getElem, List.get_eq_getElem]
  rw [List.getElem_append_right (Nat.le_add_right L₁.length j.val),
    getElem_congr_idx (show L₁.length + j.val - L₁.length = j.val by omega)]

/-- `get` on a three-block concatenation `L₁ ++ L₂ ++ [x]`, first block. -/
lemma get_append3_left {α : Type*} {L₁ L₂ : List α} {x : α} (j : Fin L₁.length) :
    (L₁ ++ L₂ ++ [x]).get
        ⟨j.val, by simp only [List.length_append, List.length_singleton]; omega⟩ = L₁.get j := by
  rw [List.get_eq_getElem, List.get_eq_getElem]
  rw [List.getElem_append_left (by simp only [List.length_append]; omega)]
  simp

/-- `get` on a three-block concatenation `L₁ ++ L₂ ++ [x]`, middle block. -/
lemma get_append3_mid {α : Type*} {L₁ L₂ : List α} {x : α} (j : Fin L₂.length) :
    (L₁ ++ L₂ ++ [x]).get
        ⟨L₁.length + j.val, by simp only [List.length_append, List.length_singleton]; omega⟩
      = L₂.get j := by
  rw [List.get_eq_getElem, List.get_eq_getElem]
  rw [List.getElem_append_left (by simp only [List.length_append]; omega)]
  rw [List.getElem_append_right (Nat.le_add_right L₁.length j.val),
    getElem_congr_idx (show L₁.length + j.val - L₁.length = j.val by omega)]

/-- `get` on a three-block concatenation `L₁ ++ L₂ ++ [x]`, last block. -/
lemma get_append3_last {α : Type*} {L₁ L₂ : List α} {x : α} :
    (L₁ ++ L₂ ++ [x]).get
        ⟨L₁.length + L₂.length, by simp only [List.length_append, List.length_singleton]; omega⟩
      = x := by
  rw [List.get_eq_getElem]
  rw [List.getElem_append_right (bs := [x]) (i := L₁.length + L₂.length)
    (by simp only [List.length_append]; omega)]
  rw [getElem_congr_idx (show L₁.length + L₂.length - (L₁ ++ L₂).length = 0 by
    rw [List.length_append]; omega)]
  simp

/-- `getElem`-form of `get_append3_left`. -/
lemma getElem_append3_left' {α : Type*} (L₁ L₂ : List α) (x : α) (i : ℕ) (h : i < L₁.length) :
    (L₁ ++ L₂ ++ [x])[i]'(by simp only [List.length_append, List.length_singleton]; omega)
      = L₁[i]'h :=
  get_append3_left (L₁ := L₁) (L₂ := L₂) (x := x) ⟨i, h⟩

/-- `getElem`-form of `get_append3_mid`. -/
lemma getElem_append3_mid' {α : Type*} (L₁ L₂ : List α) (x : α) (i : ℕ) (h : i < L₂.length) :
    (L₁ ++ L₂ ++ [x])[L₁.length + i]'
        (by simp only [List.length_append, List.length_singleton]; omega) = L₂[i]'h :=
  get_append3_mid (L₁ := L₁) (L₂ := L₂) (x := x) ⟨i, h⟩

/-- `getElem`-form of `get_append3_last`. -/
lemma getElem_append3_last' {α : Type*} (L₁ L₂ : List α) (x : α) :
    (L₁ ++ L₂ ++ [x])[L₁.length + L₂.length]'
        (by simp only [List.length_append, List.length_singleton]; omega) = x :=
  get_append3_last (L₁ := L₁) (L₂ := L₂) (x := x)

/-- Averaging over `A × B` and then over `C` is the same as averaging over `A × C` and then `B`. -/
theorem avg_swap {A B C : Type} [Fintype A] [Nonempty A] [Fintype B] [Nonempty B]
    [Fintype C] [Nonempty C] (F : A → B → C → ℝ) :
    avg (fun z : A × B => avg (fun c : C => F z.1 z.2 c)) =
      avg (fun z : A × C => avg (fun b : B => F z.1 b z.2)) := by
  rw [avg_prod (F := fun z : A × B => avg (fun c : C => F z.1 z.2 c)),
    avg_prod (F := fun z : A × C => avg (fun b : B => F z.1 b z.2))]
  congr 1
  funext a
  rw [← avg_prod (F := fun z : B × C => F a z.1 z.2),
    ← avg_prod (F := fun z : C × B => F a z.2 z.1)]
  have hcard : (Fintype.card (B × C) : ℝ) = Fintype.card (C × B) := by
    rw [Fintype.card_prod, Fintype.card_prod, Nat.mul_comm]
  rw [avg, avg, hcard]
  congr 1
  rw [Fintype.sum_prod_type, Fintype.sum_prod_type, Finset.sum_comm]


end

end Work.Peluse.SwapC
