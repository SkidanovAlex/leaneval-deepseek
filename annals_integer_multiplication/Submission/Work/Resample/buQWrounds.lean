import Mathlib
import Submission.Work.Resample.buQWdefs
import Submission.Work.Resample.buQWhs
import Submission.Work.Resample.buQWRdefs
import Submission.Work.Resample.auKit
import Submission.Work.Kernel.Raw
import Submission.Work.Resample.buQWround1

set_option autoImplicit false
set_option maxHeartbeats 4000000

namespace Work.Resample

open HvdH

/-!
# `Work.Resample.buQWrounds`

The word of `Work.Resample.buQWrounds` runs the Neumann round (`Work.Resample.buQWstep`)
`egN p α s t - 1` times, starting from the pair `(v, v)`, and outputs the second component of the
folded state (`Work.Resample.buJsumL`).  This file assembles it from

* the single-round word (the statement `Work.Resample.buQWround1`, proved in this workspace),
* the radius bookkeeping of the rounds (`Work.Resample.buQWB`, `Work.Resample.buQWB2`), and
* a cleanup word deleting the values that are no longer needed.

The loop over the `egN p α s t - 1` signs is `KernelLib.foldList` applied to the sign list
`buSignsT p α s t = zl (buSignsL (egN p α s t))`; the round word is the body of that fold, with
accumulator `[cvecVal v, cvecVal acc, buColsT, int s, int p] ++ rest`.
-/

/-! ## 1.  Preliminary list and size facts -/

/-- the `(i+1)`-st prefix of a list is the `i`-th prefix followed by the `i`-th entry -/
theorem bu_take_succ {α : Type} [Inhabited α] (l : List α) (i : ℕ) (hi : i < l.length) :
    l.take (i + 1) = l.take i ++ [l.getD i default] := by
  induction l generalizing i with
  | nil => simp at hi
  | cons a t ih =>
    cases i with
    | zero => rfl
    | succ j =>
      have hj : j < t.length := by simpa using hi
      show a :: t.take (j + 1) = a :: (t.take j ++ [t.getD j default])
      rw [ih j hj]

/-- total size of a list of values -/
theorem bu_vsz_ofList (l : List Val) : vsz (ofList l) = l.length + 1 + (l.map vsz).sum := by
  induction l with
  | nil => rfl
  | cons a t ih =>
    have h : ofList (a :: t) = Val.cons a (ofList t) := rfl
    rw [h, Work.Fx.vsz_cons, ih, List.length_cons, List.map_cons, List.sum_cons]
    ring

/-- size of a list of integers, as a value -/
theorem bu_vsz_zl (l : List ℤ) : vsz (zl l) = l.length + 1 + (l.map isz).sum := by
  unfold zl
  rw [bu_vsz_ofList, List.length_map]
  have h1 : ((l.map Val.int).map vsz) = l.map isz := by
    rw [List.map_map]
    exact List.map_congr_left (fun z _ => Work.Fx.vsz_int z)
  rw [h1]

/-- a sum of naturals bounded termwise -/
theorem bu_sum_le_length_mul {l : List ℕ} {M : ℕ} (h : ∀ x ∈ l, x ≤ M) :
    l.sum ≤ l.length * M := by
  induction l with
  | nil => simp
  | cons a t ih =>
    have ha : a ≤ M := h a (by simp)
    have ht : ∀ x ∈ t, x ≤ M := fun x hx => h x (by simp [hx])
    have := ih ht
    rw [List.sum_cons, List.length_cons]
    nlinarith

/-- size of a vector of complex fixed-point numbers -/
theorem bu_vsz_cvecVal {u : List (ℤ × ℤ)} {M : ℕ}
    (h : ∀ z ∈ u, isz z.1 ≤ M ∧ isz z.2 ≤ M) :
    vsz (cvecVal u) ≤ 3 * u.length * (M + 1) + 1 := by
  have hsum : ∀ l : List (ℤ × ℤ), (∀ z ∈ l, isz z.1 ≤ M ∧ isz z.2 ≤ M) →
      (l.map (fun z => isz z.1 + isz z.2 + 1)).sum ≤ l.length * (2 * M + 1) := by
    intro l hl
    induction l with
    | nil => simp
    | cons a t ih =>
      have ha := hl a (by simp)
      have ht : ∀ z ∈ t, isz z.1 ≤ M ∧ isz z.2 ≤ M := fun z hz => hl z (by simp [hz])
      have h1 : isz a.1 + isz a.2 + 1 ≤ 2 * M + 1 := by omega
      simp only [List.map_cons, List.sum_cons, List.length_cons]
      nlinarith [ih ht]
  unfold cvecVal
  rw [bu_vsz_ofList, List.length_map]
  have hmap : ((u.map cfxVal).map vsz) = u.map (fun z => isz z.1 + isz z.2 + 1) := by
    rw [List.map_map]
    exact List.map_congr_left (fun z _ => Work.Fx.vsz_cfxVal z)
  rw [hmap]
  have := hsum u h
  nlinarith [Nat.zero_le u.length, Nat.zero_le M]

/-- injectivity of the encodings of the work vectors -/
theorem bu_ofList_inj : Function.Injective (ofList : List Val → Val) := by
  intro l
  induction l with
  | nil =>
    intro m h
    cases m with
    | nil => rfl
    | cons y ys => exact absurd h (by simp [ofList])
  | cons x xs ih =>
    intro m h
    cases m with
    | nil => exact absurd h.symm (by simp [ofList])
    | cons y ys =>
      have h' : Val.cons x (ofList xs) = Val.cons y (ofList ys) := h
      obtain ⟨h1, h2⟩ := Val.cons.inj h'
      rw [h1, ih h2]

theorem bu_cfxVal_inj {a b : ℤ × ℤ} (h : cfxVal a = cfxVal b) : a = b := by
  have h1 := Val.cons.inj h
  exact Prod.ext (Val.int.inj h1.1) (Val.int.inj h1.2)

theorem bu_map_cfxVal_inj : Function.Injective (fun u : List (ℤ × ℤ) => u.map cfxVal) := by
  intro a
  induction a with
  | nil =>
    intro b h
    cases b with
    | nil => rfl
    | cons y ys => simp at h
  | cons x xs ih =>
    intro b h
    cases b with
    | nil => simp at h
    | cons y ys =>
      simp only [List.map_cons, List.cons.injEq] at h
      obtain ⟨h1, h2⟩ := h
      rw [bu_cfxVal_inj h1, ih h2]

theorem bu_cvecVal_inj {a b : List (ℤ × ℤ)} (h : cvecVal a = cvecVal b) : a = b := by
  unfold cvecVal at h
  exact bu_map_cfxVal_inj (bu_ofList_inj h)

/-- `buInV` is monotone in the radius -/
theorem buInV_mono {B B' : ℕ} (h : B ≤ B') {v : List (ℤ × ℤ)} (hv : buInV B v) : buInV B' v :=
  fun z hz => buIn_mono h (hv z hz)

/-! ## 2.  Folding the Neumann rounds -/

/-- one Neumann round, as a map on the pair `(v, acc)`. -/
def buStepL (Wt : ℤ → ℤ → ℤ) (p s m : ℕ) (st : List (ℤ × ℤ) × List (ℤ × ℤ)) (σ : ℤ) :
    List (ℤ × ℤ) × List (ℤ × ℤ) :=
  let v' := buRoundL Wt p s m st.1
  (v', buAddV st.2 (buSMulV σ v'))

/-- the folded state of the Neumann rounds, starting from the pair `(v0, v0)`. -/
def buFoldL (Wt : ℤ → ℤ → ℤ) (p s m : ℕ) (v0 : List (ℤ × ℤ)) (l : List ℤ) :
    List (ℤ × ℤ) × List (ℤ × ℤ) :=
  List.foldl (buStepL Wt p s m) (v0, v0) l

theorem buFoldL_append (Wt : ℤ → ℤ → ℤ) (p s m : ℕ) (v0 : List (ℤ × ℤ)) (l l' : List ℤ) :
    buFoldL Wt p s m v0 (l ++ l') =
      List.foldl (buStepL Wt p s m) (buFoldL Wt p s m v0 l) l' := by
  simp only [buFoldL, List.foldl_append]

theorem buFoldL_take_succ (Wt : ℤ → ℤ → ℤ) (p s m : ℕ) (v0 : List (ℤ × ℤ)) (l : List ℤ)
    (i : ℕ) (hi : i < l.length) :
    buFoldL Wt p s m v0 (l.take (i + 1)) =
      buStepL Wt p s m (buFoldL Wt p s m v0 (l.take i)) (l.getD i 0) := by
  rw [bu_take_succ l i hi, buFoldL_append]
  rfl

theorem buJsumL_eq (Wt : ℤ → ℤ → ℤ) (p s m n : ℕ) (v0 : List (ℤ × ℤ)) :
    buJsumL Wt p s m n v0 = (buFoldL Wt p s m v0 (buSignsL n)).2 := by
  unfold buJsumL buFoldL buStepL
  rfl

/-! ## 3.  The sign list -/

theorem buSignsL_length (n : ℕ) : (buSignsL n).length = n - 1 := by
  simp [buSignsL]

theorem buSignsL_getD (n i : ℕ) (hi : i < (buSignsL n).length) :
    (buSignsL n).getD i 0 = (-1 : ℤ) ^ (i + 1) := by
  rw [List.getD_eq_getElem _ _ hi]
  simp only [buSignsL, List.getElem_map, List.getElem_range]

theorem buSignsL_pm (n i : ℕ) (hi : i < (buSignsL n).length) :
    (buSignsL n).getD i 0 = 1 ∨ (buSignsL n).getD i 0 = -1 := by
  rw [buSignsL_getD n i hi]
  rcases Nat.even_or_odd (i + 1) with h | h
  · exact Or.inl (Even.neg_one_pow h)
  · exact Or.inr (Odd.neg_one_pow h)

theorem buSignsL_natAbs_le (n i : ℕ) (hi : i < (buSignsL n).length) :
    ((buSignsL n).getD i 0).natAbs ≤ 1 := by
  rcases buSignsL_pm n i hi with h | h <;> rw [h] <;> norm_num

/-! ## 4.  Arithmetic bounds -/

/-- `2p + 8 ≤ 2^(p-1)` for `p ≥ 100`. -/
theorem bu_two_p_add_le (k : ℕ) : 2 * (100 + k) + 8 ≤ 2 ^ (99 + k) := by
  induction k with
  | zero => norm_num
  | succ k ih =>
    have h2 : 2 ^ (99 + (k + 1)) = 2 * 2 ^ (99 + k) := by
      rw [show 99 + (k + 1) = 99 + k + 1 by ring, pow_succ]; ring
    rw [h2]
    have : 2 * (100 + (k + 1)) + 8 ≤ 2 * (2 * (100 + k) + 8) := by ring_nf; omega
    linarith

theorem bu_two_p_add_eight_le (p : ℕ) (hp : 100 ≤ p) : 2 * p + 8 ≤ 2 ^ (p - 1) := by
  obtain ⟨k, rfl⟩ : ∃ k, p = 100 + k := ⟨p - 100, by omega⟩
  have h := bu_two_p_add_le k
  rwa [show 99 + k = 100 + k - 1 by omega] at h

/-- `68 p² + 300 p + 300 ≤ 2^p` for `p ≥ 100`. -/
theorem bu_quad_le (k : ℕ) :
    68 * (100 + k) * (100 + k) + 300 * (100 + k) + 300 ≤ 2 ^ (100 + k) := by
  induction k with
  | zero => norm_num
  | succ k ih =>
    have h2 : 2 ^ (100 + (k + 1)) = 2 * 2 ^ (100 + k) := by
      rw [show 100 + (k + 1) = 100 + k + 1 by ring, pow_succ]; ring
    rw [h2]
    have h3 : 68 * (100 + (k + 1)) * (100 + (k + 1)) + 300 * (100 + (k + 1)) + 300 ≤
        2 * (68 * (100 + k) * (100 + k) + 300 * (100 + k) + 300) := by
      nlinarith
    linarith

theorem bu_quad_le' (p : ℕ) (hp : 100 ≤ p) : 68 * p * p + 300 * p + 300 ≤ 2 ^ p := by
  obtain ⟨k, rfl⟩ : ∃ k, p = 100 + k := ⟨p - 100, by omega⟩
  exact bu_quad_le k

/-- `egM p α ≤ p + 1` -/
theorem bu_egM_le (p α : ℕ) : egM p α ≤ p + 1 := by
  have h1 : Nat.sqrt p / (2 * α) ≤ Nat.sqrt p := Nat.div_le_self _ _
  have h2 : Nat.sqrt p ≤ p := Nat.sqrt_le_self p
  simp only [egM]
  omega

/-- `8 · egM p α ≤ 2^(p-1)` for `p ≥ 100`. -/
theorem bu_eight_egM_le (p α : ℕ) (hp : 100 ≤ p) : 8 * egM p α ≤ 2 ^ (p - 1) := by
  have h1 : egM p α ≤ Nat.sqrt p + 1 := by
    have h : Nat.sqrt p / (2 * α) ≤ Nat.sqrt p := Nat.div_le_self _ _
    simp only [egM]
    omega
  have h2 : Nat.sqrt p ≤ p := Nat.sqrt_le_self p
  have h3 := bu_two_p_add_eight_le p hp
  have hsq : Nat.sqrt p * Nat.sqrt p ≤ p := by
    have := Nat.sqrt_le' p
    rwa [Nat.pow_two] at this
  have hs4 : 4 ≤ Nat.sqrt p := Nat.le_sqrt.mpr (by omega)
  have h4 : 8 * Nat.sqrt p ≤ 2 * p := by nlinarith
  nlinarith [Nat.zero_le (egM p α), Nat.zero_le (Nat.sqrt p)]

/-- the number of Neumann rounds is at most `p + 1` -/
theorem bu_egN_le (p α s t : ℕ) (hs : 2 ≤ s) (hst : s < t) (hα : 2 ≤ α) (hp : 100 ≤ p)
    (hαp : α ^ 2 < p) (hθ : (p : ℝ) / (α : ℝ) ^ 4 ≤ (t : ℝ) / s - 1) :
    egN p α s t ≤ p + 1 := by
  have hsub : (t : ℝ) / (s : ℝ) - 1 = ((t - s : ℕ) : ℝ) / (s : ℝ) := by
    have h2 : ((t - s : ℕ) : ℝ) = (t : ℝ) - (s : ℝ) := by
      rw [Nat.cast_sub (le_of_lt hst)]
    rw [h2]
    have hsR : (s : ℝ) ≠ 0 := by
      have : (0 : ℝ) < (s : ℝ) := by exact_mod_cast (by omega : 0 < s)
      exact ne_of_gt this
    field_simp
  rw [hsub] at hθ
  have h1 : (p : ℝ) * (s : ℝ) ≤ (α : ℝ) ^ 4 * ((t - s : ℕ) : ℝ) := by
    have h2 : (p : ℝ) / (α : ℝ) ^ 4 * ((α : ℝ) ^ 4 * (s : ℝ)) ≤
        ((t - s : ℕ) : ℝ) / (s : ℝ) * ((α : ℝ) ^ 4 * (s : ℝ)) :=
      mul_le_mul_of_nonneg_right hθ (by positivity)
    have e1 : (p : ℝ) / (α : ℝ) ^ 4 * ((α : ℝ) ^ 4 * (s : ℝ)) = (p : ℝ) * (s : ℝ) := by
      field_simp
    have e2 : ((t - s : ℕ) : ℝ) / (s : ℝ) * ((α : ℝ) ^ 4 * (s : ℝ)) =
        ((t - s : ℕ) : ℝ) * (α : ℝ) ^ 4 := by
      field_simp
    linarith [e1 ▸ h2, e2 ▸ h2]
  have h1n : p * s ≤ α ^ 4 * (t - s) := by exact_mod_cast h1
  have hX : p * s ≤ (α ^ 2 * (t - s)) * α ^ 2 := by
    have he : (α ^ 2 * (t - s)) * α ^ 2 = α ^ 4 * (t - s) := by ring
    omega
  have hdiv : (p * s - 1) / (α ^ 2 * (t - s)) ≤ α ^ 2 :=
    Nat.div_le_of_le_mul (le_trans (Nat.sub_le _ _) hX)
  have hfin : egN p α s t - 1 ≤ α ^ 2 := by
    simp only [egN]
    omega
  omega

/-- each tabulated weight is bounded by `2^p` in absolute value -/
theorem buWt_abs_le (p α s t : ℕ) (hα : 2 ≤ α) (hp : 100 ≤ p) (hαp : α ^ 2 < p)
    (hrow : ∀ ℓ : ℤ, ∑ h ∈ egHset (egM p α),
      |(buWt p α s t ℓ h : ℝ)| ≤ (2 : ℝ) ^ p / 2 + 8 * (egM p α : ℝ))
    (ℓ : ℤ) (h : ℤ) (hh : h ∈ egHset (egM p α)) :
    |(buWt p α s t ℓ h : ℝ)| ≤ (2 : ℝ) ^ p := by
  have h1 : |(buWt p α s t ℓ h : ℝ)| ≤ (2 : ℝ) ^ p / 2 + 8 * (egM p α : ℝ) :=
    le_trans (Finset.single_le_sum (f := fun h : ℤ => |(buWt p α s t ℓ h : ℝ)|)
      (fun i _ => abs_nonneg _) hh) (hrow ℓ)
  have hm : 8 * (egM p α : ℝ) ≤ (2 : ℝ) ^ (p - 1) := by
    have h := bu_eight_egM_le p α hp
    exact_mod_cast h
  have h2p : ((2 : ℝ) ^ p) / 2 = (2 : ℝ) ^ (p - 1) := by
    have hp1 : 1 ≤ p := by omega
    conv_lhs => rw [← Nat.sub_add_cancel hp1]
    rw [pow_succ]
    ring
  linarith

/-- the size of each tabulated weight -/
theorem buWt_isz_le (p α s t : ℕ) (hα : 2 ≤ α) (hp : 100 ≤ p) (hαp : α ^ 2 < p)
    (hrow : ∀ ℓ : ℤ, ∑ h ∈ egHset (egM p α),
      |(buWt p α s t ℓ h : ℝ)| ≤ (2 : ℝ) ^ p / 2 + 8 * (egM p α : ℝ))
    (ℓ h : ℤ) (hh : h ∈ egHset (egM p α)) :
    isz (buWt p α s t ℓ h) ≤ p + 3 := by
  have h1 := buWt_abs_le p α s t hα hp hαp hrow ℓ h hh
  have h2 : (buWt p α s t ℓ h).natAbs ≤ 2 ^ p := by
    have h3 := abs_le.mp h1
    have h4 : -((2 : ℤ) ^ p) ≤ buWt p α s t ℓ h ∧ buWt p α s t ℓ h ≤ (2 : ℤ) ^ p := by
      constructor
      · exact_mod_cast h3.1
      · exact_mod_cast h3.2
    have h5 : ((buWt p α s t ℓ h).natAbs : ℤ) ≤ (2 : ℤ) ^ p := by
      rcases le_total 0 (buWt p α s t ℓ h) with hz0 | hz0
      · have he : ((buWt p α s t ℓ h).natAbs : ℤ) = buWt p α s t ℓ h := by
          rw [Int.natAbs_of_nonneg hz0]
        rw [he]; exact h4.2
      · have h8 : 0 ≤ -(buWt p α s t ℓ h) := by omega
        have he : ((buWt p α s t ℓ h).natAbs : ℤ) = -(buWt p α s t ℓ h) := by
          rw [← Int.natAbs_neg]
          exact Int.natAbs_of_nonneg h8
        rw [he]; linarith [h4.1]
    exact_mod_cast h5
  have h6 : (buWt p α s t ℓ h).natAbs < 2 ^ (p + 1) := by
    have := Nat.lt_two_pow_self (n := p)
    omega
  exact Work.Fx.isz_le_of_natAbs_lt h6

/-- the size of the whole column table -/
theorem buColsT_vsz_le (p α s t : ℕ) (hs : 2 ≤ s) (hα : 2 ≤ α) (hp : 100 ≤ p)
    (hαp : α ^ 2 < p)
    (hrow : ∀ ℓ : ℤ, ∑ h ∈ egHset (egM p α),
      |(buWt p α s t ℓ h : ℝ)| ≤ (2 : ℝ) ^ p / 2 + 8 * (egM p α : ℝ)) :
    vsz (buColsT p α s t) ≤ 20 * (egM p α + 1) * (s + 1) * (p + 1) := by
  have hm : egM p α ≤ p + 1 := bu_egM_le p α
  obtain ⟨hfins, _, hlen, _, hle, _⟩ := buQWhs (egM p α)
  have hmem : ∀ h ∈ egHs (egM p α), h ∈ egHset (egM p α) := by
    intro h hh
    rw [← hfins, List.mem_toFinset]
    exact hh
  have hisz : ∀ h ∈ egHs (egM p α), isz h ≤ p + 3 := by
    intro h hh
    have h2 : h.natAbs ≤ p + 1 := le_trans (hle h hh) hm
    have h3 : h.natAbs < 2 ^ (p + 1) :=
      lt_of_le_of_lt h2 (Nat.lt_two_pow_self (n := p + 1))
    exact Work.Fx.isz_le_of_natAbs_lt h3
  have hwt : ∀ h ∈ egHs (egM p α), ∀ ℓ : ℤ, isz (buWt p α s t ℓ h) ≤ p + 3 :=
    fun h hh ℓ => buWt_isz_le p α s t hα hp hαp hrow ℓ h (hmem h hh)
  have hcol : ∀ h ∈ egHs (egM p α), vsz (buCol p α s t h) ≤ (s + 1) * (p + 4) := by
    intro h hh
    have h1 : vsz (buCol p α s t h) =
        s + 1 + ((List.ofFn (fun ℓ : Fin s => buWt p α s t (ℓ : ℤ) h)).map isz).sum := by
      unfold buCol
      rw [bu_vsz_zl]
      simp
    rw [h1]
    have h2 : ((List.ofFn (fun ℓ : Fin s => buWt p α s t (ℓ : ℤ) h)).map isz).sum ≤
        s * (p + 3) := by
      have hb : ((List.ofFn (fun ℓ : Fin s => buWt p α s t (ℓ : ℤ) h)).map isz).sum ≤
          ((List.ofFn (fun ℓ : Fin s => buWt p α s t (ℓ : ℤ) h)).map isz).length * (p + 3) :=
        bu_sum_le_length_mul (by
          intro x hx
          rcases List.mem_map.mp hx with ⟨z, hz, rfl⟩
          obtain ⟨i, hi⟩ := List.mem_ofFn.mp hz
          rw [← hi]
          exact hwt h hh _)
      simpa using hb
    nlinarith [Nat.zero_le s, Nat.zero_le p]
  unfold buColsT
  rw [bu_vsz_ofList, List.length_map, hlen]
  have hsum : ((List.map (fun h => Val.cons (.int h) (buCol p α s t h))
      (egHs (egM p α))).map vsz).sum ≤ 2 * egM p α * (2 * (p + 4) * (s + 1)) := by
    have hb : ((List.map (fun h => Val.cons (.int h) (buCol p α s t h))
        (egHs (egM p α))).map vsz).sum ≤
        ((List.map (fun h => Val.cons (.int h) (buCol p α s t h))
        (egHs (egM p α))).map vsz).length * (2 * (p + 4) * (s + 1)) :=
      bu_sum_le_length_mul (by
        intro x hx
        rcases List.mem_map.mp hx with ⟨a, ha, rfl⟩
        rcases List.mem_map.mp ha with ⟨h, hh, rfl⟩
        rw [Work.Fx.vsz_cons, Work.Fx.vsz_int]
        have h1 := hcol h hh
        have h2 := hisz h hh
        nlinarith [Nat.zero_le s, Nat.zero_le p])
    simp only [List.length_map] at hb
    rw [hlen] at hb
    exact hb
  have hs1 : 1 ≤ s + 1 := by omega
  have hp1 : 1 ≤ p + 1 := by omega
  have hAB : 1 ≤ (s + 1) * (p + 1) := by nlinarith [hs1, hp1]
  have hsum2 : ((List.map (fun h => Val.cons (.int h) (buCol p α s t h))
      (egHs (egM p α))).map vsz).sum ≤ 8 * egM p α * ((s + 1) * (p + 1)) := by
    have hp4 : p + 4 ≤ 2 * (p + 1) := by omega
    have hmul : 2 * (p + 4) * (s + 1) ≤ 4 * ((s + 1) * (p + 1)) := by
      nlinarith [Nat.zero_le s]
    calc ((List.map (fun h => Val.cons (.int h) (buCol p α s t h))
        (egHs (egM p α))).map vsz).sum
        ≤ 2 * egM p α * (2 * (p + 4) * (s + 1)) := hsum
      _ ≤ 2 * egM p α * (4 * ((s + 1) * (p + 1))) := Nat.mul_le_mul_left _ hmul
      _ = 8 * egM p α * ((s + 1) * (p + 1)) := by ring
  have hE : 1 ≤ egM p α := by
    unfold egM
    exact Nat.succ_le_succ (Nat.zero_le _)
  have h1 : 2 * egM p α + 1 ≤ 3 * egM p α * ((s + 1) * (p + 1)) := by
    have ha : 2 * egM p α + 1 ≤ 3 * egM p α := by omega
    calc 2 * egM p α + 1 ≤ 3 * egM p α := ha
      _ = 3 * egM p α * 1 := by ring
      _ ≤ 3 * egM p α * ((s + 1) * (p + 1)) := Nat.mul_le_mul_left _ hAB
  have h2 : 11 * egM p α * ((s + 1) * (p + 1)) ≤
      20 * (egM p α + 1) * (s + 1) * (p + 1) := by
    have hb : 11 * egM p α ≤ 20 * (egM p α + 1) := by omega
    calc 11 * egM p α * ((s + 1) * (p + 1)) ≤ (20 * (egM p α + 1)) * ((s + 1) * (p + 1)) :=
          Nat.mul_le_mul_right _ hb
      _ = 20 * (egM p α + 1) * (s + 1) * (p + 1) := by ring
  have h3 : 3 * egM p α * ((s + 1) * (p + 1)) + 8 * egM p α * ((s + 1) * (p + 1)) =
      11 * egM p α * ((s + 1) * (p + 1)) := by ring
  linarith

/-! ## 5.  The cleanup word -/

/-- deleting the leftover values: `[vf, u, C, s, p] ↦ [u]`. -/
def buCleanProg (dropP : Cmd) (rollP : ℕ → Cmd) : Cmd :=
  .seq dropP (.seq (rollP 1) (.seq dropP (.seq (rollP 1) (.seq dropP (.seq (rollP 1) dropP)))))

/-- dropping the head of a window -/
theorem buPipe_drop1 (main : Cmd) {dropP : Cmd} {Kd : ℕ}
    (h : ∀ m : Cmd, WordR m dropP (fun vs => vs ≠ [])
      (fun vs out => ∃ v rest, vs = v :: rest ∧ out = rest)
      (fun vs => Kd * (vsz (vs.headD .nil) + 1)))
    (T : List Val) (x : Val) : Pipe main dropP (x :: T) T (Kd * (vsz x + 1)) :=
  Pipe.appendTail T (Pipe.drop main h x)

/-- moving the second value of a window to its head -/
theorem buPipe_roll1 (main : Cmd) {rollP : ℕ → Cmd} {Kr : ℕ}
    (h : ∀ (m : Cmd) (k : ℕ), WordR m (rollP k) (fun vs => k < vs.length)
      (fun vs out => out = vs.getD k .nil :: vs.eraseIdx k)
      (fun vs => Kr * (k + 1) * (((vs.take (k + 1)).map vsz).sum + 1)))
    (T : List Val) (x y : Val) :
    Pipe main (rollP 1) (x :: y :: T) (y :: x :: T) (Kr * 2 * (vsz x + vsz y + 1)) := by
  have h2 := Pipe.roll (main := main) (prog := rollP) (K := Kr) h
    (A := (x :: y :: T)) (k := 1) (by simp)
  have h3 : ((x :: y :: T : List Val).getD 1 .nil) :: ((x :: y :: T).eraseIdx 1) = y :: x :: T := by
    simp
  refine Pipe.le (Pipe.rw h2 h3) ?_
  rw [show ((x :: y :: T : List Val).take 2) = [x, y] by simp]
  simp [Work.Fx.szl_cons, Work.Fx.szl_singleton]

/-- the cleanup word deletes everything but the accumulator -/
theorem buPipe_clean (main : Cmd) {dropP : Cmd} {Kd : ℕ} {rollP : ℕ → Cmd} {Kr : ℕ}
    (hdrop : ∀ m : Cmd, WordR m dropP (fun vs => vs ≠ [])
      (fun vs out => ∃ v rest, vs = v :: rest ∧ out = rest)
      (fun vs => Kd * (vsz (vs.headD .nil) + 1)))
    (hroll : ∀ (m : Cmd) (k : ℕ), WordR m (rollP k) (fun vs => k < vs.length)
      (fun vs out => out = vs.getD k .nil :: vs.eraseIdx k)
      (fun vs => Kr * (k + 1) * (((vs.take (k + 1)).map vsz).sum + 1)))
    (vf u : List (ℤ × ℤ)) (p α s t : ℕ) :
    Pipe main (buCleanProg dropP rollP)
      [cvecVal vf, cvecVal u, buColsT p α s t, Val.int (s : ℤ), Val.int (p : ℤ)] [cvecVal u]
      ((4 * Kd + 6 * Kr + 8) *
        (vsz (cvecVal vf) + vsz (cvecVal u) + vsz (buColsT p α s t) + isz (s : ℤ) +
          isz (p : ℤ) + 1)) := by
  set W := vsz (cvecVal vf) + vsz (cvecVal u) + vsz (buColsT p α s t) + isz (s : ℤ) +
    isz (p : ℤ) + 1 with hW
  have s1 : Pipe main dropP
      [cvecVal vf, cvecVal u, buColsT p α s t, Val.int (s : ℤ), Val.int (p : ℤ)]
      [cvecVal u, buColsT p α s t, Val.int (s : ℤ), Val.int (p : ℤ)] (Kd * W) := by
    refine Pipe.le (buPipe_drop1 main hdrop
      [cvecVal u, buColsT p α s t, Val.int (s : ℤ), Val.int (p : ℤ)] (cvecVal vf)) ?_
    rw [hW]; exact Nat.mul_le_mul_left Kd (by omega)
  have s2 : Pipe main (rollP 1)
      [cvecVal u, buColsT p α s t, Val.int (s : ℤ), Val.int (p : ℤ)]
      [buColsT p α s t, cvecVal u, Val.int (s : ℤ), Val.int (p : ℤ)] (2 * Kr * W) := by
    refine Pipe.le (buPipe_roll1 main hroll
      [Val.int (s : ℤ), Val.int (p : ℤ)] (cvecVal u) (buColsT p α s t)) ?_
    rw [hW]
    calc Kr * 2 * (vsz (cvecVal u) + vsz (buColsT p α s t) + 1)
        ≤ Kr * 2 * (vsz (cvecVal vf) + vsz (cvecVal u) + vsz (buColsT p α s t) + isz (s : ℤ) +
            isz (p : ℤ) + 1) := Nat.mul_le_mul_left (Kr * 2) (by omega)
      _ = 2 * Kr * (vsz (cvecVal vf) + vsz (cvecVal u) + vsz (buColsT p α s t) + isz (s : ℤ) +
            isz (p : ℤ) + 1) := by ring
  have s3 : Pipe main dropP
      [buColsT p α s t, cvecVal u, Val.int (s : ℤ), Val.int (p : ℤ)]
      [cvecVal u, Val.int (s : ℤ), Val.int (p : ℤ)] (Kd * W) := by
    refine Pipe.le (buPipe_drop1 main hdrop [cvecVal u, Val.int (s : ℤ), Val.int (p : ℤ)]
      (buColsT p α s t)) ?_
    rw [hW]; exact Nat.mul_le_mul_left Kd (by omega)
  have s4 : Pipe main (rollP 1)
      [cvecVal u, Val.int (s : ℤ), Val.int (p : ℤ)]
      [Val.int (s : ℤ), cvecVal u, Val.int (p : ℤ)] (2 * Kr * W) := by
    refine Pipe.le (buPipe_roll1 main hroll [Val.int (p : ℤ)] (cvecVal u) (Val.int (s : ℤ))) ?_
    rw [hW, Work.Fx.vsz_int]
    calc Kr * 2 * (vsz (cvecVal u) + isz (s : ℤ) + 1)
        ≤ Kr * 2 * (vsz (cvecVal vf) + vsz (cvecVal u) + vsz (buColsT p α s t) + isz (s : ℤ) +
            isz (p : ℤ) + 1) := Nat.mul_le_mul_left (Kr * 2) (by omega)
      _ = 2 * Kr * (vsz (cvecVal vf) + vsz (cvecVal u) + vsz (buColsT p α s t) + isz (s : ℤ) +
            isz (p : ℤ) + 1) := by ring
  have s5 : Pipe main dropP
      [Val.int (s : ℤ), cvecVal u, Val.int (p : ℤ)]
      [cvecVal u, Val.int (p : ℤ)] (Kd * W) := by
    refine Pipe.le (buPipe_drop1 main hdrop [cvecVal u, Val.int (p : ℤ)] (Val.int (s : ℤ))) ?_
    rw [hW, Work.Fx.vsz_int]; exact Nat.mul_le_mul_left Kd (by omega)
  have s6 : Pipe main (rollP 1)
      [cvecVal u, Val.int (p : ℤ)]
      [Val.int (p : ℤ), cvecVal u] (2 * Kr * W) := by
    refine Pipe.le (buPipe_roll1 main hroll [] (cvecVal u) (Val.int (p : ℤ))) ?_
    rw [hW, Work.Fx.vsz_int]
    calc Kr * 2 * (vsz (cvecVal u) + isz (p : ℤ) + 1)
        ≤ Kr * 2 * (vsz (cvecVal vf) + vsz (cvecVal u) + vsz (buColsT p α s t) + isz (s : ℤ) +
            isz (p : ℤ) + 1) := Nat.mul_le_mul_left (Kr * 2) (by omega)
      _ = 2 * Kr * (vsz (cvecVal vf) + vsz (cvecVal u) + vsz (buColsT p α s t) + isz (s : ℤ) +
            isz (p : ℤ) + 1) := by ring
  have s7 : Pipe main dropP
      [Val.int (p : ℤ), cvecVal u] [cvecVal u] (Kd * W) := by
    refine Pipe.le (buPipe_drop1 main hdrop [cvecVal u] (Val.int (p : ℤ))) ?_
    rw [hW, Work.Fx.vsz_int]; exact Nat.mul_le_mul_left Kd (by omega)
  have h1234567 :=
    Pipe.comp s1 (Pipe.comp s2 (Pipe.comp s3 (Pipe.comp s4 (Pipe.comp s5 (Pipe.comp s6 s7)))))
  have hgoal : Pipe main (buCleanProg dropP rollP)
      [cvecVal vf, cvecVal u, buColsT p α s t, Val.int (s : ℤ), Val.int (p : ℤ)] [cvecVal u]
      ((4 * Kd + 6 * Kr + 8) * W) :=
    Pipe.le h1234567 (by
      rw [hW]
      nlinarith [Nat.zero_le Kd, Nat.zero_le Kr])
  exact hgoal

/-! ## 6.  Radius bookkeeping of the rounds -/

/-- `68 p + 74 ≤ 2^(p-1)` for `p ≥ 100`. -/
theorem bu_lin_le (k : ℕ) : 68 * (100 + k) + 74 ≤ 2 ^ (99 + k) := by
  induction k with
  | zero => norm_num
  | succ k ih =>
    have h2 : 2 ^ (99 + (k + 1)) = 2 * 2 ^ (99 + k) := by
      rw [show 99 + (k + 1) = 99 + k + 1 by ring, pow_succ]; ring
    rw [h2]
    have : 68 * (100 + (k + 1)) + 74 ≤ 2 * (68 * (100 + k) + 74) := by ring_nf; omega
    linarith

theorem bu_lin_le' (p : ℕ) (hp : 100 ≤ p) : 68 * p + 74 ≤ 2 ^ (p - 1) := by
  obtain ⟨k, rfl⟩ : ∃ k, p = 100 + k := ⟨p - 100, by omega⟩
  have h := bu_lin_le k
  rwa [show 99 + k = 100 + k - 1 by omega] at h

/-- the radius sequences stay below the side conditions of the round, and the final accumulator
radius fits in `2^(p+1)` -/
theorem buQWradAux (p α s t : ℕ) (hs : 2 ≤ s) (hst : s < t) (hα : 2 ≤ α) (hp : 100 ≤ p)
    (hαp : α ^ 2 < p) (hθ : (p : ℝ) / (α : ℝ) ^ 4 ≤ (t : ℝ) / s - 1) :
    (∀ i ≤ egN p α s t, buQWB p α i ≤ 2 ^ (p + 2) ∧ buQWB2 p α i ≤ 2 ^ (p + 2)) ∧
      buQWB2 p α (egN p α s t - 1) ≤ 2 ^ (p + 1) := by
  set c := 34 * egM p α + 4 with hc
  set B0 := 2 ^ (p - 1) + 2 with hB0
  have hB0eq : buQWB p α 0 = B0 := buQWB_zero p α
  have hB20eq : buQWB2 p α 0 = B0 := buQWB2_zero p α
  have h2c : 2 * c ≤ B0 := by
    have h1 : egM p α ≤ p + 1 := bu_egM_le p α
    have h2 : 68 * p + 74 ≤ 2 ^ (p - 1) := bu_lin_le' p hp
    simp only [hc, hB0]
    omega
  have hstep : ∀ i, buQWB p α (i + 1) = buQWB p α i / 2 + c := by
    intro i
    rw [buQWB_succ, hc]
    ring
  have hstep2 : ∀ i, buQWB2 p α (i + 1) = buQWB2 p α i + buQWB p α i / 2 + c + 1 := by
    intro i
    rw [buQWB2_succ, hc]
    ring
  have hdiv : ∀ B : ℕ, B / 2 + B / 2 ≤ B := by
    intro B
    have h1 := Nat.div_add_mod B 2
    have h2 : B % 2 < 2 := Nat.mod_lt _ (by norm_num)
    omega
  have hmain : ∀ i, buQWB p α i ≤ B0 ∧ 2 * c ≤ buQWB p α i := by
    intro i
    induction i with
    | zero => exact ⟨by rw [hB0eq], by rw [hB0eq]; exact h2c⟩
    | succ i ih =>
      obtain ⟨h1, h2⟩ := ih
      have hcle : c ≤ buQWB p α i / 2 := by omega
      constructor
      · rw [hstep i]; omega
      · rw [hstep i]; omega
  have hB2le : ∀ i, buQWB2 p α i + buQWB p α i ≤ 2 * B0 + i * (2 * c + 1) := by
    intro i
    induction i with
    | zero => rw [hB20eq, hB0eq]; omega
    | succ i ih =>
      have h3 := hdiv (buQWB p α i)
      rw [hstep2 i, hstep i]
      have h4 : (i + 1) * (2 * c + 1) = i * (2 * c + 1) + (2 * c + 1) := by ring
      rw [h4]
      omega
  have hn1 : egN p α s t - 1 ≤ p := by
    have h := bu_egN_le p α s t hs hst hα hp hαp hθ
    omega
  have h2c' : 2 * c + 1 = 68 * egM p α + 9 := by
    simp only [hc]; ring
  have hB0p : 2 * B0 = 2 ^ p + 4 := by
    have hp1 : 1 ≤ p := by omega
    have h2 : 2 * 2 ^ (p - 1) = 2 ^ p := by
      have h3 : 2 * 2 ^ (p - 1) = 2 ^ (p - 1 + 1) := by
        rw [pow_succ']
      rw [h3, Nat.sub_add_cancel hp1]
    simp only [hB0]
    omega
  have hpow : 2 ^ (p + 1) = 2 * 2 ^ p := by
    rw [pow_succ]; ring
  have hpow4 : 2 ^ (p + 2) = 4 * 2 ^ p := by
    have : 2 ^ (p + 2) = 2 ^ p * 4 := by
      rw [show p + 2 = p + 2 from rfl, pow_add]; ring
    rw [this]; ring
  have hexp2 : (p + 1) * (68 * (p + 1) + 9) = 68 * p * p + 145 * p + 77 := by ring
  have hexp3 : (p + 1) * (68 * (p + 1) + 9) + 4 = 68 * p * p + 145 * p + 81 := by ring
  have hquad2 : (p + 1) * (68 * (p + 1) + 9) + 4 ≤ 2 ^ p := by
    rw [hexp3]
    have h := bu_quad_le' p hp
    nlinarith [Nat.zero_le p]
  constructor
  · intro i hi
    obtain ⟨h1, h2⟩ := hmain i
    have h3 := hB2le i
    have hB0le : B0 ≤ 2 ^ (p + 2) := by
      have hp1 : 1 ≤ p := by omega
      have h2p : 2 ^ (p - 1) ≤ 2 ^ p := Nat.pow_le_pow_right (by norm_num) (by omega)
      have h2p2 : 2 ^ p ≤ 2 ^ (p + 2) := Nat.pow_le_pow_right (by norm_num) (by omega)
      omega
    have hi' : i * (2 * c + 1) ≤ 68 * p * p + 145 * p + 77 := by
      rw [h2c']
      have h4 : i ≤ p + 1 := le_trans hi (bu_egN_le p α s t hs hst hα hp hαp hθ)
      have h5 : 68 * egM p α + 9 ≤ 68 * (p + 1) + 9 := by
        have hm := bu_egM_le p α
        omega
      calc i * (68 * egM p α + 9) ≤ (p + 1) * (68 * (p + 1) + 9) := Nat.mul_le_mul h4 h5
        _ = 68 * p * p + 145 * p + 77 := hexp2
    have hsub : B0 - buQWB p α i ≤ B0 := Nat.sub_le _ _
    constructor
    · omega
    · omega
  · have h := hB2le (egN p α s t - 1)
    have hi : (egN p α s t - 1) * (2 * c + 1) ≤ 68 * p * p + 77 * p := by
      rw [h2c']
      have h5 : 68 * egM p α + 9 ≤ 68 * (p + 1) + 9 := by
        have hm := bu_egM_le p α
        omega
      calc (egN p α s t - 1) * (68 * egM p α + 9) ≤ p * (68 * (p + 1) + 9) :=
            Nat.mul_le_mul hn1 h5
        _ = 68 * p * p + 77 * p := by ring
    have hquad := bu_quad_le' p hp
    omega

/-! ## 7.  The Neumann fold and the assembly of `buQWrounds` -/

/-- invariant of the fold over the sign list: the accumulator holds the state of `buFoldL` after
`i` rounds, starting from the vector `vin`, with the untouched tail `rest`. -/
def buInvR (p α s t : ℕ) (vin : List (ℤ × ℤ)) (rest : List Val) (i : ℕ) (acc : List Val) : Prop :=
  ∃ (v a : List (ℤ × ℤ)),
    acc = cvecVal v :: cvecVal a :: buColsT p α s t :: Val.int (s : ℤ) :: Val.int (p : ℤ) :: rest ∧
    v.length = s ∧ a.length = s ∧
    buInV (buQWB p α i) v ∧ buInV (buQWB2 p α i) a ∧
    (v, a) = buFoldL (buWt p α s t) p s (egM p α) vin ((buSignsL (egN p α s t)).take i)

theorem buQWrounds_of
    (hround : ∀ (KL : HvdH.KernelLib) (IL : HvdH.IntLib) (LL : HvdH.LayoutLib) (FL : HvdH.FxLib),
      ∃ (q : HvdH.Cmd) (Kc : ℕ),
      ∀ (p α s t : ℕ) (hs : 2 ≤ s) (hst : s < t) (hα : 2 ≤ α) (hp : 100 ≤ p)
        (B B2 : ℕ) (hB : B ≤ 2 ^ (p + 2)) (hB2 : B2 ≤ 2 ^ (p + 2))
        (hrow : ∀ ℓ : ℤ, ∑ h ∈ egHset (egM p α),
          |(buWt p α s t ℓ h : ℝ)| ≤ (2 : ℝ) ^ p / 2 + 8 * (egM p α : ℝ))
        (main : HvdH.Cmd) (N : ℕ) (Cm : ℕ → ℕ), Monotone Cm → HvdH.MulBelow main N Cm → Kc * p < N →
      HvdH.WordR main q
        (fun vs => ∃ (σ : ℤ) (v acc : List (ℤ × ℤ)) (rest : List Val), (σ = 1 ∨ σ = -1) ∧
          vs = Val.int σ :: cvecVal v :: cvecVal acc :: buColsT p α s t ::
            Val.int (s : ℤ) :: Val.int (p : ℤ) :: rest ∧
          v.length = s ∧ acc.length = s ∧ buInV B v ∧ buInV B2 acc)
        (fun vs out => ∃ (σ : ℤ) (v acc : List (ℤ × ℤ)) (rest : List Val) (v' acc' : List (ℤ × ℤ)),
          (σ = 1 ∨ σ = -1) ∧
          vs = Val.int σ :: cvecVal v :: cvecVal acc :: buColsT p α s t ::
            Val.int (s : ℤ) :: Val.int (p : ℤ) :: rest ∧
          out = cvecVal v' :: cvecVal acc' :: buColsT p α s t ::
            Val.int (s : ℤ) :: Val.int (p : ℤ) :: rest ∧
          v' = buRoundL (buWt p α s t) p s (egM p α) v ∧
          acc' = buAddV acc (buSMulV σ v') ∧ v'.length = s ∧ acc'.length = s ∧
          buInV (B / 2 + 34 * egM p α + 4) v' ∧
          buInV (B2 + B / 2 + 34 * egM p α + 5) acc')
        (fun _ => Kc * (egM p α + 1) * (s + 1) * (Cm (Kc * p) + p + 1)))
    (KL : HvdH.KernelLib) (IL : HvdH.IntLib) (LL : HvdH.LayoutLib) (FL : HvdH.FxLib) :
    ∃ (q : HvdH.Cmd) (Kc : ℕ),
    ∀ (p α s t : ℕ) (hs : 2 ≤ s) (hst : s < t) (hα : 2 ≤ α) (hp : 100 ≤ p) (hαp : α ^ 2 < p)
      (hθ : (p : ℝ) / (α : ℝ) ^ 4 ≤ (t : ℝ) / s - 1)
      (hrow : ∀ ℓ : ℤ, ∑ h ∈ egHset (egM p α),
        |(buWt p α s t ℓ h : ℝ)| ≤ (2 : ℝ) ^ p / 2 + 8 * (egM p α : ℝ))
      (main : HvdH.Cmd) (N : ℕ) (Cm : ℕ → ℕ), Monotone Cm → HvdH.MulBelow main N Cm → Kc * p < N →
    HvdH.WordR main q
      (fun vs => ∃ (v : List (ℤ × ℤ)) (rest : List HvdH.Val),
        vs = buSignsT p α s t :: cvecVal v :: cvecVal v ::
          buColsT p α s t :: HvdH.Val.int (s : ℤ) :: HvdH.Val.int (p : ℤ) :: rest ∧
        v.length = s ∧ buInV (2 ^ (p - 1) + 2) v)
      (fun vs out => ∃ (v : List (ℤ × ℤ)) (rest : List HvdH.Val) (u : List (ℤ × ℤ)),
        vs = buSignsT p α s t :: cvecVal v :: cvecVal v ::
          buColsT p α s t :: HvdH.Val.int (s : ℤ) :: HvdH.Val.int (p : ℤ) :: rest ∧
        out = HvdH.cvecVal u :: rest ∧
        u = buJsumL (buWt p α s t) p s (egM p α) (egN p α s t) v ∧
        u.length = s ∧ buInV (2 ^ (p + 1)) u)
      (fun _ => Kc * (egN p α s t + 1) * (egM p α + 1) * (s + 1) * (Cm (Kc * p) + p + 1)) := by
  obtain ⟨qr, Kr, hqr⟩ := hround KL IL LL FL
  obtain ⟨foldP, Kf, hfold⟩ := KL.foldList
  obtain ⟨dropP, Kd, hdrop⟩ := KL.drop
  obtain ⟨rollP, Krl, hroll⟩ := KL.roll
  refine ⟨.seq (foldP qr) (buCleanProg dropP rollP),
    4 * Kf + 160 * Kd + 240 * Krl + 8 * Kr + 800, ?_⟩
  intro p α s t hs hst hα hp hαp hθ hrow main N Cm hmon hMul hN
  set Kc := 4 * Kf + 160 * Kd + 240 * Krl + 8 * Kr + 800 with hKcdef
  have hKrKc : Kr ≤ Kc := by simp only [hKcdef]; omega
  obtain ⟨hrad1, hrad2⟩ := buQWradAux p α s t hs hst hα hp hαp hθ
  have hnle : egN p α s t ≤ p + 1 := bu_egN_le p α s t hs hst hα hp hαp hθ
  -- (1) the round word at the constant `Kc`
  have hroundKc : ∀ (B B2 : ℕ), B ≤ 2 ^ (p + 2) → B2 ≤ 2 ^ (p + 2) →
      WordR main qr
        (fun vs => ∃ (σ : ℤ) (v acc : List (ℤ × ℤ)) (rest : List Val), (σ = 1 ∨ σ = -1) ∧
          vs = Val.int σ :: cvecVal v :: cvecVal acc :: buColsT p α s t ::
            Val.int (s : ℤ) :: Val.int (p : ℤ) :: rest ∧
          v.length = s ∧ acc.length = s ∧ buInV B v ∧ buInV B2 acc)
        (fun vs out => ∃ (σ : ℤ) (v acc : List (ℤ × ℤ)) (rest : List Val) (v' acc' : List (ℤ × ℤ)),
          (σ = 1 ∨ σ = -1) ∧
          vs = Val.int σ :: cvecVal v :: cvecVal acc :: buColsT p α s t ::
            Val.int (s : ℤ) :: Val.int (p : ℤ) :: rest ∧
          out = cvecVal v' :: cvecVal acc' :: buColsT p α s t ::
            Val.int (s : ℤ) :: Val.int (p : ℤ) :: rest ∧
          v' = buRoundL (buWt p α s t) p s (egM p α) v ∧
          acc' = buAddV acc (buSMulV σ v') ∧ v'.length = s ∧ acc'.length = s ∧
          buInV (B / 2 + 34 * egM p α + 4) v' ∧
          buInV (B2 + B / 2 + 34 * egM p α + 5) acc')
        (fun _ => Kc * (egM p α + 1) * (s + 1) * (Cm (Kc * p) + p + 1)) := by
    intro B B2 hB hB2
    have hN' : Kr * p < N := by
      have h2 : Kr * p ≤ Kc * p := Nat.mul_le_mul_right p hKrKc
      omega
    refine Work.Kernel.WordR_conseq
      (hqr p α s t hs hst hα hp B B2 hB hB2 hrow main N Cm hmon hMul hN')
      (fun vs h => h) (fun vs out h hQ => hQ) (fun vs h => ?_)
    have hCm : Cm (Kr * p) ≤ Cm (Kc * p) := hmon (Nat.mul_le_mul_right p hKrKc)
    have h1 : Cm (Kr * p) + p + 1 ≤ Cm (Kc * p) + p + 1 := by omega
    have h2 : Kr * (egM p α + 1) ≤ Kc * (egM p α + 1) := Nat.mul_le_mul_right _ hKrKc
    have h3 : Kr * (egM p α + 1) * (s + 1) ≤ Kc * (egM p α + 1) * (s + 1) :=
      Nat.mul_le_mul_right _ h2
    exact Nat.mul_le_mul h3 h1
  -- (2) the element bound of the fold
  have hL3 : ∀ x ∈ (buSignsL (egN p α s t)).map Val.int, vsz x ≤ 3 := by
    intro x hx
    rcases List.mem_map.mp hx with ⟨z, hz, rfl⟩
    have hzb : z = 1 ∨ z = -1 := by
      rw [buSignsL] at hz
      rcases List.mem_map.mp hz with ⟨j, hj, hjeq⟩
      rw [← hjeq]
      rcases Nat.even_or_odd (j + 1) with h | h
      · exact Or.inl (Even.neg_one_pow h)
      · exact Or.inr (Odd.neg_one_pow h)
    have hzabs : z.natAbs ≤ 1 := by rcases hzb with h | h <;> rw [h] <;> norm_num
    have hsize : z.natAbs.size ≤ 1 := Nat.size_le.mpr (by omega)
    rw [Work.Fx.vsz_int]
    simp only [isz]
    omega
  -- (3) the body of the fold
  have hbody : ∀ (vin : List (ℤ × ℤ)) (rest : List Val),
      ∀ i acc, i < ((buSignsL (egN p α s t)).map Val.int).length →
        buInvR p α s t vin rest i acc →
        WordR main qr (fun vs => vs = ((buSignsL (egN p α s t)).map Val.int).getD i .nil :: acc)
          (fun _ out => buInvR p α s t vin rest (i + 1) out)
          (fun _ => Kc * (egM p α + 1) * (s + 1) * (Cm (Kc * p) + p + 1)) := by
    intro vin rest i acc hi hI
    obtain ⟨vv, aa, hacc, hvl, hal, hdB1, hdB2, hfoldi⟩ := hI
    have hlenL : i < (buSignsL (egN p α s t)).length := by simpa using hi
    have hi_le : i ≤ egN p α s t := by
      have h := hlenL
      rw [buSignsL_length] at h
      omega
    have hget : ((buSignsL (egN p α s t)).map Val.int).getD i .nil =
        Val.int ((buSignsL (egN p α s t)).getD i 0) := by
      rw [List.getD_eq_getElem _ _ hi, List.getD_eq_getElem _ _ hlenL]
      simp only [List.getElem_map]
    have hσ := buSignsL_pm (egN p α s t) i hlenL
    refine Work.Kernel.WordR_conseq
      (hroundKc (buQWB p α i) (buQWB2 p α i) (hrad1 i hi_le).1 (hrad1 i hi_le).2) ?_ ?_ ?_
    · intro vs hvs
      exact ⟨(buSignsL (egN p α s t)).getD i 0, vv, aa, rest, hσ,
        by rw [hvs, hget, hacc], hvl, hal, hdB1, hdB2⟩
    · intro vs out hvs hQ
      obtain ⟨si, vi, ai, ri, vo, ao, hsi, hvsQ, hout, hveq, haeq, hlv, hla, hdB1', hdB2'⟩ := hQ
      have hvs2 : vs = Val.int ((buSignsL (egN p α s t)).getD i 0) :: cvecVal vv ::
          cvecVal aa :: buColsT p α s t :: Val.int (s : ℤ) :: Val.int (p : ℤ) :: rest := by
        rw [hvs, hget, hacc]
      have hcase : si = (buSignsL (egN p α s t)).getD i 0 ∧ vi = vv ∧ ai = aa ∧ ri = rest := by
        have h := hvsQ.symm.trans hvs2
        have e1 := List.cons.inj h
        have e2 := List.cons.inj e1.2
        have e3 := List.cons.inj e2.2
        have e4 := List.cons.inj e3.2
        have e5 := List.cons.inj e4.2
        have e6 := List.cons.inj e5.2
        exact ⟨Val.int.inj e1.1, bu_cvecVal_inj e2.1, bu_cvecVal_inj e3.1, e6.2⟩
      obtain ⟨rfl, rfl, rfl, rfl⟩ := hcase
      refine ⟨vo, ao, hout, hlv, hla, ?_, ?_, ?_⟩
      · rw [buQWB_succ]; exact hdB1'
      · rw [buQWB2_succ]; exact hdB2'
      · rw [buFoldL_take_succ (buWt p α s t) p s (egM p α) vin (buSignsL (egN p α s t)) i hlenL,
          ← hfoldi]
        show (vo, ao) = (buRoundL (buWt p α s t) p s (egM p α) vi,
          buAddV ai (buSMulV ((buSignsL (egN p α s t)).getD i 0)
            (buRoundL (buWt p α s t) p s (egM p α) vi)))
        refine Prod.ext hveq ?_
        rw [haeq, hveq]
    · intro vs hvs
      exact le_rfl
  -- (4) the fold, for a fixed starting vector and tail
  have hfoldW : ∀ (vin : List (ℤ × ℤ)) (rest : List Val), vin.length = s →
      buInV (2 ^ (p - 1) + 2) vin →
      WordR main (foldP qr)
        (fun vs => vs = ofList ((buSignsL (egN p α s t)).map Val.int) ::
          (cvecVal vin :: cvecVal vin :: buColsT p α s t ::
            Val.int (s : ℤ) :: Val.int (p : ℤ) :: rest))
        (fun _ out => buInvR p α s t vin rest ((buSignsL (egN p α s t)).map Val.int).length out)
        (fun _ => ((buSignsL (egN p α s t)).map Val.int).length *
          ((Kc * (egM p α + 1) * (s + 1) * (Cm (Kc * p) + p + 1)) + Kf * (3 + 1)) + Kf) := by
    intro vin rest hvl hdB
    refine Work.Kernel.WordR_conseq
      (hfold main qr ((buSignsL (egN p α s t)).map Val.int) (buInvR p α s t vin rest)
        (Kc * (egM p α + 1) * (s + 1) * (Cm (Kc * p) + p + 1)) 3 hL3 (hbody vin rest))
      ?_ (fun vs out h hQ => hQ) (fun vs h => le_rfl)
    intro vs hvs
    refine ⟨cvecVal vin :: cvecVal vin :: buColsT p α s t :: Val.int (s : ℤ) ::
        Val.int (p : ℤ) :: rest, by rw [hvs], vin, vin, rfl, hvl, hvl, ?_, ?_, rfl⟩
    · rw [buQWB_zero]; exact hdB
    · rw [buQWB2_zero]; exact hdB
  -- (5) the cleanup, for a fixed tail
  have hclean : ∀ (rest : List Val),
      WordR main (buCleanProg dropP rollP)
        (fun mid => ∃ (vf u : List (ℤ × ℤ)),
          mid = cvecVal vf :: cvecVal u :: buColsT p α s t ::
            Val.int (s : ℤ) :: Val.int (p : ℤ) :: rest ∧
          u.length = s ∧ vf.length = s ∧
          buInV (buQWB2 p α (egN p α s t - 1)) u ∧
          buInV (buQWB p α (egN p α s t - 1)) vf)
        (fun mid out => ∃ (vf u : List (ℤ × ℤ)),
          mid = cvecVal vf :: cvecVal u :: buColsT p α s t ::
            Val.int (s : ℤ) :: Val.int (p : ℤ) :: rest ∧
          u.length = s ∧ vf.length = s ∧
          buInV (buQWB2 p α (egN p α s t - 1)) u ∧
          buInV (buQWB p α (egN p α s t - 1)) vf ∧
          out = cvecVal u :: rest ∧ buInV (2 ^ (p + 1)) u)
        (fun _ => (4 * Kd + 6 * Krl + 8) * (40 * (egM p α + 1) * (s + 1) * (p + 1))) := by
    intro rest
    intro mid hmid s0 R hR0
    obtain ⟨vf, u, hmid', hul, hvl', huB, hvB⟩ := hmid
    have hpipe := buPipe_clean main hdrop hroll vf u p α s t rest
    obtain ⟨out, s', k, hout, hEv, hCost, hStk, hOth⟩ := hpipe mid hmid' s0 R hR0
    refine ⟨out, s', k, ⟨vf, u, hmid', hul, hvl', huB, hvB, by rw [hout]; rfl,
      buInV_mono hrad2 huB⟩, hEv, ?_, hStk, hOth⟩
    refine le_trans hCost ?_
    have hC : vsz (buColsT p α s t) ≤ 20 * (egM p α + 1) * (s + 1) * (p + 1) :=
      buColsT_vsz_le p α s t hs hα hp hαp hrow
    have hm1 : 1 ≤ egM p α + 1 := by omega
    have hs3 : 3 ≤ s + 1 := by omega
    have hp101 : 101 ≤ p + 1 := by omega
    have hV : vsz (cvecVal vf) ≤ 9 * (s + 1) * (p + 1) := by
      have hb := bu_vsz_cvecVal (u := vf) (M := p + 5) (by
        intro z hz
        have hz' := buInV_coord hvB hz
        have hc1 : z.1.natAbs ≤ 2 ^ (p + 2) :=
          le_trans hz'.1 (hrad1 (egN p α s t - 1) (by omega)).1
        have hc2 : z.2.natAbs ≤ 2 ^ (p + 2) :=
          le_trans hz'.2 (hrad1 (egN p α s t - 1) (by omega)).1
        exact ⟨Work.Fx.isz_le_of_natAbs_lt (by
            calc z.1.natAbs ≤ 2 ^ (p + 2) := hc1
              _ < 2 ^ (p + 3) := Nat.pow_lt_pow_right (by norm_num) (by omega)),
          Work.Fx.isz_le_of_natAbs_lt (by
            calc z.2.natAbs ≤ 2 ^ (p + 2) := hc2
              _ < 2 ^ (p + 3) := Nat.pow_lt_pow_right (by norm_num) (by omega))⟩)
      have hc : 3 * vf.length * (p + 5 + 1) + 1 ≤ 9 * (s + 1) * (p + 1) := by
        rw [hvl']
        have h1 : 3 * s * (p + 6) ≤ 9 * s * (p + 1) := by
          have h2 : p + 6 ≤ 3 * (p + 1) := by omega
          calc 3 * s * (p + 6) ≤ 3 * s * (3 * (p + 1)) := Nat.mul_le_mul_left _ h2
            _ = 9 * s * (p + 1) := by ring
        have h3 : 9 * s * (p + 1) ≤ 9 * (s + 1) * (p + 1) := by
          apply Nat.mul_le_mul_right
          omega
        have h4 : 1 ≤ 9 * (s + 1) * (p + 1) := by
          have h5 : 1 ≤ (s + 1) * (p + 1) :=
            Nat.succ_le_of_lt (Nat.mul_pos (by omega) (by omega))
          calc (1 : ℕ) ≤ (s + 1) * (p + 1) := h5
            _ = 1 * ((s + 1) * (p + 1)) := by ring
            _ ≤ 9 * ((s + 1) * (p + 1)) := Nat.mul_le_mul_right _ (by norm_num : 1 ≤ 9)
            _ = 9 * (s + 1) * (p + 1) := by ring
        linarith
      exact le_trans hb hc
    have hU : vsz (cvecVal u) ≤ 9 * (s + 1) * (p + 1) := by
      have hb := bu_vsz_cvecVal (u := u) (M := p + 4) (by
        intro z hz
        have hz' := buInV_coord huB hz
        have hc1 : z.1.natAbs ≤ 2 ^ (p + 1) := le_trans hz'.1 hrad2
        have hc2 : z.2.natAbs ≤ 2 ^ (p + 1) := le_trans hz'.2 hrad2
        exact ⟨Work.Fx.isz_le_of_natAbs_lt (by
            calc z.1.natAbs ≤ 2 ^ (p + 1) := hc1
              _ < 2 ^ (p + 2) := Nat.pow_lt_pow_right (by norm_num) (by omega)),
          Work.Fx.isz_le_of_natAbs_lt (by
            calc z.2.natAbs ≤ 2 ^ (p + 1) := hc2
              _ < 2 ^ (p + 2) := Nat.pow_lt_pow_right (by norm_num) (by omega))⟩)
      have hc : 3 * u.length * (p + 4 + 1) + 1 ≤ 9 * (s + 1) * (p + 1) := by
        rw [hul]
        have h1 : 3 * s * (p + 5) ≤ 9 * s * (p + 1) := by
          have h2 : p + 5 ≤ 3 * (p + 1) := by omega
          calc 3 * s * (p + 5) ≤ 3 * s * (3 * (p + 1)) := Nat.mul_le_mul_left _ h2
            _ = 9 * s * (p + 1) := by ring
        have h3 : 9 * s * (p + 1) ≤ 9 * (s + 1) * (p + 1) := by
          apply Nat.mul_le_mul_right
          omega
        have h4 : 1 ≤ 9 * (s + 1) * (p + 1) := by
          have h5 : 1 ≤ (s + 1) * (p + 1) :=
            Nat.succ_le_of_lt (Nat.mul_pos (by omega) (by omega))
          calc (1 : ℕ) ≤ (s + 1) * (p + 1) := h5
            _ = 1 * ((s + 1) * (p + 1)) := by ring
            _ ≤ 9 * ((s + 1) * (p + 1)) := Nat.mul_le_mul_right _ (by norm_num : 1 ≤ 9)
            _ = 9 * (s + 1) * (p + 1) := by ring
        linarith
      exact le_trans hb hc
    have hsz : isz ((s : ℤ)) ≤ 3 * (s + 1) := by
      have h : ((s : ℤ)).natAbs = s := Int.natAbs_natCast s
      have h2 : s.size ≤ s := Nat.size_le.mpr (Nat.lt_two_pow_self (n := s))
      simp only [isz, h]
      omega
    have hpz : isz ((p : ℤ)) ≤ 3 * (p + 1) := by
      have h : ((p : ℤ)).natAbs = p := Int.natAbs_natCast p
      have h2 : p.size ≤ p := Nat.size_le.mpr (Nat.lt_two_pow_self (n := p))
      simp only [isz, h]
      omega
    set Y := (egM p α + 1) * (s + 1) * (p + 1) with hY
    have hm2 : 2 ≤ egM p α + 1 := by
      have h : 1 ≤ egM p α := by
        unfold egM
        exact Nat.succ_le_succ (Nat.zero_le _)
      omega
    have hX1 : (s + 1) * (p + 1) ≤ Y := by
      rw [hY]
      calc (s + 1) * (p + 1) = 1 * ((s + 1) * (p + 1)) := by ring
        _ ≤ (egM p α + 1) * ((s + 1) * (p + 1)) := Nat.mul_le_mul_right _ hm1
        _ = (egM p α + 1) * (s + 1) * (p + 1) := by ring
    have hX2 : 3 * (s + 1) ≤ (s + 1) * (p + 1) := by
      calc 3 * (s + 1) ≤ (p + 1) * (s + 1) := Nat.mul_le_mul_right _ (by omega : 3 ≤ p + 1)
        _ = (s + 1) * (p + 1) := by ring
    have hX3 : 3 * (p + 1) ≤ (s + 1) * (p + 1) := Nat.mul_le_mul_right _ hs3
    have hX4 : 1 ≤ (s + 1) * (p + 1) :=
      Nat.succ_le_of_lt (Nat.mul_pos (by omega) (by omega))
    have hX5 : 3 * ((s + 1) * (p + 1)) ≤ 2 * Y := by
      rw [hY]
      have h2 : 3 * ((s + 1) * (p + 1)) ≤ 4 * ((s + 1) * (p + 1)) :=
        Nat.mul_le_mul_right _ (by norm_num : 3 ≤ 4)
      have h3 : 4 * ((s + 1) * (p + 1)) ≤
          2 * ((egM p α + 1) * (s + 1) * (p + 1)) := by
        calc 4 * ((s + 1) * (p + 1)) = 2 * (2 * ((s + 1) * (p + 1))) := by ring
          _ ≤ 2 * ((egM p α + 1) * ((s + 1) * (p + 1))) := by
              apply Nat.mul_le_mul_left
              exact Nat.mul_le_mul_right _ hm2
          _ = 2 * ((egM p α + 1) * (s + 1) * (p + 1)) := by ring
      linarith
    have hYb : 18 * ((s + 1) * (p + 1)) + 3 * (s + 1) + 3 * (p + 1) + 1 ≤ 20 * Y := by
      linarith [hX1, hX2, hX3, hX4, hX5]
    have hA : vsz (cvecVal vf) + vsz (cvecVal u) + vsz (buColsT p α s t) + isz ((s : ℤ)) +
        isz ((p : ℤ)) + 1 ≤ 40 * Y := by
      linarith [hC, hV, hU, hsz, hpz, hYb]
    rw [show 40 * Y = 40 * (egM p α + 1) * (s + 1) * (p + 1) by rw [hY]; ring] at hA
    exact Nat.mul_le_mul_left _ hA
  -- (6) the composite word for a fixed starting vector and tail
  have hcomp : ∀ (vin : List (ℤ × ℤ)) (rest : List Val), vin.length = s →
      buInV (2 ^ (p - 1) + 2) vin →
      WordR main (.seq (foldP qr) (buCleanProg dropP rollP))
        (fun vs => vs = ofList ((buSignsL (egN p α s t)).map Val.int) ::
          (cvecVal vin :: cvecVal vin :: buColsT p α s t ::
            Val.int (s : ℤ) :: Val.int (p : ℤ) :: rest))
        (fun _ out => ∃ (u : List (ℤ × ℤ)), out = cvecVal u :: rest ∧ u.length = s ∧
          buInV (2 ^ (p + 1)) u ∧ u = buJsumL (buWt p α s t) p s (egM p α) (egN p α s t) vin)
        (fun _ => ((buSignsL (egN p α s t)).map Val.int).length *
            ((Kc * (egM p α + 1) * (s + 1) * (Cm (Kc * p) + p + 1)) + Kf * (3 + 1)) + Kf +
          (4 * Kd + 6 * Krl + 8) * (40 * (egM p α + 1) * (s + 1) * (p + 1))) := by
    intro vin rest hvl hdB
    have hF := hfoldW vin rest hvl hdB
    have hCl := hclean rest
    have hmid1 : ∀ vs mid,
        (vs = ofList ((buSignsL (egN p α s t)).map Val.int) ::
          (cvecVal vin :: cvecVal vin :: buColsT p α s t ::
            Val.int (s : ℤ) :: Val.int (p : ℤ) :: rest)) →
        buInvR p α s t vin rest ((buSignsL (egN p α s t)).map Val.int).length mid →
        (∃ (vf u : List (ℤ × ℤ)),
          mid = cvecVal vf :: cvecVal u :: buColsT p α s t ::
            Val.int (s : ℤ) :: Val.int (p : ℤ) :: rest ∧
          u.length = s ∧ vf.length = s ∧
          buInV (buQWB2 p α (egN p α s t - 1)) u ∧
          buInV (buQWB p α (egN p α s t - 1)) vf) ∧
        ((4 * Kd + 6 * Krl + 8) * (40 * (egM p α + 1) * (s + 1) * (p + 1)) ≤
          (4 * Kd + 6 * Krl + 8) * (40 * (egM p α + 1) * (s + 1) * (p + 1))) := by
      intro vs mid hP hQ
      refine ⟨?_, le_rfl⟩
      obtain ⟨vf, u, hmid', hul, hal, huB, hvB, hfoldv⟩ := hQ
      rw [List.length_map, buSignsL_length] at hfoldv huB hvB
      have htake : (buSignsL (egN p α s t)).take (egN p α s t - 1) =
          buSignsL (egN p α s t) := by
        apply List.take_of_length_le
        rw [buSignsL_length]
      rw [htake] at hfoldv
      exact ⟨vf, u, hmid', hal, hul, hvB, huB⟩
    have hseq := Work.Kernel.WordR_seq hF hCl hmid1
    refine Work.Kernel.WordR_conseq hseq (fun vs h => h) ?_ (fun vs h => le_rfl)
    intro vs out hvs hQ
    obtain ⟨mid, hmid, hcln⟩ := hQ
    obtain ⟨vf, u, hmid', hul, hal, huB, hvB, hfoldv⟩ := hmid
    obtain ⟨vf', u', hmid'', hul', hvl'', huB', hvB', hout', huB''⟩ := hcln
    have hid : u' = u := by
      have h := hmid''.symm.trans hmid'
      have e1 := List.cons.inj h
      have e2 := List.cons.inj e1.2
      exact bu_cvecVal_inj e2.1
    rw [hid] at hout' huB'' hul'
    rw [List.length_map, buSignsL_length] at hfoldv
    have htake : (buSignsL (egN p α s t)).take (egN p α s t - 1) =
        buSignsL (egN p α s t) := by
      apply List.take_of_length_le
      rw [buSignsL_length]
    rw [htake] at hfoldv
    have huu : u = buJsumL (buWt p α s t) p s (egM p α) (egN p α s t) vin := by
      have hsnd := congrArg Prod.snd hfoldv
      rw [← buJsumL_eq (buWt p α s t) p s (egM p α) (egN p α s t) vin] at hsnd
      exact hsnd
    exact ⟨u, by rw [hout'], hul', huB'', huu⟩
  -- (7) the cost arithmetic
  have hcost : ((buSignsL (egN p α s t)).map Val.int).length *
        ((Kc * (egM p α + 1) * (s + 1) * (Cm (Kc * p) + p + 1)) + Kf * (3 + 1)) + Kf +
      (4 * Kd + 6 * Krl + 8) * (40 * (egM p α + 1) * (s + 1) * (p + 1)) ≤
      Kc * (egN p α s t + 1) * (egM p α + 1) * (s + 1) * (Cm (Kc * p) + p + 1) := by
    rw [List.length_map, buSignsL_length]
    set D := Cm (Kc * p) + p + 1 with hD
    set T := (egM p α + 1) * (s + 1) with hT
    have hD1 : 1 ≤ D := by simp only [hD]; omega
    have hDp : p + 1 ≤ D := by simp only [hD]; omega
    have hT1 : 1 ≤ T := by
      rw [hT]
      exact Nat.succ_le_of_lt (Nat.mul_pos (by omega) (by omega))
    have hX : Kc * (egM p α + 1) * (s + 1) * D = Kc * T * D := by rw [hT]; ring
    have hn1 : egN p α s t - 1 ≤ p := by
      have h := bu_egN_le p α s t hs hst hα hp hαp hθ
      omega
    have htail : (egN p α s t - 1) * (Kf * (3 + 1)) + Kf +
        (4 * Kd + 6 * Krl + 8) * (40 * (egM p α + 1) * (s + 1) * (p + 1)) ≤
        2 * (Kc * T * D) := by
      have hA : (egN p α s t - 1) * (Kf * (3 + 1)) + Kf ≤ (4 * Kf + 1) * (T * (p + 1)) := by
        have h1 : (egN p α s t - 1) * (Kf * 4) ≤ p * (Kf * 4) :=
          Nat.mul_le_mul_right _ hn1
        have h2 : p * (Kf * 4) + Kf ≤ (4 * Kf + 1) * (p + 1) := by
          have e : (4 * Kf + 1) * (p + 1) = 4 * Kf * p + 4 * Kf + p + 1 := by ring
          have e2 : p * (Kf * 4) = 4 * Kf * p := by ring
          rw [e, e2]
          omega
        have h3 : (p + 1) ≤ T * (p + 1) := by
          calc (p + 1) = 1 * (p + 1) := by ring
            _ ≤ T * (p + 1) := Nat.mul_le_mul_right _ hT1
        have h4 : (4 * Kf + 1) * (p + 1) ≤ (4 * Kf + 1) * (T * (p + 1)) :=
          Nat.mul_le_mul_left _ h3
        linarith
      have hB : (4 * Kd + 6 * Krl + 8) * (40 * (egM p α + 1) * (s + 1) * (p + 1)) =
          (40 * (4 * Kd + 6 * Krl + 8)) * (T * (p + 1)) := by rw [hT]; ring
      have hcoef : 4 * Kf + 1 + 40 * (4 * Kd + 6 * Krl + 8) ≤ 2 * Kc := by
        rw [hKcdef]; omega
      have hsum : (4 * Kf + 1) * (T * (p + 1)) +
          (40 * (4 * Kd + 6 * Krl + 8)) * (T * (p + 1)) ≤ 2 * (Kc * T * D) := by
        rw [← add_mul]
        have h4 : T * (p + 1) ≤ T * D := Nat.mul_le_mul_left T hDp
        calc (4 * Kf + 1 + 40 * (4 * Kd + 6 * Krl + 8)) * (T * (p + 1))
            ≤ (2 * Kc) * (T * D) := Nat.mul_le_mul hcoef h4
          _ = 2 * (Kc * T * D) := by ring
      rw [hB]
      linarith
    calc (egN p α s t - 1) *
          (Kc * (egM p α + 1) * (s + 1) * D + Kf * (3 + 1)) + Kf +
          (4 * Kd + 6 * Krl + 8) * (40 * (egM p α + 1) * (s + 1) * (p + 1))
        = (egN p α s t - 1) * (Kc * T * D) +
          ((egN p α s t - 1) * (Kf * (3 + 1)) + Kf +
            (4 * Kd + 6 * Krl + 8) * (40 * (egM p α + 1) * (s + 1) * (p + 1))) := by
          rw [hX]; ring
      _ ≤ (egN p α s t - 1) * (Kc * T * D) + 2 * (Kc * T * D) := add_le_add le_rfl htail
      _ = (egN p α s t + 1) * (Kc * T * D) := by
          rw [← add_mul]
          congr 1
      _ = Kc * (egN p α s t + 1) * (egM p α + 1) * (s + 1) * D := by rw [hT]; ring
  -- (8) the merged word (over the existential precondition) and the consequence step
  have hmain : WordR main (.seq (foldP qr) (buCleanProg dropP rollP))
      (fun vs => ∃ (vin : List (ℤ × ℤ)) (rest : List Val),
        vs = ofList ((buSignsL (egN p α s t)).map Val.int) ::
          (cvecVal vin :: cvecVal vin :: buColsT p α s t ::
            Val.int (s : ℤ) :: Val.int (p : ℤ) :: rest) ∧
        vin.length = s ∧ buInV (2 ^ (p - 1) + 2) vin)
      (fun vs out => ∃ (vin u : List (ℤ × ℤ)) (rest : List Val),
        vs = ofList ((buSignsL (egN p α s t)).map Val.int) ::
          (cvecVal vin :: cvecVal vin :: buColsT p α s t ::
            Val.int (s : ℤ) :: Val.int (p : ℤ) :: rest) ∧
        out = cvecVal u :: rest ∧ u.length = s ∧ buInV (2 ^ (p + 1)) u ∧
        u = buJsumL (buWt p α s t) p s (egM p α) (egN p α s t) vin)
      (fun _ => ((buSignsL (egN p α s t)).map Val.int).length *
          ((Kc * (egM p α + 1) * (s + 1) * (Cm (Kc * p) + p + 1)) + Kf * (3 + 1)) + Kf +
        (4 * Kd + 6 * Krl + 8) * (40 * (egM p α + 1) * (s + 1) * (p + 1))) := by
    intro vs hvs s0 R hR0
    obtain ⟨vin, rest, hvs', hvl, hdB⟩ := hvs
    obtain ⟨out, s', n, hout, hEv, hn, hStk, hOth⟩ :=
      hcomp vin rest hvl hdB vs hvs' s0 R hR0
    obtain ⟨u, hout', hul, huB, huu⟩ := hout
    exact ⟨out, s', n, ⟨vin, u, rest, hvs', hout', hul, huB, huu⟩, hEv, hn, hStk, hOth⟩
  refine Work.Kernel.WordR_conseq hmain ?_ ?_ ?_
  · intro vs hvs
    obtain ⟨v, rest, hvs', hvl, hdB⟩ := hvs
    exact ⟨v, rest, by rw [hvs']; rfl, hvl, hdB⟩
  · intro vs out hvs hQ
    obtain ⟨vin, u, rest, hvsQ, hout, hul, huB, huu⟩ := hQ
    exact ⟨vin, rest, u, by rw [hvsQ]; rfl, hout, huu, hul, huB⟩
  · intro vs hvs
    exact hcost

/-- **The requested lemma**: the word running the Neumann rounds of the one-dimensional `B̃`
resampling.  It is assembled from the single-round word (`Work.Resample.buQWround1`, whose
statement is a `Kc`-uniform variant of the round word `Work.Resample.buQWstep` that keeps the
static values `buColsT p α s t`, `s`, `p` on the stack) by the fold of `Work.Resample.buQWrounds_of`
above; the remaining step of the proof is the single-round word itself. -/
theorem buQWrounds (KL : HvdH.KernelLib) (IL : HvdH.IntLib) (LL : HvdH.LayoutLib) (FL : HvdH.FxLib) :
    ∃ (q : HvdH.Cmd) (Kc : ℕ),
    ∀ (p α s t : ℕ) (hs : 2 ≤ s) (hst : s < t) (hα : 2 ≤ α) (hp : 100 ≤ p) (hαp : α ^ 2 < p)
      (hθ : (p : ℝ) / (α : ℝ) ^ 4 ≤ (t : ℝ) / s - 1)
      (hrow : ∀ ℓ : ℤ, ∑ h ∈ Work.Resample.egHset (Work.Resample.egM p α),
        |(Work.Resample.buWt p α s t ℓ h : ℝ)| ≤ (2 : ℝ) ^ p / 2 + 8 * (Work.Resample.egM p α : ℝ))
      (main : HvdH.Cmd) (N : ℕ) (Cm : ℕ → ℕ), Monotone Cm → HvdH.MulBelow main N Cm → Kc * p < N →
    HvdH.WordR main q
      (fun vs => ∃ (v : List (ℤ × ℤ)) (rest : List HvdH.Val),
        vs = Work.Resample.buSignsT p α s t :: HvdH.cvecVal v :: HvdH.cvecVal v ::
          Work.Resample.buColsT p α s t :: HvdH.Val.int (s : ℤ) :: HvdH.Val.int (p : ℤ) :: rest ∧
        v.length = s ∧ Work.Resample.buInV (2 ^ (p - 1) + 2) v)
      (fun vs out => ∃ (v : List (ℤ × ℤ)) (rest : List HvdH.Val) (u : List (ℤ × ℤ)),
        vs = Work.Resample.buSignsT p α s t :: HvdH.cvecVal v :: HvdH.cvecVal v ::
          Work.Resample.buColsT p α s t :: HvdH.Val.int (s : ℤ) :: HvdH.Val.int (p : ℤ) :: rest ∧
        out = HvdH.cvecVal u :: rest ∧
        u = Work.Resample.buJsumL (Work.Resample.buWt p α s t) p s (Work.Resample.egM p α)
          (Work.Resample.egN p α s t) v ∧
        u.length = s ∧ Work.Resample.buInV (2 ^ (p + 1)) u)
      (fun _ => Kc * (Work.Resample.egN p α s t + 1) * (Work.Resample.egM p α + 1) * (s + 1) *
          (Cm (Kc * p) + p + 1)) :=
  buQWrounds_of (Work.Resample.buQWround1) KL IL LL FL


end Work.Resample
