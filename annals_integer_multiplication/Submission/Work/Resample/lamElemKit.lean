import Mathlib
import Submission.Work.Resample.lamDefs
import Submission.Work.Resample.auKit

/-!
# The `lamKey` element word: shared kit

Kit for `Work.Resample.lamElemWord`: the fixed values, window configurations and cost bounds for the
52-step word computing `lamKey s t m i` from `[cons (int i) (int m), int s, int t]`.

The word is cut into four independent chains

* `lamElemPartA` (`Submission/Work/Resample/lamElemPartA.lean`): steps 1--15, `V0  -> V15`
* `lamElemPartB`: steps 16--29, `V15 -> V29`
* `lamElemPartC`: steps 30--39, `V29 -> V39`
* `lamElemPartD`: steps 40--52, `V39 -> V52`

Every step is one of the `KernelLib`/`IntLib` words acting on a fixed window of at most 8 values,
each of size `<= Xsc s t m i = 8 * Wsz s t m i`; the uniform per-step budget is `CB (Xsc s t m i) KS`
and the window size lemmas `sz_V0 ... sz_V52` supply the size hypotheses of `le_CB_roll`.

* **part A** (steps 1--15), `V0 -> V15`: 1: KL.unconsV, 2: KL.roll 1, 3: KL.pick 2, 4: IL.mulS A, 5: KL.dup, 6: KL.pushVal Two, 7: IL.mulS B, 8: KL.pick 4, 9: KL.swap, 10: IL.add C, 11: KL.pick 4, 12: KL.pushVal Two, 13: IL.mulS E, 14: KL.swap, 15: IL.fdiv L
* **part B** (steps 16--29), `V15 -> V29`: 16: KL.dup, 17: KL.pick 5, 18: IL.mulS F, 19: KL.roll 2, 20: KL.swap, 21: IL.sub G, 22: KL.pushVal Two, 23: IL.mulS D, 24: KL.dup, 25: KL.pushVal One, 26: KL.pick 5, 27: IL.neg NS, 28: IL.sub NS1, 29: IL.lt Q1
* **part C** (steps 30--39), `V29 -> V39`: 30: KL.pick 4, 31: KL.roll 2, 32: IL.lt Q2, 33: KL.pick 4, 34: KL.pick 3, 35: IL.lt Q3, 36: KL.roll 1, 37: KL.roll 2, 38: IL.mulS H12, 39: IL.mulS H
* **part D** (steps 40--52), `V39 -> V52`: 40: KL.dup, 41: KL.roll 2, 42: IL.mulS LH, 43: KL.pick 3, 44: KL.roll 3, 45: IL.add R, 46: KL.pushVal One, 47: KL.roll 3, 48: KL.swap, 49: IL.sub N1H, 50: IL.mulS Sx, 51: KL.swap, 52: IL.add K0

## How to prove one step

For a step `Vk -> V(k+1)` given by a library word, use (for example, for `pick`)

```
  refine Pipe.le (Pipe.rw (Pipe.pick (main := main) hPick
      (A := V3 s t m i) (k := 2) (by simp only [V3]; norm_num))
      (by simp only [V3, V4, List.getD_cons_zero, List.getD_cons_succ])) ?_
  exact le_CB_roll hKpick (by norm_num) (sz_V3 s t m i hst) (by simp only [V3]; norm_num)
      (by have := Wsz_ge s t m i; simp only [Xsc]; omega)
```

and then chain with `Pipe.chain [p1,...,pn] [Vk,...,Vk+n] (CB (Xsc s t m i) KS) (by simp) steps`
and finish the cost with `cost_final`.  The library words are obtained by
`obtain ⟨pickProg, Kpk, hPick⟩ := KL.pick` etc.
-/

set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

namespace Work.Resample.LamElem

open HvdH
open Work.Fx

/-! ## Scale, budget and elementary size lemmas -/

/-- The size scale of the element word: the base of the cost bound of `lamElemWord`. -/
def Wsz (s t m i : ℕ) : ℕ := isz (i : ℤ) + isz (m : ℤ) + isz (s : ℤ) + isz (t : ℤ) + 1

/-- Uniform bound on the size of every value occurring in the element word. -/
def Xsc (s t m i : ℕ) : ℕ := 8 * Wsz s t m i

/-- Uniform per-step budget (with `X = Xsc s t m i`). -/
def CB (X KS : ℕ) : ℕ := KS * X ^ 4

theorem two_le_isz (z : ℤ) : 2 ≤ isz z := by simp only [isz]; omega

theorem isz_two : isz (2 : ℤ) = 4 := by
  have h : (2 : ℤ).natAbs = 2 := rfl
  have h2 : (2 : ℕ).size = 2 := by decide
  simp only [isz, h, h2]

theorem isz_one : isz (1 : ℤ) = 3 := by
  have h : (1 : ℤ).natAbs = 1 := rfl
  have h2 : (1 : ℕ).size = 1 := by decide
  simp only [isz, h, h2]

theorem isz_zero : isz (0 : ℤ) = 2 := by
  have h : (0 : ℤ).natAbs = 0 := rfl
  have h2 : (0 : ℕ).size = 0 := rfl
  simp only [isz, h, h2]

theorem isz_add_le' (a b : ℤ) : isz (a + b) ≤ isz a + isz b := by
  have h := isz_add_le a b
  have h2 := two_le_isz a
  have h3 := two_le_isz b
  omega

theorem isz_sub_le' (a b : ℤ) : isz (a - b) ≤ isz a + isz b := by
  have h := isz_sub_le a b
  have h2 := two_le_isz a
  have h3 := two_le_isz b
  omega

theorem isz_ite01 {c : Prop} [Decidable c] : isz (if c then (1 : ℤ) else 0) ≤ 3 := by
  split <;> simp only [isz_one, isz_zero] <;> omega

theorem natAbs_fdiv_le' {a b : ℤ} (ha : 0 ≤ a) (hb : 0 < b) :
    (Int.fdiv a b).natAbs ≤ a.natAbs := by
  have h1 : Int.fdiv a b = a / b := by
    rw [Int.fdiv_eq_ediv, if_pos (Or.inl (le_of_lt hb)), sub_zero]
  have h2 : 0 ≤ a / b := Int.ediv_nonneg ha (le_of_lt hb)
  have h3 : a / b ≤ a := Int.ediv_le_self b ha
  have h4 : ((a / b).natAbs : ℤ) ≤ (a.natAbs : ℤ) := by
    rw [Int.natAbs_of_nonneg h2, Int.natAbs_of_nonneg ha]
    exact h3
  rw [h1]
  exact_mod_cast h4

theorem isz_fdiv_le {a b : ℤ} (ha : 0 ≤ a) (hb : 0 < b) : isz (Int.fdiv a b) ≤ isz a := by
  have h := natAbs_fdiv_le' ha hb
  have h2 : (Int.fdiv a b).natAbs.size ≤ a.natAbs.size := Nat.size_mono' h
  simp only [isz]
  omega

theorem Wsz_ge (s t m i : ℕ) : 9 ≤ Wsz s t m i := by
  have h1 := two_le_isz (i : ℤ)
  have h2 := two_le_isz (m : ℤ)
  have h3 := two_le_isz (s : ℤ)
  have h4 := two_le_isz (t : ℤ)
  simp only [Wsz]
  omega

theorem isz_i_le_Wsz (s t m i : ℕ) : isz (i : ℤ) ≤ Wsz s t m i := by
  have h1 := two_le_isz (m : ℤ)
  have h3 := two_le_isz (s : ℤ)
  have h4 := two_le_isz (t : ℤ)
  simp only [Wsz]; omega

theorem isz_m_le_Wsz (s t m i : ℕ) : isz (m : ℤ) ≤ Wsz s t m i := by
  have h1 := two_le_isz (i : ℤ)
  have h3 := two_le_isz (s : ℤ)
  have h4 := two_le_isz (t : ℤ)
  simp only [Wsz]; omega

theorem isz_s_le_Wsz (s t m i : ℕ) : isz (s : ℤ) ≤ Wsz s t m i := by
  have h1 := two_le_isz (i : ℤ)
  have h2 := two_le_isz (m : ℤ)
  have h4 := two_le_isz (t : ℤ)
  simp only [Wsz]; omega

theorem isz_t_le_Wsz (s t m i : ℕ) : isz (t : ℤ) ≤ Wsz s t m i := by
  have h1 := two_le_isz (i : ℤ)
  have h2 := two_le_isz (m : ℤ)
  have h3 := two_le_isz (s : ℤ)
  simp only [Wsz]; omega

/-! ## Cost lemmas for one library step -/

theorem le_CB_const {K KS X : ℕ} (hK : K ≤ KS) (hX : 1 ≤ X) : K ≤ CB X KS := by
  rw [CB]
  calc K ≤ KS := hK
    _ = KS * 1 := (Nat.mul_one KS).symm
    _ ≤ KS * X ^ 4 := Nat.mul_le_mul_left KS (Nat.one_le_pow 4 X hX)

theorem le_CB_mul {K KS X u v : ℕ} (hK : K ≤ KS) (hu : u ≤ X) (hv : v ≤ X) (hX : 2 ≤ X) :
    K * u * v ≤ CB X KS := by
  rw [CB]
  have h2 : X * X ≤ X ^ 4 := by
    calc X * X = X ^ 2 := by ring
      _ ≤ X ^ 4 := Nat.pow_le_pow_right (by omega) (by norm_num)
  calc K * u * v ≤ KS * (X * X) := by
        rw [mul_assoc]
        exact Nat.mul_le_mul hK (Nat.mul_le_mul hu hv)
    _ ≤ KS * X ^ 4 := Nat.mul_le_mul_left KS h2

theorem le_CB_add {K KS X u v : ℕ} (hK : K ≤ KS) (hu : u ≤ X) (hv : v ≤ X) (hX : 2 ≤ X) :
    K * (u + v) ≤ CB X KS := by
  rw [CB]
  have h2 : 2 * X ≤ X ^ 4 := by
    have h2' : 2 * X ≤ X ^ 2 := by nlinarith
    calc 2 * X ≤ X ^ 2 := h2'
      _ ≤ X ^ 4 := Nat.pow_le_pow_right (by omega) (by norm_num)
  calc K * (u + v) ≤ KS * (2 * X) := Nat.mul_le_mul hK (by omega)
    _ ≤ KS * X ^ 4 := Nat.mul_le_mul_left KS h2

theorem le_CB_un1 {K KS X u : ℕ} (hK : K ≤ KS) (hu : u ≤ X) (hX : 1 ≤ X) :
    K * u ≤ CB X KS := by
  rw [CB]
  have h2 : X ≤ X ^ 4 := by
    calc X = X ^ 1 := (pow_one X).symm
      _ ≤ X ^ 4 := Nat.pow_le_pow_right hX (by norm_num)
  calc K * u ≤ KS * X := Nat.mul_le_mul hK hu
    _ ≤ KS * X ^ 4 := Nat.mul_le_mul_left KS h2

theorem le_CB_one {K KS X v : ℕ} (hK : K ≤ KS) (hv : v ≤ X) (hX : 2 ≤ X) :
    K * (v + 1) ≤ CB X KS := by
  rw [CB]
  have h2 : X + 1 ≤ X ^ 4 := by
    have h2' : X + 1 ≤ X ^ 2 := by nlinarith
    calc X + 1 ≤ X ^ 2 := h2'
      _ ≤ X ^ 4 := Nat.pow_le_pow_right (by omega) (by norm_num)
  calc K * (v + 1) ≤ KS * (X + 1) := Nat.mul_le_mul hK (by omega)
    _ ≤ KS * X ^ 4 := Nat.mul_le_mul_left KS h2

theorem le_CB_two {K KS X u v : ℕ} (hK : K ≤ KS) (hu : u ≤ X) (hv : v ≤ X) (hX : 3 ≤ X) :
    K * (u + v + 1) ≤ CB X KS := by
  rw [CB]
  have h2 : 2 * X + 1 ≤ X ^ 4 := by
    have h2' : 2 * X + 1 ≤ X ^ 2 := by nlinarith
    calc 2 * X + 1 ≤ X ^ 2 := h2'
      _ ≤ X ^ 4 := Nat.pow_le_pow_right (by omega) (by norm_num)
  calc K * (u + v + 1) ≤ KS * (2 * X + 1) := Nat.mul_le_mul hK (by omega)
    _ ≤ KS * X ^ 4 := Nat.mul_le_mul_left KS h2

theorem le_CB_roll {K KS X k : ℕ} (hK : K ≤ KS) (hk : k + 1 ≤ 8) {A : List Val}
    (hA : ∀ v ∈ A, vsz v ≤ X) (hAlen : A.length ≤ 8) (hX : 66 ≤ X) :
    K * (k + 1) * (szl (A.take (k + 1)) + 1) ≤ CB X KS := by
  rw [CB]
  have hsum : szl (A.take (k + 1)) ≤ 8 * X := by
    have h1 : szl (A.take (k + 1)) ≤ (A.take (k + 1)).length * X :=
      szl_le_len_mul (fun v hv => hA v (List.mem_of_mem_take hv))
    have hlen : (A.take (k + 1)).length ≤ 8 := by
      rw [List.length_take]; omega
    exact le_trans h1 (Nat.mul_le_mul_right X hlen)
  have h2 : 64 * X + 8 ≤ X ^ 2 := by nlinarith
  calc K * (k + 1) * (szl (A.take (k + 1)) + 1)
      ≤ (KS * 8) * (8 * X + 1) := Nat.mul_le_mul (Nat.mul_le_mul hK hk) (by omega)
    _ = KS * (64 * X + 8) := by ring
    _ ≤ KS * X ^ 2 := Nat.mul_le_mul_left KS h2
    _ ≤ KS * X ^ 4 := Nat.mul_le_mul_left KS (Nat.pow_le_pow_right (by omega) (by norm_num))

/-! ## The values -/

/-- `wI s t m i` (content of `vI`). -/
def wI (s t m i : ℕ) : ℤ := (i : ℤ)
/-- `wM s t m i` (content of `vM`). -/
def wM (s t m i : ℕ) : ℤ := (m : ℤ)
/-- `wS s t m i` (content of `vS`). -/
def wS (s t m i : ℕ) : ℤ := (s : ℤ)
/-- `wT s t m i` (content of `vT`). -/
def wT (s t m i : ℕ) : ℤ := (t : ℤ)
/-- `wOne s t m i` (content of `vOne`). -/
def wOne (s t m i : ℕ) : ℤ := (1 : ℤ)
/-- `wTwo s t m i` (content of `vTwo`). -/
def wTwo (s t m i : ℕ) : ℤ := (2 : ℤ)
/-- `wA s t m i` (content of `vA`). -/
def wA (s t m i : ℕ) : ℤ := wS s t m i * wM s t m i
/-- `wB s t m i` (content of `vB`). -/
def wB (s t m i : ℕ) : ℤ := wTwo s t m i * wA s t m i
/-- `wC s t m i` (content of `vC`). -/
def wC (s t m i : ℕ) : ℤ := wB s t m i + wT s t m i
/-- `wE s t m i` (content of `vE`). -/
def wE (s t m i : ℕ) : ℤ := wTwo s t m i * wT s t m i
/-- `wL s t m i` (content of `vL`). -/
def wL (s t m i : ℕ) : ℤ := Int.fdiv (wC s t m i) (wE s t m i)
/-- `wF s t m i` (content of `vF`). -/
def wF (s t m i : ℕ) : ℤ := wT s t m i * wL s t m i
/-- `wG s t m i` (content of `vG`). -/
def wG (s t m i : ℕ) : ℤ := wF s t m i - wA s t m i
/-- `wD s t m i` (content of `vD`). -/
def wD (s t m i : ℕ) : ℤ := wTwo s t m i * wG s t m i
/-- `wNS s t m i` (content of `vNS`). -/
def wNS (s t m i : ℕ) : ℤ := -wS s t m i
/-- `wNS1 s t m i` (content of `vNS1`). -/
def wNS1 (s t m i : ℕ) : ℤ := wNS s t m i - wOne s t m i
/-- `wQ1 s t m i` (content of `vQ1`). -/
def wQ1 (s t m i : ℕ) : ℤ := if wNS1 s t m i < wD s t m i then (1 : ℤ) else 0
/-- `wQ2 s t m i` (content of `vQ2`). -/
def wQ2 (s t m i : ℕ) : ℤ := if wD s t m i < wS s t m i then (1 : ℤ) else 0
/-- `wQ3 s t m i` (content of `vQ3`). -/
def wQ3 (s t m i : ℕ) : ℤ := if wL s t m i < wS s t m i then (1 : ℤ) else 0
/-- `wH12 s t m i` (content of `vH12`). -/
def wH12 (s t m i : ℕ) : ℤ := wQ1 s t m i * wQ2 s t m i
/-- `wH s t m i` (content of `vH`). -/
def wH (s t m i : ℕ) : ℤ := wH12 s t m i * wQ3 s t m i
/-- `wLH s t m i` (content of `vLH`). -/
def wLH (s t m i : ℕ) : ℤ := wL s t m i * wH s t m i
/-- `wR s t m i` (content of `vR`). -/
def wR (s t m i : ℕ) : ℤ := wI s t m i + wS s t m i
/-- `wN1H s t m i` (content of `vN1H`). -/
def wN1H (s t m i : ℕ) : ℤ := wOne s t m i - wH s t m i
/-- `wSx s t m i` (content of `vSx`). -/
def wSx (s t m i : ℕ) : ℤ := wN1H s t m i * wR s t m i
/-- `wK0 s t m i` (content of `vK0`). -/
def wK0 (s t m i : ℕ) : ℤ := wLH s t m i + wSx s t m i

def vI (s t m i : ℕ) : Val := .int (wI s t m i)
def vM (s t m i : ℕ) : Val := .int (wM s t m i)
def vS (s t m i : ℕ) : Val := .int (wS s t m i)
def vT (s t m i : ℕ) : Val := .int (wT s t m i)
def vOne (s t m i : ℕ) : Val := .int (wOne s t m i)
def vTwo (s t m i : ℕ) : Val := .int (wTwo s t m i)
def vA (s t m i : ℕ) : Val := .int (wA s t m i)
def vB (s t m i : ℕ) : Val := .int (wB s t m i)
def vC (s t m i : ℕ) : Val := .int (wC s t m i)
def vE (s t m i : ℕ) : Val := .int (wE s t m i)
def vL (s t m i : ℕ) : Val := .int (wL s t m i)
def vF (s t m i : ℕ) : Val := .int (wF s t m i)
def vG (s t m i : ℕ) : Val := .int (wG s t m i)
def vD (s t m i : ℕ) : Val := .int (wD s t m i)
def vNS (s t m i : ℕ) : Val := .int (wNS s t m i)
def vNS1 (s t m i : ℕ) : Val := .int (wNS1 s t m i)
def vQ1 (s t m i : ℕ) : Val := .int (wQ1 s t m i)
def vQ2 (s t m i : ℕ) : Val := .int (wQ2 s t m i)
def vQ3 (s t m i : ℕ) : Val := .int (wQ3 s t m i)
def vH12 (s t m i : ℕ) : Val := .int (wH12 s t m i)
def vH (s t m i : ℕ) : Val := .int (wH s t m i)
def vLH (s t m i : ℕ) : Val := .int (wLH s t m i)
def vR (s t m i : ℕ) : Val := .int (wR s t m i)
def vN1H (s t m i : ℕ) : Val := .int (wN1H s t m i)
def vSx (s t m i : ℕ) : Val := .int (wSx s t m i)
def vK0 (s t m i : ℕ) : Val := .int (wK0 s t m i)

/-- The input pair `cons (int i) (int m)`. -/
def vPair (s t m i : ℕ) : Val := .cons (.int (i : ℤ)) (.int (m : ℤ))

/-! ## Exact sizes of the two small constants -/

theorem isz_wOne_eq (s t m i : ℕ) : isz (wOne s t m i) = 3 := by
  simp only [wOne]; exact isz_one

theorem isz_wTwo_eq (s t m i : ℕ) : isz (wTwo s t m i) = 4 := by
  simp only [wTwo]; exact isz_two

/-! ## Size bounds of the values -/

theorem isz_wI_le (s t m i : ℕ) : isz (wI s t m i) ≤ isz (i : ℤ) := by
  simp only [wI]
  exact le_rfl

theorem isz_wM_le (s t m i : ℕ) : isz (wM s t m i) ≤ isz (m : ℤ) := by
  simp only [wM]
  exact le_rfl

theorem isz_wS_le (s t m i : ℕ) : isz (wS s t m i) ≤ isz (s : ℤ) := by
  simp only [wS]
  exact le_rfl

theorem isz_wT_le (s t m i : ℕ) : isz (wT s t m i) ≤ isz (t : ℤ) := by
  simp only [wT]
  exact le_rfl

theorem isz_wOne_le (s t m i : ℕ) : isz (wOne s t m i) ≤ 3 := by
  have h1 : isz (wOne s t m i) = 3 := isz_wOne_eq s t m i
  omega

theorem isz_wTwo_le (s t m i : ℕ) : isz (wTwo s t m i) ≤ 4 := by
  have h1 : isz (wTwo s t m i) = 4 := isz_wTwo_eq s t m i
  omega

theorem isz_wA_le (s t m i : ℕ) : isz (wA s t m i) ≤ isz (s : ℤ) + isz (m : ℤ) := by
  have h1 : isz (wA s t m i) ≤ isz (wS s t m i) + isz (wM s t m i) := isz_mul_le _ _
  have h2 := isz_wS_le s t m i
  have h3 := isz_wM_le s t m i
  omega

theorem isz_wB_le (s t m i : ℕ) : isz (wB s t m i) ≤ 4 + isz (s : ℤ) + isz (m : ℤ) := by
  have h1 : isz (wB s t m i) ≤ isz (wTwo s t m i) + isz (wA s t m i) := isz_mul_le _ _
  have h2 : isz (wTwo s t m i) = 4 := isz_wTwo_eq s t m i
  have h3 := isz_wA_le s t m i
  omega

theorem isz_wC_le (s t m i : ℕ) : isz (wC s t m i) ≤ 4 + isz (s : ℤ) + isz (m : ℤ) + isz (t : ℤ) := by
  have h1 : isz (wC s t m i) ≤ isz (wB s t m i) + isz (wT s t m i) := isz_add_le' _ _
  have h2 := isz_wB_le s t m i
  have h3 := isz_wT_le s t m i
  omega

theorem isz_wE_le (s t m i : ℕ) : isz (wE s t m i) ≤ 4 + isz (t : ℤ) := by
  have h1 : isz (wE s t m i) ≤ isz (wTwo s t m i) + isz (wT s t m i) := isz_mul_le _ _
  have h2 : isz (wTwo s t m i) = 4 := isz_wTwo_eq s t m i
  have h3 := isz_wT_le s t m i
  omega

theorem isz_wL_le (s t m i : ℕ) (hst : s < t) : isz (wL s t m i) ≤ 4 + isz (s : ℤ) + isz (m : ℤ) + isz (t : ℤ) := by
  have hnC : 0 ≤ wC s t m i := by
    simp only [wC, wB, wA, wS, wM, wTwo, wT]; positivity
  have hpE : 0 < wE s t m i := by
    have ht : (0 : ℤ) < (t : ℤ) := by exact_mod_cast (by omega : 0 < t)
    simp only [wE, wTwo, wT]; linarith
  have h1 : isz (wL s t m i) ≤ isz (wC s t m i) := by
    rw [wL]; exact isz_fdiv_le hnC hpE
  have h2 := isz_wC_le s t m i
  omega

theorem isz_wF_le (s t m i : ℕ) (hst : s < t) : isz (wF s t m i) ≤ 4 + isz (s : ℤ) + isz (m : ℤ) + 2 * isz (t : ℤ) := by
  have h1 : isz (wF s t m i) ≤ isz (wT s t m i) + isz (wL s t m i) := isz_mul_le _ _
  have h2 := isz_wT_le s t m i
  have h3 := isz_wL_le s t m i hst
  omega

theorem isz_wG_le (s t m i : ℕ) (hst : s < t) : isz (wG s t m i) ≤ 4 + 2 * isz (s : ℤ) + 2 * isz (m : ℤ) + 2 * isz (t : ℤ) := by
  have h1 : isz (wG s t m i) ≤ isz (wF s t m i) + isz (wA s t m i) := isz_sub_le' _ _
  have h2 := isz_wF_le s t m i hst
  have h3 := isz_wA_le s t m i
  omega

theorem isz_wD_le (s t m i : ℕ) (hst : s < t) : isz (wD s t m i) ≤ 8 + 2 * isz (s : ℤ) + 2 * isz (m : ℤ) + 2 * isz (t : ℤ) := by
  have h1 : isz (wD s t m i) ≤ isz (wTwo s t m i) + isz (wG s t m i) := isz_mul_le _ _
  have h2 : isz (wTwo s t m i) = 4 := isz_wTwo_eq s t m i
  have h3 := isz_wG_le s t m i hst
  omega

theorem isz_wNS_le (s t m i : ℕ) : isz (wNS s t m i) ≤ isz (s : ℤ) := by
  have h1 : isz (wNS s t m i) = isz (wS s t m i) := by rw [wNS]; exact isz_neg _
  have h2 := isz_wS_le s t m i
  omega

theorem isz_wNS1_le (s t m i : ℕ) : isz (wNS1 s t m i) ≤ 3 + isz (s : ℤ) := by
  have h1 : isz (wNS1 s t m i) ≤ isz (wNS s t m i) + isz (wOne s t m i) := isz_sub_le' _ _
  have h2 := isz_wNS_le s t m i
  have h3 : isz (wOne s t m i) = 3 := isz_wOne_eq s t m i
  omega

theorem isz_wQ1_le (s t m i : ℕ) : isz (wQ1 s t m i) ≤ 3 := by
  have h1 : isz (wQ1 s t m i) ≤ 3 := by rw [wQ1]; exact isz_ite01
  omega

theorem isz_wQ2_le (s t m i : ℕ) : isz (wQ2 s t m i) ≤ 3 := by
  have h1 : isz (wQ2 s t m i) ≤ 3 := by rw [wQ2]; exact isz_ite01
  omega

theorem isz_wQ3_le (s t m i : ℕ) : isz (wQ3 s t m i) ≤ 3 := by
  have h1 : isz (wQ3 s t m i) ≤ 3 := by rw [wQ3]; exact isz_ite01
  omega

theorem isz_wH12_le (s t m i : ℕ) : isz (wH12 s t m i) ≤ 6 := by
  have h1 : isz (wH12 s t m i) ≤ isz (wQ1 s t m i) + isz (wQ2 s t m i) := isz_mul_le _ _
  have h2 := isz_wQ1_le s t m i
  have h3 := isz_wQ2_le s t m i
  omega

theorem isz_wH_le (s t m i : ℕ) : isz (wH s t m i) ≤ 9 := by
  have h1 : isz (wH s t m i) ≤ isz (wH12 s t m i) + isz (wQ3 s t m i) := isz_mul_le _ _
  have h2 := isz_wH12_le s t m i
  have h3 := isz_wQ3_le s t m i
  omega

theorem isz_wLH_le (s t m i : ℕ) (hst : s < t) : isz (wLH s t m i) ≤ 13 + isz (s : ℤ) + isz (m : ℤ) + isz (t : ℤ) := by
  have h1 : isz (wLH s t m i) ≤ isz (wL s t m i) + isz (wH s t m i) := isz_mul_le _ _
  have h2 := isz_wL_le s t m i hst
  have h3 := isz_wH_le s t m i
  omega

theorem isz_wR_le (s t m i : ℕ) : isz (wR s t m i) ≤ isz (s : ℤ) + isz (i : ℤ) := by
  have h1 : isz (wR s t m i) ≤ isz (wI s t m i) + isz (wS s t m i) := isz_add_le' _ _
  have h2 := isz_wI_le s t m i
  have h3 := isz_wS_le s t m i
  omega

theorem isz_wN1H_le (s t m i : ℕ) : isz (wN1H s t m i) ≤ 12 := by
  have h1 : isz (wN1H s t m i) ≤ isz (wOne s t m i) + isz (wH s t m i) := isz_sub_le' _ _
  have h2 : isz (wOne s t m i) = 3 := isz_wOne_eq s t m i
  have h3 := isz_wH_le s t m i
  omega

theorem isz_wSx_le (s t m i : ℕ) : isz (wSx s t m i) ≤ 12 + isz (s : ℤ) + isz (i : ℤ) := by
  have h1 : isz (wSx s t m i) ≤ isz (wN1H s t m i) + isz (wR s t m i) := isz_mul_le _ _
  have h2 := isz_wN1H_le s t m i
  have h3 := isz_wR_le s t m i
  omega

theorem isz_wK0_le (s t m i : ℕ) (hst : s < t) : isz (wK0 s t m i) ≤ 25 + 2 * isz (s : ℤ) + isz (m : ℤ) + isz (t : ℤ) + isz (i : ℤ) := by
  have h1 : isz (wK0 s t m i) ≤ isz (wLH s t m i) + isz (wSx s t m i) := isz_add_le' _ _
  have h2 := isz_wLH_le s t m i hst
  have h3 := isz_wSx_le s t m i
  omega

/-! ## Size bounds of the values (`isz`) and of the wrappers (`vsz`) -/

theorem iszle_vI (s t m i : ℕ) : isz (wI s t m i) ≤ Xsc s t m i := by
  have h1 := isz_wI_le s t m i
  have h2 := isz_i_le_Wsz s t m i
  have h3 := isz_m_le_Wsz s t m i
  have h4 := isz_s_le_Wsz s t m i
  have h5 := isz_t_le_Wsz s t m i
  have h6 := Wsz_ge s t m i
  simp only [Xsc]
  omega

theorem vsz_vI (s t m i : ℕ) : vsz (vI s t m i) ≤ Xsc s t m i := by
  simpa only [vI, vsz_int] using iszle_vI s t m i

theorem iszle_vM (s t m i : ℕ) : isz (wM s t m i) ≤ Xsc s t m i := by
  have h1 := isz_wM_le s t m i
  have h2 := isz_i_le_Wsz s t m i
  have h3 := isz_m_le_Wsz s t m i
  have h4 := isz_s_le_Wsz s t m i
  have h5 := isz_t_le_Wsz s t m i
  have h6 := Wsz_ge s t m i
  simp only [Xsc]
  omega

theorem vsz_vM (s t m i : ℕ) : vsz (vM s t m i) ≤ Xsc s t m i := by
  simpa only [vM, vsz_int] using iszle_vM s t m i

theorem iszle_vS (s t m i : ℕ) : isz (wS s t m i) ≤ Xsc s t m i := by
  have h1 := isz_wS_le s t m i
  have h2 := isz_i_le_Wsz s t m i
  have h3 := isz_m_le_Wsz s t m i
  have h4 := isz_s_le_Wsz s t m i
  have h5 := isz_t_le_Wsz s t m i
  have h6 := Wsz_ge s t m i
  simp only [Xsc]
  omega

theorem vsz_vS (s t m i : ℕ) : vsz (vS s t m i) ≤ Xsc s t m i := by
  simpa only [vS, vsz_int] using iszle_vS s t m i

theorem iszle_vT (s t m i : ℕ) : isz (wT s t m i) ≤ Xsc s t m i := by
  have h1 := isz_wT_le s t m i
  have h2 := isz_i_le_Wsz s t m i
  have h3 := isz_m_le_Wsz s t m i
  have h4 := isz_s_le_Wsz s t m i
  have h5 := isz_t_le_Wsz s t m i
  have h6 := Wsz_ge s t m i
  simp only [Xsc]
  omega

theorem vsz_vT (s t m i : ℕ) : vsz (vT s t m i) ≤ Xsc s t m i := by
  simpa only [vT, vsz_int] using iszle_vT s t m i

theorem iszle_vOne (s t m i : ℕ) : isz (wOne s t m i) ≤ Xsc s t m i := by
  have h1 := isz_wOne_le s t m i
  have h2 := isz_i_le_Wsz s t m i
  have h3 := isz_m_le_Wsz s t m i
  have h4 := isz_s_le_Wsz s t m i
  have h5 := isz_t_le_Wsz s t m i
  have h6 := Wsz_ge s t m i
  simp only [Xsc]
  omega

theorem vsz_vOne (s t m i : ℕ) : vsz (vOne s t m i) ≤ Xsc s t m i := by
  simpa only [vOne, vsz_int] using iszle_vOne s t m i

theorem iszle_vTwo (s t m i : ℕ) : isz (wTwo s t m i) ≤ Xsc s t m i := by
  have h1 := isz_wTwo_le s t m i
  have h2 := isz_i_le_Wsz s t m i
  have h3 := isz_m_le_Wsz s t m i
  have h4 := isz_s_le_Wsz s t m i
  have h5 := isz_t_le_Wsz s t m i
  have h6 := Wsz_ge s t m i
  simp only [Xsc]
  omega

theorem vsz_vTwo (s t m i : ℕ) : vsz (vTwo s t m i) ≤ Xsc s t m i := by
  simpa only [vTwo, vsz_int] using iszle_vTwo s t m i

theorem iszle_vA (s t m i : ℕ) : isz (wA s t m i) ≤ Xsc s t m i := by
  have h1 := isz_wA_le s t m i
  have h2 := isz_i_le_Wsz s t m i
  have h3 := isz_m_le_Wsz s t m i
  have h4 := isz_s_le_Wsz s t m i
  have h5 := isz_t_le_Wsz s t m i
  have h6 := Wsz_ge s t m i
  simp only [Xsc]
  omega

theorem vsz_vA (s t m i : ℕ) : vsz (vA s t m i) ≤ Xsc s t m i := by
  simpa only [vA, vsz_int] using iszle_vA s t m i

theorem iszle_vB (s t m i : ℕ) : isz (wB s t m i) ≤ Xsc s t m i := by
  have h1 := isz_wB_le s t m i
  have h2 := isz_i_le_Wsz s t m i
  have h3 := isz_m_le_Wsz s t m i
  have h4 := isz_s_le_Wsz s t m i
  have h5 := isz_t_le_Wsz s t m i
  have h6 := Wsz_ge s t m i
  simp only [Xsc]
  omega

theorem vsz_vB (s t m i : ℕ) : vsz (vB s t m i) ≤ Xsc s t m i := by
  simpa only [vB, vsz_int] using iszle_vB s t m i

theorem iszle_vC (s t m i : ℕ) : isz (wC s t m i) ≤ Xsc s t m i := by
  have h1 := isz_wC_le s t m i
  have h2 := isz_i_le_Wsz s t m i
  have h3 := isz_m_le_Wsz s t m i
  have h4 := isz_s_le_Wsz s t m i
  have h5 := isz_t_le_Wsz s t m i
  have h6 := Wsz_ge s t m i
  simp only [Xsc]
  omega

theorem vsz_vC (s t m i : ℕ) : vsz (vC s t m i) ≤ Xsc s t m i := by
  simpa only [vC, vsz_int] using iszle_vC s t m i

theorem iszle_vE (s t m i : ℕ) : isz (wE s t m i) ≤ Xsc s t m i := by
  have h1 := isz_wE_le s t m i
  have h2 := isz_i_le_Wsz s t m i
  have h3 := isz_m_le_Wsz s t m i
  have h4 := isz_s_le_Wsz s t m i
  have h5 := isz_t_le_Wsz s t m i
  have h6 := Wsz_ge s t m i
  simp only [Xsc]
  omega

theorem vsz_vE (s t m i : ℕ) : vsz (vE s t m i) ≤ Xsc s t m i := by
  simpa only [vE, vsz_int] using iszle_vE s t m i

theorem iszle_vL (s t m i : ℕ) (hst : s < t) : isz (wL s t m i) ≤ Xsc s t m i := by
  have h1 := isz_wL_le s t m i hst
  have h2 := isz_i_le_Wsz s t m i
  have h3 := isz_m_le_Wsz s t m i
  have h4 := isz_s_le_Wsz s t m i
  have h5 := isz_t_le_Wsz s t m i
  have h6 := Wsz_ge s t m i
  simp only [Xsc]
  omega

theorem vsz_vL (s t m i : ℕ) (hst : s < t) : vsz (vL s t m i) ≤ Xsc s t m i := by
  simpa only [vL, vsz_int] using iszle_vL s t m i hst

theorem iszle_vF (s t m i : ℕ) (hst : s < t) : isz (wF s t m i) ≤ Xsc s t m i := by
  have h1 := isz_wF_le s t m i hst
  have h2 := isz_i_le_Wsz s t m i
  have h3 := isz_m_le_Wsz s t m i
  have h4 := isz_s_le_Wsz s t m i
  have h5 := isz_t_le_Wsz s t m i
  have h6 := Wsz_ge s t m i
  simp only [Xsc]
  omega

theorem vsz_vF (s t m i : ℕ) (hst : s < t) : vsz (vF s t m i) ≤ Xsc s t m i := by
  simpa only [vF, vsz_int] using iszle_vF s t m i hst

theorem iszle_vG (s t m i : ℕ) (hst : s < t) : isz (wG s t m i) ≤ Xsc s t m i := by
  have h1 := isz_wG_le s t m i hst
  have h2 := isz_i_le_Wsz s t m i
  have h3 := isz_m_le_Wsz s t m i
  have h4 := isz_s_le_Wsz s t m i
  have h5 := isz_t_le_Wsz s t m i
  have h6 := Wsz_ge s t m i
  simp only [Xsc]
  omega

theorem vsz_vG (s t m i : ℕ) (hst : s < t) : vsz (vG s t m i) ≤ Xsc s t m i := by
  simpa only [vG, vsz_int] using iszle_vG s t m i hst

theorem iszle_vD (s t m i : ℕ) (hst : s < t) : isz (wD s t m i) ≤ Xsc s t m i := by
  have h1 := isz_wD_le s t m i hst
  have h2 := isz_i_le_Wsz s t m i
  have h3 := isz_m_le_Wsz s t m i
  have h4 := isz_s_le_Wsz s t m i
  have h5 := isz_t_le_Wsz s t m i
  have h6 := Wsz_ge s t m i
  simp only [Xsc]
  omega

theorem vsz_vD (s t m i : ℕ) (hst : s < t) : vsz (vD s t m i) ≤ Xsc s t m i := by
  simpa only [vD, vsz_int] using iszle_vD s t m i hst

theorem iszle_vNS (s t m i : ℕ) : isz (wNS s t m i) ≤ Xsc s t m i := by
  have h1 := isz_wNS_le s t m i
  have h2 := isz_i_le_Wsz s t m i
  have h3 := isz_m_le_Wsz s t m i
  have h4 := isz_s_le_Wsz s t m i
  have h5 := isz_t_le_Wsz s t m i
  have h6 := Wsz_ge s t m i
  simp only [Xsc]
  omega

theorem vsz_vNS (s t m i : ℕ) : vsz (vNS s t m i) ≤ Xsc s t m i := by
  simpa only [vNS, vsz_int] using iszle_vNS s t m i

theorem iszle_vNS1 (s t m i : ℕ) : isz (wNS1 s t m i) ≤ Xsc s t m i := by
  have h1 := isz_wNS1_le s t m i
  have h2 := isz_i_le_Wsz s t m i
  have h3 := isz_m_le_Wsz s t m i
  have h4 := isz_s_le_Wsz s t m i
  have h5 := isz_t_le_Wsz s t m i
  have h6 := Wsz_ge s t m i
  simp only [Xsc]
  omega

theorem vsz_vNS1 (s t m i : ℕ) : vsz (vNS1 s t m i) ≤ Xsc s t m i := by
  simpa only [vNS1, vsz_int] using iszle_vNS1 s t m i

theorem iszle_vQ1 (s t m i : ℕ) : isz (wQ1 s t m i) ≤ Xsc s t m i := by
  have h1 := isz_wQ1_le s t m i
  have h2 := isz_i_le_Wsz s t m i
  have h3 := isz_m_le_Wsz s t m i
  have h4 := isz_s_le_Wsz s t m i
  have h5 := isz_t_le_Wsz s t m i
  have h6 := Wsz_ge s t m i
  simp only [Xsc]
  omega

theorem vsz_vQ1 (s t m i : ℕ) : vsz (vQ1 s t m i) ≤ Xsc s t m i := by
  simpa only [vQ1, vsz_int] using iszle_vQ1 s t m i

theorem iszle_vQ2 (s t m i : ℕ) : isz (wQ2 s t m i) ≤ Xsc s t m i := by
  have h1 := isz_wQ2_le s t m i
  have h2 := isz_i_le_Wsz s t m i
  have h3 := isz_m_le_Wsz s t m i
  have h4 := isz_s_le_Wsz s t m i
  have h5 := isz_t_le_Wsz s t m i
  have h6 := Wsz_ge s t m i
  simp only [Xsc]
  omega

theorem vsz_vQ2 (s t m i : ℕ) : vsz (vQ2 s t m i) ≤ Xsc s t m i := by
  simpa only [vQ2, vsz_int] using iszle_vQ2 s t m i

theorem iszle_vQ3 (s t m i : ℕ) : isz (wQ3 s t m i) ≤ Xsc s t m i := by
  have h1 := isz_wQ3_le s t m i
  have h2 := isz_i_le_Wsz s t m i
  have h3 := isz_m_le_Wsz s t m i
  have h4 := isz_s_le_Wsz s t m i
  have h5 := isz_t_le_Wsz s t m i
  have h6 := Wsz_ge s t m i
  simp only [Xsc]
  omega

theorem vsz_vQ3 (s t m i : ℕ) : vsz (vQ3 s t m i) ≤ Xsc s t m i := by
  simpa only [vQ3, vsz_int] using iszle_vQ3 s t m i

theorem iszle_vH12 (s t m i : ℕ) : isz (wH12 s t m i) ≤ Xsc s t m i := by
  have h1 := isz_wH12_le s t m i
  have h2 := isz_i_le_Wsz s t m i
  have h3 := isz_m_le_Wsz s t m i
  have h4 := isz_s_le_Wsz s t m i
  have h5 := isz_t_le_Wsz s t m i
  have h6 := Wsz_ge s t m i
  simp only [Xsc]
  omega

theorem vsz_vH12 (s t m i : ℕ) : vsz (vH12 s t m i) ≤ Xsc s t m i := by
  simpa only [vH12, vsz_int] using iszle_vH12 s t m i

theorem iszle_vH (s t m i : ℕ) : isz (wH s t m i) ≤ Xsc s t m i := by
  have h1 := isz_wH_le s t m i
  have h2 := isz_i_le_Wsz s t m i
  have h3 := isz_m_le_Wsz s t m i
  have h4 := isz_s_le_Wsz s t m i
  have h5 := isz_t_le_Wsz s t m i
  have h6 := Wsz_ge s t m i
  simp only [Xsc]
  omega

theorem vsz_vH (s t m i : ℕ) : vsz (vH s t m i) ≤ Xsc s t m i := by
  simpa only [vH, vsz_int] using iszle_vH s t m i

theorem iszle_vLH (s t m i : ℕ) (hst : s < t) : isz (wLH s t m i) ≤ Xsc s t m i := by
  have h1 := isz_wLH_le s t m i hst
  have h2 := isz_i_le_Wsz s t m i
  have h3 := isz_m_le_Wsz s t m i
  have h4 := isz_s_le_Wsz s t m i
  have h5 := isz_t_le_Wsz s t m i
  have h6 := Wsz_ge s t m i
  simp only [Xsc]
  omega

theorem vsz_vLH (s t m i : ℕ) (hst : s < t) : vsz (vLH s t m i) ≤ Xsc s t m i := by
  simpa only [vLH, vsz_int] using iszle_vLH s t m i hst

theorem iszle_vR (s t m i : ℕ) : isz (wR s t m i) ≤ Xsc s t m i := by
  have h1 := isz_wR_le s t m i
  have h2 := isz_i_le_Wsz s t m i
  have h3 := isz_m_le_Wsz s t m i
  have h4 := isz_s_le_Wsz s t m i
  have h5 := isz_t_le_Wsz s t m i
  have h6 := Wsz_ge s t m i
  simp only [Xsc]
  omega

theorem vsz_vR (s t m i : ℕ) : vsz (vR s t m i) ≤ Xsc s t m i := by
  simpa only [vR, vsz_int] using iszle_vR s t m i

theorem iszle_vN1H (s t m i : ℕ) : isz (wN1H s t m i) ≤ Xsc s t m i := by
  have h1 := isz_wN1H_le s t m i
  have h2 := isz_i_le_Wsz s t m i
  have h3 := isz_m_le_Wsz s t m i
  have h4 := isz_s_le_Wsz s t m i
  have h5 := isz_t_le_Wsz s t m i
  have h6 := Wsz_ge s t m i
  simp only [Xsc]
  omega

theorem vsz_vN1H (s t m i : ℕ) : vsz (vN1H s t m i) ≤ Xsc s t m i := by
  simpa only [vN1H, vsz_int] using iszle_vN1H s t m i

theorem iszle_vSx (s t m i : ℕ) : isz (wSx s t m i) ≤ Xsc s t m i := by
  have h1 := isz_wSx_le s t m i
  have h2 := isz_i_le_Wsz s t m i
  have h3 := isz_m_le_Wsz s t m i
  have h4 := isz_s_le_Wsz s t m i
  have h5 := isz_t_le_Wsz s t m i
  have h6 := Wsz_ge s t m i
  simp only [Xsc]
  omega

theorem vsz_vSx (s t m i : ℕ) : vsz (vSx s t m i) ≤ Xsc s t m i := by
  simpa only [vSx, vsz_int] using iszle_vSx s t m i

theorem iszle_vK0 (s t m i : ℕ) (hst : s < t) : isz (wK0 s t m i) ≤ Xsc s t m i := by
  have h1 := isz_wK0_le s t m i hst
  have h2 := isz_i_le_Wsz s t m i
  have h3 := isz_m_le_Wsz s t m i
  have h4 := isz_s_le_Wsz s t m i
  have h5 := isz_t_le_Wsz s t m i
  have h6 := Wsz_ge s t m i
  simp only [Xsc]
  omega

theorem vsz_vK0 (s t m i : ℕ) (hst : s < t) : vsz (vK0 s t m i) ≤ Xsc s t m i := by
  simpa only [vK0, vsz_int] using iszle_vK0 s t m i hst

/-! ## Size bound of the input pair -/

theorem vsz_vPair (s t m i : ℕ) : vsz (vPair s t m i) ≤ Xsc s t m i := by
  have h2 := isz_i_le_Wsz s t m i
  have h3 := isz_m_le_Wsz s t m i
  have h6 := Wsz_ge s t m i
  simp only [vPair, vsz_cons, vsz_int, Xsc]
  omega

/-! ## The windows -/

def V0 (s t m i : ℕ) : List Val := [vPair s t m i, vS s t m i, vT s t m i]
def V1 (s t m i : ℕ) : List Val := [vI s t m i, vM s t m i, vS s t m i, vT s t m i]
def V2 (s t m i : ℕ) : List Val := [vM s t m i, vI s t m i, vS s t m i, vT s t m i]
def V3 (s t m i : ℕ) : List Val := [vS s t m i, vM s t m i, vI s t m i, vS s t m i, vT s t m i]
def V4 (s t m i : ℕ) : List Val := [vA s t m i, vI s t m i, vS s t m i, vT s t m i]
def V5 (s t m i : ℕ) : List Val := [vA s t m i, vA s t m i, vI s t m i, vS s t m i, vT s t m i]
def V6 (s t m i : ℕ) : List Val := [vTwo s t m i, vA s t m i, vA s t m i, vI s t m i, vS s t m i, vT s t m i]
def V7 (s t m i : ℕ) : List Val := [vB s t m i, vA s t m i, vI s t m i, vS s t m i, vT s t m i]
def V8 (s t m i : ℕ) : List Val := [vT s t m i, vB s t m i, vA s t m i, vI s t m i, vS s t m i, vT s t m i]
def V9 (s t m i : ℕ) : List Val := [vB s t m i, vT s t m i, vA s t m i, vI s t m i, vS s t m i, vT s t m i]
def V10 (s t m i : ℕ) : List Val := [vC s t m i, vA s t m i, vI s t m i, vS s t m i, vT s t m i]
def V11 (s t m i : ℕ) : List Val := [vT s t m i, vC s t m i, vA s t m i, vI s t m i, vS s t m i, vT s t m i]
def V12 (s t m i : ℕ) : List Val := [vTwo s t m i, vT s t m i, vC s t m i, vA s t m i, vI s t m i, vS s t m i, vT s t m i]
def V13 (s t m i : ℕ) : List Val := [vE s t m i, vC s t m i, vA s t m i, vI s t m i, vS s t m i, vT s t m i]
def V14 (s t m i : ℕ) : List Val := [vC s t m i, vE s t m i, vA s t m i, vI s t m i, vS s t m i, vT s t m i]
def V15 (s t m i : ℕ) : List Val := [vL s t m i, vA s t m i, vI s t m i, vS s t m i, vT s t m i]
def V16 (s t m i : ℕ) : List Val := [vL s t m i, vL s t m i, vA s t m i, vI s t m i, vS s t m i, vT s t m i]
def V17 (s t m i : ℕ) : List Val := [vT s t m i, vL s t m i, vL s t m i, vA s t m i, vI s t m i, vS s t m i, vT s t m i]
def V18 (s t m i : ℕ) : List Val := [vF s t m i, vL s t m i, vA s t m i, vI s t m i, vS s t m i, vT s t m i]
def V19 (s t m i : ℕ) : List Val := [vA s t m i, vF s t m i, vL s t m i, vI s t m i, vS s t m i, vT s t m i]
def V20 (s t m i : ℕ) : List Val := [vF s t m i, vA s t m i, vL s t m i, vI s t m i, vS s t m i, vT s t m i]
def V21 (s t m i : ℕ) : List Val := [vG s t m i, vL s t m i, vI s t m i, vS s t m i, vT s t m i]
def V22 (s t m i : ℕ) : List Val := [vTwo s t m i, vG s t m i, vL s t m i, vI s t m i, vS s t m i, vT s t m i]
def V23 (s t m i : ℕ) : List Val := [vD s t m i, vL s t m i, vI s t m i, vS s t m i, vT s t m i]
def V24 (s t m i : ℕ) : List Val := [vD s t m i, vD s t m i, vL s t m i, vI s t m i, vS s t m i, vT s t m i]
def V25 (s t m i : ℕ) : List Val := [vOne s t m i, vD s t m i, vD s t m i, vL s t m i, vI s t m i, vS s t m i, vT s t m i]
def V26 (s t m i : ℕ) : List Val := [vS s t m i, vOne s t m i, vD s t m i, vD s t m i, vL s t m i, vI s t m i, vS s t m i, vT s t m i]
def V27 (s t m i : ℕ) : List Val := [vNS s t m i, vOne s t m i, vD s t m i, vD s t m i, vL s t m i, vI s t m i, vS s t m i, vT s t m i]
def V28 (s t m i : ℕ) : List Val := [vNS1 s t m i, vD s t m i, vD s t m i, vL s t m i, vI s t m i, vS s t m i, vT s t m i]
def V29 (s t m i : ℕ) : List Val := [vQ1 s t m i, vD s t m i, vL s t m i, vI s t m i, vS s t m i, vT s t m i]
def V30 (s t m i : ℕ) : List Val := [vS s t m i, vQ1 s t m i, vD s t m i, vL s t m i, vI s t m i, vS s t m i, vT s t m i]
def V31 (s t m i : ℕ) : List Val := [vD s t m i, vS s t m i, vQ1 s t m i, vL s t m i, vI s t m i, vS s t m i, vT s t m i]
def V32 (s t m i : ℕ) : List Val := [vQ2 s t m i, vQ1 s t m i, vL s t m i, vI s t m i, vS s t m i, vT s t m i]
def V33 (s t m i : ℕ) : List Val := [vS s t m i, vQ2 s t m i, vQ1 s t m i, vL s t m i, vI s t m i, vS s t m i, vT s t m i]
def V34 (s t m i : ℕ) : List Val := [vL s t m i, vS s t m i, vQ2 s t m i, vQ1 s t m i, vL s t m i, vI s t m i, vS s t m i, vT s t m i]
def V35 (s t m i : ℕ) : List Val := [vQ3 s t m i, vQ2 s t m i, vQ1 s t m i, vL s t m i, vI s t m i, vS s t m i, vT s t m i]
def V36 (s t m i : ℕ) : List Val := [vQ2 s t m i, vQ3 s t m i, vQ1 s t m i, vL s t m i, vI s t m i, vS s t m i, vT s t m i]
def V37 (s t m i : ℕ) : List Val := [vQ1 s t m i, vQ2 s t m i, vQ3 s t m i, vL s t m i, vI s t m i, vS s t m i, vT s t m i]
def V38 (s t m i : ℕ) : List Val := [vH12 s t m i, vQ3 s t m i, vL s t m i, vI s t m i, vS s t m i, vT s t m i]
def V39 (s t m i : ℕ) : List Val := [vH s t m i, vL s t m i, vI s t m i, vS s t m i, vT s t m i]
def V40 (s t m i : ℕ) : List Val := [vH s t m i, vH s t m i, vL s t m i, vI s t m i, vS s t m i, vT s t m i]
def V41 (s t m i : ℕ) : List Val := [vL s t m i, vH s t m i, vH s t m i, vI s t m i, vS s t m i, vT s t m i]
def V42 (s t m i : ℕ) : List Val := [vLH s t m i, vH s t m i, vI s t m i, vS s t m i, vT s t m i]
def V43 (s t m i : ℕ) : List Val := [vS s t m i, vLH s t m i, vH s t m i, vI s t m i, vS s t m i, vT s t m i]
def V44 (s t m i : ℕ) : List Val := [vI s t m i, vS s t m i, vLH s t m i, vH s t m i, vS s t m i, vT s t m i]
def V45 (s t m i : ℕ) : List Val := [vR s t m i, vLH s t m i, vH s t m i, vS s t m i, vT s t m i]
def V46 (s t m i : ℕ) : List Val := [vOne s t m i, vR s t m i, vLH s t m i, vH s t m i, vS s t m i, vT s t m i]
def V47 (s t m i : ℕ) : List Val := [vH s t m i, vOne s t m i, vR s t m i, vLH s t m i, vS s t m i, vT s t m i]
def V48 (s t m i : ℕ) : List Val := [vOne s t m i, vH s t m i, vR s t m i, vLH s t m i, vS s t m i, vT s t m i]
def V49 (s t m i : ℕ) : List Val := [vN1H s t m i, vR s t m i, vLH s t m i, vS s t m i, vT s t m i]
def V50 (s t m i : ℕ) : List Val := [vSx s t m i, vLH s t m i, vS s t m i, vT s t m i]
def V51 (s t m i : ℕ) : List Val := [vLH s t m i, vSx s t m i, vS s t m i, vT s t m i]
def V52 (s t m i : ℕ) : List Val := [vK0 s t m i, vS s t m i, vT s t m i]

/-! ## Size lemmas for the windows -/

theorem sz_V0 (s t m i : ℕ) (hst : s < t) : ∀ v ∈ V0 s t m i, vsz v ≤ Xsc s t m i := by
  intro v hv
  simp only [V0, List.mem_cons, List.mem_nil_iff, or_false] at hv
  rcases hv with rfl | rfl | rfl
  · exact vsz_vPair s t m i
  · exact vsz_vS s t m i
  · exact vsz_vT s t m i

theorem sz_V1 (s t m i : ℕ) (hst : s < t) : ∀ v ∈ V1 s t m i, vsz v ≤ Xsc s t m i := by
  intro v hv
  simp only [V1, List.mem_cons, List.mem_nil_iff, or_false] at hv
  rcases hv with rfl | rfl | rfl | rfl
  · exact vsz_vI s t m i
  · exact vsz_vM s t m i
  · exact vsz_vS s t m i
  · exact vsz_vT s t m i

theorem sz_V2 (s t m i : ℕ) (hst : s < t) : ∀ v ∈ V2 s t m i, vsz v ≤ Xsc s t m i := by
  intro v hv
  simp only [V2, List.mem_cons, List.mem_nil_iff, or_false] at hv
  rcases hv with rfl | rfl | rfl | rfl
  · exact vsz_vM s t m i
  · exact vsz_vI s t m i
  · exact vsz_vS s t m i
  · exact vsz_vT s t m i

theorem sz_V3 (s t m i : ℕ) (hst : s < t) : ∀ v ∈ V3 s t m i, vsz v ≤ Xsc s t m i := by
  intro v hv
  simp only [V3, List.mem_cons, List.mem_nil_iff, or_false] at hv
  rcases hv with rfl | rfl | rfl | rfl | rfl
  · exact vsz_vS s t m i
  · exact vsz_vM s t m i
  · exact vsz_vI s t m i
  · exact vsz_vS s t m i
  · exact vsz_vT s t m i

theorem sz_V4 (s t m i : ℕ) (hst : s < t) : ∀ v ∈ V4 s t m i, vsz v ≤ Xsc s t m i := by
  intro v hv
  simp only [V4, List.mem_cons, List.mem_nil_iff, or_false] at hv
  rcases hv with rfl | rfl | rfl | rfl
  · exact vsz_vA s t m i
  · exact vsz_vI s t m i
  · exact vsz_vS s t m i
  · exact vsz_vT s t m i

theorem sz_V5 (s t m i : ℕ) (hst : s < t) : ∀ v ∈ V5 s t m i, vsz v ≤ Xsc s t m i := by
  intro v hv
  simp only [V5, List.mem_cons, List.mem_nil_iff, or_false] at hv
  rcases hv with rfl | rfl | rfl | rfl | rfl
  · exact vsz_vA s t m i
  · exact vsz_vA s t m i
  · exact vsz_vI s t m i
  · exact vsz_vS s t m i
  · exact vsz_vT s t m i

theorem sz_V6 (s t m i : ℕ) (hst : s < t) : ∀ v ∈ V6 s t m i, vsz v ≤ Xsc s t m i := by
  intro v hv
  simp only [V6, List.mem_cons, List.mem_nil_iff, or_false] at hv
  rcases hv with rfl | rfl | rfl | rfl | rfl | rfl
  · exact vsz_vTwo s t m i
  · exact vsz_vA s t m i
  · exact vsz_vA s t m i
  · exact vsz_vI s t m i
  · exact vsz_vS s t m i
  · exact vsz_vT s t m i

theorem sz_V7 (s t m i : ℕ) (hst : s < t) : ∀ v ∈ V7 s t m i, vsz v ≤ Xsc s t m i := by
  intro v hv
  simp only [V7, List.mem_cons, List.mem_nil_iff, or_false] at hv
  rcases hv with rfl | rfl | rfl | rfl | rfl
  · exact vsz_vB s t m i
  · exact vsz_vA s t m i
  · exact vsz_vI s t m i
  · exact vsz_vS s t m i
  · exact vsz_vT s t m i

theorem sz_V8 (s t m i : ℕ) (hst : s < t) : ∀ v ∈ V8 s t m i, vsz v ≤ Xsc s t m i := by
  intro v hv
  simp only [V8, List.mem_cons, List.mem_nil_iff, or_false] at hv
  rcases hv with rfl | rfl | rfl | rfl | rfl | rfl
  · exact vsz_vT s t m i
  · exact vsz_vB s t m i
  · exact vsz_vA s t m i
  · exact vsz_vI s t m i
  · exact vsz_vS s t m i
  · exact vsz_vT s t m i

theorem sz_V9 (s t m i : ℕ) (hst : s < t) : ∀ v ∈ V9 s t m i, vsz v ≤ Xsc s t m i := by
  intro v hv
  simp only [V9, List.mem_cons, List.mem_nil_iff, or_false] at hv
  rcases hv with rfl | rfl | rfl | rfl | rfl | rfl
  · exact vsz_vB s t m i
  · exact vsz_vT s t m i
  · exact vsz_vA s t m i
  · exact vsz_vI s t m i
  · exact vsz_vS s t m i
  · exact vsz_vT s t m i

theorem sz_V10 (s t m i : ℕ) (hst : s < t) : ∀ v ∈ V10 s t m i, vsz v ≤ Xsc s t m i := by
  intro v hv
  simp only [V10, List.mem_cons, List.mem_nil_iff, or_false] at hv
  rcases hv with rfl | rfl | rfl | rfl | rfl
  · exact vsz_vC s t m i
  · exact vsz_vA s t m i
  · exact vsz_vI s t m i
  · exact vsz_vS s t m i
  · exact vsz_vT s t m i

theorem sz_V11 (s t m i : ℕ) (hst : s < t) : ∀ v ∈ V11 s t m i, vsz v ≤ Xsc s t m i := by
  intro v hv
  simp only [V11, List.mem_cons, List.mem_nil_iff, or_false] at hv
  rcases hv with rfl | rfl | rfl | rfl | rfl | rfl
  · exact vsz_vT s t m i
  · exact vsz_vC s t m i
  · exact vsz_vA s t m i
  · exact vsz_vI s t m i
  · exact vsz_vS s t m i
  · exact vsz_vT s t m i

theorem sz_V12 (s t m i : ℕ) (hst : s < t) : ∀ v ∈ V12 s t m i, vsz v ≤ Xsc s t m i := by
  intro v hv
  simp only [V12, List.mem_cons, List.mem_nil_iff, or_false] at hv
  rcases hv with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact vsz_vTwo s t m i
  · exact vsz_vT s t m i
  · exact vsz_vC s t m i
  · exact vsz_vA s t m i
  · exact vsz_vI s t m i
  · exact vsz_vS s t m i
  · exact vsz_vT s t m i

theorem sz_V13 (s t m i : ℕ) (hst : s < t) : ∀ v ∈ V13 s t m i, vsz v ≤ Xsc s t m i := by
  intro v hv
  simp only [V13, List.mem_cons, List.mem_nil_iff, or_false] at hv
  rcases hv with rfl | rfl | rfl | rfl | rfl | rfl
  · exact vsz_vE s t m i
  · exact vsz_vC s t m i
  · exact vsz_vA s t m i
  · exact vsz_vI s t m i
  · exact vsz_vS s t m i
  · exact vsz_vT s t m i

theorem sz_V14 (s t m i : ℕ) (hst : s < t) : ∀ v ∈ V14 s t m i, vsz v ≤ Xsc s t m i := by
  intro v hv
  simp only [V14, List.mem_cons, List.mem_nil_iff, or_false] at hv
  rcases hv with rfl | rfl | rfl | rfl | rfl | rfl
  · exact vsz_vC s t m i
  · exact vsz_vE s t m i
  · exact vsz_vA s t m i
  · exact vsz_vI s t m i
  · exact vsz_vS s t m i
  · exact vsz_vT s t m i

theorem sz_V15 (s t m i : ℕ) (hst : s < t) : ∀ v ∈ V15 s t m i, vsz v ≤ Xsc s t m i := by
  intro v hv
  simp only [V15, List.mem_cons, List.mem_nil_iff, or_false] at hv
  rcases hv with rfl | rfl | rfl | rfl | rfl
  · exact vsz_vL s t m i hst
  · exact vsz_vA s t m i
  · exact vsz_vI s t m i
  · exact vsz_vS s t m i
  · exact vsz_vT s t m i

theorem sz_V16 (s t m i : ℕ) (hst : s < t) : ∀ v ∈ V16 s t m i, vsz v ≤ Xsc s t m i := by
  intro v hv
  simp only [V16, List.mem_cons, List.mem_nil_iff, or_false] at hv
  rcases hv with rfl | rfl | rfl | rfl | rfl | rfl
  · exact vsz_vL s t m i hst
  · exact vsz_vL s t m i hst
  · exact vsz_vA s t m i
  · exact vsz_vI s t m i
  · exact vsz_vS s t m i
  · exact vsz_vT s t m i

theorem sz_V17 (s t m i : ℕ) (hst : s < t) : ∀ v ∈ V17 s t m i, vsz v ≤ Xsc s t m i := by
  intro v hv
  simp only [V17, List.mem_cons, List.mem_nil_iff, or_false] at hv
  rcases hv with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact vsz_vT s t m i
  · exact vsz_vL s t m i hst
  · exact vsz_vL s t m i hst
  · exact vsz_vA s t m i
  · exact vsz_vI s t m i
  · exact vsz_vS s t m i
  · exact vsz_vT s t m i

theorem sz_V18 (s t m i : ℕ) (hst : s < t) : ∀ v ∈ V18 s t m i, vsz v ≤ Xsc s t m i := by
  intro v hv
  simp only [V18, List.mem_cons, List.mem_nil_iff, or_false] at hv
  rcases hv with rfl | rfl | rfl | rfl | rfl | rfl
  · exact vsz_vF s t m i hst
  · exact vsz_vL s t m i hst
  · exact vsz_vA s t m i
  · exact vsz_vI s t m i
  · exact vsz_vS s t m i
  · exact vsz_vT s t m i

theorem sz_V19 (s t m i : ℕ) (hst : s < t) : ∀ v ∈ V19 s t m i, vsz v ≤ Xsc s t m i := by
  intro v hv
  simp only [V19, List.mem_cons, List.mem_nil_iff, or_false] at hv
  rcases hv with rfl | rfl | rfl | rfl | rfl | rfl
  · exact vsz_vA s t m i
  · exact vsz_vF s t m i hst
  · exact vsz_vL s t m i hst
  · exact vsz_vI s t m i
  · exact vsz_vS s t m i
  · exact vsz_vT s t m i

theorem sz_V20 (s t m i : ℕ) (hst : s < t) : ∀ v ∈ V20 s t m i, vsz v ≤ Xsc s t m i := by
  intro v hv
  simp only [V20, List.mem_cons, List.mem_nil_iff, or_false] at hv
  rcases hv with rfl | rfl | rfl | rfl | rfl | rfl
  · exact vsz_vF s t m i hst
  · exact vsz_vA s t m i
  · exact vsz_vL s t m i hst
  · exact vsz_vI s t m i
  · exact vsz_vS s t m i
  · exact vsz_vT s t m i

theorem sz_V21 (s t m i : ℕ) (hst : s < t) : ∀ v ∈ V21 s t m i, vsz v ≤ Xsc s t m i := by
  intro v hv
  simp only [V21, List.mem_cons, List.mem_nil_iff, or_false] at hv
  rcases hv with rfl | rfl | rfl | rfl | rfl
  · exact vsz_vG s t m i hst
  · exact vsz_vL s t m i hst
  · exact vsz_vI s t m i
  · exact vsz_vS s t m i
  · exact vsz_vT s t m i

theorem sz_V22 (s t m i : ℕ) (hst : s < t) : ∀ v ∈ V22 s t m i, vsz v ≤ Xsc s t m i := by
  intro v hv
  simp only [V22, List.mem_cons, List.mem_nil_iff, or_false] at hv
  rcases hv with rfl | rfl | rfl | rfl | rfl | rfl
  · exact vsz_vTwo s t m i
  · exact vsz_vG s t m i hst
  · exact vsz_vL s t m i hst
  · exact vsz_vI s t m i
  · exact vsz_vS s t m i
  · exact vsz_vT s t m i

theorem sz_V23 (s t m i : ℕ) (hst : s < t) : ∀ v ∈ V23 s t m i, vsz v ≤ Xsc s t m i := by
  intro v hv
  simp only [V23, List.mem_cons, List.mem_nil_iff, or_false] at hv
  rcases hv with rfl | rfl | rfl | rfl | rfl
  · exact vsz_vD s t m i hst
  · exact vsz_vL s t m i hst
  · exact vsz_vI s t m i
  · exact vsz_vS s t m i
  · exact vsz_vT s t m i

theorem sz_V24 (s t m i : ℕ) (hst : s < t) : ∀ v ∈ V24 s t m i, vsz v ≤ Xsc s t m i := by
  intro v hv
  simp only [V24, List.mem_cons, List.mem_nil_iff, or_false] at hv
  rcases hv with rfl | rfl | rfl | rfl | rfl | rfl
  · exact vsz_vD s t m i hst
  · exact vsz_vD s t m i hst
  · exact vsz_vL s t m i hst
  · exact vsz_vI s t m i
  · exact vsz_vS s t m i
  · exact vsz_vT s t m i

theorem sz_V25 (s t m i : ℕ) (hst : s < t) : ∀ v ∈ V25 s t m i, vsz v ≤ Xsc s t m i := by
  intro v hv
  simp only [V25, List.mem_cons, List.mem_nil_iff, or_false] at hv
  rcases hv with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact vsz_vOne s t m i
  · exact vsz_vD s t m i hst
  · exact vsz_vD s t m i hst
  · exact vsz_vL s t m i hst
  · exact vsz_vI s t m i
  · exact vsz_vS s t m i
  · exact vsz_vT s t m i

theorem sz_V26 (s t m i : ℕ) (hst : s < t) : ∀ v ∈ V26 s t m i, vsz v ≤ Xsc s t m i := by
  intro v hv
  simp only [V26, List.mem_cons, List.mem_nil_iff, or_false] at hv
  rcases hv with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact vsz_vS s t m i
  · exact vsz_vOne s t m i
  · exact vsz_vD s t m i hst
  · exact vsz_vD s t m i hst
  · exact vsz_vL s t m i hst
  · exact vsz_vI s t m i
  · exact vsz_vS s t m i
  · exact vsz_vT s t m i

theorem sz_V27 (s t m i : ℕ) (hst : s < t) : ∀ v ∈ V27 s t m i, vsz v ≤ Xsc s t m i := by
  intro v hv
  simp only [V27, List.mem_cons, List.mem_nil_iff, or_false] at hv
  rcases hv with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact vsz_vNS s t m i
  · exact vsz_vOne s t m i
  · exact vsz_vD s t m i hst
  · exact vsz_vD s t m i hst
  · exact vsz_vL s t m i hst
  · exact vsz_vI s t m i
  · exact vsz_vS s t m i
  · exact vsz_vT s t m i

theorem sz_V28 (s t m i : ℕ) (hst : s < t) : ∀ v ∈ V28 s t m i, vsz v ≤ Xsc s t m i := by
  intro v hv
  simp only [V28, List.mem_cons, List.mem_nil_iff, or_false] at hv
  rcases hv with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact vsz_vNS1 s t m i
  · exact vsz_vD s t m i hst
  · exact vsz_vD s t m i hst
  · exact vsz_vL s t m i hst
  · exact vsz_vI s t m i
  · exact vsz_vS s t m i
  · exact vsz_vT s t m i

theorem sz_V29 (s t m i : ℕ) (hst : s < t) : ∀ v ∈ V29 s t m i, vsz v ≤ Xsc s t m i := by
  intro v hv
  simp only [V29, List.mem_cons, List.mem_nil_iff, or_false] at hv
  rcases hv with rfl | rfl | rfl | rfl | rfl | rfl
  · exact vsz_vQ1 s t m i
  · exact vsz_vD s t m i hst
  · exact vsz_vL s t m i hst
  · exact vsz_vI s t m i
  · exact vsz_vS s t m i
  · exact vsz_vT s t m i

theorem sz_V30 (s t m i : ℕ) (hst : s < t) : ∀ v ∈ V30 s t m i, vsz v ≤ Xsc s t m i := by
  intro v hv
  simp only [V30, List.mem_cons, List.mem_nil_iff, or_false] at hv
  rcases hv with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact vsz_vS s t m i
  · exact vsz_vQ1 s t m i
  · exact vsz_vD s t m i hst
  · exact vsz_vL s t m i hst
  · exact vsz_vI s t m i
  · exact vsz_vS s t m i
  · exact vsz_vT s t m i

theorem sz_V31 (s t m i : ℕ) (hst : s < t) : ∀ v ∈ V31 s t m i, vsz v ≤ Xsc s t m i := by
  intro v hv
  simp only [V31, List.mem_cons, List.mem_nil_iff, or_false] at hv
  rcases hv with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact vsz_vD s t m i hst
  · exact vsz_vS s t m i
  · exact vsz_vQ1 s t m i
  · exact vsz_vL s t m i hst
  · exact vsz_vI s t m i
  · exact vsz_vS s t m i
  · exact vsz_vT s t m i

theorem sz_V32 (s t m i : ℕ) (hst : s < t) : ∀ v ∈ V32 s t m i, vsz v ≤ Xsc s t m i := by
  intro v hv
  simp only [V32, List.mem_cons, List.mem_nil_iff, or_false] at hv
  rcases hv with rfl | rfl | rfl | rfl | rfl | rfl
  · exact vsz_vQ2 s t m i
  · exact vsz_vQ1 s t m i
  · exact vsz_vL s t m i hst
  · exact vsz_vI s t m i
  · exact vsz_vS s t m i
  · exact vsz_vT s t m i

theorem sz_V33 (s t m i : ℕ) (hst : s < t) : ∀ v ∈ V33 s t m i, vsz v ≤ Xsc s t m i := by
  intro v hv
  simp only [V33, List.mem_cons, List.mem_nil_iff, or_false] at hv
  rcases hv with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact vsz_vS s t m i
  · exact vsz_vQ2 s t m i
  · exact vsz_vQ1 s t m i
  · exact vsz_vL s t m i hst
  · exact vsz_vI s t m i
  · exact vsz_vS s t m i
  · exact vsz_vT s t m i

theorem sz_V34 (s t m i : ℕ) (hst : s < t) : ∀ v ∈ V34 s t m i, vsz v ≤ Xsc s t m i := by
  intro v hv
  simp only [V34, List.mem_cons, List.mem_nil_iff, or_false] at hv
  rcases hv with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact vsz_vL s t m i hst
  · exact vsz_vS s t m i
  · exact vsz_vQ2 s t m i
  · exact vsz_vQ1 s t m i
  · exact vsz_vL s t m i hst
  · exact vsz_vI s t m i
  · exact vsz_vS s t m i
  · exact vsz_vT s t m i

theorem sz_V35 (s t m i : ℕ) (hst : s < t) : ∀ v ∈ V35 s t m i, vsz v ≤ Xsc s t m i := by
  intro v hv
  simp only [V35, List.mem_cons, List.mem_nil_iff, or_false] at hv
  rcases hv with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact vsz_vQ3 s t m i
  · exact vsz_vQ2 s t m i
  · exact vsz_vQ1 s t m i
  · exact vsz_vL s t m i hst
  · exact vsz_vI s t m i
  · exact vsz_vS s t m i
  · exact vsz_vT s t m i

theorem sz_V36 (s t m i : ℕ) (hst : s < t) : ∀ v ∈ V36 s t m i, vsz v ≤ Xsc s t m i := by
  intro v hv
  simp only [V36, List.mem_cons, List.mem_nil_iff, or_false] at hv
  rcases hv with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact vsz_vQ2 s t m i
  · exact vsz_vQ3 s t m i
  · exact vsz_vQ1 s t m i
  · exact vsz_vL s t m i hst
  · exact vsz_vI s t m i
  · exact vsz_vS s t m i
  · exact vsz_vT s t m i

theorem sz_V37 (s t m i : ℕ) (hst : s < t) : ∀ v ∈ V37 s t m i, vsz v ≤ Xsc s t m i := by
  intro v hv
  simp only [V37, List.mem_cons, List.mem_nil_iff, or_false] at hv
  rcases hv with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact vsz_vQ1 s t m i
  · exact vsz_vQ2 s t m i
  · exact vsz_vQ3 s t m i
  · exact vsz_vL s t m i hst
  · exact vsz_vI s t m i
  · exact vsz_vS s t m i
  · exact vsz_vT s t m i

theorem sz_V38 (s t m i : ℕ) (hst : s < t) : ∀ v ∈ V38 s t m i, vsz v ≤ Xsc s t m i := by
  intro v hv
  simp only [V38, List.mem_cons, List.mem_nil_iff, or_false] at hv
  rcases hv with rfl | rfl | rfl | rfl | rfl | rfl
  · exact vsz_vH12 s t m i
  · exact vsz_vQ3 s t m i
  · exact vsz_vL s t m i hst
  · exact vsz_vI s t m i
  · exact vsz_vS s t m i
  · exact vsz_vT s t m i

theorem sz_V39 (s t m i : ℕ) (hst : s < t) : ∀ v ∈ V39 s t m i, vsz v ≤ Xsc s t m i := by
  intro v hv
  simp only [V39, List.mem_cons, List.mem_nil_iff, or_false] at hv
  rcases hv with rfl | rfl | rfl | rfl | rfl
  · exact vsz_vH s t m i
  · exact vsz_vL s t m i hst
  · exact vsz_vI s t m i
  · exact vsz_vS s t m i
  · exact vsz_vT s t m i

theorem sz_V40 (s t m i : ℕ) (hst : s < t) : ∀ v ∈ V40 s t m i, vsz v ≤ Xsc s t m i := by
  intro v hv
  simp only [V40, List.mem_cons, List.mem_nil_iff, or_false] at hv
  rcases hv with rfl | rfl | rfl | rfl | rfl | rfl
  · exact vsz_vH s t m i
  · exact vsz_vH s t m i
  · exact vsz_vL s t m i hst
  · exact vsz_vI s t m i
  · exact vsz_vS s t m i
  · exact vsz_vT s t m i

theorem sz_V41 (s t m i : ℕ) (hst : s < t) : ∀ v ∈ V41 s t m i, vsz v ≤ Xsc s t m i := by
  intro v hv
  simp only [V41, List.mem_cons, List.mem_nil_iff, or_false] at hv
  rcases hv with rfl | rfl | rfl | rfl | rfl | rfl
  · exact vsz_vL s t m i hst
  · exact vsz_vH s t m i
  · exact vsz_vH s t m i
  · exact vsz_vI s t m i
  · exact vsz_vS s t m i
  · exact vsz_vT s t m i

theorem sz_V42 (s t m i : ℕ) (hst : s < t) : ∀ v ∈ V42 s t m i, vsz v ≤ Xsc s t m i := by
  intro v hv
  simp only [V42, List.mem_cons, List.mem_nil_iff, or_false] at hv
  rcases hv with rfl | rfl | rfl | rfl | rfl
  · exact vsz_vLH s t m i hst
  · exact vsz_vH s t m i
  · exact vsz_vI s t m i
  · exact vsz_vS s t m i
  · exact vsz_vT s t m i

theorem sz_V43 (s t m i : ℕ) (hst : s < t) : ∀ v ∈ V43 s t m i, vsz v ≤ Xsc s t m i := by
  intro v hv
  simp only [V43, List.mem_cons, List.mem_nil_iff, or_false] at hv
  rcases hv with rfl | rfl | rfl | rfl | rfl | rfl
  · exact vsz_vS s t m i
  · exact vsz_vLH s t m i hst
  · exact vsz_vH s t m i
  · exact vsz_vI s t m i
  · exact vsz_vS s t m i
  · exact vsz_vT s t m i

theorem sz_V44 (s t m i : ℕ) (hst : s < t) : ∀ v ∈ V44 s t m i, vsz v ≤ Xsc s t m i := by
  intro v hv
  simp only [V44, List.mem_cons, List.mem_nil_iff, or_false] at hv
  rcases hv with rfl | rfl | rfl | rfl | rfl | rfl
  · exact vsz_vI s t m i
  · exact vsz_vS s t m i
  · exact vsz_vLH s t m i hst
  · exact vsz_vH s t m i
  · exact vsz_vS s t m i
  · exact vsz_vT s t m i

theorem sz_V45 (s t m i : ℕ) (hst : s < t) : ∀ v ∈ V45 s t m i, vsz v ≤ Xsc s t m i := by
  intro v hv
  simp only [V45, List.mem_cons, List.mem_nil_iff, or_false] at hv
  rcases hv with rfl | rfl | rfl | rfl | rfl
  · exact vsz_vR s t m i
  · exact vsz_vLH s t m i hst
  · exact vsz_vH s t m i
  · exact vsz_vS s t m i
  · exact vsz_vT s t m i

theorem sz_V46 (s t m i : ℕ) (hst : s < t) : ∀ v ∈ V46 s t m i, vsz v ≤ Xsc s t m i := by
  intro v hv
  simp only [V46, List.mem_cons, List.mem_nil_iff, or_false] at hv
  rcases hv with rfl | rfl | rfl | rfl | rfl | rfl
  · exact vsz_vOne s t m i
  · exact vsz_vR s t m i
  · exact vsz_vLH s t m i hst
  · exact vsz_vH s t m i
  · exact vsz_vS s t m i
  · exact vsz_vT s t m i

theorem sz_V47 (s t m i : ℕ) (hst : s < t) : ∀ v ∈ V47 s t m i, vsz v ≤ Xsc s t m i := by
  intro v hv
  simp only [V47, List.mem_cons, List.mem_nil_iff, or_false] at hv
  rcases hv with rfl | rfl | rfl | rfl | rfl | rfl
  · exact vsz_vH s t m i
  · exact vsz_vOne s t m i
  · exact vsz_vR s t m i
  · exact vsz_vLH s t m i hst
  · exact vsz_vS s t m i
  · exact vsz_vT s t m i

theorem sz_V48 (s t m i : ℕ) (hst : s < t) : ∀ v ∈ V48 s t m i, vsz v ≤ Xsc s t m i := by
  intro v hv
  simp only [V48, List.mem_cons, List.mem_nil_iff, or_false] at hv
  rcases hv with rfl | rfl | rfl | rfl | rfl | rfl
  · exact vsz_vOne s t m i
  · exact vsz_vH s t m i
  · exact vsz_vR s t m i
  · exact vsz_vLH s t m i hst
  · exact vsz_vS s t m i
  · exact vsz_vT s t m i

theorem sz_V49 (s t m i : ℕ) (hst : s < t) : ∀ v ∈ V49 s t m i, vsz v ≤ Xsc s t m i := by
  intro v hv
  simp only [V49, List.mem_cons, List.mem_nil_iff, or_false] at hv
  rcases hv with rfl | rfl | rfl | rfl | rfl
  · exact vsz_vN1H s t m i
  · exact vsz_vR s t m i
  · exact vsz_vLH s t m i hst
  · exact vsz_vS s t m i
  · exact vsz_vT s t m i

theorem sz_V50 (s t m i : ℕ) (hst : s < t) : ∀ v ∈ V50 s t m i, vsz v ≤ Xsc s t m i := by
  intro v hv
  simp only [V50, List.mem_cons, List.mem_nil_iff, or_false] at hv
  rcases hv with rfl | rfl | rfl | rfl
  · exact vsz_vSx s t m i
  · exact vsz_vLH s t m i hst
  · exact vsz_vS s t m i
  · exact vsz_vT s t m i

theorem sz_V51 (s t m i : ℕ) (hst : s < t) : ∀ v ∈ V51 s t m i, vsz v ≤ Xsc s t m i := by
  intro v hv
  simp only [V51, List.mem_cons, List.mem_nil_iff, or_false] at hv
  rcases hv with rfl | rfl | rfl | rfl
  · exact vsz_vLH s t m i hst
  · exact vsz_vSx s t m i
  · exact vsz_vS s t m i
  · exact vsz_vT s t m i

theorem sz_V52 (s t m i : ℕ) (hst : s < t) : ∀ v ∈ V52 s t m i, vsz v ≤ Xsc s t m i := by
  intro v hv
  simp only [V52, List.mem_cons, List.mem_nil_iff, or_false] at hv
  rcases hv with rfl | rfl | rfl
  · exact vsz_vK0 s t m i hst
  · exact vsz_vS s t m i
  · exact vsz_vT s t m i

/-! ## The final value and the cost combination -/

/-- **The value produced by the word is `lamKey`.** -/
theorem wK0_eq_lamKey (s t m i : ℕ) :
    wK0 s t m i = Work.Resample.lamKey (s : ℤ) (t : ℤ) (m : ℤ) (i : ℤ) := by
  simp only [wK0, wLH, wSx, wN1H, wR, wH, wH12, wQ1, wQ2, wQ3, wD, wG, wF, wL, wC, wB, wE, wA,
    wTwo, wOne, wI, wM, wS, wT, wNS, wNS1, Work.Resample.lamKey, Work.Resample.lamF,
    Work.Resample.lamD, Work.Resample.lamL]
  ring_nf

/-- The four part costs fit into the final bound `10 * (KA+KB+KC+KD+1) * W^(...)`. -/
theorem cost_combine {KA KB KC KD W : ℕ} (hW : 1 ≤ W) :
    KA * W ^ KA + (KB * W ^ KB + (KC * W ^ KC + KD * W ^ KD))
      ≤ 10 * (KA + KB + KC + KD + 1) * W ^ (10 * (KA + KB + KC + KD + 1)) := by
  set K0 : ℕ := KA + KB + KC + KD + 1 with hK0
  have h1 : KA ≤ K0 := by omega
  have h2 : KB ≤ K0 := by omega
  have h3 : KC ≤ K0 := by omega
  have h4 : KD ≤ K0 := by omega
  have h1' : KA * W ^ KA ≤ K0 * W ^ K0 :=
    Nat.mul_le_mul h1 (Nat.pow_le_pow_right hW h1)
  have h2' : KB * W ^ KB ≤ K0 * W ^ K0 :=
    Nat.mul_le_mul h2 (Nat.pow_le_pow_right hW h2)
  have h3' : KC * W ^ KC ≤ K0 * W ^ K0 :=
    Nat.mul_le_mul h3 (Nat.pow_le_pow_right hW h3)
  have h4' : KD * W ^ KD ≤ K0 * W ^ K0 :=
    Nat.mul_le_mul h4 (Nat.pow_le_pow_right hW h4)
  have h5 : (4 : ℕ) * K0 ≤ 10 * K0 := by omega
  have h6 : K0 ≤ 10 * K0 := by omega
  have h7 : 4 * (K0 * W ^ K0) ≤ (10 * K0) * W ^ (10 * K0) := by
    calc 4 * (K0 * W ^ K0) = (4 * K0) * W ^ K0 := by ring
      _ ≤ (10 * K0) * W ^ K0 := Nat.mul_le_mul_right _ h5
      _ ≤ (10 * K0) * W ^ (10 * K0) := Nat.mul_le_mul_left _ (Nat.pow_le_pow_right hW h6)
  have h8 : 10 * (KA + KB + KC + KD + 1) = 10 * K0 := by rw [hK0]
  rw [h8]
  nlinarith [h1', h2', h3', h4', h7]

/-! ## Chaining a list of words along a list of windows -/

/-- The program `[p₁, …, pₙ]` sequenced in order. -/
def chainProg (ps : List Cmd) : Cmd := ps.foldr Cmd.seq .skip

theorem chainProg_nil : chainProg ([] : List Cmd) = .skip := rfl

theorem chainProg_cons (p : Cmd) (ps : List Cmd) : chainProg (p :: ps) = .seq p (chainProg ps) := rfl

theorem Pipe.skip {main : Cmd} {A : List Val} : Pipe main .skip A A 1 := by
  intro rest vs hvs s R hR
  refine ⟨A ++ rest, s, 1, rfl, Eval.skip s, le_rfl, ?_, ?_⟩
  · rw [← hvs]; exact hR
  · intro k hk; rfl

/-- Chaining words along a list of windows: if `ws = [W₀, …, Wₙ]`, `ps = [p₁, …, pₙ]` and
`pᵢ : Wᵢ → W_{i+1}` costs at most `cb`, then `chainProg ps : W₀ → Wₙ` costs at most `n·cb + 1`. -/
theorem Pipe.chain {main : Cmd} (ps : List Cmd) (ws : List (List Val)) (cb : ℕ)
    (hlen : ws.length = ps.length + 1)
    (h : ∀ i, i < ps.length →
      Pipe main (ps.getD i .skip) (ws.getD i []) (ws.getD (i + 1) []) cb) :
    Pipe main (chainProg ps) (ws.getD 0 []) (ws.getD ps.length []) (ps.length * cb + 1) := by
  induction ps generalizing ws with
  | nil =>
    have hlen1 : ws.length = 1 := by simpa using hlen
    obtain ⟨w, hw⟩ : ∃ w, ws = [w] := by
      cases ws with
      | nil => simp at hlen1
      | cons a t =>
        cases t with
        | nil => exact ⟨a, rfl⟩
        | cons b t2 => simp at hlen1
    rw [hw]
    simpa [chainProg_nil] using (Pipe.skip (main := main) (A := w))
  | cons p ps ih =>
    cases ws with
    | nil => simp at hlen
    | cons w0 ws' =>
      have hlen' : ws'.length = ps.length + 1 := by simpa using hlen
      have hstep : Pipe main p w0 (ws'.getD 0 []) cb := by
        have h0 := h 0 (by simp)
        simpa using h0
      have hrest : ∀ i, i < ps.length →
          Pipe main (ps.getD i .skip) (ws'.getD i []) (ws'.getD (i + 1) []) cb := by
        intro i hi
        have h1 := h (i + 1) (by simp; omega)
        simpa using h1
      have ihh := ih ws' hlen' hrest
      have hcomp : Pipe main (Cmd.seq p (chainProg ps)) w0 (ws'.getD ps.length [])
          (cb + (ps.length * cb + 1)) := Pipe.comp hstep ihh
      have hcost : cb + (ps.length * cb + 1) ≤ (ps.length + 1) * cb + 1 := by ring_nf; omega
      have hres := Pipe.le hcomp hcost
      simp only [chainProg_cons, List.length_cons, List.getD_cons_zero, List.getD_cons_succ]
      exact hres

/-- Final cost arithmetic: `n` steps at budget `CB (8*W) KS` fit into `K * W^K`. -/
theorem cost_final {n KS W : ℕ} (hn : n ≤ 60) (hKS : 1 ≤ KS) (hW : 9 ≤ W) :
    n * CB (8 * W) KS + 1 ≤ (1000000 * KS + 1000) * W ^ (1000000 * KS + 1000) := by
  have h1 : n * CB (8 * W) KS + 1 ≤ 61 * (KS * (8 * W) ^ 4) := by
    rw [CB]
    have h2 : n * (KS * (8 * W) ^ 4) ≤ 60 * (KS * (8 * W) ^ 4) :=
      Nat.mul_le_mul_right _ hn
    have h4 : 1 ≤ (8 * W) ^ 4 := Nat.one_le_pow 4 _ (by omega)
    have h3 : 1 ≤ KS * (8 * W) ^ 4 :=
      le_trans h4 (Nat.le_mul_of_pos_left _ (by omega : 0 < KS))
    omega
  have h4 : (8 * W) ^ 4 = 4096 * W ^ 4 := by ring
  have h5 : 61 * (KS * (4096 * W ^ 4)) = 249856 * KS * W ^ 4 := by ring
  have h6 : 249856 * KS ≤ 1000000 * KS + 1000 := by omega
  have h7 : 4 ≤ 1000000 * KS + 1000 := by omega
  calc n * CB (8 * W) KS + 1 ≤ 61 * (KS * (8 * W) ^ 4) := h1
    _ = 249856 * KS * W ^ 4 := by rw [h4, h5]
    _ ≤ (1000000 * KS + 1000) * W ^ 4 := Nat.mul_le_mul_right _ h6
    _ ≤ (1000000 * KS + 1000) * W ^ (1000000 * KS + 1000) :=
        Nat.mul_le_mul_left _ (Nat.pow_le_pow_right (by omega) h7)

end Work.Resample.LamElem
