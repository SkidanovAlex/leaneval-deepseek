/-
Auxiliary definitions and lemmas shared by the proof of `Work.SGsep.pair_separates`.

Everything here is in namespace `Work.SGsep.PSep` (abbreviation: "pair separation"), so that
neither the sibling separation files (namespace `Work.SGsep`) nor the shared glue
(`Submission/Work/SG/SGsepDefs.lean`, namespace `Work.SG`) is disturbed.
-/
import Mathlib
import Submission.Work.SG.SGsepDefs
import Submission.Work.SGsep.IsOrdOf_unique

namespace Work.SGsep

open Work.SG
open Classical

namespace PSep

/-! ## 1. Indexed access to the representative tables -/

/-- The cardinality `n` of the arithmetic table of the representative `k`. -/
def pn (k : Fin 230) : ℕ := (Data.repArith k.val).n

/-- The `i`-th element of the arithmetic table of the representative `k`, as a flat `M3`. -/
def elM (k : Fin 230) (i : ℕ) : Data.M3 := (Data.repArith k.val).elems.getD i Data.M3.one

/-- The same element as an integer matrix. -/
def elI (k : Fin 230) (i : ℕ) : IMat := (elM k i).toIMat

/-- The `i`-th numerator vector `z` of the cocycle table of the representative `k`
(`n · τ(A_i) ≡ z_i (mod n)`). -/
def zV (k : Fin 230) (i : ℕ) : Data.V3 := (Data.repZ.getD k.val []).getD i Data.V3.zero

@[simp] theorem pn_def (k : Fin 230) : pn k = (Data.repArith k.val).n := rfl
@[simp] theorem elM_def (k : Fin 230) (i : ℕ) :
    elM k i = (Data.repArith k.val).elems.getD i Data.M3.one := rfl
@[simp] theorem elI_def (k : Fin 230) (i : ℕ) : elI k i = (elM k i).toIMat := rfl
@[simp] theorem zV_def (k : Fin 230) (i : ℕ) :
    zV k i = (Data.repZ.getD k.val []).getD i Data.V3.zero := rfl

/-! ## 2. Flat integer vectors as real vectors -/

/-- A flat integer vector as a real vector. -/
def toRV (v : Data.V3) : Fin 3 → ℝ := toRVec v.toFun

theorem toRV_def (v : Data.V3) : toRV v = toRVec v.toFun := rfl

theorem toRV_inj : Function.Injective toRV := fun _ _ h => Data.V3.toFun_injective (toRVec_injective h)

@[simp] theorem toRV_zero : toRV Data.V3.zero = 0 := by
  funext i; fin_cases i <;> simp [toRV, toRVec, Data.V3.zero, Data.V3.toFun]

@[simp] theorem toRV_add (u v : Data.V3) : toRV (Data.V3.add u v) = toRV u + toRV v := by
  funext i; fin_cases i <;> simp [toRV, toRVec, Data.V3.add, Data.V3.toFun]

@[simp] theorem toRV_sub (u v : Data.V3) : toRV (Data.V3.sub u v) = toRV u - toRV v := by
  funext i; fin_cases i <;> simp [toRV, toRVec, Data.V3.sub, Data.V3.toFun]

@[simp] theorem toRV_neg (v : Data.V3) : toRV (Data.V3.smul (-1) v) = -toRV v := by
  funext i; fin_cases i <;> simp [toRV, toRVec, Data.V3.smul, Data.V3.toFun]

@[simp] theorem toRV_smul (c : ℤ) (v : Data.V3) : toRV (Data.V3.smul c v) = c • toRV v := by
  funext i; fin_cases i <;> simp [toRV, toRVec, Data.V3.smul, Data.V3.toFun]

/-! ## 3. The flat ↔ `Matrix` bridge -/

theorem toIMat_add (A B : Data.M3) : (A.add B).toIMat = A.toIMat + B.toIMat := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Data.M3.toIMat, Data.M3.add, Matrix.add_apply]

theorem toIMat_sub (A B : Data.M3) : (A.sub B).toIMat = A.toIMat - B.toIMat := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Data.M3.toIMat, Data.M3.sub, Matrix.sub_apply]

theorem toIMat_neg (A : Data.M3) : (A.neg).toIMat = -A.toIMat := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Data.M3.toIMat, Data.M3.neg, Matrix.neg_apply]

theorem toIMat_zero : ((⟨0, 0, 0, 0, 0, 0, 0, 0, 0⟩ : Data.M3)).toIMat = 0 := by
  ext i j; fin_cases i <;> fin_cases j <;> simp [Data.M3.toIMat]

theorem toIMat_pow (A : Data.M3) (m : ℕ) : (A.pow m).toIMat = A.toIMat ^ m := by
  induction m with
  | zero => simp [Data.M3.pow, Data.M3.toIMat_one]
  | succ n ih => rw [Data.M3.pow, Data.M3.toIMat_mul, ih, pow_succ']

theorem toIMat_normSum (A : Data.M3) (m : ℕ) : (A.normSum m).toIMat = Nsum A.toIMat m := by
  induction m with
  | zero => simp [Data.M3.normSum, Nsum, toIMat_zero]
  | succ n ih =>
    simp only [Data.M3.normSum, toIMat_add, ih, toIMat_pow, Nsum]
    rw [Finset.sum_range_succ, add_comm]

/-- Columns of a product: `cols (B * N) = (cols N).map (mulV B)`. -/
theorem cols_mulV (B N : Data.M3) : (B.mul N).cols = N.cols.map B.mulV := by
  simp only [Data.M3.cols, Data.M3.mulV, Data.M3.mul, List.map_cons, List.map_nil]

/-- `mulV` commutes with the passage to real vectors. -/
theorem mulV_toRV (A : Data.M3) (v : Data.V3) :
    toRV (A.mulV v) = (toRMat A.toIMat).mulVec (toRV v) := by
  show toRVec (A.mulV v).toFun = (toRMat A.toIMat).mulVec (toRVec v.toFun)
  rw [← Data.M3.toIMat_mulV, mulVec_toRVec]

/-- Membership in the lattice `M ℤ³` is exactly membership in the `ℤ`-span of the columns of
`M` (coefficients are read off a `List ℤ` via `Data.lin`). -/
theorem mem_latImg_iff_cols (M : Data.M3) (v : Data.V3) :
    toRV v ∈ latImg M.toIMat ↔ ∃ cs : List ℤ, Data.lin M.cols cs = v := by
  constructor
  · intro hv
    obtain ⟨w, hw⟩ := mem_latImg.mp hv
    have hw2 : M.toIMat.mulVec w = v.toFun := by
      apply toRVec_injective
      rw [← mulVec_toRVec]
      exact hw
    refine ⟨[w 0, w 1, w 2], ?_⟩
    apply Data.V3.toFun_injective
    have hwl : (fun i : Fin 3 => ([w 0, w 1, w 2] : List ℤ).getD i.val 0) = w := by
      funext i; fin_cases i <;> simp
    rw [← Data.M3.mulVec_getD M [w 0, w 1, w 2], hwl, hw2]
  · rintro ⟨cs, hcs⟩
    obtain ⟨w, hw⟩ := Data.M3.exists_mulVec_of_lin hcs
    refine ⟨w, ?_⟩
    show (toRMat M.toIMat).mulVec (toRVec w) = toRVec v.toFun
    rw [mulVec_toRVec, hw]

/-! ## 4. The order of an `M3` and the order of its `IMat` -/

/-- `List.find?` on `List.range n` returns the *first* satisfying index. -/
theorem find?_range_le : ∀ {n : ℕ} {p : ℕ → Bool} {a b : ℕ},
    (List.range n).find? p = some a → p b = true → b < n → a ≤ b := by
  intro n
  induction n with
  | zero => intro p a b ha _ _; exact absurd ha (by simp)
  | succ n ih =>
    intro p a b ha hb hbn
    rw [List.range_succ_eq_map] at ha
    by_cases hp0 : p 0 = true
    · rw [List.find?_cons_of_pos hp0] at ha
      simp at ha
      omega
    · rw [List.find?_cons_of_neg hp0, List.find?_map] at ha
      cases hfind : List.find? (p ∘ Nat.succ) (List.range n) with
      | none => rw [hfind] at ha; simp at ha
      | some a' =>
        rw [hfind] at ha
        simp only [Option.map_some, Option.some.injEq] at ha
        have ha' : a = a' + 1 := ha.symm
        cases b with
        | zero => exact absurd hb hp0
        | succ b' =>
          have hb' : (p ∘ Nat.succ) b' = true := hb
          have hlt : b' < n := by omega
          have := ih hfind hb' hlt
          omega

/-- If `M3.ord A ≠ 0`, it is the order of `A`. -/
theorem ord_spec {A : Data.M3} (h : A.ord ≠ 0) :
    1 ≤ A.ord ∧ A.ord ≤ 12 ∧ A.pow A.ord = Data.M3.one := by
  have hfind : (List.range 12).find? (fun k => A.pow (k + 1) == Data.M3.one) ≠ none := by
    intro hc
    exact h (by simp [Data.M3.ord, hc])
  obtain ⟨k, hk⟩ := Option.ne_none_iff_exists'.mp hfind
  have hpk : A.pow (k + 1) = Data.M3.one := by
    have := List.find?_some hk
    simpa using this
  have hklt : k < 12 := List.mem_range.mp (List.mem_of_find?_eq_some hk)
  have hval : A.ord = k + 1 := by simp [Data.M3.ord, hk]
  exact ⟨by omega, by omega, by rw [hval]; exact hpk⟩

/-- Minimality of `M3.ord` among the orders in `[1, 12]`. -/
theorem ord_min {A : Data.M3} {m : ℕ} (hm1 : 1 ≤ m) (hm12 : m ≤ 12)
    (hp : A.pow m = Data.M3.one) : A.ord ≤ m := by
  by_cases h0 : A.ord = 0
  · omega
  · have hfind : (List.range 12).find? (fun k => A.pow (k + 1) == Data.M3.one) ≠ none := by
      intro hc
      exact h0 (by simp [Data.M3.ord, hc])
    obtain ⟨k, hk⟩ := Option.ne_none_iff_exists'.mp hfind
    have hval : A.ord = k + 1 := by simp [Data.M3.ord, hk]
    have hb : (fun k => A.pow (k + 1) == Data.M3.one) (m - 1) = true := by
      have hsub : m - 1 + 1 = m := Nat.sub_add_cancel hm1
      simp [hsub, hp]
    have hkb : k ≤ m - 1 := find?_range_le hk hb (by omega)
    omega

/-- For an element of a finite table, `M3.ord` is `mOrd` of the matrix. -/
theorem ord_eq_mOrd {A : Data.M3} (h : A.ord ≠ 0) : A.ord = mOrd A.toIMat := by
  obtain ⟨h1, h12, hp⟩ := ord_spec h
  have hpow : A.toIMat ^ A.ord = 1 := by rw [← toIMat_pow, hp, Data.M3.toIMat_one]
  have hex : ∃ m, 1 ≤ m ∧ A.toIMat ^ m = 1 := ⟨A.ord, h1, hpow⟩
  have hle1 : mOrd A.toIMat ≤ A.ord := mOrd_min hex h1 hpow
  have hm1 : 1 ≤ mOrd A.toIMat := (mOrd_spec hex).1
  have hm12 : mOrd A.toIMat ≤ 12 := le_trans hle1 h12
  have hpow' : A.pow (mOrd A.toIMat) = Data.M3.one := by
    apply Data.M3.toIMat_injective
    rw [toIMat_pow, (mOrd_spec hex).2, Data.M3.toIMat_one]
  exact le_antisymm (ord_min hm1 hm12 hpow') hle1

/-! ## 5. List plumbing -/

/-- A list is the list of its `getD`-values. -/
theorem map_eq_map_getD {α β : Type*} (l : List α) (f : α → β) (d : α) :
    l.map f = (List.range l.length).map (fun i => f (l.getD i d)) := by
  induction l with
  | nil => simp
  | cons a t ih =>
    rw [List.length_cons, List.range_succ_eq_map]
    simp only [List.map_cons, List.map_map, List.getD_cons_zero, ih]
    congr 1

/-! ## 6. Order modulo a lattice -/

/-- `ordInLat` returns the (unique) order, when it exists. -/
theorem ordInLat_eq_of_IsOrdOf {L : AddSubgroup (Fin 3 → ℝ)} {v : Fin 3 → ℝ} {o : ℕ}
    (h : IsOrdOf L v o) : ordInLat L v = o :=
  IsOrdOf_unique (ordInLat_spec ⟨o, h⟩) h

/-! ## 7. `τ`-generic versions of the `pair` invariant -/

/-- The `elem` key `(det, trace, order of v_A)` for a general cocycle `τ`. -/
noncomputable def keyG (τ : IMat → Fin 3 → ℝ) (A : IMat) : ℤ × ℤ × ℕ :=
  (A.det, A.trace, ordInLat (latImg (NZ A)) (vA τ A))

/-- The `fix` bit for a general cocycle `τ`. -/
noncomputable def fixBitG (τ : IMat → Fin 3 → ℝ) (A B : IMat) : Prop :=
  ((toRMat B - 1).mulVec (vA τ A)) ∈ latImg ((B - 1) * NZ A)

/-- The `afix` bit for a general cocycle `τ`. -/
noncomputable def afixBitG (τ : IMat → Fin 3 → ℝ) (A B : IMat) : Prop :=
  ((toRMat B + 1).mulVec (vA τ A)) ∈ latImg ((B + 1) * NZ A)

/-- The six bits of a pair for a general cocycle `τ`, in the `Data.PairCert.bits` order. -/
noncomputable def pairBitsG (τ : IMat → Fin 3 → ℝ) (A B : IMat) : List Bool :=
  [if fixBitG τ A B then true else false, if afixBitG τ A B then true else false,
   if latImg (A - 1) ≤ latImg (B - 1) then true else false,
   if latImg (A + 1) ≤ latImg (B + 1) then true else false,
   if latImg (A - 1) ≤ latImg (B + 1) then true else false,
   if latImg (A + 1) ≤ latImg (B - 1) then true else false]

theorem keyE_eq_keyG (k : Fin 230) (A : IMat) : keyE k A = keyG (sgTau k) A := rfl

theorem fixBit_eq_fixBitG (k : Fin 230) (A B : IMat) : fixBit k A B = fixBitG (sgTau k) A B := rfl

theorem afixBit_eq_afixBitG (k : Fin 230) (A B : IMat) :
    afixBit k A B = afixBitG (sgTau k) A B := rfl

theorem pairBits_eq_pairBitsG (k : Fin 230) (A B : IMat) :
    pairBits k A B = pairBitsG (sgTau k) A B := rfl

/-! ## 8. A matrix inverse fact -/

theorem invMat_invMat {U : IMat} (hU : IsUnit U.det) : invMat (invMat U) = U := by
  calc invMat (invMat U) = invMat (invMat U) * 1 := (mul_one _).symm
    _ = invMat (invMat U) * (invMat U * U) := by rw [invMat_mul hU]
    _ = invMat (invMat U) * invMat U * U := (mul_assoc _ _ _).symm
    _ = 1 * U := by rw [invMat_mul (isUnit_det_invMat hU)]
    _ = U := one_mul U


/-- `Data.vOf` at representative `k` (as an element of `Fin 230`). -/
def vOfK (k : Fin 230) (i : ℕ) : Data.V3 := Data.vOf k.val i

/-- The cheap key `(det, trace, order)` of element `i` of representative `k`. -/
def ekeyK (k : Fin 230) (i : ℕ) : ℤ × ℤ × ℕ := Data.ekey k.val i

/-- `N_A` of element `i` of representative `k`, in the `Data.M3` encoding. -/
def normK (k : Fin 230) (i : ℕ) : Data.M3 := Data.normOf (elM k i)

@[simp] theorem vOfK_def (k : Fin 230) (i : ℕ) :
    vOfK k i = Data.V3.ediv (Data.M3.mulV (Data.normOf (elM k i)) (zV k i)) (pn k) := rfl

@[simp] theorem ekeyK_def (k : Fin 230) (i : ℕ) :
    ekeyK k i = (Data.M3.det (elM k i), Data.M3.trace (elM k i),
      ((Data.elemTab.getD k.val []).getD i default).o) := rfl

@[simp] theorem normK_def (k : Fin 230) (i : ℕ) : normK k i = Data.normOf (elM k i) := rfl

/-- For an `M3` whose `ord` is non-zero, `normOf` is `N_A` in matrix form. -/
theorem normOf_toIMat (A : Data.M3) (h : A.ord ≠ 0) :
    (Data.normOf A).toIMat = NZ A.toIMat := by
  rw [Data.normOf, ord_eq_mOrd h, toIMat_normSum]
  rfl

/-- `toRMat` commutes with `-`. -/
theorem toRMat_sub (A B : IMat) : toRMat (A - B) = toRMat A - toRMat B := by
  ext i j; simp [toRMat, Matrix.sub_apply]

theorem toRMat_add (A B : IMat) : toRMat (A + B) = toRMat A + toRMat B := by
  ext i j; simp [toRMat, Matrix.add_apply]

theorem toRMat_neg (A : IMat) : toRMat (-A) = -toRMat A := by
  ext i j; simp [toRMat, Matrix.neg_apply]

theorem toRMat_one : toRMat (1 : IMat) = 1 := by
  ext i j; simp [toRMat, Matrix.one_apply]


/-- Soundness of a `Data.SpanCert`: the certificate bit tells whether the vector lies in the
lattice spanned by the columns of `M`. -/
theorem spanCert_bit (M : Data.M3) (v : Data.V3) (c : Data.SpanCert)
    (h : Data.SpanCert.chk M.cols v c = true) :
    (c.bit = true ↔ toRV v ∈ latImg M.toIMat) := by
  cases c with
  | yes cs =>
    exact ⟨fun _ => (mem_latImg_iff_cols M v).mpr ⟨cs, Data.SpanCert.chk_yes h⟩, fun _ => rfl⟩
  | no φ m =>
    refine ⟨fun hf => False.elim (Bool.false_ne_true hf), fun hmem => ?_⟩
    rw [mem_latImg_iff_cols] at hmem
    obtain ⟨cs, hcs⟩ := hmem
    exfalso
    exact Data.SpanCert.chk_no h ⟨cs, hcs⟩

end PSep

end Work.SGsep
