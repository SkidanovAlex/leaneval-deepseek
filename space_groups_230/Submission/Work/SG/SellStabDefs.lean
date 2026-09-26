import Mathlib
import Submission.Work.SG.Defs
import Submission.Work.SG.Data.SellCheck

/-! Shared definitions and bridge lemmas for `conj_to_arithRep` (`Submission/Work/SG/DESIGN.md`,
node 9).  Nothing here is `sorry`ed; the file is the interface that the delegated certificate
pieces and the main assembly import. -/

namespace Work.SG

open LeanEval.Geometry.SpaceGroupsProblem

open scoped Matrix

namespace CZ

/-! ### The Selling certificate data of a graph -/

/-- The Selling data of support graph `i`. -/
abbrev Sof (i : Fin 6) : Data.SellData := Data.sellData.getD i.val default

/-! ### Bridges between the flat types `Data.V3` / `Data.M3` and `Fin 3 → ℤ` / `IMat` -/

/-- `V3` read off a function. -/
def ofFun (f : Fin 3 → ℤ) : Data.V3 := ⟨f 0, f 1, f 2⟩

theorem ofFun_toFun (f : Fin 3 → ℤ) : (ofFun f).toFun = f := by
  funext k; fin_cases k <;> rfl

theorem toFun_inj : Function.Injective Data.V3.toFun := by
  intro a b h
  have h0 := congrFun h 0
  have h1 := congrFun h 1
  have h2 := congrFun h 2
  simp only [Data.V3.toFun] at h0 h1 h2
  cases a; cases b; simp_all

/-- The `M3` of an integer matrix. -/
def toM3 (A : IMat) : Data.M3 :=
  ⟨A 0 0, A 0 1, A 0 2, A 1 0, A 1 1, A 1 2, A 2 0, A 2 1, A 2 2⟩

theorem toM3_toIMat (A : IMat) : (toM3 A).toIMat = A := by
  ext i j; fin_cases i <;> fin_cases j <;> rfl

theorem toIMat_toM3 (A : Data.M3) : toM3 A.toIMat = A := by
  cases A; rfl

theorem toIMat_inj : Function.Injective Data.M3.toIMat := by
  intro A B h
  have h1 : A.a = B.a := by have := congrFun (congrFun h 0) 0; simpa [Data.M3.toIMat] using this
  have h2 : A.b = B.b := by have := congrFun (congrFun h 0) 1; simpa [Data.M3.toIMat] using this
  have h3 : A.c = B.c := by have := congrFun (congrFun h 0) 2; simpa [Data.M3.toIMat] using this
  have h4 : A.d = B.d := by have := congrFun (congrFun h 1) 0; simpa [Data.M3.toIMat] using this
  have h5 : A.e = B.e := by have := congrFun (congrFun h 1) 1; simpa [Data.M3.toIMat] using this
  have h6 : A.f = B.f := by have := congrFun (congrFun h 1) 2; simpa [Data.M3.toIMat] using this
  have h7 : A.g = B.g := by have := congrFun (congrFun h 2) 0; simpa [Data.M3.toIMat] using this
  have h8 : A.h = B.h := by have := congrFun (congrFun h 2) 1; simpa [Data.M3.toIMat] using this
  have h9 : A.i = B.i := by have := congrFun (congrFun h 2) 2; simpa [Data.M3.toIMat] using this
  cases A; cases B; simp_all

theorem toIMat_mul (A B : Data.M3) : (Data.M3.mul A B).toIMat = A.toIMat * B.toIMat := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Data.M3.toIMat, Data.M3.mul, Matrix.mul_apply, Fin.sum_univ_three]

theorem toIMat_one : Data.M3.one.toIMat = (1 : IMat) := by
  ext i j; fin_cases i <;> fin_cases j <;> rfl

theorem toIMat_det (A : Data.M3) : A.toIMat.det = A.det := by
  simp [Data.M3.toIMat, Data.M3.det, Matrix.det_fin_three]
  ring

theorem toIMat_mulV (A : Data.M3) (v : Data.V3) :
    (Data.M3.mulV A v).toFun = A.toIMat.mulVec v.toFun := by
  funext k
  fin_cases k <;>
    simp [Data.M3.toIMat, Data.M3.mulV, Data.V3.toFun, Matrix.mulVec, dotProduct,
      Fin.sum_univ_three]

/-! ### Index-level vocabulary for a certificate table -/

/-- The `a`-th element of the stabiliser list (`1` out of range). -/
def mat (S : Data.SellData) (a : ℕ) : Data.M3 := S.stab.getD a Data.M3.one

/-- The index of the product `mat a * mat b` in the table. -/
def gmul (S : Data.SellData) (a b : ℕ) : ℕ := (S.mul.getD a []).getD b 0

/-- The set of indices `a < |stab|` with the `a`-th bit of the mask `T` set. -/
def bitsOf (S : Data.SellData) (T : ℕ) : Finset ℕ :=
  (List.range S.stab.length).toFinset.filter (fun a => T.testBit a)

/-- One step of the coset-representative recursion of a join certificate. -/
def joinStep (S : Data.SellData) (rs : List ℕ) (p : ℕ × ℕ) : List ℕ :=
  rs ++ [(S.mul.getD (rs.getD p.1 0) []).getD p.2 0]

/-- The coset representatives `r₀ = 1`, `r_{q+1} = r_{cos[q].1} * cos[q].2`. -/
def joinReps (S : Data.SellData) (cos : List (ℕ × ℕ)) : List ℕ :=
  cos.foldl (joinStep S) [S.one]


/-! ### Bitmask / index-set lemmas -/

theorem mem_bitsOf {S : Data.SellData} {T a : ℕ} :
    a ∈ bitsOf S T ↔ a < S.stab.length ∧ T.testBit a = true := by
  simp [bitsOf, List.mem_toFinset, List.mem_range]

theorem bitsOf_mono {S : Data.SellData} {T T' : ℕ}
    (h : ∀ a, T.testBit a = true → T'.testBit a = true) : bitsOf S T ⊆ bitsOf S T' := by
  intro a ha
  rw [mem_bitsOf] at ha ⊢
  exact ⟨ha.1, h a ha.2⟩

theorem testBit_lor_true {T T' a : ℕ} (h : (T ||| T').testBit a = true) :
    T.testBit a = true ∨ T'.testBit a = true := by
  rw [Nat.testBit_lor] at h
  exact Bool.or_eq_true_iff.mp h

theorem testBit_lt_two_pow {T N a : ℕ} (hT : T < 2 ^ N) (h : T.testBit a = true) : a < N := by
  by_contra hc
  have hNa : N ≤ a := by omega
  have hTa : T < 2 ^ a := lt_of_lt_of_le hT (Nat.pow_le_pow_right (by norm_num) hNa)
  rw [Nat.testBit_lt_two_pow hTa] at h
  exact Bool.noConfusion h

theorem testBit_shiftLeft_one {n a : ℕ} : (1 <<< n).testBit a = decide (n = a) := by
  rw [Nat.one_shiftLeft, Nat.testBit_two_pow]

theorem mem_bitsOf_one {S : Data.SellData} {n : ℕ} (hn : n < S.stab.length) :
    bitsOf S (1 <<< n) = {n} := by
  ext a
  rw [mem_bitsOf, Finset.mem_singleton, testBit_shiftLeft_one]
  constructor
  · rintro ⟨-, h⟩
    exact (decide_eq_true_eq.mp h).symm
  · rintro rfl
    exact ⟨hn, by simp⟩

/-- Out-of-range mask bits are `false`. -/
theorem testBit_eq_false_of_le {T N a : ℕ} (hT : T < 2 ^ N) (h : N ≤ a) :
    T.testBit a = false :=
  Nat.testBit_lt_two_pow (lt_of_lt_of_le hT (Nat.pow_le_pow_right (by norm_num) h))

end CZ

end Work.SG
