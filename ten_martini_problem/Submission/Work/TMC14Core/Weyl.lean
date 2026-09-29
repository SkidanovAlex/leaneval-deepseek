import Mathlib
import Submission.Work.TMC14Core.Rat

/-!
# TMC14Core: the Weyl (clock-and-shift) model of the Bloch matrix

For `q : ℕ`, `p : ℤ`, `θ k : ℝ` we define the two `q × q` matrices

* `wU q k`  : the cyclic shift `(U x)_n = x_{n+1}` (`n < q-1`), `(U x)_{q-1} = β x_0`
  with `β = e^{2πik}`,
* `wV p q θ`: the diagonal `diag(e^{2πi(θ+np/q)})`.

They satisfy `U V = ω V U` with `ω = om p q = e^{2πip/q}`, and
`blochMat p q lam θ k = U + U† + λ • (V + V†)`.
-/

open Matrix
open scoped ComplexConjugate

noncomputable section

namespace Work.TMC14Core

/-- `wPh x = e^{2πix}` (for real `x`). -/
def wPh (x : ℝ) : ℂ := Complex.exp (2 * Real.pi * Complex.I * (x : ℂ))

theorem wPh_add (a b : ℝ) : wPh (a + b) = wPh a * wPh b := by
  rw [wPh, wPh, wPh, ← Complex.exp_add]
  congr 1
  push_cast
  ring

theorem wPh_zero : wPh 0 = 1 := by
  rw [wPh]
  norm_num

theorem wPh_int (n : ℤ) : wPh (n : ℝ) = 1 := by
  rw [wPh]
  have h : 2 * (Real.pi : ℂ) * Complex.I * ((n : ℝ) : ℂ)
      = (n : ℂ) * (2 * (Real.pi : ℂ) * Complex.I) := by push_cast; ring
  rw [h, Complex.exp_int_mul_two_pi_mul_I]

theorem wPh_norm (x : ℝ) : ‖wPh x‖ = 1 := by
  rw [wPh, Complex.norm_exp]
  have h : (2 * (Real.pi : ℂ) * Complex.I * (x : ℂ)) = (((2 * Real.pi * x : ℝ)) : ℂ) * Complex.I := by
    push_cast; ring
  rw [h, Complex.mul_I_re]
  simp

theorem wPh_conj (x : ℝ) : star (wPh x) = wPh (-x) := by
  have h1 : 2 * (Real.pi : ℂ) * Complex.I * (x : ℂ) = (((2 * Real.pi * x : ℝ)) : ℂ) * Complex.I := by
    push_cast; ring
  have h2 : 2 * (Real.pi : ℂ) * Complex.I * ((-x : ℝ) : ℂ)
      = (((-(2 * Real.pi * x) : ℝ)) : ℂ) * Complex.I := by push_cast; ring
  rw [wPh, wPh, h1, h2]
  simp only [Complex.star_def]
  rw [← Complex.exp_conj]
  congr 1
  rw [map_mul, Complex.conj_I, Complex.conj_ofReal]
  push_cast
  ring

theorem wPh_add_conj (x : ℝ) :
    wPh x + star (wPh x) = ((2 * Real.cos (2 * Real.pi * x) : ℝ) : ℂ) := by
  rw [wPh_conj, wPh, wPh]
  have h1 : 2 * (Real.pi : ℂ) * Complex.I * (x : ℂ) = (((2 * Real.pi * x : ℝ)) : ℂ) * Complex.I := by
    push_cast; ring
  have h2 : 2 * (Real.pi : ℂ) * Complex.I * ((-x : ℝ) : ℂ)
      = (((-(2 * Real.pi * x) : ℝ)) : ℂ) * Complex.I := by push_cast; ring
  rw [h1, h2, Complex.exp_ofReal_mul_I, Complex.exp_ofReal_mul_I]
  simp only [Real.cos_neg, Real.sin_neg, Complex.ofReal_neg]
  push_cast
  ring

theorem om_eq_wPh (p : ℤ) (q : ℕ) : om p q = wPh ((p : ℝ) / (q : ℝ)) := by
  rw [wPh, om]
  congr 1
  push_cast
  ring

/-- `β = e^{2πik}`: the corner phase of the cyclic shift. -/
def wShiftBeta (k : ℝ) : ℂ := wPh k

theorem wShiftBeta_norm (k : ℝ) : ‖wShiftBeta k‖ = 1 := wPh_norm k

/-- The cyclic shift `(U x)_n = x_{n+1}` for `n < q-1` and `(U x)_{q-1} = β x_0`. -/
def wU (q : ℕ) (k : ℝ) : Matrix (Fin q) (Fin q) ℂ :=
  fun i j => if (i.val + 1) % q = j.val then (if i.val + 1 < q then 1 else wShiftBeta k) else 0

@[simp] theorem wU_apply (q : ℕ) (k : ℝ) (i j : Fin q) :
    wU q k i j = if (i.val + 1) % q = j.val then (if i.val + 1 < q then 1 else wShiftBeta k) else 0 := rfl

/-- The diagonal entries of `V`: `wVd p q θ i = e^{2πi(θ+ip/q)}`. -/
def wVd (p : ℤ) (q : ℕ) (θ : ℝ) (i : Fin q) : ℂ :=
  wPh (θ + (i.val : ℝ) * (p : ℝ) / (q : ℝ))

/-- `V = diag(e^{2πi(θ+np/q)})`. -/
def wV (p : ℤ) (q : ℕ) (θ : ℝ) : Matrix (Fin q) (Fin q) ℂ :=
  Matrix.diagonal (wVd p q θ)

@[simp] theorem wV_apply (p : ℤ) (q : ℕ) (θ : ℝ) (i j : Fin q) :
    wV p q θ i j = if i = j then wVd p q θ i else 0 := by
  rw [wV, Matrix.diagonal_apply]

theorem wVd_norm (p : ℤ) (q : ℕ) (θ : ℝ) (i : Fin q) : ‖wVd p q θ i‖ = 1 := wPh_norm _

theorem wVd_add_conj (p : ℤ) (q : ℕ) (θ : ℝ) (i : Fin q) :
    wVd p q θ i + star (wVd p q θ i)
      = ((2 * Real.cos (2 * Real.pi * (θ + (i.val : ℝ) * (p : ℝ) / (q : ℝ))) : ℝ) : ℂ) :=
  wPh_add_conj _

theorem wVd_mul_conj (p : ℤ) (q : ℕ) (θ : ℝ) (i : Fin q) :
    wVd p q θ i * star (wVd p q θ i) = 1 := by
  rw [wVd, wPh_conj, wPh, wPh, ← Complex.exp_add]
  have h : 2 * (Real.pi : ℂ) * Complex.I * ((θ + (i.val : ℝ) * (p : ℝ) / (q : ℝ) : ℝ) : ℂ)
      + 2 * (Real.pi : ℂ) * Complex.I * ((-(θ + (i.val : ℝ) * (p : ℝ) / (q : ℝ)) : ℝ) : ℂ) = 0 := by
    push_cast; ring
  rw [h, Complex.exp_zero]

/-- `wVd p q θ j = ω * wVd p q θ i` when `j = i+1 (mod q)`. -/
theorem wVd_succ (p : ℤ) (q : ℕ) (θ : ℝ) (hq : 0 < q) (i j : Fin q)
    (h : j.val = (i.val + 1) % q) : wVd p q θ j = om p q * wVd p q θ i := by
  by_cases hlt : i.val + 1 < q
  · have hj : j.val = i.val + 1 := by rw [h, Nat.mod_eq_of_lt hlt]
    rw [wVd, wVd, om_eq_wPh, ← wPh_add, hj]
    congr 1
    push_cast
    field_simp
    ring
  · have hi : i.val + 1 = q := by omega
    have hj : j.val = 0 := by rw [h, hi]; simp
    have h1 : (i.val : ℝ) + 1 = (q : ℝ) := by exact_mod_cast hi
    have h2 : (p : ℝ) / (q : ℝ) + (i.val : ℝ) * (p : ℝ) / (q : ℝ) = (p : ℝ) := by
      have hpos : ((i.val : ℝ) + 1) ≠ 0 := by positivity
      rw [← h1]
      field_simp
      ring
    have harg : (p : ℝ) / (q : ℝ) + (θ + (i.val : ℝ) * (p : ℝ) / (q : ℝ)) = θ + (p : ℝ) := by
      linarith [h2]
    rw [wVd, wVd, om_eq_wPh, ← wPh_add, hj, harg, wPh_add θ (p : ℝ), wPh_int p, mul_one]
    simp



theorem wShiftBeta_mul_star (k : ℝ) : wShiftBeta k * star (wShiftBeta k) = 1 := by
  rw [wShiftBeta, wPh_conj, wPh, wPh, ← Complex.exp_add]
  have h : 2 * (Real.pi : ℂ) * Complex.I * (k : ℂ)
      + 2 * (Real.pi : ℂ) * Complex.I * ((-k : ℝ) : ℂ) = 0 := by
    push_cast; ring
  rw [h, Complex.exp_zero]

theorem wV_mem_unitaryGroup (p : ℤ) (q : ℕ) (θ : ℝ) :
    wV p q θ ∈ Matrix.unitaryGroup (Fin q) ℂ := by
  rw [Matrix.mem_unitaryGroup_iff]
  have hstar : star (wV p q θ) = Matrix.diagonal (fun i => star (wVd p q θ i)) := by
    rw [Matrix.star_eq_conjTranspose, wV, Matrix.diagonal_conjTranspose]
    congr 1
  rw [hstar, wV]
  ext i j
  rw [Matrix.diagonal_mul, Matrix.diagonal_apply, Matrix.one_apply]
  by_cases hij : i = j
  · subst hij; rw [if_pos rfl, if_pos rfl]; exact wVd_mul_conj p q θ i
  · rw [if_neg hij, if_neg hij, mul_zero]

theorem wU_mem_unitaryGroup (q : ℕ) (k : ℝ) (hq : 0 < q) :
    wU q k ∈ Matrix.unitaryGroup (Fin q) ℂ := by
  rw [Matrix.mem_unitaryGroup_iff, Matrix.star_eq_conjTranspose]
  ext i j
  rw [Matrix.mul_apply, Matrix.one_apply]
  set l₀ : Fin q := ⟨(j.val + 1) % q, Nat.mod_lt _ hq⟩ with hl₀def
  have hl₀ : l₀.val = (j.val + 1) % q := rfl
  rw [Finset.sum_eq_single l₀]
  · simp only [Matrix.conjTranspose_apply, wU_apply]
    rw [if_pos hl₀]
    have hcond : ((i.val + 1) % q = l₀.val) ↔ i = j := by
      rw [hl₀]
      constructor
      · intro hh
        apply Fin.ext
        have hi : i.val < q := i.isLt
        have hj : j.val < q := j.isLt
        rcases Nat.lt_or_ge (i.val + 1) q with h1 | h1
        · rw [Nat.mod_eq_of_lt h1] at hh
          rcases Nat.lt_or_ge (j.val + 1) q with h2 | h2
          · rw [Nat.mod_eq_of_lt h2] at hh; omega
          · rw [show (j.val + 1) % q = 0 from by
                rw [show j.val + 1 = q from by omega, Nat.mod_self]] at hh
            omega
        · rw [show (i.val + 1) % q = 0 from by
              rw [show i.val + 1 = q from by omega, Nat.mod_self]] at hh
          rcases Nat.lt_or_ge (j.val + 1) q with h2 | h2
          · rw [Nat.mod_eq_of_lt h2] at hh; omega
          · rw [show (j.val + 1) % q = 0 from by
                rw [show j.val + 1 = q from by omega, Nat.mod_self]] at hh
            omega
      · intro hh; rw [hh]
    by_cases hij : i = j
    · subst hij
      rw [if_pos (hcond.mpr rfl)]
      rw [if_pos rfl]
      split_ifs with hlt
      · simp
      · exact wShiftBeta_mul_star k
    · rw [if_neg hij, if_neg (fun hh => hij (hcond.mp hh)), zero_mul]
  · intro l _ hl
    simp only [Matrix.conjTranspose_apply, wU_apply]
    have hne : (j.val + 1) % q ≠ l.val := by
      intro hh
      exact hl (Fin.ext (by rw [hl₀]; exact hh.symm))
    rw [if_neg hne, star_zero, mul_zero]
  · intro h; exact absurd (Finset.mem_univ l₀) h

theorem wU_mul_wV (p : ℤ) (q : ℕ) (θ k : ℝ) :
    wU q k * wV p q θ = om p q • (wV p q θ * wU q k) := by
  rcases q with _ | q'
  · ext i; exact Fin.elim0 i
  · ext i j
    rw [wV]
    rw [Matrix.mul_diagonal, Matrix.smul_apply, smul_eq_mul, Matrix.diagonal_mul]
    by_cases h : (i.val + 1) % (q' + 1) = j.val
    · rw [wU_apply, if_pos h]
      have hidx : wVd p (q' + 1) θ j = om p (q' + 1) * wVd p (q' + 1) θ i :=
        wVd_succ p (q' + 1) θ (Nat.succ_pos q') i j h.symm
      by_cases hlt : i.val + 1 < q' + 1
      · rw [if_pos hlt, one_mul, hidx]; ring
      · rw [if_neg hlt, hidx]; ring
    · rw [wU_apply, if_neg h]; simp

/-- The four Weyl letters: `(true,true)=U`, `(true,false)=U†`, `(false,true)=V`, `(false,false)=V†`. -/
def letterOf (p : ℤ) (q : ℕ) (θ k : ℝ) (x : Bool × Bool) : Matrix (Fin q) (Fin q) ℂ :=
  if x.1 then (if x.2 then wU q k else (wU q k)ᴴ)
  else (if x.2 then wV p q θ else (wV p q θ)ᴴ)

/-- The matrix product of the letters of the word `f`, in the order of `Fin n`. -/
def wordProd (p : ℤ) (q : ℕ) (θ k : ℝ) (n : ℕ) (f : Fin n → Bool × Bool) : Matrix (Fin q) (Fin q) ℂ :=
  ((List.ofFn f).map (fun x => letterOf p q θ k x)).prod

/-- Number of coordinates of `f` whose letter equals `(b,c)`. -/
def cnt (b c : Bool) (n : ℕ) (f : Fin n → Bool × Bool) : ℕ :=
  ((Finset.univ : Finset (Fin n)).filter (fun i => f i = (b, c))).card

/-- Number of `U`-before-`V` pairs of a word over the two letters
`U = (true,true)`, `V = (false,true)` (used for the phase of the normal form). -/
def invCount (n : ℕ) (f : Fin n → Bool × Bool) : ℕ :=
  ((Finset.univ : Finset (Fin n)).filter (fun i => f i = (true, true))).sum
    (fun i => ((Finset.univ : Finset (Fin n)).filter
      (fun j => f j = (false, true) ∧ i.val < j.val)).card)

end Work.TMC14Core
