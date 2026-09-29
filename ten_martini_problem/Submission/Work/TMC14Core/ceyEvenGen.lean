import Mathlib
import Submission.Work.TMC14Core.ceyTraceOdd
import Submission.Work.TMC14Core.Assembly
import Submission.Work.TMC14Core.ceyDerivBound
import Submission.Work.TMC14Core.adjugateHermitianRankOne
import Submission.Work.TMC14Core.traceUnitaryLe
import Submission.Work.TMC14Core.chamCoef_norm
import Submission.Work.TMC14Core.ceyEvenAux.countEven
import Submission.Work.TMC14Core.InvSumF
import Submission.Work.TMC14Core.ceyEvenAux.discEvalIm
import Submission.Work.TMC14Core.ceyEvenAux.charpolyDerivAdjHerm

/-!
# `Work.TMC14Core.ceyEvenGen`

The even-`q` (`q = 2m+2`) Choi--Elliott--Yui trace identity and the resulting derivative
lower bound `q λ^m |a| ≤ ‖Δ'(a)‖`, valid for **every** `λ > 0`.

For `B = wB p q lam θ k` and `W = (U†)^m (V†)^m` one has

* `tr (B^n * W) = 0` for `n ≤ 2m+1`, `n ≠ 2m`,
* `tr (B^(2m) * W) = q λ^m * wordSum (om p q) (2m) m`, and `‖wordSum …‖ ≥ 1`,

whence `tr (adjugate (z - B) * W) = z * tr (B^(2m) * W)` (the coefficient of `X^(q-1)`
of the characteristic polynomial is `-tr B = 0`), and evaluating at an eigenvalue `a` of `B`
gives `q λ^m |a| ≤ ‖tr (adjugate (a - B) * W)‖ ≤ ‖(B.charpoly).derivative.eval a‖ = ‖Δ'(a)‖`.

This is the even-`q` analogue of `ceyTraceOdd` / `ceyOddDiscDeriv`, kept in the sub-namespace
`ceyEvenGen`.
-/

open Matrix Polynomial

noncomputable section

namespace Work.TMC14Core
namespace ceyEvenGen

/-! ## The norm of the word sum `wordSum ω (2m) m` -/

open Finset


/-! ## Elementary facts about `ω = om p q` -/

/-- `‖om p q‖ = 1`. -/
theorem om_norm (p : ℤ) (q : ℕ) : ‖om p q‖ = 1 := by
  rw [om_eq_wPh]
  exact wPh_norm _

/-- For `q = 2m+2` and `gcd(p, q) = 1` the primitive `q`-th root of unity `om p q`
satisfies `(om p q)^{m+1} = -1` (it is a square root of `ω^q = 1`, and it is not `1`
because `q ∤ m+1`). -/
theorem omPowSuccNegOne (p : ℤ) (q m : ℕ) (hm : q = 2*m+2) (hpq : Nat.Coprime p.natAbs q) :
    (om p q) ^ (m+1) = -1 := by
  have hq : 0 < q := by omega
  have hsq : ((om p q) ^ (m+1)) ^ 2 = 1 := by
    rw [← pow_mul, show (m+1) * 2 = q from by omega]
    exact om_pow_q' p q
  rcases (sq_eq_one_iff.mp hsq) with h | h
  · exfalso
    have hd : q ∣ (m+1) := (om_pow_eq_one_iff p q hpq hq (m+1)).mp h
    have hle : q ≤ m+1 := Nat.le_of_dvd (by omega) hd
    omega
  · exact h

/-! ## Reindexing `Dprod` and `Qprod` as products over `Finset.range` -/

/-- `Dprod ω m = ∏_{k<m} (1 - ω^{k+1})`. -/
theorem Dprod_range (ω : ℂ) (m : ℕ) :
    Dprod ω m = ∏ k ∈ Finset.range m, (1 - ω^(k+1)) := by
  induction m with
  | zero => simp [Dprod]
  | succ m ih =>
    rw [Dprod_succ, ih, Finset.prod_range_succ]
    ring

/-- `Qprod ω m m = ∏_{k<m} (1 - ω^{m+1+k})`. -/
theorem Qprod_range (ω : ℂ) (m : ℕ) :
    Qprod ω m m = ∏ k ∈ Finset.range m, (1 - ω^(m+1+k)) := by
  rw [Qprod, ← Finset.Ico_add_one_right_eq_Icc (1:ℕ) m,
    Finset.prod_Ico_eq_prod_range (fun k => (1 - ω^(m+k))) 1 (m+1)]
  simp only [Nat.add_sub_cancel, Nat.add_assoc]

/-! ## The reflection of `Qprod ω m m` for `ω^(2m+2) = 1` -/

/-- **Reflection of `Qprod`.**  For `ω^(2m+2) = 1` the diagonal product `Qprod ω m m`
can be reflected about the index `m+1`: using `ω^{m+1+k}·ω^{m+1-k} = ω^{2m+2} = 1` one has
`1 - ω^{m+1+k} = -ω^{m+1+k}(1 - ω^{m+1-k})`, and the index reversal `k ↦ m-1-k`
turns `∏_{k<m}(1 - ω^{m+1-k})` into `∏_{k<m}(1 - ω^{k+2})`. -/
theorem QprodReflectEven (ω : ℂ) (m : ℕ) (hω : ω^(2*m+2) = 1) :
    Qprod ω m m = (-1)^m * ω^(∑ k ∈ Finset.range m, (m+1+k)) *
      ∏ k ∈ Finset.range m, (1 - ω^(k+2)) := by
  have hterm : ∀ k ∈ Finset.range m,
      (1 - ω^(m+1+k)) = -ω^(m+1+k) * (1 - ω^(m+1-k)) := by
    intro k hk
    have hk' : k < m := Finset.mem_range.mp hk
    have hmul : ω^(m+1+k) * ω^(m+1-k) = 1 := by
      rw [← pow_add]
      have hsum : m+1+k + (m+1-k) = 2*m+2 := by omega
      rw [hsum, hω]
    have h' : ω^(m+1+k) * (1 - ω^(m+1-k)) = ω^(m+1+k) - 1 := by
      rw [mul_sub, mul_one, hmul]
    have h'' : -ω^(m+1+k) * (1 - ω^(m+1-k)) = 1 - ω^(m+1+k) := by
      have e : -ω^(m+1+k) * (1 - ω^(m+1-k))
          = -(ω^(m+1+k) * (1 - ω^(m+1-k))) := by ring
      rw [e, h']; ring
    exact h''.symm
  have hstep : ∏ k ∈ Finset.range m, (1 - ω^(m+1+k))
      = ∏ k ∈ Finset.range m, (-ω^(m+1+k) * (1 - ω^(m+1-k))) :=
    Finset.prod_congr rfl hterm
  have hrefl : ∏ k ∈ Finset.range m, (1 - ω^(m+1-k))
      = ∏ k ∈ Finset.range m, (1 - ω^(k+2)) := by
    rw [← Finset.prod_range_reflect (fun j => (1 - ω^(j+2))) m]
    refine Finset.prod_congr rfl (fun j hj => ?_)
    have hjj : j < m := Finset.mem_range.mp hj
    have he : (m - 1 - j) + 2 = m + 1 - j := by omega
    rw [he]
  rw [Qprod_range, hstep, Finset.prod_mul_distrib, Finset.prod_neg, Finset.card_range,
    Finset.prod_pow_eq_pow_sum, hrefl]

/-! ## Telescoping the two range products -/

/-- `(1-ω)·∏_{k<m}(1-ω^{k+2}) = (1-ω^{m+1})·∏_{k<m}(1-ω^{k+1})`: both sides are
`∏_{k=1}^{m+1}(1-ω^k)` with the first or the last factor singled out. -/
theorem telescope (ω : ℂ) (m : ℕ) :
    (1 - ω) * (∏ k ∈ Finset.range m, (1 - ω^(k+2))) =
      (1 - ω^(m+1)) * (∏ k ∈ Finset.range m, (1 - ω^(k+1))) := by
  induction m with
  | zero => simp
  | succ m ih =>
    rw [Finset.prod_range_succ (fun k => (1 - ω^(k+2))) m,
        Finset.prod_range_succ (fun k => (1 - ω^(k+1))) m, ← mul_assoc, ih]
    ring

/-! ## The closed form of `wordSum ω (2m) m`, multiplied by `1 - ω` -/

/-- For `ω^(2m+2) = 1` and `ω^j ≠ 1` for `1 ≤ j ≤ m`,
`wordSum ω (2m) m · (1 - ω) = (-1)^m · ω^{∑_{k<m}(m+1+k)} · (1 - ω^{m+1})`. -/
theorem wordSum_mul_one_sub (ω : ℂ) (m : ℕ) (hω : ω^(2*m+2) = 1)
    (hne : ∀ j : ℕ, 1 ≤ j → j ≤ m → ω^j ≠ 1) :
    wordSum ω (2*m) m * (1 - ω) =
      (-1)^m * ω^(∑ k ∈ Finset.range m, (m+1+k)) * (1 - ω^(m+1)) := by
  have hH := Hh_eq ω m m
  rw [show m + m = 2*m from by omega] at hH
  rw [Dprod_range, QprodReflectEven ω m hω] at hH
  have htel := telescope ω m
  have hP : (∏ k ∈ Finset.range m, (1 - ω^(k+1))) ≠ 0 := by
    rw [Finset.prod_ne_zero_iff]
    intro k hk
    have hk' : k < m := Finset.mem_range.mp hk
    exact sub_ne_zero.mpr (Ne.symm (hne (k+1) (by omega) (by omega)))
  refine mul_left_cancel₀ hP ?_
  rw [← mul_assoc, hH]
  have hre : ((-1)^m * ω^(∑ k ∈ Finset.range m, (m+1+k)) *
        (∏ k ∈ Finset.range m, (1 - ω^(k+2)))) * (1 - ω)
      = (-1)^m * ω^(∑ k ∈ Finset.range m, (m+1+k)) *
        ((1 - ω) * (∏ k ∈ Finset.range m, (1 - ω^(k+2)))) := by ring
  rw [hre, htel]
  ring

theorem wordSumNormGeOne (p : ℤ) (q m : ℕ) (hm : q = 2*m+2) (hpq : Nat.Coprime p.natAbs q) :
    1 ≤ ‖wordSum (om p q) (2*m) m‖ := by
  have hq : 0 < q := by omega
  have hω : (om p q)^(2*m+2) = 1 := by rw [← hm]; exact om_pow_q' p q
  have hne : ∀ j : ℕ, 1 ≤ j → j ≤ m → (om p q)^j ≠ 1 := by
    intro j hj1 hjm h
    have hd : q ∣ j := (om_pow_eq_one_iff p q hpq hq j).mp h
    have hle : q ≤ j := Nat.le_of_dvd (by omega) hd
    omega
  have hmain := wordSum_mul_one_sub (om p q) m hω hne
  have hneg := omPowSuccNegOne p q m hm hpq
  have hωne : (1 : ℂ) - om p q ≠ 0 := by
    intro h0
    have hone : om p q = 1 := (sub_eq_zero.mp h0).symm
    have hd : q ∣ 1 := (om_pow_eq_one_iff p q hpq hq 1).mp (by simpa using hone)
    have hle : q ≤ 1 := Nat.le_of_dvd (by norm_num) hd
    omega
  have hprod : ‖wordSum (om p q) (2*m) m‖ * ‖(1 : ℂ) - om p q‖ = 2 := by
    have h := congrArg (fun z : ℂ => ‖z‖) hmain
    rw [hneg] at h
    have e1 : ‖wordSum (om p q) (2*m) m * (1 - om p q)‖
        = ‖wordSum (om p q) (2*m) m‖ * ‖(1 : ℂ) - om p q‖ := norm_mul _ _
    have e2 : ‖((-1 : ℂ)^m * om p q ^ (∑ k ∈ Finset.range m, (m+1+k))) * ((1:ℂ) - -1)‖
        = 2 := by
      rw [show (1 : ℂ) - -1 = (2 : ℂ) by norm_num]
      simp only [norm_mul, norm_pow, norm_neg, norm_one, om_norm, one_pow, mul_one, one_mul,
        Complex.norm_ofNat]
    rw [e1, e2] at h
    exact h
  have hle2 : ‖(1 : ℂ) - om p q‖ ≤ 2 := by
    have h := norm_sub_le (1 : ℂ) (om p q)
    rw [norm_one, om_norm] at h
    linarith
  have key : (1 : ℝ) * ‖(1 : ℂ) - om p q‖
      ≤ ‖wordSum (om p q) (2*m) m‖ * ‖(1 : ℂ) - om p q‖ := by
    rw [one_mul, hprod]
    exact hle2
  exact le_of_mul_le_mul_right key (norm_pos_iff.mpr hωne)


def CountHyp (m q : ℕ) : Prop :=
  ∀ a b c e : ℕ, a + b + c + e ≤ 2*m+1 →
    (q : ℤ) ∣ ((a : ℤ) - (b : ℤ) - (m : ℤ)) →
    (q : ℤ) ∣ ((c : ℤ) - (e : ℤ) - (m : ℤ)) → a = m ∧ b = 0 ∧ c = m ∧ e = 0

/-- All the traces below the top one vanish. -/
theorem evenTraceZero (p : ℤ) (q m : ℕ) (hm : q = 2*m+2) (hpq : Nat.Coprime p.natAbs q)
    (lam θ k : ℝ) (hh : CountHyp m q) (n : ℕ) (hn : n ≤ 2*m+1) (hne : n ≠ 2*m) :
    ((wB p q lam θ k) ^ n * ((star (wU q k)) ^ m * (star (wV p q θ)) ^ m)).trace = 0 := by
  have hq : 0 < q := by omega
  rw [wB_pow, Finset.sum_mul, Matrix.trace_sum]
  refine Finset.sum_eq_zero (fun f _ => ?_)
  obtain ⟨u, hu, hNFf⟩ := WordNormalForm p q θ k n f
  rw [wP_eq, Matrix.smul_mul, Matrix.trace_smul, word_trace_eq p q m θ k n f u hNFf]
  have hsum := cnt_sum n f
  have hcond : ¬ ((q : ℤ) ∣ (((cnt false true n f : ℕ) : ℤ) - ((cnt false false n f : ℕ) : ℤ)
        - (m : ℤ))) ∨
      ¬ ((q : ℤ) ∣ (((cnt true true n f : ℕ) : ℤ) - ((cnt true false n f : ℕ) : ℤ)
        - (m : ℤ))) := by
    by_contra hc
    push_neg at hc
    obtain ⟨h1, h2⟩ := hc
    obtain ⟨ha, hb, hc', he⟩ := hh _ _ _ _ (by omega) h1 h2
    omega
  rw [TraceRule p q θ k hq hpq (cnt false true n f) (cnt false false n f) (cnt true true n f)
    (cnt true false n f) m hcond]
  simp

/-- The top trace, in the even case. -/
theorem evenTraceTop (p : ℤ) (q m : ℕ) (hm : q = 2*m+2) (hpq : Nat.Coprime p.natAbs q)
    (lam θ k : ℝ) (hh : CountHyp m q) :
    ((wB p q lam θ k) ^ (2*m) * ((star (wU q k)) ^ m * (star (wV p q θ)) ^ m)).trace
      = (q : ℂ) * (lam : ℂ) ^ m * wordSum (om p q) (2*m) m := by
  have hq : 0 < q := by omega
  rw [wB_pow, Finset.sum_mul, Matrix.trace_sum]
  have hterm : ∀ f : Fin (2*m) → Bool × Bool,
      (((List.ofFn (fun i => wL p q lam θ k (f i))).prod) *
        ((star (wU q k)) ^ m * (star (wV p q θ)) ^ m)).trace
      = (if ((∀ i, f i = (true, true) ∨ f i = (false, true)) ∧
            (Finset.univ.filter (fun i : Fin (2*m) => f i = (true, true))).card = m)
          then (lam : ℂ) ^ m * ((om p q) ^ (invCount (2*m) f) * (q : ℂ)) else 0) := by
    intro f
    by_cases hf : ((∀ i, f i = (true, true) ∨ f i = (false, true)) ∧
            (Finset.univ.filter (fun i : Fin (2*m) => f i = (true, true))).card = m)
    · rw [if_pos hf, wP_eq, Matrix.smul_mul, Matrix.trace_smul,
        vcount_of_interleave m f hf.1 hf.2]
      have hV : (Finset.univ.filter (fun i : Fin (2*m) => f i = (false, true))).card = m := by
        have := interleave_card m f hf.1
        omega
      rw [InterleaveWordNorm p q θ k (2*m) f hf.1, hV, hf.2]
      rw [Matrix.smul_mul, Matrix.trace_smul]
      have hW : (wV p q θ ^ m * wU q k ^ m) *
          ((star (wU q k)) ^ m * (star (wV p q θ)) ^ m) = 1 := by
        rw [show (wV p q θ ^ m * wU q k ^ m) *
              ((star (wU q k)) ^ m * (star (wV p q θ)) ^ m)
            = wV p q θ ^ m *
              ((wU q k ^ m * (star (wU q k)) ^ m) * (star (wV p q θ)) ^ m)
          from by simp only [mul_assoc],
          wU_pow_mul_star_pow q k hq m, one_mul, wV_pow_mul_star_pow]
      rw [hW, Matrix.trace_one, Fintype.card_fin]
      ring
    · rw [if_neg hf, wP_eq, Matrix.smul_mul, Matrix.trace_smul]
      obtain ⟨u, hu, hNFf⟩ := WordNormalForm p q θ k (2*m) f
      rw [word_trace_eq p q m θ k (2*m) f u hNFf]
      have hsum := cnt_sum (2*m) f
      have hcond : ¬ ((q : ℤ) ∣ (((cnt false true (2*m) f : ℕ) : ℤ)
            - ((cnt false false (2*m) f : ℕ) : ℤ) - (m : ℤ))) ∨
          ¬ ((q : ℤ) ∣ (((cnt true true (2*m) f : ℕ) : ℤ)
            - ((cnt true false (2*m) f : ℕ) : ℤ) - (m : ℤ))) := by
        by_contra hc
        push_neg at hc
        obtain ⟨h1, h2⟩ := hc
        obtain ⟨ha, hb, hc', he⟩ := hh _ _ _ _ (by omega) h1 h2
        refine hf ⟨?_, ?_⟩
        · intro i
          have h1n : f i ≠ (false, false) := by
            intro hfi
            have hmem : i ∈ (Finset.univ.filter (fun j : Fin (2*m) => f j = (false, false))) := by
              simp [hfi]
            rw [Finset.card_eq_zero.mp hb] at hmem
            exact absurd hmem (by simp)
          have h2n : f i ≠ (true, false) := by
            intro hfi
            have hmem : i ∈ (Finset.univ.filter (fun j : Fin (2*m) => f j = (true, false))) := by
              simp [hfi]
            rw [Finset.card_eq_zero.mp he] at hmem
            exact absurd hmem (by simp)
          rcases hfi : f i with ⟨b1, b2⟩
          cases b1 <;> cases b2 <;> simp_all
        · exact hc'
      rw [TraceRule p q θ k hq hpq (cnt false true (2*m) f) (cnt false false (2*m) f)
        (cnt true true (2*m) f) (cnt true false (2*m) f) m hcond]
      simp
  rw [Finset.sum_congr rfl (fun f _ => hterm f)]
  have hword : wordSum (om p q) (2*m) m
      = ∑ f ∈ (Finset.univ : Finset (Fin (2*m) → Bool × Bool)).filter
          (fun f => (∀ i, f i = (true, true) ∨ f i = (false, true)) ∧
            (Finset.univ.filter (fun i => f i = (true, true))).card = m),
          (om p q) ^ (invCount (2*m) f) := rfl
  rw [hword, ← Finset.sum_filter]
  have hswap : (q : ℂ) * (lam : ℂ) ^ m *
        (∑ f ∈ (Finset.univ : Finset (Fin (2*m) → Bool × Bool)).filter
          (fun f => (∀ i, f i = (true, true) ∨ f i = (false, true)) ∧
            (Finset.univ.filter (fun i => f i = (true, true))).card = m),
          (om p q) ^ (invCount (2*m) f))
      = ∑ f ∈ (Finset.univ : Finset (Fin (2*m) → Bool × Bool)).filter
          (fun f => (∀ i, f i = (true, true) ∨ f i = (false, true)) ∧
            (Finset.univ.filter (fun i => f i = (true, true))).card = m),
          (lam : ℂ) ^ m * ((om p q) ^ (invCount (2*m) f) * (q : ℂ)) := by
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl (fun f _ => by ring)
  rw [hswap]

/-- **The adjugate trace identity.**  If all the traces `tr (B^k * W)` vanish for
`k ≤ 2m+1`, `k ≠ 2m`, and if the coefficient of `X^(2m+1)` of the characteristic polynomial
of `B` vanishes, then `tr (adjugate (z - B) * W) = z * tr (B^(2m) * W)`. -/
theorem evenAdjTrace (q m : ℕ) (hm : q = 2*m+2) (B W : Matrix (Fin q) (Fin q) ℂ) (z : ℂ)
    (hzero : ∀ n : ℕ, n ≤ 2*m+1 → n ≠ 2*m → ((B ^ n) * W).trace = 0)
    (hc : B.charpoly.coeff (2*m+1) = 0) :
    (Matrix.adjugate (z • (1 : Matrix (Fin q) (Fin q) ℂ) - B) * W).trace
      = z * ((B ^ (2*m)) * W).trace := by
  have hgen : (B.charmatrix).adjugate
      = ∑ i ∈ Finset.range (q + 1), Polynomial.C (B.charpoly.coeff i) • geom B i :=
    adjugate_charmatrix_eq B
  have hmapadj : (B.charmatrix).adjugate.map (Polynomial.eval z)
      = Matrix.adjugate (z • (1 : Matrix (Fin q) (Fin q) ℂ) - B) := by
    have h1 : (B.charmatrix).adjugate.map (Polynomial.eval z)
        = (B.charmatrix.map (Polynomial.eval z)).adjugate := by
      have := RingHom.map_adjugate (Polynomial.evalRingHom z) B.charmatrix
      simpa [RingHom.mapMatrix_apply] using this
    rw [h1, map_charmatrix]
  have hmap : (B.charmatrix).adjugate.map (Polynomial.eval z)
      = ∑ i ∈ Finset.range (q + 1), (B.charpoly.coeff i) • geomZ B z i := by
    rw [hgen]
    exact map_geomsum B z
  have hadj : Matrix.adjugate (z • (1 : Matrix (Fin q) (Fin q) ℂ) - B)
      = ∑ i ∈ Finset.range (q + 1), (B.charpoly.coeff i) • geomZ B z i := by
    rw [← hmapadj, hmap]
  have hinner : ∀ i, (geomZ B z i * W).trace
      = ∑ k ∈ Finset.range i, z ^ (i - 1 - k) * (B ^ k * W).trace := by
    intro i
    rw [geomZ, Matrix.sum_mul, Matrix.trace_sum]
    apply Finset.sum_congr rfl
    intro k _
    rw [Matrix.smul_mul, Matrix.trace_smul, smul_eq_mul]
  have hcoeffq : B.charpoly.coeff q = 1 := by
    have hnd : B.charpoly.natDegree = q := by simpa using Matrix.charpoly_natDegree_eq_dim B
    simpa [hnd] using (Matrix.charpoly_monic B).coeff_natDegree
  rw [hadj, Matrix.sum_mul, Matrix.trace_sum]
  simp only [Matrix.smul_mul, Matrix.trace_smul, smul_eq_mul, hinner]
  have hsum1 : (∑ i ∈ Finset.range (q + 1), B.charpoly.coeff i *
        (∑ k ∈ Finset.range i, z ^ (i - 1 - k) * (B ^ k * W).trace))
      = B.charpoly.coeff q *
        (∑ k ∈ Finset.range q, z ^ (q - 1 - k) * (B ^ k * W).trace) := by
    refine Finset.sum_eq_single q ?_ ?_
    · intro i hi hiq
      have hi' : i < q := by
        have : i < q + 1 := Finset.mem_range.mp hi
        omega
      by_cases hic : i = 2*m+1
      · rw [hic, hc, zero_mul]
      · have hik : (∑ k ∈ Finset.range i, z ^ (i - 1 - k) * (B ^ k * W).trace) = 0 := by
          apply Finset.sum_eq_zero
          intro k hk
          have hk' : k < i := Finset.mem_range.mp hk
          rw [hzero k (by omega) (by omega), mul_zero]
        rw [hik, mul_zero]
    · intro hc'
      exact absurd (Finset.mem_range.mpr (Nat.lt_succ_self q)) hc'
  rw [hsum1, hcoeffq, one_mul]
  have hsum2 : (∑ k ∈ Finset.range q, z ^ (q - 1 - k) * (B ^ k * W).trace)
      = z ^ (q - 1 - 2*m) * ((B ^ (2*m)) * W).trace := by
    refine Finset.sum_eq_single (2*m) ?_ ?_
    · intro k hk hk2m
      have hk' : k < q := Finset.mem_range.mp hk
      rw [hzero k (by omega) (by omega), mul_zero]
    · intro hc'
      exact absurd (Finset.mem_range.mpr (by omega)) hc'
  rw [hsum2, show q - 1 - 2*m = 1 by omega, pow_one]

theorem chamCoef_real (p : ℤ) (q m : ℕ) (hm : q = 2*m+2) (lam : ℝ) :
    ∃ A₀ : ℝ, chamCoef p q lam = (A₀ : ℂ) := by
  refine ⟨2 * (-lam)^q * (-1)^(p * ((q:ℤ) - 1)), ?_⟩
  rw [chamCoef]
  have h1 : (-(lam : ℂ)) ^ q = (((-lam) ^ q : ℝ) : ℂ) := by
    rw [show (-(lam : ℂ)) = ((-lam : ℝ) : ℂ) from by simp, ← Complex.ofReal_pow]
  have h2 : (-1 : ℂ) ^ (p * ((q : ℤ) - 1)) = (((-1 : ℝ) ^ (p * ((q : ℤ) - 1)) : ℝ) : ℂ) := by
    rw [show (-1 : ℂ) = ((-1 : ℝ) : ℂ) from by norm_num, ← Complex.ofReal_zpow]
  rw [h1, h2]
  push_cast
  ring

/-- The trace of the Bloch matrix vanishes (for `q ≥ 2`). -/
theorem trace_blochMat_eq_zero (p : ℤ) (q : ℕ) (lam θ k : ℝ) (hpq : Nat.Coprime p.natAbs q)
    (hq : 2 ≤ q) :
    (blochMat p q lam θ k).trace = 0 := by
  have hq1 : 0 < q := by omega
  rw [BlochMatEq, Matrix.trace_add, Matrix.trace_add, Matrix.trace_smul]
  have hU : (wU q k).trace = 0 := by
    rw [Matrix.trace]
    refine Finset.sum_eq_zero (fun i _ => ?_)
    rw [Matrix.diag_apply, wU_apply, if_neg]
    intro hcon
    by_cases hlt : i.val + 1 < q
    · rw [Nat.mod_eq_of_lt hlt] at hcon; omega
    · have hiq : i.val + 1 = q := by omega
      rw [hiq, Nat.mod_self] at hcon
      omega
  have hU' : (star (wU q k)).trace = 0 := by
    rw [Matrix.star_eq_conjTranspose, Matrix.trace_conjTranspose, hU, star_zero]
  have hVd1 : (∑ i : Fin q, wVd p q θ i) = 0 := by
    have h := TraceRuleAux.traceSumVdPowZero p q θ hq1 hpq 1 0 (by
      simp only [Nat.cast_one, Nat.cast_zero, sub_zero]
      intro hd
      have hd' : (q : ℕ) ∣ 1 := by exact_mod_cast hd
      have := Nat.le_of_dvd (by norm_num) hd'
      omega)
    simpa using h
  have hVd2 : (∑ i : Fin q, star (wVd p q θ i)) = 0 := by
    have h := TraceRuleAux.traceSumVdPowZero p q θ hq1 hpq 0 1 (by
      simp only [Nat.cast_one, Nat.cast_zero, zero_sub]
      intro hd
      have hd1 : (q : ℤ) ∣ (1 : ℤ) := by simpa using dvd_neg.mpr hd
      have hd2 : (q : ℕ) ∣ 1 := by exact_mod_cast hd1
      have := Nat.le_of_dvd (by norm_num) hd2
      omega)
    simpa using h
  have hV : (wV p q θ + star (wV p q θ)).trace = 0 := by
    rw [Matrix.trace_add]
    have h1 : (wV p q θ).trace = ∑ i : Fin q, wVd p q θ i := by
      rw [wV, Matrix.trace_diagonal]
    have h2 : (star (wV p q θ)).trace = ∑ i : Fin q, star (wVd p q θ i) := by
      rw [Matrix.star_eq_conjTranspose, wV, Matrix.diagonal_conjTranspose, Matrix.trace_diagonal]
      simp
    rw [h1, h2, hVd1, hVd2, add_zero]
  rw [hU, hU', hV]
  ring

/-- The coefficient of `X^(q-1)` of the characteristic polynomial of the Bloch matrix
vanishes. -/
theorem blochMat_charpoly_coeff_pred (p : ℤ) (q : ℕ) (lam θ k : ℝ)
    (hpq : Nat.Coprime p.natAbs q) (hq : 2 ≤ q) :
    (blochMat p q lam θ k).charpoly.coeff (q - 1) = 0 := by
  haveI : Nonempty (Fin q) := ⟨⟨0, by omega⟩⟩
  have h := Matrix.trace_eq_neg_charpoly_coeff (blochMat p q lam θ k)
  rw [Fintype.card_fin] at h
  rw [trace_blochMat_eq_zero p q lam θ k hpq hq, zero_eq_neg] at h
  exact h

/-- The derivative of the characteristic polynomial of the Bloch matrix agrees with `disc'`. -/
theorem blochMat_charpoly_deriv_eq (p : ℤ) (q : ℕ) (lam θ k : ℝ)
    (hpq : Nat.Coprime p.natAbs q) (hq : 1 ≤ q) (z : ℂ) :
    ((blochMat p q lam θ k).charpoly).derivative.eval z
      = (disc p q lam).derivative.eval z := by
  have hpoly : (blochMat p q lam θ k).charpoly
      = disc p q lam + Polynomial.C (chamCoef p q lam *
          ((Real.cos (2 * Real.pi * (q : ℝ) * θ) : ℝ) : ℂ)
          - 2 * ((Real.cos (2 * Real.pi * k) : ℝ) : ℂ)) := by
    apply Polynomial.funext
    intro w
    rw [Polynomial.eval_add, Polynomial.eval_C, Matrix.eval_charpoly]
    rw [show Matrix.scalar (Fin q) w = w • (1 : Matrix (Fin q) (Fin q) ℂ) from by
      ext i j
      rw [Matrix.scalar_apply, Matrix.diagonal_apply, Matrix.smul_apply, smul_eq_mul,
        Matrix.one_apply]
      by_cases h : i = j <;> simp [h]]
    rw [blochMat_chambers p q lam θ k w hpq hq]
    ring
  rw [hpoly, Polynomial.derivative_add, Polynomial.derivative_C, add_zero]

/-- **Eigenvalue realisation.**  If `‖Δ(a)‖ ≤ 2 + 2λ^q` then `a` is an eigenvalue of the
Bloch matrix `blochMat p q lam θ k` for suitable `θ, k`. -/
theorem exists_eigen_blochMat (p : ℤ) (q m : ℕ) (hm : q = 2*m+2) (hpq : Nat.Coprime p.natAbs q)
    (lam : ℝ) (hlam : 0 < lam) (a : ℝ) (c : ℂ)
    (hc : ‖c‖ ≤ 2 + 2*lam^q) (ha : (disc p q lam).eval ((a:ℝ):ℂ) = c) :
    ∃ θ k : ℝ, ∃ v : Fin q → ℂ, v ≠ 0 ∧ (blochMat p q lam θ k).mulVec v = ((a:ℝ):ℂ) • v := by
  have hq1 : 1 ≤ q := by omega
  obtain ⟨A₀, hA₀⟩ := chamCoef_real p q m hm lam
  have hAnorm : |A₀| = 2 * lam^q := by
    have h := chamCoef_norm p q lam hlam
    rw [hA₀] at h
    have h2 : ‖(A₀ : ℂ)‖ = |A₀| := RCLike.norm_ofReal A₀
    rw [h2] at h
    exact h
  have hcim : c.im = 0 := by
    rw [← ha]
    exact ceyEvenAux.discEvalIm p q lam a
  have hcre : c = ((c.re : ℝ) : ℂ) := by
    apply Complex.ext <;> simp [hcim]
  have hbound : |c.re| ≤ 2 + |A₀| := by
    have h1 : |c.re| ≤ ‖c‖ := Complex.abs_re_le_norm c
    have h2 : ‖c‖ ≤ 2 + |A₀| := by rw [hAnorm]; exact hc
    linarith
  have hA₀ne : A₀ ≠ 0 := by
    intro h0
    rw [h0, abs_zero] at hAnorm
    have hpos : (0:ℝ) < 2 * lam^q := by positivity
    linarith
  have hcase : ∃ u v : ℝ, |u| ≤ 1 ∧ |v| ≤ 1 ∧ 2*u - A₀*v = c.re := by
    by_cases h2 : |c.re| ≤ 2
    · refine ⟨c.re / 2, 0, ?_, ?_, ?_⟩
      · rw [abs_div]; norm_num; linarith
      · norm_num
      · ring
    · have h2' : 2 < |c.re| := lt_of_not_ge h2
      have hsplit : 2 < c.re ∨ c.re < -2 := by
        by_cases hpos : 0 ≤ c.re
        · left; rw [abs_of_nonneg hpos] at h2'; exact h2'
        · right; rw [abs_of_neg (lt_of_not_ge hpos)] at h2'; linarith
      rcases hsplit with hpos | hneg
      · refine ⟨1, (2 - c.re) / A₀, by norm_num, ?_, ?_⟩
        · rw [abs_div, div_le_one (abs_pos.mpr hA₀ne)]
          have h3 : |2 - c.re| = c.re - 2 := by rw [abs_of_neg (by linarith)]; ring
          rw [h3]
          have h4 : c.re ≤ 2 + |A₀| := by
            have h5 := hbound
            rwa [abs_of_pos (by linarith : (0:ℝ) < c.re)] at h5
          linarith
        · have hA : A₀ * ((2 - c.re) / A₀) = 2 - c.re := mul_div_cancel₀ _ hA₀ne
          calc (2 : ℝ) * 1 - A₀ * ((2 - c.re) / A₀)
              = (2 : ℝ) * 1 - (2 - c.re) := by rw [hA]
            _ = c.re := by ring
      · refine ⟨-1, (-2 - c.re) / A₀, by norm_num, ?_, ?_⟩
        · rw [abs_div, abs_of_nonneg (by linarith : (0:ℝ) ≤ -2 - c.re),
            div_le_one (abs_pos.mpr hA₀ne)]
          have h4 : -2 - c.re ≤ |A₀| := by
            have h5 := hbound
            rw [abs_of_neg (by linarith : c.re < 0)] at h5
            linarith
          linarith
        · have hA : A₀ * ((-2 - c.re) / A₀) = -2 - c.re := mul_div_cancel₀ _ hA₀ne
          calc (2 : ℝ) * (-1) - A₀ * ((-2 - c.re) / A₀)
              = (2 : ℝ) * (-1) - (-2 - c.re) := by rw [hA]
            _ = c.re := by ring
  obtain ⟨u, v, hu, hv, huv⟩ := hcase
  obtain ⟨y, hy, hcy⟩ := Real.surjOn_cos (abs_le.mp hv)
  obtain ⟨y', hy', hcy'⟩ := Real.surjOn_cos (abs_le.mp hu)
  refine ⟨y / (2 * Real.pi * (q : ℝ)), y' / (2 * Real.pi), ?_⟩
  have hne1 : (2 * Real.pi * (q : ℝ)) ≠ 0 := by positivity
  have hne2 : (2 * Real.pi) ≠ 0 := by positivity
  have hcos1 : Real.cos (2 * Real.pi * (q : ℝ) * (y / (2 * Real.pi * (q : ℝ)))) = v := by
    rw [show 2 * Real.pi * (q : ℝ) * (y / (2 * Real.pi * (q : ℝ))) = y from
      mul_div_cancel₀ _ hne1]
    exact hcy
  have hcos2 : Real.cos (2 * Real.pi * (y' / (2 * Real.pi))) = u := by
    rw [show 2 * Real.pi * (y' / (2 * Real.pi)) = y' from mul_div_cancel₀ _ hne2]
    exact hcy'
  have hdet : (((a : ℝ) : ℂ) • (1 : Matrix (Fin q) (Fin q) ℂ)
      - blochMat p q lam (y / (2 * Real.pi * (q : ℝ))) (y' / (2 * Real.pi))).det = 0 := by
    rw [blochMat_chambers p q lam _ _ ((a:ℝ):ℂ) hpq hq1, ha, hcre, hA₀, hcos1, hcos2]
    have hreal : (c.re : ℝ) + A₀ * v - 2 * u = 0 := by linarith
    rw [show ((c.re : ℝ) : ℂ) + (A₀ : ℂ) * ((v : ℝ) : ℂ) - 2 * ((u : ℝ) : ℂ)
        = (((c.re : ℝ) + A₀ * v - 2 * u : ℝ) : ℂ) from by push_cast; ring, hreal]
    simp
  obtain ⟨v', hv', hmv⟩ := Matrix.exists_mulVec_eq_zero_iff.mpr hdet
  refine ⟨v', hv', ?_⟩
  rw [Matrix.sub_mulVec, Matrix.smul_mulVec, Matrix.one_mulVec, sub_eq_zero] at hmv
  exact hmv.symm

/-! ## The main theorem -/

/-- `star (wU q k)` is unitary. -/
theorem star_wU_mem (q : ℕ) (k : ℝ) (hq : 0 < q) :
    star (wU q k) ∈ Matrix.unitaryGroup (Fin q) ℂ := by
  rw [Matrix.mem_unitaryGroup_iff, star_star]
  exact mul_eq_one_comm.mp ((Matrix.mem_unitaryGroup_iff).mp (wU_mem_unitaryGroup q k hq))

/-- `star (wV p q θ)` is unitary. -/
theorem star_wV_mem (p : ℤ) (q : ℕ) (θ : ℝ) :
    star (wV p q θ) ∈ Matrix.unitaryGroup (Fin q) ℂ := by
  rw [Matrix.mem_unitaryGroup_iff, star_star]
  exact mul_eq_one_comm.mp ((Matrix.mem_unitaryGroup_iff).mp (wV_mem_unitaryGroup p q θ))

/-- **The even-`q` CEY derivative bound, without the restriction `λ ≤ 1`.**

For `q = 2m+2` even, `gcd(p,q) = 1`, `λ > 0`, and any real `a` with `‖Δ(a)‖ ≤ 2 + 2λ^q`
(i.e. `a` in the rational union spectrum), one has `q λ^m |a| ≤ ‖Δ'(a)‖`. -/
theorem ceyEvenDiscDerivGen (p : ℤ) (q m : ℕ) (hm : q = 2*m+2) (hpq : Nat.Coprime p.natAbs q)
    (lam : ℝ) (hlam : 0 < lam) (a : ℝ) (c : ℂ) (hc : ‖c‖ ≤ 2 + 2*lam^q)
    (ha : (disc p q lam).eval (a : ℂ) = c) :
    (q : ℝ) * lam ^ m * |a| ≤ ‖(disc p q lam).derivative.eval (a : ℂ)‖ := by
  have hq1 : 1 ≤ q := by omega
  have hq2 : 2 ≤ q := by omega
  have hq0 : 0 < q := by omega
  have hcount : CountHyp m q :=
    fun a' b' c' e' h1 h2 h3 => ceyEvenAux.countEven a' b' c' e' m q hm h1 h2 h3
  have hwns : 1 ≤ ‖wordSum (om p q) (2*m) m‖ := wordSumNormGeOne p q m hm hpq
  obtain ⟨θ, k, v, hv, hev⟩ := exists_eigen_blochMat p q m hm hpq lam hlam a c hc ha
  have hBherm : (blochMat p q lam θ k).IsHermitian := blochMat_isHermitian p q lam θ k
  set W : Matrix (Fin q) (Fin q) ℂ := (star (wU q k)) ^ m * (star (wV p q θ)) ^ m with hWdef
  have hW : W ∈ Matrix.unitaryGroup (Fin q) ℂ := by
    rw [hWdef]
    exact mul_mem (pow_mem (star_wU_mem q k hq0) m) (pow_mem (star_wV_mem p q θ) m)
  have htop : ((wB p q lam θ k) ^ (2*m) * W).trace
      = (q : ℂ) * (lam : ℂ) ^ m * wordSum (om p q) (2*m) m := by
    rw [hWdef]
    exact evenTraceTop p q m hm hpq lam θ k hcount
  have hzero : ∀ n : ℕ, n ≤ 2*m+1 → n ≠ 2*m → ((wB p q lam θ k) ^ n * W).trace = 0 := by
    intro n hn hne
    rw [hWdef]
    exact evenTraceZero p q m hm hpq lam θ k hcount n hn hne
  have hBl : blochMat p q lam θ k = wB p q lam θ k := BlochMatEq p q lam θ k
  have hcoeff : (wB p q lam θ k).charpoly.coeff (2*m+1) = 0 := by
    rw [← hBl]
    have h := blochMat_charpoly_coeff_pred p q lam θ k hpq hq2
    rwa [show q - 1 = 2*m+1 by omega] at h
  have hadj : (Matrix.adjugate (((a:ℝ):ℂ) • (1 : Matrix (Fin q) (Fin q) ℂ)
        - blochMat p q lam θ k) * W).trace
      = ((a:ℝ):ℂ) * ((q : ℂ) * (lam : ℂ) ^ m * wordSum (om p q) (2*m) m) := by
    rw [hBl]
    rw [evenAdjTrace q m hm (wB p q lam θ k) W ((a:ℝ):ℂ) hzero hcoeff, htop]
  have hbound : ‖(Matrix.adjugate (((a:ℝ):ℂ) • (1 : Matrix (Fin q) (Fin q) ℂ)
        - blochMat p q lam θ k) * W).trace‖
      ≤ ‖(disc p q lam).derivative.eval ((a:ℝ):ℂ)‖ := by
    have hkSA : IsSelfAdjoint (((a:ℝ):ℂ)) := by
      rw [IsSelfAdjoint, Complex.star_def, Complex.conj_ofReal]
    have hNherm : (((a:ℝ):ℂ) • (1 : Matrix (Fin q) (Fin q) ℂ)
        - blochMat p q lam θ k).IsHermitian :=
      (Matrix.isHermitian_one.smul hkSA).sub hBherm
    have hNv : (((a:ℝ):ℂ) • (1 : Matrix (Fin q) (Fin q) ℂ)
        - blochMat p q lam θ k) *ᵥ v = 0 := by
      rw [Matrix.sub_mulVec, Matrix.smul_mulVec, Matrix.one_mulVec, sub_eq_zero]
      exact hev.symm
    obtain ⟨c₀, hc₀⟩ := adjugateHermitianRankOne _ hNherm v hv hNv
    have h1 := traceUnitaryLe c₀ v W hW
    rw [hc₀]
    refine le_trans h1 ?_
    rw [← hc₀]
    rw [← ceyEvenAux.charpolyDerivAdjHerm (blochMat p q lam θ k) hBherm ((a:ℝ):ℂ)]
    rw [blochMat_charpoly_deriv_eq p q lam θ k hpq hq1]
  have hnorm : ‖(Matrix.adjugate (((a:ℝ):ℂ) • (1 : Matrix (Fin q) (Fin q) ℂ)
        - blochMat p q lam θ k) * W).trace‖
      = (q : ℝ) * lam ^ m * |a| * ‖wordSum (om p q) (2*m) m‖ := by
    have hn1 : ‖((a:ℝ):ℂ)‖ = |a| := by simp
    have hn2 : ‖((q:ℕ):ℂ)‖ = (q:ℝ) := by simp
    have hn3 : ‖((lam:ℝ):ℂ)‖ = lam := by simp [abs_of_pos hlam]
    rw [hadj, norm_mul, norm_mul, norm_mul, hn1, hn2, norm_pow, hn3]
    ring
  calc (q : ℝ) * lam ^ m * |a| = (q : ℝ) * lam ^ m * |a| * 1 := by ring
    _ ≤ (q : ℝ) * lam ^ m * |a| * ‖wordSum (om p q) (2*m) m‖ := by
        refine mul_le_mul_of_nonneg_left hwns (by positivity)
    _ = ‖(Matrix.adjugate (((a:ℝ):ℂ) • (1 : Matrix (Fin q) (Fin q) ℂ)
          - blochMat p q lam θ k) * W).trace‖ := hnorm.symm
    _ ≤ ‖(disc p q lam).derivative.eval ((a:ℝ):ℂ)‖ := hbound

end ceyEvenGen
end Work.TMC14Core
