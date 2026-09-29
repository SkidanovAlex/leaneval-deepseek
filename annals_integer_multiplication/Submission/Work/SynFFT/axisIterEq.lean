import Mathlib
import Submission.Work.SynFFT.kit2
import Submission.Work.SynFFT.multiCons
import Submission.Work.SynFFT.axisTShift

/-!
# `axisIterEq`: the axis loop of the synthetic FFT computes the multivariate transform

`axisIterN r sgn ts u` applies the axis pass `axisT r t ts.prod sgn` once per axis `t`, innermost
first: `axisIterN r sgn (t :: ts) u = axisT r t ts.prod sgn (axisIterN r sgn ts u)`.  The claim of
`AxisIterProp` is that, on the positions actually used, this equals the natural-number-indexed
version `dftMultiN r ts sgn u` of the multivariate synthetic DFT `G_{t₁,…}` (paper Prop 3.3).

The proof is by the observation that `axisIterN ... ts u` is *block-local*: for the block length
`B = ts.prod`, the value at `x` depends on `u` only through the window `k ↦ u (x / B * B + k)`:

  `axisIterN r sgn ts u x = dftMultiN r ts sgn (fun k => u (x / B * B + k)) (x % B)`   (`*`)

(this is `axisIterN_blk` below; note that `x / B * B + x % B = x`, so for `x < B` the window is
`u` itself, which gives `AxisIterProp`).  The induction step for `ts = t :: ts'` (with `B = t * B'`)
splits the position as `x = σ + δ`, `σ = x / B * B`, `δ = x % B`:

* `multiCons` rewrites `dftMultiN r (t :: ts') sgn (the σ-window) δ` as the axis pass along `t`
  (stride `B'`) of the *blockwise* tails `q ↦ dftMultiN r ts' sgn (tail window at q) (q % B')`;
* `axisTShift` moves the axis pass back from the shifted index `δ` to `x`;
* the two arrays fed to the axis pass agree by the induction hypothesis plus
  `(σ + q) / B' * B' = σ + q / B' * B'` and `(σ + q) % B' = q % B'` for `B' ∣ σ`.
-/

set_option autoImplicit false
set_option maxHeartbeats 800000

namespace Work.SynFFT
open HvdH
open scoped BigOperators

/-- The synthetic transform of the empty axis list is multiplication by `y^0 = 1`. -/
lemma dftMultiN_nil (r : ℕ) (sgn : ℤ) (v : Arr r) (j : ℕ) :
    dftMultiN r [] sgn v j = HvdH.yMul r 0 (v 0) := by
  funext c
  simp [dftMultiN, HvdH.synExp]

/-- **Block locality of the axis loop.**  For a list of positive axes, the value of
`axisIterN r sgn ts u` at `x` is the synthetic transform of the length-`ts.prod` window of `u`
starting at `x / ts.prod * ts.prod`, at the local index `x % ts.prod`. -/
theorem axisIterN_blk (r : ℕ) (sgn : ℤ) (u : Arr r) :
    ∀ (ts : List ℕ), (∀ t ∈ ts, 0 < t) → ∀ x : ℕ,
      axisIterN r sgn ts u x =
        dftMultiN r ts sgn (fun k => u (x / ts.prod * ts.prod + k)) (x % ts.prod) := by
  rcases Nat.eq_zero_or_pos r with h0 | hr
  · subst h0
    intro ts _ x
    funext c
    exact Fin.elim0 c
  · intro ts
    induction ts with
    | nil =>
      intro _ x
      have hy : ∀ a : Fin r → ℂ, HvdH.yMul r 0 a = a := (yMulAlg r hr).2.1
      show u x = dftMultiN r [] sgn (fun k => u (x / 1 * 1 + k)) (x % 1)
      rw [dftMultiN_nil r sgn (fun k => u (x / 1 * 1 + k)) (x % 1), hy]
      simp
    | cons t ts ih =>
      intro hpos x
      simp only [List.prod_cons]
      have ht : 0 < t := hpos t List.mem_cons_self
      have hpos' : ∀ s ∈ ts, 0 < s := fun s hs => hpos s (List.mem_cons_of_mem t hs)
      have hB' : 0 < ts.prod := List.prod_pos hpos'
      have hB : 0 < t * ts.prod := Nat.mul_pos ht hB'
      set σ : ℕ := x / (t * ts.prod) * (t * ts.prod) with hσdef
      set δ : ℕ := x % (t * ts.prod) with hδdef
      have hx : σ + δ = x := by
        rw [hσdef, hδdef, mul_comm (x / (t * ts.prod)) (t * ts.prod), Nat.div_add_mod]
      have hdvd : t * ts.prod ∣ σ := ⟨x / (t * ts.prod), by rw [hσdef, mul_comm]⟩
      have hdvdB' : ts.prod ∣ σ := dvd_trans ⟨t, by rw [mul_comm]⟩ hdvd
      obtain ⟨m, hm⟩ : ∃ m, σ = ts.prod * m := by
        obtain ⟨c, hc⟩ := hdvdB'
        exact ⟨c, by rw [hc, mul_comm]⟩
      have hL : axisIterN r sgn (t :: ts) u x
          = axisT r t ts.prod sgn (fun y c => axisIterN r sgn ts u (σ + y) c) δ := by
        rw [show axisIterN r sgn (t :: ts) u = axisT r t ts.prod sgn (axisIterN r sgn ts u)
              from rfl, ← hx]
        exact (axisTShift r t ts.prod sgn σ (axisIterN r sgn ts u) hdvd δ).symm
      have hR : dftMultiN r (t :: ts) sgn (fun k => u (σ + k)) δ
          = axisT r t ts.prod sgn (fun y c =>
              dftMultiN r ts sgn (fun k => u (σ + (y / ts.prod * ts.prod + k)))
                (y % ts.prod) c) δ :=
        multiCons r t ts sgn (fun k => u (σ + k)) ht hpos' δ
          (by rw [hδdef]; exact Nat.mod_lt x hB)
      have hFG : (fun y c => axisIterN r sgn ts u (σ + y) c)
          = (fun y c => dftMultiN r ts sgn
              (fun k => u (σ + (y / ts.prod * ts.prod + k))) (y % ts.prod) c) := by
        funext y c
        have hmodw : (σ + y) % ts.prod = y % ts.prod := by rw [hm, Nat.mul_add_mod]
        have hdivw : (σ + y) / ts.prod * ts.prod = σ + y / ts.prod * ts.prod := by
          rw [hm, Nat.mul_add_div hB', add_mul, mul_comm m ts.prod]
        rw [ih hpos' (σ + y), hdivw, hmodw]
        simp only [Nat.add_assoc]
      rw [hL, hR, hFG]

theorem axisIterEq : Work.SynFFT.AxisIterProp := by
  intro r ts sgn u hpos p hp
  rw [axisIterN_blk r sgn u ts hpos p]
  have hmod : p % ts.prod = p := Nat.mod_eq_of_lt hp
  have hdiv : p / ts.prod * ts.prod = 0 := by rw [Nat.div_eq_of_lt hp, Nat.zero_mul]
  have hw : (fun k => u (p / ts.prod * ts.prod + k)) = u := by
    rw [hdiv]; funext k; simp
  rw [hmod, hw]

end Work.SynFFT
