/-
# A `T`-triple in the socket lies in `Wm1`

If `τ`, `τ+1` and `τ+2` all lie in the socket `O = U0 ∪ W1 ∪ Wm1`, then `τ` lies in `Wm1`.
This is the thinness geometry lemma that makes the first recurrence `(T-I)²F₂ = -T2op gauss`
*define* `F₂` on the whole of `Wm1`: the values `F₂(τ+1)` and `F₂(τ+2)` appearing on the
right are known, because `τ+1 ∈ U0` and `τ+2 ∈ W1`.

The proof is purely about real parts.  The three pieces of `O` occupy the disjoint strips
`(-1,1)`, `(3/4,5/4)` and `(-5/4,-3/4)`, so any point of `O` has `Re` in `(-5/4,5/4)`
(`O_re_lt`, `O_re_gt`).  If `τ ∈ U0` then `Re(τ+2) = Re τ + 2 < 5/4` forces `Re τ < -3/4`;
then `Re(τ+1) ∈ (-1/4,1/4)` and `Re(τ+2) ∈ (1,5/4)` single out `U0` and `W1` respectively,
and the thinness inequality `|Re τ + 1| < thin (Im τ)` is the thinness inequality of `τ+2 ∈ W1`
transported back.  `τ ∈ W1` is impossible (`Re(τ+1) > 7/4 > 5/4`), and `τ ∈ Wm1` is the
conclusion.
-/
import Mathlib
import Submission.Work.CKFinal.Socket.Region

open UpperHalfPlane

namespace Work.CKFinal.Socket

/-- A point of `W1` satisfies the thinness inequality around `Re τ = 1`. -/
lemma W1_thin {ℓ : Work.Kernels.LogLambdaData} {d : ℕ} {hd : d = 8 ∨ d = 24}
    {τ : ℍ} (h : τ ∈ W1 ℓ d hd) : |τ.re - 1| < thin τ.im := by
  obtain ⟨s, hs, hb⟩ := mem_W1.mp h
  exact winBall_mem_re ℓ d hd hb

/-- Every point of the socket has `Re` below `5/4`. -/
lemma O_re_lt {ℓ : Work.Kernels.LogLambdaData} {d : ℕ} {hd : d = 8 ∨ d = 24}
    {τ : ℍ} (h : τ ∈ O ℓ d hd) : τ.re < 5 / 4 := by
  rcases h with (h | h) | h
  · exact lt_trans (Work.CKFinal.mem_U0_iff.mp h).2.1 (by norm_num)
  · exact (W1_re_bounds h).2
  · exact lt_trans (Wm1_re_bounds h).2 (by norm_num)

/-- Every point of the socket has `Re` above `-5/4`. -/
lemma O_re_gt {ℓ : Work.Kernels.LogLambdaData} {d : ℕ} {hd : d = 8 ∨ d = 24}
    {τ : ℍ} (h : τ ∈ O ℓ d hd) : -5 / 4 < τ.re := by
  rcases h with (h | h) | h
  · exact lt_trans (by norm_num) (Work.CKFinal.mem_U0_iff.mp h).1
  · exact lt_trans (by norm_num) (W1_re_bounds h).1
  · exact (Wm1_re_bounds h).1

theorem T_triple_mem_Wm1 (ℓ : Work.Kernels.LogLambdaData) (d : ℕ) (hd : d = 8 ∨ d = 24)
    {τ : UpperHalfPlane} (h1 : τ ∈ Work.CKFinal.Socket.O ℓ d hd)
    (h2 : (1 : ℝ) +ᵥ τ ∈ Work.CKFinal.Socket.O ℓ d hd)
    (h3 : (2 : ℝ) +ᵥ τ ∈ Work.CKFinal.Socket.O ℓ d hd) :
    τ ∈ Work.CKFinal.Socket.Wm1 ℓ d hd := by
  by_cases hW : τ ∈ Wm1 ℓ d hd
  · exact hW
  · rw [mem_Wm1]
    -- `Re (τ+1) < 5/4` and `Re (τ+2) < 5/4`
    have h2re : ((1 : ℝ) +ᵥ τ).re < 5 / 4 := O_re_lt h2
    rw [vadd_one_re] at h2re
    have h3re : ((2 : ℝ) +ᵥ τ).re < 5 / 4 := O_re_lt h3
    rw [vadd_two_re] at h3re
    rw [O] at h1
    rcases h1 with (h1 | h1) | h1
    · -- `τ ∈ U0`: `Re τ ∈ (-1,-3/4)`
      obtain ⟨hx1, hx2, -⟩ := Work.CKFinal.mem_U0_iff.mp h1
      have hxlt : τ.re < -3 / 4 := by linarith
      -- `τ+1 ∈ U0`, because its real part lies in `(-1/4,1/4)`
      have hU0 : (1 : ℝ) +ᵥ τ ∈ U0 := by
        rw [O] at h2
        rcases h2 with (h2 | h2) | h2
        · exact h2
        · exfalso
          have hb := (W1_re_bounds h2).1
          rw [vadd_one_re] at hb
          linarith
        · exfalso
          have hb := (Wm1_re_bounds h2).2
          rw [vadd_one_re] at hb
          linarith
      -- `τ+2 ∈ W1`, because its real part lies in `(1,5/4)`
      have hW1 : (2 : ℝ) +ᵥ τ ∈ W1 ℓ d hd := by
        rw [O] at h3
        rcases h3 with (h3 | h3) | h3
        · exfalso
          have hb := (Work.CKFinal.mem_U0_iff.mp h3).2.1
          rw [vadd_two_re] at hb
          linarith
        · exact h3
        · exfalso
          have hb := (Wm1_re_bounds h3).2
          rw [vadd_two_re] at hb
          linarith
      refine ⟨hU0, hW1, ?_⟩
      -- the thinness inequality of `τ+2 ∈ W1`, transported back to `τ`
      have hthin := W1_thin hW1
      rw [vadd_two_re] at hthin
      have hre : τ.re + 2 - 1 = τ.re + 1 := by ring
      rw [hre] at hthin
      simpa using hthin
    · -- `τ ∈ W1` is impossible: `Re (τ+1) > 7/4 > 5/4`
      exfalso
      have hb := (W1_re_bounds h1).1
      linarith
    · exact absurd h1 hW

end Work.CKFinal.Socket
