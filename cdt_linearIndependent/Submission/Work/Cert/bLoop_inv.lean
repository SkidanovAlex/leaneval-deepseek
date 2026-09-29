import Mathlib
import Submission.Work.Cert.ThetaDefs
import Submission.Work.Cert.bstep_por_le
import Submission.Work.Cert.bstep_psr_le
import Submission.Work.Cert.bstep_num
import Submission.Work.Cert.bstep_Br_le
import Submission.Work.Cert.binv_base1

/-!
# The `B`-accumulator loop invariant (`Work.Cert.BInv` at `k = KTH = 12`)

`bLoop` runs `KTH = 12` steps of `bStep`, starting from
`⟨qr, qi, S, 0, S, 0, m, S, 0⟩` (i.e. `por = qr, poi = qi`, `psr = S, psi = 0`,
`Br = S, Bi = 0`, `mo = m`, `ms = S`, `dB = 0`).  The `k`-th iterate satisfies `BInv k`, the
invariant of `ThetaDefs.lean`:

* `por/poi` approximate `q^(2k+1)` (`q = qc qr qi`) with error `≤ 16/S`;
* `psr/psi` approximate `q^(k²)` with error `≤ 8k²/S`;
* the integer budgets `ms`, `mo` dominate `S·μ^(k²)`, `S·μ^(2k+1)` (`μ = mub m`), where
  `μ ≤ 79/100` bounds `‖q‖`;
* `dB` dominates the accumulated rounding/mean-value budget `Bd2 k + BdM2 m rq k`;
* `Br/Bi` approximate the partial sum `Bsum q k` with error `≤ Bd2 k/S`.

The proof is an induction on `k`.  The base case `k = 1` is the single explicit computation after
the first step (where `md S x = x`, `mu S x = x` are exact), and the step `k → k+1` for `1 ≤ k` is
assembled from the four contraction lemmas `bstep_por_le`, `bstep_psr_le`, `bstep_Br_le` and the
budget lemma `bstep_num`.
-/

namespace Work.Cert

open Complex Finset

noncomputable section

/-! ## Elementary facts about the arithmetic layer -/

/-- `cx` of a positive-scale mantissa vanishes at the origin. -/
lemma bl_cx_S_zero : cx S 0 = 1 := by
  simp only [cx]; push_cast; norm_num [S]

/-- The partial sums of `thetaB` satisfy `Bsum q (k+1) = Bsum q k + 2·(-1)^(k+1)·q^((k+1)²)`. -/
lemma bl_Bsum_succ (q : ℂ) (k : ℕ) :
    Bsum q (k+1) = Bsum q k + 2 * (-1:ℂ)^(k+1) * q^((k+1)^2) := by
  simp only [Bsum, Finset.sum_range_succ]
  ring

/-- The integer sign `if n % 2 = 1 then -1 else 1` of `bStep` is `(-1)^n` in `ℂ`. -/
lemma bl_sgc (n : ℕ) : (((if n % 2 = 1 then (-1:ℤ) else 1)) : ℂ) = (-1:ℂ)^n := by
  by_cases h : n % 2 = 1
  · rw [if_pos h]
    push_cast
    exact (Odd.neg_one_pow (α := ℂ) (Nat.odd_iff.mpr h)).symm
  · rw [if_neg h]
    push_cast
    exact (Even.neg_one_pow (α := ℂ)
      (Nat.not_odd_iff_even.mp (fun ho => h (Nat.odd_iff.mp ho)))).symm

/-! ## The parametrisation of the loop -/

/-- `bLoop` with fuel `fuel+1` starting at counter `n` applies the steps `n, …, n+fuel`; the last
of them is `bStep (n+fuel)`. -/
lemma bl_bLoop_eq (q2r q2i rq m : ℤ) : ∀ (fuel n : ℕ) (s : BS),
    bLoop q2r q2i rq m (fuel+1) n s
      = bStep q2r q2i rq m (n+fuel) (bLoop q2r q2i rq m fuel n s) := by
  intro fuel
  induction fuel with
  | zero => intro n s; rfl
  | succ fuel ih =>
    intro n s
    rw [show bLoop q2r q2i rq m (fuel+1+1) n s
        = bLoop q2r q2i rq m (fuel+1) (n+1) (bStep q2r q2i rq m n s) from rfl]
    rw [ih (n+1) (bStep q2r q2i rq m n s)]
    rw [show n + 1 + fuel = n + (fuel + 1) by omega]
    rfl

/-- `bLoop` starting at counter `1`: `k+1` steps are `k` steps followed by `bStep (k+1)`. -/
lemma bl_bLoop_succ (q2r q2i rq m : ℤ) (k : ℕ) (s : BS) :
    bLoop q2r q2i rq m (k+1) 1 s = bStep q2r q2i rq m (k+1) (bLoop q2r q2i rq m k 1 s) := by
  rw [bl_bLoop_eq q2r q2i rq m k 1 s]
  congr 1
  omega

/-! ## The `k = 0` state (used only to start the induction) -/

lemma bl_binv_zero (qr qi rq m : ℤ) (hm : 1 ≤ m) (hμ : mub m ≤ 79/100) :
    BInv qr qi rq m 0 ⟨qr, qi, S, 0, S, 0, m, S, 0⟩ := by
  have hSpos : (0:ℝ) < (S:ℝ) := thS_pos
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · simp only [qc, Nat.mul_zero, zero_add, pow_one, sub_self, norm_zero]
    positivity
  · simp [bl_cx_S_zero]
  · simp only [Nat.mul_zero, pow_zero]
    rw [div_self (ne_of_gt hSpos)]
  · simp only [Nat.mul_zero, zero_add, pow_one]
    rfl
  · simp [Bd2, BdM2]
  · simp [Bsum, Bd2, bl_cx_S_zero]

/-! ## The induction step -/

/-- One step of the `B` accumulator preserves the invariant, for `1 ≤ k ≤ 11`. -/
theorem bl_BInv_step
    (hcxmul : ∀ a b c d : ℤ, ‖cx (cmr a b c d) (cmi a b c d) - cx a b * cx c d‖ ≤ 3 / ((S : ℝ)))
    (qr qi rq m : ℤ) (hm : 1 ≤ m) (hrq : 0 ≤ rq) (hμ : mub m ≤ 79/100)
    (hz : ‖qc qr qi‖ ≤ mub m) {k : ℕ} (hk1 : 1 ≤ k) (hk11 : k ≤ 11) {s : BS}
    (hs : BInv qr qi rq m k s) :
    BInv qr qi rq m (k+1) (bStep (cmr qr qi qr qi) (cmi qr qi qr qi) rq m (k+1) s) := by
  obtain ⟨h1, h2, h3, h4, h5, h6⟩ := hs
  have h2' := bstep_psr_le hcxmul qr qi m hk1 hk11 hμ hz h1 h2
  have h34 := bstep_num rq m k hm hrq hμ h3 h4 h5
  simp only [BInv, bStep]
  exact ⟨bstep_por_le hcxmul qr qi m hμ hz h1, h2', h34.1, h34.2.1, h34.2.2,
         bstep_Br_le qr qi h6 h2'⟩

/-- The invariant holds after each of the first `12` steps of the loop. -/
theorem bl_BInv_all (hcxmul : ∀ a b c d : ℤ, ‖cx (cmr a b c d) (cmi a b c d) - cx a b * cx c d‖ ≤ 3 / ((S : ℝ)))
    (qr qi rq m : ℤ) (hm : 1 ≤ m) (hrq : 0 ≤ rq) (hμ : mub m ≤ 79/100)
    (hz : ‖qc qr qi‖ ≤ mub m) :
    ∀ k, k ≤ 12 → BInv qr qi rq m k
      (bLoop (cmr qr qi qr qi) (cmi qr qi qr qi) rq m k 1 ⟨qr, qi, S, 0, S, 0, m, S, 0⟩) := by
  intro k
  induction k with
  | zero => intro _; exact bl_binv_zero qr qi rq m hm hμ
  | succ k ih =>
    intro hk
    rw [bl_bLoop_succ]
    rcases Nat.eq_zero_or_pos k with h | h
    · subst h
      exact binv_base1 hcxmul qr qi rq m hm hrq hμ hz
    · exact bl_BInv_step hcxmul qr qi rq m hm hrq hμ hz h (by omega) (ih (by omega))

theorem bLoop_inv (hcxmul : ∀ a b c d : ℤ, ‖cx (cmr a b c d) (cmi a b c d) - cx a b * cx c d‖ ≤ 3 / ((S : ℝ)))
    (qr qi rq m : ℤ) (hm : 1 ≤ m) (hrq : 0 ≤ rq) (hμ : mub m ≤ 79 / 100) (hz : ‖qc qr qi‖ ≤ mub m) :
    BInv qr qi rq m KTH (bLoop (cmr qr qi qr qi) (cmi qr qi qr qi) rq m KTH 1 ⟨qr, qi, S, 0, S, 0, m, S, 0⟩) := by
  have hK : KTH = 12 := rfl
  rw [hK]
  exact bl_BInv_all hcxmul qr qi rq m hm hrq hμ hz 12 le_rfl

end

end Work.Cert
