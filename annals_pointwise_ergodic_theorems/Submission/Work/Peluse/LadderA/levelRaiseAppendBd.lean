import Mathlib
import Submission.Work.Peluse.LadderA.boxNormPow_level_raise

/-!
# Level raising for the box-norm power with the shift bound only on the appended directions

`Work.Peluse.LadderA.level_raise_gen` iterates Peluse's Gowers--Cauchy--Schwarz step

`(‖f‖^{2^t}_{□^t_{Q₁,…,Q_t}})^2 ≤ 2 ‖f‖^{2^{t+1}}_{□^{t+1}_{Q₁,…,Q_{t+1}}}`

along the last `b` directions of a concatenated family and produces
`(1/2)^{2^b-1}·(‖f‖^{2^a}_{□^a_P})^{2^b} ≤ ‖f‖^{2^{a+b}}_{□^{a+b}_{Fin.append P L}}`.  In
`level_raise_gen` the hypotheses are stated *uniformly* over all `a+b` directions (each direction
set is bounded by `N`).  But the GCS step `Concat.two_mul_boxNormPow_succ_ge_complex` uses the
bound **only on the last direction** — the one carrying the shift — and it imposes no bound
`‖f‖ ≤ 1` on `f`.  Hence the level raising holds with the bound required only on the `L`-directions,
which is the form needed by the ladder (`Work.Peluse.LadderA.levelRaiseAppendBd`).

The work is done by `level_raise_gen_last`, whose hypothesis is that the directions of index `≥ a`
(the ones that get consumed by the iteration) are bounded by `N`; the main theorem instantiates it
at `Q = Fin.append P L`, where those directions are exactly the `L`-entries.
-/

set_option maxHeartbeats 1600000

namespace Work.Peluse.LadderA

open Work.Peluse

/-- **Level raising with the shift bound only on the consumed directions.**  For a direction family
`Q : Fin (a+b) → Finset ℤ` whose entries are nonempty, whose entries of index `≥ a` are subsets of
`[-N,N]`, and a function `f` vanishing off `symIcc N`,
`(1/2)^{2^b-1} · (‖f‖^{2^a}_{□^a_{Q ∘ castAdd b}})^{2^b} ≤ ‖f‖^{2^{a+b}}_{□^{a+b}_Q}`.
No bound on `f` itself and no bound on the first `a` directions is needed: the GCS step used in the
iteration only ever sees the last direction. -/
lemma level_raise_gen_last (a : ℕ) : ∀ b : ℕ, ∀ {N : ℕ}, 0 < N →
    ∀ (Q : Fin (a+b) → Finset ℤ) (f : ℤ → ℂ),
    (∀ i, (Q i).Nonempty) →
    (∀ i : Fin (a+b), a ≤ i.val → ∀ z : ℤ, z ∈ Q i → |z| ≤ (N : ℤ)) →
    (∀ x : ℤ, x ∉ symIcc N → f x = 0) →
    ((1:ℝ)/2)^(2^b - 1) * (boxNormPow a (fun i => Q (Fin.castAdd b i)) (symIcc N) f)^(2^b)
      ≤ boxNormPow (a+b) Q (symIcc N) f := by
  intro b
  induction b with
  | zero =>
    intro N hN Q f hQ hbd hsup
    have h2 : (2:ℕ)^0 - 1 = 0 := rfl
    rw [h2, pow_zero, one_mul, pow_zero, pow_one]
    exact le_of_eq (by congr 1)
  | succ b ih =>
    intro N hN Q f hQ hbd hsup
    have hstep := Work.Peluse.Concat.two_mul_boxNormPow_succ_ge_complex (n := a+b) Q hN f hQ
      (fun y hy => hbd (Fin.last (a+b)) (by simp) y hy) hsup
    have hIH := ih hN (fun i : Fin (a+b) => Q (Fin.castSucc i)) f
      (fun i => hQ (Fin.castSucc i)) (fun i hi z hz => hbd (Fin.castSucc i) hi z hz) hsup
    have hfam : (fun i : Fin a => Q (Fin.castAdd b i).castSucc)
        = (fun i : Fin a => Q (Fin.castAdd (b+1) i)) := by
      funext i
      exact congrArg Q (Fin.ext rfl)
    rw [hfam] at hIH
    set X : ℝ := boxNormPow a (fun i : Fin a => Q (Fin.castAdd (b+1) i)) (symIcc N) f with hXdef
    set Z : ℝ := boxNormPow (a+b) (fun i : Fin (a+b) => Q i.castSucc) (symIcc N) f with hZdef
    have hX0 : 0 ≤ X := by rw [hXdef]; exact norm_nonneg _
    have hc0 : (0:ℝ) < (1/2)^(2^b - 1) := by positivity
    have hsq : ((1/2:ℝ)^(2^b - 1) * X^(2^b))^2 ≤ Z^2 :=
      pow_le_pow_left₀ (mul_nonneg hc0.le (pow_nonneg hX0 _)) hIH 2
    have hcoe : ((1/2:ℝ)^(2^b-1))^2 = (1/2)^(2*(2^b-1)) := by
      rw [← pow_mul]; congr 1; ring
    have hpowX : (X^(2^b))^2 = X^(2^(b+1)) := by
      rw [← pow_mul]; congr 1
    have hid : ((1/2:ℝ)^(2^b - 1) * X^(2^b))^2
        = (1/2)^(2*(2^b-1)) * X^(2^(b+1)) := by
      rw [mul_pow, hcoe, hpowX]
    rw [hid] at hsq
    have he : 2^(b+1) - 1 = 2*(2^b-1) + 1 := by
      have h1 : 1 ≤ 2^b := Nat.one_le_two_pow
      have h2 : 2^(b+1) = 2 * 2^b := by rw [pow_succ']
      omega
    have hle : (1/2:ℝ)^(2*(2^b-1)) * X^(2^(b+1))
        ≤ 2 * boxNormPow (a+(b+1)) Q (symIcc N) f := le_trans hsq hstep
    rw [he, pow_succ]
    nlinarith [hle]

/-- **Level raising for the box-norm power in the `Fin.append` normal form, with the shift bound
required only on the appended directions.**  For direction families `P : Fin a → Finset ℤ` and
`L : Fin b → Finset ℤ` with nonempty entries, `L i ⊆ [-N,N]`, and `f` vanishing off `symIcc N`,
`(1/2)^{2^b-1} · (‖f‖^{2^a}_{□^a_P})^{2^b} ≤ ‖f‖^{2^{a+b}}_{□^{a+b}_{Fin.append P L}}`. -/
theorem levelRaiseAppendBd {a b : ℕ} {N : ℕ} (hN : 0 < N)
    (P : Fin a → Finset ℤ) (L : Fin b → Finset ℤ) (f : ℤ → ℂ)
    (hP : ∀ i : Fin a, (P i).Nonempty) (hL : ∀ i : Fin b, (L i).Nonempty)
    (hLbd : ∀ i : Fin b, ∀ z : ℤ, z ∈ L i → |z| ≤ (N : ℤ))
    (hsup : ∀ x : ℤ, x ∉ Work.Peluse.symIcc N → f x = 0) :
    ((1 : ℝ) / 2) ^ (2 ^ b - 1) * (Work.Peluse.boxNormPow a P (Work.Peluse.symIcc N) f) ^ (2 ^ b)
      ≤ Work.Peluse.boxNormPow (a + b) (Fin.append P L) (Work.Peluse.symIcc N) f := by
  have hQ : ∀ i : Fin (a+b), ((Fin.append P L) i).Nonempty := by
    intro i
    induction i using Fin.addCases with
    | left j => rw [Fin.append_left P L j]; exact hP j
    | right j => rw [Fin.append_right P L j]; exact hL j
  have hbdl : ∀ i : Fin (a+b), a ≤ i.val → ∀ z : ℤ, z ∈ (Fin.append P L) i → |z| ≤ (N : ℤ) := by
    intro i hi z hz
    have hilt : i.val < a + b := i.isLt
    set j : Fin b := ⟨i.val - a, by omega⟩ with hj
    have hia : i = Fin.natAdd a j := by
      apply Fin.ext
      simp only [Fin.natAdd, Fin.val_mk, hj]
      omega
    rw [hia, Fin.append_right] at hz
    exact hLbd j z hz
  have key := level_raise_gen_last a b hN (Fin.append P L) f hQ hbdl hsup
  have hfam : (fun i : Fin a => (Fin.append P L) (Fin.castAdd b i)) = P := by
    funext i; exact Fin.append_left P L i
  rw [hfam] at key
  exact key

end Work.Peluse.LadderA
