import Mathlib
import Submission.Work.Peluse.Concat.boxNormPow_succ_ge_general

/-!
# Level raising for the box-norm power, in the `Fin.append` normal form

`Work.Peluse.Concat.two_mul_boxNormPow_succ_ge_complex` is the Gowers–Cauchy–Schwarz step

`(‖f‖^{2^t}_{□^t_{Q₁,…,Q_t}})^2 ≤ 2 ‖f‖^{2^{t+1}}_{□^{t+1}_{Q₁,…,Q_{t+1}}}`,

whose last direction set is the one carrying the shift bound.  Iterating it `b` times along the
`b` *last* directions of the concatenated family `Fin.append P L` gives the level raising

`(1/2)^{2^b - 1} · (‖f‖^{2^a}_{□^a_{P}})^{2^b} ≤ ‖f‖^{2^{a+b}}_{□^{a+b}_{Fin.append P L}}`

of `boxNormPow_level_raise` below, with the *exact* constant produced by the iteration (each step
costs `1/2`, and the `b`-fold iteration costs `(1/2)^{2^b-1}`).

The work is done by `level_raise_gen`, stated for an arbitrary direction family `Q : Fin (a+b) → _`
whose `a`-prefix is the family of the lower-level norm; the top-level statement is the instantiation
`Q = Fin.append P L`, where the prefix is `P` by `Fin.append_left`.
-/

namespace Work.Peluse.LadderA

open Work.Peluse

/-- **Level raising for the box-norm power, prefix form.**  For a direction family
`Q : Fin (a+b) → Finset ℤ` whose entries are nonempty subsets of `[-N,N]` and a function `f`
vanishing off `symIcc N`,
`(1/2)^{2^b-1} · (‖f‖^{2^a}_{□^a_{Q ∘ castAdd b}})^{2^b} ≤ ‖f‖^{2^{a+b}}_{□^{a+b}_Q}`.
Proved by iterating `Concat.two_mul_boxNormPow_succ_ge_complex` along the last `b` directions, whose
shift bound is the only one the step uses. -/
lemma level_raise_gen (a : ℕ) : ∀ b : ℕ, ∀ {N : ℕ}, 0 < N →
    ∀ (Q : Fin (a+b) → Finset ℤ) (f : ℤ → ℂ),
    (∀ i, (Q i).Nonempty) → (∀ i z, z ∈ Q i → |z| ≤ (N:ℤ)) →
    (∀ x, x ∉ symIcc N → f x = 0) →
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
      (fun y hy => hbd (Fin.last (a+b)) y hy) hsup
    have hIH := ih hN (fun i : Fin (a+b) => Q (Fin.castSucc i)) f
      (fun i => hQ (Fin.castSucc i)) (fun i z hz => hbd (Fin.castSucc i) z hz) hsup
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

theorem boxNormPow_level_raise {a b : ℕ} (hb : 0 < b) {N : ℕ} (hN : 0 < N)
    (P : Fin a → Finset ℤ) (L : Fin b → Finset ℤ) (f : ℤ → ℂ)
    (hP : ∀ i : Fin a, (P i).Nonempty) (hL : ∀ i : Fin b, (L i).Nonempty)
    (hbd : ∀ i : Fin (a + b), ∀ z : ℤ, z ∈ Fin.append P L i → |z| ≤ (N : ℤ))
    (hsup : Work.Peluse.SupportIn f N) (h1 : ∀ x : ℤ, ‖f x‖ ≤ 1) :
    ((1 : ℝ) / 2) ^ (2 ^ b - 1) * (Work.Peluse.boxNormPow a P (Work.Peluse.symIcc N) f) ^ (2 ^ b)
      ≤ Work.Peluse.boxNormPow (a + b) (Fin.append P L) (Work.Peluse.symIcc N) f := by
  have hsup' : ∀ x : ℤ, x ∉ symIcc N → f x = 0 := by
    intro x hx
    refine hsup x ?_
    have hx' : ¬ |x| ≤ (N : ℤ) := fun h => hx (Work.Peluse.PET.mem_symIcc_iff_abs.mpr h)
    have hlt : (N : ℤ) < |x| := lt_of_not_ge hx'
    have h3 : (N : ℤ) < (x.natAbs : ℤ) := by rw [Int.natCast_natAbs]; exact hlt
    exact_mod_cast h3
  have hQ : ∀ i : Fin (a+b), ((Fin.append P L) i).Nonempty := by
    intro i
    induction i using Fin.addCases with
    | left j => rw [Fin.append_left P L j]; exact hP j
    | right j => rw [Fin.append_right P L j]; exact hL j
  have key := level_raise_gen a b hN (Fin.append P L) f hQ (fun i z hz => hbd i z hz) hsup'
  have hfam : (fun i : Fin a => (Fin.append P L) (Fin.castAdd b i)) = P := by
    funext i; exact Fin.append_left P L i
  rw [hfam] at key
  exact key

end Work.Peluse.LadderA
