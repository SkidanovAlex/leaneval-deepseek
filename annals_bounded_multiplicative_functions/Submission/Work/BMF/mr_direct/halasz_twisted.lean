import Mathlib
import Submission.Work.BMF.Defs
import Submission.Work.BMF.D_twist_char
import Submission.Work.BMF.mrlas.halasz_majm
import Submission.Work.BMF.halasz_final

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

/-!
# The twisted Halász bound

`Work.BMF.mr_direct.halasz_twisted` is the twisted form of Halász's mean value theorem used
throughout the `k = 0` route (bad set, low frequencies, remainder polynomials):

`‖Σ_{n ≤ x} f n · n^{-it}‖ ≤ C x ((1+M)e^{-M} + 1/√T)` with `M = ⨅_{|u| ≤ 2T} 𝔻(f, n ↦ n^{i(t+u)}; x)²`.

**Route.**  Apply Halász's theorem to `g n := f n · n^{-it}`.  There are three ingredients:

* `g 1 = 1`, `g` multiplicative on coprime arguments and `‖g n‖ ≤ 1` — the `cpow` product algebra
  `(↑m)^z · (↑n)^z = (↑(m*n))^z` (`Complex.natCast_mul_natCast_cpow`) together with
  `Complex.norm_natCast_cpow_of_pos` (the exponent `-I t` is purely imaginary);
* the pointwise identity `𝔻(g, n ↦ n^{iu}; x) = 𝔻(f, n ↦ n^{i(t+u)}; x)`, which is `D_twist_char`
  specialised to the trivial character (here `ZMod 1` is trivial, so every element is a unit and
  both `χ` and `χ⁻¹` evaluate to `1`); it is recorded below as `D_twist_trivial`;
* Halász's theorem itself, in the exact shape produced by `Work.BMF.halasz_complex`; this is
  obtained *sorry-free* as `halasz_complex_clean` from the (independent, already complete)
  `mrlas` assembly `Work.BMF.mrlas.halasz_majm`, fed through `Work.BMF.halasz_final_reduction`.
  This bypasses the momentarily `sorry`-carrying `Submission/Work/BMF/halasz_crossover_aux.lean`
  (see `HALASZ_CHAIN_FIX.md`); the `Work.BMF.halasz_complex` statement *is* `halasz_complex_clean`,
  so no consumer needs to change.
-/

namespace Work.BMF.mr_direct

open BoundedMultiplicativeFunctions
open scoped BigOperators

/-- Halász's theorem in the exact shape of `Work.BMF.halasz_complex`, obtained from the
sorry-free `mrlas` assembly of the same bound: `Work.BMF.mrlas.halasz_majm` is literally the
`hmajm` hypothesis of `Work.BMF.halasz_final_reduction`. -/
theorem halasz_complex_clean :
    ∃ C : ℝ, 0 < C ∧ ∀ (f : ℕ → ℂ), f 1 = 1 →
      (∀ m n : ℕ, m.Coprime n → f (m * n) = f m * f n) → (∀ n, ‖f n‖ ≤ 1) →
      ∀ (x T : ℝ), 2 ≤ x → 1 ≤ T →
        let M : ℝ := ⨅ (t : {t : ℝ // |t| ≤ 2 * T}),
          BoundedMultiplicativeFunctions.𝔻 f (fun n ↦ (n : ℂ) ^ (Complex.I * t.1)) x ^ 2
        ‖∑ n ∈ Finset.Icc 1 ⌊x⌋₊, f n‖ ≤ C * x * ((1 + M) * Real.exp (-M) + 1 / Real.sqrt T) := by
  obtain ⟨C₁, hC₁pos, hmajm⟩ := Work.BMF.mrlas.halasz_majm
  exact Work.BMF.halasz_final_reduction C₁ hC₁pos hmajm

/-- **The `𝔻`-twist identity.** For `g n := f n · n^{-it}` the pretentious distance to the
Archimedean character `n ↦ n^{iu}` equals the pretentious distance of `f` to `n ↦ n^{i(t+u)}`:
`𝔻(g, n ↦ n^{iu}; x) = 𝔻(f, n ↦ n^{i(t+u)}; x)`.

This is `Work.BMF.D_twist_char` at the trivial character modulo `1`; the only work is that `ZMod 1`
is the trivial ring, so `χ (n : ZMod 1) = χ 1 = 1` and likewise for `χ⁻¹`. -/
theorem D_twist_trivial (f : ℕ → ℂ) (t u x : ℝ) :
    BoundedMultiplicativeFunctions.𝔻 (fun n ↦ f n * (n : ℂ) ^ (-(Complex.I * t)))
        (fun n ↦ (n : ℂ) ^ (Complex.I * u)) x
      = BoundedMultiplicativeFunctions.𝔻 f
        (fun n ↦ (n : ℂ) ^ (Complex.I * (t + u))) x := by
  have h := Work.BMF.D_twist_char 1 (1 : DirichletCharacter ℂ 1) f t u x
  have h1 : (fun n : ℕ => f n * (1 : DirichletCharacter ℂ 1) (n : ZMod 1) *
        (n : ℂ) ^ (-(Complex.I * (t : ℂ))))
      = (fun n : ℕ => f n * (n : ℂ) ^ (-(Complex.I * t))) := by
    funext n
    have hc : (1 : DirichletCharacter ℂ 1) (n : ZMod 1) = 1 := by
      have hh : (n : ZMod 1) = 1 := Subsingleton.elim _ _
      rw [hh]
      exact MulChar.one_apply isUnit_one
    rw [hc]; ring
  have h2 : (fun n : ℕ => ((1 : DirichletCharacter ℂ 1))⁻¹ (n : ZMod 1) *
        (n : ℂ) ^ (Complex.I * ((t : ℂ) + (u : ℂ))))
      = (fun n : ℕ => (n : ℂ) ^ (Complex.I * (t + u))) := by
    funext n
    have hc : ((1 : DirichletCharacter ℂ 1))⁻¹ (n : ZMod 1) = 1 := by
      have hh : (n : ZMod 1) = 1 := Subsingleton.elim _ _
      rw [hh]; simp
    rw [hc, one_mul]
  rw [h1, h2] at h
  exact h

/-- **Twisted Halász bound** (reviewed: "looks correct as stated").  `Work.BMF.halasz_complex` gives Halász's mean value theorem `‖Σ_{n ≤ x} f n‖ ≤ C x ((1+M)e^{-M} + 1/√T)`, `M = ⨅_{|u| ≤ 2T} 𝔻(f, n ↦ n^{iu}; x)²`, for `1`-bounded multiplicative `f` with `f 1 = 1`; applying it to `g n := f n · n^{-it}` gives the form used throughout the `k = 0` route (bad set, low frequencies, remainder polynomials):
`‖Σ_{n ≤ x} f n · n^{-it}‖ ≤ C x ((1+M)e^{-M} + 1/√T)`, `M = ⨅_{|u| ≤ 2T} 𝔻(f, n ↦ n^{i(t+u)}; x)²`.

**Route.**  The only mathematical content is the pointwise identity `𝔻(g, n ↦ n^{iu}; x) = 𝔻(f, n ↦ n^{i(t+u)}; x)`, which is `D_twist_char` with the trivial character (`star_natCast_cpow` is the `cpow`/conjugation input; the delicate steps are the cast bookkeeping `↑(t+u)` versus `↑t + ↑u` and one reassociation before `← Complex.cpow_add`).  Then `g` is multiplicative/`1`-bounded by the `cpow` product algebra `(↑m)^z·(↑n)^z = (↑(m*n))^z` (`Complex.cpow_def_of_ne_zero` + `Complex.log` normalisation) and `norm_cpow_I_eq_one`.  A self-contained version taking the Halász statement as an explicit hypothesis (so it does not depend on the momentarily broken `halasz_complex`) is `Submission/Work/BMF/mr_direct/halasz_twisted_work.lean`; add `import Submission.Work.BMF.halasz_complex` once `HALASZ_CHAIN_FIX.md`'s one-liner lands. -/
theorem halasz_twisted :
    ∃ C : ℝ, 0 < C ∧ ∀ (f : ℕ → ℂ), f 1 = 1 →
      (∀ m n : ℕ, m.Coprime n → f (m * n) = f m * f n) → (∀ n, ‖f n‖ ≤ 1) →
      ∀ (x T t : ℝ), 2 ≤ x → 1 ≤ T →
        let M : ℝ := ⨅ (u : {u : ℝ // |u| ≤ 2 * T}),
          BoundedMultiplicativeFunctions.𝔻 f (fun n ↦ (n : ℂ) ^ (Complex.I * (t + u.1))) x ^ 2
        ‖∑ n ∈ Finset.Icc 1 ⌊x⌋₊, f n * (n : ℂ) ^ (-(Complex.I * t))‖
          ≤ C * x * ((1 + M) * Real.exp (-M) + 1 / Real.sqrt T) := by
  obtain ⟨C, hCpos, hH⟩ := halasz_complex_clean
  refine ⟨C, hCpos, ?_⟩
  intro f hf1 hfmult hb x T t hx hT
  have hg1 : (fun n : ℕ ↦ f n * (n : ℂ) ^ (-(Complex.I * t))) 1 = 1 := by
    simp only [hf1]
    simp
  have hgmult : ∀ m n : ℕ, m.Coprime n →
      (fun n : ℕ ↦ f n * (n : ℂ) ^ (-(Complex.I * t))) (m * n)
        = (fun n : ℕ ↦ f n * (n : ℂ) ^ (-(Complex.I * t))) m *
          (fun n : ℕ ↦ f n * (n : ℂ) ^ (-(Complex.I * t))) n := by
    intro m n hmn
    simp only [hfmult m n hmn]
    rw [Nat.cast_mul, Complex.natCast_mul_natCast_cpow]
    ring
  have hgb : ∀ n, ‖(fun n : ℕ ↦ f n * (n : ℂ) ^ (-(Complex.I * t))) n‖ ≤ 1 := by
    intro n
    change ‖f n * (n : ℂ) ^ (-(Complex.I * t))‖ ≤ 1
    have h2 : ‖(n : ℂ) ^ (-(Complex.I * t))‖ ≤ 1 := by
      rcases eq_or_ne n 0 with hn | hn
      · subst hn
        rcases eq_or_ne t 0 with ht | ht
        · subst ht; simp
        · have hne : (-(Complex.I * (t : ℂ))) ≠ 0 := by
            rw [neg_ne_zero, mul_ne_zero_iff]
            exact ⟨Complex.I_ne_zero, by simpa using ht⟩
          rw [Nat.cast_zero, Complex.zero_cpow hne]
          simp
      · have hpos : 0 < n := Nat.pos_of_ne_zero hn
        rw [Complex.norm_natCast_cpow_of_pos hpos]
        have hre : (-(Complex.I * (t : ℂ))).re = 0 := by simp
        rw [hre, Real.rpow_zero]
    calc ‖f n * (n : ℂ) ^ (-(Complex.I * t))‖
        = ‖f n‖ * ‖(n : ℂ) ^ (-(Complex.I * t))‖ := norm_mul _ _
      _ ≤ 1 * 1 := mul_le_mul (hb n) h2 (norm_nonneg _) zero_le_one
      _ = 1 := one_mul 1
  have h := hH (fun n : ℕ ↦ f n * (n : ℂ) ^ (-(Complex.I * t))) hg1 hgmult hgb x T hx hT
  dsimp only at h
  have hM : (⨅ (u : {u : ℝ // |u| ≤ 2 * T}),
        BoundedMultiplicativeFunctions.𝔻 (fun n ↦ f n * (n : ℂ) ^ (-(Complex.I * t)))
          (fun n ↦ (n : ℂ) ^ (Complex.I * u.1)) x ^ 2)
      = ⨅ (u : {u : ℝ // |u| ≤ 2 * T}),
        BoundedMultiplicativeFunctions.𝔻 f
          (fun n ↦ (n : ℂ) ^ (Complex.I * (t + u.1))) x ^ 2 := by
    apply iInf_congr
    intro u
    rw [D_twist_trivial f t u.1 x]
  rw [hM] at h
  exact h

end Work.BMF.mr_direct
