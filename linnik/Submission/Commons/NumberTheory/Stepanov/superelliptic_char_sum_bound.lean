import Mathlib
import Submission.Commons.Algebra.Polynomial.hasseDeriv_mul_X_pow_prime_pow
import Submission.Commons.Algebra.Polynomial.hasseDeriv_mul_pow_degree
import Submission.Commons.Algebra.Polynomial.X_sub_C_pow_dvd_of_hasseDeriv_eval_eq_zero
import Submission.Commons.FieldTheory.Kummer.binomial_irreducible_iff_forall_prime
import Submission.Commons.NumberTheory.Stepanov.stevanov_count_gpow
import Submission.Commons.NumberTheory.Stepanov.gpow_main_g0
import Submission.Commons.NumberTheory.Stepanov.stepanov_numerics
import Submission.Commons.NumberTheory.Stepanov.stepanov_count_to_bound

namespace Commons.NumberTheory.Stepanov

open Polynomial

universe u

noncomputable section

set_option maxHeartbeats 4000000

/-!
# The Stepanov bound for the superelliptic character sum (Linnik, exponent `e`)

For `e ≥ 2`, `d ≥ 1` there is `C > 0` with

`#{x : g x ^ ((q-1)/e) = 1} ≤ q/e + C √q`

for every finite field `F` with `e ∣ q - 1` and every `g ∈ F[X]` of degree `≤ d` which is not a
constant multiple of a `p`-th power for any prime `p ∣ e`.

The two halves of Stepanov's method are already in the commons:

* `stevanov_witness_exists_of_arith` — the dimension count producing a nonzero family of
  auxiliary polynomials satisfying the Stepanov conditions (given the rank inequality `hdim`);
* `stevanov_count_gpow` — the counting lemma `T·M ≤ A₀ + q·B + (e-1)·k·deg g` for such a family
  with non-vanishing `R = ∑_r A_r(X,X^q)·g^(r·k)`.

The remaining non-trivial input is Stepanov's "good basis" lemma, i.e. the *non-vanishing* of `R`,
which is the injectivity of the Frobenius substitution `(A_r) ↦ ∑_r A_r(X,X^q) g^(rk)`; it is
isolated below as the hypothesis `hinj` and is supplied by the commons lemma
`Commons.NumberTheory.Stepanov.gpow_frobenius_eval_indep`.  The two purely arithmetic inputs
(`stepanov_numerics`: the choice of parameters satisfies the numerology;
`stepanov_count_to_bound`: reading off the final bound) are likewise isolated.
-/

/-- The explicit large-`q` constant obtained from the numerology. -/
def stepanovC1 (e d : ℕ) : ℝ :=
  1 / (2 * (e : ℝ)) + (1 + 4 * ((d : ℝ) + 4) + 4 * ((e : ℝ) - 1) * (d : ℝ) / (e : ℝ)) + 1

/-- The explicit threshold above which the numerology works. -/
def stepanovQ0 (e d : ℕ) : ℕ := (4 * e * (d + 1) + 2 * e ^ 3 * (d + 1) + 4) ^ 2

/-- From the hypothesis "`g` is not a constant multiple of a `p`-th power for `p ∣ e`",
`g` is nonzero and nonconstant. -/
lemma ne_zero_and_natDegree_pos {F : Type*} [Field F] (e : ℕ) (he : 2 ≤ e)
    (g : Polynomial F)
    (hnd : ∀ p : ℕ, p.Prime → p ∣ e → ∀ (a : F) (h : Polynomial F), g ≠ Polynomial.C a * h ^ p) :
    g ≠ 0 ∧ 1 ≤ g.natDegree := by
  obtain ⟨p, hp, hpe⟩ := Nat.exists_prime_and_dvd (by omega : e ≠ 1)
  have hg0 : g ≠ 0 := by
    intro h0
    exact hnd p hp hpe 0 0 (by rw [h0]; simp)
  refine ⟨hg0, ?_⟩
  rcases Nat.eq_zero_or_pos g.natDegree with h | h
  · exact absurd (hnd p hp hpe (g.coeff 0) 1
      (by rw [Polynomial.eq_C_of_natDegree_eq_zero h]; simp)) (by simp)
  · exact h

/-- **The Stepanov bound, conditional on the three inputs** (the non-vanishing lemma, the
numerology, and the final arithmetic). -/
theorem superelliptic_char_sum_bound_of_inputs
    (hinj : ∀ {K : Type u} [Field K] [Fintype K], ∀ (e : ℕ), 2 ≤ e → e ∣ Fintype.card K - 1 →
      ∀ (g : Polynomial K), g ≠ 0 →
      (∀ p : ℕ, p.Prime → p ∣ e → ∀ (a : K) (h : Polynomial K),
        g ≠ Polynomial.C a * h ^ p) →
      ∀ (A₀ : ℕ), e * A₀ + e ^ 3 * (g.natDegree + 1) < Fintype.card K →
      ∀ (A : Fin e → Polynomial (Polynomial K)),
      (∀ r i, ((A r).coeff i).natDegree ≤ A₀) →
      (∀ r, (A r).natDegree < Fintype.card K) →
      (∑ r : Fin e, (A r).eval ((Polynomial.X : Polynomial K) ^ Fintype.card K) *
        g ^ ((r : ℕ) * ((Fintype.card K - 1) / e)) = 0) →
      ∀ r, A r = 0)
    (hnumerics : ∀ (e d : ℕ), 2 ≤ e → 1 ≤ d → ∀ (D : ℕ), D ≤ d → ∀ (q : ℕ),
      stepanovQ0 e d ≤ q →
      1 ≤ Nat.sqrt q ∧ 2 * e ≤ Nat.sqrt q ∧ Nat.sqrt q ≤ (q - 1) / e ∧
      Nat.sqrt q / e + d + 3 < q ∧
      e * (Nat.sqrt q * Nat.sqrt q / (2 * e) + 1) + e ^ 3 * (D + 1) < q ∧
      Nat.sqrt q * ((Nat.sqrt q * Nat.sqrt q / (2 * e) + 1) + (Nat.sqrt q / e + d + 3) + 1)
        + D * (Nat.sqrt q * (Nat.sqrt q - 1) / 2)
        < e * (((Nat.sqrt q * Nat.sqrt q / (2 * e) + 1) + 1) * ((Nat.sqrt q / e + d + 3) + 1)))
    (hbound : ∀ (e d D q T : ℕ), 2 ≤ e → 1 ≤ d → D ≤ d → stepanovQ0 e d ≤ q →
      T * Nat.sqrt q ≤ Nat.sqrt q * Nat.sqrt q / (2 * e) + 1 + q * (Nat.sqrt q / e + d + 3)
        + (e - 1) * (((q - 1) / e) * D) →
      (T : ℝ) ≤ (q : ℝ) / (e : ℝ) + stepanovC1 e d * Real.sqrt (q : ℝ))
    (e d : ℕ) (he : 2 ≤ e) (hd : 1 ≤ d) :
    ∃ C : ℝ, 0 < C ∧
      ∀ (F : Type u) [Field F] [Fintype F] [DecidableEq F],
        e ∣ Fintype.card F - 1 →
        ∀ g : Polynomial F, g.natDegree ≤ d →
        (∀ p : ℕ, p.Prime → p ∣ e → ∀ (a : F) (h : Polynomial F),
          g ≠ Polynomial.C a * h ^ p) →
        (({x : F | g.eval x ^ ((Fintype.card F - 1) / e) = 1} : Set F).ncard : ℝ)
          ≤ (Fintype.card F : ℝ) / (e : ℝ) + C * Real.sqrt (Fintype.card F) := by
  have heR : (1 : ℝ) < (e : ℝ) := by
    have : (2 : ℝ) ≤ (e : ℝ) := by exact_mod_cast he
    linarith
  have hQ0pos : (0 : ℝ) < Real.sqrt ((stepanovQ0 e d : ℕ) : ℝ) := by
    apply Real.sqrt_pos.mpr
    have : 0 < stepanovQ0 e d := by
      rw [stepanovQ0]
      positivity
    exact_mod_cast this
  refine ⟨max (stepanovC1 e d) ((1 - 1 / (e : ℝ)) * Real.sqrt ((stepanovQ0 e d : ℕ) : ℝ)) + 1,
    ?_, ?_⟩
  · have h1 : (0 : ℝ) ≤ stepanovC1 e d := by rw [stepanovC1]; positivity
    have h2 : (0 : ℝ) ≤ (1 - 1 / (e : ℝ)) * Real.sqrt ((stepanovQ0 e d : ℕ) : ℝ) := by
      apply mul_nonneg _ (Real.sqrt_nonneg _)
      rw [sub_nonneg, div_le_one (by linarith [heR])]
      exact le_of_lt heR
    have h3 := le_max_left (stepanovC1 e d)
      ((1 - 1 / (e : ℝ)) * Real.sqrt ((stepanovQ0 e d : ℕ) : ℝ))
    have h4 := le_max_right (stepanovC1 e d)
      ((1 - 1 / (e : ℝ)) * Real.sqrt ((stepanovQ0 e d : ℕ) : ℝ))
    linarith
  intro F _ _ _ hdiv g hgd hnd
  obtain ⟨hg0, hD1⟩ := ne_zero_and_natDegree_pos e he g hnd
  set D := g.natDegree with hDdef
  have hDg : D ≤ d := hgd
  by_cases hbig : stepanovQ0 e d ≤ Fintype.card F
  · -- large `q`: the Stepanov method
    set q := Fintype.card F with hqdef
    set M := Nat.sqrt q with hMdef
    set B := M / e + d + 3 with hBdef
    set A₀ := M * M / (2 * e) + 1 with hAdef
    obtain ⟨hM1, h2e, hMk, hBq, hAinj, hdim⟩ := hnumerics e d he hd D hDg q hbig
    obtain ⟨AA, hAc, hBd, hcond, hAAne⟩ :=
      stevanov_witness_exists_of_arith (F := F) e he g hg0 hD1 A₀ B M hMk hdim
    have hRne : (∑ r : Fin e, (AA r).eval ((Polynomial.X : Polynomial F) ^ Fintype.card F) *
        g ^ ((r : ℕ) * ((Fintype.card F - 1) / e))) ≠ 0 := by
      intro hR0
      refine hAAne (funext fun r => ?_)
      exact hinj (K := F) e he hdiv g hg0 hnd A₀ hAinj AA hAc
        (fun r => lt_of_le_of_lt (hBd r) hBq) hR0 r
    have hcount := stevanov_count_gpow (F := F) e he hdiv g hg0 hD1 A₀ B M hM1 hMk AA hAc hBd
      hcond hRne
    have hcount' : (({x : F | g.eval x ^ ((Fintype.card F - 1) / e) = 1} : Set F).ncard)
        * M ≤ M * M / (2 * e) + 1 + q * (M / e + d + 3) + (e - 1) * (((q - 1) / e) * D) := by
      have hD' : D = g.natDegree := hDdef
      calc (({x : F | g.eval x ^ ((Fintype.card F - 1) / e) = 1} : Set F).ncard) * M
          ≤ A₀ + Fintype.card F * B + (e - 1) * (((Fintype.card F - 1) / e) * g.natDegree) := hcount
        _ = M * M / (2 * e) + 1 + q * (M / e + d + 3) + (e - 1) * (((q - 1) / e) * D) := by
            rw [hAdef, hBdef, hDdef, hqdef]
    have := hbound e d D q _ he hd hDg hbig hcount'
    have heq : (q : ℝ) = (Fintype.card F : ℝ) := by rw [hqdef]
    rw [← hqdef] at this
    refine le_trans this ?_
    have hC1 : stepanovC1 e d ≤ max (stepanovC1 e d)
        ((1 - 1 / (e : ℝ)) * Real.sqrt ((stepanovQ0 e d : ℕ) : ℝ)) + 1 :=
      le_trans (le_max_left _ _) (by linarith)
    have : stepanovC1 e d * Real.sqrt (q : ℝ) ≤
        (max (stepanovC1 e d) ((1 - 1 / (e : ℝ)) * Real.sqrt ((stepanovQ0 e d : ℕ) : ℝ)) + 1)
          * Real.sqrt (q : ℝ) := by
      apply mul_le_mul_of_nonneg_right hC1 (Real.sqrt_nonneg _)
    linarith
  · -- small `q`: the trivial bound
    push_neg at hbig
    have hsub : ({x : F | g.eval x ^ ((Fintype.card F - 1) / e) = 1} : Set F) ⊆ Set.univ :=
      fun x _ => Set.mem_univ x
    have hcard : (({x : F | g.eval x ^ ((Fintype.card F - 1) / e) = 1} : Set F).ncard)
        ≤ Fintype.card F := by
      have h1 := Set.ncard_le_ncard hsub (Set.finite_univ)
      rw [Set.ncard_univ, Nat.card_eq_fintype_card] at h1
      exact h1
    have hcardR : (({x : F | g.eval x ^ ((Fintype.card F - 1) / e) = 1} : Set F).ncard : ℝ)
        ≤ (Fintype.card F : ℝ) := by exact_mod_cast hcard
    have hqR : (0 : ℝ) < (Fintype.card F : ℝ) := by
      have : 0 < Fintype.card F := Fintype.card_pos
      exact_mod_cast this
    have hsqrtle : Real.sqrt (Fintype.card F : ℝ) ≤ Real.sqrt ((stepanovQ0 e d : ℕ) : ℝ) := by
      apply Real.sqrt_le_sqrt
      exact_mod_cast hbig.le
    have hsplit : (Fintype.card F : ℝ) = (Fintype.card F : ℝ) / (e : ℝ)
        + (1 - 1 / (e : ℝ)) * (Fintype.card F : ℝ) := by
      field_simp
      ring
    have hge : (0 : ℝ) ≤ 1 - 1 / (e : ℝ) := by
      rw [sub_nonneg, div_le_one (by linarith [heR])]; exact le_of_lt heR
    have hstep : (1 - 1 / (e : ℝ)) * (Fintype.card F : ℝ)
        ≤ ((1 - 1 / (e : ℝ)) * Real.sqrt ((stepanovQ0 e d : ℕ) : ℝ)) * Real.sqrt (Fintype.card F : ℝ) := by
      have h1 : (Fintype.card F : ℝ) ≤ Real.sqrt ((stepanovQ0 e d : ℕ) : ℝ) * Real.sqrt (Fintype.card F : ℝ) := by
        have h2 : Real.sqrt (Fintype.card F : ℝ) * Real.sqrt (Fintype.card F : ℝ)
            = (Fintype.card F : ℝ) := by
          simpa [pow_two] using Real.sq_sqrt (le_of_lt hqR)
        nlinarith [h2, hsqrtle, Real.sqrt_nonneg ((stepanovQ0 e d : ℕ) : ℝ),
          Real.sqrt_nonneg (Fintype.card F : ℝ)]
      calc (1 - 1 / (e : ℝ)) * (Fintype.card F : ℝ)
          ≤ (1 - 1 / (e : ℝ)) * (Real.sqrt ((stepanovQ0 e d : ℕ) : ℝ) * Real.sqrt (Fintype.card F : ℝ)) :=
            mul_le_mul_of_nonneg_left h1 hge
        _ = ((1 - 1 / (e : ℝ)) * Real.sqrt ((stepanovQ0 e d : ℕ) : ℝ)) * Real.sqrt (Fintype.card F : ℝ) := by
            ring
    have hC2 : (1 - 1 / (e : ℝ)) * Real.sqrt ((stepanovQ0 e d : ℕ) : ℝ)
        ≤ max (stepanovC1 e d) ((1 - 1 / (e : ℝ)) * Real.sqrt ((stepanovQ0 e d : ℕ) : ℝ)) + 1 :=
      le_trans (le_max_right _ _) (by linarith)
    calc (({x : F | g.eval x ^ ((Fintype.card F - 1) / e) = 1} : Set F).ncard : ℝ)
        ≤ (Fintype.card F : ℝ) := hcardR
      _ = (Fintype.card F : ℝ) / (e : ℝ) + (1 - 1 / (e : ℝ)) * (Fintype.card F : ℝ) := hsplit
      _ ≤ (Fintype.card F : ℝ) / (e : ℝ)
            + ((1 - 1 / (e : ℝ)) * Real.sqrt ((stepanovQ0 e d : ℕ) : ℝ)) * Real.sqrt (Fintype.card F : ℝ) := by
          linarith [hstep]
      _ ≤ (Fintype.card F : ℝ) / (e : ℝ)
            + (max (stepanovC1 e d) ((1 - 1 / (e : ℝ)) * Real.sqrt ((stepanovQ0 e d : ℕ) : ℝ)) + 1)
              * Real.sqrt (Fintype.card F : ℝ) := by
          have h1 : ((1 - 1 / (e : ℝ)) * Real.sqrt ((stepanovQ0 e d : ℕ) : ℝ)) * Real.sqrt (Fintype.card F : ℝ)
              ≤ (max (stepanovC1 e d) ((1 - 1 / (e : ℝ)) * Real.sqrt ((stepanovQ0 e d : ℕ) : ℝ)) + 1)
                * Real.sqrt (Fintype.card F : ℝ) :=
            mul_le_mul_of_nonneg_right hC2 (Real.sqrt_nonneg _)
          linarith


/-! ## Local copy of the non-vanishing lemma (module clash workaround) -/


/-- Substituting `X ↦ X + C c` is injective on polynomials over a commutative ring. -/
lemma gpowCompXAddCInjective {R : Type*} [CommRing R] (c : R) :
    Function.Injective (fun p : R[X] => p.comp (X + C c)) := by
  have hqq : (X + C c : R[X]).comp (X - C c) = X := by
    rw [add_comp, X_comp, C_comp, sub_add_cancel]
  intro p q hpq
  have h := congrArg (fun r : R[X] => r.comp (X - C c)) hpq
  rw [comp_assoc, comp_assoc, hqq, comp_X, comp_X] at h
  exact h

/-- If all `Y`-coefficients of `P : (F[X])[Y]` have `X`-degree at most `A₀`, then evaluating
`Y` at a constant `C c` keeps that bound. -/
lemma gpowNatDegreeEvalCle {F : Type*} [CommSemiring F] {A₀ : ℕ} {P : Polynomial (Polynomial F)}
    (hP : ∀ j, ((P.coeff j).natDegree) ≤ A₀) (c : F) :
    (P.eval (Polynomial.C c)).natDegree ≤ A₀ := by
  rw [Polynomial.eval_eq_sum_range]
  refine Polynomial.natDegree_sum_le_of_forall_le
    (Finset.range (P.natDegree + 1)) (fun i => P.coeff i * (Polynomial.C c) ^ i) ?_
  intro i _
  refine (Polynomial.natDegree_mul_le).trans ?_
  have hc : ((Polynomial.C c : Polynomial F) ^ i).natDegree = 0 := by
    rw [← Polynomial.C_pow, Polynomial.natDegree_C]
  rw [hc, add_zero]
  exact hP i

/-- The Taylor shift `Y ↦ Y + C c` of `(F[X])[Y]` does not increase the `X`-degrees of the
coefficients. -/
lemma gpowCoeffTaylorLe {F : Type*} [CommSemiring F] {A₀ : ℕ} {P : Polynomial (Polynomial F)}
    (hP : ∀ j, ((P.coeff j).natDegree) ≤ A₀) (i : ℕ) (c : F) :
    (((Polynomial.taylor (Polynomial.C c) P).coeff i).natDegree) ≤ A₀ := by
  rw [Polynomial.taylor_coeff]
  refine gpowNatDegreeEvalCle (A₀ := A₀) ?_ c
  intro j
  rw [Polynomial.hasseDeriv_coeff]
  refine (Polynomial.natDegree_mul_le).trans ?_
  have hc : ((↑((j + i).choose i) : Polynomial F)).natDegree = 0 :=
    Polynomial.natDegree_natCast _
  rw [hc, zero_add]
  exact hP (j + i)

/-- Composing with `X + C t` does not increase the degree. -/
lemma gpowNatDegreeCompXAddCLe {F : Type*} [Field F] (t : F) (p : Polynomial F) :
    (p.comp (Polynomial.X + Polynomial.C t)).natDegree ≤ p.natDegree := by
  rw [Polynomial.natDegree_comp, Polynomial.natDegree_X_add_C, mul_one]

theorem gpowShiftReduce {F : Type*} [Field F] [Fintype F]
    (e : ℕ) (he : 2 ≤ e) (hdiv : e ∣ Fintype.card F - 1) (g : Polynomial F) (hg : g ≠ 0)
    (hnd : ∀ p : ℕ, p.Prime → p ∣ e → ∀ (a : F) (h : Polynomial F),
      g ≠ Polynomial.C a * h ^ p)
    (A₀ : ℕ) (hA₀ : (e:ℕ) * A₀ + (e:ℕ) ^ 3 * (g.natDegree + 1) < Fintype.card F)
    (A : Fin e → Polynomial (Polynomial F))
    (hAd : ∀ r i, ((A r).coeff i).natDegree ≤ A₀)
    (hAn : ∀ r, (A r).natDegree < Fintype.card F)
    (h : ∑ r : Fin e, (A r).eval ((Polynomial.X : Polynomial F) ^ Fintype.card F)
          * g ^ ((r : ℕ) * ((Fintype.card F - 1) / e)) = 0) :
    ∃ (g' : Polynomial F) (A' : Fin e → Polynomial (Polynomial F)),
      g' ≠ 0 ∧ g'.eval 0 ≠ 0 ∧ g'.natDegree = g.natDegree ∧
      (∀ p : ℕ, p.Prime → p ∣ e → ∀ (a : F) (h : Polynomial F),
        g' ≠ Polynomial.C a * h ^ p) ∧
      (∀ r i, ((A' r).coeff i).natDegree ≤ A₀) ∧
      (∀ r, (A' r).natDegree < Fintype.card F) ∧
      (∑ r : Fin e, (A' r).eval ((Polynomial.X : Polynomial F) ^ Fintype.card F)
          * g' ^ ((r : ℕ) * ((Fintype.card F - 1) / e)) = 0) ∧
      ((∀ r, A' r = 0) → ∀ r, A r = 0) := by
  classical
  -- Step 1: pick `t : F` with `g t ≠ 0`.
  have hdeg_lt : g.natDegree < Fintype.card F := by
    have he3 : 1 ≤ e ^ 3 := Nat.one_le_pow 3 e (by omega)
    have h1 : g.natDegree + 1 ≤ e ^ 3 * (g.natDegree + 1) := by
      calc g.natDegree + 1 = 1 * (g.natDegree + 1) := (one_mul _).symm
        _ ≤ e ^ 3 * (g.natDegree + 1) := Nat.mul_le_mul_right _ he3
    have h2 : e ^ 3 * (g.natDegree + 1) ≤ e * A₀ + e ^ 3 * (g.natDegree + 1) :=
      Nat.le_add_left _ _
    omega
  obtain ⟨t, ht⟩ := Polynomial.exists_eval_ne_zero_of_natDegree_lt_card g hg (by
    simpa only [Cardinal.mk_fintype, Nat.cast_lt] using hdeg_lt)
  -- Step 2: the substitution `X ↦ X + t` on `F[X]`.
  set σ : Polynomial F →+* Polynomial F :=
    Polynomial.compRingHom (Polynomial.X + Polynomial.C t) with hσ
  have hσ_apply : ∀ p : Polynomial F, σ p = p.comp (Polynomial.X + Polynomial.C t) := by
    intro p; rw [hσ]; exact Polynomial.coe_compRingHom_apply p _
  have hσ_inj : Function.Injective σ := by
    rw [hσ]
    exact gpowCompXAddCInjective t
  set g' : Polynomial F := σ g with hg'
  -- Step 3: the substitution `X ↦ X + t`, `Y ↦ Y + t` on `F[X][Y]`.
  set ρ : Polynomial (Polynomial F) →+* Polynomial (Polynomial F) :=
    (Polynomial.compRingHom (Polynomial.X + Polynomial.C (Polynomial.C t))).comp
      (Polynomial.mapRingHom σ) with hρ
  have hρ_inj : Function.Injective ρ := by
    rw [hρ, RingHom.coe_comp]
    exact Function.Injective.comp (gpowCompXAddCInjective (Polynomial.C t))
      (Polynomial.map_injective σ hσ_inj)
  -- Step 4: the key identity `(X + t)^q = X^q + t`, `q = #F`, via the freshman's dream.
  obtain ⟨n, hp, hcard⟩ := FiniteField.card F (ringChar F)
  haveI : Fact (ringChar F).Prime := ⟨hp⟩
  have hX : (Polynomial.X + Polynomial.C t) ^ Fintype.card F
      = Polynomial.X ^ Fintype.card F + Polynomial.C t := by
    rw [hcard, add_pow_char_pow]
    congr 1
    rw [← Polynomial.C_pow]
    congr 1
    rw [← hcard]
    exact FiniteField.pow_card t
  -- Step 5: naturality of the evaluation `P ↦ P(X^q)`.
  have key : ∀ P : Polynomial (Polynomial F),
      Polynomial.evalRingHom (Polynomial.X ^ Fintype.card F) (ρ P)
        = σ (Polynomial.evalRingHom (Polynomial.X ^ Fintype.card F) P) := by
    intro P
    have hcomp : (Polynomial.evalRingHom (Polynomial.X ^ Fintype.card F)).comp ρ
        = σ.comp (Polynomial.evalRingHom (Polynomial.X ^ Fintype.card F)) := by
      apply Polynomial.ringHom_ext
      · intro c
        have hL : ((Polynomial.evalRingHom (Polynomial.X ^ Fintype.card F)).comp ρ)
            (Polynomial.C c) = σ c := by
          rw [RingHom.comp_apply, hρ, RingHom.comp_apply, Polynomial.coe_mapRingHom,
            Polynomial.map_C]
          simp only [Polynomial.coe_compRingHom, Polynomial.C_comp, Polynomial.coe_evalRingHom,
            Polynomial.eval_C]
        have hR : (σ.comp (Polynomial.evalRingHom (Polynomial.X ^ Fintype.card F)))
            (Polynomial.C c) = σ c := by
          rw [RingHom.comp_apply]
          simp only [Polynomial.coe_evalRingHom, Polynomial.eval_C]
        rw [hL, hR]
      · have hL : ((Polynomial.evalRingHom (Polynomial.X ^ Fintype.card F)).comp ρ)
            Polynomial.X = Polynomial.X ^ Fintype.card F + Polynomial.C t := by
          rw [RingHom.comp_apply, hρ, RingHom.comp_apply, Polynomial.coe_mapRingHom,
            Polynomial.map_X]
          simp only [Polynomial.coe_compRingHom, Polynomial.X_comp, Polynomial.coe_evalRingHom,
            Polynomial.eval_add, Polynomial.eval_X, Polynomial.eval_C]
        have hR : (σ.comp (Polynomial.evalRingHom (Polynomial.X ^ Fintype.card F)))
            Polynomial.X = Polynomial.X ^ Fintype.card F + Polynomial.C t := by
          rw [RingHom.comp_apply, Polynomial.coe_evalRingHom, Polynomial.eval_X, hσ_apply,
            Polynomial.X_pow_comp, hX]
        rw [hL, hR]
    exact congrArg (fun f : Polynomial (Polynomial F) →+* Polynomial F => f P) hcomp
  -- Step 6: bounds for `A' r = ρ (A r)`.
  have hA'_bdd : ∀ r i, (((ρ (A r)).coeff i).natDegree) ≤ A₀ := by
    intro r i
    rw [hρ, RingHom.comp_apply, Polynomial.coe_mapRingHom]
    change (((Polynomial.map σ (A r)).comp (X + C (C t))).coeff i).natDegree ≤ A₀
    rw [← Polynomial.taylor_apply]
    refine gpowCoeffTaylorLe (A₀ := A₀) ?_ i t
    intro j
    rw [Polynomial.coeff_map, hσ_apply]
    exact (gpowNatDegreeCompXAddCLe t ((A r).coeff j)).trans (hAd r j)
  have hA'_n : ∀ r, (ρ (A r)).natDegree < Fintype.card F := by
    intro r
    have h1 : (ρ (A r)).natDegree ≤ (A r).natDegree := by
      rw [hρ, RingHom.comp_apply, Polynomial.coe_mapRingHom]
      change ((Polynomial.map σ (A r)).comp (X + C (C t))).natDegree ≤ (A r).natDegree
      rw [Polynomial.natDegree_comp, Polynomial.natDegree_X_add_C, mul_one]
      exact Polynomial.natDegree_map_le
    exact lt_of_le_of_lt h1 (hAn r)
  -- Step 7: the relation is preserved.
  have hrel : ∑ r : Fin e, Polynomial.evalRingHom (Polynomial.X ^ Fintype.card F) (ρ (A r))
        * g' ^ ((r:ℕ) * ((Fintype.card F - 1)/e)) = 0 := by
    have h1 := congrArg σ h
    have h2 : ∑ r : Fin e, σ (Polynomial.evalRingHom (Polynomial.X ^ Fintype.card F) (A r))
        * (σ g) ^ ((r:ℕ) * ((Fintype.card F - 1)/e)) = 0 := by
      simpa only [map_sum, map_mul, map_pow, map_zero, Polynomial.coe_evalRingHom] using h1
    simpa only [← key, ← hg'] using h2
  -- Step 8: assemble.
  refine ⟨g', fun r => ρ (A r), ?_, ?_, ?_, ?_, hA'_bdd, hA'_n, hrel, ?_⟩
  · rw [hg']
    simpa using hσ_inj.ne hg
  · rw [hg', hσ_apply, Polynomial.eval_comp, Polynomial.eval_add, Polynomial.eval_X,
      Polynomial.eval_C, zero_add]
    exact ht
  · rw [hg', hσ_apply, Polynomial.natDegree_comp, Polynomial.natDegree_X_add_C, mul_one]
  · intro p hp hpe a hh heq
    apply hnd p hp hpe a (hh.comp (Polynomial.X - Polynomial.C t))
    have hk := congrArg (fun r : Polynomial F => r.comp (Polynomial.X - Polynomial.C t)) heq
    rw [hg', hσ_apply] at hk
    simp only [Polynomial.comp_assoc, Polynomial.add_comp, Polynomial.X_comp, Polynomial.C_comp,
      sub_add_cancel, Polynomial.comp_X, Polynomial.mul_comp, Polynomial.pow_comp] at hk
    exact hk
  · intro hzero r
    have hr : ρ (A r) = 0 := hzero r
    exact hρ_inj (by rw [hr, map_zero])



/-- The non-vanishing (injectivity) lemma of Stepanov's method, restated here with the same
statement as the commons lemma `Commons.NumberTheory.Stepanov.gpow_frobenius_eval_indep`.

(It is reproduced locally, with a renamed auxiliary lemma, because
`Submission.Commons.NumberTheory.Stepanov.gpow_shift_reduce` and
`Submission.Commons.NumberTheory.Stepanov.kopparty_sq_nonvanishing` both declare a lemma named
`natDegree_eval_C_le`, so the two modules cannot be imported into the same file.) -/
theorem gpowFrobeniusEvalIndep {F : Type*} [Field F] [Fintype F]
    (e : ℕ) (he : 2 ≤ e) (hdiv : e ∣ Fintype.card F - 1) (g : Polynomial F) (hg : g ≠ 0)
    (hnd : ∀ p : ℕ, p.Prime → p ∣ e → ∀ (a : F) (h : Polynomial F),
      g ≠ Polynomial.C a * h ^ p)
    (A₀ : ℕ) (hA₀ : (e:ℕ) * A₀ + (e:ℕ) ^ 3 * (g.natDegree + 1) < Fintype.card F)
    (A : Fin e → Polynomial (Polynomial F))
    (hAd : ∀ r i, ((A r).coeff i).natDegree ≤ A₀)
    (hAn : ∀ r, (A r).natDegree < Fintype.card F)
    (h : ∑ r : Fin e, (A r).eval ((Polynomial.X : Polynomial F) ^ Fintype.card F)
          * g ^ ((r : ℕ) * ((Fintype.card F - 1) / e)) = 0) :
    ∀ r, A r = 0 := by
  obtain ⟨g', A', hg'0, hg'e, hgn, hhnd', hAd', hAn', hsum', hconcl⟩ :=
    gpowShiftReduce e he hdiv g hg hnd A₀ hA₀ A hAd hAn h
  have hA₀' : (e:ℕ) * A₀ + (e:ℕ) ^ 3 * (g'.natDegree + 1) < Fintype.card F := by
    rw [hgn]; exact hA₀
  exact hconcl (gpow_main_g0 e he hdiv g' hg'0 hg'e hhnd' A₀ hA₀' A' hAd' hAn' hsum')

/-- **Linnik/Stepanov: the superelliptic character sum bound.**

`#{x : g x^((q-1)/e) = 1} ≤ q/e + C √q`, with `C` depending only on `e` and `d`, for every
finite field `F` with `e ∣ #F - 1` and every `g ∈ F[X]` of degree `≤ d` that is not a constant
multiple of a `p`-th power for any prime `p ∣ e`.

The proof is Stepanov's method in the one-variable (Frobenius) form: the dimension count
`stevanov_witness_exists_of_arith`, the non-vanishing (good basis) lemma
`gpow_frobenius_eval_indep`, the counting lemma `stevanov_count_gpow`, and the numerology
`stepanov_numerics` / `stepanov_count_to_bound`. -/
theorem superelliptic_char_sum_bound (e d : ℕ) (he : 2 ≤ e) (hd : 1 ≤ d) :
    ∃ C : ℝ, 0 < C ∧
      ∀ (F : Type*) [Field F] [Fintype F] [DecidableEq F],
        e ∣ Fintype.card F - 1 →
        ∀ g : Polynomial F, g.natDegree ≤ d →
        (∀ p : ℕ, p.Prime → p ∣ e → ∀ (a : F) (h : Polynomial F),
          g ≠ Polynomial.C a * h ^ p) →
        (({x : F | g.eval x ^ ((Fintype.card F - 1) / e) = 1} : Set F).ncard : ℝ)
          ≤ (Fintype.card F : ℝ) / (e : ℝ) + C * Real.sqrt (Fintype.card F) := by
  exact superelliptic_char_sum_bound_of_inputs
    (fun {K} _ _ e he hdiv g hg hnd A₀ hA₀ A hAd hAn h =>
      gpowFrobeniusEvalIndep e he hdiv g hg hnd A₀ hA₀ A hAd hAn h)
    (fun e d he hd D hD q hq => stepanov_numerics e d he hd D hD q hq)
    (fun e d D q T he hd hD hq hT => stepanov_count_to_bound e d he hd D hD q T hq hT)
    e d he hd

end

end Commons.NumberTheory.Stepanov
