import Mathlib
import Submission.CDT.SympH

/-!
# The descent of `φ`-invariant series to `ℚ[[y]]` (defines `Sym⁺H`)

This is the spine of CDT §"The symmetrization of H(x)": every power series
`f(X) ∈ ℚ[[X]]` that is invariant under the substitution `x ↦ φ(x)` (with
`φ = x/(x−1)`, `sympPhi` from `Submission.CDT.SympH`) is a power series in
the symmetrization coordinate `y = x²/(x−1) = x·φ(x)` (`sympY`): there is a
unique `g(Y) ∈ ℚ[[Y]]` with `g(y(X)) = f(X)`.

**Proved in this module**:

* the vanishing lemmas `coeff_pow_lt_one`/`coeff_pow_lt_two`, the
  substitution coefficient formulas `coeff_subst_range`/`coeff_subst_range₂`,
  `coeff_pow_self_deg` (`coeff n (b^n) = (coeff 1 b)^n`), the coefficient
  facts for `φ` and `y` (`coeff 1 φ = −1`, `coeff (2n)(y^n) = (−1)ⁿ`), and
  the **parity lemma** `symp_invariant_eq_of_even_coeff_eq`: two
  `φ`-invariant series with equal even coefficients are equal (odd
  coefficients are forced by invariance);
* **the descent half**: the well-founded triangular recursion
  `sympDescCoeff` (`g n = (f_{2n} − Σ_{m<n} g_m·coeff (2n)(y^m)) / coeff (2n)(y^n)`,
  `WellFounded.fix`-based with `sympF`, equation lemmas
  `sympDescCoeff_eq_attach`/`sympDescCoeff_eq`), the series `sympDesc f`,
  `sympDesc_even` (`coeff (2k)((sympDesc f)∘y) = coeff (2k) f`),
  `sympDesc_y_invariant`/`sympDesc_y_subst`
  (`(sympDesc f)∘y = f` for `φ`-invariant `f`), the injectivity lemma
  `symp_subst_y_injective` (`A∘y = 0 ⟹ A = 0`), and **the descent
  theorem**

```lean
theorem symp_descent (f : PowerSeries ℚ) (hf : f.subst sympPhi = f) :
    ∃! g : PowerSeries ℚ, g.subst sympY = f
```

  every `φ`-invariant series is a unique power series in the coordinate
  `y = x²/(x−1)`; and finally `sympSym H` = `Sym⁺H`, the unique series
  with `(Sym⁺H)∘y = H + H∘φ` (`sympSym_subst`), which is the
  symmetrized function `G(y)` of CDT §"The symmetrization of H(x)";
* the **symmetrized powers** `P_n(y) = xⁿ + φⁿ` (`sympP`, paper eq.
  (polysym)): `P_0 = 2`, `P_1 = y`, the quadratic roots `X² = yX − y`
  and `φ² = yφ − y` (`symp_x_sq_eq`/`symp_phi_sq_eq`), the recurrence
  `P_{n+2} = y·P_{n+1} − y·P_n` (`sympP_succ_succ`, via the generic
  `symp_pow_succ_succ_of_quad`), and `φ`-invariance `sympP_invariant`;
* **the `ℤ`-coefficient refinement** (formalising the integrality claim
  `G_A(y) = Sym⁺H_A ∈ ℤ[[y]]` of the paper's defG): the predicate
  `IntSeries` (every coefficient is the cast of an integer), its closure
  under `0, 1, X`, negation, addition, subtraction, multiplication
  (`exists_int_finset_sum_mul`), powers and substitution by a
  zero-constant-term integer series (`intSeries_subst`); the integer
  coefficient facts `sympPhi_IntSeries`/`sympY_IntSeries` (with
  `coeff_inv_X_sub_one`: all coefficients of `(X−1)⁻¹` are `−1`); the
  sign form `sympDescCoeff_eq_sign` of the descent recursion; the
  integrality theorem `sympDescCoeff_int` (integer coefficients of `f`
  and of all `y^m` force integer descent coefficients); and finally
  `sympSym_int : IntSeries H → IntSeries (Sym⁺H)` (via
  `sympSym_eq_sympDesc`, identifying `Sym⁺H` with the explicit descent
  series).  Application to `H_A` is in `Submission.CDT.SympZagier`
  (`sympSym_HA_IntSeries`).
-/

open scoped BigOperators

noncomputable section

namespace Submission.CDT

open PowerSeries

/-! ## Substitution coefficient machinery -/

/-- if `b` has zero constant term then `coeff n (b^m) = 0` for `n < m` -/
lemma coeff_pow_lt_one {b : PowerSeries ℚ} (hb : PowerSeries.coeff 0 b = 0) :
    ∀ {m n : ℕ}, n < m → PowerSeries.coeff n (b ^ m) = 0 := by
  intro m
  induction m with
  | zero =>
      intro n hn
      exfalso
      omega
  | succ m ih =>
      intro n hn
      rw [pow_succ]
      rw [PowerSeries.coeff_mul]
      apply Finset.sum_eq_zero
      intro p hp
      have hp' : p.1 + p.2 = n := (Finset.HasAntidiagonal.mem_antidiagonal.mp hp)
      by_cases h2 : p.2 = 0
      · have hz : PowerSeries.coeff p.2 b = 0 := by simp [h2, hb]
        simp [hz]
      · have hlt : p.1 < m := by omega
        have hz : PowerSeries.coeff p.1 (b ^ m) = 0 := ih hlt
        simp [hz]

/-- if the first two coefficients of `b` vanish then `coeff n (b^m) = 0`
for `n < 2m` -/
lemma coeff_pow_lt_two {b : PowerSeries ℚ} (hb0 : PowerSeries.coeff 0 b = 0)
    (hb1 : PowerSeries.coeff 1 b = 0) :
    ∀ {m n : ℕ}, n < 2 * m → PowerSeries.coeff n (b ^ m) = 0 := by
  intro m
  induction m with
  | zero =>
      intro n hn
      exfalso
      omega
  | succ m ih =>
      intro n hn
      rw [pow_succ]
      rw [PowerSeries.coeff_mul]
      apply Finset.sum_eq_zero
      intro p hp
      have hp' : p.1 + p.2 = n := (Finset.HasAntidiagonal.mem_antidiagonal.mp hp)
      by_cases h2 : p.2 < 2
      · interval_cases p.2 <;> simp [hb0, hb1]
      · have hlt : p.1 < 2 * m := by omega
        have hz : PowerSeries.coeff p.1 (b ^ m) = 0 := ih hlt
        simp [hz]

/-- the substitution coefficient formula (valuation-`1` case) -/
lemma coeff_subst_range (f : PowerSeries ℚ) {b : PowerSeries ℚ}
    (hb : PowerSeries.coeff 0 b = 0) (n : ℕ) :
    PowerSeries.coeff n (f.subst b) =
      ∑ m ∈ Finset.range (n + 1), PowerSeries.coeff m f * PowerSeries.coeff n (b ^ m) := by
  have hbs : PowerSeries.HasSubst b :=
    PowerSeries.HasSubst.of_constantCoeff_zero' (by simpa using hb)
  have h := PowerSeries.coeff_subst' (R := ℚ) (S := ℚ) hbs f n
  have hsup : Function.support (fun d : ℕ => (coeff d f) • (coeff n (b ^ d))) ⊆
      ↑(Finset.range (n + 1)) := by
    intro d hd
    simp at hd ⊢
    by_contra hn
    have hdgt : n < d := by omega
    have h0 : PowerSeries.coeff n (b ^ d) = 0 := coeff_pow_lt_one hb hdgt
    simp [h0] at hd
  have hfin := finsum_eq_sum_of_support_subset (fun d : ℕ => (coeff d f) • (coeff n (b ^ d))) hsup
  rw [h]
  rw [hfin]
  simp

/-- the substitution coefficient formula (valuation-`2` case) -/
lemma coeff_subst_range₂ (f : PowerSeries ℚ) {b : PowerSeries ℚ}
    (hb0 : PowerSeries.coeff 0 b = 0) (hb1 : PowerSeries.coeff 1 b = 0) (n : ℕ) :
    PowerSeries.coeff n (f.subst b) =
      ∑ m ∈ Finset.range (n / 2 + 1), PowerSeries.coeff m f * PowerSeries.coeff n (b ^ m) := by
  have hbs : PowerSeries.HasSubst b :=
    PowerSeries.HasSubst.of_constantCoeff_zero' (by simpa using hb0)
  have h := PowerSeries.coeff_subst' (R := ℚ) (S := ℚ) hbs f n
  have hsup : Function.support (fun d : ℕ => (coeff d f) • (coeff n (b ^ d))) ⊆
      ↑(Finset.range (n / 2 + 1)) := by
    intro d hd
    simp at hd ⊢
    by_contra hn
    have hdgt : 2 * d > n := by omega
    have h0 : PowerSeries.coeff n (b ^ d) = 0 := coeff_pow_lt_two hb0 hb1 hdgt
    simp [h0] at hd
  have hfin := finsum_eq_sum_of_support_subset (fun d : ℕ => (coeff d f) • (coeff n (b ^ d))) hsup
  rw [h]
  rw [hfin]
  simp

/-- `coeff n (b^n) = (coeff 1 b)^n` for `b` with zero constant term -/
lemma coeff_pow_self_deg {b : PowerSeries ℚ} (hb : PowerSeries.coeff 0 b = 0) (n : ℕ) :
    PowerSeries.coeff n (b ^ n) = (PowerSeries.coeff 1 b) ^ n := by
  induction n with
  | zero => simp
  | succ n ih =>
      rw [pow_succ']
      rw [PowerSeries.coeff_mul]
      let s : Finset (ℕ × ℕ) := Finset.HasAntidiagonal.antidiagonal (n + 1)
      have hmain : ∑ p ∈ s, PowerSeries.coeff p.1 b * PowerSeries.coeff p.2 (b ^ n) =
          PowerSeries.coeff 1 b * PowerSeries.coeff n (b ^ n) := by
        calc
          (∑ p ∈ s, PowerSeries.coeff p.1 b * PowerSeries.coeff p.2 (b ^ n))
              = ∑ p ∈ s, if p.2 = n then PowerSeries.coeff p.1 b * PowerSeries.coeff p.2 (b ^ n) else 0 := by
                  apply Finset.sum_congr rfl
                  intro p hp
                  by_cases hp2 : p.2 = n
                  · simp [hp2]
                  · by_cases hp2lt : p.2 < n
                    · have hz : PowerSeries.coeff p.2 (b ^ n) = 0 := coeff_pow_lt_one hb hp2lt
                      simp [hz]
                    · have hp' : p.1 + p.2 = n + 1 := by
                        simpa [s] using (Finset.HasAntidiagonal.mem_antidiagonal.mp hp)
                      have hp2' : p.2 = n + 1 := by omega
                      have hp1z : p.1 = 0 := by omega
                      simp [hp1z, hb]
          _ = ∑ p ∈ s.filter (fun p : ℕ × ℕ => p.2 = n),
                PowerSeries.coeff p.1 b * PowerSeries.coeff p.2 (b ^ n) := by
                  rw [Finset.sum_filter]
          _ = PowerSeries.coeff 1 b * PowerSeries.coeff n (b ^ n) := by
                  have hs : s.filter (fun p : ℕ × ℕ => p.2 = n) = ({(1, n)} : Finset (ℕ × ℕ)) := by
                    ext p
                    simp [s, Finset.HasAntidiagonal.mem_antidiagonal]
                    constructor
                    · intro hp
                      rcases hp with ⟨hp1, hp2⟩
                      ext <;> omega
                    · intro hp
                      rcases hp with ⟨hp1, hp2⟩
                      omega
                  rw [hs]
                  simp
      rw [hmain]
      rw [ih]
      rw [pow_succ]
      ring

/-! ## Coefficient facts for `φ` and `y` -/

/-- `coeff 0 φ = 0` -/
lemma coeff_sympPhi_zero : PowerSeries.coeff 0 sympPhi = 0 := by
  simp [sympPhi]

/-- `coeff 1 φ = −1` -/
lemma coeff_sympPhi_one : PowerSeries.coeff 1 sympPhi = -1 := by
  unfold sympPhi
  rw [mul_comm X]
  rw [PowerSeries.coeff_succ_mul_X]
  have hc : PowerSeries.coeff 0 (((X : PowerSeries ℚ) - 1)⁻¹) = -1 := by
    rw [PowerSeries.coeff_inv]
    simp
  exact hc

/-- `coeff 0 y = 0` -/
lemma coeff_sympY_zero : PowerSeries.coeff 0 sympY = 0 := by
  simp [sympY, sympPhi]

/-- `coeff 1 y = 0` -/
lemma coeff_sympY_one : PowerSeries.coeff 1 sympY = 0 := by
  change PowerSeries.coeff 1 (X * sympPhi) = 0
  rw [mul_comm X, PowerSeries.coeff_succ_mul_X]
  exact coeff_sympPhi_zero

/-- `coeff 2 y = −1` -/
lemma coeff_sympY_two : PowerSeries.coeff 2 sympY = -1 := by
  change PowerSeries.coeff 2 (X * sympPhi) = -1
  have h : PowerSeries.coeff 2 (X * sympPhi) = PowerSeries.coeff 1 sympPhi := by
    rw [mul_comm X, PowerSeries.coeff_succ_mul_X]
  rw [h]
  exact coeff_sympPhi_one

/-- the diagonal of the powers of `y`: `coeff (2n) (y^n) = (−1)ⁿ` -/
lemma coeff_sympY_pow_diag (n : ℕ) :
    PowerSeries.coeff (2 * n) (sympY ^ n) = (-1 : ℚ) ^ n := by
  have hd : ∀ m : ℕ, PowerSeries.coeff (2 * m) (sympY ^ m) = (PowerSeries.coeff 2 sympY) ^ m := by
    intro m
    induction m with
    | zero => simp
    | succ m ih =>
        rw [pow_succ']
        rw [PowerSeries.coeff_mul]
        have hmain : ∑ p ∈ Finset.HasAntidiagonal.antidiagonal (2 * (m + 1)),
              PowerSeries.coeff p.1 sympY * PowerSeries.coeff p.2 (sympY ^ m) =
            PowerSeries.coeff 2 sympY * PowerSeries.coeff (2 * m) (sympY ^ m) := by
          calc
            (∑ p ∈ Finset.HasAntidiagonal.antidiagonal (2 * (m + 1)),
                PowerSeries.coeff p.1 sympY * PowerSeries.coeff p.2 (sympY ^ m))
                = ∑ p ∈ Finset.HasAntidiagonal.antidiagonal (2 * (m + 1)),
                    if p.1 = 2 then PowerSeries.coeff p.1 sympY * PowerSeries.coeff p.2 (sympY ^ m) else 0 := by
                    apply Finset.sum_congr rfl
                    intro p hp
                    by_cases hp1 : p.1 = 2
                    · simp [hp1]
                    · by_cases hp0 : p.1 = 0
                      · have hz : PowerSeries.coeff p.1 sympY = 0 := by simp [hp0, coeff_sympY_zero]
                        simp [hz]
                      · by_cases hp1' : p.1 = 1
                        · have hz : PowerSeries.coeff p.1 sympY = 0 := by simp [hp1', coeff_sympY_one]
                          simp [hz]
                        · have hp' : p.1 + p.2 = 2 * (m + 1) :=
                            (Finset.HasAntidiagonal.mem_antidiagonal.mp hp)
                          have hlt : p.2 < 2 * m := by omega
                          have hz : PowerSeries.coeff p.2 (sympY ^ m) = 0 :=
                            coeff_pow_lt_two coeff_sympY_zero coeff_sympY_one hlt
                          simp [hz]
                _ = ∑ p ∈ (Finset.HasAntidiagonal.antidiagonal (2 * (m + 1))).filter
                      (fun p : ℕ × ℕ => p.1 = 2),
                      PowerSeries.coeff p.1 sympY * PowerSeries.coeff p.2 (sympY ^ m) := by
                      rw [Finset.sum_filter]
                _ = PowerSeries.coeff 2 sympY * PowerSeries.coeff (2 * m) (sympY ^ m) := by
                      have hs : (Finset.HasAntidiagonal.antidiagonal (2 * (m + 1))).filter
                            (fun p : ℕ × ℕ => p.1 = 2) = ({(2, 2 * m)} : Finset (ℕ × ℕ)) := by
                        ext p
                        simp [Finset.HasAntidiagonal.mem_antidiagonal]
                        constructor
                        · intro hp
                          rcases hp with ⟨hp1, hp2⟩
                          ext <;> omega
                        · intro hp
                          rcases hp with ⟨hp1, hp2⟩
                          omega
                      rw [hs]
                      simp
        rw [hmain]
        rw [ih]
        rw [pow_succ]
        ring
  rw [hd]
  rw [coeff_sympY_two]

/-! ## The parity lemma (odd coefficients are forced by invariance) -/

/-- two `φ`-invariant series with equal even coefficients are equal -/
lemma symp_invariant_eq_of_even_coeff_eq (A B : PowerSeries ℚ)
    (hA : A.subst sympPhi = A) (hB : B.subst sympPhi = B)
    (he : ∀ k : ℕ, PowerSeries.coeff (2 * k) A = PowerSeries.coeff (2 * k) B) : A = B := by
  let D : PowerSeries ℚ := A - B
  have hD : D.subst sympPhi = D := by
    dsimp [D]
    rw [PowerSeries.subst_sub sympPhi_hasSubst, hA, hB]
  have hDcoeff : ∀ n : ℕ, PowerSeries.coeff n D = 0 := by
    intro n
    induction n using Nat.strong_induction_on with
    | h n ih =>
        rcases Nat.even_or_odd n with ⟨k, hk⟩ | ⟨k, hk⟩
        · -- even: n = 2k:
          have hk2 : n = 2 * k := by omega
          rw [hk2]
          dsimp [D]
          rw [map_sub, he k]
          simp
        · -- odd: n = 2k+1: use invariance
          have hEq := congrArg (PowerSeries.coeff n) hD
          rw [coeff_subst_range D coeff_sympPhi_zero n] at hEq
          -- reduce the range-sum: terms m < n vanish by ih:
          have hsum : ∑ m ∈ Finset.range (n + 1),
                PowerSeries.coeff m D * PowerSeries.coeff n (sympPhi ^ m) =
              PowerSeries.coeff n D * PowerSeries.coeff n (sympPhi ^ n) := by
            rw [Finset.sum_range_succ]
            have hprev : ∑ m ∈ Finset.range n,
                PowerSeries.coeff m D * PowerSeries.coeff n (sympPhi ^ m) = 0 := by
              apply Finset.sum_eq_zero
              intro m hm
              have hz : PowerSeries.coeff m D = 0 := ih m (by simpa using (Finset.mem_range.mp hm))
              simp [hz]
            rw [hprev]
            ring
          have hmain : PowerSeries.coeff n D = PowerSeries.coeff n D * PowerSeries.coeff n (sympPhi ^ n) := by
            simpa [hsum] using hEq.symm
          -- coeff n (φ^n) = (coeff 1 φ)^n = −1 (n odd):
          have hd : PowerSeries.coeff n (sympPhi ^ n) = -1 := by
            rw [coeff_pow_self_deg coeff_sympPhi_zero]
            rw [coeff_sympPhi_one]
            rw [hk]
            rw [pow_succ]
            have h2k : (-1 : ℚ) ^ (2 * k) = 1 := by
              rw [pow_mul]
              norm_num
            rw [h2k]
            norm_num
          rw [hd] at hmain
          have : PowerSeries.coeff n D = -PowerSeries.coeff n D := by
            simpa using hmain
          nlinarith
  apply PowerSeries.ext
  intro n
  have hz := hDcoeff n
  dsimp [D] at hz
  rw [map_sub] at hz
  linarith

noncomputable def sympF (f : PowerSeries ℚ) :
    (n : ℕ) → ((m : ℕ) → m < n → ℚ) → ℚ := fun n rec =>
  (PowerSeries.coeff (2 * n) f -
      ∑ m ∈ (Finset.range n).attach,
        rec m.1 (by exact (Finset.mem_range.mp m.2)) * PowerSeries.coeff (2 * n) (sympY ^ m.1)) *
    (PowerSeries.coeff (2 * n) (sympY ^ n))⁻¹

noncomputable def sympDescCoeff (f : PowerSeries ℚ) : ℕ → ℚ :=
  WellFounded.fix (measure (fun n : ℕ => n)).wf (sympF f)

lemma sympDescCoeff_eq_attach (f : PowerSeries ℚ) (n : ℕ) :
    sympDescCoeff f n =
      (PowerSeries.coeff (2 * n) f -
        ∑ m ∈ (Finset.range n).attach,
          sympDescCoeff f m.1 * PowerSeries.coeff (2 * n) (sympY ^ m.1)) *
      (PowerSeries.coeff (2 * n) (sympY ^ n))⁻¹ := by
  unfold sympDescCoeff
  rw [WellFounded.fix_eq]
  unfold sympF
  simp

lemma symp_sum_attach (f : PowerSeries ℚ) (n : ℕ) :
    (∑ m ∈ (Finset.range n).attach,
        sympDescCoeff f m.1 * PowerSeries.coeff (2 * n) (sympY ^ m.1)) =
      ∑ m ∈ Finset.range n, sympDescCoeff f m * PowerSeries.coeff (2 * n) (sympY ^ m) := by
  simpa using (Finset.sum_attach (Finset.range n)
      (fun q : ℕ => sympDescCoeff f q * PowerSeries.coeff (2 * n) (sympY ^ q)))

lemma sympDescCoeff_eq (f : PowerSeries ℚ) (n : ℕ) :
    sympDescCoeff f n =
      (PowerSeries.coeff (2 * n) f -
        ∑ m ∈ Finset.range n, sympDescCoeff f m * PowerSeries.coeff (2 * n) (sympY ^ m)) *
      (PowerSeries.coeff (2 * n) (sympY ^ n))⁻¹ := by
  rw [sympDescCoeff_eq_attach f n]
  rw [symp_sum_attach f n]

/-- the series `g` whose coefficients solve the triangular descent system -/
noncomputable def sympDesc (f : PowerSeries ℚ) : PowerSeries ℚ :=
  PowerSeries.mk (fun n => sympDescCoeff f n)

lemma sympDesc_coeff (f : PowerSeries ℚ) (n : ℕ) :
    PowerSeries.coeff n (sympDesc f) = sympDescCoeff f n := by
  simp [sympDesc]

/-- the even coefficients of `(sympDesc f)∘y` match those of `f` -/
lemma sympDesc_even (f : PowerSeries ℚ) (k : ℕ) :
    PowerSeries.coeff (2 * k) ((sympDesc f).subst sympY) = PowerSeries.coeff (2 * k) f := by
  rw [coeff_subst_range₂ (sympDesc f) coeff_sympY_zero coeff_sympY_one (2 * k)]
  have hr : (2 * k) / 2 + 1 = k + 1 := by omega
  rw [hr]
  calc
    (∑ m ∈ Finset.range (k + 1), PowerSeries.coeff m (sympDesc f) * PowerSeries.coeff (2 * k) (sympY ^ m))
        = (∑ m ∈ Finset.range k, PowerSeries.coeff m (sympDesc f) * PowerSeries.coeff (2 * k) (sympY ^ m))
            + PowerSeries.coeff k (sympDesc f) * PowerSeries.coeff (2 * k) (sympY ^ k) := by
            rw [Finset.sum_range_succ]
    _ = (∑ m ∈ Finset.range k, sympDescCoeff f m * PowerSeries.coeff (2 * k) (sympY ^ m))
            + sympDescCoeff f k * PowerSeries.coeff (2 * k) (sympY ^ k) := by
            congr 1
            · apply Finset.sum_congr rfl
              intro m hm
              rw [sympDesc_coeff]
            · rw [sympDesc_coeff]
    _ = PowerSeries.coeff (2 * k) f := by
            rw [sympDescCoeff_eq f k]
            have hcknz : PowerSeries.coeff (2 * k) (sympY ^ k) ≠ 0 := by
              rw [coeff_sympY_pow_diag k]
              exact pow_ne_zero k (by norm_num)
            rw [mul_assoc]
            rw [inv_mul_cancel₀ hcknz]
            rw [mul_one]
            ring

/-- `(sympDesc f)∘y` is invariant under `φ` -/
lemma sympDesc_y_invariant (f : PowerSeries ℚ) :
    PowerSeries.subst sympPhi ((sympDesc f).subst sympY) = (sympDesc f).subst sympY := by
  calc
    PowerSeries.subst sympPhi ((sympDesc f).subst sympY)
        = (sympDesc f).subst (sympY.subst sympPhi) := by
          rw [PowerSeries.subst_comp_subst_apply (R := ℚ) sympY_hasSubst sympPhi_hasSubst]
    _ = (sympDesc f).subst sympY := by rw [symp_y_invariant]

/-- `(sympDesc f)∘y = f` for `φ`-invariant `f` -/
lemma sympDesc_y_subst (f : PowerSeries ℚ) (hf : f.subst sympPhi = f) :
    (sympDesc f).subst sympY = f := by
  apply symp_invariant_eq_of_even_coeff_eq
  · exact sympDesc_y_invariant f
  · exact hf
  · intro k
    exact sympDesc_even f k

/-- substitution by `y` is injective: `A∘y = 0` forces `A = 0` -/
lemma symp_subst_y_injective (A : PowerSeries ℚ) (hA : A.subst sympY = 0) : A = 0 := by
  apply PowerSeries.ext
  intro n
  induction n using Nat.strong_induction_on with
  | h n ih =>
      have hEq := congrArg (PowerSeries.coeff (2 * n)) hA
      rw [coeff_subst_range₂ A coeff_sympY_zero coeff_sympY_one (2 * n)] at hEq
      have hr : (2 * n) / 2 + 1 = n + 1 := by omega
      rw [hr] at hEq
      rw [Finset.sum_range_succ] at hEq
      have hprev : (∑ m ∈ Finset.range n, PowerSeries.coeff m A * PowerSeries.coeff (2 * n) (sympY ^ m)) = 0 := by
        apply Finset.sum_eq_zero
        intro m hm
        have hz : PowerSeries.coeff m A = 0 := ih m (by simpa using (Finset.mem_range.mp hm))
        simp [hz]
      have hmain : PowerSeries.coeff n A * PowerSeries.coeff (2 * n) (sympY ^ n) = 0 := by
        simpa [hprev] using hEq
      have hcknz : PowerSeries.coeff (2 * n) (sympY ^ n) ≠ 0 := by
        rw [coeff_sympY_pow_diag n]
        exact pow_ne_zero n (by norm_num)
      exact (mul_eq_zero.mp hmain).resolve_right hcknz

/-- the descent: every `φ`-invariant series is a unique power series in `y` -/
theorem symp_descent (f : PowerSeries ℚ) (hf : f.subst sympPhi = f) :
    ∃! g : PowerSeries ℚ, g.subst sympY = f := by
  refine ⟨sympDesc f, sympDesc_y_subst f hf, ?_⟩
  intro g hg
  have hmain : PowerSeries.subst sympY (g - sympDesc f) = 0 := by
    calc
      PowerSeries.subst sympY (g - sympDesc f)
          = PowerSeries.subst sympY g - PowerSeries.subst sympY (sympDesc f) := by
            rw [PowerSeries.subst_sub sympY_hasSubst]
      _ = f - f := by rw [hg, sympDesc_y_subst f hf]
      _ = 0 := by ring
  have hInj := symp_subst_y_injective (g - sympDesc f) hmain
  exact sub_eq_zero.mp hInj

/-- `Sym⁺H :=` the unique series with `(Sym⁺H)∘y = H + H∘φ` -/
noncomputable def sympSym (H : PowerSeries ℚ) : PowerSeries ℚ :=
  (Classical.choose (symp_descent (H + H.subst sympPhi) (symp_symm_invariant H)))

lemma sympSym_subst (H : PowerSeries ℚ) :
    (sympSym H).subst sympY = H + H.subst sympPhi := by
  exact (Classical.choose_spec (symp_descent (H + H.subst sympPhi) (symp_symm_invariant H))).1


/-- `P_n = x^n + φ^n` (the `n`-th symmetrized power; paper eq. (polysym)) -/
def sympP (n : ℕ) : PowerSeries ℚ := X ^ n + sympPhi ^ n

/-- `P_0 = 2` -/
lemma sympP_zero : sympP 0 = 2 := by
  norm_num [sympP]

/-- `P_1 = y` (since `X + φ = y`) -/
lemma sympP_one : sympP 1 = sympY := by
  rw [sympP]
  rw [pow_one, pow_one]
  exact symp_x_add_phi

/-- the quadratic `X² = y·X − y` for the root `X` of `T² − y·T + y` -/
lemma symp_x_sq_eq : X ^ 2 = sympY * X - sympY := by
  have h := symp_quadratic
  have h' : X ^ 2 - (sympY * X - sympY) = 0 := by
    calc
      X ^ 2 - (sympY * X - sympY) = X ^ 2 - sympY * X + sympY := by ring
      _ = 0 := h
  exact sub_eq_zero.mp h'

/-- `φ² = y·φ − y` (φ satisfies the same quadratic, by substituting `X ↦ φ`) -/
lemma symp_phi_sq_eq : sympPhi ^ 2 = sympY * sympPhi - sympY := by
  have hx := congrArg (fun z : PowerSeries ℚ => PowerSeries.subst sympPhi z) symp_x_sq_eq
  have hx2 : PowerSeries.subst sympPhi ((X : PowerSeries ℚ) ^ 2) = sympPhi ^ 2 := by
    simpa [PowerSeries.subst_X sympPhi_hasSubst] using
      (PowerSeries.subst_pow (R := ℚ) sympPhi_hasSubst (X : PowerSeries ℚ) 2)
  have hyx : PowerSeries.subst sympPhi (sympY * X - sympY) = sympY * sympPhi - sympY := by
    rw [PowerSeries.subst_sub sympPhi_hasSubst, PowerSeries.subst_mul sympPhi_hasSubst,
        PowerSeries.subst_X sympPhi_hasSubst, symp_y_invariant]
  rwa [hx2, hyx] at hx

/-- if `t` satisfies the quadratic then the powers of `t` satisfy the
recurrence `t^{n+2} = y·t^{n+1} − y·tⁿ` -/
lemma symp_pow_succ_succ_of_quad (t : PowerSeries ℚ)
    (hq : t ^ 2 = sympY * t - sympY) (n : ℕ) :
    t ^ (n + 2) = sympY * t ^ (n + 1) - sympY * t ^ n := by
  calc
    t ^ (n + 2) = t ^ 2 * t ^ n := by
      rw [show n + 2 = n + 1 + 1 by omega]
      rw [pow_succ, pow_succ]
      ring
    _ = (sympY * t - sympY) * t ^ n := by rw [hq]
    _ = sympY * t ^ (n + 1) - sympY * t ^ n := by
      rw [sub_mul]
      have htt : t * t ^ n = t ^ (n + 1) := by
        rw [mul_comm, ← pow_succ]
      rw [mul_assoc, htt]

/-- the recurrence `P_{n+2} = y·P_{n+1} − y·P_n` (paper eq. (polysym)) -/
lemma sympP_succ_succ (n : ℕ) :
    sympP (n + 2) = sympY * sympP (n + 1) - sympY * sympP n := by
  calc
    sympP (n + 2) = X ^ (n + 2) + sympPhi ^ (n + 2) := by rfl
    _ = (sympY * X ^ (n + 1) - sympY * X ^ n) +
          (sympY * sympPhi ^ (n + 1) - sympY * sympPhi ^ n) := by
          rw [symp_pow_succ_succ_of_quad X symp_x_sq_eq n,
              symp_pow_succ_succ_of_quad sympPhi symp_phi_sq_eq n]
    _ = sympY * (X ^ (n + 1) + sympPhi ^ (n + 1)) - sympY * (X ^ n + sympPhi ^ n) := by ring
    _ = sympY * sympP (n + 1) - sympY * sympP n := by rfl

/-- `P_n` is `φ`-invariant (it is a power series in `y`) -/
lemma sympP_invariant (n : ℕ) :
    PowerSeries.subst sympPhi (sympP n) = sympP n := by
  calc
    PowerSeries.subst sympPhi (sympP n)
        = PowerSeries.subst sympPhi (X ^ n) + PowerSeries.subst sympPhi (sympPhi ^ n) := by
          rw [sympP]
          rw [PowerSeries.subst_add sympPhi_hasSubst]
    _ = sympPhi ^ n + X ^ n := by
          have h1 : PowerSeries.subst sympPhi ((X : PowerSeries ℚ) ^ n) = sympPhi ^ n := by
            simpa [PowerSeries.subst_X sympPhi_hasSubst] using
              (PowerSeries.subst_pow (R := ℚ) sympPhi_hasSubst (X : PowerSeries ℚ) n)
          have h2 : PowerSeries.subst sympPhi ((sympPhi : PowerSeries ℚ) ^ n) = X ^ n := by
            simpa [symp_phi_involutive] using
              (PowerSeries.subst_pow (R := ℚ) sympPhi_hasSubst (sympPhi : PowerSeries ℚ) n)
          rw [h1, h2]
    _ = X ^ n + sympPhi ^ n := by ring
    _ = sympP n := by rfl



/-- a series with integer coefficients -/
def IntSeries (F : PowerSeries ℚ) : Prop :=
  ∀ n : ℕ, ∃ z : ℤ, (z : ℚ) = PowerSeries.coeff n F

lemma intSeries_zero : IntSeries 0 := by
  intro n
  refine ⟨0, ?_⟩
  simp

lemma intSeries_one : IntSeries (1 : PowerSeries ℚ) := by
  intro n
  by_cases hn : n = 0
  · subst n
    refine ⟨1, ?_⟩
    simp
  · refine ⟨0, ?_⟩
    simp [hn]

lemma intSeries_X : IntSeries X := by
  intro n
  rw [PowerSeries.coeff_X]
  by_cases hn : n = 1
  · subst n
    refine ⟨1, ?_⟩
    norm_num
  · refine ⟨0, ?_⟩
    norm_num [hn]

lemma intSeries_neg {F : PowerSeries ℚ} (hF : IntSeries F) : IntSeries (-F) := by
  intro n
  rcases hF n with ⟨z, hz⟩
  refine ⟨-z, ?_⟩
  rw [map_neg, ← hz]
  norm_num

lemma intSeries_add {F G : PowerSeries ℚ} (hF : IntSeries F) (hG : IntSeries G) :
    IntSeries (F + G) := by
  intro n
  rcases hF n with ⟨zf, hzf⟩
  rcases hG n with ⟨zg, hzg⟩
  refine ⟨zf + zg, ?_⟩
  rw [map_add, ← hzf, ← hzg]
  norm_num

lemma intSeries_sub {F G : PowerSeries ℚ} (hF : IntSeries F) (hG : IntSeries G) :
    IntSeries (F - G) := by
  intro n
  rcases hF n with ⟨zf, hzf⟩
  rcases hG n with ⟨zg, hzg⟩
  refine ⟨zf - zg, ?_⟩
  rw [map_sub, ← hzf, ← hzg]
  norm_num

/-- a finite sum of products of integer coefficients is an integer -/
lemma exists_int_finset_sum_mul {ι : Type*} (s : Finset ι) {a b : ι → ℚ}
    (ha : ∀ i ∈ s, ∃ z : ℤ, (z : ℚ) = a i) (hb : ∀ i ∈ s, ∃ z : ℤ, (z : ℚ) = b i) :
    ∃ z : ℤ, (z : ℚ) = ∑ i ∈ s, a i * b i := by
  classical
  let fa : ι → ℤ := fun i => if h : i ∈ s then Classical.choose (ha i h) else 0
  let fb : ι → ℤ := fun i => if h : i ∈ s then Classical.choose (hb i h) else 0
  have hfa : ∀ i ∈ s, (fa i : ℚ) = a i := by
    intro i hi
    simp [fa, hi]
    exact Classical.choose_spec (ha i hi)
  have hfb : ∀ i ∈ s, (fb i : ℚ) = b i := by
    intro i hi
    simp [fb, hi]
    exact Classical.choose_spec (hb i hi)
  refine ⟨∑ i ∈ s, fa i * fb i, ?_⟩
  calc
    ((∑ i ∈ s, fa i * fb i : ℤ) : ℚ) = ∑ i ∈ s, ((fa i * fb i : ℤ) : ℚ) := by
      rw [Int.cast_sum]
    _ = ∑ i ∈ s, (fa i : ℚ) * (fb i : ℚ) := by
      apply Finset.sum_congr rfl
      intro i hi
      rw [Int.cast_mul]
    _ = ∑ i ∈ s, a i * b i := by
      apply Finset.sum_congr rfl
      intro i hi
      rw [hfa i hi, hfb i hi]

lemma exists_int_finset_sum {ι : Type*} (s : Finset ι) {a : ι → ℚ}
    (ha : ∀ i ∈ s, ∃ z : ℤ, (z : ℚ) = a i) :
    ∃ z : ℤ, (z : ℚ) = ∑ i ∈ s, a i := by
  classical
  let fa : ι → ℤ := fun i => if h : i ∈ s then Classical.choose (ha i h) else 0
  have hfa : ∀ i ∈ s, (fa i : ℚ) = a i := by
    intro i hi
    simp [fa, hi]
    exact Classical.choose_spec (ha i hi)
  refine ⟨∑ i ∈ s, fa i, ?_⟩
  calc
    ((∑ i ∈ s, fa i : ℤ) : ℚ) = ∑ i ∈ s, (fa i : ℚ) := by
      rw [Int.cast_sum]
    _ = ∑ i ∈ s, a i := by
      apply Finset.sum_congr rfl
      intro i hi
      rw [hfa i hi]

lemma intSeries_mul {F G : PowerSeries ℚ} (hF : IntSeries F) (hG : IntSeries G) :
    IntSeries (F * G) := by
  intro n
  rw [PowerSeries.coeff_mul]
  exact exists_int_finset_sum_mul (Finset.HasAntidiagonal.antidiagonal n)
    (fun p _ => hF p.1) (fun p _ => hG p.2)

lemma intSeries_pow {F : PowerSeries ℚ} (hF : IntSeries F) (m : ℕ) :
    IntSeries (F ^ m) := by
  induction m with
  | zero =>
      simpa using (intSeries_one : IntSeries (1 : PowerSeries ℚ))
  | succ m ih =>
      rw [pow_succ']
      exact intSeries_mul (F := F) (G := F ^ m) hF ih

/-- composition `F∘b` of integer-coefficient series (with `coeff 0 b = 0`)
is integer-coefficient -/
lemma intSeries_subst {F b : PowerSeries ℚ} (hF : IntSeries F)
    (hb0 : PowerSeries.coeff 0 b = 0) (hbp : ∀ m, IntSeries (b ^ m)) :
    IntSeries (F.subst b) := by
  intro n
  rw [coeff_subst_range F hb0 n]
  exact exists_int_finset_sum_mul (Finset.range (n + 1))
    (fun m _ => hF m) (fun m _ => hbp m n)



/-- all coefficients of `(X−1)⁻¹` are `−1` -/
lemma coeff_inv_X_sub_one (j : ℕ) :
    PowerSeries.coeff j (((X : PowerSeries ℚ) - 1)⁻¹) = -1 := by
  let f : PowerSeries ℚ := ((X : PowerSeries ℚ) - 1)⁻¹
  have hmul : ((X : PowerSeries ℚ) - 1) * f = 1 := by
    dsimp [f]
    exact PowerSeries.mul_inv_cancel ((X : PowerSeries ℚ) - 1) symp_sub_one_constant_ne
  have hf : ∀ j : ℕ, PowerSeries.coeff j f = -1 := by
    intro j
    induction j with
    | zero =>
        have hc := congrArg (PowerSeries.coeff 0) hmul
        have hc' : PowerSeries.coeff 0 (((X : PowerSeries ℚ) - 1) * f) = 1 := by
          simpa using hc
        have hsplit : PowerSeries.coeff 0 (((X : PowerSeries ℚ) - 1) * f) =
            PowerSeries.coeff 0 (X * f) - PowerSeries.coeff 0 f := by
          rw [sub_mul]
          rw [map_sub]
          rw [one_mul]
        have hx : PowerSeries.coeff 0 (X * f) = 0 := by simp
        have : PowerSeries.coeff 0 f = -1 := by
          rw [hsplit, hx] at hc'
          linarith
        exact this
    | succ j ih =>
        have hc := congrArg (PowerSeries.coeff (j + 1)) hmul
        have hc' : PowerSeries.coeff (j + 1) (((X : PowerSeries ℚ) - 1) * f) = 0 := by
          simpa using hc
        have hsplit : PowerSeries.coeff (j + 1) (((X : PowerSeries ℚ) - 1) * f) =
            PowerSeries.coeff (j + 1) (X * f) - PowerSeries.coeff (j + 1) f := by
          rw [sub_mul]
          rw [map_sub]
          rw [one_mul]
        have hx : PowerSeries.coeff (j + 1) (X * f) = PowerSeries.coeff j f := by
          exact PowerSeries.coeff_succ_X_mul j f
        have : PowerSeries.coeff (j + 1) f = -1 := by
          rw [hsplit, hx] at hc'
          linarith [ih]
        exact this
  simpa [f] using hf j

/-- `φ = X/(X−1)` has integer coefficients -/
lemma sympPhi_IntSeries : IntSeries sympPhi := by
  intro k
  by_cases hk : k = 0
  · subst k
    refine ⟨0, ?_⟩
    rw [coeff_sympPhi_zero]
    norm_num
  · refine ⟨-1, ?_⟩
    have hk1 : k = (k - 1) + 1 := by omega
    rw [hk1]
    unfold sympPhi
    rw [PowerSeries.coeff_succ_X_mul (k - 1) (((X : PowerSeries ℚ) - 1)⁻¹)]
    simpa using (coeff_inv_X_sub_one (k - 1)).symm

/-- `y = X·φ` has integer coefficients -/
lemma sympY_IntSeries : IntSeries sympY := by
  change IntSeries (X * sympPhi)
  exact intSeries_mul intSeries_X sympPhi_IntSeries

/-- the descent recursion with the inverse of `(−1)^n` evaluated (sign form,
with the sign as an integer cast) -/
lemma sympDescCoeff_eq_sign (f : PowerSeries ℚ) (n : ℕ) :
    sympDescCoeff f n =
      (PowerSeries.coeff (2 * n) f -
        ∑ m ∈ Finset.range n, sympDescCoeff f m * PowerSeries.coeff (2 * n) (sympY ^ m)) *
        (((-1 : ℤ) ^ n) : ℚ) := by
  calc
    sympDescCoeff f n
        = (PowerSeries.coeff (2 * n) f -
            ∑ m ∈ Finset.range n, sympDescCoeff f m * PowerSeries.coeff (2 * n) (sympY ^ m)) *
            (PowerSeries.coeff (2 * n) (sympY ^ n))⁻¹ := by
            rw [sympDescCoeff_eq f n]
    _ = (PowerSeries.coeff (2 * n) f -
            ∑ m ∈ Finset.range n, sympDescCoeff f m * PowerSeries.coeff (2 * n) (sympY ^ m)) *
            (((-1 : ℚ) ^ n)⁻¹) := by
            rw [coeff_sympY_pow_diag n]
    _ = (PowerSeries.coeff (2 * n) f -
            ∑ m ∈ Finset.range n, sympDescCoeff f m * PowerSeries.coeff (2 * n) (sympY ^ m)) *
            ((-1 : ℚ) ^ n) := by
            rw [← inv_pow]
            norm_num
    _ = (PowerSeries.coeff (2 * n) f -
            ∑ m ∈ Finset.range n, sympDescCoeff f m * PowerSeries.coeff (2 * n) (sympY ^ m)) *
            (((-1 : ℤ) ^ n) : ℚ) := by
            congr 1

/-- `(−1)^n` as an integer cast -/
lemma negOne_pow_cast_int (n : ℕ) : ((-1 : ℤ) ^ n : ℚ) = (-1 : ℚ) ^ n := by
  induction n with
  | zero => norm_num
  | succ m ih' =>
      rw [pow_succ, pow_succ, ih']
      norm_num

/-- the descent coefficients of an integer-coefficient series are integers -/
lemma sympDescCoeff_int (f : PowerSeries ℚ)
    (hfZ : ∀ n, ∃ z : ℤ, (z : ℚ) = PowerSeries.coeff n f)
    (hyZ : ∀ (k m : ℕ), ∃ z : ℤ, (z : ℚ) = PowerSeries.coeff k (sympY ^ m)) :
    ∀ n, ∃ z : ℤ, (z : ℚ) = sympDescCoeff f n := by
  intro n
  induction n using Nat.strong_induction_on with
  | h n ih =>
      have hzsum : ∃ Z : ℤ, (Z : ℚ) =
          ∑ m ∈ Finset.range n, sympDescCoeff f m * PowerSeries.coeff (2 * n) (sympY ^ m) := by
        apply exists_int_finset_sum_mul (s := Finset.range n)
        · intro m hm
          exact ih m (by simpa using (Finset.mem_range.mp hm))
        · intro m _
          exact hyZ (2 * n) m
      rcases hzsum with ⟨Z, hZ⟩
      rcases hfZ (2 * n) with ⟨zf, hzf⟩
      refine ⟨(zf - Z) * (-1 : ℤ) ^ n, ?_⟩
      rw [sympDescCoeff_eq_sign f n]
      rw [← hZ, ← hzf]
      push_cast
      rfl

/-- the descended series of an integer-coefficient series has integer
coefficients -/
lemma intSeries_sympDesc (f : PowerSeries ℚ)
    (hfZ : ∀ n, ∃ z : ℤ, (z : ℚ) = PowerSeries.coeff n f)
    (hyZ : ∀ (k m : ℕ), ∃ z : ℤ, (z : ℚ) = PowerSeries.coeff k (sympY ^ m)) :
    IntSeries (sympDesc f) := by
  intro n
  rw [sympDesc_coeff]
  exact sympDescCoeff_int f hfZ hyZ n

/-- `Sym⁺H` agrees with the explicitly-constructed descent series -/
lemma sympSym_eq_sympDesc (H : PowerSeries ℚ) :
    sympSym H = sympDesc (H + H.subst sympPhi) := by
  rw [← sub_eq_zero]
  apply symp_subst_y_injective (sympSym H - sympDesc (H + H.subst sympPhi))
  have hy : PowerSeries.HasSubst sympY := sympY_hasSubst
  calc
    PowerSeries.subst sympY (sympSym H - sympDesc (H + H.subst sympPhi))
        = PowerSeries.subst sympY (sympSym H) - PowerSeries.subst sympY (sympDesc (H + H.subst sympPhi)) := by
          rw [PowerSeries.subst_sub hy]
    _ = (H + H.subst sympPhi) - (H + H.subst sympPhi) := by
          rw [sympSym_subst H]
          rw [sympDesc_y_subst (H + H.subst sympPhi) (symp_symm_invariant H)]
    _ = 0 := by ring

/-- `Sym⁺H` has integer coefficients whenever `H` does -/
lemma sympSym_int (H : PowerSeries ℚ) (hH : IntSeries H) : IntSeries (sympSym H) := by
  rw [sympSym_eq_sympDesc H]
  apply intSeries_sympDesc
  · intro n
    exact intSeries_add hH
      (intSeries_subst hH coeff_sympPhi_zero (fun m => intSeries_pow sympPhi_IntSeries m)) n
  · intro k m
    exact intSeries_pow sympY_IntSeries m k

/-- `Sym⁺` is additive: `Sym⁺(f+g) = Sym⁺f + Sym⁺g` (both compose with
`y` to `(f+g) + (f+g)∘φ`; uniqueness in `symp_descent`) -/
lemma sympSym_add (f g : PowerSeries ℚ) :
    sympSym (f + g) = sympSym f + sympSym g := by
  have hsub : (sympSym f + sympSym g - sympSym (f + g)).subst sympY = 0 := by
    have hy : PowerSeries.HasSubst sympY := sympY_hasSubst
    calc
      PowerSeries.subst sympY (sympSym f + sympSym g - sympSym (f + g))
          = PowerSeries.subst sympY (sympSym f) + PowerSeries.subst sympY (sympSym g)
              - PowerSeries.subst sympY (sympSym (f + g)) := by
            rw [PowerSeries.subst_sub hy]
            rw [PowerSeries.subst_add hy]
      _ = (f + f.subst sympPhi) + (g + g.subst sympPhi) - ((f + g) + (f + g).subst sympPhi) := by
            rw [sympSym_subst f, sympSym_subst g, sympSym_subst (f + g)]
      _ = 0 := by
            rw [PowerSeries.subst_add sympPhi_hasSubst]
            ring
  have hEq := symp_subst_y_injective (sympSym f + sympSym g - sympSym (f + g)) hsub
  exact (sub_eq_zero.mp hEq).symm

/-- constants are fixed by substitution: `(C r)∘g = C r` -/
lemma C_subst_eq (R : Type) [CommRing R] (r : R) (g : PowerSeries R) (hg : PowerSeries.HasSubst g) :
    (PowerSeries.C r).subst g = PowerSeries.C r := by
  rw [show PowerSeries.C r = algebraMap R (PowerSeries R) r by rfl]
  rw [← PowerSeries.coe_substAlgHom hg]
  rw [AlgHom.commutes]

/-- `Sym⁺` is `ℚ`-linear on the scalar side: `Sym⁺(r·f) = r·Sym⁺f` (the
constant `r` is fixed by both substitutions) -/
lemma sympSym_C_mul (r : ℚ) (f : PowerSeries ℚ) :
    sympSym (PowerSeries.C r * f) = PowerSeries.C r * sympSym f := by
  have hsub : (PowerSeries.C r * sympSym f - sympSym (PowerSeries.C r * f)).subst sympY = 0 := by
    have hy : PowerSeries.HasSubst sympY := sympY_hasSubst
    calc
      PowerSeries.subst sympY (PowerSeries.C r * sympSym f - sympSym (PowerSeries.C r * f))
          = PowerSeries.subst sympY (PowerSeries.C r * sympSym f)
              - PowerSeries.subst sympY (sympSym (PowerSeries.C r * f)) := by
            rw [PowerSeries.subst_sub hy]
      _ = (PowerSeries.C r).subst sympY * (sympSym f).subst sympY
              - (PowerSeries.C r * f + (PowerSeries.C r * f).subst sympPhi) := by
            rw [PowerSeries.subst_mul hy, sympSym_subst (PowerSeries.C r * f)]
      _ = PowerSeries.C r * (f + f.subst sympPhi)
              - (PowerSeries.C r * f + (PowerSeries.C r * f).subst sympPhi) := by
            rw [sympSym_subst f]
            rw [C_subst_eq ℚ r sympY sympY_hasSubst]
      _ = 0 := by
            rw [PowerSeries.subst_mul sympPhi_hasSubst]
            rw [C_subst_eq ℚ r sympPhi sympPhi_hasSubst]
            ring
  have hEq := symp_subst_y_injective (PowerSeries.C r * sympSym f - sympSym (PowerSeries.C r * f)) hsub
  exact (sub_eq_zero.mp hEq).symm

end Submission.CDT
