/-
# Level of distribution of the shifted von Mangoldt function (`d ↦ ψ_d(x)`)

Target (verbatim):

```
∀ A : ℝ, 0 < A → ∃ B : ℝ, 0 < B ∧ ∀ᶠ x : ℕ in Filter.atTop,
  Σ_{d odd, 1 ≤ d ≤ ⌊√x / (log x)^B⌋} | Σ_{n ≤ x, d ∣ n+2} Λ(n) − x/φ(d) | ≤ x/(log x)^A.
```

This is the **Bombieri–Vinogradov theorem for the fixed residue class `−2 (mod d)`**,
restricted to odd moduli (which is a harmless sub-sum: every odd `d` has `gcd(d,−2)=1`,
so the shifted von Mangoldt mass on `n ≡ −2 (mod d)` is the same as the coprime one).

## Proof architecture (as carried out in the project)

Writing `ψ(x,χ) := Σ_{n ≤ x} Λ(n)χ(n)`, character orthogonality
(`Commons.NumberTheory.BombieriVinogradov.residue_vonMangoldt_char_sum`) gives, for
odd `d ≥ 3`,
`ψ_d(x) − x/φ(d) = (1/φ(d))·( ψ_{χ₀}(x) − x + Σ_{χ ≠ χ₀} χ̄(−2) ψ(x,χ) )`, hence
`|ψ_d(x) − x/φ(d)| ≤ (1/φ(d))·( |ψ(x) − x| + ω(d)log x + Σ_{χ ≠ χ₀} ‖ψ(x,χ)‖ )`.

Summing over odd `d ≤ D`, `D = ⌊√x/(log x)^B⌋`:
* the `d = 1` term is `|ψ(x) − x|` and the `|ψ(x)−x|`-part is
  `|ψ(x)−x|·Σ_{d≤D}1/φ(d) ≪ |ψ(x)−x|·log x ≤ x/(log x)^A` for large `x`, using the
  prime number theorem with power-of-log error
  (`Commons.NumberTheory.PrimeNumberTheorem.psi_sub_id_powLog`);
* the `ω(d)log x`-part is `≪ log x·Σ_{d≤D}ω(d)/φ(d) ≪ log^3 x ≪ x/(log x)^A`;
* what remains is the **character-sum engine**
  `Σ_{d odd ≤ D} (1/φ(d)) Σ_{χ ≠ χ₀ mod d} ‖ψ(x,χ)‖ ≤ x/(log x)^A`.
  This engine is the Bombieri/core analytic input: it is obtained by splitting the moduli at
  `R = ⌊(log x)^{A+6}⌋` and combining
  (i) *small moduli* `d ≤ R`: the **Siegel–Walfisz** estimate
      `‖ψ(x,χ)‖ ≤ x·exp(−c√log x)` uniformly for `d ≤ R` — whose proof requires the
      **Siegel zero bound** `1 − β ≥ c(ε)/N^ε` for a real zero `β` of `L(·,χ)`, `χ` real
      primitive mod `N` (Siegel's theorem, via the Dirichlet class number formula);
  (ii) *large moduli* `R < d ≤ D`: the Bombieri mean-value theorem (Vaughan decomposition
      of `Λ` + the bilinear character large sieve + Pólya–Vinogradov), summed by parts.

The pieces (i)/(ii) are produced by the sibling developments; this file contains the
reduction and the verbatim target. The statement is a theorem of "Siegel strength": for
`β` a real zero of a real primitive `χ mod q` the `d = q` summand alone equals
`x^β/φ(q)`, so the inequality for all `A` forces `(1−β)log x ≥ A log log x − log φ(q)`,
i.e. `L(1,χ) ≫ q^{−ε}`, which is Siegel's theorem.
-/
import Mathlib
import Submission.Commons.NumberTheory.BombieriVinogradov.residue_vonMangoldt_char_sum
import Submission.Commons.NumberTheory.PrimeNumberTheorem.psi_sub_id_powLog
import Submission.Commons.NumberTheory.BombieriVinogradov.bombieri_vinogradov_family

open Finset
open scoped BigOperators

namespace Commons.NumberTheory.BombieriVinogradov

noncomputable section

/-- The shifted von Mangoldt sum `Σ_{n ≤ x, d ∣ n+2} Λ(n)`. -/
noncomputable def psiD (x d : ℕ) : ℝ :=
  ((Finset.range (x + 1)).filter (fun n => d ∣ n + 2)).sum
    (fun n => ArithmeticFunction.vonMangoldt n)

/-- `ψ(x,χ) = Σ_{n ≤ x} Λ(n) χ(n)`. -/
noncomputable def psiChi (x q : ℕ) (χ : DirichletCharacter ℂ q) : ℂ :=
  ∑ n ∈ Finset.range (x + 1),
    ((ArithmeticFunction.vonMangoldt n : ℝ) : ℂ) * χ (n : ZMod q)

/-- Residue-box equivalence `n % d = (d−2) % d ↔ d ∣ n+2` (for `d ≥ 2`). -/
lemma mod_eq_sub_two_iff (d : ℕ) (hd : 2 ≤ d) (n : ℕ) :
    (n % d = (d - 2) % d) ↔ d ∣ n + 2 := by
  have hd2 : (d - 2) % d = d - 2 := Nat.mod_eq_of_lt (by omega)
  constructor
  · intro h
    rw [hd2] at h
    refine ⟨n / d + 1, ?_⟩
    have hdiv : d * (n / d) + n % d = n := Nat.div_add_mod n d
    rw [Nat.mul_add, Nat.mul_one]; omega
  · rintro ⟨k, hk⟩
    have hk1 : 1 ≤ k := by
      rcases Nat.eq_zero_or_pos k with h | h
      · subst h; omega
      · exact h
    have hn : n = (d - 2) + d * (k - 1) := by
      have : d * k = d * (k - 1) + d := by rw [← Nat.mul_succ]; congr 1; omega
      omega
    rw [hd2, hn, Nat.add_mul_mod_self_left, hd2]

/-- **Per-modulus character decomposition** (odd `d ≥ 3`).

The shifted von Mangoldt sum equals the average of `χ̄(−2)·ψ(x,χ)` over the Dirichlet
characters mod `d`, and its real part is the sum of the real parts. -/
theorem psiD_eq_char_average (x d : ℕ) (hd : 3 ≤ d) (hodd : d % 2 = 1) :
    psiD x d = (d.totient : ℝ)⁻¹ *
      (∑ χ : DirichletCharacter ℂ d, (χ (((d - 2 : ℕ) : ZMod d)⁻¹) * psiChi x d χ).re) := by
  haveI hd0 : NeZero d := ⟨by omega⟩
  have hcop : Nat.Coprime (d - 2) d := by
    rw [Nat.coprime_iff_gcd_eq_one]
    have h4 : Nat.gcd (d - 2) d ∣ 2 := by
      have h1 : Nat.gcd (d - 2) d ∣ d - 2 := Nat.gcd_dvd_left _ _
      have h2 : Nat.gcd (d - 2) d ∣ d := Nat.gcd_dvd_right _ _
      have h3 : Nat.gcd (d - 2) d ∣ (d - (d - 2)) := Nat.dvd_sub h2 h1
      rwa [show d - (d - 2) = 2 by omega] at h3
    have hle := Nat.le_of_dvd (by norm_num : 0 < 2) h4
    have hge : 1 ≤ Nat.gcd (d - 2) d := Nat.gcd_pos_of_pos_left d (by omega : 0 < d - 2)
    have hne : Nat.gcd (d - 2) d ≠ 2 := by
      intro hg
      have : (2 : ℕ) ∣ d := hg ▸ Nat.gcd_dvd_right (d - 2) d
      omega
    omega
  have hfil : (Finset.range (x + 1)).filter (fun n => d ∣ n + 2)
      = (Finset.range (x + 1)).filter (fun n => n % d = (d - 2) % d) := by
    apply Finset.filter_congr
    intro n _
    exact (mod_eq_sub_two_iff d (by omega) n).symm
  have hpd : psiD x d = ∑ n ∈ (Finset.range (x + 1)).filter (fun n => n % d = (d - 2) % d),
      ArithmeticFunction.vonMangoldt n := by rw [psiD, hfil]
  have hL : (∑ n ∈ (Finset.range (x + 1)).filter (fun n => n % d = (d - 2) % d),
        (ArithmeticFunction.vonMangoldt n : ℂ)).re
      = ∑ n ∈ (Finset.range (x + 1)).filter (fun n => n % d = (d - 2) % d),
        ArithmeticFunction.vonMangoldt n := by
    rw [Complex.re_sum]; apply Finset.sum_congr rfl; intro n _; rw [Complex.ofReal_re]
  have key := Commons.NumberTheory.BombieriVinogradov.residue_vonMangoldt_char_sum
    d x (d - 2) hcop
  have hre : Complex.re ((d.totient : ℂ)⁻¹ * ∑ χ : DirichletCharacter ℂ d,
        χ (((d - 2 : ℕ) : ZMod d)⁻¹) * ∑ n ∈ Finset.range (x + 1),
          ((ArithmeticFunction.vonMangoldt n : ℝ) : ℂ) * χ (n : ZMod d))
      = (d.totient : ℝ)⁻¹ * ∑ χ : DirichletCharacter ℂ d,
        (χ (((d - 2 : ℕ) : ZMod d)⁻¹) * ∑ n ∈ Finset.range (x + 1),
          ((ArithmeticFunction.vonMangoldt n : ℝ) : ℂ) * χ (n : ZMod d)).re := by
    have h1 : (d.totient : ℂ)⁻¹ = Complex.ofReal ((d.totient : ℝ)⁻¹) := by
      rw [Complex.ofReal_inv]; rfl
    rw [h1, Complex.re_ofReal_mul]
    congr 1
    exact Complex.re_sum Finset.univ (fun χ : DirichletCharacter ℂ d =>
      χ (((d - 2 : ℕ) : ZMod d)⁻¹) * ∑ n ∈ Finset.range (x + 1),
        ((ArithmeticFunction.vonMangoldt n : ℝ) : ℂ) * χ (n : ZMod d))
  rw [hpd, ← hL, key, hre]
  simp only [psiChi]

/-- The admissible residue family `q ↦ −2 (mod q)` for odd `q` and `q ↦ 1` for even `q`.
    (For odd `q`, `q − 2` is coprime to `q`; for even `q`, `1` is coprime to `q`.) -/
def bvRes (q : ℕ) : ℕ := if q % 2 = 1 then q - 2 else 1

/-- `psiD x 1` is the ordinary Chebyshev `ψ(x) = Σ_{n ≤ x} Λ(n)`. -/
lemma psiD_one (x : ℕ) :
    psiD x 1 = ∑ n ∈ Finset.range (x + 1), ArithmeticFunction.vonMangoldt n := by
  unfold psiD
  refine Finset.sum_congr ?_ (fun _ _ => rfl)
  ext n; simp

/-- **Reduction of the target to the Bombieri–Vinogradov sum over all moduli `q ∈ [2,D]`.**
The odd-`d` filter is discarded (a sub-sum) and the `q = 1` term is the prime number
theorem error `|ψ(x) − x|`.  Consequently the target follows from the family (all-moduli)
Bombieri–Vinogradov bound together with `psi_sub_id_powLog`. -/
theorem level_of_distribution_shift_vonMangoldt_of_moduli_sum
    (hFam : ∀ A : ℝ, 0 < A → ∃ B : ℝ, 0 < B ∧ ∀ᶠ x : ℕ in Filter.atTop,
      ((Finset.Icc 2 ⌊Real.sqrt (x : ℝ) / (Real.log (x : ℝ)) ^ B⌋₊)).sum
        (fun q => |psiD x q - (x : ℝ) / (Nat.totient q : ℝ)|)
      ≤ (x : ℝ) / (Real.log (x : ℝ)) ^ A) :
    ∀ A : ℝ, 0 < A → ∃ B : ℝ, 0 < B ∧ ∀ᶠ x : ℕ in Filter.atTop,
      ((Finset.Icc 1 ⌊Real.sqrt (x : ℝ) / (Real.log (x : ℝ)) ^ B⌋₊).filter
          (fun d : ℕ => d % 2 = 1)).sum
        (fun d =>
          |((Finset.range (x + 1)).filter (fun n => d ∣ n + 2)).sum
              (fun n => ArithmeticFunction.vonMangoldt n)
            - (x : ℝ) / (Nat.totient d : ℝ)|)
        ≤ (x : ℝ) / (Real.log (x : ℝ)) ^ A := by
  intro A hA
  obtain ⟨B, hBpos, hFamB⟩ := hFam (A + 1) (by linarith)
  have hPNT : ∀ᶠ x : ℕ in Filter.atTop,
      |(∑ n ∈ Finset.range (x + 1), ArithmeticFunction.vonMangoldt n) - (x : ℝ)|
        ≤ (x : ℝ) / (Real.log (x : ℝ)) ^ (A + 1) :=
    Commons.NumberTheory.PrimeNumberTheorem.psi_sub_id_powLog (A + 1) (by linarith)
  have hlarge : ∀ᶠ x : ℕ in Filter.atTop,
      2 * ((x : ℝ) / (Real.log (x : ℝ)) ^ (A + 1)) ≤ (x : ℝ) / (Real.log (x : ℝ)) ^ A := by
    filter_upwards [tendsto_natCast_atTop_atTop.eventually
      (Real.tendsto_log_atTop.eventually_ge_atTop 2)] with x hx
    have hlog : 2 ≤ Real.log (x : ℝ) := hx
    have hlogpos : 0 < Real.log (x : ℝ) := by linarith
    have hxnn : (0 : ℝ) ≤ (x : ℝ) := Nat.cast_nonneg x
    have hLA : 0 < (Real.log (x : ℝ)) ^ A := Real.rpow_pos_of_pos hlogpos A
    rw [Real.rpow_add hlogpos A 1, Real.rpow_one]
    rw [show 2 * ((x : ℝ) / ((Real.log (x : ℝ)) ^ A * Real.log (x : ℝ)))
        = (2 * (x : ℝ)) / ((Real.log (x : ℝ)) ^ A * Real.log (x : ℝ)) by ring]
    rw [div_le_div_iff₀ (by positivity) hLA]
    have hA0 : (0:ℝ) ≤ (x : ℝ) * (Real.log (x : ℝ)) ^ A := by positivity
    nlinarith [mul_nonneg hA0 (by linarith : (0:ℝ) ≤ Real.log (x : ℝ) - 2)]
  refine ⟨B, hBpos, ?_⟩
  filter_upwards [hFamB, hPNT, hlarge,
    tendsto_natCast_atTop_atTop.eventually (Filter.eventually_ge_atTop (2:ℝ))] with x hfam hpnt hbig hx2
  set D : ℕ := ⌊Real.sqrt (x : ℝ) / (Real.log (x : ℝ)) ^ B⌋₊ with hD
  have hx1 : (1:ℝ) < (x : ℝ) := by linarith
  have hlogx : 0 < Real.log (x : ℝ) := Real.log_pos hx1
  rcases Nat.eq_zero_or_pos D with hD0 | hD1
  · rw [hD0]
    have hemp : (Finset.Icc 1 0 : Finset ℕ) = ∅ := by
      apply Finset.eq_empty_iff_forall_notMem.mpr
      intro n hn; rw [Finset.mem_Icc] at hn; omega
    simp only [hemp, Finset.filter_empty, Finset.sum_empty]
    exact div_nonneg (Nat.cast_nonneg x) (le_of_lt (Real.rpow_pos_of_pos hlogx A))
  · set S : Finset ℕ := (Finset.Icc 1 D).filter (fun d : ℕ => d % 2 = 1) with hS
    set g : ℕ → ℝ := fun d => |psiD x d - (x : ℝ) / (Nat.totient d : ℝ)| with hg
    have h1S : 1 ∈ S := by
      rw [hS, Finset.mem_filter, Finset.mem_Icc]
      exact ⟨⟨le_refl 1, hD1⟩, by norm_num⟩
    have hsplit : S.sum g = g 1 + (S.erase 1).sum g := by
      rw [← Finset.sum_erase_add S g h1S]; ring
    have hsub : (S.erase 1).sum g ≤ (Finset.Icc 2 D).sum g := by
      refine Finset.sum_le_sum_of_subset_of_nonneg ?_ (fun d _ _ => abs_nonneg _)
      intro d hd
      rw [Finset.mem_erase] at hd
      obtain ⟨hdne, hdS⟩ := hd
      rw [hS, Finset.mem_filter, Finset.mem_Icc] at hdS
      obtain ⟨⟨hd1, hdD⟩, hodd⟩ := hdS
      rw [Finset.mem_Icc]
      exact ⟨by omega, hdD⟩
    have hg1 : g 1 = |(∑ n ∈ Finset.range (x + 1), ArithmeticFunction.vonMangoldt n) - (x : ℝ)| := by
      rw [hg]
      have h := psiD_one x
      simp only [h, Nat.totient_one]
      norm_num
    calc S.sum g = g 1 + (S.erase 1).sum g := hsplit
      _ ≤ |(∑ n ∈ Finset.range (x + 1), ArithmeticFunction.vonMangoldt n) - (x : ℝ)|
            + (Finset.Icc 2 D).sum g := by rw [hg1]; linarith [hsub]
      _ ≤ (x : ℝ) / (Real.log (x : ℝ)) ^ (A + 1) + (x : ℝ) / (Real.log (x : ℝ)) ^ (A + 1) := by
            linarith [hpnt, hfam]
      _ = 2 * ((x : ℝ) / (Real.log (x : ℝ)) ^ (A + 1)) := by ring
      _ ≤ (x : ℝ) / (Real.log (x : ℝ)) ^ A := hbig

theorem level_of_distribution_shift_vonMangoldt :
    ∀ A : ℝ, 0 < A → ∃ B : ℝ, 0 < B ∧ ∀ᶠ x : ℕ in Filter.atTop,
      ((Finset.Icc 1 ⌊Real.sqrt (x : ℝ) / (Real.log (x : ℝ)) ^ B⌋₊).filter
          (fun d : ℕ => d % 2 = 1)).sum
        (fun d =>
          |((Finset.range (x + 1)).filter (fun n => d ∣ n + 2)).sum
              (fun n => ArithmeticFunction.vonMangoldt n)
            - (x : ℝ) / (Nat.totient d : ℝ)|)
        ≤ (x : ℝ) / (Real.log (x : ℝ)) ^ A := by
  intro A hA
  obtain ⟨B, hBpos, hFam⟩ :=
    Commons.NumberTheory.BombieriVinogradov.bombieri_vinogradov_family (A + 1) (by linarith)
  have hPNT : ∀ᶠ x : ℕ in Filter.atTop,
      |(∑ n ∈ Finset.range (x + 1), ArithmeticFunction.vonMangoldt n) - (x : ℝ)|
        ≤ (x : ℝ) / (Real.log (x : ℝ)) ^ (A + 1) :=
    Commons.NumberTheory.PrimeNumberTheorem.psi_sub_id_powLog (A + 1) (by linarith)
  have hlarge : ∀ᶠ x : ℕ in Filter.atTop,
      2 * ((x : ℝ) / (Real.log (x : ℝ)) ^ (A + 1)) ≤ (x : ℝ) / (Real.log (x : ℝ)) ^ A := by
    filter_upwards [tendsto_natCast_atTop_atTop.eventually
      (Real.tendsto_log_atTop.eventually_ge_atTop (2 : ℝ))] with x hx
    have hlog : 2 ≤ Real.log (x : ℝ) := hx
    have hlogpos : 0 < Real.log (x : ℝ) := by linarith
    have hxnn : (0 : ℝ) ≤ (x : ℝ) := Nat.cast_nonneg x
    have hLA : 0 < (Real.log (x : ℝ)) ^ A := Real.rpow_pos_of_pos hlogpos A
    rw [Real.rpow_add hlogpos A 1, Real.rpow_one]
    rw [show 2 * ((x : ℝ) / ((Real.log (x : ℝ)) ^ A * Real.log (x : ℝ)))
        = (2 * (x : ℝ)) / ((Real.log (x : ℝ)) ^ A * Real.log (x : ℝ)) by ring]
    rw [div_le_div_iff₀ (by positivity) hLA]
    have hA0 : (0 : ℝ) ≤ (x : ℝ) * (Real.log (x : ℝ)) ^ A := by positivity
    nlinarith [mul_nonneg hA0 (by linarith : (0 : ℝ) ≤ Real.log (x : ℝ) - 2)]
  refine ⟨B, hBpos, ?_⟩
  have hcop : ∀ q, Nat.Coprime (bvRes q) q := by
    intro q
    rw [bvRes]
    by_cases hq : q % 2 = 1
    · rw [if_pos hq]
      rcases Nat.eq_zero_or_pos (q - 2) with h0 | hpos
      · have hq1 : q = 1 := by omega
        subst hq1; decide
      · rw [Nat.coprime_iff_gcd_eq_one]
        have h4 : Nat.gcd (q - 2) q ∣ 2 := by
          have h1 : Nat.gcd (q - 2) q ∣ q - 2 := Nat.gcd_dvd_left _ _
          have h2 : Nat.gcd (q - 2) q ∣ q := Nat.gcd_dvd_right _ _
          have h3 : Nat.gcd (q - 2) q ∣ (q - (q - 2)) := Nat.dvd_sub h2 h1
          rwa [show q - (q - 2) = 2 by omega] at h3
        have hle := Nat.le_of_dvd (by norm_num : 0 < 2) h4
        have hge : 1 ≤ Nat.gcd (q - 2) q := by
          have := Nat.gcd_pos_of_pos_right (q - 2) (by omega : 0 < q)
          omega
        have hne : Nat.gcd (q - 2) q ≠ 2 := by
          intro hg
          have : (2 : ℕ) ∣ q := hg ▸ Nat.gcd_dvd_right (q - 2) q
          omega
        omega
    · rw [if_neg hq]
      exact Nat.coprime_one_left q
  have hfam := hFam bvRes hcop
  filter_upwards [hfam, hPNT, hlarge,
    tendsto_natCast_atTop_atTop.eventually (Filter.eventually_ge_atTop (2 : ℝ))]
    with x hfamx hpnt hbig hx2
  set D : ℕ := ⌊Real.sqrt (x : ℝ) / (Real.log (x : ℝ)) ^ B⌋₊ with hD
  have hx1 : (1 : ℝ) < (x : ℝ) := by linarith
  have hlogx : 0 < Real.log (x : ℝ) := Real.log_pos hx1
  set S : Finset ℕ := (Finset.Icc 1 D).filter (fun d : ℕ => d % 2 = 1) with hS
  set g : ℕ → ℝ := fun d => |psiD x d - (x : ℝ) / (Nat.totient d : ℝ)| with hg
  set fs : ℕ → ℝ := fun q => |((Finset.range (x + 1)).filter (fun n => n % q = (bvRes q) % q)).sum
      (fun n => ArithmeticFunction.vonMangoldt n) - (x : ℝ) / (Nat.totient q : ℝ)| with hfs
  have hfamD : (Finset.Icc 2 D).sum fs ≤ (x : ℝ) / (Real.log (x : ℝ)) ^ (A + 1) := hfamx
  rcases Nat.eq_zero_or_pos D with hD0 | hD1
  · rw [hS, hD0]
    have hemp : (Finset.Icc 1 0 : Finset ℕ) = ∅ := by
      apply Finset.eq_empty_iff_forall_notMem.mpr
      intro n hn; rw [Finset.mem_Icc] at hn; omega
    simp only [hemp, Finset.filter_empty, Finset.sum_empty]
    exact div_nonneg (Nat.cast_nonneg x) (le_of_lt (Real.rpow_pos_of_pos hlogx A))
  · have h1S : 1 ∈ S := by
      rw [hS, Finset.mem_filter, Finset.mem_Icc]
      exact ⟨⟨le_refl 1, hD1⟩, by norm_num⟩
    have hsplit : S.sum g = g 1 + (S.erase 1).sum g := by
      rw [← Finset.sum_erase_add S g h1S]; ring
    have hd_eq : ∀ d ∈ S.erase 1, g d = fs d := by
      intro d hdmem
      rw [Finset.mem_erase] at hdmem
      obtain ⟨hdne, hdS⟩ := hdmem
      rw [hS, Finset.mem_filter, Finset.mem_Icc] at hdS
      obtain ⟨⟨hd1, hdD⟩, hodd⟩ := hdS
      have hd2 : 2 ≤ d := by omega
      have ha_d : bvRes d = d - 2 := by rw [bvRes, if_pos hodd]
      have hpsi : psiD x d = ∑ n ∈ (Finset.range (x + 1)).filter (fun n => n % d = (d - 2) % d),
          ArithmeticFunction.vonMangoldt n := by
        unfold psiD
        refine Finset.sum_congr ?_ (fun _ _ => rfl)
        apply Finset.filter_congr
        intro n _
        exact (mod_eq_sub_two_iff d hd2 n).symm
      simp only [hg, hfs]
      rw [ha_d, hpsi]
    have hsub : (S.erase 1).sum g ≤ (Finset.Icc 2 D).sum fs := by
      rw [show (S.erase 1).sum g = (S.erase 1).sum fs from
        Finset.sum_congr rfl (fun d hd => hd_eq d hd)]
      refine Finset.sum_le_sum_of_subset_of_nonneg ?_ (fun d _ _ => abs_nonneg _)
      intro d hdmem
      rw [Finset.mem_erase] at hdmem
      obtain ⟨hdne, hdS⟩ := hdmem
      rw [hS, Finset.mem_filter, Finset.mem_Icc] at hdS
      obtain ⟨⟨hd1, hdD⟩, hodd⟩ := hdS
      rw [Finset.mem_Icc]
      exact ⟨by omega, hdD⟩
    have hg1 : g 1 = |(∑ n ∈ Finset.range (x + 1), ArithmeticFunction.vonMangoldt n) - (x : ℝ)| := by
      rw [hg]
      have h := psiD_one x
      simp only [h, Nat.totient_one]
      norm_num
    calc S.sum g = g 1 + (S.erase 1).sum g := hsplit
      _ ≤ |(∑ n ∈ Finset.range (x + 1), ArithmeticFunction.vonMangoldt n) - (x : ℝ)|
            + (Finset.Icc 2 D).sum fs := by rw [hg1]; linarith [hsub]
      _ ≤ (x : ℝ) / (Real.log (x : ℝ)) ^ (A + 1) + (x : ℝ) / (Real.log (x : ℝ)) ^ (A + 1) := by
            linarith [hpnt, hfamD]
      _ = 2 * ((x : ℝ) / (Real.log (x : ℝ)) ^ (A + 1)) := by ring
      _ ≤ (x : ℝ) / (Real.log (x : ℝ)) ^ A := hbig

end

end Commons.NumberTheory.BombieriVinogradov
