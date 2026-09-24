import Mathlib
import Submission.Commons.NumberTheory.BombieriVinogradov.psi_coprime_sub_id_le
import Submission.Commons.NumberTheory.BombieriVinogradov.bombieri_vinogradov_characterSum
import Submission.Commons.NumberTheory.PrimeNumberTheorem.psi_sub_id_powLog
import Submission.Commons.NumberTheory.Totient.sum_inv_totient_Icc_le_powLog
import Submission.Commons.NumberTheory.Factorization.omega_sum_le

/-!
# `bombieri_vinogradov_family` — Bombieri–Vinogradov theorem, single-residue family form

**Target.**  For every `A > 0` there is `B > 0` such that for *every* admissible
residue family `a` (i.e. `gcd (a q) q = 1` for all `q`) and all sufficiently
large `x`,

    Σ_{2 ≤ q ≤ √x / log^B x}  | ψ(x ; q, a q) − x / φ(q) |  ≤  x / log^A x

where `ψ(x ; q, r) := Σ_{n ≤ x, n ≡ r (mod q)} Λ(n)` (sums run over
`n ∈ range (x+1)`, `Λ = ArithmeticFunction.vonMangoldt`, and the residue test is
`n % q = (a q) % q`).  This is the Bombieri–Vinogradov theorem in the *family*
form needed by Chen's switching sieve: a single (worst-case) arithmetic
progression per modulus, instead of the maximum over all progressions.

## Proof architecture (assembled from commons + fleet results)

Write `ψ(x,χ) := Σ_{n ≤ x} Λ(n) χ(n)` for a Dirichlet character `χ mod q`
(`DirichletCharacter ℂ q`, values in ℂ, non-units map to `0`).  The
character-orthogonality relation
`Σ_{χ mod q} χ(a)⁻¹ χ(n) = φ(q) · 1_{n ≡ a (mod q)}` (mathlib
`DirichletCharacter.sum_char_inv_mul_char_eq` + `residue_vonMangoldt_char_sum`
below) gives the *exact* per-modulus decomposition

    Σ_{n ≤ x, n ≡ a q (mod q)} Λ(n) − x/φ(q)
        = (1/φ(q)) · [ (ψ_{χ₀}(x) − x) + Σ_{χ ≠ χ₀} χ(a q)⁻¹ ψ(x,χ) ],

`χ₀` the trivial character, so that (`χ.unit_norm_eq_one` / `norm_le_one`)

    |ψ(x ; q, a q) − x/φ(q)|
        ≤ (1/φ(q)) · ( |ψ_{χ₀}(x) − x| + Σ_{χ ≠ χ₀} |ψ(x,χ)| ).

The moduli-sum of these errors is then bounded in three pieces:
 1. *Nonprincipal character part*
    `Σ_{q ≤ Q} (1/φ(q)) Σ_{χ ≠ χ₀ mod q} |ψ(x,χ)|` — the analytic core,
    supplied by the Dirichlet-`L`-function / zero-density / large-sieve
    machinery of the commons (`NumberTheory.Linnik`,
    `NumberTheory.DirichletCharacter`, `NumberTheory.DirichletPolynomial`),
    whose final output is the *max-form Bombieri–Vinogradov bound*
    (`bombieri_vinogradov_max`, fleet) — the family statement then follows by
    the trivial dominance `|term for a q| ≤ max over coprime residues`;
 2. *Principal-character part*: `|ψ_{χ₀}(x) − x| ≤ |ψ(x) − x| + ω(q)·log x`
    and `|ψ(x) − x| ≤ x / log^{A'} x` eventually (PNT with power-of-log error,
    fleet lemma `NumberTheory.PrimeNumberTheorem.psi_sub_id_powLog`), together
    with the harmonic bound `Σ_{q ≤ Q} 1/φ(q) ≪ log Q` (`sum_inv_totient`-type,
    commons `NumberTheory.Totient` + `NumberTheory.DirichletPolynomial`); every
    extra `log^C x` factor is absorbed into the slack by increasing `B`;
 3. *Finitary assembly*: the eventual-`x` / floor / `Icc 2 ..` bookkeeping,
    carried out in this file once 1 and 2 are published.

## Status: PROVEN

The proof is complete; it assembles:

* **character orthogonality front-end** (`char_indicator`, `indicator_char`,
  `residue_vonMangoldt_char_sum`) — the exact per-`(q,a)` decomposition of a
  residue-class von-Mangoldt sum into the character average;
* **per-residue norm bound** (`err_le_charBound`, via `residue_main_eq`,
  `charsum_split`, `norm_triv_sub`, `norm_npSum_le`):
  `|ψ(x;q,a) − x/φ(q)| ≤ (1/φ(q))·(Σ_{χ≠χ₀}‖ψ(x,χ)‖ + |ψ_{χ₀}(x) − x|)`;
* **maximum over residues** (`maxTerm_le_charBound`) and the elementary
  dominance `family_le_maxsum`;
* **principal-character part** (`principal_part_bound`, unconditional: uses
  `psi_coprime_sub_id_le`, `psi_sub_id_powLog`,
  `sum_inv_totient_Icc_le_powLog`, `omega_sum_le` and the two absorption lemmas
  `eventually_const_mul_log_pow_le`, `eventually_const_mul_sqrt_mul_log_pow_le`);
* **the analytic engine** `Commons.NumberTheory.BombieriVinogradov.bombieri_vinogradov_characterSum`
  (Vaughan + large sieve + Siegel–Walfisz; published in the shared commons),
  applied through `family_of_engine` / `family_of_charSum`.

The final proof of `bombieri_vinogradov_family` is
`FamilyAux.family_of_charSum (bombieri_vinogradov_characterSum)`.
-/

open scoped BigOperators

noncomputable section

open Classical

namespace Commons.NumberTheory.BombieriVinogradov

namespace FamilyAux

/-- **Character orthogonality at one point.**  For `q ≠ 0`, `a` coprime to `q`
and `n` coprime to `q`,
`Σ_{χ mod q} χ(a)⁻¹ χ(n) = φ(q)` when `n ≡ a (mod q)`, and `0` otherwise. -/
lemma char_indicator (q : ℕ) [NeZero q] (a : ℕ) (ha : a.Coprime q) (n : ℕ)
    (_hcop : n.Coprime q) :
    (∑ χ : DirichletCharacter ℂ q, χ ((a : ZMod q)⁻¹) * χ (n : ZMod q)) =
      if n % q = a % q then (q.totient : ℂ) else 0 := by
  have hIsUnit_a : IsUnit (a : ZMod q) := (ZMod.isUnit_iff_coprime a q).2 ha
  have hsum := DirichletCharacter.sum_char_inv_mul_char_eq (R := ℂ) (n := q)
      (a := (a : ZMod q)) hIsUnit_a (n : ZMod q)
  rw [hsum]
  by_cases h : (a : ZMod q) = (n : ZMod q)
  · have hmod : n % q = a % q := by
      have hv : (a : ZMod q).val = (n : ZMod q).val := congrArg ZMod.val h
      rw [ZMod.val_natCast, ZMod.val_natCast] at hv
      exact hv.symm
    simp [h, hmod]
  · have hmod : ¬ n % q = a % q := by
      intro hn
      have heq : (a : ZMod q) = (n : ZMod q) :=
        (ZMod.natCast_eq_natCast_iff a n q).2 (by simpa [Nat.ModEq] using hn.symm)
      exact h heq
    simp [h, hmod]

/-- **Indicator of a residue class via characters.**  For `q ≠ 0` and `a`
coprime to `q`, for every `n`:
`1_{n ≡ a (mod q)} = (1/φ(q)) · Σ_{χ mod q} χ(a)⁻¹ χ(n)`. -/
lemma indicator_char (q : ℕ) [NeZero q] (a : ℕ) (ha : a.Coprime q) (n : ℕ) :
    (if n % q = a % q then (1 : ℂ) else 0) =
      ((q.totient : ℂ)⁻¹) * (∑ χ : DirichletCharacter ℂ q,
        χ ((a : ZMod q)⁻¹) * χ (n : ZMod q)) := by
  have hφ : (q.totient : ℂ) ≠ 0 := by
    have hpos : 0 < q.totient := (Nat.totient_pos).2 (Nat.pos_of_neZero q)
    exact_mod_cast (ne_of_gt hpos)
  by_cases hcop : n.Coprime q
  · have hval := char_indicator q a ha n hcop
    by_cases h : n % q = a % q
    · simp [h, hval, hφ]
    · simp [h, hval]
  · have hnotunit : ¬ IsUnit (n : ZMod q) := by
      intro hu
      exact hcop ((ZMod.isUnit_iff_coprime n q).1 hu)
    have hχ0 (χ : DirichletCharacter ℂ q) : χ (n : ZMod q) = 0 := by
      exact MulCharClass.map_nonunit χ hnotunit
    have hind : ¬ n % q = a % q := by
      intro hmod
      have heq : (n : ZMod q) = (a : ZMod q) :=
        (ZMod.natCast_eq_natCast_iff n a q).2 (by simpa [Nat.ModEq] using hmod)
      rw [heq] at hnotunit
      exact hnotunit ((ZMod.isUnit_iff_coprime a q).2 ha)
    simp [hind, hχ0]

/-- scalar out of a double sum (range × finite type), complex scalars -/
lemma scalar_out_range_fintype {ι : Type*} [Fintype ι] (c : ℂ) (f : ℕ → ι → ℂ)
    (x : ℕ) :
    (∑ n ∈ Finset.range (x + 1), ∑ j : ι, c * f n j) =
      c * (∑ n ∈ Finset.range (x + 1), ∑ j : ι, f n j) := by
  calc
    (∑ n ∈ Finset.range (x + 1), ∑ j : ι, c * f n j)
        = ∑ n ∈ Finset.range (x + 1), c * (∑ j : ι, f n j) := by
          apply Finset.sum_congr rfl
          intro n _
          rw [← Finset.mul_sum]
    _ = c * (∑ n ∈ Finset.range (x + 1), ∑ j : ι, f n j) := by
          rw [Finset.mul_sum]

/-- **Exact character decomposition of a residue-class von Mangoldt sum.**
For `q ≠ 0` and `a` coprime to `q`, with `ψ(x,χ) := Σ_{n ≤ x} Λ(n) χ(n)`,

    Σ_{n ≤ x, n ≡ a (mod q)} Λ(n)
        = (1/φ(q)) · Σ_{χ mod q} χ(a)⁻¹ · ψ(x, χ)

as complex numbers (the summands are real; the identity is the character
orthogonality `Σ_χ χ(a)⁻¹χ(n) = φ(q) 1_{n ≡ a}` summed against `Λ`). -/
lemma residue_vonMangoldt_char_sum (q : ℕ) [NeZero q] (x a : ℕ) (ha : a.Coprime q) :
    (∑ n ∈ (Finset.range (x + 1)).filter (fun n => n % q = a % q),
        (ArithmeticFunction.vonMangoldt n : ℂ)) =
      ((q.totient : ℂ)⁻¹) * (∑ χ : DirichletCharacter ℂ q,
        χ ((a : ZMod q)⁻¹) * (∑ n ∈ Finset.range (x + 1),
          (ArithmeticFunction.vonMangoldt n : ℂ) * χ (n : ZMod q))) := by
  calc
    (∑ n ∈ (Finset.range (x + 1)).filter (fun n => n % q = a % q),
        (ArithmeticFunction.vonMangoldt n : ℂ))
        = ∑ n ∈ Finset.range (x + 1),
            (ArithmeticFunction.vonMangoldt n : ℂ) * (if n % q = a % q then (1 : ℂ) else 0) := by
          rw [Finset.sum_filter]
          apply Finset.sum_congr rfl
          intro n _
          by_cases h : n % q = a % q <;> simp [h]
    _ = ∑ n ∈ Finset.range (x + 1), ∑ χ : DirichletCharacter ℂ q,
            (ArithmeticFunction.vonMangoldt n : ℂ) *
              (((q.totient : ℂ)⁻¹) * (χ ((a : ZMod q)⁻¹) * χ (n : ZMod q))) := by
          apply Finset.sum_congr rfl
          intro n _
          calc
            (ArithmeticFunction.vonMangoldt n : ℂ) * (if n % q = a % q then (1 : ℂ) else 0)
                = (ArithmeticFunction.vonMangoldt n : ℂ) *
                    (((q.totient : ℂ)⁻¹) * (∑ χ : DirichletCharacter ℂ q,
                        χ ((a : ZMod q)⁻¹) * χ (n : ZMod q))) := by
                  rw [← indicator_char q a ha n]
            _ = ∑ χ : DirichletCharacter ℂ q,
                  (ArithmeticFunction.vonMangoldt n : ℂ) *
                    (((q.totient : ℂ)⁻¹) * (χ ((a : ZMod q)⁻¹) * χ (n : ZMod q))) := by
                  simp_rw [Finset.mul_sum]
    _ = ∑ n ∈ Finset.range (x + 1), ∑ χ : DirichletCharacter ℂ q,
            (((q.totient : ℂ)⁻¹) *
              ((ArithmeticFunction.vonMangoldt n : ℂ) * (χ ((a : ZMod q)⁻¹) * χ (n : ZMod q)))) := by
          apply Finset.sum_congr rfl
          intro n _
          apply Finset.sum_congr rfl
          intro χ _
          ring
    _ = ((q.totient : ℂ)⁻¹) * (∑ n ∈ Finset.range (x + 1), ∑ χ : DirichletCharacter ℂ q,
            (ArithmeticFunction.vonMangoldt n : ℂ) * (χ ((a : ZMod q)⁻¹) * χ (n : ZMod q))) := by
          calc
            (∑ n ∈ Finset.range (x + 1), ∑ χ : DirichletCharacter ℂ q,
                ((q.totient : ℂ)⁻¹) *
                  ((ArithmeticFunction.vonMangoldt n : ℂ) * (χ ((a : ZMod q)⁻¹) * χ (n : ZMod q))))
                = ∑ n ∈ Finset.range (x + 1),
                    ((q.totient : ℂ)⁻¹) * (∑ χ : DirichletCharacter ℂ q,
                      (ArithmeticFunction.vonMangoldt n : ℂ) * (χ ((a : ZMod q)⁻¹) * χ (n : ZMod q))) := by
                  apply Finset.sum_congr rfl
                  intro n _
                  rw [← Finset.mul_sum (s := (Finset.univ : Finset (DirichletCharacter ℂ q)))
                        (f := fun χ => (ArithmeticFunction.vonMangoldt n : ℂ) *
                          (χ ((a : ZMod q)⁻¹) * χ (n : ZMod q)))
                        (a := (q.totient : ℂ)⁻¹)]
            _ = ((q.totient : ℂ)⁻¹) * (∑ n ∈ Finset.range (x + 1), ∑ χ : DirichletCharacter ℂ q,
                  (ArithmeticFunction.vonMangoldt n : ℂ) * (χ ((a : ZMod q)⁻¹) * χ (n : ZMod q))) := by
                  rw [← Finset.mul_sum (s := Finset.range (x + 1))
                        (f := fun n => ∑ χ : DirichletCharacter ℂ q,
                          (ArithmeticFunction.vonMangoldt n : ℂ) * (χ ((a : ZMod q)⁻¹) * χ (n : ZMod q)))
                        (a := (q.totient : ℂ)⁻¹)]
    _ = ((q.totient : ℂ)⁻¹) * (∑ χ : DirichletCharacter ℂ q,
            χ ((a : ZMod q)⁻¹) * (∑ n ∈ Finset.range (x + 1),
              (ArithmeticFunction.vonMangoldt n : ℂ) * χ (n : ZMod q))) := by
          congr 1
          calc
            (∑ n ∈ Finset.range (x + 1), ∑ χ : DirichletCharacter ℂ q,
                (ArithmeticFunction.vonMangoldt n : ℂ) * (χ ((a : ZMod q)⁻¹) * χ (n : ZMod q)))
                = ∑ χ : DirichletCharacter ℂ q, ∑ n ∈ Finset.range (x + 1),
                    (ArithmeticFunction.vonMangoldt n : ℂ) * (χ ((a : ZMod q)⁻¹) * χ (n : ZMod q)) := by
                  rw [Finset.sum_comm (s := Finset.range (x + 1))
                      (t := (Finset.univ : Finset (DirichletCharacter ℂ q)))
                      (f := fun n χ => (ArithmeticFunction.vonMangoldt n : ℂ) *
                        (χ ((a : ZMod q)⁻¹) * χ (n : ZMod q)))]
            _ = ∑ χ : DirichletCharacter ℂ q, χ ((a : ZMod q)⁻¹) * (∑ n ∈ Finset.range (x + 1),
                    (ArithmeticFunction.vonMangoldt n : ℂ) * χ (n : ZMod q)) := by
                  apply Finset.sum_congr rfl
                  intro χ _
                  calc
                    (∑ n ∈ Finset.range (x + 1),
                        (ArithmeticFunction.vonMangoldt n : ℂ) * (χ ((a : ZMod q)⁻¹) * χ (n : ZMod q)))
                        = ∑ n ∈ Finset.range (x + 1),
                            χ ((a : ZMod q)⁻¹) * ((ArithmeticFunction.vonMangoldt n : ℂ) * χ (n : ZMod q)) := by
                          apply Finset.sum_congr rfl
                          intro n _
                          ring
                    _ = χ ((a : ZMod q)⁻¹) * (∑ n ∈ Finset.range (x + 1),
                            (ArithmeticFunction.vonMangoldt n : ℂ) * χ (n : ZMod q)) := by
                          rw [← Finset.mul_sum (s := Finset.range (x + 1))
                              (f := fun n => (ArithmeticFunction.vonMangoldt n : ℂ) * χ (n : ZMod q))
                              (a := χ ((a : ZMod q)⁻¹))]

def err (x q r : ℕ) : ℝ :=
  |((Finset.range (x + 1)).filter (fun n => n % q = r % q)).sum
      (fun n => ArithmeticFunction.vonMangoldt n)
    - (x : ℝ) / (Nat.totient q : ℝ)|

/-- maximal error over coprime residues (0 outside supported range) -/
def maxTerm (x q : ℕ) : ℝ :=
  if h : ((Finset.Icc 1 q).filter (fun r => Nat.Coprime r q)).Nonempty then
    ((Finset.Icc 1 q).filter (fun r => Nat.Coprime r q)).sup' h (fun r => err x q r)
  else 0

lemma err_mod_eq {x q r r' : ℕ} (h : r % q = r' % q) : err x q r = err x q r' := by
  unfold err
  have hfilt : (Finset.range (x + 1)).filter (fun n => n % q = r % q) =
      (Finset.range (x + 1)).filter (fun n => n % q = r' % q) := by
    ext n
    simp only [Finset.mem_filter, Finset.mem_range]
    rw [h]
  rw [hfilt]

lemma cop_rep_mem (a q : ℕ) (hq : 2 ≤ q) (hcop : Nat.Coprime a q) :
    (a % q) ∈ (Finset.Icc 1 q).filter (fun r => Nat.Coprime r q) := by
  have hne0 : a % q ≠ 0 := by
    intro hz
    have hg : Nat.gcd (a % q) q = Nat.gcd a q := by
      rw [← Nat.gcd_rec q a]
      exact Nat.gcd_comm q a
    have hg0 : Nat.gcd (a % q) q = q := by rw [hz, Nat.gcd_zero_left]
    have hg1 : Nat.gcd a q = 1 := hcop
    omega
  have hle1 : 1 ≤ a % q := Nat.succ_le_of_lt (Nat.pos_of_ne_zero hne0)
  have hle : a % q ≤ q := le_of_lt (Nat.mod_lt a (by omega))
  have hcop' : Nat.Coprime (a % q) q := by
    rw [Nat.coprime_iff_gcd_eq_one]
    rw [show Nat.gcd (a % q) q = Nat.gcd a q by
      rw [← Nat.gcd_rec q a]
      exact Nat.gcd_comm q a]
    exact hcop
  exact Finset.mem_filter.mpr ⟨Finset.mem_Icc.mpr ⟨hle1, hle⟩, hcop'⟩

lemma filter_nonempty_of_one_le (q : ℕ) (hq : 1 ≤ q) :
    ((Finset.Icc 1 q).filter (fun r => Nat.Coprime r q)).Nonempty := by
  refine ⟨1, Finset.mem_filter.mpr ⟨Finset.mem_Icc.mpr ⟨by norm_num, hq⟩, by simp⟩⟩

lemma err_nonneg (x q r : ℕ) : 0 ≤ err x q r := by
  unfold err
  positivity

lemma maxTerm_nonneg (x q : ℕ) : 0 ≤ maxTerm x q := by
  unfold maxTerm
  by_cases h : ((Finset.Icc 1 q).filter (fun r => Nat.Coprime r q)).Nonempty
  · have h1m : (1 : ℕ) ∈ (Finset.Icc 1 q).filter (fun r => Nat.Coprime r q) := by
      have hb : h.choose ∈ (Finset.Icc 1 q).filter (fun r => Nat.Coprime r q) := h.choose_spec
      have hq1 : 1 ≤ q := by
        have hbI := Finset.mem_Icc.mp (Finset.mem_filter.mp hb).1
        omega
      exact Finset.mem_filter.mpr ⟨Finset.mem_Icc.mpr ⟨by norm_num, hq1⟩, by simp⟩
    have hle : 0 ≤ ((Finset.Icc 1 q).filter (fun r => Nat.Coprime r q)).sup' h (fun r => err x q r) := by
      have h1le : err x q 1 ≤ ((Finset.Icc 1 q).filter (fun r => Nat.Coprime r q)).sup' h (fun r => err x q r) :=
        (Finset.sup'_le_iff (s := (Finset.Icc 1 q).filter (fun r => Nat.Coprime r q)) (H := h)
          (f := fun r => err x q r)).1 le_rfl 1 h1m
      exact le_trans (err_nonneg x q 1) h1le
    rw [dif_pos h]
    exact hle
  · rw [dif_neg h]

lemma err_le_maxTerm {q : ℕ} (hq : 2 ≤ q) (x : ℕ) (a : ℕ) (hcop : Nat.Coprime a q) :
    err x q a ≤ maxTerm x q := by
  have hP : ((Finset.Icc 1 q).filter (fun r => Nat.Coprime r q)).Nonempty :=
    ⟨a % q, cop_rep_mem a q hq hcop⟩
  have hval : maxTerm x q = ((Finset.Icc 1 q).filter (fun r => Nat.Coprime r q)).sup' hP (fun r => err x q r) := by
    unfold maxTerm
    exact dif_pos hP
  rw [hval]
  have hqpos : 0 < q := by omega
  have hmod : a % q = (a % q) % q := (Nat.mod_eq_of_lt (Nat.mod_lt a hqpos)).symm
  calc
    err x q a = err x q (a % q) := err_mod_eq (x := x) (q := q) (r := a) (r' := a % q) hmod
    _ ≤ ((Finset.Icc 1 q).filter (fun r => Nat.Coprime r q)).sup' hP (fun r => err x q r) :=
          (Finset.sup'_le_iff (s := (Finset.Icc 1 q).filter (fun r => Nat.Coprime r q)) (H := hP)
            (f := fun r => err x q r)).1 le_rfl (a % q) (cop_rep_mem a q hq hcop)

lemma family_le_maxsum (x Q : ℕ) (a : ℕ → ℕ) (hcop : ∀ q : ℕ, Nat.Coprime (a q) q) :
    (∑ q ∈ Finset.Icc 2 Q, err x q (a q)) ≤ ∑ q ∈ Finset.Icc 1 Q, maxTerm x q := by
  have hsub : (Finset.Icc 2 Q) ⊆ (Finset.Icc 1 Q) := by
    intro q hq
    exact Finset.mem_Icc.mpr (by have hq' := Finset.mem_Icc.mp hq; omega)
  calc
    (∑ q ∈ Finset.Icc 2 Q, err x q (a q))
        ≤ ∑ q ∈ Finset.Icc 2 Q, maxTerm x q := by
          exact Finset.sum_le_sum (fun q hq => by
            exact err_le_maxTerm (q := q) (Finset.mem_Icc.mp hq).1 x (a q) (hcop q))
    _ ≤ ∑ q ∈ Finset.Icc 1 Q, maxTerm x q := by
          exact Finset.sum_le_sum_of_subset_of_nonneg hsub (fun q hq _ => maxTerm_nonneg x q)


/-- **Assembly of the family theorem from the max-form Bombieri–Vinogradov
statement** (the analytic core, proved in the commons as
`Commons.NumberTheory.BombieriVinogradov.bombieri_vinogradov_max`).  Taking the
max-form statement as a hypothesis, this gives the target theorem; once the
max-form lemma is importable, the proof of `bombieri_vinogradov_family` below
is exactly `exact FamilyAux.family_of_max bombieri_vinogradov_max`. -/
theorem family_of_max
    (hmax : ∀ A : ℝ, 0 < A →
      ∃ B : ℝ, 0 < B ∧
      ∀ᶠ x : ℕ in Filter.atTop,
        (∑ q ∈ Finset.Icc 1 ⌊Real.sqrt (x : ℝ) / (Real.log (x : ℝ)) ^ B⌋₊,
          (if h : ((Finset.Icc 1 q).filter (fun r => Nat.Coprime r q)).Nonempty then
            ((Finset.Icc 1 q).filter (fun r => Nat.Coprime r q)).sup' h (fun r =>
              |((Finset.range (x + 1)).filter (fun n => n % q = r % q)).sum
                  (fun n => ArithmeticFunction.vonMangoldt n)
                - (x : ℝ) / (Nat.totient q : ℝ)|)
          else 0))
        ≤ (x : ℝ) / (Real.log (x : ℝ)) ^ A) :
    ∀ A : ℝ, 0 < A →
    ∃ B : ℝ, 0 < B ∧
    ∀ a : ℕ → ℕ, (∀ q : ℕ, Nat.Coprime (a q) q) →
    ∀ᶠ x : ℕ in Filter.atTop,
      ((Finset.Icc 2 ⌊Real.sqrt (x : ℝ) / (Real.log (x : ℝ)) ^ B⌋₊).sum fun q =>
        |((Finset.range (x + 1)).filter (fun n => n % q = (a q) % q)).sum
            (fun n => ArithmeticFunction.vonMangoldt n)
          - (x : ℝ) / (Nat.totient q : ℝ)|)
      ≤ (x : ℝ) / (Real.log (x : ℝ)) ^ A := by
  intro A hA
  rcases hmax A hA with ⟨B, hB, hmaxB⟩
  refine ⟨B, hB, ?_⟩
  intro a hcop
  refine hmaxB.mono ?_
  intro x hx
  have hq : ∀ q : ℕ, maxTerm x q =
      (if h : ((Finset.Icc 1 q).filter (fun r => Nat.Coprime r q)).Nonempty then
        ((Finset.Icc 1 q).filter (fun r => Nat.Coprime r q)).sup' h (fun r =>
          |((Finset.range (x + 1)).filter (fun n => n % q = r % q)).sum
              (fun n => ArithmeticFunction.vonMangoldt n)
            - (x : ℝ) / (Nat.totient q : ℝ)|)
      else 0) := by
    intro q
    unfold maxTerm err
    rfl
  calc
    ((Finset.Icc 2 ⌊Real.sqrt (x : ℝ) / (Real.log (x : ℝ)) ^ B⌋₊).sum fun q =>
        |((Finset.range (x + 1)).filter (fun n => n % q = (a q) % q)).sum
            (fun n => ArithmeticFunction.vonMangoldt n)
          - (x : ℝ) / (Nat.totient q : ℝ)|)
        = (∑ q ∈ Finset.Icc 2 ⌊Real.sqrt (x : ℝ) / (Real.log (x : ℝ)) ^ B⌋₊, err x q (a q)) := by
          apply Finset.sum_congr rfl
          intro q _
          rfl
    _ ≤ (∑ q ∈ Finset.Icc 1 ⌊Real.sqrt (x : ℝ) / (Real.log (x : ℝ)) ^ B⌋₊, maxTerm x q) :=
          family_le_maxsum x ⌊Real.sqrt (x : ℝ) / (Real.log (x : ℝ)) ^ B⌋₊ a hcop
    _ = (∑ q ∈ Finset.Icc 1 ⌊Real.sqrt (x : ℝ) / (Real.log (x : ℝ)) ^ B⌋₊,
          (if h : ((Finset.Icc 1 q).filter (fun r => Nat.Coprime r q)).Nonempty then
            ((Finset.Icc 1 q).filter (fun r => Nat.Coprime r q)).sup' h (fun r =>
              |((Finset.range (x + 1)).filter (fun n => n % q = r % q)).sum
                  (fun n => ArithmeticFunction.vonMangoldt n)
                - (x : ℝ) / (Nat.totient q : ℝ)|)
          else 0)) := by
          apply Finset.sum_congr rfl
          intro q _
          exact hq q
    _ ≤ (x : ℝ) / (Real.log (x : ℝ)) ^ A := hx

def psiChar (q : ℕ) (x : ℕ) (χ : DirichletCharacter ℂ q) : ℂ :=
  ∑ n ∈ Finset.range (x + 1), (ArithmeticFunction.vonMangoldt n : ℂ) * χ (n : ZMod q)

def npSum (q : ℕ) (x : ℕ) : ℝ :=
  ∑ χ : DirichletCharacter ℂ q, if χ = 1 then 0 else ‖psiChar q x χ‖

def prinSum (q : ℕ) (x : ℕ) : ℝ :=
  ∑ n ∈ (Finset.range (x + 1)).filter (fun n => Nat.Coprime n q),
      ArithmeticFunction.vonMangoldt n

def prinErr (q : ℕ) (x : ℕ) : ℝ := |prinSum q x - (x : ℝ)|

lemma one_char_inv (q : ℕ) [NeZero q] (a : ℕ) (ha : a.Coprime q) :
    (1 : DirichletCharacter ℂ q) ((a : ZMod q)⁻¹) = 1 := by
  have hunit : IsUnit (a : ZMod q) := (ZMod.isUnit_iff_coprime a q).2 ha
  have hunit' : IsUnit ((a : ZMod q)⁻¹) :=
    ⟨⟨(a : ZMod q)⁻¹, (a : ZMod q), ZMod.inv_mul_of_unit (a : ZMod q) hunit,
      ZMod.mul_inv_of_unit (a : ZMod q) hunit⟩, rfl⟩
  exact MulChar.one_apply hunit'

lemma psiChar_one (q : ℕ) [NeZero q] (x : ℕ) :
    psiChar q x (1 : DirichletCharacter ℂ q) = ((prinSum q x : ℝ) : ℂ) := by
  unfold psiChar prinSum
  rw [Complex.ofReal_sum, Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro n _
  by_cases h : IsUnit (n : ZMod q)
  · have hc : Nat.Coprime n q := (ZMod.isUnit_iff_coprime n q).1 h
    rw [MulChar.one_apply h, if_pos hc]; simp
  · have hc : ¬ Nat.Coprime n q := fun hc => h ((ZMod.isUnit_iff_coprime n q).2 hc)
    rw [MulCharClass.map_nonunit (1 : DirichletCharacter ℂ q) h, if_neg hc]; simp

lemma norm_triv_sub (q : ℕ) [NeZero q] (x : ℕ) :
    ‖psiChar q x (1 : DirichletCharacter ℂ q) - ((x : ℝ) : ℂ)‖ = prinErr q x := by
  rw [psiChar_one]
  unfold prinErr
  rw [← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs]

lemma norm_npSum_le (q : ℕ) [NeZero q] (x a : ℕ) :
    ‖∑ χ : DirichletCharacter ℂ q, if χ = 1 then 0 else χ ((a : ZMod q)⁻¹) * psiChar q x χ‖
      ≤ npSum q x := by
  calc
    ‖∑ χ : DirichletCharacter ℂ q, if χ = 1 then 0 else χ ((a : ZMod q)⁻¹) * psiChar q x χ‖
        ≤ ∑ χ : DirichletCharacter ℂ q, ‖if χ = 1 then 0 else χ ((a : ZMod q)⁻¹) * psiChar q x χ‖ :=
          norm_sum_le _ _
    _ = ∑ χ : DirichletCharacter ℂ q, if χ = 1 then 0 else ‖χ ((a : ZMod q)⁻¹) * psiChar q x χ‖ := by
          apply Finset.sum_congr rfl
          intro χ _
          by_cases h : χ = 1 <;> simp [h]
    _ ≤ ∑ χ : DirichletCharacter ℂ q, if χ = 1 then 0 else ‖psiChar q x χ‖ := by
          apply Finset.sum_le_sum
          intro χ _
          by_cases h : χ = 1
          · simp [h]
          · simp only [h, if_false]
            calc ‖χ ((a : ZMod q)⁻¹) * psiChar q x χ‖
                = ‖χ ((a : ZMod q)⁻¹)‖ * ‖psiChar q x χ‖ := norm_mul _ _
              _ ≤ 1 * ‖psiChar q x χ‖ :=
                  mul_le_mul_of_nonneg_right (DirichletCharacter.norm_le_one χ ((a : ZMod q)⁻¹)) (norm_nonneg _)
              _ = ‖psiChar q x χ‖ := one_mul _
    _ = npSum q x := by
          rw [npSum]
          apply Finset.sum_congr rfl
          intro χ _
          by_cases h : χ = 1 <;> simp [h]

lemma charsum_split (q : ℕ) [NeZero q] (x a : ℕ) (ha : a.Coprime q) :
    (∑ χ : DirichletCharacter ℂ q, χ ((a : ZMod q)⁻¹) * psiChar q x χ)
      = psiChar q x (1 : DirichletCharacter ℂ q)
        + ∑ χ : DirichletCharacter ℂ q, if χ = 1 then 0 else χ ((a : ZMod q)⁻¹) * psiChar q x χ := by
  have hset : (Finset.univ.filter (fun χ : DirichletCharacter ℂ q => χ = 1))
      = {(1 : DirichletCharacter ℂ q)} := by
    ext χ; simp
  rw [← Finset.sum_filter_add_sum_filter_not (s := (Finset.univ : Finset (DirichletCharacter ℂ q)))
      (p := fun χ => χ = 1)]
  congr 1
  · rw [hset, Finset.sum_singleton, one_char_inv q a ha, one_mul]
  · rw [Finset.sum_filter]
    apply Finset.sum_congr rfl
    intro χ _
    by_cases h : χ = 1 <;> simp [h]

lemma residue_main_eq (q : ℕ) [NeZero q] (x a : ℕ) (ha : a.Coprime q) :
    (((∑ n ∈ (Finset.range (x + 1)).filter (fun n => n % q = a % q),
        ArithmeticFunction.vonMangoldt n : ℝ)) : ℂ)
        - ((x : ℝ) : ℂ) / ((Nat.totient q : ℝ) : ℂ)
      = (((Nat.totient q : ℝ) : ℂ))⁻¹ *
          ((∑ χ : DirichletCharacter ℂ q, χ ((a : ZMod q)⁻¹) * psiChar q x χ) - ((x : ℝ) : ℂ)) := by
  have h := residue_vonMangoldt_char_sum q x a ha
  have hS : (∑ n ∈ (Finset.range (x + 1)).filter (fun n => n % q = a % q),
        (ArithmeticFunction.vonMangoldt n : ℂ))
      = (((∑ n ∈ (Finset.range (x + 1)).filter (fun n => n % q = a % q),
        ArithmeticFunction.vonMangoldt n : ℝ)) : ℂ) := by
    rw [Complex.ofReal_sum]
  rw [hS] at h
  rw [h]
  unfold psiChar
  push_cast
  ring


lemma err_le_charBound (q : ℕ) [NeZero q] (x a : ℕ) (ha : a.Coprime q) :
    |(∑ n ∈ (Finset.range (x + 1)).filter (fun n => n % q = a % q),
        ArithmeticFunction.vonMangoldt n) - (x : ℝ) / (Nat.totient q : ℝ)|
      ≤ ((Nat.totient q : ℝ))⁻¹ * (npSum q x + prinErr q x) := by
  have hφpos : (0 : ℝ) < (Nat.totient q : ℝ) :=
    Nat.cast_pos.mpr ((Nat.totient_pos).2 (Nat.pos_of_neZero q))
  -- put the left side in ℂ
  have hnorm : |(∑ n ∈ (Finset.range (x + 1)).filter (fun n => n % q = a % q),
        ArithmeticFunction.vonMangoldt n) - (x : ℝ) / (Nat.totient q : ℝ)|
      = ‖(((∑ n ∈ (Finset.range (x + 1)).filter (fun n => n % q = a % q),
            ArithmeticFunction.vonMangoldt n : ℝ)) : ℂ)
          - ((x : ℝ) : ℂ) / ((Nat.totient q : ℝ) : ℂ)‖ := by
    rw [← Complex.ofReal_div, ← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs]
  rw [hnorm, residue_main_eq q x a ha]
  rw [norm_mul]
  have hnormφ : ‖((Nat.totient q : ℝ) : ℂ)⁻¹‖ = ((Nat.totient q : ℝ))⁻¹ := by
    rw [norm_inv, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hφpos]
  rw [hnormφ]
  have hW : ‖(∑ χ : DirichletCharacter ℂ q, χ ((a : ZMod q)⁻¹) * psiChar q x χ) - ((x : ℝ) : ℂ)‖
      ≤ prinErr q x + npSum q x := by
    rw [charsum_split q x a ha]
    have hsplit : psiChar q x (1 : DirichletCharacter ℂ q)
          + (∑ χ : DirichletCharacter ℂ q, if χ = 1 then 0 else χ ((a : ZMod q)⁻¹) * psiChar q x χ)
          - ((x : ℝ) : ℂ)
        = (psiChar q x (1 : DirichletCharacter ℂ q) - ((x : ℝ) : ℂ))
          + (∑ χ : DirichletCharacter ℂ q, if χ = 1 then 0 else χ ((a : ZMod q)⁻¹) * psiChar q x χ) := by
      ring
    rw [hsplit]
    calc ‖(psiChar q x (1 : DirichletCharacter ℂ q) - ((x : ℝ) : ℂ))
            + (∑ χ : DirichletCharacter ℂ q, if χ = 1 then 0 else χ ((a : ZMod q)⁻¹) * psiChar q x χ)‖
          ≤ ‖psiChar q x (1 : DirichletCharacter ℂ q) - ((x : ℝ) : ℂ)‖
            + ‖∑ χ : DirichletCharacter ℂ q, if χ = 1 then 0 else χ ((a : ZMod q)⁻¹) * psiChar q x χ‖ :=
            norm_add_le _ _
      _ = prinErr q x
            + ‖∑ χ : DirichletCharacter ℂ q, if χ = 1 then 0 else χ ((a : ZMod q)⁻¹) * psiChar q x χ‖ := by
            rw [norm_triv_sub]
      _ ≤ prinErr q x + npSum q x := add_le_add le_rfl (norm_npSum_le q x a)
  calc ((Nat.totient q : ℝ))⁻¹ *
        ‖(∑ χ : DirichletCharacter ℂ q, χ ((a : ZMod q)⁻¹) * psiChar q x χ) - ((x : ℝ) : ℂ)‖
      ≤ ((Nat.totient q : ℝ))⁻¹ * (prinErr q x + npSum q x) :=
        mul_le_mul_of_nonneg_left hW (inv_nonneg.mpr hφpos.le)
    _ = ((Nat.totient q : ℝ))⁻¹ * (npSum q x + prinErr q x) := by ring



private lemma tendsto_log_nat :
    Filter.Tendsto (fun x : ℕ => Real.log (x : ℝ)) Filter.atTop Filter.atTop :=
  Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop

/-- eventually `C * log x ^ k ≤ log x ^ (k+1)` -/
lemma eventually_const_mul_log_pow_le (C : ℝ) (hC : 0 ≤ C) (k : ℕ) :
    ∀ᶠ x : ℕ in Filter.atTop, C * (Real.log (x : ℝ)) ^ k ≤ (Real.log (x : ℝ)) ^ (k + 1) := by
  filter_upwards [tendsto_log_nat.eventually_ge_atTop (max C 1),
    Filter.eventually_ge_atTop (1 : ℕ)] with x hx hx1
  have hlog0 : 0 ≤ Real.log (x : ℝ) := Real.log_nonneg (by exact_mod_cast hx1)
  calc C * (Real.log (x : ℝ)) ^ k
      ≤ Real.log (x : ℝ) * (Real.log (x : ℝ)) ^ k :=
        mul_le_mul_of_nonneg_right (le_trans (le_max_left C 1) hx) (pow_nonneg hlog0 k)
    _ = (Real.log (x : ℝ)) ^ (k + 1) := by ring

/-- eventually `C * x^{1/2} * (log x)^k ≤ x / (log x)^A` (for `A, C > 0`). -/
lemma eventually_const_mul_sqrt_mul_log_pow_le (A C : ℝ) (hA : 0 < A) (hC : 0 < C) (k : ℕ) :
    ∀ᶠ x : ℕ in Filter.atTop,
      C * (x : ℝ) ^ (1/2 : ℝ) * (Real.log (x : ℝ)) ^ k ≤ (x : ℝ) / (Real.log (x : ℝ)) ^ A := by
  have hAk : 0 < A + (k : ℝ) := by positivity
  have hlitN : (fun N : ℕ => (Real.log (N : ℝ)) ^ (A + (k : ℝ))) =o[Filter.atTop]
      (fun N : ℕ => (N : ℝ) ^ (1/2 : ℝ)) :=
    (isLittleO_log_rpow_rpow_atTop (A + (k : ℝ)) (by norm_num : (0:ℝ) < 1/2)).comp_tendsto
      tendsto_natCast_atTop_atTop
  filter_upwards [hlitN.def (show (0:ℝ) < 1/C by positivity), Filter.eventually_ge_atTop (2 : ℕ)]
    with x hx hx2
  have hx0 : (0:ℝ) < (x : ℝ) := by exact_mod_cast (by omega : 0 < x)
  have hlog0 : 0 < Real.log (x : ℝ) := Real.log_pos (by exact_mod_cast (by omega : 1 < x))
  rw [Real.norm_of_nonneg (Real.rpow_nonneg hlog0.le _),
    Real.norm_of_nonneg (Real.rpow_nonneg hx0.le _)] at hx
  have hsplit : (Real.log (x : ℝ)) ^ (A + (k : ℝ))
      = (Real.log (x : ℝ)) ^ A * (Real.log (x : ℝ)) ^ k := by
    rw [← Real.rpow_natCast (Real.log (x : ℝ)) k, Real.rpow_add hlog0]
  rw [hsplit] at hx
  have hmul : C * (Real.log (x : ℝ)) ^ A * (Real.log (x : ℝ)) ^ k ≤ (x : ℝ) ^ (1/2 : ℝ) := by
    have h := mul_le_mul_of_nonneg_left hx hC.le
    have hc1 : C * (1/C) = 1 := by field_simp
    rw [← mul_assoc, ← mul_assoc, hc1, one_mul] at h
    exact h
  have hfinal : C * (x : ℝ) ^ (1/2 : ℝ) * (Real.log (x : ℝ)) ^ k * (Real.log (x : ℝ)) ^ A
      ≤ (x : ℝ) := by
    calc C * (x : ℝ) ^ (1/2 : ℝ) * (Real.log (x : ℝ)) ^ k * (Real.log (x : ℝ)) ^ A
        = (x : ℝ) ^ (1/2 : ℝ) * (C * (Real.log (x : ℝ)) ^ A * (Real.log (x : ℝ)) ^ k) := by ring
      _ ≤ (x : ℝ) ^ (1/2 : ℝ) * (x : ℝ) ^ (1/2 : ℝ) :=
          mul_le_mul_of_nonneg_left hmul (Real.rpow_nonneg hx0.le _)
      _ = (x : ℝ) := by rw [← Real.rpow_add hx0]; norm_num
  rw [le_div_iff₀ (Real.rpow_pos_of_pos hlog0 A)]
  exact hfinal

/-- **Principal-character part** of the Bombieri–Vinogradov error sum: for every
exponent `A > 0` and every `B > 0` the contribution
`Σ_{q ≤ √x/log^B x} (1/φ(q))·|ψ_{χ₀}(x) − x|` is eventually bounded by a constant
multiple of `x / log^A x`. -/
lemma principal_part_bound (A : ℝ) (hA : 0 < A) (B : ℝ) (hB : 0 < B) :
    ∃ C : ℝ, 0 < C ∧ ∀ᶠ x : ℕ in Filter.atTop,
      (∑ q ∈ Finset.Icc 1 ⌊Real.sqrt (x : ℝ) / (Real.log (x : ℝ)) ^ B⌋₊,
          ((Nat.totient q : ℝ))⁻¹ * prinErr q x)
        ≤ C * ((x : ℝ) / (Real.log (x : ℝ)) ^ A) := by
  obtain ⟨C1, hC1pos, hC1⟩ := Commons.NumberTheory.Totient.sum_inv_totient_Icc_le_powLog
  obtain ⟨C2, hC2pos, hC2⟩ := Commons.NumberTheory.Factorization.omega_sum_le
  refine ⟨C1 + 1, by positivity, ?_⟩
  have hψ := Commons.NumberTheory.PrimeNumberTheorem.psi_sub_id_powLog (A + 4) (by linarith)
  have habs := eventually_const_mul_sqrt_mul_log_pow_le A (4 * C2) hA (by positivity) 2
  have hlog2 := tendsto_log_nat.eventually_ge_atTop (2 : ℝ)
  have hQ4 : ∀ᶠ x : ℕ in Filter.atTop, 4 ≤ ⌊Real.sqrt (x : ℝ) / (Real.log (x : ℝ)) ^ B⌋₊ := by
    have hlitN : (fun N : ℕ => (Real.log (N : ℝ)) ^ B) =o[Filter.atTop]
        (fun N : ℕ => (N : ℝ) ^ (1/2 : ℝ)) :=
      (isLittleO_log_rpow_rpow_atTop B (by norm_num : (0:ℝ) < 1/2)).comp_tendsto
        tendsto_natCast_atTop_atTop
    filter_upwards [hlitN.def (show (0:ℝ) < 1/4 by norm_num), Filter.eventually_ge_atTop (2 : ℕ)]
      with x hx hx2
    have hx0 : 0 < (x : ℝ) := by exact_mod_cast (by omega : 0 < x)
    have hlogpos : 0 < Real.log (x : ℝ) := Real.log_pos (by exact_mod_cast (by omega : 1 < x))
    have hlogBpos : 0 < (Real.log (x : ℝ)) ^ B := Real.rpow_pos_of_pos hlogpos B
    rw [Real.norm_of_nonneg (Real.rpow_nonneg hlogpos.le B),
      Real.norm_of_nonneg (Real.rpow_nonneg hx0.le _)] at hx
    rw [show (x : ℝ) ^ (1/2:ℝ) = Real.sqrt (x : ℝ) from (Real.sqrt_eq_rpow _).symm] at hx
    refine Nat.le_floor ?_
    have h4 : 4 * (Real.log (x : ℝ)) ^ B ≤ Real.sqrt (x : ℝ) := by
      have hm := mul_le_mul_of_nonneg_left hx (show (0:ℝ) ≤ 4 by norm_num)
      nlinarith [hm]
    rw [le_div_iff₀ hlogBpos]
    exact h4
  filter_upwards [hψ, habs, hlog2, hQ4] with x hψx habsx hlog2x hQ4x
  set Q : ℕ := ⌊Real.sqrt (x : ℝ) / (Real.log (x : ℝ)) ^ B⌋₊ with hQdef
  have hQ2 : 2 ≤ Q := by omega
  have hx2 : 2 ≤ x := by
    have hpos : 0 < Real.log (x : ℝ) := by linarith
    by_contra h
    have hx1 : x ≤ 1 := by omega
    interval_cases x <;> simp at hpos
  have hx0 : (0:ℝ) < (x : ℝ) := by exact_mod_cast (by omega : 0 < x)
  have hlog1 : (1:ℝ) ≤ Real.log (x : ℝ) := by linarith
  have hlogpos : 0 < Real.log (x : ℝ) := by linarith
  have hQ1 : 1 ≤ Q := by omega
  have hQle : (Q : ℝ) ≤ Real.sqrt (x : ℝ) := by
    have hlogB1 : (1:ℝ) ≤ (Real.log (x : ℝ)) ^ B := Real.one_le_rpow hlog1 hB.le
    have h := Nat.floor_le (show (0:ℝ) ≤ Real.sqrt (x : ℝ) / (Real.log (x : ℝ)) ^ B by positivity)
    rw [hQdef]
    calc (⌊Real.sqrt (x : ℝ) / (Real.log (x : ℝ)) ^ B⌋₊ : ℝ)
        ≤ Real.sqrt (x : ℝ) / (Real.log (x : ℝ)) ^ B := h
      _ ≤ Real.sqrt (x : ℝ) / 1 :=
          div_le_div_of_nonneg_left (Real.sqrt_nonneg _) (by norm_num) hlogB1
      _ = Real.sqrt (x : ℝ) := by ring
  have hlogQ : Real.log (Q : ℝ) ≤ Real.log (x : ℝ) := by
    apply Real.log_le_log (Nat.cast_pos.mpr (by omega : 0 < Q))
    have hsqrtx : Real.sqrt (x : ℝ) ≤ (x : ℝ) := by
      rw [Real.sqrt_le_iff]
      refine ⟨hx0.le, ?_⟩
      have h1 : (1:ℝ) ≤ (x : ℝ) := by exact_mod_cast (by omega : 1 ≤ x)
      nlinarith [mul_nonneg hx0.le (sub_nonneg.mpr h1)]
    linarith [hQle, hsqrtx]
  -- per-`q` bound: the coprime part of `ψ` is `ψ` up to `ω(q)·log x`
  have hper : ∀ q ∈ Finset.Icc 1 Q,
      ((Nat.totient q : ℝ))⁻¹ * prinErr q x
        ≤ ((Nat.totient q : ℝ))⁻¹ *
            |(∑ n ∈ Finset.range (x + 1), ArithmeticFunction.vonMangoldt n) - (x : ℝ)|
          + (q.primeFactors.card : ℝ) * Real.log ((x : ℝ) + 2) := by
    intro q hq
    have hq1 : 1 ≤ q := (Finset.mem_Icc.mp hq).1
    haveI : NeZero q := ⟨by omega⟩
    have hψe : prinErr q x
        ≤ |(∑ n ∈ Finset.range (x + 1), ArithmeticFunction.vonMangoldt n) - (x : ℝ)|
          + (q.primeFactors.card : ℝ) * Real.log ((x : ℝ) + 2) :=
      Commons.NumberTheory.BombieriVinogradov.psi_coprime_sub_id_le q x
    have hφinv_nn : 0 ≤ ((Nat.totient q : ℝ))⁻¹ := inv_nonneg.mpr (Nat.cast_nonneg _)
    have hφ1 : ((Nat.totient q : ℝ))⁻¹ ≤ 1 := by
      rw [inv_le_one₀ (Nat.cast_pos.mpr ((Nat.totient_pos).2 (by omega : 0 < q)))]
      exact_mod_cast Nat.succ_le_of_lt ((Nat.totient_pos).2 (by omega : 0 < q))
    have hωnn : 0 ≤ (q.primeFactors.card : ℝ) * Real.log ((x : ℝ) + 2) :=
      mul_nonneg (Nat.cast_nonneg _) (Real.log_nonneg (by linarith))
    calc ((Nat.totient q : ℝ))⁻¹ * prinErr q x
        ≤ ((Nat.totient q : ℝ))⁻¹ *
            (|(∑ n ∈ Finset.range (x + 1), ArithmeticFunction.vonMangoldt n) - (x : ℝ)|
              + (q.primeFactors.card : ℝ) * Real.log ((x : ℝ) + 2)) :=
          mul_le_mul_of_nonneg_left hψe hφinv_nn
      _ = ((Nat.totient q : ℝ))⁻¹ *
            |(∑ n ∈ Finset.range (x + 1), ArithmeticFunction.vonMangoldt n) - (x : ℝ)|
          + ((Nat.totient q : ℝ))⁻¹ * ((q.primeFactors.card : ℝ) * Real.log ((x : ℝ) + 2)) := by
          ring
      _ ≤ ((Nat.totient q : ℝ))⁻¹ *
            |(∑ n ∈ Finset.range (x + 1), ArithmeticFunction.vonMangoldt n) - (x : ℝ)|
          + (q.primeFactors.card : ℝ) * Real.log ((x : ℝ) + 2) := by
          have := mul_le_mul_of_nonneg_right hφ1 hωnn
          linarith
  have hsum1 : (∑ q ∈ Finset.Icc 1 Q, ((Nat.totient q : ℝ))⁻¹)
      ≤ C1 * (Real.log (x : ℝ)) ^ 2 := by
    refine le_trans (hC1 Q hQ2) ?_
    apply mul_le_mul_of_nonneg_left _ hC1pos.le
    exact pow_le_pow_left₀ (Real.log_nonneg (by exact_mod_cast hQ1)) hlogQ 2
  have hsum2 : (∑ q ∈ Finset.Icc 1 Q, (q.primeFactors.card : ℝ))
      ≤ C2 * (Q : ℝ) * (Real.log (x : ℝ) + 1) := by
    have hraw : (∑ q ∈ Finset.Icc 1 Q, (q.primeFactors.card : ℝ))
        ≤ C2 * (Q : ℝ) * (Real.log (Q : ℝ) + 1) := by
      have h := hC2 Q hQ2
      convert h using 1
      apply Finset.sum_congr rfl
      intro q _
      rw [Nat.support_factorization]
    refine le_trans hraw ?_
    calc C2 * (Q : ℝ) * (Real.log (Q : ℝ) + 1)
        = C2 * ((Q : ℝ) * (Real.log (Q : ℝ) + 1)) := by ring
      _ ≤ C2 * ((Q : ℝ) * (Real.log (x : ℝ) + 1)) := by
          apply mul_le_mul_of_nonneg_left _ hC2pos.le
          exact mul_le_mul_of_nonneg_left (by linarith [hlogQ]) (Nat.cast_nonneg Q)
      _ = C2 * (Q : ℝ) * (Real.log (x : ℝ) + 1) := by ring
  have hstep : (∑ q ∈ Finset.Icc 1 Q, ((Nat.totient q : ℝ))⁻¹ * prinErr q x)
      ≤ |(∑ n ∈ Finset.range (x + 1), ArithmeticFunction.vonMangoldt n) - (x : ℝ)|
          * (C1 * (Real.log (x : ℝ)) ^ 2)
        + Real.log ((x : ℝ) + 2) * (C2 * (Q : ℝ) * (Real.log (x : ℝ) + 1)) := by
    have hψerr_nn : 0 ≤ |(∑ n ∈ Finset.range (x + 1), ArithmeticFunction.vonMangoldt n) - (x : ℝ)| :=
      abs_nonneg _
    have hlogx2_nn : 0 ≤ Real.log ((x : ℝ) + 2) := Real.log_nonneg (by linarith)
    calc (∑ q ∈ Finset.Icc 1 Q, ((Nat.totient q : ℝ))⁻¹ * prinErr q x)
        ≤ ∑ q ∈ Finset.Icc 1 Q,
            (((Nat.totient q : ℝ))⁻¹ *
                |(∑ n ∈ Finset.range (x + 1), ArithmeticFunction.vonMangoldt n) - (x : ℝ)|
              + (q.primeFactors.card : ℝ) * Real.log ((x : ℝ) + 2)) :=
          Finset.sum_le_sum hper
      _ = |(∑ n ∈ Finset.range (x + 1), ArithmeticFunction.vonMangoldt n) - (x : ℝ)|
            * (∑ q ∈ Finset.Icc 1 Q, ((Nat.totient q : ℝ))⁻¹)
          + Real.log ((x : ℝ) + 2) * (∑ q ∈ Finset.Icc 1 Q, (q.primeFactors.card : ℝ)) := by
          rw [Finset.sum_add_distrib]
          congr 1
          · rw [Finset.mul_sum]
            apply Finset.sum_congr rfl
            intro q _
            ring
          · rw [Finset.mul_sum]
            apply Finset.sum_congr rfl
            intro q _
            ring
      _ ≤ |(∑ n ∈ Finset.range (x + 1), ArithmeticFunction.vonMangoldt n) - (x : ℝ)|
            * (C1 * (Real.log (x : ℝ)) ^ 2)
          + Real.log ((x : ℝ) + 2) * (C2 * (Q : ℝ) * (Real.log (x : ℝ) + 1)) := by
          exact add_le_add (mul_le_mul_of_nonneg_left hsum1 hψerr_nn)
            (mul_le_mul_of_nonneg_left hsum2 hlogx2_nn)
  have hlogx2le : Real.log ((x : ℝ) + 2) ≤ 2 * Real.log (x : ℝ) := by
    have hx2r : (2:ℝ) ≤ (x : ℝ) := by exact_mod_cast hx2
    have h2 : Real.log (2 * (x : ℝ)) = Real.log 2 + Real.log (x : ℝ) :=
      Real.log_mul (by norm_num) hx0.ne'
    have h1 : Real.log ((x : ℝ) + 2) ≤ Real.log (2 * (x : ℝ)) :=
      Real.log_le_log (by positivity) (by linarith)
    have h3 : Real.log 2 ≤ Real.log (x : ℝ) :=
      Real.log_le_log (by norm_num) hx2r
    linarith [h1, h2, h3]
  have hA1 : |(∑ n ∈ Finset.range (x + 1), ArithmeticFunction.vonMangoldt n) - (x : ℝ)|
        * (C1 * (Real.log (x : ℝ)) ^ 2) ≤ C1 * ((x : ℝ) / (Real.log (x : ℝ)) ^ A) := by
    have h1 : |(∑ n ∈ Finset.range (x + 1), ArithmeticFunction.vonMangoldt n) - (x : ℝ)|
          * (C1 * (Real.log (x : ℝ)) ^ 2)
        ≤ ((x : ℝ) / (Real.log (x : ℝ)) ^ (A + 4)) * (C1 * (Real.log (x : ℝ)) ^ 2) :=
      mul_le_mul_of_nonneg_right hψx (by positivity)
    refine le_trans h1 ?_
    have heq : ((x : ℝ) / (Real.log (x : ℝ)) ^ (A + 4)) * (C1 * (Real.log (x : ℝ)) ^ 2)
        = C1 * ((x : ℝ) / (Real.log (x : ℝ)) ^ (A + 2)) := by
      rw [div_mul_eq_mul_div, ← Real.rpow_natCast (Real.log (x : ℝ)) 2]
      have hsplit : (Real.log (x : ℝ)) ^ (A + 4)
          = (Real.log (x : ℝ)) ^ (A + 2) * (Real.log (x : ℝ)) ^ (2:ℝ) := by
        rw [show A + 4 = (A + 2) + 2 by ring, Real.rpow_add hlogpos]
      rw [hsplit]
      field_simp
      ring
    rw [heq]
    apply mul_le_mul_of_nonneg_left _ hC1pos.le
    exact div_le_div_of_nonneg_left hx0.le (Real.rpow_pos_of_pos hlogpos A)
      (Real.rpow_le_rpow_of_exponent_le hlog1 (by linarith))
  have hB1 : Real.log ((x : ℝ) + 2) * (C2 * (Q : ℝ) * (Real.log (x : ℝ) + 1))
      ≤ 4 * C2 * (Real.sqrt (x : ℝ) * (Real.log (x : ℝ)) ^ 2) := by
    have hx1log : Real.log (x : ℝ) + 1 ≤ 2 * Real.log (x : ℝ) := by linarith
    have hC2nn : 0 ≤ C2 := hC2pos.le
    have hsxnn : 0 ≤ Real.sqrt (x : ℝ) := Real.sqrt_nonneg _
    have hQnn : 0 ≤ (Q : ℝ) := Nat.cast_nonneg Q
    have hlogxnn : 0 ≤ Real.log (x : ℝ) := hlogpos.le
    calc Real.log ((x : ℝ) + 2) * (C2 * (Q : ℝ) * (Real.log (x : ℝ) + 1))
        ≤ (2 * Real.log (x : ℝ)) * (C2 * Real.sqrt (x : ℝ) * (2 * Real.log (x : ℝ))) := by
          apply mul_le_mul
          · exact hlogx2le
          · exact mul_le_mul (mul_le_mul_of_nonneg_left hQle hC2nn) hx1log (by linarith) (by positivity)
          · exact mul_nonneg (mul_nonneg hC2nn hQnn) (by linarith)
          · positivity
      _ = 4 * C2 * (Real.sqrt (x : ℝ) * (Real.log (x : ℝ)) ^ 2) := by ring
  have hB2 : 4 * C2 * (Real.sqrt (x : ℝ) * (Real.log (x : ℝ)) ^ 2)
      ≤ (x : ℝ) / (Real.log (x : ℝ)) ^ A := by
    have h := habsx
    rw [show (x : ℝ) ^ (1/2:ℝ) = Real.sqrt (x : ℝ) from (Real.sqrt_eq_rpow _).symm] at h
    linarith [h]
  have hr : C1 * ((x : ℝ) / (Real.log (x : ℝ)) ^ A) + (x : ℝ) / (Real.log (x : ℝ)) ^ A
      = (C1 + 1) * ((x : ℝ) / (Real.log (x : ℝ)) ^ A) := by ring
  linarith [hstep, hA1, hB1, hB2, hr]

/-- **Maximum over coprime residues, bounded by the character average.** -/
lemma maxTerm_le_charBound (q : ℕ) [NeZero q] (x : ℕ) :
    maxTerm x q ≤ ((Nat.totient q : ℝ))⁻¹ * (npSum q x + prinErr q x) := by
  unfold maxTerm
  by_cases h : ((Finset.Icc 1 q).filter (fun r => Nat.Coprime r q)).Nonempty
  · rw [dif_pos h]
    refine Finset.sup'_le h (fun r => err x q r) ?_
    intro r hr
    exact err_le_charBound q x r (Finset.mem_filter.mp hr).2
  · rw [dif_neg h]
    have hnp : 0 ≤ npSum q x :=
      Finset.sum_nonneg (fun χ _ => by by_cases hχ : χ = 1 <;> simp [hχ])
    exact mul_nonneg (inv_nonneg.mpr (Nat.cast_nonneg _)) (add_nonneg hnp (abs_nonneg _))

/-- **Assembly of the family theorem from the character-sum engine.**  The engine
is the analytic Bombieri–Vinogradov bound for the average over moduli of the
nonprincipal character sums `Σ_{χ ≠ χ₀} ‖ψ(x,χ)‖` (the remaining input, to be
published by the fleet as `bombieri_vinogradov_characterSum`); everything else
is proved in this module. -/
theorem family_of_engine
    (hEngine : ∀ A : ℝ, 0 < A → ∃ B : ℝ, 0 < B ∧ ∀ᶠ x : ℕ in Filter.atTop,
      (∑ q ∈ Finset.Icc 1 ⌊Real.sqrt (x : ℝ) / (Real.log (x : ℝ)) ^ B⌋₊,
          ((Nat.totient q : ℝ))⁻¹ * npSum q x) ≤ (x : ℝ) / (Real.log (x : ℝ)) ^ A) :
    ∀ A : ℝ, 0 < A →
    ∃ B : ℝ, 0 < B ∧
    ∀ a : ℕ → ℕ, (∀ q : ℕ, Nat.Coprime (a q) q) →
    ∀ᶠ x : ℕ in Filter.atTop,
      ((Finset.Icc 2 ⌊Real.sqrt (x : ℝ) / (Real.log (x : ℝ)) ^ B⌋₊).sum fun q =>
        |((Finset.range (x + 1)).filter (fun n => n % q = (a q) % q)).sum
            (fun n => ArithmeticFunction.vonMangoldt n)
          - (x : ℝ) / (Nat.totient q : ℝ)|)
      ≤ (x : ℝ) / (Real.log (x : ℝ)) ^ A := by
  intro A hA
  have hA1 : 0 < A + 1 := by linarith
  rcases hEngine (A + 1) hA1 with ⟨B, hB, hEngB⟩
  obtain ⟨Cp, hCppos, hPrin⟩ := principal_part_bound (A + 1) hA1 B hB
  refine ⟨B, hB, ?_⟩
  intro a hcop
  filter_upwards [hEngB, hPrin, tendsto_log_nat.eventually_ge_atTop (1 + Cp)] with x hEngx hPrinx hlogCp
  set Q : ℕ := ⌊Real.sqrt (x : ℝ) / (Real.log (x : ℝ)) ^ B⌋₊ with hQdef
  -- family LHS = Σ_{q ∈ Icc 2 Q} err
  have hfam : ((Finset.Icc 2 Q).sum fun q =>
        |((Finset.range (x + 1)).filter (fun n => n % q = (a q) % q)).sum
            (fun n => ArithmeticFunction.vonMangoldt n)
          - (x : ℝ) / (Nat.totient q : ℝ)|)
      = ∑ q ∈ Finset.Icc 2 Q, err x q (a q) := by
    apply Finset.sum_congr rfl
    intro q _
    rfl
  rw [hfam]
  have hstep1 : (∑ q ∈ Finset.Icc 2 Q, err x q (a q))
      ≤ ∑ q ∈ Finset.Icc 1 Q, maxTerm x q := family_le_maxsum x Q a hcop
  have hstep2 : (∑ q ∈ Finset.Icc 1 Q, maxTerm x q)
      ≤ ∑ q ∈ Finset.Icc 1 Q, ((Nat.totient q : ℝ))⁻¹ * (npSum q x + prinErr q x) := by
    apply Finset.sum_le_sum
    intro q hq
    have hq1 : 1 ≤ q := (Finset.mem_Icc.mp hq).1
    haveI : NeZero q := ⟨by omega⟩
    exact maxTerm_le_charBound q x
  have hstep3 : (∑ q ∈ Finset.Icc 1 Q, ((Nat.totient q : ℝ))⁻¹ * (npSum q x + prinErr q x))
      = (∑ q ∈ Finset.Icc 1 Q, ((Nat.totient q : ℝ))⁻¹ * npSum q x)
        + (∑ q ∈ Finset.Icc 1 Q, ((Nat.totient q : ℝ))⁻¹ * prinErr q x) := by
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro q _
    ring
  have hstep4 : (∑ q ∈ Finset.Icc 1 Q, ((Nat.totient q : ℝ))⁻¹ * npSum q x)
        + (∑ q ∈ Finset.Icc 1 Q, ((Nat.totient q : ℝ))⁻¹ * prinErr q x)
      ≤ (x : ℝ) / (Real.log (x : ℝ)) ^ (A + 1) + Cp * ((x : ℝ) / (Real.log (x : ℝ)) ^ (A + 1)) :=
    add_le_add hEngx hPrinx
  have hstep5 : (x : ℝ) / (Real.log (x : ℝ)) ^ (A + 1)
        + Cp * ((x : ℝ) / (Real.log (x : ℝ)) ^ (A + 1))
      ≤ (Real.log (x : ℝ)) * ((x : ℝ) / (Real.log (x : ℝ)) ^ (A + 1)) := by
    have hlogposx : 0 < Real.log (x : ℝ) := by linarith [hlogCp, hCppos]
    have hr : 0 ≤ (x : ℝ) / (Real.log (x : ℝ)) ^ (A + 1) :=
      div_nonneg (Nat.cast_nonneg x) (Real.rpow_nonneg hlogposx.le _)
    have h1 : (1 : ℝ) + Cp ≤ Real.log (x : ℝ) := hlogCp
    nlinarith [h1, hr]
  have hstep6 : (Real.log (x : ℝ)) * ((x : ℝ) / (Real.log (x : ℝ)) ^ (A + 1))
      = (x : ℝ) / (Real.log (x : ℝ)) ^ A := by
    have hlogposx : 0 < Real.log (x : ℝ) := by linarith [hlogCp, hCppos]
    rw [mul_div_assoc', Real.rpow_add hlogposx, Real.rpow_one]
    field_simp
  calc (∑ q ∈ Finset.Icc 2 Q, err x q (a q))
      ≤ ∑ q ∈ Finset.Icc 1 Q, maxTerm x q := hstep1
    _ ≤ ∑ q ∈ Finset.Icc 1 Q, ((Nat.totient q : ℝ))⁻¹ * (npSum q x + prinErr q x) := hstep2
    _ = (∑ q ∈ Finset.Icc 1 Q, ((Nat.totient q : ℝ))⁻¹ * npSum q x)
        + (∑ q ∈ Finset.Icc 1 Q, ((Nat.totient q : ℝ))⁻¹ * prinErr q x) := hstep3
    _ ≤ (x : ℝ) / (Real.log (x : ℝ)) ^ (A + 1) + Cp * ((x : ℝ) / (Real.log (x : ℝ)) ^ (A + 1)) :=
        hstep4
    _ ≤ (Real.log (x : ℝ)) * ((x : ℝ) / (Real.log (x : ℝ)) ^ (A + 1)) := hstep5
    _ = (x : ℝ) / (Real.log (x : ℝ)) ^ A := hstep6


/-- `npSum` is the difference between the total character sum and the trivial
character term (the form in which the engine is stated). -/
lemma npSum_eq (q x : ℕ) :
    npSum q x = (∑ χ : DirichletCharacter ℂ q, ‖psiChar q x χ‖)
      - ‖psiChar q x (1 : DirichletCharacter ℂ q)‖ := by
  have h1 : npSum q x
      = ∑ χ ∈ (Finset.univ.filter (fun χ : DirichletCharacter ℂ q => χ ≠ 1)),
          ‖psiChar q x χ‖ := by
    rw [npSum, Finset.sum_filter]
    apply Finset.sum_congr rfl
    intro χ _
    by_cases h : χ = 1 <;> simp [h]
  rw [h1]
  rw [← Finset.sum_filter_add_sum_filter_not (s := (Finset.univ : Finset (DirichletCharacter ℂ q)))
      (p := fun χ => χ = 1) (f := fun χ => ‖psiChar q x χ‖)]
  have hset : (Finset.univ.filter (fun χ : DirichletCharacter ℂ q => χ = 1))
      = {(1 : DirichletCharacter ℂ q)} := by
    ext χ; simp
  rw [hset, Finset.sum_singleton, add_sub_cancel_left]


/-- **Final assembly.**  Target theorem from the engine stated in its published
form (`Σ_χ ‖ψ(x,χ)‖ − ‖ψ(x,χ₀)‖`). -/
theorem family_of_charSum
    (h : ∀ A : ℝ, 0 < A → ∃ B : ℝ, 0 < B ∧ ∀ᶠ x : ℕ in Filter.atTop,
      (∑ q ∈ Finset.Icc 1 ⌊Real.sqrt (x : ℝ) / (Real.log (x : ℝ)) ^ B⌋₊,
        (Nat.totient q : ℝ)⁻¹ *
          ((∑ χ : DirichletCharacter ℂ q, ‖psiChar q x χ‖)
            - ‖psiChar q x (1 : DirichletCharacter ℂ q)‖))
      ≤ (x : ℝ) / (Real.log (x : ℝ)) ^ A) :
    ∀ A : ℝ, 0 < A →
    ∃ B : ℝ, 0 < B ∧
    ∀ a : ℕ → ℕ, (∀ q : ℕ, Nat.Coprime (a q) q) →
    ∀ᶠ x : ℕ in Filter.atTop,
      ((Finset.Icc 2 ⌊Real.sqrt (x : ℝ) / (Real.log (x : ℝ)) ^ B⌋₊).sum fun q =>
        |((Finset.range (x + 1)).filter (fun n => n % q = (a q) % q)).sum
            (fun n => ArithmeticFunction.vonMangoldt n)
          - (x : ℝ) / (Nat.totient q : ℝ)|)
      ≤ (x : ℝ) / (Real.log (x : ℝ)) ^ A := by
  refine family_of_engine ?_
  intro A hA
  obtain ⟨B, hB, hb⟩ := h A hA
  refine ⟨B, hB, ?_⟩
  refine hb.mono ?_
  intro x hx
  have hx' : (∑ q ∈ Finset.Icc 1 ⌊Real.sqrt (x : ℝ) / (Real.log (x : ℝ)) ^ B⌋₊,
        (Nat.totient q : ℝ)⁻¹ * npSum q x) ≤ (x : ℝ) / (Real.log (x : ℝ)) ^ A := by
    simpa only [npSum_eq] using hx
  exact hx'


end FamilyAux

/-- **Bombieri–Vinogradov theorem, single-residue family form.**
(Statement fixed; the analytic core of the proof is supplied by the fleet's
Bombieri–Vinogradov / Dirichlet-`L`-function engine; see module docstring.) -/
theorem bombieri_vinogradov_family :
    ∀ A : ℝ, 0 < A →
    ∃ B : ℝ, 0 < B ∧
    ∀ a : ℕ → ℕ, (∀ q : ℕ, Nat.Coprime (a q) q) →
    ∀ᶠ x : ℕ in Filter.atTop,
      ((Finset.Icc 2 ⌊Real.sqrt (x : ℝ) / (Real.log (x : ℝ)) ^ B⌋₊).sum fun q =>
        |((Finset.range (x + 1)).filter (fun n => n % q = (a q) % q)).sum
            (fun n => ArithmeticFunction.vonMangoldt n)
          - (x : ℝ) / (Nat.totient q : ℝ)|)
      ≤ (x : ℝ) / (Real.log (x : ℝ)) ^ A :=
  FamilyAux.family_of_charSum (by
    intro A hA
    obtain ⟨B, hB, hb⟩ :=
      Commons.NumberTheory.BombieriVinogradov.bombieri_vinogradov_characterSum A hA
    refine ⟨B, hB, ?_⟩
    simpa only [FamilyAux.psiChar] using hb)

end Commons.NumberTheory.BombieriVinogradov
