/-
# `Work.FIArea7.Classical172Defs` — the classical inputs of *FI* §§21–26

*FI* Proposition 17.2 (`Work.FIArea7.Prop172_6`, the single remaining input of area 7) is proved in
the paper by the following chain of *elementary* analytic estimates — no `L`-function technology:

* §19–§20: the Dirichlet symbol `ξ_w(z) = (z/w)` (19.10) and the Jacobi–Kubota symbol
  `[z] = i^{(r-1)/2}(s/|r|)` (20.1), with the multiplier rule (20.3)/(20.4) and the separation
  (20.15)+(20.19) of its `ε`-factor;
* §21: Lemma 21.1 (evaluation of `Σ_{ζ (mod q)} (ζ/w₁)(ζ/w₂)`), the Cauchy–Schwarz bound (21.8),
  its Hölder refinement (21.9), the reciprocity symmetrisation, giving **Proposition 21.3**
  (21.10) for the bilinear form `Q(M,N)` in the Dirichlet symbol, and then **Proposition 21.4**
  (21.13) for `K(M,N)` in the Jacobi–Kubota symbol;
* §22: **Proposition 22.1** (22.3)–(22.4), the special *linear* forms `K(N)`, `K∗(N)`
  (proved in this workspace: `Work.FIArea7.KSum_bound`, `Work.FIArea7.KStar_bound`);
* §23: **Proposition 23.1** (23.8), the bilinear form `L(M,N)`, `L∗(M,N)` in the quadratic
  eigenvalues (23.1), and **Proposition 23.2** (23.11)–(23.12), the special linear forms `L(N)`,
  `L∗(N)`;
* §24: Proposition 24.2 (24.13), the combinatorial identity (proved in this workspace:
  `Work.FIArea7.SepDiv`);
* §25: the reduction of (17.18) to Props. 23.1–23.2 and **Theorem 2ψ**;
* §26: Theorem 2ψ (26.2), from Vaughan's identity (26.3), Props. 23.1–23.2 and Lemma 26.1
  (proved in this workspace: `Work.FIArea7.exists_separating_function`).

This file fixes the **statements** of the five inputs that the reduction consumes — Props. 21.3,
21.4, 23.1, 23.2 and Theorem 2ψ — as `Prop`s, so that the reductions and the final assembly can be
written against them while they are being proved.  The objects are the workspace's own
(`Work.FIPlan.gBox`, `Work.FIPlan.gnorm`, `Work.FIPlan.IsPrimary`, `Work.FIArea7.JKSym`,
`Work.FIArea7.DirichletSym`, `Work.FIArea7.grossenChar`).

**The one deliberate weakening.**  `(MN)^ε` is replaced by a fixed power of `log(MN+2)`: every
occurrence of `(MN)^ε` in §§21–26 comes from a divisor-sum `Σ τ(·) ≪ (MN)^ε`, and the final
exponent arithmetic only needs *some* polylogarithmic loss.  This is the same convention as the
already-proved `KSum_bound`.

**No local coefficient is allowed inside the eigenvalue (23.1).**  The paper's §§23–26 estimates are
bounds for linear/bilinear forms in the Jacobi–Kubota symbol with *arbitrary bounded* coefficients,
but a factor `b_z` attached to `z` *inside* `λ_b(n) = Σ^∧_{zz̄=n} b_z ψ(z)[z]` is **not** such a
coefficient: in `λ_b(cmn) = Σ_{eē=c}Σ_{ww̄=m}Σ_{zz̄=n} b_{ewz}ψ(e)ψ(w)ψ(z)[ewz]` it couples the
three summation variables and cannot be absorbed into `α_w β_z`.  Concretely, with `m = 1`,
`χ ≡ 1`, `k = 0` and `b z = conj([z])` one gets `λ_b(n) = #{primary primitive z : |z|² = n}` and
hence `L(N) = Σ_{n≤N} λ_b(n) ≫ N`, against the claimed `N^{3/4}log`.  So the statements below are
paper-faithful, with **no** such coefficient (see `NOTES.md` §60).

The `n` inserted into `quadEigen`'s box is the norm `n` itself: every `z` with `|z|² = n` satisfies
`|Re z|, |Im z| ≤ n` for `n ≥ 1` (`mem_gBox_of_gnorm_eq`), so the box `gBox n` sees all of them.
-/
import Mathlib
import Submission.Work.FIArea7.Prop172

set_option autoImplicit false

namespace Work.FIArea7

open Finset
open scoped BigOperators

attribute [local instance] Classical.propDecidable

noncomputable section

/-! ## 1. The quadratic eigenvalue (23.1) -/

/-- **(23.1)**: the quadratic eigenvalue `λ(n) = Σ^∧_{zz̄=n} ψ(z)[z]`, where `∧` restricts to
primary `z`, `ψ` is the Grössencharacter (17.17) and `[·]` is the Jacobi–Kubota symbol
(`Work.FIArea7.JKSym`).  The box is `gBox n`, which contains every `z` with `|z|² = n`
(`mem_gBox_of_gnorm_eq`). -/
def quadEigen (psi : GaussianInt → ℂ) (n : ℕ) : ℂ :=
  ∑ z ∈ Work.FIPlan.gBox (n : ℤ),
    (if Work.FIPlan.gnorm z = n ∧ Work.FIPlan.IsPrimary z then psi z * JKSym z else 0)

/-- If `a² ≤ n` (as integers) then `|a| ≤ n`: for `a ≥ 1` one has `|a| ≤ a²`, for `a = 0`
trivially. -/
lemma natAbs_le_of_sq_le {a : ℤ} {n : ℕ} (h : a ^ 2 ≤ (n : ℤ)) : a.natAbs ≤ n := by
  have h4 : ((a.natAbs : ℤ)) ^ 2 ≤ (n : ℤ) := by rw [Int.natAbs_sq]; exact h
  have h5 : a.natAbs ^ 2 ≤ n := by exact_mod_cast h4
  have h6 : a.natAbs ≤ a.natAbs ^ 2 := Nat.le_self_pow (by norm_num) a.natAbs
  omega

/-- A Gaussian integer whose norm is `n` lies in the box `gBox n`. -/
lemma mem_gBox_of_gnorm_eq {z : GaussianInt} {n : ℕ}
    (hn : Work.FIPlan.gnorm z = n) : z ∈ Work.FIPlan.gBox (n : ℤ) := by
  have h2 : (n : ℤ) = z.re ^ 2 + z.im ^ 2 := by
    rw [← Work.FIArea7.norm_eq z, hn]
  have hre : z.re.natAbs ≤ n := by
    refine natAbs_le_of_sq_le (a := z.re) (n := n) ?_
    nlinarith [sq_nonneg z.im]
  have him : z.im.natAbs ≤ n := by
    refine natAbs_le_of_sq_le (a := z.im) (n := n) ?_
    nlinarith [sq_nonneg z.re]
  refine Finset.mem_image.mpr ⟨(z.re, z.im), ?_, rfl⟩
  refine Finset.mem_product.mpr ⟨Finset.mem_Icc.mpr ⟨?_, ?_⟩, Finset.mem_Icc.mpr ⟨?_, ?_⟩⟩ <;> omega

/-- `quadEigen` is a sum over the exact level set `{z : |z|² = n}` of primary `z`. -/
lemma quadEigen_eq_sum (psi : GaussianInt → ℂ) (n : ℕ) :
    quadEigen psi n
      = ∑ z ∈ (Work.FIPlan.gBox (n : ℤ)).filter
          (fun z => Work.FIPlan.gnorm z = n ∧ Work.FIPlan.IsPrimary z),
          psi z * JKSym z := by
  rw [quadEigen, Finset.sum_filter]

/-! ## 2. The bilinear forms of §§21 and 23 -/

/-- **(21.1)**: `Q(M,N) = Σ^*_w α_w Σ_z β_z (z/w)` — the bilinear form in the Dirichlet symbol
`ξ_w(z) = (z/w)` (19.10).  The sums run over boxes `gBox Rw`, `gBox Rz`; the disc restrictions
`|w|² ≤ M`, `|z|² ≤ N` are hypotheses on the supports of `α`, `β`, so the values of `Rw`, `Rz`
are immaterial. -/
def QBilin (Rw Rz : ℤ) (α β : GaussianInt → ℂ) : ℂ :=
  ∑ w ∈ Work.FIPlan.gBox Rw, ∑ z ∈ Work.FIPlan.gBox Rz,
    α w * β z * ((DirichletSym w z : ℤ) : ℂ)

/-- **(21.11)**: `K(M,N) = Σ_w Σ_z α_w β_z [wz]` — the bilinear form in the Jacobi–Kubota
symbol. -/
def KBilin (Rw Rz : ℤ) (α β : GaussianInt → ℂ) : ℂ :=
  ∑ w ∈ Work.FIPlan.gBox Rw, ∑ z ∈ Work.FIPlan.gBox Rz, α w * β z * JKSym (w * z)

/-- **(23.4)**: `L(M,N) = Σ_{m ≤ M} Σ_{n ≤ N} α(m)β(n)λ(cmn)`. -/
def LBilin (M N c : ℕ) (psi : GaussianInt → ℂ) (α β : ℕ → ℂ) : ℂ :=
  ∑ m ∈ Finset.Icc 1 M, ∑ n ∈ Finset.Icc 1 N, α m * β n * quadEigen psi (c * m * n)

/-- **(23.7)**: `L∗(M,N)`, the restricted bilinear form `(m,n) = 1`. -/
def LBilinStar (M N c : ℕ) (psi : GaussianInt → ℂ) (α β : ℕ → ℂ) : ℂ :=
  ∑ m ∈ Finset.Icc 1 M, ∑ n ∈ Finset.Icc 1 N,
    (if Nat.Coprime m n then α m * β n * quadEigen psi (c * m * n) else 0)

/-- **(23.9)**: `L(N) = Σ_{n ≤ N} λ(mn)`. -/
def LLinear (m N : ℕ) (psi : GaussianInt → ℂ) : ℂ :=
  ∑ n ∈ Finset.Icc 1 N, quadEigen psi (m * n)

/-- **(23.10)**: `L∗(N) = Σ_{n ≤ N, (n,m)=1} λ(mn)`. -/
def LStarLinear (m N : ℕ) (psi : GaussianInt → ℂ) : ℂ :=
  ∑ n ∈ Finset.Icc 1 N, (if Nat.Coprime n m then quadEigen psi (m * n) else 0)

/-! ## 3. The five inputs -/

/-- **FI Proposition 21.3, (21.10).**  For bounded coefficients `α` on primary primitive `w` of
norm `≤ M` and `β` on arbitrary `z` of norm `≤ N`,

  `‖Q(M,N)‖ ≤ C·(M + N)^{1/12}·(M N)^{11/12}·(log(MN+2))^A`.

The paper's exponent `(MN)^{11/12+ε}` is replaced by the log-loss of this file's header. -/
def Prop213 : Prop :=
  ∃ C A : ℝ, 0 < C ∧ 0 < A ∧
    ∀ (M N : ℝ) (Rw Rz : ℤ) (α β : GaussianInt → ℂ),
      1 ≤ M → 1 ≤ N →
      (∀ w, ‖α w‖ ≤ 1) → (∀ z, ‖β z‖ ≤ 1) →
      (∀ w, α w ≠ 0 → Work.FIPlan.IsPrimary w ∧ IsCoprime w.re w.im ∧
        (Work.FIPlan.gnorm w : ℝ) ≤ M) →
      (∀ z, β z ≠ 0 → (Work.FIPlan.gnorm z : ℝ) ≤ N) →
      ‖QBilin Rw Rz α β‖
        ≤ C * (M + N) ^ ((1 : ℝ) / 12) * (M * N) ^ ((11 : ℝ) / 12)
            * (Real.log (M * N + 2)) ^ A

/-- **FI Proposition 21.4, (21.13).**  The same bound for the bilinear form `K(M,N)` in the
Jacobi–Kubota symbol, with both `w` and `z` primary. -/
def Prop214 : Prop :=
  ∃ C A : ℝ, 0 < C ∧ 0 < A ∧
    ∀ (M N : ℝ) (Rw Rz : ℤ) (α β : GaussianInt → ℂ),
      1 ≤ M → 1 ≤ N →
      (∀ w, ‖α w‖ ≤ 1) → (∀ z, ‖β z‖ ≤ 1) →
      (∀ w, α w ≠ 0 → Work.FIPlan.IsPrimary w ∧ IsCoprime w.re w.im ∧
        (Work.FIPlan.gnorm w : ℝ) ≤ M) →
      (∀ z, β z ≠ 0 → Work.FIPlan.IsPrimary z ∧ (Work.FIPlan.gnorm z : ℝ) ≤ N) →
      ‖KBilin Rw Rz α β‖
        ≤ C * (M + N) ^ ((1 : ℝ) / 12) * (M * N) ^ ((11 : ℝ) / 12)
            * (Real.log (M * N + 2)) ^ A

/-- **FI Proposition 23.1, (23.8).**  `L(M,N)` and `L∗(M,N)` are
`≪ τ(c)(M+N)^{1/12}(MN)^{11/12}` up to a loss `(MN+c+2)^ε`, for the quadratic eigenvalues of any
multiplicative, bounded character `χ`; the local coefficients `α, β` are arbitrary and bounded
by `1`.

**The loss must be a power `(·)^ε` with `ε > 0` arbitrarily small, not a polylogarithm.**
*FI* p. 1032 removes the condition `(c,mn) = 1` by the expansion `m = a m'`, `n = b n'` with
`a, b | c^∞`, `(a,b) = 1`, and then needs `Σ_{a,b | c^∞, (a,b)=1} τ(cab)(ab)^{-11/12} ≪ τ(c)`; that
inequality is **false** — its local factor at `p | c` is
`2/(1-p^{-11/12}) + 2p^{-11/12}/((e_p+1)(1-p^{-11/12})²) - 1 ≥ (1+p^{-11/12})/(1-p^{-11/12})`, so the
quotient is `≥ Π_{p|c}(1 + 2p^{-11/12})` (already `5.5, 16.2, 31.0, 49.6, 67.3` for
`c = 2, 6, 30, 210, 2310`), which is unbounded in `ω(c)`.  The factor is however `≤ c^ε` for every
`ε > 0` (indeed `≤ exp(C(log c)^{1/12})`), so the bound holds with the paper's `(MN)^ε`-type loss.
The paper's own statement (23.8) has exactly this `(MN)^{11/12+ε}`. -/
def Prop231 : Prop :=
  ∀ ε : ℝ, 0 < ε →
  ∃ C : ℝ, 0 < C ∧
    ∀ (M N c d : ℕ) (k : ℤ) (chi : GaussianInt → ℂ) (α β : ℕ → ℂ),
      1 ≤ c → 1 ≤ M → 1 ≤ N → 1 ≤ d →
      (∀ z, ‖chi z‖ ≤ 1) →
      (∀ z1 z2 : GaussianInt, IsCoprime z1 z2 → chi (z1 * z2) = chi z1 * chi z2) →
      (∀ m ∈ Finset.Icc 1 M, ‖α m‖ ≤ 1) → (∀ n ∈ Finset.Icc 1 N, ‖β n‖ ≤ 1) →
      ‖LBilin M N c (grossenChar chi k) α β‖
          ≤ C * ((c.divisors.card : ℝ)) * (M + N) ^ ((1 : ℝ) / 12)
              * (M * N) ^ ((11 : ℝ) / 12)
              * (((M : ℝ) * (N : ℝ) + (c : ℝ) + 2) ^ ε) ∧
      ‖LBilinStar M N c (grossenChar chi k) α β‖
          ≤ C * ((c.divisors.card : ℝ)) * (M + N) ^ ((1 : ℝ) / 12)
              * (M * N) ^ ((11 : ℝ) / 12)
              * (((M : ℝ) * (N : ℝ) + (c : ℝ) + 2) ^ ε)

/-- **FI Proposition 23.2, (23.11)–(23.12).**  The special linear forms
`L(N) = Σ_{n ≤ N} λ(mn)` and `L∗(N) = Σ_{n ≤ N, (n,m)=1} λ(mn)` satisfy

  `‖L(N)‖ ≤ C d(|k|+1) τ(m)^4 √m N^{3/4} log(mN+2)`,
  `‖L∗(N)‖ ≤ C d(|k|+1) τ(m)^2 √m N^{3/4} log(mN+2)`.

`d` is the modulus of the character `χ` of the Grössencharacter (its `4d`-periodicity is used
through Prop. 22.1), `τ(m) = m.divisors.card`. -/
def Prop232 : Prop :=
  ∃ C : ℝ, 0 < C ∧
    ∀ (N m d : ℕ) (k : ℤ) (chi : GaussianInt → ℂ),
      1 ≤ m → 1 ≤ d → 1 ≤ N →
      (∀ z, ‖chi z‖ ≤ 1) →
      (∀ z1 z2 : GaussianInt, IsCoprime z1 z2 → chi (z1 * z2) = chi z1 * chi z2) →
      (∀ (a b' : ℤ), chi (⟨a + 4 * (d : ℤ), b'⟩ : GaussianInt) = chi ⟨a, b'⟩) →
      (∀ (a b' : ℤ), chi (⟨a, b' + 4 * (d : ℤ)⟩ : GaussianInt) = chi ⟨a, b'⟩) →
      ‖LLinear m N (grossenChar chi k)‖
          ≤ C * (d : ℝ) * (|(k : ℝ)| + 1) * (((m.divisors.card : ℕ) : ℝ)) ^ 4
              * Real.sqrt m * (N : ℝ) ^ ((3 : ℝ) / 4) * Real.log ((m : ℝ) * N + 2) ∧
      ‖LStarLinear m N (grossenChar chi k)‖
          ≤ C * (d : ℝ) * (|(k : ℝ)| + 1) * (((m.divisors.card : ℕ) : ℝ)) ^ 2
              * Real.sqrt m * (N : ℝ) ^ ((3 : ℝ) / 4) * Real.log ((m : ℝ) * N + 2)

/-- **FI Theorem 2ψ, (26.2).**  `Σ_{n ≤ x} Λ(n) λ(cn) ≤ C c d(|k|+1) x^{76/77}` for the
quadratic eigenvalues of any multiplicative character `χ` of modulus `4d`. -/
def Theorem2psi : Prop :=
  ∃ C : ℝ, 0 < C ∧
    ∀ (N c d : ℕ) (k : ℤ) (chi : GaussianInt → ℂ),
      1 ≤ c → 1 ≤ d → 1 ≤ N →
      (∀ z, ‖chi z‖ ≤ 1) →
      (∀ z1 z2 : GaussianInt, IsCoprime z1 z2 → chi (z1 * z2) = chi z1 * chi z2) →
      (∀ (a b' : ℤ), chi (⟨a + 4 * (d : ℤ), b'⟩ : GaussianInt) = chi ⟨a, b'⟩) →
      (∀ (a b' : ℤ), chi (⟨a, b' + 4 * (d : ℤ)⟩ : GaussianInt) = chi ⟨a, b'⟩) →
      ‖∑ n ∈ Finset.Icc 1 N,
          ((ArithmeticFunction.vonMangoldt n : ℝ) : ℂ) * quadEigen (grossenChar chi k) (c * n)‖
        ≤ C * (c : ℝ) * (d : ℝ) * (|(k : ℝ)| + 1) * (N : ℝ) ^ ((76 : ℝ) / 77)

end

end Work.FIArea7
