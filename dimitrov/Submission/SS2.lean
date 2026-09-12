import Mathlib
import Submission.FeketeLim
import Submission.XTransfer
import Submission.ChebPower

/-!
# Isolated task: SS2 -- geometric Fekete decay gives polynomial decay on the star

Self-contained statements.  Prove `polyDecay_star_of_fekete_decay` (and no
other unfinished proofs may remain in the file; add helper lemmas freely).

STATEMENT: for `S : Finset ℂ`, if the Fekete numbers of `star S` decay
geometrically in the pair-count exponent,

    ∃ ρ C : ℝ, 0 ≤ ρ ∧ ρ < 1 ∧ 0 ≤ C ∧
      ∀ n ≥ 1, feketeNumber (star S) n ≤ C · ρ^(n(n−1)/2)   -- (hm)

then `PolyDecayOn (star S)` holds (monic `p_j` of every degree `j ≥ 1`
with `‖p_j‖ ≤ C·θ^j` on `star S` for some `θ < 1`).

PROOF PLAN:

0. Let `K := Submission.XTransfer.star S`.  `K` is compact
   (`Submission.ChebPower.isCompact_star S`), hence bounded
   (`IsCompact.isBounded`) -- carry these facts around.

1. limsup of the Fekete root numbers is `≤ ρ`: for every `θ > ρ`,
   eventually `(feketeNumber K (n+1))^(2/((n+1)·n)) ≤ θ`.  Indeed from
   `(hm)` with `n+1`: `m_{n+1} ≤ C·ρ^((n+1)n/2)`; raising to the
   `2/((n+1)n)` power gives
   `m_{n+1}^(2/((n+1)n)) ≤ C^(2/((n+1)n)) · ρ`, and
   `C^(2/((n+1)n)) → 1` as `n → ∞`, so eventually the right side is
   `≤ θ` (if `C = 0` trivial; if `C > 0` use `Real.rpow`-as-`exp·log` or
   `Real.log` monotonicity / `Tendsto` of `fun n => C^(2/((n+1)·n))` to
   `1`).  Conclude `Filter.limsup feketeRoot atTop ≤ ρ` via
   `Filter.limsup_le_iff`-style reasoning (for every θ>ρ, eventually ≤ θ).

2. By the PROVED one-sided Fekete half
   `Submission.FeketeLim.chebyshev_root_le_fekete_root K` (needs
   `K.Nonempty` -- `star S` is nonempty if `S` is; add a `S.Nonempty`
   hypothesis to the theorem if your proof needs it -- and bounded `K`):
       limsup (chebyshevNumber K (n+1))^(1/(n+1)) ≤ limsup feketeRoot ≤ ρ.

3. Pick `θ` with `ρ < θ < 1` (possible since `ρ < 1`; if `ρ = 0` take
   e.g. `θ = 1/2`).  limsup t-root ≤ ρ < θ implies: for all large `n`,
   `(chebyshevNumber K (n+1))^(1/(n+1)) ≤ θ`, i.e.
   `chebyshevNumber K m ≤ θ^m` for all `m ≥ N+1` (raise to the `(n+1)`
   power; use nonnegativity: `chebyshevNumber` is `≥ 0` -- see
   `Submission.FeketeLim.chebyshevNumber_nonneg`).

4. Uniform bound for all `m ≥ 1`: for the finitely many
   `1 ≤ m ≤ N+1`, bound `chebyshevNumber K m ≤ R^m` (the monic `X^m` is
   bounded by `R^m` on `K` for a norm bound `R ≥ 1` of `K` from
   boundedness -- cf. `Submission.FeketeLim.chebyshevNumber_le_pow`), so
   with a constant `M` (e.g. `max (1/R) …` times powers), for all
   `m ≥ 1`: `chebyshevNumber K m ≤ M · θ^m` (absorb the small-`m`
   factors into `M`; ensure `M ≥ 0`).

5. Polynomial witnesses: for each `j ≥ 1` apply
   `Submission.FeketeLim.exists_monic_chebyshev_add` with
   `ε := M · θ^j` (positive) to get a monic `p_j` of degree `j` with
   `∀ X ∈ K, ‖p_j.eval X‖ ≤ chebyshevNumber K j + M·θ^j ≤ 2M·θ^j`, so
   `PolyDecayOn K` holds with `C := 2M`, the chosen `θ`.

Mathlib notes: `Filter.limsup_le_iff` /
`Filter.le_limsup` / `Filter.limsup_le`; `Tendsto` of real powers to 1
(`Real.rpow`/`exp`-`log`, or `Filter.Tendsto` + `Real.continuousAt_rpow`);
`IsCompact.isBounded`; raise rpow inequalities with
`Real.rpow_le_rpow` (base ≥ 0, exponent ≥ 0 monotone) or via `n`-th
powers (`pow_le_pow_left₀` after rewriting `x^(1/k) ≤ θ ↔ x ≤ θ^k`).
-/

noncomputable section

open scoped Real Polynomial Topology BigOperators

namespace Submission.SS2

open Polynomial
open Submission.FeketeLim
open Submission.ChebPower
open Submission.XTransfer

/-- Polynomial decay on `K` (monic `p_j`, `j ≥ 1`, bounded by `C·θ^j`). -/
def PolyDecayOn (K : Set ℂ) : Prop :=
  ∃ C θ : ℝ, 0 ≤ θ ∧ θ < 1 ∧
    ∀ j : ℕ, 1 ≤ j →
      ∃ p : ℂ[X], p.Monic ∧ p.natDegree = j ∧
        ∀ X ∈ K, ‖p.eval X‖ ≤ C * θ ^ j

/-- `IsBoundedUnder (≤)` for a sequence bounded above. -/
lemma isBoundedUnder_atTop_of_le {u : ℕ → ℝ} (hb : ∃ b : ℝ, ∀ n, u n ≤ b) :
    Filter.IsBoundedUnder (· ≤ ·) Filter.atTop u := by
  rcases hb with ⟨b, hb⟩
  unfold Filter.IsBoundedUnder Filter.IsBounded
  refine ⟨b, ?_⟩
  rw [Filter.eventually_map]
  exact Filter.Eventually.of_forall hb

/-- `IsCoboundedUnder (≤)` for a sequence bounded below. -/
lemma isCoboundedUnder_atTop_of_ge {u : ℕ → ℝ} (hb : ∃ b : ℝ, ∀ n, b ≤ u n) :
    Filter.IsCoboundedUnder (· ≤ ·) Filter.atTop u := by
  rcases hb with ⟨b, hb⟩
  unfold Filter.IsCoboundedUnder Filter.IsCobounded
  refine ⟨b, ?_⟩
  intro a ha
  have ha' : ∀ᶠ n : ℕ in Filter.atTop, u n ≤ a := by simpa using ha
  rcases Filter.eventually_atTop.1 ha' with ⟨N, hN⟩
  exact le_trans (hb N) (hN N (le_rfl))

/-- `2` divides the product of two consecutive naturals `(n+1)·n`. -/
lemma two_dvd_mul_succ (n : ℕ) : (2 : ℕ) ∣ (n + 1) * n := by
  simpa [mul_comm, mul_left_comm, mul_assoc] using (n.two_dvd_mul_add_one)

/-- The exponent arithmetic `((n+1)·n/2) · (2/((n+1)·n)) = 1`. -/
lemma expo_cancel (n : ℕ) (hn : 1 ≤ n) :
    ((((n + 1) * n / 2 : ℕ) : ℝ) * (2 / (((n : ℝ) + 1) * (n : ℝ)))) = 1 := by
  have hdiv : (2 : ℕ) ∣ (n + 1) * n := two_dvd_mul_succ n
  have hcast : ((((n + 1) * n / 2 : ℕ) : ℝ) = (((n + 1) * n : ℕ) : ℝ) / 2) := by
    rw [Nat.cast_div_charZero hdiv]
    norm_num
  have hs : (((n + 1) * n : ℕ) : ℝ) = ((n : ℝ) + 1) * (n : ℝ) := by
    norm_num [Nat.cast_add, Nat.cast_mul]
  have hn0 : (n : ℝ) ≠ 0 := by exact_mod_cast (ne_of_gt hn)
  calc
    ((((n + 1) * n / 2 : ℕ) : ℝ) * (2 / (((n : ℝ) + 1) * (n : ℝ))))
        = ((((n + 1) * n : ℕ) : ℝ) / 2) * (2 / (((n : ℝ) + 1) * (n : ℝ))) := by rw [hcast]
    _ = ((((n : ℝ) + 1) * (n : ℝ)) / 2) * (2 / (((n : ℝ) + 1) * (n : ℝ))) := by rw [hs]
    _ = 1 := by
      field_simp [hn0]

/-- The pair-count exponent `2/((n+1)·n)` is positive for `1 ≤ n`. -/
lemma expo_pos (n : ℕ) (hn : 1 ≤ n) : 0 < 2 / (((n : ℝ) + 1) * (n : ℝ)) := by
  have hn0 : (0 : ℝ) < (n : ℝ) := by exact_mod_cast (lt_of_lt_of_le zero_lt_one hn)
  positivity

/-- The pair-count exponent tends to `0` as `n → ∞`. -/
lemma tendsto_expo_zero :
    Filter.Tendsto (fun n : ℕ => 2 / (((n : ℝ) + 1) * (n : ℝ))) Filter.atTop (𝓝 0) := by
  have h1 : Filter.Tendsto (fun n : ℕ => 2 / (n : ℝ)) Filter.atTop (𝓝 0) :=
    tendsto_const_div_atTop_nhds_zero_nat (2 : ℝ)
  have h2 : Filter.Tendsto (fun n : ℕ => 1 / ((n : ℝ) + 1)) Filter.atTop (𝓝 0) :=
    tendsto_one_div_add_atTop_nhds_zero_nat
  have hmul : Filter.Tendsto (fun n : ℕ => (2 / (n : ℝ)) * (1 / ((n : ℝ) + 1))) Filter.atTop (𝓝 0) := by
    simpa using h1.mul h2
  refine hmul.congr' ?_
  filter_upwards [(Filter.eventually_ge_atTop 1)] with n hn
  have hn0 : (n : ℝ) ≠ 0 := by exact_mod_cast (ne_of_gt hn)
  field_simp [hn0]

/-- `(1/(n+1))·(n+1) = 1` for the root-power raise. -/
lemma expo_raise (n : ℕ) : (1 / ((n : ℝ) + 1)) * ((n + 1 : ℕ) : ℝ) = 1 := by
  have hcast : ((n + 1 : ℕ) : ℝ) = (n : ℝ) + 1 := by norm_num [Nat.cast_add]
  rw [hcast]
  have hnnz2 : ((n : ℝ) + 1) ≠ 0 := by positivity
  field_simp [hnnz2]

/-- **SS2.**  Geometric decay of the Fekete numbers of `star S` gives
polynomial decay on `star S`. -/
theorem polyDecay_star_of_fekete_decay (S : Finset ℂ) (hSne : S.Nonempty)
    (hm : ∃ ρ C : ℝ, 0 ≤ ρ ∧ ρ < 1 ∧ 0 ≤ C ∧
      ∀ n : ℕ, 1 ≤ n →
        Submission.FeketeLim.feketeNumber (Submission.XTransfer.star S) n
          ≤ C * ρ ^ (n * (n - 1) / 2)) :
    PolyDecayOn (Submission.XTransfer.star S) := by
  classical
  let K : Set ℂ := Submission.XTransfer.star S
  rcases hm with ⟨ρ, C, hρ0, hρ1, hC0, hmn⟩
  have hKne : K.Nonempty := by
    dsimp [K]
    exact ⟨(0 : ℂ), Submission.XTransfer.zero_mem_star hSne⟩
  have hKb : Bornology.IsBounded K := by
    dsimp [K]
    exact (Submission.ChebPower.isCompact_star S).isBounded
  let e : ℕ → ℝ := fun n : ℕ => 2 / (((n : ℝ) + 1) * (n : ℝ))
  let B : ℕ → ℝ := fun n : ℕ => (feketeNumber K (n + 1)) ^ e n
  let A : ℕ → ℝ := fun n : ℕ => (chebyshevNumber K (n + 1)) ^ (1 / ((n : ℝ) + 1))
  -- choose θ with ρ < θ < 1
  let θ : ℝ := (1 + ρ) / 2
  have hθpos : 0 < θ := by
    dsimp [θ]
    nlinarith
  have hθlt1 : θ < 1 := by
    dsimp [θ]
    nlinarith
  have hρθ : ρ < θ := by
    dsimp [θ]
    nlinarith
  -- geometric-decay pointwise bound, raised to the pair exponent
  have hB_le : ∀ n : ℕ, 1 ≤ n → B n ≤ C ^ e n * ρ := by
    intro n hn
    change (feketeNumber K (n + 1)) ^ e n ≤ C ^ e n * ρ
    have hmnle : feketeNumber K (n + 1) ≤ C * ρ ^ ((n + 1) * n / 2) := by
      have hh := hmn (n + 1) (by omega)
      have hss : (n + 1) * ((n + 1) - 1) / 2 = (n + 1) * n / 2 := by
        rw [show (n + 1) - 1 = n by omega]
      simpa [hss] using hh
    have hm0 : 0 ≤ feketeNumber K (n + 1) := feketeNumber_nonneg hKne hKb (n + 1)
    have he0 : 0 ≤ e n := by
      dsimp [e]
      exact le_of_lt (expo_pos n hn)
    have hstep := Real.rpow_le_rpow hm0 hmnle he0
    have hrhs : (C * ρ ^ ((n + 1) * n / 2)) ^ e n = C ^ e n * ρ := by
      let d : ℕ := (n + 1) * n / 2
      have h1 : (C * ρ ^ d) ^ e n = C ^ e n * (ρ ^ d) ^ e n :=
        Real.mul_rpow hC0 (pow_nonneg hρ0 d)
      have h2 : (ρ ^ d) ^ e n = ρ ^ ((d : ℝ) * e n) :=
        rpow_nat_mul ρ hρ0 d (e n)
      have h3 : ((d : ℝ) * e n) = (1 : ℝ) := by
        dsimp [d, e]
        exact expo_cancel n hn
      have h4 : ρ ^ (1 : ℝ) = ρ := Real.rpow_one ρ
      calc
        (C * ρ ^ d) ^ e n = C ^ e n * (ρ ^ d) ^ e n := h1
        _ = C ^ e n * ρ ^ ((d : ℝ) * e n) := by rw [h2]
        _ = C ^ e n * ρ ^ (1 : ℝ) := by rw [h3]
        _ = C ^ e n * ρ := by rw [h4]
    calc
      (feketeNumber K (n + 1)) ^ e n ≤ (C * ρ ^ ((n + 1) * n / 2)) ^ e n := hstep
      _ = C ^ e n * ρ := hrhs
  -- eventual bound for B below every y > ρ
  have hEvB : ∀ y : ℝ, ρ < y → ∀ᶠ n : ℕ in Filter.atTop, B n < y := by
    intro y hy
    by_cases hCz : C = 0
    · have hypos : 0 < y := by linarith
      refine (Filter.eventually_ge_atTop 1).mono ?_
      intro n hn1
      have hb := hB_le n hn1
      have he0' : e n ≠ 0 := ne_of_gt (expo_pos n hn1)
      have hz : C ^ e n * ρ = 0 := by
        rw [hCz]
        simp [Real.zero_rpow he0']
      calc
        B n ≤ C ^ e n * ρ := hb
        _ = 0 := hz
        _ < y := hypos
    · have hCpos : 0 < C := lt_of_le_of_ne hC0 (Ne.symm hCz)
      have hCt : Filter.Tendsto
          (fun n : ℕ => C ^ (2 / (((n : ℝ) + 1) * (n : ℝ)))) Filter.atTop (𝓝 1) := by
        have hcont : Continuous (fun x : ℝ => C ^ x) := Real.continuous_const_rpow hCz
        have hcomp := (hcont.continuousAt.tendsto.comp tendsto_expo_zero)
        simpa [Real.rpow_zero, Function.comp_def] using hcomp
      have hprod : Filter.Tendsto
          (fun n : ℕ => C ^ (2 / (((n : ℝ) + 1) * (n : ℝ))) * ρ) Filter.atTop (𝓝 ρ) := by
        simpa [one_mul] using (hCt.mul (tendsto_const_nhds (x := ρ)))
      have hev : ∀ᶠ n : ℕ in Filter.atTop, C ^ (2 / (((n : ℝ) + 1) * (n : ℝ))) * ρ < y :=
        (hprod.eventually_lt (tendsto_const_nhds (x := y)) hy)
      refine ((Filter.eventually_ge_atTop 1).and hev).mono ?_
      intro n hn
      rcases hn with ⟨hn1, hbnd⟩
      exact lt_of_le_of_lt (hB_le n hn1) hbnd
  -- B is bounded above and below
  rcases bounded_radius hKb with ⟨R, hRpos, hR⟩
  have hB_nonneg : ∀ n : ℕ, 0 ≤ B n := by
    intro n
    have hm0 : 0 ≤ feketeNumber K (n + 1) := feketeNumber_nonneg hKne hKb (n + 1)
    dsimp [B]
    exact Real.rpow_nonneg hm0 (e n)
  have hB_bdd : ∃ b : ℝ, ∀ n : ℕ, B n ≤ b := by
    refine ⟨(max 1 (2 * R)) ^ 4, ?_⟩
    intro n
    dsimp [B]
    exact feketeRoot_bounded hKne hKb (le_of_lt hRpos) hR n
  have hlimB : Filter.limsup B Filter.atTop ≤ ρ := by
    exact (Filter.limsup_le_iff (f := Filter.atTop) (u := B) (x := ρ)
      (isCoboundedUnder_atTop_of_ge ⟨0, hB_nonneg⟩) (isBoundedUnder_atTop_of_le hB_bdd)).2 hEvB
  -- limsup A ≤ limsup B (one-sided Fekete half)
  have hlimA : Filter.limsup A Filter.atTop ≤ Filter.limsup B Filter.atTop := by
    simpa [A, B, e] using chebyshev_root_le_fekete_root (K := K) hKne hKb
  -- A bounded above
  have hA_bdd : Filter.IsBoundedUnder (· ≤ ·) Filter.atTop A := by
    refine isBoundedUnder_atTop_of_le ⟨R, ?_⟩
    intro n
    dsimp [A]
    exact chebRoot_bounded hKb (le_of_lt hRpos) hR n
  have hlimA_ltθ : Filter.limsup A Filter.atTop < θ := by
    exact lt_of_le_of_lt (le_trans hlimA hlimB) hρθ
  have hEvA : ∀ᶠ n : ℕ in Filter.atTop, A n < θ :=
    Filter.eventually_lt_of_limsup_lt (f := Filter.atTop) (u := A) hlimA_ltθ hA_bdd
  rcases Filter.eventually_atTop.1 hEvA with ⟨Nev, hNev⟩
  -- large m: t_m ≤ θ^m
  have hBig : ∀ m : ℕ, Nev + 1 ≤ m → chebyshevNumber K m ≤ θ ^ m := by
    intro m hm
    let n : ℕ := m - 1
    have hmn' : n + 1 = m := by
      dsimp [n]
      omega
    have hnn : Nev ≤ n := by
      dsimp [n]
      omega
    have hAn : (chebyshevNumber K (n + 1)) ^ (1 / ((n : ℝ) + 1)) < θ := by
      simpa [A] using (hNev n hnn)
    have ht0 : 0 ≤ chebyshevNumber K (n + 1) := chebyshevNumber_nonneg hKb (by omega : 1 ≤ n + 1)
    have hroot0 : 0 ≤ (chebyshevNumber K (n + 1)) ^ (1 / ((n : ℝ) + 1)) := Real.rpow_nonneg ht0 _
    have hlt : (chebyshevNumber K (n + 1)) ^ (1 / ((n : ℝ) + 1)) ≤ θ := le_of_lt hAn
    have hstep1 := Real.rpow_le_rpow hroot0 hlt (by positivity : (0 : ℝ) ≤ ((n + 1 : ℕ) : ℝ))
    have hL : ((chebyshevNumber K (n + 1)) ^ (1 / ((n : ℝ) + 1))) ^ (((n + 1 : ℕ) : ℝ))
        = chebyshevNumber K (n + 1) := by
      calc
        ((chebyshevNumber K (n + 1)) ^ (1 / ((n : ℝ) + 1))) ^ (((n + 1 : ℕ) : ℝ))
            = chebyshevNumber K (n + 1) ^ ((1 / ((n : ℝ) + 1)) * (((n + 1 : ℕ) : ℝ))) := by
                rw [Real.rpow_mul ht0]
        _ = chebyshevNumber K (n + 1) ^ (1 : ℝ) := by
                congr 1
                exact expo_raise n
        _ = chebyshevNumber K (n + 1) := by
                rw [Real.rpow_one]
    have hθpow : θ ^ ((n + 1 : ℕ) : ℝ) = θ ^ (n + 1) := by
      rw [Real.rpow_natCast]
    have hb : chebyshevNumber K (n + 1) ≤ θ ^ (n + 1) := by
      rw [hL] at hstep1
      rwa [hθpow] at hstep1
    simpa [hmn'] using hb
  -- constant M := (R'/θ)^{Nev}
  let R' : ℝ := max 1 R
  let M : ℝ := (R' / θ) ^ Nev
  have hR'1 : 1 ≤ R' := by dsimp [R']; exact le_max_left 1 R
  have hRleR' : R ≤ R' := by dsimp [R']; exact le_max_right 1 R
  have hθ1le : θ ≤ 1 := le_of_lt hθlt1
  have hRθ1 : 1 ≤ R' / θ := by
    dsimp [R']
    have h1 : (1 : ℝ) / θ ≤ R' / θ := div_le_div_of_nonneg_right (by linarith) (le_of_lt hθpos)
    have h2 : (1 : ℝ) ≤ 1 / θ := by
      rw [le_div_iff₀ hθpos]
      linarith
    linarith
  have hM1 : 1 ≤ M := by
    dsimp [M]
    exact one_le_pow₀ hRθ1
  have hMpos : 0 < M := lt_of_lt_of_le zero_lt_one hM1
  have hMpow : M * θ ^ Nev = (R') ^ Nev := by
    dsimp [M]
    rw [← mul_pow]
    field_simp [ne_of_gt hθpos]
  have hsmall_abs : ∀ m : ℕ, 1 ≤ m → m ≤ Nev → chebyshevNumber K m ≤ (R') ^ Nev := by
    intro m hm1 hmNev
    have ht : chebyshevNumber K m ≤ R ^ m := chebyshevNumber_le_pow (le_of_lt hRpos) hR
    have hmR : R ^ m ≤ (R') ^ m := pow_le_pow_left₀ (le_of_lt hRpos) hRleR' m
    have hmN : (R') ^ m ≤ (R') ^ Nev := pow_le_pow_right₀ hR'1 hmNev
    exact le_trans (le_trans ht hmR) hmN
  have hsmall : ∀ m : ℕ, 1 ≤ m → m ≤ Nev → chebyshevNumber K m ≤ M * θ ^ m := by
    intro m hm1 hmNev
    have h1 := hsmall_abs m hm1 hmNev
    have h3 : M * θ ^ Nev ≤ M * θ ^ m := by
      exact mul_le_mul_of_nonneg_left (pow_le_pow_of_le_one (le_of_lt hθpos) hθ1le hmNev) (le_of_lt hMpos)
    calc
      chebyshevNumber K m ≤ (R') ^ Nev := h1
      _ = M * θ ^ Nev := hMpow.symm
      _ ≤ M * θ ^ m := h3
  have hbigM : ∀ m : ℕ, Nev + 1 ≤ m → chebyshevNumber K m ≤ M * θ ^ m := by
    intro m hm
    exact le_trans (hBig m hm) (le_mul_of_one_le_left (pow_nonneg (le_of_lt hθpos) m) hM1)
  have hMbound : ∀ m : ℕ, 1 ≤ m → chebyshevNumber K m ≤ M * θ ^ m := by
    intro m hm1
    by_cases hle : m ≤ Nev
    · exact hsmall m hm1 hle
    · have hgt : Nev + 1 ≤ m := by omega
      exact hbigM m hgt
  -- final: monic polynomials
  refine ⟨2 * M, θ, le_of_lt hθpos, hθlt1, ?_⟩
  intro j hj
  have hεpos : 0 < M * θ ^ j := by
    exact mul_pos hMpos (pow_pos hθpos j)
  rcases exists_monic_chebyshev_add (K := K) hKb (n := j) hj (M * θ ^ j) hεpos with ⟨p, hpmonic, hpdeg, hpb⟩
  refine ⟨p, hpmonic, hpdeg, ?_⟩
  intro X hX
  have hmain : chebyshevNumber K j ≤ M * θ ^ j := hMbound j hj
  calc
    ‖p.eval X‖ ≤ chebyshevNumber K j + M * θ ^ j := hpb X hX
    _ ≤ M * θ ^ j + M * θ ^ j := by
      simpa [add_comm] using add_le_add_left hmain (M * θ ^ j)
    _ = 2 * M * θ ^ j := by ring

end Submission.SS2

end
