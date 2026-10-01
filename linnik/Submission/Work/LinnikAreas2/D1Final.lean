/-
# `LinnikAreas2.D1Final` — the assembly of HB Lemma 11.1 (`(D1)`)

This module reduces the contract's `(D1)` (HB Lemma 11.1, the weighted zero-density bound
`Σ_χ wHB(λ^{(χ)}) ≤ 67/6 + ε`) to its two analytic inputs, each isolated below as an interface:

* `PsiBound ε` — HB (11.14): the `ℓ²`-norm of the `ψ`-mollifier coefficient family,
  `Σ_n ‖b_n‖² ≤ (1+ε)·(2x-u-v)/(2(v-u))` at the parameters `u = 8/15`, `v = 47/60`, `x = 73/60`;
* `ThetaBound δ` — HB (11.17) *in its sharp (subtracted) form*: for every character carrying a
  working-region zero `ρ` with `λ(ρ) ≤ lamMax q` the weighted diagonal θ-series is `≤ 1`, at the
  weight `w_χ = 2w·wHB(λ(ρ))` with `w = 1/10 - δ`.  This is the estimate that makes the diagonal
  of the Gram matrix of the `a`-family equal to `1` (and *not* `1/(1-e^{-2(x-u)λ})`), which is
  what produces the constant `67/6`.

Everything else — the zero detector HB (11.8)–(11.10), the off-diagonal pair bound HB (11.16),
the operator/duality bound HB (11.15) built from them, the `ℓ²` duality principle and the
coefficient calculus of HB (11.11)/(11.12) — is already proved in the workspace and is assembled
here into `(D1)`.

The mathematical content of the assembly is the following chain (for `q ≥ q₀(ε)`, with
`𝓛 = log q`, `S = hbSet q` enumerated by `j ↦ (χ_j, ρ_j)`, `w = 1/10 - δ` and
`w_j = 2w·wHB(λ(ρ_j))`):

```
(1 - O(1/𝓛)) Σ_j w_j  ≤  Σ_j w_j(1 - C/𝓛)²
                       ≤  Σ_j ‖Σ_n a_{n,j} b_n‖²            -- detector + (11.11)/(11.12)
                       ≤  ((1+c₁) + (C/𝓛)Σ_j w_j)·Σ_n‖b_n‖²  -- (11.15)+duality, (11.16), (11.17)
                       ≤  ((1+c₁) + (C/𝓛)Σ_j w_j)·(1+ψε)67/30 -- (11.14)
```

whence `Σ_j w_j ≤ (1+O(ε))67/30`, i.e. `Σ_χ 2w·wHB(λ^{(χ)}) ≤ (1+O(ε))·(2x-u-v)/(2(v-u))`, and
finally `Σ_χ wHB(λ^{(χ)}) ≤ 67/6 + ε` (HB's step (VI)).
-/
import Mathlib
import Submission.Work.LinnikContract2.Contract
import Submission.Work.LinnikAreas2.D1Assembly
import Submission.Work.LinnikAreas2.d1_of_area1
import Submission.Work.LinnikAreas2.hb15_operator_bound
import Submission.Work.LinnikAreas2.duality_tsum
import Submission.Work.LinnikAreas2.hb11_offdiag_pair_bound
import Submission.Work.LinnikAreas.Density4.zero_detector
import Submission.Work.A7.lamChar_api

open DirichletCharacter Complex
open scoped Classical BigOperators
noncomputable section
set_option linter.unusedVariables false
set_option maxHeartbeats 1000000

namespace Work.LinnikAreas2

open Work.LinnikAreas.Density4

/-! ## 1. The two analytic inputs, as interfaces -/

/-- **HB (11.14)** at the contract's parameters `(u,v,x) = (8/15, 47/60, 73/60)`. -/
def PsiBound (ε : ℝ) : Prop :=
  ∃ q₀ : ℕ, ∀ q : ℕ, q₀ ≤ q → ∀ [NeZero q],
    (∑' n : ℕ, ‖bcoef q (8/15) (47/60) (73/60) n‖ ^ 2) ≤ (1 + ε) * (67/30)

/-- **HB (11.17), sharp (subtracted) form**, at the contract's parameters
`(u,x) = (8/15, 73/60)` and the weight cut-off `w = 1/10 - δ`. -/
def ThetaBound (δ : ℝ) : Prop :=
  ∀ c1 : ℝ, 0 < c1 → ∃ q₀ : ℕ, ∀ q : ℕ, q₀ ≤ q → ∀ [NeZero q]
    (χ : DirichletCharacter ℂ q) (ρ : ℂ),
    Work.LinnikContract2.IsZ χ ρ → Work.LinnikContract2.lamOf q ρ ≤ Work.LinnikContract2.lamMax q →
      (2*(1/10 - δ) * Work.LinnikContract2.wHB (Work.LinnikContract2.lamOf q ρ))
        * (∑' n : ℕ, ((∑ d ∈ n.divisors, thetaM ((q:ℝ)^(1/10-δ)) d : ℝ))^2
            * (n:ℝ)^(1 - 2*ρ.re) * WT q (8/15) (73/60) n) ≤ 1 + c1

/-! ## 2. Elementary helpers -/

/-- The character value identity needed to match the off-diagonal pair bound
(`Work.LinnikAreas2.hb11_offdiag_pair_bound`) against the operator bound
(`Work.LinnikAreas2.hb15_operator_bound`). -/
lemma chi_mul_inv_apply {q : ℕ} [NeZero q] (χ χ' : DirichletCharacter ℂ q) (a : ZMod q) :
    (χ * χ'⁻¹) a = χ a * (starRingEnd ℂ) (χ' a) := by
  rw [MulChar.mul_apply, MulChar.inv_apply]
  congr 1
  rw [show (starRingEnd ℂ) (χ' a) = star (χ' a) from rfl, MulChar.star_apply', MulChar.inv_apply]

lemma chi_mul_inv_ne_one {q : ℕ} [NeZero q] {χ χ' : DirichletCharacter ℂ q} (h : χ ≠ χ') :
    χ * χ'⁻¹ ≠ 1 := by
  intro h1
  refine h ?_
  have h2 := congrArg (fun (f : DirichletCharacter ℂ q) => f * χ') h1
  rwa [mul_assoc, inv_mul_cancel, mul_one, one_mul] at h2

/-- The Heath-Brown weight of the assembly is non-negative for `q ≥ 3`
(then `log q ≥ 1` and `q^{8/15} ≤ (log q)² q^{73/60}`). -/
lemma WT_nonneg {q : ℕ} (hq : 3 ≤ q) (n : ℕ) : 0 ≤ WT q (8/15) (73/60) n := by
  have hq1 : (1:ℝ) ≤ (q:ℝ) := by exact_mod_cast (by omega : 1 ≤ q)
  have hqpos : (0:ℝ) < (q:ℝ) := by positivity
  have hL1 : (1:ℝ) ≤ Real.log q := by
    rw [Real.le_log_iff_exp_le (by positivity)]
    have : (3:ℝ) ≤ (q:ℝ) := by exact_mod_cast hq
    linarith [Real.exp_one_lt_three]
  have hXpos : (0:ℝ) < (q:ℝ)^((73:ℝ)/60) := Real.rpow_pos_of_pos hqpos _
  have hUpos : (0:ℝ) < (q:ℝ)^((8:ℝ)/15) := Real.rpow_pos_of_pos hqpos _
  have hcase : (q:ℝ)^((8:ℝ)/15) ≤ (Real.log q)^2 * (q:ℝ)^((73:ℝ)/60) := by
    have h1 : (q:ℝ)^((8:ℝ)/15) ≤ (q:ℝ)^((73:ℝ)/60) :=
      Real.rpow_le_rpow_of_exponent_le hq1 (by norm_num)
    have h2 : (1:ℝ) ≤ (Real.log q)^2 := by nlinarith
    calc (q:ℝ)^((8:ℝ)/15) ≤ (q:ℝ)^((73:ℝ)/60) := h1
      _ = 1 * (q:ℝ)^((73:ℝ)/60) := by ring
      _ ≤ (Real.log q)^2 * (q:ℝ)^((73:ℝ)/60) := mul_le_mul_of_nonneg_right h2 hXpos.le
  rw [WT]
  exact wt_nonneg hUpos hXpos hcase n

/-- `‖b_n‖² ≤ n·e^{-n/q^x}`: with `|Σ_{d|n}ψ_d| ≤ n` and `‖(n:ℂ)^{-1/2}‖² = n^{-1}` this is the
(super-exponentially decaying) majorant that makes the `ψ`-coefficient family square-summable. -/
lemma norm_bcoef_sq_le {q : ℕ} [NeZero q] (u v x : ℝ) (n : ℕ) :
    ‖bcoef q u v x n‖ ^ 2 ≤ (n:ℝ) * Real.exp (-(n:ℝ)/(q:ℝ)^x) := by
  rcases Nat.eq_zero_or_pos n with hn | hn
  · subst hn; simp [bcoef_zero]
  · have hn' : (0:ℝ) < (n:ℝ) := by exact_mod_cast hn
    have hqpos : (0:ℝ) < (q:ℝ) := Nat.cast_pos.mpr (NeZero.pos q)
    have hnorm : ‖bcoef q u v x n‖ = |psiS ((q:ℝ)^u) ((q:ℝ)^v) n|
        * ‖(n:ℂ)^(-(1/2:ℂ))‖ * Real.sqrt (WT q u x n) := by
      simp only [bcoef, norm_mul, Complex.norm_real, Real.norm_eq_abs,
        abs_of_nonneg (Real.sqrt_nonneg _)]
    have hpsi : |psiS ((q:ℝ)^u) ((q:ℝ)^v) n| ≤ (n:ℝ) :=
      abs_psiS_le (Real.rpow_pos_of_pos hqpos u) n
    have hcp : ‖(n:ℂ)^(-(1/2:ℂ))‖ ^ 2 = (n:ℝ)^(-1:ℝ) := by
      rw [Complex.norm_natCast_cpow_of_pos hn]
      rw [show (-(1/2:ℂ)).re = (-(1/2:ℝ)) by simp]
      rw [pow_two, ← Real.rpow_add hn']
      norm_num
    have hsqt : (Real.sqrt (WT q u x n)) ^ 2 ≤ Real.exp (-(n:ℝ)/(q:ℝ)^x) := by
      by_cases h : 0 ≤ WT q u x n
      · rw [Real.sq_sqrt h, WT, wt]; exact wt_le_exp n
      · rw [Real.sqrt_eq_zero_of_nonpos (le_of_not_ge h)]; simp; positivity
    have h1 : |psiS ((q:ℝ)^u) ((q:ℝ)^v) n| ^ 2 ≤ (n:ℝ)^2 := by
      nlinarith [abs_nonneg (psiS ((q:ℝ)^u) ((q:ℝ)^v) n), hpsi]
    rw [hnorm, mul_pow, mul_pow, hcp]
    calc |psiS ((q:ℝ)^u) ((q:ℝ)^v) n| ^ 2 * (n:ℝ)^(-1:ℝ) * (Real.sqrt (WT q u x n)) ^ 2
        ≤ ((n:ℝ)^2 * (n:ℝ)^(-1:ℝ)) * Real.exp (-(n:ℝ)/(q:ℝ)^x) :=
          mul_le_mul (mul_le_mul h1 le_rfl (by positivity) (sq_nonneg _)) hsqt
            (sq_nonneg _) (by positivity)
      _ = (n:ℝ) * Real.exp (-(n:ℝ)/(q:ℝ)^x) := by
          rw [Real.rpow_neg_one, sq]
          field_simp

/-- The `ψ`-coefficient family `b_n` of HB (11.12) is square-summable. -/
lemma summable_norm_bcoef_sq {q : ℕ} [NeZero q] (u v x : ℝ) :
    Summable (fun n : ℕ => ‖bcoef q u v x n‖ ^ 2) := by
  have hqpos : (0:ℝ) < (q:ℝ) := Nat.cast_pos.mpr (NeZero.pos q)
  have hXpos : (0:ℝ) < (q:ℝ)^x := Real.rpow_pos_of_pos hqpos x
  refine Summable.of_norm_bounded
    (g := fun n : ℕ => (n:ℝ) * Real.exp (-(1/(q:ℝ)^x) * (n:ℝ))) ?_ ?_
  · simpa using (Real.summable_pow_mul_exp_neg_nat_mul (r := 1/(q:ℝ)^x) 1 (by positivity))
  · intro n
    have h := norm_bcoef_sq_le (q := q) u v x n
    have : ‖‖bcoef q u v x n‖ ^ 2‖ = ‖bcoef q u v x n‖ ^ 2 := by
      rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
    rw [this]
    refine le_trans h (le_of_eq ?_)
    rw [show -(1/(q:ℝ)^x) * (n:ℝ) = -(n:ℝ)/(q:ℝ)^x by ring]

/-! ## 3. Enumerating the characters with a box zero, by minimising zeros -/

/-- The `N(λ)` characters carrying a working-region zero, enumerated by `Fin S.card` and
equipped with a *minimising* zero `ρ_j` (`λ(ρ_j) = lamChar χ_j`). -/
lemma exists_enum_min {q : ℕ} [NeZero q] (S : Finset (DirichletCharacter ℂ q))
    (hS : ∀ χ ∈ S, ∃ ρ, Work.LinnikContract2.IsZ χ ρ) :
    ∃ (chi : Fin S.card → DirichletCharacter ℂ q) (rho : Fin S.card → ℂ),
      Function.Injective chi ∧ (∀ j, chi j ∈ S) ∧
      (∀ j, Work.LinnikContract2.IsZ (chi j) (rho j)) ∧
      (∀ j, Work.LinnikContract2.lamOf q (rho j) = Work.LinnikContract2.lamChar (chi j)) := by
  classical
  have hlen : S.toList.length = S.card := by rw [Finset.toList]; exact Multiset.length_toList _
  let e : Fin S.toList.length ≃ {x // x ∈ S.toList} :=
    List.Nodup.getEquiv S.toList (Finset.nodup_toList S)
  let chi : Fin S.card → DirichletCharacter ℂ q := fun j => (e (Fin.cast hlen.symm j)).1
  have hchi_mem : ∀ j, chi j ∈ S := fun j => Finset.mem_toList.mp (e (Fin.cast hlen.symm j)).2
  have hchi_inj : Function.Injective chi := by
    intro j k hjk
    have h1 : e (Fin.cast hlen.symm j) = e (Fin.cast hlen.symm k) := Subtype.ext hjk
    have h2 : Fin.cast hlen.symm j = Fin.cast hlen.symm k := e.injective h1
    exact Fin.cast_injective hlen.symm h2
  have hne : ∀ j, ∃ ρ, Work.LinnikContract2.IsZ (chi j) ρ := fun j => hS (chi j) (hchi_mem j)
  let rho : Fin S.card → ℂ := fun j =>
    Classical.choose (Work.A7.exists_lamChar_eq_lamOf (q := q) (hne j))
  have hspec : ∀ j, Work.LinnikContract2.IsZ (chi j) (rho j) ∧
      Work.LinnikContract2.lamChar (chi j) = Work.LinnikContract2.lamOf q (rho j) :=
    fun j => Classical.choose_spec (Work.A7.exists_lamChar_eq_lamOf (q := q) (hne j))
  exact ⟨chi, rho, hchi_inj, hchi_mem, fun j => (hspec j).1, fun j => (hspec j).2.symm⟩

/-- Reindexing a `Finset` sum along an injective parametrisation by `Fin S.card`. -/
lemma sum_fin_eq_sum_finset {α : Type*} (S : Finset α) {chi : Fin S.card → α}
    (hinj : Function.Injective chi) (hmem : ∀ j, chi j ∈ S) (f : α → ℝ) :
    (∑ j : Fin S.card, f (chi j)) = ∑ x ∈ S, f x := by
  have himg : Finset.image chi Finset.univ = S := by
    apply Finset.eq_of_subset_of_card_le
    · intro x hx
      rcases Finset.mem_image.mp hx with ⟨j, -, rfl⟩
      exact hmem j
    · rw [Finset.card_image_of_injective _ hinj, Finset.card_univ, Fintype.card_fin]
  refine Finset.sum_bij (fun j _ => chi j) (fun j _ => hmem j) ?_ ?_ ?_
  · intro x _ y _ hxy
    exact hinj hxy
  · intro b hb
    have : b ∈ Finset.image chi Finset.univ := by rw [himg]; exact hb
    rcases Finset.mem_image.mp this with ⟨j, -, hj⟩
    exact ⟨j, Finset.mem_univ j, hj⟩
  · intro x _
    rfl

/-! ## 5. The two analytic inputs of the literature, as `Prop`s, and the instantiation -/

/-- **Graham's `θ`-sieve estimate** (HB (11.13), `θ` case): the exact statement of
`Work.LinnikAreas2.graham_theta_sieve` (proved). -/
def GrahamTheta : Prop :=
  ∀ ε : ℝ, 0 < ε → ∃ C₁ : ℝ, 0 < C₁ ∧ ∀ (w L : ℝ), 0 < w → 0 < L →
    (∀ N : ℕ, 1 ≤ N → (N:ℝ) ≤ Real.exp (w*L) →
      (∑ n ∈ Finset.Icc 1 N, (∑ d ∈ n.divisors,
        Work.LinnikAreas.Density4.thetaM (Real.exp (w*L)) d)^2)
        ≤ 1 + (1+ε)*(N:ℝ)*Real.log (N:ℝ)/(Real.log (Real.exp (w*L)))^2
            + C₁*(N:ℝ)/(Real.log (Real.exp (w*L)))^2) ∧
    (∀ N : ℕ, Real.exp (w*L) ≤ (N:ℝ) →
      (∑ n ∈ Finset.Icc 1 N, (∑ d ∈ n.divisors,
        Work.LinnikAreas.Density4.thetaM (Real.exp (w*L)) d)^2)
        ≤ 1 + (1+ε)*(N:ℝ)/Real.log (Real.exp (w*L))
            + C₁*(N:ℝ)/(Real.log (Real.exp (w*L)))^2)

/-- **The sharp (subtracted) HB (11.17)**: the exact statement of the delegated lemma
`Work.LinnikAreas2.theta_diag_sharp2` (see `NOTE_theta_diag_sharp2.md`). -/
def ThetaSharp : Prop :=
  ∀ ε : ℝ, 0 < ε → ∀ (u w x : ℝ), 0 < w → 2*w < u → u < x →
    ∀ C₁ : ℝ, 0 < C₁ → ∃ L₀ C₂ : ℝ, 0 < L₀ ∧ 0 < C₂ ∧
    ∀ (L β : ℝ), L₀ ≤ L → (1/2 : ℝ) ≤ β → β < 1 →
      (1-β)*L ≤ Real.log (Real.log L)/3 →
      (∀ N : ℕ, 1 ≤ N → (N:ℝ) ≤ Real.exp (w*L) →
        (∑ n ∈ Finset.Icc 1 N, (∑ d ∈ n.divisors,
          Work.LinnikAreas.Density4.thetaM (Real.exp (w*L)) d)^2)
          ≤ 1 + (1+ε/2)*(N:ℝ)*Real.log N/(w*L)^2 + C₁*(N:ℝ)/(w*L)^2) →
      (∀ N : ℕ, Real.exp (w*L) ≤ (N:ℝ) →
        (∑ n ∈ Finset.Icc 1 N, (∑ d ∈ n.divisors,
          Work.LinnikAreas.Density4.thetaM (Real.exp (w*L)) d)^2)
          ≤ 1 + (1+ε/2)*(N:ℝ)/(w*L) + C₁*(N:ℝ)/(w*L)^2) →
      (∑' n : ℕ, ((∑ d ∈ n.divisors,
          Work.LinnikAreas.Density4.thetaM (Real.exp (w*L)) d : ℝ))^2
          * (n:ℝ)^(1-2*β)
          * (Real.exp (-(n:ℝ)/Real.exp (x*L)) - Real.exp (-(n:ℝ)*L^2/Real.exp (u*L))))
        ≤ (1+ε) * ((Real.exp (x*L))^(2-2*β) - (Real.exp (u*L))^(2-2*β))
            / (2*w*(1-β)*L)
          + C₂ / L

/-- **Graham's `ψ`-sieve estimate** (HB (11.13), `ψ` case): the exact statement of
`Work.LinnikAreas2.graham_psi_sieve`. -/
def GrahamPsiSieve : Prop :=
  ∀ ε : ℝ, 0 < ε → ∀ (u v : ℝ), 0 < u → u < v → ∃ C₁ : ℝ, 0 < C₁ ∧
    ∀ (L U V : ℝ), 0 < L → U = Real.exp (u * L) → V = Real.exp (v * L) →
      (∀ N : ℕ, U ≤ (N : ℝ) → (N : ℝ) ≤ V →
        Work.LinnikAreas2.psSum U V N
          ≤ (1 + ε) * (N : ℝ) * Real.log ((N : ℝ) / U) / (Real.log (V / U)) ^ 2
              + C₁ * (N : ℝ) / (Real.log (V / U)) ^ 2) ∧
      (∀ N : ℕ, V ≤ (N : ℝ) →
        Work.LinnikAreas2.psSum U V N
          ≤ (1 + ε) * (N : ℝ) / Real.log (V / U)
              + C₁ * (N : ℝ) / (Real.log (V / U)) ^ 2)

/-- **HB (11.14) with a general constant**: the exact statement of the delegated lemma
`Work.LinnikAreas2.psi_weighted_eval_gen`. -/
def PsiWeightedGen : Prop :=
  ∀ ε : ℝ, 0 < ε → ∀ (u v x : ℝ), 0 < u → u < v → v < x → v - u ≤ x - v →
    ∀ C₁ : ℝ, 0 < C₁ → ∃ C₂ : ℝ, 0 < C₂ ∧
    ∀ (L U V X : ℝ), 0 < L → 1 ≤ U → U = Real.exp (u*L) → V = Real.exp (v*L) →
      X = Real.exp (x*L) → L^2 ≤ ε * U →
      (∀ N : ℕ, U ≤ (N:ℝ) → (N:ℝ) ≤ V →
        (∑ n ∈ Finset.Icc 1 N, (∑ d ∈ n.divisors, Work.LinnikAreas.Density4.psiM U V d)^2)
          ≤ (1+ε) * (N:ℝ) * Real.log ((N:ℝ)/U) / (Real.log (V/U))^2
              + C₁ * (N:ℝ) / (Real.log (V/U))^2) →
      (∀ N : ℕ, V ≤ (N:ℝ) →
        (∑ n ∈ Finset.Icc 1 N, (∑ d ∈ n.divisors, Work.LinnikAreas.Density4.psiM U V d)^2)
          ≤ (1+ε) * (N:ℝ) / Real.log (V/U) + C₁ * (N:ℝ) / (Real.log (V/U))^2) →
      (∑' n : ℕ, (∑ d ∈ n.divisors, Work.LinnikAreas.Density4.psiM U V d)^2 * (n:ℝ)⁻¹ *
          (Real.exp (-(n:ℝ)/X) - Real.exp (-(n:ℝ)*L^2/U)))
        ≤ (1+ε) * ((2*x-u-v)/(2*(v-u))) + C₂ / L

/-- `wHB lam ≤ 1` for `lam ≥ 0`. -/
lemma wHB_le_one {lam : ℝ} (hlam : 0 ≤ lam) : Work.LinnikContract2.wHB lam ≤ 1 := by
  rw [Work.LinnikContract2.wHB]
  rcases eq_or_lt_of_le hlam with h0 | hpos
  · rw [← h0]; norm_num
  · have hden : 0 < Real.exp (73/30*lam) - Real.exp (16/15*lam) := by
      have h1 : (16/15:ℝ) * lam < (73/30) * lam := by nlinarith
      linarith [Real.exp_lt_exp.mpr h1]
    rw [div_le_one hden]
    have h3 : Real.exp (73/30*lam) - Real.exp (16/15*lam)
        = Real.exp (16/15*lam) * (Real.exp ((73/30-16/15)*lam) - 1) := by
      rw [mul_sub, mul_one, ← Real.exp_add]
      congr 1
      ring
    have h5 : (73/30-16/15:ℝ) * lam = (41/30) * lam := by ring
    have hexp : (41/30) * lam ≤ Real.exp ((41/30)*lam) - 1 := by
      have := Real.add_one_le_exp ((41/30)*lam)
      linarith
    have h6 : (1:ℝ) ≤ Real.exp (16/15*lam) := Real.one_le_exp (by positivity)
    have h7 : lam ≤ (41/30:ℝ) * lam := by nlinarith
    rw [h3, h5]
    have h8 : (41/30:ℝ) * lam ≤ Real.exp (16/15*lam) * (Real.exp ((41/30)*lam) - 1) := by
      calc (41/30:ℝ) * lam ≤ 1 * (Real.exp ((41/30)*lam) - 1) := by
            rw [one_mul]; exact hexp
        _ ≤ Real.exp (16/15*lam) * (Real.exp ((41/30)*lam) - 1) :=
            mul_le_mul_of_nonneg_right h6 (by linarith)
    linarith

/-! ## 6. Instantiating the two analytic inputs at the contract's parameters -/

/-- `(e^{aL})^{2-2β} = e^{(2a)(1-β)L}`. -/
lemma rpow_exp_eq (a L β : ℝ) : (Real.exp (a*L))^(2-2*β) = Real.exp ((2*a)*((1-β)*L)) := by
  rw [Real.rpow_def_of_pos (Real.exp_pos _), Real.log_exp]
  congr 1
  ring

/-- The `ψ`-coefficient family is the `ψ`-mollifier family of HB (11.12) in the `psiSq`/`wt`
normalisation of `psi_weighted_eval`. -/
lemma norm_bcoef_sq_eq {q : ℕ} [NeZero q] (u v x : ℝ) (n : ℕ) (hwt : 0 ≤ WT q u x n) :
    ‖bcoef q u v x n‖^2
      = Work.LinnikAreas2.psiSq ((q:ℝ)^u) ((q:ℝ)^v) n * (n:ℝ)⁻¹
        * Work.LinnikAreas2.wt (Real.log q) ((q:ℝ)^u) ((q:ℝ)^x) n := by
  rcases Nat.eq_zero_or_pos n with hn | hn
  · subst hn
    rw [bcoef_zero]
    simp [Work.LinnikAreas2.psiSq, Work.LinnikAreas.Density4.psiM]
  · have hnpos : (0:ℝ) < (n:ℝ) := by exact_mod_cast hn
    have h1 : ‖((Work.LinnikAreas.Density4.psiS ((q:ℝ)^u) ((q:ℝ)^v) n : ℝ) : ℂ)‖ = |Work.LinnikAreas.Density4.psiS ((q:ℝ)^u) ((q:ℝ)^v) n| := by
      rw [Complex.norm_real, Real.norm_eq_abs]
    have h2 : ‖((Real.sqrt (WT q u x n) : ℝ) : ℂ)‖ = Real.sqrt (WT q u x n) := by
      rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (Real.sqrt_nonneg _)]
    have h3 : ‖(n:ℂ)^(-(1/2:ℂ))‖^2 = (n:ℝ)⁻¹ := by
      rw [Complex.norm_natCast_cpow_of_pos hn]
      rw [show (-(1/2:ℂ)).re = (-(1/2:ℝ)) by simp]
      rw [pow_two, ← Real.rpow_add (by positivity)]
      norm_num
      rw [Real.rpow_neg_one]
    have hb : ‖bcoef q u v x n‖ = |Work.LinnikAreas.Density4.psiS ((q:ℝ)^u) ((q:ℝ)^v) n|
        * ‖(n:ℂ)^(-(1/2:ℂ))‖ * Real.sqrt (WT q u x n) := by
      simp only [bcoef, norm_mul, h1, h2]
    rw [hb, mul_pow, mul_pow, h3]
    have h4 : |Work.LinnikAreas.Density4.psiS ((q:ℝ)^u) ((q:ℝ)^v) n|^2
        = Work.LinnikAreas2.psiSq ((q:ℝ)^u) ((q:ℝ)^v) n := by
      rw [Work.LinnikAreas2.psiSq, Work.LinnikAreas.Density4.psiS, sq_abs]
    rw [h4, Real.sq_sqrt hwt]


/-- `(e^a)^b = e^{ab}`. -/
lemma exp_rpow (a b : ℝ) : (Real.exp a) ^ b = Real.exp (a*b) := by
  rw [Real.rpow_def_of_pos (Real.exp_pos a), Real.log_exp]

/-- **The `θ`-side of the `(D1)` assembly**: given Graham's `θ`-sieve estimate and the sharp
(subtracted) HB (11.17), the diagonal hypothesis `ThetaBound δ` of the assembly holds. -/
theorem thetaBound_of_sharp (hgraham : GrahamTheta) (hsharp : ThetaSharp) :
    ∀ δ : ℝ, 0 < δ → δ < 1/10 → ThetaBound δ := by
  intro δ hδ0 hδ10 c1 hc1
  obtain ⟨C₁, hC₁pos, hG⟩ := hgraham (c1/4) (by linarith)
  obtain ⟨L₀, C₂, hL₀pos, hC₂pos, hmain⟩ :=
    hsharp (c1/2) (by linarith) (8/15) (1/10-δ) (73/60) (by linarith) (by linarith)
      (by norm_num) C₁ hC₁pos
  obtain ⟨Q, hQ⟩ : ∃ Q : ℕ, 0 < Q ∧ ∀ q : ℕ, Q ≤ q →
      max L₀ (max (10*C₂/c1) 40) ≤ Real.log q := by
    refine ⟨⌈Real.exp (max L₀ (max (10*C₂/c1) 40))⌉₊ + 1, Nat.succ_pos _, fun q hq => ?_⟩
    rw [Real.le_log_iff_exp_le (by exact_mod_cast (by omega : 0 < q))]
    have h2 : ((⌈Real.exp (max L₀ (max (10*C₂/c1) 40))⌉₊ + 1 : ℕ) : ℝ) ≤ (q:ℝ) :=
      by exact_mod_cast hq
    have h3 : Real.exp (max L₀ (max (10*C₂/c1) 40))
        ≤ ((⌈Real.exp (max L₀ (max (10*C₂/c1) 40))⌉₊ : ℕ) : ℝ) := Nat.le_ceil _
    push_cast at h2
    linarith
  refine ⟨max 3 Q, fun q hq _ χ ρ hZ hlam => ?_⟩
  have hq3 : 3 ≤ q := le_trans (le_max_left _ _) hq
  have hqQ : Q ≤ q := le_trans (le_max_right _ _) hq
  have hqpos : (0:ℝ) < (q:ℝ) := Nat.cast_pos.mpr (NeZero.pos q)
  have hLlarge : max L₀ (max (10*C₂/c1) 40) ≤ Real.log q := hQ.2 q hqQ
  have hL₀ : L₀ ≤ Real.log q := le_trans (le_max_left _ _) hLlarge
  have hL5 : 10*C₂/c1 ≤ Real.log q :=
    le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) hLlarge
  have hL40 : 40 ≤ Real.log q :=
    le_trans (le_trans (le_max_right _ _) (le_max_right _ _)) hLlarge
  have hLpos : 0 < Real.log q := by linarith
  have hlamle : (1-ρ.re)*Real.log q ≤ Real.log (Real.log (Real.log q))/3 := by
    have h := hlam
    rw [Work.LinnikContract2.lamMax] at h
    exact h
  have hbetal : (1/2:ℝ) ≤ ρ.re := by
    have h2 : Real.log (Real.log (Real.log q))/3 ≤ Real.log q/2 := by
      have ht1 : (1:ℝ) ≤ Real.log q := by linarith
      have hlt : Real.log (Real.log (Real.log q)) ≤ Real.log q := by
        have h3 : Real.log (Real.log (Real.log q)) ≤ Real.log (Real.log q) - 1 :=
          Real.log_le_sub_one_of_pos (Real.log_pos (by linarith : (1:ℝ) < Real.log q))
        have h4 : Real.log (Real.log q) ≤ Real.log q := Real.log_le_self (by linarith)
        linarith
      linarith
    have h3 : (1-ρ.re)*Real.log q ≤ (1/2)*Real.log q := by linarith
    have h4 : (1-ρ.re) ≤ 1/2 := (mul_le_mul_iff_of_pos_right hLpos).mp h3
    linarith
  have hbetalt : ρ.re < 1 := by
    by_contra hcon
    push_neg at hcon
    have hz : DirichletCharacter.LFunction χ ρ = 0 := isZ_LFunction_zero hZ
    exact (DirichletCharacter.LFunction_ne_zero_of_one_le_re (χ := χ) (s := ρ)
      (Or.inl hZ.1) hcon) hz
  -- Graham's `θ` bounds, rewritten in the sharp lemma's normalisation
  have hG' := hG (1/10-δ) (Real.log q) (by linarith) hLpos
  rw [Real.log_exp] at hG'
  have h1' : ∀ N : ℕ, 1 ≤ N → (N:ℝ) ≤ Real.exp ((1/10-δ)*Real.log q) →
      (∑ n ∈ Finset.Icc 1 N, (∑ d ∈ n.divisors,
        Work.LinnikAreas.Density4.thetaM (Real.exp ((1/10-δ)*Real.log q)) d)^2)
        ≤ 1 + (1+(c1/2)/2)*(N:ℝ)*Real.log N/((1/10-δ)*Real.log q)^2
          + C₁*(N:ℝ)/((1/10-δ)*Real.log q)^2 := by
    intro N hN hNW
    have h := hG'.1 N hN hNW
    convert h using 3 <;> ring
  have h2' : ∀ N : ℕ, Real.exp ((1/10-δ)*Real.log q) ≤ (N:ℝ) →
      (∑ n ∈ Finset.Icc 1 N, (∑ d ∈ n.divisors,
        Work.LinnikAreas.Density4.thetaM (Real.exp ((1/10-δ)*Real.log q)) d)^2)
        ≤ 1 + (1+(c1/2)/2)*(N:ℝ)/((1/10-δ)*Real.log q)
          + C₁*(N:ℝ)/((1/10-δ)*Real.log q)^2 := by
    intro N hNW
    have h := hG'.2 N hNW
    convert h using 3 <;> ring
  have hconcl := hmain (Real.log q) ρ.re hL₀ hbetal hbetalt hlamle h1' h2'
  -- rewrite the goal into the sharp lemma's vocabulary
  have hqW : (q:ℝ)^(1/10-δ) = Real.exp ((1/10-δ)*Real.log q) := by
    rw [Real.rpow_def_of_pos hqpos]; congr 1; ring
  have hqU : (q:ℝ)^((8:ℝ)/15) = Real.exp ((8/15)*Real.log q) :=
    (Real.rpow_def_of_pos hqpos (8/15)).trans (by congr 1; ring)
  have hqX : (q:ℝ)^((73:ℝ)/60) = Real.exp ((73/60)*Real.log q) :=
    (Real.rpow_def_of_pos hqpos (73/60)).trans (by congr 1; ring)
  have hwt_eq : ∀ n : ℕ, WT q (8/15) (73/60) n
      = Real.exp (-(n:ℝ)/Real.exp ((73/60)*Real.log q))
        - Real.exp (-(n:ℝ)*(Real.log q)^2/Real.exp ((8/15)*Real.log q)) := by
    intro n
    rw [WT, wt, hqU, hqX]
  rw [hqW]
  rw [show (∑' n : ℕ, (∑ d ∈ n.divisors, Work.LinnikAreas.Density4.thetaM
        (Real.exp ((1/10-δ)*Real.log q)) d)^2 * (n:ℝ)^(1-2*ρ.re) * WT q (8/15) (73/60) n)
      = (∑' n : ℕ, (∑ d ∈ n.divisors, Work.LinnikAreas.Density4.thetaM
        (Real.exp ((1/10-δ)*Real.log q)) d)^2 * (n:ℝ)^(1-2*ρ.re)
          * (Real.exp (-(n:ℝ)/Real.exp ((73/60)*Real.log q))
            - Real.exp (-(n:ℝ)*(Real.log q)^2/Real.exp ((8/15)*Real.log q))))
      from tsum_congr (fun n => by rw [hwt_eq n])]
  -- the weight is positive and the cancellation `wHB lam · (e^{2xλ}-e^{2uλ})/λ = 1`
  set E1 : ℝ := (Real.exp ((73/60)*Real.log q))^(2-2*ρ.re) with hE1
  set E2 : ℝ := (Real.exp ((8/15)*Real.log q))^(2-2*ρ.re) with hE2
  have hlampo : 0 < (1-ρ.re)*Real.log q := by nlinarith
  have hlamne : (1-ρ.re)*Real.log q ≠ 0 := ne_of_gt hlampo
  have hden : Real.exp (73/30*((1-ρ.re)*Real.log q)) - Real.exp (16/15*((1-ρ.re)*Real.log q)) ≠ 0 := by
    have h1 : (16/15:ℝ) * ((1-ρ.re)*Real.log q) < (73/30) * ((1-ρ.re)*Real.log q) := by
      nlinarith
    linarith [Real.exp_lt_exp.mpr h1]
  have hA : E1 = Real.exp (73/30*((1-ρ.re)*Real.log q)) := by
    rw [hE1, exp_rpow]; congr 1; ring
  have hB : E2 = Real.exp (16/15*((1-ρ.re)*Real.log q)) := by
    rw [hE2, exp_rpow]; congr 1; ring
  have hcancel : Work.LinnikContract2.wHB ((1-ρ.re)*Real.log q)
      * (E1 - E2) / ((1-ρ.re)*Real.log q) = 1 := by
    rw [hA, hB, Work.LinnikContract2.wHB, div_eq_one_iff_eq hlamne]
    exact div_mul_cancel₀ _ hden
  have hwc_eq : 2*(1/10-δ)*Work.LinnikContract2.wHB (Work.LinnikContract2.lamOf q ρ)
      = 2*(1/10-δ)*Work.LinnikContract2.wHB ((1-ρ.re)*Real.log q) := by
    rw [Work.LinnikContract2.lamOf]
  rw [hwc_eq]
  have hwcpos : 0 ≤ 2*(1/10-δ)*Work.LinnikContract2.wHB ((1-ρ.re)*Real.log q) :=
    mul_nonneg (by linarith) (wHB_nonneg _)
  have hLne : Real.log q ≠ 0 := ne_of_gt hLpos
  have h1rne : (1-ρ.re) ≠ 0 := by
    intro h0
    rw [h0, zero_mul] at hlampo
    exact absurd hlampo (lt_irrefl 0)
  have h2wne : (2*(1/10-δ)) ≠ 0 := by linarith
  have h10δ : (1 - 10*δ) ≠ 0 := by linarith
  calc 2*(1/10-δ)*Work.LinnikContract2.wHB ((1-ρ.re)*Real.log q)
        * (∑' n : ℕ, (∑ d ∈ n.divisors, Work.LinnikAreas.Density4.thetaM
            (Real.exp ((1/10-δ)*Real.log q)) d)^2 * (n:ℝ)^(1-2*ρ.re)
            * (Real.exp (-(n:ℝ)/Real.exp ((73/60)*Real.log q))
              - Real.exp (-(n:ℝ)*(Real.log q)^2/Real.exp ((8/15)*Real.log q))))
      ≤ 2*(1/10-δ)*Work.LinnikContract2.wHB ((1-ρ.re)*Real.log q)
          * ((1+c1/2) * (E1 - E2)/(2*(1/10-δ)*(1-ρ.re)*Real.log q) + C₂/Real.log q) :=
        mul_le_mul_of_nonneg_left hconcl hwcpos
    _ = 2*(1/10-δ)*Work.LinnikContract2.wHB ((1-ρ.re)*Real.log q)
          * ((1+c1/2) * (E1 - E2)/(2*(1/10-δ)*(1-ρ.re)*Real.log q))
        + 2*(1/10-δ)*Work.LinnikContract2.wHB ((1-ρ.re)*Real.log q) * (C₂/Real.log q) := by
        rw [mul_add]
    _ = (1+c1/2) * (Work.LinnikContract2.wHB ((1-ρ.re)*Real.log q) * (E1 - E2)
          / ((1-ρ.re)*Real.log q))
        + 2*(1/10-δ)*Work.LinnikContract2.wHB ((1-ρ.re)*Real.log q) * (C₂/Real.log q) := by
        field_simp
    _ = (1+c1/2) + 2*(1/10-δ)*Work.LinnikContract2.wHB ((1-ρ.re)*Real.log q)
          * (C₂/Real.log q) := by rw [hcancel]; ring
    _ ≤ (1+c1/2) + C₂/Real.log q := by
        have hwb : Work.LinnikContract2.wHB ((1-ρ.re)*Real.log q) ≤ 1 :=
          wHB_le_one hlampo.le
        have hwb0 : 0 ≤ Work.LinnikContract2.wHB ((1-ρ.re)*Real.log q) := wHB_nonneg _
        have h2w : 2*(1/10-δ) ≤ 1 := by linarith
        have h2w0 : 0 ≤ 2*(1/10-δ) := by linarith
        have hC₂div : 0 ≤ C₂/Real.log q := div_nonneg hC₂pos.le hLpos.le
        have hprod : (2*(1/10-δ)) * Work.LinnikContract2.wHB ((1-ρ.re)*Real.log q) ≤ 1 := by
          nlinarith [hwb, hwb0, h2w, h2w0]
        have : (2*(1/10-δ)*Work.LinnikContract2.wHB ((1-ρ.re)*Real.log q))
            * (C₂/Real.log q) ≤ 1 * (C₂/Real.log q) :=
          mul_le_mul_of_nonneg_right hprod hC₂div
        linarith
    _ ≤ 1 + c1 := by
        have h10 : 10*C₂ ≤ c1 * Real.log q := by
          have := hL5
          rw [div_le_iff₀ hc1] at this
          linarith [this]
        have : C₂/Real.log q ≤ c1/2 := by
          rw [div_le_iff₀ hLpos]
          nlinarith [h10]
        linarith


/-- **The `ψ`-side of the `(D1)` assembly**: given Graham's `ψ`-sieve estimate and HB (11.14) with
a general constant, the norm bound `PsiBound ε` of the assembly holds. -/
theorem psiBound_of_graham (hgraham : GrahamPsiSieve) (hgen : PsiWeightedGen) :
    ∀ ε : ℝ, 0 < ε → PsiBound ε := by
  intro ε hε
  obtain ⟨C₁, hC₁pos, hG⟩ := hgraham (ε/2) (by linarith) (8/15) (47/60)
    (by norm_num) (by norm_num)
  obtain ⟨C₂, hC₂pos, hmain⟩ := hgen (ε/2) (by linarith) (8/15) (47/60) (73/60)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) C₁ hC₁pos
  -- `(log x)² ≤ (ε/2) x^{8/15}` eventually
  have hbound : ∀ᶠ x : ℝ in Filter.atTop, (Real.log x)^2 ≤ (ε/2) * x^((8:ℝ)/15) := by
    filter_upwards [((isLittleO_log_rpow_atTop (show (0:ℝ) < 4/15 by norm_num)).bound
        (show (0:ℝ) < Real.sqrt (ε/2) by positivity)),
      Filter.eventually_ge_atTop (0:ℝ)] with x hx hx0
    rw [Real.norm_of_nonneg (Real.rpow_nonneg hx0 _)] at hx
    rw [Real.norm_eq_abs] at hx
    have h1 : (Real.log x)^(2:ℕ) ≤ (Real.sqrt (ε/2) * x^((4:ℝ)/15))^(2:ℕ) := by
      rw [← sq_abs (Real.log x)]
      exact pow_le_pow_left₀ (abs_nonneg _) hx 2
    have h2 : (x^((4:ℝ)/15))^(2:ℕ) = x^((8:ℝ)/15) := by
      rw [← Real.rpow_natCast (x^((4:ℝ)/15)) 2, ← Real.rpow_mul hx0]
      norm_num
    rw [mul_pow, Real.sq_sqrt (by positivity), h2] at h1
    exact h1
  obtain ⟨a, ha⟩ := Filter.eventually_atTop.mp hbound
  refine ⟨max 3 (max (⌈max a 1⌉₊ + 1) (⌈Real.exp (60*C₂/(67*ε))⌉₊ + 1)),
    fun q hq _ => ?_⟩
  have hq3 : 3 ≤ q := le_trans (le_max_left _ _) hq
  have hqA : ⌈max a 1⌉₊ + 1 ≤ q :=
    le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) hq
  have hqB : ⌈Real.exp (60*C₂/(67*ε))⌉₊ + 1 ≤ q :=
    le_trans (le_trans (le_max_right _ _) (le_max_right _ _)) hq
  have hqpos : (0:ℝ) < (q:ℝ) := Nat.cast_pos.mpr (NeZero.pos q)
  have hLpos : 0 < Real.log q := Real.log_pos (by exact_mod_cast (by omega : 1 < q))
  have hAa : a ≤ (q:ℝ) := by
    have h1 : ⌈max a 1⌉₊ ≤ q := by omega
    have h2 : max a 1 ≤ ((⌈max a 1⌉₊ : ℕ) : ℝ) := Nat.le_ceil (max a 1)
    have h3 : ((⌈max a 1⌉₊ : ℕ) : ℝ) ≤ (q:ℝ) := by exact_mod_cast h1
    linarith [le_max_left a 1]
  have hLs : (Real.log q)^2 ≤ (ε/2) * (q:ℝ)^((8:ℝ)/15) := ha (q:ℝ) hAa
  -- the `ψ`-side estimate
  have hVe : (q:ℝ)^((47:ℝ)/60) = Real.exp ((47/60)*Real.log q) :=
    (Real.rpow_def_of_pos hqpos (47/60)).trans (by congr 1; ring)
  have hXe : (q:ℝ)^((73:ℝ)/60) = Real.exp ((73/60)*Real.log q) :=
    (Real.rpow_def_of_pos hqpos (73/60)).trans (by congr 1; ring)
  have hUe : (q:ℝ)^((8:ℝ)/15) = Real.exp ((8/15)*Real.log q) :=
    (Real.rpow_def_of_pos hqpos (8/15)).trans (by congr 1; ring)
  have hU : (1:ℝ) ≤ (q:ℝ)^((8:ℝ)/15) :=
    Real.one_le_rpow (by exact_mod_cast (by omega : 1 ≤ q)) (by norm_num)
  have hG' := hG (Real.log q) ((q:ℝ)^((8:ℝ)/15)) ((q:ℝ)^((47:ℝ)/60)) hLpos hUe hVe
  have hconcl := hmain (Real.log q) ((q:ℝ)^((8:ℝ)/15)) ((q:ℝ)^((47:ℝ)/60))
    ((q:ℝ)^((73:ℝ)/60)) hLpos hU hUe hVe hXe hLs hG'.1 hG'.2
  rw [show (2*(73/60)-8/15-47/60)/(2*(47/60-8/15)) = (67/30 : ℝ) by norm_num] at hconcl
  -- identify the `b`-family
  have hbq : ∀ n : ℕ, ‖bcoef q (8/15) (47/60) (73/60) n‖^2
      = Work.LinnikAreas2.psiSq ((q:ℝ)^((8:ℝ)/15)) ((q:ℝ)^((47:ℝ)/60)) n * (n:ℝ)⁻¹
        * Work.LinnikAreas2.wt (Real.log q) ((q:ℝ)^((8:ℝ)/15)) ((q:ℝ)^((73:ℝ)/60)) n := by
    intro n
    rw [norm_bcoef_sq_eq (q := q) (8/15) (47/60) (73/60) n (WT_nonneg hq3 n)]
  rw [tsum_congr hbq]
  have hconcl' : (∑' n : ℕ, Work.LinnikAreas2.psiSq ((q:ℝ)^((8:ℝ)/15))
        ((q:ℝ)^((47:ℝ)/60)) n * (n:ℝ)⁻¹
        * Work.LinnikAreas2.wt (Real.log q) ((q:ℝ)^((8:ℝ)/15)) ((q:ℝ)^((73:ℝ)/60)) n)
      ≤ (1+ε/2)*(67/30) + C₂/Real.log q := by
    simpa only [Work.LinnikAreas2.psiSq, Work.LinnikAreas2.wt] using hconcl
  refine le_trans hconcl' ?_
  have hlast : C₂/Real.log q ≤ (ε/2)*(67/30) := by
    rw [div_le_iff₀ hLpos]
    have h2 : ((⌈Real.exp (60*C₂/(67*ε))⌉₊ + 1 : ℕ) : ℝ) ≤ (q:ℝ) := by exact_mod_cast hqB
    have h3 : Real.exp (60*C₂/(67*ε)) ≤ ((⌈Real.exp (60*C₂/(67*ε))⌉₊ : ℕ) : ℝ) :=
      Nat.le_ceil _
    have h4 : 60*C₂/(67*ε) ≤ Real.log q := by
      rw [Real.le_log_iff_exp_le (by positivity)]
      push_cast at h2
      linarith
    have h4' : 60*C₂ ≤ 67*ε*Real.log q := by
      have := (div_le_iff₀ (by positivity : (0:ℝ) < 67*ε)).mp h4
      linarith [this]
    nlinarith [h4']
  linarith [hconcl', hlast]


/-! ## 4. The assembly of `(D1)` -/

/-- **HB Lemma 11.1 (`(D1)`) from its two analytic inputs.** -/
theorem d1_of_pieces (h1 : Work.LinnikContract2.Area1)
    (hpsi : ∀ ε : ℝ, 0 < ε → PsiBound ε)
    (htheta : ∀ δ : ℝ, 0 < δ → δ < 1/10 → ThetaBound δ) :
    Work.LinnikContract2.D1 := by
  intro ε hε
  -- the parameters of HB §11
  set a : ℝ := min (ε/10^4) (1/1000) with ha
  set δ : ℝ := min (ε/10^6) (1/1000) with hδ
  have ha0 : 0 < a := by rw [ha]; exact lt_min (by positivity) (by norm_num)
  have hδ0 : 0 < δ := by rw [hδ]; exact lt_min (by positivity) (by norm_num)
  have hδ10 : δ < 1/10 := by
    have h' : δ ≤ 1/1000 := hδ.le.trans (min_le_right _ _)
    linarith
  have ha_le1 : a ≤ ε/10^4 := ha.le.trans (min_le_left _ _)
  have ha_le2 : a ≤ 1/1000 := ha.le.trans (min_le_right _ _)
  have hδ_le : δ ≤ ε/10^6 := hδ.le.trans (min_le_left _ _)
  have hδ_le2 : δ ≤ 1/1000 := hδ.le.trans (min_le_right _ _)
  obtain ⟨qpsi, hqpsi⟩ := hpsi a ha0
  obtain ⟨qthe, hqthe⟩ := htheta δ hδ0 hδ10 a ha0
  obtain ⟨Cd, hCdpos, hCd⟩ := zero_detector h1 (8/15) (47/60) (1/10-δ) (73/60)
    (by linarith) (by linarith) (by norm_num) (by norm_num) (by linarith) (by linarith)
  obtain ⟨Cf, hCfpos, hCf⟩ := hb11_offdiag_pair_bound h1 (8/15) (1/10-δ) (73/60)
    (by linarith) (by linarith) (by norm_num) (by linarith)
  set M : ℝ := 2*Cd + Cf*(1+a)*(67/30) with hM
  have hMpos : 0 < M := by rw [hM]; positivity
  have hMge : 2*Cd ≤ M := by rw [hM]; nlinarith [hCfpos, hCdpos, ha0]
  refine ⟨max (max qpsi qthe) (max 3 (⌈Real.exp (2*M/a)⌉₊ + 1)), fun q hq _ => ?_⟩
  have hq3 : 3 ≤ q := le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) hq
  have hqpsi_le : qpsi ≤ q := le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) hq
  have hqthe_le : qthe ≤ q := le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) hq
  have hqexp : ⌈Real.exp (2*M/a)⌉₊ + 1 ≤ q :=
    le_trans (le_trans (le_max_right _ _) (le_max_right _ _)) hq
  have hq2 : 2 ≤ q := by omega
  have hLpos : 0 < Real.log q := by
    apply Real.log_pos
    have : (3:ℝ) ≤ (q:ℝ) := by exact_mod_cast hq3
    linarith
  have hlog_large : 2*M ≤ a * Real.log q := by
    have h1 : 2*M/a ≤ Real.log q := by
      rw [Real.le_log_iff_exp_le (by positivity)]
      have h2 : ((⌈Real.exp (2*M/a)⌉₊ + 1 : ℕ) : ℝ) ≤ (q:ℝ) := by exact_mod_cast hqexp
      have h3 : Real.exp (2*M/a) ≤ ((⌈Real.exp (2*M/a)⌉₊ : ℕ) : ℝ) := Nat.le_ceil _
      push_cast at h2
      linarith
    rw [div_le_iff₀ ha0] at h1
    linarith [h1]
  have hCdL : Cd / Real.log q ≤ 1 := by
    rw [div_le_one hLpos]
    have hCa : Cd * a ≤ M := by nlinarith [hMge, ha_le2, ha0, hCdpos]
    have h2 : a * (2*Cd) ≤ a * Real.log q := by nlinarith [hlog_large, hCa]
    have h3 : 2*Cd ≤ Real.log q := (mul_le_mul_iff_of_pos_left ha0).mp h2
    linarith
  -- the character set, enumerated by minimising zeros
  obtain ⟨chi, rho, hchi_inj, hchi_mem, hchiZ, hrho_lam⟩ :=
    exists_enum_min (q := q) (hbSet q) (fun χ hχ => by
      obtain ⟨ρ, hZ, -⟩ := mem_hbSet.mp hχ
      exact ⟨ρ, hZ⟩)
  have hrho_le : ∀ j, Work.LinnikContract2.lamOf q (rho j) ≤ Work.LinnikContract2.lamMax q := by
    intro j
    obtain ⟨ρ', hZ', hle'⟩ := mem_hbSet.mp (hchi_mem j)
    rw [hrho_lam j]
    exact le_trans (lamChar_le_of_isZ hq2 hZ') hle'
  -- the weights
  have hw'pos : (0:ℝ) < 1/10 - δ := by linarith
  set wc : Fin (hbSet q).card → ℝ :=
    fun j => 2*(1/10-δ)*Work.LinnikContract2.wHB (Work.LinnikContract2.lamOf q (rho j)) with hwc
  have hwc_nonneg : ∀ j, 0 ≤ wc j := by
    intro j; rw [hwc]
    exact mul_nonneg (mul_nonneg (by norm_num) hw'pos.le) (wHB_nonneg _)
  have hwt : ∀ n : ℕ, 0 ≤ WT q (8/15) (73/60) n := WT_nonneg hq3
  -- the diagonal (HB (11.17), sharp) and the off-diagonal (HB (11.16))
  have hdiag : ∀ j : Fin (hbSet q).card, wc j * (∑' n : ℕ,
      ((∑ d ∈ n.divisors, thetaM ((q:ℝ)^(1/10-δ)) d : ℝ))^2
        * (n:ℝ)^(1 - 2*(rho j).re) * WT q (8/15) (73/60) n) ≤ 1 + a := by
    intro j
    have hth := hqthe q hqthe_le (chi j) (rho j) (hchiZ j) (hrho_le j)
    rw [hwc]
    exact hth
  have hoff : ∀ j k : Fin (hbSet q).card, j ≠ k → ‖∑' n : ℕ,
      ((((∑ d ∈ n.divisors, thetaM ((q:ℝ)^(1/10-δ)) d : ℝ)) : ℂ))^2
        * ((chi j * (chi k)⁻¹) (n : ZMod q))
        * ((n : ℂ) ^ ((1 : ℂ) - rho j - (starRingEnd ℂ (rho k))))
        * (((WT q (8/15) (73/60) n : ℝ)) : ℂ)‖ ≤ Cf / Real.log q := by
    intro j k hjk
    have hne : chi j ≠ chi k := fun h => hjk (hchi_inj h)
    have h1 := hCf q hq2 (chi j) (chi k) (chi_mul_inv_ne_one hne) (rho j) (rho k)
      (hchiZ j) (hrho_le j) (hchiZ k) (hrho_le k)
    have heq : ∀ n : ℕ,
        ((((∑ d ∈ n.divisors, thetaM ((q:ℝ)^(1/10-δ)) d : ℝ)) : ℂ))^2
          * ((chi j * (chi k)⁻¹) (n : ZMod q))
          * ((n : ℂ) ^ ((1 : ℂ) - rho j - (starRingEnd ℂ (rho k))))
          * (((WT q (8/15) (73/60) n : ℝ)) : ℂ)
        = ((((∑ d ∈ n.divisors, thetaM ((q:ℝ)^(1/10-δ)) d : ℝ)) : ℂ))^2
          * ((chi j (n : ZMod q)) * (starRingEnd ℂ) (chi k (n : ZMod q)))
          * ((n : ℂ) ^ ((1 : ℂ) - rho j - (starRingEnd ℂ (rho k))))
          * (((Real.exp (-(n:ℝ)/(q:ℝ)^((73:ℝ)/60))
              - Real.exp (-(n:ℝ)*(Real.log q)^2/(q:ℝ)^((8:ℝ)/15)) : ℝ)) : ℂ) := by
      intro n
      rw [chi_mul_inv_apply, WT, wt]
    rw [tsum_congr heq]
    exact h1
  -- the operator bound of HB (11.15) and the duality principle
  set B : ℝ := (1 + a) + (Cf / Real.log q) * (∑ j : Fin (hbSet q).card, wc j) with hB
  have hTnn : 0 ≤ ∑ j : Fin (hbSet q).card, wc j := Finset.sum_nonneg (fun j _ => hwc_nonneg j)
  have hBnn : 0 ≤ B := by rw [hB]; positivity
  have hsumm_acoef : ∀ j : Fin (hbSet q).card,
      Summable (fun n : ℕ => ‖acoef q (8/15) (1/10-δ) (73/60) (chi j) (rho j) (wc j) n‖^2) := by
    intro j
    have h2 := acoef_pair_summable (q := q) (u := 8/15) (w := 1/10-δ) (x := 73/60)
      (chi j) (chi j) (rho j) (rho j) (wc j) (wc j)
    refine h2.norm.congr (fun n => ?_)
    rw [norm_mul, Complex.norm_conj, ← pow_two]
  have hop : ∀ C : Fin (hbSet q).card → ℂ,
      Summable (fun n : ℕ => ‖∑ j : Fin (hbSet q).card,
          acoef q (8/15) (1/10-δ) (73/60) (chi j) (rho j) (wc j) n * C j‖^2) ∧
      (∑' n : ℕ, ‖∑ j : Fin (hbSet q).card,
          acoef q (8/15) (1/10-δ) (73/60) (chi j) (rho j) (wc j) n * C j‖^2)
        ≤ B * ∑ j : Fin (hbSet q).card, ‖C j‖^2 := by
    intro C
    constructor
    · refine Summable.of_norm_bounded (g := fun n : ℕ =>
          (∑ j : Fin (hbSet q).card, ‖C j‖^2) *
            (∑ j : Fin (hbSet q).card,
              ‖acoef q (8/15) (1/10-δ) (73/60) (chi j) (rho j) (wc j) n‖^2)) ?_ ?_
      · have hsum' : Summable (fun n : ℕ => ∑ j : Fin (hbSet q).card,
            ‖acoef q (8/15) (1/10-δ) (73/60) (chi j) (rho j) (wc j) n‖^2) := by
          have hfin : ∀ s : Finset (Fin (hbSet q).card), Summable (fun n : ℕ =>
              ∑ j ∈ s, ‖acoef q (8/15) (1/10-δ) (73/60) (chi j) (rho j) (wc j) n‖^2) := by
            intro s
            refine Finset.induction_on s ?_ ?_
            · simpa using summable_zero
            · intro x t hxt ih
              refine ((hsumm_acoef x).add ih).congr (fun n => ?_)
              exact (Finset.sum_insert (f := fun j => ‖acoef q (8/15) (1/10-δ) (73/60)
                (chi j) (rho j) (wc j) n‖^2) hxt).symm
          exact hfin Finset.univ
        exact hsum'.mul_left _
      · intro n
        have hcs : (∑ j : Fin (hbSet q).card,
              ‖acoef q (8/15) (1/10-δ) (73/60) (chi j) (rho j) (wc j) n‖ * ‖C j‖)^2
            ≤ (∑ j : Fin (hbSet q).card,
                ‖acoef q (8/15) (1/10-δ) (73/60) (chi j) (rho j) (wc j) n‖^2)
              * (∑ j : Fin (hbSet q).card, ‖C j‖^2) :=
          Finset.sum_mul_sq_le_sq_mul_sq _ _ _
        have h1 : ‖∑ j : Fin (hbSet q).card,
            acoef q (8/15) (1/10-δ) (73/60) (chi j) (rho j) (wc j) n * C j‖
            ≤ ∑ j : Fin (hbSet q).card,
              ‖acoef q (8/15) (1/10-δ) (73/60) (chi j) (rho j) (wc j) n‖ * ‖C j‖ := by
          calc ‖∑ j : Fin (hbSet q).card,
                acoef q (8/15) (1/10-δ) (73/60) (chi j) (rho j) (wc j) n * C j‖
              ≤ ∑ j : Fin (hbSet q).card,
                  ‖acoef q (8/15) (1/10-δ) (73/60) (chi j) (rho j) (wc j) n * C j‖ :=
                norm_sum_le _ _
            _ = ∑ j : Fin (hbSet q).card,
                  ‖acoef q (8/15) (1/10-δ) (73/60) (chi j) (rho j) (wc j) n‖ * ‖C j‖ := by
                simp only [norm_mul]
        have h3 : (0:ℝ) ≤ ∑ j : Fin (hbSet q).card,
            ‖acoef q (8/15) (1/10-δ) (73/60) (chi j) (rho j) (wc j) n‖ * ‖C j‖ :=
          Finset.sum_nonneg (fun j _ => by positivity)
        have hs : ‖∑ j : Fin (hbSet q).card,
            acoef q (8/15) (1/10-δ) (73/60) (chi j) (rho j) (wc j) n * C j‖^2
            ≤ (∑ j : Fin (hbSet q).card,
              ‖acoef q (8/15) (1/10-δ) (73/60) (chi j) (rho j) (wc j) n‖ * ‖C j‖)^2 :=
          pow_le_pow_left₀ (norm_nonneg _) h1 2
        rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
        calc ‖∑ j : Fin (hbSet q).card,
              acoef q (8/15) (1/10-δ) (73/60) (chi j) (rho j) (wc j) n * C j‖^2
            ≤ (∑ j : Fin (hbSet q).card,
              ‖acoef q (8/15) (1/10-δ) (73/60) (chi j) (rho j) (wc j) n‖ * ‖C j‖)^2 := hs
          _ ≤ (∑ j : Fin (hbSet q).card,
                ‖acoef q (8/15) (1/10-δ) (73/60) (chi j) (rho j) (wc j) n‖^2)
              * (∑ j : Fin (hbSet q).card, ‖C j‖^2) := hcs
          _ = (∑ j : Fin (hbSet q).card, ‖C j‖^2) *
                (∑ j : Fin (hbSet q).card,
                  ‖acoef q (8/15) (1/10-δ) (73/60) (chi j) (rho j) (wc j) n‖^2) := by ring
    · have hb := hb15_operator_bound (u := 8/15) (w := 1/10-δ) (x := 73/60)
        (chi := chi) (rho := rho) (wc := wc) (c1 := a) (c2 := Cf / Real.log q)
        hwc_nonneg (by positivity) hwt hdiag hoff C
      rw [hB]
      calc (∑' n : ℕ, ‖∑ j : Fin (hbSet q).card,
            acoef q (8/15) (1/10-δ) (73/60) (chi j) (rho j) (wc j) n * C j‖^2)
          ≤ (1 + a) * (∑ j : Fin (hbSet q).card, ‖C j‖^2)
            + (Cf / Real.log q) * (∑ j : Fin (hbSet q).card, wc j)
              * (∑ j : Fin (hbSet q).card, ‖C j‖^2) := hb
        _ = ((1 + a) + (Cf / Real.log q) * (∑ j : Fin (hbSet q).card, wc j))
              * (∑ j : Fin (hbSet q).card, ‖C j‖^2) := by ring
  -- sum of the squared norms of the `b`-family
  have hb_summable : Summable (fun n : ℕ => ‖bcoef q (8/15) (47/60) (73/60) n‖^2) :=
    summable_norm_bcoef_sq (q := q) (8/15) (47/60) (73/60)
  have hab_summable : ∀ j : Fin (hbSet q).card,
      Summable (fun n : ℕ => acoef q (8/15) (1/10-δ) (73/60) (chi j) (rho j) (wc j) n
        * bcoef q (8/15) (47/60) (73/60) n) := by
    intro j
    refine Summable.of_norm_bounded (g := fun n : ℕ => (1/2) *
        (‖acoef q (8/15) (1/10-δ) (73/60) (chi j) (rho j) (wc j) n‖^2
          + ‖bcoef q (8/15) (47/60) (73/60) n‖^2)) ?_ ?_
    · exact ((hsumm_acoef j).add hb_summable).mul_left (1/2)
    · intro n
      rw [norm_mul]
      have h := sq_nonneg (‖acoef q (8/15) (1/10-δ) (73/60) (chi j) (rho j) (wc j) n‖
        - ‖bcoef q (8/15) (47/60) (73/60) n‖)
      nlinarith [sq_nonneg (‖acoef q (8/15) (1/10-δ) (73/60) (chi j) (rho j) (wc j) n‖
        + ‖bcoef q (8/15) (47/60) (73/60) n‖)]
  have hduality := duality_tsum
    (A := fun n (j : Fin (hbSet q).card) =>
      acoef q (8/15) (1/10-δ) (73/60) (chi j) (rho j) (wc j) n) (B := B) hBnn hop
    (fun n => bcoef q (8/15) (47/60) (73/60) n) hb_summable hab_summable
  -- the detector: `w_j(1 - C/𝓛)² ≤ ‖Σ_n a_{nj} b_n‖²`
  have hdetector : ∀ j : Fin (hbSet q).card, wc j * (1 - Cd / Real.log q)^2
      ≤ ‖∑' n : ℕ, acoef q (8/15) (1/10-δ) (73/60) (chi j) (rho j) (wc j) n
          * bcoef q (8/15) (47/60) (73/60) n‖^2 := by
    intro j
    have hd := hCd q (chi j) (rho j) hq2 (hchiZ j) (hrho_le j)
    have hts := tsum_acoef_mul_bcoef q (8/15) (47/60) (1/10-δ) (73/60) (chi j) (rho j) (wc j) hwt
    have hnorm : ‖∑' n : ℕ, acoef q (8/15) (1/10-δ) (73/60) (chi j) (rho j) (wc j) n
          * bcoef q (8/15) (47/60) (73/60) n‖
        = Real.sqrt (wc j) * ‖detSum q ((q:ℝ)^((8:ℝ)/15)) ((q:ℝ)^((47:ℝ)/60))
            ((q:ℝ)^(1/10-δ)) ((q:ℝ)^((73:ℝ)/60)) (Real.log q) (chi j) (rho j)‖ := by
      rw [hts, norm_mul, Complex.norm_real, Real.norm_eq_abs,
        abs_of_nonneg (Real.sqrt_nonneg _)]
    rw [hnorm]
    have hsq : (Real.sqrt (wc j))^2 = wc j := Real.sq_sqrt (hwc_nonneg j)
    have h1 : Real.sqrt (wc j) * (1 - Cd / Real.log q)
        ≤ Real.sqrt (wc j) * ‖detSum q ((q:ℝ)^((8:ℝ)/15)) ((q:ℝ)^((47:ℝ)/60))
            ((q:ℝ)^(1/10-δ)) ((q:ℝ)^((73:ℝ)/60)) (Real.log q) (chi j) (rho j)‖ :=
      mul_le_mul_of_nonneg_left hd (Real.sqrt_nonneg _)
    have h2 : (Real.sqrt (wc j) * (1 - Cd / Real.log q))^2
        ≤ (Real.sqrt (wc j) * ‖detSum q ((q:ℝ)^((8:ℝ)/15)) ((q:ℝ)^((47:ℝ)/60))
            ((q:ℝ)^(1/10-δ)) ((q:ℝ)^((73:ℝ)/60)) (Real.log q) (chi j) (rho j)‖)^2 :=
      pow_le_pow_left₀ (mul_nonneg (Real.sqrt_nonneg _) (by linarith [hCdL])) h1 2
    rw [mul_pow, hsq]
    rw [mul_pow, mul_pow, hsq] at h2
    exact h2
  -- assemble
  have hmain : (1 - 2 * Cd / Real.log q) * (∑ j : Fin (hbSet q).card, wc j)
      ≤ ((1 + a) + (Cf / Real.log q) * (∑ j : Fin (hbSet q).card, wc j))
        * (∑' n : ℕ, ‖bcoef q (8/15) (47/60) (73/60) n‖^2) := by
    have h1 : (1 - 2 * Cd / Real.log q) * (∑ j : Fin (hbSet q).card, wc j)
        ≤ ∑ j : Fin (hbSet q).card, wc j * (1 - Cd / Real.log q)^2 := by
      rw [Finset.mul_sum]
      refine Finset.sum_le_sum (fun j _ => ?_)
      have hx : (1 - 2 * (Cd / Real.log q)) ≤ (1 - Cd / Real.log q)^2 := by
        nlinarith [sq_nonneg (Cd / Real.log q)]
      have hy : 1 - 2 * Cd / Real.log q = 1 - 2 * (Cd / Real.log q) := by ring
      rw [hy]
      calc (1 - 2 * (Cd / Real.log q)) * wc j ≤ (1 - Cd / Real.log q)^2 * wc j :=
            mul_le_mul_of_nonneg_right hx (hwc_nonneg j)
        _ = wc j * (1 - Cd / Real.log q)^2 := by ring
    have h2 : (∑ j : Fin (hbSet q).card, wc j * (1 - Cd / Real.log q)^2)
        ≤ ∑ j : Fin (hbSet q).card, ‖∑' n : ℕ,
            acoef q (8/15) (1/10-δ) (73/60) (chi j) (rho j) (wc j) n
              * bcoef q (8/15) (47/60) (73/60) n‖^2 :=
      Finset.sum_le_sum (fun j _ => hdetector j)
    exact le_trans h1 (le_trans h2 hduality)
  -- the weighted count
  have hB_le : (∑' n : ℕ, ‖bcoef q (8/15) (47/60) (73/60) n‖^2) ≤ (1 + a) * (67/30) :=
    hqpsi q hqpsi_le
  have hML : M / Real.log q ≤ a / 2 := by
    rw [div_le_iff₀ hLpos]
    nlinarith [hlog_large]
  have hWbound : (∑ j : Fin (hbSet q).card, wc j) ≤ (1 + 4*a) * (67/30) := by
    have h3 : ((1 + a) + (Cf / Real.log q) * (∑ j : Fin (hbSet q).card, wc j))
        * (∑' n : ℕ, ‖bcoef q (8/15) (47/60) (73/60) n‖^2)
        ≤ ((1 + a) + (Cf / Real.log q) * (∑ j : Fin (hbSet q).card, wc j))
          * ((1 + a) * (67/30)) :=
      mul_le_mul_of_nonneg_left hB_le hBnn
    have hexp : ((1 + a) + (Cf / Real.log q) * (∑ j : Fin (hbSet q).card, wc j))
          * ((1 + a) * (67/30))
        = (1 + a)^2 * (67/30)
          + (M / Real.log q) * (∑ j : Fin (hbSet q).card, wc j)
          - (2 * Cd / Real.log q) * (∑ j : Fin (hbSet q).card, wc j) := by
      rw [hM]; field_simp; ring
    have hstep : (1 - a/2) * (∑ j : Fin (hbSet q).card, wc j) ≤ (1 + a)^2 * (67/30) := by
      have h4 : (1 - 2 * Cd / Real.log q) * (∑ j : Fin (hbSet q).card, wc j)
          ≤ (1 + a)^2 * (67/30) + (M / Real.log q) * (∑ j : Fin (hbSet q).card, wc j)
            - (2 * Cd / Real.log q) * (∑ j : Fin (hbSet q).card, wc j) := by
        calc (1 - 2 * Cd / Real.log q) * (∑ j : Fin (hbSet q).card, wc j)
            ≤ ((1 + a) + (Cf / Real.log q) * (∑ j : Fin (hbSet q).card, wc j))
              * (∑' n : ℕ, ‖bcoef q (8/15) (47/60) (73/60) n‖^2) := hmain
          _ ≤ ((1 + a) + (Cf / Real.log q) * (∑ j : Fin (hbSet q).card, wc j))
              * ((1 + a) * (67/30)) := h3
          _ = (1 + a)^2 * (67/30) + (M / Real.log q) * (∑ j : Fin (hbSet q).card, wc j)
              - (2 * Cd / Real.log q) * (∑ j : Fin (hbSet q).card, wc j) := hexp
      nlinarith [h4, hML, hTnn]
    have ha4 : (1+a)^2 * (67/30) / (1 - a/2) ≤ (1 + 4*a) * (67/30) := by
      rw [div_le_iff₀ (by linarith : (0:ℝ) < 1 - a/2)]
      nlinarith [ha_le2, ha0, sq_nonneg a, sq_nonneg (1+a), sq_nonneg ((1+a)^2)]
    calc (∑ j : Fin (hbSet q).card, wc j)
        ≤ (1+a)^2 * (67/30) / (1 - a/2) := by
          rw [le_div_iff₀ (by linarith : (0:ℝ) < 1 - a/2)]
          linarith [hstep]
      _ ≤ (1 + 4*a) * (67/30) := ha4
  -- final bookkeeping (HB step (VI))
  have hfinal : (∑ χ ∈ hbSet q, Work.LinnikContract2.wHB (Work.LinnikContract2.lamChar χ))
      ≤ 67/6 + ε := by
    rw [← sum_fin_eq_sum_finset (hbSet q) hchi_inj hchi_mem
      (fun χ => Work.LinnikContract2.wHB (Work.LinnikContract2.lamChar χ))]
    have hcongr : ∀ j : Fin (hbSet q).card,
        Work.LinnikContract2.wHB (Work.LinnikContract2.lamChar (chi j))
          = wc j / (2*(1/10-δ)) := by
      intro j
      rw [← hrho_lam j, hwc,
        mul_div_cancel_left₀ _ (ne_of_gt (by linarith : (0:ℝ) < 2*(1/10-δ)))]
    rw [Finset.sum_congr rfl (fun j _ => hcongr j), ← Finset.sum_div]
    have h2w : (0:ℝ) < 2*(1/10-δ) := by linarith
    have harith : (1 + 4*a) * (67/30) / (2*(1/10-δ)) ≤ 67/6 + ε := by
      have h1 : (1 + 4*a) * (67/30) / (2*(1/10-δ)) = (67/6) * ((1+4*a) / (1-10*δ)) := by
        field_simp
        ring
      rw [h1]
      have hδsmall : (1+4*a) / (1 - 10*δ) ≤ 1 + 6*ε/67 := by
        rw [div_le_iff₀ (by linarith)]
        have h4 : (1+4*a) * (1+20*δ) ≤ 1 + 6*ε/67 := by
          by_cases hε1 : ε ≤ 1
          · nlinarith [ha_le1, hδ_le, hε, ha0, hδ0]
          · push_neg at hε1
            nlinarith [ha_le2, hδ_le2, hε1, ha0, hδ0]
        have h5 : (1:ℝ) ≤ (1+20*δ) * (1-10*δ) := by nlinarith [hδ_le2, hδ0]
        have h6 : (0:ℝ) ≤ 1 - 10*δ := by linarith
        nlinarith [h4, h5, h6, ha0, hδ0]
      calc (67/6 : ℝ) * ((1+4*a) / (1-10*δ))
          ≤ (67/6) * (1 + 6*ε/67) := mul_le_mul_of_nonneg_left hδsmall (by norm_num)
        _ = 67/6 + ε := by ring
    exact le_trans (div_le_div_of_nonneg_right hWbound h2w.le) harith
  exact hfinal


end Work.LinnikAreas2
