import Mathlib
import Submission.Work.ZeroDensity.Basic
import Submission.Work.LinnikAreas.Density4.Defs

/-!
# `Work.ZeroDensity.LogFree` — the unified log-free non-principal zero-density estimate

This is the vocabulary of `Submission/Work/ZeroDensity/JUTILA_UNIFIED_LEAD.md` §3: the single
log-free estimate

`logFreeNP σ₀ c  :=  ∃ C > 0, ∀ q ≥ 2, σ ∈ [σ₀,1], T ≥ 1,  Σ'_{χ ≠ 1} N(σ,T,χ) ≤ C (qT)^{c(1-σ)}`

(with `c > 2/(2σ₀-1)`), which every consumer (Areas 2, 3 and 6) can use, together with the
parameter packet `Params` of Heath-Brown §11 run with `O(1)` constants:

* `Dpow q T a = (q(T+2))^a` — the scale `𝓓 = q(T+2)` of the note (not `q`: heights up to `T` are
  allowed);
* `P1`: `x·σ₀ ≥ 1/2 + v + w + 2η` — the detector contour condition
  (convexity on `Re s = 0` replaces Burgess on `Re s = 1-1/k`, so the `1/3` of `Density4` is
  replaced by `1/2 + η`);
* `P2`: `u·(2σ₀-1) ≥ 1/2 + 2w + 2η` — the cross-term (off-diagonal) condition;
* `poleK`, `poleGram`: the pole Gram matrix `K_ij = Γ(2-ρ_i-\barρ_j)
  (X^{2-ρ_i-\barρ_j} - U'^{2-ρ_i-\barρ_j})` of the damped large sieve (L4).

`𝓓 ≥ 𝓓₀` thresholds are written with an explicit `∃ D₀`.
-/

open DirichletCharacter Complex
open scoped Classical BigOperators
noncomputable section

namespace Work.ZeroDensity.LogFree

open Work.LinnikContract

/-! ## 1. The non-principal counting functions -/

/-- The **non-principal family zero count** `Σ'_{χ ≠ 1} N(σ,T,χ)`. -/
def famCountNP (q : ℕ) [NeZero q] (σ T : ℝ) : ℝ :=
  ∑ χ ∈ Finset.univ.erase (1 : DirichletCharacter ℂ q), zCount χ σ T

/-- **The unified log-free non-principal zero-density estimate.**  For `σ₀ ∈ (1/2,1]` and
`c > 2/(2σ₀-1)` there is `C > 0` with
`Σ'_{χ ≠ 1} N(σ,T,χ) ≤ C (qT)^{c(1-σ)}` for all `q ≥ 2`, `σ ∈ [σ₀,1]`, `T ≥ 1`.
The estimate is *log-free* (no power of `log qT`). -/
def logFreeNP (σ₀ c : ℝ) : Prop :=
  ∃ C : ℝ, 0 < C ∧ ∀ q : ℕ, 2 ≤ q → ∀ [NeZero q] (σ T : ℝ), σ₀ ≤ σ → σ ≤ 1 → 1 ≤ T →
    famCountNP q σ T ≤ C * ((q : ℝ) * T) ^ (c * (1 - σ))

/-- **Heath-Brown's (1.4) for the non-principal characters**, `Σ' N(σ,T,χ) ≪ (qT)^{(12/5+ε)(1-σ)}`
on the whole near-line range `σ ≥ 3979/5000`.  This is `logFreeNP (93/100) (12/5)` glued with
Huxley's non-principal `12/5` bound widened to `σ ≤ 93/100` (`HuxleyNPWide`). -/
def NonPrincipalTwelveFifths : Prop :=
  ∀ ε : ℝ, 0 < ε → ∃ C : ℝ, 0 < C ∧ ∀ q : ℕ, 2 ≤ q → ∀ [NeZero q] (σ T : ℝ),
    (3979 / 5000 : ℝ) ≤ σ → σ ≤ 1 → 1 ≤ T →
      famCountNP q σ T ≤ C * ((q : ℝ) * T) ^ (((12 : ℝ) / 5 + ε) * (1 - σ))

/-- **Huxley's non-principal `12/5` estimate widened to `σ ≤ 93/100`** (one logarithmic power).
Area 6 needs the range `σ ∈ [3/4, 93/100]`. -/
def HuxleyNPWide : Prop :=
  ∀ ε : ℝ, 0 < ε → ∃ C : ℝ, 0 < C ∧ ∀ q : ℕ, 2 ≤ q → ∀ [NeZero q] (σ T : ℝ),
    (3 / 4 : ℝ) ≤ σ → σ ≤ (93 / 100 : ℝ) → 1 ≤ T →
      famCountNP q σ T ≤ C * ((q : ℝ) * T) ^ (((12 : ℝ) / 5 + ε) * (1 - σ))
        * Real.log ((q : ℝ) * T)

/-! ## 2. Elementary facts -/

lemma famCountNP_nonneg (q : ℕ) [NeZero q] (σ T : ℝ) : 0 ≤ famCountNP q σ T :=
  Finset.sum_nonneg (fun χ _ => zCount_nonneg χ σ T)

lemma famCountNP_le_famCount (q : ℕ) [NeZero q] (σ T : ℝ) :
    famCountNP q σ T ≤ famCount q σ T := by
  rw [famCountNP, famCount]
  exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.erase_subset _ _)
    (fun χ _ _ => zCount_nonneg χ σ T)

lemma logFreeNP_mono {σ₀ σ₀' c c' : ℝ} (hσ : σ₀ ≤ σ₀') (hc : c ≤ c')
    (h : logFreeNP σ₀ c) : logFreeNP σ₀' c' := by
  obtain ⟨C, hC, hh⟩ := h
  refine ⟨C, hC, ?_⟩
  intro q hq _inst σ T hσ₀ hσ1 hT
  by_cases hσle : σ ≤ 1
  · have hbase1 : (1 : ℝ) ≤ (q : ℝ) * T := by
      have : (2 : ℝ) ≤ (q : ℝ) := by exact_mod_cast hq
      nlinarith
    have h0 : (0 : ℝ) ≤ 1 - σ := by linarith
    refine le_trans (hh q hq σ T (le_trans hσ hσ₀) hσle hT) ?_
    refine mul_le_mul_of_nonneg_left ?_ (le_of_lt hC)
    refine Real.rpow_le_rpow_of_exponent_le hbase1 ?_
    nlinarith
  · rw [not_le] at hσle
    have hzero : famCountNP q σ T = 0 := by
      rw [famCountNP]
      exact Finset.sum_eq_zero (fun χ _ => zCount_eq_zero_of_one_lt χ hσle)
    rw [hzero]
    exact mul_nonneg (le_of_lt hC)
      (Real.rpow_nonneg (show (0 : ℝ) ≤ (q : ℝ) * T by
        have hq0 : (0 : ℝ) ≤ (q : ℝ) := Nat.cast_nonneg q
        linarith) _)

/-! ## 3. The parameter packet of the unified argument -/

/-- **The parameters of Heath-Brown §11 run with `O(1)` constants.**  `σ₀` is the lower end of the
`σ`-range, `η` the convexity margin, and `0 < w < u < v < x` the four exponents of
`U = 𝓓^u`, `V = 𝓓^v`, `W = 𝓓^w`, `X = 𝓓^x` (`𝓓 = q(T+2)`); `P1` and `P2` are the two conditions
of `JUTILA_UNIFIED_LEAD.md` §3 that make the contour shift and the cross terms work. -/
structure Params where
  σ₀ : ℝ
  η : ℝ
  w : ℝ
  u : ℝ
  v : ℝ
  x : ℝ
  hσ₀ : 1 / 2 < σ₀
  hσ₀1 : σ₀ ≤ 1
  hη : 0 < η
  hw : 0 < w
  hwu : w < u
  huv : u < v
  hvx : v < x
  P1 : x * σ₀ ≥ 1 / 2 + v + w + 2 * η
  P2 : u * (2 * σ₀ - 1) ≥ 1 / 2 + 2 * w + 2 * η

/-- The scale `𝓓 = q(T+2)`. -/
def scale (q : ℕ) (T : ℝ) : ℝ := (q : ℝ) * (T + 2)

/-- `L = log 𝓓`. -/
def Lscale (q : ℕ) (T : ℝ) : ℝ := Real.log (scale q T)

/-- `log₂ x = log x / log 2`, written out to avoid a Mathlib name dependency. -/
def log2 (x : ℝ) : ℝ := Real.log x / Real.log 2

/-- `𝓓^a`. -/
def Dpow (q : ℕ) (T a : ℝ) : ℝ := (scale q T) ^ a

/-! ## 4. The pole Gram matrix of the damped large sieve (L4) -/

/-- The `(i,j)` entry of the pole Gram matrix of the damped large sieve:
`K_ij = Γ(2-ρ_i-\barρ_j)·(X^{2-ρ_i-\barρ_j} - U'^{2-ρ_i-\barρ_j})`. -/
def poleK (X U' : ℝ) (ρ σ : ℂ) : ℂ :=
  Complex.Gamma (2 - ρ - (starRingEnd ℂ) σ) *
    ((X : ℂ) ^ (2 - ρ - (starRingEnd ℂ) σ) - (U' : ℂ) ^ (2 - ρ - (starRingEnd ℂ) σ))

/-- The quadratic form `Σ_{i,j} z_i \bar z_j K_ij`. -/
def poleGram (m : ℕ) (X U' : ℝ) (ρ : Fin m → ℂ) (z : Fin m → ℂ) : ℂ :=
  ∑ i, ∑ j, z i * (starRingEnd ℂ) (z j) * poleK X U' (ρ i) (ρ j)

/-! ## 5. The Gram kernel of the duality count (L3) -/

/-- `Theta(n) = sum_{d | n} theta_d`, the divisor sum of the mollifier `thetaM W` (HB (11.7)). -/
def thetaS (W : ℝ) (n : ℕ) : ℝ := ∑ d ∈ n.divisors, Work.LinnikAreas.Density4.thetaM W d

/-- `Psi(n) = sum_{d | n} psi_d`, the divisor sum of the mollifier `psiM U V` (HB (11.6)). -/
def psiSum (U V : ℝ) (n : ℕ) : ℝ := ∑ d ∈ n.divisors, Work.LinnikAreas.Density4.psiM U V d

/-- `g(n) = e^(-n/X) - e^(-n/U')`, the damping factor of the duality count. -/
def gfun (X U' : ℝ) (n : ℕ) : ℝ := Real.exp (-((n : ℝ) / X)) - Real.exp (-((n : ℝ) / U'))

/-- The `(i,j)` entry `G_ij = sum_n (sum_{d|n} theta_d)^2 * chi_i * conj(chi_j)(n)
* n^(1 - rho_i - conj rho_j) * (e^(-n/X) - e^(-n/U'))` of the Gram matrix of the duality count. -/
def gramEntry (q : ℕ) [NeZero q] (W X U' : ℝ) (χ χ' : DirichletCharacter ℂ q)
    (ρ ρ' : ℂ) : ℂ :=
  ∑' n : ℕ, (((thetaS W n : ℝ)) : ℂ) ^ 2
    * ((χ * χ'⁻¹) (n : ZMod q)) * ((n : ℂ) ^ (1 - ρ - (starRingEnd ℂ) ρ'))
    * (((Real.exp (-((n : ℝ) / X)) - Real.exp (-((n : ℝ) / U')) : ℝ)) : ℂ)

/-- The **`q`-free** entry `G'_ij = sum_n (sum_{d|n} theta_d)^2 * n^(1 - rho - conj rho') * g(n)`
(dropping the restriction `(n,q) = 1`).  This is the matrix whose residue is the pole term
`poleResidue W * poleK X U' rho rho'`; dropping `1_{(n,q)=1}` adds positive semidefinite rank-one
terms, so the two-sided estimate is stated for this `q`-free matrix and transferred by Loewner
domination. -/
def gramEntryFree (W X U' : ℝ) (ρ ρ' : ℂ) : ℂ :=
  ∑' n : ℕ, ((thetaS W n : ℝ) : ℂ) ^ 2 * ((n : ℂ) ^ (1 - ρ - (starRingEnd ℂ) ρ'))
    * ((gfun X U' n : ℝ) : ℂ)

/-- The pole residue `Q(1) = sum_{d,e <= W} theta_d theta_e / [d,e]` of the duality count. -/
def poleResidue (W : ℝ) : ℝ :=
  ∑ d ∈ Finset.Icc 1 ⌈W⌉₊, ∑ e ∈ Finset.Icc 1 ⌈W⌉₊,
    Work.LinnikAreas.Density4.thetaM W d * Work.LinnikAreas.Density4.thetaM W e
      / (Nat.lcm d e : ℝ)

end Work.ZeroDensity.LogFree
