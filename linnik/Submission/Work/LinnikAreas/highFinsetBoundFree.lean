import Mathlib
import Submission.Work.LinnikAreas.SiegelBase
import Submission.Work.LinnikAreas.pairCountHeight_le_famCount
import Submission.Work.LinnikAreas.sum_mul_exp_neg_le_of_count
import Submission.Work.LinnikAreas.siegelRestHigh
import Submission.Work.LinnikAreas.pairCountHeight_dom
import Submission.Work.LinnikAreas.siegelAbelGrow
import Submission.Work.LinnikAreas.dyadicGeomFree
import Submission.Work.LinnikAreas.highDyadicLayerFree
import Submission.Work.LinnikAreas.pairCountHeightDyadicFree

open DirichletCharacter Complex
open scoped Classical BigOperators
noncomputable section

namespace Work.LinnikAreas

open Work.LinnikContract

set_option linter.unusedVariables false

/-- The dyadic height layer index of a pair, `⌊log₂ ⌊|Im ρ|⌋⌋`. -/
private noncomputable def jj {q : ℕ} (z : DirichletCharacter ℂ q × ℂ) : ℕ :=
  Nat.log 2 (Nat.floor |z.2.im|)

/-- **The `λ₁`-free mass bound for the high zeros (`|Im ρ| > 1`).**

With the `λ₁`-free log-free family count `Work.ZeroDensity.LogFreeFamHeight (5/2) (3/2)` there are
`K > 0` and `q₀` such that for every `q ≥ q₀` with `q > 1`, every threshold character `χ₁` and
point `β₁ ∈ ℂ`, and every finite set `S` of zero-pairs `(χ,ρ)` whose members are genuine zeros
(`zeroMult χ ρ ≠ 0`), are all *high* (`1 < |Im ρ|`) and are none of them the pair `(χ₁,β₁)`, the
multiplicity-weighted kernel sum is at most `K·(log q)^{-2}`:
`Σ_{(χ,ρ) ∈ S} mult(ρ)·‖Hk (11/2) (3/10) ((1-ρ)log q)‖ ≤ K·(log q)^{-2}`.

Proof recipe (all pieces are in the workspace):

* `Work.LinnikAreas.high_kernel_le` (`Submission/Work/LinnikAreas/siegelRestHigh.lean`) gives, on a
  high zero of level `q > 1`, `mult·‖Hk (11/2) (3/10) ((1-ρ)𝓛)‖ ≤ 4·mult·e^{-(49/10)λ(ρ)}/(|Im ρ|𝓛)²`.
* Group `S` by the dyadic height index `j = Nat.log 2 ⌊|Im ρ|⌋`; on the fibre `S_j` every height
  satisfies `|Im ρ| < 2^{j+1}` (via `Nat.lt_pow_succ_log_self`), hence `|Im ρ|·𝓛 ≤ 2^{j+1}·𝓛`. So
  `Work.LinnikAreas.pairCountHeight_le_famCount` with `T = 2^{j+1}·𝓛` followed by `hfam` gives the
  counting hypothesis `Σ_{z ∈ S_j, λ(z) ≤ t} mult(z) ≤ C₂·e^{(5/2)t}·(2^{j+1})^{3/2}` valid for
  `0 < t ≤ 𝓛` (note `T/𝓛 = 2^{j+1} ≥ 1` and `1 - t/𝓛 ∈ [0,1]`).
* Abel summation in `λ` against this count: apply
  `Work.LinnikAreas.sum_mul_exp_neg_le_of_count` (`Submission/Work/LinnikAreas/sum_mul_exp_neg_le_of_count.lean`)
  to the fibre, with `a₀ = 49/10`, `c = 5/2`, `D·lam₁ = C₂·(2^{j+1})^{3/2}`, `L = 𝓛` and
  `Λ = min_{z ∈ S_j} λ(z) > 0` (use `Finset.exists_mem_eq_inf'` for `Λ > 0`; the empty fibre is
  trivial). Then `Λ ≤ λ(z)` is automatic and the conclusion is
  `Σ_{z∈S_j} mult·e^{-(49/10)λ} ≤ C₂·(2^{j+1})^{3/2}·e^{5/2}·e^{-(12/5)Λ}/(1-e^{-12/5})`, which is
  `≤ C₂·(2^{j+1})^{3/2}·e^{5/2}/(1-e^{-12/5})` since `Λ > 0`.
* The kernel weight satisfies `4/(|Im ρ|𝓛)² ≤ (4/𝓛²)·(4^{j})^{-1}` on the fibre (using
  `4^j ≤ |Im ρ|²`), so the fibre contribution is at most
  `(4C₂e^{5/2}/(1-e^{-12/5}))·2^{3/2}·𝓛^{-2}·2^{-j/2}`; summing over `j ∈ S.image jj` with
  `Σ_j 2^{-j/2} ≤ (1-2^{-1/2})^{-1}` gives the claim with
  `K = 4·C₂·e^{5/2}·(1-e^{-12/5})^{-1}·2^{3/2}·(1-2^{-1/2})^{-1}`, independent of `q`, `χ₁`, `β₁`
  and `S`, and `q₀` the threshold of `hfam`.

The assembly is the same as that of `Work.LinnikAreas.high_finset_bound`
(`Submission/Work/LinnikAreas/siegelRestHigh.lean`, already proved), with the `λ₁`-saving count
`C·lam₁·e^{ct}·T^{c'}` replaced by the `λ₁`-free count above. -/
theorem highFinsetBoundFree (hfam : Work.ZeroDensity.LogFreeFamHeight (5 / 2) (3 / 2)) :
    ∃ K : ℝ, 0 < K ∧ ∃ q₀ : ℕ, ∀ {q : ℕ} [NeZero q], q₀ ≤ q → 1 < q →
      ∀ (χ₁ : DirichletCharacter ℂ q) (β₁ : ℂ) (S : Finset (DirichletCharacter ℂ q × ℂ)),
        (∀ z ∈ S, Work.LinnikContract.zeroMult z.1 z.2 ≠ 0) →
        (∀ z ∈ S, 1 < |z.2.im|) →
        (∀ z ∈ S, ¬(z.1 = χ₁ ∧ z.2 = β₁)) →
        (∑ z ∈ S, (Work.LinnikContract.zeroMult z.1 z.2 : ℝ)
            * ‖Work.LinnikContract.Hk (11 / 2) (3 / 10)
                ((1 - z.2) * (Real.log q : ℂ))‖)
          ≤ K * (Real.log q) ^ (-2 : ℝ) := by
  obtain ⟨C₂, hC₂, q₀f, hfam'⟩ := hfam
  have hr_lt_one : (2 : ℝ) ^ (-(1 / 2) : ℝ) < 1 := by
    have h1 : (2 : ℝ) ^ (-(1 / 2) : ℝ) = (Real.sqrt 2)⁻¹ := by
      rw [Real.rpow_neg (by norm_num : (0 : ℝ) ≤ 2), ← Real.sqrt_eq_rpow]
    rw [h1]
    refine inv_lt_one_of_one_lt₀ ?_
    nlinarith [Real.sq_sqrt (show (0 : ℝ) ≤ 2 by norm_num), Real.sqrt_nonneg 2]
  have hden : 0 < 1 - (2 : ℝ) ^ (-(1 / 2) : ℝ) := by linarith
  have h2p : 0 < (2 : ℝ) ^ (3 / 2 : ℝ) := Real.rpow_pos_of_pos (by norm_num) _
  refine ⟨400 * C₂ * (2 : ℝ) ^ (3 / 2 : ℝ) * (1 - (2 : ℝ) ^ (-(1 / 2) : ℝ))⁻¹,
    mul_pos (mul_pos (mul_pos (by norm_num) hC₂) h2p) (inv_pos.mpr hden), q₀f, ?_⟩
  intro q _ hq₀ hq₁ χ₁ β₁ S hzm hhigh hexc
  have hlog : 0 < Real.log q := Real.log_pos (by exact_mod_cast hq₁)
  have hC : ∀ σ T : ℝ, 0 ≤ σ → σ ≤ 1 → 1 ≤ T →
      Work.ZeroDensity.famCount q σ T
        ≤ C₂ * Real.exp ((5 / 2) * ((1 - σ) * Real.log q)) * T ^ (3 / 2 : ℝ) :=
    fun σ T h1 h2 h3 => hfam' q hq₀ σ T h1 h2 h3
  -- step 1: split `S` into the fibres of the dyadic height index `jj`
  rw [← Finset.sum_fiberwise_of_maps_to (fun z hz => Finset.mem_image_of_mem jj hz)
    (fun z => (Work.LinnikContract.zeroMult z.1 z.2 : ℝ)
      * ‖Work.LinnikContract.Hk (11 / 2) (3 / 10) ((1 - z.2) * (Real.log q : ℂ))‖)]
  -- step 2: each fibre is bounded by the per-layer estimate
  have hfib : ∀ j ∈ S.image jj,
      (∑ z ∈ S.filter (fun z => jj z = j), (Work.LinnikContract.zeroMult z.1 z.2 : ℝ)
        * ‖Work.LinnikContract.Hk (11 / 2) (3 / 10) ((1 - z.2) * (Real.log q : ℂ))‖)
      ≤ 400 * C₂ * ((4 : ℝ) ^ j)⁻¹ * ((2 : ℝ) ^ (j + 1)) ^ (3 / 2 : ℝ)
          * ((Real.log q) ^ 2)⁻¹ := by
    intro j hj
    exact highDyadicLayerFree hq₁ χ₁ β₁ hC₂ j
      (pairCountHeightDyadicFree hq₁ χ₁ β₁ j hC) _
      (fun z hz => hzm z (Finset.mem_filter.mp hz).1)
      (fun z hz => hhigh z (Finset.mem_filter.mp hz).1)
      (fun z hz => hexc z (Finset.mem_filter.mp hz).1)
      (fun z hz => by simpa only [jj] using (Finset.mem_filter.mp hz).2)
  refine le_trans (Finset.sum_le_sum hfib) ?_
  -- step 3: factor out the constant and sum the geometric series over the layers
  have hfac : (∑ j ∈ S.image jj, 400 * C₂ * ((4 : ℝ) ^ j)⁻¹ * ((2 : ℝ) ^ (j + 1)) ^ (3 / 2 : ℝ)
        * ((Real.log q) ^ 2)⁻¹)
      = 400 * C₂ * ((Real.log q) ^ 2)⁻¹
        * (∑ j ∈ S.image jj, ((4 : ℝ) ^ j)⁻¹ * ((2 : ℝ) ^ (j + 1)) ^ (3 / 2 : ℝ)) := by
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl (fun j _ => by ring)
  rw [hfac]
  have hKnn : 0 ≤ 400 * C₂ * ((Real.log q) ^ 2)⁻¹ :=
    mul_nonneg (mul_nonneg (by norm_num) hC₂.le) (inv_nonneg.mpr (sq_nonneg _))
  have hrpow : ((Real.log q) ^ 2)⁻¹ = (Real.log q) ^ (-2 : ℝ) := by
    rw [show (-2 : ℝ) = -((2 : ℕ) : ℝ) by norm_num, Real.rpow_neg hlog.le, Real.rpow_natCast]
  have hEq : 400 * C₂ * ((Real.log q) ^ 2)⁻¹
        * ((2 : ℝ) ^ (3 / 2 : ℝ) * (1 - (2 : ℝ) ^ (-(1 / 2) : ℝ))⁻¹)
      = (400 * C₂ * (2 : ℝ) ^ (3 / 2 : ℝ) * (1 - (2 : ℝ) ^ (-(1 / 2) : ℝ))⁻¹)
        * (Real.log q) ^ (-2 : ℝ) := by
    rw [hrpow]
    ring
  exact le_trans (mul_le_mul_of_nonneg_left (dyadicGeomFree (S.image jj)) hKnn) (le_of_eq hEq)

end Work.LinnikAreas
