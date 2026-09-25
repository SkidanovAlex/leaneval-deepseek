import Mathlib
import Submission.Work.BourgainPlan.IonescuWainger.OpArcLinear
import Submission.Work.BourgainPlan.IonescuWainger.StrataCompSum
import Submission.Work.BourgainPlan.IonescuWainger.opArc_l2_endpoint_strata
import Submission.Work.BourgainPlan.IonescuWainger.opArc_sup_strata_family
import Submission.Work.BourgainPlan.IonescuWainger.ellp_vector_interpolation_family

/-!
# Tao's `ortho-apply`(ii) (Rubio de Francia estimate), assembled

Source: T. Tao, *The Ionescu–Wainger multiplier theorem and the adeles*, arXiv:2008.05066, §4,
Theorem `ortho-apply`(ii), in the case `d = 1`, `H = ℂ`:

`(∑_{A₀ ∈ binom(S,≤k)} ‖(Op_{φ; α+Σ_{A₀}} f)_{α ∈ Σ_{(A₀)}}‖^p_{ℓ^p(ℤ; ℓ²)})^{1/p} ≤ C^k ‖f‖_{ℓ^p}`

for `2 ≤ p ≤ ∞`, a bump `φ` supported in the ball of radius `ε` (with `(k,S,ε)` good) and every
`f ∈ ℓ^p`.  In the conventions of this corpus the square function is indexed by
`strataCompPairSet S k` (Tao's strata `Σ_A = sigmaStrataFinset A`, *not* the exact-denominator
sets) and the operator attached to `(A₀, α)` is `opArc φ hφ (arcShift (sigmaStrataFinset A₀) α)`,
the multiplier with symbol `Σ_{γ ∈ α + Σ_{A₀}} φ(·−γ)`.

This file assembles the estimate from its two endpoints and the family-valued interpolation:

* `p = 2`: `opArc_l2_endpoint_strata` (Plancherel + the `2 ^ k` arc count);
* `p = ∞`: `opArc_sup_strata_family` (strata inclusion–exclusion + the `ℓ¹` kernel bound);
* interpolation: `ellp_vector_interpolation_family` (the outer `A₀`-sum is *inside* the `ℓ^p`
  norm, so the single-index interpolation does not apply).

`ortho_apply_upper_of_endpoints` below is the assembly with those three inputs as hypotheses, so
that the (finite, but intricate) bookkeeping of the two sums, the `ofReal` conversions and the
`⨆`/sup bookkeeping is verified independently of them; the unconditional form is the one-line
instantiation once the three inputs are imported.

Note the restriction to finitely supported data: `opArc` is defined through `ℓ²(ℤ)`, so the
statement is about `f ∈ ℓ² ∩ ℓ^p`, which is what Tao's application (`f ∈ ℓ^{2r} ∩ ℓ²` for the
limiting argument in the proof of `main`) uses.
-/

open MeasureTheory Finset
open scoped BigOperators ENNReal

set_option autoImplicit false

namespace Work.BourgainPlan.IonescuWainger

noncomputable section

/-! ## The sup of a finitely supported sequence -/

/-- For a finitely supported complex sequence the `ℝ≥0∞`-sup of the moduli is finite. -/
theorem iSup_ofReal_norm_finsupp_ne_top (f : ℤ →₀ ℂ) :
    (⨆ n : ℤ, ENNReal.ofReal ‖f n‖) ≠ ⊤ := by
  have hb : (⨆ n : ℤ, ENNReal.ofReal ‖f n‖)
      ≤ ENNReal.ofReal (∑ m ∈ f.support, ‖f m‖) := by
    refine iSup_le (fun n => ?_)
    by_cases hn : n ∈ f.support
    · exact ENNReal.ofReal_le_ofReal (Finset.single_le_sum (fun i _ => norm_nonneg _) hn)
    · rw [Finsupp.notMem_support_iff.mp hn, norm_zero, ENNReal.ofReal_zero]
      exact bot_le
  exact ne_top_of_le_ne_top ENNReal.ofReal_ne_top hb

/-- The `ℝ≥0∞`-sup of the moduli of a finitely supported sequence is `ofReal` of its `toReal`. -/
theorem ofReal_toReal_iSup_ofReal_norm_finsupp (f : ℤ →₀ ℂ) :
    ENNReal.ofReal ((⨆ n : ℤ, ENNReal.ofReal ‖f n‖).toReal)
      = ⨆ n : ℤ, ENNReal.ofReal ‖f n‖ :=
  ENNReal.ofReal_toReal (iSup_ofReal_norm_finsupp_ne_top f)

/-- Every term of a finitely supported sequence is bounded by the `toReal` of the `ℝ≥0∞`-sup of
the moduli. -/
theorem norm_le_toReal_iSup_ofReal_norm_finsupp (f : ℤ →₀ ℂ) (m : ℤ) :
    ‖f m‖ ≤ (⨆ n : ℤ, ENNReal.ofReal ‖f n‖).toReal := by
  calc ‖f m‖ = (ENNReal.ofReal ‖f m‖).toReal := (ENNReal.toReal_ofReal (norm_nonneg _)).symm
    _ ≤ _ := ENNReal.toReal_mono (iSup_ofReal_norm_finsupp_ne_top f)
        (le_iSup (fun n : ℤ => ENNReal.ofReal ‖f n‖) m)

/-- The `ℝ`-exponent `(2 : ℝ≥0∞).toReal` is `2`. -/
theorem rpow_toReal_two (x : ℝ) : x ^ (ENNReal.toReal 2) = x ^ 2 := by
  have h : ENNReal.toReal 2 = (2 : ℝ) := by simp
  rw [h, Real.rpow_two]

/-! ## The assembly -/

/-- **Tao's `ortho-apply`(ii) (`d = 1`, `H = ℂ`) from its two endpoints and the family-valued
interpolation.**  See the module docstring; `hend2`, `hendsup` and `hinterp` are exactly the
statements of `opArc_l2_endpoint_strata`, `opArc_sup_strata_family` and
`ellp_vector_interpolation_family`. -/
theorem ortho_apply_upper_of_endpoints {S : Finset ℕ} (h2S : ∀ q ∈ S, 2 ≤ q)
    (hScop : ∀ p ∈ S, ∀ q ∈ S, p ≠ q → Nat.Coprime p q)
    {k : ℕ} {qmax : ℕ} (hmax : ∀ q ∈ S, q ≤ qmax) (hqmax : 1 ≤ qmax) {ε : ℝ} (hε0 : 0 < ε)
    (hsmall : 2 * ε < 1 / (qmax : ℝ) ^ (2 * k))
    (φ : Circle → ℂ) (hφ : MemLp φ ⊤ (AddCircle.haarAddCircle (T := 1))) {M : ℝ}
    (hM : 0 ≤ M) (hφbd : ∀ ξ, ‖φ ξ‖ ≤ M) (hφsupp : ∀ ξ, ε < ‖ξ‖ → φ ξ = 0)
    {K : ℤ → ℂ} {C : ℝ} (hC0 : 0 ≤ C)
    (hK : ∀ m : ℤ, ∫ ξ, φ ξ * star (fourier m ξ)
      ∂(AddCircle.haarAddCircle (T := 1)) = K m)
    (hdecay : ∀ m : ℤ, ‖K m‖ ≤ C * ε / (1 + (ε * (m : ℝ)) ^ 2) ^ ((3 : ℝ) / 2))
    (hend2 : ∀ (f : ℤ → ℂ) (hf : Memℓp f 2), ∑ p ∈ strataCompPairSet S k, ∑' n : ℤ,
        ‖opArc φ hφ (arcShift (sigmaStrataFinset p.1) p.2) f hf n‖ ^ 2
          ≤ M ^ 2 * (2 ^ k : ℝ) * ∑' n : ℤ, ‖f n‖ ^ 2)
    (hendsup : ∀ (A₀ : Finset ℕ), A₀ ⊆ S → A₀.card ≤ k →
      ∀ (f : ℤ → ℂ) (hf : Memℓp f 2) (C' : ℝ), (∀ m : ℤ, ‖f m‖ ≤ C') → ∀ n : ℤ,
        (∑ α ∈ strataCompFinset S k A₀,
            ‖opArc φ hφ (arcShift (sigmaStrataFinset A₀) α) f hf n‖ ^ 2) ^ ((1 : ℝ) / 2)
          ≤ 2 ^ k * (8 * C * C'))
    (hinterp : ∀ {p : ℝ}, 2 ≤ p →
      ∀ (T : (A₀ : ↥(S.powerset.filter (fun A => A.card ≤ k))) →
          ↥(strataCompFinset S k A₀.1) → (ℤ →₀ ℂ) →ₗ[ℂ] (ℤ → ℂ)) (A B : ℝ), 0 ≤ A → 0 ≤ B →
      (∀ f : ℤ →₀ ℂ, (∑' n : ℤ, ∑ A₀, ∑ α,
          ENNReal.ofReal (‖T A₀ α f n‖ ^ 2))
        ≤ ENNReal.ofReal (A ^ 2) * ∑' n : ℤ, ENNReal.ofReal (‖f n‖ ^ 2)) →
      (∀ f : ℤ →₀ ℂ, (⨆ (A₀ : ↥(S.powerset.filter (fun A => A.card ≤ k))), ⨆ n : ℤ,
          (∑ α, ENNReal.ofReal (‖T A₀ α f n‖ ^ 2)) ^ ((1 : ℝ) / 2))
        ≤ ENNReal.ofReal B * (⨆ n : ℤ, ENNReal.ofReal ‖f n‖)) →
      ∀ f : ℤ →₀ ℂ,
        (∑' n : ℤ, ∑ A₀, (∑ α, ENNReal.ofReal (‖T A₀ α f n‖ ^ 2)) ^ (p / 2)) ^ (1 / p)
          ≤ ENNReal.ofReal (A ^ (2 / p) * B ^ (1 - 2 / p))
            * (∑' n : ℤ, ENNReal.ofReal (‖f n‖ ^ p)) ^ (1 / p))
    {p : ℝ} (hp : 2 ≤ p) (f : ℤ →₀ ℂ) :
    (∑' n : ℤ, ∑ A₀ ∈ S.powerset.filter (fun A => A.card ≤ k),
        (∑ α ∈ strataCompFinset S k A₀, ENNReal.ofReal
          (‖opArc φ hφ (arcShift (sigmaStrataFinset A₀) α) (⇑f) (memℓp_finsupp f) n‖ ^ 2))
          ^ (p / 2)) ^ (1 / p)
      ≤ ENNReal.ofReal ((M ^ 2 * (2 ^ k : ℝ)) ^ (1 / p) * (8 * C * (2 ^ k : ℝ)) ^ (1 - 2 / p))
        * (∑' n : ℤ, ENNReal.ofReal (‖f n‖ ^ p)) ^ (1 / p) := by
  classical
  have hAsq : (0 : ℝ) ≤ M ^ 2 * (2 ^ k : ℝ) := by positivity
  have hB0 : (0 : ℝ) ≤ 8 * C * (2 ^ k : ℝ) := by positivity
  have hB0' : (0 : ℝ) ≤ 8 * C := by positivity
  -- ### (1) the total `ℓ²` hypothesis
  have hsum2 : ∀ g : ℤ →₀ ℂ,
      (∑' n : ℤ, ∑ A₀ : ↥(S.powerset.filter (fun A => A.card ≤ k)),
          ∑ α : ↥(strataCompFinset S k A₀.1), ENNReal.ofReal
            (‖opArcLM φ hφ (arcShift (sigmaStrataFinset A₀.1) α.1) g n‖ ^ 2))
        ≤ ENNReal.ofReal (Real.sqrt (M ^ 2 * (2 ^ k : ℝ)) ^ 2)
          * ∑' n : ℤ, ENNReal.ofReal (‖g n‖ ^ 2) := by
    intro g
    have hmem : ∀ q ∈ strataCompPairSet S k,
        Memℓp (opArc φ hφ (arcShift (sigmaStrataFinset q.1) q.2) (⇑g) (memℓp_finsupp g)) 2 := by
      intro q _
      exact opMul_memℓp (arcSymbolLp φ hφ (arcShift (sigmaStrataFinset q.1) q.2))
        (⇑g) (memℓp_finsupp g)
    have hsummable : ∀ q ∈ strataCompPairSet S k, Summable (fun n : ℤ =>
        ‖opArc φ hφ (arcShift (sigmaStrataFinset q.1) q.2) (⇑g) (memℓp_finsupp g) n‖ ^ 2) := by
      intro q hq
      exact ((memℓp_gen_iff (p := 2) (by norm_num)).mp (hmem q hq)).congr
        (fun n => rpow_toReal_two _)
    have hg2 : Summable (fun n : ℤ => ‖g n‖ ^ 2) :=
      ((memℓp_gen_iff (p := 2) (by norm_num)).mp (memℓp_finsupp g)).congr
        (fun n => rpow_toReal_two _)
    have hswap : (∑' n : ℤ, ∑ q ∈ strataCompPairSet S k,
          ‖opArc φ hφ (arcShift (sigmaStrataFinset q.1) q.2) (⇑g) (memℓp_finsupp g) n‖ ^ 2)
        = ∑ q ∈ strataCompPairSet S k, ∑' n : ℤ,
          ‖opArc φ hφ (arcShift (sigmaStrataFinset q.1) q.2) (⇑g) (memℓp_finsupp g) n‖ ^ 2 :=
      Summable.tsum_finsetSum hsummable
    have hsummableW : Summable (fun n : ℤ => ∑ q ∈ strataCompPairSet S k,
        ‖opArc φ hφ (arcShift (sigmaStrataFinset q.1) q.2) (⇑g) (memℓp_finsupp g) n‖ ^ 2) :=
      summable_sum hsummable
    have hpt : ∀ n : ℤ, (∑ A₀ : ↥(S.powerset.filter (fun A => A.card ≤ k)),
          ∑ α : ↥(strataCompFinset S k A₀.1), ENNReal.ofReal
            (‖opArcLM φ hφ (arcShift (sigmaStrataFinset A₀.1) α.1) g n‖ ^ 2))
        = ENNReal.ofReal (∑ q ∈ strataCompPairSet S k,
            ‖opArc φ hφ (arcShift (sigmaStrataFinset q.1) q.2) (⇑g) (memℓp_finsupp g) n‖ ^ 2) := by
      intro n
      simp only [opArcLM_apply]
      rw [← sum_strataCompPairSet_subtype (S := S) (k := k)
        (g := fun q => ENNReal.ofReal (‖opArc φ hφ (arcShift (sigmaStrataFinset q.1) q.2)
          (⇑g) (memℓp_finsupp g) n‖ ^ 2))]
      rw [← ENNReal.ofReal_sum_of_nonneg (fun q _ => sq_nonneg _)]
    have hLHS : (∑' n : ℤ, ∑ A₀ : ↥(S.powerset.filter (fun A => A.card ≤ k)),
          ∑ α : ↥(strataCompFinset S k A₀.1), ENNReal.ofReal
            (‖opArcLM φ hφ (arcShift (sigmaStrataFinset A₀.1) α.1) g n‖ ^ 2))
        = ENNReal.ofReal (∑' n : ℤ, ∑ q ∈ strataCompPairSet S k,
            ‖opArc φ hφ (arcShift (sigmaStrataFinset q.1) q.2) (⇑g) (memℓp_finsupp g) n‖ ^ 2) := by
      rw [tsum_congr hpt]
      exact (ENNReal.ofReal_tsum_of_nonneg
        (fun n => Finset.sum_nonneg (fun q _ => sq_nonneg _)) hsummableW).symm
    rw [hLHS, hswap, Real.sq_sqrt hAsq]
    refine le_trans (ENNReal.ofReal_le_ofReal (hend2 (⇑g) (memℓp_finsupp g))) ?_
    rw [ENNReal.ofReal_mul hAsq, ENNReal.ofReal_tsum_of_nonneg (fun n => sq_nonneg _) hg2]
  -- ### (2) the per-`A₀` sup hypothesis
  have hsup : ∀ g : ℤ →₀ ℂ, (⨆ (A₀ : ↥(S.powerset.filter (fun A => A.card ≤ k))), ⨆ n : ℤ,
      (∑ α : ↥(strataCompFinset S k A₀.1), ENNReal.ofReal
        (‖opArcLM φ hφ (arcShift (sigmaStrataFinset A₀.1) α.1) g n‖ ^ 2)) ^ ((1 : ℝ) / 2))
      ≤ ENNReal.ofReal (8 * C * (2 ^ k : ℝ)) * (⨆ n : ℤ, ENNReal.ofReal ‖g n‖) := by
    intro g
    set C' : ℝ := (⨆ n : ℤ, ENNReal.ofReal ‖g n‖).toReal with hC'def
    have hC'sup : (⨆ n : ℤ, ENNReal.ofReal ‖g n‖) = ENNReal.ofReal C' := by
      rw [hC'def]; exact (ofReal_toReal_iSup_ofReal_norm_finsupp g).symm
    have hC' : ∀ m : ℤ, ‖g m‖ ≤ C' := by
      intro m; rw [hC'def]; exact norm_le_toReal_iSup_ofReal_norm_finsupp g m
    refine iSup_le (fun A₀ => iSup_le (fun n => ?_))
    have hmem := A₀.2
    rw [Finset.mem_filter, Finset.mem_powerset] at hmem
    obtain ⟨hA₀sub, hA₀card⟩ := hmem
    have hb := hendsup A₀.1 hA₀sub hA₀card (⇑g) (memℓp_finsupp g) C' hC' n
    simp only [opArcLM_apply]
    rw [Finset.sum_coe_sort (s := strataCompFinset S k A₀.1)
      (f := fun α => ENNReal.ofReal (‖opArc φ hφ (arcShift (sigmaStrataFinset A₀.1) α)
        (⇑g) (memℓp_finsupp g) n‖ ^ 2))]
    rw [← ENNReal.ofReal_sum_of_nonneg
      (fun α _ => sq_nonneg (‖opArc φ hφ (arcShift (sigmaStrataFinset A₀.1) α)
        (⇑g) (memℓp_finsupp g) n‖))]
    rw [ENNReal.ofReal_rpow_of_nonneg (Finset.sum_nonneg (fun α _ => sq_nonneg _))
      (by norm_num : (0 : ℝ) ≤ 1 / 2)]
    rw [hC'sup, ← ENNReal.ofReal_mul hB0]
    refine ENNReal.ofReal_le_ofReal ?_
    rw [show 8 * C * (2 ^ k : ℝ) * C' = 2 ^ k * (8 * C * C') by ring]
    exact hb
  -- ### (3) the family-valued interpolation
  have hmain := hinterp hp
    (fun A₀ α => opArcLM φ hφ (arcShift (sigmaStrataFinset A₀.1) α.1))
    (Real.sqrt (M ^ 2 * (2 ^ k : ℝ))) (8 * C * (2 ^ k : ℝ))
    (Real.sqrt_nonneg _) hB0 hsum2 hsup f
  simp only [opArcLM_apply] at hmain
  -- ### (4) packaging
  have hLHS : (∑' n : ℤ, ∑ A₀ ∈ S.powerset.filter (fun A => A.card ≤ k),
        (∑ α ∈ strataCompFinset S k A₀, ENNReal.ofReal
          (‖opArc φ hφ (arcShift (sigmaStrataFinset A₀) α) (⇑f) (memℓp_finsupp f) n‖ ^ 2))
          ^ (p / 2)) ^ (1 / p)
      = (∑' n : ℤ, ∑ A₀ : ↥(S.powerset.filter (fun A => A.card ≤ k)),
        (∑ α : ↥(strataCompFinset S k A₀.1), ENNReal.ofReal
          (‖opArc φ hφ (arcShift (sigmaStrataFinset A₀.1) α.1) (⇑f) (memℓp_finsupp f) n‖ ^ 2))
          ^ (p / 2)) ^ (1 / p) := by
    congr 1
    refine tsum_congr (fun n => ?_)
    exact sum_strataCompPairSet_pow (S := S) (k := k)
      (g := fun q => ENNReal.ofReal (‖opArc φ hφ (arcShift (sigmaStrataFinset q.1) q.2)
        (⇑f) (memℓp_finsupp f) n‖ ^ 2)) (F := fun u => u ^ (p / 2))
  have hconst : Real.sqrt (M ^ 2 * (2 ^ k : ℝ)) ^ (2 / p) = (M ^ 2 * (2 ^ k : ℝ)) ^ (1 / p) := by
    have hp0 : (0 : ℝ) < p := by linarith
    rw [Real.sqrt_eq_rpow, ← Real.rpow_mul hAsq]
    congr 1
    field_simp
  refine le_trans (le_of_eq hLHS) (le_trans hmain (le_of_eq (by rw [hconst])))

/-! ## The unconditional form -/

/-- **Tao's `ortho-apply`(ii) (`d = 1`, `H = ℂ`)**, obtained from the two endpoints
(`opArc_l2_endpoint_strata`, `opArc_sup_strata_family`) and the family-valued interpolation
(`ellp_vector_interpolation_family`) via `ortho_apply_upper_of_endpoints`. -/
theorem ortho_apply_upper {S : Finset ℕ} (h2S : ∀ q ∈ S, 2 ≤ q)
    (hScop : ∀ p ∈ S, ∀ q ∈ S, p ≠ q → Nat.Coprime p q)
    {k : ℕ} {qmax : ℕ} (hmax : ∀ q ∈ S, q ≤ qmax) (hqmax : 1 ≤ qmax)
    {ε : ℝ} (hε0 : 0 < ε)
    (hsmall : 2 * ε < 1 / (qmax : ℝ) ^ (2 * k))
    (φ : Circle → ℂ) (hφ : MemLp φ ⊤ (AddCircle.haarAddCircle (T := 1))) {M : ℝ}
    (hM : 0 ≤ M) (hφbd : ∀ ξ, ‖φ ξ‖ ≤ M) (hφsupp : ∀ ξ, ε < ‖ξ‖ → φ ξ = 0)
    {K : ℤ → ℂ} {C : ℝ} (hC0 : 0 ≤ C)
    (hK : ∀ m : ℤ, ∫ ξ, φ ξ * star (fourier m ξ)
      ∂(AddCircle.haarAddCircle (T := 1)) = K m)
    (hdecay : ∀ m : ℤ, ‖K m‖ ≤ C * ε / (1 + (ε * (m : ℝ)) ^ 2) ^ ((3 : ℝ) / 2))
    {p : ℝ} (hp : 2 ≤ p) (f : ℤ →₀ ℂ) :
    (∑' n : ℤ, ∑ A₀ ∈ S.powerset.filter (fun A => A.card ≤ k),
        (∑ α ∈ strataCompFinset S k A₀, ENNReal.ofReal
          (‖opArc φ hφ (arcShift (sigmaStrataFinset A₀) α) (⇑f) (memℓp_finsupp f) n‖ ^ 2))
          ^ (p / 2)) ^ (1 / p)
      ≤ ENNReal.ofReal ((M ^ 2 * (2 ^ k : ℝ)) ^ (1 / p) * (8 * C * (2 ^ k : ℝ)) ^ (1 - 2 / p))
        * (∑' n : ℤ, ENNReal.ofReal (‖f n‖ ^ p)) ^ (1 / p) := by
  have hε1 : ε ≤ 1 := by
    have hq1 : (1 : ℝ) ≤ (qmax : ℝ) := by exact_mod_cast hqmax
    have hpow : (1 : ℝ) ≤ (qmax : ℝ) ^ (2 * k) := one_le_pow₀ hq1
    have hle : 1 / (qmax : ℝ) ^ (2 * k) ≤ 1 := by
      rw [div_le_one (by positivity)]; exact hpow
    linarith
  exact ortho_apply_upper_of_endpoints h2S hScop hmax hqmax hε0 hsmall φ hφ hM hφbd hφsupp
    hC0 hK hdecay
    (fun g hg => opArc_l2_endpoint_strata h2S hScop hmax hqmax hε0.le hsmall φ hφ hM hφbd hφsupp g hg)
    (fun A₀ hA₀ hk₀ g hg C' hC' n =>
      opArc_sup_strata_family h2S hScop hA₀ hk₀ hmax hqmax hε0 hε1 φ hφ hC0 hφsupp hK hdecay
        hsmall g hg hC' n)
    (fun hp T A B hA hB h2 hinf g => ellp_vector_interpolation_family hp T A B hA hB h2 hinf g)
    hp f

end

end Work.BourgainPlan.IonescuWainger
