import Mathlib.Topology.UniformSpace.Uniformizable
import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.BoseSWE.chiSmallGradHolder
import Submission.Work.SmallBoxSliding.Sliding
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# The weighted `L²` mass of the gradient of the small-window cutoff

`Work.BoseSWE.chiScaleSqMulGradC`.  For every `M ≥ 2` there is `K ≥ 0` such that for all
`ℓ, d > 0`, all shifts `u` and all `x`,

    ∫_x χ(x/ℓ)² · ‖∇_x χ_M(x/(ℓd) − u)‖² dx
      ≤ K·((ℓd)⁻¹)² · (χ_mass)^{(M−1)/M} · ℓ^{3/M} ,

where `χ = chiScale ℓ` is the (ball-supported) corpus bump at scale `ℓ`, `χ_M = chiSmall M` the
cosine-`M`-th-power bump at unit scale, and
`χ_mass = ∫_x χ_{B(u)}(x)² dx = ∫_x (χ(x/ℓ)·χ_M(x/(ℓd) − u))² dx` is the `chiMass` of
`Work.SmallBoxSliding` (`= ∫ χ(x/ℓ)² χ_M(x/(ℓd) − u)² dx`).

## Route

* **Pointwise Hölder gradient bound** (`Work.BoseSWE.chiSmallGradHolder`, PROVED):
  `‖∇(χ_M(s⁻¹· − v)) z‖ ≤ C_M·s⁻¹·(χ_M(s⁻¹ z − v))^{(M−1)/M}` with
  `s = ℓd`, `v = u`, at the constant `C_M = 2Mπκ_M^{1/M}`.  Squaring and multiplying by
  `χ(x/ℓ)² ≥ 0` bounds the integrand pointwise by
  `C_M²(ℓd)⁻²·χ(x/ℓ)²·(χ_M(x/(ℓd) − u))^{2(M−1)/M}`.
* **Monotone integration** (`MeasureTheory.integral_mono_of_nonneg`), the dominating function being
  continuous, compactly supported and bounded, hence integrable
  (`integrable_of_hasCompactSupport_of_bound`).
* **Hölder in the sharp form** (`holder_mass`): for `0 ≤ A, c` (with `A` compactly supported and
  both continuous, say) and `α = (M−1)/M`, `p = M/(M−1)`, `q = M` (conjugate exponents),

      ∫ A² c^{2α} ≤ (∫ A² c²)^{α}·(∫ A²)^{1/M}  ,

  from `integral_mul_le_Lp_mul_Lq_of_nonneg` applied to `F = (A²c²)^α` (`F^p = A²c²`) and
  `G = A^{2/M}` (`G^q = A²`), whose product is `A²c^{2α}`.  Both factors are `MemLp` because they
  are continuous with compact support and bounded (`HasCompactSupport.memLp_of_bound`).
* The two remaining integrals are `∫ χ(x/ℓ)²χ_M(x/(ℓd)−u)² = chiMass` (definition of `chiSmallB`
  and `chiMass`) and the *proved* `∫ χ(x/ℓ)² = ℓ³` (`integral_chiScale_sq`), so that
  `(∫ A²)^{1/M} = (ℓ³)^{1/M} = ℓ^{3/M}`.
-/

noncomputable section

open MeasureTheory Metric Filter
open scoped Real Topology ENNReal

namespace Work.BoseSWE

local notation "E3" => EuclideanSpace ℝ (Fin 3)

set_option autoImplicit false

/-! ## Auxiliary facts about real powers and about integrability -/

/-- `x^2 = x^(2:ℝ)`: the `Nat`-power and the real-power spelling of the square.  (The two are
different terms in Lean — different `HPow` instances — and rewriting between them needs this
bridge as a *term*, since `rw` matches syntactically.) -/
private lemma rpow_two_eq (x : ℝ) : x ^ 2 = x ^ (2:ℝ) := by
  simpa using (Real.rpow_natCast x 2).symm

/-- Bridge between the `Nat`-power and the real-power spelling of the two-factor mass:
`a^(2:ℝ)·b^(2:ℝ) = a²b²`. -/
private lemma sq_rpow_bridge (a b : ℝ) : a ^ (2:ℝ) * b ^ (2:ℝ) = a ^ 2 * b ^ 2 := by
  rw [← rpow_two_eq a, ← rpow_two_eq b]

/-- A continuous function with compact support and a uniform bound is integrable. -/
private lemma integrable_of_hasCompactSupport_of_bound {f : E3 → ℝ} (hf : HasCompactSupport f)
    (hfc : Continuous f) (C : ℝ) (hC : ∀ x, ‖f x‖ ≤ C) : Integrable f := by
  have hml : MemLp f 1 (volume : Measure E3) :=
    HasCompactSupport.memLp_of_bound hf hfc.aestronglyMeasurable C (Eventually.of_forall hC)
  rwa [memLp_one_iff_integrable] at hml

/-! ## The Hölder-type mass inequality -/

/-- **Hölder for the two-factor mass.**  For `2 ≤ M`, nonnegative continuous functions `A`, `c` on
`ℝ³` with `A` compactly supported and bounded by `KA`, `c` bounded by `Kc`,

    ∫_x A(x)²·(c(x)^{(M−1)/M})² dx ≤ (∫_x A(x)²c(x)² dx)^{(M−1)/M}·(∫_x A(x)² dx)^{1/M} .

All powers are real powers `x^y` (`y : ℝ`) so that the exponents `(M−1)/M` and `1/M` combine
freely; the two integrals on the right are the `p`- and `q`-norms of the Hölder factors
`F = (A²c²)^{(M−1)/M}`, `G = A^{2/M}`. -/
private lemma holder_mass {M : ℕ} (hM : 2 ≤ M) {A c : E3 → ℝ}
    (hA0 : ∀ x, 0 ≤ A x) (hc0 : ∀ x, 0 ≤ c x)
    (hAc : Continuous A) (hcc : Continuous c) (hAcomp : HasCompactSupport A)
    {KA Kc : ℝ} (hKA0 : 0 ≤ KA) (hKc0 : 0 ≤ Kc)
    (hKA : ∀ x, A x ≤ KA) (hKc : ∀ x, c x ≤ Kc) :
    (∫ x, A x ^ (2:ℝ) * (c x ^ (((M:ℝ) - 1) / (M:ℝ))) ^ (2:ℝ))
      ≤ (∫ x, A x ^ (2:ℝ) * c x ^ (2:ℝ)) ^ (((M:ℝ) - 1) / (M:ℝ))
        * (∫ x, A x ^ (2:ℝ)) ^ (1 / (M:ℝ)) := by
  have hM2 : (2:ℝ) ≤ (M:ℝ) := by exact_mod_cast hM
  have hM0 : (M:ℝ) ≠ 0 := by positivity
  have hM1 : (M:ℝ) - 1 ≠ 0 := by linarith
  set α : ℝ := ((M:ℝ) - 1) / (M:ℝ) with hα
  set p : ℝ := (M:ℝ) / ((M:ℝ) - 1) with hp
  set q : ℝ := (M:ℝ) with hq
  have hαpos : 0 < α := by rw [hα]; exact div_pos (by linarith) (by linarith)
  have hpq : p.HolderConjugate q := by
    rw [Real.holderConjugate_iff]
    refine ⟨?_, ?_⟩
    · rw [hp, hq, lt_div_iff₀ (by linarith : (0:ℝ) < (M:ℝ) - 1)]
      linarith
    · rw [hp, hq]
      field_simp
      ring
  have h1p : 1/p = α := by rw [hp, hα, one_div, inv_div]
  have h1q : 1/q = 1/(M:ℝ) := by rw [hq]
  have hαp : α * p = 1 := by rw [hp, hα]; field_simp
  have hbase0 : ∀ x, 0 ≤ A x ^ (2:ℝ) * c x ^ (2:ℝ) := fun x =>
    mul_nonneg (Real.rpow_nonneg (hA0 x) _) (Real.rpow_nonneg (hc0 x) _)
  have hαne : α ≠ 0 := ne_of_gt hαpos
  have hβne : (2/(M:ℝ)) ≠ 0 := by positivity
  have htwone : (2:ℝ) ≠ 0 := by norm_num
  have hsumα : 2 * α + 2 / (M:ℝ) = (2:ℝ) := by rw [hα]; field_simp; ring
  have step1 : ∀ x, (A x ^ (2:ℝ) * c x ^ (2:ℝ)) ^ α = A x ^ (2*α) * (c x ^ α) ^ (2:ℝ) := by
    intro x
    rw [Real.mul_rpow (Real.rpow_nonneg (hA0 x) _) (Real.rpow_nonneg (hc0 x) _)]
    congr 1
    · exact (Real.rpow_mul (hA0 x) (2:ℝ) α).symm
    · calc (c x ^ (2:ℝ)) ^ α = c x ^ ((2:ℝ) * α) := (Real.rpow_mul (hc0 x) (2:ℝ) α).symm
        _ = c x ^ (α * 2) := by ring_nf
        _ = (c x ^ α) ^ (2:ℝ) := Real.rpow_mul (hc0 x) α (2:ℝ)
  have step2 : ∀ x, A x ^ (2*α) * A x ^ (2/(M:ℝ)) = A x ^ (2:ℝ) := by
    intro x
    rcases eq_or_lt_of_le (hA0 x) with h0 | hpos
    · rw [← h0]
      rw [Real.zero_rpow (mul_ne_zero htwone hαne), Real.zero_rpow hβne, Real.zero_rpow htwone]
      ring
    · rw [← Real.rpow_add hpos (2*α) (2/(M:ℝ)), hsumα]
  have hidFG : ∀ x, (A x ^ (2:ℝ) * c x ^ (2:ℝ)) ^ α * A x ^ (2/(M:ℝ))
      = A x ^ (2:ℝ) * (c x ^ α) ^ (2:ℝ) := by
    intro x
    calc (A x ^ (2:ℝ) * c x ^ (2:ℝ)) ^ α * A x ^ (2/(M:ℝ))
        = (A x ^ (2*α) * (c x ^ α) ^ (2:ℝ)) * A x ^ (2/(M:ℝ)) := by rw [step1 x]
      _ = (c x ^ α) ^ (2:ℝ) * (A x ^ (2*α) * A x ^ (2/(M:ℝ))) := by ring
      _ = (c x ^ α) ^ (2:ℝ) * A x ^ (2:ℝ) := by rw [step2 x]
      _ = A x ^ (2:ℝ) * (c x ^ α) ^ (2:ℝ) := by ring
  have hidFp : ∀ x, ((A x ^ (2:ℝ) * c x ^ (2:ℝ)) ^ α) ^ p = A x ^ (2:ℝ) * c x ^ (2:ℝ) := by
    intro x
    rw [← Real.rpow_mul (hbase0 x) α p, hαp, Real.rpow_one]
  have hidGq : ∀ x, (A x ^ (2/(M:ℝ))) ^ q = A x ^ (2:ℝ) := by
    intro x
    rw [← Real.rpow_mul (hA0 x) (2/(M:ℝ)) q]
    have hsum : 2 / (M:ℝ) * q = (2:ℝ) := by rw [hq]; field_simp
    rw [hsum]
  set F : E3 → ℝ := fun x => (A x ^ (2:ℝ) * c x ^ (2:ℝ)) ^ α with hF
  set G : E3 → ℝ := fun x => A x ^ (2/(M:ℝ)) with hG
  have hFnn : ∀ x, 0 ≤ F x := fun x => Real.rpow_nonneg (hbase0 x) _
  have hGnn : ∀ x, 0 ≤ G x := fun x => Real.rpow_nonneg (hA0 x) _
  have hFc : Continuous F := by
    rw [hF]
    exact ((hAc.rpow_const (fun _ => Or.inr (by positivity : (0:ℝ) ≤ 2))).mul
        (hcc.rpow_const (fun _ => Or.inr (by positivity : (0:ℝ) ≤ 2)))).rpow_const
      (fun _ => Or.inr (le_of_lt hαpos))
  have hGc : Continuous G := by
    rw [hG]
    exact hAc.rpow_const (fun _ => Or.inr (by positivity : (0:ℝ) ≤ 2 / (M:ℝ)))
  have hFsup : ∀ x, ‖F x‖ ≤ (KA ^ (2:ℝ) * Kc ^ (2:ℝ)) ^ α := by
    intro x
    rw [Real.norm_of_nonneg (hFnn x)]
    refine Real.rpow_le_rpow (hbase0 x) ?_ (le_of_lt hαpos)
    exact mul_le_mul
      (Real.rpow_le_rpow (hA0 x) (hKA x) (by norm_num))
      (Real.rpow_le_rpow (hc0 x) (hKc x) (by norm_num))
      (Real.rpow_nonneg (hc0 x) _) (Real.rpow_nonneg hKA0 _)
  have hGsup : ∀ x, ‖G x‖ ≤ KA ^ (2/(M:ℝ)) := by
    intro x
    rw [Real.norm_of_nonneg (hGnn x)]
    exact Real.rpow_le_rpow (hA0 x) (hKA x) (by positivity)
  have hFcomp : HasCompactSupport F := by
    rw [hF]
    refine HasCompactSupport.intro hAcomp.isCompact (fun x hx => ?_)
    have hx0 : A x = 0 := image_eq_zero_of_notMem_tsupport hx
    rw [hx0]
    simp [Real.zero_rpow hαne]
  have hGcomp : HasCompactSupport G := by
    rw [hG]
    refine HasCompactSupport.intro hAcomp.isCompact (fun x hx => ?_)
    have hx0 : A x = 0 := image_eq_zero_of_notMem_tsupport hx
    rw [hx0]
    simp [Real.zero_rpow hβne]
  have hFmem : MemLp F (ENNReal.ofReal p) (volume : Measure E3) :=
    HasCompactSupport.memLp_of_bound hFcomp hFc.aestronglyMeasurable _
      (Eventually.of_forall hFsup)
  have hGmem : MemLp G (ENNReal.ofReal q) (volume : Measure E3) :=
    HasCompactSupport.memLp_of_bound hGcomp hGc.aestronglyMeasurable _
      (Eventually.of_forall hGsup)
  have hH := integral_mul_le_Lp_mul_Lq_of_nonneg (μ := (volume : Measure E3)) hpq
    (Eventually.of_forall hFnn) (Eventually.of_forall hGnn) hFmem hGmem
  have hL : (∫ x, F x * G x) = ∫ x, A x ^ (2:ℝ) * (c x ^ α) ^ (2:ℝ) := by
    refine integral_congr_ae (Eventually.of_forall (fun x => ?_))
    rw [hF, hG]; exact hidFG x
  have hRp : (∫ x, F x ^ p) = ∫ x, A x ^ (2:ℝ) * c x ^ (2:ℝ) := by
    refine integral_congr_ae (Eventually.of_forall (fun x => ?_))
    rw [hF]; exact hidFp x
  have hRq : (∫ x, G x ^ q) = ∫ x, A x ^ (2:ℝ) := by
    refine integral_congr_ae (Eventually.of_forall (fun x => ?_))
    rw [hG]; exact hidGq x
  rw [hL, hRp, hRq, h1p, h1q] at hH
  exact hH

/-- **Integrability of the mass integrand** `A²·(c^{(M−1)/M})²` under the hypotheses of
`holder_mass`: it is continuous with compact support (contained in `tsupport A`) and bounded. -/
private lemma integrable_mass_chi {M : ℕ} (hM : 2 ≤ M) {A c : E3 → ℝ}
    (hA0 : ∀ x, 0 ≤ A x) (hc0 : ∀ x, 0 ≤ c x)
    (hAc : Continuous A) (hcc : Continuous c) (hAcomp : HasCompactSupport A)
    {KA Kc : ℝ} (hKA0 : 0 ≤ KA) (hKc0 : 0 ≤ Kc)
    (hKA : ∀ x, A x ≤ KA) (hKc : ∀ x, c x ≤ Kc) :
    Integrable (fun x : E3 => A x ^ (2:ℝ) * (c x ^ (((M:ℝ) - 1) / (M:ℝ))) ^ (2:ℝ)) := by
  have hM2 : (2:ℝ) ≤ (M:ℝ) := by exact_mod_cast hM
  have hM0 : (M:ℝ) ≠ 0 := by positivity
  set α : ℝ := ((M:ℝ) - 1) / (M:ℝ) with hα
  have hαpos : 0 < α := by rw [hα]; exact div_pos (by linarith) (by linarith)
  refine integrable_of_hasCompactSupport_of_bound ?_ ?_ (KA ^ (2:ℝ) * (Kc ^ α) ^ (2:ℝ)) ?_
  · refine HasCompactSupport.intro hAcomp.isCompact (fun x hx => ?_)
    have hx0 : A x = 0 := image_eq_zero_of_notMem_tsupport hx
    rw [hx0, Real.zero_rpow (by norm_num : (2:ℝ) ≠ 0)]
    ring
  · exact (hAc.rpow_const (fun _ => Or.inr (by norm_num : (0:ℝ) ≤ 2))).mul
      ((hcc.rpow_const (fun _ => Or.inr (le_of_lt hαpos))).rpow_const
        (fun _ => Or.inr (by norm_num : (0:ℝ) ≤ 2)))
  · intro x
    have h1 : 0 ≤ A x ^ (2:ℝ) := Real.rpow_nonneg (hA0 x) 2
    have h2 : 0 ≤ (c x ^ α) ^ (2:ℝ) := Real.rpow_nonneg (Real.rpow_nonneg (hc0 x) α) 2
    have h3 : A x ^ (2:ℝ) ≤ KA ^ (2:ℝ) := Real.rpow_le_rpow (hA0 x) (hKA x) (by norm_num)
    have h4 : (c x ^ α) ^ (2:ℝ) ≤ (Kc ^ α) ^ (2:ℝ) :=
      Real.rpow_le_rpow (Real.rpow_nonneg (hc0 x) α)
        (Real.rpow_le_rpow (hc0 x) (hKc x) (le_of_lt hαpos)) (by norm_num)
    rw [Real.norm_of_nonneg (mul_nonneg h1 h2)]
    exact mul_le_mul h3 h4 h2 (Real.rpow_nonneg hKA0 2)

/-! ## The target theorem -/

theorem chiScaleSqMulGradC {M : ℕ} (hM : 2 ≤ M) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ (ℓ d : ℝ), 0 < ℓ → 0 < d →
      ∀ u : EuclideanSpace ℝ (Fin 3),
        (∫ x : EuclideanSpace ℝ (Fin 3),
            (Submission.BoseGases.chiScale ℓ x) ^ 2
              * ‖fderiv ℝ (fun w : EuclideanSpace ℝ (Fin 3) =>
                  Submission.BoseGases.chiSmall M ((ℓ * d)⁻¹ • w - u)) x‖ ^ 2)
          ≤ K * ((ℓ * d)⁻¹) ^ 2
              * (Work.SmallBoxSliding.chiMass M ℓ d u) ^ (((M : ℝ) - 1) / M)
              * ℓ ^ (3 / (M : ℝ)) := by
  obtain ⟨C, hC0, hCgrad⟩ := chiSmallGradHolder M hM
  refine ⟨C ^ 2, sq_nonneg C, ?_⟩
  intro ℓ d hℓ hd u
  have hs0 : 0 < ℓ * d := mul_pos hℓ hd
  have hM2 : (2:ℝ) ≤ (M:ℝ) := by exact_mod_cast hM
  set s : ℝ := ℓ * d with hs
  set α : ℝ := ((M : ℝ) - 1) / (M : ℝ) with hα
  set A : E3 → ℝ := fun x => Submission.BoseGases.chiScale ℓ x with hAdef
  set c : E3 → ℝ := fun w => Submission.BoseGases.chiSmall M (s⁻¹ • w - u) with hcdef
  have hαpos : 0 < α := by rw [hα]; exact div_pos (by linarith) (by linarith)
  have hA0 : ∀ x, 0 ≤ A x := fun x => by
    rw [hAdef]; exact Submission.BoseGases.chiScale_nonneg ℓ x
  have hc0 : ∀ x, 0 ≤ c x := fun x => by
    rw [hcdef]; exact Submission.BoseGases.chiSmall_nonneg M _
  have hAc : Continuous A := by
    rw [hAdef]
    exact (Submission.BoseGases.chiScale_contDiff (ne_of_gt hℓ)).continuous
  have hcc : Continuous c := by
    rw [hcdef]
    exact (Submission.BoseGases.chiSmall_continuous (M := M) (by omega)).comp
      (((continuous_const : Continuous fun _ : E3 => s⁻¹).smul continuous_id).sub continuous_const)
  have hAcomp : HasCompactSupport A := by
    rw [hAdef]
    exact Submission.BoseGases.chiScale_hasCompactSupport (ne_of_gt hℓ)
  have hKc0 : (0:ℝ) ≤ Submission.BoseGases.chiSmallNormFactor M :=
    Submission.BoseGases.chiSmallNormFactor_nonneg M
  have hKA : ∀ x, A x ≤ Submission.BoseGases.chiSupAbs := fun x => by
    rw [hAdef]
    exact le_trans (le_abs_self _) (Submission.BoseGases.chiScale_abs_le_sup ℓ x)
  have hKc : ∀ x, c x ≤ Submission.BoseGases.chiSmallNormFactor M := fun x => by
    rw [hcdef]
    calc Submission.BoseGases.chiSmall M (s⁻¹ • x - u)
        = Submission.BoseGases.chiSmallNormFactor M *
            Submission.BoseGases.chiSmallBase M (s⁻¹ • x - u) :=
          chiSmall_eq_normFactor_mul_base M _
      _ ≤ Submission.BoseGases.chiSmallNormFactor M * 1 :=
          mul_le_mul_of_nonneg_left (Submission.BoseGases.chiSmallBase_le_one M _) hKc0
      _ = Submission.BoseGases.chiSmallNormFactor M := mul_one _
  -- the pointwise Hölder gradient bound at the scale `s = ℓd`
  have hgrad : ∀ x, ‖fderiv ℝ c x‖ ≤ C * s⁻¹ * (c x) ^ α := by
    intro x
    have h := hCgrad s hs0 u x
    rw [← hcdef] at h
    exact h
  -- squaring and inserting the weight `χ(x/ℓ)² ≥ 0`
  have hpt : ∀ x, (A x) ^ 2 * ‖fderiv ℝ c x‖ ^ 2
      ≤ C ^ 2 * s⁻¹ ^ 2 * ((A x) ^ 2 * (c x ^ α) ^ 2) := by
    intro x
    have h1 : ‖fderiv ℝ c x‖ ^ 2 ≤ (C * s⁻¹ * (c x) ^ α) ^ 2 :=
      pow_le_pow_left₀ (norm_nonneg _) (hgrad x) 2
    calc (A x) ^ 2 * ‖fderiv ℝ c x‖ ^ 2
        ≤ (A x) ^ 2 * (C * s⁻¹ * (c x) ^ α) ^ 2 := mul_le_mul_of_nonneg_left h1 (sq_nonneg _)
      _ = C ^ 2 * s⁻¹ ^ 2 * ((A x) ^ 2 * (c x ^ α) ^ 2) := by ring
  have hIntMassR : Integrable (fun x : E3 => A x ^ (2:ℝ) * (c x ^ α) ^ (2:ℝ)) :=
    integrable_mass_chi hM hA0 hc0 hAc hcc hAcomp Submission.BoseGases.chiSupAbs_nonneg hKc0
      hKA hKc
  have hIntMass : Integrable (fun x : E3 => (A x) ^ 2 * (c x ^ α) ^ 2) :=
    hIntMassR.congr (Eventually.of_forall (fun x => sq_rpow_bridge (A x) (c x ^ α)))
  have hIntUb : Integrable
      (fun x : E3 => C ^ 2 * s⁻¹ ^ 2 * ((A x) ^ 2 * (c x ^ α) ^ 2)) :=
    hIntMass.const_mul _
  have hmono : (∫ x : E3, (A x) ^ 2 * ‖fderiv ℝ c x‖ ^ 2)
      ≤ ∫ x : E3, C ^ 2 * s⁻¹ ^ 2 * ((A x) ^ 2 * (c x ^ α) ^ 2) :=
    integral_mono_of_nonneg (Eventually.of_forall (fun x => mul_nonneg (sq_nonneg _) (sq_nonneg _)))
      hIntUb (Eventually.of_forall hpt)
  have hconst : (∫ x : E3, C ^ 2 * s⁻¹ ^ 2 * ((A x) ^ 2 * (c x ^ α) ^ 2))
      = C ^ 2 * s⁻¹ ^ 2 * (∫ x : E3, (A x) ^ 2 * (c x ^ α) ^ 2) :=
    integral_const_mul _ _
  have hmass2 : (∫ x : E3, (A x) ^ 2 * (c x ^ α) ^ 2)
      = ∫ x : E3, A x ^ (2:ℝ) * (c x ^ α) ^ (2:ℝ) :=
    integral_congr_ae (Eventually.of_forall (fun x => (sq_rpow_bridge (A x) (c x ^ α)).symm))
  -- Hölder
  have hholder := holder_mass hM hA0 hc0 hAc hcc hAcomp
    Submission.BoseGases.chiSupAbs_nonneg hKc0 hKA hKc
  -- the mass integral is `chiMass`
  have hmass : (∫ x : E3, A x ^ (2:ℝ) * c x ^ (2:ℝ))
      = Work.SmallBoxSliding.chiMass M ℓ d u := by
    rw [Work.SmallBoxSliding.chiMass_def]
    refine integral_congr_ae (Eventually.of_forall (fun x => ?_))
    simp only [hAdef, hcdef, Submission.BoseGases.chiSmallB]
    rw [← rpow_two_eq (Submission.BoseGases.chiScale ℓ x),
      ← rpow_two_eq (Submission.BoseGases.chiSmall M (s⁻¹ • x - u))]
    ring
  -- `∫ A² = ℓ³`
  have hAeq : (∫ x : E3, A x ^ (2:ℝ)) = ℓ ^ 3 := by
    have hpt2 : ∀ x : E3, A x ^ (2:ℝ) = (Submission.BoseGases.chiScale ℓ x) ^ 2 := by
      intro x
      rw [hAdef]
      exact (rpow_two_eq (Submission.BoseGases.chiScale ℓ x)).symm
    refine (integral_congr_ae (Eventually.of_forall hpt2)).trans ?_
    exact Submission.BoseGases.integral_chiScale_sq hℓ
  have hrpow : (∫ x : E3, A x ^ (2:ℝ)) ^ (1 / (M:ℝ)) = ℓ ^ (3 / (M:ℝ)) := by
    have hbase : (ℓ ^ 3 : ℝ) = ℓ ^ (3:ℝ) := by
      simpa using (Real.rpow_natCast ℓ 3).symm
    rw [hAeq, hbase, ← Real.rpow_mul (le_of_lt hℓ) (3:ℝ) (1 / (M:ℝ)), mul_one_div]
  rw [hmass, hrpow] at hholder
  calc (∫ x : E3, (A x) ^ 2 * ‖fderiv ℝ c x‖ ^ 2)
      ≤ ∫ x : E3, C ^ 2 * s⁻¹ ^ 2 * ((A x) ^ 2 * (c x ^ α) ^ 2) := hmono
    _ = C ^ 2 * s⁻¹ ^ 2 * (∫ x : E3, (A x) ^ 2 * (c x ^ α) ^ 2) := hconst
    _ = C ^ 2 * s⁻¹ ^ 2 * (∫ x : E3, A x ^ (2:ℝ) * (c x ^ α) ^ (2:ℝ)) := by rw [hmass2]
    _ ≤ C ^ 2 * s⁻¹ ^ 2 * ((Work.SmallBoxSliding.chiMass M ℓ d u) ^ α * ℓ ^ (3 / (M:ℝ))) :=
        mul_le_mul_of_nonneg_left hholder (mul_nonneg (sq_nonneg _) (sq_nonneg _))
    _ = C ^ 2 * s⁻¹ ^ 2 * (Work.SmallBoxSliding.chiMass M ℓ d u) ^ α * ℓ ^ (3 / (M:ℝ)) := by
        ring

end Work.BoseSWE
