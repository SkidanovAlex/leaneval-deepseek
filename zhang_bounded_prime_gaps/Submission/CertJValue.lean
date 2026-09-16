import Mathlib
import Submission.CertAnalytic
import Submission.SimplexMarginal
import Submission.MargProfile
import Submission.MargIntegral
import Submission.Commons.MeasureTheory.Integral.beta_integral_scaled

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

open MeasureTheory Finset
open scoped BigOperators

/-!
# The `J`-side of the `k = 50` certificate

Evaluation of `Σ_i JFunc 50 i (24/25) certFun`: the marginal decomposition of the certificate
polynomial (`lmono_insAt`) turns the inner integral `∫_x certFun(insAt i x u)` into the explicit
polynomial `certH u` (one term per basis element `j` and per part `v` of its signature, with the
beta-integral coefficient `kappa (certA j) v` and the exponent `certA j + v + 1`), and the square
of `certH` is then integrated term by term with the shifted simplex master formula
`simplex_integral_lmono_shifted`.
-/

namespace Commons.NumberTheory.MaynardSieve

noncomputable section

/-- The coefficient of the `(j,v)`-term of the marginal function `certH`. -/
def certJCoef (j : Fin 1780) (v : ℕ) : ℝ :=
  (certCl j : ℝ) * (if v = 0 then 1 else ((certSig j).count v : ℝ)) * kappa (certA j) v

/-- The exponent of `26/25 - Σu` in the `(j,v)`-term. -/
def certJExp (j : Fin 1780) (v : ℕ) : ℕ := certA j + v + 1

/-- The signature of the `(j,v)`-term. -/
def certJBeta (j : Fin 1780) (v : ℕ) : List ℕ := eraseOne (certSig j) v

/-- The exponent sum `N = ã + ã'` of a pair of `certH`-terms. -/
def certJN (j : Fin 1780) (v : ℕ) (j' : Fin 1780) (v' : ℕ) : ℕ :=
  certJExp j v + certJExp j' v'

/-- The weight sum `L = |β| + |β'|` of a pair of `certH`-terms. -/
def certJL (j : Fin 1780) (v : ℕ) (j' : Fin 1780) (v' : ℕ) : ℕ :=
  (certJBeta j v).sum + (certJBeta j' v').sum

/-- The marginal function of the certificate: `∫_x certFun(insAt i x u)`. -/
def certH (u : Fin 49 → ℝ) : ℝ :=
  ∑ j : Fin 1780, ∑ v ∈ (0 :: (certSig j).dedup).toFinset,
    certJCoef j v * (((26 : ℝ) / 25) - ∑ l : Fin 49, u l) ^ (certJExp j v) *
      lmono (certJBeta j v) 49 u

/-- The membership condition of the certificate simplex after inserting a coordinate. -/
theorem mem_simplexC_insAt (i : Fin 50) (x : ℝ) (u : Fin 49 → ℝ) :
    (insAt i x u ∈ simplexC 50 ((26 : ℝ) / 25))
      ↔ ((∀ j : Fin 49, 0 ≤ u j) ∧ 0 ≤ x ∧ x + ∑ j, u j ≤ (26 : ℝ) / 25) := by
  simp only [simplexC, Set.mem_ofPred_eq]
  constructor
  · intro h
    obtain ⟨h1, h2⟩ := h
    obtain ⟨hx, hu⟩ := (nonneg_insAt i x u).mp h1
    exact ⟨hu, hx, by rw [← sum_insAt i x u]; exact h2⟩
  · rintro ⟨hu, hx, hsum⟩
    exact ⟨(nonneg_insAt i x u).mpr ⟨hx, hu⟩, by rw [sum_insAt i x u]; exact hsum⟩

/-- Pointwise form of the certificate along the line `x ↦ insAt i x u`, for `u` in the marginal
simplex. -/
theorem certFun_insAt_of_mem (i : Fin 50) (u : Fin 49 → ℝ)
    (hu : u ∈ simplexC 49 ((24 : ℝ) / 25)) (x : ℝ) :
    certFun (insAt i x u)
      = certPoly (insAt i x u) *
          (if x ∈ Set.Icc (0 : ℝ) (((26 : ℝ) / 25) - ∑ l, u l) then 1 else 0) := by
  classical
  have hu1 : ∀ l : Fin 49, 0 ≤ u l := hu.1
  have hu2 : ∑ l : Fin 49, u l ≤ (24 : ℝ) / 25 := hu.2
  rw [certFun, Set.indicator_apply]
  by_cases h : insAt i x u ∈ simplexC 50 ((26 : ℝ) / 25)
  · rw [if_pos h]
    obtain ⟨-, hx0, hxs⟩ := (mem_simplexC_insAt i x u).mp h
    rw [if_pos ⟨hx0, by linarith⟩, mul_one]
  · rw [if_neg h, if_neg, mul_zero]
    rintro ⟨hx0, hxs⟩
    exact h ((mem_simplexC_insAt i x u).mpr ⟨hu1, hx0, by linarith⟩)

/-- The line `x ↦ insAt i x u` is continuous. -/
theorem continuous_insAt (i : Fin 50) (u : Fin 49 → ℝ) :
    Continuous (fun x : ℝ => insAt i x u) := by
  rw [continuous_pi_iff]
  intro j
  by_cases h : j = i
  · simp only [insAt, dif_pos h]; exact continuous_id
  · simp only [insAt, dif_neg h]; exact continuous_const

/-- Pulling constants out of the beta integral: `∫₀^L c·(L-x)^a·(x^v·g) = c·g·κ·L^{a+v+1}`. -/
theorem interval_integral_const_beta (a v : ℕ) (c g : ℝ) (L : ℝ) (hL : 0 ≤ L) :
    ∫ x in (0 : ℝ)..L, c * ((L - x) ^ a * (x ^ v * g))
      = c * g * (kappa a v * L ^ (a + v + 1)) := by
  have h1 : (fun x : ℝ => c * ((L - x) ^ a * (x ^ v * g)))
      = fun x : ℝ => c * ((L - x) ^ a * x ^ v * g) := by funext x; ring
  rw [h1, intervalIntegral.integral_const_mul]
  rw [show (fun x : ℝ => (L - x) ^ a * x ^ v * g)
      = fun x : ℝ => ((L - x) ^ a * x ^ v) * g from rfl]
  rw [intervalIntegral.integral_mul_const, Commons.MeasureTheory.Integral.beta_integral_scaled hL a v,
    kappa]
  ring

/-- The inner integral of a single basis element of the certificate. -/
theorem integral_certTerm_of_mem (i : Fin 50) (u : Fin 49 → ℝ)
    (_hu : u ∈ simplexC 49 ((24 : ℝ) / 25)) (L : ℝ) (hL : 0 ≤ L) (j : Fin 1780) :
    ∫ x in (0 : ℝ)..L, (certCl j : ℝ) * (L - x) ^ (certA j) * lmono (certSig j) 50 (insAt i x u)
      = ∑ v ∈ (0 :: (certSig j).dedup).toFinset,
          certJCoef j v * L ^ (certJExp j v) * lmono (certJBeta j v) 49 u := by
  have hsplit : (fun x : ℝ => (certCl j : ℝ) * (L - x) ^ (certA j)
        * lmono (certSig j) 50 (insAt i x u))
      = fun x : ℝ => ∑ v ∈ (0 :: (certSig j).dedup).toFinset,
          ((certCl j : ℝ) * (if v = 0 then 1 else ((certSig j).count v : ℝ)))
            * ((L - x) ^ (certA j) * (x ^ v * lmono (eraseOne (certSig j) v) 49 u)) := by
    funext x
    rw [lmono_insAt (certSig j) (certSig_notMem_zero j) i x u, Finset.mul_sum]
    refine Finset.sum_congr rfl (fun v _ => ?_)
    ring
  rw [hsplit, intervalIntegral.integral_finsetSum]
  · refine Finset.sum_congr rfl (fun v _ => ?_)
    rw [show (fun x : ℝ => (certCl j : ℝ) * (if v = 0 then 1 else ((certSig j).count v : ℝ))
          * ((L - x) ^ (certA j) * (x ^ v * lmono (eraseOne (certSig j) v) 49 u)))
        = fun x : ℝ => ((certCl j : ℝ) * (if v = 0 then 1 else ((certSig j).count v : ℝ)))
            * ((L - x) ^ (certA j) * (x ^ v * lmono (eraseOne (certSig j) v) 49 u)) from rfl]
    rw [interval_integral_const_beta (certA j) v _ _ L hL]
    rw [certJCoef, certJExp, certJBeta]
    ring
  · intro v _
    have hc : Continuous (fun x : ℝ => (certCl j : ℝ)
        * (if v = 0 then 1 else ((certSig j).count v : ℝ))
        * ((L - x) ^ (certA j) * (x ^ v * lmono (eraseOne (certSig j) v) 49 u))) := by
      refine Continuous.mul (Continuous.mul continuous_const continuous_const) ?_
      refine Continuous.mul ((continuous_const.sub continuous_id).pow _) ?_
      exact Continuous.mul (continuous_id.pow _) continuous_const
    exact hc.intervalIntegrable _ _

/-- **The inner integral of the certificate**: `∫_x certFun(insAt i x u) = certH u` on the
marginal simplex. -/
theorem integral_certFun_insAt (i : Fin 50) (u : Fin 49 → ℝ)
    (hu : u ∈ simplexC 49 ((24 : ℝ) / 25)) :
    ∫ x : ℝ, certFun (insAt i x u) = certH u := by
  classical
  set L : ℝ := (26 : ℝ) / 25 - ∑ l : Fin 49, u l with hLdef
  have hL : 0 ≤ L := by rw [hLdef]; linarith [hu.2]
  have hstep1 : (∫ x : ℝ, certFun (insAt i x u))
      = ∫ x in Set.Icc (0:ℝ) L, certPoly (insAt i x u) := by
    rw [show (∫ x : ℝ, certFun (insAt i x u))
        = ∫ x : ℝ, certPoly (insAt i x u) * (if x ∈ Set.Icc (0:ℝ) L then 1 else 0) from
      MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall (fun x => by
        show certFun (insAt i x u)
          = certPoly (insAt i x u) * (if x ∈ Set.Icc (0 : ℝ) L then 1 else 0)
        rw [certFun_insAt_of_mem i u hu x, hLdef]))]
    rw [← MeasureTheory.integral_indicator measurableSet_Icc]
    refine MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall (fun x => ?_))
    show certPoly (insAt i x u) * (if x ∈ Set.Icc (0 : ℝ) L then 1 else 0)
      = (Set.Icc (0 : ℝ) L).indicator (fun x => certPoly (insAt i x u)) x
    by_cases h : x ∈ Set.Icc (0:ℝ) L
    · rw [Set.indicator_of_mem h, if_pos h, mul_one]
    · rw [Set.indicator_of_notMem h, if_neg h, mul_zero]
  have hstep2 : (∫ x in Set.Icc (0:ℝ) L, certPoly (insAt i x u))
      = ∫ x in (0:ℝ)..L, certPoly (insAt i x u) := by
    rw [intervalIntegral.integral_of_le hL]
    exact MeasureTheory.setIntegral_congr_set
      (MeasureTheory.Ioc_ae_eq_Icc (μ := volume) (a := (0:ℝ)) (b := L)).symm
  rw [hstep1, hstep2]
  have hpoly : (∫ x in (0:ℝ)..L, certPoly (insAt i x u))
      = ∫ x in (0:ℝ)..L, ∑ j : Fin 1780, (certCl j : ℝ) * (L - x) ^ (certA j)
          * lmono (certSig j) 50 (insAt i x u) := by
    refine intervalIntegral.integral_congr (fun x _ => ?_)
    rw [certPoly]
    refine Finset.sum_congr rfl (fun j _ => ?_)
    rw [sum_insAt i x u]
    have h1 : ((26 : ℝ) / 25 - (x + ∑ l : Fin 49, u l)) = L - x := by rw [hLdef]; ring
    rw [h1]
  rw [hpoly, intervalIntegral.integral_finsetSum]
  · rw [certH]
    exact Finset.sum_congr rfl (fun j _ => integral_certTerm_of_mem i u hu L hL j)
  · intro j _
    have hcont : Continuous (fun x : ℝ => (certCl j : ℝ) * (L - x) ^ (certA j)
        * lmono (certSig j) 50 (insAt i x u)) :=
      Continuous.mul (Continuous.mul continuous_const
        ((continuous_const.sub continuous_id).pow _))
        ((continuous_lmono _ _).comp (continuous_insAt i u))
    exact hcont.intervalIntegrable _ _

/-- **The shifted simplex master formula at `ε = 1/25`.** -/
theorem simplex_integral_cert (k N : ℕ) (β β' : List ℕ) :
    ∫ t in simplexC k ((24 : ℝ) / 25),
        (((26 : ℝ) / 25) - ∑ i, t i) ^ N * lmono β k t * lmono β' k t
      = ∑ jj ∈ Finset.range (N + 1), ((N.choose jj : ℕ) : ℝ) * ((2 : ℝ) / 25) ^ jj *
          (((24 : ℝ) / 25) ^ (k + (N - jj) + β.sum + β'.sum) * ((N - jj).factorial : ℝ) *
            (Slab β β' k : ℝ) /
              ((((N - jj) + β.sum + β'.sum + k).factorial : ℕ) : ℝ)) := by
  have hset : simplexC k ((24 : ℝ) / 25)
      = {u : Fin k → ℝ | (∀ i, 0 ≤ u i) ∧ ∑ i, u i ≤ 1 - ((1 : ℝ) / 25)} := by
    ext u
    simp only [simplexC, Set.mem_ofPred_eq]
    constructor <;> rintro ⟨h1, h2⟩ <;> exact ⟨h1, by linarith⟩
  have hgoal : (∫ t in simplexC k ((24 : ℝ) / 25),
        (((26 : ℝ) / 25) - ∑ i, t i) ^ N * lmono β k t * lmono β' k t)
      = ∫ t in {u : Fin k → ℝ | (∀ i, 0 ≤ u i) ∧ ∑ i, u i ≤ 1 - ((1 : ℝ) / 25)},
          (1 + ((1 : ℝ) / 25) - ∑ i, t i) ^ N * lmono β k t * lmono β' k t := by
    rw [hset]
    refine MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall (fun t => ?_))
    ring
  have h := Commons.NumberTheory.MaynardSieve.simplex_integral_lmono_shifted
    (k := k) (eps := ((1 : ℝ) / 25)) (by norm_num) (by norm_num) N β β'
  rw [hgoal, h]
  refine Finset.sum_congr rfl (fun jj _ => ?_)
  rw [show (2 : ℝ) * ((1 : ℝ) / 25) = (2 : ℝ) / 25 from by ring,
    show (1 : ℝ) - (1 : ℝ) / 25 = (24 : ℝ) / 25 from by ring]

/-- The `J`-functional of the certificate in `Fin 49` coordinates is the integral of the square
of the marginal function `certH`. -/
theorem JFuncFin_certFun (i : Fin 50) :
    JFuncFin 49 i ((24 : ℝ) / 25) certFun
      = ∫ u in simplexC 49 ((24 : ℝ) / 25), (certH u) ^ 2 := by
  classical
  rw [JFuncFin]
  have hpt : ∀ u : Fin 49 → ℝ,
      (∫ x : ℝ, certFun (insAt i x u)) ^ 2
          * (if u ∈ simplexC 49 ((24 : ℝ) / 25) then 1 else 0)
        = (certH u) ^ 2 * (if u ∈ simplexC 49 ((24 : ℝ) / 25) then 1 else 0) := by
    intro u
    by_cases h : u ∈ simplexC 49 ((24 : ℝ) / 25)
    · rw [if_pos h, integral_certFun_insAt i u h]
    · rw [if_neg h]; ring
  rw [MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall hpt)]
  rw [← MeasureTheory.integral_indicator (isClosed_simplexC 49 _).measurableSet]
  refine MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall (fun u => ?_))
  show (certH u) ^ 2 * (if u ∈ simplexC 49 ((24 : ℝ) / 25) then 1 else 0)
    = (simplexC 49 ((24 : ℝ) / 25)).indicator (fun u => (certH u) ^ 2) u
  by_cases h : u ∈ simplexC 49 ((24 : ℝ) / 25)
  · rw [if_pos h, Set.indicator_of_mem h, mul_one]
  · rw [if_neg h, Set.indicator_of_notMem h, mul_zero]

/-- **The `J`-value of the certificate**: the sum over the `50` marginals is `50` times the
integral of `certH²` over the marginal simplex. -/
theorem sum_JFunc_certFun :
    ∑ i : Fin 50, JFunc 50 i ((24 : ℝ) / 25) certFun
      = 50 * ∫ u in simplexC 49 ((24 : ℝ) / 25), (certH u) ^ 2 := by
  rw [Finset.sum_congr rfl (fun i _ => JFunc_eq_JFuncFin (k := 49) i ((24 : ℝ) / 25) certFun)]
  rw [Finset.sum_congr rfl (fun i _ => JFuncFin_certFun i), Finset.sum_const,
    Finset.card_univ, Fintype.card_fin]
  norm_num

/-- The shifted simplex integral of a pair of `certH`-terms (the polynomial factor omitted). -/
def certJTerm (j : Fin 1780) (v : ℕ) (j' : Fin 1780) (v' : ℕ) : ℝ :=
  ∑ jj ∈ Finset.range (certJN j v j' v' + 1),
    ((certJN j v j' v').choose jj : ℝ) * ((2 : ℝ) / 25) ^ jj *
      (((24 : ℝ) / 25) ^ (49 + (certJN j v j' v' - jj) + (certJBeta j v).sum + (certJBeta j' v').sum) *
        ((certJN j v j' v' - jj).factorial : ℝ) *
          (Slab (certJBeta j v) (certJBeta j' v') 49 : ℝ) /
            ((((certJN j v j' v' - jj) + (certJBeta j v).sum + (certJBeta j' v').sum + 49).factorial : ℕ) : ℝ))

/-- The product of two `certH`-terms is integrable on the marginal simplex. -/
theorem integrableOn_certJpair (j : Fin 1780) (v : ℕ) (j' : Fin 1780) (v' : ℕ) :
    IntegrableOn (fun u : Fin 49 → ℝ => certJCoef j v * certJCoef j' v' *
        ((((26 : ℝ) / 25) - ∑ l, u l) ^ (certJN j v j' v') * lmono (certJBeta j v) 49 u *
          lmono (certJBeta j' v') 49 u)) (simplexC 49 ((24 : ℝ) / 25)) volume := by
  refine ContinuousOn.integrableOn_compact (isCompact_simplexC 49 ((24 : ℝ) / 25)) ?_
  refine Continuous.continuousOn ?_
  refine Continuous.mul (Continuous.mul continuous_const continuous_const) ?_
  refine Continuous.mul (Continuous.mul ((continuous_const.sub
    (continuous_finsetSum _ (fun l _ => continuous_apply l))).pow _)
    (continuous_lmono _ _)) (continuous_lmono _ _)

/-- **The `J`-value of the certificate, in explicit form.** -/
theorem integral_certH_sq :
    ∫ u in simplexC 49 ((24 : ℝ) / 25), (certH u) ^ 2
      = ∑ j : Fin 1780, ∑ j' : Fin 1780,
          ∑ v ∈ (0 :: (certSig j).dedup).toFinset,
          ∑ v' ∈ (0 :: (certSig j').dedup).toFinset,
            certJCoef j v * certJCoef j' v' * certJTerm j v j' v' := by
  classical
  have hsq : ∀ u : Fin 49 → ℝ, (certH u) ^ 2
      = ∑ j : Fin 1780, ∑ j' : Fin 1780,
          ∑ v ∈ (0 :: (certSig j).dedup).toFinset,
          ∑ v' ∈ (0 :: (certSig j').dedup).toFinset,
            certJCoef j v * certJCoef j' v' *
              ((((26 : ℝ) / 25) - ∑ l, u l) ^ (certJN j v j' v') *
                lmono (certJBeta j v) 49 u * lmono (certJBeta j' v') 49 u) := by
    intro u
    rw [certH, sq, Finset.sum_mul_sum]
    refine Finset.sum_congr rfl (fun j _ => ?_)
    refine Finset.sum_congr rfl (fun j' _ => ?_)
    rw [Finset.sum_mul_sum]
    refine Finset.sum_congr rfl (fun v _ => ?_)
    refine Finset.sum_congr rfl (fun v' _ => ?_)
    rw [certJN, pow_add]
    ring
  rw [show (∫ u in simplexC 49 ((24 : ℝ) / 25), (certH u) ^ 2)
      = ∫ u in simplexC 49 ((24 : ℝ) / 25),
          ∑ j : Fin 1780, ∑ j' : Fin 1780,
            ∑ v ∈ (0 :: (certSig j).dedup).toFinset,
            ∑ v' ∈ (0 :: (certSig j').dedup).toFinset,
              certJCoef j v * certJCoef j' v' *
                ((((26 : ℝ) / 25) - ∑ l, u l) ^ (certJN j v j' v') *
                  lmono (certJBeta j v) 49 u * lmono (certJBeta j' v') 49 u) from
    MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall hsq)]
  rw [MeasureTheory.integral_finsetSum]
  · refine Finset.sum_congr rfl (fun j _ => ?_)
    rw [MeasureTheory.integral_finsetSum]
    · refine Finset.sum_congr rfl (fun j' _ => ?_)
      rw [MeasureTheory.integral_finsetSum]
      · refine Finset.sum_congr rfl (fun v _ => ?_)
        rw [MeasureTheory.integral_finsetSum]
        · refine Finset.sum_congr rfl (fun v' _ => ?_)
          rw [MeasureTheory.integral_const_mul,
            simplex_integral_cert 49 (certJN j v j' v') (certJBeta j v) (certJBeta j' v')]
          rw [certJTerm]
        · intro v' _
          exact integrableOn_certJpair j v j' v'
      · intro v _
        exact integrable_finsetSum _ (fun v' _ => integrableOn_certJpair j v j' v')
    · intro j' _
      exact integrable_finsetSum _ (fun v _ =>
        integrable_finsetSum _ (fun v' _ => integrableOn_certJpair j v j' v'))
  · intro j _
    exact integrable_finsetSum _ (fun j' _ =>
      integrable_finsetSum _ (fun v _ =>
        integrable_finsetSum _ (fun v' _ => integrableOn_certJpair j v j' v')))

/-- **The `J`-value of the certificate**: the complete explicit double sum. -/
theorem sum_JFunc_certFun_eq :
    ∑ i : Fin 50, JFunc 50 i ((24 : ℝ) / 25) certFun
      = 50 * (∑ j : Fin 1780, ∑ j' : Fin 1780,
          ∑ v ∈ (0 :: (certSig j).dedup).toFinset,
          ∑ v' ∈ (0 :: (certSig j').dedup).toFinset,
            certJCoef j v * certJCoef j' v' * certJTerm j v j' v') := by
  rw [sum_JFunc_certFun, integral_certH_sq]

/-- The `Ψ`-factor of the `J`-formula (the part not containing `Slab`). -/
def certJPsi (j : Fin 1780) (v : ℕ) (j' : Fin 1780) (v' : ℕ) : ℝ :=
  ∑ jj ∈ Finset.range (certJN j v j' v' + 1),
    ((certJN j v j' v').choose jj : ℝ) * ((2 : ℝ) / 25) ^ jj *
      (((24 : ℝ) / 25) ^ (49 + (certJN j v j' v' - jj) + (certJBeta j v).sum + (certJBeta j' v').sum) *
        ((certJN j v j' v' - jj).factorial : ℝ) /
          ((((certJN j v j' v' - jj) + (certJBeta j v).sum + (certJBeta j' v').sum + 49).factorial : ℕ) : ℝ))

/-- The `Slab` factor of `certJTerm` factors out of the `Ψ`-sum. -/
theorem certJTerm_eq (j : Fin 1780) (v : ℕ) (j' : Fin 1780) (v' : ℕ) :
    certJTerm j v j' v'
      = (Slab (certJBeta j v) (certJBeta j' v') 49 : ℝ) * certJPsi j v j' v' := by
  rw [certJTerm, certJPsi, Finset.mul_sum]
  refine Finset.sum_congr rfl (fun jj _ => ?_)
  ring

theorem certJBeta_notMem_zero (j : Fin 1780) (v : ℕ) : 0 ∉ certJBeta j v :=
  eraseOne_notMem_zero (certSig j) (certSig_notMem_zero j) v

/-- The signature weight is at most `25`. -/
theorem certSig_sum_le25 (j : Fin 1780) : (certSig j).sum ≤ 25 := by
  have h := of_decide_eq_true (List.all_eq_true.mp certBasis_sum_le (certBasisAt j)
    (List.get_mem _ _))
  have h' : (certSig j).sum + certA j ≤ 25 := h
  omega

theorem certJBeta_sum_le (j : Fin 1780) (v : ℕ) : (certJBeta j v).sum ≤ 25 :=
  le_trans (eraseOne_sum_le (certSig j) v) (certSig_sum_le25 j)

/-- The labelled coefficient against the `θ`-factor: the multiplicity factor cancels. -/
theorem certJCoef_mul_theta (j : Fin 1780) (v : ℕ)
    (hv : v ∈ (0 :: (certSig j).dedup).toFinset) :
    certJCoef j v * (theta (certJBeta j v) : ℝ)
      = (certK : ℝ) * (certCs j : ℝ) * kappa (certA j) v := by
  have hclR : (certCl j : ℝ) * (theta (certSig j) : ℝ) = (certK : ℝ) * (certCs j : ℝ) := by
    exact_mod_cast certLab_rel j
  have h2 : (if v = 0 then (1 : ℝ) else ((certSig j).count v : ℝ))
      * (theta (certJBeta j v) : ℝ) = (theta (certSig j) : ℝ) := by
    rw [certJBeta]
    exact (theta_mul_factor (certSig_notMem_zero j) hv).symm
  have h3 : ((certCl j : ℝ) * (if v = 0 then (1 : ℝ) else ((certSig j).count v : ℝ)))
      * (theta (certJBeta j v) : ℝ) = (certK : ℝ) * (certCs j : ℝ) := by
    calc ((certCl j : ℝ) * (if v = 0 then (1 : ℝ) else ((certSig j).count v : ℝ)))
          * (theta (certJBeta j v) : ℝ)
        = (certCl j : ℝ) * ((if v = 0 then (1 : ℝ) else ((certSig j).count v : ℝ))
            * (theta (certJBeta j v) : ℝ)) := by ring
      _ = (certCl j : ℝ) * (theta (certSig j) : ℝ) := by rw [h2]
      _ = (certK : ℝ) * (certCs j : ℝ) := hclR
  rw [certJCoef]
  calc ((certCl j : ℝ) * (if v = 0 then (1 : ℝ) else ((certSig j).count v : ℝ)))
        * kappa (certA j) v * (theta (certJBeta j v) : ℝ)
      = (((certCl j : ℝ) * (if v = 0 then (1 : ℝ) else ((certSig j).count v : ℝ)))
          * (theta (certJBeta j v) : ℝ)) * kappa (certA j) v := by ring
    _ = ((certK : ℝ) * (certCs j : ℝ)) * kappa (certA j) v := by rw [h3]
    _ = (certK : ℝ) * (certCs j : ℝ) * kappa (certA j) v := rfl

/-- One quadruple of the `J`-formula, in the symmetric-monomial normalisation. -/
theorem certJQuad_eq (j : Fin 1780) (v : ℕ)
    (hv : v ∈ (0 :: (certSig j).dedup).toFinset) (j' : Fin 1780) (v' : ℕ)
    (hv' : v' ∈ (0 :: (certSig j').dedup).toFinset) :
    certJCoef j v * certJCoef j' v' * certJTerm j v j' v'
      = ((certK : ℝ) * (certK : ℝ)) *
          ((certCs j : ℝ) * (certCs j' : ℝ) *
            (kappa (certA j) v * kappa (certA j') v') *
            (Ssum (certJBeta j v) (certJBeta j' v') 49 : ℝ) * certJPsi j v j' v') := by
  have h1 := certJCoef_mul_theta j v hv
  have h2 := certJCoef_mul_theta j' v' hv'
  rw [certJTerm_eq, Slab_eq_theta_mul 49 (certJBeta j v) (certJBeta j' v')
    (certJBeta_notMem_zero j v) (certJBeta_notMem_zero j' v')
    (by have := certJBeta_sum_le j v; omega) (by have := certJBeta_sum_le j' v'; omega) 49]
  push_cast
  calc certJCoef j v * certJCoef j' v' *
        ((theta (certJBeta j v) * theta (certJBeta j' v') * ↑(Ssum (certJBeta j v) (certJBeta j' v') 49))
          * certJPsi j v j' v')
      = (certJCoef j v * (theta (certJBeta j v) : ℝ))
          * (certJCoef j' v' * (theta (certJBeta j' v') : ℝ))
          * ↑(Ssum (certJBeta j v) (certJBeta j' v') 49) * certJPsi j v j' v' := by ring
    _ = ((certK : ℝ) * (certCs j : ℝ) * kappa (certA j) v)
          * ((certK : ℝ) * (certCs j' : ℝ) * kappa (certA j') v')
          * ↑(Ssum (certJBeta j v) (certJBeta j' v') 49) * certJPsi j v j' v' := by rw [h1, h2]
    _ = ((certK : ℝ) * (certK : ℝ)) *
          ((certCs j : ℝ) * (certCs j' : ℝ) *
            (kappa (certA j) v * kappa (certA j') v') *
            (Ssum (certJBeta j v) (certJBeta j' v') 49 : ℝ) * certJPsi j v j' v') := by ring

/-- **The `J`-value of the certificate in the symmetric-monomial normalisation.** -/
theorem sum_JFunc_certFun_certCs :
    ∑ i : Fin 50, JFunc 50 i ((24 : ℝ) / 25) certFun
      = 50 * (certK : ℝ) * (certK : ℝ) *
          (∑ j : Fin 1780, ∑ j' : Fin 1780,
            ∑ v ∈ (0 :: (certSig j).dedup).toFinset,
            ∑ v' ∈ (0 :: (certSig j').dedup).toFinset,
              (certCs j : ℝ) * (certCs j' : ℝ) *
                (kappa (certA j) v * kappa (certA j') v') *
                (Ssum (certJBeta j v) (certJBeta j' v') 49 : ℝ) * certJPsi j v j' v') := by
  have hsum : (∑ j : Fin 1780, ∑ j' : Fin 1780,
        ∑ v ∈ (0 :: (certSig j).dedup).toFinset,
        ∑ v' ∈ (0 :: (certSig j').dedup).toFinset,
          certJCoef j v * certJCoef j' v' * certJTerm j v j' v')
      = ((certK : ℝ) * (certK : ℝ)) *
          (∑ j : Fin 1780, ∑ j' : Fin 1780,
            ∑ v ∈ (0 :: (certSig j).dedup).toFinset,
            ∑ v' ∈ (0 :: (certSig j').dedup).toFinset,
              (certCs j : ℝ) * (certCs j' : ℝ) *
                (kappa (certA j) v * kappa (certA j') v') *
                (Ssum (certJBeta j v) (certJBeta j' v') 49 : ℝ) * certJPsi j v j' v') := by
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl (fun j _ => ?_)
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl (fun j' _ => ?_)
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl (fun v hv => ?_)
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl (fun v' hv' => certJQuad_eq j v hv j' v' hv')
  rw [sum_JFunc_certFun_eq, hsum]
  ring


end

end Commons.NumberTheory.MaynardSieve
