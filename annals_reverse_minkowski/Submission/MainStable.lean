import Submission.Filtration
import Submission.VoronoiMeasure
import Submission.GaussianMeasure
import Submission.TFacts
import Submission.Commons.Analysis.GaussianMeasure.one_dim_integral_abs_le_ten_ge_two_thirds
import Submission.Commons.Analysis.Real.product_ge_two_thirds
import Submission.Commons.Analysis.LogClaim.exp_neg_two_log_sq_add_lt_one

open Module Real Matrix MeasureTheory
open Submission.QuotientLattice
open Submission.StableLattices
open scoped Real BigOperators
set_option autoImplicit false
set_option linter.style.haveILetI false

/-!
# End-to-end assembly of Theorem 1.2 and the RM_stable black box (paper Prop. 7.2)

The [B] block (`Submission.Filtration.canonical_mass_bound`) reduces Theorem 1.2's
`n ≥ 2` branch to a single analytic statement:

**RM_stable**: for a *stable* full-rank lattice `ℒ` in ambient dimension `m`,
the Gaussian mass at parameter `1/(10 (log m + 2))` is at most `3/2`.

This module proves the whole theorem_1_2 (n ≥ 2 branch) *assuming* RM_stable.
RM_stable itself is reduced (via the `rho_gamma` bridge, already in VoronoiMeasure)
to the *Voronoi-γ statement* `gamma_stable` — the Voronoi cell of a stable lattice
has Gaussian mass `≥ 2/3` at parameter `1/(10 (log m + 2))`.  `gamma_stable` is the
single remaining `sorry` of the project; it is the statement that the whole §6–§7
analytic program (convex-geometry core, gradients, Mahler compactness, induction on
the rank) must prove, exactly as in the paper's Prop. 7.2.
-/

namespace Submission.MainStable

variable {n : ℕ}
local notation "E" => EuclideanSpace ℝ (Fin n)

/-- The paper's parameter `t = 10 (log n + 2)`. -/
noncomputable def t (n : ℕ) : ℝ := 10 * (Real.log (n : ℝ) + 2)

/-- `t(n) = 10 (log n + 2) > 0`. -/
lemma t_pos (n : ℕ) : 0 < t n := by
  dsimp [t]
  exact Submission.TFacts.t_pos n

/-- `1/t(n) > 0`. -/
lemma inv_t_pos (n : ℕ) : 0 < 1 / t n := by
  dsimp [t]
  positivity

/-- A discrete `ℤ`-submodule of full `ℤ`-rank spans the ambient `E` over `ℝ`. -/
lemma isZLattice_of_finrank (ℒ : Submodule ℤ E) [DiscreteTopology ℒ]
    (hfin : Module.finrank ℤ ℒ = n) : IsZLattice ℝ ℒ := by
  classical
  let b : Module.Basis (Fin (Module.finrank ℤ ℒ)) ℤ ℒ := Module.finBasis ℤ ℒ
  let v : Fin (Module.finrank ℤ ℒ) → E := fun i => ((b i : ℒ) : E)
  have hspanZ : Submodule.span ℤ (Set.range v) = ℒ := by
    dsimp [v]
    calc
      Submodule.span ℤ (Set.range (fun i => ((b i : ℒ) : E))) =
          Submodule.span ℤ (ℒ.subtype '' Set.range b) := by
        congr 1
        ext x
        constructor
        · rintro ⟨i, rfl⟩
          exact ⟨b i, ⟨i, rfl⟩, rfl⟩
        · rintro ⟨y, ⟨i, rfl⟩, hx⟩
          refine ⟨i, ?_⟩
          simpa using hx
      _ = Submodule.map ℒ.subtype (Submodule.span ℤ (Set.range b)) := by rw [Submodule.map_span]
      _ = Submodule.map ℒ.subtype ⊤ := by rw [b.span_eq]
      _ = ℒ := by rw [Submodule.map_top, Submodule.range_subtype]
  have hdisc : DiscreteTopology (Submodule.span ℤ (Set.range v)) := by
    rw [hspanZ]
    infer_instance
  have hfr : Module.finrank ℝ (Submodule.span ℝ (Set.range v)) = Module.finrank ℤ ℒ := by
    have hset := Real.finrank_eq_int_finrank_of_discrete (s := Set.range v) hdisc
    rw [Set.finrank, Set.finrank] at hset
    rw [hspanZ] at hset
    exact hset
  have hE : Module.finrank ℝ E = n := by simp
  have hNfin : Module.finrank ℝ (Submodule.span ℝ (Set.range v)) = n := by
    rw [hfr, hfin]
  have htop : Submodule.span ℝ (Set.range v) = ⊤ := by
    exact Submodule.eq_top_of_finrank_eq (S := Submodule.span ℝ (Set.range v)) (by rw [hNfin, hE])
  have hco : ((ℒ : Submodule ℤ E) : Set E) =
      ((Submodule.span ℤ (Set.range v) : Submodule ℤ E) : Set E) := by
    exact congrArg (fun L : Submodule ℤ E => (L : Set E)) hspanZ.symm
  exact ⟨by
    rw [hco]
    rw [Submodule.span_span_of_tower]
    exact htop⟩


/-! ## Base cases of `gamma_stable` (`m = 0`, `m = 1`)

For `m = 0` the Voronoi cell is the whole (trivial) space, whose Gaussian mass is `1`.
For `m = 1` we use the inradius bound (`half_ball_subset_voronoi_of_stable`), the
scale identity for `γ_s` at `s = 1/20 = 1/(10 (log 1 + 2))`, and the one-dimensional
integral bound `Commons.Analysis.GaussianMeasure.one_dim_integral_abs_le_ten_ge_two_thirds`,
transporting the ball integral from `EuclideanSpace ℝ (Fin 1)` to `ℝ` along the
(measure-preserving) coordinate equivalence `oneEquiv`.
-/

/-- Measure-preserving coordinate equivalence of the one-dimensional Euclidean space
`EuclideanSpace ℝ (Fin 1)` with `ℝ`. -/
noncomputable def oneEquiv : EuclideanSpace ℝ (Fin 1) ≃ᵐ ℝ :=
  (MeasurableEquiv.toLp 2 (Fin 1 → ℝ)).symm.trans (MeasurableEquiv.funUnique (Fin 1) ℝ)

/-- `oneEquiv` evaluates a vector at its single coordinate. -/
lemma oneEquiv_apply (x : EuclideanSpace ℝ (Fin 1)) :
    oneEquiv x = (WithLp.ofLp x) (0 : Fin 1) := by
  dsimp [oneEquiv]
  simp [MeasurableEquiv.toLp_symm_apply]

/-- `oneEquiv` is volume-preserving. -/
lemma oneEquiv_measurePreserving :
    MeasurePreserving oneEquiv volume volume := by
  dsimp [oneEquiv]
  change MeasurePreserving (⇑(MeasurableEquiv.funUnique (Fin 1) ℝ) ∘
      ⇑(MeasurableEquiv.toLp 2 (Fin 1 → ℝ)).symm) volume volume
  have h1s : MeasurePreserving (⇑(MeasurableEquiv.toLp 2 (Fin 1 → ℝ)).symm) volume volume := by
    exact (PiLp.volume_preserving_toLp (Fin 1)).symm (MeasurableEquiv.toLp 2 (Fin 1 → ℝ))
  have h2 : MeasurePreserving (⇑(MeasurableEquiv.funUnique (Fin 1) ℝ)) volume volume := by
    exact volume_preserving_funUnique (Fin 1) ℝ
  exact MeasurePreserving.comp h2 h1s

/-- In dimension one the norm is the absolute value of the single coordinate. -/
lemma oneEquiv_norm (x : EuclideanSpace ℝ (Fin 1)) : ‖x‖ = |oneEquiv x| := by
  have h : ‖x‖ ^ 2 = (oneEquiv x) ^ 2 := by
    rw [PiLp.norm_sq_eq_of_L2]
    simp [oneEquiv_apply]
  calc
    ‖x‖ = Real.sqrt (‖x‖ ^ 2) := by
      rw [Real.sqrt_sq_eq_abs]
      exact (abs_of_nonneg (norm_nonneg x)).symm
    _ = Real.sqrt ((oneEquiv x) ^ 2) := by rw [h]
    _ = |oneEquiv x| := Real.sqrt_sq_eq_abs (oneEquiv x)

lemma oneEquiv_norm_sq (x : EuclideanSpace ℝ (Fin 1)) : ‖x‖ ^ 2 = (oneEquiv x) ^ 2 := by
  rw [oneEquiv_norm]
  exact sq_abs (oneEquiv x)

/-- The Gaussian integral over the radius-`10` ball in dimension one equals the integral
over `[-10,10]` on the real line. -/
lemma oneDim_ball_integral :
    (∫ x in {x : EuclideanSpace ℝ (Fin 1) | ‖x‖ ≤ 10}, rexp (-Real.pi * ‖x‖ ^ 2)) =
      ∫ y in {y : ℝ | |y| ≤ 10}, rexp (-Real.pi * y ^ 2) := by
  let g : ℝ → ℝ := fun y => rexp (-Real.pi * y ^ 2)
  have hset : {x : EuclideanSpace ℝ (Fin 1) | ‖x‖ ≤ 10} =
      oneEquiv ⁻¹' {y : ℝ | |y| ≤ 10} := by
    ext x
    change ‖x‖ ≤ 10 ↔ |oneEquiv x| ≤ 10
    rw [oneEquiv_norm]
  have hmeas : MeasurableSet {x : EuclideanSpace ℝ (Fin 1) | ‖x‖ ≤ 10} := by
    exact (isClosed_Iic.preimage continuous_norm).measurableSet
  have hg : ∀ x : EuclideanSpace ℝ (Fin 1), rexp (-Real.pi * ‖x‖ ^ 2) = g (oneEquiv x) := by
    intro x
    dsimp [g]
    congr 1
    rw [oneEquiv_norm_sq]
  calc
    (∫ x in {x : EuclideanSpace ℝ (Fin 1) | ‖x‖ ≤ 10}, rexp (-Real.pi * ‖x‖ ^ 2))
        = ∫ x in {x : EuclideanSpace ℝ (Fin 1) | ‖x‖ ≤ 10}, g (oneEquiv x) := by
          refine setIntegral_congr_fun hmeas ?_
          intro x hx
          exact hg x
    _ = ∫ x in oneEquiv ⁻¹' {y : ℝ | |y| ≤ 10}, g (oneEquiv x) := by rw [hset]
    _ = ∫ y in {y : ℝ | |y| ≤ 10}, g y := by
          exact oneEquiv_measurePreserving.setIntegral_preimage_emb
            oneEquiv.measurableEmbedding g {y : ℝ | |y| ≤ 10}

/-- The preimage of the radius-`1/2` ball under the `1/20`-scaling is the radius-`10` ball. -/
lemma ball_half_scaled :
    {y : EuclideanSpace ℝ (Fin 1) | ((1 : ℝ) / 20) • y ∈
        Metric.closedBall (0 : EuclideanSpace ℝ (Fin 1)) (1 / 2)} =
      {x : EuclideanSpace ℝ (Fin 1) | ‖x‖ ≤ 10} := by
  ext x
  change ((1 : ℝ) / 20) • x ∈ Metric.closedBall (0 : EuclideanSpace ℝ (Fin 1)) (1 / 2) ↔ ‖x‖ ≤ 10
  rw [Metric.mem_closedBall, dist_eq_norm, sub_zero]
  constructor
  · intro hx
    rw [norm_smul] at hx
    have hc : ‖((1 / 20) : ℝ)‖ = 1 / 20 := by norm_num
    rw [hc] at hx
    nlinarith [norm_nonneg x]
  · intro hx
    rw [norm_smul]
    have hc : ‖((1 / 20) : ℝ)‖ = 1 / 20 := by norm_num
    rw [hc]
    nlinarith [norm_nonneg x]

/-- **Base case `m = 0` of `gamma_stable`.** -/
theorem gamma_stable_zero (ℒ : Submodule ℤ (EuclideanSpace ℝ (Fin 0)))
    [DiscreteTopology ℒ] (_hSt : Submission.StableLattices.Stable ℒ)
    (_hfin : Module.finrank ℤ ℒ = 0) :
    (2 : ℝ) / 3 ≤ Submission.GaussianMeasure.gammaMass (1 / t 0)
      (Submission.Voronoi.voronoi ℒ) := by
  have ht0 : 0 < 1 / t 0 := inv_t_pos 0
  have hV : Submission.Voronoi.voronoi ℒ = Set.univ := by
    ext x
    constructor
    · intro hx
      trivial
    · intro hx
      rw [Submission.Voronoi.mem_voronoi]
      intro y
      have hx0 : x = 0 := Subsingleton.elim x 0
      have hy0 : (y : EuclideanSpace ℝ (Fin 0)) = 0 :=
        Subsingleton.elim (y : EuclideanSpace ℝ (Fin 0)) 0
      rw [hx0, hy0]
      simp
  calc
    (2 : ℝ) / 3 ≤ 1 := by norm_num
    _ = Submission.GaussianMeasure.gammaMass (1 / t 0) (Set.univ : Set (EuclideanSpace ℝ (Fin 0))) := by
      rw [Submission.GaussianMeasure.gammaMass_univ (1 / t 0) ht0]
    _ = Submission.GaussianMeasure.gammaMass (1 / t 0) (Submission.Voronoi.voronoi ℒ) := by
      congr 1
      exact hV.symm

/-- **Base case `m = 1` of `gamma_stable`.** -/
theorem gamma_stable_one (ℒ : Submodule ℤ (EuclideanSpace ℝ (Fin 1)))
    [DiscreteTopology ℒ] (hSt : Submission.StableLattices.Stable ℒ) :
    (2 : ℝ) / 3 ≤ Submission.GaussianMeasure.gammaMass (1 / t 1)
      (Submission.Voronoi.voronoi ℒ) := by
  have ht : t 1 = 20 := by
    unfold t
    norm_num [Real.log_one]
  rw [ht]
  -- γ_{1/20}(V) ≥ γ_{1/20}(B(0,1/2)) by monotonicity of γ in the set
  have hB : (2 : ℝ) / 3 ≤
      Submission.GaussianMeasure.gammaMass (1 / 20)
        (Metric.closedBall (0 : EuclideanSpace ℝ (Fin 1)) (1 / 2)) := by
    calc
      (2 : ℝ) / 3 ≤ ∫ y in {y : ℝ | |y| ≤ 10}, rexp (-Real.pi * y ^ 2) := by
        exact Commons.Analysis.GaussianMeasure.one_dim_integral_abs_le_ten_ge_two_thirds
      _ = ∫ x in {x : EuclideanSpace ℝ (Fin 1) | ‖x‖ ≤ 10}, rexp (-Real.pi * ‖x‖ ^ 2) :=
        oneDim_ball_integral.symm
      _ = Submission.GaussianMeasure.gammaMass (1 / 20)
          (Metric.closedBall (0 : EuclideanSpace ℝ (Fin 1)) (1 / 2)) := by
        dsimp [Submission.GaussianMeasure.gammaMass]
        exact congrArg (fun S : Set (EuclideanSpace ℝ (Fin 1)) =>
          ∫ x in S, rexp (-Real.pi * ‖x‖ ^ 2)) ball_half_scaled.symm
  exact le_trans hB (by
    exact Submission.GaussianMeasure.gammaMass_mono_set (1 / 20)
      (Submission.StableLattices.half_ball_subset_voronoi_of_stable hSt)
      Metric.isClosed_closedBall.measurableSet (Submission.Voronoi.voronoi_measurable ℒ))


/-- **Boundary-case product arithmetic (paper Prop 7.2, closing step).**  With `1 ≤ d < m`,
`(1 − e^{−2log²(m/d)}/3)·(1 − e^{−2log²(m/(m−d))}/3) ≥ 2/3`.  This is the pure-real tail of
the boundary case: the two per-factor lower bounds come from the induction hypothesis plus
`gamma_concentration` (exponent `−2log²` after weakening `−25πlog²`), and this lemma closes
the product via the log-claim `e^{−2log²x} + e^{−2log²(x/(x−1))} < 1`
(`Commons.Analysis.LogClaim.exp_neg_two_log_sq_add_lt_one`) and
`Commons.Analysis.Real.product_ge_two_thirds`. -/
lemma boundary_factors_ge_two_thirds (m d : ℕ) (hm : 2 ≤ m) (hd : 1 ≤ d) (hdm : d < m) :
    (2 : ℝ) / 3 ≤
      (1 - Real.exp (-2 * (Real.log ((m : ℝ) / d)) ^ 2) / 3) *
        (1 - Real.exp (-2 * (Real.log ((m : ℝ) / (m - d))) ^ 2) / 3) := by
  have hdpos_nat : 0 < d := lt_of_lt_of_le Nat.zero_lt_one hd
  have hdpos : 0 < (d : ℝ) := by exact_mod_cast hdpos_nat
  have hmminusdpos_nat : 0 < m - d := by omega
  have hmminusdpos : 0 < ((m - d : ℕ) : ℝ) := by exact_mod_cast hmminusdpos_nat
  have hdmR : (d : ℝ) < (m : ℝ) := by exact_mod_cast hdm
  have hxgt1 : 1 < (m : ℝ) / d := (one_lt_div hdpos).2 hdmR
  have hmdsub : (m : ℝ) - (d : ℝ) ≠ 0 := by
    exact sub_ne_zero.mpr (ne_of_gt hdmR)
  have hxy : (m : ℝ) / d / ((m : ℝ) / d - 1) = (m : ℝ) / (m - d : ℕ) := by
    rw [Nat.cast_sub (le_of_lt hdm)]
    field_simp [hdpos.ne', hmdsub]
  have hlog : Real.exp (-2 * (Real.log ((m : ℝ) / d)) ^ 2) +
        Real.exp (-2 * (Real.log ((m : ℝ) / (m - d))) ^ 2) < 1 := by
    have hclaim := Commons.Analysis.LogClaim.exp_neg_two_log_sq_add_lt_one ((m : ℝ) / d) hxgt1
    rw [hxy] at hclaim
    rw [Nat.cast_sub (le_of_lt hdm)] at hclaim
    exact hclaim
  let a : ℝ := Real.exp (-2 * (Real.log ((m : ℝ) / d)) ^ 2)
  let b : ℝ := Real.exp (-2 * (Real.log ((m : ℝ) / (m - d))) ^ 2)
  change (2 : ℝ) / 3 ≤ (1 - a / 3) * (1 - b / 3)
  have ha0 : 0 ≤ a := (Real.exp_pos _).le
  have hb0 : 0 ≤ b := (Real.exp_pos _).le
  have hab : a + b ≤ 1 := by
    have hab' : a + b < 1 := by
      simpa [a, b] using hlog
    exact le_of_lt hab'
  exact Commons.Analysis.Real.product_ge_two_thirds a b ha0 hb0 hab


/-- The parameter gap `t m - t d = 10·log(m/d)` for `1 ≤ d ≤ m`. -/
lemma t_sub_t (m d : ℕ) (hd : 1 ≤ d) (hdm : d ≤ m) :
    t m - t d = 10 * Real.log ((m : ℝ) / (d : ℝ)) := by
  have hd0 : (d : ℝ) ≠ 0 := by exact_mod_cast (ne_of_gt (lt_of_lt_of_le Nat.zero_lt_one hd))
  have hm0 : (m : ℝ) ≠ 0 := by
    have : 0 < m := lt_of_lt_of_le (lt_of_lt_of_le Nat.zero_lt_one hd) hdm
    exact_mod_cast (ne_of_gt this)
  dsimp [t]
  rw [Real.log_div hm0 hd0]
  ring

/-- Exponent weakening in the boundary boost: with `τ = t m - t d = 10·log(m/d)` and
inradius `r ≥ 1/2`, the concentration exponent `π(r·τ)² ≥ π(τ/2)² = 25π·log²(m/d)` is far
above the needed `2·log²(m/d)`, so
`1 − e^{−2log²(m/d)}/3 ≤ 1 − e^{−π((τ/2))²}/3`. -/
lemma concentration_boost_bound (m d : ℕ) (hd : 1 ≤ d) (hdm : d < m) :
    1 - Real.exp (-2 * (Real.log ((m : ℝ) / (d : ℝ))) ^ 2) / 3 ≤
      1 - Real.exp (-Real.pi * (((1 : ℝ) / 2) * (t m - t d)) ^ 2) / 3 := by
  let L : ℝ := Real.log ((m : ℝ) / (d : ℝ))
  have hd0 : 0 < (d : ℝ) := by exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one hd)
  have hm0 : 0 < (m : ℝ) := by
    have : 0 < m := lt_of_lt_of_le (lt_of_lt_of_le Nat.zero_lt_one hd) (le_of_lt hdm)
    exact_mod_cast this
  have hge1 : 1 ≤ (m : ℝ) / (d : ℝ) := by
    rw [one_le_div hd0]
    exact_mod_cast (le_of_lt hdm)
  have hL0 : 0 ≤ L := by
    dsimp [L]
    exact Real.log_nonneg hge1
  have ht : t m - t d = 10 * L := by
    dsimp [L]
    exact t_sub_t m d hd (le_of_lt hdm)
  have hsq : (((1 : ℝ) / 2) * (t m - t d)) ^ 2 = (5 * L) ^ 2 := by
    rw [ht]
    ring
  have hpi : (2 : ℝ) ≤ 25 * Real.pi := by nlinarith [Real.pi_gt_three]
  have hcoef : (2 : ℝ) * L ^ 2 ≤ (25 * Real.pi) * L ^ 2 := by
    exact mul_le_mul_of_nonneg_right hpi (sq_nonneg L)
  have hineq : -Real.pi * (5 * L) ^ 2 ≤ -2 * L ^ 2 := by
    have h5 : (5 * L) ^ 2 = 25 * L ^ 2 := by ring
    rw [h5]
    nlinarith
  have hmain : Real.exp (-Real.pi * (((1 : ℝ) / 2) * (t m - t d)) ^ 2) ≤
      Real.exp (-2 * L ^ 2) := by
    rw [hsq]
    exact Real.exp_le_exp.mpr hineq
  calc
    1 - Real.exp (-2 * (Real.log ((m : ℝ) / (d : ℝ))) ^ 2) / 3
        = 1 - Real.exp (-2 * L ^ 2) / 3 := by rfl
    _ ≤ 1 - Real.exp (-Real.pi * (((1 : ℝ) / 2) * (t m - t d)) ^ 2) / 3 := by
        linarith

/-- **Boundary boost (structure)**: a per-factor lower bound at the common parameter
`1/t m` of the form supplied by `gamma_concentration` (inradius `≥ 1/2`,
`τ = t m - t d`, RHS `1 − e^{−π(τ/2)²}/3`) implies the weakened bound with exponent
`−2log²(m/d)` used by the log-claim arithmetic. -/
lemma boosted_factor_bound (m d : ℕ) (hd : 1 ≤ d) (hdm : d < m) (a : ℝ)
    (ha : 1 - Real.exp (-Real.pi * (((1 : ℝ) / 2) * (t m - t d)) ^ 2) / 3 ≤ a) :
    1 - Real.exp (-2 * (Real.log ((m : ℝ) / (d : ℝ))) ^ 2) / 3 ≤ a := by
  exact le_trans (concentration_boost_bound m d hd hdm) ha

end Submission.MainStable
