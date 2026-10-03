import Mathlib
import Submission.Work.A3.singInt_bound
import Submission.Work.A3.minorArc_contribution
import Submission.Work.A3.completeSum_power_saving
import Submission.Work.A3.weyl_poly

/-!
# Assembly of `PolyEnergyBound` from the circle-method estimates

**REPAIR COPY** (`Submission/Work/A3Fix/Assembly.lean`, 2026-09-30).  This is a verbatim copy of
`Submission/Work/A3/polyEnergyBound_assembly.lean` with the *stale* import
`Submission.Work.A3.majorArc_contribution` removed (that module does not exist in the tree — its
statement was refuted, see `NOTES_A3_majorArc_contribution_REFUTATION.md` — and its presence made
the whole A3 chain, and hence `Work.KMTAreas.area_A3`, unbuildable from source), together with the
last namespace block, whose only declaration `polyEnergy_bound_circleMethod` used the missing
`majorArc_contribution`.  That theorem is used by nothing in the tree (`polyEnergyBound_of_circleMethod`
is used only by `Work.A3.polyEnergy_bound_of_pointwise`, itself used by nothing; the unconditional
route is `Work.A3.polyEnergy_bound_complete` in `A3Fix/DeepFinal.lean`).  Every other declaration is
unchanged.

This module contains the *assembly* step of the arithmetic core of Area A3: from

* the major-arc estimate `∫_{𝔐 ∩ [0,1]} ‖expSum Q N‖^{2s} ≤ C^{2s} N^{2s-d}` and
* the minor-arc estimate `∫_{𝔪 ∩ [0,1]} ‖expSum Q N‖^{2s} ≤ C^{2s} N^{2s-d}`

(where `𝔐 = Work.A3.majorArcSet Q N (1/2)` and `𝔪` its complement) it produces the sharp mean
value estimate `Work.A3.PolyEnergyBound Q`, choosing the moment order `s` and the arc parameter
`η = 1/2` so that the two estimates apply.

The two arc estimates are the conclusions of `Work.A3.majorArc_contribution` and
`Work.A3.minorArc_contribution` (stated there for `η ∈ (0,1]` arbitrary; here `η = 1/2` is used),
so this file is self-contained: it takes them as explicit hypotheses.

## The choice of the parameters

* `η := 1/2` (any `η ∈ (0,1]` would do; `η` must only satisfy `η ≤ 1` for the minor arcs, whose
  Weyl saving is `η·2^{1-d} - ε`);
* `ε < 2^{1-d}/4` for the Weyl exponent (the caller instantiates `weyl_poly`, which holds for
  *every* `ε > 0`, at such an `ε`);
* `s` large enough that `s·δ > 1`, `2s > deg Q` and `(2s-2)(σ/2 - ε) ≥ deg Q - 1`, where
  `σ = 2^{1-d}`: `s := max 2 (max (s₁+1) (max (deg Q + 1) s₂))` with `s₁ > 1/δ` and
  `s₂ > (deg Q - 1)·2^{deg Q + 1}`.
-/

set_option autoImplicit false

namespace Work.A3

open MeasureTheory Polynomial Finset
open scoped ENNReal NNReal BigOperators

noncomputable section

/-- `θ ↦ expSum Q N θ` is continuous. -/
private lemma continuous_expSum (Q : Polynomial ℤ) (N : ℕ) :
    Continuous (fun θ : ℝ => expSum Q N θ) := by
  unfold expSum
  fun_prop

/-- `‖expSum Q N θ‖ ≤ N`. -/
private lemma norm_expSum_le (Q : Polynomial ℤ) (N : ℕ) (θ : ℝ) : ‖expSum Q N θ‖ ≤ (N : ℝ) := by
  calc ‖expSum Q N θ‖ ≤ ∑ n ∈ Finset.Icc 1 N,
        ‖Complex.exp (-(2 * Real.pi * Complex.I * (((Q.eval (n : ℤ) : ℤ) : ℝ) * θ)))‖ :=
        norm_sum_le _ _
    _ = ∑ _n ∈ Finset.Icc 1 N, (1 : ℝ) := by
        refine Finset.sum_congr rfl fun n _ => ?_
        rw [Complex.norm_exp]; simp
    _ = (N : ℝ) := by simp

/-- The major-arc set is measurable (a countable union of closed arcs). -/
private lemma majorArcSet_measurable (Q : Polynomial ℤ) (N : ℕ) (η : ℝ) :
    MeasurableSet (majorArcSet Q N η) := by
  have h : majorArcSet Q N η =
      ⋃ (q : ℕ) (a : ℤ), ⋃ (_h : 1 ≤ q ∧ IsCoprime a (q:ℤ) ∧ (q:ℝ) ≤ (N:ℝ)^η),
        Set.Icc ((a:ℝ)/(q:ℝ) - 1/((q:ℝ)*((N:ℝ)^((Q.natDegree:ℝ)/2))))
                ((a:ℝ)/(q:ℝ) + 1/((q:ℝ)*((N:ℝ)^((Q.natDegree:ℝ)/2)))) := by
    ext θ
    simp only [majorArcSet, Set.mem_iUnion, Set.mem_Icc]
    constructor
    · rintro ⟨q, a, h1, h2, h3, h4⟩
      rw [abs_le] at h4
      exact ⟨q, a, ⟨h1, h2, h3⟩, by linarith [h4.1], by linarith [h4.2]⟩
    · rintro ⟨q, a, ⟨h1, h2, h3⟩, h4, h5⟩
      exact ⟨q, a, h1, h2, h3, by rw [abs_le]; exact ⟨by linarith, by linarith⟩⟩
  rw [h]
  exact MeasurableSet.iUnion fun q => MeasurableSet.iUnion fun a =>
    MeasurableSet.iUnion fun _ => measurableSet_Icc

/-- `‖expSum Q N‖^{2s}` is integrable on `[0,1]` (it is bounded by `N^{2s}`). -/
private lemma integrable_expSum_pow (Q : Polynomial ℤ) (N s : ℕ) :
    Integrable (fun θ : ℝ => ‖expSum Q N θ‖ ^ (2*s)) (volume.restrict (Set.Icc (0:ℝ) 1)) := by
  refine Integrable.of_bound ((continuous_expSum Q N).norm.pow (2*s)).aestronglyMeasurable
    ((N:ℝ)^(2*s)) ?_
  filter_upwards with θ
  rw [Real.norm_of_nonneg (by positivity)]
  exact pow_le_pow_left₀ (norm_nonneg _) (norm_expSum_le Q N θ) _

/-- **The assembly step.**  If both arc contributions are bounded by `C^{2s}N^{2s-d}` (at the arc
parameter `η = 1/2`), then the `2s`-th moment of the exponential sum — i.e. the energy — is. -/
theorem polyEnergy_bound_of_arc_bounds (Q : Polynomial ℤ) (hd : 2 ≤ Q.natDegree)
    {s : ℕ} (hs : 2 ≤ s)
    (hmaj : ∃ C : ℝ, 0 < C ∧ ∀ N : ℕ, 1 ≤ N →
      ∫ θ in majorArcSet Q N (1/2) ∩ Set.Icc (0:ℝ) 1, ‖expSum Q N θ‖ ^ (2 * s) ≤
        C ^ (2 * s) * (N : ℝ) ^ (2 * s - Q.natDegree))
    (hmin : ∃ C : ℝ, 0 < C ∧ ∀ N : ℕ, 1 ≤ N →
      ∫ θ in (majorArcSet Q N (1/2))ᶜ ∩ Set.Icc (0:ℝ) 1, ‖expSum Q N θ‖ ^ (2 * s) ≤
        C ^ (2 * s) * (N : ℝ) ^ (2 * s - Q.natDegree)) :
    ∃ C : ℝ, 0 < C ∧ ∀ N : ℕ, 1 ≤ N →
      (polyEnergy Q s N : ℝ) ≤ C ^ (2 * s) * (N : ℝ) ^ (2 * s - Q.natDegree) := by
  obtain ⟨C₁, hC₁, hmaj⟩ := hmaj
  obtain ⟨C₂, hC₂, hmin⟩ := hmin
  refine ⟨2 * max C₁ C₂, by positivity, ?_⟩
  intro N hN
  have hA : MeasurableSet (majorArcSet Q N (1/2)) := majorArcSet_measurable Q N (1/2)
  have hint := integrable_expSum_pow Q N s
  have hsplit := integral_add_compl (μ := volume.restrict (Set.Icc (0:ℝ) 1)) hA hint
  have hA1 : ∫ x in majorArcSet Q N (1/2), ‖expSum Q N x‖ ^ (2*s)
        ∂(volume.restrict (Set.Icc (0:ℝ) 1))
      = ∫ x in majorArcSet Q N (1/2) ∩ Set.Icc (0:ℝ) 1, ‖expSum Q N x‖ ^ (2*s) := by
    rw [Measure.restrict_restrict (μ := volume) (s := majorArcSet Q N (1/2))
        (t := Set.Icc (0:ℝ) 1) (majorArcSet_measurable Q N (1/2))]
  have hA2 : ∫ x in (majorArcSet Q N (1/2))ᶜ, ‖expSum Q N x‖ ^ (2*s)
        ∂(volume.restrict (Set.Icc (0:ℝ) 1))
      = ∫ x in (majorArcSet Q N (1/2))ᶜ ∩ Set.Icc (0:ℝ) 1, ‖expSum Q N x‖ ^ (2*s) := by
    rw [Measure.restrict_restrict (μ := volume) (s := (majorArcSet Q N (1/2))ᶜ)
        (t := Set.Icc (0:ℝ) 1) (majorArcSet_measurable Q N (1/2)).compl]
  have hNnn : (0:ℝ) ≤ (N : ℝ) ^ (2 * s - Q.natDegree) := by positivity
  have hsum : C₁ ^ (2*s) + C₂ ^ (2*s) ≤ (2 * max C₁ C₂) ^ (2*s) := by
    have h2s : 1 ≤ 2*s := by omega
    have h3 : (1:ℝ) ≤ (2:ℝ)^(2*s) := one_le_pow₀ (by norm_num : (1:ℝ) ≤ 2)
    have hM : (0:ℝ) < max C₁ C₂ := lt_of_lt_of_le hC₁ (le_max_left _ _)
    have hgoal : (max C₁ C₂)^(2*s) + (max C₁ C₂)^(2*s) ≤ (2 * max C₁ C₂)^(2*s) := by
      rw [mul_pow]
      have hp : (0:ℝ) < (max C₁ C₂)^(2*s) := pow_pos hM _
      have htwo : (2:ℝ) ≤ (2:ℝ)^(2*s) := by
        calc (2:ℝ) = (2:ℝ)^1 := (pow_one 2).symm
          _ ≤ (2:ℝ)^(2*s) := pow_le_pow_right₀ (by norm_num) h2s
      calc (max C₁ C₂)^(2*s) + (max C₁ C₂)^(2*s) = 2 * (max C₁ C₂)^(2*s) := by ring
        _ ≤ (2:ℝ)^(2*s) * (max C₁ C₂)^(2*s) :=
            mul_le_mul_of_nonneg_right htwo (le_of_lt hp)
    calc C₁ ^ (2*s) + C₂ ^ (2*s)
        ≤ (max C₁ C₂)^(2*s) + (max C₁ C₂)^(2*s) :=
          add_le_add (pow_le_pow_left₀ (le_of_lt hC₁) (le_max_left _ _) _)
                     (pow_le_pow_left₀ (le_of_lt hC₂) (le_max_right _ _) _)
      _ ≤ (2 * max C₁ C₂)^(2*s) := hgoal
  calc (polyEnergy Q s N : ℝ)
      = ∫ x in Set.Icc (0:ℝ) 1, ‖expSum Q N x‖ ^ (2*s) :=
        (integral_norm_expSum_pow Q N s hN).symm
    _ = ∫ x in majorArcSet Q N (1/2), ‖expSum Q N x‖ ^ (2*s)
          ∂(volume.restrict (Set.Icc (0:ℝ) 1))
        + ∫ x in (majorArcSet Q N (1/2))ᶜ, ‖expSum Q N x‖ ^ (2*s)
          ∂(volume.restrict (Set.Icc (0:ℝ) 1)) := hsplit.symm
    _ = (∫ x in majorArcSet Q N (1/2) ∩ Set.Icc (0:ℝ) 1, ‖expSum Q N x‖ ^ (2*s))
        + (∫ x in (majorArcSet Q N (1/2))ᶜ ∩ Set.Icc (0:ℝ) 1, ‖expSum Q N x‖ ^ (2*s)) := by
        rw [hA1, hA2]
    _ ≤ C₁ ^ (2*s) * (N : ℝ) ^ (2*s - Q.natDegree)
          + C₂ ^ (2*s) * (N : ℝ) ^ (2*s - Q.natDegree) := add_le_add (hmaj N hN) (hmin N hN)
    _ = (C₁ ^ (2*s) + C₂ ^ (2*s)) * (N : ℝ) ^ (2*s - Q.natDegree) := by ring
    _ ≤ (2 * max C₁ C₂) ^ (2*s) * (N : ℝ) ^ (2*s - Q.natDegree) :=
        mul_le_mul_of_nonneg_right hsum hNnn

end
end Work.A3

namespace Work.A3

open MeasureTheory Polynomial Finset
open scoped ENNReal NNReal BigOperators

noncomputable section

/-- `2^{d+1} * 2^{-(d-1)} = 4`. -/
private lemma pow_succ_mul_inv_pow (d : ℕ) (hd : 1 ≤ d) :
    (2:ℝ)^(d+1) * (1 / (2:ℝ)^(d-1)) = 4 := by
  rw [mul_one_div, div_eq_iff (by positivity), show (4:ℝ) = (2:ℝ)^2 by norm_num, ← pow_add]
  congr 1
  omega

/-- **The circle-method assembly of `PolyEnergyBound`.**

Given the three inputs of the circle method for `Q` — Weyl's inequality for every `ε > 0`, the
power saving for complete sums, and the singular-integral bound — together with the two arc
estimates (phrased exactly as the conclusions of `Work.A3.majorArc_contribution` and
`Work.A3.minorArc_contribution`, at a general arc parameter `η`), the sharp mean value estimate
`PolyEnergyBound Q` follows. -/
theorem polyEnergyBound_of_circleMethod (Q : Polynomial ℤ) (hd : 2 ≤ Q.natDegree)
    {δ C₀ : ℝ} (hδ : 0 < δ) (hC₀ : 0 < C₀)
    (hc : ∀ (q : ℕ) (a : ℤ), 1 ≤ q → IsCoprime a (q : ℤ) →
      ‖completeSum Q a q‖ ≤ C₀ * (q : ℝ) ^ (1 - δ))
    {Cv : ℝ} (hCv : 0 < Cv)
    (hv : ∀ (N k : ℕ), 1 ≤ N → Q.natDegree < 2 * k →
      ∫ β : ℝ, ‖singInt Q N β‖ ^ (2 * k) ≤ Cv ^ (2 * k) * (N : ℝ) ^ (2 * k - Q.natDegree))
    (hweyl : ∀ (ε : ℝ), 0 < ε → ∃ CW : ℝ, 0 < CW ∧
      ∀ (M : ℕ) (a q : ℤ) (θ : ℝ), 1 ≤ M → 1 ≤ q → IsCoprime a q →
        |θ - (a : ℝ) / (q : ℝ)| ≤ 1 / ((q : ℝ) ^ 2) →
        ‖expSum Q M θ‖ ≤ CW * (M : ℝ) ^ (1 + ε) *
          (((q : ℝ)⁻¹ + (M : ℝ)⁻¹ + (q : ℝ) * (M : ℝ) ^ (-((Q.natDegree : ℤ))))
            ^ ((1 : ℝ) / (2 : ℝ) ^ (Q.natDegree - 1))))
    (hmaj : ∀ {s : ℕ} {η : ℝ}, 2 ≤ s → Q.natDegree < 2 * s → 2 * Q.natDegree ≤ s →
      1 < (s : ℝ) * δ → 0 < η → η ≤ 1 →
      ∃ C : ℝ, 0 < C ∧ ∀ N : ℕ, 1 ≤ N →
        ∫ θ in majorArcSet Q N η ∩ Set.Icc (0:ℝ) 1, ‖expSum Q N θ‖ ^ (2 * s) ≤
          C ^ (2 * s) * (N : ℝ) ^ (2 * s - Q.natDegree))
    (hmin : ∀ {s : ℕ} {η ε : ℝ}, 2 ≤ s → Q.natDegree ≤ 2 * s → 0 < η → η ≤ 1 → 0 < ε →
      (Q.natDegree - 1 : ℝ) ≤ (2 * s - 2 : ℝ) *
        (η * (1 / (2 : ℝ) ^ (Q.natDegree - 1)) - ε) →
      ∃ C : ℝ, 0 < C ∧ ∀ N : ℕ, 1 ≤ N →
        ∫ θ in (majorArcSet Q N η)ᶜ ∩ Set.Icc (0:ℝ) 1, ‖expSum Q N θ‖ ^ (2 * s) ≤
          C ^ (2 * s) * (N : ℝ) ^ (2 * s - Q.natDegree)) :
    PolyEnergyBound Q := by
  set σ : ℝ := 1 / (2:ℝ)^(Q.natDegree - 1) with hσ
  have hσpos : 0 < σ := by positivity
  obtain ⟨CW, hCW, hweyl⟩ := hweyl (σ/8) (by positivity)
  obtain ⟨s₁, hs₁⟩ := exists_nat_gt (1/δ)
  obtain ⟨s₂, hs₂⟩ := exists_nat_gt (((Q.natDegree : ℝ) - 1) * (2:ℝ)^(Q.natDegree+1) + 1)
  set s : ℕ := max 2 (max (s₁+1) (max (2 * Q.natDegree + 1) s₂)) with hs
  have hs1 : 1 ≤ s := by omega
  have hs2 : 2 ≤ s := by omega
  have hds : Q.natDegree + 1 ≤ s := by omega
  have hlarge : 2 * Q.natDegree ≤ s := by omega
  have hss₁ : s₁ + 1 ≤ s := by omega
  have hss₂ : s₂ ≤ s := by omega
  have hsd : Q.natDegree < 2 * s := by omega
  have hsδ : 1 < (s : ℝ) * δ := by
    have h1 : (1:ℝ)/δ < (s : ℝ) := lt_of_lt_of_le hs₁ (by exact_mod_cast (by omega : s₁ ≤ s))
    have h2 : 1 < (s : ℝ) * δ := by
      rw [div_lt_iff₀ hδ] at h1
      linarith
    exact h2
  have hsz : (Q.natDegree - 1 : ℝ) ≤ (2 * s - 2 : ℝ) * ((1/2) * σ - σ/8) := by
    have hd1 : (1:ℝ) ≤ (Q.natDegree : ℝ) := by exact_mod_cast (by omega : 1 ≤ Q.natDegree)
    have hpow := pow_succ_mul_inv_pow Q.natDegree (by omega : 1 ≤ Q.natDegree)
    have hs₂' : ((Q.natDegree : ℝ) - 1) * (2:ℝ)^(Q.natDegree+1) + 1 < (s : ℝ) :=
      lt_of_lt_of_le hs₂ (by exact_mod_cast (by omega : s₂ ≤ s))
    have hs2R : (2:ℝ) ≤ (s : ℝ) := by exact_mod_cast hs2
    have h2s : (s : ℝ) ≤ (2 * s - 2 : ℝ) := by
      have : (2 * s : ℕ) ≥ s + 2 := by omega
      have hcast : ((2*s : ℕ) : ℝ) = 2 * (s:ℝ) := by push_cast; ring
      have : (s:ℝ) + 2 ≤ 2 * (s:ℝ) := by
        have h := (Nat.cast_le (α := ℝ)).mpr (show s + 2 ≤ 2*s by omega)
        simpa [hcast] using h
      linarith
    have hσ4 : (2:ℝ)^(Q.natDegree+1) * σ = 4 := by
      rw [hσ]; exact pow_succ_mul_inv_pow Q.natDegree (by omega : 1 ≤ Q.natDegree)
    have hprod : ((Q.natDegree : ℝ) - 1) * (2:ℝ)^(Q.natDegree+1) * σ = 4 * ((Q.natDegree : ℝ) - 1) := by
      rw [mul_assoc, hσ4]
      ring
    have hstep : ((Q.natDegree : ℝ) - 1) * (2:ℝ)^(Q.natDegree+1) * σ < (s:ℝ) * σ := by
      rw [hprod]
      nlinarith [hs₂', hσpos]
    have hfac : ((1/2 : ℝ) * σ - σ/8) = 3*σ/8 := by ring
    rw [hfac]
    nlinarith [hstep, hσpos, h2s, hd1]
  have hη1 : (0:ℝ) < 1/2 := by norm_num
  have hη2 : (1:ℝ)/2 ≤ 1 := by norm_num
  obtain ⟨C₁, hC₁, hmaj'⟩ := hmaj (s := s) (η := 1/2) hs2 hsd hlarge hsδ hη1 hη2
  obtain ⟨C₂, hC₂, hmin'⟩ := hmin (s := s) (η := 1/2) (ε := σ/8) hs2 (le_of_lt hsd) hη1 hη2
      (by positivity) (by simpa using hsz)
  obtain ⟨C, hC, hbound⟩ := polyEnergy_bound_of_arc_bounds Q hd hs2 ⟨C₁, hC₁, hmaj'⟩ ⟨C₂, hC₂, hmin'⟩
  refine ⟨s, hs2, Real.toNNReal C, Real.toNNReal_pos.mpr hC, ?_⟩
  intro N hN
  have hcoe : ((Real.toNNReal C : ℝ≥0) : ℝ) = C := Real.coe_toNNReal C (le_of_lt hC)
  rw [hcoe]
  exact hbound N hN

end
end Work.A3


namespace Work.A3

open MeasureTheory Polynomial Finset
open scoped ENNReal NNReal BigOperators

noncomputable section

/-- **The same assembly, with the two already-proved inputs plugged in.**

This is the interface check: `Work.A3.singInt_bound` (the singular integral) and
`Work.A3.minorArc_contribution` (the minor arcs, which consumes `hweyl`) are wired into
`Work.A3.polyEnergyBound_of_circleMethod`, leaving only the complete-sum saving `hc`, Weyl's
inequality `hweyl` and the major arcs `hmaj` as explicit hypotheses. -/
theorem polyEnergyBound_of_remaining_three (Q : Polynomial ℤ) (hd : 2 ≤ Q.natDegree)
    {δ C₀ : ℝ} (hδ : 0 < δ) (hC₀ : 0 < C₀)
    (hc : ∀ (q : ℕ) (a : ℤ), 1 ≤ q → IsCoprime a (q : ℤ) →
      ‖completeSum Q a q‖ ≤ C₀ * (q : ℝ) ^ (1 - δ))
    (hweyl : ∀ (ε : ℝ), 0 < ε → ∃ CW : ℝ, 0 < CW ∧
      ∀ (M : ℕ) (a q : ℤ) (θ : ℝ), 1 ≤ M → 1 ≤ q → IsCoprime a q →
        |θ - (a : ℝ) / (q : ℝ)| ≤ 1 / ((q : ℝ) ^ 2) →
        ‖expSum Q M θ‖ ≤ CW * (M : ℝ) ^ (1 + ε) *
          (((q : ℝ)⁻¹ + (M : ℝ)⁻¹ + (q : ℝ) * (M : ℝ) ^ (-((Q.natDegree : ℤ))))
            ^ ((1 : ℝ) / (2 : ℝ) ^ (Q.natDegree - 1))))
    (hmaj : ∀ {s : ℕ} {η : ℝ}, 2 ≤ s → Q.natDegree < 2 * s → 2 * Q.natDegree ≤ s →
      1 < (s : ℝ) * δ → 0 < η → η ≤ 1 →
      ∃ C : ℝ, 0 < C ∧ ∀ N : ℕ, 1 ≤ N →
        ∫ θ in majorArcSet Q N η ∩ Set.Icc (0:ℝ) 1, ‖expSum Q N θ‖ ^ (2 * s) ≤
          C ^ (2 * s) * (N : ℝ) ^ (2 * s - Q.natDegree)) :
    PolyEnergyBound Q := by
  obtain ⟨Cv, hCv, hv⟩ := singInt_bound Q hd
  refine polyEnergyBound_of_circleMethod Q hd hδ hC₀ hc hCv ?_ hweyl hmaj ?_
  · intro N k hN hk
    exact hv N k hN (by omega) hk
  intro s η ε hs hds hη hη1 hε hsz
  obtain ⟨CW, hCW, hweyl'⟩ := hweyl ε hε
  exact minorArc_contribution Q hd hCW hε hweyl' hs hds hη hη1 hsz

end
end Work.A3


namespace Work.A3

open MeasureTheory Polynomial Finset
open scoped ENNReal NNReal BigOperators

noncomputable section

/-- **The assembly with the complete-sum saving and the singular integral plugged in.**

Only two inputs are left explicit: Weyl's inequality `hweyl` and the major-arc estimate `hmaj`.
Together with `Work.A3.completeSum_power_saving` and `Work.A3.singInt_bound` (imported here) and
`Work.A3.minorArc_contribution`, this is every piece of the circle-method proof of
`Work.A3.PolyEnergyBound`. -/
theorem polyEnergyBound_of_weyl_and_majorArc (Q : Polynomial ℤ) (hd : 2 ≤ Q.natDegree)
    (hweyl : ∀ (ε : ℝ), 0 < ε → ∃ CW : ℝ, 0 < CW ∧
      ∀ (M : ℕ) (a q : ℤ) (θ : ℝ), 1 ≤ M → 1 ≤ q → IsCoprime a q →
        |θ - (a : ℝ) / (q : ℝ)| ≤ 1 / ((q : ℝ) ^ 2) →
        ‖expSum Q M θ‖ ≤ CW * (M : ℝ) ^ (1 + ε) *
          (((q : ℝ)⁻¹ + (M : ℝ)⁻¹ + (q : ℝ) * (M : ℝ) ^ (-((Q.natDegree : ℤ))))
            ^ ((1 : ℝ) / (2 : ℝ) ^ (Q.natDegree - 1))))
    (hmaj : ∀ {δ C₀ : ℝ}, 0 < δ → 0 < C₀ →
      (∀ (q : ℕ) (a : ℤ), 1 ≤ q → IsCoprime a (q : ℤ) →
        ‖completeSum Q a q‖ ≤ C₀ * (q : ℝ) ^ (1 - δ)) →
      ∀ {s : ℕ} {η : ℝ}, 2 ≤ s → Q.natDegree < 2 * s → 2 * Q.natDegree ≤ s →
        1 < (s : ℝ) * δ → 0 < η → η ≤ 1 →
        ∃ C : ℝ, 0 < C ∧ ∀ N : ℕ, 1 ≤ N →
          ∫ θ in majorArcSet Q N η ∩ Set.Icc (0:ℝ) 1, ‖expSum Q N θ‖ ^ (2 * s) ≤
            C ^ (2 * s) * (N : ℝ) ^ (2 * s - Q.natDegree)) :
    PolyEnergyBound Q := by
  obtain ⟨δ, C₀, hδ, hC₀, hc⟩ := completeSum_power_saving Q hd
  refine polyEnergyBound_of_remaining_three Q hd hδ hC₀ hc hweyl ?_
  intro s η hs hsd hlarge hsδ hη hη1
  exact hmaj hδ hC₀ hc hs hsd hlarge hsδ hη hη1

end
end Work.A3


namespace Work.A3

open MeasureTheory Polynomial Finset
open scoped ENNReal NNReal BigOperators

noncomputable section

/-- **The whole circle method except the major arcs.**  Every input except
`Work.A3.majorArc_contribution` is already proved (`Work.A3.weyl_poly`,
`Work.A3.completeSum_power_saving`, `Work.A3.singInt_bound`, `Work.A3.minorArc_contribution`), so
this reduces the arithmetic core of Area A3 to the single major-arc estimate `hmaj`. -/
theorem polyEnergyBound_of_majorArc (Q : Polynomial ℤ) (hd : 2 ≤ Q.natDegree)
    (hmaj : ∀ {δ C₀ : ℝ}, 0 < δ → 0 < C₀ →
      (∀ (q : ℕ) (a : ℤ), 1 ≤ q → IsCoprime a (q : ℤ) →
        ‖completeSum Q a q‖ ≤ C₀ * (q : ℝ) ^ (1 - δ)) →
      ∀ {s : ℕ} {η : ℝ}, 2 ≤ s → Q.natDegree < 2 * s → 2 * Q.natDegree ≤ s →
        1 < (s : ℝ) * δ → 0 < η → η ≤ 1 →
        ∃ C : ℝ, 0 < C ∧ ∀ N : ℕ, 1 ≤ N →
          ∫ θ in majorArcSet Q N η ∩ Set.Icc (0:ℝ) 1, ‖expSum Q N θ‖ ^ (2 * s) ≤
            C ^ (2 * s) * (N : ℝ) ^ (2 * s - Q.natDegree)) :
    PolyEnergyBound Q :=
  polyEnergyBound_of_weyl_and_majorArc Q hd
    (fun ε hε => weyl_poly Q hd (ε := ε) hε) hmaj

end
end Work.A3

