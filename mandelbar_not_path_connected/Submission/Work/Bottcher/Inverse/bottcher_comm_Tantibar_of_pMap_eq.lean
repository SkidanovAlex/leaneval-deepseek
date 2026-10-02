import Mathlib
import Submission.Work.Bottcher.Defs
import Submission.Work.Bottcher.Basic
import Submission.Work.Bottcher.Green.green_comm
import Submission.Work.Bottcher.Green.green_pos_iff
import Submission.Work.Bottcher.Contraction.isPreconnected_escapeSet
import Submission.Work.Bottcher.Contraction.bottcher_comm_Tantibar_of_analytic
import Submission.Work.ParamRays.isPreconnected_subsingleton_of_pow_two_pow_eq_one
import Submission.Work.ParamRays.exists_pow_two_pow_eq_one

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


open Filter Function
open scoped Topology ComplexConjugate

namespace Work.Bottcher.Inverse

open LeanEval.ComplexAnalysis (Tantibar)

/-!
# The antiholomorphic Böttcher equation from the holomorphic one, for a *continuous* coordinate

Let `φ` be a continuous, nowhere-vanishing function on the escape set `{G_c > 0}` of the tricorn
which is *tangent to the identity at infinity* (`‖φ z - z‖ ≤ ε ‖z‖` ultimately, for every `ε > 0`),
which satisfies the Böttcher equation of the holomorphic quartic `p_c = T_c ∘ T_c`
(`φ (p_c z) = φ z ^ 4`) and whose modulus is `exp (G_c z)`.

Then `φ` satisfies the *antiholomorphic* Böttcher equation of `T_c` itself,
`φ (T_c z) = conj (φ z) ^ 2`.

The proof follows the classical "uniqueness" route, but with `has` (the tangency hypothesis)
replacing analyticity where the analytic proof uses the maximum principle:

* the ratio `K z = conj (φ (T_c z)) / (φ z)^2` is continuous on the (preconnected) escape set,
* it satisfies `K (p_c z) = K z ^ 4` and `K z → 1` at infinity (the latter from `has`, applied at
  both `z` and `T_c z`),
* hence every value `K z` is a root of unity of `2`-power order, so the preconnected image `K '' E`
  is a subsingleton, i.e. `K` is constant,
* and since `K (p_c^n z) = K z ^ (4^n) → 1` along an escaping orbit, the constant is `1`.
-/

/-- The ratio `conj (φ (T_c z)) / (φ z)^2`, whose value is `1` exactly when the
antiholomorphic Böttcher equation `φ (T_c z) = conj (φ z)^2` holds at `z`. -/
private noncomputable def ratio (c : ℂ) (φ : ℂ → ℂ) (z : ℂ) : ℂ :=
  (starRingEnd ℂ) (φ (Tantibar c z)) / (φ z) ^ 2

/-! ## Two elementary filter facts -/

/-- If the even and the odd subsequence of a sequence `u : ℕ → ℂ` both tend to `a`, then so does
`u`. -/
private lemma tendsto_atTop_nat_of_even_odd {u : ℕ → ℂ} {a : ℂ}
    (h1 : Tendsto (fun m : ℕ => u (2 * m)) atTop (nhds a))
    (h2 : Tendsto (fun m : ℕ => u (2 * m + 1)) atTop (nhds a)) :
    Tendsto u atTop (nhds a) := by
  rw [Metric.tendsto_nhds] at h1 h2 ⊢
  intro ε hε
  have h1e := h1 ε hε
  have h2e := h2 ε hε
  rw [Filter.eventually_atTop] at h1e h2e ⊢
  obtain ⟨N1, hN1⟩ := h1e
  obtain ⟨N2, hN2⟩ := h2e
  refine ⟨2 * max N1 N2 + 1, fun k hk => ?_⟩
  rcases Nat.even_or_odd k with he | ho
  · obtain ⟨m, hm⟩ := he
    rw [hm, ← two_mul]
    exact hN1 m (by omega)
  · obtain ⟨m, hm⟩ := ho
    rw [hm]
    exact hN2 m (by omega)

/-! ## `T_c` tends to the cocompact filter -/

/-- `‖T_c z‖ → ∞` along the cocompact filter. -/
private theorem tendsto_norm_Tantibar_cocompact (c : ℂ) :
    Tendsto (fun z : ℂ => ‖Tantibar c z‖) (cocompact ℂ) atTop := by
  rw [Filter.tendsto_atTop]
  intro b
  filter_upwards
    [tendsto_norm_cocompact_atTop.eventually_ge_atTop (Real.sqrt (max (b + ‖c‖) 0))] with z hz
  have hb : b ≤ ‖z‖ ^ 2 - ‖c‖ := by
    have h1 : max (b + ‖c‖) 0 ≤ ‖z‖ ^ 2 := by
      have h2 : (Real.sqrt (max (b + ‖c‖) 0)) ^ 2 = max (b + ‖c‖) 0 :=
        Real.sq_sqrt (le_max_right _ _)
      nlinarith [hz, Real.sqrt_nonneg (max (b + ‖c‖) 0), h2]
    have h3 : b + ‖c‖ ≤ max (b + ‖c‖) 0 := le_max_left _ _
    linarith
  have hbnd : ‖z‖ ^ 2 - ‖c‖ ≤ ‖Tantibar c z‖ := by
    have hT : Tantibar c z = (starRingEnd ℂ z) ^ 2 + c := rfl
    rw [hT]
    have h := norm_sub_norm_le ((starRingEnd ℂ z) ^ 2) (-c)
    rw [sub_neg_eq_add, norm_neg, norm_pow, Complex.norm_conj] at h
    exact h
  linarith

/-- `T_c` is a proper map of the plane: it pushes the cocompact filter to the cocompact filter. -/
private theorem tendsto_Tantibar_cocompact (c : ℂ) :
    Tendsto (Tantibar c) (cocompact ℂ) (cocompact ℂ) := by
  apply tendsto_cocompact_of_tendsto_dist_comp_atTop (0 : ℂ)
  simpa only [dist_zero_right] using tendsto_norm_Tantibar_cocompact c

/-- `‖z‖^2 → ∞` along the cocompact filter of `ℂ`. -/
private theorem tendsto_norm_sq_cocompact :
    Tendsto (fun z : ℂ => ‖z‖ ^ 2) (cocompact ℂ) atTop := by
  have h : Tendsto (fun z : ℂ => ‖z‖ * ‖z‖) (cocompact ℂ) atTop :=
    (tendsto_norm_cocompact_atTop (E := ℂ)).atTop_mul_atTop₀ (tendsto_norm_cocompact_atTop (E := ℂ))
  simpa only [sq] using h

/-! ## Roots of unity of `2`-power order -/

/-- If `ζ ^ (4 ^ m) → 1`, then `ζ` is a root of unity of `2`-power order. -/
private lemma exists_pow_two_pow_eq_one_of_pow_four_pow {ζ : ℂ}
    (h : Tendsto (fun m : ℕ => ζ ^ (4 ^ m)) atTop (nhds 1)) :
    ∃ n : ℕ, ζ ^ (2 ^ n) = 1 := by
  refine Work.ParamRays.exists_pow_two_pow_eq_one (tendsto_atTop_nat_of_even_odd ?_ ?_)
  · convert h using 1
    ext m
    congr 1
    rw [show (4 : ℕ) = 2 ^ 2 from rfl, ← pow_mul]
  · have h2 : Tendsto (fun m : ℕ => (ζ ^ (4 ^ m)) ^ 2) atTop (nhds 1) := by
      have hh := h.pow 2
      simpa using hh
    refine h2.congr' ?_
    filter_upwards with m
    rw [show ζ ^ (2 ^ (2 * m + 1)) = (ζ ^ (4 ^ m)) ^ 2 from ?_]
    rw [show (2 : ℕ) ^ (2 * m + 1) = (4 : ℕ) ^ m * 2 from by rw [pow_succ, pow_mul]; norm_num,
      pow_mul]

theorem bottcher_comm_Tantibar_of_pMap_eq (c : ℂ) (φ : ℂ → ℂ)
    (hcont : ContinuousOn φ (Work.Bottcher.EscapeSet c))
    (hfe : ∀ z : ℂ, 0 < Work.Bottcher.green c z → φ (Work.Bottcher.pMap c z) = φ z ^ 4)
    (hmod : ∀ z : ℂ, 0 < Work.Bottcher.green c z → ‖φ z‖ = Real.exp (Work.Bottcher.green c z))
    (hne : ∀ z : ℂ, 0 < Work.Bottcher.green c z → φ z ≠ 0)
    (has : ∀ ε : ℝ, 0 < ε → ∀ᶠ z : ℂ in Filter.cocompact ℂ, ‖φ z - z‖ ≤ ε * ‖z‖)
    (hesc : ∀ᶠ z : ℂ in Filter.cocompact ℂ, 0 < Work.Bottcher.green c z) :
    ∀ z : ℂ, 0 < Work.Bottcher.green c z →
      φ (LeanEval.ComplexAnalysis.Tantibar c z) = (starRingEnd ℂ) (φ z) ^ 2 := by
  have hTcont : Continuous (Tantibar c) := by
    show Continuous (fun z : ℂ => (starRingEnd ℂ z) ^ 2 + c)
    exact (continuous_star.pow 2).add continuous_const
  have hTmem : ∀ w : ℂ, 0 < green c w → 0 < green c (Tantibar c w) := by
    intro w hw
    rw [Work.Bottcher.Green.green_comm]
    exact mul_pos two_pos hw
  have hpMap_mem : ∀ (z : ℂ), 0 < green c z → ∀ m : ℕ, 0 < green c ((pMap c)^[m] z) := by
    intro z hz m
    rw [Work.Bottcher.Contraction.green_pMap_iterate]
    exact mul_pos (by positivity) hz
  -- ## the ratio is continuous on the escape set
  have hKcont : ContinuousOn (ratio c φ) (EscapeSet c) := by
    have hcomp : ContinuousOn (fun w : ℂ => φ (Tantibar c w)) (EscapeSet c) :=
      hcont.comp hTcont.continuousOn
        (fun w hw => mem_EscapeSet.mpr (hTmem w (mem_EscapeSet.mp hw)))
    have hconj : ContinuousOn (fun w : ℂ => (starRingEnd ℂ) (φ (Tantibar c w))) (EscapeSet c) :=
      Complex.continuous_conj.comp_continuousOn' hcomp
    change ContinuousOn
      (fun w : ℂ => (starRingEnd ℂ) (φ (Tantibar c w)) / (φ w) ^ 2) (EscapeSet c)
    exact hconj.div (hcont.pow 2) (fun w hw => pow_ne_zero 2 (hne w (mem_EscapeSet.mp hw)))
  -- ## the ratio has modulus `1` (uses the modulus hypothesis on `φ`)
  have hratio_mod : ∀ z : ℂ, 0 < green c z → ‖ratio c φ z‖ = 1 := by
    intro z hz
    have hTz : 0 < green c (Tantibar c z) := hTmem z hz
    have hexp : Real.exp (green c (Tantibar c z)) = (Real.exp (green c z)) ^ 2 := by
      rw [Work.Bottcher.Green.green_comm]
      rw [show (2 : ℝ) * green c z = green c z + green c z from by ring, Real.exp_add,
        show Real.exp (green c z) * Real.exp (green c z) = (Real.exp (green c z)) ^ 2 from by ring]
    have h1 : ‖(starRingEnd ℂ) (φ (Tantibar c z))‖ = (Real.exp (green c z)) ^ 2 := by
      rw [Complex.norm_conj, hmod (Tantibar c z) hTz, hexp]
    have h2 : ‖(φ z) ^ 2‖ = (Real.exp (green c z)) ^ 2 := by
      rw [norm_pow, hmod z hz]
    have hpos : (0 : ℝ) < (Real.exp (green c z)) ^ 2 := by positivity
    change ‖(starRingEnd ℂ) (φ (Tantibar c z)) / (φ z) ^ 2‖ = 1
    rw [norm_div, h1, h2, div_self hpos.ne']
  -- ## the ratio satisfies the quartic functional equation
  have hK4 : ∀ z : ℂ, 0 < green c z → ratio c φ (pMap c z) = (ratio c φ z) ^ 4 := by
    intro z hz
    have hTz : 0 < green c (Tantibar c z) := hTmem z hz
    have hcomm : Tantibar c (pMap c z) = pMap c (Tantibar c z) := by
      simpa using (Work.Bottcher.pMap_iterate_Tantibar c z 1).symm
    change (starRingEnd ℂ) (φ (Tantibar c (pMap c z))) / (φ (pMap c z)) ^ 2
        = ((starRingEnd ℂ) (φ (Tantibar c z)) / (φ z) ^ 2) ^ 4
    rw [hcomm, hfe (Tantibar c z) hTz, hfe z hz, map_pow, div_pow,
      show ((φ z) ^ 2) ^ 4 = ((φ z) ^ 4) ^ 2 by ring]
  -- ## the ratio tends to `1` at infinity
  have hφratio : Tendsto (fun z : ℂ => φ z / z) (cocompact ℂ) (nhds 1) := by
    rw [Metric.tendsto_nhds]
    intro ε hε
    filter_upwards [has (ε / 2) (by positivity),
      (isCompact_singleton (x := (0 : ℂ))).compl_mem_cocompact] with z hz hz0
    have hz0' : z ≠ 0 := hz0
    rw [dist_eq_norm]
    have h1 : ‖φ z / z - 1‖ = ‖φ z - z‖ / ‖z‖ := by
      rw [show φ z / z - 1 = (φ z - z) / z from by field_simp, norm_div]
    rw [h1]
    have hzpos : (0 : ℝ) < ‖z‖ := norm_pos_iff.mpr hz0'
    calc ‖φ z - z‖ / ‖z‖ ≤ (ε / 2 * ‖z‖) / ‖z‖ := div_le_div_of_nonneg_right hz (norm_nonneg z)
      _ = ε / 2 := by rw [mul_div_cancel_right₀ _ hzpos.ne']
      _ < ε := by linarith
  have hY : Tendsto (fun z : ℂ => (φ z) ^ 2 / z ^ 2) (cocompact ℂ) (nhds 1) := by
    have h := hφratio.pow 2
    simpa only [div_pow, one_pow] using h
  have hX : Tendsto (fun z : ℂ => (starRingEnd ℂ) (φ (Tantibar c z)) / z ^ 2)
      (cocompact ℂ) (nhds 1) := by
    rw [Metric.tendsto_nhds]
    intro δ hδ
    have h4 : (0 : ℝ) < δ / 4 := by linarith
    have hA : ∀ᶠ z : ℂ in cocompact ℂ,
        ‖φ (Tantibar c z) - Tantibar c z‖ ≤ (δ / 4) * ‖Tantibar c z‖ :=
      (tendsto_Tantibar_cocompact c).eventually (has (δ / 4) h4)
    have hZ : ∀ᶠ z : ℂ in cocompact ℂ, 2 * (1 + δ / 4) * ‖c‖ / δ ≤ ‖z‖ ^ 2 :=
      tendsto_norm_sq_cocompact.eventually_ge_atTop _
    filter_upwards [hA, hZ, (isCompact_singleton (x := (0 : ℂ))).compl_mem_cocompact]
      with z hAz hZz hz0
    have hz0' : z ≠ 0 := hz0
    rw [dist_eq_norm]
    have key : (starRingEnd ℂ) (φ (Tantibar c z)) / z ^ 2 - 1
        = ((starRingEnd ℂ) (φ (Tantibar c z)) - z ^ 2) / z ^ 2 := by
      rw [sub_div, div_self (pow_ne_zero 2 hz0')]
    rw [key, norm_div, show ‖z ^ 2‖ = ‖z‖ ^ 2 from norm_pow z 2]
    have hnum : ‖(starRingEnd ℂ) (φ (Tantibar c z)) - z ^ 2‖
        ≤ (δ / 4) * (‖z‖ ^ 2 + ‖c‖) + ‖c‖ := by
      have hsplit : (starRingEnd ℂ) (φ (Tantibar c z)) - z ^ 2
          = (starRingEnd ℂ) (φ (Tantibar c z) - Tantibar c z) + (starRingEnd ℂ) c := by
        have hTz : (starRingEnd ℂ) (Tantibar c z) = z ^ 2 + (starRingEnd ℂ) c := by
          simp only [LeanEval.ComplexAnalysis.Tantibar, map_add, map_pow, Complex.conj_conj]
        rw [map_sub, hTz]; ring
      rw [hsplit]
      have hTzle : ‖Tantibar c z‖ ≤ ‖z‖ ^ 2 + ‖c‖ := by
        have hT : Tantibar c z = (starRingEnd ℂ z) ^ 2 + c := rfl
        rw [hT]
        calc ‖(starRingEnd ℂ z) ^ 2 + c‖ ≤ ‖(starRingEnd ℂ z) ^ 2‖ + ‖c‖ := norm_add_le _ _
          _ = ‖z‖ ^ 2 + ‖c‖ := by rw [norm_pow, Complex.norm_conj]
      calc ‖(starRingEnd ℂ) (φ (Tantibar c z) - Tantibar c z) + (starRingEnd ℂ) c‖
          ≤ ‖(starRingEnd ℂ) (φ (Tantibar c z) - Tantibar c z)‖ + ‖(starRingEnd ℂ) c‖ :=
            norm_add_le _ _
        _ = ‖φ (Tantibar c z) - Tantibar c z‖ + ‖c‖ := by rw [Complex.norm_conj, Complex.norm_conj]
        _ ≤ (δ / 4) * (‖z‖ ^ 2 + ‖c‖) + ‖c‖ := by
            have hmul := mul_le_mul_of_nonneg_left hTzle (by linarith : (0 : ℝ) ≤ δ / 4)
            linarith [hAz, hmul]
    have hb : (δ / 4 + 1) * ‖c‖ ≤ (δ / 2) * ‖z‖ ^ 2 := by
      have h := hZz
      rw [div_le_iff₀ hδ] at h
      nlinarith [h]
    have hz2pos : (0 : ℝ) < ‖z‖ ^ 2 := pow_pos (norm_pos_iff.mpr hz0') 2
    rw [div_lt_iff₀ hz2pos]
    nlinarith [hnum, hb, hδ, hz2pos]
  have hKcoc : Tendsto (ratio c φ) (cocompact ℂ) (nhds 1) := by
    have hXY : Tendsto ((fun z : ℂ => (starRingEnd ℂ) (φ (Tantibar c z)) / z ^ 2)
        / (fun z : ℂ => (φ z) ^ 2 / z ^ 2)) (cocompact ℂ) (nhds 1) := by
      have h := hX.div hY (by norm_num : (1 : ℂ) ≠ 0)
      simpa only [div_one] using h
    refine hXY.congr' ?_
    filter_upwards [hesc, (isCompact_singleton (x := (0 : ℂ))).compl_mem_cocompact] with z hz hz0
    have hz0' : z ≠ 0 := hz0
    have hφz : φ z ≠ 0 := hne z hz
    change ((starRingEnd ℂ) (φ (Tantibar c z)) / z ^ 2) / ((φ z) ^ 2 / z ^ 2)
        = (starRingEnd ℂ) (φ (Tantibar c z)) / (φ z) ^ 2
    field_simp
  -- ## every value of the ratio is a root of unity of `2`-power order
  have hpMap_coc : ∀ z : ℂ, 0 < green c z →
      Tendsto (fun n : ℕ => (pMap c)^[n] z) atTop (cocompact ℂ) := by
    intro z hz
    apply tendsto_cocompact_of_tendsto_dist_comp_atTop (0 : ℂ)
    have hT : Tendsto (fun n : ℕ => ‖(Tantibar c)^[n] z‖) atTop atTop :=
      (Work.Bottcher.Green.green_pos_iff c z).mp hz
    have h2n : Tendsto (fun n : ℕ => 2 * n) atTop atTop :=
      Filter.tendsto_atTop_atTop.mpr (fun b => ⟨b, fun a ha => by omega⟩)
    refine (hT.comp h2n).congr' ?_
    filter_upwards with n
    simp only [Function.comp_apply, dist_zero_right, Work.Bottcher.pMap_iterate]
  have hKpow : ∀ z : ℂ, 0 < green c z → ∃ n : ℕ, (ratio c φ z) ^ (2 ^ n) = 1 := by
    intro z hz
    have hmem := hpMap_mem z hz
    have hiter : ∀ m : ℕ, (ratio c φ z) ^ (4 ^ m) = ratio c φ ((pMap c)^[m] z) := by
      intro m
      induction m with
      | zero => simp
      | succ m ih =>
          rw [Function.iterate_succ_apply',
            show (4 : ℕ) ^ (m + 1) = 4 ^ m * 4 from pow_succ 4 m, pow_mul, ih,
            ← hK4 ((pMap c)^[m] z) (hmem m)]
    have hseq : Tendsto (fun m : ℕ => (ratio c φ z) ^ (4 ^ m)) atTop (nhds 1) := by
      rw [show (fun m : ℕ => (ratio c φ z) ^ (4 ^ m))
          = fun m : ℕ => ratio c φ ((pMap c)^[m] z) from funext hiter]
      exact hKcoc.comp (hpMap_coc z hz)
    exact exists_pow_two_pow_eq_one_of_pow_four_pow hseq
  -- ## the ratio is constant
  have hsingle : (ratio c φ '' EscapeSet c).Subsingleton := by
    refine Work.ParamRays.isPreconnected_subsingleton_of_pow_two_pow_eq_one ?_ ?_
    · exact (Work.Bottcher.Contraction.isPreconnected_escapeSet c).image _ hKcont
    · rintro ζ ⟨w, hw, rfl⟩
      exact hKpow w (mem_EscapeSet.mp hw)
  intro z hz
  have hzU : z ∈ EscapeSet c := mem_EscapeSet.mpr hz
  have hconst : ∀ w : ℂ, w ∈ EscapeSet c → ratio c φ w = ratio c φ z :=
    fun w hw => hsingle ⟨w, hw, rfl⟩ ⟨z, hzU, rfl⟩
  have hlim : Tendsto (fun n : ℕ => ratio c φ ((pMap c)^[n] z)) atTop (nhds 1) :=
    hKcoc.comp (hpMap_coc z hz)
  have hconstseq : Tendsto (fun _ : ℕ => ratio c φ z) atTop (nhds 1) := by
    refine hlim.congr' ?_
    filter_upwards with n
    exact hconst ((pMap c)^[n] z) (mem_EscapeSet.mpr (hpMap_mem z hz n))
  have hKz : ratio c φ z = 1 := tendsto_nhds_unique tendsto_const_nhds hconstseq
  have hconj : (starRingEnd ℂ) (φ (Tantibar c z)) = (φ z) ^ 2 := by
    have h := hKz
    rw [ratio, div_eq_one_iff_eq (pow_ne_zero 2 (hne z hz))] at h
    exact h
  have h2 := congrArg (starRingEnd ℂ) hconj
  rw [Complex.conj_conj, map_pow] at h2
  exact h2

end Work.Bottcher.Inverse
