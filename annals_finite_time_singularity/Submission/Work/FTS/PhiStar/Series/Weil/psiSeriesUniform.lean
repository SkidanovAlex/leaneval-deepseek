import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Analysis.PSeries
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import Mathlib.Geometry.Manifold.Algebra.Monoid
import Mathlib.Topology.Separation.CompletelyRegular
import Submission.Work.FTS.PhiStar.Series.Weil.Defs
import Submission.Work.FTS.PhiStar.Series.Defs
import Submission.Work.FTS.PhiStar.Series.RemSetup
import Submission.Work.FTS.PhiStar.Series.SummableModes
import Submission.Work.FTS.H2.ModalSolR.radGreenContinuousOn
import Submission.Work.FTS.PhiStar.Series.eFamEneDefs
import Submission.Work.FTS.PhiStar.Series.Deleg.phiAPointwise
import Submission.Work.FTS.PhiStar.Series.SmoothAux.remSource_facts

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section
open scoped Real Topology BigOperators
open MeasureTheory Set Filter

namespace Work.FTS.PhiStar.Series.Weil

set_option autoImplicit false
set_option maxHeartbeats 1600000

/-!
# `psiSeriesUniform` — the Weierstrass test for the mode series of the remainder source

Let `F = RemSource α ψ = α²·𝒜φ·ψ` be the separable remainder source of the `Φ_*` decomposition
and let `t_m(z,θ) = acoeff α m F z · eFam m θ` be the `m`-th mode term of the series
`R α ψ = psiSeries α F = Σ_m t_m`.  This file proves that the *single* pointwise majorant

  `|t_m(z,θ)| ≤ C (1 + 1/z) (m+1)^{-7/2}`   (`m ≥ 1`, `z > 0`, `θ ∈ Iθ`)

already gives everything the Weyl/weak-identity argument needs:

* `ContinuousOn (uncurry (R α ψ)) Q0` (the series is locally uniformly convergent on the open
  quadrant and each partial sum is continuous there);
* on every closed box `[a,b] × [c,d] ⊆ Q0` the partial sums are uniformly bounded by
  `C (1 + 1/a) Σ_m (m+1)^{-7/2}` and converge uniformly to `R α ψ`.

The only points not covered by `hb` are `m = 0` — where the term vanishes identically because
`AngModel.moment` forces `F_*(RemSource α ψ) ≡ 0` and hence `acoeff α 0 F ≡ 0`
(`acoeff_RemSource_zero`) — and the endpoints of `Iθ`, which are included in `Iθ` itself.

The continuity of the individual mode terms is reduced, via `acoeff_RemSource`
(`acoeff α m F z = (α²·bmode m ψ)·radGreen α m (𝒜φ) z`), to `radGreenContinuousOn`, whose
integrability hypothesis `IntegrableOn (𝒜φ)² (Ioi 0)` is proved here from the two explicit
regimes `|𝒜φ| ≤ 20z` on `(0,1]` and `|𝒜φ| ≤ 24/z` on `[1,∞)`.
-/

/-! ## Tails of a summable series tend to zero -/

/-- For a summable `G : ℕ → ℝ`, the tail `Σ_i G (i + k)` tends to `0` as `k → ∞`. -/
private lemma tail_tsum_tendsto_zero {G : ℕ → ℝ} (hG : Summable G) :
    Filter.Tendsto (fun k : ℕ => ∑' i : ℕ, G (i + k)) Filter.atTop (nhds 0) := by
  have hsum : Filter.Tendsto (fun k : ℕ => ∑ i ∈ Finset.range k, G i) Filter.atTop
      (nhds (∑' i : ℕ, G i)) := hG.hasSum.tendsto_sum_nat
  have heq : (fun k : ℕ => ∑' i : ℕ, G (i + k))
      = fun k : ℕ => (∑' i : ℕ, G i) - ∑ i ∈ Finset.range k, G i := by
    funext k
    have h := hG.sum_add_tsum_nat_add k
    linarith
  rw [heq]
  have h2 : Filter.Tendsto (fun k : ℕ => (∑' i : ℕ, G i) - ∑ i ∈ Finset.range k, G i)
      Filter.atTop (nhds ((∑' i : ℕ, G i) - (∑' i : ℕ, G i))) :=
    tendsto_const_nhds.sub hsum
  simpa using h2

/-! ## The square of the radial profile is integrable on the half-line -/

private lemma phiA_sq_integrableOn {α : ℝ} (hα : 0 < α) (hα1 : α ≤ 1) :
    IntegrableOn (fun t : ℝ => Work.FTS.VocabO.phiA α t ^ 2) (Set.Ioi 0) := by
  have hcont : ContinuousOn (fun t : ℝ => Work.FTS.VocabO.phiA α t ^ 2) (Set.Ioi 0) :=
    (Work.FTS.PhiStar.Series.Deleg.psiSeriesIntegrability_phiACont α).pow 2
  -- the small-`z` piece: dominated by `400 z²` on `(0,1)`
  have hIoo : IntegrableOn (fun t : ℝ => Work.FTS.VocabO.phiA α t ^ 2) (Set.Ioo (0 : ℝ) 1) := by
    have hdom : Integrable (fun t : ℝ => (400 : ℝ) * t ^ 2)
        (volume.restrict (Set.Ioo (0 : ℝ) 1)) := by
      have hpow : IntegrableOn (fun t : ℝ => t ^ (2 : ℝ)) (Set.Ioo (0 : ℝ) 1) :=
        (intervalIntegral.integrableOn_Ioo_rpow_iff (s := (2 : ℝ)) (t := 1) one_pos).mpr
          (by norm_num)
      simpa only [Real.rpow_two] using hpow.const_mul (400 : ℝ)
    have hsm : AEStronglyMeasurable (fun t : ℝ => Work.FTS.VocabO.phiA α t ^ 2)
        (volume.restrict (Set.Ioo (0 : ℝ) 1)) := by
      have hsub : Set.Ioo (0 : ℝ) 1 ⊆ Set.Ioi (0 : ℝ) := fun t ht => ht.1
      exact (hcont.mono hsub).aestronglyMeasurable measurableSet_Ioo
    refine hdom.mono' hsm ?_
    filter_upwards [ae_restrict_mem measurableSet_Ioo] with t ht
    rw [Real.norm_eq_abs, abs_sq]
    have hb := Work.FTS.PhiStar.Series.Deleg.phiA_abs_le_small hα hα1 ht.1 ht.2.le
    have h3 : Work.FTS.VocabO.phiA α t ^ 2 ≤ (20 * t) ^ 2 := by
      have h := pow_le_pow_left₀ (abs_nonneg (Work.FTS.VocabO.phiA α t)) hb 2
      rwa [sq_abs] at h
    calc Work.FTS.VocabO.phiA α t ^ 2 ≤ (20 * t) ^ 2 := h3
      _ = 400 * t ^ 2 := by ring
  -- the large-`z` piece: dominated by `576 / z²` on `(1,∞)`
  have hIoi : IntegrableOn (fun t : ℝ => Work.FTS.VocabO.phiA α t ^ 2) (Set.Ioi (1 : ℝ)) := by
    have hdom : Integrable (fun t : ℝ => (576 : ℝ) * (t ^ 2)⁻¹)
        (volume.restrict (Set.Ioi (1 : ℝ))) := by
      have hpow : IntegrableOn (fun t : ℝ => t ^ (-(2 : ℝ))) (Set.Ioi (1 : ℝ)) :=
        (integrableOn_Ioi_rpow_iff (s := -(2 : ℝ)) (t := 1) one_pos).mpr (by norm_num)
      have hk : IntegrableOn (fun t : ℝ => (576 : ℝ) * t ^ (-(2 : ℝ))) (Set.Ioi (1 : ℝ)) :=
        hpow.const_mul (576 : ℝ)
      refine hk.congr_fun ?_ measurableSet_Ioi
      intro t ht
      have ht0 : (0 : ℝ) < t := lt_trans zero_lt_one ht
      show (576 : ℝ) * t ^ (-(2 : ℝ)) = 576 * (t ^ 2)⁻¹
      rw [Real.rpow_neg ht0.le, Real.rpow_two]
    have hsm : AEStronglyMeasurable (fun t : ℝ => Work.FTS.VocabO.phiA α t ^ 2)
        (volume.restrict (Set.Ioi (1 : ℝ))) := by
      have hsub : Set.Ioi (1 : ℝ) ⊆ Set.Ioi (0 : ℝ) :=
        fun t ht => lt_trans zero_lt_one (show (1 : ℝ) < t from ht)
      exact (hcont.mono hsub).aestronglyMeasurable measurableSet_Ioi
    refine hdom.mono' hsm ?_
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
    rw [Real.norm_eq_abs, abs_sq]
    have ht0 : (0 : ℝ) < t := lt_trans zero_lt_one ht
    have hb := Work.FTS.PhiStar.Series.Deleg.phiA_abs_le_large hα hα1 ht.le
    have h3 : Work.FTS.VocabO.phiA α t ^ 2 ≤ (24 / t) ^ 2 := by
      have h := pow_le_pow_left₀ (abs_nonneg (Work.FTS.VocabO.phiA α t)) hb 2
      rwa [sq_abs] at h
    have h4 : (24 / t) ^ 2 = 576 * (t ^ 2)⁻¹ := by
      rw [div_pow, div_eq_mul_inv]
      norm_num
    calc Work.FTS.VocabO.phiA α t ^ 2 ≤ (24 / t) ^ 2 := h3
      _ = 576 * (t ^ 2)⁻¹ := h4
  have hset : Set.Ioc (0 : ℝ) 1 ∪ Set.Ioi 1 = Set.Ioi 0 :=
    Set.Ioc_union_Ioi_eq_Ioi (zero_le_one : (0 : ℝ) ≤ 1)
  have hIoc : IntegrableOn (fun t : ℝ => Work.FTS.VocabO.phiA α t ^ 2) (Set.Ioc (0 : ℝ) 1) :=
    (integrableOn_Ioc_iff_integrableOn_Ioo (f := fun t : ℝ => Work.FTS.VocabO.phiA α t ^ 2)
      (a := (0 : ℝ)) (b := 1)).mpr hIoo
  rw [← hset]
  exact hIoc.union hIoi

/-! ## Every mode term is continuous on the quadrant -/

private lemma modeContinuous (α : ℝ) (ψ : ℝ → ℝ) (hα : 0 < α) (hα1 : α ≤ 1)
    (hψ : Work.FTS.PhiStar.AngModel α ψ) (m : ℕ) :
    ContinuousOn (fun p : ℝ × ℝ => Work.FTS.PhiStar.Series.acoeff α m
        (Work.FTS.PhiStar.RemSource α ψ) p.1
      * Work.FTS.PhiStar.Gegenbauer.eFam m p.2) Work.FTS.EllipticEst.Q0 := by
  have hphi := phiA_sq_integrableOn hα hα1
  have hcmode : ∀ t : ℝ, Work.FTS.PhiStar.Series.cmode m (Work.FTS.PhiStar.RemSource α ψ) t
      = (α ^ 2 * Work.FTS.PhiStar.Series.bmode m ψ) * Work.FTS.VocabO.phiA α t := by
    intro t
    rw [Work.FTS.PhiStar.Series.cmode_RemSource]
    ring
  have hc : IntegrableOn (fun t : ℝ => Work.FTS.PhiStar.Series.cmode m
      (Work.FTS.PhiStar.RemSource α ψ) t ^ 2) (Set.Ioi 0) := by
    have h1 : IntegrableOn (fun t : ℝ => ((α ^ 2 * Work.FTS.PhiStar.Series.bmode m ψ) ^ 2)
        * Work.FTS.VocabO.phiA α t ^ 2) (Set.Ioi 0) := hphi.const_mul _
    refine h1.congr_fun ?_ measurableSet_Ioi
    intro t ht
    show ((α ^ 2 * Work.FTS.PhiStar.Series.bmode m ψ) ^ 2) * Work.FTS.VocabO.phiA α t ^ 2
      = Work.FTS.PhiStar.Series.cmode m (Work.FTS.PhiStar.RemSource α ψ) t ^ 2
    rw [hcmode t]
    ring
  have hcm : AEStronglyMeasurable (fun t : ℝ => Work.FTS.PhiStar.Series.cmode m
      (Work.FTS.PhiStar.RemSource α ψ) t) (volume.restrict (Set.Ioi 0)) := by
    have hcont : ContinuousOn (fun t : ℝ => Work.FTS.PhiStar.Series.cmode m
        (Work.FTS.PhiStar.RemSource α ψ) t) (Set.Ioi 0) := by
      have h0 : ContinuousOn (fun t : ℝ =>
          (α ^ 2 * Work.FTS.PhiStar.Series.bmode m ψ) * Work.FTS.VocabO.phiA α t)
          (Set.Ioi 0) :=
        (Work.FTS.PhiStar.Series.Deleg.psiSeriesIntegrability_phiACont α).const_mul _
      have hfun : (fun t : ℝ => Work.FTS.PhiStar.Series.cmode m (Work.FTS.PhiStar.RemSource α ψ) t)
          = fun t : ℝ => (α ^ 2 * Work.FTS.PhiStar.Series.bmode m ψ)
              * Work.FTS.VocabO.phiA α t :=
        funext fun t => hcmode t
      rw [hfun]
      exact h0
    exact hcont.aestronglyMeasurable measurableSet_Ioi
  have hrad : ContinuousOn (fun z : ℝ => Work.FTS.PhiStar.Series.acoeff α m
      (Work.FTS.PhiStar.RemSource α ψ) z) (Set.Ioi 0) := by
    show ContinuousOn (Work.FTS.PhiStar.Radial.radGreen α m
      (fun t : ℝ => Work.FTS.PhiStar.Series.cmode m (Work.FTS.PhiStar.RemSource α ψ) t))
      (Set.Ioi 0)
    exact Work.FTS.H2.ModalSolR.radGreenContinuousOn hα hα1 m hc hcm
  have hang : ContinuousOn (fun p : ℝ × ℝ => Work.FTS.PhiStar.Gegenbauer.eFam m p.2)
      Work.FTS.EllipticEst.Q0 :=
    (continuous_eFam m).comp_continuousOn continuous_snd.continuousOn
  exact (hrad.comp continuous_fst.continuousOn (fun p hp =>
    (Work.FTS.EllipticEst.mem_Q0.mp (show (p.1, p.2) ∈ Work.FTS.EllipticEst.Q0 from hp)).1)).mul
    hang

/-! ## The partial sums are continuous on the quadrant -/

private lemma psiTrunc_continuousOn (α : ℝ) (ψ : ℝ → ℝ) (hα : 0 < α) (hα1 : α ≤ 1)
    (hψ : Work.FTS.PhiStar.AngModel α ψ) (N : ℕ) :
    ContinuousOn (Function.uncurry (Work.FTS.PhiStar.Series.psiTrunc α
      (Work.FTS.PhiStar.RemSource α ψ) N)) Work.FTS.EllipticEst.Q0 := by
  have hfun : Function.uncurry (Work.FTS.PhiStar.Series.psiTrunc α
        (Work.FTS.PhiStar.RemSource α ψ) N)
      = fun p : ℝ × ℝ => ∑ m ∈ Finset.range (N + 1),
          Work.FTS.PhiStar.Series.acoeff α m (Work.FTS.PhiStar.RemSource α ψ) p.1
            * Work.FTS.PhiStar.Gegenbauer.eFam m p.2 := by
    funext p
    simp only [Function.uncurry, Work.FTS.PhiStar.Series.psiTrunc, Finset.sum_apply]
  rw [hfun]
  exact continuousOn_finsetSum (Finset.range (N + 1))
    (fun m _ => modeContinuous α ψ hα hα1 hψ m)

/-! ## The Weierstrass estimate on a box -/

/-- On a closed box `[a,b] × [c,d] ⊆ Q0` the partial sums are uniformly bounded by
`C (1 + 1/a) Σ_m (m+1)^{-7/2}` and converge to the series uniformly. -/
private lemma box_estimate (α : ℝ) (ψ : ℝ → ℝ) {C : ℝ}
    (hα : 0 < α) (hα1 : α ≤ 1) (hψ : Work.FTS.PhiStar.AngModel α ψ) (hC : 0 < C)
    (hb : ∀ m : ℕ, 1 ≤ m → ∀ z θ : ℝ, 0 < z → θ ∈ Work.Spaces.Iθ →
      |Work.FTS.PhiStar.Series.acoeff α m (Work.FTS.PhiStar.RemSource α ψ) z
        * Work.FTS.PhiStar.Gegenbauer.eFam m θ|
        ≤ C * (1 + 1 / z) * ((m : ℝ) + 1) ^ (-(7 / 2 : ℝ)))
    {a b c d : ℝ} (ha : 0 < a) (hab : a ≤ b) (hc : 0 < c) (hcd : c ≤ d) (hd : d < π / 2) :
    (∀ (N : ℕ) (p : ℝ × ℝ), p ∈ box a b c d →
      |Work.FTS.PhiStar.Series.psiTrunc α (Work.FTS.PhiStar.RemSource α ψ) N p.1 p.2|
        ≤ C * (1 + 1 / a) * (∑' m : ℕ, ((m : ℝ) + 1) ^ (-(7 / 2 : ℝ)))) ∧
    (∀ ε : ℝ, 0 < ε → ∃ N : ℕ, ∀ n : ℕ, N ≤ n → ∀ p : ℝ × ℝ,
      p ∈ box a b c d →
      |Work.FTS.PhiStar.Series.psiTrunc α (Work.FTS.PhiStar.RemSource α ψ) n p.1 p.2
        - R α ψ p.1 p.2| < ε) := by
  have hmaj : Summable (fun m : ℕ => ((m : ℝ) + 1) ^ (-(7 / 2 : ℝ))) := by
    have h : Summable (fun n : ℕ => (n : ℝ) ^ (-(7 / 2 : ℝ))) :=
      (Real.summable_nat_rpow (p := (-(7 / 2 : ℝ)))).mpr (by norm_num)
    have h' := (summable_nat_add_iff (f := fun n : ℕ => (n : ℝ) ^ (-(7 / 2 : ℝ))) 1).mpr h
    simpa only [Nat.cast_add, Nat.cast_one] using h'
  have hmaj_nn : ∀ m : ℕ, 0 ≤ ((m : ℝ) + 1) ^ (-(7 / 2 : ℝ)) :=
    fun m => Real.rpow_nonneg (by positivity) _
  -- the `m = 0` mode coefficient vanishes
  have hzero : ∀ z : ℝ, 0 < z → Work.FTS.PhiStar.Series.acoeff α 0
      (Work.FTS.PhiStar.RemSource α ψ) z = 0 :=
    Work.FTS.PhiStar.Series.acoeff_RemSource_zero α ψ (fun t _ => by
      rw [Work.FTS.PhiStar.Series.Fstar_RemSource, hψ.moment, mul_zero])
  -- the termwise majorant
  have hterm : ∀ (m : ℕ) {z θ : ℝ}, 0 < z → θ ∈ Work.Spaces.Iθ → a ≤ z →
      |Work.FTS.PhiStar.Series.acoeff α m (Work.FTS.PhiStar.RemSource α ψ) z
        * Work.FTS.PhiStar.Gegenbauer.eFam m θ|
        ≤ C * (1 + 1 / a) * ((m : ℝ) + 1) ^ (-(7 / 2 : ℝ)) := by
    intro m z θ hz hθ haz
    rcases Nat.eq_zero_or_pos m with hm | hm
    · rw [hm, hzero z hz, zero_mul, abs_zero]
      exact mul_nonneg (mul_nonneg (le_of_lt hC) (by positivity)) (hmaj_nn 0)
    · have h1 := hb m hm z θ hz hθ
      have hg : 0 ≤ ((m : ℝ) + 1) ^ (-(7 / 2 : ℝ)) := hmaj_nn m
      have h2 : 1 + 1 / z ≤ 1 + 1 / a := by
        have := one_div_le_one_div_of_le ha haz
        linarith
      calc |Work.FTS.PhiStar.Series.acoeff α m (Work.FTS.PhiStar.RemSource α ψ) z
            * Work.FTS.PhiStar.Gegenbauer.eFam m θ|
          ≤ C * (1 + 1 / z) * ((m : ℝ) + 1) ^ (-(7 / 2 : ℝ)) := h1
        _ ≤ C * (1 + 1 / a) * ((m : ℝ) + 1) ^ (-(7 / 2 : ℝ)) :=
            mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left h2 (le_of_lt hC)) hg
  refine ⟨?_, ?_⟩
  · intro N p hp
    obtain ⟨hpz, hpθ⟩ := mem_box.mp hp
    have hz : 0 < p.1 := lt_of_lt_of_le ha hpz.1
    have hθ : p.2 ∈ Work.Spaces.Iθ :=
      ⟨(lt_of_lt_of_le hc hpθ.1).le, (lt_of_le_of_lt hpθ.2 hd).le⟩
    have h1 : |Work.FTS.PhiStar.Series.psiTrunc α (Work.FTS.PhiStar.RemSource α ψ) N p.1 p.2|
        ≤ ∑ m ∈ Finset.range (N + 1), |Work.FTS.PhiStar.Series.acoeff α m
            (Work.FTS.PhiStar.RemSource α ψ) p.1
          * Work.FTS.PhiStar.Gegenbauer.eFam m p.2| := by
      rw [Work.FTS.PhiStar.Series.psiTrunc]
      exact Finset.abs_sum_le_sum_abs _ _
    have h2 : ∑ m ∈ Finset.range (N + 1), |Work.FTS.PhiStar.Series.acoeff α m
            (Work.FTS.PhiStar.RemSource α ψ) p.1
          * Work.FTS.PhiStar.Gegenbauer.eFam m p.2|
        ≤ ∑ m ∈ Finset.range (N + 1),
            C * (1 + 1 / a) * ((m : ℝ) + 1) ^ (-(7 / 2 : ℝ)) :=
      Finset.sum_le_sum (fun m _ => hterm m hz hθ hpz.1)
    have h3 : ∑ m ∈ Finset.range (N + 1),
            C * (1 + 1 / a) * ((m : ℝ) + 1) ^ (-(7 / 2 : ℝ))
        = C * (1 + 1 / a) * ∑ m ∈ Finset.range (N + 1),
            ((m : ℝ) + 1) ^ (-(7 / 2 : ℝ)) := by
      rw [Finset.mul_sum]
    have h4 : ∑ m ∈ Finset.range (N + 1), ((m : ℝ) + 1) ^ (-(7 / 2 : ℝ))
        ≤ ∑' m : ℕ, ((m : ℝ) + 1) ^ (-(7 / 2 : ℝ)) :=
      hmaj.sum_le_tsum (Finset.range (N + 1)) (fun m _ => hmaj_nn m)
    have h5 : 0 ≤ C * (1 + 1 / a) := mul_nonneg (le_of_lt hC) (by positivity)
    calc |Work.FTS.PhiStar.Series.psiTrunc α (Work.FTS.PhiStar.RemSource α ψ) N p.1 p.2|
        ≤ ∑ m ∈ Finset.range (N + 1), C * (1 + 1 / a)
            * ((m : ℝ) + 1) ^ (-(7 / 2 : ℝ)) := le_trans h1 h2
      _ = C * (1 + 1 / a) * ∑ m ∈ Finset.range (N + 1),
            ((m : ℝ) + 1) ^ (-(7 / 2 : ℝ)) := h3
      _ ≤ C * (1 + 1 / a) * (∑' m : ℕ, ((m : ℝ) + 1) ^ (-(7 / 2 : ℝ))) :=
          mul_le_mul_of_nonneg_left h4 h5
  · intro ε hε
    have hmajK : Summable (fun m : ℕ => C * (1 + 1 / a) * ((m : ℝ) + 1) ^ (-(7 / 2 : ℝ))) :=
      hmaj.mul_left _
    obtain ⟨N, hN⟩ := Metric.tendsto_atTop.mp (tail_tsum_tendsto_zero hmajK) ε hε
    refine ⟨N, fun n hn p hp => ?_⟩
    obtain ⟨hpz, hpθ⟩ := mem_box.mp hp
    have hz : 0 < p.1 := lt_of_lt_of_le ha hpz.1
    have hθ : p.2 ∈ Work.Spaces.Iθ :=
      ⟨(lt_of_lt_of_le hc hpθ.1).le, (lt_of_le_of_lt hpθ.2 hd).le⟩
    have hsummable : Summable (fun m : ℕ => Work.FTS.PhiStar.Series.acoeff α m
        (Work.FTS.PhiStar.RemSource α ψ) p.1 * Work.FTS.PhiStar.Gegenbauer.eFam m p.2) :=
      Summable.of_norm_bounded hmajK (fun m => by
        rw [Real.norm_eq_abs]
        exact hterm m hz hθ hpz.1)
    have hsplit := hsummable.sum_add_tsum_nat_add (n + 1)
    have hdiff : Work.FTS.PhiStar.Series.psiTrunc α (Work.FTS.PhiStar.RemSource α ψ) n p.1 p.2
        - R α ψ p.1 p.2
        = -(∑' i : ℕ, Work.FTS.PhiStar.Series.acoeff α (i + (n + 1))
              (Work.FTS.PhiStar.RemSource α ψ) p.1
            * Work.FTS.PhiStar.Gegenbauer.eFam (i + (n + 1)) p.2) := by
      rw [R_apply, Work.FTS.PhiStar.Series.psiSeries, Work.FTS.PhiStar.Series.psiTrunc]
      linarith [hsplit]
    rw [hdiff, abs_neg]
    have hshift : Summable (fun i : ℕ => C * (1 + 1 / a)
        * (((i + (n + 1) : ℕ) : ℝ) + 1) ^ (-(7 / 2 : ℝ))) :=
      (summable_nat_add_iff (f := fun m : ℕ => C * (1 + 1 / a)
        * ((m : ℝ) + 1) ^ (-(7 / 2 : ℝ))) (n + 1)).mpr hmajK
    have hnorms : Summable (fun i : ℕ => ‖Work.FTS.PhiStar.Series.acoeff α (i + (n + 1))
        (Work.FTS.PhiStar.RemSource α ψ) p.1
        * Work.FTS.PhiStar.Gegenbauer.eFam (i + (n + 1)) p.2‖) :=
      Summable.of_nonneg_of_le (fun i => norm_nonneg _) (fun i => by
        rw [Real.norm_eq_abs]
        exact hterm (i + (n + 1)) hz hθ hpz.1) hshift
    have hlt : |∑' i : ℕ, C * (1 + 1 / a)
        * (((i + (n + 1) : ℕ) : ℝ) + 1) ^ (-(7 / 2 : ℝ))| < ε := by
      have hk : N ≤ n + 1 := by omega
      simpa only [Real.dist_eq, sub_zero] using hN (n + 1) hk
    calc |∑' i : ℕ, Work.FTS.PhiStar.Series.acoeff α (i + (n + 1))
            (Work.FTS.PhiStar.RemSource α ψ) p.1
          * Work.FTS.PhiStar.Gegenbauer.eFam (i + (n + 1)) p.2|
        = ‖∑' i : ℕ, Work.FTS.PhiStar.Series.acoeff α (i + (n + 1))
            (Work.FTS.PhiStar.RemSource α ψ) p.1
          * Work.FTS.PhiStar.Gegenbauer.eFam (i + (n + 1)) p.2‖ := (Real.norm_eq_abs _).symm
      _ ≤ ∑' i : ℕ, ‖Work.FTS.PhiStar.Series.acoeff α (i + (n + 1))
            (Work.FTS.PhiStar.RemSource α ψ) p.1
          * Work.FTS.PhiStar.Gegenbauer.eFam (i + (n + 1)) p.2‖ :=
          norm_tsum_le_tsum_norm hnorms
      _ ≤ ∑' i : ℕ, C * (1 + 1 / a) * (((i + (n + 1) : ℕ) : ℝ) + 1) ^ (-(7 / 2 : ℝ)) :=
          Summable.tsum_le_tsum (fun i => by
            rw [Real.norm_eq_abs]
            exact hterm (i + (n + 1)) hz hθ hpz.1) hnorms hshift
      _ < ε := lt_of_le_of_lt (le_abs_self _) hlt

/-! ## The theorem -/

theorem psiSeriesUniform (α : ℝ) (ψ : ℝ → ℝ) (hα : 0 < α) (hα1 : α ≤ 1)
    (hψ : Work.FTS.PhiStar.AngModel α ψ) {C : ℝ} (hC : 0 < C)
    (hb : ∀ m : ℕ, 1 ≤ m → ∀ z θ : ℝ, 0 < z → θ ∈ Work.Spaces.Iθ →
      |Work.FTS.PhiStar.Series.acoeff α m (Work.FTS.PhiStar.RemSource α ψ) z
        * Work.FTS.PhiStar.Gegenbauer.eFam m θ|
        ≤ C * (1 + 1 / z) * ((m : ℝ) + 1) ^ (-(7 / 2 : ℝ))) :
    ContinuousOn (Function.uncurry (Work.FTS.PhiStar.Series.Weil.R α ψ))
        Work.FTS.EllipticEst.Q0 ∧
    (∀ (a b c d : ℝ), 0 < a → a ≤ b → 0 < c → c ≤ d → d < π / 2 →
      (∀ (N : ℕ) (p : ℝ × ℝ), p ∈ Work.FTS.PhiStar.Series.Weil.box a b c d →
        |Work.FTS.PhiStar.Series.psiTrunc α (Work.FTS.PhiStar.RemSource α ψ) N p.1 p.2|
          ≤ C * (1 + 1 / a) * (∑' m : ℕ, ((m : ℝ) + 1) ^ (-(7 / 2 : ℝ)))) ∧
      (∀ ε : ℝ, 0 < ε → ∃ N : ℕ, ∀ n : ℕ, N ≤ n → ∀ p : ℝ × ℝ,
        p ∈ Work.FTS.PhiStar.Series.Weil.box a b c d →
        |Work.FTS.PhiStar.Series.psiTrunc α (Work.FTS.PhiStar.RemSource α ψ) n p.1 p.2
          - Work.FTS.PhiStar.Series.Weil.R α ψ p.1 p.2| ≤ ε)) := by
  refine ⟨?_, fun a b c d ha hab hc hcd hd => ?_⟩
  · -- continuity of the series, from local uniform convergence
    intro p hp
    have hp' : 0 < p.1 ∧ 0 < p.2 ∧ p.2 < π / 2 :=
      Work.FTS.EllipticEst.mem_Q0.mp (show (p.1, p.2) ∈ Work.FTS.EllipticEst.Q0 from hp)
    obtain ⟨hz, hθ0, hθ1⟩ := hp'
    have ha : 0 < p.1 / 2 := by linarith
    have hab : p.1 / 2 ≤ p.1 + 1 := by linarith
    have hc : 0 < p.2 / 2 := by linarith
    have hcd : p.2 / 2 ≤ (p.2 + π / 2) / 2 := by linarith [Real.pi_pos]
    have hd : (p.2 + π / 2) / 2 < π / 2 := by linarith
    obtain ⟨-, hunif⟩ := box_estimate α ψ hα hα1 hψ hC hb ha hab hc hcd hd
    have hconv : TendstoUniformlyOn
        (fun n : ℕ => Function.uncurry (Work.FTS.PhiStar.Series.psiTrunc α
          (Work.FTS.PhiStar.RemSource α ψ) n))
        (Function.uncurry (R α ψ)) atTop (box (p.1 / 2) (p.1 + 1) (p.2 / 2) ((p.2 + π / 2) / 2)) := by
      rw [Metric.tendstoUniformlyOn_iff]
      intro ε hε
      obtain ⟨N, hN⟩ := hunif ε hε
      filter_upwards [Filter.eventually_ge_atTop N] with n hn x hx
      simp only [Function.uncurry]
      rw [Real.dist_eq, abs_sub_comm]
      exact hN n hn x hx
    have hcontBox : ContinuousOn (Function.uncurry (R α ψ))
        (box (p.1 / 2) (p.1 + 1) (p.2 / 2) ((p.2 + π / 2) / 2)) :=
      hconv.continuousOn (Frequently.of_forall (fun n =>
        (psiTrunc_continuousOn α ψ hα hα1 hψ n).mono
          (box_subset_Q0 ha hab hc hcd hd)))
    have hmem : box (p.1 / 2) (p.1 + 1) (p.2 / 2) ((p.2 + π / 2) / 2) ∈ 𝓝 p := by
      refine Filter.mem_of_superset ((isOpen_Ioo.prod isOpen_Ioo).mem_nhds
        (show p ∈ Set.Ioo (p.1 / 2) (p.1 + 1) ×ˢ Set.Ioo (p.2 / 2) ((p.2 + π / 2) / 2) from
          ⟨⟨by linarith, by linarith⟩, ⟨by linarith, by linarith⟩⟩)) ?_
      rintro q ⟨hq1, hq2⟩
      exact ⟨⟨le_of_lt hq1.1, le_of_lt hq1.2⟩, ⟨le_of_lt hq2.1, le_of_lt hq2.2⟩⟩
    exact (hcontBox.continuousAt hmem).continuousWithinAt
  · obtain ⟨hbnd, hunif⟩ := box_estimate α ψ hα hα1 hψ hC hb ha hab hc hcd hd
    refine ⟨hbnd, fun ε hε => ?_⟩
    obtain ⟨N, hN⟩ := hunif ε hε
    exact ⟨N, fun n hn p hp => le_of_lt (hN n hn p hp)⟩

end Work.FTS.PhiStar.Series.Weil
