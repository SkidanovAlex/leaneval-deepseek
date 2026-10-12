import Mathlib.MeasureTheory.Function.SpecialFunctions.Basic
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Submission.Work.BoseFixB1B.MeanSqPiece.Toolkit
import Submission.Work.BoseFixB1S.MeanSq.Box3
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
The proof below goes through the sliding-window toolkit
`Submission/Work/BoseFixB1B/MeanSqPiece/Toolkit.lean` (namespace
`Work.BoseFixB1B.MeanSqPiece.CruxMean`, all of whose lemmas are already proved): its
window `I1 h ℓ u` is exactly
`Work.BoseFixB1S.slI ℓ h u`, its squared Cauchy–Schwarz bound `cs_left` turns the squared window
mean into `ofReal (2 L^{-3/2})` times the weighted `L²` mass with weight `wgtL ℓ y = √(y + ℓ/2)`,
and its counting lemma `counting_left` bounds, for each `y` in `[-ℓ/2,ℓ/2]`, the total
`2 L(t)^{-3/2}`-weight of the windows (in the left-clipped regime) that contain `y` by
`(4/h)·(wgtL ℓ y)^{-1}`.  Tonelli plus the a.e. cancellation `wgtL·(wgtL)^{-1} = 1` then give the
constant `4/h`.
-/

open MeasureTheory
open scoped ENNReal
open Work.BoseFixB1B.MeanSqPiece.CruxMean

namespace Work.BoseFixB1.Core

/-- The sliding window `slI` is the toolkit's `I1`. -/
private lemma slI_eq_I1 (ℓ h u : ℝ) : Work.BoseFixB1S.slI ℓ h u = I1 h ℓ u := by
  rw [Work.BoseFixB1S.slI_eq, I1_eq_Icc, show -ℓ / 2 = -(ℓ / 2) by ring, Set.Icc_inter_Icc]

/-- The set of `u` for which a fixed `y` lies in the window is measurable. -/
private lemma measurableSet_I1_preimage (ℓ h y : ℝ) : MeasurableSet {u : ℝ | y ∈ I1 h ℓ u} := by
  have hset : {u : ℝ | y ∈ I1 h ℓ u}
      = {u : ℝ | max (-(ℓ / 2)) (h * u - h / 2) ≤ y}
        ∩ {u : ℝ | y ≤ min (ℓ / 2) (h * u + h / 2)} := by
    ext u
    simp only [Set.mem_setOf_eq, Set.mem_inter_iff, I1_eq_Icc, Set.mem_Icc]
  rw [hset]
  exact (isClosed_le (by fun_prop : Continuous fun u : ℝ => max (-(ℓ / 2)) (h * u - h / 2))
      continuous_const).measurableSet.inter
    (isClosed_le continuous_const
      (by fun_prop : Continuous fun u : ℝ => min (ℓ / 2) (h * u + h / 2))).measurableSet

/-- Joint measurability of the window relation. -/
private lemma measurableSet_prod_I1 (ℓ h : ℝ) : MeasurableSet {p : ℝ × ℝ | p.2 ∈ I1 h ℓ p.1} := by
  have hset : {p : ℝ × ℝ | p.2 ∈ I1 h ℓ p.1}
      = {p : ℝ × ℝ | max (-(ℓ / 2)) (h * p.1 - h / 2) ≤ p.2}
        ∩ {p : ℝ × ℝ | p.2 ≤ min (ℓ / 2) (h * p.1 + h / 2)} := by
    ext p
    simp only [Set.mem_setOf_eq, Set.mem_inter_iff, I1_eq_Icc, Set.mem_Icc]
  rw [hset]
  exact (isClosed_le (by fun_prop : Continuous fun p : ℝ × ℝ => max (-(ℓ / 2)) (h * p.1 - h / 2))
      continuous_snd).measurableSet.inter
    (isClosed_le continuous_snd
      (by fun_prop : Continuous fun p : ℝ × ℝ => min (ℓ / 2) (h * p.1 + h / 2))).measurableSet

private lemma measurable_L1 (ℓ h : ℝ) : Measurable (fun u : ℝ => L1 h ℓ u) := by
  rw [show (fun u : ℝ => L1 h ℓ u)
      = fun u : ℝ => max (min (ℓ / 2) (h * u + h / 2) - max (-(ℓ / 2)) (h * u - h / 2)) 0 from
    funext fun u => L1_eq h ℓ u]
  fun_prop

private lemma measurable_wgtL (ℓ : ℝ) : Measurable (wgtL ℓ) := by
  show Measurable fun y : ℝ => ENNReal.ofReal (Real.sqrt (y + ℓ / 2))
  exact ENNReal.measurable_ofReal.comp
    (Real.continuous_sqrt.measurable.comp (measurable_id.add_const _))

private lemma lintegral_set_const_mul' {s : Set ℝ} (hs : MeasurableSet s) (c : ℝ≥0∞)
    (hc : c ≠ ⊤) (f : ℝ → ℝ≥0∞) :
    ∫⁻ x in s, c * f x = c * ∫⁻ x in s, f x := by
  rw [← lintegral_indicator hs (fun x => c * f x), ← lintegral_indicator hs f]
  refine (lintegral_congr fun x => ?_).trans (lintegral_const_mul' c _ hc)
  by_cases hx : x ∈ s <;> simp [Set.indicator_of_mem, Set.indicator_of_notMem, hx]

/-- **The left boundary (clipped) part of the one-dimensional sliding-box mean-square bound.**

For `0 < h ≤ ℓ` and a.e.-measurable `F : ℝ → ℝ≥0∞`, with
`I(u) := Work.BoseFixB1S.slI ℓ h u = Icc (max (-ℓ/2) (h·u - h/2)) (min (ℓ/2) (h·u + h/2))`:

  `∫⁻_{u ∈ (-(ℓ+h)/(2h), -(ℓ-h)/(2h)]} ( (∫⁻_{x ∈ I(u)} F x) / |I(u)| )²  ≤  (4/h) ·
      ∫⁻_{x ∈ [-ℓ/2,ℓ/2]} F x² dx`.

On this region the window is clipped on the left: `I(u) = Icc (-ℓ/2) (h u + h/2)` and
`|I(u)| = ℓ/2 + h/2 + h·u =: s ∈ (0, h]`.  Writing `u(s) = (s - ℓ/2 - h/2)/h` (so `du = ds/h`) the
left-hand side becomes `(1/h)∫⁻_{s∈(0,h]} ((∫⁻_{t∈(0,s]} G t)/s)² ds` with `G t = F (-ℓ/2 + t)`, and
the elementary weighted Cauchy–Schwarz Hardy estimate
`(∫_0^s G)² ≤ (∫_0^s G²t^{1/2})(∫_0^s t^{-1/2}) = 2√s ∫_0^s G²√t` followed by Tonelli gives
`∫⁻_{s∈(0,h]}((∫⁻_{t∈(0,s]}G)/s)² ≤ 4 ∫⁻_{t∈(0,h]} (G t)² ≤ 4∫⁻_{[-ℓ/2,ℓ/2]}F²`
(any finite universal constant in place of `4` is equally useful: downstream only existence
matters).

Alternatively the whole statement can be obtained from the right-clipped companion (path
`BoseFixB1/Core/clipRight`, if already available) by the reflection `u ↦ -u`, `x ↦ -x`, which maps
this region onto the right-clipped one and satisfies `slI ℓ h (-u) = - slI ℓ h u`-style identities.

INTENDED PROOF. Rewrite the region integral as `∫⁻_{s ∈ (0,h]} Ψ((s - ℓ/2 - h/2)/h)·(1/h)` using the
affine change of variables (`Real.map_volume_mul_left` plus translation invariance of Lebesgue
measure, then `lintegral_map`; or prove the ENNReal substitution step separately), identify
`Ψ ((s - ℓ/2 - h/2)/h) = ((∫⁻_{t∈(0,s]} F (-ℓ/2 + t))/s)²` using
`slI ℓ h ((s - ℓ/2 - h/2)/h) = Icc (-ℓ/2) (-ℓ/2 + s)` and `volume (slI ...) = ofReal s`, and apply
the weighted Cauchy–Schwarz estimate in `ℝ≥0∞` above.  END OF HINT.

NOTE (proof actually carried out).  The route used is the `Toolkit`-based one described at the top
of this file: pointwise `cs_left` in the window, Tonelli over `(u,y)`, the per-`y` counting bound
`counting_left`, and the a.e. cancellation of the weight.  The statement is unchanged.

-/
theorem clipLeft {ℓ h : ℝ} (hh : 0 < h) (hhℓ : h ≤ ℓ) {F : ℝ → ℝ≥0∞}
    (hF : AEMeasurable F (volume : Measure ℝ)) :
    ∫⁻ u in Set.Ioc (-((ℓ + h) / (2 * h))) (-((ℓ - h) / (2 * h))),
        ((∫⁻ x in Work.BoseFixB1S.slI ℓ h u, F x) / (volume (Work.BoseFixB1S.slI ℓ h u))) ^ 2
      ≤ ENNReal.ofReal (4 / h) * ∫⁻ x in Set.Icc (-ℓ / 2) (ℓ / 2), (F x) ^ 2 := by
  classical
  obtain ⟨F', hF'm, hFF'⟩ : ∃ F' : ℝ → ℝ≥0∞, Measurable F' ∧ F =ᵐ[volume] F' :=
    ⟨hF.mk F, hF.measurable_mk, hF.ae_eq_mk⟩
  have hLHS : (∫⁻ u in Set.Ioc (-((ℓ + h) / (2 * h))) (-((ℓ - h) / (2 * h))),
        ((∫⁻ x in Work.BoseFixB1S.slI ℓ h u, F x) / (volume (Work.BoseFixB1S.slI ℓ h u))) ^ 2)
      = (∫⁻ u in Set.Ioc (-((ℓ + h) / (2 * h))) (-((ℓ - h) / (2 * h))),
        ((∫⁻ x in Work.BoseFixB1S.slI ℓ h u, F' x)
          / (volume (Work.BoseFixB1S.slI ℓ h u))) ^ 2) := by
    refine lintegral_congr fun u => ?_
    have h : (∫⁻ x in Work.BoseFixB1S.slI ℓ h u, F x)
        = ∫⁻ x in Work.BoseFixB1S.slI ℓ h u, F' x :=
      lintegral_congr_ae (ae_restrict_of_ae hFF')
    rw [h]
  have hRHS : (∫⁻ x in Set.Icc (-ℓ / 2) (ℓ / 2), (F x) ^ 2)
      = ∫⁻ x in Set.Icc (-ℓ / 2) (ℓ / 2), (F' x) ^ 2 := by
    refine lintegral_congr_ae ?_
    filter_upwards [ae_restrict_of_ae hFF'] with x hx
    rw [hx]
  rw [hLHS, hRHS]
  set A : ℝ := -((ℓ + h) / (2 * h)) with hA
  set B : ℝ := -((ℓ - h) / (2 * h)) with hB
  have hB' : B = (h - ℓ) / (2 * h) := by rw [hB]; ring
  have hIcc' : Set.Icc (-(ℓ / 2)) (ℓ / 2) = Set.Icc (-ℓ / 2) (ℓ / 2) := by
    rw [show -(ℓ / 2) = -ℓ / 2 by ring]
  -- the left-regime condition on the region
  have hlu : ∀ u ∈ Set.Ioc A B, h * u - h / 2 ≤ -(ℓ / 2) := by
    intro u hu
    have huB : u ≤ B := hu.2
    rw [hB] at huB
    have h2 : h * u ≤ h * (-((ℓ - h) / (2 * h))) := mul_le_mul_of_nonneg_left huB hh.le
    have h3 : h * (-((ℓ - h) / (2 * h))) = -((ℓ - h) / 2) := by field_simp
    rw [h3] at h2
    linarith
  -- strict positivity of the window length on the region
  have hpos : ∀ u ∈ Set.Ioc A B, 0 < h * u + h / 2 + ℓ / 2 := by
    intro u hu
    have h1 : h * A = -((ℓ + h) / 2) := by rw [hA]; field_simp
    have h2 : h * A < h * u := mul_lt_mul_of_pos_left hu.1 hh
    rw [h1] at h2
    linarith
  have hL1 : ∀ u ∈ Set.Ioc A B, L1 h ℓ u = h * u + h / 2 + ℓ / 2 := by
    intro u hu
    rw [L1_eq_left hhℓ (hlu u hu), max_eq_left (hpos u hu).le]
  have hvol : ∀ u ∈ Set.Ioc A B,
      volume (Work.BoseFixB1S.slI ℓ h u) = ENNReal.ofReal (L1 h ℓ u) := by
    intro u hu
    have hfin : volume (I1 h ℓ u) ≠ ⊤ := by
      refine ne_top_of_le_ne_top ?_ (measure_mono (I1_subset h ℓ u))
      rw [Real.volume_Icc]
      exact ENNReal.ofReal_ne_top
    rw [slI_eq_I1 ℓ h u]
    exact (ENNReal.ofReal_toReal hfin).symm
  -- the pointwise Cauchy–Schwarz bound
  have hpt : ∀ u ∈ Set.Ioc A B,
      ((∫⁻ x in Work.BoseFixB1S.slI ℓ h u, F' x) / (volume (Work.BoseFixB1S.slI ℓ h u))) ^ 2
        ≤ ∫⁻ y, (I1 h ℓ u).indicator
            (fun y => ENNReal.ofReal (2 * (L1 h ℓ u) ^ (-(3 / 2) : ℝ))
              * (F' y ^ 2 * wgtL ℓ y)) y := by
    intro u hu
    have hcs := cs_left hhℓ (hlu u hu) hF'm.aemeasurable
    have h1 : ((∫⁻ x in Work.BoseFixB1S.slI ℓ h u, F' x)
          / (volume (Work.BoseFixB1S.slI ℓ h u))) ^ 2
        = (ENNReal.ofReal (1 / L1 h ℓ u) * ∫⁻ y in I1 h ℓ u, F' y) ^ 2 := by
      rw [hvol u hu, slI_eq_I1 ℓ h u]
      congr 1
      rw [hL1 u hu, div_eq_mul_inv, ← ENNReal.ofReal_inv_of_pos (hpos u hu), inv_eq_one_div,
        mul_comm]
    have h2 : ENNReal.ofReal (2 * (L1 h ℓ u) ^ (-(3 / 2) : ℝ))
          * (∫⁻ y in I1 h ℓ u, F' y ^ 2 * wgtL ℓ y)
        = ∫⁻ y, (I1 h ℓ u).indicator
            (fun y => ENNReal.ofReal (2 * (L1 h ℓ u) ^ (-(3 / 2) : ℝ))
              * (F' y ^ 2 * wgtL ℓ y)) y := by
      rw [lintegral_indicator (measurableSet_I1 h ℓ u),
        lintegral_set_const_mul' (measurableSet_I1 h ℓ u) _ ENNReal.ofReal_ne_top]
    rw [h1, ← h2]
    exact hcs
  -- the double integral and its swap
  set Ψ : ℝ → ℝ → ℝ≥0∞ := fun u y => (I1 h ℓ u).indicator
      (fun y => ENNReal.ofReal (2 * (L1 h ℓ u) ^ (-(3 / 2) : ℝ)) * (F' y ^ 2 * wgtL ℓ y)) y
    with hΨ
  have hstep2 : ∫⁻ u in Set.Ioc A B,
        ((∫⁻ x in Work.BoseFixB1S.slI ℓ h u, F' x) / (volume (Work.BoseFixB1S.slI ℓ h u))) ^ 2
      ≤ ∫⁻ u in Set.Ioc A B, ∫⁻ y, Ψ u y := by
    refine lintegral_mono_ae ?_
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with u hu
    rw [hΨ]
    exact hpt u hu
  have huncurry : AEMeasurable (Function.uncurry Ψ)
      ((volume.restrict (Set.Ioc A B)).prod (volume : Measure ℝ)) := by
    have hset := measurableSet_prod_I1 ℓ h
    have hLm : Measurable (fun u : ℝ => L1 h ℓ u) := measurable_L1 ℓ h
    have hout : Measurable (fun x : ℝ => ENNReal.ofReal (2 * x ^ (-(3 / 2) : ℝ))) := by fun_prop
    have hc : Measurable (fun u : ℝ => ENNReal.ofReal (2 * (L1 h ℓ u) ^ (-(3 / 2) : ℝ))) :=
      hout.comp hLm
    have hF2 : Measurable (fun y : ℝ => F' y ^ 2) := hF'm.pow_const 2
    have hw : Measurable (fun y : ℝ => wgtL ℓ y) := measurable_wgtL ℓ
    have heq : Function.uncurry Ψ
        = fun p : ℝ × ℝ => ({p : ℝ × ℝ | p.2 ∈ I1 h ℓ p.1}).indicator (fun _ => (1 : ℝ≥0∞)) p
            * (ENNReal.ofReal (2 * (L1 h ℓ p.1) ^ (-(3 / 2) : ℝ))
                * (F' p.2 ^ 2 * wgtL ℓ p.2)) := by
      funext p
      simp only [hΨ, Function.uncurry]
      by_cases hp : p.2 ∈ I1 h ℓ p.1
      · rw [Set.indicator_of_mem hp,
          Set.indicator_of_mem (show p ∈ {q : ℝ × ℝ | q.2 ∈ I1 h ℓ q.1} from hp)]
        simp
      · rw [Set.indicator_of_notMem hp,
          Set.indicator_of_notMem (show p ∉ {q : ℝ × ℝ | q.2 ∈ I1 h ℓ q.1} from hp)]
        simp
    rw [heq]
    exact ((measurable_const.indicator hset).mul
      ((hc.comp measurable_fst).mul ((hF2.comp measurable_snd).mul (hw.comp measurable_snd)))).aemeasurable
  have hswap : ∫⁻ u in Set.Ioc A B, ∫⁻ y, Ψ u y
      = ∫⁻ y, ∫⁻ u in Set.Ioc A B, Ψ u y :=
    lintegral_lintegral_swap huncurry
  -- the per-`y` counting bound
  have hpoint_y : ∀ y, ∫⁻ u in Set.Ioc A B, Ψ u y ≤ F' y ^ 2 * ENNReal.ofReal (4 / h) := by
    intro y
    by_cases hy : y ∈ Set.Icc (-(ℓ / 2)) (ℓ / 2)
    · by_cases htop : F' y = ⊤
      · have htop' : F' y ^ 2 * ENNReal.ofReal (4 / h) = ⊤ := by
          rw [htop, show (⊤ : ℝ≥0∞) ^ 2 = ⊤ by simp]
          exact ENNReal.top_mul
            (ENNReal.ofReal_ne_zero_iff.mpr (by positivity : (0 : ℝ) < 4 / h))
        rw [htop']
        exact le_top
      · by_cases hy0 : y + ℓ / 2 = 0
        · have hw0 : wgtL ℓ y = 0 := by
            rw [wgtL, show y + ℓ / 2 = 0 from hy0, Real.sqrt_zero]
            simp
          have hcongr : ∀ u, Ψ u y = 0 := by
            intro u
            simp only [hΨ]
            rw [Set.indicator_apply]
            by_cases hmem : y ∈ I1 h ℓ u
            · simp [hmem, hw0]
            · simp [hmem]
          rw [lintegral_congr hcongr]
          simp
        · have hwpos : 0 < y + ℓ / 2 := by
            rcases lt_or_eq_of_le hy.1 with h' | h'
            · linarith
            · exact absurd (by linarith : y + ℓ / 2 = 0) hy0
          have hw0 : wgtL ℓ y ≠ 0 := by
            rw [wgtL, ENNReal.ofReal_ne_zero_iff]
            exact Real.sqrt_pos.mpr hwpos
          have hwtop : wgtL ℓ y ≠ ⊤ := by
            rw [wgtL]; exact ENNReal.ofReal_ne_top
          have hc : F' y ^ 2 * wgtL ℓ y ≠ ⊤ :=
            ENNReal.mul_ne_top (by rw [pow_two]; exact ENNReal.mul_ne_top htop htop) hwtop
          have hS : MeasurableSet (Set.Ioc A B ∩ {u : ℝ | y ∈ I1 h ℓ u}) :=
            measurableSet_Ioc.inter (measurableSet_I1_preimage ℓ h y)
          have hinner : ∫⁻ u in Set.Ioc A B, Ψ u y
              = (F' y ^ 2 * wgtL ℓ y)
                  * ∫⁻ u in Set.Ioc A B ∩ {u : ℝ | y ∈ I1 h ℓ u},
                      ENNReal.ofReal (2 * (L1 h ℓ u) ^ (-(3 / 2) : ℝ)) := by
            have hcongr : ∀ u ∈ Set.Ioc A B, Ψ u y
                = (Set.Ioc A B ∩ {u' : ℝ | y ∈ I1 h ℓ u'}).indicator
                    (fun u => (F' y ^ 2 * wgtL ℓ y)
                      * ENNReal.ofReal (2 * (L1 h ℓ u) ^ (-(3 / 2) : ℝ))) u := by
              intro u hu
              simp only [hΨ]
              by_cases hmem : y ∈ I1 h ℓ u
              · rw [Set.indicator_of_mem hmem,
                  Set.indicator_of_mem (show u ∈ Set.Ioc A B ∩ {u' : ℝ | y ∈ I1 h ℓ u'} from
                    ⟨hu, hmem⟩)]
                ring
              · rw [Set.indicator_of_notMem hmem,
                  Set.indicator_of_notMem (show u ∉ Set.Ioc A B ∩ {u' : ℝ | y ∈ I1 h ℓ u'} from
                    fun hc' => hmem hc'.2)]
            rw [setLIntegral_congr_fun measurableSet_Ioc hcongr,
              ← lintegral_indicator measurableSet_Ioc]
            rw [show (Set.Ioc A B).indicator ((Set.Ioc A B ∩ {u' : ℝ | y ∈ I1 h ℓ u'}).indicator
                  (fun u => (F' y ^ 2 * wgtL ℓ y)
                    * ENNReal.ofReal (2 * (L1 h ℓ u) ^ (-(3 / 2) : ℝ))))
                = (Set.Ioc A B ∩ {u' : ℝ | y ∈ I1 h ℓ u'}).indicator
                  (fun u => (F' y ^ 2 * wgtL ℓ y)
                    * ENNReal.ofReal (2 * (L1 h ℓ u) ^ (-(3 / 2) : ℝ))) from by
              funext u
              by_cases hu : u ∈ Set.Ioc A B <;>
                by_cases hv : u ∈ {u' : ℝ | y ∈ I1 h ℓ u'} <;>
                simp [Set.indicator_of_mem, Set.indicator_of_notMem, hu, hv]]
            rw [lintegral_indicator hS,
              lintegral_set_const_mul' hS (F' y ^ 2 * wgtL ℓ y) hc
                (fun u => ENNReal.ofReal (2 * (L1 h ℓ u) ^ (-(3 / 2) : ℝ)))]
          rw [hinner]
          have hmono : ∫⁻ u in Set.Ioc A B ∩ {u : ℝ | y ∈ I1 h ℓ u},
                ENNReal.ofReal (2 * (L1 h ℓ u) ^ (-(3 / 2) : ℝ))
              ≤ ∫⁻ t in Set.Icc ((y - h / 2) / h) ((h - ℓ) / (2 * h)),
                  ENNReal.ofReal (2 * (L1 h ℓ t) ^ (-(3 / 2) : ℝ)) := by
            refine lintegral_mono_set ?_
            intro u hu
            obtain ⟨hu1, hu2⟩ := hu
            rw [Set.mem_setOf_eq, mem_I1_iff'] at hu2
            rw [Set.mem_Icc]
            constructor
            · rw [div_le_iff₀ hh]
              linarith [hu2.2.2.2]
            · rw [hB'] at hu1
              exact hu1.2
          have hX : ∫⁻ t in Set.Icc ((y - h / 2) / h) ((h - ℓ) / (2 * h)),
                ENNReal.ofReal (2 * (L1 h ℓ t) ^ (-(3 / 2) : ℝ))
              ≤ (wgtL ℓ y)⁻¹ * ENNReal.ofReal (4 / h) := by
            have hcount := counting_left hh hhℓ hy
            calc ∫⁻ t in Set.Icc ((y - h / 2) / h) ((h - ℓ) / (2 * h)),
                  ENNReal.ofReal (2 * (L1 h ℓ t) ^ (-(3 / 2) : ℝ))
                = (wgtL ℓ y)⁻¹ * (wgtL ℓ y
                    * ∫⁻ t in Set.Icc ((y - h / 2) / h) ((h - ℓ) / (2 * h)),
                        ENNReal.ofReal (2 * (L1 h ℓ t) ^ (-(3 / 2) : ℝ))) := by
                  rw [← mul_assoc, ENNReal.inv_mul_cancel hw0 hwtop, one_mul]
              _ ≤ (wgtL ℓ y)⁻¹ * ENNReal.ofReal (4 / h) :=
                  mul_le_mul_of_nonneg_left hcount zero_le
          calc (F' y ^ 2 * wgtL ℓ y)
                * ∫⁻ u in Set.Ioc A B ∩ {u : ℝ | y ∈ I1 h ℓ u},
                    ENNReal.ofReal (2 * (L1 h ℓ u) ^ (-(3 / 2) : ℝ))
              ≤ (F' y ^ 2 * wgtL ℓ y) * ((wgtL ℓ y)⁻¹ * ENNReal.ofReal (4 / h)) :=
                mul_le_mul_of_nonneg_left (hmono.trans hX) zero_le
            _ = F' y ^ 2 * ENNReal.ofReal (4 / h) := by
                calc F' y ^ 2 * wgtL ℓ y * ((wgtL ℓ y)⁻¹ * ENNReal.ofReal (4 / h))
                    = F' y ^ 2 * ((wgtL ℓ y * (wgtL ℓ y)⁻¹) * ENNReal.ofReal (4 / h)) := by
                      ring
                  _ = F' y ^ 2 * ENNReal.ofReal (4 / h) := by
                      rw [ENNReal.mul_inv_cancel hw0 hwtop, one_mul]
    · have hcongr : ∀ u, Ψ u y = 0 := by
        intro u
        simp only [hΨ]
        exact Set.indicator_of_notMem (fun hmem => hy (I1_subset h ℓ u hmem)) _
      rw [lintegral_congr hcongr]
      simp
  have hzbox : ∫⁻ y, ∫⁻ u in Set.Ioc A B, Ψ u y
      = ∫⁻ y in Set.Icc (-(ℓ / 2)) (ℓ / 2), ∫⁻ u in Set.Ioc A B, Ψ u y := by
    have hzero : ∀ y ∉ Set.Icc (-(ℓ / 2)) (ℓ / 2), ∫⁻ u in Set.Ioc A B, Ψ u y = 0 := by
      intro y hy
      have hcongr : ∀ u, Ψ u y = 0 := by
        intro u
        simp only [hΨ]
        exact Set.indicator_of_notMem (fun hmem => hy (I1_subset h ℓ u hmem)) _
      rw [lintegral_congr hcongr]
      simp
    have hind : (Set.Icc (-(ℓ / 2)) (ℓ / 2)).indicator (fun y => ∫⁻ u in Set.Ioc A B, Ψ u y)
        = fun y => ∫⁻ u in Set.Ioc A B, Ψ u y := by
      funext y
      by_cases hy : y ∈ Set.Icc (-(ℓ / 2)) (ℓ / 2)
      · rw [Set.indicator_of_mem hy]
      · rw [Set.indicator_of_notMem hy, hzero y hy]
    rw [← lintegral_indicator measurableSet_Icc, hind]
  calc ∫⁻ u in Set.Ioc A B,
        ((∫⁻ x in Work.BoseFixB1S.slI ℓ h u, F' x) / (volume (Work.BoseFixB1S.slI ℓ h u))) ^ 2
      ≤ ∫⁻ u in Set.Ioc A B, ∫⁻ y, Ψ u y := hstep2
    _ = ∫⁻ y, ∫⁻ u in Set.Ioc A B, Ψ u y := hswap
    _ = ∫⁻ y in Set.Icc (-(ℓ / 2)) (ℓ / 2), ∫⁻ u in Set.Ioc A B, Ψ u y := hzbox
    _ ≤ ∫⁻ y in Set.Icc (-(ℓ / 2)) (ℓ / 2), F' y ^ 2 * ENNReal.ofReal (4 / h) :=
        lintegral_mono fun y => hpoint_y y
    _ = ENNReal.ofReal (4 / h) * ∫⁻ y in Set.Icc (-(ℓ / 2)) (ℓ / 2), F' y ^ 2 := by
        rw [setLIntegral_congr_fun measurableSet_Icc
          (fun y _ => mul_comm (F' y ^ 2) (ENNReal.ofReal (4 / h)))]
        rw [lintegral_set_const_mul' measurableSet_Icc (ENNReal.ofReal (4 / h))
          ENNReal.ofReal_ne_top (fun y => F' y ^ 2)]
    _ = ENNReal.ofReal (4 / h) * ∫⁻ y in Set.Icc (-ℓ / 2) (ℓ / 2), F' y ^ 2 := by rw [hIcc']

end Work.BoseFixB1.Core
