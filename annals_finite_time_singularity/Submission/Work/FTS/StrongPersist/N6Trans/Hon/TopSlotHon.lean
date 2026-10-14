import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.MeasureTheory.Integral.Prod
import Submission.Work.FTS.StrongPersist.N6Trans.Hon.TraceAe
import Submission.Work.FTS.TransportS.T2Sup.PairBnd
import Submission.Work.FTS.TransportS.T3SlotAux.Remainder
import Submission.Work.FTS.TransportS.ip4SlotDomFixed

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section
open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.StrongPersist.N6Trans.Hon

set_option autoImplicit false
set_option maxHeartbeats 4000000

/-! ## The honest top-slot bound

This is the honest (`SmoothOpen`, `HkMem α 4`, `HkMem α 5`) port of
`Work.FTS.TransportS.T2Sup.topSlotBound`.  The two differences from that theorem are

* the smoothness of the `g`-side datum is `SmoothOpen` on the open quadrant instead of
  `SmoothQuad` on the half-strip, and
* the *pointwise* radial boundary traces `z (D_z^bD_θ^a g · w)² → 0` are replaced by the
  a.e. traces `Hon.TraceAe g`, which the honest bundle *implies*
  (`Hon.traceAe_of_honG`).

The radial integration by parts itself is `Hon.slot_prod_le_open`, whose own boundary
hypothesis is the a.e. trace predicate. -/

/-- **The honest top-slot bound.**  For a slot `(4-a, a)` and the weight
`canonW q = w² sin(2θ)^{-q}` with `q ≤ γ` (and `q ≤ η` when `a = 0`), the pairing of the
order-five derivative with the order-four slot is bounded by `2 Mf HkSq α 4 g` whenever `Mf`
dominates `|f|` and `|D_z f|` on the open quadrant and `g` lies in the honest bundle
(`SmoothOpen`, `ℋ⁴`, `ℋ⁵`). -/
theorem topSlotBoundHon {α Mf : ℝ} {f g : ℝ → ℝ → ℝ} (a : ℕ) (ha : a ≤ 4) (q : ℝ)
    (hα : 0 < α) (hMf : 0 ≤ Mf)
    (hqη : a = 0 → q ≤ Work.Spaces.eta) (hqγ : q ≤ Work.Spaces.gam α)
    (hsmf : Work.FTS.EllipticEst.SmoothOpen f)
    (hsmg : Work.FTS.EllipticEst.SmoothOpen g)
    (hm4 : Work.Spaces.HkMem α 4 g) (hm5 : Work.Spaces.HkMem α 5 g)
    (hf : ∀ z θ, 0 < z → 0 < θ → θ < π / 2 → |f z θ| ≤ Mf)
    (hDf : ∀ z θ, 0 < z → 0 < θ → θ < π / 2 → |Work.Spaces.Dz f z θ| ≤ Mf) :
    |∫ z in Work.Spaces.Iz, ∫ θ in Work.Spaces.Iθ,
        Work.FTS.TransportS.SlotT2.canonW q z θ * f z θ
          * Work.Spaces.Dz (Work.Spaces.mixed (4 - a) a g) z θ
          * Work.Spaces.mixed (4 - a) a g z θ|
      ≤ 2 * Mf * Work.Spaces.HkSq α 4 g := by
  have ha5 : a < 5 := by omega
  -- the canonical hard exponent and the multiplier
  obtain ⟨qbig, hqbig0, hqbig, hqq⟩ : ∃ qbig : ℝ,
      (a = 0 → qbig = Work.Spaces.eta) ∧ (a ≠ 0 → qbig = Work.Spaces.gam α) ∧ q ≤ qbig := by
    rcases eq_or_ne a 0 with h0 | h0
    · subst h0
      exact ⟨Work.Spaces.eta, fun _ => rfl, fun h => absurd rfl h, hqη rfl⟩
    · exact ⟨Work.Spaces.gam α, fun h => absurd h h0, fun _ => rfl, hqγ⟩
  set d : ℝ := qbig - q with hd
  have hdnn : 0 ≤ d := by rw [hd]; linarith
  -- the amended multiplier: `σ^d f`, with the degenerate points set to `0`
  set fq : ℝ → ℝ → ℝ := fun z θ =>
    if z = 0 ∨ θ = 0 ∨ θ = Real.pi / 2 then 0 else Real.sin (2 * θ) ^ d * f z θ with hfqdef
  -- the open-quadrant bound for the unamended multiplier
  have hfq_open : ∀ z θ, 0 < z → 0 < θ → θ < π / 2 →
      |Real.sin (2 * θ) ^ d * f z θ| ≤ Mf := by
    intro z θ hz hθ hθ2
    have hσ0 : 0 < Real.sin (2 * θ) := Work.FTS.TransportS.T2Sup.sin_two_pos_of_Ioo ⟨hθ, hθ2⟩
    have hσ1 : Real.sin (2 * θ) ≤ 1 := Work.FTS.TransportS.T2Sup.sin_two_le_one θ
    have hpow : Real.sin (2 * θ) ^ d ≤ 1 := Real.rpow_le_one hσ0.le hσ1 hdnn
    calc |Real.sin (2 * θ) ^ d * f z θ|
        = Real.sin (2 * θ) ^ d * |f z θ| := by
          rw [abs_mul, abs_of_nonneg (Real.rpow_nonneg hσ0.le _)]
      _ ≤ 1 * Mf := mul_le_mul hpow (hf z θ hz hθ hθ2) (abs_nonneg _) (by norm_num)
      _ = Mf := one_mul Mf
  have hDfq_open : ∀ z θ, 0 < z → 0 < θ → θ < π / 2 →
      |Work.Spaces.Dz (fun z θ => Real.sin (2 * θ) ^ d * f z θ) z θ| ≤ Mf := by
    intro z θ hz hθ hθ2
    have hσ0 : 0 < Real.sin (2 * θ) := Work.FTS.TransportS.T2Sup.sin_two_pos_of_Ioo ⟨hθ, hθ2⟩
    have hσ1 : Real.sin (2 * θ) ≤ 1 := Work.FTS.TransportS.T2Sup.sin_two_le_one θ
    have hpow : Real.sin (2 * θ) ^ d ≤ 1 := Real.rpow_le_one hσ0.le hσ1 hdnn
    rw [Work.FTS.TransportS.T2Sup.Dz_mul_sin]
    calc |Real.sin (2 * θ) ^ d * Work.Spaces.Dz f z θ|
        = Real.sin (2 * θ) ^ d * |Work.Spaces.Dz f z θ| := by
          rw [abs_mul, abs_of_nonneg (Real.rpow_nonneg hσ0.le _)]
      _ ≤ 1 * Mf := mul_le_mul hpow (hDf z θ hz hθ hθ2) (abs_nonneg _) (by norm_num)
      _ = Mf := one_mul Mf
  -- the two closed-domain bounds for the amended multiplier
  have hfq : ∀ z ∈ Work.Spaces.Iz, ∀ θ ∈ Work.Spaces.Iθ, |fq z θ| ≤ Mf := by
    intro z hz θ hθ
    by_cases hbad : z = 0 ∨ θ = 0 ∨ θ = Real.pi / 2
    · simp only [hfqdef, if_pos hbad]
      simpa using hMf
    · simp only [hfqdef, if_neg hbad]
      simp only [not_or, not_not] at hbad
      obtain ⟨hz0, hθ0, hθ2⟩ := hbad
      have hzpos : 0 < z := lt_of_le_of_ne hz (Ne.symm hz0)
      have hθpos : 0 < θ := lt_of_le_of_ne hθ.1 (Ne.symm hθ0)
      have hθlt : θ < π / 2 := lt_of_le_of_ne hθ.2 hθ2
      exact hfq_open z θ hzpos hθpos hθlt
  have hDfq : ∀ z ∈ Work.Spaces.Iz, ∀ θ ∈ Work.Spaces.Iθ,
      |Work.Spaces.Dz fq z θ| ≤ Mf := by
    intro z hz θ hθ
    rcases eq_or_lt_of_le (show (0:ℝ) ≤ z from hz) with h0 | hzpos
    · subst h0
      rw [Work.Spaces.Dz, Work.Spaces.pz]
      simp only [zero_mul, abs_zero]
      exact hMf
    · by_cases hbad : θ = 0 ∨ θ = Real.pi / 2
      · have hzero : ∀ z' : ℝ, fq z' θ = 0 := by
          intro z'
          simp only [hfqdef, if_pos (Or.inr hbad)]
        have hev : (fun z' => fq z' θ) =ᶠ[𝓝 z] fun _ => (0:ℝ) :=
          Filter.Eventually.of_forall hzero
        rw [Work.Spaces.Dz, Work.Spaces.pz, hev.deriv_eq, deriv_const]
        simp only [mul_zero, abs_zero]
        exact hMf
      · have hθI : θ ∈ Set.Ioo (0:ℝ) (π/2) := by
          simp only [not_or, not_not] at hbad
          exact ⟨lt_of_le_of_ne hθ.1 (Ne.symm hbad.1), lt_of_le_of_ne hθ.2 hbad.2⟩
        have hσ0 : 0 < Real.sin (2 * θ) := Work.FTS.TransportS.T2Sup.sin_two_pos_of_Ioo hθI
        have hσ1 : Real.sin (2 * θ) ≤ 1 := Work.FTS.TransportS.T2Sup.sin_two_le_one θ
        have hpow : Real.sin (2 * θ) ^ d ≤ 1 := Real.rpow_le_one hσ0.le hσ1 hdnn
        have hev : (fun z' => fq z' θ) =ᶠ[𝓝 z]
            (fun z' => Real.sin (2 * θ) ^ d * f z' θ) := by
          filter_upwards [isOpen_Ioi.mem_nhds hzpos] with z' hz'
          have hnot : ¬ (z' = 0 ∨ θ = 0 ∨ θ = Real.pi / 2) := by
            rintro (h | h | h)
            · exact absurd h (ne_of_gt hz')
            · exact absurd h hθI.1.ne'
            · exact absurd h hθI.2.ne
          simp only [hfqdef, if_neg hnot]
        have hDzeq : Work.Spaces.Dz fq z θ
            = Real.sin (2 * θ) ^ d * Work.Spaces.Dz f z θ := by
          rw [Work.Spaces.Dz, Work.Spaces.Dz, Work.Spaces.pz, Work.Spaces.pz, hev.deriv_eq,
            deriv_const_mul_field]
          ring
        rw [hDzeq]
        calc |Real.sin (2 * θ) ^ d * Work.Spaces.Dz f z θ|
            = Real.sin (2 * θ) ^ d * |Work.Spaces.Dz f z θ| := by
              rw [abs_mul, abs_of_nonneg (Real.rpow_nonneg hσ0.le _)]
          _ ≤ 1 * Mf := mul_le_mul hpow (hDf z θ hzpos hθI.1 hθI.2) (abs_nonneg _)
              (by norm_num)
          _ = Mf := one_mul Mf
  have hsmfq : Work.FTS.EllipticEst.SmoothOpen fq := by
    refine (Work.FTS.TransportS.T2Sup.smoothOpen_mul_rpow_sin hsmf d).congr ?_
    intro p hp
    obtain ⟨hz, hθ0, hθ1⟩ := Work.FTS.EllipticEst.mem_Q0.mp hp
    have hnot : ¬ (p.1 = 0 ∨ p.2 = 0 ∨ p.2 = Real.pi / 2) := by
      rintro (h | h | h)
      · exact absurd h (ne_of_gt hz)
      · exact absurd h (ne_of_gt hθ0)
      · exact absurd h (ne_of_lt hθ1)
    dsimp only [Function.uncurry]
    simp only [hfqdef, if_neg hnot]
  -- the `Thard`-slot is the `(4-a,a)` mixed derivative
  have hTh : Work.FTS.H2.Thard g ⟨a, ha5⟩ = fun z θ => Work.Spaces.mixed (4 - a) a g z θ :=
    Work.FTS.H2.Thard_eq_mixed g ⟨a, ha5⟩
  have hsgh : ∀ θ, Work.FTS.H2.sghard α ⟨a, ha5⟩ θ = Real.sin (2 * θ) ^ (-qbig) := by
    intro θ
    rcases eq_or_ne a 0 with h0 | h0
    · subst h0
      have hk : (⟨0, ha5⟩ : Fin 5) = 0 := Fin.ext rfl
      rw [hk, Work.FTS.H2.sghard_apply_zero, hqbig0 rfl]
    · rw [Work.FTS.H2.sghard_apply_ne α _ (by simpa using h0), hqbig h0]
  -- the pointwise identity with `gK`
  have hkey : ∀ᵐ p ∂((MeasureTheory.volume.restrict Work.Spaces.Iz).prod
      (MeasureTheory.volume.restrict Work.Spaces.Iθ)),
      (fun p : ℝ × ℝ => Work.FTS.TransportS.SlotT2.canonW q p.1 p.2 * f p.1 p.2
        * Work.Spaces.Dz (Work.Spaces.mixed (4 - a) a g) p.1 p.2
        * Work.Spaces.mixed (4 - a) a g p.1 p.2) p
      = Work.FTS.TransportS.gK α fq g ⟨a, ha5⟩ p.1 p.2 := by
    refine Work.FTS.TransportS.ae_of_forall_Qd (fun z θ hz hθ hθ2 => ?_)
    show Work.FTS.TransportS.SlotT2.canonW q z θ * f z θ
        * Work.Spaces.Dz (Work.Spaces.mixed (4 - a) a g) z θ
        * Work.Spaces.mixed (4 - a) a g z θ
      = Work.FTS.TransportS.gK α fq g ⟨a, ha5⟩ z θ
    have hσ0 : 0 < Real.sin (2 * θ) := Work.FTS.TransportS.T2Sup.sin_two_pos_of_Ioo ⟨hθ, hθ2⟩
    have hfq_eq : fq z θ = Real.sin (2 * θ) ^ d * f z θ := by
      have hnot : ¬ (z = 0 ∨ θ = 0 ∨ θ = Real.pi / 2) := by
        rintro (h | h | h)
        · exact absurd h (ne_of_gt hz)
        · exact absurd h (ne_of_gt hθ)
        · exact absurd h (ne_of_lt hθ2)
      simp only [hfqdef, if_neg hnot]
    have hpow : Real.sin (2 * θ) ^ d * Real.sin (2 * θ) ^ (-qbig)
        = Real.sin (2 * θ) ^ (-q) := by
      rw [← Real.rpow_add hσ0, show d + (-qbig) = -q by rw [hd]; ring]
    have hmain : Work.FTS.TransportS.SlotT2.canonW q z θ * f z θ
        * Work.Spaces.Dz (Work.Spaces.mixed (4 - a) a g) z θ
        * Work.Spaces.mixed (4 - a) a g z θ
        = (Real.sin (2 * θ) ^ d * Real.sin (2 * θ) ^ (-qbig) * f z θ)
          * (Work.Spaces.w z ^ 2
            * (Work.Spaces.Dz (Work.Spaces.mixed (4 - a) a g) z θ
              * Work.Spaces.mixed (4 - a) a g z θ)) := by
      rw [Work.FTS.TransportS.SlotT2.canonW, hpow]; ring
    rw [hmain, Work.FTS.TransportS.gK, hfq_eq, hsgh, hTh, Work.Spaces.Dz, Work.Spaces.pz]
    ring
  -- Fubini and the integration by parts
  have hint : MeasureTheory.Integrable
      (fun p : ℝ × ℝ => Work.FTS.TransportS.gK α fq g ⟨a, ha5⟩ p.1 p.2)
      ((MeasureTheory.volume.restrict Work.Spaces.Iz).prod
        (MeasureTheory.volume.restrict Work.Spaces.Iθ)) :=
    integrable_gK_open hsmfq hsmg hm5 hMf
      (fun z θ hz hθ hθ2 => hfq z (le_of_lt hz) θ ⟨le_of_lt hθ, le_of_lt hθ2⟩)
      ⟨a, ha5⟩
  have hint' : MeasureTheory.Integrable
      (Function.uncurry (fun z θ => Work.FTS.TransportS.gK α fq g ⟨a, ha5⟩ z θ))
      ((MeasureTheory.volume.restrict Work.Spaces.Iz).prod
        (MeasureTheory.volume.restrict Work.Spaces.Iθ)) := hint
  -- the a.e. boundary traces, from the honest bundle
  have htrTh : ∀ᵐ θ ∂(MeasureTheory.volume.restrict Work.Spaces.Iθ),
      Filter.Tendsto (fun z => z * (Work.FTS.H2.Thard g ⟨a, ha5⟩ z θ * Work.Spaces.w z) ^ 2)
        (nhdsWithin (0 : ℝ) (Set.Ioi 0)) (nhds 0) ∧
      Filter.Tendsto (fun z => z * (Work.FTS.H2.Thard g ⟨a, ha5⟩ z θ * Work.Spaces.w z) ^ 2)
        Filter.atTop (nhds 0) :=
    (traceAe_of_honG hα hsmg hm4 hm5).mono (fun θ hθ => hθ ⟨a, ha5⟩)
  have hibp := slot_prod_le_open (α := α) (Mf := Mf)
    ⟨a, ha5⟩ hMf hsmfq hsmg hm4 hm5 hfq hDfq htrTh
  -- the `Xz`-energy
  have hXz : (∫ p, (Work.FTS.TransportS.Xz α g ⟨a, ha5⟩ p.1 p.2) ^ 2
      ∂((MeasureTheory.volume.restrict Work.Spaces.Iz).prod
        (MeasureTheory.volume.restrict Work.Spaces.Iθ))) ≤ Work.Spaces.HkSq α 4 g := by
    have hInt := integrable_HkIntegrand_prod_open hsmg hm4
    calc (∫ p, (Work.FTS.TransportS.Xz α g ⟨a, ha5⟩ p.1 p.2) ^ 2
          ∂((MeasureTheory.volume.restrict Work.Spaces.Iz).prod
            (MeasureTheory.volume.restrict Work.Spaces.Iθ)))
        ≤ ∫ p, Work.Spaces.HkIntegrand α 4 g p.1 p.2
          ∂((MeasureTheory.volume.restrict Work.Spaces.Iz).prod
            (MeasureTheory.volume.restrict Work.Spaces.Iθ)) :=
          MeasureTheory.integral_mono
            (integrable_Xz_sq_open hsmg hm4 ⟨a, ha5⟩) hInt.1
            (fun p => Work.FTS.TransportS.Xz_sq_le_HkIntegrand4 α g ⟨a, ha5⟩ p.1 p.2)
      _ = Work.Spaces.HkSq α 4 g := hInt.2
  -- conclude
  have hIntLHS : MeasureTheory.Integrable
      (Function.uncurry (fun z θ => Work.FTS.TransportS.SlotT2.canonW q z θ * f z θ
        * Work.Spaces.Dz (Work.Spaces.mixed (4 - a) a g) z θ
        * Work.Spaces.mixed (4 - a) a g z θ))
      ((MeasureTheory.volume.restrict Work.Spaces.Iz).prod
        (MeasureTheory.volume.restrict Work.Spaces.Iθ)) :=
    hint'.congr (hkey.mono (fun p hp => hp.symm))
  have hEq : (∫ z in Work.Spaces.Iz, ∫ θ in Work.Spaces.Iθ,
        Work.FTS.TransportS.SlotT2.canonW q z θ * f z θ
        * Work.Spaces.Dz (Work.Spaces.mixed (4 - a) a g) z θ
        * Work.Spaces.mixed (4 - a) a g z θ)
      = ∫ p, Work.FTS.TransportS.gK α fq g ⟨a, ha5⟩ p.1 p.2
          ∂((MeasureTheory.volume.restrict Work.Spaces.Iz).prod
            (MeasureTheory.volume.restrict Work.Spaces.Iθ)) := by
    rw [MeasureTheory.integral_integral hIntLHS]
    exact MeasureTheory.integral_congr_ae hkey
  rw [hEq]
  calc |∫ p, Work.FTS.TransportS.gK α fq g ⟨a, ha5⟩ p.1 p.2
        ∂((MeasureTheory.volume.restrict Work.Spaces.Iz).prod
          (MeasureTheory.volume.restrict Work.Spaces.Iθ))|
      ≤ 2 * Mf * ∫ p, (Work.FTS.TransportS.Xz α g ⟨a, ha5⟩ p.1 p.2) ^ 2
        ∂((MeasureTheory.volume.restrict Work.Spaces.Iz).prod
          (MeasureTheory.volume.restrict Work.Spaces.Iθ)) := hibp
    _ ≤ 2 * Mf * Work.Spaces.HkSq α 4 g :=
        mul_le_mul_of_nonneg_left hXz (by linarith)

/-- **The honest top-slot clause.**  The five top slots (`a + b = 4`) of the `D_z`-part of
the transport pairing obey the frozen bound `2 Mf |g|²_{ℋ⁴}` under the honest bundle
`SmoothOpen g ∧ HkMem α 4 g ∧ HkMem α 5 g ∧ DecayAll 4 g`, i.e. with the boundary-trace
hypothesis `BdryTraces` replaced by the two weighted `L²`-integrability conditions. -/
theorem TopSlotHon : Work.FTS.StrongPersist.N6Trans.Hon.TopSlotHonProp := by
  refine ⟨2, by norm_num, ?_⟩
  intro α f g a b q Mf hα hα1 hMf hab hqη hqγ hsmf hsmg hdec hm4 hm5 hf hDf
  have ha : a ≤ 4 := by omega
  have hb : 4 - a = b := by omega
  have h := topSlotBoundHon (α := α) (Mf := Mf) (f := f) (g := g) a ha q hα hMf hqη hqγ
    hsmf hsmg hm4 hm5 hf hDf
  simpa only [hb] using h

end Work.FTS.StrongPersist.N6Trans.Hon
