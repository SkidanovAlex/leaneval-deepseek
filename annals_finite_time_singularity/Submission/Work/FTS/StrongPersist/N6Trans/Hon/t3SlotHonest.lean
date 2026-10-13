import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.MeasureTheory.Integral.Prod
import Submission.Work.FTS.StrongPersist.N6Trans.Hon.TraceDefs
import Submission.Work.FTS.StrongPersist.N6Trans.Hon.OpenTwins
import Submission.Work.FTS.StrongPersist.N6Trans.Hon.FluxOpen
import Submission.Work.FTS.TransportS.Slots
import Submission.Work.FTS.TransportS.t3SlotGuarded
import Submission.Work.FTS.TransportS.T3SlotAux.Flux
import Submission.Work.FTS.TransportS.T3BadAux.slot_prod_le
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
set_option maxHeartbeats 2000000

/-- From the a.e. trace predicate `TraceAe g`, the a.e. traces of a *single* slot `k`: this is
the form in which the per-slot estimate consumes the boundary conditions. -/
theorem traceAe_single {g : ℝ → ℝ → ℝ} (h : TraceAe g) (k : Fin 5) :
    ∀ᵐ θ ∂(MeasureTheory.volume.restrict Work.Spaces.Iθ),
      Filter.Tendsto (fun z => z * (Work.FTS.H2.Thard g k z θ * Work.Spaces.w z) ^ 2)
        (nhdsWithin (0 : ℝ) (Set.Ioi 0)) (nhds 0) ∧
      Filter.Tendsto (fun z => z * (Work.FTS.H2.Thard g k z θ * Work.Spaces.w z) ^ 2)
        Filter.atTop (nhds 0) :=
  h.mono fun _ hθ => hθ k

/-
# The honest per-slot `D_z`-transport bound

This is the *honest* (open-quadrant) form of the per-slot transport bound
`Work.FTS.TransportS.T3Slot C` (proved for a positive `C` as
`Work.FTS.TransportS.t3SlotGuarded`).  It differs from `T3Slot` only in the `g`-side
hypothesis bundle: instead of the frozen

  `T3SG α g = RegQ α 4 g ∧ HkMem α 5 g ∧ DecayAll 4 g`
            `= (SmoothQuad g ∧ HkMem α 4 g ∧ BdryTraces α 4 g) ∧ HkMem α 5 g ∧ DecayAll 4 g`

it asks the honest

  `SmoothOpen g ∧ HkMem α 4 g ∧ HkMem α 5 g ∧ DecayAll 4 g ∧ TraceAe g`,

where `TraceAe g` (`Submission/Work/FTS/StrongPersist/N6Trans/Hon/TraceDefs.lean`) is the
*almost-everywhere* form of the radial part of `BdryTraces α 4 g`:
`∀ᵐ θ ∂(volume.restrict Iθ), ∀ k : Fin 5, z (Thard g k z θ w z)² → 0` at `0⁺` and at `+∞`.

## Why it is provable

The proof of `t3SlotGuarded` uses `SmoothQuad g` only to obtain facts on the *open* quadrant
(`SmoothOpen g` suffices), and uses `BdryTraces α 4 g` only through exactly the hypothesis
`TraceAe` above (the `htr` argument of `slot_prod_le`).  The whole agent chain
(`TransportS.slotPairing`, `TransportS.SlotT2.canonW`, `TransportS.T3SlotAux.*`,
`TransportS.T3BadAux.slot_prod_le`) is reusable; only the `SmoothQuad`-typed lemmas need
open (`SmoothOpen`) twins: `integrable_HkIntegrand_prod`, `integrable_Xz_sq`,
`integrable_gK`, `continuousOn_Xz_Qd`, `continuousOn_Yz_Qd`, `continuousOn_gK_Qd`,
`continuousOn_gK'_Qd`, `continuousOn_mixed_Qd`, and `slot_slice_le_ae` / `slot_prod_le`
with the a.e. trace hypothesis `∀ᵐ θ, …,` in place of `∀ θ ∈ Ioo 0 (π/2), …`
(in `slot_slice_le_ae` the a.e. hypothesis is simply added to the `filter_upwards` list
that already contains `ae_mem_Ioo_Iθ`, `h4`, `h5`, `hX2`).

## Consumers

`Work.FTS.StrongPersist.N6Trans.IP4T3Honest` (the node this serves) combines this per-slot
bound with `Work.FTS.TransportS.ip4SlotDomFixed` (the slot domination of the concrete
`IP4`) exactly as `Work.FTS.TransportS.T3Clause_of_slot` does, to get the honest `t3`
clause for `Work.FTS.CoercivityFix.Assembly.IP4 1 1 1 1 1 1`.
-/
theorem t3SlotHonest : ∃ C : ℝ, 0 < C ∧
    ∀ (α : ℝ) (f g : ℝ → ℝ → ℝ), 0 < α → α ≤ 1 →
      Work.FTS.TransportS.T3SF α f →
      Work.FTS.EllipticEst.SmoothOpen g → Work.Spaces.HkMem α 4 g →
        Work.Spaces.HkMem α 5 g → Work.Spaces.DecayAll 4 g →
      Work.FTS.StrongPersist.N6Trans.Hon.TraceAe g →
      ∀ (a b : ℕ) (ρ : ℝ → ℝ → ℝ), a + b ≤ 4 → Work.FTS.TransportS.IsLeafW α a ρ →
        |Work.FTS.TransportS.slotPairing ρ a b (fun z θ => f z θ * Work.Spaces.Dz g z θ) g|
          ≤ C * α ^ (-(1 / 2 : ℝ))
              * (Work.Spaces.WlInf α 4 f + Work.FTS.VocabO.CoefTh 3 f)
              * (Work.Spaces.HkNorm α 4 g) ^ 2 := by
  obtain ⟨C_f, hC_f_pos, hC_f⟩ := Work.FTS.H2.OpenPort.coefTh3_mixed_gain
  refine ⟨6402 * (101 + C_f), by positivity, ?_⟩
  intro α f g hα hα1 hF hsg hm4 hm5 hdec htrAe a b ρ hab hleaf
  obtain ⟨hsf, hwf, hcf⟩ := hF
  -- ## the constant `Mf = 100|f|_{𝒲^{4,∞}} + C_f CoefTh 3 f`
  set Mf : ℝ := 100 * Work.Spaces.WlInf α 4 f + C_f * Work.FTS.VocabO.CoefTh 3 f with hMfdef
  have hWnn : 0 ≤ Work.Spaces.WlInf α 4 f := Work.Spaces.WlInf_nonneg α 4 f hwf
  have hCnn : 0 ≤ Work.FTS.VocabO.CoefTh 3 f := Work.FTS.TransportS.coefTh_nonneg 3 f
  have hMf : 0 ≤ Mf := by rw [hMfdef]; positivity
  have hMfC : C_f * Work.FTS.VocabO.CoefTh 3 f ≤ Mf := by rw [hMfdef]; linarith
  have hMfW : 100 * Work.Spaces.WlInf α 4 f ≤ Mf := by
    rw [hMfdef]; linarith [mul_nonneg hC_f_pos.le hCnn]
  have hMfW' : Work.Spaces.WlInf α 4 f ≤ Mf := by linarith [hMfW, hWnn]
  -- ## the pointwise bounds on the coefficient `f`
  have hDzb : ∀ b1 : ℕ, 1 ≤ b1 → b1 ≤ 4 → ∀ z θ : ℝ, 0 < z → 0 < θ → θ < Real.pi / 2 →
      |Work.Spaces.DzIter b1 f z θ| ≤ Mf := by
    intro b1 _ hb4 z θ hz hθ0 hθ1
    exact (Work.FTS.TransportS.T3SlotAux.dzIter_le_WlInf_open hsf hwf hb4 hz
      ⟨hθ0, hθ1⟩).trans hMfW
  have hFmix : ∀ a1 b1 : ℕ, 1 ≤ a1 → a1 + b1 ≤ 4 → ∀ z θ : ℝ, 0 < z → 0 < θ →
      θ < Real.pi / 2 →
      |Work.Spaces.mixed b1 a1 f z θ| ≤ C_f * Real.sin (2 * θ) * Work.FTS.VocabO.CoefTh 3 f :=
    fun a1 b1 ha1 hab' z θ hz hθ0 hθ1 => hC_f f hsf hcf a1 b1 ha1 hab' z θ hz hθ0 hθ1
  have hfbound : ∀ z ∈ Work.Spaces.Iz, ∀ θ ∈ Work.Spaces.Iθ, |f z θ| ≤ Mf := by
    intro z hz θ hθ
    have h := Work.Spaces.zpz_le_WlInf (α := α) hwf (j := 0) (by norm_num) hz hθ
    simpa using h.trans hMfW'
  have hDzbound : ∀ z ∈ Work.Spaces.Iz, ∀ θ ∈ Work.Spaces.Iθ, |Work.Spaces.Dz f z θ| ≤ Mf := by
    intro z hz θ hθ
    have h := Work.Spaces.zpz_le_WlInf (α := α) hwf (j := 1) (by norm_num) hz hθ
    simpa [Work.Spaces.Dz] using h.trans hMfW'
  -- ## the leaf weight data: the exponent `q`, its domination, and continuity
  have hdata : ∃ q : ℝ, 0 ≤ q ∧ q ≤ Work.FTS.TransportS.T3SlotAux.qOf α a ∧
      (∀ z θ : ℝ, 0 < z → 0 < θ → θ < Real.pi / 2 →
        ρ z θ = Work.FTS.TransportS.SlotT2.canonW q z θ) ∧
      ContinuousOn (fun p : ℝ × ℝ => ρ p.1 p.2) Work.FTS.LocData.Qd := by
    rcases hleaf with h | h | ⟨ha1, h⟩
    · subst h
      refine ⟨Work.Spaces.eta, le_of_lt Work.Spaces.eta_pos, ?_, ?_, ?_⟩
      · rcases eq_or_ne a 0 with ha0 | ha
        · rw [ha0, Work.FTS.TransportS.T3SlotAux.qOf_zero]
        · rw [Work.FTS.TransportS.T3SlotAux.qOf_of_ne ha, Work.Spaces.gam, Work.Spaces.eta]
          linarith
      · intro z θ _ _ _
        rfl
      · refine (Work.FTS.TransportS.continuousOn_w_sq_Qd.mul
          (Work.FTS.TransportS.continuousOn_sinpow_Qd (-(Work.Spaces.eta)))).congr ?_
        intro p _
        simp only [Pi.mul_apply, Work.FTS.TransportS.leafEta]
    · subst h
      refine ⟨0, le_refl 0, le_of_lt (Work.FTS.TransportS.T3SlotAux.qOf_pos α hα a), ?_, ?_⟩
      · intro z θ _ _ _
        rw [Work.FTS.TransportS.SlotT2.canonW, neg_zero, Real.rpow_zero, mul_one]
        rfl
      · simpa [Work.FTS.TransportS.leafOne] using Work.FTS.TransportS.continuousOn_w_sq_Qd
    · subst h
      refine ⟨Work.Spaces.gam α, le_of_lt (Work.Spaces.gam_pos hα), ?_, ?_, ?_⟩
      · rw [Work.FTS.TransportS.T3SlotAux.qOf_of_ne (by omega : a ≠ 0)]
      · intro z θ _ _ _
        rfl
      · refine (Work.FTS.TransportS.continuousOn_w_sq_Qd.mul
          (Work.FTS.TransportS.continuousOn_sinpow_Qd (-(Work.Spaces.gam α)))).congr ?_
        intro p _
        simp only [Pi.mul_apply, Work.FTS.TransportS.leafGam]
  obtain ⟨q, hq0, hqle, hρeq, hρcont⟩ := hdata
  have hρle : ∀ z θ : ℝ, 0 < z → 0 < θ → θ < Real.pi / 2 →
      ρ z θ ≤ Work.FTS.TransportS.SlotT2.canonW (Work.FTS.TransportS.T3SlotAux.qOf α a) z θ := by
    intro z θ hz hθ0 hθ1
    rw [hρeq z θ hz hθ0 hθ1]
    exact Work.FTS.TransportS.T3SlotAux.canonW_le_of_le hqle ⟨hθ0, hθ1⟩
  have hρnonneg : ∀ z θ : ℝ, θ ∈ Work.Spaces.Iθ → 0 ≤ ρ z θ :=
    fun z θ hθ => Work.FTS.TransportS.T3SlotAux.IsLeafW.nonneg hleaf z hθ
  -- ## the boundary traces of each top slot
  have htr : ∀ k : Fin 5, ∀ᵐ θ ∂(MeasureTheory.volume.restrict Work.Spaces.Iθ),
      Filter.Tendsto (fun z => z * (Work.FTS.H2.Thard g k z θ * Work.Spaces.w z) ^ 2)
        (nhdsWithin (0 : ℝ) (Set.Ioi 0)) (nhds 0) ∧
      Filter.Tendsto (fun z => z * (Work.FTS.H2.Thard g k z θ * Work.Spaces.w z) ^ 2)
        Filter.atTop (nhds 0) :=
    fun k => traceAe_single htrAe k
  -- ## the abbreviation `X = f · D_z g`
  set X : ℝ → ℝ → ℝ := fun z θ => f z θ * Work.Spaces.Dz g z θ with hX
  -- ## the pointwise bound on the exceptional-free remainder
  have hrempt : ∀ z θ : ℝ, 0 < z → 0 < θ → θ < Real.pi / 2 →
      |ρ z θ * (Work.Spaces.mixed b a X z θ
          - f z θ * Work.Spaces.Dz (Work.Spaces.mixed b a g) z θ)
        * Work.Spaces.mixed b a g z θ|
        ≤ 6400 * Mf * Work.Spaces.HkIntegrand α 4 g z θ := by
    intro z θ hz hθ0 hθ1
    rw [hX]
    exact Work.FTS.TransportS.T3SlotAux.remainder_pointwise (α := α) (Mf := Mf) (C_f := C_f)
      (f := f) (g := g) (a := a) (b := b) (ρ := ρ) hα hα1 hMf hsf hsg hleaf hab hDzb hFmix
      hMfC z θ hz hθ0 hθ1
  -- ## the exceptional term: integrability and bound
  have hflux : Integrable (fun p : ℝ × ℝ => ρ p.1 p.2 * f p.1 p.2
        * Work.Spaces.Dz (Work.Spaces.mixed b a g) p.1 p.2 * Work.Spaces.mixed b a g p.1 p.2)
        ((volume.restrict Work.Spaces.Iz).prod (volume.restrict Work.Spaces.Iθ)) ∧
      |∫ p, ρ p.1 p.2 * f p.1 p.2 * Work.Spaces.Dz (Work.Spaces.mixed b a g) p.1 p.2
          * Work.Spaces.mixed b a g p.1 p.2
          ∂((volume.restrict Work.Spaces.Iz).prod (volume.restrict Work.Spaces.Iθ))|
        ≤ 2 * Mf * Work.Spaces.HkSq α 4 g := by
    by_cases h4 : a + b = 4
    · -- the exceptional (order-five) slot: radial integration by parts
      let k : Fin 5 := ⟨a, by omega⟩
      have hk : k.val = a := rfl
      refine ⟨?_, ?_⟩
      · refine flux_integrable_open (α := α) (Mf := Mf) (q := q)
          (r := Work.FTS.TransportS.T3SlotAux.qOf α a - q) (f := f) (g := g) (a := a) (b := b)
          (ρ := ρ) (k := k) hMf hsf hsg hm5 hk h4 rfl hqle hρeq ?_
        intro z θ hz hθ0 hθ1
        exact (hfbound z (le_of_lt hz) θ ⟨le_of_lt hθ0, le_of_lt hθ1⟩)
      · exact flux_bound_open (α := α) (Mf := Mf) (q := q) (f := f)
          (g := g) (a := a) (b := b) (ρ := ρ) (k := k) hMf hsf hsg hm4 hm5 hk h4 hqle hρeq
          hfbound hDzbound (htr k)
    · -- the slot has order `≤ 3`: the exceptional term is an ordinary `ℋ⁴`-slot
      have hab3 : a + b ≤ 3 := by omega
      have hpt : ∀ z θ : ℝ, 0 < z → 0 < θ → θ < Real.pi / 2 →
          |ρ z θ * f z θ * Work.Spaces.Dz (Work.Spaces.mixed b a g) z θ
              * Work.Spaces.mixed b a g z θ| ≤ Mf * Work.Spaces.HkIntegrand α 4 g z θ := by
        intro z θ hz hθ0 hθ1
        have hθI : θ ∈ Work.Spaces.Iθ := ⟨le_of_lt hθ0, le_of_lt hθ1⟩
        have hρz : ρ z θ ≤ Work.FTS.TransportS.SlotT2.canonW (Work.FTS.TransportS.T3SlotAux.qOf α a) z θ :=
          hρle z θ hz hθ0 hθ1
        have hDz : Work.Spaces.Dz (Work.Spaces.mixed b a g) z θ
            = Work.Spaces.mixed (b + 1) a g z θ := rfl
        have hpair := Work.FTS.TransportS.T3SlotAux.canonW_pair_le (α := α) (g := g)
          (q := Work.FTS.TransportS.T3SlotAux.qOf α a)
          (Work.FTS.TransportS.T3SlotAux.qOf_pos α hα a)
          (Work.FTS.TransportS.T3SlotAux.qOf_le_gam α hα a)
          (j := b + 1) (i := a) (b := b) (a := a)
          (fun h => by rw [h, Work.FTS.TransportS.T3SlotAux.qOf_zero])
          (fun h => by rw [h, Work.FTS.TransportS.T3SlotAux.qOf_zero])
          (by omega) hab (le_of_lt hz) hθI
        have hXnn : 0 ≤ |Work.Spaces.mixed (b + 1) a g z θ| * |Work.Spaces.mixed b a g z θ| :=
          mul_nonneg (abs_nonneg _) (abs_nonneg _)
        have hρf : ρ z θ * |f z θ| ≤ Mf
            * Work.FTS.TransportS.SlotT2.canonW (Work.FTS.TransportS.T3SlotAux.qOf α a) z θ := by
          calc ρ z θ * |f z θ|
              ≤ Work.FTS.TransportS.SlotT2.canonW (Work.FTS.TransportS.T3SlotAux.qOf α a) z θ * Mf :=
                mul_le_mul hρz (hfbound z (le_of_lt hz) θ hθI) (abs_nonneg _)
                  (Work.FTS.TransportS.SlotT2.canonW_nonneg hθI)
            _ = Mf * Work.FTS.TransportS.SlotT2.canonW
                  (Work.FTS.TransportS.T3SlotAux.qOf α a) z θ := by ring
        rw [abs_mul, abs_mul, abs_mul, abs_of_nonneg (hρnonneg z θ hθI), hDz]
        calc (ρ z θ * |f z θ|) * |Work.Spaces.mixed (b + 1) a g z θ|
              * |Work.Spaces.mixed b a g z θ|
            = (ρ z θ * |f z θ|) * (|Work.Spaces.mixed (b + 1) a g z θ|
                * |Work.Spaces.mixed b a g z θ|) := by ring
          _ ≤ (Mf * Work.FTS.TransportS.SlotT2.canonW (Work.FTS.TransportS.T3SlotAux.qOf α a) z θ)
                * (|Work.Spaces.mixed (b + 1) a g z θ| * |Work.Spaces.mixed b a g z θ|) :=
              mul_le_mul_of_nonneg_right hρf hXnn
          _ = Mf * (Work.FTS.TransportS.SlotT2.canonW (Work.FTS.TransportS.T3SlotAux.qOf α a) z θ
                * (|Work.Spaces.mixed (b + 1) a g z θ| * |Work.Spaces.mixed b a g z θ|)) := by ring
          _ ≤ Mf * Work.Spaces.HkIntegrand α 4 g z θ := by
              refine mul_le_mul_of_nonneg_left ?_ hMf
              rw [← mul_assoc]
              exact hpair
      have haesm : AEStronglyMeasurable (fun p : ℝ × ℝ => ρ p.1 p.2 * f p.1 p.2
          * Work.Spaces.Dz (Work.Spaces.mixed b a g) p.1 p.2 * Work.Spaces.mixed b a g p.1 p.2)
          ((volume.restrict Work.Spaces.Iz).prod (volume.restrict Work.Spaces.Iθ)) := by
        refine Work.Spaces.aesm_of_continuousOn_Qd _ ?_
        refine ((hρcont.mul hsf.continuousOn).mul
          ((hsg.mixed b a).Dz.continuousOn)).mul ((hsg.mixed b a).continuousOn)
      have hint : Integrable (fun p : ℝ × ℝ => ρ p.1 p.2 * f p.1 p.2
          * Work.Spaces.Dz (Work.Spaces.mixed b a g) p.1 p.2 * Work.Spaces.mixed b a g p.1 p.2)
          ((volume.restrict Work.Spaces.Iz).prod (volume.restrict Work.Spaces.Iθ)) := by
        refine Integrable.mono'
          (((integrable_HkIntegrand_prod_open hsg hm4).1).const_mul Mf) haesm ?_
        filter_upwards [Work.FTS.TransportS.ae_of_forall_Qd (P := fun p : ℝ × ℝ =>
          |ρ p.1 p.2 * f p.1 p.2 * Work.Spaces.Dz (Work.Spaces.mixed b a g) p.1 p.2
              * Work.Spaces.mixed b a g p.1 p.2| ≤ Mf * Work.Spaces.HkIntegrand α 4 g p.1 p.2)
          (fun z θ hz hθ hθ' => hpt z θ hz hθ hθ')] with p hp
        simpa [Real.norm_eq_abs] using hp
      refine ⟨hint, ?_⟩
      calc |∫ p, ρ p.1 p.2 * f p.1 p.2 * Work.Spaces.Dz (Work.Spaces.mixed b a g) p.1 p.2
              * Work.Spaces.mixed b a g p.1 p.2
              ∂((volume.restrict Work.Spaces.Iz).prod (volume.restrict Work.Spaces.Iθ))|
          ≤ ∫ p, |ρ p.1 p.2 * f p.1 p.2 * Work.Spaces.Dz (Work.Spaces.mixed b a g) p.1 p.2
              * Work.Spaces.mixed b a g p.1 p.2|
              ∂((volume.restrict Work.Spaces.Iz).prod (volume.restrict Work.Spaces.Iθ)) :=
            abs_integral_le_integral_abs
        _ ≤ ∫ p, Mf * Work.Spaces.HkIntegrand α 4 g p.1 p.2
              ∂((volume.restrict Work.Spaces.Iz).prod (volume.restrict Work.Spaces.Iθ)) :=
            integral_mono_ae hint.abs
              (((integrable_HkIntegrand_prod_open hsg hm4).1).const_mul Mf)
              (Work.FTS.TransportS.ae_of_forall_Qd fun z θ hz hθ hθ' => hpt z θ hz hθ hθ')
        _ = Mf * Work.Spaces.HkSq α 4 g := by
            rw [MeasureTheory.integral_const_mul,
              (integrable_HkIntegrand_prod_open hsg hm4).2]
        _ ≤ 2 * Mf * Work.Spaces.HkSq α 4 g := by
            have := Work.Spaces.HkSq_nonneg α 4 g
            nlinarith [hMf]
  -- ## integrability of the remainder
  have hremaesm : AEStronglyMeasurable (fun p : ℝ × ℝ => ρ p.1 p.2
      * (Work.Spaces.mixed b a X p.1 p.2
        - f p.1 p.2 * Work.Spaces.Dz (Work.Spaces.mixed b a g) p.1 p.2)
      * Work.Spaces.mixed b a g p.1 p.2)
      ((volume.restrict Work.Spaces.Iz).prod (volume.restrict Work.Spaces.Iθ)) := by
    refine Work.Spaces.aesm_of_continuousOn_Qd _ ?_
    have hmul : Work.FTS.EllipticEst.SmoothOpen (fun z θ => f z θ * Work.Spaces.Dz g z θ) :=
      hsf.mul hsg.Dz
    rw [hX]
    refine (hρcont.mul ((hmul.mixed b a).continuousOn.sub
      (hsf.continuousOn.mul ((hsg.mixed b a).Dz.continuousOn)))).mul
      ((hsg.mixed b a).continuousOn)
  have hremint : Integrable (fun p : ℝ × ℝ => ρ p.1 p.2
      * (Work.Spaces.mixed b a X p.1 p.2
        - f p.1 p.2 * Work.Spaces.Dz (Work.Spaces.mixed b a g) p.1 p.2)
      * Work.Spaces.mixed b a g p.1 p.2)
      ((volume.restrict Work.Spaces.Iz).prod (volume.restrict Work.Spaces.Iθ)) := by
    refine Integrable.mono'
      (((integrable_HkIntegrand_prod_open hsg hm4).1).const_mul (6400 * Mf))
      hremaesm ?_
    filter_upwards [Work.FTS.TransportS.ae_of_forall_Qd (P := fun p : ℝ × ℝ =>
      |ρ p.1 p.2 * (Work.Spaces.mixed b a X p.1 p.2
          - f p.1 p.2 * Work.Spaces.Dz (Work.Spaces.mixed b a g) p.1 p.2)
        * Work.Spaces.mixed b a g p.1 p.2| ≤ 6400 * Mf * Work.Spaces.HkIntegrand α 4 g p.1 p.2)
      (fun z θ hz hθ hθ' => hrempt z θ hz hθ hθ')] with p hp
    simpa [Real.norm_eq_abs] using hp
  have hrembound : |∫ p, ρ p.1 p.2 * (Work.Spaces.mixed b a X p.1 p.2
        - f p.1 p.2 * Work.Spaces.Dz (Work.Spaces.mixed b a g) p.1 p.2)
        * Work.Spaces.mixed b a g p.1 p.2
        ∂((volume.restrict Work.Spaces.Iz).prod (volume.restrict Work.Spaces.Iθ))|
      ≤ 6400 * Mf * Work.Spaces.HkSq α 4 g := by
    calc |∫ p, ρ p.1 p.2 * (Work.Spaces.mixed b a X p.1 p.2
            - f p.1 p.2 * Work.Spaces.Dz (Work.Spaces.mixed b a g) p.1 p.2)
            * Work.Spaces.mixed b a g p.1 p.2
            ∂((volume.restrict Work.Spaces.Iz).prod (volume.restrict Work.Spaces.Iθ))|
        ≤ ∫ p, |ρ p.1 p.2 * (Work.Spaces.mixed b a X p.1 p.2
              - f p.1 p.2 * Work.Spaces.Dz (Work.Spaces.mixed b a g) p.1 p.2)
            * Work.Spaces.mixed b a g p.1 p.2|
            ∂((volume.restrict Work.Spaces.Iz).prod (volume.restrict Work.Spaces.Iθ)) :=
          abs_integral_le_integral_abs
      _ ≤ ∫ p, 6400 * Mf * Work.Spaces.HkIntegrand α 4 g p.1 p.2
            ∂((volume.restrict Work.Spaces.Iz).prod (volume.restrict Work.Spaces.Iθ)) :=
          integral_mono_ae hremint.abs
            (((integrable_HkIntegrand_prod_open hsg hm4).1).const_mul (6400 * Mf))
            (Work.FTS.TransportS.ae_of_forall_Qd fun z θ hz hθ hθ' => hrempt z θ hz hθ hθ')
      _ = 6400 * Mf * Work.Spaces.HkSq α 4 g := by
          rw [MeasureTheory.integral_const_mul,
            (integrable_HkIntegrand_prod_open hsg hm4).2]
  -- ## the product-measure form of the pairing
  have hsplit_ae : (fun p : ℝ × ℝ => ρ p.1 p.2 * Work.Spaces.mixed b a X p.1 p.2
        * Work.Spaces.mixed b a g p.1 p.2)
      =ᵐ[(volume.restrict Work.Spaces.Iz).prod (volume.restrict Work.Spaces.Iθ)]
        ((fun p : ℝ × ℝ => ρ p.1 p.2 * f p.1 p.2
            * Work.Spaces.Dz (Work.Spaces.mixed b a g) p.1 p.2
            * Work.Spaces.mixed b a g p.1 p.2)
          + fun p : ℝ × ℝ => ρ p.1 p.2 * (Work.Spaces.mixed b a X p.1 p.2
            - f p.1 p.2 * Work.Spaces.Dz (Work.Spaces.mixed b a g) p.1 p.2)
            * Work.Spaces.mixed b a g p.1 p.2) :=
    Filter.Eventually.of_forall fun p => by
      simp only [Pi.add_apply]
      ring
  have hXYint : Integrable (Function.uncurry (fun z θ : ℝ => ρ z θ
        * Work.Spaces.mixed b a X z θ * Work.Spaces.mixed b a g z θ))
      ((volume.restrict Work.Spaces.Iz).prod (volume.restrict Work.Spaces.Iθ)) :=
    (hflux.1.add hremint).congr hsplit_ae.symm
  have hident : Work.FTS.TransportS.slotPairing ρ a b X g
      = ∫ p, ρ p.1 p.2 * Work.Spaces.mixed b a X p.1 p.2 * Work.Spaces.mixed b a g p.1 p.2
          ∂((volume.restrict Work.Spaces.Iz).prod (volume.restrict Work.Spaces.Iθ)) := by
    rw [Work.FTS.TransportS.slotPairing]
    exact MeasureTheory.integral_integral
      (f := fun z θ : ℝ => ρ z θ * Work.Spaces.mixed b a X z θ
        * Work.Spaces.mixed b a g z θ) hXYint
  have hsplit : (∫ p, ρ p.1 p.2 * Work.Spaces.mixed b a X p.1 p.2
        * Work.Spaces.mixed b a g p.1 p.2
        ∂((volume.restrict Work.Spaces.Iz).prod (volume.restrict Work.Spaces.Iθ)))
      = (∫ p, ρ p.1 p.2 * f p.1 p.2 * Work.Spaces.Dz (Work.Spaces.mixed b a g) p.1 p.2
            * Work.Spaces.mixed b a g p.1 p.2
            ∂((volume.restrict Work.Spaces.Iz).prod (volume.restrict Work.Spaces.Iθ)))
        + (∫ p, ρ p.1 p.2 * (Work.Spaces.mixed b a X p.1 p.2
              - f p.1 p.2 * Work.Spaces.Dz (Work.Spaces.mixed b a g) p.1 p.2)
            * Work.Spaces.mixed b a g p.1 p.2
            ∂((volume.restrict Work.Spaces.Iz).prod (volume.restrict Work.Spaces.Iθ))) :=
    (MeasureTheory.integral_congr_ae hsplit_ae).trans
      (MeasureTheory.integral_add hflux.1 hremint)
  have hfin : |Work.FTS.TransportS.slotPairing ρ a b X g| ≤ 6402 * Mf * Work.Spaces.HkSq α 4 g := by
    rw [hident, hsplit]
    calc |(∫ p, ρ p.1 p.2 * f p.1 p.2 * Work.Spaces.Dz (Work.Spaces.mixed b a g) p.1 p.2
              * Work.Spaces.mixed b a g p.1 p.2
              ∂((volume.restrict Work.Spaces.Iz).prod (volume.restrict Work.Spaces.Iθ)))
          + (∫ p, ρ p.1 p.2 * (Work.Spaces.mixed b a X p.1 p.2
                - f p.1 p.2 * Work.Spaces.Dz (Work.Spaces.mixed b a g) p.1 p.2)
              * Work.Spaces.mixed b a g p.1 p.2
              ∂((volume.restrict Work.Spaces.Iz).prod (volume.restrict Work.Spaces.Iθ)))|
        ≤ |(∫ p, ρ p.1 p.2 * f p.1 p.2 * Work.Spaces.Dz (Work.Spaces.mixed b a g) p.1 p.2
              * Work.Spaces.mixed b a g p.1 p.2
              ∂((volume.restrict Work.Spaces.Iz).prod (volume.restrict Work.Spaces.Iθ)))|
          + |(∫ p, ρ p.1 p.2 * (Work.Spaces.mixed b a X p.1 p.2
                - f p.1 p.2 * Work.Spaces.Dz (Work.Spaces.mixed b a g) p.1 p.2)
              * Work.Spaces.mixed b a g p.1 p.2
              ∂((volume.restrict Work.Spaces.Iz).prod (volume.restrict Work.Spaces.Iθ)))| := abs_add_le _ _
      _ ≤ 2 * Mf * Work.Spaces.HkSq α 4 g + 6400 * Mf * Work.Spaces.HkSq α 4 g :=
          add_le_add hflux.2 hrembound
      _ = 6402 * Mf * Work.Spaces.HkSq α 4 g := by ring
  -- ## the arithmetic
  have hMfle : Mf ≤ (101 + C_f) * (Work.Spaces.WlInf α 4 f + Work.FTS.VocabO.CoefTh 3 f) := by
    rw [hMfdef]; nlinarith [hWnn, hCnn, hC_f_pos.le]
  have hαpow : 1 ≤ α ^ (-(1 / 2 : ℝ)) := by
    have hpos : 0 < α ^ (1 / 2 : ℝ) := Real.rpow_pos_of_pos hα _
    have hle : α ^ (1 / 2 : ℝ) ≤ 1 := Real.rpow_le_one hα.le hα1 (by norm_num)
    have hneg : α ^ (-(1 / 2 : ℝ)) = (α ^ (1 / 2 : ℝ))⁻¹ := Real.rpow_neg hα.le (1 / 2)
    rw [hneg]
    exact (one_le_inv₀ hpos).mpr hle
  rw [hX]
  refine hfin.trans ?_
  have hHk : Work.Spaces.HkSq α 4 g = (Work.FTS.Nonlin.Xn α g) ^ 2 :=
    (Work.FTS.H2.HkNorm_sq α g).symm
  rw [hHk]
  calc 6402 * Mf * (Work.FTS.Nonlin.Xn α g) ^ 2
      ≤ 6402 * ((101 + C_f) * (Work.Spaces.WlInf α 4 f + Work.FTS.VocabO.CoefTh 3 f))
          * (Work.FTS.Nonlin.Xn α g) ^ 2 := by
        refine mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hMfle (by norm_num))
          (sq_nonneg _)
    _ ≤ 6402 * ((101 + C_f) * (Work.Spaces.WlInf α 4 f + Work.FTS.VocabO.CoefTh 3 f))
          * α ^ (-(1 / 2 : ℝ)) * (Work.FTS.Nonlin.Xn α g) ^ 2 := by
        have h0 : 0 ≤ 6402 * ((101 + C_f) * (Work.Spaces.WlInf α 4 f
            + Work.FTS.VocabO.CoefTh 3 f)) := by positivity
        calc 6402 * ((101 + C_f) * (Work.Spaces.WlInf α 4 f + Work.FTS.VocabO.CoefTh 3 f))
              * (Work.FTS.Nonlin.Xn α g) ^ 2
            = (6402 * ((101 + C_f) * (Work.Spaces.WlInf α 4 f
                + Work.FTS.VocabO.CoefTh 3 f)) * 1)
              * (Work.FTS.Nonlin.Xn α g) ^ 2 := by ring
          _ ≤ (6402 * ((101 + C_f) * (Work.Spaces.WlInf α 4 f + Work.FTS.VocabO.CoefTh 3 f))
                * α ^ (-(1 / 2 : ℝ))) * (Work.FTS.Nonlin.Xn α g) ^ 2 :=
              mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hαpow h0) (sq_nonneg _)
          _ = 6402 * ((101 + C_f) * (Work.Spaces.WlInf α 4 f + Work.FTS.VocabO.CoefTh 3 f))
                * α ^ (-(1 / 2 : ℝ)) * (Work.FTS.Nonlin.Xn α g) ^ 2 := by ring
    _ = 6402 * (101 + C_f) * α ^ (-(1 / 2 : ℝ))
          * (Work.Spaces.WlInf α 4 f + Work.FTS.VocabO.CoefTh 3 f)
          * (Work.FTS.Nonlin.Xn α g) ^ 2 := by ring

end Work.FTS.StrongPersist.N6Trans.Hon
