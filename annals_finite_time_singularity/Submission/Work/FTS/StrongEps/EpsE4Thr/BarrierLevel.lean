/-
Copyright: work module for the Elgindi finite-time singularity project.

# `EpsE4Thr/BarrierLevel.lean` — the barrier lemma with the derivative hypothesis **only at the
barrier level**

`Work.FTS.Apriori.barrier_within` (and the localised forms `barrier_within_Ico`,
`barrier_within_Icc_of_hasDerivWithinAt` of `BarrierIco.lean`) require the within-derivative
`HasDerivWithinAt E (E' τ) (Icc 0 T) τ` at *every* `τ ∈ Ico 0 T`; the strict negativity `E' τ < 0`
is already required only at the times at which `E` meets the level `Y` (`hneg`).

That *global* derivative hypothesis is what makes the level-four a-priori chapter circular
(session-10 finding (XI)): the only producer of the energy identity
(`DiagCurveISolution.EnergyDeriv_IP4_JfamP_of_solution`) needs the small-ball hypothesis
`Xn α (Pz (J_ε (slice g s))) ≤ C₀ α²` on the *whole* interval `Icc 0 T`, while the ball on the
whole interval is exactly what the barrier is meant to prove.

This module removes the circularity at its root: the first-crossing argument of
`Work.FTS.Apriori.barrier_within` consumes the derivative only at the **crossing point** `p`
(cf. `Work.FTS.Apriori.crossing_Icc` + `Work.FTS.Apriori.descent_Icc`), so the global hypothesis
can be replaced by

  `∀ τ ∈ Set.Ico 0 T, E τ = Y → HasDerivWithinAt E (E' τ) (Set.Icc 0 T) τ`.

At a crossing time the ball *is* available (from the relation `E τ = Y` and the comparability
`clo·|f|²_{ℋ⁴} ≤ IP α f f` of the coercive pairing, see `BallAtLevel.lean`), so the energy identity
becomes producible at exactly the times the barrier needs it.

Everything here is `sorry`-free.
-/
import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Calculus.Deriv.Slope
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Mathlib.Analysis.Normed.Group.AddTorsor
import Mathlib.Topology.Algebra.Module.ModuleTopology
import Submission.Work.FTS.Apriori.Barrier

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section
open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.StrongEps.EpsE4Thr

set_option autoImplicit false
set_option linter.unusedVariables false

/-- **The barrier lemma with the derivative hypothesis only at the barrier level.**

Let `E` be continuous on `[0,T]`, `E 0 < Y`, and suppose that at every `τ ∈ [0,T)` at which
`E τ = Y` the function `E` has a within-`[0,T]`-derivative `E' τ < 0`.  Then `E τ ≤ Y` on `[0,T]`.

This is `Work.FTS.Apriori.barrier_within` with `hderiv` weakened from "at every `τ ∈ Ico 0 T`" to
"at every `τ ∈ Ico 0 T` with `E τ = Y`": the first-crossing argument never consults the derivative
away from the level. -/
theorem barrier_within_level {E E' : ℝ → ℝ} {Y T : ℝ}
    (hcont : ContinuousOn E (Set.Icc 0 T)) (h0 : E 0 < Y)
    (hderiv : ∀ τ ∈ Set.Ico 0 T, E τ = Y → HasDerivWithinAt E (E' τ) (Set.Icc 0 T) τ)
    (hneg : ∀ τ ∈ Set.Ico 0 T, E τ = Y → E' τ < 0) :
    ∀ τ ∈ Set.Icc 0 T, E τ ≤ Y := by
  by_contra hcon
  push_neg at hcon
  obtain ⟨τ₀, hτ₀, hgt⟩ := hcon
  obtain ⟨hp0, hplt, hpY⟩ := Work.FTS.Apriori.crossing_Icc hcont h0 hτ₀ hgt
  set p : ℝ := sSup (Set.Icc 0 τ₀ ∩ E ⁻¹' Set.Iic Y) with hpdef
  have hpT : p < T := lt_of_lt_of_le hplt hτ₀.2
  have hmem : p ∈ Set.Ico 0 T := ⟨hp0.le, hpT⟩
  obtain ⟨δ, hδpos, hδ⟩ :=
    Work.FTS.Apriori.descent_Icc hp0 hpT (hderiv p hmem hpY) (hneg p hmem hpY)
  set z : ℝ := p + min δ (τ₀ - p) / 2 with hzdef
  have hzp : p < z := by
    rw [hzdef]; have := lt_min hδpos (sub_pos.mpr hplt); linarith
  have hzτ : z < τ₀ := by
    rw [hzdef]; have := min_le_right δ (τ₀ - p); linarith
  have hzδ : z < p + δ := by
    rw [hzdef]; have := min_le_left δ (τ₀ - p); linarith
  have hzS : z ∈ Set.Icc 0 τ₀ ∩ E ⁻¹' Set.Iic Y := by
    refine ⟨⟨le_of_lt (lt_trans hp0 hzp), le_of_lt hzτ⟩, ?_⟩
    have hlt := hδ z hzp hzδ
    rw [hpY] at hlt
    exact le_of_lt hlt
  have hle := le_csSup ⟨τ₀, fun x hx => hx.1.2⟩ hzS
  rw [← hpdef] at hle
  linarith

/-- **The barrier lemma on the half-open interval, with the derivative only at the level.**

Combines `barrier_within_level` with the subinterval reduction of
`BarrierIco.barrier_within_Ico`: continuity on `Ico 0 T` suffices. -/
theorem barrier_within_level_Ico {E E' : ℝ → ℝ} {Y T : ℝ} (hT : 0 < T)
    (hcont : ContinuousOn E (Set.Ico 0 T))
    (hderiv : ∀ τ ∈ Set.Ico 0 T, E τ = Y → HasDerivWithinAt E (E' τ) (Set.Icc 0 T) τ)
    (h0 : E 0 < Y)
    (hneg : ∀ τ ∈ Set.Ico 0 T, E τ = Y → E' τ < 0) :
    ∀ τ ∈ Set.Ico 0 T, E τ ≤ Y := by
  intro τ hτ
  have hτT : τ < T := hτ.2
  set T' : ℝ := (τ + T) / 2 with hT'def
  have hT'T : T' < T := by rw [hT'def]; linarith
  have hτT' : τ ≤ T' := by rw [hT'def]; linarith
  have hsub : Set.Icc 0 T' ⊆ Set.Ico 0 T :=
    fun x hx => ⟨hx.1, lt_of_le_of_lt hx.2 hT'T⟩
  have hsubD : Set.Icc 0 T' ⊆ Set.Icc 0 T := Set.Icc_subset_Icc_right (le_of_lt hT'T)
  exact barrier_within_level (E := E) (E' := E') (Y := Y) (T := T')
    (hcont.mono hsub) h0
    (fun s hs hsY => (hderiv s (hsub ⟨hs.1, le_of_lt hs.2⟩) hsY).mono hsubD)
    (fun s hs hsY => hneg s (hsub ⟨hs.1, le_of_lt hs.2⟩) hsY)
    τ ⟨hτ.1, hτT'⟩

/-- **The `Icc`-form with a one-sided endpoint hypothesis.**

Same as `barrier_within_level`, with the conclusion extended to `τ = T` at the price of the single
hypothesis `ContinuousWithinAt E (Icc 0 T) T` (the left limit at `T`), exactly as in
`BarrierIco.barrier_within_Icc_of_hasDerivWithinAt`. -/
theorem barrier_within_level_endpoint {E E' : ℝ → ℝ} {Y T : ℝ} (hT : 0 < T)
    (hcont : ContinuousOn E (Set.Ico 0 T))
    (hderiv : ∀ τ ∈ Set.Ico 0 T, E τ = Y → HasDerivWithinAt E (E' τ) (Set.Icc 0 T) τ)
    (h0 : E 0 < Y)
    (hneg : ∀ τ ∈ Set.Ico 0 T, E τ = Y → E' τ < 0)
    (hcontT : ContinuousWithinAt E (Set.Icc 0 T) T) :
    ∀ τ ∈ Set.Icc 0 T, E τ ≤ Y := by
  have hIco : ∀ τ ∈ Set.Ico 0 T, E τ ≤ Y :=
    barrier_within_level_Ico hT hcont hderiv h0 hneg
  intro τ hτ
  rcases lt_or_eq_of_le hτ.2 with h | h
  · exact hIco τ ⟨hτ.1, h⟩
  · rw [h]
    set u : ℕ → ℝ := fun n => T - min (T / 2) (1 / ((n : ℝ) + 1)) with hudef
    have hsmall : ∀ n : ℕ, 0 < min (T / 2) (1 / ((n : ℝ) + 1)) := fun n =>
      lt_min (by linarith) (by positivity)
    have hleT : ∀ n : ℕ, min (T / 2) (1 / ((n : ℝ) + 1)) ≤ T / 2 := fun n => min_le_left _ _
    have hu_lt : ∀ n : ℕ, u n < T := by
      intro n; simp only [u]; linarith [hsmall n]
    have hu_ge : ∀ n : ℕ, 0 ≤ u n := by
      intro n; simp only [u]; linarith [hleT n, hT]
    have hmin_tendsto : Tendsto (fun n : ℕ => min (T / 2) (1 / ((n : ℝ) + 1))) atTop (𝓝 0) := by
      have h1 : Tendsto (fun n : ℕ => (1 : ℝ) / ((n : ℝ) + 1)) atTop (𝓝 (0 : ℝ)) :=
        tendsto_one_div_add_atTop_nhds_zero_nat
      have h2 : Tendsto (fun _ : ℕ => T / 2) atTop (𝓝 (T / 2)) := tendsto_const_nhds
      have h3 : Tendsto (fun n : ℕ => min (T / 2) (1 / ((n : ℝ) + 1))) atTop
          (𝓝 (min (T / 2) (0 : ℝ))) := h2.min h1
      simpa [min_eq_right (by linarith : (0 : ℝ) ≤ T / 2)] using h3
    have hu_tendsto : Tendsto u atTop (𝓝 T) := by
      have h4 : Tendsto (fun n : ℕ => T - min (T / 2) (1 / ((n : ℝ) + 1))) atTop
          (𝓝 (T - 0)) := tendsto_const_nhds.sub hmin_tendsto
      simpa [u] using h4
    have hu_nhds : Tendsto u atTop (𝓝[Set.Icc 0 T] T) := by
      rw [tendsto_nhdsWithin_iff]
      exact ⟨hu_tendsto, Filter.Eventually.of_forall fun n => ⟨hu_ge n, (hu_lt n).le⟩⟩
    have hEseq : Tendsto (fun n : ℕ => E (u n)) atTop (𝓝 (E T)) := hcontT.tendsto.comp hu_nhds
    have hle : ∀ᶠ n in atTop, E (u n) ≤ Y :=
      Filter.Eventually.of_forall fun n => hIco (u n) ⟨hu_ge n, hu_lt n⟩
    exact le_of_tendsto_of_tendsto hEseq tendsto_const_nhds hle

/-! ## The trap with **left** derivatives

The producer of the energy identity at the *right endpoint* `τ` of a horizon (module
`EnergyDerivLeft.lean`, delegated) delivers a left (within-`Icc 0 τ`) derivative: at the *first*
time at which the energy exceeds the level, the small ball is available on `[0,τ]` and only there.
The trap below uses exactly that one-sided information, and it consumes the level-point data in the
form "given the level at `τ` and the level bound on `[0,τ)`, the left derivative at `τ` exists and
is negative" — which is what the endpoint energy identity plus the `hneg` split provide. -/

/-- **One-sided descent to the left.**

If `f` has within-`[0,p]`-derivative `f' < 0` at `p`, then `f` is strictly above `f p` just to the
left of `p`.  This is the mirror image of
`Work.Construction.barrier_exists_right_lt_of_hasDerivAt_neg`; it is proved from
`HasDerivWithinAt.limsup_slope_le` and the basis `nhdsLT_basis p` of `𝓝[<] p`. -/
theorem exists_gt_of_hasDerivWithinAt_Icc_left {f : ℝ → ℝ} {f' p : ℝ} (hp : 0 ≤ p)
    (h : HasDerivWithinAt f f' (Set.Icc 0 p) p) (hf' : f' < 0) :
    ∃ δ > 0, ∀ t ∈ Set.Icc 0 p, p - δ < t → t < p → f p < f t := by
  rcases eq_or_lt_of_le hp with rfl | hp0
  · exact ⟨1, one_pos, fun t ht _ h2 => absurd h2 (not_lt.mpr ht.1)⟩
  · set r : ℝ := f' / 2 with hr
    have hrlt : f' < r := by rw [hr]; linarith
    have hev : ∀ᶠ z in 𝓝[Set.Ico 0 p] p, slope f p z < r := by
      have h1 : ∀ᶠ z in 𝓝[(Set.Icc 0 p) \ {p}] p, slope f p z < r := h.limsup_slope_le hrlt
      have hset : (Set.Icc 0 p) \ {p} = Set.Ico 0 p := by
        ext z
        simp only [Set.mem_diff, Set.mem_Icc, Set.mem_singleton_iff, Set.mem_Ico]
        constructor
        · rintro ⟨⟨h1, h2⟩, h3⟩; exact ⟨h1, lt_of_le_of_ne h2 h3⟩
        · rintro ⟨h1, h2⟩; exact ⟨⟨h1, h2.le⟩, ne_of_lt h2⟩
      rwa [hset] at h1
    have heq : 𝓝[Set.Ico 0 p] p = 𝓝[<] p := by
      refine le_antisymm (inf_le_inf_left _ (principal_mono.mpr fun z hz => hz.2)) ?_
      refine le_inf inf_le_left ?_
      rw [le_principal_iff]
      exact mem_of_superset (Ioo_mem_nhdsLT (by linarith : p / 2 < p))
        (fun z hz => ⟨by linarith [hz.1], hz.2⟩)
    rw [heq] at hev
    rw [(nhdsLT_basis p).eventually_iff] at hev
    obtain ⟨ε, hε, hε'⟩ := hev
    refine ⟨p - ε, sub_pos.mpr hε, fun t _ h1 h2 => ?_⟩
    have htε : t ∈ Set.Ioo ε p := ⟨by linarith, h2⟩
    have hd := hε' htε
    have hsl : slope f p t < 0 := lt_trans hd (show r < 0 by rw [hr]; linarith)
    rw [slope_def_field] at hsl
    have htp : t - p < 0 := by linarith
    have hpos : 0 < (f t - f p) / (t - p) * (t - p) := mul_pos_of_neg_of_neg hsl htp
    rw [div_mul_cancel₀ _ (ne_of_lt htp)] at hpos
    linarith

/-- **The trap barrier with left derivatives.**

Let `E` be continuous on `Ico 0 T` with `E 0 < Y`, and suppose that at every **interior**
`τ ∈ Ioo 0 T` at which the level is met (`E τ = Y`) *and* the level bound holds on `[0,τ)`, the
function `E` has a strictly negative within-`Icc 0 τ`-derivative at `τ` (the hypothesis is
restricted to interior `τ` because the crossing point of the proof is interior, and because at
`τ = 0` a within-`Icc 0 0`-derivative forces `E' 0 = 0`).  Then `E τ ≤ Y` on `Ico 0 T`.

Proof: let `A := {t ∈ Icc 0 τ₁ : E t > Y}` be nonempty and `t₀ := sInf A`.  Then `t₀ ∈ Ico 0 T`,
`E ≤ Y` on `[0,t₀)` (minimality of `t₀`), `t₀ > 0` (continuity at `0`), `E t₀ = Y` (two continuity
arguments), so the level-point hypothesis applies at `t₀` and the left descent of
`exists_gt_of_hasDerivWithinAt_Icc_left` contradicts `E ≤ Y` on `[0,t₀)`. -/
theorem barrier_within_level_left {E E' : ℝ → ℝ} {Y T : ℝ} (hT : 0 < T)
    (hcont : ContinuousOn E (Set.Ico 0 T))
    (h0 : E 0 < Y)
    (hlev : ∀ τ ∈ Set.Ioo 0 T, (∀ t ∈ Set.Ico 0 τ, E t ≤ Y) → E τ = Y →
      HasDerivWithinAt E (E' τ) (Set.Icc 0 τ) τ ∧ E' τ < 0) :
    ∀ τ ∈ Set.Ico 0 T, E τ ≤ Y := by
  by_contra hcon
  push_neg at hcon
  obtain ⟨τ₁, hτ₁, hgt⟩ := hcon
  have hcontIcc : ContinuousOn E (Set.Icc 0 τ₁) :=
    hcont.mono fun x hx => ⟨hx.1, lt_of_le_of_lt hx.2 hτ₁.2⟩
  set A : Set ℝ := {t : ℝ | t ∈ Set.Icc 0 τ₁ ∧ Y < E t} with hA
  have hAne : A.Nonempty := ⟨τ₁, ⟨⟨hτ₁.1, le_rfl⟩, hgt⟩⟩
  have hAbdd : BddBelow A := ⟨0, fun x hx => hx.1.1⟩
  set t₀ : ℝ := sInf A with ht₀
  have ht₀le : t₀ ≤ τ₁ := csInf_le hAbdd ⟨⟨hτ₁.1, le_rfl⟩, hgt⟩
  have ht₀ge : 0 ≤ t₀ := le_csInf hAne fun y hy => hy.1.1
  have ht₀lt : t₀ < T := lt_of_le_of_lt ht₀le hτ₁.2
  have ht₀mem : t₀ ∈ Set.Ico 0 T := ⟨ht₀ge, ht₀lt⟩
  -- the level bound on `[0,t₀)` from the minimality of `t₀`
  have hbelow : ∀ t ∈ Set.Ico 0 t₀, E t ≤ Y := by
    intro t ht
    by_contra hty
    have hty' : Y < E t := not_le.mp hty
    have htmem : t ∈ A := ⟨⟨ht.1, le_trans ht.2.le ht₀le⟩, hty'⟩
    have h2 : t₀ ≤ t := csInf_le hAbdd htmem
    linarith [ht.2]
  -- `t₀ > 0`: `E < Y` on a right neighbourhood of `0`
  have ht₀pos : 0 < t₀ := by
    have hEv : {t : ℝ | E t < Y} ∈ 𝓝[Set.Icc 0 τ₁] 0 :=
      (hcontIcc.continuousWithinAt ⟨le_rfl, hτ₁.1⟩).preimage_mem_nhdsWithin
        (isOpen_Iio.mem_nhds h0)
    have hEv' : {x : ℝ | x ∈ Set.Icc 0 τ₁ → E x < Y} ∈ 𝓝 (0 : ℝ) :=
      Filter.mem_inf_principal.mp hEv
    obtain ⟨ε, hε, hball⟩ := Metric.mem_nhds_iff.mp hEv'
    have hle : ε ≤ t₀ := by
      refine le_csInf hAne fun y hy => ?_
      by_contra hyy
      have hdist : dist y 0 < ε := by
        rw [Real.dist_eq, sub_zero, abs_of_nonneg hy.1.1]
        exact not_le.mp hyy
      exact absurd (hball hdist hy.1) (not_lt.mpr hy.2.le)
    linarith
  -- `E t₀ ≤ Y`, by continuity from the left
  have ht₀leY : E t₀ ≤ Y := by
    have hclosed : IsClosed (Set.Icc 0 τ₁ ∩ E ⁻¹' Set.Iic Y) :=
      hcontIcc.preimage_isClosed_of_isClosed isClosed_Icc isClosed_Iic
    have hsub : Set.Ioo 0 t₀ ⊆ Set.Icc 0 τ₁ ∩ E ⁻¹' Set.Iic Y := fun x hx =>
      ⟨⟨hx.1.le, le_trans hx.2.le ht₀le⟩, hbelow x ⟨hx.1.le, hx.2⟩⟩
    have hcl : Set.Icc 0 t₀ ⊆ Set.Icc 0 τ₁ ∩ E ⁻¹' Set.Iic Y := by
      rw [← closure_Ioo (ne_of_lt ht₀pos)]
      exact closure_minimal hsub hclosed
    exact (hcl ⟨ht₀ge, le_rfl⟩).2
  -- `Y ≤ E t₀`, else a right neighbourhood of `t₀` misses `A`
  have ht₀geY : Y ≤ E t₀ := by
    by_contra hlt
    have hlt' : E t₀ < Y := not_le.mp hlt
    have hEv : {t : ℝ | E t < Y} ∈ 𝓝[Set.Icc 0 τ₁] t₀ :=
      (hcontIcc.continuousWithinAt ⟨ht₀ge, ht₀le⟩).preimage_mem_nhdsWithin
        (isOpen_Iio.mem_nhds hlt')
    have hEv' : {x : ℝ | x ∈ Set.Icc 0 τ₁ → E x < Y} ∈ 𝓝 t₀ :=
      Filter.mem_inf_principal.mp hEv
    obtain ⟨ε, hε, hball⟩ := Metric.mem_nhds_iff.mp hEv'
    have hbound : ∀ y ∈ A, t₀ + min ε 1 ≤ y := by
      intro y hy
      by_contra hyy
      have hyge : t₀ ≤ y := csInf_le hAbdd hy
      have hdist : dist y t₀ < ε := by
        rw [Real.dist_eq, abs_of_nonneg (sub_nonneg.mpr hyge)]
        linarith [min_le_left ε 1]
      exact absurd (hball hdist hy.1) (not_lt.mpr hy.2.le)
    have hle : t₀ + min ε 1 ≤ t₀ := by
      have h1 : t₀ + min ε 1 ≤ sInf A := le_csInf hAne hbound
      simpa only [ht₀] using h1
    have h2 : 0 < min ε 1 := lt_min hε zero_lt_one
    linarith
  have ht₀Y : E t₀ = Y := le_antisymm ht₀leY ht₀geY
  obtain ⟨hderiv, hneg⟩ := hlev t₀ ⟨ht₀pos, ht₀lt⟩ hbelow ht₀Y
  obtain ⟨δ, hδpos, hδ⟩ := exists_gt_of_hasDerivWithinAt_Icc_left ht₀ge hderiv hneg
  set z : ℝ := t₀ - min δ t₀ / 2 with hzdef
  have hzlt : z < t₀ := by
    rw [hzdef]; have := lt_min hδpos ht₀pos; linarith
  have hzge : 0 ≤ z := by
    rw [hzdef]; have := min_le_right δ t₀; linarith
  have hzδ : t₀ - δ < z := by
    rw [hzdef]; have := min_le_left δ t₀; linarith
  have hgt' : E t₀ < E z := hδ z ⟨hzge, hzlt.le⟩ hzδ hzlt
  have hb := hbelow z ⟨hzge, hzlt⟩
  rw [ht₀Y] at hgt'
  linarith

end Work.FTS.StrongEps.EpsE4Thr
