/-
Copyright: work module for the Elgindi finite-time singularity project.

# The `hRi`-input of S8: integrability in `τ` of the mixed jets of `∂_τg`

`Work.FTS.RegExportIface.RXT.intervalIntegrable_mixed_gdot` (leaf statement of the RX-T / RX-St1
plan, `Submission/Work/FTS/RegExportIface/RXT/Leaves.lean`): under `GdotLoc S g`, for every point
`(z,θ)` of the open quadrant and every one of the six components `β = idx k`, the map
`σ ↦ D^β(∂_τg)(z,θ,σ)` is interval integrable on `[0,S]`.

`GdotLoc S g` supplies exactly two things at the point `(z,θ)`:

* every slice `gdot g σ` (`σ ∈ (0,S]`) is `C²` on the open quadrant `Q0`, and
* on every compact sub-box of `Q0` the slots `mixed j i (gdot g σ)` (`j+i ≤ 2`) are bounded
  uniformly in `σ ∈ (0,S]`.

Boundedness on the *finite* interval `(0,S]` turns the second into `IntegrableOn` as soon as the
map `σ ↦ mixed j i (gdot g σ) z θ` is a.e. strongly measurable, and the measurability is the only
real content of the proof:

`σ ↦ (gdot g σ)(z,θ) = deriv (fun s => g z θ s) σ` is measurable by `measurable_deriv`, which
needs no hypothesis at all; and the `(z,θ)`-derivatives are limits of difference quotients, so a
pointwise limit of measurable functions is again measurable.  The induction over the total order
of `(j,i)` uses the difference-quotient representation

`D_z^{j+1}D_θ^i (H σ)(a,b) = a · lim_n (D_z^jD_θ^i(H σ)(a+a/(n+1),b) - D_z^jD_θ^i(H σ)(a,b))/(a/(n+1))`

(valid because `H σ` is `C²` on the open quadrant, so the `z`-slice of each slot of total order
`≤ 1` is differentiable), and its `θ`-analogue with the shift `(π/2-θ)/(2(n+1))`.  Each induction
step keeps the `D_z`-operator outermost, which is why no commutation of `D_z` with `D_θ` is needed:
only the pairs `(j+1,i) ← (j,i)` and `(0,i+1) ← (0,i)` are used.

Note that this is the *finite-order* form of the engine `Work.FTS.StrongEps.aemeasurable_mixed_family`
(which needs `C^∞` per slice plus continuity in `σ`); the hypotheses here give only `C²` per slice.
-/
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.Calculus.FDeriv.Measurable
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.Order.CompletePartialOrder
import Submission.Work.FTS.RegExportIface.RXT.Leaves
import Submission.Work.FTS.StrongEps.HkMem_of_tendsto
import Submission.Work.FTS_RegExport.RXT.Sys.abs_mixed_gdot_le_of_GdotLoc
import Submission.Work.FTS_RegExport.RXT.Sys.integrableOn_Ioc_of_abs_bound
import Submission.Work.FTS_RegExport.RXT.Sys.aestronglyMeasurable_restrict_of_ae_eq

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section
open scoped Real Topology
open Set Filter MeasureTheory

namespace Work.FTS_RegExport.RXT.Sys

set_option autoImplicit false
set_option linter.unusedVariables false

/-! ## Two elementary tools -/

/-- **The slots of total order `≤ 1` of a `C²` function on the open quadrant are `C¹`.**  This is
the only place where the `C²`-regularity of `GdotLoc` is used beyond differentiability of `G`: the
`z`- and `θ`-slices of `mixed j i` (`j + i ≤ 1`) are differentiable at every point of `Q0`.
(For `j = i = 0` it is `ContDiffOn.of_le`; for the two first-order slots it is the finite-order
`D`-calculus of `Work.FTS.StrongEps`.) -/
private theorem contDiffOn_one_of_total_le_one {H : ℝ → ℝ → ℝ}
    (hH : ContDiffOn ℝ 2 (Function.uncurry H) Work.FTS.EllipticEst.Q0) {j i : ℕ} (hji : j + i ≤ 1) :
    ContDiffOn ℝ 1 (Function.uncurry (Work.Spaces.mixed j i H)) Work.FTS.EllipticEst.Q0 := by
  obtain rfl | rfl : j = 0 ∨ j = 1 := by omega
  · obtain rfl | rfl : i = 0 ∨ i = 1 := by omega
    · simpa [Work.Spaces.mixed] using hH.of_le (by norm_num : (1 : WithTop ℕ∞) ≤ 2)
    · simpa [Work.Spaces.mixed] using Work.FTS.StrongEps.contDiffOn_uncurry_Dth_fin
        Work.FTS.EllipticEst.isOpen_Q0 (n := 1) hH
  · obtain rfl | rfl : i = 0 ∨ i = 1 := by omega
    · simpa [Work.Spaces.mixed] using Work.FTS.StrongEps.contDiffOn_uncurry_Dz_fin
        Work.FTS.EllipticEst.isOpen_Q0 (n := 1) hH
    · omega

/-- `HasDerivAt` turns the right-hand difference quotients along `ε₀/(n+1)` into a limit. -/
private theorem tendsto_slope_seq {f : ℝ → ℝ} {x L ε₀ : ℝ} (hε : 0 < ε₀)
    (h : HasDerivAt f L x) :
    Tendsto (fun n : ℕ => (f (x + ε₀ / (n + 1)) - f x) / (ε₀ / (n + 1))) atTop (𝓝 L) := by
  have hδ0 : Tendsto (fun n : ℕ => ε₀ / (n + 1)) atTop (𝓝 (0 : ℝ)) := by
    have h1 : Tendsto (fun n : ℕ => (1 : ℝ) / (n + 1)) atTop (𝓝 0) :=
      tendsto_one_div_add_atTop_nhds_zero_nat
    simpa [div_eq_mul_inv, mul_comm] using h1.const_mul ε₀
  have hpos : ∀ n : ℕ, ε₀ / (n + 1) ≠ 0 := fun n => by positivity
  have hx : Tendsto (fun n : ℕ => x + ε₀ / (n + 1)) atTop (𝓝[≠] x) :=
    tendsto_nhdsWithin_iff.mpr ⟨by simpa using hδ0.const_add x,
      Filter.Eventually.of_forall fun n => by
        simp only [Set.mem_compl_iff, Set.mem_singleton_iff]
        intro hh
        exact hpos n (by linarith)⟩
  refine (h.tendsto_slope.comp hx).congr' ?_
  filter_upwards with n
  simp only [Function.comp_apply, slope, smul_eq_mul, div_eq_mul_inv, vsub_eq_sub]
  ring

/-! ## The two induction steps -/

/-- **The `z`-step.**  If the values `σ ↦ mixed j i (H σ) a b` are measurable (`j + i ≤ 1`), then
so are the values of `mixed (j+1) i`: on `σ ∈ (0,S]` the latter is `a` times the `z`-difference
quotient of the former, and outside that set both sides vanish. -/
private theorem measurable_zstep {S : ℝ} {H : ℝ → ℝ → ℝ → ℝ} {j i : ℕ} (hji : j + i ≤ 1)
    (hCd : ∀ σ ∈ Set.Ioc (0 : ℝ) S,
      ContDiffOn ℝ 2 (Function.uncurry (H σ)) Work.FTS.EllipticEst.Q0)
    (ih : ∀ a b : ℝ, (a, b) ∈ Work.FTS.EllipticEst.Q0 →
      Measurable (fun σ : ℝ => if σ ∈ Set.Ioc (0 : ℝ) S then
        Work.Spaces.mixed j i (H σ) a b else 0)) :
    ∀ a b : ℝ, (a, b) ∈ Work.FTS.EllipticEst.Q0 →
      Measurable (fun σ : ℝ => if σ ∈ Set.Ioc (0 : ℝ) S then
        Work.Spaces.mixed (j + 1) i (H σ) a b else 0) := by
  intro a b hab
  obtain ⟨ha, hb0, hb1⟩ := Work.FTS.EllipticEst.mem_Q0.mp hab
  have hδpos : ∀ n : ℕ, 0 < a / ((n : ℝ) + 1) := fun n => by positivity
  have hmem : ∀ n : ℕ, (a + a / ((n : ℝ) + 1), b) ∈ Work.FTS.EllipticEst.Q0 := fun n =>
    Work.FTS.EllipticEst.mem_Q0.mpr ⟨by linarith [hδpos n], hb0, hb1⟩
  have hdiff : ∀ σ ∈ Set.Ioc (0 : ℝ) S, HasDerivAt (fun z' => Work.Spaces.mixed j i (H σ) z' b)
      (Work.Spaces.pz (Work.Spaces.mixed j i (H σ)) a b) a := by
    intro σ hσ
    have hB : ContDiffOn ℝ 1 (Function.uncurry (Work.Spaces.mixed j i (H σ)))
        Work.FTS.EllipticEst.Q0 := contDiffOn_one_of_total_le_one (hCd σ hσ) hji
    have hD : DifferentiableAt ℝ (Function.uncurry (Work.Spaces.mixed j i (H σ))) (a, b) :=
      (hB.differentiableOn (by norm_num)).differentiableAt
        (Work.FTS.EllipticEst.isOpen_Q0.mem_nhds hab)
    simpa [Work.Spaces.pz] using (Work.Spaces.differentiableAt_curry_left hD).hasDerivAt
  have hmeas : ∀ n : ℕ, Measurable (fun σ : ℝ => if σ ∈ Set.Ioc (0 : ℝ) S then
      a * ((Work.Spaces.mixed j i (H σ) (a + a / ((n : ℝ) + 1)) b
        - Work.Spaces.mixed j i (H σ) a b) / (a / ((n : ℝ) + 1))) else 0) := by
    intro n
    have h1 := ih (a + a / ((n : ℝ) + 1)) b (hmem n)
    have h2 := ih a b hab
    have heq : (fun σ : ℝ => if σ ∈ Set.Ioc (0 : ℝ) S then
        a * ((Work.Spaces.mixed j i (H σ) (a + a / ((n : ℝ) + 1)) b
          - Work.Spaces.mixed j i (H σ) a b) / (a / ((n : ℝ) + 1))) else 0)
        = fun σ : ℝ => a * (((if σ ∈ Set.Ioc (0 : ℝ) S then
            Work.Spaces.mixed j i (H σ) (a + a / ((n : ℝ) + 1)) b else 0)
          - (if σ ∈ Set.Ioc (0 : ℝ) S then Work.Spaces.mixed j i (H σ) a b else 0))
            / (a / ((n : ℝ) + 1))) := by
      funext σ
      by_cases hσ : σ ∈ Set.Ioc (0 : ℝ) S <;> simp [hσ]
    rw [heq]
    exact ((h1.sub h2).div_const (a / ((n : ℝ) + 1))).const_mul a
  refine measurable_of_tendsto_metrizable hmeas ?_
  rw [tendsto_pi_nhds]
  intro σ
  by_cases hσ : σ ∈ Set.Ioc (0 : ℝ) S
  · rw [ite_eq_left hσ]
    have hlim := tendsto_slope_seq ha (hdiff σ hσ)
    have hval : Work.Spaces.mixed (j + 1) i (H σ) a b
        = a * Work.Spaces.pz (Work.Spaces.mixed j i (H σ)) a b := rfl
    rw [hval]
    refine (hlim.const_mul a).congr' ?_
    filter_upwards with n
    rw [ite_eq_left hσ]
  · rw [ite_eq_right hσ]
    have hzero : (fun n : ℕ => if σ ∈ Set.Ioc (0 : ℝ) S then
        a * ((Work.Spaces.mixed j i (H σ) (a + a / ((n : ℝ) + 1)) b
          - Work.Spaces.mixed j i (H σ) a b) / (a / ((n : ℝ) + 1))) else 0)
        = fun _ : ℕ => (0 : ℝ) := by
      funext n
      exact ite_eq_right hσ
    rw [hzero]
    exact tendsto_const_nhds

/-- **The `θ`-step, with `D_z` outermost** (`j = 0`, `i ≤ 1`): the analogue of `measurable_zstep`
in the angular direction, with the coefficient `sin (2θ)` and the shift `(π/2-θ)/(2(n+1))`, which
keeps the sample points inside the open quadrant.  Only this case of the `θ`-step is used, so no
commutation of `D_z` with `D_θ` is required. -/
private theorem measurable_thetastep_zero {S : ℝ} {H : ℝ → ℝ → ℝ → ℝ} {i : ℕ} (hi : i ≤ 1)
    (hCd : ∀ σ ∈ Set.Ioc (0 : ℝ) S,
      ContDiffOn ℝ 2 (Function.uncurry (H σ)) Work.FTS.EllipticEst.Q0)
    (ih : ∀ a b : ℝ, (a, b) ∈ Work.FTS.EllipticEst.Q0 →
      Measurable (fun σ : ℝ => if σ ∈ Set.Ioc (0 : ℝ) S then
        Work.Spaces.mixed 0 i (H σ) a b else 0)) :
    ∀ a b : ℝ, (a, b) ∈ Work.FTS.EllipticEst.Q0 →
      Measurable (fun σ : ℝ => if σ ∈ Set.Ioc (0 : ℝ) S then
        Work.Spaces.mixed 0 (i + 1) (H σ) a b else 0) := by
  intro a b hab
  obtain ⟨ha, hb0, hb1⟩ := Work.FTS.EllipticEst.mem_Q0.mp hab
  have hε : 0 < (Real.pi / 2 - b) / 2 := by linarith
  have hδmem : ∀ n : ℕ, (a, b + ((Real.pi / 2 - b) / 2) / ((n : ℝ) + 1))
      ∈ Work.FTS.EllipticEst.Q0 := by
    intro n
    have hden : (1 : ℝ) ≤ (n : ℝ) + 1 := by
      have : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg n
      linarith
    have hδpos : 0 < ((Real.pi / 2 - b) / 2) / ((n : ℝ) + 1) := div_pos hε (by linarith)
    have hle : ((Real.pi / 2 - b) / 2) / ((n : ℝ) + 1) ≤ (Real.pi / 2 - b) / 2 :=
      div_le_self (by linarith) hden
    exact Work.FTS.EllipticEst.mem_Q0.mpr ⟨ha, by linarith, by linarith⟩
  have hdiff : ∀ σ ∈ Set.Ioc (0 : ℝ) S,
      HasDerivAt (fun θ' => Work.Spaces.mixed 0 i (H σ) a θ')
        (Work.Spaces.pth (Work.Spaces.mixed 0 i (H σ)) a b) b := by
    intro σ hσ
    have hB : ContDiffOn ℝ 1 (Function.uncurry (Work.Spaces.mixed 0 i (H σ)))
        Work.FTS.EllipticEst.Q0 := contDiffOn_one_of_total_le_one (hCd σ hσ) (by omega)
    have hD : DifferentiableAt ℝ (Function.uncurry (Work.Spaces.mixed 0 i (H σ))) (a, b) :=
      (hB.differentiableOn (by norm_num)).differentiableAt
        (Work.FTS.EllipticEst.isOpen_Q0.mem_nhds hab)
    simpa [Work.Spaces.pth] using (Work.Spaces.differentiableAt_curry_right hD).hasDerivAt
  have hmeas : ∀ n : ℕ, Measurable (fun σ : ℝ => if σ ∈ Set.Ioc (0 : ℝ) S then
      Real.sin (2 * b) * ((Work.Spaces.mixed 0 i (H σ) a
        (b + ((Real.pi / 2 - b) / 2) / ((n : ℝ) + 1))
        - Work.Spaces.mixed 0 i (H σ) a b) / (((Real.pi / 2 - b) / 2) / ((n : ℝ) + 1))) else 0) := by
    intro n
    have h1 := ih a (b + ((Real.pi / 2 - b) / 2) / ((n : ℝ) + 1)) (hδmem n)
    have h2 := ih a b hab
    have heq : (fun σ : ℝ => if σ ∈ Set.Ioc (0 : ℝ) S then
        Real.sin (2 * b) * ((Work.Spaces.mixed 0 i (H σ) a
          (b + ((Real.pi / 2 - b) / 2) / ((n : ℝ) + 1))
          - Work.Spaces.mixed 0 i (H σ) a b) / (((Real.pi / 2 - b) / 2) / ((n : ℝ) + 1))) else 0)
        = fun σ : ℝ => Real.sin (2 * b) * (((if σ ∈ Set.Ioc (0 : ℝ) S then
            Work.Spaces.mixed 0 i (H σ) a (b + ((Real.pi / 2 - b) / 2) / ((n : ℝ) + 1)) else 0)
          - (if σ ∈ Set.Ioc (0 : ℝ) S then Work.Spaces.mixed 0 i (H σ) a b else 0))
            / (((Real.pi / 2 - b) / 2) / ((n : ℝ) + 1))) := by
      funext σ
      by_cases hσ : σ ∈ Set.Ioc (0 : ℝ) S <;> simp [hσ]
    rw [heq]
    exact ((h1.sub h2).div_const (((Real.pi / 2 - b) / 2) / ((n : ℝ) + 1))).const_mul
      (Real.sin (2 * b))
  refine measurable_of_tendsto_metrizable hmeas ?_
  rw [tendsto_pi_nhds]
  intro σ
  by_cases hσ : σ ∈ Set.Ioc (0 : ℝ) S
  · rw [ite_eq_left hσ]
    have hlim := tendsto_slope_seq hε (hdiff σ hσ)
    have hval : Work.Spaces.mixed 0 (i + 1) (H σ) a b
        = Real.sin (2 * b) * Work.Spaces.pth (Work.Spaces.mixed 0 i (H σ)) a b := rfl
    rw [hval]
    refine (hlim.const_mul (Real.sin (2 * b))).congr' ?_
    filter_upwards with n
    rw [ite_eq_left hσ]
  · rw [ite_eq_right hσ]
    have hzero : (fun n : ℕ => if σ ∈ Set.Ioc (0 : ℝ) S then
        Real.sin (2 * b) * ((Work.Spaces.mixed 0 i (H σ) a
          (b + ((Real.pi / 2 - b) / 2) / ((n : ℝ) + 1))
          - Work.Spaces.mixed 0 i (H σ) a b) / (((Real.pi / 2 - b) / 2) / ((n : ℝ) + 1)))
          else 0) = fun _ : ℕ => (0 : ℝ) := by
      funext n
      exact ite_eq_right hσ
    rw [hzero]
    exact tendsto_const_nhds

/-! ## The measurability of the six components -/

/-- **Measurability in `σ` of the mixed jets of `∂_τ g`.**  If every slice `gdot g σ`
(`σ ∈ (0,S]`) is `C²` on the open quadrant, then for every point `(a,b)` of the open quadrant and
every `(j,i)` with `j + i ≤ 2`, the map `σ ↦ mixed j i (gdot g σ) a b` is measurable on `(0,S]`.

The induction is over the total order, and each step keeps `D_z` outermost (see
`measurable_zstep` / `measurable_thetastep_zero`); the induction hypothesis is stated for *all*
points of the open quadrant, since the difference quotients are taken at neighbouring points. -/
private theorem measurable_mixed_gdot_quadrant {S : ℝ} {g : Work.FTS.Galerkin.Fam}
    (hCd : ∀ σ ∈ Set.Ioc (0 : ℝ) S,
      ContDiffOn ℝ 2 (Function.uncurry (Work.FTS.Galerkin.gdot g σ)) Work.FTS.EllipticEst.Q0) :
    ∀ j i : ℕ, j + i ≤ 2 → ∀ a b : ℝ, (a, b) ∈ Work.FTS.EllipticEst.Q0 →
      Measurable (fun σ : ℝ => if σ ∈ Set.Ioc (0 : ℝ) S then
        Work.Spaces.mixed j i (Work.FTS.Galerkin.gdot g σ) a b else 0) := by
  have key : ∀ n j i : ℕ, j + i = n → j + i ≤ 2 →
      ∀ a b : ℝ, (a, b) ∈ Work.FTS.EllipticEst.Q0 →
        Measurable (fun σ : ℝ => if σ ∈ Set.Ioc (0 : ℝ) S then
          Work.Spaces.mixed j i (Work.FTS.Galerkin.gdot g σ) a b else 0) := by
    intro n
    induction n using Nat.strong_induction_on with
    | h n ihn =>
      intro j i hsum h2 a b hab
      rcases Nat.eq_zero_or_pos j with hj | hj
      · subst hj
        rcases Nat.eq_zero_or_pos i with hi | hi
        · subst hi
          have heq : (fun σ : ℝ => if σ ∈ Set.Ioc (0 : ℝ) S then
                Work.Spaces.mixed 0 0 (Work.FTS.Galerkin.gdot g σ) a b else 0)
              = fun σ : ℝ => if σ ∈ Set.Ioc (0 : ℝ) S then deriv (fun s => g a b s) σ else 0 := by
            funext σ
            by_cases hσ : σ ∈ Set.Ioc (0 : ℝ) S <;> simp [hσ, Work.FTS.Galerkin.gdot]
          rw [heq]
          exact Measurable.ite measurableSet_Ioc (measurable_deriv _) measurable_const
        · obtain ⟨i', rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : i ≠ 0)
          exact measurable_thetastep_zero (by omega) hCd
            (ihn i' (by omega) 0 i' (Nat.zero_add i') (by omega)) a b hab
      · obtain ⟨j', rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : j ≠ 0)
        exact measurable_zstep (by omega) hCd
          (ihn (j' + i) (by omega) j' i rfl (by omega)) a b hab
  intro j i hji
  exact key (j + i) j i rfl hji

/-! ## Integrability on the horizon -/

/-! The bound on the jets is `abs_mixed_gdot_le_of_GdotLoc` (from the compact-box bounds of
`GdotLoc`), the a.e. strong measurability is `aestronglyMeasurable_restrict_of_ae_eq` applied to
the measurable `if`-function of `measurable_mixed_gdot_quadrant`, and the integrability on the
finite interval is `integrableOn_Ioc_of_abs_bound`. -/

/-! ## The statement -/

theorem intervalIntegrable_mixed_gdot {S α C₀ : ℝ} {Φs : Work.FTS.Galerkin.Fn}
    {E : Work.FTS.Galerkin.Fn →ₗ[ℝ] Work.FTS.Galerkin.Fn} {g : Work.FTS.Galerkin.Fam}
    (hS : 0 < S) (hα : 0 < α) (hα13 : α ≤ 1 / 3)
    (hSol : Work.FTS.FinalV2.Sol (Work.FTS.Regularity.pExp α) Φs E g)
    (hOK : Work.FTS.FinalV2.DynOK' (Work.FTS.Regularity.pExp α) C₀ Φs E g)
    (hG : Work.FTS.RegExportIface.RXT.GdotLoc S g) :
    ∀ k : Fin 6, ∀ z θ, 0 < z → 0 < θ → θ < Real.pi / 2 →
      IntervalIntegrable (fun σ => Work.Spaces.mixed (Work.FTS.RegExportIface.RXT.idx k).1
        (Work.FTS.RegExportIface.RXT.idx k).2 (Work.FTS.Galerkin.gdot g σ) z θ)
        MeasureTheory.volume 0 S := by
  intro k z θ hz hθ0 hθ1
  have hji : (Work.FTS.RegExportIface.RXT.idx k).1 + (Work.FTS.RegExportIface.RXT.idx k).2 ≤ 2 := by
    fin_cases k <;> simp [Work.FTS.RegExportIface.RXT.idx]
  have hmem : (z, θ) ∈ Work.FTS.EllipticEst.Q0 :=
    Work.FTS.EllipticEst.mem_Q0.mpr ⟨hz, hθ0, hθ1⟩
  have hit : Measurable (fun σ : ℝ => if σ ∈ Set.Ioc (0 : ℝ) S then
      Work.Spaces.mixed (Work.FTS.RegExportIface.RXT.idx k).1
        (Work.FTS.RegExportIface.RXT.idx k).2 (Work.FTS.Galerkin.gdot g σ) z θ else 0) :=
    measurable_mixed_gdot_quadrant (S := S) hG.1 _ _ hji z θ hmem
  have haesm : AEStronglyMeasurable
      (fun σ : ℝ => Work.Spaces.mixed (Work.FTS.RegExportIface.RXT.idx k).1
        (Work.FTS.RegExportIface.RXT.idx k).2 (Work.FTS.Galerkin.gdot g σ) z θ)
      (volume.restrict (Set.Ioc (0 : ℝ) S)) :=
    aestronglyMeasurable_restrict_of_ae_eq measurableSet_Ioc hit
      (fun σ hσ => by rw [ite_eq_left hσ])
  obtain ⟨C, hC0, hC⟩ := abs_mixed_gdot_le_of_GdotLoc (S := S) hG hji hz hθ0 hθ1
  exact (intervalIntegrable_iff_integrableOn_Ioc_of_le hS.le).mpr
    (integrableOn_Ioc_of_abs_bound hC0 haesm hC)

end Work.FTS_RegExport.RXT.Sys
