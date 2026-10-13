/-
# The barrier lemma of the a-priori bound (design §4 L-N5.5)

`barrier_within` is the ODE-comparison ingredient of the energy bootstrap: a function `E` which is
continuous on `[0,T]`, starts below `Y`, and whose derivative is *negative at every time at which
`E` meets the level `Y`*, never rises above `Y`.  The derivative is a *within*-derivative on
`[0,T]`, which is what the Galerkin ODE provides (`Work.FTS.Galerkin.IsSolOn`).

The proof is the first-crossing argument: `crossing_Icc` shows that the last time at which `E`
stays below `Y` before a time at which it exceeds `Y` is a genuine crossing point (`E p = Y`) in
the *interior* `(0,τ₀)`, where the within-derivative is an honest derivative; `descent_Icc` then
turns the strict negativity of the derivative at `p` into a strict decrease immediately to the
right, contradicting maximality.  This is the one-sided version of
`Work.Construction.le_of_deriv_le_of_cubic`.
-/
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Mathlib.Analysis.Normed.Order.Lattice
import Mathlib.Topology.Algebra.Module.ModuleTopology
import Submission.Work.Construction.le_of_deriv_le_of_cubic

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.Apriori

set_option autoImplicit false

/-- **One-sided descent from a strictly negative within-derivative**: if `E` has a
within-`[0,T]`-derivative `E' < 0` at an interior point `p ∈ (0,T)`, then `E` strictly decreases
just to the right of `p`. -/
theorem descent_Icc {E : ℝ → ℝ} {E' p T : ℝ} (hp : 0 < p) (hpT : p < T)
    (h : HasDerivWithinAt E E' (Set.Icc 0 T) p) (hneg : E' < 0) :
    ∃ δ > 0, ∀ y, p < y → y < p + δ → E y < E p :=
  Work.Construction.barrier_exists_right_lt_of_hasDerivAt_neg
    (h.hasDerivAt (Icc_mem_nhds hp hpT)) hneg

/-- **The first-crossing point**: if `E` is continuous on `[0,T]`, `E 0 < Y` and `Y < E τ₀` for
some `τ₀ ∈ [0,T]`, then the last time `p` at which `E ≤ Y` before `τ₀` satisfies `0 < p < τ₀` and
`E p = Y`. -/
theorem crossing_Icc {E : ℝ → ℝ} {Y T τ₀ : ℝ} (hcont : ContinuousOn E (Set.Icc 0 T))
    (h0 : E 0 < Y) (hτ₀ : τ₀ ∈ Set.Icc 0 T) (hgt : Y < E τ₀) :
    0 < sSup (Set.Icc 0 τ₀ ∩ E ⁻¹' Set.Iic Y) ∧
      sSup (Set.Icc 0 τ₀ ∩ E ⁻¹' Set.Iic Y) < τ₀ ∧
      E (sSup (Set.Icc 0 τ₀ ∩ E ⁻¹' Set.Iic Y)) = Y := by
  set S : Set ℝ := Set.Icc 0 τ₀ ∩ E ⁻¹' Set.Iic Y with hSdef
  have hcont' : ContinuousOn E (Set.Icc 0 τ₀) :=
    hcont.mono (Set.Icc_subset_Icc le_rfl hτ₀.2)
  have hSne : S.Nonempty := ⟨0, ⟨⟨le_refl 0, hτ₀.1⟩, le_of_lt h0⟩⟩
  have hSbdd : BddAbove S := ⟨τ₀, fun x hx => hx.1.2⟩
  have hScl : IsClosed S := hcont'.preimage_isClosed_of_isClosed isClosed_Icc isClosed_Iic
  have htmem : sSup S ∈ S := hScl.csSup_mem hSne hSbdd
  have ht0 : 0 ≤ sSup S := htmem.1.1
  have htle : sSup S ≤ τ₀ := htmem.1.2
  have htlt : sSup S < τ₀ := by
    rcases lt_or_eq_of_le htle with h | h
    · exact h
    · exfalso
      have : τ₀ ∈ S := h ▸ htmem
      exact absurd this.2 (not_le.mpr hgt)
  have htY : E (sSup S) = Y := by
    refine le_antisymm htmem.2 ?_
    by_contra hlt
    have hlt' : E (sSup S) < Y := not_le.mp hlt
    have hev : {z : ℝ | E z < Y} ∈ 𝓝[Set.Icc 0 τ₀] (sSup S) :=
      (hcont'.continuousWithinAt htmem.1).preimage_mem_nhdsWithin (isOpen_Iio.mem_nhds hlt')
    have hev' : {x : ℝ | x ∈ Set.Icc 0 τ₀ → E x < Y} ∈ 𝓝 (sSup S) :=
      Filter.mem_inf_principal.mp hev
    obtain ⟨ε, hε, hball⟩ := Metric.mem_nhds_iff.mp hev'
    have hfind : ∃ z ∈ Set.Ioc (sSup S) τ₀, E z < Y := by
      have hzgt : sSup S < sSup S + min ε (τ₀ - sSup S) / 2 := by
        linarith [lt_min hε (sub_pos.mpr htlt)]
      have hzlt : sSup S + min ε (τ₀ - sSup S) / 2 ≤ τ₀ := by
        linarith [min_le_right ε (τ₀ - sSup S)]
      have hdist : dist (sSup S + min ε (τ₀ - sSup S) / 2) (sSup S) < ε := by
        rw [Real.dist_eq, abs_of_pos (sub_pos.mpr hzgt)]
        linarith [min_le_left ε (τ₀ - sSup S)]
      exact ⟨_, ⟨hzgt, hzlt⟩, hball hdist ⟨le_trans ht0 hzgt.le, hzlt⟩⟩
    obtain ⟨z, hz, hzY⟩ := hfind
    have hzS : z ∈ S := ⟨⟨le_trans ht0 (le_of_lt hz.1), hz.2⟩, le_of_lt hzY⟩
    have hle := le_csSup hSbdd hzS
    linarith [hz.1]
  refine ⟨?_, htlt, htY⟩
  rcases lt_or_eq_of_le ht0 with h | h
  · exact h
  · exfalso
    have : E 0 = Y := by rw [h]; exact htY
    linarith

/-- **The barrier lemma** (design §4 L-N5.5).  Let `E` be continuous on `[0,T]` with
`E 0 < Y`, and suppose that at every `τ ∈ [0,T)` at which `E τ = Y` the within-`[0,T]`-derivative
`E' τ` is strictly negative.  Then `E τ ≤ Y` for every `τ ∈ [0,T]`. -/
theorem barrier_within {E E' : ℝ → ℝ} {Y T : ℝ}
    (hcont : ContinuousOn E (Set.Icc 0 T)) (h0 : E 0 < Y)
    (hderiv : ∀ τ ∈ Set.Ico 0 T, HasDerivWithinAt E (E' τ) (Set.Icc 0 T) τ)
    (hneg : ∀ τ ∈ Set.Ico 0 T, E τ = Y → E' τ < 0) :
    ∀ τ ∈ Set.Icc 0 T, E τ ≤ Y := by
  by_contra hcon
  push_neg at hcon
  obtain ⟨τ₀, hτ₀, hgt⟩ := hcon
  obtain ⟨hp0, hplt, hpY⟩ := crossing_Icc hcont h0 hτ₀ hgt
  have hpT : sSup (Set.Icc 0 τ₀ ∩ E ⁻¹' Set.Iic Y) < T := lt_of_lt_of_le hplt hτ₀.2
  have hmem : sSup (Set.Icc 0 τ₀ ∩ E ⁻¹' Set.Iic Y) ∈ Set.Ico 0 T := ⟨hp0.le, hpT⟩
  obtain ⟨δ, hδpos, hδ⟩ := descent_Icc hp0 hpT (hderiv _ hmem) (hneg _ hmem hpY)
  set z : ℝ := sSup (Set.Icc 0 τ₀ ∩ E ⁻¹' Set.Iic Y)
    + min δ (τ₀ - sSup (Set.Icc 0 τ₀ ∩ E ⁻¹' Set.Iic Y)) / 2 with hzdef
  have hzp : sSup (Set.Icc 0 τ₀ ∩ E ⁻¹' Set.Iic Y) < z := by
    rw [hzdef]
    have := lt_min hδpos (sub_pos.mpr hplt)
    linarith
  have hzτ : z < τ₀ := by
    rw [hzdef]
    have := min_le_right δ (τ₀ - sSup (Set.Icc 0 τ₀ ∩ E ⁻¹' Set.Iic Y))
    linarith
  have hzδ : z < sSup (Set.Icc 0 τ₀ ∩ E ⁻¹' Set.Iic Y) + δ := by
    rw [hzdef]
    have := min_le_left δ (τ₀ - sSup (Set.Icc 0 τ₀ ∩ E ⁻¹' Set.Iic Y))
    linarith
  have hzS : z ∈ Set.Icc 0 τ₀ ∩ E ⁻¹' Set.Iic Y := by
    refine ⟨⟨le_of_lt (lt_trans hp0 hzp), le_of_lt hzτ⟩, ?_⟩
    have hlt := hδ z hzp hzδ
    rw [hpY] at hlt
    exact le_of_lt hlt
  have hle := le_csSup ⟨τ₀, fun x hx => hx.1.2⟩ hzS
  linarith

end Work.FTS.Apriori
