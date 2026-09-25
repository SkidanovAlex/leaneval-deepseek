import Mathlib
import Submission.Work.CR.Flat.Holder

noncomputable section

open scoped NNReal ENNReal
open Set Filter Metric

namespace Work.NN.Final

/-- A function satisfying a Hölder bound of exponent `α > 0` on a set is uniformly continuous
there.  (The bound is stated with `dist` and a real constant `C ≥ 0`, matching the way the
`C^{k,α}` norm controls the iterated derivatives.) -/
lemma uniformContinuousOn_of_holder {X Y : Type*} [PseudoMetricSpace X] [PseudoMetricSpace Y]
    {f : X → Y} {s : Set X} {α : ℝ} (hα : 0 < α) {C : ℝ} (hC : 0 ≤ C)
    (h : ∀ x ∈ s, ∀ y ∈ s, dist (f x) (f y) ≤ C * dist x y ^ α) :
    UniformContinuousOn f s := by
  rw [Metric.uniformContinuousOn_iff]
  intro ε hε
  have hC1 : 0 < C + 1 := by linarith
  refine ⟨(ε / (C + 1)) ^ (1 / α), ?_, ?_⟩
  · exact Real.rpow_pos_of_pos (by positivity) _
  · intro x hx y hy hxy
    rcases eq_or_lt_of_le hC with hC0 | hCpos
    · have hb := h x hx y hy
      rw [← hC0, zero_mul] at hb
      exact lt_of_le_of_lt hb hε
    · have hd0 : 0 ≤ dist x y := dist_nonneg
      have hpow : dist x y ^ α < ε / (C + 1) := by
        have h1 : dist x y ^ α < ((ε / (C + 1)) ^ (1 / α)) ^ α :=
          Real.rpow_lt_rpow hd0 hxy hα
        rwa [← Real.rpow_mul (by positivity) (1 / α) α, one_div_mul_cancel hα.ne',
          Real.rpow_one] at h1
      calc dist (f x) (f y) ≤ C * dist x y ^ α := h x hx y hy
        _ < C * (ε / (C + 1)) := mul_lt_mul_of_pos_left hpow hCpos
        _ ≤ ε := by
              rw [← mul_div_assoc, div_le_iff₀ hC1]
              nlinarith [hε.le, hCpos.le]

/-- **One-sided continuity of the iterated derivatives.**  If `g : E × ℝ → ℂ` has finite
`C^{k,α}` norm on the half-space `W × (0,∞)` with `α > 0` and `W` open, then for every `i ≤ k`
the `i`-th iterated Fréchet derivative of `g` has a limit at the boundary point `(p, 0)`,
`p ∈ W`, as one approaches it inside `W × (0,∞)`.

The reason is that the finite Hölder seminorm at order `i` makes `x ↦ D^i g(x)`
Hölder continuous on the (open) half-space, hence uniformly continuous; a uniformly continuous
map on a set with values in a complete space has a limit at every point of the closure of the
set, and `(p, 0)` lies in the closure of `W × (0,∞)`. -/
theorem holderDerivTendsto {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {α : ℝ} (hα : 0 < α) {k : ℕ} {W : Set E} (hW : IsOpen W) (g : E × ℝ → ℂ)
    (hfin : Work.CR.Flat.holderNorm k α g (Set.prod W {t : ℝ | 0 < t}) ≠ ⊤)
    {i : ℕ} (hi : i ≤ k) {p : E} (hp : p ∈ W) :
    ∃ L : ContinuousMultilinearMap ℝ (fun _ : Fin i => E × ℝ) ℂ,
      Filter.Tendsto (fun x : E × ℝ => iteratedFDeriv ℝ i g x)
        (nhdsWithin (p, (0 : ℝ)) (Set.prod W {t : ℝ | 0 < t})) (nhds L) := by
  set Ω : Set (E × ℝ) := Set.prod W {t : ℝ | 0 < t} with hΩ
  have hΩopen : IsOpen Ω := by rw [hΩ]; exact hW.prod isOpen_Ioi
  -- `(p, 0)` lies in the closure of the half-space
  have hmem0 : (0 : ℝ) ∈ closure {t : ℝ | 0 < t} := by
    rw [show {t : ℝ | 0 < t} = Set.Ioi (0 : ℝ) from rfl, closure_Ioi]
    exact Set.mem_Ici.mpr le_rfl
  have hmem : (p, (0 : ℝ)) ∈ closure Ω := by
    rw [hΩ]
    show (p, (0 : ℝ)) ∈ closure (W ×ˢ {t : ℝ | 0 < t})
    rw [closure_prod_eq]
    exact ⟨subset_closure hp, hmem0⟩
  have hCne : Work.CR.Flat.holderNorm k α g Ω ≠ ⊤ := by
    rw [hΩ]; exact hfin
  set C : ℝ := (Work.CR.Flat.holderNorm k α g Ω).toReal with hCdef
  have hC0 : 0 ≤ C := by rw [hCdef]; exact ENNReal.toReal_nonneg
  -- the iterated derivatives are Hölder on `Ω`
  have hholder : ∀ x ∈ Ω, ∀ y ∈ Ω,
      dist (iteratedFDeriv ℝ i g x) (iteratedFDeriv ℝ i g y) ≤ C * dist x y ^ α := by
    intro x hx y hy
    by_cases hxy : x = y
    · subst hxy
      simp [dist_self, Real.zero_rpow hα.ne']
    · have hxd : iteratedFDerivWithin ℝ i g Ω x = iteratedFDeriv ℝ i g x :=
        iteratedFDerivWithin_of_isOpen (𝕜 := ℝ) (s := Ω) i hΩopen hx
      have hyd : iteratedFDerivWithin ℝ i g Ω y = iteratedFDeriv ℝ i g y :=
        iteratedFDerivWithin_of_isOpen (𝕜 := ℝ) (s := Ω) i hΩopen hy
      have hsemi := Work.CR.Flat.le_holderSeminorm i α g Ω hx hy hxy
      rw [hxd, hyd] at hsemi
      have hle : ENNReal.ofReal
          (‖iteratedFDeriv ℝ i g x - iteratedFDeriv ℝ i g y‖ / ‖x - y‖ ^ α)
          ≤ Work.CR.Flat.holderNorm k α g Ω :=
        le_trans hsemi (Work.CR.Flat.holderSeminorm_le_holderNorm k α g Ω hi)
      have hreal : ‖iteratedFDeriv ℝ i g x - iteratedFDeriv ℝ i g y‖ / ‖x - y‖ ^ α ≤ C := by
        rw [hCdef]
        exact (ENNReal.ofReal_le_iff_le_toReal hCne).mp hle
      have hpos : 0 < ‖x - y‖ ^ α :=
        Real.rpow_pos_of_pos (norm_pos_iff.mpr (sub_ne_zero.mpr hxy)) α
      rw [dist_eq_norm, dist_eq_norm]
      exact (div_le_iff₀ hpos).mp hreal
  have hunif : UniformContinuousOn (fun x : E × ℝ => iteratedFDeriv ℝ i g x) Ω :=
    uniformContinuousOn_of_holder hα hC0 hholder
  -- the half-space filter is Cauchy at `(p, 0)`, and the derivatives are uniformly continuous
  have hnb : (nhdsWithin (p, (0 : ℝ)) Ω).NeBot := mem_closure_iff_nhdsWithin_neBot.mp hmem
  have hCau : Cauchy (nhdsWithin (p, (0 : ℝ)) Ω) :=
    ⟨hnb,
      le_trans (Filter.prod_mono nhdsWithin_le_nhds nhdsWithin_le_nhds)
        (cauchy_nhds (a := (p, (0 : ℝ)))).2⟩
  have hCauMap : Cauchy (Filter.map (fun x : E × ℝ => iteratedFDeriv ℝ i g x)
      (nhdsWithin (p, (0 : ℝ)) Ω)) :=
    Cauchy.map_of_le hCau hunif (le_principal_iff.mpr self_mem_nhdsWithin)
  obtain ⟨L, hL⟩ := cauchy_map_iff_exists_tendsto.mp hCauMap
  exact ⟨L, by simpa only [hΩ] using hL⟩

end Work.NN.Final
