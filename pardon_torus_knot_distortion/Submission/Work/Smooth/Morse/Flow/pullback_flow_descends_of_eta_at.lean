import Mathlib
import Submission.Work.Smooth.Morse.Flow.pullback_flow_descends_of_eta
import Submission.Work.Smooth.Morse.Defs

/-!
# The descent of the level along a single flow line, with a rate `δ` on the band `[a - η, b]`

This is the pointwise (single orbit) form of
`Work.Smooth.Morse.Flow.pullback_flow_descends_of_eta`:  rather than asking for a whole flow `Φ`
satisfying the ODE at every point of the parameter plane, we are given one solution
`u ↦ Φ u q` of the ODE `p' = descentField ψ g p` on the time interval `[0, T]`, starting at `q`.

The proof is the same elementary argument, but the chain rule and the monotonicity are used in
their *within-the-interval* form, since the ODE is only known on `[0, T]`:

* the level `L u = pullback ψ g (Φ u q)` has within-derivative `-descentRate ψ g (Φ u q) ≤ 0` on
  `[0, T]` (chain rule plus `Work.Smooth.Morse.fderiv_pullback_descentField`), hence it is
  *antitone* on `[0, T]`;
* if, for contradiction, `L T ≥ a`, then by antitonicity `a ≤ L T ≤ L u ≤ L 0 < b` for every
  `u ∈ [0, T]`, so `hrate` applies throughout the whole interval and
  `Convex.image_sub_le_mul_sub_of_deriv_le` gives `L T - L 0 ≤ -δ T`;
* hence `L T ≤ L 0 - δ T < b - δ T ≤ b - (b - a + η) = a - η < a`, a contradiction.
-/

open LeanEval.KnotTheory.PardonDistortion
open Set

namespace Work.Smooth.Morse.Flow

theorem pullback_flow_descends_of_eta_at (ψ : Submission.Diffeo)
    {g : LeanEval.KnotTheory.PardonDistortion.R3 → ℝ} (hg : ContDiff ℝ 1 g)
    {Φ : ℝ → ℝ × ℝ → ℝ × ℝ} {T a b δ η : ℝ} (hδ : 0 < δ) (hη : 0 < η) (hT0 : 0 ≤ T)
    (hT : (b - a + η) / δ ≤ T) {q : ℝ × ℝ} (h0 : Φ 0 q = q)
    (hflow : ∀ u ∈ Set.Icc 0 T, HasDerivWithinAt (fun s : ℝ => Φ s q)
      (Work.Smooth.Morse.descentField ψ g (Φ u q)) (Set.Icc 0 T) u)
    (hrate : ∀ u ∈ Set.Icc 0 T, Work.Smooth.Morse.pullback ψ g (Φ u q) ∈ Set.Icc (a - η) b →
      δ ≤ Work.Smooth.Morse.descentRate ψ g (Φ u q))
    (hq : Work.Smooth.Morse.pullback ψ g q < b) :
    Work.Smooth.Morse.pullback ψ g (Φ T q) < a := by
  -- the level of the moving point, as a function of time
  set L : ℝ → ℝ := fun u => Work.Smooth.Morse.pullback ψ g (Φ u q) with hL
  have hLu : ∀ u : ℝ, L u = Work.Smooth.Morse.pullback ψ g (Φ u q) := fun u => by rw [hL]
  -- the level has within-derivative `-descentRate` on `[0, T]` (chain rule)
  have hLderiv : ∀ u ∈ Set.Icc 0 T,
      HasDerivWithinAt L (-Work.Smooth.Morse.descentRate ψ g (Φ u q)) (Set.Icc 0 T) u := by
    intro u hu
    have hd : DifferentiableAt ℝ (Work.Smooth.Morse.pullback ψ g) (Φ u q) :=
      ((Work.Smooth.Morse.pullback_contDiff_one ψ hg).differentiable one_ne_zero).differentiableAt
    have hcomp := (hd.hasFDerivAt).comp_hasDerivWithinAt u (hflow u hu)
    have hv : fderiv ℝ (Work.Smooth.Morse.pullback ψ g) (Φ u q)
        (Work.Smooth.Morse.descentField ψ g (Φ u q)) =
          -Work.Smooth.Morse.descentRate ψ g (Φ u q) :=
      Work.Smooth.Morse.fderiv_pullback_descentField ψ g (Φ u q)
    rw [hv] at hcomp
    simpa only [Function.comp_def, ← hL] using hcomp
  have hLcont : ContinuousOn L (Set.Icc 0 T) :=
    fun u hu => (hLderiv u hu).continuousWithinAt
  have hLdiff : DifferentiableOn ℝ L (interior (Set.Icc 0 T)) :=
    fun u hu => ((hLderiv u (interior_subset hu)).hasDerivAt
      (mem_interior_iff_mem_nhds.mp hu)).differentiableAt.differentiableWithinAt
  -- hence the level is nonincreasing along the flow
  have hmono : AntitoneOn L (Set.Icc 0 T) :=
    antitoneOn_of_deriv_nonpos (convex_Icc (0 : ℝ) T) hLcont hLdiff (fun u hu => by
      have hder : deriv L u = -Work.Smooth.Morse.descentRate ψ g (Φ u q) :=
        ((hLderiv u (interior_subset hu)).hasDerivAt (mem_interior_iff_mem_nhds.mp hu)).deriv
      rw [hder]
      have := Work.Smooth.Morse.descentRate_nonneg ψ g (Φ u q)
      linarith)
  -- the total time required, from the hypothesis on `T`
  have hTmul : b - a + η ≤ δ * T := by
    have h := (div_le_iff₀ hδ).mp hT
    linarith
  have hL0 : L 0 = Work.Smooth.Morse.pullback ψ g q := by
    rw [hLu 0, h0]
  by_contra hcon
  push Not at hcon
  have hmemT : T ∈ Set.Icc (0 : ℝ) T := ⟨hT0, le_rfl⟩
  have hmem0 : (0 : ℝ) ∈ Set.Icc (0 : ℝ) T := ⟨le_rfl, hT0⟩
  have hLT : a ≤ L T := hcon
  -- the level decreases at rate at least `δ` on the whole interval
  have hbound : L T - L 0 ≤ (-δ) * (T - 0) := by
    refine (convex_Icc (0 : ℝ) T).image_sub_le_mul_sub_of_deriv_le hLcont hLdiff
      (C := -δ) ?_ 0 hmem0 T hmemT hT0
    intro u hu
    have hder : deriv L u = -Work.Smooth.Morse.descentRate ψ g (Φ u q) :=
      ((hLderiv u (interior_subset hu)).hasDerivAt (mem_interior_iff_mem_nhds.mp hu)).deriv
    rw [hder]
    have huI : u ∈ Set.Icc (0 : ℝ) T := interior_subset hu
    have hLTu : L T ≤ L u := hmono huI hmemT huI.2
    have hu0L : L u ≤ L 0 := hmono hmem0 huI huI.1
    have hmem : Work.Smooth.Morse.pullback ψ g (Φ u q) ∈ Set.Icc (a - η) b := by
      constructor
      · rw [← hLu u]
        exact le_trans (by linarith) hLTu
      · rw [← hLu u]
        exact le_of_lt (lt_of_le_of_lt hu0L (by rw [hL0]; exact hq))
    have := hrate u huI hmem
    linarith
  -- whence `L T < a - η < a`, contradicting `a ≤ L T`
  have hfin : L T < a := by
    have h1 : L T ≤ L 0 - δ * T := by linarith
    have h2 : L 0 - δ * T < b - δ * T := by rw [hL0]; linarith
    have h3 : b - δ * T ≤ a - η := by linarith
    linarith
  linarith

end Work.Smooth.Morse.Flow
