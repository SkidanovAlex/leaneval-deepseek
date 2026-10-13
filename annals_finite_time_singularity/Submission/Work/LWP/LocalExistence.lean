/-
# `Work.LWP.LocalExistence` — item 2: local well-posedness in the Lichtenstein–Gunther class

This module states and derives the consumer shape of the Lichtenstein–Gunther local
well-posedness theorem for the 3D incompressible Euler equation in the `C^{1,α}` class, against
the challenge's own solution predicate `IsLocalEulerEquationSolution` and the class
`EulerData` / `LGClass` of `Work.LWP.Defs`.

## The derivation

From the named inputs of `Work.LWP.Inputs`:

* `VorticityTransportExistence α` — the Picard iteration for the vorticity equation, producing
  `ω` and the velocity `u = biotSavart (ω(·,t))` with joint `C^{1,α}` regularity;
* `PressureReconstruction α` — the elliptic step producing the pressure from the vorticity
  equation;
* `BiotSavartInverse` — the Biot–Savart law in the inverse direction, used to identify the
  reconstructed velocity at time `0` with the datum `u₀`;
* `IsOddPropagates` — the propagation of the paper's odd symmetry;

and from the *data* hypotheses `EulerData α u₀` (the analytic class) and
`EulerDataBS α u₀` (the extra Biot–Savart-compatible properties of the datum, automatic for the
compactly supported vorticity of the assembly's construction), we obtain

`∃ T > 0, ∃ p u, LGClass α u₀ T p u`,

i.e. a solution in the class the main theorem asks for.

## What is proved here

`local_existence` (the derivation above) and the auxiliary locality statement
`contDiffOn_Ico_of_strips`, which converts the joint `C^1` regularity on every strip
`ℝ³ × [0,S]`, `S < T`, into the form `ContDiffOn ℝ 1 u.uncurry (univ ×ˢ Ico 0 T)` required by
`IsLocalEulerEquationSolution`.

## What is not proved here

The four inputs themselves; see `NOTES.md` for what a proof of each requires.  In particular the
Picard iteration (`VorticityTransportExistence`) and the elliptic pressure step
(`PressureReconstruction`) are the analytic core of the Lichtenstein–Gunther theory.
-/
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Mathlib.MeasureTheory.Function.L1Space.Integrable
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.LWP.Inputs

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

open FiniteTimeSingularity Set Gradient Matrix Filter Topology MeasureTheory
open scoped Topology Matrix NNReal ENNReal

set_option autoImplicit false

namespace Work.LWP

/-! ## Locality: regularity on the strips gives regularity on the half-open interval -/

/-- If a spacetime field is `C¹` on every compact time strip `ℝ³ × [0,S]`, `S < T`, then it is
`C¹` on `ℝ³ × [0,T)`.  This is the form in which the Lichtenstein–Gunther regularity feeds the
challenge's predicate `FiniteTimeSingularity.IsLocalEulerEquationSolution`. -/
theorem contDiffOn_Ico_of_strips {T : ℝ} {f : R3 × ℝ → R3}
    (h : ∀ S ∈ Ioo 0 T, ContDiffOn ℝ 1 f (univ ×ˢ Icc 0 S)) :
    ContDiffOn ℝ 1 f (univ ×ˢ Ico 0 T) := by
  intro x hx
  obtain ⟨a, t⟩ := x
  simp only [mem_prod, mem_univ, true_and] at hx
  set S : ℝ := (t + T) / 2 with hSdef
  have hST : t < S := by simp only [hSdef]; linarith [hx.2]
  have hS : S ∈ Ioo (0 : ℝ) T :=
    ⟨by simp only [hSdef]; linarith [hx.1, hx.2], by simp only [hSdef]; linarith [hx.2]⟩
  have htS : t ∈ Icc (0 : ℝ) S := ⟨hx.1, le_of_lt hST⟩
  -- the two sets agree on a neighbourhood of `(a,t)`
  have hEv : (univ ×ˢ Icc (0 : ℝ) S) =ᶠ[𝓝 ((a, t) : R3 × ℝ)] (univ ×ˢ Ico (0 : ℝ) T) := by
    have hmem : (univ ×ˢ Ioo (-1 : ℝ) S) ∈ 𝓝 ((a, t) : R3 × ℝ) := by
      rw [nhds_prod_eq, Filter.prod_mem_prod_iff]
      exact ⟨univ_mem, Ioo_mem_nhds (by linarith [hx.1]) hST⟩
    filter_upwards [hmem] with y hy
    obtain ⟨b, s⟩ := y
    simp only [mem_prod, mem_univ, true_and, mem_Icc, mem_Ico] at hy ⊢
    exact propext ⟨fun h' => ⟨h'.1, lt_of_le_of_lt h'.2 hS.2⟩,
      fun h' => ⟨h'.1, le_of_lt hy.2⟩⟩
  exact (h S hS (a, t) ⟨mem_univ _, htS⟩).congr_set hEv

/-! ## Local well-posedness -/

/-- **Local well-posedness in the Lichtenstein–Gunther class** (item 2 of the LWP area), in the
consumer shape: from the analytic inputs and the datum classes, there is a positive time `T` and
a solution `(p,u)` of the incompressible Euler equation on `[0,T)` with data `u₀`, in the class
`LGClass α u₀ T p u` — i.e. the challenge's predicate `IsLocalEulerEquationSolution`, together
with oddness at every time and joint `C^{1,α}` regularity on every compact strip.

The proof is the reconstruction `ω ↦ u = biotSavart (ω(·,t))`:
`VorticityTransportExistence` supplies the vorticity and the joint `C^{1,α}` velocity;
`PressureReconstruction` turns the vorticity equation into the Euler equation with a pressure;
`BiotSavartInverse` identifies `u(·,0) = biotSavart (vorticity u₀) = u₀`; `IsOddPropagates`
supplies oddness. -/
theorem local_existence {α : NNReal}
    (hTrans : VorticityTransportExistence α) (hPress : PressureReconstruction α)
    (hOdd : IsOddPropagates)
    {u₀ : R3 → R3} (hdata : EulerData α u₀) (hbs : EulerDataBS α u₀)
    (hself : ∀ x, u₀ x = biotSavart (vorticity u₀) x) :
    ∃ T : ℝ, 0 < T ∧ ∃ p : R3 → ℝ → ℝ, ∃ u : R3 → ℝ → R3, LGClass α u₀ T p u := by
  classical
  obtain ⟨T, hT, ω, u, hω0, hu, _hint, _hbdd, hdivω, hvort, hdivu, hst, hve⟩ :=
    hTrans (vorticity u₀) hbs.vort_integrable hbs.vort_bounded hbs.vort_holder hbs.vort_div_free
  -- the pressure, from the vorticity equation
  obtain ⟨p, hpcd, hpeq⟩ := hPress u ω T hst hvort hdivu hve
  -- the initial condition: `u(·,0) = biotSavart (vorticity u₀) = u₀`
  have hinit : (fun x => u x 0) = u₀ := by
    funext x
    rw [hu 0 ⟨le_refl 0, hT⟩ x]
    have hω0' : (fun y => ω y 0) = vorticity u₀ := funext hω0
    rw [hω0']
    exact (hself x).symm
  -- assemble the challenge's predicate
  have hsol : IsLocalEulerEquationSolution p u₀ T u :=
    { solContDiff := contDiffOn_Ico_of_strips fun S hS => (hst S hS).1
      pressureContDiff := hpcd
      eq := hpeq
      div_free := fun t ht => hdivu t ⟨le_of_lt ht.1, ht.2⟩
      init := hinit }
  exact ⟨T, hT, p, u, ⟨hsol, hOdd u₀ T p u hdata.odd hsol, hst⟩⟩


/-! ## Restriction of a solution to a subinterval -/

/-- A Lichtenstein–Gunther solution on `[0,T)` restricts to one on `[0,T')` for `T' ≤ T`.  Used
when gluing a chain of solutions into a maximal one. -/
theorem lgClass_mono {α : NNReal} {u₀ : R3 → R3} {T T' : ℝ} {p : R3 → ℝ → ℝ}
    {u : R3 → ℝ → R3} (h : LGClass α u₀ T p u) (hT : T' ≤ T) : LGClass α u₀ T' p u := by
  refine ⟨⟨?_, ?_, ?_, ?_, ?_⟩, ?_, ?_⟩
  · exact h.sol.solContDiff.mono (Set.prod_mono Subset.rfl (Ico_subset_Ico_right hT))
  · exact h.sol.pressureContDiff.mono (Set.prod_mono Subset.rfl (Ico_subset_Ico_right hT))
  · intro x t ht
    exact h.sol.eq x t ⟨ht.1, lt_of_lt_of_le ht.2 hT⟩
  · intro t ht
    exact h.sol.div_free t ⟨ht.1, lt_of_lt_of_le ht.2 hT⟩
  · exact h.sol.init
  · intro t ht
    exact h.odd t ⟨ht.1, lt_of_lt_of_le ht.2 hT⟩
  · intro S hS
    exact h.spacetime S ⟨hS.1, lt_of_lt_of_le hS.2 hT⟩


/-- The classical route to the hypothesis `hself` of `local_existence`: the inverse Biot–Savart
law of `Work.LWP.Inputs` gives `u₀ = biotSavart (vorticity u₀)` from `C¹`, divergence-freeness,
integrability of the vorticity and decay of `u₀`. -/
theorem self_eq_biotSavart_of_inverse {α : NNReal} (hInv : BiotSavartInverse)
    {u₀ : R3 → R3} (hdata : EulerData α u₀) (hbs : EulerDataBS α u₀) :
    ∀ x, u₀ x = biotSavart (vorticity u₀) x :=
  fun x => (hInv u₀ hdata.contDiffHolder.1 (fun y => congrFun hdata.div_free y)
    hbs.vort_integrable hbs.decay x).symm

end Work.LWP
