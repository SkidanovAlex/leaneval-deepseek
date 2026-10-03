import Mathlib
import Submission.Work.KMTAreas.A7HiRep.chainPartSubAdd

namespace Work.KMTAreas.A7HiRep

open scoped ENNReal NNReal BigOperators

/-- **Additive head/tail split of the chain part.**  Splitting a sequence at level `M` into its
head (`m < M`) and tail (`M ≤ m`) splits the chain part at most additively.

This is the bookkeeping step of the reduction of `supChainsInterchange` to the *head* estimate
recorded in `NOTES_A7HiRep_supChainsInterchange_SESSION2.md`: with `M = 2^κ` from
`Work.A7HiRep.lpfLargeScaleRhoRep` (the PROVED, `l₁`-free large-scale estimate) the tail chain part
is bounded by the band square function, and the head (`n < 2^κ`, the paper's *small scales*) is the
residual. -/
theorem chainPartHeadTailSplit (r : NNReal) (hr : 1 ≤ r) (M : ℕ) (a : ℕ → ℂ) :
    Work.KMTAreas.A7Hi.chainPart r a
      ≤ Work.KMTAreas.A7Hi.chainPart r (fun m : ℕ => if m < M then a m else 0)
        + Work.KMTAreas.A7Hi.chainPart r (fun m : ℕ => if m < M then 0 else a m) := by
  refine (le_of_eq ?_).trans (chainPartSubAdd r hr
    (fun m : ℕ => if m < M then a m else 0) (fun m : ℕ => if m < M then 0 else a m))
  congr 1
  funext m
  simp only [Pi.add_apply]
  by_cases hm : m < M <;> simp [hm]

/-- **The sup-over-chains interchange for the Ionescu--Wainger low-pass walk** (`2 < p`, `2 < r`).

There are `Cρ > 0` and `C > 0`, free of the arithmetic height `l₁` and of the base level `m₀`, such
that on the good major arcs `GoodMajorArcs ρ Cρ l₁ (-(m₀:ℤ))` and for every `f ∈ ℓᵖ(ℤ)`, the
`ℓᵖ`-norm of the supremum *over all monotone chains* of the `ℓʳ`-norm of the chain jumps of the
low-pass walk `m ↦ lpf ρ l₁ m₀ m f` is at most `C` times the `ℓᵖ`-norm of the band square function
`sqFun ρ l₁ m₀ f`.

The per-chain form of this estimate (the chain fixed, the `ℓᵖ`-norm outside) is PROVED with a
constant uniform in `l`, `m₀` and the chain — `Work.KMTAreas.A7HiRep.chainValSqFunGeTwo` for
`r ≥ p.toReal`, and the same assembly from the per-block estimate
`Work.KMTAreas.A7Hi.partSum_le_partSq_of_bandSumSqRep` (uniform in `l, m₀, I`) in general — so the
content here is exactly the interchange of `eLpNorm` with the supremum over chains.  Since the walk
is unchanged by `f ↦ T_0 f` and the reverse Littlewood--Paley bridges are `l₁`-free, an equivalent
form is `‖Vʳ(walk f)‖_p ≤ C‖f‖_p` for band-limited `f`.

DEAD ROUTES (verified; full record with the explicit `φ_m` sanity family in
`NOTES_A7HiRep_supChainsInterchange_SESSION.md`): the interchange
`Work.KMTAreas.A7Hi.fkrInterchangeGen` is lossy — its right-hand side can exceed `C‖sqFun f‖_p` by
`M^{1/R-1/p} → ∞` with `R < p`, and the reverse Minkowski step needed to close it
(`ℓ²(L^p) ↪ L^p(ℓ²)`) is false for `p > 2`; the `ℓ¹` route and the truncated `(2 sup)^{1-2/r}`
interpolation lose unbounded factors; the `r = 2` endpoint is false (Jones--Wang); the
uniform-in-signs route is inapplicable because the walk's own uniform-signs bound fails by `log N`;
and the Fejér/deviation splitting cannot give a constant free of `l₁` because the twisted Fejér
kernel is positive with `ℓ¹`-mass `≈ #iwP ρ l₁`. -/
theorem supChainsInterchange (ρ : ℝ) (hρ : 0 < ρ) (hρ1 : ρ ≤ 1) (r : NNReal) (hr : 2 < r)
    (p : ENNReal) (hp : 2 < p) (hptop : p < ⊤) :
    ∃ Cρ : ℝ, 0 < Cρ ∧ ∃ C : ℝ, 0 < C ∧ ∀ (l₁ m₀ : ℕ),
      Work.Analysis.IonescuWainger.GoodMajorArcs ρ Cρ l₁ (-(m₀ : ℤ)) → ∀ f : ℤ → ℂ,
      MeasureTheory.MemLp f p MeasureTheory.Measure.count →
      MeasureTheory.eLpNorm (fun x : ℤ => ⨆ (J : ℕ) (N : ℕ → ℕ) (_ : Monotone N),
          ENNReal.ofReal ‖WithLp.toLp r (fun i : Fin J =>
            Work.KMTAreas.A7Hi.lpf ρ l₁ m₀ (N (i + 1)) f x
              - Work.KMTAreas.A7Hi.lpf ρ l₁ m₀ (N i) f x)‖)
        p MeasureTheory.Measure.count
        ≤ ENNReal.ofReal C *
            MeasureTheory.eLpNorm (Work.KMTAreas.A7Hi.sqFun ρ l₁ m₀ f) p
              MeasureTheory.Measure.count := by sorry

end Work.KMTAreas.A7HiRep
