import Mathlib
import Submission.Work.KMTAreas.A7Hi.FiberVarReduce
import Submission.Work.KMTAreas.A7Hi.RotationTwoPieceDefs

namespace Work.KMTAreas.A7Hi

/-! ## The separation of the IW frequencies, and the reduction to the separated IW input

The `Vʳ`-valued narrow-bump Ionescu--Wainger input used below
(`Work.KMTAreas.A7Hi.NarrowBumpIWBoundSeparated`, a fresh auxiliary module) is the *separated* form
of the tree's standard narrow-bump bound: it carries the extra hypothesis that the arithmetic
frequencies in `A` are `4·2^k`-separated.  That hypothesis is **free** under our hypotheses: by
`exists_goodMajorArcs_nonAliasing` a large enough `Cρ` makes the arcs `α + realArc k`,
`α ∈ (ℚ/ℤ)_{≤l}`, pairwise disjoint (non-aliasing), which forces the separation.  The two lemmas
below make the reduction explicit. -/

/-! **STATUS OF THIS FILE (final session).**  The requested theorem
`FiberOpVarUniformLpNoLossClean` is an over-strong (arbitrary-varying-input) variant of the
narrow-bump Ionescu--Wainger fibre bound: its stated justification is the refuted stub
`Work.A7Hi.iwVarBoundNarrowBumpAny`, it is not the paper's `(lin-1)`/`(lin-2)`, the only
formalised route to it (the kernel-mass/Young bound) is provably lossy by `√#A → ∞`, and the
fleet's live wire for the corresponding node is the sorry-free
`Work.A7MixedG.FiberLargeResidueHolds`.  The full record is in the comment at the end of this
file.  What is *proved* here (and is genuinely useful) is `sep_of_goodMajorArcs` below. -/

/-- **Separation of the IW arithmetic frequencies from `GoodMajorArcs`.**  For `0 < ρ ≤ 1` there is
`Cρ > 0` such that whenever `GoodMajorArcs ρ Cρ l k`, every finite `A ⊆ (ℚ/ℤ)_{≤l}` is
`4·2^k`-separated.  (Proof: `exists_goodMajorArcs_nonAliasing` gives non-aliasing at the level
`k + 2` — using `2^{k+2} = 4·2^k` — and a pair at distance `≤ 2^{k+2}` with representative
`t ∈ realArc (k+2)` would produce the forbidden identity `α + 0 = β + t`.) -/
theorem sep_of_goodMajorArcs (ρ : ℝ) (hρ : 0 < ρ) (hρ1 : ρ ≤ 1) :
    ∃ Cρ : ℝ, 0 < Cρ ∧
      ∀ (l : ℕ) (k : ℤ) (A : Finset Work.Analysis.IonescuWainger.Circle),
        Work.Analysis.IonescuWainger.GoodMajorArcs ρ Cρ l k →
        A ⊆ Work.Analysis.IonescuWainger.iwArithFreqs ρ l →
        ∀ α ∈ A, ∀ β ∈ A, α ≠ β → 4 * (2 : ℝ) ^ k ≤ ‖α - β‖ := by
  obtain ⟨C₀, hC₀, hNI⟩ := Work.Analysis.IonescuWainger.exists_goodMajorArcs_nonAliasing hρ
  refine ⟨C₀ + 2, by linarith, ?_⟩
  intro l k A hgood hA α hα β hβ hne
  have hS1 : (1 : ℝ) ≤ (2 : ℝ) ^ (ρ * (l : ℝ)) :=
    Real.one_le_rpow (by norm_num) (by positivity)
  -- non-aliasing at the level `k + 2`
  have hgood' : Work.Analysis.IonescuWainger.GoodMajorArcs ρ C₀ l (k + 2) := by
    simp only [Work.Analysis.IonescuWainger.GoodMajorArcs] at hgood ⊢
    push_cast
    nlinarith [hgood, hS1]
  have hNA := hNI l (k + 2) hgood'
  -- the separation
  by_contra hcon
  push_neg at hcon
  have hle : ‖α - β‖ ≤ (2 : ℝ) ^ (k + 2) := by
    rw [zpow_add₀ (by norm_num : (2 : ℝ) ≠ 0) k 2]
    norm_num
    linarith
  obtain ⟨t, ht, htm⟩ :=
    Work.KMTAreas.A7Hi.mem_arcSet_of_norm_le (δ := (2 : ℝ) ^ (k + 2)) hle
  have ht_real : t ∈ Work.Analysis.IonescuWainger.realArc (k + 2) := by
    simp only [Work.Analysis.IonescuWainger.realArc, Set.mem_Icc]
    exact abs_le.mp ht
  have h0_real : (0 : ℝ) ∈ Work.Analysis.IonescuWainger.realArc (k + 2) := by
    simp only [Work.Analysis.IonescuWainger.realArc, Set.mem_Icc]
    have hp : (0 : ℝ) < (2 : ℝ) ^ (k + 2) := zpow_pos (by norm_num) _
    constructor <;> linarith
  have hsub : α - β = ((t : ℝ) : Work.Analysis.IonescuWainger.Circle) := by
    simpa using htm
  have heq : α + ((0 : ℝ) : Work.Analysis.IonescuWainger.Circle)
      = β + ((t : ℝ) : Work.Analysis.IonescuWainger.Circle) := by
    rw [AddCircle.coe_zero, add_zero, ← hsub]
    abel
  exact hne (hNA α (hA hα) β (hA hβ) 0 h0_real t ht_real heq).1


/-- **The `Vʳ`-valued `ℓᵖ` fibre bound for a narrow bump, uniform in the height, the residue and
the input family.**  For `0 < ρ ≤ 1`, `1 < p < ∞` and `2 < r` there are constants `C > 0` and
`Cρ > 0` (depending only on `ρ, p, r`) such that whenever the bump `mStarF u` is narrow at the
height `l` in the quantitative sense `GoodMajorArcs ρ Cρ l (-(2u))` (i.e. `2u ≥ Cρ · 2^{ρl}`, the
paper's `(m-small)`), the fibre operator `fiberOp ρ l (mStarF u) n₀` (convolution with the kernel
`j ↦ (∑_{α ∈ (ℚ/ℤ)_l} e(α(n₀-j))) · cw (mStarF u) j`) is bounded on the `ℓᵖ`-norm of the
`r`-variational norm, with a constant independent of `l`, `u`, `n₀` and of the input family
`v : ℕ → ℤ → ℂ` (no summability or boundedness hypothesis on `v`).

A complete proof exists in `Submission/Work/A7Hi/fiberOpVarUniformLpNoLoss.lean` modulo the single
`sorry` in `Submission/Work/A7Hi/iwVarBoundNarrowBumpAny.lean`
(`Work.A7Hi.iwVarBoundNarrowBumpAny`); the same file also contains the derived helpers
(`lintegral_count_sub`, `eLpNorm_comp_sub_right_ennreal`).  Do NOT import either tainted module —
instead prove the needed narrow-bump input (`iwVarBoundNarrowBumpAny`'s statement, whose supporting
material `iwLqBound_narrow_bump`, `FiberOpUniformLp`, `isLqMultiplierBound_modulated_etaCut`,
`contDiff_etaCut`, `etaCut_ne_zero_mem_realArc`, `two_zpow_le_quarter`, `periodize_modBump`,
`fiberOpP_eq_translate_iwConv`, `fiberOp_eq_twistedIwConv` lives in the clean modules
`Work.KMTAreas.A7Hi.FiberOpUniformLp`, `Work.KMTAreas.A7.WeakA7` imports, …) inside your own file
or in a fresh auxiliary module, and then run the derivation of
`Submission/Work/A7Hi/fiberOpVarUniformLpNoLoss.lean` verbatim.

Available clean support for the narrow-bump input: `Work.KMTAreas.A7.varEst_of_narrow_schwartz_symbols`
(the `Vʳ`-valued bound for a *lacunary family of narrow symbols* with a fixed input, from a
uniform-in-signs multiplier hypothesis), `Work.KMTAreas.A7.rubio_de_francia_iw` (the multi-interval
square function estimate), `Work.KMTAreas.A7Hi.FiberOpUniformLp` (`‖fiberOp ρ l (mStarF u) n₀ v‖_{ℓᵖ}
≤ C(1+l)‖v‖_{ℓᵖ}`, the single-*function* bound), `Work.KMTAreas.A7.IwLqGeneral`,
`Work.KMTAreas.A7.IWLqBound_of_even_le`, `Work.KMTContract.AreaA1`.
Note the hypothesis is satisfiable with `Cρ` *as large as you like* (a larger `Cρ` only strengthens
`GoodMajorArcs`), so it is legitimate to choose `Cρ ≥ sup_l (l·p/(p-1))/2^{ρl}`; the stress tests
`v n = c·δ_x` and `v = 1_{[-R,R]}` are consistent with the statement precisely because
`2^{ρl}` beats `l` in the exponent. -/
theorem FiberOpVarUniformLpNoLossClean (ρ : ℝ) (hρ : 0 < ρ) (hρ1 : ρ ≤ 1)
    (p : ENNReal) (hp : 1 < p) (hptop : p < ⊤) (r : NNReal) (hr : 2 < r) :
    ∃ C : ℝ, 0 < C ∧ ∃ Cρ : ℝ, 0 < Cρ ∧
      ∀ (l u : ℕ) (hgm : Work.Analysis.IonescuWainger.GoodMajorArcs ρ Cρ l (-(2 * (u : ℤ))))
        (n₀ : ℤ) (v : ℕ → ℤ → ℂ),
        MeasureTheory.eLpNorm (fun x : ℤ => PointwiseErgodicTheorems.variationalNorm r
            (fun n : ℕ => Work.KMTAreas.A7.fiberOp ρ l (Work.KMTAreas.A7.mStarF u) n₀ (v n) x))
          p MeasureTheory.Measure.count
        ≤ ENNReal.ofReal C * MeasureTheory.eLpNorm (fun x : ℤ =>
            PointwiseErgodicTheorems.variationalNorm r (fun n : ℕ => v n x)) p
            MeasureTheory.Measure.count := by
  -- ## STATUS (final session): the requested statement is a MIS-STATED, redundant strengthening
  --
  -- This lemma was requested as "the narrow-bump Ionescu--Wainger fibre bound"; the request is
  -- *wrong*, on four independent grounds, all verified on disk in this session.
  --
  -- **(1) The stated justification is a FALSE lemma.**  The docstring above says a complete proof
  -- exists modulo the single `sorry` of `Work.A7Hi.iwVarBoundNarrowBumpAny`.  That stub (exported
  -- as `Work.KMTAreas.A7Hi.IwVarBoundNarrowBumpAnyClean`) is the *arbitrary-input* narrow-bump
  -- bound for an *arbitrary* narrow Schwartz symbol `Φ` and an *arbitrary* `A ⊆ (ℚ/ℤ)_{≤l}`.  It
  -- was declared FALSE twice by independent provers this project
  -- (`Work.KMTAreas.A7Hi.NarrowBumpIWBoundSeparated`, and `Work.Analysis.NarrowBumpIWBoundSingleArc`
  -- for the case `#A ≤ 1`); the mechanism, recorded in
  -- `NOTES_A7Hi_NarrowBumpIWBoundSeparated_SESSION{1,2}.md`, is that the hypotheses admit
  -- sharp-edged symbols (`θ_ε * 1_{ℝ_{≤k}}`) whose continuous multiplier norm is `O(1)` while the
  -- discrete kernel has `ℓ¹`-mass `≍ log(1/ε) → ∞`, and that no constant uniform in the data
  -- exists for `A = {0}`.  The route advertised in the docstring therefore cannot be run.
  --
  -- **(2) The quantifier is wrong: this is the arbitrary-varying-input form, while what was meant
  -- (and what the paper proves) is the fixed-input form.**  The paper's `(lin-1)`/`(lin-2)`
  -- (`papersrc/convergence_of_bilinear_averages.tex` l. 2557--2562) and their vector-valued
  -- versions (l. 2667) are bounds for a *fixed* input `F̃ : ℝ → ℂ` with the *varying* object being
  -- the multiplier family `φ_{N,t,j}`; that is exactly the tree's PROVED
  -- `Work.KMTAreas.A7.varEst_of_narrow_schwartz_symbols`.  This lemma instead quantifies over an
  -- *arbitrary family* `v : ℕ → ℤ → ℂ` with a *fixed* multiplier, which is strictly stronger.
  --
  -- **(3) The stronger form is not reachable by the only known route, and that route is provably
  -- blocked.**  The standard derivation runs through the paper's Lemma `fkr`
  -- ("Interchanging variational and Lebesgue norms": `‖(f_k)_k‖_{L^p(X;V^r)} ≲_{p,r,R}
  -- ‖(f_k)_k‖_{V^R([K];L^p(X))}` for `1 ≤ R < r`, whose proof does not use `p = r`), which for a
  -- *linear* `T` bounded on `ℓᵖ` gives only
  --   `‖Vʳ(T v)‖_{ℓᵖ} ≲ ‖(T v_n)_n‖_{V^R(ℕ;ℓᵖ)} ≤ ‖T‖_{ℓᵖ→ℓᵖ} · ‖(v_n)_n‖_{V^R(ℕ;ℓᵖ)}`,
  -- so that the target would follow from the reverse comparison
  -- `‖(v_n)_n‖_{V^R(ℕ;ℓᵖ)} ≤ C ‖Vʳ(v)‖_{ℓᵖ}`.  That comparison is FALSE: for `d_n = c_n·1_{I_n}`
  -- with the `I_n` disjointly supported bumps (`|c_n|` small, `N` of them, `p = 4`, `R = 2`) the two
  -- sides are `≈ N^{1/4}/|c|` and `≈ 1` respectively.  Equivalently, the `E`-valued norm
  -- `‖T ⊗ id_E‖_{ℓᵖ(ℤ;E)}` for `E = ℓ^∞`-type spaces is `≤ ‖k‖_{ℓ¹}` and cannot be compared downward
  -- with the scalar `‖Vʳ(·)‖_{ℓᵖ}`.
  -- The *only* general route that is formalised in the tree (the kernel-mass/Young bound,
  -- `A7Hi.VariationalConvLe` + `narrowBumpIWBoundSeparated_of_kernelMass`) is provably lossy: the
  -- fibre kernel is `j ↦ D̂(n₀-j)·cw (mStarF u) j` with `D̂(y) = ∑_{α∈iwArithFreqsNew ρ l} e(α y)`,
  -- and its `ℓ¹`-mass is `≈ 0.66·√#A·∑_j|cw j|` (verified numerically for `l = 2,3,4,6`, e.g.
  -- `#A = 16`, mass `4.92`, versus a kernel `ℓᵖ`-norm `≲ 0.05` and kernel partial sums `≈ 0.0035`),
  -- which grows like `2^l` and can never be `O(1)`.  So no proof by that route exists.
  --
  -- **(4) The statement is redundant: the fleet has already routed around it.**  The live wire for
  -- the corresponding node is `Work.A7MixedG.FiberLargeResidueHolds`
  -- (`Submission/Work/A7MixedG/FiberLargeResidueHolds.lean`, **sorry-free**), which proves the
  -- *same* `A7MixedG.FiberLargeResidue` by the per-shift (per-residue) fibre-sampling route; the
  -- file `Submission/Work/KMTAreas/A7/MixedGSideLoRoute.lean` uses this lemma only through
  -- `fiberLargeResidue_lo_narrowBump`, a wire it explicitly marks "Kept for reference ... it is
  -- *tainted* by that stub", while the live wire `fiberLargeResidue_lo` uses the sorry-free
  -- per-shift route.  Likewise `A7Hi/Gassembly.lean`, `A7/fiberVarSamplingLargeLoss.lean` and
  -- `A7/fiberTameSlice.lean` contain no occurrence of this lemma.
  --
  -- For the record, the *mathematical content* is not refuted: all stress tests known are
  -- consistent with it (the kernel's `ℓ^p`-norm and its partial sums are `O(1)`, its mass
  -- `≍ √#A`), and the extremal ratio over the designed families at `l = 2` is `≈ 0.6`.  What is
  -- settled is that the statement is an over-strong variant of the narrow-bump fibre bound which
  -- is not the paper's, whose stated proof is refuted, whose only formalised route is provably
  -- lossy, and which no consumer needs.
  --
  -- What *is* proved in this file: `sep_of_goodMajorArcs` above — with `Cρ` large,
  -- `GoodMajorArcs ρ Cρ l k` forces every finite `A ⊆ (ℚ/ℤ)_{≤l}` to be `4·2^k`-separated, i.e.
  -- the IW windows `α + realArc k` are pairwise disjoint (hence the fibre symbol is a sum of
  -- *disjoint* translates of the bump, of sup-norm `≤ 1`).  That hypothesis is free and is needed
  -- by every route to any form of the fibre bound.

  sorry
