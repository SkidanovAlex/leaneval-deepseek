/-
# The exact-height band of the model input `mdlF`

`mdlF ρ u l f = Π_{l,≤-u} f = piExact (kmtPj ρ) l (-(u:ℤ)) f` is the exact-height Ionescu–Wainger
shell of `f` at height `l` and window `2^{-u}`.  This module proves that it is square summable and
band-limited to the union of the arcs of radius `2^{-u}` around the *exact-height* frequencies
`diffFreqs ρ l = (ℚ/ℤ)_{≤l} \ (ℚ/ℤ)_{≤l-1}` (with `diffFreqs ρ 0 = (ℚ/ℤ)_{≤0}`).

This is the "exact-height" band statement of the adelic-packet programme
(`NOTES_A6Clean_AdelicForm_SESSION.md` §3.3): the packets of the model slice have to be minor arc
because their `ZMod Q`-spectrum sits at the *exact* height `l`, which needs the input's band to be
the union of the arcs around `diffFreqs ρ l`.

## The proof

It is the symbol computation `piExact_eq_multiplier`/`piSym` of `A6/besselG.lean`:

* `piExact (kmtPj ρ) l c (⇑F) = ⇑(multiplierOf (piSym ρ l c) _ F)` for every `F ∈ ℓ²(ℤ)`, and
  `piSym ρ l c = iwSymbolSet (pieceFreqs ρ l) (etSym c)` with `pieceFreqs = diffFreqs` and
  `etSym c = periodize (etaCut kmtEta c)` (definitionally);
* `𝓕(T_m F) = m · 𝓕F`, so the Fourier transform of `mdlF ρ u l f` is that of `f` multiplied by
  the symbol; the symbol vanishes off the union of the arcs because every non-zero summand
  `periodize (etaCut kmtEta (-(u:ℤ))) (ξ - α)` exhibits `ξ - α ∈ arcSet 0 (2^{-u})`
  (`supportedInArc_periodize_etaCut` plus `realArc k ⊆ [-2^k, 2^k]`);
* so the transform vanishes off the union and `HasFreqSupport` follows.

Note that no boundedness of `f` is needed: the whole computation is done on the `L²` side through
`multiplierOf` (unlike `FpieceEqTm_of_bounded`, which needs the convolution form).
-/
import Mathlib
import Submission.Work.KMTPlan.A6.MdlAdelicPackets

-- v4.35 port: restore the v4.34 instance-unification behaviour (respectTransparency) in this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

namespace Work.KMTPlan.A6Clean

open MeasureTheory
open scoped BigOperators ENNReal

/-- The two names of the exact-height arithmetic frequency set agree definitionally:
`pieceFreqs ρ l` (`KMTPlan/A6/besselG.lean`) is `diffFreqs ρ l` (`KMTAreas/A7/ModelOps.lean`). -/
theorem pieceFreqs_eq_diffFreqs (ρ : ℝ) (l : ℕ) :
    Work.KMTPlan.A6.pieceFreqs ρ l = Work.KMTAreas.A7.diffFreqs ρ l := rfl

theorem mdlF_hasFreqSupport_exact (ρ : ℝ) (hρ : 0 < ρ) (hρ1 : ρ ≤ 1) (u l : ℕ) (f : ℤ → ℂ)
    (hf : Memℓp f 2) :
    ∃ hw : Memℓp (Work.KMTPlan.A6.mdlF ρ u l f) 2,
      Work.BourgainPlan.IonescuWainger.HasFreqSupport (Work.KMTPlan.A6.mdlF ρ u l f) hw
        (⋃ α ∈ Work.KMTAreas.A7.diffFreqs ρ l,
          Work.BourgainPlan.IonescuWainger.arcSet α ((2 : ℝ) ^ (-(u : ℝ)))) := by
  -- the two normalisations of the arc radius `2^{-u}` (integer and real exponent)
  have hδ : (2 : ℝ) ^ (-(u : ℤ)) = (2 : ℝ) ^ (-(u : ℝ)) := by
    rw [show (-(u : ℝ)) = ((-(u : ℤ) : ℤ) : ℝ) by simp]
    exact (Real.rpow_intCast (2 : ℝ) (-(u : ℤ))).symm
  set F : Work.Analysis.IonescuWainger.L2Z := ⟨f, hf⟩ with hF
  -- the exact-height projection is the Fourier multiplier with symbol `piSym ρ l (-(u:ℤ))`
  set F' : Work.Analysis.IonescuWainger.L2Z :=
    Work.Analysis.IonescuWainger.multiplierOf (Work.KMTPlan.A6.piSym ρ l (-(u : ℤ)))
      (Work.KMTPlan.A6.memLp_piSym ρ l (-(u : ℤ))) F with hF'
  have hmdl : Work.KMTPlan.A6.mdlF ρ u l f = ⇑F' := by
    simp only [Work.KMTPlan.A6.mdlF]
    exact Work.KMTPlan.A6.piExact_eq_multiplier ρ hρ hρ1 l (-(u : ℤ)) F
  have hw : Memℓp (Work.KMTPlan.A6.mdlF ρ u l f) 2 := hmdl ▸ F'.2
  refine ⟨hw, ?_⟩
  -- the Fourier transform of the multiplier is the symbol times that of the input
  have hft : Work.Analysis.IonescuWainger.fourierZ F'
      = (Work.KMTPlan.A6.memLp_piSym ρ l (-(u : ℤ))).toLp
          (Work.KMTPlan.A6.piSym ρ l (-(u : ℤ))) •
            Work.BourgainPlan.IonescuWainger.ftLp f hf := by
    rw [hF']
    exact Work.Analysis.IonescuWainger.fourierZ_multiplierOf _ _ _
  simp only [Work.BourgainPlan.IonescuWainger.HasFreqSupport]
  rw [show Work.BourgainPlan.IonescuWainger.ftLp (Work.KMTPlan.A6.mdlF ρ u l f) hw
      = Work.BourgainPlan.IonescuWainger.ftLp (⇑F') F'.2 from
    Work.BourgainPlan.IonescuWainger.ftLp_congr hmdl hw F'.2]
  filter_upwards [MeasureTheory.Lp.ext_iff.mp hft,
    MeasureTheory.Lp.coeFn_lpSMul (p := ⊤) (q := 2) (r := 2)
      ((Work.KMTPlan.A6.memLp_piSym ρ l (-(u : ℤ))).toLp
        (Work.KMTPlan.A6.piSym ρ l (-(u : ℤ)))) (Work.BourgainPlan.IonescuWainger.ftLp f hf),
    MeasureTheory.MemLp.coeFn_toLp (Work.KMTPlan.A6.memLp_piSym ρ l (-(u : ℤ)))]
      with ξ hftξ hsmul hσeq hξ
  change (Work.Analysis.IonescuWainger.fourierZ F' :
    Work.Analysis.IonescuWainger.Circle → ℂ) ξ = 0
  rw [hftξ, hsmul]
  change ⇑((Work.KMTPlan.A6.memLp_piSym ρ l (-(u : ℤ))).toLp
      (Work.KMTPlan.A6.piSym ρ l (-(u : ℤ)))) ξ •
    (Work.BourgainPlan.IonescuWainger.ftLp f hf : Work.Analysis.IonescuWainger.Circle → ℂ) ξ = 0
  -- the symbol vanishes off the union of the arcs around the exact-height frequencies
  have hzero : Work.KMTPlan.A6.piSym ρ l (-(u : ℤ)) ξ = 0 := by
    simp only [Work.KMTPlan.A6.piSym, Work.KMTPlan.A6.etSym]
    refine Work.KMTAreas.A7.iwSymbolSet_eq_zero_of_forall_not_mem_arcSet
      (Work.KMTPlan.A6.pieceFreqs ρ l)
      (Work.Analysis.IonescuWainger.etaCut Work.KMTContract.kmtEta (-(u : ℤ)))
      ((2 : ℝ) ^ (-(u : ℤ))) ?_ ξ ?_
    · -- the periodised cutoff is supported in the arc `arcSet 0 (2^{-u})`
      intro θ hθ
      obtain ⟨t, ht, hte⟩ := Work.KMTPlan.A6.supportedInArc_periodize_etaCut (-(u : ℤ)) θ hθ
      refine ⟨t, ?_, ?_⟩
      · simp only [Work.Analysis.IonescuWainger.realArc, Set.mem_Icc] at ht
        exact abs_le.mpr ht
      · simpa using hte.symm
    · -- `ξ` avoids every arc of the union
      intro α hα hmem
      exact hξ (by
        simp only [Set.mem_iUnion]
        exact ⟨α, pieceFreqs_eq_diffFreqs ρ l ▸ hα, hδ ▸ hmem⟩)
  rw [hσeq, hzero, zero_smul]

end Work.KMTPlan.A6Clean
