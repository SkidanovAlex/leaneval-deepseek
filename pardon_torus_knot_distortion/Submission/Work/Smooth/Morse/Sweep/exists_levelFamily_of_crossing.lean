import Mathlib
import Submission.Work.Smooth.Morse.Defs
import Submission.Work.Smooth.Morse.Sweep
import Submission.Work.Smooth.Morse.Flow
import Submission.Work.Smooth.Morse.Sweep.regionEquivalent_locally_of_regularValue
import Submission.Work.Smooth.Morse.MorseModel.windingSpan_locally_const_of_span_eq
import Submission.Work.Smooth.Morse.Sweep.exists_levelFamily_of_levelData

/-!
# The level family of a smooth function, from the "crossing" local model (item 5, existence form)

`exists_levelFamily_of_levelData` builds the `Work.Smooth.Morse.LevelFamily` of a smooth function
`g` on the embedded torus once one supplies the local model `DiscModel` at every critical value.
This file proves the same existence statement from the *weakest* form of the local model which
still yields the local constancy of the winding span: at every critical value `t₀` the two regions
just below and just above `t₀` have the same winding span
(`Work.Smooth.Morse.MorseModel.windingSpan_locally_const_of_span_eq`).

This is the non-vacuous hypothesis: `DiscModel` is satisfiable only at a critical value at the
bottom of the range of `g|_F`, whereas the equality of the spans at `t₀ ± ε` is exactly the input
supplied by a family of spheres in general position.

## Main result

* `Work.Smooth.Morse.Sweep.exists_levelFamily_of_crossing` — the sublevel regions of `g`,
  reparametrised over `[0,1]`, form a `LevelFamily`.
-/

namespace Work.Smooth.Morse.Sweep

open LeanEval.KnotTheory.PardonDistortion
open Set

noncomputable section

/-! ## The nondegenerate level interval -/

/-- The construction for `a < b`, with the local model at the critical values stated as the
equality of the winding spans at `t₀ ± ε`.

Apart from the treatment of the exceptional parameters this is verbatim the construction of
`Work.Smooth.Morse.Sweep.exists_levelFamily_of_levelData_of_lt`: the level is reparametrised by
`levelParam a b`, the exceptional parameters are the finitely many `t ∈ [0,1]` whose level is a
critical value (`finite_critParams`), and the region is locally constant in loop content away from
them (`regionEquivalent_locally_of_regularValue`, via `RegularEquivalent`). -/
theorem exists_levelFamily_of_crossing_of_lt (ψ : Submission.Diffeo) {g : R3 → ℝ}
    (hg : ContDiff ℝ (⊤ : ℕ∞) g) (hcrit : LocallyFiniteCriticalValues ψ g)
    (hcross : ∀ t₀ ∈ criticalValues ψ g, ∃ ε : ℝ, 0 < ε ∧
      Work.SurgeryInvariance.WindingSpan (torus ψ) (region ψ g (t₀ - ε)) =
        Work.SurgeryInvariance.WindingSpan (torus ψ) (region ψ g (t₀ + ε)))
    {a b : ℝ} (hab : a < b) :
    ∃ S : LevelFamily (torus ψ), S.region 0 = region ψ g a ∧ S.region 1 = region ψ g b := by
  classical
  have hreg : RegularEquivalent ψ g := Work.Smooth.Morse.regularEquivalent_of_contDiff ψ hg
  have hba : 0 < b - a := sub_pos.mpr hab
  have hfin : (critParams ψ g a b).Finite := finite_critParams ψ hcrit hab
  let exc : Finset ℝ := hfin.toFinset
  have hmem_exc : ∀ t : ℝ, t ∈ exc ↔ t ∈ critParams ψ g a b := fun t => hfin.mem_toFinset
  refine ⟨{ region := fun t => region ψ g (levelParam a b t)
            exc := exc
            regular := ?_
            crossing := ?_ }, ?_, ?_⟩
  · -- the local model at a non-exceptional parameter
    intro t ht
    rcases lt_or_ge t 0 with ht0 | ht0
    · -- `t < 0`: the reparametrisation is constant near `t`
      refine ⟨-t / 2, by linarith, ?_, ?_⟩
      · intro s hs
        intro hsc
        have hs' : s < 0 := by
          have h := abs_lt.mp hs
          linarith [h.2, ht0]
        exact absurd ((hmem_exc s).mp hsc).1.1 (not_le.mpr hs')
      · intro s hs
        have hs' : s < 0 := by
          have h := abs_lt.mp hs
          linarith [h.2, ht0]
        rw [levelParam_eq_of_nonpos (le_of_lt hs'), levelParam_eq_of_nonpos (le_of_lt ht0)]
        exact Work.SurgeryInvariance.RegionEquivalent.refl _
    · rcases lt_or_ge (1 : ℝ) t with ht1 | ht1
      · -- `1 < t`: the reparametrisation is constant near `t`
        refine ⟨(t - 1) / 2, by linarith, ?_, ?_⟩
        · intro s hs
          intro hsc
          have hs' : 1 < s := by
            have h := abs_lt.mp hs
            linarith [h.1, ht1]
          exact absurd ((hmem_exc s).mp hsc).1.2 (not_le.mpr hs')
        · intro s hs
          have hs' : 1 < s := by
            have h := abs_lt.mp hs
            linarith [h.1, ht1]
          rw [levelParam_eq_of_one_le (le_of_lt hs'), levelParam_eq_of_one_le (le_of_lt ht1)]
          exact Work.SurgeryInvariance.RegionEquivalent.refl _
      · -- `0 ≤ t ≤ 1` and `t ∉ exc`, so the level `levelParam a b t` is a regular value
        have htI : t ∈ Set.Icc (0 : ℝ) 1 := ⟨ht0, ht1⟩
        have hlev : levelParam a b t ∉ criticalValues ψ g :=
          fun hc => ht ((hmem_exc t).mpr ⟨htI, hc⟩)
        obtain ⟨δ, hδpos, hδ⟩ := exists_notMem_criticalValues_near ψ hcrit hlev
        have hden : 0 < 2 * (b - a + 1) := by linarith
        have hbound : ∀ s : ℝ, |s - t| < δ / (2 * (b - a + 1)) →
            |levelParam a b s - levelParam a b t| < δ := by
          intro s hs
          calc |levelParam a b s - levelParam a b t|
              ≤ (b - a) * |s - t| := abs_levelParam_sub_le (le_of_lt hab) s t
            _ < (b - a) * (δ / (2 * (b - a + 1))) := mul_lt_mul_of_pos_left hs hba
            _ < δ := mul_div_two_mul_lt hba hδpos
        refine ⟨δ / (2 * (b - a + 1)), div_pos hδpos hden, ?_, ?_⟩
        · intro s hs
          intro hsc
          have hsmem := (hmem_exc s).mp hsc
          exact hδ (levelParam a b s) (hbound s hs) hsmem.2
        · intro s hs
          have hclose := hbound s hs
          have hI : ∀ u ∈ Set.Icc (levelParam a b t) (levelParam a b s),
              IsRegularValue ψ g u := by
            intro u hu
            rw [Set.mem_Icc] at hu
            refine hδ u ?_
            rw [abs_lt]
            exact ⟨by linarith [hδpos], by linarith [hu.2, (abs_lt.mp hclose).2]⟩
          rcases le_total (levelParam a b t) (levelParam a b s) with hle | hle
          · exact hreg _ _ hle hI
          · have hI' : ∀ u ∈ Set.Icc (levelParam a b s) (levelParam a b t),
                IsRegularValue ψ g u := by
              intro u hu
              rw [Set.mem_Icc] at hu
              refine hδ u ?_
              rw [abs_lt]
              exact ⟨by linarith [hu.1, (abs_lt.mp hclose).1], by linarith [hδpos]⟩
            exact (hreg _ _ hle hI').symm
  · -- the local model at an exceptional parameter: the winding span is locally constant
    intro t ht
    have hlevel : levelParam a b t ∈ criticalValues ψ g := ((hmem_exc t).mp ht).2
    obtain ⟨ε₁, hε₁pos, hε₁⟩ :=
      Work.Smooth.Morse.MorseModel.windingSpan_locally_const_of_span_eq ψ (hcross _ hlevel)
    have hden : 0 < 2 * (b - a + 1) := by linarith
    refine ⟨ε₁ / (2 * (b - a + 1)), div_pos hε₁pos hden, fun s hs => ?_⟩
    have hbnd : |levelParam a b s - levelParam a b t| < ε₁ := by
      calc |levelParam a b s - levelParam a b t|
          ≤ (b - a) * |s - t| := abs_levelParam_sub_le (le_of_lt hab) s t
        _ < (b - a) * (ε₁ / (2 * (b - a + 1))) := mul_lt_mul_of_pos_left hs hba
        _ < ε₁ := mul_div_two_mul_lt hba hε₁pos
    exact hε₁ (levelParam a b s) hbnd
  · simp
  · simp

/-! ## The degenerate level interval -/

/-- The construction when `a = b`: the constant family. -/
theorem exists_levelFamily_of_crossing_of_eq (ψ : Submission.Diffeo) {g : R3 → ℝ} {a b : ℝ}
    (hab : a = b) :
    ∃ S : LevelFamily (torus ψ), S.region 0 = region ψ g a ∧ S.region 1 = region ψ g b := by
  subst hab
  refine ⟨{ region := fun _ => region ψ g a
            exc := ∅
            regular := ?_
            crossing := ?_ }, rfl, rfl⟩
  · intro t _
    exact ⟨1, one_pos, by simp, fun s _ => Work.SurgeryInvariance.RegionEquivalent.refl _⟩
  · intro t ht
    exact absurd ht (by simp)

/-! ## The existence of the level family -/

/-- **Item 5, existence form, with the satisfiable local model at the critical values.**

The sublevel regions `A t = F ∩ {g < t}` of a `C^∞` function `g` on the embedded torus
`F = ψ(standard torus)`, reparametrised over the unit interval by the clamped affine map
`levelParam a b`, form a `Work.Smooth.Morse.LevelFamily`: away from the finitely many exceptional
parameters the region is locally constant in loop content (`RegularEquivalent`, item 3, proved from
the normalised gradient flow), and at an exceptional parameter the local model is the equality of
the winding spans of the two regions immediately below and above the critical level, which forces
the span to be locally constant there
(`Work.Smooth.Morse.MorseModel.windingSpan_locally_const_of_span_eq`). -/
theorem exists_levelFamily_of_crossing (ψ : Submission.Diffeo) {g : LeanEval.KnotTheory.PardonDistortion.R3 → ℝ} (hg : ContDiff ℝ (⊤ : ℕ∞) g) (hcrit : Work.Smooth.Morse.LocallyFiniteCriticalValues ψ g) (hcross : ∀ t₀ ∈ Work.Smooth.Morse.criticalValues ψ g, ∃ ε : ℝ, 0 < ε ∧ Work.SurgeryInvariance.WindingSpan (Work.Smooth.Morse.torus ψ) (Work.Smooth.Morse.region ψ g (t₀ - ε)) = Work.SurgeryInvariance.WindingSpan (Work.Smooth.Morse.torus ψ) (Work.Smooth.Morse.region ψ g (t₀ + ε))) (a b : ℝ) (hab : a ≤ b) : ∃ S : Work.Smooth.Morse.LevelFamily (Work.Smooth.Morse.torus ψ), S.region 0 = Work.Smooth.Morse.region ψ g a ∧ S.region 1 = Work.Smooth.Morse.region ψ g b := by
  rcases lt_or_eq_of_le hab with hlt | heq
  · exact exists_levelFamily_of_crossing_of_lt ψ hg hcrit hcross hlt
  · exact exists_levelFamily_of_crossing_of_eq ψ heq

end

end Work.Smooth.Morse.Sweep
