import Mathlib
import Submission.Work.Drive.pairMeet2
import Submission.Work.Drive.even_ncard_pairMeetBdry2
import Submission.Work.Drive.transportThreeLevel
import Submission.Work.Drive.exists_pairDiff2_good_shift

/-!
# T1/T3 for the symmetric pair map, transferred to the collapse count

`Submission/Work/Drive/even_ncard_pairMeetBdry2.lean` proves the box-parity engine for the **symmetric**
pair map `Work.Drive.pairDiff2` (both chart blocks `s`-dependent), and
`Submission/Work/Drive/exists_pairDiff2_good_shift.lean` supplies its two genericity fields for the
*weighted* chart-shift family (`hreg` on a compact set and the face data).  This file does for the
symmetric map what `Work.Drive.even_colCount_add` does for the asymmetric one: it transfers the engine's
conclusion, through the chart bridge, to the **honest collapse count**

> `Even (colCount β Q V W 0 + colCount β Q V W 1)`,

so that the transport (`Work.Drive.odd_topBdryMeet_zero_iff_coreSideCount_mul`) can be run at the
*perturbed* chains — with the perturbation visible only in the interior of the collapse parameter
(the bridge is used at `s ∈ {0,1}`, where the weighted perturbation vanishes and the honest chains are
the unperturbed ones).

All declarations are `sorry`-free and rest on `propext`, `Classical.choice`, `Quot.sound`.
-/

namespace Work.Drive

open Manifold Filter
open scoped Manifold ContDiff Topology

noncomputable section

/-- **The chart bridge for the symmetric pair map.** -/
theorem colMeet_eq_pairMeetSet2_of_iff
    (E : ℝ → EuclideanSpace ℝ (Fin 2) → EuclideanSpace ℝ (Fin 4))
    (E' : ℝ → EuclideanSpace ℝ (Fin 2) → EuclideanSpace ℝ (Fin 4))
    (V' W' : EuclideanSpace ℝ (Fin 3) → EuclideanSpace ℝ (Fin 4))
    (β : ℝ → ℝ) (Q : ℂ → CappingSpace)
    (V W : EuclideanSpace ℝ (Fin 3) → CappingSpace) (s : ℝ)
    (hcol : ∀ u ∈ Submission.Drive.unitBox 1, ∀ y ∈ Submission.Drive.unitBox 2,
      (colPlane β Q s u = V y ↔ E s u = V' y))
    (hdis : ∀ u ∈ Submission.Drive.unitBox 1, ∀ z ∈ Submission.Drive.unitBox 2,
      (diskPlane Q u = W z ↔ E' s u = W' z)) :
    colMeet β Q V W s = pairMeetSet2 E E' V' W' s := by
  ext p
  simp only [colMeet, pairMeetSet2, Set.mem_ofPred_eq]
  constructor
  · rintro ⟨h1, h2, h3, hV, hW⟩
    exact ⟨h1, h2, h3, (hcol p.1 h1 p.2.1 h2).mp hV, (hdis p.1 h1 p.2.2 h3).mp hW⟩
  · rintro ⟨h1, h2, h3, hV, hW⟩
    exact ⟨h1, h2, h3, (hcol p.1 h1 p.2.1 h2).mpr hV, (hdis p.1 h1 p.2.2 h3).mpr hW⟩

/-- **T1/T3 for the collapse family, in the *symmetric* pair form.**  The engine
`even_ncard_pairMeetBdry2` (both chart blocks `s`-dependent) applied to the charted chains through the
bridge at the two endpoints gives the box-parity conclusion for the honest collapse counts. -/
theorem even_colCount_add2
    (E : ℝ → EuclideanSpace ℝ (Fin 2) → EuclideanSpace ℝ (Fin 4))
    (E' : ℝ → EuclideanSpace ℝ (Fin 2) → EuclideanSpace ℝ (Fin 4))
    (V' W' : EuclideanSpace ℝ (Fin 3) → EuclideanSpace ℝ (Fin 4))
    (β : ℝ → ℝ) (Q : ℂ → CappingSpace)
    (V W : EuclideanSpace ℝ (Fin 3) → CappingSpace)
    (hE : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (Function.uncurry E))
    (hE' : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (Function.uncurry E'))
    (hV' : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) V')
    (hW' : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) W')
    (hreg : ∀ x ∈ Submission.Drive.unitBox 8, pairDiff2 E E' V' W' x = 0 →
      Function.Surjective (fderiv ℝ (pairDiff2 E E' V' W') x))
    (hface : ∀ x ∈ Submission.Drive.unitBoxBdry 8, pairDiff2 E E' V' W' x = 0 →
      ∃ i : Fin 9, (x i = 0 ∨ x i = 1) ∧ (∀ j : Fin 9, j ≠ i → x j ∈ Set.Ioo (0 : ℝ) 1) ∧
        Function.Surjective (fun v : {v : EuclideanSpace ℝ (Fin 9) // v i = 0} =>
          fderiv ℝ (pairDiff2 E E' V' W') x v.1))
    (hseamU : ∀ (s : ℝ) (u : EuclideanSpace ℝ (Fin 2)), onSeam2 u → E s (seamInv2 u) = E s u)
    (hseamU' : ∀ (s : ℝ) (u : EuclideanSpace ℝ (Fin 2)), onSeam2 u → E' s (seamInv2 u) = E' s u)
    (hseamV : ∀ y : EuclideanSpace ℝ (Fin 3), onSeam y → V' (seamInv y) = V' y)
    (hseamW : ∀ z : EuclideanSpace ℝ (Fin 3), onSeam z → W' (seamInv z) = W' z)
    (havY : ∀ x ∈ Submission.Drive.unitBox 8, pairDiff2 E E' V' W' x = 0 →
      ftY2 x ≠ 0 ∧ ftY2 x ≠ 1)
    (havZ : ∀ x ∈ Submission.Drive.unitBox 8, pairDiff2 E E' V' W' x = 0 →
      ftZ2 x ≠ 0 ∧ ftZ2 x ≠ 1)
    (hcol : ∀ s : ℝ, (s = 0 ∨ s = 1) → ∀ u ∈ Submission.Drive.unitBox 1,
      ∀ y ∈ Submission.Drive.unitBox 2, (colPlane β Q s u = V y ↔ E s u = V' y))
    (hdis : ∀ s : ℝ, (s = 0 ∨ s = 1) → ∀ u ∈ Submission.Drive.unitBox 1,
      ∀ z ∈ Submission.Drive.unitBox 2, (diskPlane Q u = W z ↔ E' s u = W' z)) :
    Even (colCount β Q V W 0 + colCount β Q V W 1) := by
  have h := even_ncard_pairMeetBdry2 E E' V' W' hE hE' hV' hW' hreg hface
    hseamU hseamU' hseamV hseamW havY havZ
  rw [colCount, colCount,
    colMeet_eq_pairMeetSet2_of_iff E E' V' W' β Q V W 0 (hcol 0 (Or.inl rfl)) (hdis 0 (Or.inl rfl)),
    colMeet_eq_pairMeetSet2_of_iff E E' V' W' β Q V W 1 (hcol 1 (Or.inr rfl)) (hdis 1 (Or.inr rfl))]
  exact h


/-! ## The transport for the *perturbed* (weighted chart-shift) pair

`Work.Drive.exists_pairDiff2_good_shift` supplies the two genericity fields of the symmetric pair map
for the weighted chart-shift family, but only at the zeros lying in a compact `K` (the weight must not
vanish there).  The two endpoint identifications of the transport require the perturbation to be
inactive near `s = 0, 1`, so the complementary region — the two end collars — is precisely where the
Sard cannot act, and the data there must be supplied by the *base* configuration (the lead's **(G2)**:
the genericity of the design's own triple).  This file assembles the two: the Sard on `K`, the collar
data as hypotheses, and the transfer `even_colCount_add2`, giving the box-parity conclusion for the
honest collapse counts at the *perturbed* chains. -/
theorem exists_even_colCount_add2_of_shift
    (E₀ : ℝ → EuclideanSpace ℝ (Fin 2) → EuclideanSpace ℝ (Fin 4))
    (E'₀ : ℝ → EuclideanSpace ℝ (Fin 2) → EuclideanSpace ℝ (Fin 4))
    (V' W' : EuclideanSpace ℝ (Fin 3) → EuclideanSpace ℝ (Fin 4))
    (β : ℝ → ℝ) (Q : ℂ → CappingSpace)
    (V W : EuclideanSpace ℝ (Fin 3) → CappingSpace)
    (w : ℝ → ℝ) (K : Set (EuclideanSpace ℝ (Fin 9))) (hK : IsCompact K)
    (hE₀ : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (Function.uncurry E₀))
    (hE'₀ : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (Function.uncurry E'₀))
    (hV' : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) V')
    (hW' : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) W')
    (hw : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) w)
    (hwne : ∀ x ∈ K, w (Work.Drive.ftS x) ≠ 0)
    (hregOut : ∀ t : EuclideanSpace ℝ (Fin 8), ∀ x ∈ Submission.Drive.unitBox 8, x ∉ K →
      Work.Drive.pairDiff2 (fun s u => E₀ s u + w s • Work.Drive.unpackFst t)
        (fun s u => E'₀ s u + w s • Work.Drive.unpackSnd t) V' W' x = 0 →
      Function.Surjective (fderiv ℝ (Work.Drive.pairDiff2
        (fun s u => E₀ s u + w s • Work.Drive.unpackFst t)
        (fun s u => E'₀ s u + w s • Work.Drive.unpackSnd t) V' W') x))
    (hfaceOut : ∀ t : EuclideanSpace ℝ (Fin 8), ∀ x ∈ Submission.Drive.unitBox 8, x ∉ K →
      Work.Drive.pairDiff2 (fun s u => E₀ s u + w s • Work.Drive.unpackFst t)
        (fun s u => E'₀ s u + w s • Work.Drive.unpackSnd t) V' W' x = 0 →
      x ∈ Submission.Drive.unitBoxBdry 8 →
      ∃ i : Fin 9, (x i = 0 ∨ x i = 1) ∧ (∀ j : Fin 9, j ≠ i → x j ∈ Set.Ioo (0 : ℝ) 1) ∧
        Function.Surjective (fun v : {v : EuclideanSpace ℝ (Fin 9) // v i = 0} =>
          fderiv ℝ (Work.Drive.pairDiff2
            (fun s u => E₀ s u + w s • Work.Drive.unpackFst t)
            (fun s u => E'₀ s u + w s • Work.Drive.unpackSnd t) V' W') x v.1))
    (havY : ∀ t : EuclideanSpace ℝ (Fin 8), ∀ x ∈ Submission.Drive.unitBox 8,
      Work.Drive.pairDiff2 (fun s u => E₀ s u + w s • Work.Drive.unpackFst t)
        (fun s u => E'₀ s u + w s • Work.Drive.unpackSnd t) V' W' x = 0 →
      Work.Drive.ftY2 x ≠ 0 ∧ Work.Drive.ftY2 x ≠ 1)
    (havZ : ∀ t : EuclideanSpace ℝ (Fin 8), ∀ x ∈ Submission.Drive.unitBox 8,
      Work.Drive.pairDiff2 (fun s u => E₀ s u + w s • Work.Drive.unpackFst t)
        (fun s u => E'₀ s u + w s • Work.Drive.unpackSnd t) V' W' x = 0 →
      Work.Drive.ftZ2 x ≠ 0 ∧ Work.Drive.ftZ2 x ≠ 1)
    (hseamU : ∀ (s : ℝ) (u : EuclideanSpace ℝ (Fin 2)), onSeam2 u → E₀ s (seamInv2 u) = E₀ s u)
    (hseamU' : ∀ (s : ℝ) (u : EuclideanSpace ℝ (Fin 2)), onSeam2 u → E'₀ s (seamInv2 u) = E'₀ s u)
    (hseamV : ∀ y : EuclideanSpace ℝ (Fin 3), onSeam y → V' (seamInv y) = V' y)
    (hseamW : ∀ z : EuclideanSpace ℝ (Fin 3), onSeam z → W' (seamInv z) = W' z)
    (hcol : ∀ s : ℝ, (s = 0 ∨ s = 1) → ∀ u ∈ Submission.Drive.unitBox 1,
      ∀ y ∈ Submission.Drive.unitBox 2, (colPlane β Q s u = V y ↔ E₀ s u = V' y))
    (hdis : ∀ s : ℝ, (s = 0 ∨ s = 1) → ∀ u ∈ Submission.Drive.unitBox 1,
      ∀ z ∈ Submission.Drive.unitBox 2, (diskPlane Q u = W z ↔ E'₀ s u = W' z))
    (hw0 : w 0 = 0) (hw1 : w 1 = 0) (ε : ℝ) (hε : 0 < ε) :
    ∃ t : EuclideanSpace ℝ (Fin 8), ‖t‖ < ε ∧
      Even (colCount β Q V W 0 + colCount β Q V W 1) := by
  obtain ⟨t, ht, hregK, hfaceK⟩ :=
    exists_pairDiff2_good_shift E₀ E'₀ V' W' w K hK hE₀ hE'₀ hV' hW' hw hwne ε hε
  refine ⟨t, ht, ?_⟩
  have hsh0 : (fun s u => E₀ s u + w s • unpackFst t) 0 = E₀ 0 := by
    funext u; simp only [hw0, zero_smul, add_zero]
  have hsh0' : (fun s u => E'₀ s u + w s • unpackSnd t) 0 = E'₀ 0 := by
    funext u; simp only [hw0, zero_smul, add_zero]
  have hsh1 : (fun s u => E₀ s u + w s • unpackFst t) 1 = E₀ 1 := by
    funext u; simp only [hw1, zero_smul, add_zero]
  have hsh1' : (fun s u => E'₀ s u + w s • unpackSnd t) 1 = E'₀ 1 := by
    funext u; simp only [hw1, zero_smul, add_zero]
  have hseamShU : ∀ (s : ℝ) (u : EuclideanSpace ℝ (Fin 2)), onSeam2 u →
      (fun s u => E₀ s u + w s • unpackFst t) s (seamInv2 u)
        = (fun s u => E₀ s u + w s • unpackFst t) s u := by
    intro s u hu
    simp only [hseamU s u hu]
  have hseamShU' : ∀ (s : ℝ) (u : EuclideanSpace ℝ (Fin 2)), onSeam2 u →
      (fun s u => E'₀ s u + w s • unpackSnd t) s (seamInv2 u)
        = (fun s u => E'₀ s u + w s • unpackSnd t) s u := by
    intro s u hu
    simp only [hseamU' s u hu]
  have hcol' : ∀ s : ℝ, (s = 0 ∨ s = 1) → ∀ u ∈ Submission.Drive.unitBox 1,
      ∀ y ∈ Submission.Drive.unitBox 2,
      (colPlane β Q s u = V y ↔ (fun s u => E₀ s u + w s • unpackFst t) s u = V' y) := by
    intro s hs
    rcases hs with h | h
    · subst h; simpa only [hw0, zero_smul, add_zero] using hcol 0 (Or.inl rfl)
    · subst h; simpa only [hw1, zero_smul, add_zero] using hcol 1 (Or.inr rfl)
  have hdis' : ∀ s : ℝ, (s = 0 ∨ s = 1) → ∀ u ∈ Submission.Drive.unitBox 1,
      ∀ z ∈ Submission.Drive.unitBox 2,
      (diskPlane Q u = W z ↔ (fun s u => E'₀ s u + w s • unpackSnd t) s u = W' z) := by
    intro s hs
    rcases hs with h | h
    · subst h; simpa only [hw0, zero_smul, add_zero] using hdis 0 (Or.inl rfl)
    · subst h; simpa only [hw1, zero_smul, add_zero] using hdis 1 (Or.inr rfl)
  refine even_colCount_add2 (fun s u => E₀ s u + w s • unpackFst t)
    (fun s u => E'₀ s u + w s • unpackSnd t) V' W' β Q V W ?_ ?_ hV' hW' ?_ ?_
    hseamShU hseamShU' hseamV hseamW ?_ ?_ hcol' hdis'
  · have hfun : (Function.uncurry fun s u => E₀ s u + w s • unpackFst t)
        = fun p : ℝ × EuclideanSpace ℝ (Fin 2) =>
          Function.uncurry E₀ p + w p.1 • unpackFst t := rfl
    rw [hfun]
    exact (hE₀.comp (contDiff_fst.prodMk contDiff_snd)).add
      ((hw.comp contDiff_fst).smul contDiff_const)
  · have hfun : (Function.uncurry fun s u => E'₀ s u + w s • unpackSnd t)
        = fun p : ℝ × EuclideanSpace ℝ (Fin 2) =>
          Function.uncurry E'₀ p + w p.1 • unpackSnd t := rfl
    rw [hfun]
    exact (hE'₀.comp (contDiff_fst.prodMk contDiff_snd)).add
      ((hw.comp contDiff_fst).smul contDiff_const)
  · intro x hx hzero
    by_cases hxK : x ∈ K
    · exact hregK x hxK hzero
    · exact hregOut t x hx hxK hzero
  · intro x hx hzero
    by_cases hxK : x ∈ K
    · exact hfaceK x hxK hzero hx
    · exact hfaceOut t x hx.1 hxK hzero hx
  · intro x hx hzero
    exact havY t x hx hzero
  · intro x hx hzero
    exact havZ t x hx hzero

end

end Work.Drive
