import Mathlib
import Submission.Work.Drive.ppParity.Defs
import Submission.Work.Drive.ppRegAt_zero_of_meet3Hyp
import Submission.Work.Drive.ppRegAt_one_of_pairData
import Submission.Work.Drive.ppParity.exists_delta_regular_collar
import Submission.Work.Drive.collapseTransport
import Submission.Work.Drive.clampedSweep

/-!
# The `hend` collar assembly of the transport `T6`: `PPRegAt` at the two end faces `ftS ∈ {0,1}`

`Work.Drive.ppParity.exists_delta_regular_collar` reduces the collar regularity `hregBase` of the
transport (the input of the intrinsic S4/S5 pair
`Work.Drive.exists_even_ppMeetEnd_add_intrinsic_strip`, hence of the box parity `heven`) to the **end**
regularity

> `hend : ∀ x ∈ ppMeet E E' V W, (ftS x = 0 ∨ ftS x = 1) → PPRegAt E E' V W x`.

Both *mathematical* halves of `hend` are on disk and proved:

* at `ftS x = 0` (`Drive/ppRegAt_zero_of_meet3Hyp.lean`) the two chart blocks `E 0`, `E' 0` coincide
  with the top face of the same chain `D 0`, so the pair map restricted to the `s = 0` hyperplane is
  the flat pair map of the **triple** `(D 0, D 1, D 2)`, and `Meet3Hyp` supplies its surjectivity;
* at `ftS x = 1` (`Drive/ppRegAt_one_of_pairData.lean`) the two chart blocks are the distinct plane
  presentations `E 1`, `E' 1`, and the hypothesis is the **pair** datum `hset`/`hC`/`hD` of the two
  plane derivatives against the two sweep derivatives.

What is *not* on disk is the glue: the case split, the interiority bookkeeping, and the packaging into
the exact form `exists_delta_regular_collar` consumes.  This file supplies it, both over an arbitrary
`4`-manifold `M` and, in `hregBase_design_chains`, at the concrete chains of the design's transport
`T6` (`Drive/transportT6Sharp.lean`,
`odd_topBdryMeet_zero_iff_coreSideCount_mul_of_design_intrinsic_nf`, whose `hregBase` is exactly the
output here).

The two *design* data carried as hypotheses (the interiority `hint` and the `s = 1` pair datum
`hpair`) are open conditions of the configuration to be added to the design's Sard family; the
identification of `hint` is the new condition of this lane (the avoidances proved on disk cover only
the *level* faces `ftY2`/`ftZ2` of the two sweeps, not their *seam* faces `ftY x 0/1`, `ftZ x 0/1`,
which a collar meet must also avoid for `PPRegAt`'s "exactly one boundary coordinate" clause to be
satisfiable).
-/

namespace Work.Drive

open Manifold Set Filter
open scoped Manifold ContDiff Topology

attribute [local instance] Work.Drive.cappingCharted Work.Drive.isManifold_cappingCharted
  Work.Drive.t2Space_cappingSpace Work.Drive.projCharted

set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2000000

noncomputable section

variable {M : Type*} [TopologicalSpace M] [T2Space M]
  [ChartedSpace (EuclideanSpace ℝ (Fin 4)) M]
  [IsManifold (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 4))) Ctop M]

/-! ## 1. The `9`-box projections of the two chart families and of the two sweeps

The `s = 0` bridge `Work.Drive.ppRegAt_zero_of_meet3Hyp` takes its smoothness in the *`9`-box*
form `z ↦ E (ftS z) (ftU z)`; the `s = 1` bridge and the collar lemma take it in the *uncurried* form
`Function.uncurry E`.  These three one-line lemmas transfer the uncurried form to the `9`-box form, so
that the user of the assembly only has to supply the uncurried one. -/

/-- The `s`-coordinate projection of the `9`-box as a continuous linear map. -/
def ftSCLM : EuclideanSpace ℝ (Fin 9) →L[ℝ] ℝ :=
  PiLp.proj 2 (fun _ : Fin 9 => ℝ) ⟨0, by omega⟩

/-- The `(s,u)`-projection of the `9`-box as a continuous linear map. -/
def ftSUCLM : EuclideanSpace ℝ (Fin 9) →L[ℝ] (ℝ × EuclideanSpace ℝ (Fin 2)) :=
  ftSCLM.prod ftUCLM

lemma ftSCLM_apply (z : EuclideanSpace ℝ (Fin 9)) : ftSCLM z = ftS z := by
  simp [ftSCLM, ftS, PiLp.proj_apply]

lemma ftSUCLM_apply (z : EuclideanSpace ℝ (Fin 9)) : ftSUCLM z = (ftS z, ftU z) := by
  simp [ftSUCLM, ftSCLM_apply, ftUCLM_eq]

/-- **The `9`-box smoothness of a chart family, from the uncurried form.** -/
theorem contMDiff_nineBox_of_uncurry {E : ℝ → EuclideanSpace ℝ (Fin 2) → M}
    (h : ContMDiff (modelWithCornersSelf ℝ (ℝ × EuclideanSpace ℝ (Fin 2)))
      (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 4))) Ctop (Function.uncurry E)) :
    ContMDiff (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 9)))
      (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 4))) Ctop
      (fun z : EuclideanSpace ℝ (Fin 9) => E (ftS z) (ftU z)) := by
  have h1 : (fun z : EuclideanSpace ℝ (Fin 9) => E (ftS z) (ftU z))
      = Function.uncurry E ∘ ftSUCLM := by
    funext z
    simp only [Function.comp_apply, ftSUCLM_apply, Function.uncurry_apply_pair]
  rw [h1]
  exact h.comp (by rw [contMDiff_iff_contDiff]; exact ftSUCLM.contDiff)

/-- **The `9`-box smoothness of a sweep, from its own smoothness.** -/
theorem contMDiff_nineBox_ftY_of {V : EuclideanSpace ℝ (Fin 3) → M}
    (h : ContMDiff (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 3)))
      (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 4))) Ctop V) :
    ContMDiff (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 9)))
      (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 4))) Ctop
      (fun z : EuclideanSpace ℝ (Fin 9) => V (ftY z)) := by
  have h1 : (fun z : EuclideanSpace ℝ (Fin 9) => V (ftY z)) = V ∘ ftYCLM := by
    funext z; simp only [Function.comp_apply, ftYCLM_eq]
  rw [h1]
  exact h.comp (by rw [contMDiff_iff_contDiff]; exact ftYCLM.contDiff)

/-- The same for the second sweep block. -/
theorem contMDiff_nineBox_ftZ_of {W : EuclideanSpace ℝ (Fin 3) → M}
    (h : ContMDiff (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 3)))
      (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 4))) Ctop W) :
    ContMDiff (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 9)))
      (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 4))) Ctop
      (fun z : EuclideanSpace ℝ (Fin 9) => W (ftZ z)) := by
  have h1 : (fun z : EuclideanSpace ℝ (Fin 9) => W (ftZ z)) = W ∘ ftZCLM := by
    funext z; simp only [Function.comp_apply, ftZCLM_eq]
  rw [h1]
  exact h.comp (by rw [contMDiff_iff_contDiff]; exact ftZCLM.contDiff)

/-! ## 2. The two pieces of design data carried by the assembly -/

/-- **The interiority datum at a collar meet**: the plane parameter and both sweep parameters are
strictly inside their boxes.  At a meet with `ftS x = 0` (resp. `1`) this is exactly what makes `0`
the *unique* boundary coordinate of the `9`-box point, i.e. what makes the second clause of `PPRegAt`
have content there. -/
def CollarInterior (x : EuclideanSpace ℝ (Fin 9)) : Prop :=
  (∀ i : Fin 2, ftU x i ∈ Set.Ioo (0 : ℝ) 1) ∧
    (∀ i : Fin 3, ftY x i ∈ Set.Ioo (0 : ℝ) 1) ∧
    (∀ i : Fin 3, ftZ x i ∈ Set.Ioo (0 : ℝ) 1)

/-- **The `s = 1` pair datum of the transport at a meet** (the hypothesis list of
`Work.Drive.ppRegAt_one_of_pairData`): no non-zero plane direction falls simultaneously into the two
sweep ranges, and the two sweeps are immersed at the meet. -/
def PairOneData (E : ℝ → EuclideanSpace ℝ (Fin 2) → M)
    (E' : ℝ → EuclideanSpace ℝ (Fin 2) → M)
    (V W : EuclideanSpace ℝ (Fin 3) → M) (x : EuclideanSpace ℝ (Fin 9)) : Prop :=
  (∀ a : EuclideanSpace ℝ (Fin 2),
    (mfderiv (𝓡 2) (𝓡 4) (fun u : EuclideanSpace ℝ (Fin 2) => E 1 u) (ftU x)) a ∈
        (mfderiv (𝓡 3) (𝓡 4) V (ftY x)).range →
      (mfderiv (𝓡 2) (𝓡 4) (fun u : EuclideanSpace ℝ (Fin 2) => E' 1 u) (ftU x)) a ∈
        (mfderiv (𝓡 3) (𝓡 4) W (ftZ x)).range → a = 0) ∧
    Function.Injective (mfderiv (𝓡 3) (𝓡 4) V (ftY x)) ∧
    Function.Injective (mfderiv (𝓡 3) (𝓡 4) W (ftZ x))

/-! ### 2bis. `CollarInterior` is *necessary* for `PPRegAt` at a collar meet

The interiority is not an artefact of the `s = 0`/`s = 1` bridges: it is forced by the *second clause*
of `PPRegAt` itself.  Since `ftS x ∈ {0,1}` already makes `x` a boundary point of the `9`-box, any
further coordinate of `x` on a face of its box would leave *no* face coordinate `i` with all others
strictly interior, i.e. the existential clause would be false.  Consequently the design's
`hregBase` (`Work.Drive.odd_topBdryMeet_zero_iff_coreSideCount_mul_of_design_intrinsic_nf`) can hold
only if every *collar pair meet* — at `ftS x = 0` these are exactly the cut triples
`cutTriples (diskPlane Q) V W` — is strictly interior, i.e. the avoidances proved on disk
(`Work.Drive.ppMeet_face_avoidances` covers only the *level* faces `ftY2`/`ftZ2`) must be extended to
the four **seam** faces `ftY x 0, ftY x 1, ftZ x 0, ftZ x 1` of the two sweeps. -/
theorem collarInterior_of_ppRegAt
    {E E' : ℝ → EuclideanSpace ℝ (Fin 2) → M} {V W : EuclideanSpace ℝ (Fin 3) → M}
    {x : EuclideanSpace ℝ (Fin 9)} (hx : x ∈ ppMeet E E' V W)
    (h0 : ftS x = 0 ∨ ftS x = 1) (hreg : PPRegAt E E' V W x) : CollarInterior x := by
  obtain ⟨i, -, hoth, -⟩ := hreg.2 ⟨hx.1, 0, h0⟩
  have hi0 : i = 0 := by
    by_contra hne
    have hx0 : x 0 ∈ Set.Ioo (0 : ℝ) 1 := hoth 0 (Ne.symm hne)
    rcases h0 with h0 | h0
    · have : x 0 = 0 := h0
      linarith [hx0.1, hx0.2, this]
    · have : x 0 = 1 := h0
      linarith [hx0.1, hx0.2, this]
  subst hi0
  have h1 : ∀ j : Fin 9, j ≠ 0 → x j ∈ Set.Ioo (0 : ℝ) 1 := hoth
  refine ⟨?_, ?_, ?_⟩
  · intro k; fin_cases k <;> exact h1 _ (by decide)
  · intro k; fin_cases k <;> exact h1 _ (by decide)
  · intro k; fin_cases k <;> exact h1 _ (by decide)

/-- **The collar predicate is monotone in the width.**  A collar of width `δ₂` that is regular is
regular on every narrower collar `δ₁ ≤ δ₂`: the hypothesis set `{ftS x ≤ δ} ∪ {1 - δ ≤ ftS x}` shrinks
as `δ` shrinks.  (Interface note: the assembly below produces *some* `δ < 1/2`; a caller with its own
collar width `δ₀` can therefore take `min δ₀ δ`, which is what the transport `T6`'s cutoffs
`hKcover`/`hwleft`/`hwright` require — they must hold at the width actually used.) -/
theorem hregBase_mono
    {E E' : ℝ → EuclideanSpace ℝ (Fin 2) → M} {V W : EuclideanSpace ℝ (Fin 3) → M}
    {δ₁ δ₂ : ℝ} (h : δ₁ ≤ δ₂)
    (hreg : ∀ x ∈ ppMeet E E' V W, (ftS x ≤ δ₂ ∨ 1 - δ₂ ≤ ftS x) → PPRegAt E E' V W x) :
    ∀ x ∈ ppMeet E E' V W, (ftS x ≤ δ₁ ∨ 1 - δ₁ ≤ ftS x) → PPRegAt E E' V W x := by
  intro x hx hc
  refine hreg x hx ?_
  rcases hc with hc | hc
  · exact Or.inl (le_trans hc h)
  · exact Or.inr (by linarith)

/-- **The `unitBox 8`-restricted form of the collar regularity** — the exact hypothesis shape of
`Work.Drive.exists_ppTubeData` (`Drive/ppDesignInputs.lean`) and of the design's transport `T6`
(whose `hregBase` is written with `x ∈ Submission.Drive.unitBox 8` and the two meet equations).  Since
`ppMeet E E' V W ⊆ unitBox 8`, the `ppMeet`-form implies it. -/
theorem hregBase_box_of_ppMeet
    {E E' : ℝ → EuclideanSpace ℝ (Fin 2) → M} {V W : EuclideanSpace ℝ (Fin 3) → M} {δ : ℝ}
    (hreg : ∀ x ∈ ppMeet E E' V W, (ftS x ≤ δ ∨ 1 - δ ≤ ftS x) → PPRegAt E E' V W x) :
    ∀ x ∈ Submission.Drive.unitBox 8, (ftS x ≤ δ ∨ 1 - δ ≤ ftS x) →
      x ∈ ppMeet E E' V W → PPRegAt E E' V W x :=
  fun x _ hc hx => hreg x hx hc

/-! ## 3. The assembly -/

/-- ***The glue lemma of the collar: `hend` from its two halves.***

From the triple `Meet3Hyp M D` at the `s = 0` end (with the two chart blocks collapsing to the top
face of `D 0`), the pair datum `hpair` at the `s = 1` end, and the interiority `hint` at the collar
meets, every collar meet is `PPRegAt`.  The smoothness is taken only in the uncurried form and
transferred to the `9`-box form by the three lemmas above. -/
theorem ppRegAt_of_collar_data
    {E E' : ℝ → EuclideanSpace ℝ (Fin 2) → M}
    {V W : EuclideanSpace ℝ (Fin 3) → M} {D : Fin 3 → EuclideanSpace ℝ (Fin 3) → M}
    (hrawE : ContMDiff (modelWithCornersSelf ℝ (ℝ × EuclideanSpace ℝ (Fin 2)))
      (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 4))) Ctop (Function.uncurry E))
    (hrawE' : ContMDiff (modelWithCornersSelf ℝ (ℝ × EuclideanSpace ℝ (Fin 2)))
      (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 4))) Ctop (Function.uncurry E'))
    (hrawV : ContMDiff (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 3)))
      (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 4))) Ctop V)
    (hrawW : ContMDiff (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 3)))
      (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 4))) Ctop W)
    (hD3 : Meet3Hyp M D)
    (hE0 : ∀ u : EuclideanSpace ℝ (Fin 2), E 0 u = D 0 (mk3 u 1))
    (hE'0 : ∀ u : EuclideanSpace ℝ (Fin 2), E' 0 u = D 0 (mk3 u 1))
    (hVeq : ∀ y : EuclideanSpace ℝ (Fin 3), V y = D 1 y)
    (hWeq : ∀ z : EuclideanSpace ℝ (Fin 3), W z = D 2 z)
    (hint : ∀ x ∈ ppMeet E E' V W, (ftS x = 0 ∨ ftS x = 1) → CollarInterior x)
    (hpair : ∀ x ∈ ppMeet E E' V W, ftS x = 1 → PairOneData E E' V W x) :
    ∀ x ∈ ppMeet E E' V W, (ftS x = 0 ∨ ftS x = 1) → PPRegAt E E' V W x := by
  intro x hx h0
  obtain ⟨hu, hy, hz⟩ := hint x hx h0
  rcases h0 with h0 | h1
  · exact ppRegAt_zero_of_meet3Hyp hD3 (contMDiff_nineBox_of_uncurry hrawE)
      (contMDiff_nineBox_of_uncurry hrawE') (contMDiff_nineBox_ftY_of hrawV)
      (contMDiff_nineBox_ftZ_of hrawW) hE0 hE'0 hVeq hWeq hx h0 hu hy hz
  · obtain ⟨hset, hC, hDd⟩ := hpair x hx h1
    exact ppRegAt_one_of_pairData hrawE hrawE' hrawV hrawW hx h1 hu hy hz hset hC hDd

/-- ***The collar regularity `hregBase` of the transport, from the end data.***

The `hend` assembly above fed into `Work.Drive.ppParity.exists_delta_regular_collar`: the result is
exactly the `hregBase` hypothesis of the design's transport `T6`
(`Work.Drive.odd_topBdryMeet_zero_iff_coreSideCount_mul_of_design_intrinsic_nf`). -/
theorem hregBase_of_collar_data
    {E E' : ℝ → EuclideanSpace ℝ (Fin 2) → M}
    {V W : EuclideanSpace ℝ (Fin 3) → M} {D : Fin 3 → EuclideanSpace ℝ (Fin 3) → M}
    (hrawE : ContMDiff (modelWithCornersSelf ℝ (ℝ × EuclideanSpace ℝ (Fin 2)))
      (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 4))) Ctop (Function.uncurry E))
    (hrawE' : ContMDiff (modelWithCornersSelf ℝ (ℝ × EuclideanSpace ℝ (Fin 2)))
      (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 4))) Ctop (Function.uncurry E'))
    (hrawV : ContMDiff (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 3)))
      (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 4))) Ctop V)
    (hrawW : ContMDiff (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 3)))
      (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 4))) Ctop W)
    (hD3 : Meet3Hyp M D)
    (hE0 : ∀ u : EuclideanSpace ℝ (Fin 2), E 0 u = D 0 (mk3 u 1))
    (hE'0 : ∀ u : EuclideanSpace ℝ (Fin 2), E' 0 u = D 0 (mk3 u 1))
    (hVeq : ∀ y : EuclideanSpace ℝ (Fin 3), V y = D 1 y)
    (hWeq : ∀ z : EuclideanSpace ℝ (Fin 3), W z = D 2 z)
    (hint : ∀ x ∈ ppMeet E E' V W, (ftS x = 0 ∨ ftS x = 1) → CollarInterior x)
    (hpair : ∀ x ∈ ppMeet E E' V W, ftS x = 1 → PairOneData E E' V W x) :
    ∃ δ : ℝ, 0 < δ ∧ δ < 1 / 2 ∧ ∀ x ∈ ppMeet E E' V W,
      (ftS x ≤ δ ∨ 1 - δ ≤ ftS x) → PPRegAt E E' V W x :=
  ppParity.exists_delta_regular_collar hrawE hrawE' hrawV hrawW
    (ppRegAt_of_collar_data hrawE hrawE' hrawV hrawW hD3 hE0 hE'0 hVeq hWeq hint hpair)


/-! ## 4. The design's transport `T6`: the collar regularity at its concrete chains -/

section Design

/-- **The collar regularity of the design's transport `T6`**, at the concrete chains of
`Work.Drive.odd_topBdryMeet_zero_iff_coreSideCount_mul_of_design_intrinsic_nf`: the two chart blocks
`colPlane β Q` (the radial collapse family) and the constant plane family `diskPlane Q`, against the
two clamped sweeps `clampedSweep c₁ (1-·) P₁`, `clampedSweep c₂ (1-·) P₂`.

The triple `D` of the assembly is the design's own triple of sweeps
`k ↦ clampedSweep (![c₀, c₁, c₂] k) (1-·) (![diskPlane Q, P₁, P₂] k)`, so `hD3` is exactly the
`Meet3Hyp` that the design's genericity provides (`DesignGoodData`'s first conjunct, up to the chain
identifications `designSweep_eq_diskPlane`), and the four identification hypotheses of the assembly
are discharged here from `colPlane_zero`, `clampedSweep_face_one` and the `![·]` bookkeeping. -/
theorem hregBase_design_chains
    (β : ℝ → ℝ) (Q : ℂ → CappingSpace)
    (P₁ P₂ : EuclideanSpace ℝ (Fin 2) → CappingSpace) (c₀ c₁ c₂ : ℝ)
    (hrawE : ContMDiff (modelWithCornersSelf ℝ (ℝ × EuclideanSpace ℝ (Fin 2)))
      (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 4))) Ctop (Function.uncurry (colPlane β Q)))
    (hrawE' : ContMDiff (modelWithCornersSelf ℝ (ℝ × EuclideanSpace ℝ (Fin 2)))
      (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 4))) Ctop
      (Function.uncurry (fun (_ : ℝ) (u : EuclideanSpace ℝ (Fin 2)) => diskPlane Q u)))
    (hrawV : ContMDiff (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 3)))
      (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 4))) Ctop
      (clampedSweep c₁ (fun t => 1 - t) P₁))
    (hrawW : ContMDiff (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 3)))
      (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 4))) Ctop
      (clampedSweep c₂ (fun t => 1 - t) P₂))
    (hD3 : Meet3Hyp CappingSpace
      (fun k => clampedSweep (![c₀, c₁, c₂] k) (fun t => 1 - t)
        (![diskPlane Q, P₁, P₂] k)))
    (hint : ∀ x ∈ ppMeet (colPlane β Q)
        (fun (_ : ℝ) (u : EuclideanSpace ℝ (Fin 2)) => diskPlane Q u)
        (clampedSweep c₁ (fun t => 1 - t) P₁) (clampedSweep c₂ (fun t => 1 - t) P₂),
      (ftS x = 0 ∨ ftS x = 1) → CollarInterior x)
    (hpair : ∀ x ∈ ppMeet (colPlane β Q)
        (fun (_ : ℝ) (u : EuclideanSpace ℝ (Fin 2)) => diskPlane Q u)
        (clampedSweep c₁ (fun t => 1 - t) P₁) (clampedSweep c₂ (fun t => 1 - t) P₂),
      ftS x = 1 → PairOneData (colPlane β Q)
        (fun (_ : ℝ) (u : EuclideanSpace ℝ (Fin 2)) => diskPlane Q u)
        (clampedSweep c₁ (fun t => 1 - t) P₁) (clampedSweep c₂ (fun t => 1 - t) P₂) x) :
    ∃ δ : ℝ, 0 < δ ∧ δ < 1 / 2 ∧ ∀ x ∈ ppMeet (colPlane β Q)
        (fun (_ : ℝ) (u : EuclideanSpace ℝ (Fin 2)) => diskPlane Q u)
        (clampedSweep c₁ (fun t => 1 - t) P₁) (clampedSweep c₂ (fun t => 1 - t) P₂),
      (ftS x ≤ δ ∨ 1 - δ ≤ ftS x) →
        PPRegAt (colPlane β Q) (fun (_ : ℝ) (u : EuclideanSpace ℝ (Fin 2)) => diskPlane Q u)
          (clampedSweep c₁ (fun t => 1 - t) P₁) (clampedSweep c₂ (fun t => 1 - t) P₂) x := by
  refine hregBase_of_collar_data (M := CappingSpace) hrawE hrawE' hrawV hrawW hD3 ?_ ?_ ?_ ?_
    hint hpair
  · -- `E 0 = D 0 ∘ (mk3 · 1)`
    intro u
    show colPlane β Q 0 u = clampedSweep (![c₀, c₁, c₂] 0) (fun t => 1 - t)
      (![diskPlane Q, P₁, P₂] 0) (mk3 u 1)
    rw [colPlane_zero, Matrix.cons_val_zero, clampedSweep_face_one _ _ _ (by norm_num) _ (by simp [mk3])]
    exact congrArg (diskPlane Q) (mk2_mk3 u 1).symm
  · -- `E' 0 = D 0 ∘ (mk3 · 1)`
    intro u
    show (fun (_ : ℝ) (u : EuclideanSpace ℝ (Fin 2)) => diskPlane Q u) 0 u
      = clampedSweep (![c₀, c₁, c₂] 0) (fun t => 1 - t)
        (![diskPlane Q, P₁, P₂] 0) (mk3 u 1)
    rw [Matrix.cons_val_zero, clampedSweep_face_one _ _ _ (by norm_num) _ (by simp [mk3])]
    exact congrArg (diskPlane Q) (mk2_mk3 u 1).symm
  · intro y; rfl
  · intro z; rfl

end Design

end

end Work.Drive
