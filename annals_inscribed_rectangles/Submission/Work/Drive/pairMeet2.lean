import Mathlib
import Submission.Work.Drive.pairMeetDefs
import Submission.Work.Drive.TParity.Basic
import Submission.Work.Drive.transportThreeLevel

/-!
# The pair map with **both** chart blocks `s`-dependent, and its `hsurj`

`Work.Drive.pairDiff` (`pairMeetDefs.lean`) has the structure

> `pairDiff E E' V W x = pair44 (E (ftS x) (ftU x) − V (ftY x)) (E' (ftU x) − W (ftZ x))`,

i.e. the first chart block is a *family* of `2`-chains (indexed by the collapse parameter `s = ftS x`),
while the **second block is `s`-independent**.  That asymmetry is what makes the transport's endpoint
identifications work (`K 0 = cutTriples (diskPlane Q) V W`, `K 1 = #fibreMeet`), but it is also a
*constraint on the admissible perturbation* (`TRANSPORT_COLLAPSE_STATUS.md` §8.6 item 2): a
perturbation weighted by `σ(1-σ)` — which is needed to keep the two endpoint identifications — cannot
be applied to an `s`-independent block.

This file introduces the **symmetric** pair map

> `pairDiff2 E E' V W x = pair44 (E (ftS x) (ftU x) − V (ftY x)) (E' (ftS x) (ftU x) − W (ftZ x))`

whose second block is *also* an `s`-family.  For the honest collapse count nothing is lost — take
`E' := fun _ u => diskPlane Q u` — and everything is gained: both chart blocks can be perturbed with
the same weighted chart-shift, so the parameter-derivative criterion of
`transportThreeLevel.lean` §4 applies *verbatim* (see `surjective_fderiv_pairDiff2_of_block` and
`surjective_fderiv_pairDiff2_weightedShift` below).

The box-parity engine for `pairDiff2` (`even_ncard_pairMeetBdry2`) is **delegated**: its proof is the
verbatim port of `Work.Drive.even_ncard_pairMeetBdry` (the general lemmas — `boxParity`,
`even_sum_ncard_labelMeet`, the labelling of the nine faces — are stated for an arbitrary
`F : Amb 8 → Tgt 8` and are reused unchanged; only the four specialisations
(`uPart`/`yPart`/`zPart`/`endFace` and the two endpoint identifications) must be redone with
`E' (ftS x) (ftU x)` in place of `E' (ftU x)`).

All declarations here are `sorry`-free and rest on `propext`, `Classical.choice`, `Quot.sound`.
-/

set_option autoImplicit false

namespace Work.Drive

open Manifold
open scoped Manifold ContDiff Topology

noncomputable section

/-! ## 1. The symmetric pair map and its meet set -/

/-- **The pair difference map with both chart blocks `s`-dependent**: at the point `(s, u, y, z)` of the
nine-box it is `(E s u − V y, E' s u − W z)`.  With `E' := fun _ u => diskPlane Q u` it is the collapse
pair map of the transport. -/
def pairDiff2 (E : ℝ → EuclideanSpace ℝ (Fin 2) → EuclideanSpace ℝ (Fin 4))
    (E' : ℝ → EuclideanSpace ℝ (Fin 2) → EuclideanSpace ℝ (Fin 4))
    (V W : EuclideanSpace ℝ (Fin 3) → EuclideanSpace ℝ (Fin 4)) :
    EuclideanSpace ℝ (Fin 9) → EuclideanSpace ℝ (Fin 8) :=
  fun x => pair44 (E (ftS x) (ftU x) - V (ftY x)) (E' (ftS x) (ftU x) - W (ftZ x))

/-- **The zero set of `pairDiff2`** is the pair of meets `E s u = V y`, `E' s u = W z`. -/
theorem pairDiff2_eq_zero_iff
    (E : ℝ → EuclideanSpace ℝ (Fin 2) → EuclideanSpace ℝ (Fin 4))
    (E' : ℝ → EuclideanSpace ℝ (Fin 2) → EuclideanSpace ℝ (Fin 4))
    (V W : EuclideanSpace ℝ (Fin 3) → EuclideanSpace ℝ (Fin 4))
    (x : EuclideanSpace ℝ (Fin 9)) :
    pairDiff2 E E' V W x = 0 ↔ E (ftS x) (ftU x) = V (ftY x) ∧ E' (ftS x) (ftU x) = W (ftZ x) := by
  have hpair : pairDiff2 E E' V W x
      = pair44 (E (ftS x) (ftU x) - V (ftY x)) (E' (ftS x) (ftU x) - W (ftZ x)) := rfl
  constructor
  · intro h
    have h1 : E (ftS x) (ftU x) - V (ftY x) = 0 := by
      ext j
      have := congrArg (fun v : EuclideanSpace ℝ (Fin 8) => v (Fin.castAdd 4 j)) h
      rw [hpair] at this
      simpa using this
    have h2 : E' (ftS x) (ftU x) - W (ftZ x) = 0 := by
      ext j
      have := congrArg (fun v : EuclideanSpace ℝ (Fin 8) => v (Fin.natAdd 4 j)) h
      rw [hpair] at this
      simpa using this
    exact ⟨sub_eq_zero.mp h1, sub_eq_zero.mp h2⟩
  · rintro ⟨h1, h2⟩
    rw [hpair, sub_eq_zero.mpr h1, sub_eq_zero.mpr h2]
    ext i
    fin_cases i <;> simp [pair44]

/-- **The pair meet set of `pairDiff2` at the family parameter `s`**: the parameter triples `(u, y, z)`
of the box at which both pair equations hold.  With `E'` constant in `s` this is
`Work.Drive.pairMeetSet`. -/
def pairMeetSet2 (E : ℝ → EuclideanSpace ℝ (Fin 2) → EuclideanSpace ℝ (Fin 4))
    (E' : ℝ → EuclideanSpace ℝ (Fin 2) → EuclideanSpace ℝ (Fin 4))
    (V W : EuclideanSpace ℝ (Fin 3) → EuclideanSpace ℝ (Fin 4)) (s : ℝ) :
    Set (EuclideanSpace ℝ (Fin 2) × EuclideanSpace ℝ (Fin 3) × EuclideanSpace ℝ (Fin 3)) :=
  {p | p.1 ∈ Submission.Drive.unitBox 1 ∧ p.2.1 ∈ Submission.Drive.unitBox 2 ∧
       p.2.2 ∈ Submission.Drive.unitBox 2 ∧ E s p.1 = V p.2.1 ∧ E' s p.1 = W p.2.2}

/-- **The `s`-face of the nine-box is the pair meet set at `s`** — the bridge the box-parity proof
needs (`Work.Drive.ncard_endFace` for `pairDiff2`).  The map `x ↦ (ftU x, ftY x, ftZ x)` is a bijection
onto `unitBox 1 × unitBox 2 × unitBox 2`. -/
theorem ncard_endFace_pairDiff2
    (E : ℝ → EuclideanSpace ℝ (Fin 2) → EuclideanSpace ℝ (Fin 4))
    (E' : ℝ → EuclideanSpace ℝ (Fin 2) → EuclideanSpace ℝ (Fin 4))
    (V W : EuclideanSpace ℝ (Fin 3) → EuclideanSpace ℝ (Fin 4))
    {s : ℝ} (hs : s = 0 ∨ s = 1) :
    (PMB.endFace (pairDiff2 E E' V W) s).ncard = (pairMeetSet2 E E' V W s).ncard := by
  have hs01 : s ∈ Set.Icc (0 : ℝ) 1 := by
    rcases hs with h | h <;> rw [h] <;> norm_num
  refine Set.ncard_congr (fun x _ => (ftU x, ftY x, ftZ x)) ?_ ?_ ?_
  · intro x hx
    obtain ⟨hbz, hsx⟩ := hx
    rw [mem_bdyZeros] at hbz
    obtain ⟨⟨hbox, -⟩, hzero⟩ := hbz
    have hd := (pairDiff2_eq_zero_iff E E' V W x).mp hzero
    rw [pairMeetSet2, Set.mem_ofPred_eq]
    refine ⟨?_, ?_, ?_, ?_, ?_⟩
    · show ∀ i : Fin 2, ftU x i ∈ Set.Icc (0 : ℝ) 1
      intro i
      rw [PMB.ftU_apply]
      exact hbox _
    · show ∀ i : Fin 3, ftY x i ∈ Set.Icc (0 : ℝ) 1
      intro i
      rw [PMB.ftY_apply]
      exact hbox _
    · show ∀ i : Fin 3, ftZ x i ∈ Set.Icc (0 : ℝ) 1
      intro i
      rw [PMB.ftZ_apply]
      exact hbox _
    · show E s (ftU x) = V (ftY x)
      rw [← hsx]
      exact hd.1
    · show E' s (ftU x) = W (ftZ x)
      rw [← hsx]
      exact hd.2
  · intro x x' hx hx' h
    have h1 : ftU x = ftU x' := congrArg (fun p : EuclideanSpace ℝ (Fin 2) ×
      EuclideanSpace ℝ (Fin 3) × EuclideanSpace ℝ (Fin 3) => p.1) h
    have h2 : ftY x = ftY x' := congrArg (fun p : EuclideanSpace ℝ (Fin 2) ×
      EuclideanSpace ℝ (Fin 3) × EuclideanSpace ℝ (Fin 3) => p.2.1) h
    have h3 : ftZ x = ftZ x' := congrArg (fun p : EuclideanSpace ℝ (Fin 2) ×
      EuclideanSpace ℝ (Fin 3) × EuclideanSpace ℝ (Fin 3) => p.2.2) h
    rw [← PMB.mk9_ft x, ← PMB.mk9_ft x', h1, h2, h3, hx.2, hx'.2]
  · intro p hp
    rw [pairMeetSet2, Set.mem_ofPred_eq] at hp
    obtain ⟨hu, hy, hz, h1, h2⟩ := hp
    refine ⟨PMB.mk9 s p.1 p.2.1 p.2.2, ?_, ?_⟩
    · refine ⟨?_, PMB.ftS_mk9 s p.1 p.2.1 p.2.2⟩
      rw [mem_bdyZeros, Submission.Drive.unitBoxBdry, Set.mem_ofPred_eq]
      refine ⟨⟨PMB.mk9_mem_unitBox hs01 hu hy hz, ?_⟩, ?_⟩
      · exact ⟨0, by rcases hs with h | h <;> simp [PMB.mk9, h]⟩
      · rw [show pairDiff2 E E' V W (PMB.mk9 s p.1 p.2.1 p.2.2)
            = pair44 (E s p.1 - V p.2.1) (E' s p.1 - W p.2.2) from by
          simp only [pairDiff2, PMB.ftS_mk9, PMB.ftU_mk9, PMB.ftY_mk9, PMB.ftZ_mk9],
          h1, h2, sub_self, sub_self]
        exact PMB.pair44_zero
    · rw [PMB.ftU_mk9, PMB.ftY_mk9, PMB.ftZ_mk9]

/-! ## 2. The block criterion and the shift theorems for `pairDiff2` -/

/-- **The block criterion for `pairDiff2`.**  Same statement as
`Work.Drive.surjective_fderiv_pairDiff_of_block`, with the second chart block an `s`-family: moving the
`E`-block and the `E'`-block independently (freezing `V` and `W`) makes the parameter-derivative of
`pairDiff2` onto `ℝ⁸`. -/
theorem surjective_fderiv_pairDiff2_of_block (m : ℕ)
    (E : EuclideanSpace ℝ (Fin m) → ℝ → EuclideanSpace ℝ (Fin 2) → EuclideanSpace ℝ (Fin 4))
    (E' : EuclideanSpace ℝ (Fin m) → ℝ → EuclideanSpace ℝ (Fin 2) → EuclideanSpace ℝ (Fin 4))
    (V W : EuclideanSpace ℝ (Fin m) → EuclideanSpace ℝ (Fin 3) → EuclideanSpace ℝ (Fin 4))
    (p : EuclideanSpace ℝ (Fin m)) (x : EuclideanSpace ℝ (Fin 9))
    (DE DE' DV DW : EuclideanSpace ℝ (Fin m) →L[ℝ] EuclideanSpace ℝ (Fin 4))
    (hE : HasFDerivAt (fun t => E t (ftS x) (ftU x)) DE p)
    (hE' : HasFDerivAt (fun t => E' t (ftS x) (ftU x)) DE' p)
    (hV : HasFDerivAt (fun t => V t (ftY x)) DV p)
    (hW : HasFDerivAt (fun t => W t (ftZ x)) DW p)
    (hblock : ∀ a b : EuclideanSpace ℝ (Fin 4), ∃ u : EuclideanSpace ℝ (Fin m),
      DE u = a ∧ DE' u = b ∧ DV u = 0 ∧ DW u = 0) :
    Function.Surjective
      (fderiv ℝ (fun t => pairDiff2 (E t) (E' t) (V t) (W t) x) p) := by
  have hprod : HasFDerivAt
      (fun t => (E t (ftS x) (ftU x) - V t (ftY x), E' t (ftS x) (ftU x) - W t (ftZ x)))
      ((DE - DV).prod (DE' - DW)) p := (hE.sub hV).prodMk (hE'.sub hW)
  have hpup : HasFDerivAt
      (fun t => TParity.pUpCLM (E t (ftS x) (ftU x) - V t (ftY x),
        E' t (ftS x) (ftU x) - W t (ftZ x)))
      (TParity.pUpCLM.comp ((DE - DV).prod (DE' - DW))) p :=
    TParity.pUpCLM.hasFDerivAt.comp p hprod
  have hfin : HasFDerivAt (fun t => pairDiff2 (E t) (E' t) (V t) (W t) x)
      (TParity.pUpCLM.comp ((DE - DV).prod (DE' - DW))) p :=
    hpup.congr_of_eventuallyEq (Filter.Eventually.of_forall fun t => by
      simp only [pairDiff2, TParity.pUpCLM_apply, pair44_eq_pairUp])
  rw [hfin.fderiv]
  intro w
  obtain ⟨u, hu1, hu2, hu3, hu4⟩ := hblock (TParity.fst8 w) (TParity.snd8 w)
  refine ⟨u, ?_⟩
  rw [ContinuousLinearMap.comp_apply, ContinuousLinearMap.prod_apply, sub_apply, sub_apply,
    hu1, hu2, hu3, hu4, sub_zero, sub_zero, TParity.pUpCLM_apply, TParity.pUp_fst8_snd8]

/-- **`hsurj` for the weighted chart-shift of *both* blocks of `pairDiff2`.**  Both blocks are shifted
by the two blocks of the parameter, with the weight `w (ftS x)`: surjective whenever the weight does not
vanish.  Since the weight can be `σ(1-σ)`, this is the form in which the perturbation keeps the
transport's two endpoint identifications *and* is regular in the interior. -/
theorem surjective_fderiv_pairDiff2_weightedShift
    (E₀ : ℝ → EuclideanSpace ℝ (Fin 2) → EuclideanSpace ℝ (Fin 4))
    (E'₀ : ℝ → EuclideanSpace ℝ (Fin 2) → EuclideanSpace ℝ (Fin 4))
    (V₀ W₀ : EuclideanSpace ℝ (Fin 3) → EuclideanSpace ℝ (Fin 4))
    (w : ℝ → ℝ) (q : EuclideanSpace ℝ (Fin 8)) (x : EuclideanSpace ℝ (Fin 9))
    (hw : w (ftS x) ≠ 0) :
    Function.Surjective (fderiv ℝ (fun t : EuclideanSpace ℝ (Fin 8) =>
      pairDiff2 (fun s u => E₀ s u + w (ftS x) • unpackFst t)
        (fun s u => E'₀ s u + w (ftS x) • unpackSnd t) V₀ W₀ x) q) := by
  refine surjective_fderiv_pairDiff2_of_block 8
    (fun t s u => E₀ s u + w (ftS x) • unpackFst t)
    (fun t s u => E'₀ s u + w (ftS x) • unpackSnd t)
    (fun _ y => V₀ y) (fun _ z => W₀ z) q x
    (w (ftS x) • unpackFst) (w (ftS x) • unpackSnd) 0 0
    (by simpa using (ContinuousLinearMap.hasFDerivAt ((w (ftS x)) • unpackFst)).const_add (E₀ (ftS x) (ftU x)))
    (by simpa using (ContinuousLinearMap.hasFDerivAt ((w (ftS x)) • unpackSnd)).const_add (E'₀ (ftS x) (ftU x)))
    (hasFDerivAt_const _ _) (hasFDerivAt_const _ _) ?_
  intro a b
  refine ⟨pairUp ((w (ftS x))⁻¹ • a) ((w (ftS x))⁻¹ • b), ?_, ?_, rfl, rfl⟩
  · rw [ContinuousLinearMap.smul_apply, unpackFst_pairUp, smul_smul,
      mul_inv_cancel₀ hw, one_smul]
  · rw [ContinuousLinearMap.smul_apply, unpackSnd_pairUp, smul_smul,
      mul_inv_cancel₀ hw, one_smul]

end

end Work.Drive
