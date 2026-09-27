import Mathlib
import Submission.Work.Drive.transportPair2
import Submission.Work.Drive.transportSep

/-!
# (G2): the two end collars of the collapse parameter, and the box-parity capstone

The transport's box-parity stage runs on the **weighted chart-shift** of the pair of chart blocks
(`Work.Drive.exists_pairDiff2_good_shift`): the Sard produces the regularity and the face data of the
perturbed pair map on a compact set `K` on which the weight `w` does not vanish, while the two
**end faces** `s ∈ {0,1}` must keep the honest chains (`w 0 = w 1 = 0`) so that the two endpoint
identifications `K 0 = n_P`, `K 1 = #fibreMeet` survive.

Consequently the weight vanishes on the two **collars** of the family parameter, and on those collars
the perturbed pair map *equals* the base one — so the base configuration's data has to be used there.
This file

* provides the collar transfers in the **`∨`-form** that covers both collars at once
  (`collar_reg`, `collar_face`, `collar_avoidY`, `collar_avoidZ`), with the base data required only
  *on the collar* (not on the whole box);
* provides the matching shape of the inactive weighted shift (`weightedShift_agrees_both`);
* assembles the capstone `exists_even_colCount_add2_of_shift_collar`: the box-parity conclusion
  `Even (K 0 + K 1)` for the honest collapse counts, with the hypothesis list reduced to
  (i) the Sard data on `K`, (ii) the **base data on the two collars** — the lead's **(G2)**, and
  (iii) the geometric level-face avoidances of the perturbed chains (produced for instance by
  `Work.Drive.pairDiff2_faceY_ne_of_sep` / `pairDiff2_faceZ_ne_of_sep`).

All declarations are `sorry`-free and rest on `propext`, `Classical.choice`, `Quot.sound`.
-/

namespace Work.Drive

open Manifold Filter
open scoped Manifold ContDiff Topology

noncomputable section

/-- The open set consisting of the two collars of the family parameter. -/
lemma isOpen_collars (δ : ℝ) :
    IsOpen ({y : EuclideanSpace ℝ (Fin 9) | ftS y < δ} ∪
      {y : EuclideanSpace ℝ (Fin 9) | 1 - δ < ftS y}) := by
  have hcont : Continuous fun y : EuclideanSpace ℝ (Fin 9) => y 0 := by fun_prop
  refine (isOpen_lt hcont continuous_const).union ?_
  simpa only [ftS] using isOpen_lt continuous_const hcont

/-- **The perturbed pair map agrees with the base one on the two collars.**  If the two perturbed
blocks agree with the base blocks at every family parameter in a collar, then the two pair maps are
equal as functions on the open union of the two collars. -/
theorem pairDiff2_eventuallyEq_collars
    (E₀ E'₀ : ℝ → EuclideanSpace ℝ (Fin 2) → EuclideanSpace ℝ (Fin 4))
    (V₀ W₀ : EuclideanSpace ℝ (Fin 3) → EuclideanSpace ℝ (Fin 4))
    (E E' : ℝ → EuclideanSpace ℝ (Fin 2) → EuclideanSpace ℝ (Fin 4)) {δ : ℝ}
    (hE : ∀ s, (s ≤ δ ∨ 1 - δ ≤ s) → ∀ u, E s u = E₀ s u)
    (hE' : ∀ s, (s ≤ δ ∨ 1 - δ ≤ s) → ∀ u, E' s u = E'₀ s u)
    (x : EuclideanSpace ℝ (Fin 9)) (hx : ftS x < δ ∨ 1 - δ < ftS x) :
    pairDiff2 E E' V₀ W₀ =ᶠ[𝓝 x] pairDiff2 E₀ E'₀ V₀ W₀ := by
  refine Filter.eventually_of_mem ((isOpen_collars δ).mem_nhds hx) fun y hy => ?_
  have hs : (ftS y ≤ δ ∨ 1 - δ ≤ ftS y) := by
    rcases hy with hy | hy
    · exact Or.inl (le_of_lt hy)
    · exact Or.inr (le_of_lt hy)
  have h1 : E (ftS y) (ftU y) = E₀ (ftS y) (ftU y) := hE (ftS y) hs (ftU y)
  have h2 : E' (ftS y) (ftU y) = E'₀ (ftS y) (ftU y) := hE' (ftS y) hs (ftU y)
  simp only [pairDiff2, h1, h2]

/-! ## The four collar transfers, with the base data required only on the collar -/

/-- **(G2), regularity**: the base configuration's regularity at its collar zeros transfers to the
perturbation. -/
theorem collar_reg
    (E₀ E'₀ : ℝ → EuclideanSpace ℝ (Fin 2) → EuclideanSpace ℝ (Fin 4))
    (V₀ W₀ : EuclideanSpace ℝ (Fin 3) → EuclideanSpace ℝ (Fin 4))
    (E E' : ℝ → EuclideanSpace ℝ (Fin 2) → EuclideanSpace ℝ (Fin 4)) {δ : ℝ}
    (hE : ∀ s, (s ≤ δ ∨ 1 - δ ≤ s) → ∀ u, E s u = E₀ s u)
    (hE' : ∀ s, (s ≤ δ ∨ 1 - δ ≤ s) → ∀ u, E' s u = E'₀ s u)
    (hregBase : ∀ x ∈ Submission.Drive.unitBox 8, (ftS x < δ ∨ 1 - δ < ftS x) →
      pairDiff2 E₀ E'₀ V₀ W₀ x = 0 →
      Function.Surjective (fderiv ℝ (pairDiff2 E₀ E'₀ V₀ W₀) x)) :
    ∀ x ∈ Submission.Drive.unitBox 8, (ftS x < δ ∨ 1 - δ < ftS x) →
      pairDiff2 E E' V₀ W₀ x = 0 →
      Function.Surjective (fderiv ℝ (pairDiff2 E E' V₀ W₀) x) := by
  intro x hx hxc hzero
  have hev := pairDiff2_eventuallyEq_collars E₀ E'₀ V₀ W₀ E E' hE hE' x hxc
  rw [hev.fderiv_eq]
  exact hregBase x hx hxc (by rw [← hev.eq_of_nhds]; exact hzero)

/-- **(G2), face clause**: the base configuration's face data (a *unique* face coordinate, all others
strictly interior, and the restricted derivative onto) transfers to the perturbation. -/
theorem collar_face
    (E₀ E'₀ : ℝ → EuclideanSpace ℝ (Fin 2) → EuclideanSpace ℝ (Fin 4))
    (V₀ W₀ : EuclideanSpace ℝ (Fin 3) → EuclideanSpace ℝ (Fin 4))
    (E E' : ℝ → EuclideanSpace ℝ (Fin 2) → EuclideanSpace ℝ (Fin 4)) {δ : ℝ}
    (hE : ∀ s, (s ≤ δ ∨ 1 - δ ≤ s) → ∀ u, E s u = E₀ s u)
    (hE' : ∀ s, (s ≤ δ ∨ 1 - δ ≤ s) → ∀ u, E' s u = E'₀ s u)
    (hfaceBase : ∀ x ∈ Submission.Drive.unitBoxBdry 8, (ftS x < δ ∨ 1 - δ < ftS x) →
      pairDiff2 E₀ E'₀ V₀ W₀ x = 0 →
      ∃ i : Fin 9, (x i = 0 ∨ x i = 1) ∧ (∀ j : Fin 9, j ≠ i → x j ∈ Set.Ioo (0 : ℝ) 1) ∧
        Function.Surjective (fun v : {v : EuclideanSpace ℝ (Fin 9) // v i = 0} =>
          fderiv ℝ (pairDiff2 E₀ E'₀ V₀ W₀) x v.1)) :
    ∀ x ∈ Submission.Drive.unitBox 8, (ftS x < δ ∨ 1 - δ < ftS x) →
      pairDiff2 E E' V₀ W₀ x = 0 →
      x ∈ Submission.Drive.unitBoxBdry 8 →
      ∃ i : Fin 9, (x i = 0 ∨ x i = 1) ∧ (∀ j : Fin 9, j ≠ i → x j ∈ Set.Ioo (0 : ℝ) 1) ∧
        Function.Surjective (fun v : {v : EuclideanSpace ℝ (Fin 9) // v i = 0} =>
          fderiv ℝ (pairDiff2 E E' V₀ W₀) x v.1) := by
  intro x _hx hxc hzero hbdry
  have hev := pairDiff2_eventuallyEq_collars E₀ E'₀ V₀ W₀ E E' hE hE' x hxc
  have hb := hfaceBase x hbdry hxc (by rw [← hev.eq_of_nhds]; exact hzero)
  rw [hev.fderiv_eq]
  exact hb

/-- **(G2), first level-face avoidance**: transfers from the base configuration on the collar. -/
theorem collar_avoidY
    (E₀ E'₀ : ℝ → EuclideanSpace ℝ (Fin 2) → EuclideanSpace ℝ (Fin 4))
    (V₀ W₀ : EuclideanSpace ℝ (Fin 3) → EuclideanSpace ℝ (Fin 4))
    (E E' : ℝ → EuclideanSpace ℝ (Fin 2) → EuclideanSpace ℝ (Fin 4)) {δ : ℝ}
    (hE : ∀ s, (s ≤ δ ∨ 1 - δ ≤ s) → ∀ u, E s u = E₀ s u)
    (hE' : ∀ s, (s ≤ δ ∨ 1 - δ ≤ s) → ∀ u, E' s u = E'₀ s u)
    (havBase : ∀ x ∈ Submission.Drive.unitBox 8, (ftS x < δ ∨ 1 - δ < ftS x) →
      pairDiff2 E₀ E'₀ V₀ W₀ x = 0 → ftY2 x ≠ 0 ∧ ftY2 x ≠ 1) :
    ∀ x ∈ Submission.Drive.unitBox 8, (ftS x < δ ∨ 1 - δ < ftS x) →
      pairDiff2 E E' V₀ W₀ x = 0 → ftY2 x ≠ 0 ∧ ftY2 x ≠ 1 := by
  intro x hx hxc hzero
  have hev := pairDiff2_eventuallyEq_collars E₀ E'₀ V₀ W₀ E E' hE hE' x hxc
  exact havBase x hx hxc (by rw [← hev.eq_of_nhds]; exact hzero)

/-- **(G2), second level-face avoidance**: transfers from the base configuration on the collar. -/
theorem collar_avoidZ
    (E₀ E'₀ : ℝ → EuclideanSpace ℝ (Fin 2) → EuclideanSpace ℝ (Fin 4))
    (V₀ W₀ : EuclideanSpace ℝ (Fin 3) → EuclideanSpace ℝ (Fin 4))
    (E E' : ℝ → EuclideanSpace ℝ (Fin 2) → EuclideanSpace ℝ (Fin 4)) {δ : ℝ}
    (hE : ∀ s, (s ≤ δ ∨ 1 - δ ≤ s) → ∀ u, E s u = E₀ s u)
    (hE' : ∀ s, (s ≤ δ ∨ 1 - δ ≤ s) → ∀ u, E' s u = E'₀ s u)
    (havBase : ∀ x ∈ Submission.Drive.unitBox 8, (ftS x < δ ∨ 1 - δ < ftS x) →
      pairDiff2 E₀ E'₀ V₀ W₀ x = 0 → ftZ2 x ≠ 0 ∧ ftZ2 x ≠ 1) :
    ∀ x ∈ Submission.Drive.unitBox 8, (ftS x < δ ∨ 1 - δ < ftS x) →
      pairDiff2 E E' V₀ W₀ x = 0 → ftZ2 x ≠ 0 ∧ ftZ2 x ≠ 1 := by
  intro x hx hxc hzero
  have hev := pairDiff2_eventuallyEq_collars E₀ E'₀ V₀ W₀ E E' hE hE' x hxc
  exact havBase x hx hxc (by rw [← hev.eq_of_nhds]; exact hzero)

/-! ## The weighted shift is inactive on the collars -/

/-- **The weighted chart-shift is inactive on the two collars** as soon as the weight vanishes there.
This is the `hE`-shape of the four transfers above for the design's perturbation
`E s u = E₀ s u + w s • unpackFst t`, `E' s u = E'₀ s u + w s • unpackSnd t`. -/
theorem weightedShift_agrees_both
    (E₀ E'₀ : ℝ → EuclideanSpace ℝ (Fin 2) → EuclideanSpace ℝ (Fin 4))
    {δ : ℝ} {w : ℝ → ℝ}
    (hwleft : ∀ s, s ≤ δ → w s = 0) (hwright : ∀ s, 1 - δ ≤ s → w s = 0)
    (t : EuclideanSpace ℝ (Fin 8)) :
    (∀ s, (s ≤ δ ∨ 1 - δ ≤ s) →
        ∀ u, (fun s u => E₀ s u + w s • unpackFst t) s u = E₀ s u) ∧
      (∀ s, (s ≤ δ ∨ 1 - δ ≤ s) →
        ∀ u, (fun s u => E'₀ s u + w s • unpackSnd t) s u = E'₀ s u) := by
  have key : ∀ s, (s ≤ δ ∨ 1 - δ ≤ s) → w s = 0 :=
    fun s hs => hs.elim (hwleft s) (hwright s)
  refine ⟨fun s hs u => ?_, fun s hs u => ?_⟩
  · simp only [key s hs, zero_smul, add_zero]
  · simp only [key s hs, zero_smul, add_zero]

/-! ## The capstone: box parity with the collar data as the only genericity input -/

/-- **The box-parity stage of the transport, with the two collars handled by the base
configuration.**  Given

* the Sard parameter `t` is produced on the compact `K` (`∃ t, ‖t‖ < ε`, `w ≠ 0` on `K`) — this is
  `Work.Drive.exists_pairDiff2_good_shift`;
* `K` contains the whole *interior slab* `{δ ≤ ftS x ≤ 1 - δ}` of the box, and the weight vanishes on
  the two complementary collars `{ftS x ≤ δ}`, `{1 - δ ≤ ftS x}`;
* the **base** configuration is regular and carries the face data at its zeros in the collar (the
  lead's **(G2)**);
* the *perturbed* configuration's level faces are avoided on the whole box (produced e.g. by
  `Work.Drive.pairDiff2_faceY_ne_of_sep` / `pairDiff2_faceZ_ne_of_sep`);
* the two seam invariances and the chart bridge at the endpoint parameters,
* `w 0 = w 1 = 0`,

the honest collapse counts at the two endpoint parameters have even sum: `Even (K 0 + K 1)`. -/
theorem exists_even_colCount_add2_of_shift_collar
    (E₀ : ℝ → EuclideanSpace ℝ (Fin 2) → EuclideanSpace ℝ (Fin 4))
    (E'₀ : ℝ → EuclideanSpace ℝ (Fin 2) → EuclideanSpace ℝ (Fin 4))
    (V' W' : EuclideanSpace ℝ (Fin 3) → EuclideanSpace ℝ (Fin 4))
    (β : ℝ → ℝ) (Q : ℂ → CappingSpace)
    (V W : EuclideanSpace ℝ (Fin 3) → CappingSpace)
    (w : ℝ → ℝ) (K : Set (EuclideanSpace ℝ (Fin 9))) (hK : IsCompact K) {δ : ℝ}
    (hE₀ : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (Function.uncurry E₀))
    (hE'₀ : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (Function.uncurry E'₀))
    (hV' : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) V')
    (hW' : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) W')
    (hw : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) w)
    (hwne : ∀ x ∈ K, w (ftS x) ≠ 0)
    (hKcover : ∀ x ∈ Submission.Drive.unitBox 8, δ ≤ ftS x → ftS x ≤ 1 - δ → x ∈ K)
    (hwleft : ∀ s, s ≤ δ → w s = 0) (hwright : ∀ s, 1 - δ ≤ s → w s = 0)
    (hregBase : ∀ x ∈ Submission.Drive.unitBox 8, (ftS x < δ ∨ 1 - δ < ftS x) →
      pairDiff2 E₀ E'₀ V' W' x = 0 →
      Function.Surjective (fderiv ℝ (pairDiff2 E₀ E'₀ V' W') x))
    (hfaceBase : ∀ x ∈ Submission.Drive.unitBoxBdry 8, (ftS x < δ ∨ 1 - δ < ftS x) →
      pairDiff2 E₀ E'₀ V' W' x = 0 →
      ∃ i : Fin 9, (x i = 0 ∨ x i = 1) ∧ (∀ j : Fin 9, j ≠ i → x j ∈ Set.Ioo (0 : ℝ) 1) ∧
        Function.Surjective (fun v : {v : EuclideanSpace ℝ (Fin 9) // v i = 0} =>
          fderiv ℝ (pairDiff2 E₀ E'₀ V' W') x v.1))
    (havY : ∀ t : EuclideanSpace ℝ (Fin 8), ∀ x ∈ Submission.Drive.unitBox 8,
      pairDiff2 (fun s u => E₀ s u + w s • unpackFst t)
        (fun s u => E'₀ s u + w s • unpackSnd t) V' W' x = 0 →
      ftY2 x ≠ 0 ∧ ftY2 x ≠ 1)
    (havZ : ∀ t : EuclideanSpace ℝ (Fin 8), ∀ x ∈ Submission.Drive.unitBox 8,
      pairDiff2 (fun s u => E₀ s u + w s • unpackFst t)
        (fun s u => E'₀ s u + w s • unpackSnd t) V' W' x = 0 →
      ftZ2 x ≠ 0 ∧ ftZ2 x ≠ 1)
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
  have hout : ∀ x ∈ Submission.Drive.unitBox 8, x ∉ K → ftS x < δ ∨ 1 - δ < ftS x := by
    intro x hx hxK
    by_contra hc
    push Not at hc
    exact hxK (hKcover x hx hc.1 hc.2)
  have hA := weightedShift_agrees_both E₀ E'₀ hwleft hwright
  refine exists_even_colCount_add2_of_shift E₀ E'₀ V' W' β Q V W w K hK hE₀ hE'₀ hV' hW' hw
    hwne ?_ ?_ havY havZ hseamU hseamU' hseamV hseamW hcol hdis hw0 hw1 ε hε
  · -- the regularity clause outside `K`
    intro t x hx hxK hzero
    have hxc := hout x hx hxK
    exact collar_reg E₀ E'₀ V' W' _ _ (hA t).1 (hA t).2 hregBase x hx hxc hzero
  · -- the face clause outside `K`
    intro t x hx hxK hzero hbdry
    have hxc := hout x hx hxK
    exact collar_face E₀ E'₀ V' W' _ _ (hA t).1 (hA t).2 hfaceBase x hx hxc hzero hbdry

end

end Work.Drive
