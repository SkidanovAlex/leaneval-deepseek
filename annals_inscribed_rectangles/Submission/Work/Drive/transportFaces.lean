import Mathlib
import Submission.Work.Drive.transportThreeLevel

/-!
# The level-face avoidances of the transport (design input of `even_ncard_pairMeetBdry`)

`Work.Drive.even_ncard_pairMeetBdry` (T1/T3 of the radial-collapse transport) carries two geometric
hypotheses `havY`/`havZ`: at every zero of the charted pair map, the *level* coordinates
`ftY2 x = x 5` and `ftZ2 x = x 8` are not `0` and not `1`.  Geometrically (see
`Submission/Work/Drive/TRANSPORT_COLLAPSE_STATUS.md` §7.7(ii)):

* `ftY2 x = 1` means the first sweep has reached its top face, where it *is* the plane `P₁`
  (`clampedSweep_face_one`), while the collapsed plane `colPlane β Q s u` lies in the range of the
  chart `Q`; so `P ∩ P₁ = ∅` kills the meet;
* `ftY2 x = 0` means the sweep has reached its bottom face, where it is the *shadow* of `P₁` at the
  level `c` (`clampedSweep_face_zero`), while the chart's levels on the disk are `> c`; so the levels
  differ and the meet cannot happen;
* the same two alternatives for the second sweep (`ftZ2`), with `diskPlane Q u` in place of the
  collapsed plane (its image is in the range of `Q` as well).

This file proves the four *honest* face statements (`colPlane_ne_sweep_top`,
`colPlane_ne_sweep_bot`, `diskPlane_ne_sweep_top`, `diskPlane_ne_sweep_bot`) and then transports them
to the charted pair map, giving `havY`/`havZ` as *theorems* once the chart bridge
(`colPlane β Q s u = … ↔ E s u = V' y`) is available.

All declarations are `sorry`-free and rest on `propext`, `Classical.choice`, `Quot.sound`.
-/

namespace Work.Drive

open Manifold Filter
open scoped Manifold ContDiff Topology

noncomputable section

/-! ## 1. Box-coordinate helpers -/

/-- The third coordinate of the first sweep parameter is the first level coordinate. -/
lemma ftY_two (x : EuclideanSpace ℝ (Fin 9)) : ftY x 2 = ftY2 x := by
  rw [PMB.ftY_apply, PMB.ftY2_eq_coord]
  exact congrArg x (Fin.ext (by norm_num))

/-- The third coordinate of the second sweep parameter is the second level coordinate. -/
lemma ftZ_two (x : EuclideanSpace ℝ (Fin 9)) : ftZ x 2 = ftZ2 x := by
  rw [PMB.ftZ_apply, PMB.ftZ2_eq_coord]
  exact congrArg x (Fin.ext (by norm_num))

lemma ftU_mem_unitBox {x : EuclideanSpace ℝ (Fin 9)} (hx : x ∈ Submission.Drive.unitBox 8) :
    ftU x ∈ Submission.Drive.unitBox 1 := by
  intro i
  rw [PMB.ftU_apply]
  exact hx _

lemma ftY_mem_unitBox {x : EuclideanSpace ℝ (Fin 9)} (hx : x ∈ Submission.Drive.unitBox 8) :
    ftY x ∈ Submission.Drive.unitBox 2 := by
  intro i
  rw [PMB.ftY_apply]
  exact hx _

lemma ftZ_mem_unitBox {x : EuclideanSpace ℝ (Fin 9)} (hx : x ∈ Submission.Drive.unitBox 8) :
    ftZ x ∈ Submission.Drive.unitBox 2 := by
  intro i
  rw [PMB.ftZ_apply]
  exact hx _

/-! ## 2. The collapsed plane lies in the range of the chart -/

/-- **The image of the collapsed plane is contained in the image of the chart.**  For a collar function
`β ≥ √·` the collapse never increases the radius of a point of the unit disk, so the collapsed disk
plane factors through the chart `Q` on the closed disk — i.e. through `range (diskPlane Q)`. -/
lemma colPlane_mem_range_diskPlane {β : ℝ → ℝ} (hβpos : ∀ t : ℝ, 0 < β t)
    (hβ : ∀ t : ℝ, Real.sqrt t ≤ β t) (Q : ℂ → CappingSpace) (s : ℝ)
    (u : EuclideanSpace ℝ (Fin 2)) :
    colPlane β Q s u ∈ Set.range (diskPlane Q) := by
  rw [range_diskPlane]
  refine ⟨colMap β s (sqDisk (foldBox u)), ?_, ?_⟩
  · exact norm_colMap_le_one hβpos hβ s _ (norm_sqDisk_le_one _ (foldBox_mem_unitBox u))
  · simp only [colPlane, colChart, diskPlane]

/-! ## 3. The four honest face statements -/

/-- **The top face of the first sweep.**  If the range of the collapsed chart meets the range of `P₁`
nowhere, then at `y 2 = 1` (where the sweep *is* the plane `P₁`) the collapsed plane misses it. -/
theorem colPlane_ne_sweep_top {β : ℝ → ℝ} (hβpos : ∀ t : ℝ, 0 < β t)
    (hβ : ∀ t : ℝ, Real.sqrt t ≤ β t) (Q : ℂ → CappingSpace)
    (P : EuclideanSpace ℝ (Fin 2) → CappingSpace) (c : ℝ)
    (hdisj : Disjoint (Set.range (diskPlane Q)) (Set.range P)) :
    ∀ (s : ℝ) (u : EuclideanSpace ℝ (Fin 2)) (y : EuclideanSpace ℝ (Fin 3)),
      u ∈ Submission.Drive.unitBox 1 → y ∈ Submission.Drive.unitBox 2 → y 2 = 1 →
      colPlane β Q s u ≠ clampedSweep c (fun t => 1 - t) P y := by
  intro s u y hu hy hy1 heq
  have htop : clampedSweep c (fun t => 1 - t) P y = P (mk2 (y 0) (y 1)) :=
    clampedSweep_face_one c (fun t => 1 - t) P (by norm_num) y hy1
  have hmem : colPlane β Q s u ∈ Set.range P := by
    rw [heq, htop]
    exact ⟨mk2 (y 0) (y 1), rfl⟩
  exact (Set.disjoint_left.mp hdisj) (colPlane_mem_range_diskPlane hβpos hβ Q s u) hmem

/-- **The bottom face of the first sweep.**  At `y 2 = 0` the sweep *is* the shadow of `P₁` at the
level `c`, whose level is `c`, while the chart's levels on the disk are `> c`. -/
theorem colPlane_ne_sweep_bot {β : ℝ → ℝ} (hβpos : ∀ t : ℝ, 0 < β t)
    (hβ : ∀ t : ℝ, Real.sqrt t ≤ β t) (Q : ℂ → CappingSpace)
    (P : EuclideanSpace ℝ (Fin 2) → CappingSpace) (c : ℝ) (hc : 0 < c)
    (hlev : ∀ z : ℂ, ‖z‖ ≤ 1 → c < levelOf (Q z)) :
    ∀ (s : ℝ) (u : EuclideanSpace ℝ (Fin 2)) (y : EuclideanSpace ℝ (Fin 3)),
      u ∈ Submission.Drive.unitBox 1 → y ∈ Submission.Drive.unitBox 2 → y 2 = 0 →
      colPlane β Q s u ≠ clampedSweep c (fun t => 1 - t) P y := by
  intro s u y hu hy hy0 heq
  have hbot : clampedSweep c (fun t => 1 - t) P y = shadow c hc (P (mk2 (y 0) (y 1))) :=
    clampedSweep_face_zero c hc (fun t => 1 - t) P (by norm_num) y hy0
  have hnorm : ‖colMap β s (sqDisk (foldBox u))‖ ≤ 1 :=
    norm_colMap_le_one hβpos hβ s _ (norm_sqDisk_le_one _ (foldBox_mem_unitBox u))
  have hl := hlev (colMap β s (sqDisk (foldBox u))) hnorm
  have hlv : levelOf (colPlane β Q s u) = c := by rw [heq, hbot, levelOf_shadow]
  have hunf : levelOf (colPlane β Q s u)
      = levelOf (Q (colMap β s (sqDisk (foldBox u)))) := by
    simp only [colPlane, colChart, diskPlane]
  rw [hunf] at hlv
  linarith

/-- **The top face of the second sweep**, for the *uncollapsed* plane `diskPlane Q`. -/
theorem diskPlane_ne_sweep_top (Q : ℂ → CappingSpace)
    (P : EuclideanSpace ℝ (Fin 2) → CappingSpace) (c : ℝ)
    (hdisj : Disjoint (Set.range (diskPlane Q)) (Set.range P)) :
    ∀ (u : EuclideanSpace ℝ (Fin 2)) (z : EuclideanSpace ℝ (Fin 3)),
      u ∈ Submission.Drive.unitBox 1 → z ∈ Submission.Drive.unitBox 2 → z 2 = 1 →
      diskPlane Q u ≠ clampedSweep c (fun t => 1 - t) P z := by
  intro u z hu hz hz1 heq
  have htop : clampedSweep c (fun t => 1 - t) P z = P (mk2 (z 0) (z 1)) :=
    clampedSweep_face_one c (fun t => 1 - t) P (by norm_num) z hz1
  have hmem : diskPlane Q u ∈ Set.range P := by
    rw [heq, htop]
    exact ⟨mk2 (z 0) (z 1), rfl⟩
  exact (Set.disjoint_left.mp hdisj) ⟨u, rfl⟩ hmem

/-- **The bottom face of the second sweep**, for the *uncollapsed* plane `diskPlane Q`. -/
theorem diskPlane_ne_sweep_bot (Q : ℂ → CappingSpace)
    (P : EuclideanSpace ℝ (Fin 2) → CappingSpace) (c : ℝ) (hc : 0 < c)
    (hlev : ∀ z : ℂ, ‖z‖ ≤ 1 → c < levelOf (Q z)) :
    ∀ (u : EuclideanSpace ℝ (Fin 2)) (z : EuclideanSpace ℝ (Fin 3)),
      u ∈ Submission.Drive.unitBox 1 → z ∈ Submission.Drive.unitBox 2 → z 2 = 0 →
      diskPlane Q u ≠ clampedSweep c (fun t => 1 - t) P z := by
  intro u z hu hz hz0 heq
  have hbot : clampedSweep c (fun t => 1 - t) P z = shadow c hc (P (mk2 (z 0) (z 1))) :=
    clampedSweep_face_zero c hc (fun t => 1 - t) P (by norm_num) z hz0
  have hnorm : ‖sqDisk (foldBox u)‖ ≤ 1 := norm_sqDisk_le_one _ (foldBox_mem_unitBox u)
  have hl := hlev (sqDisk (foldBox u)) hnorm
  have hlv : levelOf (diskPlane Q u) = c := by rw [heq, hbot, levelOf_shadow]
  have hunf : levelOf (diskPlane Q u) = levelOf (Q (sqDisk (foldBox u))) := by
    simp only [diskPlane]
  rw [hunf] at hlv
  linarith

/-! ## 4. The charted level-face avoidances `havY`/`havZ` -/

/-- **`havY` of `even_ncard_pairMeetBdry`, from the design data.**  Given the chart bridge for the
collapsed plane against the first sweep, the disjointness of the plane's range from the swept plane's
range, and the level comparison, the two level coordinates of the first sweep parameter are never `0`
or `1` at a zero of the charted pair map. -/
theorem pairDiff_faceY_ne {β : ℝ → ℝ} (hβpos : ∀ t : ℝ, 0 < β t)
    (hβ : ∀ t : ℝ, Real.sqrt t ≤ β t) (Q : ℂ → CappingSpace)
    (P₁ : EuclideanSpace ℝ (Fin 2) → CappingSpace) (c₁ : ℝ) (hc₁ : 0 < c₁)
    (E : ℝ → EuclideanSpace ℝ (Fin 2) → EuclideanSpace ℝ (Fin 4))
    (E' : EuclideanSpace ℝ (Fin 2) → EuclideanSpace ℝ (Fin 4))
    (V' W' : EuclideanSpace ℝ (Fin 3) → EuclideanSpace ℝ (Fin 4))
    (hcol : ∀ (s : ℝ) (u : EuclideanSpace ℝ (Fin 2)) (y : EuclideanSpace ℝ (Fin 3)),
      u ∈ Submission.Drive.unitBox 1 → y ∈ Submission.Drive.unitBox 2 →
      (colPlane β Q s u = clampedSweep c₁ (fun t => 1 - t) P₁ y ↔ E s u = V' y))
    (hdisj₁ : Disjoint (Set.range (diskPlane Q)) (Set.range P₁))
    (hlev : ∀ z : ℂ, ‖z‖ ≤ 1 → c₁ < levelOf (Q z)) :
    ∀ x ∈ Submission.Drive.unitBox 8, pairDiff E E' V' W' x = 0 →
      ftY2 x ≠ 0 ∧ ftY2 x ≠ 1 := by
  intro x hx hzero
  have hboxU := ftU_mem_unitBox hx
  have hboxY := ftY_mem_unitBox hx
  have hz := (pairDiff_eq_zero_iff E E' V' W' x).mp hzero
  have heq : colPlane β Q (ftS x) (ftU x) = clampedSweep c₁ (fun t => 1 - t) P₁ (ftY x) :=
    (hcol (ftS x) (ftU x) (ftY x) hboxU hboxY).mpr hz.1
  refine ⟨?_, ?_⟩
  · intro h0
    exact colPlane_ne_sweep_bot hβpos hβ Q P₁ c₁ hc₁ hlev (ftS x) (ftU x) (ftY x) hboxU hboxY
      (by rw [ftY_two]; exact h0) heq
  · intro h1
    exact colPlane_ne_sweep_top hβpos hβ Q P₁ c₁ hdisj₁ (ftS x) (ftU x) (ftY x) hboxU hboxY
      (by rw [ftY_two]; exact h1) heq

/-- **`havZ` of `even_ncard_pairMeetBdry`, from the design data.** -/
theorem pairDiff_faceZ_ne {β : ℝ → ℝ} (hβpos : ∀ t : ℝ, 0 < β t)
    (hβ : ∀ t : ℝ, Real.sqrt t ≤ β t) (Q : ℂ → CappingSpace)
    (P₂ : EuclideanSpace ℝ (Fin 2) → CappingSpace) (c₂ : ℝ) (hc₂ : 0 < c₂)
    (E : ℝ → EuclideanSpace ℝ (Fin 2) → EuclideanSpace ℝ (Fin 4))
    (E' : EuclideanSpace ℝ (Fin 2) → EuclideanSpace ℝ (Fin 4))
    (V' W' : EuclideanSpace ℝ (Fin 3) → EuclideanSpace ℝ (Fin 4))
    (hdis : ∀ (u : EuclideanSpace ℝ (Fin 2)) (z : EuclideanSpace ℝ (Fin 3)),
      u ∈ Submission.Drive.unitBox 1 → z ∈ Submission.Drive.unitBox 2 →
      (diskPlane Q u = clampedSweep c₂ (fun t => 1 - t) P₂ z ↔ E' u = W' z))
    (hdisj₂ : Disjoint (Set.range (diskPlane Q)) (Set.range P₂))
    (hlev : ∀ z : ℂ, ‖z‖ ≤ 1 → c₂ < levelOf (Q z)) :
    ∀ x ∈ Submission.Drive.unitBox 8, pairDiff E E' V' W' x = 0 →
      ftZ2 x ≠ 0 ∧ ftZ2 x ≠ 1 := by
  intro x hx hzero
  have hboxU := ftU_mem_unitBox hx
  have hboxZ := ftZ_mem_unitBox hx
  have hz := (pairDiff_eq_zero_iff E E' V' W' x).mp hzero
  have heq : diskPlane Q (ftU x) = clampedSweep c₂ (fun t => 1 - t) P₂ (ftZ x) :=
    (hdis (ftU x) (ftZ x) hboxU hboxZ).mpr hz.2
  refine ⟨?_, ?_⟩
  · intro h0
    exact diskPlane_ne_sweep_bot Q P₂ c₂ hc₂ hlev (ftU x) (ftZ x) hboxU hboxZ
      (by rw [ftZ_two]; exact h0) heq
  · intro h1
    exact diskPlane_ne_sweep_top Q P₂ c₂ hdisj₂ (ftU x) (ftZ x) hboxU hboxZ
      (by rw [ftZ_two]; exact h1) heq

/-! ## 5. The transport target with the face hypotheses *derived* -/

/-- **T6 with the level-face avoidances derived from the design data.**  Same conclusion as
`Work.Drive.odd_topBdryMeet_zero_iff_coreSideCount_mul`, but with `havY`/`havZ` no longer hypotheses:
they are produced from the two *geometric* design inputs — the disjointness of the plane's range from
the ranges of the two swept planes (`P ∩ Pᵢ = ∅`, i.e. `u ∈ Zc γ`), and the level comparison
("the floors lie below the levels") — through `pairDiff_faceY_ne`/`pairDiff_faceZ_ne`.

The bridge `hcol`/`hdis` is required for **every** family parameter `s` here (not only `s ∈ {0,1}`),
because the face statements are needed at every zero of the pair map, including the zeros at interior
`s`. -/
theorem odd_topBdryMeet_zero_iff_coreSideCount_mul_of_design
    (E : ℝ → EuclideanSpace ℝ (Fin 2) → EuclideanSpace ℝ (Fin 4))
    (E' : EuclideanSpace ℝ (Fin 2) → EuclideanSpace ℝ (Fin 4))
    (V' W' : EuclideanSpace ℝ (Fin 3) → EuclideanSpace ℝ (Fin 4))
    (β : ℝ → ℝ) (Q : ℂ → CappingSpace)
    (P₁ P₂ : EuclideanSpace ℝ (Fin 2) → CappingSpace) (c₀ c₁ c₂ : ℝ)
    (hc₁ : 0 < c₁) (hc₂ : 0 < c₂)
    (hβpos : ∀ t : ℝ, 0 < β t) (hβ : ∀ t : ℝ, Real.sqrt t ≤ β t)
    (hE : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (Function.uncurry E))
    (hE' : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) E')
    (hV' : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) V')
    (hW' : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) W')
    (hreg : ∀ x ∈ Submission.Drive.unitBox 8, pairDiff E E' V' W' x = 0 →
      Function.Surjective (fderiv ℝ (pairDiff E E' V' W') x))
    (hface : ∀ x ∈ Submission.Drive.unitBoxBdry 8, pairDiff E E' V' W' x = 0 →
      ∃ i : Fin 9, (x i = 0 ∨ x i = 1) ∧ (∀ j : Fin 9, j ≠ i → x j ∈ Set.Ioo (0 : ℝ) 1) ∧
        Function.Surjective (fun v : {v : EuclideanSpace ℝ (Fin 9) // v i = 0} =>
          fderiv ℝ (pairDiff E E' V' W') x v.1))
    (hseamU : ∀ (s : ℝ) (u : EuclideanSpace ℝ (Fin 2)), onSeam2 u → E s (seamInv2 u) = E s u)
    (hseamU' : ∀ u : EuclideanSpace ℝ (Fin 2), onSeam2 u → E' (seamInv2 u) = E' u)
    (hseamV : ∀ y : EuclideanSpace ℝ (Fin 3), onSeam y → V' (seamInv y) = V' y)
    (hseamW : ∀ z : EuclideanSpace ℝ (Fin 3), onSeam z → W' (seamInv z) = W' z)
    (hcol : ∀ (s : ℝ) (u : EuclideanSpace ℝ (Fin 2)) (y : EuclideanSpace ℝ (Fin 3)),
      u ∈ Submission.Drive.unitBox 1 → y ∈ Submission.Drive.unitBox 2 →
      (colPlane β Q s u = clampedSweep c₁ (fun t => 1 - t) P₁ y ↔ E s u = V' y))
    (hdis : ∀ (u : EuclideanSpace ℝ (Fin 2)) (z : EuclideanSpace ℝ (Fin 3)),
      u ∈ Submission.Drive.unitBox 1 → z ∈ Submission.Drive.unitBox 2 →
      (diskPlane Q u = clampedSweep c₂ (fun t => 1 - t) P₂ z ↔ E' u = W' z))
    (hdisj₁ : Disjoint (Set.range (diskPlane Q)) (Set.range P₁))
    (hdisj₂ : Disjoint (Set.range (diskPlane Q)) (Set.range P₂))
    (hlev : ∀ z : ℂ, ‖z‖ ≤ 1 → c₁ < levelOf (Q z) ∧ c₂ < levelOf (Q z))
    (hfibV : ∀ u ∈ cutBaseBox (diskPlane Q) (clampedSweep c₁ (fun t => 1 - t) P₁)
        (clampedSweep c₂ (fun t => 1 - t) P₂),
      (cutFibreBox (diskPlane Q) (clampedSweep c₁ (fun t => 1 - t) P₁) u).ncard = 1)
    (hfibW : ∀ u ∈ cutBaseBox (diskPlane Q) (clampedSweep c₁ (fun t => 1 - t) P₁)
        (clampedSweep c₂ (fun t => 1 - t) P₂),
      (cutFibreBox (diskPlane Q) (clampedSweep c₂ (fun t => 1 - t) P₂) u).ncard = 1)
    (hQseam : ∀ z : ℂ, ‖z‖ = 1 → Q (-z) = Q z)
    {δ : ℝ} (hδ : 0 ≤ δ) (hβδ : ∀ t : ℝ, δ ^ 2 ≤ t → β t = Real.sqrt t)
    (hδcut : ∀ x : EuclideanSpace ℝ (Fin 2), ‖cplxOf x‖ ≤ δ →
      x ∉ diskCut Q (clampedSweep c₂ (fun t => 1 - t) P₂))
    (hfin : (coreMeet Q c₁ P₁).Finite)
    (hfind : ∀ q ∈ coreMeet Q c₁ P₁, (diamMeet Q q.1 (clampedSweep c₂ (fun t => 1 - t) P₂)).Finite)
    (hbase : ∀ y ∈ Submission.Drive.unitBox 2,
      coreLoop Q 1 ≠ clampedSweep c₁ (fun t => 1 - t) P₁ y)
    (ht5 : ∀ t : ℝ, Odd (diamMeet Q t (clampedSweep c₂ (fun t => 1 - t) P₂)).ncard ↔
      Odd (coreSideCount Q c₂ P₂)) :
    Odd (topBdryMeet CappingSpace
        (fun k => clampedSweep (![c₀, c₁, c₂] k) (fun t => 1 - t)
          (![diskPlane Q, P₁, P₂] k)) 0).ncard ↔
      Odd (coreSideCount Q c₁ P₁) ∧ Odd (coreSideCount Q c₂ P₂) :=
  odd_topBdryMeet_zero_iff_coreSideCount_mul E E' V' W' β Q P₁ P₂ c₀ c₁ c₂
    hE hE' hV' hW' hreg hface hseamU hseamU' hseamV hseamW
    (pairDiff_faceY_ne hβpos hβ Q P₁ c₁ hc₁ E E' V' W' hcol hdisj₁
      (fun z hz => (hlev z hz).1))
    (pairDiff_faceZ_ne hβpos hβ Q P₂ c₂ hc₂ E E' V' W' hdis hdisj₂
      (fun z hz => (hlev z hz).2))
    (fun s _ u hu y hy => hcol s u y hu hy) (fun s _ u hu z hz => hdis u z hu hz)
    hfibV hfibW hQseam hδ hβδ hδcut hfin hfind hbase ht5

end

end Work.Drive