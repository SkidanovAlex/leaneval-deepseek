import Mathlib
import Submission.Work.Drive.pairMeet2
import Submission.Work.Drive.even_ncard_pairMeetBdry

/-!
# The parity of the pair-meet counts at the two ends of the *symmetric* collapse family

`Work.Drive.even_ncard_pairMeetBdry2` is the box-level form of the bordism invariance of the pair-meet
count of the **symmetric** radial-collapse transport of `Submission/Work/Drive/pairMeet2.lean`: both
chart blocks of the pair map `pairDiff2` are `s`-families, so

> `pairDiff2 E E' V W x = pair4 4 (E (ftS x) (ftU x) − V (ftY x)) (E' (ftS x) (ftU x) − W (ftZ x))`,

and the two end counts `#pairMeetSet2 E E' V W 0` and `#pairMeetSet2 E E' V W 1` have the same
parity.

The proof is the verbatim port of `Work.Drive.even_ncard_pairMeetBdry`: the general lemmas
(`boxParity`, `even_sum_ncard_labelMeet`, the whole coordinate dictionary and the three seam
involutions of the `9`-box) are stated for an arbitrary `F : Amb 8 → Tgt 8` and are reused from the
namespace `Work.Drive.PMB` unchanged; only the five specialisations that mention `pairDiff` are redone
here with `pairDiff2` (the two end faces via `ncard_endFace_pairDiff2` of `pairMeet2.lean`, the three
seam involutions, the level faces and the smoothness).
-/

set_option autoImplicit false

namespace Work.Drive

open Submission.Drive
open scoped ContDiff Topology

noncomputable section

namespace PMB2

open PMB

/-! ## 1. The value of `pairDiff2` on the coordinate decomposition of the `9`-box -/

lemma pairDiff2_mk9 (E : ℝ → EuclideanSpace ℝ (Fin 2) → EuclideanSpace ℝ (Fin 4))
    (E' : ℝ → EuclideanSpace ℝ (Fin 2) → EuclideanSpace ℝ (Fin 4))
    (V W : EuclideanSpace ℝ (Fin 3) → EuclideanSpace ℝ (Fin 4))
    (s : ℝ) (u : EuclideanSpace ℝ (Fin 2)) (y z : EuclideanSpace ℝ (Fin 3)) :
    pairDiff2 E E' V W (mk9 s u y z) = pair44 (E s u - V y) (E' s u - W z) := by
  simp only [pairDiff2, ftS_mk9, ftU_mk9, ftY_mk9, ftZ_mk9]

/-! ## 2. The three seam involutions act trivially on `pairDiff2` at a seam point -/

/-- **The pair difference map is invariant under the plane involution at a seam point.** -/
lemma pairDiff2_uInv_mk (E : ℝ → EuclideanSpace ℝ (Fin 2) → EuclideanSpace ℝ (Fin 4))
    (E' : ℝ → EuclideanSpace ℝ (Fin 2) → EuclideanSpace ℝ (Fin 4))
    (V W : EuclideanSpace ℝ (Fin 3) → EuclideanSpace ℝ (Fin 4))
    (hseamU : ∀ (s : ℝ) (u : EuclideanSpace ℝ (Fin 2)),
      onSeam2 u → E s (seamInv2 u) = E s u)
    (hseamU' : ∀ (s : ℝ) (u : EuclideanSpace ℝ (Fin 2)),
      onSeam2 u → E' s (seamInv2 u) = E' s u)
    (s : ℝ) (u : EuclideanSpace ℝ (Fin 2)) (y z : EuclideanSpace ℝ (Fin 3))
    (h : onSeam2 u) :
    pairDiff2 E E' V W (mk9 s (seamInv2 u) y z) = pairDiff2 E E' V W (mk9 s u y z) := by
  simp only [pairDiff2_mk9, hseamU s u h, hseamU' s u h]

lemma pairDiff2_uInv (E : ℝ → EuclideanSpace ℝ (Fin 2) → EuclideanSpace ℝ (Fin 4))
    (E' : ℝ → EuclideanSpace ℝ (Fin 2) → EuclideanSpace ℝ (Fin 4))
    (V W : EuclideanSpace ℝ (Fin 3) → EuclideanSpace ℝ (Fin 4))
    (hseamU : ∀ (s : ℝ) (u : EuclideanSpace ℝ (Fin 2)),
      onSeam2 u → E s (seamInv2 u) = E s u)
    (hseamU' : ∀ (s : ℝ) (u : EuclideanSpace ℝ (Fin 2)),
      onSeam2 u → E' s (seamInv2 u) = E' s u)
    (x : Amb 8) (h : onSeam2 (ftU x)) :
    pairDiff2 E E' V W (uInv x) = pairDiff2 E E' V W x := by
  rw [show uInv x = mk9 (ftS x) (seamInv2 (ftU x)) (ftY x) (ftZ x) from rfl]
  rw [pairDiff2_uInv_mk E E' V W hseamU hseamU' (ftS x) (ftU x) (ftY x) (ftZ x) h, mk9_ft x]

/-- **The pair difference map is invariant under the first sweep involution at a seam point.** -/
lemma pairDiff2_yInv_mk (E : ℝ → EuclideanSpace ℝ (Fin 2) → EuclideanSpace ℝ (Fin 4))
    (E' : ℝ → EuclideanSpace ℝ (Fin 2) → EuclideanSpace ℝ (Fin 4))
    (V W : EuclideanSpace ℝ (Fin 3) → EuclideanSpace ℝ (Fin 4))
    (hseamV : ∀ y : EuclideanSpace ℝ (Fin 3), onSeam y → V (seamInv y) = V y)
    (s : ℝ) (u : EuclideanSpace ℝ (Fin 2)) (y z : EuclideanSpace ℝ (Fin 3))
    (h : onSeam y) :
    pairDiff2 E E' V W (mk9 s u (seamInv y) z) = pairDiff2 E E' V W (mk9 s u y z) := by
  simp only [pairDiff2_mk9, hseamV y h]

lemma pairDiff2_yInv (E : ℝ → EuclideanSpace ℝ (Fin 2) → EuclideanSpace ℝ (Fin 4))
    (E' : ℝ → EuclideanSpace ℝ (Fin 2) → EuclideanSpace ℝ (Fin 4))
    (V W : EuclideanSpace ℝ (Fin 3) → EuclideanSpace ℝ (Fin 4))
    (hseamV : ∀ y : EuclideanSpace ℝ (Fin 3), onSeam y → V (seamInv y) = V y)
    (x : Amb 8) (h : onSeam (ftY x)) :
    pairDiff2 E E' V W (yInv x) = pairDiff2 E E' V W x := by
  rw [show yInv x = mk9 (ftS x) (ftU x) (seamInv (ftY x)) (ftZ x) from rfl]
  rw [pairDiff2_yInv_mk E E' V W hseamV (ftS x) (ftU x) (ftY x) (ftZ x) h, mk9_ft x]

/-- **The pair difference map is invariant under the second sweep involution at a seam point.** -/
lemma pairDiff2_zInv_mk (E : ℝ → EuclideanSpace ℝ (Fin 2) → EuclideanSpace ℝ (Fin 4))
    (E' : ℝ → EuclideanSpace ℝ (Fin 2) → EuclideanSpace ℝ (Fin 4))
    (V W : EuclideanSpace ℝ (Fin 3) → EuclideanSpace ℝ (Fin 4))
    (hseamW : ∀ z : EuclideanSpace ℝ (Fin 3), onSeam z → W (seamInv z) = W z)
    (s : ℝ) (u : EuclideanSpace ℝ (Fin 2)) (y z : EuclideanSpace ℝ (Fin 3))
    (h : onSeam z) :
    pairDiff2 E E' V W (mk9 s u y (seamInv z)) = pairDiff2 E E' V W (mk9 s u y z) := by
  simp only [pairDiff2_mk9, hseamW z h]

lemma pairDiff2_zInv (E : ℝ → EuclideanSpace ℝ (Fin 2) → EuclideanSpace ℝ (Fin 4))
    (E' : ℝ → EuclideanSpace ℝ (Fin 2) → EuclideanSpace ℝ (Fin 4))
    (V W : EuclideanSpace ℝ (Fin 3) → EuclideanSpace ℝ (Fin 4))
    (hseamW : ∀ z : EuclideanSpace ℝ (Fin 3), onSeam z → W (seamInv z) = W z)
    (x : Amb 8) (h : onSeam (ftZ x)) :
    pairDiff2 E E' V W (zInv x) = pairDiff2 E E' V W x := by
  rw [show zInv x = mk9 (ftS x) (ftU x) (ftY x) (seamInv (ftZ x)) from rfl]
  rw [pairDiff2_zInv_mk E E' V W hseamW (ftS x) (ftU x) (ftY x) (ftZ x) h, mk9_ft x]

/-! ## 3. The seam groups are invariant under their involution -/

lemma uInv_mem2 (E : ℝ → EuclideanSpace ℝ (Fin 2) → EuclideanSpace ℝ (Fin 4))
    (E' : ℝ → EuclideanSpace ℝ (Fin 2) → EuclideanSpace ℝ (Fin 4))
    (V W : EuclideanSpace ℝ (Fin 3) → EuclideanSpace ℝ (Fin 4))
    (hseamU : ∀ (s : ℝ) (u : EuclideanSpace ℝ (Fin 2)),
      onSeam2 u → E s (seamInv2 u) = E s u)
    (hseamU' : ∀ (s : ℝ) (u : EuclideanSpace ℝ (Fin 2)),
      onSeam2 u → E' s (seamInv2 u) = E' s u)
    {x : Amb 8} (hx : x ∈ uPart (pairDiff2 E E' V W)) :
    uInv x ∈ uPart (pairDiff2 E E' V W) := by
  rw [mem_uPart] at hx
  obtain ⟨hbz, hco⟩ := hx
  rw [mem_bdyZeros] at hbz
  obtain ⟨⟨hbox, -⟩, hzero⟩ := hbz
  have hsU := onSeam2_ftU_of x hco
  rw [mem_uPart]
  refine ⟨?_, ?_⟩
  · rw [mem_bdyZeros, Submission.Drive.unitBoxBdry, Set.mem_ofPred_eq]
    refine ⟨⟨uInv_mem_unitBox hbox, ?_⟩, ?_⟩
    · rcases hco with (h | h) | (h | h)
      · exact ⟨1, Or.inr (by rw [uInv_apply_one, h]; norm_num)⟩
      · exact ⟨1, Or.inl (by rw [uInv_apply_one, h]; norm_num)⟩
      · exact ⟨2, Or.inr (by rw [uInv_apply_two, h]; norm_num)⟩
      · exact ⟨2, Or.inl (by rw [uInv_apply_two, h]; norm_num)⟩
    · rw [pairDiff2_uInv E E' V W hseamU hseamU' x hsU]
      exact hzero
  · rcases hco with (h | h) | (h | h)
    · exact Or.inl (Or.inr (by rw [uInv_apply_one, h]; norm_num))
    · exact Or.inl (Or.inl (by rw [uInv_apply_one, h]; norm_num))
    · exact Or.inr (Or.inr (by rw [uInv_apply_two, h]; norm_num))
    · exact Or.inr (Or.inl (by rw [uInv_apply_two, h]; norm_num))

lemma yInv_mem2 (E : ℝ → EuclideanSpace ℝ (Fin 2) → EuclideanSpace ℝ (Fin 4))
    (E' : ℝ → EuclideanSpace ℝ (Fin 2) → EuclideanSpace ℝ (Fin 4))
    (V W : EuclideanSpace ℝ (Fin 3) → EuclideanSpace ℝ (Fin 4))
    (hseamV : ∀ y : EuclideanSpace ℝ (Fin 3), onSeam y → V (seamInv y) = V y)
    {x : Amb 8} (hx : x ∈ yPart (pairDiff2 E E' V W)) :
    yInv x ∈ yPart (pairDiff2 E E' V W) := by
  rw [mem_yPart] at hx
  obtain ⟨hbz, hco⟩ := hx
  rw [mem_bdyZeros] at hbz
  obtain ⟨⟨hbox, -⟩, hzero⟩ := hbz
  have hsV := onSeam_ftY_of x hco
  rw [mem_yPart]
  refine ⟨?_, ?_⟩
  · rw [mem_bdyZeros, Submission.Drive.unitBoxBdry, Set.mem_ofPred_eq]
    refine ⟨⟨yInv_mem_unitBox hbox, ?_⟩, ?_⟩
    · rcases hco with (h | h) | (h | h)
      · exact ⟨3, Or.inr (by rw [yInv_apply_three, h]; norm_num)⟩
      · exact ⟨3, Or.inl (by rw [yInv_apply_three, h]; norm_num)⟩
      · exact ⟨4, Or.inr (by rw [yInv_apply_four, h]; norm_num)⟩
      · exact ⟨4, Or.inl (by rw [yInv_apply_four, h]; norm_num)⟩
    · rw [pairDiff2_yInv E E' V W hseamV x hsV]
      exact hzero
  · rcases hco with (h | h) | (h | h)
    · exact Or.inl (Or.inr (by rw [yInv_apply_three, h]; norm_num))
    · exact Or.inl (Or.inl (by rw [yInv_apply_three, h]; norm_num))
    · exact Or.inr (Or.inr (by rw [yInv_apply_four, h]; norm_num))
    · exact Or.inr (Or.inl (by rw [yInv_apply_four, h]; norm_num))

lemma zInv_mem2 (E : ℝ → EuclideanSpace ℝ (Fin 2) → EuclideanSpace ℝ (Fin 4))
    (E' : ℝ → EuclideanSpace ℝ (Fin 2) → EuclideanSpace ℝ (Fin 4))
    (V W : EuclideanSpace ℝ (Fin 3) → EuclideanSpace ℝ (Fin 4))
    (hseamW : ∀ z : EuclideanSpace ℝ (Fin 3), onSeam z → W (seamInv z) = W z)
    {x : Amb 8} (hx : x ∈ zPart (pairDiff2 E E' V W)) :
    zInv x ∈ zPart (pairDiff2 E E' V W) := by
  rw [mem_zPart] at hx
  obtain ⟨hbz, hco⟩ := hx
  rw [mem_bdyZeros] at hbz
  obtain ⟨⟨hbox, -⟩, hzero⟩ := hbz
  have hsW := onSeam_ftZ_of x hco
  rw [mem_zPart]
  refine ⟨?_, ?_⟩
  · rw [mem_bdyZeros, Submission.Drive.unitBoxBdry, Set.mem_ofPred_eq]
    refine ⟨⟨zInv_mem_unitBox hbox, ?_⟩, ?_⟩
    · rcases hco with (h | h) | (h | h)
      · exact ⟨6, Or.inr (by rw [zInv_apply_six, h]; norm_num)⟩
      · exact ⟨6, Or.inl (by rw [zInv_apply_six, h]; norm_num)⟩
      · exact ⟨7, Or.inr (by rw [zInv_apply_seven, h]; norm_num)⟩
      · exact ⟨7, Or.inl (by rw [zInv_apply_seven, h]; norm_num)⟩
    · rw [pairDiff2_zInv E E' V W hseamW x hsW]
      exact hzero
  · rcases hco with (h | h) | (h | h)
    · exact Or.inl (Or.inr (by rw [zInv_apply_six, h]; norm_num))
    · exact Or.inl (Or.inl (by rw [zInv_apply_six, h]; norm_num))
    · exact Or.inr (Or.inr (by rw [zInv_apply_seven, h]; norm_num))
    · exact Or.inr (Or.inl (by rw [zInv_apply_seven, h]; norm_num))

/-! ## 4. The three seam groups carry an even number of boundary zeros -/

lemma even_ncard_uPart2 (E : ℝ → EuclideanSpace ℝ (Fin 2) → EuclideanSpace ℝ (Fin 4))
    (E' : ℝ → EuclideanSpace ℝ (Fin 2) → EuclideanSpace ℝ (Fin 4))
    (V W : EuclideanSpace ℝ (Fin 3) → EuclideanSpace ℝ (Fin 4))
    (hseamU : ∀ (s : ℝ) (u : EuclideanSpace ℝ (Fin 2)),
      onSeam2 u → E s (seamInv2 u) = E s u)
    (hseamU' : ∀ (s : ℝ) (u : EuclideanSpace ℝ (Fin 2)),
      onSeam2 u → E' s (seamInv2 u) = E' s u)
    (hfin : (uPart (pairDiff2 E E' V W)).Finite) :
    Even (uPart (pairDiff2 E E' V W)).ncard :=
  even_ncard_of_involution hfin uInv (fun _ hx => uInv_mem2 E E' V W hseamU hseamU' hx)
    (fun x _ => uInv_invol x) (fun _ hx => uInv_ne (mem_uPart.mp hx).2)

lemma even_ncard_yPart2 (E : ℝ → EuclideanSpace ℝ (Fin 2) → EuclideanSpace ℝ (Fin 4))
    (E' : ℝ → EuclideanSpace ℝ (Fin 2) → EuclideanSpace ℝ (Fin 4))
    (V W : EuclideanSpace ℝ (Fin 3) → EuclideanSpace ℝ (Fin 4))
    (hseamV : ∀ y : EuclideanSpace ℝ (Fin 3), onSeam y → V (seamInv y) = V y)
    (hfin : (yPart (pairDiff2 E E' V W)).Finite) :
    Even (yPart (pairDiff2 E E' V W)).ncard :=
  even_ncard_of_involution hfin yInv (fun _ hx => yInv_mem2 E E' V W hseamV hx)
    (fun x _ => yInv_invol x) (fun _ hx => yInv_ne (mem_yPart.mp hx).2)

lemma even_ncard_zPart2 (E : ℝ → EuclideanSpace ℝ (Fin 2) → EuclideanSpace ℝ (Fin 4))
    (E' : ℝ → EuclideanSpace ℝ (Fin 2) → EuclideanSpace ℝ (Fin 4))
    (V W : EuclideanSpace ℝ (Fin 3) → EuclideanSpace ℝ (Fin 4))
    (hseamW : ∀ z : EuclideanSpace ℝ (Fin 3), onSeam z → W (seamInv z) = W z)
    (hfin : (zPart (pairDiff2 E E' V W)).Finite) :
    Even (zPart (pairDiff2 E E' V W)).ncard :=
  even_ncard_of_involution hfin zInv (fun _ hx => zInv_mem2 E E' V W hseamW hx)
    (fun x _ => zInv_invol x) (fun _ hx => zInv_ne (mem_zPart.mp hx).2)

/-! ## 5. The level faces are free -/

lemma lvlPart_eq_empty2 (E : ℝ → EuclideanSpace ℝ (Fin 2) → EuclideanSpace ℝ (Fin 4))
    (E' : ℝ → EuclideanSpace ℝ (Fin 2) → EuclideanSpace ℝ (Fin 4))
    (V W : EuclideanSpace ℝ (Fin 3) → EuclideanSpace ℝ (Fin 4))
    (havY : ∀ x ∈ Submission.Drive.unitBox 8, pairDiff2 E E' V W x = 0 →
      ftY2 x ≠ 0 ∧ ftY2 x ≠ 1)
    (havZ : ∀ x ∈ Submission.Drive.unitBox 8, pairDiff2 E E' V W x = 0 →
      ftZ2 x ≠ 0 ∧ ftZ2 x ≠ 1) :
    lvlPart (pairDiff2 E E' V W) = ∅ := by
  ext x
  constructor
  · intro hx
    rw [mem_lvlPart] at hx
    obtain ⟨hbz, hco⟩ := hx
    rw [mem_bdyZeros] at hbz
    obtain ⟨⟨hbox, -⟩, hzero⟩ := hbz
    obtain ⟨hy1, hy2⟩ := havY x hbox hzero
    obtain ⟨hz1, hz2⟩ := havZ x hbox hzero
    rcases hco with (h | h) | (h | h)
    · exact hy1 (by rw [ftY2_eq_coord]; exact h)
    · exact hy2 (by rw [ftY2_eq_coord]; exact h)
    · exact hz1 (by rw [ftZ2_eq_coord]; exact h)
    · exact hz2 (by rw [ftZ2_eq_coord]; exact h)
  · intro hx
    exact hx.elim

/-! ## 6. Smoothness of the symmetric pair difference map -/

theorem contDiff_pairDiff2 (E : ℝ → EuclideanSpace ℝ (Fin 2) → EuclideanSpace ℝ (Fin 4))
    (E' : ℝ → EuclideanSpace ℝ (Fin 2) → EuclideanSpace ℝ (Fin 4))
    (V W : EuclideanSpace ℝ (Fin 3) → EuclideanSpace ℝ (Fin 4))
    (hE : ContDiff ℝ Ctop (Function.uncurry E)) (hE' : ContDiff ℝ Ctop (Function.uncurry E'))
    (hV : ContDiff ℝ Ctop V) (hW : ContDiff ℝ Ctop W) :
    ContDiff ℝ Ctop (pairDiff2 E E' V W) := by
  have hSU : ContDiff ℝ Ctop (fun x : Amb 8 => (ftS x, ftU x)) := by
    refine ContDiff.prodMk ?_ ?_
    · show ContDiff ℝ Ctop (fun x : Amb 8 => x 0)
      fun_prop
    · show ContDiff ℝ Ctop
        (fun x : Amb 8 => WithLp.toLp 2 (fun i : Fin 2 => x ⟨1 + i.val, by omega⟩))
      fun_prop
  have hY : ContDiff ℝ Ctop (fun x : Amb 8 => ftY x) := by
    show ContDiff ℝ Ctop
      (fun x : Amb 8 => WithLp.toLp 2 (fun i : Fin 3 => x ⟨3 + i.val, by omega⟩))
    fun_prop
  have hZ : ContDiff ℝ Ctop (fun x : Amb 8 => ftZ x) := by
    show ContDiff ℝ Ctop
      (fun x : Amb 8 => WithLp.toLp 2 (fun i : Fin 3 => x ⟨6 + i.val, by omega⟩))
    fun_prop
  have h1 : ContDiff ℝ Ctop (fun x : Amb 8 => E (ftS x) (ftU x)) := hE.comp hSU
  have h2 : ContDiff ℝ Ctop (fun x : Amb 8 => E' (ftS x) (ftU x)) := hE'.comp hSU
  have h3 : ContDiff ℝ Ctop (fun x : Amb 8 => V (ftY x)) := hV.comp hY
  have h4 : ContDiff ℝ Ctop (fun x : Amb 8 => W (ftZ x)) := hW.comp hZ
  exact contDiff_pair44 (h1.sub h3) (h2.sub h4)

end PMB2

open PMB

theorem even_ncard_pairMeetBdry2
    (E : ℝ → EuclideanSpace ℝ (Fin 2) → EuclideanSpace ℝ (Fin 4))
    (E' : ℝ → EuclideanSpace ℝ (Fin 2) → EuclideanSpace ℝ (Fin 4))
    (V W : EuclideanSpace ℝ (Fin 3) → EuclideanSpace ℝ (Fin 4))
    (hE : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (Function.uncurry E))
    (hE' : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (Function.uncurry E'))
    (hV : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) V)
    (hW : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) W)
    (hreg : ∀ x ∈ Submission.Drive.unitBox 8, Work.Drive.pairDiff2 E E' V W x = 0 →
      Function.Surjective (fderiv ℝ (Work.Drive.pairDiff2 E E' V W) x))
    (hface : ∀ x ∈ Submission.Drive.unitBoxBdry 8, Work.Drive.pairDiff2 E E' V W x = 0 →
      ∃ i : Fin 9, (x i = 0 ∨ x i = 1) ∧ (∀ j : Fin 9, j ≠ i → x j ∈ Set.Ioo (0 : ℝ) 1) ∧
        Function.Surjective (fun v : {v : EuclideanSpace ℝ (Fin 9) // v i = 0} =>
          fderiv ℝ (Work.Drive.pairDiff2 E E' V W) x v.1))
    (hseamU : ∀ (s : ℝ) (u : EuclideanSpace ℝ (Fin 2)),
      Work.Drive.onSeam2 u → E s (Work.Drive.seamInv2 u) = E s u)
    (hseamU' : ∀ (s : ℝ) (u : EuclideanSpace ℝ (Fin 2)),
      Work.Drive.onSeam2 u → E' s (Work.Drive.seamInv2 u) = E' s u)
    (hseamV : ∀ y : EuclideanSpace ℝ (Fin 3), Work.Drive.onSeam y → V (Work.Drive.seamInv y) = V y)
    (hseamW : ∀ z : EuclideanSpace ℝ (Fin 3), Work.Drive.onSeam z → W (Work.Drive.seamInv z) = W z)
    (havY : ∀ x ∈ Submission.Drive.unitBox 8, Work.Drive.pairDiff2 E E' V W x = 0 →
      Work.Drive.ftY2 x ≠ 0 ∧ Work.Drive.ftY2 x ≠ 1)
    (havZ : ∀ x ∈ Submission.Drive.unitBox 8, Work.Drive.pairDiff2 E E' V W x = 0 →
      Work.Drive.ftZ2 x ≠ 0 ∧ Work.Drive.ftZ2 x ≠ 1) :
    Even ((Work.Drive.pairMeetSet2 E E' V W 0).ncard
      + (Work.Drive.pairMeetSet2 E E' V W 1).ncard) := by
  have hFd : ContDiff ℝ Ctop (pairDiff2 E E' V W) :=
    PMB2.contDiff_pairDiff2 E E' V W hE hE' hV hW
  have hsum := even_sum_ncard_labelMeet (pairDiff2 E E' V W) hFd hreg hface label9
  rw [Fin.sum_univ_five] at hsum
  have hfin : (bdyZeros (pairDiff2 E E' V W)).Finite :=
    (boxParity 8 (pairDiff2 E E' V W) hFd hreg hface).1
  have hfinU : (uPart (pairDiff2 E E' V W)).Finite :=
    hfin.subset (fun x hx => (mem_uPart.mp hx).1)
  have hfinY : (yPart (pairDiff2 E E' V W)).Finite :=
    hfin.subset (fun x hx => (mem_yPart.mp hx).1)
  have hfinZ : (zPart (pairDiff2 E E' V W)).Finite :=
    hfin.subset (fun x hx => (mem_zPart.mp hx).1)
  have hU : Even (uPart (pairDiff2 E E' V W)).ncard :=
    PMB2.even_ncard_uPart2 E E' V W hseamU hseamU' hfinU
  have hY : Even (yPart (pairDiff2 E E' V W)).ncard :=
    PMB2.even_ncard_yPart2 E E' V W hseamV hfinY
  have hZ : Even (zPart (pairDiff2 E E' V W)).ncard :=
    PMB2.even_ncard_zPart2 E E' V W hseamW hfinZ
  have h1 : Even (labelMeet (pairDiff2 E E' V W) label9 1).ncard := hU
  have h2 : Even (labelMeet (pairDiff2 E E' V W) label9 2).ncard := hY
  have h3 : Even (labelMeet (pairDiff2 E E' V W) label9 3).ncard := hZ
  have h4 : (labelMeet (pairDiff2 E E' V W) label9 4).ncard = 0 := by
    change (lvlPart (pairDiff2 E E' V W)).ncard = 0
    rw [PMB2.lvlPart_eq_empty2 E E' V W havY havZ, Set.ncard_empty]
  have h4e : Even (labelMeet (pairDiff2 E E' V W) label9 4).ncard := by
    rw [h4]
    exact ⟨0, rfl⟩
  have hfin0 : (endFace (pairDiff2 E E' V W) 0).Finite :=
    hfin.subset (fun x hx => hx.1)
  have hfin1 : (endFace (pairDiff2 E E' V W) 1).Finite :=
    hfin.subset (fun x hx => hx.1)
  have h0 : (labelMeet (pairDiff2 E E' V W) label9 0).ncard
      = (pairMeetSet2 E E' V W 0).ncard + (pairMeetSet2 E E' V W 1).ncard := by
    rw [labelMeet_zero_eq (pairDiff2 E E' V W)]
    rw [Set.ncard_union_eq (disjoint_endFace (pairDiff2 E E' V W)) hfin0 hfin1]
    rw [ncard_endFace_pairDiff2 E E' V W
        (show (0 : ℝ) = 0 ∨ (0 : ℝ) = 1 from Or.inl rfl),
      ncard_endFace_pairDiff2 E E' V W
        (show (1 : ℝ) = 0 ∨ (1 : ℝ) = 1 from Or.inr rfl)]
  have ha : Even (labelMeet (pairDiff2 E E' V W) label9 0).ncard :=
    even_of_even_add_four hsum h1 h2 h3 h4e
  rwa [h0] at ha

end

end Work.Drive
