import Mathlib
import Submission.Work.Stems.Hur2b.Gluing3
import Submission.Work.Stems.Hur2b.Assembly
import Submission.Work.Stems.Hur2b.PsiCancel
import Submission.Work.Stems.Hur2b.psiFunCancel_seam_agree

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

/-!
# The cancellation family of the gluing of `∂I³`

`gluingMap x₀ τ : ∂I³ → X` glues the six filled faces `Ψ(τ_{i,b})` of a 3-cube.  This file builds
Hutchings' cancellation homotopy for the *glued* map: a family

* `cancelGluing` deforms `gluingMap` to the "clamp collapse" `τ ∘ clampFun` restricted to `∂I³`
  (each face's `K₁`-fillings are cancelled onto the corresponding cube edge); the seam consistency
  is `psiFunCancel_seam_agree`,

and the clamped coordinate map

* `clampFun : ∂I³ → I³` (each face is clamped onto its core square).

With the radial shrink of the cube (`τ((1-s)·x)`) this gives the full cancellation family
`gluingCancelFamily`, which is the input of `Work.Stems.Hur2b.model_homotopic_const`.
-/

open scoped unitInterval Topology

namespace Work.Stems.Hur2b

open Work.Stems.Cubical Work.Stems.Hur2

noncomputable section

variable {X : Type} [TopologicalSpace X] [SimplyConnectedSpace X]

/-! ## Basic coordinate facts -/

theorem bval_eq (b : Fin 2) : bval b = (if (b : ℕ) = 0 then 0 else 1 : unitInterval) := by
  fin_cases b <;> rfl

/-- `clamp (2·b - 1/2) = b` for `b ∈ {0,1}`. -/
theorem clamp_two_bval (b : Fin 2) : clamp (2 * (bval b : ℝ) - 1/2) = bval b := by
  have hb : bval b = 0 ∨ bval b = 1 := by
    rcases b with ⟨n, hn⟩
    interval_cases n
    · exact Or.inl bval_zero
    · exact Or.inr bval_one
  rcases hb with h | h
  · rw [h, show (2 * ((0 : unitInterval) : ℝ) - 1/2) = -(1/2) by rw [coe_zero_I]; norm_num]
    exact clamp_of_le_zero (by norm_num)
  · rw [h, show (2 * ((1 : unitInterval) : ℝ) - 1/2) = 3/2 by rw [coe_one_I]; norm_num]
    exact clamp_of_ge_one (by norm_num)

/-- The clamp of the square to its core. -/
def clampPair (t : IC 2) : IC 2 :=
  pair2 (clamp (2 * (t 0 : ℝ) - 1/2)) (clamp (2 * (t 1 : ℝ) - 1/2))

theorem clampPair_apply (t : IC 2) :
    clampPair t = pair2 (clamp (2 * (t 0 : ℝ) - 1/2)) (clamp (2 * (t 1 : ℝ) - 1/2)) := rfl

theorem continuous_clampPair : Continuous clampPair :=
  continuous_pair2 (continuous_clamp.comp (by fun_prop))
    (continuous_clamp.comp (by fun_prop))

/-! ## The clamped point of `∂I³` -/

/-- **The clamped point of `∂I³`**: the point whose "carrier" face keeps its frozen coordinate and
whose other coordinates are the clamped ones. -/
def clampFun (p : Bdy3) : IC 3 := fun k : Fin 3 =>
  if k = whichFst p.1 p.2 then bval (whichSnd p.1 p.2) else clamp (2 * (p.1 k : ℝ) - 1/2)

/-- The free (non-frozen) index together with the component of the face coordinates it carries. -/
theorem coordOf_apply_succAbove {i : Fin 3} {j : Fin 2} (z : IC 3) :
    (coordOf i z) j = z (i.succAbove j) := rfl

/-- On a face of the cube, `clampFun` is given by the face's own clamped coordinates. -/
theorem clampFun_eq_faceFun {p : Bdy3} {i : Fin 3} {b : Fin 2} (h : p.1 ∈ faceSet3 i b) :
    clampFun p = faceFun i (bval b) (clampPair (coordOf i p.1)) := by
  funext k
  by_cases hk : k = i
  · rw [hk, faceFun, Fin.succAbove_cases_eq_insertNth, Fin.insertNth_apply_same]
    unfold clampFun
    by_cases hw : i = whichFst p.1 p.2
    · have hb : whichSnd p.1 p.2 = b :=
        bval_injective (by rw [← whichFace_spec p.1 p.2, ← hw]; exact h)
      rw [if_pos hw, hb]
    · rw [if_neg hw, show p.1 i = bval b from h, clamp_two_bval]
  · obtain ⟨j, hj⟩ := Fin.exists_succAbove_eq hk
    have hface : faceFun i (bval b) (clampPair (coordOf i p.1)) k
        = clamp (2 * (p.1 k : ℝ) - 1/2) := by
      rw [faceFun, Fin.succAbove_cases_eq_insertNth, ← hj, Fin.insertNth_apply_succAbove]
      fin_cases j <;> simp [clampPair, pair2, coordOf]
    rw [hface]
    unfold clampFun
    by_cases hw : k = whichFst p.1 p.2
    · rw [if_pos hw, hw, whichFace_spec p.1 p.2, clamp_two_bval]
    · rw [if_neg hw]

theorem continuousOn_clampFun (i : Fin 3) (b : Fin 2) :
    ContinuousOn clampFun (faceSub i b) := by
  have hcont : Continuous fun p : Bdy3 => faceFun i (bval b) (clampPair (coordOf i p.1)) :=
    (faceCM i (bval b)).continuous.comp
      (continuous_clampPair.comp (continuous_pi fun j =>
        (continuous_apply (i.succAbove j)).comp continuous_subtype_val))
  exact hcont.continuousOn.congr (fun p hp => clampFun_eq_faceFun hp)

/-- **`clampFun` is continuous.** -/
theorem continuous_clampFun : Continuous clampFun := by
  rw [← continuousOn_univ]
  rw [show (Set.univ : Set Bdy3) = faceSub 0 0 ∪ (faceSub 0 1 ∪ (faceSub 1 0
        ∪ (faceSub 1 1 ∪ (faceSub 2 0 ∪ faceSub 2 1)))) from by
    ext p
    constructor
    · intro _
      obtain ⟨i, b, hb⟩ := exists_face p.1 p.2
      fin_cases i <;> fin_cases b <;> simp_all [faceSub, faceSet3]
    · intro _; trivial]
  rw [continuousOn_union_iff_of_isClosed (isClosed_faceSub 0 0)
    ((isClosed_faceSub 0 1).union ((isClosed_faceSub 1 0).union
      ((isClosed_faceSub 1 1).union ((isClosed_faceSub 2 0).union (isClosed_faceSub 2 1)))))]
  refine ⟨continuousOn_clampFun 0 0, ?_⟩
  rw [continuousOn_union_iff_of_isClosed (isClosed_faceSub 0 1)
    ((isClosed_faceSub 1 0).union ((isClosed_faceSub 1 1).union
      ((isClosed_faceSub 2 0).union (isClosed_faceSub 2 1))))]
  refine ⟨continuousOn_clampFun 0 1, ?_⟩
  rw [continuousOn_union_iff_of_isClosed (isClosed_faceSub 1 0)
    ((isClosed_faceSub 1 1).union ((isClosed_faceSub 2 0).union (isClosed_faceSub 2 1)))]
  refine ⟨continuousOn_clampFun 1 0, ?_⟩
  rw [continuousOn_union_iff_of_isClosed (isClosed_faceSub 1 1)
    ((isClosed_faceSub 2 0).union (isClosed_faceSub 2 1))]
  exact ⟨continuousOn_clampFun 1 1, (continuousOn_union_iff_of_isClosed (isClosed_faceSub 2 0)
    (isClosed_faceSub 2 1)).mpr ⟨continuousOn_clampFun 2 0, continuousOn_clampFun 2 1⟩⟩

/-! ## The cancellation of the gluing -/

/-- **The cancellation of the gluing**, at parameter `s`: on the face `(i,b)` the filling `Ψ(τ_{i,b})`
has its `K₁`-fillings cancelled to parameter `s`. -/
def cancelGluingFun (x₀ : X) (τ : C(IC 3, X)) (s : unitInterval) (p : Bdy3) : X :=
  psiFunCancel x₀ (face3 τ (whichFst p.1 p.2) (whichSnd p.1 p.2)) s
    (coordOf (whichFst p.1 p.2) p.1)

/-- On a face of the cube, the cancellation is given by the face's own family.  Two distinct faces
meeting along a cube edge give the same value by `psiFunCancel_seam_agree`. -/
theorem cancelGluingFun_eq_of_mem (x₀ : X) (τ : C(IC 3, X)) (s : unitInterval) {p : Bdy3}
    {i : Fin 3} {b : Fin 2} (h : p.1 ∈ faceSet3 i b) :
    cancelGluingFun x₀ τ s p = psiFunCancel x₀ (face3 τ i b) s (coordOf i p.1) := by
  unfold cancelGluingFun
  by_cases hcase : whichFst p.1 p.2 = i ∧ whichSnd p.1 p.2 = b
  · obtain ⟨h1, h2⟩ := hcase; rw [h1, h2]
  · have hne : whichFst p.1 p.2 ≠ i := by
      intro heq
      exact hcase ⟨heq, bval_injective (by rw [← whichFace_spec p.1 p.2, heq]; exact h)⟩
    have hz1 : p.1 (whichFst p.1 p.2)
        = (if ((whichSnd p.1 p.2 : Fin 2) : ℕ) = 0 then 0 else 1 : unitInterval) := by
      rw [whichFace_spec p.1 p.2]; exact bval_eq _
    have hz2 : p.1 i = (if (b : ℕ) = 0 then 0 else 1 : unitInterval) := by
      rw [show p.1 i = bval b from h]; exact bval_eq b
    exact psiFunCancel_seam_agree x₀ τ hne hz1 hz2 s

/-- A function on `∂I³ × I` which is continuous on each `(face) × I` is continuous. -/
theorem continuous_of_faces {f : Bdy3 × unitInterval → X}
    (h : ∀ (i : Fin 3) (b : Fin 2),
      ContinuousOn f ((faceSub i b) ×ˢ (Set.univ : Set unitInterval))) :
    Continuous f := by
  rw [← continuousOn_univ]
  rw [show (Set.univ : Set (Bdy3 × unitInterval)) =
      ((faceSub 0 0 ×ˢ (Set.univ : Set unitInterval)) ∪ ((faceSub 0 1 ×ˢ (Set.univ : Set unitInterval)) ∪
        ((faceSub 1 0 ×ˢ (Set.univ : Set unitInterval)) ∪
        ((faceSub 1 1 ×ˢ (Set.univ : Set unitInterval)) ∪ ((faceSub 2 0 ×ˢ (Set.univ : Set unitInterval)) ∪
          (faceSub 2 1 ×ˢ (Set.univ : Set unitInterval))))))) from by
    ext q
    simp only [Set.mem_univ, Set.mem_union, Set.mem_prod, and_true, true_iff]
    obtain ⟨i, b, hb⟩ := exists_face q.1.1 q.1.2
    fin_cases i <;> fin_cases b <;> simp_all [faceSub, faceSet3]]
  rw [continuousOn_union_iff_of_isClosed ((isClosed_faceSub 0 0).prod isClosed_univ)
    (((isClosed_faceSub 0 1).prod isClosed_univ).union
      (((isClosed_faceSub 1 0).prod isClosed_univ).union
        (((isClosed_faceSub 1 1).prod isClosed_univ).union
          (((isClosed_faceSub 2 0).prod isClosed_univ).union
            ((isClosed_faceSub 2 1).prod isClosed_univ)))))]
  refine ⟨h 0 0, ?_⟩
  rw [continuousOn_union_iff_of_isClosed ((isClosed_faceSub 0 1).prod isClosed_univ)
    (((isClosed_faceSub 1 0).prod isClosed_univ).union
      (((isClosed_faceSub 1 1).prod isClosed_univ).union
        (((isClosed_faceSub 2 0).prod isClosed_univ).union
          ((isClosed_faceSub 2 1).prod isClosed_univ))))]
  refine ⟨h 0 1, ?_⟩
  rw [continuousOn_union_iff_of_isClosed ((isClosed_faceSub 1 0).prod isClosed_univ)
    (((isClosed_faceSub 1 1).prod isClosed_univ).union
      (((isClosed_faceSub 2 0).prod isClosed_univ).union
        ((isClosed_faceSub 2 1).prod isClosed_univ)))]
  refine ⟨h 1 0, ?_⟩
  rw [continuousOn_union_iff_of_isClosed ((isClosed_faceSub 1 1).prod isClosed_univ)
    (((isClosed_faceSub 2 0).prod isClosed_univ).union ((isClosed_faceSub 2 1).prod isClosed_univ))]
  exact ⟨h 1 1, (continuousOn_union_iff_of_isClosed ((isClosed_faceSub 2 0).prod isClosed_univ)
    ((isClosed_faceSub 2 1).prod isClosed_univ)).mpr ⟨h 2 0, h 2 1⟩⟩

theorem continuousOn_cancelGluingFun (x₀ : X) (τ : C(IC 3, X)) (i : Fin 3) (b : Fin 2) :
    ContinuousOn (fun q : Bdy3 × unitInterval => cancelGluingFun x₀ τ q.2 q.1)
      ((faceSub i b) ×ˢ (Set.univ : Set unitInterval)) := by
  have hcont : Continuous fun q : Bdy3 × unitInterval =>
      psiFunCancel x₀ (face3 τ i b) q.2 (coordOf i q.1.1) :=
    (continuous_psiFunCancel x₀ (face3 τ i b)).comp
      (continuous_snd.prodMk (continuous_pi fun j =>
        (continuous_apply (i.succAbove j)).comp (continuous_subtype_val.comp continuous_fst)))
  exact hcont.continuousOn.congr (fun q hq => cancelGluingFun_eq_of_mem x₀ τ q.2 hq.1)

/-- **The cancellation of the gluing is continuous.** -/
theorem continuous_cancelGluing (x₀ : X) (τ : C(IC 3, X)) :
    Continuous fun q : Bdy3 × unitInterval => cancelGluingFun x₀ τ q.2 q.1 :=
  continuous_of_faces fun i b => continuousOn_cancelGluingFun x₀ τ i b

/-! ## The two endpoints of the cancellation -/

theorem face3_eq_comp (τ : C(IC 3, X)) (i : Fin 3) (b : Fin 2) :
    face3 τ i b = τ.comp (faceCM i (bval b)) := by
  rw [face3, bval_eq b]
  rfl

theorem whichFace_mem (p : Bdy3) :
    p.1 ∈ faceSet3 (whichFst p.1 p.2) (whichSnd p.1 p.2) :=
  whichFace_spec p.1 p.2

/-- At `s = 0` the cancellation is the gluing. -/
theorem cancelGluing_zero (x₀ : X) (τ : C(IC 3, X)) (p : Bdy3) :
    cancelGluingFun x₀ τ 0 p = gluingMap x₀ τ p := by
  show psiFunCancel x₀ (face3 τ (whichFst p.1 p.2) (whichSnd p.1 p.2)) 0
      (coordOf (whichFst p.1 p.2) p.1) = gluingFun x₀ τ p.1 p.2
  rw [psiFunCancel_zero, face3_eq_comp]
  rfl

/-- At `s = 1` the cancellation is the clamped map `τ ∘ clampFun`. -/
theorem cancelGluing_one (x₀ : X) (τ : C(IC 3, X)) (p : Bdy3) :
    cancelGluingFun x₀ τ 1 p = τ (clampFun p) := by
  show psiFunCancel x₀ (face3 τ (whichFst p.1 p.2) (whichSnd p.1 p.2)) 1
      (coordOf (whichFst p.1 p.2) p.1) = τ (clampFun p)
  rw [psiFunCancel_one, sigmaClamp_apply, face3_eq_comp,
    clampFun_eq_faceFun (whichFace_mem p)]
  rfl

/-! ## The radial shrink of the clamped map -/

/-- The straight-line contraction of the cube to its origin. -/
def shrinkPt (s : unitInterval) (x : IC 3) : IC 3 := fun i =>
  ⟨(1 - (s : ℝ)) * (x i : ℝ), by
    have hs := s.2; have hx := (x i).2
    constructor <;> nlinarith [hs.1, hs.2, hx.1, hx.2]⟩

@[simp] theorem shrinkPt_zero (x : IC 3) : shrinkPt 0 x = x := by
  funext i; exact Subtype.ext (by simp [shrinkPt])

@[simp] theorem shrinkPt_one (x : IC 3) : shrinkPt 1 x = 0 := by
  funext i; exact Subtype.ext (by simp [shrinkPt])

theorem continuous_shrinkPt (x : IC 3) : Continuous fun s : unitInterval => shrinkPt s x :=
  continuous_pi fun i => Continuous.subtype_mk
    (f := fun s : unitInterval => (1 - (s : ℝ)) * (x i : ℝ))
    ((continuous_const.sub continuous_subtype_val).mul continuous_const)
    (fun s => by
      have hs := s.2; have hx := (x i).2
      exact ⟨by nlinarith [hs.1, hs.2, hx.1, hx.2],
             by nlinarith [hs.1, hs.2, hx.1, hx.2]⟩)

/-- The clamped map shrunk radially. -/
def shrinkFun (x₀ : X) (τ : C(IC 3, X)) (s : unitInterval) (p : Bdy3) : X :=
  τ (shrinkPt s (clampFun p))

theorem continuous_shrinkFun (x₀ : X) (τ : C(IC 3, X)) :
    Continuous fun q : Bdy3 × unitInterval => shrinkFun x₀ τ q.2 q.1 :=
  τ.continuous.comp (continuous_pi fun i => Continuous.subtype_mk
    (f := fun q : Bdy3 × unitInterval => (1 - (q.2 : ℝ)) * (clampFun q.1 i : ℝ))
    ((continuous_const.sub continuous_snd.subtype_val).mul
      ((continuous_apply i).comp (continuous_clampFun.comp continuous_fst)).subtype_val)
    (fun q => by
      have hs := q.2.2; have hx := (clampFun q.1 i).2
      exact ⟨by nlinarith [hs.1, hs.2, hx.1, hx.2],
             by nlinarith [hs.1, hs.2, hx.1, hx.2]⟩))

/-! ## The cancellation family -/

theorem isClosed_half1 : IsClosed {q : Bdy3 × unitInterval | (q.2 : ℝ) ≤ 1/2} :=
  isClosed_le (by fun_prop) continuous_const

theorem isClosed_half2 : IsClosed {q : Bdy3 × unitInterval | (1/2 : ℝ) ≤ (q.2 : ℝ)} :=
  isClosed_le continuous_const (by fun_prop)

/-- **Hutchings' cancellation family of the gluing of `∂I³`**: it deforms `gluingMap` to the
clamped map and then collapses it radially to the constant `τ 0`. -/
def gluingCancelFamily (x₀ : X) (τ : C(IC 3, X)) : C(Bdy3 × unitInterval, X) where
  toFun q := if (q.2 : ℝ) ≤ 1/2 then cancelGluingFun x₀ τ (clamp (2 * (q.2 : ℝ))) q.1
    else shrinkFun x₀ τ (clamp (2 * (q.2 : ℝ) - 1)) q.1
  continuous_toFun := by
    have hcov : (Set.univ : Set (Bdy3 × unitInterval))
        = {q | (q.2 : ℝ) ≤ 1/2} ∪ {q | (1/2 : ℝ) ≤ (q.2 : ℝ)} := by
      ext q
      simp only [Set.mem_univ, Set.mem_union, Set.mem_setOf_eq, true_iff]
      rcases le_or_gt ((q.2 : ℝ)) (1/2) with h | h
      · exact Or.inl h
      · exact Or.inr (le_of_lt h)
    have hc1 : Continuous fun q : Bdy3 × unitInterval =>
        (q.1, clamp (2 * (q.2 : ℝ))) :=
      Continuous.prodMk (f := fun q : Bdy3 × unitInterval => q.1)
        (g := fun q : Bdy3 × unitInterval => clamp (2 * (q.2 : ℝ))) continuous_fst
        (continuous_clamp.comp (continuous_const.mul
          (continuous_subtype_val.comp continuous_snd)))
    have hc2 : Continuous fun q : Bdy3 × unitInterval =>
        (q.1, clamp (2 * (q.2 : ℝ) - 1)) :=
      Continuous.prodMk (f := fun q : Bdy3 × unitInterval => q.1)
        (g := fun q : Bdy3 × unitInterval => clamp (2 * (q.2 : ℝ) - 1)) continuous_fst
        (continuous_clamp.comp (((continuous_const.mul
          (continuous_subtype_val.comp continuous_snd)).sub continuous_const)))
    rw [← continuousOn_univ, hcov,
      continuousOn_union_iff_of_isClosed isClosed_half1 isClosed_half2]
    constructor
    · refine ((continuous_cancelGluing x₀ τ).comp hc1).continuousOn.congr (fun q hq => ?_)
      show (if ((q.2 : ℝ) ≤ 1/2) then cancelGluingFun x₀ τ (clamp (2 * (q.2 : ℝ))) q.1
          else shrinkFun x₀ τ (clamp (2 * (q.2 : ℝ) - 1)) q.1)
          = cancelGluingFun x₀ τ (clamp (2 * (q.2 : ℝ))) q.1
      rw [if_pos (show (q.2 : ℝ) ≤ 1/2 from hq)]
    · refine ((continuous_shrinkFun x₀ τ).comp hc2).continuousOn.congr (fun q hq => ?_)
      rcases lt_or_eq_of_le (show (1/2 : ℝ) ≤ (q.2 : ℝ) from hq) with h | h
      · show (if ((q.2 : ℝ) ≤ 1/2) then cancelGluingFun x₀ τ (clamp (2 * (q.2 : ℝ))) q.1
            else shrinkFun x₀ τ (clamp (2 * (q.2 : ℝ) - 1)) q.1)
            = shrinkFun x₀ τ (clamp (2 * (q.2 : ℝ) - 1)) q.1
        rw [if_neg (not_le.mpr h)]
      · show (if ((q.2 : ℝ) ≤ 1/2) then cancelGluingFun x₀ τ (clamp (2 * (q.2 : ℝ))) q.1
            else shrinkFun x₀ τ (clamp (2 * (q.2 : ℝ) - 1)) q.1)
            = shrinkFun x₀ τ (clamp (2 * (q.2 : ℝ) - 1)) q.1
        rw [if_pos (le_of_eq h.symm),
          show clamp (2 * (q.2 : ℝ)) = 1 from by
            rw [← h, show (2 * (1/2 : ℝ)) = 1 by norm_num, clamp_one],
          show clamp (2 * (q.2 : ℝ) - 1) = 0 from by
            rw [← h, show (2 * (1/2 : ℝ) - 1) = 0 by norm_num, clamp_zero],
          cancelGluing_one, shrinkFun, shrinkPt_zero]

theorem gluingCancelFamily_zero (x₀ : X) (τ : C(IC 3, X)) (p : Bdy3) :
    gluingCancelFamily x₀ τ (p, 0) = gluingMap x₀ τ p := by
  show (if (((0 : unitInterval) : ℝ) ≤ 1/2) then
    cancelGluingFun x₀ τ (clamp (2 * ((0 : unitInterval) : ℝ))) p
    else shrinkFun x₀ τ (clamp (2 * ((0 : unitInterval) : ℝ) - 1)) p) = _
  rw [if_pos (by norm_num),
    show clamp (2 * ((0 : unitInterval) : ℝ)) = 0 from by rw [coe_zero_I, mul_zero, clamp_zero],
    cancelGluing_zero]

theorem gluingCancelFamily_one (x₀ : X) (τ : C(IC 3, X)) (p : Bdy3) :
    gluingCancelFamily x₀ τ (p, 1) = τ 0 := by
  have hcl : clamp (2 * ((1 : unitInterval) : ℝ) - 1) = 1 := by
    rw [coe_one_I]
    rw [show (2 * (1:ℝ) - 1) = 1 by norm_num, clamp_one]
  show (if (((1 : unitInterval) : ℝ) ≤ 1/2) then
    cancelGluingFun x₀ τ (clamp (2 * ((1 : unitInterval) : ℝ))) p
    else shrinkFun x₀ τ (clamp (2 * ((1 : unitInterval) : ℝ) - 1)) p) = _
  rw [if_neg (by norm_num), hcl]
  show τ (shrinkPt 1 (clampFun p)) = τ 0
  rw [shrinkPt_one]


end

end Work.Stems.Hur2b
