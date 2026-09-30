import Mathlib
import Submission.Work.RatHurewicz.CubicalDefs
import Submission.Work.RatHurewicz.fillingFamilyConst
import Submission.Work.RatHurewicz.genLoop_eq_one_of_free_homotopic_const
import Submission.Work.RatHurewicz.boundaryMap
import Submission.Work.RatHurewicz.PinchGeom
import Submission.Work.RatHurewicz.geomPinch
import Submission.Work.Stems.Hur2b.Assembly
import Submission.Work.Stems.Hur2b.genLoop_homotopic_const_of_unbased

/-!
# The based-ification `Psi` of cubes, from a filling family

From a filling family `K : Work.RatHurewicz.Tower x₀ N` (Hutchings' `K`-operator,
`Submission/Work/RatHurewicz/fillingFamilyConst.lean`) with `m + 1 ≤ N` we build the
*based-ification*

  `Psi : C(I^{m+2}, X) → GenLoop (Fin (m+2)) X x₀`

of the cubical Hurewicz construction (`_ztmp_hur/hutch.txt` §2):

* `Psi s = B_s ∘ iota`, where `B_s : ∂I^{m+3} → X` is the *boundary data* of `s` — the gluing of
  the top face `s`, the bottom face `x₀` and the `K (m+1)`-fillings of the faces of `s`
  (`exists_boundaryData`, which is `Work.RatHurewicz.boundaryMap` at `k = m`) — and
  `iota : I^{m+2} → ∂I^{m+3}` is the pinch inclusion (`Work.RatHurewicz.PinchGeom.iota`), whose
  image is the complement of the open bottom face.  Since `iota` maps `∂I^{m+2}` into the bottom
  face, `Psi s` is a `GenLoop`.

The two properties proved here are:

* `Psi_apply_of_based` / `Psi_section`: for a cube `s` that is `x₀` on the boundary (in particular
  for a based cube `p`), `Psi s` is the reparametrisation `s ∘ radialPt` of `s`; and since
  `radialPt` is homotopic to the identity through maps taking the boundary to itself,
  `Work.Stems.Hur2b.genLoop_homotopic_comp_of_homotopic_id` gives `GenLoop.Homotopic (Psi p.1) p`.
* `Psi_const`: `Psi (cconst (m+2) x₀) = GenLoop.const`.
-/

open scoped unitInterval Topology
open Work.Stems.Cubical

namespace Work.RatHurewicz

noncomputable section

variable {X : Type} [TopologicalSpace X]

/-! ## The boundary data of a cube, from the tower -/

/-- The boundary data of an `(m+2)`-cube from a tower defined up to level `m+1`: a map on
`∂I^{m+3}` whose top face is `s`, whose bottom face is the constant cube at `x₀`, and whose side
faces are the `K (m+1)`-fillings of the faces of `s`.  (This is `boundaryMap` at `k = m`.) -/
theorem exists_boundaryData (N m : ℕ) {x₀ : X} (K : Tower x₀ N) (hN : m + 1 ≤ N)
    (s : C(IC (m + 2), X)) :
    ∃ B : C(↥(Cube.boundary (Fin (m + 3))), X),
      B.comp (bface (m + 2) (Fin.last (m + 2)) 1) = s ∧
      B.comp (bface (m + 2) (Fin.last (m + 2)) 0) = cconst (m + 2) x₀ ∧
      (∀ (j : Fin (m + 2)) (b : Fin 2),
        B.comp (bface (m + 2) (Fin.castSucc j) b)
          = K.Kf (m + 1) (s.comp (faceCM j (cval b)))) := by
  obtain ⟨B, h1, h2, h3⟩ := boundaryMap (k := m) x₀ (K.Kf (m + 1)) (K.Kf m) s
    (fun q => K.hα (m + 1) hN q) (fun q j b => by
      have h := K.hβ m hN q j
      fin_cases b
      · simpa using h.1
      · simpa using h.2)
  exact ⟨B, h1, h2, h3⟩

/-- Evaluating boundary data on a face: if `z` lies on the face `{z i = cval b}` and the face data
is `q`, then `B z = q (delG (m+2) i z)`. -/
theorem boundaryData_apply_face {m : ℕ} {B : C(↥(Cube.boundary (Fin (m + 3))), X)}
    {q : C(IC (m + 2), X)} {i : Fin (m + 3)} {b : Fin 2}
    (h : B.comp (bface (m + 2) i b) = q) {z : ↥(Cube.boundary (Fin (m + 3)))}
    (hz : (z : IC (m + 3)) i = cval b) : B z = q (delG (m + 2) i z) := by
  have hz' : z = bface (m + 2) i b (delG (m + 2) i (z : IC (m + 3))) :=
    Subtype.ext (delG_faceCM (n := m + 2) i (u := (z : IC (m + 3))) hz).symm
  have hz1 : B z = B (bface (m + 2) i b (delG (m + 2) i (z : IC (m + 3)))) := by
    conv_lhs => rw [hz']
  calc B z = B (bface (m + 2) i b (delG (m + 2) i (z : IC (m + 3)))) := hz1
    _ = (B.comp (bface (m + 2) i b)) (delG (m + 2) i (z : IC (m + 3))) := rfl
    _ = q (delG (m + 2) i (z : IC (m + 3))) := by rw [h]

/-! ## The based-ification -/

/-- The boundary data of an `(m+2)`-cube, chosen from the tower. -/
def PsiB (N m : ℕ) {x₀ : X} (K : Tower x₀ N) (hN : m + 1 ≤ N) (s : C(IC (m + 2), X)) :
    C(↥(Cube.boundary (Fin (m + 3))), X) :=
  Classical.choose (exists_boundaryData N m K hN s)

theorem PsiB_top (N m : ℕ) {x₀ : X} (K : Tower x₀ N) (hN : m + 1 ≤ N)
    (s : C(IC (m + 2), X)) :
    (PsiB N m K hN s).comp (bface (m + 2) (Fin.last (m + 2)) 1) = s :=
  (Classical.choose_spec (exists_boundaryData N m K hN s)).1

theorem PsiB_bot (N m : ℕ) {x₀ : X} (K : Tower x₀ N) (hN : m + 1 ≤ N)
    (s : C(IC (m + 2), X)) :
    (PsiB N m K hN s).comp (bface (m + 2) (Fin.last (m + 2)) 0) = cconst (m + 2) x₀ :=
  (Classical.choose_spec (exists_boundaryData N m K hN s)).2.1

theorem PsiB_side (N m : ℕ) {x₀ : X} (K : Tower x₀ N) (hN : m + 1 ≤ N)
    (s : C(IC (m + 2), X)) (j : Fin (m + 2)) (b : Fin 2) :
    (PsiB N m K hN s).comp (bface (m + 2) (Fin.castSucc j) b)
      = K.Kf (m + 1) (s.comp (faceCM j (cval b))) :=
  (Classical.choose_spec (exists_boundaryData N m K hN s)).2.2 j b

/-- The value of the boundary data on a **side** face. -/
theorem PsiB_apply_side (N m : ℕ) {x₀ : X} (K : Tower x₀ N) (hN : m + 1 ≤ N)
    (s : C(IC (m + 2), X)) {j : Fin (m + 2)} {b : Fin 2}
    {z : ↥(Cube.boundary (Fin (m + 3)))} (hz : (z : IC (m + 3)) (Fin.castSucc j) = cval b) :
    PsiB N m K hN s z
      = (K.Kf (m + 1) (s.comp (faceCM j (cval b)))) (delG (m + 2) (Fin.castSucc j) z) :=
  boundaryData_apply_face (i := Fin.castSucc j) (b := b) (PsiB_side N m K hN s j b) hz

/-- The value of the boundary data on the **bottom** face. -/
theorem PsiB_apply_bottom (N m : ℕ) {x₀ : X} (K : Tower x₀ N) (hN : m + 1 ≤ N)
    (s : C(IC (m + 2), X)) {z : ↥(Cube.boundary (Fin (m + 3)))}
    (hz : (z : IC (m + 3)) (Fin.last (m + 2)) = 0) : PsiB N m K hN s z = x₀ := by
  have h := boundaryData_apply_face (m := m) (i := Fin.last (m + 2)) (b := 0)
    (PsiB_bot N m K hN s) (z := z) (by simpa using hz)
  rw [h, delG_last]
  rfl

/-- The based-ification of an `(m+2)`-cube: the boundary data composed with the pinch inclusion
`iota`, which is a `GenLoop` because `iota` maps `∂I^{m+2}` into the bottom face. -/
def Psi (N m : ℕ) {x₀ : X} (K : Tower x₀ N) (hN : m + 1 ≤ N) :
    C(IC (m + 2), X) → GenLoop (Fin (m + 2)) X x₀ :=
  fun s => ⟨(PsiB N m K hN s).comp (iota (m + 2) (by omega)), by
    intro u hu
    exact PsiB_apply_bottom N m K hN s ((geomPinch (m + 2) (by omega)).2.1 u hu)⟩

@[simp] theorem Psi_apply (N m : ℕ) {x₀ : X} (K : Tower x₀ N) (hN : m + 1 ≤ N)
    (s : C(IC (m + 2), X)) (u : IC (m + 2)) :
    (Psi N m K hN s) u = PsiB N m K hN s (iota (m + 2) (by omega) u) :=
  rfl

/-- A based cube is unchanged (in class) by composing with a self-map of the cube that fixes the
boundary up to a homotopy through boundary-preserving maps.  (Copy of
`Work.Stems.Hur2b.genLoop_homotopic_comp_of_homotopic_id` without the simple connectivity
hypothesis.) -/
theorem genLoop_homotopic_comp_of_id {Y : Type} [TopologicalSpace Y] {y₀ : Y}
    (k : ℕ) [NeZero k] (φ : C(IC k, IC k))
    (hφ : ∀ y ∈ Cube.boundary (Fin k), φ y ∈ Cube.boundary (Fin k))
    (H : C(IC k × unitInterval, IC k))
    (h0 : ∀ y, H (y, 0) = φ y) (h1 : ∀ y, H (y, 1) = y)
    (Hb : ∀ y ∈ Cube.boundary (Fin k), ∀ t, H (y, t) ∈ Cube.boundary (Fin k))
    (p : GenLoop (Fin k) Y y₀) :
    GenLoop.Homotopic ⟨p.1.comp φ, fun y hy => p.2 (φ y) (hφ y hy)⟩ p := by
  refine ⟨⟨⟨fun z : unitInterval × IC k => p.1 (H (z.2, z.1)), ?_⟩, ?_, ?_⟩, ?_⟩
  · exact p.1.continuous.comp (H.continuous.comp (continuous_snd.prodMk continuous_fst))
  · intro y
    show p.1 (H (y, 0)) = p.1 (φ y)
    rw [h0]
  · intro y
    show p.1 (H (y, 1)) = p.1 y
    rw [h1]
  · intro t y hy
    show p.1 (H (y, t)) = p.1 (φ y)
    rw [p.2 (H (y, t)) (Hb y hy t), p.2 (φ y) (hφ y hy)]

/-! ## Facts about the pinch geometry -/

/-- The "space part" of `iota u` is `radialPt u`. -/
theorem initC_iotaFun (m : ℕ) (hm : 1 ≤ m) (u : IC m) :
    initC m (iotaFun m hm u) = radialPt m hm u := by
  funext i
  rw [initC_apply, iotaFun_castSucc]

/-- If the radial coordinate `sig` is `1`, i.e. `u ∈ ∂I^m`, then `radialPt` fixes `u`. -/
theorem radialPt_eq_self_of_sig_eq_one (m : ℕ) (hm : 1 ≤ m) {u : IC m}
    (h : sig m hm u = 1) : radialPt m hm u = u := by
  funext i
  apply Subtype.ext
  rw [radialPt_coe, radialR, max_eq_left (by rw [h]; norm_num : (1 / 2 : ℝ) ≤ sig m hm u), h]
  ring

/-- If `sig u ≥ 1/2` then `radialPt u` lies on the boundary of the cube. -/
theorem radialPt_mem_boundary_of_half_le (m : ℕ) (hm : 1 ≤ m) {u : IC m}
    (h : (1 / 2 : ℝ) ≤ sig m hm u) : radialPt m hm u ∈ Cube.boundary (Fin m) := by
  obtain ⟨i, -, hi⟩ := Finset.exists_mem_eq_sup' (s := Finset.univ) (finNonempty hm)
    (fun i => |2 * (u i : ℝ) - 1|)
  have hne : sig m hm u ≠ 0 := by linarith
  have hmax : max (sig m hm u) ((1 : ℝ) / 2) = sig m hm u := max_eq_left h
  have hs : sig m hm u = |2 * (u i : ℝ) - 1| := by rw [sig_def]; exact hi
  rcases (abs_eq (sig_nonneg m hm u)).mp hs.symm with h' | h'
  · refine ⟨i, Or.inr ?_⟩
    apply Subtype.ext
    rw [radialPt_coe, radialR, hmax]
    have hx : (u i : ℝ) - 1/2 = sig m hm u / 2 := by linarith
    rw [hx, show (sig m hm u / 2) / sig m hm u = 1/2 from by rw [div_eq_iff hne]; ring]
    norm_num
  · refine ⟨i, Or.inl ?_⟩
    apply Subtype.ext
    rw [radialPt_coe, radialR, hmax]
    have hx : (u i : ℝ) - 1/2 = -(sig m hm u) / 2 := by linarith
    rw [hx, show (-(sig m hm u) / 2) / sig m hm u = -1/2 from by rw [div_eq_iff hne]; ring]
    norm_num

/-- If the last coordinate of `iota u` is `0`, then `sig u = 1`. -/
theorem sig_eq_one_of_tau_eq_zero (m : ℕ) (hm : 1 ≤ m) {u : IC m}
    (h : tau m hm u = 0) : sig m hm u = 1 := by
  have h2 : ((tau m hm u : unitInterval) : ℝ) = 0 := congrArg Subtype.val h
  rw [tau_coe, tauR] at h2
  have : 2 - 2 * sig m hm u = 0 := by
    by_cases hle : (1 : ℝ) ≤ 2 - 2 * sig m hm u
    · rw [min_eq_left hle] at h2; norm_num at h2
    · rw [min_eq_right (le_of_lt (not_le.mp hle))] at h2; exact h2
  linarith

/-- The value of `Psi` on a cube that is `x₀` on its boundary: it is the reparametrisation
`s ∘ radialPt`. -/
theorem Psi_apply_of_based (N m : ℕ) {x₀ : X} (K : Tower x₀ N) (hN : m + 1 ≤ N)
    {s : C(IC (m + 2), X)} (hs : ∀ v ∈ Cube.boundary (Fin (m + 2)), s v = x₀)
    (u : IC (m + 2)) :
    PsiB N m K hN s (iota (m + 2) (by omega) u) = s (radialPt (m + 2) (by omega) u) := by
  set z : ↥(Cube.boundary (Fin (m + 3))) := iota (m + 2) (by omega) u with hzdef
  have hzval : ((z : IC (m + 3))) = iotaFun (m + 2) (by omega) u := rfl
  by_cases h1 : ((z : IC (m + 3)) (Fin.last (m + 2)) : unitInterval) = 1
  · have hface := boundaryData_apply_face (m := m) (i := Fin.last (m + 2)) (b := 1)
      (PsiB_top N m K hN s) (z := z) (by simpa using h1)
    rw [hface, delG_last]
    congr 1
    exact initC_iotaFun (m + 2) (by omega) u
  · by_cases h0 : ((z : IC (m + 3)) (Fin.last (m + 2)) : unitInterval) = 0
    · rw [PsiB_apply_bottom N m K hN s (by simpa using h0)]
      have hs1 : sig (m + 2) (by omega) u = 1 := sig_eq_one_of_tau_eq_zero (m + 2) (by omega) (by
        have : ((z : IC (m + 3)) (Fin.last (m + 2)) : unitInterval) = tau (m + 2) (by omega) u := by
          rw [hzval]; exact iotaFun_last (m + 2) (by omega) u
        rw [← this]; exact h0)
      rw [radialPt_eq_self_of_sig_eq_one (m + 2) (by omega) hs1]
      exact (hs u ((sig_eq_one_iff (m + 2) (by omega) u).mp hs1)).symm
    · obtain ⟨i, hi⟩ := z.2
      have hine : i ≠ Fin.last (m + 2) := by
        intro h; rw [h] at hi
        rcases hi with hi | hi
        · exact h0 hi
        · exact h1 hi
      rcases Fin.eq_castSucc_or_eq_last i with ⟨j, rfl⟩ | hlast
      · have hmem : radialPt (m + 2) (by omega) u ∈ Cube.boundary (Fin (m + 2)) := by
          refine ⟨j, ?_⟩
          have h3 : radialPt (m + 2) (by omega) u j = (z : IC (m + 3)) (Fin.castSucc j) := by
            rw [hzval, iotaFun_castSucc]
          rw [h3]
          rcases hi with hi | hi
          · exact Or.inl hi
          · exact Or.inr hi
        have hcube : s.comp (faceCM j (cval 0)) = cconst (m + 1) x₀ := by
          ext v; exact hs _ (mem_cubeBoundary_faceCM_cval j 0 v)
        rcases hi with hi | hi
        · rw [PsiB_apply_side N m K hN s (b := 0) (by simpa using hi), hcube, K.hγ (m + 1) hN]
          exact (hs _ hmem).symm
        · have hcube' : s.comp (faceCM j (cval 1)) = cconst (m + 1) x₀ := by
            ext v; exact hs _ (mem_cubeBoundary_faceCM_cval j 1 v)
          rw [PsiB_apply_side N m K hN s (b := 1) (by simpa using hi), hcube', K.hγ (m + 1) hN]
          exact (hs _ hmem).symm
      · exact absurd hlast hine

/-- A convex combination of three numbers of `[0,1]` (with weights `1-t`, `t`) lies in `[0,1]`. -/
theorem combo_mem {t r y : ℝ} (ht0 : 0 ≤ t) (ht1 : t ≤ 1) (hr0 : 0 ≤ r) (hr1 : r ≤ 1)
    (hy0 : 0 ≤ y) (hy1 : y ≤ 1) : 0 ≤ (1 - t) * r + t * y ∧ (1 - t) * r + t * y ≤ 1 := by
  constructor
  · nlinarith [mul_nonneg (by linarith : (0 : ℝ) ≤ 1 - t) hr0, mul_nonneg ht0 hy0]
  · nlinarith [mul_le_mul_of_nonneg_left hr1 (by linarith : (0 : ℝ) ≤ 1 - t),
      mul_le_mul_of_nonneg_left hy1 ht0]

/-- The affine interpolation between `radialPt` and the identity on the cube `I^m`. -/
def radialHom (m : ℕ) (hm : 1 ≤ m) : C(IC m × unitInterval, IC m) where
  toFun w := fun i => ⟨(1 - (w.2 : ℝ)) * (radialPt m hm w.1 i : ℝ) + (w.2 : ℝ) * (w.1 i : ℝ), by
    obtain ⟨ht0, ht1⟩ := w.2.2
    obtain ⟨hr0, hr1⟩ := (radialPt m hm w.1 i).2
    obtain ⟨hy0, hy1⟩ := (w.1 i).2
    exact combo_mem ht0 ht1 hr0 hr1 hy0 hy1⟩
  continuous_toFun := by
    apply continuous_pi
    intro i
    apply Continuous.subtype_mk
    have hA : Continuous fun a : IC m × unitInterval => (radialPt m hm a.1 i : ℝ) := by
      simp only [radialPt_coe]
      exact (continuous_radialR m hm i).comp continuous_fst
    have hB : Continuous fun a : IC m × unitInterval => ((a.2 : unitInterval) : ℝ) :=
      continuous_subtype_val.comp continuous_snd
    have hC : Continuous fun a : IC m × unitInterval => ((a.1 i : unitInterval) : ℝ) :=
      continuous_subtype_val.comp ((continuous_apply i).comp continuous_fst)
    exact ((continuous_const.sub hB).mul hA).add (hB.mul hC)

@[simp] theorem radialHom_zero (m : ℕ) (hm : 1 ≤ m) (y : IC m) :
    radialHom m hm (y, 0) = radialPt m hm y := by
  funext i
  apply Subtype.ext
  show (1 - ((0 : unitInterval) : ℝ)) * (radialPt m hm y i : ℝ) + ((0 : unitInterval) : ℝ) * (y i : ℝ)
    = (radialPt m hm y i : ℝ)
  rw [show (((0 : unitInterval)) : ℝ) = 0 from rfl]
  ring

@[simp] theorem radialHom_one (m : ℕ) (hm : 1 ≤ m) (y : IC m) :
    radialHom m hm (y, 1) = y := by
  funext i
  apply Subtype.ext
  show (1 - ((1 : unitInterval) : ℝ)) * (radialPt m hm y i : ℝ) + ((1 : unitInterval) : ℝ) * (y i : ℝ)
    = (y i : ℝ)
  rw [show (((1 : unitInterval)) : ℝ) = 1 from rfl]
  ring

theorem radialHom_mem_boundary (m : ℕ) (hm : 1 ≤ m) {y : IC m} (hy : y ∈ Cube.boundary (Fin m))
    (t : unitInterval) : radialHom m hm (y, t) ∈ Cube.boundary (Fin m) := by
  have hself : radialPt m hm y = y :=
    radialPt_eq_self_of_sig_eq_one m hm ((sig_eq_one_iff m hm y).mpr hy)
  have hH : radialHom m hm (y, t) = y := by
    funext i
    apply Subtype.ext
    show (1 - (t : ℝ)) * (radialPt m hm y i : ℝ) + (t : ℝ) * (y i : ℝ) = (y i : ℝ)
    rw [hself]
    ring
  rw [hH]
  exact hy

/-- **The section property**: for a based cube `p`, `Psi p.1` is homotopic to `p` relative to
`∂I^{m+2}`. -/
theorem Psi_section (N m : ℕ) {x₀ : X} (K : Tower x₀ N) (hN : m + 1 ≤ N)
    (p : GenLoop (Fin (m + 2)) X x₀) : GenLoop.Homotopic (Psi N m K hN p.1) p := by
  have hval : (Psi N m K hN p.1) = ⟨p.1.comp (⟨radialPt (m + 2) (by omega),
      continuous_radialPt (m + 2) (by omega)⟩ : C(IC (m + 2), IC (m + 2))),
      fun y hy => p.2 (radialPt (m + 2) (by omega) y)
        (by rw [radialPt_eq_self_of_sig_eq_one (m + 2) (by omega)
          ((sig_eq_one_iff (m + 2) (by omega) y).mpr hy)]; exact hy)⟩ := by
    apply GenLoop.ext
    intro u
    rw [Psi_apply]
    exact Psi_apply_of_based N m K hN (fun v hv => p.2 v hv) u
  rw [hval]
  refine genLoop_homotopic_comp_of_id (m + 2) (y₀ := x₀)
    ⟨radialPt (m + 2) (by omega), continuous_radialPt (m + 2) (by omega)⟩ ?_ (radialHom (m + 2) (by omega)) ?_ ?_ ?_ p
  · intro y hy
    change radialPt (m + 2) (by omega) y ∈ Cube.boundary (Fin (m + 2))
    rw [radialPt_eq_self_of_sig_eq_one (m + 2) (by omega)
      ((sig_eq_one_iff (m + 2) (by omega) y).mpr hy)]
    exact hy
  · intro y
    exact radialHom_zero (m + 2) (by omega) y
  · intro y
    exact radialHom_one (m + 2) (by omega) y
  · intro y hy t
    exact radialHom_mem_boundary (m + 2) (by omega) hy t

/-- The constant cube is based-ified to the constant loop. -/
theorem Psi_const (N m : ℕ) {x₀ : X} (K : Tower x₀ N) (hN : m + 1 ≤ N) :
    Psi N m K hN (cconst (m + 2) x₀) = GenLoop.const := by
  apply GenLoop.ext
  intro u
  rw [Psi_apply]
  rw [Psi_apply_of_based N m K hN (s := cconst (m + 2) x₀) (fun v _ => rfl) u]
  rfl

end

end Work.RatHurewicz
