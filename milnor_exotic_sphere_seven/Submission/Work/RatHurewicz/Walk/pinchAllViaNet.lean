import Mathlib
import Submission.Work.RatHurewicz.GluingPinch.PinchAll
import Submission.Work.Stems.HomAdd.PrismFaces
import Submission.Work.Stems.HomAdd.cl_rhoPos

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 400000

/-!
# `PinchAll` by killing the faces of a cube (Hutchings `(2.2b)`)

`Work.RatHurewicz.PinchAll` is proved here by the *prism* method
(`Work.Stems.HomAdd.PrismFaces`): for a side coordinate `i` the self-map `killMapPos i` of
`I^{n+1}` collapses the `(i,1)`-face into the `(n-1)`-skeleton, so the glued cube
`g' := g ⋆ᵢ (g ∘ killMapPos i)` (`g` on the first half of the `i`-th coordinate, its prism on the
second half) again vanishes on the skeleton, has a constant `(i,1)`-face, and has all other faces
changed only by concatenation with constants -- except the top face, which picks up the coordinate
movement `rhoPos i` (a sign).  Killing the `2n` side faces one after another leaves the invariant
`Qs · [top] · [bottom]⁻¹` unchanged, and for a cube whose side faces are all constant the last two
faces are homotopic (the cube is then a based homotopy between them), so the invariant is `1`.  The
final algebra turns this into the signed product of all `2(n+1)` face classes.

## Main definitions

* `clampI`, `reparHalf`, `reparHalf'`: the reparametrisations used in the gluing;
* `glueAt c f g`: the gluing of two cubes along the `c`-faces;
* `Pinched n X x₀`: a cube `I^{n+1} → X` vanishing on the `(n-1)`-skeleton;
* `sgn`, `Qs`, `Cdiff`, `Rinv`: the face classes and the invariant of the killing argument.
-/

open scoped unitInterval Topology
open Work.Stems.Cubical

namespace Work.RatHurewicz.Walk

noncomputable section

variable {n : ℕ}

/-! ## The clamp and the gluing reparametrisations -/

/-- The clamp of a real number into the unit interval. -/
def clampI (r : ℝ) : unitInterval := Set.projIcc 0 1 zero_le_one r

theorem continuous_clampI : Continuous clampI := continuous_projIcc (h := by norm_num)

theorem clampI_coe (r : ℝ) : ((clampI r : unitInterval) : ℝ) = max 0 (min 1 r) := by
  show ((Set.projIcc 0 1 zero_le_one r : unitInterval) : ℝ) = _
  rw [Set.coe_projIcc]

@[simp] theorem clampI_zero : clampI 0 = 0 := by
  apply Subtype.ext
  rw [clampI_coe, min_eq_right zero_le_one, max_eq_left (le_refl (0:ℝ))]
  rfl

@[simp] theorem clampI_one : clampI 1 = 1 := by
  apply Subtype.ext
  rw [clampI_coe, min_eq_left (le_refl (1:ℝ)), max_eq_right zero_le_one]
  rfl

theorem clampI_eq_zero_of_nonpos {r : ℝ} (h : r ≤ 0) : clampI r = 0 := by
  apply Subtype.ext
  rw [clampI_coe, min_eq_right (h.trans zero_le_one), max_eq_left h]
  rfl

theorem clampI_eq_one_of_one_le {r : ℝ} (h : 1 ≤ r) : clampI r = 1 := by
  apply Subtype.ext
  rw [clampI_coe, min_eq_left h, max_eq_right zero_le_one]
  rfl

theorem clampI_coe_of_mem {r : ℝ} (h0 : 0 ≤ r) (h1 : r ≤ 1) : (clampI r : ℝ) = r := by
  rw [clampI_coe, min_eq_right h1, max_eq_right h0]

/-- Inserting a value in the coordinate `i` only depends on the other coordinates. -/
theorem sliceFaceCM {m : ℕ} (i : Fin (m+1)) (b : unitInterval) (z : IC (m+1)) :
    faceCM i b (fun j => z (i.succAbove j)) = Function.update z i b := by
  funext j
  rcases Fin.eq_self_or_eq_succAbove i j with rfl | ⟨k, hk⟩
  · rw [faceCM_apply, Work.RatHurewicz.faceFun_apply_same, Function.update_self]
  · rw [hk, faceCM_apply, Work.RatHurewicz.faceFun_apply_succAbove,
      Function.update_of_ne (Fin.succAbove_ne i k)]

theorem update_eq_sliceFaceCM {m : ℕ} (i : Fin (m+1)) (b : unitInterval) (z : IC (m+1)) :
    Function.update z i b = faceCM i b (fun j => z (i.succAbove j)) :=
  (sliceFaceCM i b z).symm

/-- Changing the coordinate `j.succAbove k` of the `(j,b)`-face is changing the coordinate `k`. -/
theorem update_faceCM {m : ℕ} {j : Fin (m+1)} {k : Fin m} (b : unitInterval) (v : IC m)
    (w : unitInterval) :
    Function.update (faceCM j b v) (j.succAbove k) w = faceCM j b (Function.update v k w) := by
  funext t
  obtain h | ⟨l, hl⟩ := Fin.eq_self_or_eq_succAbove j t
  · rw [h, Function.update_apply, if_neg (Fin.succAbove_ne j k).symm, faceCM_apply,
      Work.RatHurewicz.faceFun_apply_same, faceCM_apply,
      Work.RatHurewicz.faceFun_apply_same]
  · rw [hl]
    by_cases hlk : l = k
    · rw [hlk, Function.update_self, faceCM_apply,
        Work.RatHurewicz.faceFun_apply_succAbove, Function.update_self]
    · rw [Function.update_apply,
        if_neg (fun hEq => hlk (Fin.succAbove_right_injective hEq)), faceCM_apply,
        Work.RatHurewicz.faceFun_apply_succAbove, faceCM_apply,
        Work.RatHurewicz.faceFun_apply_succAbove, Function.update_of_ne hlk]

/-- The reparametrisation `z ↦ z` with the `c`-th coordinate doubled (clamped): the first half of
the glued cube. -/
def reparHalf {N : ℕ} (c : Fin N) (z : IC N) : IC N :=
  Function.update z c (clampI (2 * (z c : ℝ)))

/-- The reparametrisation `z ↦ z` with the `c`-th coordinate sent to `2 z_c - 1` (clamped): the
second half of the glued cube. -/
def reparHalf' {N : ℕ} (c : Fin N) (z : IC N) : IC N :=
  Function.update z c (clampI (2 * (z c : ℝ) - 1))

@[simp] theorem reparHalf_self {N : ℕ} (c : Fin N) (z : IC N) :
    reparHalf c z c = clampI (2 * (z c : ℝ)) :=
  Function.update_self ..

@[simp] theorem reparHalf'_self {N : ℕ} (c : Fin N) (z : IC N) :
    reparHalf' c z c = clampI (2 * (z c : ℝ) - 1) :=
  Function.update_self ..

theorem reparHalf_of_ne {N : ℕ} {c j : Fin N} (h : j ≠ c) (z : IC N) :
    reparHalf c z j = z j :=
  Function.update_of_ne h ..

theorem reparHalf'_of_ne {N : ℕ} {c j : Fin N} (h : j ≠ c) (z : IC N) :
    reparHalf' c z j = z j :=
  Function.update_of_ne h ..

theorem continuous_reparHalf {N : ℕ} (c : Fin N) :
    Continuous fun z : IC N => reparHalf c z := by
  rw [continuous_pi_iff]
  intro j
  by_cases hj : j = c
  · have h : (fun z : IC N => reparHalf c z j) = fun z => clampI (2 * (z c : ℝ)) := by
      funext z
      rw [hj, reparHalf_self]
    rw [h]
    exact continuous_clampI.comp
      (continuous_const.mul (continuous_subtype_val.comp (continuous_apply c)))
  · have h : (fun z : IC N => reparHalf c z j) = fun z => z j := by
      funext z
      rw [reparHalf_of_ne hj]
    rw [h]
    exact continuous_apply j

theorem continuous_reparHalf' {N : ℕ} (c : Fin N) :
    Continuous fun z : IC N => reparHalf' c z := by
  rw [continuous_pi_iff]
  intro j
  by_cases hj : j = c
  · have h : (fun z : IC N => reparHalf' c z j) = fun z => clampI (2 * (z c : ℝ) - 1) := by
      funext z
      rw [hj, reparHalf'_self]
    rw [h]
    exact continuous_clampI.comp
      ((continuous_const.mul (continuous_subtype_val.comp (continuous_apply c))).sub
        continuous_const)
  · have h : (fun z : IC N => reparHalf' c z j) = fun z => z j := by
      funext z
      rw [reparHalf'_of_ne hj]
    rw [h]
    exact continuous_apply j

/-- `reparHalf` fixes a cube point whose `c`-th coordinate is `0`. -/
theorem reparHalf_eq_self_of_coe_zero {N : ℕ} {c : Fin N} {z : IC N}
    (h : (z c : ℝ) = 0) : reparHalf c z = z := by
  have hz : clampI (2 * (z c : ℝ)) = z c := by
    rw [h, show (2:ℝ) * 0 = 0 by norm_num, clampI_zero]
    exact (Subtype.ext h).symm
  rw [reparHalf, hz]
  exact Function.update_eq_self c z

/-- `reparHalf'` fixes a cube point whose `c`-th coordinate is `1`. -/
theorem reparHalf'_eq_self_of_coe_one {N : ℕ} {c : Fin N} {z : IC N}
    (h : (z c : ℝ) = 1) : reparHalf' c z = z := by
  have hz : clampI (2 * (z c : ℝ) - 1) = z c := by
    rw [h, show (2:ℝ) * 1 - 1 = 1 by norm_num, clampI_one]
    exact (Subtype.ext h).symm
  rw [reparHalf', hz]
  exact Function.update_eq_self c z

/-- `reparHalf` preserves extremality of every coordinate. -/
theorem isExtreme_reparHalf {N : ℕ} (c : Fin N) (z : IC N) {j : Fin N}
    (h : z j = 0 ∨ z j = 1) : reparHalf c z j = 0 ∨ reparHalf c z j = 1 := by
  rcases eq_or_ne j c with hjc | hj
  · subst hjc
    rw [reparHalf_self]
    rcases h with h | h
    · exact Or.inl (by
        rw [h, show (((0 : unitInterval) : ℝ)) = 0 by rfl,
          show (2:ℝ) * 0 = 0 by norm_num, clampI_zero])
    · exact Or.inr (by
        rw [h, show (((1 : unitInterval) : ℝ)) = 1 by rfl,
          show (2:ℝ) * 1 = 2 by norm_num, clampI_eq_one_of_one_le (by norm_num)])
  · rw [reparHalf_of_ne hj]
    exact h

/-- `reparHalf'` preserves extremality of every coordinate. -/
theorem isExtreme_reparHalf' {N : ℕ} (c : Fin N) (z : IC N) {j : Fin N}
    (h : z j = 0 ∨ z j = 1) : reparHalf' c z j = 0 ∨ reparHalf' c z j = 1 := by
  rcases eq_or_ne j c with hjc | hj
  · subst hjc
    rw [reparHalf'_self]
    rcases h with h | h
    · exact Or.inl (by
        rw [h, show (((0 : unitInterval) : ℝ)) = 0 by rfl,
          show (2:ℝ) * 0 - 1 = -1 by norm_num, clampI_eq_zero_of_nonpos (by norm_num)])
    · exact Or.inr (by
        rw [h, show (((1 : unitInterval) : ℝ)) = 1 by rfl,
          show (2:ℝ) * 1 - 1 = 1 by norm_num, clampI_one])
  · rw [reparHalf'_of_ne hj]
    exact h

theorem mem_InSkel_reparHalf {m : ℕ} {c : Fin (m+1)} {z : IC (m+1)}
    (hz : InSkel m z) : InSkel m (reparHalf c z) := by
  obtain ⟨j, j', hjj, hj, hj'⟩ := hz
  exact ⟨j, j', hjj, isExtreme_reparHalf c z hj, isExtreme_reparHalf c z hj'⟩

theorem mem_InSkel_reparHalf' {m : ℕ} {c : Fin (m+1)} {z : IC (m+1)}
    (hz : InSkel m z) : InSkel m (reparHalf' c z) := by
  obtain ⟨j, j', hjj, hj, hj'⟩ := hz
  exact ⟨j, j', hjj, isExtreme_reparHalf' c z hj, isExtreme_reparHalf' c z hj'⟩

/-! ## Gluing two cubes along a coordinate face -/

/-- **The gluing of two cubes along a coordinate face.**  If `f` and `g` agree on the `c`-faces
(`f`'s `(c,1)`-face equals `g`'s `(c,0)`-face) then `glueAt c f g` agrees with `f` on the first half
of the `c`-th coordinate and with `g` on the second half. -/
def glueAt {m : ℕ} {X : Type} [TopologicalSpace X] (c : Fin (m+1)) (f g : C(IC (m+1), X))
    (h : f.comp (faceCM c 1) = g.comp (faceCM c 0)) : C(IC (m+1), X) where
  toFun z := if (z c : ℝ) ≤ 1/2 then f (reparHalf c z) else g (reparHalf' c z)
  continuous_toFun := by
    refine continuous_if_le (continuous_subtype_val.comp (continuous_apply c)) continuous_const
      ((f.continuous.comp (continuous_reparHalf c)).continuousOn)
      ((g.continuous.comp (continuous_reparHalf' c)).continuousOn) ?_
    intro z hz
    have hzc : z c = (⟨1/2, by norm_num⟩ : unitInterval) := Subtype.ext hz
    have h1 : reparHalf c z = faceCM c 1 (fun j => z (c.succAbove j)) := by
      rw [reparHalf, hzc, show (2:ℝ) * (1/2) = 1 by norm_num, clampI_one, update_eq_sliceFaceCM]
    have h2 : reparHalf' c z = faceCM c 0 (fun j => z (c.succAbove j)) := by
      rw [reparHalf', hzc, show (2:ℝ) * (1/2) - 1 = 0 by norm_num, clampI_zero,
        update_eq_sliceFaceCM]
    rw [h1, h2, ← ContinuousMap.comp_apply, h, ContinuousMap.comp_apply]

@[simp] theorem glueAt_apply {m : ℕ} {X : Type} [TopologicalSpace X] (c : Fin (m+1))
    (f g : C(IC (m+1), X)) (h : f.comp (faceCM c 1) = g.comp (faceCM c 0)) (z : IC (m+1)) :
    glueAt c f g h z = if (z c : ℝ) ≤ 1/2 then f (reparHalf c z) else g (reparHalf' c z) := rfl

/-- The glued cube on the face `{z c = 0}` is the first cube. -/
theorem glueAt_face_zero {m : ℕ} {X : Type} [TopologicalSpace X] (c : Fin (m+1))
    (f g : C(IC (m+1), X)) (h : f.comp (faceCM c 1) = g.comp (faceCM c 0)) (v : IC m) :
    glueAt c f g h (faceCM c 0 v) = f (faceCM c 0 v) := by
  have hc : (faceCM c 0 v : IC (m+1)) c = (0 : unitInterval) := by
    rw [faceCM_apply, Work.RatHurewicz.faceFun_apply_same]
  have hcf : ((faceCM c 0 v : IC (m+1)) c : ℝ) = 0 := by rw [hc]; rfl
  have hle : ((faceCM c 0 v : IC (m+1)) c : ℝ) ≤ 1/2 := by rw [hcf]; norm_num
  rw [glueAt_apply, if_pos hle, reparHalf_eq_self_of_coe_zero hcf]

/-- The glued cube on the face `{z c = 1}` is the second cube. -/
theorem glueAt_face_one {m : ℕ} {X : Type} [TopologicalSpace X] (c : Fin (m+1))
    (f g : C(IC (m+1), X)) (h : f.comp (faceCM c 1) = g.comp (faceCM c 0)) (v : IC m) :
    glueAt c f g h (faceCM c 1 v) = g (faceCM c 1 v) := by
  have hc : (faceCM c 1 v : IC (m+1)) c = (1 : unitInterval) := by
    rw [faceCM_apply, Work.RatHurewicz.faceFun_apply_same]
  have hcf : ((faceCM c 1 v : IC (m+1)) c : ℝ) = 1 := by rw [hc]; rfl
  have hle : ¬ ((faceCM c 1 v : IC (m+1)) c : ℝ) ≤ 1/2 := by rw [hcf]; norm_num
  rw [glueAt_apply, if_neg hle, reparHalf'_eq_self_of_coe_one hcf]

/-- The value of the glued cube on a face different from the gluing coordinate: the two pieces are
read on the two halves of the distinguished coordinate. -/
theorem glueAt_face_succAbove {m : ℕ} {X : Type} [TopologicalSpace X] (j : Fin (m+1))
    (k : Fin m) (f g : C(IC (m+1), X))
    (h : f.comp (faceCM (j.succAbove k) 1) = g.comp (faceCM (j.succAbove k) 0))
    (b : unitInterval) (v : IC m) :
    glueAt (j.succAbove k) f g h (faceCM j b v) =
      if (v k : ℝ) ≤ 1/2 then f (faceCM j b (reparHalf k v))
      else g (faceCM j b (reparHalf' k v)) := by
  have hc : (faceCM j b v : IC (m+1)) (j.succAbove k) = v k := by
    rw [faceCM_apply, Work.RatHurewicz.faceFun_apply_succAbove]
  rw [glueAt_apply, hc]
  by_cases hv : (v k : ℝ) ≤ 1/2
  · rw [if_pos hv, if_pos hv]
    congr 1
    rw [reparHalf, hc]
    exact update_faceCM b v (clampI (2 * (v k : ℝ)))
  · rw [if_neg hv, if_neg hv]
    congr 1
    rw [reparHalf', hc]
    exact update_faceCM b v (clampI (2 * (v k : ℝ) - 1))

/-- The glued cube vanishes on the skeleton when both pieces do. -/
theorem glueAt_skel {m : ℕ} {X : Type} [TopologicalSpace X] {x₀ : X} (c : Fin (m+1))
    (f g : C(IC (m+1), X)) (hf : ∀ z, InSkel m z → f z = x₀)
    (hg : ∀ z, InSkel m z → g z = x₀) (h : f.comp (faceCM c 1) = g.comp (faceCM c 0)) :
    ∀ z, InSkel m z → glueAt c f g h z = x₀ := by
  intro z hz
  rw [glueAt_apply]
  split
  · exact hf _ (mem_InSkel_reparHalf hz)
  · exact hg _ (mem_InSkel_reparHalf' hz)

/-! ## The class of a concatenation and of a glued face -/

/-- The class of a concatenation of based cubes in an arbitrary coordinate. -/
theorem cl_transAt' {m : ℕ} [NeZero m] [Nontrivial (Fin m)] {X : Type} [TopologicalSpace X]
    {x₀ : X} (k : Fin m) (p q : GenLoop (Fin m) X x₀) :
    cl m X x₀ (GenLoop.transAt k q p) = cl m X x₀ p * cl m X x₀ q := by
  have h := HomotopyGroup.mul_spec (N := Fin m) (X := X) (x := x₀) (i := k) (p := p) (q := q)
  simpa only [cl] using h.symm

/-- The explicit formula for `GenLoop.transAt`. -/
theorem transAt_val {m : ℕ} {X : Type} [TopologicalSpace X] {x₀ : X} (k : Fin m)
    (p q : GenLoop (Fin m) X x₀) (t : IC m) :
    (GenLoop.transAt k p q) t
      = if (t k : ℝ) ≤ 1/2 then p (reparHalf k t) else q (reparHalf' k t) := by
  rw [GenLoop.transAt, GenLoop.coe_copy]
  rfl

/-- The `(j,b)`-face of a glued cube is the concatenation (in the coordinate `k`) of the two
pieces' faces. -/
theorem faceCube_glueAt {m : ℕ} {X : Type} [TopologicalSpace X] {x₀ : X}
    (j : Fin (m+1)) (k : Fin m) (f g : C(IC (m+1), X))
    (hf : ∀ z, InSkel m z → f z = x₀) (hg : ∀ z, InSkel m z → g z = x₀)
    (h : f.comp (faceCM (j.succAbove k) 1) = g.comp (faceCM (j.succAbove k) 0)) (b : Bool) :
    faceCube m (glueAt (j.succAbove k) f g h) (glueAt_skel (j.succAbove k) f g hf hg h) j b
      = GenLoop.transAt k (faceCube m f hf j b) (faceCube m g hg j b) := by
  apply Subtype.ext
  apply ContinuousMap.ext
  intro v
  show glueAt (j.succAbove k) f g h (faceCM j (if b then 1 else 0) v)
      = (GenLoop.transAt k (faceCube m f hf j b) (faceCube m g hg j b)) v
  rw [transAt_val, glueAt_face_succAbove]
  by_cases hv : (v k : ℝ) ≤ 1/2
  · rw [if_pos hv, if_pos hv]
    rfl
  · rw [if_neg hv, if_neg hv]
    rfl

/-- **The class of a face of a glued cube** (other than the gluing coordinate) is the product of
the classes of the corresponding faces of the pieces. -/
theorem faceCl_glueAt {m : ℕ} [NeZero m] [Nontrivial (Fin m)] {X : Type} [TopologicalSpace X]
    {x₀ : X} (j : Fin (m+1)) (k : Fin m) (f g : C(IC (m+1), X))
    (hf : ∀ z, InSkel m z → f z = x₀) (hg : ∀ z, InSkel m z → g z = x₀)
    (h : f.comp (faceCM (j.succAbove k) 1) = g.comp (faceCM (j.succAbove k) 0)) (b : Bool) :
    cl m X x₀ (faceCube m (glueAt (j.succAbove k) f g h)
        (glueAt_skel (j.succAbove k) f g hf hg h) j b)
      = cl m X x₀ (faceCube m g hg j b) * cl m X x₀ (faceCube m f hf j b) := by
  rw [faceCube_glueAt j k f g hf hg h b, cl_transAt']

/-! ## The class of a face of a glued cube, phrased without the coordinate -/

/-- **The class of a face of a glued cube** (other than the gluing coordinate) is the product of
the classes of the corresponding faces of the pieces. -/
theorem faceCl_glueAt_of {m : ℕ} [NeZero m] [Nontrivial (Fin m)] {X : Type} [TopologicalSpace X]
    {x₀ : X} (c : Fin (m+1)) (f g : C(IC (m+1), X))
    (hf : ∀ z, InSkel m z → f z = x₀) (hg : ∀ z, InSkel m z → g z = x₀)
    (h : f.comp (faceCM c 1) = g.comp (faceCM c 0)) (j : Fin (m+1)) (hj : j ≠ c) (b : Bool) :
    cl m X x₀ (faceCube m (glueAt c f g h) (glueAt_skel c f g hf hg h) j b)
      = cl m X x₀ (faceCube m g hg j b) * cl m X x₀ (faceCube m f hf j b) := by
  obtain ⟨k, hk⟩ := Fin.exists_succAbove_eq (Ne.symm hj)
  have hkc : c = j.succAbove k := hk.symm
  subst hkc
  exact faceCl_glueAt j k f g hf hg h b

/-! ## Pinched cubes -/

/-- The value of a Boolean as a point of the cube's boundary. -/
def bval (b : Bool) : unitInterval := if b then 1 else 0

/-- A cube `I^{n+1} → X` which is constant `x₀` on the `(n-1)`-skeleton. -/
structure Pinched (n : ℕ) (X : Type) [TopologicalSpace X] (x₀ : X) where
  cube : C(IC (n+1), X)
  hskel : ∀ z : IC (n+1), InSkel n z → cube z = x₀

namespace Pinched

variable {X : Type} [TopologicalSpace X] {x₀ : X}

/-- The `(j,b)`-face of a pinched cube, as a based `n`-cube. -/
def face (G : Pinched n X x₀) (j : Fin (n+1)) (b : Bool) : GenLoop (Fin n) X x₀ :=
  faceCube n G.cube G.hskel j b

/-- The class of the `(j,b)`-face. -/
def faceCl (G : Pinched n X x₀) (j : Fin (n+1)) (b : Bool) : HomotopyGroup (Fin n) X x₀ :=
  cl n X x₀ (G.face j b)

/-- A face which is (globally) constant `x₀` has class `1`. -/
theorem faceCl_eq_one_of_const {n : ℕ} [NeZero n] [Nontrivial (Fin n)] (G : Pinched n X x₀)
    (j : Fin (n+1)) (b : Bool) (h : ∀ v : IC n, G.cube (faceCM j (bval b) v) = x₀) :
    G.faceCl j b = 1 := by
  have hconst : G.face j b = (GenLoop.const : GenLoop (Fin n) X x₀) := by
    apply Subtype.ext
    apply ContinuousMap.ext
    intro v
    exact h v
  rw [faceCl, hconst, Work.RatHurewicz.cl_const]

/-- The `killMapPos i`-prism of a pinched cube. -/
def prismPos (i : Fin n) (G : Pinched n X x₀) : Pinched n X x₀ :=
  ⟨G.cube.comp (Work.Stems.HomAdd.killCMpos i),
    fun z hz => G.hskel _ (Work.Stems.HomAdd.killMapPos_mem_InSkel i hz)⟩

/-- The `killMapNeg i`-prism of a pinched cube. -/
def prismNeg (i : Fin n) (G : Pinched n X x₀) : Pinched n X x₀ :=
  ⟨G.cube.comp (Work.Stems.HomAdd.killCMneg i),
    fun z hz => G.hskel _ (Work.Stems.HomAdd.killMapNeg_mem_InSkel i hz)⟩

/-- The side faces of the positive prism are constant. -/
theorem prismPos_faceCl_side {n : ℕ} [NeZero n] [Nontrivial (Fin n)] (i : Fin n)
    (G : Pinched n X x₀) {j' : Fin n} (hj' : j' ≠ i) (b : Bool) :
    (prismPos i G).faceCl (Fin.castSucc j') b = 1 := by
  refine faceCl_eq_one_of_const _ _ _ ?_
  intro v
  exact G.hskel _ (Work.Stems.HomAdd.killMapPos_face_side_mem_InSkel i
    (fun h => hj' (Fin.castSucc_injective n h)) (Fin.castSucc_ne_last j')
    (by rcases b with _ | _ <;> simp [bval]) v)

/-- The bottom face of the positive prism is constant. -/
theorem prismPos_faceCl_bottom {n : ℕ} [NeZero n] [Nontrivial (Fin n)] (i : Fin n)
    (G : Pinched n X x₀) : (prismPos i G).faceCl (Fin.last n) false = 1 := by
  refine faceCl_eq_one_of_const _ _ _ ?_
  intro v
  exact G.hskel _ (Work.Stems.HomAdd.killMapPos_face_last_zero_mem_InSkel i v)

/-- The top face of the positive prism is the `(i,1)`-face read through `rhoPos`. -/
theorem prismPos_faceCl_top {n : ℕ} [NeZero n] [Nontrivial (Fin n)] (i : Fin n)
    (G : Pinched n X x₀) :
    (prismPos i G).faceCl (Fin.last n) true
      = (G.faceCl (Fin.castSucc i) true) ^ ((-1 : ℤ) ^ (n - (i : ℕ))) := by
  have hpt : ∀ v : IC n, (prismPos i G).face (Fin.last n) true v
      = (G.face (Fin.castSucc i) true) (Work.Stems.HomAdd.rhoPos i v) := by
    intro v
    show G.cube (Work.Stems.HomAdd.killMapPos i (faceCM (Fin.last n) 1 v))
      = G.cube (faceCM (Fin.castSucc i) 1 (Work.Stems.HomAdd.rhoPos i v))
    rw [Work.Stems.HomAdd.killMapPos_face_last_one]
  rw [faceCl, faceCl]
  exact Work.Stems.HomAdd.cl_rhoPos i (G.face (Fin.castSucc i) true)
    ((prismPos i G).face (Fin.last n) true) hpt

/-- The side faces of the negative prism are constant. -/
theorem prismNeg_faceCl_side {n : ℕ} [NeZero n] [Nontrivial (Fin n)] (i : Fin n)
    (G : Pinched n X x₀) {j' : Fin n} (hj' : j' ≠ i) (b : Bool) :
    (prismNeg i G).faceCl (Fin.castSucc j') b = 1 := by
  refine faceCl_eq_one_of_const _ _ _ ?_
  intro v
  exact G.hskel _ (Work.Stems.HomAdd.killMapNeg_face_side_mem_InSkel i
    (fun h => hj' (Fin.castSucc_injective n h)) (Fin.castSucc_ne_last j')
    (by rcases b with _ | _ <;> simp [bval]) v)

/-- The bottom face of the negative prism is constant. -/
theorem prismNeg_faceCl_bottom {n : ℕ} [NeZero n] [Nontrivial (Fin n)] (i : Fin n)
    (G : Pinched n X x₀) : (prismNeg i G).faceCl (Fin.last n) false = 1 := by
  refine faceCl_eq_one_of_const _ _ _ ?_
  intro v
  exact G.hskel _ (Work.Stems.HomAdd.killMapNeg_face_last_zero_mem_InSkel i v)

end Pinched

/-! ## The coordinate movement `rhoNeg` via `rhoPos` and a flip -/

/-- `-(-1)^m = (-1)^{m-1}`. -/
theorem neg_neg_one_pow {m : ℕ} (hm : 1 ≤ m) : -((-1 : ℤ) ^ m) = (-1 : ℤ) ^ (m - 1) := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : m ≠ 0)
  rw [show k + 1 - 1 = k from by omega, pow_succ]
  ring

theorem continuous_rhoPos {n : ℕ} (i : Fin n) :
    Continuous fun v : IC n => Work.Stems.HomAdd.rhoPos i v := by
  rw [continuous_pi_iff]
  intro m
  show Continuous fun v : IC n =>
    Work.Stems.HomAdd.killMapPos i (faceCM (Fin.last n) 1 v) ((Fin.castSucc i).succAbove m)
  exact (continuous_apply ((Fin.castSucc i).succAbove m)).comp
    ((Work.Stems.HomAdd.continuous_killMapPos i).comp (faceCM (Fin.last n) 1).continuous)

/-- `rhoPos` carries the boundary of the cube into itself. -/
theorem mem_boundary_rhoPos {n : ℕ} (i : Fin n) {v : IC n} (hv : v ∈ Cube.boundary (Fin n)) :
    Work.Stems.HomAdd.rhoPos i v ∈ Cube.boundary (Fin n) := by
  obtain ⟨j₀, hj₀⟩ := hv
  rcases eq_or_ne j₀ i with h | hne
  · rw [h] at hj₀
    obtain ⟨m, hm⟩ := Fin.exists_succAbove_eq (x := Fin.last n) (y := Fin.castSucc i)
      (Fin.castSucc_ne_last i).symm
    refine ⟨m, ?_⟩
    have hval : Work.Stems.HomAdd.rhoPos i v m
        = Work.Stems.HomAdd.killMapPos i (faceCM (Fin.last n) 1 v) (Fin.last n) := by
      rw [Work.Stems.HomAdd.rhoPos, hm]
    rw [hval, Work.Stems.HomAdd.killMapPos_apply_last, faceCM_apply,
      Work.RatHurewicz.faceFun_apply_same,
      show Fin.castSucc i = (Fin.last n).succAbove i from (congrFun Fin.succAbove_last i).symm,
      Work.RatHurewicz.faceFun_apply_succAbove, one_mul]
    rcases hj₀ with h0 | h1
    · rw [h0, unitInterval.symm_zero]; exact Or.inr rfl
    · rw [h1, unitInterval.symm_one]; exact Or.inl rfl
  · obtain ⟨m, hm⟩ := Fin.exists_succAbove_eq (x := Fin.castSucc j₀) (y := Fin.castSucc i)
      (fun heq => hne (Fin.castSucc_injective n heq))
    refine ⟨m, ?_⟩
    have hval : Work.Stems.HomAdd.rhoPos i v m
        = Work.Stems.HomAdd.killMapPos i (faceCM (Fin.last n) 1 v) (Fin.castSucc j₀) := by
      rw [Work.Stems.HomAdd.rhoPos, hm]
    rw [hval]
    have h1 : Fin.castSucc j₀ ≠ Fin.castSucc i := fun heq => hne (Fin.castSucc_injective n heq)
    have h2 : Fin.castSucc j₀ ≠ Fin.last n := Fin.castSucc_ne_last j₀
    rw [Work.Stems.HomAdd.killMapPos_apply_of_ne i h1 h2,
      show Fin.castSucc j₀ = (Fin.last n).succAbove j₀ from (congrFun Fin.succAbove_last j₀).symm,
      faceCM_apply, Work.RatHurewicz.faceFun_apply_succAbove]
    exact hj₀

/-- The `killMapNeg`-prism top face is the `killMapPos` one with the `i`-th coordinate reversed. -/
theorem rhoNeg_eq_rhoPos_flip {n : ℕ} (i : Fin n) (v : IC n) :
    Work.Stems.HomAdd.rhoNeg i v = Work.Stems.HomAdd.rhoPos i (Work.Stems.flipMap i v) := by
  have hflip : faceCM (Fin.last n) 1 (Work.Stems.flipMap i v)
      = Work.Stems.flipMap (Fin.castSucc i) (faceCM (Fin.last n) 1 v) := by
    have h1 : Work.Stems.flipMap i v = Function.update v i (unitInterval.symm (v i)) := by
      funext t
      rw [Work.Stems.flipMap_apply]
      by_cases ht : t = i
      · rw [if_pos ht, ht, Function.update_self]
      · rw [if_neg ht, Function.update_of_ne ht]
    rw [h1, ← update_faceCM,
      show (Fin.last n).succAbove i = Fin.castSucc i from congrFun Fin.succAbove_last i]
    funext t
    rw [Work.Stems.flipMap_apply]
    by_cases ht : t = Fin.castSucc i
    · rw [if_pos ht, ht, Function.update_self]
      congr 1
      rw [faceCM_apply,
        show Fin.castSucc i = (Fin.last n).succAbove i from (congrFun Fin.succAbove_last i).symm,
        Work.RatHurewicz.faceFun_apply_succAbove]
    · rw [if_neg ht, Function.update_of_ne ht]
  funext m
  have hval : Work.Stems.HomAdd.rhoNeg i v m
      = Work.Stems.HomAdd.killMapNeg i (faceCM (Fin.last n) 1 v) ((Fin.castSucc i).succAbove m) := by
    rw [Work.Stems.HomAdd.rhoNeg]
  have hval' : Work.Stems.HomAdd.rhoPos i (Work.Stems.flipMap i v) m
      = Work.Stems.HomAdd.killMapPos i (faceCM (Fin.last n) 1 (Work.Stems.flipMap i v))
          ((Fin.castSucc i).succAbove m) := by
    rw [Work.Stems.HomAdd.rhoPos]
  rw [hval, hval', hflip]
  set z : IC (n+1) := faceCM (Fin.last n) 1 v with hz
  set j : Fin (n+1) := (Fin.castSucc i).succAbove m with hj
  have hji : j ≠ Fin.castSucc i := by
    rw [hj]; exact Fin.succAbove_ne (Fin.castSucc i) m
  have hzcs : z (Fin.castSucc i) = v i := by
    rw [hz, faceCM_apply,
      show Fin.castSucc i = (Fin.last n).succAbove i from (congrFun Fin.succAbove_last i).symm,
      Work.RatHurewicz.faceFun_apply_succAbove]
  by_cases hjl : j = Fin.last n
  · rw [hjl, Work.Stems.HomAdd.killMapNeg_apply_last, Work.Stems.HomAdd.killMapPos_apply_last,
      Work.Stems.flipMap_apply, if_neg (Fin.castSucc_ne_last i).symm, Work.Stems.flipMap_apply,
      if_pos rfl, unitInterval.symm_symm]
  · rw [Work.Stems.HomAdd.killMapNeg_apply_of_ne i hji hjl,
      Work.Stems.HomAdd.killMapPos_apply_of_ne i hji hjl, Work.Stems.flipMap_apply,
      if_neg (show j ≠ Fin.castSucc i from hji)]


namespace Pinched

variable {X : Type} [TopologicalSpace X] {x₀ : X}

/-- The top face of the negative prism is the `(i,0)`-face read through `rhoNeg`. -/
theorem prismNeg_faceCl_top {n : ℕ} [NeZero n] [Nontrivial (Fin n)] (i : Fin n)
    (G : Pinched n X x₀) :
    (prismNeg i G).faceCl (Fin.last n) true
      = (G.faceCl (Fin.castSucc i) false) ^ ((-1 : ℤ) ^ (n - (i : ℕ) - 1)) := by
  set X0 : GenLoop (Fin n) X x₀ := G.face (Fin.castSucc i) false with hX0
  set p₃ : GenLoop (Fin n) X x₀ :=
    ⟨X0.1.comp ⟨fun v => Work.Stems.HomAdd.rhoPos i v, continuous_rhoPos i⟩,
      fun v hv => X0.2 _ (mem_boundary_rhoPos i hv)⟩ with hp₃
  have hcl₃ : cl n X x₀ p₃ = (cl n X x₀ X0) ^ ((-1 : ℤ) ^ (n - (i : ℕ))) :=
    Work.Stems.HomAdd.cl_rhoPos i X0 p₃ (fun v => rfl)
  have hq : (prismNeg i G).face (Fin.last n) true
      = ⟨p₃.1.comp (Work.Stems.flipMap i),
          fun v hv => p₃.2 _ (Work.Stems.flipMap_boundary i hv)⟩ := by
    apply Subtype.ext
    apply ContinuousMap.ext
    intro v
    show G.cube (Work.Stems.HomAdd.killMapNeg i (faceCM (Fin.last n) 1 v))
      = p₃ (Work.Stems.flipMap i v)
    rw [Work.Stems.HomAdd.killMapNeg_face_last_one]
    show G.cube (faceCM (Fin.castSucc i) 0 (Work.Stems.HomAdd.rhoNeg i v))
      = X0 (Work.Stems.HomAdd.rhoPos i (Work.Stems.flipMap i v))
    rw [hX0, rhoNeg_eq_rhoPos_flip]
    rfl
  rw [faceCl, hq, Work.Stems.flipMap_class i p₃, hcl₃, ← zpow_neg]
  congr 1
  exact neg_neg_one_pow (by omega)

/-! ## Killing a side face -/

/-- The gluing hypothesis of the positive kill. -/
theorem glueHypPos {n : ℕ} (i : Fin n) (G : Pinched n X x₀) :
    G.cube.comp (faceCM (Fin.castSucc i) 1)
      = (prismPos i G).cube.comp (faceCM (Fin.castSucc i) 0) := by
  apply ContinuousMap.ext
  intro v
  show G.cube (faceCM (Fin.castSucc i) 1 v)
    = G.cube (Work.Stems.HomAdd.killMapPos i (faceCM (Fin.castSucc i) 0 v))
  rw [Work.Stems.HomAdd.killMapPos_face_zero]

/-- The gluing hypothesis of the negative kill. -/
theorem glueHypNeg {n : ℕ} (i : Fin n) (G : Pinched n X x₀) :
    (prismNeg i G).cube.comp (faceCM (Fin.castSucc i) 1)
      = G.cube.comp (faceCM (Fin.castSucc i) 0) := by
  apply ContinuousMap.ext
  intro v
  show G.cube (Work.Stems.HomAdd.killMapNeg i (faceCM (Fin.castSucc i) 1 v))
    = G.cube (faceCM (Fin.castSucc i) 0 v)
  rw [Work.Stems.HomAdd.killMapNeg_face_one]

/-- **Killing the `(i,1)`-face**: glue the cube to its positive prism along the `(i,0)`-face. -/
def killPos (i : Fin n) (G : Pinched n X x₀) : Pinched n X x₀ :=
  ⟨glueAt (Fin.castSucc i) G.cube (prismPos i G).cube (glueHypPos i G),
   glueAt_skel (Fin.castSucc i) G.cube (prismPos i G).cube G.hskel (prismPos i G).hskel
     (glueHypPos i G)⟩

/-- **Killing the `(i,0)`-face**: glue the negative prism of the cube to the cube. -/
def killNeg (i : Fin n) (G : Pinched n X x₀) : Pinched n X x₀ :=
  ⟨glueAt (Fin.castSucc i) (prismNeg i G).cube G.cube (glueHypNeg i G),
   glueAt_skel (Fin.castSucc i) (prismNeg i G).cube G.cube (prismNeg i G).hskel G.hskel
     (glueHypNeg i G)⟩

variable {n : ℕ}

/-- The `(i,0)`-face is unchanged by the positive kill. -/
theorem face_killPos_same_false [NeZero n] (i : Fin n) (G : Pinched n X x₀) :
    (killPos i G).face (Fin.castSucc i) false = G.face (Fin.castSucc i) false := by
  apply Subtype.ext
  apply ContinuousMap.ext
  intro v
  show glueAt (Fin.castSucc i) G.cube (prismPos i G).cube (glueHypPos i G)
      (faceCM (Fin.castSucc i) 0 v) = G.cube (faceCM (Fin.castSucc i) 0 v)
  rw [glueAt_face_zero]

/-- The `(i,1)`-face is unchanged by the negative kill. -/
theorem face_killNeg_same_true [NeZero n] (i : Fin n) (G : Pinched n X x₀) :
    (killNeg i G).face (Fin.castSucc i) true = G.face (Fin.castSucc i) true := by
  apply Subtype.ext
  apply ContinuousMap.ext
  intro v
  show glueAt (Fin.castSucc i) (prismNeg i G).cube G.cube (glueHypNeg i G)
      (faceCM (Fin.castSucc i) 1 v) = G.cube (faceCM (Fin.castSucc i) 1 v)
  rw [glueAt_face_one]

theorem faceCl_killPos_same_false [NeZero n] (i : Fin n) (G : Pinched n X x₀) :
    (killPos i G).faceCl (Fin.castSucc i) false = G.faceCl (Fin.castSucc i) false := by
  rw [faceCl, faceCl, face_killPos_same_false i G]

theorem faceCl_killNeg_same_true [NeZero n] (i : Fin n) (G : Pinched n X x₀) :
    (killNeg i G).faceCl (Fin.castSucc i) true = G.faceCl (Fin.castSucc i) true := by
  rw [faceCl, faceCl, face_killNeg_same_true i G]

/-- The `(i,1)`-face becomes constant under the positive kill. -/
theorem faceCl_killPos_same_true [NeZero n] [Nontrivial (Fin n)] (i : Fin n)
    (G : Pinched n X x₀) : (killPos i G).faceCl (Fin.castSucc i) true = 1 := by
  refine faceCl_eq_one_of_const _ _ _ ?_
  intro v
  show glueAt (Fin.castSucc i) G.cube (prismPos i G).cube (glueHypPos i G)
      (faceCM (Fin.castSucc i) 1 v) = x₀
  rw [glueAt_face_one]
  exact G.hskel _ (Work.Stems.HomAdd.killMapPos_face_one_mem_InSkel i v)

/-- The `(i,0)`-face becomes constant under the negative kill. -/
theorem faceCl_killNeg_same_false [NeZero n] [Nontrivial (Fin n)] (i : Fin n)
    (G : Pinched n X x₀) : (killNeg i G).faceCl (Fin.castSucc i) false = 1 := by
  refine faceCl_eq_one_of_const _ _ _ ?_
  intro v
  show glueAt (Fin.castSucc i) (prismNeg i G).cube G.cube (glueHypNeg i G)
      (faceCM (Fin.castSucc i) 0 v) = x₀
  rw [glueAt_face_zero]
  exact G.hskel _ (Work.Stems.HomAdd.killMapNeg_face_zero_mem_InSkel i v)

/-- The other side faces are unchanged by the positive kill. -/
theorem faceCl_killPos_side [NeZero n] [Nontrivial (Fin n)] (i : Fin n) (G : Pinched n X x₀)
    {j' : Fin n} (hj' : j' ≠ i) (b : Bool) :
    (killPos i G).faceCl (Fin.castSucc j') b = G.faceCl (Fin.castSucc j') b := by
  change cl n X x₀ (faceCube n
      (glueAt (Fin.castSucc i) G.cube (prismPos i G).cube (glueHypPos i G))
      (glueAt_skel (Fin.castSucc i) G.cube (prismPos i G).cube G.hskel (prismPos i G).hskel
        (glueHypPos i G)) (Fin.castSucc j') b)
    = cl n X x₀ (faceCube n G.cube G.hskel (Fin.castSucc j') b)
  rw [faceCl_glueAt_of (Fin.castSucc i) G.cube (prismPos i G).cube G.hskel (prismPos i G).hskel
      (glueHypPos i G) (Fin.castSucc j') (fun h => hj' (Fin.castSucc_injective n h)) b]
  have hprism : cl n X x₀ (faceCube n (prismPos i G).cube (prismPos i G).hskel (Fin.castSucc j') b) = 1 :=
    prismPos_faceCl_side i G hj' b
  rw [hprism, one_mul]

/-- The other side faces are unchanged by the negative kill. -/
theorem faceCl_killNeg_side [NeZero n] [Nontrivial (Fin n)] (i : Fin n) (G : Pinched n X x₀)
    {j' : Fin n} (hj' : j' ≠ i) (b : Bool) :
    (killNeg i G).faceCl (Fin.castSucc j') b = G.faceCl (Fin.castSucc j') b := by
  change cl n X x₀ (faceCube n
      (glueAt (Fin.castSucc i) (prismNeg i G).cube G.cube (glueHypNeg i G))
      (glueAt_skel (Fin.castSucc i) (prismNeg i G).cube G.cube (prismNeg i G).hskel G.hskel
        (glueHypNeg i G)) (Fin.castSucc j') b)
    = cl n X x₀ (faceCube n G.cube G.hskel (Fin.castSucc j') b)
  rw [faceCl_glueAt_of (Fin.castSucc i) (prismNeg i G).cube G.cube (prismNeg i G).hskel G.hskel
      (glueHypNeg i G) (Fin.castSucc j') (fun h => hj' (Fin.castSucc_injective n h)) b]
  have hprism : cl n X x₀ (faceCube n (prismNeg i G).cube (prismNeg i G).hskel (Fin.castSucc j') b) = 1 :=
    prismNeg_faceCl_side i G hj' b
  rw [hprism, mul_one]

/-- The bottom face is unchanged by the positive kill. -/
theorem faceCl_killPos_bottom [NeZero n] [Nontrivial (Fin n)] (i : Fin n) (G : Pinched n X x₀) :
    (killPos i G).faceCl (Fin.last n) false = G.faceCl (Fin.last n) false := by
  change cl n X x₀ (faceCube n
      (glueAt (Fin.castSucc i) G.cube (prismPos i G).cube (glueHypPos i G))
      (glueAt_skel (Fin.castSucc i) G.cube (prismPos i G).cube G.hskel (prismPos i G).hskel
        (glueHypPos i G)) (Fin.last n) false)
    = cl n X x₀ (faceCube n G.cube G.hskel (Fin.last n) false)
  rw [faceCl_glueAt_of (Fin.castSucc i) G.cube (prismPos i G).cube G.hskel (prismPos i G).hskel
      (glueHypPos i G) (Fin.last n) (Fin.castSucc_ne_last i).symm false]
  have hprism : cl n X x₀ (faceCube n (prismPos i G).cube (prismPos i G).hskel (Fin.last n) false) = 1 :=
    prismPos_faceCl_bottom i G
  rw [hprism, one_mul]

/-- The bottom face is unchanged by the negative kill. -/
theorem faceCl_killNeg_bottom [NeZero n] [Nontrivial (Fin n)] (i : Fin n) (G : Pinched n X x₀) :
    (killNeg i G).faceCl (Fin.last n) false = G.faceCl (Fin.last n) false := by
  change cl n X x₀ (faceCube n
      (glueAt (Fin.castSucc i) (prismNeg i G).cube G.cube (glueHypNeg i G))
      (glueAt_skel (Fin.castSucc i) (prismNeg i G).cube G.cube (prismNeg i G).hskel G.hskel
        (glueHypNeg i G)) (Fin.last n) false)
    = cl n X x₀ (faceCube n G.cube G.hskel (Fin.last n) false)
  rw [faceCl_glueAt_of (Fin.castSucc i) (prismNeg i G).cube G.cube (prismNeg i G).hskel G.hskel
      (glueHypNeg i G) (Fin.last n) (Fin.castSucc_ne_last i).symm false]
  have hprism : cl n X x₀ (faceCube n (prismNeg i G).cube (prismNeg i G).hskel (Fin.last n) false) = 1 :=
    prismNeg_faceCl_bottom i G
  rw [hprism, mul_one]

/-- The top face changes by the `(i,1)`-face read through `rhoPos`. -/
theorem faceCl_killPos_top [NeZero n] [Nontrivial (Fin n)] (i : Fin n) (G : Pinched n X x₀) :
    (killPos i G).faceCl (Fin.last n) true
      = (G.faceCl (Fin.castSucc i) true) ^ ((-1 : ℤ) ^ (n - (i : ℕ)))
        * G.faceCl (Fin.last n) true := by
  change cl n X x₀ (faceCube n
      (glueAt (Fin.castSucc i) G.cube (prismPos i G).cube (glueHypPos i G))
      (glueAt_skel (Fin.castSucc i) G.cube (prismPos i G).cube G.hskel (prismPos i G).hskel
        (glueHypPos i G)) (Fin.last n) true)
    = cl n X x₀ (faceCube n G.cube G.hskel (Fin.castSucc i) true) ^ ((-1 : ℤ) ^ (n - (i : ℕ)))
        * cl n X x₀ (faceCube n G.cube G.hskel (Fin.last n) true)
  rw [faceCl_glueAt_of (Fin.castSucc i) G.cube (prismPos i G).cube G.hskel (prismPos i G).hskel
      (glueHypPos i G) (Fin.last n) (Fin.castSucc_ne_last i).symm true]
  have hprism : cl n X x₀ (faceCube n (prismPos i G).cube (prismPos i G).hskel (Fin.last n) true)
      = (cl n X x₀ (faceCube n G.cube G.hskel (Fin.castSucc i) true)) ^ ((-1 : ℤ) ^ (n - (i : ℕ))) :=
    prismPos_faceCl_top i G
  rw [hprism]

/-- The top face changes by the `(i,0)`-face read through `rhoNeg`. -/
theorem faceCl_killNeg_top [NeZero n] [Nontrivial (Fin n)] (i : Fin n) (G : Pinched n X x₀) :
    (killNeg i G).faceCl (Fin.last n) true
      = (G.faceCl (Fin.castSucc i) false) ^ ((-1 : ℤ) ^ (n - (i : ℕ) - 1))
        * G.faceCl (Fin.last n) true := by
  change cl n X x₀ (faceCube n
      (glueAt (Fin.castSucc i) (prismNeg i G).cube G.cube (glueHypNeg i G))
      (glueAt_skel (Fin.castSucc i) (prismNeg i G).cube G.cube (prismNeg i G).hskel G.hskel
        (glueHypNeg i G)) (Fin.last n) true)
    = cl n X x₀ (faceCube n G.cube G.hskel (Fin.castSucc i) false) ^ ((-1 : ℤ) ^ (n - (i : ℕ) - 1))
        * cl n X x₀ (faceCube n G.cube G.hskel (Fin.last n) true)
  rw [faceCl_glueAt_of (Fin.castSucc i) (prismNeg i G).cube G.cube (prismNeg i G).hskel G.hskel
      (glueHypNeg i G) (Fin.last n) (Fin.castSucc_ne_last i).symm true]
  have hprism : cl n X x₀ (faceCube n (prismNeg i G).cube (prismNeg i G).hskel (Fin.last n) true)
      = (cl n X x₀ (faceCube n G.cube G.hskel (Fin.castSucc i) false)) ^ ((-1 : ℤ) ^ (n - (i : ℕ) - 1)) :=
    prismNeg_faceCl_top i G
  rw [hprism, mul_comm]


/-! ## Pointwise constancy is preserved by the kills -/

/-- A side face is (globally) constant `x₀`. -/
def FaceConst {n : ℕ} (G : Pinched n X x₀) (i : Fin n) (b : Bool) : Prop :=
  ∀ v : IC n, G.cube (faceCM (Fin.castSucc i) (bval b) v) = x₀

theorem faceConst_glueAt {m : ℕ} {X : Type} [TopologicalSpace X] {x₀ : X} (c : Fin (m+1))
    (f g : C(IC (m+1), X)) (h : f.comp (faceCM c 1) = g.comp (faceCM c 0))
    (j : Fin (m+1)) (hj : j ≠ c) (b : Bool)
    (hf : ∀ v : IC m, f (faceCM j (bval b) v) = x₀)
    (hg : ∀ v : IC m, g (faceCM j (bval b) v) = x₀) :
    ∀ v : IC m, glueAt c f g h (faceCM j (bval b) v) = x₀ := by
  obtain ⟨k, hk⟩ := Fin.exists_succAbove_eq (Ne.symm hj)
  have hkc : c = j.succAbove k := hk.symm
  subst hkc
  intro v
  rw [glueAt_face_succAbove j k f g h (bval b) v]
  by_cases hv : (v k : ℝ) ≤ 1/2
  · rw [if_pos hv]; exact hf _
  · rw [if_neg hv]; exact hg _

theorem faceConst_prismPos_side {n : ℕ} (i : Fin n) (G : Pinched n X x₀) {j : Fin n}
    (hj : j ≠ i) (b : Bool) : FaceConst (prismPos i G) j b := by
  intro v
  show G.cube (Work.Stems.HomAdd.killMapPos i (faceCM (Fin.castSucc j) (bval b) v)) = x₀
  exact G.hskel _ (Work.Stems.HomAdd.killMapPos_face_side_mem_InSkel i
    (fun hh => hj (Fin.castSucc_injective n hh)) (Fin.castSucc_ne_last j)
    (by rcases b with _ | _ <;> simp [bval]) v)

theorem faceConst_prismNeg_side {n : ℕ} (i : Fin n) (G : Pinched n X x₀) {j : Fin n}
    (hj : j ≠ i) (b : Bool) : FaceConst (prismNeg i G) j b := by
  intro v
  show G.cube (Work.Stems.HomAdd.killMapNeg i (faceCM (Fin.castSucc j) (bval b) v)) = x₀
  exact G.hskel _ (Work.Stems.HomAdd.killMapNeg_face_side_mem_InSkel i
    (fun hh => hj (Fin.castSucc_injective n hh)) (Fin.castSucc_ne_last j)
    (by rcases b with _ | _ <;> simp [bval]) v)

theorem faceConst_killPos_self {n : ℕ} (i : Fin n) (G : Pinched n X x₀) :
    FaceConst (killPos i G) i true := by
  intro v
  change glueAt (Fin.castSucc i) G.cube (prismPos i G).cube (glueHypPos i G)
      (faceCM (Fin.castSucc i) 1 v) = x₀
  rw [glueAt_face_one]
  exact G.hskel _ (Work.Stems.HomAdd.killMapPos_face_one_mem_InSkel i v)

theorem faceConst_killNeg_self {n : ℕ} (i : Fin n) (G : Pinched n X x₀) :
    FaceConst (killNeg i G) i false := by
  intro v
  change glueAt (Fin.castSucc i) (prismNeg i G).cube G.cube (glueHypNeg i G)
      (faceCM (Fin.castSucc i) 0 v) = x₀
  rw [glueAt_face_zero]
  exact G.hskel _ (Work.Stems.HomAdd.killMapNeg_face_zero_mem_InSkel i v)

theorem faceConst_killPos_preserve {n : ℕ} (i : Fin n) (G : Pinched n X x₀) {j : Fin n} {b : Bool}
    (h : FaceConst G j b) (hp : (j, b) ≠ (i, true)) : FaceConst (killPos i G) j b := by
  rcases eq_or_ne j i with hji | hji
  · have hb : b = false := by
      rcases b with _ | _
      · rfl
      · exact absurd (rfl : (i, true) = (i, true)) (by simpa [hji] using hp)
    rw [hji, hb] at h ⊢
    intro v
    change glueAt (Fin.castSucc i) G.cube (prismPos i G).cube (glueHypPos i G)
        (faceCM (Fin.castSucc i) 0 v) = x₀
    rw [glueAt_face_zero]
    exact h v
  · exact faceConst_glueAt (Fin.castSucc i) G.cube (prismPos i G).cube (glueHypPos i G)
      (Fin.castSucc j) (fun hh => hji (Fin.castSucc_injective n hh)) b h
      (faceConst_prismPos_side i G hji b)

theorem faceConst_killNeg_preserve {n : ℕ} (i : Fin n) (G : Pinched n X x₀) {j : Fin n} {b : Bool}
    (h : FaceConst G j b) (hp : (j, b) ≠ (i, false)) : FaceConst (killNeg i G) j b := by
  rcases eq_or_ne j i with hji | hji
  · have hb : b = true := by
      rcases b with _ | _
      · exact absurd (rfl : (i, false) = (i, false)) (by simpa [hji] using hp)
      · rfl
    rw [hji, hb] at h ⊢
    intro v
    change glueAt (Fin.castSucc i) (prismNeg i G).cube G.cube (glueHypNeg i G)
        (faceCM (Fin.castSucc i) 1 v) = x₀
    rw [glueAt_face_one]
    exact h v
  · exact faceConst_glueAt (Fin.castSucc i) (prismNeg i G).cube G.cube (glueHypNeg i G)
      (Fin.castSucc j) (fun hh => hji (Fin.castSucc_injective n hh)) b
      (faceConst_prismNeg_side i G hji b) h

/-- The kill operation attached to the side face `(i,b)`. -/
def killFace {n : ℕ} (i : Fin n) (b : Bool) (G : Pinched n X x₀) : Pinched n X x₀ :=
  if b then killPos i G else killNeg i G

theorem faceConst_killFace_self {n : ℕ} (i : Fin n) (b : Bool) (G : Pinched n X x₀) :
    FaceConst (killFace i b G) i b := by
  rcases b with _ | _
  · exact faceConst_killNeg_self i G
  · exact faceConst_killPos_self i G

theorem faceConst_killFace_preserve {n : ℕ} (i : Fin n) (b : Bool) (G : Pinched n X x₀)
    {j : Fin n} {d : Bool} (h : FaceConst G j d) (hp : (j, d) ≠ (i, b)) :
    FaceConst (killFace i b G) j d := by
  rcases b with _ | _
  · exact faceConst_killNeg_preserve i G h (by simpa using hp)
  · exact faceConst_killPos_preserve i G h (by simpa using hp)

/-- Killing a list of side faces. -/
def killList {n : ℕ} (L : List (Fin n × Bool)) (G : Pinched n X x₀) : Pinched n X x₀ :=
  L.foldl (fun G p => killFace p.1 p.2 G) G

theorem faceConst_killList_preserve {n : ℕ} (L : List (Fin n × Bool)) (G : Pinched n X x₀)
    (p : Fin n × Bool) (h : FaceConst G p.1 p.2) : FaceConst (killList L G) p.1 p.2 := by
  induction L generalizing G with
  | nil => exact h
  | cons q L ih =>
      refine ih (killFace q.1 q.2 G) ?_
      by_cases hqp : q = p
      · rw [hqp]; exact faceConst_killFace_self p.1 p.2 G
      · exact faceConst_killFace_preserve q.1 q.2 G h (fun hq => hqp hq.symm)

theorem faceConst_killList_of_mem {n : ℕ} (L : List (Fin n × Bool)) (G : Pinched n X x₀)
    (p : Fin n × Bool) (hp : p ∈ L) : FaceConst (killList L G) p.1 p.2 := by
  induction L generalizing G with
  | nil => simp at hp
  | cons q L ih =>
      rw [List.mem_cons] at hp
      rcases hp with hp' | hpL
      · rw [hp']
        show FaceConst (killList L (killFace q.1 q.2 G)) q.1 q.2
        exact faceConst_killList_preserve L (killFace q.1 q.2 G) q
          (faceConst_killFace_self q.1 q.2 G)
      · exact ih (killFace q.1 q.2 G) hpL

/-- The list of all side faces. -/
def faceList (n : ℕ) : List (Fin n × Bool) :=
  (List.finRange n).flatMap (fun i => [(i, true), (i, false)])

theorem mem_faceList {n : ℕ} (p : Fin n × Bool) : p ∈ faceList n := by
  obtain ⟨i, b⟩ := p
  refine List.mem_flatMap.mpr ⟨i, List.mem_finRange i, ?_⟩
  rcases b with _ | _ <;> simp

/-! ## The invariant -/

/-- The exponents of the invariant: the sign contributed by the `i`-th side coordinate. -/
def sExp (n : ℕ) (j : Fin n) (b : Bool) : ℤ :=
  if b then (-1 : ℤ) ^ (n - (j : ℕ)) else (-1 : ℤ) ^ (n - (j : ℕ) - 1)

/-- The `j`-th factor of the product `Qs`. -/
def qFac {n : ℕ} [NeZero n] [Nontrivial (Fin n)] (G : Pinched n X x₀) (j : Fin n) :
    HomotopyGroup (Fin n) X x₀ :=
  (G.faceCl (Fin.castSucc j) false) ^ (sExp n j false)
    * (G.faceCl (Fin.castSucc j) true) ^ (sExp n j true)

/-- The product of the side-face factors. -/
def Qs {n : ℕ} [NeZero n] [Nontrivial (Fin n)] (G : Pinched n X x₀) :
    HomotopyGroup (Fin n) X x₀ := ∏ j : Fin n, G.qFac j

/-- The product of the side-face factors other than the `i`-th. -/
def QsErase {n : ℕ} [NeZero n] [Nontrivial (Fin n)] (G : Pinched n X x₀) (i : Fin n) :
    HomotopyGroup (Fin n) X x₀ :=
  ∏ j ∈ Finset.univ.erase i, G.qFac j

/-- The top-minus-bottom difference. -/
def Cdiff {n : ℕ} [NeZero n] [Nontrivial (Fin n)] (G : Pinched n X x₀) :
    HomotopyGroup (Fin n) X x₀ :=
  G.faceCl (Fin.last n) true * (G.faceCl (Fin.last n) false)⁻¹

/-- The invariant of the killing argument. -/
def Rinv {n : ℕ} [NeZero n] [Nontrivial (Fin n)] (G : Pinched n X x₀) :
    HomotopyGroup (Fin n) X x₀ := Qs G * Cdiff G

variable {n : ℕ}

theorem Qs_eq_mul_erase [NeZero n] [Nontrivial (Fin n)] (G : Pinched n X x₀) (i : Fin n) :
    Qs G = G.qFac i * QsErase G i := by
  rw [Qs, QsErase]
  exact (Finset.mul_prod_erase Finset.univ (fun j => G.qFac j) (Finset.mem_univ i)).symm

/-- **The invariant is preserved by the positive kill.** -/
theorem Rinv_killPos [NeZero n] [Nontrivial (Fin n)] (i : Fin n) (G : Pinched n X x₀) :
    Rinv (killPos i G) = Rinv G := by
  have hs1 : sExp n i true = (-1 : ℤ) ^ (n - (i : ℕ)) := rfl
  have hs0 : sExp n i false = (-1 : ℤ) ^ (n - (i : ℕ) - 1) := rfl
  have herase : QsErase (killPos i G) i = QsErase G i := by
    rw [QsErase, QsErase]
    refine Finset.prod_congr rfl (fun j hj => ?_)
    have hji : j ≠ i := (Finset.mem_erase.mp hj).1
    rw [qFac, qFac, faceCl_killPos_side i G hji false, faceCl_killPos_side i G hji true]
  rw [Rinv, Rinv, Qs_eq_mul_erase (killPos i G) i, Qs_eq_mul_erase G i, herase,
    Cdiff, Cdiff, faceCl_killPos_bottom i G, faceCl_killPos_top i G]
  simp only [qFac, hs0, hs1, faceCl_killPos_same_false i G, faceCl_killPos_same_true i G,
    one_zpow, mul_assoc, mul_comm, mul_left_comm, mul_inv_cancel, inv_mul_cancel, one_mul, mul_one]

/-- **The invariant is preserved by the negative kill.** -/
theorem Rinv_killNeg [NeZero n] [Nontrivial (Fin n)] (i : Fin n) (G : Pinched n X x₀) :
    Rinv (killNeg i G) = Rinv G := by
  have hs1 : sExp n i true = (-1 : ℤ) ^ (n - (i : ℕ)) := rfl
  have hs0 : sExp n i false = (-1 : ℤ) ^ (n - (i : ℕ) - 1) := rfl
  have herase : QsErase (killNeg i G) i = QsErase G i := by
    rw [QsErase, QsErase]
    refine Finset.prod_congr rfl (fun j hj => ?_)
    have hji : j ≠ i := (Finset.mem_erase.mp hj).1
    rw [qFac, qFac, faceCl_killNeg_side i G hji false, faceCl_killNeg_side i G hji true]
  rw [Rinv, Rinv, Qs_eq_mul_erase (killNeg i G) i, Qs_eq_mul_erase G i, herase,
    Cdiff, Cdiff, faceCl_killNeg_bottom i G, faceCl_killNeg_top i G]
  simp only [qFac, hs0, hs1, faceCl_killNeg_same_false i G, faceCl_killNeg_same_true i G,
    one_zpow, mul_assoc, mul_comm, mul_left_comm, mul_inv_cancel, inv_mul_cancel, one_mul, mul_one]

theorem Rinv_killFace [NeZero n] [Nontrivial (Fin n)] (i : Fin n) (b : Bool)
    (G : Pinched n X x₀) : Rinv (killFace i b G) = Rinv G := by
  rcases b with _ | _
  · exact Rinv_killNeg i G
  · exact Rinv_killPos i G

theorem Rinv_killList [NeZero n] [Nontrivial (Fin n)] (L : List (Fin n × Bool))
    (G : Pinched n X x₀) : Rinv (killList L G) = Rinv G := by
  induction L generalizing G with
  | nil => rfl
  | cons q L ih =>
      show Rinv (killList L (killFace q.1 q.2 G)) = Rinv G
      rw [ih (killFace q.1 q.2 G), Rinv_killFace q.1 q.2 G]

/-- If all side faces of a cube are constant then the invariant is `1`. -/
theorem Rinv_eq_one_of_faceConst [NeZero n] [Nontrivial (Fin n)] (G : Pinched n X x₀)
    (h : ∀ i : Fin n, ∀ b : Bool, FaceConst G i b) : Rinv G = 1 := by
  have hQ : Qs G = 1 := by
    rw [Qs]
    refine Finset.prod_eq_one (fun j _ => ?_)
    rw [qFac]
    simp only [faceCl_eq_one_of_const G (Fin.castSucc j) false (h j false),
      faceCl_eq_one_of_const G (Fin.castSucc j) true (h j true), one_zpow, one_mul]
  have hbt : G.faceCl (Fin.last n) true = G.faceCl (Fin.last n) false := by
    rw [faceCl, faceCl]
    have hrel : (faceCube n G.cube G.hskel (Fin.last n) false).1.HomotopyRel
        (faceCube n G.cube G.hskel (Fin.last n) true).1 (Cube.boundary (Fin n)) :=
      { toFun := fun p : unitInterval × IC n => G.cube (faceCM (Fin.last n) p.1 p.2)
        continuous_toFun := by
          refine G.cube.continuous.comp ?_
          rw [continuous_pi_iff]
          intro m
          rcases Fin.eq_self_or_eq_succAbove (Fin.last n) m with hm | ⟨k', hk'⟩
          · rw [show (fun p : unitInterval × IC n => faceCM (Fin.last n) p.1 p.2 m)
                = fun p => p.1 from funext (fun p => by rw [hm, faceCM_apply,
                  Work.RatHurewicz.faceFun_apply_same])]
            exact continuous_fst
          · rw [show (fun p : unitInterval × IC n => faceCM (Fin.last n) p.1 p.2 m)
                = fun p => p.2 k' from funext (fun p => by rw [hk', faceCM_apply,
                  Work.RatHurewicz.faceFun_apply_succAbove])]
            exact (continuous_apply k').comp continuous_snd
        map_zero_left := by
          intro v
          show G.cube (faceCM (Fin.last n) (0 : unitInterval) v)
            = G.cube (faceCM (Fin.last n) 0 v)
          rfl
        map_one_left := by
          intro v
          show G.cube (faceCM (Fin.last n) (1 : unitInterval) v)
            = G.cube (faceCM (Fin.last n) 1 v)
          rfl
        prop' := by
          intro t v hv
          obtain ⟨j, hj⟩ := hv
          have key : ∀ s : unitInterval, G.cube (faceCM (Fin.last n) s v) = x₀ := by
            intro s
            have hval : (faceCM (Fin.last n) s v : IC (n+1)) (Fin.castSucc j) = v j := by
              rw [faceCM_apply,
                show Fin.castSucc j = (Fin.last n).succAbove j from
                  (congrFun Fin.succAbove_last j).symm,
                Work.RatHurewicz.faceFun_apply_succAbove]
            have hz : faceCM (Fin.last n) s v = faceCM (Fin.castSucc j) (v j)
                (fun j' => faceCM (Fin.last n) s v ((Fin.castSucc j).succAbove j')) := by
              rw [sliceFaceCM (Fin.castSucc j) (v j) (faceCM (Fin.last n) s v), ← hval,
                Function.update_eq_self]
            rw [hz]
            rcases hj with h0 | h1
            · rw [h0]; exact h j false _
            · rw [h1]; exact h j true _
          show G.cube (faceCM (Fin.last n) t v) = G.cube (faceCM (Fin.last n) 0 v)
          rw [key t]
          exact (key 0).symm }
    have hhom : GenLoop.Homotopic (faceCube n G.cube G.hskel (Fin.last n) false)
        (faceCube n G.cube G.hskel (Fin.last n) true) := ⟨hrel⟩
    exact (Quotient.sound hhom).symm
  have hC : Cdiff G = 1 := by
    rw [Cdiff, hbt, mul_inv_cancel]
  rw [Rinv, hQ, hC, mul_one]

/-- **The invariant is `1` for every pinched cube** (kill all the side faces). -/
theorem Rinv_eq_one [NeZero n] [Nontrivial (Fin n)] (G : Pinched n X x₀) : Rinv G = 1 := by
  rw [← Rinv_killList (faceList n) G]
  exact Rinv_eq_one_of_faceConst (killList (faceList n) G)
    (fun i b => faceConst_killList_of_mem (faceList n) G (i, b) (mem_faceList (i, b)))

/-! ## The final algebra -/

/-- `(-1)^{k-j-1} = (-1)^j · (-1)^{k-1}`. -/
theorem neg_one_pow_sub (k j : ℕ) (hj : j < k) :
    (-1 : ℤ) ^ (k - j - 1) = (-1 : ℤ) ^ j * (-1 : ℤ) ^ (k - 1) := by
  have h2 : (-1 : ℤ) ^ (k - 1) = (-1 : ℤ) ^ (k - j - 1) * (-1 : ℤ) ^ j := by
    rw [← pow_add, show k - j - 1 + j = k - 1 by omega]
  have hsq : (-1 : ℤ) ^ j * (-1 : ℤ) ^ j = 1 := by
    rw [← pow_add, show j + j = 2 * j by ring, pow_mul,
      show (-1 : ℤ) ^ 2 = 1 by norm_num, one_pow]
  have key : (-1 : ℤ) ^ j * (-1 : ℤ) ^ (k - 1) = (-1 : ℤ) ^ (k - j - 1) := by
    rw [h2, ← mul_assoc, mul_comm ((-1 : ℤ) ^ j) ((-1 : ℤ) ^ (k - j - 1)), mul_assoc, hsq,
      mul_one]
  exact key.symm

/-- The alternating product of the side-face classes. -/
def Aalt {n : ℕ} [NeZero n] [Nontrivial (Fin n)] (G : Pinched n X x₀) :
    HomotopyGroup (Fin n) X x₀ :=
  ∏ j : Fin n, (G.faceCl (Fin.castSucc j) false * (G.faceCl (Fin.castSucc j) true)⁻¹)
    ^ ((-1 : ℤ) ^ (j : ℕ))

theorem qFac_eq [NeZero n] [Nontrivial (Fin n)] (G : Pinched n X x₀) (j : Fin n) :
    G.qFac j = (G.faceCl (Fin.castSucc j) false * (G.faceCl (Fin.castSucc j) true)⁻¹)
      ^ (sExp n j false) := by
  have hs : sExp n j true = - sExp n j false := by
    show (-1 : ℤ) ^ (n - (j : ℕ)) = - ((-1 : ℤ) ^ (n - (j : ℕ) - 1))
    rw [← neg_neg_one_pow (m := n - (j : ℕ)) (by omega), neg_neg]
  rw [qFac, hs, zpow_neg, mul_zpow, inv_zpow]

theorem Qs_eq_Aalt [NeZero n] [Nontrivial (Fin n)] (G : Pinched n X x₀) :
    Qs G = (Aalt G) ^ ((-1 : ℤ) ^ (n - 1)) := by
  rw [Qs, Aalt]
  rw [show (∏ j : Fin n, G.qFac j)
      = ∏ j : Fin n, (G.faceCl (Fin.castSucc j) false * (G.faceCl (Fin.castSucc j) true)⁻¹)
          ^ (sExp n j false) from Finset.prod_congr rfl (fun j _ => qFac_eq G j)]
  rw [← Finset.prod_zpow]
  refine Finset.prod_congr rfl (fun j _ => ?_)
  rw [← zpow_mul]
  congr 1
  show (-1 : ℤ) ^ (n - (j : ℕ) - 1) = (-1 : ℤ) ^ (j : ℕ) * (-1 : ℤ) ^ (n - 1)
  exact neg_one_pow_sub n (j : ℕ) j.isLt

/-- `(b · a⁻¹)^{-k} = a^k · b^{-k}`. -/
theorem zpow_neg_swap {G : Type} [CommGroup G] (a b : G) (k : ℤ) :
    (b * a⁻¹) ^ (-k) = a ^ k * b ^ (-k) := by
  rw [zpow_neg, mul_zpow, inv_zpow, mul_inv_rev, inv_inv, ← zpow_neg b k]

/-- The signed product of all face classes, in terms of `Aalt` and `Cdiff`. -/
theorem prod_faces_eq [NeZero n] [Nontrivial (Fin n)] (G : Pinched n X x₀) :
    (∏ i : Fin (n+1), (G.faceCl i false) ^ ((-1 : ℤ) ^ (i : ℕ))
        * (G.faceCl i true) ^ (-((-1 : ℤ) ^ (i : ℕ))))
      = Aalt G * (Cdiff G) ^ (-((-1 : ℤ) ^ (n : ℕ))) := by
  rw [Fin.prod_univ_castSucc]
  congr 1
  · rw [Aalt]
    refine Finset.prod_congr rfl (fun j _ => ?_)
    rw [Fin.val_castSucc, zpow_neg, mul_zpow, inv_zpow]
  · rw [Cdiff, Fin.val_last]
    exact (zpow_neg_swap (G.faceCl (Fin.last n) false) (G.faceCl (Fin.last n) true)
      ((-1 : ℤ) ^ n)).symm

/-- **The signed product of the face classes is `1`** whenever the invariant is `1`. -/
theorem prod_eq_one_of_Rinv [NeZero n] [Nontrivial (Fin n)] (G : Pinched n X x₀)
    (h : Rinv G = 1) :
    (∏ i : Fin (n+1), (G.faceCl i false) ^ ((-1 : ℤ) ^ (i : ℕ))
        * (G.faceCl i true) ^ (-((-1 : ℤ) ^ (i : ℕ)))) = 1 := by
  rw [prod_faces_eq G]
  have hA : (Aalt G) ^ ((-1 : ℤ) ^ (n - 1)) * Cdiff G = 1 := by
    rw [← Qs_eq_Aalt G, ← Rinv]
    exact h
  have hτ : (-1 : ℤ) ^ (n - 1) = -((-1 : ℤ) ^ n) := by
    have hn1 : 1 ≤ n := Nat.one_le_iff_ne_zero.mpr (NeZero.ne n)
    have h1 : (-1 : ℤ) ^ n = (-1 : ℤ) ^ (n - 1) * (-1) := by
      rw [← pow_succ, show n - 1 + 1 = n by omega]
    rw [h1]; ring
  rcases Nat.even_or_odd n with hn | hn
  · have hn1 : ((-1 : ℤ) ^ n) = 1 := hn.neg_one_pow
    have hτ' : (-1 : ℤ) ^ (n - 1) = -1 := by rw [hτ, hn1]
    have hAC : Aalt G = Cdiff G := by
      have h' := hA
      rw [hτ', zpow_neg_one] at h'
      exact inv_mul_eq_one.mp h'
    rw [hn1, zpow_neg_one, hAC, mul_inv_cancel]
  · have hn1 : ((-1 : ℤ) ^ n) = -1 := hn.neg_one_pow
    have hτ' : (-1 : ℤ) ^ (n - 1) = 1 := by rw [hτ, hn1, neg_neg]
    have hAC : Aalt G * Cdiff G = 1 := by
      have h' := hA
      rw [hτ', zpow_one] at h'
      exact h'
    rw [hn1, neg_neg, zpow_one]
    exact hAC

end Pinched

/-- **The general cubical homotopy-addition statement** (Hutchings `(2.2b)`, all `k`): a cube
`g : I^{k+1} → Y` that is `y` on its `(k-1)`-skeleton has face classes whose signed product is `1`.
Proved by killing the `2k` side faces of the cube with the prism maps (`killMapPos`, `killMapNeg`),
preserving the invariant `Qs · [top] · [bottom]⁻¹`. -/
theorem pinchAllViaNet : Work.RatHurewicz.PinchAll := by
  intro k hk Y hY y g h
  haveI : NeZero k := ⟨fun h0 => by
    rw [h0] at hk
    obtain ⟨x, y, hxy⟩ := hk.exists_pair_ne
    exact hxy (Subsingleton.elim x y)⟩
  exact Pinched.prod_eq_one_of_Rinv (⟨g, h⟩ : Pinched k Y y) (Pinched.Rinv_eq_one _)

end
end Work.RatHurewicz.Walk
