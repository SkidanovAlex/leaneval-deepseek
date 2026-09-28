import Mathlib
import Submission.Work.RatHurewicz.PsiKillsAux
import Submission.Work.Stems.Hur2b.homotopic_const_of_boundary_const

/-!
# The gluing of the pieces of an `(m+3)`-cube, and the cancellation family

Definitions and auxiliary lemmas used by `Work.RatHurewicz.assembly_null` and by the delegated
files `glue_homotopic_const`, `glue_class_of_collapse`, `exists_collapse_zero`:

* `faceSet`, `glueVal`, `glue` — the gluing of the pieces `Ψ (τ ∘ faceCM i (cval b))` along the
  faces of `∂I^{m+3}` (well defined: the pieces are `x₀` on their boundaries);
* `unpinPt`, `unpinB` — the swept point `(radialPt u, (1-r)·tau u + r)` of `∂I^{m+3}`, and the
  single-cube sweep `PsiB (unpinB 1 u) = s (radialPt u)`;
* the seam agreement `unpinB_agree`;
* `glueCancel`, `clampFamily`, `shrinkFamily` — the three families of the cancellation;
* `cl_comp_collapse` — the class of a cube model of the gluing is `1`.
-/

open scoped unitInterval Topology
open Work.Stems.Cubical

namespace Work.RatHurewicz

noncomputable section

variable {X : Type} [TopologicalSpace X] {x₀ : X}

/-! ## The faces of `∂I^{m+3}` -/

/-- The face `{z i = cval b}` of `I^{m+3}`. -/
def faceSet (m : ℕ) (i : Fin (m + 3)) (b : Fin 2) : Set (IC (m + 3)) := {z | z i = cval b}

theorem isClosed_faceSet (m : ℕ) (i : Fin (m + 3)) (b : Fin 2) :
    IsClosed (faceSet m i b) :=
  isClosed_eq (continuous_apply i) continuous_const

theorem mem_faceSet_iff {m : ℕ} {i : Fin (m + 3)} {b : Fin 2} {z : IC (m + 3)} :
    z ∈ faceSet m i b ↔ z i = cval b := Iff.rfl

/-- Every boundary point of `I^{m+3}` lies on one of the faces. -/
theorem exists_faceSet_of_mem_boundary (m : ℕ) {z : IC (m + 3)}
    (hz : z ∈ Cube.boundary (Fin (m + 3))) : ∃ (i : Fin (m + 3)) (b : Fin 2), z ∈ faceSet m i b := by
  obtain ⟨i, hi | hi⟩ := hz
  · exact ⟨i, 0, by show z i = cval 0; rw [hi, cval_zero]⟩
  · exact ⟨i, 1, by show z i = cval 1; rw [hi, cval_one]⟩

/-- A point of a face, reconstructed from its deleted coordinates. -/
theorem faceCM_delG_of_mem_faceSet {m : ℕ} {i : Fin (m + 3)} {b : Fin 2} {z : IC (m + 3)}
    (hz : z ∈ faceSet m i b) : faceCM i (cval b) (delG (m + 2) i z) = z :=
  delG_faceCM i z (mem_faceSet_iff.mp hz)

/-- If `z` lies on two different faces then its `i`-deletion lies on the boundary of `I^{m+2}`. -/
theorem delG_mem_boundary_of_mem_two {m : ℕ} {i i' : Fin (m + 3)} {b b' : Fin 2}
    {z : IC (m + 3)} (hz : z ∈ faceSet m i b) (hz' : z ∈ faceSet m i' b') (hii : i ≠ i') :
    delG (m + 2) i z ∈ Cube.boundary (Fin (m + 2)) := by
  obtain ⟨k, hk⟩ := Fin.exists_succAbove_eq (Ne.symm hii)
  have hk' : i.succAbove k = i' := hk
  fin_cases b'
  · exact ⟨k, Or.inl (by rw [delG_apply, hk', hz']; rfl)⟩
  · exact ⟨k, Or.inr (by rw [delG_apply, hk', hz']; rfl)⟩

/-! ## The value of the gluing on a face -/

/-- The value prescribed on the face `(i,b)`: the piece `Ψ(τ ∘ faceCM i (cval b))` read in the
face's own coordinates. -/
def glueVal (N m : ℕ) (K : Tower x₀ N) (hN : m + 1 ≤ N) (τ : C(IC (m + 3), X))
    (ib : Fin (m + 3) × Fin 2) (z : IC (m + 3)) : X :=
  (piece N m K hN τ ib) (delG (m + 2) ib.1 z)

theorem continuous_glueVal (N m : ℕ) (K : Tower x₀ N) (hN : m + 1 ≤ N)
    (τ : C(IC (m + 3), X)) (ib : Fin (m + 3) × Fin 2) :
    Continuous (glueVal N m K hN τ ib) :=
  (piece N m K hN τ ib).1.continuous.comp (delG (m + 2) ib.1).continuous

/-- **The prescribed values agree on the overlaps**: two pieces meeting along an `(m+1)`-face are
both `x₀` there. -/
theorem glueVal_agree (N m : ℕ) (K : Tower x₀ N) (hN : m + 1 ≤ N) (τ : C(IC (m + 3), X))
    {ib ib' : Fin (m + 3) × Fin 2} {z : IC (m + 3)} (hz : z ∈ faceSet m ib.1 ib.2)
    (hz' : z ∈ faceSet m ib'.1 ib'.2) :
    glueVal N m K hN τ ib z = glueVal N m K hN τ ib' z := by
  rcases ib with ⟨i, b⟩
  rcases ib' with ⟨i', b'⟩
  rcases eq_or_ne i i' with h | h
  · subst h
    have hb : b = b' := by
      have hc : cval b = cval b' := by rw [← hz, hz']
      fin_cases b <;> fin_cases b' <;> simp_all [cval]
    subst hb; rfl
  · rw [glueVal, glueVal]
    exact (piece N m K hN τ (i, b)).2 _ (delG_mem_boundary_of_mem_two hz hz' h) |>.trans
      ((piece N m K hN τ (i', b')).2 _ (delG_mem_boundary_of_mem_two hz' hz (Ne.symm h))).symm

/-! ## The gluing -/

/-- **The gluing of the pieces over `∂I^{m+3}`.** -/
def glue (N m : ℕ) (K : Tower x₀ N) (hN : m + 1 ≤ N) (τ : C(IC (m + 3), X)) :
    C(↥(Cube.boundary (Fin (m + 3))), X) :=
  Classical.choose (exists_cubeBoundary (m + 2)
    (fun ib : Fin (m + 3) × Fin 2 => faceSet m ib.1 ib.2)
    (fun ib => isClosed_faceSet m ib.1 ib.2)
    (fun z hz => by
      obtain ⟨i, b, hb⟩ := exists_faceSet_of_mem_boundary m hz
      exact ⟨(i, b), hb⟩)
    (fun ib => glueVal N m K hN τ ib)
    (fun ib => (continuous_glueVal N m K hN τ ib).continuousOn)
    (fun ib ib' _ hz hz' => glueVal_agree N m K hN τ hz hz'))

theorem glue_apply_face (N m : ℕ) (K : Tower x₀ N) (hN : m + 1 ≤ N) (τ : C(IC (m + 3), X))
    (ib : Fin (m + 3) × Fin 2) (z : ↥(Cube.boundary (Fin (m + 3))))
    (hz : (z : IC (m + 3)) ∈ faceSet m ib.1 ib.2) :
    glue N m K hN τ z = glueVal N m K hN τ ib z :=
  Classical.choose_spec (exists_cubeBoundary (m + 2)
    (fun ib : Fin (m + 3) × Fin 2 => faceSet m ib.1 ib.2)
    (fun ib => isClosed_faceSet m ib.1 ib.2)
    (fun z hz => by
      obtain ⟨i, b, hb⟩ := exists_faceSet_of_mem_boundary m hz
      exact ⟨(i, b), hb⟩)
    (fun ib => glueVal N m K hN τ ib)
    (fun ib => (continuous_glueVal N m K hN τ ib).continuousOn)
    (fun ib ib' _ hz hz' => glueVal_agree N m K hN τ hz hz')) z ib hz

/-- The gluing is `x₀` on the `(m+1)`-skeleton of `∂I^{m+3}`. -/
theorem glue_eq_x₀_of_mem_two (N m : ℕ) (K : Tower x₀ N) (hN : m + 1 ≤ N)
    (τ : C(IC (m + 3), X)) (z : ↥(Cube.boundary (Fin (m + 3))))
    {i i' : Fin (m + 3)} {b b' : Fin 2} (hz : (z : IC (m + 3)) ∈ faceSet m i b)
    (hz' : (z : IC (m + 3)) ∈ faceSet m i' b') (hii : i ≠ i') :
    glue N m K hN τ z = x₀ :=
  (glue_apply_face N m K hN τ (i, b) z hz).trans
    ((piece N m K hN τ (i, b)).2 _ (delG_mem_boundary_of_mem_two hz hz' hii))


/-! ## The un-pinning point of `∂I^{m+3}`

For `u : I^{m+2}` the pinch point is `iota u = (radialPt u, tau u)`, a point of `∂I^{m+3}`.  As `r`
goes from `0` to `1` we sweep the "dome height" `tau u` up to `1`; the resulting point stays in
`∂I^{m+3}` (for `sig u ≤ 1/2` because the height is `1`, for `sig u ≥ 1/2` because one of the space
coordinates is `0` or `1`).  This is the geometric content of the cancellation.
-/

@[simp] theorem coe_zero_I : (((0 : unitInterval) : ℝ)) = 0 := rfl
@[simp] theorem coe_one_I : (((1 : unitInterval) : ℝ)) = 1 := rfl

/-- The swept "dome height". -/
def unpinR (m : ℕ) (r : unitInterval) (u : IC (m + 2)) : ℝ :=
  (1 - (r : ℝ)) * ((tau (m + 2) (by omega) u : unitInterval) : ℝ) + (r : ℝ)

theorem unpinR_mem (m : ℕ) (r : unitInterval) (u : IC (m + 2)) :
    unpinR m r u ∈ Set.Icc (0 : ℝ) 1 := by
  have ht0 := (tau (m + 2) (by omega) u).2.1
  have ht1 := (tau (m + 2) (by omega) u).2.2
  have hr0 := r.2.1
  have hr1 := r.2.2
  have h1 : (0 : ℝ) ≤ 1 - (r : ℝ) := by linarith
  rw [unpinR]
  constructor
  · nlinarith [mul_nonneg h1 ht0]
  · nlinarith [mul_le_mul_of_nonneg_left ht1 h1]

/-- The swept point of `∂I^{m+3}`. -/
def unpinPt (m : ℕ) (r : unitInterval) (u : IC (m + 2)) : IC (m + 3) :=
  Fin.snoc (radialPt (m + 2) (by omega) u)
    (⟨unpinR m r u, (unpinR_mem m r u).1, (unpinR_mem m r u).2⟩ : unitInterval)

@[simp] theorem unpinPt_last (m : ℕ) (r : unitInterval) (u : IC (m + 2)) :
    unpinPt m r u (Fin.last (m + 2)) =
      (⟨unpinR m r u, (unpinR_mem m r u).1, (unpinR_mem m r u).2⟩ : unitInterval) := by
  simp [unpinPt]

@[simp] theorem unpinPt_last_val (m : ℕ) (r : unitInterval) (u : IC (m + 2)) :
    ((unpinPt m r u (Fin.last (m + 2)) : unitInterval) : ℝ) = unpinR m r u := by
  simp

@[simp] theorem unpinPt_castSucc (m : ℕ) (r : unitInterval) (u : IC (m + 2))
    (i : Fin (m + 2)) :
    unpinPt m r u (Fin.castSucc i) = radialPt (m + 2) (by omega) u i := by
  simp [unpinPt]

theorem continuous_unpinR (m : ℕ) :
    Continuous fun p : IC (m + 2) × unitInterval => unpinR m p.2 p.1 := by
  rw [show unpinR m = fun (r : unitInterval) (u : IC (m + 2)) =>
      (1 - (r : ℝ)) * ((tau (m + 2) (by omega) u : unitInterval) : ℝ) + (r : ℝ) from rfl]
  have hr : Continuous fun p : IC (m + 2) × unitInterval => ((p.2 : unitInterval) : ℝ) :=
    continuous_subtype_val.comp continuous_snd
  have ht : Continuous fun p : IC (m + 2) × unitInterval =>
      ((tau (m + 2) (by omega) p.1 : unitInterval) : ℝ) :=
    continuous_subtype_val.comp ((continuous_tau (m + 2) (by omega)).comp continuous_fst)
  exact ((continuous_const.sub hr).mul ht).add hr

theorem continuous_unpinPt (m : ℕ) :
    Continuous fun p : IC (m + 2) × unitInterval => unpinPt m p.2 p.1 := by
  rw [continuous_iff_continuousAt]
  intro p
  rw [ContinuousAt, tendsto_pi_nhds]
  intro j
  rcases Fin.eq_castSucc_or_eq_last j with ⟨i, rfl⟩ | rfl
  · simp only [unpinPt_castSucc]
    exact (continuous_radialPt_coord (m + 2) (by omega) i).continuousAt.comp continuousAt_fst
  · simp only [unpinPt_last]
    exact (Continuous.subtype_mk (continuous_unpinR m) _).continuousAt

/-- The swept point lies in `∂I^{m+3}`. -/
theorem unpinPt_mem_boundary (m : ℕ) (r : unitInterval) (u : IC (m + 2)) :
    unpinPt m r u ∈ Cube.boundary (Fin (m + 3)) := by
  by_cases hsig : sig (m + 2) (by omega) u ≤ 1 / 2
  · refine ⟨Fin.last (m + 2), Or.inr ?_⟩
    apply Subtype.ext
    rw [unpinPt_last_val, unpinR]
    have ht : ((tau (m + 2) (by omega) u : unitInterval) : ℝ) = 1 := by
      rw [tau_coe, tauR, min_eq_left]
      linarith
    rw [ht, coe_one_I]
    ring
  · push_neg at hsig
    obtain ⟨j, -, hj⟩ := Finset.exists_mem_eq_sup' (s := Finset.univ)
      (finNonempty (m := m + 2) (by omega)) (fun i => |2 * ((u i : unitInterval) : ℝ) - 1|)
    have hs : sig (m + 2) (by omega) u = |2 * ((u j : unitInterval) : ℝ) - 1| := by
      rw [sig_def]; exact hj
    have hmax : max (sig (m + 2) (by omega) u) (1 / 2) = sig (m + 2) (by omega) u :=
      max_eq_left hsig.le
    have habs : |2 * ((u j : unitInterval) : ℝ) - 1| = sig (m + 2) (by omega) u := hs.symm
    rcases (abs_eq (sig_nonneg (m + 2) (by omega) u)).mp habs with h | h
    · have hc : ((radialPt (m + 2) (by omega) u j : unitInterval) : ℝ) = 1 := by
        rw [radialPt_coe, radialR, hmax]
        field_simp
        linarith
      refine ⟨Fin.castSucc j, Or.inr ?_⟩
      rw [unpinPt_castSucc]
      apply Subtype.ext
      rw [hc]
      norm_num
    · have hc : ((radialPt (m + 2) (by omega) u j : unitInterval) : ℝ) = 0 := by
        rw [radialPt_coe, radialR, hmax]
        field_simp
        linarith
      refine ⟨Fin.castSucc j, Or.inl ?_⟩
      rw [unpinPt_castSucc]
      apply Subtype.ext
      rw [hc]
      norm_num

/-- The swept point as an element of the boundary subtype. -/
def unpinB (m : ℕ) (r : unitInterval) (u : IC (m + 2)) :
    ↥(Cube.boundary (Fin (m + 3))) := ⟨unpinPt m r u, unpinPt_mem_boundary m r u⟩

@[simp] theorem unpinB_coe (m : ℕ) (r : unitInterval) (u : IC (m + 2)) :
    ((unpinB m r u : ↥(Cube.boundary (Fin (m + 3)))) : IC (m + 3)) = unpinPt m r u := rfl

/-- At `r = 0` the swept point is the pinch point `iota u`. -/
theorem unpinPt_zero (m : ℕ) (u : IC (m + 2)) :
    unpinPt m 0 u = iotaFun (m + 2) (by omega) u := by
  funext i
  rcases Fin.eq_castSucc_or_eq_last i with ⟨j, rfl⟩ | rfl
  · rw [unpinPt_castSucc, iotaFun_castSucc]
  · apply Subtype.ext
    rw [unpinPt_last_val, iotaFun_last]
    simp only [unpinR, coe_zero_I]
    ring

/-- At `r = 1` the swept point lies on the top face `{z_last = 1}` of `∂I^{m+3}`. -/
theorem unpinPt_one_last (m : ℕ) (u : IC (m + 2)) :
    unpinPt m 1 u (Fin.last (m + 2)) = 1 := by
  apply Subtype.ext
  rw [unpinPt_last_val]
  simp only [unpinR, coe_one_I]
  ring


/-! ## The single-cube sweep

Evaluating the boundary data of a cube `s` at the swept point moves the `K`-fillings of the faces
onto the faces themselves: at `r = 1` the boundary data of `s` read at the swept point is
`s ∘ radialPt`.  At `r = 0` it is `Ψ s`.  This is the elementary geometric input of the
cancellation.
-/

theorem PsiB_unpinB_one (N m : ℕ) (K : Tower x₀ N) (hN : m + 1 ≤ N)
    (s : C(IC (m + 2), X)) (u : IC (m + 2)) :
    PsiB N m K hN s (unpinB m 1 u) = s (radialPt (m + 2) (by omega) u) := by
  have hz : (unpinB m 1 u : IC (m + 3)) (Fin.last (m + 2)) = cval 1 := by
    rw [unpinB_coe]
    apply Subtype.ext
    rw [unpinPt_last_val, cval_one]
    simp only [unpinR, coe_one_I]
    ring
  have h := boundaryData_apply_face (m := m) (i := Fin.last (m + 2)) (b := 1)
    (PsiB_top N m K hN s) (z := unpinB m 1 u) hz
  rw [h, delG_last]
  congr 1
  funext i
  rw [initC_apply, unpinB_coe, unpinPt_castSucc]

theorem Psi_unpinB_zero (N m : ℕ) (K : Tower x₀ N) (hN : m + 1 ≤ N)
    (s : C(IC (m + 2), X)) (u : IC (m + 2)) :
    PsiB N m K hN s (unpinB m 0 u) = Psi N m K hN s u := by
  rw [Psi_apply]
  congr 1
  apply Subtype.ext
  rw [unpinB_coe]
  exact unpinPt_zero m u

theorem continuous_PsiB_unpinB (N m : ℕ) (K : Tower x₀ N) (hN : m + 1 ≤ N)
    (s : C(IC (m + 2), X)) :
    Continuous fun p : IC (m + 2) × unitInterval => PsiB N m K hN s (unpinB m p.2 p.1) :=
  (PsiB N m K hN s).continuous.comp
    (Continuous.subtype_mk (continuous_unpinPt m) (fun p => unpinPt_mem_boundary m p.2 p.1))


/-! ## The seam consistency of the cancellation family

On the `(m+1)`-skeleton of `∂I^{m+3}` (where two faces meet) the swept values of the boundary data
of the two adjacent pieces agree: both reduce to the `K (m+1)`-filling of the *same* `(m+1)`-face
of `τ`, evaluated at the same point.  This is what makes the cancellation family globally defined.
-/

theorem unpinPt_eq_snoc_of_mem_boundary (m : ℕ) (r : unitInterval) {u : IC (m + 2)}
    (hu : u ∈ Cube.boundary (Fin (m + 2))) :
    unpinPt m r u = Fin.snoc u r := by
  funext i
  cases i using Fin.lastCases with
  | last =>
    rw [unpinPt_last, Fin.snoc_last]
    apply Subtype.ext
    show unpinR m r u = ((r : unitInterval) : ℝ)
    rw [unpinR]
    have ht : ((tau (m + 2) (by omega) u : unitInterval) : ℝ) = 0 := by
      rw [tau_coe, tauR, (sig_eq_one_iff (m + 2) (by omega) u).mpr hu]
      norm_num
    rw [ht]
    ring
  | cast j =>
    rw [unpinPt_castSucc, Fin.snoc_castSucc,
      radialPt_eq_self_of_sig_eq_one (m + 2) (by omega)
        ((sig_eq_one_iff (m + 2) (by omega) u).mpr hu)]

/-- Deleting a "space" coordinate commutes with appending the last one. -/
theorem delG_snoc (m : ℕ) (k : Fin (m + 2)) (u : IC (m + 2)) (r : unitInterval) :
    delG (m + 2) (Fin.castSucc k) (Fin.snoc u r) = Fin.snoc (delG (m + 1) k u) r := by
  funext i
  cases i using Fin.lastCases with
  | last =>
    have h : (Fin.castSucc k).succAbove (Fin.last (m + 1)) = Fin.last (m + 2) := by
      apply Fin.ext
      simp only [val_succAbove, Fin.val_castSucc, Fin.val_last]
      rw [if_neg (by omega)]
    simp only [delG_apply, h, Fin.snoc_last]
  | cast j =>
    have h : (Fin.castSucc k).succAbove (Fin.castSucc j) = Fin.castSucc (k.succAbove j) := by
      apply Fin.ext
      simp only [val_succAbove, Fin.val_castSucc]
    simp only [delG_apply, h, Fin.snoc_castSucc]

theorem unpinB_agree {X : Type} [TopologicalSpace X] {x₀ : X}
    (N m : ℕ) (K : Tower x₀ N) (hN : m + 1 ≤ N)
    (τ : C(IC (m + 3), X)) (i i' : Fin (m + 3)) (b b' : Fin 2)
    (hii : i ≠ i') (z : IC (m + 3))
    (hz : z ∈ faceSet m i b) (hz' : z ∈ faceSet m i' b') (r : unitInterval) :
    PsiB N m K hN (τ.comp (faceCM i (cval b))) (unpinB m r (delG (m + 2) i z))
      = PsiB N m K hN (τ.comp (faceCM i' (cval b'))) (unpinB m r (delG (m + 2) i' z)) := by
  have hu : delG (m + 2) i z ∈ Cube.boundary (Fin (m + 2)) :=
    delG_mem_boundary_of_mem_two hz hz' hii
  have hu' : delG (m + 2) i' z ∈ Cube.boundary (Fin (m + 2)) :=
    delG_mem_boundary_of_mem_two hz' hz (Ne.symm hii)
  have hp : (unpinB m r (delG (m + 2) i z) : IC (m + 3))
      = Fin.snoc (delG (m + 2) i z) r := by
    rw [unpinB_coe]
    exact unpinPt_eq_snoc_of_mem_boundary m r hu
  have hp' : (unpinB m r (delG (m + 2) i' z) : IC (m + 3))
      = Fin.snoc (delG (m + 2) i' z) r := by
    rw [unpinB_coe]
    exact unpinPt_eq_snoc_of_mem_boundary m r hu'
  set k : Fin (m + 2) := predG i i' hii.symm with hk
  set k' : Fin (m + 2) := predG i' i hii with hk'
  have hk1 : i.succAbove k = i' := succAbove_predG i i' hii.symm
  have hk2 : i'.succAbove k' = i := succAbove_predG i' i hii
  have hzk : ((unpinB m r (delG (m + 2) i z) : IC (m + 3)) (Fin.castSucc k)) = cval b' := by
    rw [hp, Fin.snoc_castSucc, delG_apply, hk1, hz']
  have hzk' : ((unpinB m r (delG (m + 2) i' z) : IC (m + 3)) (Fin.castSucc k')) = cval b := by
    rw [hp', Fin.snoc_castSucc, delG_apply, hk2, hz]
  rw [PsiB_apply_side N m K hN _ hzk, PsiB_apply_side N m K hN _ hzk']
  have hface : (τ.comp (faceCM i (cval b))).comp (faceCM k (cval b'))
      = (τ.comp (faceCM i' (cval b'))).comp (faceCM k' (cval b)) := by
    simp only [ContinuousMap.comp_assoc]
    rw [faceCM_comp_eq_gen i i' hii (cval b) (cval b')]
  have harg : delG (m + 2) (Fin.castSucc k) (unpinB m r (delG (m + 2) i z))
      = delG (m + 2) (Fin.castSucc k') (unpinB m r (delG (m + 2) i' z)) := by
    rw [hp, hp', delG_snoc, delG_snoc]
    have hD := congrFun (congrArg (fun g : C(IC (m + 3), IC (m + 1)) => (g : IC (m + 3) → IC (m + 1)))
      (delG_comp_eq (n := m + 1) i i' hii)) z
    simp only [ContinuousMap.comp_apply] at hD
    rw [hD]
  rw [hface, harg]


/-! ## The cancellation family of the gluing -/

theorem continuous_unpinB_const (m : ℕ) (r : unitInterval) (i : Fin (m + 3)) :
    Continuous fun z : IC (m + 3) => unpinB m r (delG (m + 2) i z) :=
  Continuous.subtype_mk
    ((continuous_unpinPt m).comp ((delG (m + 2) i).continuous.prodMk continuous_const)) _

/-- The value of the cancellation family on the face `(i,b)`. -/
def glueCancelVal (N m : ℕ) (K : Tower x₀ N) (hN : m + 1 ≤ N) (τ : C(IC (m + 3), X))
    (r : unitInterval) (ib : Fin (m + 3) × Fin 2) (z : IC (m + 3)) : X :=
  PsiB N m K hN (τ.comp (faceCM ib.1 (cval ib.2))) (unpinB m r (delG (m + 2) ib.1 z))

theorem continuous_glueCancelVal (N m : ℕ) (K : Tower x₀ N) (hN : m + 1 ≤ N)
    (τ : C(IC (m + 3), X)) (r : unitInterval) (ib : Fin (m + 3) × Fin 2) :
    Continuous (glueCancelVal N m K hN τ r ib) :=
  (PsiB N m K hN _).continuous.comp (continuous_unpinB_const m r ib.1)

/-- **The cancellation family of the gluing.** -/
def glueCancel (N m : ℕ) (K : Tower x₀ N) (hN : m + 1 ≤ N) (τ : C(IC (m + 3), X))
    (r : unitInterval) : C(↥(Cube.boundary (Fin (m + 3))), X) :=
  Classical.choose (exists_cubeBoundary (m + 2)
    (fun ib : Fin (m + 3) × Fin 2 => faceSet m ib.1 ib.2)
    (fun ib => isClosed_faceSet m ib.1 ib.2)
    (fun z hz => by
      obtain ⟨i, b, hb⟩ := exists_faceSet_of_mem_boundary m hz
      exact ⟨(i, b), hb⟩)
    (fun ib => glueCancelVal N m K hN τ r ib)
    (fun ib => (continuous_glueCancelVal N m K hN τ r ib).continuousOn)
    (fun ib ib' z hz hz' => by
      rcases ib with ⟨i, b⟩
      rcases ib' with ⟨i', b'⟩
      rcases eq_or_ne i i' with h | h
      · subst h
        have hb : b = b' := by
          have hc : cval b = cval b' := by rw [← hz, hz']
          fin_cases b <;> fin_cases b' <;> simp_all [cval]
        subst hb; rfl
      · exact unpinB_agree N m K hN τ i i' b b' h z hz hz' r))

theorem glueCancel_apply_face (N m : ℕ) (K : Tower x₀ N) (hN : m + 1 ≤ N)
    (τ : C(IC (m + 3), X)) (r : unitInterval) (ib : Fin (m + 3) × Fin 2)
    (z : ↥(Cube.boundary (Fin (m + 3)))) (hz : (z : IC (m + 3)) ∈ faceSet m ib.1 ib.2) :
    glueCancel N m K hN τ r z = glueCancelVal N m K hN τ r ib z :=
  Classical.choose_spec (exists_cubeBoundary (m + 2)
    (fun ib : Fin (m + 3) × Fin 2 => faceSet m ib.1 ib.2)
    (fun ib => isClosed_faceSet m ib.1 ib.2)
    (fun z hz => by
      obtain ⟨i, b, hb⟩ := exists_faceSet_of_mem_boundary m hz
      exact ⟨(i, b), hb⟩)
    (fun ib => glueCancelVal N m K hN τ r ib)
    (fun ib => (continuous_glueCancelVal N m K hN τ r ib).continuousOn)
    (fun ib ib' z hz hz' => by
      rcases ib with ⟨i, b⟩
      rcases ib' with ⟨i', b'⟩
      rcases eq_or_ne i i' with h | h
      · subst h
        have hb : b = b' := by
          have hc : cval b = cval b' := by rw [← hz, hz']
          fin_cases b <;> fin_cases b' <;> simp_all [cval]
        subst hb; rfl
      · exact unpinB_agree N m K hN τ i i' b b' h z hz hz' r)) z ib hz

/-- At `r = 0` the cancellation family is the gluing. -/
theorem glueCancel_zero (N m : ℕ) (K : Tower x₀ N) (hN : m + 1 ≤ N)
    (τ : C(IC (m + 3), X)) :
    glueCancel N m K hN τ 0 = glue N m K hN τ := by
  ext z
  obtain ⟨i, b, hb⟩ := exists_faceSet_of_mem_boundary m z.2
  rw [glueCancel_apply_face N m K hN τ 0 (i, b) z hb,
    glue_apply_face N m K hN τ (i, b) z hb]
  exact Psi_unpinB_zero N m K hN (τ.comp (faceCM i (cval b))) (delG (m + 2) i z)

/-- The clamped map `z ↦ τ (faceCM i (cval b) (radialPt (delG i z)))` on the face `(i,b)`. -/
def clampVal (N m : ℕ) (τ : C(IC (m + 3), X)) (ib : Fin (m + 3) × Fin 2)
    (z : IC (m + 3)) : X :=
  τ (faceCM ib.1 (cval ib.2) (radialPt (m + 2) (by omega) (delG (m + 2) ib.1 z)))

theorem glueCancel_one_apply_face (N m : ℕ) (K : Tower x₀ N) (hN : m + 1 ≤ N)
    (τ : C(IC (m + 3), X)) (ib : Fin (m + 3) × Fin 2)
    (z : ↥(Cube.boundary (Fin (m + 3)))) (hz : (z : IC (m + 3)) ∈ faceSet m ib.1 ib.2) :
    glueCancel N m K hN τ 1 z = clampVal N m τ ib z :=
  (glueCancel_apply_face N m K hN τ 1 ib z hz).trans
    (PsiB_unpinB_one N m K hN (τ.comp (faceCM ib.1 (cval ib.2))) (delG (m + 2) ib.1 z))


/-! ## `τ|∂I^{m+3}` is the clamped map, and the gluing is freely null -/

/-- `radialHom` fixes the boundary pointwise. -/
theorem radialHom_eq_self_of_mem_boundary (m : ℕ) (hm : 1 ≤ m) {y : IC m}
    (hy : y ∈ Cube.boundary (Fin m)) (t : unitInterval) : radialHom m hm (y, t) = y := by
  have hself : radialPt m hm y = y :=
    radialPt_eq_self_of_sig_eq_one m hm ((sig_eq_one_iff m hm y).mpr hy)
  funext i
  apply Subtype.ext
  show (1 - (t : ℝ)) * (radialPt m hm y i : ℝ) + (t : ℝ) * (y i : ℝ) = (y i : ℝ)
  rw [hself]; ring

/-- The clamped-family value on a face. -/
def clampFamilyVal (m : ℕ) (τ : C(IC (m + 3), X)) (s : unitInterval)
    (ib : Fin (m + 3) × Fin 2) (z : IC (m + 3)) : X :=
  τ (faceCM ib.1 (cval ib.2) (radialHom (m + 2) (by omega) (delG (m + 2) ib.1 z, s)))

theorem continuous_clampFamilyVal (m : ℕ) (τ : C(IC (m + 3), X)) (s : unitInterval)
    (ib : Fin (m + 3) × Fin 2) : Continuous (clampFamilyVal m τ s ib) :=
  τ.continuous.comp ((faceCM ib.1 (cval ib.2)).continuous.comp
    ((radialHom (m + 2) (by omega)).continuous.comp
      (((delG (m + 2) ib.1).continuous).prodMk continuous_const)))

theorem clampFamilyVal_agree (m : ℕ) (τ : C(IC (m + 3), X)) (s : unitInterval)
    {ib ib' : Fin (m + 3) × Fin 2} {z : IC (m + 3)}
    (hz : z ∈ faceSet m ib.1 ib.2) (hz' : z ∈ faceSet m ib'.1 ib'.2) :
    clampFamilyVal m τ s ib z = clampFamilyVal m τ s ib' z := by
  rcases ib with ⟨i, b⟩
  rcases ib' with ⟨i', b'⟩
  rcases eq_or_ne i i' with h | h
  · subst h
    have hb : b = b' := by
      have hc : cval b = cval b' := by rw [← hz, hz']
      fin_cases b <;> fin_cases b' <;> simp_all [cval]
    subst hb; rfl
  · have hu : delG (m + 2) i z ∈ Cube.boundary (Fin (m + 2)) :=
      delG_mem_boundary_of_mem_two hz hz' h
    have hu' : delG (m + 2) i' z ∈ Cube.boundary (Fin (m + 2)) :=
      delG_mem_boundary_of_mem_two hz' hz (Ne.symm h)
    show τ (faceCM i (cval b) (radialHom (m + 2) (by omega) (delG (m + 2) i z, s)))
      = τ (faceCM i' (cval b') (radialHom (m + 2) (by omega) (delG (m + 2) i' z, s)))
    rw [radialHom_eq_self_of_mem_boundary (m + 2) (by omega) hu s,
      radialHom_eq_self_of_mem_boundary (m + 2) (by omega) hu' s,
      faceCM_delG_of_mem_faceSet hz, faceCM_delG_of_mem_faceSet hz']

/-- **The clamped family**: `glueCancel 1` deformed to `τ|∂I^{m+3}`. -/
def clampFamily (N m : ℕ) (K : Tower x₀ N) (hN : m + 1 ≤ N) (τ : C(IC (m + 3), X))
    (s : unitInterval) : C(↥(Cube.boundary (Fin (m + 3))), X) :=
  Classical.choose (exists_cubeBoundary (m + 2)
    (fun ib : Fin (m + 3) × Fin 2 => faceSet m ib.1 ib.2)
    (fun ib => isClosed_faceSet m ib.1 ib.2)
    (fun z hz => by
      obtain ⟨i, b, hb⟩ := exists_faceSet_of_mem_boundary m hz
      exact ⟨(i, b), hb⟩)
    (fun ib => clampFamilyVal m τ s ib)
    (fun ib => (continuous_clampFamilyVal m τ s ib).continuousOn)
    (fun ib ib' _ hz hz' => clampFamilyVal_agree m τ s hz hz'))

theorem clampFamily_apply_face (N m : ℕ) (K : Tower x₀ N) (hN : m + 1 ≤ N)
    (τ : C(IC (m + 3), X)) (s : unitInterval) (ib : Fin (m + 3) × Fin 2)
    (z : ↥(Cube.boundary (Fin (m + 3)))) (hz : (z : IC (m + 3)) ∈ faceSet m ib.1 ib.2) :
    clampFamily N m K hN τ s z = clampFamilyVal m τ s ib z :=
  Classical.choose_spec (exists_cubeBoundary (m + 2)
    (fun ib : Fin (m + 3) × Fin 2 => faceSet m ib.1 ib.2)
    (fun ib => isClosed_faceSet m ib.1 ib.2)
    (fun z hz => by
      obtain ⟨i, b, hb⟩ := exists_faceSet_of_mem_boundary m hz
      exact ⟨(i, b), hb⟩)
    (fun ib => clampFamilyVal m τ s ib)
    (fun ib => (continuous_clampFamilyVal m τ s ib).continuousOn)
    (fun ib ib' _ hz hz' => clampFamilyVal_agree m τ s hz hz')) z ib hz

theorem radialHome_zero (m : ℕ) (u : IC (m + 2)) :
    radialHom (m + 2) (by omega) (u, 0) = radialPt (m + 2) (by omega) u :=
  radialHom_zero (m + 2) (by omega) u

theorem radialHome_one (m : ℕ) (u : IC (m + 2)) :
    radialHom (m + 2) (by omega) (u, 1) = u :=
  radialHom_one (m + 2) (by omega) u

/-- At `s = 0` the clamped family is `glueCancel 1`. -/
theorem clampFamily_zero (N m : ℕ) (K : Tower x₀ N) (hN : m + 1 ≤ N)
    (τ : C(IC (m + 3), X)) : clampFamily N m K hN τ 0 = glueCancel N m K hN τ 1 := by
  ext z
  obtain ⟨i, b, hb⟩ := exists_faceSet_of_mem_boundary m z.2
  rw [clampFamily_apply_face N m K hN τ 0 (i, b) z hb,
    glueCancel_one_apply_face N m K hN τ (i, b) z hb]
  show τ (faceCM i (cval b) (radialHom (m + 2) (by omega) (delG (m + 2) i z, 0)))
    = τ (faceCM i (cval b) (radialPt (m + 2) (by omega) (delG (m + 2) i z)))
  rw [radialHome_zero]

/-- At `s = 1` the clamped family is `τ` on the boundary. -/
theorem clampFamily_one_apply (N m : ℕ) (K : Tower x₀ N) (hN : m + 1 ≤ N)
    (τ : C(IC (m + 3), X)) (z : ↥(Cube.boundary (Fin (m + 3)))) :
    clampFamily N m K hN τ 1 z = τ z.1 := by
  obtain ⟨i, b, hb⟩ := exists_faceSet_of_mem_boundary m z.2
  rw [clampFamily_apply_face N m K hN τ 1 (i, b) z hb]
  show τ (faceCM i (cval b) (radialHom (m + 2) (by omega) (delG (m + 2) i z, 1))) = τ z.1
  rw [radialHome_one, faceCM_delG_of_mem_faceSet hb]


/-- **The shrink family**: `τ|∂I^{m+3}` shrunk to the constant `τ 0`. -/
def shrinkFamily (N m : ℕ) (K : Tower x₀ N) (hN : m + 1 ≤ N) (τ : C(IC (m + 3), X))
    (s : unitInterval) : C(↥(Cube.boundary (Fin (m + 3))), X) where
  toFun z := τ fun k => ⟨(1 - (s : ℝ)) * ((z.1 k : unitInterval) : ℝ), by
    have h1 := (z.1 k).2.1
    have h2 := (z.1 k).2.2
    have hs0 := s.2.1
    have hs1 := s.2.2
    have : (0 : ℝ) ≤ 1 - (s : ℝ) := by linarith
    constructor
    · nlinarith
    · nlinarith⟩
  continuous_toFun := by
    apply τ.continuous.comp
    apply continuous_pi
    intro k
    apply Continuous.subtype_mk
    have hz : Continuous fun z : ↥(Cube.boundary (Fin (m + 3))) =>
        ((z.1 k : unitInterval) : ℝ) :=
      continuous_subtype_val.comp ((continuous_apply k).comp continuous_subtype_val)
    fun_prop

theorem shrinkFamily_zero (N m : ℕ) (K : Tower x₀ N) (hN : m + 1 ≤ N)
    (τ : C(IC (m + 3), X)) :
    shrinkFamily N m K hN τ 0 = clampFamily N m K hN τ 1 := by
  ext z
  rw [clampFamily_one_apply N m K hN τ z]
  show τ (fun k => (⟨(1 - ((0 : unitInterval) : ℝ)) * ((z.1 k : unitInterval) : ℝ), _⟩ :
      unitInterval)) = τ z.1
  congr 1
  funext k
  apply Subtype.ext
  simp

theorem shrinkFamily_one (N m : ℕ) (K : Tower x₀ N) (hN : m + 1 ≤ N)
    (τ : C(IC (m + 3), X)) :
    shrinkFamily N m K hN τ 1 = ContinuousMap.const _ (τ 0) := by
  ext z
  show τ (fun k => (⟨(1 - ((1 : unitInterval) : ℝ)) * ((z.1 k : unitInterval) : ℝ), _⟩ :
      unitInterval)) = τ 0
  congr 1
  funext k
  apply Subtype.ext
  simp

/-! ## The gluing at the origin -/

theorem zero_mem_boundary (m : ℕ) : (0 : IC (m + 3)) ∈ Cube.boundary (Fin (m + 3)) := by
  refine ⟨0, Or.inl ?_⟩
  rfl

theorem zero_mem_boundary_two (m : ℕ) : (0 : IC (m + 2)) ∈ Cube.boundary (Fin (m + 2)) :=
  ⟨0, Or.inl rfl⟩

/-- **The gluing is `x₀` at the origin** (the origin lies on two distinct faces). -/
theorem glue_zero (N m : ℕ) (K : Tower x₀ N) (hN : m + 1 ≤ N) (τ : C(IC (m + 3), X)) :
    glue N m K hN τ ⟨0, zero_mem_boundary m⟩ = x₀ := by
  have h0 : ((0 : IC (m + 3)) : IC (m + 3)) (0 : Fin (m + 3)) = cval (0 : Fin 2) := by
    show (0 : unitInterval) = cval (0 : Fin 2); rw [cval_zero]
  have h1 : ((0 : IC (m + 3)) : IC (m + 3)) (1 : Fin (m + 3)) = cval (0 : Fin 2) := by
    show (0 : unitInterval) = cval (0 : Fin 2); rw [cval_zero]
  exact glue_eq_x₀_of_mem_two N m K hN τ ⟨0, zero_mem_boundary m⟩
    (i := (0 : Fin (m + 3))) (i' := (1 : Fin (m + 3)))
    (b := (0 : Fin 2)) (b' := (0 : Fin 2)) h0 h1 zero_ne_one

/-! ## The based class of the gluing model is trivial -/

/-- **The cancellation, in class form.**  If the gluing admits a free homotopy to a constant (with
arbitrary value `z`), then for any collapse `φ` onto a point where the gluing is `x₀` the based cube
`glue ∘ φ` has trivial class. -/
theorem cl_comp_collapse (N m : ℕ) (K : Tower x₀ N) (hN : m + 1 ≤ N)
    (τ : C(IC (m + 3), X)) (H : C(↥(Cube.boundary (Fin (m + 3))) × unitInterval, X)) (z : X)
    (hH0 : ∀ p, H (p, 0) = glue N m K hN τ p) (hH1 : ∀ p, H (p, 1) = z)
    (φ : C(IC (m + 2), ↥(Cube.boundary (Fin (m + 3)))))
    (hφ : ∀ u ∈ Cube.boundary (Fin (m + 2)), φ u = φ 0)
    (hv : glue N m K hN τ (φ 0) = x₀) :
    cl (m + 2) X x₀
      ⟨(glue N m K hN τ).comp φ, fun u hu => by
        rw [ContinuousMap.comp_apply, hφ u hu, hv]⟩ = 1 := by
  haveI : NeZero (m + 2) := ⟨by omega⟩
  rw [cl, HomotopyGroup.one_def]
  refine Quotient.sound (Work.Stems.Hur2b.homotopic_const_of_boundary_const (m + 2)
    (x₀ := x₀) ⟨(glue N m K hN τ).comp φ, fun u hu => by
      rw [ContinuousMap.comp_apply, hφ u hu, hv]⟩ z
    ⟨fun p => H (φ p.1, p.2), by fun_prop⟩ ?_ ?_ ?_)
  · intro u
    show H (φ u, 0) = (glue N m K hN τ) (φ u)
    rw [hH0]
  · intro u
    show H (φ u, 1) = z
    rw [hH1]
  · intro u u' r hu hu'
    show H (φ u, r) = H (φ u', r)
    rw [hφ u hu, hφ u' hu']

end

end Work.RatHurewicz
