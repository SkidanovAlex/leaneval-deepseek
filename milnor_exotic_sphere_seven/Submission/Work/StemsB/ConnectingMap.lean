import Mathlib
import Submission.Work.StemsB.LESHelpers
import Submission.Work.StemsB.PiMap

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

/-!
# The connecting map `π_{k+2}(B) → π_{k+1}(F)`

Given `p : E → B` with the relative homotopy lifting property, we construct the connecting map of
the long exact homotopy sequence of `p`, and prove that it is well defined on homotopy classes and
is a group homomorphism.
-/

open scoped Topology Topology.Homotopy unitInterval

namespace Work.StemsB

noncomputable section

open Classical

variable {E B : Type*} [TopologicalSpace E] [TopologicalSpace B]

/-! ## Reindexing a based cube -/

/-- The cube `(x, t) ↦ f (Fin.cons t x)` associated with a based `(k+2)`-cube `f`.  Splitting off
the first coordinate turns the relative lifting property into the connecting map. -/
def cubeReindex {p : C(E, B)} {e₀ : E} {k : ℕ}
    (f : GenLoop (Fin (k+2)) B (p e₀)) : C((Fin (k+1) → I) × I, B) :=
  ⟨fun q => f (Fin.cons q.2 q.1), f.1.continuous.comp (consCM (k+1)).continuous⟩

@[simp] theorem cubeReindex_apply {p : C(E, B)} {e₀ : E} {k : ℕ}
    (f : GenLoop (Fin (k+2)) B (p e₀)) (q : (Fin (k+1) → I) × I) :
    cubeReindex f q = f (Fin.cons q.2 q.1) := rfl

theorem cubeReindex_zero {p : C(E, B)} {e₀ : E} {k : ℕ}
    (f : GenLoop (Fin (k+2)) B (p e₀)) (x : Fin (k+1) → I) :
    cubeReindex f (x, 0) = p e₀ :=
  f.2 _ (cons_zero_mem_boundary x)

theorem cubeReindex_one {p : C(E, B)} {e₀ : E} {k : ℕ}
    (f : GenLoop (Fin (k+2)) B (p e₀)) (x : Fin (k+1) → I) :
    cubeReindex f (x, 1) = p e₀ :=
  f.2 _ (cons_one_mem_boundary x)

theorem cubeReindex_bd {p : C(E, B)} {e₀ : E} {k : ℕ}
    (f : GenLoop (Fin (k+2)) B (p e₀)) (x : CubeBdry (k+1)) (t : I) :
    cubeReindex f (x.1, t) = p e₀ :=
  f.2 _ (cons_mem_boundary x.2)

/-! ## The chosen lift -/

section Lift

variable (p : C(E, B)) (e₀ : E)

/-- The relative lifting property applied to the cube of a based cube: there is a lift which is
constantly `e₀` on the bottom face and on the lateral boundary. -/
theorem exists_dLift (hrel : ∀ k, HasHLPRel p k) {k : ℕ}
    (f : GenLoop (Fin (k+2)) B (p e₀)) :
    ∃ G : C((Fin (k+1) → I) × I, E),
      p.comp G = cubeReindex f ∧
      (∀ x : Fin (k+1) → I, G (x, 0) = e₀) ∧
      (∀ (x : CubeBdry (k+1)) (t : I), G (x.1, t) = e₀) := by
  have hf : p.comp (ContinuousMap.const (Fin (k+1) → I) e₀) =
      (cubeReindex f).comp (zeroIncl (k+1)) := by
    ext x
    show p e₀ = cubeReindex f (x, 0)
    exact (cubeReindex_zero f x).symm
  have hg : p.comp (ContinuousMap.const (CubeBdry (k+1) × I) e₀) =
      (cubeReindex f).comp (bdryIncl (k+1)) := by
    ext q
    show p e₀ = cubeReindex f (q.1.1, q.2)
    exact (cubeReindex_bd f q.1 q.2).symm
  have hg0 : ∀ (x : CubeBdry (k+1)),
      (ContinuousMap.const (CubeBdry (k+1) × I) e₀) (x, 0)
        = (ContinuousMap.const (Fin (k+1) → I) e₀) x.1 := fun x => rfl
  exact hrel (k+1) (cubeReindex f) (ContinuousMap.const (Fin (k+1) → I) e₀) hf
    (ContinuousMap.const (CubeBdry (k+1) × I) e₀) hg hg0

/-- A chosen lift of the cube of a based cube. -/
noncomputable def dLift (hrel : ∀ k, HasHLPRel p k) {k : ℕ}
    (f : GenLoop (Fin (k+2)) B (p e₀)) : C((Fin (k+1) → I) × I, E) :=
  Classical.choose (exists_dLift p e₀ hrel f)

theorem dLift_spec (hrel : ∀ k, HasHLPRel p k) {k : ℕ}
    (f : GenLoop (Fin (k+2)) B (p e₀)) :
    p.comp (dLift p e₀ hrel f) = cubeReindex f ∧
    (∀ x : Fin (k+1) → I, dLift p e₀ hrel f (x, 0) = e₀) ∧
    (∀ (x : CubeBdry (k+1)) (t : I), dLift p e₀ hrel f (x.1, t) = e₀) :=
  Classical.choose_spec (exists_dLift p e₀ hrel f)

/-- **The connecting map on representatives**: the top face of the chosen lift. -/
noncomputable def dGenLoop (hrel : ∀ k, HasHLPRel p k) {k : ℕ}
    (f : GenLoop (Fin (k+2)) B (p e₀)) :
    GenLoop (Fin (k+1)) (fibre p (p e₀)) (fibrePoint p e₀) :=
  topFaceG (k+1) (cubeReindex f) (cubeReindex_one f) (dLift p e₀ hrel f)
    (dLift_spec p e₀ hrel f).1 (dLift_spec p e₀ hrel f).2.2

theorem dGenLoop_coe (hrel : ∀ k, HasHLPRel p k) {k : ℕ}
    (f : GenLoop (Fin (k+2)) B (p e₀)) :
    (dGenLoop p e₀ hrel f).1 = topFace (k+1) (cubeReindex f) (cubeReindex_one f)
      (dLift p e₀ hrel f) (dLift_spec p e₀ hrel f).1 := rfl

@[simp] theorem dGenLoop_apply_coe (hrel : ∀ k, HasHLPRel p k) {k : ℕ}
    (f : GenLoop (Fin (k+2)) B (p e₀)) (x : Fin (k+1) → I) :
    ((dGenLoop p e₀ hrel f) x).1 = dLift p e₀ hrel f (x, 1) := rfl

/-- The canonical top face of a lift has the expected values. -/
theorem topFaceG_apply_coe {p' : C(E, B)} {e : E} {k : ℕ}
    (H : C((Fin k → I) × I, B)) (hH1 : ∀ x : Fin k → I, H (x, 1) = p' e)
    (G : C((Fin k → I) × I, E)) (hG : p'.comp G = H)
    (hGbd : ∀ (x : CubeBdry k) (t : I), G (x.1, t) = e)
    (x : Fin k → I) : ((topFaceG k H hH1 G hG hGbd) x).1 = G (x, 1) := rfl

end Lift

/-! ## Homotopy invariance of the lift -/

section LiftHomotopy

variable (p : C(E, B)) (e₀ : E)

/-- **Homotopy invariance of the lift.**  If `f, f'` are homotopic based cubes and `G, G'` are
lifts of their cubes which are constantly `e₀` on the bottom face and the lateral boundary, then
the top faces are homotopic relative to the boundary.  The proof is one application of the relative
lifting property, interpolating between `G` and `G'` in a new cube coordinate `s`. -/
theorem liftHomotopy (hrel : ∀ k, HasHLPRel p k) {k : ℕ}
    (f f' : GenLoop (Fin (k+2)) B (p e₀))
    (Φ : ContinuousMap.HomotopyRel f.1 f'.1 (Cube.boundary (Fin (k+2))))
    (G G' : C((Fin (k+1) → I) × I, E))
    (hG : p.comp G = cubeReindex f) (hG' : p.comp G' = cubeReindex f')
    (hG0 : ∀ x : Fin (k+1) → I, G (x, 0) = e₀) (hG'0 : ∀ x : Fin (k+1) → I, G' (x, 0) = e₀)
    (hGbd : ∀ (x : CubeBdry (k+1)) (t : I), G (x.1, t) = e₀)
    (hG'bd : ∀ (x : CubeBdry (k+1)) (t : I), G' (x.1, t) = e₀) :
    GenLoop.Homotopic
      (topFaceG (k+1) (cubeReindex f) (cubeReindex_one f) G hG hGbd)
      (topFaceG (k+1) (cubeReindex f') (cubeReindex_one f') G' hG' hG'bd) := by
  have hGp : ∀ q, p (G q) = cubeReindex f q := fun q => ContinuousMap.congr_fun hG q
  have hG'p : ∀ q, p (G' q) = cubeReindex f' q := fun q => ContinuousMap.congr_fun hG' q
  have hΦ0 : ∀ u : Fin (k+2) → I, Φ (0, u) = f.1 u := fun u => Φ.map_zero_left u
  have hΦ1 : ∀ u : Fin (k+2) → I, Φ (1, u) = f'.1 u := fun u => Φ.map_one_left u
  have hΦbd : ∀ (u : Fin (k+2) → I), u ∈ Cube.boundary (Fin (k+2)) → ∀ s : I, Φ (s, u) = p e₀ :=
    fun u hu s => (Φ.eq_fst s hu).trans (f.2 u hu)
  have hnorm0 : ((0:I) : ℝ) ≤ 1/2 := by norm_num
  have hnorm1 : ¬ (((1:I) : ℝ) ≤ 1/2) := by norm_num
  -- the ambient cube map
  let Hhas : C((Fin (k+2) → I) × I, B) :=
    ⟨fun q => Φ (q.1 0, Fin.cons q.2 (Fin.tail q.1)), by
      have h0 : Continuous fun q : (Fin (k+2) → I) × I => q.1 0 :=
        (continuous_apply 0).comp continuous_fst
      have h1 : Continuous fun q : (Fin (k+2) → I) × I => (Fin.tail q.1, q.2) :=
        ((continuous_finTail (k+1)).comp continuous_fst).prodMk continuous_snd
      exact Φ.continuous.comp (h0.prodMk ((consCM (k+1)).continuous.comp h1))⟩
  have hHhas : ∀ (w : Fin (k+2) → I) (u : I),
      Hhas (w, u) = Φ (w 0, Fin.cons u (Fin.tail w)) := fun w u => rfl
  -- the lateral lift
  let ghas : C(CubeBdry (k+2) × I, E) :=
    ⟨fun q => if (q.1.1 0 : ℝ) ≤ 1/2 then G (Fin.tail q.1.1, q.2)
      else G' (Fin.tail q.1.1, q.2), by
      have hcoord : Continuous fun q : CubeBdry (k+2) × I => (q.1.1 0 : ℝ) :=
        continuous_subtype_val.comp ((continuous_apply 0).comp
          (continuous_subtype_val.comp continuous_fst))
      have htail : Continuous fun q : CubeBdry (k+2) × I => Fin.tail q.1.1 :=
        (continuous_finTail (k+1)).comp (continuous_subtype_val.comp continuous_fst)
      have hpair : Continuous fun q : CubeBdry (k+2) × I => (Fin.tail q.1.1, q.2) :=
        htail.prodMk continuous_snd
      apply Continuous.if
      · intro q hq
        have hclosed : IsClosed {q : CubeBdry (k+2) × I | (q.1.1 0 : ℝ) ≤ 1/2} :=
          isClosed_Iic.preimage hcoord
        have hqle : (q.1.1 0 : ℝ) ≤ 1/2 := by
          have h1 : q ∈ closure {q : CubeBdry (k+2) × I | (q.1.1 0 : ℝ) ≤ 1/2} := hq.1
          rwa [hclosed.closure_eq] at h1
        have hqe : (q.1.1 0 : ℝ) = 1/2 := by
          refine le_antisymm hqle ?_
          by_contra hlt
          have hlt' : (q.1.1 0 : ℝ) < 1/2 := lt_of_not_ge hlt
          have : q ∈ interior {q : CubeBdry (k+2) × I | (q.1.1 0 : ℝ) ≤ 1/2} := by
            apply mem_interior_iff_mem_nhds.mpr
            have hop : IsOpen {q : CubeBdry (k+2) × I | (q.1.1 0 : ℝ) < 1/2} :=
              isOpen_lt hcoord continuous_const
            refine Filter.mem_of_superset (hop.mem_nhds hlt') ?_
            intro y hy
            exact le_of_lt (show (y.1.1 0 : ℝ) < 1/2 from hy)
          exact hq.2 this
        have hb : Fin.tail q.1.1 ∈ Cube.boundary (Fin (k+1)) := by
          refine tail_mem_boundary_of_cons q.1.2 ?_ ?_
          · intro h; rw [h] at hqe; norm_num at hqe
          · intro h; rw [h] at hqe; norm_num at hqe
        rw [hGbd ⟨_, hb⟩ q.2, hG'bd ⟨_, hb⟩ q.2]
      · exact G.continuous.comp hpair
      · exact G'.continuous.comp hpair⟩
  have hghas : ∀ (w : CubeBdry (k+2)) (u : I),
      ghas (w, u) = if (w.1 0 : ℝ) ≤ 1/2 then G (Fin.tail w.1, u)
        else G' (Fin.tail w.1, u) := fun w u => rfl
  -- lifting data
  have hf : p.comp (ContinuousMap.const (Fin (k+2) → I) e₀) = Hhas.comp (zeroIncl (k+2)) := by
    ext w
    show p e₀ = Hhas (w, 0)
    rw [hHhas]
    exact (hΦbd _ (cons_zero_mem_boundary (Fin.tail w)) (w 0)).symm
  have hg : p.comp ghas = Hhas.comp (bdryIncl (k+2)) := by
    ext q
    show p (ghas q) = Hhas (q.1.1, q.2)
    rw [hghas q.1 q.2, hHhas]
    by_cases h : (q.1.1 0 : ℝ) ≤ 1/2
    · rw [if_pos h, hGp]
      rw [cubeReindex_apply]
      by_cases h0 : q.1.1 0 = 0
      · rw [h0]; exact (hΦ0 _).symm
      · have hb : Fin.tail q.1.1 ∈ Cube.boundary (Fin (k+1)) := by
          refine tail_mem_boundary_of_cons q.1.2 h0 ?_
          intro h1; rw [h1] at h; norm_num at h
        rw [hΦbd _ (cons_mem_boundary hb) _]
        exact f.2 _ (cons_mem_boundary hb)
    · rw [if_neg h, hG'p]
      rw [cubeReindex_apply]
      by_cases h1 : q.1.1 0 = 1
      · rw [h1]; exact (hΦ1 _).symm
      · have h0 : q.1.1 0 ≠ 0 := by intro h0; rw [h0] at h; norm_num at h
        have hb : Fin.tail q.1.1 ∈ Cube.boundary (Fin (k+1)) :=
          tail_mem_boundary_of_cons q.1.2 h0 h1
        rw [hΦbd _ (cons_mem_boundary hb) _]
        exact f'.2 _ (cons_mem_boundary hb)
  have hg0 : ∀ (x : CubeBdry (k+2)),
      ghas (x, 0) = (ContinuousMap.const (Fin (k+2) → I) e₀) x.1 := by
    intro x
    rw [hghas x 0]
    by_cases h : (x.1 0 : ℝ) ≤ 1/2
    · rw [if_pos h]; exact hG0 _
    · rw [if_neg h]; exact hG'0 _
  obtain ⟨Ψ, hΨp, hΨ0, hΨbd⟩ :=
    hrel (k+2) Hhas (ContinuousMap.const (Fin (k+2) → I) e₀) hf ghas hg hg0
  have hΨp' : ∀ q, p (Ψ q) = Hhas q := fun q => ContinuousMap.congr_fun hΨp q
  -- the interpolating homotopy
  have hΛ_cont : Continuous fun q : (Fin (k+1) → I) × I => Ψ (consCM (k+1) q, 1) :=
    Ψ.continuous.comp ((consCM (k+1)).continuous.prodMk continuous_const)
  let Λ : C((Fin (k+1) → I) × I, E) := ⟨fun q => Ψ (consCM (k+1) q, 1), hΛ_cont⟩
  have hΛ : ∀ q : (Fin (k+1) → I) × I, Λ q = Ψ (Fin.cons q.2 q.1, 1) := fun q => rfl
  have hΛmem : ∀ q : (Fin (k+1) → I) × I, p (Λ q) = p e₀ := by
    intro q
    rw [hΛ, hΨp']
    rw [hHhas, Fin.cons_zero, Fin.tail_cons]
    exact hΦbd _ (cons_one_mem_boundary q.1) q.2
  refine ⟨ContinuousMap.HomotopyWith.mk
    (ContinuousMap.Homotopy.mk ⟨fun s => ⟨Λ (s.2, s.1), hΛmem (s.2, s.1)⟩, ?_⟩ ?_ ?_) ?_⟩
  · exact Continuous.subtype_mk (hΛ_cont.comp (continuous_snd.prodMk continuous_fst)) _
  · -- zero
    intro x
    apply Subtype.ext
    have hmem : Fin.cons (0:I) x ∈ Cube.boundary (Fin (k+2)) := cons_zero_mem_boundary x
    show Λ (x, 0) = G (x, 1)
    rw [hΛ, hΨbd ⟨Fin.cons (0:I) x, hmem⟩ 1, hghas ⟨Fin.cons (0:I) x, hmem⟩ 1]
    simp only [Fin.cons_zero, Fin.tail_cons]
    rw [if_pos hnorm0]
  · -- one
    intro x
    apply Subtype.ext
    have hmem : Fin.cons (1:I) x ∈ Cube.boundary (Fin (k+2)) := cons_one_mem_boundary x
    show Λ (x, 1) = G' (x, 1)
    rw [hΛ, hΨbd ⟨Fin.cons (1:I) x, hmem⟩ 1, hghas ⟨Fin.cons (1:I) x, hmem⟩ 1]
    simp only [Fin.cons_zero, Fin.tail_cons]
    rw [if_neg hnorm1]
  · -- boundary
    intro t x hx
    apply Subtype.ext
    have hmem : Fin.cons t x ∈ Cube.boundary (Fin (k+2)) := cons_mem_boundary hx
    show Λ (x, t) = G (x, 1)
    rw [hΛ, hΨbd ⟨Fin.cons t x, hmem⟩ 1, hghas ⟨Fin.cons t x, hmem⟩ 1]
    simp only [Fin.cons_zero, Fin.tail_cons]
    by_cases h : (t : ℝ) ≤ 1/2
    · rw [if_pos h, hGbd ⟨x, hx⟩ 1]
    · rw [if_neg h, hG'bd ⟨x, hx⟩ 1, hGbd ⟨x, hx⟩ 1]

end LiftHomotopy

/-! ## Tools for the concatenation `GenLoop.transAt` -/

namespace GenLoop

theorem transAt_apply {N : Type*} [DecidableEq N] {X : Type*} [TopologicalSpace X] {x : X}
    (i : N) (f g : Ω^ N X x) (u : N → I) :
    (GenLoop.transAt i f g) u =
      (if (u i : ℝ) ≤ 1/2
        then f (Function.update u i (Set.projIcc 0 1 zero_le_one (2 * (u i : ℝ))))
        else g (Function.update u i (Set.projIcc 0 1 zero_le_one (2 * (u i : ℝ) - 1)))) := by
  rw [GenLoop.transAt, GenLoop.coe_copy]

end GenLoop

theorem projIcc_zero' : Set.projIcc (0:ℝ) 1 zero_le_one (0:ℝ) = 0 := by
  rw [Set.projIcc_left]; exact Subtype.ext rfl

theorem projIcc_one' : Set.projIcc (0:ℝ) 1 zero_le_one (1:ℝ) = 1 := by
  rw [Set.projIcc_right]; exact Subtype.ext rfl

theorem projIcc_two' : Set.projIcc (0:ℝ) 1 zero_le_one (2:ℝ) = 1 := by
  apply Subtype.ext; rw [Set.coe_projIcc]; norm_num

theorem projIcc_of_le_zero {c : ℝ} (hc : c ≤ 0) : Set.projIcc (0:ℝ) 1 zero_le_one c = 0 := by
  rw [Set.projIcc_of_le_left (a := 0) (b := 1) (h := zero_le_one) (x := c) hc]
  exact Subtype.ext rfl

/-- Updating a coordinate of a cube with a continuously varying value. -/
def updateCM {n : ℕ} (j : Fin n) (φ : C(Fin n → I, I)) : C(Fin n → I, Fin n → I) where
  toFun x := Function.update x j (φ x)
  continuous_toFun := by
    apply continuous_pi
    intro l
    rw [show (fun x : Fin n → I => Function.update x j (φ x) l)
        = fun x => if l = j then φ x else x l from
      funext fun x => Function.update_apply x j (φ x) l]
    exact Continuous.if_const (l = j) φ.continuous (continuous_apply l)

@[simp] theorem updateCM_apply {n : ℕ} (j : Fin n) (φ : C(Fin n → I, I)) (x : Fin n → I) :
    updateCM j φ x = Function.update x j (φ x) := rfl

theorem update_cons_succ {n : ℕ} (t : I) (x : Fin n → I) (j : Fin n) (w : I) :
    Function.update (Fin.cons t x : Fin (n+1) → I) (Fin.succ j) w
      = Fin.cons t (Function.update x j w : Fin n → I) := by
  funext l
  cases l using Fin.cases with
  | zero =>
    rw [Function.update_of_ne (Fin.succ_ne_zero j).symm w (Fin.cons t x : Fin (n+1) → I)]
    simp [Fin.cons_zero]
  | succ m =>
    simp only [Function.update_apply, Fin.cons_succ]
    by_cases h : m = j
    · rw [if_pos (by rw [h] : Fin.succ m = Fin.succ j), if_pos h]
    · rw [if_neg (fun hh => h (Fin.succ_inj.mp hh)), if_neg h]

/-! ## The connecting map is a homomorphism -/

section Hom

variable (p : C(E, B)) (e₀ : E)

/-- **The connecting map is compatible with concatenation.**  Concatenating two based cubes along
the `(j+1)`-st coordinate and then applying the connecting map gives the concatenation of the two
connecting-map values along the `j`-th coordinate. -/
theorem dGenLoop_transAt (hrel : ∀ k, HasHLPRel p k) {k : ℕ} (j : Fin (k+1))
    (f f' : GenLoop (Fin (k+2)) B (p e₀)) :
    GenLoop.Homotopic (dGenLoop p e₀ hrel (GenLoop.transAt (Fin.succ j) f' f))
      (GenLoop.transAt j (dGenLoop p e₀ hrel f') (dGenLoop p e₀ hrel f)) := by
  have hnorm1 : ¬ (((1:I):ℝ) ≤ 1/2) := by norm_num
  let p1 : C(Fin (k+1) → I, I) :=
    ⟨fun x => Set.projIcc 0 1 zero_le_one (2 * (x j : ℝ)),
      continuous_projIcc.comp
        (continuous_const.mul (continuous_subtype_val.comp (continuous_apply j)))⟩
  let p2 : C(Fin (k+1) → I, I) :=
    ⟨fun x => Set.projIcc 0 1 zero_le_one (2 * (x j : ℝ) - 1),
      continuous_projIcc.comp
        ((continuous_const.mul (continuous_subtype_val.comp (continuous_apply j))).sub
          continuous_const)⟩
  have hp1 : ∀ x, p1 x = Set.projIcc 0 1 zero_le_one (2 * (x j : ℝ)) := fun x => rfl
  have hp2 : ∀ x, p2 x = Set.projIcc 0 1 zero_le_one (2 * (x j : ℝ) - 1) := fun x => rfl
  -- continuity of the interpolating lift
  have hcoord : Continuous fun q : (Fin (k+1) → I) × I => (q.1 j : ℝ) :=
    continuous_subtype_val.comp ((continuous_apply j).comp continuous_fst)
  have hGt_cont : Continuous fun q : (Fin (k+1) → I) × I =>
      if (q.1 j : ℝ) ≤ 1/2 then dLift p e₀ hrel f' (updateCM j p1 q.1, q.2)
        else dLift p e₀ hrel f (updateCM j p2 q.1, q.2) := by
    apply Continuous.if
    · intro q hq
      have hclosed : IsClosed {q : (Fin (k+1) → I) × I | (q.1 j : ℝ) ≤ 1/2} :=
        isClosed_Iic.preimage hcoord
      have hqle : (q.1 j : ℝ) ≤ 1/2 := by
        have h1 : q ∈ closure {q : (Fin (k+1) → I) × I | (q.1 j : ℝ) ≤ 1/2} := hq.1
        rwa [hclosed.closure_eq] at h1
      have hqe : (q.1 j : ℝ) = 1/2 := by
        refine le_antisymm hqle ?_
        by_contra hlt
        have hlt' : (q.1 j : ℝ) < 1/2 := lt_of_not_ge hlt
        have : q ∈ interior {q : (Fin (k+1) → I) × I | (q.1 j : ℝ) ≤ 1/2} := by
          apply mem_interior_iff_mem_nhds.mpr
          have hop : IsOpen {q : (Fin (k+1) → I) × I | (q.1 j : ℝ) < 1/2} :=
            isOpen_lt hcoord continuous_const
          exact Filter.mem_of_superset (hop.mem_nhds hlt')
            (fun y hy => le_of_lt (show (y.1 j : ℝ) < 1/2 from hy))
        exact hq.2 this
      have htwo : (2:ℝ) * (1/2) = 1 := by norm_num
      have h1v : (updateCM j p1 q.1) j = 1 := by
        rw [updateCM_apply, Function.update_apply, if_pos rfl, hp1, hqe, htwo, projIcc_one']
      have h2v : (updateCM j p2 q.1) j = 0 := by
        rw [updateCM_apply, Function.update_apply, if_pos rfl, hp2, hqe, htwo,
          show (1:ℝ) - 1 = 0 by norm_num, projIcc_zero']
      rw [(dLift_spec p e₀ hrel f').2.2 ⟨_, ⟨j, Or.inr h1v⟩⟩ q.2,
        (dLift_spec p e₀ hrel f).2.2 ⟨_, ⟨j, Or.inl h2v⟩⟩ q.2]
    · exact (dLift p e₀ hrel f').continuous.comp
        (((updateCM j p1).continuous.comp continuous_fst).prodMk continuous_snd)
    · exact (dLift p e₀ hrel f).continuous.comp
        (((updateCM j p2).continuous.comp continuous_fst).prodMk continuous_snd)
  let Gt : C((Fin (k+1) → I) × I, E) :=
    ⟨fun q => if (q.1 j : ℝ) ≤ 1/2 then dLift p e₀ hrel f' (updateCM j p1 q.1, q.2)
      else dLift p e₀ hrel f (updateCM j p2 q.1, q.2), hGt_cont⟩
  have hGt : ∀ q, Gt q = if (q.1 j : ℝ) ≤ 1/2 then dLift p e₀ hrel f' (updateCM j p1 q.1, q.2)
      else dLift p e₀ hrel f (updateCM j p2 q.1, q.2) := fun q => rfl
  -- the cube it lifts
  have hcr : ∀ q : (Fin (k+1) → I) × I,
      cubeReindex (GenLoop.transAt (Fin.succ j) f' f) q
        = (if (q.1 j : ℝ) ≤ 1/2
          then f' (Fin.cons q.2 (Function.update q.1 j (Set.projIcc 0 1 zero_le_one (2 * (q.1 j : ℝ)))))
          else f (Fin.cons q.2 (Function.update q.1 j (Set.projIcc 0 1 zero_le_one (2 * (q.1 j : ℝ) - 1))))) := by
    intro q
    rw [cubeReindex_apply, GenLoop.transAt_apply, Fin.cons_succ, update_cons_succ, update_cons_succ]
  have hmem1 : ∀ x : CubeBdry (k+1), updateCM j p1 x.1 ∈ Cube.boundary (Fin (k+1)) := by
    intro x
    obtain ⟨l, hl⟩ := x.2
    by_cases hlj : l = j
    · subst hlj
      rcases hl with h0 | h1
      · refine ⟨l, Or.inl ?_⟩
        rw [updateCM_apply, Function.update_apply, if_pos rfl, hp1]
        have hc : (x.1 l : ℝ) = 0 := by rw [h0]; rfl
        rw [hc, show (2:ℝ) * 0 = 0 by norm_num, projIcc_zero']
      · refine ⟨l, Or.inr ?_⟩
        rw [updateCM_apply, Function.update_apply, if_pos rfl, hp1]
        have hc : (x.1 l : ℝ) = 1 := by rw [h1]; rfl
        rw [hc, show (2:ℝ) * 1 = 2 by norm_num, projIcc_two']
    · refine ⟨l, ?_⟩
      rw [updateCM_apply, Function.update_of_ne hlj]
      exact hl
  have hmem2 : ∀ x : CubeBdry (k+1), updateCM j p2 x.1 ∈ Cube.boundary (Fin (k+1)) := by
    intro x
    obtain ⟨l, hl⟩ := x.2
    by_cases hlj : l = j
    · subst hlj
      rcases hl with h0 | h1
      · refine ⟨l, Or.inl ?_⟩
        rw [updateCM_apply, Function.update_apply, if_pos rfl, hp2]
        have hc : (x.1 l : ℝ) = 0 := by rw [h0]; rfl
        rw [hc, show (2:ℝ) * 0 - 1 = -1 by norm_num, projIcc_of_le_zero (by norm_num)]
      · refine ⟨l, Or.inr ?_⟩
        rw [updateCM_apply, Function.update_apply, if_pos rfl, hp2]
        have hc : (x.1 l : ℝ) = 1 := by rw [h1]; rfl
        rw [hc, show (2:ℝ) * 1 - 1 = 1 by norm_num, projIcc_one']
    · refine ⟨l, ?_⟩
      rw [updateCM_apply, Function.update_of_ne hlj]
      exact hl
  have hG'p' : ∀ q : (Fin (k+1) → I) × I, p (dLift p e₀ hrel f' q) = cubeReindex f' q :=
    fun q => ContinuousMap.congr_fun (dLift_spec p e₀ hrel f').1 q
  have hGp' : ∀ q : (Fin (k+1) → I) × I, p (dLift p e₀ hrel f q) = cubeReindex f q :=
    fun q => ContinuousMap.congr_fun (dLift_spec p e₀ hrel f).1 q
  have hGt_lift : p.comp Gt = cubeReindex (GenLoop.transAt (Fin.succ j) f' f) := by
    ext q
    show p (Gt q) = cubeReindex (GenLoop.transAt (Fin.succ j) f' f) q
    rw [hGt q, hcr q]
    by_cases h : (q.1 j : ℝ) ≤ 1/2
    · rw [if_pos h, if_pos h, hG'p', cubeReindex_apply, updateCM_apply, hp1]
    · rw [if_neg h, if_neg h, hGp', cubeReindex_apply, updateCM_apply, hp2]
  have hGt0 : ∀ x : Fin (k+1) → I, Gt (x, 0) = e₀ := by
    intro x
    rw [hGt]
    by_cases h : (x j : ℝ) ≤ 1/2
    · rw [if_pos h]; exact (dLift_spec p e₀ hrel f').2.1 _
    · rw [if_neg h]; exact (dLift_spec p e₀ hrel f).2.1 _
  have hGtbd : ∀ (x : CubeBdry (k+1)) (t : I), Gt (x.1, t) = e₀ := by
    intro x t
    rw [hGt]
    by_cases h : (x.1 j : ℝ) ≤ 1/2
    · rw [if_pos h]; exact (dLift_spec p e₀ hrel f').2.2 ⟨_, hmem1 x⟩ t
    · rw [if_neg h]; exact (dLift_spec p e₀ hrel f).2.2 ⟨_, hmem2 x⟩ t
  -- the top face of `Gt` is the concatenation
  have hTop : topFaceG (k+1) (cubeReindex (GenLoop.transAt (Fin.succ j) f' f))
      (cubeReindex_one _) Gt hGt_lift hGtbd
      = GenLoop.transAt j (dGenLoop p e₀ hrel f') (dGenLoop p e₀ hrel f) := by
    apply GenLoop.ext
    intro x
    apply Subtype.ext
    show Gt (x, 1) = ((GenLoop.transAt j (dGenLoop p e₀ hrel f') (dGenLoop p e₀ hrel f)) x).1
    rw [GenLoop.transAt_apply]
    by_cases h : (x j : ℝ) ≤ 1/2
    · rw [if_pos h]
      show Gt (x, 1) = ((dGenLoop p e₀ hrel f')
        (Function.update x j (Set.projIcc 0 1 zero_le_one (2 * (x j : ℝ))))).1
      rw [hGt, if_pos h, dGenLoop_apply_coe]
      rfl
    · rw [if_neg h]
      show Gt (x, 1) = ((dGenLoop p e₀ hrel f)
        (Function.update x j (Set.projIcc 0 1 zero_le_one (2 * (x j : ℝ) - 1)))).1
      rw [hGt, if_neg h, dGenLoop_apply_coe]
      rfl
  have h1 : GenLoop.Homotopic (dGenLoop p e₀ hrel (GenLoop.transAt (Fin.succ j) f' f))
      (topFaceG (k+1) (cubeReindex (GenLoop.transAt (Fin.succ j) f' f))
        (cubeReindex_one _) Gt hGt_lift hGtbd) :=
    liftUniqueness p e₀ hrel (k+1) (cubeReindex (GenLoop.transAt (Fin.succ j) f' f))
      (cubeReindex_zero _) (cubeReindex_one _) (dLift p e₀ hrel _) Gt
      (dLift_spec p e₀ hrel _).1 hGt_lift (dLift_spec p e₀ hrel _).2.1 hGt0
      (dLift_spec p e₀ hrel _).2.2 hGtbd
  rw [hTop] at h1
  exact h1

end Hom

/-! ## The connecting map on homotopy classes -/

section DMap

variable (p : C(E, B)) (e₀ : E)

/-- The connecting map respects homotopy. -/
theorem dGenLoop_homotopic (hrel : ∀ k, HasHLPRel p k) {k : ℕ}
    {f f' : GenLoop (Fin (k+2)) B (p e₀)} (h : GenLoop.Homotopic f f') :
    GenLoop.Homotopic (dGenLoop p e₀ hrel f) (dGenLoop p e₀ hrel f') := by
  obtain ⟨Φ⟩ := h
  exact liftHomotopy p e₀ hrel f f' Φ (dLift p e₀ hrel f) (dLift p e₀ hrel f')
    (dLift_spec p e₀ hrel f).1 (dLift_spec p e₀ hrel f').1
    (dLift_spec p e₀ hrel f).2.1 (dLift_spec p e₀ hrel f').2.1
    (dLift_spec p e₀ hrel f).2.2 (dLift_spec p e₀ hrel f').2.2

/-- The connecting map of a constant cube is trivial. -/
theorem dGenLoop_const (hrel : ∀ k, HasHLPRel p k) {k : ℕ} :
    GenLoop.Homotopic (dGenLoop p e₀ hrel (GenLoop.const : GenLoop (Fin (k+2)) B (p e₀)))
      (GenLoop.const : GenLoop (Fin (k+1)) (fibre p (p e₀)) (fibrePoint p e₀)) := by
  have hGc : p.comp (ContinuousMap.const ((Fin (k+1) → I) × I) e₀)
      = cubeReindex (GenLoop.const : GenLoop (Fin (k+2)) B (p e₀)) := rfl
  have hc := liftUniqueness p e₀ hrel (k+1)
    (cubeReindex (GenLoop.const : GenLoop (Fin (k+2)) B (p e₀)))
    (cubeReindex_zero _) (cubeReindex_one _) (dLift p e₀ hrel _)
    (ContinuousMap.const ((Fin (k+1) → I) × I) e₀)
    (dLift_spec p e₀ hrel _).1 hGc (dLift_spec p e₀ hrel _).2.1 (fun _ => rfl)
    (dLift_spec p e₀ hrel _).2.2 (fun _ _ => rfl)
  have hconst : topFaceG (k+1) (cubeReindex (GenLoop.const : GenLoop (Fin (k+2)) B (p e₀)))
      (cubeReindex_one _) (ContinuousMap.const ((Fin (k+1) → I) × I) e₀) hGc (fun _ _ => rfl)
      = (GenLoop.const : GenLoop (Fin (k+1)) (fibre p (p e₀)) (fibrePoint p e₀)) := by
    apply GenLoop.ext
    intro x
    apply Subtype.ext
    rfl
  rw [hconst] at hc
  exact hc

/-- The underlying function of the connecting map, on homotopy groups. -/
noncomputable def dFun (hrel : ∀ k, HasHLPRel p k) (k : ℕ) :
    HomotopyGroup (Fin (k+2)) B (p e₀) →
      HomotopyGroup (Fin (k+1)) (fibre p (p e₀)) (fibrePoint p e₀) :=
  Quotient.lift (fun f => Quotient.mk _ (dGenLoop p e₀ hrel f))
    (fun f f' h => Quotient.sound (dGenLoop_homotopic p e₀ hrel h))

theorem dFun_mk (hrel : ∀ k, HasHLPRel p k) {k : ℕ}
    (f : GenLoop (Fin (k+2)) B (p e₀)) :
    dFun p e₀ hrel k ⟦f⟧ = ⟦dGenLoop p e₀ hrel f⟧ :=
  Quotient.lift_mk (fun g => Quotient.mk _ (dGenLoop p e₀ hrel g))
    (fun g g' h => Quotient.sound (dGenLoop_homotopic p e₀ hrel h)) f

theorem dFun_one (hrel : ∀ k, HasHLPRel p k) {k : ℕ} :
    dFun p e₀ hrel k 1 = 1 := by
  rw [HomotopyGroup.one_def (N := Fin (k+2)), dFun_mk,
    HomotopyGroup.one_def (N := Fin (k+1))]
  exact Quotient.sound (dGenLoop_const p e₀ hrel)

theorem dFun_mul (hrel : ∀ k, HasHLPRel p k) {k : ℕ}
    (a b : HomotopyGroup (Fin (k+2)) B (p e₀)) :
    dFun p e₀ hrel k (a * b) = dFun p e₀ hrel k a * dFun p e₀ hrel k b := by
  refine Quotient.inductionOn₂ a b (fun f f' => ?_)
  let j : Fin (k+1) := 0
  have hmul₁ := HomotopyGroup.mul_spec (N := Fin (k+2)) (X := B) (x := p e₀)
    (i := Fin.succ j) (p := f) (q := f')
  have hmul₂ := HomotopyGroup.mul_spec (N := Fin (k+1)) (X := fibre p (p e₀))
    (x := fibrePoint p e₀) (i := j) (p := dGenLoop p e₀ hrel f) (q := dGenLoop p e₀ hrel f')
  show dFun p e₀ hrel k (((· * ·) : HomotopyGroup (Fin (k+2)) B (p e₀) →
      HomotopyGroup (Fin (k+2)) B (p e₀) → HomotopyGroup (Fin (k+2)) B (p e₀)) ⟦f⟧ ⟦f'⟧)
    = ((· * ·) : HomotopyGroup (Fin (k+1)) (fibre p (p e₀)) (fibrePoint p e₀) →
      HomotopyGroup (Fin (k+1)) (fibre p (p e₀)) (fibrePoint p e₀) →
      HomotopyGroup (Fin (k+1)) (fibre p (p e₀)) (fibrePoint p e₀))
        (dFun p e₀ hrel k ⟦f⟧) (dFun p e₀ hrel k ⟦f'⟧)
  rw [hmul₁, dFun_mk, dFun_mk, dFun_mk, hmul₂]
  exact Quotient.sound (dGenLoop_transAt p e₀ hrel j f f')

/-- **The connecting map** `π_{k+2}(B) →* π_{k+1}(F)` of the long exact homotopy sequence. -/
noncomputable def dMap (hrel : ∀ k, HasHLPRel p k) (k : ℕ) :
    HomotopyGroup (Fin (k+2)) B (p e₀) →*
    HomotopyGroup (Fin (k+1)) (fibre p (p e₀)) (fibrePoint p e₀) where
  toFun := dFun p e₀ hrel k
  map_one' := dFun_one p e₀ hrel
  map_mul' := dFun_mul p e₀ hrel

end DMap

end

end Work.StemsB
