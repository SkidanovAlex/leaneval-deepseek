import Mathlib
import Submission.Work.StemsB.exists_lift_rel
import Submission.Work.StemsB.Fibrations

/-!
# Transport of joined points in the fibres of a Serre fibration along a lifted path

If `p : E → B` is a Serre fibration, `γ` is a path in `B` and `u`, `v` are two lifts of `γ` whose
starting points are joined inside the fibre `p ⁻¹' {γ 0}`, then their endpoints are joined inside
the fibre `p ⁻¹' {γ 1}`.

This is the well-definedness of the transport of `π₀` of the fibres along a path (the `π₀` of the
fibres of a Serre fibration is functorial in the path), and it is precisely the input needed by
`Work.Serre.zerothHomotopy_fibre_equiv_of_path`.

The proof is one application of the relative homotopy lifting property
(`Work.StemsB.exists_lift_rel`, the `k = 1` case) to the square `I¹ × I` and the base homotopy
`(x, t) ↦ γ t`, which is constant in the first coordinate:

* its lateral boundary `∂I¹ × I` is the union of the two faces `x = 0` and `x = 1`, carrying the
  lifts `u` and `v`;
* its bottom face `I¹ × {0}` carries the path `w` inside the fibre over `γ 0` joining `u 0` to
  `v 0`;
* the top face `I¹ × {1}` of the resulting lift is therefore a path in the fibre over `γ 1` joining
  `u 1` to `v 1`.
-/

open scoped Topology unitInterval

namespace Work.Serre

noncomputable section

/-- A point of the boundary of the `1`-cube has its only coordinate equal to `0` or to `1`. -/
private theorem cubeBdry_one_coord (x : Work.StemsB.CubeBdry 1) : x.1 0 = 0 ∨ x.1 0 = 1 := by
  obtain ⟨i, hi⟩ := x.2
  have hi0 : i = 0 := Subsingleton.elim i 0
  subst hi0
  exact hi

/-- `(1 : I) ≠ 0` in the unit interval. -/
private theorem one_ne_zero_I : ¬ ((1 : I) = 0) := by
  intro h
  have h2 : (((1 : I) : ℝ)) = (((0 : I) : ℝ)) := congrArg (fun z : I => (z : ℝ)) h
  norm_num at h2

/-- **The lateral boundary lift of the square is continuous.**  On the lateral boundary
`∂I¹ × I` the two faces `x = 0` and `x = 1` are both open and closed, so the map which is `u` on
the first face and `v` on the second is continuous. -/
private theorem continuous_cubeBdry_one_lateral {Y : Type*} [TopologicalSpace Y] (u v : C(I, Y)) :
    Continuous fun w : Work.StemsB.CubeBdry 1 × I => if w.1.1 0 = 0 then u w.2 else v w.2 := by
  have hcontI : Continuous fun w : Work.StemsB.CubeBdry 1 × I => w.1.1 0 :=
    (continuous_apply 0).comp (continuous_subtype_val.comp continuous_fst)
  have hcontR : Continuous fun w : Work.StemsB.CubeBdry 1 × I => ((w.1.1 0 : I) : ℝ) :=
    continuous_subtype_val.comp hcontI
  have hiff0 : ∀ w : Work.StemsB.CubeBdry 1 × I,
      (w.1.1 0 = 0) ↔ ((w.1.1 0 : I) : ℝ) < 1 / 2 := by
    intro w
    constructor
    · intro h; rw [h]; norm_num
    · intro h
      rcases cubeBdry_one_coord w.1 with h' | h'
      · exact h'
      · rw [h'] at h; norm_num at h
  have hclosed0 : IsClosed {w : Work.StemsB.CubeBdry 1 × I | w.1.1 0 = 0} :=
    isClosed_eq hcontI continuous_const
  have hopen0 : IsOpen {w : Work.StemsB.CubeBdry 1 × I | w.1.1 0 = 0} := by
    rw [show {w : Work.StemsB.CubeBdry 1 × I | w.1.1 0 = 0}
        = {w : Work.StemsB.CubeBdry 1 × I | ((w.1.1 0 : I) : ℝ) < 1 / 2} from Set.ext hiff0]
    exact isOpen_lt hcontR continuous_const
  have hfront : frontier {w : Work.StemsB.CubeBdry 1 × I | w.1.1 0 = 0} = ∅ := by
    rw [frontier_eq_closure_inter_closure, hclosed0.closure_eq, hopen0.isClosed_compl.closure_eq,
      Set.inter_compl_self]
  exact Continuous.if (fun a ha => absurd ha (by rw [hfront]; exact Set.notMem_empty a))
    (u.continuous.comp continuous_snd) (v.continuous.comp continuous_snd)

theorem joinedIn_fibre_of_lifted_path {E B : Type} [TopologicalSpace E] [TopologicalSpace B]
    (p : C(E, B)) (hp : Work.StemsB.IsSerreFibration p) (γ : C(unitInterval, B))
    (u v : C(unitInterval, E)) (hu : p.comp u = γ) (hv : p.comp v = γ)
    (hjoin : JoinedIn (p ⁻¹' {γ 0}) (u 0) (v 0)) :
    JoinedIn (p ⁻¹' {γ 1}) (u 1) (v 1) := by
  classical
  -- the path in the fibre over `γ 0` joining the starting points
  obtain ⟨w, hw⟩ := hjoin
  have hwt : ∀ t : I, p (w t) = γ 0 := fun t => hw t
  have hut : ∀ t : I, p (u t) = γ t := fun t => ContinuousMap.congr_fun hu t
  have hvt : ∀ t : I, p (v t) = γ t := fun t => ContinuousMap.congr_fun hv t
  let wC : C(I, E) := w.toContinuousMap
  have hwC : ∀ t : I, wC t = w t := fun t => rfl
  -- the base homotopy: the path `γ`, constant in the square coordinate
  let HH : C((Fin 1 → I) × I, B) := ⟨fun z => γ z.2, γ.continuous.comp continuous_snd⟩
  -- the lift of the bottom face: the path `w` inside the fibre over `γ 0`
  let f : C(Fin 1 → I, E) := wC.comp ⟨fun z : Fin 1 → I => z 0, continuous_apply 0⟩
  have hfval : ∀ z : Fin 1 → I, f z = w (z 0) := fun z => by
    show wC (z 0) = w (z 0)
    exact hwC (z 0)
  -- the lift of the lateral boundary: `u` on the face `x 0 = 0`, `v` on the face `x 0 = 1`
  let gd : C(Work.StemsB.CubeBdry 1 × I, E) :=
    ⟨fun z => if z.1.1 0 = 0 then u z.2 else v z.2, continuous_cubeBdry_one_lateral u v⟩
  have hgdval : ∀ (x : Work.StemsB.CubeBdry 1) (t : I),
      gd (x, t) = if x.1 0 = 0 then u t else v t := fun x t => rfl
  have hne : ∀ x : Work.StemsB.CubeBdry 1, x.1 0 = 1 → ¬ (x.1 0 = 0) := by
    intro x hx0 h0
    rw [hx0] at h0
    exact one_ne_zero_I h0
  have hf : p.comp f = HH.comp (Work.StemsB.zeroIncl 1) := by
    ext z
    show p (f z) = γ 0
    rw [hfval z]
    exact hwt (z 0)
  have hg : p.comp gd = HH.comp (Work.StemsB.bdryIncl 1) := by
    ext z
    obtain ⟨x, t⟩ := z
    show p (if x.1 0 = 0 then u t else v t) = γ t
    rcases cubeBdry_one_coord x with h | h
    · rw [if_pos h]; exact hut t
    · rw [if_neg (hne x h)]; exact hvt t
  have hg0 : ∀ x : Work.StemsB.CubeBdry 1, gd (x, 0) = f x.1 := by
    intro x
    show (if x.1 0 = 0 then u 0 else v 0) = w (x.1 0)
    rcases cubeBdry_one_coord x with h | h
    · rw [if_pos h, h]
      exact (w.source').symm
    · rw [if_neg (hne x h), h]
      exact (w.target').symm
  -- the relative homotopy lifting property, in the case `k = 1`
  obtain ⟨G, hGp, hG0, hGlat⟩ :=
    Work.StemsB.exists_lift_rel p hp 1 HH f hf gd hg hg0
  let z0 : Fin 1 → I := fun _ => 0
  let z1 : Fin 1 → I := fun _ => 1
  have hz0 : z0 ∈ Cube.boundary (Fin 1) := ⟨0, Or.inl rfl⟩
  have hz1 : z1 ∈ Cube.boundary (Fin 1) := ⟨0, Or.inr rfl⟩
  have hz10 : ¬ ((z1 : Fin 1 → I) 0 = 0) := fun h => one_ne_zero_I h
  -- the top face of the lift, a path in `E` from `u 1` to `v 1`
  refine ⟨Path.mk ⟨fun t : I => G ((fun _ => t), 1), by fun_prop⟩ ?_ ?_, ?_⟩
  · show G (z0, 1) = u 1
    rw [show G (z0, 1) = gd (⟨z0, hz0⟩, 1) from hGlat ⟨z0, hz0⟩ 1]
    show (if (z0 : Fin 1 → I) 0 = 0 then u 1 else v 1) = u 1
    rw [if_pos rfl]
  · show G (z1, 1) = v 1
    rw [show G (z1, 1) = gd (⟨z1, hz1⟩, 1) from hGlat ⟨z1, hz1⟩ 1]
    show (if (z1 : Fin 1 → I) 0 = 0 then u 1 else v 1) = v 1
    rw [if_neg hz10]
  · intro t
    show p (G ((fun _ => t), 1)) = γ 1
    have h1 : p (G ((fun _ => t), 1)) = HH ((fun _ => t), 1) :=
      ContinuousMap.congr_fun hGp ((fun _ => t), 1)
    rw [h1]
    rfl

/-- **The reverse direction**: the same statement with the roles of the two endpoints of the path
exchanged, obtained by applying `joinedIn_fibre_of_lifted_path` to the reversed path (and the
reversed lifts). -/
theorem joinedIn_fibre_of_lifted_path_symm {E B : Type} [TopologicalSpace E] [TopologicalSpace B]
    (p : C(E, B)) (hp : Work.StemsB.IsSerreFibration p) (γ : C(unitInterval, B))
    (u v : C(unitInterval, E)) (hu : p.comp u = γ) (hv : p.comp v = γ)
    (hjoin : JoinedIn (p ⁻¹' {γ 1}) (u 1) (v 1)) :
    JoinedIn (p ⁻¹' {γ 0}) (u 0) (v 0) := by
  let s : C(I, I) := ⟨unitInterval.symm, unitInterval.continuous_symm⟩
  have hγ0 : (γ.comp s) 0 = γ 1 := by
    show γ (s 0) = γ 1
    rw [show s 0 = 1 from unitInterval.symm_zero]
  have hγ1 : (γ.comp s) 1 = γ 0 := by
    show γ (s 1) = γ 0
    rw [show s 1 = 0 from unitInterval.symm_one]
  have hu0 : (u.comp s) 0 = u 1 := by
    show u (s 0) = u 1
    rw [show s 0 = 1 from unitInterval.symm_zero]
  have hu1 : (u.comp s) 1 = u 0 := by
    show u (s 1) = u 0
    rw [show s 1 = 0 from unitInterval.symm_one]
  have hv0 : (v.comp s) 0 = v 1 := by
    show v (s 0) = v 1
    rw [show s 0 = 1 from unitInterval.symm_zero]
  have hv1 : (v.comp s) 1 = v 0 := by
    show v (s 1) = v 0
    rw [show s 1 = 0 from unitInterval.symm_one]
  have hu' : p.comp (u.comp s) = γ.comp s := by
    ext t
    show p (u (s t)) = γ (s t)
    exact ContinuousMap.congr_fun hu (s t)
  have hv' : p.comp (v.comp s) = γ.comp s := by
    ext t
    show p (v (s t)) = γ (s t)
    exact ContinuousMap.congr_fun hv (s t)
  have hjoin' : JoinedIn (p ⁻¹' {(γ.comp s) 0}) ((u.comp s) 0) ((v.comp s) 0) := by
    rw [hγ0, hu0, hv0]
    exact hjoin
  have h := joinedIn_fibre_of_lifted_path p hp (γ.comp s) (u.comp s) (v.comp s) hu' hv' hjoin'
  rwa [hγ1, hu1, hv1] at h

/-- **The transport of the fibres of a Serre fibration is an equivalence relation at the level of
`π₀`**: two points over `γ 0` are joined in the fibre `p ⁻¹' {γ 0}` if and only if the endpoints of
any two lifts of `γ` through them are joined in the fibre `p ⁻¹' {γ 1}`.

(Only the two implications for a *fixed* pair of lifts `u`, `v` are asserted here; the statement is
the one used to show that the transport map is well defined on path components.) -/
theorem joinedIn_fibre_iff_of_lifted_path {E B : Type} [TopologicalSpace E] [TopologicalSpace B]
    (p : C(E, B)) (hp : Work.StemsB.IsSerreFibration p) (γ : C(unitInterval, B))
    (u v : C(unitInterval, E)) (hu : p.comp u = γ) (hv : p.comp v = γ) :
    JoinedIn (p ⁻¹' {γ 0}) (u 0) (v 0) ↔ JoinedIn (p ⁻¹' {γ 1}) (u 1) (v 1) :=
  ⟨fun h => joinedIn_fibre_of_lifted_path p hp γ u v hu hv h,
    fun h => joinedIn_fibre_of_lifted_path_symm p hp γ u v hu hv h⟩

end

end Work.Serre
