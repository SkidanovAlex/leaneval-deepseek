import Mathlib
import Submission.Work.Stems.Pi

/-!
# Changing the base point of a homotopy group, and homotopy invariance

This file supplies the geometric input for `Work.Stems.mulEquiv_of_homotopyEquiv`.
-/

open scoped Topology Topology.Homotopy unitInterval
open ContinuousMap

namespace Work.Stems

namespace Pinch

/-! ## The distance to the boundary of the cube -/

/-- The coordinatewise distance of `u i` to the two endpoints of the interval. -/
noncomputable def bdistFun {N : Type*} (i : N) (u : I^N) : ℝ := min (u i : ℝ) (1 - (u i : ℝ))

theorem continuous_bdistFun {N : Type*} (i : N) : Continuous (bdistFun i) := by
  have h : Continuous fun u : I^N => ((u i : I) : ℝ) :=
    continuous_subtype_val.comp (continuous_apply i)
  exact h.min (continuous_const.sub h)

theorem bdistFun_nonneg {N : Type*} (u : I^N) (i : N) : 0 ≤ bdistFun i u :=
  le_min (u i).2.1 (sub_nonneg.mpr (u i).2.2)

theorem bdistFun_le_half {N : Type*} (u : I^N) (i : N) : bdistFun i u ≤ 1 / 2 := by
  rcases le_total ((u i : I) : ℝ) (1 / 2) with h | h
  · exact le_trans (min_le_left _ _) h
  · exact le_trans (min_le_right _ _) (by linarith)

theorem bdistFun_eq_zero_iff {N : Type*} (u : I^N) (i : N) :
    bdistFun i u = 0 ↔ u i = 0 ∨ u i = 1 := by
  constructor
  · intro h
    rcases le_total ((u i : I) : ℝ) (1 - (u i : ℝ)) with hle | hle
    · left
      have h2 : ((u i : I) : ℝ) = 0 := by
        have := (min_eq_left hle).symm.trans h
        simpa using this
      exact Subtype.ext (h2.trans rfl)
    · right
      have h1 : 1 - ((u i : I) : ℝ) = 0 := (min_eq_right hle).symm.trans h
      have h2 : ((u i : I) : ℝ) = 1 := by linarith
      exact Subtype.ext (h2.trans rfl)
  · rintro (h | h)
    · rw [bdistFun, show ((u i : I) : ℝ) = 0 by rw [h]; rfl]
      simp
    · rw [bdistFun, show ((u i : I) : ℝ) = 1 by rw [h]; rfl]
      simp

theorem bdistFun_eq_quarter_imp {N : Type*} (u : I^N) (i : N) (h : bdistFun i u = 1 / 4) :
    ((u i : I) : ℝ) = 1 / 4 ∨ ((u i : I) : ℝ) = 3 / 4 := by
  rcases le_total ((u i : I) : ℝ) (1 - (u i : ℝ)) with hle | hle
  · left
    have : ((u i : I) : ℝ) = 1 / 4 := by
      have := (min_eq_left hle).symm.trans h
      simpa using this
    exact this
  · right
    have h1 : 1 - ((u i : I) : ℝ) = 1 / 4 := (min_eq_right hle).symm.trans h
    linarith

/-! ## Two basic constructions -/

/-- Postcomposition of a generalized loop with a continuous map, as a generalized loop. -/
def mapGenLoop {N X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y] (f : C(X, Y)) {x : X}
    (w : Ω^ N X x) : Ω^ N Y (f x) :=
  ⟨f.comp w.1, fun y hy => by
    rw [ContinuousMap.comp_apply]
    exact congr_arg f (GenLoop.boundary w y hy)⟩

theorem HomotopyGroup.map_mk' {N X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
    (f : C(X, Y)) {x : X} (w : Ω^ N X x) :
    HomotopyGroup.map f ⟦w⟧ = ⟦mapGenLoop f w⟧ := rfl

@[simp]
theorem mapGenLoop_apply {N X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
    (f : C(X, Y)) {x : X} (w : Ω^ N X x) (t : I^N) : mapGenLoop f w t = f (w t) := rfl

theorem mapGenLoop_comp {N X Y Z : Type*} [TopologicalSpace X] [TopologicalSpace Y]
    [TopologicalSpace Z] (f : C(X, Y)) (g : C(Y, Z)) {x : X} (w : Ω^ N X x) :
    mapGenLoop g (mapGenLoop f w) = mapGenLoop (g.comp f) w := rfl

/-- The path traced by a base point under a homotopy. -/
def homotopyPath {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y] {f g : C(X, Y)}
    (H : f.Homotopy g) (x : X) : Path (f x) (g x) where
  toContinuousMap :=
    ⟨fun t => H (t, x), H.continuous.comp (continuous_id.prodMk continuous_const)⟩
  source' := H.map_zero_left x
  target' := H.map_one_left x

theorem homotopyPath_apply {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
    {f g : C(X, Y)} (H : f.Homotopy g) (x : X) (t : I) :
    homotopyPath H x t = H (t, x) := rfl

theorem homotopyPath_symm {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
    {f g : C(X, Y)} (H : f.Homotopy g) (x : X) :
    homotopyPath H.symm x = (homotopyPath H x).symm := by
  ext t
  rfl

section Finite

variable {N : Type*} [Fintype N] [Nonempty N]
variable {Y : Type*} [TopologicalSpace Y]

/-- The distance of a point of the cube `I^N` to its boundary, measured coordinatewise.
It is `0` exactly on the boundary and `1 / 2` at the centre. -/
noncomputable def bdist : (I^N) → ℝ := Finset.univ.inf' Finset.univ_nonempty bdistFun

theorem bdist_apply (u : I^N) :
    bdist u = Finset.univ.inf' Finset.univ_nonempty (fun i => bdistFun i u) :=
  Finset.inf'_apply ..

theorem continuous_bdist : Continuous (bdist (N := N)) := by
  rw [bdist]
  exact Continuous.finset_inf' (s := (Finset.univ : Finset N))
    (hne := (Finset.univ_nonempty : (Finset.univ : Finset N).Nonempty))
    (fun i _ => continuous_bdistFun i)

theorem bdist_le_apply (u : I^N) (i : N) : bdist u ≤ bdistFun i u := by
  rw [bdist_apply u]
  exact Finset.inf'_le _ (Finset.mem_univ i)

theorem bdist_le_iff {a : ℝ} (u : I^N) :
    bdist u ≤ a ↔ ∃ i, bdistFun i u ≤ a := by
  rw [bdist_apply u, Finset.inf'_le_iff Finset.univ_nonempty]
  simp

theorem le_bdist {a : ℝ} (u : I^N) : a ≤ bdist u ↔ ∀ i, a ≤ bdistFun i u := by
  rw [bdist_apply u]
  exact ⟨fun h i => le_trans h (Finset.inf'_le _ (Finset.mem_univ i)),
    fun h => Finset.le_inf' _ _ fun i _ => h i⟩

theorem bdist_nonneg (u : I^N) : 0 ≤ bdist u := by
  rw [le_bdist]; exact fun i => bdistFun_nonneg u i

theorem bdist_le_half (u : I^N) : bdist u ≤ 1 / 2 :=
  le_trans (bdist_le_apply u (Classical.arbitrary N)) (bdistFun_le_half u _)

theorem bdist_eq_zero_iff (u : I^N) : bdist u = 0 ↔ u ∈ Cube.boundary N := by
  constructor
  · intro h
    obtain ⟨i, hi⟩ := (bdist_le_iff u).mp (le_of_eq h)
    exact ⟨i, (bdistFun_eq_zero_iff u i).mp (le_antisymm hi (bdistFun_nonneg u i))⟩
  · rintro ⟨i, hi⟩
    have h0 : bdist u ≤ 0 := by
      refine le_trans (bdist_le_apply u i) ?_
      rw [(bdistFun_eq_zero_iff u i).mpr hi]
    exact le_antisymm h0 (bdist_nonneg u)

theorem bdist_eq_quarter_imp (u : I^N) (h : bdist u = 1 / 4) :
    ∃ i, ((u i : I) : ℝ) = 1 / 4 ∨ ((u i : I) : ℝ) = 3 / 4 := by
  obtain ⟨i, -, hi⟩ := Finset.exists_mem_eq_inf' (s := (Finset.univ : Finset N))
    Finset.univ_nonempty (fun i => bdistFun i u)
  have h0 : bdistFun i u = 1 / 4 := by
    rw [bdist_apply u] at h
    rw [hi] at h
    exact h
  exact ⟨i, bdistFun_eq_quarter_imp u i h0⟩

/-- The rescaling of the inner cube `{u | 1 / 4 ≤ bdist u}` onto the whole cube. -/
noncomputable def expandFun (u : I^N) : I^N :=
  fun i => Set.projIcc (0 : ℝ) 1 zero_le_one (2 * (u i : ℝ) - 1 / 2)

theorem continuous_expandFun : Continuous (expandFun (N := N)) := by
  refine continuous_pi fun i => ?_
  have h : Continuous fun u : I^N => ((u i : I) : ℝ) :=
    continuous_subtype_val.comp (continuous_apply i)
  exact continuous_projIcc.comp ((continuous_const.mul h).sub continuous_const)

/-- `expand` as a continuous map. -/
noncomputable def expand : C(I^N, I^N) := ⟨expandFun, continuous_expandFun⟩

theorem expand_apply (u : I^N) (i : N) :
    expand u i = Set.projIcc (0 : ℝ) 1 zero_le_one (2 * (u i : ℝ) - 1 / 2) := rfl

theorem expand_mem_boundary_of_bdist_eq (u : I^N) (h : bdist u = 1 / 4) :
    expand u ∈ Cube.boundary N := by
  obtain ⟨i, hi | hi⟩ := bdist_eq_quarter_imp u h
  · refine ⟨i, Or.inl ?_⟩
    show expandFun u i = 0
    have hz : 2 * ((u i : I) : ℝ) - 1 / 2 = 0 := by rw [hi]; norm_num
    rw [expandFun, hz]
    simpa using Set.projIcc_left (a := (0 : ℝ)) (b := 1) zero_le_one
  · refine ⟨i, Or.inr ?_⟩
    show expandFun u i = 1
    have hz : 2 * ((u i : I) : ℝ) - 1 / 2 = 1 := by rw [hi]; norm_num
    rw [expandFun, hz]
    simpa using Set.projIcc_right (a := (0 : ℝ)) (b := 1) zero_le_one

/-- The shell parameter: `1` on the boundary, `0` on the inner cube `bdist u ≥ 1 / 4`. -/
noncomputable def shparamFun (u : I^N) : I :=
  Set.projIcc (0 : ℝ) 1 zero_le_one (1 - 4 * bdist u)

theorem continuous_shparamFun : Continuous (shparamFun (N := N)) :=
  continuous_projIcc.comp (continuous_const.sub ((continuous_bdist (N := N)).const_mul 4))

/-- `shparam` as a continuous map. -/
noncomputable def shparam : C(I^N, I) := ⟨shparamFun, continuous_shparamFun⟩

theorem shparam_apply (u : I^N) :
    shparam u = Set.projIcc (0 : ℝ) 1 zero_le_one (1 - 4 * bdist u) := rfl

theorem shparam_eq_one_of_mem_boundary (u : I^N) (h : u ∈ Cube.boundary N) : shparam u = 1 := by
  show shparamFun u = 1
  have h0 : bdist u = 0 := (bdist_eq_zero_iff u).mpr h
  have h1 : 1 - 4 * bdist u = 1 := by rw [h0]; norm_num
  rw [shparamFun, h1]
  simpa using Set.projIcc_right (a := (0 : ℝ)) (b := 1) zero_le_one

theorem shparam_eq_zero_of_bdist_ge (u : I^N) (h : 1 / 4 ≤ bdist u) : shparam u = 0 := by
  show shparamFun u = 0
  have h1 : 1 - 4 * bdist u ≤ 0 := by linarith
  rw [shparamFun]
  simpa using Set.projIcc_of_le_left (a := (0 : ℝ)) (b := 1) (h := zero_le_one) (x := 1 - 4 * bdist u) h1

theorem bdistFun_expand (u : I^N) (i : N) (h : 1 / 4 ≤ bdistFun i u) :
    bdistFun i (expand u) = 2 * (bdistFun i u - 1 / 4) := by
  have h1 : (1 / 4 : ℝ) ≤ ((u i : I) : ℝ) := le_trans h (min_le_left _ _)
  have h2 : (1 / 4 : ℝ) ≤ 1 - ((u i : I) : ℝ) := le_trans h (min_le_right _ _)
  have hA : ((expand u) i : ℝ) = 2 * ((u i : I) : ℝ) - 1 / 2 := by
    rw [expand_apply,
      Set.projIcc_of_mem zero_le_one (show 2 * ((u i : I) : ℝ) - 1 / 2 ∈ Set.Icc 0 1 by
        constructor <;> linarith)]
  rw [bdistFun, bdistFun, hA]
  rcases le_total ((u i : I) : ℝ) (1 - ((u i : I) : ℝ)) with hle | hle
  · have hle' : 2 * ((u i : I) : ℝ) - 1 / 2 ≤ 1 - (2 * ((u i : I) : ℝ) - 1 / 2) := by linarith
    rw [min_eq_left hle, min_eq_left hle']
    ring
  · have hle' : 1 - (2 * ((u i : I) : ℝ) - 1 / 2) ≤ 2 * ((u i : I) : ℝ) - 1 / 2 := by linarith
    rw [min_eq_right hle, min_eq_right hle']
    ring

theorem bdist_expand_eq (u : I^N) (h : 1 / 4 ≤ bdist u) :
    bdist (expand u) = 2 * (bdist u - 1 / 4) := by
  refine le_antisymm ?_ ?_
  · obtain ⟨j, -, hj⟩ := Finset.exists_mem_eq_inf' (s := (Finset.univ : Finset N))
      Finset.univ_nonempty (fun i => bdistFun i u)
    have hbu : bdist u = bdistFun j u := by rw [bdist_apply u, hj]
    calc bdist (expand u) ≤ bdistFun j (expand u) := bdist_le_apply _ _
      _ = 2 * (bdistFun j u - 1 / 4) := bdistFun_expand u j (hbu ▸ h)
      _ = 2 * (bdist u - 1 / 4) := by rw [hbu]
  · rw [le_bdist]
    intro i
    have hi : 1 / 4 ≤ bdistFun i u := le_trans h (bdist_le_apply u i)
    calc 2 * (bdist u - 1 / 4) ≤ 2 * (bdistFun i u - 1 / 4) := by
          have := bdist_le_apply u i; linarith
      _ = bdistFun i (expand u) := (bdistFun_expand u i hi).symm

theorem expand_mem_boundary_of_bdist_le (u : I^N) (h : bdist u ≤ 1 / 4) :
    expand u ∈ Cube.boundary N := by
  obtain ⟨i, hi⟩ := (bdist_le_iff u).mp h
  have hcase : ((u i : I) : ℝ) ≤ 1 / 4 ∨ 3 / 4 ≤ ((u i : I) : ℝ) := by
    rcases le_total ((u i : I) : ℝ) (1 - ((u i : I) : ℝ)) with hle | hle
    · left
      rw [bdistFun, min_eq_left hle] at hi
      exact hi
    · right
      rw [bdistFun, min_eq_right hle] at hi
      linarith
  refine ⟨i, ?_⟩
  rcases hcase with hcase | hcase
  · left
    show expandFun u i = 0
    rw [expandFun, Set.projIcc_of_le_left (a := (0 : ℝ)) (b := 1) (h := zero_le_one)
      (x := 2 * ((u i : I) : ℝ) - 1 / 2) (by linarith)]
    rfl
  · right
    show expandFun u i = 1
    rw [expandFun, Set.projIcc_of_right_le (a := (0 : ℝ)) (b := 1) (h := zero_le_one)
      (x := 2 * ((u i : I) : ℝ) - 1 / 2) (by linarith)]
    rfl

/-- The underlying function of the pinched loop: the inner cube carries a rescaled copy of `w`,
the shell is filled by `p`. -/
noncomputable def pinchFun {y z : Y} (p : Path y z) (w : Ω^ N Y y) (u : I^N) : Y :=
  if (1 / 4 : ℝ) ≤ bdist u then w (expand u) else p (shparam u)

theorem continuous_pinchFun {y z : Y} (p : Path y z) (w : Ω^ N Y y) :
    Continuous (pinchFun (N := N) p w) := by
  refine Continuous.if_le (f' := fun u : I^N => w (expand u))
    (g' := fun u : I^N => p (shparam u)) (f := fun _ : I^N => (1 / 4 : ℝ)) (g := bdist)
    ?_ ?_ continuous_const (continuous_bdist (N := N)) ?_
  · exact w.1.continuous.comp expand.continuous
  · exact p.continuous.comp shparam.continuous
  · intro u hu
    have hb : bdist u = 1 / 4 := hu.symm
    rw [GenLoop.boundary w (expand u) (expand_mem_boundary_of_bdist_eq u hb),
      shparam_eq_zero_of_bdist_ge u (le_of_eq hb.symm)]
    exact (Path.source p).symm

/-- **The pinched loop.**  Given a loop `w : Ω^ N Y y` and a path `p : Path y z`, put a rescaled
copy of `w` on the inner cube and fill the shell with `p`.  The result is a loop based at `z`. -/
noncomputable def pinch {y z : Y} (p : Path y z) (w : Ω^ N Y y) : Ω^ N Y z :=
  ⟨⟨pinchFun (N := N) p w, continuous_pinchFun p w⟩, by
    intro u hu
    have h0 : bdist u = 0 := (bdist_eq_zero_iff u).mpr hu
    have hlt : ¬ (1 / 4 : ℝ) ≤ bdist u := by rw [h0]; norm_num
    show (if (1 / 4 : ℝ) ≤ bdist u then w (expand u) else p (shparam u)) = z
    rw [if_neg hlt, shparam_eq_one_of_mem_boundary u hu]
    exact Path.target p⟩

theorem pinch_apply {y z : Y} (p : Path y z) (w : Ω^ N Y y) (u : I^N) :
    pinch p w u = pinchFun (N := N) p w u := rfl

/-- The pinching construction is compatible with homotopies relative to the boundary. -/
theorem pinch_homotopic {y z : Y} (p : Path y z) {w w' : Ω^ N Y y}
    (h : GenLoop.Homotopic w w') : GenLoop.Homotopic (pinch p w) (pinch p w') := by
  obtain ⟨H⟩ := h
  refine ⟨⟨⟨fun su : I × I^N =>
      if (1 / 4 : ℝ) ≤ bdist su.2 then H (su.1, expand su.2) else p (shparam su.2), ?_⟩,
    ?_, ?_⟩, ?_⟩
  · refine Continuous.if_le (f' := fun su : I × I^N => H (su.1, expand su.2))
      (g' := fun su : I × I^N => p (shparam su.2))
      (f := fun _ : I × I^N => (1 / 4 : ℝ))
      (g := fun su : I × I^N => bdist su.2) ?_ ?_ continuous_const
      (continuous_bdist.comp continuous_snd) ?_
    · exact H.continuous.comp (continuous_fst.prodMk (expand.continuous.comp continuous_snd))
    · exact (p.continuous.comp shparam.continuous).comp continuous_snd
    · intro su hsu
      have hb : bdist su.2 = 1 / 4 := hsu.symm
      have hbnd := expand_mem_boundary_of_bdist_eq su.2 hb
      have h1 : H (su.1, expand su.2) = y := by
        rw [H.eq_fst su.1 hbnd]
        exact GenLoop.boundary w (expand su.2) hbnd
      have h2 : p (shparam su.2) = y := by
        rw [shparam_eq_zero_of_bdist_ge su.2 (le_of_eq hb.symm)]
        exact Path.source p
      rw [h1, h2]
  · intro u
    show (if (1 / 4 : ℝ) ≤ bdist u then H (0, expand u) else p (shparam u)) =
      pinchFun (N := N) p w u
    have h : H (0, expand u) = w (expand u) := H.map_zero_left (expand u)
    rw [h]
    rfl
  · intro u
    show (if (1 / 4 : ℝ) ≤ bdist u then H (1, expand u) else p (shparam u)) =
      pinchFun (N := N) p w' u
    have h : H (1, expand u) = w' (expand u) := H.map_one_left (expand u)
    rw [h]
    rfl
  · intro t u hu
    have h0 : bdist u = 0 := (bdist_eq_zero_iff u).mpr hu
    have hlt : ¬ (1 / 4 : ℝ) ≤ bdist u := by rw [h0]; norm_num
    show (if (1 / 4 : ℝ) ≤ bdist u then H (t, expand u) else p (shparam u)) =
      pinchFun (N := N) p w u
    rw [if_neg hlt, pinchFun, if_neg hlt]

/-- **Base point change** on the `N`-th homotopy group, along a path. -/
noncomputable def transport {y z : Y} (p : Path y z) :
    HomotopyGroup N Y y → HomotopyGroup N Y z :=
  Quotient.map (pinch (N := N) p) (fun _ _ h => pinch_homotopic p h)

theorem transport_mk {y z : Y} (p : Path y z) (w : Ω^ N Y y) :
    transport (N := N) p ⟦w⟧ = ⟦pinch p w⟧ := rfl

/-! ## Undoing the rescaling: the reparametrisation `σ_r` -/

section Helper

variable {N : Type*} [Fintype N] [Nonempty N]

@[simp] theorem coe_zero_I : ((0 : I) : ℝ) = 0 := rfl
@[simp] theorem coe_one_I : ((1 : I) : ℝ) = 1 := rfl

theorem projIcc_self (x : I) : Set.projIcc (0 : ℝ) 1 zero_le_one (x : ℝ) = x :=
  Set.projIcc_of_mem zero_le_one x.2

theorem projIcc_of_le_zero {x : ℝ} (hx : x ≤ 0) :
    Set.projIcc (0 : ℝ) 1 zero_le_one x = (0 : I) := by
  simpa using Set.projIcc_of_le_left (a := (0 : ℝ)) (b := 1) (h := zero_le_one) hx

theorem projIcc_of_one_le {x : ℝ} (hx : 1 ≤ x) :
    Set.projIcc (0 : ℝ) 1 zero_le_one x = (1 : I) := by
  simpa using Set.projIcc_of_right_le (a := (0 : ℝ)) (b := 1) (h := zero_le_one) hx

/-- A one-parameter family of self-maps of the cube, deforming `expand` into the identity. -/
noncomputable def sigmadef (r : ℝ) (u : I^N) : I^N :=
  fun i => Set.projIcc (0 : ℝ) 1 zero_le_one
    ((1 - r) * (2 * (u i : ℝ) - 1 / 2) + r * (u i : ℝ))

theorem continuous_sigmadef : Continuous fun q : I × I^N => sigmadef (q.1 : ℝ) q.2 := by
  refine continuous_pi fun i => ?_
  refine continuous_projIcc.comp ?_
  have h1 : Continuous fun q : I × I^N => ((q.2 i : I) : ℝ) :=
    continuous_subtype_val.comp ((continuous_apply i).comp continuous_snd)
  have h2 : Continuous fun q : I × I^N => (q.1 : ℝ) :=
    continuous_subtype_val.comp continuous_fst
  exact (((continuous_const.sub h2).mul ((h1.const_mul 2).sub continuous_const)).add
    (h2.mul h1))

theorem sigmadef_zero (u : I^N) : sigmadef 0 u = expand u := by
  funext i
  apply Subtype.ext
  have harg : (1 - (0 : ℝ)) * (2 * (u i : ℝ) - 1 / 2) + (0 : ℝ) * (u i : ℝ)
      = 2 * (u i : ℝ) - 1 / 2 := by ring
  unfold sigmadef
  rw [expand_apply, harg]

theorem sigmadef_one (u : I^N) : sigmadef 1 u = u := by
  funext i
  apply Subtype.ext
  unfold sigmadef
  norm_num

theorem sigmadef_mem_boundary {r : ℝ} (hr0 : 0 ≤ r) (hr1 : r ≤ 1) {u : I^N}
    (hu : u ∈ Cube.boundary N) : sigmadef r u ∈ Cube.boundary N := by
  obtain ⟨i, hi | hi⟩ := hu
  · have hi' : ((u i : I) : ℝ) = 0 := by rw [hi]; rfl
    refine ⟨i, Or.inl ?_⟩
    show sigmadef r u i = 0
    simp only [sigmadef, hi', mul_zero, add_zero]
    rw [show (1 - r) * (0 - 1 / 2) = -(1 - r) / 2 by ring]
    exact projIcc_of_le_zero (by linarith)
  · have hi' : ((u i : I) : ℝ) = 1 := by rw [hi]; rfl
    refine ⟨i, Or.inr ?_⟩
    show sigmadef r u i = 1
    simp only [sigmadef, hi']
    rw [show (1 - r) * (2 * 1 - 1 / 2) + r * 1 = 3 / 2 - r / 2 by ring]
    exact projIcc_of_one_le (by linarith)

end Helper

/-! ## The "rescaled copy" of a loop -/

section Rescale

variable {N : Type*} [Fintype N] [Nonempty N] {Y : Type*} [TopologicalSpace Y]

/-- The loop obtained by precomposing `w` with the rescaling `expand`. -/
noncomputable def innerGraph {X : Type*} [TopologicalSpace X] (g : C(X, Y)) {x : X}
    (α : Ω^ N X x) : Ω^ N Y (g x) :=
  ⟨(mapGenLoop g α).1.comp expand, fun u hu => by
    refine GenLoop.boundary (mapGenLoop g α) (expand u) ?_
    refine expand_mem_boundary_of_bdist_le u ?_
    rw [(bdist_eq_zero_iff u).mpr hu]
    norm_num⟩

theorem innerGraph_apply {X : Type*} [TopologicalSpace X] (g : C(X, Y)) {x : X}
    (α : Ω^ N X x) (u : I^N) : innerGraph g α u = g (α (expand u)) := rfl

theorem innerGraph_apply_of_shell {X : Type*} [TopologicalSpace X] (g : C(X, Y)) {x : X}
    (α : Ω^ N X x) (u : I^N) (h : bdist u ≤ 1 / 4) : innerGraph g α u = g x := by
  rw [innerGraph_apply, GenLoop.boundary α (expand u) (expand_mem_boundary_of_bdist_le u h)]

/-- Precomposing with the rescaling `expand` does not change the homotopy class of a loop. -/
theorem innerGraph_homotopic {X : Type*} [TopologicalSpace X] (g : C(X, Y)) {x : X}
    (α : Ω^ N X x) : GenLoop.Homotopic (innerGraph g α) (mapGenLoop g α) := by
  refine ⟨⟨⟨fun q : I × I^N => g (α (sigmadef (q.1 : ℝ) q.2)), ?_⟩, ?_, ?_⟩, ?_⟩
  · exact (mapGenLoop g α).1.continuous.comp continuous_sigmadef
  · intro u
    show g (α (sigmadef ((0 : I) : ℝ) u)) = innerGraph g α u
    rw [coe_zero_I, sigmadef_zero]
    rfl
  · intro u
    show g (α (sigmadef ((1 : I) : ℝ) u)) = mapGenLoop g α u
    rw [coe_one_I, sigmadef_one]
    rfl
  · intro r u hu
    show g (α (sigmadef (r : ℝ) u)) = innerGraph g α u
    rw [GenLoop.boundary α (sigmadef (r : ℝ) u)
      (sigmadef_mem_boundary r.2.1 r.2.2 hu)]
    exact (innerGraph_apply_of_shell g α u (by rw [(bdist_eq_zero_iff u).mpr hu]; norm_num)).symm

end Rescale


/-! ## Homotopy invariance of the homotopy groups -/

section HomInv

variable {X : Type*} [TopologicalSpace X] {f g : C(X, Y)}

/-- The homotopy used in the proof of homotopy invariance. -/
noncomputable def PhiFun (H : f.Homotopy g) {x : X} (α : Ω^ N X x) (q : I × I^N) : Y :=
  if (1 / 4 : ℝ) ≤ bdist q.2 then H (q.1, α (expand q.2))
  else homotopyPath H x (Set.projIcc (0 : ℝ) 1 zero_le_one
    ((q.1 : ℝ) + (1 - (q.1 : ℝ)) * ((shparam q.2 : I) : ℝ)))

theorem continuous_PhiFun (H : f.Homotopy g) {x : X} (α : Ω^ N X x) :
    Continuous (PhiFun (N := N) H α) := by
  have h2 : Continuous fun q : I × I^N => (q.1 : ℝ) :=
    continuous_subtype_val.comp continuous_fst
  have h3 : Continuous fun q : I × I^N => ((shparam q.2 : I) : ℝ) :=
    continuous_subtype_val.comp (shparam.continuous.comp continuous_snd)
  have h4 : Continuous fun q : I × I^N => Set.projIcc (0 : ℝ) 1 zero_le_one
      ((q.1 : ℝ) + (1 - (q.1 : ℝ)) * ((shparam q.2 : I) : ℝ)) :=
    continuous_projIcc.comp (h2.add ((continuous_const.sub h2).mul h3))
  refine Continuous.if_le (f' := fun q : I × I^N => H (q.1, α (expand q.2)))
    (g' := fun q : I × I^N => homotopyPath H x (Set.projIcc (0 : ℝ) 1 zero_le_one
      ((q.1 : ℝ) + (1 - (q.1 : ℝ)) * ((shparam q.2 : I) : ℝ))))
    (f := fun _ : I × I^N => (1 / 4 : ℝ)) (g := fun q : I × I^N => bdist q.2)
    ?_ ?_ continuous_const (continuous_bdist.comp continuous_snd) ?_
  · exact H.continuous.comp (continuous_fst.prodMk
      (α.1.continuous.comp (expand.continuous.comp continuous_snd)))
  · exact (homotopyPath H x).continuous.comp h4
  · intro q hq
    have hb : bdist q.2 = 1 / 4 := hq.symm
    have h0 : shparam q.2 = 0 := shparam_eq_zero_of_bdist_ge q.2 (le_of_eq hb.symm)
    have hx : α (expand q.2) = x :=
      GenLoop.boundary α (expand q.2) (expand_mem_boundary_of_bdist_eq q.2 hb)
    have harg : (q.1 : ℝ) + (1 - (q.1 : ℝ)) * ((shparam q.2 : I) : ℝ) = (q.1 : ℝ) := by
      rw [h0, coe_zero_I]; ring
    rw [hx, harg, projIcc_self, homotopyPath_apply]

/-- **The first half of homotopy invariance.** -/
theorem pinch_homotopic_innerGraph (H : f.Homotopy g) {x : X} (α : Ω^ N X x) :
    GenLoop.Homotopic (pinch (homotopyPath H x) (mapGenLoop f α)) (innerGraph g α) := by
  refine ⟨⟨⟨PhiFun (N := N) H α, continuous_PhiFun H α⟩, ?_, ?_⟩, ?_⟩
  · intro u
    show PhiFun (N := N) H α (0, u) = pinchFun (N := N) (homotopyPath H x) (mapGenLoop f α) u
    show (if (1 / 4 : ℝ) ≤ bdist u then H ((0 : I), α (expand u))
        else homotopyPath H x (Set.projIcc (0 : ℝ) 1 zero_le_one
          (((0 : I) : ℝ) + (1 - ((0 : I) : ℝ)) * ((shparam u : I) : ℝ))))
      = (if (1 / 4 : ℝ) ≤ bdist u then mapGenLoop f α (expand u)
        else homotopyPath H x (shparam u))
    split_ifs with h
    · exact H.map_zero_left (α (expand u))
    · congr 1
      rw [show ((0 : I) : ℝ) + (1 - ((0 : I) : ℝ)) * ((shparam u : I) : ℝ) = (shparam u : ℝ) by
        rw [coe_zero_I]; ring]
      exact projIcc_self (shparam u)
  · intro u
    show PhiFun (N := N) H α (1, u) = innerGraph g α u
    show (if (1 / 4 : ℝ) ≤ bdist u then H ((1 : I), α (expand u))
        else homotopyPath H x (Set.projIcc (0 : ℝ) 1 zero_le_one
          (((1 : I) : ℝ) + (1 - ((1 : I) : ℝ)) * ((shparam u : I) : ℝ))))
      = g (α (expand u))
    split_ifs with h
    · exact H.map_one_left (α (expand u))
    · have hinner : g (α (expand u)) = g x := by
        rw [GenLoop.boundary α (expand u)
          (expand_mem_boundary_of_bdist_le u (le_of_lt (not_le.mp h)))]
      have hg : H ((1 : I), x) = g x := H.map_one_left x
      rw [hinner, homotopyPath_apply,
        show ((1 : I) : ℝ) + (1 - ((1 : I) : ℝ)) * ((shparam u : I) : ℝ) = 1 by
          rw [coe_one_I]; ring,
        projIcc_of_one_le le_rfl, hg]
  · intro r u hu
    show PhiFun (N := N) H α (r, u)
      = pinchFun (N := N) (homotopyPath H x) (mapGenLoop f α) u
    have h0 : bdist u = 0 := (bdist_eq_zero_iff u).mpr hu
    show (if (1 / 4 : ℝ) ≤ bdist u then H (r, α (expand u))
        else homotopyPath H x (Set.projIcc (0 : ℝ) 1 zero_le_one
          ((r : ℝ) + (1 - (r : ℝ)) * ((shparam u : I) : ℝ))))
      = (if (1 / 4 : ℝ) ≤ bdist u then mapGenLoop f α (expand u)
        else homotopyPath H x (shparam u))
    split_ifs with h
    · exfalso; rw [h0] at h; norm_num at h
    · rw [shparam_eq_one_of_mem_boundary u hu, coe_one_I,
        show (r : ℝ) + (1 - (r : ℝ)) * 1 = 1 by ring,
        projIcc_of_one_le le_rfl, homotopyPath_apply]

/-- **Homotopy invariance**: a homotopy `H : f ~ g` induces the base point change. -/
theorem pinch_homotopic_mapGenLoop (H : f.Homotopy g) {x : X} (α : Ω^ N X x) :
    GenLoop.Homotopic (pinch (homotopyPath H x) (mapGenLoop f α)) (mapGenLoop g α) :=
  (pinch_homotopic_innerGraph H α).trans (innerGraph_homotopic g α)

theorem transport_map (H : f.Homotopy g) (x : X) (a : HomotopyGroup N X x) :
    transport (N := N) (homotopyPath H x) (HomotopyGroup.map f a) = HomotopyGroup.map g a := by
  induction a using Quotient.inductionOn with
  | h α =>
    rw [HomotopyGroup.map_mk', transport_mk, HomotopyGroup.map_mk']
    exact Quotient.sound (pinch_homotopic_mapGenLoop H α)

end HomInv


/-! ## The transport along `p` and along `p.symm` are mutually inverse -/

section Invert

variable {Y : Type*} [TopologicalSpace Y]

theorem sigma_val (t : I) : (σ t : ℝ) = 1 - (t : ℝ) := rfl

/-- Radial profile of the shell of a doubly pinched loop: `p` up and back down. -/
noncomputable def updownFun (t : ℝ) : ℝ := if t ≤ 1 / 4 then 4 * t else 3 - 8 * t

theorem continuous_updownFun : Continuous updownFun := by
  unfold updownFun
  refine continuous_if_le continuous_id continuous_const ?_ ?_ ?_
  · fun_prop
  · fun_prop
  · intro x hx; linarith

theorem updownFun_le {t : ℝ} (h : t ≤ 1 / 4) : updownFun t = 4 * t := if_pos h

theorem updownFun_ge {t : ℝ} (h : 1 / 4 ≤ t) : updownFun t = 3 - 8 * t := by
  rcases lt_or_eq_of_le h with hlt | heq
  · rw [updownFun, if_neg (not_le.mpr hlt)]
  · subst heq; rw [updownFun_le le_rfl]; norm_num

theorem updownFun_mem {t : ℝ} (ht0 : 0 ≤ t) (ht : t ≤ 3 / 8) :
    updownFun t ∈ Set.Icc (0 : ℝ) 1 := by
  rcases le_or_gt t (1 / 4) with h | h
  · rw [updownFun_le h]; constructor <;> linarith
  · rw [updownFun_ge (le_of_lt h)]; constructor <;> linarith

theorem shparam_val {u : I^N} (h : bdist u ≤ 1 / 4) :
    ((shparam u : I) : ℝ) = 1 - 4 * bdist u := by
  have hx : (1 - 4 * bdist u) ∈ Set.Icc (0 : ℝ) 1 := by
    constructor <;> linarith [bdist_nonneg u]
  rw [shparam_apply, Set.projIcc_of_mem zero_le_one hx]

theorem bdist_expand_eq_max (u : I^N) :
    bdist (expand u) = 2 * max 0 (bdist u - 1 / 4) := by
  rcases le_or_gt (bdist u) (1 / 4) with h | h
  · rw [max_eq_left (by linarith), mul_zero]
    exact (bdist_eq_zero_iff _).mpr (expand_mem_boundary_of_bdist_le u h)
  · rw [max_eq_right (by linarith)]
    exact bdist_expand_eq u (le_of_lt h)

theorem bdist_expand_le_of_lt (u : I^N) (h : bdist u < 3 / 8) : bdist (expand u) < 1 / 4 := by
  rw [bdist_expand_eq_max]
  rcases le_or_gt (bdist u) (1 / 4) with h' | h'
  · rw [max_eq_left (by linarith), mul_zero]; norm_num
  · rw [max_eq_right (by linarith)]; linarith

theorem bdist_expand_le_of_le (u : I^N) (h : bdist u ≤ 3 / 8) : bdist (expand u) ≤ 1 / 4 := by
  rw [bdist_expand_eq_max]
  rcases le_or_gt (bdist u) (1 / 4) with h' | h'
  · rw [max_eq_left (by linarith), mul_zero]; norm_num
  · rw [max_eq_right (by linarith)]; linarith

theorem expand_expand_mem_boundary (u : I^N) (h : bdist u ≤ 3 / 8) :
    expand (expand u) ∈ Cube.boundary N :=
  expand_mem_boundary_of_bdist_le (expand u) (bdist_expand_le_of_le u h)

/-- Pointwise description of the doubly pinched loop, outer shell case. -/
theorem pinch_symm_pinch_outer {y z : Y} (p : Path y z) (w : Ω^ N Y y) (u : I^N)
    (h : bdist u < 1 / 4) :
    pinchFun (N := N) p.symm (pinch (N := N) p w) u
      = p (Set.projIcc (0 : ℝ) 1 zero_le_one (updownFun (bdist u))) := by
  have hmem : updownFun (bdist u) ∈ Set.Icc (0 : ℝ) 1 :=
    updownFun_mem (bdist_nonneg u) (by linarith)
  have hmem' : (4 * bdist u) ∈ Set.Icc (0 : ℝ) 1 := by
    rw [← updownFun_le (le_of_lt h)]; exact hmem
  rw [pinchFun, if_neg (not_le.mpr h), Path.symm_apply, Function.comp_apply]
  refine congrArg p ?_
  apply Subtype.ext
  rw [sigma_val, shparam_val (le_of_lt h), updownFun_le (le_of_lt h),
    Set.projIcc_of_mem zero_le_one hmem']
  ring

/-- Pointwise description of the doubly pinched loop, first inner layer. -/
theorem pinch_symm_pinch_middle {y z : Y} (p : Path y z) (w : Ω^ N Y y) (u : I^N)
    (h1 : 1 / 4 ≤ bdist u) (h2 : bdist u < 3 / 8) :
    pinchFun (N := N) p.symm (pinch (N := N) p w) u
      = p (Set.projIcc (0 : ℝ) 1 zero_le_one (updownFun (bdist u))) := by
  have h3 : bdist (expand u) < 1 / 4 := bdist_expand_le_of_lt u h2
  have hmem : updownFun (bdist u) ∈ Set.Icc (0 : ℝ) 1 :=
    updownFun_mem (bdist_nonneg u) (le_of_lt h2)
  have hmem' : (3 - 8 * bdist u) ∈ Set.Icc (0 : ℝ) 1 := by
    rw [← updownFun_ge h1]; exact hmem
  rw [pinchFun, if_pos h1, pinch_apply, pinchFun, if_neg (not_le.mpr h3)]
  refine congrArg p ?_
  apply Subtype.ext
  rw [shparam_val (u := expand u) (le_of_lt h3), bdist_expand_eq_max, max_eq_right (by linarith),
    updownFun_ge h1, Set.projIcc_of_mem zero_le_one hmem']
  ring

/-- Pointwise description of the doubly pinched loop, inner region. -/
theorem pinch_symm_pinch_inner {y z : Y} (p : Path y z) (w : Ω^ N Y y) (u : I^N)
    (h : 3 / 8 ≤ bdist u) :
    pinchFun (N := N) p.symm (pinch (N := N) p w) u = w (expand (expand u)) := by
  have h1 : (1 / 4 : ℝ) ≤ bdist u := by linarith
  have hge : (1 / 4 : ℝ) ≤ bdist (expand u) := by
    rw [bdist_expand_eq_max, max_eq_right (by linarith)]; linarith
  rw [pinchFun, if_pos h1, pinch_apply, pinchFun, if_pos hge]

theorem pinchFun_symm_pinch {y z : Y} (p : Path y z) (w : Ω^ N Y y) (u : I^N) :
    pinchFun (N := N) p.symm (pinch (N := N) p w) u
      = if 3 / 8 ≤ bdist u then w (expand (expand u))
        else p (Set.projIcc (0 : ℝ) 1 zero_le_one (updownFun (bdist u))) := by
  rcases lt_or_ge (bdist u) (3 / 8) with h | h
  · rw [if_neg (not_le.mpr h)]
    rcases lt_or_ge (bdist u) (1 / 4) with h4 | h4
    · exact pinch_symm_pinch_outer p w u h4
    · exact pinch_symm_pinch_middle p w u h4 h
  · rw [if_pos h]
    exact pinch_symm_pinch_inner p w u h

/-- Precomposing a loop with the rescaling `expand` does not change its homotopy class. -/
theorem rescale_homotopic {y : Y} (w : Ω^ N Y y) :
    GenLoop.Homotopic (innerGraph (ContinuousMap.id Y) (N := N) w) w := by
  refine ⟨⟨⟨fun q : I × I^N => w (sigmadef (q.1 : ℝ) q.2), ?_⟩, ?_, ?_⟩, ?_⟩
  · exact w.1.continuous.comp continuous_sigmadef
  · intro u
    show w (sigmadef ((0 : I) : ℝ) u) = innerGraph (ContinuousMap.id Y) (N := N) w u
    rw [coe_zero_I, sigmadef_zero]
    rfl
  · intro u
    show w (sigmadef ((1 : I) : ℝ) u) = w u
    rw [coe_one_I, sigmadef_one]
  · intro r u hu
    show w (sigmadef (r : ℝ) u) = innerGraph (ContinuousMap.id Y) (N := N) w u
    rw [GenLoop.boundary w (sigmadef (r : ℝ) u) (sigmadef_mem_boundary r.2.1 r.2.2 hu)]
    exact (innerGraph_apply_of_shell (ContinuousMap.id Y) w u
      (by rw [(bdist_eq_zero_iff u).mpr hu]; norm_num)).symm

/-- The first stage: contracting the shell of the doubly pinched loop. -/
theorem pinch_symm_pinch_stage {y z : Y} (p : Path y z) (w : Ω^ N Y y) :
    GenLoop.Homotopic (pinch (N := N) p.symm (pinch (N := N) p w))
      (innerGraph (ContinuousMap.id Y) (N := N)
        (innerGraph (ContinuousMap.id Y) (N := N) w)) := by
  refine ⟨⟨⟨fun q : I × I^N =>
      if (3 / 8 : ℝ) ≤ bdist q.2 then w (expand (expand q.2))
      else p (Set.projIcc (0 : ℝ) 1 zero_le_one
        ((1 - (q.1 : ℝ)) * updownFun (bdist q.2))), ?_⟩, ?_, ?_⟩, ?_⟩
  · have hφ : Continuous fun q : I × I^N => (1 - (q.1 : ℝ)) * updownFun (bdist q.2) :=
      (continuous_const.sub (continuous_subtype_val.comp continuous_fst)).mul
        (continuous_updownFun.comp (continuous_bdist.comp continuous_snd))
    refine Continuous.if_le (f' := fun q : I × I^N => w (expand (expand q.2)))
      (g' := fun q : I × I^N => p (Set.projIcc (0 : ℝ) 1 zero_le_one
        ((1 - (q.1 : ℝ)) * updownFun (bdist q.2))))
      (f := fun _ : I × I^N => (3 / 8 : ℝ)) (g := fun q : I × I^N => bdist q.2)
      ?_ ?_ continuous_const (continuous_bdist.comp continuous_snd) ?_
    · exact w.1.continuous.comp (expand.continuous.comp (expand.continuous.comp continuous_snd))
    · exact p.continuous.comp (continuous_projIcc.comp hφ)
    · intro q hq
      have hb : bdist q.2 = 3 / 8 := hq.symm
      have h0 : updownFun (bdist q.2) = 0 := by
        rw [hb, updownFun_ge (by norm_num : (1 : ℝ) / 4 ≤ 3 / 8)]; norm_num
      rw [h0, mul_zero, projIcc_of_le_zero (le_refl 0), Path.source,
        GenLoop.boundary w (expand (expand q.2)) (expand_expand_mem_boundary q.2 (le_of_eq hb))]
  · intro u
    show (if (3 / 8 : ℝ) ≤ bdist u then w (expand (expand u))
      else p (Set.projIcc (0 : ℝ) 1 zero_le_one ((1 - ((0 : I) : ℝ)) * updownFun (bdist u))))
      = pinchFun (N := N) p.symm (pinch (N := N) p w) u
    rw [show (1 - ((0 : I) : ℝ)) = 1 by rw [coe_zero_I]; ring, one_mul]
    rw [pinchFun_symm_pinch]
  · intro u
    show (if (3 / 8 : ℝ) ≤ bdist u then w (expand (expand u))
      else p (Set.projIcc (0 : ℝ) 1 zero_le_one ((1 - ((1 : I) : ℝ)) * updownFun (bdist u))))
      = innerGraph (ContinuousMap.id Y) (N := N) (innerGraph (ContinuousMap.id Y) (N := N) w) u
    rw [show (1 - ((1 : I) : ℝ)) = 0 by rw [coe_one_I]; ring, zero_mul,
      projIcc_of_le_zero (le_refl 0), Path.source]
    by_cases h : (3 / 8 : ℝ) ≤ bdist u
    · rw [if_pos h]; rfl
    · rw [if_neg h]
      exact (GenLoop.boundary w (expand (expand u))
        (expand_expand_mem_boundary u (le_of_lt (not_le.mp h)))).symm
  · intro r u hu
    show (if (3 / 8 : ℝ) ≤ bdist u then w (expand (expand u))
      else p (Set.projIcc (0 : ℝ) 1 zero_le_one ((1 - (r : ℝ)) * updownFun (bdist u))))
      = pinchFun (N := N) p.symm (pinch (N := N) p w) u
    have h0 : bdist u = 0 := (bdist_eq_zero_iff u).mpr hu
    rw [if_neg (by rw [h0]; norm_num), pinchFun_symm_pinch,
      if_neg (by rw [h0]; norm_num), h0, updownFun_le (by norm_num)]
    simp only [mul_zero, projIcc_of_le_zero (le_refl (0 : ℝ)), Path.source]

/-- **`transport p.symm` inverts `transport p`.** -/
theorem pinch_symm_pinch {y z : Y} (p : Path y z) (w : Ω^ N Y y) :
    GenLoop.Homotopic (pinch (N := N) p.symm (pinch (N := N) p w)) w :=
  (pinch_symm_pinch_stage p w).trans ((rescale_homotopic _).trans (rescale_homotopic w))

/-- The transport along `p.symm` is a left inverse of the transport along `p`. -/
theorem transport_symm_apply {y z : Y} (p : Path y z) (a : HomotopyGroup N Y y) :
    transport (N := N) p.symm (transport (N := N) p a) = a := by
  induction a using Quotient.inductionOn with
  | h w =>
    rw [transport_mk, transport_mk]
    exact Quotient.sound (pinch_symm_pinch p w)

/-- The transport along `p` is a left inverse of the transport along `p.symm`. -/
theorem transport_symm_apply' {y z : Y} (p : Path y z) (a : HomotopyGroup N Y z) :
    transport (N := N) p (transport (N := N) p.symm a) = a := by
  induction a using Quotient.inductionOn with
  | h w =>
    rw [transport_mk, transport_mk]
    exact Quotient.sound (by
      have h := pinch_symm_pinch (p := p.symm) (y := z) (z := y) (w := w)
      rwa [Path.symm_symm] at h)

end Invert


end Finite

end Pinch

end Work.Stems
