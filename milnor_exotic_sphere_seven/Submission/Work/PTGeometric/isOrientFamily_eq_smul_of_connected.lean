import Mathlib
import Submission.Work.Orient.Defs
import Submission.Work.Orient.Closed
import Submission.Work.ThomBordism.isCoordBall_restrict_iso_free

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 400000

/-!
# Two orientation families on a connected manifold differ by a global sign

`Work.Orient.IsOrientFamily n W γ` is an orientation of a charted space `W` in the form of a
locally consistent family of local generators `γ x ∈ H_n(W, W∖{x})`.  This file proves that on a
**connected** `W` any two such families differ by one global sign:

`Work.PTGeometric.isOrientFamily_eq_smul_of_connected` :
`∃ ε : ℤ, (ε = 1 ∨ ε = -1) ∧ ∀ x, γ' x = ε • γ x`.

The mathematics is the standard torsor structure of orientations: the local group is infinite
cyclic, so at every point the two generators differ by `±1`; the subset of `W` where the sign is
`+1` is both open (the generators of a coordinate ball are the restrictions of a *single* class of
`H_n(W, W∖K)`, and the restriction map is injective) and closed (its complement is the set where
`γ' = -γ`), so connectedness makes the sign constant.

Ingredients:

* `nonempty_locH_iso_int` — the local group of a charted space is `ℤ`, **without compactness**
  (the compactness-free form of `Work.Cohomology.localHomology` in the `Work.Orient.LocH`
  spelling);
* `ne_zero_of_span_eq_top_locH` — a single generator of the local group is nonzero;
* `exists_pm_one_smul_eq_of_span_eq_top` — two generators of a cyclic `ℤ`-module differ by `±1`;
* `injective_resRelH_isCoordBall`, `surjective_resRelH_isCoordBall` — the restriction
  `H_n(W, W∖K) → H_n(W, W∖{x})` out of a coordinate ball is an isomorphism, without compactness
  (the compactness-free form of `Work.ThomBordism.IsCoordBall.isIso_restrict`);
* `exists_pm_one_smul_of_isOrientFamily_ball` — the sign is constant on a coordinate ball.
-/

set_option autoImplicit false
set_option maxHeartbeats 1600000

open CategoryTheory AlgebraicTopology CategoryTheory.Limits
open scoped Topology

namespace Work.PTGeometric

noncomputable section

variable {n : ℕ}

/-! ## Small module-theoretic facts about cyclic `ℤ`-modules -/

/-- **The local homology group of a charted space is infinite cyclic.**

This is `Work.Cohomology.localHomology`, transported to the `Work.Orient.LocH` spelling (the
excluded sets `{x}ᶜ` and `{y | y ≠ x}` are the same).  Unlike `Work.ThomBordism.RelH_point_iso`
it needs **no compactness** hypothesis on `W`. -/
theorem nonempty_locH_iso_int (n : ℕ) (hn : 1 ≤ n) (W : TopCat)
    [ChartedSpace (EuclideanSpace ℝ (Fin n)) W] (x : W) :
    Nonempty (Work.Orient.LocH W n x ≅ ModuleCat.of ℤ ℤ) := by
  have hTop : (Work.Cohomology.relChains (TopCat.of (W : Type)) ({x} : Set (W : Type))ᶜ).homology n
      = (Work.Cohomology.relChains W ({x} : Set W)ᶜ).homology n := rfl
  have hh : ({x} : Set (W : Type))ᶜ = {y : (W : Type) | y ≠ x} := by ext y; simp
  obtain ⟨e0⟩ := Work.Cohomology.localHomology n hn (W : Type) x
  refine ⟨(eqToIso hTop).symm.trans ((eqToIso (congrArg (fun S : Set (W : Type) =>
    (Work.Cohomology.relChains (TopCat.of (W : Type)) S).homology n) hh)).trans e0)⟩

/-- **A generator of a nontrivial cyclic `ℤ`-module is nonzero.** -/
theorem ne_zero_of_span_eq_top_locH (n : ℕ) (hn : 1 ≤ n) (W : TopCat)
    [ChartedSpace (EuclideanSpace ℝ (Fin n)) W] {x : W}
    {u : Work.Orient.LocH W n x}
    (hu : Submodule.span ℤ ({u} : Set (Work.Orient.LocH W n x)) = ⊤) : u ≠ 0 := by
  intro hu0
  obtain ⟨e⟩ := nonempty_locH_iso_int n hn W x
  have hsub : Subsingleton (Work.Orient.LocH W n x) := by
    have hbot : Submodule.span ℤ ({u} : Set (Work.Orient.LocH W n x)) = ⊥ := by
      rw [hu0]
      exact Submodule.span_singleton_eq_bot.mpr rfl
    refine ⟨fun a b => ?_⟩
    have ha : a ∈ (⊥ : Submodule ℤ (Work.Orient.LocH W n x)) := by
      rw [← hbot, hu]; exact Submodule.mem_top
    have hb : b ∈ (⊥ : Submodule ℤ (Work.Orient.LocH W n x)) := by
      rw [← hbot, hu]; exact Submodule.mem_top
    rw [Submodule.mem_bot] at ha hb
    rw [ha, hb]
  have e' : Work.Orient.LocH W n x ≃ₗ[ℤ] ℤ := e.toLinearEquiv
  have h1 : (1 : ℤ) = 0 := by
    have h := Subsingleton.elim (e'.symm 1) (e'.symm 0)
    simpa using congrArg (fun z => e' z) h
  exact one_ne_zero h1

/-- **Two generators of a cyclic `ℤ`-module differ by `±1`.** -/
theorem exists_pm_one_smul_eq_of_span_eq_top {A : Type*} [AddCommGroup A] [Module ℤ A]
    (e : A ≃ₗ[ℤ] ℤ) {u v : A}
    (hu : Submodule.span ℤ ({u} : Set A) = ⊤)
    (hv : Submodule.span ℤ ({v} : Set A) = ⊤) :
    ∃ ε : ℤ, (ε = 1 ∨ ε = -1) ∧ v = ε • u := by
  obtain ⟨m, hm⟩ := Submodule.mem_span_singleton.mp (show v ∈ Submodule.span ℤ ({u} : Set A) from by
    rw [hu]; exact Submodule.mem_top)
  obtain ⟨k, hk⟩ := Submodule.mem_span_singleton.mp (show u ∈ Submodule.span ℤ ({v} : Set A) from by
    rw [hv]; exact Submodule.mem_top)
  have hm' : m • u = v := (int_smul_eq_zsmul (inferInstance : Module ℤ A) m u).symm.trans hm
  have hk' : k • v = u := (int_smul_eq_zsmul (inferInstance : Module ℤ A) k v).symm.trans hk
  obtain ⟨w, hw⟩ : ∃ w : A, e w = 1 := ⟨e.symm 1, by simp⟩
  obtain ⟨c, hc⟩ := Submodule.mem_span_singleton.mp (show w ∈ Submodule.span ℤ ({u} : Set A) from by
    rw [hu]; exact Submodule.mem_top)
  have hc' : c • u = w := (int_smul_eq_zsmul (inferInstance : Module ℤ A) c u).symm.trans hc
  have heu : e u ≠ 0 := by
    intro h0
    have h1 : (1 : ℤ) = 0 := by
      have h2 : (1 : ℤ) = c * e u := by
        rw [← hw, ← hc', map_zsmul, zsmul_eq_mul, Int.cast_id]
      rw [h2, h0, mul_zero]
    exact one_ne_zero h1
  have hkm : k * m = 1 := by
    have h1 : (k * m) • u = u := by rw [mul_zsmul, hm', hk']
    have h2 : (k * m) * e u = e u := by
      have h2' : (k * m) • e u = e u := by
        have := congrArg (fun z => e z) h1
        rwa [map_zsmul] at this
      simpa [zsmul_eq_mul, Int.cast_id] using h2'
    have h3 : (k * m - 1) * e u = 0 := by rw [sub_mul, one_mul, h2, sub_self]
    rcases mul_eq_zero.mp h3 with h | h
    · omega
    · exact absurd h heu
  rcases Int.eq_one_or_neg_one_of_mul_eq_one' hkm with ⟨-, h⟩ | ⟨-, h⟩
  · exact ⟨m, Or.inl h, hm'.symm⟩
  · exact ⟨m, Or.inr h, hm'.symm⟩

/-! ## The restriction map out of a coordinate ball, without compactness -/

/-- Injectivity of the restriction `H_n(W, W∖K) → H_n(W, W∖{x})` for a coordinate ball `K ∋ x`.
No compactness of `W` is needed. -/
theorem injective_resRelH_isCoordBall {W : TopCat} [T2Space W]
    [ChartedSpace (EuclideanSpace ℝ (Fin n)) W] {K : Set W}
    (hn : 1 ≤ n) (hK : Work.ThomBordism.IsCoordBall n W K) {x : W} (hx : x ∈ K) :
    Function.Injective (Work.Orient.resRelH W n (Set.singleton_subset_iff.mpr hx)) := by
  have hIso := Work.ThomBordism.isCoordBall_restrict_iso_free (M := W) hn hK hx
  intro u v huv
  exact (ModuleCat.mono_iff_injective (HomologicalComplex.homologyMap
    (Work.Cohomology.relCokerMap W Kᶜ ({x} : Set W)ᶜ
      (Set.compl_subset_compl.mpr (Set.singleton_subset_iff.mpr hx))) n)).mp inferInstance huv

/-- Surjectivity of the restriction `H_n(W, W∖K) → H_n(W, W∖{x})` for a coordinate ball `K ∋ x`. -/
theorem surjective_resRelH_isCoordBall {W : TopCat} [T2Space W]
    [ChartedSpace (EuclideanSpace ℝ (Fin n)) W] {K : Set W}
    (hn : 1 ≤ n) (hK : Work.ThomBordism.IsCoordBall n W K) {x : W} (hx : x ∈ K) :
    Function.Surjective (Work.Orient.resRelH W n (Set.singleton_subset_iff.mpr hx)) := by
  have hIso := Work.ThomBordism.isCoordBall_restrict_iso_free (M := W) hn hK hx
  intro y
  exact (ModuleCat.epi_iff_surjective (HomologicalComplex.homologyMap
    (Work.Cohomology.relCokerMap W Kᶜ ({x} : Set W)ᶜ
      (Set.compl_subset_compl.mpr (Set.singleton_subset_iff.mpr hx))) n)).mp inferInstance y

/-! ## Two orientation families agree up to sign, locally -/

/-- **On a coordinate ball, two orientation families differ by a constant sign.** -/
theorem exists_pm_one_smul_of_isOrientFamily_ball (hn : 1 ≤ n) (W : TopCat) [T2Space W]
    [ChartedSpace (EuclideanSpace ℝ (Fin n)) W]
    {γ γ' : (x : W) → Work.Orient.LocH W n x}
    (hγ : Work.Orient.IsOrientFamily n W γ) (hγ' : Work.Orient.IsOrientFamily n W γ')
    {K : Set W} (hK : Work.ThomBordism.IsCoordBall n W K) {x : W} (hx : x ∈ K) :
    ∃ ε : ℤ, (ε = 1 ∨ ε = -1) ∧ ∀ y ∈ K, γ' y = ε • γ y := by
  obtain ⟨a, ha⟩ := hγ.2 K hK
  obtain ⟨b, hb⟩ := hγ'.2 K hK
  let R : Work.ThomBordism.RelH W n K →ₗ[ℤ] Work.Orient.LocH W n x :=
    Work.Orient.resRelH W n (Set.singleton_subset_iff.mpr hx)
  have hinj : Function.Injective R :=
    injective_resRelH_isCoordBall (n := n) (W := W) hn hK hx
  have hsurj : Function.Surjective R :=
    surjective_resRelH_isCoordBall (n := n) (W := W) hn hK hx
  have hRa : R a = γ x := ha x hx
  have hRb : R b = γ' x := hb x hx
  -- generation transfers back to the coordinate ball: `R` is injective and
  -- `Submodule.map R (span {a}) = span {R a} = span {γ x} = ⊤`
  have hgen_a : Submodule.span ℤ ({a} : Set (Work.ThomBordism.RelH W n K)) = ⊤ := by
    rw [Submodule.eq_top_iff']
    intro v
    have hmap : Submodule.map R (Submodule.span ℤ ({a} : Set (Work.ThomBordism.RelH W n K)))
        = ⊤ := by
      rw [Submodule.map_span, Set.image_singleton, hRa, hγ.1 x]
    have hv : R v ∈ Submodule.map R (Submodule.span ℤ
        ({a} : Set (Work.ThomBordism.RelH W n K))) := by
      rw [hmap]
      exact Submodule.mem_top
    obtain ⟨w, hw, hwv⟩ := Submodule.mem_map.mp hv
    rwa [hinj hwv] at hw
  have hgen_b : Submodule.span ℤ ({b} : Set (Work.ThomBordism.RelH W n K)) = ⊤ := by
    rw [Submodule.eq_top_iff']
    intro v
    have hmap : Submodule.map R (Submodule.span ℤ ({b} : Set (Work.ThomBordism.RelH W n K)))
        = ⊤ := by
      rw [Submodule.map_span, Set.image_singleton, hRb, hγ'.1 x]
    have hv : R v ∈ Submodule.map R (Submodule.span ℤ
        ({b} : Set (Work.ThomBordism.RelH W n K))) := by
      rw [hmap]
      exact Submodule.mem_top
    obtain ⟨w, hw, hwv⟩ := Submodule.mem_map.mp hv
    rwa [hinj hwv] at hw
  -- the isomorphism `H_n(W, W∖K) ≅ ℤ`
  have e0 : Work.Orient.LocH W n x ≃ₗ[ℤ] ℤ :=
    (Classical.choice (nonempty_locH_iso_int n hn W x)).toLinearEquiv
  have eK : Work.ThomBordism.RelH W n K ≃ₗ[ℤ] ℤ :=
    (LinearEquiv.ofBijective R ⟨hinj, hsurj⟩).trans e0
  obtain ⟨ε, hε, hb_eq⟩ := exists_pm_one_smul_eq_of_span_eq_top eK hgen_a hgen_b
  refine ⟨ε, hε, fun y hy => ?_⟩
  have h := congrArg (Work.Orient.resRelH W n (Set.singleton_subset_iff.mpr hy)) hb_eq
  rw [show (Work.Orient.resRelH W n (Set.singleton_subset_iff.mpr hy)) (ε • a)
      = ε • (Work.Orient.resRelH W n (Set.singleton_subset_iff.mpr hy)) a
      from map_zsmul _ ε a] at h
  rw [hb y hy, ha y hy] at h
  exact h

/-! ## The main theorem -/

theorem isOrientFamily_eq_smul_of_connected {n : ℕ} (hn : 1 ≤ n) (W : TopCat) [T2Space W]
    [ChartedSpace (EuclideanSpace ℝ (Fin n)) W] [ConnectedSpace W]
    {γ γ' : (x : W) → Work.Orient.LocH W n x}
    (hγ : Work.Orient.IsOrientFamily n W γ) (hγ' : Work.Orient.IsOrientFamily n W γ') :
    ∃ ε : ℤ, (ε = 1 ∨ ε = -1) ∧ ∀ x : W, γ' x = ε • γ x := by
  classical
  set S : Set W := {x : W | γ' x = γ x} with hS
  set T : Set W := {x : W | γ' x = -γ x} with hT
  -- every point lies in `S` or in `T`
  have hcover : S ∪ T = Set.univ := by
    ext x
    simp only [hS, hT, Set.mem_union, Set.mem_ofPred_eq, Set.mem_univ, iff_true]
    obtain ⟨K, hK, hxK, -⟩ := Work.Orient.exists_isCoordBall_mem_nhds n W x
    obtain ⟨ε, hε, hball⟩ := exists_pm_one_smul_of_isOrientFamily_ball hn W hγ hγ' hK hxK
    have hxε : γ' x = ε • γ x := hball x hxK
    rcases hε with h1 | h1
    · left
      rw [hxε, h1]
      simp
    · right
      rw [hxε, h1]
      simp
  -- `S` is open
  have hSopen : IsOpen S := by
    rw [isOpen_iff_mem_nhds]
    intro x hxS
    have hxS' : γ' x = γ x := hxS
    obtain ⟨K, hK, hxK, hKn⟩ := Work.Orient.exists_isCoordBall_mem_nhds n W x
    obtain ⟨a, ha⟩ := hγ.2 K hK
    obtain ⟨b, hb⟩ := hγ'.2 K hK
    let Rx : Work.ThomBordism.RelH W n K →ₗ[ℤ] Work.Orient.LocH W n x :=
      Work.Orient.resRelH W n (Set.singleton_subset_iff.mpr hxK)
    have hinj : Function.Injective Rx :=
      injective_resRelH_isCoordBall (n := n) (W := W) hn hK hxK
    have hbX : Rx b = γ' x := hb x hxK
    have haX : Rx a = γ x := ha x hxK
    have hzero : b - a = 0 := by
      apply hinj
      rw [map_sub, hbX, haX, map_zero, hxS', sub_self]
    filter_upwards [hKn] with y hy
    let Ry : Work.ThomBordism.RelH W n K →ₗ[ℤ] Work.Orient.LocH W n y :=
      Work.Orient.resRelH W n (Set.singleton_subset_iff.mpr hy)
    have hbY : Ry b = γ' y := hb y hy
    have haY : Ry a = γ y := ha y hy
    have hzeroY : Ry b - Ry a = 0 := by rw [← map_sub, hzero, map_zero]
    show γ' y = γ y
    have h : γ' y - γ y = 0 := by rw [← hbY, ← haY]; exact hzeroY
    exact sub_eq_zero.mp h
  -- `T` is open
  have hTopen : IsOpen T := by
    rw [isOpen_iff_mem_nhds]
    intro x hxT
    have hxT' : γ' x = -γ x := hxT
    obtain ⟨K, hK, hxK, hKn⟩ := Work.Orient.exists_isCoordBall_mem_nhds n W x
    obtain ⟨a, ha⟩ := hγ.2 K hK
    obtain ⟨b, hb⟩ := hγ'.2 K hK
    let Rx : Work.ThomBordism.RelH W n K →ₗ[ℤ] Work.Orient.LocH W n x :=
      Work.Orient.resRelH W n (Set.singleton_subset_iff.mpr hxK)
    have hinj : Function.Injective Rx :=
      injective_resRelH_isCoordBall (n := n) (W := W) hn hK hxK
    have hbX : Rx b = γ' x := hb x hxK
    have haX : Rx a = γ x := ha x hxK
    have hzero : b + a = 0 := by
      apply hinj
      rw [map_add, hbX, haX, map_zero, hxT', neg_add_cancel]
    filter_upwards [hKn] with y hy
    let Ry : Work.ThomBordism.RelH W n K →ₗ[ℤ] Work.Orient.LocH W n y :=
      Work.Orient.resRelH W n (Set.singleton_subset_iff.mpr hy)
    have hbY : Ry b = γ' y := hb y hy
    have haY : Ry a = γ y := ha y hy
    have hzeroY : Ry b + Ry a = 0 := by rw [← map_add, hzero, map_zero]
    show γ' y = -γ y
    exact eq_neg_of_add_eq_zero_left (by rw [← hbY, ← haY]; exact hzeroY)
  -- `S` and `T` are disjoint
  have hdisj : Disjoint S T := by
    rw [Set.disjoint_iff]
    intro x hx
    exfalso
    have hxS' : γ' x = γ x := hx.1
    have hxT' : γ' x = -γ x := hx.2
    have h1 : γ x = -γ x := hxS'.symm.trans hxT'
    have h2 : γ x + γ x = 0 := by
      nth_rewrite 1 [h1]
      rw [neg_add_cancel]
    have e0 : Work.Orient.LocH W n x ≃ₗ[ℤ] ℤ :=
      (Classical.choice (nonempty_locH_iso_int n hn W x)).toLinearEquiv
    have h3 : γ x = 0 := by
      have h4 : e0 (γ x) + e0 (γ x) = 0 := by rw [← map_add, h2, map_zero]
      have h5 : e0 (γ x) = 0 := by linarith
      exact e0.injective (by rw [h5, map_zero])
    exact ne_zero_of_span_eq_top_locH n hn W (hγ.1 x) h3
  -- connectedness finishes the proof
  have hpc := (isPreconnected_iff_subset_of_disjoint.mp (isPreconnected_univ (α := W)))
    S T hSopen hTopen (by rw [hcover]) (by
      rw [Set.univ_inter]
      exact Set.disjoint_iff_inter_eq_empty.mp hdisj)
  rcases hpc with hSall | hTall
  · refine ⟨1, Or.inl rfl, fun x => ?_⟩
    have hx : γ' x = γ x := hSall (Set.mem_univ x)
    rw [hx]
    simp
  · refine ⟨-1, Or.inr rfl, fun x => ?_⟩
    have hx : γ' x = -γ x := hTall (Set.mem_univ x)
    rw [hx]
    simp

end

end Work.PTGeometric
