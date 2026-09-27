import Mathlib
import Submission.Work.Drive.N2.exists_modelAdapted_levelFlow_v2
import Submission.Work.Drive.N2.modelFlowDefs
import Submission.Work.Drive.Morse

/-!
# The model-adapted level flow: the chart ODE clause

`Work.Drive.N2.exists_modelAdapted_levelFlow_v2` builds, for a compact surface with a morse chart
datum, a smooth flow `Φ` which raises `f` at unit speed off the model balls and on which the chart
radius `‖φ i ·‖` is monotone along the regions `C i`.  Its construction
(`Work.Drive.N2.exists_modelAdapted_levelFlow_of_bumps`) is the flow of a smooth compactly supported
ambient field on `ℝ ^ 5`, transported to the surface by a nearest-point retraction; inside the region
`C i` the field is *exactly* the model field of the chart `i`, so the chart coordinates of the orbit
solve the model ODE `u' = chartMult (r i) (‖u‖ ^ 2) • (s₁ i * u 0, s₂ i * u 1)`.

That last fact is derived inside `levelFlowAssembly.lean` (it is the first half of the proof of the
radius monotonicity) but is *discarded* from the conclusion.  This file re-exposes it:

* `exists_modelAdapted_levelFlow_of_bumps_chartODE` — the same assembly as
  `Work.Drive.N2.exists_modelAdapted_levelFlow_of_bumps`, with the chart ODE clause added to the
  conclusion (and the radius monotonicity kept);
* `exists_modelAdapted_levelFlow_chartODE` — the target statement, assembled from the same bump data
  as `Work.Drive.N2.exists_modelAdapted_levelFlow_v2`.

The chart ODE is what makes the box `{|u 0| ≤ a, |u 1| ≤ b}` orbit-convex
(`Work.Drive.N2.model_orbit_mem_box_Icc`), i.e. the confinement needed by the movie/blend route.
-/

namespace Work.Drive.N2

open scoped Manifold ContDiff Topology
open Set Function

set_option maxHeartbeats 1600000

variable {M : Type*} [TopologicalSpace M] [ChartedSpace (EuclideanSpace ℝ (Fin 2)) M]
  [IsManifold (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 2))) ((⊤ : ℕ∞) : WithTop ℕ∞) M]
  [T2Space M] [SecondCountableTopology M] [CompactSpace M]

theorem exists_modelAdapted_levelFlow_of_bumps_chartODE
    (A : AmbSetup M) {ι : Type*} [Fintype ι]
    (f : M → ℝ) (hf : ContMDiff (𝓡 2) (modelWithCornersSelf ℝ ℝ) ((⊤ : ℕ∞) : WithTop ℕ∞) f)
    (x : ι → M) (φ : ι → OpenPartialHomeomorph M (EuclideanSpace ℝ (Fin 2)))
    (s₁ s₂ r : ι → ℝ) (hr : ∀ i, 0 < r i)
    (hsrc : ∀ i, x i ∈ (φ i).source) (hcen : ∀ i, φ i (x i) = 0)
    (hsgn : ∀ i, (s₁ i = 1 ∨ s₁ i = -1) ∧ (s₂ i = 1 ∨ s₂ i = -1))
    (hval : ∀ i y, y ∈ (φ i).source → f y = f (x i) + chartQ (φ i) (s₁ i) (s₂ i) y)
    (hφ : ∀ i, ContMDiffOn (𝓡 2) (𝓡 2) ((⊤ : ℕ∞) : WithTop ℕ∞) (fun y => φ i y) (φ i).source)
    (hφ' : ∀ i, ContMDiffOn (𝓡 2) (𝓡 2) ((⊤ : ℕ∞) : WithTop ℕ∞)
      (fun u => (φ i).symm u) (φ i).target)
    (hdisj : ∀ i j, i ≠ j → Disjoint (φ i).source (φ j).source)
    (C : ι → Set M) (hCsub : ∀ i, C i ⊆ (φ i).source)
    (hCcl : ∀ i, IsCompact (closure (C i)) ∧ closure (C i) ⊆ (φ i).source)
    (hCball : ∀ i, modelBall (φ i) (r i) ⊆ C i)
    (hCcrit : ∀ y, (∀ i, y ∉ C i) → ¬ Work.Drive.Morse.IsCritical f y)
    (χd : EuclideanSpace ℝ (Fin 5) → ℝ) (hχd_sm : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) χd)
    (hχd_supp : tsupport χd ⊆ A.U)
    (hχd_int : Set.range A.e ⊆ interior {z | χd z = 1})
    (χi : ι → EuclideanSpace ℝ (Fin 5) → ℝ) (hχi_sm : ∀ i, ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (χi i))
    (hχi_cs : ∀ i, HasCompactSupport (χi i))
    (hχi_supp : ∀ i, tsupport (χi i) ⊆ modelRegion A (φ i) ∩ interior {z | χd z = 1})
    (hχi_one : ∀ i, A.e '' closure (C i) ⊆ interior {z | χi i z = 1})
    (χf : EuclideanSpace ℝ (Fin 5) → ℝ) (hχf_sm : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) χf)
    (hχf_cs : HasCompactSupport χf)
    (hχf_supp : tsupport χf ⊆ {z | auxField (fun z => χd z • A.e (A.π z))
        (fun z => χd z • f (A.π z)) z ≠ 0} ∩ interior {z | χd z = 1})
    (hχf_one : A.e '' {y : M | (∑ i, χi i (A.e y)) ≠ 1} ⊆ interior {z | χf z = 1}) :
    ∃ Φ : ℝ × M → M,
      ContMDiff ((modelWithCornersSelf ℝ ℝ).prod (𝓡 2)) (𝓡 2) ((⊤ : ℕ∞) : WithTop ℕ∞) Φ ∧
      (∀ y, Φ (0, y) = y) ∧
      (∀ a b y, Φ (a, Φ (b, y)) = Φ (a + b, y)) ∧
      (∀ (y : M) (t : ℝ), (∀ i, y ∉ modelBall (φ i) (r i)) →
        (∀ u ∈ Set.Icc (min 0 t) (max 0 t), ∀ i, Φ (u, y) ∉ modelBall (φ i) (r i)) →
        f (Φ (t, y)) = f y + t) ∧
      (∀ (i : ι) (y : M) (t₁ t₂ : ℝ),
        (∀ u ∈ Set.Icc (min t₁ t₂) (max t₁ t₂), Φ (u, y) ∈ C i ∧ 0 < ‖φ i (Φ (u, y))‖) →
        |chartQ (φ i) (s₁ i) (s₂ i) (Φ (t₁, y))| <
          |chartQ (φ i) (s₁ i) (s₂ i) (Φ (t₂, y))| →
        ‖φ i (Φ (t₁, y))‖ < ‖φ i (Φ (t₂, y))‖) ∧
      (∀ (i : ι) (y : M) (t : ℝ),
        (∀ u ∈ Set.Icc (min 0 t) (max 0 t), Φ (u, y) ∈ C i) →
        HasDerivAt (fun σ : ℝ => φ i (Φ (σ, y)) 0)
          (chartMult (r i) (‖φ i (Φ (t, y))‖ ^ 2) * (s₁ i * φ i (Φ (t, y)) 0)) t ∧
        HasDerivAt (fun σ : ℝ => φ i (Φ (σ, y)) 1)
          (chartMult (r i) (‖φ i (Φ (t, y))‖ ^ 2) * (s₂ i * φ i (Φ (t, y)) 1)) t) := by
  classical
  set Ed : EuclideanSpace ℝ (Fin 5) → EuclideanSpace ℝ (Fin 5) :=
    fun z => χd z • A.e (A.π z) with hEd_def
  set Gd : EuclideanSpace ℝ (Fin 5) → ℝ := fun z => χd z • f (A.π z) with hGd_def
  have hEd_sm : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) Ed :=
    (contDiff_damped_E_G A χd hχd_sm hχd_supp f hf).1
  have hGd_sm : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) Gd :=
    (contDiff_damped_E_G A χd hχd_sm hχd_supp f hf).2
  have hχd_e : ∀ y : M, χd (A.e y) = 1 := fun y => by
    simpa using interior_subset (s := {w | χd w = 1}) (hχd_int ⟨y, rfl⟩)
  -- the field
  set Y : EuclideanSpace ℝ (Fin 5) → EuclideanSpace ℝ (Fin 5) :=
    (∑ i, (χi i) • modelField A (φ i) (chartMult (r i)) (s₁ i) (s₂ i))
      + (fun z => (1 - ∑ i, χi i z)) • levelField Ed Gd χf with hY_def
  have hLF_spec := levelField_spec Ed Gd χf hEd_sm hGd_sm
  have hLF_sm : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (levelField Ed Gd χf) :=
    (contDiff_levelField Ed Gd χf hEd_sm hGd_sm hχf_sm hχf_cs
      (hχf_supp.trans inter_subset_left)).1
  have hLF_cs : HasCompactSupport (levelField Ed Gd χf) :=
    (contDiff_levelField Ed Gd χf hEd_sm hGd_sm hχf_sm hχf_cs
      (hχf_supp.trans inter_subset_left)).2
  have hsum_sm : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
      (∑ i, (χi i) • modelField A (φ i) (chartMult (r i)) (s₁ i) (s₂ i)) := by
    have hfun : (fun z : EuclideanSpace ℝ (Fin 5) => ∑ i, (χi i z) •
          modelField A (φ i) (chartMult (r i)) (s₁ i) (s₂ i) z)
        = (∑ i, (χi i) • modelField A (φ i) (chartMult (r i)) (s₁ i) (s₂ i)) := by
      funext z
      rw [Finset.sum_apply]
      exact Finset.sum_congr rfl fun i _ => (Pi.smul_apply' _ _ _).symm
    rw [← hfun]
    suffices h : ∀ s : Finset ι, ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
        (fun z : EuclideanSpace ℝ (Fin 5) =>
          ∑ i ∈ s, (χi i z) • modelField A (φ i) (chartMult (r i)) (s₁ i) (s₂ i) z) by
      simpa using h Finset.univ
    intro s
    induction s using Finset.induction_on with
    | empty => simpa using contDiff_const (c := (0 : EuclideanSpace ℝ (Fin 5)))
    | insert a s ha ih =>
        have h1 : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
            (fun z : EuclideanSpace ℝ (Fin 5) =>
              (χi a z) • modelField A (φ a) (chartMult (r a)) (s₁ a) (s₂ a) z) :=
          contDiff_smul_of_contDiffOn_aux (F := EuclideanSpace ℝ (Fin 5))
            (O := modelRegion A (φ a)) (g := χi a)
            (f := modelField A (φ a) (chartMult (r a)) (s₁ a) (s₂ a))
            (isOpen_modelRegion A (φ a) (hφ a)) (hχi_sm a)
            (contDiffOn_modelField A (φ a) (hφ a) (chartMult (r a))
              (chartMult_contDiff (r a) (hr a)) (s₁ a) (s₂ a))
            ((hχi_supp a).trans inter_subset_left)
        simp only [Finset.sum_insert ha]
        exact h1.add ih
  have hsum_cs : HasCompactSupport
      (∑ i, (χi i) • modelField A (φ i) (chartMult (r i)) (s₁ i) (s₂ i)) := by
    suffices h : ∀ s : Finset ι, HasCompactSupport
        (∑ i ∈ s, (χi i) • modelField A (φ i) (chartMult (r i)) (s₁ i) (s₂ i)) by
      simpa using h Finset.univ
    intro s
    induction s using Finset.induction_on with
    | empty => simpa using HasCompactSupport.zero
    | insert a s ha ih =>
        rw [Finset.sum_insert ha]
        exact ((hχi_cs a).smul_right).add ih
  have hY_sm : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) Y := by
    rw [hY_def]
    exact hsum_sm.add ((contDiff_const.sub (ContDiff.sum (f := fun i => χi i)
      (s := (Finset.univ : Finset ι)) fun i _ => hχi_sm i)).smul hLF_sm)
  have hY_cs : HasCompactSupport Y := by
    rw [hY_def]
    exact hsum_cs.add (hLF_cs.smul_left)
  -- vanishing of `Y` off the supports of the bumps
  have hY_eq_zero : ∀ z, (∀ i, z ∉ tsupport (χi i)) → z ∉ tsupport χf →
      {w : EuclideanSpace ℝ (Fin 5) | Y w = 0} ∈ 𝓝 z := by
    intro z hzi hzf
    have h1 : ∀ i, ∀ᶠ w in 𝓝 z, χi i w = 0 := fun i =>
      Filter.mem_of_superset ((isClosed_tsupport (χi i)).isOpen_compl.mem_nhds (hzi i))
        (fun w hw => Function.notMem_support.mp (fun h => hw (subset_tsupport (χi i) h)))
    have h2 : ∀ᶠ w in 𝓝 z, χf w = 0 :=
      Filter.mem_of_superset ((isClosed_tsupport χf).isOpen_compl.mem_nhds hzf)
        (fun w hw => Function.notMem_support.mp (fun h => hw (subset_tsupport χf h)))
    rw [hY_def]
    filter_upwards [Filter.eventually_all.mpr h1, h2] with w hw1 hw2
    have hs : (∑ i, (χi i) • modelField A (φ i) (chartMult (r i)) (s₁ i) (s₂ i)) w = 0 := by
      rw [Finset.sum_apply]
      exact Finset.sum_eq_zero fun i _ => by rw [Pi.smul_apply', hw1 i, zero_smul]
    have hψ : (1 - ∑ i, χi i w) = 1 := by
      rw [Finset.sum_eq_zero fun i _ => hw1 i, sub_zero]
    rw [Pi.add_apply, hs, zero_add]
    change (1 - ∑ i, χi i w) • levelField Ed Gd χf w = 0
    rw [hψ, one_smul, levelField, hw2, zero_smul]
  -- the topological support of `Y` lies in the interior of `{χd = 1}`
  have hY_tsup : tsupport Y ⊆ interior {z | χd z = 1} := by
    intro z hz
    by_contra hznot
    have hzi : ∀ i, z ∉ tsupport (χi i) := fun i hmem =>
      hznot (Set.subset_inter_iff.mp (hχi_supp i) |>.2 hmem)
    have hzf : z ∉ tsupport χf := fun hmem => hznot ((hχf_supp hmem).2)
    obtain ⟨u, hu_sub, hu_open, hzu⟩ := mem_nhds_iff.mp (hY_eq_zero z hzi hzf)
    have hsub : Function.support Y ⊆ uᶜ := by
      intro w hw
      simp only [Set.mem_compl_iff]
      intro hwu
      exact hw (hu_sub hwu)
    have hcl : closure (Function.support Y) ⊆ uᶜ := closure_minimal hsub hu_open.isClosed_compl
    exact hcl hz hzu
  -- the field is tangent to the image of `Ed`
  have hdEd_eq : ∀ z ∈ interior {z | χd z = 1},
      fderiv ℝ Ed z = fderiv ℝ (fun w => A.e (A.π w)) z := by
    intro z hz
    have hev : Ed =ᶠ[𝓝 z] fun w => A.e (A.π w) := by
      filter_upwards [isOpen_interior.mem_nhds hz] with w hw
      show χd w • A.e (A.π w) = A.e (A.π w)
      rw [interior_subset (s := {z | χd z = 1}) hw, one_smul]
    exact hev.fderiv_eq
  have hY_range : ∀ z, Y z ∈ (fderiv ℝ Ed z).range := by
    intro z
    by_cases hz : z ∈ tsupport Y
    · have hzint : z ∈ interior {z | χd z = 1} := hY_tsup hz
      have hmodel : ∀ i, modelField A (φ i) (chartMult (r i)) (s₁ i) (s₂ i) z
          ∈ (fderiv ℝ Ed z).range := by
        intro i
        rw [hdEd_eq z hzint]
        exact ⟨modelRaw A (φ i) (chartMult (r i)) (s₁ i) (s₂ i) z, rfl⟩
      have hfar : levelField Ed Gd χf z ∈ (fderiv ℝ Ed z).range := hLF_spec.2 z
      show ((∑ i, (χi i) • modelField A (φ i) (chartMult (r i)) (s₁ i) (s₂ i))
        + (fun z => (1 - ∑ i, χi i z)) • levelField Ed Gd χf) z ∈ (fderiv ℝ Ed z).range
      rw [Pi.add_apply, Finset.sum_apply]
      simp only [Pi.smul_apply']
      exact Submodule.add_mem _ (Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _ (hmodel i))
        (Submodule.smul_mem _ _ hfar)
    · rw [Function.notMem_support.mp (fun h => hz (subset_tsupport Y h))]
      exact Submodule.zero_mem _
  have hY_orth : ∀ z ∈ tsupport Y, z - Ed z ∈ (fderiv ℝ Ed z).rangeᗮ := by
    intro z hz
    have hzint : z ∈ interior {z | χd z = 1} := hY_tsup hz
    have hχz : χd z ≠ 0 := by
      have h1 : χd z = 1 := interior_subset (s := {w | χd w = 1}) hzint
      rw [h1]; exact one_ne_zero
    have hzU : z ∈ A.U := hχd_supp (subset_tsupport χd (Function.mem_support.mpr hχz))
    have hEdz : Ed z = A.e (A.π z) := by
      show χd z • A.e (A.π z) = A.e (A.π z)
      rw [interior_subset (s := {w | χd w = 1}) hzint, one_smul]
    rw [hdEd_eq z hzint, hEdz]
    exact A.hπorth z hzU
  -- the value of `Y` on the regions `C i`
  have hY_model : ∀ (i : ι) (y : M), y ∈ C i →
      Y (A.e y) = modelField A (φ i) (chartMult (r i)) (s₁ i) (s₂ i) (A.e y) := by
    intro i y hy
    have hev : A.e y ∈ interior {z | χi i z = 1} := hχi_one i ⟨y, subset_closure hy, rfl⟩
    have hχi_1 : χi i (A.e y) = 1 := interior_subset (s := {z | χi i z = 1}) hev
    have hχj_0 : ∀ j, j ≠ i → χi j (A.e y) = 0 := by
      intro j hj
      by_contra hne
      have hmem : A.e y ∈ tsupport (χi j) := subset_tsupport _ (Function.mem_support.mpr hne)
      have hsrc : A.π (A.e y) ∈ (φ j).source := (Set.subset_inter_iff.mp (hχi_supp j) |>.1 hmem).1.2
      rw [A.hπe] at hsrc
      exact Set.disjoint_left.mp (hdisj j i hj) hsrc (hCsub i hy)
    have hsum : (∑ j, χi j (A.e y)) = 1 := by
      rw [Finset.sum_eq_single i (fun j _ hj => hχj_0 j hj)
        (fun h => absurd (Finset.mem_univ i) h), hχi_1]
    have h1 : (∑ j, (χi j) • modelField A (φ j) (chartMult (r j)) (s₁ j) (s₂ j)) (A.e y)
        = modelField A (φ i) (chartMult (r i)) (s₁ i) (s₂ i) (A.e y) := by
      rw [Finset.sum_apply]
      rw [Finset.sum_eq_single i]
      · rw [Pi.smul_apply', hχi_1, one_smul]
      · intro j _ hj
        rw [Pi.smul_apply', hχj_0 j hj, zero_smul]
      · intro h
        exact absurd (Finset.mem_univ i) h
    have h2 : ((fun z => 1 - ∑ j, χi j z) • levelField Ed Gd χf) (A.e y) = 0 := by
      have hψ : (1 - ∑ j, χi j (A.e y)) = 0 := by rw [hsum, sub_self]
      rw [Pi.smul_apply', hψ, zero_smul]
    rw [hY_def, Pi.add_apply, h1, h2, add_zero]
  -- the level law off the model balls
  have hχd_nhds : ∀ y : M, ∀ᶠ w in 𝓝 (A.e y), χd w = 1 := fun y =>
    Filter.mem_of_superset (isOpen_interior.mem_nhds (hχd_int ⟨y, rfl⟩))
      (fun w hw => interior_subset (s := {z | χd z = 1}) hw)
  have hGd_eq : ∀ y : M, fderiv ℝ Gd (A.e y) = fderiv ℝ (fun z => f (A.π z)) (A.e y) := by
    intro y
    have hev : Gd =ᶠ[𝓝 (A.e y)] fun z => f (A.π z) := by
      filter_upwards [hχd_nhds y] with w hw
      show χd w • f (A.π w) = f (A.π w)
      rw [hw, one_smul]
    exact hev.fderiv_eq
  have hG_eq : ∀ y : M, fderiv ℝ (fun z => f (A.π z)) (A.e y) = fderiv ℝ Gd (A.e y) :=
    fun y => (hGd_eq y).symm
  have hY_law : ∀ y : M, (∀ i, y ∉ modelBall (φ i) (r i)) →
      (fderiv ℝ Gd (A.e y)) (Y (A.e y)) = 1 := by
    intro y hball
    have hterm : ∀ i, χi i (A.e y) ≠ 0 →
        (fderiv ℝ (fun z => f (A.π z)) (A.e y))
          (modelField A (φ i) (chartMult (r i)) (s₁ i) (s₂ i) (A.e y)) = 1 := by
      intro i hc
      have hmem : A.e y ∈ tsupport (χi i) := subset_tsupport _ (Function.mem_support.mpr hc)
      have hreg : A.π (A.e y) ∈ (φ i).source := (Set.subset_inter_iff.mp (hχi_supp i) |>.1 hmem).1.2
      have hsrc : y ∈ (φ i).source := by rwa [A.hπe] at hreg
      have hge : r i ≤ ‖φ i y‖ := by
        by_contra hlt
        push_neg at hlt
        exact hball i ⟨hsrc, hlt⟩
      have h1 := fderiv_piF_modelField A (φ i) (hφ i) (hφ' i) f hf (chartMult (r i))
        (s₁ i) (s₂ i) (hsgn i).1 (hsgn i).2 (f (x i)) (fun z hz => hval i z hz) hsrc
      rw [h1]
      have h2 : (r i) ^ 2 ≤ ‖φ i y‖ ^ 2 := by nlinarith [hge, norm_nonneg (φ i y), hr i]
      rw [chartMult_mul (hr i) h2]
    have hfar : (1 - ∑ i, χi i (A.e y)) ≠ 0 →
        (fderiv ℝ (fun z => f (A.π z)) (A.e y)) (levelField Ed Gd χf (A.e y)) = 1 := by
      intro hc
      have hnot : (∑ j, χi j (A.e y)) ≠ 1 := by
        intro hcon
        exact hc (by rw [hcon, sub_self])
      have hyfar : ∀ i, y ∉ C i := by
        intro i hyi
        apply hnot
        have h1 : χi i (A.e y) = 1 :=
          interior_subset (s := {z | χi i z = 1}) (hχi_one i ⟨y, subset_closure hyi, rfl⟩)
        have h2 : ∀ j, j ≠ i → χi j (A.e y) = 0 := by
          intro j hj
          by_contra hne
          have hmem : A.e y ∈ tsupport (χi j) := subset_tsupport _ (Function.mem_support.mpr hne)
          have hsrc : A.π (A.e y) ∈ (φ j).source :=
            (Set.subset_inter_iff.mp (hχi_supp j) |>.1 hmem).1.2
          rw [A.hπe] at hsrc
          exact Set.disjoint_left.mp (hdisj j i hj) hsrc (hCsub i hyi)
        rw [Finset.sum_eq_single i (fun j _ hj => h2 j hj) (fun h => absurd (Finset.mem_univ i) h), h1]
      have hcrit : ¬ Work.Drive.Morse.IsCritical f y := hCcrit y hyfar
      have haux : auxField Ed Gd (A.e y) ≠ 0 := by
        have := auxField_damped_ne_zero A χd hχd_int f hf hcrit
        simpa [Ed, Gd] using this
      have h1 : (fderiv ℝ Gd (A.e y)) (levelField Ed Gd χf (A.e y)) = χf (A.e y) :=
        hLF_spec.1 (A.e y) haux
      have h2 : χf (A.e y) = 1 := by
        have hmem : A.e y ∈ interior {z | χf z = 1} := hχf_one ⟨y, hnot, rfl⟩
        exact interior_subset (s := {z | χf z = 1}) hmem
      rw [← hGd_eq y, h1, h2]
    have hsum_val : (∑ i, (χi i) • modelField A (φ i) (chartMult (r i)) (s₁ i) (s₂ i)) (A.e y)
        = ∑ i, χi i (A.e y) • modelField A (φ i) (chartMult (r i)) (s₁ i) (s₂ i) (A.e y) := by
      rw [Finset.sum_apply]
      exact Finset.sum_congr rfl fun i _ => Pi.smul_apply' _ _ _
    have hsumterm : ∀ i, (fderiv ℝ (fun z => f (A.π z)) (A.e y))
        (χi i (A.e y) • modelField A (φ i) (chartMult (r i)) (s₁ i) (s₂ i) (A.e y))
        = χi i (A.e y) * ((fderiv ℝ (fun z => f (A.π z)) (A.e y))
            (modelField A (φ i) (chartMult (r i)) (s₁ i) (s₂ i) (A.e y))) := by
      intro i
      rw [ContinuousLinearMap.map_smul, smul_eq_mul]
    have hfarterm : (fderiv ℝ (fun z => f (A.π z)) (A.e y))
        ((1 - ∑ i, χi i (A.e y)) • levelField Ed Gd χf (A.e y))
        = (1 - ∑ i, χi i (A.e y)) * ((fderiv ℝ (fun z => f (A.π z)) (A.e y))
            (levelField Ed Gd χf (A.e y))) := by
      rw [ContinuousLinearMap.map_smul, smul_eq_mul]
    have hsumrewrite : (fderiv ℝ (fun z => f (A.π z)) (A.e y))
        (∑ i, χi i (A.e y) • modelField A (φ i) (chartMult (r i)) (s₁ i) (s₂ i) (A.e y))
        = ∑ i, χi i (A.e y) * ((fderiv ℝ (fun z => f (A.π z)) (A.e y))
            (modelField A (φ i) (chartMult (r i)) (s₁ i) (s₂ i) (A.e y))) := by
      rw [map_sum]
      exact Finset.sum_congr rfl fun i _ => hsumterm i
    rw [hY_def, Pi.add_apply, hsum_val, Pi.smul_apply', hGd_eq y, map_add, hsumrewrite, hfarterm]
    have h1 : ∑ i, χi i (A.e y) *
        ((fderiv ℝ (fun z => f (A.π z)) (A.e y))
          (modelField A (φ i) (chartMult (r i)) (s₁ i) (s₂ i) (A.e y)))
        = ∑ i, χi i (A.e y) := by
      refine Finset.sum_congr rfl fun i _ => ?_
      by_cases hc : χi i (A.e y) = 0
      · rw [hc, zero_mul]
      · rw [hterm i hc, mul_one]
    have h2 : (1 - ∑ i, χi i (A.e y)) *
        ((fderiv ℝ (fun z => f (A.π z)) (A.e y)) (levelField Ed Gd χf (A.e y)))
        = 1 - ∑ i, χi i (A.e y) := by
      by_cases hc : (1 - ∑ i, χi i (A.e y)) = 0
      · rw [hc, zero_mul]
      · rw [hfar hc, mul_one]
    rw [h1, h2]
    ring
  -- the flow of the ambient field
  obtain ⟨FL, δ, hδ, hFL0, hFLsem, hFLcurve, _hFLslice⟩ :=
    Work.Whitney.CutPush.flow_of_compactSupport Y hY_sm hY_cs
  obtain ⟨M0, _hM00, hM0bd⟩ := Work.ODE.exists_norm_le_of_hasCompactSupport hY_sm.continuous hY_cs
  have hfdcont : Continuous (fderiv ℝ Y) := hY_sm.continuous_fderiv (by norm_num)
  have hfdcs : HasCompactSupport (fderiv ℝ Y) := hY_cs.fderiv (𝕜 := ℝ)
  obtain ⟨K0, _hK00, hK0bd⟩ := Work.ODE.exists_norm_le_of_hasCompactSupport hfdcont hfdcs
  have hFLjoint : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
      (fun p : ℝ × EuclideanSpace ℝ (Fin 5) => FL p.1 p.2) :=
    contDiff_flow_joint_of_bounds Y hY_sm M0 K0 hM0bd hK0bd FL hFL0 hFLsem hFLcurve
  -- the trajectories stay on the embedded surface
  have htraj : ∀ y : M, ∀ t : ℝ, A.e (A.π (FL t (A.e y))) = FL t (A.e y) := by
    intro y t
    have hχd_traj : ∀ s : ℝ, χd (FL s (A.e y)) = 1 := by
      intro s
      rcases isIntegralCurve_mem_tsupport_or_eq Y hY_sm hY_cs (fun s => FL s (A.e y))
        (hFLcurve (A.e y)) s with hmem | heq
      · exact interior_subset (s := {w | χd w = 1}) (hY_tsup hmem)
      · rw [heq, hFL0]; exact hχd_e y
    have hfix := retraction_fixed_of_isIntegralCurve Ed Y (fun s => FL s (A.e y)) hEd_sm hY_sm
      hY_cs hY_range hY_orth (hFLcurve (A.e y)) ?_
    · have h := hfix t
      rwa [show Ed (FL t (A.e y)) = A.e (A.π (FL t (A.e y))) from by
        show χd (FL t (A.e y)) • A.e (A.π (FL t (A.e y))) = A.e (A.π (FL t (A.e y)))
        rw [hχd_traj t, one_smul]] at h
    · show Ed (FL 0 (A.e y)) = FL 0 (A.e y)
      rw [hFL0]
      show χd (A.e y) • A.e (A.π (A.e y)) = A.e y
      rw [A.hπe y, hχd_e y, one_smul]
  have hΦ_sm : ContMDiff ((𝓘(ℝ, ℝ)).prod (𝓡 2)) (𝓡 2) ((⊤ : ℕ∞) : WithTop ℕ∞)
      (fun p : ℝ × M => A.π (FL p.1 (A.e p.2))) := by
    have hq : ContMDiff ((𝓘(ℝ, ℝ)).prod (𝓡 2)) (𝓡 5) ((⊤ : ℕ∞) : WithTop ℕ∞)
        (fun p : ℝ × M => FL p.1 (A.e p.2)) := by
      have h1 : ContMDiff ((𝓘(ℝ, ℝ)).prod (𝓡 2))
          ((modelWithCornersSelf ℝ ℝ).prod (𝓡 5)) ((⊤ : ℕ∞) : WithTop ℕ∞)
          (fun p : ℝ × M => (p.1, A.e p.2)) :=
        ContMDiff.prodMk contMDiff_fst (A.he.comp contMDiff_snd)
      have h2 : ContMDiff ((modelWithCornersSelf ℝ ℝ).prod (𝓡 5)) (𝓡 5)
          ((⊤ : ℕ∞) : WithTop ℕ∞)
          (fun q : ℝ × EuclideanSpace ℝ (Fin 5) => FL q.1 q.2) := by
        rw [show (modelWithCornersSelf ℝ ℝ).prod (𝓡 5)
            = 𝓘(ℝ, ℝ × EuclideanSpace ℝ (Fin 5)) from
          (modelWithCornersSelf_prod (F := EuclideanSpace ℝ (Fin 5))).symm]
        rw [show prodChartedSpace ℝ ℝ (EuclideanSpace ℝ (Fin 5)) (EuclideanSpace ℝ (Fin 5))
            = chartedSpaceSelf (ℝ × EuclideanSpace ℝ (Fin 5)) from chartedSpaceSelf_prod]
        exact (contMDiff_iff_contDiff).mpr hFLjoint
      exact h2.comp h1
    have hcomp : ContMDiffOn ((𝓘(ℝ, ℝ)).prod (𝓡 2)) (𝓡 2) ((⊤ : ℕ∞) : WithTop ℕ∞)
        (fun p : ℝ × M => A.π (FL p.1 (A.e p.2))) Set.univ :=
      A.hπ.comp (hq.contMDiffOn (s := Set.univ)) (fun p _ => by
        show FL p.1 (A.e p.2) ∈ A.U
        rw [← htraj p.2 p.1]
        exact A.hUe ⟨_, rfl⟩)
    exact contMDiffOn_univ.mp hcomp
  refine ⟨fun p : ℝ × M => A.π (FL p.1 (A.e p.2)), hΦ_sm, ?_, ?_, ?_, ?_, ?_⟩
  · -- the flow fixes the initial point
    intro y
    show A.π (FL 0 (A.e y)) = y
    rw [hFL0, A.hπe y]
  · -- the semigroup law
    intro a b y
    show A.π (FL a (A.e (A.π (FL b (A.e y))))) = A.π (FL (a + b) (A.e y))
    rw [htraj y b, ← hFLsem a b]
  · -- the level law off the model balls
    intro y t hy hseg
    have hzero : ∀ z : M, A.π (FL 0 (A.e z)) = z := fun z => by rw [hFL0, A.hπe z]
    have hderiv : ∀ z : M, z ∉ ⋃ i, modelBall (φ i) (r i) →
        HasDerivAt (fun s : ℝ => f (A.π (FL s (A.e z)))) 1 0 := by
      intro z hz
      have hz' : ∀ i, z ∉ modelBall (φ i) (r i) :=
        fun i hi => hz (Set.mem_iUnion.mpr ⟨i, hi⟩)
      have hcont0 : ContinuousAt (fun s : ℝ => FL s (A.e z)) 0 := by
        have h1 : Continuous (fun p : ℝ × EuclideanSpace ℝ (Fin 5) => FL p.1 p.2) :=
          hFLjoint.continuous
        have h2 : Continuous (fun s : ℝ => (s, A.e z)) := continuous_id.prodMk continuous_const
        have h3 := h1.comp h2
        simpa [Function.comp_def] using h3.continuousAt
      have hbase : (fun s : ℝ => FL s (A.e z)) 0 ∈ interior {w | χd w = 1} := by
        show FL 0 (A.e z) ∈ interior {w | χd w = 1}
        rw [hFL0]
        exact hχd_int ⟨z, rfl⟩
      have hmem : ∀ᶠ s : ℝ in 𝓝 (0 : ℝ), χd (FL s (A.e z)) = 1 :=
        (hcont0.eventually (isOpen_interior.mem_nhds hbase)).mono
          (fun s hs => interior_subset (s := {w | χd w = 1}) hs)
      have hev : (fun s : ℝ => f (A.π (FL s (A.e z)))) =ᶠ[𝓝 (0 : ℝ)]
          (fun s : ℝ => Gd (FL s (A.e z))) := by
        filter_upwards [hmem] with s hs
        show f (A.π (FL s (A.e z))) = χd (FL s (A.e z)) • f (A.π (FL s (A.e z)))
        rw [hs, one_smul]
      have hcurve0 : HasDerivAt (fun s : ℝ => FL s (A.e z)) (Y (A.e z)) 0 := by
        have h := hFLcurve (A.e z) 0
        have h0 : FL 0 (A.e z) = A.e z := hFL0 (A.e z)
        simpa [h0] using h
      have hderiv' : HasDerivAt (fun s : ℝ => Gd (FL s (A.e z)))
          ((fderiv ℝ Gd (A.e z)) (Y (A.e z))) 0 := by
        have hF : HasFDerivAt Gd (fderiv ℝ Gd (A.e z)) ((fun s : ℝ => FL s (A.e z)) 0) := by
          have h0 : (fun s : ℝ => FL s (A.e z)) 0 = A.e z := by simp [hFL0]
          rw [h0]
          exact (hGd_sm.differentiable (by simp)).differentiableAt.hasFDerivAt
        simpa [Function.comp_def] using hF.comp_hasDerivAt (x := (0 : ℝ)) hcurve0
      have := hderiv'.congr_of_eventuallyEq hev
      rw [hY_law z hz'] at this
      exact this
    exact level_law_of_deriv (Φ := fun p : ℝ × M => A.π (FL p.1 (A.e p.2)))
      (f := f) (U := ⋃ i, modelBall (φ i) (r i)) hf.continuous
      (hΦ_sm.continuous.comp (continuous_id.prodMk continuous_const))
      hzero (fun a b => by
        show A.π (FL a (A.e (A.π (FL b (A.e y))))) = A.π (FL (a + b) (A.e y))
        rw [htraj y b, ← hFLsem a b])
      hderiv (fun u hu hmem => (Set.mem_iUnion.mp hmem).elim fun i hi => hseg u hu i hi)
  · -- the model monotonicity on the regions `C i`
    intro i y t₁ t₂ hseg hQ
    set u₁ : ℝ → ℝ := fun t => (φ i (A.π (FL t (A.e y)))).ofLp 0 with hu₁
    set v₁ : ℝ → ℝ := fun t => (φ i (A.π (FL t (A.e y)))).ofLp 1 with hv₁
    have hnorm : ∀ t : ℝ,
        u₁ t ^ 2 + v₁ t ^ 2 = ‖φ i (A.π (FL t (A.e y)))‖ ^ 2 := by
      intro t
      rw [hu₁, hv₁]
      exact norm_uVec _
    have hode : ∀ t ∈ Set.Icc (min t₁ t₂) (max t₁ t₂),
        HasDerivAt u₁ ((chartMult (r i) (u₁ t ^ 2 + v₁ t ^ 2)) * (s₁ i * u₁ t)) t := by
      intro t ht
      have hCt : A.π (FL t (A.e y)) ∈ C i := (hseg t ht).1
      have hsrc : A.π (FL t (A.e y)) ∈ (φ i).source := hCsub i hCt
      have hU : DifferentiableAt ℝ (uCoord A (φ i) 0) (FL t (A.e y)) := by
        rw [← htraj y t]
        exact (contDiffAt_uCoord A (φ i) (hφ i) hsrc 0).differentiableAt (by simp)
      have hchain := hU.hasFDerivAt.comp_hasDerivAt (x := t) (hFLcurve (A.e y) t)
      have hYt : Y (FL t (A.e y))
          = modelField A (φ i) (chartMult (r i)) (s₁ i) (s₂ i) (FL t (A.e y)) := by
        rw [← htraj y t]
        exact hY_model i (A.π (FL t (A.e y))) hCt
      have hval' : (fderiv ℝ (uCoord A (φ i) 0) (FL t (A.e y))) (Y (FL t (A.e y)))
          = chartMult (r i) (u₁ t ^ 2 + v₁ t ^ 2) * (s₁ i * u₁ t) := by
        rw [hYt, ← htraj y t,
          fderiv_uCoord_modelField A (φ i) (hφ i) (hφ' i) (chartMult (r i))
            (s₁ i) (s₂ i) hsrc 0]
        rw [(chartVel_apply (chartMult (r i)) (s₁ i) (s₂ i) (φ i (A.π (FL t (A.e y))))).1,
          ← norm_uVec (φ i (A.π (FL t (A.e y))))]
      have h := hchain
      rw [hval', Function.comp_def] at h
      have hfun : (fun s : ℝ => uCoord A (φ i) 0 (FL s (A.e y))) = u₁ := by
        funext s
        simp [uCoord, hu₁]
      rw [hfun] at h
      exact h
    have hodev : ∀ t ∈ Set.Icc (min t₁ t₂) (max t₁ t₂),
        HasDerivAt v₁ ((chartMult (r i) (u₁ t ^ 2 + v₁ t ^ 2)) * (s₂ i * v₁ t)) t := by
      intro t ht
      have hCt : A.π (FL t (A.e y)) ∈ C i := (hseg t ht).1
      have hsrc : A.π (FL t (A.e y)) ∈ (φ i).source := hCsub i hCt
      have hU : DifferentiableAt ℝ (uCoord A (φ i) 1) (FL t (A.e y)) := by
        rw [← htraj y t]
        exact (contDiffAt_uCoord A (φ i) (hφ i) hsrc 1).differentiableAt (by simp)
      have hchain := hU.hasFDerivAt.comp_hasDerivAt (x := t) (hFLcurve (A.e y) t)
      have hYt : Y (FL t (A.e y))
          = modelField A (φ i) (chartMult (r i)) (s₁ i) (s₂ i) (FL t (A.e y)) := by
        rw [← htraj y t]
        exact hY_model i (A.π (FL t (A.e y))) hCt
      have hval' : (fderiv ℝ (uCoord A (φ i) 1) (FL t (A.e y))) (Y (FL t (A.e y)))
          = chartMult (r i) (u₁ t ^ 2 + v₁ t ^ 2) * (s₂ i * v₁ t) := by
        rw [hYt, ← htraj y t,
          fderiv_uCoord_modelField A (φ i) (hφ i) (hφ' i) (chartMult (r i))
            (s₁ i) (s₂ i) hsrc 1]
        rw [(chartVel_apply (chartMult (r i)) (s₁ i) (s₂ i) (φ i (A.π (FL t (A.e y))))).2,
          ← norm_uVec (φ i (A.π (FL t (A.e y))))]
      have h := hchain
      rw [hval', Function.comp_def] at h
      have hfun : (fun s : ℝ => uCoord A (φ i) 1 (FL s (A.e y))) = v₁ := by
        funext s
        simp [uCoord, hv₁]
      rw [hfun] at h
      exact h
    have hQ' : |s₁ i * u₁ t₁ ^ 2 + s₂ i * v₁ t₁ ^ 2|
        < |s₁ i * u₁ t₂ ^ 2 + s₂ i * v₁ t₂ ^ 2| := by
      have h := hQ
      simpa [hu₁, hv₁, chartQ] using h
    have hmono := model_orbit_norm_mono_of_factor (u := u₁) (v := v₁)
      (lam := fun t => chartMult (r i) (u₁ t ^ 2 + v₁ t ^ 2))
      (hsgn i).1 (hsgn i).2 hode hodev hQ'
    have hsqrt : ∀ t : ℝ, ‖φ i (A.π (FL t (A.e y)))‖ = Real.sqrt (u₁ t ^ 2 + v₁ t ^ 2) := by
      intro t
      rw [(Real.sqrt_sq (norm_nonneg (φ i (A.π (FL t (A.e y)))))).symm, hnorm t]
    have hgoal : ‖φ i (A.π (FL t₁ (A.e y)))‖ < ‖φ i (A.π (FL t₂ (A.e y)))‖ := by
      rw [hsqrt t₁, hsqrt t₂]
      exact hmono
    simpa using hgoal

  · -- the chart ODE on the regions `C i`
    intro i y t hseg
    change HasDerivAt (fun σ : ℝ => φ i (A.π (FL σ (A.e y))) 0)
        (chartMult (r i) (‖φ i (A.π (FL t (A.e y)))‖ ^ 2)
          * (s₁ i * φ i (A.π (FL t (A.e y))) 0)) t ∧
      HasDerivAt (fun σ : ℝ => φ i (A.π (FL σ (A.e y))) 1)
        (chartMult (r i) (‖φ i (A.π (FL t (A.e y)))‖ ^ 2)
          * (s₂ i * φ i (A.π (FL t (A.e y))) 1)) t
    have hCt : A.π (FL t (A.e y)) ∈ C i :=
      hseg t ⟨min_le_right (0 : ℝ) t, le_max_right (0 : ℝ) t⟩
    have hsrc : A.π (FL t (A.e y)) ∈ (φ i).source := hCsub i hCt
    have hFLt : HasDerivAt (fun σ : ℝ => FL σ (A.e y)) (Y (FL t (A.e y))) t := by
      have h := hFLcurve (A.e y) t
      simpa using h
    have hYt : Y (FL t (A.e y))
        = modelField A (φ i) (chartMult (r i)) (s₁ i) (s₂ i) (FL t (A.e y)) := by
      rw [← htraj y t]
      exact hY_model i (A.π (FL t (A.e y))) hCt
    have hU0 : DifferentiableAt ℝ (uCoord A (φ i) 0) (FL t (A.e y)) := by
      rw [← htraj y t]
      exact (contDiffAt_uCoord A (φ i) (hφ i) hsrc 0).differentiableAt (by simp)
    have hU1 : DifferentiableAt ℝ (uCoord A (φ i) 1) (FL t (A.e y)) := by
      rw [← htraj y t]
      exact (contDiffAt_uCoord A (φ i) (hφ i) hsrc 1).differentiableAt (by simp)
    have hval0 : (fderiv ℝ (uCoord A (φ i) 0) (FL t (A.e y))) (Y (FL t (A.e y)))
        = chartMult (r i) (‖φ i (A.π (FL t (A.e y)))‖ ^ 2)
          * (s₁ i * φ i (A.π (FL t (A.e y))) 0) := by
      conv_lhs =>
        rw [hYt, ← htraj y t,
          fderiv_uCoord_modelField A (φ i) (hφ i) (hφ' i) (chartMult (r i))
            (s₁ i) (s₂ i) hsrc 0,
          (chartVel_apply (chartMult (r i)) (s₁ i) (s₂ i)
            (φ i (A.π (FL t (A.e y))))).1]
    have hval1 : (fderiv ℝ (uCoord A (φ i) 1) (FL t (A.e y))) (Y (FL t (A.e y)))
        = chartMult (r i) (‖φ i (A.π (FL t (A.e y)))‖ ^ 2)
          * (s₂ i * φ i (A.π (FL t (A.e y))) 1) := by
      conv_lhs =>
        rw [hYt, ← htraj y t,
          fderiv_uCoord_modelField A (φ i) (hφ i) (hφ' i) (chartMult (r i))
            (s₁ i) (s₂ i) hsrc 1,
          (chartVel_apply (chartMult (r i)) (s₁ i) (s₂ i)
            (φ i (A.π (FL t (A.e y))))).2]
    have hd0 : HasDerivAt (fun σ : ℝ => φ i (A.π (FL σ (A.e y))) 0)
        (chartMult (r i) (‖φ i (A.π (FL t (A.e y)))‖ ^ 2)
          * (s₁ i * φ i (A.π (FL t (A.e y))) 0)) t := by
      have h := hU0.hasFDerivAt.comp_hasDerivAt (x := t) hFLt
      rw [hval0] at h
      simpa [Function.comp_def, uCoord] using h
    have hd1 : HasDerivAt (fun σ : ℝ => φ i (A.π (FL σ (A.e y))) 1)
        (chartMult (r i) (‖φ i (A.π (FL t (A.e y)))‖ ^ 2)
          * (s₂ i * φ i (A.π (FL t (A.e y))) 1)) t := by
      have h := hU1.hasFDerivAt.comp_hasDerivAt (x := t) hFLt
      rw [hval1] at h
      simpa [Function.comp_def, uCoord] using h
    exact ⟨hd0, hd1⟩



/-- **The chart ODE row of the model-adapted flow.**  For every chart `i`, along any piece of an
orbit which stays in the region `C i`, the chart coordinates of the orbit solve the model ODE. -/
theorem exists_modelAdapted_levelFlow_chartODE {M : Type*} [TopologicalSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin 2)) M]
    [IsManifold (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 2))) ((⊤ : ℕ∞) : WithTop ℕ∞) M]
    [T2Space M] [SecondCountableTopology M] [CompactSpace M]
    (f : M → ℝ)
    (hf : ContMDiff (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 2)))
      (modelWithCornersSelf ℝ ℝ) ((⊤ : ℕ∞) : WithTop ℕ∞) f)
    {ι : Type*} [Fintype ι]
    (x : ι → M) (φ : ι → OpenPartialHomeomorph M (EuclideanSpace ℝ (Fin 2)))
    (s₁ s₂ r : ι → ℝ) (hr : ∀ i, 0 < r i)
    (hsrc : ∀ i, x i ∈ (φ i).source) (hcen : ∀ i, φ i (x i) = 0)
    (hsgn : ∀ i, (s₁ i = 1 ∨ s₁ i = -1) ∧ (s₂ i = 1 ∨ s₂ i = -1))
    (hval : ∀ i y, y ∈ (φ i).source →
      f y = f (x i) + Work.Drive.N2.chartQ (φ i) (s₁ i) (s₂ i) y)
    (hφ : ∀ i, ContMDiffOn (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 2)))
      (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 2))) ((⊤ : ℕ∞) : WithTop ℕ∞)
      (fun y => φ i y) (φ i).source)
    (hφ' : ∀ i, ContMDiffOn (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 2)))
      (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 2))) ((⊤ : ℕ∞) : WithTop ℕ∞)
      (fun y => (φ i).symm y) (φ i).target)
    (hdisj : ∀ i j, i ≠ j → Disjoint (φ i).source (φ j).source)
    (C : ι → Set M) (hCsub : ∀ i, C i ⊆ (φ i).source)
    (hCcl : ∀ i, IsCompact (closure (C i)) ∧ closure (C i) ⊆ (φ i).source)
    (hCball : ∀ i, Work.Drive.N2.modelBall (φ i) (r i) ⊆ C i)
    (hCcrit : ∀ y, (∀ i, y ∉ C i) → ¬ Work.Drive.Morse.IsCritical f y) :
    ∃ Φ : ℝ × M → M,
      ContMDiff ((modelWithCornersSelf ℝ ℝ).prod (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 2))))
        (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 2))) ((⊤ : ℕ∞) : WithTop ℕ∞) Φ ∧
      (∀ y, Φ (0, y) = y) ∧
      (∀ a b y, Φ (a, Φ (b, y)) = Φ (a + b, y)) ∧
      (∀ (y : M) (t : ℝ), (∀ i, y ∉ Work.Drive.N2.modelBall (φ i) (r i)) →
        (∀ u ∈ Set.Icc (min 0 t) (max 0 t), ∀ i,
          Φ (u, y) ∉ Work.Drive.N2.modelBall (φ i) (r i)) →
        f (Φ (t, y)) = f y + t) ∧
      (∀ (i : ι) (y : M) (t : ℝ),
        (∀ u ∈ Set.Icc (min 0 t) (max 0 t), Φ (u, y) ∈ C i) →
        HasDerivAt (fun σ : ℝ => φ i (Φ (σ, y)) 0)
          (Work.Drive.N2.chartMult (r i) (‖φ i (Φ (t, y))‖ ^ 2) * (s₁ i * φ i (Φ (t, y)) 0))
          t ∧
        HasDerivAt (fun σ : ℝ => φ i (Φ (σ, y)) 1)
          (Work.Drive.N2.chartMult (r i) (‖φ i (Φ (t, y))‖ ^ 2) * (s₂ i * φ i (Φ (t, y)) 1))
          t) := by
  classical
  by_cases hne : Nonempty M
  · haveI := hne
    obtain ⟨A⟩ := exists_ambSetup_of_compact M
    obtain ⟨χd, χi, χf, hχd_sm, _hχd_cs, hχd_supp, hχd_int, hχi, hχf_sm, hχf_cs, hχf_supp,
      hχf_one⟩ :=
      exists_modelAdapted_bumpData A f hf φ hφ hφ' hdisj C hCsub hCcl hCcrit
    obtain ⟨Φ, h1, h2, h3, h4, _h5, h6⟩ :=
      exists_modelAdapted_levelFlow_of_bumps_chartODE A f hf x φ s₁ s₂ r hr hsrc hcen hsgn
        hval hφ hφ' hdisj C hCsub hCcl hCball hCcrit χd hχd_sm hχd_supp hχd_int χi
        (fun i => (hχi i).1) (fun i => (hχi i).2.1) (fun i => (hχi i).2.2.1)
        (fun i => (hχi i).2.2.2) χf hχf_sm hχf_cs hχf_supp hχf_one
    exact ⟨Φ, h1, h2, h3, h4, h6⟩
  · haveI : IsEmpty M := not_nonempty_iff.mp hne
    refine ⟨fun p : ℝ × M => p.2, contMDiff_snd, ?_, ?_, ?_, ?_⟩
    · intro y; exact isEmptyElim y
    · intro a b y; exact isEmptyElim y
    · intro y; exact isEmptyElim y
    · intro i y; exact isEmptyElim y

end Work.Drive.N2
