import Submission.Work.StemsB.CollarModel
import Submission.Work.StemsB.serreSphere_sets
import Submission.Work.StemsB.serreSphere_contract_big
import Submission.Work.StemsB.onePoint_radialPush
import Submission.Work.StemsB.FibreTrivial
import Submission.Work.StemsB.RelThickening

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 400000

/-!
# The two thickenings of the Serre exact sequence over a sphere

This file collects the point-set and homotopy-theoretic inputs of the pentagon of
`Submission/Work/StemsB/SERRE_PLAN.md` that concern the two **pieces** of the sphere model
`SphModel n = OnePoint ℝⁿ`:

* the sup-norm outer piece `sphLoopOuter n = {∞} ∪ {|v|_∞ > 1/2}` is open, it covers the model
  together with the inner cube `sphLoopBig n = {|v|_∞ < 3/2}`, it is contained in the Euclidean
  thickening `sphLoopThick n`, and it is **based-contractible to `∞`**: the radial push
  `Work.StemsB.onePoint_radialPush_outer`;
* the inner cube `sphLoopBig n` is contractible to `sphShellPt n` (`serreSphere_contract_big`), and
  `sphShellPt n` lies in the collar `sphLoopCollar n`.

From a *based contraction* of a piece `W` to a point `d₀ ∈ W` the thickening step of the pentagon
follows: the inclusion `p⁻¹d₀ ↪ p⁻¹W` is a homotopy equivalence
(`Work.StemsB.preimageIncl_homotopyEquiv_of_deformation`), so the map of relative chain complexes
`C_*(E, p⁻¹d₀) → C_*(E, p⁻¹W)` is a quasi-isomorphism.  This is packaged as

* `Work.StemsB.isIso_relChainsMapOf_preimageIncl_of_deformation`,
* `Work.StemsB.isIso_relChainsMapOf_sphLoopOuter` (the outer piece),
* `Work.StemsB.isIso_relChainsMapOf_sphLoopBig` (the inner piece).
-/

open scoped Topology unitInterval
open CategoryTheory CategoryTheory.Limits

set_option maxHeartbeats 2000000
set_option linter.unusedSectionVars false

namespace Work.StemsB

noncomputable section

variable {n : ℕ}

/-! ## The radial push at the endpoints -/

theorem pushFun_zero (n : ℕ) (x : SphModel n) : pushFun n (x, 0) = x := by
  rcases x with _ | v
  · exact pushFun_infty n 0
  · show pushFun n (OnePoint.some v, 0) = OnePoint.some v
    simp [pushFun_some]

theorem pushFun_one (n : ℕ) (x : SphModel n) : pushFun n (x, 1) = OnePoint.infty := by
  rcases x with _ | v
  · exact pushFun_infty n 1
  · show pushFun n (OnePoint.some v, 1) = OnePoint.infty
    rw [pushFun_some, if_pos (by norm_num : (((1 : unitInterval)) : ℝ) = 1)]

/-! ## The outer piece -/

theorem sphLoopOuter_subset_sphLoopThick (n : ℕ) : sphLoopOuter n ⊆ sphLoopThick n := by
  rintro x (rfl | ⟨v, rfl, i, hi⟩)
  · exact Or.inl rfl
  · refine Or.inr ⟨v, rfl, ?_⟩
    exact lt_of_lt_of_le hi (PiLp.norm_apply_le v i)

/-- **The radial push stays in the outer piece**: the factor `(1-t)⁻¹` is `≥ 1` on `[0,1]`, so the
absolute values of the coordinates do not decrease. -/
theorem mem_sphLoopOuter_pushFun (n : ℕ) {x : SphModel n} (hx : x ∈ sphLoopOuter n)
    (t : unitInterval) : pushFun n (x, t) ∈ sphLoopOuter n := by
  rcases hx with h | ⟨v, hv, i, hi⟩
  · rw [show x = OnePoint.infty from h, pushFun_infty]
    exact Or.inl rfl
  · rw [show x = OnePoint.some v from hv, pushFun_some]
    by_cases h1 : (t : ℝ) = 1
    · rw [if_pos h1]; exact Or.inl rfl
    · have ht : (t : ℝ) < 1 := lt_of_le_of_ne t.2.2 h1
      have hpos : (0 : ℝ) < 1 - (t : ℝ) := by linarith
      have hle : (1 : ℝ) ≤ (1 - (t : ℝ))⁻¹ := by
        rw [one_le_inv₀ hpos]; linarith [t.2.1]
      rw [if_neg h1]
      refine Or.inr ⟨_, rfl, i, ?_⟩
      rw [PiLp.smul_apply, smul_eq_mul, abs_mul,
        abs_of_nonneg (le_trans zero_le_one hle)]
      nlinarith [abs_nonneg (v i), hi, hle]

theorem continuous_pushFun_outer (n : ℕ) :
    Continuous fun q : ↥(sphLoopOuter n) × unitInterval => pushFun n (q.1.1, q.2) := by
  rw [continuous_iff_continuousAt]
  intro q
  have hincl : ContinuousAt
      (fun q : ↥(sphLoopOuter n) × unitInterval => (q.1.1, q.2)) q :=
    ((continuous_subtype_val.comp continuous_fst).prodMk continuous_snd).continuousAt
  have h1 : ContinuousAt (fun p : SphModel n × unitInterval => pushFun n p) (q.1.1, q.2) := by
    rcases q.1.2 with h | ⟨v, hv, i, hi⟩
    · rw [show q.1.1 = OnePoint.infty from h]
      exact continuousAt_pushFun_infty n q.2
    · have hv0 : v ≠ 0 := by
        intro h0
        rw [h0] at hi
        simp at hi
        linarith [hi]
      rw [show q.1.1 = OnePoint.some v from hv]
      exact continuousAt_pushFun_some n v hv0 q.2
  exact ContinuousAt.comp (f := fun q : ↥(sphLoopOuter n) × unitInterval => (q.1.1, q.2))
    (g := fun p : SphModel n × unitInterval => pushFun n p) h1 hincl

/-- **The outer piece is based-contractible to `∞`**, by the radial push. -/
theorem onePoint_radialPush_outer (n : ℕ) :
    ∃ F : C(↥(sphLoopOuter n) × unitInterval, ↥(sphLoopOuter n)),
      (∀ u, F (u, 0) = u) ∧
      (∀ u, F (u, 1) = ⟨OnePoint.infty, Or.inl rfl⟩) ∧
      (∀ t, F (⟨OnePoint.infty, Or.inl rfl⟩, t) = ⟨OnePoint.infty, Or.inl rfl⟩) := by
  have hmem : ∀ q : ↥(sphLoopOuter n) × unitInterval,
      pushFun n (q.1.1, q.2) ∈ sphLoopOuter n := fun q => mem_sphLoopOuter_pushFun n q.1.2 q.2
  refine ⟨⟨fun q => ⟨pushFun n (q.1.1, q.2), hmem q⟩,
    (continuous_pushFun_outer n).subtype_mk hmem⟩, ?_, ?_, ?_⟩
  · intro u
    apply Subtype.ext
    exact pushFun_zero n u.1
  · intro u
    apply Subtype.ext
    exact pushFun_one n u.1
  · intro t
    apply Subtype.ext
    exact pushFun_infty n t

/-! ## Openness, the cover, and the collar point -/

/-- **The outer piece as a union of explicit open sets**: the complement of the closed unit cube
together with the coordinate strips `|v i| > 1/2`. -/
theorem sphLoopOuter_eq (n : ℕ) :
    sphLoopOuter n =
      ((OnePoint.some '' {v : EuclideanSpace ℝ (Fin n) | coordSup n v ≤ 1})ᶜ ∪
        ⋃ i : Fin n, (OnePoint.some '' {v : EuclideanSpace ℝ (Fin n) | (1 / 2 : ℝ) < |v i|})) := by
  ext x
  constructor
  · rintro (rfl | ⟨v, rfl, i, hi⟩)
    · left
      intro h
      obtain ⟨w, -, hw⟩ := h
      exact absurd hw (by simp)
    · right
      exact Set.mem_iUnion.mpr ⟨i, ⟨v, hi, rfl⟩⟩
  · intro hx
    rw [Set.mem_union, Set.mem_iUnion] at hx
    rcases hx with h | ⟨i, hi⟩
    · by_cases hxinf : x = OnePoint.infty
      · exact Or.inl hxinf
      · right
        rcases x with _ | v
        · exact absurd rfl hxinf
        · refine ⟨v, rfl, ?_⟩
          by_contra hcon
          push Not at hcon
          refine h ⟨v, ?_, rfl⟩
          exact (coordSup_le_one_iff n v).mpr fun i => by
            rw [Set.mem_Icc, ← abs_le]
            linarith [hcon i]
    · obtain ⟨v, hi, rfl⟩ := hi
      exact Or.inr ⟨v, rfl, i, hi⟩


theorem isOpen_sphLoopOuter (n : ℕ) : IsOpen (sphLoopOuter n) := by
  rw [sphLoopOuter_eq]
  refine IsOpen.union ?_ ?_
  · exact OnePoint.isOpen_compl_image_coe.mpr
      ⟨(isCompact_coordSup_le_one n).isClosed, isCompact_coordSup_le_one n⟩
  · refine isOpen_iUnion fun i => OnePoint.isOpen_image_coe.mpr ?_
    exact isOpen_lt continuous_const (continuous_abs.comp (PiLp.continuous_apply (p := 2)
      (β := fun _ : Fin n => ℝ) i))

theorem sphLoopOuter_union_sphLoopBig (n : ℕ) : sphLoopOuter n ∪ sphLoopBig n = Set.univ := by
  ext x
  constructor
  · intro _; exact Set.mem_univ x
  · intro _
    rcases x with _ | v
    · exact Or.inl (Or.inl rfl)
    · by_cases h : ∃ i, (1 / 2 : ℝ) < |v i|
      · exact Or.inl (Or.inr ⟨v, rfl, h⟩)
      · push Not at h
        exact Or.inr ⟨v, rfl, fun i => lt_of_le_of_lt (h i) (by norm_num)⟩

theorem sphShellPt_mem_sphLoopOuter (n : ℕ) (hn : 1 ≤ n) : sphShellPt n ∈ sphLoopOuter n := by
  refine Or.inr ⟨sphShellVec n, sphShellPt_eq n,
    ⟨⟨0, Nat.pos_of_ne_zero (by omega)⟩, ?_⟩⟩
  rw [sphShellVec]
  simp only [WithLp.equiv_symm_apply, WithLp.ofLp_toLp]
  norm_num

theorem sphShellPt_mem_sphLoopCollar (n : ℕ) (hn : 1 ≤ n) : sphShellPt n ∈ sphLoopCollar n :=
  ⟨sphShellPt_mem_sphLoopOuter n hn, (serreSphere_sets n hn).2.2.2.2⟩

/-! ## The thickening step of the pentagon -/

section Thickening

variable {E B : Type} [TopologicalSpace E] [TopologicalSpace B]

/-- The inclusion of the preimages of `A ⊆ W`. -/
def preimageIncl (p : C(E, B)) (A W : Set B) (hAW : A ⊆ W) :
    TopCat.of (p ⁻¹' A) ⟶ TopCat.of (p ⁻¹' W) :=
  TopCat.ofHom ⟨fun x => ⟨x.1, hAW x.2⟩, continuous_subtype_val.subtype_mk _⟩

theorem preimageIncl_subtypeIncl (p : C(E, B)) (A W : Set B) (hAW : A ⊆ W) :
    Work.Cohomology.subtypeIncl (TopCat.of E) (p ⁻¹' A) ≫ 𝟙 (TopCat.of E)
      = preimageIncl p A W hAW ≫ Work.Cohomology.subtypeIncl (TopCat.of E) (p ⁻¹' W) := by
  apply TopCat.hom_ext
  apply ContinuousMap.ext
  intro x
  rfl

/-- A homotopy of the underlying maps, packaged as a `TopCat.Homotopy` (the variable order of the
underlying continuous map is swapped, since `TopCat.Homotopy` takes the time variable first). -/
def topCatHomotopyOf {X Y : TopCat} {f : X ⟶ Y} {g : Y ⟶ X}
    (H : C(↑X × unitInterval, ↑X)) (h0 : ∀ x, H (x, 0) = x) (h1 : ∀ x, H (x, 1) = g (f x)) :
    TopCat.Homotopy (f ≫ g) (𝟙 X) :=
  (ContinuousMap.Homotopy.mk ⟨fun z => H (z.2, z.1), H.continuous.comp (by fun_prop)⟩
    (fun x => h0 x) (fun x => h1 x)).symm

/-- **The thickening step**: for a *based contraction* of `W ⊆ B` to a point `d₀ ∈ W` (fixing `d₀`)
the map of relative chain complexes `C_*(E, p⁻¹d₀) → C_*(E, p⁻¹W)` is a quasi-isomorphism. -/
theorem isIso_relChainsMapOf_preimageIncl_of_deformation (p : C(E, B))
    (hp : IsHurewiczFibration p) (A W : Set B) (hAW : A ⊆ W)
    (ρ : C(↥W × unitInterval, ↥W)) (hρ0 : ∀ w, ρ (w, 0) = w)
    (hρ1 : ∀ w, (ρ (w, 1)).1 ∈ A)
    (hρA : ∀ (a : ↥A) (t), ρ (⟨a.1, hAW a.2⟩, t) = ⟨a.1, hAW a.2⟩) (k : ℕ) :
    IsIso (HomologicalComplex.homologyMap (Work.Cohomology.relChainsMapOf
      (TopCat.of E) (TopCat.of E) (p ⁻¹' A) (p ⁻¹' W) (𝟙 (TopCat.of E))
      (preimageIncl p A W hAW) (preimageIncl_subtypeIncl p A W hAW)) k) := by
  obtain ⟨f, g, hgf, ⟨H, hH0, hH1⟩, ⟨H', hH'0, hH'1⟩⟩ :=
    preimageIncl_homotopyEquiv_of_deformation p hp A W hAW ρ hρ0 hρ1 hρA
  refine Work.StemsB.isIso_relChainsMapOf_of_homotopyEquiv (X := TopCat.of E)
    (A := p ⁻¹' A) (B := p ⁻¹' W) (preimageIncl p A W hAW) (TopCat.ofHom f) ?_ ?_
    (preimageIncl_subtypeIncl p A W hAW) k
  · have hsym : TopCat.Homotopy (𝟙 (TopCat.of (p ⁻¹' A)))
        (preimageIncl p A W hAW ≫ TopCat.ofHom f) :=
      ContinuousMap.Homotopy.mk ⟨fun z => H' (z.2, z.1), H'.continuous.comp (by fun_prop)⟩
        (fun x => hH'0 x)
        (fun x => by
          show H' (x, 1) = f (preimageIncl p A W hAW x)
          rw [hH'1 x]
          exact congrArg f (Subtype.ext (hgf x)))
    exact hsym.symm
  · have hsym : TopCat.Homotopy (𝟙 (TopCat.of (p ⁻¹' W)))
        (TopCat.ofHom f ≫ preimageIncl p A W hAW) :=
      ContinuousMap.Homotopy.mk ⟨fun z => H (z.2, z.1), H.continuous.comp (by fun_prop)⟩
        (fun x => hH0 x)
        (fun x => by
          show H (x, 1) = preimageIncl p A W hAW (f x)
          rw [hH1 x]
          exact Subtype.ext ((hgf (f x)).trans rfl))
    exact hsym.symm

end Thickening

/-! ## The two thickening steps of the sphere -/

section SphereThickening

variable {E : Type} [TopologicalSpace E]

/-- **The thickening step at the outer piece** `sphLoopOuter n`, based at `∞`. -/
theorem isIso_relChainsMapOf_sphLoopOuter (n : ℕ) (p : C(E, SphModel n))
    (hp : IsHurewiczFibration p) (hAW : {OnePoint.infty} ⊆ sphLoopOuter n) (k : ℕ) :
    IsIso (HomologicalComplex.homologyMap (Work.Cohomology.relChainsMapOf
      (TopCat.of E) (TopCat.of E) (p ⁻¹' {OnePoint.infty}) (p ⁻¹' sphLoopOuter n)
      (𝟙 (TopCat.of E))
      (preimageIncl p {OnePoint.infty} (sphLoopOuter n) hAW)
      (preimageIncl_subtypeIncl p {OnePoint.infty} (sphLoopOuter n) hAW)) k) := by
  obtain ⟨ρ, hρ0, hρ1, hρc⟩ := onePoint_radialPush_outer n
  refine isIso_relChainsMapOf_preimageIncl_of_deformation p hp {OnePoint.infty}
    (sphLoopOuter n) hAW ρ hρ0 ?_ ?_ k
  · intro w
    rw [hρ1 w]
    exact Set.mem_singleton _
  · intro a t
    have ha : (⟨a.1, hAW a.2⟩ : ↥(sphLoopOuter n)) = ⟨OnePoint.infty, Or.inl rfl⟩ :=
      Subtype.ext (Set.mem_singleton_iff.mp a.2)
    rw [ha]
    exact hρc t

/-- **The thickening step at the inner cube** `sphLoopBig n`, based at the collar point
`sphShellPt n`. -/
theorem isIso_relChainsMapOf_sphLoopBig (n : ℕ) (hn : 1 ≤ n) (p : C(E, SphModel n))
    (hp : IsHurewiczFibration p) (hAW : {sphShellPt n} ⊆ sphLoopBig n) (k : ℕ) :
    IsIso (HomologicalComplex.homologyMap (Work.Cohomology.relChainsMapOf
      (TopCat.of E) (TopCat.of E) (p ⁻¹' {sphShellPt n}) (p ⁻¹' sphLoopBig n)
      (𝟙 (TopCat.of E))
      (preimageIncl p {sphShellPt n} (sphLoopBig n) hAW)
      (preimageIncl_subtypeIncl p {sphShellPt n} (sphLoopBig n) hAW)) k) := by
  obtain ⟨c, hc0, hc1, hcc⟩ := serreSphere_contract_big n hn (hAW (Set.mem_singleton _))
  refine isIso_relChainsMapOf_preimageIncl_of_deformation p hp {sphShellPt n}
    (sphLoopBig n) hAW c hc0 ?_ ?_ k
  · intro w
    rw [hc1 w]
    exact Set.mem_singleton _
  · intro a t
    have ha : (⟨a.1, hAW a.2⟩ : ↥(sphLoopBig n)) =
        ⟨sphShellPt n, hAW (Set.mem_singleton _)⟩ :=
      Subtype.ext (Set.mem_singleton_iff.mp a.2)
    rw [ha]
    exact hcc t

end SphereThickening

/-! ## The two excisions for the open cover `(sphLoopOuter, sphLoopBig)` -/

theorem sphLoopOuter_open (n : ℕ) : IsOpen (sphLoopOuter n) := isOpen_sphLoopOuter n

theorem sphLoopBig_open (n : ℕ) : IsOpen (sphLoopBig n) := serreSphere_isOpen_big n

/-- **Excision on the total space.**  The relative chain complex of `(E, E|_Q)` is quasi-isomorphic
to that of `(E|_P, E|_{P∩Q})`, where `P = sphLoopOuter n` and `Q = sphLoopBig n`. -/
theorem isIso_relChainsMap_excision (n : ℕ) {E : Type} [TopologicalSpace E] (p : C(E, SphModel n))
    (k : ℕ) :
    IsIso (HomologicalComplex.homologyMap (Work.Cohomology.relChainsMap (TopCat.of E)
      (p ⁻¹' sphLoopBig n) (p ⁻¹' sphLoopOuter n)) k) :=
  Work.Cohomology.excision_relChainsMap_isIso (TopCat.of E) (p ⁻¹' sphLoopBig n)
    (p ⁻¹' sphLoopOuter n) (sphLoopBig_open n |>.preimage p.continuous)
    (sphLoopOuter_open n |>.preimage p.continuous)
    (by
      rw [← Set.preimage_union, Set.union_comm (sphLoopBig n) (sphLoopOuter n),
        sphLoopOuter_union_sphLoopBig, Set.preimage_univ]) k

/-- **Excision on the base**: the relative chain complex of `(Sᵇ, Q)` is quasi-isomorphic to that
of `(P, P∩Q)`. -/
theorem isIso_relChainsMap_excision_base (n : ℕ) (k : ℕ) :
    IsIso (HomologicalComplex.homologyMap (Work.Cohomology.relChainsMap
      (TopCat.of (SphModel n)) (sphLoopBig n) (sphLoopOuter n)) k) :=
  Work.Cohomology.excision_relChainsMap_isIso (TopCat.of (SphModel n)) (sphLoopBig n)
    (sphLoopOuter n) (sphLoopBig_open n) (sphLoopOuter_open n)
    (by rw [Set.union_comm (sphLoopBig n) (sphLoopOuter n), sphLoopOuter_union_sphLoopBig]) k

/-! ## The thickening on the base -/

/-- The based contraction of `sphLoopOuter n` to `∞`, as a continuous map (chosen witness of
`Work.StemsB.onePoint_radialPush_outer`). -/
def sphLoopOuterContr (n : ℕ) : C(↥(sphLoopOuter n) × unitInterval, ↥(sphLoopOuter n)) :=
  Classical.choose (onePoint_radialPush_outer n)

theorem sphLoopOuterContr_zero (n : ℕ) (w : ↥(sphLoopOuter n)) :
    sphLoopOuterContr n (w, 0) = w := (Classical.choose_spec (onePoint_radialPush_outer n)).1 w

theorem sphLoopOuterContr_one (n : ℕ) (w : ↥(sphLoopOuter n)) :
    sphLoopOuterContr n (w, 1) = ⟨OnePoint.infty, Or.inl rfl⟩ :=
  (Classical.choose_spec (onePoint_radialPush_outer n)).2.1 w

theorem sphLoopOuterContr_fixes (n : ℕ) (t : unitInterval) :
    sphLoopOuterContr n (⟨OnePoint.infty, Or.inl rfl⟩, t) = ⟨OnePoint.infty, Or.inl rfl⟩ :=
  (Classical.choose_spec (onePoint_radialPush_outer n)).2.2 t

/-- The end map of the contraction, as a map onto the singleton `{∞}`. -/
def sphLoopOuterEnd (n : ℕ) : C(↥(sphLoopOuter n), ↥({OnePoint.infty} : Set (SphModel n))) :=
  ⟨fun w => ⟨(sphLoopOuterContr n (w, 1)).1, by
      have h := congrArg Subtype.val (sphLoopOuterContr_one n w)
      rw [h]
      exact Set.mem_singleton _⟩, by
    refine Continuous.subtype_mk ?_ _
    fun_prop⟩

/-- **The thickening step on the base**: for the identity map of the model, the inclusion
`{∞} ↪ sphLoopOuter n` is a homotopy equivalence (the outer piece is based-contractible to `∞`), so
`C_*(Sᵇ, {∞}) → C_*(Sᵇ, sphLoopOuter n)` is a quasi-isomorphism. -/
theorem isIso_relChainsMapOf_self_sphLoopOuter (n : ℕ)
    (hAW : {OnePoint.infty} ⊆ sphLoopOuter n) (k : ℕ) :
    IsIso (HomologicalComplex.homologyMap (Work.Cohomology.relChainsMapOf
      (TopCat.of (SphModel n)) (TopCat.of (SphModel n)) {OnePoint.infty} (sphLoopOuter n)
      (𝟙 (TopCat.of (SphModel n)))
      (preimageIncl (ContinuousMap.id (SphModel n)) {OnePoint.infty} (sphLoopOuter n) hAW)
      (preimageIncl_subtypeIncl (ContinuousMap.id (SphModel n)) {OnePoint.infty}
        (sphLoopOuter n) hAW)) k) := by
  have hgf : TopCat.Homotopy
      (preimageIncl (ContinuousMap.id (SphModel n)) {OnePoint.infty} (sphLoopOuter n) hAW
        ≫ TopCat.ofHom (sphLoopOuterEnd n))
      (𝟙 (TopCat.of ↥({OnePoint.infty} : Set (SphModel n)))) := by
    refine topCatHomotopyOf (X := TopCat.of ↥({OnePoint.infty} : Set (SphModel n)))
      (Y := TopCat.of (↥(sphLoopOuter n)))
      (f := preimageIncl (ContinuousMap.id (SphModel n)) {OnePoint.infty} (sphLoopOuter n) hAW)
      (g := TopCat.ofHom (sphLoopOuterEnd n))
      ⟨fun _ => (⟨OnePoint.infty, Set.mem_singleton _⟩ :
        ↥({OnePoint.infty} : Set (SphModel n))), continuous_const⟩ ?_ ?_
    · intro x; exact Subsingleton.elim _ _
    · intro x; exact Subsingleton.elim _ _
  refine Work.StemsB.isIso_relChainsMapOf_of_homotopyEquiv (X := TopCat.of (SphModel n))
    (A := {OnePoint.infty}) (B := sphLoopOuter n)
    (preimageIncl (ContinuousMap.id (SphModel n)) {OnePoint.infty} (sphLoopOuter n) hAW)
    (TopCat.ofHom (sphLoopOuterEnd n)) hgf ?_
    (preimageIncl_subtypeIncl (ContinuousMap.id (SphModel n)) {OnePoint.infty}
      (sphLoopOuter n) hAW) k
  · refine topCatHomotopyOf (X := TopCat.of (↥(sphLoopOuter n)))
      (Y := TopCat.of ↥({OnePoint.infty} : Set (SphModel n)))
      (f := TopCat.ofHom (sphLoopOuterEnd n))
      (g := preimageIncl (ContinuousMap.id (SphModel n)) {OnePoint.infty}
        (sphLoopOuter n) hAW)
      (sphLoopOuterContr n) ?_ ?_
    · intro w; exact sphLoopOuterContr_zero n w
    · intro w
      show sphLoopOuterContr n (w, 1) = preimageIncl (ContinuousMap.id (SphModel n))
        {OnePoint.infty} (sphLoopOuter n) hAW (sphLoopOuterEnd n w)
      rw [sphLoopOuterContr_one n w]
      exact Subtype.ext (by
        show OnePoint.infty = (sphLoopOuterEnd n w).1
        rw [show (sphLoopOuterEnd n w).1 = (sphLoopOuterContr n (w, 1)).1 from rfl]
        exact (congrArg Subtype.val (sphLoopOuterContr_one n w)).symm)

end

end Work.StemsB
