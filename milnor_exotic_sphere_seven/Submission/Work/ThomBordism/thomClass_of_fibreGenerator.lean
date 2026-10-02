import Mathlib
import Submission.Work.ThomBordism.thomClassFibreDefs
import Submission.Work.ThomBordism.localThom_of_fibreGenerator_chart
import Submission.Work.ThomBordism.localThom_iUnion_of_fibreGenerator
import Submission.Work.ThomBordism.thomClass_of_fibreGenerator_zero
import Submission.Work.Thom.localThom_union
import Submission.Work.Thom.openThom_eq_zero_of_baseSet_rank
import Submission.Work.Thom.subsingleton_PieceCoh_of_lt_finrank

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 400000

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1600000
set_option linter.unusedSectionVars false

/-!
# A fibre generator of the Thom pair at the rank degree is a Thom class

`Work.ThomBordism.thomClass_of_fibreGenerator`: for a real bundle `Z → B` of rank `n` and a class
`σ ∈ H^n(E, E∖0;ℤ)` whose restriction to every fibre pair `(Z_b, Z_b∖0) ≅ (D^n, S^{n-1})` is a
generator, the Thom map `x ↦ π^*(x) ⌣ σ` is bijective in every degree (the Leray–Hirsch direction
of the equivalence of the two definitions of a Thom class, Hatcher Cor. 4D.9).

## The proof

* `Work.ThomBordism.localThom_of_fibreGenerator_chart` (delegated): on a chart piece the
  restriction of `σ` is a local Thom class — the trivial-bundle (Leray–Hirsch) core of the
  argument, where the fibre-generator hypothesis enters.
* `Work.ThomBordism.localThom_iUnion_of_fibreGenerator` (delegated): the local Thom property
  passes to unions of chains of open pieces.  This is the transfinite patching step; the rank
  hypothesis is what makes it true (`Subsingleton (PieceCoh Z W (n - 1))` for *arbitrary* `W`,
  `Work.Thom.subsingleton_PieceCoh_of_lt_finrank`), and it is false without it.
* `Work.Thom.localThom_union` (two pieces, with the same low-degree vanishing) and Zorn's lemma:
  the local Thom property is closed under adjoining one chart piece, so a maximal piece is the
  whole base (`isLocalThom_univ`).
* `Work.Thom.thomMap_restrict` at `Set.univ` plus the identifications of the piece over `univ`
  with the base and the Thom pair: a local Thom class over `univ` is a Thom class
  (`thomMap_bijective_of_isLocalThom_univ`).
* the rank-`0` case is `Work.ThomBordism.thomClass_of_fibreGenerator_zero` (delegated).

-/

namespace Work.ThomBordism

open Work.TangentClasses

noncomputable section

variable {B : Type} [TopologicalSpace B] {F : Type} [NormedAddCommGroup F] [NormedSpace ℝ F]
variable [FiniteDimensional ℝ F]
variable {ι : Type} {n : ℕ}

/-- "`σ` restricted to `W` is a local Thom class": the local Thom map of `σ|_W` is bijective in
every degree. -/
def isLocalThom (Z : RealBundle B F ι) (n : ℕ) (σ : Work.Thom.OpenThom Z n) (W : Set B) : Prop :=
  ∀ k : ℕ, Function.Bijective
    (Work.Thom.localThomMap Z n W ((Work.Thom.PieceRes Z W n).hom σ) k)

/-- The local Thom property passes to unions of chains of open pieces (the patching step). -/
def Crux (Z : RealBundle B F ι) (n : ℕ) (σ : Work.Thom.OpenThom Z n) : Prop :=
  ∀ (C : Set (Set B)), (∀ W ∈ C, IsOpen W) → (∀ W ∈ C, ∀ W' ∈ C, W ⊆ W' ∨ W' ⊆ W) →
    (∀ W (_hW : W ∈ C), isLocalThom Z n σ W) → isLocalThom Z n σ (⋃₀ C)

/-- **The two-piece step**, in the form needed by the Zorn argument: adjoining one chart piece. -/
theorem isLocalThom_union_baseSet (Z : RealBundle B F ι) (n : ℕ) (hn : 1 ≤ n)
    (hr : n = Module.finrank ℝ F) (σ : Work.Thom.OpenThom Z n)
    (hchart : ∀ (i : ι) (W : Set B), W ⊆ Z.baseSet i → isLocalThom Z n σ W)
    {W : Set B} (hW : IsOpen W) (hP : isLocalThom Z n σ W) (i : ι) :
    isLocalThom Z n σ (W ∪ Z.baseSet i) := by
  have hU : IsOpen (Z.baseSet i) := Z.isOpen_baseSet i
  have hPU : isLocalThom Z n σ (Z.baseSet i) := hchart i _ subset_rfl
  have hPI : isLocalThom Z n σ (W ∩ Z.baseSet i) := hchart i _ Set.inter_subset_right
  have hlow : Subsingleton (Work.Thom.PieceCoh Z (W ∩ Z.baseSet i) (n - 1)) :=
    Work.Thom.subsingleton_PieceCoh_of_lt_finrank Z _ (by omega)
  have hlow' : Subsingleton (Work.Cohomology.pdCohSub (TopCat.of Z.TotalSpace)
      (Work.Thom.zeroComplement Z) ((Z.proj ⁻¹' W) ∩ (Z.proj ⁻¹' Z.baseSet i)) (n - 1)) := by
    rw [← Set.preimage_inter]
    exact hlow
  obtain ⟨c, hc, hcW, hcU⟩ := Work.Thom.localThom_union Z n hn hW hU
    ((Work.Thom.PieceRes Z W n).hom σ) hP
    ((Work.Thom.PieceRes Z (Z.baseSet i) n).hom σ) hPU
    ((Work.Thom.PieceRes Z (W ∩ Z.baseSet i) n).hom σ) hPI
    (Work.Thom.PieceRes_eq_pdCohMap Z n Set.inter_subset_left σ).symm
    (Work.Thom.PieceRes_eq_pdCohMap Z n Set.inter_subset_right σ).symm hlow
  have hEq : c = (Work.Thom.PieceRes Z (W ∪ Z.baseSet i) n).hom σ := by
    have key := Work.Thom.pdCohSub_pdCohMap_biprod_injective (X := TopCat.of Z.TotalSpace)
      (A := Work.Thom.zeroComplement Z) (W := Z.proj ⁻¹' (W ∪ Z.baseSet i))
      (U := Z.proj ⁻¹' W) (V := Z.proj ⁻¹' Z.baseSet i)
      (hUW := Set.preimage_mono Set.subset_union_left)
      (hVW := Set.preimage_mono Set.subset_union_right)
      (hU := hW.preimage Z.continuous_proj) (hV := hU.preimage Z.continuous_proj)
      (hcov := by rw [Set.preimage_union]) n hlow'
    have hWres : (ModuleCat.Hom.hom (Work.Cohomology.pdCohMap (TopCat.of Z.TotalSpace)
        (Work.Thom.zeroComplement Z) (Z.proj ⁻¹' (W ∪ Z.baseSet i)) (Z.proj ⁻¹' W)
        (Set.preimage_mono Set.subset_union_left) n))
        ((Work.Thom.PieceRes Z (W ∪ Z.baseSet i) n).hom σ)
        = (Work.Thom.PieceRes Z W n).hom σ :=
      (Work.Thom.PieceRes_eq_pdCohMap Z n Set.subset_union_left σ).symm
    have hUres : (ModuleCat.Hom.hom (Work.Cohomology.pdCohMap (TopCat.of Z.TotalSpace)
        (Work.Thom.zeroComplement Z) (Z.proj ⁻¹' (W ∪ Z.baseSet i)) (Z.proj ⁻¹' Z.baseSet i)
        (Set.preimage_mono Set.subset_union_right) n))
        ((Work.Thom.PieceRes Z (W ∪ Z.baseSet i) n).hom σ)
        = (Work.Thom.PieceRes Z (Z.baseSet i) n).hom σ :=
      (Work.Thom.PieceRes_eq_pdCohMap Z n Set.subset_union_right σ).symm
    have hdiff : c - (Work.Thom.PieceRes Z (W ∪ Z.baseSet i) n).hom σ = 0 := by
      apply key
      simp only [map_sub, map_zero]
      rw [Prod.mk.injEq]
      exact ⟨by rw [hcW, hWres]; exact sub_self _,
             by rw [hcU, hUres]; exact sub_self _⟩
    exact sub_eq_zero.mp hdiff
  rw [hEq] at hc
  exact hc

/-- **The Zorn argument**: from the patching step and the chart-local statement, `σ` is a local
Thom class over the whole base. -/
theorem isLocalThom_univ (Z : RealBundle B F ι) (n : ℕ) (hn : 1 ≤ n)
    (hr : n = Module.finrank ℝ F) (σ : Work.Thom.OpenThom Z n)
    (hcrux : Crux Z n σ)
    (hchart : ∀ (i : ι) (W : Set B), W ⊆ Z.baseSet i → isLocalThom Z n σ W) :
    isLocalThom Z n σ Set.univ := by
  classical
  let S : Set (Set B) := {W | IsOpen W ∧ isLocalThom Z n σ W}
  have hZorn : ∀ c ⊆ S, IsChain (· ⊆ ·) c → ∃ ub ∈ S, ∀ s ∈ c, s ⊆ ub := by
    intro c hc hchain
    have htot : ∀ s ∈ c, ∀ s' ∈ c, s ⊆ s' ∨ s' ⊆ s := by
      intro s hs s' hs'
      rcases eq_or_ne s s' with h | h
      · exact Or.inl (le_of_eq h)
      · exact hchain hs hs' h
    refine ⟨⋃₀ c, ⟨isOpen_sUnion fun s hs => (hc hs).1, ?_⟩,
      fun s hs => Set.subset_sUnion_of_mem hs⟩
    exact hcrux c (fun s hs => (hc hs).1) htot (fun s hs => (hc hs).2)
  obtain ⟨m, hm⟩ := zorn_subset S hZorn
  have hmS : m ∈ S := hm.1
  have hmax : ∀ a ∈ S, m ⊆ a → a ⊆ m := hm.2
  have huniv : m = Set.univ := by
    by_contra hne
    have hb : ∃ b, b ∉ m := by
      by_contra h
      push_neg at h
      exact hne (Set.eq_univ_of_forall h)
    obtain ⟨b, hb⟩ := hb
    have hstep : isLocalThom Z n σ (m ∪ Z.baseSet (Z.indexAt b)) :=
      isLocalThom_union_baseSet Z n hn hr σ hchart hmS.1 hmS.2 (Z.indexAt b)
    have hSm : m ∪ Z.baseSet (Z.indexAt b) ∈ S :=
      ⟨hmS.1.union (Z.isOpen_baseSet _), hstep⟩
    have hle : m ∪ Z.baseSet (Z.indexAt b) ⊆ m := hmax _ hSm Set.subset_union_left
    exact hb (hle (Set.mem_union_right m (Z.mem_baseSet_at b)))
  have : Set.univ ∈ S := huniv ▸ hmS
  exact this.2

/-- **The final bookkeeping**: a local Thom class over `Set.univ` is a Thom class. -/
theorem thomMap_bijective_of_isLocalThom_univ (Z : RealBundle B F ι) (n : ℕ)
    (σ : Work.Thom.OpenThom Z n) (h : isLocalThom Z n σ Set.univ) :
    ∀ k, Function.Bijective (Work.Thom.thomMap Z n σ k) := by
  intro k
  have hloc := h k
  have hres_inj : Function.Injective (Work.Thom.PieceRes Z (Set.univ : Set B) (k+n)).hom := by
    show Function.Injective (Work.Cohomology.pdCohRes (TopCat.of Z.TotalSpace)
      (Work.Thom.zeroComplement Z) (Z.proj ⁻¹' (Set.univ : Set B)) (k+n)).hom
    rw [Set.preimage_univ]
    exact Work.Thom.pdCohRes_univ_injective (Work.Thom.zeroComplement Z) (k+n)
  let φ : C(B, ↥(Set.univ : Set B)) :=
    ⟨fun b => ⟨b, Set.mem_univ b⟩, continuous_id.subtype_mk _⟩
  let g : C(↥(Set.univ : Set B), B) := Work.Thom.subtypeMap Set.univ
  have hgφ : g.comp φ = ContinuousMap.id B := by ext b; rfl
  have hφg : φ.comp g = ContinuousMap.id ↥(Set.univ : Set B) := by ext b; rfl
  have hCoh_bij : Function.Bijective (Work.Thom.CohMap g ℤ k).hom := by
    have h1 : ((Work.Thom.CohMap g ℤ k).hom).comp ((Work.Thom.CohMap φ ℤ k).hom)
        = LinearMap.id := by
      have h := Work.Thom.CohMap_comp g φ ℤ k
      rw [hφg, Work.Thom.CohMap_id] at h
      have h2 := congrArg (fun f : Work.Thom.Coh ℤ k ↥(Set.univ : Set B) ⟶
        Work.Thom.Coh ℤ k ↥(Set.univ : Set B) => f.hom) h.symm
      simpa [ModuleCat.hom_comp, ModuleCat.hom_id] using h2
    have h2 : ((Work.Thom.CohMap φ ℤ k).hom).comp ((Work.Thom.CohMap g ℤ k).hom)
        = LinearMap.id := by
      have h := Work.Thom.CohMap_comp φ g ℤ k
      rw [hgφ, Work.Thom.CohMap_id] at h
      have h3 := congrArg (fun f : Work.Thom.Coh ℤ k B ⟶ Work.Thom.Coh ℤ k B => f.hom) h.symm
      simpa [ModuleCat.hom_comp, ModuleCat.hom_id] using h3
    constructor
    · intro a b hab
      have ha := LinearMap.congr_fun h2 a
      have hb := LinearMap.congr_fun h2 b
      simp only [LinearMap.comp_apply, LinearMap.id_apply] at ha hb
      rw [hab] at ha
      exact ha.symm.trans hb
    · intro b
      exact ⟨(Work.Thom.CohMap φ ℤ k).hom b, LinearMap.congr_fun h1 b⟩
  constructor
  · intro x y hxy
    have hz : (Work.Thom.localThomMap Z n Set.univ ((Work.Thom.PieceRes Z Set.univ n).hom σ) k)
        ((Work.Thom.CohMap g ℤ k).hom x)
        = (Work.Thom.localThomMap Z n Set.univ ((Work.Thom.PieceRes Z Set.univ n).hom σ) k)
          ((Work.Thom.CohMap g ℤ k).hom y) := by
      rw [← Work.Thom.thomMap_restrict Z n k Set.univ σ x,
        ← Work.Thom.thomMap_restrict Z n k Set.univ σ y, hxy]
    exact hCoh_bij.1 (hloc.1 hz)
  · intro y
    obtain ⟨x', hx'⟩ := hloc.2 ((Work.Thom.PieceRes Z Set.univ (k+n)).hom y)
    obtain ⟨x, hx⟩ := hCoh_bij.2 x'
    refine ⟨x, hres_inj ?_⟩
    rw [Work.Thom.thomMap_restrict Z n k Set.univ σ x, hx, hx']

/-- **The patching step for `σ`**: the local Thom property passes to unions of chains. -/
theorem crux_of_fibreGenerator (Z : RealBundle B F ι) (n : ℕ)
    (hn : n = Module.finrank ℝ F) (σ : Work.Thom.OpenThom Z n)
    (hσ : IsFibreGenerator Z n σ) : Crux Z n σ := by
  intro C hC hchain h
  exact localThom_iUnion_of_fibreGenerator Z σ hn hσ C hC hchain
    (fun W hW k => by
      rw [← Work.Thom.PieceRes_eq_pdCohMap Z n (Set.subset_sUnion_of_mem hW) σ]
      exact h W hW k)

theorem thomClass_of_fibreGenerator {B : Type} [TopologicalSpace B] {F : Type} [NormedAddCommGroup F]
    [NormedSpace ℝ F] [FiniteDimensional ℝ F] {ι : Type} {n : ℕ}
    (Z : Work.TangentClasses.RealBundle B F ι) (σ : Work.Thom.OpenThom Z n)
    (hn : n = Module.finrank ℝ F) (h : Work.ThomBordism.IsFibreGenerator Z n σ) :
    ∀ k : ℕ, Function.Bijective (Work.Thom.thomMap Z n σ k) := by
  rcases Nat.eq_zero_or_pos n with hn0 | hpos
  · subst hn0
    exact thomClass_of_fibreGenerator_zero Z σ hn h
  · exact thomMap_bijective_of_isLocalThom_univ Z n σ
      (isLocalThom_univ Z n hpos hn σ (crux_of_fibreGenerator Z n hn σ h)
        (localThom_of_fibreGenerator_chart Z σ hn h))

end

end Work.ThomBordism
