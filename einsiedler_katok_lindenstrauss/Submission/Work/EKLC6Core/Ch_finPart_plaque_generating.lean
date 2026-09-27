import Mathlib
import Submission.Work.EKLC6Core.Basic
import Submission.Work.EKLC6Core.plaquePartitionAux
import Submission.Work.EKLC6Core.finPart_plaquePast_exists
import Submission.Work.EKLC6Core.exists_covering_thin_inj_partition
import Submission.Work.EKLC6Core.plaqueAlgebra_of_ae_pointwise
import Submission.Work.EKLC6Core.ae_free_orbit_of_contraction

/-!
# `Work.EKLC6Core.Ch_finPart_plaque_generating`

The frozen target and its assembly from the workspace's (axiom-clean) machinery plus two
external inputs, each stated and delegated separately.

* **the thin cover** (`Work.EKLC6Core.exists_covering_thin_inj_partition`, PROVED): for every
  `ε ∈ (0,1)` there are pieces `Q : Fin N → Set X₃`, an index `i₀` with `μ (Q i₀) < ε`, centres
  `g`, a radius `ρ` and a constant `c` with the `V ρ`-ball containments, `Γ₃`-freeness of the
  centres and the thin-frontier bound.

* **the shape data** (`Work.EKLC6Core.Ch_piece_bdd_thin_cover`, delegated): the boundedness of
  the `Uminus t`-shape of the `partSigma`-atom at free points of the pieces.

* **the atom bound** (`Work.EKLC6Core.Ch_hsep_thin_cover`, delegated): a.e. the atom of
  `pastSigFinPart t P` is contained in the `Uminus t`-orbit of its point.

The one-sided plaque-algebra clause is assembled here from these via the PROVED
`ae_isOpen_shape_pastSigFinPart_of_thin_inj_data`, `ae_hbdd_of_pieces` and
`plaqueAlgebra_of_ae_pointwise`; the generation half is reproduced in this file (see
`Ch_genFinPartPlaque_of_twoSided`).
-/


/-!
## FINDINGS (why this finite-partition form is mis-stated)

The target is the *finite*-partition form of Einsiedler–Lindenstrauss (Pisa notes) Prop. 7.37/7.38
+ 7.43.  The source proves the **countable**-partition form, and in the remark following 7.53 it
explicitly *declines* the finite one: "If however, we have `μ(Q_n) = 0` for all but finitely many
`n`, then `P` is actually a finite partition mod `μ` and **the last statement may not hold**",
repairing it by refining to a countably infinite partition with rapidly decaying pieces.

Concretely, the obstruction is the centraliser `C(aDiag t)`.  For `y ∈ atom (pastSigFinPart t P) x`
one only gets `y = u·c·x` with `u ∈ Uminus t` and `c ∈ C(aDiag t)`
(`Work.EKLC6Core.mem_uminus_of_shadowing`), i.e. `c ∈ C` must be killed.  The source kills it by
intersecting over *infinitely many scales*: for a partition element `Q_{n₀}` visited infinitely
often, the displacement satisfies `h ∈ B(e^{-α n₀} r / 2)`, and `⋂_{n₀} B(e^{-α n₀} r/2) = {e}`
because `n₀ → ∞`.  This needs pieces of arbitrarily small size — inexpressible in `FinPart`
(finitely many parts of fixed size).  Correspondingly, the workspace's proven machinery for the
atom bound (`pin_of_finitely_many_reps`, `mem_uminus_of_shadowing`) needs displacements that are
`V (ε k)`-small with `ε k → 0`, i.e. exactly the shrinking pieces.

This is *not* repairable by the non-degeneracy hypotheses of the target (`hne`, `hent`):

* the delegated piece `Ch_hsep_thin_cover` (the atom bound for the thin-cover data) was refuted
  by its prover: a cover whose adapted partition has both non-empty parts *invariant* under
  `c₀ = diag(1,-1,-1) ∈ Γ₃ ∩ C(aDiag t)` satisfies all hypotheses while `c₀·x ∈ atom x` and
  `c₀ ∉ Uminus t`, so the atom is not contained in the `Uminus t`-orbit;
* the delegated piece `Ch_bdd_thin_cover` (boundedness of the `Uminus t`-shape) was refuted
  formally in `Submission/Work/EKLC6Core/_bdd_thin_cover_refute.lean` (axiom-clean): the
  one-piece cover `Q ≡ X₃` satisfies all hypotheses (`hthin` because `frontier X₃ = ∅`) while
  `shape (partSigma (adaptedPart Q hdisj)) (Uminus t) x = Uminus t` is unbounded.  Moreover, for
  a `Uminus t`-invariant `μ` (the source's setting) the *level-`0`* shape is unbounded a.e., so
  the standard margin route to the *openness* of the shape is unavailable for a finite partition;
* the same statement was independently declared mis-stated by two earlier provers of this
  workspace (`Work.EKLC6Core.exists_finPart_plaquePast_generating`, and
  `..._generating_alt`), for the same reason.

What IS proved in this file (sorry-free, and independent of the above): the *generation* half of
the statement — the bi-infinite orbit σ-algebra is the join of the past and future σ-algebras
(`Ch_biOrbitFinPart_eq_sup`), its countable generation
(`Ch_cg_biOrbitFinPart`), the mod-`μ` separation criterion
(`Ch_exists_measurableSet_ae_eq_of_atom_singleton`) and the reduction
`Ch_genFinPartPlaque_of_twoSided`: two-sided plaque data (plus the two-sided fibre condition)
yield `GeneratesModMu`.  So the *only* missing input for a two-sided proof is the one-sided
plaque-algebra clause — which is exactly the part that fails/falters for a finite `FinPart`.
-/

open MeasureTheory Filter
open scoped ENNReal

noncomputable section

set_option linter.unusedVariables false
set_option linter.style.haveILetI false

namespace Work.EKLC6Core

open Work.EKLContract

/-! ## 1. The generation half (reproduced from the workspace's proven module
`Work.EKLC6Core.genFinPartPlaque`, under local names so that this file builds independently) -/

/-- A point lies in its own atom. -/
theorem Ch_mem_atom_self (m : MeasurableSpace X3) (x : X3) : x ∈ atom m x :=
  Set.mem_sInter.mpr fun _ hs => hs.2

/-- **Atoms of a join** are the intersections of the atoms. -/
theorem Ch_atom_sup_eq {m m' : MeasurableSpace X3} (x : X3) :
    atom (m ⊔ m') x = atom m x ∩ atom m' x := by
  ext y
  rw [Set.mem_inter_iff, mem_atom_iff, mem_atom_iff, mem_atom_iff]
  constructor
  · intro h
    exact ⟨fun s hs => h s ((MeasurableSpace.le_def.mp le_sup_left) s hs),
      fun s hs => h s ((MeasurableSpace.le_def.mp le_sup_right) s hs)⟩
  · rintro ⟨h1, h2⟩ s hs
    let A : MeasurableSpace X3 :=
      { MeasurableSet' := fun s => (x ∈ s ↔ y ∈ s)
        measurableSet_empty := by simp
        measurableSet_compl := by
          intro s hs
          simp only [Set.mem_compl_iff]
          exact not_iff_not.mpr hs
        measurableSet_iUnion := by
          intro f hf
          simp only [Set.mem_iUnion]
          exact ⟨fun h => h.imp fun n hn => (hf n).mp hn,
            fun h => h.imp fun n hn => (hf n).mpr hn⟩ }
    exact (MeasurableSpace.le_def.mp (sup_le (fun s hs => h1 s hs) (fun s hs => h2 s hs))) s hs

/-- The bi-infinite orbit σ-algebra is the join of the past and the future σ-algebra. -/
theorem Ch_biOrbitFinPart_eq_sup (t : Fin 3 → ℝ) (P : FinPart X3) :
    biOrbitFinPart t P = pastSigFinPart t P ⊔ pastSigFinPart (-t) P := by
  rw [biOrbitFinPart, pastSigFinPart, pastSigFinPart, iSup_sup_eq]

/-- The σ-algebra of a finite partition is countably generated. -/
theorem Ch_cg_partSigma (P : FinPart X3) :
    ∃ b : Set (Set X3), b.Countable ∧ partSigma P = MeasurableSpace.generateFrom b :=
  ⟨Set.range P.parts, Set.countable_range _, rfl⟩

/-- The pullback of a countably generated σ-algebra is countably generated. -/
theorem Ch_cg_comap {m : MeasurableSpace X3} (f : X3 → X3)
    (h : ∃ b : Set (Set X3), b.Countable ∧ m = MeasurableSpace.generateFrom b) :
    ∃ b : Set (Set X3), b.Countable ∧
      MeasurableSpace.comap f m = MeasurableSpace.generateFrom b := by
  obtain ⟨b, hb, rfl⟩ := h
  exact ⟨(fun s : Set X3 => f ⁻¹' s) '' b, hb.image _, MeasurableSpace.comap_generateFrom⟩

/-- The supremum of two countably generated σ-algebras is countably generated. -/
theorem Ch_cg_sup {m m' : MeasurableSpace X3}
    (h : ∃ b : Set (Set X3), b.Countable ∧ m = MeasurableSpace.generateFrom b)
    (h' : ∃ b : Set (Set X3), b.Countable ∧ m' = MeasurableSpace.generateFrom b) :
    ∃ b : Set (Set X3), b.Countable ∧ (m ⊔ m') = MeasurableSpace.generateFrom b := by
  obtain ⟨b, hb, rfl⟩ := h
  obtain ⟨b', hb', rfl⟩ := h'
  refine ⟨b ∪ b', hb.union hb', ?_⟩
  refine le_antisymm (sup_le ?_ ?_) (MeasurableSpace.generateFrom_le ?_)
  · exact MeasurableSpace.generateFrom_mono Set.subset_union_left
  · exact MeasurableSpace.generateFrom_mono Set.subset_union_right
  · rintro s (hs | hs)
    · exact (MeasurableSpace.le_def.mp le_sup_left) s
        (MeasurableSpace.measurableSet_generateFrom hs)
    · exact (MeasurableSpace.le_def.mp le_sup_right) s
        (MeasurableSpace.measurableSet_generateFrom hs)

/-- The supremum of countably many countably generated σ-algebras is countably generated. -/
theorem Ch_cg_iSup {A : ℕ → MeasurableSpace X3}
    (h : ∀ n, ∃ b : Set (Set X3), b.Countable ∧ A n = MeasurableSpace.generateFrom b) :
    ∃ b : Set (Set X3), b.Countable ∧ (⨆ n, A n) = MeasurableSpace.generateFrom b := by
  choose b hb hA using h
  refine ⟨⋃ n, b n, Set.countable_iUnion hb, ?_⟩
  rw [show (⨆ n, A n) = ⨆ n, MeasurableSpace.generateFrom (b n) from iSup_congr hA]
  rw [MeasurableSpace.iSup_generateFrom]

/-- The bi-infinite orbit σ-algebra is countably generated. -/
theorem Ch_cg_biOrbitFinPart (t : Fin 3 → ℝ) (P : FinPart X3) :
    ∃ b : Set (Set X3), b.Countable ∧ biOrbitFinPart t P = MeasurableSpace.generateFrom b := by
  have h : (⨆ n : ℕ, (MeasurableSpace.comap ((fun x : X3 => aDiag t • x)^[n]) (partSigma P) ⊔
      MeasurableSpace.comap ((fun x : X3 => aDiag (-t) • x)^[n]) (partSigma P)))
      = biOrbitFinPart t P := rfl
  rw [← h]
  exact Ch_cg_iSup (fun n => Ch_cg_sup (Ch_cg_comap _ (Ch_cg_partSigma P))
      (Ch_cg_comap _ (Ch_cg_partSigma P)))

/-- The bi-infinite orbit σ-algebra is a sub-σ-algebra of the Borel σ-algebra. -/
theorem Ch_biOrbitFinPart_le_borel (t : Fin 3 → ℝ) (P : FinPart X3) :
    biOrbitFinPart t P ≤ instMeasurableSpaceX3 := by
  rw [Ch_biOrbitFinPart_eq_sup]
  exact sup_le (pastSigFinPart_le t P) (pastSigFinPart_le (-t) P)

/-- **The mod-`μ` separation criterion.** -/
theorem Ch_exists_measurableSet_ae_eq_of_atom_singleton {α : Type*} [mα : MeasurableSpace α]
    (hSB : @StandardBorelSpace α mα) {μ : MeasureTheory.Measure α}
    [MeasureTheory.IsProbabilityMeasure μ]
    (S : SigWrap α) (hm : S.m ≤ mα)
    (hcg : ∃ b : Set (Set α), b.Countable ∧ S.m = MeasurableSpace.generateFrom b)
    (Z : Set α) (hZ : @MeasurableSet α mα Z) (hZc : μ Zᶜ = 0)
    (hatom : ∀ x ∈ Z, ∀ y : α, (∀ s : Set α, MeasurableSet[S.m] s → x ∈ s → y ∈ s) → y = x) :
    ∀ E : Set α, @MeasurableSet α mα E →
      ∃ E' : Set α, MeasurableSet[S.m] E' ∧ μ (E \ E') = 0 ∧ μ (E' \ E) = 0 := by
  classical
  haveI hSB' : StandardBorelSpace α := hSB
  haveI hSBsub : StandardBorelSpace ↥Z := hZ.standardBorel
  let SZ : SigWrap ↥Z := ⟨MeasurableSpace.comap (Subtype.val : ↥Z → α) S.m⟩
  have hcgZ : ∃ b : Set (Set ↥Z), b.Countable ∧ SZ.m = MeasurableSpace.generateFrom b := by
    obtain ⟨b, hbc, hbm⟩ := hcg
    refine ⟨(fun s : Set α => Subtype.val ⁻¹' s) '' b, hbc.image _, ?_⟩
    show MeasurableSpace.comap (Subtype.val : ↥Z → α) S.m = _
    rw [hbm, MeasurableSpace.comap_generateFrom]
  haveI hcgZi : @MeasurableSpace.CountablyGenerated ↥Z SZ.m :=
    @MeasurableSpace.CountablyGenerated.mk ↥Z SZ.m hcgZ
  have hsepZ : @MeasurableSpace.SeparatesPoints ↥Z SZ.m :=
    @MeasurableSpace.SeparatesPoints.mk ↥Z SZ.m (fun x y h => by
      have h' : ∀ s : Set α, MeasurableSet[S.m] s → (x : α) ∈ s → (y : α) ∈ s := by
        intro s hs hxs
        exact h (Subtype.val ⁻¹' s) (MeasurableSpace.measurableSet_comap.mpr ⟨s, hs, rfl⟩) hxs
      exact Subtype.ext ((hatom (x : α) x.2 (y : α) h').symm))
  haveI hcsZi : @MeasurableSpace.CountablySeparated ↥Z SZ.m :=
    @MeasurableSpace.countablySeparated_of_separatesPoints ↥Z SZ.m hcgZi hsepZ
  have hle : SZ.m ≤ (inferInstance : MeasurableSpace ↥Z) := by
    show MeasurableSpace.comap (Subtype.val : ↥Z → α) S.m ≤
      MeasurableSpace.comap (Subtype.val : ↥Z → α) mα
    exact MeasurableSpace.comap_mono hm
  have hmeas : @Measurable ↥Z ↥Z (inferInstance : MeasurableSpace ↥Z) SZ.m id := by
    rw [measurable_iff_comap_le, MeasurableSpace.comap_id]
    exact hle
  have hemb : @MeasurableEmbedding ↥Z ↥Z (inferInstance : MeasurableSpace ↥Z) SZ.m id :=
    @Measurable.measurableEmbedding ↥Z ↥Z SZ.m id hcsZi _ _ hmeas (fun _ _ h => h)
  have hcomap : SZ.m = (inferInstance : MeasurableSpace ↥Z) := by
    have h := @MeasurableEmbedding.comap_eq ↥Z ↥Z (inferInstance : MeasurableSpace ↥Z) SZ.m id hemb
    rwa [MeasurableSpace.comap_id] at h
  intro E hE
  have hs : @MeasurableSet ↥Z SZ.m (Subtype.val ⁻¹' E) := by
    rw [hcomap]
    exact MeasurableSpace.measurableSet_comap.mpr ⟨E, hE, rfl⟩
  obtain ⟨t, htm, ht⟩ := MeasurableSpace.measurableSet_comap.mp hs
  refine ⟨t, htm, ?_, ?_⟩
  · refine measure_mono_null (fun x hx => ?_) hZc
    intro hxZ
    have h1 : (⟨x, hxZ⟩ : ↥Z) ∈ Subtype.val ⁻¹' E := hx.1
    rw [← ht] at h1
    exact hx.2 (show x ∈ t from h1)
  · refine measure_mono_null (fun x hx => ?_) hZc
    intro hxZ
    have h1 : (⟨x, hxZ⟩ : ↥Z) ∈ Subtype.val ⁻¹' t := hx.1
    rw [ht] at h1
    exact hx.2 (show x ∈ E from h1)

/-- **The generator criterion.** -/
theorem Ch_generatesModMu_of_atom_singleton {μ : MeasureTheory.Measure X3}
    [MeasureTheory.IsProbabilityMeasure μ] (hSB : @StandardBorelSpace X3 instMeasurableSpaceX3)
    (t : Fin 3 → ℝ) (P : FinPart X3) (Z : Set X3) (hZ : MeasurableSet Z) (hZc : μ Zᶜ = 0)
    (hatom : ∀ x ∈ Z, atom (biOrbitFinPart t P) x = {x}) :
    GeneratesModMu μ t P := by
  intro E hE
  obtain ⟨E', hE', h1, h2⟩ :=
    Ch_exists_measurableSet_ae_eq_of_atom_singleton (μ := μ) hSB
      ⟨biOrbitFinPart t P⟩ (Ch_biOrbitFinPart_le_borel t P) (Ch_cg_biOrbitFinPart t P) Z hZ hZc
      (fun x hx y hy => by
        have hmem : y ∈ atom (biOrbitFinPart t P) x :=
          Set.mem_sInter.mpr fun s hs => hy s hs.1 hs.2
        rw [hatom x hx] at hmem
        exact Set.mem_singleton_iff.mp hmem) E hE
  exact ⟨E', hE', h1, h2⟩

/-- **The reduction to the two-sided data.**  A finite partition whose past *and* future
σ-algebras are plaque algebras for the two opposite horospherical subgroups on a common conull
set, with the two-sided fibres meeting only in the point itself, is a generator modulo `μ`. -/
theorem Ch_genFinPartPlaque_of_twoSided {μ : MeasureTheory.Measure X3}
    [MeasureTheory.IsProbabilityMeasure μ] (t : Fin 3 → ℝ)
    (hSB : @StandardBorelSpace X3 instMeasurableSpaceX3)
    (hdata : ∃ (P : @FinPart X3 instMeasurableSpaceX3) (Z : Set X3),
      MeasurableSet Z ∧ μ Zᶜ = 0 ∧
      IsPlaqueAlgebra (Uminus t) Z (pastSigFinPart t P) ∧
      IsPlaqueAlgebra (Uminus (-t)) Z (pastSigFinPart (-t) P) ∧
      (∀ x ∈ Z, ∀ y ∈ Z, y ∈ atom (pastSigFinPart t P) x →
        y ∈ atom (pastSigFinPart (-t) P) x → y = x)) :
    ∃ (P : @FinPart X3 instMeasurableSpaceX3) (Z : Set X3),
      μ Zᶜ = 0 ∧
      IsPlaqueAlgebra (Uminus t) Z (pastSigFinPart t P) ∧
      GeneratesModMu μ t P := by
  obtain ⟨P, Z, hZmeas, hZc, hplq, _hplq2, hint⟩ := hdata
  refine ⟨P, Z, hZc, hplq, ?_⟩
  refine Ch_generatesModMu_of_atom_singleton hSB t P Z hZmeas hZc (fun x hx => ?_)
  rw [Ch_biOrbitFinPart_eq_sup, Ch_atom_sup_eq]
  refine Set.Subset.antisymm ?_ (Set.singleton_subset_iff.mpr
    ⟨Ch_mem_atom_self _ x, Ch_mem_atom_self _ x⟩)
  rintro y ⟨hyA, hyB⟩
  exact Set.mem_singleton_iff.mpr
    (hint x hx y ((hplq.2.2.2 x hx).1 hyA) hyA hyB)

end Work.EKLC6Core

end
