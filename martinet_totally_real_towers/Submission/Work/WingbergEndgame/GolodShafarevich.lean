import Mathlib
import Submission.Work.WingbergEndgame.Defs
import Submission.Work.WingbergEndgame.certificate_quotient_six
import Submission.Work.WingbergEndgame.isPGroup_of_finite_of_injective_dense
import Submission.Work.WingbergEndgame.isPGroup_of_finite_galoisGroup
import Submission.Commons.GroupTheory.ProPGroup.golod_shafarevich_presentation_card_lt
import Submission.Work.RelatorRank.ElementaryQuotient
import Submission.Work.RelatorRank.Cohomology.card_continuousHom_eq_two_pow_generatorRank

/-!
# `Work.WingbergEndgame.GolodShafarevich` -- the Golod--Shafarevich step

The wall `Work.WingbergEndgame.h3DeficiencyWall` gives, for the wide maximal pro-`2` extension `E`
of `gsF`, a genuine pro-`2` presentation of `Γ = Gal(gsF_∞/gsF)` on `d₁(Γ)` generators and at most
`d₁(Γ) + 2` relators.  This module feeds it to Golod--Shafarevich:

* the genus certificate `gsM/gsF` gives `d₁(Γ) ≥ 6` (`certificate_quotient_six` together with
  `Work.RelatorRank.generatorRank_ge_of_surjective_elementaryAbelian`);
* hence the numerical inequality `4 · r ≤ d₁(Γ)²` holds for `r = d₁(Γ) + 2`;
* the abstract group `G = FreeGroup (Fin d₁) ⧸ ⟪relators⟫` presented by the presentation embeds
  *densely* in `Γ`, so `G` infinite implies `Γ` infinite; and `G` is infinite by the finite
  `2`-group Golod--Shafarevich inequality
  (`Commons.GroupTheory.ProPGroup.golod_shafarevich_presentation_card_lt`, itself obtained from
  `Submission.GroupTheory.finitePGroupGolodShafarevich_of_commons`), for which the only remaining
  hypothesis is *minimality* of the generating set -- supplied by the density of `G` in `Γ`: a
  generating finset of `G` maps to a dense generating family of `Γ`, of size at least the
  generator rank `d₁(Γ)`, since `GeneratorRank` is a `sInf`
  (`Work.RelatorRank.generatorRank_le_of_hasDenseGeneratingFamily`).

Everything is proved; nothing is assumed beyond the wall. -/

set_option autoImplicit false
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false
set_option linter.style.haveILetI false
set_option maxHeartbeats 1600000

open scoped Classical
open scoped NumberField
open NumberField

noncomputable section

namespace Work.WingbergEndgame

/-- **A dense range of a map into a finite `T1` space is surjective.** -/
theorem surjective_of_denseRange_of_finite {α β : Type*} [TopologicalSpace β] [T1Space β]
    [Finite β] {f : α → β} (hf : DenseRange f) : Function.Surjective f := by
  haveI : Finite (Set.range f) :=
    Finite.of_injective (fun x : Set.range f => (x : β)) Subtype.coe_injective
  have hclosed : IsClosed (Set.range f) := (Set.toFinite _).isClosed
  have hrange : (Set.range f : Set β) = Set.univ := by
    rw [DenseRange, dense_iff_closure_eq] at hf
    rw [← hf, hclosed.closure_eq]
  intro b
  have : b ∈ (Set.range f : Set β) := hrange ▸ Set.mem_univ b
  exact this

/-- **A generating finset of a group mapping densely into `Γ` has at least `GeneratorRank Γ`
elements.**  This is the *minimality* clause of the Golod--Shafarevich inequality: a finite
generating set of `G` maps to a dense generating family of `Γ`, and `GeneratorRank` is the `sInf`
of the sizes of dense generating families. -/
theorem generatorRank_le_card_of_dense_of_closure_eq_top {F : Type} [Field F] [NumberField F]
    (E : UnramifiedProTwoExtension F) {G : Type} [Group G] (φ : G →* galoisGroup E)
    (hdenseφ : DenseRange φ) (S' : Finset G) (hS' : Subgroup.closure (S' : Set G) = ⊤) :
    Work.RelatorRank.GeneratorRank (galoisGroup E) ≤ S'.card := by
  have hgen : Work.RelatorRank.HasDenseGeneratingFamily (galoisGroup E) (Fintype.card ↥S') := by
    refine ⟨fun i => φ (((Fintype.equivFin ↥S').symm i : ↥S') : G), ?_⟩
    rw [Work.RelatorRank.denseGenerating_iff]
    have hrange : Set.range (fun i : Fin (Fintype.card ↥S') =>
          φ (((Fintype.equivFin ↥S').symm i : ↥S') : G)) = φ '' (S' : Set G) := by
      ext y
      constructor
      · rintro ⟨i, rfl⟩
        exact ⟨_, ((Fintype.equivFin ↥S').symm i).2, rfl⟩
      · rintro ⟨x, hx, rfl⟩
        exact ⟨Fintype.equivFin ↥S' ⟨x, hx⟩, by simp⟩
    rw [hrange, ← MonoidHom.map_closure φ (S' : Set G), hS', Subgroup.map_top,
      Work.RelatorRank.topologicalClosure_eq_top_iff_dense]
    exact hdenseφ
  have h1 := Work.RelatorRank.generatorRank_le_of_hasDenseGeneratingFamily hgen
  rwa [Fintype.card_coe] at h1

/-- **The Golod--Shafarevich step for a genuine pro-`2` presentation.**

Let `E` be a wide maximal pro-`2` extension of a number field `F`, `Γ = Gal(E.K/F)`, and suppose
`Γ` has a genuine pro-`2` presentation with `d` generators and `r` relators, where `d` is the
generator rank of `Γ` (`hd`), `6 ≤ d` (`h6`, the numerical content of the genus certificate) and
`r ≤ d + 2` (`hr`, Shafarevich/Wingberg's relation-rank bound with `d₂(O_F^×) = 2`).  Then `Γ` is
infinite. -/
theorem infinite_of_presentationDatum {F : Type} [Field F] [NumberField F]
    (E : UnramifiedProTwoExtension F) {d r : ℕ} (gen : Fin d → galoisGroup E)
    (S : Finset (FreeGroup (Fin d))) (hdense : Work.RelatorRank.DenseGenerating gen)
    (hker : MonoidHom.ker (FreeGroup.lift gen) = Subgroup.normalClosure (S : Set (FreeGroup (Fin d))))
    (hS : S.card ≤ r)
    (hd : d = Work.RelatorRank.GeneratorRank (galoisGroup E)) (h6 : 6 ≤ d) (hr : r ≤ d + 2) :
    Infinite (galoisGroup E) := by
  classical
  -- the abstract group presented by the relators, embedded densely in `Γ`
  let G := FreeGroup (Fin d) ⧸ Subgroup.normalClosure (S : Set (FreeGroup (Fin d)))
  have hHdense : Dense (((FreeGroup.lift gen).range) : Set (galoisGroup E)) := by
    rw [← Work.RelatorRank.topologicalClosure_eq_top_iff_dense (FreeGroup.lift gen).range,
      FreeGroup.range_lift_eq_closure]
    exact (Work.RelatorRank.denseGenerating_iff gen).mp hdense
  let ψe : G ≃* ↥(FreeGroup.lift gen).range :=
    (QuotientGroup.congr (Subgroup.normalClosure (S : Set (FreeGroup (Fin d))))
        (FreeGroup.lift gen).ker (MulEquiv.refl _) (by rw [hker]; simp)).trans
      (QuotientGroup.quotientKerEquivRange (FreeGroup.lift gen))
  let φ : G →* galoisGroup E := (Subgroup.subtype _).comp ψe.toMonoidHom
  have hdenseφ : DenseRange φ := by
    have hrange : Set.range φ = (((FreeGroup.lift gen).range) : Set (galoisGroup E)) := by
      ext x
      constructor
      · rintro ⟨g, rfl⟩
        exact (ψe g).2
      · intro hx
        refine ⟨ψe.symm ⟨x, hx⟩, ?_⟩
        simp [φ]
    rw [DenseRange, hrange]
    exact hHdense
  have hinj : Function.Injective φ := fun a b hab => ψe.injective (Subtype.coe_injective hab)
  -- minimality of the generating set
  have hmin : ∀ S' : Finset G, Subgroup.closure (S' : Set G) = ⊤ → Fintype.card (Fin d) ≤ S'.card := by
    intro S' hS'
    simpa [hd, Fintype.card_fin] using
      generatorRank_le_card_of_dense_of_closure_eq_top E φ hdenseφ S' hS'
  -- the numerical Golod--Shafarevich inequality
  have hineq : 4 * S.card ≤ d * d := by
    have h1 : S.card ≤ d + 2 := le_trans hS hr
    have h2 : 4 * (d + 2) ≤ d * d := by
      nlinarith [h6, sq_nonneg ((d : ℤ) - 6)]
    exact le_trans (Nat.mul_le_mul_left 4 h1) h2
  -- `G` is infinite by Golod--Shafarevich
  have hGinf : Infinite G := by
    by_contra hfin
    haveI : Finite G := not_infinite_iff_finite.mp hfin
    haveI : Fintype G := Fintype.ofFinite G
    have hpgG : IsPGroup 2 G :=
      isPGroup_of_finite_of_injective_dense E φ hinj hdenseφ inferInstance
    haveI : Nontrivial G := by
      rw [← not_subsingleton_iff_nontrivial]
      intro hss
      haveI := hss
      have hcl : Subgroup.closure ((∅ : Finset G) : Set G) = ⊤ := by
        refine eq_top_iff.mpr fun x _ => ?_
        rw [Subsingleton.elim x 1]
        exact Subgroup.one_mem _
      have hh := hmin ∅ hcl
      simp only [Finset.card_empty, Fintype.card_fin] at hh
      omega
    have hkey := Commons.GroupTheory.ProPGroup.golod_shafarevich_presentation_card_lt 2 hpgG S
      ⟨MulEquiv.refl _⟩ hmin
    rw [Fintype.card_fin] at hkey
    omega
  exact Infinite.of_injective φ hinj

/-- **The Golod--Shafarevich step, from a genuine pro-`2` presentation.** -/
theorem infinite_of_hasProTwoPresentation {F : Type} [Field F] [NumberField F]
    (E : UnramifiedProTwoExtension F) {d r : ℕ}
    (h : HasProTwoPresentation (galoisGroup E) d r)
    (hd : d = Work.RelatorRank.GeneratorRank (galoisGroup E)) (h6 : 6 ≤ d) (hr : r ≤ d + 2) :
    Infinite (galoisGroup E) := by
  obtain ⟨gen, S, hcard, hdense, hker, -⟩ := h
  exact infinite_of_presentationDatum E gen S hdense hker hcard hd h6 hr

/-- **The Golod--Shafarevich step, from the tree's discrete (faithful) presentation
`Work.RelatorRank.HasProP2Presentation`.**  The completeness clause of `HasProTwoPresentation` is
*not* used by the Golod--Shafarevich argument (it is needed only for the realization of the
quotients, `Work.WingbergEndgame.exists_finite_galois_of_presentation_quotient`), so the weaker
presentation suffices here. -/
theorem infinite_of_hasProP2Presentation {F : Type} [Field F] [NumberField F]
    (E : UnramifiedProTwoExtension F) {d r : ℕ}
    (h : Work.RelatorRank.HasProP2Presentation (galoisGroup E) d r)
    (hd : d = Work.RelatorRank.GeneratorRank (galoisGroup E)) (h6 : 6 ≤ d) (hr : r ≤ d + 2) :
    Infinite (galoisGroup E) := by
  obtain ⟨D⟩ := h
  exact infinite_of_presentationDatum E D.gen D.rel D.dense D.ker_eq D.card_le hd h6 hr

/-- **The wall makes the wide maximal pro-`2` extension of `gsF` infinite.** -/
theorem exists_infinite_of_h3DeficiencyWall (h : h3DeficiencyWall) :
    ∃ E : UnramifiedProTwoExtension gsF, Infinite (galoisGroup E) := by
  obtain ⟨E, gen, S, hcard, hdense, hker, hext⟩ := h
  refine ⟨E, infinite_of_hasProTwoPresentation E ⟨gen, S, hcard, hdense, hker, hext⟩ rfl ?_ ?_⟩
  · obtain ⟨ψ, hsurj, hcont⟩ := certificate_quotient_six E
    exact Work.RelatorRank.generatorRank_ge_of_surjective_elementaryAbelian ψ hcont hsurj
      ⟨_, gen, hdense⟩
  · have hu : Work.ClassFieldTower.unitTwoRank gsF = 2 := unitTwoRank_gsF
    omega

end Work.WingbergEndgame
