import Mathlib
import Submission.Work.ProPDeficiency.Basic
import Submission.Work.ProPDeficiency.card_le_rel_card_of_finite

/-!
# Deficiency bound from finiteness of the *abelianization*

**Namespace** `Work.ShafarevichKoch`; module
`Submission.Work.ShafarevichKoch.card_le_rel_card_of_finite_abelianization`.

`Work.ProPDeficiency.card_le_rel_card_of_finite` shows that a *finite* group presented on `α` by
`rel` satisfies `card α ≤ rel.card` (the deficiency of a finite group is `≤ 0`).  Here we prove
the sharper statement in which finiteness of `G` is replaced by finiteness of its
**abelianization**: `G ≃* FreeGroup α ⧸ N` with `Abelianization G` finite still forces
`card α ≤ rel.card`.

The gain is genuine, the hypothesis is strictly weaker: `ℤ/2 * ℤ/2` is infinite and is presented
by `⟨a, b ∣ a², b²⟩`, with finite abelianization `(ℤ/2)²`.

The proof is the one of `card_le_rel_card_of_finite` with a single change: a homomorphism from
`G` to the abelian group `Multiplicative ℚ` factors through `Abelianization G`
(`Abelianization.lift`), and a homomorphism from a finite group to `Multiplicative ℚ` is trivial
(`Work.ProPDeficiency.monoidHom_to_rat_eq_one`).  The abelianised relation matrix
`relMatrix rel : (α → ℚ) →ₗ[ℚ] (rel → ℚ)` is therefore injective, whence
`card α = finrank ℚ (α → ℚ) ≤ finrank ℚ (rel → ℚ) = rel.card`.
-/

set_option linter.style.haveILetI false

open scoped Classical

namespace Work.ShafarevichKoch

noncomputable section

variable {α : Type*} [Fintype α]

/-- **A group with finite abelianization has no nontrivial homomorphism to `ℚ`.**  A homomorphism
`f : G →* Multiplicative ℚ` lands in an abelian group, hence factors through the abelianization
(`Abelianization.lift`); the resulting homomorphism out of the finite group `Abelianization G` is
trivial because `ℚ` is torsion free. -/
theorem monoidHom_to_rat_eq_one_of_finite_abelianization {G : Type*} [Group G]
    (hab : Finite (Abelianization G)) (f : G →* Multiplicative ℚ) : f = 1 := by
  have hlift : Abelianization.lift f = 1 :=
    @Work.ProPDeficiency.monoidHom_to_rat_eq_one (Abelianization G) _ hab
      (Abelianization.lift f)
  calc f = (Abelianization.lift f).comp Abelianization.of := by
        ext x; exact Abelianization.lift_apply_of f x
    _ = 1 := by rw [hlift]; ext x; simp

/-- **The abelianised relation matrix is injective, finiteness of `G` replaced by finiteness of
`Abelianization G`.**  If `v : α → ℚ` lies in the kernel then `ratEval v` kills every relator,
hence kills the normal closure of `rel`, hence descends to a homomorphism
`G →* Multiplicative ℚ`; that homomorphism is trivial by
`monoidHom_to_rat_eq_one_of_finite_abelianization`, so `ratEval v = 1` and `v = 0`. -/
theorem relMatrix_injective_of_finite_abelianization {G : Type*} [Group G]
    (rel : Finset (FreeGroup α)) (hpres : Work.ProPDeficiency.IsPresentation α rel G)
    (hab : Finite (Abelianization G)) :
    Function.Injective (Work.ProPDeficiency.relMatrix rel) := by
  have hker : ∀ v : α → ℚ, Work.ProPDeficiency.relMatrix rel v = 0 → v = 0 := by
    intro v hv
    have hkill : ∀ x ∈ (rel : Set (FreeGroup α)), Work.ProPDeficiency.ratEval v x = 1 := by
      intro x hx
      have hx0 : Work.ProPDeficiency.relMatrix rel v ⟨x, hx⟩ = 0 := by rw [hv]; rfl
      have h1 : Multiplicative.toAdd (Work.ProPDeficiency.ratEval v x) = 0 := by
        rw [← Work.ProPDeficiency.relMatrix_apply_eq rel v ⟨x, hx⟩, hx0]
      exact toAdd_eq_zero.mp h1
    have hN : Subgroup.normalClosure (rel : Set (FreeGroup α)) ≤
        (Work.ProPDeficiency.ratEval v).ker :=
      Subgroup.normalClosure_le_normal hkill
    obtain ⟨e⟩ := hpres
    set L : (FreeGroup α ⧸ Subgroup.normalClosure (rel : Set (FreeGroup α))) →*
        Multiplicative ℚ :=
      QuotientGroup.lift _ (Work.ProPDeficiency.ratEval v) hN with hL
    have htriv : L.comp e.toMonoidHom = 1 :=
      monoidHom_to_rat_eq_one_of_finite_abelianization hab _
    have hsymm : e.toMonoidHom.comp e.symm.toMonoidHom = MonoidHom.id _ := by
      ext x; simp
    have hL1 : L = 1 := by
      calc L = L.comp (e.toMonoidHom.comp e.symm.toMonoidHom) := by
              rw [hsymm, MonoidHom.comp_id]
        _ = (L.comp e.toMonoidHom).comp e.symm.toMonoidHom :=
              (MonoidHom.comp_assoc e.symm.toMonoidHom e.toMonoidHom L).symm
        _ = 1 := by rw [htriv]; ext x; simp
    have hfac : Work.ProPDeficiency.ratEval v =
        L.comp (QuotientGroup.mk' (Subgroup.normalClosure (rel : Set (FreeGroup α)))) := by
      rw [hL]
      ext x
      simp
    have hrat1 : Work.ProPDeficiency.ratEval v = 1 := by rw [hfac, hL1]; ext x; simp
    funext a
    have h := DFunLike.congr_fun hrat1 (FreeGroup.of a)
    simp only [Work.ProPDeficiency.ratEval_of, MonoidHom.one_apply] at h
    exact ofAdd_eq_one.mp h
  intro u w h
  have h0 : Work.ProPDeficiency.relMatrix rel (u - w) = 0 := by rw [map_sub, h, sub_self]
  have h2 := hker (u - w) h0
  rwa [sub_eq_zero] at h2

/-- **The deficiency of a finitely generated group is bounded by the rank of its abelianization.**
Concretely: if `G` is presented on the finite generating set `α` by the relators `rel`, and the
abelianization of `G` is finite, then there are at least as many relators as generators.

The content is the classical inequality `d - r ≤ rank(G^{ab})` for a finite presentation, here in
its extreme case `rank(G^{ab}) = 0`: the image of `rel` in the free abelian group on `α` (the
abelianization of a free group) generates a finite-index subgroup, hence a subgroup of the same
rank `card α`, and a subgroup generated by `rel.card` elements has rank at most `rel.card`.  For
a presentation of the maximal unramified pro-`2` Galois group `G_∅` of a number field (whose
abelianization is the `2`-part of its class group, hence finite) this is the `0 ≤ df` half of the
classical Shafarevich relation bound `0 ≤ r - d ≤ d₂(O_K^×)`.

Caveat (README §9.3): it does *not* apply to the workspace's `HasProTwoPresentation F d r`, whose
presented group is a dense *subgroup* `⟨g⟩ ≤ G_∅` with possibly infinite abelianization. -/
theorem card_le_rel_card_of_finite_abelianization {G : Type*} [Group G] {α : Type*} [Fintype α]
    {rel : Finset (FreeGroup α)} (h : Work.ProPDeficiency.IsPresentation α rel G)
    (hab : Finite (Abelianization G)) : Fintype.card α ≤ rel.card := by
  calc Fintype.card α = Module.finrank ℚ (α → ℚ) :=
        (Module.finrank_fintype_fun_eq_card ℚ).symm
    _ ≤ Module.finrank ℚ (rel → ℚ) :=
        LinearMap.finrank_le_finrank_of_injective
          (relMatrix_injective_of_finite_abelianization rel h hab)
    _ = rel.card := by rw [Module.finrank_fintype_fun_eq_card ℚ, Fintype.card_coe]

end

end Work.ShafarevichKoch
