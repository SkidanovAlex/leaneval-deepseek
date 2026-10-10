import Mathlib.FieldTheory.KrullTopology
import Mathlib.RingTheory.Henselian
import Mathlib.NumberTheory.NumberField.Basic
import Mathlib.RingTheory.Flat.TorsionFree
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
import Submission.Work.AbsoluteGalois.exists_hom_lift_iff_pullbackCocycle_mem_B2
import Submission.Work.AbsoluteGalois.sectionCocycle_mem_Z2
import Submission.Work.AbsoluteKummer.Factorisation.exists_finiteGalois_le_ker_pair
import Submission.Work.AbsoluteKummer.Functoriality
import Submission.Work.AbsoluteKummer.Grunwald.sqClassLocalize_surjective
import Submission.Work.AbsoluteKummer.H1Pi.nonempty_h1_pi_equiv
import Submission.Work.AbsoluteKummer.Kummer.kummerQuotientEquiv
import Submission.Work.AbsoluteKummer.Kummer.nonempty_h0_addUnits_equiv
import Submission.Work.AbsoluteKummer.KummerBijective
import Submission.Work.AbsoluteKummer.Rat
import Submission.Work.AbsoluteKummer.SES.exists_connecting_exact_H2
import Submission.Work.Properness.Defs
import Submission.Work.SSGRoute.LTDDefs.H2locAux
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace Work.SSGRoute

/-- **Extension of a locally constant function on a closed subgroup of `G_k = Ω ≃ₐ[k] Ω`.**

Every locally constant `f : ↥D → E` on a closed subgroup `D` extends to an ambient function
`b : (Ω ≃ₐ[k] Ω) → E` whose restriction to `D` is `f` and which is locally constant *on* `D` in the
sense of `SSGRoute.IsLocConstOn` (right invariant by `U ∩ D` for an open subgroup `U ≤ G_k`).

`b` is the naive extension by `0`; the whole content is the *uniform* local constancy of `f` on the
compact subgroup `D`, which is `Work.SSGRoute.exists_openSubgroup_mul_eq_of_isLocallyConstant`
(`LTDDefs/H2locAux.lean`, already on disk and `sorry`-free).  Note that
`isLocConstOn_of_isLocallyConstant` alone does **not** give this: it produces an open subgroup of
`↥D`, and one needs an open *subgroup of `G_k`* whose trace lies inside it — which is exactly what
`exists_openSubgroup_mul_eq_of_isLocallyConstant` supplies (it is proved through the Krull
neighbourhood basis, `krullTopology_mem_nhds_one_iff`).

This is what makes the *ambient* form of the local conditions (`SSGRoute.IsCoboundary2On`, whose
`1`-cochain is a function on the whole group) follow from the *subgroup* form (`B²_c(D)`). -/
theorem exists_isLocConstOn_extension_krull {k : Type} [Field k] [NumberField k] {Ω : Type}
    [Field Ω] [Algebra k Ω] [IsAlgClosure k Ω] (D : Subgroup (Ω ≃ₐ[k] Ω)) (hD : IsClosed (D : Set (Ω ≃ₐ[k] Ω)))
    {E : Type} [AddCommGroup E] {f : ↥D → E}
    (hf : Work.AbsoluteKummer.IsLocallyConstant f) :
    ∃ b : (Ω ≃ₐ[k] Ω) → E, (∀ x : ↥D, b ↑x = f x) ∧ SSGRoute.IsLocConstOn D b := by
  classical
  obtain ⟨U, hUo, hU⟩ :=
    Work.SSGRoute.exists_openSubgroup_mul_eq_of_isLocallyConstant (k := k) (Ω := Ω) D hD hf
  refine ⟨fun g => if hg : g ∈ D then f ⟨g, hg⟩ else 0, ?_, U, hUo, ?_⟩
  · intro x
    simp only [dif_pos x.2]
  · intro g hg u hu huD
    have hgu : g * u ∈ D := D.mul_mem hg huD
    simp only [dif_pos hgu, dif_pos hg]
    exact hU ⟨g, hg⟩ u huD hu

/-- **A locally constant function on a compact topological group is locally constant on every
subgroup** in the sense of `SSGRoute.IsLocConstOn`.

This is the general-`H` form of
`Work.SSGRoute.bridge_isLocConstOn_top_of_isLocallyConstant` (the case `H = ⊤`): the *same* proof
goes through, and in fact the argument produces an open subgroup `U` such that
`f (g * u) = f g` for **all** `g` and all `u ∈ U`, so the extra hypotheses `g ∈ H`, `u ∈ H` of
`IsLocConstOn` are simply unused.

It is the bridge that lets a *continuous* existence statement (a locally constant `1`-cochain, i.e.
an element of `C1c`) be turned into the pointwise `IsCoboundary2On` clause in which the local
conditions of the E1a lane are stated, at an arbitrary subgroup (`decomp k A`, `decompK w`, …).

The argument is the one of `bridge_isLocConstOn_top_of_isLocallyConstant`: the agreement set
`{(g, u) | f (g * u) = f g}` is open in `Γ × Γ` (because `f` is locally constant) and contains
`Γ × {1}`; the compactness of `Γ` (tube lemma) produces a single open neighbourhood `t ∋ 1`;
`P := {u | ∀ g, f (g * u) = f g}` is a subgroup containing `t`, and `Subgroup.closure t` is open. -/
theorem isLocConstOn_of_isLocallyConstant {Γ M : Type} [Group Γ] [TopologicalSpace Γ]
    [IsTopologicalGroup Γ] [CompactSpace Γ] [AddCommGroup M] (H : Subgroup Γ) (f : Γ → M)
    (hf : Work.AbsoluteKummer.IsLocallyConstant f) : SSGRoute.IsLocConstOn H f := by
  have hZ : IsOpen {p : Γ × Γ | f (p.1 * p.2) = f p.1} := by
    rw [isOpen_iff_forall_mem_open]
    rintro ⟨g, u⟩ (hgu : f (g * u) = f g)
    obtain ⟨W₁, hW₁o, hW₁mem, hW₁c⟩ := hf (g * u)
    obtain ⟨W₂, hW₂o, hW₂mem, hW₂c⟩ := hf g
    refine ⟨{p : Γ × Γ | p.1 * p.2 ∈ W₁ ∧ p.1 ∈ W₂}, ?sub, ?opn, ?mem⟩
    · rintro ⟨g', u'⟩ ⟨h1, h2⟩
      show f (g' * u') = f g'
      rw [hW₁c (g' * u') h1, hgu, hW₂c g' h2]
    · exact (continuous_mul.isOpen_preimage W₁ hW₁o).inter (hW₂o.preimage continuous_fst)
    · exact ⟨hW₁mem, hW₂mem⟩
  have hsub : Set.univ ×ˢ ({1} : Set Γ) ⊆ {p : Γ × Γ | f (p.1 * p.2) = f p.1} := by
    rintro ⟨g, x⟩ ⟨-, hx⟩
    rw [Set.mem_singleton_iff] at hx
    subst hx
    simp
  obtain ⟨s, t, _hso, hto, hs, ht, hst⟩ :=
    generalized_tube_lemma (s := Set.univ) (t := {1}) isCompact_univ isCompact_singleton hZ hsub
  set P : Subgroup Γ :=
    { carrier := {u | ∀ g : Γ, f (g * u) = f g}
      one_mem' := by intro g; simp
      mul_mem' := by
        intro a b ha hb g
        show f (g * (a * b)) = f g
        rw [← mul_assoc, hb (g * a), ha g]
      inv_mem' := by
        intro a ha g
        have h := ha (g * a⁻¹)
        rw [← h, mul_assoc, inv_mul_cancel, mul_one] }
  have hvP : t ⊆ (P : Set Γ) := by
    intro x hx g
    exact hst (Set.mk_mem_prod (hs (Set.mem_univ g)) hx)
  refine ⟨Subgroup.closure t, ?_, ?_⟩
  · apply Subgroup.isOpen_of_one_mem_interior
    exact interior_maximal Subgroup.subset_closure hto (ht (Set.mem_singleton 1))
  · intro g _ u hu _
    exact ((Subgroup.closure_le P).mpr hvP hu) g

end Work.SSGRoute
