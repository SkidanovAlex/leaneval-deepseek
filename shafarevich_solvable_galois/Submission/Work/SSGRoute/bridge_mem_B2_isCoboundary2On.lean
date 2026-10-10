import Mathlib.Topology.Algebra.OpenSubgroup
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
import Submission.Work.SSGRoute.Interfaces
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# The bridge `c ∈ B² ↔ IsCoboundary2On act ⊤ c`

`Work.AbsoluteKummer.B2 Γ M` is the group of continuous `2`-coboundaries of a topological group
`Γ` with coefficients in the `Γ`-module `M`, i.e. `d¹` of the locally constant `1`-cochains.  The
predicate `SSGRoute.IsCoboundary2On act ⊤ c` says that the `2`-cochain `c` is the coboundary of a
`1`-cochain `b` which is right invariant under an open subgroup of `Γ` (the `SSGRoute` substitute
for "continuous with values in a discrete module"), with the action of `Γ` on `M` induced by a
homomorphism `act : Γ →* G`.

The two conditions coincide: locally constant functions on `Γ` are exactly those right invariant
under an open subgroup, because `Γ` is compact (the crucial input is
`top_isLocConstOn_of_isLocallyConstant` below, where compactness is used through the tube lemma).

## Main result

* `Work.SSGRoute.bridge_mem_B2_isCoboundary2On`.
-/

open Filter

open scoped Pointwise Topology

set_option linter.style.haveILetI false

namespace Work.SSGRoute

section Bridge

variable {Γ M : Type} [Group Γ] [TopologicalSpace Γ]

/-- **Locally constant `1`-cochains are right invariant under an open subgroup.**

For a locally constant `f : Γ → M` on a compact topological group `Γ`, the set of "right periods"
of `f` is an open subgroup of `Γ`.  Compactness enters in the form of the tube lemma: the set
`{(x, v) | f (x * v) = f x}` is an open neighbourhood of `Γ × {1}`, hence contains a tube
`Γ × V` with `V` open; the period group contains `V`. -/
theorem top_isLocConstOn_of_isLocallyConstant [IsTopologicalGroup Γ] [CompactSpace Γ] {f : Γ → M}
    (hf : Work.AbsoluteKummer.IsLocallyConstant f) :
    SSGRoute.IsLocConstOn (⊤ : Subgroup Γ) f := by
  have hB : IsOpen {p : Γ × Γ | f (p.1 * p.2) = f p.1} := by
    rw [isOpen_iff_mem_nhds]
    rintro ⟨x, v⟩ hxv
    obtain ⟨O, hO, hxO, hOf⟩ := hf x
    obtain ⟨O', hO', hxvO', hO'f⟩ := hf (x * v)
    have hcont : Continuous fun p : Γ × Γ => p.1 * p.2 := continuous_fst.mul continuous_snd
    have hmem : (fun p : Γ × Γ => p.1 * p.2) ⁻¹' O' ∈ 𝓝 (x, v) :=
      hcont.continuousAt (hO'.mem_nhds hxvO')
    rw [nhds_prod_eq, Filter.mem_prod_iff] at hmem
    obtain ⟨X, hX, W, hW, hXW⟩ := hmem
    rw [nhds_prod_eq]
    refine Filter.mem_of_superset
      (Filter.prod_mem_prod (Filter.inter_mem hX (hO.mem_nhds hxO)) hW) ?_
    rintro ⟨x', v'⟩ ⟨⟨hx'X, hx'O⟩, hv'W⟩
    show f (x' * v') = f x'
    rw [hO'f (x' * v') (hXW (Set.mk_mem_prod hx'X hv'W)), hOf x' hx'O, hxv]
  obtain ⟨u, v, -, hv, hu', h1v, huv⟩ :=
    generalized_tube_lemma isCompact_univ isCompact_singleton hB (by
      rintro ⟨x, y⟩ ⟨-, hy⟩
      have hy' : y = (1 : Γ) := hy
      subst hy'
      show f (x * 1) = f x
      rw [mul_one])
  let U : Subgroup Γ :=
    { carrier := {u | ∀ g : Γ, f (g * u) = f g}
      mul_mem' := by
        rintro a b ha hb g
        rw [← mul_assoc, hb, ha]
      one_mem' := by intro g; rw [mul_one]
      inv_mem' := by
        intro a ha g
        have h := ha (g * a⁻¹)
        rw [mul_assoc, inv_mul_cancel, mul_one] at h
        exact h.symm }
  have hmemU : (U : Set Γ) ∈ 𝓝 (1 : Γ) :=
    Filter.mem_of_superset (hv.mem_nhds (h1v (Set.mem_singleton (1 : Γ))))
      (fun x hx g => huv (Set.mk_mem_prod (hu' (Set.mem_univ g)) hx))
  exact ⟨U, Subgroup.isOpen_of_mem_nhds U hmemU, fun g _ u hu _ => hu g⟩

/-- Conversely, right invariance under an open subgroup is local constancy (no compactness is
needed): the translates `g • U` are open neighbourhoods of `g` on which `f` is constant. -/
theorem top_isLocallyConstant_of_isLocConstOn [IsTopologicalGroup Γ] {f : Γ → M}
    (hf : SSGRoute.IsLocConstOn (⊤ : Subgroup Γ) f) :
    Work.AbsoluteKummer.IsLocallyConstant f := by
  obtain ⟨U, hUopen, hUf⟩ := hf
  intro g
  refine ⟨g • (U : Set Γ), hUopen.leftCoset g, ?_, ?_⟩
  · rw [Set.mem_smul_set]
    exact ⟨1, one_mem U, by show g * 1 = g; rw [mul_one]⟩
  · rintro x hx
    rw [Set.mem_smul_set] at hx
    obtain ⟨u, hu, rfl⟩ := hx
    exact hUf g (Subgroup.mem_top g) u hu (Subgroup.mem_top u)

end Bridge

theorem bridge_mem_B2_isCoboundary2On {Γ G M : Type} [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ] [CompactSpace Γ] [Group G] [AddCommGroup M] [DistribMulAction G M] (act : Γ →* G) (c : Γ × Γ → M) : c ∈ @Work.AbsoluteKummer.B2 Γ M _ _ _ (DistribMulAction.compHom M act) ↔ SSGRoute.IsCoboundary2On act ⊤ (fun g h => c (g, h)) := by
  letI : DistribMulAction Γ M := DistribMulAction.compHom M act
  have hcomp : ∀ (g : Γ) (m : M), (g • m : M) = act g • m := fun g m => rfl
  have key : c ∈ Work.AbsoluteKummer.B2 Γ M ↔
      SSGRoute.IsCoboundary2On act ⊤ (fun g h => c (g, h)) := by
    constructor
    · intro hc
      rw [Work.AbsoluteKummer.mem_B2_iff] at hc
      obtain ⟨f, hfC1, hfd1⟩ := hc
      refine ⟨f, top_isLocConstOn_of_isLocallyConstant hfC1, ?_⟩
      intro g _ h _
      show c (g, h) = act g • f h - f (g * h) + f g
      have h1 : (Work.GroupCohomology.d1 Γ M) f (g, h) = c (g, h) := congrFun hfd1 (g, h)
      rw [← h1, Work.GroupCohomology.d1_apply, hcomp g (f h)]
    · rintro ⟨b, hb, hbc⟩
      have hbc' : ∀ g h : Γ, c (g, h) = act g • b h - b (g * h) + b g :=
        fun g h => hbc g (Subgroup.mem_top g) h (Subgroup.mem_top h)
      rw [Work.AbsoluteKummer.mem_B2_iff]
      refine ⟨b, top_isLocallyConstant_of_isLocConstOn hb, ?_⟩
      funext p
      obtain ⟨g, h⟩ := p
      rw [Work.GroupCohomology.d1_apply, hbc' g h, hcomp g (b h)]
  exact key

end Work.SSGRoute
