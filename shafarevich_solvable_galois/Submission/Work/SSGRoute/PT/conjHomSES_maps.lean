import Mathlib.FieldTheory.IsAlgClosed.Basic
import Mathlib.Topology.Algebra.Group.Defs
import Submission.Work.AbsoluteKummer.SES.ConnectingH2
import Submission.Work.SSGRoute.PT.alphaConnectingCompat
import Submission.Work.SSGRoute.PT.exists_addHom_extend_addUnits
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# The dually exact coefficient sequence, with its maps identified

`PT/shortExactSeq_conjHom.lean` proves that for a short exact sequence `0 → N' → N → N'' → 0` of
discrete `G`-modules and `C = Additive Ωˣ` with `Ω` algebraically closed, the transposed sequence
`0 → Hom(N'',C) → Hom(N,C) → Hom(N',C) → 0` of conjugation modules is *nonempty*.  For the
assembly of Milne's dévissage (the `hι`/`hπ` inputs of
`PT.alphaTwo_deltaH2_eq_alphaOneMap_delta` and the exactness computations of the `r = 1` descent)
one needs the sequence *together with* the identification of its maps as the transposes
`ConjHom.precomp S.pi` and `ConjHom.precomp S.iota`; the `Nonempty` form is opaque
(`Classical.choice` of a `Prop`), so the identifications cannot be recovered from it.

This file re-runs the construction of `PT/shortExactSeq_conjHom` (the same proof, of which it is a
*strengthening*: the extra conjuncts are `rfl` for the constructed structure) and returns the
sequence together with the two map identities.
-/

set_option linter.unusedSectionVars false

namespace Work.SSGRoute.PT

universe u

/-- **The dual short exact sequence, with its maps.**  The sequence
`0 → Hom(N'',C) → Hom(N,C) → Hom(N',C) → 0` has `iota = ConjHom.precomp S.pi` and
`pi = ConjHom.precomp S.iota` (definitionally), and both identities are returned as conjuncts. -/
theorem shortExactSeq_conjHom_with_maps
    {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    {N' : Type u} [AddCommGroup N'] [DistribMulAction G N']
    {N : Type u} [AddCommGroup N] [DistribMulAction G N]
    {N'' : Type u} [AddCommGroup N''] [DistribMulAction G N'']
    (S : Work.AbsoluteKummer.ShortExactSeq G N' N N'')
    {Ω : Type u} [Field Ω] [IsAlgClosed Ω] [DistribMulAction G (Additive Ωˣ)]
    (hD'' : Work.AbsoluteKummer.IsDiscreteModule G (ConjHom N'' (Additive Ωˣ)))
    (hD : Work.AbsoluteKummer.IsDiscreteModule G (ConjHom N (Additive Ωˣ)))
    (hD' : Work.AbsoluteKummer.IsDiscreteModule G (ConjHom N' (Additive Ωˣ))) :
    ∃ Scoef : Work.AbsoluteKummer.ShortExactSeq G
        (ConjHom N'' (Additive Ωˣ)) (ConjHom N (Additive Ωˣ)) (ConjHom N' (Additive Ωˣ)),
      (∀ x : ConjHom N'' (Additive Ωˣ),
        (Scoef.iota x : ConjHom N (Additive Ωˣ)) = ConjHom.precomp S.pi x) ∧
      (∀ y : ConjHom N (Additive Ωˣ),
        (Scoef.pi y : ConjHom N' (Additive Ωˣ)) = ConjHom.precomp S.iota y) := by
  classical
  have hiota_inj : Function.Injective
      (ConjHom.precomp S.pi : ConjHom N'' (Additive Ωˣ) →+ ConjHom N (Additive Ωˣ)) := by
    intro f g h
    refine ConjHom.ext_apply (fun n => ?_)
    obtain ⟨m, rfl⟩ := S.pi_surjective n
    exact congrArg (fun φ : ConjHom N (Additive Ωˣ) => φ m) h
  have hpi_surj : Function.Surjective
      (ConjHom.precomp S.iota : ConjHom N (Additive Ωˣ) →+ ConjHom N' (Additive Ωˣ)) := by
    intro f
    obtain ⟨ψ, hψ⟩ := exists_addHom_extend_addUnits S.iota S.iota_injective f.toHom
    refine ⟨⟨ψ⟩, ?_⟩
    refine ConjHom.ext_apply (fun n => ?_)
    show ψ (S.iota n) = f.toHom n
    simpa using congrArg (fun (φ : N' →+ Additive Ωˣ) => φ n) hψ
  have hrange : (ConjHom.precomp S.pi : ConjHom N'' (Additive Ωˣ) →+ ConjHom N (Additive Ωˣ)).range
      = (ConjHom.precomp S.iota : ConjHom N (Additive Ωˣ) →+ ConjHom N' (Additive Ωˣ)).ker := by
    apply le_antisymm
    · rintro f ⟨g, rfl⟩
      rw [AddMonoidHom.mem_ker]
      refine ConjHom.ext_apply (fun n => ?_)
      simp [ConjHom.precomp_apply, S.pi_iota]
    · intro f hf
      rw [AddMonoidHom.mem_ker] at hf
      have hfk : ∀ a : N', f (S.iota a) = 0 := by
        intro a
        have h := congrArg (fun (φ : ConjHom N' (Additive Ωˣ)) => φ a) hf
        simpa [ConjHom.precomp_apply] using h
      have hle : S.pi.ker ≤ f.toHom.ker := by
        intro x hx
        have hx' : x ∈ S.iota.range := by
          rw [S.range_iota_eq_ker_pi]
          exact hx
        obtain ⟨a, ha⟩ := AddMonoidHom.mem_range.mp hx'
        rw [AddMonoidHom.mem_ker, ← ha]
        exact hfk a
      let g : N'' →+ Additive Ωˣ :=
        (AddMonoidHom.liftOfSurjective S.pi S.pi_surjective) ⟨f.toHom, hle⟩
      have hg : ∀ x : N, g (S.pi x) = f x := fun x =>
        AddMonoidHom.liftOfRightInverse_comp_apply S.pi (Function.surjInv S.pi_surjective)
          (Function.rightInverse_surjInv S.pi_surjective) ⟨f.toHom, hle⟩ x
      refine AddMonoidHom.mem_range.mpr ⟨⟨g⟩, ?_⟩
      refine ConjHom.ext_apply (fun n => ?_)
      exact hg n
  exact ⟨{ iota := ConjHom.precomp S.pi
         , pi := ConjHom.precomp S.iota
         , iota_equivariant := precomp_smul S.pi S.pi_equivariant
         , pi_equivariant := precomp_smul S.iota S.iota_equivariant
         , iota_injective := hiota_inj
         , pi_surjective := hpi_surj
         , range_iota_eq_ker_pi := hrange
         , isDiscreteM := hD''
         , isDiscreteN := hD
         , isDiscreteP := hD' }, fun _ => rfl, fun _ => rfl⟩

end Work.SSGRoute.PT
