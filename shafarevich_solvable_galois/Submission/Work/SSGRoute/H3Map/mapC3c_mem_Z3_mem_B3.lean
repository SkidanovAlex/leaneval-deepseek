import Mathlib.GroupTheory.QuotientGroup.Defs
import Mathlib.Topology.Constructions.SumProd
import Mathlib.Algebra.Group.Subgroup.Basic
import Mathlib.Algebra.GroupWithZero.Action.Defs
import Submission.Work.SSGRoute.kummerBase_euler_h3_absKummer
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# Naturality of the degree-`3` differential in the coefficient module

The `H³` layer of the workspace's continuous-cohomology model lives in
`Submission/Work/SSGRoute/kummerBase_euler_h3_absKummer.lean` (`d3`, `C3c`, `Z3`, `B3`, `H3`,
`H3π`), and the *second* connecting map of a short exact sequence of coefficient modules,
`ShortExactSeq.deltaH3 : H²(G,P) →+ H³(G,M)`, together with its exactness
`range_mapH2_eq_ker_deltaH3`, lives in
`Submission/Work/SSGRoute/kummerBase_euler_connectingH3_descent.lean`.  The one declaration of
that layer which is missing — nothing in the tree mentions it — is the *functoriality in the
coefficient module*, the degree-`3` analogue of `Work.AbsoluteKummer.mapH1` / `mapH2`
(`AbsoluteKummer/Basic.lean`), i.e. the `mapH3` attached to an equivariant additive map
`φ : M →+ N`.

This file supplies the two membership facts that such a `mapH3` is built from: the map
`c ↦ φ ∘ c` on `3`-cochains carries continuous `3`-cocycles to continuous `3`-cocycles and
continuous `3`-coboundaries to continuous `3`-coboundaries.  Consequently
`QuotientAddGroup.lift` produces `H³(G,M) →+ H³(G,N)`, exactly as `mapH2` is produced from
`Work.AbsoluteKummer.mapZ2` and `mapC1c_mem_B2`.

Mathematically this is the statement that the differential `d³` commutes with the coefficient
change (`d³ (φ ∘ c) = φ ∘ d³ c`, from additivity and equivariance of `φ`) and that local
constancy is preserved by post-composition with any function.  It is the degree-`3` input of the
coefficient-module dévissage of the terminal vanishing `H³(G, Hom_ℤ(N,C)) = 0` in Milne's
five-lemma proof of *Arithmetic Duality Theorems* I.1.8(a).
-/

namespace Work.SSGRoute.H3Map

open Work.GroupCohomology

variable {G : Type*} [TopologicalSpace G] [Group G]
  {M : Type*} [AddCommGroup M] [DistribMulAction G M]
  {N : Type*} [AddCommGroup N] [DistribMulAction G N]

/-- **The degree-`3` differential commutes with an equivariant change of coefficients**, on
cocycles and on coboundaries: `c ↦ φ ∘ c` maps `Z³(G,M)` into `Z³(G,N)` and `B³(G,M)` into
`B³(G,N)`. -/
theorem mapC3c_mem_Z3_mem_B3 (φ : M →+ N) (hφ : Work.GroupCohomology.IsEquivariant G φ) :
    (∀ c : G × G × G → M, c ∈ Work.SSGRoute.Z3 (M := M) G →
        (fun p => φ (c p)) ∈ Work.SSGRoute.Z3 (M := N) G) ∧
      (∀ c : G × G × G → M, c ∈ Work.SSGRoute.B3 (M := M) G →
        (fun p => φ (c p)) ∈ Work.SSGRoute.B3 (M := N) G) := by
  constructor
  · intro c hc
    rw [Work.SSGRoute.mem_Z3_iff] at hc ⊢
    obtain ⟨hd, hlc⟩ := hc
    refine ⟨?_, Work.AbsoluteKummer.IsLocallyConstant.map φ hlc⟩
    have hcomm : Work.SSGRoute.d3 (A := N) (fun p => φ (c p))
        = fun p => φ (Work.SSGRoute.d3 (A := M) c p) := by
      funext p
      obtain ⟨g, h, k, l⟩ := p
      rw [Work.SSGRoute.d3_apply, Work.SSGRoute.d3_apply, ← hφ,
        ← map_sub, ← map_add, ← map_sub, ← map_add]
    rw [hcomm, hd]
    funext p
    simp
  · intro c hc
    rw [Work.SSGRoute.mem_B3_iff] at hc ⊢
    obtain ⟨b, hblc, hbd⟩ := hc
    refine ⟨fun p => φ (b p), Work.AbsoluteKummer.IsLocallyConstant.map φ hblc, ?_⟩
    have hcomm : Work.GroupCohomology.d2 G N (fun p => φ (b p))
        = fun p => φ (Work.GroupCohomology.d2 G M b p) := by
      funext p
      obtain ⟨g, h, k⟩ := p
      rw [Work.GroupCohomology.d2_apply, Work.GroupCohomology.d2_apply, ← hφ,
        ← map_sub, ← map_add, ← map_sub]
    rw [hcomm, hbd]

/-! ## The functoriality `H³` in the coefficient module

With the two membership facts above, the coefficient change `φ : M →+ N` induces a map
`H³(G,M) →+ H³(G,N)`, exactly as `Work.AbsoluteKummer.mapH1`/`mapH2` are produced from
`mapZ1`/`mapC1c_mem_B1` and `mapZ2`/`mapC1c_mem_B2`.  The computation rule is `mapH3_H3π`. -/

/-- The map `c ↦ φ ∘ c` on `3`-cochains. -/
def mapC3c (φ : M →+ N) : (G × G × G → M) →+ (G × G × G → N) where
  toFun c := fun p => φ (c p)
  map_zero' := by funext p; simp
  map_add' c c' := by funext p; simp [map_add]

@[simp] theorem mapC3c_apply (φ : M →+ N) (c : G × G × G → M) (p : G × G × G) :
    mapC3c φ c p = φ (c p) := rfl

/-- The map `Z³(G,M) → Z³(G,N)` induced by an equivariant `φ`. -/
def mapZ3 (φ : M →+ N) (hφ : Work.GroupCohomology.IsEquivariant G φ) :
    Work.SSGRoute.Z3 (M := M) G →+ Work.SSGRoute.Z3 (M := N) G where
  toFun c := ⟨mapC3c φ (c : G × G × G → M),
    (mapC3c_mem_Z3_mem_B3 φ hφ).1 _ c.2⟩
  map_zero' := Subtype.ext (by funext p; simp)
  map_add' c c' := Subtype.ext (by funext p; simp)

@[simp] theorem mapZ3_apply (φ : M →+ N) (hφ : Work.GroupCohomology.IsEquivariant G φ)
    (c : Work.SSGRoute.Z3 (M := M) G) (p : G × G × G) :
    (mapZ3 φ hφ c : G × G × G → N) p = φ ((c : G × G × G → M) p) := rfl

/-- **Functoriality of `H³` in the coefficient module.** -/
noncomputable def mapH3 (φ : M →+ N) (hφ : Work.GroupCohomology.IsEquivariant G φ) :
    Work.SSGRoute.H3 (M := M) G →+ Work.SSGRoute.H3 (M := N) G :=
  QuotientAddGroup.lift
    ((Work.SSGRoute.B3 (M := M) G).comap (Work.SSGRoute.Z3 (M := M) G).subtype)
    ((Work.SSGRoute.H3π (M := N) G).comp (mapZ3 φ hφ)) (by
      intro x hx
      have hx' : ((x : Work.SSGRoute.Z3 (M := M) G) : G × G × G → M)
          ∈ Work.SSGRoute.B3 (M := M) G :=
        AddSubgroup.mem_comap.mp hx
      rw [AddMonoidHom.mem_ker, AddMonoidHom.comp_apply,
        Work.SSGRoute.H3π_eq_zero_iff (M := N) G]
      exact (mapC3c_mem_Z3_mem_B3 φ hφ).2 _ hx')

/-- The computation rule of `mapH3` on the classes of `3`-cocycles. -/
theorem mapH3_H3π (φ : M →+ N) (hφ : Work.GroupCohomology.IsEquivariant G φ)
    (c : Work.SSGRoute.Z3 (M := M) G) :
    mapH3 φ hφ (Work.SSGRoute.H3π (M := M) G c)
      = Work.SSGRoute.H3π (M := N) G (mapZ3 φ hφ c) :=
  QuotientAddGroup.lift_mk' _ _ c


/-- The identity input acts as the identity on `H³` (the analogue of `mapH1_id_H1π`). -/
theorem mapH3_id_H3π (c : Work.SSGRoute.Z3 (M := M) G) :
    mapH3 (AddMonoidHom.id M) (Work.GroupCohomology.isEquivariant_id (G := G) (A := M))
        (Work.SSGRoute.H3π (M := M) G c)
      = Work.SSGRoute.H3π (M := M) G c := by
  rw [mapH3_H3π]
  exact congrArg (Work.SSGRoute.H3π (M := M) G) (Subtype.ext rfl)

/-- `mapH3` is compatible with composition of coefficient maps (the analogue of
`mapH1_comp_H1π`). -/
theorem mapH3_comp_H3π {P : Type*} [AddCommGroup P] [DistribMulAction G P]
    (φ : M →+ N) (ψ : N →+ P) (hφ : Work.GroupCohomology.IsEquivariant G φ)
    (hψ : Work.GroupCohomology.IsEquivariant G ψ) (c : Work.SSGRoute.Z3 (M := M) G) :
    mapH3 (ψ.comp φ) (hψ.comp hφ) (Work.SSGRoute.H3π (M := M) G c)
      = mapH3 ψ hψ (mapH3 φ hφ (Work.SSGRoute.H3π (M := M) G c)) := by
  rw [mapH3_H3π, mapH3_H3π, mapH3_H3π]
  exact congrArg (Work.SSGRoute.H3π (M := P) G) (Subtype.ext rfl)


/-- Induction principle for `H³` of the continuous cohomology: it suffices to check a predicate on
the classes of continuous `3`-cocycles.  This is the degree-`3` analogue of
`Work.AbsoluteKummer.SES.H2_induction_on`. -/
theorem H3_induction_on {C : Work.SSGRoute.H3 (M := M) G → Prop}
    (x : Work.SSGRoute.H3 (M := M) G)
    (h : ∀ c : Work.SSGRoute.Z3 (M := M) G, C (Work.SSGRoute.H3π (M := M) G c)) : C x := by
  obtain ⟨c, rfl⟩ := QuotientAddGroup.mk'_surjective
    ((Work.SSGRoute.B3 (M := M) G).comap (Work.SSGRoute.Z3 (M := M) G).subtype) x
  exact h c


end Work.SSGRoute.H3Map
