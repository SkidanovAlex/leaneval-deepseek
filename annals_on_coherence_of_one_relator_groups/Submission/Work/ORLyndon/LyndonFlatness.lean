import Mathlib
import Submission.Work.ORLyndon.Lyndon
import Submission.Work.ORLyndon.Magnus
import Submission.Work.ORLyndon.MagnusMiddle
import Submission.Work.ORLyndon.magnusTwoTerm_of_lyndon
import Submission.Work.ORLyndon.Augmentation
import Submission.Work.ORFlatness.Tor2ORCoherence
import Submission.Work.ORCoherence.Tor

/-!
# The Lyndon exact sequence, JL Claim 5.8, and `Tor₂^{K[G]}(D, -) = 0` for a one-relator group

This file is the interface of node **N3** with the flatness node **N9**
(`Submission/Work/ORFlatness`) and with the assembly (`Submission/Work/ORAssembly`).

For a one-relator presentation `G = ⟨X | r⟩` with `r = u ^ l`, a distinguished generator
`t : X` and the remaining generators `Y` (`ht : t ∉ Y`, `hY : ∀ x ∉ Y, x = t`), put
`A = ⟨Y⟩ ≤ G` (the Magnus subgroup, free on `Y` by the Freiheitssatz) and let `β : K[G]` be the
outside Fox derivative `presentAlg K r (foxD t u)`.

The transposed form of JL Claim 5.10 (`Work.ORLyndon.magnusTwoTerm_of_lyndon`, from Lyndon's
identity theorem) is the exact sequence of left `K[G]`-modules

`0 → K[G]/K[G](u-1) → I^G_{K[A]} ⊕ K[G] → I_{K[G]} → 0`,

which is packaged by the data structure `Work.ORLyndon.MagnusTwoTermExact`.  Its maps are called
`γ` and `π` below; the three objects of the sequence, in the vocabulary of `Work.ORFlatness`, are

* `A := ↥(relationModule K r u) = K[G] ⧸ Ideal.span {of (ρ u) - 1}`
  (`Work.ORLyndon.relationModule`; it is the relation module `K[G] ⊗_{K⟨u⟩} K`),
* `B := ↥(augIdealIn K (magnusSub Y r)) × K[G] = I^G_{K[A]} ⊕ K[G]`
  (`Work.ORLyndon.magnusMiddle`),
* `C := ↥(augIdeal K (OneRelatorGroup r)) = I_{K[G]}` (`Work.ORLyndon.augIdealModule`).

## What is proved here, and what is taken as a hypothesis

* `Work.ORLyndon.magnusTwoTerm_shortExact` — the exact sequence above in the shape
  `f : A →ₗ B`, `g : B →ₗ C`, `Surjective g`, `f.range = g.ker` demanded by
  `Work.ORFlatness.torTwoVanishes_diagonal_jl_right`.
* `Work.ORLyndon.magnus_hB` — **JL Claim 5.8** in the form `hB` of node N9:
  `Tor₁^{K[G]}(D ⊗_K M, I^G_{K[A]} ⊕ K[G]) = 0` for every `K[G]`-module `M` with a compatible
  `K`-structure.  In the single two-cell case the middle term is *free*: it is isomorphic to
  `K[G]^X` (`Work.ORLyndon.magnusMiddle_projective`), so `Tor₁` vanishes against it for trivial
  reasons.
* `Work.ORLyndon.magnus_torTwoVanishes_of_twoTerm` and `Work.ORLyndon.magnus_torTwoVanishes` —
  the assembly: from the above exact sequence, `hB`, and the hypotheses of nodes N8 (`hA`,
  Lemma 5.1′ in right-module form) and N1 (`hswap`, `hchain`, Lemma 5.2), conclude
  `Work.ORCoherence.TorTwoVanishes φ.toRingHom` — exactly the hypothesis `RingInputs.hTor` of the
  assembly, in exactly the form of `Work.ORAssembly.RingInputs.ofDatumFlat`.
-/

set_option autoImplicit false
set_option linter.unusedVariables false

open MonoidAlgebra
open scoped TensorProduct

open CategoryTheory Limits

universe u

namespace Work.ORLyndon

variable (K X : Type u) [Field K] [DecidableEq X]

/-- The middle term `I^G_{K[A]} ⊕ K[G]` of the two-term form of Lyndon's identity theorem
(JL Claim 5.10) for the Magnus subgroup `A = magnusSub Y r ≤ ⟨X | r⟩`. -/
abbrev magnusMiddle (Y : Finset X) (r : FreeGroup X) : Type u :=
  ↥(augIdealIn K (magnusSub Y r)) × MonoidAlgebra K (OneRelatorGroup r)

/-- The third term `I_{K[G]}` of the transposed Claim 5.10: the augmentation ideal of `K[G]`,
`G = ⟨X | r⟩`.  This is the `C` of node N9 (`Work.ORFlatness`). -/
abbrev augIdealModule (r : FreeGroup X) : Type u :=
  ↥(augIdeal K (OneRelatorGroup r))

/-- **The Lyndon/Magnus exact sequence of `⟨X | r⟩`** (transposed JL Claim 5.10), in the shape
demanded by `Work.ORFlatness.torTwoVanishes_diagonal_jl_right`: maps
`f : A →ₗ B`, `g : B →ₗ C` with `g` surjective and `f.range = g.ker`, where
`A = ↥(relationModule K r u)`, `B = I^G_{K[A]} ⊕ K[G]` and `C = I_{K[G]}`. -/
theorem magnusTwoTerm_shortExact (Y : Finset X) (t : X) (r u : FreeGroup X) (l : ℕ)
    (h : MagnusTwoTermExact K (magnusSub Y r) (presentRho r u) l
      ((presentAlg K r) (foxD (K := K) t u))) :
    ∃ (f : relationModule K r u →ₗ[MonoidAlgebra K (OneRelatorGroup r)] magnusMiddle K X Y r)
      (g : magnusMiddle K X Y r →ₗ[MonoidAlgebra K (OneRelatorGroup r)] augIdealModule K X r),
      Function.Surjective g ∧ f.range = g.ker :=
  ⟨h.γ, h.π, h.π_surjective, h.ker_eq_range.symm⟩

/-- **JL Claim 5.8**, in the exact form of the hypothesis `hB` of node N9: for every left
`K[G]`-module `M` with a compatible `K`-module structure, `Tor₁^{K[G]}` vanishes against the middle
term `I^G_{K[A]} ⊕ K[G]` of the transposed Claim 5.10, where `D ⊗_K M` carries the diagonal right
action `Work.ORFlatness.diagRightModule`.

In the single two-cell case this needs no homological input at all: the middle term is isomorphic to
the free module `K[G]^X` (`Work.ORLyndon.magnusMiddle_projective`). -/
theorem magnus_hB (Y : Finset X) {t : X} (ht : t ∉ Y) (hY : ∀ x : X, x ∉ Y → x = t)
    (r : FreeGroup X)
    (hinj : Function.Injective (Work.OROneRel.presentedGroupMap r (Y : Set X)))
    (S : Type u) [Ring S] [Algebra K S] (φ : MonoidAlgebra K (OneRelatorGroup r) →ₐ[K] S) :
    ∀ (M : Type u) [AddCommGroup M] [Module K M] [Module (MonoidAlgebra K (OneRelatorGroup r)) M]
      [IsScalarTower K (MonoidAlgebra K (OneRelatorGroup r)) M]
      [SMulCommClass K (MonoidAlgebra K (OneRelatorGroup r)) M],
      letI := Work.ORFlatness.diagRightModule K (OneRelatorGroup r) S φ M
      Work.ORFlatness.Tor1Vanishes (MonoidAlgebra K (OneRelatorGroup r)) (S ⊗[K] M)
        (magnusMiddle K X Y r) := by
  intro M _ _ _ _ _
  letI := Work.ORFlatness.diagRightModule K (OneRelatorGroup r) S φ M
  exact tor1Vanishes_magnusMiddle Y ht hY r hinj _

/-- **Node N9 `hB` from the Freiheitssatz**: the same statement as `Work.ORLyndon.magnus_hB`, with
the injectivity of `presentedGroupMap r Y` (i.e. the freeness of the Magnus subgroup on `Y`)
supplied by the Freiheitssatz `Work.OROneRel.freiheitssatz_at`. -/
theorem magnus_hB_of_freiheitssatz (Y : Finset X) {t : X} (ht : t ∉ Y)
    (hY : ∀ x : X, x ∉ Y → x = t) (r : FreeGroup X)
    (hcr : Work.OROneRel.IsCyclicallyReducedRelator r)
    (hnotmem : r ∉ Subgroup.closure (FreeGroup.of '' (Y : Set X)))
    (S : Type u) [Ring S] [Algebra K S] (φ : MonoidAlgebra K (OneRelatorGroup r) →ₐ[K] S) :
    ∀ (M : Type u) [AddCommGroup M] [Module K M] [Module (MonoidAlgebra K (OneRelatorGroup r)) M]
      [IsScalarTower K (MonoidAlgebra K (OneRelatorGroup r)) M]
      [SMulCommClass K (MonoidAlgebra K (OneRelatorGroup r)) M],
      letI := Work.ORFlatness.diagRightModule K (OneRelatorGroup r) S φ M
      Work.ORFlatness.Tor1Vanishes (MonoidAlgebra K (OneRelatorGroup r)) (S ⊗[K] M)
        (magnusMiddle K X Y r) :=
  magnus_hB K X Y ht hY r
    (Work.OROneRel.freiheitssatz_at r hcr (Y : Set X) hnotmem) S φ

/-- **Node N9 from the two-term form of Lyndon's identity theorem.**

Given the exact sequence `0 → A → B → C → 0` of the transposed Claim 5.10 (`h`, with maps `h.γ`,
`h.π`), the freeness of the Magnus subgroup on `Y` (`hinj`), and the two remaining inputs of
JL §5 — `hA` (Lemma 5.1 + Claim 5.9, node N8, in the right-module form) and `hswap`, `hchain`
(the duality and dimension-shifting chain of Lemma 5.2, node N1) — conclude
`Tor₂^{K[G]}(D, -) = 0`, i.e. `Work.ORCoherence.TorTwoVanishes φ.toRingHom`.

This is `Work.ORFlatness.torTwoVanishes_diagonal_jl_right` with `hB` (Claim 5.8) *proved* here
rather than assumed. -/
theorem magnus_torTwoVanishes_of_twoTerm (Y : Finset X) {t : X} (ht : t ∉ Y)
    (hY : ∀ x : X, x ∉ Y → x = t) (r u : FreeGroup X) (l : ℕ)
    (hinj : Function.Injective (Work.OROneRel.presentedGroupMap r (Y : Set X)))
    (h : MagnusTwoTermExact K (magnusSub Y r) (presentRho r u) l
      ((presentAlg K r) (foxD (K := K) t u)))
    (S : Type u) [Ring S] [Algebra K S] (φ : MonoidAlgebra K (OneRelatorGroup r) →ₐ[K] S)
    [Jinst : Module ((MonoidAlgebra K (OneRelatorGroup r))ᵐᵒᵖ)
      (S ⊗[K] ↥(augIdeal K (OneRelatorGroup r)))]
    (hA : ∀ (M : Type u) [AddCommGroup M] [Module K M]
      [Module (MonoidAlgebra K (OneRelatorGroup r)) M]
      [IsScalarTower K (MonoidAlgebra K (OneRelatorGroup r)) M]
      [SMulCommClass K (MonoidAlgebra K (OneRelatorGroup r)) M],
      letI := Work.ORFlatness.diagRightModule K (OneRelatorGroup r) S φ M
      Function.Injective (Work.ORFlatness.BalTensor.map (MonoidAlgebra K (OneRelatorGroup r))
        (LinearMap.id : (S ⊗[K] M) →ₗ[(MonoidAlgebra K (OneRelatorGroup r))ᵐᵒᵖ] (S ⊗[K] M)) h.γ))
    (hswap : ∀ (M : Type u) [AddCommGroup M] [Module K M]
      [Module (MonoidAlgebra K (OneRelatorGroup r)) M]
      [IsScalarTower K (MonoidAlgebra K (OneRelatorGroup r)) M]
      [SMulCommClass K (MonoidAlgebra K (OneRelatorGroup r)) M],
      letI := Work.ORFlatness.diagRightModule K (OneRelatorGroup r) S φ M
      (Work.ORFlatness.Tor1Vanishes (MonoidAlgebra K (OneRelatorGroup r)) (S ⊗[K] M)
          ↥(augIdeal K (OneRelatorGroup r)) ↔
        Work.ORFlatness.Tor1Vanishes (MonoidAlgebra K (OneRelatorGroup r))
          (S ⊗[K] ↥(augIdeal K (OneRelatorGroup r))) M))
    (hchain : ∀ (M : ModuleCat.{u} (MonoidAlgebra K (OneRelatorGroup r))),
      IsZero (Work.ORCoherence.Tor φ.toRingHom 2 M) ↔
        Work.ORFlatness.Tor1Vanishes (MonoidAlgebra K (OneRelatorGroup r))
          (S ⊗[K] ↥(augIdeal K (OneRelatorGroup r))) (↥M)) :
    Work.ORCoherence.TorTwoVanishes φ.toRingHom :=
  Work.ORFlatness.torTwoVanishes_diagonal_jl_right K (OneRelatorGroup r) S φ
    h.γ h.π h.π_surjective h.ker_eq_range.symm
    (magnus_hB K X Y ht hY r hinj S φ) hA hswap hchain

/-- **Node N9 from Lyndon's identity theorem.**  The same as
`Work.ORLyndon.magnus_torTwoVanishes_of_twoTerm`, but with the exact sequence of Claim 5.10 built
here from

* Lyndon's identity theorem `h : LyndonIdentity K X r u l` (the last named input of node N3, see
  `Work.ORLyndon.LyndonIndependence` and `Work.ORLyndon.lyndonIdentity_of_independence`),
* the Freiheitssatz (`Work.OROneRel.freiheitssatz_at`), giving both the exactness of the two-term
  form (`Work.ORLyndon.magnusTwoTerm_of_lyndon`) and the freeness of the Magnus subgroup,

and the flatness hypotheses `hA` (node N8) and `hswap`, `hchain` (node N1).

The conclusion `Work.ORCoherence.TorTwoVanishes φ.toRingHom` is the field `hTor` of
`Work.ORAssembly.RingInputs`; the other fields of that structure are supplied by nodes N5/N6/N7
(the Linnell datum), N4 (the torsion-free finite-index subgroup) and
`Work.ORLyndon.globalDim_le_two_of_lyndon` (the `hgl` field, node N3). -/
theorem magnus_torTwoVanishes (Y : Finset X) {t : X} (ht : t ∉ Y)
    (hY : ∀ x : X, x ∉ Y → x = t) (r u : FreeGroup X) (l : ℕ)
    (hcr : Work.OROneRel.IsCyclicallyReducedRelator r)
    (hnotmem : r ∉ Subgroup.closure (FreeGroup.of '' (Y : Set X)))
    (h : LyndonIdentity K X r u l)
    (S : Type u) [Ring S] [Algebra K S] (φ : MonoidAlgebra K (OneRelatorGroup r) →ₐ[K] S)
    [Jinst : Module ((MonoidAlgebra K (OneRelatorGroup r))ᵐᵒᵖ)
      (S ⊗[K] ↥(augIdeal K (OneRelatorGroup r)))]
    (hA : ∀ (M : Type u) [AddCommGroup M] [Module K M]
      [Module (MonoidAlgebra K (OneRelatorGroup r)) M]
      [IsScalarTower K (MonoidAlgebra K (OneRelatorGroup r)) M]
      [SMulCommClass K (MonoidAlgebra K (OneRelatorGroup r)) M],
      letI := Work.ORFlatness.diagRightModule K (OneRelatorGroup r) S φ M
      Function.Injective (Work.ORFlatness.BalTensor.map (MonoidAlgebra K (OneRelatorGroup r))
        (LinearMap.id : (S ⊗[K] M) →ₗ[(MonoidAlgebra K (OneRelatorGroup r))ᵐᵒᵖ] (S ⊗[K] M))
        (magnusTwoTerm_of_lyndon Y t ht hY hcr hnotmem h).γ))
    (hswap : ∀ (M : Type u) [AddCommGroup M] [Module K M]
      [Module (MonoidAlgebra K (OneRelatorGroup r)) M]
      [IsScalarTower K (MonoidAlgebra K (OneRelatorGroup r)) M]
      [SMulCommClass K (MonoidAlgebra K (OneRelatorGroup r)) M],
      letI := Work.ORFlatness.diagRightModule K (OneRelatorGroup r) S φ M
      (Work.ORFlatness.Tor1Vanishes (MonoidAlgebra K (OneRelatorGroup r)) (S ⊗[K] M)
          ↥(augIdeal K (OneRelatorGroup r)) ↔
        Work.ORFlatness.Tor1Vanishes (MonoidAlgebra K (OneRelatorGroup r))
          (S ⊗[K] ↥(augIdeal K (OneRelatorGroup r))) M))
    (hchain : ∀ (M : ModuleCat.{u} (MonoidAlgebra K (OneRelatorGroup r))),
      IsZero (Work.ORCoherence.Tor φ.toRingHom 2 M) ↔
        Work.ORFlatness.Tor1Vanishes (MonoidAlgebra K (OneRelatorGroup r))
          (S ⊗[K] ↥(augIdeal K (OneRelatorGroup r))) (↥M)) :
    Work.ORCoherence.TorTwoVanishes φ.toRingHom :=
  magnus_torTwoVanishes_of_twoTerm K X Y ht hY r u l
    (Work.OROneRel.freiheitssatz_at r hcr (Y : Set X) hnotmem)
    (magnusTwoTerm_of_lyndon Y t ht hY hcr hnotmem h) S φ hA hswap hchain

end Work.ORLyndon
