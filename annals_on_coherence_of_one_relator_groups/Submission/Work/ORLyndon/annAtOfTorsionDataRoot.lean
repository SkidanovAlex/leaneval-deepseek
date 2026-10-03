/-
# The paper's route to `annAt`, with the Weinbaum input discharged

`Work.ORLyndon.annAt_of_torsionData` (`Submission/Work/ORLyndon/annAtOfTorsionData.lean`) proves the
annihilator statement `Work.ORLyndon.annAt K r u {x}` for the root Fox vector `β = rootVec K r u x`
from the two inputs of the paper (Jaikin-Zapirain--Linton, Annals 2025):

* a **torsion datum** `L : TorsionData K (OneRelatorGroup r) U` whose root `L.u` is the class of `u`
  (this packages the division closure `D(G) ⊆ U(G)` of the affiliated-operator algebra; JL
  Lemma 5.1′ / node N8), and
* **JL Claim 5.9 / Weinbaum's subword theorem** in the form
  `hβ : Set.InjOn (QuotientGroup.mk (s := normalClosure {L.u})) (rootVec K r u x).coeff.support`:
  the support of the Fox component has pairwise distinct images in `G ⧸ ⟨⟨L.u⟩⟩`.

The second input is a *hypothesis* there, because the module `Work.OROneRel.weinbaum_at` proving it in
the `Work.OROneRel` cone cannot be imported together with the `annChain` cone (the duplicate
declaration `Work.OROneRel.mk_flatten_replicate`).  The present file **discharges `hβ`** from the
import-hygiene port `Work.ORLyndon.occTerm_distinct_clean`
(`Submission/Work/ORLyndon/occTerm_distinct_clean.lean`), in which Weinbaum's theorem *is* available
inside the `annChain` cone.

## The argument

Let `G = ⟨α | r⟩` with `r = u ^ l`, `u` cyclically reduced and not a proper power, and let
`ψ : G →* ⟨α | u⟩` be the quotient map killing the class of the root `u` (`relRootHom` below; it
exists because `r = u ^ l`).  The Fox component expands as a signed sum of the *monomials* attached
to the occurrence terms (`Work.ORLyndon.rootVec_eq_sum_occEps`),

`β = Σ_i c_i • of (presentRho r (occTerm x (wordOf u) i))`,

so every element of the support is of the form `presentRho r (occTerm … i)` with `i` an *occurrence*
index (the coefficient `c_i` does not vanish, and hence `occSign … i ≠ 0`).  Since `ψ` kills
`presentRho r u`, two support elements with the same image in `G ⧸ ⟨⟨L.u⟩⟩` have the same image under
`ψ` in `⟨α | u⟩`, i.e. the corresponding occurrence terms are equal in `⟨α | u⟩`; by
`Work.ORLyndon.occTerm_distinct_clean` (Weinbaum) this forces the two indices to be equal, hence the
two support elements to be equal.

## Main results

* `Work.ORLyndon.relRootHom`, `relRootHom_mk`, `relRootHom_presentRho`, `relRootHom_u` -- the
  quotient map `⟨α | r⟩ →* ⟨α | u⟩` for `r = u ^ l`;
* `Work.ORLyndon.rootVec_eq_sum_single`, `exists_occTerm_of_mem_support`;
* `Work.ORLyndon.rootVec_support_injOn` -- the hypothesis `hβ` of `annAt_of_torsionData`;
* `Work.ORLyndon.annAt_of_torsionData_root`, `annAt_of_torsionData_root_of_charZero` -- the paper's
  route to `annAt`, with the *only* remaining input the torsion datum;
* `Work.ORLyndon.magnusDescent_of_torsionData_root` -- the same in the shape of `MagnusDescent`.
-/
import Mathlib
import Submission.Work.ORLyndon.annAtOfTorsionData
import Submission.Work.ORLyndon.occTerm_distinct_clean

set_option autoImplicit false
set_option linter.unusedVariables false

namespace Work.ORLyndon

open MonoidAlgebra

universe u v w

variable {α : Type u} [DecidableEq α] {K : Type v} [Field K]

/-! ## The quotient map `⟨α | r⟩ →* ⟨α | u⟩` for `r = u ^ l` -/

/-- The canonical map `⟨α | r⟩ →* ⟨α | u⟩` for `r = u ^ l`: it is the identity on generators, and it
kills the class of the root `u` (`relRootHom_u`). -/
noncomputable def relRootHom (r u : FreeGroup α) (l : ℕ) (hpow : r = u ^ l) :
    OneRelatorGroup r →* PresentedGroup ({u} : Set (FreeGroup α)) :=
  PresentedGroup.toGroup
    (f := fun a => PresentedGroup.mk ({u} : Set (FreeGroup α)) (FreeGroup.of a))
    (by
      intro w hw
      rw [Set.mem_singleton_iff] at hw
      subst hw
      have hlift : FreeGroup.lift
          (fun a => PresentedGroup.mk ({u} : Set (FreeGroup α)) (FreeGroup.of a))
          = PresentedGroup.mk ({u} : Set (FreeGroup α)) :=
        MonoidHom.ext fun y =>
          (FreeGroup.lift_unique (g := PresentedGroup.mk ({u} : Set (FreeGroup α)))
            (f := fun a => PresentedGroup.mk ({u} : Set (FreeGroup α)) (FreeGroup.of a))
            (fun _ => rfl) (x := y)).symm
      rw [hlift, hpow, map_pow, PresentedGroup.one_of_mem (Set.mem_singleton u), one_pow])

/-- `relRootHom` on a generator: the class of the same generator. -/
theorem relRootHom_of (r u : FreeGroup α) (l : ℕ) (hpow : r = u ^ l) (x : α) :
    relRootHom r u l hpow (PresentedGroup.of x) =
      PresentedGroup.mk ({u} : Set (FreeGroup α)) (FreeGroup.of x) := by
  rw [relRootHom]
  exact PresentedGroup.toGroup.of _

/-- `relRootHom` on an element of the free group: it is the class of the same word in `⟨α | u⟩`. -/
theorem relRootHom_mk (r u : FreeGroup α) (l : ℕ) (hpow : r = u ^ l) (y : FreeGroup α) :
    relRootHom r u l hpow (PresentedGroup.mk ({r} : Set (FreeGroup α)) y) =
      PresentedGroup.mk ({u} : Set (FreeGroup α)) y := by
  have hlift : FreeGroup.lift
      (fun a => PresentedGroup.mk ({u} : Set (FreeGroup α)) (FreeGroup.of a))
      = PresentedGroup.mk ({u} : Set (FreeGroup α)) :=
    MonoidHom.ext fun y =>
      (FreeGroup.lift_unique (g := PresentedGroup.mk ({u} : Set (FreeGroup α)))
        (f := fun a => PresentedGroup.mk ({u} : Set (FreeGroup α)) (FreeGroup.of a))
        (fun _ => rfl) (x := y)).symm
  refine Eq.trans ?_ (DFunLike.congr_fun hlift y)
  exact FreeGroup.lift_unique
    (g := (relRootHom r u l hpow).comp (PresentedGroup.mk ({r} : Set (FreeGroup α))))
    (f := fun a => PresentedGroup.mk ({u} : Set (FreeGroup α)) (FreeGroup.of a))
    (fun x => by
      rw [MonoidHom.comp_apply]
      exact relRootHom_of r u l hpow x) (x := y)

/-- `relRootHom` in the vocabulary of this chapter (`Work.ORLyndon.presentRho`). -/
theorem relRootHom_presentRho (r u : FreeGroup α) (l : ℕ) (hpow : r = u ^ l) (y : FreeGroup α) :
    relRootHom r u l hpow (presentRho r y) =
      PresentedGroup.mk ({u} : Set (FreeGroup α)) y :=
  relRootHom_mk r u l hpow y

/-- The map `relRootHom` kills the class of the root `u`. -/
theorem relRootHom_u (r u : FreeGroup α) (l : ℕ) (hpow : r = u ^ l) :
    relRootHom r u l hpow (presentRho r u) = 1 := by
  rw [relRootHom_presentRho, PresentedGroup.one_of_mem (Set.mem_singleton u)]

/-! ## The support of the root Fox vector -/

/-- The root Fox vector as a signed sum of the *monomials* attached to the occurrence positions. -/
theorem rootVec_eq_sum_single {r u : FreeGroup α} (x : α) :
    rootVec K r u x =
      ∑ i : Fin (Work.OROneRel.wordOf u).length,
        MonoidAlgebra.single (presentRho r (occTerm x (Work.OROneRel.wordOf u) i))
          (occEps K x (Work.OROneRel.wordOf u) i) := by
  rw [rootVec_eq_sum_occEps (K := K) (r := r) (u := u) x]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [MonoidAlgebra.of_apply, MonoidAlgebra.smul_single, smul_eq_mul, mul_one]

/-- Every element of the support of the root Fox vector is one of the occurrence terms, and the
attached occurrence sign does not vanish there. -/
theorem exists_occTerm_of_mem_support {r u : FreeGroup α} {x : α} {a : OneRelatorGroup r}
    (ha : a ∈ (rootVec K r u x).coeff.support) :
    ∃ i : Fin (Work.OROneRel.wordOf u).length,
      presentRho r (occTerm x (Work.OROneRel.wordOf u) i) = a ∧
        occSign x (Work.OROneRel.wordOf u) i ≠ 0 := by
  classical
  rw [rootVec_eq_sum_single (K := K) (r := r) (u := u) x] at ha
  rw [MonoidAlgebra.coeff_sum] at ha
  obtain ⟨i, _, hi⟩ := Finsupp.mem_support_finsetSum a ha
  rw [Finsupp.mem_support_iff, MonoidAlgebra.coeff_single, Finsupp.single_apply] at hi
  by_cases h : presentRho r (occTerm x (Work.OROneRel.wordOf u) i) = a
  · refine ⟨i, h, occSign_ne_zero_of_occEps_ne_zero (K := K) x _ i ?_⟩
    rw [if_pos h] at hi
    exact hi
  · exfalso
    rw [if_neg h] at hi
    exact hi rfl

/-! ## The Weinbaum input of the paper's route -/

variable {U : Type w} [Ring U] [Algebra K U]

/-- **The hypothesis `hβ` of `annAt_of_torsionData`, discharged.**  For a torsion datum `L` for the
one-relator group `G = ⟨α | r = u ^ l⟩` whose root is the class of `u` (with `u` cyclically reduced
and not a proper power), the support of the root Fox component `rootVec K r u x` maps *injectively*
into `G ⧸ ⟨⟨L.u⟩⟩`.  This is JL Claim 5.9, i.e. Weinbaum's subword theorem in the import-hygiene
form `Work.ORLyndon.occTerm_distinct_clean`. -/
theorem rootVec_support_injOn {r u : FreeGroup α} {l : ℕ} (hpow : r = u ^ l)
    (hcyc : Work.OROneRel.IsCyclicallyReducedRelator u)
    (hpp : ¬ Work.OROneRel.IsProperPower u) {x : α}
    (L : Work.ORTorsion.TorsionData K (OneRelatorGroup r) U) (hu : L.u = presentRho r u) :
    Set.InjOn (QuotientGroup.mk (s := Subgroup.normalClosure ({L.u} : Set (OneRelatorGroup r))))
      (rootVec K r u x).coeff.support := by
  classical
  intro a ha b hb hab
  obtain ⟨i, hi, hsi⟩ := exists_occTerm_of_mem_support (K := K) ha
  obtain ⟨j, hj, hsj⟩ := exists_occTerm_of_mem_support (K := K) hb
  -- the two support elements have the same image under `ψ : ⟨α | r⟩ →* ⟨α | u⟩`
  have hψ : relRootHom r u l hpow a = relRootHom r u l hpow b := by
    have hmem : a⁻¹ * b ∈ Subgroup.normalClosure ({L.u} : Set (OneRelatorGroup r)) := by
      rw [← QuotientGroup.eq]
      exact hab
    have hle := Subgroup.normalClosure_le_normal (s := ({L.u} : Set (OneRelatorGroup r)))
      (N := MonoidHom.ker (relRootHom r u l hpow)) (fun z hz => by
        show relRootHom r u l hpow z = 1
        rw [Set.mem_singleton_iff] at hz
        rw [hz, hu, relRootHom_u])
    have h1 : relRootHom r u l hpow (a⁻¹ * b) = 1 := MonoidHom.mem_ker.mp (hle hmem)
    rw [map_mul, map_inv] at h1
    exact inv_mul_eq_one.mp h1
  -- hence the occurrence terms are equal in `⟨α | u⟩`, so (Weinbaum) the indices coincide
  rw [← hi, ← hj, relRootHom_presentRho, relRootHom_presentRho] at hψ
  have hij : i = j := by
    by_contra hne
    exact occTerm_distinct_clean u hcyc hpp hsi hsj hne hψ
  rw [← hi, ← hj, hij]

/-! ## The paper's route with the Weinbaum input discharged -/

/-- **`annAt` from the paper's single remaining input.**  If `L` is the torsion datum for
`G = ⟨α | r = u ^ l⟩` (with `u` cyclically reduced and not a proper power) whose root is the class of
`u`, and the Fox component `β = rootVec K r u x` is non-zero, then `β` is a right non-zero-divisor of
`K[G]`.  Compared to `Work.ORLyndon.annAt_of_torsionData`, the Weinbaum hypothesis `hβ` is
discharged here by `rootVec_support_injOn`. -/
theorem annAt_of_torsionData_root [Nontrivial U] {r u : FreeGroup α} {l : ℕ} (hpow : r = u ^ l)
    (hcyc : Work.OROneRel.IsCyclicallyReducedRelator u)
    (hpp : ¬ Work.OROneRel.IsProperPower u) {x : α}
    (L : Work.ORTorsion.TorsionData K (OneRelatorGroup r) U) (hu : L.u = presentRho r u)
    (hβ0 : rootVec K r u x ≠ 0) : annAt K r u {x} :=
  annAt_of_torsionData L hu hβ0 (rootVec_support_injOn hpow hcyc hpp L hu)

/-- **`annAt` from the paper's single remaining input, in characteristic zero.**  The non-vanishing
of the Fox component follows from `eps x u ≠ 0` via `Work.ORLyndon.augmentation_rootVec`, so the only
remaining input is the torsion datum itself. -/
theorem annAt_of_torsionData_root_of_charZero [Nontrivial U] [CharZero K] {r u : FreeGroup α}
    {l : ℕ} (hpow : r = u ^ l) (hcyc : Work.OROneRel.IsCyclicallyReducedRelator u)
    (hpp : ¬ Work.OROneRel.IsProperPower u) {x : α} (hx : Work.OROneRel.eps x u ≠ 0)
    (L : Work.ORTorsion.TorsionData K (OneRelatorGroup r) U) (hu : L.u = presentRho r u) :
    annAt K r u {x} :=
  annAt_of_torsionData_of_charZero L hu hx (rootVec_support_injOn hpow hcyc hpp L hu)

/-- **The `MagnusDescent` half of `EpsNeZeroDescent` from the paper's single remaining input.**  For
`2 ≤ relatorNorm u`, a nonempty set `S` of letters of `u`, and a letter `x ∈ S`, a torsion datum for
the root presentation `⟨α | u ^ l⟩` produces the descent datum for `(u, l, S)`. -/
theorem magnusDescent_of_torsionData_root [Nontrivial U] {u : FreeGroup α} {l : ℕ}
    (hcyc : Work.OROneRel.IsCyclicallyReducedRelator u)
    (hpp : ¬ Work.OROneRel.IsProperPower u) {S : Set α} (hS : S.Nonempty)
    (hrn : 2 ≤ Work.OROneRel.relatorNorm u) {x : α} (hxS : x ∈ S)
    (L : Work.ORTorsion.TorsionData K (OneRelatorGroup (u ^ l)) U)
    (hu : L.u = presentRho (u ^ l) u) (hβ0 : rootVec K (u ^ l) u x ≠ 0) :
    MagnusDescent K u l S :=
  magnusDescent_of_torsionData hS hrn hxS L hu hβ0
    (rootVec_support_injOn (r := u ^ l) (u := u) (l := l) rfl hcyc hpp L hu)

end Work.ORLyndon
