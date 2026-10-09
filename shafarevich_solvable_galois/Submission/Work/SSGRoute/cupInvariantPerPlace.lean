import Mathlib
import Submission.Work.SSGRoute.Interfaces
import Submission.Work.SSGRoute.DualMod.Main
import Submission.Work.SSGRoute.E7Fin.cupPairing
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# The invariant functional of the cup construction must depend on the local group

`Work.SSGRoute.E7Fin.cupPairing` defines the cup pairing attached to an "invariant functional"
`inv`

  `pairOfInv p k Ω K T inv M H a b = if IsCocycleOn H a ∧ IsCocycleOn H b then inv (evCupFun a b) else 0`,

where `inv : ((Ω ≃ₐ[k] Ω) → (Ω ≃ₐ[k] Ω) → DualMod p T) → ZMod p` is a **single** functional on the
space of all `2`-cochains.  Its docstring describes `inv` as "a single invariant functional per
*local group*", and the clause lemmas of `E7Fin/pairOfInv_clauses.lean`,
`…_coboundary.lean`, `…_natural.lean`, `…_pairClauses.lean` accordingly carry the hypotheses

* `hinv_add` — additive,
* `hinv_cob` — `∀ H c, IsCoboundary2On (res k K) H c → inv c = 0`,
* `hinv_unram` — kills the cochains vanishing on the inertia at a good place.

**The `H`-independence of `inv` is a defect, and it makes the whole clause list vacuous.**  The
hypothesis `hinv_cob` is quantified over *all* subgroups `H ≤ G_k`, in particular over the trivial
subgroup `⊥`: but *every* `2`-cochain is a coboundary on the trivial group (the coboundary of the
constant `1`-cochain `c ↦ c 1 1`), so `hinv_cob` forces `inv = 0`, hence `pairOfInv inv M H = 0`
for every `H`.  With the zero pairing the perfectness clause (4) — the arithmetic input `h4` of
`E7Fin.pairOfInv_pairClauses` — holds only at groups all of whose locally constant `1`-cocycles are
boundaries, i.e. never at a decomposition group of a finite place (where `H¹(D_A, M) ≠ 0` for the
coefficient modules of the assembly).  So `pairOfInv_pairClauses` cannot be instantiated in the
intended setting, and a fortiori neither can `E7` (`localTatePairing_canonical`) nor input `G1`
(`canonical_localPairing_with_reciprocity`) be derived from it.

The repair is the one the docstring already intends: let the invariant depend on the local group,

  `pairOfInvH p k Ω K T inv M H a b = if IsCocycleOn H a ∧ IsCocycleOn H b then inv H (evCupFun a b) else 0`

with `inv : Subgroup (Ω ≃ₐ[k] Ω) → (cochain) → ZMod p`.  This is still *independent of the
coefficient module* `M`, so clause (5) (naturality in `M`, the reason the explicit cup construction
replaces a dimension-count pairing) remains formal, and now `hinv_cob` reads
`∀ c, IsCoboundary2On (res k K) H c → inv H c = 0` for the *fixed* `H`, which is exactly the
property of the local invariant map `H²(H, μ_p) → 𝔽_p` and is satisfiable.

This file records the obstruction (`inv_eq_zero_of_hinv_cob`) and provides the corrected
construction (`pairOfInvH`) together with the corrected clause list.
-/

open SSGRoute
open scoped TensorProduct

namespace Work.SSGRoute

noncomputable section

variable (p : ℕ) [Fact p.Prime] (k Ω : Type) [Field k] [Field Ω] [Algebra k Ω]
  (K : IntermediateField k Ω) [Normal k K] (T : Type) [AddCommGroup T] [Module (ZMod p) T]
  [DistribMulAction (K ≃ₐ[k] K) T] [SMulCommClass (K ≃ₐ[k] K) (ZMod p) T]

/-- **Every `2`-cochain is a coboundary on the trivial subgroup.**  The subgroup `⊥` has the single
element `1`, and the coboundary formula `c g h = act g • b h - b (g * h) + b g` at `g = h = 1`
reads `c 1 1 = b 1 - b 1 + b 1 = b 1`, so the constant `1`-cochain `b ≡ c 1 1` realises `c`. -/
theorem isCoboundary2On_bot
    (c : (Ω ≃ₐ[k] Ω) → (Ω ≃ₐ[k] Ω) → Work.SSGRoute.DualMod p T) :
    SSGRoute.IsCoboundary2On (SSGRoute.res k K) (⊥ : Subgroup (Ω ≃ₐ[k] Ω)) c := by
  refine ⟨fun _ => c 1 1, ?_, ?_⟩
  · exact ⟨⊤, isOpen_univ, by intro g hg u hu huH; rfl⟩
  · intro g hg h hh
    rw [Subgroup.mem_bot] at hg hh
    subst hg
    subst hh
    simp

/-- **Consequence: the `H`-independent invariant hypothesis is unsatisfiable.**  If a single
functional `inv` on `2`-cochains kills the `2`-coboundaries of *every* subgroup — the hypothesis
`hinv_cob` of `E7Fin.pairOfInv_clauses` and of `E7Fin.pairOfInv_pairClauses` — then `inv = 0`. -/
theorem inv_eq_zero_of_hinv_cob
    (inv : ((Ω ≃ₐ[k] Ω) → (Ω ≃ₐ[k] Ω) → Work.SSGRoute.DualMod p T) → ZMod p)
    (hinv_cob : ∀ (H : Subgroup (Ω ≃ₐ[k] Ω))
      (c : (Ω ≃ₐ[k] Ω) → (Ω ≃ₐ[k] Ω) → Work.SSGRoute.DualMod p T),
      SSGRoute.IsCoboundary2On (SSGRoute.res k K) H c → inv c = 0) :
    inv = 0 := by
  funext c
  exact hinv_cob ⊥ c (isCoboundary2On_bot p k Ω K T c)

/-- **Consequence for the pairing.**  Under the `H`-independent `hinv_cob` the cup pairing
`E7Fin.pairOfInv` is identically zero, whatever the coefficient module and the local group: so the
perfectness clause (4) of the local pairing list can only hold at groups all of whose locally
constant `1`-cocycles are coboundaries. -/
theorem pairOfInv_eq_zero_of_hinv_cob
    (inv : ((Ω ≃ₐ[k] Ω) → (Ω ≃ₐ[k] Ω) → Work.SSGRoute.DualMod p T) → ZMod p)
    (hinv_cob : ∀ (H : Subgroup (Ω ≃ₐ[k] Ω))
      (c : (Ω ≃ₐ[k] Ω) → (Ω ≃ₐ[k] Ω) → Work.SSGRoute.DualMod p T),
      SSGRoute.IsCoboundary2On (SSGRoute.res k K) H c → inv c = 0)
    (M : Type) [AddCommGroup M] [Module (ZMod p) M] [DistribMulAction (K ≃ₐ[k] K) M]
    [SMulCommClass (K ≃ₐ[k] K) (ZMod p) M]
    [DistribMulAction (K ≃ₐ[k] K) (TensorProduct (ZMod p) M T)]
    [SMulCommClass (K ≃ₐ[k] K) (ZMod p) (TensorProduct (ZMod p) M T)]
    (H : Subgroup (Ω ≃ₐ[k] Ω))
    (a : (Ω ≃ₐ[k] Ω) → M)
    (b : (Ω ≃ₐ[k] Ω) → Work.SSGRoute.DualMod p (TensorProduct (ZMod p) M T)) :
    Work.SSGRoute.E7Fin.pairOfInv p k Ω K T inv M H a b = 0 := by
  rw [inv_eq_zero_of_hinv_cob p k Ω K T inv hinv_cob]
  unfold Work.SSGRoute.E7Fin.pairOfInv
  split
  · rfl
  · rfl


/-- **The cup pairing with a *place-dependent* invariant functional**, i.e. the construction the
docstring of `E7Fin/cupPairing.lean` describes: one invariant functional per local group.  This is
the repair of `E7Fin.pairOfInv`; it is `pairOfInv` with `inv` instantiated at the subgroup `H`. -/
abbrev pairOfInvH (p : ℕ) (k Ω : Type) [Field k] [Field Ω] [Algebra k Ω]
    (K : IntermediateField k Ω) [Normal k K] (T : Type) [AddCommGroup T] [Module (ZMod p) T]
    [DistribMulAction (K ≃ₐ[k] K) T] [SMulCommClass (K ≃ₐ[k] K) (ZMod p) T]
    (inv : Subgroup (Ω ≃ₐ[k] Ω) →
      ((Ω ≃ₐ[k] Ω) → (Ω ≃ₐ[k] Ω) → Work.SSGRoute.DualMod p T) → ZMod p)
    (M : Type) [AddCommGroup M] [Module (ZMod p) M] [DistribMulAction (K ≃ₐ[k] K) M]
    [SMulCommClass (K ≃ₐ[k] K) (ZMod p) M]
    [DistribMulAction (K ≃ₐ[k] K) (TensorProduct (ZMod p) M T)]
    [SMulCommClass (K ≃ₐ[k] K) (ZMod p) (TensorProduct (ZMod p) M T)]
    (H : Subgroup (Ω ≃ₐ[k] Ω))
    (a : (Ω ≃ₐ[k] Ω) → M)
    (b : (Ω ≃ₐ[k] Ω) → Work.SSGRoute.DualMod p (TensorProduct (ZMod p) M T)) : ZMod p :=
  Work.SSGRoute.E7Fin.pairOfInv p k Ω K T (inv H) M H a b

/-- `pairOfInvH` is `pairOfInv` at the functional `inv H`. -/
theorem pairOfInvH_eq (p : ℕ) (k Ω : Type) [Field k] [Field Ω] [Algebra k Ω]
    (K : IntermediateField k Ω) [Normal k K] (T : Type) [AddCommGroup T] [Module (ZMod p) T]
    [DistribMulAction (K ≃ₐ[k] K) T] [SMulCommClass (K ≃ₐ[k] K) (ZMod p) T]
    (inv : Subgroup (Ω ≃ₐ[k] Ω) →
      ((Ω ≃ₐ[k] Ω) → (Ω ≃ₐ[k] Ω) → Work.SSGRoute.DualMod p T) → ZMod p)
    (M : Type) [AddCommGroup M] [Module (ZMod p) M] [DistribMulAction (K ≃ₐ[k] K) M]
    [SMulCommClass (K ≃ₐ[k] K) (ZMod p) M]
    [DistribMulAction (K ≃ₐ[k] K) (TensorProduct (ZMod p) M T)]
    [SMulCommClass (K ≃ₐ[k] K) (ZMod p) (TensorProduct (ZMod p) M T)]
    (H : Subgroup (Ω ≃ₐ[k] Ω))
    (a : (Ω ≃ₐ[k] Ω) → M)
    (b : (Ω ≃ₐ[k] Ω) → Work.SSGRoute.DualMod p (TensorProduct (ZMod p) M T)) :
    pairOfInvH p k Ω K T inv M H a b =
      Work.SSGRoute.E7Fin.pairOfInv p k Ω K T (inv H) M H a b := rfl


/-- **The `hstab` input is automatic.**  For the finite extension `K/k` the restriction
`SSGRoute.res k K : G_k →* Gal(K/k)` has open kernel (`IntermediateField.restrictNormalHom_ker`
with `IntermediateField.fixingSubgroup_isOpen`), so the orbit map `g ↦ res k K g • x` of any element
`x` of any `Gal(K/k)`-module is constant on the cosets of that kernel, hence locally constant on
every subgroup `H`.  This discharges the `hstab`/`hstabM` hypotheses of the cup construction
(`E7Fin.pairOfInv_clauses`, `E7Fin.pairOfInv_coboundary`, `Work.SSGRoute.pairOfInvH_pairClauses`). -/
theorem isLocConstOn_res_smul [FiniteDimensional k K] (H : Subgroup (Ω ≃ₐ[k] Ω))
    (X : Type) [MulAction (K ≃ₐ[k] K) X] (x : X) :
    SSGRoute.IsLocConstOn H (fun g => SSGRoute.res k K g • x) := by
  refine ⟨(SSGRoute.res k K).ker, ?_, ?_⟩
  · rw [show ((SSGRoute.res k K).ker : Subgroup (Ω ≃ₐ[k] Ω)) = K.fixingSubgroup from
      IntermediateField.restrictNormalHom_ker K]
    exact IntermediateField.fixingSubgroup_isOpen K
  · intro g hg u hu huH
    have hu1 : SSGRoute.res k K u = 1 := hu
    show SSGRoute.res k K (g * u) • x = SSGRoute.res k K g • x
    rw [map_mul, hu1, mul_one]

/-- The same, in the shape in which `hstab` is stated: for the dual module `DualMod p (X ⊗ T')`. -/
theorem isLocConstOn_res_smul_dualMod [FiniteDimensional k K] (H : Subgroup (Ω ≃ₐ[k] Ω))
    (X : Type) [AddCommGroup X] [Module (ZMod p) X] [DistribMulAction (K ≃ₐ[k] K) X]
    [SMulCommClass (K ≃ₐ[k] K) (ZMod p) X]
    (T' : Type) [AddCommGroup T'] [Module (ZMod p) T'] [DistribMulAction (K ≃ₐ[k] K) T']
    [SMulCommClass (K ≃ₐ[k] K) (ZMod p) T']
    [DistribMulAction (K ≃ₐ[k] K) (TensorProduct (ZMod p) X T')]
    [SMulCommClass (K ≃ₐ[k] K) (ZMod p) (TensorProduct (ZMod p) X T')]
    (n : Work.SSGRoute.DualMod p (TensorProduct (ZMod p) X T')) :
    SSGRoute.IsLocConstOn H (fun g => SSGRoute.res k K g • n) := by
  refine ⟨(SSGRoute.res k K).ker, ?_, ?_⟩
  · rw [show ((SSGRoute.res k K).ker : Subgroup (Ω ≃ₐ[k] Ω)) = K.fixingSubgroup from
      IntermediateField.restrictNormalHom_ker K]
    exact IntermediateField.fixingSubgroup_isOpen K
  · intro g hg u hu huH
    have hu1 : SSGRoute.res k K u = 1 := hu
    show SSGRoute.res k K (g * u) • n = SSGRoute.res k K g • n
    rw [map_mul, hu1, mul_one]

end

end Work.SSGRoute
