import Mathlib.FieldTheory.KrullTopology
import Mathlib.RingTheory.Henselian
import Mathlib.Algebra.Field.ZMod
import Mathlib.NumberTheory.NumberField.Basic
import Mathlib.RingTheory.Flat.TorsionFree
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.RootsOfUnity.PrimitiveRoots
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.RingTheory.Valuation.ValuationSubring
import Mathlib.Algebra.Module.StablyFree.Basic
import Submission.Work.SSGRoute.tatePoitouEmbedding
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-! Guidance from the project lead (the requester):

ROUTE: read Submission/Work/SSGRoute/DESIGN.md and the orchestrator's addendum DESIGN2 (copied as Submission/Work/SSGRoute/DESIGN2.md). Interfaces: Submission/Work/SSGRoute/Interfaces.lean (namespace SSGRoute; do NOT edit). NK.* CFT library available. Siblings in parallel.

# sha2_dual_control  (THE arithmetic core of node H7; replaces `tatePoitou_sha2_image`)

**Statement.** For `c ∈ Ш²(k,E)` there is one functional `l` on `Ш¹(k,E')`, where `E' = Hom(E⊗μ_p^∨, 𝔽_p)
= Hom(E, μ_p)`, that controls `c` under every coefficient map. If `l ∘ f'_* = 0` on `Ш¹(k,E₂')`, then
`f_* c` is a coboundary. Here `f'` is the dual of `f ⊗ T`, passed with its characterising equation `hff'`,
so the statement contains no proof terms.

**Why true.** Take the Poitou–Tate pairing `⟨·,·⟩ : Ш¹(k,E') × Ш²(k,E) → 𝔽_p` (Milne ADT I.4.10(a),
NSW 8.6.8) and set `l = ⟨·, c⟩`. Naturality gives `⟨a, f_*c⟩ = ⟨f'a, c⟩`. Right non-degeneracy then
gives `f_*c = 0`.

- Only the *injectivity half* is needed: `Ш²(k,E) ↪ Ш¹(k,E')^∨`, naturally in `E`.

**Imports.** `Submission.Work.SSGRoute.ShaCocycles`, `Submission.Work.SSGRoute.DualMod.Main`,
`Submission.Work.CohomologicalShrinking.All`.

## What this file contains

* the *assembly* (`sha2_dual_control_of_tatePoitouEmbedding`): the target theorem follows by a
  diagram chase from the single arithmetic input `Φ`, a family of maps
  `Φ_E : Ш²(k,E) →ₗ Ш¹(k,E^∨(1))^∨` which is injective and natural in the coefficient module `E`;
* the target theorem `sha2_dual_control`, deduced from the existence of such a `Φ`
  (delegated to `Work.SSGRoute.tatePoitouEmbedding`, the "injectivity half of Tate--Poitou
  duality, natural in `E`" of Milne *Arithmetic Duality Theorems* I.4.10(a));
* `finite_sha1`: `Ш¹(k,M)` is finite, via the (proved) Hasse/Bauer descent `Ш¹(k,M) ↪ H¹(Gal(K/k),M)`;
* `selmer_dual_inflated`: node **G3** of the Poitou–Tate design `DESIGN_PT.md` (Bauer/Chebotarev for
  the *dual Selmer group*, "provable now"), proved here in full — a continuous `1`-cocycle with
  `Gal(K/k)`-coefficients that is a coboundary on the decomposition groups of the places split in
  `N`, off the conjugates of a finite set `S`, factors through `Gal(N/k)`.

## Position in the Poitou–Tate design (`DESIGN_PT.md`, per the project lead)

The atom `tatePoitouEmbedding` is node **G5** of that design: it is to be assembled from the Ext-core
`E0–E9` and the Galois-side glue `G1` (`pt_localPairing`), `G2` (`pt_selmer_relaxed`) and `G3`
(`selmer_dual_inflated`).  The mathematical content of `Φ` is that assembly; the content of *this*
file is the reduction of the "dual control" statement to it, together with the banked node `G3`.
-/

/-! ## Note (corrected) on the Ext-lane node `E1a` (`ext_sha2_bridge`)

An earlier version of this note recorded a doubt about the `↔` clause of
`Work.SSGRoute.ext_sha2_bridge` (E1a), namely that `Sha2`'s local conditions are imposed at the
*full* local groups `D_A = decomp k A = G_{k_v}` whereas `ker extToIdeles` appeared to be imposed
at the smaller groups `D_w = Gal(K_w/k_v)`, so that the two would differ by the kernel of the
inflation `H²(D_w,E) → H²(D_A,E)`.  **That doubt is unfounded** (project-lead ruling, and the
mathematics below); it is recorded here in corrected form so that the (false) objection is not
re-raised.

The point is that the Ext-side local object is `Ext²_{D_w}(M', K_w^×)` with
`M' = DualMod p (E ⊗ T)`, `K_w^× = Ω_v^{×,G_{K_w}}`, and *not* `H²(D_w,E)`: the dictionary
`Ext^n_{D}(M', X) ≅ H^n(D, Hom_ℤ(M', X))` requires `X` to be **divisible**, and `K_w^×` is not.
Via the Hochschild–Serre spectral sequence of `G_{K_w} ◁ G_{k_v}` with
`E_2^{a,b} = Ext^a_{D_w}(M', H^b(G_{K_w}, Ω̄_v^×)) ⟹ Ext^{a+b}_{G_{k_v}}(M', Ω̄_v^×)` one has
`H^b(G_{K_w}, Ω̄_v^×) = 0` for `b ≥ 1` (local Hilbert 90), so the sequence degenerates at `E_2` and

  `Ext^a_{D_w}(M', K_w^×) ≅ Ext^a_{G_{k_v}}(M', Ω̄_v^×) ≅ H^a(k_v, E)`  (`Ω̄_v^×` divisible),

the last isomorphism being the (correct, divisible-coefficient) dictionary.  Hence the local
condition "`res_{D_A}(inf y) = 0`" and the component "`extLoc_w y = 0`" cut out the *same* subgroup,
with no transgression defect, and E1a's `↔` clause is correct as stated.  (The same degeneration
with global Hilbert 90 gives the edge `Ext²_G(M',K^×) ↪ H²(k,E)` used by the lane; the detection of
`extToIdeles y = 0` place by place uses that `𝕀_K = colim_S 𝕀_S`, that `Ext²(M',·)` commutes with
that filtered colimit, and that `Ext²_{D_w}(M', U_w) = 0` for `v` unramified in `K/k` because `U_w`
is cohomologically trivial.)

The target below is independent of E1a: it is reached through the atom
`tatePoitouEmbedding`, i.e. through the two halves of Milne I.4.10(a) — see
`sha2_dual_control_of_pairingAndCard` and `sha2_dual_control_of_tatePoitouEmbedding`.

-/

set_option linter.ambiguousOpen false
set_option maxHeartbeats 1000000

namespace Work.SSGRoute

open SSGRoute
open scoped TensorProduct

section Helpers

variable (p : ℕ) (k Ω : Type) [Field k] [Field Ω] [Algebra k Ω]
  (K : IntermediateField k Ω) [Normal k K]

/-- The class in `Ш¹(k,M) = Z¹_loc/B¹` of a locally trivial continuous `1`-cocycle. -/
def sha1Class (M : Type) [AddCommGroup M] [Module (ZMod p) M]
    [DistribMulAction (K ≃ₐ[k] K) M] [SMulCommClass (K ≃ₐ[k] K) (ZMod p) M]
    (φ : (Ω ≃ₐ[k] Ω) → M) (hφ : φ ∈ Z1loc p k Ω K M) : Sha1 p k Ω K M :=
  Submodule.Quotient.mk ⟨φ, hφ⟩

/-- The Hasse descent (Bauer/Chebotarev, `Work.SSGRoute.hassePrinciple_h1_cocycles`) embeds
`Ш¹(k,M)` into the finite group `H¹(Gal(K/k),M)`; hence `Ш¹(k,M)` is finite.  This finiteness is
used by every route to the Tate--Poitou duality. -/
theorem finite_sha1 (p : ℕ) [Fact p.Prime] (k Ω : Type) [Field k] [NumberField k] [Field Ω]
    [Algebra k Ω] [IsAlgClosure k Ω] (K : IntermediateField k Ω) [FiniteDimensional k K]
    [IsGalois k K] [Fintype (K ≃ₐ[k] K)] (M : Type) [AddCommGroup M] [Module (ZMod p) M]
    [DistribMulAction (K ≃ₐ[k] K) M] [SMulCommClass (K ≃ₐ[k] K) (ZMod p) M] [Finite M] :
    Finite (Sha1 p k Ω K M) := by
  haveI : Finite (Work.GroupCohomology.H1 (K ≃ₐ[k] K) M) := inferInstance
  exact Finite.of_injective (sha1DescentHom p k Ω K M) (sha1DescentHom_injective p k Ω K M)

end Helpers

/-- **The assembly.** Let `Φ` be a family, natural in the coefficient module, of *injective* maps
from `Ш²(k,E)` to the dual of `Ш¹(k, Hom(E,μ_p))`:

* `Φ_E` is injective for every finite `E`;
* for every `G`-equivariant `f : E → E₂` with transpose `f'` (characterised by `hff'`), the
  naturality square `Φ_{E₂} ∘ f_* = (f'_*)^∨ ∘ Φ_E` commutes.

Then the conclusion of `sha2_dual_control` holds: `l := Φ_E([c])` controls `c` under every
coefficient map. -/
theorem sha2_dual_control_of_tatePoitouEmbedding (p : ℕ) [Fact p.Prime] (k Ω : Type) [Field k]
    [NumberField k] [Field Ω] [Algebra k Ω] [IsAlgClosure k Ω] (K : IntermediateField k Ω)
    [FiniteDimensional k K] [IsGalois k K] [Fintype (K ≃ₐ[k] K)] (ζ : Ω)
    (hζ : IsPrimitiveRoot ζ p) (hζK : ζ ∈ K)
    (E T : Type) [AddCommGroup E] [Module (ZMod p) E] [DistribMulAction (K ≃ₐ[k] K) E]
    [SMulCommClass (K ≃ₐ[k] K) (ZMod p) E] [Finite E]
    [AddCommGroup T] [Module (ZMod p) T] [DistribMulAction (K ≃ₐ[k] K) T]
    [SMulCommClass (K ≃ₐ[k] K) (ZMod p) T]
    (hT : SSGRoute.IsCyclotomicDual p (T := T) (SSGRoute.res k K) ζ)
    (c : (Ω ≃ₐ[k] Ω) → (Ω ≃ₐ[k] Ω) → E) (hc : c ∈ Work.SSGRoute.Z2loc p k Ω K E)
    (Φ : ∀ (E' : Type) [AddCommGroup E'] [Module (ZMod p) E']
      [DistribMulAction (K ≃ₐ[k] K) E'] [SMulCommClass (K ≃ₐ[k] K) (ZMod p) E'] [Finite E'],
      Sha2 p k Ω K E' →ₗ[ZMod p]
        (Sha1 p k Ω K (DualMod p (E' ⊗[ZMod p] T)) →ₗ[ZMod p] ZMod p))
    (hΦinj : ∀ (E' : Type) [AddCommGroup E'] [Module (ZMod p) E']
      [DistribMulAction (K ≃ₐ[k] K) E'] [SMulCommClass (K ≃ₐ[k] K) (ZMod p) E'] [Finite E'],
      Function.Injective (Φ E'))
    (hΦnat : ∀ (E₁ : Type) [AddCommGroup E₁] [Module (ZMod p) E₁]
        [DistribMulAction (K ≃ₐ[k] K) E₁] [SMulCommClass (K ≃ₐ[k] K) (ZMod p) E₁] [Finite E₁]
        (E₂ : Type) [AddCommGroup E₂] [Module (ZMod p) E₂]
        [DistribMulAction (K ≃ₐ[k] K) E₂] [SMulCommClass (K ≃ₐ[k] K) (ZMod p) E₂] [Finite E₂]
        (f : E₁ →ₗ[ZMod p] E₂) (hf : ∀ (g : K ≃ₐ[k] K) (e : E₁), f (g • e) = g • f e)
        (f' : DualMod p (E₂ ⊗[ZMod p] T) →ₗ[ZMod p] DualMod p (E₁ ⊗[ZMod p] T))
        (hf' : ∀ (g : K ≃ₐ[k] K) (φ : DualMod p (E₂ ⊗[ZMod p] T)), f' (g • φ) = g • f' φ)
        (hff' : ∀ (φ : DualMod p (E₂ ⊗[ZMod p] T)) (e : E₁) (t : T),
          f' φ (e ⊗ₜ[ZMod p] t) = φ (f e ⊗ₜ[ZMod p] t))
        (b : Sha2 p k Ω K E₁),
        Φ E₂ (Sha2Map p k Ω K E₁ E₂ f hf b)
          = (Φ E₁ b).comp
              (Sha1Map p k Ω K (DualMod p (E₂ ⊗[ZMod p] T))
                (DualMod p (E₁ ⊗[ZMod p] T)) f' hf')) :
    ∃ l : Work.SSGRoute.Sha1 p k Ω K (Work.SSGRoute.DualMod p (E ⊗[ZMod p] T)) →ₗ[ZMod p] ZMod p,
      ∀ (E₂ : Type) [AddCommGroup E₂] [Module (ZMod p) E₂] [DistribMulAction (K ≃ₐ[k] K) E₂]
        [SMulCommClass (K ≃ₐ[k] K) (ZMod p) E₂] [Finite E₂]
        (f : E →ₗ[ZMod p] E₂) (hf : ∀ (g : K ≃ₐ[k] K) (e : E), f (g • e) = g • f e)
        (f' : Work.SSGRoute.DualMod p (E₂ ⊗[ZMod p] T) →ₗ[ZMod p]
          Work.SSGRoute.DualMod p (E ⊗[ZMod p] T))
        (hf' : ∀ (g : K ≃ₐ[k] K) (φ : Work.SSGRoute.DualMod p (E₂ ⊗[ZMod p] T)),
          f' (g • φ) = g • f' φ)
        (hff' : ∀ (φ : Work.SSGRoute.DualMod p (E₂ ⊗[ZMod p] T)) (e : E) (t : T),
          f' φ (e ⊗ₜ[ZMod p] t) = φ (f e ⊗ₜ[ZMod p] t)),
        l.comp (Work.SSGRoute.Sha1Map p k Ω K (Work.SSGRoute.DualMod p (E₂ ⊗[ZMod p] T))
          (Work.SSGRoute.DualMod p (E ⊗[ZMod p] T)) f' hf') = 0 →
        SSGRoute.IsCoboundary2On (SSGRoute.res k K) ⊤ (fun σ τ => f (c σ τ)) := by
  classical
  -- the class of `c` in `Ш²(k,E)`
  set b : Sha2 p k Ω K E :=
    sha2Class p k Ω K E hc.1 hc.2.1 hc.2.2.1 hc.2.2.2 with hb
  refine ⟨Φ E b, ?_⟩
  intro E₂ _ _ _ _ _ f hf f' hf' hff' hzero
  -- the image class of `f_* b` under `Φ` vanishes, since it is `l ∘ f'_*`
  have hnat := hΦnat E E₂ f hf f' hf' hff' b
  have hb0 : Sha2Map p k Ω K E E₂ f hf b = 0 := by
    apply hΦinj E₂
    rw [map_zero]
    rw [hnat]
    refine LinearMap.ext (fun a => ?_)
    have h := congrArg (fun (g : Sha1 p k Ω K (DualMod p (E₂ ⊗[ZMod p] T)) →ₗ[ZMod p] ZMod p) =>
      g a) hzero
    simpa using h
  -- push the class forward and conclude with `sha2Class_eq_zero_iff`
  have hpush := Sha2Map_sha2Class p k Ω K E E₂ f hf hc.1 hc.2.1 hc.2.2.1 hc.2.2.2
  have hcls : sha2Class p k Ω K E₂ (isCocycle2_push hc.1 f.toAddMonoidHom hf)
      (isLocConst2_push hc.2.1 f.toAddMonoidHom)
      (fun A hA => isCoboundary2On_push (hc.2.2.1 A hA) f.toAddMonoidHom hf)
      (fun σ hσ => isCoboundary2On_push (hc.2.2.2 σ hσ) f.toAddMonoidHom hf) = 0 := by
    rw [← hpush, hb0]
  exact (sha2Class_eq_zero_iff p k Ω K E₂ (isCocycle2_push hc.1 f.toAddMonoidHom hf)
    (isLocConst2_push hc.2.1 f.toAddMonoidHom)
    (fun A hA => isCoboundary2On_push (hc.2.2.1 A hA) f.toAddMonoidHom hf)
    (fun σ hσ => isCoboundary2On_push (hc.2.2.2 σ hσ) f.toAddMonoidHom hf)).mp hcls

/-! ## The two halves of the atom, and the deduction path to the target

`Work.SSGRoute.PTembedding.tatePoitouEmbedding_of_pairing` assembles the injective, natural family
`Φ` of `tatePoitouEmbedding` out of the two halves of Milne, *Arithmetic Duality Theorems*, I.4.10(a):

* a *natural* pairing `pair E : Ш¹(k,E^∨(1)) →ₗ (Ш²(k,E) →ₗ 𝔽_p)` whose kernel on the **left** is
  zero (the left-nondegeneracy of the Poitou–Tate pairing), and
* the global Euler characteristic `#Ш²(k,E) = #Ш¹(k,E^∨(1))` (Milne, §5).

That module imports *this* one (it consumes `finite_sha1` above), so the step cannot be imported
here; it is carried out again below, in the exact form in which this file's target consumes it.
The content is the linear algebra of the adjoint of a pairing between two finite `𝔽_p`-vector
spaces of equal cardinality (an injection whose codomain has the same size is a bijection, so the
adjoint is injective too), transported along the naturality clause.

Consequently the remaining arithmetic content of `sha2_dual_control` is *exactly* the pair of
nodes `PTembedding/poitouTate_pairing` and `PTembedding/sha_card_euler`: as soon as both are
available, the target below is the two-line application of
`sha2_dual_control_of_pairingAndCard`. -/

section AtomHalves

/-- The tensor product of two finite `𝔽_p`-modules is finite. -/
private lemma finite_tensor_aux (p : ℕ) [Fact p.Prime] (E T : Type) [AddCommGroup E]
    [Module (ZMod p) E] [Finite E] [AddCommGroup T] [Module (ZMod p) T] [Finite T] :
    Finite (TensorProduct (ZMod p) E T) := by
  haveI : Module.Finite (ZMod p) E := Module.Finite.of_finite
  haveI : Module.Finite (ZMod p) T := Module.Finite.of_finite
  haveI : Module.Finite (ZMod p) (TensorProduct (ZMod p) E T) :=
    Module.Finite.tensorProduct (ZMod p) E T
  have h1 : Nat.card (TensorProduct (ZMod p) E T)
      = Nat.card (ZMod p) ^ Module.finrank (ZMod p) (TensorProduct (ZMod p) E T) :=
    Module.natCard_eq_pow_finrank (K := ZMod p) (V := TensorProduct (ZMod p) E T)
  have h2 : 0 < Nat.card (TensorProduct (ZMod p) E T) := by
    rw [h1]
    exact pow_pos (Nat.pos_of_ne_zero (by
      rw [Nat.card_eq_fintype_card, ZMod.card]
      exact (Fact.out : p.Prime).ne_zero)) _
  exact (Nat.card_pos_iff.mp h2).2

/-- A line over `𝔽_p` is finite. -/
private theorem finite_line_aux (p : ℕ) [Fact p.Prime] (T : Type) [AddCommGroup T]
    [Module (ZMod p) T] (h : Module.finrank (ZMod p) T = 1) : Finite T := by
  obtain ⟨e⟩ : Nonempty (ZMod p ≃ₗ[ZMod p] T) :=
    Module.nonempty_linearEquiv_of_finrank_eq_one (R := ZMod p) h
  exact Finite.of_injective e.symm.toFun e.symm.injective

/-- The `𝔽_p`-dual of a finite `𝔽_p`-module is finite. -/
private lemma finite_dualMod_aux (p : ℕ) [Fact p.Prime] (X : Type) [AddCommGroup X]
    [Module (ZMod p) X] [Finite X] : Finite (DualMod p X) := by
  classical
  haveI : NeZero p := ⟨(Fact.out : p.Prime).ne_zero⟩
  haveI : Fintype X := Fintype.ofFinite X
  haveI : Fintype (X → ZMod p) := inferInstance
  exact Finite.of_injective (fun f : DualMod p X => (f : X → ZMod p))
    (fun f g h => LinearMap.ext (congrFun h))

/-- The `𝔽_p`-dual of a finite `𝔽_p`-module has the same cardinality. -/
private theorem natCard_dualMod_aux (p : ℕ) [Fact p.Prime] (M : Type) [AddCommGroup M]
    [Module (ZMod p) M] [Finite M] : Nat.card (DualMod p M) = Nat.card M := by
  haveI : Module.Free (ZMod p) M := Module.Free.of_divisionRing (ZMod p) M
  haveI : Module.Finite (ZMod p) M := Module.Finite.of_finite
  haveI hfin : Finite (DualMod p M) := finite_dualMod_aux p M
  haveI : Module.Finite (ZMod p) (DualMod p M) := Module.Finite.of_finite
  rw [Module.natCard_eq_pow_finrank (K := ZMod p) (V := DualMod p M),
    Module.natCard_eq_pow_finrank (K := ZMod p) (V := M)]
  congr 1
  have b := Module.finBasis (ZMod p) M
  rw [Module.finrank_eq_card_basis b.dualBasis, Module.finrank_eq_card_basis b]
  simp

/-- **The target from the two halves of Tate–Poitou duality.**  Given the left-nondegenerate
natural pairing of the two Tate–Shafarevich groups and the global Euler characteristic
`#Ш²(k,E) = #Ш¹(k,E^∨(1))`, the conclusion of `sha2_dual_control` holds: its controlling
functional is the adjoint `l = Φ_E([c])` of the pairing. -/
theorem sha2_dual_control_of_pairingAndCard (p : ℕ) [Fact p.Prime] (k Ω : Type) [Field k]
    [NumberField k] [Field Ω] [Algebra k Ω] [IsAlgClosure k Ω] (K : IntermediateField k Ω)
    [FiniteDimensional k K] [IsGalois k K] [Fintype (K ≃ₐ[k] K)] (ζ : Ω)
    (hζ : IsPrimitiveRoot ζ p) (hζK : ζ ∈ K)
    (T : Type) [AddCommGroup T] [Module (ZMod p) T] [DistribMulAction (K ≃ₐ[k] K) T]
    [SMulCommClass (K ≃ₐ[k] K) (ZMod p) T]
    (hT : SSGRoute.IsCyclotomicDual p (T := T) (SSGRoute.res k K) ζ)
    (hcard : ∀ (E : Type) [AddCommGroup E] [Module (ZMod p) E]
        [DistribMulAction (K ≃ₐ[k] K) E] [SMulCommClass (K ≃ₐ[k] K) (ZMod p) E] [Finite E],
        Nat.card (Sha2 p k Ω K E)
          = Nat.card (Sha1 p k Ω K (DualMod p (E ⊗[ZMod p] T))))
    (pair : ∀ (E : Type) [AddCommGroup E] [Module (ZMod p) E]
        [DistribMulAction (K ≃ₐ[k] K) E] [SMulCommClass (K ≃ₐ[k] K) (ZMod p) E] [Finite E],
        Sha1 p k Ω K (DualMod p (E ⊗[ZMod p] T)) →ₗ[ZMod p]
          (Sha2 p k Ω K E →ₗ[ZMod p] ZMod p))
    (hleft : ∀ (E : Type) [AddCommGroup E] [Module (ZMod p) E]
        [DistribMulAction (K ≃ₐ[k] K) E] [SMulCommClass (K ≃ₐ[k] K) (ZMod p) E] [Finite E],
        Function.Injective (pair E))
    (hnat : ∀ (E₁ : Type) [AddCommGroup E₁] [Module (ZMod p) E₁]
        [DistribMulAction (K ≃ₐ[k] K) E₁] [SMulCommClass (K ≃ₐ[k] K) (ZMod p) E₁] [Finite E₁]
        (E₂ : Type) [AddCommGroup E₂] [Module (ZMod p) E₂]
        [DistribMulAction (K ≃ₐ[k] K) E₂] [SMulCommClass (K ≃ₐ[k] K) (ZMod p) E₂] [Finite E₂]
        (f : E₁ →ₗ[ZMod p] E₂) (hf : ∀ (g : K ≃ₐ[k] K) (e : E₁), f (g • e) = g • f e)
        (f' : DualMod p (E₂ ⊗[ZMod p] T) →ₗ[ZMod p] DualMod p (E₁ ⊗[ZMod p] T))
        (hf' : ∀ (g : K ≃ₐ[k] K) (φ : DualMod p (E₂ ⊗[ZMod p] T)), f' (g • φ) = g • f' φ)
        (hff' : ∀ (φ : DualMod p (E₂ ⊗[ZMod p] T)) (e : E₁) (t : T),
          f' φ (e ⊗ₜ[ZMod p] t) = φ (f e ⊗ₜ[ZMod p] t))
        (a : Sha1 p k Ω K (DualMod p (E₂ ⊗[ZMod p] T))) (b : Sha2 p k Ω K E₁),
        pair E₂ a (Sha2Map p k Ω K E₁ E₂ f hf b)
          = pair E₁ (Sha1Map p k Ω K (DualMod p (E₂ ⊗[ZMod p] T))
              (DualMod p (E₁ ⊗[ZMod p] T)) f' hf' a) b)
    (E : Type) [AddCommGroup E] [Module (ZMod p) E] [DistribMulAction (K ≃ₐ[k] K) E]
    [SMulCommClass (K ≃ₐ[k] K) (ZMod p) E] [Finite E]
    (c : (Ω ≃ₐ[k] Ω) → (Ω ≃ₐ[k] Ω) → E) (hc : c ∈ Work.SSGRoute.Z2loc p k Ω K E) :
    ∃ l : Work.SSGRoute.Sha1 p k Ω K (Work.SSGRoute.DualMod p (E ⊗[ZMod p] T)) →ₗ[ZMod p] ZMod p,
      ∀ (E₂ : Type) [AddCommGroup E₂] [Module (ZMod p) E₂] [DistribMulAction (K ≃ₐ[k] K) E₂]
        [SMulCommClass (K ≃ₐ[k] K) (ZMod p) E₂] [Finite E₂]
        (f : E →ₗ[ZMod p] E₂) (hf : ∀ (g : K ≃ₐ[k] K) (e : E), f (g • e) = g • f e)
        (f' : Work.SSGRoute.DualMod p (E₂ ⊗[ZMod p] T) →ₗ[ZMod p]
          Work.SSGRoute.DualMod p (E ⊗[ZMod p] T))
        (hf' : ∀ (g : K ≃ₐ[k] K) (φ : Work.SSGRoute.DualMod p (E₂ ⊗[ZMod p] T)),
          f' (g • φ) = g • f' φ)
        (hff' : ∀ (φ : Work.SSGRoute.DualMod p (E₂ ⊗[ZMod p] T)) (e : E) (t : T),
          f' φ (e ⊗ₜ[ZMod p] t) = φ (f e ⊗ₜ[ZMod p] t)),
        l.comp (Work.SSGRoute.Sha1Map p k Ω K (Work.SSGRoute.DualMod p (E₂ ⊗[ZMod p] T))
          (Work.SSGRoute.DualMod p (E ⊗[ZMod p] T)) f' hf') = 0 →
        SSGRoute.IsCoboundary2On (SSGRoute.res k K) ⊤ (fun σ τ => f (c σ τ)) := by
  classical
  -- `T ≅ μ_p^∨` is a line, hence finite
  haveI hTfin : Finite T := finite_line_aux p T hT.1
  -- The adjoint `Φ_E := (b ↦ (a ↦ pair_E a b))` of the pairing, as in
  -- `Work.SSGRoute.PTembedding.tatePoitouEmbedding_of_pairing`.
  have hex : ∃ Φ : ∀ (E' : Type) [AddCommGroup E'] [Module (ZMod p) E']
        [DistribMulAction (K ≃ₐ[k] K) E'] [SMulCommClass (K ≃ₐ[k] K) (ZMod p) E'] [Finite E'],
        Sha2 p k Ω K E' →ₗ[ZMod p]
          (Sha1 p k Ω K (DualMod p (E' ⊗[ZMod p] T)) →ₗ[ZMod p] ZMod p),
      (∀ (E' : Type) [AddCommGroup E'] [Module (ZMod p) E']
          [DistribMulAction (K ≃ₐ[k] K) E'] [SMulCommClass (K ≃ₐ[k] K) (ZMod p) E'] [Finite E'],
        Function.Injective (Φ E')) ∧
      (∀ (E₁ : Type) [AddCommGroup E₁] [Module (ZMod p) E₁]
          [DistribMulAction (K ≃ₐ[k] K) E₁] [SMulCommClass (K ≃ₐ[k] K) (ZMod p) E₁] [Finite E₁]
          (E₂ : Type) [AddCommGroup E₂] [Module (ZMod p) E₂]
          [DistribMulAction (K ≃ₐ[k] K) E₂] [SMulCommClass (K ≃ₐ[k] K) (ZMod p) E₂] [Finite E₂]
          (f : E₁ →ₗ[ZMod p] E₂) (hf : ∀ (g : K ≃ₐ[k] K) (e : E₁), f (g • e) = g • f e)
          (f' : DualMod p (E₂ ⊗[ZMod p] T) →ₗ[ZMod p] DualMod p (E₁ ⊗[ZMod p] T))
          (hf' : ∀ (g : K ≃ₐ[k] K) (φ : DualMod p (E₂ ⊗[ZMod p] T)), f' (g • φ) = g • f' φ)
          (hff' : ∀ (φ : DualMod p (E₂ ⊗[ZMod p] T)) (e : E₁) (t : T),
            f' φ (e ⊗ₜ[ZMod p] t) = φ (f e ⊗ₜ[ZMod p] t))
          (b : Sha2 p k Ω K E₁),
          Φ E₂ (Sha2Map p k Ω K E₁ E₂ f hf b)
            = (Φ E₁ b).comp (Sha1Map p k Ω K (DualMod p (E₂ ⊗[ZMod p] T))
                (DualMod p (E₁ ⊗[ZMod p] T)) f' hf')) := by
    refine ⟨fun E' => LinearMap.flip (pair E'), ?_, ?_⟩
    · -- injectivity of the adjoint: `pair` is injective between `𝔽_p`-spaces of equal size, hence
      -- bijective, and an element of `Ш²` killed by every functional vanishes
      intro E' _ _ _ _ _ b₁ b₂ h12
      have hker : LinearMap.flip (pair E') (b₁ - b₂) = 0 := by rw [map_sub, h12, sub_self]
      have hzero : b₁ - b₂ = 0 := by
        by_contra hne
        obtain ⟨β, hβ⟩ := Module.Projective.exists_dual_ne_zero (ZMod p) hne
        haveI hfET : Finite (E' ⊗[ZMod p] T) := finite_tensor_aux p E' T
        haveI hfD : Finite (DualMod p (E' ⊗[ZMod p] T)) :=
          finite_dualMod_aux p (E' ⊗[ZMod p] T)
        haveI hf1 : Finite (Sha1 p k Ω K (DualMod p (E' ⊗[ZMod p] T))) :=
          finite_sha1 p k Ω K (DualMod p (E' ⊗[ZMod p] T))
        haveI hf2 : Finite (Sha2 p k Ω K E') := by
          have hpos : 0 < Nat.card (Sha2 p k Ω K E') := by
            rw [hcard E']
            exact Nat.card_pos_iff.mpr ⟨⟨0⟩, hf1⟩
          exact (Nat.card_pos_iff.mp hpos).2
        haveI hf2d : Finite (Sha2 p k Ω K E' →ₗ[ZMod p] ZMod p) :=
          finite_dualMod_aux p (Sha2 p k Ω K E')
        have hle : Nat.card (Sha2 p k Ω K E' →ₗ[ZMod p] ZMod p)
            ≤ Nat.card (Sha1 p k Ω K (DualMod p (E' ⊗[ZMod p] T))) := by
          rw [natCard_dualMod_aux p (Sha2 p k Ω K E'), hcard E']
        have hsurj : Function.Surjective (pair E') :=
          ((hleft E').bijective_of_nat_card_le hle).surjective
        obtain ⟨a, ha⟩ := hsurj β
        have h1 : (pair E' a) (b₁ - b₂) = 0 := by
          have h2 : (LinearMap.flip (pair E') (b₁ - b₂)) a = 0 := by rw [hker]; rfl
          simpa [LinearMap.flip_apply] using h2
        exact hβ (by rw [← ha]; exact h1)
      exact sub_eq_zero.mp hzero
    · -- naturality of the adjoint, from the naturality of the pairing
      intro E₁ _ _ _ _ _ E₂ _ _ _ _ _ f hf f' hf' hff' b
      refine LinearMap.ext (fun a => ?_)
      exact hnat E₁ E₂ f hf f' hf' hff' a b
  obtain ⟨Φ, hΦinj, hΦnat⟩ := hex
  exact sha2_dual_control_of_tatePoitouEmbedding p k Ω K ζ hζ hζK E T hT c hc Φ hΦinj hΦnat

end AtomHalves

/-- **The target from the vanishing of `Ш²`** (`l = 0`): if `Ш²(k,M)` is a subsingleton for every
finite coefficient module `M`, then the push-forward of a locally trivial `2`-cocycle along every
coefficient map is a global coboundary, so the zero functional controls `c`.

This is the third complete deduction path to the target, beside the atom
(`sha2_dual_control_of_tatePoitouEmbedding`) and the two halves of Milne I.4.10(a)
(`sha2_dual_control_of_pairingAndCard`).  It is recorded here because a lane of the fleet pursues
`Ш² ≡ 0` (`Submission/Work/SSGRoute/PTCore/sha2_into_sha1_dual_inj.lean`) and because it is the only
path which does not need `Work.SSGRoute.PTCore.sha_card_euler_var`. -/
theorem sha2_dual_control_of_sha2_subsingleton (p : ℕ) [Fact p.Prime] (k Ω : Type) [Field k]
    [NumberField k] [Field Ω] [Algebra k Ω] [IsAlgClosure k Ω] (K : IntermediateField k Ω)
    [FiniteDimensional k K] [IsGalois k K] [Fintype (K ≃ₐ[k] K)] (ζ : Ω)
    (hζ : IsPrimitiveRoot ζ p) (hζK : ζ ∈ K)
    (hSha2 : ∀ (M : Type) [AddCommGroup M] [Module (ZMod p) M]
      [DistribMulAction (K ≃ₐ[k] K) M] [SMulCommClass (K ≃ₐ[k] K) (ZMod p) M] [Finite M],
      Subsingleton (Sha2 p k Ω K M))
    (E T : Type) [AddCommGroup E] [Module (ZMod p) E] [DistribMulAction (K ≃ₐ[k] K) E]
    [SMulCommClass (K ≃ₐ[k] K) (ZMod p) E] [Finite E]
    [AddCommGroup T] [Module (ZMod p) T] [DistribMulAction (K ≃ₐ[k] K) T]
    [SMulCommClass (K ≃ₐ[k] K) (ZMod p) T]
    (hT : SSGRoute.IsCyclotomicDual p (T := T) (SSGRoute.res k K) ζ)
    (c : (Ω ≃ₐ[k] Ω) → (Ω ≃ₐ[k] Ω) → E) (hc : c ∈ Work.SSGRoute.Z2loc p k Ω K E) :
    ∃ l : Work.SSGRoute.Sha1 p k Ω K (Work.SSGRoute.DualMod p (E ⊗[ZMod p] T)) →ₗ[ZMod p] ZMod p,
      ∀ (E₂ : Type) [AddCommGroup E₂] [Module (ZMod p) E₂] [DistribMulAction (K ≃ₐ[k] K) E₂]
        [SMulCommClass (K ≃ₐ[k] K) (ZMod p) E₂] [Finite E₂]
        (f : E →ₗ[ZMod p] E₂) (hf : ∀ (g : K ≃ₐ[k] K) (e : E), f (g • e) = g • f e)
        (f' : Work.SSGRoute.DualMod p (E₂ ⊗[ZMod p] T) →ₗ[ZMod p]
          Work.SSGRoute.DualMod p (E ⊗[ZMod p] T))
        (hf' : ∀ (g : K ≃ₐ[k] K) (φ : Work.SSGRoute.DualMod p (E₂ ⊗[ZMod p] T)),
          f' (g • φ) = g • f' φ)
        (hff' : ∀ (φ : Work.SSGRoute.DualMod p (E₂ ⊗[ZMod p] T)) (e : E) (t : T),
          f' φ (e ⊗ₜ[ZMod p] t) = φ (f e ⊗ₜ[ZMod p] t)),
        l.comp (Work.SSGRoute.Sha1Map p k Ω K (Work.SSGRoute.DualMod p (E₂ ⊗[ZMod p] T))
          (Work.SSGRoute.DualMod p (E ⊗[ZMod p] T)) f' hf') = 0 →
        SSGRoute.IsCoboundary2On (SSGRoute.res k K) ⊤ (fun σ τ => f (c σ τ)) := by
  classical
  refine ⟨0, ?_⟩
  intro E₂ _ _ _ _ _ f hf f' hf' hff' _
  haveI := hSha2 E₂
  have h0 : sha2Class p k Ω K E₂ (isCocycle2_push hc.1 f.toAddMonoidHom hf)
      (isLocConst2_push hc.2.1 f.toAddMonoidHom)
      (fun A hA => isCoboundary2On_push (hc.2.2.1 A hA) f.toAddMonoidHom hf)
      (fun σ hσ => isCoboundary2On_push (hc.2.2.2 σ hσ) f.toAddMonoidHom hf) = 0 :=
    Subsingleton.elim _ _
  exact (sha2Class_eq_zero_iff p k Ω K E₂ (isCocycle2_push hc.1 f.toAddMonoidHom hf)
    (isLocConst2_push hc.2.1 f.toAddMonoidHom)
    (fun A hA => isCoboundary2On_push (hc.2.2.1 A hA) f.toAddMonoidHom hf)
    (fun σ hσ => isCoboundary2On_push (hc.2.2.2 σ hσ) f.toAddMonoidHom hf)).mp h0

theorem sha2_dual_control (p : ℕ) [Fact p.Prime] (k Ω : Type) [Field k] [NumberField k]
    [Field Ω] [Algebra k Ω] [IsAlgClosure k Ω] (K : IntermediateField k Ω) [FiniteDimensional k K]
    [IsGalois k K] [Fintype (K ≃ₐ[k] K)] (ζ : Ω) (hζ : IsPrimitiveRoot ζ p) (hζK : ζ ∈ K)
    (E T : Type) [AddCommGroup E] [Module (ZMod p) E] [DistribMulAction (K ≃ₐ[k] K) E]
    [SMulCommClass (K ≃ₐ[k] K) (ZMod p) E] [Finite E]
    [AddCommGroup T] [Module (ZMod p) T] [DistribMulAction (K ≃ₐ[k] K) T]
    [SMulCommClass (K ≃ₐ[k] K) (ZMod p) T]
    (hT : SSGRoute.IsCyclotomicDual p (T := T) (SSGRoute.res k K) ζ)
    (c : (Ω ≃ₐ[k] Ω) → (Ω ≃ₐ[k] Ω) → E) (hc : c ∈ Work.SSGRoute.Z2loc p k Ω K E) :
    ∃ l : Work.SSGRoute.Sha1 p k Ω K (Work.SSGRoute.DualMod p (E ⊗[ZMod p] T)) →ₗ[ZMod p] ZMod p,
      ∀ (E₂ : Type) [AddCommGroup E₂] [Module (ZMod p) E₂] [DistribMulAction (K ≃ₐ[k] K) E₂]
        [SMulCommClass (K ≃ₐ[k] K) (ZMod p) E₂] [Finite E₂]
        (f : E →ₗ[ZMod p] E₂) (hf : ∀ (g : K ≃ₐ[k] K) (e : E), f (g • e) = g • f e)
        (f' : Work.SSGRoute.DualMod p (E₂ ⊗[ZMod p] T) →ₗ[ZMod p]
          Work.SSGRoute.DualMod p (E ⊗[ZMod p] T))
        (hf' : ∀ (g : K ≃ₐ[k] K) (φ : Work.SSGRoute.DualMod p (E₂ ⊗[ZMod p] T)),
          f' (g • φ) = g • f' φ)
        (hff' : ∀ (φ : Work.SSGRoute.DualMod p (E₂ ⊗[ZMod p] T)) (e : E) (t : T),
          f' φ (e ⊗ₜ[ZMod p] t) = φ (f e ⊗ₜ[ZMod p] t)),
        l.comp (Work.SSGRoute.Sha1Map p k Ω K (Work.SSGRoute.DualMod p (E₂ ⊗[ZMod p] T))
          (Work.SSGRoute.DualMod p (E ⊗[ZMod p] T)) f' hf') = 0 →
        SSGRoute.IsCoboundary2On (SSGRoute.res k K) ⊤ (fun σ τ => f (c σ τ)) := by
  -- The three-line assembly: the whole arithmetic content is the atom
  -- `Work.SSGRoute.tatePoitouEmbedding` (`Submission/Work/SSGRoute/tatePoitouEmbedding.lean`,
  -- node G5 of `DESIGN_PT.md`), proved via the Ext core (`e1aFiled_clean`, `pt_sha2_core`,
  -- `PTembedding/G5Core`); the reduction to it is `sha2_dual_control_of_tatePoitouEmbedding` above.
  obtain ⟨Φ, hΦinj, hΦnat⟩ :=
    Work.SSGRoute.tatePoitouEmbedding p k Ω K ζ hζ hζK T hT
  exact sha2_dual_control_of_tatePoitouEmbedding p k Ω K ζ hζ hζK E T hT c hc Φ hΦinj hΦnat

end Work.SSGRoute


/-! ## G3 of `DESIGN_PT.md`: Bauer/Chebotarev for the dual Selmer group

A continuous `1`-cocycle `b` whose coefficients are a `Gal(K/k)`-module (`K ≤ N`) and which is a
*coboundary* on the decomposition group of every finite place split in `N`, apart from the
conjugates of the finitely many places in `S`, factors through `Gal(N/k)`.  This is the
Chebotarev/Bauer argument of `eq_zero_on_fixingSubgroup_of_eq_zero_on_split` with the exceptional
set carried along; it is the "provable now" input (G3) of the Poitou–Tate design.
-/

namespace Work.SSGRoute

open scoped Pointwise Topology

variable {k Ω : Type} [Field k] [NumberField k] [Field Ω] [Algebra k Ω] [IsAlgClosure k Ω]

/-- The trace on `k` of a place of `Ω` is invariant under `G_k`. -/
private lemma comap_smul_algebraMap (A : ValuationSubring Ω) (g : Ω ≃ₐ[k] Ω) :
    (g • A).comap (algebraMap k Ω) = A.comap (algebraMap k Ω) := by
  ext x
  rw [ValuationSubring.mem_comap, ValuationSubring.mem_comap,
    ValuationSubring.mem_pointwise_smul_iff_inv_smul_mem]
  have hfix : (g⁻¹ : Ω ≃ₐ[k] Ω) • (algebraMap k Ω x) = algebraMap k Ω x := by
    rw [AlgEquiv.smul_def]
    exact (g⁻¹).commutes x
  rw [hfix]

/-- Places of `Ω` lying over the same prime of `k` are `G_k`-conjugate. -/
private lemma isConjPlace_of_comap_eq_sdc {A B : ValuationSubring Ω}
    (h : B.comap (algebraMap k Ω) = A.comap (algebraMap k Ω)) :
    SSGRoute.IsConjPlace k A B := by
  haveI : IsGalois k Ω := IsAlgClosure.isGalois k Ω
  obtain ⟨σ, hσ⟩ :=
    Commons.RingTheory.Valuation.exists_smul_eq_of_comap_eq (F := k) (E := Ω) A B h.symm
  exact ⟨σ, hσ⟩

/-- `IsConjPlace` is symmetric. -/
private lemma isConjPlace_symm_sdc {A B : ValuationSubring Ω} (h : SSGRoute.IsConjPlace k A B) :
    SSGRoute.IsConjPlace k B A := by
  obtain ⟨σ, hσ⟩ := h
  exact ⟨σ⁻¹, by rw [← hσ, inv_smul_smul]⟩

/-- Conjugate places compose: if `A` and `B` are conjugate and `B` and `C` are, so are `A` and
`C`. -/
private lemma isConjPlace_trans_sdc {A B C : ValuationSubring Ω}
    (h₁ : SSGRoute.IsConjPlace k A B) (h₂ : SSGRoute.IsConjPlace k B C) :
    SSGRoute.IsConjPlace k A C := by
  obtain ⟨σ, hσ⟩ := h₁
  obtain ⟨τ, hτ⟩ := h₂
  exact ⟨τ * σ, by rw [mul_smul, hσ, hτ]⟩

/-- Translating a place by `g ∈ G_k` conjugates its decomposition group. -/
private lemma decomp_smul_sdc (A : ValuationSubring Ω) (g : Ω ≃ₐ[k] Ω) :
    SSGRoute.decomp k (g • A) = (SSGRoute.decomp k A).map (MulAut.conj g).toMonoidHom :=
  MulAction.stabilizer_smul_eq_stabilizer_map_conj g A

/-- The subgroup generated by a conjugation-invariant set is normal. -/
private lemma closure_normal_of_conj_invariant_sdc {G : Type*} [Group G] (T : Set G)
    (hT : ∀ g : G, ∀ x ∈ T, g * x * g⁻¹ ∈ T) : (Subgroup.closure T).Normal := by
  rw [Subgroup.normal_iff_map_conj_eq]
  intro g
  have h : Subgroup.map (MulAut.conj g) (Subgroup.closure T) = Subgroup.closure T := by
    rw [MonoidHom.map_closure]
    congr 1
    ext x
    constructor
    · rintro ⟨y, hy, rfl⟩
      exact hT g y hy
    · intro hx
      refine ⟨g⁻¹ * x * g, ?_, ?_⟩
      · simpa using hT g⁻¹ x hx
      · change (MulAut.conj g) (g⁻¹ * x * g) = x
        rw [MulAut.conj_apply]; group
  exact h

end Work.SSGRoute

namespace Work.SSGRoute

open scoped Pointwise Topology

variable {k Ω : Type} [Field k] [NumberField k] [Field Ω] [Algebra k Ω] [IsAlgClosure k Ω]

/-- **Bauer/Chebotarev for the dual Selmer group (G3 of `DESIGN_PT.md`).**  A continuous `1`-cocycle
`b` with coefficients in a `Gal(K/k)`-module (`K ≤ N`) which is a *coboundary* on the decomposition
group of every finite place split completely in `N`, apart from the `G_k`-conjugates of the finite
set `S` of places, factors through `Gal(N/k)`. -/
theorem selmer_dual_inflated_sdc (K N : IntermediateField k Ω) [FiniteDimensional k K] [IsGalois k K]
    [FiniteDimensional k N] [IsGalois k N] (hKN : K ≤ N)
    (M : Type) [AddCommGroup M] [DistribMulAction (K ≃ₐ[k] K) M]
    (S : Finset (ValuationSubring Ω))
    (b : (Ω ≃ₐ[k] Ω) → M) (hb : SSGRoute.IsCocycleOn (SSGRoute.res k K) ⊤ b)
    (hlc : SSGRoute.IsLocConstOn ⊤ b)
    (hsplit : ∀ B : ValuationSubring Ω, SSGRoute.IsFinPlace k B →
      (∀ A ∈ S, ¬ SSGRoute.IsConjPlace k A B) → SSGRoute.IsSplitIn k N B →
        SSGRoute.IsCoboundaryOn (SSGRoute.res k K) (SSGRoute.decomp k B) b) :
    ∃ b₀ : (N ≃ₐ[k] N) → M, ∀ σ : Ω ≃ₐ[k] Ω, b σ = b₀ (SSGRoute.res k N σ) := by
  classical
  -- ## the coefficient action of `G_N` is trivial
  have hNtriv : ∀ (σ : Ω ≃ₐ[k] Ω), σ ∈ N.fixingSubgroup → ∀ m : M,
      SSGRoute.res k K σ • m = m := by
    intro σ hσ m
    have hσK : σ ∈ K.fixingSubgroup := (IntermediateField.fixingSubgroup_le hKN) hσ
    have h1 : SSGRoute.res k K σ = 1 := by
      rw [← MonoidHom.mem_ker, IntermediateField.restrictNormalHom_ker K]
      exact hσK
    rw [h1, one_smul]
  have hNnorm : (N.fixingSubgroup : Subgroup (Ω ≃ₐ[k] Ω)).Normal :=
    IsGalois.fixingSubgroup_normal_of_isGalois N
  -- ## `b` vanishes on the relevant decomposition groups
  have hzero : ∀ (B : ValuationSubring Ω), SSGRoute.IsFinPlace k B →
      (∀ A ∈ S, ¬ SSGRoute.IsConjPlace k A B) → SSGRoute.IsSplitIn k N B →
      ∀ τ ∈ SSGRoute.decomp k B, b τ = 0 := by
    intro B hB hS hBsplt τ hτ
    obtain ⟨m, hm⟩ := hsplit B hB hS hBsplt
    rw [hm τ hτ]
    have : SSGRoute.res k K τ • m = m := hNtriv τ (hBsplt hτ) m
    rw [this, sub_self]
  -- ## the subgroup generated by these decomposition groups
  set T : Set (Ω ≃ₐ[k] Ω) := {τ | ∃ B : ValuationSubring Ω, SSGRoute.IsFinPlace k B ∧
    (∀ A ∈ S, ¬ SSGRoute.IsConjPlace k A B) ∧ SSGRoute.IsSplitIn k N B ∧
    τ ∈ SSGRoute.decomp k B} with hTdef
  have hTconj : ∀ g : Ω ≃ₐ[k] Ω, ∀ x ∈ T, g * x * g⁻¹ ∈ T := by
    rintro g τ ⟨B, hB, hS, hBsplt, hτD⟩
    refine ⟨g • B, ?_, ?_, ?_, ?_⟩
    · simp only [SSGRoute.IsFinPlace]
      rw [comap_smul_algebraMap]
      exact hB
    · intro A hA hconj
      exact hS A hA (isConjPlace_trans_sdc hconj ⟨g⁻¹, inv_smul_smul g B⟩)
    · simp only [SSGRoute.IsSplitIn]
      rw [decomp_smul_sdc, Subgroup.map_le_iff_le_comap]
      intro x hx
      simpa using hNnorm.conj_mem x (hBsplt hx) g
    · rw [decomp_smul_sdc]
      exact Subgroup.mem_map_of_mem (MulAut.conj g).toMonoidHom hτD
  set H : Subgroup (Ω ≃ₐ[k] Ω) := Subgroup.closure T with hHdef
  have hHle : H ≤ N.fixingSubgroup := by
    rw [hHdef]
    refine (Subgroup.closure_le _).mpr ?_
    rintro τ ⟨B, hB, hS, hBsplt, hτ⟩
    exact hBsplt hτ
  have hHnormal : H.Normal := by
    rw [hHdef]
    exact closure_normal_of_conj_invariant_sdc T hTconj
  have hHker : ∀ h ∈ H, b h = 0 := by
    have hb1 : b 1 = 0 := by
      have h := hb 1 trivial 1 trivial
      rw [mul_one, map_one, one_smul] at h
      exact (add_left_cancel (by rw [add_zero]; exact h)).symm
    let S₀ : Subgroup (Ω ≃ₐ[k] Ω) :=
      { carrier := {x | b x = 0}
        one_mem' := hb1
        mul_mem' := by
          intro x y hx hy
          show b (x * y) = 0
          rw [hb x trivial y trivial, hy, smul_zero, add_zero, hx]
        inv_mem' := by
          intro x hx
          have h := hb x trivial x⁻¹ trivial
          rw [mul_inv_cancel, hb1, hx, zero_add] at h
          have h2 := congrArg (fun z : M => (SSGRoute.res k K x)⁻¹ • z) h
          rw [smul_zero, inv_smul_smul] at h2
          exact h2.symm }
    have hTS₀ : T ⊆ S₀ := by
      rintro x ⟨B, hB, hS, hBsplt, hxD⟩
      exact hzero B hB hS hBsplt x hxD
    have hHleS₀ : H ≤ S₀ := by
      rw [hHdef]
      exact Subgroup.closure_le S₀ |>.mpr hTS₀
    intro h hh
    exact hHleS₀ hh
  -- ## a large finite Galois level `M'`
  obtain ⟨U, hUopen, hUcst⟩ := hlc
  have hGNopen : IsOpen (N.fixingSubgroup : Set (Ω ≃ₐ[k] Ω)) :=
    IntermediateField.fixingSubgroup_isOpen N
  have hVopen : IsOpen (((U ⊓ N.fixingSubgroup : Subgroup (Ω ≃ₐ[k] Ω))) : Set (Ω ≃ₐ[k] Ω)) := by
    rw [Subgroup.coe_inf]
    exact hUopen.inter hGNopen
  have hVnhds : (((U ⊓ N.fixingSubgroup : Subgroup (Ω ≃ₐ[k] Ω))) : Set (Ω ≃ₐ[k] Ω)) ∈
      𝓝 (1 : Ω ≃ₐ[k] Ω) :=
    hVopen.mem_nhds (Subgroup.mem_inf.mpr ⟨U.one_mem, N.fixingSubgroup.one_mem⟩)
  obtain ⟨E', hEfin, hEnorm, hEU⟩ :=
    (krullTopology_mem_nhds_one_iff_of_normal k Ω
      (((U ⊓ N.fixingSubgroup : Subgroup (Ω ≃ₐ[k] Ω))) : Set (Ω ≃ₐ[k] Ω))).mp hVnhds
  let M' : IntermediateField k Ω := E' ⊔ N
  haveI hEfinI : FiniteDimensional k E' := hEfin
  haveI hEnormI : Normal k E' := hEnorm
  haveI hMfin : FiniteDimensional k M' := inferInstance
  haveI hMnorm : Normal k M' := inferInstance
  haveI hMgal : IsGalois k M' := Commons.FieldTheory.Galois.isGalois_of_normal_of_charZero
  have hGMle : M'.fixingSubgroup ≤ U ⊓ N.fixingSubgroup := by
    intro x hx
    rw [show M'.fixingSubgroup = E'.fixingSubgroup ⊓ N.fixingSubgroup by
      dsimp only [M']
      rw [IntermediateField.fixingSubgroup_sup]] at hx
    exact ⟨(hEU hx.1).1, hx.2⟩
  have hGMGN : M'.fixingSubgroup ≤ N.fixingSubgroup := fun x hx => (hGMle hx).2
  -- ## the places split in `N`, not over the primes below `S`, have their decomposition group in `H`
  have hHsplit_le : ∀ A : ValuationSubring Ω, SSGRoute.IsFinPlace k A →
      A.comap (algebraMap k Ω) ∉ S.image (fun X => X.comap (algebraMap k Ω)) →
      SSGRoute.IsSplitIn k N A → SSGRoute.decomp k A ≤ H := by
    intro A hAfin hAnotS hAsplit x hx
    rw [hHdef]
    refine Subgroup.subset_closure ⟨A, hAfin, ?_, hAsplit, hx⟩
    intro A' hA'S hconj
    have h1 : A.comap (algebraMap k Ω) = A'.comap (algebraMap k Ω) := by
      obtain ⟨g, hg⟩ := hconj
      rw [← hg, comap_smul_algebraMap]
    have h2 : A'.comap (algebraMap k Ω) ∈ S.image (fun X => X.comap (algebraMap k Ω)) :=
      Finset.mem_image.mpr ⟨A', hA'S, rfl⟩
    exact hAnotS (h1 ▸ h2)
  -- ## Chebotarev/Bauer: `G_N = H · G_M'`
  have hcrux : ∀ τ ∈ N.fixingSubgroup, ∃ h ∈ H, ∃ g ∈ M'.fixingSubgroup, h * g = τ := by
    intro τ hτ
    let φ : (Ω ≃ₐ[k] Ω) →* (M' ≃ₐ[k] M') :=
      AlgEquiv.restrictNormalHom (F := k) (K₁ := Ω) ↥M'
    have hφsurj : Function.Surjective φ :=
      AlgEquiv.restrictNormalHom_surjective (F := k) (K₁ := ↥M') (E := Ω)
    let K₁ : Subgroup (M' ≃ₐ[k] M') := H.map φ
    have hK₁n : K₁.Normal := Subgroup.Normal.map hHnormal φ hφsurj
    let H' : Subgroup (Ω ≃ₐ[k] Ω) := K₁.comap φ
    have hH'n : H'.Normal := hK₁n.comap φ
    have hH'H : H ≤ H' := fun x hx => Subgroup.mem_map_of_mem φ hx
    have hH'N : H' ≤ N.fixingSubgroup := by
      intro x hx
      have hx' : φ x ∈ K₁ := hx
      obtain ⟨h, hhH, hhh⟩ := Subgroup.mem_map.mp hx'
      have hker : h⁻¹ * x ∈ M'.fixingSubgroup := by
        rw [← IntermediateField.restrictNormalHom_ker M', MonoidHom.mem_ker]
        show φ (h⁻¹ * x) = 1
        rw [map_mul, map_inv, hhh, inv_mul_cancel]
      have hxeq : x = h * (h⁻¹ * x) := by group
      rw [hxeq]
      exact N.fixingSubgroup.mul_mem (hHle hhH) (hGMGN hker)
    have hM'H' : M'.fixingSubgroup ≤ H' := by
      intro x hx
      rw [← IntermediateField.restrictNormalHom_ker M'] at hx
      have hx1 : φ x = 1 := MonoidHom.mem_ker.mp hx
      change φ x ∈ K₁
      rw [hx1]
      exact K₁.one_mem
    obtain ⟨hNF, hFfin, hFnorm, hFfix⟩ :=
      fixedField_of_le_fixingSubgroup k Ω N H' hH'N hH'n M' hM'H'
    set F : IntermediateField k Ω := IntermediateField.fixedField H' with hFdef
    haveI hFfinI : FiniteDimensional k F := hFfin
    haveI hFnormI : Normal k F := hFnorm
    haveI hFgalI : IsGalois k F :=
      Commons.FieldTheory.Galois.isGalois_of_normal_of_charZero
    have hsplitF : ∀ A : ValuationSubring Ω, SSGRoute.IsFinPlace k A →
        A.comap (algebraMap k Ω) ∉ S.image (fun X => X.comap (algebraMap k Ω)) →
        SSGRoute.IsSplitIn k N A → SSGRoute.IsSplitIn k F A := by
      intro A hAfin hAnotS hAsplit
      refine le_trans (hHsplit_le A hAfin hAnotS hAsplit) ?_
      intro x hx
      rw [hFdef, hFfix]
      exact hH'H hx
    have hFN : F ≤ N :=
      bauer_of_chebotarev k Ω F N (S.image (fun X => X.comap (algebraMap k Ω))) hsplitF
    have hFeqN : F = N := le_antisymm hFN hNF
    have hGN : N.fixingSubgroup = H' := by
      rw [← hFeqN, hFdef, hFfix]
    have hτH' : τ ∈ H' := hGN ▸ hτ
    obtain ⟨h, hhH, hhτ⟩ := Subgroup.mem_map.mp hτH'
    refine ⟨h, hhH, h⁻¹ * τ, ?_, ?_⟩
    · rw [← IntermediateField.restrictNormalHom_ker M', MonoidHom.mem_ker]
      show φ (h⁻¹ * τ) = 1
      rw [map_mul, map_inv, hhτ, inv_mul_cancel]
    · group
  -- ## hence `b` vanishes on `G_N`
  have hbzero : ∀ τ ∈ N.fixingSubgroup, b τ = 0 := by
    intro τ hτ
    obtain ⟨h, hhH, g, hgM, hhg⟩ := hcrux τ hτ
    have hgu : g⁻¹ ∈ U := U.inv_mem (hGMle hgM).1
    have hσg : τ * g⁻¹ = h := by
      have := congrArg (fun x => x * g⁻¹) hhg
      simpa using this.symm
    calc b τ = b (τ * g⁻¹) := (hUcst τ trivial g⁻¹ hgu trivial).symm
      _ = b h := by rw [hσg]
      _ = 0 := hHker h hhH
  -- ## factor through `res k N`
  have hsurj : Function.Surjective (SSGRoute.res k N) :=
    AlgEquiv.restrictNormalHom_surjective (F := k) (K₁ := ↥N) (E := Ω)
  refine ⟨fun x => b (Classical.choose (hsurj x)), ?_⟩
  intro σ
  set σ₀ : Ω ≃ₐ[k] Ω := Classical.choose (hsurj (SSGRoute.res k N σ)) with hσ₀
  have hspec : SSGRoute.res k N σ₀ = SSGRoute.res k N σ := Classical.choose_spec (hsurj _)
  have hn : σ₀⁻¹ * σ ∈ N.fixingSubgroup := by
    rw [← IntermediateField.restrictNormalHom_ker N, MonoidHom.mem_ker]
    simp only [map_mul, map_inv, hspec, inv_mul_cancel]
  have hright : b (σ₀ * (σ₀⁻¹ * σ)) = b σ₀ := by
    have h := hb σ₀ trivial (σ₀⁻¹ * σ) trivial
    rw [hbzero (σ₀⁻¹ * σ) hn, smul_zero, add_zero] at h
    exact h
  rw [show b σ = b (σ₀ * (σ₀⁻¹ * σ)) from by rw [mul_inv_cancel_left]]
  exact hright

end Work.SSGRoute
