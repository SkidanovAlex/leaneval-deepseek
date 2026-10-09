import Mathlib
import Submission.Work.SSGRoute.kummerBase_euler_additive
import Submission.Work.SSGRoute.LTDDefs.Basic
import Submission.Work.SSGRoute.LTDDefs.H1loc_iso_H1cont
import Submission.Work.SSGRoute.LTDDefs.H2locEquivH2
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# Additivity of the Euler characteristic in the vocabulary of `kummerBase_euler`

`Submission/Work/SSGRoute/kummerBase_euler_additive.lean` proves the multiplicativity of the
Euler characteristic `χ(G,M) = |H⁰||H²|/|H¹|` over a short exact sequence of discrete
`G`-modules, in the continuous-cochain model `Work.AbsoluteKummer`.  This file transports that
statement into the vocabulary in which the target `Work.SSGRoute.kummerBase_euler` is stated:
the locally constant cochain model `H0loc`/`H1loc`/`H2loc` of `LTDDefs/Basic.lean` at the
decomposition group `D_A = decomp k A` of a finite place.

Writing `h⁰,h¹,h²` for the `𝔽_p`-dimensions of `H0loc`, `H1loc`, `H2loc`, the transported
statement is the *additivity* of `X ↦ h⁰(X) - h¹(X) + h²(X)` over a short exact sequence
`0 → M → N → P → 0` of finite `𝔽_p[Gal(K/k)]`-modules:

`h⁰(M) + h⁰(P) + h¹(N) + h²(M) + h²(P) = h⁰(N) + h¹(M) + h¹(P) + h²(N)`.

The passage uses the model bridges `H1locEquivH1` and `H2locEquivH2` (both of which hold for an
*arbitrary* action of `↥(decomp k A)` compatible with `res k K`) together with
`Module.natCard_eq_pow_finrank`, which converts the cardinality relation into a relation of
`𝔽_p`-dimensions.
-/

open Work

namespace Work.SSGRoute

noncomputable section

variable (p : ℕ) [Fact p.Prime] (k Ω : Type) [Field k] [NumberField k] [Field Ω] [Algebra k Ω]
  [IsAlgClosure k Ω]

/-- `Nat.card` of a finite `𝔽_p`-module is `p` to its dimension. -/
theorem natCard_eq_pow_finrank_zmod {X : Type} [AddCommGroup X] [Module (ZMod p) X] [Finite X] :
    Nat.card X = p ^ Module.finrank (ZMod p) X := by
  haveI : Module.Finite (ZMod p) X := Module.Finite.of_finite
  rw [Module.natCard_eq_pow_finrank (K := ZMod p) (V := X), Nat.card_eq_fintype_card, ZMod.card]

/-- With a `↥(decomp k A)`-action compatible with `res k K`, the invariants of the local model
`H0loc` and of the continuous-cochain model `H0` coincide. -/
theorem H0loc_eq_H0_of_compat (K : IntermediateField k Ω) [FiniteDimensional k K] [IsGalois k K]
    (A : ValuationSubring Ω) (M : Type) [AddCommGroup M] [Module (ZMod p) M]
    [DistribMulAction (K ≃ₐ[k] K) M] [SMulCommClass (K ≃ₐ[k] K) (ZMod p) M]
    [DistribMulAction ↥(SSGRoute.decomp k A) M]
    (hm : ∀ (h : ↥(SSGRoute.decomp k A)) (m : M), h • m = SSGRoute.res k K (h : Ω ≃ₐ[k] Ω) • m) :
    (H0loc p k Ω K M (SSGRoute.decomp k A) : Set M) =
      (Work.AbsoluteKummer.H0 ↥(SSGRoute.decomp k A) M : Set M) := by
  ext m
  rw [SetLike.mem_coe, SetLike.mem_coe, H0loc, Work.AbsoluteKummer.H0,
    Work.GroupCohomology.mem_invariants]
  constructor
  · intro h g
    rw [hm g m]
    exact h (g : Ω ≃ₐ[k] Ω) g.2
  · intro h g hg
    rw [← hm ⟨g, hg⟩ m]
    exact h ⟨g, hg⟩

/-- **Additivity of the Euler characteristic over a short exact sequence, in the vocabulary of
`kummerBase_euler`.**  For a finite place `A` of `Ω` over `k`, a compatible action of
`D_A = decomp k A` on finite `𝔽_p[Gal(K/k)]`-modules `M`, `N`, `P` fitting into a short exact
sequence `0 → M → N → P → 0` (in the continuous-cochain model), and with
`H³(D_A,M) = 0` and `H1loc`, `H2loc` finite at `M`, `N`, `P`,

`h⁰(M) + h⁰(P) + h¹(N) + h²(M) + h²(P) = h⁰(N) + h¹(M) + h¹(P) + h²(N)`,

where `hⁱ` is the `𝔽_p`-dimension of `Hⁱ(D_A, ·)`.  Equivalently `χ(N) = χ(M)·χ(P)`. -/
theorem euler_alternating_loc
    (K : IntermediateField k Ω) [FiniteDimensional k K] [IsGalois k K]
    (A : ValuationSubring Ω) (hA : SSGRoute.IsFinPlace k A)
    (hclosed : IsClosed (SSGRoute.decomp k A : Set (Ω ≃ₐ[k] Ω)))
    {M N P : Type} [AddCommGroup M] [AddCommGroup N] [AddCommGroup P]
    [Module (ZMod p) M] [Module (ZMod p) N] [Module (ZMod p) P]
    [DistribMulAction (K ≃ₐ[k] K) M] [DistribMulAction (K ≃ₐ[k] K) N]
    [DistribMulAction (K ≃ₐ[k] K) P]
    [SMulCommClass (K ≃ₐ[k] K) (ZMod p) M] [SMulCommClass (K ≃ₐ[k] K) (ZMod p) N]
    [SMulCommClass (K ≃ₐ[k] K) (ZMod p) P]
    [DistribMulAction ↥(SSGRoute.decomp k A) M] [DistribMulAction ↥(SSGRoute.decomp k A) N]
    [DistribMulAction ↥(SSGRoute.decomp k A) P]
    (hm : ∀ (h : ↥(SSGRoute.decomp k A)) (m : M),
      h • m = SSGRoute.res k K (h : Ω ≃ₐ[k] Ω) • m)
    (hn : ∀ (h : ↥(SSGRoute.decomp k A)) (m : N),
      h • m = SSGRoute.res k K (h : Ω ≃ₐ[k] Ω) • m)
    (hp : ∀ (h : ↥(SSGRoute.decomp k A)) (m : P),
      h • m = SSGRoute.res k K (h : Ω ≃ₐ[k] Ω) • m)
    [Finite M] [Finite N] [Finite P]
    (S : Work.AbsoluteKummer.ShortExactSeq ↥(SSGRoute.decomp k A) M N P)
    (h3M : Subsingleton (Work.SSGRoute.H3 (M := M) ↥(SSGRoute.decomp k A)))
    [Finite (H1loc p k Ω K M (SSGRoute.decomp k A))]
    [Finite (H2loc p k Ω K M (SSGRoute.decomp k A))]
    [Finite (H1loc p k Ω K N (SSGRoute.decomp k A))]
    [Finite (H2loc p k Ω K N (SSGRoute.decomp k A))]
    [Finite (H1loc p k Ω K P (SSGRoute.decomp k A))]
    [Finite (H2loc p k Ω K P (SSGRoute.decomp k A))] :
    Module.finrank (ZMod p) ↥(H0loc p k Ω K M (SSGRoute.decomp k A)) +
      Module.finrank (ZMod p) ↥(H0loc p k Ω K P (SSGRoute.decomp k A)) +
      Module.finrank (ZMod p) (H1loc p k Ω K N (SSGRoute.decomp k A)) +
      Module.finrank (ZMod p) (H2loc p k Ω K M (SSGRoute.decomp k A)) +
      Module.finrank (ZMod p) (H2loc p k Ω K P (SSGRoute.decomp k A)) =
    Module.finrank (ZMod p) ↥(H0loc p k Ω K N (SSGRoute.decomp k A)) +
      Module.finrank (ZMod p) (H1loc p k Ω K M (SSGRoute.decomp k A)) +
      Module.finrank (ZMod p) (H1loc p k Ω K P (SSGRoute.decomp k A)) +
      Module.finrank (ZMod p) (H2loc p k Ω K N (SSGRoute.decomp k A)) := by
  -- finiteness of the local `H0loc` groups, and of the continuous model
  haveI hF0M : Finite ↥(H0loc p k Ω K M (SSGRoute.decomp k A)) :=
    Finite.of_injective (Subtype.val) Subtype.val_injective
  haveI hF0N : Finite ↥(H0loc p k Ω K N (SSGRoute.decomp k A)) :=
    Finite.of_injective (Subtype.val) Subtype.val_injective
  haveI hF0P : Finite ↥(H0loc p k Ω K P (SSGRoute.decomp k A)) :=
    Finite.of_injective (Subtype.val) Subtype.val_injective
  haveI hF0Ma : Finite ↥(Work.AbsoluteKummer.H0 ↥(SSGRoute.decomp k A) M) :=
    Finite.of_injective (Subtype.val) Subtype.val_injective
  haveI hF0Na : Finite ↥(Work.AbsoluteKummer.H0 ↥(SSGRoute.decomp k A) N) :=
    Finite.of_injective (Subtype.val) Subtype.val_injective
  haveI hF0Pa : Finite ↥(Work.AbsoluteKummer.H0 ↥(SSGRoute.decomp k A) P) :=
    Finite.of_injective (Subtype.val) Subtype.val_injective
  haveI hF1Ma : Finite (Work.AbsoluteKummer.H1 ↥(SSGRoute.decomp k A) M) :=
    Finite.of_injective (H1locEquivH1 p k Ω K M (SSGRoute.decomp k A) hm).symm
      (H1locEquivH1 p k Ω K M (SSGRoute.decomp k A) hm).symm.injective
  haveI hF1Na : Finite (Work.AbsoluteKummer.H1 ↥(SSGRoute.decomp k A) N) :=
    Finite.of_injective (H1locEquivH1 p k Ω K N (SSGRoute.decomp k A) hn).symm
      (H1locEquivH1 p k Ω K N (SSGRoute.decomp k A) hn).symm.injective
  haveI hF1Pa : Finite (Work.AbsoluteKummer.H1 ↥(SSGRoute.decomp k A) P) :=
    Finite.of_injective (H1locEquivH1 p k Ω K P (SSGRoute.decomp k A) hp).symm
      (H1locEquivH1 p k Ω K P (SSGRoute.decomp k A) hp).symm.injective
  have h2M := Classical.choice
    (LTDDefs.H2locEquivH2 p k Ω K M (SSGRoute.decomp k A) hclosed hm)
  have h2N := Classical.choice
    (LTDDefs.H2locEquivH2 p k Ω K N (SSGRoute.decomp k A) hclosed hn)
  have h2P := Classical.choice
    (LTDDefs.H2locEquivH2 p k Ω K P (SSGRoute.decomp k A) hclosed hp)
  haveI hF2Ma : Finite (Work.AbsoluteKummer.H2 ↥(SSGRoute.decomp k A) M) :=
    Finite.of_injective h2M.symm h2M.symm.injective
  haveI hF2Na : Finite (Work.AbsoluteKummer.H2 ↥(SSGRoute.decomp k A) N) :=
    Finite.of_injective h2N.symm h2N.symm.injective
  haveI hF2Pa : Finite (Work.AbsoluteKummer.H2 ↥(SSGRoute.decomp k A) P) :=
    Finite.of_injective h2P.symm h2P.symm.injective
  -- the model bridges, as cardinality equalities
  have c0M : Nat.card ↥(H0loc p k Ω K M (SSGRoute.decomp k A)) =
      Nat.card ↥(Work.AbsoluteKummer.H0 ↥(SSGRoute.decomp k A) M) :=
    Nat.card_congr (Set.equivOfEq (H0loc_eq_H0_of_compat p k Ω K A M hm))
  have c0N : Nat.card ↥(H0loc p k Ω K N (SSGRoute.decomp k A)) =
      Nat.card ↥(Work.AbsoluteKummer.H0 ↥(SSGRoute.decomp k A) N) :=
    Nat.card_congr (Set.equivOfEq (H0loc_eq_H0_of_compat p k Ω K A N hn))
  have c0P : Nat.card ↥(H0loc p k Ω K P (SSGRoute.decomp k A)) =
      Nat.card ↥(Work.AbsoluteKummer.H0 ↥(SSGRoute.decomp k A) P) :=
    Nat.card_congr (Set.equivOfEq (H0loc_eq_H0_of_compat p k Ω K A P hp))
  have c1M : Nat.card (H1loc p k Ω K M (SSGRoute.decomp k A)) =
      Nat.card (Work.AbsoluteKummer.H1 ↥(SSGRoute.decomp k A) M) :=
    Nat.card_congr (H1locEquivH1 p k Ω K M (SSGRoute.decomp k A) hm).toEquiv
  have c1N : Nat.card (H1loc p k Ω K N (SSGRoute.decomp k A)) =
      Nat.card (Work.AbsoluteKummer.H1 ↥(SSGRoute.decomp k A) N) :=
    Nat.card_congr (H1locEquivH1 p k Ω K N (SSGRoute.decomp k A) hn).toEquiv
  have c1P : Nat.card (H1loc p k Ω K P (SSGRoute.decomp k A)) =
      Nat.card (Work.AbsoluteKummer.H1 ↥(SSGRoute.decomp k A) P) :=
    Nat.card_congr (H1locEquivH1 p k Ω K P (SSGRoute.decomp k A) hp).toEquiv
  have c2M : Nat.card (H2loc p k Ω K M (SSGRoute.decomp k A)) =
      Nat.card (Work.AbsoluteKummer.H2 ↥(SSGRoute.decomp k A) M) :=
    Nat.card_congr h2M.toEquiv
  have c2N : Nat.card (H2loc p k Ω K N (SSGRoute.decomp k A)) =
      Nat.card (Work.AbsoluteKummer.H2 ↥(SSGRoute.decomp k A) N) :=
    Nat.card_congr h2N.toEquiv
  have c2P : Nat.card (H2loc p k Ω K P (SSGRoute.decomp k A)) =
      Nat.card (Work.AbsoluteKummer.H2 ↥(SSGRoute.decomp k A) P) :=
    Nat.card_congr h2P.toEquiv
  -- the alternating relation in the continuous model
  have haux := eulerChar_alternating_natCard S h3M
  rw [← c0M, ← c0P, ← c1N, ← c2M, ← c2P,
    ← c0N, ← c1M, ← c1P, ← c2N] at haux
  -- convert cardinalities into dimensions
  rw [natCard_eq_pow_finrank_zmod (p := p) (X := ↥(H0loc p k Ω K M (SSGRoute.decomp k A))),
    natCard_eq_pow_finrank_zmod (p := p) (X := ↥(H0loc p k Ω K P (SSGRoute.decomp k A))),
    natCard_eq_pow_finrank_zmod (p := p) (X := H1loc p k Ω K N (SSGRoute.decomp k A)),
    natCard_eq_pow_finrank_zmod (p := p) (X := H2loc p k Ω K M (SSGRoute.decomp k A)),
    natCard_eq_pow_finrank_zmod (p := p) (X := H2loc p k Ω K P (SSGRoute.decomp k A)),
    natCard_eq_pow_finrank_zmod (p := p) (X := ↥(H0loc p k Ω K N (SSGRoute.decomp k A))),
    natCard_eq_pow_finrank_zmod (p := p) (X := H1loc p k Ω K M (SSGRoute.decomp k A)),
    natCard_eq_pow_finrank_zmod (p := p) (X := H1loc p k Ω K P (SSGRoute.decomp k A)),
    natCard_eq_pow_finrank_zmod (p := p) (X := H2loc p k Ω K N (SSGRoute.decomp k A))] at haux
  repeat rw [← pow_add] at haux
  have hfin := Nat.pow_right_injective (Fact.out : p.Prime).two_le haux
  omega

end

end Work.SSGRoute
