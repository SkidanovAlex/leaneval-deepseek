import Mathlib
import Submission.Work.ProPDeficiency.Basic
import Submission.Work.ProPDeficiency.HomRank
import Submission.Commons.GroupTheory.PGroup.burnside_basis
import Submission.Commons.GroupTheory.PGroup.frattini_eq_pow_sup_commutator
import Submission.Commons.GroupTheory.PGroup.quotient_frattini_exponent_p

/-!
# `dGens G = dim_{𝔽_p} H¹(G, 𝔽_p)` for a finite `p`-group

**Namespace** `Work.ProPDeficiency`; module `Submission.Work.ProPDeficiency.dGens_eq_pHomDim_of_isPGroup`.

The main result is `dGens_eq_pHomDim_of_isPGroup`: for a finite `p`-group `G`,

`pHomDim p G = dGens G`,

i.e. the `𝔽_p`-dimension of `H¹(G, 𝔽_p) = Hom(G, 𝔽_p)` (recorded as `Nat.log p` of the cardinality
of `HomFp p G = G →* Multiplicative (ZMod p)`, see `HomRank`) equals the minimal number of
generators of `G` (see `Basic`).

The proof is the classical one: the Frattini subgroup `Φ(G) = G^p[G,G]` is killed by every
homomorphism to `𝔽_p`, so precomposition with the quotient map `G ⧸ Φ(G) ↠ G` is a bijection
`HomFp p (G ⧸ Φ(G)) ≃ HomFp p G`; the quotient `G ⧸ Φ(G)` is elementary abelian of order
`p ^ dGens G` (Burnside's basis theorem, `Commons.GroupTheory.PGroup.burnside_basis`), and the
`𝔽_p`-span of an elementary abelian `p`-group has the same number of additive homomorphisms to
`𝔽_p` as the group has elements (duality of finite-dimensional `𝔽_p`-vector spaces).
-/

set_option autoImplicit false
set_option linter.unusedVariables false
set_option linter.style.haveILetI false

namespace Work.ProPDeficiency

open scoped IsMulCommutative

/-! ## Elementary abelian `p`-groups and their duals -/

/-- Every element of `𝔽_p = ZMod p`, written multiplicatively as `Multiplicative (ZMod p)`, has
order dividing `p`. -/
private theorem multiplicate_zmod_pow_prime {p : ℕ} [Fact p.Prime]
    (x : Multiplicative (ZMod p)) : x ^ p = 1 := by
  have h : Nat.card (Multiplicative (ZMod p)) = p := natCard_multiplicative_zmod
  simpa [h] using pow_card_eq_one' (x := x)

/-- The number of additive homomorphisms from a finite `𝔽_p`-vector space to `𝔽_p` equals the
order of the space: `|Hom(A, 𝔽_p)| = p ^ dim A`.  This is the self-duality of finite-dimensional
vector spaces, in counting form. -/
private theorem natCard_addMonoidHom_zmod {p : ℕ} [Fact p.Prime] (A : Type*) [AddCommGroup A]
    [Module (ZMod p) A] [Finite A] :
    Nat.card (A →+ ZMod p) = p ^ Module.finrank (ZMod p) A := by
  haveI hA : Module.Finite (ZMod p) A := Module.Finite.of_finite
  haveI hD : Module.Finite (ZMod p) (Module.Dual (ZMod p) A) := inferInstance
  rw [Nat.card_congr (AddMonoidHom.toZModLinearMapEquiv p).toEquiv]
  rw [Module.natCard_eq_pow_finrank (K := ZMod p) (V := Module.Dual (ZMod p) A)]
  rw [Subspace.dual_finrank_eq (K := ZMod p) (V := A)]
  rw [Nat.card_eq_fintype_card, ZMod.card]

/-! ## The Frattini quotient -/

/-- In a finite `p`-group the derived subgroup is contained in the Frattini subgroup: every
maximal subgroup has index `p`, hence has abelian quotient. -/
private theorem commutator_le_frattini_of_isPGroup {p : ℕ} [Fact p.Prime] {G : Type*} [Group G]
    [Finite G] (hG : IsPGroup p G) : commutator G ≤ frattini G := by
  rw [frattini, Order.radical]
  refine le_iInf fun M => le_iInf fun hM => ?_
  haveI : Group.IsNilpotent G := hG.isNilpotent
  haveI hMn : M.Normal :=
    Subgroup.NormalizerCondition.normal_of_coatom M
      (Group.normalizerCondition_of_isNilpotent (G := G)) hM
  have hcard : Nat.card (G ⧸ M) = p :=
    Commons.GroupTheory.PGroup.natCard_quotient_coatom_eq_prime hG hM
  haveI : IsMulCommutative (G ⧸ M) := (isCyclic_of_prime_card hcard).isMulCommutative
  exact (Subgroup.Normal.quotient_commutative_iff_commutator_le (N := M)).mp
    (inferInstance : IsMulCommutative (G ⧸ M))

/-- Every homomorphism from a finite `p`-group to `𝔽_p` kills the Frattini subgroup: the image is
abelian of exponent `p`, so both `G^p` and `[G,G]` lie in the kernel, and `Φ(G) = G^p[G,G]`. -/
private theorem frattini_le_ker_of_homFp {p : ℕ} [Fact p.Prime] {G : Type*} [Group G] [Finite G]
    (hG : IsPGroup p G) (f : HomFp p G) : frattini G ≤ f.ker := by
  rw [Commons.GroupTheory.PGroup.frattini_eq_pow_sup_commutator hG]
  refine sup_le ?_ ?_
  · refine (Subgroup.closure_le (f.ker)).mpr ?_
    rintro y ⟨x, rfl⟩
    show f (x ^ p) = 1
    rw [map_pow]
    exact multiplicate_zmod_pow_prime (f x)
  · haveI : IsMulCommutative f.range :=
      IsMulCommutative.of_comm fun a b =>
        Subtype.ext (mul_comm (a : Multiplicative (ZMod p)) (b : Multiplicative (ZMod p)))
    haveI : IsMulCommutative (G ⧸ f.ker) := by
      refine IsMulCommutative.of_comm fun a b => ?_
      refine (QuotientGroup.quotientKerEquivRange f).injective ?_
      rw [map_mul, map_mul]
      exact mul_comm' _ _
    exact (Subgroup.Normal.quotient_commutative_iff_commutator_le (N := f.ker)).mp
      (inferInstance : IsMulCommutative (G ⧸ f.ker))

/-- Precomposition with the quotient map `G ⧸ Φ(G) ↠ G` is a bijection of homomorphism groups,
because `Φ(G)` is killed by every homomorphism to `𝔽_p`. -/
private theorem bijective_comp_mk'_frattini {p : ℕ} [Fact p.Prime] {G : Type*} [Group G]
    [Finite G] (hG : IsPGroup p G) :
    Function.Bijective fun φ : HomFp p (G ⧸ frattini G) =>
      φ.comp (QuotientGroup.mk' (frattini G)) := by
  constructor
  · intro φ ψ h
    refine MonoidHom.ext fun y => ?_
    obtain ⟨g, hg⟩ := QuotientGroup.mk'_surjective (frattini G) y
    rw [← hg]
    exact DFunLike.congr_fun h g
  · intro f
    exact ⟨QuotientGroup.lift (frattini G) f (frattini_le_ker_of_homFp hG f),
      QuotientGroup.lift_comp_mk' (frattini G) f (frattini_le_ker_of_homFp hG f)⟩

/-! ## The main theorem -/

theorem dGens_eq_pHomDim_of_isPGroup {p : ℕ} [Fact p.Prime] {G : Type*} [Group G] [Finite G]
    (hG : IsPGroup p G) : pHomDim p G = dGens G := by
  classical
  -- Burnside's basis theorem: a minimal generating set, and `|G ⧸ Φ(G)| = p ^ dGens G`.
  obtain ⟨S, hScard, hSgen, hSmin⟩ :=
    Commons.GroupTheory.PGroup.burnside_basis (p := p) hG
  have hdGens : dGens G = S.card := IsMinimalGeneratingSet.dGens_eq ⟨hSgen, hSmin⟩
  -- `G ⧸ Φ(G)` is elementary abelian, hence an `𝔽_p`-vector space.
  haveI hcomm : IsMulCommutative (G ⧸ frattini G) :=
    (Subgroup.Normal.quotient_commutative_iff_commutator_le (N := frattini G)).mpr
      (commutator_le_frattini_of_isPGroup hG)
  let A := Additive (G ⧸ frattini G)
  have hsmul : ∀ x : A, p • x = 0 := by
    intro x
    induction x using Additive.rec with
    | ofMul g =>
      rw [← ofMul_pow,
        Commons.GroupTheory.PGroup.quotient_frattini_exponent_p hG g, ofMul_one]
  letI : Module (ZMod p) A := AddCommGroup.zmodModule (n := p) hsmul
  -- `|Hom(G, 𝔽_p)| = |Hom(G ⧸ Φ(G), 𝔽_p)| = |A →+ 𝔽_p| = p ^ dGens G`.
  have h1 : Nat.card (HomFp p G) = Nat.card (HomFp p (G ⧸ frattini G)) :=
    (Nat.card_congr (Equiv.ofBijective _ (bijective_comp_mk'_frattini hG))).symm
  have h2 : Nat.card (HomFp p (G ⧸ frattini G)) = Nat.card (A →+ ZMod p) :=
    Nat.card_congr (MonoidHom.toAdditiveLeft (α := G ⧸ frattini G) (β := ZMod p))
  have hfin : Module.finrank (ZMod p) A = S.card := by
    have hA : Nat.card A = p ^ Module.finrank (ZMod p) A := by
      haveI : Module.Finite (ZMod p) A := Module.Finite.of_finite
      rw [Module.natCard_eq_pow_finrank (K := ZMod p) (V := A), Nat.card_eq_fintype_card, ZMod.card]
    have hA' : Nat.card A = p ^ S.card := by
      rw [← hScard]
      exact Nat.card_congr Additive.ofMul
    exact Nat.pow_right_injective (Fact.out : p.Prime).two_le (hA.symm.trans hA')
  have hcard : Nat.card (HomFp p G) = p ^ dGens G := by
    calc Nat.card (HomFp p G) = Nat.card (HomFp p (G ⧸ frattini G)) := h1
      _ = Nat.card (A →+ ZMod p) := h2
      _ = p ^ Module.finrank (ZMod p) A := natCard_addMonoidHom_zmod (p := p) A
      _ = p ^ S.card := by rw [hfin]
      _ = p ^ dGens G := by rw [hdGens]
  rw [pHomDim, hcard]
  exact Nat.log_pow (Fact.out : p.Prime).one_lt (dGens G)

end Work.ProPDeficiency
