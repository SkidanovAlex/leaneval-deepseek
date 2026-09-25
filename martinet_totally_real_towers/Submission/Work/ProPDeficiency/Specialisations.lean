import Mathlib
import Submission.Work.ProPDeficiency.Basic
import Submission.Work.ProPDeficiency.HomRank
import Submission.Work.ProPDeficiency.Deficiency
import Submission.Work.ProPDeficiency.GolodShafarevich
import Submission.Work.ProPDeficiency.Quotients
import Submission.Work.ProPDeficiency.Arithmetic
import Submission.Work.ProPDeficiency.pHomDim_le_dGens
import Submission.Work.ProPDeficiency.card_homFp_eq_pow_pHomDim
import Submission.Work.ProPDeficiency.dGens_eq_log_card_frattini
import Submission.Work.ProPDeficiency.dGens_freeGroup
import Submission.Work.ProPDeficiency.le_dGens_of_surjective_zmod_pow
import Submission.Work.ProPDeficiency.hasPresentation_of_isPresentation
import Submission.Work.ProPDeficiency.dGens_eq_pHomDim_of_isPGroup
import Submission.Work.ProPDeficiency.dGens_zmod_pow
import Submission.Work.ProPDeficiency.dGens_quotient_frattini
import Submission.Work.ProPDeficiency.nonempty_equiv_frattini_zmod_pow
import Submission.Work.ProPDeficiency.dGens_eq_pHomDim_of_maximal_finiteIndex

/-!
# The `p = 2` specialisations

**Namespace** `Work.ProPDeficiency`; module `Submission.Work.ProPDeficiency.Specialisations`.

The arithmetic side works exclusively with `p = 2`.  This module collects the `p = 2` corollaries
of the general chapter, so that a caller never has to instantiate `p` by hand.

## Main results

* `pHomDim_two_le_dGens` : `dim H¹(G, 𝔽₂) ≤ dGens G`;
* `card_homFp_two_eq_pow` : `#Hom(G, 𝔽₂) = 2 ^ pHomDim 2 G` for finitely generated `G`;
* `dGens_eq_log_card_frattini_two` : for a finite `2`-group, `#(G ⧸ Φ(G)) = 2 ^ dGens G`;
* `dGens_freeGroup_fin` : `dGens (FreeGroup (Fin n)) = n`.
-/

set_option autoImplicit false
set_option linter.unusedVariables false
set_option linter.style.haveILetI false

namespace Work.ProPDeficiency

/-- `dim_{𝔽₂} H¹(G, 𝔽₂) ≤ dGens G` for a finitely generated group. -/
theorem pHomDim_two_le_dGens {G : Type*} [Group G] [Group.FG G] :
    pHomDim 2 G ≤ dGens G :=
  pHomDim_le_dGens (by norm_num)

/-- For finitely generated `G`, `Hom(G, 𝔽₂)` is a finite `𝔽₂`-vector space and
`Nat.card (Hom(G, 𝔽₂)) = 2 ^ pHomDim 2 G`. -/
theorem card_homFp_two_eq_pow {G : Type*} [Group G] [Group.FG G] :
    Nat.card (HomFp 2 G) = 2 ^ pHomDim 2 G :=
  card_homFp_eq_pow_pHomDim Nat.prime_two

/-- For a finite `2`-group, the elementary abelian `2`-group `G ⧸ Φ(G)` has order `2 ^ dGens G`. -/
theorem dGens_eq_log_card_frattini_two {G : Type*} [Group G] [Finite G] (hG : IsPGroup 2 G) :
    Nat.card (G ⧸ frattini G) = 2 ^ dGens G :=
  dGens_eq_log_card_frattini hG

/-- `dGens (FreeGroup (Fin n)) = n`. -/
theorem dGens_freeGroup_fin (n : ℕ) : dGens (FreeGroup (Fin n)) = n := by
  simpa using dGens_freeGroup (Fin n)

/-- **The arithmetic shape of `d ≥ |S|`.**  A surjection of `G` onto the elementary abelian
`2`-group of rank `n` forces `n ≤ dGens G`.  In the tame Golod--Shafarevich route the surjection
comes from the multiquadratic extension of `ℚ` of degree `2 ^ |S|`. -/
theorem le_dGens_of_surjective_zmod_two {n : ℕ} {G : Type*} [Group G] [Group.FG G]
    (f : G →* (Fin n → Multiplicative (ZMod 2))) (hf : Function.Surjective f) :
    n ≤ dGens G :=
  le_dGens_of_surjective_zmod_pow f hf

/-- The same with `dGens G` replaced by the (equal) number of generators of any minimal
presentation of `G`, which is the form the arithmetic side has in hand. -/
theorem le_card_of_hasMinimalPresentation {α : Type} [Fintype α] {rel : Finset (FreeGroup α)}
    {G : Type} [Group G] [Group.FG G] {p n : ℕ} [Fact p.Prime]
    (h : HasMinimalPresentation α rel G)
    (f : G →* (Fin n → Multiplicative (ZMod p))) (hf : Function.Surjective f) :
    n ≤ Fintype.card α := by
  have h1 : n ≤ dGens G := le_dGens_of_surjective_zmod_pow f hf
  rwa [h.dGens_eq] at h1

/-- The `p = 2` case of `le_card_of_hasMinimalPresentation`. -/
theorem le_card_of_hasMinimalPresentation_two {α : Type} [Fintype α]
    {rel : Finset (FreeGroup α)} {G : Type} [Group G] [Group.FG G] {n : ℕ}
    (h : HasMinimalPresentation α rel G)
    (f : G →* (Fin n → Multiplicative (ZMod 2))) (hf : Function.Surjective f) :
    n ≤ Fintype.card α :=
  le_card_of_hasMinimalPresentation h f hf

/-- For a finite `2`-group, `dim_{𝔽₂} H¹(G, 𝔽₂) = dGens G`. -/
theorem dGens_eq_pHomDim_two_of_isTwoGroup {G : Type*} [Group G] [Finite G] (hG : IsPGroup 2 G) :
    pHomDim 2 G = dGens G :=
  dGens_eq_pHomDim_of_isPGroup hG

/-- The elementary abelian `2`-group of rank `n` has exactly `n` generators. -/
theorem dGens_zmod_two_pow (n : ℕ) : dGens (Fin n → Multiplicative (ZMod 2)) = n :=
  dGens_zmod_pow 2 n

/-- `d ≥ |S|` with the elementary abelian group given up to isomorphism: if `G` surjects onto a
group isomorphic to `(ℤ/2) ^ n`, then `n ≤ dGens G`.  This is the form in which a multiquadratic
field extension supplies the input (its Galois group is an abstract elementary abelian `2`-group). -/
theorem le_dGens_of_surjective_of_mulEquiv_zmod_two {n : ℕ} {G A : Type*} [Group G] [Group A]
    [Group.FG G] (e : A ≃* (Fin n → Multiplicative (ZMod 2))) (f : G →* A)
    (hf : Function.Surjective f) : n ≤ dGens G :=
  le_dGens_of_surjective_zmod_two (e.toMonoidHom.comp f)
    (e.surjective.comp hf)

/-- The same, with `dGens G` replaced by the generator count of a minimal presentation. -/
theorem le_card_of_surjective_of_mulEquiv_zmod_two {n : ℕ} {G A : Type*} [Group G] [Group A]
    [Group.FG G] {α : Type} [Fintype α] {rel : Finset (FreeGroup α)}
    (h : HasMinimalPresentation α rel G) (e : A ≃* (Fin n → Multiplicative (ZMod 2)))
    (f : G →* A) (hf : Function.Surjective f) : n ≤ Fintype.card α := by
  have h1 : n ≤ dGens G := le_dGens_of_surjective_of_mulEquiv_zmod_two e f hf
  rwa [h.dGens_eq] at h1

/-- For a finite `2`-group, `Φ(G)` is a non-generator: `dGens (G ⧸ Φ(G)) = dGens G`. -/
theorem dGens_quotient_frattini_two {G : Type*} [Group G] [Finite G] (hG : IsPGroup 2 G) :
    dGens (G ⧸ frattini G) = dGens G :=
  dGens_quotient_frattini hG

/-- The literal `dGens = dim_{𝔽₂}` statement: for a finite `2`-group, `G ⧸ Φ(G)` is isomorphic to
the `dGens G`-dimensional `𝔽₂`-vector space. -/
theorem nonempty_equiv_frattini_zmod_two_pow {G : Type*} [Group G] [Finite G] (hG : IsPGroup 2 G) :
    Nonempty (G ⧸ frattini G ≃* (Fin (dGens G) → Multiplicative (ZMod 2))) :=
  nonempty_equiv_frattini_zmod_pow hG

/-- The finite case of `dim H¹ = dGens`, in the hypothesis style of the arithmetic side: a finite
group all of whose finite quotients are `2`-groups is a `2`-group, so `pHomDim 2 G = dGens G`. -/
theorem dGens_eq_pHomDim_two_of_forall_quotient {G : Type*} [Group G] [Finite G]
    (h : ∀ (N : Subgroup G) [N.Normal], Finite (G ⧸ N) → IsPGroup 2 (G ⧸ N)) :
    pHomDim 2 G = dGens G :=
  dGens_eq_pHomDim_two_of_isTwoGroup (isPGroup_of_forall_quotient_isPGroup h)

/-- The `p = 2` case of the `d = dim H¹` identity for finitely generated discrete groups all of
whose finite quotients are `2`-groups and all of whose maximal subgroups have finite index (the
discrete condition replacing "`G` is a finitely generated pro-`2` group"). -/
theorem dGens_eq_pHomDim_two_of_maximal_finiteIndex {G : Type*} [Group G] [Group.FG G]
    (hquot : ∀ (N : Subgroup G) [N.Normal], Finite (G ⧸ N) → IsPGroup 2 (G ⧸ N))
    (hmax : ∀ M : Subgroup G, IsCoatom M → M.FiniteIndex) : pHomDim 2 G = dGens G :=
  dGens_eq_pHomDim_of_maximal_finiteIndex hquot hmax

end Work.ProPDeficiency
