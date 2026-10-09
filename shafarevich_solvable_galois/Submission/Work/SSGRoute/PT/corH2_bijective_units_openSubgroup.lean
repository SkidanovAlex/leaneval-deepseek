import Mathlib
import Submission.Work.SSGRoute.PT.alphaTwo_beta
import Submission.Work.SSGRoute.PT.corH2_ptorsion_bij
import Submission.Work.SSGRoute.Nakayama.br_pTorsion
import Submission.Work.SSGRoute.zmultiples_eq_top_of_card_le_prime
import Submission.Work.SSGRoute.PT.cardH2_units_openSubgroup_decomp
import Submission.Work.SSGRoute.PT.exists_resH2_pTorsion_nsmul_ne_zero
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

set_option synthInstance.maxHeartbeats 4000000
set_option maxHeartbeats 8000000

namespace Work.SSGRoute.PT

/-- **Bijectivity on `p`-torsion from one nonzero value.**  Let `V, W` be abelian groups whose
`p`-torsion subgroups (for a prime `p`) have exactly `p` elements each.  If `φ : V →+ W` is nonzero
on the `p`-torsion of `V`, then the induced map `V[p] → W[p]` is bijective. -/
theorem bijective_of_nonzero_on_ptorsion {V W : Type*} [AddCommGroup V] [AddCommGroup W]
    (p : ℕ) [Fact p.Prime] (φ : V →+ W)
    (hcardV : Nat.card {y : V // p • y = 0} = p) (hcardW : Nat.card {y : W // p • y = 0} = p)
    (hnz : ∃ x : V, p • x = 0 ∧ φ x ≠ 0) :
    Function.Bijective (fun x : {y : V // p • y = 0} =>
      (⟨φ x.1, by rw [← map_nsmul, x.2, map_zero]⟩ : {y : W // p • y = 0})) := by
  classical
  have hkerV : ∀ y : V, y ∈ AddMonoidHom.ker (p • AddMonoidHom.id V) ↔ p • y = 0 := by
    intro y; simp [AddMonoidHom.mem_ker]
  have hkerW : ∀ y : W, y ∈ AddMonoidHom.ker (p • AddMonoidHom.id W) ↔ p • y = 0 := by
    intro y; simp [AddMonoidHom.mem_ker]
  have hcardV' : Nat.card ↥(AddMonoidHom.ker (p • AddMonoidHom.id V)) = p :=
    (Nat.card_congr (Equiv.subtypeEquivRight hkerV)).symm.trans hcardV
  have hcardW' : Nat.card ↥(AddMonoidHom.ker (p • AddMonoidHom.id W)) = p :=
    (Nat.card_congr (Equiv.subtypeEquivRight hkerW)).symm.trans hcardW
  have hp0 : p ≠ 0 := (Fact.out : p.Prime).ne_zero
  haveI : Finite ↥(AddMonoidHom.ker (p • AddMonoidHom.id V)) :=
    Nat.finite_of_card_ne_zero (by rw [hcardV']; exact hp0)
  haveI : Finite ↥(AddMonoidHom.ker (p • AddMonoidHom.id W)) :=
    Nat.finite_of_card_ne_zero (by rw [hcardW']; exact hp0)
  haveI : Fintype ↥(AddMonoidHom.ker (p • AddMonoidHom.id V)) := Fintype.ofFinite _
  haveI : Fintype ↥(AddMonoidHom.ker (p • AddMonoidHom.id W)) := Fintype.ofFinite _
  let Φ : ↥(AddMonoidHom.ker (p • AddMonoidHom.id V)) →+
      ↥(AddMonoidHom.ker (p • AddMonoidHom.id W)) :=
    { toFun := fun x => ⟨φ x.1, by
        rw [hkerW, ← map_nsmul, (hkerV x.1).mp x.2, map_zero]⟩
      map_zero' := Subtype.ext (map_zero φ)
      map_add' := fun a b => Subtype.ext (map_add φ a.1 b.1) }
  have hΦnz : ∃ x : ↥(AddMonoidHom.ker (p • AddMonoidHom.id V)), Φ x ≠ 0 := by
    obtain ⟨x, hx, hxnz⟩ := hnz
    have hv : (Φ ⟨x, (hkerV x).mpr hx⟩).1 = φ x := rfl
    refine ⟨⟨x, (hkerV x).mpr hx⟩, fun h => hxnz ?_⟩
    have := congrArg Subtype.val h
    rw [hv] at this
    exact this
  have hinj : Function.Injective Φ := by
    obtain ⟨x₀, hx₀⟩ := hΦnz
    have hx₀' : x₀ ≠ 0 := fun h => hx₀ (by rw [h, map_zero])
    have htop : AddSubgroup.zmultiples x₀ = ⊤ :=
      Work.SSGRoute.zmultiples_eq_top_of_card_le_prime p
        (fun z => Subtype.ext (by simpa using (hkerV z.1).mp z.2)) (le_of_eq hcardV') x₀ hx₀'
    intro x y hxy
    have hmem : x - y ∈ AddSubgroup.zmultiples x₀ := by rw [htop]; exact trivial
    obtain ⟨m, hm⟩ := AddSubgroup.mem_zmultiples_iff.mp hmem
    have hzero : Φ (x - y) = 0 := by rw [map_sub, hxy, sub_self]
    rw [← hm] at hzero
    have hm0 : m • Φ x₀ = 0 := by rw [← map_zsmul]; exact hzero
    have hord : addOrderOf (Φ x₀) = p := by
      refine addOrderOf_eq_prime ?_ hx₀
      exact Subtype.ext (by simpa using (hkerW (Φ x₀).1).mp (Φ x₀).2)
    have hdvd : (p : ℤ) ∣ m := by
      have h := (addOrderOf_dvd_iff_zsmul_eq_zero (x := Φ x₀) (i := m)).mpr hm0
      rwa [hord] at h
    obtain ⟨j, hj⟩ := hdvd
    have hpz : (p : ℤ) • x₀ = 0 := by
      refine Subtype.ext ?_
      show (p : ℤ) • (x₀ : V) = 0
      rw [natCast_zsmul]
      exact (hkerV x₀.1).mp x₀.2
    have hxy0 : x - y = 0 := by
      rw [← hm, hj, mul_zsmul, smul_comm, hpz, smul_zero]
    exact sub_eq_zero.mp hxy0
  have hbij : Function.Bijective Φ :=
    (Fintype.bijective_iff_injective_and_card Φ).mpr ⟨hinj, by
      rw [Fintype.card_eq_nat_card, Fintype.card_eq_nat_card, hcardV', hcardW']⟩
  let eV : {y : V // p • y = 0} ≃ ↥(AddMonoidHom.ker (p • AddMonoidHom.id V)) :=
    Equiv.subtypeEquivRight hkerV
  let eW : {y : W // p • y = 0} ≃ ↥(AddMonoidHom.ker (p • AddMonoidHom.id W)) :=
    Equiv.subtypeEquivRight hkerW
  have hfun : (fun x : {y : V // p • y = 0} =>
        (⟨φ x.1, by rw [← map_nsmul, x.2, map_zero]⟩ : {y : W // p • y = 0}))
      = fun x => eW.symm (Φ (eV x)) := by
    funext x
    refine Subtype.ext ?_
    rw [show (eW.symm (Φ (eV x))).1 = (Φ (eV x)).1 from rfl]
    rfl
  rw [hfun]
  exact (Equiv.bijective eW.symm).comp (hbij.comp (Equiv.bijective eV))


/-- **The corestriction on the `p`-torsion of the local Brauer group is an isomorphism at every
level** — the class-formation axiom Milne, *ADT*, (1.1b) in the form used by the dévissage of
Theorem I.1.8.

For the local class formation `(D_A, \bar k_v^×)`, `D_A = decomp k A`, and every open subgroup
`U ≤ D_A`, the corestriction `cor : H²(U, \bar k_v^×) → H²(D_A, \bar k_v^×)` restricted to the
`p`-torsion is bijective.

This is the arithmetic input of the base case of the `α²`-dévissage: it is the `hcor` hypothesis of
`Work.SSGRoute.PT.alphaTwo_coind_bijective_of_cor` (via
`Work.SSGRoute.PT.hcor_of_corH2_ptorsion`).

**Route.**  Both groups are cyclic of order `p` on their `p`-torsion — that is
`Work.SSGRoute.PT.br_pTorsion_openSubgroup` at `U` and `Work.SSGRoute.Nakayama.br_pTorsion` at
`D_A` — so it suffices to show that `cor` restricted to the `p`-torsion is *nonzero*, equivalently
injective.  This is the statement that the invariant maps are compatible under corestriction:
writing `inv_U : H²(U, \bar k_v^×) ≅ ℚ/ℤ` for the local invariant map of the level `U` (the level
corresponding to a finite extension `M/k_v`, `U ≅ G_M`), one has
`inv_{D_A}(cor β) = inv_U(β)`.

Equivalently: `corH2 U hU C` is, under the invariant isomorphisms, the *identity* of `ℚ/ℤ`; note
that this is **not** the formal identity `cor ∘ res = [D_A:U]·id` of `PT.corH2_resH2` (that is the
other composite), and that `res ∘ cor = [D_A:U]·id` is *false* for a general coefficient module
(in degree `0`, `res ∘ cor` is the conjugation norm).  The consistency of
`cor ∘ res = [D_A:U]·id` with `inv_U(res α) = [D_A:U]·inv_{D_A}(α)` forces exactly
`inv_{D_A} ∘ cor = inv_U`.

Ingredients on disk: the fundamental class and the norm/invariant theory at a finite level
(`NK.NUV2.LC.natCard_groupCohomology_two_units_local_eq_finrank`,
`NK/NUV2/LC/invariantMap.lean`: `localInvariant`, `localInvariant_ker`,
`localInvariant_surjective`), Hilbert 90 at open subgroups
(`PT.hilbert90_H1_eq_zero_openSubgroup`) and `PT.corH2_resH2`. -/
theorem corH2_bijective_units_openSubgroup
    (p : ℕ) [Fact p.Prime] (k Ω : Type) [Field k] [NumberField k] [Field Ω] [Algebra k Ω]
    [IsAlgClosure k Ω] (A : ValuationSubring Ω) (hA : SSGRoute.IsFinPlace k A)
    (U : Subgroup ↥(SSGRoute.decomp k A)) (hU : IsOpen (U : Set ↥(SSGRoute.decomp k A)))
    [U.FiniteIndex] [Fintype (↥(SSGRoute.decomp k A) ⧸ U)] :
    Function.Bijective
      (fun x : {y : Work.AbsoluteKummer.H2 ↥U (Additive (Units Ω)) // p • y = 0} =>
        (⟨Work.SSGRoute.PT.corH2 U hU (Additive (Units Ω)) x.1, by
            rw [← map_nsmul, x.2, map_zero]⟩ :
          {y : Work.AbsoluteKummer.H2 ↥(SSGRoute.decomp k A) (Additive (Units Ω)) //
            p • y = 0})) := by
  classical
  have hp2 : 2 ≤ p := (Fact.out : p.Prime).two_le
  have hp0 : p ≠ 0 := (Fact.out : p.Prime).ne_zero
  -- the cardinality at the top level (Milne (1.1b) at `D_A`)
  have hcardW : Nat.card {y : Work.AbsoluteKummer.H2 ↥(SSGRoute.decomp k A)
      (Additive (Units Ω)) // p • y = 0} = p :=
    Work.SSGRoute.Nakayama.br_pTorsion p k Ω A hA
  -- the cardinality at the level `U` (the level-wise class-formation axiom)
  have hcardV : Nat.card {y : Work.AbsoluteKummer.H2 ↥U (Additive (Units Ω)) // p • y = 0} = p :=
    cardH2_units_openSubgroup_decomp p k Ω A hA U hU
  -- a nonzero value of `cor` on the `p`-torsion
  have hnz : ∃ x : Work.AbsoluteKummer.H2 ↥U (Additive (Units Ω)), p • x = 0 ∧
      Work.SSGRoute.PT.corH2 U hU (Additive (Units Ω)) x ≠ 0 := by
    by_cases hp : p ∣ Nat.card (↥(SSGRoute.decomp k A) ⧸ U)
    · -- `p`-power index: the restriction of a high-order class is nonzero `p`-torsion
      obtain ⟨w, hw1, hw2⟩ := exists_resH2_pTorsion_nsmul_ne_zero p k Ω A hA U hU hp
      refine ⟨Work.SSGRoute.PT.resH2 U w, ?_, ?_⟩
      · simpa using hw1
      · rw [Work.SSGRoute.PT.corH2_resH2 U hU (Additive (Units Ω)) w]; exact hw2
    · -- index prime to `p`: the restriction of a nonzero `p`-torsion class works
      haveI : Finite {y : Work.AbsoluteKummer.H2 ↥(SSGRoute.decomp k A) (Additive (Units Ω)) //
          p • y = 0} := Nat.finite_of_card_ne_zero (by rw [hcardW]; exact hp0)
      haveI : Fintype {y : Work.AbsoluteKummer.H2 ↥(SSGRoute.decomp k A) (Additive (Units Ω)) //
          p • y = 0} := Fintype.ofFinite _
      obtain ⟨y, hy⟩ : ∃ y : {y : Work.AbsoluteKummer.H2 ↥(SSGRoute.decomp k A)
          (Additive (Units Ω)) // p • y = 0},
          y ≠ (⟨0, by simp⟩ : {y : Work.AbsoluteKummer.H2 ↥(SSGRoute.decomp k A)
            (Additive (Units Ω)) // p • y = 0}) := by
        refine Fintype.exists_ne_of_one_lt_card ?_ (⟨0, by simp⟩ : {y : Work.AbsoluteKummer.H2
          ↥(SSGRoute.decomp k A) (Additive (Units Ω)) // p • y = 0})
        rw [Fintype.card_eq_nat_card, hcardW]
        exact (Fact.out : p.Prime).one_lt
      have hy0 : y.1 ≠ 0 := fun h => hy (Subtype.ext h)
      have hord : addOrderOf y.1 = p := addOrderOf_eq_prime y.2 hy0
      have hny : Nat.card (↥(SSGRoute.decomp k A) ⧸ U) • y.1 ≠ 0 := by
        intro h
        have hdvd : addOrderOf y.1 ∣ Nat.card (↥(SSGRoute.decomp k A) ⧸ U) :=
          addOrderOf_dvd_iff_nsmul_eq_zero.mpr h
        rw [hord] at hdvd
        exact hp hdvd
      refine ⟨Work.SSGRoute.PT.resH2 U y.1, ?_, ?_⟩
      · rw [← map_nsmul, y.2, map_zero]
      · rw [Work.SSGRoute.PT.corH2_resH2 U hU (Additive (Units Ω)) y.1]; exact hny
  exact bijective_of_nonzero_on_ptorsion (V := Work.AbsoluteKummer.H2 ↥U (Additive (Units Ω)))
    (W := Work.AbsoluteKummer.H2 ↥(SSGRoute.decomp k A) (Additive (Units Ω)))
    p (Work.SSGRoute.PT.corH2 U hU (Additive (Units Ω))) hcardV hcardW hnz


end Work.SSGRoute.PT
