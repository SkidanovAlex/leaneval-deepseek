import Mathlib
import Submission.Work.HallHigman.FT71
import Submission.Work.HallHigman.HallHigmanB
import Submission.Work.HallHigman.FT71Field
import Submission.Work.HallHigman.FTLemma71_zmod_of_HallHigmanB

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

namespace Work.HallHigman

universe u v w

open Polynomial in
/-- **Feit--Thompson's Lemma 7.1 in the general form of the paper** (Chapter II, p. 791), deduced
from Hall--Higman Theorem B: for *any* field `K` of characteristic `p ≠ 2`, a `p`-solvable linear
group `H` of odd order has `O_p(H)` containing every element whose minimal polynomial is
`(X - 1) ^ 2`.

The proof is the same induction as in the `ZMod p` case
(`Work.HallHigman.FTLemma71_zmod_of_HallHigmanB`); the auxiliary lemmas of `Work.HallHigman.ModRep`,
`Work.HallHigman.FT71` and `Work.HallHigman.HallHigmanB` that are stated for `ZMod p` have to be
restated and reproved for a general field `K` with `[CharP K p]`.  Note in particular that the
fixed point lemma `exists_ne_zero_fixed_of_isPGroup` is proved by orbit counting over the finite
field `ZMod p` and does *not* generalise directly: over a general field of characteristic `p` one
uses instead that a `p`-group `P` acting on a nonzero `K`-module has a nonzero fixed vector
(take a central element `z` of order `p`; `(z - 1) ^ p = 0` gives a nonzero fixed vector of `z`,
then descend through the centre by induction on `|P|`). -/
theorem FTLemma71_of_HallHigmanB {K : Type u} [Field K] {p : ℕ} [CharP K p] [Fact p.Prime]
    (hB : Work.HallHigman.HallHigmanB.{u, v} K p) (hp : p ≠ 2) :
    Work.HallHigman.FTLemma71.{u, v} K p := by
  suffices key : ∀ N : ℕ, ∀ (H : Type v) [Group H] [Finite H], IsPSolvable p H →
      Odd (Nat.card H) → ∀ (V : FDRep K H), Function.Injective V.ρ →
      Module.finrank K V = N → ∀ x : H,
      minpoly K (V.ρ x) = (Polynomial.X - 1) ^ 2 → x ∈ pCore p H by
    intro H _ _ hsol hodd V hfaith x hmin
    exact key _ H hsol hodd V hfaith rfl x hmin
  intro N
  refine Nat.strong_induction_on N (fun N ih => ?_)
  intro H _ _ hsol hodd V hfaith hdim x hmin
  -- `x` acts unipotently of index two
  have hsq : (V.ρ x - 1) ^ 2 = 0 := by
    have h := minpoly.aeval K (V.ρ x)
    rw [hmin] at h
    simpa using h
  -- the same statement with `1 : K[X]` written as `C 1` (the form used by the degree lemmas)
  have hminC : minpoly K (V.ρ x) = (Polynomial.X - Polynomial.C (1 : K)) ^ 2 := by
    simpa only [Polynomial.C_1] using hmin
  -- and not trivially
  have hne : V.ρ x ≠ 1 := by
    intro hone
    have hdvd : minpoly K (V.ρ x) ∣ (Polynomial.X - Polynomial.C (1 : K)) := by
      refine minpoly.dvd K (V.ρ x) ?_
      rw [hone]
      simp
    rw [hminC] at hdvd
    have hdeg := Polynomial.natDegree_le_of_dvd hdvd (Polynomial.X_sub_C_ne_zero (1 : K))
    rw [natDegree_X_sub_C_one_pow (K := K) 2, Polynomial.natDegree_X_sub_C] at hdeg
    omega
  have hx1 : x ≠ 1 := fun h => hne (by rw [h, map_one])
  obtain ⟨n, hn⟩ := orderOf_eq_prime_pow_of_sq_sub_one_eq_zero_univ V.ρ hfaith hsq
  have hnpos : 0 < n := by
    rcases Nat.eq_zero_or_pos n with h | h
    · exfalso
      subst h
      rw [pow_zero] at hn
      exact hx1 (orderOf_eq_one_iff.mp hn)
    · exact h
  have hPne : pCore p H ≠ ⊥ := by
    intro hbot
    exact minpoly_ne_X_sub_one_sq_psolvable (hB := hB) (hp := hp) (hsol := hsol) (hodd := hodd)
      (V := V) (hfaith := hfaith) (hOp := hbot) (x := x) (n := n) (hn := hnpos) (hx := hn) hmin
  haveI hnt : Nontrivial ↥V := by
    by_contra hcon
    rw [not_nontrivial_iff_subsingleton] at hcon
    haveI := hcon
    exact hne (Subsingleton.elim _ _)
  -- the fixed space of `O_p(H)`
  let Z : Submodule K ↥V := fixedByField V.ρ (pCore p H)
  have hZne : Z ≠ ⊥ := fixedByField_pCore_ne_bot V.ρ hnt
  have hZtop : Z ≠ ⊤ := fixedByField_pCore_ne_top V.ρ hfaith hPne
  have hstable : ∀ g : H, Z ≤ Z.comap (V.ρ g) := fun g =>
    Submodule.map_le_iff_le_comap.mp (map_invariants_le_of_normal V.ρ (pCore p H) g)
  let Zρ : Representation K H ↥Z := Representation.subrepresentation V.ρ Z hstable
  let Qρ : Representation K H (↥V ⧸ Z) := Representation.quotient V.ρ Z hstable
  let H₀ : Subgroup H := Zρ.ker
  haveI hH₀N : H₀.Normal := MonoidHom.normal_ker Zρ
  let H₁ : Subgroup H := Qρ.ker
  haveI hH₁N : H₁.Normal := MonoidHom.normal_ker Qρ
  let Zbar : Representation K (H ⧸ H₀) ↥Z := QuotientGroup.lift H₀ Zρ le_rfl
  let Qbar : Representation K (H ⧸ H₁) (↥V ⧸ Z) := QuotientGroup.lift H₁ Qρ le_rfl
  have hZbar_inj : Function.Injective Zbar := injective_quotientGroup_lift_ker Zρ
  have hQbar_inj : Function.Injective Qbar := injective_quotientGroup_lift_ker Qρ
  -- dimension drops
  have hZlt : Module.finrank K ↥Z < N := by
    have hlt := Submodule.finrank_lt (K := K) hZtop
    have hdim' : Module.finrank K ↥V = N := hdim
    omega
  have hQlt : Module.finrank K (↥V ⧸ Z) < N := by
    have h1 : Module.finrank K (↥V ⧸ Z) + Module.finrank K ↥Z = Module.finrank K ↥V :=
      Submodule.finrank_quotient_add_finrank Z
    have h2 : 0 < Module.finrank K ↥Z := by
      haveI : Nontrivial ↥Z := Submodule.nontrivial_iff_ne_bot.mpr hZne
      exact Module.finrank_pos
    have hdim' : Module.finrank K ↥V = N := hdim
    omega
  -- the two quotient groups
  have hsol0 : IsPSolvable p (H ⧸ H₀) := isPSolvable_quotient_of_prime Fact.out H₀ hsol
  have hodd0 : Odd (Nat.card (H ⧸ H₀)) :=
    Odd.of_dvd_nat hodd (Subgroup.card_quotient_dvd_card H₀)
  have hsol1 : IsPSolvable p (H ⧸ H₁) := isPSolvable_quotient_of_prime Fact.out H₁ hsol
  have hodd1 : Odd (Nat.card (H ⧸ H₁)) :=
    Odd.of_dvd_nat hodd (Subgroup.card_quotient_dvd_card H₁)
  -- induction hypothesis on the fixed space
  have hmem0 : QuotientGroup.mk' H₀ x ∈ pCore p (H ⧸ H₀) := by
    by_cases hx0 : x ∈ H₀
    · have hmk0 : QuotientGroup.mk' H₀ x = 1 := (QuotientGroup.eq_one_iff x).mpr hx0
      rw [hmk0]
      exact Subgroup.one_mem _
    · have hneZ : Zρ x ≠ 1 := fun h1 => hx0 (MonoidHom.mem_ker.mpr h1)
      have hminZ : minpoly K ((FDRep.of Zbar).ρ (QuotientGroup.mk' H₀ x)) =
          (Polynomial.X - 1) ^ 2 := by
        rw [FDRep.of_ρ']
        have hx0' : Zbar (QuotientGroup.mk' H₀ x) = Zρ x :=
          QuotientGroup.lift_mk' (φ := Zρ) H₀ le_rfl x
        rw [hx0']
        exact minpoly_subrepresentation_eq_sq_field_univ V.ρ Z hstable x hsq hneZ
      refine ih (Module.finrank K ↥Z) hZlt (H ⧸ H₀) hsol0 hodd0 (FDRep.of Zbar) ?_ rfl
        (QuotientGroup.mk' H₀ x) hminZ
      rw [FDRep.of_ρ']
      exact hZbar_inj
  -- induction hypothesis on the quotient
  have hmem1 : QuotientGroup.mk' H₁ x ∈ pCore p (H ⧸ H₁) := by
    by_cases hx1' : x ∈ H₁
    · have hmk1 : QuotientGroup.mk' H₁ x = 1 := (QuotientGroup.eq_one_iff x).mpr hx1'
      rw [hmk1]
      exact Subgroup.one_mem _
    · have hneQ : Qρ x ≠ 1 := fun h1 => hx1' (MonoidHom.mem_ker.mpr h1)
      have hminQ : minpoly K ((FDRep.of Qbar).ρ (QuotientGroup.mk' H₁ x)) =
          (Polynomial.X - 1) ^ 2 := by
        rw [FDRep.of_ρ']
        have hx1'' : Qbar (QuotientGroup.mk' H₁ x) = Qρ x :=
          QuotientGroup.lift_mk' (φ := Qρ) H₁ le_rfl x
        rw [hx1'']
        exact minpoly_quotient_eq_sq_field_univ V.ρ Z hstable x hsq hneQ
      refine ih (Module.finrank K (↥V ⧸ Z)) hQlt (H ⧸ H₁) hsol1 hodd1
        (FDRep.of Qbar) ?_ rfl (QuotientGroup.mk' H₁ x) hminQ
      rw [FDRep.of_ρ']
      exact hQbar_inj
  -- the intersection of the two preimages is a `p`-group
  let P₀ : Subgroup H := (pCore p (H ⧸ H₀)).comap (QuotientGroup.mk' H₀)
  haveI hP₀N : P₀.Normal :=
    Subgroup.Normal.comap (inferInstance : (pCore p (H ⧸ H₀)).Normal) (QuotientGroup.mk' H₀)
  let P₁ : Subgroup H := (pCore p (H ⧸ H₁)).comap (QuotientGroup.mk' H₁)
  haveI hP₁N : P₁.Normal :=
    Subgroup.Normal.comap (inferInstance : (pCore p (H ⧸ H₁)).Normal) (QuotientGroup.mk' H₁)
  have hxP : x ∈ P₀ ⊓ P₁ := ⟨hmem0, hmem1⟩
  have hPgroup : IsPGroup p ↥(P₀ ⊓ P₁) := by
    refine isPGroup_of_forall_pow_trivial_field_univ (Z := Z) (P := P₀ ⊓ P₁) V.ρ hfaith ?_ ?_ ?_
    · intro y hy v hv
      exact (hstable y) hv
    · intro y hy
      obtain ⟨k, hk⟩ := isPGroup_pCore (p := p) (G := H ⧸ H₀)
        ⟨QuotientGroup.mk' H₀ y, hy.1⟩
      have hk' : (QuotientGroup.mk' H₀ y) ^ p ^ k = 1 := by
        simpa using congrArg Subtype.val hk
      refine ⟨k, fun v hv => ?_⟩
      have hmk : QuotientGroup.mk' H₀ (y ^ p ^ k) = 1 := by rw [map_pow, hk']
      have hy0 : y ^ p ^ k ∈ H₀ := (QuotientGroup.eq_one_iff _).mp hmk
      have hZρ1 : Zρ (y ^ p ^ k) = 1 := MonoidHom.mem_ker.mp hy0
      have h1 : Zρ (y ^ p ^ k) ⟨v, hv⟩ = ⟨v, hv⟩ := by rw [hZρ1]; rfl
      have h2 := congrArg Subtype.val h1
      simpa [Zρ, Representation.subrepresentation_apply, LinearMap.restrict_apply] using h2
    · intro y hy
      obtain ⟨k, hk⟩ := isPGroup_pCore (p := p) (G := H ⧸ H₁)
        ⟨QuotientGroup.mk' H₁ y, hy.2⟩
      have hk' : (QuotientGroup.mk' H₁ y) ^ p ^ k = 1 := by
        simpa using congrArg Subtype.val hk
      refine ⟨k, fun v => ?_⟩
      have hmk : QuotientGroup.mk' H₁ (y ^ p ^ k) = 1 := by rw [map_pow, hk']
      have hy1 : y ^ p ^ k ∈ H₁ := (QuotientGroup.eq_one_iff _).mp hmk
      have hQρ1 : Qρ (y ^ p ^ k) = 1 := MonoidHom.mem_ker.mp hy1
      have hQρ1' : (Representation.quotient V.ρ Z hstable) (y ^ p ^ k) = 1 := hQρ1
      have h1 : (Representation.quotient V.ρ Z hstable) (y ^ p ^ k) (Submodule.Quotient.mk v)
          = Submodule.Quotient.mk v := by
        rw [hQρ1']; rfl
      rw [Work.HallHigman.Representation.quotient_mk_apply] at h1
      exact (Submodule.Quotient.eq (p := Z)).mp h1
  have hle : P₀ ⊓ P₁ ≤ pCore p H :=
    le_pCore_of_isPGroup (inferInstance : (P₀ ⊓ P₁).Normal) hPgroup
  exact hle hxP

/-- The unfolded form of Feit--Thompson's Lemma 7.1 over a general field, in the shape in which the
drive uses it downstream (the general-field analogue of `Work.HallHigman.lemma_7_1`): if `H` is a
`p`-solvable group of odd order with `p ≠ 2` acting faithfully on a finite dimensional `K`-module
`V` in characteristic `p`, then every element whose minimal polynomial on `V` is `(X - 1) ^ 2` lies
in the `p`-core `O_p(H)`. -/
theorem lemma_7_1_field {K : Type u} [Field K] {p : ℕ} [CharP K p] [Fact p.Prime]
    (hB : Work.HallHigman.HallHigmanB.{u, v} K p) (hp : p ≠ 2)
    {H : Type v} [Group H] [Finite H] (hsol : IsPSolvable p H) (hodd : Odd (Nat.card H))
    (V : FDRep K H) (hfaith : Function.Injective V.ρ) (x : H)
    (hx : minpoly K (V.ρ x) = (Polynomial.X - 1) ^ 2) : x ∈ pCore p H :=
  FTLemma71_of_HallHigmanB hB hp H hsol hodd V hfaith x hx

end Work.HallHigman
