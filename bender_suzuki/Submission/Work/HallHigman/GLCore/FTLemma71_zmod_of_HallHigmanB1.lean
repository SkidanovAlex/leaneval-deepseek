import Mathlib
import Submission.Work.HallHigman.HallHigmanB
import Submission.Work.HallHigman.FT71
import Submission.Work.HallHigman.FTLemma71_zmod_of_HallHigmanB
import Submission.Work.HallHigman.GLCore.pCore_ne_bot_of_minpoly_sq_B1

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

namespace Work.HallHigman.GLCore

universe v

open Polynomial in
/-- **The final bridge of the GL-core programme** (L19 of `NOTES_LEAD_ft_hallhigman.md` §3):
Feit--Thompson's Lemma 7.1 over `ZMod p`, deduced from the *order-`p`* form `HallHigmanB1` of
Hall--Higman Theorem B.

This is the same induction as `Work.HallHigman.FTLemma71_zmod_of_HallHigmanB`
(`Submission/Work/HallHigman/FTLemma71_zmod_of_HallHigmanB.lean`, proved), with the engine
`Work.HallHigman.pCore_ne_bot_of_minpoly_sq` replaced by its `HallHigmanB1`-based version
`Work.HallHigman.GLCore.pCore_ne_bot_of_minpoly_sq_B1`.  Everything else — the dimension induction,
the fixed space of `O_p(H)`, the two quotient kernels and the final
`isPGroup_of_forall_pow_trivial` step — is copied verbatim. -/
theorem FTLemma71_zmod_of_HallHigmanB1 {p : ℕ} [Fact p.Prime]
    (hB : Work.HallHigman.HallHigmanB1.{0, v} (ZMod p) p) (hp : p ≠ 2) :
    Work.HallHigman.FTLemma71.{0, v} (ZMod p) p := by
  suffices key : ∀ N : ℕ, ∀ (H : Type v) [Group H] [Finite H], IsPSolvable p H →
      Odd (Nat.card H) → ∀ (V : FDRep (ZMod p) H), Function.Injective V.ρ →
      Module.finrank (ZMod p) V = N → ∀ x : H,
      minpoly (ZMod p) (V.ρ x) = (Polynomial.X - 1) ^ 2 → x ∈ pCore p H by
    intro H _ _ hsol hodd V hfaith x hmin
    exact key _ H hsol hodd V hfaith rfl x hmin
  intro N
  refine Nat.strong_induction_on N (fun N ih => ?_)
  intro H _ _ hsol hodd V hfaith hdim x hmin
  have hmin' : minpoly (ZMod p) (V.ρ x) = (Polynomial.X - Polynomial.C (1 : ZMod p)) ^ 2 :=
    hmin
  -- `x` acts unipotently of index two
  have hsq : (V.ρ x - 1) ^ 2 = 0 := by
    have h := minpoly.aeval (ZMod p) (V.ρ x)
    rw [hmin'] at h
    simpa using h
  -- and not trivially
  have hne : V.ρ x ≠ 1 := by
    intro hone
    have hd : minpoly (ZMod p) (V.ρ x) ∣ (Polynomial.X - Polynomial.C (1 : ZMod p)) := by
      refine minpoly.dvd (ZMod p) (V.ρ x) ?_
      rw [hone]
      simp
    rw [hmin'] at hd
    have h1 : (Polynomial.X - Polynomial.C (1 : ZMod p)) *
        (Polynomial.X - Polynomial.C (1 : ZMod p)) ∣
          (Polynomial.X - Polynomial.C (1 : ZMod p)) * 1 := by
      simpa [pow_two] using hd
    have h2 : (Polynomial.X - Polynomial.C (1 : ZMod p)) ∣ (1 : (ZMod p)[X]) :=
      (mul_dvd_mul_iff_left (Polynomial.X_sub_C_ne_zero (1 : ZMod p))).mp h1
    exact (Polynomial.irreducible_X_sub_C (1 : ZMod p)).not_isUnit (isUnit_iff_dvd_one.mpr h2)
  have hx1 : x ≠ 1 := fun h => hne (by rw [h, map_one])
  obtain ⟨n, hn⟩ := orderOf_eq_prime_pow_of_sq_sub_one_eq_zero V.ρ hfaith hsq
  have hnpos : 0 < n := by
    rcases Nat.eq_zero_or_pos n with h | h
    · exfalso
      subst h
      rw [pow_zero] at hn
      exact hx1 (orderOf_eq_one_iff.mp hn)
    · exact h
  have hPne : pCore p H ≠ ⊥ :=
    pCore_ne_bot_of_minpoly_sq_B1 (x := x) (n := n) hB hp hsol hodd V hfaith hnpos hn hmin
  haveI hnt : Nontrivial ↥V.V := by
    by_contra hcon
    rw [not_nontrivial_iff_subsingleton] at hcon
    haveI := hcon
    exact hne (Subsingleton.elim _ _)
  haveI hfinV : Finite ↥V.V := Module.finite_of_finite (ZMod p)
  -- the fixed space of `O_p(H)`
  let Z : Submodule (ZMod p) ↥V.V := fixedBy V.ρ (pCore p H)
  have hZne : Z ≠ ⊥ := Work.HallHigman.fixedBy_pCore_ne_bot_univ V.ρ hnt
  have hZtop : Z ≠ ⊤ := Work.HallHigman.fixedBy_pCore_ne_top_univ V.ρ hfaith hPne
  have hstable : ∀ g : H, Z ≤ Z.comap (V.ρ g) := fun g =>
    Submodule.map_le_iff_le_comap.mp (map_invariants_le_of_normal V.ρ (pCore p H) g)
  let Zρ : Representation (ZMod p) H ↥Z := Representation.subrepresentation V.ρ Z hstable
  let Qρ : Representation (ZMod p) H (↥V.V ⧸ Z) := Representation.quotient V.ρ Z hstable
  let H₀ : Subgroup H := Zρ.ker
  haveI hH₀N : H₀.Normal := MonoidHom.normal_ker Zρ
  let H₁ : Subgroup H := Qρ.ker
  haveI hH₁N : H₁.Normal := MonoidHom.normal_ker Qρ
  let Zbar : Representation (ZMod p) (H ⧸ H₀) ↥Z := QuotientGroup.lift H₀ Zρ le_rfl
  let Qbar : Representation (ZMod p) (H ⧸ H₁) (↥V.V ⧸ Z) := QuotientGroup.lift H₁ Qρ le_rfl
  have hZbar_inj : Function.Injective Zbar :=
    Work.HallHigman.injective_quotientGroup_lift_ker Zρ
  have hQbar_inj : Function.Injective Qbar :=
    Work.HallHigman.injective_quotientGroup_lift_ker Qρ
  -- dimension drops
  have hZlt : Module.finrank (ZMod p) ↥Z < N := by
    have hlt := Submodule.finrank_lt (K := ZMod p) hZtop
    have hdim' : Module.finrank (ZMod p) ↥V.V = N := hdim
    omega
  have hQlt : Module.finrank (ZMod p) (↥V.V ⧸ Z) < N := by
    have h1 : Module.finrank (ZMod p) (↥V.V ⧸ Z) + Module.finrank (ZMod p) ↥Z =
        Module.finrank (ZMod p) ↥V.V := Submodule.finrank_quotient_add_finrank Z
    have h2 : 0 < Module.finrank (ZMod p) ↥Z := by
      haveI : Nontrivial ↥Z := Submodule.nontrivial_iff_ne_bot.mpr hZne
      exact Module.finrank_pos
    have hdim' : Module.finrank (ZMod p) ↥V.V = N := hdim
    omega
  -- the two quotient groups
  have hsol0 : IsPSolvable p (H ⧸ H₀) :=
    Work.HallHigman.isPSolvable_quotient_of_prime Fact.out H₀ hsol
  have hodd0 : Odd (Nat.card (H ⧸ H₀)) :=
    Odd.of_dvd_nat hodd (Subgroup.card_quotient_dvd_card H₀)
  have hsol1 : IsPSolvable p (H ⧸ H₁) :=
    Work.HallHigman.isPSolvable_quotient_of_prime Fact.out H₁ hsol
  have hodd1 : Odd (Nat.card (H ⧸ H₁)) :=
    Odd.of_dvd_nat hodd (Subgroup.card_quotient_dvd_card H₁)
  -- induction hypothesis on the fixed space
  have hmem0 : QuotientGroup.mk' H₀ x ∈ pCore p (H ⧸ H₀) := by
    by_cases hx0 : x ∈ H₀
    · have hmk0 : QuotientGroup.mk' H₀ x = 1 := (QuotientGroup.eq_one_iff x).mpr hx0
      rw [hmk0]
      exact Subgroup.one_mem _
    · have hneZ : Zρ x ≠ 1 := fun h1 => hx0 (MonoidHom.mem_ker.mpr h1)
      have hminZ : minpoly (ZMod p) ((FDRep.of Zbar).ρ (QuotientGroup.mk' H₀ x)) =
          (Polynomial.X - 1) ^ 2 := by
        rw [FDRep.of_ρ']
        have hx0' : Zbar (QuotientGroup.mk' H₀ x) = Zρ x :=
          QuotientGroup.lift_mk' (φ := Zρ) H₀ le_rfl x
        rw [hx0']
        exact minpoly_subrepresentation_eq_sq V.ρ Z hstable x hsq hneZ
      refine ih (Module.finrank (ZMod p) ↥Z) hZlt (H ⧸ H₀) hsol0 hodd0 (FDRep.of Zbar) ?_
        rfl (QuotientGroup.mk' H₀ x) hminZ
      rw [FDRep.of_ρ']
      exact hZbar_inj
  -- induction hypothesis on the quotient
  have hmem1 : QuotientGroup.mk' H₁ x ∈ pCore p (H ⧸ H₁) := by
    by_cases hx1' : x ∈ H₁
    · have hmk1 : QuotientGroup.mk' H₁ x = 1 := (QuotientGroup.eq_one_iff x).mpr hx1'
      rw [hmk1]
      exact Subgroup.one_mem _
    · have hneQ : Qρ x ≠ 1 := fun h1 => hx1' (MonoidHom.mem_ker.mpr h1)
      have hminQ : minpoly (ZMod p) ((FDRep.of Qbar).ρ (QuotientGroup.mk' H₁ x)) =
          (Polynomial.X - 1) ^ 2 := by
        rw [FDRep.of_ρ']
        have hx1'' : Qbar (QuotientGroup.mk' H₁ x) = Qρ x :=
          QuotientGroup.lift_mk' (φ := Qρ) H₁ le_rfl x
        rw [hx1'']
        exact minpoly_quotient_eq_sq V.ρ Z hstable x hsq hneQ
      refine ih (Module.finrank (ZMod p) (↥V.V ⧸ Z)) hQlt (H ⧸ H₁) hsol1 hodd1
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
    refine isPGroup_of_forall_pow_trivial_univ (Z := Z) (P := P₀ ⊓ P₁) V.ρ hfaith ?_ ?_ ?_
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
  have hle : P₀ ⊓ P₁ ≤ pCore p H := le_pCore_of_isPGroup (inferInstance : (P₀ ⊓ P₁).Normal) hPgroup
  exact hle hxP

end Work.HallHigman.GLCore
