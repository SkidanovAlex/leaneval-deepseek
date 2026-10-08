import Mathlib
import Submission.Work.HallHigman.Basic
import Submission.Work.HallHigman.HallHigmanB
import Submission.Work.HallHigman.ModRep
import Submission.Work.HallHigman.Unipotent
import Submission.Work.HallHigman.FT71
import Submission.Work.HallHigman.orderOf_eq_prime_pow_of_sq_sub_one_eq_zero
import Submission.Work.HallHigman.minpoly_eq_X_sub_one_pow_iff
import Submission.Work.HallHigman.minpoly_dvd_X_sub_one_pow
import Submission.Work.HallHigman.exists_ne_zero_fixed_of_isPGroup
import Submission.Work.HallHigman.map_invariants_le_of_normal

import Submission.Work.HallHigman.minpoly_eq_X_sub_one_sq_of_sq_eq_zero
import Submission.Work.HallHigman.minpoly_subrepresentation_eq_sq
import Submission.Work.HallHigman.minpoly_quotient_eq_sq
import Submission.Work.HallHigman.isPGroup_of_forall_pow_trivial_univ

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

namespace Work.HallHigman

universe v

open Polynomial

section Helpers

variable {p : ℕ} [Fact p.Prime]

/-- The fixed space of `O_p(H)` is nonzero (mixed-universe form of
`Work.HallHigman.fixedBy_pCore_ne_bot`). -/
theorem fixedBy_pCore_ne_bot_univ {H : Type*} [Group H] [Finite H]
    {V : Type*} [AddCommGroup V] [Module (ZMod p) V] [Finite V]
    (ρ : Representation (ZMod p) H V) (hV : Nontrivial V) : fixedBy ρ (pCore p H) ≠ ⊥ := by
  intro hbot
  obtain ⟨u, hu, hfix⟩ := exists_ne_zero_fixed_of_isPGroup ρ isPGroup_pCore hV
  have hmem : u ∈ fixedBy ρ (pCore p H) := (mem_fixedBy_iff ρ (pCore p H) u).mpr hfix
  rw [hbot] at hmem
  exact hu (by simpa using hmem)

/-- The fixed space of `O_p(H)` is proper (mixed-universe form of
`Work.HallHigman.fixedBy_pCore_ne_top`). -/
theorem fixedBy_pCore_ne_top_univ {H : Type*} [Group H] [Finite H]
    {V : Type*} [AddCommGroup V] [Module (ZMod p) V]
    (ρ : Representation (ZMod p) H V) (hfaith : Function.Injective ρ) (hP : pCore p H ≠ ⊥) :
    fixedBy ρ (pCore p H) ≠ ⊤ := by
  intro htop
  have hle : pCore p H ≤ repKernel ρ := by
    intro g hg
    rw [mem_repKernel_iff]
    intro v
    have : v ∈ fixedBy ρ (pCore p H) := by rw [htop]; trivial
    exact (mem_fixedBy_iff ρ (pCore p H) v).mp this g hg
  have hbot : pCore p H ≤ ⊥ := by
    rw [← (repKernel_eq_bot_iff ρ).mpr hfaith]
    exact hle
  exact hP (le_bot_iff.mp hbot)

/-- The action of the quotient representation on the class of a vector. -/
lemma Representation.quotient_mk_apply {G V : Type*} {k : Type*} [Ring k] [Monoid G]
    [AddCommGroup V] [Module k V] (ρ : Representation k G V) (W : Submodule k V)
    (hW : ∀ g, W ≤ W.comap (ρ g)) (g : G) (v : V) :
    (Representation.quotient ρ W hW) g (Submodule.Quotient.mk v) =
      Submodule.Quotient.mk (ρ g v) := by
  rw [Representation.quotient_apply, Submodule.mapQ_apply]

/-- `p`-solvability (Feit--Thompson's notion, `Work.HallHigman.IsPSolvable`) passes to quotients
when `p` is a prime: push a normal series forward along the quotient map; the index of an image
factor divides the index of the corresponding factor, so a factor which is a `p`-group or a
`p'`-group stays one. -/
theorem isPSolvable_quotient_of_prime {p : ℕ} (hp : p.Prime) {G : Type*} [Group G]
    (N : Subgroup G) [N.Normal] (h : IsPSolvable p G) : IsPSolvable p (G ⧸ N) := by
  obtain ⟨n, f, hf0, hftop, hnorm, hidx⟩ := h
  refine ⟨n, fun i => (f i).map (QuotientGroup.mk' N), ?_, ?_, ?_, ?_⟩
  · show Subgroup.map (QuotientGroup.mk' N) (f ⟨0, Nat.succ_pos n⟩) = ⊥
    rw [hf0, Subgroup.map_bot]
  · show Subgroup.map (QuotientGroup.mk' N) (f (Fin.last n)) = ⊤
    rw [hftop, Subgroup.map_top_of_surjective _ (QuotientGroup.mk'_surjective N)]
  · intro i
    exact (hnorm i).map _ (QuotientGroup.mk'_surjective N)
  · intro i
    set A : Subgroup G := f i.castSucc with hA
    set B : Subgroup G := f i.succ with hB
    set φ : G →* G ⧸ N := QuotientGroup.mk' N with hφ
    have hAn : A.Normal := hnorm i.castSucc
    have hBn : B.Normal := hnorm i.succ
    have hAmapn : (A.map φ).Normal := hAn.map φ (QuotientGroup.mk'_surjective N)
    haveI : (A.subgroupOf B).Normal := hAn.comap B.subtype
    haveI : ((A.map φ).subgroupOf (B.map φ)).Normal := hAmapn.comap (B.map φ).subtype
    have hdiv : ((A.map φ).subgroupOf (B.map φ)).index ∣ (A.subgroupOf B).index := by
      have hψsurj : Function.Surjective ((φ).subgroupMap B) := φ.subgroupMap_surjective B
      have hmem : ∀ x ∈ A.subgroupOf B,
          ((φ).subgroupMap B) x ∈ (A.map φ).subgroupOf (B.map φ) := by
        intro x hx
        rw [Subgroup.mem_subgroupOf]
        simpa using Subgroup.mem_map_of_mem φ ((Subgroup.mem_subgroupOf).mp hx)
      have hker : A.subgroupOf B ≤ ((QuotientGroup.mk' ((A.map φ).subgroupOf (B.map φ))).comp
          (φ.subgroupMap B)).ker := by
        intro x hx
        rw [MonoidHom.mem_ker, MonoidHom.comp_apply]
        exact (QuotientGroup.eq_one_iff _).mpr (hmem x hx)
      have hsurjφ : Function.Surjective
          ((QuotientGroup.mk' ((A.map φ).subgroupOf (B.map φ))).comp (φ.subgroupMap B)) :=
        (QuotientGroup.mk'_surjective _).comp hψsurj
      have hsurj : Function.Surjective (QuotientGroup.lift (A.subgroupOf B)
          ((QuotientGroup.mk' ((A.map φ).subgroupOf (B.map φ))).comp (φ.subgroupMap B)) hker) :=
        QuotientGroup.lift_surjective_of_surjective (A.subgroupOf B) _ hsurjφ hker
      have hcard := Subgroup.card_dvd_of_surjective hsurj
      simpa only [Subgroup.index_eq_card] using hcard
    rcases hidx i with hnd | ⟨k, hk⟩
    · left
      intro hpdvd
      exact hnd (hpdvd.trans hdiv)
    · right
      obtain ⟨j, -, hj⟩ := (Nat.dvd_prime_pow hp).mp (hk ▸ hdiv)
      exact ⟨j, hj⟩

/-- The representation of `G ⧸ ker φ` induced by `φ` is faithful. -/
lemma injective_quotientGroup_lift_ker {G M : Type*} [Group G] [Monoid M]
    (φ : G →* M) : Function.Injective (QuotientGroup.lift φ.ker φ le_rfl) := by
  rw [← MonoidHom.ker_eq_bot_iff, QuotientGroup.ker_lift]
  rw [Subgroup.map_eq_bot_iff]
  intro x hx
  rw [MonoidHom.mem_ker]
  exact (QuotientGroup.eq_one_iff x).mpr hx

end Helpers

open Polynomial in
/-- **Feit--Thompson's Lemma 7.1, deduced from Hall--Higman Theorem B** (`Work.HallHigman.FTLemma71`):
if `H` is a `p`-solvable linear group of odd order over `ZMod p` with `p ≠ 2`, then the `p`-core
`O_p(H)` contains every element whose minimal polynomial is `(X - 1) ^ 2`.

Plan of the paper's proof (all ingredients below are already in this area, see
`Submission/Work/HallHigman/NOTES.md` §4 (T2)):

* Let `x ∈ H` have minimal polynomial `(X - 1) ^ 2` on `V`; proceed by strong induction on
  `finrank (ZMod p) V` (the proposition is universally quantified over the group).
* `(V.ρ x - 1) ^ 2 = 0` (`minpoly.aeval`) and `x ≠ 1`; from the latter and
  `Work.HallHigman.orderOf_eq_prime_pow_of_sq_sub_one_eq_zero` we get `orderOf x = p ^ n`, `n > 0`.
* `Work.HallHigman.pCore_ne_bot_of_minpoly_sq` (a consequence of `hB`, using `p ≠ 2`) gives
  `O_p(H) ≠ 1`.
* `Z := Work.HallHigman.fixedBy V.ρ (pCore p H)` is nonzero
  (`Work.HallHigman.fixedBy_pCore_ne_bot`) and proper
  (`Work.HallHigman.fixedBy_pCore_ne_top`), and `H`-invariant.
* Let `H₀ := {h | ∀ v ∈ Z, V.ρ h v = v}` and `H₁ := {h | ∀ v, V.ρ h v - v ∈ Z}`; both are normal,
  the actions on `Z` resp. `V ⧸ Z` factor through *faithful* representations of `H ⧸ H₀` resp.
  `H ⧸ H₁` of smaller dimension, to which the induction hypothesis applies: thus
  `x H₀ ∈ O_p(H ⧸ H₀)` and `x H₁ ∈ O_p(H ⧸ H₁)`.
* So `x ∈ P₀ ⊓ P₁`, where `Pᵢ` is the preimage of `O_p(H ⧸ Hᵢ)`. Every element `y ∈ P₀` has some
  `p`-power acting trivially on `Z`, and every element of `P₁` has some `p`-power acting trivially
  on `V ⧸ Z`; hence `Work.HallHigman.isPGroup_of_forall_pow_trivial` shows that `P₀ ⊓ P₁` is a
  `p`-group, and being normal it lies in `O_p(H)` (`Work.HallHigman.le_pCore_of_isPGroup`), giving
  `x ∈ O_p(H)`. -/
theorem FTLemma71_zmod_of_HallHigmanB {p : ℕ} [Fact p.Prime]
    (hB : Work.HallHigman.HallHigmanB.{0, v} (ZMod p) p) (hp : p ≠ 2) :
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
    pCore_ne_bot_of_minpoly_sq (x := x) (n := n) hB hp hsol hodd V hfaith hnpos hn hmin
  haveI hnt : Nontrivial ↥V.V := by
    by_contra hcon
    rw [not_nontrivial_iff_subsingleton] at hcon
    haveI := hcon
    exact hne (Subsingleton.elim _ _)
  haveI hfinV : Finite ↥V.V := Module.finite_of_finite (ZMod p)
  -- the fixed space of `O_p(H)`
  let Z : Submodule (ZMod p) ↥V.V := fixedBy V.ρ (pCore p H)
  have hZne : Z ≠ ⊥ := fixedBy_pCore_ne_bot_univ V.ρ hnt
  have hZtop : Z ≠ ⊤ := fixedBy_pCore_ne_top_univ V.ρ hfaith hPne
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
  have hZbar_inj : Function.Injective Zbar := injective_quotientGroup_lift_ker Zρ
  have hQbar_inj : Function.Injective Qbar := injective_quotientGroup_lift_ker Qρ
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

end Work.HallHigman
