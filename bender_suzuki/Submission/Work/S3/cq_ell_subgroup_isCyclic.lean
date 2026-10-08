import Mathlib
import Submission.Work.ThmF.ChV3.NearField
import Submission.Work.ThmF.Prove.S3.fpf_isCyclic
import Submission.Work.ThmF.ChV3.step2

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

/-!
# `Work.S3.cq_ell_subgroup_isCyclic`

Every odd `ℓ`-subgroup of `C_Q(P)` is cyclic, in the standing context of Peterfalvi II Ch. V §3.

The near-field input `NearFieldAppXIProp` (App. XI Prop. 1) provides a subgroup `R` with
`N = Ker H Q P t ≤ R ≤ C_G(P)`, `|R| = |N| · f^m`, `|C_Q(P)| + 1 = f^m` (`f = o(st)` prime) and
such that `C_Q(P)` acts *fixed-point-freely* on the quotient `R/N` by conjugation (the elementwise
clause `y x y⁻¹ x⁻¹ ∈ N → y = 1`).

Since `C_G(P)` normalises both `R` and `N`, conjugation gives a genuine action of `C_Q(P)` on the
group `R/N` by automorphisms; the cardinalities `|C_Q(P)| = f^m - 1` and `|R/N| = f^m` are
coprime.  Burnside's theorem on Frobenius complements
(`Work.ThmF.Prove.S3.fpf_isCyclic`) then says every odd `ℓ`-subgroup of `C_Q(P)` is cyclic, which
is the statement below.

The technical points are (i) the conjugation automorphism of a subgroup normalised by an element,
(ii) transporting it to the quotient by the (normal) subgroup `N`, and (iii) assembling the
resulting family of quotient automorphisms into a `MulDistribMulAction` so that `fpf_isCyclic`
applies.
-/

set_option autoImplicit false
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
set_option linter.style.haveILetI false
set_option linter.unusedTactic false

namespace Work.S3

namespace CQEll

variable {G : Type} [Group G]

/-- Conjugation by an element `g` of the normaliser of `R`, as an automorphism of `R`. -/
noncomputable def conjAut (R : Subgroup G) (g : G)
    (hg : g ∈ Subgroup.normalizer (R : Set G)) : ↥R ≃* ↥R where
  toFun x := ⟨g * (x : G) * g⁻¹, (Subgroup.mem_normalizer_iff.mp hg (x : G)).mp x.2⟩
  invFun x := ⟨g⁻¹ * (x : G) * g,
    (Subgroup.mem_normalizer_iff.mp hg (g⁻¹ * (x : G) * g)).mpr (by
      have h : g * (g⁻¹ * (x : G) * g) * g⁻¹ = (x : G) := by group
      rw [h]; exact x.2)⟩
  left_inv x := by apply Subtype.ext; group
  right_inv x := by apply Subtype.ext; group
  map_mul' x y := by apply Subtype.ext; simp only [Subgroup.coe_mul]; group

lemma conjAut_val (R : Subgroup G) (g : G) (hg) (x : ↥R) :
    ((conjAut R g hg) x : G) = g * (x : G) * g⁻¹ := rfl

lemma conjAut_symm_val (R : Subgroup G) (g : G) (hg) (x : ↥R) :
    (((conjAut R g hg).symm) x : G) = g⁻¹ * (x : G) * g := by
  have h := conjAut_val R g hg ((conjAut R g hg).symm x)
  rw [MulEquiv.apply_symm_apply] at h
  rw [h]; group

/-- Conjugation as a monoid homomorphism from the normaliser of `R` to `Aut R`. -/
noncomputable def conjAutHom (R : Subgroup G) :
    ↥(Subgroup.normalizer (R : Set G)) →* MulAut ↥R where
  toFun g := conjAut R (g : G) g.2
  map_one' := by
    apply MulEquiv.ext; intro x; apply Subtype.ext
    rw [conjAut_val, MulAut.one_apply]
    simp only [Subgroup.coe_one, one_mul, inv_one, mul_one]
  map_mul' a b := by
    apply MulEquiv.ext; intro x; apply Subtype.ext
    rw [conjAut_val, MulAut.mul_apply, conjAut_val, conjAut_val]
    simp only [Subgroup.coe_mul]
    group

/-- `N` as a subgroup of `R` is invariant under conjugation by any element normalising both
`N` and `R`. -/
lemma map_subgroupOf_conjAut (R N : Subgroup G) (g : G)
    (hgR : g ∈ Subgroup.normalizer (R : Set G)) (hgN : g ∈ Subgroup.normalizer (N : Set G)) :
    (N.subgroupOf R).map (conjAut R g hgR).toMonoidHom = N.subgroupOf R := by
  ext x
  rw [Subgroup.mem_map_equiv, Subgroup.mem_subgroupOf, Subgroup.mem_subgroupOf, conjAut_symm_val]
  rw [Subgroup.mem_normalizer_iff.mp hgN (g⁻¹ * (x : G) * g)]
  congr 1
  group

/-- The form of `map_subgroupOf_conjAut` in which the automorphism is written as a coercion, which
is the form required by `QuotientGroup.congr`. -/
lemma map_subgroupOf_conjAut' (R N : Subgroup G) (g : G)
    (hgR : g ∈ Subgroup.normalizer (R : Set G)) (hgN : g ∈ Subgroup.normalizer (N : Set G)) :
    Subgroup.map (↑(conjAut R g hgR) : ↥R →* ↥R) (N.subgroupOf R) = N.subgroupOf R :=
  map_subgroupOf_conjAut R N g hgR hgN

end CQEll

open CQEll

theorem cq_ell_subgroup_isCyclic {G : Type} [Group G] [Finite G] {H Q : Subgroup G} {t s r : G}
    {P : Subgroup G} (hNF : Work.ThmF.ChV3.NearFieldAppXIProp)
    (c : Work.ThmF.ChV3.CtxF H Q t s r P) {ℓ : ℕ} (hℓ : ℓ.Prime) (hℓ2 : ℓ ≠ 2)
    {B : Subgroup G} (hB : B ≤ Work.ThmF.ChV3.CQ Q P) (hBpg : IsPGroup ℓ ↥B) :
    IsCyclic ↥B := by
  classical
  -- The near-field shadow of App. XI Prop. 1
  obtain ⟨m, R, N, _hN, hm, hf, hNR, hRc, hRn, hNn, hRcard, hcq, hfpf⟩ :=
    hNF G H Q t s r P c
  -- `C_Q(P) = Q ⊓ C_G(P)`
  have hCle : Work.ThmF.ChV3.CQ Q P ≤ Subgroup.centralizer (P : Set G) := inf_le_right
  -- `N`, viewed inside `R`, is normal there
  haveI hRNnormal : (N.subgroupOf R).Normal :=
    ⟨fun n hn g => by
      have hn' : (n : G) ∈ N := Subgroup.mem_subgroupOf.mp hn
      show ((g : G) * (n : G) * (g : G)⁻¹) ∈ N
      exact (Subgroup.mem_normalizer_iff.mp (hNn (hRc g.2)) (n : G)).mp hn'⟩
  let RN : Subgroup ↥R := N.subgroupOf R
  let E := ↥R ⧸ RN
  -- the conjugation action of `C_Q(P)` on `R`
  let ψ : ↥(Work.ThmF.ChV3.CQ Q P) →* ↥(Subgroup.normalizer (R : Set G)) :=
    { toFun := fun y => ⟨(y : G), hRn (hCle y.2)⟩
      map_one' := Subtype.ext rfl
      map_mul' := fun a b => Subtype.ext rfl }
  let cAhom : ↥(Work.ThmF.ChV3.CQ Q P) →* MulAut ↥R := (conjAutHom R).comp ψ
  have hpres : ∀ y : ↥(Work.ThmF.ChV3.CQ Q P),
      Subgroup.map (↑(cAhom y)) RN = RN := fun y =>
    map_subgroupOf_conjAut' R N (y : G) (hRn (hCle y.2)) (hNn (hCle y.2))
  -- the induced action on `R/N`, as a `MulDistribMulAction`
  let smulFun : ↥(Work.ThmF.ChV3.CQ Q P) → E → E :=
    fun y e => QuotientGroup.congr RN RN (cAhom y) (hpres y) e
  letI : MulDistribMulAction ↥(Work.ThmF.ChV3.CQ Q P) E :=
    { smul := smulFun
      one_smul := fun e => by
        refine QuotientGroup.induction_on e ?_
        intro x
        show (QuotientGroup.congr RN RN (cAhom 1) (hpres 1)) (↑x : E) = ↑x
        rw [QuotientGroup.congr_mk, map_one cAhom, MulAut.one_apply]
      mul_smul := fun y z e => by
        refine QuotientGroup.induction_on e ?_
        intro x
        show (QuotientGroup.congr RN RN (cAhom (y * z)) (hpres (y * z))) (↑x : E)
            = (QuotientGroup.congr RN RN (cAhom y) (hpres y))
                ((QuotientGroup.congr RN RN (cAhom z) (hpres z)) (↑x : E))
        rw [QuotientGroup.congr_mk, QuotientGroup.congr_mk, QuotientGroup.congr_mk]
        rw [map_mul cAhom, MulAut.mul_apply]
      smul_one := fun y => by
        show (QuotientGroup.congr RN RN (cAhom y) (hpres y)) (1 : E) = 1
        rw [show (1 : E) = (↑(1 : ↥R) : E) from (QuotientGroup.mk_one RN).symm]
        rw [QuotientGroup.congr_mk, map_one (cAhom y)]
      smul_mul := fun y e₁ e₂ => by
        refine QuotientGroup.induction_on e₁ ?_
        intro x₁
        refine QuotientGroup.induction_on e₂ ?_
        intro x₂
        show (QuotientGroup.congr RN RN (cAhom y) (hpres y)) ((↑x₁ : E) * (↑x₂ : E))
            = (QuotientGroup.congr RN RN (cAhom y) (hpres y)) (↑x₁ : E)
                * (QuotientGroup.congr RN RN (cAhom y) (hpres y)) (↑x₂ : E)
        rw [show (↑x₁ : E) * (↑x₂ : E) = (↑(x₁ * x₂) : E) from
              (QuotientGroup.mk_mul RN x₁ x₂).symm]
        rw [QuotientGroup.congr_mk, QuotientGroup.congr_mk, QuotientGroup.congr_mk]
        rw [map_mul (cAhom y), QuotientGroup.mk_mul] }
  -- cardinality of `R/N`
  have hcardE : Nat.card E = orderOf (s * t) ^ m := by
    have hRNcard : Nat.card ↥RN = Nat.card ↥N :=
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe hNR).toEquiv
    have hpos : 0 < Nat.card ↥N := Nat.card_pos
    have h : Nat.card E * Nat.card ↥N = orderOf (s * t) ^ m * Nat.card ↥N := by
      calc Nat.card E * Nat.card ↥N
          = Nat.card (↥R ⧸ RN) * Nat.card ↥RN := by rw [hRNcard]
        _ = Nat.card ↥R := (Subgroup.card_eq_card_quotient_mul_card_subgroup RN).symm
        _ = Nat.card ↥N * orderOf (s * t) ^ m := hRcard
        _ = orderOf (s * t) ^ m * Nat.card ↥N := Nat.mul_comm _ _
    exact Nat.mul_right_cancel hpos h
  -- `R/N` is nontrivial
  haveI : Nontrivial E := by
    rw [← Finite.one_lt_card_iff_nontrivial, hcardE]
    have h2 : 2 ≤ orderOf (s * t) ^ m := by
      calc 2 ≤ orderOf (s * t) := hf.two_le
        _ = orderOf (s * t) ^ 1 := (pow_one _).symm
        _ ≤ orderOf (s * t) ^ m := Nat.pow_le_pow_right hf.pos hm
    omega
  -- `|C_Q(P)|` and `|R/N|` are coprime
  have hcop : (Nat.card ↥(Work.ThmF.ChV3.CQ Q P)).Coprime (Nat.card E) := by
    rw [hcardE, ← hcq]
    exact (Nat.coprime_self_add_right (m := Nat.card ↥(Work.ThmF.ChV3.CQ Q P)) (n := 1)).mpr
      (Nat.coprime_one_right _)
  -- the action of `C_Q(P)` on `R/N` is fixed-point-free
  have hfp : ∀ a : ↥(Work.ThmF.ChV3.CQ Q P), a ≠ 1 → ∀ e : E, a • e = e → e = 1 := by
    intro a ha e
    refine QuotientGroup.induction_on e ?_
    intro x he
    change (QuotientGroup.congr RN RN (cAhom a) (hpres a)) (↑x : E) = ↑x at he
    rw [QuotientGroup.congr_mk] at he
    -- `he : ↑(cAhom a x) = ↑x`, i.e. `(a x a⁻¹)⁻¹ x ∈ N`
    have hx1 : ((cAhom a x)⁻¹ * x : ↥R) ∈ RN := QuotientGroup.eq.mp he
    have hcomm' : (a : G) * (x : G)⁻¹ * (a : G)⁻¹ * (x : G) ∈ N := by
      have h : (((cAhom a x : ↥R) : G))⁻¹ * (x : G) ∈ N := by
        have h' := Subgroup.mem_subgroupOf.mp hx1
        simpa only [Subgroup.coe_mul, Subgroup.coe_inv] using h'
      have hcA : ((cAhom a x : ↥R) : G) = (a : G) * (x : G) * (a : G)⁻¹ := rfl
      rw [hcA] at h
      convert h using 1
      group
    have hcomm : (a : G) * (x : G) * (a : G)⁻¹ * (x : G)⁻¹ ∈ N := by
      have h1 : (((a : G) * (x : G)⁻¹ * (a : G)⁻¹ * (x : G))⁻¹) ∈ N := Subgroup.inv_mem _ hcomm'
      have h2 := (Subgroup.mem_normalizer_iff.mp (hNn (hRc x.2))
        ((a : G) * (x : G)⁻¹ * (a : G)⁻¹ * (x : G))⁻¹).mp h1
      convert h2 using 1
      group
    by_contra hxe
    have hxNmem : (x : G) ∈ N := by
      by_contra hxNotN
      exact ha (Subtype.ext (by
        simpa only [Subgroup.coe_one] using hfpf (x : G) x.2 hxNotN (a : G) a.2 hcomm))
    exact hxe ((QuotientGroup.eq_one_iff x).mpr (Subgroup.mem_subgroupOf.mpr hxNmem))
  -- Burnside's theorem on Frobenius complements
  refine (MulEquiv.isCyclic (Subgroup.subgroupOfEquivOfLe hB)).mp ?_
  haveI : Fact ℓ.Prime := ⟨hℓ⟩
  have hBpg' : IsPGroup ℓ ↥(B.subgroupOf (Work.ThmF.ChV3.CQ Q P)) := by
    obtain ⟨n, hn⟩ := (IsPGroup.iff_card).mp hBpg
    exact IsPGroup.of_card
      (by rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hB).toEquiv, hn])
  exact Work.ThmF.Prove.S3.fpf_isCyclic hcop hfp hℓ hℓ2 hBpg'

end Work.S3
