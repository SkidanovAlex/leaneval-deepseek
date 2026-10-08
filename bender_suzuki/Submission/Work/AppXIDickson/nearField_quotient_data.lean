import Mathlib
import Submission.Work.ThmF.ChV3.Chain15
import Submission.Work.S3.cq_ell_subgroup_isCyclic
import Submission.Work.AppXIField.Defs

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

set_option autoImplicit false
set_option linter.unusedVariables false
set_option linter.style.haveILetI false
set_option linter.unnecessarySeqFocus false

namespace Work.AppXIDickson

/-- **The near-field quotient `V = R/N` of App. XI Prop. 1, carrying its `C_Q(P)`-action.**

In the standing context `CtxF H Q t s r P` of Peterfalvi II Ch. V §3, let `N = Ker H Q P t ≤ R`
be the subgroups supplied by the step-(2) shadow (App. XI Prop. 1), with `|R| = |N| · f^m`,
`f = o(s t)`, `C_G(P)` normalising both `R` and `N`, `C_Q(P)` acting fixed-point-freely on the
non-identity elements of `R/N` (`hfpf`), and `[R,R] ≤ N` (`hcomm`).  Then the quotient `R/N` is a
finite abelian group `V` of order `f^m = |C_Q(P)| + 1` carrying a genuine `DistribMulAction` of
`C_Q(P)` by group automorphisms, whose fixed points on `V \ {0}` are trivial.

Route.  `hcomm` makes `N` normal in `R` (`Subgroup.commutator_le`) and `↥R ⧸ N.subgroupOf R`
abelian.  The conjugation action of `C_G(P)` on `↥R` (`Work.S3.CQEll.conjAut` / `conjAutHom`)
pushes to the quotient `↥R ⧸ N.subgroupOf R` via `QuotientGroup.congr` (the invariance of
`N.subgroupOf R` is `Work.S3.CQEll.map_subgroupOf_conjAut'`), giving
`MulDistribMulAction ↥(C_G(P)) (↥R ⧸ N.subgroupOf R)`; restrict along the inclusion
`C_Q(P) ≤ C_G(P)` and transport to `Additive` (helper
`Work.AppXIField.Defs.distribMulActionAdditiveOfHom`, with `QuotV G R N := Additive (↥R ⧸ N.subgroupOf R)`).
`Nat.card V = f ^ m` follows from `hRcard` and `Subgroup.card_eq_card_quotient_mul_card_subgroup`
(as in `Work.S3.cq_ell_subgroup_isCyclic`, whose proof contains the whole construction).  The
fixed-point-freeness is `hfpf` in quotient form: `y • v = v` for `v = xN` with `x ∉ N` says
`y * x * y⁻¹ * x⁻¹ ∈ N` (conjugating the derived `x⁻¹ y x y⁻¹ ∈ N` by `x ∈ R`, using `N ⊴ R`), so
`y = 1` (every element of `R/N` is of the form `xN`). -/
theorem nearField_quotient_data {G : Type} [Group G] [Finite G] {H Q : Subgroup G} {t s r : G}
    {P : Subgroup G} (c : Work.ThmF.ChV3.CtxF H Q t s r P) {R N : Subgroup G} {f m : ℕ}
    (hN : N = Work.ThmF.ChV3.Ker H Q P t) (hNR : N ≤ R)
    (hRn : Subgroup.centralizer (P : Set G) ≤ Subgroup.normalizer (R : Set G))
    (hNn : Subgroup.centralizer (P : Set G) ≤ Subgroup.normalizer (N : Set G))
    (hRcard : Nat.card R = Nat.card N * f ^ m)
    (hcq : Nat.card ↥(Work.ThmF.ChV3.CQ Q P) + 1 = f ^ m)
    (hfpf : ∀ x ∈ R, x ∉ N → ∀ y ∈ Work.ThmF.ChV3.CQ Q P,
      y * x * y⁻¹ * x⁻¹ ∈ N → y = 1)
    (hcomm : ∀ x ∈ R, ∀ y ∈ R, x * y * x⁻¹ * y⁻¹ ∈ N) :
    ∃ (V : Type) (_ : AddCommGroup V) (_ : Finite V)
      (_ : DistribMulAction ↥(Work.ThmF.ChV3.CQ Q P) V),
      Nat.card V = f ^ m ∧
      (∀ y : ↥(Work.ThmF.ChV3.CQ Q P), y ≠ 1 → ∀ v : V, y • v = v → v = 0) := by
  classical
  -- `C_Q(P) ≤ C_G(P)`
  have hCle : Work.ThmF.ChV3.CQ Q P ≤ Subgroup.centralizer (P : Set G) := inf_le_right
  -- `[R,R] ≤ N` makes `N` normal in `R` (via `⁅g,n⁆ = g n g⁻¹ n⁻¹`)
  have hNnormal : (N.subgroupOf R).Normal := by
    refine ⟨fun n hn g => ?_⟩
    rw [Subgroup.mem_subgroupOf] at ⊢
    simp only [Subgroup.coe_mul, Subgroup.coe_inv]
    have hnN : ((n : ↥R) : G) ∈ N := Subgroup.mem_subgroupOf.mp hn
    have hc : (g : G) * ((n : ↥R) : G) * (g : G)⁻¹ * ((n : ↥R) : G)⁻¹ ∈ N :=
      hcomm (g : G) g.2 _ (hNR hnN)
    have : (g : G) * ((n : ↥R) : G) * (g : G)⁻¹
        = ((g : G) * ((n : ↥R) : G) * (g : G)⁻¹ * ((n : ↥R) : G)⁻¹) * ((n : ↥R) : G) := by
      group
    rw [this]
    exact Subgroup.mul_mem _ hc hnN
  letI : (N.subgroupOf R).Normal := hNnormal
  let RN : Subgroup ↥R := N.subgroupOf R
  let A := Work.ThmF.ChV3.CQ Q P
  let E := ↥R ⧸ RN
  -- the quotient `R/N` is abelian, since `[R,R] ≤ N`
  letI : CommGroup E :=
    { (inferInstance : Group E) with
      mul_comm := fun a b => by
        refine QuotientGroup.induction_on a ?_
        intro x
        refine QuotientGroup.induction_on b ?_
        intro y
        rw [← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul, QuotientGroup.eq_iff_div_mem,
          Subgroup.mem_subgroupOf]
        convert hcomm (x : G) x.2 (y : G) y.2 using 1 <;> simp [div_eq_mul_inv] <;> group }
  -- the conjugation action of `C_Q(P)` on `R`
  let ψ : A →* ↥(Subgroup.normalizer (R : Set G)) :=
    { toFun := fun y => ⟨(y : G), hRn (hCle y.2)⟩
      map_one' := Subtype.ext rfl
      map_mul' := fun a b => Subtype.ext rfl }
  let cAhom : A →* MulAut ↥R := (Work.S3.CQEll.conjAutHom R).comp ψ
  have hpres : ∀ y : A, Subgroup.map (↑(cAhom y)) RN = RN := fun y =>
    Work.S3.CQEll.map_subgroupOf_conjAut' R N (y : G) (hRn (hCle y.2)) (hNn (hCle y.2))
  -- pushed to the quotient
  let F : A →* MulAut E :=
    { toFun := fun y => QuotientGroup.congr RN RN (cAhom y) (hpres y)
      map_one' := by
        apply MulEquiv.ext; intro x
        refine QuotientGroup.induction_on x ?_; intro z
        simp only [QuotientGroup.congr_mk, map_one cAhom, MulAut.one_apply]
      map_mul' := fun y z => by
        apply MulEquiv.ext; intro x
        refine QuotientGroup.induction_on x ?_; intro w
        rw [MulAut.mul_apply, QuotientGroup.congr_mk, QuotientGroup.congr_mk, QuotientGroup.congr_mk,
          map_mul cAhom, MulAut.mul_apply] }
  letI : DistribMulAction A (Additive E) := Work.AppXIField.distribMulActionAdditiveOfHom A E F
  -- cardinality of `R/N`
  have hcardE : Nat.card E = f ^ m := by
    have hRNcard : Nat.card ↥RN = Nat.card ↥N :=
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe hNR).toEquiv
    have hpos : 0 < Nat.card ↥N := Nat.card_pos
    have h : Nat.card E * Nat.card ↥N = f ^ m * Nat.card ↥N := by
      calc Nat.card E * Nat.card ↥N
          = Nat.card (↥R ⧸ RN) * Nat.card ↥RN := by rw [hRNcard]
        _ = Nat.card ↥R := (Subgroup.card_eq_card_quotient_mul_card_subgroup RN).symm
        _ = Nat.card ↥N * f ^ m := hRcard
        _ = f ^ m * Nat.card ↥N := Nat.mul_comm _ _
    exact Nat.mul_right_cancel hpos h
  have hcard : Nat.card (Additive E) = f ^ m := by
    rw [Nat.card_congr Additive.toMul]; exact hcardE
  -- fixed-point-freeness
  have hfpf' : ∀ y : A, y ≠ 1 → ∀ v : Additive E, y • v = v → v = 0 := by
    intro y hy v hv
    revert hv
    refine QuotientGroup.induction_on v ?_
    intro x hv
    change (QuotientGroup.mk x : E) = 1
    have hfix : QuotientGroup.congr RN RN (cAhom y) (hpres y) (QuotientGroup.mk x) =
        QuotientGroup.mk x := hv
    rw [QuotientGroup.congr_mk] at hfix
    have hq : ((cAhom y x) / x : ↥R) ∈ RN := (QuotientGroup.eq_iff_div_mem).mp hfix
    have hmem : (y : G) * (x : G) * (y : G)⁻¹ * (x : G)⁻¹ ∈ N := by
      have h'' := Subgroup.mem_subgroupOf.mp hq
      have hcA : (((cAhom y x : ↥R) : G)) = (y : G) * (x : G) * (y : G)⁻¹ :=
        Work.S3.CQEll.conjAut_val R (y : G) (hRn (hCle y.2)) x
      simpa only [Subgroup.coe_div, Subgroup.coe_mul, Subgroup.coe_inv, div_eq_mul_inv, hcA]
        using h''
    exact (QuotientGroup.eq_one_iff x).mpr (Subgroup.mem_subgroupOf.mpr (by
      by_contra hx
      exact hy (Subtype.ext (by
        simpa only [Subgroup.coe_one] using hfpf (x : G) x.2 hx (y : G) y.2 hmem))))
  exact ⟨Additive E, inferInstance, inferInstance, inferInstance, hcard, hfpf'⟩

end Work.AppXIDickson
