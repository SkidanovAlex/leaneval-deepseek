import Mathlib.FieldTheory.KrullTopology
import Mathlib.RingTheory.Henselian
import Mathlib.NumberTheory.NumberField.Basic
import Mathlib.RingTheory.Flat.TorsionFree
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.RingTheory.Valuation.ValuationSubring
import Mathlib.NumberTheory.Padics.PadicVal.Basic
import Submission.Work.SSGRoute.E7Fin.resH2_mu_eq_zero_decomp_pt
import Submission.Work.SSGRoute.PT.H2_decomp_p_divisible
import Submission.Work.SSGRoute.PT.cardH2_units_openSubgroup_decomp
import Submission.Work.SSGRoute.PT.exists_kummerSES_units
import Submission.Work.SSGRoute.zmultiples_eq_top_of_card_le_prime
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# Milne, *ADT*, (1.1b) for the local class formation `(D_A, Ωˣ)`: the corestriction is injective
on the `p`-torsion

`Work.SSGRoute.E7Fin.corH2_injective_ptorsion_of_dvd_index_pt`: for a finite place `A` of `Ω` over
a number field `k` and an open subgroup `U ≤ D_A` of finite index, the corestriction
`corH2 U hU (Ωˣ) : H²(U, Ωˣ) → H²(D_A, Ωˣ)` is injective on the `p`-torsion for every prime `p`
dividing the index `[D_A : U]`.

This is the *single* arithmetic input of the local-arithmetic chapter (Milne, *ADT*, (1.1b) at the
open subgroup `U`), from which `hcor`, `hα₂` and the degree-`0`/`2` duality follow.

The chain, with every link proved in this workspace:

* `E7Fin.resH2_mu_eq_zero_decomp_pt` — restriction kills the index-torsion of `H²(D_A, μ_n)`
  (the local statement at the completion, transported to `D_A`);
* `E7Fin.resH2_eq_zero_of_mu_eq_zero_any_pt` — the Kummer sequence turns that into "restriction
  kills the `n`-torsion of `H²(D_A, Ωˣ)`";
* `exists_ptorsion_cor_ne_zero_pt` + `ptorsion_injective_of_nonzero_pt` (elementary group theory,
  reproduced here because the file holding them cannot be imported together with the proved local
  statement `PT.local_resH2_mu_eq_zero`: both define `PT.resH2_mapH2`) together with the
  card-formation inputs `Nakayama.br_pTorsion` and `PT.cardH2_units_openSubgroup_decomp`.
-/

open SSGRoute

namespace Work.SSGRoute.E7Fin

noncomputable section

set_option linter.style.haveILetI false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option maxHeartbeats 2000000

/-! ## Elementary group theory -/

/-- `p` does not divide the `p`-free part of `n ≠ 0`. -/
theorem padicValNat_not_dvd_div_pt (p n : ℕ) [Fact p.Prime] (hn : n ≠ 0) :
    ¬ p ∣ n / p ^ padicValNat p n := by
  have h1 : padicValNat p (n / p ^ padicValNat p n) = 0 := by
    rw [padicValNat.div_pow (pow_padicValNat_dvd)]
    exact Nat.sub_self _
  rcases (padicValNat.eq_zero_iff (p := p) (n := n / p ^ padicValNat p n)).mp h1 with h | h | h
  · exact absurd h (Fact.out : p.Prime).ne_one
  · have hle : p ^ padicValNat p n ≤ n := Nat.le_of_dvd (Nat.pos_of_ne_zero hn) pow_padicValNat_dvd
    exact absurd h (Nat.div_pos hle (pow_pos (Fact.out : p.Prime).pos _)).ne'
  · exact h

/-- Divisibility by `p` gives divisibility by every `p`-power. -/
theorem nsmul_pow_surjective_pt (p v : ℕ) {B : Type*} [AddCommGroup B]
    (hdiv : ∀ b : B, ∃ b' : B, p • b' = b) (b : B) :
    ∃ b' : B, p ^ v • b' = b := by
  induction v with
  | zero => exact ⟨b, by rw [pow_zero, one_smul]⟩
  | succ v ih =>
      obtain ⟨b', hb'⟩ := ih
      obtain ⟨b'', hb''⟩ := hdiv b'
      exact ⟨b'', by rw [pow_succ, mul_nsmul', hb'', hb']⟩

/-- A group whose `p`-torsion has `p` elements has a non-zero `p`-torsion element. -/
theorem ptorsion_ne_zero_of_natCard_pt {V : Type*} [AddCommGroup V] (p : ℕ) [Fact p.Prime]
    (h : Nat.card {y : V // p • y = 0} = p) :
    ∃ b : V, p • b = 0 ∧ b ≠ 0 := by
  haveI : Finite {y : V // p • y = 0} :=
    Nat.finite_of_card_ne_zero (by rw [h]; exact (Fact.out : p.Prime).ne_zero)
  haveI : Fintype {y : V // p • y = 0} := Fintype.ofFinite _
  obtain ⟨b, hb⟩ := Fintype.exists_ne_of_one_lt_card
    (by rw [Fintype.card_eq_nat_card, h]; exact (Fact.out : p.Prime).one_lt)
    (⟨0, by simp⟩ : {y : V // p • y = 0})
  exact ⟨b.1, b.2, fun h0 => hb (Subtype.ext h0)⟩

/-- **Elementary core.**  Let `cor : A → B`, `res : B → A` be additive maps with
`cor ∘ res = (k * m) • id` where `p ∤ m`, let `B` be `k`-divisible, let `res` kill the `k`-torsion
of `B`, and let `B` have a non-zero `p`-torsion element.  Then `cor` is non-zero on the
`p`-torsion of `A`. -/
theorem exists_ptorsion_cor_ne_zero_pt {A B : Type*} [AddCommGroup A] [AddCommGroup B]
    (p k m : ℕ) [Fact p.Prime] (hm : ¬ p ∣ m) (hk : 0 < k)
    (cor : A →+ B) (res : B →+ A)
    (hcr : ∀ b : B, cor (res b) = (k * m : ℕ) • b)
    (hdiv : ∀ b : B, ∃ b' : B, k • b' = b)
    (hker : ∀ b : B, k • b = 0 → res b = 0)
    (hne : ∃ b : B, p • b = 0 ∧ b ≠ 0) :
    ∃ y : A, p • y = 0 ∧ cor y ≠ 0 := by
  obtain ⟨b, hb, hbne⟩ := hne
  obtain ⟨b', hb'⟩ := hdiv b
  have hkp : k • (p • b') = 0 := by rw [smul_comm, hb', hb]
  refine ⟨res b', ?_, ?_⟩
  · rw [← map_nsmul]
    exact hker (p • b') hkp
  · intro hcor0
    have h1 : (k * m : ℕ) • b' = 0 := by rw [← hcr b', hcor0]
    have h2 : m • b = 0 := by
      rw [← hb']
      rw [← mul_nsmul]
      exact h1
    have hord : addOrderOf b = p := addOrderOf_eq_prime hb hbne
    have hdvd : addOrderOf b ∣ m := addOrderOf_dvd_iff_nsmul_eq_zero.mpr h2
    rw [hord] at hdvd
    exact hm hdvd

/-- **Injectivity on the `p`-torsion from one non-zero value.**  If the `p`-torsion of `V` has
exactly `p` elements and `φ` is non-zero on it, then `φ` is injective on it. -/
theorem ptorsion_injective_of_nonzero_pt {V W : Type*} [AddCommGroup V] [AddCommGroup W]
    (p : ℕ) [Fact p.Prime] (φ : V →+ W)
    (hcardV : Nat.card {y : V // p • y = 0} = p)
    (hnz : ∃ x : V, p • x = 0 ∧ φ x ≠ 0) :
    ∀ y : V, p • y = 0 → φ y = 0 → y = 0 := by
  classical
  let f : V →+ V :=
    { toFun := fun y => p • y, map_zero' := smul_zero p, map_add' := fun a b => smul_add p a b }
  have hkerV : ∀ y : V, y ∈ AddMonoidHom.ker f ↔ p • y = 0 := by
    intro y; simp [f, AddMonoidHom.mem_ker]
  have hcardK : Nat.card ↥(AddMonoidHom.ker f) = p :=
    (Nat.card_congr (Equiv.subtypeEquivRight hkerV)).symm.trans hcardV
  have hp0 : p ≠ 0 := (Fact.out : p.Prime).ne_zero
  haveI : Finite ↥(AddMonoidHom.ker f) := Nat.finite_of_card_ne_zero (by rw [hcardK]; exact hp0)
  have hpall : ∀ z : ↥(AddMonoidHom.ker f), p • z = 0 :=
    fun z => Subtype.ext (by simpa using (hkerV z.1).mp z.2)
  have hbound : Nat.card ↥(AddMonoidHom.ker f) ≤ p := le_of_eq hcardK
  obtain ⟨x, hx0, hxne⟩ := hnz
  have hxmem : x ∈ AddMonoidHom.ker f := (hkerV x).mpr hx0
  have hxne' : (⟨x, hxmem⟩ : ↥(AddMonoidHom.ker f)) ≠ 0 := by
    intro h
    have hx_eq : x = 0 := congrArg Subtype.val h
    exact hxne (by rw [hx_eq, map_zero])
  have htop := Work.SSGRoute.zmultiples_eq_top_of_card_le_prime p hpall hbound
    (⟨x, hxmem⟩ : ↥(AddMonoidHom.ker f)) hxne'
  have hord : addOrderOf (φ x) = p := by
    refine addOrderOf_eq_prime ?_ hxne
    rw [← map_nsmul, hx0, map_zero]
  intro y hy hyphi
  have hymem : y ∈ AddMonoidHom.ker f := (hkerV y).mpr hy
  have hzy : (⟨y, hymem⟩ : ↥(AddMonoidHom.ker f)) ∈
      AddSubgroup.zmultiples (⟨x, hxmem⟩ : ↥(AddMonoidHom.ker f)) := by
    rw [htop]; exact AddSubgroup.mem_top _
  obtain ⟨m, hm⟩ := AddSubgroup.mem_zmultiples_iff.mp hzy
  have hcoe : m • x = y := by
    have := congrArg Subtype.val hm
    simpa using this
  have hdvd : (p : ℤ) ∣ m := by
    have h : (↑(addOrderOf (φ x)) : ℤ) ∣ m :=
      (addOrderOf_dvd_iff_zsmul_eq_zero (x := φ x)).mpr (by rw [← map_zsmul, hcoe, hyphi])
    rwa [hord] at h
  obtain ⟨j, hj⟩ := hdvd
  rw [← hcoe, hj, mul_zsmul, natCast_zsmul, smul_comm, hx0, smul_zero]

/-! ## The Kummer step: from `μ_n` to the units -/

/-- **From the `μ_n`-form of (1.1b) to `res` killing the `n`-torsion of `H²(D_A, Ωˣ)`.**

If restriction kills the index-torsion of the `μ_n`-coefficient group `H²(D_A, μ_n(Ω))`, then for
`n ∣ [D_A : U]` it kills the `n`-torsion of `H²(D_A, Ωˣ)`: a class `e` with `n • e = 0` is the
image of a `μ_n`-class under the Kummer sequence
`1 → μ_n → Ωˣ →^n Ωˣ → 1`, and every `μ_n`-class has exponent dividing `n`, hence is
index-torsion. -/
theorem resH2_eq_zero_of_mu_eq_zero_any_pt (n : ℕ) [NeZero n] (k Ω : Type) [Field k]
    [NumberField k] [Field Ω] [Algebra k Ω] [IsAlgClosure k Ω] (A : ValuationSubring Ω)
    (hA : SSGRoute.IsFinPlace k A) (U : Subgroup ↥(SSGRoute.decomp k A))
    (hU : IsOpen (U : Set ↥(SSGRoute.decomp k A))) [U.FiniteIndex]
    [Fintype (↥(SSGRoute.decomp k A) ⧸ U)]
    (hndvd : n ∣ Nat.card (↥(SSGRoute.decomp k A) ⧸ U))
    (hμ : ∀ x : Work.AbsoluteKummer.H2 ↥(SSGRoute.decomp k A) (Additive (rootsOfUnity n Ω)),
      Nat.card (↥(SSGRoute.decomp k A) ⧸ U) • x = 0 → Work.SSGRoute.PT.resH2 U x = 0)
    (e : Work.AbsoluteKummer.H2 ↥(SSGRoute.decomp k A) (Additive (Units Ω)))
    (he : n • e = 0) : Work.SSGRoute.PT.resH2 U e = 0 := by
  classical
  obtain ⟨S, hpi, _⟩ := Work.SSGRoute.PT.exists_kummerSES_units n k Ω
    (SSGRoute.decomp k A) (Work.SSGRoute.PTembedding.isClosed_decomp' k Ω A)
  have hpi' : ∀ u : Additive (Units Ω), S.pi u = n • u := hpi
  have hrange := Work.SSGRoute.PT.range_mapH2_eq_ker_nsmul n S hpi'
  have hemem : e ∈ (Work.SSGRoute.PT.nsmulHom n
      (Work.AbsoluteKummer.H2 ↥(SSGRoute.decomp k A) (Additive (Units Ω)))).ker := by
    rw [AddMonoidHom.mem_ker, Work.SSGRoute.PT.nsmulHom_apply]
    exact he
  obtain ⟨x, hx⟩ := AddMonoidHom.mem_range.mp (by rw [hrange]; exact hemem)
  have hCoeff : ∀ m : Additive (rootsOfUnity n Ω), n • m = 0 := by
    intro m
    show Additive.ofMul ((Additive.toMul m : rootsOfUnity n Ω) ^ n) = 0
    have hm : ((Additive.toMul m : rootsOfUnity n Ω) : Ωˣ) ^ n = 1 :=
      (mem_rootsOfUnity n ((Additive.toMul m : rootsOfUnity n Ω) : Ωˣ)).mp
        (Additive.toMul m).2
    rw [show (Additive.toMul m : rootsOfUnity n Ω) ^ n = 1 from
      Subtype.ext (by simpa using hm)]
    rfl
  have hidx : Nat.card (↥(SSGRoute.decomp k A) ⧸ U) • x = 0 := by
    obtain ⟨k', hk'⟩ := hndvd
    rw [hk', mul_nsmul, H2_nsmul_eq_zero_of_exponent n hCoeff x, smul_zero]
  rw [← hx, resH2_mapH2 U S.iota S.iota_equivariant x, hμ x hidx, map_zero]

/-! ## The target -/

/-- **Milne, *ADT*, (1.1b) at the open subgroup `U` of `D_A`** (`p`-torsion form): the corestriction
`corH2 U hU (Ωˣ) : H²(U, Ωˣ) → H²(D_A, Ωˣ)` is injective on the `p`-torsion for every prime `p`
dividing the index `[D_A : U]`. -/
theorem corH2_injective_ptorsion_of_dvd_index_pt (k Ω : Type) [Field k] [NumberField k]
    [Field Ω] [Algebra k Ω] [IsAlgClosure k Ω] (A : ValuationSubring Ω)
    (hA : SSGRoute.IsFinPlace k A) (U : Subgroup ↥(SSGRoute.decomp k A))
    (hU : IsOpen (U : Set ↥(SSGRoute.decomp k A))) [U.FiniteIndex]
    [Fintype (↥(SSGRoute.decomp k A) ⧸ U)] (p : ℕ) [Fact p.Prime]
    (hp : p ∣ Nat.card (↥(SSGRoute.decomp k A) ⧸ U))
    (x : Work.AbsoluteKummer.H2 ↥U (Additive (Units Ω)))
    (hx : p • x = 0)
    (hcor : Work.SSGRoute.PT.corH2 U hU (Additive (Units Ω)) x = 0) :
    x = 0 := by
  classical
  set n := Nat.card (↥(SSGRoute.decomp k A) ⧸ U) with hn
  set a := padicValNat p n with ha
  set kk := p ^ a with hkk
  set m := n / kk with hm
  have hn0 : n ≠ 0 := by
    rw [hn, Nat.card_eq_fintype_card]; exact Fintype.card_ne_zero
  have hkvdvd : kk ∣ n := by rw [hkk, ha]; exact pow_padicValNat_dvd
  have hkm : kk * m = n := by rw [hm]; exact Nat.mul_div_cancel' hkvdvd
  have hkpos : 0 < kk := by rw [hkk]; exact pow_pos (Fact.out : p.Prime).pos a
  have hndvd : ¬ p ∣ m := by
    rw [hm, hkk, ha]
    exact padicValNat_not_dvd_div_pt p n hn0
  haveI : NeZero kk := ⟨hkpos.ne'⟩
  -- `res` kills the `kk`-torsion of `H²(D_A, Ωˣ)`
  have hkill : ∀ b : Work.AbsoluteKummer.H2 ↥(SSGRoute.decomp k A) (Additive (Units Ω)),
      kk • b = 0 → Work.SSGRoute.PT.resH2 U b = 0 := by
    intro b hb
    refine resH2_eq_zero_of_mu_eq_zero_any_pt kk k Ω A hA U hU ?_ ?_ b hb
    · rw [← hn]; exact hkvdvd
    · intro y hy
      exact resH2_mu_eq_zero_decomp_pt kk k Ω A hA U hU y (by rwa [← hn] at hy)
  -- `H²(D_A, Ωˣ)` is `kk`-divisible
  have hdivB : ∀ b : Work.AbsoluteKummer.H2 ↥(SSGRoute.decomp k A) (Additive (Units Ω)),
      ∃ b' : Work.AbsoluteKummer.H2 ↥(SSGRoute.decomp k A) (Additive (Units Ω)), kk • b' = b := by
    intro b
    rw [hkk]
    exact nsmul_pow_surjective_pt p a (Work.SSGRoute.PT.H2_decomp_p_divisible p k Ω A hA) b
  -- a non-zero `p`-torsion class of the local Brauer group
  have hne : ∃ b : Work.AbsoluteKummer.H2 ↥(SSGRoute.decomp k A) (Additive (Units Ω)),
      p • b = 0 ∧ b ≠ 0 :=
    ptorsion_ne_zero_of_natCard_pt
      (V := Work.AbsoluteKummer.H2 ↥(SSGRoute.decomp k A) (Additive (Units Ω)))
      p (Work.SSGRoute.Nakayama.br_pTorsion p k Ω A hA)
  -- the two composites
  have hcr : ∀ b : Work.AbsoluteKummer.H2 ↥(SSGRoute.decomp k A) (Additive (Units Ω)),
      Work.SSGRoute.PT.corH2 U hU (Additive (Units Ω)) (Work.SSGRoute.PT.resH2 U b)
        = (kk * m) • b := by
    intro b
    rw [Work.SSGRoute.PT.corH2_resH2_eq_index, Subgroup.index_eq_card U, ← hn, ← hkm]
  obtain ⟨y, hy0, hyne⟩ := exists_ptorsion_cor_ne_zero_pt
    (A := Work.AbsoluteKummer.H2 ↥U (Additive (Units Ω)))
    (B := Work.AbsoluteKummer.H2 ↥(SSGRoute.decomp k A) (Additive (Units Ω)))
    p kk m hndvd hkpos
    (Work.SSGRoute.PT.corH2 U hU (Additive (Units Ω))) (Work.SSGRoute.PT.resH2 U)
    hcr hdivB hkill hne
  exact ptorsion_injective_of_nonzero_pt
    (V := Work.AbsoluteKummer.H2 ↥U (Additive (Units Ω)))
    (W := Work.AbsoluteKummer.H2 ↥(SSGRoute.decomp k A) (Additive (Units Ω))) p
    (Work.SSGRoute.PT.corH2 U hU (Additive (Units Ω)))
    (Work.SSGRoute.PT.cardH2_units_openSubgroup_decomp p k Ω A hA U hU)
    ⟨y, hy0, hyne⟩ x hx hcor

end

end Work.SSGRoute.E7Fin
