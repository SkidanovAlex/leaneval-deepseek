import Mathlib
import Submission.Work.Higman.Q3.Defs
import Submission.Work.Higman.CoordDefs

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

open scoped commutatorElement
open IsMulCommutative

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.style.haveILetI false

namespace Work.Higman

theorem assembly {P : Type} [Group P] [Finite P]
    (hsq : ∀ x : P, x ^ 2 ∈ Subgroup.center P)
    (hexp : ∀ z : P, z ∈ Subgroup.center P → z ^ 2 = 1)
    (hC : ∀ (n : ℕ) (A : Fin n → P),
      (∀ v w u : Fin n → ZMod 2, cocy n A (v + w) u = cocy n A v u * cocy n A w u) ∧
      (∀ v w u : Fin n → ZMod 2, cocy n A v (w + u) = cocy n A v w * cocy n A v u) ∧
      (∀ v w : Fin n → ZMod 2, cocy n A v w ∈ Subgroup.center P)) :
    Nonempty (TwoStepModel.{0,0,0} P) := by
  haveI hcomm : IsMulCommutative (P ⧸ Subgroup.center P) := by
    refine IsMulCommutative.of_comm ?_
    have hq : ∀ z : P ⧸ Subgroup.center P, z ^ 2 = 1 := by
      intro z
      induction z using QuotientGroup.induction_on with
      | _ a => rw [← QuotientGroup.mk_pow, QuotientGroup.eq_one_iff]; exact hsq a
    have hq2 : ∀ z : P ⧸ Subgroup.center P, z * z = 1 := fun z => by simpa [pow_two] using hq z
    intro x y
    have hx : x⁻¹ = x := inv_eq_of_mul_eq_one_right (hq2 x)
    have hy : y⁻¹ = y := inv_eq_of_mul_eq_one_right (hq2 y)
    have hxy : (x*y)⁻¹ = x*y := inv_eq_of_mul_eq_one_right (hq2 (x*y))
    rw [← hxy, mul_inv_rev, hx, hy]
  have hq : ∀ z : P ⧸ Subgroup.center P, z ^ 2 = 1 := by
    intro z
    induction z using QuotientGroup.induction_on with
    | _ a => rw [← QuotientGroup.mk_pow, QuotientGroup.eq_one_iff]; exact hsq a
  haveI hAddV : Work.Higman.AddExpTwo (Additive (P ⧸ Subgroup.center P)) :=
    ⟨fun x => by
      apply Additive.ext
      simp only [toMul_add, toMul_zero]
      simpa [pow_two] using hq (Additive.toMul x)⟩
  haveI hAddW : Work.Higman.AddExpTwo (Additive ↥(Subgroup.center P)) :=
    ⟨fun x => by
      apply Additive.ext
      simp only [toMul_add, toMul_zero]
      have h := hexp ((Additive.toMul x : ↥(Subgroup.center P)) : P) (Additive.toMul x).2
      rw [pow_two] at h
      exact Subtype.ext h⟩
  haveI hModV : Module (ZMod 2) (Additive (P ⧸ Subgroup.center P)) :=
    AddCommGroup.zmodModule (by
      intro x; rw [two_nsmul]; exact Work.Higman.AddExpTwo.add_self x)
  haveI hFinV : Module.Finite (ZMod 2) (Additive (P ⧸ Subgroup.center P)) :=
    Module.Finite.of_finite
  let π : P → Additive (P ⧸ Subgroup.center P) :=
    fun x => Additive.ofMul (x : P ⧸ Subgroup.center P)
  have hπ : ∀ x y, π (x * y) = π x + π y := by
    intro x y; simp only [π, QuotientGroup.mk_mul, ofMul_mul]
  have hπ1 : π 1 = 0 := by simp [π]
  have hπker : ∀ z : P, π z = 0 ↔ z ∈ Subgroup.center P := by
    intro z
    constructor
    · intro h
      have h' : (z : P ⧸ Subgroup.center P) = 1 := by
        apply Additive.ofMul.injective
        rw [ofMul_one]
        exact h
      rwa [QuotientGroup.eq_one_iff] at h'
    · intro hz
      simp only [π]
      rw [show (z : P ⧸ Subgroup.center P) = 1 from by
        rw [QuotientGroup.eq_one_iff]; exact hz]
      rfl
  have hπinv : ∀ x, π x⁻¹ = -π x := by
    intro x
    have h := hπ x x⁻¹
    rw [mul_inv_cancel, hπ1] at h
    exact eq_neg_of_add_eq_zero_right h.symm
  let n := Module.finrank (ZMod 2) (Additive (P ⧸ Subgroup.center P))
  let bb : Module.Basis (Fin n) (ZMod 2) (Additive (P ⧸ Subgroup.center P)) :=
    Module.finBasis (ZMod 2) (Additive (P ⧸ Subgroup.center P))
  let e : Additive (P ⧸ Subgroup.center P) ≃ₗ[ZMod 2] (Fin n → ZMod 2) := bb.equivFun
  have hπsurj : ∀ v : Additive (P ⧸ Subgroup.center P), ∃ x : P, π x = v := by
    intro v
    obtain ⟨x, hx⟩ := QuotientGroup.mk'_surjective (Subgroup.center P) (Additive.toMul v)
    refine ⟨x, ?_⟩
    rw [show v = Additive.ofMul (Additive.toMul v) from (ofMul_toMul v).symm]
    congr 1
  let A : Fin n → P := fun i => Classical.choose (hπsurj (bb i))
  have hA : ∀ i, π (A i) = bb i := fun i => Classical.choose_spec (hπsurj (bb i))
  have hpi : ∀ v : Additive (P ⧸ Subgroup.center P), π (coordSec n A (e v)) = v := by
    intro v
    rw [pi_coordSec π hπ hπ1 n A bb hA (e v)]
    rw [← Module.Basis.equivFun_symm_apply bb (e v)]
    exact e.symm_apply_apply v
  obtain ⟨hL, hR, hMem⟩ := hC n A
  let b : Additive (P ⧸ Subgroup.center P) → Additive (P ⧸ Subgroup.center P) →
      Additive ↥(Subgroup.center P) :=
    fun v w => Additive.ofMul ⟨cocy n A (e v) (e w), hMem (e v) (e w)⟩
  have hb : Work.Higman.Biadd b := by
    constructor
    · intro v v' w
      apply Additive.ext
      simp only [b, toMul_add, toMul_ofMul]
      apply Subtype.ext
      rw [map_add]
      exact hL (e v) (e v') (e w)
    · intro v w w'
      apply Additive.ext
      simp only [b, toMul_add, toMul_ofMul]
      apply Subtype.ext
      rw [map_add]
      exact hR (e v) (e w) (e w')
  let ofW : Additive ↥(Subgroup.center P) → P :=
    fun z => ((Additive.toMul z : ↥(Subgroup.center P)) : P)
  have hofW_add : ∀ z z' : Additive ↥(Subgroup.center P), ofW (z + z') = ofW z * ofW z' := by
    intro z z'; simp only [ofW, toMul_add]; rfl
  have hofW_mem : ∀ z : Additive ↥(Subgroup.center P), ofW z ∈ Subgroup.center P :=
    fun z => (Additive.toMul z).2
  have hofW_inj : Function.Injective ofW := by
    intro z z' h
    have h' : (Additive.toMul z : ↥(Subgroup.center P)) = Additive.toMul z' := Subtype.ext h
    exact Additive.toMul.injective h'
  have hπ_ofW : ∀ z : Additive ↥(Subgroup.center P), π (ofW z) = 0 := by
    intro z; exact (hπker _).mpr (Additive.toMul z).2
  let s : Additive (P ⧸ Subgroup.center P) → P := fun v => coordSec n A (e v)
  have hπs : ∀ v, π (s v) = v := fun v => hpi v
  have hs_eq : ∀ v w : Additive (P ⧸ Subgroup.center P),
      cocy n A (e v) (e w) = s v * s w * (s (v + w))⁻¹ := by
    intro v w
    simp only [cocy, s, map_add]
  have hofWb : ∀ v w : Additive (P ⧸ Subgroup.center P), ofW (b v w) = cocy n A (e v) (e w) := by
    intro v w
    simp only [ofW, b, toMul_ofMul, Subtype.coe_mk]
  have hkey : ∀ v w : Additive (P ⧸ Subgroup.center P), s v * s w = ofW (b v w) * s (v + w) := by
    intro v w
    rw [hofWb v w, hs_eq v w]
    group
  have hs0 : s (0 : Additive (P ⧸ Subgroup.center P)) = 1 := by
    simp only [s, map_zero, coordSec_zero_fun]
  have hofW0 : ofW (0 : Additive ↥(Subgroup.center P)) = 1 := by simp [ofW]
  let φfun : TwoStep (Additive (P ⧸ Subgroup.center P)) (Additive ↥(Subgroup.center P)) b → P :=
    fun x => s x.fst * ofW x.snd
  have hφmul : ∀ x y : TwoStep (Additive (P ⧸ Subgroup.center P)) (Additive ↥(Subgroup.center P)) b,
      φfun (x * y) = φfun x * φfun y := by
    intro x y
    have hc1 : ∀ t : P, t * ofW x.snd = ofW x.snd * t :=
      Subgroup.mem_center_iff.mp (hofW_mem x.snd)
    have hcb : ∀ t : P, t * ofW (b x.fst y.fst) = ofW (b x.fst y.fst) * t :=
      Subgroup.mem_center_iff.mp (hofW_mem (b x.fst y.fst))
    have hstep : (s x.fst * ofW x.snd) * (s y.fst * ofW y.snd)
        = (s x.fst * s y.fst) * (ofW x.snd * ofW y.snd) := by
      rw [mul_assoc]
      rw [← mul_assoc (ofW x.snd) (s y.fst) (ofW y.snd)]
      rw [← hc1 (s y.fst)]
      rw [mul_assoc (s y.fst) (ofW x.snd) (ofW y.snd),
        ← mul_assoc (s x.fst) (s y.fst) (ofW x.snd * ofW y.snd)]
    show s (x.fst + y.fst) * ofW (x.snd + y.snd + b x.fst y.fst)
        = (s x.fst * ofW x.snd) * (s y.fst * ofW y.snd)
    rw [hstep, hkey x.fst y.fst, hofW_add, hofW_add]
    conv_lhs => rw [hcb (ofW x.snd * ofW y.snd), ← mul_assoc, hcb (s (x.fst + y.fst))]
  have hφ1 : φfun 1 = 1 := by
    show s (0 : Additive (P ⧸ Subgroup.center P)) * ofW (0 : Additive ↥(Subgroup.center P)) = 1
    rw [hs0, hofW0, one_mul]
  have hφinj : Function.Injective φfun := by
    intro x y hxy
    have hv : x.fst = y.fst := by
      have hh := congrArg π hxy
      simp only [φfun, hπ, hπs, hπ_ofW, add_zero] at hh
      exact hh
    have hz : x.snd = y.snd := by
      have hh : s y.fst * ofW x.snd = s y.fst * ofW y.snd := by
        have h2 := hxy
        simp only [φfun] at h2
        rw [hv] at h2
        exact h2
      exact hofW_inj (mul_left_cancel hh)
    exact TwoStep.ext_iff hv hz
  have hφsurj : Function.Surjective φfun := by
    intro y
    have hyc : (s (π y))⁻¹ * y ∈ Subgroup.center P := by
      rw [← hπker]
      rw [hπ, hπinv, hπs]
      abel
    refine ⟨⟨π y, Additive.ofMul ⟨(s (π y))⁻¹ * y, hyc⟩⟩, ?_⟩
    show s (π y) * ofW (Additive.ofMul ⟨(s (π y))⁻¹ * y, hyc⟩) = y
    have hofWy : ofW (Additive.ofMul ⟨(s (π y))⁻¹ * y, hyc⟩) = (s (π y))⁻¹ * y := by
      simp only [ofW, toMul_ofMul, Subtype.coe_mk]
    rw [hofWy]
    group
  let φ : TwoStep (Additive (P ⧸ Subgroup.center P)) (Additive ↥(Subgroup.center P)) b →* P :=
    { toFun := φfun, map_one' := hφ1, map_mul' := hφmul }
  have hφbij : Function.Bijective φ := ⟨hφinj, hφsurj⟩
  let φe : TwoStep (Additive (P ⧸ Subgroup.center P)) (Additive ↥(Subgroup.center P)) b ≃* P :=
    MulEquiv.ofBijective φ hφbij
  have hcardV : Nat.card (Additive (P ⧸ Subgroup.center P)) = Nat.card (P ⧸ Subgroup.center P) :=
    Nat.card_congr (Additive.toMul : Additive (P ⧸ Subgroup.center P) ≃ (P ⧸ Subgroup.center P))
  have hcardW : Nat.card (Additive ↥(Subgroup.center P)) = Nat.card ↥(Subgroup.center P) :=
    Nat.card_congr (Additive.toMul : Additive ↥(Subgroup.center P) ≃ ↥(Subgroup.center P))
  refine ⟨{ V := Additive (P ⧸ Subgroup.center P)
            W := Additive ↥(Subgroup.center P)
            b := b
            biadd_b := hb
            card_V := hcardV
            card_W := hcardW
            iso := φe.symm }⟩

end Work.Higman
