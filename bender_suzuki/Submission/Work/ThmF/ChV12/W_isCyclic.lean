import Mathlib
import Submission.Work.ThmF.ChV12.L6basic
import Submission.Work.ThmF.ChV12.L6faith
import Submission.Work.ThmF.ChV12.L6setup
import Submission.Work.ThmF.ChV12.W_semireg
import Submission.Work.ThmF.ChV12.W_layer_safe
import Submission.Work.ThmF.ChV12.psi_preimage_isXiLayer
import Submission.Work.ThmF.ChV12.orderOf_lam_eq
import Submission.Work.Higman.typeB_scalar
import Submission.Work.Higman.typeB_of_odd_fpf
import Submission.Work.Higman.typeB
import Submission.Work.Higman.BS.Defs

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

set_option autoImplicit false
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false
set_option linter.style.haveILetI false
set_option maxHeartbeats 1600000

open LeanEval.GroupTheory.Defs
open scoped commutatorElement

namespace Work.ThmF.ChV12

open Submission.Blueprint Work.ThmF

variable {G : Type} [Group G] [Finite G] {H Q : Subgroup G} {t s : G}

/-! ## §1. The conjugation action of `W = C_V(K)` on `Q`

`W ≤ D = twoPoint H t ≤ N_G(Q)`, so conjugation gives a monoid homomorphism
`↥(W H t) →* MulAut ↥Q`, injective because `D` acts faithfully on `Q` (`L6faith`). -/

theorem conjAut_proof_irrel {G : Type} [Group G] {Q : Subgroup G} (g : G)
    (h1 h2 : g ∈ Subgroup.normalizer (Q : Set G)) :
    conjAut g h1 = conjAut g h2 := by
  apply MulEquiv.ext
  intro x
  apply Subtype.ext
  rfl

theorem conjAut_mul {G : Type} [Group G] {Q : Subgroup G} (g g' : G)
    (hg : g ∈ Subgroup.normalizer (Q : Set G)) (hg' : g' ∈ Subgroup.normalizer (Q : Set G))
    (hgg' : g * g' ∈ Subgroup.normalizer (Q : Set G)) :
    conjAut (g * g') hgg' = conjAut g hg * conjAut g' hg' := by
  apply MulEquiv.ext
  intro x
  apply Subtype.ext
  show (g * g') * (x : G) * (g * g')⁻¹ = g * (g' * (x : G) * g'⁻¹) * g⁻¹
  group

theorem W_le_normalizer (h : IsSplitRankOne H Q t) :
    W H t ≤ Subgroup.normalizer (Q : Set G) :=
  fun w hw => h.normal (Subgroup.mem_inf.mp
    (centD_le_twoPoint (H := H) t (W_le_centD H t hw))).1

/-- Conjugation by an element of `W`, as an automorphism of `↥Q`. -/
noncomputable def conjAutHom (h : IsSplitRankOne H Q t) : ↥(W H t) →* MulAut ↥Q where
  toFun w := conjAut (w : G) (W_le_normalizer h w.2)
  map_one' := by
    apply MulEquiv.ext
    intro x
    apply Subtype.ext
    show (1 : G) * (x : G) * (1 : G)⁻¹ = (x : G)
    simp
  map_mul' := fun a b => by
    apply MulEquiv.ext
    intro x
    apply Subtype.ext
    show (a : G) * (b : G) * (x : G) * ((a : G) * (b : G))⁻¹
      = (a : G) * ((b : G) * (x : G) * (b : G)⁻¹) * (a : G)⁻¹
    group

theorem conjAutHom_apply (h : IsSplitRankOne H Q t) (w : ↥(W H t)) (x : ↥Q) :
    ((conjAutHom h w x : ↥Q) : G) = (w : G) * (x : G) * (w : G)⁻¹ := rfl

/-- `W` acts faithfully on `Q`: an element of `W` inducing the identity on `Q` is trivial. -/
theorem conjAutHom_injective (hS : Situation G) (h : IsSplitRankOne H Q t) :
    Function.Injective (conjAutHom h) := by
  intro a b hab
  have hmem : (a : G) ∈ twoPoint H t := centD_le_twoPoint (H := H) t (W_le_centD H t a.2)
  have hmem' : (b : G) ∈ twoPoint H t := centD_le_twoPoint (H := H) t (W_le_centD H t b.2)
  have hxy : ∀ x ∈ Q, (a : G) * x * (a : G)⁻¹ = (b : G) * x * (b : G)⁻¹ := by
    intro x hx
    have h1 : (conjAutHom h a) ⟨x, hx⟩ = (conjAutHom h b) ⟨x, hx⟩ := by rw [hab]
    have h2 := congrArg (fun y : ↥Q => (y : G)) h1
    rwa [conjAutHom_apply, conjAutHom_apply] at h2
  have hcen : ∀ x ∈ Q, ((b : G)⁻¹ * (a : G)) * x = x * ((b : G)⁻¹ * (a : G)) := by
    intro x hx
    have h3 : (b : G)⁻¹ * (a : G) * x * ((b : G)⁻¹ * (a : G))⁻¹ = x := by
      calc (b : G)⁻¹ * (a : G) * x * ((b : G)⁻¹ * (a : G))⁻¹
          = (b : G)⁻¹ * ((a : G) * x * (a : G)⁻¹) * (b : G) := by group
        _ = (b : G)⁻¹ * ((b : G) * x * (b : G)⁻¹) * (b : G) := by rw [hxy x hx]
        _ = x := by group
    have h4 := congrArg (fun y => y * ((b : G)⁻¹ * (a : G))) h3
    simpa [mul_assoc] using h4
  have hd : (b : G)⁻¹ * (a : G) ∈ twoPoint H t :=
    (twoPoint H t).mul_mem ((twoPoint H t).inv_mem hmem') hmem
  have h1 : (b : G)⁻¹ * (a : G) = 1 := eq_one_of_centralizes_Q hS h hd hcen
  refine Subtype.ext ?_
  have := congrArg (fun y => (b : G) * y) h1
  simpa using this

/-- `conjAutHom` fixes the centre `Z(Q)` pointwise (`W` centralises `Q₀ = Z(Q)`). -/
theorem conjAutHom_center (hC4 : ChIIFourProp) (hH : Work.ThmF.Lemma5.Hyp5 H Q t s)
    (hHig : HigmanProp) (hSuz : IsSuzukiTwoGroup ↥Q) (w : ↥(W H t)) (z : ↥Q)
    (hz : z ∈ Subgroup.center ↥Q) :
    conjAutHom hH.split w z = z := by
  have hzQ0 : (z : G) ∈ Q0sub H :=
    Subgroup.mem_subgroupOf.mp (by rw [← center_eq_subgroupOf hC4 hH hHig hSuz]; exact hz)
  have hzc := Subgroup.mem_centralizer_iff.mp
    (W_le_centralizer_Q0sub hC4 hH.sit hH.split w.2) (z : G) hzQ0
  apply Subtype.ext
  rw [conjAutHom_apply]
  show (w : G) * (z : G) * (w : G)⁻¹ = (z : G)
  rw [hzc.symm, mul_assoc, mul_inv_cancel, mul_one]

/-- Conjugation by `w ∈ W` commutes with conjugation by `k ∈ Kset H t`. -/
theorem conjAutHom_comm_k (h : IsSplitRankOne H Q t) {k : G} (hkK : k ∈ Kset H t)
    (hkN : k ∈ Subgroup.normalizer (Q : Set G)) (w : ↥(W H t)) :
    conjAutHom h w * conjAut k hkN = conjAut k hkN * conjAutHom h w := by
  have hwk : k * (w : G) = (w : G) * k :=
    Subgroup.mem_centralizer_iff.mp (Subgroup.mem_inf.mp w.2).2 k hkK
  apply MulEquiv.ext
  intro z
  apply Subtype.ext
  have lhs : (((conjAutHom h w) * conjAut k hkN) z : G)
      = (w : G) * (k * (z : G) * k⁻¹) * (w : G)⁻¹ := by
    rw [MulAut.mul_apply, conjAutHom_apply, conjAut_coe]
  have rhs : (((conjAut k hkN) * conjAutHom h w) z : G)
      = k * ((w : G) * (z : G) * (w : G)⁻¹) * k⁻¹ := by
    rw [MulAut.mul_apply, conjAut_coe, conjAutHom_apply]
  rw [lhs, rhs]
  calc (w : G) * (k * (z : G) * k⁻¹) * (w : G)⁻¹
      = ((w : G) * k) * (z : G) * ((w : G) * k)⁻¹ := by group
    _ = (k * (w : G)) * (z : G) * (k * (w : G))⁻¹ := by rw [hwk]
    _ = k * ((w : G) * (z : G) * (w : G)⁻¹) * k⁻¹ := by group

/-- Every automorphism of a group preserves its centre (as a set). -/
theorem mulAut_mem_center {P : Type} [Group P] (φ : MulAut P) {z : P}
    (hz : z ∈ Subgroup.center P) : φ z ∈ Subgroup.center P := by
  rw [Subgroup.mem_center_iff] at hz ⊢
  intro g
  calc g * φ z = φ (φ.symm g * z) := by rw [map_mul, MulEquiv.apply_symm_apply]
    _ = φ (z * φ.symm g) := by rw [hz (φ.symm g)]
    _ = φ z * g := by rw [map_mul, MulEquiv.apply_symm_apply]

/-! ## §2. The `F`-linear action of `W` on `V = F × F ≅ Q / Z(Q)`

Fix a finite field `F` of order `q = |Z(Q)|`, an additive surjection `ψ : ↥Q → F × F` with
kernel `Z(Q)` and `λ ∈ Fˣ` with `ψ (ξ x) = λ • ψ x`.  Then every `w ∈ W` induces an `F`-linear
automorphism `φ w` of `F × F` characterised by `φ w (ψ x) = ψ (w x w⁻¹)`. -/

section Linear

variable {F : Type} [Field F] [Fintype F] {ψ : ↥Q → F × F}

theorem psi_one (hadd : ∀ x y : ↥Q, ψ (x * y) = ψ x + ψ y) : ψ 1 = 0 := by
  have h1 : ψ 1 = ψ 1 + ψ 1 := by rw [← hadd 1 1, one_mul]
  have h2 : ψ 1 + 0 = ψ 1 + ψ 1 := by rw [add_zero]; exact h1
  exact (add_left_cancel h2).symm

theorem psi_inv (hadd : ∀ x y : ↥Q, ψ (x * y) = ψ x + ψ y) (x : ↥Q) : ψ x⁻¹ = - ψ x := by
  have h0 : ψ x + ψ x⁻¹ = 0 := by
    have h1 : ψ (x * x⁻¹) = ψ x + ψ x⁻¹ := hadd x x⁻¹
    rw [mul_inv_cancel, psi_one hadd] at h1
    exact h1.symm
  exact eq_neg_of_add_eq_zero_right h0

/-- The action of `w ∈ W` on `F × F`, defined by transporting along `ψ`. -/
noncomputable def phiFun (hsurj : Function.Surjective ψ) (h : IsSplitRankOne H Q t)
    (w : ↥(W H t)) (v : F × F) : F × F :=
  ψ (conjAutHom h w (Classical.choose (hsurj v)))

theorem phiFun_eq (hadd : ∀ x y : ↥Q, ψ (x * y) = ψ x + ψ y)
    (hker : ∀ x : ↥Q, ψ x = 0 ↔ x ∈ Subgroup.center ↥Q)
    (hsurj : Function.Surjective ψ) (h : IsSplitRankOne H Q t)
    (hcen : ∀ (w : ↥(W H t)) (z : ↥Q), z ∈ Subgroup.center ↥Q → conjAutHom h w z = z)
    (w : ↥(W H t)) {y : ↥Q} {v : F × F} (hy : ψ y = v) :
    phiFun hsurj h w v = ψ (conjAutHom h w y) := by
  have hspec : ψ (Classical.choose (hsurj v)) = v := Classical.choose_spec (hsurj v)
  show ψ (conjAutHom h w (Classical.choose (hsurj v))) = ψ (conjAutHom h w y)
  have hyy : ψ (Classical.choose (hsurj v)) = ψ y := by rw [hspec, hy]
  have hz0 : ψ (Classical.choose (hsurj v) * y⁻¹) = 0 := by
    rw [hadd, hyy, psi_inv hadd, add_neg_cancel]
  have hz : Classical.choose (hsurj v) * y⁻¹ ∈ Subgroup.center ↥Q := (hker _).mp hz0
  have hkey : conjAutHom h w (Classical.choose (hsurj v))
      = (Classical.choose (hsurj v) * y⁻¹) * conjAutHom h w y := by
    conv_lhs => rw [show Classical.choose (hsurj v)
      = (Classical.choose (hsurj v) * y⁻¹) * y from by group]
    rw [map_mul, hcen w _ hz]
  rw [hkey, hadd, hz0, zero_add]

theorem phiFun_add (hadd : ∀ x y : ↥Q, ψ (x * y) = ψ x + ψ y)
    (hker : ∀ x : ↥Q, ψ x = 0 ↔ x ∈ Subgroup.center ↥Q)
    (hsurj : Function.Surjective ψ) (h : IsSplitRankOne H Q t)
    (hcen : ∀ (w : ↥(W H t)) (z : ↥Q), z ∈ Subgroup.center ↥Q → conjAutHom h w z = z)
    (w : ↥(W H t)) (v v' : F × F) :
    phiFun hsurj h w (v + v') = phiFun hsurj h w v + phiFun hsurj h w v' := by
  obtain ⟨y, hy⟩ := hsurj v
  obtain ⟨y', hy'⟩ := hsurj v'
  have hyy' : ψ (y * y') = v + v' := by rw [hadd, hy, hy']
  rw [phiFun_eq hadd hker hsurj h hcen w hyy', phiFun_eq hadd hker hsurj h hcen w hy,
    phiFun_eq hadd hker hsurj h hcen w hy']
  rw [map_mul, hadd]

theorem phiFun_smul_lam (hadd : ∀ x y : ↥Q, ψ (x * y) = ψ x + ψ y)
    (hker : ∀ x : ↥Q, ψ x = 0 ↔ x ∈ Subgroup.center ↥Q)
    (hsurj : Function.Surjective ψ) {ξ : MulAut ↥Q} {lam : Fˣ}
    (hlam : ∀ x : ↥Q, ψ (ξ x) = (lam : F) • ψ x) (h : IsSplitRankOne H Q t)
    (hcen : ∀ (w : ↥(W H t)) (z : ↥Q), z ∈ Subgroup.center ↥Q → conjAutHom h w z = z)
    (w : ↥(W H t)) (hcomm : conjAutHom h w * ξ = ξ * conjAutHom h w) (v : F × F) :
    phiFun hsurj h w ((lam : F) • v) = (lam : F) • phiFun hsurj h w v := by
  obtain ⟨y, hy⟩ := hsurj v
  have h1 : ψ (ξ y) = (lam : F) • v := by rw [hlam, hy]
  rw [phiFun_eq hadd hker hsurj h hcen w h1, phiFun_eq hadd hker hsurj h hcen w hy,
    show conjAutHom h w (ξ y) = ξ (conjAutHom h w y) from by
      have hh := congrArg (fun f : MulAut ↥Q => f y) hcomm
      rwa [MulAut.mul_apply, MulAut.mul_apply] at hh]
  rw [hlam]

theorem phiFun_smul (hadd : ∀ x y : ↥Q, ψ (x * y) = ψ x + ψ y)
    (hker : ∀ x : ↥Q, ψ x = 0 ↔ x ∈ Subgroup.center ↥Q)
    (hsurj : Function.Surjective ψ) {ξ : MulAut ↥Q} {lam : Fˣ}
    (hlam : ∀ x : ↥Q, ψ (ξ x) = (lam : F) • ψ x) (h : IsSplitRankOne H Q t)
    (hcen : ∀ (w : ↥(W H t)) (z : ↥Q), z ∈ Subgroup.center ↥Q → conjAutHom h w z = z)
    (w : ↥(W H t)) (hcomm : conjAutHom h w * ξ = ξ * conjAutHom h w)
    (hlamgen : ∀ c : F, c = 0 ∨ ∃ n : ℕ, c = (lam : F) ^ n) (c : F) (v : F × F) :
    phiFun hsurj h w (c • v) = c • phiFun hsurj h w v := by
  rcases hlamgen c with rfl | ⟨n, rfl⟩
  · rw [zero_smul]
    have hzero : phiFun hsurj h w (0 : F × F) = 0 := by
      have hh := phiFun_eq hadd hker hsurj h hcen w (y := (1 : ↥Q)) (psi_one hadd)
      simpa [psi_one hadd] using hh
    rw [hzero, zero_smul]
  · induction n with
    | zero => simp
    | succ n ih =>
        calc phiFun hsurj h w ((lam : F) ^ (n + 1) • v)
            = phiFun hsurj h w ((lam : F) • ((lam : F) ^ n • v)) := by
              rw [pow_succ', mul_smul]
          _ = (lam : F) • phiFun hsurj h w ((lam : F) ^ n • v) :=
              phiFun_smul_lam hadd hker hsurj hlam h hcen w hcomm ((lam : F) ^ n • v)
          _ = (lam : F) • ((lam : F) ^ n • phiFun hsurj h w v) := by rw [ih]
          _ = (lam : F) ^ (n + 1) • phiFun hsurj h w v := by rw [pow_succ', mul_smul]

theorem phiFun_injective (hadd : ∀ x y : ↥Q, ψ (x * y) = ψ x + ψ y)
    (hker : ∀ x : ↥Q, ψ x = 0 ↔ x ∈ Subgroup.center ↥Q)
    (hsurj : Function.Surjective ψ) (h : IsSplitRankOne H Q t)
    (hcen : ∀ (w : ↥(W H t)) (z : ↥Q), z ∈ Subgroup.center ↥Q → conjAutHom h w z = z)
    (w : ↥(W H t)) : Function.Injective (phiFun hsurj h w) := by
  intro v v' hvv'
  obtain ⟨y, hy⟩ := hsurj v
  obtain ⟨y', hy'⟩ := hsurj v'
  have e1 : ψ (conjAutHom h w y) = ψ (conjAutHom h w y') := by
    rw [← phiFun_eq hadd hker hsurj h hcen w hy,
      ← phiFun_eq hadd hker hsurj h hcen w hy', hvv']
  have e2 : ψ (conjAutHom h w y * (conjAutHom h w y')⁻¹) = 0 := by
    rw [hadd, e1, psi_inv hadd, add_neg_cancel]
  have e3 : conjAutHom h w (y * y'⁻¹) ∈ Subgroup.center ↥Q := by
    rw [map_mul, map_inv]
    exact (hker _).mp e2
  have e4 : y * y'⁻¹ ∈ Subgroup.center ↥Q := by
    have h2 : (conjAutHom h w)⁻¹ (conjAutHom h w (y * y'⁻¹)) = y * y'⁻¹ :=
      MulEquiv.apply_symm_apply _ _
    rw [← h2]
    exact mulAut_mem_center _ e3
  have e5 : ψ (y * y'⁻¹) = 0 := (hker _).mpr e4
  have hfin : ψ y = ψ y' := by
    have h6 : ψ ((y * y'⁻¹) * y') = ψ (y * y'⁻¹) + ψ y' := hadd _ _
    rw [show (y * y'⁻¹) * y' = y from by group, e5, zero_add] at h6
    exact h6
  rw [← hy, ← hy', hfin]

/-- If the action of `w ∈ W` on `V = F × F` is trivial, then `w` acts trivially on `Q`:
`A y * y⁻¹ ∈ Z(Q)` for all `y`, so `A² = 1`, and `A` has odd order. -/
theorem conjAutHom_eq_one_of_phi_id (hadd : ∀ x y : ↥Q, ψ (x * y) = ψ x + ψ y)
    (hker : ∀ x : ↥Q, ψ x = 0 ↔ x ∈ Subgroup.center ↥Q)
    (hsurj : Function.Surjective ψ) (h : IsSplitRankOne H Q t)
    (hcen : ∀ (w : ↥(W H t)) (z : ↥Q), z ∈ Subgroup.center ↥Q → conjAutHom h w z = z)
    (hzsq : ∀ z : ↥Q, z ∈ Subgroup.center ↥Q → z ^ 2 = 1)
    (w : ↥(W H t)) (hodd : Odd (orderOf (conjAutHom h w)))
    (hid : ∀ v : F × F, phiFun hsurj h w v = v) :
    conjAutHom h w = 1 := by
  have h1 : ∀ y : ↥Q, ψ (conjAutHom h w y) = ψ y := by
    intro y
    rw [← phiFun_eq hadd hker hsurj h hcen w (rfl : ψ y = ψ y)]
    exact hid (ψ y)
  have hz : ∀ y : ↥Q, conjAutHom h w y * y⁻¹ ∈ Subgroup.center ↥Q := by
    intro y
    have hh : ψ (conjAutHom h w y * y⁻¹) = 0 := by
      rw [hadd, h1 y, psi_inv hadd, add_neg_cancel]
    exact (hker _).mp hh
  have hA2 : (conjAutHom h w) ^ 2 = 1 := by
    apply MulEquiv.ext
    intro y
    set zc : ↥Q := conjAutHom h w y * y⁻¹ with hcdef
    have hy : zc ∈ Subgroup.center ↥Q := hz y
    have hty : conjAutHom h w y = zc * y := by rw [hcdef]; group
    have hsq : zc * zc = 1 := by simpa [pow_two] using hzsq zc hy
    rw [pow_two, MulAut.mul_apply, hty, map_mul, hcen w zc hy, hty, ← mul_assoc, hsq, one_mul,
      MulAut.one_apply]
  have hdvd : orderOf (conjAutHom h w) ∣ 2 := by
    rw [orderOf_dvd_iff_pow_eq_one, pow_two]; exact hA2
  have hone : orderOf (conjAutHom h w) = 1 := by
    obtain ⟨m, hm⟩ := hodd
    have h2 := Nat.le_of_dvd (by norm_num) hdvd
    omega
  exact orderOf_eq_one_iff.mp hone

end Linear

/-! ## §3. The main theorem -/

-- Route: if `W = ⊥` then `⊥` is cyclic.  Otherwise `K = Ksub H t = Kset H t` is cyclic of
-- order `q - 1` (`L6setup.Ksub_eq_Kset_of_W_ne_bot`), acting on `Q` with generator `ξ`; the pair
-- `(↥Q, ξ)` is a Suzuki 2-group of order `q³` (`Work.Higman.IsSuzuki2Grp`) satisfying
-- `Work.Higman.FpfXi ξ`.  Every `w ∈ W#` moves every `ξ`-invariant layer (if it preserved one,
-- then `orderOf w ∣ q - 1` by semiregularity on that layer modulo `Z(Q)`, whereas `hdvd` gives
-- `orderOf w ∣ q + 1`).  So `Work.Higman.typeB_of_odd_fpf` gives `IsTypeB ξ`, and
-- `Work.Higman.typeB_scalar` gives a field `F` of order `q`, a surjective additive
-- `ψ : ↥Q → F × F` with kernel `Z(Q)`, and `lam ∈ F^×` with `ψ (ξ x) = lam • ψ x`.
-- Then `W` acts on `V = F × F` by group automorphisms commuting with `⟨lam⟩ = F^×`
-- (`|K| = q - 1 = |F^×|`, and `ξ` acts faithfully on `Q / Z(Q)`), i.e. `W ≤ GL_F(V) = GL_2(F)`.
-- Eigenvectors of `w ∈ W#` correspond bijectively to invariant layers, which do not exist, so
-- the `gl2` hypothesis applies and `W` is cyclic.
theorem W_isCyclic {G : Type} [Group G] [Finite G] {H Q : Subgroup G} {t s : G}
    (hC4 : Submission.Blueprint.ChIIFourProp) (hHig : Submission.Blueprint.HigmanProp)
    (h : Work.ThmF.Lemma5.Hyp5 H Q t s) (hSuz : Submission.Blueprint.IsSuzukiTwoGroup ↥Q)
    (hcard : Nat.card ↥Q = Nat.card ↥(Work.ThmF.Q0sub H) ^ 3)
    (hsemi : ∀ w ∈ Work.ThmF.W H t, w ≠ 1 → ∀ x ∈ Q, w * x = x * w →
      x ∈ Work.ThmF.Q0sub H)
    (hdvd : Nat.card ↥(Work.ThmF.W H t) ∣ Nat.card ↥(Work.ThmF.Q0sub H) + 1)
    (gl2 : ∀ {F : Type} [Field F] [Finite F] {V : Type} [AddCommGroup V] [Module F V]
      [FiniteDimensional F V], Module.finrank F V = 2 → (A : Subgroup (V ≃ₗ[F] V)) →
      Odd (Nat.card ↥A) →
      (∀ a ∈ A, a ≠ 1 → ∀ (c : F) (v : V), v ≠ 0 → (a : V ≃ₗ[F] V) v ≠ c • v) →
      IsCyclic ↥A) :
    IsCyclic ↥(Work.ThmF.W H t) := by
  classical
  by_cases hW : W H t = ⊥
  · haveI : Subsingleton ↥(W H t) := by
      refine ⟨fun a b => Subtype.ext ?_⟩
      have ha : (a : G) = 1 := Subgroup.mem_bot.mp (by rw [← hW]; exact a.2)
      have hb : (b : G) = 1 := Subgroup.mem_bot.mp (by rw [← hW]; exact b.2)
      rw [ha, hb]
    exact isCyclic_of_subsingleton
  · obtain ⟨hKsub, hKcyc⟩ := Ksub_eq_Kset_and_cyclic_of_W_ne_bot h.sit h.split hC4 hW
    obtain ⟨k, hkK, hkgen⟩ := exists_generator_Ksub (H := H) (t := t) hKcyc
    have hkKset : k ∈ Kset H t := hKsub ▸ hkK
    have hkN : k ∈ Subgroup.normalizer (Q : Set G) :=
      h.split.normal (Ksub_le_H_hyp5 H t hkK)
    have hfpf : Work.Higman.FpfXi (conjAut k hkN) :=
      fpfXi_conjAut hC4 h hHig hSuz hcard hKsub hkK hkgen hkN
    obtain ⟨hSuz2⟩ := (Work.Higman.isSuzukiTwoGroup_iff_nonempty_isSuzuki2Grp).mp hSuz
    have hzsq : ∀ z : ↥Q, z ∈ Subgroup.center ↥Q → z ^ 2 = 1 :=
      fun z hz => ((hHig ↥Q hSuz).1 z).mp hz
    have hcen : ∀ (w : ↥(W H t)) (z : ↥Q),
        z ∈ Subgroup.center ↥Q → conjAutHom h.split w z = z :=
      fun w z hz => conjAutHom_center hC4 h hHig hSuz w z hz
    have hcomm : ∀ w : ↥(W H t),
        conjAutHom h.split w * conjAut k hkN = conjAut k hkN * conjAutHom h.split w :=
      fun w => conjAutHom_comm_k h.split hkKset hkN w
    have hoddW : Odd (Nat.card ↥(W H t)) := odd_card_W h.split
    have hoddAut : ∀ w : ↥(W H t), Odd (orderOf (conjAutHom h.split w)) := by
      intro w
      have hwo : orderOf w = orderOf (w : G) := (Subgroup.orderOf_coe w).symm
      have h1 : orderOf (conjAutHom h.split w) ∣ orderOf (w : G) := by
        rw [orderOf_dvd_iff_pow_eq_one, ← map_pow, ← hwo, pow_orderOf_eq_one, map_one]
      have h2 : orderOf (w : G) ∣ Nat.card ↥(W H t) := by
        rw [← hwo]
        exact orderOf_dvd_natCard w
      exact hoddW.of_dvd_nat (h1.trans h2)
    -- `ξ = conjAut k` is of type `B`: every `w ∈ W#` moves every `ξ`-invariant layer
    have hB : Work.Higman.IsTypeB (conjAut k hkN) := by
      obtain ⟨w0, hw0W, hw01⟩ := exists_ne_one_of_ne_bot hW
      have hw0ne : conjAutHom h.split (⟨w0, hw0W⟩ : ↥(W H t)) ≠ 1 := by
        intro hcon
        refine hw01 ?_
        have h1 : conjAutHom h.split (⟨w0, hw0W⟩ : ↥(W H t)) = conjAutHom h.split 1 := by
          rw [hcon, map_one]
        have h2 : (⟨w0, hw0W⟩ : ↥(W H t)) = 1 := conjAutHom_injective h.sit h.split h1
        simpa using congrArg (fun x : ↥(W H t) => (x : G)) h2
      have hfree : ∀ M : Subgroup ↥Q, Work.Higman.IsXiLayer (conjAut k hkN) M →
          M.map (conjAutHom h.split (⟨w0, hw0W⟩ : ↥(W H t))).toMonoidHom ≠ M := by
        intro M hM
        exact WLayerSafe.W_layer_not_preserved hC4 hHig h hSuz hcard hsemi hdvd
          (w := w0) hw0W hw01 (W_le_normalizer h.split hw0W) M hM.1 hM.2.2
      exact Work.Higman.typeB_of_odd_fpf hSuz2 hfpf (hcomm (⟨w0, hw0W⟩ : ↥(W H t)))
        (hoddAut (⟨w0, hw0W⟩ : ↥(W H t))) hw0ne hfree
    -- the scalar description of `Q / Z(Q)`
    obtain ⟨F, hF, hFint, ψ, hcardF, hψadd, hψker, hψsurj, lam, hψlam⟩ :=
      Work.Higman.typeB_scalar hSuz2 hfpf hB
    letI := hF
    letI := hFint
    haveI : Finite F := Finite.of_fintype F
    obtain ⟨-, hlamgen⟩ := orderOf_lam_eq hSuz2 hfpf hψadd hψker hψsurj hcardF hψlam
    haveI : Module.Finite F (F × F) := Module.Finite.of_finite
    -- the linear action of `W` on `V = F × F`
    let phiLin : ↥(W H t) → ((F × F) →ₗ[F] (F × F)) := fun w =>
      { toFun := phiFun hψsurj h.split w
        map_add' := phiFun_add hψadd hψker hψsurj h.split hcen w
        map_smul' := phiFun_smul hψadd hψker hψsurj hψlam h.split hcen w (hcomm w) hlamgen }
    let phiHom : ↥(W H t) →* ((F × F) ≃ₗ[F] (F × F)) :=
      { toFun := fun w => LinearEquiv.ofBijective (phiLin w)
          ⟨phiFun_injective hψadd hψker hψsurj h.split hcen w,
           (LinearMap.injective_iff_surjective_of_finrank_eq_finrank
              (K := F) (V := F × F) (V₂ := F × F) rfl).mp
             (phiFun_injective hψadd hψker hψsurj h.split hcen w)⟩
        map_one' := by
          apply LinearEquiv.ext
          intro v
          show phiFun hψsurj h.split 1 v = v
          obtain ⟨y, hy⟩ := hψsurj v
          rw [phiFun_eq hψadd hψker hψsurj h.split hcen 1 hy, map_one, MulAut.one_apply, hy]
        map_mul' := fun a b => by
          apply LinearEquiv.ext
          intro v
          show phiFun hψsurj h.split (a * b) v
            = phiFun hψsurj h.split a (phiFun hψsurj h.split b v)
          obtain ⟨y, hy⟩ := hψsurj v
          rw [phiFun_eq hψadd hψker hψsurj h.split hcen (a * b) hy, map_mul, MulAut.mul_apply,
            phiFun_eq hψadd hψker hψsurj h.split hcen b hy,
            phiFun_eq hψadd hψker hψsurj h.split hcen a
              (show ψ (conjAutHom h.split b y) = ψ (conjAutHom h.split b y) from rfl)] }
    have hphi_eq : ∀ (w : ↥(W H t)) (x : ↥Q),
        phiHom w (ψ x) = ψ (conjAutHom h.split w x) :=
      fun w x => phiFun_eq hψadd hψker hψsurj h.split hcen w (rfl : ψ x = ψ x)
    -- `φ` is injective: it separates the elements of `W`
    have hphi_inj : Function.Injective phiHom := by
      intro a b hab
      have h1 : phiHom (a * b⁻¹) = 1 := by
        rw [map_mul, map_inv, hab]
        exact mul_inv_cancel _
      have h2 : ∀ v : F × F, phiFun hψsurj h.split (a * b⁻¹) v = v := by
        intro v
        show (phiHom (a * b⁻¹)) v = v
        rw [h1]
        rfl
      have h3 := conjAutHom_eq_one_of_phi_id hψadd hψker hψsurj h.split hcen hzsq
        (a * b⁻¹) (hoddAut _) h2
      exact mul_inv_eq_one.mp (conjAutHom_injective h.sit h.split (by rw [h3, map_one]))
    -- no element of `W#` has an eigenvalue on `V`
    have hnoeigen : ∀ a ∈ phiHom.range, a ≠ 1 → ∀ (c : F) (v : F × F), v ≠ 0 →
        a v ≠ c • v := by
      intro a ha ha1 c v hv hcon
      obtain ⟨w, hw⟩ := MonoidHom.mem_range.mp ha
      subst hw
      have hLmap : Submodule.map (phiHom w).toLinearMap (Submodule.span F ({v} : Set (F × F)))
          ≤ Submodule.span F ({v} : Set (F × F)) := by
        rw [Submodule.map_span, Set.image_singleton, Submodule.span_le]
        intro x hx
        rw [Set.mem_singleton_iff] at hx
        subst hx
        show (phiHom w) v ∈ (F ∙ v : Submodule F (F × F))
        rw [Submodule.mem_span_singleton]
        exact ⟨c, hcon.symm⟩
      obtain ⟨M, hMmem, hMlayer⟩ :=
        psi_preimage_isXiLayer ψ hψadd hψker hψsurj hcardF hψlam hv
      have hMle : M.map (conjAutHom h.split w).toMonoidHom ≤ M := by
        intro y hy
        obtain ⟨x, hxM, rfl⟩ := Subgroup.mem_map.mp hy
        refine (hMmem _).mpr ?_
        show ψ (conjAutHom h.split w x) ∈ Submodule.span F ({v} : Set (F × F))
        rw [← hphi_eq w x]
        exact hLmap (Submodule.mem_map.mpr ⟨ψ x, (hMmem x).mp hxM, rfl⟩)
      have hcardmap : Nat.card ↥(M.map (conjAutHom h.split w).toMonoidHom) = Nat.card ↥M :=
        Subgroup.card_map_of_injective (MulEquiv.injective _)
      have hMeq : M.map (conjAutHom h.split w).toMonoidHom = M :=
        Subgroup.eq_of_le_of_card_ge hMle (le_of_eq hcardmap.symm)
      have hw1G : (w : G) ≠ 1 := fun hw1' => ha1 (by
        rw [show w = 1 from Subtype.ext hw1', map_one])
      have hne := WLayerSafe.W_layer_not_preserved hC4 hHig h hSuz hcard hsemi hdvd w.2 hw1G
        (W_le_normalizer h.split w.2) M hMlayer.1 hMlayer.2.2
      exact hne hMeq
    -- apply the `GL₂` hypothesis to the image of `W` and transport cyclicity back
    have hoddA : Odd (Nat.card ↥phiHom.range) := by
      rw [← Nat.card_congr (MonoidHom.ofInjective hphi_inj).toEquiv]
      exact hoddW
    have hfr : Module.finrank F (F × F) = 2 := by
      rw [Module.finrank_prod, Module.finrank_self]
    have hcyc : IsCyclic ↥phiHom.range :=
      gl2 (F := F) (V := F × F) hfr phiHom.range hoddA hnoeigen
    haveI := hcyc
    exact isCyclic_of_surjective
      ((MonoidHom.ofInjective hphi_inj).symm : ↥phiHom.range →* ↥(W H t))
      (MulEquiv.surjective _)

end Work.ThmF.ChV12
