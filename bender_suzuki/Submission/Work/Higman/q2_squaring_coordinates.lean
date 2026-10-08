import Mathlib
import Submission.Work.Higman.Defs
import Submission.Work.Higman.Basic
import Submission.Work.Higman.exists_singer_iso
import Submission.Work.Higman.monomial_form
import Submission.Work.Higman.gcd_two_pow
import Submission.Work.Higman.orderOf_frobeniusEquiv_pow
import Submission.Work.Higman.exists_linearEquiv_monomial
import Submission.Work.Higman.no_equivariant_linearEquiv

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.style.haveILetI false

open scoped commutatorElement

namespace Work.Higman

open LeanEval.GroupTheory.Defs

/-! ## Elementary helpers -/

/-- Every element of `ZMod 2` is `0` or `1`. -/
lemma zmod_two_eq_zero_or_one (c : ZMod 2) : c = 0 ∨ c = 1 := by revert c; decide

/-- In a `ZMod 2`-module, `a + b + d + a + b = d`. -/
lemma add_add_add_self {M : Type*} [AddCommGroup M] [Module (ZMod 2) M] (a b d : M) :
    (a + b + d) + a + b = d := by
  have h2 : ∀ y : M, y + y = 0 := by
    intro y
    rw [← one_smul (ZMod 2) y, ← one_smul (ZMod 2) y, ← add_smul]
    have h1 : (1 + 1 : ZMod 2) = 0 := by decide
    rw [h1, zero_smul]
  calc (a + b + d) + a + b = (a + a) + (b + b) + d := by abel
    _ = 0 + 0 + d := by rw [h2 a, h2 b]
    _ = d := by simp

/-- The centre is mapped to itself by every automorphism. -/
theorem center_map_mulAut {P : Type} [Group P] (φ : MulAut P) :
    (Subgroup.center P).map (φ : MulAut P).toMonoidHom = Subgroup.center P :=
  Subgroup.characteristic_iff_map_eq.mp (inferInstance : (Subgroup.center P).Characteristic)
    (φ : P ≃* P)

/-- A multiplicative equivalence between exponent-`2` groups, viewed additively. -/
noncomputable def mulEquivToAddEquiv {G H : Type*} [Monoid G] [Monoid H] (e : G ≃* H) :
    Additive G ≃+ Additive H where
  toFun := fun x => Additive.ofMul (e x.toMul)
  invFun := fun y => Additive.ofMul (e.symm y.toMul)
  left_inv := by intro x; simp
  right_inv := by intro y; simp
  map_add' := by
    intro x y
    show Additive.ofMul (e (x + y).toMul) =
      Additive.ofMul (e x.toMul) + Additive.ofMul (e y.toMul)
    rw [toMul_add, map_mul, ofMul_mul]

/-- An additive equivalence of `ZMod 2`-modules is automatically linear. -/
noncomputable def zmodLinearEquivOfAddEquiv {M N : Type*} [AddCommGroup M] [AddCommGroup N]
    [Module (ZMod 2) M] [Module (ZMod 2) N] (e : M ≃+ N) : M ≃ₗ[ZMod 2] N where
  toFun := e
  invFun := e.symm
  map_add' := e.map_add
  map_smul' := fun c x => by
    rcases zmod_two_eq_zero_or_one c with h | h <;> subst h <;> simp
  left_inv := e.left_inv
  right_inv := e.right_inv

/-- `x * y * x⁻¹ = [x, y] * y`. -/
theorem mul_mul_inv_eq_commutator_mul {G : Type*} [Group G] (x y : G) :
    x * y * x⁻¹ = ⁅x, y⁆ * y := by
  rw [commutatorElement_def]; group

/-- In a group whose commutators are central, everything commutes with every commutator. -/
theorem commutator_central_comm {G : Type*} [Group G]
    (hZ : ⁅(⊤ : Subgroup G), ⊤⁆ ≤ Subgroup.center G) (x y z : G) :
    z * ⁅x, y⁆ = ⁅x, y⁆ * z :=
  Subgroup.mem_center_iff.mp
    (hZ (Subgroup.commutator_mem_commutator (Subgroup.mem_top x) (Subgroup.mem_top y))) z

/-- Class two: `[x * y, z] = [x, z] * [y, z]`. -/
theorem commutator_mul_left_class_two {G : Type*} [Group G]
    (hZ : ⁅(⊤ : Subgroup G), ⊤⁆ ≤ Subgroup.center G) (x y z : G) :
    ⁅x * y, z⁆ = ⁅x, z⁆ * ⁅y, z⁆ := by
  have hcy : ∀ w : G, w * ⁅y, z⁆ = ⁅y, z⁆ * w := commutator_central_comm hZ y z
  have hcx : ∀ w : G, w * ⁅x, z⁆ = ⁅x, z⁆ * w := commutator_central_comm hZ x z
  have h1 : x * z * x⁻¹ = ⁅x, z⁆ * z := mul_mul_inv_eq_commutator_mul x z
  have h2 : y * z * y⁻¹ = ⁅y, z⁆ * z := mul_mul_inv_eq_commutator_mul y z
  rw [commutatorElement_def]
  rw [show x * y * z * (x * y)⁻¹ * z⁻¹ = x * (y * z * y⁻¹) * x⁻¹ * z⁻¹ by group]
  rw [h2]
  rw [show x * (⁅y, z⁆ * z) * x⁻¹ * z⁻¹ = (x * ⁅y, z⁆) * (z * x⁻¹) * z⁻¹ by group]
  rw [hcy x]
  rw [show (⁅y, z⁆ * x) * (z * x⁻¹) * z⁻¹ = ⁅y, z⁆ * (x * z * x⁻¹) * z⁻¹ by group]
  rw [h1]
  rw [show ⁅y, z⁆ * (⁅x, z⁆ * z) * z⁻¹ = ⁅y, z⁆ * ⁅x, z⁆ by group]
  rw [hcx ⁅y, z⁆]

/-- Class two: `[z, x * y] = [z, x] * [z, y]`. -/
theorem commutator_mul_right_class_two {G : Type*} [Group G]
    (hZ : ⁅(⊤ : Subgroup G), ⊤⁆ ≤ Subgroup.center G) (x y z : G) :
    ⁅z, x * y⁆ = ⁅z, x⁆ * ⁅z, y⁆ := by
  have h1 : ⁅z, x * y⁆ = ⁅x * y, z⁆⁻¹ := by rw [← commutatorElement_inv]
  rw [h1, commutator_mul_left_class_two hZ x y z, mul_inv_rev, commutatorElement_inv,
    commutatorElement_inv]
  exact (commutator_central_comm hZ z y ⁅z, x⁆).symm

/-- A central element commutes out of a commutator on the left. -/
theorem commutator_eq_one_of_mem_center_left {G : Type*} [Group G] {z : G}
    (hz : z ∈ Subgroup.center G) (x : G) : ⁅z, x⁆ = 1 := by
  rw [commutatorElement_def, ← Subgroup.mem_center_iff.mp hz x]
  group

/-- A central element commutes out of a commutator on the right. -/
theorem commutator_eq_one_of_mem_center_right {G : Type*} [Group G] {z : G}
    (hz : z ∈ Subgroup.center G) (x : G) : ⁅x, z⁆ = 1 := by
  rw [commutatorElement_def, Subgroup.mem_center_iff.mp hz x]
  group

/-- **The abstract `𝔽₂`-linear core of the Singer-coordinate theorem.**

Two `𝔽₂`-vector spaces of order `2 ^ n` carrying free automorphisms `ξV`, `ξW` of order `2 ^ n - 1`
(so both are cyclic of order `2 ^ n - 1`), an anisotropic `ξ`-equivariant quadratic map
`Q : V → W` with biadditive polar form, and *no* `ξ`-equivariant linear isomorphism `V ≃ W`:
then `Q` is the twisted product `Ψ (Q v) = Φ v * θ (Φ v)` in suitable `𝔽₂`-linear coordinates,
with `θ ≠ 1` of odd order. -/
theorem q2_linear_core_aux {V W : Type}
    [AddCommGroup V] [Module (ZMod 2) V] [Finite V]
    [AddCommGroup W] [Module (ZMod 2) W] [Finite W]
    (n : ℕ) (hn : 0 < n) (hVn : Nat.card V = 2 ^ n) (hWn : Nat.card W = 2 ^ n)
    (ξV : V ≃ₗ[ZMod 2] V) (ξW : W ≃ₗ[ZMod 2] W)
    (hordV : orderOf ξV = 2 ^ n - 1) (hordW : orderOf ξW = 2 ^ n - 1)
    (hfreeV : ∀ v : V, ξV v = v → v = 0) (hfreeW : ∀ w : W, ξW w = w → w = 0)
    (Q : V → W) (hQ0 : Q 0 = 0) (hQne : ∀ v : V, v ≠ 0 → Q v ≠ 0)
    (hQeq : ∀ v : V, Q (ξV v) = ξW (Q v))
    (hadd1 : ∀ a a' c : V, Q (a + a' + c) + Q (a + a') + Q c =
      (Q (a + c) + Q a + Q c) + (Q (a' + c) + Q a' + Q c))
    (hadd2 : ∀ a c c' : V, Q (a + (c + c')) + Q a + Q (c + c') =
      (Q (a + c) + Q a + Q c) + (Q (a + c') + Q a + Q c'))
    (hnoiso : ¬ ∃ σ : V ≃ₗ[ZMod 2] W, ∀ v : V, σ (ξV v) = ξW (σ v)) :
    ∃ (θ : GaloisField 2 n ≃+* GaloisField 2 n)
      (Φ : V ≃ GaloisField 2 n) (Ψ : W ≃ GaloisField 2 n),
      θ ≠ RingEquiv.refl _ ∧ Odd (orderOf θ) ∧
      (∀ v w : V, Φ (v + w) = Φ v + Φ w) ∧
      (∀ z w : W, Ψ (z + w) = Ψ z + Ψ w) ∧
      (∀ v : V, Ψ (Q v) = Φ v * θ (Φ v)) := by
  classical
  obtain ⟨φ, ν, hνord, hφ⟩ := exists_singer_iso hn hVn ξV hordV hfreeV
  obtain ⟨ψ, lam, hlamord, hψ⟩ := exists_singer_iso hn hWn ξW hordW hfreeW
  -- the coordinate expression of `Q`
  let Qc : GaloisField 2 n → GaloisField 2 n := fun α => ψ (Q (φ.symm α))
  have hQc0 : Qc 0 = 0 := by
    show ψ (Q (φ.symm 0)) = 0
    rw [map_zero, hQ0, map_zero]
  have hQcne : ∀ α, α ≠ 0 → Qc α ≠ 0 := by
    intro α hα h0
    have h0' : ψ (Q (φ.symm α)) = 0 := h0
    have h1 : φ.symm α = 0 := by
      by_contra hne
      exact hQne (φ.symm α) hne (ψ.injective (by rw [h0', map_zero]))
    have h3 : α = 0 := by
      have := congrArg φ h1
      simpa using this
    exact hα h3
  have hQcξ : ∀ α, Qc ((ν : GaloisField 2 n) * α) = (lam : GaloisField 2 n) * Qc α := by
    intro α
    have h1 : φ.symm ((ν : GaloisField 2 n) * α) = ξV (φ.symm α) := by
      apply φ.injective
      rw [LinearEquiv.apply_symm_apply, hφ, LinearEquiv.apply_symm_apply]
    show ψ (Q (φ.symm ((ν : GaloisField 2 n) * α)))
      = (lam : GaloisField 2 n) * ψ (Q (φ.symm α))
    rw [h1, hQeq, hψ]
  have hQcadd1 : ∀ a a' c : GaloisField 2 n,
      Qc (a + a' + c) + Qc (a + a') + Qc c =
        (Qc (a + c) + Qc a + Qc c) + (Qc (a' + c) + Qc a' + Qc c) := by
    intro a a' c
    have h := congrArg ψ (hadd1 (φ.symm a) (φ.symm a') (φ.symm c))
    have e1 : φ.symm (a + a' + c) = φ.symm a + φ.symm a' + φ.symm c := by
      rw [map_add, map_add]
    have e2 : φ.symm (a + a') = φ.symm a + φ.symm a' := map_add _ _ _
    have e3 : φ.symm (a + c) = φ.symm a + φ.symm c := map_add _ _ _
    have e4 : φ.symm (a' + c) = φ.symm a' + φ.symm c := map_add _ _ _
    simpa [Qc, map_add, e1, e2, e3, e4] using h
  have hQcadd2 : ∀ a c c' : GaloisField 2 n,
      Qc (a + (c + c')) + Qc a + Qc (c + c') =
        (Qc (a + c) + Qc a + Qc c) + (Qc (a + c') + Qc a + Qc c') := by
    intro a c c'
    have h := congrArg ψ (hadd2 (φ.symm a) (φ.symm c) (φ.symm c'))
    have e1 : φ.symm (a + (c + c')) = φ.symm a + (φ.symm c + φ.symm c') := by
      rw [map_add, map_add]
    have e2 : φ.symm (c + c') = φ.symm c + φ.symm c' := map_add _ _ _
    have e3 : φ.symm (a + c) = φ.symm a + φ.symm c := map_add _ _ _
    have e4 : φ.symm (a + c') = φ.symm a + φ.symm c' := map_add _ _ _
    simpa [Qc, map_add, e1, e2, e3, e4] using h
  -- ## Frobenius powers
  have hfrob : ∀ (k : ℕ) (α : GaloisField 2 n),
      ((frobeniusEquiv (GaloisField 2 n) 2) ^ k) α = α ^ 2 ^ k := by
    intro k
    induction k with
    | zero => intro α; simp
    | succ k ih =>
      intro α
      have h1 : ((frobeniusEquiv (GaloisField 2 n) 2) ^ (k + 1)) α
          = ((frobeniusEquiv (GaloisField 2 n) 2) ^ k)
              ((frobeniusEquiv (GaloisField 2 n) 2) α) := by
        rw [pow_succ]; rfl
      rw [h1, ih ((frobeniusEquiv (GaloisField 2 n) 2) α), frobeniusEquiv_apply, frobenius_def,
        ← pow_mul, show 2 * 2 ^ k = 2 ^ (k + 1) by rw [mul_comm, ← pow_succ]]
  -- ## Gorenstein–Thompson gives `ν ≠ lam ^ (2 ^ s)`
  have hnotconj : ∀ s : ℕ, (ν : GaloisField 2 n) ≠ (lam : GaloisField 2 n) ^ 2 ^ s := by
    intro s hs
    let t : ℕ := n - s % n
    have hνt : (ν : GaloisField 2 n) ^ (2 ^ t) = (lam : GaloisField 2 n) := by
      have hsadd : s + t = n * (s / n + 1) := by
        have h1 : s = n * (s / n) + s % n := (Nat.div_add_mod s n).symm
        have h2 : s % n < n := Nat.mod_lt s hn
        have h3 : t = n - s % n := rfl
        have h4 : n * (s / n + 1) = n * (s / n) + n := by rw [mul_add, mul_one]
        rw [h3, h4]
        omega
      have hlam1 : (lam : GaloisField 2 n) ^ (2 ^ n - 1) = 1 := by
        have huo : orderOf (lam : GaloisField 2 n) = 2 ^ n - 1 := by
          rw [orderOf_units]; exact hlamord
        rw [← huo]; exact pow_orderOf_eq_one _
      have hlampow : (lam : GaloisField 2 n) ^ (2 ^ (s + t)) = (lam : GaloisField 2 n) := by
        have hdvd : (2 ^ n - 1) ∣ (2 ^ (s + t) - 1) := by
          rw [hsadd, pow_mul]
          exact Nat.sub_one_dvd_pow_sub_one (2 ^ n) (s / n + 1)
        obtain ⟨c, hc⟩ := hdvd
        have hexp : 2 ^ (s + t) = (2 ^ n - 1) * c + 1 := by
          rw [← hc]
          exact (Nat.sub_add_cancel (Nat.one_le_two_pow (n := s + t))).symm
        rw [hexp, pow_add, pow_mul, hlam1, one_pow, one_mul, pow_one]
      rw [hs, ← pow_mul, ← pow_add]
      exact hlampow
    let χ : GaloisField 2 n ≃ₗ[ZMod 2] GaloisField 2 n :=
      zmodLinearEquivOfAddEquiv
        { (frobeniusEquiv (GaloisField 2 n) 2 ^ t).toEquiv with
          map_add' := fun a b => (frobeniusEquiv (GaloisField 2 n) 2 ^ t).map_add a b }
    have hχlin : ∀ α, χ ((ν : GaloisField 2 n) * α) = (lam : GaloisField 2 n) * χ α := by
      intro α
      change ((frobeniusEquiv (GaloisField 2 n) 2) ^ t) ((ν : GaloisField 2 n) * α)
        = (lam : GaloisField 2 n) * ((frobeniusEquiv (GaloisField 2 n) 2) ^ t) α
      rw [hfrob t, mul_pow, hνt, ← hfrob t]
    have hsymm : ∀ y : GaloisField 2 n,
        ψ.symm ((lam : GaloisField 2 n) * y) = ξW (ψ.symm y) := by
      intro y
      apply ψ.injective
      rw [LinearEquiv.apply_symm_apply, hψ, LinearEquiv.apply_symm_apply]
    refine hnoiso ⟨φ.trans (χ.trans ψ.symm), fun v => ?_⟩
    have h1 : χ (φ (ξV v)) = (lam : GaloisField 2 n) * χ (φ v) := by
      rw [hφ v]; exact hχlin (φ v)
    have h2 : (φ.trans (χ.trans ψ.symm)) (ξV v) = ψ.symm (χ (φ (ξV v))) := by
      rw [LinearEquiv.trans_apply, LinearEquiv.trans_apply]
    have h3 : (φ.trans (χ.trans ψ.symm)) v = ψ.symm (χ (φ v)) := by
      rw [LinearEquiv.trans_apply, LinearEquiv.trans_apply]
    rw [h2, h3, h1, hsymm]
  -- ## Higman's Lemma 11 (linear algebra)
  obtain ⟨i, j, hij, hjn, hνlam, c, hc, hQcm⟩ :=
    monomial_form hn ν lam hνord hlamord hnotconj Qc hQc0 hQcne hQcadd1 hQcadd2 hQcξ
  -- the coprimality coming from primitivity of `ν`, `lam`
  have hcop : (2 ^ (j - i) + 1).Coprime (2 ^ n - 1) := by
    rw [Nat.coprime_iff_gcd_eq_one, Nat.gcd_comm]
    have hNpos : 0 < 2 ^ n - 1 := by
      have h2 : 1 < 2 ^ n := Nat.one_lt_pow (by omega) (by norm_num)
      omega
    have huo : orderOf ((ν : GaloisField 2 n)) = 2 ^ n - 1 := by
      rw [orderOf_units]; exact hνord
    have h3 : orderOf ((ν : (GaloisField 2 n)ˣ) ^ (2 ^ i + 2 ^ j))
        = (2 ^ n - 1) / (2 ^ n - 1).gcd (2 ^ i + 2 ^ j) := by
      rw [orderOf_pow, hνord]
    have h4 : orderOf ((ν : (GaloisField 2 n)ˣ) ^ (2 ^ i + 2 ^ j)) = 2 ^ n - 1 := by
      rw [← orderOf_units, Units.val_pow_eq_pow_val, hνlam, orderOf_units]
      exact hlamord
    have h2 : (2 ^ n - 1) / (2 ^ n - 1).gcd (2 ^ i + 2 ^ j) = 2 ^ n - 1 := by
      rw [← h3]; exact h4
    have hdiv : (2 ^ n - 1).gcd (2 ^ i + 2 ^ j) ∣ 2 ^ n - 1 := Nat.gcd_dvd_left _ _
    have hg1 : (2 ^ n - 1).gcd (2 ^ i + 2 ^ j) = 1 := by
      set g := (2 ^ n - 1).gcd (2 ^ i + 2 ^ j) with hg'
      have hdiv' : g ∣ 2 ^ n - 1 := by rw [hg']; exact Nat.gcd_dvd_left _ _
      have h2' : (2 ^ n - 1) / g = 2 ^ n - 1 := h2
      have hfinal : g * (2 ^ n - 1) = 1 * (2 ^ n - 1) := by
        rw [one_mul]
        conv_lhs => rw [← h2']
        exact Nat.mul_div_cancel' hdiv'
      exact Nat.eq_of_mul_eq_mul_right hNpos hfinal
    have h2ij : 2 ^ i + 2 ^ j = 2 ^ i * (2 ^ (j - i) + 1) := by
      rw [mul_add, mul_one, ← pow_add, Nat.add_sub_of_le (le_of_lt hij), add_comm]
    refine Nat.dvd_one.mp ?_
    have h1 : (2 ^ n - 1).gcd (2 ^ (j - i) + 1) ∣ (2 ^ n - 1).gcd (2 ^ i + 2 ^ j) := by
      rw [h2ij]
      exact Nat.dvd_gcd (Nat.gcd_dvd_left _ _) (Dvd.dvd.mul_left (Nat.gcd_dvd_right _ _) _)
    rw [hg1] at h1
    exact h1
  obtain ⟨φ', hφ'⟩ := exists_linearEquiv_monomial hij hjn hcop c hc Qc hQcm
  -- ## assembly
  let θ : GaloisField 2 n ≃+* GaloisField 2 n := (frobeniusEquiv (GaloisField 2 n) 2) ^ (j - i)
  refine ⟨θ, φ.trans φ', ψ, ?_, ?_, ?_, ?_, ?_⟩
  · intro hθ
    have h1 : orderOf θ = 1 := by rw [hθ]; exact orderOf_one
    have hlt : j - i < n := lt_of_le_of_lt (Nat.sub_le j i) hjn
    have hpos : 0 < j - i := Nat.sub_pos_of_lt hij
    rw [show orderOf θ = n / n.gcd (j - i) from orderOf_frobeniusEquiv_pow n (j - i) hn] at h1
    have h2 : n = n.gcd (j - i) := by
      have hdiv : n.gcd (j - i) ∣ n := Nat.gcd_dvd_left n (j - i)
      calc n = n.gcd (j - i) * (n / n.gcd (j - i)) := (Nat.mul_div_cancel' hdiv).symm
        _ = n.gcd (j - i) * 1 := by rw [h1]
        _ = n.gcd (j - i) := mul_one _
    have h3 : n.gcd (j - i) ≤ j - i := Nat.le_of_dvd hpos (Nat.gcd_dvd_right n (j - i))
    omega
  · rw [show orderOf θ = n / n.gcd (j - i) from orderOf_frobeniusEquiv_pow n (j - i) hn]
    exact (gcd_two_pow n (j - i) hn).mp (Nat.coprime_iff_gcd_eq_one.mp hcop.symm)
  · intro v w
    show φ' (φ (v + w)) = φ' (φ v) + φ' (φ w)
    rw [map_add, map_add]
  · intro z w
    show ψ (z + w) = ψ z + ψ w
    rw [map_add]
  · intro v
    have h1 : Qc (φ v) = ψ (Q v) := by
      show ψ (Q (φ.symm (φ v))) = ψ (Q v)
      rw [LinearEquiv.symm_apply_apply]
    have h2 : θ ((φ.trans φ') v) = ((φ.trans φ') v) ^ 2 ^ (j - i) := hfrob (j - i) _
    have h5 : (φ.trans φ') v = φ' (φ v) := LinearEquiv.trans_apply v
    show ψ (Q v) = (φ.trans φ') v * θ ((φ.trans φ') v)
    rw [← h1, hφ' (φ v), h2, h5, pow_add, pow_one]

/-- **Higman (1963), Lemma 11, order-`q ^ 2` case: Singer coordinates for the squaring map.**

Let `P` be a Suzuki 2-group of order `q ^ 2` (`q = |Z(P)|`) in which every square is central and
`Z(P) = Ω₁(P)`, and suppose some `ξ ∈ Aut P` has order `|Invol P| = q - 1` and permutes the
involutions transitively (this is `Work.Higman.xi_regular`).  Then the quotient `P ⧸ Z(P)` and the
centre `Z(P)` can both be given the structure of the field `GF(2 ^ n)` (`q = 2 ^ n`), in such a way
that the squaring map becomes the "twisted product" `α ↦ α * θ α` for a field automorphism `θ ≠ 1`
of odd order.

Route.  Since `Z(P) = Ω₁(P)` and `|P| = |Z(P)| ^ 2`, one has `|P ⧸ Z(P)| = |Z(P)| = q = 2 ^ n`.
`ξ` has order `|Invol P| = |Ω₁(P)| - 1 = q - 1` and acts freely on `P \ {1}` (a nontrivial `ξ ^ k`
fixing `x ≠ 1` fixes the involution of `⟨x⟩`; `⟨ξ⟩` acts regularly on the involutions because it is
transitive of order `|Invol P|`).  Consequently `ξ` induces
* on `V = P ⧸ Z(P)`: a linear automorphism of order `q - 1` acting freely on `V \ {0}`
  (if `ξ ^ k x = x * z` with `z ∈ Z(P) = Ω₁(P)` then `ξ ^ k (x ^ 2) = x ^ 2` with `x ^ 2` a
  nonidentity involution, so `ξ ^ k = 1`);
* on `W = Z(P) = Ω₁(P)`: an automorphism of order `q - 1`, transitive on `W \ {0}`.
`Work.Higman.exists_singer_iso` then gives `𝔽₂`-linear `Φ : V ≃ GF(2^n)`, `Ψ : W ≃ GF(2^n)` with
`ξ` acting as multiplication by primitive elements `ν`, `λ`.  The squaring map `Q : V → W`
(well defined by `hb` and `hZ`) is `ξ`-equivariant and anisotropic, and its polar form
`Δ (v,w) = Q (v + w) + Q v + Q w` is the commutator form, biadditive because `P` has class 2.
In the coordinates `Φ, Ψ` it satisfies the hypotheses of `Work.Higman.monomial_form`; the extra
hypothesis `λ ≠ ν ^ (2 ^ s)` needed there is Gorenstein–Thompson
(`Work.Higman.no_equivariant_linearEquiv` applied to the alternating `ξ`-equivariant pairing
`β (v,w) = [x_v, x_w]`, which is nonzero because `P` is nonabelian).
Thus `Q α = c * α ^ (2 ^ i + 2 ^ j)`, `i < j < n`, `ν ^ (2 ^ i + 2 ^ j) = λ`; since `ν, λ` are
primitive, `gcd (2 ^ (j - i) + 1, 2 ^ n - 1) = 1` (`Work.Higman.gcd_two_pow`), and
`Work.Higman.exists_linearEquiv_monomial` changes `Φ` so that `Q` becomes `α ↦ α * θ α` with
`θ = (frobeniusEquiv _ 2) ^ (j - i)`.  Finally `θ ≠ 1` because `0 < j - i < n`, and
`Odd (orderOf θ)` by `gcd_two_pow` with `Work.Higman.orderOf_frobeniusEquiv_pow`. -/
theorem q2_squaring_coordinates {P : Type} [Group P] [Finite P]
    (h : IsSuzuki2Grp P) (hcard : Nat.card P = Nat.card ↥(Subgroup.center P) ^ 2)
    (hb : ∀ x : P, x ^ 2 ∈ Subgroup.center P)
    (hZ : Subgroup.center P = omega1 P)
    (hreg : ∃ ξ : MulAut P, orderOf ξ = (Invol P).ncard ∧
      ∀ x y : P, orderOf x = 2 → orderOf y = 2 → ∃ k : ℕ, (ξ ^ k) x = y) :
    ∃ (n : ℕ) (θ : GaloisField 2 n ≃+* GaloisField 2 n)
      (Φ : (P ⧸ Subgroup.center P) ≃ GaloisField 2 n)
      (Ψ : ↥(Subgroup.center P) ≃ GaloisField 2 n),
      Nat.card ↥(Subgroup.center P) = 2 ^ n ∧ θ ≠ RingEquiv.refl _ ∧ Odd (orderOf θ) ∧
      (∀ v w : P ⧸ Subgroup.center P, Φ (v * w) = Φ v + Φ w) ∧
      (∀ z w : ↥(Subgroup.center P), Ψ (z * w) = Ψ z + Ψ w) ∧
      (∀ x : P, Ψ ⟨x ^ 2, hb x⟩ = Φ (QuotientGroup.mk x) * θ (Φ (QuotientGroup.mk x))) := by
  classical
  obtain ⟨ξ, hξord, hξtrans⟩ := hreg
  -- ## 1. Cardinal arithmetic
  obtain ⟨n, hn_omega⟩ := h.exists_card_omega1_eq_two_pow
  have hZcard : Nat.card ↥(Subgroup.center P) = 2 ^ n := by rw [hZ]; exact hn_omega
  have hInvol : (Invol P).ncard = 2 ^ n - 1 := by
    have h1 : (Invol P).ncard + 1 = 2 ^ n := by rw [← hn_omega]; exact (h.card_omega1).symm
    omega
  have hξord' : orderOf ξ = 2 ^ n - 1 := hξord.trans hInvol
  have hn2 : 2 ≤ n := by
    have h4 : 4 ≤ 2 ^ n := by rw [← hn_omega]; exact h.omega1_card_ge_four
    by_contra hc
    push_neg at hc
    interval_cases n <;> norm_num at h4
  have hnpos : 0 < n := by omega
  have hpow4 : 4 ≤ 2 ^ n := Nat.pow_le_pow_right (show 0 < 2 by norm_num) hn2
  -- ## 2. the stabiliser of an involution inside `⟨ξ⟩` is trivial
  have hstab : ∀ (u : P) (k : ℕ), orderOf u = 2 → (ξ ^ k) u = u → ξ ^ k = 1 := by
    intro u k hu hfix
    have horb : (MulAction.orbit (Subgroup.zpowers ξ) u : Set P) = Invol P := by
      ext z
      rw [MulAction.mem_orbit_iff, mem_Invol]
      constructor
      · rintro ⟨g, rfl⟩
        show orderOf (g • u) = 2
        rw [show g • u = (g : MulAut P) u from rfl, MulEquiv.orderOf_eq, hu]
      · intro hz
        obtain ⟨j, hj⟩ := hξtrans u z hu hz
        exact ⟨⟨ξ ^ j, Subgroup.pow_mem (Subgroup.zpowers ξ) (Subgroup.mem_zpowers ξ) j⟩, hj⟩
    have hoscard : Nat.card ↥(MulAction.orbit (Subgroup.zpowers ξ) u) = (Invol P).ncard := by
      rw [Nat.card_coe_set_eq, horb]
    have hos : Nat.card ↥(MulAction.orbit (Subgroup.zpowers ξ) u) *
        Nat.card ↥(MulAction.stabilizer (Subgroup.zpowers ξ) u) = orderOf ξ := by
      have hh := Nat.card_congr (MulAction.orbitProdStabilizerEquivGroup (Subgroup.zpowers ξ) u)
      rwa [Nat.card_prod, Nat.card_zpowers] at hh
    have hstab1 : Nat.card ↥(MulAction.stabilizer (Subgroup.zpowers ξ) u) = 1 := by
      rw [hoscard, hξord] at hos
      have hpos : 0 < (Invol P).ncard := by
        rw [hInvol]
        have h1 : 1 < 2 ^ n := Nat.one_lt_pow (by omega) (by norm_num)
        omega
      exact Nat.eq_of_mul_eq_mul_left hpos (by rw [mul_one]; exact hos)
    have hmem : (⟨ξ ^ k, Subgroup.pow_mem (Subgroup.zpowers ξ) (Subgroup.mem_zpowers ξ) k⟩ :
        Subgroup.zpowers ξ) ∈ MulAction.stabilizer (Subgroup.zpowers ξ) u := by
      rw [MulAction.mem_stabilizer_iff]
      exact hfix
    have hbot := Subgroup.card_eq_one.mp hstab1
    rw [hbot, Subgroup.mem_bot] at hmem
    simpa using Subtype.ext_iff.mp hmem
  -- ## 3. `P` has a non-involution square
  have hex : ∃ x : P, x ^ 2 ≠ 1 := by
    by_contra hcon
    push_neg at hcon
    obtain ⟨a, b, hab⟩ := h.noncomm
    refine hab ?_
    have ha : a * a = 1 := by rw [← pow_two]; exact hcon a
    have hb' : b * b = 1 := by rw [← pow_two]; exact hcon b
    have hab' : (a * b) * (a * b) = 1 := by rw [← pow_two]; exact hcon (a * b)
    calc a * b = (a * b)⁻¹ := (inv_eq_of_mul_eq_one_right hab').symm
      _ = b⁻¹ * a⁻¹ := mul_inv_rev a b
      _ = b * a := by rw [inv_eq_of_mul_eq_one_right hb', inv_eq_of_mul_eq_one_right ha]
  -- ## 4. `V = P ⧸ Z(P)` and `W = Z(P)` as `𝔽₂`-vector spaces
  have hcommZ : commutator P ≤ Subgroup.center P := by
    rw [commutator, Subgroup.commutator_le]
    intro x _ y _
    set N : Subgroup P := Subgroup.center P with hN
    have hexp : ∀ q : P ⧸ N, q * q = 1 := by
      intro q
      induction q using QuotientGroup.induction_on with
      | H z =>
        rw [← QuotientGroup.mk_mul, QuotientGroup.eq_one_iff]
        simpa [pow_two] using hb z
    have hcomm : ∀ a b : P ⧸ N, a * b = b * a := by
      intro a b
      have ha : a * a = 1 := hexp a
      have hbq : b * b = 1 := hexp b
      have hab : a * b * (a * b) = 1 := hexp (a * b)
      calc a * b = (a * b)⁻¹ := (inv_eq_of_mul_eq_one_right hab).symm
        _ = b⁻¹ * a⁻¹ := mul_inv_rev a b
        _ = b * a := by rw [inv_eq_of_mul_eq_one_right hbq, inv_eq_of_mul_eq_one_right ha]
    have key : (QuotientGroup.mk' N) ⁅x, y⁆ = 1 := by
      have h1 := hcomm ((QuotientGroup.mk' N) x) ((QuotientGroup.mk' N) y)
      rw [commutatorElement_def]
      simp only [map_mul, map_inv]
      rw [h1]
      group
    exact (QuotientGroup.eq_one_iff ⁅x, y⁆).mp key
  haveI hmcq : IsMulCommutative (P ⧸ Subgroup.center P) :=
    Subgroup.Normal.quotient_commutative_iff_commutator_le.mpr hcommZ
  letI cGq : CommGroup (P ⧸ Subgroup.center P) :=
    { (inferInstance : Group (P ⧸ Subgroup.center P)) with
      mul_comm := fun a b => hmcq.is_comm.comm a b }
  letI cGz : CommGroup ↥(Subgroup.center P) :=
    { (inferInstance : Group ↥(Subgroup.center P)) with
      mul_comm := fun a b => Subtype.ext ((Subgroup.mem_center_iff.mp b.2) (a : P)) }
  let mkc : P → Additive (P ⧸ Subgroup.center P) :=
    fun z => Additive.ofMul (QuotientGroup.mk z)
  have h2V : ∀ v : Additive (P ⧸ Subgroup.center P), (2 : ℕ) • v = 0 := by
    intro v
    refine Quotient.inductionOn v (fun x => ?_)
    change (2 : ℕ) • Additive.ofMul (QuotientGroup.mk x) = 0
    rw [← ofMul_pow, ofMul_eq_zero]
    have hxx : ((x * x : P) : P ⧸ Subgroup.center P) = 1 :=
      (QuotientGroup.eq_one_iff (N := Subgroup.center P) (x * x)).mpr
        (by simpa [pow_two] using hb x)
    simpa [pow_two] using hxx
  haveI hmodV : Module (ZMod 2) (Additive (P ⧸ Subgroup.center P)) :=
    AddCommGroup.zmodModule h2V
  have h2W : ∀ v : Additive ↥(Subgroup.center P), (2 : ℕ) • v = 0 := by
    intro v
    rw [← ofMul_toMul v, ← ofMul_pow]
    simp only [ofMul_eq_zero]
    apply Subtype.ext
    change ((v.toMul : ↥(Subgroup.center P)) : P) ^ 2 = 1
    have h1 : ((v.toMul : ↥(Subgroup.center P)) : P) ∈ omega1 P := by
      rw [← hZ]; exact (v.toMul).2
    exact h.mem_omega1.mp h1
  haveI hmodW : Module (ZMod 2) (Additive ↥(Subgroup.center P)) :=
    AddCommGroup.zmodModule h2W
  haveI hfinV : Finite (Additive (P ⧸ Subgroup.center P)) := inferInstance
  haveI hfinW : Finite (Additive ↥(Subgroup.center P)) := inferInstance
  have hVc : Nat.card (P ⧸ Subgroup.center P) = 2 ^ n := by
    have h1 := Subgroup.card_eq_card_quotient_mul_card_subgroup (Subgroup.center P)
    have h2 : Nat.card ↥(Subgroup.center P) * Nat.card ↥(Subgroup.center P)
        = Nat.card (P ⧸ Subgroup.center P) * Nat.card ↥(Subgroup.center P) := by
      rw [← pow_two, ← hcard, h1]
    have hzc : 0 < Nat.card ↥(Subgroup.center P) :=
      Nat.card_pos_iff.mpr ⟨⟨1⟩, inferInstance⟩
    have h3 : Nat.card ↥(Subgroup.center P) = Nat.card (P ⧸ Subgroup.center P) :=
      Nat.eq_of_mul_eq_mul_right hzc h2
    rw [← h3, hZcard]
  have hVn : Nat.card (Additive (P ⧸ Subgroup.center P)) = 2 ^ n := hVc
  have hWn : Nat.card (Additive ↥(Subgroup.center P)) = 2 ^ n := hZcard
  -- ## 5. the squaring map and its polar form
  let qf : P → ↥(Subgroup.center P) := fun g => ⟨g * g, by simpa [pow_two] using hb g⟩
  have hqw : ∀ a b : P, a⁻¹ * b ∈ Subgroup.center P → qf a = qf b := by
    intro a b hab
    obtain ⟨z, hz, rfl⟩ : ∃ z ∈ Subgroup.center P, b = a * z := ⟨a⁻¹ * b, hab, by group⟩
    apply Subtype.ext
    show a * a = (a * z) * (a * z)
    have hzc : z * z = 1 := by
      have h1 : z ∈ omega1 P := by rw [← hZ]; exact hz
      have h2 := h.mem_omega1.mp h1
      rwa [pow_two] at h2
    have hc : z * a = a * z := (Subgroup.mem_center_iff.mp hz a).symm
    calc a * a = a * a * (z * z) := by rw [hzc, mul_one]
      _ = a * (a * (z * z)) := by group
      _ = a * ((a * z) * z) := by group
      _ = a * ((z * a) * z) := by rw [hc]
      _ = (a * z) * (a * z) := by group
  have hqw' : ∀ a b : P, (QuotientGroup.leftRel (Subgroup.center P)) a b →
      Additive.ofMul (qf a) = Additive.ofMul (qf b) :=
    fun a b hab => congrArg Additive.ofMul (hqw a b (QuotientGroup.leftRel_apply.mp hab))
  let Q : Additive (P ⧸ Subgroup.center P) → Additive ↥(Subgroup.center P) :=
    fun v => Quotient.liftOn v.toMul (fun g => Additive.ofMul (qf g)) hqw'
  have Q_mk : ∀ g : P, Q (mkc g) = Additive.ofMul (qf g) :=
    fun g => congrArg Additive.ofMul
      (Quotient.liftOn_mk (s := QuotientGroup.leftRel (Subgroup.center P))
        (fun g => Additive.ofMul (qf g)) hqw' g)
  have Q_zero : Q 0 = 0 := by
    change Q (mkc 1) = 0
    rw [Q_mk, ofMul_eq_zero]
    apply Subtype.ext
    show (1 : P) * 1 = 1
    group
  have Q_aniso : ∀ v, Q v = 0 → v = 0 := by
    intro v
    refine Quotient.inductionOn v (fun g => ?_)
    intro hv
    have hv' : Q (mkc g) = 0 := hv
    rw [Q_mk, ofMul_eq_zero] at hv'
    have hg : g * g = 1 := congrArg Subtype.val hv'
    have hg2 : g ^ 2 = 1 := by rw [pow_two]; exact hg
    change mkc g = 0
    rw [ofMul_eq_zero, QuotientGroup.eq_one_iff, hZ]
    exact h.mem_omega1.mpr hg2
  let bZ : P → P → ↥(Subgroup.center P) :=
    fun x y => ⟨⁅y, x⁆, hcommZ (Subgroup.commutator_mem_commutator
      (Subgroup.mem_top y) (Subgroup.mem_top x))⟩
  have bZ_mul₁ : ∀ a b y : P, bZ (a * b) y = bZ a y * bZ b y := by
    intro a b y
    apply Subtype.ext
    show ⁅y, a * b⁆ = ⁅y, a⁆ * ⁅y, b⁆
    exact commutator_mul_right_class_two hcommZ a b y
  have bZ_mul₂ : ∀ y a b : P, bZ y (a * b) = bZ y a * bZ y b := by
    intro y a b
    apply Subtype.ext
    show ⁅a * b, y⁆ = ⁅a, y⁆ * ⁅b, y⁆
    exact commutator_mul_left_class_two hcommZ a b y
  have bZ_wd : ∀ a₁ b₁ a₂ b₂ : P,
      (QuotientGroup.leftRel (Subgroup.center P)) a₁ a₂ →
      (QuotientGroup.leftRel (Subgroup.center P)) b₁ b₂ → bZ a₁ b₁ = bZ a₂ b₂ := by
    intro a₁ b₁ a₂ b₂ ha hb₂
    obtain ⟨z, hz, rfl⟩ : ∃ z ∈ Subgroup.center P, a₂ = a₁ * z :=
      ⟨a₁⁻¹ * a₂, QuotientGroup.leftRel_apply.mp ha, by group⟩
    obtain ⟨w, hw, rfl⟩ : ∃ w ∈ Subgroup.center P, b₂ = b₁ * w :=
      ⟨b₁⁻¹ * b₂, QuotientGroup.leftRel_apply.mp hb₂, by group⟩
    apply Subtype.ext
    show ⁅b₁, a₁⁆ = ⁅b₁ * w, a₁ * z⁆
    rw [commutator_mul_left_class_two hcommZ b₁ w (a₁ * z),
        commutator_eq_one_of_mem_center_left hw (a₁ * z), mul_one,
        commutator_mul_right_class_two hcommZ a₁ z b₁,
        commutator_eq_one_of_mem_center_right hz b₁, mul_one]
  let bZq : Additive (P ⧸ Subgroup.center P) → Additive (P ⧸ Subgroup.center P) →
      Additive ↥(Subgroup.center P) :=
    fun v w => Additive.ofMul (Quotient.liftOn₂ v.toMul w.toMul bZ bZ_wd)
  have bZq_mk : ∀ x y : P, bZq (mkc x) (mkc y) = Additive.ofMul (bZ x y) :=
    fun x y => congrArg Additive.ofMul (Quotient.liftOn₂_mk bZ bZ_wd x y)
  have hsum : ∀ x y : P, mkc x + mkc y = mkc (x * y) := by
    intro x y
    show Additive.ofMul (QuotientGroup.mk x) + Additive.ofMul (QuotientGroup.mk y)
      = Additive.ofMul (QuotientGroup.mk (x * y))
    rw [← ofMul_mul, ← QuotientGroup.mk_mul]
  have bZq_zero₁ : ∀ w : Additive (P ⧸ Subgroup.center P), bZq 0 w = 0 := by
    intro w
    refine Quotient.inductionOn w (fun z => ?_)
    change bZq (mkc 1) (mkc z) = 0
    rw [bZq_mk 1 z, ofMul_eq_zero]
    apply Subtype.ext
    show ⁅z, 1⁆ = 1
    rw [commutatorElement_def]; group
  have bZq_zero₂ : ∀ w : Additive (P ⧸ Subgroup.center P), bZq w 0 = 0 := by
    intro w
    refine Quotient.inductionOn w (fun z => ?_)
    change bZq (mkc z) (mkc 1) = 0
    rw [bZq_mk z 1, ofMul_eq_zero]
    apply Subtype.ext
    show ⁅1, z⁆ = 1
    rw [commutatorElement_def]; group
  have bZq_add₁ : ∀ v₁ v₂ w : Additive (P ⧸ Subgroup.center P),
      bZq (v₁ + v₂) w = bZq v₁ w + bZq v₂ w := by
    intro v₁ v₂ w
    refine Quotient.inductionOn v₁ (fun x => ?_)
    refine Quotient.inductionOn v₂ (fun y => ?_)
    refine Quotient.inductionOn w (fun z => ?_)
    change bZq (mkc x + mkc y) (mkc z) = bZq (mkc x) (mkc z) + bZq (mkc y) (mkc z)
    rw [hsum x y, bZq_mk (x * y) z, bZq_mk x z, bZq_mk y z, ← ofMul_mul, ← bZ_mul₁ x y z]
  have bZq_add₂ : ∀ v w₁ w₂ : Additive (P ⧸ Subgroup.center P),
      bZq v (w₁ + w₂) = bZq v w₁ + bZq v w₂ := by
    intro v w₁ w₂
    refine Quotient.inductionOn v (fun z => ?_)
    refine Quotient.inductionOn w₁ (fun x => ?_)
    refine Quotient.inductionOn w₂ (fun y => ?_)
    change bZq (mkc z) (mkc x + mkc y) = bZq (mkc z) (mkc x) + bZq (mkc z) (mkc y)
    rw [hsum x y, bZq_mk z (x * y), bZq_mk z x, bZq_mk z y, ← ofMul_mul, ← bZ_mul₂ z x y]
  have bZq_smul₁ : ∀ (c : ZMod 2) (v w : Additive (P ⧸ Subgroup.center P)),
      bZq (c • v) w = c • bZq v w := by
    intro c v w
    let φ : Additive (P ⧸ Subgroup.center P) →+ Additive ↥(Subgroup.center P) :=
      { toFun := fun x => bZq x w
        map_zero' := bZq_zero₁ w
        map_add' := fun x y => bZq_add₁ x y w }
    exact ZMod.map_smul φ c v
  have bZq_smul₂ : ∀ (c : ZMod 2) (v w : Additive (P ⧸ Subgroup.center P)),
      bZq v (c • w) = c • bZq v w := by
    intro c v w
    let φ : Additive (P ⧸ Subgroup.center P) →+ Additive ↥(Subgroup.center P) :=
      { toFun := fun x => bZq v x
        map_zero' := bZq_zero₂ v
        map_add' := fun x y => bZq_add₂ v x y }
    exact ZMod.map_smul φ c w
  let bq : Additive (P ⧸ Subgroup.center P) →ₗ[ZMod 2]
      Additive (P ⧸ Subgroup.center P) →ₗ[ZMod 2] Additive ↥(Subgroup.center P) :=
    LinearMap.mk₂ (ZMod 2) bZq bZq_add₁ bZq_smul₁ bZq_add₂ bZq_smul₂
  have hbq : ∀ v w, Q (v + w) = Q v + Q w + bq v w := by
    intro v w
    refine Quotient.inductionOn v (fun x => ?_)
    refine Quotient.inductionOn w (fun y => ?_)
    change Q (mkc x + mkc y) = Q (mkc x) + Q (mkc y) + bZq (mkc x) (mkc y)
    rw [hsum x y, Q_mk, Q_mk x, Q_mk y, bZq_mk x y, ← ofMul_mul, ← ofMul_mul]
    congr 1
    apply Subtype.ext
    show (x * y) * (x * y) = (x * x) * (y * y) * ⁅y, x⁆
    have hc : ⁅y, x⁆ ∈ Subgroup.center P := hcommZ (Subgroup.commutator_mem_commutator
      (Subgroup.mem_top y) (Subgroup.mem_top x))
    have h1 : ⁅y, x⁆ * x = x * ⁅y, x⁆ := (Subgroup.mem_center_iff.mp hc x).symm
    have h2 : ⁅y, x⁆ * y = y * ⁅y, x⁆ := (Subgroup.mem_center_iff.mp hc y).symm
    have hcyx : y * x = ⁅y, x⁆ * x * y := by rw [commutatorElement_def]; group
    calc (x * y) * (x * y) = x * (y * x) * y := by group
      _ = x * (⁅y, x⁆ * x * y) * y := by rw [hcyx]
      _ = (x * x) * (y * y) * ⁅y, x⁆ := by
            calc x * (⁅y, x⁆ * x * y) * y = x * (x * (⁅y, x⁆ * y)) * y := by
                  rw [h1]; group
              _ = x * (x * (y * ⁅y, x⁆)) * y := by rw [h2]
              _ = x * (x * y) * (⁅y, x⁆ * y) := by group
              _ = x * (x * y) * (y * ⁅y, x⁆) := by rw [h2]
              _ = (x * x) * (y * y) * ⁅y, x⁆ := by group
  have hB : ∀ v w : Additive (P ⧸ Subgroup.center P), Q (v + w) + Q v + Q w = bq v w := by
    intro v w
    have h := hbq v w
    rw [h]
    exact add_add_add_self (Q v) (Q w) (bq v w)
  have hadd1 : ∀ a a' c : Additive (P ⧸ Subgroup.center P),
      Q (a + a' + c) + Q (a + a') + Q c =
        (Q (a + c) + Q a + Q c) + (Q (a' + c) + Q a' + Q c) := by
    intro a a' c
    rw [hB (a + a') c, hB a c, hB a' c, map_add, LinearMap.add_apply]
  have hadd2 : ∀ a c c' : Additive (P ⧸ Subgroup.center P),
      Q (a + (c + c')) + Q a + Q (c + c') =
        (Q (a + c) + Q a + Q c) + (Q (a + c') + Q a + Q c') := by
    intro a c c'
    rw [hB a (c + c'), hB a c, hB a c', map_add]
  -- ## 6. the induced actions of `ξ`
  let ξVM : MulAut (P ⧸ Subgroup.center P) :=
    QuotientGroup.congr (Subgroup.center P) (Subgroup.center P) (ξ : P ≃* P) (center_map_mulAut ξ)
  have ξVM_mk : ∀ x : P, ξVM (mkc x) = mkc (ξ x) := by
    intro x
    change ξVM (QuotientGroup.mk x) = QuotientGroup.mk (ξ x)
    exact QuotientGroup.congr_mk _ _ (ξ : P ≃* P) (center_map_mulAut ξ) x
  have ξVM_pow_mk : ∀ (k : ℕ) (x : P), (ξVM ^ k) (mkc x) = mkc ((ξ ^ k) x) := by
    intro k
    induction k with
    | zero => intro x; rfl
    | succ k ih =>
      intro x
      have hmul : (ξVM ^ (k + 1)) (mkc x) = (ξVM ^ k) (ξVM (mkc x)) := by
        rw [pow_succ]; rfl
      rw [hmul, ξVM_mk, show (ξ ^ (k + 1)) x = (ξ ^ k) (ξ x) by rw [pow_succ]; rfl]
      exact ih (ξ x)
  let toLin : MulAut (P ⧸ Subgroup.center P) →*
      (Additive (P ⧸ Subgroup.center P) ≃ₗ[ZMod 2] Additive (P ⧸ Subgroup.center P)) :=
    { toFun := fun e => zmodLinearEquivOfAddEquiv (mulEquivToAddEquiv e)
      map_one' := by ext v; rfl
      map_mul' := by intro a b; ext v; rw [LinearEquiv.mul_apply]; rfl }
  let ξV : Additive (P ⧸ Subgroup.center P) ≃ₗ[ZMod 2] Additive (P ⧸ Subgroup.center P) :=
    toLin ξVM
  have toLin_apply : ∀ (e : MulAut (P ⧸ Subgroup.center P))
      (w : Additive (P ⧸ Subgroup.center P)), toLin e w = e w := fun e w => rfl
  have ξV_mk : ∀ x : P, ξV (mkc x) = mkc (ξ x) := by
    intro x
    rw [show ξV (mkc x) = toLin ξVM (mkc x) from rfl, toLin_apply]
    exact ξVM_mk x
  have ξV_pow_mk : ∀ (k : ℕ) (x : P), (ξV ^ k) (mkc x) = mkc ((ξ ^ k) x) := by
    intro k
    induction k with
    | zero => intro x; rfl
    | succ k ih =>
      intro x
      rw [pow_succ, LinearEquiv.mul_apply, ξV_mk,
        show (ξ ^ (k + 1)) x = (ξ ^ k) (ξ x) by rw [pow_succ, MulAut.mul_apply]]
      exact ih (ξ x)
  let ξZmul : MulAut ↥(Subgroup.center P) :=
    (MulEquiv.subgroupMap (ξ : P ≃* P) (Subgroup.center P)).trans
      (MulEquiv.subgroupCongr (center_map_mulAut ξ))
  have ξZmul_coe : ∀ z : ↥(Subgroup.center P),
      ((ξZmul z : ↥(Subgroup.center P)) : P) = ξ (z : P) := fun z => rfl
  have ξZmul_pow_coe : ∀ (k : ℕ) (z : ↥(Subgroup.center P)),
      (((ξZmul ^ k) z : ↥(Subgroup.center P)) : P) = (ξ ^ k) (z : P) := by
    intro k
    induction k with
    | zero => intro z; rfl
    | succ k ih =>
      intro z
      rw [pow_succ, MulAut.mul_apply, ih (ξZmul z), ξZmul_coe z,
        show (ξ ^ (k + 1)) (z : P) = (ξ ^ k) (ξ (z : P)) by
          rw [pow_succ, MulAut.mul_apply]]
  let toLinW : MulAut ↥(Subgroup.center P) →*
      (Additive ↥(Subgroup.center P) ≃ₗ[ZMod 2] Additive ↥(Subgroup.center P)) :=
    { toFun := fun e => zmodLinearEquivOfAddEquiv (mulEquivToAddEquiv e)
      map_one' := by ext v; rfl
      map_mul' := by intro a b; ext v; rw [LinearEquiv.mul_apply]; rfl }
  let ξW : Additive ↥(Subgroup.center P) ≃ₗ[ZMod 2] Additive ↥(Subgroup.center P) :=
    toLinW ξZmul
  have toLinW_apply : ∀ (e : MulAut ↥(Subgroup.center P)) (z : Additive ↥(Subgroup.center P)),
      toLinW e z = e z := fun e z => rfl
  have ξW_apply : ∀ z : Additive ↥(Subgroup.center P), ξW z = ξZmul z := fun z => rfl
  have ξW_ofMul : ∀ z : ↥(Subgroup.center P),
      ξW (Additive.ofMul z) = Additive.ofMul (⟨ξ (z : P), by
        have h := Subgroup.mem_map_of_mem (ξ : MulAut P).toMonoidHom z.2
        rwa [center_map_mulAut ξ] at h⟩ : ↥(Subgroup.center P)) := by
    intro z
    change toLinW ξZmul (Additive.ofMul z) = _
    rw [toLinW_apply]
    exact congrArg Additive.ofMul (Subtype.ext (ξZmul_coe z))
  have ξW_pow_coe : ∀ (k : ℕ) (z : Additive ↥(Subgroup.center P)),
      ((Additive.toMul ((ξW ^ k) z) : ↥(Subgroup.center P)) : P)
        = (ξ ^ k) ((Additive.toMul z : ↥(Subgroup.center P)) : P) := by
    intro k
    induction k with
    | zero => intro z; rfl
    | succ k ih =>
      intro z
      have hcoe : ((Additive.toMul (ξZmul z) : ↥(Subgroup.center P)) : P)
          = ξ ((Additive.toMul z : ↥(Subgroup.center P)) : P) := ξZmul_coe z
      rw [pow_succ, LinearEquiv.mul_apply, ξW_apply, ih (ξZmul z), hcoe,
        show (ξ ^ (k + 1)) ((Additive.toMul z : ↥(Subgroup.center P)) : P)
            = (ξ ^ k) (ξ ((Additive.toMul z : ↥(Subgroup.center P)) : P)) by
          rw [pow_succ]; rfl]
  -- ## 7. `ξ` acts on `V` faithfully and freely
  have hVfix : ∀ (k : ℕ) (v : Additive (P ⧸ Subgroup.center P)),
      (ξV ^ k) v = v → v ≠ 0 → ξ ^ k = 1 := by
    intro k v hv hv0
    revert hv hv0
    refine Quotient.inductionOn v (fun x => ?_)
    intro hv hv0
    change (ξV ^ k) (mkc x) = mkc x at hv
    change mkc x ≠ 0 at hv0
    have h1 : (ξVM ^ k) (mkc x) = mkc x := by
      have h := hv
      rw [ξV_pow_mk k x, ← ξVM_pow_mk k x] at h
      exact h
    have hx : x ∉ Subgroup.center P := by
      intro hxmem
      apply hv0
      change Additive.ofMul (QuotientGroup.mk x) = 0
      rw [ofMul_eq_zero, QuotientGroup.eq_one_iff]
      exact hxmem
    have hz : ((ξ ^ k) x)⁻¹ * x ∈ Subgroup.center P := by
      have h2 : (QuotientGroup.mk ((ξ ^ k) x) : P ⧸ Subgroup.center P)
          = QuotientGroup.mk x := by
        have h := h1
        rw [ξVM_pow_mk k x] at h
        exact Additive.ofMul.injective h
      exact QuotientGroup.eq.mp h2
    obtain ⟨w, hw, hwx⟩ : ∃ w ∈ Subgroup.center P, (ξ ^ k) x = x * w := by
      refine ⟨(((ξ ^ k) x)⁻¹ * x)⁻¹, Subgroup.inv_mem _ hz, ?_⟩
      group
    have hyfix : (ξ ^ k) (x * x) = x * x := by
      have hc : w * x = x * w := (Subgroup.mem_center_iff.mp hw x).symm
      have hw2 : w * w = 1 := by
        have h1 : w ∈ omega1 P := by rw [← hZ]; exact hw
        have h2 := h.mem_omega1.mp h1
        rwa [pow_two] at h2
      calc (ξ ^ k) (x * x) = (x * w) * (x * w) := by rw [map_mul, hwx]
        _ = x * (w * x) * w := by group
        _ = x * (x * w) * w := by rw [hc]
        _ = (x * x) * (w * w) := by group
        _ = x * x := by rw [hw2, mul_one]
    have hy2 : orderOf (x * x) = 2 := by
      have hne : x * x ≠ 1 := by
        intro h1
        exact hx (by rw [hZ]; exact h.mem_omega1.mpr (by rw [pow_two]; exact h1))
      have hsq : (x * x) * (x * x) = 1 := by
        have h1 : x * x ∈ omega1 P := by rw [← hZ, ← pow_two]; exact hb x
        have h2 := h.mem_omega1.mp h1
        rwa [pow_two] at h2
      exact orderOf_eq_prime_iff.mpr ⟨by rw [pow_two]; exact hsq, hne⟩
    exact hstab (x * x) k hy2 hyfix
  have hVMpow : ξVM ^ (2 ^ n - 1) = 1 := by
    ext q
    induction q using QuotientGroup.induction_on with
    | H x =>
      change (ξVM ^ (2 ^ n - 1)) (mkc x) = (1 : MulAut (P ⧸ Subgroup.center P)) (mkc x)
      rw [ξVM_pow_mk,
        show (ξ ^ (2 ^ n - 1)) = (1 : MulAut P) by rw [← hξord', pow_orderOf_eq_one]]
      rfl
  have hpowV : ξV ^ (2 ^ n - 1) = 1 := by
    change (toLin ξVM) ^ (2 ^ n - 1) = 1
    rw [← map_pow, hVMpow, map_one]
  have hordV : orderOf ξV = 2 ^ n - 1 := by
    refine Nat.dvd_antisymm (orderOf_dvd_iff_pow_eq_one.mpr hpowV) ?_
    have hnt : Nontrivial (Additive (P ⧸ Subgroup.center P)) := by
      refine not_subsingleton_iff_nontrivial.mp fun hsub => ?_
      haveI := hsub
      have h1 : Nat.card (Additive (P ⧸ Subgroup.center P)) = 1 :=
        Nat.card_eq_one_iff_unique.mpr ⟨inferInstance, ⟨0⟩⟩
      rw [hVn] at h1
      have h2 : 1 < 2 ^ n := Nat.one_lt_pow (by omega) (by norm_num)
      omega
    obtain ⟨v₀, hv₀⟩ := exists_ne (0 : Additive (P ⧸ Subgroup.center P))
    rw [← hξord']
    exact orderOf_dvd_iff_pow_eq_one.mpr
      (hVfix (orderOf ξV) v₀ (by rw [pow_orderOf_eq_one]; rfl) hv₀)
  have hfreeV : ∀ v : Additive (P ⧸ Subgroup.center P), ξV v = v → v = 0 := by
    intro v hv
    by_contra hv0
    have h1 : ξ ^ 1 = 1 := hVfix 1 v (by simpa using hv) hv0
    have h1' : ξ = 1 := by simpa using h1
    have h2 : 2 ^ n - 1 = 1 := by rw [← hξord', h1', orderOf_one]
    omega
  -- ## 8. `ξ` acts on `W = Z(P) = Ω₁(P)` with order `q - 1` and freely
  obtain ⟨u₀, u₁, hu₀, hu₁, hu₀₁⟩ := h.manyInvol
  have hstabW : ∀ k : ℕ, (ξW ^ k) = 1 → ξ ^ k = 1 := by
    intro k hk
    have h1 : (ξW ^ k) (Additive.ofMul ⟨u₀, h.invol_mem_center hu₀⟩) =
        Additive.ofMul (⟨u₀, h.invol_mem_center hu₀⟩ : ↥(Subgroup.center P)) := by
      rw [hk]
      rfl
    have h2 : (ξ ^ k) u₀ = u₀ := by
      have h3 := ξW_pow_coe k (Additive.ofMul ⟨u₀, h.invol_mem_center hu₀⟩)
      rw [h1] at h3
      simpa using h3.symm
    exact hstab u₀ k hu₀ h2
  have hordW : orderOf ξW = 2 ^ n - 1 := by
    refine Nat.dvd_antisymm ?_ ?_
    · rw [orderOf_dvd_iff_pow_eq_one]
      ext z
      rw [ξW_pow_coe, ← hξord', pow_orderOf_eq_one]
      rfl
    · rw [← hξord', orderOf_dvd_iff_pow_eq_one]
      exact hstabW (orderOf ξW) (pow_orderOf_eq_one ξW)
  have hfreeW : ∀ w : Additive ↥(Subgroup.center P), ξW w = w → w = 0 := by
    intro w hw
    by_contra hw0
    have hw1 : w ≠ (1 : ↥(Subgroup.center P)) := hw0
    have h2 : ξ ((Additive.toMul w : ↥(Subgroup.center P)) : P)
        = ((Additive.toMul w : ↥(Subgroup.center P)) : P) := by
      have h3 : ((Additive.toMul ((ξW ^ 1) w) : ↥(Subgroup.center P)) : P)
          = (ξ ^ 1) ((Additive.toMul w : ↥(Subgroup.center P)) : P) := ξW_pow_coe 1 w
      rw [pow_one] at h3
      rw [hw] at h3
      exact h3.symm
    have hz2 : orderOf ((Additive.toMul w : ↥(Subgroup.center P)) : P) = 2 := by
      have hmem : ((Additive.toMul w : ↥(Subgroup.center P)) : P) ∈ omega1 P := by
        rw [← hZ]; exact (Additive.toMul w : ↥(Subgroup.center P)).2
      exact orderOf_eq_prime_iff.mpr
        ⟨h.mem_omega1.mp hmem, fun h => hw1 (Subtype.ext h)⟩
    have h4 : ξ = 1 := hstab ((Additive.toMul w : ↥(Subgroup.center P)) : P) 1 hz2
      (by simpa using h2)
    have h5 : orderOf ξ = 1 := by rw [h4]; exact orderOf_one
    rw [hξord'] at h5
    omega
  -- ## 9. Gorenstein–Thompson: no `ξ`-equivariant linear isomorphism `V ≃ W`
  obtain ⟨Φs, ν, hνord, hΦs⟩ := exists_singer_iso hnpos hVn ξV hordV hfreeV
  have hΦs_pow : ∀ (k : ℕ) (v : Additive (P ⧸ Subgroup.center P)),
      Φs ((ξV ^ k) v) = ((ν ^ k : (GaloisField 2 n)ˣ) : GaloisField 2 n) * Φs v := by
    intro k
    induction k with
    | zero => intro v; simp
    | succ k ih =>
      intro v
      have h1 : (ξV ^ (k + 1)) v = (ξV ^ k) (ξV v) := by
        rw [pow_succ, LinearEquiv.mul_apply]
      rw [h1, ih (ξV v), hΦs v,
        show ((ν ^ (k + 1) : (GaloisField 2 n)ˣ) : GaloisField 2 n)
          = ((ν ^ k : (GaloisField 2 n)ˣ) : GaloisField 2 n) * (ν : GaloisField 2 n)
          from by rw [pow_succ, Units.val_mul]]
      ring
  have hgen : Subgroup.zpowers ν = ⊤ := by
    apply Subgroup.eq_top_of_card_eq
    rw [Nat.card_zpowers, hνord, Nat.card_units, GaloisField.card 2 n (by omega)]
  have htransV : ∀ a b : Additive (P ⧸ Subgroup.center P), a ≠ 0 → b ≠ 0 →
      ∃ k : ℕ, (ξV ^ k) a = b := by
    intro a b ha hb'
    have hΦa : Φs a ≠ 0 := fun h => ha (Φs.injective (by rw [h, map_zero]))
    have hΦb : Φs b ≠ 0 := fun h => hb' (Φs.injective (by rw [h, map_zero]))
    set u : (GaloisField 2 n)ˣ := Units.mk0 (Φs b * (Φs a)⁻¹)
      (mul_ne_zero hΦb (inv_ne_zero hΦa)) with hu
    have hmem : u ∈ Subgroup.zpowers ν := by rw [hgen]; exact Subgroup.mem_top _
    have hfin : IsOfFinOrder ν := isOfFinOrder_of_finite ν
    have h2 := (IsOfFinOrder.mem_zpowers_iff_mem_range_orderOf hfin).mp hmem
    rcases Finset.mem_image.mp h2 with ⟨k, -, hk⟩
    refine ⟨k, Φs.injective ?_⟩
    rw [hΦs_pow]
    have hk' : ((ν ^ k : (GaloisField 2 n)ˣ) : GaloisField 2 n) = Φs b * (Φs a)⁻¹ := by
      rw [hk, hu]
      exact Units.val_mk0 _
    rw [hk', mul_assoc, inv_mul_cancel₀ hΦa, mul_one]
  have hne_pair : ∃ a b : Additive (P ⧸ Subgroup.center P), bq a b ≠ 0 := by
    obtain ⟨x, y, hxy⟩ := h.noncomm
    refine ⟨mkc x, mkc y, ?_⟩
    change bZq (mkc x) (mkc y) ≠ 0
    rw [bZq_mk]
    intro h0
    have h1 : ⁅y, x⁆ = 1 := by
      have h2 : bZ x y = 1 := ofMul_eq_zero.mp h0
      have h3 : ((bZ x y : ↥(Subgroup.center P)) : P) = 1 :=
        congrArg (fun z : ↥(Subgroup.center P) => (z : P)) h2
      simpa [bZ] using h3
    exact hxy (commutatorElement_eq_one_iff_mul_comm.mp h1).symm
  have halt : ∀ a : Additive (P ⧸ Subgroup.center P), bq a a = 0 := by
    intro a
    refine Quotient.inductionOn a (fun x => ?_)
    change bZq (mkc x) (mkc x) = 0
    rw [bZq_mk, ofMul_eq_zero]
    apply Subtype.ext
    show ⁅x, x⁆ = 1
    rw [commutatorElement_def]; group
  have heq : ∀ a b : Additive (P ⧸ Subgroup.center P), bq (ξV a) (ξV b) = ξW (bq a b) := by
    intro a b
    refine Quotient.inductionOn a (fun x => ?_)
    refine Quotient.inductionOn b (fun y => ?_)
    change bZq (ξV (mkc x)) (ξV (mkc y)) = ξW (bZq (mkc x) (mkc y))
    rw [ξV_mk x, ξV_mk y, bZq_mk (ξ x) (ξ y), bZq_mk x y, ξW_ofMul]
    congr 1
    apply Subtype.ext
    show ⁅ξ y, ξ x⁆ = ξ ⁅y, x⁆
    simp only [commutatorElement_def, map_mul, map_inv]
  have hβ1 : ∀ a b d : Additive (P ⧸ Subgroup.center P), bq (a + b) d = bq a d + bq b d := by
    intro a b d; rw [map_add, LinearMap.add_apply]
  have hβ2 : ∀ a b d : Additive (P ⧸ Subgroup.center P), bq a (b + d) = bq a b + bq a d := by
    intro a b d; rw [map_add]
  have hnoiso : ¬ ∃ σ : Additive (P ⧸ Subgroup.center P) ≃ₗ[ZMod 2]
      Additive ↥(Subgroup.center P), ∀ v, σ (ξV v) = ξW (σ v) :=
    no_equivariant_linearEquiv ξV htransV ξW (fun a b => bq a b) hβ1 hβ2 halt heq hne_pair
  -- ## 10. assemble
  have hQeq : ∀ v : Additive (P ⧸ Subgroup.center P), Q (ξV v) = ξW (Q v) := by
    intro v
    refine Quotient.inductionOn v (fun x => ?_)
    change Q (ξV (mkc x)) = ξW (Q (mkc x))
    rw [ξV_mk x, Q_mk, Q_mk, ξW_ofMul (qf x)]
    congr 1
    apply Subtype.ext
    show (ξ x) * (ξ x) = ξ (x * x)
    rw [← map_mul]
  obtain ⟨θ, Φ₀, Ψ₀, hθne, hθodd, hΦadd, hΨadd, hQcoord⟩ :=
    q2_linear_core_aux (V := Additive (P ⧸ Subgroup.center P))
      (W := Additive ↥(Subgroup.center P)) n hnpos hVn hWn ξV ξW hordV hordW hfreeV hfreeW
      Q Q_zero (fun v hv h0 => hv (Q_aniso v h0)) hQeq hadd1 hadd2 hnoiso
  refine ⟨n, θ, Additive.ofMul.trans Φ₀, Additive.ofMul.trans Ψ₀, hZcard, hθne, hθodd,
    ?_, ?_, ?_⟩
  · intro v w
    show Φ₀ (Additive.ofMul (v * w)) = Φ₀ (Additive.ofMul v) + Φ₀ (Additive.ofMul w)
    rw [ofMul_mul, hΦadd]
  · intro z w
    show Ψ₀ (Additive.ofMul (z * w)) = Ψ₀ (Additive.ofMul z) + Ψ₀ (Additive.ofMul w)
    rw [ofMul_mul, hΨadd]
  · intro x
    show Ψ₀ (Additive.ofMul ⟨x ^ 2, hb x⟩) =
      Φ₀ (Additive.ofMul (QuotientGroup.mk x)) * θ (Φ₀ (Additive.ofMul (QuotientGroup.mk x)))
    have h1 : Q (mkc x) = Additive.ofMul ⟨x ^ 2, hb x⟩ := by
      rw [Q_mk]
      congr 1
      apply Subtype.ext
      show x * x = x ^ 2
      rw [pow_two]
    rw [← h1, hQcoord]

end Work.Higman
