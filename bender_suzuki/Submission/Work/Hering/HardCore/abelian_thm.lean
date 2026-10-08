/-
# The computation of Peterfalvi I §3 Prop. 2 (abelian case) — main development

This file contains the heart of the abelian case of the hard core of Hering's theorem: the
contradiction (`abelian_contra`) obtained from the configuration together with the hypothesis
that all involutions of `G` lie in `C = C_G(V)`.
-/

import Mathlib
import Submission.Work.Hering.Config
import Submission.Work.Hering.HardCore.abelian_setup
import Submission.Work.Hering.HardCore.EndgameDefs
import Submission.Work.Hering.HardCore.endgame_algebra
import Submission.Work.Hering.HardCore.aut_inv_conj_V
import Submission.Work.Hering.HardCore.omega_card
import Submission.Work.Hering.HardCore.phi_mul
import Submission.Work.Hering.HardCore.phi_smul
import Submission.Work.Hering.HardCore.phi_of_cols
import Submission.Work.Hering.HardCore.adjust_witness
import Submission.Work.Hering.HardCore.zmod_two_torsion
import Submission.Work.Hering.HardCore.zmod_two_mul_of_even
import Submission.Work.Hering.HardCore.zmod_unit_of_odd
import Submission.Work.Hering.HardCore.conj_c1_inv

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

set_option autoImplicit false

namespace Work.Hering.HardCore

open LeanEval.GroupTheory.Defs

variable {G : Type*} [Group G] [Finite G]

/-! ## The model `(ℤ/2)³`: independence of the standard basis -/

/-- The standard basis of `(ℤ/2)³` is independent (over the exponents `{0,1}`). -/
lemma M3_hind_aux : ∀ a b c : Fin 2,
    (stdB 0 : M3) ^ (a : ℕ) * (stdB 1) ^ (b : ℕ) * (stdB 2) ^ (c : ℕ) = 1 →
      (a : ℕ) = 0 ∧ (b : ℕ) = 0 ∧ (c : ℕ) = 0 := by decide

/-! ## The basis of `V` attached to an isomorphism `↥V ≃* M3`, and the transvections -/

section Vbasis

variable (V : Subgroup G)

/-- The basis element `vᵢ = e⁻¹(eᵢ)` of `V`. -/
def vB (e : ↥V ≃* M3) (i : Fin 3) : ↥V := e.symm (stdB i)

/-- The transvection `σ` of `V` (`v₀ ↦ v₀`, `v₁ ↦ v₁`, `v₂ ↦ v₁v₂`), as an automorphism of `V`
transported across `e`. -/
def sigmaV (e : ↥V ≃* M3) : MulAut ↥V where
  toFun x := e.symm (sigmaM (e x))
  invFun x := e.symm (sigmaM (e x))
  left_inv x := by
    show e.symm (sigmaM (e (e.symm (sigmaM (e x))))) = x
    rw [MulEquiv.apply_symm_apply]
    rw [show sigmaM (sigmaM (e x)) = e x by
      rw [← MulAut.mul_apply, sigmaM_mul_self, MulAut.one_apply]]
    rw [MulEquiv.symm_apply_apply]
  right_inv x := by
    show e.symm (sigmaM (e (e.symm (sigmaM (e x))))) = x
    rw [MulEquiv.apply_symm_apply]
    rw [show sigmaM (sigmaM (e x)) = e x by
      rw [← MulAut.mul_apply, sigmaM_mul_self, MulAut.one_apply]]
    rw [MulEquiv.symm_apply_apply]
  map_mul' x y := by
    show e.symm (sigmaM (e (x * y))) = e.symm (sigmaM (e x)) * e.symm (sigmaM (e y))
    rw [map_mul, map_mul, map_mul]

/-- The transvection `τ` of `V` (`v₀ ↦ v₀`, `v₁ ↦ v₀v₁`, `v₂ ↦ v₀v₂`). -/
def tauV (e : ↥V ≃* M3) : MulAut ↥V where
  toFun x := e.symm (tauM (e x))
  invFun x := e.symm (tauM (e x))
  left_inv x := by
    show e.symm (tauM (e (e.symm (tauM (e x))))) = x
    rw [MulEquiv.apply_symm_apply]
    rw [show tauM (tauM (e x)) = e x by
      rw [← MulAut.mul_apply, tauM_mul_self, MulAut.one_apply]]
    rw [MulEquiv.symm_apply_apply]
  right_inv x := by
    show e.symm (tauM (e (e.symm (tauM (e x))))) = x
    rw [MulEquiv.apply_symm_apply]
    rw [show tauM (tauM (e x)) = e x by
      rw [← MulAut.mul_apply, tauM_mul_self, MulAut.one_apply]]
    rw [MulEquiv.symm_apply_apply]
  map_mul' x y := by
    show e.symm (tauM (e (x * y))) = e.symm (tauM (e x)) * e.symm (tauM (e y))
    rw [map_mul, map_mul, map_mul]

@[simp] lemma sigmaV_apply (e : ↥V ≃* M3) (x : ↥V) :
    (sigmaV V e x : ↥V) = e.symm (sigmaM (e x)) := rfl

@[simp] lemma tauV_apply (e : ↥V ≃* M3) (x : ↥V) :
    (tauV V e x : ↥V) = e.symm (tauM (e x)) := rfl

@[simp] lemma e_vB (e : ↥V ≃* M3) (i : Fin 3) : e (vB V e i) = stdB i := by
  simp [vB]

lemma sigmaV_vB_zero (e : ↥V ≃* M3) : sigmaV V e (vB V e 0) = vB V e 0 := by
  apply e.injective
  simp [sigmaM_stdB_zero]

lemma sigmaV_vB_one (e : ↥V ≃* M3) : sigmaV V e (vB V e 1) = vB V e 1 := by
  apply e.injective
  simp [sigmaM_stdB_one]

lemma sigmaV_vB_two (e : ↥V ≃* M3) :
    sigmaV V e (vB V e 2) = vB V e 1 * vB V e 2 := by
  apply e.injective
  simp [sigmaM_stdB_two]

lemma tauV_vB_zero (e : ↥V ≃* M3) : tauV V e (vB V e 0) = vB V e 0 := by
  apply e.injective
  simp [tauM_stdB_zero]

lemma tauV_vB_one (e : ↥V ≃* M3) :
    tauV V e (vB V e 1) = vB V e 0 * vB V e 1 := by
  apply e.injective
  simp [tauM_stdB_one]

lemma tauV_vB_two (e : ↥V ≃* M3) :
    tauV V e (vB V e 2) = vB V e 0 * vB V e 2 := by
  apply e.injective
  simp [tauM_stdB_two]

lemma sigmaV_mul_self (e : ↥V ≃* M3) : sigmaV V e * sigmaV V e = 1 := by
  apply MulEquiv.ext
  intro x
  show sigmaV V e (sigmaV V e x) = x
  apply e.injective
  rw [show e (sigmaV V e (sigmaV V e x)) = sigmaM (sigmaM (e x)) by
    simp only [sigmaV_apply, MulEquiv.apply_symm_apply]]
  rw [← MulAut.mul_apply, sigmaM_mul_self, MulAut.one_apply]

lemma tauV_mul_self (e : ↥V ≃* M3) : tauV V e * tauV V e = 1 := by
  apply MulEquiv.ext
  intro x
  show tauV V e (tauV V e x) = x
  apply e.injective
  rw [show e (tauV V e (tauV V e x)) = tauM (tauM (e x)) by
    simp only [tauV_apply, MulEquiv.apply_symm_apply]]
  rw [← MulAut.mul_apply, tauM_mul_self, MulAut.one_apply]

/-- The independence of the basis `(v₀, v₁, v₂)` of `V`. -/
lemma vB_independent (e : ↥V ≃* M3) {a b c : ℕ} (ha : a < 2) (hb : b < 2) (hc : c < 2)
    (h : (vB V e 0 : G) ^ a * (vB V e 1 : G) ^ b * (vB V e 2 : G) ^ c = 1) :
    a = 0 ∧ b = 0 ∧ c = 0 := by
  have h' : (stdB 0 : M3) ^ a * (stdB 1) ^ b * (stdB 2) ^ c = 1 := by
    have hV : (vB V e 0) ^ a * (vB V e 1) ^ b * (vB V e 2) ^ c = 1 :=
      Subtype.ext (by simpa using h)
    have h2 := congrArg e hV
    simpa [vB, map_mul, map_pow] using h2
  have := M3_hind_aux ⟨a, ha⟩ ⟨b, hb⟩ ⟨c, hc⟩ h'
  simpa using this

end Vbasis


/-! ## From an automorphism of `V` to an element of `G` acting as it -/

section Conjugation

variable (V C : Subgroup G) [V.Normal]

/-- If `g ∈ G` acts trivially on `V`, then `g ∈ C = C_G(V)`. -/
lemma mem_C_of_conjNormal_eq_one (hC : C = Subgroup.centralizer ((V : Set G))) {g : G}
    (hg : ∀ x : ↥V, MulAut.conjNormal g x = x) : g ∈ C := by
  rw [mem_C_iff V C hC]
  intro w hw
  have h1 : MulAut.conjNormal g ⟨w, hw⟩ = ⟨w, hw⟩ := hg ⟨w, hw⟩
  have h2 : g * w * g⁻¹ = w := by
    have := congrArg (fun x : ↥V => (x : G)) h1
    simpa [MulAut.conjNormal_apply] using this
  calc w * g = (g * w * g⁻¹) * g := by rw [h2]
    _ = g * w := by group

/-- An element `g ∈ G` realising a given automorphism `φ` of `V` by conjugation. -/
lemma conjNormal_eq_of_hAut (hAut : ActsAsAut V (inferInstance : V.Normal)) (φ : MulAut ↥V) :
    ∃ g : G, ∀ x : ↥V, φ x = MulAut.conjNormal g x := by
  obtain ⟨g, hg⟩ := hAut φ
  refine ⟨g, fun x => ?_⟩
  apply Subtype.ext
  rw [hg x, MulAut.conjNormal_apply]

end Conjugation


/-! ## The computation -/

section Contra

variable (V C : Subgroup G) [V.Normal]

/-- `vᵢ ≠ 1`. -/
lemma vB_ne_one (e : ↥V ≃* M3) (i : Fin 3) : (vB V e i : G) ≠ 1 := by
  intro h
  have h1 : vB V e i = 1 := Subtype.ext h
  have h2 : e (vB V e i) = 1 := by rw [h1, map_one]
  rw [e_vB] at h2
  exact absurd h2 (by fin_cases i <;> decide)

/-- `σ` is a nontrivial automorphism of `V`. -/
lemma tauV_ne_one (e : ↥V ≃* M3) : tauV V e ≠ 1 := by
  intro h
  have h2 : tauV V e (vB V e 1) = vB V e 1 := by rw [h, MulAut.one_apply]
  rw [tauV_vB_one] at h2
  have h3 : (vB V e 0 : G) * (vB V e 1 : G) = (vB V e 1 : G) := by
    simpa using congrArg (fun x : ↥V => (x : G)) h2
  have h4 : (vB V e 0 : G) * (vB V e 1 : G) = 1 * (vB V e 1 : G) := by
    rw [one_mul]; exact h3
  exact vB_ne_one V e 0 (mul_right_cancel h4)

lemma sigmaV_ne_one (e : ↥V ≃* M3) : sigmaV V e ≠ 1 := by
  intro h
  have h2 : sigmaV V e (vB V e 2) = vB V e 2 := by rw [h, MulAut.one_apply]
  rw [sigmaV_vB_two] at h2
  have h3 : (vB V e 1 : G) * (vB V e 2 : G) = (vB V e 2 : G) := by
    simpa using congrArg (fun x : ↥V => (x : G)) h2
  refine vB_ne_one V e 1 ?_
  have h4 : (vB V e 1 : G) * (vB V e 2 : G) = 1 * (vB V e 2 : G) := by
    rw [one_mul]; exact h3
  exact mul_right_cancel h4

/-- `(v₁v₂)(v₀v₁)v₂ = v₀` in `V`, checked in the model `(ℤ/2)³`. -/
lemma vB_relation (e : ↥V ≃* M3) :
    ((vB V e 1 : G) * (vB V e 2 : G)) * ((vB V e 0 : G) * (vB V e 1 : G)) * (vB V e 2 : G)
      = (vB V e 0 : G) := by
  have h' : (vB V e 1 * vB V e 2) * (vB V e 0 * vB V e 1) * vB V e 2 = vB V e 0 := by
    apply e.injective
    simp only [map_mul, e_vB]
    exact (by decide : (stdB 1 * stdB 2 : M3) * (stdB 0 * stdB 1) * stdB 2 = stdB 0)
  simpa using congrArg (fun y : ↥V => (y : G)) h'

/-- The element `v₀ ∈ V` is the square of the transvection `s` in the source's computation. -/
lemma vB_zero_sq (e : ↥V ≃* M3) :
    ((vB V e 0 : G) * (vB V e 0 : G)) = 1 := by
  have h' : (vB V e 0) * (vB V e 0) = 1 := by
    apply e.injective
    rw [map_mul, map_one, e_vB]
    exact (by decide : (stdB 0 : M3) * stdB 0 = 1)
  simpa using congrArg (fun y : ↥V => (y : G)) h'

/-! ## The contradiction -/

/-- `e` intertwines `σ_V` with `σ_M`. -/
@[simp] lemma e_sigmaV (e : ↥V ≃* M3) (x : ↥V) : e (sigmaV V e x) = sigmaM (e x) := by
  simp [sigmaV]

/-- `e` intertwines `τ_V` with `τ_M`. -/
@[simp] lemma e_tauV (e : ↥V ≃* M3) (x : ↥V) : e (tauV V e x) = tauM (e x) := by
  simp [tauV]

/-- Transport of powers of the product `σ_V τ_V` to the model. -/
lemma e_comp_pow (e : ↥V ≃* M3) (f g : MulAut ↥V)
    (hf : ∀ x : ↥V, e (f x) = sigmaM (e x)) (hg : ∀ x : ↥V, e (g x) = tauM (e x))
    (n : ℕ) (x : ↥V) : e (((f * g) ^ n) x) = ((sigmaM * tauM) ^ n) (e x) := by
  induction n generalizing x with
  | zero => simp
  | succ n ih =>
      calc e (((f * g) ^ (n + 1)) x)
          = e (((f * g) ^ n) ((f * g) x)) := by rw [pow_succ, MulAut.mul_apply]
        _ = ((sigmaM * tauM) ^ n) (e ((f * g) x)) := ih ((f * g) x)
        _ = ((sigmaM * tauM) ^ n) ((sigmaM * tauM) (e x)) := by
              rw [MulAut.mul_apply, hf, hg, MulAut.mul_apply]
        _ = ((sigmaM * tauM) ^ (n + 1)) (e x) := by
              simp only [pow_succ, MulAut.mul_apply]

lemma sigmaV_mul_tauV_pow_four (e : ↥V ≃* M3) :
    (sigmaV V e * tauV V e) ^ 4 = 1 := by
  apply MulEquiv.ext
  intro x
  apply e.injective
  rw [MulAut.one_apply,
    e_comp_pow (V := V) e (sigmaV V e) (tauV V e) (fun y => e_sigmaV V e y)
      (fun y => e_tauV V e y) 4 x,
    sigmaM_mul_tauM_pow_four, MulAut.one_apply]

lemma sigmaV_mul_tauV_pow_two_ne_one (e : ↥V ≃* M3) :
    (sigmaV V e * tauV V e) ^ 2 ≠ 1 := by
  intro h
  apply sigmaM_mul_tauM_pow_two_ne_one
  apply MulEquiv.ext
  intro y
  have h1 : e (((sigmaV V e * tauV V e) ^ 2) (e.symm y)) = y := by
    rw [h, MulAut.one_apply, MulEquiv.apply_symm_apply]
  rw [e_comp_pow (V := V) e (sigmaV V e) (tauV V e) (fun y => e_sigmaV V e y)
      (fun y => e_tauV V e y) 2 (e.symm y), MulEquiv.apply_symm_apply] at h1
  rw [h1, MulAut.one_apply]

/-- `(τ_V σ_V)² ≠ 1` (the product in the reverse order of `σ_V τ_V`). -/
lemma tauV_mul_sigmaV_pow_two_ne_one (e : ↥V ≃* M3) :
    (tauV V e * sigmaV V e) ^ 2 ≠ 1 := by
  intro h
  apply sigmaV_mul_tauV_pow_two_ne_one V e
  have key : (sigmaV V e * tauV V e) ^ 2
      = (tauV V e)⁻¹ * (tauV V e * sigmaV V e) ^ 2 * (tauV V e) := by
    rw [pow_two, pow_two]
    group
  rw [key, h]
  simp

lemma sigmaV_mul_tauV_fixed (e : ↥V ≃* M3) {x : ↥V}
    (h : (sigmaV V e * tauV V e) x = x) : x = 1 ∨ x = vB V e 0 := by
  have h1 : (sigmaM * tauM) (e x) = e x := by
    have h2 := congrArg e h
    rwa [MulAut.mul_apply, e_sigmaV, e_tauV] at h2
  rcases sigmaM_mul_tauM_fixed _ h1 with h2 | h2
  · left
    apply e.injective
    rw [h2, map_one]
  · right
    apply e.injective
    rw [h2, e_vB]

/-- In a `2`-group `C` with `Ω₁(C) = V`, every non-identity element of `C` has a power of
`2`-power order lying in `V#`. -/
lemma exists_pow_two_pow_mem_V (V C : Subgroup G) (hC2 : IsPGroup 2 ↥C)
    (hinv : ∀ x ∈ C, orderOf x = 2 → x ∈ V) {x : G} (hx : x ∈ C) (hx1 : x ≠ 1) :
    ∃ k : ℕ, x ^ (2 ^ k) ∈ V ∧ x ^ (2 ^ k) ≠ 1 := by
  obtain ⟨n, hn⟩ := hC2 ⟨x, hx⟩
  have hxpow : x ^ (2 ^ n) = 1 := by
    simpa using congrArg (fun y : ↥C => (y : G)) hn
  have hdvd : orderOf x ∣ 2 ^ n := orderOf_dvd_iff_pow_eq_one.mpr hxpow
  obtain ⟨j, hjn, hj⟩ := (Nat.dvd_prime_pow (by norm_num : Nat.Prime 2)).mp hdvd
  have hjpos : 1 ≤ j := by
    rcases Nat.eq_zero_or_pos j with h | h
    · exfalso
      rw [h, pow_zero] at hj
      exact hx1 (orderOf_eq_one_iff.mp hj)
    · exact h
  have hlt : 2 ^ (j - 1) < 2 ^ j := Nat.pow_lt_pow_right (by norm_num) (by omega)
  have hordpow : x ^ orderOf x = 1 := orderOf_dvd_iff_pow_eq_one.mp (dvd_refl (orderOf x))
  have hmain : x ^ 2 ^ (j - 1) ≠ 1 := by
    intro hcon
    have hle : orderOf x ≤ 2 ^ (j - 1) :=
      Nat.le_of_dvd (by positivity) (orderOf_dvd_iff_pow_eq_one.mpr hcon)
    rw [hj] at hle
    omega
  have hstep : (x ^ 2 ^ (j - 1)) ^ 2 = x ^ (2 ^ j) := by
    have hexp : 2 ^ (j - 1) + 2 ^ (j - 1) = 2 ^ j := by
      have h2 : 2 ^ (j - 1) * 2 = 2 ^ j := by
        rw [← pow_succ]
        congr 1
        omega
      omega
    rw [pow_two, ← pow_add, hexp]
  have hmem : x ^ 2 ^ (j - 1) ∈ V := by
    refine hinv _ (C.pow_mem hx _) (orderOf_eq_prime ?_ hmain)
    rw [hstep, ← hj]
    exact hordpow
  exact ⟨j - 1, hmem, hmain⟩

/-- In `ZMod n` with `n ≠ 0`, the canonical representative of `-1` is `n - 1`. -/
lemma zmod_neg_one_val {n : ℕ} [NeZero n] : ((-1 : ZMod n)).val = n - 1 := by
  have hn : 0 < n := Nat.pos_of_ne_zero (NeZero.ne n)
  have h1 : ((-1 : ZMod n)) = ((n - 1 : ℕ) : ZMod n) := by
    rw [Nat.cast_sub (show 1 ≤ n by omega), Nat.cast_one, ZMod.natCast_self, zero_sub]
  rw [h1, ZMod.val_natCast]
  exact Nat.mod_eq_of_lt (by omega)

/-- `c ^ ((-1 : ZMod n)).val = c⁻¹` when `c ^ n = 1`. -/
lemma pow_zmod_neg_one {G : Type*} [Group G] {n : ℕ} [NeZero n] (c : G) (hc : c ^ n = 1) :
    c ^ ((-1 : ZMod n)).val = c⁻¹ := by
  have hn : 0 < n := Nat.pos_of_ne_zero (NeZero.ne n)
  rw [zmod_neg_one_val]
  refine eq_inv_of_mul_eq_one_right ?_
  rw [← pow_succ', show n - 1 + 1 = n by omega, hc]

/-- If `a * b = 1` then `a = b⁻¹`. -/
lemma eq_inv_of_mul_eq_one_of {G : Type*} [Group G] {a b : G} (h : a * b = 1) : a = b⁻¹ := by
  calc a = a * 1 := (mul_one a).symm
    _ = a * (b * b⁻¹) := by rw [mul_inv_cancel]
    _ = (a * b) * b⁻¹ := by rw [mul_assoc]
    _ = 1 * b⁻¹ := by rw [h]
    _ = b⁻¹ := one_mul _

/-- Every element of the cyclic subgroup generated by `d` (of finite order) is a non-negative
power of `d`, with exponent less than `orderOf d`. -/
lemma exists_pow_eq_of_mem_zpowers {G : Type*} [Group G] {d x : G} (hpos : 0 < orderOf d)
    (h : x ∈ Subgroup.zpowers d) : ∃ k : ℕ, k < orderOf d ∧ d ^ k = x := by
  obtain ⟨n, hn⟩ := Subgroup.mem_zpowers_iff.mp h
  have hcast : (0 : ℤ) < (orderOf d : ℤ) := by exact_mod_cast hpos
  have h0 : 0 ≤ n % (orderOf d : ℤ) := Int.emod_nonneg n (by omega)
  have h1 : n % (orderOf d : ℤ) < (orderOf d : ℤ) := Int.emod_lt_of_pos n (by omega)
  have h2 : (n % (orderOf d : ℤ)).toNat < orderOf d := by omega
  refine ⟨(n % (orderOf d : ℤ)).toNat, h2, ?_⟩
  rw [← hn, ← zpow_natCast, zpow_eq_zpow_iff_modEq, Int.toNat_of_nonneg h0]
  exact Int.emod_emod n (orderOf d)

/-- The `2^{m-1}`-th power of a coordinate product, in terms of the parity of the coordinates. -/
lemma phi_pow_two_pow' {G : Type*} [Group G] [Finite G] {C : Subgroup G}
    (hCab : ∀ x ∈ C, ∀ y ∈ C, x * y = y * x) {m : ℕ} {c : Fin 3 → G} (hc : ∀ i, c i ∈ C)
    {v : Fin 3 → G} (hcv : ∀ i, (c i) ^ 2 ^ (m - 1) = v i) (hv2 : ∀ i, (v i) * (v i) = 1)
    (x : Fin 3 → ZMod (2 ^ m)) :
    (Phi c x) ^ (2 ^ (m - 1))
      = (v 0) ^ ((x 0).val % 2) * (v 1) ^ ((x 1).val % 2) * (v 2) ^ ((x 2).val % 2) := by
  have hc01 : Commute (c 0) (c 1) := (commute_iff_eq _ _).mpr (hCab _ (hc 0) _ (hc 1))
  have hc02 : Commute (c 0) (c 2) := (commute_iff_eq _ _).mpr (hCab _ (hc 0) _ (hc 2))
  have hc12 : Commute (c 1) (c 2) := (commute_iff_eq _ _).mpr (hCab _ (hc 1) _ (hc 2))
  have e0 : (c 0 ^ (x 0).val) ^ (2 ^ (m - 1)) = (v 0) ^ ((x 0).val % 2) := by
    rw [show (c 0 ^ (x 0).val) ^ (2 ^ (m - 1)) = (c 0 ^ (2 ^ (m - 1))) ^ (x 0).val by
        rw [← pow_mul, ← pow_mul, mul_comm], hcv 0]
    exact pow_eq_pow_mod_two (hv2 0) ((x 0).val)
  have e1 : (c 1 ^ (x 1).val) ^ (2 ^ (m - 1)) = (v 1) ^ ((x 1).val % 2) := by
    rw [show (c 1 ^ (x 1).val) ^ (2 ^ (m - 1)) = (c 1 ^ (2 ^ (m - 1))) ^ (x 1).val by
        rw [← pow_mul, ← pow_mul, mul_comm], hcv 1]
    exact pow_eq_pow_mod_two (hv2 1) ((x 1).val)
  have e2 : (c 2 ^ (x 2).val) ^ (2 ^ (m - 1)) = (v 2) ^ ((x 2).val % 2) := by
    rw [show (c 2 ^ (x 2).val) ^ (2 ^ (m - 1)) = (c 2 ^ (2 ^ (m - 1))) ^ (x 2).val by
        rw [← pow_mul, ← pow_mul, mul_comm], hcv 2]
    exact pow_eq_pow_mod_two (hv2 2) ((x 2).val)
  have hcomm_a : Commute (c 0 ^ (x 0).val) (c 1 ^ (x 1).val * c 2 ^ (x 2).val) :=
    ((hc01.pow_left (x 0).val).pow_right (x 1).val).mul_right
      ((hc02.pow_left (x 0).val).pow_right (x 2).val)
  have hcomm_b : Commute (c 1 ^ (x 1).val) (c 2 ^ (x 2).val) :=
    (hc12.pow_left (x 1).val).pow_right (x 2).val
  calc (Phi c x) ^ (2 ^ (m - 1))
      = (c 0 ^ (x 0).val * (c 1 ^ (x 1).val * c 2 ^ (x 2).val)) ^ (2 ^ (m - 1)) := by
        rw [show Phi c x = c 0 ^ (x 0).val * c 1 ^ (x 1).val * c 2 ^ (x 2).val from rfl,
          mul_assoc]
    _ = (c 0 ^ (x 0).val) ^ (2 ^ (m - 1))
          * ((c 1 ^ (x 1).val * c 2 ^ (x 2).val) ^ (2 ^ (m - 1))) := hcomm_a.mul_pow _
    _ = (c 0 ^ (x 0).val) ^ (2 ^ (m - 1))
          * ((c 1 ^ (x 1).val) ^ (2 ^ (m - 1)) * (c 2 ^ (x 2).val) ^ (2 ^ (m - 1))) := by
        rw [hcomm_b.mul_pow]
    _ = (v 0) ^ ((x 0).val % 2)
          * ((v 1) ^ ((x 1).val % 2) * (v 2) ^ ((x 2).val % 2)) := by rw [e0, e1, e2]
    _ = (v 0) ^ ((x 0).val % 2) * (v 1) ^ ((x 1).val % 2) * (v 2) ^ ((x 2).val % 2) := by
        rw [mul_assoc]

/-- Injectivity of the coordinate map, from the independence of the `2^{m-1}`-th powers. -/
lemma Phi_injective_of {G : Type*} [Group G] [Finite G] (V C : Subgroup G) (hVC : V ≤ C)
    (hOmega : ∀ x : G, x ∈ C → (x * x = 1 ↔ x ∈ V))
    (hCab : ∀ x ∈ C, ∀ y ∈ C, x * y = y * x) {m : ℕ} (hm : 1 ≤ m) {c : Fin 3 → G}
    (hc : ∀ i, c i ∈ C) (hpow : ∀ i, (c i) ^ (2 ^ m) = 1) {v : Fin 3 → G} (hv : ∀ i, v i ∈ V)
    (hcv : ∀ i, (c i) ^ 2 ^ (m - 1) = v i)
    (hind : ∀ a b d : ℕ, a < 2 → b < 2 → d < 2 → (v 0) ^ a * (v 1) ^ b * (v 2) ^ d = 1 →
      a = 0 ∧ b = 0 ∧ d = 0) :
    Function.Injective (Phi (n := 2 ^ m) c) := by
  have hpd := pow_independent V C hVC hOmega hCab hm (hc 0) (hc 1) (hc 2) (hv 0) (hv 1) (hv 2)
    (hcv 0) (hcv 1) (hcv 2) hind
  have hzero : ∀ z : Fin 3 → ZMod (2 ^ m), Phi (n := 2 ^ m) c z = 1 → z = 0 := by
    intro z hz
    have h1 : c 0 ^ (z 0).val * c 1 ^ (z 1).val * c 2 ^ (z 2).val = 1 := hz
    obtain ⟨h0, h1', h2'⟩ := hpd (z 0).val (z 1).val (z 2).val (ZMod.val_lt _) (ZMod.val_lt _)
      (ZMod.val_lt _) h1
    funext i
    have hcase : i = 0 ∨ i = 1 ∨ i = 2 := by fin_cases i <;> simp
    rcases hcase with h | h | h
    · rw [h]; exact (ZMod.val_eq_zero (z 0)).mp h0
    · rw [h]; exact (ZMod.val_eq_zero (z 1)).mp h1'
    · rw [h]; exact (ZMod.val_eq_zero (z 2)).mp h2'
  intro x yw hxy
  have h1 : Phi (n := 2 ^ m) c (x - yw) = 1 := by
    have h2 : Phi (n := 2 ^ m) c (x - yw) * Phi (n := 2 ^ m) c yw
        = 1 * Phi (n := 2 ^ m) c yw := by
      rw [one_mul, phi_mul hCab hc hpow (x - yw) yw, sub_add_cancel, hxy]
    exact mul_right_cancel h2
  have h3 : x - yw = 0 := hzero _ h1
  funext i
  have h4 := congrFun h3 i
  exact sub_eq_zero.mp (by simpa using h4)

/-- `c ^ (a * b).val = (c ^ a.val) ^ b.val` when `c ^ N = 1`. -/
lemma pow_val_mul_aux {G : Type*} [Group G] {N : ℕ} [NeZero N] (c : G) (hc : c ^ N = 1)
    (a b : ZMod N) : c ^ (a * b).val = (c ^ a.val) ^ b.val := by
  rw [← pow_mul]
  refine pow_eq_pow_of_modEq ?_ hc
  rw [ZMod.val_mul]
  show (a.val * b.val % N) % N = a.val * b.val % N
  exact Nat.mod_mod _ _

/-- `c ^ (a - 1).val = c ^ a.val * c⁻¹` when `c ^ N = 1` and `1 < N`. -/
lemma pow_val_sub_one {G : Type*} [Group G] {N : ℕ} [NeZero N] (c : G) (hc : c ^ N = 1)
    (hN : 1 < N) (a : ZMod N) : c ^ (a - 1).val = c ^ a.val * c⁻¹ := by
  have h1 : c ^ ((a - 1).val + 1) = c ^ a.val := by
    refine pow_eq_pow_of_modEq ?_ hc
    have h2 : ((a - 1) + 1 : ZMod N) = a := by ring
    have h3 := ZMod.val_add (a - 1) (1 : ZMod N)
    rw [h2] at h3
    have h4 : ((1 : ZMod N)).val = 1 := by
      rw [show (1 : ZMod N) = ((1 : ℕ) : ZMod N) by norm_num, ZMod.val_natCast]
      exact Nat.mod_eq_of_lt hN
    rw [h4] at h3
    rw [h3]
    exact (Nat.mod_mod _ _).symm
  calc c ^ (a - 1).val = c ^ (a - 1).val * 1 := (mul_one _).symm
    _ = c ^ (a - 1).val * (c * c⁻¹) := by rw [mul_inv_cancel]
    _ = (c ^ (a - 1).val * c) * c⁻¹ := by rw [mul_assoc]
    _ = c ^ ((a - 1).val + 1) * c⁻¹ := by rw [← pow_succ]
    _ = c ^ a.val * c⁻¹ := by rw [h1]

set_option maxHeartbeats 1600000 in
/-- **Peterfalvi I §3, Proposition 2 (the computation).**  In the configuration, if all
involutions of `G` lie in `C = C_G(V)` and some element of `G∖C` has square a non-identity
element of `V`, then `False`. -/
theorem abelian_contra (V C : Subgroup G) [V.Normal] (hcard : Nat.card V = 8)
    (hexp : ∀ x ∈ V, x * x = 1) (hC : C = Subgroup.centralizer ((V : Set G)))
    (hC2 : IsPGroup 2 ↥C) (hinv : ∀ x ∈ C, orderOf x = 2 → x ∈ V)
    (hAut : ActsAsAut V (inferInstance : V.Normal))
    (hCab : ∀ x ∈ C, ∀ y ∈ C, x * y = y * x)
    (hout : ∀ u : G, orderOf u = 2 → u ∈ C)
    (hwit : ∃ x : G, x ∉ C ∧ x * x ∈ V ∧ x * x ≠ 1) : False := by
  classical
  have hVleC : V ≤ C := V_le_C V C hC hexp
  have hCn : C.Normal := C_normal V C inferInstance hC
  have hexp' : ∀ x : ↥V, x * x = 1 := fun x => Subtype.ext (by simpa using hexp x x.2)
  obtain ⟨e⟩ := Work.Hering.Step5.iso_fin3 hcard hexp'
  -- ## the transvections `s` (adjusted and normalized) and `t`
  obtain ⟨s₀, hs₀⟩ := conjNormal_eq_of_hAut (V := V) hAut (sigmaV V e)
  obtain ⟨t, ht⟩ := conjNormal_eq_of_hAut (V := V) hAut (tauV V e)
  have hs₀eq : MulAut.conjNormal s₀ = sigmaV V e := by
    apply MulEquiv.ext
    intro x
    exact (hs₀ x).symm
  have hs₀conj : ∀ x : ↥V, s₀ * (x : G) * s₀⁻¹ = (sigmaV V e x : G) := by
    intro x
    have h1 := congrArg (fun (f : MulAut ↥V) => (f x : G)) hs₀eq
    rw [MulAut.conjNormal_apply] at h1
    exact h1
  have hs₀sqC : s₀ * s₀ ∈ C := by
    apply mem_C_of_conjNormal_eq_one V C hC
    intro x
    rw [map_mul, hs₀eq, MulAut.mul_apply, ← MulAut.mul_apply, sigmaV_mul_self, MulAut.one_apply]
  have hs₀C : s₀ ∉ C := by
    intro h
    have h1 : ∀ x : ↥V, MulAut.conjNormal s₀ x = x := by
      intro x
      apply Subtype.ext
      rw [MulAut.conjNormal_apply]
      have hcv : (x : G) * s₀ = s₀ * (x : G) := (mem_C_iff V C hC s₀).mp h (x : G) x.2
      calc s₀ * (x : G) * s₀⁻¹ = ((x : G) * s₀) * s₀⁻¹ := by rw [← hcv]
        _ = (x : G) := by group
    have h2 : sigmaV V e = 1 := by
      rw [← hs₀eq]
      apply MulEquiv.ext
      intro x
      exact h1 x
    exact sigmaV_ne_one V e h2
  obtain ⟨c, hcC, hsc2V, hsc2ne⟩ :=
    adjust_witness V C inferInstance hcard hexp hC hAut hwit hs₀C hs₀sqC
  set s : G := s₀ * c with hsdef
  have hs2V : s * s ∈ V := by rw [hsdef]; exact hsc2V
  have hs2ne : s * s ≠ 1 := by rw [hsdef]; exact hsc2ne
  have hsσ : ∀ x : ↥V, sigmaV V e x = MulAut.conjNormal s x := by
    intro x
    rw [hsdef]
    have hcx : MulAut.conjNormal c x = x := by
      apply Subtype.ext
      rw [MulAut.conjNormal_apply]
      have hcv : (x : G) * c = c * (x : G) := (mem_C_iff V C hC c).mp hcC (x : G) x.2
      calc c * (x : G) * c⁻¹ = ((x : G) * c) * c⁻¹ := by rw [← hcv]
        _ = (x : G) := by group
    rw [map_mul, MulAut.mul_apply, hs₀ x, hcx]
  have hsconj : ∀ x : ↥V, s * (x : G) * s⁻¹ = (sigmaV V e x : G) := by
    intro x
    have h1 := congrArg (fun y : ↥V => (y : G)) (hsσ x)
    rw [MulAut.conjNormal_apply] at h1
    exact h1.symm
  have hsC : s ∉ C := by
    intro h
    apply hs₀C
    have h2 : s₀ = s * c⁻¹ := by rw [hsdef]; group
    rw [h2]
    exact C.mul_mem h (C.inv_mem hcC)
  have hs2fix : sigmaV V e ⟨s * s, hs2V⟩ = ⟨s * s, hs2V⟩ := by
    rw [hsσ]
    apply Subtype.ext
    rw [MulAut.conjNormal_apply]
    show s * (s * s) * s⁻¹ = s * s
    group
  have hs2fixedM : sigmaM (e ⟨s * s, hs2V⟩) = e ⟨s * s, hs2V⟩ := by
    have h2 := congrArg e hs2fix
    simpa [sigmaV] using h2
  have hsq_cancel : ((vB V e 1 : G) * (vB V e 2 : G)) * (vB V e 2 : G) = (vB V e 1 : G) := by
    have h' : (vB V e 1 * vB V e 2) * vB V e 2 = vB V e 1 := by
      apply e.injective
      simp only [map_mul, e_vB]
      exact (by decide : (stdB 1 * stdB 2 : M3) * stdB 2 = stdB 1)
    simpa using congrArg (fun y : ↥V => (y : G)) h'
  have hv1conj : ∀ s1 : G, (∀ x : ↥V, sigmaV V e x = MulAut.conjNormal s1 x) →
      s1 * (vB V e 2 : G) * s1⁻¹ = (vB V e 1 : G) * (vB V e 2 : G) := by
    intro s1 hs1
    have h1 := congrArg (fun (f : MulAut ↥V) => (f (vB V e 2) : G))
      (MulEquiv.ext (fun x => (hs1 x).symm))
    rw [MulAut.conjNormal_apply, sigmaV_vB_two] at h1
    simpa using h1
  -- exclude `e ⟨s²⟩ = 1` and `e ⟨s²⟩ = stdB 1`
  have hs2cases : e ⟨s * s, hs2V⟩ = stdB 0 ∨ e ⟨s * s, hs2V⟩ = stdB 0 * stdB 1 := by
    rcases sigmaM_fixed _ hs2fixedM with h | h | h | h
    · exfalso
      exact hs2ne (by
        have : (⟨s * s, hs2V⟩ : ↥V) = 1 := by
          apply e.injective
          rw [h, map_one]
        simpa using congrArg (fun y : ↥V => (y : G)) this)
    · exact Or.inl h
    · exfalso
      have hsq : s * s = (vB V e 1 : G) := by
        have : (⟨s * s, hs2V⟩ : ↥V) = vB V e 1 := by
          apply e.injective
          rw [h, e_vB]
        simpa using congrArg (fun y : ↥V => (y : G)) this
      exact constraint_step1 C hCn hout hsC (hVleC hs2V)
        ⟨(vB V e 2 : G), hVleC (vB V e 2).2, by
          calc s * (vB V e 2 : G) * s⁻¹ * (vB V e 2 : G)
              = ((vB V e 1 : G) * (vB V e 2 : G)) * (vB V e 2 : G) := by rw [hv1conj s hsσ]
            _ = (vB V e 1 : G) := hsq_cancel
            _ = s * s := hsq.symm⟩
    · exact Or.inr h
  -- the normalized transvection `s₁` with `s₁ * s₁ = v₀`
  obtain ⟨s₁, hs₁σ, hs₁sq⟩ : ∃ s₁ : G,
      (∀ x : ↥V, sigmaV V e x = MulAut.conjNormal s₁ x) ∧ s₁ * s₁ = (vB V e 0 : G) := by
    rcases hs2cases with h | h
    · refine ⟨s, hsσ, ?_⟩
      have : (⟨s * s, hs2V⟩ : ↥V) = vB V e 0 := by
        apply e.injective
        rw [h, e_vB]
      simpa using congrArg (fun y : ↥V => (y : G)) this
    · refine ⟨s * (vB V e 2 : G), ?_, ?_⟩
      · intro x
        rw [hsσ x]
        apply Subtype.ext
        rw [MulAut.conjNormal_apply, MulAut.conjNormal_apply]
        have hv2x : (vB V e 2 : G) * (x : G) = (x : G) * (vB V e 2 : G) :=
          V_comm V hexp (vB V e 2).2 x.2
        have hconj : (vB V e 2 : G) * (x : G) * (vB V e 2 : G)⁻¹ = (x : G) := by
          rw [hv2x]; group
        have key : (s * (vB V e 2 : G)) * (x : G) * (s * (vB V e 2 : G))⁻¹ = s * (x : G) * s⁻¹ := by
          calc (s * (vB V e 2 : G)) * (x : G) * (s * (vB V e 2 : G))⁻¹
              = s * ((vB V e 2 : G) * (x : G) * (vB V e 2 : G)⁻¹) * s⁻¹ := by group
            _ = s * (x : G) * s⁻¹ := by rw [hconj]
        exact key.symm
      · have hsq : s * s = (vB V e 0 : G) * (vB V e 1 : G) := by
          have h' : (⟨s * s, hs2V⟩ : ↥V) = vB V e 0 * vB V e 1 := by
            apply e.injective
            rw [h, map_mul, e_vB, e_vB]
          simpa using congrArg (fun y : ↥V => (y : G)) h'
        calc (s * (vB V e 2 : G)) * (s * (vB V e 2 : G))
            = (s * (vB V e 2 : G) * s⁻¹) * (s * s) * (vB V e 2 : G) := by group
          _ = ((vB V e 1 : G) * (vB V e 2 : G)) * ((vB V e 0 : G) * (vB V e 1 : G))
                * (vB V e 2 : G) := by rw [hv1conj s hsσ, hsq]
          _ = (vB V e 0 : G) := vB_relation V e
  -- the transvection `t` has square in `C`
  have ht2C : t * t ∈ C := by
    apply mem_C_of_conjNormal_eq_one V C hC
    intro x
    rw [map_mul, MulAut.mul_apply, ← ht x, ← ht (tauV V e x), ← MulAut.mul_apply, tauV_mul_self,
      MulAut.one_apply]
  -- ## the element `a = s₁ t`, `b = a²`, `c₁ = a⁴ = b²`, its order `2^m`, and `(4.1)`
  have hsc : MulAut.conjNormal s₁ = sigmaV V e := by
    apply MulEquiv.ext
    intro x
    exact (hs₁σ x).symm
  have htc : MulAut.conjNormal t = tauV V e := by
    apply MulEquiv.ext
    intro x
    exact (ht x).symm
  set c₁ : G := (s₁ * t) ^ 4 with hc₁def
  set b : G := (s₁ * t) ^ 2 with hbdef
  have hb2 : b * b = c₁ := by rw [hbdef, hc₁def]; group
  have hb_eq : MulAut.conjNormal b = (sigmaV V e * tauV V e) ^ 2 := by
    rw [hbdef, map_pow, map_mul, hsc, htc]
  have hc₁_eq : MulAut.conjNormal c₁ = (sigmaV V e * tauV V e) ^ 4 := by
    rw [hc₁def, map_pow, map_mul, hsc, htc]
  have hconjC : ∀ g : G, (∀ x : ↥V, MulAut.conjNormal g x = x) → g ∈ C :=
    fun g hg => mem_C_of_conjNormal_eq_one V C hC hg
  have hc₁C : c₁ ∈ C :=
    hconjC c₁ (by
      intro x
      rw [hc₁_eq, sigmaV_mul_tauV_pow_four, MulAut.one_apply])
  have hbC : b ∉ C := by
    intro h
    have h1 : (sigmaV V e * tauV V e) ^ 2 = 1 := by
      rw [← hb_eq]
      apply MulEquiv.ext
      intro x
      apply Subtype.ext
      rw [MulAut.conjNormal_apply, MulAut.one_apply]
      have hcv : (x : G) * b = b * (x : G) := (mem_C_iff V C hC b).mp h (x : G) x.2
      calc b * (x : G) * b⁻¹ = ((x : G) * b) * b⁻¹ := by rw [← hcv]
        _ = (x : G) := by group
    exact sigmaV_mul_tauV_pow_two_ne_one V e h1
  have hb1 : b ≠ 1 := fun h => hbC (by rw [h]; exact C.one_mem)
  have hc₁ne : c₁ ≠ 1 := by
    intro h
    have h2 : b * b = 1 := by rw [hb2, h]
    have hord : orderOf b = 2 := orderOf_eq_prime (by rw [pow_two]; exact h2) hb1
    exact hbC (hout b hord)
  obtain ⟨n, hn⟩ := hC2 ⟨c₁, hc₁C⟩
  have hc₁pow : c₁ ^ (2 ^ n) = 1 := by
    simpa using congrArg (fun y : ↥C => (y : G)) hn
  obtain ⟨m, hmle, hmn⟩ : ∃ m, m ≤ n ∧ orderOf c₁ = 2 ^ m := by
    have hdvd : orderOf c₁ ∣ 2 ^ n := orderOf_dvd_iff_pow_eq_one.mpr hc₁pow
    exact (Nat.dvd_prime_pow (by norm_num : Nat.Prime 2)).mp hdvd
  have hm1 : 1 ≤ m := by
    rcases Nat.eq_zero_or_pos m with h | h
    · exfalso
      rw [h, pow_zero] at hmn
      exact hc₁ne (orderOf_eq_one_iff.mp hmn)
    · exact h
  have hc₁powm : c₁ ^ (2 ^ m) = 1 := by
    rw [← hmn]
    exact orderOf_dvd_iff_pow_eq_one.mp (dvd_refl (orderOf c₁))
  have hhalf_ne : c₁ ^ 2 ^ (m - 1) ≠ 1 := by
    intro h
    have hdvd : orderOf c₁ ∣ 2 ^ (m - 1) := orderOf_dvd_iff_pow_eq_one.mpr h
    have hle : 2 ^ m ≤ 2 ^ (m - 1) := by
      rw [← hmn]
      exact Nat.le_of_dvd (by positivity) hdvd
    have hlt : 2 ^ (m - 1) < 2 ^ m :=
      Nat.pow_lt_pow_right (by norm_num) (by omega)
    omega
  have hhalf_sq : (c₁ ^ 2 ^ (m - 1)) * (c₁ ^ 2 ^ (m - 1)) = 1 := by
    rw [← pow_two, ← pow_mul,
      show 2 ^ (m - 1) * 2 = 2 ^ m by rw [← pow_succ]; congr 1; omega, hc₁powm]
  have hhalfV : c₁ ^ 2 ^ (m - 1) ∈ V :=
    hinv _ (C.pow_mem hc₁C _) (orderOf_eq_prime (by rw [pow_two]; exact hhalf_sq) hhalf_ne)
  have hhalf_fixed : (s₁ * t) * (c₁ ^ 2 ^ (m - 1)) * (s₁ * t)⁻¹ = c₁ ^ 2 ^ (m - 1) := by
    have hpow : ∀ k : ℕ, (s₁ * t) * (s₁ * t) ^ k * (s₁ * t)⁻¹ = (s₁ * t) ^ k := by
      intro k
      rw [← pow_succ', pow_succ, mul_assoc, mul_inv_cancel, mul_one]
    have hc₁pow' : c₁ ^ 2 ^ (m - 1) = (s₁ * t) ^ (4 * 2 ^ (m - 1)) := by
      show ((s₁ * t) ^ 4) ^ (2 ^ (m - 1)) = (s₁ * t) ^ (4 * 2 ^ (m - 1))
      rw [pow_mul]
    rw [hc₁pow', hpow]
  have hfixV : (sigmaV V e * tauV V e) ⟨c₁ ^ 2 ^ (m - 1), hhalfV⟩
      = ⟨c₁ ^ 2 ^ (m - 1), hhalfV⟩ := by
    rw [← hsc, ← htc, ← map_mul]
    apply Subtype.ext
    rw [MulAut.conjNormal_apply]
    exact hhalf_fixed
  have hc₁half : c₁ ^ 2 ^ (m - 1) = (vB V e 0 : G) := by
    rcases sigmaV_mul_tauV_fixed V e hfixV with h | h
    · exact absurd (by simpa using congrArg (fun y : ↥V => (y : G)) h) hhalf_ne
    · simpa using congrArg (fun y : ↥V => (y : G)) h
  have hm2 : 2 ≤ m := by
    rcases lt_or_ge m 2 with h | h
    · exfalso
      have hm1' : m = 1 := by omega
      have hc₁eq : c₁ = (vB V e 0 : G) := by
        have h := hc₁half
        rw [hm1', show 2 ^ (1 - 1) = 1 by norm_num, pow_one] at h
        exact h
      have hb3 : b * (vB V e 2 : G) * b⁻¹ = (vB V e 0 : G) * (vB V e 2 : G) := by
        have h1 := hb_eq
        have h2 : b * (vB V e 2 : G) * b⁻¹
            = (((sigmaV V e * tauV V e) ^ 2) (vB V e 2) : G) := by
          rw [← h1]
          rfl
        rw [h2]
        have h3 : ((sigmaV V e * tauV V e) ^ 2) (vB V e 2)
            = vB V e 0 * vB V e 2 := by
          apply e.injective
          rw [e_comp_pow (V := V) e (sigmaV V e) (tauV V e) (fun y => e_sigmaV V e y)
            (fun y => e_tauV V e y) 2 (vB V e 2), e_vB, map_mul, e_vB, e_vB]
          exact sigmaM_mul_tauM_sq_stdB_two
        rw [h3]
        rfl
      refine constraint_step1 C hCn hout hbC (hVleC ?_) ⟨(vB V e 2 : G), hVleC (vB V e 2).2, ?_⟩
      · rw [hb2, hc₁eq]; exact (vB V e 0).2
      · calc b * (vB V e 2 : G) * b⁻¹ * (vB V e 2 : G)
            = ((vB V e 0 : G) * (vB V e 2 : G)) * (vB V e 2 : G) := by rw [hb3]
          _ = (vB V e 0 : G) := by
                rw [mul_assoc,
                  show (vB V e 2 : G) * (vB V e 2 : G) = 1 from hexp _ (vB V e 2).2, mul_one]
          _ = b * b := by rw [hb2, hc₁eq]
    · exact h
  -- ## the transvections `s₁`, `t` and the element `c₁`
  have htrans : ∀ v ∈ V, ∀ w ∈ V, v ≠ 1 → w ≠ 1 → ∃ g : G, w = g * v * g⁻¹ :=
    trans_of_hAut V (inferInstance : V.Normal) hcard hexp hAut
  have hdesc : ∀ x ∈ C, x ≠ 1 → ∃ k : ℕ, x ^ (2 ^ k) ∈ V ∧ x ^ (2 ^ k) ≠ 1 :=
    fun x hx hx1 => exists_pow_two_pow_mem_V V C hC2 hinv hx hx1
  have hs₁C : s₁ ∉ C := by
    intro h
    have h1 : MulAut.conjNormal (H := V) s₁ = 1 := by
      apply MulEquiv.ext
      intro x
      apply Subtype.ext
      rw [MulAut.conjNormal_apply, MulAut.one_apply]
      have hcv : (x : G) * s₁ = s₁ * (x : G) := (mem_C_iff V C hC s₁).mp h (x : G) x.2
      calc s₁ * (x : G) * s₁⁻¹ = ((x : G) * s₁) * s₁⁻¹ := by rw [← hcv]
        _ = (x : G) := by group
    rw [hsc] at h1
    exact sigmaV_ne_one V e h1
  have hconstraint : ¬ ∃ c ∈ C, s₁ * c * s₁⁻¹ * c = s₁ * s₁ :=
    constraint_step1 C hCn hout hs₁C (by rw [hs₁sq]; exact hVleC (vB V e 0).2)
  have hfix : ∀ x : G, x ∈ V → s₁ * x * s₁⁻¹ = x → t * x * t⁻¹ = x →
      x = 1 ∨ x = (vB V e 0 : G) := by
    intro x hx hxs hxt
    have h1 : sigmaV V e ⟨x, hx⟩ = ⟨x, hx⟩ := by
      rw [hs₁σ]
      apply Subtype.ext
      rw [MulAut.conjNormal_apply]
      exact hxs
    have h2 : tauV V e ⟨x, hx⟩ = ⟨x, hx⟩ := by
      rw [ht]
      apply Subtype.ext
      rw [MulAut.conjNormal_apply]
      exact hxt
    have h3 : sigmaM (e ⟨x, hx⟩) = e ⟨x, hx⟩ := by
      have hh := congrArg e h1
      simpa [sigmaV] using hh
    have h4 : tauM (e ⟨x, hx⟩) = e ⟨x, hx⟩ := by
      have hh := congrArg e h2
      simpa [tauV] using hh
    rcases sigmaM_tauM_fixed _ h3 h4 with h | h
    · left
      have h5 : (⟨x, hx⟩ : ↥V) = 1 := by
        apply e.injective
        rw [h, map_one]
      simpa using congrArg (fun y : ↥V => (y : G)) h5
    · right
      have h5 : (⟨x, hx⟩ : ↥V) = vB V e 0 := by
        apply e.injective
        rw [h, e_vB]
      simpa using congrArg (fun y : ↥V => (y : G)) h5
  obtain ⟨hc₁s, hc₁t⟩ :=
    conj_c1_inv (V := V) (C := C) hCn hCab hc₁C (hVleC (vB V e 0).2) hs₁sq ht2C hc₁def
      hfix hconstraint hdesc
  -- ## the elements `c₃`, `c₂` and the action of `s₁`
  obtain ⟨c₃, hc₃C, hc₃pow⟩ :=
    pow_image_eq_V V C (inferInstance : V.Normal) hcard hexp hC hCab htrans m hc₁C
      (by rw [hc₁half]; exact (vB V e 0).2) hhalf_ne (vB V e 2) (vB V e 2).2
  set c₂ : G := s₁ * c₃ * s₁⁻¹ * c₃ with hc₂def
  have hc₂C : c₂ ∈ C :=
    C.mul_mem (hCn.conj_mem c₃ hc₃C s₁) hc₃C
  have hc₃s : s₁ * c₃ * s₁⁻¹ = c₂ * c₃⁻¹ := by
    rw [hc₂def, mul_assoc, mul_assoc]
    group
  have hc₂s : s₁ * c₂ * s₁⁻¹ = c₂ := by
    have hxmem : s₁ * c₃ * s₁⁻¹ ∈ C := hCn.conj_mem c₃ hc₃C s₁
    have hx : s₁ * (s₁ * c₃ * s₁⁻¹) * s₁⁻¹ = c₃ := by
      calc s₁ * (s₁ * c₃ * s₁⁻¹) * s₁⁻¹ = (s₁ * s₁) * c₃ * (s₁ * s₁)⁻¹ := by group
        _ = c₃ := by
              rw [hs₁sq]
              have hv := (mem_C_iff V C hC c₃).mp hc₃C (vB V e 0 : G) (vB V e 0).2
              calc (vB V e 0 : G) * c₃ * (vB V e 0 : G)⁻¹
                  = (c₃ * (vB V e 0 : G)) * (vB V e 0 : G)⁻¹ := by rw [← hv]
                _ = c₃ := by group
    calc s₁ * c₂ * s₁⁻¹
        = (s₁ * (s₁ * c₃ * s₁⁻¹) * s₁⁻¹) * (s₁ * c₃ * s₁⁻¹) := by rw [hc₂def]; group
      _ = c₃ * (s₁ * c₃ * s₁⁻¹) := by rw [hx]
      _ = (s₁ * c₃ * s₁⁻¹) * c₃ := hCab c₃ hc₃C _ hxmem
      _ = c₂ := by rw [hc₂def]
  have hc₂pow : c₂ ^ 2 ^ (m - 1) = (vB V e 1 : G) := by
    have hxmem : s₁ * c₃ * s₁⁻¹ ∈ C := hCn.conj_mem c₃ hc₃C s₁
    have hcomm : Commute (s₁ * c₃ * s₁⁻¹) c₃ :=
      (commute_iff_eq _ _).mpr (hCab _ hxmem _ hc₃C)
    rw [hc₂def, hcomm.mul_pow]
    have hx : (s₁ * c₃ * s₁⁻¹) ^ (2 ^ (m - 1)) = (vB V e 1 : G) * (vB V e 2 : G) := by
      rw [show s₁ * c₃ * s₁⁻¹ = MulAut.conj s₁ c₃ by rw [MulAut.conj_apply], ← map_pow,
        MulAut.conj_apply, hc₃pow]
      exact hv1conj s₁ hs₁σ
    rw [hx, hc₃pow, mul_assoc,
      show (vB V e 2 : G) * (vB V e 2 : G) = 1 from hexp _ (vB V e 2).2, mul_one]
  -- ## the coordinate vector `c = (c₁,c₂,c₃)` and the coordinate map `Φ`
  have hc₁2m : c₁ ^ (2 ^ m) = 1 := by
    have h : c₁ ^ (2 ^ m) = (c₁ ^ 2 ^ (m - 1)) ^ 2 := by
      rw [show 2 ^ m = 2 ^ (m - 1) * 2 by rw [← pow_succ]; congr 1; omega, pow_mul]
    rw [h, pow_two, hhalf_sq]
  have hc₂2m : c₂ ^ (2 ^ m) = 1 := by
    have h : c₂ ^ (2 ^ m) = (c₂ ^ 2 ^ (m - 1)) ^ 2 := by
      rw [show 2 ^ m = 2 ^ (m - 1) * 2 by rw [← pow_succ]; congr 1; omega, pow_mul]
    rw [h, hc₂pow, pow_two]
    exact hexp _ (vB V e 1).2
  have hc₃2m : c₃ ^ (2 ^ m) = 1 := by
    have h : c₃ ^ (2 ^ m) = (c₃ ^ 2 ^ (m - 1)) ^ 2 := by
      rw [show 2 ^ m = 2 ^ (m - 1) * 2 by rw [← pow_succ]; congr 1; omega, pow_mul]
    rw [h, hc₃pow, pow_two]
    exact hexp _ (vB V e 2).2
  let c : Fin 3 → G := fun i => if i = 0 then c₁ else if i = 1 then c₂ else c₃
  have hc0 : c 0 = c₁ := by simp [c]
  have hc1 : c 1 = c₂ := by simp [c]
  have hc2 : c 2 = c₃ := by simp [c]
  have hcmem : ∀ i, c i ∈ C := by
    intro i
    have hcase : i = 0 ∨ i = 1 ∨ i = 2 := by fin_cases i <;> simp
    rcases hcase with h | h | h
    · rw [h, hc0]; exact hc₁C
    · rw [h, hc1]; exact hc₂C
    · rw [h, hc2]; exact hc₃C
  have hcpow : ∀ i, (c i) ^ (2 ^ m) = 1 := by
    intro i
    have hcase : i = 0 ∨ i = 1 ∨ i = 2 := by fin_cases i <;> simp
    rcases hcase with h | h | h
    · rw [h, hc0]; exact hc₁2m
    · rw [h, hc1]; exact hc₂2m
    · rw [h, hc2]; exact hc₃2m
  have hPhi_mul : ∀ x y : Fin 3 → ZMod (2 ^ m),
      Phi (n := 2 ^ m) c x * Phi (n := 2 ^ m) c y = Phi (n := 2 ^ m) c (x + y) :=
    fun x y => phi_mul hCab hcmem hcpow x y
  have hPhi_inj : Function.Injective (Phi (n := 2 ^ m) c) := by
    have hind : ∀ a b d : ℕ, a < 2 → b < 2 → d < 2 →
        (vB V e 0 : G) ^ a * (vB V e 1 : G) ^ b * (vB V e 2 : G) ^ d = 1 →
        a = 0 ∧ b = 0 ∧ d = 0 :=
      fun a b d ha hb hd h => vB_independent V e ha hb hd h
    have hpd := pow_independent V C hVleC (fun x hx => (mem_V_iff V C hexp hinv hx).symm) hCab
      hm1 (hcmem 0) (hcmem 1) (hcmem 2) (vB V e 0).2 (vB V e 1).2 (vB V e 2).2
      (by rw [hc0]; exact hc₁half) (by rw [hc1]; exact hc₂pow) (by rw [hc2]; exact hc₃pow) hind
    have hzero : ∀ z : Fin 3 → ZMod (2 ^ m), Phi c z = 1 → z = 0 := by
      intro z hz
      have h1 : c 0 ^ (z 0).val * c 1 ^ (z 1).val * c 2 ^ (z 2).val = 1 := hz
      obtain ⟨h0, h1', h2'⟩ := hpd (z 0).val (z 1).val (z 2).val (ZMod.val_lt _)
        (ZMod.val_lt _) (ZMod.val_lt _) h1
      funext i
      have hcase : i = 0 ∨ i = 1 ∨ i = 2 := by fin_cases i <;> simp
      rcases hcase with h | h | h
      · rw [h]; exact (ZMod.val_eq_zero (z 0)).mp h0
      · rw [h]; exact (ZMod.val_eq_zero (z 1)).mp h1'
      · rw [h]; exact (ZMod.val_eq_zero (z 2)).mp h2'
    intro x y hxy
    have h1 : Phi c (x - y) = 1 := by
      have h2 : Phi c (x - y) * Phi c y = 1 * Phi c y := by
        rw [one_mul, hPhi_mul (x - y) y, sub_add_cancel, hxy]
      exact mul_right_cancel h2
    have h3 : x - y = 0 := hzero _ h1
    funext i
    have h4 := congrFun h3 i
    exact sub_eq_zero.mp (by simpa using h4)
  have hPhi_mem : ∀ x : Fin 3 → ZMod (2 ^ m),
      Phi c x ∈ Subgroup.closure ({c₁, c₂, c₃} : Set G) := by
    intro x
    have hprod : ∀ (y : Fin 3 → ZMod (2 ^ m)), (∀ i, c i ∈ Subgroup.closure ({c₁, c₂, c₃} : Set G)) →
        Phi c y ∈ Subgroup.closure ({c₁, c₂, c₃} : Set G) := by
      intro y hy
      rw [show Phi c y = c 0 ^ (y 0).val * c 1 ^ (y 1).val * c 2 ^ (y 2).val from rfl]
      exact Subgroup.mul_mem _ (Subgroup.mul_mem _ (Subgroup.pow_mem _ (hy 0) _)
        (Subgroup.pow_mem _ (hy 1) _)) (Subgroup.pow_mem _ (hy 2) _)
    exact hprod x (by
      intro i
      have hcase : i = 0 ∨ i = 1 ∨ i = 2 := by fin_cases i <;> simp
      rcases hcase with h | h | h
      · rw [h, hc0]; exact Subgroup.subset_closure (by simp)
      · rw [h, hc1]; exact Subgroup.subset_closure (by simp)
      · rw [h, hc2]; exact Subgroup.subset_closure (by simp))
  have hval0 : ((0 : ZMod (2 ^ m))).val = 0 := (ZMod.val_eq_zero 0).mpr rfl
  have hval1 : ((1 : ZMod (2 ^ m))).val = 1 := by
    have hlt : 1 < 2 ^ m := by
      have h := Nat.pow_le_pow_right (by norm_num : 1 ≤ 2) hm1
      simp only [pow_one] at h
      omega
    rw [show (1 : ZMod (2 ^ m)) = ((1 : ℕ) : ZMod (2 ^ m)) by norm_num, ZMod.val_natCast]
    exact Nat.mod_eq_of_lt hlt
  have hPhi_surj : ∀ y ∈ Subgroup.closure ({c₁, c₂, c₃} : Set G),
      ∃ x : Fin 3 → ZMod (2 ^ m), Phi (n := 2 ^ m) c x = y := by
    intro y hy
    refine Subgroup.closure_induction (k := ({c₁, c₂, c₃} : Set G)) ?_ ?_ ?_ ?_ hy
    · intro z hz
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hz
      rcases hz with rfl | rfl | rfl
      · exact ⟨fun i : Fin 3 => if i = 0 then (1 : ZMod (2 ^ m)) else 0, by
          simp only [Phi]
          rw [hc0, hc1, hc2]
          simp [hval0, hval1]⟩
      · exact ⟨fun i : Fin 3 => if i = 1 then (1 : ZMod (2 ^ m)) else 0, by
          simp only [Phi]
          rw [hc0, hc1, hc2]
          simp [hval0, hval1]⟩
      · exact ⟨fun i : Fin 3 => if i = 2 then (1 : ZMod (2 ^ m)) else 0, by
          simp only [Phi]
          rw [hc0, hc1, hc2]
          simp [hval0, hval1]⟩
    · exact ⟨0, Phi_zero c⟩
    · intro a b ha hb xa xb
      obtain ⟨x, hx⟩ := xa
      obtain ⟨yw, hyw⟩ := xb
      exact ⟨x + yw, by rw [← hPhi_mul, hx, hyw]⟩
    · intro a ha xa
      obtain ⟨x, hx⟩ := xa
      refine ⟨-x, ?_⟩
      have h2 : Phi (n := 2 ^ m) c (-x) * Phi (n := 2 ^ m) c x = 1 := by
        rw [hPhi_mul, neg_add_cancel, Phi_zero]
      have h3 : Phi (n := 2 ^ m) c (-x) = (Phi (n := 2 ^ m) c x)⁻¹ :=
        eq_inv_of_mul_eq_one_of h2
      rw [h3, hx]
  have hcardS : Nat.card ↥(Subgroup.closure ({c₁, c₂, c₃} : Set G)) = 2 ^ (3 * m) := by
    let F : (Fin 3 → ZMod (2 ^ m)) → ↥(Subgroup.closure ({c₁, c₂, c₃} : Set G)) :=
      fun x => ⟨Phi (n := 2 ^ m) c x, hPhi_mem x⟩
    have hF : Function.Bijective F :=
      ⟨fun x y hxy => hPhi_inj (Subtype.ext_iff.mp hxy), fun y => by
        obtain ⟨x, hx⟩ := hPhi_surj y y.2
        exact ⟨x, Subtype.ext hx⟩⟩
    have hbij : Nat.card ↥(Subgroup.closure ({c₁, c₂, c₃} : Set G))
        = Nat.card (Fin 3 → ZMod (2 ^ m)) := (Nat.card_congr (Equiv.ofBijective F hF)).symm
    rw [hbij]
    have h1 : Nat.card (Fin 3 → ZMod (2 ^ m)) = ((2 : ℕ) ^ m) ^ 3 := by
      rw [Nat.card_eq_fintype_card, Fintype.card_fun]
      norm_num [ZMod.card]
    rw [h1, ← pow_mul]
    ring_nf
  have hOmegaS : Omega C hCab m = Subgroup.closure ({c₁, c₂, c₃} : Set G) := by
    have hsurjm : ∀ v ∈ V, ∃ cc ∈ C, cc ^ 2 ^ (m - 1) = v :=
      pow_image_eq_V V C (inferInstance : V.Normal) hcard hexp hC hCab htrans m hc₁C
        (by rw [hc₁half]; exact (vB V e 0).2) hhalf_ne
    have hcardΩ : Nat.card ↥(Omega C hCab m) = 8 ^ m :=
      omega_card V C hCab hcard (by
        ext x
        rw [mem_Omega]
        constructor
        · rintro ⟨hxC, hx2⟩
          rcases eq_or_ne x 1 with rfl | hx1
          · exact V.one_mem
          · exact hinv x hxC (orderOf_eq_prime (by simpa using hx2) hx1)
        · intro hx
          exact ⟨hVleC hx, by
            rw [show (2 : ℕ) ^ 1 = 2 by norm_num, pow_two]
            exact hexp x hx⟩) hm1 hsurjm
    have hcardΩ' : Nat.card ↥(Omega C hCab m) = 2 ^ (3 * m) := by
      rw [hcardΩ]
      rw [show (8 : ℕ) = 2 ^ 3 by norm_num, ← pow_mul]
    have hle : Subgroup.closure ({c₁, c₂, c₃} : Set G) ≤ Omega C hCab m :=
      (Subgroup.closure_le (Omega C hCab m)).mpr (by
        rintro z (rfl | rfl | rfl)
        · exact ⟨hcmem 0, hcpow 0⟩
        · exact ⟨hcmem 1, hcpow 1⟩
        · exact ⟨hcmem 2, hcpow 2⟩)
    have heq : Subgroup.closure ({c₁, c₂, c₃} : Set G) = Omega C hCab m :=
      Subgroup.eq_of_le_of_card_ge hle (by rw [hcardS, hcardΩ'])
    exact heq.symm
  -- ## the action of `s₁` on `Ω_m(C)` is given by `SMat`
  have heval : ∀ (a₀ a₁ a₂ : ZMod (2 ^ m)),
      Phi (n := 2 ^ m) c (fun i : Fin 3 => if i = 0 then a₀ else if i = 1 then a₁ else a₂)
        = c 0 ^ a₀.val * c 1 ^ a₁.val * c 2 ^ a₂.val := by
    intro a₀ a₁ a₂
    simp only [Phi]
    simp
  have hScol0 : Phi (n := 2 ^ m) c (fun j : Fin 3 => SMat m j 0) = c₁⁻¹ := by
    have h1 : (fun j : Fin 3 => SMat m j 0)
        = (fun j : Fin 3 => if j = 0 then (-1 : ZMod (2 ^ m))
            else if j = 1 then 0 else 0) := by
      funext j
      fin_cases j <;> simp [SMat]
    rw [h1, heval (-1) 0 0]
    simp only [hval0, pow_zero, mul_one, hc0]
    exact pow_zmod_neg_one c₁ hc₁2m
  have hScol1 : Phi (n := 2 ^ m) c (fun j : Fin 3 => SMat m j 1) = c₂ := by
    have h1 : (fun j : Fin 3 => SMat m j 1)
        = (fun j : Fin 3 => if j = 0 then (0 : ZMod (2 ^ m))
            else if j = 1 then 1 else 0) := by
      funext j
      fin_cases j <;> simp [SMat]
    rw [h1, heval 0 1 0]
    simp only [hval0, hval1, pow_zero, pow_one, mul_one, one_mul, hc0, hc1, hc2]
  have hScol2 : Phi (n := 2 ^ m) c (fun j : Fin 3 => SMat m j 2) = c₂ * c₃⁻¹ := by
    have h1 : (fun j : Fin 3 => SMat m j 2)
        = (fun j : Fin 3 => if j = 0 then (0 : ZMod (2 ^ m))
            else if j = 1 then 1 else -1) := by
      funext j
      fin_cases j <;> simp [SMat]
    rw [h1, heval 0 1 (-1)]
    simp only [hval0, hval1, pow_zero, pow_one, mul_one, one_mul, hc0, hc1, hc2]
    rw [pow_zmod_neg_one c₃ hc₃2m]
  have hcolS : ∀ i : Fin 3, s₁ * c i * s₁⁻¹ = Phi (n := 2 ^ m) c (fun j => SMat m j i) := by
    intro i
    have hcase : i = 0 ∨ i = 1 ∨ i = 2 := by fin_cases i <;> simp
    rcases hcase with h | h | h
    · rw [h, hc0, hc₁s, hScol0]
    · rw [h, hc1, hc₂s, hScol1]
    · rw [h, hc2, hc₃s, hScol2]
  have hS : ∀ x : Fin 3 → ZMod (2 ^ m),
      s₁ * Phi (n := 2 ^ m) c x * s₁⁻¹ = Phi (n := 2 ^ m) c (Matrix.mulVec (SMat m) x) :=
    fun x => phi_of_cols hCab hcmem hcpow hcolS x
  -- ## the transport: `Im(t̄ + 1)` is generated by `d = c₂^t c₂`
  have hs₁sqC : s₁ * s₁ ∈ C := by rw [hs₁sq]; exact hVleC (vB V e 0).2
  have ht_conj : ∀ x : ↥V, t * (x : G) * t⁻¹ = (tauV V e x : G) := by
    intro x
    have h1 := congrArg (fun y : ↥V => (y : G)) (ht x)
    rw [MulAut.conjNormal_apply] at h1
    exact h1.symm
  obtain ⟨φ, hφ⟩ := aut_inv_conj_V (V := ↥V) hcard hexp' (sigmaV V e) (tauV V e)
    (sigmaV_ne_one V e) (sigmaV_mul_self V e) (tauV_ne_one V e) (tauV_mul_self V e)
  obtain ⟨g, hg⟩ := conjNormal_eq_of_hAut (V := V) hAut φ
  have hgφ : MulAut.conjNormal g = φ := by
    apply MulEquiv.ext
    intro x
    exact (hg x).symm
  have hgconj : MulAut.conjNormal (g * s₁ * g⁻¹) = tauV V e := by
    rw [show g * s₁ * g⁻¹ = (g * s₁) * g⁻¹ by rfl, map_mul, map_mul, map_inv, hsc, hgφ]
    exact hφ.symm
  have hc₀'C : t * (g * s₁ * g⁻¹)⁻¹ ∈ C := by
    refine hconjC _ (fun (x : ↥V) => ?_)
    have h1 : MulAut.conjNormal (H := V) (t * (g * s₁ * g⁻¹)⁻¹) = 1 := by
      rw [map_mul, map_inv, hgconj, htc, mul_inv_cancel]
    rw [h1, MulAut.one_apply]
  obtain ⟨c₀, hc₀C, hc₀eq⟩ : ∃ c₀ ∈ C, t = g * s₁ * g⁻¹ * c₀ := by
    refine ⟨(g * s₁ * g⁻¹)⁻¹ * (t * (g * s₁ * g⁻¹)⁻¹) * (g * s₁ * g⁻¹),
      ?_, ?_⟩
    · simpa using hCn.conj_mem _ hc₀'C (g * s₁ * g⁻¹)⁻¹
    · group
  have htransp : ∀ x ∈ Omega C hCab m,
      t * x * t⁻¹ * x = g * (s₁ * (g⁻¹ * x * g) * s₁⁻¹ * (g⁻¹ * x * g)) * g⁻¹ :=
    fun x hx => image_conj_add_one_transport C hCn hCab hc₀C hc₀eq x hx.1
  have him : ∀ x ∈ Omega C hCab m,
      t * x * t⁻¹ * x ∈ Subgroup.zpowers (g * c₂ * g⁻¹) := by
    intro x hx
    rw [htransp x hx]
    have hxgC : g⁻¹ * x * g ∈ C := by simpa using hCn.conj_mem x hx.1 g⁻¹
    have hxgp : (g⁻¹ * x * g) ^ (2 ^ m) = 1 := by
      have h2 : g⁻¹ * x * g = (MulAut.conj g⁻¹) x := by rw [MulAut.conj_apply, inv_inv]
      rw [h2, ← map_pow, hx.2, map_one]
    have hxg : g⁻¹ * x * g ∈ Subgroup.closure ({c₁, c₂, c₃} : Set G) := by
      rw [← hOmegaS]
      exact ⟨hxgC, hxgp⟩
    have h1 := image_conj_add_one C hCn hCab hc₁C hc₂C hc₃C hc₁s hc₂s hc₃s (g⁻¹ * x * g) hxg
    obtain ⟨j, -, hj⟩ := exists_pow_eq_of_mem_zpowers (by
      have h := orderOf_dvd_iff_pow_eq_one.mpr hc₂2m
      have h4 : 0 < 2 ^ m := by positivity
      exact Nat.pos_of_dvd_of_pos h h4) h1
    refine Subgroup.mem_zpowers_iff.mpr ⟨(j : ℤ), ?_⟩
    rw [zpow_natCast, ← hj]
    have hpow_conj : ∀ i : ℕ, (g * c₂ * g⁻¹) ^ i = g * c₂ ^ i * g⁻¹ := by
      intro i
      induction i with
      | zero => simp
      | succ i ih => rw [pow_succ, pow_succ, ih]; group
    rw [hpow_conj j]
  have ht_v1 : t * (vB V e 1 : G) * t⁻¹ = (vB V e 0 : G) * (vB V e 1 : G) := by
    have h1 := ht_conj (vB V e 1)
    rw [tauV_vB_one] at h1
    simpa using h1
  set d : G := t * c₂ * t⁻¹ * c₂ with hddef
  have hd_pow : d ^ 2 ^ (m - 1) = (vB V e 0 : G) := by
    have hxmem : t * c₂ * t⁻¹ ∈ C := hCn.conj_mem c₂ hc₂C t
    have hcomm : Commute (t * c₂ * t⁻¹) c₂ :=
      (commute_iff_eq _ _).mpr (hCab _ hxmem _ hc₂C)
    rw [hddef, hcomm.mul_pow]
    have h1 : (t * c₂ * t⁻¹) ^ (2 ^ (m - 1)) = (vB V e 0 : G) * (vB V e 1 : G) := by
      rw [show t * c₂ * t⁻¹ = MulAut.conj t c₂ by rw [MulAut.conj_apply], ← map_pow,
        MulAut.conj_apply, hc₂pow]
      exact ht_v1
    rw [h1, hc₂pow, mul_assoc,
      show (vB V e 1 : G) * (vB V e 1 : G) = 1 from hexp _ (vB V e 1).2, mul_one]
  have hd_ord : orderOf d = 2 ^ m := by
    have h1 : d ^ 2 ^ (m - 1) ≠ 1 := by rw [hd_pow]; exact vB_ne_one V e 0
    have h2 : d ^ (2 ^ (m - 1 + 1)) = 1 := by
      rw [show 2 ^ (m - 1 + 1) = 2 ^ (m - 1) * 2 by rw [pow_succ], pow_mul, hd_pow, pow_two]
      exact hexp _ (vB V e 0).2
    have h3 := orderOf_eq_prime_pow (p := 2) (n := m - 1) h1 h2
    rwa [show m - 1 + 1 = m by omega] at h3
  have hc₂ord : orderOf c₂ = 2 ^ m := by
    have h1 : c₂ ^ 2 ^ (m - 1) ≠ 1 := by rw [hc₂pow]; exact vB_ne_one V e 1
    have h2 : c₂ ^ (2 ^ (m - 1 + 1)) = 1 := by
      rw [show 2 ^ (m - 1 + 1) = 2 ^ (m - 1) * 2 by rw [pow_succ], pow_mul, hc₂pow, pow_two]
      exact hexp _ (vB V e 1).2
    have h3 := orderOf_eq_prime_pow (p := 2) (n := m - 1) h1 h2
    rwa [show m - 1 + 1 = m by omega] at h3
  have hd_zp : Subgroup.zpowers d = Subgroup.zpowers (g * c₂ * g⁻¹) := by
    have hconj : (g * c₂ * g⁻¹) ^ 2 ^ (m - 1) = g * (vB V e 1 : G) * g⁻¹ := by
      have h2 : g * c₂ * g⁻¹ = (MulAut.conj g) c₂ := by rw [MulAut.conj_apply]
      rw [h2, ← map_pow, hc₂pow, MulAut.conj_apply]
    have h1 : (g * c₂ * g⁻¹) ^ 2 ^ (m - 1) ≠ 1 := by
      rw [hconj]
      intro h
      apply vB_ne_one V e 1
      calc (vB V e 1 : G) = g⁻¹ * (g * (vB V e 1 : G) * g⁻¹) * g := by group
        _ = 1 := by rw [h]; group
    have h2 : (g * c₂ * g⁻¹) ^ (2 ^ (m - 1 + 1)) = 1 := by
      have h4 : (g * (vB V e 1 : G) * g⁻¹) * (g * (vB V e 1 : G) * g⁻¹) = 1 := by
        rw [show (g * (vB V e 1 : G) * g⁻¹) * (g * (vB V e 1 : G) * g⁻¹)
            = g * ((vB V e 1 : G) * (vB V e 1 : G)) * g⁻¹ by group,
          show (vB V e 1 : G) * (vB V e 1 : G) = 1 from hexp _ (vB V e 1).2]
        group
      rw [show 2 ^ (m - 1 + 1) = 2 ^ (m - 1) * 2 by rw [pow_succ], pow_mul, hconj, pow_two]
      exact h4
    have hgc₂ord : orderOf (g * c₂ * g⁻¹) = 2 ^ m := by
      have h3 := orderOf_eq_prime_pow (p := 2) (n := m - 1) h1 h2
      rwa [show m - 1 + 1 = m by omega] at h3
    refine Subgroup.eq_of_le_of_card_ge ?_ ?_
    · rw [Subgroup.zpowers_le]
      exact him c₂ ⟨hc₂C, hc₂2m⟩
    · rw [Nat.card_zpowers, hgc₂ord, Nat.card_zpowers, hd_ord]
  have hc₃t_zp : t * c₃ * t⁻¹ * c₃ ∈ Subgroup.zpowers d := by
    rw [hd_zp]
    exact him c₃ ⟨hc₃C, hc₃2m⟩
  obtain ⟨k₀, hk₀lt, hk₀⟩ := exists_pow_eq_of_mem_zpowers (by rw [hd_ord]; positivity) hc₃t_zp
  have hk₀lt' : k₀ < 2 ^ m := by rw [← hd_ord]; exact hk₀lt
  obtain ⟨k, hk⟩ : ∃ k : ZMod (2 ^ m), d ^ k.val = t * c₃ * t⁻¹ * c₃ := by
    refine ⟨(k₀ : ZMod (2 ^ m)), ?_⟩
    rw [show ((k₀ : ZMod (2 ^ m))).val = k₀ by
      rw [ZMod.val_natCast]
      exact Nat.mod_eq_of_lt hk₀lt']
    exact hk₀
  have hd_2m : d ^ (2 ^ m) = 1 := by
    have h2 : 2 ^ m = 2 ^ (m - 1) * 2 := by
      rw [← pow_succ]
      congr 1
      omega
    rw [h2, pow_mul, hd_pow, pow_two]
    exact hexp _ (vB V e 0).2
  have hd_memC : d ∈ C := by
    have h1 : t * c₂ * t⁻¹ ∈ C := hCn.conj_mem c₂ hc₂C t
    have h2 : Commute (t * c₂ * t⁻¹) c₂ := (commute_iff_eq _ _).mpr (hCab _ h1 _ hc₂C)
    rw [hddef]
    exact C.mul_mem h1 hc₂C
  have hd_coords : ∃ y : Fin 3 → ZMod (2 ^ m), Phi (n := 2 ^ m) c y = d := by
    have h1 : d ∈ Omega C hCab m := ⟨hd_memC, hd_2m⟩
    rw [hOmegaS] at h1
    exact hPhi_surj d h1
  -- ## the parity of the coordinates of `d`, and the normalized basis
  obtain ⟨y, hy, hy0, hy1, hy2⟩ : ∃ y : Fin 3 → ZMod (2 ^ m), Phi (n := 2 ^ m) c y = d ∧
      (y 0).val % 2 = 1 ∧ (y 1).val % 2 = 0 ∧ (y 2).val % 2 = 0 := by
    obtain ⟨y, hy⟩ := hd_coords
    have h1 : (Phi (n := 2 ^ m) c y) ^ (2 ^ (m - 1))
        = (vB V e 0 : G) ^ ((y 0).val % 2) * (vB V e 1 : G) ^ ((y 1).val % 2)
          * (vB V e 2 : G) ^ ((y 2).val % 2) :=
      phi_pow_two_pow' (v := fun i => (vB V e i : G)) hCab hcmem
        (fun i => by
          have hcase : i = 0 ∨ i = 1 ∨ i = 2 := by fin_cases i <;> simp
          rcases hcase with h | h | h
          · rw [h]; exact hc₁half
          · rw [h]; exact hc₂pow
          · rw [h]; exact hc₃pow)
        (fun i => by
          have hcase : i = 0 ∨ i = 1 ∨ i = 2 := by fin_cases i <;> simp
          rcases hcase with h | h | h
          · rw [h]; exact hexp _ (vB V e 0).2
          · rw [h]; exact hexp _ (vB V e 1).2
          · rw [h]; exact hexp _ (vB V e 2).2) y
    rw [hy, hd_pow] at h1
    have hc01 : Commute (vB V e 0 : G) (vB V e 1 : G) :=
      (commute_iff_eq _ _).mpr (V_comm V hexp (vB V e 0).2 (vB V e 1).2)
    have hc02 : Commute (vB V e 0 : G) (vB V e 2 : G) :=
      (commute_iff_eq _ _).mpr (V_comm V hexp (vB V e 0).2 (vB V e 2).2)
    have hc0 : Commute (vB V e 0 : G)
        ((vB V e 1 : G) ^ ((y 1).val % 2) * (vB V e 2 : G) ^ ((y 2).val % 2)) :=
      (hc01.pow_right _).mul_right (hc02.pow_right _)
    have hpow : (vB V e 0 : G) ^ ((y 0).val % 2) * (vB V e 1 : G) ^ ((y 1).val % 2)
        * (vB V e 2 : G) ^ ((y 2).val % 2) = (vB V e 0 : G) ^ 1 := by
      rw [pow_one, ← h1]
    have h5 : ((vB V e 0 : G) ^ ((y 0).val % 2) * (vB V e 1 : G) ^ ((y 1).val % 2)
        * (vB V e 2 : G) ^ ((y 2).val % 2)) * (vB V e 0 : G) = 1 := by
      rw [hpow, pow_one, vB_zero_sq V e]
    have h6 : (vB V e 0 : G) ^ (((y 0).val % 2) + 1) * (vB V e 1 : G) ^ ((y 1).val % 2)
        * (vB V e 2 : G) ^ ((y 2).val % 2) = 1 := by
      calc (vB V e 0 : G) ^ (((y 0).val % 2) + 1) * (vB V e 1 : G) ^ ((y 1).val % 2)
            * (vB V e 2 : G) ^ ((y 2).val % 2)
          = ((vB V e 0 : G) ^ ((y 0).val % 2) * (vB V e 0 : G))
            * (vB V e 1 : G) ^ ((y 1).val % 2) * (vB V e 2 : G) ^ ((y 2).val % 2) := by
              rw [pow_succ]
        _ = (vB V e 0 : G) ^ ((y 0).val % 2)
            * ((vB V e 0 : G) * ((vB V e 1 : G) ^ ((y 1).val % 2)
              * (vB V e 2 : G) ^ ((y 2).val % 2))) := by group
        _ = (vB V e 0 : G) ^ ((y 0).val % 2)
            * (((vB V e 1 : G) ^ ((y 1).val % 2) * (vB V e 2 : G) ^ ((y 2).val % 2))
              * (vB V e 0 : G)) := by rw [hc0.eq]
        _ = ((vB V e 0 : G) ^ ((y 0).val % 2) * (vB V e 1 : G) ^ ((y 1).val % 2)
            * (vB V e 2 : G) ^ ((y 2).val % 2)) * (vB V e 0 : G) := by group
        _ = 1 := h5
    have h7 : (vB V e 0 : G) ^ ((((y 0).val % 2) + 1) % 2) * (vB V e 1 : G) ^ ((y 1).val % 2)
        * (vB V e 2 : G) ^ ((y 2).val % 2) = 1 := by
      rw [← pow_eq_pow_mod_two (hexp _ (vB V e 0).2) (((y 0).val % 2) + 1)]
      exact h6
    obtain ⟨h8, h9, h10⟩ := vB_independent V e (Nat.mod_lt _ (by norm_num))
      (Nat.mod_lt _ (by norm_num)) (Nat.mod_lt _ (by norm_num)) h7
    refine ⟨y, hy, ?_, h9, h10⟩
    have h11 : ((y 0).val % 2 + 1) % 2 = 0 := h8
    have hlt : (y 0).val % 2 = 0 ∨ (y 0).val % 2 = 1 := by
      have h12 : (y 0).val % 2 < 2 := Nat.mod_lt _ (by norm_num)
      omega
    rcases hlt with h | h
    · rw [h] at h11
      norm_num at h11
    · exact h
  -- ## the normalized basis `c' = (c₁', c₂, c₃)`
  set c₁' : G := c₁ ^ (y 0).val with hc₁'def
  have hc₁'mem : c₁' ∈ C := C.pow_mem hc₁C _
  have hc₁'pow : c₁' ^ 2 ^ (m - 1) = (vB V e 0 : G) := by
    have h2 : ∀ (x : G) (a N : ℕ), (x ^ a) ^ N = (x ^ N) ^ a := by
      intro x a N
      rw [← pow_mul, ← pow_mul, mul_comm]
    rw [hc₁'def, h2, hc₁half,
      pow_eq_pow_mod_two (hexp _ (vB V e 0).2) ((y 0).val), hy0, pow_one]
  have hc₁'2m : c₁' ^ (2 ^ m) = 1 := by
    have h2 : 2 ^ m = 2 ^ (m - 1) * 2 := by
      rw [← pow_succ]
      congr 1
      omega
    rw [h2, pow_mul, hc₁'pow, pow_two]
    exact hexp _ (vB V e 0).2
  have hc₁'s : s₁ * c₁' * s₁⁻¹ = c₁'⁻¹ := by
    have h2 : ∀ (x : G) (N : ℕ), s₁ * x ^ N * s₁⁻¹ = (s₁ * x * s₁⁻¹) ^ N := by
      intro x N
      induction N with
      | zero => simp
      | succ N ih =>
        rw [pow_succ, pow_succ,
          show s₁ * (x ^ N * x) * s₁⁻¹ = (s₁ * x ^ N * s₁⁻¹) * (s₁ * x * s₁⁻¹) by group, ih]
    rw [hc₁'def, h2, hc₁s, inv_pow]
  have hc₁'t : t * c₁' * t⁻¹ = c₁'⁻¹ := by
    have h2 : ∀ (x : G) (N : ℕ), t * x ^ N * t⁻¹ = (t * x * t⁻¹) ^ N := by
      intro x N
      induction N with
      | zero => simp
      | succ N ih =>
        rw [pow_succ, pow_succ,
          show t * (x ^ N * x) * t⁻¹ = (t * x ^ N * t⁻¹) * (t * x * t⁻¹) by group, ih]
    rw [hc₁'def, h2, hc₁t, inv_pow]
  let c' : Fin 3 → G := fun i => if i = 0 then c₁' else if i = 1 then c₂ else c₃
  have hc'0 : c' 0 = c₁' := by simp [c']
  have hc'1 : c' 1 = c₂ := by simp [c']
  have hc'2 : c' 2 = c₃ := by simp [c']
  have hc'mem : ∀ i, c' i ∈ C := by
    intro i
    have hcase : i = 0 ∨ i = 1 ∨ i = 2 := by fin_cases i <;> simp
    rcases hcase with h | h | h
    · rw [h, hc'0]; exact hc₁'mem
    · rw [h, hc'1]; exact hc₂C
    · rw [h, hc'2]; exact hc₃C
  have hc'pow : ∀ i, (c' i) ^ (2 ^ m) = 1 := by
    intro i
    have hcase : i = 0 ∨ i = 1 ∨ i = 2 := by fin_cases i <;> simp
    rcases hcase with h | h | h
    · rw [h, hc'0]; exact hc₁'2m
    · rw [h, hc'1]; exact hc₂2m
    · rw [h, hc'2]; exact hc₃2m
  have hPhi'_mul : ∀ x z : Fin 3 → ZMod (2 ^ m),
      Phi (n := 2 ^ m) c' x * Phi (n := 2 ^ m) c' z = Phi (n := 2 ^ m) c' (x + z) :=
    fun x z => phi_mul hCab hc'mem hc'pow x z
  have hPhi'_neg : ∀ x : Fin 3 → ZMod (2 ^ m),
      Phi (n := 2 ^ m) c' (-x) = (Phi (n := 2 ^ m) c' x)⁻¹ := by
    intro x
    have h2 : Phi (n := 2 ^ m) c' (-x) * Phi (n := 2 ^ m) c' x = 1 := by
      rw [hPhi'_mul, neg_add_cancel, Phi_zero]
    exact eq_inv_of_mul_eq_one_of h2
  have hPhi'_inj : Function.Injective (Phi (n := 2 ^ m) c') :=
    Phi_injective_of V C hVleC (fun x hx => (mem_V_iff V C hexp hinv hx).symm) hCab hm1 hc'mem
      hc'pow (fun i => (vB V e i).2)
      (fun i => by
        have hcase : i = 0 ∨ i = 1 ∨ i = 2 := by fin_cases i <;> simp
        rcases hcase with h | h | h
        · rw [h, hc'0]; exact hc₁'pow
        · rw [h, hc'1]; exact hc₂pow
        · rw [h, hc'2]; exact hc₃pow)
      (fun a b dd ha hb hd h => vB_independent V e ha hb hd h)
  have heval' : ∀ (a₀ a₁ a₂ : ZMod (2 ^ m)),
      Phi (n := 2 ^ m) c' (fun i : Fin 3 => if i = 0 then a₀ else if i = 1 then a₁ else a₂)
        = c' 0 ^ a₀.val * c' 1 ^ a₁.val * c' 2 ^ a₂.val := by
    intro a₀ a₁ a₂
    simp only [Phi]
    simp
  -- ## the `S`-action on the normalized basis
  have hScol0' : Phi (n := 2 ^ m) c' (fun j : Fin 3 => SMat m j 0) = c₁'⁻¹ := by
    have h1 : (fun j : Fin 3 => SMat m j 0)
        = (fun j : Fin 3 => if j = 0 then (-1 : ZMod (2 ^ m)) else if j = 1 then 0 else 0) := by
      funext j
      fin_cases j <;> simp [SMat]
    rw [h1, heval' (-1) 0 0]
    simp only [hval0, pow_zero, mul_one, hc'0]
    exact pow_zmod_neg_one c₁' hc₁'2m
  have hScol1' : Phi (n := 2 ^ m) c' (fun j : Fin 3 => SMat m j 1) = c₂ := by
    have h1 : (fun j : Fin 3 => SMat m j 1)
        = (fun j : Fin 3 => if j = 0 then (0 : ZMod (2 ^ m)) else if j = 1 then 1 else 0) := by
      funext j
      fin_cases j <;> simp [SMat]
    rw [h1, heval' 0 1 0]
    simp [hval0, hval1, hc'0, hc'1, hc'2]
  have hScol2' : Phi (n := 2 ^ m) c' (fun j : Fin 3 => SMat m j 2) = c₂ * c₃⁻¹ := by
    have h1 : (fun j : Fin 3 => SMat m j 2)
        = (fun j : Fin 3 => if j = 0 then (0 : ZMod (2 ^ m)) else if j = 1 then 1 else -1) := by
      funext j
      fin_cases j <;> simp [SMat]
    rw [h1, heval' 0 1 (-1)]
    simp only [hval0, hval1, pow_zero, pow_one, mul_one, one_mul, hc'0, hc'1, hc'2]
    rw [pow_zmod_neg_one c₃ hc₃2m]
  have hcolS' : ∀ i : Fin 3, s₁ * c' i * s₁⁻¹ = Phi (n := 2 ^ m) c' (fun j => SMat m j i) := by
    intro i
    have hcase : i = 0 ∨ i = 1 ∨ i = 2 := by fin_cases i <;> simp
    rcases hcase with h | h | h
    · rw [h, hc'0, hc₁'s, hScol0']
    · rw [h, hc'1, hc₂s, hScol1']
    · rw [h, hc'2, hc₃s, hScol2']
  have hS' : ∀ x : Fin 3 → ZMod (2 ^ m),
      s₁ * Phi (n := 2 ^ m) c' x * s₁⁻¹ = Phi (n := 2 ^ m) c' (Matrix.mulVec (SMat m) x) :=
    fun x => phi_of_cols hCab hc'mem hc'pow hcolS' x
  -- ## the parameters of the `t`-action
  obtain ⟨k₂, hk₂⟩ := zmod_two_mul_of_even (m := m) (x := (y 1)) hy1
  obtain ⟨k₃, hk₃⟩ := zmod_two_mul_of_even (m := m) (x := (y 2)) hy2
  have hd_eq : Phi (n := 2 ^ m) c'
      (fun i : Fin 3 => if i = 0 then (1 : ZMod (2 ^ m)) else if i = 1 then 2 * k₂ else 2 * k₃)
      = d := by
    rw [heval' 1 (2 * k₂) (2 * k₃), hc'0, hc'1, hc'2, hval1, pow_one, hc₁'def, ← hk₂, ← hk₃,
      ← hy]
    rfl
  have hTcol0' : Phi (n := 2 ^ m) c' (fun j : Fin 3 => TMat m k k₂ k₃ j 0) = c₁'⁻¹ := by
    have h1 : (fun j : Fin 3 => TMat m k k₂ k₃ j 0)
        = (fun j : Fin 3 => if j = 0 then (-1 : ZMod (2 ^ m)) else if j = 1 then 0 else 0) := by
      funext j
      fin_cases j <;> simp [TMat]
    rw [h1, heval' (-1) 0 0]
    simp only [hval0, pow_zero, mul_one, hc'0]
    exact pow_zmod_neg_one c₁' hc₁'2m
  have hTcol1' : Phi (n := 2 ^ m) c' (fun j : Fin 3 => TMat m k k₂ k₃ j 1)
      = c₁' * c₂ ^ (2 * k₂ - 1).val * c₃ ^ (2 * k₃).val := by
    have h1 : (fun j : Fin 3 => TMat m k k₂ k₃ j 1)
        = (fun j : Fin 3 => if j = 0 then (1 : ZMod (2 ^ m))
            else if j = 1 then 2 * k₂ - 1 else 2 * k₃) := by
      funext j
      fin_cases j <;> simp [TMat]
    rw [h1, heval' 1 (2 * k₂ - 1) (2 * k₃), hc'0, hc'1, hc'2, hval1, pow_one]
  have hTcol2' : Phi (n := 2 ^ m) c' (fun j : Fin 3 => TMat m k k₂ k₃ j 2)
      = c₁' ^ k.val * c₂ ^ (2 * k * k₂).val * c₃ ^ (2 * k * k₃ - 1).val := by
    have h1 : (fun j : Fin 3 => TMat m k k₂ k₃ j 2)
        = (fun j : Fin 3 => if j = 0 then k else if j = 1 then 2 * k * k₂ else 2 * k * k₃ - 1) := by
      funext j
      fin_cases j <;> simp [TMat]
    rw [h1, heval' k (2 * k * k₂) (2 * k * k₃ - 1), hc'0, hc'1, hc'2]
  have hPhi'_mem : ∀ x : Fin 3 → ZMod (2 ^ m), Phi (n := 2 ^ m) c' x ∈ C := by
    intro x
    rw [show Phi (n := 2 ^ m) c' x
        = c' 0 ^ (x 0).val * c' 1 ^ (x 1).val * c' 2 ^ (x 2).val from rfl]
    exact C.mul_mem (C.mul_mem (C.pow_mem (hc'mem 0) _) (C.pow_mem (hc'mem 1) _))
      (C.pow_mem (hc'mem 2) _)
  have hneg1 : c₂⁻¹ = Phi (n := 2 ^ m) c'
      (fun i : Fin 3 => if i = 0 then (0 : ZMod (2 ^ m)) else if i = 1 then -1 else 0) := by
    rw [heval' 0 (-1) 0]
    simp only [hval0, pow_zero, one_mul, mul_one, hc'0, hc'1, hc'2]
    exact (pow_zmod_neg_one c₂ hc₂2m).symm
  have hneg2 : c₃⁻¹ = Phi (n := 2 ^ m) c'
      (fun i : Fin 3 => if i = 0 then (0 : ZMod (2 ^ m)) else if i = 1 then 0 else -1) := by
    rw [heval' 0 0 (-1)]
    simp only [hval0, pow_zero, mul_one, one_mul, hc'0, hc'1, hc'2]
    exact (pow_zmod_neg_one c₃ hc₃2m).symm
  have ht_c₂ : t * c' 1 * t⁻¹ = c₁' * c₂ ^ (2 * k₂ - 1).val * c₃ ^ (2 * k₃).val := by
    rw [hc'1]
    have h1 : t * c₂ * t⁻¹ = d * c₂⁻¹ := by
      rw [show d = t * c₂ * t⁻¹ * c₂ from hddef]
      group
    rw [h1, ← hd_eq, hneg1, hPhi'_mul, ← hTcol1']
    congr 1
    funext i
    fin_cases i <;> simp [TMat] <;> ring
  have ht_c₃ : t * c' 2 * t⁻¹ = c₁' ^ k.val * c₂ ^ (2 * k * k₂).val * c₃ ^ (2 * k * k₃ - 1).val := by
    rw [hc'2]
    have h1 : t * c₃ * t⁻¹ = d ^ k.val * c₃⁻¹ := by
      have h2 : t * c₃ * t⁻¹ * c₃ = d ^ k.val := hk.symm
      rw [← h2]
      group
    rw [h1]
    have h3 : d ^ k.val = Phi (n := 2 ^ m) c'
        (k • (fun i : Fin 3 => if i = 0 then (1 : ZMod (2 ^ m))
          else if i = 1 then 2 * k₂ else 2 * k₃)) := by
      rw [← hd_eq]
      exact (phi_smul hCab hc'mem hc'pow k _).symm
    rw [h3, hneg2, hPhi'_mul, ← hTcol2']
    congr 1
    funext i
    fin_cases i <;> simp [Pi.smul_apply, TMat] <;> ring
  have hcolT' : ∀ i : Fin 3,
      t * c' i * t⁻¹ = Phi (n := 2 ^ m) c' (fun j => TMat m k k₂ k₃ j i) := by
    intro i
    have hcase : i = 0 ∨ i = 1 ∨ i = 2 := by fin_cases i <;> simp
    rcases hcase with h | h | h
    · rw [h, hc'0, hc₁'t, hTcol0']
    · rw [h, ht_c₂, hTcol1']
    · rw [h, ht_c₃, hTcol2']
  have hT' : ∀ x : Fin 3 → ZMod (2 ^ m),
      t * Phi (n := 2 ^ m) c' x * t⁻¹ = Phi (n := 2 ^ m) c' (Matrix.mulVec (TMat m k k₂ k₃) x) :=
    fun x => phi_of_cols hCab hc'mem hc'pow hcolT' x
  -- ## the matrices `TMat` and `SMat` satisfy the hypotheses of `endgame_algebra`
  have hTinv : ∀ x : Fin 3 → ZMod (2 ^ m),
      Matrix.mulVec (TMat m k k₂ k₃) (Matrix.mulVec (TMat m k k₂ k₃) x) = x := by
    intro x
    apply hPhi'_inj
    have h2 : t * (t * Phi (n := 2 ^ m) c' x * t⁻¹) * t⁻¹ = Phi (n := 2 ^ m) c' x := by
      rw [show t * (t * Phi (n := 2 ^ m) c' x * t⁻¹) * t⁻¹
          = (t * t) * Phi (n := 2 ^ m) c' x * (t * t)⁻¹ by group,
        hCab _ ht2C _ (hPhi'_mem x)]
      group
    calc Phi (n := 2 ^ m) c' (Matrix.mulVec (TMat m k k₂ k₃) (Matrix.mulVec (TMat m k k₂ k₃) x))
        = t * Phi (n := 2 ^ m) c' (Matrix.mulVec (TMat m k k₂ k₃) x) * t⁻¹ :=
          (hT' (Matrix.mulVec (TMat m k k₂ k₃) x)).symm
      _ = t * (t * Phi (n := 2 ^ m) c' x * t⁻¹) * t⁻¹ := by rw [hT' x]
      _ = Phi (n := 2 ^ m) c' x := h2
  have hT : TMat m k k₂ k₃ * TMat m k k₂ k₃ = 1 := by
    apply Matrix.mulVec_injective
    funext x
    rw [← Matrix.mulVec_mulVec x (TMat m k k₂ k₃) (TMat m k k₂ k₃), Matrix.one_mulVec]
    exact hTinv x
  have h91 : ∃ u : ZMod (2 ^ m), k₂ + k * k₃ - 1 = 2 ^ (m - 1) * u := by
    have h2 : (TMat m k k₂ k₃ * TMat m k k₂ k₃) 0 1 = 0 := by
      rw [hT, Matrix.one_apply_ne (show (0 : Fin 3) ≠ 1 by decide)]
    rw [Matrix.mul_apply, Fin.sum_univ_three] at h2
    rw [show (TMat m k k₂ k₃) 0 0 = -1 by simp [TMat],
        show (TMat m k k₂ k₃) 0 1 = 1 by simp [TMat],
        show (TMat m k k₂ k₃) 0 2 = k by simp [TMat],
        show (TMat m k k₂ k₃) 1 1 = 2 * k₂ - 1 by simp [TMat],
        show (TMat m k k₂ k₃) 2 1 = 2 * k₃ by simp [TMat]] at h2
    have h3 : 2 * (k₂ + k * k₃ - 1) = 0 := by linear_combination h2
    rcases zmod_two_torsion h3 with h4 | h4
    · exact ⟨0, by rw [h4, mul_zero]⟩
    · exact ⟨1, by rw [h4, mul_one]⟩
  have hTS : ∀ x : Fin 3 → ZMod (2 ^ m),
      (t * s₁) * Phi (n := 2 ^ m) c' x * (t * s₁)⁻¹
        = Phi (n := 2 ^ m) c' (Matrix.mulVec (TMat m k k₂ k₃ * SMat m) x) := by
    intro x
    calc (t * s₁) * Phi (n := 2 ^ m) c' x * (t * s₁)⁻¹
        = t * (s₁ * Phi (n := 2 ^ m) c' x * s₁⁻¹) * t⁻¹ := by group
      _ = t * Phi (n := 2 ^ m) c' (Matrix.mulVec (SMat m) x) * t⁻¹ := by rw [hS' x]
      _ = Phi (n := 2 ^ m) c' (Matrix.mulVec (TMat m k k₂ k₃) (Matrix.mulVec (SMat m) x)) :=
          hT' _
      _ = Phi (n := 2 ^ m) c' (Matrix.mulVec (TMat m k k₂ k₃ * SMat m) x) := by
          rw [Matrix.mulVec_mulVec]
  have hpow : ∀ n : ℕ, ∀ x : Fin 3 → ZMod (2 ^ m),
      Phi (n := 2 ^ m) c' (Matrix.mulVec ((TMat m k k₂ k₃ * SMat m) ^ n) x)
        = (t * s₁) ^ n * Phi (n := 2 ^ m) c' x * ((t * s₁) ^ n)⁻¹ := by
    intro n
    induction n with
    | zero => intro x; simp
    | succ n ih =>
      intro x
      calc Phi (n := 2 ^ m) c'
            (Matrix.mulVec ((TMat m k k₂ k₃ * SMat m) ^ (n + 1)) x)
          = Phi (n := 2 ^ m) c' (Matrix.mulVec ((TMat m k k₂ k₃ * SMat m) ^ n)
              (Matrix.mulVec (TMat m k k₂ k₃ * SMat m) x)) := by
              rw [pow_succ, Matrix.mulVec_mulVec]
        _ = (t * s₁) ^ n
              * Phi (n := 2 ^ m) c' (Matrix.mulVec (TMat m k k₂ k₃ * SMat m) x)
              * ((t * s₁) ^ n)⁻¹ := ih _
        _ = (t * s₁) ^ n * ((t * s₁) * Phi (n := 2 ^ m) c' x * (t * s₁)⁻¹)
              * ((t * s₁) ^ n)⁻¹ := by rw [hTS x]
        _ = (t * s₁) ^ (n + 1) * Phi (n := 2 ^ m) c' x * ((t * s₁) ^ (n + 1))⁻¹ := by
              rw [pow_succ]
              group
  have hconj_pow : ∀ n : ℕ, (s₁⁻¹ * (s₁ * t) * s₁) ^ n = s₁⁻¹ * (s₁ * t) ^ n * s₁ := by
    intro n
    induction n with
    | zero => simp
    | succ n ih => rw [pow_succ, pow_succ, ih]; group
  have h4 : (t * s₁) ^ 4 = c₁⁻¹ := by
    have h1 : t * s₁ = s₁⁻¹ * (s₁ * t) * s₁ := by group
    have h3 : s₁⁻¹ * c₁ * s₁ = c₁⁻¹ := by
      rw [show s₁⁻¹ * c₁ * s₁ = ((s₁ * s₁)⁻¹) * (s₁ * c₁ * s₁⁻¹) * (s₁ * s₁) by group, hc₁s,
        show s₁ * s₁ = (vB V e 0 : G) from hs₁sq]
      rw [hCab _ (C.inv_mem (hVleC (vB V e 0).2)) _ (C.inv_mem hc₁C)]
      group
    rw [h1, hconj_pow 4, show (s₁ * t) ^ 4 = c₁ from hc₁def.symm, h3]
  have hA : (TMat m k k₂ k₃ * SMat m) ^ 4 = 1 := by
    have h5 : ∀ x : Fin 3 → ZMod (2 ^ m),
        Matrix.mulVec ((TMat m k k₂ k₃ * SMat m) ^ 4) x = x := by
      intro x
      apply hPhi'_inj
      rw [hpow 4 x, h4]
      rw [show c₁⁻¹ * Phi (n := 2 ^ m) c' x * (c₁⁻¹)⁻¹ = Phi (n := 2 ^ m) c' x by
        rw [hCab _ (C.inv_mem hc₁C) _ (hPhi'_mem x)]
        group]
    apply Matrix.mulVec_injective
    funext x
    rw [h5 x, Matrix.one_mulVec]
  -- ## The parity of `k`: the action of `t` on `Ω_m(C)` reduces to its action on `V`
  have ht_v2 : t * (vB V e 2 : G) * t⁻¹ = (vB V e 0 : G) * (vB V e 2 : G) := by
    have h1 := ht_conj (vB V e 2)
    rw [tauV_vB_two] at h1
    simpa using h1
  have ht_col2 : t * c₃ * t⁻¹
      = Phi (n := 2 ^ m) c' (fun j : Fin 3 => TMat m k k₂ k₃ j 2) := by
    rw [← hc'2]
    exact hcolT' 2
  have hpk : (Phi (n := 2 ^ m) c' (fun j : Fin 3 => TMat m k k₂ k₃ j 2)) ^ (2 ^ (m - 1))
      = (vB V e 0 : G) * (vB V e 2 : G) := by
    rw [← ht_col2,
      show (t * c₃ * t⁻¹) ^ (2 ^ (m - 1)) = t * c₃ ^ (2 ^ (m - 1)) * t⁻¹ by
        rw [show t * c₃ * t⁻¹ = MulAut.conj t c₃ from (MulAut.conj_apply t c₃).symm,
          ← map_pow, MulAut.conj_apply],
      hc₃pow]
    exact ht_v2
  have hpk2 : (Phi (n := 2 ^ m) c' (fun i : Fin 3 =>
        if i = 0 then (1 : ZMod (2 ^ m)) else if i = 1 then 0 else 1)) ^ (2 ^ (m - 1))
      = (vB V e 0 : G) * (vB V e 2 : G) := by
    have h1 : Phi (n := 2 ^ m) c' (fun i : Fin 3 =>
        if i = 0 then (1 : ZMod (2 ^ m)) else if i = 1 then 0 else 1) = c₁' * c₃ := by
      rw [heval' 1 0 1]
      simp [hval1, hval0, hc'0, hc'1, hc'2]
    rw [h1, Commute.mul_pow ((commute_iff_eq _ _).mpr (hCab c₁' hc₁'mem c₃ hc₃C))
      (2 ^ (m - 1)), hc₁'pow, hc₃pow]
  have hlt : m - 1 < m := by omega
  have hsmul1 : (Phi (n := 2 ^ m) c' (fun j : Fin 3 => TMat m k k₂ k₃ j 2)) ^ (2 ^ (m - 1))
      = Phi (n := 2 ^ m) c'
          (((2 ^ (m - 1) : ℕ) : ZMod (2 ^ m)) • (fun j : Fin 3 => TMat m k k₂ k₃ j 2)) := by
    have h := (phi_smul hCab hc'mem hc'pow ((2 ^ (m - 1) : ℕ) : ZMod (2 ^ m))
      (fun j : Fin 3 => TMat m k k₂ k₃ j 2)).symm
    rwa [ZMod.val_natCast_of_lt (Nat.pow_lt_pow_right (by norm_num) hlt)] at h
  have hsmul2 : (Phi (n := 2 ^ m) c' (fun i : Fin 3 =>
        if i = 0 then (1 : ZMod (2 ^ m)) else if i = 1 then 0 else 1)) ^ (2 ^ (m - 1))
      = Phi (n := 2 ^ m) c'
          (((2 ^ (m - 1) : ℕ) : ZMod (2 ^ m)) • (fun i : Fin 3 =>
            if i = 0 then (1 : ZMod (2 ^ m)) else if i = 1 then 0 else 1)) := by
    have h := (phi_smul hCab hc'mem hc'pow ((2 ^ (m - 1) : ℕ) : ZMod (2 ^ m))
      (fun i : Fin 3 => if i = 0 then (1 : ZMod (2 ^ m)) else if i = 1 then 0 else 1)).symm
    rwa [ZMod.val_natCast_of_lt (Nat.pow_lt_pow_right (by norm_num) hlt)] at h
  have hk : ∃ u : ZMod (2 ^ m), k = 2 * u + 1 := by
    have hcoord : (((2 ^ (m - 1) : ℕ) : ZMod (2 ^ m))) * k
        = (((2 ^ (m - 1) : ℕ) : ZMod (2 ^ m))) * 1 := by
      have h1 : (((2 ^ (m - 1) : ℕ) : ZMod (2 ^ m))) • (fun j : Fin 3 => TMat m k k₂ k₃ j 2)
          = (((2 ^ (m - 1) : ℕ) : ZMod (2 ^ m))) • (fun i : Fin 3 =>
              if i = 0 then (1 : ZMod (2 ^ m)) else if i = 1 then 0 else 1) := by
        apply hPhi'_inj
        rw [← hsmul1, ← hsmul2, hpk, hpk2]
      have h2 := congrFun h1 0
      simpa [Pi.smul_apply, smul_eq_mul, TMat] using h2
    have h1 : (((2 ^ (m - 1) : ℕ) : ZMod (2 ^ m))) * (k - 1) = 0 := by
      have h2 : (((2 ^ (m - 1) : ℕ) : ZMod (2 ^ m))) * (k - 1)
          = (((2 ^ (m - 1) : ℕ) : ZMod (2 ^ m))) * k
            - (((2 ^ (m - 1) : ℕ) : ZMod (2 ^ m))) * 1 := by ring
      rw [h2, hcoord]
      ring
    have h3 : 2 ^ (m - 1) * (k - 1).val % 2 ^ m = 0 := by
      have h4 := congrArg ZMod.val h1
      rw [ZMod.val_mul, (ZMod.val_eq_zero (0 : ZMod (2 ^ m))).mpr rfl,
        ZMod.val_natCast_of_lt (Nat.pow_lt_pow_right (by norm_num) hlt)] at h4
      exact h4
    have key : ∀ n : ℕ, 2 ^ m ∣ 2 ^ (m - 1) * n → 2 ∣ n := by
      intro n hn
      have h7 : 2 ^ m = 2 ^ (m - 1) * 2 := by
        conv_lhs => rw [show m = (m - 1) + 1 by omega]
        rw [pow_succ]
      have h8 : 2 ^ (m - 1) * 2 ∣ 2 ^ (m - 1) * n := by rw [← h7]; exact hn
      exact Nat.dvd_of_mul_dvd_mul_left (by positivity) h8
    obtain ⟨s, hs⟩ := key (k - 1).val (Nat.dvd_iff_mod_eq_zero.mpr h3)
    refine ⟨(s : ZMod (2 ^ m)), ?_⟩
    have h8 : k - 1 = ((2 * s : ℕ) : ZMod (2 ^ m)) := by
      rw [← ZMod.natCast_zmod_val (k - 1), hs]
    rw [show k = (k - 1) + 1 by ring, h8]
    push_cast
    ring
  obtain ⟨x₀, hx₀⟩ := endgame_algebra m hm2 k k₂ k₃ hk h91 hT hA
  -- ## The image of `z ↦ b z b⁻¹ z` on `C` contains `c₁'` but not `c₁⁻¹`
  set b : G := (t * s₁) ^ 2 with hbdef
  have hbsq : b * b = c₁⁻¹ := by
    rw [hbdef, show (t * s₁) ^ 2 * (t * s₁) ^ 2 = (t * s₁) ^ 4 by group]
    exact h4
  have hb2C : b * b ∈ C := by rw [hbsq]; exact C.inv_mem hc₁C
  have hb_notC : b ∉ C := by
    intro hbin
    have h1 : MulAut.conjNormal (H := V) b = 1 := by
      apply MulEquiv.ext
      intro x
      rw [MulAut.one_apply]
      apply Subtype.ext
      rw [MulAut.conjNormal_apply]
      have hcv : (x : G) * b = b * (x : G) := (mem_C_iff V C hC b).mp hbin (x : G) x.2
      calc b * (x : G) * b⁻¹ = ((x : G) * b) * b⁻¹ := by rw [← hcv]
        _ = (x : G) := by group
    have h2 : MulAut.conjNormal (H := V) b = (tauV V e * sigmaV V e) ^ 2 := by
      rw [hbdef, pow_two, map_mul, map_mul, htc, hsc, ← pow_two]
    rw [h2] at h1
    exact tauV_mul_sigmaV_pow_two_ne_one V e h1
  have hbimg : ∀ z : G, z ∈ C → b * z * b⁻¹ * z ∈ C :=
    fun z hz => C.mul_mem (hCn.conj_mem z hz b) hz
  let φ : ↥C →* ↥C :=
    { toFun := fun z => ⟨b * (z : G) * b⁻¹ * (z : G), hbimg z z.2⟩
      map_one' := by
        apply Subtype.ext
        simp
      map_mul' := by
        intro x y
        apply Subtype.ext
        have hx : (x : G) ∈ C := x.2
        have hy : (y : G) ∈ C := y.2
        have hyb : b * (y : G) * b⁻¹ ∈ C := hCn.conj_mem _ hy b
        show b * ((x : G) * (y : G)) * b⁻¹ * ((x : G) * (y : G))
            = (b * (x : G) * b⁻¹ * (x : G)) * (b * (y : G) * b⁻¹ * (y : G))
        calc b * ((x : G) * (y : G)) * b⁻¹ * ((x : G) * (y : G))
            = (b * (x : G) * b⁻¹) * ((b * (y : G) * b⁻¹) * (x : G)) * (y : G) := by group
          _ = (b * (x : G) * b⁻¹) * ((x : G) * (b * (y : G) * b⁻¹)) * (y : G) := by
                rw [(hCab (x : G) hx (b * (y : G) * b⁻¹) hyb).symm]
          _ = (b * (x : G) * b⁻¹ * (x : G)) * (b * (y : G) * b⁻¹ * (y : G)) := by group }
  have hc₁'range : (⟨c₁', hc₁'mem⟩ : ↥C) ∈ φ.range := by
    have hΦ1 : Phi (n := 2 ^ m) c' (Pi.single (0 : Fin 3) (1 : ZMod (2 ^ m))) = c₁' := by
      simp [Phi, Pi.single_eq_same, Pi.single_eq_of_ne, hval1, hval0, hc'0, hc'1, hc'2]
    have hΦ2 : Phi (n := 2 ^ m) c'
        (Matrix.mulVec ((TMat m k k₂ k₃ * SMat m) ^ 2 + 1) x₀) = c₁' := by
      rw [hx₀, hΦ1]
    refine ⟨⟨Phi (n := 2 ^ m) c' x₀, hPhi'_mem x₀⟩, ?_⟩
    apply Subtype.ext
    show b * Phi (n := 2 ^ m) c' x₀ * b⁻¹ * Phi (n := 2 ^ m) c' x₀ = c₁'
    rw [← hΦ2, hbdef, Matrix.add_mulVec, Matrix.one_mulVec,
      ← hPhi'_mul (Matrix.mulVec ((TMat m k k₂ k₃ * SMat m) ^ 2) x₀) x₀, hpow 2 x₀]
  have hc₁'inv_zp : (⟨c₁⁻¹, C.inv_mem hc₁C⟩ : ↥C)
      ∈ Subgroup.zpowers (⟨c₁', hc₁'mem⟩ : ↥C) := by
    obtain ⟨bb, hbb⟩ := zmod_unit_of_odd (m := m) (x := y 0) hy0
    have h1 : c₁ = c₁' ^ bb.val := by
      rw [hc₁'def, ← pow_val_mul_aux c₁ hc₁2m (y 0) bb, hbb, hval1, pow_one]
    have h2 : (⟨c₁, hc₁C⟩ : ↥C) = (⟨c₁', hc₁'mem⟩ : ↥C) ^ bb.val := Subtype.ext h1
    refine Subgroup.mem_zpowers_iff.mpr ⟨-(bb.val : ℤ), ?_⟩
    rw [zpow_neg, zpow_natCast, ← h2]
    exact Subtype.ext rfl
  have hfinal : ∃ z ∈ C, b * z * b⁻¹ * z = b * b := by
    have hle : Subgroup.zpowers (⟨c₁', hc₁'mem⟩ : ↥C) ≤ φ.range :=
      (Subgroup.zpowers_le).mpr hc₁'range
    obtain ⟨z, hz⟩ := hle hc₁'inv_zp
    refine ⟨(z : G), z.2, ?_⟩
    have h3 := congrArg (fun w : ↥C => (w : G)) hz
    rw [hbsq]
    exact h3
  exact constraint_step1 C hCn hout hb_notC hb2C hfinal
