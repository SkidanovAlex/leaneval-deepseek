/-
# Definitions for the abelian case of the hard core of Hering's theorem (Peterfalvi I §3 Prop. 2)

This file collects the definitions used by the computation in `abelian_case.lean`:

* `M3` is the model `(ℤ/2)³ = Multiplicative (Fin 3 → ZMod 2)` of the elementary abelian group
  `V` of order `8`, and `stdB i` its standard basis.
* `sigmaM`, `tauM` are the two transvections of `Aut((ℤ/2)³)` (the images `σ`, `τ` of the
  elements `s`, `t` of the source proof on `V`).  Since `M3` is a concrete finite type, all the
  elementary properties are proved by `decide`.
* `Omega V C hCab m` is the level-`m` subgroup `{x ∈ C : x ^ 2^m = 1}` of the abelian group `C`.
* `Phi c x = c₀ ^ x₀ · c₁ ^ x₁ · c₂ ^ x₂` is the coordinate map `(ℤ/2^m)³ → G` attached to a
  triple `c` of elements of `C`; it is the bridge between the group `G` and the matrix
  computation `endgame_algebra` of `EndgameDefs`/`endgame_algebra.lean`.
-/

import Mathlib
import Submission.Work.Hering.Config
import Submission.Work.Hering.Step5.mulAut_eight_order21
import Submission.Work.Hering.HardCore.EndgameDefs
import Submission.Work.Hering.HardCore.aut_involutions_conj
import Submission.Work.Hering.HardCore.closure_three_eq

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

set_option autoImplicit false

namespace Work.Hering.HardCore

open LeanEval.GroupTheory.Defs

variable {G : Type*} [Group G]

/-! ## Elementary facts about `ℤ/2` -/

/-- In `ℤ/2`, `x + x = 0`. -/
lemma add_self_eq_zero_zmod2' (x : ZMod 2) : x + x = 0 := by revert x; decide

/-- In `ℤ/2`, `a + b + b = a`. -/
lemma zmod2_add3 (a b : ZMod 2) : a + b + b = a := by
  rw [show a + b + b = a + (b + b) by abel, add_self_eq_zero_zmod2' b, add_zero]

/-- In `ℤ/2`, `a + b + c + b + c = a`. -/
lemma zmod2_pat (a b c : ZMod 2) : a + b + c + b + c = a := by
  rw [show a + b + c + b + c = a + (b + b) + (c + c) by abel,
    add_self_eq_zero_zmod2' b, add_self_eq_zero_zmod2' c, add_zero, add_zero]

/-! ## The model `(ℤ/2)³` and its transvections -/

/-- The model of the elementary abelian group `(ℤ/2)³`. -/
abbrev M3 : Type := Multiplicative (Fin 3 → ZMod 2)

/-- The standard basis vector `eᵢ` of `(ℤ/2)³`. -/
def stdB (i : Fin 3) : M3 := Multiplicative.ofAdd (Pi.single i (1 : ZMod 2))

/-- The automorphism of `Multiplicative M` induced by a linear equivalence of the additive group
`M` over `ℤ/2`. -/
def mulAutOfLinear {M : Type*} [AddCommGroup M] [Module (ZMod 2) M] (f : M ≃ₗ[ZMod 2] M) :
    MulAut (Multiplicative M) where
  toFun x := Multiplicative.ofAdd (f (Multiplicative.toAdd x))
  invFun y := Multiplicative.ofAdd (f.symm (Multiplicative.toAdd y))
  left_inv x := by simp
  right_inv y := by simp
  map_mul' x y := by simp [ofAdd_add, map_add]

/-- The underlying map of the transvection `σ` (`v₀ ↦ v₀`, `v₁ ↦ v₁`, `v₂ ↦ v₁ + v₂`). -/
def sigmaFun (x : Fin 3 → ZMod 2) : Fin 3 → ZMod 2 :=
  fun i => if i = 0 then x 0 else if i = 1 then x 1 + x 2 else x 2

/-- The underlying map of the transvection `τ` (`v₀ ↦ v₀`, `v₁ ↦ v₀ + v₁`, `v₂ ↦ v₀ + v₂`). -/
def tauFun (x : Fin 3 → ZMod 2) : Fin 3 → ZMod 2 :=
  fun i => if i = 0 then x 0 + x 1 + x 2 else if i = 1 then x 1 else x 2

/-- The linear equivalence underlying `σ` (an involution). -/
def sigmaLin : (Fin 3 → ZMod 2) ≃ₗ[ZMod 2] (Fin 3 → ZMod 2) where
  toFun := sigmaFun
  invFun := sigmaFun
  left_inv x := by
    funext i; fin_cases i <;> simp [sigmaFun] <;>
      first | rfl | exact zmod2_add3 _ _ | exact zmod2_pat _ _ _
  right_inv x := by
    funext i; fin_cases i <;> simp [sigmaFun] <;>
      first | rfl | exact zmod2_add3 _ _ | exact zmod2_pat _ _ _
  map_add' x y := by funext i; fin_cases i <;> simp [sigmaFun] <;> abel
  map_smul' c x := by funext i; fin_cases i <;> simp [sigmaFun] <;> ring

/-- The linear equivalence underlying `τ` (an involution). -/
def tauLin : (Fin 3 → ZMod 2) ≃ₗ[ZMod 2] (Fin 3 → ZMod 2) where
  toFun := tauFun
  invFun := tauFun
  left_inv x := by
    funext i; fin_cases i <;> simp [tauFun] <;>
      first | rfl | exact zmod2_add3 _ _ | exact zmod2_pat _ _ _
  right_inv x := by
    funext i; fin_cases i <;> simp [tauFun] <;>
      first | rfl | exact zmod2_add3 _ _ | exact zmod2_pat _ _ _
  map_add' x y := by funext i; fin_cases i <;> simp [tauFun] <;> abel
  map_smul' c x := by funext i; fin_cases i <;> simp [tauFun] <;> ring

/-- The transvection `σ` of `Aut((ℤ/2)³)`: `v₀ ↦ v₀`, `v₁ ↦ v₁`, `v₂ ↦ v₁v₂`. -/
def sigmaM : MulAut M3 := mulAutOfLinear sigmaLin

/-- The transvection `τ` of `Aut((ℤ/2)³)`: `v₀ ↦ v₀`, `v₁ ↦ v₀v₁`, `v₂ ↦ v₀v₂`. -/
def tauM : MulAut M3 := mulAutOfLinear tauLin

section M3facts

lemma sigmaM_stdB_zero : sigmaM (stdB 0) = stdB 0 := by decide
lemma sigmaM_stdB_one : sigmaM (stdB 1) = stdB 1 := by decide
lemma sigmaM_stdB_two : sigmaM (stdB 2) = stdB 1 * stdB 2 := by decide
lemma tauM_stdB_zero : tauM (stdB 0) = stdB 0 := by decide
lemma tauM_stdB_one : tauM (stdB 1) = stdB 0 * stdB 1 := by decide
lemma tauM_stdB_two : tauM (stdB 2) = stdB 0 * stdB 2 := by decide

lemma sigmaM_mul_self : sigmaM * sigmaM = 1 := by decide
lemma tauM_mul_self : tauM * tauM = 1 := by decide

/-- The fixed points of `σ` on `(ℤ/2)³` are `0, e₀, e₁, e₀+e₁`. -/
lemma sigmaM_fixed : ∀ x : M3, sigmaM x = x →
    x = 1 ∨ x = stdB 0 ∨ x = stdB 1 ∨ x = stdB 0 * stdB 1 := by decide

/-- The fixed points of `τ` on `(ℤ/2)³` are `0, e₀, e₁+e₂, e₀+e₁+e₂`. -/
lemma tauM_fixed : ∀ x : M3, tauM x = x →
    x = 1 ∨ x = stdB 0 ∨ x = stdB 1 * stdB 2 ∨ x = stdB 0 * (stdB 1 * stdB 2) := by decide

/-- The image of `σ + 1` on `(ℤ/2)³` is generated by `e₁`. -/
lemma sigmaM_add_one : ∀ x : M3, sigmaM x * x = 1 ∨ sigmaM x * x = stdB 1 := by decide

/-- The image of `τ + 1` on `(ℤ/2)³` is generated by `e₀`. -/
lemma tauM_add_one : ∀ x : M3, tauM x * x = 1 ∨ tauM x * x = stdB 0 := by decide

/-- The common fixed points of `σ` and `τ` on `(ℤ/2)³` are `0` and `e₀`. -/
lemma sigmaM_tauM_fixed : ∀ x : M3, sigmaM x = x → tauM x = x → x = 1 ∨ x = stdB 0 := by decide

/-- The fixed points of `τσ` on `(ℤ/2)³` are `0` and `e₀`. -/
lemma tauSigmaM_fixed : ∀ x : M3, (tauM * sigmaM) x = x → x = 1 ∨ x = stdB 0 := by decide

/-- `(τσ)⁴ = 1` in `Aut((ℤ/2)³)`. -/
lemma tauSigmaM_pow_four : (tauM * sigmaM) ^ 4 = 1 := by decide

/-- `(τσ)² ≠ 1` in `Aut((ℤ/2)³)`. -/
lemma tauSigmaM_pow_two_ne_one : (tauM * sigmaM) ^ 2 ≠ 1 := by decide

/-- `(στ)⁴ = 1` in `Aut((ℤ/2)³)`. -/
lemma sigmaM_mul_tauM_pow_four : (sigmaM * tauM) ^ 4 = 1 := by decide

/-- `(στ)² ≠ 1` in `Aut((ℤ/2)³)`. -/
lemma sigmaM_mul_tauM_pow_two_ne_one : (sigmaM * tauM) ^ 2 ≠ 1 := by decide

/-- The fixed points of `στ` on `(ℤ/2)³` are `0` and `e₀`. -/
lemma sigmaM_mul_tauM_fixed : ∀ x : M3, (sigmaM * tauM) x = x → x = 1 ∨ x = stdB 0 := by decide

/-- `(στ)²` maps `e₂` to `e₀ + e₂`. -/
lemma sigmaM_mul_tauM_sq_stdB_two : ((sigmaM * tauM) ^ 2) (stdB 2) = stdB 0 * stdB 2 := by decide

/-- `e₁ = v₂^σ · v₂`. -/
lemma sigmaM_add_one_stdB_two : sigmaM (stdB 2) * stdB 2 = stdB 1 := by decide

/-- `e₀ = v₁^τ · v₁`. -/
lemma tauM_add_one_stdB_one : tauM (stdB 1) * stdB 1 = stdB 0 := by decide

end M3facts

/-! ## The levels `Ω_m(C)` of the abelian group `C` -/

/-- `Ω_m(C) = {x ∈ C : x ^ 2^m = 1}`, for `C` abelian. -/
def Omega (C : Subgroup G) (hCab : ∀ x ∈ C, ∀ y ∈ C, x * y = y * x) (m : ℕ) : Subgroup G where
  carrier := {x : G | x ∈ C ∧ x ^ (2 ^ m) = 1}
  mul_mem' := by
    rintro a b ⟨haC, ha⟩ ⟨hbC, hb⟩
    refine ⟨C.mul_mem haC hbC, ?_⟩
    rw [Commute.mul_pow ((commute_iff_eq a b).mpr (hCab a haC b hbC)), ha, hb, one_mul]
  one_mem' := ⟨C.one_mem, by simp⟩
  inv_mem' := by
    rintro a ⟨haC, ha⟩
    exact ⟨C.inv_mem haC, by rw [inv_pow, ha, inv_one]⟩

/-- Membership in `Ω_m(C)`. -/
lemma mem_Omega {C : Subgroup G} {hCab : ∀ x ∈ C, ∀ y ∈ C, x * y = y * x} {m : ℕ} {x : G} :
    x ∈ Omega C hCab m ↔ x ∈ C ∧ x ^ (2 ^ m) = 1 := Iff.rfl

/-- `Ω_m(C) ≤ C`. -/
lemma Omega_le (C : Subgroup G) (hCab : ∀ x ∈ C, ∀ y ∈ C, x * y = y * x) (m : ℕ) :
    Omega C hCab m ≤ C := fun _ hx => hx.1

/-! ## The coordinate map `Φ` -/

/-- The coordinate map attached to a triple `c : Fin 3 → G`: `x ↦ c₀^x₀ · c₁^x₁ · c₂^x₂`. -/
def Phi {n : ℕ} (c : Fin 3 → G) (x : Fin 3 → ZMod n) : G :=
  c 0 ^ (x 0).val * c 1 ^ (x 1).val * c 2 ^ (x 2).val

/-- `Φ c 0 = 1`. -/
lemma Phi_zero {n : ℕ} (c : Fin 3 → G) : Phi c (0 : Fin 3 → ZMod n) = 1 := by
  simp [Phi]


variable {G : Type*} [Group G] [Finite G]

/-! ## Transitivity of `Aut(V)` on `V#` (re-derived from `aut_involutions_conj`)

The modules `HardCore.aut_transitive` and `HardCore.aut_involutions_conj` both declare the helper
`exists_linearEquiv_apply_eq_expTwo`, so they cannot be imported together.  Since the conjugacy of the
involutions of `Aut(V)` (`aut_involutions_conj`) is needed here, the transitivity of `Aut(V)` on
`V#` is re-derived from that module instead. -/

/-- The group `(ℤ/2)³` is transitive on its non-identity elements. -/
private lemma mulAut_transitive_fin3_aux (v w : Multiplicative (Fin 3 → ZMod 2))
    (hv : v ≠ 1) (hw : w ≠ 1) :
    ∃ φ : MulAut (Multiplicative (Fin 3 → ZMod 2)), φ v = w := by
  have hv' : Multiplicative.toAdd v ≠ 0 := fun h0 =>
    hv (by simpa using congrArg Multiplicative.ofAdd h0)
  have hw' : Multiplicative.toAdd w ≠ 0 := fun h0 =>
    hw (by simpa using congrArg Multiplicative.ofAdd h0)
  obtain ⟨e, he⟩ := exists_linearEquiv_apply_eq_expTwo hv' hw'
  refine ⟨{ toFun := fun x => Multiplicative.ofAdd (e (Multiplicative.toAdd x))
            invFun := fun y => Multiplicative.ofAdd (e.symm (Multiplicative.toAdd y))
            left_inv := by intro x; simp
            right_inv := by intro y; simp
            map_mul' := by intro x y; simp [toAdd_mul, ofAdd_add, map_add] }, ?_⟩
  show Multiplicative.ofAdd (e (Multiplicative.toAdd v)) = w
  rw [he, ofAdd_toAdd]

/-- **`Aut(V)` is transitive on `V#`** for `V` a group of order `8` and exponent `2`. -/
private lemma aut_transitive_aux {U : Type*} [Group U] [Finite U] (hcard : Nat.card U = 8)
    (hexp : ∀ x : U, x * x = 1) :
    ∀ v w : U, v ≠ 1 → w ≠ 1 → ∃ φ : MulAut U, φ v = w := by
  intro v w hv hw
  obtain ⟨e⟩ := Work.Hering.Step5.iso_fin3 hcard hexp
  have hev : e v ≠ 1 := fun h1 => hv (by simpa using congrArg e.symm h1)
  have hew : e w ≠ 1 := fun h1 => hw (by simpa using congrArg e.symm h1)
  obtain ⟨φ', hφ'⟩ := mulAut_transitive_fin3_aux (e v) (e w) hev hew
  refine ⟨(e.trans φ').trans e.symm, ?_⟩
  rw [MulEquiv.trans_apply, MulEquiv.trans_apply, hφ', MulEquiv.symm_apply_apply]

/-! ## Basic consequences of the configuration -/

section Basic

variable (V C : Subgroup G)

/-- In the configuration, `V` has exponent two, hence is abelian. -/
lemma V_comm (hexp : ∀ x ∈ V, x * x = 1) {x y : G} (hx : x ∈ V) (hy : y ∈ V) :
    x * y = y * x := by
  have hx1 : x * x = 1 := hexp x hx
  have hy1 : y * y = 1 := hexp y hy
  have hxy : (x * y) * (x * y) = 1 := hexp (x * y) (V.mul_mem hx hy)
  have hxinv : x⁻¹ = x := inv_eq_of_mul_eq_one_right hx1
  have hyinv : y⁻¹ = y := inv_eq_of_mul_eq_one_right hy1
  have h2 : x * y = (x * y)⁻¹ := (inv_eq_of_mul_eq_one_right hxy).symm
  rw [mul_inv_rev, hxinv, hyinv] at h2
  exact h2

/-- `C = C_G(V)` consists of the elements of `G` commuting with every element of `V`. -/
lemma mem_C_iff (hC : C = Subgroup.centralizer ((V : Set G))) (x : G) :
    x ∈ C ↔ ∀ v ∈ (V : Set G), v * x = x * v := by
  rw [hC, Subgroup.mem_centralizer_iff]

/-- `V` is contained in `C = C_G(V)`, because it is abelian. -/
lemma V_le_C (hC : C = Subgroup.centralizer ((V : Set G)))
    (hexp : ∀ x ∈ V, x * x = 1) : V ≤ C := by
  intro x hx
  rw [mem_C_iff V C hC]
  intro v hv
  exact V_comm V hexp hv hx

/-- `C = C_G(V)` is normal in `G`. -/
lemma C_normal (hV : V.Normal) (hC : C = Subgroup.centralizer ((V : Set G))) : C.Normal := by
  rw [hC]
  exact Subgroup.normal_centralizer

/-- Every non-identity element of `V` has order two. -/
lemma orderOf_two_of_mem_V (hexp : ∀ x ∈ V, x * x = 1) {x : G} (hx : x ∈ V) (h1 : x ≠ 1) :
    orderOf x = 2 := by
  have h2 : x ^ 2 = 1 := by rw [pow_two]; exact hexp x hx
  exact orderOf_eq_prime h2 h1

/-- Every element of `C` of order two lies in `V`; every element of `V \ {1}` has order two. -/
lemma mem_V_iff (hexp : ∀ x ∈ V, x * x = 1) (hinv : ∀ x ∈ C, orderOf x = 2 → x ∈ V)
    {x : G} (hx : x ∈ C) : x ∈ V ↔ x * x = 1 := by
  constructor
  · intro h
    exact hexp x h
  · intro h
    rcases eq_or_ne x 1 with rfl | h1
    · exact V.one_mem
    · have h2 : x ^ 2 = 1 := by rw [pow_two]; exact h
      exact hinv x hx (orderOf_eq_prime h2 h1)

/-- Every element of order two of `G` lies in `V`. -/
lemma mem_V_of_orderOf_two (hinv : ∀ x ∈ C, orderOf x = 2 → x ∈ V)
    (hnoinv : ∀ u : G, orderOf u = 2 → u ∈ C) {u : G} (h : orderOf u = 2) : u ∈ V :=
  hinv u (hnoinv u h) h

/-- `Inv(G) = V#`, i.e. the set of involutions of `G` is the set of non-identity elements of
`V`. -/
lemma involutions_eq (hexp : ∀ x ∈ V, x * x = 1) (hinv : ∀ x ∈ C, orderOf x = 2 → x ∈ V)
    (hnoinv : ∀ u : G, orderOf u = 2 → u ∈ C) :
    {u : G | orderOf u = 2} = ((V : Set G) \ {1}) := by
  ext u
  constructor
  · intro hu
    refine ⟨mem_V_of_orderOf_two V C hinv hnoinv hu, ?_⟩
    simp only [Set.mem_singleton_iff]
    intro h
    simp only [Set.mem_ofPred_eq] at hu
    rw [h, orderOf_one] at hu
    exact absurd hu (by norm_num)
  · rintro ⟨hu, hu1⟩
    exact orderOf_two_of_mem_V V hexp hu (by simpa using hu1)

/-- The elements of `C` of order dividing two are exactly the elements of `V`. -/
lemma Omega1_C (hC : C = Subgroup.centralizer ((V : Set G)))
    (hexp : ∀ x ∈ V, x * x = 1) (hinv : ∀ x ∈ C, orderOf x = 2 → x ∈ V) :
    {x : G | x ∈ C ∧ x * x = 1} = (V : Set G) := by
  ext x
  constructor
  · rintro ⟨hxC, hx2⟩
    rcases eq_or_ne x 1 with rfl | h1
    · exact V.one_mem
    · have h2 : x ^ 2 = 1 := by rw [pow_two]; exact hx2
      exact hinv x hxC (orderOf_eq_prime h2 h1)
  · intro hx
    exact ⟨V_le_C V C hC hexp hx, hexp x hx⟩

end Basic

/-! ## Step 1 of Peterfalvi I §3 Prop. 2: the cosets of `C` over transvections contain no
involution -/

section Constraint

variable (C : Subgroup G)

/-- **Step 1 of Peterfalvi I §3 Prop. 2.** If `x ∉ C` and `x * x ∈ C` then no element of the
coset `xC` is an involution: there is no `c ∈ C` with `(xc)² = 1`.  Equivalently
`x * x ∉ Im(x̄ + 1)` in the module `C`. -/
lemma constraint_step1 (hCn : C.Normal)
    (hnoinv : ∀ u : G, orderOf u = 2 → u ∈ C)
    {x : G} (hxC : x ∉ C) (hx2 : x * x ∈ C) :
    ¬ ∃ c ∈ C, x * c * x⁻¹ * c = x * x := by
  rintro ⟨c, hcC, hc⟩
  -- `x * c * x⁻¹ = (x * x) * c⁻¹`
  have h1 : x * c * x⁻¹ = (x * x) * c⁻¹ := by
    rw [← hc]; group
  -- invert it
  have h2 : x * c⁻¹ * x⁻¹ = c * (x * x)⁻¹ := by
    have h1' := congrArg Inv.inv h1
    simpa [mul_inv_rev, inv_inv, mul_assoc] using h1'
  -- hence `(x * c⁻¹)² = 1`
  have h3 : (x * c⁻¹) * (x * c⁻¹) = 1 :=
    calc (x * c⁻¹) * (x * c⁻¹) = (x * c⁻¹ * x⁻¹) * (x * x) * c⁻¹ := by group
      _ = (c * (x * x)⁻¹) * (x * x) * c⁻¹ := by rw [h2]
      _ = 1 := by group
  have hne : x * c⁻¹ ≠ 1 := by
    intro h
    apply hxC
    have h' := congrArg (fun t => t * c) h
    have : x = c := by simpa [mul_assoc] using h'
    rw [this]; exact hcC
  have h4 : (x * c⁻¹) ^ 2 = 1 := by rw [pow_two]; exact h3
  have hord : orderOf (x * c⁻¹) = 2 := orderOf_eq_prime h4 hne
  have hmem : x * c⁻¹ ∈ C := hnoinv _ hord
  apply hxC
  have h5 : x = (x * c⁻¹) * c := by group
  rw [h5]
  exact C.mul_mem hmem hcC

end Constraint

/-! ## Powers of elements of `C` cover `V`

The transitivity of the conjugation action on `V#` shows that once *one* element of `V#` is a
`2^{k}`-th power of an element of `C`, then *every* element of `V` is such a power.  This is the
form in which the structure of `C` is used: for `k = 1` it says that every element of `V` is a
square in `C`, and for `k = m - 1` it produces the elements `c₁, c₂, c₃` of the source proof. -/

section Powers

variable (V C : Subgroup G)

/-- If some `2^{k-1}`-th power of an element of `C` is a non-identity element of `V`, then the
`2^{k-1}`-th powers of elements of `C` exhaust `V`. -/
lemma pow_image_eq_V (hV : V.Normal) (hcard : Nat.card V = 8)
    (hexp : ∀ x ∈ V, x * x = 1) (hC : C = Subgroup.centralizer ((V : Set G)))
    (hCab : ∀ x ∈ C, ∀ y ∈ C, x * y = y * x)
    (htrans : ∀ v ∈ V, ∀ w ∈ V, v ≠ 1 → w ≠ 1 → ∃ g : G, w = g * v * g⁻¹)
    (k : ℕ) {d : G} (hdC : d ∈ C) (hd : d ^ (2 ^ (k - 1)) ∈ V)
    (hd1 : d ^ (2 ^ (k - 1)) ≠ 1) :
    ∀ v ∈ V, ∃ c ∈ C, c ^ (2 ^ (k - 1)) = v := by
  classical
  have hCn : C.Normal := C_normal V C hV hC
  intro v hv
  rcases eq_or_ne v 1 with rfl | hv1
  · exact ⟨1, C.one_mem, by rw [one_pow]⟩
  · -- conjugate the witness to `v`
    obtain ⟨g, hg⟩ := htrans (d ^ (2 ^ (k - 1))) hd v hv hd1 hv1
    refine ⟨g * d * g⁻¹, hCn.conj_mem d hdC g, ?_⟩
    rw [show g * d * g⁻¹ = MulAut.conj g d from (MulAut.conj_apply g d).symm, ← map_pow,
      MulAut.conj_apply]
    exact hg.symm

end Powers

/-! ## The orders of the elements `c₁, c₂, c₃`

In the source's computation one has `cᵢ ^ 2 ^ (m-1) = vᵢ` with `vᵢ ∈ V#`.  Since `vᵢ` is an
involution different from `1`, `cᵢ` has order exactly `2 ^ m`. -/

section Orders

variable {m : ℕ}

/-- If `c ^ 2 ^ (m-1) = v` with `v ≠ 1` and `v * v = 1`, then `orderOf c = 2 ^ m`. -/
lemma orderOf_eq_two_pow_of_pow_eq {c v : G} (hm : 1 ≤ m) (hv1 : v ≠ 1) (hv2 : v * v = 1)
    (h : c ^ 2 ^ (m - 1) = v) : orderOf c = 2 ^ m := by
  have hnot : ¬ c ^ 2 ^ (m - 1) = 1 := by rw [h]; exact hv1
  have hfin : c ^ 2 ^ (m - 1 + 1) = 1 := by
    rw [show (2 : ℕ) ^ (m - 1 + 1) = 2 ^ (m - 1) * 2 by rw [pow_succ], pow_mul, h]
    rw [pow_two]
    exact hv2
  have := orderOf_eq_prime_pow (p := 2) (n := m - 1) hnot hfin
  rwa [show m - 1 + 1 = m by omega] at this

end Orders

/-! ## The `2`-adic independence of `c₁, c₂, c₃`

This is the engine of the source's computation: if `c₁, c₂, c₃ ∈ C` have `2^(m-1)`-th powers
`v₁, v₂, v₃` forming a basis of `V = Ω₁(C)`, then the exponents in any relation
`c₁^A · c₂^B · c₃^C = 1` are divisible by every power of two up to `2^m`, hence vanish modulo
`2^m`. -/

section Independent

variable (V C : Subgroup G)

/-- If `x * y * z = 1` with `x, y, z ∈ C` (abelian), then `x^n * y^n * z^n = 1`. -/
lemma mul_pow_three {C : Subgroup G} (hCab : ∀ x ∈ C, ∀ y ∈ C, x * y = y * x)
    {x y z : G} (hx : x ∈ C) (hy : y ∈ C) (hz : z ∈ C) (h : x * y * z = 1) (n : ℕ) :
    x ^ n * y ^ n * z ^ n = 1 := by
  have hyz : y * z ∈ C := C.mul_mem hy hz
  have hc1 : Commute x (y * z) := (commute_iff_eq x (y * z)).mpr (hCab x hx (y * z) hyz)
  have hc2 : Commute y z := (commute_iff_eq y z).mpr (hCab y hy z hz)
  have h1 : (x * y * z) ^ n = x ^ n * (y * z) ^ n := by
    rw [show x * y * z = x * (y * z) by group]
    exact hc1.mul_pow n
  have h2 : (y * z) ^ n = y ^ n * z ^ n := hc2.mul_pow n
  have hxyz : (x * y * z) ^ n = 1 := by rw [h, one_pow]
  rw [h1, h2] at hxyz
  simpa [mul_assoc] using hxyz

/-- If `x * x = 1` then `x ^ n = x ^ (n % 2)`. -/
lemma pow_eq_pow_mod_two {x : G} (hx : x * x = 1) (n : ℕ) : x ^ n = x ^ (n % 2) := by
  conv_lhs => rw [← Nat.div_add_mod n 2]
  rw [pow_add, pow_mul, show x ^ 2 = 1 by rwa [pow_two], one_pow, one_mul]

/-- **The `2`-adic independence.**  Let `C` be abelian with `Ω₁(C) = V`, let `v₁, v₂, v₃` be
elements of `V` independent over `𝔽₂`, and let `c₁, c₂, c₃ ∈ C` satisfy
`cᵢ ^ 2 ^ (m-1) = vᵢ`.  Then a relation `c₁ ^ A * c₂ ^ B * c₃ ^ D = 1` with
`A, B, D < 2 ^ m` forces `A = B = D = 0`. -/
theorem pow_independent (hVC : V ≤ C) (hOmega : ∀ x : G, x ∈ C → (x * x = 1 ↔ x ∈ V))
    (hCab : ∀ x ∈ C, ∀ y ∈ C, x * y = y * x)
    {m : ℕ} (hm : 1 ≤ m) {c₁ c₂ c₃ v₁ v₂ v₃ : G}
    (hc₁ : c₁ ∈ C) (hc₂ : c₂ ∈ C) (hc₃ : c₃ ∈ C)
    (hv₁ : v₁ ∈ V) (hv₂ : v₂ ∈ V) (hv₃ : v₃ ∈ V)
    (h₁ : c₁ ^ 2 ^ (m - 1) = v₁) (h₂ : c₂ ^ 2 ^ (m - 1) = v₂) (h₃ : c₃ ^ 2 ^ (m - 1) = v₃)
    (hind : ∀ a b c : ℕ, a < 2 → b < 2 → c < 2 → v₁ ^ a * v₂ ^ b * v₃ ^ c = 1 →
      a = 0 ∧ b = 0 ∧ c = 0) :
    ∀ A B D : ℕ, A < 2 ^ m → B < 2 ^ m → D < 2 ^ m →
      c₁ ^ A * c₂ ^ B * c₃ ^ D = 1 → A = 0 ∧ B = 0 ∧ D = 0 := by
  have hv₁2 : v₁ * v₁ = 1 := (hOmega v₁ (hVC hv₁)).mpr hv₁
  have hv₂2 : v₂ * v₂ = 1 := (hOmega v₂ (hVC hv₂)).mpr hv₂
  have hv₃2 : v₃ * v₃ = 1 := (hOmega v₃ (hVC hv₃)).mpr hv₃
  -- raising a relation to `2^(m-1-t)` shows the exponents even
  have parity : ∀ t : ℕ, t ≤ m - 1 → ∀ A B D : ℕ,
      (c₁ ^ 2 ^ t) ^ A * (c₂ ^ 2 ^ t) ^ B * (c₃ ^ 2 ^ t) ^ D = 1 →
      2 ∣ A ∧ 2 ∣ B ∧ 2 ∣ D := by
    intro t ht A B D hrel
    have e₁ : (c₁ ^ 2 ^ t) ^ 2 ^ (m - 1 - t) = v₁ := by
      rw [← pow_mul, show 2 ^ t * 2 ^ (m - 1 - t) = 2 ^ (m - 1) by
        rw [← pow_add]; congr 1; omega, h₁]
    have e₂ : (c₂ ^ 2 ^ t) ^ 2 ^ (m - 1 - t) = v₂ := by
      rw [← pow_mul, show 2 ^ t * 2 ^ (m - 1 - t) = 2 ^ (m - 1) by
        rw [← pow_add]; congr 1; omega, h₂]
    have e₃ : (c₃ ^ 2 ^ t) ^ 2 ^ (m - 1 - t) = v₃ := by
      rw [← pow_mul, show 2 ^ t * 2 ^ (m - 1 - t) = 2 ^ (m - 1) by
        rw [← pow_add]; congr 1; omega, h₃]
    have hpow : v₁ ^ A * v₂ ^ B * v₃ ^ D = 1 := by
      have hmem₁ : c₁ ^ 2 ^ t ∈ C := C.pow_mem hc₁ _
      have hmem₂ : c₂ ^ 2 ^ t ∈ C := C.pow_mem hc₂ _
      have hmem₃ : c₃ ^ 2 ^ t ∈ C := C.pow_mem hc₃ _
      have h := mul_pow_three hCab (C.pow_mem hmem₁ A) (C.pow_mem hmem₂ B)
        (C.pow_mem hmem₃ D) hrel (2 ^ (m - 1 - t))
      rw [show ((c₁ ^ 2 ^ t) ^ A) ^ 2 ^ (m - 1 - t) = v₁ ^ A by
            rw [← pow_mul, mul_comm, pow_mul, e₁],
          show ((c₂ ^ 2 ^ t) ^ B) ^ 2 ^ (m - 1 - t) = v₂ ^ B by
            rw [← pow_mul, mul_comm, pow_mul, e₂],
          show ((c₃ ^ 2 ^ t) ^ D) ^ 2 ^ (m - 1 - t) = v₃ ^ D by
            rw [← pow_mul, mul_comm, pow_mul, e₃]] at h
      exact h
    have hmod : v₁ ^ (A % 2) * v₂ ^ (B % 2) * v₃ ^ (D % 2) = 1 := by
      rwa [pow_eq_pow_mod_two hv₁2 A, pow_eq_pow_mod_two hv₂2 B,
        pow_eq_pow_mod_two hv₃2 D] at hpow
    obtain ⟨ha, hb, hc⟩ := hind (A % 2) (B % 2) (D % 2)
      (Nat.mod_lt _ (by norm_num)) (Nat.mod_lt _ (by norm_num)) (Nat.mod_lt _ (by norm_num)) hmod
    exact ⟨⟨A / 2, by omega⟩, ⟨B / 2, by omega⟩, ⟨D / 2, by omega⟩⟩
  -- grinding up the `2`-adic valuation of the exponents
  have key : ∀ t ≤ m, ∀ A B D : ℕ, c₁ ^ A * c₂ ^ B * c₃ ^ D = 1 →
      2 ^ t ∣ A ∧ 2 ^ t ∣ B ∧ 2 ^ t ∣ D := by
    intro t ht
    induction t with
    | zero => intro A B D _; exact ⟨one_dvd _, one_dvd _, one_dvd _⟩
    | succ t ih =>
      intro A B D hrel
      obtain ⟨hA, hB, hD⟩ := ih (by omega) A B D hrel
      obtain ⟨A₁, rfl⟩ := hA
      obtain ⟨B₁, rfl⟩ := hB
      obtain ⟨D₁, rfl⟩ := hD
      have hrel' : (c₁ ^ 2 ^ t) ^ A₁ * (c₂ ^ 2 ^ t) ^ B₁ * (c₃ ^ 2 ^ t) ^ D₁ = 1 := by
        have e₁' : (c₁ ^ 2 ^ t) ^ A₁ = c₁ ^ (2 ^ t * A₁) := (pow_mul c₁ (2 ^ t) A₁).symm
        have e₂' : (c₂ ^ 2 ^ t) ^ B₁ = c₂ ^ (2 ^ t * B₁) := (pow_mul c₂ (2 ^ t) B₁).symm
        have e₃' : (c₃ ^ 2 ^ t) ^ D₁ = c₃ ^ (2 ^ t * D₁) := (pow_mul c₃ (2 ^ t) D₁).symm
        rw [e₁', e₂', e₃']
        exact hrel
      obtain ⟨hA₁, hB₁, hD₁⟩ := parity t (by omega) A₁ B₁ D₁ hrel'
      obtain ⟨A₂, rfl⟩ := hA₁
      obtain ⟨B₂, rfl⟩ := hB₁
      obtain ⟨D₂, rfl⟩ := hD₁
      exact ⟨⟨A₂, by ring⟩, ⟨B₂, by ring⟩, ⟨D₂, by ring⟩⟩
  intro A B D hA hB hD hrel
  obtain ⟨hdvdA, hdvdB, hdvdD⟩ := key m le_rfl A B D hrel
  exact ⟨Nat.eq_zero_of_dvd_of_lt hdvdA hA, Nat.eq_zero_of_dvd_of_lt hdvdB hB,
    Nat.eq_zero_of_dvd_of_lt hdvdD hD⟩

end Independent

/-! ## Step (6.2): the image of `x ↦ x^s · x` on `⟨c₁, c₂, c₃⟩`

If conjugation by `s` acts on the generators `c₁, c₂, c₃` of `H = ⟨c₁, c₂, c₃⟩` as
`c₁ ↦ c₁⁻¹`, `c₂ ↦ c₂`, `c₃ ↦ c₂c₃⁻¹` (the matrix `SMat`), then `x ↦ x^s · x` maps `H` into the
cyclic group `⟨c₂⟩`; and `c₂` itself is such an image (of `c₃`), so the image is exactly
`⟨c₂⟩`, cyclic of order `2^m`.  This is the source's step (6.2); by conjugating it (the
involutions of `G/C ≅ GL(3,2)` form one class) it gives (7.1) for every involution. -/

section Step62

variable (C : Subgroup G)

/-- **(6.2).**  With `c₁^s = c₁⁻¹`, `c₂^s = c₂`, `c₃^s = c₂c₃⁻¹`, the image of `x ↦ x^s · x` on
`⟨c₁, c₂, c₃⟩` lies in `⟨c₂⟩`, and `c₂ = c₃^s · c₃` is attained. -/
lemma image_conj_add_one (hCn : C.Normal) (hCab : ∀ x ∈ C, ∀ y ∈ C, x * y = y * x)
    {s c₁ c₂ c₃ : G} (hc₁ : c₁ ∈ C) (hc₂ : c₂ ∈ C) (hc₃ : c₃ ∈ C)
    (h1 : s * c₁ * s⁻¹ = c₁⁻¹) (h2 : s * c₂ * s⁻¹ = c₂)
    (h3 : s * c₃ * s⁻¹ = c₂ * c₃⁻¹) :
    ∀ x ∈ Subgroup.closure ({c₁, c₂, c₃} : Set G),
      s * x * s⁻¹ * x ∈ Subgroup.zpowers c₂ := by
  have hH_le : Subgroup.closure ({c₁, c₂, c₃} : Set G) ≤ C :=
    (Subgroup.closure_le C).mpr (by
      rintro y (rfl | rfl | rfl)
      · exact hc₁
      · exact hc₂
      · exact hc₃)
  have hconj : ∀ y ∈ C, s * y * s⁻¹ ∈ C := fun y hy => hCn.conj_mem y hy s
  intro x hx
  refine Subgroup.closure_induction (k := ({c₁, c₂, c₃} : Set G)) ?_ ?_ ?_ ?_ hx
  · intro y hy
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hy
    rcases hy with hy1 | hy2 | hy3
    · rw [hy1]
      have : s * c₁ * s⁻¹ * c₁ = 1 := by rw [h1]; group
      rw [this]; exact Subgroup.one_mem _
    · rw [hy2]
      have : s * c₂ * s⁻¹ * c₂ = c₂ ^ (2 : ℤ) := by rw [h2, zpow_ofNat, pow_two]
      rw [this]; exact Subgroup.mem_zpowers_iff.mpr ⟨2, rfl⟩
    · rw [hy3]
      have : s * c₃ * s⁻¹ * c₃ = c₂ ^ (1 : ℤ) := by rw [h3, zpow_one]; group
      rw [this]; exact Subgroup.mem_zpowers_iff.mpr ⟨1, rfl⟩
  · rw [show s * 1 * s⁻¹ * 1 = 1 by group]
    exact Subgroup.one_mem _
  · intro a b ha hb hpa hpb
    have haC : a ∈ C := hH_le ha
    have hbC : b ∈ C := hH_le hb
    have hsaC : s * a * s⁻¹ ∈ C := hconj a haC
    have hsbC : s * b * s⁻¹ ∈ C := hconj b hbC
    have hstep : ((s * a * s⁻¹) * (s * b * s⁻¹)) * (a * b)
        = ((s * a * s⁻¹) * a) * ((s * b * s⁻¹) * b) := by
      have hswap : (s * b * s⁻¹) * a = a * (s * b * s⁻¹) := hCab _ hsbC a haC
      calc ((s * a * s⁻¹) * (s * b * s⁻¹)) * (a * b)
          = (s * a * s⁻¹) * ((s * b * s⁻¹) * a) * b := by group
        _ = (s * a * s⁻¹) * (a * (s * b * s⁻¹)) * b := by rw [hswap]
        _ = ((s * a * s⁻¹) * a) * ((s * b * s⁻¹) * b) := by group
    have hone : s * (a * b) * s⁻¹ * (a * b)
        = ((s * a * s⁻¹) * (s * b * s⁻¹)) * (a * b) := by group
    rw [hone, hstep]
    exact Subgroup.mul_mem _ hpa hpb
  · intro a ha hpa
    have haC : a ∈ C := hH_le ha
    have hsaC : s * a * s⁻¹ ∈ C := hconj a haC
    have hsa_invC : (s * a * s⁻¹)⁻¹ ∈ C := C.inv_mem hsaC
    have key : s * a⁻¹ * s⁻¹ * a⁻¹ = (s * a * s⁻¹ * a)⁻¹ := by
      rw [show s * a * s⁻¹ * a = (s * a * s⁻¹) * a by group, mul_inv_rev,
        show (s * a * s⁻¹)⁻¹ = s * a⁻¹ * s⁻¹ by group,
        hCab a⁻¹ (C.inv_mem haC) (s * a⁻¹ * s⁻¹) (by
          rw [show s * a⁻¹ * s⁻¹ = (s * a * s⁻¹)⁻¹ by group]; exact hsa_invC)]
    rw [key]
    exact Subgroup.inv_mem _ hpa

end Step62

/-! ## Transport of the image of `x ↦ x^g · x` along conjugation

If `t ≡ g s g⁻¹` modulo `C` (with `C` normal and abelian), then conjugating the image of
`x ↦ x^s · x` by `g` gives the image of `x ↦ x^t · x`.  Combined with (6.2) and the fact that
`s` and `t` realise conjugate transvections of `V = Ω₁(C)`, this is the source's step (7.1):
for every involution of `G/C`, the image of `x ↦ x^x̄ · x` on `C` is cyclic of order `2^m`. -/

section Transport

variable (C : Subgroup G)

/-- **Transport.**  If `t = g * s * g⁻¹ * c` with `c ∈ C` (`C` normal abelian), then
`x^t · x = g · (y^s · y) · g⁻¹` for `y = g⁻¹ x g`. -/
lemma image_conj_add_one_transport (hCn : C.Normal)
    (hCab : ∀ x ∈ C, ∀ y ∈ C, x * y = y * x)
    {s t g c : G} (hc : c ∈ C) (h : t = g * s * g⁻¹ * c) :
    ∀ x ∈ C, t * x * t⁻¹ * x
      = g * (s * (g⁻¹ * x * g) * s⁻¹ * (g⁻¹ * x * g)) * g⁻¹ := by
  intro x hx
  have hxg : g⁻¹ * x * g ∈ C := by
    have := hCn.conj_mem x hx g⁻¹
    simpa [mul_assoc] using this
  have htx : t * x * t⁻¹ = g * (s * (g⁻¹ * x * g) * s⁻¹) * g⁻¹ := by
    rw [h]
    rw [show (g * s * g⁻¹ * c)⁻¹ = c⁻¹ * g * s⁻¹ * g⁻¹ by group]
    rw [show g * s * g⁻¹ * c * x * (c⁻¹ * g * s⁻¹ * g⁻¹)
          = (g * s * g⁻¹) * (c * x) * (c⁻¹ * g * s⁻¹ * g⁻¹) by group]
    rw [hCab c hc x hx]
    group
  rw [htx]
  group

end Transport


/-! ## The cosets of `C` outside `C` contain no involutions -/

section Cosets

variable (C : Subgroup G)

/-- If all involutions of `G` lie in `C`, then for `x ∉ C` no element of the coset `xC` is an
involution. -/
lemma sq_ne_one_of_coset (hnoinv : ∀ u : G, orderOf u = 2 → u ∈ C)
    {x : G} (hxC : x ∉ C) (c : G) (hc : c ∈ C) : (x * c) * (x * c) ≠ 1 := by
  intro h
  have h2 : (x * c) ^ 2 = 1 := by rw [pow_two]; exact h
  rcases eq_or_ne (x * c) 1 with h1 | h1
  · exact hxC (by rw [show x = (x * c) * c⁻¹ by group, h1, one_mul]; exact C.inv_mem hc)
  · have hord : orderOf (x * c) = 2 := orderOf_eq_prime h2 h1
    have hmem : x * c ∈ C := hnoinv _ hord
    exact hxC (by rw [show x = (x * c) * c⁻¹ by group]; exact C.mul_mem hmem (C.inv_mem hc))

end Cosets

/-! ## `Aut(V)`-transitivity and the action of `G` on `V#` -/

section Trans

variable (V : Subgroup G)

/-- `G` acts transitively by conjugation on `V#`, because every automorphism of `V` is realised
(`hAut`) and `Aut(V)` is transitive on `V#`. -/
lemma trans_of_hAut (hV : V.Normal) (hcard : Nat.card V = 8) (hexp : ∀ x ∈ V, x * x = 1)
    (hAut : ActsAsAut V hV) :
    ∀ v ∈ V, ∀ w ∈ V, v ≠ 1 → w ≠ 1 → ∃ g : G, w = g * v * g⁻¹ := by
  intro v hv w hw hv1 hw1
  have hcard' : Nat.card ↥V = 8 := hcard
  have hexp' : ∀ x : ↥V, x * x = 1 := fun x => Subtype.ext (by simpa using hexp x x.2)
  obtain ⟨φ, hφ⟩ := aut_transitive_aux hcard' hexp' ⟨v, hv⟩ ⟨w, hw⟩
    (by simpa using hv1) (by simpa using hw1)
  obtain ⟨g, hg⟩ := hAut φ
  refine ⟨g, ?_⟩
  have h1 := hg ⟨v, hv⟩
  rw [hφ] at h1
  simpa using congrArg Subtype.val h1

end Trans

/-! ## The second level `C₂ = {c ∈ C : c² ∈ V}` -/

section Level2

variable (V C : Subgroup G)

/-- `C₂ = {c ∈ C | c² ∈ V}`: the second level of the abelian `2`-group `C`.  It is a subgroup
because `C` is abelian. -/
def level2 (hC : C = Subgroup.centralizer ((V : Set G)))
    (hCab : ∀ x ∈ C, ∀ y ∈ C, x * y = y * x)
    (hexp : ∀ x ∈ V, x * x = 1) : Subgroup G where
  carrier := {x : G | x ∈ C ∧ x * x ∈ V}
  mul_mem' := by
    intro a b ha hb
    obtain ⟨haC, ha2⟩ := ha
    obtain ⟨hbC, hb2⟩ := hb
    refine ⟨C.mul_mem haC hbC, ?_⟩
    have hcomm : a * b = b * a := hCab a haC b hbC
    have hsq : (a * b) * (a * b) = (a * a) * (b * b) := by
      calc (a * b) * (a * b) = a * (b * a) * b := by group
        _ = a * (a * b) * b := by rw [hcomm]
        _ = (a * a) * (b * b) := by group
    rw [hsq]
    exact V.mul_mem ha2 hb2
  one_mem' := ⟨C.one_mem, by rw [one_mul]; exact V.one_mem⟩
  inv_mem' := by
    intro a ha
    obtain ⟨haC, ha2⟩ := ha
    refine ⟨C.inv_mem haC, ?_⟩
    have h1 : a⁻¹ * a⁻¹ = (a * a)⁻¹ := by group
    rw [h1]
    exact V.inv_mem ha2

/-- Every element of `V` lies in the second level. -/
lemma V_le_level2 (hC : C = Subgroup.centralizer ((V : Set G)))
    (hCab : ∀ x ∈ C, ∀ y ∈ C, x * y = y * x)
    (hexp : ∀ x ∈ V, x * x = 1) : V ≤ level2 V C hC hCab hexp := by
  intro x hx
  refine ⟨V_le_C V C hC hexp hx, ?_⟩
  rw [hexp x hx]
  exact V.one_mem

/-- An element of `C` lies in the second level exactly when its square lies in `V`. -/
lemma mem_level2_iff (hC : C = Subgroup.centralizer ((V : Set G)))
    (hCab : ∀ x ∈ C, ∀ y ∈ C, x * y = y * x)
    (hexp : ∀ x ∈ V, x * x = 1) {x : G} :
    x ∈ level2 V C hC hCab hexp ↔ x ∈ C ∧ x * x ∈ V := Iff.rfl

end Level2

end Work.Hering.HardCore
