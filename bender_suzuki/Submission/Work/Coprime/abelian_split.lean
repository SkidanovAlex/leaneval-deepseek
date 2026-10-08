/-
Coprime action of a finite group `A` on a finite abelian group `G`: the fixed points
`C_G(A)` and the commutator `[G,A]` are complementary subgroups.

The proof uses the norm (trace) `N(x) = ∏_{a ∈ A} a • x`:
* `N` is multiplicative and takes values in `C_G(A)`;
* `N(x) = x ^ |A|` for `x ∈ C_G(A)`, so `x ↦ N(x) ^ m` (where `|A| · m ≡ 1` mod `|G|`)
  is a projection onto `C_G(A)`;
* `N(x) ≡ x ^ |A|` modulo `[G,A]`, whence `x · (N(x)^m)⁻¹ ∈ [G,A]`.

Since the coprimality hypothesis gives an exponent `m` with `|A| * m = |G| * t + 1`,
`e x := N(x) ^ m` satisfies `e x = x` on `C_G(A)`, `e x = 1` on `[G,A]`, `e` is a monoid
homomorphism, and `g = e g * (g * (e g)⁻¹)` is the required unique decomposition.
-/
import Mathlib
import Submission.Work.Coprime.Defs
import Submission.Work.Coprime.Basic

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

set_option linter.unusedVariables false
set_option linter.unusedSectionVars false
set_option linter.style.haveILetI false

open scoped Pointwise
open scoped IsMulCommutative

namespace Work.Coprime

section Norm

variable {G : Type*} [Group G] [Fintype G] [IsMulCommutative G]
variable {A : Type*} [Group A] [Fintype A] [MulDistribMulAction A G]

/-- The norm (trace) of `x` under the action of `A`: `∏ a, a • x`. -/
private def Norm (A : Type*) [Group A] [Fintype A] [MulDistribMulAction A G] (x : G) : G :=
  ∏ a : A, a • x

/-- The norm is fixed by the action of `A`. -/
@[simp]
private lemma smul_Norm (a : A) (x : G) : a • Norm A x = Norm A x := by
  rw [Norm, Finset.smul_prod']
  simp only [smul_smul]
  exact Equiv.prod_comp (Equiv.mulLeft a) (fun c : A => c • x)

private lemma Norm_mul (x y : G) : Norm A (x * y) = Norm A x * Norm A y := by
  simp only [Norm, smul_mul']
  rw [Finset.prod_mul_distrib]

private lemma Norm_smul (a : A) (x : G) : Norm A (a • x) = Norm A x := by
  simp only [Norm, smul_smul]
  exact Equiv.prod_comp (Equiv.mulRight a) (fun c : A => c • x)

private lemma Norm_mem_fixedPoints (x : G) : Norm A x ∈ FT.fixedPoints A G := by
  rw [FT.mem_fixedPoints]
  exact fun a => smul_Norm a x

private lemma Norm_eq_pow_mul (x : G) :
    Norm A x = x ^ Fintype.card A * ∏ a : A, x⁻¹ * (a • x) := by
  have hx : x ^ Fintype.card A = ∏ _a : A, x := by
    rw [Finset.prod_const, Finset.card_univ]
  rw [Norm, hx, ← Finset.prod_mul_distrib]
  apply Finset.prod_congr rfl
  intro a _
  group

/-- `N(x) ≡ x ^ |A|` modulo `[G,A]`. -/
private lemma inv_pow_mul_Norm_mem (x : G) :
    (x ^ Fintype.card A)⁻¹ * Norm A x ∈ FT.commutator A (⊤ : Subgroup G) := by
  rw [Norm_eq_pow_mul (A := A) x, ← mul_assoc, inv_mul_cancel, one_mul]
  apply Subgroup.prod_mem
  intro a _
  exact FT.le_commutator a (Subgroup.mem_top x)

end Norm

theorem abelian_split (A : Type*) {G : Type*} [Group A] [Group G] [Finite A] [Finite G]
    [MulDistribMulAction A G] [IsMulCommutative G] (hcop : (Nat.card A).Coprime (Nat.card G)) :
    (FT.fixedPoints A G).IsComplement' (FT.commutator A (⊤ : Subgroup G)) := by
  classical
  letI : Fintype A := Fintype.ofFinite A
  letI : Fintype G := Fintype.ofFinite G
  haveI : Nonempty A := ⟨1⟩
  haveI : Nonempty G := ⟨1⟩
  -- coprimality in terms of the chosen `Fintype` instances
  have hcop' : (Fintype.card A).Coprime (Fintype.card G) := by
    simpa [Nat.card_eq_fintype_card] using hcop
  -- an exponent `m` inverting `|A|` modulo `|G|`
  have hunit : IsUnit ((Fintype.card A : ℕ) : ZMod (Fintype.card G)) := by
    rw [ZMod.isUnit_iff_coprime]
    exact hcop'
  obtain ⟨u, hu⟩ := hunit
  haveI : NeZero (Fintype.card G) := ⟨Fintype.card_ne_zero⟩
  obtain ⟨m : ℕ, hm_cast, hm_pos⟩ : ∃ m : ℕ,
      ((m : ℕ) : ZMod (Fintype.card G)) =
        ((u⁻¹ : (ZMod (Fintype.card G))ˣ) : ZMod (Fintype.card G)) ∧ 1 ≤ m := by
    refine ⟨ZMod.val ((u⁻¹ : (ZMod (Fintype.card G))ˣ) : ZMod (Fintype.card G))
      + Fintype.card G, ?_, ?_⟩
    · rw [Nat.cast_add, ZMod.natCast_zmod_val, ZMod.natCast_self, add_zero]
    · have h1 : 1 ≤ Fintype.card G := Fintype.card_pos
      omega
  have hnm : Fintype.card A * m ≡ 1 [MOD Fintype.card G] := by
    rw [← ZMod.natCast_eq_natCast_iff, Nat.cast_mul, ← hu, hm_cast, ← Units.val_mul,
      mul_inv_cancel]
    simp
  have hpos : 1 ≤ Fintype.card A * m := by
    have := Nat.mul_pos (Fintype.card_pos (α := A)) (by omega : 0 < m)
    omega
  obtain ⟨t, ht⟩ := (Nat.modEq_iff_dvd' hpos).mp hnm.symm
  have hmain : Fintype.card A * m = Fintype.card G * t + 1 :=
    (Nat.sub_eq_iff_eq_add hpos).mp ht
  -- `x ^ (|A| * m) = x` for all `x`
  have hpow : ∀ x : G, x ^ (Fintype.card A * m) = x := by
    intro x
    rw [hmain, pow_add, pow_mul, pow_card_eq_one]
    simp
  -- the projection `e`
  let efun : G → G := fun x => (Norm A x) ^ m
  have efun_one : efun 1 = 1 := by
    show (Norm A 1) ^ m = 1
    simp [Norm]
  have efun_mul : ∀ x y : G, efun (x * y) = efun x * efun y := by
    intro x y
    show (Norm A (x * y)) ^ m = (Norm A x) ^ m * (Norm A y) ^ m
    rw [Norm_mul, mul_pow]
  let e : G →* G := MonoidHom.mk' efun efun_mul
  have e_apply : ∀ x : G, e x = (Norm A x) ^ m := fun x => rfl
  have e_mem : ∀ x : G, e x ∈ FT.fixedPoints A G := fun x =>
    Subgroup.pow_mem (FT.fixedPoints A G) (Norm_mem_fixedPoints (A := A) x) m
  have e_fixed : ∀ c : G, c ∈ FT.fixedPoints A G → e c = c := by
    intro c hc
    have hNorm : Norm A c = c ^ Fintype.card A := by
      rw [Norm]
      have hcc : ∀ a : A, a • c = c := fun a => hc a
      simp only [hcc]
      rw [Finset.prod_const, Finset.card_univ]
    show (Norm A c) ^ m = c
    rw [hNorm, ← pow_mul, hpow c]
  have e_ker : ∀ d : G, d ∈ FT.commutator A (⊤ : Subgroup G) → e d = 1 := by
    have hgen : ∀ (a : A) (x : G), e (x⁻¹ * (a • x)) = 1 := by
      intro a x
      have h1 : e (a • x) = e x := by
        show (Norm A (a • x)) ^ m = (Norm A x) ^ m
        rw [Norm_smul]
      rw [map_mul, map_inv, h1, inv_mul_cancel]
    have hle : FT.commutator A (⊤ : Subgroup G) ≤ e.ker := by
      refine FT.commutator_le ?_
      intro a x _
      rw [MonoidHom.mem_ker]
      exact hgen a x
    intro d hd
    exact MonoidHom.mem_ker.mp (hle hd)
  -- `x * (e x)⁻¹ ∈ [G,A]`
  have e_d : ∀ x : G, x * (e x)⁻¹ ∈ FT.commutator A (⊤ : Subgroup G) := by
    intro x
    have hk : (x ^ Fintype.card A)⁻¹ * Norm A x ∈ FT.commutator A (⊤ : Subgroup G) :=
      inv_pow_mul_Norm_mem x
    have hx : e x = x * ((x ^ Fintype.card A)⁻¹ * Norm A x) ^ m := by
      have hNk : Norm A x = x ^ Fintype.card A * ((x ^ Fintype.card A)⁻¹ * Norm A x) :=
        (mul_inv_cancel_left _ _).symm
      show (Norm A x) ^ m = x * ((x ^ Fintype.card A)⁻¹ * Norm A x) ^ m
      conv_lhs => rw [hNk]
      rw [mul_pow, ← pow_mul, hpow x]
    have hx2 : x * (e x)⁻¹ = (x⁻¹ * e x)⁻¹ := by
      rw [mul_inv, inv_inv]
    have hx3 : x⁻¹ * e x = ((x ^ Fintype.card A)⁻¹ * Norm A x) ^ m := by
      rw [hx, inv_mul_cancel_left]
    rw [hx2, hx3]
    exact Subgroup.inv_mem _ (Subgroup.pow_mem _ hk m)
  -- assemble the complement
  rw [Subgroup.isComplement'_def, Subgroup.isComplement_iff_existsUnique]
  intro g
  refine ⟨⟨⟨e g, e_mem g⟩, ⟨g * (e g)⁻¹, e_d g⟩⟩, ?_, ?_⟩
  · show e g * (g * (e g)⁻¹) = g
    rw [mul_comm g (e g)⁻¹, mul_inv_cancel_left]
  · rintro ⟨⟨c, hc⟩, ⟨d, hd⟩⟩ hcd
    change c * d = g at hcd
    have hc_eq : c = e g := by
      have h1 : e (c * d) = e g := by rw [hcd]
      rw [map_mul, e_fixed c hc, e_ker d hd, mul_one] at h1
      exact h1
    have hd_eq : d = g * (e g)⁻¹ := by
      have h3 : d = c⁻¹ * g := by
        rw [← inv_mul_cancel_left c d, hcd]
      rw [h3, hc_eq, mul_comm g (e g)⁻¹]
    exact Prod.ext (Subtype.ext hc_eq) (Subtype.ext hd_eq)

end Work.Coprime
