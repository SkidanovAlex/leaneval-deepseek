import Mathlib
import Submission.Work.BrauerSuzuki.Quaternion.character_setup
import Submission.Work.BrauerSuzuki.Quaternion.signHom_index_two
import Submission.Work.Induction.indFun_apply_eq_zero

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

/-!
# The characters of a generalized quaternion group: the values

Companion of `Work.BrauerSuzuki.Quaternion.character_setup`.  Let `P = ⟨τ, ρ⟩` be a
generalized quaternion group in Dade's normal form, `H = ⟨τ⟩` its cyclic subgroup of index
two, `λ` the linear character of `H` with `λ (τ ^ i) = I ^ i`, and `th = Ind_H^P λ`.

* `signHom d`/`signFun d` is the non-trivial linear character of `P/H` (`= 1` on `H`, `= -1`
  off `H`), an irreducible character of `P`;
* `indFun_lamFun_apply_mem`: `th x = λ x + λ x⁻¹` for `x ∈ H`
  (the two cosets of `H` contribute `λ x` and `λ x⁻¹`);
* `indFun_lamFun_apply_notMem`: `th x = 0` for `x ∉ H`;
* `indFun_lamFun_mem_Irr`: `th` is an irreducible character of `P`;
* `indFun_lamFun_tau_zpow`: `th (τ ^ i) = I ^ i + I ^ (-i)`.
-/

noncomputable section

open Classical

namespace Work.BrauerSuzuki.Quaternion

variable {P : Type*} [Group P] [Fintype P]

/-! ## The non-trivial linear character of `P / ⟨τ⟩` -/

/-- The non-trivial linear character of `P` with kernel `⟨τ⟩`. -/
def signFun (d : GenQuaternionData P) : P → ℂ :=
  fun x => (signHom (tauSub d) (tauSub_index d) x : ℂ)

/-- The non-trivial linear character of `P / ⟨τ⟩` is an irreducible character of `P`. -/
theorem signFun_mem_Irr (d : GenQuaternionData P) : signFun d ∈ CharCore.Irr P := by
  obtain ⟨χ, hχ, hval⟩ := CharCore.exists_irr_of_monoidHom (signHom (tauSub d) (tauSub_index d))
  rw [show signFun d = χ from funext fun x => (hval x).symm]
  exact hχ

@[simp] theorem signFun_mem (d : GenQuaternionData P) {x : P} (hx : x ∈ tauSub d) :
    signFun d x = 1 := by
  show ((signHom (tauSub d) (tauSub_index d) x : ℂˣ) : ℂ) = 1
  rw [signHom_apply_of_mem (tauSub_index d) hx, Units.val_one]

theorem signFun_notMem (d : GenQuaternionData P) {x : P} (hx : x ∉ tauSub d) :
    signFun d x = -1 := by
  show ((signHom (tauSub d) (tauSub_index d) x : ℂˣ) : ℂ) = -1
  rw [signHom_apply_of_notMem (tauSub_index d) hx]
  simp

/-! ## The coset decomposition `P = ⟨τ⟩ ⊔ ρ ⟨τ⟩` -/

/-- `(false, h) ↦ h`, `(true, h) ↦ ρ * h`: a bijection `Bool × ⟨τ⟩ → P`. -/
def coverFun (d : GenQuaternionData P) : Bool × ↥(tauSub d) → P
  | (false, h) => (h : P)
  | (true, h) => d.rho * (h : P)

theorem coverFun_injective (d : GenQuaternionData P) : Function.Injective (coverFun d) := by
  rintro ⟨b1, h1⟩ ⟨b2, h2⟩ heq
  cases b1 <;> cases b2
  · exact congrArg (Prod.mk false) (Subtype.ext heq)
  · exfalso
    have heq' : (h1 : P) = d.rho * (h2 : P) := heq
    have hρ : d.rho = (h1 : P) * (h2 : P)⁻¹ := by rw [heq']; group
    refine rho_notMem_tauSub d ?_
    rw [hρ]
    exact Subgroup.mul_mem _ h1.2 (Subgroup.inv_mem _ h2.2)
  · exfalso
    have heq' : d.rho * (h1 : P) = (h2 : P) := heq
    have hρ : d.rho = (h2 : P) * (h1 : P)⁻¹ := by rw [← heq']; group
    refine rho_notMem_tauSub d ?_
    rw [hρ]
    exact Subgroup.mul_mem _ h2.2 (Subgroup.inv_mem _ h1.2)
  · have heq' : d.rho * (h1 : P) = d.rho * (h2 : P) := heq
    exact congrArg (Prod.mk true) (Subtype.ext (mul_left_cancel heq'))

theorem coverFun_surjective (d : GenQuaternionData P) : Function.Surjective (coverFun d) := by
  intro g
  rcases coset_cover d g with hg | ⟨h, hh, hgh⟩
  · exact ⟨(false, ⟨g, hg⟩), rfl⟩
  · exact ⟨(true, ⟨h, hh⟩), hgh.symm⟩

/-- The bijection `Bool × ⟨τ⟩ ≃ P` given by the two cosets of `⟨τ⟩`. -/
noncomputable def coverBij (d : GenQuaternionData P) : Bool × ↥(tauSub d) ≃ P :=
  Equiv.ofBijective (coverFun d) ⟨coverFun_injective d, coverFun_surjective d⟩

@[simp] theorem coverBij_false (d : GenQuaternionData P) (h : ↥(tauSub d)) :
    coverBij d (false, h) = (h : P) := rfl

@[simp] theorem coverBij_true (d : GenQuaternionData P) (h : ↥(tauSub d)) :
    coverBij d (true, h) = d.rho * (h : P) := rfl

/-! ## The values of `Ind λ` -/

/-- The summand of the induced character `Ind_{⟨τ⟩}^P λ` at `y`: since `⟨τ⟩` is normal,
`y * x * y⁻¹ ∈ ⟨τ⟩` and the summand is `λ (y * x * y⁻¹)`. -/
def indTerm (d : GenQuaternionData P) (x : ↥(tauSub d)) (y : P) : ℂ :=
  lamFun d ⟨y * (x : P) * y⁻¹, (tauSub_normal d).conj_mem (x : P) x.2 y⟩

theorem indTerm_conj (d : GenQuaternionData P) (x : ↥(tauSub d)) :
    ∀ h : ↥(tauSub d), indTerm d x (coverBij d (false, h)) = lamFun d x := by
  intro h
  show lamFun d ⟨(h : P) * (x : P) * (h : P)⁻¹,
    (tauSub_normal d).conj_mem (x : P) x.2 (coverBij d (false, h))⟩ = lamFun d x
  exact lamFun_conj d h x

theorem indTerm_conj_rho (d : GenQuaternionData P) (x : ↥(tauSub d)) :
    ∀ h : ↥(tauSub d), indTerm d x (coverBij d (true, h)) = lamFun d x⁻¹ := by
  intro h
  have key : (⟨(d.rho * (h : P)) * (x : P) * (d.rho * (h : P))⁻¹,
        (tauSub_normal d).conj_mem (x : P) x.2 (coverBij d (true, h))⟩ : ↥(tauSub d))
      = rhoConj d (h * x * h⁻¹) := by
    apply Subtype.ext
    show (d.rho * (h : P)) * (x : P) * (d.rho * (h : P))⁻¹
        = d.rho * ((h : P) * (x : P) * (h : P)⁻¹) * d.rho⁻¹
    group
  show lamFun d ⟨(d.rho * (h : P)) * (x : P) * (d.rho * (h : P))⁻¹, _⟩ = lamFun d x⁻¹
  rw [key, lamFun_rhoConj]
  have h2 : ((h * x * h⁻¹)⁻¹ : ↥(tauSub d)) = h * x⁻¹ * h⁻¹ := by group
  rw [h2]
  exact lamFun_conj d h x⁻¹

/-- **The value of `Ind_{⟨τ⟩}^P λ` at an element of `⟨τ⟩`**: the two cosets of `⟨τ⟩`
contribute `λ x` and `λ x⁻¹`. -/
theorem indFun_lamFun_apply_mem (d : GenQuaternionData P) (x : ↥(tauSub d)) :
    Work.Induction.indFun (tauSub d) (lamFun d) (x : P) = lamFun d x + lamFun d x⁻¹ := by
  classical
  have hcard : ((Nat.card ↥(tauSub d) : ℕ) : ℂ) ≠ 0 := by
    rw [Nat.card_eq_fintype_card, Nat.cast_ne_zero]
    exact Fintype.card_ne_zero
  have hstep : Work.Induction.indFun (tauSub d) (lamFun d) (x : P)
      = (Nat.card ↥(tauSub d) : ℂ)⁻¹ * ∑ y : P, indTerm d x y := by
    rw [Work.Induction.indFun_apply_def]
    congr 1
    exact Finset.sum_congr rfl
      fun y _ => dif_pos ((tauSub_normal d).conj_mem (x : P) x.2 y)
  have hsum : ∑ y : P, indTerm d x y
      = (Nat.card ↥(tauSub d) : ℂ) * (lamFun d x + lamFun d x⁻¹) := by
    rw [← Equiv.sum_comp (coverBij d) (fun y => indTerm d x y)]
    rw [Fintype.sum_prod_type, Fintype.sum_bool]
    have hs1 : (∑ h : ↥(tauSub d), indTerm d x (coverBij d (false, h)))
        = (Nat.card ↥(tauSub d) : ℂ) * lamFun d x := by
      rw [Finset.sum_congr rfl (fun h _ => indTerm_conj d x h), Finset.sum_const,
        Finset.card_univ, nsmul_eq_mul, ← Nat.card_eq_fintype_card]
    have hs2 : (∑ h : ↥(tauSub d), indTerm d x (coverBij d (true, h)))
        = (Nat.card ↥(tauSub d) : ℂ) * lamFun d x⁻¹ := by
      rw [Finset.sum_congr rfl (fun h _ => indTerm_conj_rho d x h), Finset.sum_const,
        Finset.card_univ, nsmul_eq_mul, ← Nat.card_eq_fintype_card]
    rw [hs1, hs2]
    ring
  rw [hstep, hsum, ← mul_assoc, inv_mul_cancel₀ hcard, one_mul]

/-- **The value of `Ind_{⟨τ⟩}^P λ` off `⟨τ⟩`**: it vanishes. -/
theorem indFun_lamFun_apply_notMem (d : GenQuaternionData P) {x : P} (hx : x ∉ tauSub d) :
    Work.Induction.indFun (tauSub d) (lamFun d) x = 0 := by
  refine Work.Induction.indFun_apply_eq_zero (tauSub d) (lamFun d) x fun y hy => hx ?_
  have h := (tauSub_normal d).conj_mem (y * x * y⁻¹) hy y⁻¹
  rw [show y⁻¹ * (y * x * y⁻¹) * y⁻¹⁻¹ = x from by group] at h
  exact h

/-- **`th = Ind_{⟨τ⟩}^P λ` is an irreducible character of `P`.** -/
theorem indFun_lamFun_mem_Irr (d : GenQuaternionData P) :
    Work.Induction.indFun (tauSub d) (lamFun d) ∈ CharCore.Irr P := by
  have hV : CharCore.IsVChar (Work.Induction.indFun (tauSub d) (lamFun d)) :=
    Work.Induction.isVChar_indFun (CharCore.IsVChar.of_mem_Irr (lamFun_mem_Irr d))
  obtain ⟨χ, hχ, hcase⟩ := CharCore.vchar_norm_one hV (cfInner_indFun_lamFun_self d)
  rcases hcase with h | h
  · rwa [h]
  · exfalso
    have h1 : Work.Induction.indFun (tauSub d) (lamFun d) 1 = -χ 1 := by rw [h]; rfl
    rw [indFun_lamFun_one, CharCore.irrDeg_spec hχ] at h1
    have h2 : (2 : ℝ) = -(CharCore.irrDeg χ : ℝ) := by
      apply Complex.ofReal_injective
      push_cast
      exact h1
    have h3 : (0 : ℝ) < (CharCore.irrDeg χ : ℝ) := CharCore.irrDeg_pos' hχ
    linarith

/-- **The values of `th` at powers of `τ`**: `th (τ ^ i) = I ^ i + I ^ (-i)`. -/
theorem indFun_lamFun_tau_zpow (d : GenQuaternionData P) (i : ℤ) :
    Work.Induction.indFun (tauSub d) (lamFun d) (d.tau ^ i)
      = Complex.I ^ i + Complex.I ^ (-i) := by
  have h := indFun_lamFun_apply_mem d
    ⟨d.tau ^ i, Subgroup.zpow_mem (Subgroup.zpowers d.tau) (Subgroup.mem_zpowers d.tau) i⟩
  rw [h, lamFun_inv, lamFun_tau_zpow, ← zpow_neg]

/-- The subgroup `⟨τ ^ 2⟩` is contained in `⟨τ⟩`. -/
theorem zpowers_two_le (d : GenQuaternionData P) :
    Subgroup.zpowers (d.tau ^ 2) ≤ tauSub d :=
  Subgroup.zpowers_le.mpr
    (Subgroup.pow_mem (Subgroup.zpowers d.tau) (Subgroup.mem_zpowers d.tau) 2)

/-- The subgroup `⟨τ ^ 4⟩` is contained in `⟨τ⟩`. -/
theorem zpowers_four_le (d : GenQuaternionData P) :
    Subgroup.zpowers (d.tau ^ 4) ≤ tauSub d :=
  Subgroup.zpowers_le.mpr
    (Subgroup.pow_mem (Subgroup.zpowers d.tau) (Subgroup.mem_zpowers d.tau) 4)

end Work.BrauerSuzuki.Quaternion
