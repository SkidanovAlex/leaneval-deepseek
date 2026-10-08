import Mathlib
import Submission.Work.Higman.typeB
import Submission.Work.Higman.BS.Defs
import Submission.Work.Higman.Defs

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

namespace Work.ThmF.ChV12

open scoped Classical

/-! ## Auxiliary lemmas for `orderOf_lam_eq` -/

variable {P : Type} [Group P]

/-- Iterating the intertwining relation `ψ (ξ x) = λ • ψ x`. -/
theorem psi_xi_pow_apply {F : Type} [Field F] {ξ : MulAut P} {ψ : P → F × F}
    {lam : Fˣ} (hlam : ∀ x, ψ (ξ x) = (lam : F) • ψ x) (k : ℕ) (x : P) :
    ψ ((ξ ^ k) x) = (lam : F) ^ k • ψ x := by
  induction k with
  | zero => simp
  | succ k ih =>
      rw [pow_succ', MulAut.mul_apply, hlam, ih, smul_smul, ← pow_succ']

/-- **First direction.** If `λ ^ k = 1` then `ξ ^ k` acts trivially on `P ⧸ Z(P)`, hence
(by `Work.Higman.quotCenterAut_pow_eq_one_iff`) `ξ ^ k = 1`. -/
theorem lam_pow_eq_one_imp_xi_pow_eq_one_aux {P : Type} [Group P] [Finite P] (h : Work.Higman.IsSuzuki2Grp P)
    {ξ : MulAut P} (hξ : Work.Higman.FpfXi ξ)
    {F : Type} [Field F] [Fintype F] {ψ : P → F × F}
    (hadd : ∀ x y, ψ (x * y) = ψ x + ψ y)
    (hker : ∀ x, ψ x = 0 ↔ x ∈ Subgroup.center P)
    {lam : Fˣ} (hlam : ∀ x, ψ (ξ x) = (lam : F) • ψ x) :
    ∀ k : ℕ, lam ^ k = 1 → ξ ^ k = 1 := by
  intro k hlk
  refine (Work.Higman.quotCenterAut_pow_eq_one_iff h hξ k).mp ?_
  ext v
  obtain ⟨x, rfl⟩ := Work.Higman.centerProj_surjective v
  rw [Work.Higman.quotCenterAut_pow_mk, MulAut.one_apply]
  have hval : (lam : F) ^ k = 1 := by
    rw [← Units.val_pow_eq_pow_val, hlk, Units.val_one]
  have h1 : ψ ((ξ ^ k) x) = ψ x := by
    rw [psi_xi_pow_apply hlam k x, hval, one_smul]
  have h2 : ψ ((ξ ^ k) x * x⁻¹) = 0 := by
    have hh := hadd ((ξ ^ k) x * x⁻¹) x
    rw [inv_mul_cancel_right] at hh
    rw [h1] at hh
    exact add_eq_right.mp hh.symm
  have hmem : (ξ ^ k) x * x⁻¹ ∈ Subgroup.center P := (hker _).mp h2
  have hz : QuotientGroup.mk' (Subgroup.center P) ((ξ ^ k) x * x⁻¹) = 1 :=
    (QuotientGroup.eq_one_iff _).mpr hmem
  calc QuotientGroup.mk' (Subgroup.center P) ((ξ ^ k) x)
      = QuotientGroup.mk' (Subgroup.center P) (((ξ ^ k) x * x⁻¹) * x) := by
        rw [inv_mul_cancel_right]
    _ = QuotientGroup.mk' (Subgroup.center P) ((ξ ^ k) x * x⁻¹) *
          QuotientGroup.mk' (Subgroup.center P) x := map_mul _ _ _
    _ = 1 * QuotientGroup.mk' (Subgroup.center P) x := by rw [hz]
    _ = QuotientGroup.mk' (Subgroup.center P) x := one_mul _

/-- **Second direction.** If `ξ ^ k = 1`, then `ψ x = λ ^ k • ψ x` for every `x`; taking `x`
with `ψ x ≠ 0` (surjectivity) and looking at a non-zero coordinate of `ψ x` gives `λ ^ k = 1`. -/
theorem xi_pow_eq_one_imp_lam_pow_eq_one_aux {P : Type} [Group P]
    {F : Type} [Field F] {ψ : P → F × F}
    (hsurj : Function.Surjective ψ)
    {ξ : MulAut P} {lam : Fˣ} (hlam : ∀ x, ψ (ξ x) = (lam : F) • ψ x) :
    ∀ k : ℕ, ξ ^ k = 1 → lam ^ k = 1 := by
  intro k hk
  obtain ⟨x, hxmem⟩ : ∃ x : P, (ψ x).1 ≠ 0 ∨ (ψ x).2 ≠ 0 := by
    obtain ⟨y, hy⟩ := hsurj (1, 0)
    refine ⟨y, Or.inl ?_⟩
    rw [hy]
    exact one_ne_zero
  have hfix : (lam : F) ^ k • ψ x = ψ x := by
    have h := psi_xi_pow_apply hlam k x
    rw [hk, MulAut.one_apply] at h
    exact h.symm
  have hcoord : (lam : F) ^ k * (ψ x).1 = (ψ x).1 ∧
      (lam : F) ^ k * (ψ x).2 = (ψ x).2 := by
    constructor
    · have := congrArg Prod.fst hfix
      simpa [Prod.smul_def] using this
    · have := congrArg Prod.snd hfix
      simpa [Prod.smul_def] using this
  apply Units.ext
  rw [Units.val_pow_eq_pow_val, Units.val_one]
  rcases hxmem with hne | hne
  · exact mul_right_cancel₀ hne (by rw [one_mul]; exact hcoord.1)
  · exact mul_right_cancel₀ hne (by rw [one_mul]; exact hcoord.2)

/-- In a finite field, a unit of order `|F| - 1` generates the multiplicative group, so every
element of `F` is `0` or a natural power of it. -/
theorem finite_field_pow_of_orderOf_eq_card_sub_one_aux {F : Type} [Field F] [Fintype F]
    {lam : Fˣ} (h : orderOf lam = Nat.card F - 1) :
    ∀ c : F, c = 0 ∨ ∃ n : ℕ, c = (lam : F) ^ n := by
  intro c
  by_cases hc : c = 0
  · exact Or.inl hc
  · right
    have htop : Subgroup.zpowers lam = ⊤ := by
      refine (Subgroup.card_eq_iff_eq_top (Subgroup.zpowers lam)).mp ?_
      rw [Nat.card_zpowers, Nat.card_units F, h]
    have hmem : Units.mk0 c hc ∈ Subgroup.zpowers lam := by
      rw [htop]; exact Subgroup.mem_top _
    have hpow : Units.mk0 c hc ∈ Submonoid.powers lam :=
      mem_powers_iff_mem_zpowers.mpr hmem
    obtain ⟨n, hn⟩ := (Submonoid.mem_powers_iff (Units.mk0 c hc) lam).mp hpow
    exact ⟨n, by rw [← Units.val_pow_eq_pow_val, hn, Units.val_mk0]⟩

-- Let `P` be a Suzuki 2-group with `FpfXi ξ` (`|P| = |Z(P)|³`, `orderOf ξ = |Z(P)| - 1`), and
-- let `ψ : P → F × F` be additive, surjective, with kernel `Z(P)` and `|F| = |Z(P)|`, and
-- intertwining `ξ` with multiplication by `λ ∈ Fˣ`.  Then `orderOf λ = |F| - 1 = |Fˣ|`, so `λ`
-- is a primitive element of `F`: every element of `F` is `0` or a power of `λ`.
--
-- Proof.  `λ^k = 1` implies `ψ (ξ^k x) = ψ x` for all `x`, so `ξ^k` acts trivially on
-- `P ⧸ Z(P)` (as `ker ψ = Z(P)`), i.e. `quotCenterAut ξ ^ k = 1`
-- (`Work.Higman.quotCenterAut_pow_mk` plus surjectivity of the quotient projection); by
-- `Work.Higman.quotCenterAut_pow_eq_one_iff` (`Work/Higman/BS/Defs.lean`) `ξ^k = 1`, i.e.
-- `orderOf ξ ∣ k`.  Conversely `ξ^k = 1` gives `λ^k = 1` using the surjectivity of `ψ` (pick
-- `x` with `ψ x ≠ 0`).  Hence `orderOf λ = orderOf ξ = |Z(P)| - 1 = |F| - 1` (`FpfXi.order`,
-- `hcardF`).  For the second conjunct: `|Fˣ| = |F| - 1` (`Fintype.card_units`), so
-- `Nat.card ↥(Subgroup.zpowers lam) = orderOf lam = Nat.card Fˣ` (`Nat.card_zpowers`), whence
-- `Subgroup.card_eq_iff_eq_top` gives `Subgroup.zpowers lam = ⊤` and every non-zero `c : F` is a
-- natural power of `λ`.
theorem orderOf_lam_eq {P : Type} [Group P] [Finite P] (h : Work.Higman.IsSuzuki2Grp P)
    {ξ : MulAut P} (hξ : Work.Higman.FpfXi ξ)
    {F : Type} [Field F] [Fintype F] {ψ : P → F × F}
    (hadd : ∀ x y, ψ (x * y) = ψ x + ψ y)
    (hker : ∀ x, ψ x = 0 ↔ x ∈ Subgroup.center P)
    (hsurj : Function.Surjective ψ)
    (hcardF : Nat.card F = Nat.card ↥(Subgroup.center P))
    {lam : Fˣ} (hlam : ∀ x, ψ (ξ x) = (lam : F) • ψ x) :
    orderOf lam = Nat.card F - 1 ∧ ∀ c : F, c = 0 ∨ ∃ n : ℕ, c = (lam : F) ^ n := by
  have hD := lam_pow_eq_one_imp_xi_pow_eq_one_aux h hξ hadd hker hlam
  have hE := xi_pow_eq_one_imp_lam_pow_eq_one_aux hsurj hlam
  have hdvd1 : orderOf ξ ∣ orderOf lam := by
    rw [orderOf_dvd_iff_pow_eq_one]
    exact hD _ (pow_orderOf_eq_one lam)
  have hdvd2 : orderOf lam ∣ orderOf ξ := by
    rw [orderOf_dvd_iff_pow_eq_one]
    exact hE _ (pow_orderOf_eq_one ξ)
  have horder : orderOf lam = orderOf ξ := Nat.dvd_antisymm hdvd2 hdvd1
  have hfirst : orderOf lam = Nat.card F - 1 := by
    rw [horder, hξ.order, ← hcardF]
  exact ⟨hfirst, finite_field_pow_of_orderOf_eq_card_sub_one_aux hfirst⟩

end Work.ThmF.ChV12
