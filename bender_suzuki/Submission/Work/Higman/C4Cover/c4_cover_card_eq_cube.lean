/-
# The `C₄` cover has order exactly `q³`

Higman, *Suzuki 2-groups*, Illinois J. Math. 7 (1963), 79--96.

In the `C₄` setting with a minimal `ξ`-invariant normal cover `C > A` and `⁅C,C⁆ = A²`:

* `c4_cover_card_le` gives `|C| ≤ |A| · |Ω₁(P)| = q³`;
* `Work.Higman.H8.xi_invariant_card_sub_one_dvd` (sorry-free) gives `(q − 1) ∣ |C| − 1`;
* with `X := |C : A|` (so `|C| = X · |A| = X · q²`) this gives `(q − 1) ∣ X − 1`, and as `X` is a
  power of two, `X = 2^k` with `2^n − 1 ∣ 2^k − 1`, so `n ∣ k`, `X ≥ q`, and `|C| ≥ q³`.

Hence `|C| = q³`.  Since `C ≠ ⊤` (else `⁅C,C⁆ = ⁅⊤,⊤⁆ = A ≠ A²`), this also yields `|P| ≥ 2q³`
(`c4_two_mul_card_le`), so the `C₄` shape is incompatible with the bound `|P| ≤ |Ω₁(P)|³`.
-/
import Mathlib
import Submission.Work.Higman.C4Cover.arith
import Submission.Work.Higman.C4Cover.c4_cover_card_le_final
import Submission.Work.Higman.H8.c4_sq_a2_orbit

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

namespace Work.Higman.C4Cover

variable {P : Type} [Group P] [Finite P]

/-- **The `C₄` cover has order `q³`.** -/
theorem c4_cover_card_eq_cube (h : Work.Higman.IsSuzuki2Grp P) {A C : Subgroup P}
    (hAab : ∀ x ∈ A, ∀ y ∈ A, x * y = y * x)
    (hNA : Work.Higman.omega1 P ≤ A)
    (hGs : ⁅(⊤ : Subgroup P), ⊤⁆ = A)
    (hsq : ∀ x : P, x ^ 2 ∈ A)
    (htop : Work.Higman.powSub A 2 = Work.Higman.omega1 P)
    (hcard : Nat.card ↥A = (Nat.card ↥(Work.Higman.omega1 P)) ^ 2)
    (hCn : C.Normal) (hCinv : C.map (h.xi : MulAut P).toMonoidHom = C)
    (hAC : A ≤ C) (hCA : A ≠ C)
    (hcover : ∀ E : Subgroup P, E.Normal → E.map (h.xi : MulAut P).toMonoidHom = E →
      A ≤ E → E ≤ C → E = A ∨ E = C)
    (hCd : ⁅C, C⁆ = Work.Higman.powSub A 2) :
    Nat.card ↥C = (Nat.card ↥(Work.Higman.omega1 P)) ^ 3 := by
  classical
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨n, hn⟩ := h.exists_card_omega1_eq_two_pow
  have hnpos : 0 < n := by
    rcases Nat.eq_zero_or_pos n with h0 | hpos
    · exfalso
      rw [h0, pow_zero] at hn
      have := h.omega1_card_ge_four
      omega
    · exact hpos
  have hle := c4_cover_card_le h hAab hNA hGs hsq htop hcard hCn hCinv hAC hCA hcover hCd
  have hAle : Nat.card ↥A = 2 ^ (2 * n) := by
    rw [hcard, hn, show (2 ^ n) ^ 2 = 2 ^ (n * 2) from by rw [pow_mul], Nat.mul_comm]
  obtain ⟨N, hN⟩ := (h.isPGroup.to_subgroup C).exists_card_eq
  have hsubcard : Nat.card ↥(A.subgroupOf C) = Nat.card ↥A :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe hAC).toEquiv
  have hXeq : (A.subgroupOf C).index * Nat.card ↥A = Nat.card ↥C := by
    rw [← hsubcard]
    exact Subgroup.index_mul_card (A.subgroupOf C)
  have hXdiv : (A.subgroupOf C).index ∣ 2 ^ N :=
    ⟨2 ^ (2 * n), by rw [← hAle, ← hN]; exact hXeq.symm⟩
  obtain ⟨k, -, hk⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp hXdiv
  -- positivity bookkeeping
  have hCne0 : Nat.card ↥C ≠ 0 :=
    Nat.card_ne_zero.mpr ⟨⟨(1 : ↥C)⟩, inferInstance⟩
  have hCpos : 1 ≤ Nat.card ↥C := Nat.one_le_iff_ne_zero.mpr hCne0
  have hXpos : 1 ≤ (A.subgroupOf C).index := by
    rcases Nat.eq_zero_or_pos (A.subgroupOf C).index with h0 | hpos
    · exfalso
      rw [h0, zero_mul] at hXeq
      exact hCne0 hXeq.symm
    · exact hpos
  -- `(q - 1) ∣ X - 1`
  have ha1 : Nat.card ↥A ≡ 1 [MOD Nat.card ↥(Work.Higman.omega1 P) - 1] := by
    rw [hcard]
    have hq1le : 1 ≤ Nat.card ↥(Work.Higman.omega1 P) := by
      have := h.omega1_card_ge_four
      omega
    have hq1 : Nat.card ↥(Work.Higman.omega1 P) ≡ 1
        [MOD Nat.card ↥(Work.Higman.omega1 P) - 1] :=
      (Nat.modEq_of_dvd' (n := Nat.card ↥(Work.Higman.omega1 P) - 1) (a := 1)
        (b := Nat.card ↥(Work.Higman.omega1 P)) hq1le
        (by simpa using dvd_refl (Nat.card ↥(Work.Higman.omega1 P) - 1))).symm
    simpa using hq1.pow 2
  have hdvd := Work.Higman.H8.xi_invariant_card_sub_one_dvd h hCinv
  have hXdvd : Nat.card ↥(Work.Higman.omega1 P) - 1 ∣ (A.subgroupOf C).index - 1 :=
    index_sub_one_dvd hXeq.symm ha1 hCpos hXpos hdvd
  -- `2^n - 1 ∣ 2^k - 1`, so `n ∣ k` and `X ≥ q`
  have hkdiv : 2 ^ n - 1 ∣ 2 ^ k - 1 := by
    have h1 := hXdvd
    rw [hn, hk] at h1
    exact h1
  have hnk : n ∣ k := two_pow_sub_one_dvd_imp hnpos hkdiv
  have hkge : n ≤ k := by
    rcases Nat.eq_zero_or_pos k with h0 | hpos
    · exfalso
      have h1 : (A.subgroupOf C).index = 1 := by rw [hk, h0]; norm_num
      have h2 : Nat.card ↥C = Nat.card ↥A := by rw [← hXeq, h1, one_mul]
      exact hCA (Subgroup.eq_of_le_of_card_ge hAC (le_of_eq h2))
    · exact Nat.le_of_dvd hpos hnk
  have hXq : Nat.card ↥(Work.Higman.omega1 P) ≤ (A.subgroupOf C).index := by
    have hkn : 2 ^ n ≤ 2 ^ k := Nat.pow_le_pow_right (by norm_num) hkge
    rw [hn, hk]
    exact hkn
  refine le_antisymm ?_ ?_
  · calc Nat.card ↥C ≤ Nat.card ↥(Work.Higman.omega1 P) * Nat.card ↥A := hle
      _ = (Nat.card ↥(Work.Higman.omega1 P)) ^ 3 := by rw [hcard]; ring
  · have h1 : (Nat.card ↥(Work.Higman.omega1 P)) ^ 3
        = Nat.card ↥(Work.Higman.omega1 P) * Nat.card ↥A := by rw [hcard]; ring
    rw [h1, ← hXeq]
    exact Nat.mul_le_mul_right _ hXq

/-- **The `C₄` cover is a proper subgroup of order `q³`**, so `|P| ≥ 2q³`. -/
theorem c4_two_mul_card_le (h : Work.Higman.IsSuzuki2Grp P) {A C : Subgroup P}
    (hAab : ∀ x ∈ A, ∀ y ∈ A, x * y = y * x)
    (hNA : Work.Higman.omega1 P ≤ A)
    (hGs : ⁅(⊤ : Subgroup P), ⊤⁆ = A)
    (hsq : ∀ x : P, x ^ 2 ∈ A)
    (htop : Work.Higman.powSub A 2 = Work.Higman.omega1 P)
    (hcard : Nat.card ↥A = (Nat.card ↥(Work.Higman.omega1 P)) ^ 2)
    (hCn : C.Normal) (hCinv : C.map (h.xi : MulAut P).toMonoidHom = C)
    (hAC : A ≤ C) (hCA : A ≠ C)
    (hcover : ∀ E : Subgroup P, E.Normal → E.map (h.xi : MulAut P).toMonoidHom = E →
      A ≤ E → E ≤ C → E = A ∨ E = C)
    (hCd : ⁅C, C⁆ = Work.Higman.powSub A 2) :
    2 * (Nat.card ↥(Work.Higman.omega1 P)) ^ 3 ≤ Nat.card P := by
  have hcube := c4_cover_card_eq_cube h hAab hNA hGs hsq htop hcard hCn hCinv hAC hCA hcover hCd
  -- `C ≠ ⊤`
  have hCne : C ≠ ⊤ := by
    intro htop'
    have h1 : A = Work.Higman.powSub A 2 := by rw [← hCd, htop', hGs]
    have h2 : Nat.card ↥A = Nat.card ↥(Work.Higman.powSub A 2) :=
      congrArg (fun S : Subgroup P => Nat.card ↥S) h1
    rw [hcard, htop] at h2
    have h4 := h.omega1_card_ge_four
    nlinarith [h2, h4]
  have hPne0 : Nat.card P ≠ 0 := Nat.card_ne_zero.mpr ⟨⟨(1 : P)⟩, inferInstance⟩
  have hidx0 : C.index ≠ 0 := by
    intro h0
    have h1 := Subgroup.index_mul_card C
    rw [h0, zero_mul] at h1
    exact hPne0 h1.symm
  have hidx1 : C.index ≠ 1 := by
    intro h1
    have h2 : Nat.card ↥C = Nat.card P := by
      have h3 := Subgroup.index_mul_card C
      rw [h1, one_mul] at h3
      exact h3
    exact hCne (Subgroup.eq_top_of_card_eq C h2)
  have hidx2 : 2 ≤ C.index := by omega
  have h1 : C.index * Nat.card ↥C = Nat.card P := Subgroup.index_mul_card C
  calc 2 * (Nat.card ↥(Work.Higman.omega1 P)) ^ 3 = 2 * Nat.card ↥C := by rw [hcube]
    _ ≤ C.index * Nat.card ↥C := Nat.mul_le_mul_right _ hidx2
    _ = Nat.card P := h1

/-- **The `C₄` shape is incompatible with `|P| ≤ |Ω₁(P)|³`.**  Hence proving that upper bound for
Suzuki 2-groups (Higman's Theorem 1 / Lemma 13) closes the `C₄` exclusion. -/
theorem c4_false_of_card_le (h : Work.Higman.IsSuzuki2Grp P) {A C : Subgroup P}
    (hAab : ∀ x ∈ A, ∀ y ∈ A, x * y = y * x)
    (hNA : Work.Higman.omega1 P ≤ A)
    (hGs : ⁅(⊤ : Subgroup P), ⊤⁆ = A)
    (hsq : ∀ x : P, x ^ 2 ∈ A)
    (htop : Work.Higman.powSub A 2 = Work.Higman.omega1 P)
    (hcard : Nat.card ↥A = (Nat.card ↥(Work.Higman.omega1 P)) ^ 2)
    (hCn : C.Normal) (hCinv : C.map (h.xi : MulAut P).toMonoidHom = C)
    (hAC : A ≤ C) (hCA : A ≠ C)
    (hcover : ∀ E : Subgroup P, E.Normal → E.map (h.xi : MulAut P).toMonoidHom = E →
      A ≤ E → E ≤ C → E = A ∨ E = C)
    (hCd : ⁅C, C⁆ = Work.Higman.powSub A 2)
    (hcardle : Nat.card P ≤ (Nat.card ↥(Work.Higman.omega1 P)) ^ 3) :
    False := by
  have h2 := c4_two_mul_card_le h hAab hNA hGs hsq htop hcard hCn hCinv hAC hCA hcover hCd
  have h3 : 0 < (Nat.card ↥(Work.Higman.omega1 P)) ^ 3 := by
    have h4 := h.omega1_card_ge_four
    exact pow_pos (by omega) 3
  omega

end Work.Higman.C4Cover
