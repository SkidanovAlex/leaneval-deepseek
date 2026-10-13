import Mathlib
import Submission.Work.DSM2p.Basic
import Submission.Work.DSM2p.nilp_lem_subring
import Submission.Work.DSM2p.AALvaln
import Submission.Work.DSM2p.AALcopy_approx_lem
import Submission.Work.DSM2p.area_AAL_proved

namespace Work.DSM2p

open scoped Classical

universe u

/-! ## Bookkeeping lemmas for exponents

`nilp_lem_subring` produces *some* exponent `n` with `a ^ n ∈ ϖ · A`.  The target below asks for a
*single* positive exponent working for three membership conditions at once.  These lemmas move
between exponents: `AAL_N_mul_exp` multiplies a known exponent by a positive integer (the set of
exponents of membership in `ϖ·A` is closed under such products), and `AAL_N_pos_exp` upgrades an
exponent to a *positive* one — if `0` is the only exponent known then `1 ∈ ϖ·A`, so `ϖ` is a unit
of the `hgen`-ring `A[1/ϖ] = B`, hence `B = A`, and `1` is again an exponent. -/

/-- If `a^n ∈ ϖ·A` (witnessed by `x ∈ A` with `x·ϖ = a^n`) then so is `a^(n·k)` for every `k ≥ 1`:
`a^(n·k) = (x ϖ)^k = ϖ · (x^k ϖ^(k-1))` with `x^k ϖ^(k-1) ∈ A`. -/
theorem AAL_N_mul_exp {B : Type*} [CommRing B] (ϖ : B) (A : Subring B) (hϖA : ϖ ∈ A) (a : B)
    {n : ℕ} (k : ℕ) (hk : 1 ≤ k) (h : ∃ x : A, (x : B) * ϖ = a ^ n) :
    ∃ y : A, (y : B) * ϖ = a ^ (n * k) := by
  obtain ⟨x, hx⟩ := h
  refine ⟨⟨(x : B) ^ k * ϖ ^ (k - 1),
      A.mul_mem (A.pow_mem x.2 k) (A.pow_mem hϖA (k - 1))⟩, ?_⟩
  show ((x : B) ^ k * ϖ ^ (k - 1)) * ϖ = a ^ (n * k)
  rw [pow_mul, ← hx, mul_pow]
  rw [mul_assoc, ← pow_succ, Nat.sub_add_cancel hk]

/-- An exponent for membership in `ϖ·A` can be taken positive, provided `B = A[1/ϖ]` in the
generation sense of `nilp_lem_subring` (`hgen`). -/
theorem AAL_N_pos_exp {B : Type*} [CommRing B] (ϖ : B) (A : Subring B)
    (hgen : ∀ z : B, ∃ n : ℕ, ∃ a : A, z * ϖ ^ n = (a : B)) (a : B)
    (h : ∃ n : ℕ, ∃ x : A, (x : B) * ϖ = a ^ n) :
    ∃ N : ℕ, 0 < N ∧ ∃ y : A, (y : B) * ϖ = a ^ N := by
  obtain ⟨n, x, hx⟩ := h
  rcases Nat.eq_zero_or_pos n with hn | hn
  · -- `n = 0`: `x ϖ = 1`, so `ϖ` is a unit of `A`; then `hgen` forces `B = A`, and `N = 1`
    subst hn
    have hx1 : (x : B) * ϖ = 1 := by simpa using hx
    have hBA : ∀ z : B, z ∈ A := by
      intro z
      obtain ⟨k, a', ha'⟩ := hgen z
      have hxpow : (x : B) ^ k * ϖ ^ k = 1 := by rw [← mul_pow, hx1, one_pow]
      have hz : z = (a' : B) * (x : B) ^ k := by
        calc z = z * 1 := (mul_one z).symm
          _ = z * ((x : B) ^ k * ϖ ^ k) := by rw [hxpow]
          _ = (z * ϖ ^ k) * (x : B) ^ k := by ring
          _ = (a' : B) * (x : B) ^ k := by rw [ha']
      rw [hz]
      exact A.mul_mem a'.2 (A.pow_mem x.2 k)
    have ha : a ∈ A := hBA a
    refine ⟨1, Nat.one_pos, ⟨⟨a * (x : B), A.mul_mem ha x.2⟩, ?_⟩⟩
    show (a * (x : B)) * ϖ = a ^ 1
    rw [pow_one, mul_assoc, hx1, mul_one]
  · exact ⟨n, hn, x, hx⟩

/-! ## The main reduction

Given a tilt element `Q` approximating `P` with the Česnavičius–Scholze estimate, produce a single
positive exponent `N` satisfying all three membership conditions. -/

theorem AAL_N_aux {p : ℕ} [Fact p.Prime] {R : Type u} [CommRing R] (QR : DSMap.PerfectoidData p R)
    (P : R) (m : ℕ) (Q : R)
    (hest : ∀ {Γ₀ : Type u} [LinearOrderedCommGroupWithZero Γ₀] (v : Valuation R Γ₀),
      IsContinuousValuation (QR.ϖ 0) v → IsUnitBall v Set.univ →
        v (P - Q) ≤ v (p : R) * max (v Q) (v (QR.ϖ 0) ^ (p * m))) :
    ∃ N : ℕ, 0 < N ∧ (P - Q) ^ N ∈ Ideal.span {QR.ϖ 0} ∧
      (algebraMap R (Localization.Away (QR.ϖ 0)) (P - Q)
          * IsLocalization.Away.invSelf (QR.ϖ 0) ^ m) ^ N ∈
        (Algebra.adjoin R
          ({(algebraMap R (Localization.Away (QR.ϖ 0)) P)
            * IsLocalization.Away.invSelf (QR.ϖ 0) ^ m} :
              Set (Localization.Away (QR.ϖ 0)))).toSubmodule.map
          (LinearMap.mulLeft R (algebraMap R (Localization.Away (QR.ϖ 0)) (QR.ϖ 0))) ∧
      (algebraMap R (Localization.Away (QR.ϖ 0)) (P - Q)
          * IsLocalization.Away.invSelf (QR.ϖ 0) ^ m) ^ N ∈
        (Algebra.adjoin R
          ({(algebraMap R (Localization.Away (QR.ϖ 0)) Q)
            * IsLocalization.Away.invSelf (QR.ϖ 0) ^ m} :
              Set (Localization.Away (QR.ϖ 0)))).toSubmodule.map
          (LinearMap.mulLeft R (algebraMap R (Localization.Away (QR.ϖ 0)) (QR.ϖ 0))) := by
  classical
  have hϖreg : IsSMulRegular (Localization.Away (QR.ϖ 0))
      (algebraMap R (Localization.Away (QR.ϖ 0)) (QR.ϖ 0)) :=
    IsUnit.isSMulRegular _ (IsLocalization.Away.algebraMap_isUnit (QR.ϖ 0))
  -- (i) exponent for the range subring of `R → L`
  have hcondR : ∀ {Γ₀ : Type u} [LinearOrderedCommGroupWithZero Γ₀]
      (v : Valuation (Localization.Away (QR.ϖ 0)) Γ₀),
      IsContinuousValuation (algebraMap R (Localization.Away (QR.ϖ 0)) (QR.ϖ 0)) v →
      IsUnitBall v (((algebraMap R (Localization.Away (QR.ϖ 0))).range) :
          Set (Localization.Away (QR.ϖ 0))) →
      v (algebraMap R (Localization.Away (QR.ϖ 0)) (P - Q)) < 1 := by
    intro Γ₀ _ v hv hball
    have hv' : IsContinuousValuation (QR.ϖ 0)
        (Valuation.precomp (algebraMap R (Localization.Away (QR.ϖ 0))) v) :=
      IsContinuousValuation.precomp (algebraMap R (Localization.Away (QR.ϖ 0))) hv
    have hb' : IsUnitBall (Valuation.precomp (algebraMap R (Localization.Away (QR.ϖ 0))) v)
        (Set.univ : Set R) :=
      IsUnitBall.precomp (algebraMap R (Localization.Away (QR.ϖ 0))) (s := Set.univ)
        (by simpa using hball)
    have hlt := diff_lt_one_of_estimate (P := P) (Q := Q) QR m hest
      (Γ₀ := Γ₀) (Valuation.precomp (algebraMap R (Localization.Away (QR.ϖ 0))) v) hv' hb'
    simpa [Valuation.precomp_apply] using hlt
  obtain ⟨n₁, x₁, hx₁⟩ := nilp_lem_subring
    (algebraMap R (Localization.Away (QR.ϖ 0)) (QR.ϖ 0)) hϖreg
    ((algebraMap R (Localization.Away (QR.ϖ 0))).range) ⟨QR.ϖ 0, rfl⟩
    (generates_of_range QR) (algebraMap R (Localization.Away (QR.ϖ 0)) (P - Q)) hcondR
  -- (ii) exponent for `R[P·u]`
  set AP : Subring (Localization.Away (QR.ϖ 0)) :=
    (Algebra.adjoin R
      ({(algebraMap R (Localization.Away (QR.ϖ 0)) P)
        * IsLocalization.Away.invSelf (QR.ϖ 0) ^ m} :
          Set (Localization.Away (QR.ϖ 0)))).toSubring with hAP
  have hgenP : ∀ z : Localization.Away (QR.ϖ 0), ∃ n : ℕ, ∃ a : AP,
      z * (algebraMap R (Localization.Away (QR.ϖ 0)) (QR.ϖ 0)) ^ n
        = (a : Localization.Away (QR.ϖ 0)) :=
    generates_of_adjoin QR
      ((algebraMap R (Localization.Away (QR.ϖ 0)) P)
        * IsLocalization.Away.invSelf (QR.ϖ 0) ^ m)
  have hϖAP : algebraMap R (Localization.Away (QR.ϖ 0)) (QR.ϖ 0) ∈ AP :=
    (Algebra.adjoin R
      ({(algebraMap R (Localization.Away (QR.ϖ 0)) P)
        * IsLocalization.Away.invSelf (QR.ϖ 0) ^ m} :
          Set (Localization.Away (QR.ϖ 0)))).algebraMap_mem (QR.ϖ 0)
  have hcondP : ∀ {Γ₀ : Type u} [LinearOrderedCommGroupWithZero Γ₀]
      (v : Valuation (Localization.Away (QR.ϖ 0)) Γ₀),
      IsContinuousValuation (algebraMap R (Localization.Away (QR.ϖ 0)) (QR.ϖ 0)) v →
      IsUnitBall v ((AP : Subring (Localization.Away (QR.ϖ 0))) :
          Set (Localization.Away (QR.ϖ 0))) →
      v (algebraMap R (Localization.Away (QR.ϖ 0)) (P - Q)
        * IsLocalization.Away.invSelf (QR.ϖ 0) ^ m) < 1 :=
    delta_lt_one_of_ball_P (P := P) (Q := Q) QR m hest
  obtain ⟨n₂, x₂, hx₂⟩ := nilp_lem_subring
    (algebraMap R (Localization.Away (QR.ϖ 0)) (QR.ϖ 0)) hϖreg AP hϖAP hgenP
    (algebraMap R (Localization.Away (QR.ϖ 0)) (P - Q)
      * IsLocalization.Away.invSelf (QR.ϖ 0) ^ m) hcondP
  -- (iii) exponent for `R[Q·u]`
  set AQ : Subring (Localization.Away (QR.ϖ 0)) :=
    (Algebra.adjoin R
      ({(algebraMap R (Localization.Away (QR.ϖ 0)) Q)
        * IsLocalization.Away.invSelf (QR.ϖ 0) ^ m} :
          Set (Localization.Away (QR.ϖ 0)))).toSubring with hAQ
  have hgenQ : ∀ z : Localization.Away (QR.ϖ 0), ∃ n : ℕ, ∃ a : AQ,
      z * (algebraMap R (Localization.Away (QR.ϖ 0)) (QR.ϖ 0)) ^ n
        = (a : Localization.Away (QR.ϖ 0)) :=
    generates_of_adjoin QR
      ((algebraMap R (Localization.Away (QR.ϖ 0)) Q)
        * IsLocalization.Away.invSelf (QR.ϖ 0) ^ m)
  have hϖAQ : algebraMap R (Localization.Away (QR.ϖ 0)) (QR.ϖ 0) ∈ AQ :=
    (Algebra.adjoin R
      ({(algebraMap R (Localization.Away (QR.ϖ 0)) Q)
        * IsLocalization.Away.invSelf (QR.ϖ 0) ^ m} :
          Set (Localization.Away (QR.ϖ 0)))).algebraMap_mem (QR.ϖ 0)
  have hcondQ : ∀ {Γ₀ : Type u} [LinearOrderedCommGroupWithZero Γ₀]
      (v : Valuation (Localization.Away (QR.ϖ 0)) Γ₀),
      IsContinuousValuation (algebraMap R (Localization.Away (QR.ϖ 0)) (QR.ϖ 0)) v →
      IsUnitBall v ((AQ : Subring (Localization.Away (QR.ϖ 0))) :
          Set (Localization.Away (QR.ϖ 0))) →
      v (algebraMap R (Localization.Away (QR.ϖ 0)) (P - Q)
        * IsLocalization.Away.invSelf (QR.ϖ 0) ^ m) < 1 :=
    delta_lt_one_of_ball_Q (P := P) (Q := Q) QR m hest
  obtain ⟨n₃, x₃, hx₃⟩ := nilp_lem_subring
    (algebraMap R (Localization.Away (QR.ϖ 0)) (QR.ϖ 0)) hϖreg AQ hϖAQ hgenQ
    (algebraMap R (Localization.Away (QR.ϖ 0)) (P - Q)
      * IsLocalization.Away.invSelf (QR.ϖ 0) ^ m) hcondQ
  -- upgrade to positive exponents
  obtain ⟨N₂, hN₂pos, x₂', hx₂'⟩ := AAL_N_pos_exp _ AP hgenP _ ⟨n₂, x₂, hx₂⟩
  obtain ⟨N₃, hN₃pos, x₃', hx₃'⟩ := AAL_N_pos_exp _ AQ hgenQ _ ⟨n₃, x₃, hx₃⟩
  -- (i) pull back the range exponent to `R`
  have hmem₁ : (P - Q) ^ n₁ ∈ Ideal.span {QR.ϖ 0} := by
    obtain ⟨r, hr⟩ := RingHom.mem_range.mp x₁.2
    have h2 : (P - Q) ^ n₁ = r * (QR.ϖ 0) := by
      have h1 : algebraMap R (Localization.Away (QR.ϖ 0)) ((P - Q) ^ n₁)
          = algebraMap R (Localization.Away (QR.ϖ 0)) (r * (QR.ϖ 0)) := by
        rw [map_pow, map_mul, hr]
        exact hx₁.symm
      exact algebraMap_away_injective QR h1
    rw [h2]
    exact Ideal.mul_mem_left _ r (Ideal.mem_span_singleton_self _)
  set N : ℕ := N₂ * N₃ * (n₁ + 1) with hNdef
  have hfoldP : N₂ * (N₃ * (n₁ + 1)) = N := by rw [hNdef]; ring
  have hfoldQ : N₃ * (N₂ * (n₁ + 1)) = N := by rw [hNdef]; ring
  have hle₁ : n₁ ≤ N := by
    have h2 : 1 ≤ N₂ * N₃ := by
      calc 1 = 1 * 1 := (mul_one 1).symm
        _ ≤ N₂ * N₃ := Nat.mul_le_mul hN₂pos hN₃pos
    rw [hNdef]
    calc n₁ ≤ n₁ + 1 := Nat.le_succ n₁
      _ = 1 * (n₁ + 1) := (one_mul _).symm
      _ ≤ N₂ * N₃ * (n₁ + 1) := Nat.mul_le_mul_right _ h2
  have hmulNZ : 1 ≤ N₃ * (n₁ + 1) := by
    calc 1 = 1 * 1 := (mul_one 1).symm
      _ ≤ N₃ * (n₁ + 1) := Nat.mul_le_mul hN₃pos (Nat.succ_le_succ (Nat.zero_le n₁))
  have hmulNP : 1 ≤ N₂ * (n₁ + 1) := by
    calc 1 = 1 * 1 := (mul_one 1).symm
      _ ≤ N₂ * (n₁ + 1) := Nat.mul_le_mul hN₂pos (Nat.succ_le_succ (Nat.zero_le n₁))
  -- (i) with the large exponent
  have hfin₁ : (P - Q) ^ N ∈ Ideal.span {QR.ϖ 0} := by
    have hstep : (P - Q) ^ N = (P - Q) ^ (N - n₁) * (P - Q) ^ n₁ := by
      rw [← pow_add, Nat.sub_add_cancel hle₁]
    rw [hstep]
    exact Ideal.mul_mem_left _ _ hmem₁
  -- (ii)
  have hδP : (algebraMap R (Localization.Away (QR.ϖ 0)) (P - Q)
        * IsLocalization.Away.invSelf (QR.ϖ 0) ^ m) ^ N ∈
      (Algebra.adjoin R
        ({(algebraMap R (Localization.Away (QR.ϖ 0)) P)
          * IsLocalization.Away.invSelf (QR.ϖ 0) ^ m} :
            Set (Localization.Away (QR.ϖ 0)))).toSubmodule.map
        (LinearMap.mulLeft R (algebraMap R (Localization.Away (QR.ϖ 0)) (QR.ϖ 0))) := by
    obtain ⟨y, hy⟩ := AAL_N_mul_exp _ AP hϖAP _ (N₃ * (n₁ + 1)) hmulNZ ⟨x₂', hx₂'⟩
    rw [hfoldP] at hy
    refine Submodule.mem_map.mpr ⟨(y : Localization.Away (QR.ϖ 0)), ?_, ?_⟩
    · show (y : Localization.Away (QR.ϖ 0)) ∈
        Algebra.adjoin R ({(algebraMap R (Localization.Away (QR.ϖ 0)) P)
          * IsLocalization.Away.invSelf (QR.ϖ 0) ^ m} :
            Set (Localization.Away (QR.ϖ 0)))
      exact y.2
    · rw [LinearMap.mulLeft_apply, mul_comm, hy]
  -- (iii)
  have hδQ : (algebraMap R (Localization.Away (QR.ϖ 0)) (P - Q)
        * IsLocalization.Away.invSelf (QR.ϖ 0) ^ m) ^ N ∈
      (Algebra.adjoin R
        ({(algebraMap R (Localization.Away (QR.ϖ 0)) Q)
          * IsLocalization.Away.invSelf (QR.ϖ 0) ^ m} :
            Set (Localization.Away (QR.ϖ 0)))).toSubmodule.map
        (LinearMap.mulLeft R (algebraMap R (Localization.Away (QR.ϖ 0)) (QR.ϖ 0))) := by
    obtain ⟨y, hy⟩ := AAL_N_mul_exp _ AQ hϖAQ _ (N₂ * (n₁ + 1)) hmulNP ⟨x₃', hx₃'⟩
    rw [hfoldQ] at hy
    refine Submodule.mem_map.mpr ⟨(y : Localization.Away (QR.ϖ 0)), ?_, ?_⟩
    · show (y : Localization.Away (QR.ϖ 0)) ∈
        Algebra.adjoin R ({(algebraMap R (Localization.Away (QR.ϖ 0)) Q)
          * IsLocalization.Away.invSelf (QR.ϖ 0) ^ m} :
            Set (Localization.Away (QR.ϖ 0)))
      exact y.2
    · rw [LinearMap.mulLeft_apply, mul_comm, hy]
  exact ⟨N, Nat.mul_pos (Nat.mul_pos hN₂pos hN₃pos) (Nat.succ_pos n₁), hfin₁, hδP, hδQ⟩

theorem AAL_N (p : ℕ) [Fact p.Prime] (R : Type*) [CommRing R] (QR : DSMap.PerfectoidData p R)
    (P : R) (m : ℕ) :
    ∃ (Qr : ℕ → R) (N : ℕ), 0 < N ∧ (∀ j, Qr (j + 1) ^ p = Qr j) ∧
      (P - Qr 0) ^ N ∈ Ideal.span {QR.ϖ 0} ∧
      let L := Localization.Away (QR.ϖ 0)
      let u : L := IsLocalization.Away.invSelf (QR.ϖ 0) ^ m
      (algebraMap R L (P - Qr 0) * u) ^ N ∈
          (Algebra.adjoin R {algebraMap R L P * u}).toSubmodule.map
            (LinearMap.mulLeft R (algebraMap R L (QR.ϖ 0))) ∧
      (algebraMap R L (P - Qr 0) * u) ^ N ∈
          (Algebra.adjoin R {algebraMap R L (Qr 0) * u}).toSubmodule.map
            (LinearMap.mulLeft R (algebraMap R L (QR.ϖ 0))) := by
  by_cases hp : IsUnit (p : R)
  · -- `p` a unit: `R` is the zero ring, everything is trivial
    haveI : Subsingleton R := subsingleton_of_isUnit_p QR hp
    have hP0 : P - (0 : R) = 0 := Subsingleton.elim _ _
    refine ⟨fun _ => 0, 1, Nat.one_pos, fun j => ?_, ?_, ?_, ?_⟩
    · rw [zero_pow ((Fact.out : p.Prime).pos).ne']
    · rw [hP0, pow_one]
      exact Ideal.zero_mem _
    · show (algebraMap R (Localization.Away (QR.ϖ 0)) (P - (fun _ => (0 : R)) 0)
            * IsLocalization.Away.invSelf (QR.ϖ 0) ^ m) ^ (1 : ℕ) ∈ _
      rw [hP0, map_zero, zero_mul, pow_one]
      exact Submodule.zero_mem _
    · show (algebraMap R (Localization.Away (QR.ϖ 0)) (P - (fun _ => (0 : R)) 0)
            * IsLocalization.Away.invSelf (QR.ϖ 0) ^ m) ^ (1 : ℕ) ∈ _
      rw [hP0, map_zero, zero_mul, pow_one]
      exact Submodule.zero_mem _
  · haveI : Fact (¬ IsUnit (p : R)) := ⟨hp⟩
    haveI : IsAdicComplete (Ideal.span {(p : R)}) R := QR.complete
    obtain ⟨ξ, hξ⟩ := approx_lem QR P m
    set Q : R := PreTilt.untilt ξ with hQ
    have hQroots : HasCompatPRoots p Q := by
      rw [hQ]; exact untilt_hasCompatPRoots ξ
    obtain ⟨Qr, hQr0, hQrroot⟩ := hQroots
    obtain ⟨N, hNpos, h1, h2, h3⟩ := AAL_N_aux QR P m Q hξ
    refine ⟨Qr, N, hNpos, hQrroot, ?_, ?_, ?_⟩
    · rw [hQr0]; exact h1
    · show (algebraMap R (Localization.Away (QR.ϖ 0)) (P - Qr 0)
            * IsLocalization.Away.invSelf (QR.ϖ 0) ^ m) ^ N ∈ _
      rw [hQr0]; exact h2
    · show (algebraMap R (Localization.Away (QR.ϖ 0)) (P - Qr 0)
            * IsLocalization.Away.invSelf (QR.ϖ 0) ^ m) ^ N ∈ _
      rw [hQr0]; exact h3

end Work.DSM2p
