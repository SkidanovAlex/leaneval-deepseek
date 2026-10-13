import Submission.Work.DSM2p.N8deps

namespace Work.DSM2p

/-! ## Basic facts about the `ϖ`-system inside `Λ = A[T^{1/p^∞}]` -/

/-- `ϖ_j` viewed inside `Λ = Lam1 A p`. -/
noncomputable abbrev wj (A : Type*) [CommRing A] (p : ℕ) (P : DSMap.PerfectoidData p A) :
    ℕ → Lam1 A p :=
  fun j => algebraMap A (Lam1 A p) (P.ϖ j)

theorem wj_root (A : Type*) [CommRing A] (p : ℕ) (P : DSMap.PerfectoidData p A) (j : ℕ) :
    wj A p P (j + 1) ^ p = wj A p P j := by
  rw [wj, ← map_pow, P.root j]

theorem wj_pow (A : Type*) [CommRing A] (p : ℕ) (P : DSMap.PerfectoidData p A) (j k : ℕ) :
    wj A p P (j + k) ^ (p ^ k) = wj A p P j := by
  induction k with
  | zero => simp [wj]
  | succ k ih =>
    have h1 : j + (k + 1) = (j + k) + 1 := by ring
    rw [h1, pow_succ' p k, pow_mul, wj_root A p P (j + k)]
    exact ih

theorem wj_pow_zero (A : Type*) [CommRing A] (p : ℕ) (P : DSMap.PerfectoidData p A) (j : ℕ) :
    wj A p P j ^ (p ^ j) = wj A p P 0 := by
  simpa using wj_pow A p P 0 j

theorem wj_reg0 (A : Type*) [CommRing A] (p : ℕ) [Fact p.Prime] (P : DSMap.PerfectoidData p A) :
    IsSMulRegular (Lam1 A p) (wj A p P 0) := by
  have hp : p.Prime := Fact.out
  have hp1 : 1 ≤ p := hp.one_le
  have hpreg : IsSMulRegular (Lam1 A p) (p : Lam1 A p) :=
    rootClosure_isSMulRegular A p PUnit P.torsionFree
  obtain ⟨v, hv⟩ := P.unit
  set u : (Lam1 A p)ˣ := Units.map (algebraMap A (Lam1 A p)) v with hu
  have hvp : wj A p P 0 ^ p = (p : Lam1 A p) * (u : Lam1 A p) := by
    rw [hu, wj, ← map_pow, hv, map_mul, map_natCast, Units.coe_map]
    rfl
  have h1 : IsSMulRegular (Lam1 A p) (wj A p P 0 ^ p) := by
    rw [hvp]
    exact hpreg.mul (IsUnit.isSMulRegular _ (Units.isUnit u))
  intro x y hxy
  simp only [smul_eq_mul] at hxy
  have h2 : wj A p P 0 ^ p * x = wj A p P 0 ^ p * y := by
    calc wj A p P 0 ^ p * x = (wj A p P 0 ^ (p - 1) * wj A p P 0) * x := by
          rw [← pow_succ, Nat.sub_add_cancel hp1]
      _ = wj A p P 0 ^ (p - 1) * (wj A p P 0 * x) := by rw [mul_assoc]
      _ = wj A p P 0 ^ (p - 1) * (wj A p P 0 * y) := by rw [hxy]
      _ = (wj A p P 0 ^ (p - 1) * wj A p P 0) * y := by rw [mul_assoc]
      _ = wj A p P 0 ^ p * y := by rw [← pow_succ, Nat.sub_add_cancel hp1]
  exact h1 (by simpa only [smul_eq_mul] using h2)

theorem Lam1Loc_algebraMap_injective (A : Type*) [CommRing A] (p : ℕ) [Fact p.Prime]
    (P : DSMap.PerfectoidData p A) :
    Function.Injective (algebraMap (Lam1 A p) (Lam1Loc A p (P.ϖ 0))) := by
  have hle : Submonoid.powers (algebraMap A (Lam1 A p) (P.ϖ 0)) ≤
      nonZeroDivisors (Lam1 A p) := by
    intro x hx
    obtain ⟨n, rfl⟩ :=
      (Submonoid.mem_powers_iff x (algebraMap A (Lam1 A p) (P.ϖ 0))).mp hx
    rw [mem_nonZeroDivisors_iff]
    have hreg := (wj_reg0 A p P).pow n
    constructor
    · intro a ha
      exact hreg (by simpa only [smul_eq_mul, mul_zero] using ha)
    · intro a ha
      have h2 : (algebraMap A (Lam1 A p) (P.ϖ 0)) ^ n * a = 0 := by
        rw [mul_comm]; exact ha
      exact hreg (by simpa only [smul_eq_mul, mul_zero] using h2)
  exact IsLocalization.injective
    (M := Submonoid.powers (algebraMap A (Lam1 A p) (P.ϖ 0)))
    (S := Lam1Loc A p (P.ϖ 0)) hle

theorem wj_unit_L (A : Type*) [CommRing A] (p : ℕ) [Fact p.Prime] (P : DSMap.PerfectoidData p A)
    (j : ℕ) : IsUnit (algebraMap (Lam1 A p) (Lam1Loc A p (P.ϖ 0)) (wj A p P j)) := by
  have hp0 : p ^ j ≠ 0 := pow_ne_zero _ (Fact.out : p.Prime).ne_zero
  refine (isUnit_pow_iff hp0).mp ?_
  rw [← map_pow, wj_pow_zero A p P j]
  exact IsLocalization.Away.algebraMap_isUnit _

theorem p_mem_wj0 (A : Type*) [CommRing A] (p : ℕ) [Fact p.Prime] (P : DSMap.PerfectoidData p A) :
    (p : Lam1 A p) ∈ Ideal.span {wj A p P 0} := by
  have hp1 : 1 ≤ p := (Fact.out : p.Prime).one_le
  obtain ⟨v, hv⟩ := P.unit
  set u : (Lam1 A p)ˣ := Units.map (algebraMap A (Lam1 A p)) v with hu
  have hup : (p : Lam1 A p) * (u : Lam1 A p) = wj A p P 0 ^ p := by
    rw [hu, wj, ← map_pow, hv, map_mul, map_natCast, Units.coe_map]
    rfl
  refine Ideal.mem_span_singleton'.mpr
    ⟨wj A p P 0 ^ (p - 1) * ((u⁻¹ : (Lam1 A p)ˣ) : Lam1 A p), ?_⟩
  have hcalc : wj A p P 0 ^ p * ((u⁻¹ : (Lam1 A p)ˣ) : Lam1 A p) = (p : Lam1 A p) := by
    rw [← hup, mul_assoc, Units.mul_inv, mul_one]
  rw [← hcalc]
  rw [mul_assoc, mul_comm (((u⁻¹ : (Lam1 A p)ˣ) : Lam1 A p)) (wj A p P 0), ← mul_assoc,
    ← pow_succ, Nat.sub_add_cancel hp1]

theorem mem_span_wj0_of_mem_span_p (A : Type*) [CommRing A] (p : ℕ) [Fact p.Prime]
    (P : DSMap.PerfectoidData p A) {c : Lam1 A p} (hc : c ∈ Ideal.span {(p : Lam1 A p)}) :
    c ∈ Ideal.span {wj A p P 0} :=
  (Ideal.span_singleton_le_iff_mem _).mpr (p_mem_wj0 A p P) hc

theorem Lam1_frobSurj_wj0 (A : Type*) [CommRing A] (p : ℕ) [Fact p.Prime]
    (P : DSMap.PerfectoidData p A) :
    ∀ x : Lam1 A p, ∃ y : Lam1 A p, x - y ^ p ∈ Ideal.span {wj A p P 0} := by
  intro x
  obtain ⟨y, hy⟩ := Lam1_frobSurj A p P x
  exact ⟨y, mem_span_wj0_of_mem_span_p A p P hy⟩

theorem frobInj_wj1 (A : Type*) [CommRing A] (p : ℕ) [Fact p.Prime]
    (P : DSMap.PerfectoidData p A) {b : Lam1 A p}
    (hb : b ^ p ∈ Ideal.span {wj A p P 1 ^ p}) : b ∈ Ideal.span {wj A p P 1} := by
  have hspan : Ideal.span {wj A p P 1 ^ p} = Ideal.span {algebraMap A (Lam1 A p) (P.ϖ 0)} := by
    rw [wj_root A p P 0]
  rw [hspan] at hb
  have h := N5d_frobInj_scaled A p P 0 b (by simpa [wj] using hb)
  simpa [wj] using h

theorem hgen_L (A : Type*) [CommRing A] (p : ℕ) [Fact p.Prime] (P : DSMap.PerfectoidData p A) :
    ∀ z : Lam1Loc A p (P.ϖ 0), ∃ k : ℕ, ∃ c : Lam1 A p,
      algebraMap (Lam1 A p) (Lam1Loc A p (P.ϖ 0)) (wj A p P 1 ^ k) * z =
        algebraMap (Lam1 A p) (Lam1Loc A p (P.ϖ 0)) c := by
  intro z
  obtain ⟨n, a, ha⟩ := IsLocalization.Away.surj (algebraMap A (Lam1 A p) (P.ϖ 0)) z
  refine ⟨p * n, a, ?_⟩
  have hV : algebraMap (Lam1 A p) (Lam1Loc A p (P.ϖ 0)) (wj A p P 0) *
      IsLocalization.Away.invSelf (algebraMap A (Lam1 A p) (P.ϖ 0)) = 1 :=
    IsLocalization.Away.mul_invSelf _
  have hVn : (algebraMap (Lam1 A p) (Lam1Loc A p (P.ϖ 0)) (wj A p P 0)) ^ n *
      IsLocalization.Away.invSelf (algebraMap A (Lam1 A p) (P.ϖ 0)) ^ n = 1 := by
    rw [← mul_pow, hV, one_pow]
  have hz : z = algebraMap (Lam1 A p) (Lam1Loc A p (P.ϖ 0)) a *
      IsLocalization.Away.invSelf (algebraMap A (Lam1 A p) (P.ϖ 0)) ^ n := by
    calc z = z * (algebraMap (Lam1 A p) (Lam1Loc A p (P.ϖ 0)) (wj A p P 0) *
          IsLocalization.Away.invSelf (algebraMap A (Lam1 A p) (P.ϖ 0))) ^ n := by
          rw [hV, one_pow, mul_one]
      _ = z * (algebraMap (Lam1 A p) (Lam1Loc A p (P.ϖ 0)) (wj A p P 0)) ^ n *
            IsLocalization.Away.invSelf (algebraMap A (Lam1 A p) (P.ϖ 0)) ^ n := by
          rw [mul_pow, mul_assoc]
      _ = algebraMap (Lam1 A p) (Lam1Loc A p (P.ϖ 0)) a *
            IsLocalization.Away.invSelf (algebraMap A (Lam1 A p) (P.ϖ 0)) ^ n := by
          rw [ha]
  have hkey : algebraMap (Lam1 A p) (Lam1Loc A p (P.ϖ 0)) (wj A p P 1 ^ (p * n)) =
      (algebraMap (Lam1 A p) (Lam1Loc A p (P.ϖ 0)) (wj A p P 0)) ^ n := by
    rw [map_pow, pow_mul, ← map_pow, wj_root A p P 0]
  calc algebraMap (Lam1 A p) (Lam1Loc A p (P.ϖ 0)) (wj A p P 1 ^ (p * n)) * z
      = (algebraMap (Lam1 A p) (Lam1Loc A p (P.ϖ 0)) (wj A p P 0)) ^ n *
          (algebraMap (Lam1 A p) (Lam1Loc A p (P.ϖ 0)) a *
            IsLocalization.Away.invSelf (algebraMap A (Lam1 A p) (P.ϖ 0)) ^ n) := by
        rw [hz, hkey]
    _ = algebraMap (Lam1 A p) (Lam1Loc A p (P.ϖ 0)) a := by
        rw [mul_left_comm, hVn, mul_one]



/-! ## The fraction calculus on `L = Λ[1/ϖ₀]` -/

/-- The inverse of `ϖ₀` in `L`. -/
noncomputable def V0 (A : Type*) [CommRing A] (p : ℕ) (P : DSMap.PerfectoidData p A) :
    Lam1Loc A p (P.ϖ 0) :=
  IsLocalization.Away.invSelf (algebraMap A (Lam1 A p) (P.ϖ 0))

/-- `frac` in the "explicit denominator" form. -/
theorem frac_eq (A : Type*) [CommRing A] (p : ℕ) (P : DSMap.PerfectoidData p A)
    (a : Lam1 A p) (M : ℕ) :
    frac A p (P.ϖ 0) a M = algebraMap (Lam1 A p) (Lam1Loc A p (P.ϖ 0)) a * V0 A p P ^ M := by
  simp only [frac, V0]

theorem frac_sub (A : Type*) [CommRing A] (p : ℕ) (P : DSMap.PerfectoidData p A)
    (a b : Lam1 A p) (M : ℕ) :
    frac A p (P.ϖ 0) a M - frac A p (P.ϖ 0) b M = frac A p (P.ϖ 0) (a - b) M := by
  have h : algebraMap (Lam1 A p) (Lam1Loc A p (P.ϖ 0)) (a - b) =
      algebraMap (Lam1 A p) (Lam1Loc A p (P.ϖ 0)) a -
        algebraMap (Lam1 A p) (Lam1Loc A p (P.ϖ 0)) b :=
    RingHom.map_sub _ a b
  rw [frac_eq, frac_eq, frac_eq, h, sub_mul]

theorem wj0_pow_mul_invSelf_pow (A : Type*) [CommRing A] (p : ℕ) (P : DSMap.PerfectoidData p A)
    (k : ℕ) : (algebraMap (Lam1 A p) (Lam1Loc A p (P.ϖ 0)) (wj A p P 0)) ^ k * V0 A p P ^ k = 1 := by
  have hV : algebraMap (Lam1 A p) (Lam1Loc A p (P.ϖ 0)) (wj A p P 0) * V0 A p P = 1 :=
    IsLocalization.Away.mul_invSelf _
  rw [← mul_pow, hV, one_pow]

/-- Clearing a power of `ϖ₀` from the numerator. -/
theorem frac_mul_wj0_pow (A : Type*) [CommRing A] (p : ℕ) (P : DSMap.PerfectoidData p A)
    (b : Lam1 A p) {k N : ℕ} (hk : k ≤ N) :
    frac A p (P.ϖ 0) (b * wj A p P 0 ^ k) N = frac A p (P.ϖ 0) b (N - k) := by
  have hVN : V0 A p P ^ N = V0 A p P ^ k * V0 A p P ^ (N - k) := by
    conv_lhs => rw [show N = k + (N - k) from (Nat.add_sub_cancel' hk).symm]
    rw [pow_add]
  calc frac A p (P.ϖ 0) (b * wj A p P 0 ^ k) N
      = (algebraMap (Lam1 A p) (Lam1Loc A p (P.ϖ 0)) b *
          (algebraMap (Lam1 A p) (Lam1Loc A p (P.ϖ 0)) (wj A p P 0)) ^ k) *
          V0 A p P ^ N := by
        rw [frac_eq, map_mul, map_pow]
    _ = (algebraMap (Lam1 A p) (Lam1Loc A p (P.ϖ 0)) b *
          (algebraMap (Lam1 A p) (Lam1Loc A p (P.ϖ 0)) (wj A p P 0)) ^ k) *
          (V0 A p P ^ k * V0 A p P ^ (N - k)) := by rw [hVN]
    _ = algebraMap (Lam1 A p) (Lam1Loc A p (P.ϖ 0)) b *
          (((algebraMap (Lam1 A p) (Lam1Loc A p (P.ϖ 0)) (wj A p P 0)) ^ k * V0 A p P ^ k) *
            V0 A p P ^ (N - k)) := by ring
    _ = algebraMap (Lam1 A p) (Lam1Loc A p (P.ϖ 0)) b * V0 A p P ^ (N - k) := by
        rw [wj0_pow_mul_invSelf_pow, one_mul]
    _ = frac A p (P.ϖ 0) b (N - k) := by rw [frac_eq]

theorem frac_mul_wj0_pow_self (A : Type*) [CommRing A] (p : ℕ) (P : DSMap.PerfectoidData p A)
    (b : Lam1 A p) (N : ℕ) :
    frac A p (P.ϖ 0) (b * wj A p P 0 ^ N) N =
      algebraMap (Lam1 A p) (Lam1Loc A p (P.ϖ 0)) b := by
  rw [frac_mul_wj0_pow A p P b (le_refl N), Nat.sub_self, frac_eq, pow_zero, mul_one]

theorem algebraMap_varpi_mul_frac (A : Type*) [CommRing A] (p : ℕ) (P : DSMap.PerfectoidData p A)
    (c : Lam1 A p) (N : ℕ) :
    algebraMap (Lam1 A p) (Lam1Loc A p (P.ϖ 0)) (wj A p P 0 ^ N) *
      frac A p (P.ϖ 0) c N = algebraMap (Lam1 A p) (Lam1Loc A p (P.ϖ 0)) c := by
  rw [frac_eq, map_pow, mul_left_comm, wj0_pow_mul_invSelf_pow, mul_one]

theorem frac_pow (A : Type*) [CommRing A] (p : ℕ) (P : DSMap.PerfectoidData p A)
    (a : Lam1 A p) (N k : ℕ) :
    frac A p (P.ϖ 0) a N ^ k = frac A p (P.ϖ 0) (a ^ k) (N * k) := by
  rw [frac_eq, frac_eq, mul_pow, ← map_pow, ← pow_mul]

/-! ## Elementary exponent identities -/

theorem mul_pred_add_self {M j p : ℕ} (hp : 1 ≤ p) : M * (p ^ j - 1) + M = M * p ^ j := by
  have hs : (p ^ j - 1).succ = p ^ j := Nat.succ_pred_eq_of_pos (one_le_pow₀ hp)
  have h := Nat.mul_succ M (p ^ j - 1)
  rw [hs] at h
  exact h.symm

theorem self_add_mul_pred {M j p : ℕ} (hp : 1 ≤ p) : M + M * (p ^ j - 1) = M * p ^ j := by
  rw [Nat.add_comm]; exact mul_pred_add_self hp

theorem mul_sub_pred {M p : ℕ} (hp : 1 ≤ p) : M * p - M * (p - 1) = M := by
  rw [← Nat.mul_sub_left_distrib, Nat.sub_sub_self hp, mul_one]

theorem pow_succ_sub_one {p j : ℕ} (hp : 1 ≤ p) :
    p ^ (j + 1) - 1 = (p ^ j - 1) + p ^ j * (p - 1) := by
  have hpj : 1 ≤ p ^ j := one_le_pow₀ hp
  have h1 : p ^ j * p = p ^ j * (p - 1) + p ^ j := by
    have h := Nat.mul_succ (p ^ j) (p - 1)
    rwa [show (p - 1).succ = p from Nat.succ_pred_eq_of_pos hp] at h
  have h2 : p ^ (j + 1) = p ^ j * p := by rw [pow_succ', mul_comm]
  rw [h2, h1, Nat.add_sub_assoc hpj, Nat.add_comm]

/-- The exponent identity driving the monotonicity of the `x_j`. -/
theorem wj_expo_step (A : Type*) [CommRing A] (p : ℕ) [Fact p.Prime]
    (P : DSMap.PerfectoidData p A) (M j : ℕ) :
    wj A p P (j + 1) ^ (M * (p ^ (j + 1) - 1) * p) =
      wj A p P j ^ (M * (p ^ j - 1)) * wj A p P 0 ^ (M * (p - 1)) := by
  have hp1 : 1 ≤ p := (Fact.out : p.Prime).one_le
  have hpe := pow_succ_sub_one (p := p) (j := j) hp1
  have h2 : p ^ (j + 1) = p ^ j * p := by rw [pow_succ', mul_comm]
  have hexp : M * (p ^ (j + 1) - 1) * p
      = p * (M * (p ^ j - 1)) + p ^ (j + 1) * (M * (p - 1)) := by
    rw [hpe, h2]; ring
  have hfirst : wj A p P (j + 1) ^ (p * (M * (p ^ j - 1))) =
      wj A p P j ^ (M * (p ^ j - 1)) := by
    rw [pow_mul, wj_root A p P j]
  have hsecond : wj A p P (j + 1) ^ (p ^ (j + 1) * (M * (p - 1))) =
      wj A p P 0 ^ (M * (p - 1)) := by
    rw [pow_mul, wj_pow_zero A p P (j + 1)]
  rw [hexp, pow_add, hfirst, hsecond]


end Work.DSM2p
