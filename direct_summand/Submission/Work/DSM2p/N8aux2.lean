import Submission.Work.DSM2p.N8aux1

namespace Work.DSM2p

/-! ## The candidate pieces and their properties -/

/-- The numerator of the `j`-th flat piece. -/
noncomputable abbrev num (A : Type*) [CommRing A] (p : ℕ) (P : DSMap.PerfectoidData p A)
    (M : ℕ) (q : ℕ → Lam1 A p) (j : ℕ) : Lam1 A p :=
  q j * wj A p P j ^ (M * (p ^ j - 1))

/-- The `F(T)/ϖ^M`-generator. -/
noncomputable abbrev yF (A : Type*) [CommRing A] (p : ℕ) (P : DSMap.PerfectoidData p A)
    (F : Polynomial A) (M : ℕ) : Lam1Loc A p (P.ϖ 0) :=
  frac A p (P.ϖ 0) (Polynomial.aeval (T1 A p 0) F) M

theorem num_zero (A : Type*) [CommRing A] (p : ℕ) (P : DSMap.PerfectoidData p A)
    (M : ℕ) (q : ℕ → Lam1 A p) : num A p P M q 0 = q 0 := by
  simp only [num, pow_zero, Nat.sub_self, Nat.mul_zero, mul_one]

theorem num_pow_succ (A : Type*) [CommRing A] (p : ℕ) [Fact p.Prime]
    (P : DSMap.PerfectoidData p A) (M : ℕ) (q : ℕ → Lam1 A p) (j : ℕ) :
    num A p P M q (j + 1) ^ p =
      q (j + 1) ^ p * wj A p P j ^ (M * (p ^ j - 1)) * wj A p P 0 ^ (M * (p - 1)) := by
  rw [mul_pow, ← pow_mul, wj_expo_step, mul_assoc]

theorem num_pow_pow (A : Type*) [CommRing A] (p : ℕ) (P : DSMap.PerfectoidData p A)
    (M : ℕ) (q : ℕ → Lam1 A p) (j : ℕ) :
    num A p P M q j ^ (p ^ j) = q j ^ (p ^ j) * wj A p P 0 ^ (M * (p ^ j - 1)) := by
  rw [mul_pow, ← pow_mul, mul_comm (M * (p ^ j - 1)) (p ^ j), pow_mul, wj_pow_zero A p P j]

theorem stage_hs (A : Type*) [CommRing A] (p : ℕ) (P : DSMap.PerfectoidData p A)
    (M : ℕ) (j : ℕ) : (wj A p P (j + 1) ^ M) ^ p = wj A p P j ^ M := by
  rw [← pow_mul, mul_comm M p, pow_mul, wj_root A p P j]

theorem stage_hsL (A : Type*) [CommRing A] (p : ℕ) [Fact p.Prime]
    (P : DSMap.PerfectoidData p A) (M : ℕ) (j : ℕ) :
    IsUnit (algebraMap (Lam1 A p) (Lam1Loc A p (P.ϖ 0)) (wj A p P j ^ M)) := by
  rw [map_pow]
  exact (wj_unit_L A p P j).pow M

/-- The `x_j` and `s_j` satisfy `s_j * x_j = q_j`, with `s_j = ϖ_j^M`. -/
theorem stage_hx (A : Type*) [CommRing A] (p : ℕ) [Fact p.Prime]
    (P : DSMap.PerfectoidData p A) (M : ℕ) (q : ℕ → Lam1 A p) (j : ℕ) :
    algebraMap (Lam1 A p) (Lam1Loc A p (P.ϖ 0)) (wj A p P j ^ M) *
      frac A p (P.ϖ 0) (num A p P M q j) M =
      algebraMap (Lam1 A p) (Lam1Loc A p (P.ϖ 0)) (q j) := by
  have hp1 : 1 ≤ p := (Fact.out : p.Prime).one_le
  have hAB : (algebraMap (Lam1 A p) (Lam1Loc A p (P.ϖ 0)) (wj A p P j)) ^ M *
      (algebraMap (Lam1 A p) (Lam1Loc A p (P.ϖ 0)) (wj A p P j)) ^ (M * (p ^ j - 1)) =
      (algebraMap (Lam1 A p) (Lam1Loc A p (P.ϖ 0)) (wj A p P 0)) ^ M := by
    rw [← pow_add, self_add_mul_pred (M := M) hp1, mul_comm M (p ^ j), pow_mul,
      ← map_pow, wj_pow_zero A p P j]
  calc algebraMap (Lam1 A p) (Lam1Loc A p (P.ϖ 0)) (wj A p P j ^ M) *
        frac A p (P.ϖ 0) (num A p P M q j) M
      = (algebraMap (Lam1 A p) (Lam1Loc A p (P.ϖ 0)) (wj A p P j)) ^ M *
          ((algebraMap (Lam1 A p) (Lam1Loc A p (P.ϖ 0)) (q j) *
            (algebraMap (Lam1 A p) (Lam1Loc A p (P.ϖ 0)) (wj A p P j)) ^ (M * (p ^ j - 1)) *
              V0 A p P ^ M)) := by
        rw [frac_eq, map_pow, map_mul, map_pow]
    _ = algebraMap (Lam1 A p) (Lam1Loc A p (P.ϖ 0)) (q j) *
          ((algebraMap (Lam1 A p) (Lam1Loc A p (P.ϖ 0)) (wj A p P j)) ^ M *
            (algebraMap (Lam1 A p) (Lam1Loc A p (P.ϖ 0)) (wj A p P j)) ^ (M * (p ^ j - 1)) *
              V0 A p P ^ M) := by ring
    _ = algebraMap (Lam1 A p) (Lam1Loc A p (P.ϖ 0)) (q j) *
          ((algebraMap (Lam1 A p) (Lam1Loc A p (P.ϖ 0)) (wj A p P 0)) ^ M *
            V0 A p P ^ M) := by rw [hAB]
    _ = algebraMap (Lam1 A p) (Lam1Loc A p (P.ϖ 0)) (q j) := by
        rw [wj0_pow_mul_invSelf_pow, mul_one]

theorem stage_hq (A : Type*) [CommRing A] (p : ℕ) [Fact p.Prime]
    (P : DSMap.PerfectoidData p A) (M : ℕ) (q : ℕ → Lam1 A p)
    (ha : ∀ j, q (j + 1) ^ p - q j ∈
      Ideal.span {algebraMap A (Lam1 A p) (P.ϖ 0 ^ (M + 1))}) (j : ℕ) :
    q (j + 1) ^ p - q j ∈ Ideal.span {wj A p P j ^ M * wj A p P 1 ^ p} := by
  have hp1 : 1 ≤ p := (Fact.out : p.Prime).one_le
  have hexp : M * (p ^ j - 1) + M = M * p ^ j := mul_pred_add_self (M := M) hp1
  have h := ha j
  rw [show algebraMap A (Lam1 A p) (P.ϖ 0 ^ (M + 1)) = wj A p P 0 ^ (M + 1) from by
    rw [map_pow]] at h
  refine (Ideal.span_singleton_le_iff_mem _).mpr ?_ h
  refine Ideal.mem_span_singleton'.mpr ⟨wj A p P j ^ (M * (p ^ j - 1)), ?_⟩
  rw [wj_root A p P 0]
  rw [← mul_assoc, ← pow_add, hexp, mul_comm M (p ^ j), pow_mul, wj_pow_zero A p P j,
    ← pow_succ]

theorem stage_hker (A : Type*) [CommRing A] (p : ℕ) [Fact p.Prime]
    (P : DSMap.PerfectoidData p A) (M : ℕ) (hM : 1 ≤ M) (q : ℕ → Lam1 A p) (t : ℕ)
    (hb : ∀ j, ∃ n : ℕ, ∃ g : Polynomial A, g.Monic ∧
      q j - Polynomial.aeval (T1 A p n) g ∈
        Ideal.span {algebraMap A (Lam1 A p) (P.ϖ (j + t))}) (j : ℕ) :
    RingHom.ker (Polynomial.aeval (R := Lam1 A p)
        (frac A p (P.ϖ 0) (num A p P M q j) M)).toRingHom =
      Ideal.span {Polynomial.C (wj A p P j ^ M) * Polynomial.X - Polynomial.C (q j)} := by
  obtain ⟨n, g, hgmonic, hgmem⟩ := hb j
  have hp1 : 1 ≤ p := (Fact.out : p.Prime).one_le
  have hπe : (algebraMap A (Lam1 A p) (P.ϖ (j + t))) ^ (M * p ^ t) = wj A p P j ^ M := by
    rw [mul_comm M (p ^ t), pow_mul, wj_pow A p P j t]
  have he : 1 ≤ M * p ^ t := Nat.mul_le_mul hM (one_le_pow₀ hp1)
  have ha : IsSMulRegular (Lam1 A p ⧸ Ideal.span {algebraMap A (Lam1 A p) (P.ϖ (j + t))})
      (Ideal.Quotient.mk (Ideal.span {algebraMap A (Lam1 A p) (P.ϖ (j + t))}) (q j)) := by
    have h1 : Ideal.Quotient.mk (Ideal.span {algebraMap A (Lam1 A p) (P.ϖ (j + t))}) (q j) =
        Ideal.Quotient.mk (Ideal.span {algebraMap A (Lam1 A p) (P.ϖ (j + t))})
          (Polynomial.aeval (T1 A p n) g) :=
      (Ideal.Quotient.eq (I := Ideal.span {algebraMap A (Lam1 A p) (P.ϖ (j + t))})).mpr hgmem
    rw [h1]
    have hI : (Ideal.span {P.ϖ (j + t)}).map (algebraMap A (Lam1 A p)) =
        Ideal.span {algebraMap A (Lam1 A p) (P.ϖ (j + t))} := by
      rw [Ideal.map_span, Set.image_singleton]
    rw [← hI]
    exact N1_monic_isSMulRegular_quot A p (Ideal.span {P.ϖ (j + t)}) n g hgmonic
  have hx' : algebraMap (Lam1 A p) (Lam1Loc A p (P.ϖ 0))
        ((algebraMap A (Lam1 A p) (P.ϖ (j + t))) ^ (M * p ^ t)) *
        frac A p (P.ϖ 0) (num A p P M q j) M =
      algebraMap (Lam1 A p) (Lam1Loc A p (P.ϖ 0)) (q j) := by
    rw [hπe]; exact stage_hx A p P M q j
  have hN3 := N3_ker_aeval (C := Lam1 A p) (L := Lam1Loc A p (P.ϖ 0))
    (Lam1Loc_algebraMap_injective A p P) (algebraMap A (Lam1 A p) (P.ϖ (j + t))) (q j)
    (M * p ^ t) he (wj_unit_L A p P (j + t)) ha (frac A p (P.ϖ 0) (num A p P M q j) M) hx'
  rwa [hπe] at hN3

theorem stage_hmono (A : Type*) [CommRing A] (p : ℕ) [Fact p.Prime]
    (P : DSMap.PerfectoidData p A) (M : ℕ) (q : ℕ → Lam1 A p)
    (ha : ∀ j, q (j + 1) ^ p - q j ∈
      Ideal.span {algebraMap A (Lam1 A p) (P.ϖ 0 ^ (M + 1))}) (j : ℕ) :
    frac A p (P.ϖ 0) (num A p P M q j) M ∈
      Algebra.adjoin (Lam1 A p) {frac A p (P.ϖ 0) (num A p P M q (j + 1)) M} := by
  have hp1 : 1 ≤ p := (Fact.out : p.Prime).one_le
  obtain ⟨b, hb⟩ := Ideal.mem_span_singleton'.mp (by
    have h := ha j
    rwa [show algebraMap A (Lam1 A p) (P.ϖ 0 ^ (M + 1)) = wj A p P 0 ^ (M + 1) from by
      rw [map_pow]] at h)
  have hMdiff : M * p - M * (p - 1) = M := mul_sub_pred (M := M) hp1
  have hk : M * (p - 1) ≤ M * p := Nat.mul_le_mul_left M (Nat.sub_le p 1)
  have hkey : frac A p (P.ϖ 0) (num A p P M q (j + 1)) M ^ p =
      frac A p (P.ϖ 0)
        ((q (j + 1) ^ p * wj A p P j ^ (M * (p ^ j - 1))) * wj A p P 0 ^ (M * (p - 1)))
        (M * p) := by
    rw [frac_eq, frac_eq, mul_pow, ← map_pow, num_pow_succ, ← pow_mul]
  have hfac : (q (j + 1) ^ p * wj A p P j ^ (M * (p ^ j - 1))) -
      (q j * wj A p P j ^ (M * (p ^ j - 1))) =
      (q (j + 1) ^ p - q j) * wj A p P j ^ (M * (p ^ j - 1)) := by ring
  have hmain : frac A p (P.ϖ 0) (num A p P M q (j + 1)) M ^ p -
      frac A p (P.ϖ 0) (num A p P M q j) M =
      algebraMap (Lam1 A p) (Lam1Loc A p (P.ϖ 0))
        (b * wj A p P 0 * wj A p P j ^ (M * (p ^ j - 1))) := by
    rw [hkey, frac_mul_wj0_pow A p P _ hk, hMdiff, frac_sub, hfac, ← hb]
    rw [show b * wj A p P 0 ^ (M + 1) * wj A p P j ^ (M * (p ^ j - 1)) =
        (b * wj A p P 0 * wj A p P j ^ (M * (p ^ j - 1))) * wj A p P 0 ^ M from by
      rw [pow_succ]; ring]
    rw [frac_mul_wj0_pow_self]
  have : frac A p (P.ϖ 0) (num A p P M q j) M =
      frac A p (P.ϖ 0) (num A p P M q (j + 1)) M ^ p -
        algebraMap (Lam1 A p) (Lam1Loc A p (P.ϖ 0))
          (b * wj A p P 0 * wj A p P j ^ (M * (p ^ j - 1))) := by
    rw [← hmain]; ring
  rw [this]
  exact Subalgebra.sub_mem _ (Subalgebra.pow_mem _ (Algebra.subset_adjoin (Set.mem_singleton _)) p)
    (Subalgebra.algebraMap_mem _ _)

theorem stage_hpow (A : Type*) [CommRing A] (p : ℕ) [Fact p.Prime]
    (P : DSMap.PerfectoidData p A) (M : ℕ) (q : ℕ → Lam1 A p)
    (ha : ∀ j, q (j + 1) ^ p - q j ∈
      Ideal.span {algebraMap A (Lam1 A p) (P.ϖ 0 ^ (M + 1))}) (j : ℕ) :
    ∃ c : Lam1 A p, frac A p (P.ϖ 0) (num A p P M q j) M ^ (p ^ j) =
      frac A p (P.ϖ 0) (num A p P M q 0) M +
        algebraMap (Lam1 A p) (Lam1Loc A p (P.ϖ 0)) c := by
  have hp1 : 1 ≤ p := (Fact.out : p.Prime).one_le
  have ha' : ∀ i, q (i + 1) ^ p - q i ∈ Ideal.span {wj A p P 0 ^ (M + 1)} := by
    intro i
    have h := ha i
    rwa [show algebraMap A (Lam1 A p) (P.ϖ 0 ^ (M + 1)) = wj A p P 0 ^ (M + 1) from by
      rw [map_pow]] at h
  have hle : Ideal.span {wj A p P 0 ^ (M + 1)} ≤ Ideal.span {wj A p P 0 ^ M} := by
    refine (Ideal.span_singleton_le_iff_mem _).mpr ?_
    exact Ideal.mem_span_singleton'.mpr ⟨wj A p P 0, by rw [pow_succ']⟩
  have hqpow : q j ^ (p ^ j) - q 0 ∈ Ideal.span {wj A p P 0 ^ M} := by
    induction j with
    | zero => rw [pow_zero, pow_one, sub_self]; exact Ideal.zero_mem _
    | succ j ih =>
      have hstep : q (j + 1) ^ (p ^ (j + 1)) - q j ^ (p ^ j) ∈
          Ideal.span {wj A p P 0 ^ (M + 1)} := by
        obtain ⟨b, hb⟩ := Ideal.mem_span_singleton'.mp (ha' j)
        obtain ⟨c, hc⟩ := sub_dvd_pow_sub_pow (q (j + 1) ^ p) (q j) (p ^ j)
        refine Ideal.mem_span_singleton'.mpr ⟨b * c, ?_⟩
        have hq1 : (q (j + 1) ^ p) ^ (p ^ j) = q (j + 1) ^ (p ^ (j + 1)) := by
          rw [← pow_mul, pow_succ']
        rw [← hq1, hc, ← hb]
        ring
      rw [show q (j + 1) ^ (p ^ (j + 1)) - q 0 =
        (q (j + 1) ^ (p ^ (j + 1)) - q j ^ (p ^ j)) + (q j ^ (p ^ j) - q 0) from by ring]
      exact Ideal.add_mem _ (hle hstep) ih
  obtain ⟨c, hc⟩ := Ideal.mem_span_singleton'.mp hqpow
  refine ⟨c, ?_⟩
  have hx0 : frac A p (P.ϖ 0) (num A p P M q 0) M = frac A p (P.ϖ 0) (q 0) M := by
    rw [num_zero]
  have hk : M * (p ^ j - 1) ≤ M * p ^ j := Nat.mul_le_mul_left M (Nat.sub_le (p ^ j) 1)
  have hkey : frac A p (P.ϖ 0) (num A p P M q j) M ^ (p ^ j) =
      frac A p (P.ϖ 0) (q j ^ (p ^ j) * wj A p P 0 ^ (M * (p ^ j - 1))) (M * p ^ j) := by
    rw [frac_eq, frac_eq, mul_pow, ← map_pow, num_pow_pow, ← pow_mul]
  have htarget : frac A p (P.ϖ 0) (q j ^ (p ^ j)) M - frac A p (P.ϖ 0) (q 0) M =
      algebraMap (Lam1 A p) (Lam1Loc A p (P.ϖ 0)) c := by
    rw [frac_sub, ← hc, frac_mul_wj0_pow_self]
  rw [hx0, hkey, frac_mul_wj0_pow A p P _ hk,
    mul_sub_pred (M := M) (p := p ^ j) (one_le_pow₀ hp1), ← htarget]
  ring

theorem stage_hdelta (A : Type*) [CommRing A] (p : ℕ) [Fact p.Prime]
    (P : DSMap.PerfectoidData p A) (F : Polynomial A) (M : ℕ) (q : ℕ → Lam1 A p)
    (N : ℕ) (hN : 0 < N)
    (hc : ∃ v ∈ Algebra.adjoin (Lam1 A p)
        {frac A p (P.ϖ 0) (Polynomial.aeval (T1 A p 0) F) M},
      frac A p (P.ϖ 0) (Polynomial.aeval (T1 A p 0) F - q 0) M ^ N =
        algebraMap A (Lam1Loc A p (P.ϖ 0)) (P.ϖ 0) * v)
    (hd : ∃ v ∈ Algebra.adjoin (Lam1 A p) {frac A p (P.ϖ 0) (q 0) M},
      frac A p (P.ϖ 0) (Polynomial.aeval (T1 A p 0) F - q 0) M ^ N =
        algebraMap A (Lam1Loc A p (P.ϖ 0)) (P.ϖ 0) * v) :
    (∃ c : Lam1 A p,
        algebraMap (Lam1 A p) (Lam1Loc A p (P.ϖ 0)) (wj A p P 0 ^ M) *
          (frac A p (P.ϖ 0) (Polynomial.aeval (T1 A p 0) F) M -
            frac A p (P.ϖ 0) (num A p P M q 0) M) =
          algebraMap (Lam1 A p) (Lam1Loc A p (P.ϖ 0)) c) ∧
      (∃ v ∈ Algebra.adjoin (Lam1 A p) {frac A p (P.ϖ 0) (Polynomial.aeval (T1 A p 0) F) M},
        (frac A p (P.ϖ 0) (Polynomial.aeval (T1 A p 0) F) M -
          frac A p (P.ϖ 0) (num A p P M q 0) M) ^ N =
          algebraMap (Lam1 A p) (Lam1Loc A p (P.ϖ 0)) (wj A p P 0) * v) ∧
      (∃ v ∈ Algebra.adjoin (Lam1 A p) {frac A p (P.ϖ 0) (num A p P M q 0) M},
        (frac A p (P.ϖ 0) (Polynomial.aeval (T1 A p 0) F) M -
          frac A p (P.ϖ 0) (num A p P M q 0) M) ^ N =
          algebraMap (Lam1 A p) (Lam1Loc A p (P.ϖ 0)) (wj A p P 0) * v) := by
  have hy0 : frac A p (P.ϖ 0) (Polynomial.aeval (T1 A p 0) F) M -
      frac A p (P.ϖ 0) (num A p P M q 0) M =
      frac A p (P.ϖ 0) (Polynomial.aeval (T1 A p 0) F - q 0) M := by
    rw [num_zero, frac_sub]
  have hx0 : frac A p (P.ϖ 0) (num A p P M q 0) M = frac A p (P.ϖ 0) (q 0) M := by
    rw [num_zero]
  have hmap : algebraMap (Lam1 A p) (Lam1Loc A p (P.ϖ 0)) (wj A p P 0) =
      algebraMap A (Lam1Loc A p (P.ϖ 0)) (P.ϖ 0) :=
    (IsScalarTower.algebraMap_apply A (Lam1 A p) (Lam1Loc A p (P.ϖ 0)) (P.ϖ 0)).symm
  refine ⟨⟨Polynomial.aeval (T1 A p 0) F - q 0, ?_⟩, ?_, ?_⟩
  · rw [hy0, algebraMap_varpi_mul_frac]
  · obtain ⟨v, hv, hve⟩ := hc
    exact ⟨v, hv, by rw [hy0, hmap]; exact hve⟩
  · obtain ⟨v, hv, hve⟩ := hd
    exact ⟨v, by rwa [← hx0] at hv, by rw [hy0, hmap]; exact hve⟩


/-! ## The `A`-algebra structures on the stages and on the union -/

noncomputable instance stageInstAlgebra (A : Type*) [CommRing A] (p : ℕ)
    (P : DSMap.PerfectoidData p A) (F : Polynomial A) (M : ℕ) :
    Algebra A ↥(pIntClosure p ((Algebra.adjoin (Lam1 A p) {yF A p P F M}).toSubring)) :=
  (RingHom.codRestrict (AAlgHomLamOne A p (P.ϖ 0)) _
    (fun a => le_pIntClosure p _
      (Subalgebra.mem_toSubring.2
        (Subalgebra.algebraMap_mem _ (algebraMap A (Lam1 A p) a))))).toAlgebra

noncomputable instance stageSupInstAlgebra (A : Type*) [CommRing A] (p : ℕ)
    (P : DSMap.PerfectoidData p A) (F : Polynomial A) :
    Algebra A ↥(⨆ m : ℕ, pIntClosure p
      ((Algebra.adjoin (Lam1 A p) {yF A p P F (m + 1)}).toSubring)) :=
  (RingHom.codRestrict (AAlgHomLamOne A p (P.ϖ 0)) _
    (fun a => le_iSup (fun m : ℕ => pIntClosure p
        ((Algebra.adjoin (Lam1 A p) {yF A p P F (m + 1)}).toSubring)) 0
      (le_pIntClosure p _
        (Subalgebra.mem_toSubring.2
          (Subalgebra.algebraMap_mem _ (algebraMap A (Lam1 A p) a)))))).toAlgebra

/-- `yF M = yF (M+1) · ϖ₀`. -/
theorem yF_succ (A : Type*) [CommRing A] (p : ℕ) (P : DSMap.PerfectoidData p A)
    (F : Polynomial A) (M : ℕ) :
    yF A p P F M = yF A p P F (M + 1) *
      algebraMap (Lam1 A p) (Lam1Loc A p (P.ϖ 0)) (wj A p P 0) := by
  have hkey : V0 A p P ^ (M + 1) *
      algebraMap (Lam1 A p) (Lam1Loc A p (P.ϖ 0)) (wj A p P 0) = V0 A p P ^ M := by
    rw [pow_succ, mul_assoc,
      mul_comm (V0 A p P) (algebraMap (Lam1 A p) (Lam1Loc A p (P.ϖ 0)) (wj A p P 0))]
    rw [show algebraMap (Lam1 A p) (Lam1Loc A p (P.ϖ 0)) (wj A p P 0) * V0 A p P = 1 from by
      rw [show V0 A p P =
        IsLocalization.Away.invSelf (algebraMap A (Lam1 A p) (P.ϖ 0)) from rfl]
      exact IsLocalization.Away.mul_invSelf _]
    rw [mul_one]
  show frac A p (P.ϖ 0) (Polynomial.aeval (T1 A p 0) F) M =
    frac A p (P.ϖ 0) (Polynomial.aeval (T1 A p 0) F) (M + 1) *
      algebraMap (Lam1 A p) (Lam1Loc A p (P.ϖ 0)) (wj A p P 0)
  rw [frac_eq, frac_eq, mul_assoc, hkey]

/-! ## The per-`M` flatness statement -/

theorem N8_stage_flat (A : Type*) [CommRing A] (p : ℕ) [Fact p.Prime]
    (P : DSMap.PerfectoidData p A) (F : Polynomial A) (hF : F.Monic) (M : ℕ) (hM : 1 ≤ M) :
    Module.Flat A ↥(pIntClosure p
      ((Algebra.adjoin (Lam1 A p) {yF A p P F M}).toSubring)) := by
  classical
  obtain ⟨q, t, N, hN, ha, hb, hc, hd⟩ := N5_AAL_Lam A p P F hF M hM
  have hx' : ∀ j, frac A p (P.ϖ 0) (num A p P M q j) M ∈ Algebra.adjoin (Lam1 A p)
      {frac A p (P.ϖ 0) (num A p P M q (j + 1)) M} := fun j => stage_hmono A p P M q ha j
  have hker : ∀ j, RingHom.ker (Polynomial.aeval (R := Lam1 A p)
      (frac A p (P.ϖ 0) (num A p P M q j) M)).toRingHom =
      Ideal.span {Polynomial.C (wj A p P j ^ M) * Polynomial.X - Polynomial.C (q j)} :=
    fun j => stage_hker A p P M hM q t hb j
  have hflat : ∀ j, Module.Flat A (Polynomial (Lam1 A p) ⧸ Ideal.span
      {Polynomial.C (wj A p P j ^ M) * Polynomial.X - Polynomial.C (q j)}) := by
    intro j
    obtain ⟨n, g, hgmonic, hgmem⟩ := hb j
    have hπe : (algebraMap A (Lam1 A p) (P.ϖ (j + t))) ^ (M * p ^ t) = wj A p P j ^ M := by
      rw [mul_comm M (p ^ t), pow_mul, wj_pow A p P j t]
    have h := N2b_flat_presentation A p (P.ϖ (j + t)) (M * p ^ t) (q j) n g hgmonic hgmem
    rw [← hπe]
    exact h
  have hpw : (p : Lam1 A p) ∈ Ideal.span {wj A p P 1 ^ p} := by
    rw [wj_root A p P 0]; exact p_mem_wj0 A p P
  have hsurjw : ∀ c : Lam1 A p, ∃ b : Lam1 A p, c - b ^ p ∈ Ideal.span {wj A p P 1 ^ p} := by
    intro c
    obtain ⟨b, hb'⟩ := Lam1_frobSurj_wj0 A p P c
    exact ⟨b, by rw [wj_root A p P 0]; exact hb'⟩
  have hU : IsPIntegrallyClosedIn p
      (⨆ j, (Algebra.adjoin (Lam1 A p)
        {frac A p (P.ϖ 0) (num A p P M q j) M}).toSubring) :=
    N4P_isPIntegrallyClosed_iSup p (Lam1Loc_algebraMap_injective A p P) (wj A p P 1)
      (wj_unit_L A p P 1) (hgen_L A p P) hpw hsurjw
      (fun b hb' => frobInj_wj1 A p P hb') (fun j => wj A p P j ^ M) q
      (fun j => frac A p (P.ϖ 0) (num A p P M q j) M)
      (fun j => stage_hs A p P M j) (fun j => stage_hsL A p P M j)
      (fun j => stage_hx A p P M q j) (fun j => stage_hq A p P M q ha j) hker
  obtain ⟨hδs, hδy, hδx⟩ := stage_hdelta A p P F M q N hN hc hd
  have hN6 : pIntClosure p ((Algebra.adjoin (Lam1 A p) {yF A p P F M}).toSubring) =
      ⨆ j, (Algebra.adjoin (Lam1 A p)
        {frac A p (P.ϖ 0) (num A p P M q j) M}).toSubring :=
    N6_pIntClosure_eq p (wj A p P 0) (fun j => frac A p (P.ϖ 0) (num A p P M q j) M)
      (frac A p (P.ϖ 0) (Polynomial.aeval (T1 A p 0) F) M) hU
      (fun j => stage_hmono A p P M q ha j) (fun j => stage_hpow A p P M q ha j)
      M N hN hδs hδy hδx
  have hsupSub : Module.Flat A ↥(⨆ j, Algebra.adjoin (Lam1 A p)
      {frac A p (P.ϖ 0) (num A p P M q j) M}) :=
    N7_flat_iSup_adjoin (fun j => frac A p (P.ϖ 0) (num A p P M q j) M) hx'
      (fun j => Polynomial.C (wj A p P j ^ M) * Polynomial.X - Polynomial.C (q j)) hker hflat
  have hEq : (⨆ j, Algebra.adjoin (Lam1 A p)
        {frac A p (P.ϖ 0) (num A p P M q j) M}).toSubring =
      ⨆ j, (Algebra.adjoin (Lam1 A p)
        {frac A p (P.ϖ 0) (num A p P M q j) M}).toSubring :=
    N7b_toSubring_iSup _ hx'
  have hN6eq : pIntClosure p ((Algebra.adjoin (Lam1 A p) {yF A p P F M}).toSubring) =
      (⨆ j, Algebra.adjoin (Lam1 A p)
        {frac A p (P.ϖ 0) (num A p P M q j) M}).toSubring := hN6.trans hEq.symm
  haveI : Module.Flat A ↥(⨆ j, Algebra.adjoin (Lam1 A p)
      {frac A p (P.ϖ 0) (num A p P M q j) M}) := hsupSub
  have hTalg : ∀ a : A, ((algebraMap A ↥(pIntClosure p
      ((Algebra.adjoin (Lam1 A p) {yF A p P F M}).toSubring)) a :
        ↥(pIntClosure p ((Algebra.adjoin (Lam1 A p) {yF A p P F M}).toSubring))) :
      Lam1Loc A p (P.ϖ 0)) =
      algebraMap (Lam1 A p) (Lam1Loc A p (P.ϖ 0)) (algebraMap A (Lam1 A p) a) := fun a => rfl
  have hmemT : ∀ z : ↥(⨆ j, Algebra.adjoin (Lam1 A p)
        {frac A p (P.ϖ 0) (num A p P M q j) M}),
      ((z : Lam1Loc A p (P.ϖ 0)) ∈
        pIntClosure p ((Algebra.adjoin (Lam1 A p) {yF A p P F M}).toSubring)) :=
    fun z => le_of_eq hN6eq.symm (Subalgebra.mem_toSubring.2 z.2)
  have hmemS : ∀ z : ↥(pIntClosure p ((Algebra.adjoin (Lam1 A p) {yF A p P F M}).toSubring)),
      ((z : Lam1Loc A p (P.ϖ 0)) ∈ ⨆ j, Algebra.adjoin (Lam1 A p)
        {frac A p (P.ϖ 0) (num A p P M q j) M}) :=
    fun z => Subalgebra.mem_toSubring.1 (le_of_eq hN6eq z.2)
  let toF : ↥(⨆ j, Algebra.adjoin (Lam1 A p)
        {frac A p (P.ϖ 0) (num A p P M q j) M}) →
      ↥(pIntClosure p ((Algebra.adjoin (Lam1 A p) {yF A p P F M}).toSubring)) :=
    fun z => Subtype.mk (z : Lam1Loc A p (P.ϖ 0)) (hmemT z)
  let invF : ↥(pIntClosure p ((Algebra.adjoin (Lam1 A p) {yF A p P F M}).toSubring)) →
      ↥(⨆ j, Algebra.adjoin (Lam1 A p)
        {frac A p (P.ϖ 0) (num A p P M q j) M}) :=
    fun z => Subtype.mk (z : Lam1Loc A p (P.ϖ 0)) (hmemS z)
  have hsmul : ∀ (a : A) (z : ↥(⨆ j, Algebra.adjoin (Lam1 A p)
        {frac A p (P.ϖ 0) (num A p P M q j) M})),
      ((a • z : ↥(⨆ j, Algebra.adjoin (Lam1 A p)
        {frac A p (P.ϖ 0) (num A p P M q j) M})) : Lam1Loc A p (P.ϖ 0)) =
      ((a • toF z : ↥(pIntClosure p
        ((Algebra.adjoin (Lam1 A p) {yF A p P F M}).toSubring))) : Lam1Loc A p (P.ϖ 0)) := by
    intro a z
    rw [Algebra.smul_def, Algebra.smul_def]
    show (algebraMap A ↥(⨆ j, Algebra.adjoin (Lam1 A p)
            {frac A p (P.ϖ 0) (num A p P M q j) M}) a : Lam1Loc A p (P.ϖ 0)) *
          (z : Lam1Loc A p (P.ϖ 0)) =
        (algebraMap (Lam1 A p) (Lam1Loc A p (P.ϖ 0))
          (algebraMap A (Lam1 A p) a)) * (z : Lam1Loc A p (P.ϖ 0))
    rw [Subalgebra.coe_algebraMap,
      IsScalarTower.algebraMap_apply A (Lam1 A p) (Lam1Loc A p (P.ϖ 0))]
  let e : ↥(⨆ j, Algebra.adjoin (Lam1 A p)
        {frac A p (P.ϖ 0) (num A p P M q j) M}) ≃ₗ[A]
      ↥(pIntClosure p ((Algebra.adjoin (Lam1 A p) {yF A p P F M}).toSubring)) :=
    show ↥(⨆ j, Algebra.adjoin (Lam1 A p)
          {frac A p (P.ϖ 0) (num A p P M q j) M}) ≃ₗ[A]
        ↥(pIntClosure p ((Algebra.adjoin (Lam1 A p) {yF A p P F M}).toSubring)) from
      { toFun := toF, invFun := invF, left_inv := fun _ => Subtype.ext rfl,
        right_inv := fun _ => Subtype.ext rfl, map_add' := fun _ _ => Subtype.ext rfl,
        map_smul' := fun a z => Subtype.ext (hsmul a z) }
  exact Module.Flat.of_linearEquiv e.symm

end Work.DSM2p
