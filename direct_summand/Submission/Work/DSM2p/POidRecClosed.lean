import Submission.Work.DSM2p.POidRec

open scoped Classical

namespace Work.DSM2p

universe u

variable {p : ℕ} [Fact p.Prime] {A : Type u} [CommRing A] {P : DSMap.PerfectoidData p A}

/-! ## The union of the tower is `p`-integrally closed in `T` -/

/-- Every element of `T = Λ[1/ϖ]` is `λ · ϖ ^ (-n)` with `λ ∈ Λ`. -/
theorem exists_lambda_iT_pow (y : RootAlgLocPos A p (P.ϖ 0)) :
    ∃ (n : ℕ) (lam : RootAlgPos A p),
      y = algebraMap (RootAlgPos A p) (RootAlgLocPos A p (P.ϖ 0)) lam
        * iT (p := p) (A := A) (P := P) ^ n := by
  obtain ⟨n, a, ha⟩ := IsLocalization.Away.surj (R := RootAlgPos A p)
    (S := RootAlgLocPos A p (P.ϖ 0)) (x := algebraMap A (RootAlgPos A p) (P.ϖ 0)) y
  refine ⟨n, a, ?_⟩
  have hmapψ : algebraMap (RootAlgPos A p) (RootAlgLocPos A p (P.ϖ 0))
        (algebraMap A (RootAlgPos A p) (P.ϖ 0)) = psi (p := p) (A := A) (P := P) 0 := rfl
  have hx1 : (algebraMap (RootAlgPos A p) (RootAlgLocPos A p (P.ϖ 0))
        (algebraMap A (RootAlgPos A p) (P.ϖ 0))) ^ n * iT (p := p) (A := A) (P := P) ^ n = 1 := by
    rw [← mul_pow, hmapψ, vT_mul_iT (p := p) (A := A) (P := P), one_pow]
  calc y = y * 1 := (mul_one y).symm
    _ = y * ((algebraMap (RootAlgPos A p) (RootAlgLocPos A p (P.ϖ 0))
          (algebraMap A (RootAlgPos A p) (P.ϖ 0))) ^ n * iT ^ n) := by rw [hx1]
    _ = (y * (algebraMap (RootAlgPos A p) (RootAlgLocPos A p (P.ϖ 0))
          (algebraMap A (RootAlgPos A p) (P.ϖ 0))) ^ n) * iT ^ n := by ring
    _ = algebraMap (RootAlgPos A p) (RootAlgLocPos A p (P.ϖ 0)) a * iT ^ n := by rw [ha]

/-- The division step for the union: `a ∈ ⋃Rᵢ` with `a ^ p = ϖ ^ p * c`, `c ∈ ⋃Rᵢ`, gives
`a / ϖ = a · iT ∈ ⋃Rᵢ`. -/
theorem mul_iT_mem_csTowerSup {a c : RootAlgLocPos A p (P.ϖ 0)}
    (ha : a ∈ csTowerSup (p := p) (A := A) (P := P))
    (hc : c ∈ csTowerSup (p := p) (A := A) (P := P))
    (h : a ^ p = (psi (p := p) (A := A) (P := P) 0) ^ p * c) :
    a * iT ∈ csTowerSup (p := p) (A := A) (P := P) := by
  obtain ⟨i, hi⟩ := ha
  obtain ⟨j, hj⟩ := hc
  exact ⟨max i j + 1, mul_iT_mem_csTower_succ
    (csTower_mono (le_max_left i j) hi) (csTower_mono (le_max_right i j) hj) h⟩

theorem mul_iT_pow_mul (a : RootAlgLocPos A p (P.ϖ 0)) (n : ℕ) :
    (a * iT ^ n) ^ p * (psi (p := p) (A := A) (P := P) 0) ^ (p * n) = a ^ p := by
  have hpow : iT (p := p) (A := A) (P := P) ^ n
      * (psi (p := p) (A := A) (P := P) 0) ^ n = 1 := by
    rw [← mul_pow, iT_mul_vT (p := p) (A := A) (P := P), one_pow]
  calc (a * iT ^ n) ^ p * (psi 0) ^ (p * n)
      = (a * iT ^ n) ^ p * ((psi 0) ^ n) ^ p := by rw [mul_comm p n, pow_mul]
    _ = (a * iT ^ n * (psi 0) ^ n) ^ p := by rw [← mul_pow]
    _ = (a * (iT ^ n * (psi 0) ^ n)) ^ p := by rw [mul_assoc]
    _ = a ^ p := by rw [hpow, mul_one]

/-- **The union of the tower is `p`-integrally closed in `T`** (Česnavičius–Scholze
`p-oid-rec`: the injectivity half is built into the construction, and the `p`-integral
closedness in the fraction ring follows by descending along the `ϖ`-adic valuation, using
`T = ⋃_n Λ · ϖ ^ (-n)`). -/
theorem isPIntegrallyClosedIn_csTowerSup :
    IsPIntegrallyClosedIn p (csTowerSup (p := p) (A := A) (P := P)) := by
  have hψ : (psi (p := p) (A := A) (P := P) 0) ∈ csTowerSup (p := p) (A := A) (P := P) :=
    csTower_zero_le_csTowerSup (psi_mem_CSAlgPos 0)
  have key : ∀ n (a : RootAlgLocPos A p (P.ϖ 0)),
      a ∈ csTowerSup (p := p) (A := A) (P := P) →
      (a * iT ^ n) ^ p ∈ csTowerSup (p := p) (A := A) (P := P) →
      a * iT ^ n ∈ csTowerSup (p := p) (A := A) (P := P) := by
    intro n
    induction n with
    | zero => intro a ha _; simpa using ha
    | succ k ih =>
      intro a ha hp
      have hap : a ^ p = (psi (p := p) (A := A) (P := P) 0) ^ p
          * ((a * iT ^ (k + 1)) ^ p * (psi (p := p) (A := A) (P := P) 0) ^ (p * k)) := by
        rw [← mul_iT_pow_mul (p := p) (A := A) (P := P) a (k + 1)]
        rw [show p * (k + 1) = p + p * k by ring, pow_add]
        ring
      have hcof : (a * iT ^ (k + 1)) ^ p
          * (psi (p := p) (A := A) (P := P) 0) ^ (p * k)
          ∈ csTowerSup (p := p) (A := A) (P := P) :=
        mul_mem hp (csTower_zero_le_csTowerSup (pow_mem (psi_mem_CSAlgPos 0) (p * k)))
      rw [show a * iT ^ (k + 1) = a * iT * iT ^ k by rw [mul_assoc, ← pow_succ']]
      exact ih (a * iT) (mul_iT_mem_csTowerSup ha hcof hap)
        (by rw [mul_assoc, ← pow_succ']; exact hp)
  intro x hx
  obtain ⟨n, lam, hlam⟩ := exists_lambda_iT_pow (p := p) (A := A) (P := P) x
  have hla : algebraMap (RootAlgPos A p) (RootAlgLocPos A p (P.ϖ 0)) lam
      ∈ csTowerSup (p := p) (A := A) (P := P) :=
    csTower_zero_le_csTowerSup (Subring.subset_closure (Set.mem_union_left _ ⟨lam, rfl⟩))
  rw [hlam]
  refine key n (algebraMap (RootAlgPos A p) (RootAlgLocPos A p (P.ϖ 0)) lam) hla ?_
  rwa [← hlam]

/-! ## The union of the tower *is* the `p`-integral closure of `A_∞` -/

/-- The easy inclusion: every generator of the tower is an iterated `p`-th root of an element
of a lower level, hence lies in the `p`-integral closure `A'` of `A_∞`. -/
theorem csTowerSup_le_CSIntegralClosurePos :
    csTowerSup (p := p) (A := A) (P := P) ≤ CSIntegralClosurePos A p (P.ϖ 0) := by
  have hA' : IsPIntegrallyClosedIn p (CSIntegralClosurePos A p (P.ϖ 0)) :=
    CSIntegralClosurePos_isPIntegrallyClosed A p (P.ϖ 0)
  have key : ∀ i, csTower (p := p) (A := A) (P := P) i ≤ CSIntegralClosurePos A p (P.ϖ 0) := by
    intro i
    induction i with
    | zero => exact CSAlgPos_le_CSIntegralClosurePos A p (P.ϖ 0)
    | succ k ih =>
      rw [csTower_succ]
      refine sup_le ih ?_
      refine Subring.closure_le.mpr ?_
      rintro w ⟨v, hv, m, ⟨e, he, hve⟩, rfl⟩
      exact mem_of_pow_pow_mem hA' _ (m + 1) (by rw [mul_uPi_pow hve]; exact ih he)
  rintro x ⟨i, hi⟩
  exact key i hi

/-- **`A' = ⋃ Rᵢ`**: the union of the Česnavičius–Scholze tower is exactly the `p`-integral
closure of `A_∞` in `T`. -/
theorem csTowerSup_eq_CSIntegralClosurePos :
    csTowerSup (p := p) (A := A) (P := P) = CSIntegralClosurePos A p (P.ϖ 0) :=
  le_antisymm csTowerSup_le_CSIntegralClosurePos
    (pIntClosure_le csTower_zero_le_csTowerSup isPIntegrallyClosedIn_csTowerSup)

end Work.DSM2p
