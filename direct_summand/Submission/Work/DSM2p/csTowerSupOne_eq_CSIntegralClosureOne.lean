import Mathlib
import Submission.Work.DSM2p.POidRecOne
import Submission.Work.DSM2p.One
import Submission.Work.DSM2p.LamOne

/-!
# DSM2p — the union of the one-polynomial Česnavičius–Scholze tower is the
`p`-integral closure `A'_F`

This file transcribes `Submission/Work/DSM2p/POidRecClosed.lean` (the multi-variable statement
`csTowerSup_eq_CSIntegralClosurePos`) to the one-polynomial situation of
`Submission/Work/DSM2p/POidRecOne.lean` / `One.lean`:

`csTowerSupOne F = CSIntegralClosureOne A p (P.ϖ 0) F`, i.e. the union `⋃ᵢ Rᵢ` of the tower
`R₀ = A_∞ = CSAlgOne A p ϖ F`, `Rᵢ₊₁ = Rᵢ[csGenOne F Rᵢ]` is exactly `pIntClosure p A_∞`.

The two halves are:

* `csTowerSupOne_le_CSIntegralClosureOne` — every generator of a tower step is an iterated
  `p`-th root of an element of the previous level (`mul_uPiOne_pow`), hence belongs to the
  `p`-integral closure, which is `p`-integrally closed;
* `isPIntegrallyClosedIn_csTowerSupOne` — the union is `p`-integrally closed: writing an
  arbitrary `x ∈ T = Λ[1/ϖ]` as `λ · ϖ^{-n}` (`exists_lambda_iTOne_pow`) one descends along the
  `ϖ`-adic valuation using the division step `mul_iTOne_mem_csTowerSupOne`.

The target then follows from `pIntClosure_le` (minimality of the `p`-integral closure).
-/

open scoped Classical

namespace Work.DSM2p

universe u

variable {p : ℕ} [Fact p.Prime] {A : Type u} [CommRing A] {P : DSMap.PerfectoidData p A}

/-! ## The union of the tower is `p`-integrally closed in `T = Λ[1/ϖ]` -/

/-- Every element of `T = Λ[1/ϖ]` is `λ · ϖ ^ (-n)` with `λ ∈ Λ`. -/
theorem exists_lambda_iTOne_pow (y : Lam1Loc A p (P.ϖ 0)) :
    ∃ (n : ℕ) (lam : Lam1 A p),
      y = algebraMap (Lam1 A p) (Lam1Loc A p (P.ϖ 0)) lam
        * iTOne (p := p) (A := A) (P := P) ^ n := by
  obtain ⟨n, a, ha⟩ := IsLocalization.Away.surj (R := Lam1 A p)
    (S := Lam1Loc A p (P.ϖ 0)) (x := algebraMap A (Lam1 A p) (P.ϖ 0)) y
  refine ⟨n, a, ?_⟩
  have hmapψ : algebraMap (Lam1 A p) (Lam1Loc A p (P.ϖ 0))
        (algebraMap A (Lam1 A p) (P.ϖ 0)) = psiOne (p := p) (A := A) (P := P) 0 := rfl
  have hx1 : (algebraMap (Lam1 A p) (Lam1Loc A p (P.ϖ 0))
        (algebraMap A (Lam1 A p) (P.ϖ 0))) ^ n * iTOne (p := p) (A := A) (P := P) ^ n = 1 := by
    rw [← mul_pow, hmapψ, vT_mul_iTOne (p := p) (A := A) (P := P), one_pow]
  calc y = y * 1 := (mul_one y).symm
    _ = y * ((algebraMap (Lam1 A p) (Lam1Loc A p (P.ϖ 0))
          (algebraMap A (Lam1 A p) (P.ϖ 0))) ^ n * iTOne ^ n) := by rw [hx1]
    _ = (y * (algebraMap (Lam1 A p) (Lam1Loc A p (P.ϖ 0))
          (algebraMap A (Lam1 A p) (P.ϖ 0))) ^ n) * iTOne ^ n := by ring
    _ = algebraMap (Lam1 A p) (Lam1Loc A p (P.ϖ 0)) a * iTOne ^ n := by rw [ha]

/-- The division step for the union: `a ∈ ⋃Rᵢ` with `a ^ p = ϖ ^ p * c`, `c ∈ ⋃Rᵢ`, gives
`a / ϖ = a · iTOne ∈ ⋃Rᵢ`. -/
theorem mul_iTOne_mem_csTowerSupOne {F : Polynomial A} {a c : Lam1Loc A p (P.ϖ 0)}
    (ha : a ∈ csTowerSupOne (p := p) (A := A) (P := P) F)
    (hc : c ∈ csTowerSupOne (p := p) (A := A) (P := P) F)
    (h : a ^ p = (psiOne (p := p) (A := A) (P := P) 0) ^ p * c) :
    a * iTOne ∈ csTowerSupOne (p := p) (A := A) (P := P) F := by
  obtain ⟨i, hi⟩ := ha
  obtain ⟨j, hj⟩ := hc
  exact ⟨max i j + 1, mul_iTOne_mem_csTowerOne_succ
    (csTowerOne_mono F (le_max_left i j) hi) (csTowerOne_mono F (le_max_right i j) hj) h⟩

theorem mul_iTOne_pow_mul (a : Lam1Loc A p (P.ϖ 0)) (n : ℕ) :
    (a * iTOne (p := p) (A := A) (P := P) ^ n) ^ p
      * (psiOne (p := p) (A := A) (P := P) 0) ^ (p * n) = a ^ p := by
  have hpow : iTOne (p := p) (A := A) (P := P) ^ n
      * (psiOne (p := p) (A := A) (P := P) 0) ^ n = 1 := by
    rw [← mul_pow, iTOne_mul_vT (p := p) (A := A) (P := P), one_pow]
  calc (a * iTOne ^ n) ^ p * (psiOne 0) ^ (p * n)
      = (a * iTOne ^ n) ^ p * ((psiOne 0) ^ n) ^ p := by rw [mul_comm p n, pow_mul]
    _ = (a * iTOne ^ n * (psiOne 0) ^ n) ^ p := by rw [← mul_pow]
    _ = (a * (iTOne ^ n * (psiOne 0) ^ n)) ^ p := by rw [mul_assoc]
    _ = a ^ p := by rw [hpow, mul_one]

/-- **The union of the tower is `p`-integrally closed in `T`** (Česnavičius–Scholze
`p-oid-rec`: the injectivity half is built into the construction, and the `p`-integral
closedness in the fraction ring follows by descending along the `ϖ`-adic valuation, using
`T = ⋃_n Λ · ϖ ^ (-n)`). -/
theorem isPIntegrallyClosedIn_csTowerSupOne (F : Polynomial A) :
    IsPIntegrallyClosedIn p (csTowerSupOne (p := p) (A := A) (P := P) F) := by
  have hψ : (psiOne (p := p) (A := A) (P := P) 0) ∈ csTowerSupOne (p := p) (A := A) (P := P) F :=
    csTowerOne_zero_le_csTowerSupOne F (psiOne_mem_CSAlgOne F 0)
  have key : ∀ n (a : Lam1Loc A p (P.ϖ 0)),
      a ∈ csTowerSupOne (p := p) (A := A) (P := P) F →
      (a * iTOne ^ n) ^ p ∈ csTowerSupOne (p := p) (A := A) (P := P) F →
      a * iTOne ^ n ∈ csTowerSupOne (p := p) (A := A) (P := P) F := by
    intro n
    induction n with
    | zero => intro a ha _; simpa using ha
    | succ k ih =>
      intro a ha hp
      have hap : a ^ p = (psiOne (p := p) (A := A) (P := P) 0) ^ p
          * ((a * iTOne ^ (k + 1)) ^ p * (psiOne (p := p) (A := A) (P := P) 0) ^ (p * k)) := by
        rw [← mul_iTOne_pow_mul (p := p) (A := A) (P := P) a (k + 1)]
        rw [show p * (k + 1) = p + p * k by ring, pow_add]
        ring
      have hcof : (a * iTOne ^ (k + 1)) ^ p
          * (psiOne (p := p) (A := A) (P := P) 0) ^ (p * k)
          ∈ csTowerSupOne (p := p) (A := A) (P := P) F :=
        mul_mem hp (csTowerOne_zero_le_csTowerSupOne F
          (pow_mem (psiOne_mem_CSAlgOne F 0) (p * k)))
      rw [show a * iTOne ^ (k + 1) = a * iTOne * iTOne ^ k by rw [mul_assoc, ← pow_succ']]
      exact ih (a * iTOne) (mul_iTOne_mem_csTowerSupOne ha hcof hap)
        (by rw [mul_assoc, ← pow_succ']; exact hp)
  intro x hx
  obtain ⟨n, lam, hlam⟩ := exists_lambda_iTOne_pow (p := p) (A := A) (P := P) x
  have hla : algebraMap (Lam1 A p) (Lam1Loc A p (P.ϖ 0)) lam
      ∈ csTowerSupOne (p := p) (A := A) (P := P) F :=
    csTowerOne_zero_le_csTowerSupOne F
      (Subring.subset_closure (Set.mem_union_left _ ⟨lam, rfl⟩))
  rw [hlam]
  refine key n (algebraMap (Lam1 A p) (Lam1Loc A p (P.ϖ 0)) lam) hla ?_
  rwa [← hlam]

/-! ## The union of the tower *is* the `p`-integral closure of `A_∞` -/

/-- The easy inclusion: every generator of the tower is an iterated `p`-th root of an element
of a lower level, hence lies in the `p`-integral closure `A'_F` of `A_∞`. -/
theorem csTowerSupOne_le_CSIntegralClosureOne (F : Polynomial A) :
    csTowerSupOne (p := p) (A := A) (P := P) F
      ≤ CSIntegralClosureOne A p (P.ϖ 0) F := by
  have hA' : IsPIntegrallyClosedIn p (CSIntegralClosureOne A p (P.ϖ 0) F) :=
    CSIntegralClosureOne_isPIntegrallyClosed A p (P.ϖ 0) F
  have key : ∀ i, csTowerOne (p := p) (A := A) (P := P) F i
      ≤ CSIntegralClosureOne A p (P.ϖ 0) F := by
    intro i
    induction i with
    | zero => exact CSAlgOne_le_CSIntegralClosureOne A p (P.ϖ 0) F
    | succ k ih =>
      rw [csTowerOne_succ]
      refine sup_le ih ?_
      refine Subring.closure_le.mpr ?_
      rintro w ⟨v, hv, m, ⟨e, he, hve⟩, rfl⟩
      exact mem_of_pow_pow_memOne (F := F) hA' _ (m + 1)
        (by rw [mul_uPiOne_pow (F := F) hve]; exact ih he)
  rintro x ⟨i, hi⟩
  exact key i hi

/-! ## The target -/

theorem csTowerSupOne_eq_CSIntegralClosureOne (A : Type*) [CommRing A] (p : ℕ) [Fact p.Prime]
    (P : DSMap.PerfectoidData p A) (F : Polynomial A) :
    csTowerSupOne (p := p) (A := A) (P := P) F = CSIntegralClosureOne A p (P.ϖ 0) F :=
  le_antisymm (csTowerSupOne_le_CSIntegralClosureOne F)
    (pIntClosure_le (csTowerOne_zero_le_csTowerSupOne F) (isPIntegrallyClosedIn_csTowerSupOne F))

end Work.DSM2p
