import Mathlib
import Submission.Work.DSM2p.LamOne
import Submission.Work.DSM2p.frobSurj_rootClosurePos
import Submission.Work.DSM2p.exists_mul_of_pow_mem
import Submission.Work.DSM2p.sum_pow_sub_mem
import Submission.Work.DSM2p.crossTerm_mem

/-!
# DSM2p — Česnavičius–Scholze `p-oid-rec`, the one-polynomial (`Λ = A[T^{1/p^∞}]`) case

This is the one-variable counterpart of `Submission/Work/DSM2p/POidRec.lean`: the tower of
Česnavičius–Scholze (`p-oid-rec`, arXiv:1912.10932, §"`p`-integral closedness of perfectoid
rings") built inside the ambient ring

`L = Λ[1/ϖ] = Lam1Loc A p (P.ϖ 0)`,  where `Λ = Lam1 A p = A[T^{1/p^∞}]` and `ϖ = P.ϖ 0`,

with the starting subring `A_∞ := CSAlgOne A p ϖ F` and target `A'_F = pIntClosure p A_∞`.

The statements and proofs are verbatim transcriptions of the multi-variable version, with
`RootAlgPos A p` replaced by `Lam1 A p = rootClosure A p PUnit`, `RootAlgLocPos A p ϖ` by
`Lam1Loc A p ϖ`, `CSAlgPos A p ϖ` by `CSAlgOne A p ϖ F` and `AAlgHomLocPos` by
`AAlgHomLamOne`; every name is suffixed with `One` so that the two developments coexist.

`R` is *Frobenius-surjective modulo `ϖ ^ p`* if every `x ∈ R` differs from a `p`-th power of
an element of `R` by a multiple of `ϖ ^ p` **whose cofactor lies in `R`** (or in `R ⊔ A_∞`):

`∃ y ∈ R, ∃ c ∈ R, x - y ^ p = ϖ ^ p * c`.

The next level of the tower from `R` adjoins the quotients `v / ϖ ^{1/p^m} = v * uPiOne m` for
`v ∈ R` with `v ^{p ^ (m + 1)} = ϖ ^ p * e`, `e ∈ R`; here `π n := ϖ ^{1/p^n} ∈ Λ` (`psiOne n`)
and `uPiOne n := (π n)⁻¹`.
-/

open scoped Classical

namespace Work.DSM2p

universe u

variable {p : ℕ} [Fact p.Prime] {A : Type u} [CommRing A] {P : DSMap.PerfectoidData p A}

/-! ## The structure map and the `ϖ`-roots inside `L = Λ[1/ϖ]` -/

set_option maxHeartbeats 1600000 in
/-- The structure map `Λ → Λ[1/ϖ]`, as an explicit ring hom: using this instead of the
`algebraMap` term keeps the elaboration of later proofs cheap. -/
noncomputable def iΛTOne (A : Type u) [CommRing A] (p : ℕ) (ϖ : A) : Lam1 A p →+* Lam1Loc A p ϖ :=
  algebraMap (Lam1 A p) (Lam1Loc A p ϖ)

theorem iΛTOne_apply (A : Type u) [CommRing A] (p : ℕ) (ϖ : A) (l : Lam1 A p) :
    iΛTOne A p ϖ l = algebraMap (Lam1 A p) (Lam1Loc A p ϖ) l := rfl

/-- The image of `Λ` lies in `A_∞ = CSAlgOne A p ϖ F`. -/
theorem iΛTOne_mem_CSAlgOne (A : Type u) [CommRing A] (p : ℕ) (ϖ : A) (F : Polynomial A)
    (l : Lam1 A p) : iΛTOne A p ϖ l ∈ CSAlgOne A p ϖ F :=
  Subring.subset_closure (Set.mem_union_left _ ⟨l, rfl⟩)

/-- `π n = ϖ ^ (1/p^n) ∈ L`, the compatible system of `p`-power roots of `ϖ = P.ϖ 0`. -/
noncomputable def psiOne (n : ℕ) : Lam1Loc A p (P.ϖ 0) :=
  AAlgHomLamOne A p (P.ϖ 0) (P.ϖ n)

/-- The inverse of `ϖ` in `L = Λ[1/ϖ]`. -/
noncomputable def iTOne : Lam1Loc A p (P.ϖ 0) :=
  IsLocalization.Away.invSelf (algebraMap A (Lam1 A p) (P.ϖ 0))

/-- `(π n)⁻¹ = π n ^ (p^n - 1) · ϖ⁻¹ ∈ L`. -/
noncomputable def uPiOne (n : ℕ) : Lam1Loc A p (P.ϖ 0) := psiOne n ^ (p ^ n - 1) * iTOne

theorem psiOne_zero :
    psiOne (p := p) (A := A) (P := P) 0 = AAlgHomLamOne A p (P.ϖ 0) (P.ϖ 0) := rfl

theorem psiOne_zero_eq (n : ℕ) : psiOne (p := p) (A := A) (P := P) n
    = AAlgHomLamOne A p (P.ϖ 0) (P.ϖ n) := rfl

theorem psiOne_succ_pow (n : ℕ) : (psiOne (p := p) (A := A) (P := P) (n + 1)) ^ p
    = psiOne (p := p) (A := A) (P := P) n := by
  rw [psiOne, psiOne, ← map_pow, P.root n]

/-- `(π n) ^ (p ^ n) = ϖ` in `L`. -/
theorem psiOne_pow (n : ℕ) : (psiOne (p := p) (A := A) (P := P) n) ^ (p ^ n)
    = psiOne (p := p) (A := A) (P := P) 0 := by
  induction n with
  | zero => simp
  | succ k ih =>
    rw [pow_succ' p k, pow_mul, psiOne_succ_pow k, ih]

/-- `(π n) ^ (p ^ (n+1)) = ϖ ^ p`. -/
theorem psiOne_pow_succ (n : ℕ) : (psiOne (p := p) (A := A) (P := P) n) ^ (p ^ (n + 1))
    = (psiOne (p := p) (A := A) (P := P) 0) ^ p := by
  rw [Nat.pow_succ, pow_mul, psiOne_pow]

/-- `ϖ · ϖ⁻¹ = 1` in `L`. -/
theorem vT_mul_iTOne : psiOne (p := p) (A := A) (P := P) 0 * iTOne = 1 := by
  have h := IsLocalization.Away.mul_invSelf (R := Lam1 A p)
    (S := Lam1Loc A p (P.ϖ 0)) (algebraMap A (Lam1 A p) (P.ϖ 0))
  simpa [iTOne, psiOne, AAlgHomLamOne] using h

theorem iTOne_mul_vT : iTOne (p := p) (A := A) (P := P) * psiOne 0 = 1 := by
  rw [mul_comm, vT_mul_iTOne]

/-- `ϖ ^ p · (ϖ⁻¹) ^ p = 1`. -/
theorem vT_pow_mul_iTOne_pow :
    (psiOne (p := p) (A := A) (P := P) 0) ^ p * iTOne ^ p = 1 := by
  rw [← mul_pow, vT_mul_iTOne, one_pow]

/-- `(π n) · (π n)⁻¹ = 1`. -/
theorem psiOne_mul_uPi (n : ℕ) : psiOne (p := p) (A := A) (P := P) n * uPiOne n = 1 := by
  have hpow : psiOne (p := p) (A := A) (P := P) n * psiOne n ^ (p ^ n - 1)
      = psiOne (p := p) (A := A) (P := P) n ^ (p ^ n) := by
    have h : p ^ n - 1 + 1 = p ^ n :=
      Nat.sub_add_cancel (Nat.one_le_pow n p (Fact.out : p.Prime).pos)
    calc psiOne n * psiOne n ^ (p ^ n - 1) = psiOne n ^ (p ^ n - 1) * psiOne n := by
          rw [mul_comm]
      _ = psiOne n ^ ((p ^ n - 1) + 1) := by rw [pow_add, pow_one]
      _ = psiOne n ^ (p ^ n) := by rw [h]
  rw [uPiOne, ← mul_assoc, hpow, psiOne_pow, vT_mul_iTOne]

theorem uPiOne_mul_psi (n : ℕ) : uPiOne (p := p) (A := A) (P := P) n * psiOne n = 1 := by
  rw [mul_comm, psiOne_mul_uPi]

/-- The defining relation of the inverse system: `((π (n+1))⁻¹) ^ p = (π n)⁻¹`. -/
theorem uPiOne_succ_pow (n : ℕ) : (uPiOne (p := p) (A := A) (P := P) (n + 1)) ^ p = uPiOne n := by
  have h1 : (uPiOne (p := p) (A := A) (P := P) (n + 1)) ^ p * psiOne n = 1 := by
    rw [← psiOne_succ_pow n]
    calc (uPiOne (n + 1)) ^ p * (psiOne (n + 1)) ^ p = (uPiOne (n + 1) * psiOne (n + 1)) ^ p := by
          rw [mul_pow]
      _ = 1 := by rw [uPiOne_mul_psi, one_pow]
  calc (uPiOne (p := p) (A := A) (P := P) (n + 1)) ^ p
      = (uPiOne (n + 1)) ^ p * 1 := (mul_one _).symm
    _ = (uPiOne (n + 1)) ^ p * (psiOne n * uPiOne n) := by rw [psiOne_mul_uPi]
    _ = ((uPiOne (n + 1)) ^ p * psiOne n) * uPiOne n := by ring
    _ = uPiOne n := by rw [h1, one_mul]

/-- `(π n)⁻¹` is the `p ^ n`-th root of `ϖ⁻¹`. -/
theorem uPiOne_pow (n : ℕ) : (uPiOne (p := p) (A := A) (P := P) n) ^ (p ^ n) = iTOne := by
  induction n with
  | zero => simp [uPiOne]
  | succ k ih => rw [Nat.pow_succ', pow_mul, uPiOne_succ_pow k, ih]

theorem uPiOne_pow_succ (n : ℕ) :
    (uPiOne (p := p) (A := A) (P := P) n) ^ (p ^ (n + 1)) = iTOne ^ p := by
  rw [Nat.pow_succ, pow_mul, uPiOne_pow]

/-- `uPiOne 0 = ϖ⁻¹`. -/
theorem uPiOne_zero : uPiOne (p := p) (A := A) (P := P) 0 = iTOne := by
  simp [uPiOne]

/-- `ϖ ^ p · (π m)⁻¹ = (π m) ^ (p ^ (m+1) - 1)`: the fundamental computation which lets a
cofactor `ϖ ^ p` be moved into an integral power of `π m` (i.e. into the ring). -/
theorem varpi_pow_mul_uPiOne (m : ℕ) :
    (psiOne (p := p) (A := A) (P := P) 0) ^ p * uPiOne m
      = (psiOne (p := p) (A := A) (P := P) m) ^ (p ^ (m + 1) - 1) := by
  have h1 : (psiOne (p := p) (A := A) (P := P) m) ^ (p ^ (m + 1) - 1)
      * psiOne (p := p) (A := A) (P := P) m = (psiOne (p := p) (A := A) (P := P) 0) ^ p := by
    rw [← pow_succ,
      Nat.sub_add_cancel (Nat.one_le_pow (m + 1) p (Fact.out : p.Prime).pos)]
    exact psiOne_pow_succ m
  calc (psiOne 0) ^ p * uPiOne m
      = ((psiOne m) ^ (p ^ (m + 1) - 1) * psiOne m) * uPiOne m := by rw [h1]
    _ = (psiOne m) ^ (p ^ (m + 1) - 1) * (psiOne m * uPiOne m) := by ring
    _ = (psiOne m) ^ (p ^ (m + 1) - 1) := by rw [psiOne_mul_uPi, mul_one]

/-! ## `p` is a multiple of `ϖ ^ p` -/

/-- `ϖ ^ p` lies in `A_∞ = CSAlgOne`. -/
theorem varpi_pow_mem_CSAlgOne (F : Polynomial A) :
    (psiOne (p := p) (A := A) (P := P) 0) ^ p ∈ CSAlgOne A p (P.ϖ 0) F := by
  rw [psiOne_zero, ← map_pow]
  exact AAlgHomLamOne_mem_CSAlgOne A p (P.ϖ 0) F ((P.ϖ 0) ^ p)

/-- Every `π n = ϖ ^ (1/p^n)` lies in `A_∞ = CSAlgOne`. -/
theorem psiOne_mem_CSAlgOne (F : Polynomial A) (n : ℕ) :
    psiOne (p := p) (A := A) (P := P) n ∈ CSAlgOne A p (P.ϖ 0) F := by
  rw [psiOne_zero_eq]
  exact AAlgHomLamOne_mem_CSAlgOne A p (P.ϖ 0) F (P.ϖ n)

/-- `ϖ ^ p` lies in any subring of `L` containing `A_∞ = CSAlgOne`. -/
theorem varpi_pow_memOne (F : Polynomial A) (R : Subring (Lam1Loc A p (P.ϖ 0))) :
    (psiOne (p := p) (A := A) (P := P) 0) ^ p ∈ R ⊔ CSAlgOne A p (P.ϖ 0) F :=
  le_sup_right (a := R) (b := CSAlgOne A p (P.ϖ 0) F) (varpi_pow_mem_CSAlgOne F)

/-- **`p = ϖ ^ p · v⁻¹` in `L`**, for `ϖ ^ p = p · v` with `v ∈ A ^×` (`P.unit`).  This is the
identity which lets a cofactor `p` be rewritten as a cofactor `ϖ ^ p`. -/
theorem natCast_p_eqOne (v : Aˣ) (hv : (P.ϖ 0) ^ p = (p : A) * ↑v) :
    (p : Lam1Loc A p (P.ϖ 0))
      = (psiOne (p := p) (A := A) (P := P) 0) ^ p
        * AAlgHomLamOne A p (P.ϖ 0) (↑(v⁻¹) : A) := by
  have hpsi : (psiOne (p := p) (A := A) (P := P) 0) ^ p
      = (p : Lam1Loc A p (P.ϖ 0)) * AAlgHomLamOne A p (P.ϖ 0) (↑v : A) := by
    rw [psiOne_zero, ← map_pow, hv, map_mul, map_natCast]
  have hvu : (↑(v⁻¹) : A) * (↑v : A) = 1 := Units.inv_mul v
  have hunit : AAlgHomLamOne A p (P.ϖ 0) (↑(v⁻¹) : A)
      * AAlgHomLamOne A p (P.ϖ 0) (↑v : A) = 1 := by
    rw [← map_mul, hvu, map_one]
  calc (p : Lam1Loc A p (P.ϖ 0)) = (p : Lam1Loc A p (P.ϖ 0)) * 1 := (mul_one _).symm
    _ = (p : Lam1Loc A p (P.ϖ 0))
          * (AAlgHomLamOne A p (P.ϖ 0) (↑(v⁻¹) : A)
              * AAlgHomLamOne A p (P.ϖ 0) (↑v : A)) := by rw [hunit]
    _ = ((p : Lam1Loc A p (P.ϖ 0)) * AAlgHomLamOne A p (P.ϖ 0) (↑v : A))
          * AAlgHomLamOne A p (P.ϖ 0) (↑(v⁻¹) : A) := by ring
    _ = (psiOne (p := p) (A := A) (P := P) 0) ^ p
          * AAlgHomLamOne A p (P.ϖ 0) (↑(v⁻¹) : A) := by rw [← hpsi]

/-! ## The subring of elements congruent to a `p`-th power modulo `ϖ ^ p R` -/

set_option maxHeartbeats 1600000 in
/-- The set of elements of `L` which are congruent modulo `ϖ ^ p` to a `p`-th power of an
element of `R`, with the cofactor taken in `R ⊔ A_∞`.  It is a subring of `L`: the Frobenius
is additive modulo `p` with integer-coefficient cofactors (`crossTerm_mem`) and `p` is a
`ϖ ^ p`-multiple whose cofactor `v⁻¹` lies in `R ⊔ A_∞` (`natCast_p_eqOne`). -/
def frobSubROne (F : Polynomial A) (R : Subring (Lam1Loc A p (P.ϖ 0))) :
    Subring (Lam1Loc A p (P.ϖ 0)) where
  carrier := {x | ∃ y ∈ R, ∃ c ∈ R ⊔ CSAlgOne A p (P.ϖ 0) F,
    x - y ^ p = (psiOne (p := p) (A := A) (P := P) 0) ^ p * c}
  mul_mem' := by
    rintro x x' ⟨y, hyR, c, hcW, hxy⟩ ⟨y', hyR', c', hcW', hxy'⟩
    refine ⟨y * y', mul_mem hyR hyR',
      c * y' ^ p + y ^ p * c' + (psiOne (p := p) (A := A) (P := P) 0) ^ p * c * c', ?_, ?_⟩
    · exact add_mem (add_mem
        (mul_mem hcW (pow_mem (le_sup_left (a := R) (b := CSAlgOne A p (P.ϖ 0) F) hyR') p))
        (mul_mem (pow_mem (le_sup_left (a := R) (b := CSAlgOne A p (P.ϖ 0) F) hyR) p) hcW'))
        (mul_mem (mul_mem (varpi_pow_memOne F R) hcW) hcW')
    · have hx : x = y ^ p + (psiOne 0) ^ p * c := by
        have := sub_eq_iff_eq_add.mp hxy
        rw [this]; ring
      have hx' : x' = y' ^ p + (psiOne 0) ^ p * c' := by
        have := sub_eq_iff_eq_add.mp hxy'
        rw [this]; ring
      rw [hx, hx', mul_pow]
      ring
  add_mem' := by
    rintro x x' ⟨y, hyR, c, hcW, hxy⟩ ⟨y', hyR', c', hcW', hxy'⟩
    obtain ⟨h, hhW, hh⟩ := crossTerm_mem (Fact.out : p.Prime) (R ⊔ CSAlgOne A p (P.ϖ 0) F)
      (le_sup_left (a := R) (b := CSAlgOne A p (P.ϖ 0) F) hyR)
      (le_sup_left (a := R) (b := CSAlgOne A p (P.ϖ 0) F) hyR')
    obtain ⟨v, hv⟩ := P.unit
    have hp_eq : (p : Lam1Loc A p (P.ϖ 0)) * h
        = (psiOne 0) ^ p * (AAlgHomLamOne A p (P.ϖ 0) (↑(v⁻¹) : A) * h) := by
      rw [natCast_p_eqOne v hv]; ring
    refine ⟨y + y', add_mem hyR hyR',
      c + c' - AAlgHomLamOne A p (P.ϖ 0) (↑(v⁻¹) : A) * h, ?_, ?_⟩
    · exact sub_mem (add_mem hcW hcW')
        (mul_mem (le_sup_right (a := R) (b := CSAlgOne A p (P.ϖ 0) F)
          (AAlgHomLamOne_mem_CSAlgOne A p (P.ϖ 0) F _)) hhW)
    · have hx : x = y ^ p + (psiOne 0) ^ p * c := by
        have := sub_eq_iff_eq_add.mp hxy
        rw [this]; ring
      have hx' : x' = y' ^ p + (psiOne 0) ^ p * c' := by
        have := sub_eq_iff_eq_add.mp hxy'
        rw [this]; ring
      have h2 : (y + y') ^ p = y ^ p + (y' ^ p + (p : Lam1Loc A p (P.ϖ 0)) * h) := by
        have h1 : (y + y') ^ p - y ^ p = (p : Lam1Loc A p (P.ϖ 0)) * h + y' ^ p :=
          sub_eq_iff_eq_add.mp hh
        rw [sub_eq_iff_eq_add.mp h1]
        ring
      rw [hx, hx', h2, hp_eq]
      ring
  zero_mem' := ⟨0, R.zero_mem, 0, (R ⊔ CSAlgOne A p (P.ϖ 0) F).zero_mem, by
    rw [zero_pow (Fact.out : p.Prime).ne_zero, sub_zero, mul_zero]⟩
  one_mem' := ⟨1, R.one_mem, 0, (R ⊔ CSAlgOne A p (P.ϖ 0) F).zero_mem, by
    rw [one_pow, sub_self, mul_zero]⟩
  neg_mem' := by
    rintro x ⟨y, hyR, c, hcW, hxy⟩
    have hx : x = y ^ p + (psiOne 0) ^ p * c := by
      have := sub_eq_iff_eq_add.mp hxy
      rw [this]; ring
    rcases (Fact.out : p.Prime).eq_two_or_odd with h2 | hodd
    · subst h2
      obtain ⟨v, hv⟩ := P.unit
      have hp_eq : (2 : Lam1Loc A 2 (P.ϖ 0))
          = (psiOne (p := 2) (A := A) (P := P) 0) ^ 2
            * AAlgHomLamOne A 2 (P.ϖ 0) (↑(v⁻¹) : A) := by
        simpa using natCast_p_eqOne v hv
      refine ⟨-y, neg_mem hyR,
        -c - AAlgHomLamOne A 2 (P.ϖ 0) (↑(v⁻¹) : A) * y ^ 2, ?_, ?_⟩
      · exact sub_mem (neg_mem hcW) (mul_mem
          (le_sup_right (a := R) (b := CSAlgOne A 2 (P.ϖ 0) F)
            (AAlgHomLamOne_mem_CSAlgOne A 2 (P.ϖ 0) F _))
          (pow_mem (le_sup_left (a := R) (b := CSAlgOne A 2 (P.ϖ 0) F) hyR) 2))
      · rw [hx]
        rw [show (-y : Lam1Loc A 2 (P.ϖ 0)) ^ 2 = y ^ 2 by ring]
        linear_combination (-1 * y ^ 2) * hp_eq
    · have hneg : (-y) ^ p = -y ^ p := by
        rw [neg_eq_neg_one_mul, mul_pow, Odd.neg_one_pow (Nat.odd_iff.mpr hodd), neg_one_mul]
      refine ⟨-y, neg_mem hyR, -c, neg_mem hcW, ?_⟩
      rw [hx, hneg]
      ring

theorem mem_frobSubROne {F : Polynomial A} {R : Subring (Lam1Loc A p (P.ϖ 0))}
    {x : Lam1Loc A p (P.ϖ 0)} :
    x ∈ frobSubROne F R ↔ ∃ y ∈ R, ∃ c ∈ R ⊔ CSAlgOne A p (P.ϖ 0) F,
      x - y ^ p = (psiOne (p := p) (A := A) (P := P) 0) ^ p * c := Iff.rfl

/-- `R` is Frobenius-surjective modulo `ϖ ^ p` (with cofactor in `R`). -/
def IsFrobModROne (F : Polynomial A) (R : Subring (Lam1Loc A p (P.ϖ 0))) : Prop :=
  R ≤ frobSubROne F R

theorem isFrobModROne_iff (F : Polynomial A) (R : Subring (Lam1Loc A p (P.ϖ 0))) :
    IsFrobModROne F R ↔ ∀ x ∈ R, x ∈ frobSubROne F R := Iff.rfl

/-- If `R` contains `A_∞ = CSAlgOne`, the cofactor can be taken in `R` itself. -/
theorem isFrobModROne_cofactor {F : Polynomial A} {R : Subring (Lam1Loc A p (P.ϖ 0))}
    (hR : CSAlgOne A p (P.ϖ 0) F ≤ R) (h : IsFrobModROne F R) :
    ∀ x ∈ R, ∃ y ∈ R, ∃ c ∈ R, x - y ^ p
      = (psiOne (p := p) (A := A) (P := P) 0) ^ p * c := by
  intro x hx
  obtain ⟨y, hy, c, hc, hxy⟩ := (mem_frobSubROne.mp (h hx))
  refine ⟨y, hy, c, ?_, hxy⟩
  rwa [sup_eq_left.mpr hR] at hc

/-! ## The Česnavičius–Scholze tower -/

/-- The elements adjoined at the next level of the tower: the quotients `v / ϖ ^ (1/p^m)`
for `v ∈ R` with `v ^ (p ^ (m+1)) = ϖ ^ p * e` for some `e ∈ R`. -/
def csGenOne (F : Polynomial A) (R : Subring (Lam1Loc A p (P.ϖ 0))) :
    Set (Lam1Loc A p (P.ϖ 0)) :=
  {w | ∃ v ∈ R, ∃ m : ℕ, (∃ e ∈ R, v ^ (p ^ (m + 1))
        = (psiOne (p := p) (A := A) (P := P) 0) ^ p * e) ∧ w = v * uPiOne m}

/-- The Česnavičius–Scholze tower: `R 0 = A_∞ = CSAlgOne` and `R (i+1)` is obtained from
`R i` by adjoining all the elements of `csGenOne F (R i)`. -/
noncomputable def csTowerOne (F : Polynomial A) : ℕ → Subring (Lam1Loc A p (P.ϖ 0))
  | 0 => CSAlgOne A p (P.ϖ 0) F
  | i + 1 => csTowerOne F i ⊔ Subring.closure (csGenOne F (csTowerOne F i))

theorem csTowerOne_zero (F : Polynomial A) :
    csTowerOne (p := p) (A := A) (P := P) F 0 = CSAlgOne A p (P.ϖ 0) F := rfl

theorem csTowerOne_succ (F : Polynomial A) (i : ℕ) :
    csTowerOne (p := p) (A := A) (P := P) F (i + 1)
      = csTowerOne F i ⊔ Subring.closure (csGenOne F (csTowerOne F i)) := rfl

theorem csTowerOne_mono (F : Polynomial A) :
    Monotone (csTowerOne (p := p) (A := A) (P := P) F) := by
  intro m n hmn
  induction n, hmn using Nat.le_induction with
  | base => exact le_rfl
  | succ k hk ih => exact ih.trans le_sup_left

theorem csTowerOne_zero_le (F : Polynomial A) (i : ℕ) :
    CSAlgOne A p (P.ϖ 0) F ≤ csTowerOne (p := p) (A := A) (P := P) F i := by
  rw [← csTowerOne_zero (p := p) (A := A) (P := P) F]
  exact csTowerOne_mono F (Nat.zero_le i)

/-- The union of the tower, as a subring of `L`. -/
noncomputable def csTowerSupOne (F : Polynomial A) : Subring (Lam1Loc A p (P.ϖ 0)) where
  carrier := {x | ∃ i : ℕ, x ∈ csTowerOne (p := p) (A := A) (P := P) F i}
  mul_mem' := by
    rintro x y ⟨m, hm⟩ ⟨n, hn⟩
    exact ⟨max m n, mul_mem (csTowerOne_mono F (le_max_left m n) hm)
      (csTowerOne_mono F (le_max_right m n) hn)⟩
  one_mem' := ⟨0, (csTowerOne (p := p) (A := A) (P := P) F 0).one_mem⟩
  add_mem' := by
    rintro x y ⟨m, hm⟩ ⟨n, hn⟩
    exact ⟨max m n, add_mem (csTowerOne_mono F (le_max_left m n) hm)
      (csTowerOne_mono F (le_max_right m n) hn)⟩
  zero_mem' := ⟨0, (csTowerOne (p := p) (A := A) (P := P) F 0).zero_mem⟩
  neg_mem' := by
    rintro x ⟨n, hn⟩
    exact ⟨n, neg_mem hn⟩

theorem le_csTowerSupOne (F : Polynomial A) (i : ℕ) :
    csTowerOne (p := p) (A := A) (P := P) F i ≤ csTowerSupOne F :=
  fun _ hx => ⟨i, hx⟩

theorem csTowerOne_zero_le_csTowerSupOne (F : Polynomial A) :
    CSAlgOne A p (P.ϖ 0) F ≤ csTowerSupOne (p := p) (A := A) (P := P) F := by
  rw [← csTowerOne_zero (p := p) (A := A) (P := P) F]
  exact le_csTowerSupOne F 0

/-! ## Elementary consequences of the construction -/

/-- `(v * uPiOne m) ^ (p ^ (m+1)) = e` whenever `v ^ (p ^ (m+1)) = ϖ ^ p * e`:  every generator
of the tower step is an `(m+1)`-fold `p`-th root of an element of the previous level. -/
theorem mul_uPiOne_pow {F : Polynomial A} {v : Lam1Loc A p (P.ϖ 0)} {m : ℕ}
    {e : Lam1Loc A p (P.ϖ 0)}
    (h : v ^ (p ^ (m + 1)) = (psiOne (p := p) (A := A) (P := P) 0) ^ p * e) :
    (v * uPiOne (p := p) (A := A) (P := P) m) ^ (p ^ (m + 1)) = e := by
  calc (v * uPiOne (p := p) (A := A) (P := P) m) ^ (p ^ (m + 1))
      = v ^ (p ^ (m + 1)) * (uPiOne (p := p) (A := A) (P := P) m) ^ (p ^ (m + 1)) := by
        rw [mul_pow]
    _ = ((psiOne (p := p) (A := A) (P := P) 0) ^ p * e) * iTOne ^ p := by
        rw [h, uPiOne_pow_succ]
    _ = e * ((psiOne (p := p) (A := A) (P := P) 0) ^ p * iTOne ^ p) := by ring
    _ = e := by rw [vT_pow_mul_iTOne_pow, mul_one]

/-- **The division property of one tower step.**  If `x ∈ Rᵢ` has `x ^ p = ϖ ^ p · c` with
`c ∈ Rᵢ`, then `x / ϖ = x · iTOne ∈ Rᵢ₊₁`. -/
theorem mul_iTOne_mem_csTowerOne_succ {F : Polynomial A} {i : ℕ}
    {x : Lam1Loc A p (P.ϖ 0)}
    (hx : x ∈ csTowerOne (p := p) (A := A) (P := P) F i)
    {c : Lam1Loc A p (P.ϖ 0)}
    (hc : c ∈ csTowerOne (p := p) (A := A) (P := P) F i)
    (h : x ^ p = (psiOne (p := p) (A := A) (P := P) 0) ^ p * c) :
    x * iTOne ∈ csTowerOne (p := p) (A := A) (P := P) F (i + 1) := by
  rw [csTowerOne_succ]
  refine le_sup_right (a := csTowerOne (p := p) (A := A) (P := P) F i)
    (b := Subring.closure (csGenOne F (csTowerOne (p := p) (A := A) (P := P) F i)))
    (Subring.subset_closure ⟨x, hx, 0, ⟨c, hc, ?_⟩, ?_⟩)
  · simpa using h
  · rw [uPiOne_zero]

/-- In a `p`-integrally closed subring, an element whose `p ^ k`-th power lies in the ring is
in the ring. -/
theorem mem_of_pow_pow_memOne {F : Polynomial A} {R : Subring (Lam1Loc A p (P.ϖ 0))}
    (hR : IsPIntegrallyClosedIn p R) (x : Lam1Loc A p (P.ϖ 0)) (k : ℕ)
    (hx : x ^ (p ^ k) ∈ R) : x ∈ R := by
  induction k with
  | zero => simpa using hx
  | succ k ih => exact ih (hR (x ^ p ^ k) (by rwa [← pow_mul, ← Nat.pow_succ]))

end Work.DSM2p
