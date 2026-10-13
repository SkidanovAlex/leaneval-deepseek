import Mathlib
import Submission.Work.DSM2p.ConstructionPos
import Submission.Work.DSM2p.frobSurj_rootClosurePos
import Submission.Work.DSM2p.exists_mul_of_pow_mem
import Submission.Work.DSM2p.adicCompletion_eq_zero_of_mem_pow
import Submission.Work.DSM2p.sum_pow_sub_mem
import Submission.Work.DSM2p.crossTerm_mem

/-!
# DSM2p — Česnavičius–Scholze `p-oid-rec`, the surjectivity half

This file builds the *tower* of Česnavičius–Scholze (`p-oid-rec`, the proposition in
§"`p`-integral closedness of perfectoid rings" of arXiv:1912.10932) inside the ambient ring

`T = Λ[1/ϖ] = RootAlgLocPos A p (P.ϖ 0)`,

where `Λ = RootAlgPos A p = rootClosure A p 𝒫⁺` and `ϖ = P.ϖ 0`.

The starting subring is `A_∞ := CSAlgPos A p ϖ` (the ring of the construction), which is
Frobenius-surjective modulo `ϖ ^ p`.  The aim is to prove the same for the `p`-integral closure
`A' = pIntClosure p A_∞ = CSIntegralClosurePos A p ϖ`, hence for its `p`-adic completion
`B = CSCompletionPos A p ϖ`.

## The statement proved at each level

`R` is *Frobenius-surjective modulo `ϖ ^ p`* if every `x ∈ R` differs from a `p`-th power of
an element of `R` by a multiple of `ϖ ^ p` **whose cofactor lies in `R`**:

`∃ y ∈ R, ∃ c ∈ R, x - y ^ p = ϖ ^ p * c`.

This ("cofactor in the ring") is the form needed at the end: it is exactly what makes the
level-one reduction `R/ϖR → R/ϖ^pR` surjective, and it is what CS prove for the levels
`A_i` of their tower.

## The construction

Since `ϖ ^ p = p · v` with `v ∈ A ^×` and `ϖ` admits compatible `p`-power roots `ϖ^{1/p^n}`
(`P.root`), put `π n := ϖ ^{1/p^n} ∈ T` (`psi n`) and `uPi n := (π n)⁻¹` (`= π n ^ (p^n - 1) · ϖ⁻¹`).
The next level from `R` adjoins all the quotients

`v / ϖ ^{1/p^m} = v * uPi m`    for `v ∈ R` with `v ^{p ^ (m + 1)} = ϖ ^ p * e`, `e ∈ R`:

* this contains the CS generators `a_n / π_n` of any "specific sequence" `a_0 = u`,
  `a_n ^ p ≡ a_{n-1}` mod `ϖ ^ p R` (iterate `a_n^{p^k} ≡ a_{n-k}` to get `a_n^{p^{n+1}} ≡ u^p
  = ϖ^p c`), and also the divisions `u / ϖ` (`m = 0`) which make the limit `p`-integrally closed;
* each generator is an `(m+1)`-fold `p`-th root of an element of `R` (`mul_uPi_pow`), hence
  lies in `A'` by `p`-integral closedness;
* Frobenius-surjectivity is preserved: for the generator `w = v * uPi m` take
  `y = v₁ * uPi (m+1) + π_{m+1}^{p^{m+1}-1} c'`, where `v₁^p = v - ϖ^p c` and `(c')^p = c + ϖ^p f`
  come from the induction hypothesis; then `y ∈ R'` and
  `w - y^p = ϖ^p · (π_m^{p^{m+1}-1} f + v^{-1} h)`, with `h` the cross terms of `(z, ε)`.
-/

open scoped Classical

namespace Work.DSM2p

universe u

variable {p : ℕ} [Fact p.Prime] {A : Type u} [CommRing A] {P : DSMap.PerfectoidData p A}

set_option maxHeartbeats 1600000 in
/-- The structure map `Λ → Λ[1/ϖ]`, as an explicit ring hom: using this instead of the
`algebraMap` term keeps the elaboration of later proofs cheap (the `RingHom` structure of that
`algebraMap` is expensive to synthesize). -/
noncomputable def iΛT : RootAlgPos A p →+* RootAlgLocPos A p (P.ϖ 0) :=
  algebraMap (RootAlgPos A p) (RootAlgLocPos A p (P.ϖ 0))

theorem iΛT_apply (l : RootAlgPos A p) :
    iΛT l = algebraMap (RootAlgPos A p) (RootAlgLocPos A p (P.ϖ 0)) l := rfl

/-- The image of `Λ` lies in `A_∞ = CSAlgPos`. -/
theorem iΛT_mem_CSAlgPos (l : RootAlgPos A p) : iΛT l ∈ CSAlgPos A p (P.ϖ 0) :=
  Subring.subset_closure (Set.mem_union_left _ ⟨l, rfl⟩)

/-- `π n = ϖ ^ (1/p^n) ∈ T`, the compatible system of `p`-power roots of `ϖ = P.ϖ 0`. -/
noncomputable def psi (n : ℕ) : RootAlgLocPos A p (P.ϖ 0) :=
  AAlgHomLocPos A p (P.ϖ 0) (P.ϖ n)

/-- The inverse of `ϖ` in `T = Λ[1/ϖ]`. -/
noncomputable def iT : RootAlgLocPos A p (P.ϖ 0) :=
  IsLocalization.Away.invSelf (algebraMap A (RootAlgPos A p) (P.ϖ 0))

/-- `(π n)⁻¹ = π n ^ (p^n - 1) · ϖ⁻¹ ∈ T`. -/
noncomputable def uPi (n : ℕ) : RootAlgLocPos A p (P.ϖ 0) := psi n ^ (p ^ n - 1) * iT

theorem psi_zero : psi (p := p) (A := A) (P := P) 0 = AAlgHomLocPos A p (P.ϖ 0) (P.ϖ 0) := rfl

theorem psi_zero_eq (n : ℕ) : psi (p := p) (A := A) (P := P) n
    = AAlgHomLocPos A p (P.ϖ 0) (P.ϖ n) := rfl

theorem psi_succ_pow (n : ℕ) : (psi (p := p) (A := A) (P := P) (n + 1)) ^ p
    = psi (p := p) (A := A) (P := P) n := by
  rw [psi, psi, ← map_pow, P.root n]

/-- `(π n) ^ (p ^ n) = ϖ` in `T`. -/
theorem psi_pow (n : ℕ) : (psi (p := p) (A := A) (P := P) n) ^ (p ^ n)
    = psi (p := p) (A := A) (P := P) 0 := by
  induction n with
  | zero => simp
  | succ k ih =>
    rw [pow_succ' p k, pow_mul, psi_succ_pow k, ih]

/-- `(π n) ^ (p ^ (n+1)) = ϖ ^ p`. -/
theorem psi_pow_succ (n : ℕ) : (psi (p := p) (A := A) (P := P) n) ^ (p ^ (n + 1))
    = (psi (p := p) (A := A) (P := P) 0) ^ p := by
  rw [Nat.pow_succ, pow_mul, psi_pow]

/-- `ϖ · ϖ⁻¹ = 1` in `T`. -/
theorem vT_mul_iT : psi (p := p) (A := A) (P := P) 0 * iT = 1 := by
  have h := IsLocalization.Away.mul_invSelf (R := RootAlgPos A p)
    (S := RootAlgLocPos A p (P.ϖ 0)) (algebraMap A (RootAlgPos A p) (P.ϖ 0))
  simpa [iT, psi, AAlgHomLocPos] using h

theorem iT_mul_vT : iT (p := p) (A := A) (P := P) * psi 0 = 1 := by
  rw [mul_comm, vT_mul_iT]

/-- `ϖ ^ p · (ϖ⁻¹) ^ p = 1`. -/
theorem vT_pow_mul_iT_pow :
    (psi (p := p) (A := A) (P := P) 0) ^ p * iT ^ p = 1 := by
  rw [← mul_pow, vT_mul_iT, one_pow]

/-- `(π n) · (π n)⁻¹ = 1`. -/
theorem psi_mul_uPi (n : ℕ) : psi (p := p) (A := A) (P := P) n * uPi n = 1 := by
  have hpow : psi (p := p) (A := A) (P := P) n * psi n ^ (p ^ n - 1)
      = psi (p := p) (A := A) (P := P) n ^ (p ^ n) := by
    have h : p ^ n - 1 + 1 = p ^ n :=
      Nat.sub_add_cancel (Nat.one_le_pow n p (Fact.out : p.Prime).pos)
    calc psi n * psi n ^ (p ^ n - 1) = psi n ^ (p ^ n - 1) * psi n := by rw [mul_comm]
      _ = psi n ^ ((p ^ n - 1) + 1) := by rw [pow_add, pow_one]
      _ = psi n ^ (p ^ n) := by rw [h]
  rw [uPi, ← mul_assoc, hpow, psi_pow, vT_mul_iT]

theorem uPi_mul_psi (n : ℕ) : uPi (p := p) (A := A) (P := P) n * psi n = 1 := by
  rw [mul_comm, psi_mul_uPi]

/-- The defining relation of the inverse system: `((π (n+1))⁻¹) ^ p = (π n)⁻¹`. -/
theorem uPi_succ_pow (n : ℕ) : (uPi (p := p) (A := A) (P := P) (n + 1)) ^ p = uPi n := by
  have h1 : (uPi (p := p) (A := A) (P := P) (n + 1)) ^ p * psi n = 1 := by
    rw [← psi_succ_pow n]
    calc (uPi (n + 1)) ^ p * (psi (n + 1)) ^ p = (uPi (n + 1) * psi (n + 1)) ^ p := by
          rw [mul_pow]
      _ = 1 := by rw [uPi_mul_psi, one_pow]
  calc (uPi (p := p) (A := A) (P := P) (n + 1)) ^ p
      = (uPi (n + 1)) ^ p * 1 := (mul_one _).symm
    _ = (uPi (n + 1)) ^ p * (psi n * uPi n) := by rw [psi_mul_uPi]
    _ = ((uPi (n + 1)) ^ p * psi n) * uPi n := by ring
    _ = uPi n := by rw [h1, one_mul]

/-- `(π n)⁻¹` is the `p ^ n`-th root of `ϖ⁻¹`. -/
theorem uPi_pow (n : ℕ) : (uPi (p := p) (A := A) (P := P) n) ^ (p ^ n) = iT := by
  induction n with
  | zero => simp [uPi]
  | succ k ih => rw [Nat.pow_succ', pow_mul, uPi_succ_pow k, ih]

theorem uPi_pow_succ (n : ℕ) : (uPi (p := p) (A := A) (P := P) n) ^ (p ^ (n + 1)) = iT ^ p := by
  rw [Nat.pow_succ, pow_mul, uPi_pow]

/-- `uPi 0 = ϖ⁻¹`. -/
theorem uPi_zero : uPi (p := p) (A := A) (P := P) 0 = iT := by
  simp [uPi]

/-- `ϖ ^ p · (π m)⁻¹ = (π m) ^ (p ^ (m+1) - 1)`: the fundamental computation which lets a
cofactor `ϖ ^ p` be moved into an integral power of `π m` (i.e. into the ring). -/
theorem varpi_pow_mul_uPi (m : ℕ) :
    (psi (p := p) (A := A) (P := P) 0) ^ p * uPi m
      = (psi (p := p) (A := A) (P := P) m) ^ (p ^ (m + 1) - 1) := by
  have h1 : (psi (p := p) (A := A) (P := P) m) ^ (p ^ (m + 1) - 1)
      * psi (p := p) (A := A) (P := P) m = (psi (p := p) (A := A) (P := P) 0) ^ p := by
    rw [← pow_succ,
      Nat.sub_add_cancel (Nat.one_le_pow (m + 1) p (Fact.out : p.Prime).pos)]
    exact psi_pow_succ m
  calc (psi 0) ^ p * uPi m = ((psi m) ^ (p ^ (m + 1) - 1) * psi m) * uPi m := by rw [h1]
    _ = (psi m) ^ (p ^ (m + 1) - 1) * (psi m * uPi m) := by ring
    _ = (psi m) ^ (p ^ (m + 1) - 1) := by rw [psi_mul_uPi, mul_one]

/-! ## `p` is a multiple of `ϖ ^ p` -/

/-- `ϖ ^ p` lies in `A_∞ = CSAlgPos`. -/
theorem varpi_pow_mem_CSAlgPos :
    (psi (p := p) (A := A) (P := P) 0) ^ p ∈ CSAlgPos A p (P.ϖ 0) := by
  rw [psi_zero, ← map_pow]
  exact AAlgHomLocPos_mem_CSAlgPos A p (P.ϖ 0) ((P.ϖ 0) ^ p)

/-- Every `π n = ϖ ^ (1/p^n)` lies in `A_∞ = CSAlgPos`. -/
theorem psi_mem_CSAlgPos (n : ℕ) : psi (p := p) (A := A) (P := P) n ∈ CSAlgPos A p (P.ϖ 0) := by
  rw [psi_zero_eq]
  exact AAlgHomLocPos_mem_CSAlgPos A p (P.ϖ 0) (P.ϖ n)

/-- `ϖ ^ p` lies in any subring of `T` containing `A_∞ = CSAlgPos`. -/
theorem varpi_pow_mem (R : Subring (RootAlgLocPos A p (P.ϖ 0))) :
    (psi (p := p) (A := A) (P := P) 0) ^ p ∈ R ⊔ CSAlgPos A p (P.ϖ 0) :=
  le_sup_right (a := R) (b := CSAlgPos A p (P.ϖ 0)) varpi_pow_mem_CSAlgPos

/-- **`p = ϖ ^ p · v⁻¹` in `T`**, for `ϖ ^ p = p · v` with `v ∈ A ^×` (`P.unit`).  This is the
identity which lets a cofactor `p` be rewritten as a cofactor `ϖ ^ p`. -/
theorem natCast_p_eq (v : Aˣ) (hv : (P.ϖ 0) ^ p = (p : A) * ↑v) :
    (p : RootAlgLocPos A p (P.ϖ 0))
      = (psi (p := p) (A := A) (P := P) 0) ^ p * AAlgHomLocPos A p (P.ϖ 0) (↑(v⁻¹) : A) := by
  have hpsi : (psi (p := p) (A := A) (P := P) 0) ^ p
      = (p : RootAlgLocPos A p (P.ϖ 0)) * AAlgHomLocPos A p (P.ϖ 0) (↑v : A) := by
    rw [psi_zero, ← map_pow, hv, map_mul, map_natCast]
  have hvu : (↑(v⁻¹) : A) * (↑v : A) = 1 := Units.inv_mul v
  have hunit : AAlgHomLocPos A p (P.ϖ 0) (↑(v⁻¹) : A)
      * AAlgHomLocPos A p (P.ϖ 0) (↑v : A) = 1 := by
    rw [← map_mul, hvu, map_one]
  calc (p : RootAlgLocPos A p (P.ϖ 0)) = (p : RootAlgLocPos A p (P.ϖ 0)) * 1 := (mul_one _).symm
    _ = (p : RootAlgLocPos A p (P.ϖ 0))
          * (AAlgHomLocPos A p (P.ϖ 0) (↑(v⁻¹) : A)
              * AAlgHomLocPos A p (P.ϖ 0) (↑v : A)) := by rw [hunit]
    _ = ((p : RootAlgLocPos A p (P.ϖ 0)) * AAlgHomLocPos A p (P.ϖ 0) (↑v : A))
          * AAlgHomLocPos A p (P.ϖ 0) (↑(v⁻¹) : A) := by ring
    _ = (psi (p := p) (A := A) (P := P) 0) ^ p
          * AAlgHomLocPos A p (P.ϖ 0) (↑(v⁻¹) : A) := by rw [← hpsi]

/-! ## The subring of elements congruent to a `p`-th power modulo `ϖ ^ p R` -/

/-- The set of elements of `T` which are congruent modulo `ϖ ^ p` to a `p`-th power of an
element of `R`, with the cofactor taken in `R ⊔ A_∞`.  It is a subring of `T`: the Frobenius
is additive modulo `p` with integer-coefficient cofactors (`crossTerm_mem`) and `p` is a
`ϖ ^ p`-multiple whose cofactor `v⁻¹` lies in `R ⊔ A_∞` (`natCast_p_eq`). -/
def frobSubR (R : Subring (RootAlgLocPos A p (P.ϖ 0))) :
    Subring (RootAlgLocPos A p (P.ϖ 0)) where
  carrier := {x | ∃ y ∈ R, ∃ c ∈ R ⊔ CSAlgPos A p (P.ϖ 0),
    x - y ^ p = (psi (p := p) (A := A) (P := P) 0) ^ p * c}
  mul_mem' := by
    rintro x x' ⟨y, hyR, c, hcW, hxy⟩ ⟨y', hyR', c', hcW', hxy'⟩
    refine ⟨y * y', mul_mem hyR hyR',
      c * y' ^ p + y ^ p * c' + (psi (p := p) (A := A) (P := P) 0) ^ p * c * c', ?_, ?_⟩
    · exact add_mem (add_mem
        (mul_mem hcW (pow_mem (le_sup_left (a := R) (b := CSAlgPos A p (P.ϖ 0)) hyR') p))
        (mul_mem (pow_mem (le_sup_left (a := R) (b := CSAlgPos A p (P.ϖ 0)) hyR) p) hcW'))
        (mul_mem (mul_mem (varpi_pow_mem R) hcW) hcW')
    · have hx : x = y ^ p + (psi 0) ^ p * c := by
        have := sub_eq_iff_eq_add.mp hxy
        rw [this]; ring
      have hx' : x' = y' ^ p + (psi 0) ^ p * c' := by
        have := sub_eq_iff_eq_add.mp hxy'
        rw [this]; ring
      rw [hx, hx', mul_pow]
      ring
  add_mem' := by
    rintro x x' ⟨y, hyR, c, hcW, hxy⟩ ⟨y', hyR', c', hcW', hxy'⟩
    obtain ⟨h, hhW, hh⟩ := crossTerm_mem (Fact.out : p.Prime) (R ⊔ CSAlgPos A p (P.ϖ 0))
      (le_sup_left (a := R) (b := CSAlgPos A p (P.ϖ 0)) hyR)
      (le_sup_left (a := R) (b := CSAlgPos A p (P.ϖ 0)) hyR')
    obtain ⟨v, hv⟩ := P.unit
    have hp_eq : (p : RootAlgLocPos A p (P.ϖ 0)) * h
        = (psi 0) ^ p * (AAlgHomLocPos A p (P.ϖ 0) (↑(v⁻¹) : A) * h) := by
      rw [natCast_p_eq v hv]; ring
    refine ⟨y + y', add_mem hyR hyR',
      c + c' - AAlgHomLocPos A p (P.ϖ 0) (↑(v⁻¹) : A) * h, ?_, ?_⟩
    · exact sub_mem (add_mem hcW hcW')
        (mul_mem (le_sup_right (a := R) (b := CSAlgPos A p (P.ϖ 0))
          (AAlgHomLocPos_mem_CSAlgPos A p (P.ϖ 0) _)) hhW)
    · have hx : x = y ^ p + (psi 0) ^ p * c := by
        have := sub_eq_iff_eq_add.mp hxy
        rw [this]; ring
      have hx' : x' = y' ^ p + (psi 0) ^ p * c' := by
        have := sub_eq_iff_eq_add.mp hxy'
        rw [this]; ring
      have h2 : (y + y') ^ p = y ^ p + (y' ^ p + (p : RootAlgLocPos A p (P.ϖ 0)) * h) := by
        have h1 : (y + y') ^ p - y ^ p = (p : RootAlgLocPos A p (P.ϖ 0)) * h + y' ^ p :=
          sub_eq_iff_eq_add.mp hh
        rw [sub_eq_iff_eq_add.mp h1]
        ring
      rw [hx, hx', h2, hp_eq]
      ring
  zero_mem' := ⟨0, R.zero_mem, 0, (R ⊔ CSAlgPos A p (P.ϖ 0)).zero_mem, by
    rw [zero_pow (Fact.out : p.Prime).ne_zero, sub_zero, mul_zero]⟩
  one_mem' := ⟨1, R.one_mem, 0, (R ⊔ CSAlgPos A p (P.ϖ 0)).zero_mem, by
    rw [one_pow, sub_self, mul_zero]⟩
  neg_mem' := by
    rintro x ⟨y, hyR, c, hcW, hxy⟩
    have hx : x = y ^ p + (psi 0) ^ p * c := by
      have := sub_eq_iff_eq_add.mp hxy
      rw [this]; ring
    rcases (Fact.out : p.Prime).eq_two_or_odd with h2 | hodd
    · subst h2
      obtain ⟨v, hv⟩ := P.unit
      have hp_eq : (2 : RootAlgLocPos A 2 (P.ϖ 0))
          = (psi (p := 2) (A := A) (P := P) 0) ^ 2
            * AAlgHomLocPos A 2 (P.ϖ 0) (↑(v⁻¹) : A) := by
        simpa using natCast_p_eq v hv
      refine ⟨-y, neg_mem hyR,
        -c - AAlgHomLocPos A 2 (P.ϖ 0) (↑(v⁻¹) : A) * y ^ 2, ?_, ?_⟩
      · exact sub_mem (neg_mem hcW) (mul_mem
          (le_sup_right (a := R) (b := CSAlgPos A 2 (P.ϖ 0))
            (AAlgHomLocPos_mem_CSAlgPos A 2 (P.ϖ 0) _))
          (pow_mem (le_sup_left (a := R) (b := CSAlgPos A 2 (P.ϖ 0)) hyR) 2))
      · rw [hx]
        rw [show (-y : RootAlgLocPos A 2 (P.ϖ 0)) ^ 2 = y ^ 2 by ring]
        linear_combination (-1 * y ^ 2) * hp_eq
    · have hneg : (-y) ^ p = -y ^ p := by
        rw [neg_eq_neg_one_mul, mul_pow, Odd.neg_one_pow (Nat.odd_iff.mpr hodd), neg_one_mul]
      refine ⟨-y, neg_mem hyR, -c, neg_mem hcW, ?_⟩
      rw [hx, hneg]
      ring

theorem mem_frobSubR {R : Subring (RootAlgLocPos A p (P.ϖ 0))}
    {x : RootAlgLocPos A p (P.ϖ 0)} :
    x ∈ frobSubR R ↔ ∃ y ∈ R, ∃ c ∈ R ⊔ CSAlgPos A p (P.ϖ 0),
      x - y ^ p = (psi (p := p) (A := A) (P := P) 0) ^ p * c := Iff.rfl

/-- `R` is Frobenius-surjective modulo `ϖ ^ p` (with cofactor in `R`). -/
def IsFrobModR (R : Subring (RootAlgLocPos A p (P.ϖ 0))) : Prop := R ≤ frobSubR R

theorem isFrobModR_iff (R : Subring (RootAlgLocPos A p (P.ϖ 0))) :
    IsFrobModR R ↔ ∀ x ∈ R, x ∈ frobSubR R := Iff.rfl

/-- If `R` contains `A_∞ = CSAlgPos` (as all levels of the tower do), the cofactor can be
taken in `R` itself. -/
theorem isFrobModR_cofactor {R : Subring (RootAlgLocPos A p (P.ϖ 0))}
    (hR : CSAlgPos A p (P.ϖ 0) ≤ R) (h : IsFrobModR R) :
    ∀ x ∈ R, ∃ y ∈ R, ∃ c ∈ R, x - y ^ p
      = (psi (p := p) (A := A) (P := P) 0) ^ p * c := by
  intro x hx
  obtain ⟨y, hy, c, hc, hxy⟩ := (mem_frobSubR.mp (h hx))
  refine ⟨y, hy, c, ?_, hxy⟩
  rwa [sup_eq_left.mpr hR] at hc

/-! ## The Česnavičius–Scholze tower -/

/-- The elements adjoined at the next level of the tower: the quotients `v / ϖ ^ (1/p^m)`
for `v ∈ R` with `v ^ (p ^ (m+1)) = ϖ ^ p * e` for some `e ∈ R`.

These include the Česnavičius–Scholze elements `a_n / π_n` of any specific sequence
(`a_n^{p^{n+1}} ≡ a_0^p = ϖ^p c`) and the divisions `u / ϖ` (`m = 0`). -/
def csGen (R : Subring (RootAlgLocPos A p (P.ϖ 0))) :
    Set (RootAlgLocPos A p (P.ϖ 0)) :=
  {w | ∃ v ∈ R, ∃ m : ℕ, (∃ e ∈ R, v ^ (p ^ (m + 1))
        = (psi (p := p) (A := A) (P := P) 0) ^ p * e) ∧ w = v * uPi m}

/-- The Česnavičius–Scholze tower: `R 0 = A_∞ = CSAlgPos A p ϖ` and `R (i+1)` is obtained
from `R i` by adjoining all the elements of `csGen (R i)`. -/
noncomputable def csTower : ℕ → Subring (RootAlgLocPos A p (P.ϖ 0))
  | 0 => CSAlgPos A p (P.ϖ 0)
  | i + 1 => csTower i ⊔ Subring.closure (csGen (csTower i))

theorem csTower_zero : csTower (p := p) (A := A) (P := P) 0 = CSAlgPos A p (P.ϖ 0) := rfl

theorem csTower_succ (i : ℕ) : csTower (p := p) (A := A) (P := P) (i + 1)
    = csTower i ⊔ Subring.closure (csGen (csTower i)) := rfl

theorem csTower_mono : Monotone (csTower (p := p) (A := A) (P := P)) := by
  intro m n hmn
  induction n, hmn using Nat.le_induction with
  | base => exact le_rfl
  | succ k hk ih => exact ih.trans le_sup_left

theorem csTower_zero_le (i : ℕ) :
    CSAlgPos A p (P.ϖ 0) ≤ csTower (p := p) (A := A) (P := P) i := by
  rw [← csTower_zero (p := p) (A := A) (P := P)]
  exact csTower_mono (Nat.zero_le i)

/-- The union of the tower, as a subring of `T`. -/
noncomputable def csTowerSup : Subring (RootAlgLocPos A p (P.ϖ 0)) where
  carrier := {x | ∃ i : ℕ, x ∈ csTower (p := p) (A := A) (P := P) i}
  mul_mem' := by
    rintro x y ⟨m, hm⟩ ⟨n, hn⟩
    exact ⟨max m n, mul_mem (csTower_mono (le_max_left m n) hm)
      (csTower_mono (le_max_right m n) hn)⟩
  one_mem' := ⟨0, (csTower (p := p) (A := A) (P := P) 0).one_mem⟩
  add_mem' := by
    rintro x y ⟨m, hm⟩ ⟨n, hn⟩
    exact ⟨max m n, add_mem (csTower_mono (le_max_left m n) hm)
      (csTower_mono (le_max_right m n) hn)⟩
  zero_mem' := ⟨0, (csTower (p := p) (A := A) (P := P) 0).zero_mem⟩
  neg_mem' := by
    rintro x ⟨n, hn⟩
    exact ⟨n, neg_mem hn⟩

theorem le_csTowerSup (i : ℕ) : csTower (p := p) (A := A) (P := P) i ≤ csTowerSup :=
  fun _ hx => ⟨i, hx⟩

theorem csTower_zero_le_csTowerSup :
    CSAlgPos A p (P.ϖ 0) ≤ csTowerSup (p := p) (A := A) (P := P) := by
  rw [← csTower_zero (p := p) (A := A) (P := P)]
  exact le_csTowerSup 0

/-! ## Elementary consequences of the construction -/

/-- `(v * uPi m) ^ (p ^ (m+1)) = e` whenever `v ^ (p ^ (m+1)) = ϖ ^ p * e`:  every generator
of the tower step is an `(m+1)`-fold `p`-th root of an element of the previous level. -/
theorem mul_uPi_pow {v : RootAlgLocPos A p (P.ϖ 0)} {m : ℕ}
    {e : RootAlgLocPos A p (P.ϖ 0)}
    (h : v ^ (p ^ (m + 1)) = (psi (p := p) (A := A) (P := P) 0) ^ p * e) :
    (v * uPi (p := p) (A := A) (P := P) m) ^ (p ^ (m + 1)) = e := by
  calc (v * uPi (p := p) (A := A) (P := P) m) ^ (p ^ (m + 1))
      = v ^ (p ^ (m + 1)) * (uPi (p := p) (A := A) (P := P) m) ^ (p ^ (m + 1)) := by
        rw [mul_pow]
    _ = ((psi (p := p) (A := A) (P := P) 0) ^ p * e) * iT ^ p := by
        rw [h, uPi_pow_succ]
    _ = e * ((psi (p := p) (A := A) (P := P) 0) ^ p * iT ^ p) := by ring
    _ = e := by rw [vT_pow_mul_iT_pow, mul_one]

/-- **The division property of one tower step.**  If `x ∈ Rᵢ` has `x ^ p = ϖ ^ p · c` with
`c ∈ Rᵢ`, then `x / ϖ = x · iT ∈ Rᵢ₊₁`. -/
theorem mul_iT_mem_csTower_succ {i : ℕ} {x : RootAlgLocPos A p (P.ϖ 0)}
    (hx : x ∈ csTower (p := p) (A := A) (P := P) i)
    {c : RootAlgLocPos A p (P.ϖ 0)}
    (hc : c ∈ csTower (p := p) (A := A) (P := P) i)
    (h : x ^ p = (psi (p := p) (A := A) (P := P) 0) ^ p * c) :
    x * iT ∈ csTower (p := p) (A := A) (P := P) (i + 1) := by
  rw [csTower_succ]
  refine le_sup_right (a := csTower (p := p) (A := A) (P := P) i)
    (b := Subring.closure (csGen (csTower (p := p) (A := A) (P := P) i)))
    (Subring.subset_closure ⟨x, hx, 0, ⟨c, hc, ?_⟩, ?_⟩)
  · simpa using h
  · rw [uPi_zero]

/-- In a `p`-integrally closed subring, an element whose `p ^ k`-th power lies in the ring is
in the ring. -/
theorem mem_of_pow_pow_mem {R : Subring (RootAlgLocPos A p (P.ϖ 0))}
    (hR : IsPIntegrallyClosedIn p R) (x : RootAlgLocPos A p (P.ϖ 0)) (k : ℕ)
    (hx : x ^ (p ^ k) ∈ R) : x ∈ R := by
  induction k with
  | zero => simpa using hx
  | succ k ih => exact ih (hR (x ^ p ^ k) (by rwa [← pow_mul, ← Nat.pow_succ]))

end Work.DSM2p
