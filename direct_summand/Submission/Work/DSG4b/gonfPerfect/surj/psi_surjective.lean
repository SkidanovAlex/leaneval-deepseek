import Mathlib
import Submission.Work.DSG4b.gonfPerfect.Basic
import Submission.Work.DSG4b.pBasis.pBasis_pow_basis
import Submission.Work.DSG4b.gonfPerfect.pbPow.pow_decomp

/-!
# Surjectivity of `psi : S →+* PC`

Let `k = R/𝔪` have characteristic the prime `p`, fix `D : PData R p` with `p`-basis `Λ = D.pB`,
and let `PC = PerfectClosure k p` be the perfect closure of `k`, i.e. the residue field of the
colimit `S = D.S`.  We prove that the canonical map

`D.psi : D.S →+* D.PC`

is **surjective**.

Every element of `PC` is of the form `mk (n, x)` for some `n : ℕ` and `x : k`
(`PerfectClosure.mk_surjective`), viewed as `x ^ (p ^ -n)`.  By the `p`-basis input at level `n`
(`pow_decomp`, which is `pBasisPowBasis` + `mem_K`), `x` can be written as a `k^(p^n)`-linear
combination of the monomials `mono e = ∏ a, a ^ (e a)` with `e a < p ^ n`, say
`x = ∑_e d_e^(p^n) · mono e`.  Writing each `d_e` as the residue of some `r_e ∈ R`, the element

`s = ∑_e φ(r_e) · mon n e ∈ S`

maps to `mk (n, x)`: indeed `ψ (incl n (mon n e)) = ∏ a, mk (n, a) ^ (e a) = mk (n, mono e)` and
`ψ (φ r_e) = of (d_e) = (mk (n, d_e)) ^ (p^n)`, so each summand contributes
`mk (n, d_e^(p^n) · mono e)`, and `mk (n, ·)` is a ring homomorphism.
-/

namespace Work.DSG4b.gonfPerfect.surj

open PerfectClosure

/-! ### The ring homomorphisms `x ↦ mk (n, x)`

For fixed `n`, the map `x ↦ mk (n, x)` (viewed as `x ↦ x ^ (p ^ -n)`) is a ring homomorphism;
it is the `(p ^ n)`-th root map on the image of `k` inside `PerfectClosure k p`. -/

section MkN

variable (L : Type*) [CommRing L] (p : ℕ) [Fact p.Prime] [CharP L p]

lemma mk_mul_same (n : ℕ) (x y : L) :
    PerfectClosure.mk L p (n, x * y) = PerfectClosure.mk L p (n, x) * PerfectClosure.mk L p (n, y) := by
  rw [PerfectClosure.mk_mul_mk]
  simp only
  rw [← iterate_map_mul]
  exact PerfectClosure.R.sound L p n n (x * y) ((⇑(frobenius L p))^[n] (x * y)) rfl

lemma mk_add_same (n : ℕ) (x y : L) :
    PerfectClosure.mk L p (n, x + y) = PerfectClosure.mk L p (n, x) + PerfectClosure.mk L p (n, y) := by
  rw [PerfectClosure.mk_add_mk]
  simp only
  rw [← iterate_map_add]
  exact PerfectClosure.R.sound L p n n (x + y) ((⇑(frobenius L p))^[n] (x + y)) rfl

lemma mk_one_same (n : ℕ) : PerfectClosure.mk L p (n, (1 : L)) = 1 := by
  rw [show (1 : L) = ((1 : ℕ) : L) from (Nat.cast_one).symm]
  exact (PerfectClosure.natCast L p n 1).symm.trans Nat.cast_one

/-- `x ↦ mk (n, x)`, the `p ^ n`-th root map, as a ring homomorphism. -/
noncomputable def mkN (n : ℕ) : L →+* PerfectClosure L p where
  toFun x := PerfectClosure.mk L p (n, x)
  map_one' := mk_one_same L p n
  map_mul' := mk_mul_same L p n
  map_zero' := PerfectClosure.mk_zero_right L p n
  map_add' := mk_add_same L p n

@[simp] lemma mkN_apply (n : ℕ) (x : L) : mkN L p n x = PerfectClosure.mk L p (n, x) := rfl

/-- `(mk (n, x)) ^ (p ^ n) = of x`. -/
lemma mkN_pow_eq_of (n : ℕ) (x : L) : (mkN L p n x) ^ p ^ n = PerfectClosure.of L p x := by
  rw [mkN_apply]
  induction n with
  | zero => rw [PerfectClosure.of_apply]; simp
  | succ k ih =>
    rw [pow_succ', pow_mul, PerfectClosure.mk_pow, PerfectClosure.mk_succ_pow]
    exact ih

/-- `mk (n, ·)` is multiplicative on monomials. -/
lemma mkN_prod (n : ℕ) {α : Type*} (e : α →₀ ℕ) (c : α → L) :
    mkN L p n (e.prod (fun a k => (c a) ^ k)) = e.prod (fun a k => (mkN L p n (c a)) ^ k) := by
  rw [Finsupp.prod, Finsupp.prod, map_prod]
  exact Finset.prod_congr rfl (fun a _ => map_pow _ _ _)

end MkN

/-! ### The tower computations -/

/-- The value of `psi` on the class of a reduced monomial: it is the corresponding monomial in the
`p ^ n`-th roots of the `p`-basis elements. -/
lemma psi_mon {R : Type*} [CommRing R] [IsLocalRing R] {p : ℕ} [Fact p.Prime]
    [CharP (IsLocalRing.ResidueField R) p] {D : PData R p} (n : ℕ) (e : D.Idx n) :
    D.psi (D.incl n (D.mon n e)) =
      e.1.prod (fun a k =>
        (PerfectClosure.mk (IsLocalRing.ResidueField R) p (n, (a : IsLocalRing.ResidueField R))) ^ k) := by
  rw [PData.psi_incl, PData.mon_eq, PData.tauN_mk, MvPolynomial.eval₂Hom_monomial, map_one, one_mul]

/-- `psi` of a reduced monomial in `S` equals `mk (n, ·)` of the corresponding monomial of `k`. -/
lemma psi_mkN_mon {R : Type*} [CommRing R] [IsLocalRing R] {p : ℕ} [Fact p.Prime]
    [CharP (IsLocalRing.ResidueField R) p] {D : PData R p} (n : ℕ) (e : D.Idx n) :
    mkN (IsLocalRing.ResidueField R) p n
        (e.1.prod (fun a k => ((a : IsLocalRing.ResidueField R)) ^ k))
      = D.psi (D.incl n (D.mon n e)) := by
  rw [mkN_prod (IsLocalRing.ResidueField R) p n e.1 (fun a => (a : IsLocalRing.ResidueField R))]
  simp only [mkN_apply]
  exact (psi_mon n e).symm

/-- The elements of `k` are hit by `psi ∘ phi` (up to `of`). -/
lemma of_eq_psi_phi {R : Type*} [CommRing R] [IsLocalRing R] {p : ℕ} [Fact p.Prime]
    [CharP (IsLocalRing.ResidueField R) p] (D : PData R p) (r : R)
    (d : IsLocalRing.ResidueField R) (h : IsLocalRing.residue R r = d) :
    PerfectClosure.of (IsLocalRing.ResidueField R) p d = D.psi (D.phi r) := by
  rw [← h]
  exact (D.psi_comp_phi r).symm

/-! ### Surjectivity -/

theorem psi_surjective (R : Type*) [CommRing R] [IsLocalRing R] (p : ℕ) [Fact p.Prime]
    [CharP (IsLocalRing.ResidueField R) p] (D : PData R p) :
    Function.Surjective D.psi := by
  classical
  intro z
  obtain ⟨⟨n, x⟩, rfl⟩ :=
    PerfectClosure.mk_surjective (K := IsLocalRing.ResidueField R) (p := p) z
  obtain ⟨s, hs⟩ := Work.DSG4b.gonfPerfect.pbPow.pow_decomp
    (IsLocalRing.ResidueField R) p D.pB D.basis D.basis_apply n x
  choose r hr using fun e : D.Idx n => IsLocalRing.residue_surjective (s e)
  refine ⟨s.sum (fun e _ => D.phi (r e) * D.incl n (D.mon n e)), ?_⟩
  have key : PerfectClosure.mk (IsLocalRing.ResidueField R) p (n, x)
      = s.sum (fun e _ => D.psi (D.phi (r e) * D.incl n (D.mon n e))) := by
    rw [hs]
    change mkN (IsLocalRing.ResidueField R) p n
        (s.sum (fun e d => d ^ p ^ n * e.1.prod (fun a k => ((a : IsLocalRing.ResidueField R)) ^ k)))
      = s.sum (fun e _ => D.psi (D.phi (r e) * D.incl n (D.mon n e)))
    simp only [Finsupp.sum, map_sum]
    refine Finset.sum_congr rfl (fun e _ => ?_)
    calc mkN (IsLocalRing.ResidueField R) p n
            (s e ^ p ^ n * e.1.prod (fun a k => ((a : IsLocalRing.ResidueField R)) ^ k))
        = mkN (IsLocalRing.ResidueField R) p n (s e ^ p ^ n)
            * mkN (IsLocalRing.ResidueField R) p n
                (e.1.prod (fun a k => ((a : IsLocalRing.ResidueField R)) ^ k)) := map_mul _ _ _
      _ = (mkN (IsLocalRing.ResidueField R) p n (s e)) ^ p ^ n
            * mkN (IsLocalRing.ResidueField R) p n
                (e.1.prod (fun a k => ((a : IsLocalRing.ResidueField R)) ^ k)) := by rw [map_pow]
      _ = PerfectClosure.of (IsLocalRing.ResidueField R) p (s e)
            * mkN (IsLocalRing.ResidueField R) p n
                (e.1.prod (fun a k => ((a : IsLocalRing.ResidueField R)) ^ k)) := by
            rw [mkN_pow_eq_of]
      _ = D.psi (D.phi (r e)) * D.psi (D.incl n (D.mon n e)) := by
            rw [of_eq_psi_phi D (r e) (s e) (hr e), psi_mkN_mon n e]
      _ = D.psi (D.phi (r e) * D.incl n (D.mon n e)) := (map_mul _ _ _).symm
  have h2 : D.psi (s.sum (fun e _ => D.phi (r e) * D.incl n (D.mon n e)))
      = s.sum (fun e _ => D.psi (D.phi (r e) * D.incl n (D.mon n e))) := by
    simp only [Finsupp.sum, map_sum]
  exact h2.trans key.symm

end Work.DSG4b.gonfPerfect.surj
