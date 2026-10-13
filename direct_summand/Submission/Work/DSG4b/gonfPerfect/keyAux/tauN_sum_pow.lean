import Mathlib
import Submission.Work.DSG4b.gonfPerfect.Basic

namespace Work.DSG4b.gonfPerfect.keyAux

open MvPolynomial

variable {R : Type*} [CommRing R] [IsLocalRing R] {p : ℕ} [Fact p.Prime]
  [CharP (IsLocalRing.ResidueField R) p]

/-- Raising `tauN` of a reduced monomial to the `p ^ N`-th power lands in the image of the
residue field, where it is the monomial of the exponent vector. -/
theorem tauN_mon_pow (D : PData R p) (N : ℕ) (e : D.Idx N) :
    (D.tauN N (D.mon N e)) ^ p ^ N =
      PerfectClosure.of (IsLocalRing.ResidueField R) p
        (e.1.prod (fun b kb => ((b : IsLocalRing.ResidueField R) ^ kb))) := by
  have h1 : e.1.prod (fun b kb => (PerfectClosure.mk (IsLocalRing.ResidueField R) p
        (N, (b : IsLocalRing.ResidueField R))) ^ kb)
      = ∏ b ∈ e.1.support, (PerfectClosure.mk (IsLocalRing.ResidueField R) p
        (N, (b : IsLocalRing.ResidueField R))) ^ (e.1 b) :=
    Finsupp.prod_of_support_subset (f := e.1) (s := e.1.support) (by simp)
      (fun b kb => (PerfectClosure.mk (IsLocalRing.ResidueField R) p
        (N, (b : IsLocalRing.ResidueField R))) ^ kb) (by intro i hi; simp)
  have h2 : e.1.prod (fun b kb => ((b : IsLocalRing.ResidueField R) ^ kb))
      = ∏ b ∈ e.1.support, ((b : IsLocalRing.ResidueField R) ^ (e.1 b)) :=
    Finsupp.prod_of_support_subset (f := e.1) (s := e.1.support) (by simp)
      (fun b kb => ((b : IsLocalRing.ResidueField R) ^ kb)) (by intro i hi; simp)
  rw [PData.mon_eq, D.tauN_mk, MvPolynomial.eval₂Hom_monomial]
  simp only [map_one, one_mul]
  rw [h1]
  calc (∏ b ∈ e.1.support, (PerfectClosure.mk (IsLocalRing.ResidueField R) p
          (N, (b : IsLocalRing.ResidueField R))) ^ (e.1 b)) ^ p ^ N
      = ∏ b ∈ e.1.support, ((PerfectClosure.mk (IsLocalRing.ResidueField R) p
          (N, (b : IsLocalRing.ResidueField R))) ^ (e.1 b)) ^ p ^ N := by
        rw [Finset.prod_pow]
    _ = ∏ b ∈ e.1.support, (PerfectClosure.of (IsLocalRing.ResidueField R) p
          ((b : IsLocalRing.ResidueField R))) ^ (e.1 b) := by
        refine Finset.prod_congr rfl (fun b hb => ?_)
        rw [← pow_mul, pow_mul', PData.pc_mk_pow]
    _ = ∏ b ∈ e.1.support, PerfectClosure.of (IsLocalRing.ResidueField R) p
          (((b : IsLocalRing.ResidueField R)) ^ (e.1 b)) := by
        refine Finset.prod_congr rfl (fun b hb => ?_)
        rw [map_pow]
    _ = PerfectClosure.of (IsLocalRing.ResidueField R) p
          (∏ b ∈ e.1.support, ((b : IsLocalRing.ResidueField R)) ^ (e.1 b)) := by
        rw [map_prod]
    _ = PerfectClosure.of (IsLocalRing.ResidueField R) p
          (e.1.prod (fun b kb => ((b : IsLocalRing.ResidueField R) ^ kb))) := by
        rw [h2]

theorem tauN_sum_pow (R : Type*) [CommRing R] [IsLocalRing R] (p : ℕ) [Fact p.Prime]
    [CharP (IsLocalRing.ResidueField R) p] (D : PData R p) (N : ℕ)
    (s : Finset (D.Idx N)) (r : D.Idx N → R) :
    (D.tauN N (∑ e ∈ s, algebraMap R (D.AN N) (r e) * D.mon N e)) ^ p ^ N =
      PerfectClosure.of (IsLocalRing.ResidueField R) p
        (∑ e ∈ s, (IsLocalRing.residue R (r e)) ^ p ^ N *
          (e.1.prod (fun b kb => ((b : IsLocalRing.ResidueField R) ^ kb)))) := by
  have term : ∀ e : D.Idx N,
      (D.tauN N (algebraMap R (D.AN N) (r e) * D.mon N e)) ^ p ^ N =
        PerfectClosure.of (IsLocalRing.ResidueField R) p
          ((IsLocalRing.residue R (r e)) ^ p ^ N *
            e.1.prod (fun b kb => ((b : IsLocalRing.ResidueField R) ^ kb))) := by
    intro e
    rw [map_mul, mul_pow, ← D.toAN_eq_algebraMap, D.tauN_toAN,
      ← map_pow (PerfectClosure.of (IsLocalRing.ResidueField R) p), tauN_mon_pow,
      ← map_mul (PerfectClosure.of (IsLocalRing.ResidueField R) p)]
  have hsplit : D.tauN N (∑ e ∈ s, algebraMap R (D.AN N) (r e) * D.mon N e)
      = ∑ e ∈ s, D.tauN N (algebraMap R (D.AN N) (r e) * D.mon N e) :=
    map_sum (D.tauN N) _ _
  rw [hsplit, sum_pow_char_pow]
  rw [Finset.sum_congr rfl (fun e _ => term e)]
  exact (map_sum (PerfectClosure.of (IsLocalRing.ResidueField R) p) _ _).symm

end Work.DSG4b.gonfPerfect.keyAux
