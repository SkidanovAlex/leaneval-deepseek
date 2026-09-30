import Mathlib
import Submission.Work.BW.GradedHilbDefs
import Submission.Work.BW.BWGradedBase
import Submission.Work.BW.count_eq_primLen
import Submission.Work.BW.hilbIdeal_colon_add
import Submission.Work.BW.homogeneous_colon_prime
import Submission.Work.BW.colon_localize_length_add

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

namespace Work.BW

open MvPolynomial

/-! ## Auxiliary statements (temporarily local; will be imported) -/

/-! ## The graded prime series -/

/-- `J` admits a graded prime series: finitely many homogeneous primes `P j ⊇ J`, shifts
`E j`, giving the graded pieces of `R/J` and matching the lengths of the localizations. -/
private def HasSeries (N : ℕ) (J : Ideal (MR N)) : Prop :=
  ∃ (k : ℕ) (P : Fin k → Ideal (MR N)) (E : Fin k → Fin (N + 1) →₀ ℕ),
    (∀ j, (P j).IsPrime) ∧ (∀ j, MultiHomZ N (P j)) ∧ (∀ j, J ≤ P j) ∧
    (∀ u : Fin (N + 1) →₀ ℤ,
      hilbIdeal N J u = ∑ j, hilbIdeal N (P j) (u - castF (E j))) ∧
    (∀ (q : Ideal (MR N)) (hq : q.IsPrime), J ≤ q →
      locLenAt q hq J = ∑ j, locLenAt q hq (P j))

private theorem hasSeries_top (N : ℕ) : HasSeries N ⊤ := by
  refine ⟨0, Fin.elim0, Fin.elim0, ?_, ?_, ?_, ?_, ?_⟩
  · intro j; exact j.elim0
  · intro j; exact j.elim0
  · intro j; exact j.elim0
  · intro u
    rw [hilbIdeal_top]
    simp
  · intro q hq hle
    have hmap : (⊤ : Ideal (MR N)).map (algebraMap (MR N) (Localization.AtPrime q)) = ⊤ :=
      Ideal.map_top _
    rw [show locLenAt q hq ⊤ = Module.length (Localization.AtPrime q)
        (Localization.AtPrime q ⧸ (⊤ : Ideal (MR N)).map
          (algebraMap (MR N) (Localization.AtPrime q))) from rfl, hmap]
    rw [Module.length_eq_zero]
    simp

private theorem hasSeries_of_le (N : ℕ) (I J : Ideal (MR N)) (hIJ : I ≤ J)
    (hJ : MultiHomZ N J) : HasSeries N J := by
  by_contra hcon
  have hS : ({J' : Ideal (MR N) | I ≤ J' ∧ MultiHomZ N J' ∧ ¬ HasSeries N J'}).Nonempty :=
    ⟨J, hIJ, hJ, hcon⟩
  obtain ⟨J₀, hJ₀max⟩ := WellFoundedGT.exists_maximal (α := Ideal (MR N))
    (inferInstance : WellFoundedGT (Ideal (MR N)))
    ({J' : Ideal (MR N) | I ≤ J' ∧ MultiHomZ N J' ∧ ¬ HasSeries N J'}) hS
  obtain ⟨⟨hIJ₀, hJ₀hom, hJ₀not⟩, hJ₀maximal⟩ := hJ₀max
  have hJ₀ne : J₀ ≠ ⊤ := fun htop => hJ₀not (htop ▸ hasSeries_top N)
  obtain ⟨d, x, hxd, hxJ₀, hpprime, hphom, hJ₀leP⟩ := homogeneous_colon_prime J₀ hJ₀hom hJ₀ne
  have hxpiece : x ∈ pieceZ N (castF d) := homPiece_eq_pieceZ d ▸ hxd
  have hJ'hom : MultiHomZ N (J₀ ⊔ Ideal.span {x}) :=
    MultiHomZ.sup hJ₀hom (MultiHomZ.span_singleton hxpiece)
  have hxJ' : x ∈ J₀ ⊔ Ideal.span {x} :=
    Submodule.mem_sup_right (Ideal.mem_span_singleton_self x)
  have hnotS : ¬ (I ≤ J₀ ⊔ Ideal.span {x} ∧ MultiHomZ N (J₀ ⊔ Ideal.span {x}) ∧
      ¬ HasSeries N (J₀ ⊔ Ideal.span {x})) := by
    rintro ⟨h1, h2, h3⟩
    have hle : J₀ ⊔ Ideal.span {x} ≤ J₀ := hJ₀maximal ⟨h1, h2, h3⟩ le_sup_left
    exact hxJ₀ (hle hxJ')
  have hIJ' : I ≤ J₀ ⊔ Ideal.span {x} := hIJ₀.trans le_sup_left
  have hJ'has : HasSeries N (J₀ ⊔ Ideal.span {x}) := by
    by_contra hh
    exact hnotS ⟨hIJ', hJ'hom, hh⟩
  obtain ⟨k, P, E, hprime, hhom, hle, hhilb, hlen⟩ := hJ'has
  have hspan_le : Ideal.span {x} ≤ J₀ ⊔ Ideal.span {x} := le_sup_right
  refine hJ₀not ⟨k + 1, Fin.cons (colonSpan J₀ x) P, Fin.cons d E, ?_, ?_, ?_, ?_, ?_⟩
  · exact Fin.cases hpprime (fun i => hprime i)
  · exact Fin.cases hphom (fun i => hhom i)
  · refine Fin.cases hJ₀leP (fun i => ?_)
    exact le_sup_left.trans (hle i)
  · intro u
    rw [hilbIdeal_colon_add J₀ hJ₀hom d x hxd u, hhilb u, Fin.sum_univ_succ]
    simp [Fin.cons_zero, Fin.cons_succ]
  · intro q hq hJ₀q
    rw [colon_localize_length_add q hq J₀ x, Fin.sum_univ_succ]
    by_cases hxq : x ∈ q
    · have hJ'q : J₀ ⊔ Ideal.span {x} ≤ q :=
        sup_le hJ₀q (Ideal.span_le.mpr (by rintro y rfl; exact hxq))
      rw [hlen q hq hJ'q]
      simp [colonSpan, Fin.cons_zero, Fin.cons_succ]
    · have hnotle : ¬ J₀ ⊔ Ideal.span {x} ≤ q := fun h => hxq (h hxJ')
      rw [locLenAt_eq_zero_of_not_le q hq _ hnotle]
      have hsum0 : (∑ j : Fin k, locLenAt q hq (P j)) = 0 := by
        refine Finset.sum_eq_zero fun j _ => locLenAt_eq_zero_of_not_le q hq _ ?_
        exact fun hle' => hnotle ((hle j).trans hle')
      simp only [Fin.cons_zero, Fin.cons_succ, hsum0, add_zero]

/-- Multigraded prime series with length multiplicities. For a multihomogeneous ideal `I` of
`MR N` there are finitely many homogeneous primes `P j ⊇ I` and shifts `E j ∈ ℕ^{N+1}` such that
the graded pieces of `R/I` decompose as the sum of the (shifted) graded pieces of the `R / P j`, and
such that every minimal prime `q` of `I` occurs exactly `length((R/I)_q)` times.

Suggested route. (1) Existence of a *graded* series: work with the module `M` equal to `R/I` graded
by the images of `pieceZ N u`, use well-founded induction on the submodules of `M` (as in Mathlib's
proof of `IsNoetherianRing.exists_relSeries_isQuotientEquivQuotientPrime`, via
`WellFoundedGT.induction_top`): for a graded `N ⊆ M` with `M/N ≠ 0` choose a nonzero *homogeneous*
element `x` of `M/N` whose annihilator `p` is maximal among annihilators of nonzero homogeneous
elements (exists by ACC); then `p` is a prime ideal and is homogeneous, `R x ≅ (R/p)(-d)` for `d`
the degree of `x` as graded modules, and one recurses on `M/(N + Rx)`. Equivalently: a strictly
increasing chain `I = J 0 ⊆ J 1 ⊆ ... ⊆ J k = ⊤` of multihomogeneous ideals where `J (j+1)` is
`J j + (x j)` and `(J (j+1))/J j ≅ (R / p j)(-d j)`.
(2) The graded exact sequences of the chain give, on graded pieces, `hilbIdeal N I u` as the sum of
the `hilbIdeal N (P j) (u - castF (E j))`.
(3) Count: for `q ∈ I.minimalPrimes`, localize the series at `q`; lengths are additive over the
filtered localizations (`Module.length_eq_add_of_exact`), `length((R/P j)_q)` is `1` when `P j = q`
and `0` otherwise (if `P j ⊄ q` the localization vanishes; `P j ⊊ q` is impossible because `P j ⊇ I`
and `q` is minimal over `I`), so the number of occurrences of `q` equals
`primLen I q = length((R/I)_q)`, which is finite since `(R/I)_q` is a zero dimensional local ring. -/
theorem exists_graded_prime_series (N : ℕ) (I : Ideal (MR N)) (hI : MultiHom N I) :
    ∃ (k : ℕ) (P : Fin k → Ideal (MR N)) (E : Fin k → (Fin (N + 1) →₀ ℕ)),
      (∀ j, (P j).IsPrime) ∧ (∀ j, MultiHom N (P j)) ∧ (∀ j, I ≤ P j) ∧
      (∀ u : Fin (N + 1) →₀ ℤ,
        hilbIdeal N I u = ∑ j, hilbIdeal N (P j) (u - castF (E j))) ∧
      (∀ q ∈ I.minimalPrimes,
        (Finset.univ.filter (fun j : Fin k => P j = q)).card = (primLen I q).toNat) := by
  obtain ⟨k, P, E, hprime, hhom, hle, hhilb, hlen⟩ :=
    hasSeries_of_le N I I le_rfl ((multiHom_iff_multiHomZ I).mp hI)
  refine ⟨k, P, E, hprime, ?_, hle, hhilb, ?_⟩
  · intro j
    exact (multiHom_iff_multiHomZ (P j)).mpr (hhom j)
  · intro q hq
    exact count_eq_primLen I k P hprime hle hlen q hq

end Work.BW
