import Mathlib
import Submission.Work.SpecLin.Points.Basic
import Submission.Work.SpecLin.Core.linEquiv_of_sections
import Submission.Work.SpecLin.Core.linEquiv_of_sections_of_chart
import Submission.Work.SpecLin.Alt.conservationNumber
import Submission.Work.SpecLin.Content.isPrincipal_of_fg_of_cyclic_map_quotient
import Submission.Work.SpecLin.Core.section_prime_sup_fibre_quot
import Submission.Work.SpecLin.Core.sectionEquation
import Submission.Work.SpecLin.Core.module_free_chartTensor
import Submission.Work.CurveBasics.Basic
import Submission.Work.SpecLin.Alt.exists_mem_sectionPrime_span_map_eq

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.


universe u

namespace Work.SpecLin.Setup

set_option linter.style.haveILetI false

/-- **The unit criterion in terms of the section equation.**  For a nonzero element `f` of a
domain `B` and a prime `p`, the element `f` (viewed in `FractionRing B`) is a unit at `p` if and
only if `f ∉ p`, i.e. if and only if the image of `f` in `B_p` is a unit. -/
private lemma isUnitAt_algebraMap_fractionRing_iff {B : Type u} [CommRing B] [IsDomain B]
    (f : B) (hf : f ≠ 0) (p : Ideal B) (hp : p.IsPrime) :
    Work.SpecLin.Alt.IsUnitAt (algebraMap B (FractionRing B) f) p ↔ f ∉ p := by
  have hι : algebraMap B (FractionRing B) f ≠ 0 := fun h =>
    hf (IsFractionRing.injective B (FractionRing B) (by simpa using h))
  constructor
  · -- If `f` is a unit at `p` then `f ∉ p`: otherwise `f` lies in the maximal ideal of `B_p`.
    rintro ⟨-, b, s, hs, hbs⟩
    intro hfp
    refine hs ?_
    have h1 : algebraMap B (FractionRing B) s = algebraMap B (FractionRing B) (f * b) := by
      rw [map_mul]
      have h := congrArg (fun y => algebraMap B (FractionRing B) f * y) hbs
      rw [← mul_assoc, mul_inv_cancel₀ hι, one_mul] at h
      exact h
    have hs_eq : s = f * b := IsFractionRing.injective B (FractionRing B) h1
    rw [hs_eq]
    exact Ideal.mul_mem_right b p hfp
  · -- Conversely `f ∉ p` exhibits both `f` and `f⁻¹` as fractions with denominator outside `p`.
    intro hfp
    refine ⟨⟨f, 1, (Ideal.ne_top_iff_one p).mp hp.ne_top, by simp⟩, 1, f, hfp, ?_⟩
    rw [map_one]; exact inv_mul_cancel₀ hι

/-- **Contraction of the local equation.**  If `I · B_N = (f) · B_N` inside `B_N` (`N` maximal)
and `p ≤ N` is a prime with `f ∈ p`, then `I ≤ p`: for `g ∈ I` the element `g · s = f · b` with
`s ∉ N`, and `s ∉ p`, so `g ∈ p` since `p` is prime. -/
private lemma le_of_mem_of_eq_span_map {B : Type u} [CommRing B] [IsDomain B]
    (I : Ideal B) (f : B) (N p : Ideal B) (hN : N.IsMaximal) (hp : p.IsPrime) (hpN : p ≤ N)
    (hmap : I.map (algebraMap B (Localization.AtPrime N)) =
      Ideal.span {algebraMap B (Localization.AtPrime N) f})
    (hf : f ∈ p) : I ≤ p := by
  haveI : N.IsPrime := hN.isPrime
  intro g hg
  have hmem : algebraMap B (Localization.AtPrime N) g ∈
      Ideal.span {algebraMap B (Localization.AtPrime N) f} := by
    rw [← hmap]; exact Ideal.mem_map_of_mem _ hg
  obtain ⟨c, hc⟩ := (Ideal.mem_span_singleton' (x := algebraMap B (Localization.AtPrime N) g)
    (y := algebraMap B (Localization.AtPrime N) f)).mp hmem
  obtain ⟨⟨b', s'⟩, hsa⟩ := IsLocalization.surj N.primeCompl c
  have hinj : Function.Injective (algebraMap B (Localization.AtPrime N)) :=
    IsLocalization.injective _ N.primeCompl_le_nonZeroDivisors
  have hgs : g * (s' : B) = f * b' := by
    apply hinj
    calc algebraMap B (Localization.AtPrime N) (g * (s' : B))
        = algebraMap B (Localization.AtPrime N) g
            * algebraMap B (Localization.AtPrime N) (s' : B) := map_mul _ _ _
      _ = (c * algebraMap B (Localization.AtPrime N) f)
            * algebraMap B (Localization.AtPrime N) (s' : B) := by rw [← hc]
      _ = algebraMap B (Localization.AtPrime N) f
            * (c * algebraMap B (Localization.AtPrime N) (s' : B)) := by ring
      _ = algebraMap B (Localization.AtPrime N) f
            * algebraMap B (Localization.AtPrime N) b' := by rw [hsa]
      _ = algebraMap B (Localization.AtPrime N) (f * b') := (map_mul _ _ _).symm
  have hs'p : (s' : B) ∉ p := fun h => s'.2 (hpN h)
  have hmem2 : g * (s' : B) ∈ p := by rw [hgs]; exact Ideal.mul_mem_right b' p hf
  rcases hp.mem_or_mem hmem2 with h | h
  · exact h
  · exact absurd h hs'p

/-- **A local equation of the section prime at a closed point of the special fibre.**

`I = sectionPrime R W (rgMap R W hW s hs) = ker (B →_K R)` is the prime of the generic point of
the section given by the `R`-point `s` of the chart `W`, and `N ⊇ P = chartFibrePrime R W` is a
maximal ideal of `B = Γ(C,W) ⊗[K] R`, i.e. a closed point of the chart `W_κ` of the special
fibre.  Then there is `f ∈ I` with `f ∉ P` which generates `I` locally at `N`:

  `I · B_N = f · B_N`.

Equivalently `I · B_N` is principal ("the section is a Cartier divisor at the closed points of
the special fibre"): if `I ⊔ P ≠ N` then `I · B_N = B_N` and `f` may be taken to be `1`; if
`I ⊔ P = N` then `B ⧸ (I ⊔ P) ≅ κ` (`Core.section_prime_sup_fibre_quot`) makes
`I ⧸ (N·I)` cyclic over `κ`, and Nakayama
(`Content.isPrincipal_of_fg_of_cyclic_map_quotient`) applies.

The last conjunct records the resulting *unit criterion* at every prime `p ≤ N`:
`f` is a unit of `B_p` if and only if `I ⊄ p`.  (It follows formally from the principality: if
`I ≤ p` then `f ∈ I ⊆ p`; if `I ⧸⊆ p` then `I · B_p = B_p` and `f` generates it.) -/
theorem sectionEquationPull {K : Type u} [Field K] {C : Work.CurveBasics.Curve K}
    (R : Type u) [CommRing R] [IsDomain R] [ValuationRing R] [Algebra K R]
    (W : C.left.Opens) (hW : AlgebraicGeometry.IsAffineOpen W)
    [Nonempty W] [IsDomain (Work.SpecLin.Core.chartTensor R W)]
    (s : Work.SpecLin.CurvePt C R)
    (hs : Set.range (s.left.base) ⊆ (W : Set C.left))
    (N : Ideal (Work.SpecLin.Core.chartTensor R W)) (hN : N.IsMaximal)
    (hPN : Work.SpecLin.Core.chartFibrePrime R W ≤ N) :
    ∃ f : Work.SpecLin.Core.chartTensor R W,
      f ∈ Work.SpecLin.Core.sectionPrime R W (Work.SpecLin.Core.rgMap R W hW s hs) ∧
      f ∉ Work.SpecLin.Core.chartFibrePrime R W ∧
      (Work.SpecLin.Core.sectionPrime R W (Work.SpecLin.Core.rgMap R W hW s hs)).map
          (algebraMap (Work.SpecLin.Core.chartTensor R W)
            (Localization.AtPrime N))
        = Ideal.span (singleton (algebraMap (Work.SpecLin.Core.chartTensor R W)
            (Localization.AtPrime N) f)) ∧
      (∀ p : Ideal (Work.SpecLin.Core.chartTensor R W), p.IsPrime → p ≤ N →
        (Work.SpecLin.Alt.IsUnitAt
            (algebraMap (Work.SpecLin.Core.chartTensor R W)
              (FractionRing (Work.SpecLin.Core.chartTensor R W)) f) p
          ↔ ¬ (Work.SpecLin.Core.sectionPrime R W
                (Work.SpecLin.Core.rgMap R W hW s hs) ≤ p))) := by
  haveI := hN
  obtain ⟨f, hfI, hfP, hmap⟩ :=
    Work.SpecLin.Alt.exists_mem_sectionPrime_span_map_eq R W hW s hs N hPN
  refine ⟨f, hfI, hfP, hmap, ?_⟩
  intro p hp hpN
  have hf0 : f ≠ 0 := fun h =>
    hfP (h.symm ▸ (Work.SpecLin.Core.chartFibrePrime R W).zero_mem)
  rw [isUnitAt_algebraMap_fractionRing_iff f hf0 p hp]
  constructor
  · intro hfp hIle
    exact hfp (hIle hfI)
  · intro hnot
    by_contra hfmem
    exact hnot (le_of_mem_of_eq_span_map _ f N p hN hp hpN hmap hfmem)

end Work.SpecLin.Setup
