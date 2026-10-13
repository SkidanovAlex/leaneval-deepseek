import Mathlib
import Submission.Work.DSMap.Mix2
import Submission.Work.DSM5b.Basic
import Submission.Work.DSM5b.PerfComplexDefs
import Submission.Work.DSM5b.H0Defs
import Submission.Work.DSM5b.perfChartRing_pow_p_mem_iff
import Submission.Work.DSM5b.chartCechH0_root_killing
import Submission.Work.DSM5b.perfCechCoordEquiv
import Submission.Work.DSM5b.honestCechCoordEquiv
import Submission.Work.DSM5b.PCd_pow_isCycle
import Submission.Work.DSM5b.rootBookkeeping

/-!
# DSM5b — the `H⁰` half of M5b

## The route formalised here (for `perfChartH0_root_killing`)

1. **Coordinates** (`perfCechCoordEquiv`, `honestCechCoordEquiv`): the degree-`0` terms of the Čech
   complexes of the perfected and of the honest chart presheaves are identified with the concrete
   tuple complexes `PCX p t 0` and `HCX t 0` of `PerfComplexDefs`/`H0Defs`, compatibly with the
   coaugmentations and with the cycle condition (`PCd p t 0`, `HCd t 0`).
2. **The `p^e`-th power lift** (`PCd_pow_isCycle`): if `Z` is a `PCd`-cycle and `e` is a level at
   which all its components are honest, then the componentwise `p^e`-th powers form an `HCd`-cycle
   `Y` (Freshman's dream in the chart localisations).
3. **The honest input** (`chartCechH0_root_killing`): the honest chart Čech complex has
   `ϖ k`-almost surjective `H⁰`; applied to the honest cycle obtained from `Y` under the coordinate
   equivalence, it yields `ϖ k • Y = HCcoaug t w` for some `w : R`.
4. **Root bookkeeping** (`rootBookkeeping`): applying the `p^e`-th root map componentwise to
   `ϖ k • Y = HCcoaug t w` and multiplying by the missing power of `ϖ (k+e)` turns it into
   `ϖ k • Z = PCcoaug p t w'` for the single `w' = (ϖ (k+e))^(p^e - 1) * ψ^e w`, using
   `ϖ k = (ϖ (k+e))^(p^e)`.
5. Transporting back along the coordinate equivalence gives the statement.

Steps 2 and 4 are the "Frobenius upgrade" of the design in the only form in which it is valid: the
root map is applied to the *equation* (not to a cycle of the complex), and the multiplier is
readjusted by the tower relation.  Note in particular that the naive upgrade of a *power* killing
`(ϖ k)^m z = e w` to the single factor is not available; what is used instead is the honest
statement of step 3, in which the multiplier is `ϖ k` from the start.
-/

namespace Work.DSM5b

open CategoryTheory DSMap DSMap.Mix DSMap.Mix2
open Opposite Limits
open scoped Simplicial

universe a

/-- **M5b, almost surjectivity of the coaugmentation.** Every descent datum for the perfected chart
cover of `Bl_{(t)} R` (i.e. every `0`-cycle of the Čech complex) is, after multiplication by the
`p`-power root `ϖ k = T ^ (1/p^k)` of `T`, in the image of the coaugmentation `R → ∏_i R[J/t_i]`.

Route: inverting `ϖ k` makes the `t_i` generate the unit ideal of `R[1/ϖ k]` (since `t j₀ = T^e`),
the localised chart rings become `R[1/(ϖ k * t_S)]`, and the localised complex is the Amitsur
complex of the covering family `{D(t_i)}` of `Spec R[1/ϖ k]`; its `H⁰` is `R[1/ϖ k]` via the
coaugmentation, so `z/1 = e(w')` for some `w' ∈ R[1/ϖ k]`, and clearing the denominator
(`∃m, ϖ k^m * z = e(w)`, `w = ϖ k^m * w' ∈ R`) gives *power* killing.  The upgrade to the single
factor `ϖ k` uses the componentwise Frobenius (`x ↦ x^p`) and its inverse, the `p`-th root map,
which exists because `R` is perfect (and the perfected chart rings are stable under it): applying
the `j`-th root map with `p^j ≥ m` and then the `j`-th power map, bookkeeping the `ϖ (k+j)`-powers,
uses `ϖ k = (ϖ (k+j))^(p^j)` to turn `m`-fold killing into killing by `ϖ k`.

Do NOT use the frozen sorried declaration `DSMap.Mix2.area_M5b`. -/
theorem perfChartH0_root_killing (p : ℕ) [Fact p.Prime] (R : Type a) [CommRing R] [CharP R p]
    [PerfectRing R p] {ι : Type a} [Finite ι] [DecidableEq ι] (t : ι → R) (T : R) (j₀ : ι) (e : ℕ)
    (hj₀ : t j₀ = T ^ e) (k : ℕ)
    (z : ((cechComplexFunctor (chartIdx ι)).obj (perfChartPresheaf p t)).X 0)
    (hz : ((cechComplexFunctor (chartIdx ι)).obj (perfChartPresheaf p t)).d 0 1 z = 0) :
    ∃ w : R, (frobeniusEquiv R p).symm^[k] T • z = (perfChartCoaug p t).hom w := by
  -- 1. the coordinate equivalences
  obtain ⟨Φp, hcoaugP, hcycP⟩ := perfCechCoordEquiv p R t
  obtain ⟨Φh, hcoaugH, hcycH⟩ := honestCechCoordEquiv R t
  -- 2. the concrete perfected cycle
  set Z : PCX p t 0 := Φp z with hZdef
  have hZcyc : PCd p t 0 Z = 0 := (hcycP z).mp hz
  -- 3. a uniform level at which all components of `Z` are honest
  haveI : Fintype ι := Fintype.ofFinite ι
  choose ee hee using fun τ : Fin 1 → ι =>
    (mem_perfChartRing_iff p t (tupRng τ)).mp (Z τ).2
  set e' : ℕ := Finset.univ.sup ee with he'def
  have he' : ∀ τ : Fin 1 → ι,
      (Z τ : Localization.Away (tS t (tupRng τ))) ^ (p ^ e') ∈ chartRing t (tupRng τ) :=
    fun τ => perfChartGens_mono p t (tupRng τ) (Finset.le_sup (Finset.mem_univ τ)) (hee τ)
  -- 4. the honest concrete cycle given by the `p^e'`-th powers
  set Y : HCX t 0 :=
    fun τ => ⟨(Z τ : Localization.Away (tS t (tupRng τ))) ^ (p ^ e'), he' τ⟩ with hYdef
  have hYcyc : HCd t 0 Y = 0 := PCd_pow_isCycle p t e' Z hZcyc he'
  -- 5. transport to the honest Čech complex and apply the honest statement
  set y : ((cechComplexFunctor (chartIdx ι)).obj (chartPresheaf t)).X 0 := Φh.symm Y with hydef
  have hycyc : ((cechComplexFunctor (chartIdx ι)).obj (chartPresheaf t)).d 0 1 y = 0 :=
    (hcycH y).mpr (by rw [hydef, LinearEquiv.apply_symm_apply]; exact hYcyc)
  obtain ⟨w, hw⟩ := chartCechH0_root_killing p R t T j₀ e hj₀ k y hycyc
  -- 6. transport the honest killing equation back
  have hwY : (frobeniusEquiv R p).symm^[k] T • Y = HCcoaug t w := by
    have h1 := congrArg (fun q => Φh q) hw
    rw [map_smul] at h1
    rw [show Φh y = Y from by rw [hydef, LinearEquiv.apply_symm_apply]] at h1
    rw [hcoaugH w] at h1
    exact h1
  -- 7. root bookkeeping
  obtain ⟨w', hw'⟩ := rootBookkeeping p t T k Z e' he' w hwY
  -- 8. transport back to the perfected Čech complex
  refine ⟨w', ?_⟩
  have h2 := congrArg (fun q => Φp.symm q) hw'
  rw [map_smul] at h2
  rw [show Φp.symm Z = z from by rw [hZdef, LinearEquiv.symm_apply_apply]] at h2
  have h3 : Φp.symm (PCcoaug p t w') = (perfChartCoaug p t).hom w' := by
    have hco : Φp ((perfChartCoaug p t).hom w') = PCcoaug p t w' := hcoaugP w'
    rw [← hco]
    exact LinearEquiv.symm_apply_apply Φp _
  rw [h3] at h2
  exact h2

end Work.DSM5b
