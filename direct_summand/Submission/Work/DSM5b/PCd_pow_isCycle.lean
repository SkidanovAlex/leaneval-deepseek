import Mathlib
import Submission.Work.DSMap.Mix2
import Submission.Work.DSM5b.Basic
import Submission.Work.DSM5b.PerfComplexDefs
import Submission.Work.DSM5b.H0Defs
import Submission.Work.DSM5b.perfChartRing_pow_p_mem_iff

namespace Work.DSM5b

open CategoryTheory DSMap DSMap.Mix DSMap.Mix2
universe a

/-- **The `p^e`-th power of a perfected-concrete cycle is an honest-concrete cycle.**

`Z : PCX p t 0 = ∀ τ : Fin 1 → ι, perfChartRing p t (tupRng τ)` is a cycle of the concrete perfected
chart complex (`PCd p t 0 Z = 0`, see `Submission/Work/DSM5b/PerfComplexDefs.lean`) and `e` is a
level at which all its components are honest, i.e. `(Z τ)^{p^e} ∈ chartRing t (tupRng τ)` for every
`τ`. Then the componentwise `p^e`-th power family is a cycle of the honest concrete complex
`HCd t 0` of `Submission/Work/DSM5b/H0Defs.lean`.

Route: expand both differentials with `PCd_apply`/`HCd_apply`.  For each `σ : Fin 2 → ι`, the
`σ`-component of `PCd p t 0 Z` is `Σ i : Fin 2, (-1)^i • rho (Z (tupDel i σ)) = 0` (`Fin.sum_univ_two`
writes the two terms as `rho (Z (tupDel 0 σ)) - rho (Z (tupDel 1 σ))`).  The
`σ`-component of `HCd t 0 Y`, where `Y τ = ⟨(Z τ)^{p^e}, he τ⟩`, is
`rhoH (Y (tupDel 0 σ)) - rhoH (Y (tupDel 1 σ))`, and
`rhoH (Y (tupDel i σ)) = (rho (Z (tupDel i σ)))^{p^e}` as elements of `chartRing t (tupRng σ)`
(both sides are `locRes` of `(Z _)^{p^e}`; `Subtype.ext` and `map_pow`).  Hence the honest component
equals `(rho (Z (tupDel 0 σ)) - rho (Z (tupDel 1 σ)))^{p^e}`, by the Freshman's dream
`Work.DSM5b.add_pow_p_localization` (`(x + y)^(p^n) = x^(p^n) + y^(p^n)` in the localisation;
available in `Submission/Work/DSM5b/perfChartRing_pow_p_mem_iff.lean`, no `CharP` instance on the
localisation is needed), together with `(-x)^(p^e) = -x^(p^e)`.  That is `0^(p^e) = 0` by the cycle
hypothesis.  Work in the localisation and conclude with `Subtype.ext`. -/
theorem PCd_pow_isCycle (p : ℕ) [Fact p.Prime] {R : Type a} [CommRing R] [CharP R p]
    [PerfectRing R p] {ι : Type a} [DecidableEq ι] (t : ι → R) (e : ℕ) (Z : PCX p t 0)
    (hZ : PCd p t 0 Z = 0)
    (he : ∀ τ : Fin 1 → ι,
      (Z τ : Localization.Away (tS t (tupRng τ))) ^ (p ^ e) ∈ chartRing t (tupRng τ)) :
    HCd t 0 (fun τ => ⟨(Z τ : Localization.Away (tS t (tupRng τ))) ^ (p ^ e), he τ⟩) = 0 := by
  funext σ
  show HCd t 0 (fun τ => ⟨↑(Z τ) ^ (p ^ e), he τ⟩) σ = 0
  -- The cycle hypothesis, read in the localisation: the two terms of the `PCd`-component of `Z`
  -- cancel there.
  have hZc : (∑ i : Fin 2, (-1 : R) ^ ((i : ℕ)) •
      locRes t (tupRng_del_subset i σ) ↑(Z (tupDel i σ))) = 0 := by
    have h1 : (PCd p t 0 Z) σ = 0 := by rw [hZ]; rfl
    have h2 := congrArg (fun x : perfChartRing p t (tupRng σ) =>
      (x : Localization.Away (tS t (tupRng σ)))) h1
    rw [Subalgebra.coe_zero] at h2
    exact h2
  -- hence the two localised restrictions of `Z`'s components are equal
  have hg01 : locRes t (tupRng_del_subset 0 σ) ↑(Z (tupDel 0 σ))
      = locRes t (tupRng_del_subset 1 σ) ↑(Z (tupDel 1 σ)) := by
    have h := hZc
    rw [Fin.sum_univ_two] at h
    exact sub_eq_zero.mp (by simpa [sub_eq_add_neg] using h)
  apply Subtype.ext
  rw [HCd_apply, Subalgebra.coe_zero]
  -- push the coercion into the summation and rewrite each `rhoH`-term as the `p^e`-th power
  change (Subalgebra.val (chartRing t (tupRng σ)))
    (∑ i : Fin 2, (-1 : R) ^ ((i : ℕ)) • rhoH t (tupRng_del_subset i σ)
      ⟨↑(Z (tupDel i σ)) ^ (p ^ e), he (tupDel i σ)⟩) = 0
  rw [map_sum]
  simp only [map_smul, Subalgebra.val_apply, rhoH_coe, map_pow]
  -- two terms, and the two localised restrictions agree
  rw [Fin.sum_univ_two]
  rw [hg01]
  simp

end Work.DSM5b
