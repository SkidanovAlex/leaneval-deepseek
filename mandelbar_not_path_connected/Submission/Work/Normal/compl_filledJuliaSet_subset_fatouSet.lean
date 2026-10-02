import Mathlib
import Submission.Work.Normal.Basic
import Submission.Work.Normal.escapeRadius
import Submission.Work.Normal.filledJulia_locallyUniform_escape
import Submission.Work.Normal.exists_const_subseq_or_tendsto_atTop
import Submission.Work.Normal.isNormalFamily_of_tendsto_iterate

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


namespace Work.Normal

open Filter Set Topology Function
open scoped Topology

/-! ### Normality from locally uniform divergence to `∞`

The basic input for this file: if the sequence of iterates of `f` tends to `∞` locally uniformly
on `U`, then the family of iterates of `f` is normal on `U`.  The point is that an arbitrary
sequence `f ^[k n]` of iterates either has `k → ∞` (in which case it still tends to `∞` locally
uniformly, since local uniform divergence only depends on the "far" indices) or `k` takes some
value infinitely often (in which case a subsequence of iterates is constant, hence convergent). -/

/-- Local uniform divergence to `∞` is preserved by reindexing with a map tending to `atTop`. -/
theorem TendstoLocallyUniformlyAtTop.comp_atTop {F : ℕ → ℂ → ℂ} {U : Set ℂ} {τ : ℕ → ℕ}
    (h : TendstoLocallyUniformlyAtTop F U) (hτ : Tendsto τ atTop atTop) :
    TendstoLocallyUniformlyAtTop (fun n => F (τ n)) U := by
  intro K hKU hK R
  obtain ⟨N, hN⟩ := h K hKU hK R
  rw [tendsto_atTop_atTop] at hτ
  obtain ⟨a, ha⟩ := hτ N
  exact ⟨a, fun n hn z hz => hN (τ n) (ha n hn) z hz⟩

/-- If the iterates of `f` tend to `∞` locally uniformly on `U`, then the family of iterates of
`f` is normal on `U`. -/
theorem isNormalFamily_of_tendstoLocallyUniformlyAtTop_iterate {f : ℂ → ℂ} {U : Set ℂ}
    (h : TendstoLocallyUniformlyAtTop (fun n : ℕ => f^[n]) U) :
    IsNormalFamily (iterateFamily f) U := by
  classical
  intro u hu
  -- every member of the iterate family is an iterate `f ^[k n]`
  choose k hk using fun n => hu n
  rcases exists_const_subseq_or_tendsto_atTop k with ⟨m, hm⟩ | hktop
  · -- some iterate `f ^[m]` occurs infinitely often: a constant subsequence converges
    have hfreq : ∃ᶠ n in atTop, k n = m := by
      rw [frequently_atTop]
      intro a
      obtain ⟨n, hn, hkn⟩ := hm a
      exact ⟨n, le_of_lt hn, hkn⟩
    obtain ⟨φ, hφ, hφk⟩ := extraction_of_frequently_atTop hfreq
    refine ⟨φ, hφ, Or.inl ⟨f^[m], ?_⟩⟩
    have hconst : TendstoLocallyUniformlyOn (fun _ : ℕ => (f^[m] : ℂ → ℂ)) (f^[m]) atTop U :=
      tendstoLocallyUniformlyOn_const_fun (f^[m]) U
    refine hconst.congr fun n z _ => ?_
    show (f^[m]) z = u (φ n) z
    rw [← hk (φ n), hφk n]
  · -- the indices escape to `∞`: the subsequence still tends locally uniformly to `∞`
    refine ⟨id, strictMono_id, Or.inr ?_⟩
    have h1 : TendstoLocallyUniformlyAtTop (fun n => f^[k n]) U := h.comp_atTop hktop
    have h2 : (fun n => u (id n)) = fun n => f^[k n] := funext fun n => (hk n).symm
    rw [h2]
    exact h1

/-- The complement of the filled Julia set of a polynomial map of degree at least two is contained
in the Fatou set: there the iterates tend locally uniformly to `∞`.

Route: `escapeRadius` gives, for each escaping point `z`, an open neighbourhood on which
`fun n => f^[n]` tends locally uniformly to `∞` (see `filledJulia_locallyUniform_escape`).  Every
sequence of iterates on that neighbourhood has a subsequence whose indices are either bounded
(hence a constant subsequence) or tend to `∞` (hence again tend locally uniformly to `∞`), so the
iterate family is normal. -/
theorem compl_filledJuliaSet_subset_fatouSet {d : ℕ} {f : ℂ → ℂ} (hd : 2 ≤ d)
    (hf : IsPolynomialMapOfDegree d f) : (FilledJuliaSet f)ᶜ ⊆ FatouSet f := by
  obtain ⟨R, hR2, hRf, -, hesc, -, -, -⟩ := escapeRadius hd hf
  intro z hz
  obtain ⟨U, hUmem, hUo, hUlim⟩ := hesc z hz
  exact fatouSet_of_mem_nhds hUmem hUo
    (isNormalFamily_of_tendstoLocallyUniformlyAtTop_iterate hUlim)

end Work.Normal
