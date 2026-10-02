import Mathlib
import Submission.Work.SeedDyn.Defs
import Submission.Work.ELTop.Defs
import Submission.Work.ELRig.Pa_subset_K

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


namespace Work.SeedDyn.PortraitCount

open LeanEval.ComplexAnalysis (Tantibar Mandelbar)
open Filter

/-! ## Two elementary ingredients of the critical-value portrait count

`noRayAtCritValue_of_flower` says that no external ray of `T_c` lands at the critical value `c`
of a root-parabolic parameter, as soon as the critical orbit eventually enters the attracting
petal `Pa` of the Leau--Fatou flower at the parabolic point `z₁`.

The two facts used are

* `boundedOrbit_of_iterate_Tantibar` — the filled Julia set `K c` is backward invariant under the
  iterates of `T_c` (a bounded forward orbit stays bounded after dropping finitely many terms);
* `landsN_notMem_interior` — a landing point of a ray is a limit of ray points, which all lie off
  `K c`, hence is not an interior point of `K c`.

The proof then shows that, because `Pa ⊆ K c` (`Work.ELRig.Pa_subset_K`) is open and
`(F c)^[N] c ∈ Pa`, a whole neighbourhood of `c` is mapped into `K c`; backward invariance of
`K c` then puts `c` in `interior (K c)`, contradicting a landing at `c`. -/

/-- **Backward invariance of the filled Julia set.**  If the `n`-th `T_c`-iterate of `z` has a
bounded orbit, then so does `z`: the first `n` terms of the orbit of `z` are finitely many, and
from index `n` on the orbit of `z` is the orbit of `(T_c)^[n] z`. -/
theorem boundedOrbit_of_iterate_Tantibar {c z : ℂ} {n : ℕ}
    (h : Work.ParamRays.BoundedOrbit c ((Tantibar c)^[n] z)) :
    Work.ParamRays.BoundedOrbit c z := by
  obtain ⟨M, hM⟩ := h
  refine ⟨max M (∑ j ∈ Finset.range n, ‖Work.ParamRays.orbit c z j‖), fun k => ?_⟩
  rcases lt_or_ge k n with hk | hk
  · refine le_trans ?_ (le_max_right _ _)
    exact Finset.single_le_sum (fun i _ => norm_nonneg _) (Finset.mem_range.mpr hk)
  · have hk' : k = n + (k - n) := by omega
    rw [hk', Work.ParamRays.orbit_add]
    have he : Work.ParamRays.orbit c z n = (Tantibar c)^[n] z := rfl
    rw [he]
    exact le_trans (hM (k - n)) (le_max_left _ _)

/-- **A landing point is not an interior point of the filled Julia set.**  The ray points of level
`t > 1` all lie outside `K c` (`Work.EL.rayPt_notMem_K`), and they converge to the landing point,
so the landing point lies in the closure of `(K c)ᶜ = (interior (K c))ᶜ`. -/
theorem landsN_notMem_interior {c : ℂ} {φ : ℂ → ℂ} (hN : Work.EL.DynB c φ) {θ : ℝ} {y : ℂ}
    (hland : Work.EL.LandsN hN θ y) : y ∉ interior (Work.EL.K c) := by
  have hcl : y ∈ closure ((Work.EL.K c)ᶜ) :=
    mem_closure_of_tendsto hland (by
      filter_upwards [self_mem_nhdsWithin] with t ht
      exact Work.EL.rayPt_notMem_K hN ht)
  intro hint
  obtain ⟨w, hw⟩ := mem_closure_iff.mp hcl (interior (Work.EL.K c)) isOpen_interior hint
  exact hw.2 (interior_subset hw.1)

/-- **No external ray lands at the critical value of a root-parabolic parameter whose critical
orbit enters the parabolic petal.**  Since `Pa ⊆ K c` (open) and some iterate of `F c = (T_c)^[10]`
maps `c` into `Pa`, a neighbourhood of `c` is mapped into `K c` and hence (backward invariance of
`K c`) lies in `K c`: `c ∈ interior (K c)`.  But a landing point is never an interior point of
`K c`, so no ray can land at `c`. -/
theorem noRayAtCritValue_of_flower {c : ℂ} (d : Work.EL.RootParabolic c)
    (fl : Work.EL.ParabolicFlower (Work.EL.F c) ((LeanEval.ComplexAnalysis.Tantibar c)^[5]) d.z₁)
    (henter : ∃ N : ℕ, (Work.EL.F c)^[N] c ∈ fl.Pa) :
    ∀ θ : ℝ, ¬ Work.EL.LandsN d.hN θ c := by
  have hPaK : fl.Pa ⊆ Work.EL.K c := Work.ELRig.Pa_subset_K fl
  have hcint : c ∈ interior (Work.EL.K c) := by
    obtain ⟨N, hNmem⟩ := henter
    have hTsq : Continuous (Work.Landing.Tsq c) := by
      rw [show Work.Landing.Tsq c = fun z => (z ^ 2 + star c) ^ 2 + c from rfl]
      fun_prop
    have hcont : Continuous ((Work.EL.F c)^[N]) := by
      rw [Work.EL.F]
      exact (hTsq.iterate 5).iterate N
    have hopen : IsOpen (((Work.EL.F c)^[N]) ⁻¹' fl.Pa) := fl.isOpen_Pa.preimage hcont
    refine interior_maximal ?_ hopen hNmem
    intro z hz
    have hPK : Work.ParamRays.BoundedOrbit c ((Work.EL.F c)^[N] z) := hPaK hz
    have he : (Work.EL.F c)^[N] z = (Tantibar c)^[10 * N] z := by
      rw [Work.EL.F_eq_tantibar, Function.iterate_mul]
    have hb : Work.ParamRays.BoundedOrbit c ((Tantibar c)^[10 * N] z) := he ▸ hPK
    exact boundedOrbit_of_iterate_Tantibar hb
  intro θ hland
  exact landsN_notMem_interior d.hN hland hcint

end Work.SeedDyn.PortraitCount
