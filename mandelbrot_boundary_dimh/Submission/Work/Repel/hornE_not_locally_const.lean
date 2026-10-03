import Mathlib
import Submission.Work.Interfaces.Parabolic
import Submission.Work.Horn.E_not_locally_const
import Submission.Work.Horn.false_of_const_on_upper_unbounded
import Submission.Work.Horn.false_of_const_on_lower_unbounded
import Submission.Work.L62.basin_iface

namespace Work.Repel

open MandelDim Set Metric Filter

/-!
# `d.E` is nowhere locally constant on `hd.Bu ∪ hd.Bl`

The lifted horn map `E = Φ ∘ φ` of a `ParabData` is analytic on `DE = φ⁻¹(basin)` and, by the
`HornData` fields `surj_u`/`surj_l`, surjective from *each* of the two `T`-invariant components
`Bu`, `Bl` onto `ℂ` (these components are the relevant pieces of `DE`, cf. `hd.sub`).

If `E` were constant (necessarily `= E w`) on a neighbourhood of `w ∈ Bu ∪ Bl`, the identity
principle for analytic functions on the connected component `C` of `DE` through `w` would make `E`
equal to `E w` on all of `C`.  Since `Bu` (resp. `Bl`) is connected, contains `w` and is contained
in `DE`, it is contained in `C`; but `surj_u` (resp. `surj_l`) produces `w' ∈ Bu` (resp. `Bl`) with
`E w' = E w + 1`, which lies in `C` and contradicts `E w' = E w`.

(This replaces the slightly stronger hypotheses of `Work.Horn.E_not_locally_const`, where `Bu`,
`Bl` are given as explicit connected components, by the abstract `HornData` fields; the analytic
continuation step is the same, and the surjectivity fields of `HornData` do the rest.)
-/

theorem hornE_not_locally_const {f₀ : ℂ → ℂ} {D₀ : Set ℂ} (d : MandelDim.ParabData f₀ D₀)
    (hd : MandelDim.HornData d) :
    ∀ w ∈ hd.Bu ∪ hd.Bl, ¬ (∀ᶠ u in nhds w, d.E u = d.E w) := by
  intro w hw hconst
  have hwDE : w ∈ d.DE := hd.sub hw
  have hDEopen : IsOpen d.DE := by
    rw [show d.DE = d.Dφ ∩ d.φ ⁻¹' MandelDim.ParabolicBasin f₀ D₀ from rfl]
    exact d.φ_holo.continuousOn.isOpen_inter_preimage d.Dφ_open
      (Work.L62.isOpen_parabolicBasin f₀ D₀)
  have hAn : AnalyticOnNhd ℂ d.E (connectedComponentIn d.DE w) := fun x hx =>
    (Work.Horn.differentiableOn_E d).analyticAt
      (hDEopen.mem_nhds (connectedComponentIn_subset d.DE w hx))
  -- identity principle: `E ≡ E w` on the whole component of `d.DE` through `w`
  have hconstC : EqOn d.E (fun _ => d.E w) (connectedComponentIn d.DE w) :=
    AnalyticOnNhd.eqOn_of_preconnected_of_eventuallyEq hAn analyticOnNhd_const
      isPreconnected_connectedComponentIn (mem_connectedComponentIn hwDE)
      (show d.E =ᶠ[nhds w] (fun _ => d.E w) from hconst)
  rcases hw with hwBu | hwBl
  · obtain ⟨w', hw'Bu, hw'E⟩ := hd.surj_u (d.E w + 1)
    have hw'C : w' ∈ connectedComponentIn d.DE w :=
      hd.Bu_conn.isPreconnected.subset_connectedComponentIn hwBu
        (fun x hx => hd.sub (Or.inl hx)) hw'Bu
    have h1 : d.E w + 1 = d.E w := by rw [← hw'E]; exact hconstC hw'C
    have h2 : (1 : ℂ) = 0 := by simpa using sub_eq_zero.mpr h1
    exact one_ne_zero h2
  · obtain ⟨w', hw'Bl, hw'E⟩ := hd.surj_l (d.E w + 1)
    have hw'C : w' ∈ connectedComponentIn d.DE w :=
      hd.Bl_conn.isPreconnected.subset_connectedComponentIn hwBl
        (fun x hx => hd.sub (Or.inr hx)) hw'Bl
    have h1 : d.E w + 1 = d.E w := by rw [← hw'E]; exact hconstC hw'C
    have h2 : (1 : ℂ) = 0 := by simpa using sub_eq_zero.mpr h1
    exact one_ne_zero h2

end Work.Repel
