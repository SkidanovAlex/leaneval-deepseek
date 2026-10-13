/-
  annals_wilkies_conjecture, hole `C4a_puiseux` (`PuiseuxReal`): the assembly.

  This file wires the pieces of the area into the deliverable
  `WilkiesDesign.CG.C4a.C4a_puiseux_proved : PuiseuxReal`:

  * `complexify_coeff` : complexification of the real-analytic coefficients;
  * `exists_analytic_root_of_simple` : the analytic implicit function statement;
  * `sqfree_branches` : the square-free case of the complex Puiseux statement (monodromy of
    the root covering plus removable singularities);
  * `exists_cluster_factor` : the analytic Hensel (cluster) splitting;
  * `complex_puiseux` : the general complex Puiseux statement;
  * `polyOf_basic`, `real_branches` : the polynomial attached to the complexified coefficients
    and the extraction of the real branches.
-/
import Submission.Work.WilC4aP.RealExtract
import Submission.Work.WilC4aP.complexify_coeff
import Submission.Work.WilC4aP.exists_analytic_root_of_simple
import Submission.Work.WilC4aP.sqfree_branches
import Submission.Work.WilC4aP.exists_cluster_factor
import Submission.Work.WilC4aP.complex_puiseux
import Submission.Work.WilC4aP.polyOf_basic
import Submission.Work.WilC4aP.real_branches

set_option autoImplicit false
noncomputable section
open Classical Topology Filter
open scoped BigOperators

namespace Work.WilC4aP

/-- The general complex Puiseux statement of this area, assembled from its holes. -/
theorem complexPuiseux_proved : ComplexPuiseux :=
  complex_puiseux
    (fun P hmon han α hα hder => exists_analytic_root_of_simple P hmon han hα hder)
    (fun P hmon hdeg han ρ₀ hρ₀ hsep => sqfree_branches P hmon hdeg han hρ₀ hsep)
    (fun P hmon hdeg han α k hroot hk => exists_cluster_factor P hmon hdeg han hroot hk)

end Work.WilC4aP

namespace WilkiesDesign.CG.C4a

open WilkiesDesign WilkiesConjecture

/-- **`C4a_puiseux`, the Puiseux statement used by `CG.C4a_rexp_polyBounded`.** The real
branches of the roots of `c d * Y ^ d + ⋯ + c 0` along `s = r ^ N` are real-analytic functions
of `r`; equivalently the real roots of `mpoly c (r ^ N)` are exactly the values of finitely
many real-analytic functions. -/
theorem C4a_puiseux_proved : PuiseuxReal := by
  intro d c hc
  classical
  -- complexify the coefficients
  choose F ρF hρF hFana hFc using fun j : Fin d => Work.WilC4aP.complexify_coeff (c j) (hc j)
  -- a common radius of holomorphy
  set ρ0 : ℝ := if h : (Finset.univ : Finset (Fin d)).Nonempty then Finset.univ.inf' h ρF
    else 1 with hρ0def
  have hρ0le : ∀ j : Fin d, ρ0 ≤ ρF j := by
    intro j
    rw [hρ0def]
    split_ifs with h
    · exact Finset.inf'_le _ (Finset.mem_univ j)
    · exact absurd ⟨j, Finset.mem_univ j⟩ h
  have hρ0pos : 0 < ρ0 := by
    rw [hρ0def]
    split_ifs with h
    · rw [Finset.lt_inf'_iff]
      exact fun j _ => hρF j
    · norm_num
  have hF' : ∀ j, AnalyticOnNhd ℂ (F j) (Metric.ball 0 ρ0) := fun j =>
    (hFana j).mono (Metric.ball_subset_ball (hρ0le j))
  have hFc' : ∀ j, ∀ x : ℝ, |x| < ρ0 → F j (x : ℂ) = (c j x : ℂ) := fun j x hx =>
    hFc j x (lt_of_lt_of_le hx (hρ0le j))
  -- the polynomial attached to the complexified coefficients
  have hF0 : ∀ j, AnalyticAt ℂ (F j) 0 := fun j =>
    (hFana j) 0 (by simpa [Metric.mem_ball] using hρF j)
  obtain ⟨hm, hdeg, hhol⟩ := Work.WilC4aP.polyOf_basic F hF0
  -- complex Puiseux
  obtain ⟨N, η, ρ, hN, hρ, hη, hfac⟩ :=
    Work.WilC4aP.complexPuiseux_proved (Work.WilC4aP.polyOf F) hm hdeg hhol
  -- real extraction
  obtain ⟨m, ζ, hζ, r0, hr0, hiff⟩ :=
    Work.WilC4aP.real_branches hρ0pos hF' hFc' hN hρ hη hfac
  exact ⟨N, m, ζ, hN, hζ, r0, hr0, hiff⟩

/-- Type check: `C4a_puiseux_proved` has the statement of the frozen hole `C4a_puiseux`. -/
example : PuiseuxReal := @C4a_puiseux_proved

/-- The frozen hole itself (`WilkiesDesign.CG.C4a.C4a_puiseux`), for comparison. -/
example : PuiseuxReal := @WilkiesDesign.CG.C4a.C4a_puiseux

end WilkiesDesign.CG.C4a
