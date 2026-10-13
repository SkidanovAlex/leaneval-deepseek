/-
  WilG4c / CoreThin / core_thin.

  The four fibre cores of a definable function `h : ℝ^n → ℝ` (`FibreCoreDefs`) are *thin*:
  the closure of each of them has empty interior.

  The four families are

  * `fibCore h (.fbad i)   = fibBad h i`,
  * `fibCore h (.fbadJ i i') = fibBad (junkP h i) i'`,
  * `fibCore h (.discJ i)   = disc (junkP h i)`,
  * `fibCore h (.disc0)     = disc h`,

  so each of them is a fibre-non-differentiability set or a discontinuity locus of a function
  whose graph is `Ω`-definable (`h` itself and its junk partials `junkP h i`, whose definability
  is `junkIt_mem` / `junkPartial_mem`).  For such sets the chain of already established results is

  * `Junk.fibBad_mem` / `Junk.disc_mem`  — the set is an `Ω`-set (`b.eval D`);
  * `Junk.fibBad_thin_of_last` (with `partialBad_thin`), `generic_continuity` — it has empty
    interior;
  * `thin_closure` — an `Ω`-set of empty interior has `interior (closure ·) = ∅` (this is where
    `SharpCD` enters).
-/
import Mathlib
import Submission.Work.WilG4c.FibreCoreDefs
import Submission.Work.WilG1.Cell.smooth_k_cover

namespace Work.WilG4c.CoreThin

open WilkiesDesign
open Work.WilG1.Cell

/-- The graph of a junk partial of `h` is again `Ω`-definable, with the bound still a polynomial
in the same `D`. -/
theorem junkP_graph_mem (S : WilkiesDesign.SOMin) {n F D : ℕ} (h : (Fin n → ℝ) → ℝ)
    (hh : WilkiesDesign.graphOf h ∈ S.Ω F D (n + 1)) (i : Fin n) :
    ∃ (a : ℕ) (b : Polynomial ℕ),
      WilkiesDesign.graphOf (junkP h i) ∈ S.Ω a (b.eval D) (n + 1) := by
  rcases n with _ | m
  · exact i.elim0
  · obtain ⟨a, b, hab⟩ :=
      Work.WilG1.Plumb.junkPartial_mem (S := S) (n := m) (F := F) (D := D) i h hh
    refine ⟨a, b, ?_⟩
    rw [junkP_eq_junkPartial]
    exact hab

theorem core_thin (S : WilkiesDesign.SOMin) (hcd : S.SharpCD) (n : ℕ) :
    ∀ (F D : ℕ) (h : (Fin n → ℝ) → ℝ),
      WilkiesDesign.graphOf h ∈ S.Ω F D (n + 1) →
      ∀ a : Work.WilG4c.CoreIx n, interior (closure (Work.WilG4c.fibCore h a)) = ∅ := by
  intro F D h hh a
  -- The closure of a fibre-non-differentiability locus of an `Ω`-definable function is thin.
  have hbad : ∀ (m F' D' : ℕ) (g : (Fin m → ℝ) → ℝ),
      WilkiesDesign.graphOf g ∈ S.Ω F' D' (m + 1) →
      ∀ i : Fin m, interior (closure (fibBad g i)) = ∅ := by
    intro m F' D' g hg i
    obtain ⟨a, b, hmem⟩ := Junk.fibBad_mem (S := S) g hg i
    have hthin : interior (fibBad g i) = ∅ :=
      Junk.fibBad_thin_of_last (S := S)
        (fun p F'' D'' G hG => partialBad_thin (S := S) hcd G hG) g hg i
    exact thin_closure (S := S) hcd hmem hthin
  -- The closure of a discontinuity locus of an `Ω`-definable function is thin.
  have hdisc : ∀ (m F' D' : ℕ) (g : (Fin m → ℝ) → ℝ),
      WilkiesDesign.graphOf g ∈ S.Ω F' D' (m + 1) →
      interior (closure (disc g)) = ∅ := by
    intro m F' D' g hg
    obtain ⟨a, b, hmem⟩ := Junk.disc_mem (S := S) g hg
    have hthin : interior (disc g) = ∅ := generic_continuity (S := S) hcd g hg
    exact thin_closure (S := S) hcd hmem hthin
  cases a with
  | fbad i => exact hbad n F D h hh i
  | fbadJ i i' =>
      obtain ⟨a', b', hg⟩ := junkP_graph_mem (S := S) h hh i
      exact hbad n a' (b'.eval D) (junkP h i) hg i'
  | discJ i =>
      obtain ⟨a', b', hg⟩ := junkP_graph_mem (S := S) h hh i
      exact hdisc n a' (b'.eval D) (junkP h i) hg
  | disc0 => exact hdisc n F D h hh

end Work.WilG4c.CoreThin
