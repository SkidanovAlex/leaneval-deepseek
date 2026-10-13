import Mathlib
import Submission.Work.WilE7.MainDesignDefs
import Submission.Work.WilE7.eaEval_eventually_eq
import Submission.Work.WilE7.Dim.fibre_closed_of_fullRank
import Submission.Work.WilE7.DimAPI.ProjRankAux

namespace Work.CoreStep

open WilkiesDesign WilkiesDesign.E
open scoped Topology

/-- The absolute set of a stratum lives over the (unique) base point of `ℝ^0`: `absSet S` is the
fibre of `S.X.set` over `(fun i : Fin 0 => i.elim0)`, transported by the coordinate reindexing
`absPt`.  Both directions use the round-trip lemmas `absPt_absPtInv` / `absPtInv_absPt`. -/
theorem absSet_eq_fiber {N : ℕ} (S : WilkiesDesign.E.Stratum 0 N) :
    Work.WilE7.MainDesign.absSet S
      = WilkiesDesign.E.fiber S.X.set (fun i : Fin 0 => i.elim0) := by
  have happ : ∀ u : Fin N → ℝ,
      Fin.append (fun i : Fin 0 => i.elim0) u = Work.WilE7.DimAPI.absPtInv N u := by
    intro u
    funext i
    show Fin.append (fun i : Fin 0 => i.elim0) u i = u (Fin.cast (Nat.zero_add N) i)
    conv_lhs =>
      rw [show i = Fin.natAdd 0 (Fin.cast (Nat.zero_add N) i) from
        Fin.ext (by simp [Fin.natAdd])]
    rw [Fin.append_right]
  ext u
  rw [Work.WilE7.MainDesign.absSet, WilkiesDesign.E.fiber, Set.mem_image, Set.mem_setOf_eq]
  constructor
  · rintro ⟨z, hz, rfl⟩
    rw [happ, Work.WilE7.DimAPI.absPtInv_absPt]
    exact hz
  · intro hu
    rw [happ u] at hu
    exact ⟨Work.WilE7.DimAPI.absPtInv N u, hu, Work.WilE7.DimAPI.absPt_absPtInv N u⟩

theorem absSet_point_isolated {N : ℕ} (S : WilkiesDesign.E.Stratum 0 N)
    (hS : S.Good) (hj : S.j = N) {w : Fin N → ℝ}
    (hw : w ∈ Work.WilE7.MainDesign.absSet S) :
    ∃ U : Set (Fin N → ℝ), IsOpen U ∧ w ∈ U ∧
      ∀ w' ∈ U, w' ∈ Work.WilE7.MainDesign.absSet S → w' = w := by
  have hfib := absSet_eq_fiber S
  -- Every point of `absSet S` is isolated in `absSet S`: this is `fiber_isolated`, the
  -- uniqueness half of the implicit function theorem applied to the `N` equations `S.h` whose
  -- Jacobian has rank `S.j = N` at every point of the stratum.
  have hiso : ∀ u ∈ Work.WilE7.MainDesign.absSet S,
      ∀ᶠ u' in 𝓝 u, u' ∈ Work.WilE7.MainDesign.absSet S → u' = u := by
    intro u hu
    rw [hfib] at hu ⊢
    exact Work.WilE7.Dim.fiber_isolated S hS hj (fun i : Fin 0 => i.elim0) u hu
  -- An eventual statement at `w` gives an open neighbourhood on which it holds.
  obtain ⟨U, hUsub, hUopen, hwU⟩ :=
    mem_nhds_iff.mp (Filter.eventually_iff.mp (hiso w hw))
  exact ⟨U, hUopen, hwU, fun w' hw' hw'mem => hUsub hw' hw'mem⟩

end Work.CoreStep
