import Mathlib
import Submission.Work.WilG4c.StepCleanDefs
import Submission.Work.WilG4c.JointC1LocMem
import Submission.Work.WilG4c.GraphFree
import Submission.Work.WilG4c.DefinableSection

namespace Work.WilG4c

/-- For a definable family `g : ℝ^m → ℝ^N → ℝ` whose `y`-slices are `C¹` on an open set `U` for every parameter `w` in an open set `W`, the set of parameters at which some fibre point `y ∈ U` is a non-`C¹` point of the joint function `famFun g` is thin.

(Definability is essential: for a non-definable `g(w,y) = φ(w)` with `φ` discontinuous on a fat set the slices are constant but the bad set is fat.) -/
theorem C1SliceProjThin (S : WilkiesDesign.SOMin) (hcd : S.SharpCD) (m N F0 D : ℕ)
    (g : (Fin m → ℝ) → (Fin N → ℝ) → ℝ)
    (hg : WilkiesDesign.CG.famGraph g ∈ S.Ω F0 D (m + N + 1))
    (W : Set (Fin m → ℝ)) (hW : IsOpen W)
    (U : Set (Fin N → ℝ)) (hU : IsOpen U)
    (hsm : ∀ w ∈ W, ContDiffOn ℝ 1 (g w) U) :
    interior {w : Fin m → ℝ | w ∈ W ∧
      ∃ y ∈ U, ¬ ContDiffAt ℝ 1 (Work.WilG4c.famFun g) (Fin.append w y)} = ∅ := by
  -- The joint `C¹`-locus `L` is `Ω`-definable (`JointC1LocMem`); write `Z := Lᶜ`, the joint
  -- non-`C¹` locus, so `Z ∈ S.Ω` with `append w y ∈ Z ↔ ¬ ContDiffAt ℝ 1 (famFun g) (append w y)`.
  obtain ⟨aL, bL, hL⟩ := JointC1LocMem S hcd m N F0
  have hLmem : {z : Fin (m + N) → ℝ | ContDiffAt ℝ 1 (famFun g) z}
      ∈ S.Ω aL (bL.eval D) (m + N) := hL D g hg
  set Z : Set (Fin (m + N) → ℝ) :=
    {z : Fin (m + N) → ℝ | ContDiffAt ℝ 1 (famFun g) z}ᶜ with hZ
  have hZmem : Z ∈ S.Ω (aL + 1) (bL.eval D) (m + N) := S.compl hLmem
  have hmemZ : ∀ (w : Fin m → ℝ) (y : Fin N → ℝ),
      Fin.append w y ∈ Z ↔ ¬ ContDiffAt ℝ 1 (famFun g) (Fin.append w y) := by
    intro w y; rw [hZ]; simp
  by_contra hne
  -- the interior of the bad parameter set is nonempty: extract a ball of bad parameters
  have hne' : (interior {w : Fin m → ℝ | w ∈ W ∧
      ∃ y ∈ U, ¬ ContDiffAt ℝ 1 (famFun g) (Fin.append w y)}).Nonempty :=
    Set.nonempty_iff_ne_empty.mpr hne
  obtain ⟨w₀, hw₀int⟩ := hne'
  have hw₀B : w₀ ∈ {w : Fin m → ℝ | w ∈ W ∧
      ∃ y ∈ U, ¬ ContDiffAt ℝ 1 (famFun g) (Fin.append w y)} := interior_subset hw₀int
  obtain ⟨hw₀W, -⟩ := hw₀B
  obtain ⟨r, hr, hball⟩ := Metric.isOpen_iff.mp isOpen_interior w₀ hw₀int
  -- `DefinableSection` produces a continuous section `γ` of the bad locus `Z` over a nonempty
  -- open set `O ⊆ W` with values in `U`
  have hhyp : ∃ w : Fin m → ℝ, w ∈ W ∧ ∃ r : ℝ, 0 < r ∧ ∀ w' : Fin m → ℝ, w' ∈ W →
      dist w' w < r → ∃ y : Fin N → ℝ, y ∈ U ∧ Fin.append w' y ∈ Z := by
    refine ⟨w₀, hw₀W, r, hr, ?_⟩
    intro w' _ hd
    have hw'B : w' ∈ {w : Fin m → ℝ | w ∈ W ∧
        ∃ y ∈ U, ¬ ContDiffAt ℝ 1 (famFun g) (Fin.append w y)} :=
      interior_subset (hball (Metric.mem_ball.mpr hd))
    obtain ⟨-, y, hyU, hybad⟩ := hw'B
    exact ⟨y, hyU, (hmemZ w' y).mpr hybad⟩
  obtain ⟨O, γ, hOopen, hOne, hOW, hγcont, hγU, hγZ⟩ :=
    DefinableSection S hcd m N (aL + 1) (bL.eval D) Z hZmem W hW U hU hhyp
  -- but no graph over an open set of parameters lies in the joint non-`C¹` locus
  exact GraphFree S hcd m N F0 D g hg W hW U hU hsm O hOopen hOne hOW γ hγcont hγU
    (fun w hw => (hmemZ w (γ w)).mp (hγZ w hw))

end Work.WilG4c
