import Mathlib
import Submission.Work.Noncompact.CompressionTube.ctc.exists_local_transverse_piece
import Submission.Work.Noncompact.CompressionTube.ctc.transverse_open

/-!
# A finite cover of a compact parameter interval by transverse pieces

Given a smooth proper embedding `γ : ℝ → M` of a line into a smooth `n`-manifold `M` (`n ≥ 2`),
a smooth `g : M → ℝ` with `g (γ s) = s`, and a compact parameter interval `[a,b]`, we produce a
**finite** family of *pieces*: for finitely many parameters `t` a globally smooth
`ψ t : M → ℝ^{n-1}` vanishing on the line, together with a radius `rr t > 0`, such that `ψ t` is
transverse at `γ s` for every `s ∈ (t - rr t, t + rr t)`, and such that the half-intervals
`(t - rr t/2, t + rr t/2)` cover `[a,b]`.

There is no geometry left in this lemma beyond the two ingredients already proved:

* `exists_local_transverse_piece` — a globally smooth piece which is transverse at one prescribed
  parameter `t` (and vanishes on the whole line);
* `transverse_open` — transversality at `γ t` persists for all `s` with `|s - t| < ρ`, some
  `ρ > 0`.

Putting them together, every `t : ℝ` carries a piece `ψ t` and a radius `rr t > 0` with
transversality on the *full* interval `(t - rr t, t + rr t)`.  The intervals of *half* that radius
cover `[a,b]` (each `s` is covered by the interval centred at `s` itself), so compactness of
`[a,b]` (`IsCompact.elim_finite_subcover`) extracts the finite subfamily `F`.  Since
`(t - rr t/2, t + rr t/2) ⊆ (t - rr t, t + rr t)`, the transversality conclusion holds on the
covering intervals, exactly as required.
-/

namespace Work.Noncompact.CompressionTube

open scoped Manifold ContDiff
open Topology Set

noncomputable section

theorem exists_finite_piece_cover {n : ℕ} (hn : 2 ≤ n) {M : Type*} [TopologicalSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
    [IsManifold (Work.Noncompact.CompressionTube.MC n)
      Work.Noncompact.CompressionTube.smoothOrder M]
    [T2Space M] [SecondCountableTopology M]
    {γ : ℝ → M} (hγ : ContMDiff Work.Noncompact.CompressionTube.MCreal
      (Work.Noncompact.CompressionTube.MC n)
      Work.Noncompact.CompressionTube.smoothOrder γ) (hinj : Function.Injective γ)
    (hprop : IsProperMap γ) (himm : ∀ s : ℝ, Function.Injective (mfderiv
      Work.Noncompact.CompressionTube.MCreal (Work.Noncompact.CompressionTube.MC n) γ s))
    {g : M → ℝ} (hg : ContMDiff (Work.Noncompact.CompressionTube.MC n)
      Work.Noncompact.CompressionTube.MCreal Work.Noncompact.CompressionTube.smoothOrder g)
    (hgcore : ∀ s : ℝ, g (γ s) = s) (a b : ℝ) :
    ∃ (F : Finset ℝ) (ψ : ℝ → M → EuclideanSpace ℝ (Fin (n - 1))) (rr : ℝ → ℝ),
      (∀ t ∈ F, ContMDiff (Work.Noncompact.CompressionTube.MC n)
          (Work.Noncompact.CompressionTube.MC (n - 1))
          Work.Noncompact.CompressionTube.smoothOrder (ψ t) ∧
        (∀ s : ℝ, ψ t (γ s) = 0) ∧ 0 < rr t ∧
        ∀ s : ℝ, |s - t| < rr t →
          Work.Noncompact.CompressionTube.Transverse γ g (ψ t) s) ∧
      Set.Icc a b ⊆ ⋃ t ∈ F, Set.Ioo (t - rr t / 2) (t + rr t / 2) := by
  classical
  -- Step 1: at every parameter there is a piece together with a (full) transversality radius.
  have hkey : ∀ t : ℝ, ∃ (ψ : M → EuclideanSpace ℝ (Fin (n - 1))) (ρ : ℝ),
      0 < ρ ∧ ContMDiff (MC n) (MC (n - 1)) smoothOrder ψ ∧
        (∀ s : ℝ, ψ (γ s) = 0) ∧
        ∀ s : ℝ, |s - t| < ρ → Transverse γ g ψ s := by
    intro t
    obtain ⟨ψ, hψsm, hψ0, htr⟩ :=
      exists_local_transverse_piece hn hγ hinj hprop himm hg hgcore t
    obtain ⟨ρ, hρpos, hρ⟩ :=
      transverse_open hn hγ hinj hprop himm hg hgcore hψsm hψ0 htr
    exact ⟨ψ, ρ, hρpos, hψsm, hψ0, hρ⟩
  choose ψf ρf hspec using hkey
  -- Step 2: the half-radius intervals already cover `[a,b]`.
  have hcover : Set.Icc a b ⊆ ⋃ t : ℝ, Set.Ioo (t - ρf t / 2) (t + ρf t / 2) := by
    intro s _
    refine mem_iUnion.mpr ⟨s, ?_⟩
    have hpos : 0 < ρf s := (hspec s).1
    rw [mem_Ioo]
    constructor <;> linarith
  -- Step 3: compactness of `[a,b]` extracts a finite subcover.
  obtain ⟨F, hF⟩ := IsCompact.elim_finite_subcover isCompact_Icc
    (fun t : ℝ => Set.Ioo (t - ρf t / 2) (t + ρf t / 2)) (fun _ => isOpen_Ioo) hcover
  refine ⟨F, ψf, ρf, ?_, hF⟩
  intro t _
  have h := hspec t
  exact ⟨h.2.1, h.2.2.1, h.1, h.2.2.2⟩

end

end Work.Noncompact.CompressionTube
