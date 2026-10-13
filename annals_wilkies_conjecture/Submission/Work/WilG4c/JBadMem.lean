/-
  WilG4c / `JBadMem` — the joint `C^k`-locus `jLoc` and its complement `jBad` are
  `Ω`-definable, with format and degree uniform in the order `k`
  (degree polynomial in the input degree `D` and in `k`).

  This is the *projection and complement* corollary of the sharp-derivative hypothesis
  `SOMin.SharpDeriv` (`hder`), in the vocabulary of `AlSliceBase`:

  * `jLoc p n f k` is the interior of the `C^k`-locus of `famFunHat f` (the family member read
    as a single function on `ℝ^{p + (n+1)}`, matching `WilkiesDesign.CG.famGraph`);
  * `jBad p n f k = (jLoc p n f k)ᶜ`.

  `SharpDeriv` controls the *graph* of the joint `k`-th directional derivative over `jLoc`
  (`Work.WilkG4c.AlDgList_mem_sharp`, proved, with `AlDgList` the graph and `AlLoc` the
  interior of the `C`-locus).  Two `Ω`-operations convert this into the present statement:

  * `projLast (AlDgList p n f L) = AlLoc p n f L.length` (`projLast_AlDgList`), and
    `jLoc = AlLoc` definitionally, so `jLoc` is the projection of the (Ω-definable) graph:
    format `+1`.
  * `jBad` is the complement: format `+1` again.

  No smoothness or tameness is used here beyond what `SharpDeriv` already supplies, and the
  degree polynomial stays that of `SharpDeriv` (`b1`): neither projection nor complement
  changes the degree.  Note that this is the *joint* locus; the corresponding statements for
  the weaker *fibre* (slice) locus are the ones that need cell decompositions
  (`SliceDerivGraphMem`).

  ## Naming

  The directory is `Submission/Work/WilG4c/`, and the lemma was requested under the name
  `Work.WilG4c.JBadMem`; the surrounding theory (`jLoc`, `jBad`, `AlDgList`, …) lives in the
  namespace `Work.WilkG4c` (as do all the other files of this directory).  The main theorem is
  therefore `Work.WilG4c.JBadMem`, and an alias with the same statement is provided under the
  theory-consistent spelling `Work.WilkG4c.JBadMem` for importers.
-/
import Mathlib
import Submission.Work.WilG4c.AlSliceBase
import Submission.Work.WilG4c.CurveFamAlpha

namespace Work.WilkG4c

/-- **`jLoc` is the projection of the joint derivative graph.**  For any list `L` of cube
directions of length `k`, the projection (dropping the value coordinate) of `AlDgList p n f L`
is the joint `C^k`-locus `jLoc p n f k`.  In particular `jLoc p n f k` is `Ω`-definable
whenever the graph is, with format one higher. -/
theorem jLoc_eq_projLast_AlDgList {p n : ℕ}
    (f : (Fin p → ℝ) → (Fin (n + 1) → ℝ) → ℝ) {k : ℕ}
    {L : List (Fin (p + (n + 1)))} (hL : L.length = k) :
    jLoc p n f k = WilkiesDesign.projLast (AlDgList p n f L) := by
  rw [projLast_AlDgList, hL]
  rfl

end Work.WilkG4c

namespace Work.WilG4c

theorem JBadMem (S : WilkiesDesign.SOMin) (hder : S.SharpDeriv) (p n F0 : ℕ) :
    ∃ (a : ℕ) (b : MvPolynomial (Fin 2) ℕ), ∀ (D k : ℕ)
      (f : (Fin p → ℝ) → (Fin (n + 1) → ℝ) → ℝ),
      WilkiesDesign.CG.famGraph f ∈ S.Ω F0 D (p + (n + 1) + 1) →
      (Work.WilkG4c.jLoc p n f k ∈ S.Ω a (MvPolynomial.eval ![D, k] b) (p + (n + 1))) ∧
      (Work.WilkG4c.jBad p n f k ∈ S.Ω a (MvPolynomial.eval ![D, k] b) (p + (n + 1))) := by
  -- `SharpDeriv` at the ambient dimension `p + (n+1)`, in the `AlDgList`/`AlLoc` spelling.
  obtain ⟨a1, b1, hAl⟩ := Work.WilkG4c.AlDgList_mem_sharp S hder F0 p n
  -- The format is the `SharpDeriv` format plus one for the projection and one for the complement;
  -- the degree polynomial is unchanged.
  refine ⟨a1 + 2, b1, fun D k f hf => ?_⟩
  -- Pick any list of `k` cube directions (at least one coordinate exists, since `n + 1 ≥ 1`).
  have hp : 0 < p + (n + 1) := by omega
  have hG := hAl D f (List.replicate k ⟨0, hp⟩) hf
  have hlen : (List.replicate k ⟨0, hp⟩ : List (Fin (p + (n + 1)))).length = k :=
    List.length_replicate ..
  rw [hlen] at hG
  -- `jLoc` is the projection of the graph, hence of format `a1 + 1`.
  have hproj : Work.WilkG4c.jLoc p n f k
      = WilkiesDesign.projLast
          (Work.WilkG4c.AlDgList p n f (List.replicate k ⟨0, hp⟩)) :=
    Work.WilkG4c.jLoc_eq_projLast_AlDgList f hlen
  have hJloc : Work.WilkG4c.jLoc p n f k ∈ S.Ω (a1 + 1) (MvPolynomial.eval ![D, k] b1)
      (p + (n + 1)) := hproj ▸ S.proj hG
  -- `jLoc` at the declared format `a1 + 2`, and `jBad` as its complement at the same format.
  exact ⟨S.mono_F hJloc, by simpa [Work.WilkG4c.jBad] using S.compl hJloc⟩

end Work.WilG4c

namespace Work.WilkG4c

/-- Alias of `Work.WilG4c.JBadMem` in the namespace of the surrounding theory, so that clients
of the module `Submission.Work.WilG4c.JBadMem` may refer to it under either spelling. -/
theorem JBadMem (S : WilkiesDesign.SOMin) (hder : S.SharpDeriv) (p n F0 : ℕ) :
    ∃ (a : ℕ) (b : MvPolynomial (Fin 2) ℕ), ∀ (D k : ℕ)
      (f : (Fin p → ℝ) → (Fin (n + 1) → ℝ) → ℝ),
      WilkiesDesign.CG.famGraph f ∈ S.Ω F0 D (p + (n + 1) + 1) →
      (Work.WilkG4c.jLoc p n f k ∈ S.Ω a (MvPolynomial.eval ![D, k] b) (p + (n + 1))) ∧
      (Work.WilkG4c.jBad p n f k ∈ S.Ω a (MvPolynomial.eval ![D, k] b) (p + (n + 1))) :=
  Work.WilG4c.JBadMem S hder p n F0

end Work.WilkG4c
