import Mathlib
import Submission.Work.TMComp.IDSDefs
import Submission.Work.TMComp.IDSBox.gbounds
import Submission.Work.TMComp.IDSBox.polyroots
import Submission.Work.TMComp.IDSBox.levelcount

/-!
# Sturm oscillation counting for the box characteristic polynomial (`P_IDSSpectrum`)

The Prüfer angle `E ↦ pruferIter α lam E n θ 0` is antitone and decreases from `n` at `-∞`
to `0` at `+∞`, and `E` is a root of the box characteristic polynomial `jacPoly α lam θ n`
exactly when that angle is a half-integer (AJ §2.2, Sturm oscillation).  Consequently the
angle crosses each of the `n` levels `1/2, 3/2, …, n - 1/2` exactly once, these `n` points
exhaust the roots of the degree-`n` polynomial, and the number of roots below a point `X`
is `n - g X` up to an error of at most `2`.

The proof combines three independent lemmas:

* `gbounds` (real analysis): the angle takes values in `[0, n]` and each half-integer level
  `m + 1/2` with `m < n` is attained (monotonicity, the limits, and the intermediate value
  theorem);
* `polyroots` (algebra): an `n`-element set of roots of a monic degree-`n` polynomial
  exhausts them and they are simple;
* `levelcount` (order combinatorics): for an antitone `g` whose half-integer levels sit at
  the points of an `n`-element duplicate-free set, the count below `X` is `n - g X` to
  within `2`.
-/

noncomputable section

namespace Work.TMComp.IDSBox

theorem rootcount (α lam θ : ℝ) (n : ℕ)
    (hcont : Continuous fun E : ℝ => Work.TMContract.pruferIter α lam E n θ 0)
    (hmono : Antitone fun E : ℝ => Work.TMContract.pruferIter α lam E n θ 0)
    (htop : Filter.Tendsto (fun E : ℝ => Work.TMContract.pruferIter α lam E n θ 0)
      Filter.atTop (nhds 0))
    (hbot : Filter.Tendsto (fun E : ℝ => Work.TMContract.pruferIter α lam E n θ 0)
      Filter.atBot (nhds (n : ℝ)))
    (hmonic : (Work.TMComp.jacPoly α lam θ n).Monic)
    (hdeg : (Work.TMComp.jacPoly α lam θ n).natDegree = n)
    (hroot : ∀ E : ℝ, (Work.TMComp.jacPoly α lam θ n).eval E = 0 ↔
      ∃ m : ℤ, Work.TMContract.pruferIter α lam E n θ 0 = m + 1/2) :
    ∀ X : ℝ, |(((Work.TMComp.jacPoly α lam θ n).roots.filter (fun r => r < X)).card : ℝ)
      - ((n : ℝ) - Work.TMContract.pruferIter α lam X n θ 0)| ≤ 2 := by
  obtain ⟨hb, hlevE⟩ :=
    gbounds (fun E : ℝ => Work.TMContract.pruferIter α lam E n θ 0) n hcont hmono htop hbot
  -- pick, for each `m < n`, a point where the angle equals `m + 1/2`
  choose f hf using fun m : Fin n => hlevE (m : ℕ) m.isLt
  have hinj : Function.Injective f := by
    intro m m' h
    have h1 : ((m : ℕ) : ℝ) + 1/2 = ((m' : ℕ) : ℝ) + 1/2 := by
      rw [← hf m, ← hf m', h]
    have h2 : ((m : ℕ) : ℝ) = ((m' : ℕ) : ℝ) := by linarith
    exact Fin.ext (Nat.cast_injective h2)
  have hcardT : (Finset.univ.image f).card = n := by
    rw [Finset.card_image_of_injective _ hinj, Finset.card_univ, Fintype.card_fin]
  -- these `n` points are roots of the characteristic polynomial
  have hTroot : ∀ t ∈ Finset.univ.image f, (Work.TMComp.jacPoly α lam θ n).eval t = 0 := by
    intro t ht
    rw [Finset.mem_image] at ht
    obtain ⟨m, -, rfl⟩ := ht
    rw [hroot]
    refine ⟨(m : ℤ), ?_⟩
    rw [hf m]
    push_cast
    ring
  -- hence the root multiset is duplicate-free with exactly these `n` members
  obtain ⟨hnodup, htofinset, -⟩ :=
    polyroots hmonic hdeg (Finset.univ.image f) hcardT hTroot
  intro X
  exact levelcount (fun E : ℝ => Work.TMContract.pruferIter α lam E n θ 0) n f _ hmono hf
    hnodup htofinset hb X

end Work.TMComp.IDSBox
