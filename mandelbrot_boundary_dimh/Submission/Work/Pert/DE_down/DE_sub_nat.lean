import Mathlib
import Submission.Work.Interfaces.Parabolic
import Submission.Work.Parab.basinBack.basin_backward

/-!
# `DE` is invariant under `w ↦ w - j`

`d.DE = {w | w ∈ d.Dφ ∧ d.φ w ∈ ParabolicBasin f₀ D₀}` is the domain of the lifted horn map
`Ẽ_{f₀} = Φ₀ ∘ φ₀` (a `T`-invariant set when `φ (Dφ) ⊆ D₀`).  Here we prove the *downward*
half of that invariance: `w ∈ DE` implies `w - j ∈ DE` for every `j : ℕ`.

The two ingredients are exactly the two fields of `ParabData` that describe the maximal domain of
the Fatou coordinate:

* `left_inv : w ∈ Dφ → w - 1 ∈ Dφ` — the maximal domain is closed under `w ↦ w - 1`;
* `succ_iff : (w + 1 ∈ Dφ ↔ φ w ∈ D₀)` together with the Abel equation
  `φ_abel : φ (w + 1) = f₀ (φ w)`.

The latter converts `f₀ (φ (w - 1)) ∈ ParabolicBasin f₀ D₀` into `φ (w - 1) ∈ ParabolicBasin f₀ D₀`:
`f₀ (φ (w-1)) = φ w` and `φ (w-1) ∈ D₀` (so `f₀` is analytic there and `D₀` is a neighbourhood of
it), and `Work.Parab.basinBack.basin_backward` says that the uniform parabolic basin is backward
invariant along an analytic map.  Iterating the one-step statement gives the claim.
-/

namespace Work.Pert.DE_down

open Set

/-- **One step of downward closedness of `d.DE`.**  If `w` lies in the domain of the lifted horn
map `Ẽ_{f₀} = Φ₀ ∘ φ₀`, then so does `w - 1`.

The point is that `φ (w - 1)` maps to `φ w` under `f₀` (the Abel equation at `w - 1`), that
`φ (w - 1) ∈ D₀` (via (4.1.2) `succ_iff`, since `(w - 1) + 1 = w ∈ Dφ`), and that the uniform
parabolic basin is backward invariant under an analytic map (`Work.Parab.basinBack.basin_backward`,
with `D₀ ∈ 𝓝 (φ (w-1))` because `D₀` is open). -/
theorem DE_sub_one {f₀ : ℂ → ℂ} {D₀ : Set ℂ} (d : MandelDim.ParabData f₀ D₀)
    (hd : MandelDim.IsParabolicGerm f₀ D₀) {w : ℂ} (hw : w ∈ d.DE) :
    w - 1 ∈ d.DE := by
  obtain ⟨hopen, -, hdiff, -, -, -⟩ := hd
  have hwDφ : w ∈ d.Dφ := hw.1
  have hwB : d.φ w ∈ MandelDim.ParabolicBasin f₀ D₀ := hw.2
  -- the maximal domain is closed under `w ↦ w - 1`
  have h1Dφ : w - 1 ∈ d.Dφ := d.left_inv w hwDφ
  -- `(w - 1) + 1 = w ∈ Dφ`, hence `φ (w - 1) ∈ D₀` by (4.1.2)
  have h1D₀ : d.φ (w - 1) ∈ D₀ :=
    (d.succ_iff (w - 1) h1Dφ).mp (by simpa using hwDφ)
  -- the Abel equation at `w - 1`: `f₀ (φ (w - 1)) = φ w`
  have habel : f₀ (d.φ (w - 1)) = d.φ w := by
    have h := d.φ_abel (w - 1) h1Dφ (by simpa using hwDφ)
    rw [show (w - 1) + 1 = w from sub_add_cancel w 1] at h
    exact h.symm
  -- `f₀ (φ (w - 1))` is a basin point, so `φ (w - 1)` is, by backward invariance
  have hfB : f₀ (d.φ (w - 1)) ∈ MandelDim.ParabolicBasin f₀ D₀ := by
    rw [habel]; exact hwB
  exact ⟨h1Dφ, Work.Parab.basinBack.basin_backward
    (hdiff.analyticAt (hopen.mem_nhds h1D₀)) (hopen.mem_nhds h1D₀) hfB⟩

theorem DE_sub_nat {f₀ : ℂ → ℂ} {D₀ : Set ℂ} (d : MandelDim.ParabData f₀ D₀)
    (hd : MandelDim.IsParabolicGerm f₀ D₀) {w : ℂ} (hw : w ∈ d.DE) (j : ℕ) :
    w - (j : ℂ) ∈ d.DE := by
  have hstep : ∀ u ∈ d.DE, u - 1 ∈ d.DE := fun u hu => DE_sub_one d hd hu
  induction j with
  | zero => simpa using hw
  | succ j ih =>
    have h := hstep (w - (j : ℂ)) ih
    simpa [Nat.cast_succ, sub_sub] using h

end Work.Pert.DE_down
