/-
  WilG4a / CD / `fibDerivAux` — the elementary dictionary between the *slice* derivatives
  `iteratedDeriv m (fun t => f l t)` and the *joint* `x`-derivatives
  `iteratedFDeriv ℝ m (famFun f) (Fin.snoc l t) (∂_x)`.

  This is the shared vocabulary used by the proof of
  `Work.WilG4a.CD.fibDerivSet_eq_fibMainSet_on_germ`: on the joint `C^m` locus the two agree
  (`iteratedDeriv_eq_jointDeriv`, from `Work.WilG4a.iteratedDeriv_snoc`), membership in
  `derivGraphSet` is exactly "the value coordinate is the joint derivative over the joint
  `C^m` locus" (`mem_derivGraphSet_iff`), the fibre germ gives a punctured neighbourhood of
  joint smoothness (`smoothLocus_of_fibGerm`, `sliceContDiffAt_of_germ`), and continuity of
  the iterated derivative follows from `ContDiffAt` (`continuousAt_iteratedDeriv_of_contDiffAt`,
  in the punctured `ε`-`δ` form `exists_delta_of_continuousAt`).
-/
import Mathlib
import Submission.Work.WilG4a.Defs
import Submission.Work.WilG4a.Cells
import Submission.Work.WilG4a.iteratedDeriv_snoc
import Submission.Work.WilG4a.slice_contDiffAt
import Submission.Work.WilG4a.CD.fibDerivDefs

set_option autoImplicit false
noncomputable section
open Classical
open Filter Set
open scoped Topology ContDiff

namespace Work.WilG4a.CD
open WilkiesDesign WilkiesConjecture Work.WilG4a

/-- The `m`-th joint `x`-derivative of the family `f` at `(l,t)`: the `m`-th iterated Fréchet
derivative of the joint function `famFun f` at `Fin.snoc l t`, evaluated in the `x`-direction
`Fin.last p`. -/
def jointDeriv {p : ℕ} (f : (Fin p → ℝ) → ℝ → ℝ) (m : ℕ) (l : Fin p → ℝ) (t : ℝ) : ℝ :=
  iteratedFDeriv ℝ m (famFun f) (Fin.snoc l t) (fun _ : Fin m => Pi.single (xDir p) 1)

/-- **Currying.** Where the joint function is `C^m`, the `m`-th derivative of the slice is the
`m`-th joint `x`-derivative.  This is `Work.WilG4a.iteratedDeriv_snoc` read through `famFun`. -/
theorem iteratedDeriv_eq_jointDeriv {p : ℕ} (f : (Fin p → ℝ) → ℝ → ℝ) (m : ℕ)
    (l : Fin p → ℝ) (t : ℝ) (h : ContDiffAt ℝ m (famFun f) (Fin.snoc l t)) :
    iteratedDeriv m (fun s : ℝ => f l s) t = jointDeriv f m l t := by
  have h' := iteratedDeriv_snoc p (famFun f) l t m h
  simp only [famFun_apply, jointDeriv, xDir] at h' ⊢
  exact h'

/-- A `C^j` function has continuous `j`-th iterated derivative (the junk-free formulation: at
`x` itself). -/
theorem continuousAt_iteratedDeriv_of_contDiffAt {G : ℝ → ℝ} {j : ℕ} {x : ℝ}
    (h : ContDiffAt ℝ j G x) : ContinuousAt (iteratedDeriv j G) x := by
  rw [iteratedDeriv_eq_equiv_comp]
  exact (ContinuousMultilinearMap.piFieldEquiv ℝ (Fin j) ℝ).symm.continuous.continuousAt.comp
    (h.continuousAt_iteratedFDeriv le_rfl)

/-- The punctured `ε`-`δ` form of continuity at a point. -/
theorem exists_delta_of_continuousAt {F : ℝ → ℝ} {x : ℝ} (h : ContinuousAt F x)
    (ε : ℝ) (hε : 0 < ε) : ∃ δ > 0, ∀ t : ℝ, t ≠ x → |t - x| < δ → |F t - F x| < ε := by
  rw [Metric.continuousAt_iff] at h
  obtain ⟨δ, hδ, hδp⟩ := h ε hε
  refine ⟨δ, hδ, fun t _ hlt => ?_⟩
  have h1 := hδp (x := t) (by simpa only [Real.dist_eq] using hlt)
  simpa only [Real.dist_eq] using h1

/-- If `G` is `C^j` at `x` and its `j`-th iterated derivative tends to `y` along the punctured
neighbourhood, then `y` is the value of the `j`-th iterated derivative at `x`. -/
theorem eq_of_tendsto_iteratedDeriv {G : ℝ → ℝ} {j : ℕ} {x y : ℝ} (h : ContDiffAt ℝ j G x)
    (htend : ∀ ε > 0, ∃ δ > 0, ∀ t : ℝ, t ≠ x → |t - x| < δ →
      |iteratedDeriv j G t - y| < ε) :
    iteratedDeriv j G x = y := by
  have hc := continuousAt_iteratedDeriv_of_contDiffAt h
  have hkey : ∀ ε > 0, |iteratedDeriv j G x - y| < ε := by
    intro ε hε
    obtain ⟨δ₁, hδ₁, hδ₁p⟩ := exists_delta_of_continuousAt hc (ε / 2) (by linarith)
    obtain ⟨δ₂, hδ₂, hδ₂p⟩ := htend (ε / 2) (by linarith)
    set c : ℝ := min δ₁ δ₂ / 2 with hcdef
    have hcpos : 0 < c := by rw [hcdef]; linarith [lt_min hδ₁ hδ₂]
    have hc₁ : |(x + c) - x| < δ₁ := by
      rw [add_sub_cancel_left, abs_of_pos hcpos]; linarith [min_le_left δ₁ δ₂]
    have hc₂ : |(x + c) - x| < δ₂ := by
      rw [add_sub_cancel_left, abs_of_pos hcpos]; linarith [min_le_right δ₁ δ₂]
    have hne : x + c ≠ x := by linarith
    have h1 := hδ₁p (x + c) hne hc₁
    have h2 := hδ₂p (x + c) hne hc₂
    have h3 : |iteratedDeriv j G x - y| ≤
        |iteratedDeriv j G x - iteratedDeriv j G (x + c)| +
          |iteratedDeriv j G (x + c) - y| := abs_sub_le _ _ _
    have h4 : |iteratedDeriv j G x - iteratedDeriv j G (x + c)|
        = |iteratedDeriv j G (x + c) - iteratedDeriv j G x| := abs_sub_comm _ _
    linarith
  have hz : |iteratedDeriv j G x - y| = 0 := by
    by_contra hcon
    have hpos : 0 < |iteratedDeriv j G x - y| := lt_of_le_of_ne (abs_nonneg _) (Ne.symm hcon)
    exact absurd (hkey _ hpos) (lt_irrefl _)
  exact sub_eq_zero.mp (abs_eq_zero.mp hz)

/-- The fibre germ gives a radius on which the punctured slice lies in the joint `C^j` locus. -/
theorem smoothLocus_of_fibGerm {p : ℕ} (f : (Fin p → ℝ) → ℝ → ℝ) (j : ℕ)
    {l : Fin p → ℝ} {x : ℝ} (h : Fin.snoc l x ∈ fibGerm f j) :
    ∃ ρ : ℝ, 0 < ρ ∧ ∀ t : ℝ, t ≠ x → |t - x| < ρ → Fin.snoc l t ∈ smoothLocus f j := by
  obtain ⟨ρ, hρ, hg⟩ := (mem_fibGerm f j (Fin.snoc l x)).mp h
  refine ⟨ρ, hρ, fun t ht hlt => ?_⟩
  simpa only [Fin.snoc_last, Fin.init_snoc] using
    hg t (by simpa using ht) (by simpa using hlt)

/-- The joint `C^j` locus is contained in the joint `C^m` locus for `m ≤ j`. -/
theorem smoothLocus_subset {p : ℕ} (f : (Fin p → ℝ) → ℝ → ℝ) {j m : ℕ} (hmj : m ≤ j) :
    smoothLocus f j ⊆ smoothLocus f m :=
  interior_mono fun z hz =>
    show ContDiffAt ℝ m (famFun f) z from
      (show ContDiffAt ℝ j (famFun f) z from hz).of_le
        (show ((m : ℕ∞ω) ≤ (j : ℕ∞ω)) from by exact_mod_cast hmj)

/-- On the joint `C^j` locus the joint function is `C^m` for `m ≤ j`. -/
theorem contDiffAt_famFun_of_smooth {p : ℕ} (f : (Fin p → ℝ) → ℝ → ℝ) {j m : ℕ} (hmj : m ≤ j)
    {l : Fin p → ℝ} {t : ℝ} (h : Fin.snoc l t ∈ smoothLocus f j) :
    ContDiffAt ℝ m (famFun f) (Fin.snoc l t) := by
  have h' : ContDiffAt ℝ j (famFun f) (Fin.snoc l t) := interior_subset h
  exact h'.of_le (show ((m : ℕ∞ω) ≤ (j : ℕ∞ω)) from by exact_mod_cast hmj)

/-- Membership in the derivative graph set, at a point of a fibre: the value coordinate is the
joint `m`-th `x`-derivative, over the joint `C^m` locus. -/
theorem mem_derivGraphSet_iff {p : ℕ} (f : (Fin p → ℝ) → ℝ → ℝ) (m : ℕ)
    (l : Fin p → ℝ) (t v : ℝ) :
    Fin.snoc (Fin.snoc l t) v ∈ derivGraphSet f m ↔
      Fin.snoc l t ∈ smoothLocus f m ∧ v = jointDeriv f m l t := by
  simp only [derivGraphSet, smoothLocus, Set.mem_ofPred_eq, jointDeriv, xDir, Fin.init_snoc,
    Fin.snoc_last]

/-- On the fibre germ, the slice of the family is `C^j` on the punctured neighbourhood. -/
theorem sliceContDiffAt_of_germ {p : ℕ} (f : (Fin p → ℝ) → ℝ → ℝ) (j : ℕ)
    {l : Fin p → ℝ} {x : ℝ} (h : Fin.snoc l x ∈ fibGerm f j) :
    ∃ ρ : ℝ, 0 < ρ ∧ ∀ t : ℝ, t ≠ x → |t - x| < ρ → ContDiffAt ℝ j (fun s : ℝ => f l s) t := by
  obtain ⟨ρ, hρ, hsm⟩ := smoothLocus_of_fibGerm f j h
  exact ⟨ρ, hρ, fun t ht hlt => by
    have h1 := slice_contDiffAt p (famFun f) j l t (hsm t ht hlt)
    simpa only [famFun_apply] using h1⟩

end Work.WilG4a.CD
