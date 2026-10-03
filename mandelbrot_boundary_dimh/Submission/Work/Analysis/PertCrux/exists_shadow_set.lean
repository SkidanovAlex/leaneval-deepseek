import Mathlib
import Submission.Work.Interfaces.Parabolic
import Submission.Work.Pert.Ksub2.exists_lipschitzOn_of_compact
import Submission.Work.Analysis.PertCrux.exists_tube

namespace Work.Analysis.PertCrux

open Set Metric Filter Topology
open MandelDim

/-- **The shadowing pair `L ⊆ L'` for the orbit of `d.φ '' K`.**  The tube radius `ε₀ > 0` is
*produced*, not assumed (the pointwise basin neighbourhoods of the points `d.φ w` admit a uniform
Lebesgue number on the compact `K`).  `L` is the closure of the forward orbit of the closed
`ε₀`-tube around `d.φ '' K`: compact, forward invariant, contained in `D₀`, and containing the
orbit segment `f₀^[j](d.φ w)`, `j ≤ m`.  `L'` is a compact `rom`-tube around `L` inside `D₀`, on
which `f₀` is `K₀`-Lipschitz.  This is exactly the input pair of
`Work.Analysis.PertCrux.tube_shadowing`.

Existence: `IsParabolicGerm` gives `D₀` open, `f₀` differentiable (hence continuous and locally
Lipschitz) on it; each `d.φ w` has a basin neighbourhood `U_w` with `f₀^[n](U_w) ⊆ D₀` and uniform
convergence to `0`, so a finite subcover of `K` gives `ε₀ > 0` with the `ε₀`-tube inside the union
of the `U_w`; the forward orbit of that tube stays in `D₀`, is bounded (finite initial segment +
eventual small ball around the interior point `0`) and converges to `0`, so its closure `L` is
compact, forward invariant and `⊆ D₀`; finally `L'` is a small closed tube around `L` inside `D₀`
and `K₀` a Lipschitz constant of `f₀` on the compact `L' ⊆ D₀`. -/
theorem exists_shadow_set {f₀ : ℂ → ℂ} {D₀ : Set ℂ} (d : MandelDim.ParabData f₀ D₀)
    (hd : MandelDim.IsParabolicGerm f₀ D₀) {K : Set ℂ} (hKc : IsCompact K) (hK : K ⊆ d.DE)
    (m : ℕ) :
    ∃ L L' : Set ℂ, ∃ rom K₀ ε₀ : ℝ,
      1 ≤ K₀ ∧ 0 < rom ∧ rom ≤ 1 ∧ 0 < ε₀ ∧ IsCompact L ∧ IsCompact L' ∧ L ⊆ L' ∧ L' ⊆ D₀ ∧
      (∀ w ∈ K, Metric.ball (d.φ w) ε₀ ⊆ L) ∧
      (∀ w ∈ K, ∀ j : ℕ, j ≤ m → f₀^[j] (d.φ w) ∈ L) ∧
      (∀ z ∈ L, f₀ z ∈ L) ∧
      (∀ z ∈ L', ∀ z' ∈ L', ‖f₀ z - f₀ z'‖ ≤ K₀ * ‖z - z'‖) ∧
      (∀ z ∈ L, Metric.ball (f₀ z) rom ⊆ L') := by
  classical
  -- the tube around `d.φ '' K` (with uniform convergence of its forward orbits)
  obtain ⟨ε₀, hε₀pos, T, hTc, hTball, hTmap, hTconv⟩ := exists_tube d hd hKc hK
  -- basic data of the parabolic germ
  obtain ⟨hD₀open, h0D₀, hf_diff, hf0, -, -⟩ := hd
  have hfcontD₀ : ContinuousOn f₀ D₀ := hf_diff.continuousOn
  -- a closed ball around `0` inside `D₀`
  obtain ⟨r₁, hr₁pos, hr₁sub⟩ := Metric.isOpen_iff.mp hD₀open 0 h0D₀
  set ρ : ℝ := r₁ / 2 with hρdef
  have hρpos : 0 < ρ := by rw [hρdef]; linarith
  have hρsub : closedBall (0 : ℂ) ρ ⊆ D₀ :=
    (closedBall_subset_ball (by rw [hρdef]; linarith)).trans hr₁sub
  -- beyond time `N` the whole tube orbit is inside the `ρ`-ball
  obtain ⟨N, hN⟩ := hTconv ρ hρpos
  -- `f₀` iterates are continuous on the tube
  have hcont_iter : ∀ n : ℕ, ContinuousOn (f₀^[n]) T := by
    intro n
    induction n with
    | zero => simpa using (continuousOn_id : ContinuousOn (id : ℂ → ℂ) T)
    | succ k ih =>
        have hmaps : MapsTo (f₀^[k]) T D₀ := fun y hy => hTmap y hy k
        have hcomp : ContinuousOn (f₀ ∘ (f₀^[k])) T := hfcontD₀.comp ih hmaps
        simpa only [Function.iterate_succ'] using hcomp
  -- the (finite) initial orbit segment of `T`
  set A : Set ℂ := ⋃ n : Fin (N + 1), (f₀^[(n : ℕ)]) '' T with hAdef
  have hAc : IsCompact A := by
    rw [hAdef]
    exact isCompact_iUnion (fun n : Fin (N + 1) =>
      hTc.image_of_continuousOn (hcont_iter (n : ℕ)))
  have hA_sub : A ⊆ D₀ := by
    rw [hAdef]
    intro u hu
    obtain ⟨n, hn⟩ := Set.mem_iUnion.mp hu
    obtain ⟨y, hy, rfl⟩ := hn
    exact hTmap y hy (n : ℕ)
  -- the whole forward orbit, and its closure
  set U : Set ℂ := ⋃ n : ℕ, (f₀^[n]) '' T with hUdef
  set L : Set ℂ := closure U with hLdef
  have hU_sub : U ⊆ A ∪ closedBall (0 : ℂ) ρ := by
    intro u hu
    obtain ⟨n, hn⟩ := Set.mem_iUnion.mp (by rw [hUdef] at hu; exact hu)
    obtain ⟨y, hy, rfl⟩ := hn
    rcases le_or_gt n N with h | h
    · exact Or.inl (by rw [hAdef]; exact Set.mem_iUnion.mpr ⟨⟨n, Nat.lt_succ_of_le h⟩, ⟨y, hy, rfl⟩⟩)
    · refine Or.inr ?_
      rw [Metric.mem_closedBall, dist_zero_right]
      exact le_of_lt (hN n (le_of_lt h) y hy)
  have hclosed : IsClosed (A ∪ closedBall (0 : ℂ) ρ) :=
    (hAc.union (isCompact_closedBall 0 ρ)).isClosed
  have hL_sub : L ⊆ A ∪ closedBall (0 : ℂ) ρ := by
    rw [hLdef]
    exact closure_minimal hU_sub hclosed
  have hLclosed : IsClosed L := by rw [hLdef]; exact isClosed_closure
  have hLc : IsCompact L :=
    (hAc.union (isCompact_closedBall 0 ρ)).of_isClosed_subset hLclosed hL_sub
  have hLD₀ : L ⊆ D₀ := hL_sub.trans (union_subset hA_sub hρsub)
  have hT_sub_U : T ⊆ U := by
    rw [hUdef]
    intro y hy
    exact Set.mem_iUnion.mpr ⟨0, by simpa using hy⟩
  have hTL : T ⊆ L := by
    have h : U ⊆ L := by rw [hLdef]; exact subset_closure
    exact hT_sub_U.trans h
  -- `L` is forward invariant
  have hmapU : f₀ '' U ⊆ U := by
    rintro x ⟨u, hu, rfl⟩
    rw [hUdef] at hu ⊢
    obtain ⟨n, hn⟩ := Set.mem_iUnion.mp hu
    obtain ⟨y, hy, rfl⟩ := hn
    exact Set.mem_iUnion.mpr ⟨n + 1, ⟨y, hy, Function.iterate_succ_apply' f₀ n y⟩⟩
  have hmapL : ∀ z ∈ L, f₀ z ∈ L := by
    intro z hz
    have hzU : z ∈ closure U := by rw [hLdef] at hz; exact hz
    have hzD₀ : z ∈ D₀ := hLD₀ hz
    have hcont : ContinuousAt f₀ z := hfcontD₀.continuousAt (hD₀open.mem_nhds hzD₀)
    have h1 : f₀ z ∈ closure (f₀ '' U) := mem_closure_image hcont hzU
    have h2 : closure (f₀ '' U) ⊆ closure U := closure_mono hmapU
    rw [hLdef]
    exact h2 h1
  -- the tube points and their orbit segments lie in `L`
  have hdphiT : ∀ w ∈ K, d.φ w ∈ T := fun w hw => hTball w hw (Metric.mem_ball_self hε₀pos)
  have hMapsL : MapsTo f₀ L L := hmapL
  have horb : ∀ w ∈ K, ∀ j : ℕ, j ≤ m → f₀^[j] (d.φ w) ∈ L :=
    fun w hw j _ => (MapsTo.iterate hMapsL j) (hTL (hdphiT w hw))
  -- `L'`: a compact tube around `L` inside `D₀`, on which `f₀` is Lipschitz
  obtain ⟨r, hrpos, hrsub⟩ := hLc.exists_cthickening_subset_open hD₀open hLD₀
  set L' : Set ℂ := cthickening r L with hL'def
  have hL'c : IsCompact L' := by rw [hL'def]; exact hLc.cthickening
  have hL'D₀ : L' ⊆ D₀ := by rw [hL'def]; exact hrsub
  have hLL' : L ⊆ L' := by rw [hL'def]; exact self_subset_cthickening L
  obtain ⟨L₀, hL₀nn, hlip⟩ :=
    Work.Pert.Ksub2.exists_lipschitzOn_of_compact hD₀open hL'c hL'D₀ hf_diff
  refine ⟨L, L', min r 1, max L₀ 1, ε₀, le_max_right L₀ 1, lt_min hrpos one_pos,
    min_le_right r 1, hε₀pos, hLc, hL'c, hLL', hL'D₀, ?_, horb, hmapL, ?_, ?_⟩
  · intro w hw
    exact (hTball w hw).trans hTL
  · intro z hz z' hz'
    have h1 : ‖f₀ z - f₀ z'‖ ≤ L₀ * ‖z - z'‖ := hlip z hz z' hz'
    have h2 : L₀ * ‖z - z'‖ ≤ max L₀ 1 * ‖z - z'‖ :=
      mul_le_mul_of_nonneg_right (le_max_left L₀ 1) (norm_nonneg _)
    linarith
  · intro z hz
    have hzL : f₀ z ∈ L := hmapL z hz
    calc Metric.ball (f₀ z) (min r 1) ⊆ closedBall (f₀ z) (min r 1) := ball_subset_closedBall
      _ ⊆ cthickening (min r 1) L := closedBall_subset_cthickening hzL (min r 1)
      _ ⊆ cthickening r L := cthickening_mono (min_le_left r 1) L
      _ = L' := by rw [hL'def]

end Work.Analysis.PertCrux
