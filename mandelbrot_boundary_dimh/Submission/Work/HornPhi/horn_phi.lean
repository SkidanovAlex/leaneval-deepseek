import Mathlib
import Submission.Work.Interfaces.HornParts
import Submission.Work.HornTopo.horn_topo
import Submission.Work.Horn.pushdown_critval_unique
import Submission.Work.Parab.basinEnters.zero_not_mem_basin
import Submission.Work.L62.lift_section
import Submission.Work.HornPhi.proper_iterate
import Submission.Work.HornPhi.inverse_Phi_omega
import Submission.Work.HornPhi.covering_iterate
import Submission.Work.HornPhi.critval_excl
import Submission.Work.HornPhi.ball_avoid_sub_nat

/-! Guidance from the project lead (the requester):

AREA HORN-PHI (Claim A): prove HornPhiStatement.
Contracts: Submission/Work/Interfaces/HornParts.lean (namespace MandelDim; imports Parabolic.lean). Lead route: NOTES_LEAD_horn.md at the workspace root (read it). Paper: REFS/shishikura_math9201282/hdim5.tex (Lemma 5.2, Prop 5.3). Reusable in the workspace: Submission/Work/Horn/* (basic.lean: piExp facts, E_add_one; basin.lean; flower_q.lean), Submission/Work/Parab/basinEnters/zero_not_mem_basin.lean, Submission/Work/Normal (Montel, Hurwitz), Submission/Work/L62/{lift_section,cartan}.lean. Never edit the interface files; if a statement is false, report a counterexample and the corrected statement. Go wide.

## HornPhi = Claim A (Φ on B)
- Surjectivity: given y, take N with y + N ∈ Φ(Ωp) (Φ_image). Then y + N = Φ(z'), z' ∈ Ωp ⊆ B. f^N : B → B is onto, so there is z ∈ B with f^N z = z', and Φ z = y.
- Sections. Let y avoid v − ℕ. Pick r > 0 with ball y (2r) ∩ (v − ℕ) = ∅. For N large, ball (y+N) (2r) ⊆ Φ(Ωp) (Φ_image). Set W_N := (Φ|Ωp)⁻¹(ball (y+N) r): open, and homeomorphic to a disc via Φ, so simply connected.
  - Critical values of f^N in B lying in W_N would be f^k c with Φ = v + k ∈ ball(y+N, r), i.e. v − (N−k) ∈ ball(y, r). This is excluded.
  - By F4, each component K of f^{-N}(W_N) ∩ B maps homeomorphically onto W_N by f^N. Then σ_K := (f^N|K)⁻¹ ∘ (Φ|Ωp)⁻¹ ∘ (· + N) is a holomorphic section of Φ over ball y r (Φ(f^N u) = Φ u + N).
- Every z ∈ B with Φ z ∈ ball y r is hit: f^m z ∈ Ωp for some m (basin_enter), and then f^N z ∈ Ωp for all N ≥ m, with Φ(f^N z) = Φ z + N ∈ ball(y+N, r). So f^N z ∈ W_N by Φ-injectivity on Ωp, and z lies in some component K.
- Note: "N large" must work for the given z. Take N ≥ max(m, N₀).

## Implementation (this file)
* `Wset d y r N = Ω₊ ∩ Φ⁻¹(ball (y+N) r)` — the fundamental domain over which `f^N` is a covering.
* `HornPhi/proper_iterate`  : `B ∩ (f^N)⁻¹K` is compact for compact `K ⊆ B` (from `IsImmediateBasin`).
* `HornPhi/inverse_Phi_omega`: the inverse branch `Ψ` of `Φ|Ω₊` over `ball (y+N) r` (below the
  critical values, where `Φ|Ω₊` is a biholomorphism onto `Φ(Ω₊)`), and simple connectivity of `Wset`.
* `HornPhi/covering_iterate : `f^N` is a covering map over `Wset` (proper + local homeomorphism).
* `HornPhi/critval_excl`    : `deriv (f^N) ≠ 0` on `(f^N)⁻¹(Wset)` (the critical values `Φ c - ℕ` are
  excluded by the choice of `r`).
* `HornPhi/ball_avoid_sub_nat`: the choice of `r` (a ball avoiding `Φ c - ℕ`).
* `Work.L62.lift_section`   : a holomorphic section of a covering over a simply connected base.

Assembly: `σ u := s (Ψ (u + N))` where `s` is the holomorphic section of `f^N` over `Wset` through
`f^N z`; then `Φ (σ u) = Φ (s (Ψ (u+N))) = Φ (f^N (s (Ψ (u+N)))) - N = Φ (Ψ (u+N)) - N = u`. -/

namespace Work.HornPhi

open MandelDim Complex Set Metric Filter Topology
open scoped Topology

noncomputable section

variable {f₀ : ℂ → ℂ} {D₀ B : Set ℂ} {c : ℂ} {d : ParabData f₀ D₀}

/-- `W_N = Ω₊ ∩ Φ⁻¹(ball (y+N) r)`: the piece of the petal sitting over the ball. -/
def Wset (d : ParabData f₀ D₀) (y : ℂ) (r : ℝ) (N : ℕ) : Set ℂ :=
  {w : ℂ | w ∈ d.Ωp ∧ d.Φ w ∈ Metric.ball (y + N) r}

/-- **`f^N : B → B` is onto**: `B` is forward invariant and `B ⊆ f '' B`. -/
theorem f_iterate_surj (h : IsF0Setup f₀ D₀ B c) :
    ∀ N : ℕ, ∀ y ∈ B, ∃ z ∈ B, (f₀^[N]) z = y := by
  have hB := h.2.1
  have hsurj : B ⊆ f₀ '' B := hB.2.2.2.2.2.1
  intro N
  induction N with
  | zero => intro y hy; exact ⟨y, hy, rfl⟩
  | succ n ih =>
      intro y hy
      obtain ⟨w, hwB, hw⟩ := hsurj hy
      obtain ⟨z, hzB, hz⟩ := ih w hwB
      exact ⟨z, hzB, by rw [Function.iterate_succ_apply', hz, hw]⟩

/-- The iterates of `f₀` are holomorphic on the immediate basin. -/
theorem iter_differentiableOn (h : IsF0Setup f₀ D₀ B c) (N : ℕ) :
    DifferentiableOn ℂ (f₀^[N]) B := by
  have hB := h.2.1
  have hsub : B ⊆ D₀ := Work.HornTopo.subset_D₀_of_immediateBasin hB
  have hfd : DifferentiableOn ℂ f₀ B := h.1.2.2.1.mono hsub
  exact hfd.iterate hB.2.2.2.2.1 N

/-- Points of `B` have orbits that never hit `0`. -/
theorem iter_ne_zero (h : IsF0Setup f₀ D₀ B c) {z : ℂ} (hz : z ∈ B) :
    ∀ n : ℕ, (f₀^[n]) z ≠ 0 := by
  have hB := h.2.1
  have hzero : (0 : ℂ) ∉ ParabolicBasin f₀ D₀ :=
    Work.Parab.basinEnters.zero_not_mem_parabolicBasin h.1
  have hmem : ∀ n : ℕ, (f₀^[n]) z ∈ B :=
    fun n => (hB.2.2.2.2.1.iterate n) hz
  intro n hn
  exact hzero (hn ▸ hB.2.2.1 (hmem n))

/-- `W_N` is open. -/
theorem isOpen_Wset (d : ParabData f₀ D₀) (y : ℂ) (r : ℝ) (N : ℕ) :
    IsOpen (Wset d y r N) := by
  have hcont : ContinuousOn d.Φ d.Ωp := d.Φ_holo.continuousOn.mono d.Ωp_sub
  have h := hcont.isOpen_inter_preimage d.Ωp_open
    (Metric.isOpen_ball (x := y + N) (ε := r))
  rw [show Wset d y r N = d.Ωp ∩ d.Φ ⁻¹' Metric.ball (y + N) r from rfl]
  exact h

/-- For large `N` the ball `ball (y+N) r` is contained in `Φ '' Ω₊`. -/
theorem exists_ball_subset_Phi_image (d : ParabData f₀ D₀) (y : ℂ) {r : ℝ} (hr : 0 < r) :
    ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N → ∀ u ∈ Metric.ball (y + N) r, ∃ z ∈ d.Ωp, d.Φ z = u := by
  obtain ⟨C, hC⟩ := d.Φ_image (|y.im| + r)
  refine ⟨⌈C - y.re + r⌉₊, fun N hN u hu => ?_⟩
  have hNr : C - y.re + r ≤ (N : ℝ) := le_trans (Nat.le_ceil _) (by exact_mod_cast hN)
  have hdist : ‖u - (y + N)‖ < r := by simpa [dist_eq_norm] using hu
  have hre : C < u.re := by
    have h2 : |u.re - (y + N).re| ≤ ‖u - (y + N)‖ := by
      have h := Complex.abs_re_le_norm (u - (y + N))
      rwa [Complex.sub_re] at h
    have h3 : (y + N).re = y.re + (N : ℝ) := by simp
    have := (abs_lt.mp (lt_of_le_of_lt h2 hdist)).1
    rw [h3] at this
    linarith
  have him : |u.im| ≤ |y.im| + r := by
    have h2 : |u.im - (y + N).im| ≤ ‖u - (y + N)‖ := by
      have h := Complex.abs_im_le_norm (u - (y + N))
      rwa [Complex.sub_im] at h
    have h3 : (y + N).im = y.im := by simp
    have hb : |u.im - y.im| ≤ r := le_of_lt (lt_of_le_of_lt (by simpa [h3] using h2) hdist)
    have h4 : |u.im| ≤ |u.im - y.im| + |y.im| := by
      have := abs_add_le (u.im - y.im) y.im
      simpa using this
    linarith
  exact hC u hre him

/-- **`Φ` is onto `ℂ`**: `Φ (f^N z) = Φ z + N` shifts the (nonempty) image of the petal, and
`f^N` is onto `B`. -/
theorem Phi_surj (h : IsF0Setup f₀ D₀ B c) (d : ParabData f₀ D₀) (y : ℂ) :
    ∃ z ∈ B, d.Φ z = y := by
  obtain ⟨C, hC⟩ := d.Φ_image (|y.im| + 1)
  obtain ⟨N, hN⟩ := exists_nat_gt (C - y.re)
  have hre : C < (y + N).re := by
    have h2 : (y + N).re = y.re + (N : ℝ) := by simp
    rw [h2]; linarith
  have him : |(y + N).im| ≤ |y.im| + 1 := by
    have h2 : (y + N).im = y.im := by simp
    rw [h2]
    have := le_abs_self y.im
    linarith
  obtain ⟨z', hz'Ω, hz'Φ⟩ := hC (y + N) hre him
  have hz'B : z' ∈ B := Work.HornTopo.omega_subset_B h d hz'Ω
  obtain ⟨z, hzB, hz⟩ := f_iterate_surj h N z' hz'B
  refine ⟨z, hzB, ?_⟩
  have h1 : d.Φ (f₀^[N] z) = d.Φ z + (N : ℂ) :=
    (Work.Horn.critval_Phi_iterate d h.2.1 hzB N).symm
  rw [hz, hz'Φ] at h1
  exact add_right_cancel h1.symm


/-- If `w ∈ Ω₊` and `Φ w` lies in the ball, then `w ∈ W_N`. -/
theorem mem_Wset_of_mem_omega (d : ParabData f₀ D₀) {w : ℂ} (hw : w ∈ d.Ωp)
    {y : ℂ} {r : ℝ} {N : ℕ} (h : d.Φ w ∈ Metric.ball (y + N) r) :
    w ∈ Wset d y r N := ⟨hw, h⟩

/-- **Claim A (HornPhi)**: `Φ : B → ℂ` is onto and every point of `B` over a disc avoiding
`Φ c - ℕ` is the value at its own `Φ`-image of a holomorphic section of `Φ` over that disc. -/
theorem horn_phi : HornPhiStatement := by
  intro f₀ D₀ B c d h
  refine ⟨fun y => Phi_surj h d y, ?_⟩
  intro y hy
  obtain ⟨r, hr, hav⟩ := ball_avoid_sub_nat (v := d.Φ c) (y := y) hy
  refine ⟨r, hr, ?_⟩
  intro z hzB hzball
  -- the orbit of `z` enters the petal
  obtain ⟨m, hm⟩ := d.basin_enter z (h.2.1.2.2.1 hzB) (iter_ne_zero h hzB)
  -- and for large `N` the ball `ball (y+N) r` is contained in `Φ '' Ω₊`
  obtain ⟨N₀, hN₀⟩ := exists_ball_subset_Phi_image d y hr
  set N : ℕ := max m N₀ with hNdef
  have hmN : m ≤ N := le_max_left _ _
  have hN₀N : N₀ ≤ N := le_max_right _ _
  -- basic facts about `f^N` on `B`
  have hBopen : IsOpen B := h.2.1.1
  have hWN_sub : Wset d y r N ⊆ B := fun w hw => Work.HornTopo.omega_subset_B h d hw.1
  have hdiffN : ∀ w ∈ B, DifferentiableAt ℂ (f₀^[N]) w := fun w hw =>
    (iter_differentiableOn h N).differentiableAt (hBopen.mem_nhds hw)
  have hloc : ∀ w ∈ B, (f₀^[N]) w ∈ Wset d y r N → deriv (f₀^[N]) w ≠ 0 :=
    fun w hwB hw => critval_excl h hr hav hwB hw.2
  have hprof : ∀ L : Set ℂ, L ⊆ B → IsCompact L → IsCompact (B ∩ (f₀^[N]) ⁻¹' L) :=
    proper_iterate (d := d) h N
  -- `f^N z ∈ W_N`
  have hΦfNz : d.Φ ((f₀^[N]) z) = d.Φ z + (N : ℂ) :=
    (Work.Horn.critval_Phi_iterate d h.2.1 hzB N).symm
  have hfNzΩ : (f₀^[N]) z ∈ d.Ωp := by
    have hsplit : (f₀^[N]) z = (f₀^[N - m]) ((f₀^[m]) z) := by
      conv_lhs => rw [← Nat.sub_add_cancel hmN]
      exact Function.iterate_add_apply f₀ (N - m) m z
    rw [hsplit]
    exact (d.Ωp_maps.iterate (N - m)) hm
  have hfNzball : d.Φ ((f₀^[N]) z) ∈ Metric.ball (y + N) r := by
    rw [hΦfNz]
    rw [Metric.mem_ball, dist_eq_norm] at hzball ⊢
    convert hzball using 2
    ring
  have hfNzW : (f₀^[N]) z ∈ Wset d y r N := ⟨hfNzΩ, hfNzball⟩
  -- the two analytic inputs
  obtain ⟨Ψ, hΨdiff, hΨU, hΨinv, hΨsc⟩ :=
    inverse_Phi_omega (Φ := d.Φ) (U := d.Ωp) d.Ωp_open (d.Φ_holo.mono d.Ωp_sub) d.Φ_inj
      hr (fun u hu => hN₀ N hN₀N u hu)
  have hcov : IsCoveringMapOn (fun w : {w : ℂ // w ∈ B} => (f₀^[N]) w) (Wset d y r N) :=
    covering_iterate hBopen (isOpen_Wset d y r N) hWN_sub hdiffN hloc hprof
  -- the holomorphic section of `f^N` over `W_N` through `z`
  obtain ⟨s, hsdiff, hs0, hs⟩ :=
    Work.L62.lift_section hBopen (iter_differentiableOn h N) (isOpen_Wset d y r N) hΨsc hcov
      hfNzW hzB rfl
  -- the sheet of `Φ` through `z`
  have hΨUball : ∀ u ∈ Metric.ball y r, Ψ (u + N) ∈ d.Ωp ∧ d.Φ (Ψ (u + N)) = u + N := by
    intro u hu
    refine hΨU (u + N) ?_
    rw [Metric.mem_ball, dist_eq_norm] at hu ⊢
    convert hu using 2
    ring
  have hballN : ∀ u ∈ Metric.ball y r, u + (N : ℂ) ∈ Metric.ball (y + N) r := by
    intro u hu
    rw [Metric.mem_ball, dist_eq_norm] at hu ⊢
    convert hu using 2
    ring
  have hΨW : ∀ u ∈ Metric.ball y r, Ψ (u + N) ∈ Wset d y r N := fun u hu =>
    ⟨(hΨUball u hu).1, by rw [(hΨUball u hu).2]; exact hballN u hu⟩
  refine ⟨fun u => s (Ψ (u + N)), ?_, ?_, ?_, ?_⟩
  · -- differentiability of the section
    have h1 : DifferentiableOn ℂ (fun u : ℂ => Ψ (u + N)) (Metric.ball y r) := by
      refine hΨdiff.comp (differentiableOn_id.add_const (N : ℂ)) ?_
      intro u hu
      rw [Metric.mem_ball, dist_eq_norm] at hu ⊢
      convert hu using 2
      ring
    exact hsdiff.comp h1 fun u hu => (hΨW u hu)
  · -- the section maps into `B`
    intro u hu
    exact (hs (Ψ (u + N)) (hΨW u hu)).1
  · -- `Φ ∘ σ = id`
    intro u hu
    have hwB : s (Ψ (u + N)) ∈ B := (hs (Ψ (u + N)) (hΨW u hu)).1
    have h1 : d.Φ (s (Ψ (u + N))) + (N : ℂ) = d.Φ ((f₀^[N]) (s (Ψ (u + N)))) :=
      Work.Horn.critval_Phi_iterate d h.2.1 hwB N
    have h2 : (f₀^[N]) (s (Ψ (u + N))) = Ψ (u + N) := (hs (Ψ (u + N)) (hΨW u hu)).2
    have h3 : d.Φ (Ψ (u + N)) = u + N := (hΨUball u hu).2
    exact add_right_cancel (by rw [h1, h2, h3])
  · -- `σ (Φ z) = z`
    have hΦzmem : d.Φ z + (N : ℂ) ∈ Metric.ball (y + N) r := by
      have := hfNzball
      rwa [hΦfNz] at this
    have h6 : Ψ (d.Φ ((f₀^[N]) z)) = (f₀^[N]) z := hΨinv _ hfNzΩ hfNzball
    show s (Ψ (d.Φ z + (N : ℂ))) = z
    rw [← hΦfNz, h6]
    exact hs0

end

end Work.HornPhi
