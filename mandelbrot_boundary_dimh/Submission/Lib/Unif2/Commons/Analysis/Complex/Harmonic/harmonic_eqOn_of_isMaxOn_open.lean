import Mathlib.Analysis.InnerProductSpace.Harmonic.Basic
import Mathlib.Topology.Connected.Basic
import Submission.Lib.Unif2.Commons.Analysis.Complex.Harmonic.harmonic_eqOn_ball_of_isMaxOn

noncomputable section
open Set Metric Complex InnerProductSpace Filter
open scoped Real Topology

namespace Commons.Analysis.Complex.Harmonic

/-- **Strong maximum principle for harmonic functions on a connected open set.**
If `u` is harmonic on the connected open set `U` and attains its maximum over
`U` at the point `x₀ ∈ U`, then `u` is constant on `U`.

Proof: the level set `S = {z ∈ U | u z = u x₀}` is nonempty (it contains `x₀`),
open (by the ball version of the maximum principle applied around each of its
points), and closed relative to `U` (complement `{z ∈ U | u z < u x₀}` is open
by continuity of the harmonic function `u`).  Connectedness of `U` forces
`S = U`. -/
theorem harmonic_eqOn_of_isMaxOn_open {U : Set ℂ} (hUopen : IsOpen U) (hUconn : IsPreconnected U)
    {u : ℂ → ℝ} (hu : ∀ x : ℂ, x ∈ U → HarmonicAt u x) {x₀ : ℂ} (hx₀ : x₀ ∈ U)
    (hmax : ∀ x : ℂ, x ∈ U → u x ≤ u x₀) :
    ∀ x : ℂ, x ∈ U → u x = u x₀ := by
  classical
  let M : ℝ := u x₀
  let S : Set ℂ := {z : ℂ | z ∈ U ∧ u z = M}
  /- `S` is open: around each `z ∈ S` a whole ball inside `U` is contained in
     `S`, by the ball version of the strong maximum principle. -/
  have hS_open : IsOpen S := by
    rw [Metric.isOpen_iff]
    intro z hzS
    rcases hzS with ⟨hzU, hzM⟩
    rcases (Metric.isOpen_iff.mp hUopen) z hzU with ⟨r, hrpos, hrball⟩
    refine ⟨r, hrpos, ?_⟩
    intro w hw
    constructor
    · exact hrball hw
    · have hu_ball : HarmonicOnNhd u (ball z r) := by
        intro y hy
        exact hu y (hrball hy)
      have hmax_z : ∀ y ∈ ball z r, u y ≤ u z := by
        intro y hy
        calc
          u y ≤ M := hmax y (hrball hy)
          _ = u z := hzM.symm
      have h_eqOn : ∀ y ∈ ball z r, u y = u z :=
        harmonic_eqOn_ball_of_isMaxOn (c := z) (r := r) hrpos hu_ball hmax_z
      calc
        u w = u z := h_eqOn w hw
        _ = M := hzM
  /- The complement of `S` inside `U` is open: at points of `U` where
     `u < M` continuity of the harmonic function `u` keeps values below `M`
     on a neighbourhood. -/
  have hV_open : IsOpen (U \ S) := by
    rw [Metric.isOpen_iff]
    intro z hzV
    rcases hzV with ⟨hzU, hznotS⟩
    have hneq : u z ≠ M := by
      intro hzeq
      exact hznotS ⟨hzU, hzeq⟩
    have hlt : u z < M := lt_of_le_of_ne (hmax z hzU) hneq
    have hcontAt : ContinuousAt u z := (hu z hzU).1.continuousAt
    have hevent : ∀ᶠ y in 𝓝 z, u y < M := by
      simpa [M] using
        (ContinuousAt.eventually_lt hcontAt (continuousAt_const : ContinuousAt (fun _ : ℂ => M) z) hlt)
    have hballMem : U ∈ 𝓝 z := hUopen.mem_nhds hzU
    rcases (Metric.mem_nhds_iff.mp hballMem) with ⟨ε₁, hε₁pos, hε₁⟩
    rcases (Metric.eventually_nhds_iff.mp hevent) with ⟨ε₂, hε₂pos, hε₂⟩
    refine ⟨min ε₁ ε₂, lt_min hε₁pos hε₂pos, ?_⟩
    intro y hy
    have hy₁ : y ∈ ball z ε₁ := (Metric.ball_subset_ball (min_le_left ε₁ ε₂)) hy
    have hy₂ : y ∈ ball z ε₂ := (Metric.ball_subset_ball (min_le_right ε₁ ε₂)) hy
    have hyU : y ∈ U := hε₁ hy₁
    have hyM : u y < M := hε₂ hy₂
    exact ⟨hyU, by
      intro hyS
      exact (ne_of_lt hyM) hyS.2⟩
  /- `S` is a nonempty relatively open-and-closed subset of the connected set
     `U`, hence `S = U`. -/
  have hdisj : Disjoint S (U \ S) := by
    rw [Set.disjoint_left]
    intro y hyS hyV
    exact hyV.2 hyS
  have hcover : U ⊆ S ∪ (U \ S) := by
    intro y hyU
    by_cases hyS : y ∈ S
    · exact Or.inl hyS
    · exact Or.inr ⟨hyU, hyS⟩
  have hS_nonempty : (U ∩ S).Nonempty := ⟨x₀, hx₀, by dsimp [S, M]; exact ⟨hx₀, rfl⟩⟩
  have hU_sub_S : U ⊆ S :=
    IsPreconnected.subset_left_of_subset_union hS_open hV_open hdisj hcover hS_nonempty hUconn
  intro x hxU
  simpa [M] using (hU_sub_S hxU).2

end Commons.Analysis.Complex.Harmonic
