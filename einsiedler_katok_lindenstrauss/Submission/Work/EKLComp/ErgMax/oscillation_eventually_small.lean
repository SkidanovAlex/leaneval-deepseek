import Mathlib
import Submission.Work.EKLComp.ErgMax.Basic

namespace Work.EKLComp.ErgMax

open Filter Topology

theorem oscillation_eventually_small (K : Set Work.EKLContract.X3) (hK : IsCompact K)
    (f : BoundedContinuousFunction Work.EKLContract.X3 ℝ) (ε : ℝ) (hε : 0 < ε) :
    ∀ᶠ N : ℕ in Filter.atTop, ∀ z ∈ K, ∀ a b : ℝ, 0 ≤ a → a ≤ 1 / (N : ℝ) → 0 ≤ b →
      b ≤ 1 / (N : ℝ) → |f (Work.EKLContract.aPlus a b • z) - f z| < ε := by
  -- The joint map `((a,b),z) ↦ f (aPlus a b • z) - f z` is continuous and vanishes at `((0,0),z)`.
  have hcont : Continuous (fun p : (ℝ × ℝ) × Work.EKLContract.X3 =>
      f (Work.EKLContract.aPlus p.1.1 p.1.2 • p.2) - f p.2) :=
    (f.continuous.comp continuous_aPlus_smul).sub (f.continuous.comp continuous_snd)
  -- At each point of `K` the set where this is `< ε` is a neighbourhood in the product.
  have hmem : ∀ y ∈ K, ∀ᶠ p : (ℝ × ℝ) × Work.EKLContract.X3 in 𝓝 (((0:ℝ),(0:ℝ)), y),
      |f (Work.EKLContract.aPlus p.1.1 p.1.2 • p.2) - f p.2| < ε := by
    intro y hy
    have hpt : |f (Work.EKLContract.aPlus (0:ℝ) 0 • y) - f y| < ε := by
      rw [Work.EKLContract.aPlus_zero, one_smul, sub_self, abs_zero]; exact hε
    have hopen : IsOpen {p : (ℝ × ℝ) × Work.EKLContract.X3 |
        |f (Work.EKLContract.aPlus p.1.1 p.1.2 • p.2) - f p.2| < ε} := by
      have h1 : IsOpen {r : ℝ | |r| < ε} := by
        rw [show {r : ℝ | |r| < ε} = Set.Ioo (-ε) ε from by ext r; simp [abs_lt]]
        exact isOpen_Ioo
      exact h1.preimage hcont
    exact hopen.mem_nhds hpt
  -- Compactness of `K` turns the pointwise statement into a neighbourhood of `(0,0)`.
  have hforall := hK.eventually_forall_of_forall_eventually (x₀ := ((0:ℝ),(0:ℝ)))
    (P := fun (x : ℝ × ℝ) (y : Work.EKLContract.X3) =>
      |f (Work.EKLContract.aPlus x.1 x.2 • y) - f y| < ε) hmem
  rcases Metric.mem_nhds_iff.mp hforall with ⟨δ, hδpos, hδ⟩
  obtain ⟨N₀, hN₀⟩ := exists_nat_gt (1/δ)
  refine Filter.eventually_atTop.2 ⟨N₀, fun N hN => ?_⟩
  intro z hz a b ha hab hb hbb
  have hNle : (N₀ : ℝ) ≤ (N : ℝ) := Nat.cast_le.mpr hN
  have hNpos : (0:ℝ) < (N:ℝ) := by
    have h0 : (0:ℝ) < (N₀:ℝ) := by
      have : (0:ℝ) < 1/δ := by positivity
      linarith
    linarith
  -- `1/N < δ` for all `N ≥ N₀`, so `(a,b)` lies in the metric ball of radius `δ`.
  have h1N : 1/(N:ℝ) < δ := by
    rw [div_lt_iff₀ hNpos]
    have key : (1:ℝ) < (N:ℝ) * δ := (div_lt_iff₀ hδpos).mp (lt_of_lt_of_le hN₀ hNle)
    linarith
  have ha' : |a| < δ := by rw [abs_of_nonneg ha]; linarith
  have hb' : |b| < δ := by rw [abs_of_nonneg hb]; linarith
  have hdist : dist ((a,b) : ℝ × ℝ) ((0:ℝ),(0:ℝ)) < δ := by
    have hd : dist ((a,b) : ℝ × ℝ) ((0:ℝ),(0:ℝ)) = max |a| |b| := by
      simp [Prod.dist_eq]
    rw [hd]; exact max_lt ha' hb'
  exact hδ (Metric.mem_ball.mpr hdist) z hz

end Work.EKLComp.ErgMax
