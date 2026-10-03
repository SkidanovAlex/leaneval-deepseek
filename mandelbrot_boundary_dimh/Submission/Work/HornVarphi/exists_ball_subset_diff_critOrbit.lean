import Mathlib
import Submission.Work.Interfaces.HornParts
import Submission.Work.Horn.basin_facts

/-!
# The critical orbit has no accumulation point in the immediate basin

(Step (F3) of the HORN-VARPHI blueprint.)  Let `f₀` be a parabolic germ with immediate basin `B`
and critical point `c ∈ B`, and let `y ∈ B` be a point of the basin that is not on the forward
critical orbit `critOrbit f₀ c = {f₀^k c | k ≥ 1}`.  Then `y` has a whole ball around it inside
`B` which is disjoint from `critOrbit f₀ c`.

The proof is the standard one: the critical orbit converges to `0`, and `0 ∉ B` (a germ with
`f 0 = 0`, `deriv f 0 = 1` cannot have `0` in its basin), so `y ≠ 0`; the tail of the critical
orbit stays in the small ball `ball 0 (‖y‖/4)` around `0`, which stays away from `y`, while the
finitely many remaining points `f₀^k c` (`1 ≤ k < K`) avoid `y` (they lie on the critical orbit)
and hence are at positive distance from `y`.
-/

namespace Work.HornVarphi

open MandelDim Filter Topology Metric
open scoped Topology

/-- Given a sequence `u` with `u k ≠ y` for every `k ≥ 1`, the finite initial segments `k < K`
(`k ≥ 1`) are at positive distance from `y`. -/
private lemma exists_pos_le_dist_of_forall_ne {y : ℂ} {u : ℕ → ℂ}
    (hu : ∀ k : ℕ, 1 ≤ k → u k ≠ y) :
    ∀ K : ℕ, ∃ d : ℝ, 0 < d ∧ ∀ k : ℕ, 1 ≤ k → k < K → d ≤ ‖u k - y‖ := by
  intro K
  induction K with
  | zero => exact ⟨1, one_pos, fun k _ hklt => absurd hklt (Nat.not_lt_zero k)⟩
  | succ K ih =>
      rcases Nat.eq_zero_or_pos K with hK | hK
      · subst hK
        exact ⟨1, one_pos, fun k hk hklt => absurd hklt (by omega)⟩
      · obtain ⟨d, hd, hle⟩ := ih
        have hK1 : 1 ≤ K := by omega
        have hpos : 0 < ‖u K - y‖ := by
          rw [norm_pos_iff, sub_ne_zero]
          exact hu K hK1
        refine ⟨min d ‖u K - y‖, lt_min hd hpos, fun k hk hklt => ?_⟩
        rcases Nat.lt_succ_iff_lt_or_eq.mp hklt with hlt | heq
        · exact le_trans (min_le_left _ _) (hle k hk hlt)
        · rw [heq]; exact min_le_right _ _

theorem exists_ball_subset_diff_critOrbit {f₀ : ℂ → ℂ} {D₀ B : Set ℂ} {c : ℂ}
    (hS : MandelDim.IsF0Setup f₀ D₀ B c) {y : ℂ} (hyB : y ∈ B)
    (hy : y ∉ MandelDim.critOrbit f₀ c) :
    ∃ R : ℝ, 0 < R ∧ Metric.ball y R ⊆ B ∧
      ∀ z ∈ Metric.ball y R, z ∉ MandelDim.critOrbit f₀ c := by
  obtain ⟨hD₀open, h0D₀, hf₀diff, hf₀0, hdf₀, -⟩ := hS.1
  obtain ⟨hBopen, -, hBsub, -, -, -, -⟩ := hS.2.1
  obtain ⟨hcB, -, -⟩ := hS.2.2
  -- `0` is not in the basin, hence not in `B`
  have h0basin : (0 : ℂ) ∉ ParabolicBasin f₀ D₀ :=
    Work.Horn.BasinAux.zero_not_mem hD₀open h0D₀ hf₀diff hf₀0 hdf₀
  have h0B : (0 : ℂ) ∉ B := fun h => h0basin (hBsub h)
  have hyne : y ≠ 0 := fun h => h0B (h ▸ hyB)
  have hynorm : 0 < ‖y‖ := norm_pos_iff.mpr hyne
  -- the critical orbit converges to `0`
  have hconv : Tendsto (fun k : ℕ => f₀^[k] c) atTop (𝓝 0) :=
    Work.Horn.BasinAux.tendsto_zero (hBsub hcB)
  set δ : ℝ := ‖y‖ / 4 with hδdef
  have hδpos : 0 < δ := by rw [hδdef]; linarith
  -- the tail of the critical orbit lies in `ball 0 δ`
  obtain ⟨K, hK⟩ := Metric.tendsto_atTop.mp hconv δ hδpos
  -- the finitely many earlier orbit points keep their distance from `y`
  obtain ⟨d, hdpos, hdle⟩ :=
    exists_pos_le_dist_of_forall_ne (y := y) (u := fun k => f₀^[k] c)
      (fun k hk h => hy ⟨k, hk, h.symm⟩) K
  -- `B` is open at `y`
  obtain ⟨r₀, hr₀pos, hr₀sub⟩ := Metric.isOpen_iff.mp hBopen y hyB
  refine ⟨min r₀ (min (δ / 2) (d / 2)), lt_min hr₀pos (lt_min (by linarith) (by linarith)),
    ?_, ?_⟩
  · intro z hz
    exact hr₀sub (ball_subset_ball (min_le_left _ _) hz)
  · intro z hz hzcrit
    obtain ⟨k, hk1, rfl⟩ := hzcrit
    have hzR : dist (f₀^[k] c) y < min r₀ (min (δ / 2) (d / 2)) := hz
    rcases lt_or_ge k K with hkK | hkK
    · -- `k < K`: positive distance from the finite initial segment
      have h1 : d ≤ ‖f₀^[k] c - y‖ := hdle k hk1 hkK
      have h2 : ‖f₀^[k] c - y‖ < d / 2 := by
        rw [dist_eq_norm] at hzR
        have hle : min r₀ (min (δ / 2) (d / 2)) ≤ d / 2 :=
          le_trans (min_le_right r₀ (min (δ / 2) (d / 2))) (min_le_right (δ / 2) (d / 2))
        linarith
      linarith
    · -- `k ≥ K`: the tail stays near `0`, far away from `y`
      have htail : ‖f₀^[k] c‖ < δ := by
        have h := hK k hkK
        rwa [dist_eq_norm, sub_zero] at h
      have hzn : ‖y - f₀^[k] c‖ < δ / 2 := by
        have h : dist (f₀^[k] c) y < min (δ / 2) (d / 2) :=
          lt_of_lt_of_le hzR (min_le_right _ _)
        rw [dist_eq_norm, norm_sub_rev] at h
        exact lt_of_lt_of_le h (min_le_left _ _)
      have htri : ‖y‖ ≤ ‖y - f₀^[k] c‖ + ‖f₀^[k] c‖ := by
        calc ‖y‖ = ‖(y - f₀^[k] c) + f₀^[k] c‖ := by ring_nf
          _ ≤ ‖y - f₀^[k] c‖ + ‖f₀^[k] c‖ := norm_add_le _ _
      have hδeq : δ = ‖y‖ / 4 := hδdef
      linarith

end Work.HornVarphi
