import Mathlib

namespace Work.L62

/-- **Perturbation of the identity has a unique zero.**  Let `S : ℂ → ℂ` be a map whose
displacement `w ↦ S w - w` is bounded by `δ` on the closed ball `B(z, R₀)` and is `k`-Lipschitz
there, with `k < 1` and `δ ≤ (1 - k) R₀`.  Then `S w = z` has exactly one solution in `B(z, R₀)`,
and it lies within `δ` of `z`.

Proof: the map `G w = z - (S w - w)` maps `B(z, R₀)` into itself, is a `k`-contraction there, and
`S w = z ↔ G w = w`; Banach's fixed point theorem gives a unique fixed point, and the displacement
bound gives `‖w - z‖ = ‖S w - w‖ ≤ δ`. -/
theorem exists_unique_eq_of_lipschitz_close {S : ℂ → ℂ} {z : ℂ} {R₀ k δ : ℝ}
    (hR₀ : 0 < R₀) (hk0 : 0 ≤ k) (hk1 : k < 1) (hδ : 0 ≤ δ)
    (hδR₀ : δ ≤ (1 - k) * R₀)
    (hSval : ∀ w ∈ Metric.closedBall z R₀, ‖S w - w‖ ≤ δ)
    (hlip : ∀ a ∈ Metric.closedBall z R₀, ∀ b ∈ Metric.closedBall z R₀,
        ‖(S a - a) - (S b - b)‖ ≤ k * ‖a - b‖) :
    ∃ w ∈ Metric.closedBall z R₀, S w = z ∧ ‖w - z‖ ≤ δ ∧
      ∀ w' ∈ Metric.closedBall z R₀, S w' = z → w' = w := by
  have hδR : δ ≤ R₀ := by nlinarith [hδR₀, hk0, hR₀]
  -- the contraction `G w = z - (S w - w)`
  let G : ℂ → ℂ := fun w => z - (S w - w)
  -- `G` maps the closed ball into itself
  have hGmem : Set.MapsTo G (Metric.closedBall z R₀) (Metric.closedBall z R₀) := by
    intro w hw
    rw [Metric.mem_closedBall, dist_eq_norm]
    have h1 : G w - z = -(S w - w) := by simp only [G]; ring
    rw [h1, norm_neg]
    exact le_trans (hSval w hw) hδR
  -- `G` is `k`-Lipschitz on the closed ball
  have hGlip : ∀ a ∈ Metric.closedBall z R₀, ∀ b ∈ Metric.closedBall z R₀,
      dist (G a) (G b) ≤ k * dist a b := by
    intro a ha b hb
    rw [dist_eq_norm, dist_eq_norm]
    have h1 : G a - G b = -((S a - a) - (S b - b)) := by simp only [G]; ring
    rw [h1, norm_neg]
    exact hlip a ha b hb
  -- `G` restricted to the closed ball is a contraction
  let Gs : Metric.closedBall z R₀ → Metric.closedBall z R₀ := fun x => ⟨G x, hGmem x.2⟩
  have hGslip : LipschitzWith ⟨k, hk0⟩ Gs := by
    apply LipschitzWith.of_dist_le_mul
    intro x y
    have h1 : dist (Gs x) (Gs y) = dist (G (x : ℂ)) (G (y : ℂ)) := Subtype.dist_eq _ _
    rw [h1]
    calc dist (G (x : ℂ)) (G (y : ℂ)) ≤ k * dist (x : ℂ) (y : ℂ) := hGlip x x.2 y y.2
      _ = (⟨k, hk0⟩ : NNReal) * dist x y := by
            rw [show ((⟨k, hk0⟩ : NNReal) : ℝ) = k from rfl, Subtype.dist_eq]
  have hGsc : ContractingWith ⟨k, hk0⟩ Gs := ⟨by exact_mod_cast hk1, hGslip⟩
  haveI : IsClosed (Metric.closedBall z R₀) := Metric.isClosed_closedBall
  haveI : CompleteSpace ↥(Metric.closedBall z R₀) := IsClosed.completeSpace_coe
  haveI : Nonempty ↥(Metric.closedBall z R₀) :=
    ⟨⟨z, Metric.mem_closedBall_self hR₀.le⟩⟩
  -- Banach's fixed point theorem
  let fp := ContractingWith.fixedPoint Gs hGsc
  have hfpx : Gs fp = fp := ContractingWith.fixedPoint_isFixedPt hGsc
  have hGy : G fp.1 = fp.1 := by
    have h := congrArg Subtype.val hfpx
    simpa [Gs] using h
  have hz1 : z - (S fp.1 - fp.1) = fp.1 := by simpa only [G] using hGy
  have hSy : S fp.1 = z := by linear_combination -hz1
  refine ⟨fp.1, fp.2, hSy, ?_, ?_⟩
  · -- the fixed point is within `δ` of `z`
    have hy2 : fp.1 - z = -(S fp.1 - fp.1) := by rw [hSy]; ring
    rw [hy2, norm_neg]
    exact hSval fp.1 fp.2
  · -- uniqueness
    intro w' hw' hSw'
    have hw'fix : G w' = w' := by
      simp only [G]; rw [hSw']; ring
    have hle : ‖w' - fp.1‖ ≤ k * ‖w' - fp.1‖ := by
      have h1 : w' - fp.1 = G w' - G fp.1 := by rw [hw'fix, hGy]
      have h2 : G w' - G fp.1 = -((S w' - w') - (S fp.1 - fp.1)) := by simp only [G]; ring
      calc ‖w' - fp.1‖ = ‖G w' - G fp.1‖ := by rw [h1]
        _ = ‖(S w' - w') - (S fp.1 - fp.1)‖ := by rw [h2, norm_neg]
        _ ≤ k * ‖w' - fp.1‖ := hlip w' hw' fp.1 fp.2
    have hzero : ‖w' - fp.1‖ = 0 := by nlinarith [norm_nonneg (w' - fp.1), hle]
    exact sub_eq_zero.mp (norm_eq_zero.mp hzero)

end Work.L62
