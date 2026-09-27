import Mathlib
import Submission.Work.Drive.Whitney.modelChart

/-!
# The lens region of the Whitney move, and the two interfaces it feeds

This module fixes the vocabulary of the *Milnor route* to `Work.Drive.hasPushSignedSmooth_milnor`
(see `Drive/PushDisc/NOTES_H344_ASSEMBLY_DESIGN.md` and `Drive/PushDisc/NOTES_LENS_ROUTE.md`).

In the `Φ₀`-chart of `Work.Drive.PushDisc.straightFlatTubeArc` (the flat tube of the first arc,
which is straightened) the model space is `Mdl k = ℝ × ℝ × ℝ^k × ℝ^k`, `n = k + 1`, and:

* the **lens** `lensK = {|x| ≤ 1, 0 ≤ y ≤ 1 - x²}` is the image in the `(x,y)`-plane of the model
  disc `asymDisc k c` for `c = arch`;
* its **open part** `lensKo` is where the four bumps are non-degenerate;
* the disc approximation `Δ : ℝ × ℝ → Mdl k` (the `L0` of the lead's design) must have the two
  arcs as its boundary values, be immersive and injective on the lens, and have its *open* lens
  image disjoint from `Φ₀ '' f '' M` (the *cleanliness* row — this is what makes the isolation of
  the Whitney disc work without any reference to the given disc).

The two interface statements requested on top of this file are `exists_lensDiscApprox`
(the disc approximation, delegated) and `exists_lensFrames` (the two frames of the framing chart,
delegated).
-/

namespace Work.Drive.PushDisc

open scoped Manifold ContDiff
open Set Metric

noncomputable section

/-- The arch of the lens. -/
def arch (x : ℝ) : ℝ := 1 - x ^ 2

/-- The **lens** (the image of the model disc `asymDisc k arch` in the `(x,y)`-plane). -/
def lensK : Set (ℝ × ℝ) := {p | |p.1| ≤ 1 ∧ 0 ≤ p.2 ∧ p.2 ≤ arch p.1}

/-- The **open** lens: the region where the four bumps of `lensBump` are non-degenerate. -/
def lensKo : Set (ℝ × ℝ) := {p | |p.1| < 1 ∧ 0 < p.2 ∧ p.2 < arch p.1}

theorem lensKo_subset_lensK : lensKo ⊆ lensK := by
  rintro ⟨x, y⟩ ⟨hx, hy0, hy1⟩
  exact ⟨le_of_lt hx, le_of_lt hy0, le_of_lt hy1⟩

theorem arch_pos {x : ℝ} (hx : |x| < 1) : 0 < arch x := by
  have h : x ^ 2 < 1 := by rw [abs_lt] at hx; nlinarith [hx.1, hx.2]
  simp only [arch]; linarith

theorem arch_neg {x : ℝ} (hx : 1 < |x|) : arch x < 0 := by
  have h : 1 < x ^ 2 := by
    have h2 : (1 : ℝ) ^ 2 < |x| ^ 2 := by nlinarith [abs_nonneg x]
    simpa [sq_abs] using h2
  simp only [arch]; linarith

/-- The lens is compact. -/
theorem isCompact_lensK : IsCompact lensK := by
  have h1 : IsClosed {p : ℝ × ℝ | |p.1| ≤ 1} :=
    isClosed_le (continuous_abs.comp continuous_fst) continuous_const
  have h2 : IsClosed {p : ℝ × ℝ | 0 ≤ p.2} := isClosed_Ici.preimage continuous_snd
  have h3 : IsClosed {p : ℝ × ℝ | p.2 ≤ arch p.1} := by
    rw [show arch = fun x : ℝ => 1 - x ^ 2 from rfl]
    exact isClosed_le continuous_snd (continuous_const.sub (continuous_fst.pow 2))
  have heq : lensK = {p : ℝ × ℝ | |p.1| ≤ 1} ∩ ({p : ℝ × ℝ | 0 ≤ p.2}
      ∩ {p : ℝ × ℝ | p.2 ≤ arch p.1}) := by
    ext p
    exact ⟨fun h => ⟨h.1, h.2.1, h.2.2⟩, fun h => ⟨h.1, h.2.1, h.2.2⟩⟩
  have hsub : lensK ⊆ Metric.closedBall (0 : ℝ × ℝ) 2 := by
    intro p hp
    obtain ⟨hp1, hp2, hp3⟩ := hp
    have harch1 : arch p.1 ≤ 1 := by simp only [arch]; linarith [sq_nonneg p.1]
    rw [Metric.mem_closedBall, dist_zero_right, Prod.norm_def]
    have h1' : ‖p.1‖ ≤ 1 := by simpa [Real.norm_eq_abs] using hp1
    have h2' : ‖p.2‖ ≤ 1 := by
      rw [Real.norm_eq_abs, abs_le]; exact ⟨by linarith, by linarith⟩
    calc max ‖p.1‖ ‖p.2‖ ≤ 1 := max_le h1' h2'
      _ ≤ 2 := by norm_num
  rw [heq]
  exact Metric.isCompact_iff_isClosed_bounded.mpr
    ⟨h1.inter (h2.inter h3), isBounded_closedBall.subset hsub⟩

/-- The lens is convex (hence star-convex about any of its points). -/
theorem convex_lensK : Convex ℝ lensK := by
  intro p hp q hq a b ha hb hab
  obtain ⟨hp1, hp2, hp3⟩ := hp
  obtain ⟨hq1, hq2, hq3⟩ := hq
  have hp1' : -1 ≤ p.1 ∧ p.1 ≤ 1 := abs_le.mp hp1
  have hq1' : -1 ≤ q.1 ∧ q.1 ≤ 1 := abs_le.mp hq1
  have hp3' : p.2 ≤ 1 - p.1 ^ 2 := hp3
  have hq3' : q.2 ≤ 1 - q.1 ^ 2 := hq3
  refine ⟨?_, ?_, ?_⟩
  · rw [show (a • p + b • q).1 = a * p.1 + b * q.1 from rfl, abs_le]
    constructor <;> nlinarith
  · rw [show (a • p + b • q).2 = a * p.2 + b * q.2 from rfl]
    nlinarith [mul_nonneg ha hp2, mul_nonneg hb hq2]
  · rw [show (a • p + b • q).2 = a * p.2 + b * q.2 from rfl,
        show (a • p + b • q).1 = a * p.1 + b * q.1 from rfl]
    have key : (a * p.1 + b * q.1) ^ 2 ≤ a * p.1 ^ 2 + b * q.1 ^ 2 := by
      nlinarith [mul_nonneg ha hb, sq_nonneg (p.1 - q.1)]
    have harch : arch (a * p.1 + b * q.1) = 1 - (a * p.1 + b * q.1) ^ 2 := rfl
    rw [harch]
    nlinarith [mul_le_mul_of_nonneg_left hp3' ha, mul_le_mul_of_nonneg_left hq3' hb,
      ha, hb, hab, key]

/-- The inclusion of the `u`-block of the first sheet's plane: `u ↦ (0,0,u,0)`. -/
noncomputable def uPart (k : ℕ) : EuclideanSpace ℝ (Fin k) →ₗ[ℝ] Work.Drive.Whitney.Mdl k where
  toFun v := (0, 0, v, 0)
  map_add' x y := by ext <;> simp
  map_smul' c x := by ext <;> simp

/-- The standard `u`-frame of the model space: `ιu i = (0, 0, eᵢ, 0)`. -/
noncomputable def iotaU (k : ℕ) : Fin k → Work.Drive.Whitney.Mdl k :=
  fun i => uPart k (EuclideanSpace.single i (1 : ℝ))

/-- The defining property of the standard frame: `∑ i, u i • ιu i = (0,0,u,0)`. -/
theorem sum_smul_iotaU (k : ℕ) (u : EuclideanSpace ℝ (Fin k)) :
    (∑ i : Fin k, u i • iotaU k i) = (0, 0, u, 0) := by
  have hsum : (∑ i : Fin k, u i • (EuclideanSpace.single i (1 : ℝ))) = u := by
    have h : WithLp.ofLp (∑ i : Fin k, u i • (EuclideanSpace.single i (1 : ℝ)))
        = WithLp.ofLp u := by
      rw [WithLp.ofLp_sum, WithLp.ofLp]
      ext j
      simp [Finset.sum_apply, PiLp.ofLp_single, Pi.single_apply, Finset.sum_ite_eq]
    exact (WithLp.equiv 2 (Fin k → ℝ)).injective h
  have h1 : (∑ i : Fin k, u i • iotaU k i)
      = ∑ i : Fin k, uPart k (u i • (EuclideanSpace.single i (1 : ℝ))) := by
    refine Finset.sum_congr rfl (fun i _ => ?_)
    simp only [iotaU, map_smul]
  rw [h1, ← map_sum (uPart k), hsum]
  rfl

/-- The two vectors `(∂ₓ, ∂_y)` of a map on the `(x,y)`-plane, as a `2`-frame. -/
noncomputable def planeFrame (k : ℕ) (dx dy : ℝ × ℝ → Work.Drive.Whitney.Mdl k)
    (p : ℝ × ℝ) : Fin 2 → Work.Drive.Whitney.Mdl k := ![dx p, dy p]

/-- The **corner frame** `[∂ₓ, ∂_y, V, ιu]` at the point `(x, arch x)` of the top edge. -/
noncomputable def cornerFrame {k : ℕ} (dx dy : ℝ × ℝ → Work.Drive.Whitney.Mdl k)
    (V : ℝ → Fin k → Work.Drive.Whitney.Mdl k) (x : ℝ) : Fin (2 + k + k) → Work.Drive.Whitney.Mdl k :=
  Fin.append (Fin.append (planeFrame k dx dy (x, arch x)) (V x)) (iotaU k)

/-- The determinant of a frame, in a chosen linear identification of the model space with `ℝ^m`. -/
noncomputable def frameDet {k : ℕ} (m : ℕ)
    (T : Work.Drive.Whitney.Mdl k ≃ₗ[ℝ] EuclideanSpace ℝ (Fin m))
    (F : Fin m → Work.Drive.Whitney.Mdl k) : ℝ :=
  Matrix.det (fun i j => (T (F i)) j)

end

end Work.Drive.PushDisc
