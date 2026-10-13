import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.RingTheory.Etale.Weakly
import Mathlib.RingTheory.Flat.TorsionFree
import Mathlib.RingTheory.TotallySplit
import Submission.Work.FTS_StreamBdry.Basic
import Submission.Work.FTS_StreamBdry.SB25.Defs
import Submission.Work.FTS_StreamBdry.SB25.cont_rate_left
import Submission.Work.FTS_StreamBdry.SB25.cont_rate_right

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# `Work.FTS_StreamBdry.SB25.lip_edge_trace`

Leaf **B2** of the SB2/SB5 plan (`sources/ftsV2/fts_sb25_leafplans.md`): a function on the strip
`z > 0`, `a < θ < b` whose slices are `θ`-Lipschitz with constant `K` has continuous edge traces
`fa` (at `θ = a`) and `fb` (at `θ = b`), approached at the linear rate `K·(θ - a)` resp.
`K·(b - θ)`.

The proof has three ingredients.

* **Lipschitz slices** (here, `slice_lipschitzOnWith`). For `0 < z` the mean value inequality
  (`Convex.norm_image_sub_le_of_norm_deriv_le`) turns the pointwise bound `|∂_θ f| ≤ K` into
  `LipschitzOnWith K (f z ·) (Ioo a b)`.
* **Extension** (here, `exists_lip_ext`). `LipschitzOnWith.extend_real` extends each slice to a
  globally `K`-Lipschitz function `G z : ℝ → ℝ`; the traces are `fa z = G z a`, `fb z = G z b`, and
  the rate bounds are the Lipschitz estimate read at the endpoints.
* **Continuity in `z`** (`cont_rate_left`, `cont_rate_right`, in their own modules).
  `G z a = lim_{θ→a⁺} f z θ` is a *uniform* (in `z`) limit of the continuous slices
  `z ↦ f z θ`, hence continuous on `Ioi 0`; likewise `G z b = lim_{θ→b⁻} f z θ` at the other end.

For `K < 0` the rate hypothesis is unsatisfiable (`|·| ≥ 0`), so the statement is vacuous; that
branch is discharged by `linarith` at a single interior point.
-/

noncomputable section
open Set

namespace Work.FTS_StreamBdry.SB25

set_option autoImplicit false

/-! ## §1 Lipschitz slices and their extension -/

/-- A slice of `f` is `K`-Lipschitz on `(a,b)` as soon as `|∂_θ f| ≤ K` there (mean value
inequality). -/
lemma slice_lipschitzOnWith {f : ℝ → ℝ → ℝ} {a b K z : ℝ} (hK : 0 ≤ K)
    (hd : ∀ θ ∈ Ioo a b, DifferentiableAt ℝ (fun θ' => f z θ') θ)
    (hB : ∀ θ ∈ Ioo a b, |Work.Spaces.pth f z θ| ≤ K) :
    LipschitzOnWith (Real.toNNReal K) (fun θ => f z θ) (Ioo a b) := by
  refine LipschitzOnWith.of_dist_le_mul fun x hx y hy => ?_
  have key := (convex_Ioo a b).norm_image_sub_le_of_norm_deriv_le (f := fun θ => f z θ)
    (x := y) (y := x) (C := K)
    (fun t ht => hd t ht) (fun t ht => by rw [Real.norm_eq_abs]; exact hB t ht) hy hx
  simpa [Real.dist_eq, Real.norm_eq_abs, Real.coe_toNNReal K hK] using key

/-- Each slice `f z ·` (`0 < z`) extends to a globally `K`-Lipschitz function `G z`. -/
lemma exists_lip_ext {f : ℝ → ℝ → ℝ} {a b K : ℝ} (hK : 0 ≤ K)
    (hd : ∀ z θ, 0 < z → θ ∈ Ioo a b → DifferentiableAt ℝ (fun θ' => f z θ') θ)
    (hB : ∀ z θ, 0 < z → θ ∈ Ioo a b → |Work.Spaces.pth f z θ| ≤ K) :
    ∃ G : ℝ → ℝ → ℝ, ∀ z, 0 < z →
      LipschitzWith (Real.toNNReal K) (G z) ∧ EqOn (fun θ => f z θ) (G z) (Ioo a b) := by
  refine ⟨fun z => if hz : 0 < z then
      Classical.choose ((slice_lipschitzOnWith hK (fun θ hθ => hd z θ hz hθ)
        (fun θ hθ => hB z θ hz hθ)).extend_real) else fun _ => 0, ?_⟩
  intro z hz
  simp only [dite_eq_left hz]
  exact Classical.choose_spec ((slice_lipschitzOnWith hK (fun θ hθ => hd z θ hz hθ)
        (fun θ hθ => hB z θ hz hθ)).extend_real)

/-! ## §2 The leaf -/

theorem lip_edge_trace (f : ℝ → ℝ → ℝ) (a b K : ℝ) :
    Work.FTS_StreamBdry.SB25.LipEdgeTrace f a b K := by
  intro hab hcont hd hB
  by_cases hK0 : 0 ≤ K
  · obtain ⟨G, hG⟩ := exists_lip_ext (f := f) (a := a) (b := b) (K := K) hK0 hd hB
    have hfa : ∀ z θ, 0 < z → θ ∈ Ioo a b → |f z θ - G z a| ≤ K * (θ - a) := by
      intro z θ hz hθ
      obtain ⟨hlip, heq⟩ := hG z hz
      have heqθ : f z θ = G z θ := heq hθ
      have h := hlip.dist_le_mul θ a
      rw [Real.dist_eq, Real.dist_eq, Real.coe_toNNReal K hK0] at h
      rw [abs_of_pos (by linarith [hθ.1] : (0 : ℝ) < θ - a)] at h
      calc |f z θ - G z a| = |G z θ - G z a| := by rw [heqθ]
        _ ≤ K * (θ - a) := h
    have hfb : ∀ z θ, 0 < z → θ ∈ Ioo a b → |f z θ - G z b| ≤ K * (b - θ) := by
      intro z θ hz hθ
      obtain ⟨hlip, heq⟩ := hG z hz
      have heqθ : f z θ = G z θ := heq hθ
      have h := hlip.dist_le_mul θ b
      rw [Real.dist_eq, Real.dist_eq, Real.coe_toNNReal K hK0] at h
      rw [abs_of_neg (by linarith [hθ.2] : θ - b < 0), neg_sub] at h
      calc |f z θ - G z b| = |G z θ - G z b| := by rw [heqθ]
        _ ≤ K * (b - θ) := h
    exact ⟨fun z => G z a, fun z => G z b,
      cont_rate_left (f := f) (g := fun z => G z a) (a := a) (b := b) (K := K)
        hab hK0 hcont hfa,
      cont_rate_right (f := f) (g := fun z => G z b) (a := a) (b := b) (K := K)
        hab hK0 hcont hfb,
      fun z θ hz hθ => ⟨hfa z θ hz hθ, hfb z θ hz hθ⟩⟩
  · -- `K < 0`: the rate hypothesis is unsatisfiable, so the statement is vacuous.
    exfalso
    have hKlt : K < 0 := not_le.mp hK0
    have hmid : (a + b) / 2 ∈ Ioo a b := ⟨by linarith, by linarith⟩
    have h1 := hB 1 ((a + b) / 2) one_pos hmid
    have h2 : (0 : ℝ) ≤ |Work.Spaces.pth f 1 ((a + b) / 2)| := abs_nonneg _
    linarith

end Work.FTS_StreamBdry.SB25
