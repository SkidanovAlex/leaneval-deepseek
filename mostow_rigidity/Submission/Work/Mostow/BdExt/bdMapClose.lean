import Mathlib
import Submission.Work.Mostow.BdExt.bdMap
import Submission.Work.Mostow.BdExt.closeSeq

/-!
# `bdMapClose`: quasi-isometries at bounded distance have the same boundary map

If `Φ₁, Φ₂` are quasi-isometries of `ℍⁿ` and `hdist (Φ₁ u) (Φ₂ u) ≤ D` for all `u`, then
`bdMap n Φ₁ ξ = bdMap n Φ₂ ξ` for every `ξ ∈ Sph n`.

Indeed `bdMap n Φᵢ ξ` is the limit of `dirv (Φᵢ (ray ξ k))`: the two sequences are at bounded
hyperbolic distance and both escape to infinity (`lvl_image_ray`), so `closeSeq` identifies their
limits. -/

namespace Work.Mostow.BdExt

open Submission.Mostow Filter

noncomputable section

/-- The hyperbolic level along the image of a geodesic ray escapes to `+∞`: this is the
sequence form of `lvl_image_ray`. -/
lemma tendsto_lvl_image_ray (n : ℕ) (hI : Submission.Mostow.HypIsometryProp n)
    (Φ : E n → E n) (K C : ℝ) (hK : 1 ≤ K) (hC : 0 ≤ C)
    (hlow : ∀ u v, hdist u v ≤ K * hdist (Φ u) (Φ v) + C)
    (ξ : E n) (hξ : ξ ∈ Sph n) :
    Tendsto (fun k : ℕ => lvl (Φ (ray ξ (k : ℝ)))) atTop atTop := by
  have hKpos : 0 < K := lt_of_lt_of_le zero_lt_one hK
  have hbase : Tendsto (fun k : ℕ => (k : ℝ) / K) atTop atTop :=
    Tendsto.atTop_div_const hKpos tendsto_natCast_atTop_atTop
  have hshift : Tendsto (fun k : ℕ => (k : ℝ) / K + (-(C / K + lvl (Φ 0)))) atTop atTop :=
    tendsto_atTop_add_const_right _ _ hbase
  refine tendsto_atTop_mono (fun k => ?_) hshift
  refine le_trans (le_of_eq ?_)
    (lvl_image_ray n hI Φ K C hK hC hlow ξ hξ (k : ℝ) (Nat.cast_nonneg k))
  ring

theorem bdMapClose (n : ℕ) (hI : Submission.Mostow.HypIsometryProp n)
    (Φ₁ Φ₂ : Submission.Mostow.E n → Submission.Mostow.E n) (K₁ C₁ K₂ C₂ D : ℝ)
    (hK₁ : 1 ≤ K₁) (hC₁ : 0 ≤ C₁) (hK₂ : 1 ≤ K₂) (hC₂ : 0 ≤ C₂)
    (hup₁ : ∀ u v, Submission.Mostow.hdist (Φ₁ u) (Φ₁ v) ≤ K₁ * Submission.Mostow.hdist u v + C₁)
    (hlow₁ : ∀ u v, Submission.Mostow.hdist u v ≤ K₁ * Submission.Mostow.hdist (Φ₁ u) (Φ₁ v) + C₁)
    (hup₂ : ∀ u v, Submission.Mostow.hdist (Φ₂ u) (Φ₂ v) ≤ K₂ * Submission.Mostow.hdist u v + C₂)
    (hlow₂ : ∀ u v, Submission.Mostow.hdist u v ≤ K₂ * Submission.Mostow.hdist (Φ₂ u) (Φ₂ v) + C₂)
    (hD : 0 ≤ D) (hclose : ∀ u, Submission.Mostow.hdist (Φ₁ u) (Φ₂ u) ≤ D)
    (ξ : Submission.Mostow.E n) (hξ : ξ ∈ Submission.Mostow.Sph n) :
    Work.Mostow.BdExt.bdMap n Φ₁ ξ = Work.Mostow.BdExt.bdMap n Φ₂ ξ := by
  obtain ⟨-, hlim₁⟩ := bdMap_spec n hI Φ₁ K₁ C₁ hK₁ hC₁ hup₁ hlow₁ ξ hξ
  obtain ⟨-, hlim₂⟩ := bdMap_spec n hI Φ₂ K₂ C₂ hK₂ hC₂ hup₂ hlow₂ ξ hξ
  have hu : Tendsto (fun k : ℕ => lvl (Φ₁ (ray ξ (k : ℝ)))) atTop atTop :=
    tendsto_lvl_image_ray n hI Φ₁ K₁ C₁ hK₁ hC₁ hlow₁ ξ hξ
  have hv : Tendsto (fun k : ℕ => lvl (Φ₂ (ray ξ (k : ℝ)))) atTop atTop :=
    tendsto_lvl_image_ray n hI Φ₂ K₂ C₂ hK₂ hC₂ hlow₂ ξ hξ
  have hseq := closeSeq n hI (fun k : ℕ => Φ₁ (ray ξ (k : ℝ)))
    (fun k : ℕ => Φ₂ (ray ξ (k : ℝ))) D hD
    (fun k => hclose (ray ξ (k : ℝ))) hu hv (bdMap n Φ₁ ξ) hlim₁
  exact tendsto_nhds_unique hseq hlim₂

end

end Work.Mostow.BdExt
