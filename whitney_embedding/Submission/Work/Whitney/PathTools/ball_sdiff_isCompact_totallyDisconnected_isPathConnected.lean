import Mathlib
import Submission.Work.Whitney.PathTools.RemovabilityGeneral

/-!
# A compact totally disconnected set is removable in a ball of dimension `≥ 2`

Target: `Work.Whitney.PathTools.ball_sdiff_isCompact_totallyDisconnected_isPathConnected`.

`E` is a finite dimensional real inner product space with `2 ≤ finrank ℝ E`, `K ⊆ E` is compact
and totally disconnected, and `K ⊆ Metric.ball c r`.  Then `Metric.ball c r \ K` is path connected.

The global statement is
`Work.Whitney.PathTools.compl_isCompact_isTotallyDisconnected_pathConnected_gen`: a compact totally
disconnected set of dimension `≥ 2` does not separate.  It is transported to the ball by the radial
homeomorphism

  `ψ z = c + (r / (1 + ‖z‖)) • z`

from the whole space onto `Metric.ball c r`: the preimage `K' = ψ ⁻¹' K` is again compact and
totally disconnected, `E \ K'` is path connected, and `ball c r \ K = ψ '' (E \ K')`.
-/

namespace Work.Whitney.PathTools

open Set Metric Topology
open scoped Topology

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- **Removability in a ball.**  A compact totally disconnected subset of an open ball in a finite
dimensional real inner product space of dimension `≥ 2` can be removed without destroying path
connectedness. -/
theorem ball_sdiff_isCompact_totallyDisconnected_isPathConnected [FiniteDimensional ℝ E]
    (hm : 2 ≤ Module.finrank ℝ E) {c : E} {r : ℝ} (hr : 0 < r) {K : Set E}
    (hK : IsCompact K) (hsub : K ⊆ Metric.ball c r) (htd : IsTotallyDisconnected K) :
    IsPathConnected (Metric.ball c r \ K) := by
  classical
  haveI : Nontrivial E := Module.nontrivial_of_finrank_pos (R := ℝ) (M := E) (by omega)
  haveI : ProperSpace E := FiniteDimensional.proper ℝ E
  -- the radial parametrisation of the ball
  set ψ : E → E := fun z => c + (r / (1 + ‖z‖)) • z with hψdef
  have hψcont : Continuous ψ := by
    rw [hψdef]
    have hden : Continuous fun z : E => (1 : ℝ) + ‖z‖ := continuous_const.add continuous_norm
    exact continuous_const.add
      ((continuous_const.div₀ hden (fun z => by positivity)).smul continuous_id)
  have hpos : ∀ z : E, (0 : ℝ) < r / (1 + ‖z‖) := by
    intro z
    exact div_pos hr (by positivity)
  have hψmem : ∀ z : E, ‖ψ z - c‖ = r * ‖z‖ / (1 + ‖z‖) := by
    intro z
    rw [hψdef, add_sub_cancel_left, norm_smul, Real.norm_of_nonneg (le_of_lt (hpos z))]
    ring
  have hψlt : ∀ z : E, ‖ψ z - c‖ < r := by
    intro z
    rw [hψmem z, div_lt_iff₀ (by positivity : (0:ℝ) < 1 + ‖z‖)]
    nlinarith [norm_nonneg z, hr]
  -- surjectivity onto the ball
  have hψsurj : ∀ w ∈ Metric.ball c r, ∃ z : E, ψ z = w := by
    intro w hw
    have hd : ‖w - c‖ < r := by
      have h := Metric.mem_ball.mp hw
      rwa [dist_eq_norm] at h
    by_cases h0 : w - c = 0
    · refine ⟨0, ?_⟩
      have hwc : w = c := sub_eq_zero.mp h0
      rw [hwc, hψdef]
      simp only [norm_zero, add_zero, div_one, smul_zero, add_zero]
    · have hrne : r - ‖w - c‖ ≠ 0 := ne_of_gt (by linarith)
      refine ⟨(r - ‖w - c‖)⁻¹ • (w - c), ?_⟩
      have hnorm : ‖(r - ‖w - c‖)⁻¹ • (w - c)‖ = ‖w - c‖ / (r - ‖w - c‖) := by
        rw [norm_smul, Real.norm_of_nonneg (by positivity), inv_mul_eq_div]
      have h2 : (1 : ℝ) + ‖w - c‖ / (r - ‖w - c‖) = r / (r - ‖w - c‖) := by
        field_simp
        ring
      have hkey : r / (1 + ‖(r - ‖w - c‖)⁻¹ • (w - c)‖) = r - ‖w - c‖ := by
        rw [hnorm, h2, div_div_eq_mul_div]
        field_simp
      show c + (r / (1 + ‖(r - ‖w - c‖)⁻¹ • (w - c)‖)) •
        ((r - ‖w - c‖)⁻¹ • (w - c)) = w
      rw [hkey, smul_smul, mul_inv_cancel₀ hrne, one_smul]
      abel
  -- injectivity
  have hψinj : Function.Injective ψ := by
    intro z z' h
    have h1 : r * ‖z‖ / (1 + ‖z‖) = r * ‖z'‖ / (1 + ‖z'‖) := by
      rw [← hψmem z, ← hψmem z', h]
    have h2 : ‖z‖ = ‖z'‖ := by
      rw [div_eq_div_iff (ne_of_gt (by positivity : (0:ℝ) < 1 + ‖z‖))
        (ne_of_gt (by positivity : (0:ℝ) < 1 + ‖z'‖))] at h1
      have h1' : r * ‖z‖ = r * ‖z'‖ := by nlinarith [h1]
      exact mul_left_cancel₀ (ne_of_gt hr) h1'
    have h3 : (r / (1 + ‖z‖)) • z = (r / (1 + ‖z'‖)) • z' := by
      have h4 : c + (r / (1 + ‖z‖)) • z = c + (r / (1 + ‖z'‖)) • z' := h
      exact add_left_cancel h4
    have hcoe : r / (1 + ‖z'‖) = r / (1 + ‖z‖) := by rw [h2]
    rw [hcoe] at h3
    have h5 : (r / (1 + ‖z‖)) • (z - z') = 0 := by
      rw [smul_sub, h3, sub_self]
    rcases smul_eq_zero.mp h5 with h6 | h6
    · exact absurd h6 (ne_of_gt (hpos z))
    · exact sub_eq_zero.mp h6
  -- the preimage of `K`
  set K' : Set E := ψ ⁻¹' K with hK'def
  have hK'mem : ∀ z : E, z ∈ K' ↔ ψ z ∈ K := fun z => Set.mem_preimage
  have hK'closed : IsClosed K' := hK.isClosed.preimage hψcont
  -- a uniform distance of `K` from the sphere
  obtain ⟨δ, hδpos, hδle⟩ : ∃ δ : ℝ, 0 < δ ∧ ∀ w ∈ K, ‖w - c‖ ≤ r - δ := by
    rcases K.eq_empty_or_nonempty with h | hne
    · exact ⟨r / 2, by linarith, by simp [h]⟩
    · obtain ⟨w₀, hw₀, hmin⟩ := hK.exists_isMinOn hne
        (continuous_const.sub (continuous_id.sub continuous_const).norm).continuousOn
      have hval : 0 < r - ‖w₀ - c‖ := by
        have h1 := hsub hw₀
        rw [Metric.mem_ball, dist_eq_norm] at h1
        linarith
      refine ⟨r - ‖w₀ - c‖, hval, fun w hw => ?_⟩
      have h2 : r - ‖w₀ - c‖ ≤ r - ‖w - c‖ := hmin hw
      linarith
  have hK'bdd : Bornology.IsBounded K' := by
    refine (Metric.isBounded_iff_subset_closedBall (0 : E)).mpr ⟨(r - δ) / δ, ?_⟩
    intro z hz
    have hzK : ψ z ∈ K := (hK'mem z).mp hz
    have h1 : ‖ψ z - c‖ ≤ r - δ := hδle (ψ z) hzK
    rw [hψmem z, div_le_iff₀ (by positivity : (0:ℝ) < 1 + ‖z‖)] at h1
    rw [Metric.mem_closedBall, dist_zero_right, le_div_iff₀ hδpos]
    nlinarith [h1, norm_nonneg z]
  have hK'cpt : IsCompact K' := Metric.isCompact_iff_isClosed_bounded.mpr ⟨hK'closed, hK'bdd⟩
  have hK'td : IsTotallyDisconnected K' := by
    intro S hSK hSpre
    have himg : IsPreconnected (ψ '' S) := hSpre.image ψ hψcont.continuousOn
    have hsub' : ψ '' S ⊆ K := fun z ⟨s, hs, hzs⟩ => hzs ▸ hSK hs
    have hsing : (ψ '' S).Subsingleton := htd _ hsub' himg
    intro x hx y hy
    exact hψinj (hsing ⟨x, hx, rfl⟩ ⟨y, hy, rfl⟩)
  -- the global theorem in the flat space
  have hpc : IsPathConnected (K'ᶜ) :=
    compl_isCompact_isTotallyDisconnected_pathConnected_gen hm hK'cpt hK'td
  -- transport back
  have himgpc : IsPathConnected (ψ '' (K'ᶜ)) := hpc.image hψcont
  have hset : ψ '' (K'ᶜ) = Metric.ball c r \ K := by
    ext w
    constructor
    · rintro ⟨z, hz, rfl⟩
      refine ⟨?_, ?_⟩
      · rw [Metric.mem_ball, dist_eq_norm]
        exact hψlt z
      · intro hmem
        exact hz ((hK'mem z).mpr hmem)
    · intro hw
      obtain ⟨z, hz⟩ := hψsurj w hw.1
      exact ⟨z, fun hzK => hw.2 (hz ▸ ((hK'mem z).mp hzK)), hz⟩
  rwa [hset] at himgpc

end Work.Whitney.PathTools
