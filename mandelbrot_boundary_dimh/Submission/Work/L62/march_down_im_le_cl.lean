import Mathlib
import Submission.Work.L62.chain
import Submission.Work.L62.march_up_im_nonneg

/-!
# `Work.L62.march_down_im_le_cl`: the lower-end marching direction forces `Im β ≤ Im cl`

Mirror of `Work.L62.march_up_im_nonneg` for the *lower* end of the cylinder.

Shishikura's Lemma 6.2 (lifted `ℂ/ℤ` model) produces, for `ĥ = d.E - β` with `d.E = Φ ∘ φ` the
lifted horn map, a backward chain of discs `W j` with `ĥ '' W (j+1) = W j` marching to one end of
the cylinder.  In the `s = -1` case the discs march to the *lower* end (`Im w → -∞`), and the
argument below shows that this forces `Im β ≤ Im cl`, where `cl` is the lower-end limit of the
horn map (`d.E w - w → cl` as `Im w → -∞`, field `E_lower` / hypothesis `hcl`).

Mechanism: for `w` of very negative imaginary part,

`Im (d.E w - β) - Im w = (Im (d.E w) - Im w) - Im β ≈ Im cl - Im β`.

So if `Im cl < Im β`, the disc `W (j+1)` sits *above* the disc `W j`: every `w ∈ W (j+1)` has

`Im w ≥ Im (ĥ w) + ε` with `ε = (Im β - Im cl) / 2 > 0`.

Since the discs `W (J+K)` are bounded (by `R`, say) at level `J` and all their heights are
eventually below any bound, the "height floors" of the discs *rise* by `ε` at every step:
`∀ K, ∀ w ∈ W (J+K), -R + K ε ≤ Im w`.  But `marching` (with `s = -1`) says that for `j` large
every point of `W j` has `Im w < -R`; at index `J + J₂` both bounds apply to a point of the
nonempty disc `W (J+J₂)` (nonempty because it is connected), a contradiction.
-/

namespace Work.L62

open MandelDim Set Filter Topology
open scoped Topology

noncomputable section

/-- The lower-end asymptotic of the horn map, in the quantitative form used by the marching
arguments: for every `ε > 0` the points of sufficiently negative imaginary part satisfy
`‖d.E w - w - cl‖ < ε`.  (A version of `MandelDim.ParabData.E_lower_iff` for a limit `cl`
supplied by the caller.) -/
theorem lowerEnd_eventually_norm {g₀ : ℂ → ℂ} {D : Set ℂ} (d : ParabData g₀ D) {cl : ℂ}
    (hcl : Tendsto (fun w => d.Φ (d.φ w) - w) MandelDim.lowerEnd (𝓝 cl)) {ε : ℝ} (hε : 0 < ε) :
    ∃ T : ℝ, ∀ w : ℂ, w.im < -T → ‖d.E w - w - cl‖ < ε := by
  have hmem : ∀ᶠ x : ℂ in MandelDim.lowerEnd, dist (d.Φ (d.φ x) - x) cl < ε :=
    hcl.eventually (Metric.ball_mem_nhds cl hε)
  rw [MandelDim.lowerEnd, Filter.eventually_iff, Filter.mem_comap] at hmem
  obtain ⟨t, ht, hts⟩ := hmem
  rw [Filter.mem_atBot_sets] at ht
  obtain ⟨R₀, hR₀⟩ := ht
  refine ⟨-R₀, fun w hw => ?_⟩
  have h1 : w.im ∈ t := hR₀ w.im (by linarith)
  have h3 := hts h1
  simp only [Set.mem_ofPred_eq] at h3
  simpa only [ParabData.E, dist_eq_norm] using h3

/-- Mirror of `Work.L62.march_up_im_nonneg`.  A chain `W` for the map `ĥ = d.E - β` marching to the LOWER end (`s = -1`) forces `β.im ≤ cl.im`, where `cl` is the lower-end limit of the horn map `d.E = Φ ∘ φ` (`ParabData.E_lower`).  Mechanism: at the lower end `d.E w - w → cl`, so `Im (d.E w - β) - Im w → Im cl - Im β`; if `Im β > Im cl` then going backwards along the chain raises the heights, contradicting that the discs march to `-∞`. -/
theorem march_down_im_le_cl {g₀ : ℂ → ℂ} {D : Set ℂ} (d : ParabData g₀ D) {cl : ℂ} (hcl : Tendsto (fun w => d.Φ (d.φ w) - w) MandelDim.lowerEnd (𝓝 cl)) {β : ℂ} {DR : Set ℂ} {ζa ζb : ℂ} {ρ C₀ C₁ C₁' : ℝ} {W : ℕ → Set ℂ} (h : Work.L62.IsChain d.E β DR ζa ζb ρ (-1 : ℝ) C₀ C₁ C₁' W) : β.im ≤ cl.im := by
  by_contra hcon
  have hlt : cl.im < β.im := lt_of_not_ge hcon
  -- the drift per step: `ε > 0` with `Im β = Im cl + 2 ε`
  set ε : ℝ := (β.im - cl.im) / 2 with hεdef
  have hεpos : 0 < ε := by rw [hεdef]; linarith
  have hβim : β.im = cl.im + 2 * ε := by rw [hεdef]; ring
  -- the lower-end asymptotic of `d.E`
  obtain ⟨T, hT⟩ := lowerEnd_eventually_norm d hcl hεpos
  -- beyond index `J` all discs sit below height `-T`, hence in the lower-end region
  obtain ⟨J, hJ⟩ := h.marching T
  have hJ' : ∀ j, J ≤ j → ∀ w ∈ W j, w.im < -T := by
    intro j hj w hw
    have h1 := hJ j hj w hw
    linarith
  obtain ⟨R, hR⟩ := (h.bounded J).1.exists_norm_le
  -- height floors of the discs rise by `ε` at each step
  have key : ∀ K : ℕ, ∀ w ∈ W (J + K), -R + (K : ℝ) * ε ≤ w.im := by
    intro K
    induction K with
    | zero =>
        intro w hw
        simp only [Nat.cast_zero, zero_mul, add_zero]
        have h1 : -|w.im| ≤ w.im := neg_abs_le w.im
        have h2 : |w.im| ≤ ‖w‖ := Complex.abs_im_le_norm w
        have h3 := hR w hw
        linarith
    | succ K ih =>
        intro w hw
        have hw' : w ∈ W ((J + K) + 1) := by rwa [← Nat.add_assoc] at hw
        have himage : d.E w - β ∈ W (J + K) := by
          rw [← (h.chain (J + K)).2.2]
          exact mem_image_of_mem _ hw'
        have hih := ih (d.E w - β) himage
        have hlow : w.im < -T := hJ' (J + K + 1) (by omega) w hw'
        have herr : ‖d.E w - w - cl‖ < ε := hT w hlow
        have h2 : |(d.E w - w - cl).im| ≤ ‖d.E w - w - cl‖ := Complex.abs_im_le_norm _
        have h4 : (d.E w - w - cl).im < ε :=
          lt_of_le_of_lt (le_trans (le_abs_self _) h2) herr
        simp only [Complex.sub_im] at h4
        have h5 : (d.E w - β).im + ε ≤ w.im := by
          have h6 : (d.E w - β).im = (d.E w).im - β.im := Complex.sub_im _ _
          rw [h6, hβim]
          linarith
        rw [Nat.cast_succ]
        linarith
  -- contradiction: `W (J + J₂)` is nonempty, but must lie both above and below height `-R`
  obtain ⟨J₂, hJ₂⟩ := h.marching R
  obtain ⟨w, hw⟩ := ((h.open_conn (J + J₂)).2).nonempty
  have h1 : w.im < -R := by
    have h3 := hJ₂ (J + J₂) (by omega) w hw
    linarith
  have h2 : -R ≤ w.im := by
    have h3 := key J₂ w hw
    have h4 : (0 : ℝ) ≤ (J₂ : ℝ) * ε := mul_nonneg (Nat.cast_nonneg _) (le_of_lt hεpos)
    linarith
  linarith

end

end Work.L62
