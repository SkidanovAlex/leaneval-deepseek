import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Submission.Work.FTS.RegPkgGal.R7d.Vth_edge_cont
import Submission.Work.FTS.RegPkgGal.R7d.Vth_lip_slice

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

open Filter
open scoped Topology

namespace Work.FTS.RegPkgGal.R7d

/-- Barrier estimate for the angular component of a Lipschitz velocity field which vanishes on
the two angular endpoints.

If `(Vz, Vθ)` is `K`-Lipschitz on the open quadrant `(0,∞) × (0,π/2)`, uniformly for the
parameter `τ ∈ [0,S]`, jointly continuous on the closed strip `(0,∞) × [0,π/2] × [0,S]`, and
`Vθ` vanishes at `θ = 0` and at `θ = π/2` (for `τ > 0`), then for `z > 0`, `θ ∈ (0,π/2)` and
`τ ∈ [0,S]` one has `|Vθ z θ τ| ≤ K θ` and `|Vθ z θ τ| ≤ K (π/2 - θ)`.

The two ingredients are separated out: `Vth_lip_slice` turns the Lipschitz hypothesis into the
slicewise bound `|Vθ z θ₁ τ - Vθ z θ₂ τ| ≤ K |θ₁ - θ₂|`, and `Vth_edge_cont` gives the one-sided
continuity at the two endpoints.  Both limits `θ₂ → 0⁺` and `θ₂ → (π/2)⁻` are then taken by
`le_of_tendsto_of_tendsto`.

At `τ = 0` the two endpoint values are *recovered* from the joint continuity in `τ` together
with the `τ > 0` vanishing, so no case distinction is needed in the conclusion. -/
theorem Vth_barrier {Vz Vθ : ℝ → ℝ → ℝ → ℝ} {K S : ℝ} (hS : 0 < S) (hK : 0 ≤ K)
    (hlip : ∀ τ ∈ Set.Icc 0 S, LipschitzOnWith ⟨K, hK⟩
      (fun p : ℝ × ℝ => (Vz p.1 p.2 τ, Vθ p.1 p.2 τ))
      (Set.Ioi (0:ℝ) ×ˢ Set.Ioo (0:ℝ) (Real.pi / 2)))
    (hcont : ContinuousOn (fun p : ℝ × ℝ × ℝ => (Vz p.1 p.2.1 p.2.2, Vθ p.1 p.2.1 p.2.2))
      (Set.Ioi (0:ℝ) ×ˢ (Set.Icc (0:ℝ) (Real.pi / 2) ×ˢ Set.Icc (0:ℝ) S)))
    (h0 : ∀ z τ : ℝ, 0 < z → 0 < τ → τ ≤ S → Vθ z 0 τ = 0)
    (hπ : ∀ z τ : ℝ, 0 < z → 0 < τ → τ ≤ S → Vθ z (Real.pi / 2) τ = 0) :
    ∀ z θ τ : ℝ, 0 < z → 0 < θ → θ < Real.pi / 2 → 0 ≤ τ → τ ≤ S →
      |Vθ z θ τ| ≤ K * θ ∧ |Vθ z θ τ| ≤ K * (Real.pi / 2 - θ) := by
  intro z θ τ hz hθ0 hθπ hτ0 hτS
  have hπ2pos : (0:ℝ) < Real.pi / 2 := by linarith [Real.pi_pos]
  set reg : Set (ℝ × ℝ × ℝ) :=
    Set.Ioi (0:ℝ) ×ˢ (Set.Icc (0:ℝ) (Real.pi / 2) ×ˢ Set.Icc (0:ℝ) S) with hreg
  -- the two angular boundary points lie in the continuity region
  have hmem0 : (z, (0:ℝ), τ) ∈ reg := ⟨hz, ⟨⟨le_rfl, hπ2pos.le⟩, ⟨hτ0, hτS⟩⟩⟩
  have hmemπ : (z, Real.pi / 2, τ) ∈ reg := ⟨hz, ⟨⟨hπ2pos.le, le_rfl⟩, ⟨hτ0, hτS⟩⟩⟩
  -- the Lipschitz control of a slice (proved in `Vth_lip_slice`)
  have hlip_slice : ∀ θ₁ θ₂ : ℝ, θ₁ ∈ Set.Ioo (0:ℝ) (Real.pi / 2) →
      θ₂ ∈ Set.Ioo (0:ℝ) (Real.pi / 2) → |Vθ z θ₁ τ - Vθ z θ₂ τ| ≤ K * |θ₁ - θ₂| :=
    fun θ₁ θ₂ h₁ h₂ => Vth_lip_slice (K := K) (S := S) hK hlip hz ⟨hτ0, hτS⟩ h₁ h₂
  -- one-sided continuity in `θ` at the two endpoints (proved in `Vth_edge_cont`)
  have hedge := Vth_edge_cont (S := S) hcont hz hτ0 hτS
  have htend0 : Tendsto (fun θ' : ℝ => Vθ z θ' τ) (𝓝[>] (0:ℝ)) (𝓝 (Vθ z 0 τ)) := hedge.1
  have htendπ : Tendsto (fun θ' : ℝ => Vθ z θ' τ) (𝓝[<] (Real.pi / 2))
      (𝓝 (Vθ z (Real.pi / 2) τ)) := hedge.2
  -- the two endpoint values vanish (at `τ = 0` recovered by continuity in `τ`)
  have hb0 : Vθ z 0 τ = 0 := by
    rcases eq_or_lt_of_le hτ0 with hτ | hτ
    · subst hτ
      have hc : Tendsto (fun t : ℝ => Vθ z 0 t) (𝓝[>] (0:ℝ)) (𝓝 (Vθ z 0 0)) := by
        have hmap : Set.MapsTo (fun t : ℝ => (z, (0:ℝ), t)) (Set.Ioo (0:ℝ) S) reg := by
          intro t ht
          exact ⟨hz, ⟨⟨le_rfl, hπ2pos.le⟩, ⟨ht.1.le, ht.2.le⟩⟩⟩
        have hcw := ContinuousWithinAt.comp (f := fun t : ℝ => (z, (0:ℝ), t))
          (s := Set.Ioo (0:ℝ) S) (x := (0:ℝ))
          (hcont.continuousWithinAt hmem0) (by fun_prop) hmap
        change Tendsto (fun t : ℝ => (Vz z 0 t, Vθ z 0 t))
          (𝓝[Set.Ioo (0:ℝ) S] (0:ℝ)) (𝓝 (Vz z 0 0, Vθ z 0 0)) at hcw
        rw [nhdsWithin_Ioo_eq_nhdsGT hS, nhds_prod_eq] at hcw
        exact hcw.snd
      have hev : (fun _ : ℝ => (0:ℝ)) =ᶠ[𝓝[>] (0:ℝ)] (fun t : ℝ => Vθ z 0 t) := by
        filter_upwards [Ioo_mem_nhdsGT hS] with t ht
        exact (h0 z t hz ht.1 ht.2.le).symm
      exact tendsto_nhds_unique hc (Tendsto.congr' hev tendsto_const_nhds)
    · exact h0 z τ hz hτ hτS
  have hbπ : Vθ z (Real.pi / 2) τ = 0 := by
    rcases eq_or_lt_of_le hτ0 with hτ | hτ
    · subst hτ
      have hc : Tendsto (fun t : ℝ => Vθ z (Real.pi / 2) t) (𝓝[>] (0:ℝ))
          (𝓝 (Vθ z (Real.pi / 2) 0)) := by
        have hmap : Set.MapsTo (fun t : ℝ => (z, Real.pi / 2, t)) (Set.Ioo (0:ℝ) S) reg := by
          intro t ht
          exact ⟨hz, ⟨⟨hπ2pos.le, le_rfl⟩, ⟨ht.1.le, ht.2.le⟩⟩⟩
        have hcw := ContinuousWithinAt.comp (f := fun t : ℝ => (z, Real.pi / 2, t))
          (s := Set.Ioo (0:ℝ) S) (x := (0:ℝ))
          (hcont.continuousWithinAt hmemπ) (by fun_prop) hmap
        change Tendsto (fun t : ℝ => (Vz z (Real.pi / 2) t, Vθ z (Real.pi / 2) t))
          (𝓝[Set.Ioo (0:ℝ) S] (0:ℝ))
          (𝓝 (Vz z (Real.pi / 2) 0, Vθ z (Real.pi / 2) 0)) at hcw
        rw [nhdsWithin_Ioo_eq_nhdsGT hS, nhds_prod_eq] at hcw
        exact hcw.snd
      have hev : (fun _ : ℝ => (0:ℝ)) =ᶠ[𝓝[>] (0:ℝ)] (fun t : ℝ => Vθ z (Real.pi / 2) t) := by
        filter_upwards [Ioo_mem_nhdsGT hS] with t ht
        exact (hπ z t hz ht.1 ht.2.le).symm
      exact tendsto_nhds_unique hc (Tendsto.congr' hev tendsto_const_nhds)
    · exact hπ z τ hz hτ hτS
  have hθmem : θ ∈ Set.Ioo (0:ℝ) (Real.pi / 2) := ⟨hθ0, hθπ⟩
  -- the two limit passages `θ₂ → 0⁺` and `θ₂ → (π/2)⁻`
  have key0 : |Vθ z θ τ - Vθ z 0 τ| ≤ K * θ := by
    have hev : (fun θ₂ : ℝ => |Vθ z θ τ - Vθ z θ₂ τ|) ≤ᶠ[𝓝[>] (0:ℝ)]
        (fun θ₂ : ℝ => K * |θ - θ₂|) := by
      filter_upwards [Ioo_mem_nhdsGT hπ2pos] with θ₂ hθ₂
      exact hlip_slice θ θ₂ hθmem ⟨hθ₂.1, hθ₂.2⟩
    have hlim1 : Tendsto (fun θ₂ : ℝ => |Vθ z θ τ - Vθ z θ₂ τ|) (𝓝[>] (0:ℝ))
        (𝓝 |Vθ z θ τ - Vθ z 0 τ|) :=
      ((tendsto_const_nhds : Tendsto (fun _ : ℝ => Vθ z θ τ) (𝓝[>] (0:ℝ))
        (𝓝 (Vθ z θ τ))).sub htend0).abs
    have hlim2 : Tendsto (fun θ₂ : ℝ => K * |θ - θ₂|) (𝓝[>] (0:ℝ)) (𝓝 (K * θ)) := by
      have hA : Tendsto (fun x : ℝ => |θ - x|) (𝓝[>] (0:ℝ)) (𝓝 |θ - 0|) :=
        (((continuous_const.sub continuous_id).tendsto 0).mono_left
          nhdsWithin_le_nhds).abs
      have hB := hA.const_mul K
      simpa [abs_of_pos hθ0] using hB
    exact le_of_tendsto_of_tendsto hlim1 hlim2 hev
  have keyπ : |Vθ z θ τ - Vθ z (Real.pi / 2) τ| ≤ K * (Real.pi / 2 - θ) := by
    have hev : (fun θ₂ : ℝ => |Vθ z θ τ - Vθ z θ₂ τ|) ≤ᶠ[𝓝[<] (Real.pi / 2)]
        (fun θ₂ : ℝ => K * |θ - θ₂|) := by
      filter_upwards [Ioo_mem_nhdsLT hπ2pos] with θ₂ hθ₂
      exact hlip_slice θ θ₂ hθmem ⟨hθ₂.1, hθ₂.2⟩
    have hlim1 : Tendsto (fun θ₂ : ℝ => |Vθ z θ τ - Vθ z θ₂ τ|) (𝓝[<] (Real.pi / 2))
        (𝓝 |Vθ z θ τ - Vθ z (Real.pi / 2) τ|) :=
      ((tendsto_const_nhds : Tendsto (fun _ : ℝ => Vθ z θ τ) (𝓝[<] (Real.pi / 2))
        (𝓝 (Vθ z θ τ))).sub htendπ).abs
    have hlim2 : Tendsto (fun θ₂ : ℝ => K * |θ - θ₂|) (𝓝[<] (Real.pi / 2))
        (𝓝 (K * (Real.pi / 2 - θ))) := by
      have hA : Tendsto (fun x : ℝ => |θ - x|) (𝓝[<] (Real.pi / 2)) (𝓝 |θ - Real.pi / 2|) :=
        (((continuous_const.sub continuous_id).tendsto (Real.pi / 2)).mono_left
          nhdsWithin_le_nhds).abs
      have hB := hA.const_mul K
      have habs : |θ - Real.pi / 2| = Real.pi / 2 - θ := by
        rw [abs_of_neg (show θ - Real.pi / 2 < 0 by linarith)]
        ring
      simpa [habs] using hB
    exact le_of_tendsto_of_tendsto hlim1 hlim2 hev
  have hfinal0 : |Vθ z θ τ| ≤ K * θ := by
    have h := key0
    rw [hb0, sub_zero] at h
    exact h
  have hfinalπ : |Vθ z θ τ| ≤ K * (Real.pi / 2 - θ) := by
    have h := keyπ
    rw [hbπ, sub_zero] at h
    exact h
  exact ⟨hfinal0, hfinalπ⟩

end Work.FTS.RegPkgGal.R7d
