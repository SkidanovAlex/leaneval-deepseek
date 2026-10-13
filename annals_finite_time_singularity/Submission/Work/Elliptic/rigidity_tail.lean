import Mathlib.Analysis.SpecialFunctions.Pow.Continuity
import Mathlib.Topology.GDelta.MetrizableSpace

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end


open Filter Set Topology
namespace Work.Elliptic

/-- Rigidity of the tail profile: if `g z = A z^(-5/α) + B` on `z > 0` with
`0 < α < 5/2`, `g → 0` at `+∞`, and `z^2 g z → 0` as `z → 0+`, then `A = B = 0`. -/
lemma rigidity_tail (α : ℝ) (hα : 0 < α) (hα2 : α < 5 / 2) (A B : ℝ) (g : ℝ → ℝ)
    (hform : ∀ z ∈ Set.Ioi (0 : ℝ), g z = A * z ^ (-(5 / α)) + B)
    (hdec : Filter.Tendsto g Filter.atTop (nhds 0))
    (h0 : Filter.Tendsto (fun z => z ^ 2 * g z) (nhdsWithin (0 : ℝ) (Set.Ioi 0)) (nhds 0)) :
    A = 0 ∧ B = 0 := by
  have hαpos : 0 < 5 / α := by positivity
  have hgt : 2 < 5 / α := by rw [lt_div_iff₀ hα]; linarith
  have hp : 0 < 5 / α - 2 := by linarith
  have hpne : (5 / α - 2) ≠ 0 := ne_of_gt hp
  have hid : Tendsto (fun z : ℝ => z) (𝓝[>] (0:ℝ)) (𝓝 (0:ℝ)) :=
    (continuousAt_id.tendsto).mono_left (nhdsWithin_le_nhds)
  have hzp : Tendsto (fun z : ℝ => z ^ (5 / α - 2)) (𝓝[>] (0:ℝ)) (𝓝 0) := by
    have h := hid.rpow_const (Or.inr (le_of_lt hp))
    simpa [Real.zero_rpow hpne] using h
  have hzq : Tendsto (fun z : ℝ => z ^ (5 / α)) (𝓝[>] (0:ℝ)) (𝓝 0) := by
    have h := hid.rpow_const (Or.inr (le_of_lt hαpos))
    simpa [Real.zero_rpow (ne_of_gt hαpos)] using h
  -- On `z > 0`, `z^(5/α-2) * (z^2 * g z) = A + B z^(5/α)`.
  have heq : (fun z : ℝ => z ^ (5/α - 2) * (z^2 * g z))
      =ᶠ[𝓝[>] (0:ℝ)] (fun z => A + B * z^(5/α)) := by
    filter_upwards [self_mem_nhdsWithin] with z hz
    rw [hform z hz, ← Real.rpow_two (x := z)]
    have h2 : z ^ (5/α - 2) * z^(2:ℝ) = z^(5/α) := by
      rw [← Real.rpow_add hz (5/α - 2) 2, show 5/α - 2 + 2 = 5/α by ring]
    have h1 : z ^ (5/α-2) * z^(2:ℝ) * z^(-(5/α)) = 1 := by
      rw [h2, ← Real.rpow_add hz (5/α) (-(5/α)), show 5/α + -(5/α) = 0 by ring,
        Real.rpow_zero]
    have step : z ^ (5 / α - 2) * (z ^ (2:ℝ) * (A * z ^ (-(5 / α)) + B))
        = A * (z ^ (5/α - 2) * z^(2:ℝ) * z^(-(5/α)))
          + B * (z^(5/α-2)*z^(2:ℝ)) := by ring
    rw [step, h1, h2]; ring
  have hL : Tendsto (fun z : ℝ => z ^ (5/α - 2) * (z^2 * g z)) (𝓝[>] (0:ℝ)) (𝓝 0) := by
    have h := hzp.mul h0; simpa using h
  have hR : Tendsto (fun z : ℝ => A + B * z^(5/α)) (𝓝[>] (0:ℝ)) (𝓝 A) := by
    have h := (tendsto_const_nhds (x := A)).add (hzq.const_mul B); simpa using h
  -- `A = 0`: the same function tends to both `0` and `A`.
  have hA : A = 0 := by
    have hL' : Tendsto (fun z : ℝ => z ^ (5/α - 2) * (z^2 * g z)) (𝓝[>] (0:ℝ)) (𝓝 A) :=
      hR.congr' heq.symm
    exact (tendsto_nhds_unique hL hL').symm
  refine ⟨hA, ?_⟩
  -- With `A = 0`, `g` is eventually constantly `B`, so `B = 0`.
  have heq0 : g =ᶠ[Filter.atTop] (fun _ : ℝ => B) := by
    filter_upwards [eventually_gt_atTop (0:ℝ)] with z hz
    rw [hform z (Set.mem_Ioi.mpr hz), hA]; ring
  have hB : Tendsto (fun _ : ℝ => B) Filter.atTop (𝓝 (0:ℝ)) := hdec.congr' heq0
  exact (tendsto_const_nhds_iff).mp hB

end Work.Elliptic
