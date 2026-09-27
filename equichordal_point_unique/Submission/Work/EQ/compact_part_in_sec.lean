import Mathlib
import Submission.Work.EQ.EquiLocalDefs

namespace Work.EQ

open Filter _root_.Topology

/-- Points of `S` in a fixed compact subset of `H0` lying over `ψ₁ = u`, with `u ≠ u₁` close to
`u₁`, are forced into any set that is a neighbourhood, in `H0`, of every point of the fibre of `S`
over `u₁`. -/
theorem compact_part_in_sec {a : ℝ} {h : ℂ → ℂ} {r : ℝ} (ha0 : 0 < a) (ha1 : a < 1)
    (hh : IsStableGerm a h r) {S T : Set ChainData} {u₁ : ℂ} (hu₁ : u₁ ≠ 0)
    (hSH : S ⊆ H0 a h)
    (hScl : ∀ q ∈ closure S, q ∈ H0 a h → q ∈ S)
    (hT : ∀ q ∈ S, q.2.1 = u₁ → T ∈ 𝓝[H0 a h] q)
    {C : Set ChainData} (hC : IsCompact C) (hCH : C ⊆ H0 a h) :
    ∃ ρ : ℝ, 0 < ρ ∧ ∀ u ∈ Metric.ball u₁ ρ, u ≠ u₁ → ∀ x ∈ C, x ∈ S → x.2.1 = u → x ∈ T := by
  -- Suppose no radius works; then there are counterexamples arbitrarily close to `u₁`.
  by_contra hcon
  have hforall : ∀ ρ : ℝ, 0 < ρ → ∃ u : ℂ, u ∈ Metric.ball u₁ ρ ∧ u ≠ u₁ ∧
      ∃ x : ChainData, x ∈ C ∧ x ∈ S ∧ x.2.1 = u ∧ x ∉ T := by
    intro ρ hρ
    by_contra hbad
    refine hcon ⟨ρ, hρ, ?_⟩
    intro u hu hu1 x hxC hxS hxpsi
    by_contra hxT
    exact hbad ⟨u, hu, hu1, x, hxC, hxS, hxpsi, hxT⟩
  choose U hUm hUne X hXC hXS hXpsi hXT using
    fun n : ℕ => hforall (1 / ((n : ℝ) + 1)) (by positivity)
  -- The parameters `U n` tend to `u₁`.
  have hbase : Tendsto (fun n : ℕ => (1 : ℝ) / ((n : ℝ) + 1)) atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop
      ((tendsto_natCast_atTop_atTop (R := ℝ)).atTop_add tendsto_const_nhds)
  have hUtend : Tendsto U atTop (𝓝 u₁) := by
    rw [tendsto_iff_dist_tendsto_zero]
    exact squeeze_zero (fun n => dist_nonneg)
      (fun n => le_of_lt (Metric.mem_ball.mp (hUm n))) hbase
  -- Compactness of `C` produces a limit point of the counterexamples.
  obtain ⟨x, hxC, φ, hφmono, hφtend⟩ := IsCompact.tendsto_subseq hC hXC
  have hφT : Tendsto φ atTop atTop := hφmono.tendsto_atTop
  have hUφ : Tendsto (fun n => U (φ n)) atTop (𝓝 u₁) := hUtend.comp hφT
  have hXφ : Tendsto (fun n => X (φ n)) atTop (𝓝 x) := hφtend
  -- The limit point lies over `u₁`.
  have hxpsi : x.2.1 = u₁ := by
    have hcont : Continuous (fun q : ChainData => q.2.1) := by fun_prop
    have h1 : Tendsto (fun n => (X (φ n)).2.1) atTop (𝓝 x.2.1) :=
      (hcont.tendsto x).comp hXφ
    have h2 : Tendsto (fun n => (X (φ n)).2.1) atTop (𝓝 u₁) :=
      hUφ.congr (fun n => (hXpsi (φ n)).symm)
    exact tendsto_nhds_unique h1 h2
  -- The limit point is a limit of points of `S`, hence lies in `S` by closedness of `S` in `H0`.
  have hxcl : x ∈ closure S :=
    isClosed_closure.mem_of_tendsto hXφ
      (Eventually.of_forall fun n => subset_closure (hXS (φ n)))
  have hxS : x ∈ S := hScl x hxcl (hCH hxC)
  -- Thus `T` is a neighbourhood of `x` in `H0`, and the counterexamples fall into it.
  obtain ⟨V, hVmem, hVsub⟩ :=
    mem_nhdsWithin_iff_exists_mem_nhds_inter.mp (hT x hxS hxpsi)
  obtain ⟨n, hn⟩ := (hXφ.eventually hVmem).exists
  exact hXT (φ n) (hVsub ⟨hn, hCH (hXC (φ n))⟩)

end Work.EQ
