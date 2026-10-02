import Mathlib

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


namespace Work.ParamRays

/-- The exterior of a closed ball in `ℂ` is preconnected: it is the image of the preconnected
set `{r : ℝ | M < r} × univ` under the continuous surjection `(r, θ) ↦ r · exp(θ * I)`. -/
lemma isPreconnected_lt_norm {M : ℝ} (hM : 0 ≤ M) : IsPreconnected {z : ℂ | M < ‖z‖} := by
  have hdom : IsPreconnected ({r : ℝ | M < r} ×ˢ (Set.univ : Set ℝ)) :=
    IsPreconnected.prod isPreconnected_Ioi isPreconnected_univ
  have hcont : ContinuousOn (fun p : ℝ × ℝ => (p.1 : ℂ) * Complex.exp ((p.2 : ℂ) * Complex.I))
      ({r : ℝ | M < r} ×ˢ (Set.univ : Set ℝ)) := by fun_prop
  have himg := hdom.image (fun p : ℝ × ℝ => (p.1 : ℂ) * Complex.exp ((p.2 : ℂ) * Complex.I)) hcont
  convert himg using 1
  ext z
  simp only [Set.mem_image, Set.mem_ofPred_eq, Set.mem_prod, Set.mem_univ]
  constructor
  · intro hz
    exact ⟨(‖z‖, z.arg), ⟨hz, trivial⟩, Complex.norm_mul_exp_arg_mul_I z⟩
  · rintro ⟨p, hp, rfl⟩
    rw [norm_mul, Complex.norm_real, Complex.norm_exp_ofReal_mul_I, mul_one]
    rw [Real.norm_eq_abs, abs_of_pos (lt_of_le_of_lt hM hp.1)]
    exact hp.1

/-- **Superlevel sets of `‖f‖` for an entire coercive `f` are preconnected.**

If `f : ℂ → ℂ` is entire and `‖f z‖ → ∞` as `z → ∞` (`hc`), then for every `R ≥ 0` the set
`{z : ℂ | R < ‖f z‖}` is preconnected.  Indeed it is open, and its complement is compact; the
exterior of a large ball lies in it and is preconnected, so any separation of it would leave a
nonempty bounded open piece `B` with `frontier B ⊆ {‖f‖ ≤ R}`.  The maximum modulus principle
(`Complex.norm_le_of_forall_mem_frontier_norm_le`) then forces `‖f‖ ≤ R` on `B`, contradicting
`B ⊆ {R < ‖f‖}`. -/
theorem isPreconnected_lt_norm_of_differentiable {f : ℂ → ℂ} (hf : Differentiable ℂ f)
    (hc : Filter.Tendsto (fun z : ℂ => ‖f z‖) (Filter.cocompact ℂ) Filter.atTop)
    {R : ℝ} (hR : 0 ≤ R) : IsPreconnected {z : ℂ | R < ‖f z‖} := by
  let S : Set ℂ := {z : ℂ | R < ‖f z‖}
  change IsPreconnected S
  have hSopen : IsOpen S := isOpen_lt continuous_const hf.continuous.norm
  have hSmem : S ∈ Filter.cocompact ℂ := hc.eventually (Filter.Ioi_mem_atTop R)
  rw [Filter.mem_cocompact] at hSmem
  obtain ⟨K, hKc, hKsub⟩ := hSmem
  obtain ⟨r₀, hr₀⟩ := hKc.isBounded.subset_closedBall (0 : ℂ)
  let M : ℝ := max (max r₀ 0) R
  have hM0 : 0 ≤ M := le_trans hR (le_max_right _ _)
  have hKball : K ⊆ Metric.closedBall 0 M := by
    intro z hz
    have h1 := hr₀ hz
    rw [Metric.mem_closedBall, dist_zero_right] at h1 ⊢
    exact le_trans h1 (le_trans (le_max_left r₀ 0) (le_max_left (max r₀ 0) R))
  have hOsub : {z : ℂ | M < ‖z‖} ⊆ S := by
    intro z hz
    apply hKsub
    rw [Set.mem_compl_iff]
    intro hzK
    have h2 : ‖z‖ ≤ M := by
      have := hKball hzK
      rwa [Metric.mem_closedBall, dist_zero_right] at this
    exact absurd h2 (not_le.mpr hz)
  have hOpre : IsPreconnected {z : ℂ | M < ‖z‖} := isPreconnected_lt_norm hM0
  intro u v hu hv huv hEu hEv
  by_contra hcon
  have hdisj : Disjoint (S ∩ u) (S ∩ v) := by
    rw [Set.disjoint_left]
    intro x hx hx'
    exact hcon ⟨x, hx.1, hx.2, hx'.2⟩
  have hAopen : IsOpen (S ∩ u) := hSopen.inter hu
  have hBopen : IsOpen (S ∩ v) := hSopen.inter hv
  have hcover : S ⊆ (S ∩ u) ∪ (S ∩ v) := by
    intro z hz
    rcases huv hz with h | h
    · exact Or.inl ⟨hz, h⟩
    · exact Or.inr ⟨hz, h⟩
  have hOAB : {z : ℂ | M < ‖z‖} ⊆ (S ∩ u) ∪ (S ∩ v) := fun z hz => hcover (hOsub hz)
  rcases hOpre.subset_or_subset hAopen hBopen hdisj hOAB with hOA | hOB
  · have hBbound : Bornology.IsBounded (S ∩ v) := by
      refine (Metric.isBounded_closedBall (x := (0:ℂ)) (r := M)).subset ?_
      intro z hz
      rw [Metric.mem_closedBall, dist_zero_right]
      by_contra hle
      exact (Set.disjoint_left.mp hdisj (hOA (not_le.mp hle))) hz
    have hfront : ∀ z ∈ frontier (S ∩ v), ‖f z‖ ≤ R := by
      intro z hz
      have hzcl : z ∈ closure (S ∩ v) := hz.1
      have hzni : z ∉ S ∩ v := by
        have h2 := hz.2
        rwa [hBopen.interior_eq] at h2
      by_contra hnot
      have hzS : z ∈ S := not_le.mp hnot
      have hzA : z ∈ S ∩ u := by
        refine ⟨hzS, ?_⟩
        rcases huv hzS with h | h
        · exact h
        · exact absurd ⟨hzS, h⟩ hzni
      obtain ⟨w, hw⟩ := mem_closure_iff.mp hzcl (S ∩ u) hAopen hzA
      exact Set.disjoint_left.1 hdisj hw.1 hw.2
    have hd : DiffContOnCl ℂ f (S ∩ v) := ⟨hf.differentiableOn, hf.continuous.continuousOn⟩
    obtain ⟨z₀, hz₀⟩ := hEv
    have hzle := Complex.norm_le_of_forall_mem_frontier_norm_le hBbound hd hfront (subset_closure hz₀)
    exact absurd hzle (not_le.mpr hz₀.1)
  · have hAbound : Bornology.IsBounded (S ∩ u) := by
      refine (Metric.isBounded_closedBall (x := (0:ℂ)) (r := M)).subset ?_
      intro z hz
      rw [Metric.mem_closedBall, dist_zero_right]
      by_contra hle
      exact (Set.disjoint_left.mp hdisj hz) (hOB (not_le.mp hle))
    have hfront : ∀ z ∈ frontier (S ∩ u), ‖f z‖ ≤ R := by
      intro z hz
      have hzcl : z ∈ closure (S ∩ u) := hz.1
      have hzni : z ∉ S ∩ u := by
        have h2 := hz.2
        rwa [hAopen.interior_eq] at h2
      by_contra hnot
      have hzS : z ∈ S := not_le.mp hnot
      have hzB : z ∈ S ∩ v := by
        refine ⟨hzS, ?_⟩
        rcases huv hzS with h | h
        · exact absurd ⟨hzS, h⟩ hzni
        · exact h
      obtain ⟨w, hw⟩ := mem_closure_iff.mp hzcl (S ∩ v) hBopen hzB
      exact Set.disjoint_left.1 hdisj.symm hw.1 hw.2
    have hd : DiffContOnCl ℂ f (S ∩ u) := ⟨hf.differentiableOn, hf.continuous.continuousOn⟩
    obtain ⟨z₀, hz₀⟩ := hEu
    have hzle := Complex.norm_le_of_forall_mem_frontier_norm_le hAbound hd hfront (subset_closure hz₀)
    exact absurd hzle (not_le.mpr hz₀.1)

end Work.ParamRays
