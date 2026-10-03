import Mathlib

namespace Work.Horn

/-- Local trivialization / counting lemma: if `w₀ ∈ B` has finitely many preimages `S` in `B`,
each surrounded by a ball `Metric.ball x (ρ x) ⊆ B` on which `f` is injective, with pairwise
disjoint balls, and each such ball contains the full fibre of any `w` sufficiently close to `w₀`
(`hlocal`), while the preimage map is proper over `B` (`hprop`), then for all `w` near `w₀` the
set `B ∩ f ⁻¹' {w}` has cardinality `S.card`.

The properness hypothesis `hprop` is what rules out preimages of nearby `w` escaping the union of
the balls. -/
theorem eventually_ncard_eq_of_local_trivialization {B : Set ℂ} {f : ℂ → ℂ} {w₀ : ℂ}
    (hB : IsOpen B)
    (hcont : ContinuousOn f B)
    (hprop : ∀ L ⊆ B, IsCompact L → IsCompact (B ∩ f ⁻¹' L))
    (hw₀B : w₀ ∈ B)
    (S : Finset ℂ) (hS : ∀ z : ℂ, z ∈ (S : Set ℂ) ↔ z ∈ B ∧ f z = w₀)
    (ρ : ℂ → ℝ) (hρpos : ∀ x ∈ S, 0 < ρ x)
    (hρsub : ∀ x ∈ S, Metric.ball x (ρ x) ⊆ B)
    (hdisj : ∀ x ∈ S, ∀ y ∈ S, x ≠ y → Disjoint (Metric.ball x (ρ x)) (Metric.ball y (ρ y)))
    (hinj : ∀ x ∈ S, Set.InjOn f (Metric.ball x (ρ x)))
    (δ : ℂ → ℝ) (hδpos : ∀ x ∈ S, 0 < δ x)
    (hlocal : ∀ x ∈ S, ∀ w : ℂ, ‖w - w₀‖ < δ x → ∃ u ∈ Metric.ball x (ρ x), f u = w) :
    ∀ᶠ w in nhds w₀, (B ∩ f ⁻¹' {w}).ncard = S.card := by
  let U : Set ℂ := ⋃ x : (S : Set ℂ), Metric.ball (x : ℂ) (ρ x)
  have hUopen : IsOpen U := isOpen_iUnion (fun x => Metric.isOpen_ball)
  have hballU : ∀ x ∈ S, Metric.ball x (ρ x) ⊆ U := by
    intro x hx z hz
    exact Set.mem_iUnion.mpr ⟨⟨x, hx⟩, hz⟩
  -- Every `w` close enough to `w₀` has all its `B`-preimages inside the balls.
  have h_upper : ∀ᶠ w in nhds w₀, B ∩ f ⁻¹' {w} ⊆ U := by
    obtain ⟨ε₁, hε₁pos, hε₁sub⟩ := Metric.isOpen_iff.mp hB w₀ hw₀B
    have hLsub : Metric.closedBall w₀ (ε₁/2) ⊆ B :=
      (Metric.closedBall_subset_ball (by linarith)).trans hε₁sub
    have hLcomp : IsCompact (Metric.closedBall w₀ (ε₁/2)) := isCompact_closedBall w₀ (ε₁/2)
    have hKcomp : IsCompact (B ∩ f ⁻¹' Metric.closedBall w₀ (ε₁/2)) := hprop _ hLsub hLcomp
    have hAcomp : IsCompact ((B ∩ f ⁻¹' Metric.closedBall w₀ (ε₁/2)) \ U) := hKcomp.diff hUopen
    have hFAcomp : IsCompact (f '' ((B ∩ f ⁻¹' Metric.closedBall w₀ (ε₁/2)) \ U)) :=
      hAcomp.image_of_continuousOn (hcont.mono (fun z hz => hz.1.1))
    have hFAnotin : w₀ ∉ f '' ((B ∩ f ⁻¹' Metric.closedBall w₀ (ε₁/2)) \ U) := by
      rintro ⟨a, haA, haeq⟩
      have haB : a ∈ B := haA.1.1
      have haS : a ∈ S := (hS a).mpr ⟨haB, haeq⟩
      have hmem : a ∈ Metric.ball a (ρ a) :=
        Metric.mem_ball.mpr (by rw [dist_self]; exact hρpos a haS)
      exact haA.2 (hballU a haS hmem)
    obtain ⟨εa, hεapos, hεasub⟩ :=
      Metric.isOpen_iff.mp hFAcomp.isClosed.isOpen_compl w₀ hFAnotin
    rw [Metric.eventually_nhds_iff]
    refine ⟨min εa (ε₁/2), lt_min hεapos (by linarith), ?_⟩
    intro w hw z hz
    have hzB : z ∈ B := hz.1
    have hzfw : f z = w := Set.mem_singleton_iff.mp hz.2
    by_contra hzU
    have hzL : f z ∈ Metric.closedBall w₀ (ε₁/2) := by
      rw [Metric.mem_closedBall, hzfw]
      exact le_of_lt (lt_of_lt_of_le hw (min_le_right _ _))
    have hzA : z ∈ (B ∩ f ⁻¹' Metric.closedBall w₀ (ε₁/2)) \ U :=
      ⟨⟨hzB, hzL⟩, hzU⟩
    have hwin : w ∈ f '' ((B ∩ f ⁻¹' Metric.closedBall w₀ (ε₁/2)) \ U) := by
      rw [← hzfw]; exact ⟨z, hzA, rfl⟩
    have hwball : w ∈ Metric.ball w₀ εa := by
      rw [Metric.mem_ball]; exact lt_of_lt_of_le hw (min_le_left _ _)
    exact (hεasub hwball) hwin
  -- Every `w` close enough to `w₀` has a preimage in each ball.
  have h_small : ∀ᶠ w in nhds w₀, ∀ x ∈ S, ‖w - w₀‖ < δ x := by
    rw [Finset.eventually_all]
    intro x hx
    filter_upwards [Metric.ball_mem_nhds w₀ (hδpos x hx)] with w hw
    simpa only [Metric.mem_ball, dist_eq_norm] using hw
  filter_upwards [h_upper, h_small] with w hUw hδw
  rw [← Set.ncard_coe_finset S]
  -- A chosen preimage of `w` inside each ball, as a function on `S`.
  let g : (a : ℂ) → a ∈ (S : Set ℂ) → ℂ := fun a ha => Classical.choose (hlocal a ha w (hδw a ha))
  have hg_mem : ∀ (a : ℂ) (ha : a ∈ (S : Set ℂ)), g a ha ∈ B ∩ f ⁻¹' {w} := by
    intro a ha
    have hspec := Classical.choose_spec (hlocal a ha w (hδw a ha))
    refine ⟨hρsub a ha hspec.1, ?_⟩
    change f (Classical.choose (hlocal a ha w (hδw a ha))) ∈ ({w} : Set ℂ)
    simpa using hspec.2
  -- `g` is injective: distinct balls are disjoint.
  have hg_inj : ∀ (a b : ℂ) (ha : a ∈ (S : Set ℂ)) (hb : b ∈ (S : Set ℂ)),
      g a ha = g b hb → a = b := by
    intro a b ha hb heq
    by_contra hab
    have hsa : g a ha ∈ Metric.ball a (ρ a) :=
      (Classical.choose_spec (hlocal a ha w (hδw a ha))).1
    have hsb : g b hb ∈ Metric.ball b (ρ b) :=
      (Classical.choose_spec (hlocal b hb w (hδw b hb))).1
    have hdj := Set.disjoint_left.mp (hdisj a ha b hb hab)
    exact (hdj hsa) (heq.symm ▸ hsb)
  -- `g` is surjective onto the fibre: `h_upper` puts every preimage into a ball,
  -- where injectivity identifies it with the chosen point.
  have hg_surj : ∀ b ∈ B ∩ f ⁻¹' {w}, ∃ a, ∃ ha : a ∈ (S : Set ℂ), g a ha = b := by
    intro b hb
    have hbfw : f b = w := Set.mem_singleton_iff.mp hb.2
    have hbU : b ∈ U := hUw hb
    obtain ⟨x, hxball⟩ := Set.mem_iUnion.mp hbU
    refine ⟨x.1, x.2, ?_⟩
    have hspec := Classical.choose_spec (hlocal x.1 x.2 w (hδw x.1 x.2))
    exact (hinj x.1 x.2 hxball hspec.1 (hbfw.trans hspec.2.symm)).symm
  exact (Set.ncard_congr g hg_mem hg_inj hg_surj).symm

end Work.Horn
