import Mathlib
import Submission.Work.RPB.Port.Drive.SeparationBase
import Submission.Work.RPB.Port.Drive.isOpen_Zc
import Submission.Work.RPB.Port.Drive.curve_deriv_ne_zero
import Submission.Work.RPB.Port.Drive.curve_arc_cover
import Submission.Work.RPB.Port.Drive.curve_straightening

/-!
# The curve separates a small disc around each of its points

`Work.RPB.Port.Drive.curve_localSep`: for a smooth embedded closed plane curve `γ : Circle → ℝ × ℝ` and
every `p ∈ range γ` there is a neighbourhood `U` of `p` which is split by `range γ` into two
nonempty open path connected pieces `U₁`, `U₂`, each of which accumulates at every point of
`U ∩ range γ` (`Work.RPB.Port.Drive.LocalSep`).

The proof has three ingredients, all of them about the `ℝ`-parametrisation `curve γ` of the curve
at a point, say `curve γ θ₀ = p`:

* **Covering by the local parameter.**  Since the parametrisation is injective modulo `2π`
  (`Work.RPB.Port.Drive.curve_eq_iff`), every point of the curve close to `p` is `curve γ t` for some `t`
  close to `θ₀`: this is a compactness statement about the parameters far from `θ₀`
  (`Work.RPB.Port.Drive.curve_arc_cover`).
* **Straightening.**  The normal-bundle map `(t, s) ↦ G t + s • rot90 (G' 0)` (where
  `G t = curve γ (θ₀ + t)`) is a local homeomorphism of the plane at the origin: its derivative has
  the two independent columns `G' 0` and `rot90 (G' 0)` (`Work.RPB.Port.Drive.curve_straightening`).
* **Assembly.**  Mapping a small ball through this local homeomorphism and splitting it according
  to the sign of the second coordinate gives the two pieces (this file).

The two analytic inputs are stated as explicit hypotheses of `curve_localSep_aux`, so that this
file builds (and can be reviewed) on its own.
-/

namespace Work.RPB.Port.Drive

open Manifold Set
open scoped ContDiff Topology

noncomputable section

/-- The plane curve `t ↦ γ (Circle.exp t)` of a smooth embedding is `C^∞`. -/
private lemma contDiff_curve_top (γ : Circle → ℝ × ℝ)
    (hγ : Manifold.IsSmoothEmbedding (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 1)))
      (modelWithCornersSelf ℝ (ℝ × ℝ)) ((⊤ : ℕ∞) : WithTop ℕ∞) γ) :
    ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (curve γ) := by
  have h1 : ContMDiff (𝓡 1) (𝓘(ℝ, ℝ × ℝ)) ((⊤ : ℕ∞) : WithTop ℕ∞) γ := hγ.contMDiff
  have h2 : ContMDiff (𝓘(ℝ, ℝ)) (𝓘(ℝ, ℝ × ℝ)) ((⊤ : ℕ∞) : WithTop ℕ∞) (curve γ) :=
    h1.comp (contMDiff_circleExp (m := ((⊤ : ℕ∞) : WithTop ℕ∞)))
  exact contMDiff_iff_contDiff.mp h2

/-- The ball of radius `ρ` around the origin of `ℝ × ℝ` (which carries the supremum norm) is the
open square of side `2ρ`. -/
private lemma mem_ball_zero_prod {ρ : ℝ} {z : ℝ × ℝ} :
    z ∈ Metric.ball (0 : ℝ × ℝ) ρ ↔ |z.1| < ρ ∧ |z.2| < ρ := by
  rw [Metric.mem_ball, dist_zero_right, Prod.norm_def, Real.norm_eq_abs, Real.norm_eq_abs,
    max_lt_iff]

/-- Membership in the ball of radius `ρ` around the origin, in coordinates. -/
private lemma mem_ball_zero_prod' {ρ b x₁ : ℝ} (h1 : |x₁| < ρ) (h2 : |b| < ρ) :
    ((x₁, b) : ℝ × ℝ) ∈ Metric.ball (0 : ℝ × ℝ) ρ := by
  rw [mem_ball_zero_prod]
  exact ⟨by simpa using h1, by simpa using h2⟩

/-- The distance of `(x.1, b)` from `(x.1, 0)` is `|b|`. -/
private lemma dist_mk_fst (x : ℝ × ℝ) (b : ℝ) : dist (x.1, b) (x.1, 0) = |b| := by
  simp [Prod.dist_eq]

/-- **Local separation, given the local arc and the straightening.**

`hcover` is `Work.RPB.Port.Drive.curve_arc_cover`: points of the curve close to `curve γ θ₀` come from
parameters close to `θ₀`.  `hstraight` is `Work.RPB.Port.Drive.curve_straightening`: the normal-bundle map
`(t, s) ↦ G t + s • rot90 (G' 0)` of a `C^∞` curve with nonvanishing derivative is a local
homeomorphism of the plane at the origin. -/
lemma curve_localSep_aux
    (hcover : ∀ (γ : Circle → ℝ × ℝ)
      (hγ : Manifold.IsSmoothEmbedding (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 1)))
        (modelWithCornersSelf ℝ (ℝ × ℝ)) ((⊤ : ℕ∞) : WithTop ℕ∞) γ)
      (θ₀ : ℝ) {δ : ℝ}, 0 < δ → δ < Real.pi →
      ∃ η > 0, ∀ c : Circle, γ c ∈ Metric.ball (curve γ θ₀) η →
        ∃ t : ℝ, |t - θ₀| < δ ∧ γ c = curve γ t)
    (hstraight : ∀ (G : ℝ → ℝ × ℝ), ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) G → deriv G 0 ≠ 0 →
      ∃ (r : ℝ) (Φ : OpenPartialHomeomorph (ℝ × ℝ) (ℝ × ℝ)), 0 < r ∧
        (∀ z : ℝ × ℝ, z ∈ Metric.ball (0 : ℝ × ℝ) r → z ∈ Φ.source) ∧
        (∀ z : ℝ × ℝ, Φ z = G z.1 + z.2 • rot90 (deriv G 0)))
    (γ : Circle → ℝ × ℝ)
    (hγ : Manifold.IsSmoothEmbedding (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 1)))
      (modelWithCornersSelf ℝ (ℝ × ℝ)) ((⊤ : ℕ∞) : WithTop ℕ∞) γ) :
    ∀ p ∈ Set.range γ, ∃ U U₁ U₂ : Set (ℝ × ℝ), LocalSep (Set.range γ) U U₁ U₂ ∧ p ∈ U := by
  intro p hp
  obtain ⟨c₀, rfl⟩ := hp
  obtain ⟨θ₀, hθ₀⟩ := Circle.exp_surjective c₀
  have hpθ : curve γ θ₀ = γ c₀ := by
    show γ (Circle.exp θ₀) = γ c₀
    rw [hθ₀]
  -- the curve, reparametrised so that it starts at `p`
  let G : ℝ → ℝ × ℝ := fun t => curve γ (θ₀ + t)
  have hG0 : G 0 = γ c₀ := by
    show curve γ (θ₀ + 0) = γ c₀
    rw [add_zero]
    exact hpθ
  have hGc : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) G :=
    (contDiff_curve_top γ hγ).comp (by fun_prop : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
      (fun t : ℝ => θ₀ + t))
  have hGder : deriv G 0 ≠ 0 := by
    have h : deriv G 0 = deriv (curve γ) θ₀ := by
      show deriv (fun t : ℝ => curve γ (θ₀ + t)) 0 = deriv (curve γ) θ₀
      rw [deriv_comp_const_add, add_zero]
    rw [h]
    exact curve_deriv_ne_zero γ hγ θ₀
  obtain ⟨r, Φ, hrpos, hsrc, hΦ⟩ := hstraight G hGc hGder
  -- the straightening map
  set H : ℝ × ℝ → ℝ × ℝ := fun z => G z.1 + z.2 • rot90 (deriv G 0) with hHdef
  have hH_apply : ∀ z : ℝ × ℝ, H z = G z.1 + z.2 • rot90 (deriv G 0) := fun z => rfl
  have hH_pair : ∀ a b : ℝ, H (a, b) = G a + b • rot90 (deriv G 0) := by
    intro a b
    exact hH_apply (a, b)
  have hHΦ : ∀ z : ℝ × ℝ, Φ z = H z := by
    intro z
    rw [hΦ z]
  have hHcont : Continuous H := by
    rw [hHdef]
    exact (hGc.continuous.comp continuous_fst).add (continuous_snd.smul continuous_const)
  have hH0 : H 0 = γ c₀ := by
    rw [show (0 : ℝ × ℝ) = (0, 0) from rfl, hH_pair 0 0, zero_smul, add_zero, hG0]
  have hH0c : H 0 = curve γ θ₀ := by rw [hH0, hpθ]
  -- the radius coming from the local arc statement
  set δc : ℝ := min (r / 2) (Real.pi / 2) with hδcdef
  have hδcpos : 0 < δc := lt_min (by linarith) (by positivity)
  have hδcpi : δc < Real.pi := lt_of_le_of_lt (min_le_right _ _) (by linarith [Real.pi_pos])
  have hδcr : δc ≤ r / 2 := min_le_left _ _
  obtain ⟨η, hηpos, hη⟩ := hcover γ hγ θ₀ hδcpos hδcpi
  -- shrink so that the straightening map sends a ball into the `η`-ball
  have hpre : H ⁻¹' Metric.ball (H 0) η ∈ 𝓝 (0 : ℝ × ℝ) :=
    hHcont.continuousAt.preimage_mem_nhds (Metric.ball_mem_nhds _ hηpos)
  obtain ⟨ε, hεpos, hεsub⟩ := Metric.mem_nhds_iff.mp hpre
  set ρ : ℝ := min ε (r / 2) with hρdef
  have hρpos : 0 < ρ := lt_min hεpos (by linarith)
  have hρr : ρ ≤ r := by
    rw [hρdef]; exact le_trans (min_le_right _ _) (by linarith)
  have hρε : ρ ≤ ε := by
    rw [hρdef]; exact min_le_left _ _
  set B : Set (ℝ × ℝ) := Metric.ball (0 : ℝ × ℝ) ρ with hBdef
  have hBopen : IsOpen B := by rw [hBdef]; exact Metric.isOpen_ball
  have hBsub : B ⊆ Φ.source := fun z hz => hsrc z (Metric.ball_subset_ball hρr hz)
  have hHB : H '' B ⊆ Metric.ball (curve γ θ₀) η := by
    rintro _ ⟨z, hz, rfl⟩
    have h := hεsub (Metric.ball_subset_ball hρε hz)
    rwa [hH0c] at h
  -- injectivity of the straightening on its source
  have hinj : Set.InjOn H Φ.source := by
    intro a ha b hb hab
    have h : Φ a = Φ b := by rw [hHΦ a, hHΦ b, hab]
    exact Φ.injOn ha hb h
  -- **the key point**: the curve meets `H '' B` only where the second coordinate vanishes
  have key : ∀ z ∈ B, z.2 ≠ 0 → H z ∉ Set.range γ := by
    intro z hzB hz2 hmem
    obtain ⟨c, hc⟩ := hmem
    obtain ⟨t, htδ, htval⟩ := hη c (by rw [hc]; exact hHB ⟨z, hzB, rfl⟩)
    have htδ' : |t - θ₀| < r / 2 := lt_of_lt_of_le htδ hδcr
    have hu1 : H (t - θ₀, 0) = curve γ t := by
      rw [hH_pair (t - θ₀) 0, zero_smul, add_zero]
      show curve γ (θ₀ + (t - θ₀)) = curve γ t
      congr 1
      ring
    have hu : H (t - θ₀, 0) = H z := by rw [hu1, ← htval, ← hc]
    have hsrc' : (t - θ₀, 0) ∈ Φ.source := by
      refine hsrc _ (mem_ball_zero_prod' (by simpa using (by linarith : |t - θ₀| < r))
        (by simpa using hrpos))
    have hzu : (t - θ₀, 0) = z := hinj hsrc' (hBsub hzB) hu
    exact hz2 (by rw [← hzu])
  -- the two pieces: `s > 0` and `s < 0` of the straightened ball
  set U : Set (ℝ × ℝ) := H '' B with hUdef
  set P : Set (ℝ × ℝ) := {z : ℝ × ℝ | 0 < z.2} with hPdef
  set Q : Set (ℝ × ℝ) := {z : ℝ × ℝ | z.2 < 0} with hQdef
  set U₁ : Set (ℝ × ℝ) := H '' (B ∩ P) with hU₁def
  set U₂ : Set (ℝ × ℝ) := H '' (B ∩ Q) with hU₂def
  have himg : ∀ S : Set (ℝ × ℝ), H '' S = Φ '' S := by
    intro S
    apply Set.image_congr
    intro z _
    exact (hHΦ z).symm
  have hPopen : IsOpen P := by
    rw [hPdef]
    exact isOpen_lt continuous_const continuous_snd
  have hQopen : IsOpen Q := by
    rw [hQdef]
    exact isOpen_lt continuous_snd continuous_const
  have hPconv : Convex ℝ P := by
    have h : P = (Set.univ : Set ℝ) ×ˢ Set.Ioi (0 : ℝ) := by
      rw [hPdef]; ext z; simp
    rw [h]
    exact convex_univ.prod (convex_Ioi 0)
  have hQconv : Convex ℝ Q := by
    have h : Q = (Set.univ : Set ℝ) ×ˢ Set.Iio (0 : ℝ) := by
      rw [hQdef]; ext z; simp
    rw [h]
    exact convex_univ.prod (convex_Iio 0)
  have hsubP : B ∩ P ⊆ Φ.source := fun z hz => hBsub hz.1
  have hsubQ : B ∩ Q ⊆ Φ.source := fun z hz => hBsub hz.1
  have hUopen : IsOpen U := by
    rw [hUdef, himg B]
    exact Φ.isOpen_image_of_subset_source hBopen hBsub
  have hU₁open : IsOpen U₁ := by
    rw [hU₁def, himg (B ∩ P)]
    exact Φ.isOpen_image_of_subset_source (hBopen.inter hPopen) hsubP
  have hU₂open : IsOpen U₂ := by
    rw [hU₂def, himg (B ∩ Q)]
    exact Φ.isOpen_image_of_subset_source (hBopen.inter hQopen) hsubQ
  have hpc₁ : IsPathConnected U₁ := by
    rw [hU₁def]
    refine IsPathConnected.image ?_ hHcont
    have hconv : Convex ℝ (B ∩ P) := by
      rw [hBdef]
      exact (convex_ball (0 : ℝ × ℝ) ρ).inter hPconv
    refine hconv.isPathConnected ⟨(0, ρ / 2), ?_, ?_⟩
    · exact mem_ball_zero_prod' (by simp; linarith)
        (by rw [abs_of_pos (by linarith : (0 : ℝ) < ρ / 2)]; linarith)
    · show (0 : ℝ) < ρ / 2
      linarith
  have hpc₂ : IsPathConnected U₂ := by
    rw [hU₂def]
    refine IsPathConnected.image ?_ hHcont
    have hconv : Convex ℝ (B ∩ Q) := by
      rw [hBdef]
      exact (convex_ball (0 : ℝ × ℝ) ρ).inter hQconv
    refine hconv.isPathConnected ⟨(0, -ρ / 2), ?_, ?_⟩
    · exact mem_ball_zero_prod' (by simp; linarith)
        (by rw [abs_of_neg (by linarith : -ρ / 2 < (0 : ℝ))]; linarith)
    · show (-ρ / 2 : ℝ) < 0
      linarith
  have hdisj : Disjoint U₁ U₂ := by
    rw [Set.disjoint_left]
    intro y hy₁ hy₂
    obtain ⟨z, ⟨hzB, hzP⟩, rfl⟩ := hy₁
    obtain ⟨z', ⟨hz'B, hz'Q⟩, hz'⟩ := hy₂
    have hzz' : z' = z := hinj (hBsub hz'B) (hBsub hzB) hz'
    subst hzz'
    rw [hPdef] at hzP
    rw [hQdef] at hz'Q
    simp only [Set.mem_ofPred_eq] at hzP hz'Q
    linarith
  have hunion : U₁ ∪ U₂ = U \ Set.range γ := by
    apply Set.Subset.antisymm
    · intro y hy
      rcases hy with hy | hy
      · obtain ⟨z, ⟨hzB, hzP⟩, rfl⟩ := hy
        rw [hPdef] at hzP
        simp only [Set.mem_ofPred_eq] at hzP
        exact ⟨⟨z, hzB, rfl⟩, key z hzB (ne_of_gt hzP)⟩
      · obtain ⟨z, ⟨hzB, hzQ⟩, rfl⟩ := hy
        rw [hQdef] at hzQ
        simp only [Set.mem_ofPred_eq] at hzQ
        exact ⟨⟨z, hzB, rfl⟩, key z hzB (ne_of_lt hzQ)⟩
    · rintro y ⟨⟨z, hzB, rfl⟩, hyK⟩
      have hz2 : z.2 ≠ 0 := by
        intro h
        refine hyK ⟨Circle.exp (θ₀ + z.1), ?_⟩
        show curve γ (θ₀ + z.1) = H z
        have h1 : G z.1 = H z := by rw [hH_apply z, h, zero_smul, add_zero]
        exact h1
      rcases lt_or_gt_of_ne hz2 with h | h
      · refine Or.inr ⟨z, ⟨hzB, ?_⟩, rfl⟩
        rw [hQdef]; exact h
      · refine Or.inl ⟨z, ⟨hzB, ?_⟩, rfl⟩
        rw [hPdef]; exact h
  -- every point of `U ∩ range γ` is a limit of points of each piece
  have acc₁ : ∀ q ∈ U ∩ Set.range γ, q ∈ closure U₁ := by
    rintro q ⟨⟨x, hxB, rfl⟩, hqK⟩
    have hx2 : x.2 = 0 := by
      by_contra h
      exact key x hxB h hqK
    have hxnorm : ‖x‖ < ρ := by
      have h := hxB; rw [hBdef, Metric.mem_ball, dist_zero_right] at h; exact h
    have hxeq : H x = H (x.1, 0) := by
      congr 1
      exact Prod.ext rfl hx2
    rw [Metric.mem_closure_iff]
    intro ε hε
    have hpre' : H ⁻¹' Metric.ball (H (x.1, 0)) ε ∈ 𝓝 (x.1, 0) :=
      hHcont.continuousAt.preimage_mem_nhds (Metric.ball_mem_nhds _ hε)
    obtain ⟨ν, hνpos, hνsub⟩ := Metric.mem_nhds_iff.mp hpre'
    set τ : ℝ := min (ν / 2) ((ρ - ‖x‖) / 2) with hτdef
    have hτpos : 0 < τ := lt_min (by linarith) (by linarith)
    have hτν : τ < ν := lt_of_le_of_lt (min_le_left _ _) (by linarith)
    have hτρ : τ < ρ - ‖x‖ := by
      have h1 : τ ≤ (ρ - ‖x‖) / 2 := min_le_right _ _
      linarith
    have hfst : |x.1| ≤ ‖x‖ := by
      rw [Prod.norm_def, Real.norm_eq_abs]; exact le_max_left _ _
    refine ⟨H (x.1, τ), ⟨(x.1, τ), ⟨?_, ?_⟩, rfl⟩, ?_⟩
    · exact mem_ball_zero_prod' (by simpa using (lt_of_le_of_lt hfst hxnorm))
        (by simpa [abs_of_pos hτpos] using
          (lt_of_lt_of_le hτρ (by linarith [norm_nonneg x]) : τ < ρ))
    · show (0 : ℝ) < τ
      exact hτpos
    · have hdist : dist ((x.1), τ) ((x.1), (0 : ℝ)) < ν := by
        rw [dist_mk_fst, abs_of_pos hτpos]
        exact hτν
      have h1 : dist (H (x.1, 0)) (H (x.1, τ)) < ε := by
        rw [dist_comm]
        exact hνsub hdist
      rw [hxeq]
      exact h1
  have acc₂ : ∀ q ∈ U ∩ Set.range γ, q ∈ closure U₂ := by
    rintro q ⟨⟨x, hxB, rfl⟩, hqK⟩
    have hx2 : x.2 = 0 := by
      by_contra h
      exact key x hxB h hqK
    have hxnorm : ‖x‖ < ρ := by
      have h := hxB; rw [hBdef, Metric.mem_ball, dist_zero_right] at h; exact h
    have hxeq : H x = H (x.1, 0) := by
      congr 1
      exact Prod.ext rfl hx2
    rw [Metric.mem_closure_iff]
    intro ε hε
    have hpre' : H ⁻¹' Metric.ball (H (x.1, 0)) ε ∈ 𝓝 (x.1, 0) :=
      hHcont.continuousAt.preimage_mem_nhds (Metric.ball_mem_nhds _ hε)
    obtain ⟨ν, hνpos, hνsub⟩ := Metric.mem_nhds_iff.mp hpre'
    set τ : ℝ := min (ν / 2) ((ρ - ‖x‖) / 2) with hτdef
    have hτpos : 0 < τ := lt_min (by linarith) (by linarith)
    have hτν : τ < ν := lt_of_le_of_lt (min_le_left _ _) (by linarith)
    have hτρ : τ < ρ - ‖x‖ := by
      have h1 : τ ≤ (ρ - ‖x‖) / 2 := min_le_right _ _
      linarith
    have hfst : |x.1| ≤ ‖x‖ := by
      rw [Prod.norm_def, Real.norm_eq_abs]; exact le_max_left _ _
    refine ⟨H (x.1, -τ), ⟨(x.1, -τ), ⟨?_, ?_⟩, rfl⟩, ?_⟩
    · exact mem_ball_zero_prod' (by simpa using (lt_of_le_of_lt hfst hxnorm))
        (by simpa [abs_of_neg (by linarith : -τ < (0 : ℝ))] using
          (lt_of_lt_of_le hτρ (by linarith [norm_nonneg x]) : τ < ρ))
    · show (-τ : ℝ) < 0
      linarith
    · have hdist : dist ((x.1), -τ) ((x.1), (0 : ℝ)) < ν := by
        rw [dist_mk_fst, abs_of_neg (by linarith : -τ < (0 : ℝ))]
        linarith
      have h1 : dist (H (x.1, 0)) (H (x.1, -τ)) < ε := by
        rw [dist_comm]
        exact hνsub hdist
      rw [hxeq]
      exact h1
  refine ⟨U, U₁, U₂, ⟨hUopen, hU₁open, hU₂open, hpc₁, hpc₂, hdisj, hunion, acc₁, acc₂⟩, ?_⟩
  refine ⟨0, ?_, ?_⟩
  · rw [hBdef, Metric.mem_ball, dist_zero_right, norm_zero]; exact hρpos
  · rw [hH0]

theorem curve_localSep (γ : Circle → ℝ × ℝ)
    (hγ : Manifold.IsSmoothEmbedding (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 1)))
      (modelWithCornersSelf ℝ (ℝ × ℝ)) ((⊤ : ℕ∞) : WithTop ℕ∞) γ) :
    ∀ p ∈ Set.range γ, ∃ U U₁ U₂ : Set (ℝ × ℝ), LocalSep (Set.range γ) U U₁ U₂ ∧ p ∈ U :=
  curve_localSep_aux curve_arc_cover curve_straightening γ hγ

end

end Work.RPB.Port.Drive
