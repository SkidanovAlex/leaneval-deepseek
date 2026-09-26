import Mathlib
import Submission.Work.Drive.localInjBlur
import Submission.Work.Drive.chordSweepSmooth

/-!
# From *pointwise* local injectivity of a parameter blur to global injectivity

Lane H2 (`Work.Drive.unknotted_of_avoidingArc`), the slices clause of the top end.

The chamfered sweep loop is *not* differentiable at its four junctions, and the old route to the
slices clause asked for **one** direction whose pairing grows along the whole loop
(`Work.Drive.sweepSlicesCone`), which is refuted.  The route of this module is the honest local one:

* `Work.Drive.exists_uniform_local_radius` — **compactness**: if a curve is *pointwise* locally
  injective, then on a compact set it is injective on a *uniform* window.  (This is the step that
  turns "the blur is injective near every point" into a single number.)
* `Work.Drive.injOn_Ico_of_radius_and_farSep` — **the global assembly**: a uniform local radius plus
  the already-proved far separation `Work.Drive.sweepFamFarSep` gives injectivity on one period.
* `Work.Drive.exists_injOn_blur_of_halfspace_window` — the **local** injectivity of a parameter blur
  on an interval `[α, β]` on which the pairing with a fixed `n` grows at rate `c > 0`: the blur is
  injective on `(α + δ, β - δ)`.
* `Work.Drive.exists_uniform_halfspace_radius` — the **piece lemma**: on a compact parameter interval
  on which the curve is `C¹` with nonvanishing derivative there are **uniform** `ρ, c > 0` with
  `c ≤ ⟪γ' t, γ' s⟫` whenever `|s - t| ≤ ρ`.
* `Work.Drive.exists_injOn_blur_local_of_halfspace_piece` — the corollary in the exact shape of the
  pointwise hypothesis of `Work.Drive.exists_uniform_local_radius`.

Nothing here mentions knots: the whole module is about a curve, a kernel `b` and the blur
`Work.Drive.blur b δ γ` (which *is* the sliced sweep `Work.Drive.sweepSmoothT r D lam δ s` — see
`Work.Drive.blur_eq_sweepSmoothT`).
-/

noncomputable section
namespace Work.Drive

open scoped Real Topology intervalIntegral
open MeasureTheory

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

/-! ## 1. A uniform local radius from pointwise local injectivity -/

/-- **Compactness step.**  If a curve `γ` is injective on a neighbourhood of every point, then on a
compact set `K` there is a *single* radius `R > 0` such that `γ` is injective on `(t - R, t + R)`
for every `t ∈ K`. -/
theorem exists_uniform_local_radius {γ : ℝ → E} {K : Set ℝ} (hK : IsCompact K)
    (hloc : ∀ t : ℝ, ∃ r : ℝ, 0 < r ∧ Set.InjOn γ (Set.Ioo (t - r) (t + r))) :
    ∃ R : ℝ, 0 < R ∧ ∀ t ∈ K, Set.InjOn γ (Set.Ioo (t - R) (t + R)) := by
  classical
  choose r hr using hloc
  rcases K.eq_empty_or_nonempty with hK0 | hKne
  · refine ⟨1, one_pos, ?_⟩
    intro t ht
    rw [hK0] at ht
    exact absurd ht (Set.notMem_empty t)
  set U : ℝ → Set ℝ := fun t => Set.Ioo (t - r t / 2) (t + r t / 2) with hU
  have hUopen : ∀ t : ℝ, IsOpen (U t) := fun t => isOpen_Ioo
  have hcov : K ⊆ ⋃ t, U t := by
    intro t ht
    refine Set.mem_iUnion.mpr ⟨t, ?_⟩
    have h1 : 0 < r t := (hr t).1
    rw [hU]
    exact ⟨by linarith, by linarith⟩
  obtain ⟨F, hF⟩ := hK.elim_finite_subcover U hUopen hcov
  have hFne : F.Nonempty := by
    rcases F.eq_empty_or_nonempty with h | h
    · exfalso
      obtain ⟨x, hx⟩ := hKne
      have hx' := hF hx
      rw [h] at hx'
      simpa using hx'
    · exact h
  refine ⟨F.inf' hFne (fun t => r t / 2), ?_, ?_⟩
  · refine (Finset.lt_inf'_iff hFne).mpr ?_
    intro i _
    exact half_pos (hr i).1
  · intro t ht
    have ht' := hF ht
    rw [Set.mem_iUnion] at ht'
    obtain ⟨s, hs⟩ := ht'
    rw [Set.mem_iUnion] at hs
    obtain ⟨hsF, hts⟩ := hs
    rw [hU] at hts
    have hts' : |t - s| < r s / 2 := by
      rw [abs_lt]
      exact ⟨by linarith [hts.1], by linarith [hts.2]⟩
    have hRs : F.inf' hFne (fun t => r t / 2) ≤ r s / 2 := Finset.inf'_le _ hsF
    intro x hx y hy hxy
    refine (hr s).2 ?_ ?_ hxy
    · have h1 : |x - t| < F.inf' hFne (fun t => r t / 2) := by
        rw [abs_lt]
        exact ⟨by linarith [hx.1], by linarith [hx.2]⟩
      have h2 : |x - s| < r s := by
        have h3 : |x - s| ≤ |x - t| + |t - s| := by
          rw [show x - s = (x - t) + (t - s) by ring]
          exact abs_add_le _ _
        linarith
      rw [abs_lt] at h2
      exact ⟨by linarith [h2.1], by linarith [h2.2]⟩
    · have h1 : |y - t| < F.inf' hFne (fun t => r t / 2) := by
        rw [abs_lt]
        exact ⟨by linarith [hy.1], by linarith [hy.2]⟩
      have h2 : |y - s| < r s := by
        have h3 : |y - s| ≤ |y - t| + |t - s| := by
          rw [show y - s = (y - t) + (t - s) by ring]
          exact abs_add_le _ _
        linarith
      rw [abs_lt] at h2
      exact ⟨by linarith [h2.1], by linarith [h2.2]⟩

/-! ## 2. The global assembly -/

/-- **Global injectivity from a uniform local radius and the far separation.**  For a `p`-periodic
curve `γ`: if `γ` is injective on every window of radius `R` centred at a point of `[0, p]`, and if
pairs of parameters at distance in `[R, p - R]` have images at distance at least `ρ > 0`, then `γ`
is injective on `[0, p)`. -/
theorem injOn_Ico_of_radius_and_farSep {γ : ℝ → E} {p R ρ : ℝ} (hp : 0 < p) (hR : 0 < R)
    (hρ : 0 < ρ) (hper : ∀ t : ℝ, γ (t + p) = γ t)
    (hloc : ∀ t ∈ Set.Icc (0 : ℝ) p, Set.InjOn γ (Set.Ioo (t - R) (t + R)))
    (hsep : ∀ t₁ ∈ Set.Ico (0 : ℝ) p, ∀ t₂ ∈ Set.Ico (0 : ℝ) p,
      R ≤ |t₂ - t₁| → |t₂ - t₁| ≤ p - R → ρ ≤ ‖γ t₁ - γ t₂‖) :
    Set.InjOn γ (Set.Ico (0 : ℝ) p) := by
  have key : ∀ t₁ ∈ Set.Ico (0 : ℝ) p, ∀ t₂ ∈ Set.Ico (0 : ℝ) p, t₁ ≤ t₂ →
      γ t₁ = γ t₂ → t₁ = t₂ := by
    intro t₁ ht₁ t₂ ht₂ hle heq
    have hd : 0 ≤ t₂ - t₁ := sub_nonneg.mpr hle
    have habs : |t₂ - t₁| = t₂ - t₁ := abs_of_nonneg hd
    have ht₁Icc : t₁ ∈ Set.Icc (0 : ℝ) p := ⟨ht₁.1, ht₁.2.le⟩
    rcases lt_or_ge (t₂ - t₁) R with hlt | hge
    · refine hloc t₁ ht₁Icc ⟨by linarith, by linarith⟩ ⟨by linarith, by linarith⟩ heq
    · rcases le_or_gt (t₂ - t₁) (p - R) with hfar | hwrap
      · have h := hsep t₁ ht₁ t₂ ht₂ (by rwa [habs]) (by rwa [habs])
        rw [heq, sub_self, norm_zero] at h
        linarith
      · have hwin : t₂ - p ∈ Set.Ioo (t₁ - R) (t₁ + R) := by
          refine ⟨by linarith [hwrap], by linarith [ht₂.2, ht₁.1, hR]⟩
        have hγ : γ (t₂ - p) = γ t₁ := by
          have h1 : γ (t₂ - p + p) = γ (t₂ - p) := hper (t₂ - p)
          rw [show t₂ - p + p = t₂ by ring] at h1
          rw [← h1]
          exact heq.symm
        have := hloc t₁ ht₁Icc ⟨by linarith [hR], by linarith [hR]⟩ hwin hγ.symm
        exact absurd this (by linarith [ht₁.1, ht₂.2])
  intro t₁ ht₁ t₂ ht₂ heq
  rcases le_total t₁ t₂ with h | h
  · exact key t₁ ht₁ t₂ ht₂ h heq
  · exact (key t₂ ht₂ t₁ ht₁ h heq.symm).symm

/-! ## 3. Local injectivity of the blur on a half-space window -/

/-- **Local injectivity of the blur on an interval of growth.**  If the pairing of the velocity with a
fixed `n` is at least `c > 0` on `[α, β]` and `2δ < β - α`, then the blur of width `δ` is injective
on `(α + δ, β - δ)`.  (The blur window of every such parameter stays inside `[α, β]`, where the
pairing grows.) -/
theorem exists_injOn_blur_of_halfspace_window {b : ℝ → ℝ} (hb : Continuous b)
    (hnn : ∀ u : ℝ, 0 ≤ b u) (hmass : 0 < ∫ u in (-1 : ℝ)..1, b u)
    {γ γ' : ℝ → E} (hγ : Continuous γ) (hder : ∀ x : ℝ, HasDerivAt γ (γ' x) x)
    {n : E} {α β c δ : ℝ} (hc : 0 < c) (hδ : 0 < δ) (h2δ : 2 * δ < β - α)
    (hint : IntervalIntegrable (fun s => inner ℝ n (γ' s)) volume α β)
    (hpos : ∀ s ∈ Set.Icc α β, c ≤ inner ℝ n (γ' s)) :
    Set.InjOn (blur b δ γ) (Set.Ioo (α + δ) (β - δ)) := by
  have hαβ : α ≤ β := by linarith
  have h := injOn_blur_of_halfspace hb hnn hmass hδ hc hγ (α := α) (β := β) (a := α + δ)
    (d := β - δ) hαβ (by linarith) (by linarith) (fun s _ => hder s) hint hpos
  exact h.mono Set.Ioo_subset_Icc_self

/-! ## 4. The piece lemma: a uniform half-space radius on a compact piece -/

/-- **The piece lemma.**  On a compact parameter interval `[α, β]` on which `γ'` is continuous and
nowhere zero there are *uniform* constants `ρ > 0` and `c > 0` such that
`c ≤ ⟪γ' t, γ' s⟫` whenever `t, s ∈ [α, β]` and `|s - t| ≤ ρ`.

Concretely: `c₀ = min ‖γ'‖ > 0` on `[α, β]`, and uniform continuity of `γ'` gives `ρ` with
`‖γ' s - γ' t‖ < c₀/4` there; then `‖γ' t‖ ≥ 3c₀/4` and
`⟪γ' t, γ' s⟫ ≥ (3c₀/4)·(3c₀/4 - c₀/4) = 3c₀²/8 > 0`. -/
theorem exists_uniform_halfspace_radius {γ' : ℝ → E} (hγ'c : Continuous γ')
    {α β : ℝ} (hαβ : α ≤ β) (hne : ∀ s ∈ Set.Icc α β, γ' s ≠ 0) :
    ∃ ρ : ℝ, 0 < ρ ∧ ∃ c : ℝ, 0 < c ∧
      ∀ t ∈ Set.Icc α β, ∀ s ∈ Set.Icc α β, |s - t| ≤ ρ → c ≤ inner ℝ (γ' t) (γ' s) := by
  obtain ⟨x₀, hx₀, hmin⟩ :=
    isCompact_Icc.exists_isMinOn (⟨α, le_rfl, hαβ⟩ : (Set.Icc α β).Nonempty)
      hγ'c.continuousOn.norm
  set m : ℝ := ‖γ' x₀‖ with hm
  have hmpos : 0 < m := by
    rw [hm]; exact norm_pos_iff.mpr (hne x₀ hx₀)
  have huc : UniformContinuousOn γ' (Set.Icc α β) :=
    isCompact_Icc.uniformContinuousOn_of_continuous hγ'c.continuousOn
  rw [Metric.uniformContinuousOn_iff] at huc
  obtain ⟨δ₀, hδ₀pos, hδ₀⟩ := huc (m / 4) (by linarith)
  refine ⟨δ₀ / 2, half_pos hδ₀pos, 3 * m ^ 2 / 8, by positivity, ?_⟩
  intro t ht s hs hst
  have hclose : ‖γ' s - γ' t‖ < m / 4 := by
    have h1 : dist (γ' t) (γ' s) < m / 4 := by
      refine hδ₀ t ht s hs ?_
      rw [Real.dist_eq, abs_sub_comm]
      linarith
    rw [dist_eq_norm, norm_sub_rev] at h1
    exact h1
  have hnt : m ≤ ‖γ' t‖ := hmin ht
  have hns : m ≤ ‖γ' s‖ := hmin hs
  have hb1 : 3 * m / 4 ≤ ‖γ' t‖ := by
    have h2 : |‖γ' s‖ - ‖γ' t‖| ≤ ‖γ' s - γ' t‖ := abs_norm_sub_norm_le _ _
    rw [abs_le] at h2
    linarith [h2.2]
  have hsplit : inner ℝ (γ' t) (γ' s)
      = inner ℝ (γ' t) (γ' t) + inner ℝ (γ' t) (γ' s - γ' t) := by
    rw [inner_sub_right]; ring
  have hself : inner ℝ (γ' t) (γ' t) = ‖γ' t‖ ^ 2 := real_inner_self_eq_norm_sq _
  have hlow : -(‖γ' t‖ * ‖γ' s - γ' t‖) ≤ inner ℝ (γ' t) (γ' s - γ' t) := by
    have h3 := abs_real_inner_le_norm (γ' t) (γ' s - γ' t)
    rw [abs_le] at h3
    exact h3.1
  have hstep : ‖γ' t‖ * ‖γ' s - γ' t‖ < ‖γ' t‖ * (m / 4) :=
    mul_lt_mul_of_pos_left hclose (by linarith [hb1, hmpos])
  have hlow2 : -(‖γ' t‖ * (m / 4)) ≤ inner ℝ (γ' t) (γ' s - γ' t) := by linarith
  have hmid : ‖γ' t‖ ^ 2 - ‖γ' t‖ * (m / 4) ≤ inner ℝ (γ' t) (γ' s) := by
    rw [hsplit, hself]; linarith
  have hkey : (3 * m / 4) * (3 * m / 4 - m / 4) ≤ inner ℝ (γ' t) (γ' s) := by
    have hquad : (3 * m / 4) * (m / 2) ≤ ‖γ' t‖ ^ 2 - ‖γ' t‖ * (m / 4) := by
      nlinarith [hb1, hmpos, norm_nonneg (γ' t)]
    have hval' : (3 * m / 4) * (3 * m / 4 - m / 4) = (3 * m / 4) * (m / 2) := by ring
    linarith [hval'.le, hquad, hmid]
  have hval : (3 * m / 4) * (3 * m / 4 - m / 4) = 3 * m ^ 2 / 8 := by ring
  linarith [hkey, hval.ge]

/-! ## 5. The corollary in the shape of the pointwise hypothesis -/

/-- **Pointwise local injectivity of the blur at the interior points of a piece.**  From the uniform
half-space data `(ρ, c)` of `exists_uniform_halfspace_radius`, and for a blur width `δ < ρ`, the blur
is locally injective at every parameter `t` whose blur window `(t - δ, t + δ)` stays inside the piece
(`t ∈ (α + δ, β - δ)`). -/
theorem exists_injOn_blur_local_of_halfspace_piece {b : ℝ → ℝ} (hb : Continuous b)
    (hnn : ∀ u : ℝ, 0 ≤ b u) (hmass : 0 < ∫ u in (-1 : ℝ)..1, b u)
    {γ γ' : ℝ → E} (hγ : Continuous γ) (hder : ∀ x : ℝ, HasDerivAt γ (γ' x) x)
    (hγ'c : Continuous γ')
    {α β ρ c δ : ℝ} (hρ : 0 < ρ) (hc : 0 < c) (hαβ : α ≤ β)
    (hwin : ∀ t ∈ Set.Icc α β, ∀ s ∈ Set.Icc α β, |s - t| ≤ ρ → c ≤ inner ℝ (γ' t) (γ' s))
    (hδ : 0 < δ) (hδρ : δ < ρ) :
    ∀ t ∈ Set.Ioo (α + δ) (β - δ),
      ∃ r : ℝ, 0 < r ∧ Set.InjOn (blur b δ γ) (Set.Ioo (t - r) (t + r)) := by
  intro t ht
  rw [Set.mem_Ioo] at ht
  have htlo : α < t - δ := by linarith [ht.1]
  have hthi : t + δ < β := by linarith [ht.2]
  set a : ℝ := max α (t - ρ) with ha
  set bB : ℝ := min β (t + ρ) with hbB
  have ha3 : a < t - δ := max_lt_iff.mpr ⟨htlo, by linarith⟩
  have hb3 : t + δ < bB := lt_min_iff.mpr ⟨hthi, by linarith⟩
  have haI : a ∈ Set.Icc α β := by
    refine ⟨le_max_left _ _, ?_⟩
    linarith [ha3, hδ]
  have hbI : bB ∈ Set.Icc α β := by
    refine ⟨?_, min_le_left _ _⟩
    linarith [hb3, hδ]
  have hab : a < bB := by linarith
  have hpos : ∀ s ∈ Set.Icc a bB, c ≤ inner ℝ (γ' t) (γ' s) := by
    intro s hs
    have hsa : t - ρ ≤ s := le_trans (le_max_right _ _) hs.1
    have hsb : s ≤ t + ρ := le_trans hs.2 (min_le_right _ _)
    refine hwin t ⟨by linarith [ht.1], by linarith [ht.2]⟩ s
      ⟨le_trans haI.1 hs.1, le_trans hs.2 hbI.2⟩ ?_
    rw [abs_le]
    exact ⟨by linarith, by linarith⟩
  have hint : IntervalIntegrable (fun s => inner ℝ (γ' t) (γ' s)) volume a bB :=
    (continuous_const.inner hγ'c).intervalIntegrable _ _
  have h2δ : 2 * δ < bB - a := by linarith
  have hinj := exists_injOn_blur_of_halfspace_window hb hnn hmass hγ hder hc hδ
    h2δ hint hpos
  have htmem : t ∈ Set.Ioo (a + δ) (bB - δ) := ⟨by linarith, by linarith⟩
  set e1 : ℝ := t - (a + δ) with he1
  set e2 : ℝ := (bB - δ) - t with he2
  have he1pos : 0 < e1 := by rw [he1]; linarith [htmem.1]
  have he2pos : 0 < e2 := by rw [he2]; linarith [htmem.2]
  have hmin1 : min e1 e2 ≤ e1 := min_le_left _ _
  have hmin2 : min e1 e2 ≤ e2 := min_le_right _ _
  have hminpos : 0 < min e1 e2 := lt_min he1pos he2pos
  refine ⟨min e1 e2 / 2, by linarith, ?_⟩
  refine hinj.mono ?_
  intro x hx
  rw [Set.mem_Ioo] at hx ⊢
  constructor
  · have h1 : a + δ ≤ t - min e1 e2 / 2 := by
      rw [he1] at hmin1; linarith
    linarith [hx.1]
  · have h2 : t + min e1 e2 / 2 ≤ bB - δ := by
      rw [he2] at hmin2; linarith
    linarith [hx.2]

/-! ## 6. The bridge to the sliced sweep -/

open LeanEval.KnotTheory.Quadrisecant in
/-- The parameter blur of the chamfered sweep loop *is* the sliced sweep. -/
lemma blur_eq_sweepSmoothT (r : ℝ → Space) {d : BandArcData} (D : SweepData d)
    (lam δ s t : ℝ) :
    blur sweepBump δ (sweepLoopChamfer r D lam s) t = sweepSmoothT r D lam δ s t := rfl

/-! ## 7. The velocity of the blur at the interior points of a piece -/

/-- **The velocity of the blur does not vanish in the middle of a piece.**  With the uniform
half-space data `(ρ, c)` of `exists_uniform_halfspace_radius` and a blur width `δ < ρ`, the vector

    ∫ u in (-1)..1, b u • γ' (t - δ * u)

(the velocity of the blur, when `γ` is differentiable with derivative `γ'` everywhere — the caller
supplies that as `hderiv`) is **nonzero** at every `t` whose blur window `(t - δ, t + δ)` stays
inside the piece.  Indeed its pairing with `γ' t` is `≥ c · ∫ b > 0`. -/
theorem blurVel_ne_zero_of_halfspace_piece {b : ℝ → ℝ} (hb : Continuous b)
    (hnn : ∀ u : ℝ, 0 ≤ b u) (hmass : 0 < ∫ u in (-1 : ℝ)..1, b u)
    {γ γ' : ℝ → E} (hγ'c : Continuous γ')
    {α β ρ c δ : ℝ} (hρ : 0 < ρ) (hc : 0 < c) (hαβ : α ≤ β)
    (hwin : ∀ t ∈ Set.Icc α β, ∀ s ∈ Set.Icc α β, |s - t| ≤ ρ → c ≤ inner ℝ (γ' t) (γ' s))
    (hδ : 0 < δ) (hδρ : δ < ρ)
    (hderiv : ∀ t ∈ Set.Ioo (α + δ) (β - δ),
      HasDerivAt (blur b δ γ) (∫ u in (-1 : ℝ)..1, b u • γ' (t - δ * u)) t) :
    ∀ t ∈ Set.Ioo (α + δ) (β - δ), (∫ u in (-1 : ℝ)..1, b u • γ' (t - δ * u)) ≠ 0 := by
  intro t ht
  rw [Set.mem_Ioo] at ht
  have htIcc : t ∈ Set.Icc α β := ⟨by linarith, by linarith⟩
  have hsIcc : ∀ u ∈ Set.Icc (-1 : ℝ) 1, t - δ * u ∈ Set.Icc α β := by
    intro u hu
    constructor
    · nlinarith [ht.1, hu.2, hδ]
    · nlinarith [ht.2, hu.1, hδ]
  have hcont : Continuous (fun u : ℝ => b u * inner ℝ (γ' t) (γ' (t - δ * u))) :=
    hb.mul (continuous_const.inner (hγ'c.comp (by fun_prop)))
  have hcont2 : Continuous (fun u : ℝ => b u * c) := hb.mul continuous_const
  have hle : ∀ u ∈ Set.Icc (-1 : ℝ) 1,
      b u * c ≤ b u * inner ℝ (γ' t) (γ' (t - δ * u)) := by
    intro u hu
    refine mul_le_mul_of_nonneg_left ?_ (hnn u)
    have h1 : |t - δ * u - t| ≤ ρ := by
      have e : t - δ * u - t = -(δ * u) := by ring
      rw [e, abs_neg, abs_mul, abs_of_pos hδ]
      have h3 : |u| ≤ 1 := by rw [abs_le]; exact ⟨hu.1, hu.2⟩
      nlinarith
    exact hwin t htIcc (t - δ * u) (hsIcc u hu) h1
  have hmono : (∫ u in (-1 : ℝ)..1, b u * c)
      ≤ ∫ u in (-1 : ℝ)..1, b u * inner ℝ (γ' t) (γ' (t - δ * u)) :=
    intervalIntegral.integral_mono_on (by norm_num) (hcont2.intervalIntegrable _ _)
      (hcont.intervalIntegrable _ _) hle
  have hconst : (∫ u in (-1 : ℝ)..1, b u * c) = c * ∫ u in (-1 : ℝ)..1, b u := by
    rw [intervalIntegral.integral_mul_const]; ring
  have hpos : 0 < ∫ u in (-1 : ℝ)..1, b u * inner ℝ (γ' t) (γ' (t - δ * u)) := by
    rw [hconst] at hmono
    linarith [mul_pos hc hmass]
  have hpair : inner ℝ (γ' t) (∫ u in (-1 : ℝ)..1, b u • γ' (t - δ * u))
      = ∫ u in (-1 : ℝ)..1, b u * inner ℝ (γ' t) (γ' (t - δ * u)) :=
    inner_intervalIntegral_smul_eq
      ((hb.smul (hγ'c.comp (by fun_prop))).intervalIntegrable _ _)
  intro hzero
  rw [hzero, inner_zero_right] at hpair
  linarith [hpos, hpair]

end Work.Drive
