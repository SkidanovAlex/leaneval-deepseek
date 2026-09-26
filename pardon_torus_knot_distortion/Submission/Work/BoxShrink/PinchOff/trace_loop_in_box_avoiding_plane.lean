import Mathlib
import Submission.Work.BoxShrink.Pinch.LocalForm
import Submission.Work.BoxShrink.Pinch.TraceSpanLeOneSmoothHolds

/-!
# The push-off of a loop of the cutting-plane trace inside the box

`Work.BoxShrink.PinchOff.trace_loop_in_box_avoiding_plane`: a closed curve `γ` of the smooth
torus `F = ψ(F_standard)` whose image lies in the *trace of the cutting plane*
`F ∩ {y (σ 2) = c (σ 2) + u}` and inside the *open box* `PBox s c σ` can be pushed off the plane
without leaving the box: there is a closed curve `γ'` of `F` with the same winding vector whose
image lies in `upperRegion ∪ lowerRegion = F ∩ PBox s c σ ∩ {planeCoord ≠ 0}`.

## The construction

Let `G = planeG ψ c σ u = planeCoord c σ u ∘ par ψ` be the plane coordinate read in the parameter
plane and `W = descentField ψ g` the normalised descent field of `g = planeCoord c σ u`; recall

  `W = -((1 + (∂₁G)² + (∂₂G)²))⁻¹ • (∂₁G, ∂₂G)`,
  `fderiv ℝ G p (W p) = -descentRate ψ g p ≤ 0`,  `descentRate ψ g p = 0 ↔ fderiv ℝ G p = 0`.

`W` is globally Lipschitz, bounded by `1` and `2πℤ²`-periodic
(`Work.Smooth.Morse.Flow.lipschitzWith_descentField`), so the *one-step* map

  `Ψ_ε (q) = q + ε • W q`

is continuous and equivariant under the period lattice: it therefore descends
(`Work.BoxShrink.Bubble.Flow.exists_curve_of_periodicFlow`) to a map carrying closed curves of the
torus to closed curves with the *same* winding vector.

The two landing conditions are the point of the lemma:

* *off the plane.*  `0` is a regular value of `g|_F` — this is exactly `TransverseTrace` — so
  `descentRate` is bounded below by a positive `δ` on the whole trace `{G = 0}`
  (`Work.Smooth.Morse.Flow.exists_descentRate_lower_bound`).  The map
  `(p, q) ↦ fderiv ℝ G p (W q)` is continuous and takes the value `-descentRate ψ g q ≤ -δ` on the
  compact diagonal over `K`, so on a neighbourhood of the diagonal it is `< -δ/2`; hence for `ε`
  small the whole segment `s ↦ q + s • W q`, `s ∈ [0, ε]`, lies in that neighbourhood and the
  level of `G` along it has derivative `≤ -δ/2`, so `G (Ψ_ε q) ≤ G q - (δ/2) ε < 0`.
* *inside the box.*  `K` is a compact subset of the open set `{boxB < s}`, which therefore
  contains a `cthickening` of `K`; since `‖W q‖ ≤ 1`, the point `q + ε • W q` is at distance
  `≤ ε` from `q`.

The compact set `K` is the image under the lift of `γ` of the period interval `[0, 2π]`; the
periodicity of `W` and of the two coordinates extends the conclusion from `K` to the whole real
line.
-/

open LeanEval.KnotTheory.PardonDistortion
open Set

namespace Work.BoxShrink.PinchOff

noncomputable section

/-- The one-step push of a parameter of the torus along the descent field of `g`. -/
def pushMap (ψ : Submission.Diffeo) (g : R3 → ℝ) (ε : ℝ) (q : ℝ × ℝ) : ℝ × ℝ :=
  q + ε • Work.Smooth.Morse.descentField ψ g q

/-- The parametrisation of the torus `Work.Smooth.Morse.torus ψ` is `Work.BoxShrink.Pinch.par ψ`:
the point of the surface attached to a parameter. -/
theorem torus_psi_eq_par (ψ : Submission.Diffeo) (p : ℝ × ℝ) :
    (Work.Smooth.Morse.torus ψ).psi p.1 p.2 = Work.BoxShrink.Pinch.par ψ p := by
  rw [Work.Smooth.Morse.torus_psi, Work.BoxShrink.Pinch.par_def]

/-- **The one-step push-off lemma.**  For a compact `K` in the parameter plane on which the box
norm is `< s` and the plane coordinate vanishes, there is `ε > 0` such that the one-step push
`q ↦ q + ε • W q` carries every `q ∈ K` into `{planeG < 0} ∩ {boxB < s}`. -/
private theorem exists_push_epsilon
    (ψ : Submission.Diffeo) (s : ℝ) (c : R3) (σ : Equiv.Perm (Fin 3)) (u : ℝ)
    (hTT : Work.BoxShrink.Pinch.TransverseTrace ψ c σ u)
    {K : Set (ℝ × ℝ)} (hK : IsCompact K)
    (hbox : ∀ q ∈ K, Work.BoxShrink.Pinch.boxB ψ c σ q < s)
    (hG : ∀ q ∈ K, Work.BoxShrink.Pinch.planeG ψ c σ u q = 0) :
    ∃ ε : ℝ, 0 < ε ∧ ∀ q ∈ K,
      Work.BoxShrink.Pinch.planeG ψ c σ u
          (pushMap ψ (Work.BoxShrink.Bubble.planeCoord c σ u) ε q) < 0 ∧
        Work.BoxShrink.Pinch.boxB ψ c σ
          (pushMap ψ (Work.BoxShrink.Bubble.planeCoord c σ u) ε q) < s := by
  classical
  let g : R3 → ℝ := Work.BoxShrink.Bubble.planeCoord c σ u
  let W : ℝ × ℝ → ℝ × ℝ := Work.Smooth.Morse.descentField ψ g
  let G : ℝ × ℝ → ℝ := Work.Smooth.Morse.pullback ψ g
  have hg2 : ContDiff ℝ 2 g := Work.BoxShrink.Bubble.contDiff_planeCoord c σ u
  have hg1 : ContDiff ℝ 1 g := hg2.of_le (by norm_num)
  have hG1 : ContDiff ℝ 1 G := Work.Smooth.Morse.pullback_contDiff_one ψ hg1
  have hfdcont : Continuous (fderiv ℝ G) := hG1.continuous_fderiv one_ne_zero
  have hWcont : Continuous W := (Work.Smooth.Morse.Flow.contDiff_descentField ψ hg2).continuous
  -- `0` is a regular value of the plane coordinate: this is the transversality hypothesis
  have hreg0 : Work.Smooth.Morse.IsRegularValue ψ g 0 := by
    rw [Work.Smooth.Morse.isRegularValue_iff]
    intro p hp
    exact hTT p hp
  -- a positive lower bound for the descent rate on the whole trace `{G = 0}`
  obtain ⟨δ, hδpos, hδ⟩ :=
    Work.Smooth.Morse.Flow.exists_descentRate_lower_bound ψ hg1 (le_refl (0 : ℝ))
      (fun t ht => by
        have ht0 : t = 0 := by
          have h := Set.mem_Icc.mp ht
          linarith [h.1, h.2]
        rw [ht0]
        exact hreg0)
  -- the open set of pairs where the derivative of `G` along the frozen field is `< -δ/2`
  have hO : IsOpen {x : (ℝ × ℝ) × (ℝ × ℝ) | fderiv ℝ G x.1 (W x.2) < -(δ / 2)} :=
    isOpen_lt ((hfdcont.comp continuous_fst).clm_apply (hWcont.comp continuous_snd))
      continuous_const
  set Kd : Set ((ℝ × ℝ) × (ℝ × ℝ)) := (fun q : ℝ × ℝ => (q, q)) '' K with hKd
  have hKdc : IsCompact Kd := hK.image (continuous_id.prodMk continuous_id)
  have hKdsub : Kd ⊆ {x : (ℝ × ℝ) × (ℝ × ℝ) | fderiv ℝ G x.1 (W x.2) < -(δ / 2)} := by
    rintro x ⟨q, hq, rfl⟩
    have hz : G q = 0 := hG q hq
    have hz' : Work.Smooth.Morse.pullback ψ g q = 0 := hz
    have hlow : δ ≤ Work.Smooth.Morse.descentRate ψ g q :=
      hδ q (by rw [hz']; exact ⟨le_rfl, le_rfl⟩)
    have hval : fderiv ℝ G q (W q) = -Work.Smooth.Morse.descentRate ψ g q :=
      Work.Smooth.Morse.fderiv_pullback_descentField ψ g q
    show fderiv ℝ G q (W q) < -(δ / 2)
    rw [hval]
    linarith
  obtain ⟨ρ, hρpos, hρ⟩ := hKdc.exists_cthickening_subset_open hO hKdsub
  -- the box condition
  have hOb : IsOpen {p : ℝ × ℝ | Work.BoxShrink.Pinch.boxB ψ c σ p < s} :=
    isOpen_lt (Work.BoxShrink.Pinch.boxB_continuous ψ c σ) continuous_const
  obtain ⟨ρb, hρbpos, hρb⟩ := hK.exists_cthickening_subset_open hOb hbox
  -- the bound `‖W q‖ ≤ 1`
  have hWle : ∀ q : ℝ × ℝ, ‖W q‖ ≤ 1 :=
    (Work.Smooth.Morse.Flow.lipschitzWith_descentField ψ hg2).choose_spec.2.1
  refine ⟨min ρ ρb, lt_min hρpos hρbpos, ?_⟩
  intro q hq
  have hερ : min ρ ρb ≤ ρ := min_le_left _ _
  have hερb : min ρ ρb ≤ ρb := min_le_right _ _
  have hεpos : (0 : ℝ) < min ρ ρb := lt_min hρpos hρbpos
  constructor
  · -- the level drops below `0`
    show G (pushMap ψ g (min ρ ρb) q) < 0
    let f : ℝ → ℝ := G ∘ fun t : ℝ => q + t • W q
    have hfderiv : ∀ x : ℝ, HasDerivAt f (fderiv ℝ G (q + x • W q) (W q)) x := by
      intro x
      have hline : HasDerivAt (fun t : ℝ => q + t • W q) (W q) x := by
        have h := ((hasDerivAt_id x).smul_const (W q)).const_add q
        simpa using h
      have hGd : DifferentiableAt ℝ G (q + x • W q) :=
        (hG1.differentiable one_ne_zero).differentiableAt
      exact (hGd.hasFDerivAt).comp_hasDerivAt x hline
    have hderiv : ∀ x ∈ interior (Set.Icc (0 : ℝ) (min ρ ρb)), deriv f x ≤ -(δ / 2) := by
      intro x hx
      have hxI : x ∈ Set.Icc (0 : ℝ) (min ρ ρb) := interior_subset hx
      have hx0 : 0 ≤ x := hxI.1
      have hxε : x ≤ min ρ ρb := hxI.2
      have hmemD : (q + x • W q, q) ∈ Metric.cthickening ρ Kd := by
        refine Metric.mem_cthickening_of_dist_le (q + x • W q, q) (q, q) ρ Kd
          ⟨q, hq, rfl⟩ ?_
        rw [Prod.dist_eq]
        apply max_le
        · rw [dist_eq_norm]
          have hsub : q + x • W q - q = x • W q := by abel
          rw [hsub, norm_smul, Real.norm_eq_abs, abs_of_nonneg hx0]
          calc x * ‖W q‖ ≤ x * 1 := by gcongr; exact hWle q
            _ = x := mul_one x
            _ ≤ min ρ ρb := hxε
            _ ≤ ρ := hερ
        · rw [dist_self]
          exact hρpos.le
      have hopen := hρ hmemD
      rw [(hfderiv x).deriv]
      exact le_of_lt hopen
    have hcont : ContinuousOn f (Set.Icc (0 : ℝ) (min ρ ρb)) := by
      have hc : Continuous f :=
        hG1.continuous.comp (continuous_const.add (continuous_id.smul continuous_const))
      exact hc.continuousOn
    have hdiff : DifferentiableOn ℝ f (interior (Set.Icc (0 : ℝ) (min ρ ρb))) :=
      fun x _ => ((hfderiv x).differentiableAt).differentiableWithinAt
    have hkey := (convex_Icc (0 : ℝ) (min ρ ρb)).image_sub_le_mul_sub_of_deriv_le hcont hdiff
      (C := -(δ / 2)) hderiv 0 ⟨le_rfl, hεpos.le⟩ (min ρ ρb)
      ⟨hεpos.le, le_rfl⟩ hεpos.le
    have hf0 : f 0 = 0 := by
      have hz : G q = 0 := hG q hq
      simp [f, W, hz]
    have hlt : f (min ρ ρb) < 0 := by
      nlinarith [hkey, hf0, hδpos, hεpos]
    simpa [f, pushMap, W] using hlt
  · -- the box condition
    show Work.BoxShrink.Pinch.boxB ψ c σ (pushMap ψ g (min ρ ρb) q) < s
    apply hρb
    refine Metric.mem_cthickening_of_dist_le (pushMap ψ g (min ρ ρb) q) q ρb K hq ?_
    rw [dist_eq_norm]
    have hsub : pushMap ψ g (min ρ ρb) q - q = (min ρ ρb) • W q := by
      simp [pushMap, W]
    rw [hsub, norm_smul, Real.norm_eq_abs, abs_of_nonneg hεpos.le]
    calc min ρ ρb * ‖W q‖ ≤ min ρ ρb * 1 := by gcongr; exact hWle q
      _ = min ρ ρb := mul_one _
      _ ≤ ρb := hερb

theorem trace_loop_in_box_avoiding_plane (ψ : Submission.Diffeo) (s : ℝ)
    (c : LeanEval.KnotTheory.PardonDistortion.R3) (σ : Equiv.Perm (Fin 3)) (u : ℝ)
    (hTT : Work.BoxShrink.Pinch.TransverseTrace ψ c σ u)
    (γ : Work.CoreTopology.ClosedCurve (Work.Smooth.Morse.torus ψ))
    (hin : ∀ t : ℝ, γ t ∈ (Work.Smooth.Morse.torus ψ).carrier ∩
      Work.BoxShrink.Core.cutPlane c σ u)
    (hbox : ∀ t : ℝ, γ t ∈ Submission.PBox s c σ) :
    ∃ γ' : Work.CoreTopology.ClosedCurve (Work.Smooth.Morse.torus ψ),
      (∀ t : ℝ, γ' t ∈ Work.BoxShrink.Core.upperRegion (Work.Smooth.Morse.torus ψ) s c σ u ∪
        Work.BoxShrink.Core.lowerRegion (Work.Smooth.Morse.torus ψ) s c σ u) ∧
      Work.SurgeryInvariance.windingOf (Work.Smooth.Morse.torus ψ) γ' =
        Work.SurgeryInvariance.windingOf (Work.Smooth.Morse.torus ψ) γ := by
  classical
  obtain ⟨L⟩ := Work.TorusCover.ParamTorus_exists_liftOf (Work.Smooth.Morse.torus ψ) γ
  let Lp : ℝ → ℝ × ℝ := fun t => (L.Θ t, L.Φ t)
  have hLpc : Continuous Lp := L.contΘ.prodMk L.contΦ
  let K : Set (ℝ × ℝ) := Lp '' Set.Icc (0 : ℝ) (2 * Real.pi)
  have hK : IsCompact K := isCompact_Icc.image hLpc
  have hlift : ∀ t : ℝ, Work.BoxShrink.Pinch.par ψ (Lp t) = γ t := by
    intro t
    show (Work.Smooth.Morse.torus ψ).psi (L.Θ t) (L.Φ t) = γ.γ t
    exact L.lifts t
  have hboxK : ∀ q ∈ K, Work.BoxShrink.Pinch.boxB ψ c σ q < s := by
    rintro q ⟨t, -, rfl⟩
    have h1 : Lp t ∈ Work.BoxShrink.Pinch.par ψ ⁻¹' Submission.PBox s c σ := by
      rw [Set.mem_preimage, hlift t]
      exact hbox t
    rwa [Work.BoxShrink.Pinch.preimage_PBox] at h1
  have hGK : ∀ q ∈ K, Work.BoxShrink.Pinch.planeG ψ c σ u q = 0 := by
    rintro q ⟨t, -, rfl⟩
    have hcut : γ t ∈ Work.BoxShrink.Core.cutPlane c σ u := (hin t).2
    rw [Work.BoxShrink.Pinch.planeG_apply, hlift t]
    rw [Work.BoxShrink.Bubble.planeCoord_apply]
    rw [Work.BoxShrink.Core.mem_cutPlane] at hcut
    rw [hcut, sub_self]
  obtain ⟨ε, hεpos, hε⟩ := exists_push_epsilon ψ s c σ u hTT hK hboxK hGK
  have hWcont : Continuous
      (Work.Smooth.Morse.descentField ψ (Work.BoxShrink.Bubble.planeCoord c σ u)) :=
    (Work.Smooth.Morse.Flow.contDiff_descentField ψ
      (Work.BoxShrink.Bubble.contDiff_planeCoord c σ u)).continuous
  obtain ⟨Kl, hKlip, hWle, hWper⟩ :=
    Work.Smooth.Morse.Flow.lipschitzWith_descentField ψ
      (Work.BoxShrink.Bubble.contDiff_planeCoord c σ u)
  obtain ⟨γ', hγ'apply, hγ'wind⟩ :=
    Work.BoxShrink.Bubble.Flow.exists_curve_of_periodicFlow (Work.Smooth.Morse.torus ψ)
      (fun r q => q + (r * ε) •
        Work.Smooth.Morse.descentField ψ (Work.BoxShrink.Bubble.planeCoord c σ u) q)
      (by
        have h1 : Continuous (fun p : ℝ × (ℝ × ℝ) =>
            (p.1 * ε) • Work.Smooth.Morse.descentField ψ
              (Work.BoxShrink.Bubble.planeCoord c σ u) p.2) :=
          (continuous_fst.mul continuous_const).smul (hWcont.comp continuous_snd)
        have h2 : Continuous (fun p : ℝ × (ℝ × ℝ) => p.2) := continuous_snd
        have h3 : Continuous (fun p : ℝ × (ℝ × ℝ) =>
            p.2 + (p.1 * ε) • Work.Smooth.Morse.descentField ψ
              (Work.BoxShrink.Bubble.planeCoord c σ u) p.2) := h2.add h1
        exact h3)
      (by
        intro r q k l
        have hp := hWper q k l
        show (q.1 + ↑k * (2 * Real.pi), q.2 + ↑l * (2 * Real.pi)) + (r * ε) •
            Work.Smooth.Morse.descentField ψ (Work.BoxShrink.Bubble.planeCoord c σ u)
              (q.1 + ↑k * (2 * Real.pi), q.2 + ↑l * (2 * Real.pi)) =
          ((q + (r * ε) • Work.Smooth.Morse.descentField ψ
              (Work.BoxShrink.Bubble.planeCoord c σ u) q).1 + ↑k * (2 * Real.pi),
            (q + (r * ε) • Work.Smooth.Morse.descentField ψ
              (Work.BoxShrink.Bubble.planeCoord c σ u) q).2 + ↑l * (2 * Real.pi))
        rw [hp]
        ext <;> simp <;> ring)
      L
  refine ⟨γ', ?_, ?_⟩
  · -- reduce to the period interval using the periodicity of `γ'`
    intro t
    have hper : Function.Periodic γ'.γ (2 * Real.pi) := γ'.periodic
    set k : ℤ := ⌊t / (2 * Real.pi)⌋ with hk
    set t' : ℝ := t - (k : ℝ) * (2 * Real.pi) with ht'
    have hπ : (0 : ℝ) < 2 * Real.pi := by positivity
    have ht'mem : t' ∈ Set.Icc (0 : ℝ) (2 * Real.pi) := by
      constructor
      · have h := Int.floor_le (t / (2 * Real.pi))
        rw [← hk] at h
        have h2 : (k : ℝ) * (2 * Real.pi) ≤ (t / (2 * Real.pi)) * (2 * Real.pi) :=
          mul_le_mul_of_nonneg_right h hπ.le
        rw [div_mul_cancel₀ _ (ne_of_gt hπ)] at h2
        simp only [ht']
        linarith
      · have h := Int.lt_floor_add_one (t / (2 * Real.pi))
        rw [← hk] at h
        have h3 : (t / (2 * Real.pi)) * (2 * Real.pi) < ((k : ℝ) + 1) * (2 * Real.pi) :=
          mul_lt_mul_of_pos_right h hπ
        rw [div_mul_cancel₀ _ (ne_of_gt hπ)] at h3
        simp only [ht']
        linarith
    have ht_eq : t = t' + (k : ℝ) * (2 * Real.pi) := by
      simp only [ht']
      ring
    rw [ht_eq, (hper.int_mul k) t']
    have hq : Lp t' ∈ K := ⟨t', ht'mem, rfl⟩
    rw [hγ'apply t']
    simp only [one_mul]
    have hmem : Work.BoxShrink.Pinch.par ψ
        ((L.Θ t', L.Φ t') + ε • Work.Smooth.Morse.descentField ψ
            (Work.BoxShrink.Bubble.planeCoord c σ u) (L.Θ t', L.Φ t')) ∈
        Work.BoxShrink.Core.upperRegion (Work.Smooth.Morse.torus ψ) s c σ u ∪
          Work.BoxShrink.Core.lowerRegion (Work.Smooth.Morse.torus ψ) s c σ u := by
      have hε' := hε (Lp t') hq
      have heq : pushMap ψ (Work.BoxShrink.Bubble.planeCoord c σ u) ε (Lp t') =
          ((L.Θ t', L.Φ t') + ε • Work.Smooth.Morse.descentField ψ
            (Work.BoxShrink.Bubble.planeCoord c σ u) (L.Θ t', L.Φ t')) := by
        simp [pushMap, Lp]
      rw [heq] at hε'
      rw [← Set.mem_preimage, Work.BoxShrink.Pinch.preimage_union_halfRegions]
      exact ⟨hε'.2, ne_of_lt hε'.1⟩
    rw [torus_psi_eq_par ψ ((L.Θ t', L.Φ t') + ε • Work.Smooth.Morse.descentField ψ
            (Work.BoxShrink.Bubble.planeCoord c σ u) (L.Θ t', L.Φ t'))]
    exact hmem
  · rw [hγ'wind, ← Work.SurgeryInvariance.windingOf_eq (Work.Smooth.Morse.torus ψ) γ L]

end

end Work.BoxShrink.PinchOff
