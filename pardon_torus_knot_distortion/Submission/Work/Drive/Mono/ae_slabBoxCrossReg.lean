import Mathlib
import Submission.Work.Drive.Mono.BoxGenE
import Submission.Work.Smooth.BoxGeneric.Sard.exists_isOpen_volume_image_restrictedCritical_null

namespace Work.Drive.Mono

open LeanEval.KnotTheory.PardonDistortion
open MeasureTheory Set
open scoped ENNReal

noncomputable section

/-!
## Auxiliary material for `ae_slabBoxCrossReg`

The proof of `Work.Drive.Mono.ae_slabBoxCrossReg` rests on two facts which the modules that
establish them keep `private` (they appear inside the proof of the two-dimensional Sard theorem
`Work.Smooth.BoxGeneric.Sard.criticalValues_null_of_contDiffTwo_periodic_pair`), so we repeat their
short proofs here:

* `volume_restrictedCriticalValues_eq_zero` — Sard's theorem in dimension one **at a fixed level**:
  for `C¹` functions `G H : ℝ × ℝ → ℝ` and any `u : ℝ`, the set of values of `G` taken at
  critical points of its restriction to the level set `{H = u}` (a point of that level set where
  `fderiv H ≠ 0` and `fderiv G` is proportional to `fderiv H`) is Lebesgue-null.  This is the
  form of Sard's theorem that applies at a *prescribed* first coordinate, which is what the
  face regularity `hreg` provides.
* `exists_smul_snd_of_not_isInvertible` — the linear algebra of a non-invertible endomorphism of
  `ℝ × ℝ` whose first row does not vanish: its second row is a multiple of the first.
-/

/-! ### Elementary linear algebra on `ℝ × ℝ` -/

/-- An endomorphism of `ℝ × ℝ` that is injective is invertible (the space is finite dimensional,
and every linear map on it is continuous). -/
private lemma isInvertible_of_injective {T : (ℝ × ℝ) →L[ℝ] (ℝ × ℝ)}
    (h : Function.Injective T) : T.IsInvertible := by
  let e : (ℝ × ℝ) ≃ₗ[ℝ] (ℝ × ℝ) := LinearEquiv.ofInjectiveEndo T.toLinearMap h
  have he : ⇑e = T := LinearEquiv.coe_ofInjectiveEndo T.toLinearMap h
  refine ⟨e.toContinuousLinearEquiv, ContinuousLinearMap.ext ?_⟩
  intro x
  simpa [he] using congrFun he x

/-- An endomorphism of `ℝ × ℝ` that is surjective is invertible. -/
private lemma isInvertible_of_surjective {T : (ℝ × ℝ) →L[ℝ] (ℝ × ℝ)}
    (h : Function.Surjective T) : T.IsInvertible :=
  isInvertible_of_injective (LinearMap.injective_iff_surjective.mpr h)

/-- At a point where the differential `T` of a map is not invertible and whose **first row**
`fst ∘ T` does not vanish, the second row is a multiple of the first. -/
private lemma exists_smul_snd_of_not_isInvertible {T : (ℝ × ℝ) →L[ℝ] (ℝ × ℝ)}
    (hT : ¬ T.IsInvertible) (h1 : ContinuousLinearMap.fst ℝ ℝ ℝ ∘L T ≠ 0) :
    ∃ a : ℝ, ContinuousLinearMap.snd ℝ ℝ ℝ ∘L T = a • (ContinuousLinearMap.fst ℝ ℝ ℝ ∘L T) := by
  have hsurj : ¬ Function.Surjective T := fun hs => hT (isInvertible_of_surjective hs)
  have hrange : LinearMap.range T.toLinearMap < ⊤ := by
    rw [lt_top_iff_ne_top]
    intro htop
    apply hsurj
    intro y
    have : y ∈ LinearMap.range T.toLinearMap := by rw [htop]; trivial
    obtain ⟨x, hx⟩ := this
    exact ⟨x, hx⟩
  obtain ⟨L, hLne, hL⟩ :=
    Submodule.exists_le_ker_of_lt_top (LinearMap.range T.toLinearMap) hrange
  set α : ℝ := L ((1 : ℝ), 0) with hα
  set β : ℝ := L ((0 : ℝ), 1) with hβ
  have hLapply : ∀ v : ℝ × ℝ, L v = α * v.1 + β * v.2 := by
    rintro ⟨x, y⟩
    have hxy : ((x, y) : ℝ × ℝ) = x • ((1 : ℝ), 0) + y • ((0 : ℝ), 1) := by ext <;> simp
    calc L (x, y) = L (x • ((1 : ℝ), 0) + y • ((0 : ℝ), 1)) := by rw [hxy]
      _ = α * x + β * y := by rw [map_add, map_smul, map_smul, hα, hβ]; ring
  have hzero : ∀ v : ℝ × ℝ, L (T v) = 0 := fun v => hL (LinearMap.mem_range.mpr ⟨v, rfl⟩)
  have hcomb : ∀ v : ℝ × ℝ, α * ((ContinuousLinearMap.fst ℝ ℝ ℝ ∘L T) v)
      + β * ((ContinuousLinearMap.snd ℝ ℝ ℝ ∘L T) v) = 0 := by
    intro v
    have h := hzero v
    rw [hLapply (T v)] at h
    simpa only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.coe_fst',
      ContinuousLinearMap.coe_snd'] using h
  by_cases hβ0 : β = 0
  · exfalso
    have hα0 : α ≠ 0 := by
      intro hαz
      apply hLne
      refine LinearMap.ext (fun v => ?_)
      rw [hLapply v, hαz, hβ0]
      simp
    have hfst0 : ContinuousLinearMap.fst ℝ ℝ ℝ ∘L T = 0 := by
      refine ContinuousLinearMap.ext (fun v => ?_)
      have h := hcomb v
      rw [hβ0] at h
      simp only [zero_mul, add_zero] at h
      simpa using (mul_eq_zero.mp h).resolve_left hα0
    exact h1 hfst0
  · refine ⟨-(α / β), ?_⟩
    refine ContinuousLinearMap.ext (fun v => ?_)
    have h := hcomb v
    have hβne : β ≠ 0 := hβ0
    have key : ((ContinuousLinearMap.snd ℝ ℝ ℝ ∘L T) v)
        = -(α * ((ContinuousLinearMap.fst ℝ ℝ ℝ ∘L T) v)) / β := by
      rw [eq_div_iff hβne]
      linarith
    rw [key, ContinuousLinearMap.smul_apply, smul_eq_mul]
    ring

/-! ### Sard at a fixed level -/

/-- **Sard in dimension one at a prescribed level.**  For `C¹` maps `G H : ℝ × ℝ → ℝ` and a
level `u`, the set of values of `G` at points of the level set `{H = u}` where `H` has non-vanishing
derivative and the differentials of `G` and `H` are proportional is Lebesgue-null.  These are
exactly the critical values of the restriction of `G` to that level curve, and the point of the
statement is that it holds at the *specific* level `u`. -/
private lemma volume_restrictedCriticalValues_eq_zero {G H : ℝ × ℝ → ℝ}
    (hG : ContDiff ℝ 1 G) (hH : ContDiff ℝ 1 H) (u : ℝ) :
    volume {v : ℝ | ∃ q : ℝ × ℝ, G q = v ∧ H q = u ∧ fderiv ℝ H q ≠ 0 ∧
      ∃ a : ℝ, fderiv ℝ G q = a • fderiv ℝ H q} = 0 := by
  classical
  set A : Set (ℝ × ℝ) := {q : ℝ × ℝ | H q = u ∧ fderiv ℝ H q ≠ 0 ∧
    ∃ a : ℝ, fderiv ℝ G q = a • fderiv ℝ H q} with hA
  have hmemA : ∀ q, q ∈ A ↔ H q = u ∧ fderiv ℝ H q ≠ 0 ∧
      ∃ a : ℝ, fderiv ℝ G q = a • fderiv ℝ H q := fun q => by simp [hA]
  have hderiv : ∀ q : ℝ × ℝ, fderiv ℝ (fun p : ℝ × ℝ => H p - u) q = fderiv ℝ H q := by
    intro q
    have h1 : (fun p : ℝ × ℝ => H p - u) = H - (Function.const (ℝ × ℝ) u) := rfl
    rw [h1, fderiv_sub, fderiv_const]
    · simp
    · exact (hH.differentiable (by norm_num : (1 : WithTop ℕ∞) ≠ 0)).differentiableAt
    · exact differentiableAt_const u
  have hset : {v : ℝ | ∃ q : ℝ × ℝ, G q = v ∧ H q = u ∧ fderiv ℝ H q ≠ 0 ∧
      ∃ a : ℝ, fderiv ℝ G q = a • fderiv ℝ H q} = G '' A := by
    ext v; constructor
    · rintro ⟨q, h1, h2, h3, h4⟩; exact ⟨q, (hmemA q).mpr ⟨h2, h3, h4⟩, h1⟩
    · rintro ⟨q, hq, h1⟩; exact ⟨q, h1, (hmemA q).mp hq⟩
  rw [hset]
  have hpt : ∀ p ∈ A, ∃ U : Set (ℝ × ℝ), IsOpen U ∧ p ∈ U ∧
      volume (G '' ({q : ℝ × ℝ | (fun p : ℝ × ℝ => H p - u) q = 0 ∧
        ∃ a : ℝ, fderiv ℝ G q = a • fderiv ℝ (fun p : ℝ × ℝ => H p - u) q} ∩ U)) = 0 := by
    intro p hp
    have hcd : ContDiff ℝ 1 (fun p : ℝ × ℝ => H p - u) := hH.sub contDiff_const
    have hp0 : (fun p : ℝ × ℝ => H p - u) p = 0 := by
      simp [((hmemA p).mp hp).1]
    have hg : fderiv ℝ (fun p : ℝ × ℝ => H p - u) p ≠ 0 := by
      rw [hderiv p]; exact ((hmemA p).mp hp).2.1
    exact Work.Smooth.BoxGeneric.Sard.exists_isOpen_volume_image_restrictedCritical_null hG hcd hp0 hg
  let U : ℝ × ℝ → Set (ℝ × ℝ) := fun p => if h : p ∈ A then (hpt p h).choose else ∅
  have hU : ∀ p : ℝ × ℝ, ∀ hp : p ∈ A, IsOpen (U p) ∧ p ∈ U p ∧
      volume (G '' ({q : ℝ × ℝ | (fun p : ℝ × ℝ => H p - u) q = 0 ∧
        ∃ a : ℝ, fderiv ℝ G q = a • fderiv ℝ (fun p : ℝ × ℝ => H p - u) q} ∩ U p)) = 0 := by
    intro p hp
    simp only [U, dif_pos hp]
    exact (hpt p hp).choose_spec
  have hnhd : ∀ p ∈ A, U p ∈ nhds p := fun p hp => (hU p hp).1.mem_nhds (hU p hp).2.1
  obtain ⟨t, htc, htsub, hcover⟩ :=
    (HereditarilyLindelofSpace.isLindelof A).elim_nhds_subcover U hnhd
  have hsub : G '' A ⊆ ⋃ p ∈ t, G '' ({q : ℝ × ℝ | (fun p : ℝ × ℝ => H p - u) q = 0 ∧
      ∃ a : ℝ, fderiv ℝ G q = a • fderiv ℝ (fun p : ℝ × ℝ => H p - u) q} ∩ U p) := by
    rintro v ⟨q, hqA, rfl⟩
    have hq' : q ∈ ⋃ p ∈ t, U p := hcover hqA
    obtain ⟨x, hx⟩ := Set.mem_iUnion.mp hq'
    obtain ⟨hxt, hxq⟩ := Set.mem_iUnion.mp hx
    refine Set.mem_biUnion hxt ⟨q, ⟨⟨?_, ?_⟩, hxq⟩, rfl⟩
    · show H q - u = 0
      rw [((hmemA q).mp hqA).1]
      simp
    · obtain ⟨a, ha⟩ := ((hmemA q).mp hqA).2.2
      exact ⟨a, by rw [hderiv q]; exact ha⟩
  refine le_antisymm (le_trans (MeasureTheory.measure_mono hsub) (le_of_eq ?_)) bot_le
  rw [MeasureTheory.measure_biUnion_null_iff htc]
  intro x hx
  exact (hU x (htsub x hx)).2.2

/-! ## The bad values of the `v`-height on a box face -/

/-- **The restricted-critical `v`-values of a box face.**  The set of values `w` of the `v`-height
`q ↦ ⟪v, par ψ q⟫` at parameter points `q` of the face
`{q | (par ψ q) (σ i) = c (σ i) + ε * boxSide i * s}` which are *critical* for the restriction of
that height to the face: `q` lies on the face, the face level is regular there
(`fderiv (y_{σ i} ∘ par) q ≠ 0`) and the two differentials are proportional. -/
def SlabFaceCritVals (ψ : Submission.Diffeo) (c : R3) (σ : Equiv.Perm (Fin 3)) (s : ℝ)
    (v : R3) (i : Fin 3) (ε : ℝ) : Set ℝ :=
  {w : ℝ | ∃ q : ℝ × ℝ,
    inner ℝ v (Work.BoxShrink.Pinch.par ψ q) = w ∧
    (Work.BoxShrink.Pinch.par ψ q) (σ i) = c (σ i) + ε * Submission.boxSide i * s ∧
    fderiv ℝ (fun q : ℝ × ℝ => (Work.BoxShrink.Pinch.par ψ q) (σ i)) q ≠ 0 ∧
    ∃ b : ℝ, fderiv ℝ (fun q : ℝ × ℝ => inner ℝ v (Work.BoxShrink.Pinch.par ψ q)) q
      = b • fderiv ℝ (fun q : ℝ × ℝ => (Work.BoxShrink.Pinch.par ψ q) (σ i)) q}

/-- The face coordinate `q ↦ (par ψ q) (σ i)` is `C¹`. -/
private lemma contDiff_faceCoord (ψ : Submission.Diffeo) (i : Fin 3) :
    ContDiff ℝ 1 (fun q : ℝ × ℝ => (Work.BoxShrink.Pinch.par ψ q) i) := by
  have h : (fun q : ℝ × ℝ => (Work.BoxShrink.Pinch.par ψ q) i)
      = Work.Smooth.Morse.pullback ψ (fun y : R3 => y i) := by funext q; rfl
  rw [h]
  exact Work.Smooth.Morse.pullback_contDiff_one ψ
    ((PiLp.proj 2 (fun _ : Fin 3 => ℝ) i : R3 →L[ℝ] ℝ).contDiff)

/-- The tilted height `q ↦ ⟪v, par ψ q⟫` is `C¹`. -/
private lemma contDiff_heightV_one (ψ : Submission.Diffeo) (v : R3) :
    ContDiff ℝ 1 (fun q : ℝ × ℝ => inner ℝ v (Work.BoxShrink.Pinch.par ψ q)) := by
  have h : (fun q : ℝ × ℝ => inner ℝ v (Work.BoxShrink.Pinch.par ψ q))
      = Work.Smooth.Morse.pullback ψ (fun y : R3 => inner ℝ v y) := by funext q; rfl
  rw [h]
  exact Work.Smooth.Morse.pullback_contDiff_one ψ ((innerSL ℝ v).contDiff)

/-- **The restricted-critical values of a box face are null.** -/
theorem volume_slabFaceCritVals_eq_zero (ψ : Submission.Diffeo) (c : R3)
    (σ : Equiv.Perm (Fin 3)) (s : ℝ) (v : R3) (i : Fin 3) (ε : ℝ) :
    volume (SlabFaceCritVals ψ c σ s v i ε) = 0 :=
  volume_restrictedCriticalValues_eq_zero (contDiff_heightV_one ψ v) (contDiff_faceCoord ψ (σ i))
    (c (σ i) + ε * Submission.boxSide i * s)

/-- **Almost every half-width avoids the restricted-critical values of a box face.**  The pinned
second coordinate `a + η h` is affine in `h` with slope `η = ±1`, hence for almost every `h` it
misses the null set `SlabFaceCritVals ψ c σ s v i ε`. -/
theorem ae_avoid_slabFaceCritVals (ψ : Submission.Diffeo) (c : R3) (σ : Equiv.Perm (Fin 3))
    (s : ℝ) (v : R3) (i : Fin 3) (ε a : ℝ) :
    ∀ᵐ h ∂(MeasureTheory.volume : MeasureTheory.Measure ℝ),
      ∀ η : ℝ, (η = 1 ∨ η = -1) → a + η * h ∉ SlabFaceCritVals ψ c σ s v i ε := by
  have hC : volume (SlabFaceCritVals ψ c σ s v i ε) = 0 :=
    volume_slabFaceCritVals_eq_zero ψ c σ s v i ε
  have h1 : ∀ᵐ h ∂(volume : MeasureTheory.Measure ℝ),
      a + h ∉ SlabFaceCritVals ψ c σ s v i ε := by
    rw [MeasureTheory.ae_iff]
    have hset : {h : ℝ | ¬ (a + h ∉ SlabFaceCritVals ψ c σ s v i ε)}
        = (fun h : ℝ => a + h) ⁻¹' SlabFaceCritVals ψ c σ s v i ε := by ext h; simp
    rw [hset, MeasureTheory.measure_preimage_add]
    exact hC
  have h2 : ∀ᵐ h ∂(volume : MeasureTheory.Measure ℝ),
      a - h ∉ SlabFaceCritVals ψ c σ s v i ε := by
    rw [MeasureTheory.ae_iff]
    have hset : {h : ℝ | ¬ (a - h ∉ SlabFaceCritVals ψ c σ s v i ε)}
        = (fun h : ℝ => a - h) ⁻¹' SlabFaceCritVals ψ c σ s v i ε := by ext h; simp
    rw [hset]
    have hmap := MeasureTheory.Measure.map_sub_left_eq_self
      (MeasureTheory.volume : MeasureTheory.Measure ℝ) a
    have hle := MeasureTheory.Measure.le_map_apply
      (μ := (MeasureTheory.volume : MeasureTheory.Measure ℝ))
      (f := fun u : ℝ => a - u) (measurable_const.sub measurable_id).aemeasurable
      (SlabFaceCritVals ψ c σ s v i ε)
    rw [hmap, hC] at hle
    exact le_antisymm hle bot_le
  filter_upwards [h1, h2] with h hh1 hh2 η hη
  rcases hη with hη | hη
  · rw [hη]; simpa using hh1
  · rw [hη]; simpa only [neg_one_mul, sub_eq_add_neg] using hh2

/-! ## The main statement -/

/-- **Triple-point transversality at almost every half-width, given the face regularity**
(project lead, message of 2026-09-26 08:5x;
`Submission/Work/Drive/Final/NOTES_tripleGatesCorrected_REFUTED.md`).

`Work.Drive.Mono.SlabBoxCrossReg ψ c σ s v a h` says that at every triple point — a point of the
surface on a box *face* `{y (σ i) = c (σ i) + ε boxSide i * s}` and on a slab face
`{⟪v,·⟫ = a + η h}` — the two face curves on the surface meet transversally, i.e. the pair
`Φᵢ = ((y (σ i)) ∘ par, ⟪v,·⟫ ∘ par)` has invertible derivative at every point of its fibre over the
pinned point `(c (σ i) + ε boxSide i * s, a + η h)`.  It is the missing hypothesis of
`Work.Drive.Final.tripleGatesCorrected`.

The hypothesis `hreg` is **necessary and is exactly `BoxGen`'s face regularity** (clause (i) of
`Work.Drive.Mono.BoxGen`, proved a.e. in `s` by the workspace's `ae_face_regular_of_sardCoord`): the
box-face value `c (σ i) + ε boxSide i * s` must be a *regular value* of `(y (σ i)) ∘ par`.  Without
it the statement is false (the frozen first coordinate can be a critical value — e.g. the top circle
of the standard torus — and then a whole segment of `h` is bad).  With it, the fibre is a compact
one-manifold, the restriction of `⟪v,·⟫ ∘ par` to it is a `C^∞` function whose critical values are
null (one-dimensional Sard), and the pinned second coordinate `⟪v,c⟫ + u + η h` is affine in `h` with
slope `η ≠ 0`, so for a.e. `h` it avoids them; the finite intersection over `i ≠ 2`, `ε = ±1`,
`η = ±1` finishes.

Equivalently, `(fderiv Φᵢ p).IsInvertible` holds at a fibre point `p` exactly when the derivative of
`⟪v,·⟫ ∘ par` restricted to the fibre of `(y (σ i)) ∘ par` is non-zero at `p`.

The producer gets `hreg` from its `BoxGen` hypothesis and chooses `h` in a conull subset of its
half-width interval, so this costs nothing there. -/
theorem ae_slabBoxCrossReg (ψ : Submission.Diffeo) (c : R3) (σ : Equiv.Perm (Fin 3)) (s u : ℝ)
    (v : R3)
    (hreg : ∀ i : Fin 3, i ≠ 2 → ∀ ε : ℝ, (ε = 1 ∨ ε = -1) → ∀ p : ℝ × ℝ,
      (Work.BoxShrink.Pinch.par ψ p) (σ i) = c (σ i) + ε * Submission.boxSide i * s →
      fderiv ℝ (fun q : ℝ × ℝ => (Work.BoxShrink.Pinch.par ψ q) (σ i)) p ≠ 0) :
    ∀ᵐ h ∂(MeasureTheory.volume : MeasureTheory.Measure ℝ),
      Work.Drive.Mono.SlabBoxCrossReg ψ c σ s v (inner ℝ v c + u) h := by
  classical
  -- Every face `i ≠ 2` and sign `ε = ±1` contributes a null set of bad half-widths.
  have key : ∀ᵐ h ∂(MeasureTheory.volume : MeasureTheory.Measure ℝ),
      ∀ i : {i : Fin 3 // i ≠ 2}, ∀ ε : ℝ, (ε = 1 ∨ ε = -1) → ∀ η : ℝ, (η = 1 ∨ η = -1) →
        (inner ℝ v c + u) + η * h ∉ SlabFaceCritVals ψ c σ s v i.1 ε := by
    refine MeasureTheory.ae_all_iff.mpr (fun i => ?_)
    have h1 := ae_avoid_slabFaceCritVals ψ c σ s v i.1 1 (inner ℝ v c + u)
    have h2 := ae_avoid_slabFaceCritVals ψ c σ s v i.1 (-1) (inner ℝ v c + u)
    filter_upwards [h1, h2] with h hh1 hh2 ε hε
    rcases hε with hε | hε
    · subst hε; exact hh1
    · subst hε; exact hh2
  filter_upwards [key] with h hgood
  dsimp only [SlabBoxCrossReg]
  intro i hi ε hε η hη p hH hF
  -- Suppose the pair derivative is *not* invertible at such a triple point `p`.
  by_contra hnot
  have hd1 : DifferentiableAt ℝ (fun q : ℝ × ℝ => (Work.BoxShrink.Pinch.par ψ q) (σ i)) p :=
    ((contDiff_faceCoord ψ (σ i)).differentiable (by norm_num)).differentiableAt
  have hd2 : DifferentiableAt ℝ (fun q : ℝ × ℝ => inner ℝ v (Work.BoxShrink.Pinch.par ψ q)) p :=
    ((contDiff_heightV_one ψ v).differentiable (by norm_num)).differentiableAt
  have hfd : fderiv ℝ (fun q : ℝ × ℝ => ((Work.BoxShrink.Pinch.par ψ q) (σ i),
        inner ℝ v (Work.BoxShrink.Pinch.par ψ q))) p
      = (fderiv ℝ (fun q : ℝ × ℝ => (Work.BoxShrink.Pinch.par ψ q) (σ i)) p).prod
        (fderiv ℝ (fun q : ℝ × ℝ => inner ℝ v (Work.BoxShrink.Pinch.par ψ q)) p) :=
    DifferentiableAt.fderiv_prodMk hd1 hd2
  rw [hfd] at hnot
  -- The face regularity makes the first row non-zero, so the second row is a multiple of it.
  have hfst : ContinuousLinearMap.fst ℝ ℝ ℝ ∘L
      ((fderiv ℝ (fun q : ℝ × ℝ => (Work.BoxShrink.Pinch.par ψ q) (σ i)) p).prod
        (fderiv ℝ (fun q : ℝ × ℝ => inner ℝ v (Work.BoxShrink.Pinch.par ψ q)) p)) ≠ 0 := by
    rw [ContinuousLinearMap.fst_comp_prod]
    exact hreg i hi ε hε p hH
  obtain ⟨b, hb⟩ := exists_smul_snd_of_not_isInvertible hnot hfst
  have hb' : fderiv ℝ (fun q : ℝ × ℝ => inner ℝ v (Work.BoxShrink.Pinch.par ψ q)) p
      = b • fderiv ℝ (fun q : ℝ × ℝ => (Work.BoxShrink.Pinch.par ψ q) (σ i)) p := by
    rw [ContinuousLinearMap.snd_comp_prod, ContinuousLinearMap.fst_comp_prod] at hb
    exact hb
  -- Hence the pinned second coordinate is a restricted-critical value.
  have hmem : inner ℝ v (Work.BoxShrink.Pinch.par ψ p) ∈ SlabFaceCritVals ψ c σ s v i ε :=
    ⟨p, rfl, hH, hreg i hi ε hε p hH, ⟨b, hb'⟩⟩
  exact hgood ⟨i, hi⟩ ε hε η hη (hF ▸ hmem)

end

end Work.Drive.Mono
