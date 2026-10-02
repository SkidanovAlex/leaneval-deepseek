import Mathlib
import Submission.Work.RatHurewicz.CompressionDefs

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

/-!
# The contraction of the pinched part `J ⊆ ∂I^{e+1}` to the centre of the bottom face

`Work.RatHurewicz.exists_pinchContraction`: the set
`PinchSet e` (the bottom face `{x (Fin.last e) = 0}` together with the side faces
`{x (Fin.castSucc i) = 0 ∨ x (Fin.castSucc i) = 1}` of `I^{e+1}`) is contracted to the centre
`pinchBase e` of the bottom face, *inside the boundary* `∂I^{e+1}`.

The contraction has two phases.  Writing `z = Fin.snoc u s`:

* `t ≤ 1/2`: `Fin.snoc u ((1 - 2t)·s)`: the side faces are pushed down onto the bottom face (the
  `u`-part is kept, and a point of `PinchSet e` with `s > 0` has a coordinate of `u` in `{0,1}`);
* `t ≥ 1/2`: `Fin.snoc ((1 - λ)·u + λ·(1/2,…)) 0` with `λ = 2t - 1`, a convex combination in the
  bottom face `{s = 0} ⊆ ∂I^{e+1}`, which is the contraction of the bottom face to its centre.

The two branches agree at `t = 1/2`, so the map glues continuously.
-/

set_option linter.unusedVariables false
set_option maxHeartbeats 1000000

open scoped Topology unitInterval

namespace Work.RatHurewicz

noncomputable section

variable {e : ℕ}

/-- The product of a real number, clamped to `[0,1]`, with an element of `I`. -/
def unitScale (c : ℝ) (s : unitInterval) : unitInterval :=
  ⟨max 0 (min 1 c) * (s : ℝ), by
    have hc0 : (0 : ℝ) ≤ max 0 (min 1 c) := le_max_left _ _
    have hc1 : max 0 (min 1 c) ≤ 1 := max_le (by norm_num) (min_le_left _ _)
    exact ⟨mul_nonneg hc0 s.2.1, by nlinarith [hc0, hc1, s.2.1, s.2.2]⟩⟩

theorem unitScale_coe (c : ℝ) (s : unitInterval) :
    ((unitScale c s : unitInterval) : ℝ) = max 0 (min 1 c) * (s : ℝ) := rfl

theorem unitScale_of_mem {c : ℝ} (h0 : 0 ≤ c) (h1 : c ≤ 1) (s : unitInterval) :
    (unitScale c s : ℝ) = c * (s : ℝ) := by
  rw [unitScale_coe, min_eq_right h1, max_eq_right h0]

theorem continuous_unitScale : Continuous fun p : ℝ × unitInterval => unitScale p.1 p.2 := by
  refine Continuous.subtype_mk ?_ _
  exact (continuous_const.max (continuous_const.min continuous_fst)).mul
    (continuous_subtype_val.comp continuous_snd)

/-- The convex combination `c • s + (1 - c) • t` of two points of `I`, with `c` clamped to
`[0,1]`. -/
def convI (c : ℝ) (s t : unitInterval) : unitInterval :=
  ⟨max 0 (min 1 c) * (s : ℝ) + (1 - max 0 (min 1 c)) * (t : ℝ), by
    have hc0 : (0 : ℝ) ≤ max 0 (min 1 c) := le_max_left _ _
    have hc1 : max 0 (min 1 c) ≤ 1 := max_le (by norm_num) (min_le_left _ _)
    have hs0 : (0:ℝ) ≤ (s:ℝ) := s.2.1
    have hs1 : (s:ℝ) ≤ 1 := s.2.2
    have ht0 : (0:ℝ) ≤ (t:ℝ) := t.2.1
    have ht1 : (t:ℝ) ≤ 1 := t.2.2
    have h1 : max 0 (min 1 c) * (s:ℝ) ≤ max 0 (min 1 c) * 1 :=
      mul_le_mul_of_nonneg_left hs1 hc0
    have h2 : (1 - max 0 (min 1 c)) * (t:ℝ) ≤ (1 - max 0 (min 1 c)) * 1 :=
      mul_le_mul_of_nonneg_left ht1 (by linarith)
    have h3 : 0 ≤ max 0 (min 1 c) * (s:ℝ) := mul_nonneg hc0 hs0
    have h4 : 0 ≤ (1 - max 0 (min 1 c)) * (t:ℝ) := mul_nonneg (by linarith) ht0
    exact ⟨by linarith, by linarith⟩⟩

theorem convI_coe (c : ℝ) (s t : unitInterval) :
    ((convI c s t : unitInterval) : ℝ)
      = max 0 (min 1 c) * (s : ℝ) + (1 - max 0 (min 1 c)) * (t : ℝ) := rfl

theorem convI_of_mem {c : ℝ} (h0 : 0 ≤ c) (h1 : c ≤ 1) (s t : unitInterval) :
    ((convI c s t : unitInterval) : ℝ) = c * (s : ℝ) + (1 - c) * (t : ℝ) := by
  rw [convI_coe, min_eq_right h1, max_eq_right h0]

theorem continuous_convI : Continuous fun p : ℝ × (unitInterval × unitInterval) =>
    convI p.1 p.2.1 p.2.2 := by
  refine Continuous.subtype_mk ?_ _
  have hc : Continuous fun p : ℝ × (unitInterval × unitInterval) => max 0 (min 1 p.1) :=
    continuous_const.max (continuous_const.min continuous_fst)
  have hs : Continuous fun p : ℝ × (unitInterval × unitInterval) =>
      ((p.2.1 : unitInterval) : ℝ) := continuous_subtype_val.comp (continuous_fst.comp continuous_snd)
  have ht : Continuous fun p : ℝ × (unitInterval × unitInterval) =>
      ((p.2.2 : unitInterval) : ℝ) := continuous_subtype_val.comp (continuous_snd.comp continuous_snd)
  exact (hc.mul hs).add ((continuous_const.sub hc).mul ht)

/-- Phase 1 of the contraction: push the side faces onto the bottom face. -/
def contr₁ (e : ℕ) (t : unitInterval) (z : ICube (e + 1)) : ICube (e + 1) :=
  Fin.snoc (Fin.init z) (unitScale (1 - 2 * (t : ℝ)) (z (Fin.last e)))

/-- Phase 2 of the contraction: contract the bottom face to its centre. -/
def contr₂ (e : ℕ) (t : unitInterval) (z : ICube (e + 1)) : ICube (e + 1) :=
  Fin.snoc (fun i : Fin e => convI (2 * (t : ℝ) - 1) half (z (Fin.castSucc i)))
    (0 : unitInterval)

theorem contr₁_apply_castSucc (t : unitInterval) (z : ICube (e + 1)) (i : Fin e) :
    contr₁ e t z (Fin.castSucc i) = z (Fin.castSucc i) := by
  simp only [contr₁, Fin.snoc_castSucc, Fin.init]

theorem contr₁_apply_last (t : unitInterval) (z : ICube (e + 1)) :
    contr₁ e t z (Fin.last e) = unitScale (1 - 2 * (t : ℝ)) (z (Fin.last e)) := by
  simp only [contr₁, Fin.snoc_last]

theorem contr₂_apply_castSucc (t : unitInterval) (z : ICube (e + 1)) (i : Fin e) :
    contr₂ e t z (Fin.castSucc i) = convI (2 * (t : ℝ) - 1) half (z (Fin.castSucc i)) := by
  simp only [contr₂, Fin.snoc_castSucc]

theorem contr₂_apply_last (t : unitInterval) (z : ICube (e + 1)) :
    contr₂ e t z (Fin.last e) = 0 := by
  simp only [contr₂, Fin.snoc_last]

theorem continuous_contr₁ (e : ℕ) :
    Continuous fun p : ICube (e + 1) × unitInterval => contr₁ e p.2 p.1 := by
  refine continuous_pi fun j => ?_
  rcases Fin.eq_castSucc_or_eq_last j with ⟨i, rfl⟩ | rfl
  · rw [show (fun p : ICube (e + 1) × unitInterval => contr₁ e p.2 p.1 (Fin.castSucc i))
        = (fun p => p.1 (Fin.castSucc i)) from funext (fun p => contr₁_apply_castSucc p.2 p.1 i)]
    exact (continuous_apply (Fin.castSucc i)).comp continuous_fst
  · rw [show (fun p : ICube (e + 1) × unitInterval => contr₁ e p.2 p.1 (Fin.last e))
        = (fun p => unitScale (1 - 2 * (p.2 : ℝ)) (p.1 (Fin.last e))) from
      funext (fun p => contr₁_apply_last p.2 p.1)]
    exact continuous_unitScale.comp
      (Continuous.prodMk
        (continuous_const.sub (continuous_const.mul (continuous_subtype_val.comp continuous_snd)))
        ((continuous_apply (Fin.last e)).comp continuous_fst))

theorem continuous_contr₂ (e : ℕ) :
    Continuous fun p : ICube (e + 1) × unitInterval => contr₂ e p.2 p.1 := by
  refine continuous_pi fun j => ?_
  rcases Fin.eq_castSucc_or_eq_last j with ⟨i, rfl⟩ | rfl
  · rw [show (fun p : ICube (e + 1) × unitInterval => contr₂ e p.2 p.1 (Fin.castSucc i))
        = (fun p => convI (2 * (p.2 : ℝ) - 1) half (p.1 (Fin.castSucc i))) from
      funext (fun p => contr₂_apply_castSucc p.2 p.1 i)]
    exact continuous_convI.comp
      (Continuous.prodMk
        (continuous_const.mul (continuous_subtype_val.comp continuous_snd) |>.sub continuous_const)
        (Continuous.prodMk continuous_const
          ((continuous_apply (Fin.castSucc i)).comp continuous_fst)))
  · rw [show (fun p : ICube (e + 1) × unitInterval => contr₂ e p.2 p.1 (Fin.last e))
        = (fun _ => (0 : unitInterval)) from funext (fun p => contr₂_apply_last p.2 p.1)]
    exact continuous_const

/-- The contraction of `PinchSet e` to the centre of the bottom face. -/
def pinchContrFun (e : ℕ) (p : ↥(PinchSet e) × unitInterval) : ICube (e + 1) :=
  if (p.2 : ℝ) ≤ 1 / 2 then contr₁ e p.2 p.1.1 else contr₂ e p.2 p.1.1

theorem pinchContrFun_of_le (e : ℕ) {p : ↥(PinchSet e) × unitInterval}
    (hp : (p.2 : ℝ) ≤ 1 / 2) : pinchContrFun e p = contr₁ e p.2 p.1.1 := if_pos hp

theorem pinchContrFun_of_gt (e : ℕ) {p : ↥(PinchSet e) × unitInterval}
    (hp : ¬ ((p.2 : ℝ) ≤ 1 / 2)) : pinchContrFun e p = contr₂ e p.2 p.1.1 := if_neg hp

/-- The two phases of the contraction agree at `t = 1/2`. -/
theorem contr₁_eq_contr₂_half (e : ℕ) (z : ICube (e + 1)) :
    contr₁ e (⟨1 / 2, by norm_num⟩ : unitInterval) z
      = contr₂ e (⟨1 / 2, by norm_num⟩ : unitInterval) z := by
  have hsc : unitScale (1 - 2 * ((⟨1 / 2, by norm_num⟩ : unitInterval) : ℝ)) (z (Fin.last e))
      = 0 := by
    apply Subtype.ext
    rw [unitScale_of_mem (by norm_num) (by norm_num)]
    norm_num
  have hcv : ∀ s : unitInterval,
      convI (2 * ((⟨1 / 2, by norm_num⟩ : unitInterval) : ℝ) - 1) half s = s := by
    intro s
    apply Subtype.ext
    rw [convI_of_mem (by norm_num) (by norm_num)]
    norm_num
  rw [show contr₁ e (⟨1 / 2, by norm_num⟩ : unitInterval) z = Fin.snoc (Fin.init z)
      (unitScale (1 - 2 * ((⟨1 / 2, by norm_num⟩ : unitInterval) : ℝ)) (z (Fin.last e)))
      from rfl, hsc]
  funext j
  rcases Fin.eq_castSucc_or_eq_last j with ⟨i, rfl⟩ | rfl
  · rw [Fin.snoc_castSucc, contr₂_apply_castSucc, hcv]
    rfl
  · rw [Fin.snoc_last, contr₂_apply_last]

theorem pinchContrFun_zero (e : ℕ) (x : ↥(PinchSet e)) :
    pinchContrFun e (x, 0) = x.1 := by
  have hle : ((0 : unitInterval) : ℝ) ≤ 1 / 2 := by norm_num
  rw [pinchContrFun_of_le e hle]
  have hs : unitScale (1 - 2 * ((0 : unitInterval) : ℝ)) (x.1 (Fin.last e)) = x.1 (Fin.last e) := by
    apply Subtype.ext
    rw [unitScale_of_mem (by norm_num) (by norm_num)]
    norm_num
  rw [show contr₁ e 0 x.1 = Fin.snoc (Fin.init x.1)
      (unitScale (1 - 2 * ((0 : unitInterval) : ℝ)) (x.1 (Fin.last e))) from rfl, hs]
  funext j
  rcases Fin.eq_castSucc_or_eq_last j with ⟨i, rfl⟩ | rfl
  · rw [Fin.snoc_castSucc]; rfl
  · rw [Fin.snoc_last]

theorem pinchContrFun_one (e : ℕ) (x : ↥(PinchSet e)) :
    pinchContrFun e (x, 1) = pinchBase e := by
  have hgt : ¬ (((1 : unitInterval) : ℝ) ≤ 1 / 2) := by norm_num
  rw [pinchContrFun_of_gt e hgt]
  have h1 : (2 * ((1 : unitInterval) : ℝ) - 1) = 1 := by norm_num
  rw [show contr₂ e 1 x.1 = Fin.snoc (fun i : Fin e => convI (2 * ((1 : unitInterval) : ℝ) - 1)
      half (x.1 (Fin.castSucc i))) (0 : unitInterval) from rfl, h1, pinchBase]
  congr 2
  funext i
  apply Subtype.ext
  rw [convI_of_mem (by norm_num) (by norm_num)]
  norm_num

theorem pinchContrFun_mem_boundary (e : ℕ) (p : ↥(PinchSet e) × unitInterval) :
    pinchContrFun e p ∈ Cube.boundary (Fin (e + 1)) := by
  by_cases hp : (p.2 : ℝ) ≤ 1 / 2
  · rw [pinchContrFun_of_le e hp]
    -- the side coordinates are kept, the last coordinate is scaled by `⊗ 1 - 2t ∈ [0,1]`
    rcases p.1.2 with hlast | ⟨i, hi | hi⟩
    · -- the last coordinate was `0`
      refine ⟨Fin.last e, Or.inl ?_⟩
      rw [contr₁_apply_last]
      apply Subtype.ext
      rw [unitScale_of_mem (by linarith [p.2.2.1]) (by linarith [p.2.2.1]), hlast]
      norm_num
    · refine ⟨Fin.castSucc i, Or.inl ?_⟩
      rw [contr₁_apply_castSucc, hi]
    · refine ⟨Fin.castSucc i, Or.inr ?_⟩
      rw [contr₁_apply_castSucc, hi]
  · rw [pinchContrFun_of_gt e hp]
    exact ⟨Fin.last e, Or.inl (contr₂_apply_last p.2 p.1.1)⟩

theorem continuous_pinchContrFun (e : ℕ) : Continuous (pinchContrFun e) := by
  have hA : IsClosed {p : ↥(PinchSet e) × unitInterval | (p.2 : ℝ) ≤ 1 / 2} :=
    isClosed_le (continuous_subtype_val.comp continuous_snd) continuous_const
  have hB : IsClosed {p : ↥(PinchSet e) × unitInterval | (1 : ℝ) / 2 ≤ (p.2 : ℝ)} :=
    isClosed_le continuous_const (continuous_subtype_val.comp continuous_snd)
  have hcontA : ContinuousOn (pinchContrFun e) {p | (p.2 : ℝ) ≤ 1 / 2} := by
    refine ContinuousOn.congr (f := fun p : ↥(PinchSet e) × unitInterval =>
      contr₁ e p.2 p.1.1) ?_ (fun p hp => ?_)
    · have hmap : Continuous fun p : ↥(PinchSet e) × unitInterval => (p.1.1, p.2) :=
        Continuous.prodMk (continuous_subtype_val.comp continuous_fst) continuous_snd
      exact ((continuous_contr₁ e).comp hmap).continuousOn
    · exact pinchContrFun_of_le e hp
  have hcontB : ContinuousOn (pinchContrFun e) {p | (1 : ℝ) / 2 ≤ (p.2 : ℝ)} := by
    refine ContinuousOn.congr (f := fun p : ↥(PinchSet e) × unitInterval =>
      contr₂ e p.2 p.1.1) ?_ (fun p hp => ?_)
    · have hmap : Continuous fun p : ↥(PinchSet e) × unitInterval => (p.1.1, p.2) :=
        Continuous.prodMk (continuous_subtype_val.comp continuous_fst) continuous_snd
      exact ((continuous_contr₂ e).comp hmap).continuousOn
    · rcases p with ⟨x, t⟩
      have hp' : (1 : ℝ) / 2 ≤ (t : ℝ) := hp
      by_cases hc : (t : ℝ) ≤ 1 / 2
      · have ht : t = (⟨1 / 2, by norm_num⟩ : unitInterval) := Subtype.ext (le_antisymm hc hp')
        rw [pinchContrFun_of_le e hc, ht, contr₁_eq_contr₂_half]
      · exact pinchContrFun_of_gt e hc
  have hcov : {p : ↥(PinchSet e) × unitInterval | (p.2 : ℝ) ≤ 1 / 2} ∪
      {p : ↥(PinchSet e) × unitInterval | (1 : ℝ) / 2 ≤ (p.2 : ℝ)} = Set.univ := by
    ext p
    simp only [Set.mem_union, Set.mem_setOf_eq, Set.mem_univ, iff_true]
    exact le_total (p.2 : ℝ) (1 / 2)
  have hall := ContinuousOn.union_of_isClosed hcontA hcontB hA hB
  rw [hcov] at hall
  exact continuousOn_univ.mp hall

/-- **The contraction of the pinched part.** -/
theorem exists_pinchContraction (e : ℕ) :
    ∃ κ : C(↥(PinchSet e) × unitInterval, ICube (e + 1)),
      (∀ x, κ (x, 0) = x.1) ∧
      (∀ x, κ (x, 1) = pinchBase e) ∧
      (∀ x τ, κ (x, τ) ∈ Cube.boundary (Fin (e + 1))) :=
  ⟨⟨pinchContrFun e, continuous_pinchContrFun e⟩,
    pinchContrFun_zero e, pinchContrFun_one e,
    fun x τ => pinchContrFun_mem_boundary e (x, τ)⟩

end

end Work.RatHurewicz
