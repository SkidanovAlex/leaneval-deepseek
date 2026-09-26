import Mathlib
import Submission.Work.Drive.framePathDefs
import Submission.Helpers
import Submission.KnotMap
import Submission.Commons.Analysis.CrossProduct.cross3_contDiff

/-!
# The normal frame of a smooth knot

Given a smooth knot `r` and a direction `w` which is nowhere parallel to the velocity of `r`
(`Work.Drive.GoodDir`), this module constructs a periodic orthonormal frame `(T, n, m)` along `r`:
the orthonormalised projection `normal₁ r w` of `w` onto the normal plane, and the cross product
`normal₂ r w` of the unit tangent with it.

The frame is the raw material of the tubular-neighbourhood theorem
(`Work.Drive.normalTube_of_smoothKnot`): its defining properties are unit norm, pairwise
orthogonality, orthogonality to the velocity, periodicity, and continuity.  The last section gives
the orthogonal decomposition of a vector in the frame, which is what turns the nearest-point
property of the knot into normal coordinates.
-/

namespace Work.Drive

open LeanEval.KnotTheory.Quadrisecant
open scoped RealInnerProductSpace

noncomputable section

/-- **A direction which is nowhere parallel to the velocity of `r`.** -/
def GoodDir (r : ℝ → Space) (w : Space) : Prop :=
  w ≠ 0 ∧ ∀ t : ℝ, ∀ c : ℝ, velocity r t ≠ c • w

/-- The component of `w` orthogonal to the velocity at `t`. -/
def normalRaw (r : ℝ → Space) (w : Space) (t : ℝ) : Space :=
  w - (inner ℝ w (velocity r t) / ‖velocity r t‖ ^ 2) • velocity r t

/-- The unit tangent field of `r`. -/
def unitTan (r : ℝ → Space) (t : ℝ) : Space :=
  (‖velocity r t‖)⁻¹ • velocity r t

/-- The first unit normal field of `r` associated with the direction `w`. -/
def normal₁ (r : ℝ → Space) (w : Space) (t : ℝ) : Space :=
  (‖normalRaw r w t‖)⁻¹ • normalRaw r w t

/-- The second unit normal field of `r` associated with the direction `w`. -/
def normal₂ (r : ℝ → Space) (w : Space) (t : ℝ) : Space :=
  crossv (unitTan r t) (normal₁ r w t)

variable {r : ℝ → Space} {w : Space}

/-! ### The cross product -/

/-- The cross product is orthogonal to its second argument. -/
lemma inner_crossv_right (u v : Space) : inner ℝ (crossv u v) v = 0 := by
  rw [inner_eq_dot, crossv_ofLp, dotProduct_comm]
  exact dot_cross_self u.ofLp v.ofLp

/-- The cross product of two orthonormal vectors is a unit vector. -/
lemma norm_crossv_of_orthonormal {u v : Space} (hu : ‖u‖ = 1) (hv : ‖v‖ = 1)
    (huv : inner ℝ u v = 0) : ‖crossv u v‖ = 1 := by
  have h := norm_sq_crossv u v
  rw [hu, hv, huv] at h
  have h1 : ‖crossv u v‖ ^ 2 = (1 : ℝ) ^ 2 := by rw [h]; norm_num
  rcases sq_eq_sq_iff_eq_or_eq_neg.mp h1 with h2 | h2
  · exact h2
  · exact absurd h2 (by linarith [norm_nonneg (crossv u v)])

/-- The cross product of continuous curves is continuous. -/
lemma continuous_crossv {a b : ℝ → Space} (ha : Continuous a) (hb : Continuous b) :
    Continuous fun t : ℝ => crossv (a t) (b t) :=
  Commons.Analysis.CrossProduct.cross3_contDiff.continuous.comp (ha.prodMk hb)

/-! ### The raw normal component -/

/-- The raw normal component is orthogonal to the velocity. -/
lemma inner_normalRaw_velocity {r : ℝ → Space} {w : Space} (hreg : ∀ t : ℝ, velocity r t ≠ 0)
    (t : ℝ) : inner ℝ (normalRaw r w t) (velocity r t) = 0 := by
  have h : ‖velocity r t‖ ^ 2 ≠ 0 := pow_ne_zero 2 (norm_ne_zero_iff.mpr (hreg t))
  rw [normalRaw, inner_sub_left, real_inner_smul_left, real_inner_self_eq_norm_sq,
    div_mul_cancel₀ _ h, sub_self]

/-- The raw normal component does not vanish for a good direction. -/
lemma normalRaw_ne_zero {r : ℝ → Space} {w : Space} (hw : GoodDir r w) (t : ℝ) :
    normalRaw r w t ≠ 0 := by
  intro h0
  have hc : w = (inner ℝ w (velocity r t) / ‖velocity r t‖ ^ 2) • velocity r t :=
    sub_eq_zero.mp h0
  set c : ℝ := inner ℝ w (velocity r t) / ‖velocity r t‖ ^ 2 with hcdef
  have hcne : c ≠ 0 := by
    intro hczero
    refine hw.1 ?_
    rw [hc, hcdef] at *
    rw [hczero, zero_smul]
  exact hw.2 t c⁻¹ (by rw [hc, inv_smul_smul₀ hcne])

/-! ### The unit tangent -/

lemma norm_unitTan {r : ℝ → Space} (hr : IsSmoothKnot r) (t : ℝ) : ‖unitTan r t‖ = 1 := by
  have h : ‖velocity r t‖ ≠ 0 := norm_ne_zero_iff.mpr (hr.regular t)
  rw [unitTan, norm_smul, Real.norm_eq_abs, abs_inv, abs_of_nonneg (norm_nonneg _),
    inv_mul_cancel₀ h]

lemma velocity_eq_norm_smul_unitTan {r : ℝ → Space} (hr : IsSmoothKnot r) (t : ℝ) :
    velocity r t = ‖velocity r t‖ • unitTan r t := by
  have h : ‖velocity r t‖ ≠ 0 := norm_ne_zero_iff.mpr (hr.regular t)
  rw [unitTan, smul_smul, mul_inv_cancel₀ h, one_smul]

/-! ### The first normal field -/

lemma inner_normal₁_velocity {r : ℝ → Space} {w : Space} (hr : IsSmoothKnot r) (t : ℝ) :
    inner ℝ (normal₁ r w t) (velocity r t) = 0 := by
  rw [normal₁, inner_smul_left, inner_normalRaw_velocity (fun s => hr.regular s) t]
  simp

lemma norm_normal₁ {r : ℝ → Space} {w : Space} (hr : IsSmoothKnot r) (hw : GoodDir r w)
    (t : ℝ) : ‖normal₁ r w t‖ = 1 := by
  have h : ‖normalRaw r w t‖ ≠ 0 := norm_ne_zero_iff.mpr (normalRaw_ne_zero hw t)
  rw [normal₁, norm_smul, Real.norm_eq_abs, abs_inv, abs_of_nonneg (norm_nonneg _),
    inv_mul_cancel₀ h]

lemma inner_normal₁_unitTan {r : ℝ → Space} {w : Space} (hr : IsSmoothKnot r) (t : ℝ) :
    inner ℝ (normal₁ r w t) (unitTan r t) = 0 := by
  rw [unitTan, inner_smul_right, inner_normal₁_velocity hr t, mul_zero]

/-! ### The second normal field -/

lemma norm_normal₂ {r : ℝ → Space} {w : Space} (hr : IsSmoothKnot r) (hw : GoodDir r w)
    (t : ℝ) : ‖normal₂ r w t‖ = 1 := by
  refine norm_crossv_of_orthonormal (norm_unitTan hr t) (norm_normal₁ hr hw t) ?_
  rw [real_inner_comm]
  exact inner_normal₁_unitTan hr t

lemma inner_normal₂_unitTan {r : ℝ → Space} {w : Space} (t : ℝ) :
    inner ℝ (normal₂ r w t) (unitTan r t) = 0 := by
  rw [normal₂]
  exact inner_crossv_self (unitTan r t) (normal₁ r w t)

lemma inner_normal₂_normal₁ {r : ℝ → Space} {w : Space} (t : ℝ) :
    inner ℝ (normal₂ r w t) (normal₁ r w t) = 0 := by
  rw [normal₂]
  exact inner_crossv_right (unitTan r t) (normal₁ r w t)

lemma inner_normal₁_normal₂ {r : ℝ → Space} {w : Space} (t : ℝ) :
    inner ℝ (normal₁ r w t) (normal₂ r w t) = 0 := by
  rw [real_inner_comm]
  exact inner_normal₂_normal₁ t

lemma inner_normal₂_velocity {r : ℝ → Space} {w : Space} (hr : IsSmoothKnot r) (t : ℝ) :
    inner ℝ (normal₂ r w t) (velocity r t) = 0 := by
  rw [velocity_eq_norm_smul_unitTan hr t, inner_smul_right, inner_normal₂_unitTan t, mul_zero]

/-- The squared norm of a normal offset of the knot, computed in the frame. -/
lemma norm_sq_smul_normal_add {r : ℝ → Space} {w : Space} (hr : IsSmoothKnot r)
    (hw : GoodDir r w) (s u : ℝ) (t : ℝ) :
    ‖s • normal₁ r w t + u • normal₂ r w t‖ ^ 2 = s ^ 2 + u ^ 2 := by
  rw [norm_add_sq_real, norm_smul, norm_smul, Real.norm_eq_abs, Real.norm_eq_abs,
    norm_normal₁ hr hw t, norm_normal₂ hr hw t, real_inner_smul_left, real_inner_smul_right,
    inner_normal₁_normal₂ t]
  ring_nf
  rw [sq_abs, sq_abs]

/-! ### Periodicity -/

lemma unitTan_periodic {r : ℝ → Space} (hr : IsSmoothKnot r) (t : ℝ) :
    unitTan r (t + period) = unitTan r t := by
  rw [unitTan, unitTan, hr.velocity_periodic t]

lemma normalRaw_periodic {r : ℝ → Space} {w : Space} (hr : IsSmoothKnot r) (t : ℝ) :
    normalRaw r w (t + period) = normalRaw r w t := by
  rw [normalRaw, normalRaw, hr.velocity_periodic t]

lemma normal₁_periodic {r : ℝ → Space} {w : Space} (hr : IsSmoothKnot r) (t : ℝ) :
    normal₁ r w (t + period) = normal₁ r w t := by
  rw [normal₁, normal₁, normalRaw_periodic hr t]

lemma normal₂_periodic {r : ℝ → Space} {w : Space} (hr : IsSmoothKnot r) (t : ℝ) :
    normal₂ r w (t + period) = normal₂ r w t := by
  rw [normal₂, normal₂, unitTan_periodic hr t, normal₁_periodic hr t]

/-! ### Continuity -/

lemma continuous_unitTan {r : ℝ → Space} (hr : IsSmoothKnot r) : Continuous (unitTan r) := by
  have hv : Continuous (velocity r) := hr.smooth.continuous_deriv (by simp)
  exact ((hv.norm).inv₀ fun t => norm_ne_zero_iff.mpr (hr.regular t)).smul hv

lemma continuous_normalRaw {r : ℝ → Space} {w : Space} (hr : IsSmoothKnot r) :
    Continuous (normalRaw r w) := by
  have hv : Continuous (velocity r) := hr.smooth.continuous_deriv (by simp)
  have h1 : Continuous fun t : ℝ => inner ℝ w (velocity r t) := continuous_const.inner hv
  have h2 : Continuous fun t : ℝ => ‖velocity r t‖ ^ 2 := (hv.norm).pow 2
  have h3 : Continuous fun t : ℝ => inner ℝ w (velocity r t) / ‖velocity r t‖ ^ 2 :=
    h1.div h2 (fun t => pow_ne_zero 2 (norm_ne_zero_iff.mpr (hr.regular t)))
  exact continuous_const.sub (h3.smul hv)

lemma continuous_normal₁ {r : ℝ → Space} {w : Space} (hr : IsSmoothKnot r) (hw : GoodDir r w) :
    Continuous (normal₁ r w) := by
  have hQ : Continuous (normalRaw r w) := continuous_normalRaw hr
  exact ((hQ.norm).inv₀ fun t => norm_ne_zero_iff.mpr (normalRaw_ne_zero hw t)).smul hQ

lemma continuous_normal₂ {r : ℝ → Space} {w : Space} (hr : IsSmoothKnot r) (hw : GoodDir r w) :
    Continuous (normal₂ r w) :=
  continuous_crossv (continuous_unitTan hr) (continuous_normal₁ hr hw)

/-! ### The orthogonal decomposition in the frame -/

/-- **A vector orthogonal to an orthonormal family indexed by `Fin 3` is zero.** -/
lemma eq_zero_of_inner_eq_zero_of_orthonormal {f : Fin 3 → Space} (horth : Orthonormal ℝ f)
    {z : Space} (h : ∀ i : Fin 3, inner ℝ z (f i) = 0) : z = 0 := by
  have hli : LinearIndependent ℝ f := horth.linearIndependent
  have hcard : Fintype.card (Fin 3) = Module.finrank ℝ Space := by
    rw [Fintype.card_fin]
    simp [finrank_euclideanSpace_fin]
  have htop : Submodule.span ℝ (Set.range f) = ⊤ :=
    LinearIndependent.span_eq_top_of_card_eq_finrank hli hcard
  let ζ : Space →ₗ[ℝ] ℝ :=
    { toFun := fun u => inner ℝ z u
      map_add' := fun a b => inner_add_right z a b
      map_smul' := fun c a => by simp [inner_smul_right] }
  have hle : Submodule.span ℝ (Set.range f) ≤ LinearMap.ker ζ :=
    Submodule.span_le.mpr (by
      rintro u ⟨i, rfl⟩
      exact LinearMap.mem_ker.mpr (h i))
  have hzK : z ∈ (Submodule.span ℝ (Set.range f))ᗮ := by
    rw [Submodule.mem_orthogonal']
    exact fun u hu => LinearMap.mem_ker.mp (hle hu)
  rw [htop] at hzK
  rw [Submodule.mem_orthogonal'] at hzK
  exact inner_self_eq_zero.mp (hzK z Submodule.mem_top)

/-- **The orthogonal decomposition of a vector in the normal frame:** a vector orthogonal to the
velocity is a combination of the two normal fields. -/
lemma eq_smul_normal_of_inner_velocity_eq_zero {r : ℝ → Space} {w : Space} (hr : IsSmoothKnot r)
    (hw : GoodDir r w) (t : ℝ) (z : Space) (hz : inner ℝ z (velocity r t) = 0) :
    z = (inner ℝ z (normal₁ r w t)) • normal₁ r w t
      + (inner ℝ z (normal₂ r w t)) • normal₂ r w t := by
  have hT : inner ℝ z (unitTan r t) = 0 := by
    have hv : velocity r t = ‖velocity r t‖ • unitTan r t := velocity_eq_norm_smul_unitTan hr t
    rw [hv, inner_smul_right] at hz
    rcases mul_eq_zero.mp hz with h | h
    · exact absurd h (norm_ne_zero_iff.mpr (hr.regular t))
    · exact h
  have horth : Orthonormal ℝ ![normal₁ r w t, normal₂ r w t, unitTan r t] := by
    rw [orthonormal_iff_ite]
    intro i j
    fin_cases i <;> fin_cases j <;>
      simp [real_inner_self_eq_norm_sq, norm_normal₁ hr hw t, norm_normal₂ hr hw t,
        norm_unitTan hr t, inner_normal₁_normal₂ t, inner_normal₂_normal₁ t,
        inner_normal₁_unitTan hr t, inner_normal₂_unitTan t, real_inner_comm]
  set z' : Space := z - (inner ℝ z (normal₁ r w t)) • normal₁ r w t
    - (inner ℝ z (normal₂ r w t)) • normal₂ r w t with hz'
  have hz'0 : z' = 0 := by
    refine eq_zero_of_inner_eq_zero_of_orthonormal horth fun i => ?_
    fin_cases i <;>
      simp [hz', inner_sub_left, real_inner_smul_left, real_inner_self_eq_norm_sq,
        norm_normal₁ hr hw t, norm_normal₂ hr hw t, norm_unitTan hr t, hT, hz,
        inner_normal₁_normal₂ t, inner_normal₂_normal₁ t, inner_normal₁_unitTan hr t,
        inner_normal₂_unitTan t] <;>
      ring
  refine eq_of_sub_eq_zero ?_
  rw [show z - ((inner ℝ z (normal₁ r w t)) • normal₁ r w t
      + (inner ℝ z (normal₂ r w t)) • normal₂ r w t)
      = z - (inner ℝ z (normal₁ r w t)) • normal₁ r w t
        - (inner ℝ z (normal₂ r w t)) • normal₂ r w t by abel]
  exact hz'0

end

end Work.Drive
