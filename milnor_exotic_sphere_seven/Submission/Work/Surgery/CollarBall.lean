import Submission.Work.Surgery.Collar
import Submission.Work.Surgery.Handle

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 400000

/-!
# The collar of the closed disk

The closed disk `D^{n+1}` (`Work.Surgery.Disk n = Work.SignatureBordism.Ball n`) admits an explicit
collar: the map

`S^n × [0,∞) → D^{n+1}`,  `(x, t) ↦ x/(1+t)`

is a homeomorphism onto the punctured disk `D^{n+1} ∖ {0}`, which is open in `D^{n+1}`; hence it is
an open embedding with `(x, 0) ↦ x`, i.e. a collar in the sense of
`Submission/Work/Surgery/Collar.lean`.

## Main results

* `Work.Surgery.puncturedDisk`, `isOpen_puncturedDisk` — the punctured disk;
* `Work.Surgery.ballCollarHomeo` — the homeomorphism `S^n × [0,∞) ≅ D^{n+1} ∖ {0}`;
* `Work.Surgery.ballCollar` — **the collar of the closed disk** (`Collar n (Disk n)`);
* `Work.Surgery.hasCollar_ball` — the disk satisfies the collar neighbourhood theorem.
-/

open scoped Manifold Topology ContDiff
open Function Set
open Classical

namespace Work.Surgery

noncomputable section

variable {n : ℕ}

/-- The Euclidean space in which the disk lives, as a shorthand. -/
local notation "E" => EuclideanSpace ℝ (Fin (n + 1))

/-- The punctured disk `D^{n+1} ∖ {0}`, as a subset of the closed disk. -/
def puncturedDisk (n : ℕ) : Set (Disk n) := {y | (y : EuclideanSpace ℝ (Fin (n + 1))) ≠ 0}

theorem mem_puncturedDisk_iff (y : Disk n) :
    y ∈ puncturedDisk n ↔ (y : EuclideanSpace ℝ (Fin (n + 1))) ≠ 0 := Iff.rfl

theorem isOpen_puncturedDisk (n : ℕ) : IsOpen (puncturedDisk n) := by
  have h : puncturedDisk n
      = ((fun y : Disk n => (y : EuclideanSpace ℝ (Fin (n + 1)))) ⁻¹' {0})ᶜ := by
    ext y
    simp [puncturedDisk, Set.mem_singleton_iff]
  rw [h]
  exact (isClosed_singleton.isOpen_compl).preimage continuous_subtype_val

/-- **A point of the closed disk has norm at most `1`.** -/
theorem norm_le_one_of_mem_disk (x : Disk n) : ‖(x : EuclideanSpace ℝ (Fin (n + 1)))‖ ≤ 1 := by
  have h := x.2
  rw [Metric.mem_closedBall, dist_zero_right] at h
  exact h

/-- **The norm of a boundary point of the disk is `1`.** -/
theorem norm_eq_one_of_mem_bnd_disk {x : Disk n}
    (hx : x ∈ (𝓡∂ (n + 1)).boundary (Disk n)) :
    ‖(x : EuclideanSpace ℝ (Fin (n + 1)))‖ = 1 :=
  (mem_diskSphere_iff n x).mp (by rwa [bnd_disk n] at hx)

/-- The forward map of the collar of the disk: `(x, t) ↦ x/(1+t)`. -/
def ballCollarToFun (n : ℕ) :
    ((𝓡∂ (n + 1)).boundary (Disk n) × HalfLine) → ↥(puncturedDisk n) :=
  fun p => ⟨⟨(1 / (1 + (p.2 : ℝ))) • ((p.1.1 : Disk n) : EuclideanSpace ℝ (Fin (n + 1))),
      by
        have hx := norm_eq_one_of_mem_bnd_disk p.1.2
        have ht : (0 : ℝ) ≤ (p.2 : ℝ) := p.2.2
        rw [Metric.mem_closedBall, dist_zero_right, norm_smul,
          Real.norm_of_nonneg (by positivity), hx, mul_one]
        rw [div_le_one (by linarith)]
        linarith⟩,
    by
      have hx := norm_eq_one_of_mem_bnd_disk p.1.2
      have ht : (0 : ℝ) ≤ (p.2 : ℝ) := p.2.2
      simp only [mem_puncturedDisk_iff, Subtype.coe_mk]
      intro h
      have h' : ‖(1 / (1 + (p.2 : ℝ))) • ((p.1.1 : Disk n) : EuclideanSpace ℝ (Fin (n + 1)))‖
          = 0 := by
        rw [h, norm_zero]
      rw [norm_smul, Real.norm_of_nonneg (by positivity), hx, mul_one] at h'
      have hpos : 0 < 1 / (1 + (p.2 : ℝ)) := by positivity
      linarith⟩

/-- The inverse map of the collar of the disk: `y ↦ (y/‖y‖, 1/‖y‖ - 1)`. -/
def ballCollarInvFun (n : ℕ) (y : ↥(puncturedDisk n)) :
    ((𝓡∂ (n + 1)).boundary (Disk n) × HalfLine) :=
  (⟨⟨(‖((y : Disk n) : EuclideanSpace ℝ (Fin (n + 1)))‖)⁻¹
        • ((y : Disk n) : EuclideanSpace ℝ (Fin (n + 1))),
      by
        have hpos : 0 < ‖((y : Disk n) : EuclideanSpace ℝ (Fin (n + 1)))‖ :=
          norm_pos_iff.mpr y.2
        rw [Metric.mem_closedBall, dist_zero_right, norm_smul,
          Real.norm_of_nonneg (by positivity), inv_mul_cancel₀ (ne_of_gt hpos)]⟩,
    by
      have hpos : 0 < ‖((y : Disk n) : EuclideanSpace ℝ (Fin (n + 1)))‖ :=
        norm_pos_iff.mpr y.2
      rw [bnd_disk n, mem_diskSphere_iff, norm_smul,
        Real.norm_of_nonneg (by positivity), inv_mul_cancel₀ (ne_of_gt hpos)]⟩,
  ⟨(‖((y : Disk n) : EuclideanSpace ℝ (Fin (n + 1)))‖)⁻¹ - 1,
    by
      have hpos : 0 < ‖((y : Disk n) : EuclideanSpace ℝ (Fin (n + 1)))‖ :=
        norm_pos_iff.mpr y.2
      have hle := norm_le_one_of_mem_disk (y : Disk n)
      have : 1 ≤ (‖((y : Disk n) : EuclideanSpace ℝ (Fin (n + 1)))‖)⁻¹ := by
        rw [one_le_inv₀ hpos]
        exact hle
      linarith⟩)

theorem ballCollarInvFun_toFun (n : ℕ)
    (p : (𝓡∂ (n + 1)).boundary (Disk n) × HalfLine) :
    ballCollarInvFun n (ballCollarToFun n p) = p := by
  obtain ⟨x, t⟩ := p
  have hx : ‖((x.1 : Disk n) : EuclideanSpace ℝ (Fin (n + 1)))‖ = 1 :=
    norm_eq_one_of_mem_bnd_disk x.2
  have ht : (0 : ℝ) ≤ (t : ℝ) := t.2
  have hpos : 0 < 1 + (t : ℝ) := by linarith
  have hnorm : ‖(1 / (1 + (t : ℝ))) • ((x.1 : Disk n) : EuclideanSpace ℝ (Fin (n + 1)))‖
      = 1 / (1 + (t : ℝ)) := by
    rw [norm_smul, Real.norm_of_nonneg (by positivity), hx, mul_one]
  refine Prod.ext ?_ ?_
  · refine Subtype.ext ?_
    refine Subtype.ext ?_
    show (‖(1 / (1 + (t : ℝ))) • ((x.1 : Disk n) : EuclideanSpace ℝ (Fin (n + 1)))‖)⁻¹
        • ((1 / (1 + (t : ℝ))) • ((x.1 : Disk n) : EuclideanSpace ℝ (Fin (n + 1))))
      = ((x.1 : Disk n) : EuclideanSpace ℝ (Fin (n + 1)))
    rw [hnorm, smul_smul, inv_mul_cancel₀ (by positivity), one_smul]
  · refine Subtype.ext ?_
    show ‖(1 / (1 + (t : ℝ))) • ((x.1 : Disk n) : EuclideanSpace ℝ (Fin (n + 1)))‖⁻¹ - 1
      = (t : ℝ)
    rw [hnorm, inv_div, div_one]
    ring

theorem ballCollarToFun_invFun (n : ℕ) (y : ↥(puncturedDisk n)) :
    ballCollarToFun n (ballCollarInvFun n y) = y := by
  have hpos : 0 < ‖((y : Disk n) : EuclideanSpace ℝ (Fin (n + 1)))‖ := norm_pos_iff.mpr y.2
  refine Subtype.ext ?_
  refine Subtype.ext ?_
  show (1 / (1 + ((‖((y : Disk n) : EuclideanSpace ℝ (Fin (n + 1)))‖)⁻¹ - 1)))
      • ((‖((y : Disk n) : EuclideanSpace ℝ (Fin (n + 1)))‖)⁻¹
        • ((y : Disk n) : EuclideanSpace ℝ (Fin (n + 1))))
    = ((y : Disk n) : EuclideanSpace ℝ (Fin (n + 1)))
  have h1 : 1 + ((‖((y : Disk n) : EuclideanSpace ℝ (Fin (n + 1)))‖)⁻¹ - 1)
      = (‖((y : Disk n) : EuclideanSpace ℝ (Fin (n + 1)))‖)⁻¹ := by ring
  rw [h1, one_div, smul_smul,
    show (‖((y : Disk n) : EuclideanSpace ℝ (Fin (n + 1)))‖)⁻¹⁻¹
        * (‖((y : Disk n) : EuclideanSpace ℝ (Fin (n + 1)))‖)⁻¹ = 1 from by
      rw [inv_inv, mul_inv_cancel₀ (ne_of_gt hpos)],
    one_smul]

theorem continuous_ballCollarToFun (n : ℕ) : Continuous (ballCollarToFun n) := by
  refine Continuous.subtype_mk (Continuous.subtype_mk ?_ _) _
  have h2 : Continuous fun p : (𝓡∂ (n + 1)).boundary (Disk n) × HalfLine => (p.2 : ℝ) :=
    continuous_subtype_val.comp continuous_snd
  have hx : Continuous fun p : (𝓡∂ (n + 1)).boundary (Disk n) × HalfLine =>
      ((p.1.1 : Disk n) : EuclideanSpace ℝ (Fin (n + 1))) :=
    continuous_subtype_val.comp (continuous_subtype_val.comp continuous_fst)
  have hne : ∀ p : (𝓡∂ (n + 1)).boundary (Disk n) × HalfLine, (1 + (p.2 : ℝ)) ≠ 0 := by
    intro p
    have := p.2.2
    positivity
  have hdiv : Continuous fun p : (𝓡∂ (n + 1)).boundary (Disk n) × HalfLine =>
      1 / (1 + (p.2 : ℝ)) := by
    simp only [one_div]
    exact (continuous_const.add h2).inv₀ hne
  exact hdiv.smul hx

theorem continuous_ballCollarInvFun (n : ℕ) : Continuous (ballCollarInvFun n) := by
  have hv : Continuous fun y : ↥(puncturedDisk n) =>
      ((y : Disk n) : EuclideanSpace ℝ (Fin (n + 1))) :=
    continuous_subtype_val.comp continuous_subtype_val
  have hnorm : Continuous fun y : ↥(puncturedDisk n) =>
      ‖((y : Disk n) : EuclideanSpace ℝ (Fin (n + 1)))‖ := continuous_norm.comp hv
  have hne : ∀ y : ↥(puncturedDisk n),
      ‖((y : Disk n) : EuclideanSpace ℝ (Fin (n + 1)))‖ ≠ 0 := by
    intro y
    exact ne_of_gt (norm_pos_iff.mpr y.2)
  have hinv : Continuous fun y : ↥(puncturedDisk n) =>
      (‖((y : Disk n) : EuclideanSpace ℝ (Fin (n + 1)))‖)⁻¹ := hnorm.inv₀ hne
  refine Continuous.prodMk ?_ ?_
  · refine Continuous.subtype_mk (Continuous.subtype_mk (hinv.smul hv) _) _
  · refine Continuous.subtype_mk (hinv.sub continuous_const) _

/-- **The collar homeomorphism of the disk**: `(x, t) ↦ x/(1+t)`, a homeomorphism of `S^n × [0,∞)`
onto the punctured disk. -/
def ballCollarHomeo (n : ℕ) :
    ((𝓡∂ (n + 1)).boundary (Disk n) × HalfLine) ≃ₜ ↥(puncturedDisk n) where
  toFun := ballCollarToFun n
  invFun := ballCollarInvFun n
  left_inv := ballCollarInvFun_toFun n
  right_inv := ballCollarToFun_invFun n
  continuous_toFun := continuous_ballCollarToFun n
  continuous_invFun := continuous_ballCollarInvFun n

/-- **The collar of the closed disk** `D^{n+1}`, in the sense of
`Submission/Work/Surgery/Collar.lean`. -/
def ballCollar (n : ℕ) : Collar n (Disk n) where
  toFun := fun p => (ballCollarToFun n p : Disk n)
  isOpenEmbedding :=
    (isOpen_puncturedDisk n).isOpenEmbedding_subtypeVal.comp
      (ballCollarHomeo n).isOpenEmbedding
  toFun_zero := by
    intro x
    refine Subtype.ext ?_
    show (1 / (1 + (0 : ℝ))) • ((x.1 : Disk n) : EuclideanSpace ℝ (Fin (n + 1)))
      = ((x.1 : Disk n) : EuclideanSpace ℝ (Fin (n + 1)))
    rw [add_zero, div_one, one_smul]

/-- **The closed disk satisfies the collar neighbourhood theorem.** -/
theorem hasCollar_ball (n : ℕ) : HasCollar n (Disk n) := ⟨ballCollar n⟩

end

end Work.Surgery
