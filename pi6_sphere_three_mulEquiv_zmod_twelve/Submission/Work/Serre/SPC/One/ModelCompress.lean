import Mathlib
import Submission.Work.Serre.SPC.One.DiscDefs
import Submission.Work.Serre.CellStep.Tools

set_option synthInstance.maxHeartbeats 400000


/-!
# The compression of the punctured model interval onto its boundary

The punctured interval `D¹ ∖ {0}` retracts onto its two endpoints `S⁰ = {±1}` by pushing each half
linearly towards its endpoint.  This is the model computation behind the "relative part shrink"
step of the `1`-cell step, both on the base side (giving `H_*(D¹∖{0}, S⁰) = 0`) and, after lifting,
on the total space side.
-/

open scoped Topology unitInterval
open CategoryTheory CategoryTheory.Limits

namespace Work.Serre.SPC.One

noncomputable section

/-! ## Continuity is local for an open cover -/

/-- Continuity is local for an open cover. -/
theorem continuous_of_isOpen_cover {X Z : Type*} [TopologicalSpace X] [TopologicalSpace Z]
    {κ : Type*} {U : κ → Set X} (hU : ∀ k, IsOpen (U k)) (hcov : (⋃ k, U k) = Set.univ)
    {g : X → Z} (hg : ∀ k, Continuous fun x : ↥(U k) => g x) : Continuous g := by
  rw [continuous_def]
  intro O hO
  have hpre : g ⁻¹' O = ⋃ k, Subtype.val '' ((fun x : ↥(U k) => g x) ⁻¹' O) := by
    ext x
    constructor
    · intro hx
      have hxU : x ∈ ⋃ k, U k := by rw [hcov]; trivial
      obtain ⟨k, hk⟩ := Set.mem_iUnion.mp hxU
      exact Set.mem_iUnion.mpr ⟨k, ⟨⟨x, hk⟩, hx, rfl⟩⟩
    · intro hx
      obtain ⟨k, y, hy, hxy⟩ := Set.mem_iUnion.mp hx
      rw [← hxy]
      exact hy
  rw [hpre]
  refine isOpen_iUnion fun k => ?_
  obtain ⟨W, hW, hWeq⟩ := isOpen_induced_iff.mp ((hg k).isOpen_preimage O hO)
  have hWk : Subtype.val '' ((fun x : ↥(U k) => g x) ⁻¹' O) = U k ∩ W := by
    ext x
    constructor
    · rintro ⟨y, hy, rfl⟩
      refine ⟨y.2, ?_⟩
      show y ∈ Subtype.val ⁻¹' W
      rw [hWeq]
      exact hy
    · rintro ⟨hxU, hxW⟩
      refine ⟨⟨x, hxU⟩, ?_, rfl⟩
      rw [← hWeq]
      exact hxW
  rw [hWk]
  exact (hU k).inter hW

/-! ## The punctured model interval -/

/-- The punctured model interval `D¹ ∖ {0}`. -/
def punctDisc : Set cellD1 := {x | x ≠ cellD1Centre}

@[simp] theorem mem_punctDisc {x : cellD1} : x ∈ punctDisc ↔ x ≠ cellD1Centre := Iff.rfl

theorem isOpen_punctDisc : IsOpen punctDisc := isClosed_singleton.isOpen_compl

/-- The punctured model interval, as a type. -/
abbrev PD : Type := ↥punctDisc

theorem coe_ne_zero {x : ↥punctDisc} : ((x : cellD1) : ℝ) ≠ 0 := by
  intro h
  exact x.2 (Subtype.ext (by simpa [cellD1Centre] using h))

/-- The coordinate of the push of the punctured interval towards its endpoints. -/
def pushVal (x : ↥punctDisc) (s : I) : ℝ :=
  (1 - (s : ℝ)) * ((x : cellD1) : ℝ) + (s : ℝ) * (|((x : cellD1) : ℝ)| / ((x : cellD1) : ℝ))

theorem abs_div_self (x : ℝ) (hx : x ≠ 0) : |x| / x = 1 ∨ |x| / x = -1 := by
  rcases lt_or_gt_of_ne hx with h | h
  · right; rw [abs_of_neg h]; field_simp
  · left; rw [abs_of_pos h]; field_simp

theorem abs_abs_div_self (x : ℝ) (hx : x ≠ 0) : |(|x| / x)| = 1 := by
  obtain h | h := abs_div_self x hx <;> rw [h] <;> norm_num

/-- The push is the sign of `x` times the convex combination of `|x|` and `1`. -/
theorem pushVal_eq (x : ↥punctDisc) (s : I) :
    pushVal x s = (|((x : cellD1) : ℝ)| / ((x : cellD1) : ℝ)) *
      ((1 - (s : ℝ)) * |((x : cellD1) : ℝ)| + (s : ℝ)) := by
  have hx : ((x : cellD1) : ℝ) ≠ 0 := coe_ne_zero
  rw [pushVal]
  field_simp
  rw [← sq_abs]
  ring

theorem abs_pushVal (x : ↥punctDisc) (s : I) :
    |pushVal x s| = (1 - (s : ℝ)) * |((x : cellD1) : ℝ)| + (s : ℝ) := by
  rw [pushVal_eq, abs_mul, abs_abs_div_self _ coe_ne_zero, one_mul]
  have hs0 : (0 : ℝ) ≤ (s : ℝ) := s.2.1
  have hs1 : (s : ℝ) ≤ 1 := s.2.2
  have hx0 : (0 : ℝ) ≤ |((x : cellD1) : ℝ)| := abs_nonneg _
  rw [abs_of_nonneg]
  have h1 : (0 : ℝ) ≤ 1 - (s : ℝ) := by linarith
  exact add_nonneg (mul_nonneg h1 hx0) hs0

theorem pushVal_mem (x : ↥punctDisc) (s : I) : pushVal x s ∈ Metric.closedBall (0 : ℝ) 1 := by
  have hx : |((x : cellD1) : ℝ)| ≤ 1 := by
    have h := Metric.mem_closedBall.mp (x : cellD1).2
    simpa [dist_eq_norm, Real.norm_eq_abs] using h
  have hs0 : (0 : ℝ) ≤ (s : ℝ) := s.2.1
  have hs1 : (s : ℝ) ≤ 1 := s.2.2
  rw [Metric.mem_closedBall, dist_eq_norm, Real.norm_eq_abs, sub_zero, abs_pushVal]
  have h1 : (0 : ℝ) ≤ 1 - (s : ℝ) := by linarith
  have := mul_le_mul_of_nonneg_left hx h1
  linarith

theorem pushVal_ne_zero (x : ↥punctDisc) (s : I) : pushVal x s ≠ 0 := by
  intro hzero
  have hx0 : (0 : ℝ) ≤ |((x : cellD1) : ℝ)| := abs_nonneg _
  have hs0 : (0 : ℝ) ≤ (s : ℝ) := s.2.1
  have hkey : (1 - (s : ℝ)) * |((x : cellD1) : ℝ)| + (s : ℝ) = 0 := by
    have h := congrArg (fun r : ℝ => (|((x : cellD1) : ℝ)| / ((x : cellD1) : ℝ))⁻¹ * r) hzero
    rw [pushVal_eq] at h
    rw [← mul_assoc, inv_mul_cancel₀] at h
    · simpa using h
    · intro hc
      have h1 := abs_abs_div_self ((x : cellD1) : ℝ) coe_ne_zero
      rw [hc, abs_zero] at h1
      exact one_ne_zero h1.symm
  have hs1 : (s : ℝ) ≤ 1 := s.2.2
  have h1 : (0 : ℝ) ≤ 1 - (s : ℝ) := by linarith
  have hprod : (0 : ℝ) ≤ (1 - (s : ℝ)) * |((x : cellD1) : ℝ)| := mul_nonneg h1 hx0
  have hs : (s : ℝ) = 0 := le_antisymm (by linarith) hs0
  have hxa : ((x : cellD1) : ℝ) = 0 := by
    rw [hs] at hkey
    simpa using hkey
  exact coe_ne_zero hxa

/-- The coordinate of the push, as a real-valued function. -/
def pushCoord (p : (↥punctDisc) × I) : ℝ := pushVal p.1 p.2

theorem pushCoord_continuous : Continuous pushCoord := by
  rw [show pushCoord = fun p : (↥punctDisc) × I => pushVal p.1 p.2 from rfl]
  simp only [pushVal]
  have hx : ∀ p : (↥punctDisc) × I, (((p.1 : ↥punctDisc) : cellD1) : ℝ) ≠ 0 :=
    fun p => coe_ne_zero (x := p.1)
  fun_prop (disch := first | exact coe_ne_zero (x := ‹_›) | assumption)

/-- The push of the punctured model interval towards its endpoints, as a function. -/
def punctContractFun (p : ↥punctDisc × I) : ↥punctDisc :=
  ⟨⟨pushVal p.1 p.2, pushVal_mem p.1 p.2⟩,
    fun h => pushVal_ne_zero p.1 p.2 (congrArg Subtype.val h)⟩

theorem punctContractFun_continuous : Continuous punctContractFun := by
  have h2 : Continuous (fun p : (↥punctDisc) × I =>
      (Subtype.mk (Subtype.mk (pushCoord p) (pushVal_mem p.1 p.2))
        (fun hh => pushVal_ne_zero p.1 p.2 (congrArg Subtype.val hh)) : ↥punctDisc)) :=
    Continuous.subtype_mk
      (Continuous.subtype_mk
        (show Continuous (fun p : (↥punctDisc) × I => pushCoord p) from pushCoord_continuous) _) _
  exact h2

/-! ## The compression -/

/-- **The punctured model interval compresses onto its boundary `S⁰`.** -/
theorem compressRel_punctDisc (d : ℕ) :
    Work.RatHurewicz.CompressRel ↥punctDisc
      {x : ↥punctDisc | (x : cellD1) ∈ cellS0Set} d := by
  refine Work.Serre.SPC.compressRel_of_deformation
    (⟨punctContractFun, punctContractFun_continuous⟩ :
      C(↥punctDisc × I, ↥punctDisc)) ?_ ?_ ?_ d
  · -- at time `0` the push is the identity
    intro x
    apply Subtype.ext
    apply Subtype.ext
    show pushVal x 0 = ((x : cellD1) : ℝ)
    rw [pushVal_eq]
    have h1 : (|((x : cellD1) : ℝ)| / ((x : cellD1) : ℝ)) * ((x : cellD1) : ℝ) = |((x : cellD1) : ℝ)| :=
      div_mul_cancel₀ _ coe_ne_zero
    have h2 : (|((x : cellD1) : ℝ)| / ((x : cellD1) : ℝ)) * (|((x : cellD1) : ℝ)| / ((x : cellD1) : ℝ)) = 1 := by
      obtain h | h := abs_div_self ((x : cellD1) : ℝ) coe_ne_zero <;> rw [h] <;> norm_num
    have hthis : (|((x : cellD1) : ℝ)| / ((x : cellD1) : ℝ)) * |((x : cellD1) : ℝ)| = ((x : cellD1) : ℝ) := by
      calc (|((x : cellD1) : ℝ)| / ((x : cellD1) : ℝ)) * |((x : cellD1) : ℝ)|
          = (|((x : cellD1) : ℝ)| / ((x : cellD1) : ℝ)) * ((|((x : cellD1) : ℝ)| / ((x : cellD1) : ℝ)) * ((x : cellD1) : ℝ)) := by rw [h1]
        _ = ((|((x : cellD1) : ℝ)| / ((x : cellD1) : ℝ)) * (|((x : cellD1) : ℝ)| / ((x : cellD1) : ℝ))) * ((x : cellD1) : ℝ) := by ring
        _ = ((x : cellD1) : ℝ) := by rw [h2]; ring
    have h0 : (1 - ((0 : I) : ℝ)) * |((x : cellD1) : ℝ)| + ((0 : I) : ℝ) = |((x : cellD1) : ℝ)| := by
      norm_num
    rw [h0, hthis]
  · -- at time `1` the push lands on the boundary
    intro x
    obtain heps | heps := abs_div_self ((x : cellD1) : ℝ) coe_ne_zero
    · refine ⟨⟨1, ?_⟩, ?_⟩
      · simp [Metric.mem_sphere, dist_eq_norm, Real.norm_eq_abs]
      · apply Subtype.ext
        show (1 : ℝ) = pushVal x 1
        rw [pushVal_eq, heps]
        norm_num
    · refine ⟨⟨-1, ?_⟩, ?_⟩
      · simp [Metric.mem_sphere, dist_eq_norm, Real.norm_eq_abs]
      · apply Subtype.ext
        show (-1 : ℝ) = pushVal x 1
        rw [pushVal_eq, heps]
        norm_num
  · -- the push fixes the boundary
    intro y hy t
    obtain ⟨z, hz⟩ := hy
    have hyval : ((y : cellD1) : ℝ) = (z : ℝ) := (congrArg Subtype.val hz).symm
    have hzabs : |(z : ℝ)| = 1 := by
      have h := Metric.mem_sphere.mp z.2
      rw [dist_eq_norm, sub_zero, Real.norm_eq_abs] at h
      exact h
    apply Subtype.ext
    apply Subtype.ext
    show pushVal y t = ((y : cellD1) : ℝ)
    have hyabs : |((y : cellD1) : ℝ)| = 1 := by rw [hyval, hzabs]
    have hdiv : |((y : cellD1) : ℝ)| / ((y : cellD1) : ℝ) = ((y : cellD1) : ℝ) := by
      rcases (abs_eq (show (0 : ℝ) ≤ 1 by norm_num)).mp hyabs with h | h <;> rw [h] <;> norm_num
    rw [pushVal_eq, hdiv, hyabs]
    ring

/-- **The relative homology of the punctured model interval over its boundary vanishes.** -/
theorem isZero_relChains_punctDisc (m : ℕ) :
    IsZero ((Work.Cohomology.relChains (TopCat.of ↥punctDisc)
      {x : ↥punctDisc | (x : cellD1) ∈ cellS0Set}).homology m) :=
  Work.Serre.isZero_relChains_of_compress (fun d => compressRel_punctDisc d) m

end

end Work.Serre.SPC.One
