import Mathlib
import Submission.Work.Interfaces.Fatou

/-!
# Geometry of Shishikura's region `Qreg` (helpers for `fatouInjOnQ`)

`MandelDim.Qreg b₁ b₂` is the complement of the closed cones of aperture `π/2` with apex `b₁`
(opening to the left) and `b₂` (opening to the right).  Writing the complement of a cone as the
union of two half-planes gives the decomposition used below:

* `Ph a = {z | 0 < Re (z-a) + Im (z-a)}`, `Pm a = {z | 0 < Re (z-a) - Im (z-a)}`  satisfy
  `Qreg (some a) none = Ph a ∪ Pm a`;
* `Rh c = {z | Re (z-c) + Im (z-c) < 0}`, `Rm c = {z | Re (z-c) - Im (z-c) < 0}`  satisfy
  `Qreg none (some c) = Rh c ∪ Rm c`;
* `Qreg (some a) (some c) = (Ph a ∪ Pm a) ∩ (Rh c ∪ Rm c)`.

Two further convex half-planes `Rpos a = {Re (z-a) > 0} ⊆ Ph a ∪ Pm a` and
`Rneg c = {Re (z-c) < 0} ⊆ Rh c ∪ Rm c` are the ones through which paths are routed.

The main content of this file is `norm_le_two_mul_of_split`: if two points of `Ph a ∪ Pm a` do not
lie in a common one of the two half-planes then they lie in the two opposite sectors, which forces
both to be within twice their mutual distance of the apex `a`.  The version for `Rh c ∪ Rm c` is
`norm_le_two_mul_of_split_R`.
-/

namespace Work.Fatou.Qreg

open MandelDim Set Metric Filter
open scoped Topology

section defs

/-- `{z | Re (z - a) + Im (z - a) > 0}`: one half of the complement of the closed cone with apex
`a` opening to the left. -/
def Ph (a : ℂ) : Set ℂ := {z | 0 < (z - a).re + (z - a).im}

/-- `{z | Re (z - a) - Im (z - a) > 0}`: the other half of the complement of that cone. -/
def Pm (a : ℂ) : Set ℂ := {z | 0 < (z - a).re - (z - a).im}

/-- `{z | Re (z - c) + Im (z - c) < 0}`. -/
def Rh (c : ℂ) : Set ℂ := {z | (z - c).re + (z - c).im < 0}

/-- `{z | Re (z - c) - Im (z - c) < 0}`. -/
def Rm (c : ℂ) : Set ℂ := {z | (z - c).re - (z - c).im < 0}

/-- The half-plane `{Re (z - a) > 0}`, contained in `Ph a ∪ Pm a`. -/
def Rpos (a : ℂ) : Set ℂ := {z | 0 < (z - a).re}

/-- The half-plane `{Re (z - c) < 0}`, contained in `Rh c ∪ Rm c`. -/
def Rneg (c : ℂ) : Set ℂ := {z | (z - c).re < 0}

@[simp] lemma mem_Ph {a z : ℂ} : z ∈ Ph a ↔ 0 < (z - a).re + (z - a).im := Iff.rfl
@[simp] lemma mem_Pm {a z : ℂ} : z ∈ Pm a ↔ 0 < (z - a).re - (z - a).im := Iff.rfl
@[simp] lemma mem_Rh {c z : ℂ} : z ∈ Rh c ↔ (z - c).re + (z - c).im < 0 := Iff.rfl
@[simp] lemma mem_Rm {c z : ℂ} : z ∈ Rm c ↔ (z - c).re - (z - c).im < 0 := Iff.rfl
@[simp] lemma mem_Rpos {a z : ℂ} : z ∈ Rpos a ↔ 0 < (z - a).re := Iff.rfl
@[simp] lemma mem_Rneg {c z : ℂ} : z ∈ Rneg c ↔ (z - c).re < 0 := Iff.rfl

end defs

/-! ## The real-linear functionals defining the half-planes -/

/-- The real-linear functional `z ↦ Re z + Im z`. -/
def reAddIm : ℂ →ₗ[ℝ] ℝ where
  toFun z := z.re + z.im
  map_add' x y := by simp only [Complex.add_re, Complex.add_im]; ring
  map_smul' c x := by
    simp only [Complex.smul_re, Complex.smul_im, smul_eq_mul, RingHom.id_apply]; ring

/-- The real-linear functional `z ↦ Re z - Im z`. -/
def reSubIm : ℂ →ₗ[ℝ] ℝ where
  toFun z := z.re - z.im
  map_add' x y := by simp only [Complex.add_re, Complex.add_im]; ring
  map_smul' c x := by
    simp only [Complex.smul_re, Complex.smul_im, smul_eq_mul, RingHom.id_apply]; ring

/-- The real-linear functional `z ↦ Re z`. -/
def reL : ℂ →ₗ[ℝ] ℝ where
  toFun z := z.re
  map_add' x y := by simp only [Complex.add_re]
  map_smul' c x := by simp only [Complex.smul_re, smul_eq_mul, RingHom.id_apply]

@[simp] lemma reAddIm_apply (z : ℂ) : (reAddIm : ℂ → ℝ) z = z.re + z.im := rfl
@[simp] lemma reSubIm_apply (z : ℂ) : (reSubIm : ℂ → ℝ) z = z.re - z.im := rfl
@[simp] lemma reL_apply (z : ℂ) : (reL : ℂ → ℝ) z = z.re := rfl

/-! ## Convexity of the half-planes -/

lemma convex_Ph (a : ℂ) : Convex ℝ (Ph a) := by
  have h : Ph a = reAddIm ⁻¹' (Ioi (reAddIm a)) := by
    ext z
    simp only [mem_Ph, Set.mem_preimage, Set.mem_Ioi, reAddIm_apply, Complex.sub_re,
      Complex.sub_im]
    constructor <;> intro h <;> linarith
  rw [h]; exact (convex_Ioi _).linear_preimage reAddIm

lemma convex_Pm (a : ℂ) : Convex ℝ (Pm a) := by
  have h : Pm a = reSubIm ⁻¹' (Ioi (reSubIm a)) := by
    ext z
    simp only [mem_Pm, Set.mem_preimage, Set.mem_Ioi, reSubIm_apply, Complex.sub_re,
      Complex.sub_im]
    constructor <;> intro h <;> linarith
  rw [h]; exact (convex_Ioi _).linear_preimage reSubIm

lemma convex_Rh (c : ℂ) : Convex ℝ (Rh c) := by
  have h : Rh c = (-reAddIm) ⁻¹' (Ioi ((-reAddIm) c)) := by
    ext z
    simp only [mem_Rh, Set.mem_preimage, Set.mem_Ioi, LinearMap.neg_apply, reAddIm_apply,
      Complex.sub_re, Complex.sub_im]
    constructor <;> intro h <;> linarith
  rw [h]; exact (convex_Ioi _).linear_preimage (-reAddIm)

lemma convex_Rm (c : ℂ) : Convex ℝ (Rm c) := by
  have h : Rm c = (-reSubIm) ⁻¹' (Ioi ((-reSubIm) c)) := by
    ext z
    simp only [mem_Rm, Set.mem_preimage, Set.mem_Ioi, LinearMap.neg_apply, reSubIm_apply,
      Complex.sub_re, Complex.sub_im]
    constructor <;> intro h <;> linarith
  rw [h]; exact (convex_Ioi _).linear_preimage (-reSubIm)

lemma convex_Rpos (a : ℂ) : Convex ℝ (Rpos a) := by
  have h : Rpos a = reL ⁻¹' (Ioi (reL a)) := by
    ext z
    simp only [mem_Rpos, Set.mem_preimage, Set.mem_Ioi, reL_apply, Complex.sub_re]
    constructor <;> intro h <;> linarith
  rw [h]; exact (convex_Ioi _).linear_preimage reL

lemma convex_Rneg (c : ℂ) : Convex ℝ (Rneg c) := by
  have h : Rneg c = (-reL) ⁻¹' (Ioi ((-reL) c)) := by
    ext z
    simp only [mem_Rneg, Set.mem_preimage, Set.mem_Ioi, LinearMap.neg_apply, reL_apply,
      Complex.sub_re]
    constructor <;> intro h <;> linarith
  rw [h]; exact (convex_Ioi _).linear_preimage (-reL)

/-! ## Membership in the unions of half-planes -/

/-- `-|Im w| < Re w` as a disjunction (membership in `Ph a ∪ Pm a` for `w = z - a`). -/
lemma neg_abs_im_lt_re_iff (w : ℂ) : -|w.im| < w.re ↔ 0 < w.re + w.im ∨ 0 < w.re - w.im := by
  rw [neg_lt, lt_abs]
  constructor
  · rintro (h | h)
    · exact Or.inl (by linarith)
    · exact Or.inr (by linarith)
  · rintro (h | h)
    · exact Or.inl (by linarith)
    · exact Or.inr (by linarith)

/-- `Re w < |Im w|` as a disjunction (membership in `Rh c ∪ Rm c` for `w = z - c`). -/
lemma re_lt_abs_im_iff (w : ℂ) : w.re < |w.im| ↔ w.re + w.im < 0 ∨ w.re - w.im < 0 := by
  rw [lt_abs]
  constructor
  · rintro (h | h)
    · exact Or.inr (by linarith)
    · exact Or.inl (by linarith)
  · rintro (h | h)
    · exact Or.inr (by linarith)
    · exact Or.inl (by linarith)

lemma mem_union_Ph_iff (a z : ℂ) : z ∈ Ph a ∪ Pm a ↔ -|(z - a).im| < (z - a).re := by
  simp only [Set.mem_union, mem_Ph, mem_Pm]
  exact (neg_abs_im_lt_re_iff (z - a)).symm

lemma mem_union_Rh_iff (c z : ℂ) : z ∈ Rh c ∪ Rm c ↔ (z - c).re < |(z - c).im| := by
  simp only [Set.mem_union, mem_Rh, mem_Rm]
  exact (re_lt_abs_im_iff (z - c)).symm

/-- The `Rh`/`Rm` conditions with the roles of `z` and `c` exchanged. -/
lemma mem_Rh_iff' (c z : ℂ) : z ∈ Rh c ↔ 0 < (c - z).re + (c - z).im := by
  simp only [mem_Rh, Complex.sub_re, Complex.sub_im]
  constructor <;> intro h <;> linarith

lemma mem_Rm_iff' (c z : ℂ) : z ∈ Rm c ↔ 0 < (c - z).re - (c - z).im := by
  simp only [mem_Rm, Complex.sub_re, Complex.sub_im]
  constructor <;> intro h <;> linarith

lemma mem_union_Ph_of_re_pos {a z : ℂ} (h : 0 < (z - a).re) : z ∈ Ph a ∪ Pm a := by
  rw [mem_union_Ph_iff]
  have := neg_nonpos.mpr (abs_nonneg (z - a).im)
  linarith

lemma mem_union_Rh_of_re_neg {c z : ℂ} (h : (z - c).re < 0) : z ∈ Rh c ∪ Rm c := by
  rw [mem_union_Rh_iff]
  exact lt_of_lt_of_le h (abs_nonneg _)

lemma Rpos_subset_Ph_union (a : ℂ) : Rpos a ⊆ Ph a ∪ Pm a := fun _ hz =>
  mem_union_Ph_of_re_pos hz

lemma Rneg_subset_Rh_union (c : ℂ) : Rneg c ⊆ Rh c ∪ Rm c := fun _ hz =>
  mem_union_Rh_of_re_neg hz

lemma Ph_inter_Pm_subset_Rpos (a : ℂ) : Ph a ∩ Pm a ⊆ Rpos a := by
  intro z hz
  simp only [Set.mem_inter_iff, mem_Ph, mem_Pm] at hz
  simp only [mem_Rpos]
  linarith [hz.1, hz.2]

lemma Rh_inter_Rm_subset_Rneg (c : ℂ) : Rh c ∩ Rm c ⊆ Rneg c := by
  intro z hz
  simp only [Set.mem_inter_iff, mem_Rh, mem_Rm] at hz
  simp only [mem_Rneg]
  linarith [hz.1, hz.2]

/-! ## The region as a union/intersection of half-planes -/

/-- The two "left" conditions of `Qreg` for `some a`. -/
lemma Qreg_conditions_Ph {a z : ℂ} :
    (∀ b ∈ (some a : Option ℂ), -|(z - b).im| < (z - b).re) ↔
      (0 < (z - a).re + (z - a).im ∨ 0 < (z - a).re - (z - a).im) := by
  simp only [Option.mem_some_iff, forall_eq', neg_abs_im_lt_re_iff]

/-- The two "right" conditions of `Qreg` for `some c`. -/
lemma Qreg_conditions_Rh {c z : ℂ} :
    (∀ b ∈ (some c : Option ℂ), (z - b).re < |(z - b).im|) ↔
      ((z - c).re + (z - c).im < 0 ∨ (z - c).re - (z - c).im < 0) := by
  simp only [Option.mem_some_iff, forall_eq']
  exact re_lt_abs_im_iff (z - c)

lemma Qreg_none_none : Qreg (none : Option ℂ) none = univ := by
  ext z; simp [Qreg]

lemma Qreg_some_none (a : ℂ) : Qreg (some a) none = Ph a ∪ Pm a := by
  ext z
  change ((∀ b ∈ (some a : Option ℂ), -|(z - b).im| < (z - b).re) ∧
    (∀ b ∈ (none : Option ℂ), (z - b).re < |(z - b).im|)) ↔ z ∈ Ph a ∪ Pm a
  have h₂ : (∀ b ∈ (none : Option ℂ), (z - b).re < |(z - b).im|) :=
    fun b hb => absurd hb (Option.not_mem_none b)
  rw [Qreg_conditions_Ph, mem_union_Ph_iff, neg_abs_im_lt_re_iff]
  exact ⟨fun h => h.1, fun h => ⟨h, h₂⟩⟩

lemma Qreg_none_some (c : ℂ) : Qreg none (some c) = Rh c ∪ Rm c := by
  ext z
  change ((∀ b ∈ (none : Option ℂ), -|(z - b).im| < (z - b).re) ∧
    (∀ b ∈ (some c : Option ℂ), (z - b).re < |(z - b).im|)) ↔ z ∈ Rh c ∪ Rm c
  have h₁ : (∀ b ∈ (none : Option ℂ), -|(z - b).im| < (z - b).re) :=
    fun b hb => absurd hb (Option.not_mem_none b)
  rw [Qreg_conditions_Rh, mem_union_Rh_iff, re_lt_abs_im_iff]
  exact ⟨fun h => h.2, fun h => ⟨h₁, h⟩⟩

lemma Qreg_some_some (a c : ℂ) :
    Qreg (some a) (some c) = (Ph a ∪ Pm a) ∩ (Rh c ∪ Rm c) := by
  ext z
  change ((∀ b ∈ (some a : Option ℂ), -|(z - b).im| < (z - b).re) ∧
    (∀ b ∈ (some c : Option ℂ), (z - b).re < |(z - b).im|)) ↔
    z ∈ (Ph a ∪ Pm a) ∩ (Rh c ∪ Rm c)
  rw [Qreg_conditions_Ph, Qreg_conditions_Rh, Set.mem_inter_iff, mem_union_Ph_iff,
    mem_union_Rh_iff, neg_abs_im_lt_re_iff, re_lt_abs_im_iff]

lemma isOpen_Qreg (b₁ b₂ : Option ℂ) : IsOpen (Qreg b₁ b₂) := by
  have hPh : ∀ a : ℂ, IsOpen (Ph a) := fun a => by
    have hc : Continuous fun z : ℂ => (z - a).re + (z - a).im :=
      (Complex.continuous_re.comp (continuous_id.sub continuous_const)).add
        (Complex.continuous_im.comp (continuous_id.sub continuous_const))
    exact isOpen_lt continuous_const hc
  have hPm : ∀ a : ℂ, IsOpen (Pm a) := fun a => by
    have hc : Continuous fun z : ℂ => (z - a).re - (z - a).im :=
      (Complex.continuous_re.comp (continuous_id.sub continuous_const)).sub
        (Complex.continuous_im.comp (continuous_id.sub continuous_const))
    exact isOpen_lt continuous_const hc
  have hRh : ∀ c : ℂ, IsOpen (Rh c) := fun c => by
    have hc : Continuous fun z : ℂ => (z - c).re + (z - c).im :=
      (Complex.continuous_re.comp (continuous_id.sub continuous_const)).add
        (Complex.continuous_im.comp (continuous_id.sub continuous_const))
    exact isOpen_lt hc continuous_const
  have hRm : ∀ c : ℂ, IsOpen (Rm c) := fun c => by
    have hc : Continuous fun z : ℂ => (z - c).re - (z - c).im :=
      (Complex.continuous_re.comp (continuous_id.sub continuous_const)).sub
        (Complex.continuous_im.comp (continuous_id.sub continuous_const))
    exact isOpen_lt hc continuous_const
  rcases b₁ with _ | a <;> rcases b₂ with _ | c
  · rw [Qreg_none_none]; exact isOpen_univ
  · rw [Qreg_none_some]; exact (hRh c).union (hRm c)
  · rw [Qreg_some_none]; exact (hPh a).union (hPm a)
  · rw [Qreg_some_some]
    exact ((hPh a).union (hPm a)).inter ((hRh c).union (hRm c))

/-! ## Points in opposite sectors are close to the apex -/

/-- If two points of the complement of the closed cone at the origin (both satisfying
`0 < Re ± Im`) do not lie in a common one of the two half-planes, then they lie in the two
opposite sectors and both are within `2 * ‖u₁ - u₂‖` of the origin. -/
lemma norm_le_two_mul_of_split {u₁ u₂ : ℂ}
    (h₁ : 0 < u₁.re + u₁.im ∨ 0 < u₁.re - u₁.im)
    (h₂ : 0 < u₂.re + u₂.im ∨ 0 < u₂.re - u₂.im)
    (hsep : ¬ ((0 < u₁.re + u₁.im ∧ 0 < u₂.re + u₂.im) ∨
      (0 < u₁.re - u₁.im ∧ 0 < u₂.re - u₂.im))) :
    ‖u₁‖ ≤ 2 * ‖u₁ - u₂‖ ∧ ‖u₂‖ ≤ 2 * ‖u₁ - u₂‖ := by
  have key : ∀ {u v : ℂ}, (0 < u.re - u.im) → u.re + u.im ≤ 0 →
      (0 < v.re + v.im) → v.re - v.im ≤ 0 →
      ‖u‖ ≤ 2 * ‖u - v‖ ∧ ‖v‖ ≤ 2 * ‖u - v‖ := by
    intro u v hu hu' hv hv'
    have hu_im : u.im < 0 := by linarith
    have hv_im : 0 < v.im := by linarith
    have hre_u : u.re * u.re ≤ u.im * u.im := by nlinarith
    have hnn : (0:ℝ) ≤ -u.im := by linarith
    have hle : -u.im ≤ v.im - u.im := by linarith
    have h2u : u.im * u.im ≤ (v.im - u.im) * (v.im - u.im) := by
      have h := mul_self_le_mul_self hnn hle
      simpa using h
    have him : v.im - u.im ≤ ‖u - v‖ := by
      have h := Complex.abs_im_le_norm (u - v)
      rw [Complex.sub_im, abs_of_nonpos (by linarith : u.im - v.im ≤ 0)] at h
      linarith
    have hsq : (v.im - u.im) * (v.im - u.im) ≤ ‖u - v‖ * ‖u - v‖ :=
      mul_self_le_mul_self (by linarith) him
    have hn : ‖u - v‖ ^ 2 = (u.re - v.re) * (u.re - v.re) + (u.im - v.im) * (u.im - v.im) := by
      rw [← Complex.normSq_eq_norm_sq, Complex.normSq_apply, Complex.sub_re, Complex.sub_im]
    have hb_u : ‖u‖ ^ 2 ≤ (2 * ‖u - v‖) ^ 2 := by
      rw [← Complex.normSq_eq_norm_sq, Complex.normSq_apply, mul_pow, hn]
      nlinarith [hre_u, h2u, hsq]
    have hb_v : ‖v‖ ^ 2 ≤ (2 * ‖u - v‖) ^ 2 := by
      rw [← Complex.normSq_eq_norm_sq, Complex.normSq_apply, mul_pow, hn]
      have hre_v : v.re * v.re ≤ v.im * v.im := by nlinarith
      have h2v : v.im * v.im ≤ (v.im - u.im) * (v.im - u.im) := by
        have h := mul_self_le_mul_self (by linarith : (0:ℝ) ≤ v.im) (by linarith : v.im ≤ v.im - u.im)
        simpa using h
      nlinarith [hre_v, h2v, hsq]
    constructor
    · have h := sq_le_sq.mp hb_u
      rwa [abs_of_nonneg (norm_nonneg u),
        abs_of_nonneg (by positivity : (0:ℝ) ≤ 2 * ‖u - v‖)] at h
    · have h := sq_le_sq.mp hb_v
      rwa [abs_of_nonneg (norm_nonneg v),
        abs_of_nonneg (by positivity : (0:ℝ) ≤ 2 * ‖u - v‖)] at h
  by_cases hp₁ : 0 < u₁.re + u₁.im
  · by_cases hp₂ : 0 < u₂.re + u₂.im
    · exact absurd (Or.inl ⟨hp₁, hp₂⟩) hsep
    · have hu : 0 < u₂.re - u₂.im := (h₂.resolve_left hp₂)
      have hv' : u₁.re - u₁.im ≤ 0 := by
        by_contra hc
        exact hsep (Or.inr ⟨not_le.mp hc, hu⟩)
      have h := key hu (le_of_not_gt hp₂) hp₁ hv'
      rw [norm_sub_rev u₂ u₁] at h
      exact ⟨h.2, h.1⟩
  · have hu : 0 < u₁.re - u₁.im := (h₁.resolve_left hp₁)
    by_cases hp₂ : 0 < u₂.re + u₂.im
    · have hv' : u₂.re - u₂.im ≤ 0 := by
        by_contra hc
        exact hsep (Or.inr ⟨hu, not_le.mp hc⟩)
      exact key hu (le_of_not_gt hp₁) hp₂ hv'
    · have hv : 0 < u₂.re - u₂.im := (h₂.resolve_left hp₂)
      exact absurd (Or.inr ⟨hu, hv⟩) hsep

/-- The `Ph`/`Pm` form of `norm_le_two_mul_of_split`. -/
lemma norm_le_two_mul_of_split_Ph {a z₁ z₂ : ℂ}
    (h₁ : z₁ ∈ Ph a ∪ Pm a) (h₂ : z₂ ∈ Ph a ∪ Pm a)
    (hsep : ¬ ((z₁ ∈ Ph a ∧ z₂ ∈ Ph a) ∨ (z₁ ∈ Pm a ∧ z₂ ∈ Pm a))) :
    ‖z₁ - a‖ ≤ 2 * ‖z₁ - z₂‖ ∧ ‖z₂ - a‖ ≤ 2 * ‖z₁ - z₂‖ := by
  have h := norm_le_two_mul_of_split (u₁ := z₁ - a) (u₂ := z₂ - a)
    ((neg_abs_im_lt_re_iff (z₁ - a)).mp ((mem_union_Ph_iff a z₁).mp h₁))
    ((neg_abs_im_lt_re_iff (z₂ - a)).mp ((mem_union_Ph_iff a z₂).mp h₂))
    (by
      intro hc
      apply hsep
      rcases hc with ⟨h, h'⟩ | ⟨h, h'⟩
      · exact Or.inl ⟨mem_Ph.mpr h, mem_Ph.mpr h'⟩
      · exact Or.inr ⟨mem_Pm.mpr h, mem_Pm.mpr h'⟩)
  rwa [sub_sub_sub_cancel_right] at h

/-- The `Rh`/`Rm` form of `norm_le_two_mul_of_split`. -/
lemma norm_le_two_mul_of_split_R {c z₁ z₂ : ℂ}
    (h₁ : z₁ ∈ Rh c ∪ Rm c) (h₂ : z₂ ∈ Rh c ∪ Rm c)
    (hsep : ¬ ((z₁ ∈ Rh c ∧ z₂ ∈ Rh c) ∨ (z₁ ∈ Rm c ∧ z₂ ∈ Rm c))) :
    ‖z₁ - c‖ ≤ 2 * ‖z₁ - z₂‖ ∧ ‖z₂ - c‖ ≤ 2 * ‖z₁ - z₂‖ := by
  have h := norm_le_two_mul_of_split (u₁ := c - z₁) (u₂ := c - z₂)
    (by
      have hh : z₁ ∈ Rh c ∨ z₁ ∈ Rm c := by simpa only [Set.mem_union] using h₁
      rcases hh with h | h
      · exact Or.inl ((mem_Rh_iff' c z₁).mp h)
      · exact Or.inr ((mem_Rm_iff' c z₁).mp h))
    (by
      have hh : z₂ ∈ Rh c ∨ z₂ ∈ Rm c := by simpa only [Set.mem_union] using h₂
      rcases hh with h | h
      · exact Or.inl ((mem_Rh_iff' c z₂).mp h)
      · exact Or.inr ((mem_Rm_iff' c z₂).mp h))
    (by
      intro hc
      apply hsep
      rcases hc with ⟨h, h'⟩ | ⟨h, h'⟩
      · exact Or.inl ⟨(mem_Rh_iff' c z₁).mpr h, (mem_Rh_iff' c z₂).mpr h'⟩
      · exact Or.inr ⟨(mem_Rm_iff' c z₁).mpr h, (mem_Rm_iff' c z₂).mpr h'⟩)
  rw [sub_sub_sub_cancel_left] at h
  rwa [norm_sub_rev c z₁, norm_sub_rev c z₂, norm_sub_rev z₂ z₁] at h


/-! ## Short paths in one 270° sector -/

/-- Two points of `Ph a ∪ Pm a` (the complement of the closed `π/2`-cone with apex `a` opening
left) at distance at most `1` are joined inside that set by a polygonal path of total length at
most `8` times their distance. -/
theorem pathSingleP {a z₁ z₂ : ℂ} (h₁ : z₁ ∈ Ph a ∪ Pm a) (h₂ : z₂ ∈ Ph a ∪ Pm a)
    (_hd : ‖z₁ - z₂‖ ≤ 1) :
    ∃ p ∈ Ph a ∪ Pm a, segment ℝ z₁ p ⊆ Ph a ∪ Pm a ∧ segment ℝ p z₂ ⊆ Ph a ∪ Pm a ∧
      ‖z₁ - p‖ + ‖p - z₂‖ ≤ 8 * ‖z₁ - z₂‖ := by
  by_cases hP : (z₁ ∈ Ph a ∧ z₂ ∈ Ph a) ∨ (z₁ ∈ Pm a ∧ z₂ ∈ Pm a)
  · rcases hP with ⟨h₁', h₂'⟩ | ⟨h₁', h₂'⟩
    · refine ⟨z₁, h₁, ?_, ?_, ?_⟩
      · rw [segment_same]; exact singleton_subset_iff.mpr h₁
      · exact fun w hw => Or.inl ((convex_Ph a).segment_subset h₁' h₂' hw)
      · simp only [sub_self, norm_zero, zero_add]
        exact le_mul_of_one_le_left (norm_nonneg _) (by norm_num)
    · refine ⟨z₁, h₁, ?_, ?_, ?_⟩
      · rw [segment_same]; exact singleton_subset_iff.mpr h₁
      · exact fun w hw => Or.inr ((convex_Pm a).segment_subset h₁' h₂' hw)
      · simp only [sub_self, norm_zero, zero_add]
        exact le_mul_of_one_le_left (norm_nonneg _) (by norm_num)
  · have hne : z₁ ≠ z₂ := by
      intro he
      apply hP
      rcases (by simpa only [Set.mem_union] using h₁ : z₁ ∈ Ph a ∨ z₁ ∈ Pm a) with h | h
      · exact Or.inl ⟨h, by simpa [he] using h⟩
      · exact Or.inr ⟨h, by simpa [he] using h⟩
    have hdpos : 0 < ‖z₁ - z₂‖ := norm_pos_iff.mpr (sub_ne_zero.mpr hne)
    obtain ⟨ha₁, ha₂⟩ := norm_le_two_mul_of_split_Ph h₁ h₂ hP
    refine ⟨a + (‖z₁ - z₂‖ : ℂ), ?_, ?_, ?_, ?_⟩
    · apply mem_union_Ph_of_re_pos
      simpa using hdpos
    · have hpPh : a + (‖z₁ - z₂‖ : ℂ) ∈ Ph a := by
        simp only [mem_Ph, add_sub_cancel_left, Complex.ofReal_re, Complex.ofReal_im, add_zero]
        exact hdpos
      have hpPm : a + (‖z₁ - z₂‖ : ℂ) ∈ Pm a := by
        simp only [mem_Pm, add_sub_cancel_left, Complex.ofReal_re, Complex.ofReal_im, sub_zero]
        exact hdpos
      rcases (by simpa only [Set.mem_union] using h₁ : z₁ ∈ Ph a ∨ z₁ ∈ Pm a) with h | h
      · exact fun w hw => Or.inl ((convex_Ph a).segment_subset h hpPh hw)
      · exact fun w hw => Or.inr ((convex_Pm a).segment_subset h hpPm hw)
    · have hpPh : a + (‖z₁ - z₂‖ : ℂ) ∈ Ph a := by
        simp only [mem_Ph, add_sub_cancel_left, Complex.ofReal_re, Complex.ofReal_im, add_zero]
        exact hdpos
      have hpPm : a + (‖z₁ - z₂‖ : ℂ) ∈ Pm a := by
        simp only [mem_Pm, add_sub_cancel_left, Complex.ofReal_re, Complex.ofReal_im, sub_zero]
        exact hdpos
      rcases (by simpa only [Set.mem_union] using h₂ : z₂ ∈ Ph a ∨ z₂ ∈ Pm a) with h | h
      · exact fun w hw => Or.inl ((convex_Ph a).segment_subset hpPh h hw)
      · exact fun w hw => Or.inr ((convex_Pm a).segment_subset hpPm h hw)
    · have hn : ‖(‖z₁ - z₂‖ : ℂ)‖ = ‖z₁ - z₂‖ := by
        have h1 : ‖(‖z₁ - z₂‖ : ℂ)‖ ^ 2 = ‖z₁ - z₂‖ ^ 2 := by
          rw [← Complex.normSq_eq_norm_sq, Complex.normSq_ofReal]
          ring
        nlinarith [h1, norm_nonneg (z₁ - z₂), norm_nonneg ((‖z₁ - z₂‖ : ℝ) : ℂ)]
      have hseg₁ : ‖z₁ - (a + (‖z₁ - z₂‖ : ℂ))‖ ≤ 3 * ‖z₁ - z₂‖ := by
        have h : z₁ - (a + (‖z₁ - z₂‖ : ℂ)) = (z₁ - a) - (‖z₁ - z₂‖ : ℂ) := by ring
        rw [h]
        calc ‖(z₁ - a) - (‖z₁ - z₂‖ : ℂ)‖ ≤ ‖z₁ - a‖ + ‖(‖z₁ - z₂‖ : ℂ)‖ := norm_sub_le _ _
          _ ≤ 2 * ‖z₁ - z₂‖ + ‖z₁ - z₂‖ := by rw [hn]; linarith
          _ = 3 * ‖z₁ - z₂‖ := by ring
      have hseg₂ : ‖(a + (‖z₁ - z₂‖ : ℂ)) - z₂‖ ≤ 3 * ‖z₁ - z₂‖ := by
        have h : (a + (‖z₁ - z₂‖ : ℂ)) - z₂ = (a - z₂) + (‖z₁ - z₂‖ : ℂ) := by ring
        rw [h]
        calc ‖(a - z₂) + (‖z₁ - z₂‖ : ℂ)‖ ≤ ‖a - z₂‖ + ‖(‖z₁ - z₂‖ : ℂ)‖ := norm_add_le _ _
          _ ≤ 2 * ‖z₁ - z₂‖ + ‖z₁ - z₂‖ := by rw [hn]; rw [norm_sub_rev]; linarith
          _ = 3 * ‖z₁ - z₂‖ := by ring
      linarith

/-- Two points of `Rh c ∪ Rm c` (the complement of the closed `π/2`-cone with apex `c` opening
right) at distance at most `1` are joined inside that set by a polygonal path of total length at
most `8` times their distance. -/
theorem pathSingleR {c z₁ z₂ : ℂ} (h₁ : z₁ ∈ Rh c ∪ Rm c) (h₂ : z₂ ∈ Rh c ∪ Rm c)
    (_hd : ‖z₁ - z₂‖ ≤ 1) :
    ∃ p ∈ Rh c ∪ Rm c, segment ℝ z₁ p ⊆ Rh c ∪ Rm c ∧ segment ℝ p z₂ ⊆ Rh c ∪ Rm c ∧
      ‖z₁ - p‖ + ‖p - z₂‖ ≤ 8 * ‖z₁ - z₂‖ := by
  by_cases hP : (z₁ ∈ Rh c ∧ z₂ ∈ Rh c) ∨ (z₁ ∈ Rm c ∧ z₂ ∈ Rm c)
  · rcases hP with ⟨h₁', h₂'⟩ | ⟨h₁', h₂'⟩
    · refine ⟨z₁, h₁, ?_, ?_, ?_⟩
      · rw [segment_same]; exact singleton_subset_iff.mpr h₁
      · exact fun w hw => Or.inl ((convex_Rh c).segment_subset h₁' h₂' hw)
      · simp only [sub_self, norm_zero, zero_add]
        exact le_mul_of_one_le_left (norm_nonneg _) (by norm_num)
    · refine ⟨z₁, h₁, ?_, ?_, ?_⟩
      · rw [segment_same]; exact singleton_subset_iff.mpr h₁
      · exact fun w hw => Or.inr ((convex_Rm c).segment_subset h₁' h₂' hw)
      · simp only [sub_self, norm_zero, zero_add]
        exact le_mul_of_one_le_left (norm_nonneg _) (by norm_num)
  · have hne : z₁ ≠ z₂ := by
      intro he
      apply hP
      rcases (by simpa only [Set.mem_union] using h₁ : z₁ ∈ Rh c ∨ z₁ ∈ Rm c) with h | h
      · exact Or.inl ⟨h, by simpa [he] using h⟩
      · exact Or.inr ⟨h, by simpa [he] using h⟩
    have hdpos : 0 < ‖z₁ - z₂‖ := norm_pos_iff.mpr (sub_ne_zero.mpr hne)
    obtain ⟨ha₁, ha₂⟩ := norm_le_two_mul_of_split_R h₁ h₂ hP
    refine ⟨c - (‖z₁ - z₂‖ : ℂ), ?_, ?_, ?_, ?_⟩
    · apply mem_union_Rh_of_re_neg
      simp only [sub_sub_cancel_left, Complex.neg_re, Complex.ofReal_re]
      linarith
    · have hpRh : c - (‖z₁ - z₂‖ : ℂ) ∈ Rh c := by
        simp only [mem_Rh, sub_sub_cancel_left, Complex.neg_re, Complex.neg_im,
          Complex.ofReal_re, Complex.ofReal_im]
        linarith
      have hpRm : c - (‖z₁ - z₂‖ : ℂ) ∈ Rm c := by
        simp only [mem_Rm, sub_sub_cancel_left, Complex.neg_re, Complex.neg_im,
          Complex.ofReal_re, Complex.ofReal_im]
        linarith
      rcases (by simpa only [Set.mem_union] using h₁ : z₁ ∈ Rh c ∨ z₁ ∈ Rm c) with h | h
      · exact fun w hw => Or.inl ((convex_Rh c).segment_subset h hpRh hw)
      · exact fun w hw => Or.inr ((convex_Rm c).segment_subset h hpRm hw)
    · have hpRh : c - (‖z₁ - z₂‖ : ℂ) ∈ Rh c := by
        simp only [mem_Rh, sub_sub_cancel_left, Complex.neg_re, Complex.neg_im,
          Complex.ofReal_re, Complex.ofReal_im]
        linarith
      have hpRm : c - (‖z₁ - z₂‖ : ℂ) ∈ Rm c := by
        simp only [mem_Rm, sub_sub_cancel_left, Complex.neg_re, Complex.neg_im,
          Complex.ofReal_re, Complex.ofReal_im]
        linarith
      rcases (by simpa only [Set.mem_union] using h₂ : z₂ ∈ Rh c ∨ z₂ ∈ Rm c) with h | h
      · exact fun w hw => Or.inl ((convex_Rh c).segment_subset hpRh h hw)
      · exact fun w hw => Or.inr ((convex_Rm c).segment_subset hpRm h hw)
    · have hn : ‖(‖z₁ - z₂‖ : ℂ)‖ = ‖z₁ - z₂‖ := by
        have h1 : ‖(‖z₁ - z₂‖ : ℂ)‖ ^ 2 = ‖z₁ - z₂‖ ^ 2 := by
          rw [← Complex.normSq_eq_norm_sq, Complex.normSq_ofReal]
          ring
        nlinarith [h1, norm_nonneg (z₁ - z₂), norm_nonneg ((‖z₁ - z₂‖ : ℝ) : ℂ)]
      have hseg₁ : ‖z₁ - (c - (‖z₁ - z₂‖ : ℂ))‖ ≤ 3 * ‖z₁ - z₂‖ := by
        have h : z₁ - (c - (‖z₁ - z₂‖ : ℂ)) = (z₁ - c) + (‖z₁ - z₂‖ : ℂ) := by ring
        rw [h]
        calc ‖(z₁ - c) + (‖z₁ - z₂‖ : ℂ)‖ ≤ ‖z₁ - c‖ + ‖(‖z₁ - z₂‖ : ℂ)‖ := norm_add_le _ _
          _ ≤ 2 * ‖z₁ - z₂‖ + ‖z₁ - z₂‖ := by rw [hn]; linarith
          _ = 3 * ‖z₁ - z₂‖ := by ring
      have hseg₂ : ‖(c - (‖z₁ - z₂‖ : ℂ)) - z₂‖ ≤ 3 * ‖z₁ - z₂‖ := by
        have h : (c - (‖z₁ - z₂‖ : ℂ)) - z₂ = (c - z₂) - (‖z₁ - z₂‖ : ℂ) := by ring
        rw [h]
        calc ‖(c - z₂) - (‖z₁ - z₂‖ : ℂ)‖ ≤ ‖c - z₂‖ + ‖(‖z₁ - z₂‖ : ℂ)‖ := norm_sub_le _ _
          _ ≤ 2 * ‖z₁ - z₂‖ + ‖z₁ - z₂‖ := by rw [hn]; rw [norm_sub_rev]; linarith
          _ = 3 * ‖z₁ - z₂‖ := by ring
      linarith


/-! ## The pair case: two sectors with `Re b₂ > Re b₁ + 4` -/

/-- `‖(‖w‖ : ℂ)‖ = ‖w‖`. -/
lemma norm_ofReal_norm (w : ℂ) : ‖((‖w‖ : ℝ) : ℂ)‖ = ‖w‖ := by
  have h1 : ‖((‖w‖ : ℝ) : ℂ)‖ ^ 2 = ‖w‖ ^ 2 := by
    rw [← Complex.normSq_eq_norm_sq, Complex.normSq_ofReal]
    ring
  nlinarith [h1, norm_nonneg w, norm_nonneg (((‖w‖ : ℝ) : ℂ))]

/-- Two points of `(Ph a ∪ Pm a) ∩ (Rh c ∪ Rm c)` (with `Re a + 4 < Re c`) at distance at most
`1/2` are joined inside that set by a polygonal path of total length at most `8` times their
distance. -/
theorem exists_mid_pair {a c : ℂ} (hadm : a.re + 4 < c.re) {z₁ z₂ : ℂ}
    (h₁ : z₁ ∈ (Ph a ∪ Pm a) ∩ (Rh c ∪ Rm c))
    (h₂ : z₂ ∈ (Ph a ∪ Pm a) ∩ (Rh c ∪ Rm c)) (hd : ‖z₁ - z₂‖ ≤ 1 / 2) :
    ∃ p ∈ (Ph a ∪ Pm a) ∩ (Rh c ∪ Rm c),
      segment ℝ z₁ p ⊆ (Ph a ∪ Pm a) ∩ (Rh c ∪ Rm c) ∧
      segment ℝ p z₂ ⊆ (Ph a ∪ Pm a) ∩ (Rh c ∪ Rm c) ∧
      ‖z₁ - p‖ + ‖p - z₂‖ ≤ 8 * ‖z₁ - z₂‖ := by
  obtain ⟨hP₁, hR₁⟩ := h₁
  obtain ⟨hP₂, hR₂⟩ := h₂
  have hd0 : (0 : ℝ) ≤ ‖z₁ - z₂‖ := norm_nonneg _
  have key : ∀ {P R : Set ℂ}, Convex ℝ P → Convex ℝ R → P ⊆ Ph a ∪ Pm a →
      R ⊆ Rh c ∪ Rm c → z₁ ∈ P → z₂ ∈ P → z₁ ∈ R → z₂ ∈ R →
      ∃ p ∈ (Ph a ∪ Pm a) ∩ (Rh c ∪ Rm c),
        segment ℝ z₁ p ⊆ (Ph a ∪ Pm a) ∩ (Rh c ∪ Rm c) ∧
        segment ℝ p z₂ ⊆ (Ph a ∪ Pm a) ∩ (Rh c ∪ Rm c) ∧
        ‖z₁ - p‖ + ‖p - z₂‖ ≤ 8 * ‖z₁ - z₂‖ := by
    intro P R hPc hRc hPs hRs hz₁P hz₂P hz₁R hz₂R
    exact ⟨z₁, ⟨hPs hz₁P, hRs hz₁R⟩,
      by rw [segment_same]; exact singleton_subset_iff.mpr ⟨hPs hz₁P, hRs hz₁R⟩,
      fun w hw => ⟨hPs (hPc.segment_subset hz₁P hz₂P hw),
        hRs (hRc.segment_subset hz₁R hz₂R hw)⟩,
      by
        simp only [sub_self, norm_zero, zero_add]
        exact le_mul_of_one_le_left hd0 (by norm_num)⟩
  have hne_of : ∀ (h : ¬ ((z₁ ∈ Ph a ∧ z₂ ∈ Ph a) ∨ (z₁ ∈ Pm a ∧ z₂ ∈ Pm a))), z₁ ≠ z₂ := by
    intro h he
    apply h
    rcases (by simpa only [Set.mem_union] using hP₁ : z₁ ∈ Ph a ∨ z₁ ∈ Pm a) with hh | hh
    · exact Or.inl ⟨hh, by simpa [he] using hh⟩
    · exact Or.inr ⟨hh, by simpa [he] using hh⟩
  have hne_of' : ∀ (h : ¬ ((z₁ ∈ Rh c ∧ z₂ ∈ Rh c) ∨ (z₁ ∈ Rm c ∧ z₂ ∈ Rm c))),
      z₁ ≠ z₂ := by
    intro h he
    apply h
    rcases (by simpa only [Set.mem_union] using hR₁ : z₁ ∈ Rh c ∨ z₁ ∈ Rm c) with hh | hh
    · exact Or.inl ⟨hh, by simpa [he] using hh⟩
    · exact Or.inr ⟨hh, by simpa [he] using hh⟩
  have hmemPh : ∀ {x : ℂ}, x ∈ Ph a ∪ Pm a → x ∈ Ph a ∨ x ∈ Pm a := by
    intro x hx; simpa only [Set.mem_union] using hx
  by_cases hB : (z₁ ∈ Rh c ∧ z₂ ∈ Rh c) ∨ (z₁ ∈ Rm c ∧ z₂ ∈ Rm c)
  · by_cases hA : (z₁ ∈ Ph a ∧ z₂ ∈ Ph a) ∨ (z₁ ∈ Pm a ∧ z₂ ∈ Pm a)
    · rcases hA with ⟨p₁, p₂⟩ | ⟨p₁, p₂⟩
      · rcases hB with ⟨q₁, q₂⟩ | ⟨q₁, q₂⟩
        · exact key (convex_Ph a) (convex_Rh c) (fun _ hw => Or.inl hw)
            (fun _ hw => Or.inl hw) p₁ p₂ q₁ q₂
        · exact key (convex_Ph a) (convex_Rm c) (fun _ hw => Or.inl hw)
            (fun _ hw => Or.inr hw) p₁ p₂ q₁ q₂
      · rcases hB with ⟨q₁, q₂⟩ | ⟨q₁, q₂⟩
        · exact key (convex_Pm a) (convex_Rh c) (fun _ hw => Or.inr hw)
            (fun _ hw => Or.inl hw) p₁ p₂ q₁ q₂
        · exact key (convex_Pm a) (convex_Rm c) (fun _ hw => Or.inr hw)
            (fun _ hw => Or.inr hw) p₁ p₂ q₁ q₂
    · -- not a common left sector: both points are within `2 ‖z₁-z₂‖` of `a`; take `p = a + d`
      have hdpos : 0 < ‖z₁ - z₂‖ := norm_pos_iff.mpr (sub_ne_zero.mpr (hne_of hA))
      obtain ⟨ha₁, ha₂⟩ := norm_le_two_mul_of_split_Ph hP₁ hP₂ hA
      have hpPh : a + (‖z₁ - z₂‖ : ℂ) ∈ Ph a := by
        simp only [mem_Ph, add_sub_cancel_left, Complex.ofReal_re, Complex.ofReal_im, add_zero]
        exact hdpos
      have hpPm : a + (‖z₁ - z₂‖ : ℂ) ∈ Pm a := by
        simp only [mem_Pm, add_sub_cancel_left, Complex.ofReal_re, Complex.ofReal_im, sub_zero]
        exact hdpos
      have hpneg : a + (‖z₁ - z₂‖ : ℂ) ∈ Rneg c := by
        rw [mem_Rneg]
        have h : (a + (‖z₁ - z₂‖ : ℂ) - c).re = (a - c).re + ‖z₁ - z₂‖ := by
          simp only [Complex.add_re, Complex.sub_re, Complex.ofReal_re]
          ring
        rw [h, Complex.sub_re]
        linarith
      have hneg : ∀ x : ℂ, ‖x - a‖ ≤ 2 * ‖z₁ - z₂‖ → x ∈ Rneg c := by
        intro x hx
        rw [mem_Rneg]
        have h : (x - c).re = (x - a).re + (a - c).re := by
          simp only [Complex.sub_re]
          ring
        rw [h]
        have h2 : (x - a).re ≤ ‖x - a‖ :=
          le_trans (le_abs_self _) (Complex.abs_re_le_norm (x - a))
        have h3 : (a - c).re < -4 := by simp only [Complex.sub_re]; linarith
        linarith
      have hn : ‖(‖z₁ - z₂‖ : ℂ)‖ = ‖z₁ - z₂‖ := norm_ofReal_norm _
      refine ⟨a + (‖z₁ - z₂‖ : ℂ), ⟨Or.inl hpPh, Rneg_subset_Rh_union c hpneg⟩, ?_, ?_, ?_⟩
      · intro w hw
        refine ⟨?_, Rneg_subset_Rh_union c ((convex_Rneg c).segment_subset (hneg z₁ ha₁) hpneg hw)⟩
        rcases hmemPh hP₁ with h | h
        · exact Or.inl ((convex_Ph a).segment_subset h hpPh hw)
        · exact Or.inr ((convex_Pm a).segment_subset h hpPm hw)
      · intro w hw
        refine ⟨?_, Rneg_subset_Rh_union c ((convex_Rneg c).segment_subset hpneg (hneg z₂ ha₂) hw)⟩
        rcases hmemPh hP₂ with h | h
        · exact Or.inl ((convex_Ph a).segment_subset hpPh h hw)
        · exact Or.inr ((convex_Pm a).segment_subset hpPm h hw)
      · have hseg₁ : ‖z₁ - (a + (‖z₁ - z₂‖ : ℂ))‖ ≤ 3 * ‖z₁ - z₂‖ := by
          have h : z₁ - (a + (‖z₁ - z₂‖ : ℂ)) = (z₁ - a) - (‖z₁ - z₂‖ : ℂ) := by ring
          rw [h]
          calc ‖(z₁ - a) - (‖z₁ - z₂‖ : ℂ)‖ ≤ ‖z₁ - a‖ + ‖(‖z₁ - z₂‖ : ℂ)‖ := norm_sub_le _ _
            _ ≤ 2 * ‖z₁ - z₂‖ + ‖z₁ - z₂‖ := by rw [hn]; linarith
            _ = 3 * ‖z₁ - z₂‖ := by ring
        have hseg₂ : ‖(a + (‖z₁ - z₂‖ : ℂ)) - z₂‖ ≤ 3 * ‖z₁ - z₂‖ := by
          have h : (a + (‖z₁ - z₂‖ : ℂ)) - z₂ = (a - z₂) + (‖z₁ - z₂‖ : ℂ) := by ring
          rw [h]
          calc ‖(a - z₂) + (‖z₁ - z₂‖ : ℂ)‖ ≤ ‖a - z₂‖ + ‖(‖z₁ - z₂‖ : ℂ)‖ := norm_add_le _ _
            _ ≤ 2 * ‖z₁ - z₂‖ + ‖z₁ - z₂‖ := by rw [hn, norm_sub_rev]; linarith
            _ = 3 * ‖z₁ - z₂‖ := by ring
        linarith
  · -- the two points lie in opposite right sectors: both are within `2 ‖z₁-z₂‖` of `c`
    have hdpos : 0 < ‖z₁ - z₂‖ := norm_pos_iff.mpr (sub_ne_zero.mpr (hne_of' hB))
    obtain ⟨hc₁, hc₂⟩ := norm_le_two_mul_of_split_R hR₁ hR₂ hB
    have hpRh : c - (‖z₁ - z₂‖ : ℂ) ∈ Rh c := by
      simp only [mem_Rh, sub_sub_cancel_left, Complex.neg_re, Complex.neg_im, Complex.ofReal_re,
        Complex.ofReal_im]
      linarith
    have hpRm : c - (‖z₁ - z₂‖ : ℂ) ∈ Rm c := by
      simp only [mem_Rm, sub_sub_cancel_left, Complex.neg_re, Complex.neg_im, Complex.ofReal_re,
        Complex.ofReal_im]
      linarith
    have hpos : ∀ x : ℂ, ‖x - c‖ ≤ 2 * ‖z₁ - z₂‖ → x ∈ Rpos a := by
      intro x hx
      rw [mem_Rpos]
      have h : (x - a).re = (x - c).re + (c - a).re := by
        simp only [Complex.sub_re]
        ring
      rw [h]
      have h2 : -(‖x - c‖) ≤ (x - c).re :=
        le_trans (neg_le_neg (Complex.abs_re_le_norm (x - c))) (neg_abs_le _)
      have h3 : 4 < (c - a).re := by simp only [Complex.sub_re]; linarith
      linarith
    have hppos : c - (‖z₁ - z₂‖ : ℂ) ∈ Rpos a := by
      rw [mem_Rpos]
      have h : (c - (‖z₁ - z₂‖ : ℂ) - a).re = (c - a).re - ‖z₁ - z₂‖ := by
        simp only [Complex.sub_re, Complex.ofReal_re]
        ring
      rw [h, Complex.sub_re]
      linarith
    have hn : ‖(‖z₁ - z₂‖ : ℂ)‖ = ‖z₁ - z₂‖ := norm_ofReal_norm _
    refine ⟨c - (‖z₁ - z₂‖ : ℂ), ⟨Rpos_subset_Ph_union a hppos,
      Or.inl hpRh⟩, ?_, ?_, ?_⟩
    · intro w hw
      refine ⟨Rpos_subset_Ph_union a ((convex_Rpos a).segment_subset (hpos z₁ hc₁) hppos hw), ?_⟩
      rcases (by simpa only [Set.mem_union] using hR₁ : z₁ ∈ Rh c ∨ z₁ ∈ Rm c) with h | h
      · exact Or.inl ((convex_Rh c).segment_subset h hpRh hw)
      · exact Or.inr ((convex_Rm c).segment_subset h hpRm hw)
    · intro w hw
      refine ⟨Rpos_subset_Ph_union a ((convex_Rpos a).segment_subset hppos (hpos z₂ hc₂) hw), ?_⟩
      rcases (by simpa only [Set.mem_union] using hR₂ : z₂ ∈ Rh c ∨ z₂ ∈ Rm c) with h | h
      · exact Or.inl ((convex_Rh c).segment_subset hpRh h hw)
      · exact Or.inr ((convex_Rm c).segment_subset hpRm h hw)
    · have hseg₁ : ‖z₁ - (c - (‖z₁ - z₂‖ : ℂ))‖ ≤ 3 * ‖z₁ - z₂‖ := by
        have h : z₁ - (c - (‖z₁ - z₂‖ : ℂ)) = (z₁ - c) + (‖z₁ - z₂‖ : ℂ) := by ring
        rw [h]
        calc ‖(z₁ - c) + (‖z₁ - z₂‖ : ℂ)‖ ≤ ‖z₁ - c‖ + ‖(‖z₁ - z₂‖ : ℂ)‖ := norm_add_le _ _
          _ ≤ 2 * ‖z₁ - z₂‖ + ‖z₁ - z₂‖ := by rw [hn]; linarith
          _ = 3 * ‖z₁ - z₂‖ := by ring
      have hseg₂ : ‖(c - (‖z₁ - z₂‖ : ℂ)) - z₂‖ ≤ 3 * ‖z₁ - z₂‖ := by
        have h : (c - (‖z₁ - z₂‖ : ℂ)) - z₂ = (c - z₂) - (‖z₁ - z₂‖ : ℂ) := by ring
        rw [h]
        calc ‖(c - z₂) - (‖z₁ - z₂‖ : ℂ)‖ ≤ ‖c - z₂‖ + ‖(‖z₁ - z₂‖ : ℂ)‖ := norm_sub_le _ _
          _ ≤ 2 * ‖z₁ - z₂‖ + ‖z₁ - z₂‖ := by rw [hn, norm_sub_rev]; linarith
          _ = 3 * ‖z₁ - z₂‖ := by ring
      linarith

end Work.Fatou.Qreg
