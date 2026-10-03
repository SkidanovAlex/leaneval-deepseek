import Mathlib
import Submission.Lib.Unif2.Commons.Topology.Crossing.crossing_lemma_rect_path
import Submission.Lib.Unif2.Commons.Topology.Jordan.two_arcs_through

set_option autoImplicit false
set_option maxHeartbeats 1600000

open Set Metric Filter
open scoped Topology
open unitInterval

namespace Commons.Topology.Jordan

noncomputable section

/-- The closed rectangle `[-1,1] × [-2,2]` in `ℂ`. -/
def Rect : Set ℂ := {z : ℂ | z.re ∈ Icc (-1:ℝ) 1 ∧ z.im ∈ Icc (-2:ℝ) 2}

/-- Its (topological) boundary. -/
def RectBd : Set ℂ := {z : ℂ | z.re = 1 ∨ z.re = -1 ∨ z.im = 2 ∨ z.im = -2}

/-- The vertical segment from `-2i` to `2i`. -/
def VSeg : Set ℂ := {z : ℂ | z.re = 0 ∧ z.im ∈ Icc (-2:ℝ) 2}

def Spt : ℂ := ((-2:ℝ) : ℂ) * Complex.I
def Npt : ℂ := ((2:ℝ) : ℂ) * Complex.I

lemma Rect_closed : IsClosed Rect := by
  have h1 : IsClosed (Complex.re ⁻¹' Icc (-1:ℝ) 1) := isClosed_Icc.preimage Complex.continuous_re
  have h2 : IsClosed (Complex.im ⁻¹' Icc (-2:ℝ) 2) := isClosed_Icc.preimage Complex.continuous_im
  convert h1.inter h2 using 1
  ext z; simp [Rect]

lemma Rect_open_inside : {z : ℂ | z.re ∈ Ioo (-1:ℝ) 1 ∧ z.im ∈ Ioo (-2:ℝ) 2} ⊆ interior Rect := by
  have hopen : IsOpen {z : ℂ | z.re ∈ Ioo (-1:ℝ) 1 ∧ z.im ∈ Ioo (-2:ℝ) 2} := by
    have h1 : IsOpen (Complex.re ⁻¹' Ioo (-1:ℝ) 1) := isOpen_Ioo.preimage Complex.continuous_re
    have h2 : IsOpen (Complex.im ⁻¹' Ioo (-2:ℝ) 2) := isOpen_Ioo.preimage Complex.continuous_im
    convert h1.inter h2 using 1
    ext z; simp [and_comm]
  refine interior_maximal ?_ hopen
  intro z hz
  exact ⟨⟨le_of_lt hz.1.1, le_of_lt hz.1.2⟩, ⟨le_of_lt hz.2.1, le_of_lt hz.2.2⟩⟩

lemma frontier_Rect_subset : frontier Rect ⊆ RectBd := by
  intro z hz
  have hzcl : z ∈ Rect := by
    have h := frontier_subset_closure hz
    rwa [Rect_closed.closure_eq] at h
  have hznot : z ∉ interior Rect := (mem_frontier_iff_notMem_interior hzcl).mp hz
  by_contra hcon
  refine hznot (Rect_open_inside ⟨?_, ?_⟩)
  · rcases eq_or_lt_of_le hzcl.1.1 with h | h
    · exact absurd h.symm (fun hh => hcon (Or.inr (Or.inl hh)))
    · rcases eq_or_lt_of_le hzcl.1.2 with h2 | h2
      · exact absurd h2 (fun hh => hcon (Or.inl hh))
      · exact ⟨h, h2⟩
  · rcases eq_or_lt_of_le hzcl.2.1 with h | h
    · exact absurd h.symm (fun hh => hcon (Or.inr (Or.inr (Or.inr hh))))
    · rcases eq_or_lt_of_le hzcl.2.2 with h2 | h2
      · exact absurd h2 (fun hh => hcon (Or.inr (Or.inr (Or.inl hh))))
      · exact ⟨h, h2⟩

lemma RectBd_mem_Icc (z : ℂ) (hz : z ∈ RectBd) : z.im ∈ Icc (-2:ℝ) 2 ∨ z.re ∈ Icc (-1:ℝ) 1 := by
  rcases hz with h | h | h | h
  · right; rw [h]; norm_num
  · right; rw [h]; norm_num
  · left; rw [h]; norm_num
  · left; rw [h]; norm_num

lemma VSeg_closed : IsClosed VSeg := by
  have h1 : IsClosed {z : ℂ | z.re = 0} := isClosed_eq Complex.continuous_re continuous_const
  have h2 : IsClosed {z : ℂ | z.im ∈ Icc (-2:ℝ) 2} := isClosed_Icc.preimage Complex.continuous_im
  convert h1.inter h2 using 1
  ext z; simp [VSeg]

lemma Spt_mem_VSeg : Spt ∈ VSeg := by simp [Spt, VSeg]
lemma Npt_mem_VSeg : Npt ∈ VSeg := by simp [Npt, VSeg]


/-- The straight segment as a path. -/
def segPath (a b : ℂ) : Path a b where
  toFun t := (1 - (t:ℝ)) * a + (t:ℝ) * b
  continuous_toFun := by fun_prop
  source' := by simp
  target' := by simp

@[simp] lemma segPath_apply (a b : ℂ) (t : I) :
    segPath a b t = (1 - (t:ℝ)) * a + (t:ℝ) * b := rfl

lemma segPath_re (a b : ℂ) (t : I) :
    (segPath a b t).re = (1 - (t:ℝ)) * a.re + (t:ℝ) * b.re := by
  simp [segPath_apply, Complex.add_re, Complex.mul_re]

lemma segPath_im (a b : ℂ) (t : I) :
    (segPath a b t).im = (1 - (t:ℝ)) * a.im + (t:ℝ) * b.im := by
  simp [segPath_apply, Complex.add_im, Complex.mul_im]

lemma VSeg_convex : Convex ℝ VSeg := by
  have h1 : Convex ℝ {z : ℂ | z.re = 0} := by
    have h : {z : ℂ | z.re = 0} = Complex.re ⁻¹' (Set.Icc (0:ℝ) 0) := by ext z; simp
    rw [h]
    exact (convex_Icc (0:ℝ) 0).linear_preimage (Complex.reCLM : ℂ →ₗ[ℝ] ℝ)
  have h2 : Convex ℝ {z : ℂ | z.im ∈ Set.Icc (-2:ℝ) 2} :=
    (convex_Icc (-2:ℝ) 2).linear_preimage (Complex.imCLM : ℂ →ₗ[ℝ] ℝ)
  exact h1.inter h2

lemma segPath_mem_VSeg {a b : ℂ} (ha : a ∈ VSeg) (hb : b ∈ VSeg) (t : I) :
    segPath a b t ∈ VSeg := by
  have h := VSeg_convex ha hb (show (0:ℝ) ≤ 1 - (t:ℝ) by linarith [t.2.2])
    t.2.1 (by ring : (1 - (t:ℝ)) + (t:ℝ) = 1)
  simpa [segPath_apply, Complex.real_smul] using h

lemma segPath_mem_Rect {a b : ℂ} (ha : a ∈ Rect) (hb : b ∈ Rect) :
    ∀ t : I, segPath a b t ∈ Rect := by
  intro t
  refine ⟨⟨?_, ?_⟩, ⟨?_, ?_⟩⟩
  · rw [segPath_re]; nlinarith [ha.1.1, ha.1.2, hb.1.1, hb.1.2, t.2.1, t.2.2]
  · rw [segPath_re]; nlinarith [ha.1.1, ha.1.2, hb.1.1, hb.1.2, t.2.1, t.2.2]
  · rw [segPath_im]; nlinarith [ha.2.1, ha.2.2, hb.2.1, hb.2.2, t.2.1, t.2.2]
  · rw [segPath_im]; nlinarith [ha.2.1, ha.2.2, hb.2.1, hb.2.2, t.2.1, t.2.2]

lemma segPath_re_eq_zero {a b : ℂ} (ha : a.re = 0) (hb : b.re = 0) (t : I) :
    (segPath a b t).re = 0 := by
  rw [segPath_re, ha, hb]; ring

@[simp] lemma Path.cast_apply {X : Type*} [TopologicalSpace X] {a b : X} (γ : Path a b)
    {a' b' : X} (ha : a' = a) (hb : b' = b) (t : I) : (γ.cast ha hb) t = γ t :=
  congr_fun (Path.cast_coe γ ha hb) t

@[simp] lemma Path.cast_range {X : Type*} [TopologicalSpace X] {a b : X} (γ : Path a b)
    {a' b' : X} (ha : a' = a) (hb : b' = b) :
    Set.range (γ.cast ha hb) = Set.range γ := by
  have h : ⇑(γ.cast ha hb) = ⇑γ := Path.cast_coe γ ha hb
  rw [h]

lemma Path.exists_subpath {X : Type*} [TopologicalSpace X] {a b : X} (γ : Path a b) (s t : I) :
    ∃ δ : Path (γ s) (γ t), Set.range δ ⊆ Set.range γ :=
  ⟨γ.subpath s t, by rw [Path.range_subpath]; exact Set.image_subset_range _ _⟩

/-- A point of a subpath of an injective path `Path (-1) 1` between two interior parameters is
neither `1` nor `-1`. -/
lemma subpath_ne_pm_one {γ : Path (-1 : ℂ) 1} (hγ : Function.Injective (⇑γ))
    {s t : I} (hs0 : (s:ℝ) ≠ 0) (hs1 : (s:ℝ) ≠ 1) (ht0 : (t:ℝ) ≠ 0) (ht1 : (t:ℝ) ≠ 1)
    (u : I) : γ.subpath s t u ≠ 1 ∧ γ.subpath s t u ≠ -1 := by
  have hs : (s:ℝ) ∈ Ioo 0 1 := ⟨lt_of_le_of_ne s.2.1 (Ne.symm hs0), lt_of_le_of_ne s.2.2 hs1⟩
  have ht : (t:ℝ) ∈ Ioo 0 1 := ⟨lt_of_le_of_ne t.2.1 (Ne.symm ht0), lt_of_le_of_ne t.2.2 ht1⟩
  obtain ⟨v, hv, hvu⟩ : ∃ v ∈ Set.uIcc s t, γ v = γ.subpath s t u := by
    have hmem : γ.subpath s t u ∈ Set.range (γ.subpath s t) := ⟨u, rfl⟩
    rwa [Path.range_subpath] at hmem
  have hvI : (v:ℝ) ∈ Ioo (0:ℝ) 1 := by
    have hv' : (v:ℝ) ∈ Set.uIcc (s:ℝ) (t:ℝ) := hv
    rcases le_total (s:ℝ) (t:ℝ) with hst | hts
    · rw [Set.uIcc_of_le hst] at hv'
      exact ⟨lt_of_lt_of_le hs.1 hv'.1, lt_of_le_of_lt hv'.2 ht.2⟩
    · rw [Set.uIcc_of_ge hts] at hv'
      exact ⟨lt_of_lt_of_le ht.1 hv'.1, lt_of_le_of_lt hv'.2 hs.2⟩
  constructor
  · intro h
    have hv1 : γ v = γ 1 := by rw [hvu, h, γ.target]
    have : v = 1 := hγ hv1
    have : (v:ℝ) = 1 := by rw [this]; rfl
    linarith [hvI.2]
  · intro h
    have hv0 : γ v = γ 0 := by rw [hvu, h, γ.source]
    have : v = 0 := hγ hv0
    have : (v:ℝ) = 0 := by rw [this]; rfl
    linarith [hvI.1]

/-! ## The two halves of the rectangle boundary -/

/-- Left half of the lower boundary arc. -/
def LsetA : Set ℂ := {z : ℂ | z.re = -1} ∩ {z : ℂ | z.im ∈ Set.Ico (-2:ℝ) 0}
/-- Bottom side of the rectangle. -/
def LsetB : Set ℂ := {z : ℂ | z.im = -2} ∩ {z : ℂ | z.re ∈ Set.Icc (-1:ℝ) 1}
/-- Right half of the lower boundary arc. -/
def LsetC : Set ℂ := {z : ℂ | z.re = 1} ∩ {z : ℂ | z.im ∈ Set.Ico (-2:ℝ) 0}
/-- The lower boundary arc of `Rect`, without its endpoints. -/
def Lset : Set ℂ := LsetA ∪ LsetB ∪ LsetC

/-- Left half of the upper boundary arc. -/
def UsetA : Set ℂ := {z : ℂ | z.re = -1} ∩ {z : ℂ | z.im ∈ Set.Ioc (0:ℝ) 2}
/-- Top side of the rectangle. -/
def UsetB : Set ℂ := {z : ℂ | z.im = 2} ∩ {z : ℂ | z.re ∈ Set.Icc (-1:ℝ) 1}
/-- Right half of the upper boundary arc. -/
def UsetC : Set ℂ := {z : ℂ | z.re = 1} ∩ {z : ℂ | z.im ∈ Set.Ioc (0:ℝ) 2}
/-- The upper boundary arc of `Rect`, without its endpoints. -/
def Uset : Set ℂ := UsetA ∪ UsetB ∪ UsetC

lemma Spt_mem_Lset : Spt ∈ Lset := by
  refine Or.inl (Or.inr ⟨by simp [Spt], ?_⟩)
  constructor <;> simp [Spt]

lemma Npt_mem_Uset : Npt ∈ Uset := by
  refine Or.inl (Or.inr ⟨by simp [Npt], ?_⟩)
  constructor <;> simp [Npt]

lemma LsetA_convex : Convex ℝ LsetA := by
  have h1 : Convex ℝ {z : ℂ | z.re = -1} := by
    have : {z : ℂ | z.re = -1} = Complex.re ⁻¹' Set.Icc (-1:ℝ) (-1) := by
      ext z; simp
    rw [this]
    exact (convex_Icc (-1:ℝ) (-1)).linear_preimage (Complex.reCLM : ℂ →ₗ[ℝ] ℝ)
  have h2 : Convex ℝ {z : ℂ | z.im ∈ Set.Ico (-2:ℝ) 0} :=
    (convex_Ico (-2:ℝ) 0).linear_preimage (Complex.imCLM : ℂ →ₗ[ℝ] ℝ)
  exact h1.inter h2

lemma LsetB_convex : Convex ℝ LsetB := by
  have h1 : Convex ℝ {z : ℂ | z.im = -2} := by
    have : {z : ℂ | z.im = -2} = Complex.im ⁻¹' Set.Icc (-2:ℝ) (-2) := by
      ext z; simp
    rw [this]
    exact (convex_Icc (-2:ℝ) (-2)).linear_preimage (Complex.imCLM : ℂ →ₗ[ℝ] ℝ)
  have h2 : Convex ℝ {z : ℂ | z.re ∈ Set.Icc (-1:ℝ) 1} :=
    (convex_Icc (-1:ℝ) 1).linear_preimage (Complex.reCLM : ℂ →ₗ[ℝ] ℝ)
  exact h1.inter h2

lemma LsetC_convex : Convex ℝ LsetC := by
  have h1 : Convex ℝ {z : ℂ | z.re = 1} := by
    have : {z : ℂ | z.re = 1} = Complex.re ⁻¹' Set.Icc (1:ℝ) 1 := by
      ext z; simp
    rw [this]
    exact (convex_Icc (1:ℝ) 1).linear_preimage (Complex.reCLM : ℂ →ₗ[ℝ] ℝ)
  have h2 : Convex ℝ {z : ℂ | z.im ∈ Set.Ico (-2:ℝ) 0} :=
    (convex_Ico (-2:ℝ) 0).linear_preimage (Complex.imCLM : ℂ →ₗ[ℝ] ℝ)
  exact h1.inter h2

lemma UsetA_convex : Convex ℝ UsetA := by
  have h1 : Convex ℝ {z : ℂ | z.re = -1} := by
    have : {z : ℂ | z.re = -1} = Complex.re ⁻¹' Set.Icc (-1:ℝ) (-1) := by
      ext z; simp
    rw [this]
    exact (convex_Icc (-1:ℝ) (-1)).linear_preimage (Complex.reCLM : ℂ →ₗ[ℝ] ℝ)
  have h2 : Convex ℝ {z : ℂ | z.im ∈ Set.Ioc (0:ℝ) 2} :=
    (convex_Ioc (0:ℝ) 2).linear_preimage (Complex.imCLM : ℂ →ₗ[ℝ] ℝ)
  exact h1.inter h2

lemma UsetB_convex : Convex ℝ UsetB := by
  have h1 : Convex ℝ {z : ℂ | z.im = 2} := by
    have : {z : ℂ | z.im = 2} = Complex.im ⁻¹' Set.Icc (2:ℝ) 2 := by
      ext z; simp
    rw [this]
    exact (convex_Icc (2:ℝ) 2).linear_preimage (Complex.imCLM : ℂ →ₗ[ℝ] ℝ)
  have h2 : Convex ℝ {z : ℂ | z.re ∈ Set.Icc (-1:ℝ) 1} :=
    (convex_Icc (-1:ℝ) 1).linear_preimage (Complex.reCLM : ℂ →ₗ[ℝ] ℝ)
  exact h1.inter h2

lemma UsetC_convex : Convex ℝ UsetC := by
  have h1 : Convex ℝ {z : ℂ | z.re = 1} := by
    have : {z : ℂ | z.re = 1} = Complex.re ⁻¹' Set.Icc (1:ℝ) 1 := by
      ext z; simp
    rw [this]
    exact (convex_Icc (1:ℝ) 1).linear_preimage (Complex.reCLM : ℂ →ₗ[ℝ] ℝ)
  have h2 : Convex ℝ {z : ℂ | z.im ∈ Set.Ioc (0:ℝ) 2} :=
    (convex_Ioc (0:ℝ) 2).linear_preimage (Complex.imCLM : ℂ →ₗ[ℝ] ℝ)
  exact h1.inter h2

lemma LsetA_ne : LsetA.Nonempty := ⟨(-1:ℂ) - Complex.I, by
  refine ⟨by simp, ?_⟩; constructor <;> simp⟩
lemma LsetB_ne : LsetB.Nonempty := ⟨Spt, by
  refine ⟨by simp [Spt], ?_⟩; constructor <;> simp [Spt]⟩
lemma LsetC_ne : LsetC.Nonempty := ⟨(1:ℂ) - Complex.I, by
  refine ⟨by simp, ?_⟩; constructor <;> simp⟩
lemma UsetA_ne : UsetA.Nonempty := ⟨(-1:ℂ) + Complex.I, by
  refine ⟨by simp, ?_⟩; constructor <;> simp⟩
lemma UsetB_ne : UsetB.Nonempty := ⟨Npt, by
  refine ⟨by simp [Npt], ?_⟩; constructor <;> simp [Npt]⟩
lemma UsetC_ne : UsetC.Nonempty := ⟨(1:ℂ) + Complex.I, by
  refine ⟨by simp, ?_⟩; constructor <;> simp⟩

lemma LsetAB_ne : (LsetA ∩ LsetB).Nonempty := ⟨(-1:ℂ) - 2 * Complex.I, by
  refine ⟨⟨by simp, ?_⟩, by simp, ?_⟩ <;> constructor <;> simp⟩
lemma LsetBC_ne : ((LsetA ∪ LsetB) ∩ LsetC).Nonempty := ⟨(1:ℂ) - 2 * Complex.I, by
  refine ⟨Or.inr ⟨by simp, ?_⟩, by simp, ?_⟩ <;> constructor <;> simp⟩
lemma UsetAB_ne : (UsetA ∩ UsetB).Nonempty := ⟨(-1:ℂ) + 2 * Complex.I, by
  refine ⟨⟨by simp, ?_⟩, by simp, ?_⟩ <;> constructor <;> simp⟩
lemma UsetBC_ne : ((UsetA ∪ UsetB) ∩ UsetC).Nonempty := ⟨(1:ℂ) + 2 * Complex.I, by
  refine ⟨Or.inr ⟨by simp, ?_⟩, by simp, ?_⟩ <;> constructor <;> simp⟩

lemma isPathConnected_Lset : IsPathConnected Lset := by
  have hA : IsPathConnected LsetA := LsetA_convex.isPathConnected LsetA_ne
  have hB : IsPathConnected LsetB := LsetB_convex.isPathConnected LsetB_ne
  have hC : IsPathConnected LsetC := LsetC_convex.isPathConnected LsetC_ne
  have hAB : IsPathConnected (LsetA ∪ LsetB) := hA.union hB LsetAB_ne
  have : Lset = (LsetA ∪ LsetB) ∪ LsetC := rfl
  rw [this]
  exact hAB.union hC LsetBC_ne

lemma isPathConnected_Uset : IsPathConnected Uset := by
  have hA : IsPathConnected UsetA := UsetA_convex.isPathConnected UsetA_ne
  have hB : IsPathConnected UsetB := UsetB_convex.isPathConnected UsetB_ne
  have hC : IsPathConnected UsetC := UsetC_convex.isPathConnected UsetC_ne
  have hAB : IsPathConnected (UsetA ∪ UsetB) := hA.union hB UsetAB_ne
  have : Uset = (UsetA ∪ UsetB) ∪ UsetC := rfl
  rw [this]
  exact hAB.union hC UsetBC_ne

lemma Lset_subset_Rect : Lset ⊆ Rect := by
  rintro z ((hz | hz) | hz)
  · obtain ⟨hzr, hzi⟩ := hz
    simp only [Set.mem_setOf_eq] at hzr hzi
    exact ⟨⟨by norm_num [hzr], by norm_num [hzr]⟩, ⟨hzi.1, by linarith [hzi.2]⟩⟩
  · obtain ⟨hzi, hzr⟩ := hz
    simp only [Set.mem_setOf_eq] at hzr hzi
    exact ⟨⟨hzr.1, hzr.2⟩, ⟨by norm_num [hzi], by norm_num [hzi]⟩⟩
  · obtain ⟨hzr, hzi⟩ := hz
    simp only [Set.mem_setOf_eq] at hzr hzi
    exact ⟨⟨by norm_num [hzr], by norm_num [hzr]⟩, ⟨hzi.1, by linarith [hzi.2]⟩⟩

lemma Uset_subset_Rect : Uset ⊆ Rect := by
  rintro z ((hz | hz) | hz)
  · obtain ⟨hzr, hzi⟩ := hz
    simp only [Set.mem_setOf_eq] at hzr hzi
    exact ⟨⟨by norm_num [hzr], by norm_num [hzr]⟩, ⟨by linarith [hzi.1], hzi.2⟩⟩
  · obtain ⟨hzi, hzr⟩ := hz
    simp only [Set.mem_setOf_eq] at hzr hzi
    exact ⟨⟨hzr.1, hzr.2⟩, ⟨by norm_num [hzi], by norm_num [hzi]⟩⟩
  · obtain ⟨hzr, hzi⟩ := hz
    simp only [Set.mem_setOf_eq] at hzr hzi
    exact ⟨⟨by norm_num [hzr], by norm_num [hzr]⟩, ⟨by linarith [hzi.1], hzi.2⟩⟩

lemma Lset_subset_RectBd : Lset ⊆ RectBd := by
  rintro z ((hz | hz) | hz)
  · exact Or.inr (Or.inl hz.1)
  · exact Or.inr (Or.inr (Or.inr hz.1))
  · exact Or.inl hz.1

lemma Uset_subset_RectBd : Uset ⊆ RectBd := by
  rintro z ((hz | hz) | hz)
  · exact Or.inr (Or.inl hz.1)
  · exact Or.inr (Or.inr (Or.inl hz.1))
  · exact Or.inl hz.1

lemma Lset_ne_one : ∀ z ∈ Lset, z ≠ 1 := by
  rintro z ((hz | hz) | hz) h
  · have h1 : z.re = (1:ℂ).re := congrArg Complex.re h
    rw [hz.1] at h1; norm_num at h1
  · have h1 : z.im = (1:ℂ).im := congrArg Complex.im h
    rw [hz.1] at h1; norm_num at h1
  · have h1 : z.im = (1:ℂ).im := congrArg Complex.im h
    rw [Complex.one_im] at h1; linarith [hz.2.2, h1]

lemma Lset_ne_neg_one : ∀ z ∈ Lset, z ≠ -1 := by
  rintro z ((hz | hz) | hz) h
  · have h1 : z.im = (-1:ℂ).im := congrArg Complex.im h
    rw [Complex.neg_im, Complex.one_im] at h1; linarith [hz.2.2, h1]
  · have h1 : z.im = (-1:ℂ).im := congrArg Complex.im h
    rw [hz.1] at h1; norm_num at h1
  · have h1 : z.re = (-1:ℂ).re := congrArg Complex.re h
    rw [hz.1] at h1; norm_num at h1

lemma Uset_ne_one : ∀ z ∈ Uset, z ≠ 1 := by
  rintro z ((hz | hz) | hz) h
  · have h1 : z.re = (1:ℂ).re := congrArg Complex.re h
    rw [hz.1] at h1; norm_num at h1
  · have h1 : z.im = (1:ℂ).im := congrArg Complex.im h
    rw [hz.1] at h1; norm_num at h1
  · have h1 : z.im = (1:ℂ).im := congrArg Complex.im h
    rw [Complex.one_im] at h1; linarith [hz.2.1, h1]

lemma Uset_ne_neg_one : ∀ z ∈ Uset, z ≠ -1 := by
  rintro z ((hz | hz) | hz) h
  · have h1 : z.im = (-1:ℂ).im := congrArg Complex.im h
    rw [Complex.neg_im, Complex.one_im] at h1; linarith [hz.2.1, h1]
  · have h1 : z.im = (-1:ℂ).im := congrArg Complex.im h
    rw [hz.1] at h1; norm_num at h1
  · have h1 : z.re = (-1:ℂ).re := congrArg Complex.re h
    rw [hz.1] at h1; norm_num at h1

lemma Rect_inter_RectBd_subset : Rect ∩ RectBd ⊆ Lset ∪ Uset ∪ {(1:ℂ), -1} := by
  rintro z ⟨hzR, hzB⟩
  obtain ⟨⟨hzre1, hzre2⟩, ⟨hzim1, hzim2⟩⟩ := hzR
  rcases hzB with h | h | h | h
  · rcases lt_trichotomy z.im 0 with hlt | heq | hgt
    · exact Or.inl (Or.inl (Or.inr ⟨h, ⟨hzim1, hlt⟩⟩))
    · have hz1 : z = 1 := Complex.ext h (by simpa using heq)
      exact Or.inr (by rw [hz1]; simp)
    · exact Or.inl (Or.inr (Or.inr ⟨h, ⟨hgt, hzim2⟩⟩))
  · rcases lt_trichotomy z.im 0 with hlt | heq | hgt
    · exact Or.inl (Or.inl (Or.inl (Or.inl ⟨h, ⟨hzim1, hlt⟩⟩)))
    · have hz1 : z = -1 := Complex.ext h (by simpa using heq)
      exact Or.inr (by rw [hz1]; simp)
    · exact Or.inl (Or.inr (Or.inl (Or.inl ⟨h, ⟨hgt, hzim2⟩⟩)))
  · exact Or.inl (Or.inr (Or.inl (Or.inr ⟨h, ⟨hzre1, hzre2⟩⟩)))
  · exact Or.inl (Or.inl (Or.inl (Or.inr ⟨h, ⟨hzre1, hzre2⟩⟩)))

/-- The crossing lemma specialized to the rectangle `Rect` and the vertical segment. -/
lemma cross_exists (h : Path (-1:ℂ) 1) (v : Path Spt Npt)
    (hh : ∀ t, h t ∈ Rect) (hv : ∀ t, v t ∈ Rect) : ∃ s t, h s = v t := by
  have hx : (((-1:ℝ):ℂ)) = (-1:ℂ) := by norm_num
  have hy : (((1:ℝ):ℂ)) = (1:ℂ) := by norm_num
  have hcoe : ⇑(h.cast hx hy) = ⇑h := Path.cast_coe h hx hy
  have hh' : ∀ t, (h.cast hx hy t).re ∈ Set.Icc (-1:ℝ) 1 ∧
      (h.cast hx hy t).im ∈ Set.Icc (-2:ℝ) 2 := by
    intro t
    rw [show h.cast hx hy t = h t from congr_fun hcoe t]
    exact hh t
  have hv' : ∀ t, (v t).re ∈ Set.Icc (-1:ℝ) 1 ∧ (v t).im ∈ Set.Icc (-2:ℝ) 2 := hv
  obtain ⟨s, t, hst⟩ := Commons.Topology.Crossing.crossing_lemma_rect_path
    (a := -1) (b := 1) (c := -2) (d := 2) (by norm_num) (by norm_num) (h.cast hx hy) v hh' hv'
  exact ⟨s, t, (congr_fun hcoe s).symm.trans hst⟩

lemma mem_closedBall_three_of_mem_Rect {z : ℂ} (hz : z ∈ Rect) : z ∈ closedBall (0:ℂ) 3 := by
  rw [Metric.mem_closedBall, dist_zero_right]
  have h1 := hz.1; have h2 := hz.2
  have hn : ‖z‖ ^ 2 = z.re ^ 2 + z.im ^ 2 := by
    rw [Complex.sq_norm, Complex.normSq_apply]; ring
  nlinarith [norm_nonneg z, h1.1, h1.2, h2.1, h2.2]

lemma Rect_isBounded : Bornology.IsBounded Rect :=
  Metric.isBounded_closedBall.subset (fun z hz => mem_closedBall_three_of_mem_Rect hz)

lemma Spt_mem_Rect : Spt ∈ Rect := ⟨⟨by norm_num [Spt], by norm_num [Spt]⟩,
  ⟨by norm_num [Spt], by norm_num [Spt]⟩⟩
lemma Npt_mem_Rect : Npt ∈ Rect := ⟨⟨by norm_num [Npt], by norm_num [Npt]⟩,
  ⟨by norm_num [Npt], by norm_num [Npt]⟩⟩
lemma VSeg_subset_Rect : VSeg ⊆ Rect := fun z hz => ⟨⟨by rw [hz.1]; norm_num, by rw [hz.1]; norm_num⟩, hz.2⟩

/-- In the normalized setting for a Jordan curve `γ` — image inside the rectangle
`[-1,1] × [-2,2]`, meeting its boundary only in `±1`, and with `±1` on the curve — some
component of the complement of the curve is bounded.  (The "interior" of the curve.) -/
theorem bounded_component_exists (γ : C(Circle, ℂ)) (hγ : Function.Injective γ)
    (hE : ∀ t : Circle, (γ t).re ∈ Set.Icc (-1:ℝ) 1 ∧ (γ t).im ∈ Set.Icc (-2:ℝ) 2)
    (hbd : ∀ t : Circle, (γ t).re = 1 ∨ (γ t).re = -1 ∨ (γ t).im = 2 ∨ (γ t).im = -2 →
      γ t = 1 ∨ γ t = -1)
    (h1 : (1:ℂ) ∈ Set.range γ) (hm1 : (-1:ℂ) ∈ Set.range γ) :
    ∃ z ∈ (Set.range γ)ᶜ, Bornology.IsBounded (connectedComponentIn (Set.range γ)ᶜ z) := by
  classical
  have hKsub : Set.range γ ⊆ Rect := fun z hz => by
    rcases hz with ⟨t, rfl⟩; exact ⟨(hE t).1, (hE t).2⟩
  have hKBd : ∀ z ∈ Set.range γ, z ∈ RectBd → z = 1 ∨ z = -1 := by
    rintro z ⟨t, rfl⟩ hz; exact hbd t hz
  have hre0 : ∃ t : Circle, (γ t).re = 0 := by
    obtain ⟨t₁, ht₁⟩ := hm1
    obtain ⟨t₂, ht₂⟩ := h1
    obtain ⟨t, -, ht⟩ := (PreconnectedSpace.isPreconnected_univ (α := Circle)).intermediate_value₂
      (show t₁ ∈ (univ : Set Circle) from trivial) (show t₂ ∈ (univ : Set Circle) from trivial)
      (f := fun t : Circle => (γ t).re) (g := fun _ : Circle => (0:ℝ))
      (by fun_prop) continuousOn_const (by rw [ht₁]; norm_num) (by rw [ht₂]; norm_num)
    exact ⟨t, ht⟩
  have hne : (Set.range γ ∩ VSeg).Nonempty := by
    obtain ⟨t, ht⟩ := hre0
    exact ⟨γ t, ⟨⟨t, rfl⟩, ⟨ht, (hE t).2⟩⟩⟩
  have hcomp : IsCompact (Set.range γ ∩ VSeg) :=
    (isCompact_range γ.continuous).inter_right VSeg_closed
  obtain ⟨l, hl, hlmax⟩ := hcomp.exists_isMaxOn hne Complex.continuous_im.continuousOn
  have hlK : l ∈ Set.range γ := hl.1
  have hlV : l ∈ VSeg := hl.2
  have hl_re : l.re = 0 := hlV.1
  have hl_ne1 : l ≠ 1 := by intro h; have := hlV.1; rw [h] at this; norm_num at this
  have hl_nem1 : l ≠ -1 := by intro h; have := hlV.1; rw [h] at this; norm_num at this
  obtain ⟨P, Q, hPQrange, hPQinter, hPinj, hQinj, hlP⟩ :=
    Commons.Topology.Jordan.two_arcs_through γ hγ l hlK hl_ne1 hl_nem1 h1 hm1
  have hPsubK : Set.range P ⊆ Set.range γ := by rw [← hPQrange]; exact Set.subset_union_left
  have hQsubK : Set.range Q ⊆ Set.range γ := by rw [← hPQrange]; exact Set.subset_union_right
  have hPrect : ∀ t, P t ∈ Rect := fun t => hKsub (hPsubK ⟨t, rfl⟩)
  have hQrect : ∀ t, Q t ∈ Rect := fun t => hKsub (hQsubK ⟨t, rfl⟩)
  have hSPne : (Set.range P ∩ VSeg).Nonempty := ⟨l, hlP, hlV⟩
  have hSPcomp : IsCompact (Set.range P ∩ VSeg) :=
    (isCompact_range P.continuous).inter_right VSeg_closed
  obtain ⟨m, hm, hmmin⟩ := hSPcomp.exists_isMinOn hSPne Complex.continuous_im.continuousOn
  have hmP : m ∈ Set.range P := hm.1
  have hmV : m ∈ VSeg := hm.2
  have hm_re : m.re = 0 := hmV.1
  have hm_ne1 : m ≠ 1 := by intro h; have := hmV.1; rw [h] at this; norm_num at this
  have hm_nem1 : m ≠ -1 := by intro h; have := hmV.1; rw [h] at this; norm_num at this
  obtain ⟨al, hal⟩ : ∃ al : I, P al = l := by exact hlP
  obtain ⟨am, ham⟩ : ∃ am : I, P am = m := by exact hmP
  have hal0 : (al:ℝ) ≠ 0 := by
    intro h0
    have hal' : al = 0 := Subtype.ext h0
    rw [hal', Path.source] at hal
    exact hl_nem1 hal.symm
  have hal1 : (al:ℝ) ≠ 1 := by
    intro h0
    have hal' : al = 1 := Subtype.ext h0
    rw [hal', Path.target] at hal
    exact hl_ne1 hal.symm
  have ham0 : (am:ℝ) ≠ 0 := by
    intro h0
    have ham' : am = 0 := Subtype.ext h0
    rw [ham', Path.source] at ham
    exact hm_nem1 ham.symm
  have ham1 : (am:ℝ) ≠ 1 := by
    intro h0
    have ham' : am = 1 := Subtype.ext h0
    rw [ham', Path.target] at ham
    exact hm_ne1 ham.symm
  let arc : Path m l := (P.subpath am al).cast ham.symm hal.symm
  have harc_coe : ∀ u : I, arc u = P.subpath am al u := by
    intro u
    simp only [arc, Path.cast_coe]
  have harc_range : Set.range arc ⊆ Set.range P := by
    rintro z ⟨u, rfl⟩
    refine ⟨Icc.convexComb am al u, ?_⟩
    rw [harc_coe u]
    rfl
  have harc_ne : ∀ u, arc u ≠ 1 ∧ arc u ≠ -1 := by
    intro u
    rw [harc_coe u]
    exact subpath_ne_pm_one hPinj ham0 ham1 hal0 hal1 u
  let v6 : Path Spt Npt := (segPath Spt m).trans (arc.trans (segPath l Npt))
  have hSpt_re : Spt.re = 0 := by norm_num [Spt]
  have hNpt_re : Npt.re = 0 := by norm_num [Npt]
  have hSpt_im : Spt.im = -2 := by norm_num [Spt]
  have hNpt_im : Npt.im = 2 := by norm_num [Npt]
  have hseg_Sm : Set.range (segPath Spt m) ⊆ Rect := by
    rintro z ⟨u, rfl⟩
    exact segPath_mem_Rect Spt_mem_Rect (VSeg_subset_Rect hmV) u
  have harc_rect : Set.range arc ⊆ Rect := fun z hz => hKsub (hPsubK (harc_range hz))
  have hseg_lN : Set.range (segPath l Npt) ⊆ Rect := by
    rintro z ⟨u, rfl⟩
    exact segPath_mem_Rect (VSeg_subset_Rect hlV) Npt_mem_Rect u
  have hv6range : Set.range v6 ⊆ Rect := by
    intro z hz
    have hz' : z ∈ Set.range (segPath Spt m) ∪ (Set.range arc ∪ Set.range (segPath l Npt)) := by
      simpa [v6, Path.trans_range] using hz
    rcases hz' with h | h | h
    · exact hseg_Sm h
    · exact harc_rect h
    · exact hseg_lN h
  obtain ⟨s0, t0, hst0⟩ := cross_exists Q v6 hQrect (fun t => hv6range ⟨t, rfl⟩)
  have harc_Q : ∀ z, z ∈ Set.range arc → z ∈ Set.range Q → False := by
    rintro z ⟨u, rfl⟩ hzQ
    have h1 := (harc_ne u).1
    have h2 := (harc_ne u).2
    have hzP : arc u ∈ Set.range P := harc_range ⟨u, rfl⟩
    have hmem : arc u ∈ Set.range P ∩ Set.range Q := ⟨hzP, hzQ⟩
    rw [hPQinter] at hmem
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hmem
    rcases hmem with h | h
    · exact h1 h
    · exact h2 h
  have hseg_Q : ∀ z, z ∈ Set.range (segPath l Npt) → z ∈ Set.range Q → False := by
    rintro z ⟨u, rfl⟩ hzQ
    have hzV : segPath l Npt u ∈ VSeg := segPath_mem_VSeg hlV Npt_mem_VSeg u
    have hzK : segPath l Npt u ∈ Set.range γ := hQsubK hzQ
    have hle : (segPath l Npt u).im ≤ l.im := isMaxOn_iff.mp hlmax _ ⟨hzK, hzV⟩
    have hge : l.im ≤ (segPath l Npt u).im := by
      rw [segPath_im, hNpt_im]
      have hlim2 : l.im ≤ 2 := hlV.2.2
      have := mul_nonneg u.2.1 (by linarith : (0:ℝ) ≤ 2 - l.im); linarith
    have heq_im : (segPath l Npt u).im = l.im := le_antisymm hle hge
    have heq : segPath l Npt u = l := Complex.ext (by rw [hzV.1, hl_re]) heq_im
    have hlQ : l ∈ Set.range Q := heq ▸ hzQ
    have hmem : l ∈ Set.range P ∩ Set.range Q := ⟨hlP, hlQ⟩
    rw [hPQinter] at hmem
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hmem
    rcases hmem with h | h
    · exact hl_ne1 h
    · exact hl_nem1 h
  have hQmseg : (Set.range Q ∩ Set.range (segPath Spt m)).Nonempty := by
    have hmem : Q s0 ∈ Set.range v6 := ⟨t0, hst0.symm⟩
    have hmem' : Q s0 ∈ Set.range (segPath Spt m) ∪ (Set.range arc ∪ Set.range (segPath l Npt)) := by
      simpa [v6, Path.trans_range] using hmem
    rcases hmem' with h | h | h
    · exact ⟨Q s0, ⟨⟨s0, rfl⟩, h⟩⟩
    · exact absurd (harc_Q (Q s0) h ⟨s0, rfl⟩) (fun hh => hh)
    · exact absurd (hseg_Q (Q s0) h ⟨s0, rfl⟩) (fun hh => hh)
  have hQcompact : IsCompact (Set.range Q) := isCompact_range Q.continuous
  have hsegcompact : IsCompact (Set.range (segPath Spt m)) :=
    isCompact_range (segPath Spt m).continuous
  obtain ⟨p, hp, hpmax⟩ := (hQcompact.inter hsegcompact).exists_isMaxOn hQmseg
    Complex.continuous_im.continuousOn
  have hpQ : p ∈ Set.range Q := hp.1
  have hpS : p ∈ Set.range (segPath Spt m) := hp.2
  have hpV : p ∈ VSeg := by
    obtain ⟨u, rfl⟩ := hpS
    refine ⟨segPath_re_eq_zero hSpt_re hm_re u, ?_⟩
    rw [segPath_im, hSpt_im]
    constructor <;> nlinarith [hmV.2.1, hmV.2.2, u.2.1, u.2.2]
  have hp_im_le : p.im ≤ m.im := by
    obtain ⟨u, rfl⟩ := hpS
    rw [segPath_im, hSpt_im]
    nlinarith [hmV.2.1, u.2.1, u.2.2]
  have hp_ne_m : p ≠ m := by
    intro hpm
    have hmQ : m ∈ Set.range Q := hpm ▸ hpQ
    have hmem : m ∈ Set.range P ∩ Set.range Q := ⟨hmP, hmQ⟩
    rw [hPQinter] at hmem
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hmem
    rcases hmem with h | h
    · exact hm_ne1 h
    · exact hm_nem1 h
  have hp_im_lt : p.im < m.im := by
    refine lt_of_le_of_ne hp_im_le (fun h => hp_ne_m ?_)
    exact Complex.ext (by rw [hpV.1, hm_re]) h
  let z0 : ℂ := (m + p) / 2
  have hz0_re : z0.re = 0 := by
    simp only [z0, Complex.add_re, Complex.div_ofNat_re]
    rw [hm_re, hpV.1]; ring
  have hz0_im : z0.im = (m.im + p.im) / 2 := by
    simp only [z0, Complex.add_im, Complex.div_ofNat_im]
  have hz0_lt_m : z0.im < m.im := by rw [hz0_im]; linarith [hp_im_lt]
  have hz0_gt_p : p.im < z0.im := by rw [hz0_im]; linarith [hp_im_lt]
  have hm_im_gt : (-2:ℝ) < m.im := by
    refine lt_of_le_of_ne hmV.2.1 (fun h => ?_)
    have hmBd : m ∈ RectBd := Or.inr (Or.inr (Or.inr h.symm))
    rcases hKBd m (hPsubK hmP) hmBd with h1 | h1
    · exact hm_ne1 h1
    · exact hm_nem1 h1
  have hz0_im_lo : (-2:ℝ) < z0.im := by rw [hz0_im]; linarith [hm_im_gt, hpV.2.1]
  have hz0_im_hi : z0.im < 2 := by rw [hz0_im]; linarith [hp_im_lt, hp_im_le, hmV.2.2]
  have hz0_int : z0 ∈ interior Rect :=
    Rect_open_inside ⟨⟨by rw [hz0_re]; norm_num, by rw [hz0_re]; norm_num⟩,
      ⟨hz0_im_lo, hz0_im_hi⟩⟩
  have hzS : z0 ∈ Set.range (segPath Spt m) := by
    obtain ⟨up, hup⟩ := hpS
    refine ⟨⟨(1 + (up:ℝ)) / 2, ⟨by linarith [up.2.1], by linarith [up.2.2]⟩⟩, ?_⟩
    have hup' : p = (1 - (up:ℝ)) * Spt + (up:ℝ) * m := by rw [← hup, segPath_apply]
    rw [segPath_apply]
    simp only [z0]
    rw [hup']
    push_cast
    ring
  have hz0_notK : z0 ∉ Set.range γ := by
    intro hz
    have hzV : z0 ∈ VSeg := ⟨hz0_re, ⟨le_of_lt hz0_im_lo, le_of_lt hz0_im_hi⟩⟩
    have hz2 : z0 ∈ Set.range P ∪ Set.range Q := by rw [hPQrange]; exact hz
    rcases hz2 with hzP | hzQ
    · have hle := isMinOn_iff.mp hmmin z0 ⟨hzP, hzV⟩
      linarith [hz0_lt_m]
    · have hle := isMaxOn_iff.mp hpmax z0 ⟨hzQ, hzS⟩
      linarith [hz0_gt_p]
  have hseg_z0m : Set.range (segPath z0 m) ⊆ Set.range (segPath Spt m) := by
    rintro w ⟨v, rfl⟩
    obtain ⟨u0, hu0⟩ : ∃ u0 : I, segPath Spt m u0 = z0 := hzS
    refine ⟨⟨(1 - (v:ℝ)) * (u0:ℝ) + (v:ℝ), ⟨?_, ?_⟩⟩, ?_⟩
    · nlinarith [u0.2.1, u0.2.2, v.2.1, v.2.2]
    · nlinarith [u0.2.1, u0.2.2, v.2.1, v.2.2]
    · show segPath Spt m _ = segPath z0 m v
      rw [segPath_apply, segPath_apply]
      rw [show z0 = (1 - (u0:ℝ)) * Spt + (u0:ℝ) * m from by rw [← hu0, segPath_apply]]
      push_cast
      ring
  have hLset_K : ∀ z ∈ Lset, z ∉ Set.range γ := by
    intro z hzL hzK
    rcases hKBd z hzK (Lset_subset_RectBd hzL) with h | h
    · exact Lset_ne_one z hzL h
    · exact Lset_ne_neg_one z hzL h
  have hUset_K : ∀ z ∈ Uset, z ∉ Set.range γ := by
    intro z hzU hzK
    rcases hKBd z hzK (Uset_subset_RectBd hzU) with h | h
    · exact Uset_ne_one z hzU h
    · exact Uset_ne_neg_one z hzU h
  have hKc_open : IsOpen (Set.range γ)ᶜ := (isCompact_range γ.continuous).isClosed.isOpen_compl
  refine ⟨z0, hz0_notK, ?_⟩
  by_contra hbdd
  have hUopen : IsOpen (connectedComponentIn (Set.range γ)ᶜ z0) := hKc_open.connectedComponentIn
  have hUconn : IsConnected (connectedComponentIn (Set.range γ)ᶜ z0) :=
    ⟨⟨z0, mem_connectedComponentIn hz0_notK⟩, isPreconnected_connectedComponentIn⟩
  have hUpc : IsPathConnected (connectedComponentIn (Set.range γ)ᶜ z0) :=
    (hUopen.isConnected_iff_isPathConnected).mp hUconn
  obtain ⟨y, hyU, hyRect⟩ : ∃ y ∈ connectedComponentIn (Set.range γ)ᶜ z0, y ∉ Rect := by
    by_contra hc
    push Not at hc
    exact hbdd (Metric.isBounded_closedBall.subset
      (fun z hz => mem_closedBall_three_of_mem_Rect (hc z hz)))
  obtain ⟨sgg, hsggmem⟩ : ∃ sg1 : Path z0 y, Set.range sg1 ⊆ connectedComponentIn (Set.range γ)ᶜ z0 := by
    have hjo := hUpc.joinedIn z0 (mem_connectedComponentIn hz0_notK) y hyU
    exact ⟨hjo.somePath, Set.range_subset_iff.mpr hjo.somePath_mem⟩
  have hsggKc : ∀ t, sgg t ∈ (Set.range γ)ᶜ := fun t =>
    connectedComponentIn_subset _ _ (hsggmem ⟨t, rfl⟩)
  have hsgg0 : sgg (0 : I) = z0 := sgg.source
  set A : Set I := sgg ⁻¹' Rect with hAdef
  have hAclosed : IsClosed A := Rect_closed.preimage sgg.continuous
  set B : Set I := {t : I | ∀ s : I, s ≤ t → s ∈ A} with hBdef
  have hBclosed : IsClosed B := by
    refine isOpen_compl_iff.mp ?_
    rw [isOpen_iff_mem_nhds]
    intro t ht
    have ht' : ¬ (∀ s : I, s ≤ t → s ∈ A) := by simpa [hBdef] using ht
    rw [not_forall] at ht'
    obtain ⟨s, hs⟩ := ht'
    rw [Classical.not_imp] at hs
    obtain ⟨hst, hsA⟩ := hs
    rcases lt_or_eq_of_le hst with hlt | heq
    · refine mem_of_superset ((isOpen_lt continuous_const continuous_id).mem_nhds hlt) ?_
      intro t' ht''
      rw [hBdef, Set.mem_compl_iff, Set.mem_setOf_eq]
      intro hcon
      exact hsA (hcon s (le_of_lt ht''))
    · subst heq
      refine mem_of_superset (hAclosed.isOpen_compl.mem_nhds hsA) ?_
      intro t' ht''
      rw [hBdef, Set.mem_compl_iff, Set.mem_setOf_eq]
      intro hcon
      exact ht'' (hcon t' le_rfl)
  have hA0 : (0 : I) ∈ A := by
    rw [hAdef, Set.mem_preimage, Path.source]
    exact interior_subset hz0_int
  have hA1 : (1 : I) ∉ A := by
    rw [hAdef, Set.mem_preimage, Path.target]
    exact hyRect
  have hBne : B.Nonempty := ⟨0, by
    intro s hs
    have hs0 : s = 0 := Subtype.ext (le_antisymm (Subtype.coe_le_coe.mpr hs) s.2.1)
    rwa [hs0]⟩
  obtain ⟨u, huAR, humax⟩ := (hBclosed.isCompact.image continuous_subtype_val).exists_isMaxOn
    (hBne.image _) continuous_id.continuousOn
  obtain ⟨ua, huaB, hua_val⟩ := huAR
  have huI : u ∈ Set.Icc (0:ℝ) 1 := hua_val ▸ ua.2
  have huB : (⟨u, huI⟩ : I) ∈ B := by
    have : (⟨u, huI⟩ : I) = ua := Subtype.ext hua_val.symm
    rw [this]; exact huaB
  have huA : (⟨u, huI⟩ : I) ∈ A := huB ⟨u, huI⟩ (le_refl _)
  have h1B : (1 : I) ∉ B := by
    intro h1B
    exact hA1 (h1B 1 le_rfl)
  have hu_lt_one : u < 1 := by
    refine lt_of_le_of_ne huI.2 (fun h => h1B ?_)
    have h2 : (⟨u, huI⟩ : I) = 1 := Subtype.ext h
    rwa [h2] at huB
  have huwRect : sgg ⟨u, huI⟩ ∈ Rect := huA
  have huw_not_int : sgg ⟨u, huI⟩ ∉ interior Rect := by
    intro hint
    have hnhds : sgg ⁻¹' interior Rect ∈ 𝓝 (⟨u, huI⟩ : I) :=
      sgg.continuous.continuousAt (isOpen_interior.mem_nhds hint)
    obtain ⟨ε, hε, hεball⟩ := Metric.mem_nhds_iff.mp hnhds
    obtain ⟨t, hut, htI, htε⟩ : ∃ t : ℝ, u < t ∧ t ∈ Set.Icc (0:ℝ) 1 ∧ t < u + ε := by
      refine ⟨min ((u + 1) / 2) (u + ε / 2), ?_, ?_, ?_⟩
      · exact lt_min (by linarith) (by linarith)
      · refine ⟨?_, le_trans (min_le_left _ _) (by linarith)⟩
        linarith [huI.1, lt_min (show u < (u+1)/2 by linarith) (show u < u + ε/2 by linarith)]
      · exact lt_of_le_of_lt (min_le_right _ _) (by linarith)
    have htdist : (⟨t, htI⟩ : I) ∈ Metric.ball (⟨u, huI⟩ : I) ε := by
      rw [Metric.mem_ball, Subtype.dist_eq, Real.dist_eq, abs_lt]
      exact ⟨by linarith, by linarith⟩
    have htA : (⟨t, htI⟩ : I) ∈ A := by
      rw [hAdef, Set.mem_preimage]
      exact interior_subset (hεball htdist)
    have htB : (⟨t, htI⟩ : I) ∈ B := by
      intro s hs
      by_cases hsu : (s:ℝ) ≤ u
      · exact huB s (Subtype.coe_le_coe.mp hsu)
      · push Not at hsu
        rw [hAdef, Set.mem_preimage]
        refine interior_subset (hεball ?_)
        rw [Metric.mem_ball, Subtype.dist_eq, Real.dist_eq, abs_lt]
        have hsle : (s:ℝ) ≤ t := Subtype.coe_le_coe.mpr hs
        constructor <;> linarith
    have htAR : t ∈ Subtype.val '' B := ⟨⟨t, htI⟩, htB, rfl⟩
    have := isMaxOn_iff.mp humax t htAR
    simp only [id_eq] at this
    linarith
  have huwBd : sgg ⟨u, huI⟩ ∈ RectBd :=
    frontier_Rect_subset ((mem_frontier_iff_notMem_interior huwRect).mpr huw_not_int)
  have huw_ne1 : sgg ⟨u, huI⟩ ≠ 1 := fun h => hsggKc _ (h ▸ h1)
  have huw_nem1 : sgg ⟨u, huI⟩ ≠ -1 := fun h => hsggKc _ (h ▸ hm1)
  have huwLU : sgg ⟨u, huI⟩ ∈ Lset ∪ Uset := by
    rcases Rect_inter_RectBd_subset ⟨huwRect, huwBd⟩ with h | h
    · exact h
    · simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at h
      rcases h with h | h
      · exact absurd h huw_ne1
      · exact absurd h huw_nem1
  have hτrect : Set.range (sgg.subpath 0 ⟨u, huI⟩) ⊆ Rect := by
    intro z hz
    rw [Path.range_subpath_of_le sgg (0:I) ⟨u, huI⟩ huI.1] at hz
    obtain ⟨θ, hθ, rfl⟩ := hz
    exact huB θ hθ.2
  have hτsub : Set.range (sgg.subpath 0 ⟨u, huI⟩) ⊆ Set.range sgg := by
    rw [Path.range_subpath]
    exact Set.image_subset_range _ _
  have hτKc : ∀ z ∈ Set.range (sgg.subpath 0 ⟨u, huI⟩), z ∈ (Set.range γ)ᶜ := by
    intro z hz
    obtain ⟨θ, hθ⟩ := hτsub hz
    rw [← hθ]; exact hsggKc θ
  have hseg_Q' : ∀ z, z ∈ Set.range (segPath z0 m) → z ∈ Set.range Q → False := by
    intro z hz hzQ
    obtain ⟨v, rfl⟩ := hz
    have hle : (segPath z0 m v).im ≤ p.im := isMaxOn_iff.mp hpmax _ ⟨hzQ, hseg_z0m ⟨v, rfl⟩⟩
    rw [segPath_im] at hle
    have hkey : (0:ℝ) ≤ (v:ℝ) * (m.im - z0.im) := mul_nonneg v.2.1 (by linarith [hz0_lt_m])
    nlinarith [hkey, hle, hz0_gt_p]
  rcases huwLU with hwL | hwU
  · obtain ⟨δ, hδ⟩ : ∃ δ : Path Spt (sgg ⟨u, huI⟩), Set.range δ ⊆ Lset := by
      have hjo := isPathConnected_Lset.joinedIn Spt Spt_mem_Lset _ hwL
      exact ⟨hjo.somePath, Set.range_subset_iff.mpr hjo.somePath_mem⟩
    let vL : Path Spt Npt := δ.trans ((((sgg.subpath 0 ⟨u, huI⟩).symm).cast rfl hsgg0.symm).trans
      ((segPath z0 m).trans (arc.trans (segPath l Npt))))
    have hvrange : Set.range vL ⊆ Rect := by
      intro z hz
      have hz' : z ∈ Set.range δ ∪ (Set.range (sgg.subpath 0 ⟨u, huI⟩) ∪
          (Set.range (segPath z0 m) ∪ (Set.range arc ∪ Set.range (segPath l Npt)))) := by
        simpa [vL, Path.trans_range, Path.symm_range, Path.cast_range] using hz
      rcases hz' with h | h | h | h | h
      · exact Lset_subset_Rect (hδ h)
      · exact hτrect h
      · obtain ⟨θ, rfl⟩ := h
        exact segPath_mem_Rect (interior_subset hz0_int) (VSeg_subset_Rect hmV) θ
      · exact harc_rect h
      · exact hseg_lN h
    have hav : ∀ z, z ∈ Set.range vL → z ∈ Set.range Q → False := by
      intro z hz hzQ
      have hz' : z ∈ Set.range δ ∪ (Set.range (sgg.subpath 0 ⟨u, huI⟩) ∪
          (Set.range (segPath z0 m) ∪ (Set.range arc ∪ Set.range (segPath l Npt)))) := by
        simpa [vL, Path.trans_range, Path.symm_range, Path.cast_range] using hz
      rcases hz' with h | h | h | h | h
      · exact hLset_K z (hδ h) (hQsubK hzQ)
      · exact hτKc z h (hQsubK hzQ)
      · exact hseg_Q' z h hzQ
      · exact harc_Q z h hzQ
      · exact hseg_Q z h hzQ
    obtain ⟨s1, t1, hs1⟩ := cross_exists Q vL hQrect (fun t => hvrange ⟨t, rfl⟩)
    exact hav _ ⟨t1, rfl⟩ ⟨s1, hs1⟩
  · obtain ⟨δ, hδ⟩ : ∃ δ : Path (sgg ⟨u, huI⟩) Npt, Set.range δ ⊆ Uset := by
      have hjo := isPathConnected_Uset.joinedIn _ hwU Npt Npt_mem_Uset
      exact ⟨hjo.somePath, Set.range_subset_iff.mpr hjo.somePath_mem⟩
    have hδKc : ∀ z ∈ Set.range δ, z ∈ (Set.range γ)ᶜ := fun z hz => hUset_K z (hδ hz)
    have hseg_P : ∀ z, z ∈ Set.range (segPath Spt z0) → z ∈ Set.range P → False := by
      intro z hz hzP
      obtain ⟨v, rfl⟩ := hz
      have hzV : segPath Spt z0 v ∈ VSeg :=
        segPath_mem_VSeg Spt_mem_VSeg ⟨hz0_re, ⟨le_of_lt hz0_im_lo, le_of_lt hz0_im_hi⟩⟩ v
      have hle := isMinOn_iff.mp hmmin _ ⟨hzP, hzV⟩
      have him : (segPath Spt z0 v).im ≤ z0.im := by
        rw [segPath_im, hSpt_im]
        nlinarith [hz0_im_lo, v.2.1, v.2.2]
      linarith [hz0_lt_m]
    let vU : Path Spt Npt := (segPath Spt z0).trans
      (((sgg.subpath 0 ⟨u, huI⟩).cast hsgg0.symm rfl).trans δ)
    have hvrange : Set.range vU ⊆ Rect := by
      intro z hz
      have hz' : z ∈ Set.range (segPath Spt z0) ∪ (Set.range (sgg.subpath 0 ⟨u, huI⟩)
          ∪ Set.range δ) := by
        simpa [vU, Path.trans_range, Path.cast_range] using hz
      rcases hz' with h | h | h
      · obtain ⟨θ, rfl⟩ := h
        exact segPath_mem_Rect Spt_mem_Rect (interior_subset hz0_int) θ
      · exact hτrect h
      · exact Uset_subset_Rect (hδ h)
    have hav : ∀ z, z ∈ Set.range vU → z ∈ Set.range P → False := by
      intro z hz hzP
      have hz' : z ∈ Set.range (segPath Spt z0) ∪ (Set.range (sgg.subpath 0 ⟨u, huI⟩)
          ∪ Set.range δ) := by
        simpa [vU, Path.trans_range, Path.cast_range] using hz
      rcases hz' with h | h | h
      · exact hseg_P z h hzP
      · exact hτKc z h (hPsubK hzP)
      · exact hδKc z h (hPsubK hzP)
    obtain ⟨s1, t1, hs1⟩ := cross_exists P vU hPrect (fun t => hvrange ⟨t, rfl⟩)
    exact hav _ ⟨t1, rfl⟩ ⟨s1, hs1⟩

end

end Commons.Topology.Jordan