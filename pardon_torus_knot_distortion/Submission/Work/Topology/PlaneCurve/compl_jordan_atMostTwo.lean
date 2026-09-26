import Mathlib
import Submission.Work.Smooth.SphereJordan.brouwer_disc
import Submission.Work.Topology.PlaneCurve.plane_crossing_lemma
import Submission.Work.Topology.PlaneCurve.jordanRectSetup
import Submission.Work.Topology.PlaneCurve.frontier_component_eq_range
import Submission.Work.Smooth.SphereJordan.range_eq_of_subset_of_periodic

/-!
# At most two components of the complement of a simple closed plane curve

The main result of this file is `Work.Topology.PlaneCurve.compl_jordan_atMostTwo`: for a
continuous `2π`-periodic curve `γ : ℝ → ℂ` which is injective on one period `[0, 2π)`, of any
three points of `ℂ` outside the trace of `γ`, two lie in the same connected component of the
complement of the trace.

The proof follows Maehara's elementary proof of the Jordan curve theorem (R. Maehara, *The Jordan
curve theorem via the Brouwer fixed point theorem*, Amer. Math. Monthly **91** (1984), 637-646):
after rescaling so that the two points of the trace at maximal distance are `±1`, the trace lies in
the rectangle `(-1,1) × (-2,2)` with the crossing lemma providing a "window" on the vertical
crosscut; a bottom–top path crosses the box through that window, so that any component of the
complement other than the window's component and the unbounded one allows a left–right path
avoiding that bottom–top path, contradicting the crossing lemma
(`Work.Topology.PlaneCurve.plane_crossing_lemma`), and, finally,
`Work.Topology.PlaneCurve.frontier_component_eq_range` (Maehara's Lemma 1) is used to reach the
points `±1`.
-/

namespace Work.Topology.PlaneCurve

set_option maxHeartbeats 4000000

open Set Metric

noncomputable section


/-! ## Elementary helpers -/

/-- The complement of the closed box, described by the four half-planes removed by it. -/
theorem compl_closedBox_eq :
    (closedBox : Set ℂ)ᶜ = {z : ℂ | 1 < z.re ∨ z.re < -1 ∨ 2 < z.im ∨ z.im < -2} := by
  ext z
  simp only [Set.mem_compl_iff, closedBox, Set.mem_setOf_eq]
  constructor
  · intro h
    rcases le_or_gt z.re 1 with h1 | h1
    · rcases le_or_gt (-1) z.re with h2 | h2
      · rcases le_or_gt z.im 2 with h3 | h3
        · rcases le_or_gt (-2) z.im with h4 | h4
          · exact absurd ⟨abs_le.mpr ⟨h2, h1⟩, abs_le.mpr ⟨h4, h3⟩⟩ h
          · exact Or.inr (Or.inr (Or.inr (by linarith)))
        · exact Or.inr (Or.inr (Or.inl (by linarith)))
      · exact Or.inr (Or.inl (by linarith))
    · exact Or.inl (by linarith)
  · rintro (h | h | h | h) ⟨h1, h2⟩
    · linarith [abs_le.mp h1]
    · linarith [abs_le.mp h1]
    · linarith [abs_le.mp h2]
    · linarith [abs_le.mp h2]

/-- The open half-plane `{z : ℂ | c < z.re}` is preconnected. -/
theorem isPreconnected_re_gt (c : ℝ) : IsPreconnected {z : ℂ | c < z.re} := by
  have h := (isPreconnected_Ioi (a := c)).prod (isPreconnected_univ (α := ℝ))
  have h2 := h.image (fun p : ℝ × ℝ => (p.1 : ℂ) + (p.2 : ℂ) * Complex.I) (by fun_prop)
  rw [show {z : ℂ | c < z.re}
      = (fun p : ℝ × ℝ => (p.1 : ℂ) + (p.2 : ℂ) * Complex.I) '' (Ioi c ×ˢ univ) from ?_]
  exact h2
  ext z
  constructor
  · intro hz
    exact ⟨(z.re, z.im), ⟨hz, trivial⟩, by simp⟩
  · rintro ⟨⟨x, y⟩, ⟨hx, -⟩, rfl⟩
    show c < ((x : ℂ) + (y : ℂ) * Complex.I).re
    simpa using hx

/-- The open half-plane `{z : ℂ | c < z.im}` is preconnected. -/
theorem isPreconnected_im_gt (c : ℝ) : IsPreconnected {z : ℂ | c < z.im} := by
  have h := (isPreconnected_Ioi (a := c)).prod (isPreconnected_univ (α := ℝ))
  have h2 := h.image (fun p : ℝ × ℝ => (p.2 : ℂ) + (p.1 : ℂ) * Complex.I) (by fun_prop)
  rw [show {z : ℂ | c < z.im}
      = (fun p : ℝ × ℝ => (p.2 : ℂ) + (p.1 : ℂ) * Complex.I) '' (Ioi c ×ˢ univ) from ?_]
  exact h2
  ext z
  constructor
  · intro hz
    exact ⟨(z.im, z.re), ⟨hz, trivial⟩, by simp⟩
  · rintro ⟨⟨x, y⟩, ⟨hx, -⟩, rfl⟩
    show c < ((y : ℂ) + (x : ℂ) * Complex.I).im
    simpa using hx

/-- The open half-plane `{z : ℂ | z.re < c}` is preconnected. -/
theorem isPreconnected_re_lt (c : ℝ) : IsPreconnected {z : ℂ | z.re < c} := by
  have h := (isPreconnected_Iio (a := c)).prod (isPreconnected_univ (α := ℝ))
  have h2 := h.image (fun p : ℝ × ℝ => (p.1 : ℂ) + (p.2 : ℂ) * Complex.I) (by fun_prop)
  rw [show {z : ℂ | z.re < c}
      = (fun p : ℝ × ℝ => (p.1 : ℂ) + (p.2 : ℂ) * Complex.I) '' (Iio c ×ˢ univ) from ?_]
  exact h2
  ext z
  constructor
  · intro hz
    exact ⟨(z.re, z.im), ⟨hz, trivial⟩, by simp⟩
  · rintro ⟨⟨x, y⟩, ⟨hx, -⟩, rfl⟩
    show ((x : ℂ) + (y : ℂ) * Complex.I).re < c
    simpa using hx

/-- The open half-plane `{z : ℂ | z.im < c}` is preconnected. -/
theorem isPreconnected_im_lt (c : ℝ) : IsPreconnected {z : ℂ | z.im < c} := by
  have h := (isPreconnected_Iio (a := c)).prod (isPreconnected_univ (α := ℝ))
  have h2 := h.image (fun p : ℝ × ℝ => (p.2 : ℂ) + (p.1 : ℂ) * Complex.I) (by fun_prop)
  rw [show {z : ℂ | z.im < c}
      = (fun p : ℝ × ℝ => (p.2 : ℂ) + (p.1 : ℂ) * Complex.I) '' (Iio c ×ˢ univ) from ?_]
  exact h2
  ext z
  constructor
  · intro hz
    exact ⟨(z.im, z.re), ⟨hz, trivial⟩, by simp⟩
  · rintro ⟨⟨x, y⟩, ⟨hx, -⟩, rfl⟩
    show ((y : ℂ) + (x : ℂ) * Complex.I).im < c
    simpa using hx

/-- The complement of the closed box is preconnected. -/
theorem isPreconnected_compl_closedBox : IsPreconnected ((closedBox : Set ℂ)ᶜ) := by
  have hcs : ((closedBox : Set ℂ)ᶜ)
      = ((({z : ℂ | 1 < z.re} ∪ {z : ℂ | 2 < z.im}) ∪ {z : ℂ | z.re < -1})
        ∪ {z : ℂ | z.im < -2}) := by
    rw [compl_closedBox_eq]
    ext z
    simp only [Set.mem_setOf_eq, Set.mem_union]
    tauto
  rw [hcs]
  have h12 : IsPreconnected ({z : ℂ | 1 < z.re} ∪ {z : ℂ | 2 < z.im}) :=
    IsPreconnected.union (2 + 3 * Complex.I)
      (by norm_num [Complex.add_re, Complex.mul_re])
      (by norm_num [Complex.add_re, Complex.mul_re])
      (isPreconnected_re_gt 1) (isPreconnected_im_gt 2)
  have h123 : IsPreconnected (({z : ℂ | 1 < z.re} ∪ {z : ℂ | 2 < z.im}) ∪ {z : ℂ | z.re < -1}) :=
    IsPreconnected.union (-2 + 3 * Complex.I)
      (by norm_num [Complex.add_re, Complex.mul_re])
      (by norm_num [Complex.add_re, Complex.mul_re])
      h12 (isPreconnected_re_lt (-1))
  exact IsPreconnected.union (2 - 3 * Complex.I)
    (by norm_num [Complex.add_re, Complex.mul_re])
    (by norm_num [Complex.add_re, Complex.mul_re])
    h123 (isPreconnected_im_lt (-2))

/-- Concatenation of two paths (given as maps on `ℝ`): `f` continued by `g`, starting at the point
where `f` reaches level `n`. -/
def concat (n : ℝ) (f g : ℝ → ℂ) : ℝ → ℂ := fun t => if t ≤ n then f t else g (t - n)

theorem continuous_concat {n : ℝ} {f g : ℝ → ℂ} (hf : Continuous f) (hg : Continuous g)
    (h : f n = g 0) : Continuous (concat n f g) := by
  refine Continuous.if ?_ (hf.comp (by fun_prop)) (hg.comp (by fun_prop))
  intro t ht
  have h1 : t ∈ frontier (Iic n) := ht
  rw [frontier_Iic] at h1
  subst h1
  simpa [concat] using h

theorem concat_of_le {n t : ℝ} {f g : ℝ → ℂ} (h : t ≤ n) : concat n f g t = f t := by
  simp [concat, h]

theorem concat_of_not_le {n t : ℝ} {f g : ℝ → ℂ} (h : ¬ t ≤ n) : concat n f g t = g (t - n) := by
  simp [concat, h]

theorem range_concat_subset {n : ℝ} (f g : ℝ → ℂ) :
    Set.range (concat n f g) ⊆ Set.range f ∪ Set.range g := by
  rintro w ⟨t, rfl⟩
  by_cases h : t ≤ n
  · exact Or.inl ⟨t, (concat_of_le h).symm⟩
  · exact Or.inr ⟨t - n, (concat_of_not_le h).symm⟩


/-- The closed box is convex. -/
theorem convex_closedBox : Convex ℝ closedBox := by
  intro x hx y hy a b ha hb hab
  obtain ⟨hx1, hx2⟩ := hx
  obtain ⟨hy1, hy2⟩ := hy
  refine ⟨?_, ?_⟩
  · have h1 : (a • x + b • y).re = a * x.re + b * y.re := by
      rw [Complex.add_re, Complex.smul_re, Complex.smul_re]; rfl
    rw [h1, abs_le]
    constructor <;> nlinarith [abs_le.mp hx1, abs_le.mp hy1, ha, hb, hab]
  · have h1 : (a • x + b • y).im = a * x.im + b * y.im := by
      rw [Complex.add_im, Complex.smul_im, Complex.smul_im]; rfl
    rw [h1, abs_le]
    constructor <;> nlinarith [abs_le.mp hx2, abs_le.mp hy2, ha, hb, hab]

/-- The vertical segment is contained in the closed box. -/
theorem vSeg_subset_closedBox : vSeg ⊆ closedBox := by
  intro z hz
  exact ⟨by rw [hz.1]; norm_num, abs_le.mpr ⟨hz.2.1, hz.2.2⟩⟩

/-- The vertical segment is closed. -/
theorem isClosed_vSeg : IsClosed vSeg := by
  have h1 : IsClosed {z : ℂ | z.re = 0} := isClosed_eq Complex.continuous_re continuous_const
  have h2 : IsClosed {z : ℂ | -2 ≤ z.im} := isClosed_le continuous_const Complex.continuous_im
  have h3 : IsClosed {z : ℂ | z.im ≤ 2} := isClosed_le Complex.continuous_im continuous_const
  have hset : vSeg = {z : ℂ | z.re = 0} ∩ {z : ℂ | -2 ≤ z.im} ∩ {z : ℂ | z.im ≤ 2} := by
    ext z
    simp [vSeg, and_assoc]
  rw [hset]
  exact (h1.inter h2).inter h3

/-- **Maehara's argument, in the normalised situation.**  `γ` is a Jordan curve whose trace lies in
`rectR ∪ {-1, 1}` and contains `±1`; then the complement of the trace has at most two connected
components. -/
theorem atMostTwo_of_rectSetup {γ : ℝ → ℂ} (hcont : Continuous γ)
    (hper : Function.Periodic γ (2 * Real.pi)) (hinj : Set.InjOn γ (Set.Ico 0 (2 * Real.pi)))
    (hsub : ∀ w ∈ Set.range γ, w ∈ rectR ∨ w = -1 ∨ w = 1)
    (hm1 : -1 ∈ Set.range γ) (h1 : 1 ∈ Set.range γ)
    (hdis : ¬ IsPreconnected (Set.range γ)ᶜ)
    (hfront : ∀ w : ℂ, w ∉ Set.range γ →
      frontier (connectedComponentIn (Set.range γ)ᶜ w) = Set.range γ)
    {x y z : ℂ} (hx : x ∉ Set.range γ) (hy : y ∉ Set.range γ) (hz : z ∉ Set.range γ) :
    connectedComponentIn (Set.range γ)ᶜ x = connectedComponentIn (Set.range γ)ᶜ y ∨
    connectedComponentIn (Set.range γ)ᶜ x = connectedComponentIn (Set.range γ)ᶜ z ∨
    connectedComponentIn (Set.range γ)ᶜ y = connectedComponentIn (Set.range γ)ᶜ z := by
  classical
  -- ## Step 0: replace `γ` by a shift with `γ 0 = -1`
  obtain ⟨s₀, hs₀⟩ := hm1
  set γ' : ℝ → ℂ := fun t => γ (t + s₀) with hγ'def
  have hcont' : Continuous γ' := hcont.comp (by fun_prop)
  have hper' : Function.Periodic γ' (2 * Real.pi) := by
    intro t
    show γ (t + 2 * Real.pi + s₀) = γ (t + s₀)
    rw [show t + 2 * Real.pi + s₀ = (t + s₀) + 2 * Real.pi by ring, hper]
  have hrange' : Set.range γ' = Set.range γ := by
    ext w; constructor
    · rintro ⟨t, rfl⟩; exact ⟨t + s₀, rfl⟩
    · rintro ⟨u, rfl⟩
      refine ⟨u - s₀, ?_⟩
      show γ (u - s₀ + s₀) = γ u
      rw [show u - s₀ + s₀ = u by ring]
  have hinj' : Set.InjOn γ' (Set.Ico 0 (2 * Real.pi)) := by
    intro u hu v hv huv
    obtain ⟨k, hk⟩ := Work.Smooth.SphereJordan.exists_int_sub_eq_of_periodic_injOn hper hinj huv
    have h1 : |u - v| < 2 * Real.pi := by
      rw [abs_lt]
      exact ⟨by linarith [hu.1, hv.2], by linarith [hu.2, hv.1]⟩
    have h2 : (k : ℝ) * (2 * Real.pi) = (u + s₀) - (v + s₀) := by linarith [hk]
    have hk0 : k = 0 := by
      by_contra hkne
      have h3 : (1 : ℝ) ≤ |(k : ℝ)| := by rw [← Int.cast_abs]; exact_mod_cast Int.one_le_abs hkne
      have h4 : 2 * Real.pi ≤ |(u + s₀) - (v + s₀)| := by
        rw [← h2, abs_mul, abs_of_pos (by positivity : (0 : ℝ) < 2 * Real.pi)]
        nlinarith [h3, Real.pi_pos]
      rw [show (u + s₀) - (v + s₀) = u - v by ring] at h4
      linarith
    rw [hk0] at h2
    simp only [Int.cast_zero, zero_mul] at h2
    linarith [h2]
  have hx' : x ∉ Set.range γ' := by rwa [hrange']
  have hy' : y ∉ Set.range γ' := by rwa [hrange']
  have hz' : z ∉ Set.range γ' := by rwa [hrange']
  have hsub' : ∀ w ∈ Set.range γ', w ∈ rectR ∨ w = -1 ∨ w = 1 := by
    intro w hw; rw [hrange'] at hw; exact hsub w hw
  have hone : 1 ∈ Set.range γ' := by rw [hrange']; exact h1
  have hm1' : (-1 : ℂ) ∈ Set.range γ' := ⟨0, by simp [hγ'def, hs₀]⟩
  have hfront' : ∀ w : ℂ, w ∉ Set.range γ' →
      frontier (connectedComponentIn (Set.range γ')ᶜ w) = Set.range γ' := by
    intro w hw; rw [hrange'] at hw ⊢; exact hfront w hw
  -- it suffices to treat `γ'`
  rw [← hrange']
  -- ## Step 1: basic facts
  have hJcompact : IsCompact (Set.range γ') := isCompact_range_of_periodic hcont' hper'
  have hJclosed : IsClosed (Set.range γ') := hJcompact.isClosed
  have hJsub : Set.range γ' ⊆ closedBox := range_subset_closedBox hsub'
  have h0' : γ' 0 = -1 := by simp [hγ'def, hs₀]
  have hπ : (0 : ℝ) < 2 * Real.pi := by positivity
  -- ## Step 2: the unbounded component `Uinf`
  set Uinf : Set ℂ := connectedComponentIn (Set.range γ')ᶜ (3 * Complex.I) with hUinfdef
  have h3Ire : (3 * Complex.I : ℂ).re = 0 := by simp
  have h3Iim : (3 * Complex.I : ℂ).im = 3 := by simp
  have hm3Ire : (-3 * Complex.I : ℂ).re = 0 := by simp
  have hm3Iim : (-3 * Complex.I : ℂ).im = -3 := by simp
  have h3Iout : (3 * Complex.I : ℂ) ∈ ((closedBox : Set ℂ)ᶜ) := by
    rw [compl_closedBox_eq]
    exact Or.inr (Or.inr (Or.inl (by rw [h3Iim]; norm_num)))
  have hm3Iout : (-3 * Complex.I : ℂ) ∈ ((closedBox : Set ℂ)ᶜ) := by
    rw [compl_closedBox_eq]
    exact Or.inr (Or.inr (Or.inr (by rw [hm3Iim]; norm_num)))
  have houtUinf : ((closedBox : Set ℂ)ᶜ) ⊆ Uinf := by
    have hsubJ : ((closedBox : Set ℂ)ᶜ) ⊆ (Set.range γ')ᶜ := by
      intro w hw hwJ; exact hw (hJsub hwJ)
    have h := isPreconnected_compl_closedBox.subset_connectedComponentIn
      (F := (Set.range γ')ᶜ) (x := 3 * Complex.I) h3Iout hsubJ
    rwa [← hUinfdef] at h
  have hUinf_eq : connectedComponentIn (Set.range γ')ᶜ (-3 * Complex.I) = Uinf := by
    have h1 : (-3 * Complex.I : ℂ) ∈ connectedComponentIn (Set.range γ')ᶜ (3 * Complex.I) := by
      have := houtUinf hm3Iout
      rwa [hUinfdef] at this
    rw [← connectedComponentIn_eq h1, ← hUinfdef]
  -- ## Step 3: the crosscut `vSeg`, its intersection with the trace, and the outer pieces
  have hKne : (Set.range γ' ∩ vSeg).Nonempty := vSeg_meet hcont' hsub' hm1' hone
  have hKcompact : IsCompact (Set.range γ' ∩ vSeg) := hJcompact.inter_right isClosed_vSeg
  obtain ⟨l, hlK, hlmax⟩ := hKcompact.exists_isMaxOn hKne
    (Complex.continuous_im.continuousOn : ContinuousOn (fun z : ℂ => z.im) _)
  obtain ⟨q, hqK, hqmin⟩ := hKcompact.exists_isMinOn hKne
    (Complex.continuous_im.continuousOn : ContinuousOn (fun z : ℂ => z.im) _)
  have hlJ : l ∈ Set.range γ' := hlK.1
  have hqJ : q ∈ Set.range γ' := hqK.1
  have hlSeg : l ∈ vSeg := hlK.2
  have hqSeg : q ∈ vSeg := hqK.2
  have hlBox : l ∈ closedBox := hJsub hlJ
  have hqBox : q ∈ closedBox := hJsub hqJ
  have hlim2 : |l.im| ≤ 2 := hlBox.2
  have hqim2 : |q.im| ≤ 2 := hqBox.2
  have hlim_le : l.im ≤ 2 := by linarith [abs_le.mp hlim2]
  have hqim_ge : -2 ≤ q.im := by linarith [abs_le.mp hqim2]
  -- vertical rays
  have hray_top : {z : ℂ | z.re = 0 ∧ l.im < z.im}
      = (fun t : ℝ => (t : ℂ) * Complex.I) '' (Set.Ioi l.im) := by
    ext z
    constructor
    · rintro ⟨hre, him⟩
      exact ⟨z.im, by simpa using him,
        by apply Complex.ext <;> simp [hre]⟩
    · rintro ⟨t, ht, rfl⟩
      exact ⟨by simp, by simpa using ht⟩
  have hray_bot : {z : ℂ | z.re = 0 ∧ z.im < q.im}
      = (fun t : ℝ => (t : ℂ) * Complex.I) '' (Set.Iio q.im) := by
    ext z
    constructor
    · rintro ⟨hre, him⟩
      exact ⟨z.im, by simpa using him,
        by apply Complex.ext <;> simp [hre]⟩
    · rintro ⟨t, ht, rfl⟩
      exact ⟨by simp, by simpa using ht⟩
  -- the top piece
  have htopPre : IsPreconnected ({z : ℂ | z.re = 0 ∧ l.im < z.im} ∪ ((closedBox : Set ℂ)ᶜ)) := by
    have h1 : IsPreconnected {z : ℂ | z.re = 0 ∧ l.im < z.im} := by
      rw [hray_top]
      exact (isPreconnected_Ioi (a := l.im)).image _ (by fun_prop)
    have h3Iin : (3 * Complex.I : ℂ) ∈ {z : ℂ | z.re = 0 ∧ l.im < z.im} :=
      ⟨h3Ire, by rw [h3Iim]; linarith⟩
    exact IsPreconnected.union (3 * Complex.I) h3Iin h3Iout h1 isPreconnected_compl_closedBox
  have htopUinf : ({z : ℂ | z.re = 0 ∧ l.im < z.im} ∪ ((closedBox : Set ℂ)ᶜ)) ⊆ Uinf := by
    have h3Iin : (3 * Complex.I : ℂ) ∈ {z : ℂ | z.re = 0 ∧ l.im < z.im} :=
      ⟨h3Ire, by rw [h3Iim]; linarith⟩
    have hfree : ∀ w ∈ ({z : ℂ | z.re = 0 ∧ l.im < z.im} ∪ ((closedBox : Set ℂ)ᶜ)),
        w ∉ Set.range γ' := by
      rintro w (⟨hwr, hwi⟩ | hw) hwJ
      · have hwBox : w ∈ closedBox := hJsub hwJ
        have hwim : |w.im| ≤ 2 := hwBox.2
        have hseg : w ∈ vSeg := ⟨hwr, by linarith [abs_le.mp hwim], by linarith [abs_le.mp hwim]⟩
        have hle : w.im ≤ l.im := hlmax ⟨hwJ, hseg⟩
        linarith
      · exact hw (hJsub hwJ)
    have h := htopPre.subset_connectedComponentIn (F := (Set.range γ')ᶜ) (x := 3 * Complex.I)
      (Or.inl h3Iin) hfree
    rwa [← hUinfdef] at h
  -- the bottom piece
  have hbotPre : IsPreconnected ({z : ℂ | z.re = 0 ∧ z.im < q.im} ∪ ((closedBox : Set ℂ)ᶜ)) := by
    have h1 : IsPreconnected {z : ℂ | z.re = 0 ∧ z.im < q.im} := by
      rw [hray_bot]
      exact (isPreconnected_Iio (a := q.im)).image _ (by fun_prop)
    have hm3Iin : (-3 * Complex.I : ℂ) ∈ {z : ℂ | z.re = 0 ∧ z.im < q.im} :=
      ⟨hm3Ire, by rw [hm3Iim]; linarith⟩
    exact IsPreconnected.union (-3 * Complex.I) hm3Iin hm3Iout h1 isPreconnected_compl_closedBox
  have hbotUinf : ({z : ℂ | z.re = 0 ∧ z.im < q.im} ∪ ((closedBox : Set ℂ)ᶜ)) ⊆ Uinf := by
    have hm3Iin : (-3 * Complex.I : ℂ) ∈ {z : ℂ | z.re = 0 ∧ z.im < q.im} :=
      ⟨hm3Ire, by rw [hm3Iim]; linarith⟩
    have hfree : ∀ w ∈ ({z : ℂ | z.re = 0 ∧ z.im < q.im} ∪ ((closedBox : Set ℂ)ᶜ)),
        w ∉ Set.range γ' := by
      rintro w (⟨hwr, hwi⟩ | hw) hwJ
      · have hwBox : w ∈ closedBox := hJsub hwJ
        have hwim : |w.im| ≤ 2 := hwBox.2
        have hseg : w ∈ vSeg := ⟨hwr, by linarith [abs_le.mp hwim], by linarith [abs_le.mp hwim]⟩
        have hle : q.im ≤ w.im := hqmin ⟨hwJ, hseg⟩
        linarith
      · exact hw (hJsub hwJ)
    have h := hbotPre.subset_connectedComponentIn (F := (Set.range γ')ᶜ) (x := -3 * Complex.I)
      (Or.inl hm3Iin) hfree
    rwa [hUinf_eq] at h
  -- ## Step 4: the two arcs of the trace between `-1` and `1`
  obtain ⟨t₁, ht₁⟩ : ∃ t : ℝ, γ' t = 1 := hone
  obtain ⟨m₀, hm₀⟩ := exists_int_mul_add_mem_Ico hπ 0 t₁
  set θ : ℝ := t₁ + (m₀ : ℝ) * (2 * Real.pi) with hθdef
  have hγθ : γ' θ = 1 := by
    have h1 : γ' (t₁ + (m₀ : ℝ) * (2 * Real.pi)) = γ' t₁ := (hper'.int_mul m₀) t₁
    rw [hθdef]; exact h1.trans ht₁
  have hθIco : θ ∈ Set.Ico 0 (2 * Real.pi) := ⟨hm₀.1, by linarith [hm₀.2]⟩
  have hθpos : 0 < θ := by
    rcases lt_or_eq_of_le hθIco.1 with h | h
    · exact h
    · exfalso
      have h1 : γ' θ = -1 := by rw [← h]; exact h0'
      rw [hγθ] at h1
      norm_num at h1
  have hθlt : θ < 2 * Real.pi := hθIco.2
  have hγ2π : γ' (2 * Real.pi) = -1 := by
    have h := hper' 0
    simp only [zero_add] at h
    rw [h, h0']
  -- ## Step 4: the two arcs of the trace between `-1` and `1`
  set A : Set ℂ := γ' '' Set.Icc 0 θ with hAdef
  set B : Set ℂ := γ' '' Set.Icc θ (2 * Real.pi) with hBdef
  have hIcc_union : Set.Icc (0 : ℝ) θ ∪ Set.Icc θ (2 * Real.pi) = Set.Icc 0 (2 * Real.pi) := by
    ext t; constructor
    · rintro (⟨h1, h2⟩ | ⟨h1, h2⟩)
      · exact ⟨h1, le_trans h2 hθlt.le⟩
      · exact ⟨le_trans hθpos.le h1, h2⟩
    · rintro ⟨h1, h2⟩
      rcases le_or_gt t θ with h | h
      · exact Or.inl ⟨h1, h⟩
      · exact Or.inr ⟨le_of_lt h, h2⟩
  have hAB : A ∪ B = Set.range γ' := by
    have h1 : A ∪ B = γ' '' (Set.Icc 0 θ ∪ Set.Icc θ (2 * Real.pi)) := by
      rw [hAdef, hBdef, Set.image_union]
    rw [h1, hIcc_union, range_eq_image_Icc hper']
  have hAB_inter : A ∩ B ⊆ ({-1, 1} : Set ℂ) := by
    rintro w ⟨⟨u, hu, huw⟩, ⟨v, hv, hvw⟩⟩
    have huv : γ' u = γ' v := by rw [huw, hvw]
    obtain ⟨k, hk⟩ :=
      Work.Smooth.SphereJordan.exists_int_sub_eq_of_periodic_injOn hper' hinj' huv
    have hkv : (k : ℝ) * (2 * Real.pi) = u - v := by linarith [hk]
    have hk_le : k ≤ 0 := by
      by_contra hcon
      push_neg at hcon
      have hcon' : (0 : ℝ) < (k : ℝ) := by exact_mod_cast hcon
      have h1 : (0 : ℝ) * (2 * Real.pi) < (k : ℝ) * (2 * Real.pi) :=
        mul_lt_mul_of_pos_right hcon' (by positivity : (0 : ℝ) < 2 * Real.pi)
      have h2 : (k : ℝ) * (2 * Real.pi) ≤ 0 := by linarith [hu.2, hv.1, hkv]
      linarith
    have hk_ge : -1 ≤ k := by
      by_contra hcon
      push_neg at hcon
      have hcon' : (k : ℝ) < -1 := by exact_mod_cast hcon
      have h1 : (k : ℝ) * (2 * Real.pi) < (-1 : ℝ) * (2 * Real.pi) :=
        mul_lt_mul_of_pos_right hcon' (by positivity : (0 : ℝ) < 2 * Real.pi)
      have h2 : (-1 : ℝ) * (2 * Real.pi) ≤ (k : ℝ) * (2 * Real.pi) := by
        linarith [hu.1, hv.2, hkv]
      linarith
    have hk_cases : k = 0 ∨ k = -1 := by omega
    have hw : w = 1 ∨ w = -1 := by
      rcases hk_cases with h | h
      · left
        have hsub0 : u - v = 0 := by
          rw [h] at hkv; push_cast at hkv; linarith [hkv]
        have huv' : u = v := sub_eq_zero.mp hsub0
        have huθ : u = θ := le_antisymm hu.2 (by rw [huv']; exact hv.1)
        rw [← huw, huθ, hγθ]
      · right
        have hsub0 : u - v = -2 * Real.pi := by
          rw [h] at hkv; push_cast at hkv; linarith [hkv]
        have hv2 : v = 2 * Real.pi := le_antisymm hv.2 (by linarith [hu.1, hsub0])
        have hu0 : u = 0 := by linarith [hsub0, hv2]
        rw [← huw, hu0, h0']
    rcases hw with h | h <;> simp [h]
  -- ## Step 5: parameters on the period and the arcs `J₁`, `J₂`
  have exists_par : ∀ w ∈ Set.range γ', ∃ u ∈ Set.Ico 0 (2 * Real.pi), γ' u = w := by
    rintro w ⟨t, rfl⟩
    obtain ⟨k, hk⟩ := exists_int_mul_add_mem_Ico hπ 0 t
    exact ⟨t + (k : ℝ) * (2 * Real.pi), ⟨hk.1, by linarith [hk.2]⟩, (hper'.int_mul k) t⟩
  have par_unique : ∀ {u v : ℝ}, u ∈ Set.Ico 0 (2 * Real.pi) → v ∈ Set.Ico 0 (2 * Real.pi) →
      γ' u = γ' v → u = v := by
    intro u v hu hv huv
    obtain ⟨k, hk⟩ :=
      Work.Smooth.SphereJordan.exists_int_sub_eq_of_periodic_injOn hper' hinj' huv
    have h1 : |u - v| < 2 * Real.pi := by
      rw [abs_lt]; exact ⟨by linarith [hu.1, hv.2], by linarith [hu.2, hv.1]⟩
    have h2 : (k : ℝ) * (2 * Real.pi) = u - v := by linarith [hk]
    have hk0 : k = 0 := by
      by_contra hkne
      have h3 : (1 : ℝ) ≤ |(k : ℝ)| := by rw [← Int.cast_abs]; exact_mod_cast Int.one_le_abs hkne
      have h4 : 2 * Real.pi ≤ |u - v| := by
        rw [← h2, abs_mul, abs_of_pos (by positivity : (0 : ℝ) < 2 * Real.pi)]
        nlinarith [h3, Real.pi_pos]
      linarith
    rw [hk0] at h2
    simp only [Int.cast_zero, zero_mul] at h2
    linarith [h2]
  obtain ⟨u_l, hu_lmem, hu_l⟩ := exists_par l hlJ
  obtain ⟨u_q, hu_qmem, hu_q⟩ := exists_par q hqJ
  -- the parameter intervals of the two arcs
  set c₁ : ℝ := if l ∈ A then 0 else θ with hc₁def
  set d₁ : ℝ := if l ∈ A then θ else 2 * Real.pi with hd₁def
  set c₂ : ℝ := if l ∈ A then θ else 0 with hc₂def
  set d₂ : ℝ := if l ∈ A then 2 * Real.pi else θ with hd₂def
  have hJ₁eq : γ' '' Set.Icc c₁ d₁ = if l ∈ A then A else B := by
    by_cases h : l ∈ A
    · have e1 : c₁ = 0 := by rw [hc₁def]; exact if_pos h
      have e2 : d₁ = θ := by rw [hd₁def]; exact if_pos h
      rw [e1, e2, ← hAdef, if_pos h]
    · have e1 : c₁ = θ := by rw [hc₁def]; exact if_neg h
      have e2 : d₁ = 2 * Real.pi := by rw [hd₁def]; exact if_neg h
      rw [e1, e2, ← hBdef, if_neg h]
  have hJ₂eq : γ' '' Set.Icc c₂ d₂ = if l ∈ A then B else A := by
    by_cases h : l ∈ A
    · have e1 : c₂ = θ := by rw [hc₂def]; exact if_pos h
      have e2 : d₂ = 2 * Real.pi := by rw [hd₂def]; exact if_pos h
      rw [e1, e2, ← hBdef, if_pos h]
    · have e1 : c₂ = 0 := by rw [hc₂def]; exact if_neg h
      have e2 : d₂ = θ := by rw [hd₂def]; exact if_neg h
      rw [e1, e2, ← hAdef, if_neg h]
  have hu_l_Icc : u_l ∈ Set.Icc c₁ d₁ := by
    by_cases hlA : l ∈ A
    · obtain ⟨u, hu, hul⟩ := hlA
      have hlA' : l ∈ A := ⟨u, hu, hul⟩
      have huIco : u ∈ Set.Ico 0 (2 * Real.pi) := ⟨hu.1, lt_of_le_of_lt hu.2 hθlt⟩
      have h : u_l = u := par_unique hu_lmem huIco (by rw [hu_l, hul])
      have hc : c₁ = 0 := by rw [hc₁def]; exact if_pos hlA'
      have hd : d₁ = θ := by rw [hd₁def]; exact if_pos hlA'
      rw [hc, hd, h]; exact hu
    · have hlB : l ∈ B := by
        rcases (show l ∈ A ∪ B from by rw [hAB]; exact hlJ) with h' | h'
        · exact absurd h' hlA
        · exact h'
      obtain ⟨u, hu, hul⟩ := hlB
      have huIco : u ∈ Set.Ico 0 (2 * Real.pi) := by
        refine ⟨le_trans hθpos.le hu.1, lt_of_le_of_ne hu.2 (fun h => ?_)⟩
        rw [h, hγ2π] at hul
        have h1 : l.re = 0 := hlSeg.1
        rw [← hul] at h1
        norm_num at h1
      have h : u_l = u := par_unique hu_lmem huIco (by rw [hu_l, hul])
      have hc : c₁ = θ := by rw [hc₁def]; exact if_neg hlA
      have hd : d₁ = 2 * Real.pi := by rw [hd₁def]; exact if_neg hlA
      rw [hc, hd, h]; exact hu
  have hc₁_cases : (c₁ = 0 ∧ d₁ = θ) ∨ (c₁ = θ ∧ d₁ = 2 * Real.pi) := by
    by_cases h : l ∈ A
    · left; exact ⟨by rw [hc₁def]; exact if_pos h, by rw [hd₁def]; exact if_pos h⟩
    · right; exact ⟨by rw [hc₁def]; exact if_neg h, by rw [hd₁def]; exact if_neg h⟩
  have hc₂_cases : (c₂ = θ ∧ d₂ = 2 * Real.pi) ∨ (c₂ = 0 ∧ d₂ = θ) := by
    by_cases h : l ∈ A
    · left; exact ⟨by rw [hc₂def]; exact if_pos h, by rw [hd₂def]; exact if_pos h⟩
    · right; exact ⟨by rw [hc₂def]; exact if_neg h, by rw [hd₂def]; exact if_neg h⟩
  have hmem_l_J₁ : l ∈ γ' '' Set.Icc c₁ d₁ := by
    rw [hJ₁eq]
    by_cases h : l ∈ A
    · simp [h]
    · simp only [if_neg h]
      rcases (show l ∈ A ∪ B from by rw [hAB]; exact hlJ) with h' | h'
      · exact absurd h' h
      · exact h'
  have hJ12_inter : (γ' '' Set.Icc c₁ d₁) ∩ (γ' '' Set.Icc c₂ d₂) ⊆ ({-1, 1} : Set ℂ) := by
    rw [hJ₁eq, hJ₂eq]
    by_cases h : l ∈ A
    · rw [if_pos h, if_pos h]
      exact hAB_inter
    · rw [if_neg h, if_neg h]
      rw [Set.inter_comm]
      exact hAB_inter
  -- the comparison point `m`
  set K₁ : Set ℂ := (γ' '' Set.Icc c₁ d₁) ∩ vSeg with hK₁def
  set K₂ : Set ℂ := (γ' '' Set.Icc c₂ d₂) ∩ vSeg with hK₂def
  have hK₁ne : K₁.Nonempty := ⟨l, hmem_l_J₁, hlSeg⟩
  have hK₁compact : IsCompact K₁ :=
    (isCompact_Icc.image hcont').inter_right isClosed_vSeg
  obtain ⟨m, hmK₁, hmmin⟩ := hK₁compact.exists_isMinOn hK₁ne
    (Complex.continuous_im.continuousOn : ContinuousOn (fun z : ℂ => z.im) _)
  have hmJ₁ : m ∈ γ' '' Set.Icc c₁ d₁ := hmK₁.1
  have hmSeg : m ∈ vSeg := hmK₁.2
  have hmJ : m ∈ Set.range γ' := by
    obtain ⟨u, -, rfl⟩ := hmJ₁
    exact ⟨u, rfl⟩
  have hK_sub : K₁ ∪ K₂ = Set.range γ' ∩ vSeg := by
    have h12 : Set.Icc c₁ d₁ ∪ Set.Icc c₂ d₂ = Set.Icc 0 (2 * Real.pi) := by
      by_cases hlA : l ∈ A
      · have e1 : c₁ = 0 := by rw [hc₁def]; exact if_pos hlA
        have e2 : d₁ = θ := by rw [hd₁def]; exact if_pos hlA
        have e3 : c₂ = θ := by rw [hc₂def]; exact if_pos hlA
        have e4 : d₂ = 2 * Real.pi := by rw [hd₂def]; exact if_pos hlA
        rw [e1, e2, e3, e4]; exact hIcc_union
      · have e1 : c₁ = θ := by rw [hc₁def]; exact if_neg hlA
        have e2 : d₁ = 2 * Real.pi := by rw [hd₁def]; exact if_neg hlA
        have e3 : c₂ = 0 := by rw [hc₂def]; exact if_neg hlA
        have e4 : d₂ = θ := by rw [hd₂def]; exact if_neg hlA
        rw [e1, e2, e3, e4, Set.union_comm]; exact hIcc_union
    rw [hK₁def, hK₂def, ← Set.union_inter_distrib_right, ← Set.image_union, h12,
      range_eq_image_Icc hper']
  have hmK : m ∈ Set.range γ' ∩ vSeg := ⟨hmJ, hmSeg⟩
  have hq_le_m : q.im ≤ m.im := hqmin hmK
  have hq_mem_K : q ∈ K₁ ∪ K₂ := by rw [hK_sub]; exact hqK
  have hc₂A : l ∈ A → (c₂ = θ ∧ d₂ = 2 * Real.pi) := fun h =>
    ⟨by rw [hc₂def]; exact if_pos h, by rw [hd₂def]; exact if_pos h⟩
  have hc₂B : ¬ l ∈ A → (c₂ = 0 ∧ d₂ = θ) := fun h =>
    ⟨by rw [hc₂def]; exact if_neg h, by rw [hd₂def]; exact if_neg h⟩
  -- ## Step 6: avoidance of `±1` on the open arcs
  have hIoo01 : ∀ u ∈ Set.Ioo (0 : ℝ) θ, γ' u ≠ -1 ∧ γ' u ≠ 1 := by
    intro u hu
    have huIco : u ∈ Set.Ico 0 (2 * Real.pi) := ⟨le_of_lt hu.1, lt_of_lt_of_le hu.2 hθlt.le⟩
    constructor
    · intro hcon
      have h0Ico : (0 : ℝ) ∈ Set.Ico 0 (2 * Real.pi) := ⟨le_refl 0, hπ⟩
      have := par_unique huIco h0Ico (by rw [hcon, h0'])
      linarith [this, hu.1]
    · intro hcon
      have := par_unique huIco hθIco (by rw [hcon, hγθ])
      linarith [this, hu.2]
  have hIooθ2 : ∀ u ∈ Set.Ioo θ (2 * Real.pi), γ' u ≠ -1 ∧ γ' u ≠ 1 := by
    intro u hu
    have huIco : u ∈ Set.Ico 0 (2 * Real.pi) := ⟨le_of_lt (lt_trans hθpos hu.1), hu.2⟩
    constructor
    · intro hcon
      have h0Ico : (0 : ℝ) ∈ Set.Ico 0 (2 * Real.pi) := ⟨le_refl 0, hπ⟩
      have := par_unique huIco h0Ico (by rw [hcon, h0'])
      linarith [this, hu.1, hθpos]
    · intro hcon
      have := par_unique huIco hθIco (by rw [hcon, hγθ])
      linarith [this, hu.1]
  have hIoo12 : ∀ u ∈ Set.Ioo c₁ d₁, γ' u ≠ -1 ∧ γ' u ≠ 1 := by
    intro u hu
    rcases hc₁_cases with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · rw [h1, h2] at hu; exact hIoo01 u hu
    · rw [h1, h2] at hu; exact hIooθ2 u hu
  have hIoo22 : ∀ u ∈ Set.Ioo c₂ d₂, γ' u ≠ -1 ∧ γ' u ≠ 1 := by
    intro u hu
    rcases hc₂_cases with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · rw [h1, h2] at hu; exact hIooθ2 u hu
    · rw [h1, h2] at hu; exact hIoo01 u hu
  have hc₁_ends : γ' c₁ = -1 ∨ γ' c₁ = 1 := by
    rcases hc₁_cases with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · left; rw [h1, h0']
    · right; rw [h1, hγθ]
  have hd₁_ends : γ' d₁ = -1 ∨ γ' d₁ = 1 := by
    rcases hc₁_cases with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · right; rw [h2, hγθ]
    · left; rw [h2, hγ2π]
  have hc₂_ends : γ' c₂ = -1 ∨ γ' c₂ = 1 := by
    rcases hc₂_cases with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · right; rw [h1, hγθ]
    · left; rw [h1, h0']
  have hd₂_ends : γ' d₂ = -1 ∨ γ' d₂ = 1 := by
    rcases hc₂_cases with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · left; rw [h2, hγ2π]
    · right; rw [h2, hγθ]
  have hpar_ends₁ : ∀ u : ℝ, (u = c₁ ∨ u = d₁) → γ' u = -1 ∨ γ' u = 1 := by
    intro u hu
    rcases hu with h | h
    · rw [h]; exact hc₁_ends
    · rw [h]; exact hd₁_ends
  -- the parameters of `m` and `l` in the arc `J₁`
  obtain ⟨u_m, hu_mIcc, hu_m⟩ := hmJ₁
  have hu_mIoo : u_m ∈ Set.Ioo c₁ d₁ := by
    refine ⟨lt_of_le_of_ne hu_mIcc.1 (fun h => ?_), lt_of_le_of_ne hu_mIcc.2 (fun h => ?_)⟩
    · rcases hpar_ends₁ u_m (Or.inl h.symm) with h2 | h2
      · have h3 : m = -1 := by rw [← hu_m, h2]
        have h1 : m.re = 0 := hmSeg.1
        rw [h3] at h1
        norm_num at h1
      · have h3 : m = 1 := by rw [← hu_m, h2]
        have h1 : m.re = 0 := hmSeg.1
        rw [h3] at h1
        norm_num at h1
    · rcases hpar_ends₁ u_m (Or.inr h) with h2 | h2
      · have h3 : m = -1 := by rw [← hu_m, h2]
        have h1 : m.re = 0 := hmSeg.1
        rw [h3] at h1
        norm_num at h1
      · have h3 : m = 1 := by rw [← hu_m, h2]
        have h1 : m.re = 0 := hmSeg.1
        rw [h3] at h1
        norm_num at h1
  have hu_lIoo : u_l ∈ Set.Ioo c₁ d₁ := by
    refine ⟨lt_of_le_of_ne hu_l_Icc.1 (fun h => ?_), lt_of_le_of_ne hu_l_Icc.2 (fun h => ?_)⟩
    · rcases hpar_ends₁ u_l (Or.inl h.symm) with h2 | h2
      · have h3 : l = -1 := by rw [← hu_l, h2]
        have h1 : l.re = 0 := hlSeg.1
        rw [h3] at h1
        norm_num at h1
      · have h3 : l = 1 := by rw [← hu_l, h2]
        have h1 : l.re = 0 := hlSeg.1
        rw [h3] at h1
        norm_num at h1
    · rcases hpar_ends₁ u_l (Or.inr h) with h2 | h2
      · have h3 : l = -1 := by rw [← hu_l, h2]
        have h1 : l.re = 0 := hlSeg.1
        rw [h3] at h1
        norm_num at h1
      · have h3 : l = 1 := by rw [← hu_l, h2]
        have h1 : l.re = 0 := hlSeg.1
        rw [h3] at h1
        norm_num at h1
  -- ## Step 6b: the crossing lemma gives a point of `K₂` at or below `m`
  have hK₂_below : ∃ k ∈ K₂, k.im ≤ m.im := by
    set P : ℝ → ℂ := concat 1 (fun t : ℝ => (1 - t) • ptBot + t • m)
        (concat 1 (fun t : ℝ => γ' (u_m + t * (u_l - u_m)))
          (fun t : ℝ => (1 - t) • l + t • ptTop)) with hPdef
    have hpiece1 : ∀ t ∈ Set.Icc (0 : ℝ) 1, (1 - t) • ptBot + t • m ∈ closedBox := by
      intro t ht
      have hseg : (1 - t) • ptBot + t • m ∈ segment ℝ ptBot m := by
        rw [segment_eq_image]
        exact ⟨t, ht, rfl⟩
      exact vSeg_subset_closedBox (vSeg_convex.segment_subset ptBot_mem_vSeg hmSeg hseg)
    have hpiece2 : ∀ t ∈ Set.Icc (0 : ℝ) 1,
        γ' (u_m + t * (u_l - u_m)) ∈ closedBox := by
      intro t ht
      have harg : u_m + t * (u_l - u_m) ∈ Set.Icc c₁ d₁ := by
        rcases le_or_gt u_m u_l with hlm | hlt
        · exact ⟨by nlinarith [hu_mIcc.1, hu_l_Icc.1, ht.1, ht.2, hlm],
            by nlinarith [hu_mIcc.2, hu_l_Icc.2, ht.1, ht.2, hlm]⟩
        · exact ⟨by nlinarith [hu_mIcc.1, hu_l_Icc.1, ht.1, ht.2, hlt],
            by nlinarith [hu_mIcc.2, hu_l_Icc.2, ht.1, ht.2, hlt]⟩
      have harg2 : u_m + t * (u_l - u_m) ∈ Set.Icc 0 (2 * Real.pi) := by
        rcases hc₁_cases with ⟨e1, e2⟩ | ⟨e1, e2⟩
        · rw [e1, e2] at harg
          exact ⟨harg.1, le_trans harg.2 hθlt.le⟩
        · rw [e1, e2] at harg
          exact ⟨le_trans hθpos.le harg.1, harg.2⟩
      exact hJsub (by
        rw [range_eq_image_Icc hper']
        exact ⟨_, harg2, rfl⟩)
    have hpiece3 : ∀ t ∈ Set.Icc (0 : ℝ) 1, (1 - t) • l + t • ptTop ∈ closedBox := by
      intro t ht
      have hseg : (1 - t) • l + t • ptTop ∈ segment ℝ l ptTop := by
        rw [segment_eq_image]
        exact ⟨t, ht, rfl⟩
      exact vSeg_subset_closedBox (vSeg_convex.segment_subset hlSeg ptTop_mem_vSeg hseg)
    have hPcont : Continuous P := by
      rw [hPdef]
      refine continuous_concat (by fun_prop) (continuous_concat ?_ (by fun_prop) ?_) ?_
      · exact hcont'.comp (by fun_prop)
      · have h1 : γ' (u_m + 1 * (u_l - u_m)) = (1 - (0 : ℝ)) • l + (0 : ℝ) • ptTop := by
          rw [show u_m + 1 * (u_l - u_m) = u_l by ring, hu_l]
          simp
        exact h1
      · have h1 : (1 - (1 : ℝ)) • ptBot + (1 : ℝ) • m =
            (concat 1 (fun t : ℝ => γ' (u_m + t * (u_l - u_m)))
              (fun t : ℝ => (1 - t) • l + t • ptTop)) 0 := by
          rw [concat_of_le (by norm_num : (0 : ℝ) ≤ 1)]
          rw [show u_m + (0 : ℝ) * (u_l - u_m) = u_m by ring, hu_m]
          simp
        exact h1
    have hPbox : ∀ t ∈ Set.Icc (0 : ℝ) 3, P t ∈ closedBox := by
      intro t ht
      rw [hPdef]
      by_cases h1 : t ≤ 1
      · rw [concat_of_le h1]
        exact hpiece1 t ⟨ht.1, h1⟩
      · rw [concat_of_not_le h1]
        by_cases h2 : t - 1 ≤ 1
        · rw [concat_of_le h2]
          exact hpiece2 (t - 1) ⟨by linarith [not_le.mp h1], h2⟩
        · rw [concat_of_not_le h2]
          have h3 := hpiece3 (t - 2) ⟨by linarith [not_le.mp h2], by linarith [ht.2]⟩
          simpa only [show t - 1 - 1 = t - 2 by ring] using h3
    have hP0 : P 0 = ptBot := by
      rw [hPdef, concat_of_le (by norm_num : (0 : ℝ) ≤ 1)]
      simp
    have hP3 : P 3 = ptTop := by
      rw [hPdef]
      rw [concat_of_not_le (by norm_num : ¬ (3 : ℝ) ≤ 1)]
      rw [concat_of_not_le (by norm_num : ¬ ((3 : ℝ) - 1) ≤ 1)]
      norm_num
    set v : ℝ → ℂ := fun t => P (3 * (t + 1) / 2) with hvdef
    have hvcont : Continuous v := hPcont.comp (by fun_prop)
    have hv_bot : (v (-1)).im = -2 := by
      have h : v (-1) = ptBot := by
        rw [hvdef]
        norm_num
        exact hP0
      rw [h, ptBot_im]
    have hv_top : (v 1).im = 2 := by
      have h : v 1 = ptTop := by
        rw [hvdef]
        norm_num
        exact hP3
      rw [h, ptTop_im]
    have hvbox : ∀ t ∈ Set.Icc (-1 : ℝ) 1, |(v t).re| ≤ 1 ∧ |(v t).im| ≤ 2 := by
      intro t ht
      have h1 : 3 * (t + 1) / 2 ∈ Set.Icc (0 : ℝ) 3 := ⟨by linarith [ht.1], by linarith [ht.2]⟩
      have h2 := hPbox _ h1
      rw [hvdef]
      exact h2
    -- the left-right path along `J₂`
    set e₁ : ℝ := θ with he₁def
    set em1 : ℝ := if l ∈ A then 2 * Real.pi else 0 with hem1def
    have he₁mem : e₁ ∈ Set.Icc c₂ d₂ := by
      rw [he₁def]
      by_cases h : l ∈ A
      · obtain ⟨h1, h2⟩ := hc₂A h
        rw [h1, h2]; exact ⟨le_refl _, hθlt.le⟩
      · obtain ⟨h1, h2⟩ := hc₂B h
        rw [h1, h2]; exact ⟨hθpos.le, le_refl _⟩
    have hem1mem : em1 ∈ Set.Icc c₂ d₂ := by
      rw [hem1def]
      by_cases h : l ∈ A
      · rw [if_pos h]
        obtain ⟨h1, h2⟩ := hc₂A h
        rw [h1, h2]; exact ⟨hθlt.le, le_refl _⟩
      · rw [if_neg h]
        obtain ⟨h1, h2⟩ := hc₂B h
        rw [h1, h2]; exact ⟨le_refl _, hθpos.le⟩
    have hem1 : γ' em1 = -1 := by
      rw [hem1def]
      by_cases h : l ∈ A
      · rw [if_pos h]
        exact hγ2π
      · rw [if_neg h]; exact h0'
    have he₁ : γ' e₁ = 1 := by rw [he₁def]; exact hγθ
    set h₂ : ℝ → ℂ := fun t => γ' (em1 + (t + 1) / 2 * (e₁ - em1)) with hh₂def
    have hh₂arg : ∀ t ∈ Set.Icc (-1 : ℝ) 1, em1 + (t + 1) / 2 * (e₁ - em1) ∈ Set.Icc c₂ d₂ := by
      intro t ht
      rcases le_or_gt em1 e₁ with hle | hlt
      · exact ⟨by nlinarith [hem1mem.1, he₁mem.1, ht.1, ht.2, hle],
          by nlinarith [hem1mem.2, he₁mem.2, ht.1, ht.2, hle]⟩
      · exact ⟨by nlinarith [hem1mem.1, he₁mem.1, ht.1, ht.2, hlt],
          by nlinarith [hem1mem.2, he₁mem.2, ht.1, ht.2, hlt]⟩
    have hh₂cont : Continuous h₂ := hcont'.comp (by fun_prop)
    have hh₂_left : (h₂ (-1)).re = -1 := by
      have h : h₂ (-1) = -1 := by
        show γ' (em1 + ((-1 : ℝ) + 1) / 2 * (e₁ - em1)) = -1
        have harg : em1 + ((-1 : ℝ) + 1) / 2 * (e₁ - em1) = em1 := by ring
        rw [harg, hem1]
      rw [h]; norm_num
    have hh₂_right : (h₂ 1).re = 1 := by
      have h : h₂ 1 = 1 := by
        show γ' (em1 + ((1 : ℝ) + 1) / 2 * (e₁ - em1)) = 1
        have harg : em1 + ((1 : ℝ) + 1) / 2 * (e₁ - em1) = e₁ := by ring
        rw [harg, he₁]
      rw [h]; norm_num
    have hh₂box : ∀ t ∈ Set.Icc (-1 : ℝ) 1, |(h₂ t).re| ≤ 1 ∧ |(h₂ t).im| ≤ 2 := by
      intro t ht
      have harg := hh₂arg t ht
      have harg2 : em1 + (t + 1) / 2 * (e₁ - em1) ∈ Set.Icc 0 (2 * Real.pi) := by
        by_cases h : l ∈ A
        · obtain ⟨h1, h2⟩ := hc₂A h
          rw [h1, h2] at harg
          exact ⟨le_trans hθpos.le harg.1, harg.2⟩
        · obtain ⟨h1, h2⟩ := hc₂B h
          rw [h1, h2] at harg
          exact ⟨harg.1, le_trans harg.2 hθlt.le⟩
      have hmem : h₂ t ∈ Set.range γ' := by
        rw [hh₂def, range_eq_image_Icc hper']
        exact ⟨_, harg2, rfl⟩
      exact hJsub hmem
    obtain ⟨s₁, hs₁, t₁, ht₁, heq⟩ :=
      crossing_rect hh₂cont hvcont hh₂box hvbox hh₂_left hh₂_right hv_bot hv_top
    -- the meeting point
    have hyJ₂ : h₂ s₁ ∈ γ' '' Set.Icc c₂ d₂ := by
      rw [hh₂def]
      exact ⟨_, hh₂arg s₁ hs₁, rfl⟩
    set y : ℂ := h₂ s₁ with hydef
    have hyv : y = v t₁ := heq
    set τ : ℝ := 3 * (t₁ + 1) / 2 with hτdef
    have hτmem : τ ∈ Set.Icc (0 : ℝ) 3 := ⟨by linarith [ht₁.1], by linarith [ht₁.2]⟩
    have hyτ : y = P τ := by rw [hyv, hvdef]
    have hyseg : vSeg ⊆ closedBox := vSeg_subset_closedBox
    rcases le_or_gt τ 1 with hτ1 | hτ1
    · refine ⟨y, ⟨hyJ₂, ?_⟩, ?_⟩
      · rw [hyτ, hPdef, concat_of_le hτ1]
        have hseg : (1 - τ) • ptBot + τ • m ∈ segment ℝ ptBot m := by
          rw [segment_eq_image]
          exact ⟨τ, ⟨hτmem.1, hτ1⟩, rfl⟩
        exact vSeg_convex.segment_subset ptBot_mem_vSeg hmSeg hseg
      · rw [hyτ, hPdef, concat_of_le hτ1]
        have h1 : ((1 - τ) • ptBot + τ • m).im = (1 - τ) * ptBot.im + τ * m.im := by simp
        rw [h1, ptBot_im]
        have hm1 : -2 ≤ m.im := hmSeg.2.1
        nlinarith [hτmem.1, hτ1]
    · rcases le_or_gt τ 2 with hτ2 | hτ2
      · exfalso
        have hyarc : y = γ' (u_m + (τ - 1) * (u_l - u_m)) := by
          rw [hyτ, hPdef, concat_of_not_le (not_le.mpr hτ1),
            concat_of_le (by linarith : τ - 1 ≤ 1)]
        have harg : u_m + (τ - 1) * (u_l - u_m) ∈ Set.Ioo c₁ d₁ := by
          have hσ0 : (0 : ℝ) < τ - 1 := by linarith
          have hσ1 : τ - 1 ≤ 1 := by linarith
          rcases le_or_gt u_m u_l with hlm | hlt
          · refine ⟨by nlinarith [hu_mIoo.1, hu_lIoo.1, hσ0, hσ1, hlm],
              by nlinarith [hu_mIoo.2, hu_lIoo.2, hσ0, hσ1, hlm]⟩
          · refine ⟨by nlinarith [hu_mIoo.1, hu_lIoo.1, hσ0, hσ1, hlt],
              by nlinarith [hu_mIoo.2, hu_lIoo.2, hσ0, hσ1, hlt]⟩
        have hargIcc : u_m + (τ - 1) * (u_l - u_m) ∈ Set.Icc c₁ d₁ := ⟨harg.1.le, harg.2.le⟩
        have hyJ₁ : y ∈ γ' '' Set.Icc c₁ d₁ := by
          rw [hyarc]; exact ⟨_, hargIcc, rfl⟩
        have h12 : y ∈ ({-1, 1} : Set ℂ) := hJ12_inter ⟨hyJ₁, hyJ₂⟩
        have hne := hIoo12 _ harg
        rw [hyarc] at h12
        rcases h12 with h | h
        · exact hne.1 h
        · exact hne.2 h
      · exfalso
        have h2ne : ¬ τ - 1 ≤ 1 := by linarith
        have hyseg2 : y = (1 - (τ - 1 - 1)) • l + (τ - 1 - 1) • ptTop := by
          rw [hyτ, hPdef, concat_of_not_le (not_le.mpr hτ1), concat_of_not_le h2ne]
        have hyvSeg : y ∈ vSeg := by
          rw [hyseg2]
          have hseg : (1 - (τ - 1 - 1)) • l + (τ - 1 - 1) • ptTop ∈ segment ℝ l ptTop := by
            rw [segment_eq_image]
            exact ⟨τ - 1 - 1, ⟨by linarith, by linarith [hτmem.2]⟩, rfl⟩
          exact vSeg_convex.segment_subset hlSeg ptTop_mem_vSeg hseg
        have hyJ : y ∈ Set.range γ' := ⟨_, rfl⟩
        have hle : y.im ≤ l.im := hlmax ⟨hyJ, hyvSeg⟩
        have hge : l.im ≤ y.im := by
          rw [hyseg2]
          have h1 : ((1 - (τ - 1 - 1)) • l + (τ - 1 - 1) • ptTop).im =
              (1 - (τ - 1 - 1)) * l.im + (τ - 1 - 1) * ptTop.im := by simp
          rw [h1, ptTop_im]
          have hσ : 0 ≤ τ - 1 - 1 := by linarith
          have hlim2 : l.im ≤ 2 := hlSeg.2.2
          nlinarith
        have hyim : y.im = l.im := le_antisymm hle hge
        have hyl : y = l := by
          apply Complex.ext
          · rw [hyvSeg.1, hlSeg.1]
          · exact hyim
        have hl12 : l ∈ ({-1, 1} : Set ℂ) := hJ12_inter ⟨hmem_l_J₁, hyl ▸ hyJ₂⟩
        have hlne : l ≠ -1 ∧ l ≠ 1 := by
          constructor <;> intro h
          · have h1 := congrArg Complex.re h
            rw [hlSeg.1] at h1
            norm_num at h1
          · have h1 := congrArg Complex.re h
            rw [hlSeg.1] at h1
            norm_num at h1
        rcases hl12 with h | h
        · exact hlne.1 h
        · exact hlne.2 h
  -- ## Step 7: the window and the component `U`
  have hK₁K₂ : K₁ ∩ K₂ = ∅ := by
    rw [Set.eq_empty_iff_forall_notMem]
    rintro w ⟨hw₁, hw₂⟩
    have h1 : w ∈ ({-1, 1} : Set ℂ) := hJ12_inter ⟨hw₁.1, hw₂.1⟩
    have h2 : w ∈ vSeg := hw₁.2
    have h3 : w ≠ -1 ∧ w ≠ 1 := by
      constructor
      · intro h
        have h4 := h2.1
        rw [h] at h4
        norm_num at h4
      · intro h
        have h4 := h2.1
        rw [h] at h4
        norm_num at h4
    rcases h1 with h | h
    · exact h3.1 h
    · exact h3.2 h
  have hK₂compact : IsCompact K₂ := (isCompact_Icc.image hcont').inter_right isClosed_vSeg
  have hK₂le_closed : IsClosed {z : ℂ | z.im ≤ m.im} :=
    isClosed_le Complex.continuous_im continuous_const
  obtain ⟨p₁, hp₁K, hp₁max⟩ := (hK₂compact.inter_right hK₂le_closed).exists_isMaxOn
    hK₂_below (Complex.continuous_im.continuousOn : ContinuousOn (fun z : ℂ => z.im) _)
  have hp₁K₂ : p₁ ∈ K₂ := hp₁K.1
  have hp₁im : p₁.im ≤ m.im := hp₁K.2
  have hp₁Seg : p₁ ∈ vSeg := hp₁K₂.2
  have hp₁lt : p₁.im < m.im := by
    rcases lt_or_eq_of_le hp₁im with h | h
    · exact h
    · exfalso
      have hpm : p₁ = m := by
        apply Complex.ext
        · rw [hp₁Seg.1, hmSeg.1]
        · exact h
      have hmK₂ : m ∈ K₂ := hpm ▸ hp₁K₂
      exact (Set.eq_empty_iff_forall_notMem.mp hK₁K₂ m) ⟨hmK₁, hmK₂⟩
  obtain ⟨k₀, hk₀K₂, hk₀im⟩ := hK₂_below
  have hqK₂ : q ∈ K₂ := by
    rcases hq_mem_K with h | h
    · exfalso
      have h1 : m.im ≤ q.im := hmmin h
      have h2 : q.im = m.im := le_antisymm hq_le_m h1
      have h3 : q.im ≤ k₀.im := hqmin ⟨Set.image_subset_range _ _ hk₀K₂.1, hk₀K₂.2⟩
      have h4 : k₀.im = m.im := le_antisymm hk₀im (by linarith)
      have h5 : k₀ = m := by
        apply Complex.ext
        · rw [hk₀K₂.2.1, hmSeg.1]
        · exact h4
      exact (Set.eq_empty_iff_forall_notMem.mp hK₁K₂ m) ⟨hmK₁, h5 ▸ hk₀K₂⟩
    · exact h
  have hq_le_p₁ : q.im ≤ p₁.im := hp₁max ⟨hqK₂, hq_le_m⟩
  -- the window
  set z₀ : ℂ := (p₁ + m) / 2 with hz₀def
  set win : Set ℂ := {z : ℂ | z.re = 0 ∧ p₁.im < z.im ∧ z.im < m.im} with hwindef
  set U : Set ℂ := connectedComponentIn (Set.range γ')ᶜ z₀ with hUdef
  have hwinPre : IsPreconnected win := by
    have hset : win = (fun t : ℝ => (t : ℂ) * Complex.I) '' (Set.Ioo p₁.im m.im) := by
      rw [hwindef]
      ext z
      constructor
      · rintro ⟨hre, h1, h2⟩
        exact ⟨z.im, ⟨h1, h2⟩, by apply Complex.ext <;> simp [hre]⟩
      · rintro ⟨t, ⟨h1, h2⟩, rfl⟩
        exact ⟨by simp, by simpa using h1, by simpa using h2⟩
    rw [hset]
    exact (convex_Ioo p₁.im m.im).isPreconnected.image _ (by fun_prop)
  have hz₀_re : z₀.re = 0 := by
    rw [hz₀def]
    have h1 : p₁.re = 0 := hp₁Seg.1
    have h2 : m.re = 0 := hmSeg.1
    simp only [Complex.add_re, Complex.div_ofNat_re]
    rw [h1, h2]
    norm_num
  have hz₀_im : z₀.im = (p₁.im + m.im) / 2 := by
    rw [hz₀def]
    simp [Complex.add_im, Complex.div_ofNat_im, hp₁Seg.1, hmSeg.1]
  have hz₀win : z₀ ∈ win := by
    refine ⟨hz₀_re, ?_, ?_⟩
    · rw [hz₀_im]; linarith
    · rw [hz₀_im]; linarith
  have hwin_free : win ⊆ (Set.range γ')ᶜ := by
    intro z hz hzJ
    obtain ⟨hzre, hz1, hz2⟩ := hz
    have hzSeg : z ∈ vSeg := ⟨hzre, by linarith [hp₁Seg.2.1], by linarith [hmSeg.2.2]⟩
    have hzK : z ∈ K₁ ∪ K₂ := by rw [hK_sub]; exact ⟨hzJ, hzSeg⟩
    rcases hzK with h | h
    · have h1 : m.im ≤ z.im := hmmin h
      linarith
    · have h1 : z.im ≤ p₁.im := hp₁max ⟨h, le_of_lt hz2⟩
      linarith
  have hwinU : win ⊆ U := by
    have h := hwinPre.subset_connectedComponentIn (F := (Set.range γ')ᶜ) (x := z₀)
      hz₀win hwin_free
    rwa [← hUdef] at h
  -- ## Step 8: the path `β`
  obtain ⟨u_p₁, hu_p₁Icc, hu_p₁⟩ := hp₁K₂.1
  obtain ⟨u_q, hu_qIcc, hu_q⟩ := hqK₂.1
  have hpar_ends₂ : ∀ u : ℝ, (u = c₂ ∨ u = d₂) → γ' u = -1 ∨ γ' u = 1 := by
    intro u hu
    rcases hu with h | h
    · rw [h]; exact hc₂_ends
    · rw [h]; exact hd₂_ends
  have hu_p₁Ioo : u_p₁ ∈ Set.Ioo c₂ d₂ := by
    refine ⟨lt_of_le_of_ne hu_p₁Icc.1 (fun h => ?_), lt_of_le_of_ne hu_p₁Icc.2 (fun h => ?_)⟩
    · rcases hpar_ends₂ u_p₁ (Or.inl h.symm) with h2 | h2
      · have h3 : p₁ = -1 := by rw [← hu_p₁, h2]
        have h1 : p₁.re = 0 := hp₁Seg.1
        rw [h3] at h1
        norm_num at h1
      · have h3 : p₁ = 1 := by rw [← hu_p₁, h2]
        have h1 : p₁.re = 0 := hp₁Seg.1
        rw [h3] at h1
        norm_num at h1
    · rcases hpar_ends₂ u_p₁ (Or.inr h) with h2 | h2
      · have h3 : p₁ = -1 := by rw [← hu_p₁, h2]
        have h1 : p₁.re = 0 := hp₁Seg.1
        rw [h3] at h1
        norm_num at h1
      · have h3 : p₁ = 1 := by rw [← hu_p₁, h2]
        have h1 : p₁.re = 0 := hp₁Seg.1
        rw [h3] at h1
        norm_num at h1
  have hu_qIoo : u_q ∈ Set.Ioo c₂ d₂ := by
    refine ⟨lt_of_le_of_ne hu_qIcc.1 (fun h => ?_), lt_of_le_of_ne hu_qIcc.2 (fun h => ?_)⟩
    · rcases hpar_ends₂ u_q (Or.inl h.symm) with h2 | h2
      · have h3 : q = -1 := by rw [← hu_q, h2]
        have h1 : q.re = 0 := hqSeg.1
        rw [h3] at h1
        norm_num at h1
      · have h3 : q = 1 := by rw [← hu_q, h2]
        have h1 : q.re = 0 := hqSeg.1
        rw [h3] at h1
        norm_num at h1
    · rcases hpar_ends₂ u_q (Or.inr h) with h2 | h2
      · have h3 : q = -1 := by rw [← hu_q, h2]
        have h1 : q.re = 0 := hqSeg.1
        rw [h3] at h1
        norm_num at h1
      · have h3 : q = 1 := by rw [← hu_q, h2]
        have h1 : q.re = 0 := hqSeg.1
        rw [h3] at h1
        norm_num at h1
  set β : ℝ → ℂ := concat 1 (fun t : ℝ => (1 - t) • ptBot + t • q)
      (concat 1 (fun t : ℝ => γ' (u_q + t * (u_p₁ - u_q)))
        (concat 1 (fun t : ℝ => (1 - t) • p₁ + t • m)
          (concat 1 (fun t : ℝ => γ' (u_m + t * (u_l - u_m)))
            (fun t : ℝ => (1 - t) • l + t • ptTop)))) with hβdef
  have hβcont : Continuous β := by
    rw [hβdef]
    have hA : Continuous (fun t : ℝ => (1 - t) • ptBot + t • q) := by fun_prop
    have hB : Continuous (fun t : ℝ => γ' (u_q + t * (u_p₁ - u_q))) :=
      hcont'.comp (by fun_prop)
    have hC : Continuous (fun t : ℝ => (1 - t) • p₁ + t • m) := by fun_prop
    have hD : Continuous (fun t : ℝ => γ' (u_m + t * (u_l - u_m))) :=
      hcont'.comp (by fun_prop)
    have hE : Continuous (fun t : ℝ => (1 - t) • l + t • ptTop) := by fun_prop
    have hDE : (fun t : ℝ => γ' (u_m + t * (u_l - u_m))) 1
        = (fun t : ℝ => (1 - t) • l + t • ptTop) 0 := by
      show γ' (u_m + 1 * (u_l - u_m)) = (1 - (0 : ℝ)) • l + (0 : ℝ) • ptTop
      rw [show u_m + 1 * (u_l - u_m) = u_l by ring, hu_l]
      simp
    have hCD : (fun t : ℝ => (1 - t) • p₁ + t • m) 1
        = (concat 1 (fun t : ℝ => γ' (u_m + t * (u_l - u_m)))
            (fun t : ℝ => (1 - t) • l + t • ptTop)) 0 := by
      rw [concat_of_le (by norm_num : (0 : ℝ) ≤ 1)]
      show (1 - (1 : ℝ)) • p₁ + (1 : ℝ) • m = γ' (u_m + 0 * (u_l - u_m))
      rw [show u_m + 0 * (u_l - u_m) = u_m by ring, hu_m]
      simp
    have hBC : (fun t : ℝ => γ' (u_q + t * (u_p₁ - u_q))) 1
        = (concat 1 (fun t : ℝ => (1 - t) • p₁ + t • m)
            (concat 1 (fun t : ℝ => γ' (u_m + t * (u_l - u_m)))
              (fun t : ℝ => (1 - t) • l + t • ptTop))) 0 := by
      rw [concat_of_le (by norm_num : (0 : ℝ) ≤ 1)]
      show γ' (u_q + 1 * (u_p₁ - u_q)) = (1 - (0 : ℝ)) • p₁ + (0 : ℝ) • m
      rw [show u_q + 1 * (u_p₁ - u_q) = u_p₁ by ring, hu_p₁]
      simp
    have hAB : (fun t : ℝ => (1 - t) • ptBot + t • q) 1
        = (concat 1 (fun t : ℝ => γ' (u_q + t * (u_p₁ - u_q)))
            (concat 1 (fun t : ℝ => (1 - t) • p₁ + t • m)
              (concat 1 (fun t : ℝ => γ' (u_m + t * (u_l - u_m)))
                (fun t : ℝ => (1 - t) • l + t • ptTop)))) 0 := by
      rw [concat_of_le (by norm_num : (0 : ℝ) ≤ 1)]
      show (1 - (1 : ℝ)) • ptBot + (1 : ℝ) • q = γ' (u_q + 0 * (u_p₁ - u_q))
      rw [show u_q + 0 * (u_p₁ - u_q) = u_q by ring, hu_q]
      simp
    exact continuous_concat hA (continuous_concat hB (continuous_concat hC
      (continuous_concat hD hE hDE) hCD) hBC) hAB
  have hβ0 : β 0 = ptBot := by
    rw [hβdef, concat_of_le (by norm_num : (0 : ℝ) ≤ 1)]
    simp
  have hβ5 : β 5 = ptTop := by
    rw [hβdef]
    rw [concat_of_not_le (by norm_num : ¬ (5 : ℝ) ≤ 1)]
    rw [concat_of_not_le (by norm_num : ¬ ((5 : ℝ) - 1) ≤ 1)]
    rw [concat_of_not_le (by norm_num : ¬ ((5 : ℝ) - 1 - 1) ≤ 1)]
    rw [concat_of_not_le (by norm_num : ¬ ((5 : ℝ) - 1 - 1 - 1) ≤ 1)]
    norm_num
  have hβbox : ∀ t ∈ Set.Icc (0 : ℝ) 5, β t ∈ closedBox := by
    intro t ht
    rw [hβdef]
    by_cases h1 : t ≤ 1
    · rw [concat_of_le h1]
      have hseg : (1 - t) • ptBot + t • q ∈ segment ℝ ptBot q := by
        rw [segment_eq_image]
        exact ⟨t, ⟨ht.1, h1⟩, rfl⟩
      exact vSeg_subset_closedBox (vSeg_convex.segment_subset ptBot_mem_vSeg hqSeg hseg)
    · rw [concat_of_not_le h1]
      by_cases h2 : t - 1 ≤ 1
      · rw [concat_of_le h2]
        have harg : u_q + (t - 1) * (u_p₁ - u_q) ∈ Set.Icc c₂ d₂ := by
          rcases le_or_gt u_q u_p₁ with hlm | hlt
          · exact ⟨by nlinarith [hu_qIcc.1, hu_p₁Icc.1, ht.1, h2, hlm],
              by nlinarith [hu_qIcc.2, hu_p₁Icc.2, ht.1, h2, hlm]⟩
          · exact ⟨by nlinarith [hu_qIcc.1, hu_p₁Icc.1, ht.1, h2, hlt],
              by nlinarith [hu_qIcc.2, hu_p₁Icc.2, ht.1, h2, hlt]⟩
        have harg2 : u_q + (t - 1) * (u_p₁ - u_q) ∈ Set.Icc 0 (2 * Real.pi) := by
          by_cases h : l ∈ A
          · obtain ⟨e1, e2⟩ := hc₂A h
            rw [e1, e2] at harg
            exact ⟨le_trans hθpos.le harg.1, harg.2⟩
          · obtain ⟨e1, e2⟩ := hc₂B h
            rw [e1, e2] at harg
            exact ⟨harg.1, le_trans harg.2 hθlt.le⟩
        exact hJsub (by
          rw [range_eq_image_Icc hper']
          exact ⟨_, harg2, rfl⟩)
      · rw [concat_of_not_le h2]
        by_cases h3 : t - 1 - 1 ≤ 1
        · rw [concat_of_le h3]
          have hseg : (1 - (t - 1 - 1)) • p₁ + (t - 1 - 1) • m ∈ segment ℝ p₁ m := by
            rw [segment_eq_image]
            exact ⟨t - 1 - 1, ⟨by linarith [not_le.mp h2], h3⟩, rfl⟩
          exact vSeg_subset_closedBox (vSeg_convex.segment_subset hp₁Seg hmSeg hseg)
        · rw [concat_of_not_le h3]
          by_cases h4 : t - 1 - 1 - 1 ≤ 1
          · rw [concat_of_le h4]
            have harg : u_m + (t - 1 - 1 - 1) * (u_l - u_m) ∈ Set.Icc c₁ d₁ := by
              rcases le_or_gt u_m u_l with hlm | hlt
              · exact ⟨by nlinarith [hu_mIcc.1, hu_l_Icc.1, ht.1, h4, hlm],
                  by nlinarith [hu_mIcc.2, hu_l_Icc.2, ht.1, h4, hlm]⟩
              · exact ⟨by nlinarith [hu_mIcc.1, hu_l_Icc.1, ht.1, h4, hlt],
                  by nlinarith [hu_mIcc.2, hu_l_Icc.2, ht.1, h4, hlt]⟩
            have harg2 : u_m + (t - 1 - 1 - 1) * (u_l - u_m) ∈ Set.Icc 0 (2 * Real.pi) := by
              by_cases h : l ∈ A
              · have e1 : c₁ = 0 := by rw [hc₁def]; exact if_pos h
                have e2 : d₁ = θ := by rw [hd₁def]; exact if_pos h
                rw [e1, e2] at harg
                exact ⟨harg.1, le_trans harg.2 hθlt.le⟩
              · have e1 : c₁ = θ := by rw [hc₁def]; exact if_neg h
                have e2 : d₁ = 2 * Real.pi := by rw [hd₁def]; exact if_neg h
                rw [e1, e2] at harg
                exact ⟨le_trans hθpos.le harg.1, harg.2⟩
            exact hJsub (by
              rw [range_eq_image_Icc hper']
              exact ⟨_, harg2, rfl⟩)
          · rw [concat_of_not_le h4]
            have hseg : (1 - (t - 1 - 1 - 1 - 1)) • l + (t - 1 - 1 - 1 - 1) • ptTop ∈
                segment ℝ l ptTop := by
              rw [segment_eq_image]
              exact ⟨t - 1 - 1 - 1 - 1, ⟨by linarith [not_le.mp h4], by linarith [ht.2]⟩, rfl⟩
            exact vSeg_subset_closedBox (vSeg_convex.segment_subset hlSeg ptTop_mem_vSeg hseg)
  -- `β` avoids `±1` and is disjoint from every other component
  have hβpm : ∀ t ∈ Set.Icc (0 : ℝ) 5, β t ≠ -1 ∧ β t ≠ 1 := by
    intro t ht
    rw [hβdef]
    by_cases h1 : t ≤ 1
    · rw [concat_of_le h1]
      have hseg : (1 - t) • ptBot + t • q ∈ segment ℝ ptBot q := by
        rw [segment_eq_image]
        exact ⟨t, ⟨ht.1, h1⟩, rfl⟩
      have hmem := vSeg_convex.segment_subset ptBot_mem_vSeg hqSeg hseg
      exact ⟨fun h => by have := hmem.1; rw [h] at this; norm_num at this,
        fun h => by have := hmem.1; rw [h] at this; norm_num at this⟩
    · rw [concat_of_not_le h1]
      by_cases h2 : t - 1 ≤ 1
      · rw [concat_of_le h2]
        have harg : u_q + (t - 1) * (u_p₁ - u_q) ∈ Set.Ioo c₂ d₂ := by
          have hσ0 : (0 : ℝ) < t - 1 := by linarith [not_le.mp h1]
          have hσ1 : t - 1 ≤ 1 := h2
          rcases le_or_gt u_q u_p₁ with hlm | hlt
          · exact ⟨by nlinarith [hu_qIoo.1, hu_p₁Ioo.1, hσ0, hσ1, hlm],
              by nlinarith [hu_qIoo.2, hu_p₁Ioo.2, hσ0, hσ1, hlm]⟩
          · exact ⟨by nlinarith [hu_qIoo.1, hu_p₁Ioo.1, hσ0, hσ1, hlt],
              by nlinarith [hu_qIoo.2, hu_p₁Ioo.2, hσ0, hσ1, hlt]⟩
        exact hIoo22 _ harg
      · rw [concat_of_not_le h2]
        by_cases h3 : t - 1 - 1 ≤ 1
        · rw [concat_of_le h3]
          have hseg : (1 - (t - 1 - 1)) • p₁ + (t - 1 - 1) • m ∈ segment ℝ p₁ m := by
            rw [segment_eq_image]
            exact ⟨t - 1 - 1, ⟨by linarith [not_le.mp h2], h3⟩, rfl⟩
          have hmem := vSeg_convex.segment_subset hp₁Seg hmSeg hseg
          exact ⟨fun h => by have := hmem.1; rw [h] at this; norm_num at this,
            fun h => by have := hmem.1; rw [h] at this; norm_num at this⟩
        · rw [concat_of_not_le h3]
          by_cases h4 : t - 1 - 1 - 1 ≤ 1
          · rw [concat_of_le h4]
            have harg : u_m + (t - 1 - 1 - 1) * (u_l - u_m) ∈ Set.Ioo c₁ d₁ := by
              have hσ0 : (0 : ℝ) < t - 1 - 1 - 1 := by linarith [not_le.mp h3]
              have hσ1 : t - 1 - 1 - 1 ≤ 1 := h4
              rcases le_or_gt u_m u_l with hlm | hlt
              · exact ⟨by nlinarith [hu_mIoo.1, hu_lIoo.1, hσ0, hσ1, hlm],
                  by nlinarith [hu_mIoo.2, hu_lIoo.2, hσ0, hσ1, hlm]⟩
              · exact ⟨by nlinarith [hu_mIoo.1, hu_lIoo.1, hσ0, hσ1, hlt],
                  by nlinarith [hu_mIoo.2, hu_lIoo.2, hσ0, hσ1, hlt]⟩
            exact hIoo12 _ harg
          · rw [concat_of_not_le h4]
            have hseg : (1 - (t - 1 - 1 - 1 - 1)) • l + (t - 1 - 1 - 1 - 1) • ptTop ∈
                segment ℝ l ptTop := by
              rw [segment_eq_image]
              exact ⟨t - 1 - 1 - 1 - 1, ⟨by linarith [not_le.mp h4], by linarith [ht.2]⟩, rfl⟩
            have hmem := vSeg_convex.segment_subset hlSeg ptTop_mem_vSeg hseg
            exact ⟨fun h => by have := hmem.1; rw [h] at this; norm_num at this,
              fun h => by have := hmem.1; rw [h] at this; norm_num at this⟩
  -- ## Step 9: the final argument
  have hkey : ∀ w : ℂ, w ∉ Set.range γ' →
      connectedComponentIn (Set.range γ')ᶜ w = U ∨ connectedComponentIn (Set.range γ')ᶜ w = Uinf := by
    intro w hw
    by_contra hcon
    rw [not_or] at hcon
    obtain ⟨hWU, hWUinf⟩ := hcon
    set W : Set ℂ := connectedComponentIn (Set.range γ')ᶜ w with hWdef
    have hwW : w ∈ W := mem_connectedComponentIn hw
    have hWsub : W ⊆ (Set.range γ')ᶜ := connectedComponentIn_subset _ _
    have hWopen : IsOpen W := IsOpen.connectedComponentIn hJclosed.isOpen_compl
    have hWbox : W ⊆ closedBox := by
      intro z hz
      by_contra hzout
      have hzUinf : z ∈ Uinf := houtUinf hzout
      have h1 : connectedComponentIn (Set.range γ')ᶜ z = W := by
        rw [hWdef]; exact (connectedComponentIn_eq hz).symm
      have h3 : z ∈ connectedComponentIn (Set.range γ')ᶜ (3 * Complex.I) := by
        rwa [← hUinfdef]
      have h2 : connectedComponentIn (Set.range γ')ᶜ z = Uinf :=
        (connectedComponentIn_eq (x := 3 * Complex.I) h3).symm.trans hUinfdef.symm
      exact hWUinf (h1.symm.trans h2)
    have hfrW : frontier W = Set.range γ' := by
      rw [hWdef]
      exact hfront' w hw
    have hpm_cl : (-1 : ℂ) ∈ closure W ∧ (1 : ℂ) ∈ closure W := by
      constructor <;> refine frontier_subset_closure ?_
      · rw [hfrW]; exact hm1'
      · rw [hfrW]; exact (show (1 : ℂ) ∈ Set.range γ' from by rw [hrange']; exact h1)
    have hβ_compact : IsCompact (β '' Set.Icc (0 : ℝ) 5) := isCompact_Icc.image hβcont
    have hβ_avoid : ∀ t ∈ Set.Icc (0 : ℝ) 5, β t ∉ ({-1, 1} : Set ℂ) := by
      intro t ht hcon
      rcases hcon with h | h
      · exact (hβpm t ht).1 h
      · exact (hβpm t ht).2 h
    -- ## the separation from `±1` and the points of `W`
    have hne_β : (β '' Set.Icc (0 : ℝ) 5).Nonempty := ⟨β 0, ⟨0, ⟨le_rfl, by norm_num⟩, rfl⟩⟩
    obtain ⟨ya, hyaMem, hyamin⟩ := hβ_compact.exists_isMinOn hne_β
      ((continuous_id.dist continuous_const).continuousOn : ContinuousOn (fun z : ℂ => dist z (-1)) _)
    obtain ⟨yb, hybMem, hybmin⟩ := hβ_compact.exists_isMinOn hne_β
      ((continuous_const.dist continuous_id).continuousOn : ContinuousOn (fun z : ℂ => dist 1 z) _)
    have hyapos : 0 < dist ya (-1) := by
      obtain ⟨t, ht, rfl⟩ := hyaMem
      exact dist_pos.mpr (fun h => (hβ_avoid t ht) (by rw [h]; simp))
    have hybpos : 0 < dist 1 yb := by
      obtain ⟨t, ht, rfl⟩ := hybMem
      exact dist_pos.mpr (fun h => (hβ_avoid t ht) (by rw [← h]; simp))
    set ε : ℝ := min (dist ya (-1)) (dist 1 yb) with hεdef
    have hεpos : 0 < ε := lt_min hyapos hybpos
    have hεsep : ∀ t ∈ Set.Icc (0 : ℝ) 5,
        ε ≤ dist (β t) (-1) ∧ ε ≤ dist 1 (β t) := by
      intro t ht
      exact ⟨le_trans (min_le_left _ _) (hyamin ⟨t, ht, rfl⟩),
        le_trans (min_le_right _ _) (hybmin ⟨t, ht, rfl⟩)⟩
    -- ## the path `β` meets no other component
    have hbelow_q_Uinf : ∀ z : ℂ, z.re = 0 → z.im < q.im → z ∈ Uinf :=
      fun z h1 h2 => hbotUinf (Or.inl ⟨h1, h2⟩)
    have habove_l_Uinf : ∀ z : ℂ, z.re = 0 → l.im < z.im → z ∈ Uinf :=
      fun z h1 h2 => htopUinf (Or.inl ⟨h1, h2⟩)
    have hfill : (1 : ℝ) - (4 : ℝ) = -3 := by norm_num
    have hβ_mem : ∀ t ∈ Set.Icc (0 : ℝ) 5,
        β t ∈ U ∨ β t ∈ Uinf ∨ β t ∈ Set.range γ' := by
      intro t ht
      rw [hβdef]
      by_cases h1 : t ≤ 1
      · rw [concat_of_le h1]
        have hxSeg : (1 - t) • ptBot + t • q ∈ vSeg := by
          have hseg : (1 - t) • ptBot + t • q ∈ segment ℝ ptBot q := by
            rw [segment_eq_image]
            exact ⟨t, ⟨ht.1, h1⟩, rfl⟩
          exact vSeg_convex.segment_subset ptBot_mem_vSeg hqSeg hseg
        rcases eq_or_lt_of_le h1 with h1' | h1'
        · rw [h1']
          simp only [sub_self, zero_smul, one_smul, zero_add]
          exact Or.inr (Or.inr ⟨u_q, hu_q⟩)
        · rcases eq_or_ne ((1 - t) • ptBot + t • q) q with hxq | hxq
          · exact Or.inr (Or.inr ⟨u_q, hu_q.trans hxq.symm⟩)
          · refine Or.inr (Or.inl (hbelow_q_Uinf _ hxSeg.1 ?_))
            have hle : ((1 - t) • ptBot + t • q).im ≤ q.im := by
              have him : ((1 - t) • ptBot + t • q).im = (1 - t) * ptBot.im + t * q.im := by simp
              rw [him, ptBot_im]
              nlinarith [hqSeg.2.1, h1']
            refine lt_of_le_of_ne hle (fun h => hxq ?_)
            apply Complex.ext
            · rw [hxSeg.1, hqSeg.1]
            · exact h
      · rw [concat_of_not_le h1]
        by_cases h2 : t - 1 ≤ 1
        · rw [concat_of_le h2]
          have harg : u_q + (t - 1) * (u_p₁ - u_q) ∈ Set.Icc c₂ d₂ := by
            rcases le_or_gt u_q u_p₁ with hlm | hlt
            · exact ⟨by nlinarith [hu_qIcc.1, hu_p₁Icc.1, ht.1, h2, hlm],
                by nlinarith [hu_qIcc.2, hu_p₁Icc.2, ht.1, h2, hlm]⟩
            · exact ⟨by nlinarith [hu_qIcc.1, hu_p₁Icc.1, ht.1, h2, hlt],
                by nlinarith [hu_qIcc.2, hu_p₁Icc.2, ht.1, h2, hlt]⟩
          exact Or.inr (Or.inr ⟨_, rfl⟩)
        · rw [concat_of_not_le h2]
          by_cases h3 : t - 1 - 1 ≤ 1
          · rw [concat_of_le h3]
            set σ : ℝ := t - 1 - 1 with hσdef
            have hσ0 : 0 ≤ σ := by linarith [not_le.mp h2]
            have hσ1 : σ ≤ 1 := h3
            have hxSeg : (1 - σ) • p₁ + σ • m ∈ segment ℝ p₁ m := by
              rw [segment_eq_image]
              exact ⟨σ, ⟨hσ0, hσ1⟩, rfl⟩
            have hxMem := vSeg_convex.segment_subset hp₁Seg hmSeg hxSeg
            rcases eq_or_lt_of_le hσ0 with h0 | h0
            · rw [h0.symm]
              simp only [sub_zero, zero_smul, one_smul, add_zero]
              exact Or.inr (Or.inr ⟨u_p₁, hu_p₁⟩)
            · rcases eq_or_lt_of_le hσ1 with h1' | h1'
              · rw [h1']
                simp only [sub_self, zero_smul, one_smul, zero_add]
                exact Or.inr (Or.inr ⟨u_m, hu_m⟩)
              · refine Or.inl (hwinU ?_)
                have him : ((1 - σ) • p₁ + σ • m).im = (1 - σ) * p₁.im + σ * m.im := by simp
                refine ⟨hxMem.1, ?_, ?_⟩
                · rw [him]; nlinarith [h0, hp₁lt]
                · rw [him]; nlinarith [h1', hp₁lt]
          · rw [concat_of_not_le h3]
            by_cases h4 : t - 1 - 1 - 1 ≤ 1
            · rw [concat_of_le h4]
              have harg : u_m + (t - 1 - 1 - 1) * (u_l - u_m) ∈ Set.Icc c₁ d₁ := by
                rcases le_or_gt u_m u_l with hlm | hlt
                · exact ⟨by nlinarith [hu_mIcc.1, hu_l_Icc.1, ht.1, h4, hlm],
                    by nlinarith [hu_mIcc.2, hu_l_Icc.2, ht.1, h4, hlm]⟩
                · exact ⟨by nlinarith [hu_mIcc.1, hu_l_Icc.1, ht.1, h4, hlt],
                    by nlinarith [hu_mIcc.2, hu_l_Icc.2, ht.1, h4, hlt]⟩
              exact Or.inr (Or.inr ⟨_, rfl⟩)
            · rw [concat_of_not_le h4]
              set σ : ℝ := t - 1 - 1 - 1 - 1 with hσdef
              have hσ0 : 0 ≤ σ := by linarith [not_le.mp h4]
              have hxSeg : (1 - σ) • l + σ • ptTop ∈ vSeg := by
                have hseg : (1 - σ) • l + σ • ptTop ∈ segment ℝ l ptTop := by
                  rw [segment_eq_image]
                  exact ⟨σ, ⟨hσ0, by linarith [ht.2]⟩, rfl⟩
                exact vSeg_convex.segment_subset hlSeg ptTop_mem_vSeg hseg
              rcases eq_or_lt_of_le hσ0 with h0 | h0
              · rw [h0.symm]
                simp only [sub_zero, zero_smul, one_smul, add_zero]
                exact Or.inr (Or.inr ⟨u_l, hu_l⟩)
              · rcases eq_or_ne ((1 - σ) • l + σ • ptTop) l with hxl | hxl
                · exact Or.inr (Or.inr ⟨u_l, hu_l.trans hxl.symm⟩)
                · refine Or.inr (Or.inl (habove_l_Uinf _ hxSeg.1 ?_))
                  have hge : l.im ≤ ((1 - σ) • l + σ • ptTop).im := by
                    have him : ((1 - σ) • l + σ • ptTop).im = (1 - σ) * l.im + σ * ptTop.im := by simp
                    rw [him, ptTop_im]
                    nlinarith [hlSeg.2.2, h0]
                  refine lt_of_le_of_ne hge (fun h => hxl ?_)
                  apply Complex.ext
                  · rw [hxSeg.1, hlSeg.1]
                  · exact h.symm
    have hβ_notW : ∀ t ∈ Set.Icc (0 : ℝ) 5, β t ∉ W := by
      intro t ht hcon
      -- `W` is a component distinct from `U` and `Uinf`
      have hWUdisj : Disjoint W U := by
        rw [Set.disjoint_left]
        intro z hzW hzU
        have hzU' : z ∈ connectedComponentIn (Set.range γ')ᶜ z₀ := by rwa [← hUdef]
        have h1 : connectedComponentIn (Set.range γ')ᶜ z = connectedComponentIn (Set.range γ')ᶜ z₀ :=
          (connectedComponentIn_eq hzU').symm
        have h2 : connectedComponentIn (Set.range γ')ᶜ z = W := by
          rw [hWdef]; exact (connectedComponentIn_eq hzW).symm
        exact hWU ((h2.symm.trans h1).trans hUdef.symm)
      have hWUinfdisj : Disjoint W Uinf := by
        rw [Set.disjoint_left]
        intro z hzW hzU
        have hzU' : z ∈ connectedComponentIn (Set.range γ')ᶜ (3 * Complex.I) := by rwa [← hUinfdef]
        have h1 : connectedComponentIn (Set.range γ')ᶜ z = connectedComponentIn (Set.range γ')ᶜ (3 * Complex.I) :=
          (connectedComponentIn_eq hzU').symm
        have h2 : connectedComponentIn (Set.range γ')ᶜ z = W := by
          rw [hWdef]; exact (connectedComponentIn_eq hzW).symm
        exact hWUinf ((h2.symm.trans h1).trans hUinfdef.symm)
      rcases hβ_mem t ht with h | h | h
      · exact Set.disjoint_left.mp hWUdisj hcon h
      · exact Set.disjoint_left.mp hWUinfdisj hcon h
      · exact hWsub hcon h
    -- ## the two paths and the crossing lemma
    have hWpath : IsPathConnected W := by
      have hWconn : IsConnected W := ⟨⟨w, hwW⟩, isPreconnected_connectedComponentIn⟩
      exact (hWopen.isConnected_iff_isPathConnected).mp hWconn
    obtain ⟨a₁, ha₁W, ha₁ball⟩ : ∃ a₁ ∈ W, a₁ ∈ Metric.ball (-1) (ε/2) := by
      have hcl := hpm_cl.1
      rw [Metric.mem_closure_iff] at hcl
      obtain ⟨y, hyW, hyd⟩ := hcl (ε/2) (by linarith)
      exact ⟨y, hyW, by rw [Metric.mem_ball, dist_comm]; exact hyd⟩
    obtain ⟨b₁, hb₁W, hb₁ball⟩ : ∃ b₁ ∈ W, b₁ ∈ Metric.ball 1 (ε/2) := by
      have hcl := hpm_cl.2
      rw [Metric.mem_closure_iff] at hcl
      obtain ⟨y, hyW, hyd⟩ := hcl (ε/2) (by linarith)
      exact ⟨y, hyW, by rw [Metric.mem_ball, dist_comm]; exact hyd⟩
    have ha₁box : a₁ ∈ closedBox := hWbox ha₁W
    have hb₁box : b₁ ∈ closedBox := hWbox hb₁W
    obtain ⟨ρpath, hρpath⟩ := hWpath.joinedIn a₁ ha₁W b₁ hb₁W
    -- the left–right path
    set lamP : ℝ → ℂ := concat 1 (fun t : ℝ => (1 - t) • (-1) + t • a₁)
      (concat 1 (fun t : ℝ => ρpath.extend t) (fun t : ℝ => (1 - t) • b₁ + t • 1)) with hlamPdef
    have hlamPcont : Continuous lamP := by
      rw [hlamPdef]
      refine continuous_concat (by fun_prop) (continuous_concat ?_ (by fun_prop) ?_) ?_
      · exact ρpath.extend.continuous
      · have h1 : (fun t : ℝ => ρpath.extend t) 1 = (1 - (0 : ℝ)) • b₁ + (0 : ℝ) • 1 := by
          show ρpath.extend 1 = (1 - (0 : ℝ)) • b₁ + (0 : ℝ) • 1
          rw [Path.extend_one ρpath]; simp
        exact h1
      · have h1 : (1 - (1 : ℝ)) • (-1) + (1 : ℝ) • a₁ =
            (concat 1 (fun t : ℝ => ρpath.extend t)
              (fun t : ℝ => (1 - t) • b₁ + t • 1)) 0 := by
          rw [concat_of_le (by norm_num : (0 : ℝ) ≤ 1), Path.extend_zero ρpath]
          simp
        exact h1
    set hLR : ℝ → ℂ := fun t => lamP (3 * (t + 1) / 2) with hhLRdef
    set hBT : ℝ → ℂ := fun t => β (5 * (t + 1) / 2) with hhBTdef
    have hLRcont : Continuous hLR := hlamPcont.comp (by fun_prop)
    have hBTcont : Continuous hBT := hβcont.comp (by fun_prop)
    have hLR_left : (hLR (-1)).re = -1 := by
      have h1 : hLR (-1) = (-1 : ℂ) := by
        show lamP (3 * ((-1 : ℝ) + 1) / 2) = (-1 : ℂ)
        have h2 : 3 * ((-1 : ℝ) + 1) / 2 = 0 := by norm_num
        rw [h2, hlamPdef, concat_of_le (by norm_num : (0 : ℝ) ≤ 1)]
        simp
      rw [h1]; norm_num
    have hLR_right : (hLR 1).re = 1 := by
      have h1 : hLR 1 = (1 : ℂ) := by
        show lamP (3 * ((1 : ℝ) + 1) / 2) = (1 : ℂ)
        have h2 : 3 * ((1 : ℝ) + 1) / 2 = 3 := by norm_num
        rw [h2, hlamPdef]
        rw [concat_of_not_le (by norm_num : ¬ (3 : ℝ) ≤ 1)]
        rw [concat_of_not_le (by norm_num : ¬ ((3 : ℝ) - 1) ≤ 1)]
        norm_num
      rw [h1]; norm_num
    have hBT_bot : (hBT (-1)).im = -2 := by
      have h1 : hBT (-1) = ptBot := by
        show β (5 * ((-1 : ℝ) + 1) / 2) = ptBot
        have h2 : 5 * ((-1 : ℝ) + 1) / 2 = 0 := by norm_num
        rw [h2, hβ0]
      rw [h1, ptBot_im]
    have hBT_top : (hBT 1).im = 2 := by
      have h1 : hBT 1 = ptTop := by
        show β (5 * ((1 : ℝ) + 1) / 2) = ptTop
        have h2 : 5 * ((1 : ℝ) + 1) / 2 = 5 := by norm_num
        rw [h2, hβ5]
      rw [h1, ptTop_im]
    have hLRbox : ∀ t ∈ Set.Icc (-1 : ℝ) 1, |(hLR t).re| ≤ 1 ∧ |(hLR t).im| ≤ 2 := by
      intro t ht
      have hu : 3 * (t + 1) / 2 ∈ Set.Icc (0 : ℝ) 3 := ⟨by linarith [ht.1], by linarith [ht.2]⟩
      show lamP (3 * (t + 1) / 2) ∈ closedBox
      rw [hlamPdef]
      by_cases h1 : 3 * (t + 1) / 2 ≤ 1
      · rw [concat_of_le h1]
        have hseg : (1 - (3 * (t + 1) / 2)) • (-1) + (3 * (t + 1) / 2) • a₁ ∈
            segment ℝ (-1) a₁ := by
          rw [segment_eq_image]
          exact ⟨_, ⟨by linarith [hu.1], h1⟩, rfl⟩
        have hmem := convex_closedBox.segment_subset neg1_mem_closedBox ha₁box hseg
        simpa using hmem
      · rw [concat_of_not_le h1]
        by_cases h2 : 3 * (t + 1) / 2 - 1 ≤ 1
        · rw [concat_of_le h2]
          have h3 : 3 * (t + 1) / 2 - 1 ∈ Set.Icc (0 : ℝ) 1 :=
            ⟨by linarith [not_le.mp h1], h2⟩
          rw [Path.extend_apply ρpath h3]
          simpa using hWbox (hρpath _)
        · rw [concat_of_not_le h2]
          have hseg : (1 - (3 * (t + 1) / 2 - 1 - 1)) • b₁ + (3 * (t + 1) / 2 - 1 - 1) • 1 ∈
              segment ℝ b₁ 1 := by
            rw [segment_eq_image]
            exact ⟨_, ⟨by linarith [not_le.mp h2], by linarith [hu.2]⟩, rfl⟩
          have hmem := convex_closedBox.segment_subset hb₁box one_mem_closedBox hseg
          simpa using hmem
    have hBTbox : ∀ t ∈ Set.Icc (-1 : ℝ) 1, |(hBT t).re| ≤ 1 ∧ |(hBT t).im| ≤ 2 := by
      intro t ht
      have hu : 5 * (t + 1) / 2 ∈ Set.Icc (0 : ℝ) 5 := ⟨by linarith [ht.1], by linarith [ht.2]⟩
      have hmem := hβbox _ hu
      show β (5 * (t + 1) / 2) ∈ closedBox
      exact hmem
    have hnommet : ∀ s ∈ Set.Icc (-1 : ℝ) 1, ∀ t ∈ Set.Icc (-1 : ℝ) 1, hLR s ≠ hBT t := by
      intro s hs t ht heq
      have ht5 : 5 * (t + 1) / 2 ∈ Set.Icc (0 : ℝ) 5 := ⟨by linarith [ht.1], by linarith [ht.2]⟩
      have hβt : hBT t = β (5 * (t + 1) / 2) := rfl
      have hreg : hLR s ∈ W ∨ hLR s ∈ Metric.ball (-1) (ε/2) ∨ hLR s ∈ Metric.ball 1 (ε/2) := by
        have hu : 3 * (s + 1) / 2 ∈ Set.Icc (0 : ℝ) 3 := ⟨by linarith [hs.1], by linarith [hs.2]⟩
        rw [hhLRdef]
        show lamP (3 * (s + 1) / 2) ∈ W ∨ lamP (3 * (s + 1) / 2) ∈ ball (-1) (ε / 2) ∨
          lamP (3 * (s + 1) / 2) ∈ ball 1 (ε / 2)
        rw [hlamPdef]
        by_cases h1 : 3 * (s + 1) / 2 ≤ 1
        · rw [concat_of_le h1]
          right; left
          have hseg : (1 - (3 * (s + 1) / 2)) • (-1) + (3 * (s + 1) / 2) • a₁ ∈
              segment ℝ (-1) a₁ := by
            rw [segment_eq_image]
            exact ⟨_, ⟨by linarith [hu.1], h1⟩, rfl⟩
          exact (convex_ball (-1) (ε/2)).segment_subset
            (Metric.mem_ball_self (by linarith)) ha₁ball hseg
        · rw [concat_of_not_le h1]
          by_cases h2 : 3 * (s + 1) / 2 - 1 ≤ 1
          · rw [concat_of_le h2]
            left
            have h3 : 3 * (s + 1) / 2 - 1 ∈ Set.Icc (0 : ℝ) 1 :=
              ⟨by linarith [not_le.mp h1], h2⟩
            rw [Path.extend_apply ρpath h3]
            exact hρpath _
          · rw [concat_of_not_le h2]
            right; right
            have hseg : (1 - (3 * (s + 1) / 2 - 1 - 1)) • b₁ + (3 * (s + 1) / 2 - 1 - 1) • 1 ∈
                segment ℝ b₁ 1 := by
              rw [segment_eq_image]
              exact ⟨_, ⟨by linarith [not_le.mp h2], by linarith [hu.2]⟩, rfl⟩
            exact (convex_ball 1 (ε/2)).segment_subset hb₁ball
              (Metric.mem_ball_self (by linarith)) hseg
      rcases hreg with h | h | h
      · exact hβ_notW _ ht5 (by rw [← hβt, ← heq]; exact h)
      · have h4 : dist (β (5 * (t + 1) / 2)) (-1) < ε / 2 := by
          have h5 : dist (hLR s) (-1) < ε / 2 := Metric.mem_ball.mp h
          rw [show β (5 * (t + 1) / 2) = hLR s from by rw [hβt.symm, ← heq]]
          exact h5
        have h6 : ε ≤ dist (β (5 * (t + 1) / 2)) (-1) := (hεsep _ ht5).1
        linarith
      · have h4 : dist 1 (β (5 * (t + 1) / 2)) < ε / 2 := by
          have h5 : dist 1 (hLR s) < ε / 2 := by rw [dist_comm]; exact Metric.mem_ball.mp h
          rw [show β (5 * (t + 1) / 2) = hLR s from by rw [hβt.symm, ← heq]]
          exact h5
        have h6 : ε ≤ dist 1 (β (5 * (t + 1) / 2)) := (hεsep _ ht5).2
        linarith
    obtain ⟨s, hs, t, ht, heq⟩ :=
      crossing_rect hLRcont hBTcont hLRbox hBTbox hLR_left hLR_right hBT_bot hBT_top
    exact hnommet s hs t ht heq
  -- ## Step 10: two of the three components coincide
  rcases hkey x hx' with hxU | hxU <;> rcases hkey y hy' with hyU | hyU <;>
    rcases hkey z hz' with hzU | hzU <;>
    first
      | exact Or.inl (hxU.trans hyU.symm)
      | exact Or.inr (Or.inl (hxU.trans hzU.symm))
      | exact Or.inr (Or.inr (hyU.trans hzU.symm))


/-- **At most two connected components.**  The complement of the trace of a simple closed plane
curve has at most two connected components. -/
theorem compl_jordan_atMostTwo {γ : ℝ → ℂ} (hcont : Continuous γ)
    (hper : Function.Periodic γ (2 * Real.pi)) (hinj : Set.InjOn γ (Set.Ico 0 (2 * Real.pi)))
    {x y z : ℂ} (hx : x ∉ Set.range γ) (hy : y ∉ Set.range γ) (hz : z ∉ Set.range γ) :
    connectedComponentIn (Set.range γ)ᶜ x = connectedComponentIn (Set.range γ)ᶜ y ∨
    connectedComponentIn (Set.range γ)ᶜ x = connectedComponentIn (Set.range γ)ᶜ z ∨
    connectedComponentIn (Set.range γ)ᶜ y = connectedComponentIn (Set.range γ)ᶜ z := by
  classical
  by_cases hdis : IsPreconnected (Set.range γ)ᶜ
  · have hx' : connectedComponentIn (Set.range γ)ᶜ x = (Set.range γ)ᶜ :=
      Subset.antisymm (connectedComponentIn_subset _ _)
        (hdis.subset_connectedComponentIn hx (subset_refl _))
    have hy' : connectedComponentIn (Set.range γ)ᶜ y = (Set.range γ)ᶜ :=
      Subset.antisymm (connectedComponentIn_subset _ _)
        (hdis.subset_connectedComponentIn hy (subset_refl _))
    exact Or.inl (hx'.trans hy'.symm)
  · -- the trace is compact and has at least two points
    have hJcompact : IsCompact (Set.range γ) := isCompact_range_of_periodic hcont hper
    have hJne : (Set.range γ).Nonempty := ⟨γ 0, ⟨0, rfl⟩⟩
    -- a pair of points of the trace at maximal distance
    obtain ⟨p, hp, hpmax⟩ := (hJcompact.prod hJcompact).exists_isMaxOn (hJne.prod hJne)
      (continuous_dist.continuousOn : ContinuousOn (fun q : ℂ × ℂ => dist q.1 q.2) _)
    set a : ℂ := p.1 with hadef
    set b : ℂ := p.2 with hbdef
    have haJ : a ∈ Set.range γ := hp.1
    have hbJ : b ∈ Set.range γ := hp.2
    have hmax : ∀ u ∈ Set.range γ, ∀ v ∈ Set.range γ, dist u v ≤ dist a b := by
      intro u hu v hv
      have h := hpmax (show (u, v) ∈ Set.range γ ×ˢ Set.range γ from ⟨hu, hv⟩)
      simpa [hadef, hbdef] using h
    have hab : a ≠ b := by
      intro hab_eq
      have hab0 : dist a b = 0 := by rw [hab_eq, dist_self]
      have hall : ∀ u ∈ Set.range γ, u = a := by
        intro u hu
        have h := hmax u hu a haJ
        rw [hab0] at h
        exact dist_eq_zero.mp (le_antisymm h dist_nonneg)
      have hsingle : Set.range γ = {a} := by
        ext u; constructor
        · intro hu; exact hall u hu
        · rintro rfl; exact haJ
      exact hdis (hsingle ▸ Work.Smooth.JordanSeparation.isPreconnected_compl_point a)
    -- the similarity normalising `a ↦ -1`, `b ↦ 1`
    set c : ℂ := (b - a) / 2 with hcdef
    set m : ℂ := (a + b) / 2 with hmdef
    have hc : c ≠ 0 := by
      intro h
      have h1 : b - a = 0 := by
        have := congrArg (fun z : ℂ => 2 * z) h
        simpa [hcdef, mul_div_cancel₀] using this
      exact hab (sub_eq_zero.mp h1).symm
    let φ : ℂ ≃ₜ ℂ := (Homeomorph.subRight m).trans (Homeomorph.mulLeft₀ c⁻¹ (inv_ne_zero hc))
    have hφ_apply : ∀ z : ℂ, φ z = (z - m) / c := by
      intro z
      show c⁻¹ * (z - m) = (z - m) / c
      rw [div_eq_mul_inv, mul_comm]
    have hφa : φ a = -1 := by
      rw [hφ_apply]
      have h1 : a - m = -c := by
        rw [hmdef, hcdef]; ring
      rw [h1, neg_div, div_self hc]
    have hφb : φ b = 1 := by
      rw [hφ_apply]
      have h1 : b - m = c := by
        rw [hmdef, hcdef]; ring
      rw [h1, div_self hc]
    have hc2 : ‖c‖ = ‖b - a‖ / 2 := by rw [hcdef, norm_div]; simp
    have hcoe : ‖b - a‖ ≠ 0 := norm_ne_zero_iff.mpr (sub_ne_zero.mpr (Ne.symm hab))
    have hφnorm : ∀ u : ℂ, ‖φ u + 1‖ = ‖u - a‖ / ‖b - a‖ * 2 := by
      intro u
      have h1 : φ u + 1 = (u - a) / c := by
        rw [hφ_apply]
        field_simp
        ring
      rw [h1, norm_div, hc2]
      field_simp
    set γ' : ℝ → ℂ := fun t => φ (γ t) with hγ'def
    have hcont' : Continuous γ' := φ.continuous.comp hcont
    have hper' : Function.Periodic γ' (2 * Real.pi) := fun t => by
      show φ (γ (t + 2 * Real.pi)) = φ (γ t)
      rw [hper t]
    have hinj' : Set.InjOn γ' (Set.Ico 0 (2 * Real.pi)) :=
      fun u hu v hv huv => hinj hu hv (φ.injective huv)
    have hrange' : Set.range γ' = φ '' Set.range γ := by
      ext w; constructor
      · rintro ⟨t, rfl⟩; exact ⟨γ t, ⟨t, rfl⟩, rfl⟩
      · rintro ⟨u, ⟨t, rfl⟩, rfl⟩; exact ⟨t, rfl⟩
    have hsub' : ∀ w ∈ Set.range γ', w ∈ rectR ∨ w = -1 ∨ w = 1 := by
      intro w hw
      rw [hrange'] at hw
      obtain ⟨u, hu, rfl⟩ := hw
      have hu1 : dist u a ≤ dist a b := hmax u hu a haJ
      have hu2 : dist u b ≤ dist a b := hmax u hu b hbJ
      have hu1' : ‖u - a‖ ≤ ‖b - a‖ := by
        have h : ‖u - a‖ ≤ ‖a - b‖ := by simpa [dist_eq_norm] using hu1
        rwa [norm_sub_rev a b] at h
      have hu2' : ‖u - b‖ ≤ ‖b - a‖ := by
        have h : ‖u - b‖ ≤ ‖a - b‖ := by simpa [dist_eq_norm] using hu2
        rwa [norm_sub_rev a b] at h
      have hI1 : ‖φ u + 1‖ ≤ 2 := by
        rw [hφnorm, div_mul_eq_mul_div, div_le_iff₀ (by positivity : (0:ℝ) < ‖b - a‖)]
        nlinarith
      have hI2 : ‖φ u - 1‖ ≤ 2 := by
        have h2 : φ u - 1 = (u - b) / c := by
          rw [hφ_apply]; field_simp; ring
        rw [h2, norm_div, hc2]
        have hdiv : ‖u - b‖ / (‖b - a‖ / 2) = 2 * ‖u - b‖ / ‖b - a‖ := by field_simp
        rw [hdiv]
        rw [div_le_iff₀ (by positivity : (0:ℝ) < ‖b - a‖)]
        nlinarith
      -- coordinate consequences
      have h1 : ((φ u).re + 1) ^ 2 + (φ u).im ^ 2 ≤ 4 := by
        have h2 := pow_le_pow_left₀ (norm_nonneg (φ u + 1)) hI1 2
        rw [show (2 : ℝ) ^ 2 = 4 by norm_num] at h2
        rw [Complex.sq_norm, Complex.normSq_apply] at h2
        simpa [pow_two] using h2
      have h2 : ((φ u).re - 1) ^ 2 + (φ u).im ^ 2 ≤ 4 := by
        have h3 := pow_le_pow_left₀ (norm_nonneg (φ u - 1)) hI2 2
        rw [show (2 : ℝ) ^ 2 = 4 by norm_num] at h3
        rw [Complex.sq_norm, Complex.normSq_apply] at h3
        simpa [pow_two] using h3
      have himsq : (φ u).im ^ 2 < 4 := by
        by_contra hcon
        push_neg at hcon
        have h3 : ((φ u).re + 1) ^ 2 ≤ 0 := by nlinarith [h1, hcon]
        have h4 : (φ u).re + 1 = 0 := by nlinarith [sq_nonneg ((φ u).re + 1), h3]
        nlinarith [h2, h4]
      have him2 : -2 < (φ u).im ∧ (φ u).im < 2 := by
        have h3 : |(φ u).im| < 2 := by
          rw [abs_lt]
          constructor <;> nlinarith [himsq]
        rwa [abs_lt] at h3
      rcases lt_trichotomy (φ u).re 1 with hlt | heq | hgt
      · rcases lt_trichotomy (φ u).re (-1) with hlt2 | heq2 | hgt2
        · exact absurd h2 (by nlinarith)
        · have h5 : (φ u).im = 0 := by nlinarith [h2]
          exact Or.inr (Or.inl (by apply Complex.ext <;> simp [heq2, h5]))
        · exact Or.inl ⟨hgt2, hlt, him2.1, him2.2⟩
      · have h5 : (φ u).im = 0 := by nlinarith [h1]
        exact Or.inr (Or.inr (by apply Complex.ext <;> simp [heq, h5]))
      · exact absurd h1 (by nlinarith)
    have hdis' : ¬ IsPreconnected (Set.range γ')ᶜ := by
      intro hcon
      apply hdis
      have hcompl : (Set.range γ')ᶜ = φ '' (Set.range γ)ᶜ := by
        rw [hrange', Set.image_compl_eq φ.bijective]
      have h2 : IsPreconnected (φ '' (Set.range γ)ᶜ) := hcompl ▸ hcon
      have h3 : IsPreconnected ((⇑φ.symm ∘ ⇑φ) '' (Set.range γ)ᶜ) := by
        have h4 := h2.image (⇑φ.symm) φ.symm.continuous.continuousOn
        rwa [Set.image_image] at h4
      rw [show (⇑φ.symm ∘ ⇑φ) = id from funext fun x => φ.symm_apply_apply x,
        Set.image_id] at h3
      exact h3
    have hfront' : ∀ w : ℂ, w ∉ Set.range γ' →
        frontier (connectedComponentIn (Set.range γ')ᶜ w) = Set.range γ' :=
      frontier_component_eq_range hcont' hper' hinj' hdis'
    have hx' : φ x ∉ Set.range γ' := by
      rw [hrange']
      rintro ⟨u, hu, hux⟩
      exact hx (φ.injective hux ▸ hu)
    have hy' : φ y ∉ Set.range γ' := by
      rw [hrange']
      rintro ⟨u, hu, huy⟩
      exact hy (φ.injective huy ▸ hu)
    have hz' : φ z ∉ Set.range γ' := by
      rw [hrange']
      rintro ⟨u, hu, huz⟩
      exact hz (φ.injective huz ▸ hu)
    obtain ⟨a₀, ha₀⟩ : ∃ t : ℝ, γ t = a := haJ
    obtain ⟨b₀, hb₀⟩ : ∃ t : ℝ, γ t = b := hbJ
    have hm1' : (-1 : ℂ) ∈ Set.range γ' := ⟨a₀, by show φ (γ a₀) = -1; rw [ha₀, hφa]⟩
    have hone' : (1 : ℂ) ∈ Set.range γ' := ⟨b₀, by show φ (γ b₀) = 1; rw [hb₀, hφb]⟩
    have hkey := atMostTwo_of_rectSetup hcont' hper' hinj' hsub' hm1' hone' hdis' hfront'
      hx' hy' hz'
    -- transfer the conclusion back
    have hcomp : ∀ u : ℂ, u ∉ Set.range γ →
        φ '' connectedComponentIn (Set.range γ)ᶜ u = connectedComponentIn (Set.range γ')ᶜ (φ u) := by
      intro u hu
      have h := φ.image_connectedComponentIn (s := (Set.range γ)ᶜ) hu
      rw [Set.image_compl_eq φ.bijective, ← hrange'] at h
      exact h
    rcases hkey with h | h | h
    · exact Or.inl (Set.image_injective.mpr φ.injective ((hcomp x hx).trans (h.trans (hcomp y hy).symm)))
    · exact Or.inr (Or.inl (Set.image_injective.mpr φ.injective ((hcomp x hx).trans (h.trans (hcomp z hz).symm))))
    · exact Or.inr (Or.inr (Set.image_injective.mpr φ.injective ((hcomp y hy).trans (h.trans (hcomp z hz).symm))))

end

end Work.Topology.PlaneCurve