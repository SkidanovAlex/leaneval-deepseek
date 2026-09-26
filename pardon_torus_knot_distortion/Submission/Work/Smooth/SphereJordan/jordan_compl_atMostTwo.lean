import Mathlib
import Submission.Work.Topology.PlaneCurve.jordanRectSetup
import Submission.Work.Topology.PlaneCurve.frontier_component_eq_range
import Submission.Work.Smooth.SphereJordan.memClosureConnectedComponentIn
import Submission.Work.Smooth.JordanSeparation.phragmen_brouwer_of_square
import Submission.Work.Smooth.JordanSeparation.nonempty_planeSeparation
import Submission.Work.Smooth.SphereJordan.atMostTwoNormalized

/-!
# At most two components of the complement of a continuous simple closed plane curve

For a continuous `2π`-periodic curve `γ : ℝ → ℂ` which is injective on one period, the complement
of its trace has at most two connected components: of any three points off the trace, two lie in
the same component.

## Structure of the proof

* **Normalisation** (`exists_normalized`, `toUnitHomeo`, `exists_diam_pair`): taking two points of
  the trace at maximal distance and sending them to `-1` and `1` with a similarity puts the curve
  in "standard position": the trace passes through `±1` and lies otherwise in the open rectangle
  `(-1,1) × (-2,2)`.  The statement is transported along the similarity
  (`image_connectedComponentIn_homeomorph`, `image_connectedComponentIn_eq_iff`).

* **The normalised core** (`atMostTwo_of_normalized_aux`, the geometric heart, classical
  Maehara/Luisto argument): in standard position the boundary of the closed box `[-1,1] × [-2,2]`
  meets the trace only in `±1`, so every point outside the box lies in the unbounded complementary
  component `U∞` (as do the top and bottom edges); the vertical segment `{re = 0, |im| ≤ 2}` meets
  the trace by the crossing lemma, its topmost point `m` splits the trace into two arcs `J₁ ∋ m`
  and `J₂`, and the crossing lemma again shows that a certain bottom-to-top polygonal path
  `σ ⊆ J ∪ U ∪ U∞` (with `U` the component of a point whose small vertical window misses the
  trace) cuts the box into two pieces.  Any further complementary component `G` would have points
  near both `±1` (Maehara's lemma), hence a left-to-right path avoiding `σ` in the box,
  contradicting the crossing lemma.
-/

open Set

namespace Work.Smooth.SphereJordan

noncomputable section

/-! ## Normalising the curve

Composing with a similarity of the plane, we may assume that the trace of the curve passes through
`-1` and `1` and that every other point of the trace lies in the open rectangle
`(-1,1) × (-2,2)`: take two points of the trace at maximal distance and send them to `∓1`. -/

/-- The image of a connected component under a homeomorphism of the plane. -/
theorem image_connectedComponentIn_homeomorph (e : ℂ ≃ₜ ℂ) (s : Set ℂ) (x : ℂ) :
    e '' connectedComponentIn s x = connectedComponentIn (e '' s) (e x) := by
  by_cases hx : x ∈ s
  · refine Set.Subset.antisymm ?_ ?_
    · have hpre : IsPreconnected (e '' connectedComponentIn s x) :=
        isPreconnected_connectedComponentIn.image e e.continuous.continuousOn
      refine hpre.subset_connectedComponentIn ⟨x, mem_connectedComponentIn hx, rfl⟩ ?_
      rintro z ⟨y, hy, rfl⟩
      exact ⟨y, connectedComponentIn_subset s x hy, rfl⟩
    · have hpre : IsPreconnected (e.symm '' connectedComponentIn (e '' s) (e x)) :=
        isPreconnected_connectedComponentIn.image e.symm e.symm.continuous.continuousOn
      have hsub : e.symm '' connectedComponentIn (e '' s) (e x) ⊆ s := by
        rintro z ⟨y, hy, rfl⟩
        obtain ⟨w, hw, hwy⟩ := connectedComponentIn_subset (e '' s) (e x) hy
        rw [← hwy]
        simpa using hw
      have hxe : x ∈ e.symm '' connectedComponentIn (e '' s) (e x) :=
        ⟨e x, mem_connectedComponentIn ⟨x, hx, rfl⟩, by simp⟩
      intro z hz
      exact ⟨e.symm z,
        (hpre.subset_connectedComponentIn hxe hsub) ⟨z, hz, by simp⟩, by simp⟩
  · have hes : e x ∉ e '' s := by
      rintro ⟨y, hy, hyx⟩
      exact hx (by rw [← e.injective hyx]; exact hy)
    rw [connectedComponentIn_eq_empty hx, Set.image_empty, connectedComponentIn_eq_empty hes]

/-- The image of the complement of a set under a homeomorphism of the plane. -/
theorem image_compl_of_homeomorph (e : ℂ ≃ₜ ℂ) (F : Set ℂ) : e '' Fᶜ = (e '' F)ᶜ := by
  ext w
  constructor
  · rintro ⟨z, hz, rfl⟩ hcon
    obtain ⟨y, hy, hyz⟩ := hcon
    exact hz (by rwa [e.injective hyz] at hy)
  · intro hw
    exact ⟨e.symm w, fun h => hw ⟨e.symm w, h, by simp⟩, by simp⟩

/-- Two points lie in the same connected component of a set if and only if their images under a
homeomorphism of the plane do. -/
theorem image_connectedComponentIn_eq_iff (e : ℂ ≃ₜ ℂ) (C : Set ℂ) (u v : ℂ) :
    connectedComponentIn (e '' C) (e u) = connectedComponentIn (e '' C) (e v) ↔
      connectedComponentIn C u = connectedComponentIn C v := by
  constructor
  · intro h
    have h1 : e.symm '' connectedComponentIn (e '' C) (e u) =
        e.symm '' connectedComponentIn (e '' C) (e v) := congrArg _ h
    rw [image_connectedComponentIn_homeomorph e.symm (e '' C) (e u),
      image_connectedComponentIn_homeomorph e.symm (e '' C) (e v)] at h1
    have h2 : e.symm '' (e '' C) = C := by
      rw [Set.image_image]
      have : (fun x => e.symm (e x)) = id := funext (fun x => by simp)
      rw [this, Set.image_id]
    rw [h2] at h1
    simpa using h1
  · intro h
    rw [← image_connectedComponentIn_homeomorph e C u,
      ← image_connectedComponentIn_homeomorph e C v, h]

/-- **Two points of the trace at maximal distance.** -/
theorem exists_diam_pair {γ : ℝ → ℂ} (hcont : Continuous γ)
    (hper : Function.Periodic γ (2 * Real.pi)) (hinj : Set.InjOn γ (Set.Ico 0 (2 * Real.pi))) :
    ∃ a ∈ Set.range γ, ∃ b ∈ Set.range γ, a ≠ b ∧
      ∀ w ∈ Set.range γ, dist w a ≤ dist a b ∧ dist w b ≤ dist a b := by
  have hJc : IsCompact (Set.range γ) :=
    Work.Topology.PlaneCurve.isCompact_range_of_periodic hcont hper
  have hmem0 : γ 0 ∈ Set.range γ := ⟨0, rfl⟩
  have hmemπ : γ Real.pi ∈ Set.range γ := ⟨Real.pi, rfl⟩
  have hne : γ 0 ≠ γ Real.pi := by
    intro h
    have h0 : (0 : ℝ) ∈ Set.Ico 0 (2 * Real.pi) := ⟨le_refl 0, by positivity⟩
    have hπ : Real.pi ∈ Set.Ico 0 (2 * Real.pi) :=
      ⟨Real.pi_pos.le, by nlinarith [Real.pi_pos]⟩
    have := hinj h0 hπ h
    linarith [Real.pi_pos]
  obtain ⟨p, hp, hmax⟩ := (hJc.prod hJc).exists_isMaxOn
    (⟨(γ 0, γ Real.pi), hmem0, hmemπ⟩) continuous_dist.continuousOn
  refine ⟨p.1, hp.1, p.2, hp.2, ?_, ?_⟩
  · intro hab
    have h1 : dist (γ 0) (γ Real.pi) ≤ dist p.1 p.2 :=
      hmax (a := (γ 0, γ Real.pi)) ⟨hmem0, hmemπ⟩
    rw [hab, dist_self] at h1
    have h2 : 0 < dist (γ 0) (γ Real.pi) := dist_pos.mpr hne
    linarith
  · intro w hw
    exact ⟨hmax (a := (w, p.1)) ⟨hw, hp.1⟩,
      by simpa [dist_comm] using hmax (a := (p.2, w)) ⟨hp.2, hw⟩⟩

/-- The similarity of the plane sending `a` to `-1` and `b` to `1`. -/
noncomputable def toUnitHomeo (a b : ℂ) (hab : a ≠ b) : ℂ ≃ₜ ℂ where
  toFun z := (2 / (b - a)) * (z - (a + b) / 2)
  invFun w := w * (b - a) / 2 + (a + b) / 2
  left_inv z := by
    have hba : b - a ≠ 0 := sub_ne_zero.mpr hab.symm
    field_simp
    ring
  right_inv w := by
    have hba : b - a ≠ 0 := sub_ne_zero.mpr hab.symm
    field_simp
    ring
  continuous_toFun := by fun_prop
  continuous_invFun := by fun_prop

theorem toUnitHomeo_apply (a b z : ℂ) (hab : a ≠ b) :
    toUnitHomeo a b hab z = (2 / (b - a)) * (z - (a + b) / 2) := rfl

theorem toUnitHomeo_neg_one (a b : ℂ) (hab : a ≠ b) : toUnitHomeo a b hab a = -1 := by
  rw [toUnitHomeo_apply]
  have hba : b - a ≠ 0 := sub_ne_zero.mpr hab.symm
  field_simp
  ring

theorem toUnitHomeo_one (a b : ℂ) (hab : a ≠ b) : toUnitHomeo a b hab b = 1 := by
  rw [toUnitHomeo_apply]
  have hba : b - a ≠ 0 := sub_ne_zero.mpr hab.symm
  field_simp
  ring

theorem toUnitHomeo_sub_one (a b z : ℂ) (hab : a ≠ b) :
    toUnitHomeo a b hab z - 1 = (2 / (b - a)) * (z - b) := by
  rw [toUnitHomeo_apply]
  have hba : b - a ≠ 0 := sub_ne_zero.mpr hab.symm
  field_simp
  ring

theorem toUnitHomeo_add_one (a b z : ℂ) (hab : a ≠ b) :
    toUnitHomeo a b hab z + 1 = (2 / (b - a)) * (z - a) := by
  rw [toUnitHomeo_apply]
  have hba : b - a ≠ 0 := sub_ne_zero.mpr hab.symm
  field_simp
  ring

theorem toUnitHomeo_dist_one (a b z : ℂ) (hab : a ≠ b) :
    ‖toUnitHomeo a b hab z - 1‖ = 2 * dist z b / dist a b := by
  have h1 : ‖toUnitHomeo a b hab z - 1‖ = (2 / ‖b - a‖) * ‖z - b‖ := by
    rw [toUnitHomeo_sub_one, norm_mul, norm_div, Complex.norm_ofNat]
  rw [h1, Complex.dist_eq, Complex.dist_eq, ← norm_sub_rev b a]
  ring

theorem toUnitHomeo_dist_neg_one (a b z : ℂ) (hab : a ≠ b) :
    ‖toUnitHomeo a b hab z + 1‖ = 2 * dist z a / dist a b := by
  have h1 : ‖toUnitHomeo a b hab z + 1‖ = (2 / ‖b - a‖) * ‖z - a‖ := by
    rw [toUnitHomeo_add_one, norm_mul, norm_div, Complex.norm_ofNat]
  rw [h1, Complex.dist_eq, Complex.dist_eq, ← norm_sub_rev b a]
  ring

/-- Distance bounds for the normalised curve, in terms of the norm inequalities. -/
theorem toUnit_norm_bounds {a b z : ℂ} (hab : a ≠ b) (hzb : dist z b ≤ dist a b)
    (hza : dist z a ≤ dist a b) :
    ‖toUnitHomeo a b hab z - 1‖ ≤ 2 ∧ ‖toUnitHomeo a b hab z + 1‖ ≤ 2 := by
  have hd : 0 < dist a b := dist_pos.mpr hab
  constructor
  · rw [toUnitHomeo_dist_one, div_le_iff₀ hd]
    linarith
  · rw [toUnitHomeo_dist_neg_one, div_le_iff₀ hd]
    linarith

/-- The real/imaginary data of a point at distance `≤ 2` from both `-1` and `1`: the real part is
in `[-1,1]`, it is `±1` only for `w = ±1`, and the imaginary part is `< 2` in absolute value. -/
theorem re_im_data {w : ℂ} (h1 : ‖w - 1‖ ≤ 2) (h2 : ‖w + 1‖ ≤ 2) :
    |w.re| ≤ 1 ∧ (|w.re| = 1 → w = 1 ∨ w = -1) ∧ |w.im| < 2 := by
  have hsq : ∀ u : ℂ, ‖u‖ ≤ 2 → Complex.normSq u ≤ 4 := by
    intro u hu
    rw [Complex.normSq_eq_norm_sq]
    nlinarith [norm_nonneg u, hu]
  have hsq1 : (w.re - 1) ^ 2 + w.im ^ 2 ≤ 4 := by
    have h := hsq (w - 1) h1
    rw [show Complex.normSq (w - 1) = (w.re - 1) ^ 2 + w.im ^ 2 by
      simp [Complex.normSq_apply, Complex.sub_re, Complex.sub_im, Complex.one_re, Complex.one_im]
      ring] at h
    exact h
  have hsq2 : (w.re + 1) ^ 2 + w.im ^ 2 ≤ 4 := by
    have h := hsq (w + 1) h2
    rw [show Complex.normSq (w + 1) = (w.re + 1) ^ 2 + w.im ^ 2 by
      simp [Complex.normSq_apply, Complex.add_re, Complex.add_im, Complex.one_re, Complex.one_im]
      ring] at h
    exact h
  have hre : |w.re| ≤ 1 := by
    have h3 : |w.re - 1| ≤ 2 := by
      have := Complex.abs_re_le_norm (w - 1)
      rw [Complex.sub_re, Complex.one_re] at this
      exact le_trans this h1
    have h4 : |w.re + 1| ≤ 2 := by
      have := Complex.abs_re_le_norm (w + 1)
      rw [Complex.add_re, Complex.one_re] at this
      exact le_trans this h2
    rw [abs_le] at h3 h4 ⊢
    constructor <;> linarith
  have him : |w.im| < 2 := by
    rcases lt_trichotomy |w.im| 2 with h | h | h
    · exact h
    · exfalso
      rcases (abs_eq (by norm_num : (0 : ℝ) ≤ 2)).mp h with h' | h'
      · rw [h'] at hsq1 hsq2
        have h5 : (w.re - 1) ^ 2 = 0 := by nlinarith [sq_nonneg (w.re - 1)]
        have h6 : (w.re + 1) ^ 2 = 0 := by nlinarith [sq_nonneg (w.re + 1)]
        nlinarith [h5, h6]
      · rw [h'] at hsq1 hsq2
        have h5 : (w.re - 1) ^ 2 = 0 := by nlinarith [sq_nonneg (w.re - 1)]
        have h6 : (w.re + 1) ^ 2 = 0 := by nlinarith [sq_nonneg (w.re + 1)]
        nlinarith [h5, h6]
    · exfalso
      have h4 : w.im ^ 2 ≤ 4 := by nlinarith [sq_nonneg (w.re - 1)]
      have h5 : |w.im| ^ 2 ≤ 4 := by rwa [sq_abs]
      nlinarith [h]
  refine ⟨hre, ?_, him⟩
  intro heq
  rcases (abs_eq (by norm_num : (0 : ℝ) ≤ 1)).mp heq with h | h
  · have h3 : w.im = 0 := by
      rw [h] at hsq2
      nlinarith [sq_nonneg w.im]
    exact Or.inl (Complex.ext h (by rw [h3]; simp))
  · have h3 : w.im = 0 := by
      rw [h] at hsq1
      nlinarith [sq_nonneg w.im]
    exact Or.inr (Complex.ext h (by rw [h3]; simp))

/-- **Normalisation of a simple closed curve.**  After a similarity of the plane, the trace passes
through `-1` and `1` and all its remaining points lie in the open rectangle `(-1,1) × (-2,2)`. -/
theorem exists_normalized {γ : ℝ → ℂ} (hcont : Continuous γ)
    (hper : Function.Periodic γ (2 * Real.pi)) (hinj : Set.InjOn γ (Set.Ico 0 (2 * Real.pi))) :
    ∃ e : ℂ ≃ₜ ℂ, (∃ t : ℝ, (e ∘ γ) t = -1) ∧ (∃ t : ℝ, (e ∘ γ) t = 1) ∧
      (∀ w ∈ Set.range (e ∘ γ),
        w ∈ Work.Topology.PlaneCurve.rectR ∨ w = -1 ∨ w = 1) := by
  obtain ⟨a, ha, b, hb, hab, hmax⟩ := exists_diam_pair hcont hper hinj
  obtain ⟨sa, hsa⟩ := ha
  obtain ⟨sb, hsb⟩ := hb
  refine ⟨toUnitHomeo a b hab, ⟨sa, ?_⟩, ⟨sb, ?_⟩, ?_⟩
  · show toUnitHomeo a b hab (γ sa) = -1
    rw [hsa]
    exact toUnitHomeo_neg_one a b hab
  · show toUnitHomeo a b hab (γ sb) = 1
    rw [hsb]
    exact toUnitHomeo_one a b hab
  · rintro w ⟨t, rfl⟩
    change toUnitHomeo a b hab (γ t) ∈ Work.Topology.PlaneCurve.rectR ∨
      toUnitHomeo a b hab (γ t) = -1 ∨ toUnitHomeo a b hab (γ t) = 1
    obtain ⟨hza, hzb⟩ := hmax (γ t) ⟨t, rfl⟩
    obtain ⟨h1, h2⟩ := toUnit_norm_bounds (z := γ t) hab hzb hza
    obtain ⟨hre, hre1, him⟩ := re_im_data h1 h2
    rcases lt_trichotomy |(toUnitHomeo a b hab (γ t)).re| 1 with hlt | heq | hgt
    · exact Or.inl (by rw [abs_lt] at hlt him; exact ⟨hlt.1, hlt.2, him.1, him.2⟩)
    · rcases hre1 heq with h | h
      · exact Or.inr (Or.inr h)
      · exact Or.inr (Or.inl h)
    · exact absurd hgt (not_lt.mpr hre)

/-- Traces of `γ` and of a parameter shift agree. -/
theorem range_shift (γ : ℝ → ℂ) (s : ℝ) :
    Set.range (fun t : ℝ => γ (t + s)) = Set.range γ := by
  ext w
  constructor
  · rintro ⟨t, rfl⟩
    exact ⟨t + s, rfl⟩
  · rintro ⟨u, rfl⟩
    exact ⟨u - s, by ring_nf⟩

/-- Injectivity on one period is preserved by a shift of the parameter. -/
theorem injOn_shift_add {γ : ℝ → ℂ} (hper : Function.Periodic γ (2 * Real.pi))
    (hinj : Set.InjOn γ (Set.Ico 0 (2 * Real.pi))) (s : ℝ) :
    Set.InjOn (fun t : ℝ => γ (t + s)) (Set.Ico 0 (2 * Real.pi)) := by
  intro u hu v hv huv
  obtain ⟨k, hk⟩ := exists_int_sub_eq_of_periodic_injOn hper hinj huv
  have h1 : u - v = (k : ℝ) * (2 * Real.pi) := by
    have : (u + s) - (v + s) = u - v := by ring
    rw [this] at hk
    exact hk
  have h2 : |u - v| < 2 * Real.pi := by
    rw [abs_lt]
    constructor <;> linarith [hu.1, hu.2, hv.1, hv.2]
  have hk0 : k = 0 := by
    by_contra hkne
    have h3 : (1 : ℝ) ≤ |(k : ℝ)| := by
      rw [← Int.cast_abs]
      exact_mod_cast Int.one_le_abs hkne
    have h4 : 2 * Real.pi ≤ |u - v| := by
      rw [h1, abs_mul, abs_of_pos (by positivity : (0 : ℝ) < 2 * Real.pi)]
      nlinarith [h3, Real.pi_pos]
    linarith
  rw [hk0] at h1
  simp only [Int.cast_zero, zero_mul] at h1
  linarith

/-! ## The two cases of the target -/

theorem jordan_compl_atMostTwo {γ : ℝ → ℂ} (hcont : Continuous γ)
    (hper : Function.Periodic γ (2 * Real.pi)) (hinj : Set.InjOn γ (Set.Ico 0 (2 * Real.pi)))
    {x y z : ℂ} (hx : x ∉ Set.range γ) (hy : y ∉ Set.range γ) (hz : z ∉ Set.range γ) :
    connectedComponentIn (Set.range γ)ᶜ x = connectedComponentIn (Set.range γ)ᶜ y ∨
    connectedComponentIn (Set.range γ)ᶜ x = connectedComponentIn (Set.range γ)ᶜ z ∨
    connectedComponentIn (Set.range γ)ᶜ y = connectedComponentIn (Set.range γ)ᶜ z := by
  classical
  by_cases hdis : IsPreconnected (Set.range γ)ᶜ
  · exact Or.inl (by rw [hdis.connectedComponentIn hx, hdis.connectedComponentIn hy])
  · -- normalise the curve and move the origin to `-1`
    obtain ⟨e, hneg, hpos, hsub⟩ := exists_normalized hcont hper hinj
    obtain ⟨s, hs⟩ := hneg
    set γ' : ℝ → ℂ := fun t => (e ∘ γ) (t + s) with hγ'def
    have hrange : Set.range γ' = Set.range (e ∘ γ) := range_shift (e ∘ γ) s
    have hcont' : Continuous γ' := (e.continuous.comp hcont).comp (by fun_prop)
    have hcomp_per : Function.Periodic (e ∘ γ) (2 * Real.pi) := fun t => by
      show e (γ (t + 2 * Real.pi)) = e (γ t)
      rw [hper]
    have hcomp_inj : Set.InjOn (e ∘ γ) (Set.Ico 0 (2 * Real.pi)) := fun u hu v hv huv =>
      hinj hu hv (e.injective huv)
    have hper' : Function.Periodic γ' (2 * Real.pi) := by
      intro t
      show (e ∘ γ) (t + 2 * Real.pi + s) = (e ∘ γ) (t + s)
      rw [show t + 2 * Real.pi + s = (t + s) + 2 * Real.pi by ring]
      exact hcomp_per (t + s)
    have hinj' : Set.InjOn γ' (Set.Ico 0 (2 * Real.pi)) :=
      injOn_shift_add hcomp_per hcomp_inj s
    have hzero' : γ' 0 = -1 := by
      show (e ∘ γ) (0 + s) = -1
      rw [zero_add]
      exact hs
    have hpos' : 1 ∈ Set.range γ' := by
      rw [hrange]
      exact hpos
    have hsub' : ∀ w ∈ Set.range γ', w ∈ Work.Topology.PlaneCurve.rectR ∨ w = -1 ∨ w = 1 := by
      intro w hw
      rw [hrange] at hw
      exact hsub w hw
    have key := atMostTwoNormalized hcont' hper' hinj' hzero' hpos' hsub'
    -- transfer back along the similarity
    have hnotmem : ∀ u : ℂ, u ∉ Set.range γ → e u ∉ Set.range γ' := by
      intro u hu hcon
      rw [hrange] at hcon
      obtain ⟨t, ht⟩ := hcon
      exact hu ⟨t, e.injective ht⟩
    have hx' : e x ∉ Set.range γ' := hnotmem x hx
    have hy' : e y ∉ Set.range γ' := hnotmem y hy
    have hz' : e z ∉ Set.range γ' := hnotmem z hz
    have htransfer : ∀ u v : ℂ,
        connectedComponentIn (Set.range γ')ᶜ (e u) = connectedComponentIn (Set.range γ')ᶜ (e v) →
        connectedComponentIn (Set.range γ)ᶜ u = connectedComponentIn (Set.range γ)ᶜ v := by
      intro u v huv
      rw [hrange, Set.range_comp, ← image_compl_of_homeomorph e (Set.range γ)] at huv
      exact (image_connectedComponentIn_eq_iff e (Set.range γ)ᶜ u v).mp huv
    rcases key (e x) (e y) (e z) hx' hy' hz' with h | h | h
    · exact Or.inl (htransfer x y h)
    · exact Or.inr (Or.inl (htransfer x z h))
    · exact Or.inr (Or.inr (htransfer y z h))


end

end Work.Smooth.SphereJordan
