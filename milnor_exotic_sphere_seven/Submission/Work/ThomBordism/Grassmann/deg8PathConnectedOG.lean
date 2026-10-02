import Mathlib
import Submission.Work.ThomBordism.Grassmann.Grassmannian

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false
set_option maxHeartbeats 2000000
set_option backward.isDefEq.respectTransparency false

/-!
# The oriented Grassmannian `G̃r_k(ℝ^{k+m})` is path connected

`Work.ThomBordism.Grassmann.OG k m` is the quotient of the Stiefel manifold `V_k(ℝ^{k+m})` of
orthonormal `k`-frames by the action of `SO(k)`; it is the space of *oriented* `k`-dimensional
subspaces of `ℝ^{k+m}`.  This module proves that it is path connected (for `1 ≤ m`), and the proof
goes through the Stiefel manifold:

* `joined_frames`: for every finite-dimensional real inner product space `E` and every `k` with
  `k + 1 ≤ finrank ℝ E`, any two orthonormal `k`-frames in `E` are joined by a path of orthonormal
  `k`-frames.

The argument is an induction on `k`.  The key geometric step is elementary: if `f` is an orthonormal
`(k+1)`-frame with first vector `a` and `v` is a unit vector with `v ≠ a`, then deforming the
reflection vector `c` (chosen orthogonal to `a`) to `‖a - v‖⁻¹ • (a - v)` along the unit sphere gives
a one-parameter family of isometries `Φ_t = reflect (γ t) ∘ reflect c` with `Φ_0 = id` and
`Φ_1 a = v`; applying it to `f` aligns the first vector with `v` without destroying orthonormality.
The remaining `k` vectors are then frames in the orthogonal complement of `v`, where the induction
hypothesis applies.

`Work.ThomBordism.Grassmann.deg8PathConnectedOG` is the case `E = ℝ^{k+m}` combined with the
quotient map `V_k(ℝ^{k+m}) → G̃r_k(ℝ^{k+m})`.
-/

namespace Work.ThomBordism.Grassmann

open scoped Topology

noncomputable section

/-! ## Reflection in the hyperplane orthogonal to a unit vector -/

section Reflect

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- The reflection of `x` in the hyperplane `{y | ⟪y,u⟫ = 0}`, written out explicitly (it needs no
completeness assumption on the hyperplane). -/
def reflect (u x : E) : E := x - (2 * inner ℝ x u) • u

/-- `reflect u` preserves the inner product when `u` is a unit vector. -/
lemma reflect_inner {u x y : E} (hu : ‖u‖ = 1) :
    inner ℝ (reflect u x) (reflect u y) = inner ℝ x y := by
  have huu : inner ℝ u u = 1 := by rw [real_inner_self_eq_norm_sq, hu]; norm_num
  have huy : inner ℝ u y = inner ℝ y u := (real_inner_comm u y).symm
  simp only [reflect, inner_sub_left, inner_sub_right, inner_smul_left, inner_smul_right,
    starRingEnd_apply, star_trivial]
  rw [huu, huy]
  ring

/-- `reflect u` is an involution when `u` is a unit vector. -/
lemma reflect_self {u x : E} (hu : ‖u‖ = 1) : reflect u (reflect u x) = x := by
  have huu : inner ℝ u u = 1 := by rw [real_inner_self_eq_norm_sq, hu]; norm_num
  have h : inner ℝ (x - (2 * inner ℝ x u) • u) u = - inner ℝ x u := by
    simp only [inner_sub_left, inner_smul_left, starRingEnd_apply, star_trivial]
    rw [huu]
    ring
  simp only [reflect, h]
  module

/-- The reflection in the hyperplane orthogonal to `u` fixes every vector orthogonal to `u`. -/
lemma reflect_of_inner_zero {u a : E} (h : inner ℝ a u = 0) : reflect u a = a := by
  simp [reflect, h]

/-- Two reflections in hyperplanes orthogonal to unit vectors preserve the inner product. -/
lemma inner_reflect_reflect {u c x y : E} (hu : ‖u‖ = 1) (hc : ‖c‖ = 1) :
    inner ℝ (reflect u (reflect c x)) (reflect u (reflect c y)) = inner ℝ x y := by
  rw [reflect_inner hu, reflect_inner hc]

/-- The norm is preserved by a reflection. -/
lemma norm_reflect {u x : E} (hu : ‖u‖ = 1) : ‖reflect u x‖ = ‖x‖ := by
  have h : ‖reflect u x‖ ^ 2 = ‖x‖ ^ 2 := by
    rw [← real_inner_self_eq_norm_sq, reflect_inner hu, real_inner_self_eq_norm_sq]
  nlinarith [norm_nonneg (reflect u x), norm_nonneg x]

lemma continuous_reflect_apply {α : Type*} [TopologicalSpace α] {A : α → E} {x : E}
    (hA : Continuous A) : Continuous fun t => reflect (A t) x := by
  simp only [reflect]
  fun_prop

end Reflect

/-! ## The end point of the alignment -/

section Align

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- The unit vector `‖a - v‖⁻¹ • (a - v)` defining the reflection that moves `a` to `v`. -/
def alignEnd (a v : E) : E := ‖a - v‖⁻¹ • (a - v)

lemma norm_alignEnd {a v : E} (hne : v ≠ a) : ‖alignEnd a v‖ = 1 := by
  have hne' : a - v ≠ 0 := sub_ne_zero.mpr (Ne.symm hne)
  rw [alignEnd]
  exact norm_smul_inv_norm (𝕜 := ℝ) hne'

lemma norm_sub_sq_eq {a v : E} (ha : ‖a‖ = 1) (hv : ‖v‖ = 1) :
    ‖a - v‖ ^ 2 = 2 - 2 * inner ℝ a v := by
  rw [norm_sub_sq_real, ha, hv]
  ring

/-- The reflection in the hyperplane orthogonal to `alignEnd a v` sends `a` to `v`. -/
lemma reflect_alignEnd {a v : E} (ha : ‖a‖ = 1) (hv : ‖v‖ = 1) (hne : v ≠ a) :
    reflect (alignEnd a v) a = v := by
  have hne' : a - v ≠ 0 := sub_ne_zero.mpr (Ne.symm hne)
  have hnorm : ‖a - v‖ ≠ 0 := norm_ne_zero_iff.mpr hne'
  have hinner : inner ℝ a (a - v) = 1 - inner ℝ a v := by
    rw [inner_sub_right, real_inner_self_eq_norm_sq, ha]; ring
  have hkey : 2 * inner ℝ a (alignEnd a v) = ‖a - v‖ := by
    rw [alignEnd, inner_smul_right, hinner]
    field_simp
    rw [norm_sub_sq_eq (a := a) (v := v) ha hv]
    ring
  rw [reflect, hkey, alignEnd, smul_smul, mul_inv_cancel₀ hnorm, one_smul]
  module

/-- Any two unit vectors of `E` are joined by a continuous path of unit vectors, as soon as
`E` has dimension at least two. -/
lemma exists_unit_path {c d : E} (hc : ‖c‖ = 1) (hd : ‖d‖ = 1)
    (hrank : 1 < Module.rank ℝ E) :
    ∃ γ : C(unitInterval, E), γ 0 = c ∧ γ 1 = d ∧ ∀ t, ‖γ t‖ = 1 := by
  have hc' : c ∈ Metric.sphere (0 : E) 1 := by
    rw [Metric.mem_sphere, dist_eq_norm]; simpa using hc
  have hd' : d ∈ Metric.sphere (0 : E) 1 := by
    rw [Metric.mem_sphere, dist_eq_norm]; simpa using hd
  have hpc : IsPathConnected (Metric.sphere (0 : E) 1) :=
    isPathConnected_sphere hrank (0 : E) (r := 1) (by norm_num)
  obtain ⟨γ⟩ := (joinedIn_iff_joined hc' hd').mp (hpc.joinedIn c hc' d hd')
  refine ⟨⟨fun t => (γ t : E), continuous_subtype_val.comp γ.continuous⟩, ?_, ?_, ?_⟩
  · exact congrArg Subtype.val γ.source
  · exact congrArg Subtype.val γ.target
  · intro t
    have h := (γ t).2
    rw [Metric.mem_sphere, dist_eq_norm] at h
    simpa using h

/-- Given a unit vector `a` in a space of dimension `≥ 2`, there is a unit vector orthogonal
to it. -/
lemma exists_unit_orthogonal [FiniteDimensional ℝ E] (a : E) (ha : ‖a‖ = 1)
    (hdim : 2 ≤ Module.finrank ℝ E) :
    ∃ c : E, ‖c‖ = 1 ∧ inner ℝ c a = 0 := by
  have ha0 : a ≠ 0 := by
    intro h0
    rw [h0, norm_zero] at ha
    exact one_ne_zero ha.symm
  have hsum := Submodule.finrank_add_finrank_orthogonal (𝕜 := ℝ) (E := E) (ℝ ∙ a)
  rw [finrank_span_singleton ha0] at hsum
  have hfin : 1 ≤ Module.finrank ℝ ↥((ℝ ∙ a)ᗮ) := by omega
  have hne : (ℝ ∙ a)ᗮ ≠ ⊥ := by
    intro h
    rw [h, finrank_bot] at hfin
    omega
  obtain ⟨w, hw, hw0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hne
  refine ⟨‖w‖⁻¹ • w, ?_, ?_⟩
  · exact norm_smul_inv_norm (𝕜 := ℝ) hw0
  · have hmem : inner ℝ w a = 0 := (Submodule.mem_orthogonal_singleton_iff_inner_left.mp hw)
    simp [inner_smul_left, hmem]

end Align

/-! ## Index bookkeeping: prepending a vector to a tuple -/

section ConsFun

variable {E : Type*}

/-- The tuple `(v, g 0, g 1, …)` obtained by prepending `v` to `g`. -/
def consFun (v : E) {k : ℕ} (g : Fin k → E) : Fin (k+1) → E :=
  fun i => Fin.cases (motive := fun _ => E) v g i

@[simp] lemma consFun_zero (v : E) {k : ℕ} (g : Fin k → E) : consFun v g 0 = v := rfl

@[simp] lemma consFun_succ (v : E) {k : ℕ} (g : Fin k → E) (i : Fin k) :
    consFun v g i.succ = g i := rfl

/-- Prepending the first term of a tuple to its tail recovers the tuple. -/
lemma consFun_tail {k : ℕ} (f : Fin (k+1) → E) : consFun (f 0) (fun i => f i.succ) = f := by
  funext i
  induction i using Fin.cases with
  | zero => rfl
  | succ i => rfl

lemma continuous_consFun {k : ℕ} [TopologicalSpace E] :
    Continuous fun p : E × (Fin k → E) => consFun p.1 p.2 := by
  refine continuous_pi fun i => ?_
  induction i using Fin.cases with
  | zero => simp only [consFun_zero]; exact continuous_fst
  | succ i => simp only [consFun_succ]; exact (continuous_apply i).comp continuous_snd

end ConsFun

/-! ## Orthonormal frames, tails and conses -/

section Frames

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- The type of orthonormal `k`-frames in `E`. -/
abbrev ONFrames (k : ℕ) (E : Type*) [NormedAddCommGroup E] [InnerProductSpace ℝ E] :=
  {f : Fin k → E // Orthonormal ℝ f}

variable {k : ℕ}

/-- The tail of an orthonormal `(k+1)`-frame, as an orthonormal `k`-frame in the orthogonal
complement of a vector `v` orthogonal to all its members. -/
def tailAt (f : ONFrames (k+1) E) (v : E) (hv : ∀ i : Fin k, inner ℝ v (f.1 i.succ) = 0) :
    ONFrames k ↥((ℝ ∙ v)ᗮ) :=
  ⟨fun i => ⟨f.1 i.succ, by
      rw [Submodule.mem_orthogonal_singleton_iff_inner_left]
      exact (real_inner_comm v (f.1 i.succ)).trans (hv i)⟩,
    by
      rw [orthonormal_iff_ite]
      intro i j
      have h := (orthonormal_iff_ite.mp f.2) i.succ j.succ
      simpa [Submodule.coe_inner, Fin.succ_inj] using h⟩

/-- The tail of an orthonormal `(k+1)`-frame, in the orthogonal complement of its first vector. -/
def tailFrame (f : ONFrames (k+1) E) : ONFrames k ↥((ℝ ∙ f.1 0)ᗮ) :=
  tailAt f (f.1 0) fun i => f.2.2 (Fin.succ_ne_zero i).symm

/-- Prepending a unit vector to an orthonormal `k`-frame lying in its orthogonal complement. -/
def consFrame (v : E) (hv : ‖v‖ = 1) (g : ONFrames k ↥((ℝ ∙ v)ᗮ)) : ONFrames (k+1) E :=
  ⟨consFun v (fun i => (g.1 i : E)),
    by
      rw [orthonormal_iff_ite]
      intro i j
      induction i using Fin.cases with
      | zero =>
        induction j using Fin.cases with
        | zero => simp [consFun_zero, hv]
        | succ j =>
          rw [consFun_zero, consFun_succ, if_neg (Fin.succ_ne_zero j).symm]
          have hmem := (g.1 j).2
          rw [Submodule.mem_orthogonal_singleton_iff_inner_left] at hmem
          rwa [real_inner_comm]
      | succ i =>
        induction j using Fin.cases with
        | zero =>
          rw [consFun_zero, consFun_succ, if_neg (Fin.succ_ne_zero i)]
          have hmem := (g.1 i).2
          rw [Submodule.mem_orthogonal_singleton_iff_inner_left] at hmem
          exact hmem
        | succ j =>
          rw [consFun_succ, consFun_succ]
          by_cases hij : i = j
          · subst hij
            have h := (orthonormal_iff_ite.mp g.2) i i
            simp only [↓reduceIte] at h
            simpa [Submodule.coe_inner] using h
          · have h := (orthonormal_iff_ite.mp g.2) i j
            rw [if_neg (fun hh => hij (Fin.succ_inj.mp hh))]
            simpa [Submodule.coe_inner, hij] using h⟩

/-- Prepending the first vector of a frame to its own tail recovers the frame. -/
lemma consFrame_tailAt (f : ONFrames (k+1) E) (v : E) (hv : f.1 0 = v)
    (horth : ∀ i : Fin k, inner ℝ v (f.1 i.succ) = 0) (hvn : ‖v‖ = 1) :
    consFrame v hvn (tailAt f v horth) = f := by
  refine Subtype.ext ?_
  show consFun v (fun i => ((tailAt f v horth).1 i : E)) = f.1
  funext i
  induction i using Fin.cases with
  | zero => simp only [consFun_zero]; exact hv.symm
  | succ i => simp only [consFun_succ]; rfl

/-- Prepending a fixed unit vector is continuous. -/
lemma continuous_consFrame (v : E) (hv : ‖v‖ = 1) :
    Continuous (consFrame (k := k) v hv) := by
  unfold consFrame
  refine Continuous.subtype_mk ?_ _
  refine continuous_pi fun i => ?_
  induction i using Fin.cases with
  | zero => simp only [consFun_zero]; exact continuous_const
  | succ i =>
    simp only [consFun_succ]
    exact continuous_subtype_val.comp ((continuous_apply i).comp continuous_subtype_val)

lemma joined_cons {v : E} (hv : ‖v‖ = 1) {g₁ g₂ : ONFrames k ↥((ℝ ∙ v)ᗮ)}
    (h : Joined g₁ g₂) : Joined (consFrame v hv g₁) (consFrame v hv g₂) :=
  h.map (continuous_consFrame v hv)

end Frames

/-! ## The alignment step -/

section AlignStep

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
variable {k : ℕ}

/-- **The alignment step.**  If `f` is an orthonormal `(k+1)`-frame with first vector `a`, if `c` is
a unit vector orthogonal to `a`, and `v ≠ a` is a unit vector, then `f` is joined to a frame `F₁`
whose first vector is `v` and all of whose remaining vectors are orthogonal to `v`. -/
lemma exists_joined_align (f : ONFrames (k+1) E) (c v : E) (hc : ‖c‖ = 1)
    (hc0 : inner ℝ c (f.1 0) = 0) (hv : ‖v‖ = 1) (hne : v ≠ f.1 0)
    (hrank : 1 < Module.rank ℝ E) :
    ∃ F₁ : ONFrames (k+1) E, F₁.1 0 = v ∧ (∀ i : Fin k, inner ℝ v (F₁.1 i.succ) = 0) ∧
      Joined f F₁ := by
  obtain ⟨γ, hγ0, hγ1, hγnorm⟩ := exists_unit_path hc (norm_alignEnd hne) hrank
  have hON : ∀ t : unitInterval, Orthonormal ℝ (fun i => reflect (γ t) (reflect c (f.1 i))) := by
    intro t
    rw [orthonormal_iff_ite]
    intro i j
    rw [inner_reflect_reflect (hγnorm t) hc]
    exact (orthonormal_iff_ite.mp f.2) i j
  have hkey1 : reflect (γ 1) (reflect c (f.1 0)) = v := by
    rw [hγ1]
    rw [reflect_of_inner_zero (u := c) (a := f.1 0)
      ((real_inner_comm (f.1 0) c).symm.trans hc0)]
    exact reflect_alignEnd (f.2.1 0) hv hne
  have hkey2 : ∀ i : Fin k, inner ℝ v (reflect (γ 1) (reflect c (f.1 i.succ))) = 0 := by
    intro i
    rw [← hkey1, inner_reflect_reflect (hγnorm 1) hc]
    exact f.2.2 (fun h => Fin.succ_ne_zero i h.symm)
  refine ⟨⟨fun i => reflect (γ 1) (reflect c (f.1 i)), hON 1⟩, hkey1, hkey2, ?_⟩
  refine ⟨⟨⟨fun t => ⟨fun i => reflect (γ t) (reflect c (f.1 i)), hON t⟩, ?_⟩, ?_, ?_⟩⟩
  · refine Continuous.subtype_mk ?_ _
    refine continuous_pi fun i => ?_
    exact continuous_reflect_apply γ.continuous (x := reflect c (f.1 i))
  · exact Subtype.ext (funext fun i => by
      show reflect (γ 0) (reflect c (f.1 i)) = f.1 i
      rw [hγ0]
      exact reflect_self hc)
  · rfl

end AlignStep

/-! ## The Stiefel manifold of a finite-dimensional inner product space is path connected -/

section Main

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]

/-- **Any two orthonormal `k`-frames are joined by a path of orthonormal `k`-frames**, provided
`k + 1 ≤ finrank ℝ E` (this is the statement that the Stiefel manifold `V_k(E)` is path connected
in the range where it is). -/
theorem joined_frames (k : ℕ) :
    ∀ (E : Type*) [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E],
      k + 1 ≤ Module.finrank ℝ E → ∀ f g : ONFrames k E, Joined f g := by
  induction k with
  | zero =>
    intro E _ _ _ _ f g
    have h : f = g := Subtype.ext (funext fun i => i.elim0)
    exact h ▸ Joined.refl g
  | succ k ih =>
    intro E _ _ _ hk f g
    have hE2 : 2 ≤ Module.finrank ℝ E := by omega
    have hrank : 1 < Module.rank ℝ E := by
      rw [← Module.finrank_eq_rank]
      exact_mod_cast hE2
    by_cases hva : g.1 0 = f.1 0
    · -- the two frames have the same first vector: reduce to the tails
      haveI hsub : k + 1 ≤ Module.finrank ℝ ↥((ℝ ∙ f.1 0)ᗮ) := by
        have hsum := Submodule.finrank_add_finrank_orthogonal (𝕜 := ℝ) (E := E) (ℝ ∙ f.1 0)
        have ha0 : f.1 0 ≠ 0 := by
          intro h0
          have h1 := f.2.1 0
          rw [h0, norm_zero] at h1
          exact one_ne_zero h1.symm
        rw [finrank_span_singleton ha0] at hsum
        omega
      have horth_f : ∀ i : Fin k, inner ℝ (f.1 0) (f.1 i.succ) = 0 :=
        fun i => f.2.2 (Fin.succ_ne_zero i).symm
      have horth_g : ∀ i : Fin k, inner ℝ (f.1 0) (g.1 i.succ) = 0 := by
        intro i
        rw [← hva]
        exact g.2.2 (Fin.succ_ne_zero i).symm
      have htail : Joined (tailAt f (f.1 0) horth_f) (tailAt g (f.1 0) horth_g) :=
        ih ↥((ℝ ∙ f.1 0)ᗮ) hsub _ _
      have h₁ : consFrame (f.1 0) (f.2.1 0) (tailAt f (f.1 0) horth_f) = f :=
        consFrame_tailAt f (f.1 0) rfl horth_f (f.2.1 0)
      have h₂ : consFrame (f.1 0) (f.2.1 0) (tailAt g (f.1 0) horth_g) = g :=
        consFrame_tailAt g (f.1 0) hva horth_g (f.2.1 0)
      obtain ⟨γ⟩ := joined_cons (f.2.1 0) htail
      exact ⟨γ.cast h₁.symm h₂.symm⟩
    · -- the first vectors differ: align the first vector, then use the induction hypothesis
      obtain ⟨c, hc, hc0⟩ := exists_unit_orthogonal (f.1 0) (f.2.1 0) hE2
      obtain ⟨F₁, hF₁0, hF₁orth, hjoin₁⟩ :=
        exists_joined_align f c (g.1 0) hc hc0 (g.2.1 0) hva hrank
      haveI hsub : k + 1 ≤ Module.finrank ℝ ↥((ℝ ∙ g.1 0)ᗮ) := by
        have hsum := Submodule.finrank_add_finrank_orthogonal (𝕜 := ℝ) (E := E) (ℝ ∙ g.1 0)
        have ha0 : g.1 0 ≠ 0 := by
          intro h0
          have h1 := g.2.1 0
          rw [h0, norm_zero] at h1
          exact one_ne_zero h1.symm
        rw [finrank_span_singleton ha0] at hsum
        omega
      have htail : Joined (tailAt F₁ (g.1 0) hF₁orth) (tailFrame g) :=
        ih ↥((ℝ ∙ g.1 0)ᗮ) hsub _ _
      have h₁ : consFrame (g.1 0) (g.2.1 0) (tailAt F₁ (g.1 0) hF₁orth) = F₁ :=
        consFrame_tailAt F₁ (g.1 0) hF₁0 hF₁orth (g.2.1 0)
      have h₂ : consFrame (g.1 0) (g.2.1 0) (tailFrame g) = g := by
        rw [tailFrame]
        exact consFrame_tailAt g (g.1 0) rfl
          (fun i => g.2.2 (Fin.succ_ne_zero i).symm) (g.2.1 0)
      obtain ⟨γ⟩ := joined_cons (g.2.1 0) htail
      exact hjoin₁.trans ⟨γ.cast h₁.symm h₂.symm⟩

end Main

/-! ## The oriented Grassmannian -/

/-- **The oriented Grassmannian `G̃r_k(ℝ^{k+m})` is path connected** (for `1 ≤ m`), because it is a
continuous image of the path connected Stiefel manifold `V_k(ℝ^{k+m})`. -/
theorem deg8PathConnectedOG (k m : ℕ) (hm : 1 ≤ m) :
    PathConnectedSpace (Work.ThomBordism.Grassmann.OG k m) := by
  haveI hpc : PathConnectedSpace (Stiefel k m) :=
    PathConnectedSpace.mk (nonempty_stiefel k m)
      (fun f g => joined_frames k (Amb (k + m)) (by simp [Amb]; omega) f g)
  refine PathConnectedSpace.mk
    ⟨ogMk k m (Classical.choice (nonempty_stiefel k m))⟩ fun x y => ?_
  refine Quotient.inductionOn x fun fx => ?_
  refine Quotient.inductionOn y fun fy => ?_
  exact (PathConnectedSpace.joined fx fy).map (ogMk k m).continuous

end

end Work.ThomBordism.Grassmann
