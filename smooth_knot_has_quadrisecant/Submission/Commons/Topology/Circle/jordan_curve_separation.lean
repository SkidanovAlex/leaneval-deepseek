import Mathlib
import Submission.Commons.Topology.Jordan.plane_separation
set_option autoImplicit false
open scoped RealInnerProductSpace
open scoped Topology
open Filter

namespace Commons.Topology.Circle

open _root_.Circle

noncomputable def loopLift (f : C(Circle, Circle)) : C(ℝ, ℝ) :=
  Classical.choose (Circle.isCoveringMap_exp.existsUnique_continuousMap_lifts
    (f.comp Circle.exp) 0 (Complex.arg (f 1 : ℂ)) (by
      rw [Circle.exp_arg]; simp [ContinuousMap.comp_apply, Circle.exp_zero]))

lemma loopLift_zero (f : C(Circle, Circle)) : (loopLift f) 0 = Complex.arg (f 1 : ℂ) :=
  (Classical.choose_spec (Circle.isCoveringMap_exp.existsUnique_continuousMap_lifts
    (f.comp Circle.exp) 0 (Complex.arg (f 1 : ℂ)) (by
      rw [Circle.exp_arg]; simp [ContinuousMap.comp_apply, Circle.exp_zero]))).1.1

lemma loopLift_lifts (f : C(Circle, Circle)) :
    Circle.exp ∘ (loopLift f) = ⇑(f.comp Circle.exp) :=
  (Classical.choose_spec (Circle.isCoveringMap_exp.existsUnique_continuousMap_lifts
    (f.comp Circle.exp) 0 (Complex.arg (f 1 : ℂ)) (by
      rw [Circle.exp_arg]; simp [ContinuousMap.comp_apply, Circle.exp_zero]))).1.2

lemma loopLift_unique (f : C(Circle, Circle)) (F : C(ℝ, ℝ))
    (h0 : F 0 = Complex.arg (f 1 : ℂ)) (hlift : Circle.exp ∘ F = ⇑(f.comp Circle.exp)) :
    F = loopLift f :=
  ((Classical.choose_spec (Circle.isCoveringMap_exp.existsUnique_continuousMap_lifts
    (f.comp Circle.exp) 0 (Complex.arg (f 1 : ℂ)) (by
      rw [Circle.exp_arg]; simp [ContinuousMap.comp_apply, Circle.exp_zero]))).2 F ⟨h0, hlift⟩)

lemma loopLift_apply (f : C(Circle, Circle)) (t : ℝ) :
    Circle.exp ((loopLift f) t) = f (Circle.exp t) := by
  have h := congr_fun (loopLift_lifts f) t
  simpa [ContinuousMap.comp_apply] using h

lemma exists_loopLift_period (f : C(Circle, Circle)) :
    ∃ m : ℤ, (loopLift f) (2 * Real.pi) = (loopLift f) 0 + m * (2 * Real.pi) := by
  rw [← Circle.exp_eq_exp, loopLift_apply, loopLift_apply, Circle.exp_two_pi, Circle.exp_zero]

noncomputable def loopDegree (f : C(Circle, Circle)) : ℤ :=
  Classical.choose (exists_loopLift_period f)

lemma loopLift_period (f : C(Circle, Circle)) :
    (loopLift f) (2 * Real.pi) = (loopLift f) 0 + (loopDegree f) * (2 * Real.pi) :=
  Classical.choose_spec (exists_loopLift_period f)

lemma zsmul_range_sep {c : ℝ} (hc : 0 < c) {a b : ℝ}
    (ha : ∃ m : ℤ, a = m * c) (hb : ∃ m : ℤ, b = m * c) (hab : |a - b| < c) : a = b := by
  obtain ⟨m, rfl⟩ := ha
  obtain ⟨n, rfl⟩ := hb
  have hab' : |((m : ℝ) - (n : ℝ)) * c| < c := by
    convert hab using 2
    ring
  rw [abs_mul, abs_of_pos hc] at hab'
  have h2 : |((m : ℝ) - (n : ℝ))| < 1 := by nlinarith [abs_nonneg ((m:ℝ) - (n:ℝ)), hab', hc]
  have h2' : ((|m - n| : ℤ) : ℝ) < 1 := by
    rw [Int.cast_abs]; push_cast; exact h2
  have h3 : |(m - n : ℤ)| < 1 := by exact_mod_cast h2'
  have hmn : m = n := by
    by_contra hne
    have := Int.one_le_abs (sub_ne_zero.mpr hne)
    omega
  rw [show (m : ℝ) = n from by exact_mod_cast hmn]

lemma eq_const_mul_of_sub_mem {X : Type*} [PseudoMetricSpace X] [PreconnectedSpace X]
    [Nonempty X] {c : ℝ} (hc : 0 < c) {f : C(X, ℝ)} (hf : ∀ x, ∃ m : ℤ, f x = m * c) :
    ∃ m : ℤ, ∀ x, f x = m * c := by
  obtain ⟨x₀⟩ := (inferInstance : Nonempty X)
  obtain ⟨m₀, hm₀⟩ := hf x₀
  refine ⟨m₀, fun x => ?_⟩
  have hopen : IsOpen {y | f y = m₀ * c} := by
    rw [isOpen_iff_mem_nhds]
    intro y hy
    have hyc : f y = m₀ * c := hy
    obtain ⟨δ, hδ, hδ'⟩ := (Metric.continuousAt_iff.mp (f.continuous.continuousAt (x := y))) (c/2) (by linarith)
    refine Filter.mem_of_superset (Metric.ball_mem_nhds y hδ) ?_
    intro z hz
    have hdz : dist (f z) (f y) < c/2 := hδ' hz
    rw [Real.dist_eq, hyc] at hdz
    obtain ⟨n, hn⟩ := hf z
    rw [hn] at hdz
    show f z = m₀ * c
    rw [hn]
    exact zsmul_range_sep hc ⟨n, rfl⟩ ⟨m₀, rfl⟩ (by linarith)
  have hclo : IsClosed {y | f y = m₀ * c} := isClosed_eq f.continuous continuous_const
  have hunion : (Set.univ : Set X) ⊆ {y | f y = m₀ * c} ∪ {y | f y ≠ m₀ * c} := by
    intro y _; by_cases h : f y = m₀ * c <;> simp [h]
  rcases IsPreconnected.subset_or_subset (s := (Set.univ : Set X)) hopen hclo.isOpen_compl
      disjoint_compl_right hunion isPreconnected_univ with h | h
  · exact h (Set.mem_univ x)
  · exact absurd hm₀ (h (Set.mem_univ x₀))

lemma diff_lift_const {F G : C(ℝ, ℝ)} (h : Circle.exp ∘ F = Circle.exp ∘ G) :
    ∃ m : ℤ, ∀ t, F t = G t + m * (2 * Real.pi) := by
  have hmem : ∀ t : ℝ, ∃ m : ℤ, F t - G t = m * (2 * Real.pi) := by
    intro t
    have h' : Circle.exp (F t) = Circle.exp (G t) := by
      have := congr_fun h t; simpa [ContinuousMap.comp_apply] using this
    obtain ⟨m, hm⟩ := Circle.exp_eq_exp.mp h'
    exact ⟨m, by linarith⟩
  have hcont : Continuous fun t : ℝ => F t - G t := F.continuous.sub G.continuous
  obtain ⟨m, hm⟩ := eq_const_mul_of_sub_mem (c := 2 * Real.pi) (by positivity)
    (f := ⟨fun t : ℝ => F t - G t, hcont⟩) hmem
  refine ⟨m, fun t => ?_⟩
  have ht := hm t
  change F t - G t = m * (2 * Real.pi) at ht
  linarith

lemma loopDegree_homotopic {f g : C(Circle, Circle)} (h : ContinuousMap.Homotopic f g) :
    loopDegree f = loopDegree g := by
  obtain ⟨H⟩ := h
  let Φ : C(ℝ × ℝ, Circle) := H.toContinuousMap.comp
    ((ContinuousMap.projIccCM (a := (0:ℝ)) (b := 1)).prodMap Circle.exp)
  have hΦ : ∀ s t : ℝ, Φ (s, t) = H (Set.projIcc 0 1 (by norm_num : (0:ℝ) ≤ 1) s, Circle.exp t) := by
    intro s t
    rfl
  have hproj0 : Set.projIcc 0 1 (by norm_num : (0:ℝ) ≤ 1) 0 = (0 : unitInterval) :=
    Subtype.ext (by simp [Set.projIcc])
  have hproj1 : Set.projIcc 0 1 (by norm_num : (0:ℝ) ≤ 1) 1 = (1 : unitInterval) :=
    Subtype.ext (by simp [Set.projIcc])
  have he : Circle.exp (Complex.arg (f 1 : ℂ)) = Φ (0, 0) := by
    rw [hΦ, hproj0, Circle.exp_arg, Circle.exp_zero]
    exact (H.apply_zero (1 : Circle)).symm
  obtain ⟨K, hK0, hKlift⟩ :=
    (Circle.isCoveringMap_exp.existsUnique_continuousMap_lifts Φ (0, 0)
      (Complex.arg (f 1 : ℂ)) he).exists
  have hK : ∀ p : ℝ × ℝ, Circle.exp (K p) = Φ p := by
    intro p; have := congr_fun hKlift p; simpa [ContinuousMap.comp_apply] using this
  have hKc : Continuous fun p : ℝ × ℝ => K p := K.continuous
  let K0 : C(ℝ, ℝ) := ⟨fun t : ℝ => K (0, t), hKc.comp (continuous_const.prodMk continuous_id)⟩
  let K1 : C(ℝ, ℝ) := ⟨fun t : ℝ => K (1, t), hKc.comp (continuous_const.prodMk continuous_id)⟩
  have hK0_apply : ∀ t : ℝ, K0 t = K (0, t) := fun t => rfl
  have hK1_apply : ∀ t : ℝ, K1 t = K (1, t) := fun t => rfl
  have hK00 : K0 0 = Complex.arg (f 1 : ℂ) := by rw [hK0_apply]; exact hK0
  have hslice0 : Circle.exp ∘ K0 = ⇑(f.comp Circle.exp) := by
    funext t
    simp only [Function.comp_apply, ContinuousMap.comp_apply]
    rw [hK0_apply, hK, hΦ, hproj0]
    simp only [H.apply_zero]
  have hslice1 : Circle.exp ∘ K1 = ⇑(g.comp Circle.exp) := by
    funext t
    simp only [Function.comp_apply, ContinuousMap.comp_apply]
    rw [hK1_apply, hK, hΦ, hproj1]
    simp only [H.apply_one]
  have hK0_eq : K0 = loopLift f := loopLift_unique f K0 hK00 hslice0
  obtain ⟨m₁, hm₁⟩ := diff_lift_const (F := K1) (G := loopLift g)
    (hslice1.trans (loopLift_lifts g).symm)
  have hInt : ∀ s : ℝ, ∃ m : ℤ, (K (s, 2 * Real.pi) - K (s, 0)) / (2 * Real.pi) = m * 1 := by
    intro s
    have heq : Circle.exp (K (s, 2*Real.pi)) = Circle.exp (K (s, 0)) := by
      rw [hK, hK, hΦ, hΦ, Circle.exp_two_pi, Circle.exp_zero]
    obtain ⟨m, hm⟩ := Circle.exp_eq_exp.mp heq
    refine ⟨m, ?_⟩
    rw [hm]; field_simp; ring
  let W : C(ℝ, ℝ) := ⟨fun s : ℝ => (K (s, 2 * Real.pi) - K (s, 0)) / (2 * Real.pi),
      ((hKc.comp (continuous_id.prodMk continuous_const)).sub
        (hKc.comp (continuous_id.prodMk continuous_const))).div_const _⟩
  have hW : ∀ s : ℝ, W s = (K (s, 2 * Real.pi) - K (s, 0)) / (2 * Real.pi) := fun s => rfl
  obtain ⟨M, hM⟩ := eq_const_mul_of_sub_mem (c := 1) (by norm_num) (f := W) (by
    intro s; rw [hW]; simpa using hInt s)
  have hw0 : W 0 = (loopDegree f : ℝ) := by
    rw [hW]
    rw [← hK0_apply (2*Real.pi), ← hK0_apply 0, hK0_eq]
    rw [loopLift_period f]
    field_simp
    ring
  have hw1 : W 1 = (loopDegree g : ℝ) := by
    rw [hW]
    rw [← hK1_apply (2*Real.pi), ← hK1_apply 0]
    rw [hm₁ (2*Real.pi), hm₁ 0]
    rw [loopLift_period g]
    field_simp
    ring
  have hconst : W 0 = W 1 := by rw [hM 0, hM 1]
  rw [hw0, hw1] at hconst
  exact_mod_cast hconst


open _root_.Circle

lemma loopDegree_const (c : Circle) : loopDegree (ContinuousMap.const Circle c) = 0 := by
  have hlift : Circle.exp ∘ (ContinuousMap.const ℝ (Complex.arg (c : ℂ)))
      = ⇑((ContinuousMap.const Circle c).comp Circle.exp) := by
    ext t
    simp only [ContinuousMap.comp_apply, ContinuousMap.const_apply, Function.comp_apply]
    exact congrArg Subtype.val (Circle.exp_arg c)
  have h0 : (ContinuousMap.const ℝ (Complex.arg (c : ℂ))) 0
      = Complex.arg (((ContinuousMap.const Circle c) 1 : Circle) : ℂ) := by simp
  have h1 : loopLift (ContinuousMap.const Circle c)
      = ContinuousMap.const ℝ (Complex.arg (c : ℂ)) :=
    (loopLift_unique (ContinuousMap.const Circle c) _ h0 hlift).symm
  have hp := loopLift_period (ContinuousMap.const Circle c)
  rw [h1] at hp
  simp only [ContinuousMap.const_apply] at hp
  have h3 : (loopDegree (ContinuousMap.const Circle c) : ℝ) * (2 * Real.pi) = 0 := by linarith
  have h4 : (loopDegree (ContinuousMap.const Circle c) : ℝ) = 0 :=
    (mul_eq_zero.mp h3).resolve_right (by positivity)
  exact_mod_cast h4

lemma loopDegree_id : loopDegree (ContinuousMap.id Circle) = 1 := by
  have hlift : Circle.exp ∘ (ContinuousMap.id ℝ)
      = ⇑((ContinuousMap.id Circle).comp Circle.exp) := by
    ext t; rfl
  have h0 : (ContinuousMap.id ℝ) 0 = Complex.arg (((ContinuousMap.id Circle) 1 : Circle) : ℂ) := by
    simp [Complex.arg_one]
  have h1 : loopLift (ContinuousMap.id Circle) = ContinuousMap.id ℝ :=
    (loopLift_unique (ContinuousMap.id Circle) _ h0 hlift).symm
  have hp := loopLift_period (ContinuousMap.id Circle)
  rw [h1] at hp
  simp only [ContinuousMap.id_apply] at hp
  have h3 : (loopDegree (ContinuousMap.id Circle) : ℝ) * (2 * Real.pi) = 2 * Real.pi := by linarith
  have hne : (2 * (Real.pi : ℝ)) ≠ 0 := by positivity
  have h4 : (loopDegree (ContinuousMap.id Circle) : ℝ) = 1 := by
    rw [mul_comm] at h3
    exact (mul_right_inj' hne).mp (by simpa using h3)
  exact_mod_cast h4


lemma loopDegree_eq_zero_of_nullhomotopic {f : C(Circle, Circle)} (hf : f.Nullhomotopic) :
    loopDegree f = 0 := by
  obtain ⟨y, hy⟩ := hf
  rw [loopDegree_homotopic hy, loopDegree_const]

lemma not_nullhomotopic_id : ¬ (ContinuousMap.id Circle).Nullhomotopic := by
  intro h
  have := loopDegree_eq_zero_of_nullhomotopic h
  rw [loopDegree_id] at this
  exact one_ne_zero this

abbrev Ball := Metric.closedBall (0:ℂ) 1

noncomputable def qa (f : C(Ball, Ball)) (x : Ball) : ℝ := ‖((x:ℂ)) - (((f x):ℂ))‖^2
noncomputable def qb (f : C(Ball, Ball)) (x : Ball) : ℝ := 2 * inner ℝ (((f x):ℂ)) (((x:ℂ)) - (((f x):ℂ)))
noncomputable def qc (f : C(Ball, Ball)) (x : Ball) : ℝ := ‖(((f x):ℂ))‖^2 - 1
noncomputable def qs (f : C(Ball, Ball)) (x : Ball) : ℝ :=
  (-(qb f x) + Real.sqrt ((qb f x)^2 - 4*(qa f x)*(qc f x))) / (2 * qa f x)
noncomputable def qr (f : C(Ball, Ball)) (x : Ball) : ℂ :=
  (((f x):ℂ)) + (qs f x) • (((x:ℂ)) - (((f x):ℂ)))

lemma qa_pos (f : C(Ball, Ball)) (hf : ∀ x, f x ≠ x) (x : Ball) : 0 < qa f x := by
  rw [qa]
  have h : ((x:ℂ)) - (((f x):ℂ)) ≠ 0 := by
    intro hh
    exact hf x (Subtype.ext (sub_eq_zero.mp hh)).symm
  exact pow_pos (norm_pos_iff.mpr h) 2

lemma qc_le (f : C(Ball, Ball)) (x : Ball) : qc f x ≤ 0 := by
  have h : ‖(((f x):ℂ))‖ ≤ 1 := by
    have := (f x).2; rw [Metric.mem_closedBall, dist_zero_right] at this; exact this
  rw [qc]
  nlinarith [norm_nonneg (((f x):ℂ)), sq_nonneg (‖(((f x):ℂ))‖)]

lemma qa_add_qb_add_qc (f : C(Ball, Ball)) (x : Ball) : qa f x + qb f x + qc f x = ‖((x:ℂ))‖^2 - 1 := by
  rw [qa, qb, qc, real_inner_comm]
  have h1 := norm_add_sq_real (((x:ℂ)) - (((f x):ℂ))) (((f x):ℂ))
  rw [sub_add_cancel] at h1
  linarith [h1]

lemma qs_eq_one (f : C(Ball, Ball)) (hf : ∀ x, f x ≠ x) (x : Ball) (hx : ‖((x:ℂ))‖ = 1) :
    qs f x = 1 := by
  have hsum : qa f x + qb f x + qc f x = 0 := by
    rw [qa_add_qb_add_qc, hx]; norm_num
  have hbc : qb f x = -(qa f x) - qc f x := by linarith
  have hD : (qb f x)^2 - 4*(qa f x)*(qc f x) = (2*(qa f x) + qb f x)^2 := by
    rw [hbc]; ring
  have h2a : 0 < 2*(qa f x) + qb f x := by
    have := qa_pos f hf x; have := qc_le f x; rw [hbc]; linarith
  rw [qs, hD, Real.sqrt_sq (le_of_lt h2a), hbc]
  have ha0 : qa f x ≠ 0 := ne_of_gt (qa_pos f hf x)
  field_simp
  ring

lemma qr_norm (f : C(Ball, Ball)) (hf : ∀ x, f x ≠ x) (x : Ball) : ‖qr f x‖ = 1 := by
  have ha0 : 0 < qa f x := qa_pos f hf x
  have hc0 : qc f x ≤ 0 := qc_le f x
  have hD : 0 ≤ (qb f x)^2 - 4*(qa f x)*(qc f x) := by
    nlinarith [sq_nonneg (qb f x), ha0, hc0]
  have hsq : (Real.sqrt ((qb f x)^2 - 4*(qa f x)*(qc f x)))^2
      = (qb f x)^2 - 4*(qa f x)*(qc f x) := Real.sq_sqrt hD
  have hquad : (qa f x) * (qs f x)^2 + (qb f x) * (qs f x) + (qc f x) = 0 := by
    rw [qs]
    set u := Real.sqrt ((qb f x) ^ 2 - 4 * (qa f x) * (qc f x)) with hu
    have huu : u^2 = (qb f x)^2 - 4*(qa f x)*(qc f x) := hsq
    field_simp
    nlinarith [huu]
  have hnorm : ‖qr f x‖^2
      = (qa f x) * (qs f x)^2 + (qb f x) * (qs f x) + ‖(((f x):ℂ))‖^2 := by
    rw [qr, norm_add_sq_real, real_inner_smul_right, norm_smul, Real.norm_eq_abs, mul_pow, sq_abs]
    rw [qa, qb]
    ring
  have : ‖qr f x‖^2 = 1 := by rw [hnorm, qc] at *; linarith
  nlinarith [norm_nonneg (qr f x), this]

lemma qr_self (f : C(Ball, Ball)) (hf : ∀ x, f x ≠ x) (x : Ball) (hx : ‖((x:ℂ))‖ = 1) :
    qr f x = x := by
  rw [qr, qs_eq_one f hf x hx, one_smul]
  abel


lemma qa_cont (f : C(Ball, Ball)) : Continuous (qa f) := by
  change Continuous fun x : Ball => ‖((x:ℂ)) - (((f x):ℂ))‖^2
  fun_prop

lemma qb_cont (f : C(Ball, Ball)) : Continuous (qb f) := by
  change Continuous fun x : Ball => 2 * inner ℝ (((f x):ℂ)) (((x:ℂ)) - (((f x):ℂ)))
  fun_prop

lemma qc_cont (f : C(Ball, Ball)) : Continuous (qc f) := by
  change Continuous fun x : Ball => ‖(((f x):ℂ))‖^2 - 1
  fun_prop

lemma qr_cont (f : C(Ball, Ball)) (hf : ∀ x, f x ≠ x) : Continuous (qr f) := by
  have hqs : Continuous (qs f) := by
    change Continuous fun x : Ball =>
      (-(qb f x) + Real.sqrt ((qb f x)^2 - 4*(qa f x)*(qc f x))) / (2 * qa f x)
    apply Continuous.div
    · apply Continuous.add
      · exact (qb_cont f).neg
      · apply Real.continuous_sqrt.comp
        have hp : Continuous fun x : Ball => (qb f x)^2 := (qb_cont f).pow 2
        have hq : Continuous fun x : Ball => 4 * (qa f x) * (qc f x) := by
          have h := ((qa_cont f).mul (qc_cont f)).const_mul 4
          simpa [mul_assoc] using h
        exact hp.sub hq
    · show Continuous fun x : Ball => 2 * (qa f x)
      exact (qa_cont f).const_mul 2
    · intro x; have := qa_pos f hf x; positivity
  change Continuous fun x : Ball => (((f x):ℂ)) + (qs f x) • (((x:ℂ)) - (((f x):ℂ)))
  fun_prop

noncomputable def qrmap (f : C(Ball, Ball)) (hf : ∀ x, f x ≠ x) : C(Ball, Metric.sphere (0:ℂ) 1) :=
  ⟨fun x => ⟨qr f x, by rw [Metric.mem_sphere, dist_zero_right]; exact qr_norm f hf x⟩,
    Continuous.subtype_mk (qr_cont f hf) _⟩

lemma qrmap_self (f : C(Ball, Ball)) (hf : ∀ x, f x ≠ x) (x : Ball) (hx : ‖((x:ℂ))‖ = 1) :
    qrmap f hf x = ⟨x.1, by rwa [Metric.mem_sphere, dist_zero_right]⟩ := by
  apply Subtype.ext
  exact qr_self f hf x hx

noncomputable def sphereIncl : C(Metric.sphere (0:ℂ) 1, Ball) where
  toFun x := ⟨x.1, by
    rw [Metric.mem_closedBall, dist_zero_right]
    have h := x.2
    rw [Metric.mem_sphere, dist_zero_right] at h
    exact le_of_eq h⟩
  continuous_toFun := by fun_prop

lemma sphereIncl_coe (x : Metric.sphere (0:ℂ) 1) : ((sphereIncl x : Ball) : ℂ) = (x : ℂ) := rfl

lemma nullhomotopic_of_contractible {X : Type*} [TopologicalSpace X] {Y : Type*} [TopologicalSpace Y]
    [ContractibleSpace Y] (f : C(X, Y)) : f.Nullhomotopic := by
  have h1 : (ContinuousMap.id Y).Nullhomotopic := id_nullhomotopic Y
  have h2 := h1.comp_left f
  rwa [ContinuousMap.id_comp] at h2

theorem brouwer_fixed_point (f : C(Ball, Ball)) : ∃ x, f x = x := by
  by_contra h
  push_neg at h
  haveI : ContractibleSpace Ball :=
    (convex_closedBall (0:ℂ) 1).contractibleSpace ⟨0, by simp [Metric.mem_closedBall]⟩
  have hcomp : ContinuousMap.Nullhomotopic (sphereIncl : C(Metric.sphere (0:ℂ) 1, Ball)) :=
    nullhomotopic_of_contractible sphereIncl
  have hw_nul : ((qrmap f h).comp sphereIncl).Nullhomotopic := hcomp.comp_right (qrmap f h)
  have hw_id : (qrmap f h).comp sphereIncl = ContinuousMap.id Circle := by
    ext c
    have hc : ‖((c : Circle) : ℂ)‖ = 1 := by
      have := c.2; rwa [Metric.mem_sphere, dist_zero_right] at this
    have h1 := qrmap_self f h (sphereIncl c) (by rw [sphereIncl_coe]; exact hc)
    rw [ContinuousMap.comp_apply, h1]
    rfl
  have hdeg : loopDegree ((qrmap f h).comp sphereIncl) = 0 :=
    loopDegree_eq_zero_of_nullhomotopic hw_nul
  have h2 : loopDegree (ContinuousMap.id Circle) = 0 :=
    (congrArg loopDegree hw_id).symm.trans hdeg
  rw [loopDegree_id] at h2
  exact one_ne_zero h2



/-! ### The square-disk homeomorphism -/

abbrev BallC := Metric.closedBall (0:ℂ) 1
abbrev SqC : Set ℂ := {z : ℂ | |z.re| ≤ 1 ∧ |z.im| ≤ 1}

noncomputable def Phi (z : ℂ) : ℂ :=
  if z = 0 then 0 else (‖z‖ / (max |z.re| |z.im|)) * z

noncomputable def Psi (w : ℂ) : ℂ :=
  if w = 0 then 0 else ((max |w.re| |w.im|) / ‖w‖) * w

lemma Phi_apply {z : ℂ} (hz : z ≠ 0) : Phi z = (‖z‖ / (max |z.re| |z.im|)) * z := by
  rw [Phi, if_neg hz]

lemma Psi_apply {w : ℂ} (hw : w ≠ 0) : Psi w = ((max |w.re| |w.im|) / ‖w‖) * w := by
  rw [Psi, if_neg hw]

lemma max_nonneg (z : ℂ) : 0 ≤ max |z.re| |z.im| := le_trans (abs_nonneg _) (le_max_left _ _)

lemma max_pos {z : ℂ} (hz : z ≠ 0) : 0 < max |z.re| |z.im| := by
  rcases lt_max_iff.mp (lt_of_le_of_ne (max_nonneg z) (by
    intro h
    have h1 : |z.re| = 0 := le_antisymm (le_trans (le_max_left _ _) (le_of_eq h.symm)) (abs_nonneg _)
    have h2 : |z.im| = 0 := le_antisymm (le_trans (le_max_right _ _) (le_of_eq h.symm)) (abs_nonneg _)
    exact hz (Complex.ext (abs_eq_zero.mp h1) (abs_eq_zero.mp h2)))) with h | h
  · exact lt_of_lt_of_le h (le_max_left _ _)
  · exact lt_of_lt_of_le h (le_max_right _ _)

lemma max_le_norm (z : ℂ) : max |z.re| |z.im| ≤ ‖z‖ :=
  max_le (Complex.abs_re_le_norm z) (Complex.abs_im_le_norm z)

lemma Phi_re (z : ℂ) : (Phi z).re = ‖z‖ / (max |z.re| |z.im|) * z.re := by
  by_cases h : z = 0
  · subst h; rw [Phi, if_pos rfl]; simp
  · rw [Phi_apply h, ← Complex.ofReal_div, Complex.re_ofReal_mul]

lemma Phi_im (z : ℂ) : (Phi z).im = ‖z‖ / (max |z.re| |z.im|) * z.im := by
  by_cases h : z = 0
  · subst h; rw [Phi, if_pos rfl]; simp
  · rw [Phi_apply h, ← Complex.ofReal_div, Complex.im_ofReal_mul]

lemma Psi_re (w : ℂ) : (Psi w).re = max |w.re| |w.im| / ‖w‖ * w.re := by
  by_cases h : w = 0
  · subst h; rw [Psi, if_pos rfl]; simp
  · rw [Psi_apply h, ← Complex.ofReal_div, Complex.re_ofReal_mul]

lemma Psi_im (w : ℂ) : (Psi w).im = max |w.re| |w.im| / ‖w‖ * w.im := by
  by_cases h : w = 0
  · subst h; rw [Psi, if_pos rfl]; simp
  · rw [Psi_apply h, ← Complex.ofReal_div, Complex.im_ofReal_mul]

lemma norm_Phi {z : ℂ} (h : z ≠ 0) : ‖Phi z‖ = ‖z‖^2 / max |z.re| |z.im| := by
  rw [Phi_apply h, norm_mul, Complex.norm_div, Complex.norm_real, Complex.norm_real,
    Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg (norm_nonneg z), abs_of_nonneg (max_nonneg z)]
  field_simp

lemma max_Phi (z : ℂ) : max |(Phi z).re| |(Phi z).im| = ‖z‖ := by
  by_cases h : z = 0
  · subst h; rw [Phi, if_pos rfl]; simp
  · rw [Phi_re, Phi_im, abs_mul, abs_mul, abs_of_nonneg (div_nonneg (norm_nonneg z) (le_of_lt (max_pos h)))]
    rw [mul_comm (‖z‖ / max |z.re| |z.im|) |z.re|, mul_comm (‖z‖ / max |z.re| |z.im|) |z.im|]
    rw [← max_mul_of_nonneg |z.re| |z.im| (div_nonneg (norm_nonneg z) (le_of_lt (max_pos h)))]
    rw [mul_div_cancel₀ _ (ne_of_gt (max_pos h))]

lemma max_Psi {w : ℂ} (h : w ≠ 0) :
    max |(Psi w).re| |(Psi w).im| = (max |w.re| |w.im|) / ‖w‖ * max |w.re| |w.im| := by
  rw [Psi_re, Psi_im, abs_mul, abs_mul, abs_of_nonneg (div_nonneg (max_nonneg w) (norm_nonneg w))]
  rw [mul_comm (max |w.re| |w.im| / ‖w‖) |w.re|, mul_comm (max |w.re| |w.im| / ‖w‖) |w.im|]
  rw [← max_mul_of_nonneg |w.re| |w.im| (div_nonneg (max_nonneg w) (norm_nonneg w))]
  rw [mul_comm]

lemma norm_Psi (w : ℂ) : ‖Psi w‖ = max |w.re| |w.im| := by
  by_cases h : w = 0
  · subst h; rw [Psi, if_pos rfl]; simp
  · rw [Psi_apply h, norm_mul, Complex.norm_div, Complex.norm_real, Complex.norm_real,
      Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg (max_nonneg w), abs_of_nonneg (norm_nonneg w)]
    rw [div_mul_cancel₀ _ (norm_ne_zero_iff.mpr h)]

lemma Phi_mem (z : ℂ) (hz : z ∈ BallC) : Phi z ∈ SqC := by
  rw [Metric.mem_closedBall, dist_zero_right] at hz
  constructor
  · calc |(Phi z).re| ≤ max |(Phi z).re| |(Phi z).im| := le_max_left _ _
      _ = ‖z‖ := max_Phi z
      _ ≤ 1 := hz
  · calc |(Phi z).im| ≤ max |(Phi z).re| |(Phi z).im| := le_max_right _ _
      _ = ‖z‖ := max_Phi z
      _ ≤ 1 := hz

lemma Psi_mem (w : ℂ) (hw : w ∈ SqC) : Psi w ∈ BallC := by
  rw [Metric.mem_closedBall, dist_zero_right, norm_Psi]
  exact max_le hw.1 hw.2

lemma Phi_Psi (w : ℂ) (hw : w ∈ SqC) : Phi (Psi w) = w := by
  by_cases h : w = 0
  · subst h; rw [Psi, if_pos rfl, Phi, if_pos rfl]
  · have hPsi : Psi w ≠ 0 := by
      rw [← norm_ne_zero_iff, norm_Psi]
      exact ne_of_gt (max_pos h)
    rw [Phi_apply hPsi, norm_Psi, max_Psi h, Psi_apply h]
    have hm : 0 < max |w.re| |w.im| := max_pos h
    have hn : (0:ℝ) < ‖w‖ := norm_pos_iff.mpr h
    push_cast
    field_simp
    have hm' : (↑(max |w.re| |w.im|) : ℂ) ≠ 0 := by exact_mod_cast ne_of_gt hm
    have hn' : (↑‖w‖ : ℂ) ≠ 0 := by exact_mod_cast ne_of_gt hn
    field_simp

lemma Psi_Phi (z : ℂ) (hz : z ∈ BallC) : Psi (Phi z) = z := by
  by_cases h : z = 0
  · subst h; rw [Phi, if_pos rfl, Psi, if_pos rfl]
  · have hPhi : Phi z ≠ 0 := by
      rw [← norm_ne_zero_iff, norm_Phi h]
      exact div_ne_zero (ne_of_gt (pow_pos (norm_pos_iff.mpr h) 2)) (ne_of_gt (max_pos h))
    rw [Psi_apply hPhi, max_Phi z, norm_Phi h, Phi_apply h]
    have hm : 0 < max |z.re| |z.im| := max_pos h
    have hn : (0:ℝ) < ‖z‖ := norm_pos_iff.mpr h
    have hm' : ((max |z.re| |z.im| : ℝ) : ℂ) ≠ 0 := by exact_mod_cast ne_of_gt hm
    have hn' : ((‖z‖ : ℝ) : ℂ) ≠ 0 := by exact_mod_cast ne_of_gt hn
    push_cast
    field_simp



section HomeomorphSq

open _root_.Circle

lemma norm_Phi_le (z : ℂ) : ‖Phi z‖ ≤ 2 * ‖z‖ := by
  rcases eq_or_ne z 0 with hz | hz
  · subst hz; simp [Phi]
  · rw [norm_Phi hz]
    have hm : 0 < max |z.re| |z.im| := max_pos hz
    rw [div_le_iff₀ hm]
    have h1 : z.re ^ 2 ≤ (max |z.re| |z.im|) ^ 2 := by
      nlinarith [le_max_left |z.re| |z.im|, abs_nonneg z.re, sq_abs z.re]
    have h2 : z.im ^ 2 ≤ (max |z.re| |z.im|) ^ 2 := by
      nlinarith [le_max_right |z.re| |z.im|, abs_nonneg z.im, sq_abs z.im]
    have h3 : ‖z‖ ^ 2 = z.re ^ 2 + z.im ^ 2 := by
      rw [Complex.sq_norm, Complex.normSq_apply]; ring
    nlinarith [h3, h1, h2, hm.le, max_le_norm z, norm_nonneg z]

lemma Phi_continuous : Continuous Phi := by
  rw [continuous_iff_continuousAt]
  intro w
  by_cases hw : w = 0
  · subst hw
    rw [ContinuousAt]
    have hPhi0 : Phi (0:ℂ) = 0 := by rw [Phi, if_pos rfl]
    rw [hPhi0, tendsto_zero_iff_norm_tendsto_zero]
    have h2 : Tendsto (fun z : ℂ => 2 * ‖z‖) (𝓝 0) (𝓝 0) := by
      simpa [ContinuousAt] using (continuous_norm.continuousAt (x := (0:ℂ))).const_mul 2
    exact squeeze_zero (fun z => norm_nonneg _) norm_Phi_le h2
  · have heq : Phi =ᶠ[𝓝 w] ((fun z : ℂ => ‖z‖ / max |z.re| |z.im|) • fun z : ℂ => z) := by
      filter_upwards [isClosed_singleton.isOpen_compl.mem_nhds hw] with z hz
      rw [Phi_apply hz]
      simp [Complex.real_smul, Complex.ofReal_div]
    rw [continuousAt_congr heq]
    have hmax : ContinuousAt (fun z : ℂ => max |z.re| |z.im|) w := by fun_prop
    have hne : max |w.re| |w.im| ≠ 0 := ne_of_gt (max_pos hw)
    exact ((continuous_norm.continuousAt (x := w)).div hmax hne).smul
      (continuous_id.continuousAt (x := w))

lemma Psi_continuous : Continuous Psi := by
  rw [continuous_iff_continuousAt]
  intro w
  by_cases hw : w = 0
  · subst hw
    rw [ContinuousAt]
    have hPsi0 : Psi (0:ℂ) = 0 := by rw [Psi, if_pos rfl]
    rw [hPsi0, tendsto_zero_iff_norm_tendsto_zero]
    have hb : ∀ z : ℂ, ‖Psi z‖ ≤ ‖z‖ := by
      intro z; rw [norm_Psi]; exact max_le_norm z
    have h2 : Tendsto (fun z : ℂ => ‖z‖) (𝓝 0) (𝓝 0) := by
      simpa [ContinuousAt] using continuous_norm.continuousAt (x := (0:ℂ))
    exact squeeze_zero (fun z => norm_nonneg _) hb h2
  · have heq : Psi =ᶠ[𝓝 w] ((fun z : ℂ => max |z.re| |z.im| / ‖z‖) • fun z : ℂ => z) := by
      filter_upwards [isClosed_singleton.isOpen_compl.mem_nhds hw] with z hz
      rw [Psi_apply hz]
      simp [Complex.real_smul, Complex.ofReal_div]
    rw [continuousAt_congr heq]
    have hmax : ContinuousAt (fun z : ℂ => max |z.re| |z.im|) w := by fun_prop
    have hne : ‖w‖ ≠ 0 := norm_ne_zero_iff.mpr hw
    exact (hmax.div (continuous_norm.continuousAt (x := w)) hne).smul
      (continuous_id.continuousAt (x := w))

noncomputable def sqBallHomeo : C(BallC, SqC) where
  toFun := fun (z : BallC) => ⟨Phi (z : ℂ), Phi_mem (z : ℂ) z.2⟩
  continuous_toFun := Continuous.subtype_mk (f := fun z : BallC => Phi (z : ℂ))
    (Phi_continuous.comp continuous_subtype_val)
    (fun (z : BallC) => Phi_mem (z : ℂ) z.2)

noncomputable def ballSqHomeo : C(SqC, BallC) where
  toFun := fun (w : SqC) => ⟨Psi (w : ℂ), Psi_mem (w : ℂ) w.2⟩
  continuous_toFun := Continuous.subtype_mk (f := fun w : SqC => Psi (w : ℂ))
    (Psi_continuous.comp continuous_subtype_val)
    (fun (w : SqC) => Psi_mem (w : ℂ) w.2)

lemma sqBallHomeo_ballSqHomeo (w : SqC) :
    sqBallHomeo (ballSqHomeo w) = w := by
  apply Subtype.ext
  simp only [sqBallHomeo, ballSqHomeo, ContinuousMap.coe_mk]
  exact Phi_Psi (w : ℂ) w.2

lemma ballSqHomeo_sqBallHomeo (z : BallC) :
    ballSqHomeo (sqBallHomeo z) = z := by
  apply Subtype.ext
  simp only [sqBallHomeo, ballSqHomeo, ContinuousMap.coe_mk]
  exact Psi_Phi (z : ℂ) z.2

noncomputable def sqBallHomeomorph : BallC ≃ₜ SqC where
  toFun := sqBallHomeo
  invFun := ballSqHomeo
  left_inv := ballSqHomeo_sqBallHomeo
  right_inv := sqBallHomeo_ballSqHomeo
  continuous_toFun := sqBallHomeo.continuous
  continuous_invFun := ballSqHomeo.continuous

end HomeomorphSq

section CrossingLemma

lemma re_add_mul_I (r s : ℝ) : (((r:ℝ):ℂ) + ((s:ℝ):ℂ) * Complex.I).re = r := by simp
lemma im_add_mul_I (r s : ℝ) : (((r:ℝ):ℂ) + ((s:ℝ):ℂ) * Complex.I).im = s := by simp

/-- `brouwer_fixed_point` transported to the square `[-1,1] × [-1,1]`. -/
theorem brouwer_fixed_point_square (f : C(SqC, SqC)) : ∃ x, f x = x := by
  obtain ⟨x, hx⟩ := brouwer_fixed_point (ballSqHomeo.comp (f.comp sqBallHomeo))
  refine ⟨sqBallHomeo x, ?_⟩
  have hx' : ballSqHomeo (f (sqBallHomeo x)) = x := hx
  rw [← sqBallHomeo_ballSqHomeo (f (sqBallHomeo x)), hx']

/-- **Crossing lemma** (Maehara's Lemma 2).  Two paths in the rectangle
`E(a,b;c,d)` — one joining the left side to the right side, the other the bottom
side to the top side — must meet. -/
theorem crossing_lemma {a b c d : ℝ}
    (h v : C(ℝ, ℂ))
    (hh : ∀ t : ℝ, t ∈ Set.Icc (-1:ℝ) 1 → (h t).re ∈ Set.Icc a b ∧ (h t).im ∈ Set.Icc c d)
    (hv : ∀ t : ℝ, t ∈ Set.Icc (-1:ℝ) 1 → (v t).re ∈ Set.Icc a b ∧ (v t).im ∈ Set.Icc c d)
    (h1 : ((h (-1))).re = a) (h2 : ((h 1)).re = b)
    (v1 : ((v (-1))).im = c) (v2 : ((v 1)).im = d) :
    ∃ s ∈ Set.Icc (-1:ℝ) 1, ∃ t ∈ Set.Icc (-1:ℝ) 1, h s = v t := by
  by_contra hcon
  simp only [not_exists, ne_eq] at hcon
  have hmem : ∀ z : SqC, z.1.re ∈ Set.Icc (-1:ℝ) 1 ∧ z.1.im ∈ Set.Icc (-1:ℝ) 1 := by
    intro z
    have hr := abs_le.mp z.2.1; have hi := abs_le.mp z.2.2
    exact ⟨⟨hr.1, hr.2⟩, ⟨hi.1, hi.2⟩⟩
  set A : SqC → ℝ := fun z => (v z.1.im).re - (h z.1.re).re with hAdef
  set B : SqC → ℝ := fun z => (h z.1.re).im - (v z.1.im).im with hBdef
  set N : SqC → ℝ := fun z => max |A z| |B z| with hNdef
  have hNpos : ∀ z : SqC, 0 < N z := by
    intro z
    have hz0 : max |A z| |B z| ≠ 0 := by
      intro h0
      have hA0 : A z = 0 := by
        have h1' : |A z| ≤ max |A z| |B z| := le_max_left _ _
        rw [h0] at h1'
        exact abs_eq_zero.mp (le_antisymm h1' (abs_nonneg _))
      have hB0 : B z = 0 := by
        have h1' : |B z| ≤ max |A z| |B z| := le_max_right _ _
        rw [h0] at h1'
        exact abs_eq_zero.mp (le_antisymm h1' (abs_nonneg _))
      have hA' : (v z.1.im).re - (h z.1.re).re = 0 := by rw [hAdef] at hA0; exact hA0
      have hB' : (h z.1.re).im - (v z.1.im).im = 0 := by rw [hBdef] at hB0; exact hB0
      have hEq : h z.1.re = v z.1.im := by
        apply Complex.ext
        · show (h z.1.re).re = (v z.1.im).re; linarith
        · show (h z.1.re).im = (v z.1.im).im; linarith
      exact hcon z.1.re ⟨(hmem z).1, z.1.im, (hmem z).2, hEq⟩
    rw [hNdef]
    exact lt_of_le_of_ne (le_max_of_le_left (abs_nonneg _)) (Ne.symm hz0)
  have hAcont : Continuous A := by rw [hAdef]; fun_prop
  have hBcont : Continuous B := by rw [hBdef]; fun_prop
  have hNcont : Continuous N := by rw [hNdef]; exact hAcont.abs.max hBcont.abs
  have hNne : ∀ z, N z ≠ 0 := fun z => ne_of_gt (hNpos z)
  have hquotA : Continuous fun z : SqC => A z / N z := hAcont.div hNcont hNne
  have hquotB : Continuous fun z : SqC => B z / N z := hBcont.div hNcont hNne
  have hmemF : ∀ z : SqC,
      ((A z / N z : ℝ) : ℂ) + ((B z / N z : ℝ) : ℂ) * Complex.I ∈ SqC := by
    intro z
    have hAz : |A z| ≤ N z := by rw [hNdef]; exact le_max_left _ _
    have hBz : |B z| ≤ N z := by rw [hNdef]; exact le_max_right _ _
    have hNz : 0 < N z := hNpos z
    constructor
    · rw [re_add_mul_I, abs_div, abs_of_pos hNz]
      exact (div_le_one hNz).mpr hAz
    · rw [im_add_mul_I, abs_div, abs_of_pos hNz]
      exact (div_le_one hNz).mpr hBz
  have hFcont : Continuous fun z : SqC =>
      (⟨((A z / N z : ℝ) : ℂ) + ((B z / N z : ℝ) : ℂ) * Complex.I, hmemF z⟩ : SqC) :=
    Continuous.subtype_mk
      ((Complex.continuous_ofReal.comp hquotA).add
        ((Complex.continuous_ofReal.comp hquotB).mul continuous_const)) hmemF
  let F : C(SqC, SqC) :=
    ⟨fun z => ⟨((A z / N z : ℝ) : ℂ) + ((B z / N z : ℝ) : ℂ) * Complex.I, hmemF z⟩, hFcont⟩
  obtain ⟨x, hx⟩ := brouwer_fixed_point_square F
  have hFx : (F x : ℂ) = ((A x / N x : ℝ) : ℂ) + ((B x / N x : ℝ) : ℂ) * Complex.I := rfl
  have hxval : (F x : ℂ) = (x : ℂ) := congrArg Subtype.val hx
  have hxre : (x : ℂ).re = A x / N x := by rw [← hxval, hFx, re_add_mul_I]
  have hxim : (x : ℂ).im = B x / N x := by rw [← hxval, hFx, im_add_mul_I]
  have hboundary : |A x / N x| = 1 ∨ |B x / N x| = 1 := by
    rcases max_cases |A x| |B x| with he | he
    · left
      have hNx : N x = |A x| := by rw [hNdef]; exact he.1
      have hne : |A x| ≠ 0 := by rw [← hNx]; exact hNne x
      rw [abs_div, abs_of_pos (hNpos x), hNx, div_self hne]
    · right
      have hNx : N x = |B x| := by rw [hNdef]; exact he.1
      have hne : |B x| ≠ 0 := by rw [← hNx]; exact hNne x
      rw [abs_div, abs_of_pos (hNpos x), hNx, div_self hne]
  have hAxval : A x = (v x.1.im).re - (h x.1.re).re := by rw [hAdef]
  have hBxval : B x = (h x.1.re).im - (v x.1.im).im := by rw [hBdef]
  rcases hboundary with hb | hb
  · rcases (abs_eq zero_le_one).mp hb with hb1 | hb1
    · have hxr : (x.1 : ℂ).re = 1 := by rw [hxre, hb1]
      have hAxN : A x = N x := (div_eq_one_iff_eq (hNne x)).mp hb1
      have hval : A x = (v x.1.im).re - b := by rw [hAxval, hxr, h2]
      have hle : (v x.1.im).re ≤ b := (hv x.1.im (hmem x).2).1.2
      rw [hval] at hAxN
      linarith [hNpos x]
    · have hxr : (x.1 : ℂ).re = -1 := by rw [hxre, hb1]
      have hAxN : A x = -N x := by
        have := (div_eq_iff (hNne x)).mp hb1
        linarith
      have hval : A x = (v x.1.im).re - a := by rw [hAxval, hxr, h1]
      have hge : a ≤ (v x.1.im).re := (hv x.1.im (hmem x).2).1.1
      rw [hval] at hAxN
      linarith [hNpos x]
  · rcases (abs_eq zero_le_one).mp hb with hb1 | hb1
    · have hxi : (x.1 : ℂ).im = 1 := by rw [hxim, hb1]
      have hBxN : B x = N x := (div_eq_one_iff_eq (hNne x)).mp hb1
      have hval : B x = (h x.1.re).im - d := by rw [hBxval, hxi, v2]
      have hle : (h x.1.re).im ≤ d := (hh x.1.re (hmem x).1).2.2
      rw [hval] at hBxN
      linarith [hNpos x]
    · have hxi : (x.1 : ℂ).im = -1 := by rw [hxim, hb1]
      have hBxN : B x = -N x := by
        have := (div_eq_iff (hNne x)).mp hb1
        linarith
      have hval : B x = (h x.1.re).im - c := by rw [hBxval, hxi, v1]
      have hge : c ≤ (h x.1.re).im := (hh x.1.re (hmem x).1).2.1
      rw [hval] at hBxN
      linarith [hNpos x]


end CrossingLemma

section Arcs

/-- Clamp a real number to `[-1,1]`. -/
noncomputable def clamp11 (t : ℝ) : ℝ := max (-1) (min t 1)

lemma clamp11_mem (t : ℝ) : clamp11 t ∈ Set.Icc (-1:ℝ) 1 :=
  ⟨le_max_left _ _, max_le (by norm_num) (min_le_right _ _)⟩

lemma clamp11_of_mem {t : ℝ} (ht : t ∈ Set.Icc (-1:ℝ) 1) : clamp11 t = t := by
  rw [clamp11, max_eq_right (le_min ht.1 (by norm_num)), min_eq_left ht.2]

lemma clamp11_continuous : Continuous clamp11 := by unfold clamp11; fun_prop

/-- The arc of the circle from angle `θ₁` to angle `θ₂`, as a path on `ℝ`
(constant outside `[-1,1]`). -/
noncomputable def circleArcPath (θ₁ θ₂ : ℝ) : C(ℝ, Circle) :=
  ⟨fun t => Circle.exp (((1 - clamp11 t) / 2) * θ₁ + ((1 + clamp11 t) / 2) * θ₂),
    Circle.exp.continuous.comp (by
      have h : Continuous fun t : ℝ => clamp11 t := clamp11_continuous
      fun_prop)⟩

@[simp] lemma circleArcPath_neg_one (θ₁ θ₂ : ℝ) :
    circleArcPath θ₁ θ₂ (-1) = Circle.exp θ₁ := by
  have h : clamp11 (-1) = (-1:ℝ) := clamp11_of_mem ⟨le_rfl, by norm_num⟩
  rw [circleArcPath, ContinuousMap.coe_mk, h]
  congr 1
  ring

@[simp] lemma circleArcPath_one (θ₁ θ₂ : ℝ) :
    circleArcPath θ₁ θ₂ 1 = Circle.exp θ₂ := by
  have h : clamp11 1 = (1:ℝ) := clamp11_of_mem ⟨by norm_num, le_rfl⟩
  rw [circleArcPath, ContinuousMap.coe_mk, h]
  congr 1
  ring

lemma circleArcPath_range {θ₁ θ₂ : ℝ} (h : θ₁ ≤ θ₂) :
    Set.range (circleArcPath θ₁ θ₂) = Circle.exp '' Set.Icc θ₁ θ₂ := by
  ext z
  constructor
  · rintro ⟨t, rfl⟩
    have hc := clamp11_mem t
    have h1 : 0 ≤ (1 - clamp11 t) / 2 := by linarith [hc.1, hc.2]
    have h2 : 0 ≤ (1 + clamp11 t) / 2 := by linarith [hc.1, hc.2]
    have hsum : (1 - clamp11 t) / 2 + (1 + clamp11 t) / 2 = 1 := by ring
    exact ⟨_, ⟨by nlinarith, by nlinarith⟩, rfl⟩
  · rintro ⟨θ, hθ, rfl⟩
    rcases lt_or_eq_of_le h with hlt | heq
    · refine ⟨(2 * θ - θ₁ - θ₂) / (θ₂ - θ₁), ?_⟩
      rw [circleArcPath, ContinuousMap.coe_mk]
      have hden : (0:ℝ) < θ₂ - θ₁ := by linarith
      have hc1 : -1 ≤ (2 * θ - θ₁ - θ₂) / (θ₂ - θ₁) := by
        rw [le_div_iff₀ hden]; linarith [hθ.1]
      have hc2 : (2 * θ - θ₁ - θ₂) / (θ₂ - θ₁) ≤ 1 := by
        rw [div_le_iff₀ hden]; linarith [hθ.2]
      rw [clamp11_of_mem ⟨hc1, hc2⟩]
      congr 1
      field_simp
      ring
    · refine ⟨0, ?_⟩
      have hθeq : θ = θ₂ := by
        rw [← heq] at hθ
        rw [le_antisymm hθ.2 hθ.1, heq]
      rw [circleArcPath, ContinuousMap.coe_mk, hθeq,
        show clamp11 0 = (0:ℝ) from clamp11_of_mem ⟨by norm_num, by norm_num⟩]
      congr 1
      rw [← heq]
      ring

lemma exists_angle_period (θ θ₁ : ℝ) :
    ∃ k : ℤ, θ + k * (2 * Real.pi) ∈ Set.Icc θ₁ (θ₁ + 2 * Real.pi) := by
  refine ⟨⌈(θ₁ - θ) / (2 * Real.pi)⌉, ?_, ?_⟩
  · have h : (θ₁ - θ) / (2 * Real.pi) ≤ ((⌈(θ₁ - θ) / (2 * Real.pi)⌉ : ℤ) : ℝ) :=
      Int.le_ceil _
    have hp : (0:ℝ) < 2 * Real.pi := by positivity
    have h2 := mul_le_mul_of_nonneg_right h hp.le
    rw [div_mul_cancel₀] at h2
    · linarith
    · exact ne_of_gt hp
  · have h : ((⌈(θ₁ - θ) / (2 * Real.pi)⌉ : ℤ) : ℝ) < (θ₁ - θ) / (2 * Real.pi) + 1 :=
      Int.ceil_lt_add_one _
    have hp : (0:ℝ) < 2 * Real.pi := by positivity
    have h2 := mul_lt_mul_of_pos_right h hp
    rw [add_mul, div_mul_cancel₀] at h2
    · linarith
    · exact ne_of_gt hp

lemma circleArcPath_union {θ₁ θ₂ : ℝ} (h1 : θ₁ < θ₂) (h2 : θ₂ ≤ θ₁ + 2 * Real.pi) :
    Set.range (circleArcPath θ₁ θ₂) ∪ Set.range (circleArcPath θ₂ (θ₁ + 2 * Real.pi)) =
      Set.univ := by
  ext z
  simp only [Set.mem_union, Set.mem_univ, iff_true]
  obtain ⟨θ, rfl⟩ := Circle.exp_surjective z
  obtain ⟨k, hk⟩ := exists_angle_period θ θ₁
  set θ' := θ + k * (2 * Real.pi) with hθ'def
  have hexp : Circle.exp θ' = Circle.exp θ := by
    rw [hθ'def, Circle.exp_add, Circle.exp_int_mul_two_pi, mul_one]
  rw [← hexp, circleArcPath_range h1.le, circleArcPath_range (by linarith)]
  simp only [Set.mem_image, Set.mem_Icc]
  rcases le_total θ' θ₂ with hl | hl
  · exact Or.inl ⟨θ', ⟨hk.1, hl⟩, rfl⟩
  · exact Or.inr ⟨θ', ⟨hl, hk.2⟩, rfl⟩

lemma circleArcPath_inter {θ₁ θ₂ : ℝ} (h1 : θ₁ < θ₂) (h2 : θ₂ ≤ θ₁ + 2 * Real.pi) :
    Set.range (circleArcPath θ₁ θ₂) ∩ Set.range (circleArcPath θ₂ (θ₁ + 2 * Real.pi)) =
      {Circle.exp θ₁, Circle.exp θ₂} := by
  rw [circleArcPath_range h1.le, circleArcPath_range (by linarith)]
  ext z
  constructor
  · rintro ⟨⟨θ, hθ, rfl⟩, θ', hθ', hm⟩
    rw [Circle.exp_eq_exp] at hm
    obtain ⟨m, hm⟩ := hm
    have hp : (0:ℝ) < 2 * Real.pi := by positivity
    have hmlow : (0:ℝ) ≤ (m:ℝ) := by
      have h3 : θ' - θ = (m:ℝ) * (2 * Real.pi) := by linarith [hm]
      have h4 : θ - θ' ≤ 0 := by linarith [hθ.2, hθ'.1]
      nlinarith [Real.pi_pos]
    have hmhigh : (m:ℝ) ≤ 1 := by
      have h3 : θ' - θ = (m:ℝ) * (2 * Real.pi) := by linarith [hm]
      have h4 : -2 * Real.pi ≤ θ - θ' := by linarith [hθ.1, hθ'.2]
      nlinarith [Real.pi_pos]
    have hm0 : (0:ℤ) ≤ m := by exact_mod_cast hmlow
    have hm1 : m ≤ 1 := by exact_mod_cast hmhigh
    have hmcase : m = 0 ∨ m = 1 := by omega
    rw [Set.mem_insert_iff, Set.mem_singleton_iff]
    rcases hmcase with rfl | rfl
    · right
      have h4 : θ' = θ := by simpa using hm
      have h5 : θ = θ₂ := le_antisymm hθ.2 (by linarith [hθ'.1, h4])
      rw [h5]
    · left
      have h4 : θ' = θ + 2 * Real.pi := by simpa using hm
      have h5 : θ = θ₁ := le_antisymm (by linarith [hθ'.2, h4]) hθ.1
      rw [h5]
  · intro hz
    rw [Set.mem_insert_iff, Set.mem_singleton_iff] at hz
    rcases hz with hz | hz
    · rw [hz]
      exact ⟨⟨θ₁, ⟨le_rfl, h1.le⟩, rfl⟩,
        ⟨θ₁ + 2 * Real.pi, ⟨by linarith, le_rfl⟩, by rw [Circle.exp_add_two_pi]⟩⟩
    · rw [hz]
      exact ⟨⟨θ₂, ⟨h1.le, le_rfl⟩, rfl⟩, ⟨θ₂, ⟨le_rfl, h2⟩, rfl⟩⟩


end Arcs

section Similarity

/-- The similarity `z ↦ 2 (z - (a+b)/2)/(b-a)`, sending `a` to `-1` and `b` to `1`. -/
noncomputable def sim (a b z : ℂ) : ℂ := 2 * (z - (a + b) / 2) / (b - a)

/-- The inverse of `sim a b`. -/
noncomputable def invSim (a b w : ℂ) : ℂ := (b - a) / 2 * w + (a + b) / 2

lemma sim_continuous (a b : ℂ) : Continuous (sim a b) := by unfold sim; fun_prop

lemma invSim_continuous (a b : ℂ) : Continuous (invSim a b) := by unfold invSim; fun_prop

lemma sim_sub {a b : ℂ} (hab : a ≠ b) (z w : ℂ) :
    sim a b z - sim a b w = (2 / (b - a)) * (z - w) := by
  have hb : b - a ≠ 0 := sub_ne_zero.mpr (Ne.symm hab)
  unfold sim
  field_simp
  ring

lemma sim_apply_a {a b : ℂ} (hab : a ≠ b) : sim a b a = -1 := by
  have hb : b - a ≠ 0 := sub_ne_zero.mpr (Ne.symm hab)
  unfold sim
  field_simp
  ring

lemma sim_apply_b {a b : ℂ} (hab : a ≠ b) : sim a b b = 1 := by
  have hb : b - a ≠ 0 := sub_ne_zero.mpr (Ne.symm hab)
  unfold sim
  field_simp
  ring

lemma invSim_sim {a b : ℂ} (hab : a ≠ b) (z : ℂ) : invSim a b (sim a b z) = z := by
  have hb : b - a ≠ 0 := sub_ne_zero.mpr (Ne.symm hab)
  unfold sim invSim
  field_simp
  ring

lemma sim_invSim {a b : ℂ} (hab : a ≠ b) (w : ℂ) : sim a b (invSim a b w) = w := by
  have hb : b - a ≠ 0 := sub_ne_zero.mpr (Ne.symm hab)
  unfold sim invSim
  field_simp
  ring

lemma sim_injective {a b : ℂ} (hab : a ≠ b) : Function.Injective (sim a b) := by
  intro z w hzw
  have hb : b - a ≠ 0 := sub_ne_zero.mpr (Ne.symm hab)
  have h := sim_sub hab z w
  rw [hzw, sub_self] at h
  have h2 : (2 / (b - a) : ℂ) ≠ 0 := div_ne_zero two_ne_zero hb
  have h3 : z - w = 0 := by
    rcases mul_eq_zero.mp h.symm with h4 | h4
    · exact absurd h4 h2
    · exact h4
  exact sub_eq_zero.mp h3

lemma sim_norm_sub {a b : ℂ} (hab : a ≠ b) (z w : ℂ) :
    ‖sim a b z - sim a b w‖ = 2 / ‖b - a‖ * ‖z - w‖ := by
  rw [sim_sub hab, norm_mul, norm_div]
  norm_num

lemma sim_preimage_compl_range {a b : ℂ} (hab : a ≠ b) (γ : C(Circle, ℂ)) :
    sim a b ⁻¹' (Set.range (fun t : Circle => sim a b (γ t)))ᶜ = (Set.range γ)ᶜ := by
  ext z
  simp only [Set.mem_preimage, Set.mem_compl_iff, Set.mem_range]
  constructor
  · intro h ⟨t, ht⟩
    exact h ⟨t, by rw [ht]⟩
  · intro h ⟨t, ht⟩
    exact h ⟨t, sim_injective hab ht⟩

lemma sim_preimage_eq_image {a b : ℂ} (hab : a ≠ b) (U : Set ℂ) :
    sim a b ⁻¹' U = invSim a b '' U := by
  ext z
  constructor
  · intro hz
    exact ⟨sim a b z, hz, invSim_sim hab z⟩
  · rintro ⟨w, hw, rfl⟩
    show sim a b (invSim a b w) ∈ U
    rw [sim_invSim hab w]; exact hw


end Similarity

section PlaneSetup

/-- The closed rectangle `E(-1,1;-2,2)`. -/
abbrev Erect : Set ℂ := {z : ℂ | z.re ∈ Set.Icc (-1:ℝ) 1 ∧ z.im ∈ Set.Icc (-2:ℝ) 2}

/-- The vertical segment joining `s = -2i` and `n = 2i`. -/
abbrev nsSeg : Set ℂ := {z : ℂ | z.re = 0 ∧ z.im ∈ Set.Icc (-2:ℝ) 2}

/-- The vertical segment `ns`, as a path on `ℝ` (constant outside `[-1,1]`). -/
noncomputable def nsPath : C(ℝ, ℂ) :=
  ⟨fun t => (((clamp11 t) * 2 : ℝ) : ℂ) * Complex.I, by
    have h : Continuous fun t : ℝ => clamp11 t := clamp11_continuous
    fun_prop⟩

@[simp] lemma nsPath_re (t : ℝ) : (nsPath t).re = 0 := by simp [nsPath]
@[simp] lemma nsPath_im (t : ℝ) : (nsPath t).im = clamp11 t * 2 := by simp [nsPath]

@[simp] lemma nsPath_neg_one : nsPath (-1) = -2 * Complex.I := by
  rw [nsPath, ContinuousMap.coe_mk,
    show clamp11 (-1) = (-1:ℝ) from clamp11_of_mem ⟨le_rfl, by norm_num⟩]
  norm_num

@[simp] lemma nsPath_one : nsPath 1 = 2 * Complex.I := by
  rw [nsPath, ContinuousMap.coe_mk,
    show clamp11 1 = (1:ℝ) from clamp11_of_mem ⟨by norm_num, le_rfl⟩]
  norm_num

lemma nsPath_mem_Erect (t : ℝ) : nsPath t ∈ Erect := by
  have h := clamp11_mem t
  exact ⟨⟨by rw [nsPath_re]; norm_num, by rw [nsPath_re]; norm_num⟩,
    ⟨by rw [nsPath_im]; linarith [h.1], by rw [nsPath_im]; linarith [h.2]⟩⟩

lemma norm_sq_eq (z : ℂ) : ‖z‖^2 = z.re^2 + z.im^2 := by
  rw [Complex.sq_norm, Complex.normSq_apply]; ring

lemma norm_add_one_sq (z : ℂ) : ‖z + 1‖^2 = (z.re + 1)^2 + z.im^2 := by
  rw [norm_sq_eq]; simp

theorem range_subset_Erect {γ : C(Circle, ℂ)} (hdiam : ∀ s t : Circle, ‖γ s - γ t‖ ≤ 2)
    (hneg : ∃ t : Circle, γ t = -1) (hpos : ∃ t : Circle, γ t = 1) :
    Set.range γ ⊆ Erect := by
  rintro z ⟨t, rfl⟩
  obtain ⟨t₁, h₁⟩ := hneg
  obtain ⟨t₂, h₂⟩ := hpos
  have hA : ‖γ t + 1‖ ≤ 2 := by have h := hdiam t t₁; rw [h₁] at h; simpa using h
  have hB : ‖γ t - 1‖ ≤ 2 := by have h := hdiam t t₂; rwa [h₂] at h
  have hAre : |(γ t + 1).re| ≤ 2 := le_trans (Complex.abs_re_le_norm _) hA
  have hBre : |(γ t - 1).re| ≤ 2 := le_trans (Complex.abs_re_le_norm _) hB
  have hAim : |(γ t + 1).im| ≤ 2 := le_trans (Complex.abs_im_le_norm _) hA
  simp only [Complex.add_re, Complex.one_re, Complex.sub_re, Complex.add_im, Complex.one_im,
    Complex.sub_im, sub_zero] at hAre hBre hAim
  refine ⟨⟨?_, ?_⟩, ⟨?_, ?_⟩⟩
  · linarith [(abs_le.mp hBre).1]
  · linarith [(abs_le.mp hAre).2]
  · linarith [(abs_le.mp hAim).1]
  · linarith [(abs_le.mp hAim).2]

theorem eq_one_or_neg_one_of_boundary {γ : C(Circle, ℂ)}
    (hdiam : ∀ s t : Circle, ‖γ s - γ t‖ ≤ 2)
    (hneg : ∃ t : Circle, γ t = -1) (hpos : ∃ t : Circle, γ t = 1)
    {z : ℂ} (hz : z ∈ Set.range γ)
    (hb : z.re = 1 ∨ z.re = -1 ∨ z.im = 2 ∨ z.im = -2) :
    z = 1 ∨ z = -1 := by
  obtain ⟨t₁, h₁⟩ := hneg
  obtain ⟨t₂, h₂⟩ := hpos
  obtain ⟨t, ht⟩ := hz
  subst ht
  have hA : ‖γ t + 1‖ ≤ 2 := by have h := hdiam t t₁; rw [h₁] at h; simpa using h
  have hB : ‖γ t - 1‖ ≤ 2 := by have h := hdiam t t₂; rwa [h₂] at h
  have hA2 : ‖γ t + 1‖^2 ≤ 4 := by nlinarith [norm_nonneg (γ t + 1)]
  have hB2 : ‖γ t - 1‖^2 ≤ 4 := by nlinarith [norm_nonneg (γ t - 1)]
  rw [norm_add_one_sq] at hA2
  rcases hb with hb | hb | hb | hb
  · -- z.re = 1
    have him : (γ t).im = 0 := by nlinarith [sq_nonneg (γ t).im]
    left
    apply Complex.ext
    · simpa using hb
    · simpa [him] using (show (γ t).im = (0:ℂ).im from by simp [him])
  · -- z.re = -1
    have hB3 : ‖γ t - 1‖^2 = ((γ t).re - 1)^2 + (γ t).im^2 := by rw [norm_sq_eq]; simp
    rw [hB3] at hB2
    have him : (γ t).im = 0 := by nlinarith [sq_nonneg (γ t).im]
    right
    apply Complex.ext
    · simpa using hb
    · simpa [him] using (show (γ t).im = (0:ℂ).im from by simp [him])
  · -- z.im = 2
    have : ((γ t).re + 1)^2 = 0 := by nlinarith
    have hre : (γ t).re = -1 := by nlinarith [sq_nonneg ((γ t).re + 1)]
    have hB3 : ‖γ t - 1‖^2 = ((γ t).re - 1)^2 + (γ t).im^2 := by rw [norm_sq_eq]; simp
    rw [hB3] at hB2
    exfalso
    nlinarith [hb, hre]
  · -- z.im = -2
    have : ((γ t).re + 1)^2 = 0 := by nlinarith
    have hre : (γ t).re = -1 := by nlinarith [sq_nonneg ((γ t).re + 1)]
    have hB3 : ‖γ t - 1‖^2 = ((γ t).re - 1)^2 + (γ t).im^2 := by rw [norm_sq_eq]; simp
    rw [hB3] at hB2
    exfalso
    nlinarith [hb, hre]

end PlaneSetup

section ArcsOfJ

lemma circleArcPath_of_le_neg_one {θ₁ θ₂ t : ℝ} (h : t ≤ -1) :
    circleArcPath θ₁ θ₂ t = Circle.exp θ₁ := by
  have hc : clamp11 t = (-1:ℝ) := by
    rw [clamp11, min_eq_left (by linarith), max_eq_left (by linarith)]
  change Circle.exp (((1 - clamp11 t) / 2) * θ₁ + ((1 + clamp11 t) / 2) * θ₂) = Circle.exp θ₁
  rw [hc]
  congr 1
  ring

lemma circleArcPath_of_ge_one {θ₁ θ₂ t : ℝ} (h : 1 ≤ t) :
    circleArcPath θ₁ θ₂ t = Circle.exp θ₂ := by
  have hc : clamp11 t = (1:ℝ) := by
    rw [clamp11, min_eq_right (by linarith), max_eq_right (by norm_num)]
  change Circle.exp (((1 - clamp11 t) / 2) * θ₁ + ((1 + clamp11 t) / 2) * θ₂) = Circle.exp θ₂
  rw [hc]
  congr 1
  ring

/-- `γ` composed with a circle arc: a path on `ℝ`, constant outside `[-1,1]`. -/
noncomputable def arcPath (γ : C(Circle, ℂ)) (θ₁ θ₂ : ℝ) : C(ℝ, ℂ) :=
  γ.comp (circleArcPath θ₁ θ₂)

@[simp] lemma arcPath_neg_one (γ : C(Circle, ℂ)) (θ₁ θ₂ : ℝ) :
    arcPath γ θ₁ θ₂ (-1) = γ (Circle.exp θ₁) := by
  simp only [arcPath, ContinuousMap.comp_apply, circleArcPath_neg_one]

@[simp] lemma arcPath_one (γ : C(Circle, ℂ)) (θ₁ θ₂ : ℝ) :
    arcPath γ θ₁ θ₂ 1 = γ (Circle.exp θ₂) := by
  simp only [arcPath, ContinuousMap.comp_apply, circleArcPath_one]

lemma arcPath_range (γ : C(Circle, ℂ)) {θ₁ θ₂ : ℝ} (h : θ₁ ≤ θ₂) :
    Set.range (arcPath γ θ₁ θ₂) = γ '' (Circle.exp '' Set.Icc θ₁ θ₂) := by
  rw [arcPath, ContinuousMap.coe_comp, Set.range_comp, circleArcPath_range h]

lemma arcPath_union (γ : C(Circle, ℂ)) {θ₁ θ₂ : ℝ} (h1 : θ₁ < θ₂)
    (h2 : θ₂ ≤ θ₁ + 2 * Real.pi) :
    Set.range (arcPath γ θ₁ θ₂) ∪ Set.range (arcPath γ θ₂ (θ₁ + 2 * Real.pi)) =
      Set.range γ := by
  rw [arcPath_range γ h1.le, arcPath_range γ (by linarith), ← Set.image_union,
    ← circleArcPath_range h1.le, ← circleArcPath_range (by linarith),
    circleArcPath_union h1 h2, Set.image_univ]

lemma arcPath_inter (γ : C(Circle, ℂ)) (hγ : Function.Injective γ) {θ₁ θ₂ : ℝ}
    (h1 : θ₁ < θ₂) (h2 : θ₂ ≤ θ₁ + 2 * Real.pi) :
    Set.range (arcPath γ θ₁ θ₂) ∩ Set.range (arcPath γ θ₂ (θ₁ + 2 * Real.pi)) =
      {γ (Circle.exp θ₁), γ (Circle.exp θ₂)} := by
  rw [arcPath_range γ h1.le, arcPath_range γ (by linarith), ← Set.image_inter hγ,
    ← circleArcPath_range h1.le, ← circleArcPath_range (by linarith),
    circleArcPath_inter h1 h2, Set.image_pair]

lemma arcPath_injOn (γ : C(Circle, ℂ)) (hγ : Function.Injective γ) {θ₁ θ₂ : ℝ}
    (h1 : θ₁ < θ₂) (h2 : θ₂ - θ₁ < 2 * Real.pi) :
    Set.InjOn (arcPath γ θ₁ θ₂) (Set.Icc (-1:ℝ) 1) := by
  intro t ht t' ht' heq
  have hc : clamp11 t = t := clamp11_of_mem ht
  have hc' : clamp11 t' = t' := clamp11_of_mem ht'
  have h := hγ heq
  simp only [arcPath, ContinuousMap.comp_apply, circleArcPath, ContinuousMap.coe_mk,
    hc, hc'] at h
  have hmem1 : ((1 - t) / 2) * θ₁ + ((1 + t) / 2) * θ₂ ∈ Set.Icc θ₁ θ₂ :=
    ⟨by nlinarith [ht.1, ht.2, h1], by nlinarith [ht.1, ht.2, h1]⟩
  have hmem2 : ((1 - t') / 2) * θ₁ + ((1 + t') / 2) * θ₂ ∈ Set.Icc θ₁ θ₂ :=
    ⟨by nlinarith [ht'.1, ht'.2, h1], by nlinarith [ht'.1, ht'.2, h1]⟩
  have hthis : ((1 - t) / 2) * θ₁ + ((1 + t) / 2) * θ₂ =
      ((1 - t') / 2) * θ₁ + ((1 + t') / 2) * θ₂ :=
    Circle.exp_injOn_Icc h2 hmem1 hmem2 h
  have hlin : (t - t') * (θ₂ - θ₁) = 0 := by
    linear_combination 2 * hthis
  have hne : θ₂ - θ₁ ≠ 0 := by linarith
  rcases mul_eq_zero.mp hlin with h0 | h0
  · linarith
  · exact absurd h0 hne

lemma arcPath_mem_Erect {γ : C(Circle, ℂ)} (hE : Set.range γ ⊆ Erect)
    (θ₁ θ₂ : ℝ) (t : ℝ) : arcPath γ θ₁ θ₂ t ∈ Erect :=
  hE ⟨circleArcPath θ₁ θ₂ t, rfl⟩

lemma arcPath_outside (γ : C(Circle, ℂ)) {θ₁ θ₂ : ℝ} (t : ℝ) (ht : t ∉ Set.Icc (-1:ℝ) 1) :
    arcPath γ θ₁ θ₂ t = γ (Circle.exp θ₁) ∨ arcPath γ θ₁ θ₂ t = γ (Circle.exp θ₂) := by
  have ht' : t < -1 ∨ 1 < t := by
    by_contra hcon
    push Not at hcon
    exact ht ⟨hcon.1, hcon.2⟩
  rcases ht' with h | h
  · left
    rw [arcPath, ContinuousMap.comp_apply, circleArcPath_of_le_neg_one (by linarith)]
  · right
    rw [arcPath, ContinuousMap.comp_apply, circleArcPath_of_ge_one (by linarith)]

end ArcsOfJ

section TwoArcs

open Circle

/-- The two arcs of a Jordan curve between two distinct points, oriented and with the
endpoint conditions needed for the Maehara argument. -/
theorem exists_two_arcs (γ : C(Circle, ℂ)) (hγ : Function.Injective γ)
    (hneg : ∃ t : Circle, γ t = -1) (hpos : ∃ t : Circle, γ t = 1) :
    ∃ P Q : C(ℝ, ℂ), P (-1) = -1 ∧ P 1 = 1 ∧ Q (-1) = 1 ∧ Q 1 = -1 ∧
      (∀ t : ℝ, t ∉ Set.Icc (-1:ℝ) 1 → P t = -1 ∨ P t = 1) ∧
      (∀ t : ℝ, t ∉ Set.Icc (-1:ℝ) 1 → Q t = 1 ∨ Q t = -1) ∧
      Set.range P ∪ Set.range Q = Set.range γ ∧
      Set.range P ∩ Set.range Q = {(1:ℂ), -1} ∧
      Set.InjOn P (Set.Icc (-1:ℝ) 1) ∧ Set.InjOn Q (Set.Icc (-1:ℝ) 1) := by
  obtain ⟨u, hu⟩ := hneg
  obtain ⟨v, hv⟩ := hpos
  let α : ℝ := (Circle.argEquiv u : ℝ)
  let β : ℝ := (Circle.argEquiv v : ℝ)
  have hαmem : α ∈ Set.Ioc (-Real.pi) Real.pi := (Circle.argEquiv u).2
  have hβmem : β ∈ Set.Ioc (-Real.pi) Real.pi := (Circle.argEquiv v).2
  have hexpα : Circle.exp α = u := by
    show Circle.exp (↑(Circle.argEquiv u) : ℝ) = u
    rw [Circle.argEquiv_apply_coe, Circle.exp_arg]
  have hexpβ : Circle.exp β = v := by
    show Circle.exp (↑(Circle.argEquiv v) : ℝ) = v
    rw [Circle.argEquiv_apply_coe, Circle.exp_arg]
  have hne : α ≠ β := by
    intro h
    have huv : u = v := by rw [← hexpα, ← hexpβ, h]
    have : γ u = γ v := by rw [huv]
    rw [hu, hv] at this
    norm_num at this
  have hpipos : (0:ℝ) < Real.pi := Real.pi_pos
  obtain ⟨θ₂, hαθ₂, hθ₂le, hθ₂exp, hθ₂diff⟩ :
      ∃ θ₂ : ℝ, α < θ₂ ∧ θ₂ ≤ α + 2 * Real.pi ∧ Circle.exp θ₂ = v ∧ θ₂ - α < 2 * Real.pi := by
    rcases lt_or_gt_of_ne hne with h | h
    · exact ⟨β, h, by linarith [hαmem.1, hβmem.2], hexpβ,
        by linarith [hαmem.1, hβmem.2]⟩
    · exact ⟨β + 2 * Real.pi, by linarith [hαmem.2, hβmem.1],
        by linarith, by rw [Circle.exp_add_two_pi, hexpβ], by linarith⟩
  refine ⟨arcPath γ α θ₂, arcPath γ θ₂ (α + 2 * Real.pi), ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [arcPath_neg_one, hexpα, hu]
  · rw [arcPath_one, hθ₂exp, hv]
  · rw [arcPath_neg_one, hθ₂exp, hv]
  · rw [arcPath_one, Circle.exp_add_two_pi, hexpα, hu]
  · intro t ht
    rcases arcPath_outside γ t ht with h | h
    · exact Or.inl (by rw [h, hexpα, hu])
    · exact Or.inr (by rw [h, hθ₂exp, hv])
  · intro t ht
    rcases arcPath_outside γ t ht with h | h
    · exact Or.inl (by rw [h, hθ₂exp, hv])
    · exact Or.inr (by rw [h, Circle.exp_add_two_pi, hexpα, hu])
  · exact arcPath_union γ hαθ₂ hθ₂le
  · rw [arcPath_inter γ hγ hαθ₂ hθ₂le, hexpα, hθ₂exp, hu, hv, Set.pair_comm]
  · exact arcPath_injOn γ hγ hαθ₂ hθ₂diff
  · exact arcPath_injOn γ hγ (by linarith [hθ₂diff]) (by linarith)

/-- Existence of a topmost point of `J ∩ nsSeg`. -/
theorem exists_top_ns {γ : C(Circle, ℂ)} (P : C(ℝ, ℂ))
    (hE : Set.range γ ⊆ Erect) (hP1 : P (-1) = -1) (hP2 : P 1 = 1)
    (hP : ∀ t : ℝ, P t ∈ Set.range γ) :
    ∃ l ∈ Set.range γ, l.re = 0 ∧ ∀ z ∈ Set.range γ, z.re = 0 → z.im ≤ l.im := by
  have hnsseg_closed : IsClosed nsSeg := by
    have h1 : IsClosed {z : ℂ | z.re = 0} := isClosed_eq Complex.continuous_re continuous_const
    have h2 : IsClosed {x : ℂ | x.im ∈ Set.Icc (-2:ℝ) 2} :=
      isClosed_Icc.preimage Complex.continuous_im
    exact h1.inter h2
  have hcomp : IsCompact (Set.range γ ∩ nsSeg) :=
    (isCompact_range γ.continuous).inter_right hnsseg_closed
  have hnonempty : (Set.range γ ∩ nsSeg).Nonempty := by
    obtain ⟨s, hs, t, ht, hst⟩ := crossing_lemma P nsPath
      (fun t ht => hE (hP t))
      (fun t ht => nsPath_mem_Erect t)
      (by rw [hP1]; norm_num)
      (by rw [hP2]; norm_num)
      (by rw [nsPath_neg_one]; norm_num)
      (by rw [nsPath_one]; norm_num)
    exact ⟨P s, ⟨hP s, by rw [hst]; exact ⟨nsPath_re t, (nsPath_mem_Erect t).2⟩⟩⟩
  obtain ⟨l, hl, hlmax⟩ := hcomp.exists_isMaxOn hnonempty Complex.continuous_im.continuousOn
  refine ⟨l, hl.1, hl.2.1, ?_⟩
  intro z hz hzre
  exact hlmax ⟨hz, ⟨hzre, (hE hz).2⟩⟩

end TwoArcs

section Transport

/-- **The Jordan curve theorem in the plane** (as stated for the target theorem).
This is the analytic core; see `Submission.Commons.Topology.Jordan.plane_separation`. -/
theorem jordan_curve_separation_plane (γ : C(Circle, ℂ)) (hγ : Function.Injective γ) :
    ∃ U V : Set ℂ, IsOpen U ∧ IsOpen V ∧ IsConnected U ∧ IsConnected V ∧ Disjoint U V ∧
      Bornology.IsBounded U ∧ ¬ Bornology.IsBounded V ∧ U ∪ V = (Set.range γ)ᶜ :=
  Commons.Topology.Jordan.plane_separation γ hγ

/-- The Jordan curve theorem for the plane `EuclideanSpace ℝ (Fin 2)`, obtained from the
complex plane by a linear isometry. -/
theorem jordan_curve_separation (γ : C(Circle, EuclideanSpace ℝ (Fin 2)))
    (hγ : Function.Injective γ) :
    ∃ U V : Set (EuclideanSpace ℝ (Fin 2)),
      IsOpen U ∧ IsOpen V ∧ IsConnected U ∧ IsConnected V ∧ Disjoint U V ∧
        Bornology.IsBounded U ∧ ¬ Bornology.IsBounded V ∧
        U ∪ V = (Set.range γ)ᶜ := by
  classical
  let e : ℂ ≃ₗᵢ[ℝ] EuclideanSpace ℝ (Fin 2) :=
    Complex.isometryOfOrthonormal (EuclideanSpace.basisFun (Fin 2) ℝ)
  let γ' : C(Circle, ℂ) := ⟨fun t => e.symm (γ t), e.symm.continuous.comp γ.continuous⟩
  have hγ' : Function.Injective γ' := fun a b h => hγ (e.symm.injective h)
  obtain ⟨U, V, hUo, hVo, hUc, hVc, hdisj, hUb, hVb, hUV⟩ :=
    jordan_curve_separation_plane γ' hγ'
  have hrange : Set.range γ' = e.symm '' Set.range γ := by
    ext z
    constructor
    · rintro ⟨t, rfl⟩
      exact ⟨γ t, ⟨t, rfl⟩, rfl⟩
    · rintro ⟨w, ⟨t, rfl⟩, rfl⟩
      exact ⟨t, rfl⟩
  have hnorm : ∀ x : ℂ, ‖e x‖ = ‖x‖ := by
    intro x
    calc ‖e x‖ = dist (e x) 0 := (dist_zero_right _).symm
      _ = dist (e x) (e 0) := by rw [map_zero]
      _ = dist x 0 := e.isometry.dist_eq x 0
      _ = ‖x‖ := dist_zero_right _
  refine ⟨e '' U, e '' V, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact (e.toHomeomorph).isOpen_image.mpr hUo
  · exact (e.toHomeomorph).isOpen_image.mpr hVo
  · exact hUc.image _ e.continuous.continuousOn
  · exact hVc.image _ e.continuous.continuousOn
  · exact hdisj.image e.injective.injOn (Set.subset_univ _) (Set.subset_univ _)
  · obtain ⟨R, hR⟩ := (Metric.isBounded_iff_subset_closedBall (s := U) (0:ℂ)).mp hUb
    refine (Metric.isBounded_iff_subset_closedBall (s := e '' U)
      (0 : EuclideanSpace ℝ (Fin 2))).mpr ⟨R, ?_⟩
    rintro y ⟨x, hx, rfl⟩
    have hx' : ‖x‖ ≤ R := by
      have := hR hx
      rwa [Metric.mem_closedBall, dist_zero_right] at this
    rw [Metric.mem_closedBall, dist_zero_right, hnorm x]
    exact hx'
  · intro hb
    apply hVb
    obtain ⟨R, hR⟩ := (Metric.isBounded_iff_subset_closedBall (s := e '' V)
      (0 : EuclideanSpace ℝ (Fin 2))).mp hb
    refine (Metric.isBounded_iff_subset_closedBall (s := V) (0:ℂ)).mpr ⟨R, ?_⟩
    intro x hx
    have h2 : ‖e x‖ ≤ R := by
      have := hR ⟨x, hx, rfl⟩
      rwa [Metric.mem_closedBall, dist_zero_right] at this
    rw [Metric.mem_closedBall, dist_zero_right, ← hnorm x]
    exact h2
  · rw [← Set.image_union, hUV, hrange, Set.image_compl_eq e.bijective, Set.image_image]
    rw [show (fun x : EuclideanSpace ℝ (Fin 2) => e (e.symm x)) = id from
      funext fun x => e.apply_symm_apply x, Set.image_id]

end Transport
