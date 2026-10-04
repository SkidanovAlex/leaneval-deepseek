import ChallengeDeps
import Mathlib
import Submission.Work.Diff.STE.B3.tame_defs
import Submission.Work.Diff.STE.B3.ENormSq_mat_inv_le
import Submission.Work.Diff.STE.B3.ENormSq_basic
import Submission.Work.Diff.STE.Torus
import Submission.Work.Diff.STE.periodization_contDiff_periodic
import Submission.Work.Diff.STE.pd_periodization
import Submission.Work.Diff.STE.Lead.Gal.PerKit
import Submission.Work.Diff.STE.B3.integral_unitCube_eq_centreCube
import Submission.Work.Diff.STE.Lead.GalTame.periodic_eq_of_eqOn_openCube

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

namespace Work.Diff.STE.Lead.GalTame

open MeasureTheory

set_option maxHeartbeats 1000000


/-! ## Auxiliary definitions -/

/-- The Kronecker delta as a real scalar. -/
def kd {n : ℕ} (i j : Fin n) : ℝ := if i = j then (1 : ℝ) else 0

lemma kd_apply {n : ℕ} (i j : Fin n) : kd i j = if i = j then (1 : ℝ) else 0 := rfl

@[simp] lemma kd_self {n : ℕ} (i : Fin n) : kd i i = 1 := by simp [kd]

lemma kd_of_ne {n : ℕ} {i j : Fin n} (h : i ≠ j) : kd i j = 0 := by simp [kd, h]

/-- The complex periodisation of a function on `ℝⁿ`. -/
noncomputable def perC {n : ℕ} (f : (Fin n → ℝ) → ℂ) : (Fin n → ℝ) → ℂ :=
  fun z => ∑' m : Fin n → ℤ, f (z + Work.Diff.STE.iVec m)

lemma perC_apply {n : ℕ} (f : (Fin n → ℝ) → ℂ) (z : Fin n → ℝ) :
    perC f z = ∑' m : Fin n → ℤ, f (z + Work.Diff.STE.iVec m) := rfl

lemma perC_periodic {n : ℕ} (f : (Fin n → ℝ) → ℂ) : Work.Diff.STE.Periodic1 (perC f) :=
  Work.Diff.STE.periodization_periodic f

lemma periodic1_add_const {n : ℕ} {f : (Fin n → ℝ) → ℂ} (c : ℂ)
    (hf : Work.Diff.STE.Periodic1 f) : Work.Diff.STE.Periodic1 (fun z => f z + c) := by
  intro i x
  show f (x + Pi.single i 1) + c = f x + c
  rw [hf i x]

lemma periodic1_norm_sq {n : ℕ} {g : (Fin n → ℝ) → ℂ} (hg : Work.Diff.STE.Periodic1 g) :
    Work.Diff.STE.Periodic1 (fun z => ‖g z‖ ^ 2) := by
  intro i x
  show ‖g (x + Pi.single i 1)‖ ^ 2 = ‖g x‖ ^ 2
  rw [hg i x]

lemma support_ofReal_comp {n : ℕ} (f : (Fin n → ℝ) → ℝ) :
    Function.support (fun z : Fin n → ℝ => ((f z : ℝ) : ℂ)) = Function.support f := by
  ext z
  simp only [Function.mem_support, ne_eq]
  constructor
  · intro h hz; exact h (by rw [hz]; norm_num)
  · intro h hz; exact h (Complex.ofReal_eq_zero.mp hz)

lemma support_subset_openCube {n : ℕ} {f : (Fin n → ℝ) → ℂ}
    (hsupp : Function.support f ⊆ Metric.ball (0 : Fin n → ℝ) (1 / 2)) :
    Function.support f ⊆ Set.pi Set.univ (fun _ : Fin n => Set.Ioo (-(1 / 2 : ℝ)) (1 / 2)) := by
  intro x hx
  have hxb : ‖x‖ < 1 / 2 := by
    have h := hsupp hx
    rwa [Metric.mem_ball, dist_zero_right] at h
  rw [Set.mem_pi]
  intro i _
  have h1 : |x i| ≤ ‖x‖ := by
    have h := norm_le_pi_norm x i
    rwa [Real.norm_eq_abs] at h
  rw [Set.mem_Ioo]
  exact abs_lt.mp (by linarith)

lemma measSet_unitCube {ι : Type*} [Fintype ι] [DecidableEq ι] :
    MeasurableSet (Work.Diff.STE.unitCube (ι := ι)) := by
  rw [Work.Diff.STE.unitCube]
  exact MeasurableSet.pi Set.countable_univ (fun _ _ => measurableSet_Ioc)

lemma ENormSq_nonneg {ι : Type*} [Fintype ι] [DecidableEq ι] (m : ℕ) (f : (ι → ℝ) → ℂ) :
    0 ≤ Work.Diff.STE.ENormSq m f := by
  rw [Work.Diff.STE.ENormSq]
  exact Finset.sum_nonneg (fun l _ => integral_nonneg (fun x => by positivity))

/-! ## The periodisation of a ball-supported function -/

/-- On the half-open centred cube `(-1/2,1/2]ⁿ` the periodisation of a function supported in the
*open* ball of radius `1/2` agrees with the function. -/
lemma perC_eq_self_of_mem_halfCube {n : ℕ} {f : (Fin n → ℝ) → ℂ}
    (hsupp : Function.support f ⊆ Metric.ball (0 : Fin n → ℝ) (1 / 2)) {z : Fin n → ℝ}
    (hz : ∀ i, z i ∈ Set.Ioc (-(1 / 2 : ℝ)) (1 / 2)) : perC f z = f z := by
  rw [perC, tsum_eq_single (0 : Fin n → ℤ)]
  · simp
  · intro m hm
    by_contra hc
    have hmem : z + Work.Diff.STE.iVec m ∈ Function.support f := Function.mem_support.mpr hc
    have h1 : ‖z + Work.Diff.STE.iVec m‖ < 1 / 2 := by
      have h := hsupp hmem
      rwa [Metric.mem_ball, dist_zero_right] at h
    have hi : ∃ i, m i ≠ 0 := by
      by_contra h'
      push_neg at h'
      exact hm (funext h')
    obtain ⟨i, hi⟩ := hi
    have h2 : (1 / 2 : ℝ) ≤ |z i + (m i : ℝ)| := by
      have hz1 := (Set.mem_Ioc.mp (hz i)).1
      have hz2 := (Set.mem_Ioc.mp (hz i)).2
      rcases lt_trichotomy (m i) 0 with h | h | h
      · have hm1 : m i ≤ -1 := by omega
        have hm2 : (m i : ℝ) ≤ -1 := by exact_mod_cast hm1
        rw [le_abs]
        right
        linarith
      · exact absurd h hi
      · have hm1 : (1 : ℤ) ≤ m i := by omega
        have hm2 : (1 : ℝ) ≤ (m i : ℝ) := by exact_mod_cast hm1
        rw [le_abs]
        left
        linarith
    have h3 : ‖(z + Work.Diff.STE.iVec m) i‖ ≤ ‖z + Work.Diff.STE.iVec m‖ :=
      norm_le_pi_norm _ i
    have h4 : |z i + (m i : ℝ)| = ‖(z + Work.Diff.STE.iVec m) i‖ := by
      rw [Real.norm_eq_abs]
      simp only [Pi.add_apply, Work.Diff.STE.iVec_apply]
    rw [h4] at h2
    linarith

/-- Every point of `ℝⁿ` can be translated into the half-open centred cube by an integer vector. -/
lemma exists_intVec_add_mem_halfCube {n : ℕ} (z : Fin n → ℝ) :
    ∃ m : Fin n → ℤ, ∀ i, (((fun j => (m j : ℝ)) + z) i) ∈ Set.Ioc (-(1 / 2 : ℝ)) (1 / 2) := by
  have hU : ∀ i : Fin n, ∃ m : ℤ, z i + (m : ℝ) ∈ Set.Ioc (-(1 / 2 : ℝ)) (1 / 2) := by
    intro i
    obtain ⟨m, hm, -⟩ := existsUnique_add_zsmul_mem_Ioc (a := (1 : ℝ)) one_pos (z i) (-(1 / 2))
    refine ⟨m, ?_⟩
    have h1 : (-(1 / 2 : ℝ)) + 1 = 1 / 2 := by norm_num
    rw [h1] at hm
    simpa using hm
  choose m hm using hU
  exact ⟨m, fun i => by
    have h := hm i
    rw [Pi.add_apply, add_comm]
    exact h⟩

/-! ## The derivatives of a ball-supported function vanish outside the ball -/

/-- `pdList` of the zero function is zero. -/
lemma cm_pdList_zero {ι : Type*} [DecidableEq ι] (l : List ι) :
    Work.Diff.STE.pdList l (0 : (ι → ℝ) → ℂ) = 0 := by
  induction l with
  | nil => rfl
  | cons i t ih =>
      simp only [Work.Diff.STE.pdList, List.foldr_cons] at ih ⊢
      rw [ih]
      funext x
      simp [Work.Diff.STE.pd]

/-- `pdVec` of the zero function is zero. -/
lemma cm_pdVec_zero {ι : Type*} [DecidableEq ι] (m : ℕ) (l : Fin m → ι) :
    Work.Diff.STE.pdVec m l (0 : (ι → ℝ) → ℂ) = 0 :=
  cm_pdList_zero (List.ofFn l)

/-- Every iterated partial derivative of a smooth function supported in the open ball of radius
`R > 0` vanishes on the closed complement of that ball (by continuity, it already vanishes off the
closed ball). -/
lemma pdVec_eq_zero_of_le_norm {n m : ℕ} {f : (Fin n → ℝ) → ℂ} {R : ℝ}
    {β : Fin m → Fin n} (hf : ContDiff ℝ (⊤ : ℕ∞) f)
    (hsupp : Function.support f ⊆ Metric.ball (0 : Fin n → ℝ) R) (hRpos : 0 < R) :
    ∀ x : Fin n → ℝ, R ≤ ‖x‖ → Work.Diff.STE.pdVec m β f x = 0 := by
  have hFcont : Continuous (Work.Diff.STE.pdVec m β f) :=
    (Work.Diff.STE.csqp_contDiff_pdList_top (List.ofFn β) hf).continuous
  have hF0onU : ∀ y : Fin n → ℝ, R < ‖y‖ → Work.Diff.STE.pdVec m β f y = 0 := by
    intro y hy
    have hUopen : IsOpen {z : Fin n → ℝ | R < ‖z‖} := isOpen_lt continuous_const continuous_norm
    have hfy : f =ᶠ[nhds y] (fun _ => (0 : ℂ)) := by
      refine Filter.eventually_of_mem (hUopen.mem_nhds hy) (fun z hz => ?_)
      have hznb : z ∉ Metric.ball (0 : Fin n → ℝ) R := by
        simp only [Metric.mem_ball, not_lt, dist_zero_right]
        exact le_of_lt hz
      by_contra hne
      exact hznb (hsupp (Function.mem_support.mpr hne))
    have h1 : Work.Diff.STE.pdVec m β f y = Work.Diff.STE.pdVec m β (fun _ => (0 : ℂ)) y :=
      Work.Diff.STE.csqp_pdVec_congr β hfy
    rw [h1]
    have hzz : Work.Diff.STE.pdVec m β (fun _ : Fin n → ℝ => (0 : ℂ)) = 0 :=
      cm_pdVec_zero m β
    rw [hzz]
    rfl
  intro x hx
  by_cases hxlt : R < ‖x‖
  · exact hF0onU x hxlt
  · have hnorm : ‖x‖ = R := le_antisymm (not_lt.mp hxlt) hx
    have hxpos : 0 < ‖x‖ := lt_of_lt_of_le hRpos hx
    have hcl : x ∈ closure {z : Fin n → ℝ | R < ‖z‖} := by
      rw [Metric.mem_closure_iff]
      intro ε hε
      have ht : 0 < ε / (2 * ‖x‖) := by positivity
      refine ⟨(1 + ε / (2 * ‖x‖)) • x, ?_, ?_⟩
      · change R < ‖(1 + ε / (2 * ‖x‖)) • x‖
        rw [norm_smul, Real.norm_eq_abs,
          abs_of_pos (by positivity : (0 : ℝ) < 1 + ε / (2 * ‖x‖))]
        have hlt : ‖x‖ < (1 + ε / (2 * ‖x‖)) * ‖x‖ := by
          nlinarith [mul_pos ht hxpos, norm_nonneg x]
        linarith [hlt, hnorm]
      · rw [dist_comm, dist_eq_norm]
        have hsub : (1 + ε / (2 * ‖x‖)) • x - x = (ε / (2 * ‖x‖)) • x := by
          rw [add_smul, one_smul, add_sub_cancel_left]
        rw [hsub, norm_smul, Real.norm_eq_abs, abs_of_pos ht]
        have hmul : (ε / (2 * ‖x‖)) * ‖x‖ = ε / 2 := by
          field_simp
        rw [hmul]
        linarith
    have hclosed : IsClosed {z : Fin n → ℝ | Work.Diff.STE.pdVec m β f z = 0} :=
      isClosed_eq hFcont continuous_const
    have hsub : {z : Fin n → ℝ | R < ‖z‖}
        ⊆ {z : Fin n → ℝ | Work.Diff.STE.pdVec m β f z = 0} := fun z hz => hF0onU z hz
    exact hclosed.closure_subset_iff.mpr hsub hcl

/-- The support of an iterated partial derivative of a smooth ball-supported function is again
contained in the open ball. -/
lemma support_pdVec_subset_ball {n m : ℕ} {f : (Fin n → ℝ) → ℂ}
    {β : Fin m → Fin n} (hf : ContDiff ℝ (⊤ : ℕ∞) f)
    (hsupp : Function.support f ⊆ Metric.ball (0 : Fin n → ℝ) (1 / 2)) :
    Function.support (Work.Diff.STE.pdVec m β f) ⊆ Metric.ball (0 : Fin n → ℝ) (1 / 2) := by
  intro x hx
  rw [Metric.mem_ball, dist_zero_right]
  by_contra h
  exact hx (pdVec_eq_zero_of_le_norm hf hsupp (by norm_num) x (not_lt.mp h))

/-! ## The fundamental-domain identity for real-valued functions -/

/-- The integral of a `1`-periodic real-valued function over the unit cube equals its integral over
the centred cube, both being fundamental domains for the action of `ℤⁿ`. -/
lemma integral_unitCube_eq_centreCube_real {ι : Type*} [Fintype ι] [DecidableEq ι]
    (F : (ι → ℝ) → ℝ) (hper : Work.Diff.STE.Periodic1 F) :
    (∫ z in Work.Diff.STE.unitCube (ι := ι), F z)
      = ∫ z in Set.pi Set.univ (fun _ : ι => Set.Ioc (-(1 / 2 : ℝ)) (1 / 2)), F z := by
  have hf : ∀ (n : ι → ℤ) (x : ι → ℝ), F (n +ᵥ x) = F x :=
    fun n x => Work.Diff.STE.B3.Periodic1.add_intVec hper n x
  have hmain := IsAddFundamentalDomain.setIntegral_eq
    (Work.Diff.STE.B3.isAddFundamentalDomain_cube_Ioc (ι := ι) 0)
    (Work.Diff.STE.B3.isAddFundamentalDomain_cube_Ioc (ι := ι) (-(1 / 2)))
    (f := F) hf
  have hone : (-(1 / 2 : ℝ)) + 1 = 1 / 2 := by norm_num
  rw [hone] at hmain
  simpa [Work.Diff.STE.unitCube] using hmain

/-- The open ball of radius `1/2` is contained in the half-open centred cube. -/
lemma ball_subset_centreCube {n : ℕ} :
    Metric.ball (0 : Fin n → ℝ) (1 / 2)
      ⊆ Set.pi Set.univ (fun _ : Fin n => Set.Ioc (-(1 / 2 : ℝ)) (1 / 2)) := by
  intro x hx
  rw [Metric.mem_ball, dist_zero_right] at hx
  rw [Set.mem_pi]
  intro i _
  have h1 : |x i| ≤ ‖x‖ := by
    have h := norm_le_pi_norm x i
    rwa [Real.norm_eq_abs] at h
  have h2 : |x i| < 1 / 2 := by linarith
  rw [Set.mem_Ioc]
  exact ⟨(abs_lt.mp h2).1, le_of_lt (abs_lt.mp h2).2⟩

/-- **The whole-space `L²` norm of a ball-supported function is the `L²` norm of its periodisation
over the unit cube.** -/
lemma integral_normSq_eq_integral_cube_perC {n : ℕ} {F : (Fin n → ℝ) → ℂ}
    (hF : ContDiff ℝ (⊤ : ℕ∞) F)
    (hsupp : Function.support F ⊆ Metric.ball (0 : Fin n → ℝ) (1 / 2)) :
    (∫ x : Fin n → ℝ, ‖F x‖ ^ 2)
      = ∫ x in Work.Diff.STE.unitCube (ι := Fin n), ‖perC F x‖ ^ 2 := by
  have hcube : Function.support F ⊆
      Set.pi Set.univ (fun _ : Fin n => Set.Ioo (-(1 / 2 : ℝ)) (1 / 2)) :=
    support_subset_openCube hsupp
  have hper : Work.Diff.STE.Periodic1 (perC F) := perC_periodic F
  -- (a) the whole-space integral equals the integral over the centred cube
  have ha : (∫ x in Set.pi Set.univ (fun _ : Fin n => Set.Ioc (-(1 / 2 : ℝ)) (1 / 2)), ‖F x‖ ^ 2)
      = ∫ x : Fin n → ℝ, ‖F x‖ ^ 2 := by
    refine setIntegral_eq_integral_of_forall_compl_eq_zero (fun x hx => ?_)
    have hxb : x ∉ Metric.ball (0 : Fin n → ℝ) (1 / 2) :=
      fun hball => hx (ball_subset_centreCube hball)
    have hzero : F x = 0 := by
      by_contra hne
      exact hxb (hsupp (Function.mem_support.mpr hne))
    rw [hzero]
    simp
  -- (b) on the centred cube, the two integrands agree
  have hb : (∫ x in Set.pi Set.univ (fun _ : Fin n => Set.Ioc (-(1 / 2 : ℝ)) (1 / 2)), ‖F x‖ ^ 2)
      = ∫ x in Set.pi Set.univ (fun _ : Fin n => Set.Ioc (-(1 / 2 : ℝ)) (1 / 2)),
          ‖perC F x‖ ^ 2 := by
    refine setIntegral_congr_fun
      (MeasurableSet.pi Set.countable_univ (fun _ _ => measurableSet_Ioc)) (fun x hx => ?_)
    have hx' : ∀ i, x i ∈ Set.Ioc (-(1 / 2 : ℝ)) (1 / 2) := fun i =>
      Set.mem_pi.mp hx i (Set.mem_univ i)
    rw [perC_eq_self_of_mem_halfCube hsupp hx']
  -- (c) the fundamental-domain change of variables
  have hc := integral_unitCube_eq_centreCube_real (fun z => ‖perC F z‖ ^ 2)
    (periodic1_norm_sq hper)
  rw [← ha, hb, ← hc]

/-- The partial derivative kills an additive constant. -/
lemma cm_pd_add_const {ι : Type*} [Fintype ι] [DecidableEq ι] (i : ι)
    (g : (ι → ℝ) → ℂ) (c : ℂ) :
    Work.Diff.STE.pd i (fun z => g z + c) = Work.Diff.STE.pd i g := by
  funext x
  simp only [Work.Diff.STE.pd, fderiv_add_const]

/-- The iterated partial derivative kills an additive constant, on nonempty lists of directions. -/
lemma cm_pdList_add_const {ι : Type*} [Fintype ι] [DecidableEq ι] :
    ∀ (l : List ι), l ≠ [] → ∀ (g : (ι → ℝ) → ℂ) (c : ℂ),
      Work.Diff.STE.pdList l (fun z => g z + c) = Work.Diff.STE.pdList l g := by
  intro l
  induction l with
  | nil => intro h; exact absurd rfl h
  | cons i t ih =>
      intro _ g c
      cases t with
      | nil => exact cm_pd_add_const i g c
      | cons j t' =>
          have ih' := ih (List.cons_ne_nil j t') g c
          simpa only [Work.Diff.STE.pdList, List.foldr_cons] using
            congrArg (fun h => Work.Diff.STE.pd i h) ih'

/-- The iterated partial derivative (of order `m ≥ 1`) kills an additive constant. -/
lemma cm_pdVec_add_const {ι : Type*} [Fintype ι] [DecidableEq ι] {m : ℕ} (hm : 1 ≤ m)
    (l : Fin m → ι) (g : (ι → ℝ) → ℂ) (c : ℂ) :
    Work.Diff.STE.pdVec m l (fun z => g z + c) = Work.Diff.STE.pdVec m l g := by
  have hl : List.ofFn l ≠ [] := by
    intro h
    have hlen := congrArg List.length h
    simp [List.length_ofFn] at hlen
    omega
  simpa only [Work.Diff.STE.pdVec] using cm_pdList_add_const (List.ofFn l) hl g c

/-! ## The derivative of a periodisation -/

/-- On the unit cube, the `m`-th iterated partial derivative of the periodisation of a
ball-supported smooth function is the periodisation of the iterated partial derivative. -/
lemma pdVec_perC_eq_perC_pdVec_on_cube {n m : ℕ} {f : (Fin n → ℝ) → ℂ}
    (hf : ContDiff ℝ (⊤ : ℕ∞) f)
    (hsupp : Function.support f ⊆ Metric.ball (0 : Fin n → ℝ) (1 / 2)) (β : Fin m → Fin n) :
    ∀ x ∈ Work.Diff.STE.unitCube (ι := Fin n),
      Work.Diff.STE.pdVec m β (perC f) x = perC (Work.Diff.STE.pdVec m β f) x := by
  have hcube : Function.support f ⊆
      Set.pi Set.univ (fun _ : Fin n => Set.Ioo (-(1 / 2 : ℝ)) (1 / 2)) :=
    support_subset_openCube hsupp
  have hcube' : Function.support (Work.Diff.STE.pdVec m β f) ⊆
      Set.pi Set.univ (fun _ : Fin n => Set.Ioo (-(1 / 2 : ℝ)) (1 / 2)) :=
    support_subset_openCube (support_pdVec_subset_ball hf hsupp)
  intro x hx
  have hz : ∀ i : Fin n, x i ∈ Set.Ioo (-(1 / 4 : ℝ)) (5 / 4) := by
    intro i
    have hxi : x i ∈ Set.Ioc (0 : ℝ) 1 := by
      have := Set.mem_pi.mp hx i (Set.mem_univ i)
      simpa only [Work.Diff.STE.unitCube, Set.mem_Ioc] using this
    exact ⟨by linarith [(Set.mem_Ioc.mp hxi).1], by linarith [(Set.mem_Ioc.mp hxi).2]⟩
  have h1 : Work.Diff.STE.pdVec m β (perC f) x
      = ∑ n ∈ Work.Diff.STE.csqp_boxIdx (Fin n),
          Work.Diff.STE.pdVec m β f (x + Work.Diff.STE.iVec n) :=
    Work.Diff.STE.B3.steB3_pdVec_periodization_eq_sum hf hcube m β x hx
  have h2 : perC (Work.Diff.STE.pdVec m β f) x
      = ∑ n ∈ Work.Diff.STE.csqp_boxIdx (Fin n),
          Work.Diff.STE.pdVec m β f (x + Work.Diff.STE.iVec n) :=
    Work.Diff.STE.csqp_periodization_eq_sum_boxIdx hcube' hz
  rw [h1, h2]

/-- The norm of a real number embedded into the complex numbers. -/
lemma cm_norm_ofReal (x : ℝ) : ‖((x : ℝ) : ℂ)‖ = ‖x‖ := by simp

/-! ## Transfer lemmas -/

/-- The sup bound for the periodised field `perC M + c`. -/
lemma norm_perMat_le {n : ℕ} {M : (Fin n → ℝ) → Fin n → Fin n → ℂ}
    {c : Fin n → Fin n → ℂ} {B : ℝ} (p q : Fin n)
    (hMsupp : Function.support (fun z : Fin n → ℝ => M z p q) ⊆ Metric.ball 0 (1 / 2))
    (hMb : ∀ z : Fin n → ℝ, ‖M z p q + c p q‖ ≤ B) :
    ∀ z : Fin n → ℝ, ‖perC (fun y : Fin n → ℝ => M y p q) z + c p q‖ ≤ B := by
  intro z
  obtain ⟨m, hm⟩ := exists_intVec_add_mem_halfCube z
  have hper : Work.Diff.STE.Periodic1 (perC (fun y : Fin n → ℝ => M y p q)) := perC_periodic _
  have h1 : perC (fun y : Fin n → ℝ => M y p q) z
      = perC (fun y : Fin n → ℝ => M y p q) ((fun j => (m j : ℝ)) + z) :=
    (Work.Diff.STE.B3.Periodic1.add_intVec hper m z).symm
  rw [h1, perC_eq_self_of_mem_halfCube hMsupp hm]
  exact hMb _

/-- The `L²` norm, over the unit cube, of one jet of the periodised field equals the whole-space
`L²` norm of the corresponding jet of the original field. -/
lemma integral_cube_pdVec_perMat_eq {n m : ℕ} (hm : 1 ≤ m)
    {M : (Fin n → ℝ) → Fin n → Fin n → ℂ} {c : Fin n → Fin n → ℂ}
    (hMsm : ∀ i j : Fin n, ContDiff ℝ (⊤ : ℕ∞) (fun z : Fin n → ℝ => M z i j))
    (hMsupp : ∀ i j : Fin n, Function.support (fun z : Fin n → ℝ => M z i j)
      ⊆ Metric.ball (0 : Fin n → ℝ) (1 / 2))
    (p q : Fin n) (γ : Fin m → Fin n) :
    (∫ x in Work.Diff.STE.unitCube (ι := Fin n),
        ‖Work.Diff.STE.pdVec m γ
          (fun z : Fin n → ℝ => perC (fun y : Fin n → ℝ => M y p q) z + c p q) x‖ ^ 2)
      = ∫ x : Fin n → ℝ, ‖Work.Diff.STE.pdVec m γ (fun y : Fin n → ℝ => M y p q) x‖ ^ 2 := by
  have hkey : (∫ x in Work.Diff.STE.unitCube (ι := Fin n),
        ‖Work.Diff.STE.pdVec m γ
          (fun z : Fin n → ℝ => perC (fun y : Fin n → ℝ => M y p q) z + c p q) x‖ ^ 2)
      = ∫ x in Work.Diff.STE.unitCube (ι := Fin n),
          ‖perC (Work.Diff.STE.pdVec m γ (fun y : Fin n → ℝ => M y p q)) x‖ ^ 2 := by
    refine setIntegral_congr_fun measSet_unitCube (fun x hx => ?_)
    rw [cm_pdVec_add_const hm γ _ _,
      pdVec_perC_eq_perC_pdVec_on_cube (hMsm p q) (hMsupp p q) γ x hx]
  rw [hkey]
  exact (integral_normSq_eq_integral_cube_perC
    (Work.Diff.STE.csqp_contDiff_pdList_top (List.ofFn γ) (hMsm p q))
    (support_pdVec_subset_ball (hMsm p q) (hMsupp p q))).symm

/-- A single jet of the original field is bounded by the full `Hᵐ` energy of the periodised field. -/
lemma integral_pdVec_le_ENormSq_perMat {n m : ℕ} (hm : 1 ≤ m)
    {M : (Fin n → ℝ) → Fin n → Fin n → ℂ} {c : Fin n → Fin n → ℂ}
    (hMsm : ∀ i j : Fin n, ContDiff ℝ (⊤ : ℕ∞) (fun z : Fin n → ℝ => M z i j))
    (hMsupp : ∀ i j : Fin n, Function.support (fun z : Fin n → ℝ => M z i j)
      ⊆ Metric.ball (0 : Fin n → ℝ) (1 / 2))
    (p q : Fin n) (β : Fin m → Fin n) :
    (∫ x : Fin n → ℝ, ‖Work.Diff.STE.pdVec m β (fun y : Fin n → ℝ => M y p q) x‖ ^ 2)
      ≤ Work.Diff.STE.ENormSq m
          (fun z : Fin n → ℝ => perC (fun y : Fin n → ℝ => M y p q) z + c p q) := by
  rw [Work.Diff.STE.ENormSq]
  refine le_trans (le_of_eq ?_) (Finset.single_le_sum
    (f := fun γ : Fin m → Fin n =>
      ∫ x in Work.Diff.STE.unitCube (ι := Fin n),
        ‖Work.Diff.STE.pdVec m γ
          (fun z : Fin n → ℝ => perC (fun y : Fin n → ℝ => M y p q) z + c p q) x‖ ^ 2)
    (fun γ _ => integral_nonneg (fun x => by positivity)) (Finset.mem_univ β))
  exact (integral_cube_pdVec_perMat_eq hm hMsm hMsupp p q β).symm

/-- The full `Hᵐ` energy of the periodised field, expanded in the jets of the original field. -/
lemma ENormSq_perMat_eq {n m : ℕ} (hm : 1 ≤ m)
    {M : (Fin n → ℝ) → Fin n → Fin n → ℂ} {c : Fin n → Fin n → ℂ}
    (hMsm : ∀ i j : Fin n, ContDiff ℝ (⊤ : ℕ∞) (fun z : Fin n → ℝ => M z i j))
    (hMsupp : ∀ i j : Fin n, Function.support (fun z : Fin n → ℝ => M z i j)
      ⊆ Metric.ball (0 : Fin n → ℝ) (1 / 2))
    (p q : Fin n) :
    Work.Diff.STE.ENormSq m (fun z : Fin n → ℝ => perC (fun y : Fin n → ℝ => M y p q) z + c p q)
      = ∑ γ : Fin m → Fin n,
          ∫ x : Fin n → ℝ, ‖Work.Diff.STE.pdVec m γ (fun y : Fin n → ℝ => M y p q) x‖ ^ 2 := by
  rw [Work.Diff.STE.ENormSq]
  exact Finset.sum_congr rfl (fun γ _ => integral_cube_pdVec_perMat_eq hm hMsm hMsupp p q γ)

/-- If two matrix fields agree, on the open cube, with two real fields whose product is the
identity, then the pointwise product of their periodisations, evaluated at an arbitrary point, is
the identity. -/
lemma perMat_mul_eq_one {n : ℕ}
    {G H : (Fin n → ℝ) → Fin n → Fin n → ℝ}
    {Pmat Qmat : (Fin n → ℝ) → Fin n → Fin n → ℂ}
    (hPper : ∀ p q : Fin n, Work.Diff.STE.Periodic1 (fun x : Fin n → ℝ => Pmat x p q))
    (hQper : ∀ p q : Fin n, Work.Diff.STE.Periodic1 (fun x : Fin n → ℝ => Qmat x p q))
    (hPsm : ∀ p q : Fin n, ContDiff ℝ (⊤ : ℕ∞) (fun x : Fin n → ℝ => Pmat x p q))
    (hQsm : ∀ p q : Fin n, ContDiff ℝ (⊤ : ℕ∞) (fun x : Fin n → ℝ => Qmat x p q))
    (hPopen : ∀ z : Fin n → ℝ, (∀ i, z i ∈ Set.Ioo (-(1 / 2 : ℝ)) (1 / 2)) →
      ∀ p q : Fin n, Pmat z p q = ((G z p q : ℝ) : ℂ))
    (hQopen : ∀ z : Fin n → ℝ, (∀ i, z i ∈ Set.Ioo (-(1 / 2 : ℝ)) (1 / 2)) →
      ∀ p q : Fin n, Qmat z p q = ((H z p q : ℝ) : ℂ))
    (hGH : ∀ z : Fin n → ℝ, Matrix.of (G z) * Matrix.of (H z) = 1) :
    ∀ z : Fin n → ℝ, Matrix.of (Pmat z) * Matrix.of (Qmat z) = 1 := by
  intro z
  ext p q
  have hper1 : Work.Diff.STE.Periodic1
      (fun w : Fin n → ℝ => (Matrix.of (Pmat w) * Matrix.of (Qmat w)) p q) := by
    intro i x
    show (Matrix.of (Pmat (x + Pi.single i 1)) * Matrix.of (Qmat (x + Pi.single i 1))) p q
        = (Matrix.of (Pmat x) * Matrix.of (Qmat x)) p q
    simp only [Matrix.mul_apply, Matrix.of_apply]
    exact Finset.sum_congr rfl (fun k _ => by
      have h1 : Pmat (x + Pi.single i 1) p k = Pmat x p k := hPper p k i x
      have h2 : Qmat (x + Pi.single i 1) k q = Qmat x k q := hQper k q i x
      rw [h1, h2])
  have hper2 : Work.Diff.STE.Periodic1
      (fun _ : Fin n → ℝ => (1 : Matrix (Fin n) (Fin n) ℂ) p q) := fun i x => rfl
  have hcont1 : Continuous
      (fun w : Fin n → ℝ => (Matrix.of (Pmat w) * Matrix.of (Qmat w)) p q) := by
    simp only [Matrix.mul_apply, Matrix.of_apply]
    exact continuous_finsetSum _ (fun k _ => ((hPsm p k).continuous).mul ((hQsm k q).continuous))
  have hcont2 : Continuous (fun _ : Fin n → ℝ => (1 : Matrix (Fin n) (Fin n) ℂ) p q) :=
    continuous_const
  have heq := Work.Diff.STE.Lead.GalTame.periodic_eq_of_eqOn_openCube hper1 hper2 hcont1 hcont2
    (fun w hw => ?_)
  · exact congrFun heq z
  · have hPw : ∀ a b : Fin n, Pmat w a b = ((G w a b : ℝ) : ℂ) := hPopen w hw
    have hQw : ∀ a b : Fin n, Qmat w a b = ((H w a b : ℝ) : ℂ) := hQopen w hw
    simp only [Matrix.mul_apply, Matrix.of_apply]
    calc ∑ k : Fin n, Pmat w p k * Qmat w k q
        = ((∑ k : Fin n, G w p k * H w k q : ℝ) : ℂ) := by
          rw [Complex.ofReal_sum]
          exact Finset.sum_congr rfl (fun k _ => by rw [hPw p k, hQw k q, Complex.ofReal_mul])
      _ = ((Matrix.of (G w) * Matrix.of (H w)) p q : ℝ) := by
          simp only [Matrix.mul_apply, Matrix.of_apply]
      _ = ((1 : Matrix (Fin n) (Fin n) ℝ) p q : ℝ) := by rw [hGH w]
      _ = (1 : Matrix (Fin n) (Fin n) ℂ) p q := by
          rw [Matrix.one_apply, Matrix.one_apply]
          by_cases hpq : p = q <;> simp [hpq]

/-- **Moser-type tame estimate for the inverse of a compactly supported matrix field, with
whole-space (`∫_{ℝⁿ}`) `L²` energies.**

Let `G` and `H` be smooth `n × n` matrix fields on `ℝⁿ` which are compactly supported perturbations
of the identity matrix (the support of `G - 1` and of `H - 1` is contained in the open ball of
radius `1/2`), uniformly bounded by `U`, `W`, and satisfy `G · H = 1` pointwise.  Then for every
`m ≥ 1` the whole-space `L²` energy of the top jet of any entry of `H` is bounded by a constant
(depending only on `n`, `m`, `U`, `W` and the Gagliardo–Nirenberg constant `K`) times `1` plus the
corresponding top-order energy of `G`:
`∫_{ℝⁿ} ‖∂^m_β H_{ij}‖² ≤ C (1 + Σ_{pq} Σ_γ ∫_{ℝⁿ} ‖∂^m_γ G_{pq}‖²)`.

This is the whole-space form of the Moser estimate
`Work.Diff.STE.B3.ENormSq_mat_inv_le` (`Submission/Work/Diff/STE/B3/ENormSq_mat_inv_le.lean`,
**proved, sorry-free**), which is stated on the torus: for smooth `1`-periodic `P, Q` with
`P · Q = 1`, sup bounds `U`, `W` and the Gagliardo–Nirenberg hypothesis `hGN`, it gives
`ENormSqMat m Q ≤ C (1 + ENormSqMat m P)` where `ENormSqMat m M = Σ_{ij} ENormSq m (M · i j)`.
(The Gagliardo–Nirenberg hypothesis is
`∃ K ≥ 0, ∀ U' f, ContDiff … f → Periodic1 f → (∀ x, ‖f x‖ ≤ U') → HasGNBound m U' K f`, with
`Work.Diff.STE.B3.HasGNBound` from `Submission/Work/Diff/STE/B3/tame_defs.lean`; it can be supplied
by `Work.Diff.STE.Lead.GalTame.gnTorusSharp` (module in flight) or by the statement of
`Work.Diff.STE.GNclean.gnTorus`.)

PROOF ROUTE (short; nothing but bookkeeping).  Periodise: since `G - 1` and `H - 1` are supported in
the open ball of radius `1/2` (hence strictly inside the half-open fundamental cube
`(-1/2, 1/2]^n`), the functions `P := 1 + per(G - 1)` and `Q := 1 + per(H - 1)` are smooth
`1`-periodic (`Submission/Work/Diff/STE/periodization_contDiff_periodic.lean`), agree with `G`, `H`
on the half-open cube (`Work.Diff.STE.Lead.Gal.per_eq_self_of_mem_halfCube`,
`Submission/Work/Diff/STE/Lead/Gal/PerKit.lean`, and its support hypothesis `‖y‖ < 1/2` must be
weakened to `‖y‖ ≤ 1/2`, using the *open* ball), hence `P · Q = 1` everywhere (both sides are
periodic and agree on the half-open cube), with sup bounds `max U 1`, `max W 1`, so
`ENormSq_mat_inv_le` applies.  Then transfer the conclusion to the whole-space integrals: for a
smooth `f` supported in the open ball of radius `1/2`, the `m`-th jet of its periodisation is the
periodisation of the `m`-th jet of `f` (`Submission/Work/Diff/STE/pd_periodization.lean`), so
`ENormSq m (per f) = ∫_{ℝⁿ} ‖∂^m f‖²` by disjointness of the translates of the (small) support; the
integral over `unitCube = (0,1]^n` may be replaced by the integral over the half-open centred cube
since both are fundamental domains for the periodic integrand.  Finally
`ENormSq 0 (pdVec m β Q_{ij}) ≤ ENormSq m (Q_{ij})` is
`Work.Diff.STE.B3.ENormSq_zero_pdVec_le` (`Submission/Work/Diff/STE/B3/tmA_ENormSq_le.lean`, proved
above its `sorry`ed target) or the one-line `Finset.single_le_sum` argument.  Note that for `m ≥ 1`
all the whole-space integrals are of compactly supported functions, so no integrability issue
arises; formally, `∫` of a non-integrable function is `0` in Mathlib, so the statement is also
formally true for `m = 0`, but it is only *used* with `m ≥ 1`. -/
theorem invEnergyWhole {n : ℕ} (m : ℕ) (hm : 1 ≤ m)
    (hGN : ∃ K : ℝ, 0 ≤ K ∧ ∀ (U' : ℝ) (f : (Fin n → ℝ) → ℂ),
      ContDiff ℝ ((⊤ : ENat) : WithTop ENat) f → Work.Diff.STE.Periodic1 f →
      (∀ x : Fin n → ℝ, ‖f x‖ ≤ U') →
      Work.Diff.STE.B3.HasGNBound m U' K f)
    (U W : ℝ) (hU : 0 ≤ U) (hW : 0 ≤ W) :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ (G H : (Fin n → ℝ) → Fin n → Fin n → ℝ),
        (∀ i j : Fin n, ContDiff ℝ ((⊤ : ENat) : WithTop ENat) (fun z : Fin n → ℝ => G z i j)) →
        (∀ i j : Fin n, ContDiff ℝ ((⊤ : ENat) : WithTop ENat) (fun z : Fin n → ℝ => H z i j)) →
        (∀ i j : Fin n, Function.support (fun z : Fin n → ℝ =>
          G z i j - (if i = j then (1 : ℝ) else 0)) ⊆ Metric.ball 0 (1 / 2)) →
        (∀ i j : Fin n, Function.support (fun z : Fin n → ℝ =>
          H z i j - (if i = j then (1 : ℝ) else 0)) ⊆ Metric.ball 0 (1 / 2)) →
        (∀ (z : Fin n → ℝ) (i j : Fin n), ‖G z i j‖ ≤ U) →
        (∀ (z : Fin n → ℝ) (i j : Fin n), ‖H z i j‖ ≤ W) →
        (∀ z : Fin n → ℝ, Matrix.of (G z) * Matrix.of (H z) = 1) →
        ∀ (β : Fin m → Fin n) (i j : Fin n),
          ∫ z : Fin n → ℝ,
              ‖Work.Diff.STE.pdVec m β (fun y : Fin n → ℝ => ((H y i j : ℝ) : ℂ)) z‖ ^ 2
            ≤ C * (1 + ∑ p : Fin n, ∑ q : Fin n, ∑ γ : Fin m → Fin n,
                ∫ z : Fin n → ℝ,
                  ‖Work.Diff.STE.pdVec m γ (fun y : Fin n → ℝ => ((G y p q : ℝ) : ℂ)) z‖ ^ 2) := by  classical
  obtain ⟨C₀, hC₀, hmos⟩ := Work.Diff.STE.B3.ENormSq_mat_inv_le (ι := Fin n) n m
    (max U 1) (max W 1) (le_trans hU (le_max_left _ _)) (le_trans hW (le_max_left _ _)) hGN
  refine ⟨max C₀ 1, le_trans zero_le_one (le_max_right _ _), ?_⟩
  intro G H hGsm hHsm hGsupp hHsupp hGb hHb hGH β i j
  -- the two residual matrix fields
  set gR : (Fin n → ℝ) → Fin n → Fin n → ℂ :=
    fun z p q => ((G z p q - kd p q : ℝ) : ℂ) with hgR
  set hR : (Fin n → ℝ) → Fin n → Fin n → ℂ :=
    fun z p q => ((H z p q - kd p q : ℝ) : ℂ) with hhR
  have hgRsm : ∀ p q : Fin n, ContDiff ℝ (⊤ : ℕ∞) (fun z : Fin n → ℝ => gR z p q) := by
    intro p q
    have h1 : ContDiff ℝ (⊤ : ℕ∞) (fun z : Fin n → ℝ => G z p q - kd p q) :=
      (hGsm p q).sub contDiff_const
    have h2 : ContDiff ℝ (⊤ : ℕ∞) (fun z : Fin n → ℝ => ((G z p q - kd p q : ℝ) : ℂ)) :=
      Complex.ofRealCLM.contDiff.comp h1
    simpa only [hgR] using h2
  have hhRsm : ∀ p q : Fin n, ContDiff ℝ (⊤ : ℕ∞) (fun z : Fin n → ℝ => hR z p q) := by
    intro p q
    have h1 : ContDiff ℝ (⊤ : ℕ∞) (fun z : Fin n → ℝ => H z p q - kd p q) :=
      (hHsm p q).sub contDiff_const
    have h2 : ContDiff ℝ (⊤ : ℕ∞) (fun z : Fin n → ℝ => ((H z p q - kd p q : ℝ) : ℂ)) :=
      Complex.ofRealCLM.contDiff.comp h1
    simpa only [hhR] using h2
  have hgRsupp : ∀ p q : Fin n, Function.support (fun z : Fin n → ℝ => gR z p q)
      ⊆ Metric.ball (0 : Fin n → ℝ) (1 / 2) := by
    intro p q
    have h1 : Function.support (fun z : Fin n → ℝ => ((G z p q - kd p q : ℝ) : ℂ))
        ⊆ Metric.ball (0 : Fin n → ℝ) (1 / 2) := by
      rw [support_ofReal_comp]
      exact hGsupp p q
    simpa [hgR] using h1
  have hhRsupp : ∀ p q : Fin n, Function.support (fun z : Fin n → ℝ => hR z p q)
      ⊆ Metric.ball (0 : Fin n → ℝ) (1 / 2) := by
    intro p q
    have h1 : Function.support (fun z : Fin n → ℝ => ((H z p q - kd p q : ℝ) : ℂ))
        ⊆ Metric.ball (0 : Fin n → ℝ) (1 / 2) := by
      rw [support_ofReal_comp]
      exact hHsupp p q
    simpa [hhR] using h1
  have hgRb : ∀ (z : Fin n → ℝ) (p q : Fin n),
      ‖gR z p q + ((kd p q : ℝ) : ℂ)‖ ≤ max U 1 := by
    intro z p q
    have h1 : gR z p q + ((kd p q : ℝ) : ℂ) = ((G z p q : ℝ) : ℂ) := by
      simp only [hgR]
      push_cast
      ring
    rw [h1, cm_norm_ofReal]
    exact le_trans (hGb z p q) (le_max_left U 1)
  have hhRb : ∀ (z : Fin n → ℝ) (p q : Fin n),
      ‖hR z p q + ((kd p q : ℝ) : ℂ)‖ ≤ max W 1 := by
    intro z p q
    have h1 : hR z p q + ((kd p q : ℝ) : ℂ) = ((H z p q : ℝ) : ℂ) := by
      simp only [hhR]
      push_cast
      ring
    rw [h1, cm_norm_ofReal]
    exact le_trans (hHb z p q) (le_max_left W 1)
  -- the two periodic matrix fields
  set Pmat : (Fin n → ℝ) → Fin n → Fin n → ℂ :=
    fun z p q => perC (fun y : Fin n → ℝ => gR y p q) z + ((kd p q : ℝ) : ℂ) with hPmat
  set Qmat : (Fin n → ℝ) → Fin n → Fin n → ℂ :=
    fun z p q => perC (fun y : Fin n → ℝ => hR y p q) z + ((kd p q : ℝ) : ℂ) with hQmat
  have hPsm : ∀ p q : Fin n, ContDiff ℝ (⊤ : ℕ∞) (fun x : Fin n → ℝ => Pmat x p q) := by
    intro p q
    have h1 : ContDiff ℝ (⊤ : ℕ∞)
        (fun x : Fin n → ℝ => perC (fun y : Fin n → ℝ => gR y p q) x + ((kd p q : ℝ) : ℂ)) :=
      (Work.Diff.STE.csqp_periodization_contDiff (hgRsm p q)
        (support_subset_openCube (hgRsupp p q))).add contDiff_const
    simpa [hPmat] using h1
  have hQsm : ∀ p q : Fin n, ContDiff ℝ (⊤ : ℕ∞) (fun x : Fin n → ℝ => Qmat x p q) := by
    intro p q
    have h1 : ContDiff ℝ (⊤ : ℕ∞)
        (fun x : Fin n → ℝ => perC (fun y : Fin n → ℝ => hR y p q) x + ((kd p q : ℝ) : ℂ)) :=
      (Work.Diff.STE.csqp_periodization_contDiff (hhRsm p q)
        (support_subset_openCube (hhRsupp p q))).add contDiff_const
    simpa [hQmat] using h1
  have hPper : ∀ p q : Fin n, Work.Diff.STE.Periodic1 (fun x : Fin n → ℝ => Pmat x p q) := by
    intro p q
    have h1 := periodic1_add_const ((kd p q : ℝ) : ℂ)
      (perC_periodic (fun y : Fin n → ℝ => gR y p q))
    simpa [hPmat] using h1
  have hQper : ∀ p q : Fin n, Work.Diff.STE.Periodic1 (fun x : Fin n → ℝ => Qmat x p q) := by
    intro p q
    have h1 := periodic1_add_const ((kd p q : ℝ) : ℂ)
      (perC_periodic (fun y : Fin n → ℝ => hR y p q))
    simpa [hQmat] using h1
  have hPb : ∀ (x : Fin n → ℝ) (p q : Fin n), ‖Pmat x p q‖ ≤ max U 1 := by
    intro x p q
    have h1 := norm_perMat_le (M := gR) (c := fun p q => ((kd p q : ℝ) : ℂ)) (B := max U 1)
      p q (hgRsupp p q) (fun z => hgRb z p q) x
    simpa [hPmat] using h1
  have hQb : ∀ (x : Fin n → ℝ) (p q : Fin n), ‖Qmat x p q‖ ≤ max W 1 := by
    intro x p q
    have h1 := norm_perMat_le (M := hR) (c := fun p q => ((kd p q : ℝ) : ℂ)) (B := max W 1)
      p q (hhRsupp p q) (fun z => hhRb z p q) x
    simpa [hQmat] using h1
  have hPQ : ∀ z : Fin n → ℝ, Matrix.of (Pmat z) * Matrix.of (Qmat z) = 1 :=
    perMat_mul_eq_one hPper hQper hPsm hQsm
      (fun z hz p q => by
        have h1 : perC (fun y : Fin n → ℝ => gR y p q) z = gR z p q :=
          perC_eq_self_of_mem_halfCube (hgRsupp p q)
            (fun i => ⟨by linarith [(hz i).1], by linarith [(hz i).2]⟩)
        have h2 : perC (fun y : Fin n → ℝ => gR y p q) z + ((kd p q : ℝ) : ℂ)
            = ((G z p q : ℝ) : ℂ) := by
          rw [h1]
          simp only [hgR]
          push_cast
          ring
        simpa [hPmat] using h2)
      (fun z hz p q => by
        have h1 : perC (fun y : Fin n → ℝ => hR y p q) z = hR z p q :=
          perC_eq_self_of_mem_halfCube (hhRsupp p q)
            (fun i => ⟨by linarith [(hz i).1], by linarith [(hz i).2]⟩)
        have h2 : perC (fun y : Fin n → ℝ => hR y p q) z + ((kd p q : ℝ) : ℂ)
            = ((H z p q : ℝ) : ℂ) := by
          rw [h1]
          simp only [hhR]
          push_cast
          ring
        simpa [hQmat] using h2)
      hGH
  have hmos' := hmos Pmat Qmat hPsm hQsm hPper hQper hPb hQb hPQ
  -- bridges between the target's own fields and the residual fields
  have hbridgeH : ∀ (p q : Fin n) (γ : Fin m → Fin n),
      Work.Diff.STE.pdVec m γ (fun y : Fin n → ℝ => ((H y p q : ℝ) : ℂ))
        = Work.Diff.STE.pdVec m γ (fun y : Fin n → ℝ => hR y p q) := by
    intro p q γ
    have h2 : (fun y : Fin n → ℝ => hR y p q)
        = (fun y : Fin n → ℝ => ((H y p q : ℝ) : ℂ) + (-(((kd p q : ℝ)) : ℂ))) := by
      funext y
      simp only [hhR]
      push_cast
      ring
    rw [h2, cm_pdVec_add_const hm γ _ _]
  have hbridgeG : ∀ (p q : Fin n) (γ : Fin m → Fin n),
      Work.Diff.STE.pdVec m γ (fun y : Fin n → ℝ => ((G y p q : ℝ) : ℂ))
        = Work.Diff.STE.pdVec m γ (fun y : Fin n → ℝ => gR y p q) := by
    intro p q γ
    have h2 : (fun y : Fin n → ℝ => gR y p q)
        = (fun y : Fin n → ℝ => ((G y p q : ℝ) : ℂ) + (-(((kd p q : ℝ)) : ℂ))) := by
      funext y
      simp only [hgR]
      push_cast
      ring
    rw [h2, cm_pdVec_add_const hm γ _ _]
  -- the left hand side
  have hLHS1 : (∫ z : Fin n → ℝ,
        ‖Work.Diff.STE.pdVec m β (fun y : Fin n → ℝ => ((H y i j : ℝ) : ℂ)) z‖ ^ 2)
      = ∫ z : Fin n → ℝ,
        ‖Work.Diff.STE.pdVec m β (fun y : Fin n → ℝ => hR y i j) z‖ ^ 2 := by
    refine integral_congr_ae (Filter.Eventually.of_forall (fun z => ?_))
    rw [hbridgeH i j β]
  have hLHS2 : (∫ z : Fin n → ℝ,
        ‖Work.Diff.STE.pdVec m β (fun y : Fin n → ℝ => hR y i j) z‖ ^ 2)
      ≤ Work.Diff.STE.ENormSq m (fun z : Fin n → ℝ => Qmat z i j) := by
    have h1 := integral_pdVec_le_ENormSq_perMat (M := hR) (c := fun p q => ((kd p q : ℝ) : ℂ))
      hm hhRsm hhRsupp i j β
    simpa [hQmat] using h1
  have hQle : Work.Diff.STE.ENormSq m (fun z : Fin n → ℝ => Qmat z i j)
      ≤ Work.Diff.STE.B3.ENormSqMat m Qmat := by
    simp only [Work.Diff.STE.B3.ENormSqMat]
    have h2 : Work.Diff.STE.ENormSq m (fun z : Fin n → ℝ => Qmat z i j)
        ≤ ∑ q : Fin n, Work.Diff.STE.ENormSq m (fun z : Fin n → ℝ => Qmat z i q) :=
      Finset.single_le_sum
        (f := fun q : Fin n => Work.Diff.STE.ENormSq m (fun z : Fin n → ℝ => Qmat z i q))
        (fun q _ => ENormSq_nonneg m _) (Finset.mem_univ j)
    have h3 : (∑ q : Fin n, Work.Diff.STE.ENormSq m (fun z : Fin n → ℝ => Qmat z i q))
        ≤ ∑ p : Fin n, ∑ q : Fin n,
            Work.Diff.STE.ENormSq m (fun z : Fin n → ℝ => Qmat z p q) :=
      Finset.single_le_sum
        (f := fun p : Fin n => ∑ q : Fin n,
          Work.Diff.STE.ENormSq m (fun z : Fin n → ℝ => Qmat z p q))
        (fun p _ => Finset.sum_nonneg (fun q _ => ENormSq_nonneg m _)) (Finset.mem_univ i)
    exact le_trans h2 h3
  have hENP : Work.Diff.STE.B3.ENormSqMat m Pmat
      = ∑ p : Fin n, ∑ q : Fin n, ∑ γ : Fin m → Fin n,
          ∫ z : Fin n → ℝ,
            ‖Work.Diff.STE.pdVec m γ (fun y : Fin n → ℝ => ((G y p q : ℝ) : ℂ)) z‖ ^ 2 := by
    simp only [Work.Diff.STE.B3.ENormSqMat]
    refine Finset.sum_congr rfl (fun p _ => Finset.sum_congr rfl (fun q _ => ?_))
    rw [ENormSq_perMat_eq (M := gR) (c := fun p q => ((kd p q : ℝ) : ℂ)) hm hgRsm hgRsupp p q]
    exact Finset.sum_congr rfl (fun γ _ => by rw [← hbridgeG p q γ])
  have hRHSnn : 0 ≤ ∑ p : Fin n, ∑ q : Fin n, ∑ γ : Fin m → Fin n,
      ∫ z : Fin n → ℝ,
        ‖Work.Diff.STE.pdVec m γ (fun y : Fin n → ℝ => ((G y p q : ℝ) : ℂ)) z‖ ^ 2 := by
    apply Finset.sum_nonneg
    intro p _
    apply Finset.sum_nonneg
    intro q _
    apply Finset.sum_nonneg
    intro γ _
    exact integral_nonneg (fun x => by positivity)
  calc (∫ z : Fin n → ℝ,
        ‖Work.Diff.STE.pdVec m β (fun y : Fin n → ℝ => ((H y i j : ℝ) : ℂ)) z‖ ^ 2)
      = ∫ z : Fin n → ℝ,
        ‖Work.Diff.STE.pdVec m β (fun y : Fin n → ℝ => hR y i j) z‖ ^ 2 := hLHS1
    _ ≤ Work.Diff.STE.ENormSq m (fun z : Fin n → ℝ => Qmat z i j) := hLHS2
    _ ≤ Work.Diff.STE.B3.ENormSqMat m Qmat := hQle
    _ ≤ C₀ * (1 + Work.Diff.STE.B3.ENormSqMat m Pmat) := hmos'
    _ = C₀ * (1 + ∑ p : Fin n, ∑ q : Fin n, ∑ γ : Fin m → Fin n,
          ∫ z : Fin n → ℝ,
            ‖Work.Diff.STE.pdVec m γ (fun y : Fin n → ℝ => ((G y p q : ℝ) : ℂ)) z‖ ^ 2) := by
        rw [hENP]
    _ ≤ max C₀ 1 * (1 + ∑ p : Fin n, ∑ q : Fin n, ∑ γ : Fin m → Fin n,
          ∫ z : Fin n → ℝ,
            ‖Work.Diff.STE.pdVec m γ (fun y : Fin n → ℝ => ((G y p q : ℝ) : ℂ)) z‖ ^ 2) := by
        refine mul_le_mul_of_nonneg_right (le_max_left C₀ 1) ?_
        linarith [hRHSnn]


end Work.Diff.STE.Lead.GalTame
