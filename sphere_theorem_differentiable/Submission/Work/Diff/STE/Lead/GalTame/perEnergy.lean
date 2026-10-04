import Mathlib
import Submission.Work.Diff.STE.Torus
import Submission.Work.Diff.STE.periodization_contDiff_periodic
import Submission.Work.Diff.STE.B3.CSq_period_le_integral_deriv
import Submission.Work.Diff.STE.Lead.GalTame.periodic_eq_of_eqOn_openCube

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

namespace Work.Diff.STE.Lead.GalTame

open MeasureTheory

/-! ## Elementary helpers around `pdVec` at order `0` -/

private lemma pdVec_zero_apply {ι : Type*} [DecidableEq ι]
    (l : Fin 0 → ι) (g : (ι → ℝ) → ℂ) :
    Work.Diff.STE.pdVec 0 l g = g := by
  simp [Work.Diff.STE.pdVec, Work.Diff.STE.pdList]

private lemma pdList_zero {ι : Type*} [DecidableEq ι] (l : List ι) :
    Work.Diff.STE.pdList l (0 : (ι → ℝ) → ℂ) = 0 := by
  induction l with
  | nil => rfl
  | cons i t ih =>
      change Work.Diff.STE.pd i (Work.Diff.STE.pdList t (0 : (ι → ℝ) → ℂ)) = 0
      rw [ih]
      funext x
      simp [Work.Diff.STE.pd]

/-- `ENormSq 0` is the `L²` norm squared over the unit cube. -/
private lemma ENormSq_zero_eq_integral {ι : Type*} [Fintype ι] [DecidableEq ι]
    (g : (ι → ℝ) → ℂ) :
    Work.Diff.STE.ENormSq 0 g = ∫ x in Work.Diff.STE.unitCube (ι := ι), ‖g x‖ ^ 2 := by
  rw [Work.Diff.STE.ENormSq]
  rw [show (∑ l : Fin 0 → ι, ∫ x in Work.Diff.STE.unitCube (ι := ι),
        ‖Work.Diff.STE.pdVec 0 l g x‖ ^ 2)
      = ∑ _l : Fin 0 → ι, (∫ x in Work.Diff.STE.unitCube (ι := ι), ‖g x‖ ^ 2) from
      Finset.sum_congr rfl (fun l _ => by rw [pdVec_zero_apply l g])]
  rw [Finset.sum_const, Finset.card_univ, Fintype.card_fun, Fintype.card_fin, pow_zero]
  simp

/-- The `Fin 0`-sum of whole-space integrals of the order `0` derivatives collapses. -/
private lemma sum_fin_zero_integral {ι : Type*} [Fintype ι] [DecidableEq ι]
    (g : (ι → ℝ) → ℂ) :
    (∑ l : Fin 0 → ι, ∫ x : ι → ℝ, ‖Work.Diff.STE.pdVec 0 l g x‖ ^ 2)
      = ∫ x : ι → ℝ, ‖g x‖ ^ 2 := by
  rw [show (∑ l : Fin 0 → ι, ∫ x : ι → ℝ, ‖Work.Diff.STE.pdVec 0 l g x‖ ^ 2)
      = ∑ _l : Fin 0 → ι, (∫ x : ι → ℝ, ‖g x‖ ^ 2) from
      Finset.sum_congr rfl (fun l _ => by rw [pdVec_zero_apply l g])]
  rw [Finset.sum_const, Finset.card_univ, Fintype.card_fun, Fintype.card_fin, pow_zero]
  simp

/-! ## Support statements -/

/-- A function whose support lies in the open ball of radius `R ≤ 1/2` is supported in the open
unit cube `(-1/2,1/2)^ι`. -/
private lemma support_subset_openCube {n : ℕ} {f : (Fin n → ℝ) → ℂ} {R : ℝ}
    (hsupp : Function.support f ⊆ Metric.ball (0 : Fin n → ℝ) R) (hR : R ≤ 1 / 2) :
    Function.support f ⊆ Set.pi Set.univ (fun _ : Fin n => Set.Ioo (-(1 / 2 : ℝ)) (1 / 2)) := by
  intro x hx
  have hxb : ‖x‖ < R := by
    have h := hsupp hx
    rwa [Metric.mem_ball, dist_zero_right] at h
  rw [Set.mem_pi]
  intro i _
  have h1 : |x i| ≤ ‖x‖ := by
    have h := norm_le_pi_norm x i
    rwa [Real.norm_eq_abs] at h
  have h2 : |x i| < 1 / 2 := by linarith
  rw [Set.mem_Ioo]
  exact abs_lt.mp h2

/-- Every iterated partial derivative of a smooth function supported in the open ball of radius
`R > 0` vanishes on the closed complement of that ball.  Off the *closed* ball this is clear; on
the sphere it follows from the continuity of the derivative together with the fact that the
exterior of the closed ball is open and dense in the complement of the open ball. -/
private lemma pdVec_eq_zero_of_le_norm {n m : ℕ} {f : (Fin n → ℝ) → ℂ} {R : ℝ}
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
      pdList_zero (List.ofFn β)
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

/-- **The `L²` energy of the periodisation is the full energy of the function.**

Let `f : (Fin n → ℝ) → ℂ` be smooth and supported in the open ball of radius `R ≤ 1/2` about the
origin, and let `per f` be its periodisation, `per f (z) = Σ' k : Fin n → ℤ, f (z + k)`.  Then the
`L²` norm squared of the `m`-th iterated partial derivative `∂^β` of the periodisation over the unit
cube — which is `ENormSq 0 (pdVec m β (per f))` — is bounded by a constant (depending only on `n`)
times the *full* integral of `‖∂^β f‖²` over the ball:

  `ENormSq 0 (pdVec m β (per f)) ≤ C * ∫ z in Metric.ball 0 R, ‖pdVec m β f z‖²`.

In fact the inequality holds with `C = 1` and as an equality.

Route: `per f` is `1`-periodic and agrees with `f` on the open fundamental cube
(`Work.Diff.STE.periodization_contDiff_periodic`), and `per (∂^β f) = ∂^β (per f)`
(the periodisation commutes with the partial derivatives — for this, note that `∂^β f` is again
supported inside the closed ball of radius `R ≤ 1/2` and is smooth, so `per (∂^β f)` is
`1`-periodic and continuous and agrees with `∂^β f` on the open cube, as does `∂^β (per f)`;
apply `periodic_eq_of_eqOn_openCube`; cf. also `B3/CSq_period_le_integral_deriv.lean`).
Then decompose the unit cube into the `2^n` cells indexed by `ε ∈ {0,1}^n` on which the sum
`Σ'_k f (z + k)` has exactly the one non-zero term `k = -ε` (because two distinct lattice points in
the open ball of radius `1/2` are at distance `< 1`), so that the integral over the unit cube is the
integral of `‖∂^β f‖²` over a translate of each cell, and those translates tile the fundamental cube
`(-1/2,1/2]^n`.  Since `∂^β f` is supported in the closed ball of radius `R ≤ 1/2`, contained in the
fundamental cube, the integral over the fundamental cube is `∫_{ℝ^n} ‖∂^β f‖² = ∫_{ball 0 R} ‖∂^β f‖²`.

Alternatively one may use the Fourier side: the Fourier coefficients of a periodisation agree with
those of the original function, and Parseval (`Work.Diff.STE.B3.parseval_cube`) identifies both
integrals with `Σ_k ‖fourierCoeff (∂^β f) k‖²`. -/
theorem perEnergy (n m : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ (f : (Fin n → ℝ) → ℂ) (R : ℝ),
        ContDiff ℝ ((⊤ : ENat) : WithTop ENat) f →
        Function.support f ⊆ Metric.ball (0 : Fin n → ℝ) R →
        R ≤ 1 / 2 →
        ∀ β : Fin m → Fin n,
        Work.Diff.STE.ENormSq 0 (Work.Diff.STE.pdVec m β
            (fun z : Fin n → ℝ => ∑' k : Fin n → ℤ, f (z + Work.Diff.STE.iVec k)))
          ≤ C * ∫ z in Metric.ball (0 : Fin n → ℝ) R, ‖Work.Diff.STE.pdVec m β f z‖ ^ 2 := by
  classical
  refine ⟨((Work.Diff.STE.csqp_boxIdx (Fin n)).card : ℝ) ^ 2, by positivity, ?_⟩
  intro f R hf hsupp hR β
  have hf' : ContDiff ℝ (⊤ : ℕ∞) f := hf
  set F : (Fin n → ℝ) → ℂ := Work.Diff.STE.pdVec m β f with hF
  have hFcd : ContDiff ℝ (⊤ : ℕ∞) F := by
    rw [hF]
    exact Work.Diff.STE.csqp_contDiff_pdList_top (List.ofFn β) hf'
  by_cases hR0 : R ≤ 0
  · -- the ball is empty, hence `f ≡ 0` and both sides vanish
    have hball : Metric.ball (0 : Fin n → ℝ) R = ∅ := Metric.ball_eq_empty.mpr hR0
    have hf0 : ∀ x : Fin n → ℝ, f x = 0 := by
      intro x
      by_contra hx
      have hxs : x ∈ Function.support f := Function.mem_support.mpr hx
      rw [hball] at hsupp
      exact hsupp hxs
    have hP0 : (fun z : Fin n → ℝ => ∑' k : Fin n → ℤ, f (z + Work.Diff.STE.iVec k)) = 0 := by
      funext z
      simp [hf0]
    have hL : Work.Diff.STE.ENormSq 0 (Work.Diff.STE.pdVec m β
        (fun z : Fin n → ℝ => ∑' k : Fin n → ℤ, f (z + Work.Diff.STE.iVec k))) = 0 := by
      rw [ENormSq_zero_eq_integral, hP0]
      have hzz : Work.Diff.STE.pdVec m β (0 : (Fin n → ℝ) → ℂ) = 0 := pdList_zero (List.ofFn β)
      rw [hzz]
      simp
    have hRHS0 : (∫ z in Metric.ball (0 : Fin n → ℝ) R,
        ‖Work.Diff.STE.pdVec m β f z‖ ^ 2) = 0 := by
      rw [hball, setIntegral_empty]
    rw [hL, hRHS0, mul_zero]
  · have hRpos : 0 < R := lt_of_not_ge hR0
    have hsupp_open : Function.support f ⊆
        Set.pi Set.univ (fun _ : Fin n => Set.Ioo (-(1 / 2 : ℝ)) (1 / 2)) :=
      support_subset_openCube hsupp hR
    have hFzero : ∀ x : Fin n → ℝ, R ≤ ‖x‖ → F x = 0 := by
      rw [hF]
      exact pdVec_eq_zero_of_le_norm hf' hsupp hRpos
    have hsuppFball : Function.support F ⊆ Metric.ball (0 : Fin n → ℝ) R := by
      intro x hx
      rw [Metric.mem_ball, dist_zero_right]
      by_contra h
      exact hx (hFzero x (not_lt.mp h))
    have hsuppF_open : Function.support F ⊆
        Set.pi Set.univ (fun _ : Fin n => Set.Ioo (-(1 / 2 : ℝ)) (1 / 2)) :=
      support_subset_openCube hsuppFball hR
    -- the periodisation of `F` is the finite sum over the box of contributing lattice vectors
    have hperF : ∀ x : Fin n → ℝ, (∀ i : Fin n, x i ∈ Set.Ioo (-(1 / 4 : ℝ)) (5 / 4)) →
        (fun z : Fin n → ℝ => ∑' k : Fin n → ℤ, F (z + Work.Diff.STE.iVec k)) x
          = ∑ n ∈ Work.Diff.STE.csqp_boxIdx (Fin n), F (x + Work.Diff.STE.iVec n) := by
      intro x hz
      exact Work.Diff.STE.csqp_periodization_eq_sum_boxIdx (f := F) hsuppF_open hz
    have hpoint : ∀ x ∈ Work.Diff.STE.unitCube (ι := Fin n),
        Work.Diff.STE.pdVec m β
            (fun z : Fin n → ℝ => ∑' k : Fin n → ℤ, f (z + Work.Diff.STE.iVec k)) x
          = (fun z : Fin n → ℝ => ∑' k : Fin n → ℤ, F (z + Work.Diff.STE.iVec k)) x := by
      intro x hx
      have hz : ∀ i : Fin n, x i ∈ Set.Ioo (-(1 / 4 : ℝ)) (5 / 4) := by
        intro i
        have hxi : x i ∈ Set.Ioc (0 : ℝ) 1 := by
          have h := Set.mem_pi.mp hx i (Set.mem_univ i)
          simpa only [Work.Diff.STE.unitCube, Set.mem_Ioc] using h
        exact ⟨by linarith [(Set.mem_Ioc.mp hxi).1], by linarith [(Set.mem_Ioc.mp hxi).2]⟩
      rw [Work.Diff.STE.B3.steB3_pdVec_periodization_eq_sum hf' hsupp_open m β x hx]
      rw [hperF x hz]
    have hint_eq : (∫ x in Work.Diff.STE.unitCube (ι := Fin n),
          ‖Work.Diff.STE.pdVec m β
            (fun z : Fin n → ℝ => ∑' k : Fin n → ℤ, f (z + Work.Diff.STE.iVec k)) x‖ ^ 2)
        = ∫ x in Work.Diff.STE.unitCube (ι := Fin n),
            ‖(fun z : Fin n → ℝ => ∑' k : Fin n → ℤ, F (z + Work.Diff.STE.iVec k)) x‖ ^ 2 := by
      refine setIntegral_congr_fun BesselCont.measSet_unitCube (fun x hx => ?_)
      rw [hpoint x hx]
    have hkey : Work.Diff.STE.ENormSq 0 (Work.Diff.STE.pdVec m β
          (fun z : Fin n → ℝ => ∑' k : Fin n → ℤ, f (z + Work.Diff.STE.iVec k)))
        ≤ ((Work.Diff.STE.csqp_boxIdx (Fin n)).card : ℝ) ^ 2
            * ∫ z in Metric.ball (0 : Fin n → ℝ) R, ‖F z‖ ^ 2 := by
      have hball_eq : (∫ z in Metric.ball (0 : Fin n → ℝ) R, ‖F z‖ ^ 2)
          = ∫ z : Fin n → ℝ, ‖F z‖ ^ 2 := by
        refine setIntegral_eq_integral_of_forall_compl_eq_zero (fun x hx => ?_)
        have hxR : R ≤ ‖x‖ := by
          rw [Metric.mem_ball] at hx
          rw [dist_zero_right] at hx
          exact not_lt.mp hx
        rw [hFzero x hxR]
        simp
      calc Work.Diff.STE.ENormSq 0 (Work.Diff.STE.pdVec m β
            (fun z : Fin n → ℝ => ∑' k : Fin n → ℤ, f (z + Work.Diff.STE.iVec k)))
          = ∫ x in Work.Diff.STE.unitCube (ι := Fin n),
              ‖Work.Diff.STE.pdVec m β
                (fun z : Fin n → ℝ => ∑' k : Fin n → ℤ, f (z + Work.Diff.STE.iVec k)) x‖ ^ 2 :=
            ENormSq_zero_eq_integral _
        _ = ∫ x in Work.Diff.STE.unitCube (ι := Fin n),
              ‖(fun z : Fin n → ℝ => ∑' k : Fin n → ℤ, F (z + Work.Diff.STE.iVec k)) x‖ ^ 2 :=
            hint_eq
        _ = Work.Diff.STE.ENormSq 0
              (fun z : Fin n → ℝ => ∑' k : Fin n → ℤ, F (z + Work.Diff.STE.iVec k)) :=
            (ENormSq_zero_eq_integral _).symm
        _ ≤ ((Work.Diff.STE.csqp_boxIdx (Fin n)).card : ℝ) ^ 2 * ∫ x : Fin n → ℝ, ‖F x‖ ^ 2 := by
            have h := Work.Diff.STE.B3.steB3_ENormSq_periodization_le_integral hFcd hsuppF_open 0
            rw [sum_fin_zero_integral F] at h
            exact h
        _ = ((Work.Diff.STE.csqp_boxIdx (Fin n)).card : ℝ) ^ 2
              * ∫ z in Metric.ball (0 : Fin n → ℝ) R, ‖F z‖ ^ 2 := by rw [← hball_eq]
    simpa [hF] using hkey

end Work.Diff.STE.Lead.GalTame
