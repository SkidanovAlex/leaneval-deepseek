import Mathlib
import Submission.Work.Radial.Basic
import Submission.Work.Core.Basic
import Submission.Work.RadialSpace.Basic
import Submission.Work.RadialSpace.Profile
import Submission.Work.RadialSpace.EvenHalfDeriv
import Submission.Work.RadialSpace.evenHalfDeriv_eq
import Submission.Work.RadialSpace.iteratedDeriv_comp_sqrt
import Submission.Work.RadialSpace.tendsto_iteratedDeriv_comp_sqrt
import Submission.Work.RadialSpace.iteratedDeriv_comp_sqrt_pow_mul_le
import Submission.Work.RadialSpace.borel_lemma
import Submission.Work.RadialSpace.contDiff_glue
import Submission.Work.Sampling.rapidlyDecreasing_coeffs

namespace Work.Radial

open LeanEval.Analysis.CKMRVInterpolation
open Filter Topology

/-- The `Work.Radial.profile` of a function is the `Work.RadialSpace.profile`
composed with `t ↦ √t`. -/
lemma profile_eq_comp_sqrt {n : ℕ} [NeZero n]
    (f : EuclideanSpace ℝ (Fin n) → ℂ) (t : ℝ) :
    Work.Radial.profile f t = Work.RadialSpace.profile f (Real.sqrt t) := by
  rw [Work.Radial.profile, Work.RadialSpace.profile, Function.comp_apply, axis]
  exact congrArg f (Work.Sampling.realIncl_eq_smul (n := n) (Real.sqrt t)).symm

/-- For a radial function, the profile at `‖x‖²` recovers the function. -/
lemma profile_norm_sq {n : ℕ} [NeZero n]
    (f : EuclideanSpace ℝ (Fin n) → ℂ) (hf : Radial f) (x : EuclideanSpace ℝ (Fin n)) :
    f x = Work.Radial.profile f (‖x‖ ^ 2) := by
  rw [profile_eq_comp_sqrt, Real.sqrt_sq (norm_nonneg x)]
  exact Work.RadialSpace.profile_eq_of_radial hf x

/-! ### A smooth function of `√·` -/

/-- An even smooth function composed with `√·` is smooth on `[0, ∞)`. -/
theorem contDiffOn_comp_sqrt {g : ℝ → ℂ} (hg : ContDiff ℝ Work.RadialSpace.Smooth g)
    (he : Function.Even g) :
    ContDiffOn ℝ Work.RadialSpace.Smooth (fun t : ℝ => g (Real.sqrt t)) (Set.Ici 0) := by
  obtain ⟨W, hW, hWjet⟩ := Work.RadialSpace.borel_lemma
    (fun m => (Work.RadialSpace.evenHalfDeriv^[m]) g 0)
  have hW0 : W 0 = g 0 := by simpa using hWjet 0
  have hjet : ∀ m : ℕ, Filter.Tendsto (iteratedDeriv m fun t : ℝ => g (Real.sqrt t))
      (nhdsWithin (0:ℝ) (Set.Ioi 0)) (nhds (iteratedDeriv m W 0)) := by
    intro m
    simpa only [hWjet m] using Work.RadialSpace.tendsto_iteratedDeriv_comp_sqrt hg he m
  have hS : ContDiffOn ℝ Work.RadialSpace.Smooth (fun t : ℝ => Real.sqrt t) (Set.Ioi 0) := by
    intro x hx
    rw [contDiffWithinAt_iff_contDiffAt (isOpen_Ioi.mem_nhds hx)]
    exact Real.contDiffAt_sqrt (ne_of_gt hx)
  have hF : ContDiffOn ℝ Work.RadialSpace.Smooth (fun t : ℝ => g (Real.sqrt t)) (Set.Ioi 0) :=
    (hg.contDiffOn (s := Set.univ)).comp hS (fun x _ => trivial)
  have hglue := Work.RadialSpace.contDiff_glue hF hW hjet
  exact hglue.contDiffOn.congr (fun t ht => by
    by_cases h : 0 < t
    · simp [h]
    · have ht0 : t = 0 := le_antisymm (le_of_not_gt h) ht
      subst ht0; simp [hW0])

/-! ### The derivatives of the exponential factor -/

lemma hasDerivAt_exp_mul (c t : ℝ) :
    HasDerivAt (fun s : ℝ => (Real.exp (c * s) : ℂ)) ((c:ℂ) * (Real.exp (c * t) : ℂ)) t := by
  have h1 : HasDerivAt (fun s : ℝ => c * s) c t := by
    simpa using (hasDerivAt_id t).const_mul c
  have h := ((Real.hasDerivAt_exp (c * t)).comp t h1).ofReal_comp
  have h2 : ((Real.exp (c * t) * c : ℝ) : ℂ) = (c:ℂ) * (Real.exp (c * t) : ℂ) := by
    push_cast; ring
  rwa [h2] at h

lemma iteratedDeriv_exp_mul (c : ℝ) (i : ℕ) (t : ℝ) :
    iteratedDeriv i (fun s : ℝ => (Real.exp (c * s) : ℂ)) t
      = (c : ℂ) ^ i * (Real.exp (c * t) : ℂ) := by
  induction i generalizing t with
  | zero => simp
  | succ i ih =>
      rw [iteratedDeriv_succ, show iteratedDeriv i (fun s : ℝ => (Real.exp (c * s) : ℂ))
            = fun t => (c:ℂ)^i * (Real.exp (c*t):ℂ) from funext ih]
      rw [deriv_const_mul _ ((hasDerivAt_exp_mul c t).differentiableAt)]
      rw [(hasDerivAt_exp_mul c t).deriv]
      rw [pow_succ]
      ring

lemma norm_ofReal_exp (x : ℝ) : ‖((Real.exp x : ℝ) : ℂ)‖ = Real.exp x := by
  rw [Complex.ofReal_exp, Complex.norm_exp]; simp

/-- Leibniz with the exponential factor pulled out. -/
lemma exp_mul_iteratedDeriv_le (c t : ℝ) (G : ℝ → ℂ) (j : ℕ)
    (hE : ContDiffAt ℝ (↑j) (fun s : ℝ => (Real.exp (c * s) : ℂ)) t)
    (hG : ContDiffAt ℝ (↑j) G t) :
    Real.exp (-(c * t)) * ‖iteratedDeriv j (fun s : ℝ => (Real.exp (c * s) : ℂ) * G s) t‖
      ≤ ∑ i ∈ Finset.range (j + 1), (j.choose i : ℝ) * |c| ^ i * ‖iteratedDeriv (j - i) G t‖ := by
  change Real.exp (-(c * t)) * ‖iteratedDeriv j ((fun s : ℝ => (Real.exp (c * s) : ℂ)) * G) t‖
      ≤ ∑ i ∈ Finset.range (j + 1), (j.choose i : ℝ) * |c| ^ i * ‖iteratedDeriv (j - i) G t‖
  rw [iteratedDeriv_mul hE hG]
  have h2 : Real.exp (-(c * t)) * ‖∑ i ∈ Finset.range (j + 1),
        ↑(j.choose i) * iteratedDeriv i (fun s : ℝ => (Real.exp (c * s) : ℂ)) t
          * iteratedDeriv (j - i) G t‖
      = ‖(↑(Real.exp (-(c * t))) : ℂ) * (∑ i ∈ Finset.range (j + 1),
        ↑(j.choose i) * iteratedDeriv i (fun s : ℝ => (Real.exp (c * s) : ℂ)) t
          * iteratedDeriv (j - i) G t)‖ := by
    rw [norm_mul, norm_ofReal_exp]
  rw [h2]
  have h3 : (↑(Real.exp (-(c * t))) : ℂ) * (∑ i ∈ Finset.range (j + 1),
        ↑(j.choose i) * iteratedDeriv i (fun s : ℝ => (Real.exp (c * s) : ℂ)) t
          * iteratedDeriv (j - i) G t)
      = ∑ i ∈ Finset.range (j + 1), ↑(j.choose i) * (c : ℂ) ^ i
          * iteratedDeriv (j - i) G t := by
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun i hi => ?_
    rw [iteratedDeriv_exp_mul]
    have hcc : (↑(Real.exp (-(c * t))) : ℂ) * ↑(Real.exp (c * t)) = 1 := by
      rw [← Complex.ofReal_mul, ← Real.exp_add, show -(c * t) + c * t = 0 by ring, Real.exp_zero,
        Complex.ofReal_one]
    linear_combination (↑(j.choose i) * (↑c : ℂ) ^ i * iteratedDeriv (j - i) G t) * hcc
  rw [h3]
  refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun i hi => ?_)
  rw [norm_mul, norm_mul]
  have hc1 : ‖(↑(j.choose i) : ℂ)‖ = (j.choose i : ℝ) := by simp
  have hc2 : ‖(c : ℂ) ^ i‖ = |c| ^ i := by rw [norm_pow]; simp
  rw [hc1, hc2]

/-! ### Decay of the de-Gaussed profile -/

/-- The de-Gaussed profile `e^{c t} g(√t)` has derivatives decaying faster than any
polynomial. -/
theorem deGaussed_decay (g : SchwartzMap ℝ ℂ) (he : Function.Even ⇑g) (c : ℝ) :
    ∀ j K : ℕ, ∀ ε : ℝ, 0 < ε → ∃ T : ℝ, ∀ t : ℝ, T ≤ t →
      (1 + t) ^ K * Real.exp (-(c * t)) *
        ‖iteratedDerivWithin j
          (fun s : ℝ => (Real.exp (c * s) : ℂ) * ⇑g (Real.sqrt s))
          (Set.Ici 0) t‖ ≤ ε := by
  intro j K ε hε
  choose C hC using fun m => Work.RadialSpace.iteratedDeriv_comp_sqrt_pow_mul_le g he m (K+1)
  have hCnn : ∀ m, 0 ≤ C m := fun m =>
    le_trans (norm_nonneg _) (by simpa using hC m 1 le_rfl)
  set W : ℝ := ∑ i ∈ Finset.range (j+1), (j.choose i : ℝ) * |c|^i with hW
  set δ : ℝ := ε / W with hδ
  have hW1 : 1 ≤ W := by
    rw [hW]
    refine le_trans ?_ (Finset.single_le_sum (f := fun i => (j.choose i : ℝ) * |c|^i)
      (fun i _ => by positivity) (Finset.mem_range.mpr (Nat.succ_pos j)))
    simp
  have hWpos : 0 < W := lt_of_lt_of_le one_pos hW1
  have hδpos : 0 < δ := by rw [hδ]; exact div_pos hε hWpos
  refine ⟨max 1 ((Finset.range (j+1)).sup' ⟨0, Finset.mem_range.mpr (Nat.succ_pos j)⟩
      (fun m => 2^K * C m / δ)), fun t ht => ?_⟩
  have hT1 : (1:ℝ) ≤ t := le_trans (le_max_left _ _) ht
  have htpos : 0 < t := lt_of_lt_of_le one_pos hT1
  have hEs : ContDiffAt ℝ (↑j) (fun s : ℝ => (Real.exp (c * s) : ℂ)) t := by
    have h1 : ContDiffAt ℝ (↑j : WithTop ℕ∞) (fun s : ℝ => c * s) t :=
      (contDiff_const.mul contDiff_id).contDiffAt
    exact Complex.ofRealCLM.contDiff.contDiffAt.comp t (Real.contDiff_exp.contDiffAt.comp t h1)
  have hGs : ContDiffAt ℝ (↑j) (fun s : ℝ => ⇑g (Real.sqrt s)) t := by
    have h1 : ContDiffAt ℝ Work.RadialSpace.Smooth (fun s : ℝ => ⇑g (Real.sqrt s)) t :=
      (g.smooth ⊤).contDiffAt.comp t (Real.contDiffAt_sqrt (ne_of_gt htpos))
    exact h1.of_le (WithTop.coe_le_coe.mpr le_top)
  rw [iteratedDerivWithin_eq_iteratedDeriv (uniqueDiffOn_Ici (0:ℝ)) (hEs.mul hGs)
    (Set.mem_Ici.mpr htpos.le)]
  calc (1 + t) ^ K * Real.exp (-(c * t)) *
        ‖iteratedDeriv j (fun s : ℝ => (Real.exp (c * s) : ℂ) * ⇑g (Real.sqrt s)) t‖
      = (1+t)^K * (Real.exp (-(c*t)) *
          ‖iteratedDeriv j (fun s : ℝ => (Real.exp (c * s) : ℂ) * ⇑g (Real.sqrt s)) t‖) := by ring
    _ ≤ (1+t)^K * ∑ i ∈ Finset.range (j+1), (j.choose i : ℝ) * |c|^i
          * ‖iteratedDeriv (j-i) (fun s : ℝ => ⇑g (Real.sqrt s)) t‖ :=
        mul_le_mul_of_nonneg_left
          (exp_mul_iteratedDeriv_le c t (fun s : ℝ => ⇑g (Real.sqrt s)) j hEs hGs) (by positivity)
    _ = ∑ i ∈ Finset.range (j+1), (j.choose i : ℝ) * |c|^i
          * ((1+t)^K * ‖iteratedDeriv (j-i) (fun s : ℝ => ⇑g (Real.sqrt s)) t‖) := by
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl fun i hi => ?_
        ring
    _ ≤ ∑ i ∈ Finset.range (j+1), (j.choose i : ℝ) * |c|^i * δ := by
        refine Finset.sum_le_sum fun i hi => ?_
        refine mul_le_mul_of_nonneg_left ?_ (by positivity)
        have hm : j - i ∈ Finset.range (j+1) :=
          Finset.mem_range.mpr (Nat.lt_succ_of_le (Nat.sub_le j i))
        have hsup : 2^K * C (j-i) / δ ≤ t :=
          le_trans (Finset.le_sup' (fun m => 2^K * C m / δ) hm)
            (le_trans (le_max_right _ _) ht)
        have hCm := hC (j-i) t hT1
        have hCmnn : 0 ≤ C (j-i) := hCnn _
        have hM : ‖iteratedDeriv (j-i) (fun s : ℝ => ⇑g (Real.sqrt s)) t‖
            ≤ C (j-i) / t^(K+1) := by
          rw [le_div_iff₀ (by positivity), mul_comm]
          exact hCm
        have hkey : (1+t)^K / t^(K+1) ≤ 2^K / t := by
          rw [show (1+t)^K / t^(K+1) = ((1+t)/t)^K / t from by rw [div_pow, div_div, pow_succ]]
          refine div_le_div_of_nonneg_right ?_ htpos.le
          refine pow_le_pow_left₀ (by positivity) ?_ K
          rw [div_le_iff₀ htpos]
          linarith
        calc (1+t)^K * ‖iteratedDeriv (j-i) (fun s : ℝ => ⇑g (Real.sqrt s)) t‖
            ≤ (1+t)^K * (C (j-i) / t^(K+1)) := mul_le_mul_of_nonneg_left hM (by positivity)
          _ = C (j-i) * ((1+t)^K / t^(K+1)) := by ring
          _ ≤ C (j-i) * (2^K / t) := mul_le_mul_of_nonneg_left hkey hCmnn
          _ = 2^K * C (j-i) / t := by ring
          _ ≤ δ := by
              rw [div_le_iff₀ htpos]
              have h := mul_le_mul_of_nonneg_right hsup hδpos.le
              rw [div_mul_cancel₀ _ hδpos.ne'] at h
              linarith [h]
    _ = ε := by
        rw [← Finset.sum_mul, ← hW, hδ, mul_comm, div_mul_cancel₀ _ hWpos.ne']

end Work.Radial

namespace Work.Radial

open scoped ContDiff

/-- The de-Gaussed profile is smooth on `[0, ∞)`, its derivatives decay faster than
any polynomial, and the profile recovers the function. -/
theorem deGaussed_profile (n : ℕ) [NeZero n] (y : ℝ)
    (f : SchwartzMap (EuclideanSpace ℝ (Fin n)) ℂ)
    (hf : LeanEval.Analysis.CKMRVInterpolation.Radial (f : EuclideanSpace ℝ (Fin n) → ℂ)) :
    ContDiffOn ℝ ∞
        (fun t : ℝ => Real.exp (Real.pi * y * t) *
          Work.Radial.profile (f : EuclideanSpace ℝ (Fin n) → ℂ) t) (Set.Ici 0) ∧
    (∀ j K : ℕ, ∀ ε : ℝ, 0 < ε → ∃ T : ℝ, ∀ t : ℝ, T ≤ t →
      (1 + t) ^ K * Real.exp (-(Real.pi * y * t)) *
        ‖iteratedDerivWithin j
          (fun t : ℝ => Real.exp (Real.pi * y * t) *
            Work.Radial.profile (f : EuclideanSpace ℝ (Fin n) → ℂ) t) (Set.Ici 0) t‖ ≤ ε) ∧
    (∀ x : EuclideanSpace ℝ (Fin n),
      f x = Work.Radial.profile (f : EuclideanSpace ℝ (Fin n) → ℂ) (‖x‖ ^ 2)) := by
  set P : ℝ → ℂ := ⇑(Work.RadialSpace.profileCLM f) with hP
  have hPfun : ∀ t : ℝ, P t = Work.RadialSpace.profile (⇑f) t := by
    intro t; rw [hP, Work.RadialSpace.profileCLM_apply]
  have hProffun : ∀ t : ℝ, Work.Radial.profile (⇑f) t = P (Real.sqrt t) := by
    intro t; rw [profile_eq_comp_sqrt, hPfun]
  have hPe : Function.Even P := by
    intro x
    rw [hPfun x, hPfun (-x)]
    exact Work.RadialSpace.profile_even hf x
  have hPsm : ContDiff ℝ Work.RadialSpace.Smooth P := by
    rw [hP]; exact (Work.RadialSpace.profileCLM f).smooth ⊤
  have hfun : (fun t : ℝ => Real.exp (Real.pi * y * t) *
        Work.Radial.profile (f : EuclideanSpace ℝ (Fin n) → ℂ) t)
      = (fun s : ℝ => (Real.exp (Real.pi * y * s) : ℂ) *
        ⇑(Work.RadialSpace.profileCLM f) (Real.sqrt s)) := by
    funext t
    rw [hProffun t]
  refine ⟨?_, ?_, ?_⟩
  · have hexp : ContDiffOn ℝ Work.RadialSpace.Smooth
        (fun t : ℝ => (Real.exp ((Real.pi * y) * t) : ℂ)) (Set.Ici 0) := by
      have h1 : ContDiffOn ℝ Work.RadialSpace.Smooth
          (fun t : ℝ => Real.exp ((Real.pi * y) * t)) (Set.Ici 0) :=
        Real.contDiff_exp.comp_contDiffOn
          ((contDiff_const (c := Real.pi * y)).mul contDiff_id).contDiffOn
      exact Complex.ofRealCLM.contDiff.comp_contDiffOn h1
    have hsqrt : ContDiffOn ℝ Work.RadialSpace.Smooth
        (fun s : ℝ => ⇑(Work.RadialSpace.profileCLM f) (Real.sqrt s)) (Set.Ici 0) :=
      contDiffOn_comp_sqrt hPsm hPe
    refine (hexp.mul hsqrt).congr ?_
    intro t ht
    rw [hProffun t]
  · intro j K ε hε
    obtain ⟨T, hT⟩ := deGaussed_decay (Work.RadialSpace.profileCLM f) hPe (Real.pi * y)
      j K ε hε
    refine ⟨T, fun t ht => ?_⟩
    rw [hfun]
    exact hT t ht
  · intro x
    exact profile_norm_sq (⇑f) hf x

end Work.Radial
