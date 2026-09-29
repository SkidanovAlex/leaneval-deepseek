import Mathlib
import Submission.Work.TMC13.Basic
import Submission.Work.TMContract.Components
import Submission.Work.TMPuig.PosDefs
import Submission.Work.TMPuig.pruferStep_basic
import Submission.Work.TMComp.IDSPrufer.contx
import Submission.Work.TMPuig.upperTri_decomp_periodic

/-!
# Existence of a bounded positive projective lift (Puig's argument, AJ Lemma 4.3)

For a continuous `1`-periodic `SL(2,ℝ)`-valued family `B` of *degree zero* there is a
continuous `h : ℝ × ℝ → ℝ` with

* `h y (t+1) = h y t + 1` and `h (y+1) t = h y t`,
* `B y · dvec t = ρ · dvec (h y t)` with `ρ > 0` (`dvec t = (cos πt, sin πt)`),
* `|h y t - t| ≤ M` for some constant `M`.

The lift is built explicitly: `HasDegree` (or rather `upperTri_decomp_periodic`) writes
`B y = rot (η y) * !![ρ y, σ y; 0, 1/ρ y]` with `η, ρ, σ` continuous and `1`-periodic and
`ρ > 0`; the upper triangular factor is lifted by the composition `upperLiftC` of the three
Prüfer steps corresponding to the factorization into companion matrices
`!![r,q;0,1/r] = comp (r(q-1)) * comp (-(1/r)) * comp (-r)`, and `rot (η y)` shifts the angle
by `2 η y`.
-/

set_option autoImplicit false

open Matrix
open scoped Matrix
open Set

namespace Work.TMPuig

noncomputable section

/-! ### The upper-triangular positive lift, as a product of three Prüfer steps -/

/-- The upper triangular matrix `!![r,q;0,1/r]` (`r > 0`) is the product of the three
companion matrices `comp (r*(q-1)) * (comp (-(1/r)) * comp (-r))`. -/
lemma comp_prod_eq (r q : ℝ) (hr : 0 < r) :
    (!![r, q; 0, 1 / r] : Matrix (Fin 2) (Fin 2) ℝ) =
      Work.TMComp.RotBasics.comp (r * (q - 1)) *
        (Work.TMComp.RotBasics.comp (-(1 / r)) * Work.TMComp.RotBasics.comp (-r)) := by
  have hr0 : r ≠ 0 := ne_of_gt hr
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp only [Matrix.mul_apply, Fin.sum_univ_two, Work.TMComp.RotBasics.comp,
      Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.empty_val',
      Matrix.of_apply, Matrix.head_cons, Matrix.tail_cons, Matrix.head_fin_const,
      Fin.zero_eta, Fin.mk_one, Fin.isValue] <;>
    field_simp <;> ring

/-- `upperLiftC r q` is the positive projective lift of `!![r,q;0,1/r]`. -/
lemma upperLiftC_posLift (r q : ℝ) (hr : 0 < r) :
    Work.TMComp.RotBasics.IsPosLift (!![r, q; 0, 1 / r]) (upperLiftC r q) := by
  rw [comp_prod_eq r q hr]
  have h1 : Work.TMComp.RotBasics.IsPosLift (Work.TMComp.RotBasics.comp (r * (q - 1)))
      (Work.TMContract.pruferStep (r * (q - 1))) :=
    Work.TMComp.RotBasics.pruferStep_isPosLift (r * (q - 1))
  have h2 : Work.TMComp.RotBasics.IsPosLift (Work.TMComp.RotBasics.comp (-(1 / r)))
      (Work.TMContract.pruferStep (-(1 / r))) :=
    Work.TMComp.RotBasics.pruferStep_isPosLift (-(1 / r))
  have h3 : Work.TMComp.RotBasics.IsPosLift (Work.TMComp.RotBasics.comp (-r))
      (Work.TMContract.pruferStep (-r)) :=
    Work.TMComp.RotBasics.pruferStep_isPosLift (-r)
  have h23 := Work.TMComp.RotBasics.IsPosLift.comp _ _ _ _ h2 h3
  have h123 := Work.TMComp.RotBasics.IsPosLift.comp _ _ _ _ h1 h23
  exact h123

/-! ### Glue -/

lemma smul_vc_eq_mulVec (A : Matrix (Fin 2) (Fin 2) ℝ) (t : ℝ) :
    Work.TMComp.RotBasics.smul A (Work.TMComp.RotBasics.vc t) =
      ⟨(A.mulVec (Work.TMC13.dvec t)) 0, (A.mulVec (Work.TMC13.dvec t)) 1⟩ := by
  refine Complex.ext ?_ ?_ <;>
    simp [Work.TMComp.RotBasics.smul, Work.TMComp.RotBasics.vc, Work.TMC13.dvec,
      Matrix.mulVec_fin_two, Fin.sum_univ_two]

lemma mulVec_dvec_ne_zero {A : Matrix (Fin 2) (Fin 2) ℝ} (t : ℝ) (hA : A.det = 1) :
    A.mulVec (Work.TMC13.dvec t) ≠ 0 := by
  intro h0
  have h1 : A 0 0 * Real.cos (Real.pi * t) + A 0 1 * Real.sin (Real.pi * t) = 0 := by
    have hh := congrFun h0 0
    simpa [Matrix.mulVec_fin_two, Work.TMC13.dvec, Fin.sum_univ_two,
      Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one] using hh
  have h2 : A 1 0 * Real.cos (Real.pi * t) + A 1 1 * Real.sin (Real.pi * t) = 0 := by
    have hh := congrFun h0 1
    simpa [Matrix.mulVec_fin_two, Work.TMC13.dvec, Fin.sum_univ_two,
      Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one] using hh
  have hc : Real.cos (Real.pi * t) = 0 := by
    have key : A.det * Real.cos (Real.pi * t) = 0 := by
      rw [Matrix.det_fin_two]
      linear_combination (A 1 1) * h1 - (A 0 1) * h2
    rwa [hA, one_mul] at key
  have hs : Real.sin (Real.pi * t) = 0 := by
    have key : A.det * Real.sin (Real.pi * t) = 0 := by
      rw [Matrix.det_fin_two]
      linear_combination (A 0 0) * h2 - (A 1 0) * h1
    rwa [hA, one_mul] at key
  have h3 := Real.cos_sq_add_sin_sq (Real.pi * t)
  rw [hc, hs] at h3
  norm_num at h3

lemma smul_vc_ne_zero {A : Matrix (Fin 2) (Fin 2) ℝ} (hA : A.det = 1) (t : ℝ) :
    Work.TMComp.RotBasics.smul A (Work.TMComp.RotBasics.vc t) ≠ 0 := by
  intro h
  have hvec : A.mulVec (Work.TMC13.dvec t) = 0 := by
    have h1 : (A.mulVec (Work.TMC13.dvec t)) 0 = 0 := by
      have hh := congrArg Complex.re h
      rw [smul_vc_eq_mulVec A t] at hh
      simpa using hh
    have h2 : (A.mulVec (Work.TMC13.dvec t)) 1 = 0 := by
      have hh := congrArg Complex.im h
      rw [smul_vc_eq_mulVec A t] at hh
      simpa using hh
    funext i
    fin_cases i
    · exact h1
    · exact h2
  exact mulVec_dvec_ne_zero t hA hvec

lemma isPosLift_mulVec {A : Matrix (Fin 2) (Fin 2) ℝ} {G : ℝ → ℝ} (hA : A.det = 1)
    (h : Work.TMComp.RotBasics.IsPosLift A G) (t : ℝ) :
    ∃ ρ : ℝ, 0 < ρ ∧ A.mulVec (Work.TMC13.dvec t) = ρ • Work.TMC13.dvec (G t) := by
  refine ⟨‖Work.TMComp.RotBasics.smul A (Work.TMComp.RotBasics.vc t)‖,
    norm_pos_iff.mpr (smul_vc_ne_zero hA t), ?_⟩
  have hh' : (⟨(A.mulVec (Work.TMC13.dvec t)) 0, (A.mulVec (Work.TMC13.dvec t)) 1⟩ : ℂ) =
      (↑(‖Work.TMComp.RotBasics.smul A (Work.TMComp.RotBasics.vc t)‖ : ℝ) : ℂ) •
        Work.TMComp.RotBasics.vc (G t) := by
    rw [← smul_vc_eq_mulVec A t]
    exact h t
  have hre := congrArg Complex.re hh'
  have him := congrArg Complex.im hh'
  simp only [Work.TMComp.RotBasics.vc, Complex.smul_re, Complex.smul_im, Complex.ofReal_re,
    Complex.ofReal_im, mul_zero, sub_zero, zero_mul, add_zero] at hre him
  ext i
  fin_cases i
  · simpa [Work.TMComp.RotBasics.vc, Work.TMC13.dvec, Matrix.mulVec_fin_two,
      Fin.sum_univ_two] using hre
  · simpa [Work.TMComp.RotBasics.vc, Work.TMC13.dvec, Matrix.mulVec_fin_two,
      Fin.sum_univ_two] using him

lemma upperLiftC_add_one (r q t : ℝ) : upperLiftC r q (t + 1) = upperLiftC r q t + 1 := by
  unfold upperLiftC
  rw [Work.TMComp.RotBasics.pruferStep_add_one,
    Work.TMComp.RotBasics.pruferStep_add_one,
    Work.TMComp.RotBasics.pruferStep_add_one]

lemma upperLiftC_sub_bound (r q t : ℝ) : |upperLiftC r q t - t| ≤ 9 / 2 := by
  have key : ∀ a s : ℝ, |Work.TMContract.pruferStep a s - s| ≤ 3 / 2 := by
    intro a s
    have h := Work.TMPuig.pruferStep_sub_mem a s
    rw [abs_le]
    constructor <;> linarith [h.1, h.2]
  set u : ℝ := Work.TMContract.pruferStep (-r) t with hu
  set v : ℝ := Work.TMContract.pruferStep (-(1 / r)) u with hv
  set w : ℝ := Work.TMContract.pruferStep (r * (q - 1)) v with hw
  have h3 : |u - t| ≤ 3 / 2 := key _ _
  have h2 : |v - u| ≤ 3 / 2 := key _ _
  have h1 : |w - v| ≤ 3 / 2 := key _ _
  have hsum : upperLiftC r q t - t = (u - t) + (v - u) + (w - v) := by
    simp only [hu, hv, hw]
    unfold upperLiftC
    ring
  rw [hsum]
  have hA : |(u - t) + (v - u) + (w - v)| ≤ |(u - t) + (v - u)| + |w - v| := abs_add_le _ _
  have hB : |(u - t) + (v - u)| ≤ |u - t| + |v - u| := abs_add_le _ _
  linarith

lemma upperLiftC_continuous_pair {R Q : ℝ → ℝ} (hR : Continuous R) (hR0 : ∀ y, R y ≠ 0)
    (hQ : Continuous Q) :
    Continuous (fun p : ℝ × ℝ => upperLiftC (R p.1) (Q p.1) p.2) := by
  have hR' : Continuous fun p : ℝ × ℝ => R p.1 := hR.comp continuous_fst
  have hQ' : Continuous fun p : ℝ × ℝ => Q p.1 := hQ.comp continuous_fst
  have h1 : Continuous fun p : ℝ × ℝ => Work.TMContract.pruferStep (-R p.1) p.2 :=
    Work.TMComp.IDSPrufer.pruferStep_pair_cont.comp (hR'.neg.prodMk continuous_snd)
  have hb : Continuous fun p : ℝ × ℝ => -(1 / R p.1) := by
    simp only [one_div]
    exact (hR'.inv₀ (fun p => hR0 p.1)).neg
  have h2 : Continuous fun p : ℝ × ℝ =>
      Work.TMContract.pruferStep (-(1 / R p.1)) (Work.TMContract.pruferStep (-R p.1) p.2) :=
    Work.TMComp.IDSPrufer.pruferStep_pair_cont.comp (hb.prodMk h1)
  have ha : Continuous fun p : ℝ × ℝ => R p.1 * (Q p.1 - 1) := hR'.mul (hQ'.sub continuous_const)
  have h3 : Continuous fun p : ℝ × ℝ =>
      Work.TMContract.pruferStep (R p.1 * (Q p.1 - 1))
        (Work.TMContract.pruferStep (-(1 / R p.1)) (Work.TMContract.pruferStep (-R p.1) p.2)) :=
    Work.TMComp.IDSPrufer.pruferStep_pair_cont.comp (ha.prodMk h2)
  exact h3

lemma eta_int_period {η : ℝ → ℝ} (h : ∀ x : ℝ, η (x + 1) = η x) :
    ∀ (n : ℤ) (x : ℝ), η (x + (n : ℝ)) = η x := by
  have hnat : ∀ k : ℕ, ∀ x : ℝ, η (x + (k : ℝ)) = η x := by
    intro k
    induction k with
    | zero => intro x; simp
    | succ j ih =>
        intro x
        have hcast : ((j + 1 : ℕ) : ℝ) = (j : ℝ) + 1 := by push_cast; ring
        rw [hcast, show x + ((j : ℝ) + 1) = (x + (j : ℝ)) + 1 by ring, h, ih]
  intro n x
  obtain ⟨k, hk | hk⟩ := Int.eq_nat_or_neg n
  · rw [hk]; push_cast; exact hnat k x
  · rw [hk]; push_cast
    have hh := hnat k (x - (k : ℝ))
    rw [show x - (k : ℝ) + (k : ℝ) = x by ring] at hh
    rw [show x + -(k : ℝ) = x - (k : ℝ) by ring, hh]

lemma eta_bounded {η : ℝ → ℝ} (hc : Continuous η) (h : ∀ x : ℝ, η (x + 1) = η x) :
    ∃ K : ℝ, ∀ x : ℝ, |η x| ≤ K := by
  obtain ⟨K, hK⟩ :=
    (isCompact_Icc (a := (0 : ℝ)) (b := 1)).exists_bound_of_continuousOn hc.continuousOn
  refine ⟨K, fun x => ?_⟩
  have hmem : x - (⌊x⌋ : ℝ) ∈ Set.Icc (0 : ℝ) 1 :=
    ⟨by linarith [Int.floor_le x], by linarith [Int.lt_floor_add_one x]⟩
  have hper : η x = η (x - (⌊x⌋ : ℝ)) := by
    have hh := eta_int_period h ⌊x⌋ (x - (⌊x⌋ : ℝ))
    rwa [show x - (⌊x⌋ : ℝ) + (⌊x⌋ : ℝ) = x by ring] at hh
  have hb := hK (x - (⌊x⌋ : ℝ)) hmem
  rw [Real.norm_eq_abs] at hb
  rwa [hper]

theorem pos_lift_exists
    (B : ℝ → Matrix (Fin 2) (Fin 2) ℝ)
    (hB : ∀ i j, AnalyticOnNhd ℝ (fun x => B x i j) univ)
    (hper : ∀ x, B (x + 1) = B x) (hdet : ∀ x, (B x).det = 1)
    (hdeg : Work.TMContract.HasDegree B 0) :
    ∃ h : ℝ → ℝ → ℝ,
      Continuous (Function.uncurry h) ∧
      (∀ y t : ℝ, h y (t + 1) = h y t + 1) ∧
      (∀ y t : ℝ, h (y + 1) t = h y t) ∧
      (∀ y t : ℝ, ∃ ρ : ℝ, 0 < ρ ∧
        (B y).mulVec (Work.TMC13.dvec t) = ρ • Work.TMC13.dvec (h y t)) ∧
      (∃ M : ℝ, ∀ y t : ℝ, |h y t - t| ≤ M) := by
  obtain ⟨η, ρ, σ, hηc, hηp, hρc, hσc, hρper, hσper, hρpos, hdecomp⟩ :=
    upperTri_decomp_periodic B hper hdet hdeg
  refine ⟨fun y t => upperLiftC (ρ y) (σ y) t + 2 * η y, ?_, ?_, ?_, ?_, ?_⟩
  · -- continuity
    have h1 : Continuous fun p : ℝ × ℝ => 2 * η p.1 := (hηc.comp continuous_fst).const_mul 2
    have h2 : Continuous fun p : ℝ × ℝ => upperLiftC (ρ p.1) (σ p.1) p.2 :=
      upperLiftC_continuous_pair hρc (fun y => ne_of_gt (hρpos y)) hσc
    exact h2.add h1
  · -- `t`-periodicity
    intro y t
    show upperLiftC (ρ y) (σ y) (t + 1) + 2 * η y
      = (upperLiftC (ρ y) (σ y) t + 2 * η y) + 1
    rw [upperLiftC_add_one]
    ring
  · -- `y`-periodicity
    intro y t
    show upperLiftC (ρ (y + 1)) (σ (y + 1)) t + 2 * η (y + 1)
      = upperLiftC (ρ y) (σ y) t + 2 * η y
    rw [hηp y, hρper y, hσper y]
  · -- projective identity
    intro y t
    have hpos := upperLiftC_posLift (ρ y) (σ y) (hρpos y)
    have hshift0 := Work.TMComp.RotBasics.IsPosLift.shift
      (!![ρ y, σ y; 0, 1 / ρ y]) (upperLiftC (ρ y) (σ y)) (2 * η y) hpos
    rw [show (2 * η y) / 2 = η y by ring] at hshift0
    have hshift : Work.TMComp.RotBasics.IsPosLift (B y)
        (fun t => upperLiftC (ρ y) (σ y) t + 2 * η y) := by
      rw [hdecomp y]
      exact hshift0
    exact isPosLift_mulVec (hdet y) hshift t
  · -- bounded displacement
    obtain ⟨K, hK⟩ := eta_bounded hηc hηp
    refine ⟨2 * K + 9 / 2, fun y t => ?_⟩
    have h1 : |upperLiftC (ρ y) (σ y) t - t| ≤ 9 / 2 := upperLiftC_sub_bound _ _ _
    have h2 : |2 * η y| ≤ 2 * K := by
      rw [abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 2)]
      linarith [hK y]
    have hsplit : upperLiftC (ρ y) (σ y) t + 2 * η y - t
        = (upperLiftC (ρ y) (σ y) t - t) + 2 * η y := by ring
    rw [hsplit]
    calc |(upperLiftC (ρ y) (σ y) t - t) + 2 * η y|
        ≤ |upperLiftC (ρ y) (σ y) t - t| + |2 * η y| := abs_add_le _ _
      _ ≤ 9 / 2 + 2 * K := by linarith
      _ = 2 * K + 9 / 2 := by ring

end

end Work.TMPuig
