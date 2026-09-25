import Mathlib
import Submission.Work.CR.Flat.Holder
import Submission.Work.CR.Flat.Polydisc
import Submission.Work.NN.Core.CnPert

/-!
# Flat functions times `C^k` functions on a polydisc

This file proves `Work.NN.Core.contDiff_flatMul`: if `v : ℂⁿ → ℂ` is smooth and vanishes outside
the open polydisc `polydisc 0 ρ`, and `u` is `C^{k+1}` on that polydisc with finite `C^{k,α}` norm
there, then `z ↦ v z * u z` is `C^k` on all of `ℂⁿ`.

The mechanism is the classical one: since `v` is smooth and vanishes on the *closed* complement of
the open polydisc, all iterated derivatives of `v` vanish on that closed set (`iteratedFDeriv_eq_zero_of_notMem_polydisc`),
so near a boundary point `x₀` each derivative `D^i v` decays like `‖y - x₀‖^N` for every `N`
(`flat_iteratedFDeriv_bound`).  The Leibniz bound `norm_iteratedFDerivWithin_mul_le` for the
iterated derivatives of a product then shows that the within-derivatives of `v * u` on the
polydisc also decay like `‖y - x₀‖^N` at the boundary, while being the honest derivatives inside;
this makes all of them extend by `0` to the complement as continuous `C^k` data, and exhibiting this
explicit Taylor series gives `ContDiff ℝ k (fun z => v z * u z)`.

Note: the hypothesis `hv : ContDiff ℝ ⊤ v` of the requested statement is the *analytic* level
`ω = ⊤`; the proof below only uses that `v` is smooth, so we also record the smooth version
`contDiff_flatMul_of_smooth` (same conclusion, hypothesis `ContDiff ℝ ∞ v`).
-/

noncomputable section

namespace Work.NN.Core

open scoped NNReal ENNReal ContDiff Classical
open Set

/-! ## Decay of a flat function

If a smooth function is flat at a point (all its iterated derivatives vanish there), then so are
all of its iterated derivatives, with a quantitative power decay. -/

theorem flat_iteratedFDeriv_bound {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    {g : E → F} (hg : ContDiff ℝ ∞ g) (x₀ : E)
    (hflat : ∀ i : ℕ, iteratedFDeriv ℝ i g x₀ = 0) (i N : ℕ) :
    ∃ C δ : ℝ, 0 ≤ C ∧ 0 < δ ∧ ∀ y : E, ‖y - x₀‖ < δ →
      ‖iteratedFDeriv ℝ i g y‖ ≤ C * ‖y - x₀‖ ^ N := by
  induction N generalizing i with
  | zero =>
      have hcont : ContinuousAt (fun y => iteratedFDeriv ℝ i g y) x₀ :=
        ((hg.ftaylorSeries).cont i (WithTop.coe_le_coe.mpr le_top)).continuousAt
      obtain ⟨δ, hδ, hδ'⟩ := (Metric.continuousAt_iff.mp hcont) 1 one_pos
      refine ⟨1, δ, zero_le_one, hδ, fun y hy => ?_⟩
      have h1 : dist (iteratedFDeriv ℝ i g y) (iteratedFDeriv ℝ i g x₀) < 1 :=
        hδ' (by rwa [dist_eq_norm])
      rw [dist_eq_norm, hflat i, sub_zero] at h1
      rw [pow_zero, mul_one]
      exact h1.le
  | succ N ih =>
      obtain ⟨C, δ, hC, hδ, hb⟩ := ih (i + 1)
      refine ⟨C, δ, hC, hδ, fun y hy => ?_⟩
      have hfderiv : ∀ z ∈ segment ℝ x₀ y,
          fderiv ℝ (fun y => iteratedFDeriv ℝ i g y) z = (iteratedFDeriv ℝ (i + 1) g z).curryLeft :=
        fun z _ => (hg.ftaylorSeries).fderiv_eq (WithTop.coe_lt_coe.mpr (WithTop.coe_lt_top i)) z
      have hdiff : ∀ z ∈ segment ℝ x₀ y,
          DifferentiableAt ℝ (fun y => iteratedFDeriv ℝ i g y) z :=
        fun z _ => ((hg.ftaylorSeries).fderiv i
          (WithTop.coe_lt_coe.mpr (WithTop.coe_lt_top i)) z).differentiableAt
      have hbound : ∀ z ∈ segment ℝ x₀ y,
          ‖fderiv ℝ (fun y => iteratedFDeriv ℝ i g y) z‖ ≤ C * ‖y - x₀‖ ^ N := by
        intro z hz
        rw [hfderiv z hz, ContinuousMultilinearMap.curryLeft_norm]
        calc ‖iteratedFDeriv ℝ (i + 1) g z‖ ≤ C * ‖z - x₀‖ ^ N :=
              hb z (lt_of_le_of_lt (norm_sub_le_of_mem_segment hz) hy)
          _ ≤ C * ‖y - x₀‖ ^ N :=
              mul_le_mul_of_nonneg_left
                (pow_le_pow_left₀ (norm_nonneg _) (norm_sub_le_of_mem_segment hz) N) hC
      have hmv := Convex.norm_image_sub_le_of_norm_fderiv_le (𝕜 := ℝ)
        (f := fun y => iteratedFDeriv ℝ i g y) (s := segment ℝ x₀ y) (C := C * ‖y - x₀‖ ^ N)
        hdiff hbound (convex_segment x₀ y) (left_mem_segment ℝ x₀ y) (right_mem_segment ℝ x₀ y)
      rw [hflat i, sub_zero] at hmv
      calc ‖iteratedFDeriv ℝ i g y‖ ≤ C * ‖y - x₀‖ ^ N * ‖y - x₀‖ := hmv
        _ = C * ‖y - x₀‖ ^ (N + 1) := by rw [pow_succ]; ring

/-! ## Vanishing of all derivatives on the complement of the polydisc -/

theorem iteratedFDeriv_eq_zero_of_notMem_polydisc {n : ℕ} {ρ : Fin n → ℝ} (hρ : ∀ j, 0 < ρ j)
    {v : (Fin n → ℂ) → ℂ} (hv : ContDiff ℝ ∞ v)
    (hv0 : ∀ z, (∃ j, ρ j ≤ ‖z j‖) → v z = 0)
    {z : Fin n → ℂ} (hz : z ∉ Work.CR.Flat.polydisc 0 ρ) (m : ℕ) :
    iteratedFDeriv ℝ m v z = 0 := by
  obtain ⟨j, hj⟩ : ∃ j, ρ j ≤ ‖z j‖ := by
    by_contra h
    push Not at h
    exact hz (by rw [Work.CR.Flat.mem_polydisc]; exact fun i => by simpa using h i)
  set U : Set (Fin n → ℂ) := {w | ∃ i, ρ i < ‖w i‖} with hU
  have hUopen : IsOpen U := by
    have heq : U = ⋃ i, {w : Fin n → ℂ | ρ i < ‖w i‖} := by
      ext w; simp [hU]
    rw [heq]
    exact isOpen_iUnion fun i => isOpen_lt continuous_const ((continuous_apply i).norm)
  -- the boundary point `z` is a limit of points of the open exterior `U`
  set w₀ : Fin n → ℂ := Pi.single j (z j) with hw₀
  set f : ℝ → (Fin n → ℂ) := fun t => z + t • w₀ with hf
  have hfcont : Continuous f := by
    rw [hf]
    exact continuous_const.add (continuous_id.smul continuous_const)
  have hf0 : f 0 = z := by simp [hf]
  have hsub : f '' Set.Ioi (0 : ℝ) ⊆ U := by
    rintro y ⟨t, ht, rfl⟩
    rw [Set.mem_Ioi] at ht
    refine ⟨j, ?_⟩
    have h1 : (f t) j = (1 + (t : ℂ)) * z j := by
      simp only [hf, Pi.add_apply, Pi.smul_apply, hw₀, Pi.single_eq_same, Complex.real_smul]
      ring
    have h2 : ‖(1 + (t : ℂ))‖ = 1 + t := by
      rw [← Complex.ofReal_one, ← Complex.ofReal_add, Complex.norm_real,
        Real.norm_of_nonneg (by linarith : (0 : ℝ) ≤ 1 + t)]
    rw [h1, norm_mul, h2]
    nlinarith [hj, hρ j, norm_nonneg (z j), ht]
  have hzclosure : z ∈ closure U := by
    have h0 : (0 : ℝ) ∈ closure (Set.Ioi (0 : ℝ)) := by
      rw [Metric.mem_closure_iff]
      intro ε hε
      exact ⟨ε / 2, by rw [Set.mem_Ioi]; linarith, by
        rw [Real.dist_eq, zero_sub, abs_neg, abs_of_pos (by linarith : (0 : ℝ) < ε / 2)]
        linarith⟩
    have h1 : z ∈ f '' closure (Set.Ioi (0 : ℝ)) := ⟨0, h0, hf0⟩
    exact closure_mono hsub (image_closure_subset_closure_image hfcont h1)
  -- on `U` the function vanishes identically, so all its derivatives vanish there
  have hvan : Set.EqOn (iteratedFDeriv ℝ m v)
      (fun _ => (0 : ContinuousMultilinearMap ℝ (fun _ : Fin m => (Fin n → ℂ)) ℂ)) U := by
    intro y hy
    have hA : iteratedFDerivWithin ℝ m v U y =
        iteratedFDerivWithin ℝ m (fun _ => (0 : ℂ)) U y :=
      iteratedFDerivWithin_congr
        (fun w hw => hv0 w (by obtain ⟨i, hi⟩ := hw; exact ⟨i, le_of_lt hi⟩)) hy m
    have hB : iteratedFDerivWithin ℝ m v U y = iteratedFDeriv ℝ m v y :=
      (iteratedFDerivWithin_of_isOpen (s := U) m hUopen) hy
    have hC : iteratedFDerivWithin ℝ m (fun _ => (0 : ℂ)) U y =
        iteratedFDeriv ℝ m (fun _ => (0 : ℂ)) y :=
      (iteratedFDerivWithin_of_isOpen (s := U) m hUopen) hy
    rw [← hB, hA, hC, iteratedFDeriv_fun_zero]
    rfl
  have hcont : Continuous (iteratedFDeriv ℝ m v) :=
    (hv.ftaylorSeries).cont m (WithTop.coe_le_coe.mpr le_top)
  exact Set.EqOn.closure hvan hcont continuous_const hzclosure

/-! ## Bounds on the derivatives of a function with finite Hölder norm -/

theorem exists_iteratedFDerivWithin_bound_of_holderNorm_ne_top {n : ℕ} {k : ℕ} {α : ℝ}
    {ρ : Fin n → ℝ} {u : (Fin n → ℂ) → ℂ}
    (huf : Work.CR.Flat.holderNorm k α u (Work.CR.Flat.polydisc 0 ρ) ≠ ⊤) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ j : ℕ, j ≤ k → ∀ x : Fin n → ℂ,
      x ∈ Work.CR.Flat.polydisc 0 ρ →
      ‖iteratedFDerivWithin ℝ j u (Work.CR.Flat.polydisc 0 ρ) x‖ ≤ C := by
  refine ⟨(Work.CR.Flat.holderNorm k α u (Work.CR.Flat.polydisc 0 ρ)).toReal,
    ENNReal.toReal_nonneg, fun j hj x hx => ?_⟩
  have h1 : ENNReal.ofReal ‖iteratedFDerivWithin ℝ j u (Work.CR.Flat.polydisc 0 ρ) x‖
      ≤ Work.CR.Flat.holderNorm k α u (Work.CR.Flat.polydisc 0 ρ) :=
    le_trans (Work.CR.Flat.le_iterDerivNorm j u _ hx)
      (Work.CR.Flat.iterDerivNorm_le_holderNorm k α u _ hj)
  have h2 := ENNReal.toReal_mono huf h1
  rwa [ENNReal.toReal_ofReal (norm_nonneg _)] at h2

/-! ## The master estimate

Every within-derivative of `z ↦ v z * u z` on the polydisc, extended by `0` outside, decays at
every order at each point of the complement of the polydisc.  This is the Leibniz bound
`norm_iteratedFDerivWithin_mul_le` combined with the decay of the derivatives of the flat factor
`v` and the boundedness of the derivatives of `u`. -/

theorem flatMul_iteratedFDerivWithin_bound {n : ℕ} {k : ℕ} {α : ℝ} {ρ : Fin n → ℝ}
    (hρ : ∀ j, 0 < ρ j)
    {v : (Fin n → ℂ) → ℂ} (hv : ContDiff ℝ ∞ v)
    (hv0 : ∀ z, (∃ j, ρ j ≤ ‖z j‖) → v z = 0)
    {u : (Fin n → ℂ) → ℂ}
    (hu : ContDiffOn ℝ (((k + 1 : ℕ)) : ℕ∞) u (Work.CR.Flat.polydisc 0 ρ))
    (huf : Work.CR.Flat.holderNorm k α u (Work.CR.Flat.polydisc 0 ρ) ≠ ⊤)
    {m : ℕ} (hm : m ≤ k) {x₀ : Fin n → ℂ} (hx₀ : x₀ ∉ Work.CR.Flat.polydisc 0 ρ) (N : ℕ) :
    ∃ C δ : ℝ, 0 ≤ C ∧ 0 < δ ∧ ∀ y : Fin n → ℂ, ‖y - x₀‖ < δ →
      ‖(if y ∈ Work.CR.Flat.polydisc 0 ρ then
          iteratedFDerivWithin ℝ m (fun z => v z * u z) (Work.CR.Flat.polydisc 0 ρ) y
        else 0)‖ ≤ C * ‖y - x₀‖ ^ N := by
  classical
  set Ω : Set (Fin n → ℂ) := Work.CR.Flat.polydisc 0 ρ with hΩ
  have hΩopen : IsOpen Ω := Work.CR.Flat.isOpen_polydisc 0 ρ
  have hΩuniq : UniqueDiffOn ℝ Ω := hΩopen.uniqueDiffOn
  obtain ⟨Cu, hCunn, huC⟩ := exists_iteratedFDerivWithin_bound_of_holderNorm_ne_top huf
  have hvflat : ∀ i : ℕ, iteratedFDeriv ℝ i v x₀ = 0 :=
    fun i => iteratedFDeriv_eq_zero_of_notMem_polydisc hρ hv hv0 hx₀ i
  choose Cv δv hCv hδv hbnd using fun i : ℕ => flat_iteratedFDeriv_bound hv x₀ hvflat i N
  set δ : ℝ := (Finset.range (m + 1)).inf' ⟨0, Finset.mem_range.mpr (Nat.succ_pos m)⟩ δv with hδdef
  have hδpos : 0 < δ := by
    rw [hδdef]
    exact (Finset.lt_inf'_iff _).mpr fun i _ => hδv i
  have hδle : ∀ i ∈ Finset.range (m + 1), δ ≤ δv i := fun i hi => by
    rw [hδdef]
    exact Finset.inf'_le δv hi
  set C : ℝ := (∑ i ∈ Finset.range (m + 1), (m.choose i : ℝ) * Cv i) * Cu with hCdef
  have hCnn : 0 ≤ C := by
    rw [hCdef]
    exact mul_nonneg (Finset.sum_nonneg fun i _ => mul_nonneg (Nat.cast_nonneg _) (hCv i)) hCunn
  have hvΩ : ContDiffOn ℝ (((k : ℕ)) : ℕ∞) v Ω :=
    (hv.of_le (WithTop.coe_le_coe.mpr le_top)).contDiffOn
  have huΩ : ContDiffOn ℝ (((k : ℕ)) : ℕ∞) u Ω :=
    hu.of_le (by
      refine WithTop.coe_le_coe.mpr (WithTop.coe_le_coe.mpr ?_)
      exact_mod_cast Nat.le_succ k)
  refine ⟨C, δ, hCnn, hδpos, fun y hy => ?_⟩
  by_cases hyΩ : y ∈ Ω
  · rw [ite_eq_left hyΩ]
    refine le_trans (norm_iteratedFDerivWithin_mul_le (s := Ω) (A := ℂ) (f := v) (g := u)
      (N := (((k : ℕ)) : ℕ∞)) hvΩ huΩ hΩuniq hyΩ
      (show (((m : ℕ)) : ℕ∞ω) ≤ (((k : ℕ)) : ℕ∞ω) from
        WithTop.coe_le_coe.mpr (WithTop.coe_le_coe.mpr hm))) ?_
    calc (∑ i ∈ Finset.range (m + 1), (m.choose i : ℝ) *
            ‖iteratedFDerivWithin ℝ i v Ω y‖ * ‖iteratedFDerivWithin ℝ (m - i) u Ω y‖)
        ≤ ∑ i ∈ Finset.range (m + 1), (m.choose i : ℝ) * Cv i * Cu * ‖y - x₀‖ ^ N :=
          Finset.sum_le_sum fun i hi => ?_
      _ = C * ‖y - x₀‖ ^ N := by
          rw [hCdef, ← Finset.sum_mul, ← Finset.sum_mul]
    have him : i ≤ m := Nat.lt_succ_iff.mp (Finset.mem_range.mp hi)
    have hik : i ≤ k := le_trans him hm
    have hmi : m - i ≤ k := le_trans (Nat.sub_le m i) hm
    have hvbound : ‖iteratedFDerivWithin ℝ i v Ω y‖ ≤ Cv i * ‖y - x₀‖ ^ N := by
      rw [(iteratedFDerivWithin_of_isOpen (s := Ω) i hΩopen) hyΩ]
      exact hbnd i y (lt_of_lt_of_le hy (hδle i hi))
    have hubound : ‖iteratedFDerivWithin ℝ (m - i) u Ω y‖ ≤ Cu := huC (m - i) hmi y hyΩ
    calc (m.choose i : ℝ) * ‖iteratedFDerivWithin ℝ i v Ω y‖ *
            ‖iteratedFDerivWithin ℝ (m - i) u Ω y‖
        ≤ (m.choose i : ℝ) * (Cv i * ‖y - x₀‖ ^ N) * Cu :=
          mul_le_mul (mul_le_mul_of_nonneg_left hvbound (Nat.cast_nonneg _)) hubound
            (norm_nonneg _)
            (mul_nonneg (Nat.cast_nonneg _) (mul_nonneg (hCv i) (pow_nonneg (norm_nonneg _) N)))
      _ = (m.choose i : ℝ) * Cv i * Cu * ‖y - x₀‖ ^ N := by ring
  · rw [ite_eq_right hyΩ]
    simp only [norm_zero]
    exact mul_nonneg hCnn (pow_nonneg (norm_nonneg _) N)

/-! ## The main theorem -/

/-- **Smooth version.**  If `v : ℂⁿ → ℂ` is `C^∞` and vanishes outside the open polydisc
`polydisc 0 ρ`, and `u` is `C^{k+1}` on that polydisc with finite `C^{k,α}` norm there, then
`z ↦ v z * u z` is `C^k` on all of `ℂⁿ`. -/
theorem contDiff_flatMul_of_smooth {n : ℕ} {k : ℕ} {α : ℝ} {ρ : Fin n → ℝ} (hρ : ∀ j, 0 < ρ j)
    {v : Work.NN.Core.Cn n → ℂ} (hv : ContDiff ℝ ∞ v)
    (hv0 : ∀ z, (∃ j, ρ j ≤ ‖z j‖) → v z = 0)
    {u : Work.NN.Core.Cn n → ℂ}
    (hu : ContDiffOn ℝ (((k + 1 : ℕ)) : ℕ∞) u (Work.CR.Flat.polydisc 0 ρ))
    (huf : Work.CR.Flat.holderNorm k α u (Work.CR.Flat.polydisc 0 ρ) ≠ ⊤) :
    ContDiff ℝ k (fun z => v z * u z) := by
  classical
  set Ω : Set (Work.NN.Core.Cn n) := Work.CR.Flat.polydisc 0 ρ with hΩ
  have hΩopen : IsOpen Ω := Work.CR.Flat.isOpen_polydisc 0 ρ
  have hΩuniq : UniqueDiffOn ℝ Ω := hΩopen.uniqueDiffOn
  have hv0' : ∀ z ∉ Ω, v z = 0 := fun z hz =>
    hv0 z (by
      by_contra h
      push Not at h
      exact hz (by rw [Work.CR.Flat.mem_polydisc]; exact fun i => by simpa using h i))
  -- smoothness of the pieces on the polydisc
  have hk1 : (((k + 1 : ℕ)) : ℕ∞) ≤ (∞ : ℕ∞ω) := WithTop.coe_le_coe.mpr le_top
  have hk0 : (((k : ℕ)) : ℕ∞ω) ≤ (((k + 1 : ℕ)) : ℕ∞ω) :=
    WithTop.coe_le_coe.mpr (WithTop.coe_le_coe.mpr (Nat.le_succ k))
  have hvΩ : ContDiffOn ℝ (((k + 1 : ℕ)) : ℕ∞) v Ω := (hv.of_le hk1).contDiffOn
  have hwΩ : ContDiffOn ℝ (((k + 1 : ℕ)) : ℕ∞) (fun z => v z * u z) Ω := hvΩ.mul hu
  have hwkΩ : ContDiffOn ℝ (((k : ℕ)) : ℕ∞) (fun z => v z * u z) Ω := hwΩ.of_le hk0
  -- the candidate Taylor family: the within-derivatives on the polydisc, extended by `0`
  set p : Work.NN.Core.Cn n → FormalMultilinearSeries ℝ (Work.NN.Core.Cn n) ℂ :=
    fun x m => if x ∈ Ω then iteratedFDerivWithin ℝ m (fun z => v z * u z) Ω x else 0 with hp
  have hp_pos : ∀ x ∈ Ω, ∀ m, p x m = iteratedFDerivWithin ℝ m (fun z => v z * u z) Ω x :=
    fun x hx m => by simp only [hp]; exact ite_eq_left hx
  have hp_neg : ∀ x ∉ Ω, ∀ m, p x m = 0 := fun x hx m => by simp only [hp]; exact ite_eq_right hx
  have hzero : ∀ x, (p x 0).curry0 = (fun z => v z * u z) x := by
    intro x
    by_cases hx : x ∈ Ω
    · rw [hp_pos x hx 0]
      simp [ContinuousMultilinearMap.curry0_apply, iteratedFDerivWithin_zero_apply]
    · rw [hp_neg x hx 0]
      simp only [ContinuousMultilinearMap.curry0_apply, zero_apply]
      rw [show v x = 0 from hv0' x hx, zero_mul]
  have hfderiv : ∀ m : ℕ, m < (((k : ℕ)) : ℕ∞ω) → ∀ x,
      HasFDerivAt (fun y => p y m) (p x m.succ).curryLeft x := by
    intro m hm x
    have hmk : m < k := by exact_mod_cast hm
    have hmk1 : m < k + 1 := Nat.lt_succ_of_lt hmk
    by_cases hx : x ∈ Ω
    · have hFTS := hwΩ.ftaylorSeriesWithin hΩuniq
      have hfd := hFTS.fderivWithin m (by exact_mod_cast hmk1) x hx
      have h2 : HasFDerivAt (fun y => iteratedFDerivWithin ℝ m (fun z => v z * u z) Ω y)
          ((p x m.succ).curryLeft) x := by
        have h3 : (iteratedFDerivWithin ℝ (m + 1) (fun z => v z * u z) Ω x).curryLeft
            = (p x m.succ).curryLeft := by
          rw [hp_pos x hx m.succ]
        rw [← h3]
        exact hfd.hasFDerivAt (hΩopen.mem_nhds hx)
      refine h2.congr_of_eventuallyEq ?_
      filter_upwards [hΩopen.mem_nhds hx] with y hy
      exact hp_pos y hy m
    · rw [hp_neg x hx m.succ]
      have hzero' : (0 : ContinuousMultilinearMap ℝ
          (fun _ : Fin (m + 1) => Work.NN.Core.Cn n) ℂ).curryLeft = 0 := by
        ext v w
        simp [ContinuousMultilinearMap.curryLeft_apply]
      rw [hzero', hasFDerivAt_iff_isLittleO, Asymptotics.isLittleO_iff]
      intro c hc
      obtain ⟨C, δ, hCnn, hδ, hbound⟩ :=
        flatMul_iteratedFDerivWithin_bound hρ hv hv0 hu huf (le_of_lt hmk) hx 2
      have hA : 0 < min δ (c / (C + 1)) := lt_min hδ (div_pos hc (by linarith))
      filter_upwards [Metric.ball_mem_nhds x hA] with y hy
      rw [Metric.mem_ball, dist_eq_norm] at hy
      have hyδ : ‖y - x‖ < δ := lt_of_lt_of_le hy (min_le_left _ _)
      have hyc : ‖y - x‖ < c / (C + 1) := lt_of_lt_of_le hy (min_le_right _ _)
      have hbd : ‖p y m‖ ≤ C * ‖y - x‖ ^ 2 := by
        rw [hp]
        exact hbound y hyδ
      have hx0 : p x m = 0 := hp_neg x hx m
      rw [hx0]
      simp only [zero_apply, sub_zero]
      calc ‖p y m‖ ≤ C * ‖y - x‖ ^ 2 := hbd
        _ = C * ‖y - x‖ * ‖y - x‖ := by rw [pow_two]; ring
        _ ≤ c * ‖y - x‖ := by
            refine mul_le_mul_of_nonneg_right ?_ (norm_nonneg _)
            have hpos : 0 ≤ c / (C + 1) := div_nonneg hc.le (by linarith)
            calc C * ‖y - x‖ ≤ C * (c / (C + 1)) := mul_le_mul_of_nonneg_left hyc.le hCnn
              _ ≤ (C + 1) * (c / (C + 1)) := mul_le_mul_of_nonneg_right (by linarith) hpos
              _ = c := by
                  rw [show (C + 1) * (c / (C + 1)) = c * (C + 1) / (C + 1) by ring,
                    mul_div_cancel_right₀ c (by linarith : (C + 1) ≠ 0)]
  have hcont : ∀ m : ℕ, m ≤ (((k : ℕ)) : ℕ∞ω) → Continuous fun x => p x m := by
    intro m hm
    have hmk : m ≤ k := by exact_mod_cast hm
    rw [continuous_iff_continuousAt]
    intro x
    by_cases hx : x ∈ Ω
    · have hcontΩ : ContinuousOn
          (fun y => iteratedFDerivWithin ℝ m (fun z => v z * u z) Ω y) Ω :=
        hwkΩ.continuousOn_iteratedFDerivWithin hm hΩuniq
      refine (hcontΩ.continuousAt (hΩopen.mem_nhds hx)).congr ?_
      filter_upwards [hΩopen.mem_nhds hx] with y hy
      exact (hp_pos y hy m).symm
    · have hx0 : p x m = 0 := hp_neg x hx m
      rw [ContinuousAt, hx0]
      rw [Metric.tendsto_nhds]
      intro ε hε
      obtain ⟨C, δ, hCnn, hδ, hbound⟩ :=
        flatMul_iteratedFDerivWithin_bound hρ hv hv0 hu huf hmk hx 1
      have hA : 0 < min δ (ε / (2 * (C + 1))) :=
        lt_min hδ (div_pos (by linarith) (by linarith))
      filter_upwards [Metric.ball_mem_nhds x hA] with y hy
      rw [Metric.mem_ball, dist_eq_norm] at hy
      have hyδ : ‖y - x‖ < δ := lt_of_lt_of_le hy (min_le_left _ _)
      have hyε : ‖y - x‖ < ε / (2 * (C + 1)) := lt_of_lt_of_le hy (min_le_right _ _)
      have hbd : ‖p y m‖ ≤ C * ‖y - x‖ := by
        have h := hbound y hyδ
        rw [pow_one] at h
        exact h
      rw [dist_eq_norm, sub_zero]
      have h3 : C * ‖y - x‖ ≤ ε / 2 := by
        have hpos : 0 ≤ ε / (2 * (C + 1)) := div_nonneg hε.le (by linarith)
        calc C * ‖y - x‖ ≤ C * (ε / (2 * (C + 1))) := mul_le_mul_of_nonneg_left hyε.le hCnn
          _ ≤ (C + 1) * (ε / (2 * (C + 1))) := mul_le_mul_of_nonneg_right (by linarith) hpos
          _ = ε / 2 := by
              rw [show (C + 1) * (ε / (2 * (C + 1))) = ε * (C + 1) / (2 * (C + 1)) by ring,
                mul_div_mul_right ε 2 (by linarith : (C + 1) ≠ 0)]
      linarith
  exact HasFTaylorSeriesUpTo.contDiff ⟨hzero, hfderiv, hcont⟩

/-- **The requested statement.**  Note that the hypothesis `ContDiff ℝ ⊤ v` is the *analytic*
level `ω = ⊤`; the proof only uses that `v` is smooth, see `contDiff_flatMul_of_smooth`. -/
theorem contDiff_flatMul {n : ℕ} {k : ℕ} {α : ℝ} {ρ : Fin n → ℝ} (hρ : ∀ j, 0 < ρ j)
    {v : Work.NN.Core.Cn n → ℂ} (hv : ContDiff ℝ ⊤ v)
    (hv0 : ∀ z, (∃ j, ρ j ≤ ‖z j‖) → v z = 0)
    {u : Work.NN.Core.Cn n → ℂ}
    (hu : ContDiffOn ℝ (((k + 1 : ℕ)) : ℕ∞) u (Work.CR.Flat.polydisc 0 ρ))
    (huf : Work.CR.Flat.holderNorm k α u (Work.CR.Flat.polydisc 0 ρ) ≠ ⊤) :
    ContDiff ℝ k (fun z => v z * u z) :=
  contDiff_flatMul_of_smooth hρ (hv.of_le le_top) hv0 hu huf

end Work.NN.Core
