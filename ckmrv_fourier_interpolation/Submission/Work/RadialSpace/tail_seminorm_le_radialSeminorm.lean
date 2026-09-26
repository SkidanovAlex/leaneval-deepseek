import Mathlib
import Submission.Work.RadialSpace.RadialSeminorm
import Submission.Work.RadialSpace.Basic
import Submission.Work.RadialSpace.EvenHalfDeriv
import Submission.Work.RadialSpace.evenHalfDeriv_eq
import Submission.Work.RadialSpace.iteratedDeriv_comp_sqrt
import Submission.Work.RadialSpace.iteratedDeriv_comp_sqrt_pow_mul_le
import Submission.Work.Radial.quad_iteratedFDeriv_bound


/-!
# Tail seminorm estimate for radial smooth functions

For a smooth radial function `F` on `R^n` and natural numbers `k, l`, the weighted
`(k, l)` Schwartz seminorm of `F` is controlled on the region `‖x‖ ≥ 1` by the sum
`radialSeminormSum k l F` of the radial seminorms `⨆ x, ‖x‖ ^ m * ‖D^j g (‖x‖)‖` of the
profile `g = profile F`, for `j ≤ l` and `m ≤ k + l`:

`‖x‖ ^ k * ‖iteratedFDeriv ℝ l F x‖ ≤ C * radialSeminormSum k l F` for `‖x‖ ≥ 1`.

This is the "easy" half of the equivalence between the Schwartz seminorms and the
radial seminorms of a smooth radial function; it is the direction needed to see that
finiteness of the radial seminorms bounds the Schwartz seminorms of `F` away from the
origin.

## Strategy

Write `g = profile F` (smooth and even, with `F x = g ‖x‖ = Ψ (‖x‖ ^ 2)` where
`Ψ s = g (√s)`).  Then

* Faà di Bruno's formula for the composition `Ψ ∘ (‖·‖²)` (`iteratedFDeriv_comp`),
  together with the fact that only the derivatives of order `1` and `2` of `‖·‖²`
  are non-zero, bounds `‖D^l F x‖` by a multiple of `(1 + ‖x‖)^l * ∑_{j ≤ l} ‖∂^j Ψ (‖x‖²)‖`
  (`taylorComp_bound`);
* `∂^j Ψ (u²) = (evenHalfDeriv^[j] g) u`, and the iterated half-derivatives of an even
  smooth function are bounded by the derivatives of `g` (`evenHalfDeriv_iterate_le`,
  proved with Faà di Bruno for `s ↦ g (√s)` and the explicit values of the derivatives
  of `√·`).

## Main result

* `Work.RadialSpace.tail_seminorm_le_radialSeminorm`
-/

open Filter Topology
open scoped ContDiff ENNReal BigOperators

namespace Work.RadialSpace

open LeanEval.Analysis.CKMRVInterpolation

lemma coe_nat_le_smooth (k : ℕ) : (k : ℕ∞ω) ≤ (∞ : ℕ∞ω) := WithTop.coe_le_coe.mpr le_top

lemma norm_iteratedFDeriv_norm_sq_le_sharp {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℝ F]
    {m : ℕ} (hm : 1 ≤ m) (x : F) :
    ‖iteratedFDeriv ℝ m (fun y : F => ‖y‖ ^ 2) x‖ ≤ 2 * (1 + ‖x‖) := by
  rcases eq_or_lt_of_le hm with h | h
  · rw [← h, norm_iteratedFDeriv_one, Work.Radial.fderiv_norm_sq_eq]
    calc ‖(Work.Radial.quadDerivCLM F) x‖ ≤ ‖Work.Radial.quadDerivCLM F‖ * ‖x‖ :=
          (Work.Radial.quadDerivCLM F).le_opNorm x
      _ ≤ 2 * ‖x‖ := mul_le_mul_of_nonneg_right (Work.Radial.norm_quadDerivCLM_le F) (norm_nonneg x)
      _ ≤ 2 * (1 + ‖x‖) := by linarith [norm_nonneg x]
  · have hkey : ‖iteratedFDeriv ℝ m (fun y : F => ‖y‖ ^ 2) x‖
        = ‖iteratedFDeriv ℝ (m - 1) (fun y => Work.Radial.quadDerivCLM F y) x‖ := by
      have hh := norm_iteratedFDeriv_fderiv (𝕜 := ℝ) (f := fun y : F => ‖y‖ ^ 2) (x := x) (n := m - 1)
      rw [Work.Radial.fderiv_norm_sq_eq, Nat.sub_add_cancel (by omega : 1 ≤ m)] at hh
      exact hh.symm
    rw [hkey]
    calc ‖iteratedFDeriv ℝ (m - 1) (fun y => Work.Radial.quadDerivCLM F y) x‖
        ≤ ‖Work.Radial.quadDerivCLM F‖ * (1 + ‖x‖) :=
          Work.Radial.norm_iteratedFDeriv_linearMap_le _ _ _
      _ ≤ 2 * (1 + ‖x‖) :=
          mul_le_mul_of_nonneg_right (Work.Radial.norm_quadDerivCLM_le F) (by positivity)

theorem taylorComp_bound (n : ℕ) (l : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (Ψ : ℝ → ℂ) (x : EuclideanSpace ℝ (Fin n)),
      ContDiffAt ℝ Smooth Ψ (‖x‖ ^ 2) →
      ‖iteratedFDeriv ℝ l (fun y : EuclideanSpace ℝ (Fin n) => Ψ (‖y‖ ^ 2)) x‖ ≤
        C * (1 + ‖x‖) ^ l * ∑ j ∈ Finset.range (l + 1), ‖iteratedDeriv j Ψ (‖x‖ ^ 2)‖ := by
  refine ⟨(Fintype.card (OrderedFinpartition l) : ℝ) * 2 ^ l,
    mul_nonneg (Nat.cast_nonneg _) (by positivity), ?_⟩
  intro Ψ x hΨ
  have hQ : ContDiffAt ℝ Smooth (fun y : EuclideanSpace ℝ (Fin n) => ‖y‖ ^ 2) x := (contDiff_norm_sq ℝ).contDiffAt
  have hcomp := iteratedFDeriv_comp (𝕜 := ℝ) (n := Smooth)
    (f := fun y : EuclideanSpace ℝ (Fin n) => ‖y‖ ^ 2) (g := Ψ) (x := x) hΨ hQ (i := l) (coe_nat_le_smooth l)
  rw [show (fun y : EuclideanSpace ℝ (Fin n) => Ψ (‖y‖ ^ 2)) = (Ψ ∘ (fun y : EuclideanSpace ℝ (Fin n) => ‖y‖ ^ 2)) from rfl, hcomp]
  set q : FormalMultilinearSeries ℝ ℝ ℂ := ftaylorSeries ℝ Ψ (‖x‖ ^ 2) with hq
  set p : FormalMultilinearSeries ℝ (EuclideanSpace ℝ (Fin n)) ℝ := ftaylorSeries ℝ (fun y : EuclideanSpace ℝ (Fin n) => ‖y‖ ^ 2) x with hp
  have h1 : ‖q.taylorComp p l‖ ≤ ∑ c : OrderedFinpartition l, ‖q c.length‖ * ∏ i, ‖p (c.partSize i)‖ := by
    show ‖∑ c : OrderedFinpartition l, q.compAlongOrderedFinpartition p c‖ ≤ ∑ c : OrderedFinpartition l, ‖q c.length‖ * ∏ i, ‖p (c.partSize i)‖
    refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun c _ => ?_)
    exact c.norm_compAlongOrderedFinpartition_le _ _
  have h2 : ∀ c : OrderedFinpartition l, ∏ i, ‖p (c.partSize i)‖ ≤ (2 * (1 + ‖x‖)) ^ l := by
    intro c
    have hle : ∀ i : Fin c.length, ‖p (c.partSize i)‖ ≤ 2 * (1 + ‖x‖) := by
      intro i
      rw [hp]
      exact norm_iteratedFDeriv_norm_sq_le_sharp (c.partSize_pos i) x
    calc ∏ i, ‖p (c.partSize i)‖ ≤ ∏ _i : Fin c.length, (2 * (1 + ‖x‖)) :=
          Finset.prod_le_prod₀ (fun i _ => norm_nonneg _) (fun i _ => hle i)
      _ = (2 * (1 + ‖x‖)) ^ c.length := by rw [Finset.prod_const, Finset.card_univ, Fintype.card_fin]
      _ ≤ (2 * (1 + ‖x‖)) ^ l := pow_le_pow_right₀ (by linarith [norm_nonneg x]) c.length_le
  have h3 : ∑ c : OrderedFinpartition l, ‖q c.length‖ * ∏ i, ‖p (c.partSize i)‖
      ≤ (Fintype.card (OrderedFinpartition l) : ℝ) * (2 * (1 + ‖x‖)) ^ l * ∑ j ∈ Finset.range (l + 1), ‖q j‖ := by
    have hA : (0:ℝ) ≤ (2 * (1 + ‖x‖)) ^ l := by positivity
    have hunif : ∀ c : OrderedFinpartition l, ‖q c.length‖ ≤ ∑ j ∈ Finset.range (l + 1), ‖q j‖ := by
      intro c
      exact Finset.single_le_sum (f := fun j => ‖q j‖) (fun j _ => norm_nonneg _)
        (Finset.mem_range.mpr (Nat.lt_succ_of_le c.length_le))
    calc ∑ c : OrderedFinpartition l, ‖q c.length‖ * ∏ i, ‖p (c.partSize i)‖
        ≤ ∑ c : OrderedFinpartition l, ‖q c.length‖ * (2 * (1 + ‖x‖)) ^ l :=
          Finset.sum_le_sum (fun c _ => mul_le_mul_of_nonneg_left (h2 c) (norm_nonneg _))
      _ = (2 * (1 + ‖x‖)) ^ l * ∑ c : OrderedFinpartition l, ‖q c.length‖ := by
          rw [Finset.mul_sum]
          exact Finset.sum_congr rfl (fun c _ => mul_comm _ _)
      _ ≤ (2 * (1 + ‖x‖)) ^ l * ((Fintype.card (OrderedFinpartition l) : ℝ) * ∑ j ∈ Finset.range (l + 1), ‖q j‖) := by
          apply mul_le_mul_of_nonneg_left _ hA
          calc ∑ c : OrderedFinpartition l, ‖q c.length‖
              ≤ ∑ _c : OrderedFinpartition l, ∑ j ∈ Finset.range (l + 1), ‖q j‖ :=
                Finset.sum_le_sum (fun c _ => hunif c)
            _ = (Fintype.card (OrderedFinpartition l) : ℝ) * ∑ j ∈ Finset.range (l + 1), ‖q j‖ := by
                rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
      _ = (Fintype.card (OrderedFinpartition l) : ℝ) * (2 * (1 + ‖x‖)) ^ l * ∑ j ∈ Finset.range (l + 1), ‖q j‖ := by
          ring
  have hEq : ∑ j ∈ Finset.range (l + 1), ‖q j‖ = ∑ j ∈ Finset.range (l + 1), ‖iteratedDeriv j Ψ (‖x‖ ^ 2)‖ := by
    apply Finset.sum_congr rfl
    intro j _
    rw [hq]
    exact norm_iteratedFDeriv_eq_norm_iteratedDeriv
  calc ‖q.taylorComp p l‖
      ≤ ∑ c : OrderedFinpartition l, ‖q c.length‖ * ∏ i, ‖p (c.partSize i)‖ := h1
    _ ≤ (Fintype.card (OrderedFinpartition l) : ℝ) * (2 * (1 + ‖x‖)) ^ l * ∑ j ∈ Finset.range (l + 1), ‖q j‖ := h3
    _ = (Fintype.card (OrderedFinpartition l) : ℝ) * 2 ^ l * (1 + ‖x‖) ^ l *
          ∑ j ∈ Finset.range (l + 1), ‖iteratedDeriv j Ψ (‖x‖ ^ 2)‖ := by
        rw [hEq, mul_pow]
        ring

theorem evenHalfDeriv_iterate_le {g : ℝ → ℂ} (hg : ContDiff ℝ Smooth g) (he : Function.Even g)
    (j : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ u : ℝ, 1 ≤ u →
      ‖(evenHalfDeriv^[j]) g u‖ ≤ C * ∑ i ∈ Finset.range (j + 1), ‖iteratedDeriv i g u‖ := by
  set B : ℝ := ∑ k ∈ Finset.range (j + 1), |sqrtCoeff k| with hB
  have hB0 : 0 ≤ B := hB ▸ Finset.sum_nonneg (fun k _ => abs_nonneg (sqrtCoeff k))
  have hB1 : 1 ≤ B := by
    have hmem : 0 ∈ Finset.range (j+1) := Finset.mem_range.mpr (Nat.succ_pos j)
    have hle := Finset.single_le_sum (f := fun k => |sqrtCoeff k|) (fun k _ => abs_nonneg (sqrtCoeff k)) hmem
    rw [hB]
    simpa [sqrtCoeff_zero] using hle
  refine ⟨(Fintype.card (OrderedFinpartition j) : ℝ) * B ^ j,
    mul_nonneg (Nat.cast_nonneg _) (by positivity), ?_⟩
  intro u hu
  have hu0 : 0 < u := lt_of_lt_of_le zero_lt_one hu
  have hu2 : (0:ℝ) < u ^ 2 := by positivity
  have hu21 : (1:ℝ) ≤ u ^ 2 := by nlinarith
  have h1 : (evenHalfDeriv^[j]) g u = iteratedDeriv j (fun s => g (Real.sqrt s)) (u ^ 2) := by
    have h := (iteratedDeriv_comp_sqrt hg he hu2 j).symm
    rwa [Real.sqrt_sq (le_of_lt hu0)] at h
  rw [h1]
  have hfb := iteratedDeriv_scomp_eq_sum_orderedFinpartition (𝕜 := ℝ) (g := g)
    (f := fun s : ℝ => Real.sqrt s) (x := u ^ 2) (n := Smooth) (i := j)
    (hg.contDiffAt) (Real.contDiffAt_sqrt (ne_of_gt hu2)) (coe_nat_le_smooth j)
  rw [show iteratedDeriv j (fun s => g (Real.sqrt s)) (u^2)
      = ∑ c : OrderedFinpartition j, (∏ i, iteratedDeriv (c.partSize i) (fun s : ℝ => Real.sqrt s) (u^2)) •
          iteratedDeriv c.length g (Real.sqrt (u^2)) from hfb]
  have hterm : ∀ c : OrderedFinpartition j,
      ‖(∏ i, iteratedDeriv (c.partSize i) (fun s : ℝ => Real.sqrt s) (u^2)) •
          iteratedDeriv c.length g (Real.sqrt (u^2))‖
        ≤ B^j * ‖iteratedDeriv c.length g u‖ := by
    intro c
    have hprod : ∏ i, ‖iteratedDeriv (c.partSize i) (fun s : ℝ => Real.sqrt s) (u^2)‖ ≤ B^j := by
      have heach : ∀ i : Fin c.length, ‖iteratedDeriv (c.partSize i) (fun s : ℝ => Real.sqrt s) (u^2)‖ ≤ B := by
        intro i
        refine (abs_iteratedDeriv_sqrt_le (c.partSize i) (c.partSize_pos i) hu21).trans ?_
        rw [hB]
        exact Finset.single_le_sum (fun k _ => abs_nonneg (sqrtCoeff k))
          (Finset.mem_range.mpr (Nat.lt_succ_of_le (c.partSize_le i)))
      calc ∏ i, ‖iteratedDeriv (c.partSize i) (fun s : ℝ => Real.sqrt s) (u^2)‖
          ≤ ∏ _i : Fin c.length, B := Finset.prod_le_prod₀ (fun i _ => norm_nonneg _) (fun i _ => heach i)
        _ = B ^ c.length := by rw [Finset.prod_const, Finset.card_univ, Fintype.card_fin]
        _ ≤ B ^ j := pow_le_pow_right₀ hB1 c.length_le
    have hnm : ‖(∏ i, iteratedDeriv (c.partSize i) (fun s : ℝ => Real.sqrt s) (u^2))‖
        = ∏ i, ‖iteratedDeriv (c.partSize i) (fun s : ℝ => Real.sqrt s) (u^2)‖ :=
      norm_prod _ _
    have hsm : ‖(∏ i, iteratedDeriv (c.partSize i) (fun s : ℝ => Real.sqrt s) (u^2)) •
          iteratedDeriv c.length g (Real.sqrt (u^2))‖
        = ‖(∏ i, iteratedDeriv (c.partSize i) (fun s : ℝ => Real.sqrt s) (u^2))‖ *
          ‖iteratedDeriv c.length g (Real.sqrt (u^2))‖ := norm_smul _ _
    rw [hsm, hnm, Real.sqrt_sq (le_of_lt hu0)]
    exact mul_le_mul_of_nonneg_right hprod (norm_nonneg _)
  have hunif : ∀ c : OrderedFinpartition j, ‖iteratedDeriv c.length g u‖ ≤
      ∑ i ∈ Finset.range (j + 1), ‖iteratedDeriv i g u‖ := by
    intro c
    exact Finset.single_le_sum (f := fun i => ‖iteratedDeriv i g u‖) (fun i _ => norm_nonneg _)
      (Finset.mem_range.mpr (Nat.lt_succ_of_le c.length_le))
  calc ‖∑ c : OrderedFinpartition j, (∏ i, iteratedDeriv (c.partSize i) (fun s : ℝ => Real.sqrt s) (u^2)) •
        iteratedDeriv c.length g (Real.sqrt (u^2))‖
      ≤ ∑ c : OrderedFinpartition j, ‖(∏ i, iteratedDeriv (c.partSize i) (fun s : ℝ => Real.sqrt s) (u^2)) •
          iteratedDeriv c.length g (Real.sqrt (u^2))‖ := norm_sum_le _ _
    _ ≤ ∑ c : OrderedFinpartition j, B^j * ‖iteratedDeriv c.length g u‖ :=
        Finset.sum_le_sum (fun c _ => hterm c)
    _ = B^j * ∑ c : OrderedFinpartition j, ‖iteratedDeriv c.length g u‖ := by
        rw [Finset.mul_sum]
    _ ≤ B^j * ((Fintype.card (OrderedFinpartition j) : ℝ) * ∑ i ∈ Finset.range (j + 1), ‖iteratedDeriv i g u‖) := by
        apply mul_le_mul_of_nonneg_left _ (by positivity)
        calc ∑ c : OrderedFinpartition j, ‖iteratedDeriv c.length g u‖
            ≤ ∑ _c : OrderedFinpartition j, ∑ i ∈ Finset.range (j + 1), ‖iteratedDeriv i g u‖ :=
              Finset.sum_le_sum (fun c _ => hunif c)
          _ = (Fintype.card (OrderedFinpartition j) : ℝ) * ∑ i ∈ Finset.range (j + 1), ‖iteratedDeriv i g u‖ := by
              rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
    _ = (Fintype.card (OrderedFinpartition j) : ℝ) * B ^ j * ∑ i ∈ Finset.range (j + 1), ‖iteratedDeriv i g u‖ := by
        ring

lemma profile_contDiff {n : ℕ} [NeZero n] {F : EuclideanSpace ℝ (Fin n) → ℂ}
    (hF : ContDiff ℝ Smooth F) : ContDiff ℝ Smooth (profile F) := by
  have h : profile F = F ∘ (⇑(realInclCLM n)) := by
    funext r; rw [Function.comp_apply, realInclCLM_apply]; rfl
  rw [h]
  exact hF.comp (realInclCLM n).contDiff

theorem tail_seminorm_le_radialSeminorm {n : ℕ} [NeZero n] (F : EuclideanSpace ℝ (Fin n) → ℂ)
    (hF : ContDiff ℝ Work.RadialSpace.Smooth F) (hr : LeanEval.Analysis.CKMRVInterpolation.Radial F)
    (k l : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ x : EuclideanSpace ℝ (Fin n), 1 ≤ ‖x‖ →
      ENNReal.ofReal (‖x‖ ^ k * ‖iteratedFDeriv ℝ l F x‖) ≤
        ENNReal.ofReal C * (Work.RadialSpace.radialSeminormSum k l F + 1) := by
  have hg : ContDiff ℝ Smooth (profile F) := profile_contDiff hF
  have hge : Function.Even (profile F) := profile_even hr
  obtain ⟨CA, hCA0, hCA⟩ := taylorComp_bound n l
  choose CB hCB using fun j => evenHalfDeriv_iterate_le hg hge j
  set KB : ℝ := ∑ j ∈ Finset.range (l + 1), CB j with hKBdef
  have hKB0 : 0 ≤ KB := by rw [hKBdef]; exact Finset.sum_nonneg (fun j _ => (hCB j).1)
  have hCBle : ∀ j ∈ Finset.range (l+1), CB j ≤ KB := by
    intro j hj
    rw [hKBdef]
    exact Finset.single_le_sum (f := CB) (fun i _ => (hCB i).1) hj
  refine ⟨max 1 (CA * (l+1) * KB * 2^l), le_trans zero_le_one (le_max_left _ _), ?_⟩
  intro x hx
  have hx0 : 0 < ‖x‖ := lt_of_lt_of_le zero_lt_one hx
  have hpsi : ContDiffAt ℝ Smooth (fun s : ℝ => profile F (Real.sqrt s)) (‖x‖ ^ 2) := by
    have h1 : ContDiffAt ℝ Smooth (fun s : ℝ => Real.sqrt s) (‖x‖ ^ 2) :=
      Real.contDiffAt_sqrt (by positivity : (‖x‖ ^ 2) ≠ 0)
    have h2 := (hg.contDiffAt).comp (‖x‖ ^ 2) h1
    simpa only [Function.comp_def] using h2
  have hFpsi : F = fun y : EuclideanSpace ℝ (Fin n) => profile F (Real.sqrt (‖y‖ ^ 2)) := by
    funext y
    rw [Real.sqrt_sq (norm_nonneg y)]
    exact profile_eq_of_radial hr y
  have hA : ‖iteratedFDeriv ℝ l F x‖ ≤ CA * (1 + ‖x‖) ^ l *
      ∑ j ∈ Finset.range (l + 1), ‖iteratedDeriv j (fun s : ℝ => profile F (Real.sqrt s)) (‖x‖ ^ 2)‖ := by
    have h := hCA (fun s : ℝ => profile F (Real.sqrt s)) x hpsi
    rw [← hFpsi] at h
    exact h
  have hsum : ∑ j ∈ Finset.range (l + 1), ‖iteratedDeriv j (fun s : ℝ => profile F (Real.sqrt s)) (‖x‖ ^ 2)‖
      ≤ (l + 1) * KB * ∑ i ∈ Finset.range (l + 1), ‖iteratedDeriv i (profile F) ‖x‖‖ := by
    have heach : ∀ j ∈ Finset.range (l + 1),
        ‖iteratedDeriv j (fun s : ℝ => profile F (Real.sqrt s)) (‖x‖ ^ 2)‖ ≤
          KB * ∑ i ∈ Finset.range (l + 1), ‖iteratedDeriv i (profile F) ‖x‖‖ := by
      intro j hj
      have hjl : j ≤ l := Nat.lt_succ_iff.mp (Finset.mem_range.mp hj)
      have h1 : ‖iteratedDeriv j (fun s : ℝ => profile F (Real.sqrt s)) (‖x‖ ^ 2)‖
          = ‖(evenHalfDeriv^[j]) (profile F) ‖x‖‖ := by
        have h := iteratedDeriv_comp_sqrt hg hge (by positivity : 0 < ‖x‖ ^ 2) j
        rw [Real.sqrt_sq (norm_nonneg x)] at h
        exact congrArg norm h
      rw [h1]
      refine ((hCB j).2 ‖x‖ hx).trans ?_
      calc CB j * ∑ i ∈ Finset.range (j + 1), ‖iteratedDeriv i (profile F) ‖x‖‖
          ≤ KB * ∑ i ∈ Finset.range (j + 1), ‖iteratedDeriv i (profile F) ‖x‖‖ :=
            mul_le_mul_of_nonneg_right (hCBle j hj) (Finset.sum_nonneg (fun i _ => norm_nonneg _))
        _ ≤ KB * ∑ i ∈ Finset.range (l + 1), ‖iteratedDeriv i (profile F) ‖x‖‖ :=
            mul_le_mul_of_nonneg_left
              (Finset.sum_le_sum_of_subset_of_nonneg (Finset.range_mono (Nat.succ_le_succ hjl))
                (fun i _ _ => norm_nonneg _)) hKB0
    calc ∑ j ∈ Finset.range (l + 1), ‖iteratedDeriv j (fun s : ℝ => profile F (Real.sqrt s)) (‖x‖ ^ 2)‖
        ≤ ∑ j ∈ Finset.range (l + 1), KB * ∑ i ∈ Finset.range (l + 1), ‖iteratedDeriv i (profile F) ‖x‖‖ :=
          Finset.sum_le_sum heach
      _ = (l + 1) * KB * ∑ i ∈ Finset.range (l + 1), ‖iteratedDeriv i (profile F) ‖x‖‖ := by
          rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
          push_cast
          ring
  have hpow : ‖x‖ ^ k * (1 + ‖x‖) ^ l ≤ 2 ^ l * ‖x‖ ^ (k + l) := by
    have h1 : 1 + ‖x‖ ≤ 2 * ‖x‖ := by linarith
    calc ‖x‖ ^ k * (1 + ‖x‖) ^ l ≤ ‖x‖ ^ k * (2 * ‖x‖) ^ l :=
          mul_le_mul_of_nonneg_left
            (pow_le_pow_left₀ (by linarith [norm_nonneg x]) h1 l) (pow_nonneg (norm_nonneg x) k)
      _ = 2 ^ l * ‖x‖ ^ (k + l) := by rw [mul_pow]; ring
  have hS2 : (0:ℝ) ≤ ∑ i ∈ Finset.range (l + 1), ‖iteratedDeriv i (profile F) ‖x‖‖ :=
    Finset.sum_nonneg (fun i _ => norm_nonneg _)
  have hK0 : (0:ℝ) ≤ CA * (l+1) * KB * 2^l :=
    mul_nonneg (mul_nonneg (mul_nonneg hCA0 (by positivity)) hKB0) (by positivity)
  have hreal : ‖x‖ ^ k * ‖iteratedFDeriv ℝ l F x‖ ≤
      (CA * (l+1) * KB * 2^l) * ∑ i ∈ Finset.range (l + 1), (‖x‖ ^ (k + l) * ‖iteratedDeriv i (profile F) ‖x‖‖) := by
    calc ‖x‖ ^ k * ‖iteratedFDeriv ℝ l F x‖
        ≤ ‖x‖ ^ k * (CA * (1 + ‖x‖) ^ l * ((l + 1) * KB * ∑ i ∈ Finset.range (l + 1), ‖iteratedDeriv i (profile F) ‖x‖‖)) := by
          apply mul_le_mul_of_nonneg_left _ (pow_nonneg (norm_nonneg x) k)
          calc ‖iteratedFDeriv ℝ l F x‖
              ≤ CA * (1 + ‖x‖) ^ l * ∑ j ∈ Finset.range (l + 1), ‖iteratedDeriv j (fun s : ℝ => profile F (Real.sqrt s)) (‖x‖ ^ 2)‖ := hA
            _ ≤ CA * (1 + ‖x‖) ^ l * ((l + 1) * KB * ∑ i ∈ Finset.range (l + 1), ‖iteratedDeriv i (profile F) ‖x‖‖) := by
                apply mul_le_mul_of_nonneg_left hsum
                exact mul_nonneg hCA0 (by positivity)
      _ = CA * (l+1) * KB * (‖x‖ ^ k * (1 + ‖x‖) ^ l) * (∑ i ∈ Finset.range (l + 1), ‖iteratedDeriv i (profile F) ‖x‖‖) := by ring
      _ ≤ CA * (l+1) * KB * (2 ^ l * ‖x‖ ^ (k + l)) * (∑ i ∈ Finset.range (l + 1), ‖iteratedDeriv i (profile F) ‖x‖‖) := by
          apply mul_le_mul_of_nonneg_right _ hS2
          exact mul_le_mul_of_nonneg_left hpow (mul_nonneg (mul_nonneg hCA0 (by positivity)) hKB0)
      _ = (CA * (l+1) * KB * 2^l) * ∑ i ∈ Finset.range (l + 1), (‖x‖ ^ (k + l) * ‖iteratedDeriv i (profile F) ‖x‖‖) := by
          rw [← Finset.mul_sum]
          ring
  have hstep : ENNReal.ofReal (∑ i ∈ Finset.range (l + 1), (‖x‖ ^ (k + l) * ‖iteratedDeriv i (profile F) ‖x‖‖))
      ≤ radialSeminormSum k l F := by
    have hstep' : ENNReal.ofReal (∑ i ∈ Finset.range (l + 1), (‖x‖ ^ (k + l) * ‖iteratedDeriv i (profile F) ‖x‖‖))
        ≤ ∑ j ∈ Finset.range (l + 1), ∑ m ∈ Finset.range (k + l + 1), radialSeminorm m j F := by
      rw [ENNReal.ofReal_sum_of_nonneg (fun i _ => mul_nonneg (pow_nonneg (norm_nonneg x) _) (norm_nonneg _))]
      calc ∑ i ∈ Finset.range (l + 1), ENNReal.ofReal (‖x‖ ^ (k + l) * ‖iteratedDeriv i (profile F) ‖x‖‖)
          ≤ ∑ i ∈ Finset.range (l + 1), radialSeminorm (k + l) i F := by
            refine Finset.sum_le_sum (fun i hi => ?_)
            have key1 : ENNReal.ofReal (‖x‖ ^ (k + l) * ‖iteratedDeriv i (profile F) ‖x‖‖)
                = ENNReal.ofReal (‖realIncl (n := n) ‖x‖‖ ^ (k + l) * ‖radialDerivPow i F (realIncl (n := n) ‖x‖)‖) := by
              rw [radialDerivPow_apply, Work.Sampling.realIncl_norm, abs_of_nonneg (norm_nonneg x)]
            rw [key1]
            exact ofReal_le_radialSeminorm (k + l) i F (realIncl ‖x‖)
        _ ≤ ∑ j ∈ Finset.range (l + 1), ∑ m ∈ Finset.range (k + l + 1), radialSeminorm m j F := by
            refine Finset.sum_le_sum (f := fun i => radialSeminorm (k + l) i F)
              (g := fun j => ∑ m ∈ Finset.range (k + l + 1), radialSeminorm m j F) ?_
            intro i _
            exact Finset.single_le_sum (f := fun m => radialSeminorm m i F) (fun m _ => bot_le)
              (Finset.mem_range.mpr (by omega : k + l < k + l + 1))
    exact hstep'
  have hfin : ENNReal.ofReal (‖x‖ ^ k * ‖iteratedFDeriv ℝ l F x‖) ≤
      ENNReal.ofReal (CA * (l+1) * KB * 2^l) * radialSeminormSum k l F := by
    refine (ENNReal.ofReal_le_ofReal hreal).trans ?_
    rw [ENNReal.ofReal_mul hK0]
    exact mul_le_mul_right hstep _
  calc ENNReal.ofReal (‖x‖ ^ k * ‖iteratedFDeriv ℝ l F x‖)
      ≤ ENNReal.ofReal (CA * (l+1) * KB * 2^l) * radialSeminormSum k l F := hfin
    _ ≤ ENNReal.ofReal (max 1 (CA * (l+1) * KB * 2^l)) * radialSeminormSum k l F :=
        mul_le_mul_left (ENNReal.ofReal_le_ofReal (le_max_right _ _)) _
    _ ≤ ENNReal.ofReal (max 1 (CA * (l+1) * KB * 2^l)) * (radialSeminormSum k l F + 1) :=
        mul_le_mul_right (self_le_add_right _ _) _

end Work.RadialSpace
