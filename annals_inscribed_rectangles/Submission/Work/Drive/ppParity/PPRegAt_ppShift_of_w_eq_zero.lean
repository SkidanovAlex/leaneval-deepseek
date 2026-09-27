import Mathlib
import Submission.Work.Drive.ppParity.Defs
import Submission.Work.Drive.ppParity.Shift
import Submission.Work.Drive.ppParity.partial_fderiv_tendsto
import Submission.Work.Drive.ppParity.contDiffAt_chr_ppShift
import Submission.Work.Drive.ppParity.fderiv_pair44_comp
import Submission.Work.Drive.ppParity.surjective_domRestrict_open

/-!
# The pointwise transfer of pair regularity at a vanishing weight

This is the honest (non-collar) form of the S3 transfer of the lead's residency plan
(`Submission/Work/Drive/NOTES_LEAD_residency.md`): at a point `x` of the nine-box where the *weight*
vanishes, `w (ftS x) = 0`, the intrinsically perturbed pair chains

> `ppShift Ξ w (unpackFst τ) E`, `ppShift Ξ w (unpackSnd τ) E'`

agree with the base chains *at the two chart centres of `x`* (because `w (ftS x) • τ = 0` and
`Ξ 0 = id`), and differ from them — near `x`, uniformly in small `τ` — by a map that is smooth and
`C¹`-small.  Hence the two clauses of `PPRegAt` at `x` transfer: surjectivity of the Fréchet
derivative is an open condition among continuous linear maps with finite-dimensional target, and the
combinatorial part of the boundary clause is a statement about `x` alone.

The proof splits the pair map of the perturbed family as

> `Pmap τ = Bmap + Dmap τ`, where `Dmap τ = pair44 (A τ − A 0) (A' τ − A' 0)`

is the difference of the two perturbed charted chains; the base map `Bmap` is differentiable at `x`
(since its Fréchet derivative is surjective onto the non-trivial `ℝ⁸`), so the derivative of the
perturbed map is `fderiv Bmap x + fderiv (Dmap τ) x` and the perturbation is small.

Note that no hypothesis that `x` is a *meet* is needed: the blocks `chr c (V (ftY ·))` and
`chr c' (W (ftZ ·))` are never differentiated, they cancel in the difference.
-/

namespace Work.Drive.ppParity

open scoped Manifold ContDiff Topology
open Manifold Set Filter

set_option backward.isDefEq.respectTransparency false
set_option linter.unusedVariables false

noncomputable section

local notation "Ctop" => ((⊤ : ℕ∞) : WithTop ℕ∞)


/-! ## Small perturbations of a surjective continuous linear map

Surjectivity onto a finite-dimensional space is an open condition in the operator norm: the standard
right inverse argument (a linear right inverse of a surjective map onto a finite-dimensional space is
automatically continuous, and `1 + S ∘ R` is a unit for `‖S ∘ R‖ < 1` by the Neumann series). -/
private lemma exists_pos_norm_lt_surjective_add
    {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
    (L : E →L[ℝ] F) (hL : Function.Surjective L) :
    ∃ ε : ℝ, 0 < ε ∧ ∀ S : E →L[ℝ] F, ‖S‖ < ε → Function.Surjective (L + S) := by
  classical
  obtain ⟨R, hR⟩ := LinearMap.exists_rightInverse_of_surjective L.toLinearMap
    (LinearMap.range_eq_top.2 hL)
  let Rc : F →L[ℝ] E := R.toContinuousLinearMap
  have hRc : ∀ w : F, L (Rc w) = w := by
    intro w
    have h := congrArg (fun f : F →ₗ[ℝ] F => f w) hR
    simpa [Rc] using h
  refine ⟨(1 + ‖Rc‖)⁻¹, inv_pos.mpr (by positivity), ?_⟩
  intro S hS
  have hST : ‖S.comp Rc‖ < 1 := by
    refine lt_of_le_of_lt (ContinuousLinearMap.opNorm_comp_le S Rc) ?_
    rcases eq_or_lt_of_le (norm_nonneg Rc) with h0 | h0
    · rw [← h0, mul_zero]; norm_num
    · have h3 : (1 + ‖Rc‖)⁻¹ * ‖Rc‖ < 1 := by
        have hb : (0 : ℝ) < 1 + ‖Rc‖ := by positivity
        have h4 := mul_lt_mul_of_pos_left (by linarith : ‖Rc‖ < 1 + ‖Rc‖) (inv_pos.mpr hb)
        rwa [inv_mul_cancel₀ (ne_of_gt hb)] at h4
      exact lt_of_lt_of_le (mul_lt_mul_of_pos_right hS h0) h3.le
  have hunit : IsUnit (1 + S.comp Rc) := by
    have h := isUnit_one_sub_of_norm_lt_one (x := -(S.comp Rc)) (by simpa using hST)
    simpa [sub_neg_eq_add] using h
  obtain ⟨u, hu⟩ := hunit
  intro w
  have hsurjT : ∃ y, (1 + S.comp Rc) y = w := by
    refine ⟨(u.inv : F →L[ℝ] F) w, ?_⟩
    have h1 : ((1 + S.comp Rc) * (u.inv : F →L[ℝ] F) = 1) := by
      rw [← hu]; exact Units.mul_inv u
    have h := congrArg (fun f : F →L[ℝ] F => f w) h1
    simpa [mul_apply_eq_comp] using h
  obtain ⟨y, hy⟩ := hsurjT
  refine ⟨Rc y, ?_⟩
  have hy' : y + (S.comp Rc) y = w := by simpa using hy
  show L (Rc y) + S (Rc y) = w
  rw [hRc y]
  exact hy'

/-! ## Additivity of the packing `pair44` -/

@[simp] lemma ppPair44_add (a b c d : EuclideanSpace ℝ (Fin 4)) :
    pair44 a b + pair44 c d = pair44 (a + c) (b + d) := by
  ext i
  fin_cases i <;> simp [pair44, WithLp.ofLp_toLp]

@[simp] lemma ppPair44_sub (a b c d : EuclideanSpace ℝ (Fin 4)) :
    pair44 a b - pair44 c d = pair44 (a - c) (b - d) := by
  ext i
  fin_cases i <;> simp [pair44, WithLp.ofLp_toLp]

/-! ## The block smallness lemma

The charted shifted chain `y ↦ chr c (ppShift Ξ w (B τ) E (ftS y) (ftU y))` is, for small `τ`,
differentiable at `x` and its Fréchet derivative differs from that of the base chain
`y ↦ chr c (E (ftS y) (ftU y))` by less than any prescribed `ε`.  This is the combination of the
joint smoothness of the two-variable map `(τ, y) ↦ chr c (ppShift Ξ w (B τ) E (ftS y) (ftU y))`
(delegated smoothness lemma) with the continuity of its partial derivative in `τ` (delegated
abstract lemma). -/

private lemma exists_delta_block_diff_lt
    {M : Type*} [TopologicalSpace M] [T2Space M]
    [ChartedSpace (EuclideanSpace ℝ (Fin 4)) M]
    [IsManifold (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 4))) Ctop M]
    {Ξ : EuclideanSpace ℝ (Fin 4) → M → M}
    (hΞ : ContMDiff ((modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 4))).prod
        (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 4))))
      (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 4))) Ctop
      (fun q : EuclideanSpace ℝ (Fin 4) × M => Ξ q.1 q.2))
    (hΞ0 : ∀ p : M, Ξ 0 p = p)
    {w : ℝ → ℝ} (hw : ContDiff ℝ Ctop w)
    {E : ℝ → EuclideanSpace ℝ (Fin 2) → M}
    (hE : ContMDiff (modelWithCornersSelf ℝ (ℝ × EuclideanSpace ℝ (Fin 2)))
      (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 4))) Ctop (Function.uncurry E))
    (B : EuclideanSpace ℝ (Fin 8) →L[ℝ] EuclideanSpace ℝ (Fin 4))
    {c : M} {x : EuclideanSpace ℝ (Fin 9)}
    (hsrc : E (ftS x) (ftU x) ∈ (chr c).source)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ τ : EuclideanSpace ℝ (Fin 8), ‖τ‖ < δ →
      DifferentiableAt ℝ (fun y : EuclideanSpace ℝ (Fin 9) =>
          chr c (ppShift Ξ w (B τ) E (ftS y) (ftU y))) x ∧
      DifferentiableAt ℝ (fun y : EuclideanSpace ℝ (Fin 9) =>
          chr c (E (ftS y) (ftU y))) x ∧
      ‖fderiv ℝ (fun y : EuclideanSpace ℝ (Fin 9) =>
          chr c (ppShift Ξ w (B τ) E (ftS y) (ftU y))) x -
       fderiv ℝ (fun y : EuclideanSpace ℝ (Fin 9) =>
          chr c (E (ftS y) (ftU y))) x‖ < ε := by
  classical
  set F : EuclideanSpace ℝ (Fin 8) × EuclideanSpace ℝ (Fin 9) → EuclideanSpace ℝ (Fin 4) :=
    fun q => chr c (ppShift Ξ w (B q.1) E (ftS q.2) (ftU q.2)) with hF
  have hFsm : ContDiffAt ℝ Ctop F (0, x) :=
    contDiffAt_chr_ppShift (Ξ := Ξ) hΞ hΞ0 hw hE B hsrc
  obtain ⟨δ, hδ, hprop⟩ := partial_fderiv_tendsto (F := F) hFsm ε hε
  have h0 : (fun y : EuclideanSpace ℝ (Fin 9) => F (0, y))
      = fun y : EuclideanSpace ℝ (Fin 9) => chr c (E (ftS y) (ftU y)) := by
    funext y
    simp only [hF, ppShift, ContinuousLinearMap.map_zero, smul_zero, hΞ0]
  refine ⟨δ, hδ, fun τ hτ => ?_⟩
  obtain ⟨hd1, hd2, hnorm⟩ := hprop τ (by simpa using hτ)
  refine ⟨?_, ?_, ?_⟩
  · simpa only [hF] using hd1
  · rw [h0] at hd2
    exact hd2
  · rw [h0] at hnorm
    exact hnorm

/-! ## The target -/

theorem PPRegAt_ppShift_of_w_eq_zero
    {M : Type*} [TopologicalSpace M] [T2Space M]
    [ChartedSpace (EuclideanSpace ℝ (Fin 4)) M]
    [IsManifold (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 4))) ((⊤ : ℕ∞) : WithTop ℕ∞) M]
    {E E' : ℝ → EuclideanSpace ℝ (Fin 2) → M} {V W : EuclideanSpace ℝ (Fin 3) → M}
    (hE : ContMDiff (modelWithCornersSelf ℝ (ℝ × EuclideanSpace ℝ (Fin 2)))
      (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 4))) ((⊤ : ℕ∞) : WithTop ℕ∞)
      (Function.uncurry E))
    (hE' : ContMDiff (modelWithCornersSelf ℝ (ℝ × EuclideanSpace ℝ (Fin 2)))
      (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 4))) ((⊤ : ℕ∞) : WithTop ℕ∞)
      (Function.uncurry E'))
    (hV : ContMDiff (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 3)))
      (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 4))) ((⊤ : ℕ∞) : WithTop ℕ∞) V)
    (hW : ContMDiff (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 3)))
      (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 4))) ((⊤ : ℕ∞) : WithTop ℕ∞) W)
    (Ξ : EuclideanSpace ℝ (Fin 4) → M → M)
    (hΞ : ContMDiff ((modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 4))).prod
        (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 4))))
      (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 4))) ((⊤ : ℕ∞) : WithTop ℕ∞)
      (fun q : EuclideanSpace ℝ (Fin 4) × M => Ξ q.1 q.2))
    (hΞ0 : ∀ p : M, Ξ 0 p = p)
    (w : ℝ → ℝ) (hw : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) w)
    {x : EuclideanSpace ℝ (Fin 9)} (hx : x ∈ Submission.Drive.unitBox 8)
    (hwm : w (Work.Drive.ftS x) = 0) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ τ : EuclideanSpace ℝ (Fin 8), ‖τ‖ < δ →
      (Work.Drive.PPRegAt E E' V W x →
        Work.Drive.PPRegAt (Work.Drive.ppShift Ξ w (Work.Drive.unpackFst τ) E)
          (Work.Drive.ppShift Ξ w (Work.Drive.unpackSnd τ) E') V W x) := by
  classical
  by_cases hreg : PPRegAt E E' V W x
  · -- the chart values of the perturbed chains at `x` are the base ones
    have hPS : ∀ τ : EuclideanSpace ℝ (Fin 8),
        ppShift Ξ w (unpackFst τ) E (ftS x) (ftU x) = E (ftS x) (ftU x) := by
      intro τ
      simp only [ppShift, hwm, zero_smul, hΞ0]
    have hPS' : ∀ τ : EuclideanSpace ℝ (Fin 8),
        ppShift Ξ w (unpackSnd τ) E' (ftS x) (ftU x) = E' (ftS x) (ftU x) := by
      intro τ
      simp only [ppShift, hwm, zero_smul, hΞ0]
    -- the maps
    set Bmap : EuclideanSpace ℝ (Fin 9) → EuclideanSpace ℝ (Fin 8) :=
      ppDiff (E (ftS x) (ftU x)) (E' (ftS x) (ftU x)) E E' V W with hBmap
    set A : EuclideanSpace ℝ (Fin 8) → EuclideanSpace ℝ (Fin 9) → EuclideanSpace ℝ (Fin 4) :=
      fun τ y => chr (E (ftS x) (ftU x)) (Ξ (w (ftS y) • unpackFst τ) (E (ftS y) (ftU y)))
      with hA
    set A' : EuclideanSpace ℝ (Fin 8) → EuclideanSpace ℝ (Fin 9) → EuclideanSpace ℝ (Fin 4) :=
      fun τ y => chr (E' (ftS x) (ftU x)) (Ξ (w (ftS y) • unpackSnd τ) (E' (ftS y) (ftU y)))
      with hA'
    set A0 : EuclideanSpace ℝ (Fin 9) → EuclideanSpace ℝ (Fin 4) :=
      fun y => chr (E (ftS x) (ftU x)) (E (ftS y) (ftU y)) with hA0
    set A0' : EuclideanSpace ℝ (Fin 9) → EuclideanSpace ℝ (Fin 4) :=
      fun y => chr (E' (ftS x) (ftU x)) (E' (ftS y) (ftU y)) with hA0'
    set Dmap : EuclideanSpace ℝ (Fin 8) → EuclideanSpace ℝ (Fin 9) → EuclideanSpace ℝ (Fin 8) :=
      fun τ y => pair44 (A τ y - A0 y) (A' τ y - A0' y) with hDmap
    set Pmap : EuclideanSpace ℝ (Fin 8) → EuclideanSpace ℝ (Fin 9) → EuclideanSpace ℝ (Fin 8) :=
      fun τ => ppDiff (E (ftS x) (ftU x)) (E' (ftS x) (ftU x))
        (ppShift Ξ w (unpackFst τ) E) (ppShift Ξ w (unpackSnd τ) E') V W with hPmap
    -- the base derivative is surjective, hence the base map is differentiable
    have hL : Function.Surjective (fderiv ℝ Bmap x) := hreg.1
    have hBdiff : DifferentiableAt ℝ Bmap x := by
      by_contra hcon
      have h0 : fderiv ℝ Bmap x = 0 := fderiv_zero_of_not_differentiableAt hcon
      have hsurj : Function.Surjective (0 : EuclideanSpace ℝ (Fin 9) →L[ℝ] EuclideanSpace ℝ (Fin 8)) :=
        h0 ▸ hL
      have hzero : ∀ y : EuclideanSpace ℝ (Fin 8), y = 0 := by
        intro y
        obtain ⟨v, hv⟩ := hsurj y
        simpa using hv.symm
      have hsub : Subsingleton (EuclideanSpace ℝ (Fin 8)) :=
        ⟨fun a b => by rw [hzero a, hzero b]⟩
      exact (not_subsingleton_iff_nontrivial.mpr
        (inferInstance : Nontrivial (EuclideanSpace ℝ (Fin 8)))) hsub
    -- the additive splitting of the perturbed map
    have hdecomp : ∀ τ : EuclideanSpace ℝ (Fin 8), Pmap τ = Bmap + Dmap τ := by
      intro τ
      funext y
      have hP : Pmap τ y = pair44 (A τ y - chr (E (ftS x) (ftU x)) (V (ftY y)))
          (A' τ y - chr (E' (ftS x) (ftU x)) (W (ftZ y))) := rfl
      have hB : Bmap y = pair44 (A0 y - chr (E (ftS x) (ftU x)) (V (ftY y)))
          (A0' y - chr (E' (ftS x) (ftU x)) (W (ftZ y))) := rfl
      rw [hP, Pi.add_apply, hB]
      simp only [hDmap]
      rw [ppPair44_add,
        show (A0 y - chr (E (ftS x) (ftU x)) (V (ftY y))) + (A τ y - A0 y)
            = A τ y - chr (E (ftS x) (ftU x)) (V (ftY y)) from by abel,
        show (A0' y - chr (E' (ftS x) (ftU x)) (W (ftZ y))) + (A' τ y - A0' y)
            = A' τ y - chr (E' (ftS x) (ftU x)) (W (ftZ y)) from by abel]
    -- the perturbation budget
    have hbudget : ∀ ε₀ : ℝ, 0 < ε₀ → ∃ δ : ℝ, 0 < δ ∧
        ∀ τ : EuclideanSpace ℝ (Fin 8), ‖τ‖ < δ →
          DifferentiableAt ℝ (Dmap τ) x ∧ ‖fderiv ℝ (Dmap τ) x‖ < ε₀ := by
      intro ε₀ hε₀
      have hεb : 0 < ε₀ / 2 := by linarith
      obtain ⟨δ₁, hδ₁, h₁⟩ := exists_delta_block_diff_lt (Ξ := Ξ) hΞ hΞ0 hw hE unpackFst
        (c := E (ftS x) (ftU x)) (x := x) (mem_chart_source _ _) hεb
      obtain ⟨δ₂, hδ₂, h₂⟩ := exists_delta_block_diff_lt (Ξ := Ξ) hΞ hΞ0 hw hE' unpackSnd
        (c := E' (ftS x) (ftU x)) (x := x) (mem_chart_source _ _) hεb
      refine ⟨min δ₁ δ₂, lt_min hδ₁ hδ₂, fun τ hτ => ?_⟩
      have hτ₁ : ‖τ‖ < δ₁ := lt_of_lt_of_le hτ (min_le_left _ _)
      have hτ₂ : ‖τ‖ < δ₂ := lt_of_lt_of_le hτ (min_le_right _ _)
      obtain ⟨hd1, hd10, hb1⟩ := h₁ τ hτ₁
      obtain ⟨hd2, hd20, hb2⟩ := h₂ τ hτ₂
      have hdA : DifferentiableAt ℝ (A τ) x := by simpa only [hA, ppShift] using hd1
      have hdA0 : DifferentiableAt ℝ A0 x := by simpa only [hA0] using hd10
      have hdA' : DifferentiableAt ℝ (A' τ) x := by simpa only [hA', ppShift] using hd2
      have hdA0' : DifferentiableAt ℝ A0' x := by simpa only [hA0'] using hd20
      have hbA : ‖fderiv ℝ (A τ) x - fderiv ℝ A0 x‖ < ε₀ / 2 := by
        simpa only [hA, hA0, ppShift] using hb1
      have hbA' : ‖fderiv ℝ (A' τ) x - fderiv ℝ A0' x‖ < ε₀ / 2 := by
        simpa only [hA', hA0', ppShift] using hb2
      have hsubA : fderiv ℝ (fun y : EuclideanSpace ℝ (Fin 9) => A τ y - A0 y) x
          = fderiv ℝ (A τ) x - fderiv ℝ A0 x := fderiv_sub hdA hdA0
      have hsubA' : fderiv ℝ (fun y : EuclideanSpace ℝ (Fin 9) => A' τ y - A0' y) x
          = fderiv ℝ (A' τ) x - fderiv ℝ A0' x := fderiv_sub hdA' hdA0'
      have hnA : ‖fderiv ℝ (fun y : EuclideanSpace ℝ (Fin 9) => A τ y - A0 y) x‖ < ε₀ / 2 := by
        rw [hsubA]; exact hbA
      have hnA' : ‖fderiv ℝ (fun y : EuclideanSpace ℝ (Fin 9) => A' τ y - A0' y) x‖ < ε₀ / 2 := by
        rw [hsubA']; exact hbA'
      have hpair := fderiv_pair44_comp
        (f := fun y : EuclideanSpace ℝ (Fin 9) => A τ y - A0 y)
        (g := fun y : EuclideanSpace ℝ (Fin 9) => A' τ y - A0' y)
        (hdA.sub hdA0) (hdA'.sub hdA0')
      have hdD : DifferentiableAt ℝ (Dmap τ) x := by
        simpa only [hDmap] using hpair.1
      have hnD : ‖fderiv ℝ (Dmap τ) x‖ ≤ 2 * max
          ‖fderiv ℝ (fun y : EuclideanSpace ℝ (Fin 9) => A τ y - A0 y) x‖
          ‖fderiv ℝ (fun y : EuclideanSpace ℝ (Fin 9) => A' τ y - A0' y) x‖ := by
        simpa only [hDmap] using hpair.2
      refine ⟨hdD, ?_⟩
      have hmax : max ‖fderiv ℝ (fun y : EuclideanSpace ℝ (Fin 9) => A τ y - A0 y) x‖
          ‖fderiv ℝ (fun y : EuclideanSpace ℝ (Fin 9) => A' τ y - A0' y) x‖ < ε₀ / 2 :=
        max_lt hnA hnA'
      linarith
    -- the core transfer: a small perturbation of the base derivative transfers regularity
    have hcore : ∀ (τ : EuclideanSpace ℝ (Fin 8))
        (S : EuclideanSpace ℝ (Fin 9) →L[ℝ] EuclideanSpace ℝ (Fin 8)),
        S = fderiv ℝ (Dmap τ) x → DifferentiableAt ℝ (Dmap τ) x →
        (Function.Surjective (fderiv ℝ Bmap x + S) ∧
          (x ∈ Submission.Drive.unitBoxBdry 8 → ∃ i : Fin 9, (x i = 0 ∨ x i = 1) ∧
            (∀ j : Fin 9, j ≠ i → x j ∈ Set.Ioo (0 : ℝ) 1) ∧
            Function.Surjective (fun v : {v : EuclideanSpace ℝ (Fin 9) // v i = 0} =>
              (fderiv ℝ Bmap x + S) v.1))) →
        PPRegAt (ppShift Ξ w (unpackFst τ) E) (ppShift Ξ w (unpackSnd τ) E') V W x := by
      intro τ S hS hdD hdata
      have hPderiv : fderiv ℝ (ppDiff (E (ftS x) (ftU x)) (E' (ftS x) (ftU x))
            (ppShift Ξ w (unpackFst τ) E) (ppShift Ξ w (unpackSnd τ) E') V W) x
          = fderiv ℝ Bmap x + S := by
        rw [hS]
        have hfun : Pmap τ = ppDiff (E (ftS x) (ftU x)) (E' (ftS x) (ftU x))
            (ppShift Ξ w (unpackFst τ) E) (ppShift Ξ w (unpackSnd τ) E') V W := rfl
        rw [← hfun, hdecomp τ, fderiv_add hBdiff hdD]
      unfold PPRegAt
      rw [hPS τ, hPS' τ, hPderiv]
      exact hdata
    by_cases hb : x ∈ Submission.Drive.unitBoxBdry 8
    · obtain ⟨i, hi, hint, hLh⟩ := hreg.2 hb
      obtain ⟨ε₁, hε₁, hε₁p⟩ := exists_pos_norm_lt_surjective_add (fderiv ℝ Bmap x) hL
      obtain ⟨εh, hεh, hεhp⟩ := surjective_domRestrict_open i (fderiv ℝ Bmap x) hLh
      obtain ⟨δ, hδ, hδp⟩ := hbudget (min ε₁ εh) (lt_min hε₁ hεh)
      refine ⟨δ, hδ, fun τ hτ _ => ?_⟩
      obtain ⟨hdD, hnD⟩ := hδp τ hτ
      have hn₁ : ‖fderiv ℝ (Dmap τ) x‖ < ε₁ := lt_of_lt_of_le hnD (min_le_left _ _)
      have hnh : ‖fderiv ℝ (Dmap τ) x‖ < εh := lt_of_lt_of_le hnD (min_le_right _ _)
      exact hcore τ (fderiv ℝ (Dmap τ) x) rfl hdD
        ⟨hε₁p _ hn₁, fun _ => ⟨i, hi, hint, hεhp _ hnh⟩⟩
    · obtain ⟨ε₁, hε₁, hε₁p⟩ := exists_pos_norm_lt_surjective_add (fderiv ℝ Bmap x) hL
      obtain ⟨δ, hδ, hδp⟩ := hbudget ε₁ hε₁
      refine ⟨δ, hδ, fun τ hτ _ => ?_⟩
      obtain ⟨hdD, hnD⟩ := hδp τ hτ
      exact hcore τ (fderiv ℝ (Dmap τ) x) rfl hdD
        ⟨hε₁p _ hnD, fun hb' => absurd hb' hb⟩
  · exact ⟨1, one_pos, fun τ hτ hreg' => absurd hreg' hreg⟩

end

end Work.Drive.ppParity
