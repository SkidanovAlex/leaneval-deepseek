import Mathlib.Analysis.Fourier.AddCircleMulti
import Mathlib.Data.ZMod.ValMinAbs
import Mathlib.LinearAlgebra.Complex.FiniteDimensional
import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Submission.Work.BoseBoxFock.hatChiSq_cubeCompl_tail
import Submission.Work.BoseRowQ2.chiLatticeParseval
import Submission.Work.BoseRowQ2.maskTailDefs
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Work.BoseBoxFock.thetaTail_bound` — the `O(N^{-K})` truncation bound for the `χ²`-row tail

The `χ²`-row of the corpus `Q₁` (FS's `prop:Hamilton2ndQuant`) is the *truncated* lattice sum
`∑_{s ∈ Lab N, s ≠ 0} hatChiSq(ℓ • kmomLab ℓ N s) • thetaExp(ℓ, kmomLab ℓ N s)`, while its ideal
(whole-dual-lattice) value is the position-space mode `χ_Λ² − θ`.  `thetaTail` is the difference,
and this file proves the statement requested by `FINDING_PotChiLin_exists.md` §3 (lemma `(L1)`, the
`θ`-half): for every `K` there is an absolute constant `C` with

    `‖thetaTail ℓ N x‖ ≤ C / ((N : ℝ) + 1) ^ K`     for all `ℓ > 0`, `N`, `x`,

**uniformly in `ℓ`** — the `∃ Nmin` repair of `PotChiLin_exists` needs exactly this.

## The mathematics

`corpusBox` is the corpus bump `Submission.BoseGases.chi` (`C^∞`, even, `∫χ² = 1`, vanishing for
`‖x‖ ≥ 1/2`), and `hatChiSq p = ∫ χ(x)² cos⟪p,x⟫ dx` is the cosine transform of `χ²`.  Two facts:

1. **Poisson summation for `χ²`** (`thetaPoisson_cell`, proved below by generalising the corpus's
   `Work.BoseB7AK.Q2Gram.chiSq_fourier_sum` — the same statement at `z = 0` — from `0` to an
   arbitrary point of the unit cell):

       `∑'_{m ∈ ℤ³} χ̂²(2πm) e^{2πi⟪m,z⟫} = χ(z)²`     (`z ∈ unitCell`),

   which is `∑'_m χ̂²(vec m) e^{i⟪vec m,z⟫} = ∑'_d χ(z+d)²` together with the fact that every
   translate `d ≠ 0` contributes `0` (some coordinate of `z + d` has modulus `≥ 1/2`, and `χ`
   vanishes at `‖·‖ ≥ 1/2`).

2. **The cube-complement tail** (`Work.BoseBoxFock.hatChiSq_cubeCompl_tail`):

       `∑'_{m ∉ [−N,N]³} |χ̂²(vec m)| ≤ C_K/((N:ℝ)+1)^K`,

   from the Schwartz decay of `χ̂²` (`Work.BoseK15.ChiReg_corpus`, any order) and the lattice count
   (`Work.BoseK15.sum_inv_one_add_norm_tail`).

The truncation over `Lab N` is the cube `[−N,N]³` reindexed (`Work.BoseRowQ2.image_labVec_eq_cube`),
so the tail is precisely the sum over the cube complement.  `θ = 0` off the box and `χ_Λ` vanishes
off the box as well, so the trivial case is immediate; the `ℓ`-dependence cancels in the identity
`ℓ • kmomLab ℓ N s = vec (labVec N s)`, which is what makes the bound uniform in `ℓ`.
-/

attribute [local instance] instMeasureSpaceUnitAddCircle

noncomputable section
open scoped BigOperators Pointwise
open MeasureTheory

namespace Work.BoseBoxFock

local notation "E3" => EuclideanSpace ℝ (Fin 3)

/-! ## 1. Poisson summation for `χ²` at a point of the unit cell -/

/-- The periodization `F y = ∑'_n χ(y+n)²` of `χ²` is `χ²` at every point of the *closed* unit
cell.  This is `Work.BoseB7AK.Q2Gram.F_eq_of_mem_cube` with the half-open hypothesis weakened to
the closed one: its proof only ever uses `|y i| ≤ 1/2`. -/
private lemma F_eq_of_abs_le (y : Fin 3 → ℝ) (hy : ∀ i : Fin 3, |y i| ≤ (1 / 2 : ℝ)) :
    Work.BoseB7AK.Q2Gram.F y = Work.BoseB7AK.Q2Gram.g1 y := by
  rw [Work.BoseB7AK.Q2Gram.F, tsum_eq_single 0 (fun n hn => ?_)]
  · congr 1
    funext i
    simp [Work.BoseB7AK.Q2Gram.kv]
  · obtain ⟨i, hi⟩ : ∃ i : Fin 3, n i ≠ 0 := by
      by_contra h
      push Not at h
      exact hn (funext h)
    refine Work.BoseB7AK.Q2Gram.g1_zero_of_abs_coord (y + Work.BoseB7AK.Q2Gram.kv n) i ?_
    have hni : (1 : ℝ) ≤ |(n i : ℝ)| := by
      have h1 : (1 : ℤ) ≤ |n i| := by
        have hpos : 0 < |n i| := abs_pos.mpr hi
        omega
      exact_mod_cast h1
    have hstep : |(n i : ℝ)| - |y i| ≤ |y i + (n i : ℝ)| := by
      have h := abs_sub_abs_le_abs_sub ((n i : ℝ)) (-(y i))
      rw [abs_neg, sub_neg_eq_add] at h
      simpa [add_comm] using h
    simp only [Pi.add_apply, Work.BoseB7AK.Q2Gram.kv]
    linarith [hni, hy i, hstep]

/-- The torus Fourier monomial evaluated at the class of a point of `ℝ³`. -/
private lemma mFourier_apply (m : Fin 3 → ℤ) (z : E3) :
    UnitAddTorus.mFourier m (fun i => (z i : UnitAddCircle))
      = Complex.exp (Complex.I * (inner ℝ (Work.BoseB4.vec m) z : ℂ)) := by
  have h := Work.BoseB7AK.Q2Gram.mFourier_neg_apply (-m) (fun i : Fin 3 => z i)
  rw [neg_neg, WithLp.toLp_ofLp, vec_neg, inner_neg_left] at h
  rw [h, Complex.ofReal_neg]
  congr 1
  ring

/-- **Poisson summation for `χ²` at an arbitrary point of the unit cell** (the `z`-dependent
generalisation of `Work.BoseB7AK.Q2Gram.chiSq_fourier_sum`, which is the case `z = 0`). -/
private theorem thetaPoisson_cell {z : E3} (hz : z ∈ Work.BoseB4.unitCell) :
    (∑' m : Fin 3 → ℤ,
        ((Work.BoseK15.corpusBox.hatChiSq (Work.BoseB4.vec m) : ℝ) : ℂ)
          * Complex.exp (Complex.I * (inner ℝ (Work.BoseB4.vec m) z : ℂ)))
      = ((Submission.BoseGases.chi z ^ 2 : ℝ) : ℂ) := by
  have hz' : ∀ i : Fin 3, |z i| ≤ (1 / 2 : ℝ) := fun i => hz i
  have hsum := UnitAddTorus.hasSum_mFourier_series_apply_of_summable
    (f := (⟨Work.BoseB7AK.Q2Gram.P, Work.BoseB7AK.Q2Gram.P_continuous⟩ :
      C(UnitAddTorus (Fin 3), ℂ)))
    (by simpa using Work.BoseB7AK.Q2Gram.summable_coeff) (fun i => (z i : UnitAddCircle))
  have hsum' : HasSum (fun m : Fin 3 → ℤ =>
      UnitAddTorus.mFourierCoeff Work.BoseB7AK.Q2Gram.P m
        • UnitAddTorus.mFourier m (fun i => (z i : UnitAddCircle)))
      (Work.BoseB7AK.Q2Gram.P (fun i => (z i : UnitAddCircle))) := hsum
  have hval : Work.BoseB7AK.Q2Gram.P (fun i => (z i : UnitAddCircle))
      = ((Submission.BoseGases.chi z ^ 2 : ℝ) : ℂ) := by
    rw [Work.BoseB7AK.Q2Gram.P_apply, F_eq_of_abs_le _ hz']
    simp only [Work.BoseB7AK.Q2Gram.g1_apply, WithLp.toLp_ofLp]
  have hcoeff : ∀ m : Fin 3 → ℤ, UnitAddTorus.mFourierCoeff Work.BoseB7AK.Q2Gram.P m
      = ((Work.BoseK15.corpusBox.hatChiSq (Work.BoseB4.vec m) : ℝ) : ℂ) := by
    intro m
    have h := Work.BoseRowQ2.integral_exp_inner_of_even
      (F := fun y : E3 => (Submission.BoseGases.chi y) ^ 2)
      (Submission.BoseGases.chi_continuous.pow 2)
      (Submission.BoseGases.chi_hasCompactSupport.comp_left
        (g := fun r : ℝ => r ^ 2) (by norm_num))
      (fun x => by rw [Submission.BoseGases.chi_even]) (Work.BoseB4.vec m)
    have h1 : (∫ x : E3, ((Submission.BoseGases.chi x : ℂ)) ^ 2
            * Complex.exp (-(Complex.I * (inner ℝ (Work.BoseB4.vec m) x : ℂ))))
        = ∫ x : E3, Complex.exp (-(Complex.I * (inner ℝ (Work.BoseB4.vec m) x : ℂ)))
            * (((Submission.BoseGases.chi x) ^ 2 : ℝ) : ℂ) := by
      refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
      simp only [Complex.ofReal_pow]
      ring
    rw [Work.BoseB7AK.Q2Gram.mFourierCoeff_P, h1, h]
    simp only [Work.BoseB4.BoxData.hatChiSq, Work.BoseK15.corpusBox_chi]
  have h2 : HasSum (fun m : Fin 3 → ℤ =>
      ((Work.BoseK15.corpusBox.hatChiSq (Work.BoseB4.vec m) : ℝ) : ℂ)
        * Complex.exp (Complex.I * (inner ℝ (Work.BoseB4.vec m) z : ℂ)))
      ((Submission.BoseGases.chi z ^ 2 : ℝ) : ℂ) := by
    rw [← hval]
    refine hsum'.congr_fun (fun m => ?_)
    rw [hcoeff m, mFourier_apply m z, smul_eq_mul]
  exact h2.tsum_eq

/-! ## 2. The ideal mode and the subtype reindexing -/

/-- The ideal lattice mode of the `χ²`-row at the cell point `z`. -/
private def thetaTailIdeal (z : E3) (m : Fin 3 → ℤ) : ℂ :=
  ((Work.BoseK15.corpusBox.hatChiSq (Work.BoseB4.vec m) : ℝ) : ℂ)
    * Complex.exp (Complex.I * (inner ℝ (Work.BoseB4.vec m) z : ℂ))

/-- Reindexing a `tsum` over a subtype along a propositional equivalence of the predicates
(a plain `rw` fails here: the motive is not type correct). -/
private lemma tsum_subtype_congr {α : Type*} {p q : α → Prop} (h : ∀ a, p a ↔ q a)
    (f : α → ℝ) : (∑' a : {a // p a}, f a) = ∑' a : {a // q a}, f a :=
  Equiv.tsum_eq (Equiv.subtypeEquivRight h) (fun a : {a // q a} => f a)

/-! ## 3. The truncation bound -/

theorem thetaTail_bound (K : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (ℓ : ℝ), 0 < ℓ → ∀ (N : ℕ) (x : EuclideanSpace ℝ (Fin 3)),
      ‖thetaTail ℓ N x‖ ≤ C / ((N : ℝ) + 1) ^ K := by
  obtain ⟨C, hC0, hC⟩ := hatChiSq_cubeCompl_tail K
  refine ⟨C, hC0, ?_⟩
  intro ℓ hℓ N x
  set y : E3 := ℓ⁻¹ • x with hy
  -- ## summability of `thetaTailIdeal y`
  have hsumg : Summable (thetaTailIdeal y) := by
    obtain ⟨Cchi, hCchi0, hChi⟩ := Work.BoseK15.ChiReg_corpus 2
    have hpoint : ∀ m : Fin 3 → ℤ,
        ‖thetaTailIdeal y m‖ ≤ Cchi * (((1 : ℝ) + ‖Work.BoseB4.vec m‖ ^ 2) ^ 2)⁻¹ := by
      intro m
      have hD : (0 : ℝ) < (1 + ‖Work.BoseB4.vec m‖ ^ 2) ^ 2 := by positivity
      have hle : |Work.BoseK15.corpusBox.hatChiSq (Work.BoseB4.vec m)|
          ≤ Cchi * (((1 : ℝ) + ‖Work.BoseB4.vec m‖ ^ 2) ^ 2)⁻¹ := by
        have h2 : |Work.BoseK15.corpusBox.hatChiSq (Work.BoseB4.vec m)|
            ≤ Cchi / (1 + ‖Work.BoseB4.vec m‖ ^ 2) ^ 2 := by
          rw [le_div_iff₀ hD]
          exact hChi.2 (Work.BoseB4.vec m)
        simpa only [div_eq_mul_inv] using h2
      rw [thetaTailIdeal, Complex.norm_mul]
      have h1 : ‖((Work.BoseK15.corpusBox.hatChiSq (Work.BoseB4.vec m) : ℝ) : ℂ)‖
          = |Work.BoseK15.corpusBox.hatChiSq (Work.BoseB4.vec m)| :=
        RCLike.norm_ofReal _
      have h2 : ‖Complex.exp (Complex.I * (inner ℝ (Work.BoseB4.vec m) y : ℂ))‖ = 1 := by
        rw [Complex.norm_exp]
        simp
      rw [h1, h2, mul_one]
      exact hle
    obtain ⟨C2, _hC2, hC2b⟩ := Work.BoseK15.sum_inv_one_add_norm_le 2 (by norm_num)
    refine Summable.of_norm_bounded
      (g := fun m : Fin 3 → ℤ => Cchi * (((1 : ℝ) + ‖Work.BoseB4.vec m‖ ^ 2) ^ 2)⁻¹)
      ?_ hpoint
    exact (summable_of_sum_le (fun n => by positivity) hC2b).mul_left Cchi
  by_cases hx : x ∈ Work.BoseK15.corpusBox.boxL ℓ
  · -- ## the main case: `x` is in the box
    have hxsmul : x ∈ (ℓ • (Work.BoseB4.unitCell : Set E3)) := hx
    have hycell : y ∈ Work.BoseB4.unitCell :=
      (Set.mem_smul_set_iff_inv_smul_mem₀ (ne_of_gt hℓ) Work.BoseB4.unitCell x).mp hxsmul
    have htheta : Work.BoseK15.corpusBox.thetaFun ℓ x = 1 := by
      rw [Work.BoseB4.BoxData.thetaFun_apply, if_pos hx]
    have hchiLam : Work.BoseK15.corpusBox.chiLam ℓ x = Submission.BoseGases.chi y := by
      rw [Work.BoseB4.BoxData.chiLam_apply, ← hy]
      rfl
    have hkmom : ∀ s : Lab N, ℓ • kmomLab ℓ N s = Work.BoseB4.vec (labVec N s) := by
      intro s
      simp only [kmomLab, smul_smul, mul_inv_cancel₀ (ne_of_gt hℓ), one_smul]
    have hinner : ∀ s : Lab N,
        inner ℝ (kmomLab ℓ N s) x = inner ℝ (Work.BoseB4.vec (labVec N s)) y := by
      intro s
      simp only [kmomLab, hy, real_inner_smul_left, real_inner_smul_right]
    have hsmd : ∀ s ∈ (Finset.univ.filter (fun s : Lab N => s ≠ 0)),
        ((Work.BoseK15.corpusBox.hatChiSq (ℓ • kmomLab ℓ N s) : ℝ) : ℂ)
            * Work.BoseK15.corpusBox.thetaExp ℓ (kmomLab ℓ N s) x
        = thetaTailIdeal y (labVec N s) := by
      intro s _
      simp only [Work.BoseB4.BoxData.thetaExp_apply]
      rw [htheta, mul_one, hkmom s, hinner s, thetaTailIdeal]
    have hthetaTail : thetaTail ℓ N x
        = ((Submission.BoseGases.chi y) ^ 2 : ℂ) - 1
          - ∑ s ∈ (Finset.univ.filter (fun s : Lab N => s ≠ 0)),
              thetaTailIdeal y (labVec N s) := by
      have h1 : thetaTail ℓ N x
          = ((Work.BoseK15.corpusBox.chiLam ℓ x : ℂ)) ^ 2
            - Work.BoseK15.corpusBox.thetaFun ℓ x
            - ∑ s ∈ (Finset.univ.filter (fun s : Lab N => s ≠ 0)),
                ((Work.BoseK15.corpusBox.hatChiSq (ℓ • kmomLab ℓ N s) : ℝ) : ℂ)
                  * Work.BoseK15.corpusBox.thetaExp ℓ (kmomLab ℓ N s) x := rfl
      rw [h1, hchiLam, htheta, Finset.sum_congr rfl hsmd]
    -- the filtered sum is the full `Lab N` sum minus the zero label
    have hA : (∑ s ∈ (Finset.univ.filter (fun s : Lab N => s ≠ 0)),
          thetaTailIdeal y (labVec N s))
        = (∑ s : Lab N, thetaTailIdeal y (labVec N s)) - thetaTailIdeal y (labVec N 0) := by
      rw [Finset.filter_ne' Finset.univ (0 : Lab N),
        ← Finset.sum_erase_add Finset.univ
          (fun s : Lab N => thetaTailIdeal y (labVec N s)) (Finset.mem_univ (0 : Lab N))]
      ring
    have hlab0 : labVec N (0 : Lab N) = 0 := by
      funext i
      simp [labVec]
    have hval0 : thetaTailIdeal y (labVec N 0) = 1 := by
      have hv0 : Work.BoseB4.vec (0 : Fin 3 → ℤ) = 0 := by
        refine PiLp.ext fun i => ?_
        simp [Work.BoseB4.vec]
      rw [hlab0, thetaTailIdeal, hv0, Work.BoseB4.BoxData.hatChiSq_zero]
      simp
    have hB : (∑ s : Lab N, thetaTailIdeal y (labVec N s))
        = ∑ m ∈ Work.BoseRowQ2.cube N, thetaTailIdeal y m := by
      rw [← Work.BoseRowQ2.image_labVec_eq_cube N, Finset.sum_image]
      intro a _ b _ hab
      exact Work.BoseRowQ2.labVec_inj' N hab
    have hC' : ((Submission.BoseGases.chi y) ^ 2 : ℂ)
        = ∑' m : Fin 3 → ℤ, thetaTailIdeal y m := by
      rw [← Complex.ofReal_pow, ← thetaPoisson_cell hycell]
      rfl
    have hsplit : (∑' m : Fin 3 → ℤ, thetaTailIdeal y m)
        = (∑ m ∈ Work.BoseRowQ2.cube N, thetaTailIdeal y m)
          + ∑' m : {m : Fin 3 → ℤ // m ∉ Work.BoseRowQ2.cube N}, thetaTailIdeal y m :=
      (hsumg.sum_add_tsum_subtype_compl (s := Work.BoseRowQ2.cube N)).symm
    have hkey : thetaTail ℓ N x
        = ∑' m : {m : Fin 3 → ℤ // m ∉ Work.BoseRowQ2.cube N},
            thetaTailIdeal y m := by
      rw [hthetaTail, hA, hval0, hB, hC', hsplit]
      ring
    rw [hkey]
    -- ## the norm bound
    have hnorm_ideal : ∀ m : Fin 3 → ℤ,
        ‖thetaTailIdeal y m‖ = |Work.BoseK15.corpusBox.hatChiSq (Work.BoseB4.vec m)| := by
      intro m
      rw [thetaTailIdeal, Complex.norm_mul]
      have h1 : ‖((Work.BoseK15.corpusBox.hatChiSq (Work.BoseB4.vec m) : ℝ) : ℂ)‖
          = |Work.BoseK15.corpusBox.hatChiSq (Work.BoseB4.vec m)| :=
        RCLike.norm_ofReal _
      have h2 : ‖Complex.exp (Complex.I * (inner ℝ (Work.BoseB4.vec m) y : ℂ))‖ = 1 := by
        rw [Complex.norm_exp]
        simp
      rw [h1, h2, mul_one]
    have htail : (∑' m : {m : Fin 3 → ℤ // m ∉ Work.BoseRowQ2.cube N},
        |Work.BoseK15.corpusBox.hatChiSq (Work.BoseB4.vec m)|)
        ≤ C / ((N : ℝ) + 1) ^ K := by
      rw [tsum_subtype_congr
        (fun m : Fin 3 → ℤ => not_congr (Work.BoseRowQ2.mem_cube (N := N) (m := m)))
        (fun m : Fin 3 → ℤ => |Work.BoseK15.corpusBox.hatChiSq (Work.BoseB4.vec m)|)]
      exact hC N
    calc ‖∑' m : {m : Fin 3 → ℤ // m ∉ Work.BoseRowQ2.cube N}, thetaTailIdeal y m‖
        ≤ ∑' m : {m : Fin 3 → ℤ // m ∉ Work.BoseRowQ2.cube N}, ‖thetaTailIdeal y m‖ :=
          norm_tsum_le_tsum_norm ((hsumg.subtype _).norm)
      _ = ∑' m : {m : Fin 3 → ℤ // m ∉ Work.BoseRowQ2.cube N},
            |Work.BoseK15.corpusBox.hatChiSq (Work.BoseB4.vec m)| :=
          tsum_congr fun m => hnorm_ideal m
      _ ≤ C / ((N : ℝ) + 1) ^ K := htail
  · -- ## the trivial case: `x` is outside the box
    have hzero : thetaTail ℓ N x = 0 := by
      have hθ : Work.BoseK15.corpusBox.thetaFun ℓ x = 0 := by
        rw [Work.BoseB4.BoxData.thetaFun_apply, if_neg hx]
      have hchi : Work.BoseK15.corpusBox.chiLam ℓ x = 0 := by
        have hyc : ¬ (∀ i : Fin 3, |y i| ≤ (1 / 2 : ℝ)) := by
          intro hall
          exact hx ((Set.mem_smul_set_iff_inv_smul_mem₀ (ne_of_gt hℓ)
            Work.BoseB4.unitCell x).mpr (by
              show ∀ i : Fin 3, |y i| ≤ (1 / 2 : ℝ)
              exact hall))
        obtain ⟨i, hi⟩ := not_forall.mp hyc
        have hnorm : (1 / 2 : ℝ) < ‖y‖ := by
          have h1 : |y i| ≤ ‖y‖ := by
            simpa [Real.norm_eq_abs] using PiLp.norm_apply_le y i
          exact lt_of_lt_of_le (not_le.mp hi) h1
        rw [Work.BoseB4.BoxData.chiLam_apply, ← hy]
        exact Submission.BoseGases.chi_eq_zero_of_norm_gt y hnorm
      have hsum0 : (∑ s ∈ (Finset.univ.filter (fun s : Lab N => s ≠ 0)),
          ((Work.BoseK15.corpusBox.hatChiSq (ℓ • kmomLab ℓ N s) : ℝ) : ℂ)
            * Work.BoseK15.corpusBox.thetaExp ℓ (kmomLab ℓ N s) x) = 0 := by
        refine Finset.sum_eq_zero fun s _ => ?_
        simp only [Work.BoseB4.BoxData.thetaExp_apply, hθ, mul_zero]
      have h1 : thetaTail ℓ N x
          = ((Work.BoseK15.corpusBox.chiLam ℓ x : ℂ)) ^ 2
            - Work.BoseK15.corpusBox.thetaFun ℓ x
            - ∑ s ∈ (Finset.univ.filter (fun s : Lab N => s ≠ 0)),
                ((Work.BoseK15.corpusBox.hatChiSq (ℓ • kmomLab ℓ N s) : ℝ) : ℂ)
                  * Work.BoseK15.corpusBox.thetaExp ℓ (kmomLab ℓ N s) x := rfl
      rw [h1, hchi, hθ, hsum0]
      simp
    rw [hzero, norm_zero]
    exact div_nonneg hC0 (by positivity)

end Work.BoseBoxFock
