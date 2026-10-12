import Mathlib.Algebra.Ring.IsFormallyReal
import Mathlib.Analysis.RCLike.Inner
import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.Analysis.CStarAlgebra.Module.Constructions
import Submission.Work.BoseBoxFock.Defs
import Submission.Work.BoseDict.Defs2
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace Work.BoseBoxFock

open MeasureTheory
open scoped ComplexInnerProductSpace

/-!
# `Work.BoseBoxFock.qVec_eq_etaOf_of_pairing`

The box mode `Q(e^{ikx}χ_Λ) = qVec` whose pairings against the orthonormal family `e` are the
coordinates of the vector `√(ℓ³)·f k` is *equal* to that vector, on almost every point.

The mathematical content is a single fact of Hilbert space theory: if `v : Fin m → E` is an
orthonormal family in a complex inner product space and `∑ i, ‖⟪v i, x⟫⟫‖² = ‖x‖²` (Bessel
*equality*, i.e. no mass is lost outside `span (v i)`), then `x = ∑ i, ⟪v i, x⟫ • v i`.  We apply
it in `Lp ℂ 2 volume`; the Bessel equality is exactly the corpus's `HonestModes.hphys` pinning
(`gram (f k) (f k) = ℓ^{-3}·realIP (qVec k) (qVec k)`, i.e. `Σ_l (f k l)² = ℓ^{-3}∫‖qVec_k‖²`).
-/

/-- **Orthonormal expansion from Bessel equality.**  If `v` is a finite orthonormal family in a
complex inner product space and `x` has no mass outside `span{v i}` (tested by
`∑ i, ‖⟪v i, x⟫‖² = ‖x‖²`), then `x` is exactly its expansion in the family. -/
theorem eq_of_orthonormal_of_norm_eq {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    {m : ℕ} {v : Fin m → E} (hv : Orthonormal ℂ v) (x : E)
    (h : (∑ i, ‖⟪v i, x⟫‖ ^ 2) = ‖x‖ ^ 2) :
    x = ∑ i, ⟪v i, x⟫ • v i := by
  have hns : ∀ y : E, ‖y‖ ^ 2 = RCLike.re ⟪y, y⟫ := fun y => InnerProductSpace.norm_sq_eq_re_inner y
  have hns2 : ∀ y z : E, ‖y - z‖ ^ 2
      = ‖y‖ ^ 2 - 2 * RCLike.re ⟪y, z⟫ + ‖z‖ ^ 2 := fun y z => norm_sub_sq y z
  have key : ∀ z : ℂ, z * (starRingEnd ℂ) z = ((‖z‖ ^ 2 : ℝ) : ℂ) := by
    intro z; rw [Complex.mul_conj, Complex.normSq_eq_norm_sq]
  have key' : ∀ z : ℂ, (starRingEnd ℂ) z * z = ((‖z‖ ^ 2 : ℝ) : ℂ) := by
    intro z; rw [mul_comm, key]
  have hSS : ‖∑ i : Fin m, ⟪v i, x⟫ • v i‖ ^ 2 = ∑ i, ‖⟪v i, x⟫‖ ^ 2 := by
    rw [hns, Orthonormal.inner_sum hv _ _ Finset.univ]
    simp only [map_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [key']; exact Complex.ofReal_re _
  have hxS : RCLike.re ⟪x, ∑ i : Fin m, ⟪v i, x⟫ • v i⟫ = ∑ i, ‖⟪v i, x⟫‖ ^ 2 := by
    rw [inner_sum, map_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    have h1 : ⟪x, ⟪v i, x⟫ • v i⟫ = ⟪v i, x⟫ * ⟪x, v i⟫ := inner_smul_right x (v i) ⟪v i, x⟫
    have h2 : ⟪x, v i⟫ = (starRingEnd ℂ) ⟪v i, x⟫ := (inner_conj_symm x (v i)).symm
    rw [h1, h2, key]; exact Complex.ofReal_re _
  have hbf : ‖x - ∑ i : Fin m, ⟪v i, x⟫ • v i‖ ^ 2
      = ‖x‖ ^ 2 - ∑ i, ‖⟪v i, x⟫‖ ^ 2 := by
    rw [hns2, hxS, hSS]; ring
  have hzero : ‖x - ∑ i : Fin m, ⟪v i, x⟫ • v i‖ ^ 2 = 0 := by rw [hbf, h]; ring
  exact sub_eq_zero.mp (norm_eq_zero.mp (sq_eq_zero_iff.mp hzero))

/-- The `L²` inner product of two `toLp` classes is the Bochner integral of the pointwise
pairing (the representative-independent form used in this file). -/
theorem toLp_inner_eq {f g : ℝ³ → ℂ}
    (hf : MemLp f 2 (volume : Measure ℝ³)) (hg : MemLp g 2 (volume : Measure ℝ³)) :
    ⟪hf.toLp f, hg.toLp g⟫ = ∫ x, (starRingEnd ℂ) (f x) * g x := by
  rw [MeasureTheory.L2.inner_def]
  refine integral_congr_ae ?_
  filter_upwards [hf.coeFn_toLp, hg.coeFn_toLp] with x hx hx'
  rw [hx, hx', RCLike.inner_apply']

/-- The `L²` norm of a `toLp` class. -/
theorem norm_toLp_sq {f : ℝ³ → ℂ} (hf : MemLp f 2 (volume : Measure ℝ³)) :
    ‖hf.toLp f‖ ^ 2 = ∫ x, ‖f x‖ ^ 2 := by
  have hns : ‖hf.toLp f‖ ^ 2 = RCLike.re ⟪hf.toLp f, hf.toLp f⟫ :=
    InnerProductSpace.norm_sq_eq_re_inner _
  rw [hns, MeasureTheory.L2.inner_def]
  rw [← integral_re (MeasureTheory.L2.integrable_inner (hf.toLp f) (hf.toLp f))]
  refine integral_congr_ae ?_
  filter_upwards [hf.coeFn_toLp] with x hx
  rw [hx, RCLike.inner_apply', mul_comm, Complex.mul_conj, Complex.normSq_eq_norm_sq]
  exact Complex.ofReal_re _

/-- **The general expansion lemma.**  If `{e l}` is orthonormal, `Q` has pairings `c l` against
`e l` and Bessel equality holds (`∑ l, ‖c l‖² = ∫ ‖Q‖²`), then `Q` is a.e. the superposition
`∑ l, c l · e l`. -/
theorem eq_etaOf_of_pairing {m : ℕ} {e : Fin m → ℝ³ → ℂ} {Q : ℝ³ → ℂ} {c : Fin m → ℂ}
    (horth : ∀ l l', (∫ x, (starRingEnd ℂ) (e l x) * e l' x) = if l = l' then 1 else 0)
    (hpair : ∀ l, (∫ x, (starRingEnd ℂ) (e l x) * Q x) = c l)
    (hmemE : ∀ l, MemLp (e l) 2 (volume : Measure ℝ³))
    (hmemQ : MemLp Q 2 (volume : Measure ℝ³))
    (hnorm : (∑ l, ‖c l‖ ^ 2) = ∫ x, ‖Q x‖ ^ 2) :
    Q =ᵐ[volume] fun x => ∑ l, c l * e l x := by
  classical
  set V : Fin m → Lp ℂ 2 (volume : Measure ℝ³) := fun l => (hmemE l).toLp (e l) with hV
  set X : Lp ℂ 2 (volume : Measure ℝ³) := hmemQ.toLp Q with hX
  have hVl : ∀ l, V l = (hmemE l).toLp (e l) := fun l => by rw [hV]
  have hVae : ∀ l, ((V l : Lp ℂ 2 (volume : Measure ℝ³)) : ℝ³ → ℂ) =ᵐ[volume] e l :=
    fun l => by rw [hVl l]; exact (hmemE l).coeFn_toLp
  have hVorth : Orthonormal ℂ V := by
    rw [orthonormal_iff_ite]
    intro l l'
    rw [hVl l, hVl l', toLp_inner_eq (hmemE l) (hmemE l'), horth l l']
  have hcoef : ∀ l, ⟪V l, X⟫ = c l := by
    intro l
    rw [hVl l, hX, toLp_inner_eq (hmemE l) hmemQ, hpair l]
  have hbessel : (∑ l, ‖⟪V l, X⟫‖ ^ 2) = ‖X‖ ^ 2 := by
    simp only [hcoef]
    rw [hX, norm_toLp_sq hmemQ]
    exact hnorm
  have hXeq : X = ∑ l, ⟪V l, X⟫ • V l := eq_of_orthonormal_of_norm_eq hVorth X hbessel
  have hXae : (X : ℝ³ → ℂ) =ᵐ[volume] Q := by
    rw [hX]; exact hmemQ.coeFn_toLp
  have hSae : ((∑ l, ⟪V l, X⟫ • V l : Lp ℂ 2 (volume : Measure ℝ³)) : ℝ³ → ℂ)
      =ᵐ[volume] fun x => ∑ l, c l * e l x := by
    have h1 : ((∑ l, ⟪V l, X⟫ • V l : Lp ℂ 2 (volume : Measure ℝ³)) : ℝ³ → ℂ)
        =ᵐ[volume] (∑ l, (((⟪V l, X⟫ • V l : Lp ℂ 2 (volume : Measure ℝ³)) : ℝ³ → ℂ))) :=
      Lp.coeFn_finsetSum Finset.univ (fun l => ⟪V l, X⟫ • V l)
    have hterm : ∀ l, ((((⟪V l, X⟫ • V l : Lp ℂ 2 (volume : Measure ℝ³)) : ℝ³ → ℂ)))
        =ᵐ[volume] fun x => c l * e l x := by
      intro l
      refine (Lp.coeFn_smul (⟪V l, X⟫) (V l)).trans ?_
      filter_upwards [hVae l] with x hx
      simp only [Pi.smul_apply, smul_eq_mul, hcoef l, hx]
    have hall : ∀ᵐ x ∂(volume : Measure ℝ³), ∀ l ∈ (Finset.univ : Finset (Fin m)),
        ((((⟪V l, X⟫ • V l : Lp ℂ 2 (volume : Measure ℝ³)) : ℝ³ → ℂ))) x = c l * e l x :=
      (Finset.eventually_all (Finset.univ : Finset (Fin m))).2 (fun l _ => hterm l)
    have h2 : (∑ l, ((((⟪V l, X⟫ • V l : Lp ℂ 2 (volume : Measure ℝ³)) : ℝ³ → ℂ))))
        =ᵐ[volume] (fun x => ∑ l, c l * e l x) := by
      filter_upwards [hall] with x hx
      rw [Finset.sum_apply]
      exact Finset.sum_congr rfl (fun l _ => hx l (Finset.mem_univ l))
    exact h1.trans h2
  have hae : (X : ℝ³ → ℂ) =ᵐ[volume]
      ((∑ l, ⟪V l, X⟫ • V l : Lp ℂ 2 (volume : Measure ℝ³)) : ℝ³ → ℂ) :=
    Filter.EventuallyEq.of_eq
      (congrArg (fun Y : Lp ℂ 2 (volume : Measure ℝ³) => (Y : ℝ³ → ℂ)) hXeq)
  exact hXae.symm.trans (hae.trans hSae)

/-- The real inner product of `Q` with itself is the `L²` mass: `realIP Q Q = ∫ ‖Q x‖²`. -/
theorem realIP_self_eq_integral {Q : ℝ³ → ℂ} :
    Work.BoseK15.corpusBox.realIP Q Q = ∫ x, ‖Q x‖ ^ 2 := by
  rw [Work.BoseB4.BoxData.realIP_apply]
  refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
  change ((starRingEnd ℂ) (Q x) * Q x).re = ‖Q x‖ ^ 2
  rw [mul_comm, Complex.mul_conj, Complex.normSq_eq_norm_sq]
  exact Complex.ofReal_re _

/-- **The Bessel equality of the box mode**, i.e. the `HonestModes.hphys` pinning read in the
form the expansion lemma needs: `Σ_l ‖√(ℓ³)·f k l‖² = ∫ ‖qVec_k‖²`. -/
theorem sum_normSq_sqrt_mul_f_eq (v : ℝ³ → ℝ) (μ : ℝ) (HM : Work.BoseBoxFock.HonestModes v μ)
    (k : Work.BoseBoxFock.Lab HM.N) :
    (∑ l : Fin HM.m, ‖((Real.sqrt ((Work.BoseBoxFock.ellH v μ) ^ 3) : ℝ) : ℂ)
        * ((HM.f k l : ℝ) : ℂ)‖ ^ 2)
      = ∫ x : ℝ³, ‖Work.BoseK15.corpusBox.qVec (Work.BoseBoxFock.ellH v μ)
          (Work.BoseBoxFock.kmomLab (Work.BoseBoxFock.ellH v μ) HM.N k) x‖ ^ 2 := by
  have hpos : 0 < Work.BoseBoxFock.ellH v μ := Work.BoseBoxFock.ellH_pos v μ
  have hzpow : (Work.BoseBoxFock.ellH v μ) ^ 3 * (Work.BoseBoxFock.ellH v μ) ^ (-(3:ℤ)) = 1 := by
    rw [zpow_neg]
    exact mul_inv_cancel₀ (pow_ne_zero 3 (ne_of_gt hpos))
  have h1 : ∀ l : Fin HM.m,
      ‖((Real.sqrt ((Work.BoseBoxFock.ellH v μ) ^ 3) : ℝ) : ℂ) * ((HM.f k l : ℝ) : ℂ)‖ ^ 2
        = (Real.sqrt ((Work.BoseBoxFock.ellH v μ) ^ 3)) ^ 2 * (HM.f k l) ^ 2 := by
    intro l
    rw [← Complex.ofReal_mul, ← Complex.normSq_eq_norm_sq, Complex.normSq_ofReal]
    ring
  simp only [h1]
  rw [← Finset.mul_sum, Real.sq_sqrt (by positivity)]
  have hgram : (∑ l : Fin HM.m, (HM.f k l) ^ 2) = Work.BoseB4.gram (HM.f k) (HM.f k) := by
    simp [Work.BoseB4.gram, pow_two]
  rw [hgram, HM.hphys k k, realIP_self_eq_integral]
  rw [← mul_assoc, hzpow, one_mul]

theorem qVec_eq_etaOf_of_pairing (v : ℝ³ → ℝ) (μ : ℝ) (HM : Work.BoseBoxFock.HonestModes v μ)
    (e : Fin HM.m → ℝ³ → ℂ)
    (horth : ∀ l l', (∫ x : ℝ³, (starRingEnd ℂ) (e l x) * e l' x)
      = if l = l' then 1 else 0)
    (hpair : ∀ (k : Work.BoseBoxFock.Lab HM.N) (l : Fin HM.m),
      (∫ x : ℝ³, (starRingEnd ℂ) (e l x) *
          Work.BoseK15.corpusBox.qVec (Work.BoseBoxFock.ellH v μ)
            (Work.BoseBoxFock.kmomLab (Work.BoseBoxFock.ellH v μ) HM.N k) x)
        = (((Work.BoseBoxFock.ellH v μ) ^ (3 / 2 : ℝ) * (HM.f k l) : ℝ) : ℂ))
    (hmemE : ∀ l, MeasureTheory.MemLp (e l) 2
      (MeasureTheory.volume : MeasureTheory.Measure ℝ³))
    (hmemQ : ∀ k, MeasureTheory.MemLp
      (Work.BoseK15.corpusBox.qVec (Work.BoseBoxFock.ellH v μ)
        (Work.BoseBoxFock.kmomLab (Work.BoseBoxFock.ellH v μ) HM.N k)) 2
      (MeasureTheory.volume : MeasureTheory.Measure ℝ³))
    (k : Work.BoseBoxFock.Lab HM.N) :
    Work.BoseK15.corpusBox.qVec (Work.BoseBoxFock.ellH v μ)
        (Work.BoseBoxFock.kmomLab (Work.BoseBoxFock.ellH v μ) HM.N k)
      =ᵐ[MeasureTheory.volume] fun x =>
        ((Real.sqrt ((Work.BoseBoxFock.ellH v μ) ^ 3) : ℝ) : ℂ) *
          Work.BoseDict.etaOf e (HM.f k) x := by
  classical
  have hsqrt : Real.sqrt ((Work.BoseBoxFock.ellH v μ) ^ 3)
      = (Work.BoseBoxFock.ellH v μ) ^ (3 / 2 : ℝ) := by
    rw [Real.sqrt_eq_rpow, ← Real.rpow_natCast (Work.BoseBoxFock.ellH v μ) 3,
      ← Real.rpow_mul (le_of_lt (Work.BoseBoxFock.ellH_pos v μ))]
    norm_num
  have hpair' : ∀ l : Fin HM.m,
      (∫ x : ℝ³, (starRingEnd ℂ) (e l x) *
          Work.BoseK15.corpusBox.qVec (Work.BoseBoxFock.ellH v μ)
            (Work.BoseBoxFock.kmomLab (Work.BoseBoxFock.ellH v μ) HM.N k) x)
        = ((Real.sqrt ((Work.BoseBoxFock.ellH v μ) ^ 3) : ℝ) : ℂ) * ((HM.f k l : ℝ) : ℂ) := by
    intro l
    rw [hpair k l, Complex.ofReal_mul, ← hsqrt]
  have hmain := eq_etaOf_of_pairing (e := e)
      (Q := fun x : ℝ³ => Work.BoseK15.corpusBox.qVec (Work.BoseBoxFock.ellH v μ)
            (Work.BoseBoxFock.kmomLab (Work.BoseBoxFock.ellH v μ) HM.N k) x)
      (c := fun l : Fin HM.m => ((Real.sqrt ((Work.BoseBoxFock.ellH v μ) ^ 3) : ℝ) : ℂ)
              * ((HM.f k l : ℝ) : ℂ))
      horth hpair' hmemE (hmemQ k) (sum_normSq_sqrt_mul_f_eq v μ HM k)
  refine hmain.trans ?_
  filter_upwards with x
  rw [Work.BoseDict.etaOf, Finset.mul_sum]
  refine Finset.sum_congr rfl (fun l _ => ?_)
  ring

end Work.BoseBoxFock
