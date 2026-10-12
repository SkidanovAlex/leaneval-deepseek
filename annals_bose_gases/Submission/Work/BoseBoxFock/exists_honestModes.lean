import Mathlib.Data.ZMod.ValMinAbs
import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.BoseBoxFock.exists_chiLam_zero
import Submission.Work.BoseBoxFock.exists_jointGramLab
import Submission.Work.BoseBoxFock.matrix_solve_of_orthogonal_ker
import Submission.Work.BoseBoxFock.qVec_zero_of_measure
import Submission.Work.BoseBoxFock.sumSq_ccrKernel
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END


/-!
# `Work.BoseBoxFock.exists_honestModes` — BF1: the honest box model exists at every cube size

`exists_honestModes v μ N` produces `HonestModes v μ` with `N` the prescribed cube size
`Lab N = (ZMod (2N+1))³`, i.e. the coordinate model of FS §8's one-particle vectors
`Q(e^{ikx}χ_Λ)` (χ-modes, `f`) and `e^{isx}θ` (θ-modes, `g`) from the *honest* box data
`corpusBox` at the side `ellH v μ`.

The construction:

* `exists_jointGramLab` gives coordinates `f`, `g` for the χ-modes, the θ-modes `s ≠ 0` and
  their cross Gram products;
* the `s = 0` row of `hcross` (which is *not* the condensate overlap: it demands
  `⟨g 0, f k⟩ = χ̂(ℓ K k)`, while the condensate `θ_Λ` is orthogonal to every `qVec`) is
  produced by `matrix_solve_of_orthogonal_ker`, applied to the matrix
  `ccrMat ℓ N` (`= χ̂²(ℓ(K i−K j)) − χ̂(ℓK i)χ̂(ℓK j)`) and the vector `hatChi (ℓ K ·)`:
  its solvability is `ker_ccrMat_orth`, i.e. `sumSq_ccrKernel` (the χ-block quadratic form is
  the squared `L²`-norm of the superposition) combined with `qVec_zero_of_measure` and
  `exists_chiLam_zero` (a superposition of `qVec`s that vanishes a.e. cannot be a nonzero
  multiple of `θ_Λ`, because `χ_Λ` vanishes of the ball of radius `ℓ/2` while `θ_Λ = 1` on
  the corners of the box);
* `Fin.cons 0 ·` embeds the coordinates into one extra dimension, which is exactly what the
  structure asks for in `hf0`/`hg0`.
-/

namespace Work.BoseBoxFock

open scoped BigOperators
open Work.BoseB4

set_option autoImplicit false
set_option linter.unusedVariables false

/-! ## Elementary facts -/

lemma kmomLab_zero (ℓ : ℝ) (N : ℕ) : kmomLab ℓ N 0 = 0 := by
  have hlab : labVec N 0 = 0 := by
    funext i
    show ZMod.valMinAbs ((0 : Lab N) i) = (0 : ℤ)
    rw [show (0 : Lab N) i = (0 : ZMod (2 * N + 1)) from rfl]
    exact (ZMod.valMinAbs_eq_zero (0 : ZMod (2 * N + 1))).mpr rfl
  simp only [kmomLab, hlab]
  have hv : Work.BoseB4.vec (0 : Fin 3 → ℤ) = 0 := by
    ext i
    simp [Work.BoseB4.vec]
  rw [hv, smul_zero]

lemma gram_cons {m : ℕ} (a b : ℝ) (v w : Fin m → ℝ) :
    Work.BoseB4.gram (Fin.cons a v) (Fin.cons b w) = a * b + Work.BoseB4.gram v w := by
  rw [Work.BoseB4.gram, Fin.sum_univ_succ, Work.BoseB4.gram]
  simp [Fin.cons_zero, Fin.cons_succ]

/-! ## The χ-block matrix and its symmetry -/

noncomputable def ccrMat (ℓ : ℝ) (N : ℕ) : Matrix (Lab N) (Lab N) ℝ :=
  Matrix.of (fun i j => Work.BoseB7.ccrKernel ℓ Work.BoseK15.corpusBox.hatChiSq
    Work.BoseK15.corpusBox.hatChi (kmomLab ℓ N i) (kmomLab ℓ N j))

lemma ccrMat_isSymm (ℓ : ℝ) (N : ℕ) : (ccrMat ℓ N).IsSymm := by
  rw [Matrix.IsSymm.ext_iff]
  intro i j
  simp only [ccrMat, Matrix.of_apply, Work.BoseB7.ccrKernel]
  have hev : Work.BoseK15.corpusBox.hatChiSq (ℓ • (kmomLab ℓ N j - kmomLab ℓ N i))
      = Work.BoseK15.corpusBox.hatChiSq (ℓ • (kmomLab ℓ N i - kmomLab ℓ N j)) := by
    rw [show ℓ • (kmomLab ℓ N j - kmomLab ℓ N i)
        = -(ℓ • (kmomLab ℓ N i - kmomLab ℓ N j)) by simp only [smul_sub]; abel,
      Work.BoseB4.BoxData.hatChiSq_neg]
  rw [hev]
  ring

/-! ## The kernel-orthogonality of the χ̂-vector -/

theorem ker_ccrMat_orth (ℓ : ℝ) (hℓ : 0 < ℓ) (N : ℕ) :
    ∀ x : Lab N → ℝ,
      (∀ i, ∑ j, ccrMat ℓ N i j * x j = 0) →
      ∑ i, x i * Work.BoseK15.corpusBox.hatChi (ℓ • kmomLab ℓ N i) = 0 := by
  intro x hx
  -- the quadratic form vanishes
  have hquad : (∑ i, ∑ j, x i * x j *
      Work.BoseB7.ccrKernel ℓ Work.BoseK15.corpusBox.hatChiSq Work.BoseK15.corpusBox.hatChi
        (kmomLab ℓ N i) (kmomLab ℓ N j)) = 0 := by
    have h1 : (∑ i, ∑ j, x i * (ccrMat ℓ N i j * x j)) = 0 := by
      have : ∀ i, (∑ j, x i * (ccrMat ℓ N i j * x j)) = x i * 0 := by
        intro i
        rw [← Finset.mul_sum, hx i, mul_zero]
      rw [Finset.sum_congr rfl fun i _ => this i]
      simp
    rw [← h1]
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
    simp only [ccrMat, Matrix.of_apply]
    ring
  have hint : (∫ y, Complex.normSq (∑ i, (x i : ℂ) *
      Work.BoseK15.corpusBox.qVec ℓ (kmomLab ℓ N i) y)) = 0 := by
    have h := sumSq_ccrKernel ℓ hℓ N (kmomLab ℓ N) x
    rw [hquad, mul_zero] at h
    exact h.symm
  obtain ⟨B, hB, hvol, hchi, htheta⟩ := exists_chiLam_zero ℓ hℓ
  exact qVec_zero_of_measure ℓ hℓ N (kmomLab ℓ N) x hB hvol hchi htheta hint

/-! ## The Gram product of a linear combination -/

lemma gram_sum_smul {ι : Type*} [Fintype ι] {m : ℕ} (x : ι → ℝ)
    (f : ι → Fin m → ℝ) (w : Fin m → ℝ) :
    Work.BoseB4.gram (∑ i, x i • f i) w
      = ∑ i, x i * Work.BoseB4.gram (f i) w := by
  have h1 : ∀ l, (∑ i, x i • f i) l = ∑ i, x i * f i l := by
    intro l
    simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
  simp only [Work.BoseB4.gram, h1]
  trans ∑ l, ∑ i, (x i * f i l) * w l
  · exact Finset.sum_congr rfl fun l _ => Finset.sum_mul _ _ _
  · rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl fun l _ => by ring

/-! ## The main theorem -/

theorem exists_honestModes (v : ℝ³ → ℝ) (μ : ℝ) (N : ℕ) :
    ∃ HM : HonestModes v μ, HM.N = N := by
  set ℓ := ellH v μ with hℓdef
  have hℓ : 0 < ℓ := ellH_pos v μ
  -- the joint coordinate model of the χ- and θ-modes
  obtain ⟨m, f, g, hf, hg, hcross⟩ := exists_jointGramLab v μ N
  -- the solution of the linear system `A x = c` (the `s = 0` row of the cross Gram)
  obtain ⟨x, hx⟩ := matrix_solve_of_orthogonal_ker (ccrMat ℓ N) (ccrMat_isSymm ℓ N)
    (fun i => Work.BoseK15.corpusBox.hatChi (ℓ • kmomLab ℓ N i))
    (fun y hy => by
      have h := ker_ccrMat_orth ℓ hℓ N y hy
      rw [Finset.sum_congr rfl (fun i _ =>
        mul_comm (y i) (Work.BoseK15.corpusBox.hatChi (ℓ • kmomLab ℓ N i)))] at h
      exact h)
  -- the vector realising the `s = 0` cross Gram products
  set u : Fin m → ℝ := ∑ i, x i • f i with hudef
  have hu_inner : ∀ k, Work.BoseB4.gram u (f k)
      = Work.BoseK15.corpusBox.hatChi (ellH v μ • kmomLab (ellH v μ) N k) := by
    intro k
    rw [hudef, gram_sum_smul]
    have h1 : ∀ i, x i * Work.BoseB4.gram (f i) (f k) = x i * ccrMat ℓ N i k := by
      intro i
      rw [hf i k]
      rfl
    rw [Finset.sum_congr rfl fun i _ => h1 i]
    have h2 : ∀ i, ccrMat ℓ N i k = ccrMat ℓ N k i := fun i => (ccrMat_isSymm ℓ N).apply k i
    rw [Finset.sum_congr rfl fun i _ => by rw [h2 i]]
    rw [Finset.sum_congr rfl fun i _ => mul_comm (x i) (ccrMat ℓ N k i)]
    simpa [hℓdef] using hx k
  -- the embedded model
  set F : Lab N → Fin (m + 1) → ℝ := fun k => Fin.cons 0 (f k) with hFdef
  set G : Lab N → Fin (m + 1) → ℝ :=
    fun s => if s = 0 then Fin.cons 0 u else Fin.cons 0 (g s) with hGdef
  have hG_zero : G 0 = Fin.cons 0 u := by rw [hGdef]; simp
  have hG_ne : ∀ s, s ≠ 0 → G s = Fin.cons 0 (g s) := by
    intro s hs; rw [hGdef]; simp [hs]
  have hK0 : kmomLab (ellH v μ) N 0 = 0 := kmomLab_zero (ellH v μ) N
  refine ⟨{ N := N, m := m + 1, f := F, g := G, hf := ?_, hg := ?_, hcross := ?_, hf0 := ?_, hg0 := ?_, hphys := ?_ }, rfl⟩
  · intro i j
    rw [hFdef]
    simp only [gram_cons]
    simpa using hf i j
  · intro s t hs ht
    rw [hG_ne s hs, hG_ne t ht]
    simp only [gram_cons]
    simpa using hg s t hs ht
  · intro s k
    by_cases hs : s = 0
    · subst hs
      rw [hG_zero, hFdef]
      simp only [gram_cons, zero_mul, zero_add]
      rw [hu_inner k]
      congr 1
      rw [hK0, sub_zero]
    · rw [hG_ne s hs, hFdef]
      simp only [gram_cons]
      simpa using hcross s k hs
  · intro k
    rw [hFdef]
    simp
  · intro s hs
    rw [hG_ne s hs]
    simp
  · intro i j
    have h3 : ℓ ^ (-(3 : ℤ)) * ℓ ^ 3 = 1 := by
      rw [← zpow_natCast ℓ 3, ← zpow_add₀ hℓ.ne']
      simp
    have hbox : Work.BoseB4.gram (F i) (F j)
        = Work.BoseB4.BoxData.boxKernel Work.BoseK15.corpusBox ℓ
            (kmomLab ℓ N i) (kmomLab ℓ N j) := by
      rw [hFdef]
      simp only [gram_cons, zero_mul, zero_add]
      have h := hf i j
      simp only [Work.BoseB7.ccrKernel, Work.BoseB4.BoxData.boxKernel] at h ⊢
      exact h
    rw [hbox, Work.BoseB4.realIP_qVec_qVec Work.BoseK15.corpusBox hℓ]
    rw [show ℓ ^ (-(3 : ℤ)) * (ℓ ^ 3 * Work.BoseB4.BoxData.boxKernel Work.BoseK15.corpusBox ℓ
          (kmomLab ℓ N i) (kmomLab ℓ N j))
        = (ℓ ^ (-(3 : ℤ)) * ℓ ^ 3) * Work.BoseB4.BoxData.boxKernel Work.BoseK15.corpusBox ℓ
          (kmomLab ℓ N i) (kmomLab ℓ N j) by ring,
      h3, one_mul]

end Work.BoseBoxFock
