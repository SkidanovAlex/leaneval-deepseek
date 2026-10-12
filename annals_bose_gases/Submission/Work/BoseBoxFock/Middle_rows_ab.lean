import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.Analysis.InnerProductSpace.PiL2
import Submission.Work.BoseBoxFock.Middle_aux
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Work.BoseBoxFock.Middle_rows_ab` — the `(a)`- and `(b)`-channels of `Middle`

The four-channel split `summand_four_split` of the cubic row's middle kernel `Middle` has two
*purely algebraic* channels — those whose two `pinQ` factors contribute their `χ_Λ`-part:

* `Middle_row_a` — the `(a)`-channel: the two phases factorise **without any evenness input**;
* `Middle_row_b` — the `(b)`-channel: the `y`-slot phase splits off `e^{i⟪κ_k,y⟫}`, which lands on
  the `χ̂`-weighted frame `Kχfr y`.

Both are proved from `PotCubicExpansion.summand_four_split`'s terms, `hsub` (the guarded additivity
of `kmomLab` on the supports) and the plane-wave algebra `Middle_aux.phase1`/`phase2`.
`sorry`-free and axiom-clean.
-/

noncomputable section

open scoped BigOperators
open MeasureTheory

namespace Work.BoseBoxFock

local notation "Ω" => EuclideanSpace ℝ (Fin 3)

set_option autoImplicit false

/-- **The `(a)`-channel**: `Σ_{s,k}fLh(s)W1h(k)·e^{−i⟪κ_{s−k},y⟫}χ(y)·e^{i⟪κ_s,x⟫}θ(x)·e^{−i⟪κ_k,u⟫}χ(u)`
`= Ksfr(x−y)·χ(y)·θ(x)·χ(u)·Kfr(y−u)`. -/
lemma Middle_row_a (v : Ω → ℝ) (h : Work.UBB.ScatSol v) (fc fu : Work.BoseBoxFix.LowCut)
    (μ : ℝ) (N : ℕ) (x y u : Ω)
    (hsub : ∀ s ∈ Work.BoseB7.excited (Lab N), fLh v fc μ N s ≠ 0 →
      ∀ k ∈ Work.BoseB7.excited (Lab N), W1h v h μ fu N k ≠ 0 →
      kmomLab (ellH v μ) N (s - k) = kmomLab (ellH v μ) N s - kmomLab (ellH v μ) N k) :
    (∑ s ∈ Work.BoseB7.excited (Lab N), ∑ k ∈ Work.BoseB7.excited (Lab N),
        ((fLh v fc μ N s * W1h v h μ fu N k : ℝ) : ℂ)
          * (Complex.exp (-(Complex.I * (inner ℝ (kmomLab (ellH v μ) N (s - k)) y : ℂ)))
              * ((Work.BoseK15.corpusBox.chiLam (ellH v μ) y : ℝ) : ℂ)
              * (Complex.exp (Complex.I * (inner ℝ (kmomLab (ellH v μ) N s) x : ℂ))
                * Work.BoseK15.corpusBox.thetaFun (ellH v μ) x)
              * (Complex.exp (-(Complex.I * (inner ℝ (kmomLab (ellH v μ) N k) u : ℂ)))
                * ((Work.BoseK15.corpusBox.chiLam (ellH v μ) u : ℝ) : ℂ))))
      = Ksfr v fc μ N (x - y) * ((Work.BoseK15.corpusBox.chiLam (ellH v μ) y : ℝ) : ℂ)
          * Work.BoseK15.corpusBox.thetaFun (ellH v μ) x
          * ((Work.BoseK15.corpusBox.chiLam (ellH v μ) u : ℝ) : ℂ)
          * Kfr v h μ fu N (y - u) := by
  set ex := Work.BoseB7.excited (Lab N) with hex
  set χy : ℂ := ((Work.BoseK15.corpusBox.chiLam (ellH v μ) y : ℝ) : ℂ) with hχy
  set θx : ℂ := Work.BoseK15.corpusBox.thetaFun (ellH v μ) x with hθx
  set χu : ℂ := ((Work.BoseK15.corpusBox.chiLam (ellH v μ) u : ℝ) : ℂ) with hχu
  rw [show (∑ s ∈ ex, ∑ k ∈ ex,
        ((fLh v fc μ N s * W1h v h μ fu N k : ℝ) : ℂ)
          * (Complex.exp (-(Complex.I * (inner ℝ (kmomLab (ellH v μ) N (s - k)) y : ℂ)))
              * χy
              * (Complex.exp (Complex.I * (inner ℝ (kmomLab (ellH v μ) N s) x : ℂ)) * θx)
              * (Complex.exp (-(Complex.I * (inner ℝ (kmomLab (ellH v μ) N k) u : ℂ))) * χu)))
      = ∑ s ∈ ex, ∑ k ∈ ex,
        ((fLh v fc μ N s * W1h v h μ fu N k : ℝ) : ℂ)
          * ((Complex.exp (Complex.I * (inner ℝ (kmomLab (ellH v μ) N s) (x - y) : ℂ)) * χy * θx)
            * (Complex.exp (Complex.I * (inner ℝ (kmomLab (ellH v μ) N k) (y - u) : ℂ)) * χu)) from by
    refine Finset.sum_congr rfl fun s hs => Finset.sum_congr rfl fun k hk => ?_
    by_cases hw : ((fLh v fc μ N s * W1h v h μ fu N k : ℝ) : ℂ) = 0
    · rw [hw, zero_mul, zero_mul]
    · have hmul : fLh v fc μ N s * W1h v h μ fu N k ≠ 0 := by simpa using hw
      have hcs : fLh v fc μ N s ≠ 0 := fun hh => hmul (by rw [hh, zero_mul])
      have hdk : W1h v h μ fu N k ≠ 0 := fun hh => hmul (by rw [hh, mul_zero])
      rw [hsub s hs hcs k hk hdk, phase1]]
  rw [show (∑ s ∈ ex, ∑ k ∈ ex,
        ((fLh v fc μ N s * W1h v h μ fu N k : ℝ) : ℂ)
          * ((Complex.exp (Complex.I * (inner ℝ (kmomLab (ellH v μ) N s) (x - y) : ℂ)) * χy * θx)
            * (Complex.exp (Complex.I * (inner ℝ (kmomLab (ellH v μ) N k) (y - u) : ℂ)) * χu)))
      = (∑ s ∈ ex, ((fLh v fc μ N s : ℝ) : ℂ)
            * (Complex.exp (Complex.I * (inner ℝ (kmomLab (ellH v μ) N s) (x - y) : ℂ)) * χy * θx))
        * (∑ k ∈ ex, ((W1h v h μ fu N k : ℝ) : ℂ)
            * (Complex.exp (Complex.I * (inner ℝ (kmomLab (ellH v μ) N k) (y - u) : ℂ)) * χu)) from by
    rw [Finset.sum_mul_sum]
    refine Finset.sum_congr rfl fun s _ => Finset.sum_congr rfl fun k _ => ?_
    rw [Complex.ofReal_mul]; ring]
  rw [show (∑ s ∈ ex, ((fLh v fc μ N s : ℝ) : ℂ)
        * (Complex.exp (Complex.I * (inner ℝ (kmomLab (ellH v μ) N s) (x - y) : ℂ)) * χy * θx))
      = Ksfr v fc μ N (x - y) * (χy * θx) from by
    rw [show (∑ s ∈ ex, ((fLh v fc μ N s : ℝ) : ℂ)
          * (Complex.exp (Complex.I * (inner ℝ (kmomLab (ellH v μ) N s) (x - y) : ℂ)) * χy * θx))
        = (∑ s ∈ ex, ((fLh v fc μ N s : ℝ) : ℂ)
            * Complex.exp (Complex.I * (inner ℝ (kmomLab (ellH v μ) N s) (x - y) : ℂ))) * (χy * θx) from by
      rw [Finset.sum_mul]
      exact Finset.sum_congr rfl fun s _ => by ring]
    rw [show (∑ s ∈ ex, ((fLh v fc μ N s : ℝ) : ℂ)
            * Complex.exp (Complex.I * (inner ℝ (kmomLab (ellH v μ) N s) (x - y) : ℂ)))
          = Ksfr v fc μ N (x - y) from by
      simp only [ex, Ksfr]]]
  rw [show (∑ k ∈ ex, ((W1h v h μ fu N k : ℝ) : ℂ)
        * (Complex.exp (Complex.I * (inner ℝ (kmomLab (ellH v μ) N k) (y - u) : ℂ)) * χu))
      = Kfr v h μ fu N (y - u) * χu from by
    rw [show (∑ k ∈ ex, ((W1h v h μ fu N k : ℝ) : ℂ)
          * (Complex.exp (Complex.I * (inner ℝ (kmomLab (ellH v μ) N k) (y - u) : ℂ)) * χu))
        = (∑ k ∈ ex, ((W1h v h μ fu N k : ℝ) : ℂ)
            * Complex.exp (Complex.I * (inner ℝ (kmomLab (ellH v μ) N k) (y - u) : ℂ))) * χu from by
      rw [Finset.sum_mul]
      exact Finset.sum_congr rfl fun k _ => by ring]
    rw [show (∑ k ∈ ex, ((W1h v h μ fu N k : ℝ) : ℂ)
            * Complex.exp (Complex.I * (inner ℝ (kmomLab (ellH v μ) N k) (y - u) : ℂ)))
          = Kfr v h μ fu N (y - u) from by
      simp only [ex, Kfr]]]
  ring

/-- **The `(b)`-channel**:
`Σ_{s,k}fLh(s)W1h(k)·e^{−i⟪κ_{s−k},y⟫}χ(y)·e^{i⟪κ_s,x⟫}θ(x)·χ̂(ℓκ_k)θ(u)`
`= Ksfr(x−y)·χ(y)·θ(x)·θ(u)·Kχfr(y)`. -/
lemma Middle_row_b (v : Ω → ℝ) (h : Work.UBB.ScatSol v) (fc fu : Work.BoseBoxFix.LowCut)
    (μ : ℝ) (N : ℕ) (x y u : Ω)
    (hsub : ∀ s ∈ Work.BoseB7.excited (Lab N), fLh v fc μ N s ≠ 0 →
      ∀ k ∈ Work.BoseB7.excited (Lab N), W1h v h μ fu N k ≠ 0 →
      kmomLab (ellH v μ) N (s - k) = kmomLab (ellH v μ) N s - kmomLab (ellH v μ) N k) :
    (∑ s ∈ Work.BoseB7.excited (Lab N), ∑ k ∈ Work.BoseB7.excited (Lab N),
        ((fLh v fc μ N s * W1h v h μ fu N k : ℝ) : ℂ)
          * (Complex.exp (-(Complex.I * (inner ℝ (kmomLab (ellH v μ) N (s - k)) y : ℂ)))
              * ((Work.BoseK15.corpusBox.chiLam (ellH v μ) y : ℝ) : ℂ)
              * (Complex.exp (Complex.I * (inner ℝ (kmomLab (ellH v μ) N s) x : ℂ))
                * Work.BoseK15.corpusBox.thetaFun (ellH v μ) x)
              * (((Work.BoseK15.corpusBox.hatChi ((ellH v μ) • kmomLab (ellH v μ) N k) : ℝ) : ℂ)
                * Work.BoseK15.corpusBox.thetaFun (ellH v μ) u)))
      = Ksfr v fc μ N (x - y) * ((Work.BoseK15.corpusBox.chiLam (ellH v μ) y : ℝ) : ℂ)
          * Work.BoseK15.corpusBox.thetaFun (ellH v μ) x
          * Work.BoseK15.corpusBox.thetaFun (ellH v μ) u
          * Kχfr v h μ fu N y := by
  set ex := Work.BoseB7.excited (Lab N) with hex
  set χy : ℂ := ((Work.BoseK15.corpusBox.chiLam (ellH v μ) y : ℝ) : ℂ) with hχy
  set θx : ℂ := Work.BoseK15.corpusBox.thetaFun (ellH v μ) x with hθx
  set θu : ℂ := Work.BoseK15.corpusBox.thetaFun (ellH v μ) u with hθu
  rw [show (∑ s ∈ ex, ∑ k ∈ ex,
        ((fLh v fc μ N s * W1h v h μ fu N k : ℝ) : ℂ)
          * (Complex.exp (-(Complex.I * (inner ℝ (kmomLab (ellH v μ) N (s - k)) y : ℂ)))
              * χy
              * (Complex.exp (Complex.I * (inner ℝ (kmomLab (ellH v μ) N s) x : ℂ)) * θx)
              * (((Work.BoseK15.corpusBox.hatChi ((ellH v μ) • kmomLab (ellH v μ) N k) : ℝ) : ℂ) * θu)))
      = ∑ s ∈ ex, ∑ k ∈ ex,
        ((fLh v fc μ N s * W1h v h μ fu N k : ℝ) : ℂ)
          * ((Complex.exp (Complex.I * (inner ℝ (kmomLab (ellH v μ) N s) (x - y) : ℂ)) * χy * θx)
            * (Complex.exp (Complex.I * (inner ℝ (kmomLab (ellH v μ) N k) y : ℂ))
                * ((Work.BoseK15.corpusBox.hatChi ((ellH v μ) • kmomLab (ellH v μ) N k) : ℝ) : ℂ) * θu)) from by
    refine Finset.sum_congr rfl fun s hs => Finset.sum_congr rfl fun k hk => ?_
    by_cases hw : ((fLh v fc μ N s * W1h v h μ fu N k : ℝ) : ℂ) = 0
    · rw [hw, zero_mul, zero_mul]
    · have hmul : fLh v fc μ N s * W1h v h μ fu N k ≠ 0 := by simpa using hw
      have hcs : fLh v fc μ N s ≠ 0 := fun hh => hmul (by rw [hh, zero_mul])
      have hdk : W1h v h μ fu N k ≠ 0 := fun hh => hmul (by rw [hh, mul_zero])
      rw [hsub s hs hcs k hk hdk, phase2]]
  rw [show (∑ s ∈ ex, ∑ k ∈ ex,
        ((fLh v fc μ N s * W1h v h μ fu N k : ℝ) : ℂ)
          * ((Complex.exp (Complex.I * (inner ℝ (kmomLab (ellH v μ) N s) (x - y) : ℂ)) * χy * θx)
            * (Complex.exp (Complex.I * (inner ℝ (kmomLab (ellH v μ) N k) y : ℂ))
                * ((Work.BoseK15.corpusBox.hatChi ((ellH v μ) • kmomLab (ellH v μ) N k) : ℝ) : ℂ) * θu)))
      = (∑ s ∈ ex, ((fLh v fc μ N s : ℝ) : ℂ)
            * (Complex.exp (Complex.I * (inner ℝ (kmomLab (ellH v μ) N s) (x - y) : ℂ)) * χy * θx))
        * (∑ k ∈ ex, ((W1h v h μ fu N k : ℝ) : ℂ)
            * (Complex.exp (Complex.I * (inner ℝ (kmomLab (ellH v μ) N k) y : ℂ))
                * ((Work.BoseK15.corpusBox.hatChi ((ellH v μ) • kmomLab (ellH v μ) N k) : ℝ) : ℂ) * θu)) from by
    rw [Finset.sum_mul_sum]
    refine Finset.sum_congr rfl fun s _ => Finset.sum_congr rfl fun k _ => ?_
    rw [Complex.ofReal_mul]; ring]
  rw [show (∑ s ∈ ex, ((fLh v fc μ N s : ℝ) : ℂ)
        * (Complex.exp (Complex.I * (inner ℝ (kmomLab (ellH v μ) N s) (x - y) : ℂ)) * χy * θx))
      = Ksfr v fc μ N (x - y) * (χy * θx) from by
    rw [show (∑ s ∈ ex, ((fLh v fc μ N s : ℝ) : ℂ)
          * (Complex.exp (Complex.I * (inner ℝ (kmomLab (ellH v μ) N s) (x - y) : ℂ)) * χy * θx))
        = (∑ s ∈ ex, ((fLh v fc μ N s : ℝ) : ℂ)
            * Complex.exp (Complex.I * (inner ℝ (kmomLab (ellH v μ) N s) (x - y) : ℂ))) * (χy * θx) from by
      rw [Finset.sum_mul]
      exact Finset.sum_congr rfl fun s _ => by ring]
    rw [show (∑ s ∈ ex, ((fLh v fc μ N s : ℝ) : ℂ)
            * Complex.exp (Complex.I * (inner ℝ (kmomLab (ellH v μ) N s) (x - y) : ℂ)))
          = Ksfr v fc μ N (x - y) from by
      simp only [ex, Ksfr]]]
  rw [show (∑ k ∈ ex, ((W1h v h μ fu N k : ℝ) : ℂ)
        * (Complex.exp (Complex.I * (inner ℝ (kmomLab (ellH v μ) N k) y : ℂ))
            * ((Work.BoseK15.corpusBox.hatChi ((ellH v μ) • kmomLab (ellH v μ) N k) : ℝ) : ℂ) * θu))
      = Kχfr v h μ fu N y * θu from by
    rw [show (∑ k ∈ ex, ((W1h v h μ fu N k : ℝ) : ℂ)
          * (Complex.exp (Complex.I * (inner ℝ (kmomLab (ellH v μ) N k) y : ℂ))
              * ((Work.BoseK15.corpusBox.hatChi ((ellH v μ) • kmomLab (ellH v μ) N k) : ℝ) : ℂ) * θu))
        = (∑ k ∈ ex, ((W1h v h μ fu N k : ℝ) : ℂ)
            * (Complex.exp (Complex.I * (inner ℝ (kmomLab (ellH v μ) N k) y : ℂ))
              * ((Work.BoseK15.corpusBox.hatChi ((ellH v μ) • kmomLab (ellH v μ) N k) : ℝ) : ℂ))) * θu from by
      rw [Finset.sum_mul]
      exact Finset.sum_congr rfl fun k _ => by ring]
    rw [show (∑ k ∈ ex, ((W1h v h μ fu N k : ℝ) : ℂ)
            * (Complex.exp (Complex.I * (inner ℝ (kmomLab (ellH v μ) N k) y : ℂ))
              * ((Work.BoseK15.corpusBox.hatChi ((ellH v μ) • kmomLab (ellH v μ) N k) : ℝ) : ℂ)))
          = ∑ k ∈ ex, (((W1h v h μ fu N k * Work.BoseK15.corpusBox.hatChi
                ((ellH v μ) • kmomLab (ellH v μ) N k) : ℝ)) : ℂ)
              * Complex.exp (Complex.I * (inner ℝ (kmomLab (ellH v μ) N k) y : ℂ)) from by
      refine Finset.sum_congr rfl fun k _ => ?_
      rw [Complex.ofReal_mul]; ring]
    simp only [ex, Kχfr, hatChih]]
  ring

end Work.BoseBoxFock
