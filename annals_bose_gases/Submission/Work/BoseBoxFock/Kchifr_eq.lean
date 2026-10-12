import ChallengeDeps
import Mathlib.Analysis.CStarAlgebra.Classes
import Submission.Work.BoseBoxFock.W1_chatChi_latticeSum_eq
import Submission.Work.BoseBoxFock.pcfFrameDefs
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Work.BoseBoxFock.Kchifr_eq` — the `χ̂`-weighted `k`-frame evaluated

`Kχfr v h μ fu N z = Σ_{k∈excited} Ŵ₁(k)χ̂(ℓk)e^{i⟨kmom k,z⟩}` is the `χ̂`-weighted frame of the
cubic dictionary (`pcfFrameDefs`).  Its *evaluation* is a direct instance of the Poisson sampling
identity `Work.BoseBoxFock.W1_chatChi_latticeSum_eq` at the box side `ℓ = ellH v μ`
(`= sideAt μ (a v)` under the hypothesis `hℓ0`) and at the point `y = -z`: the `excited`-sum is
the full lattice sum with the zero mode removed, the removed zero mode is the subtracted constant
`uvCut 0 · Ŵ₁(0)`, and the two exponentials `e^{-i⟨k,(y∓w)⟩}` combine into the cosine of the
sampling formula.

This file is the `χ̂`-weighted twin of `Work.BoseBoxFock.Kfr_eq`; the two elementary bricks
(zero label carries momentum `0`, an `excited`-sum is a lattice sum with the zero mode dropped)
are reproduced here so that this file's import cone stays exactly the statement's.
-/

noncomputable section

open scoped BigOperators

namespace Work.BoseBoxFock

set_option autoImplicit false

/-- A sum over the excited modes is the lattice sum with the zero mode dropped. -/
private lemma sum_excited_eq_sum_ite_Kchi {M : Type*} [AddCommGroup M] (N : ℕ) (f : Lab N → M) :
    (∑ k ∈ Work.BoseB7.excited (Lab N), f k) = ∑ k : Lab N, (if k = 0 then 0 else f k) := by
  have h1 : (∑ k ∈ Finset.univ.erase (0 : Lab N), f k) = (∑ k : Lab N, f k) - f 0 := by
    rw [eq_sub_iff_add_eq]
    exact Finset.sum_erase_add _ f (Finset.mem_univ 0)
  have h2 : (∑ k : Lab N, (if k = 0 then (0 : M) else f k)) = (∑ k : Lab N, f k) - f 0 := by
    have hpt : ∀ k : Lab N,
        (if k = 0 then (0 : M) else f k) = f k - (if k = 0 then f k else 0) := by
      intro k
      by_cases hk : k = 0 <;> simp [hk]
    calc (∑ k : Lab N, (if k = 0 then (0 : M) else f k))
        = ∑ k : Lab N, (f k - (if k = 0 then f k else 0)) :=
          Finset.sum_congr rfl fun k _ => hpt k
      _ = (∑ k : Lab N, f k) - ∑ k : Lab N, (if k = 0 then f k else 0) :=
          Finset.sum_sub_distrib _ _
      _ = (∑ k : Lab N, f k) - f 0 := by
          rw [Finset.sum_ite_eq' Finset.univ (0 : Lab N) f, if_pos (Finset.mem_univ 0)]
  simp only [Work.BoseB7.excited]
  rw [h1, h2]

theorem Kchifr_eq {v : EuclideanSpace ℝ (Fin 3) → ℝ} {h : Work.UBB.ScatSol v}
    {fu : Work.BoseBoxFix.LowCut} {μ : ℝ} {N : ℕ}
    (hℓ0 : 0 < Work.BoseBox.sideAt μ (BoseGases.a v)) (hN : 1 ≤ N)
    (hI : MeasureTheory.Integrable (Work.BoseFixR.W1fun v h (Work.BoseBoxFock.ellH v μ)))
    (hcs : HasCompactSupport (Work.BoseFixR.W1fun v h (Work.BoseBoxFock.ellH v μ)))
    (hev : ∀ x, Work.BoseFixR.W1fun v h (Work.BoseBoxFock.ellH v μ) (-x)
      = Work.BoseFixR.W1fun v h (Work.BoseBoxFock.ellH v μ) x)
    (z : EuclideanSpace ℝ (Fin 3)) :
    Work.BoseBoxFock.Kχfr v h μ fu N z
      = ((Work.BoseBoxFock.ellH v μ ^ (-3 : ℤ) : ℝ) : ℂ)
        * ∫ w : EuclideanSpace ℝ (Fin 3),
            ((Work.BoseK15.corpusBox.chiLam (Work.BoseBoxFock.ellH v μ) w : ℝ) : ℂ)
              * (1 / 2 : ℂ) *
              (((Work.BoseBoxFock.ellH v μ : ℂ) ^ 3 * (∑' d : Fin 3 → ℤ,
                  ((Work.BoseBoxFock.uvSmear fu
                    (Work.BoseBoxFock.uvRad (Work.BoseBoxFock.ellH v μ) N)
                    (Work.BoseFixR.W1fun v h (Work.BoseBoxFock.ellH v μ))
                    (-z - w + Work.BoseBoxFock.ellH v μ • Work.BoseBoxFock.latVec d) : ℝ) : ℂ))
                - ((Work.BoseBoxFock.uvCut fu
                    (Work.BoseBoxFock.uvRad (Work.BoseBoxFock.ellH v μ) N) 0
                  * Work.BoseFixR.chat (Work.BoseFixR.W1fun v h (Work.BoseBoxFock.ellH v μ)) 0
                  : ℝ) : ℂ))
              + ((Work.BoseBoxFock.ellH v μ : ℂ) ^ 3 * (∑' d : Fin 3 → ℤ,
                  ((Work.BoseBoxFock.uvSmear fu
                    (Work.BoseBoxFock.uvRad (Work.BoseBoxFock.ellH v μ) N)
                    (Work.BoseFixR.W1fun v h (Work.BoseBoxFock.ellH v μ))
                    (-z + w + Work.BoseBoxFock.ellH v μ • Work.BoseBoxFock.latVec d) : ℝ) : ℂ))
                - ((Work.BoseBoxFock.uvCut fu
                    (Work.BoseBoxFock.uvRad (Work.BoseBoxFock.ellH v μ) N) 0
                  * Work.BoseFixR.chat (Work.BoseFixR.W1fun v h (Work.BoseBoxFock.ellH v μ)) 0
                  : ℝ) : ℂ))) := by
  -- the box side is positive, hence `ellH v μ = sideAt μ (a v)`
  have hℓ : 0 < ellH v μ := ellH_pos v μ
  have hside : ellH v μ = Work.BoseBox.sideAt μ (BoseGases.a v) := by
    rw [ellH, if_pos hℓ0]
  -- the Poisson sampling identity at `ℓ = ellH v μ` and `y = -z`
  have hls := W1_chatChi_latticeSum_eq (v := v) (h := h) (ℓ := ellH v μ) hℓ (fu := fu) N hN (-z)
    hI hcs hev
  -- `W1h` is the cut-off weight of the lattice sum
  have hW1h : ∀ k : Lab N, W1h v h μ fu N k
      = uvCut fu (uvRad (ellH v μ) N) (kmomLab (ellH v μ) N k)
        * Work.BoseFixR.chat (Work.BoseFixR.W1fun v h (ellH v μ))
            (kmomLab (ellH v μ) N k) := by
    intro k
    simp only [W1h, ← hside]
  -- `hatChih` is the `χ̂`-weight of the lattice sum
  have hhat : ∀ k : Lab N, hatChih v μ N k
      = Work.BoseK15.corpusBox.hatChi (ellH v μ • kmomLab (ellH v μ) N k) := by
    intro k
    rfl
  -- the two exponentials agree: `e^{i⟨k,z⟩} = e^{-i⟨k,-z⟩}`
  have hz : ∀ k : Lab N,
      Complex.exp (Complex.I * (inner ℝ (kmomLab (ellH v μ) N k) z : ℂ))
        = Complex.exp (-(Complex.I * (inner ℝ (kmomLab (ellH v μ) N k) (-z) : ℂ))) := by
    intro k
    congr 1
    rw [inner_neg_right]
    push_cast
    ring
  -- the two summands: the frame's (`G`, cut-off weight `W1h χ̂`) and the lattice sum's (`T`)
  set G : Lab N → ℂ := fun k => ((W1h v h μ fu N k * hatChih v μ N k : ℝ) : ℂ)
      * Complex.exp (Complex.I * (inner ℝ (kmomLab (ellH v μ) N k) z : ℂ)) with hG
  set T : Lab N → ℂ := fun k =>
      ((uvCut fu (uvRad (ellH v μ) N) (kmomLab (ellH v μ) N k)
        * Work.BoseFixR.chat (Work.BoseFixR.W1fun v h (ellH v μ))
            (kmomLab (ellH v μ) N k)
        * Work.BoseK15.corpusBox.hatChi (ellH v μ • kmomLab (ellH v μ) N k) : ℝ) : ℂ)
      * Complex.exp (-(Complex.I * (inner ℝ (kmomLab (ellH v μ) N k) (-z) : ℂ))) with hT
  have hGT : ∀ k : Lab N, G k = T k := by
    intro k
    simp only [hG, hT, hW1h k, hhat k, hz k]
  -- drop the zero mode from the excited sum
  have hsum := sum_excited_eq_sum_ite_Kchi N G
  have hKχ : Kχfr v h μ fu N z = ∑ k ∈ Work.BoseB7.excited (Lab N), G k := rfl
  have hSumT : (∑ k : Lab N, (if k = 0 then 0 else G k))
      = (∑ k : Lab N, (if k = 0 then 0 else T k)) := by
    refine Finset.sum_congr rfl fun k _ => ?_
    by_cases hk : k = 0
    · simp [hk]
    · simp [hk, hGT k]
  rw [hKχ, hsum, hSumT]
  exact hls

end Work.BoseBoxFock
