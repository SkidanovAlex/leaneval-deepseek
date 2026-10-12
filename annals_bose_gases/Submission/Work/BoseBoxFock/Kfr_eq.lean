import ChallengeDeps
import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.Data.ZMod.ValMinAbs
import Submission.Work.BoseBoxFock.W1_latticeSum_eq
import Submission.Work.BoseBoxFock.pcfFrameDefs
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Work.BoseBoxFock.Kfr_eq` — the `k`-frame evaluated by the lattice sum of `W₁`

`Kfr v h μ fu N z = Σ_{k ∈ excited (Lab N)} W1h k · e^{i⟨kmom k, z⟩}` is the `k`-frame of the
cubic dictionary (`pcfFrameDefs`).  Its *evaluation* is a direct instance of the Poisson sampling
identity `Work.BoseBoxFock.W1_latticeSum_eq` at the box side `ℓ = ellH v μ` (`= sideAt μ (a v)`
under the hypothesis `hℓ0`): the `excited`-sum is the full lattice sum with the zero mode removed,
and the removed zero mode is exactly the subtracted constant `W1h 0`.

The two elementary bricks used are proved here (`private`): the zero label carries momentum `0`,
and a sum over `excited` is a lattice sum with the zero mode dropped.
-/

noncomputable section

open scoped BigOperators

namespace Work.BoseBoxFock

set_option autoImplicit false

/-- The label `0` of the cube carries momentum `0`: `kmomLab ℓ N 0 = 0`.
(A local copy of `GramVDefs.kmomLab_zero`, to keep this file's import cone unchanged.) -/
private lemma kmomLab_zero_Kfr (ℓ : ℝ) (N : ℕ) : kmomLab ℓ N (0 : Lab N) = 0 := by
  have h0 : labVec N (0 : Lab N) = 0 := by
    funext i
    simp [labVec]
  rw [kmomLab, h0]
  ext i
  simp [Work.BoseB4.vec]

/-- A sum over the excited modes is the lattice sum with the zero mode dropped. -/
private lemma sum_excited_eq_sum_ite_Kfr {M : Type*} [AddCommGroup M] (N : ℕ) (f : Lab N → M) :
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

theorem Kfr_eq {v : EuclideanSpace ℝ (Fin 3) → ℝ} {h : Work.UBB.ScatSol v}
    {fu : Work.BoseBoxFix.LowCut} {μ : ℝ} {N : ℕ}
    (hℓ0 : 0 < Work.BoseBox.sideAt μ (BoseGases.a v))
    (hI : MeasureTheory.Integrable (Work.BoseFixR.W1fun v h (Work.BoseBoxFock.ellH v μ)))
    (hcs : HasCompactSupport (Work.BoseFixR.W1fun v h (Work.BoseBoxFock.ellH v μ)))
    (hev : ∀ x, Work.BoseFixR.W1fun v h (Work.BoseBoxFock.ellH v μ) (-x)
      = Work.BoseFixR.W1fun v h (Work.BoseBoxFock.ellH v μ) x)
    (hN1 : 1 ≤ N) (z : EuclideanSpace ℝ (Fin 3)) :
    Work.BoseBoxFock.Kfr v h μ fu N z
      = ((Work.BoseBoxFock.ellH v μ : ℂ)) ^ 3 * (∑' d : Fin 3 → ℤ,
          ((Work.BoseBoxFock.uvSmear fu (Work.BoseBoxFock.uvRad (Work.BoseBoxFock.ellH v μ) N)
            (Work.BoseFixR.W1fun v h (Work.BoseBoxFock.ellH v μ))
            (z + (Work.BoseBoxFock.ellH v μ) • Work.BoseBoxFock.latVec d) : ℝ) : ℂ))
        - ((Work.BoseBoxFock.W1h v h μ fu N 0 : ℝ) : ℂ) := by
  -- the box side is positive, hence `ellH v μ = sideAt μ (a v)`
  have hℓ : 0 < ellH v μ := ellH_pos v μ
  have hside : ellH v μ = Work.BoseBox.sideAt μ (BoseGases.a v) := by
    rw [ellH, if_pos hℓ0]
  -- the Poisson sampling identity at `ℓ = ellH v μ`
  have hls := W1_latticeSum_eq (v := v) (h := h) (ℓ := ellH v μ) hℓ (fu := fu) N hN1 z
    hI hcs hev
  -- `W1h` is the cut-off weight of the lattice sum
  have hW1h : ∀ k : Lab N, W1h v h μ fu N k
      = uvCut fu (uvRad (ellH v μ) N) (kmomLab (ellH v μ) N k)
        * Work.BoseFixR.chat (Work.BoseFixR.W1fun v h (ellH v μ))
            (kmomLab (ellH v μ) N k) := by
    intro k
    simp only [W1h, ← hside]
  have hZ0 : W1h v h μ fu N 0 = uvCut fu (uvRad (ellH v μ) N) 0
      * Work.BoseFixR.chat (Work.BoseFixR.W1fun v h (ellH v μ)) 0 := by
    rw [hW1h 0, kmomLab_zero_Kfr]
  -- the two summands: the frame's (`G`, cut-off weight `W1h`) and the lattice sum's (`T`)
  set G : Lab N → ℂ := fun k => ((W1h v h μ fu N k : ℝ) : ℂ)
      * Complex.exp (Complex.I * (inner ℝ (kmomLab (ellH v μ) N k) z : ℂ)) with hG
  set T : Lab N → ℂ := fun k =>
      ((uvCut fu (uvRad (ellH v μ) N) (kmomLab (ellH v μ) N k)
        * Work.BoseFixR.chat (Work.BoseFixR.W1fun v h (ellH v μ))
            (kmomLab (ellH v μ) N k) : ℝ) : ℂ)
      * Complex.exp (Complex.I * (inner ℝ (kmomLab (ellH v μ) N k) z : ℂ)) with hT
  have hGT : ∀ k : Lab N, G k = T k := by
    intro k
    simp only [hG, hT, hW1h k]
  -- drop the zero mode from the excited sum
  have hsum : (∑ k ∈ Work.BoseB7.excited (Lab N), G k)
      = ∑ k : Lab N, (if k = 0 then 0 else G k) := sum_excited_eq_sum_ite_Kfr N G
  -- the lattice sum in the vocabulary of `T`
  have hlsT : (∑ k : Lab N, (if k = 0 then 0 else T k))
      = ((ellH v μ : ℂ)) ^ 3 * (∑' d : Fin 3 → ℤ,
          ((uvSmear fu (uvRad (ellH v μ) N) (Work.BoseFixR.W1fun v h (ellH v μ))
            (z + (ellH v μ) • latVec d) : ℝ) : ℂ))
        - ((uvCut fu (uvRad (ellH v μ) N) 0
            * Work.BoseFixR.chat (Work.BoseFixR.W1fun v h (ellH v μ)) 0 : ℝ) : ℂ) := by
    rw [hT]
    exact hls
  have hKfr : Kfr v h μ fu N z = ∑ k ∈ Work.BoseB7.excited (Lab N), G k := rfl
  calc Kfr v h μ fu N z
      = ∑ k ∈ Work.BoseB7.excited (Lab N), G k := hKfr
    _ = ∑ k : Lab N, (if k = 0 then 0 else G k) := hsum
    _ = ∑ k : Lab N, (if k = 0 then 0 else T k) := by
        refine Finset.sum_congr rfl fun k _ => ?_
        by_cases hk : k = 0
        · simp [hk]
        · simp [hk, hGT k]
    _ = ((ellH v μ : ℂ)) ^ 3 * (∑' d : Fin 3 → ℤ,
          ((uvSmear fu (uvRad (ellH v μ) N) (Work.BoseFixR.W1fun v h (ellH v μ))
            (z + (ellH v μ) • latVec d) : ℝ) : ℂ))
        - ((uvCut fu (uvRad (ellH v μ) N) 0
            * Work.BoseFixR.chat (Work.BoseFixR.W1fun v h (ellH v μ)) 0 : ℝ) : ℂ) := hlsT
    _ = ((ellH v μ : ℂ)) ^ 3 * (∑' d : Fin 3 → ℤ,
          ((uvSmear fu (uvRad (ellH v μ) N) (Work.BoseFixR.W1fun v h (ellH v μ))
            (z + (ellH v μ) • latVec d) : ℝ) : ℂ))
        - ((W1h v h μ fu N 0 : ℝ) : ℂ) := by rw [hZ0]

end Work.BoseBoxFock
