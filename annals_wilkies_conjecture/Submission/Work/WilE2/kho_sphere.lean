/-
  Work.WilE2 — the "sphere" / properness step of the Khovanskii induction.

  Given a system `S, F` (`n` equations in `n` variables, chain of `s+1` functions) with a
  finite set `T` of nondegenerate zeros, this produces a system in `n+1` variables, still
  with `s+1` chain functions, whose *lifted* system map is proper, with a finite set `T'` of
  nondegenerate zeros of size `2 * T.card`, at the cost of two extra total degree.

  Construction (the paper's claim "G-proper"): keep the same chain (extended by a coordinate
  on which it does not depend, `ESys.ravel`), transport each old equation to `n+1` coordinates
  (`embedP`), and add the sphere equation `∑ x_k² + ψ_{s+1}² = c` as the last component.
  Choosing `c = 1 + ∑_{x ∈ T} (‖x‖² + ψ_{s+1}(x)²)` makes `c - ‖x‖² - ψ_{s+1}(x)² > 0` for
  `x ∈ T`, so each old zero gives two new ones `x_n = ±√(c - ‖x‖² - ψ_{s+1}(x)²)`; the extra
  component of the *lifted* map is `∑ w_j² - c`, hence coercive, which makes that map proper.

  The delegated pieces live in the sibling modules
  `isProperMap_of_sq_sum_component`, `continuous_liftSystem`, `det_ne_zero_of_lastCol_zero`,
  `ravel_embedP`, `spherePoly_facts`, `liftSystem_last_apply`, `two_mul_card_le_card_newT`;
  the shared vocabulary is in `KhoSphereDefs`.
-/
import Mathlib
import Submission.Work.WilE2.KhoSphereDefs
import Submission.Work.WilE2.isProperMap_of_sq_sum_component
import Submission.Work.WilE2.continuous_liftSystem
import Submission.Work.WilE2.det_ne_zero_of_lastCol_zero
import Submission.Work.WilE2.ravel_embedP
import Submission.Work.WilE2.spherePoly_facts
import Submission.Work.WilE2.liftSystem_last_apply
import Submission.Work.WilE2.two_mul_card_le_card_newT

set_option autoImplicit false
set_option maxHeartbeats 4000000

noncomputable section
open Classical
namespace Work.WilE2

open WilkiesDesign WilkiesDesign.E WilkiesConjecture

variable {n s : ℕ}

/-! ## Positivity of the sphere constant on `T` -/

theorem fT_nonneg (S : ESys n (s + 1)) (x : Fin n → ℝ) : 0 ≤ fT S x := by
  have h1 : 0 ≤ ∑ k : Fin n, (x k) ^ 2 := Finset.sum_nonneg fun k _ => sq_nonneg _
  have h2 : 0 ≤ (S.psi (Fin.last s) x) ^ 2 := sq_nonneg _
  rw [fT]
  linarith

theorem khoC_sub_pos (S : ESys n (s + 1)) (T : Finset (Fin n → ℝ)) {x : Fin n → ℝ}
    (hx : x ∈ T) : 0 < khoC S T - fT S x := by
  have hsub : ({x} : Finset (Fin n → ℝ)) ⊆ T := by
    intro y hy
    rw [Finset.mem_singleton] at hy
    subst hy
    exact hx
  have hle : fT S x ≤ ∑ y ∈ T, fT S y := by
    have h2 := Finset.sum_le_sum_of_subset_of_nonneg hsub (fun y _ _ => fT_nonneg S y)
    simpa using h2
  rw [khoC]
  linarith

/-! ## The two nondegenerate points over an old zero -/

/-- If `t ≠ 0` and `t² = c - fT S x`, then `Fin.snoc x t` is a nondegenerate zero of the new
system `S.ravel, newF F c`. -/
theorem nondegen_snoc (S : ESys n (s + 1)) (F : Fin n → EPoly n (s + 1)) (c : ℝ)
    {x : Fin n → ℝ} (hx : S.Nondegen F x) {t : ℝ} (htsq : t ^ 2 = c - fT S x)
    (ht : t ≠ 0) : (S.ravel).Nondegen (newF F c) (Fin.snoc x t) := by
  constructor
  · intro i
    revert i
    refine Fin.lastCases ?_ ?_
    · rw [newF_last, (spherePoly_facts S c).2.1 (Fin.snoc x t)]
      have hsum : (∑ k : Fin (n + 1), ((Fin.snoc x t) k) ^ 2)
          = (∑ k : Fin n, (x k) ^ 2) + t ^ 2 := by
        rw [Fin.sum_univ_castSucc]
        simp [Fin.snoc_castSucc, Fin.snoc_last]
      rw [hsum, Fin.init_snoc, htsq, fT]
      ring
    · intro i
      rw [newF_castSucc, (ravel_embedP S (F i)).1 (Fin.snoc x t), Fin.init_snoc]
      exact hx.1 i
  · set M : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ :=
      Matrix.of fun i j => (S.ravel).ev ((S.ravel).d j (newF F c i)) (Fin.snoc x t) with hM
    have h0 : ∀ i : Fin n, M (Fin.castSucc i) (Fin.last n) = 0 := by
      intro i
      simp only [hM, Matrix.of_apply, newF_castSucc, (ravel_embedP S (F i)).2.2.1]
      simp [ESys.ev]
    have hA : (M.submatrix Fin.castSucc Fin.castSucc).det ≠ 0 := by
      have hmat : M.submatrix Fin.castSucc Fin.castSucc
          = Matrix.of (fun i j => S.ev (S.d j (F i)) x) := by
        ext i j
        simp only [Matrix.submatrix_apply, hM, Matrix.of_apply, newF_castSucc,
          (ravel_embedP S (F i)).2.1 j,
          (ravel_embedP S (S.d j (F i))).1 (Fin.snoc x t), Fin.init_snoc]
      rw [hmat]
      exact hx.2
    have hc : M (Fin.last n) (Fin.last n) ≠ 0 := by
      intro h
      have h2 : (2 : ℝ) * t = 0 := by
        rw [← h]
        simp only [hM, Matrix.of_apply, newF_last, (spherePoly_facts S c).2.2]
        simp [ESys.ev, Fin.snoc_last]
      rcases mul_eq_zero.mp h2 with h3 | h3
      · norm_num at h3
      · exact ht h3
    intro hdet
    exact det_ne_zero_of_lastCol_zero M h0 hA hc hdet

/-! ## The theorem -/

theorem kho_sphere {n s : ℕ} (S : ESys n (s + 1)) (F : Fin n → EPoly n (s + 1))
    (T : Finset (Fin n → ℝ)) (hT : ∀ x ∈ T, S.Nondegen F x) :
    ∃ (S' : ESys (n + 1) (s + 1)) (F' : Fin (n + 1) → EPoly (n + 1) (s + 1))
      (T' : Finset (Fin (n + 1) → ℝ)),
      IsProperMap (liftSystem S' F') ∧ (∀ z ∈ T', S'.Nondegen F' z) ∧
        (∑ i, (F' i).totalDegree) ≤ (∑ i, (F i).totalDegree) + 2 ∧ 2 * T.card ≤ T'.card := by
  refine ⟨S.ravel, newF F (khoC S T), newT S T (khoC S T), ?_, ?_, ?_, ?_⟩
  · refine isProperMap_of_sq_sum_component (khoC S T) (liftSystem S.ravel (newF F (khoC S T)))
      (continuous_liftSystem S.ravel (newF F (khoC S T))) (Fin.last n) ?_
    intro w
    exact liftSystem_last_apply S F (khoC S T) w
  · intro z hz
    rw [newT] at hz
    rcases Finset.mem_biUnion.mp hz with ⟨x, hxT, hxz⟩
    rw [Finset.mem_insert, Finset.mem_singleton] at hxz
    have hpos := khoC_sub_pos S T hxT
    rcases hxz with hz' | hz'
    · rw [hz']
      exact nondegen_snoc S F (khoC S T) (hT x hxT)
        (by rw [Real.sq_sqrt (le_of_lt hpos)]) (ne_of_gt (Real.sqrt_pos.mpr hpos))
    · rw [hz']
      exact nondegen_snoc S F (khoC S T) (hT x hxT)
        (by rw [neg_sq, Real.sq_sqrt (le_of_lt hpos)])
        (neg_ne_zero.mpr (ne_of_gt (Real.sqrt_pos.mpr hpos)))
  · rw [Fin.sum_univ_castSucc]
    have h1 : (∑ i : Fin n, (newF F (khoC S T) (Fin.castSucc i)).totalDegree)
        ≤ ∑ i : Fin n, (F i).totalDegree :=
      Finset.sum_le_sum fun i _ => by
        rw [newF_castSucc]
        exact (ravel_embedP S (F i)).2.2.2
    have h2 : (newF F (khoC S T) (Fin.last n)).totalDegree ≤ 2 := by
      rw [newF_last]
      exact (spherePoly_facts S (khoC S T)).1
    linarith
  · exact two_mul_card_le_card_newT S T (khoC S T) (fun x hx => khoC_sub_pos S T hx)

end Work.WilE2
