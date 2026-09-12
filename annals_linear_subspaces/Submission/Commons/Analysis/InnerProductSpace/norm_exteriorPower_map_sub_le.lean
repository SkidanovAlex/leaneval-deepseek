import Mathlib
import Submission.Commons.Analysis.InnerProductSpace.exteriorPower_norm_wedge_le_prod

set_option linter.unusedVariables false

open scoped BigOperators

namespace Commons.Analysis.InnerProductSpace

/-- Telescoping expansion of the difference of two exterior products of `Fin i`-tuples:
replacing the entries of `x` by those of `y` one at a time. -/
theorem iMulti_sub_eq_sum {i : ℕ} {E : Type*} [AddCommGroup E] [Module ℝ E] (x y : Fin i → E) :
    exteriorPower.ιMulti ℝ i x - exteriorPower.ιMulti ℝ i y =
      ∑ k : Fin i, exteriorPower.ιMulti ℝ i
        (fun j => if j < k then x j else if j = k then x k - y k else y j) := by
  classical
  let c : ℕ → Fin i → E := fun k j => if (j : ℕ) < k then x j else y j
  let g : ℕ → (⋀[ℝ]^i E) := fun k => exteriorPower.ιMulti ℝ i (c k)
  have hc0 : c 0 = y := by funext j; simp [c]
  have hci : c i = x := by funext j; simp [c, j.isLt]
  have hstep : ∀ (k : ℕ) (hk : k < i),
      g (k + 1) - g k = exteriorPower.ιMulti ℝ i
        (fun j => if j < (⟨k, hk⟩ : Fin i) then x j
          else if j = (⟨k, hk⟩ : Fin i) then x ⟨k, hk⟩ - y ⟨k, hk⟩ else y j) := by
    intro k hk
    have hupd : c (k + 1) = Function.update (c k) ⟨k, hk⟩ (x ⟨k, hk⟩) := by
      funext j
      rw [Function.update_apply]
      by_cases h : (j : ℕ) = k
      · have hjk : j = (⟨k, hk⟩ : Fin i) := Fin.ext h
        simp [hjk, c]
      · have hjk : ¬ (j = (⟨k, hk⟩ : Fin i)) := fun hh => h (by rw [hh])
        have hlt : ((j : ℕ) < k + 1) = ((j : ℕ) < k) := by
          apply propext; omega
        simp [hjk, c, hlt]
    have hval : c k ⟨k, hk⟩ = y ⟨k, hk⟩ := by simp [c]
    have hb : c k = Function.update (c k) ⟨k, hk⟩ (y ⟨k, hk⟩) := by
      rw [← hval]
      exact (Function.update_eq_self ⟨k, hk⟩ (c k)).symm
    have hkey : exteriorPower.ιMulti ℝ i (Function.update (c k) ⟨k, hk⟩ (x ⟨k, hk⟩))
        - exteriorPower.ιMulti ℝ i (c k)
        = exteriorPower.ιMulti ℝ i
            (Function.update (c k) ⟨k, hk⟩ (x ⟨k, hk⟩ - y ⟨k, hk⟩)) := by
      rw [congrArg (exteriorPower.ιMulti ℝ i) hb]
      exact (AlternatingMap.map_update_sub (exteriorPower.ιMulti ℝ i) (c k) ⟨k, hk⟩
        (x ⟨k, hk⟩) (y ⟨k, hk⟩)).symm
    simp only [g]
    rw [hupd, hkey]
    apply congrArg (exteriorPower.ιMulti ℝ i)
    funext j
    rw [Function.update_apply]
    by_cases hjk : j = (⟨k, hk⟩ : Fin i)
    · subst hjk
      simp
    · rw [if_neg hjk]
      simp only [c]
      by_cases hlt : (j : ℕ) < k
      · have hjlt : j < (⟨k, hk⟩ : Fin i) := by simpa [Fin.lt_def] using hlt
        simp [hlt, hjlt]
      · have hjlt : ¬ (j < (⟨k, hk⟩ : Fin i)) := by simpa [Fin.lt_def] using hlt
        simp [hlt, hjlt, hjk]
  have hsum : (∑ k : Fin i, (g (k + 1) - g k)) = g i - g 0 := by
    rw [Fin.sum_univ_eq_sum_range (fun k => g (k + 1) - g k) i]
    exact Finset.sum_range_sub g i
  have hmain : (∑ k : Fin i, exteriorPower.ιMulti ℝ i
        (fun j => if j < k then x j else if j = k then x k - y k else y j))
      = exteriorPower.ιMulti ℝ i x - exteriorPower.ιMulti ℝ i y := by
    calc (∑ k : Fin i, exteriorPower.ιMulti ℝ i
            (fun j => if j < k then x j else if j = k then x k - y k else y j))
        = ∑ k : Fin i, (g (k + 1) - g k) := by
          apply Finset.sum_congr rfl
          intro k _
          exact (hstep k k.isLt).symm
      _ = g i - g 0 := hsum
      _ = exteriorPower.ιMulti ℝ i x - exteriorPower.ιMulti ℝ i y := by
          simp [g, hc0, hci]
  exact hmain.symm

/-- Summing the comparison weights `∏_j (if j < k then 1 else if j = k then δ else 1 + δ)`
over `k : Fin i` gives the geometric expression `(1 + δ)^i - 1`. -/
theorem sum_prod_ite_eq (i : ℕ) (δ : ℝ) :
    (∑ k : Fin i, ∏ j : Fin i,
        (if j < k then (1 : ℝ) else if j = k then δ else 1 + δ)) = (1 + δ) ^ i - 1 := by
  induction i with
  | zero => simp
  | succ n ih =>
      have hcast : ∀ k : Fin n,
          (∏ j : Fin (n + 1),
              (if j < k.castSucc then (1 : ℝ) else if j = k.castSucc then δ else 1 + δ))
            = (∏ j : Fin n, (if j < k then (1 : ℝ) else if j = k then δ else 1 + δ))
              * (1 + δ) := by
        intro k
        rw [Fin.prod_univ_castSucc]
        have hlast : ¬ (Fin.last n < k.castSucc) :=
          not_lt.mpr (le_of_lt (Fin.castSucc_lt_last k))
        have hlast2 : ¬ (Fin.last n = k.castSucc) :=
          fun h => (ne_of_lt (Fin.castSucc_lt_last k)) h.symm
        rw [if_neg hlast, if_neg hlast2]
        congr 1
        apply Finset.prod_congr rfl
        intro j _
        simp only [Fin.castSucc_lt_castSucc_iff, Fin.castSucc_inj]
      have hlastP : (∏ j : Fin (n + 1),
            (if j < (Fin.last n) then (1 : ℝ) else if j = Fin.last n then δ else 1 + δ))
          = δ := by
        rw [Fin.prod_univ_castSucc]
        have h1 : (∏ j : Fin n,
            (if j.castSucc < Fin.last n then (1 : ℝ)
              else if j.castSucc = Fin.last n then δ else 1 + δ)) = 1 := by
          apply Finset.prod_eq_one
          intro j _
          rw [if_pos (Fin.castSucc_lt_last j)]
        rw [h1, one_mul]
        rw [if_neg (lt_irrefl (Fin.last n)), if_pos rfl]
      rw [Fin.sum_univ_castSucc, hlastP]
      rw [Finset.sum_congr rfl (fun k _ => hcast k)]
      rw [← Finset.sum_mul, ih, pow_succ]
      ring

/-- If `P` is a linear contraction and `u`, `v` are families of unit vectors with
`‖v k - u k‖ ≤ δ`, then the norms of the induced maps on `i`-fold exterior powers differ by
at most `(1 + δ)^i - 1`. -/
theorem norm_exteriorPower_map_sub_le {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] {i : ℕ} (P : E →L[ℝ] E) (hP1 : ∀ x, ‖P x‖ ≤ ‖x‖)
    (hP2 : ∀ x, P (P x) = P x) {δ : ℝ} (hδ : 0 ≤ δ) (u v : Fin i → E)
    (hu : ∀ k, ‖u k‖ = 1) (hv : ∀ k, ‖v k - u k‖ ≤ δ) :
    ‖exteriorPower.map i (P : E →ₗ[ℝ] E) (exteriorPower.ιMulti ℝ i u)‖ - ((1 + δ) ^ i - 1) ≤
      ‖exteriorPower.map i (P : E →ₗ[ℝ] E) (exteriorPower.ιMulti ℝ i v)‖ := by
  classical
  let x : Fin i → E := fun k => P (u k)
  let y : Fin i → E := fun k => P (v k)
  have hmapu : exteriorPower.map i (P : E →ₗ[ℝ] E) (exteriorPower.ιMulti ℝ i u)
      = exteriorPower.ιMulti ℝ i x := by
    rw [exteriorPower.map_apply_ιMulti]
    congr 1
  have hmapv : exteriorPower.map i (P : E →ₗ[ℝ] E) (exteriorPower.ιMulti ℝ i v)
      = exteriorPower.ιMulti ℝ i y := by
    rw [exteriorPower.map_apply_ιMulti]
    congr 1
  rw [hmapu, hmapv]
  have hx : ∀ k : Fin i, ‖x k‖ ≤ 1 := fun k => by
    calc ‖x k‖ = ‖P (u k)‖ := rfl
      _ ≤ ‖u k‖ := hP1 _
      _ = 1 := hu k
  have hy : ∀ k : Fin i, ‖y k‖ ≤ 1 + δ := fun k => by
    calc ‖y k‖ = ‖P (v k)‖ := rfl
      _ ≤ ‖v k‖ := hP1 _
      _ = ‖(v k - u k) + u k‖ := by rw [sub_add_cancel]
      _ ≤ ‖v k - u k‖ + ‖u k‖ := norm_add_le _ _
      _ ≤ δ + 1 := add_le_add (hv k) (le_of_eq (hu k))
      _ = 1 + δ := by ring
  have hxy : ∀ k : Fin i, ‖x k - y k‖ ≤ δ := fun k => by
    have hsub : x k - y k = P (u k - v k) := by
      simp only [x, y]
      rw [← map_sub]
    rw [hsub]
    calc ‖P (u k - v k)‖ ≤ ‖u k - v k‖ := hP1 _
      _ = ‖v k - u k‖ := by simpa using (norm_neg (u k - v k)).symm
      _ ≤ δ := hv k
  have hterm : ∀ k : Fin i, ‖exteriorPower.ιMulti ℝ i
        (fun j => if j < k then x j else if j = k then x k - y k else y j)‖
      ≤ ∏ j : Fin i, (if j < k then (1 : ℝ) else if j = k then δ else 1 + δ) := by
    intro k
    calc ‖exteriorPower.ιMulti ℝ i
            (fun j => if j < k then x j else if j = k then x k - y k else y j)‖
        ≤ ∏ j : Fin i, ‖if j < k then x j else if j = k then x k - y k else y j‖ :=
          exteriorPower_norm_wedge_le_prod
            (v := fun j => if j < k then x j else if j = k then x k - y k else y j)
      _ ≤ ∏ j : Fin i, (if j < k then (1 : ℝ) else if j = k then δ else 1 + δ) := by
          apply Finset.prod_le_prod
          · intro j _
            exact norm_nonneg _
          · intro j _
            by_cases h1 : j < k
            · rw [if_pos h1, if_pos h1]
              exact hx j
            · by_cases h2 : j = k
              · rw [if_neg h1, if_pos h2, if_neg h1, if_pos h2]
                exact hxy k
              · rw [if_neg h1, if_neg h2, if_neg h1, if_neg h2]
                exact hy j
  have hbound : ‖exteriorPower.ιMulti ℝ i x - exteriorPower.ιMulti ℝ i y‖ ≤ (1 + δ) ^ i - 1 := by
    rw [iMulti_sub_eq_sum (E := E) x y]
    calc ‖∑ k : Fin i, exteriorPower.ιMulti ℝ i
            (fun j => if j < k then x j else if j = k then x k - y k else y j)‖
        ≤ ∑ k : Fin i, ‖exteriorPower.ιMulti ℝ i
            (fun j => if j < k then x j else if j = k then x k - y k else y j)‖ :=
          norm_sum_le Finset.univ _
      _ ≤ ∑ k : Fin i, ∏ j : Fin i,
            (if j < k then (1 : ℝ) else if j = k then δ else 1 + δ) :=
          Finset.sum_le_sum (fun k _ => hterm k)
      _ = (1 + δ) ^ i - 1 := sum_prod_ite_eq i δ
  have hfinal : ‖exteriorPower.ιMulti ℝ i x‖ - ‖exteriorPower.ιMulti ℝ i y‖ ≤ (1 + δ) ^ i - 1 :=
    le_trans (norm_sub_norm_le _ _) hbound
  linarith

end Commons.Analysis.InnerProductSpace
