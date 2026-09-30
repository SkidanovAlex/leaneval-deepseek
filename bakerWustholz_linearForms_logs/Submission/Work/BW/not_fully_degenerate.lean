import Mathlib
import Submission.Work.BW.ACBase
import Submission.Work.BW.multiplicity_bound
import Submission.Work.BW.eval_pderiv_iterate_aeval_X

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

namespace Work.BW

/-- Fully degenerate case of `multiplicity_prop` (BW §10, P86* route), closed by contradiction as
instructed by the project lead: if every torus degree bound is `< 1`, then `degreeOf i P = 0` for
every `i ≥ 1`, so `P` lives on `ℂ[Y₀]`; the vanishing hypothesis at `s = 0,…,⌊𝒮⌋` and orders
`t₀ ≤ ⌊𝒯⌋` then forces `deg_{Y₀}P ≥ (⌊𝒯⌋+1)(⌊𝒮⌋+1)`, which contradicts (E1) at `m = 0`
(`(r+1)𝒟₀ < (Sq 0+1)(Tq 0+1)`) together with `∑Sq ≤ 𝒮` and `∑Tq ≤ 𝒯`. Hence the hypotheses of
`multiplicity_prop` cannot hold in this case (in particular the quotient has no torus coordinates
left, so the zero estimate would return `ρ = 0`, which the conclusion forbids).
`obstruction_aux` (in `Submission.Work.BW.analytic_core`) provides the univariate reduction
`P = Q(X₀)` with `Q.natDegree ≤ P.degreeOf 0` and `eval (ptS ℓ s) P = Q.eval s`. -/
theorem not_fully_degenerate {r : ℕ} (hr : 2 ≤ r) (P : MvPolynomial (Fin (r + 1)) ℂ) (hP : P ≠ 0)
    (𝒟 : Fin (r + 1) → ℝ) (hdeg : ∀ j, (P.degreeOf j : ℝ) ≤ 𝒟 j) (h𝒟0 : 1 ≤ 𝒟 0)
    (hlt : ∀ j : Fin r, 𝒟 j.succ < 1) (𝒮 𝒯 : ℝ) (Sq Tq : ℕ → ℕ)
    (hSsum : ((∑ m ∈ Finset.range (r + 1), Sq m : ℕ) : ℝ) ≤ 𝒮)
    (hTsum : ((∑ m ∈ Finset.range (r + 1), Tq m : ℕ) : ℝ) ≤ 𝒯)
    (hE1e0 : ((r : ℝ) + 1) * 𝒟 0 < ((Sq 0 : ℝ) + 1) * ((Tq 0 + 1).choose 1 : ℝ))
    (ℓ : Fin r → ℂ) (c : Fin (r - 1) → Fin r → ℚ)
    (hvan : ∀ s : ℕ, (s : ℝ) ≤ 𝒮 → ∀ (t0 : ℕ) (t : Fin (r - 1) → ℕ),
      ((t0 + ∑ m, t m : ℕ) : ℝ) ≤ 𝒯 →
      MvPolynomial.eval (ptS ℓ s) (applyDer c t0 t P) = 0) :
    False := by
  classical
  -- (i) `P` is constant in the torus variables `Y₁, …, Y_r`: each of their degree bounds is `< 1`.
  have hdeg0 : ∀ j : Fin (r + 1), j ≠ 0 → P.degreeOf j = 0 := by
    intro j hj
    obtain ⟨i, rfl⟩ := Fin.eq_succ_of_ne_zero hj
    exact Nat.cast_lt_one.mp (lt_of_le_of_lt (hdeg i.succ) (hlt i))
  -- (ii) Hence `P = Q(X₀)` for a univariate `Q`, with `Q.natDegree ≤ deg_{Y₀}P`.
  obtain ⟨hQdeg, hQeval, hQP⟩ := obstruction_aux ℓ P hdeg0
  set Q : Polynomial ℂ := ∑ κ ∈ P.support, Polynomial.C (P.coeff κ) * Polynomial.X ^ (κ 0) with hQdef
  have hQne : Q ≠ 0 := fun h0 => hP (by rw [hQP, h0]; simp)
  -- (iii) Floors and the sums `∑Sq ≤ 𝒮`, `∑Tq ≤ 𝒯`.
  have hSnonneg : (0 : ℝ) ≤ 𝒮 := le_trans (by positivity) hSsum
  have hTnonneg : (0 : ℝ) ≤ 𝒯 := le_trans (by positivity) hTsum
  have hSq_le : Sq 0 ≤ ⌊𝒮⌋₊ := by
    apply Nat.le_floor
    refine le_trans ?_ hSsum
    exact_mod_cast Finset.single_le_sum (f := Sq) (fun _ _ => Nat.zero_le _)
      (Finset.mem_range.mpr (by omega))
  have hTq_le : Tq 0 ≤ ⌊𝒯⌋₊ := by
    apply Nat.le_floor
    refine le_trans ?_ hTsum
    exact_mod_cast Finset.single_le_sum (f := Tq) (fun _ _ => Nat.zero_le _)
      (Finset.mem_range.mpr (by omega))
  -- (iv) `hvan` with all `t m = 0`: the `k`-th pure `Y₀`-derivative vanishes at `s`.
  have hvan' : ∀ s k : ℕ, (s : ℝ) ≤ 𝒮 → (k : ℝ) ≤ 𝒯 →
      MvPolynomial.eval (ptS ℓ s) ((MvPolynomial.pderiv (0 : Fin (r + 1)))^[k] P) = 0 := by
    intro s k hs hk
    have h := hvan s hs k (fun _ => 0) (by simpa using hk)
    simpa [applyDer] using h
  -- (v) Transport along the univariate reduction.
  have hderiv : ∀ s k : ℕ, s ≤ ⌊𝒮⌋₊ → k ≤ ⌊𝒯⌋₊ →
      (Polynomial.derivative^[k] Q).eval (s : ℂ) = 0 := by
    intro s k hs hk
    have hs' : (s : ℝ) ≤ 𝒮 := (Nat.le_floor_iff hSnonneg).mp hs
    have hk' : (k : ℝ) ≤ 𝒯 := (Nat.le_floor_iff hTnonneg).mp hk
    have h := hvan' s k hs' hk'
    rw [hQP] at h
    have h2 : MvPolynomial.eval (ptS ℓ s)
        ((MvPolynomial.pderiv (0 : Fin (r + 1)))^[k]
          (Polynomial.aeval (MvPolynomial.X (0 : Fin (r + 1))) Q))
        = (Polynomial.derivative^[k] Q).eval (s : ℂ) := by
      simpa [ptS] using eval_pderiv_iterate_aeval_X (ptS ℓ s) k Q
    rw [h2] at h
    exact h
  -- (vi) Multiplicity bound: `Q` has `N` roots each of multiplicity `M`, so `N * M ≤ deg Q`.
  have hmult := multiplicity_bound Q hQne (⌊𝒮⌋₊ + 1) (⌊𝒯⌋₊ + 1)
    (fun s hs k hk => hderiv s k (by omega) (by omega))
  have hle : ((Sq 0 + 1) * (Tq 0 + 1) : ℝ) ≤ 𝒟 0 := by
    have h1 : ((⌊𝒮⌋₊ + 1) * (⌊𝒯⌋₊ + 1) : ℝ) ≤ 𝒟 0 := by
      calc ((⌊𝒮⌋₊ + 1) * (⌊𝒯⌋₊ + 1) : ℝ) = ((⌊𝒮⌋₊ + 1) * (⌊𝒯⌋₊ + 1) : ℕ) := by
            push_cast; ring
        _ ≤ (Q.natDegree : ℝ) := by exact_mod_cast hmult
        _ ≤ (P.degreeOf 0 : ℝ) := by exact_mod_cast hQdeg
        _ ≤ 𝒟 0 := hdeg 0
    have h2 : (Sq 0 + 1) * (Tq 0 + 1) ≤ (⌊𝒮⌋₊ + 1) * (⌊𝒯⌋₊ + 1) :=
      Nat.mul_le_mul (Nat.succ_le_succ hSq_le) (Nat.succ_le_succ hTq_le)
    calc ((Sq 0 + 1) * (Tq 0 + 1) : ℝ) = ((Sq 0 + 1) * (Tq 0 + 1) : ℕ) := by push_cast; ring
      _ ≤ ((⌊𝒮⌋₊ + 1) * (⌊𝒯⌋₊ + 1) : ℕ) := by exact_mod_cast h2
      _ = ((⌊𝒮⌋₊ + 1) * (⌊𝒯⌋₊ + 1) : ℝ) := by push_cast; ring
      _ ≤ 𝒟 0 := h1
  -- (vii) (E1) at `m = 0` contradicts `(Sq 0 + 1) * (Tq 0 + 1) ≤ 𝒟 0` since `r ≥ 2`, `𝒟 0 ≥ 1`.
  have hE1' : ((r : ℝ) + 1) * 𝒟 0 < ((Sq 0 + 1) * (Tq 0 + 1) : ℝ) := by
    rw [Nat.choose_one_right] at hE1e0
    calc ((r : ℝ) + 1) * 𝒟 0 < ((Sq 0 : ℝ) + 1) * ((Tq 0 + 1 : ℕ) : ℝ) := hE1e0
      _ = ((Sq 0 + 1) * (Tq 0 + 1) : ℝ) := by push_cast; ring
  nlinarith [hE1', hle, h𝒟0, hr]

end Work.BW
