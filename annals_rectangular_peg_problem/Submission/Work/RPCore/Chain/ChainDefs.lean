import Submission.Work.RPCore.Defs

/-!
# `Work.RPCore.Chain`: chain-action bookkeeping

Definitions and elementary lemmas used by the chain-action critical-point analysis
(`chainAction_crit`).

For `q : Fin (n+1) → ℝ²` and `P : Fin n → ℝ²`:

* `Peff n P : Fin (n+1) → ℝ²` is the second argument fed to `W j` inside `chainAction`:
  `P j` for `j < n` and `0` for `j = n`;
* `Pprev n P : Fin (n+1) → ℝ²` is the "previous" momentum: `P (k-1)` for `k ≥ 1` and `0`
  for `k = 0`.

`differentiableAt_chainAction` records that `chainAction`, read as a function of `(q, P)`,
is differentiable wherever every `W j` is.
-/

namespace Work.RPCore.Chain

open Work.RPV

noncomputable section

/-- The `P`-argument of `W j` in `chainAction`: `P j` for `j < n`, and `0` for `j = n`. -/
def Peff (n : ℕ) (P : Fin n → ℝ × ℝ) : Fin (n + 1) → ℝ × ℝ :=
  fun j => if h : (j : ℕ) < n then P ⟨j, h⟩ else 0

/-- The momentum `P (k-1)`, `0` for `k = 0`; the `P`-slot paired with `q k` from below. -/
def Pprev (n : ℕ) (P : Fin n → ℝ × ℝ) : Fin (n + 1) → ℝ × ℝ :=
  fun k => if h : 0 < (k : ℕ) then P ⟨(k : ℕ) - 1, by omega⟩ else 0

theorem Peff_lt {n : ℕ} {P : Fin n → ℝ × ℝ} {j : Fin (n + 1)} (h : (j : ℕ) < n) :
    Peff n P j = P ⟨j, h⟩ := by
  simp only [Peff]; rw [dif_pos h]

theorem Peff_last (n : ℕ) (P : Fin n → ℝ × ℝ) : Peff n P (Fin.last n) = 0 := by
  simp only [Peff]; rw [dif_neg (by simp)]

theorem Peff_castSucc (n : ℕ) (P : Fin n → ℝ × ℝ) (j : Fin n) :
    Peff n P j.castSucc = P j := by
  rw [Peff_lt (by simp)]
  congr 1

theorem Pprev_pos {n : ℕ} {P : Fin n → ℝ × ℝ} {k : Fin (n + 1)} (h : 0 < (k : ℕ)) :
    Pprev n P k = P ⟨(k : ℕ) - 1, by omega⟩ := by
  simp only [Pprev]; rw [dif_pos h]

theorem Pprev_zero (n : ℕ) (P : Fin n → ℝ × ℝ) : Pprev n P 0 = 0 := by
  simp only [Pprev]; rw [dif_neg (by simp)]

theorem Pprev_succ (n : ℕ) (P : Fin n → ℝ × ℝ) (j : Fin n) :
    Pprev n P j.succ = P j := by
  have h : 0 < ((j.succ : Fin (n + 1)) : ℕ) := by simp
  rw [Pprev_pos h]
  congr 1

/-- `chainAction`, read as a function of `(q, P)`, is differentiable at every point as soon as
all the generating functions `W j` are differentiable. -/
theorem differentiableAt_chainAction (n : ℕ) (W : Fin (n + 1) → PS → ℝ)
    (hWd : ∀ j, Differentiable ℝ (W j)) (q : Fin (n + 1) → ℝ × ℝ) (P : Fin n → ℝ × ℝ) :
    DifferentiableAt ℝ (fun z : (Fin (n + 1) → ℝ × ℝ) × (Fin n → ℝ × ℝ) =>
      chainAction n W z.1 z.2) (q, P) := by
  have hW : DifferentiableAt ℝ (fun z : (Fin (n + 1) → ℝ × ℝ) × (Fin n → ℝ × ℝ) =>
      (∑ j : Fin (n+1), W j (z.1 j, if h : (j:ℕ)<n then z.2 ⟨j,h⟩ else 0))) (q, P) := by
    have h : (fun z : (Fin (n + 1) → ℝ × ℝ) × (Fin n → ℝ × ℝ) =>
          (∑ j : Fin (n+1), W j (z.1 j, if h : (j:ℕ)<n then z.2 ⟨j,h⟩ else 0)))
        = (∑ j : Fin (n+1), fun z : (Fin (n + 1) → ℝ × ℝ) × (Fin n → ℝ × ℝ) =>
            W j (z.1 j, if h : (j:ℕ)<n then z.2 ⟨j,h⟩ else 0)) := by
      funext z; simp
    rw [h]
    apply DifferentiableAt.sum
    intro j _
    have hlin : DifferentiableAt ℝ (fun z : (Fin (n + 1) → ℝ × ℝ) × (Fin n → ℝ × ℝ) =>
        (z.1 j, if h : (j:ℕ)<n then z.2 ⟨j,h⟩ else 0)) (q, P) := by
      by_cases h : (j:ℕ) < n
      · simp only [dif_pos h]; fun_prop
      · simp only [dif_neg h]; fun_prop
    exact (hWd j).differentiableAt.comp (q,P) hlin
  have hT : DifferentiableAt ℝ (fun z : (Fin (n + 1) → ℝ × ℝ) × (Fin n → ℝ × ℝ) =>
      (∑ j : Fin n, ((z.2 j).1 * ((z.1 j.succ).1 - (z.1 j.castSucc).1) +
        (z.2 j).2 * ((z.1 j.succ).2 - (z.1 j.castSucc).2)))) (q,P) := by
    have h : (fun z : (Fin (n + 1) → ℝ × ℝ) × (Fin n → ℝ × ℝ) =>
          (∑ j : Fin n, ((z.2 j).1 * ((z.1 j.succ).1 - (z.1 j.castSucc).1) +
            (z.2 j).2 * ((z.1 j.succ).2 - (z.1 j.castSucc).2))))
        = (∑ j : Fin n, fun z : (Fin (n + 1) → ℝ × ℝ) × (Fin n → ℝ × ℝ) =>
            ((z.2 j).1 * ((z.1 j.succ).1 - (z.1 j.castSucc).1) +
              (z.2 j).2 * ((z.1 j.succ).2 - (z.1 j.castSucc).2))) := by
      funext z; simp
    rw [h]
    apply DifferentiableAt.sum
    intro j _
    fun_prop
  have hfun : (fun z : (Fin (n + 1) → ℝ × ℝ) × (Fin n → ℝ × ℝ) => chainAction n W z.1 z.2)
      = (fun z : (Fin (n + 1) → ℝ × ℝ) × (Fin n → ℝ × ℝ) =>
          (∑ j : Fin n, ((z.2 j).1 * ((z.1 j.succ).1 - (z.1 j.castSucc).1) +
            (z.2 j).2 * ((z.1 j.succ).2 - (z.1 j.castSucc).2)))
          - (∑ j : Fin (n+1), W j (z.1 j, if h : (j:ℕ)<n then z.2 ⟨j,h⟩ else 0))) := by
    funext z; rfl
  rw [hfun]
  exact hT.sub hW

end

end Work.RPCore.Chain
