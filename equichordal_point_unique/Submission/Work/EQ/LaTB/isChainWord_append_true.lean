import Mathlib
import Submission.Work.EQ.H0_tail_bounded
import Submission.Work.EQ.StableTailDefs
import Submission.Work.EQ.germC_facts

set_option linter.unusedVariables false

namespace Work.EQ.LaTB

open Work.EQ

/-- **The fan of a run of principal letters is the stable germ.**

If the principal inverse branch inverts the stable step on the ball of radius `ρg`, i.e.
`invBranch a true (germC a h (λ * u)) = germC a h u` for `‖u‖ < ρg`, and `‖λ‖ ≤ 1`, then the
same holds for a whole run `true, …, true` of principal letters: for `‖v‖ < ρg`,

`fan a h (List.replicate t true) v = germC a h v`.

(Induction on `t`; the radius hypothesis is inherited because `‖λ * v‖ ≤ ‖v‖`.) -/
theorem fan_replicate_true_eq_germC {a : ℝ} {h : ℂ → ℂ} {ρg : ℝ}
    (hstep : ∀ u : ℂ, ‖u‖ < ρg →
      invBranch a true (germC a h ((eqLam a : ℂ) * u)) = germC a h u)
    (hlam : ‖(eqLam a : ℂ)‖ ≤ 1) :
    ∀ t : ℕ, ∀ v : ℂ, ‖v‖ < ρg → fan a h (List.replicate t true) v = germC a h v := by
  intro t
  induction t with
  | zero => intro v hv; rfl
  | succ t ih =>
      intro v hv
      have hv' : ‖(eqLam a : ℂ) * v‖ < ρg := by
        calc ‖(eqLam a : ℂ) * v‖ = ‖(eqLam a : ℂ)‖ * ‖v‖ := norm_mul _ _
          _ ≤ 1 * ‖v‖ := by gcongr
          _ = ‖v‖ := one_mul _
          _ < ρg := hv
      rw [show fan a h (List.replicate (Nat.succ t) true) v
            = invBranch a true (fan a h (List.replicate t true) ((eqLam a : ℂ) * v)) from rfl]
      rw [ih ((eqLam a : ℂ) * v) hv']
      exact hstep v hv

/-- **Appending a run of principal letters does not change the fan value.**

For `‖u‖ < ρg` (and `hstep`, `hlam` as in `fan_replicate_true_eq_germC`),

`fan a h (w ++ List.replicate t true) u = fan a h w u`.

Indeed the principal leaf is a fixed point of one principal step, so appending principal letters to
the *end* of a word does not move the initial point of the fan; induction on `w` reduces this to
`fan_replicate_true_eq_germC`. -/
theorem fan_append_replicate_true {a : ℝ} {h : ℂ → ℂ} {ρg : ℝ}
    (hstep : ∀ u : ℂ, ‖u‖ < ρg →
      invBranch a true (germC a h ((eqLam a : ℂ) * u)) = germC a h u)
    (hlam : ‖(eqLam a : ℂ)‖ ≤ 1) :
    ∀ (w : List Bool) (t : ℕ) (u : ℂ), ‖u‖ < ρg →
      fan a h (w ++ List.replicate t true) u = fan a h w u := by
  intro w
  induction w with
  | nil =>
      intro t u hu
      have h0 : fan a h ([] : List Bool) u = germC a h u := rfl
      rw [List.nil_append, h0]
      exact fan_replicate_true_eq_germC (h := h) hstep hlam t u hu
  | cons c w' ih =>
      intro t u hu
      have hu' : ‖(eqLam a : ℂ) * u‖ < ρg := by
        calc ‖(eqLam a : ℂ) * u‖ = ‖(eqLam a : ℂ)‖ * ‖u‖ := norm_mul _ _
          _ ≤ 1 * ‖u‖ := by gcongr
          _ = ‖u‖ := one_mul _
          _ < ρg := hu
      rw [show fan a h ((c :: w') ++ List.replicate t true) u
            = invBranch a c (fan a h (w' ++ List.replicate t true) ((eqLam a : ℂ) * u)) from rfl]
      rw [ih t ((eqLam a : ℂ) * u) hu']
      rfl

/-- **Extending a chain word by stationary letters.**

`Work.EQ.IsChainWord a h p N ε` says that the letters of `ε` are the branch labels of the chain
`p` over the index range `[0, N]` (so in particular `p.1 0 = fan a h ε (ψ₁ p)`).  If moreover the
chain follows the principal leaf from index `N` on (`hN`) and the parameter `ψ₁ p` is small
enough (`hsmall`, with `hstep` the identity `invBranch a true (germC (λ u)) = germC u` valid on
the ball of radius `ρg`), then the *letter* of every step from index `N` on is principal, so the
word can be extended by arbitrarily many `true` letters:

`IsChainWord a h p (N + t) (ε ++ List.replicate t true)`.

This is what lets the uniform tail-bound argument feed a chain whose reading word is *constant*
(case (i) of the trichotomy) into the case-(ii) interface: a word of length `L ≥ tailIdx a h p`
whose letters are the chain's labels pins the chain down completely, because beyond the tail index
the chain *is* the principal leaf. -/
theorem isChainWord_append_true {a : ℝ} (ha0 : 0 < a) (ha1 : a < 1) {h : ℂ → ℂ} {p : Work.EQ.ChainData}
    (hp : Work.EQ.IsChain a h p) {N : ℕ} {ε : List Bool} (hw : Work.EQ.IsChainWord a h p N ε)
    (hN : ∀ n : ℕ, N ≤ n → p.1 (n : ℤ) = Work.EQ.germC a h (((Work.EQ.eqLam a : ℝ) : ℂ) ^ n * p.2.1))
    {ρg : ℝ} (hstep : ∀ u : ℂ, ‖u‖ < ρg →
      Work.EQ.invBranch a true (Work.EQ.germC a h (((Work.EQ.eqLam a : ℝ) : ℂ) * u)) =
        Work.EQ.germC a h u)
    (hsmall : ‖p.2.1‖ < ρg) (t : ℕ) :
    Work.EQ.IsChainWord a h p (N + t) (ε ++ List.replicate t true) := by
  obtain ⟨hlen, hfan, hlab⟩ := hw
  have hlam_le : ‖(eqLam a : ℂ)‖ ≤ 1 := by
    rw [show ‖(eqLam a : ℂ)‖ = |eqLam a| from RCLike.norm_ofReal _,
      abs_of_pos (eqLam_pos' ha0 ha1)]
    exact (eqLam_lt_one' ha0 ha1).le
  have hpow : ∀ j : ℕ, ‖((eqLam a : ℝ) : ℂ) ^ j * p.2.1‖ < ρg := by
    intro j
    refine lt_of_le_of_lt ?_ hsmall
    rw [norm_mul]
    calc ‖((eqLam a : ℝ) : ℂ) ^ j‖ * ‖p.2.1‖ ≤ 1 * ‖p.2.1‖ := by
          gcongr
          rw [norm_pow]
          exact pow_le_one₀ (norm_nonneg _) hlam_le
      _ = ‖p.2.1‖ := one_mul _
  refine ⟨?_, ?_, ?_⟩
  · simp [List.length_append, List.length_replicate, hlen]
  · rw [fan_append_replicate_true (h := h) hstep hlam_le ε t p.2.1 hsmall]
    exact hfan
  · intro j hj
    by_cases hjN : j < N
    · have hjlen : j < ε.length := by omega
      rw [List.getD_append ε (List.replicate t true) true j hjlen]
      exact hlab j hjN
    · have hjN' : N ≤ j := not_lt.mp hjN
      have hget : (ε ++ List.replicate t true).getD j true = true := by
        rw [List.getD_append_right ε (List.replicate t true) true j (by omega)]
        exact List.getD_replicate true (by omega)
      rw [hget]
      have h1 : p.1 (j : ℤ) = germC a h (((eqLam a : ℝ) : ℂ) ^ j * p.2.1) := hN j hjN'
      have h2 : p.1 ((j : ℤ) + 1) = germC a h (((eqLam a : ℝ) : ℂ) ^ (j+1) * p.2.1) := by
        have hh := hN (j+1) (by omega)
        rwa [show ((j+1 : ℕ) : ℤ) = (j : ℤ) + 1 from by push_cast; ring] at hh
      rw [h1, h2]
      rw [show ((eqLam a : ℝ) : ℂ) ^ (j+1) * p.2.1
            = ((eqLam a : ℝ) : ℂ) * (((eqLam a : ℝ) : ℂ) ^ j * p.2.1) from by
            rw [pow_succ]; ring]
      exact (hstep _ (hpow j)).symm

end Work.EQ.LaTB
