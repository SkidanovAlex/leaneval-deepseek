import Mathlib
import Submission.Work.EQ.DefsCore
import Submission.Work.EQ.fan_base
import Submission.Work.EQ.bp_aux

namespace Work.EQ

open Filter _root_.Topology

/-- **A `k`-th root with bounded modulus.**  If `w : ℂ` is nonzero and `k ≥ 1`, `ρ > 0` with
`‖w‖ < ρ ^ k`, then `w` has a `k`-th root `t` of modulus `< ρ`.  (The modulus of any `k`-th root
of `w` equals `‖w‖ ^ (1/k)`, so this says exactly that `{‖w‖ < ρ ^ k}` is a disc of radius `ρ`
in the `t`-plane.) -/
lemma bp_root_aux {w : ℂ} {ρ : ℝ} {k : ℕ} (hk : 0 < k) (hρ : 0 < ρ) (hw : w ≠ 0)
    (h : ‖w‖ < ρ ^ k) : ∃ t : ℂ, t ^ k = w ∧ 0 < ‖t‖ ∧ ‖t‖ < ρ := by
  obtain ⟨t, ht⟩ : ∃ t : ℂ, t = w ^ ((k : ℂ)⁻¹) := ⟨_, rfl⟩
  have htk : t ^ k = w := by
    rw [ht]; exact Complex.cpow_nat_inv_pow w (by omega)
  have hnorm : ‖t‖ ^ k = ‖w‖ := by
    have h1 : ‖t ^ k‖ = ‖w‖ := by rw [htk]
    rwa [norm_pow] at h1
  have hwpos : 0 < ‖w‖ := norm_pos_iff.mpr hw
  refine ⟨t, htk, ?_, ?_⟩
  · rcases eq_or_lt_of_le (norm_nonneg t) with h0 | h0
    · exfalso
      have hz : ‖w‖ = 0 := by rw [← hnorm, ← h0, zero_pow (by omega : k ≠ 0)]
      exact (ne_of_gt hwpos) hz
    · exact h0
  · rw [← hnorm] at h
    exact lt_of_pow_lt_pow_left₀ k hρ.le h


/-- **F3 (backward Puiseux covering).**  Let `c : ℂ → ℂ × ℂ` be analytic on `ball u₀ R`, `u₀ ≠ 0`.
Fix `N : ℕ`.  Then there are `k ≥ 1`, `κ ≠ 0`, `ρ > 0` and finitely many families
`β : Fin m → ℂ → Fin (N+1) → ℂ × ℂ` such that, for every `u` with `0 < ‖u - u₀‖ < ‖κ‖ ρᵏ`,
every *regular* backward `EqRelC`-chain of length `N` ending at `c u` (i.e. `P : Fin (N+1) → ℂ × ℂ`
with `P (Fin.last N) = c u` and `RegPair a (P (Fin.castSucc j)) (P (Fin.succ j))` for all `j`) is one
of the families `β i` evaluated at a `k`-th root `t` of `(u - u₀)/κ`.  Each `β i t` is itself such a
chain, and each coordinate of `β i` is analytic on the punctured disc `ball 0 ρ \ {0}`.

Route (the requester's notes; the mathematics is Rychlik's, see `PAPER_PROOFS.md` §0).

* **One step.**  Given `Q`, the backward points `P` with `EqRelC a P Q` are `-Q ± (Q - O₁)/ρ'`
  with `ρ' = ((Q.1 + a/2)² + Q.2²)^(1/2)` (use `Complex.cpow_nat_inv_pow` for `(z^(1/2))^2 = z`).
  If `ρ'² ≠ 0` this is two points, and dividing the parametrisation by a unit keeps it analytic.
  The interesting case is `ρ'²` vanishing somewhere: then write `ρ'² = t^ν · unit` near the zero
  and substitute `t = s²` when `ν` is odd — that is the only place where the exponent `k > 1` and
  the loss of a factor `2` per step come from.
* **Induction on `N`.**  Compose the one-step description with the length-`(N-1)` description of the
  *new* end `u ↦ P_1(u)`; a `2^N`-th root `t` of `(u - u₀)/κ` linearises every nested radical.  At
  each step the finitely many branch points of the radicands are isolated, so shrink `ρ`.
* **Finite cover.**  Equivalently: the solution set of the polynomial system `RegPair`-chain-of-
  length-`N`-ending-at-`c u` over a punctured annulus around `u₀` is a finite unbranched cover of
  the annulus (the fibre has at most `2^N` points away from the finitely many bad `u`), so it is
  `t ↦ β_i(t)` with `u = u₀ + κ t^k`, `k` a multiple of the sheet number.
* Degenerate cases are handled by `m = 0` (no regular chain) and by constant ends. -/
theorem backward_puiseux {a : ℝ} {u₀ : ℂ} (hu₀ : u₀ ≠ 0) {R : ℝ} (hR : 0 < R)
    {c : ℂ → ℂ × ℂ} (hc : AnalyticOnNhd ℂ c (Metric.ball u₀ R)) (N : ℕ) :
    ∃ (k : ℕ) (_ : 0 < k) (κ : ℂ) (_ : κ ≠ 0) (ρ : ℝ) (_ : 0 < ρ) (m : ℕ)
      (β : Fin m → ℂ → Fin (N + 1) → ℂ × ℂ),
      (∀ i j, AnalyticOnNhd ℂ (fun t => (β i t) j) (Metric.ball (0 : ℂ) ρ \ {0})) ∧
      (∀ i, ∀ t ∈ Metric.ball (0 : ℂ) ρ \ {0},
        (β i t) (Fin.last N) = c (u₀ + κ * t ^ k) ∧
        ∀ j : Fin N, RegPair a ((β i t) (Fin.castSucc j)) ((β i t) (Fin.succ j))) ∧
      (∀ u : ℂ, 0 < ‖u - u₀‖ → ‖u - u₀‖ < ‖κ‖ * ρ ^ k →
        ∀ P : Fin (N + 1) → ℂ × ℂ, P (Fin.last N) = c u →
          (∀ j : Fin N, RegPair a (P (Fin.castSucc j)) (P (Fin.succ j))) →
            ∃ i : Fin m, ∃ t : ℂ, t ^ k = (u - u₀) / κ ∧ 0 < ‖t‖ ∧ ‖t‖ < ρ ∧
              ∀ j : Fin (N + 1), P j = (β i t) j) := by
  classical
  let e : {σ : Fin N → Bool // Adm a c u₀ R σ} ≃
      Fin (Fintype.card {σ : Fin N → Bool // Adm a c u₀ R σ}) := Fintype.equivFin _
  refine ⟨2 ^ N, by positivity, 1, one_ne_zero, rhoFin' a c u₀ R N, rhoFin'_pos hR hc,
    Fintype.card {σ : Fin N → Bool // Adm a c u₀ R σ},
    fun i => branchPt a c u₀ R (e.symm i).val, ?_, ?_, ?_⟩
  · intro i j
    have h := branchPt_analytic hR hc (e.symm i).property j
    exact h.1.prod h.2
  · intro i t ht
    refine ⟨?_, ?_⟩
    · simp only []
      rw [branchPt_last, one_mul]
    · intro j
      have hb : ‖t‖ < rhoFin' a c u₀ R N := by
        have h := ht.1
        rwa [Metric.mem_ball, dist_zero_right] at h
      exact branchPt_reg hR hc (e.symm i).property hb (by simpa using ht.2) j
  · intro u h1 h2 P hP hreg
    have h2' : ‖u - u₀‖ < (rhoFin' a c u₀ R N) ^ (2 ^ N) := by simpa using h2
    obtain ⟨t, ht, ht0, htρ⟩ := bp_root_aux (w := u - u₀) (ρ := rhoFin' a c u₀ R N)
      (k := 2 ^ N) (by positivity) (rhoFin'_pos hR hc)
      (by intro hh; rw [hh] at h1; simp at h1) h2'
    obtain ⟨sg, hsg, hPj⟩ := coverage hR hc ht (norm_pos_iff.mp ht0) htρ P hP hreg
    refine ⟨e ⟨sg, hsg⟩, t, ?_, ht0, htρ, ?_⟩
    · rw [ht, div_one]
    · intro j
      simp only []
      rw [hPj j, Equiv.symm_apply_apply]

end Work.EQ
