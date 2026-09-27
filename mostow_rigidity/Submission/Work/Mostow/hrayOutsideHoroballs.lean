import Mathlib
import Submission.Work.Mostow.horoballOverlapCriterion
import Submission.Work.Mostow.BaryBase

namespace Work.Mostow

open Submission.Mostow

noncomputable section

variable {n : ℕ}

/-- The Busemann level along the ray towards `ξ ∈ Sph n`: for `p = hray ξ s = sinh s • ξ` one has
`tpart p = cosh s`, `⟪p,ξ⟫ = sinh s` and hence
`tpart p - ⟪p,ξ⟫ = cosh s - sinh s = exp (-s)`, i.e. `busemann ξ (hray ξ s) = -s`. -/
private lemma busemann_hray_sinh {n : ℕ} {ξ : E n} (hξ : ξ ∈ Sph n) (t : ℝ) :
    busemann ξ (hray ξ t) = -t := by
  have hξn : ‖ξ‖ = 1 := (mem_Sph_iff ξ).mp hξ
  have h1 : tpart (Real.sinh t • ξ) = Real.cosh t := by
    have hnorm : ‖Real.sinh t • ξ‖ ^ 2 = Real.sinh t ^ 2 := by
      rw [norm_smul, Real.norm_eq_abs, hξn, mul_one, sq_abs]
    rw [tpart, hnorm]
    have h2 : 1 + Real.sinh t ^ 2 = Real.cosh t ^ 2 := by rw [Real.cosh_sq]; ring
    rw [h2, Real.sqrt_sq (le_of_lt (Real.cosh_pos t))]
  have h3 : inner ℝ (Real.sinh t • ξ) ξ = Real.sinh t := by
    rw [real_inner_smul_left, real_inner_self_eq_norm_sq, hξn]
    ring
  rw [hray, busemann, h1, h3, ← Real.log_exp (-t)]
  congr 1
  rw [Real.cosh_eq, Real.sinh_eq]
  ring

/-- A point of the horosphere bounding `horoball ξ (ht ξ)` — namely `hray ξ (-(ht ξ)) = sinh (-ht ξ) • ξ`,
whose Busemann level at `ξ` is exactly `ht ξ` — lies outside every horoball of a pairwise disjoint
family `{horoball η (ht η)}_{η ∈ P}`.

Hint: `busemann ξ (hray ξ s) = -s` for `ξ ∈ Sph n` (because `tpart (sinh s • ξ) = cosh s` and
`⟪sinh s • ξ, ξ⟫ = sinh s`, and `cosh s - sinh s = exp (-s)`), so with `s = -(ht ξ)` the point
`p = hray ξ (-(ht ξ))` has level exactly `ht ξ` and hence is not in `horoball ξ (ht ξ)`.
For `η ≠ ξ` use `Work.Mostow.horoballOverlapCriterion`: disjointness gives
`1 - ⟪ξ,η⟫ ≥ 2 * exp (ht ξ + ht η)`; combined with `Work.Mostow.horoball_minkowski_pair` at `p`
(and `tpart p - ⟪p,ξ⟫ = exp (ht ξ)`) this gives `tpart p - ⟪p,η⟫ ≥ exp (ht η)`. -/
theorem hrayOutsideHoroballs (n : ℕ) (P : Set (Submission.Mostow.E n)) (ht : Submission.Mostow.E n → ℝ)
    (hPsub : P ⊆ Submission.Mostow.Sph n)
    (hdisj : P.Pairwise (fun ξ η => Disjoint (Submission.Mostow.horoball ξ (ht ξ))
      (Submission.Mostow.horoball η (ht η))))
    (ξ : Submission.Mostow.E n) (hξ : ξ ∈ P) :
    ∀ η ∈ P, Work.Mostow.hray ξ (-(ht ξ)) ∉ Submission.Mostow.horoball η (ht η) := by
  intro η hη
  have hξS : ξ ∈ Sph n := hPsub hξ
  have hηS : η ∈ Sph n := hPsub hη
  set p : E n := hray ξ (-(ht ξ)) with hp
  -- the Busemann level of `p` at `ξ` is exactly `ht ξ`
  have hbp : busemann ξ p = ht ξ := by
    rw [hp, busemann_hray_sinh hξS]; ring
  -- equivalently `tpart p - ⟪p,ξ⟫ = exp (ht ξ)`
  have hlevξ : tpart p - inner ℝ p ξ = Real.exp (ht ξ) := by
    rw [← exp_busemann ξ hξS p, hbp]
  intro hmem
  by_cases hne : ξ = η
  · -- `p` sits exactly on the boundary horosphere of `horoball ξ (ht ξ)`, so it is not inside it
    subst hne
    rw [horoball, Set.mem_ofPred_eq] at hmem
    rw [hbp] at hmem
    exact absurd hmem (lt_irrefl _)
  · -- disjointness of the two horoballs: `2 exp (ht ξ + ht η) ≤ 1 - ⟪ξ,η⟫`
    have hdis := hdisj hξ hη hne
    have hnotin : ¬ (1 - inner ℝ ξ η < 2 * Real.exp (ht ξ + ht η)) := by
      intro hlt
      obtain ⟨u, hu1, hu2⟩ := (horoballOverlapCriterion n ξ η hξS hηS (ht ξ) (ht η)).2 hlt
      exact Set.disjoint_left.mp hdis hu1 hu2
    have hdisjineq : 2 * Real.exp (ht ξ + ht η) ≤ 1 - inner ℝ ξ η := not_lt.mp hnotin
    -- the Minkowski pair inequality at `p`
    have hmink := horoball_minkowski_pair n ξ η hξS hηS p
    rw [hlevξ] at hmink
    have hexp : Real.exp (ht ξ) * Real.exp (ht η)
        ≤ Real.exp (ht ξ) * (tpart p - inner ℝ p η) := by
      rw [Real.exp_add] at hdisjineq
      linarith
    have hkey : Real.exp (ht η) ≤ tpart p - inner ℝ p η :=
      le_of_mul_le_mul_left hexp (Real.exp_pos (ht ξ))
    rw [horoball, Set.mem_ofPred_eq] at hmem
    have hlog : ht η ≤ busemann η p := by
      rw [busemann, ← Real.log_exp (ht η)]
      exact Real.log_le_log (Real.exp_pos _) hkey
    linarith

end

end Work.Mostow
