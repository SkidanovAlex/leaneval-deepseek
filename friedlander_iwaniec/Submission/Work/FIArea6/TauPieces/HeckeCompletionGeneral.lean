/-
# `Submission.Work.FIArea6.TauPieces.HeckeCompletionGeneral`

**Existence of the completed Hecke `L`-function of `ℚ(i)` for an arbitrary strict character mod
`4d` and an arbitrary integer weight `m`** — the analytic input that the §16 argument of
Friedlander–Iwaniec consumes as (16.20): for every strict `χ` mod `4d` (`IsCharMod4dStrict`, i.e. a
genuine character of `(ℤ[i]/4dℤ[i])^*` extended by zero) and every `m : ℤ` **except** the single
exceptional datum `m = 0` with `χ` trivial on the primary units mod `4d` (that case is *false*:
`heckeLSeries χ 0` is then `ζ_{ℚ(i)}` with finitely many Euler factors removed, which has a pole at
`s = 1`, so no entire function agrees with `heckeArch d 0 s · heckeLSeries χ 0 s` on `re s > 1` —
`Work.FIArea6Hecke.R.noCompletion_of_primaryTrivial`), there is an entire `Lam` with

  `Lam s = heckeArch d m s · heckeLSeries χ m s`   for `re s > 1 + |m|/2`.

The two pieces are entirely different analytics, and both are already in the workspace:

* `m = 0`: `Work.FIArea6Hecke.R.exists_completion_strict` — the Mellin transform of the
  weight-`0` holomorphic theta series `θ(u) = Σ_{z odd} χ(z)e^{-πu|z|²}`, whose Poisson dual has
  non-zero constant term exactly when `χ` is non-trivial on the primary units (this is the
  hypothesis); the completion is the Mellin transform of the sum of the two halves of the cut
  integral.
* `m ≠ 0`: write `m = ±k` with `k ≥ 1`.  Then the weight-`k` theta series
  `θ(u) = Σ_{z odd} χ(z)z^k e^{-πu|z|²}` has **no constant term in its Poisson dual** (`z = 0` is
  killed by `z^k`), so *no* non-triviality of `χ` is needed.  This is
  `Work.FIArea6Hecke.R.hci_completion_nat_big` (`k ≥ 1`, every strict `χ`), and the negative weight
  is the conjugation `Λ(s) = conj(Λ₀(conj s))` of the positive-weight completion of the conjugate
  character `χ̄ = star ∘ χ`.
-/
import Mathlib
import Submission.Work.FIArea6Hecke.R.HeckeCompletionAll
import Submission.Work.FIArea6Hecke.R.exists_completion_strict
import Submission.Work.FIArea6Hecke.R.heckeCompletionImprimitive

namespace Work.FIArea6.TauPieces

noncomputable section

/-! ## The two weights -/

/-- **The completion at a positive weight `k ≥ 1`**, for an *arbitrary* strict `χ` mod `4d` (no
non-triviality hypothesis: the Poisson dual of `Σ_{z odd} χ(z)z^k e^{-πu|z|²}` has no `z = 0`
term). -/
theorem heckeCompletion_posWeight (d : ℕ) (chi : GaussianInt → ℂ) (k : ℕ) (hd : 1 ≤ d)
    (hchi : Work.FIArea5.S16Hecke.IsCharMod4dStrict d chi) (hk : 1 ≤ k) :
    ∃ Lam : ℂ → ℂ, AnalyticOn ℂ Lam Set.univ ∧
      ∀ s : ℂ, 1 + |((k : ℤ) : ℝ)| / 2 < s.re →
        Lam s = Work.FITop4.Bridge.heckeArch d (k : ℤ) s *
          Work.FIArea5.S16Hecke.heckeLSeries chi (k : ℤ) s := by
  obtain ⟨Lam, hAn, hag⟩ :=
    Work.FIArea6Hecke.R.hci_completion_nat_big d chi k hd hchi hk
  have hkabs : |((k : ℤ) : ℝ)| = (k : ℝ) := by
    rw [Int.cast_natCast]; exact abs_of_nonneg (by positivity)
  refine ⟨Lam, hAn, fun s hs => ?_⟩
  rw [hkabs] at hs
  exact hag s hs

/-- **The completion at a negative weight `-k`, `k ≥ 1`**, by conjugating the positive-weight
completion of the conjugate character `χ̄`:
`Λ(s) = conj(Λ₀(conj s))`, using `conj(heckeArch d k (conj s)) = heckeArch d (-k) s` and
`conj(L(conj s, ψ_{χ̄,k})) = L(s, ψ_{χ,-k})`. -/
theorem heckeCompletion_negWeight (d : ℕ) (chi : GaussianInt → ℂ) (k : ℕ) (hd : 1 ≤ d)
    (hchi : Work.FIArea5.S16Hecke.IsCharMod4dStrict d chi) (hk : 1 ≤ k) :
    ∃ Lam : ℂ → ℂ, AnalyticOn ℂ Lam Set.univ ∧
      ∀ s : ℂ, 1 + |((-(k : ℤ) : ℤ) : ℝ)| / 2 < s.re →
        Lam s = Work.FITop4.Bridge.heckeArch d (-(k : ℤ)) s *
          Work.FIArea5.S16Hecke.heckeLSeries chi (-(k : ℤ)) s := by
  have hchi' : Work.FIArea5.S16Hecke.IsCharMod4dStrict d (fun z : GaussianInt => star (chi z)) :=
    Work.FIArea6Hecke.R.hci_isCharMod4dStrict_conj hchi
  obtain ⟨L0, hAn0, hag0⟩ :=
    Work.FIArea6Hecke.R.hci_completion_nat_big d (fun z : GaussianInt => star (chi z)) k hd hchi' hk
  refine ⟨fun s => star (L0 (star s)), ?_, ?_⟩
  · refine DifferentiableOn.analyticOn ?_ isOpen_univ
    intro z _
    have h1 : DifferentiableAt ℂ L0 (star z) :=
      (hAn0.analyticAt (Filter.univ_mem)).differentiableAt
    have h2 := DifferentiableAt.conj_conj (f := L0) (x := star z) h1
    have h2' : DifferentiableAt ℂ (fun s => star (L0 (star s))) (star (star z)) := h2
    rw [star_star] at h2'
    exact h2'.differentiableWithinAt
  · intro s hs
    have hkabs : |((-(k : ℤ) : ℤ) : ℝ)| = (k : ℝ) := by
      rw [show (((-(k : ℤ) : ℤ)) : ℝ) = -((k : ℝ)) by push_cast; ring, abs_neg,
        abs_of_nonneg (by positivity)]
    have hs' : 1 + (k : ℝ) / 2 < (star s).re := by
      rw [Complex.star_def, Complex.conj_re]
      rwa [hkabs] at hs
    have h0 := hag0 (star s) hs'
    have hA : star (Work.FITop4.Bridge.heckeArch d ((k : ℤ)) (star s))
        = Work.FITop4.Bridge.heckeArch d (-(k : ℤ)) s :=
      Work.FIArea6Hecke.R.hci_star_heckeArch d (k : ℤ) s hd
    have hB : star (Work.FIArea5.S16Hecke.heckeLSeries (fun z : GaussianInt => star (chi z))
        ((k : ℤ)) (star s)) = Work.FIArea5.S16Hecke.heckeLSeries chi (-(k : ℤ)) s := by
      rw [← Work.FIArea5.S16Hecke.heckeLSeries_conj (fun z : GaussianInt => star (chi z)) k s]
      congr 1
      funext z
      simp
    show star (L0 (star s)) = _
    rw [h0, star_mul, hA, hB]
    ring

/-! ## The target -/

theorem HeckeCompletionGeneral (d : ℕ) (chi : GaussianInt → ℂ) (m : ℤ) (hd : 1 ≤ d)
    (hchi : Work.FIArea5.S16Hecke.IsCharMod4dStrict d chi)
    (hnontriv : m ≠ 0 ∨ ∃ z : GaussianInt, Work.FIPlan.IsPrimary z ∧
        Work.FIArea5.S16Hecke.IsUnitMod4d d z ∧ chi z ≠ 1) :
    ∃ Lam : ℂ → ℂ, AnalyticOn ℂ Lam Set.univ ∧
      ∀ s : ℂ, 1 + |(m : ℝ)| / 2 < s.re →
        Lam s = Work.FITop4.Bridge.heckeArch d m s *
          Work.FIArea5.S16Hecke.heckeLSeries chi m s := by
  by_cases hm : m = 0
  · -- the weight-`0` case: the Mellin transform of the weight-`0` theta series, which is entire
    -- exactly when `χ` is non-trivial on the primary units
    subst hm
    rcases hnontriv with h | ⟨z, hz1, hz2, hz3⟩
    · exact absurd rfl h
    · obtain ⟨Lam, hAn, hag⟩ :=
        Work.FIArea6Hecke.R.exists_completion_strict hd hchi ⟨z, hz1, hz2, hz3⟩
      refine ⟨Lam, hAn, fun s hs => hag s ?_⟩
      simpa using hs
  · -- `m ≠ 0`: no non-triviality of `χ` is needed (the weight-`k`, `k ≥ 1`, theta series is
    -- cuspidal in the dual)
    rcases lt_or_gt_of_ne hm with hmneg | hmpos
    · obtain ⟨k, rfl⟩ : ∃ k : ℕ, m = -((k : ℕ) : ℤ) := ⟨m.natAbs, by omega⟩
      have hk : 1 ≤ k := by omega
      exact heckeCompletion_negWeight d chi k hd hchi hk
    · obtain ⟨k, rfl⟩ : ∃ k : ℕ, m = ((k : ℕ) : ℤ) :=
        ⟨m.toNat, (Int.toNat_of_nonneg hmpos.le).symm⟩
      have hk : 1 ≤ k := by omega
      exact heckeCompletion_posWeight d chi k hd hchi hk

end

end Work.FIArea6.TauPieces
