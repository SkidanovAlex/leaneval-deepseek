import Mathlib

namespace Work.Peluse.UControl

/-- **Independence of a "distinct fresh variables" family of multivariate polynomials.**

The level chain of Peluse's Lemma 4.8 (`Work.Peluse.UControl.LevRound`, file
`Submission/Work/Peluse/UControl/levRoundHolds.lean`) produces, at its closing step, atoms of the
shape `atoms'_s = C D * (Σ_{s' ∈ P s} atoms_{s'}) * X s`, i.e. an element of the *old* block
`MvPolynomial (Fin L) ℤ` times the *fresh* variable `X s`.  The new state is a punctured cube over
the fresh coordinates, and both of its defining properties

* `LevIndep (L + N) A' atoms'` (distinct histories have distinct atom sums), and
* `natDegree = D - 1` for the slots of the new state (the new leading coefficient is nonzero),

boil down to the statement proved here: **the map `w ↦ Σ_{j : w j} c_j · X_j`, with the `c_j` lying
in the *old* block `MvPolynomial (Fin L) R` and all nonzero, is injective** — the terms carry
distinct variables, so nothing cancels.

## Proof routes (for the prover; both verified by the reviewer)

(1) Collapse all but one fresh variable: fix `j₀`, and use the `R`-algebra hom
`φ : MvPolynomial (Fin (L+N)) R →ₐ[R] MvPolynomial (Fin L) R` sending `X i ↦ X i` for `i < L`,
`X (L+j₀) ↦ 1`, and `X (L+j) ↦ 0` for `j ≠ j₀` (e.g. `MvPolynomial.aeval` with that variable map,
or `MvPolynomial.eval₂Hom`).  Then `φ (rename (Fin.castAdd N) (c j)) = c j` and
`φ (X (Fin.natAdd L j)) = if j = j₀ then 1 else 0`, so applying `φ` to the whole `w`-sum gives
`if w j₀ then c j₀ else 0`; since `c j₀ ≠ 0` this recovers the bit `w j₀`.

(2) Transport along the algebra isomorphism
`(MvPolynomial.renameEquiv R e).trans (MvPolynomial.sumAlgEquiv R (Fin N) (Fin L))` for the
`e : Fin (L+N) ≃ Fin N ⊕ Fin L` with `Fin.natAdd L j ↦ Sum.inl j`, `Fin.castAdd N i ↦ Sum.inr i`,
then read off the coefficient of the monomial `Finsupp.single j₀ 1` (using `MvPolynomial.coeff_sum`,
`MvPolynomial.coeff_mul_X`, `MvPolynomial.coeff_mul_X'`, `Finsupp.mem_support_iff`).
-/
/- The computation underlying `sumRenameMulXInj`: applying the collapsing hom `φ` (which fixes
the old block `MvPolynomial (Fin L) R`, sends `X (Fin.natAdd L j₀)` to `1` and every other fresh
variable to `0`) to the `w`-sum yields the single term `c j₀` exactly when the bit `w j₀` is set. -/
private lemma sumRenameMulXInj_aeval {R : Type*} [CommRing R] {L N : ℕ}
    (c : Fin N → MvPolynomial (Fin L) R) (j₀ : Fin N) (w : Fin N → Bool) :
    MvPolynomial.aeval (Fin.addCases (fun i : Fin L => MvPolynomial.X i)
        (fun j : Fin N => if j = j₀ then (1 : MvPolynomial (Fin L) R) else 0))
      (∑ j : Fin N, if w j then
        MvPolynomial.rename (Fin.castAdd N) (c j) * MvPolynomial.X (Fin.natAdd L j) else 0)
    = if w j₀ then c j₀ else 0 := by
  rw [map_sum]
  have hterm : ∀ j : Fin N,
      MvPolynomial.aeval (Fin.addCases (fun i : Fin L => MvPolynomial.X i)
          (fun j : Fin N => if j = j₀ then (1 : MvPolynomial (Fin L) R) else 0))
        (if w j = true then
          MvPolynomial.rename (Fin.castAdd N) (c j) * MvPolynomial.X (Fin.natAdd L j) else 0)
      = if w j = true then c j * (if j = j₀ then 1 else 0) else 0 := by
    intro j
    have hmap : ((fun i => Fin.addCases (fun i : Fin L => MvPolynomial.X i)
          (fun j : Fin N => if j = j₀ then (1 : MvPolynomial (Fin L) R) else 0) i)
          ∘ Fin.castAdd N)
        = (MvPolynomial.X : Fin L → MvPolynomial (Fin L) R) := by
      funext i
      simp
    by_cases hw : w j = true
    · rw [if_pos hw]
      rw [map_mul, MvPolynomial.aeval_X, MvPolynomial.aeval_rename]
      rw [hmap, MvPolynomial.aeval_X_left_apply, Fin.addCases_right, if_pos hw]
    · rw [if_neg hw, map_zero, if_neg hw]
  simp only [hterm]
  rw [Finset.sum_eq_single j₀]
  · by_cases hw : w j₀ = true <;> simp [hw]
  · intro j _ hj
    rw [if_neg hj, mul_zero]
    by_cases hw : w j = true <;> simp [hw]
  · intro hj
    exact absurd (Finset.mem_univ j₀) hj

theorem sumRenameMulXInj {R : Type*} [CommRing R] {L N : ℕ}
    (c : Fin N → MvPolynomial (Fin L) R) (hne : ∀ j, c j ≠ 0) :
    Function.Injective (fun w : Fin N → Bool =>
      ∑ j : Fin N, if w j then
        MvPolynomial.rename (Fin.castAdd N) (c j) * MvPolynomial.X (Fin.natAdd L j) else 0) := by
  intro w w' hww
  funext j₀
  -- The collapsing `R`-algebra hom: it fixes the old block, sends the fresh variable `X (L + j₀)`
  -- to `1` and every other fresh variable to `0`.
  have h1 := sumRenameMulXInj_aeval c j₀ w
  have h2 := sumRenameMulXInj_aeval c j₀ w'
  have hcongr := congrArg
    (MvPolynomial.aeval (Fin.addCases (fun i : Fin L => MvPolynomial.X i)
      (fun j : Fin N => if j = j₀ then (1 : MvPolynomial (Fin L) R) else 0))) hww
  have heq : (if w j₀ then c j₀ else 0) = (if w' j₀ then c j₀ else 0) :=
    h1.symm.trans (hcongr.trans h2)
  by_cases hw : w j₀ = true
  · have hw' : w' j₀ = true := by
      by_contra hc
      rw [if_pos hw, if_neg hc] at heq
      exact hne j₀ heq
    rw [hw, hw']
  · have hw0 : w j₀ = false := by
      cases h : w j₀
      · rfl
      · exact absurd h hw
    have hw' : w' j₀ = false := by
      by_contra hc
      have hc' : w' j₀ = true := by
        cases h : w' j₀
        · exact absurd h hc
        · rfl
      rw [if_neg hw, if_pos hc'] at heq
      exact hne j₀ heq.symm
    rw [hw0, hw']

end Work.Peluse.UControl
