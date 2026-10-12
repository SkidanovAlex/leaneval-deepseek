import Mathlib.Tactic.Module
import Mathlib.Algebra.CharP.Defs
import Mathlib.Algebra.Order.Star.Real
import Submission.Work.BoseBogFS.sum_normSq_bogBShift_le
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Submission.Work.BoseBogFS.qw_KzBogFS_le_window`

The **upper** bound companion of `qw_KzBogFS_ge` (FS `thm:BogHamDiag`'s zero-point
bound): on a window state `f` (`T.NWindow E.bigM f`) the Bogoliubov quadratic
`KzBogFS` is at most

  `(Dsup·(600·𝓜 + 32·#Mode + 32) + #Mode + 1)·‖f‖²`

whenever `𝒟_k ≤ Dsup` for every label `k`.

## The proof

`qw_KzBogFS_eq` (the diagonalised value of `𝒦^Bog`, FS `eq:BogIdentity`) gives the
*exact* identity

  `⟨f, 𝒦^Bog f⟩ = Σ_k 𝒟_k‖b̂_k f‖² − (Σ_k ½(𝒟_kα_k²·ccr2_k + κ_k))·‖f‖²`,

with `b̂_k = b_k + c_k` FS's shifted squeezing operator.  The companion lemma
`sum_normSq_bogBShift_le` bounds `Σ_k‖b̂_k f‖² ≤ (600𝓜 + 32#Mode + 32)‖f‖²`, and
`𝒟_k ≤ Dsup` upgrades the first term.  It remains to see that the subtracted
constant is non-negative, i.e. that the commutator sum `ccr2_k` is non-negative —
this is the one genuinely non-formal point, and it is where the **window**
hypothesis enters, through the number operator `T.N` alone:

* a nonzero `T.N`-eigenvector `f` with `T.N f = m·f`, `m ∈ ℕ`, forces `0 ≤ ccrK k k`
  for *every* `k` (`ccrK_nonneg_of_eigenvector` below).  Indeed the grading
  `N∘a_k = a_k∘N − a_k` (`T.N_a`) gives `T.N (a_k^j f) = (m−j)·a_k^j f`, so
  `a_k^{m+1} f` would have `N`-eigenvalue `−1`, which is impossible by
  `T.N_nonneg` (`F.bp_def`).  Hence with `j` minimal such that `a_k^j f = 0`,
  the vector `g = a_k^{j−1} f` is nonzero and annihilated by `a_k`, so
  `0 ≤ ‖a_k† g‖² = ⟨g, a_k a_k† g⟩ = ‖a_k g‖² + ccrK k k·‖g‖² = ccrK k k·‖g‖²`.
* a nonzero window state has a nonzero half of the family `φ` of `N`-eigenvectors
  defining it, so the previous point applies.

Consequently `Σ_k ½(𝒟_kα_k²·ccr2_k + κ_k) ≥ 0` (`𝒟_k ≥ 0`, `α_k² ≥ 0`,
`ccr2_k ≥ 0` componentwise, and `κ_k = 2𝒟_kγ_k² ≥ 0`), and the two terms of the
right-hand side give the statement.
-/

namespace Work.BoseBogFS

noncomputable section

open scoped BigOperators

set_option autoImplicit false
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false

variable {Mode : Type*} [AddCommGroup Mode] [Fintype Mode] [DecidableEq Mode]

/-- **A nonzero `T.N`-eigenvector forces the box commutator kernel to be non-negative.**
If `f ≠ 0` and `T.N f = m·f` with `m : ℕ`, then `0 ≤ [a_k, a_k†] = F.ccrK k k` for every
label `k`.

The grading `N∘a_k = a_k∘N − a_k` pushes `f` down the `N`-ladder,
`T.N (a_k^j f) = (m−j)·a_k^j f`; at `j = m+1` the eigenvalue is `−1`, which
`T.N_nonneg` forbids, so some `a_k^j f` vanishes, and the last nonzero `g = a_k^{j−1}f`
satisfies `a_k g = 0`.  Then `‖a_k†g‖² = ⟨g, a_k a_k† g⟩ = ‖a_k g‖² + ccrK k k·‖g‖²`
(`F.ccr`) leaves `ccrK k k·‖g‖² ≥ 0`. -/
theorem ccrK_nonneg_of_eigenvector (F : Work.BoseB7.FockData Mode)
    (T : Work.BoseB7A.TildeData F) (k : Mode) (f : F.H) (m : ℕ) (hf : f ≠ 0)
    (heig : T.N f = (m : ℝ) • f) : 0 ≤ F.ccrK k k := by
  classical
  -- the `a_k`-orbit of `f`
  set u : ℕ → F.H := fun j => (F.a k)^[j] f with hu
  have hu0 : u 0 = f := rfl
  have husucc : ∀ j : ℕ, u (j + 1) = F.a k (u j) :=
    fun j => Function.iterate_succ_apply' (F.a k) j f
  -- the `N`-eigenvalue along the orbit
  have hiter : ∀ j : ℕ, T.N (u j) = ((m : ℝ) - (j : ℝ)) • u j := by
    intro j
    induction j with
    | zero => simpa [hu0] using heig
    | succ j ih =>
      have hNa : T.N (F.a k (u j)) = F.a k (T.N (u j)) - F.a k (u j) := by
        have h := congrArg (fun (S : F.H →ₗ[ℝ] F.H) => S (u j)) (T.N_a k)
        simpa [LinearMap.comp_apply, LinearMap.sub_apply] using h
      rw [husucc j, hNa, ih, map_smul, Nat.cast_succ]
      module
  -- the orbit dies at `m+1` (eigenvalue `-1` is impossible)
  have hlast : u (m + 1) = 0 := by
    have hN : T.N (u (m + 1)) = (-1 : ℝ) • u (m + 1) := by
      have h := hiter (m + 1)
      have hc : ((m : ℝ) - (((m + 1 : ℕ) : ℝ))) = -1 := by push_cast; ring
      rwa [hc] at h
    have hq : 0 ≤ F.bp ((-1 : ℝ) • u (m + 1)) (u (m + 1)) := by
      rw [← hN]; exact T.N_nonneg _
    rw [map_smul, LinearMap.smul_apply, smul_eq_mul, neg_one_mul] at hq
    have hnn : 0 ≤ F.bp (u (m + 1)) (u (m + 1)) := F.bp_nonneg _
    have hzero : F.bp (u (m + 1)) (u (m + 1)) = 0 := by linarith
    exact F.bp_def _ hzero
  -- the last nonzero vector of the orbit
  set P : ℕ → Prop := fun j => 1 ≤ j ∧ u j = 0 with hP
  have hex : ∃ j, P j := ⟨m + 1, Nat.succ_le_succ (Nat.zero_le m), hlast⟩
  set j := Nat.find hex with hj
  have hjP : P j := Nat.find_spec hex
  have hjmin : ∀ i, i < j → ¬ P i := fun i hi => Nat.find_min hex hi
  have hj1 : 1 ≤ j := hjP.1
  have hj0 : u j = 0 := hjP.2
  set g : F.H := u (j - 1) with hg
  have hgne : g ≠ 0 := by
    rcases Nat.eq_zero_or_pos (j - 1) with h | h
    · rw [hg, h, hu0]; exact hf
    · intro hc
      exact hjmin (j - 1) (by omega) ⟨h, by rw [hg] at hc; exact hc⟩
  have hag : F.a k g = 0 := by
    have hj : j = (j - 1) + 1 := by omega
    have : F.a k g = u j := by
      rw [hg]
      conv_rhs => rw [hj]
      exact (husucc (j - 1)).symm
    rw [this, hj0]
  -- `g` realises the commutator as a norm
  have hop : F.a k (F.aDag k g) = F.aDag k (F.a k g) + (F.ccrK k k) • g := by
    have h := congrArg (fun (S : F.H →ₗ[ℝ] F.H) => S g) (F.ccr k k)
    simpa using h
  have hop' : F.a k (F.aDag k g) = (F.ccrK k k) • g := by rw [hop, hag, map_zero, zero_add]
  have hkey : F.bp (F.aDag k g) (F.aDag k g) = (F.ccrK k k) * F.bp g g := by
    rw [F.aDag_adjoint k g (F.aDag k g), hop']
    simp [smul_eq_mul]
  have hgpos : 0 < F.bp g g :=
    lt_of_le_of_ne (F.bp_nonneg g) (fun h => hgne (F.bp_def g h.symm))
  nlinarith [F.bp_nonneg (F.aDag k g), hkey, hgpos]

theorem qw_KzBogFS_le_window {Mode : Type*} [AddCommGroup Mode] [Fintype Mode]
    [DecidableEq Mode] (F : Work.BoseB7.FockData Mode) (T : Work.BoseB7A.TildeData F)
    (E : Work.BoseB7.Q3Env Mode) (ρ Cn Dsup : ℝ)
    (hnum : Work.BoseBogFS.BogNumeric F E ρ) (hbigM : 0 ≤ E.bigM)
    (hDsup : ∀ k : Mode, Work.BoseBogFS.bogD E ρ k ≤ Dsup) (hCn : Cn ≤ 16)
    (hBessel : ∀ f : F.H, F.bp ((∑ k : Mode, F.nOp k) f) f ≤ Cn * F.bp (T.N f) f)
    (hγ : ∀ k : Mode, (Work.BoseBogFS.bogGamma E ρ k) ^ 2 ≤ 1)
    (hα : ∀ k : Mode, (Work.BoseBogFS.bogAlpha E ρ k) ^ 2 ≤ 1) :
    ∀ f : F.H, T.NWindow E.bigM f →
      F.qw f (Work.BoseBogFS.KzBogFS F E ρ)
        ≤ (Dsup * (600 * E.bigM + 32 * (Fintype.card Mode : ℝ) + 32)
            + (Fintype.card Mode : ℝ) + 1) * F.normSq f := by
  intro f hf
  have hfwin : T.NWindow E.bigM f := hf
  by_cases hf0 : f = 0
  · subst hf0
    rw [Work.BoseB7.FockData.qw, Work.BoseB7.FockData.normSq]
    simp
  obtain ⟨φ, hφeig, hφsum⟩ := hf
  -- a nonzero window state carries a nonzero `N`-eigenvector
  have hex : ∃ m : ℕ, φ m ≠ 0 := by
    by_contra h
    exact hf0 (by
      rw [hφsum]
      exact Finset.sum_eq_zero fun m _ => by
        by_contra hc
        exact h ⟨m, hc⟩)
  obtain ⟨m, hm⟩ := hex
  -- hence the commutator kernel is non-negative on every label
  have hccrKnn : ∀ k : Mode, 0 ≤ F.ccrK k k :=
    fun k => ccrK_nonneg_of_eigenvector F T k (φ m) m hm (hφeig m)
  have hccr2nn : ∀ k : Mode, 0 ≤ Work.BoseBogFS.bogCcr2 F k := fun k => by
    rw [Work.BoseBogFS.bogCcr2]
    exact add_nonneg (hccrKnn k) (hccrKnn (-k))
  have hDnn : ∀ k : Mode, 0 ≤ Work.BoseBogFS.bogD E ρ k := fun k => by
    rw [Work.BoseBogFS.bogD]
    exact le_of_lt (Submission.BoseGases.bogD_pos (A := Work.BoseBogFS.bogA E ρ k)
      (B := Work.BoseBogFS.bogB E ρ k) (hnum.hA k) (hnum.hB k))
  have hDsup0 : 0 ≤ Dsup := le_trans (hDnn 0) (hDsup 0)
  have hκnn : ∀ k : Mode, 0 ≤ Work.BoseB6.bogKappaErr (Work.BoseBogFS.bogA E ρ k)
      (Work.BoseBogFS.bogB E ρ k) (Work.BoseBogFS.bogC E ρ k) := fun k => by
    rw [Work.BoseB6.bogKappaErr]
    exact div_nonneg (by positivity) (le_of_lt (hnum.hAB k))
  -- so the subtracted constant is non-negative
  have hSnn : 0 ≤ ∑ k : Mode, (1 / 2 : ℝ) * (Work.BoseBogFS.bogD E ρ k
      * (Work.BoseBogFS.bogAlpha E ρ k) ^ 2 * Work.BoseBogFS.bogCcr2 F k
      + Work.BoseB6.bogKappaErr (Work.BoseBogFS.bogA E ρ k) (Work.BoseBogFS.bogB E ρ k)
          (Work.BoseBogFS.bogC E ρ k)) :=
    Finset.sum_nonneg fun k _ => mul_nonneg (by norm_num)
      (add_nonneg (mul_nonneg (mul_nonneg (hDnn k) (sq_nonneg _)) (hccr2nn k)) (hκnn k))
  have hid := qw_KzBogFS_eq F E ρ f hnum.hA hnum.hB hnum.hAB hnum.hAe hnum.hBe hnum.hCe
  have hshift := sum_normSq_bogBShift_le F T E ρ Cn hnum hbigM hBessel hCn hγ hα f hfwin
  have hDsum : (∑ k : Mode, Work.BoseBogFS.bogD E ρ k
        * F.normSq ((Work.BoseBogFS.bogBShift F E ρ k) f))
      ≤ Dsup * ∑ k : Mode, F.normSq ((Work.BoseBogFS.bogBShift F E ρ k) f) := by
    rw [Finset.mul_sum]
    exact Finset.sum_le_sum fun k _ =>
      mul_le_mul_of_nonneg_right (hDsup k) (F.bp_nonneg _)
  have hfnn : 0 ≤ F.normSq f := F.bp_nonneg f
  have hcard : 0 ≤ (Fintype.card Mode : ℝ) + 1 := by positivity
  rw [hid]
  calc (∑ k : Mode, Work.BoseBogFS.bogD E ρ k
          * F.normSq ((Work.BoseBogFS.bogBShift F E ρ k) f))
        - (∑ k : Mode, (1 / 2 : ℝ) * (Work.BoseBogFS.bogD E ρ k
              * (Work.BoseBogFS.bogAlpha E ρ k) ^ 2 * Work.BoseBogFS.bogCcr2 F k
              + Work.BoseB6.bogKappaErr (Work.BoseBogFS.bogA E ρ k)
                  (Work.BoseBogFS.bogB E ρ k) (Work.BoseBogFS.bogC E ρ k))) * F.normSq f
      ≤ (∑ k : Mode, Work.BoseBogFS.bogD E ρ k
          * F.normSq ((Work.BoseBogFS.bogBShift F E ρ k) f)) :=
        sub_le_self _ (mul_nonneg hSnn hfnn)
    _ ≤ Dsup * ∑ k : Mode, F.normSq ((Work.BoseBogFS.bogBShift F E ρ k) f) := hDsum
    _ ≤ Dsup * ((600 * E.bigM + 32 * (Fintype.card Mode : ℝ) + 32) * F.normSq f) :=
        mul_le_mul_of_nonneg_left hshift hDsup0
    _ ≤ (Dsup * (600 * E.bigM + 32 * (Fintype.card Mode : ℝ) + 32)
          + (Fintype.card Mode : ℝ) + 1) * F.normSq f := by
        nlinarith [hcard, hfnn]

end

end Work.BoseBogFS
