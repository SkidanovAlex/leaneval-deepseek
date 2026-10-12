import Mathlib.Algebra.Algebra.Basic
import Mathlib.Algebra.Order.Star.Real
import Submission.Work.BoseB7.Estimates
import Submission.Work.BoseB7.bp_cauchy
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Work.BoseBogFS.linHi_form_le` — the linear term of the Bogoliubov Hamiltonian

The chapter's `eq:Combined1` has a *linear* slot: the Bogoliubov linear term

  `Σ_{k ∈ S} (c_k/2) (a_k + a_k† + a_{-k} + a_{-k}†)`

(a sum over a *negation-symmetric* mode set `S` with an *even* coefficient
`c_k = c_{-k}`, the reflection symmetry of the box).  This module bounds its
Fock quadratic form by the state's one-body `a`-energies: if

  `Σ_{k ∈ S} ⟨a_k f, a_k f⟩ ≤ K`   (the hypothesis `hnorm`),

then

  `|⟨f, L f⟩| ≤ 2 √(Σ_{k∈S} c_k²) √K √‖f‖²`.

## The argument (three independent pieces, all proved here)

* **`sum_neg_comp_eq_of_symm`** — a sum over a negation-symmetric finset may be
  reindexed by `k ↦ -k`.

* **`linHi_op_eq`** — the `(1/2)`-weighted four-term sum is exactly the sum of
  the annihilation and creation halves: the `k ↦ -k` half of the summand is the
  `+k` half again (reindexing), so the two halves double and the `1/2` cancels:
  `L f = (Σ_k c_k a_k) f + (Σ_k c_k a_k†) f`.

* **`bp_sum_a_le`** — the ℓ²-bound for a weighted annihilation sum.  Since
  `a_k†` is the adjoint of `a_k`, the form of `L` is twice its annihilation part
  `A = Σ_k c_k a_k`; for `A` one has
  `⟨A f, f⟩ = Σ_k c_k ⟨a_k f, f⟩`, so the *finset* Cauchy–Schwarz inequality
  (`Finset.sum_mul_sq_le_sq_mul_sq`, the ℓ² bound, sharper in `c` than the ℓ¹
  bound of `Work.BoseB7.linearTerm_bound`), together with the per-mode
  Cauchy–Schwarz `⟨a_k f, f⟩² ≤ ⟨a_k f, a_k f⟩⟨f, f⟩`
  (`Work.BoseB7.bp_cauchy_sq`) and the hypothesis `hnorm`, gives
  `|⟨A f, f⟩| ≤ √(Σc²)·√(K‖f‖²) = √(Σc²)√K√‖f‖²`.

The main theorem `linHi_form_le` is the assembly: `linHi_op_eq` reduces the form
of `L` to that of `A` (plus its adjoint, which has the same form), and
`bp_sum_a_le` bounds it.
-/

open scoped BigOperators

namespace Work.BoseBogFS

/-- **Reindexing a sum over a negation-symmetric finset**: if `k ∈ S ↔ -k ∈ S`
then `Σ_{k ∈ S} g (-k) = Σ_{k ∈ S} g k`.

The map `k ↦ -k` is an involution of the finite set `S`; the sum is unchanged
because a finite sum only depends on the multiset of indices. -/
lemma sum_neg_comp_eq_of_symm {α M : Type*} [AddCommGroup α] [AddCommMonoid M]
    (S : Finset α) (hS : ∀ k : α, k ∈ S ↔ -k ∈ S) (g : α → M) :
    (∑ k ∈ S, g (-k)) = ∑ k ∈ S, g k := by
  rw [Finset.sum_nbij' (fun k => -k) (fun k => -k)]
  · intro a ha; exact (hS a).mp ha
  · intro a ha; exact (hS a).mp ha
  · intro a ha; simp
  · intro a ha; simp
  · intro a ha; rfl

/-- **The linear Bogoliubov sum is the sum of its two halves.**  For a
negation-symmetric `S` and an even coefficient `c` (`c (-k) = c k`),

  `(Σ_{k ∈ S} (c_k/2) (a_k + a_k† + a_{-k} + a_{-k}†)) f
     = (Σ_{k ∈ S} c_k a_k) f + (Σ_{k ∈ S} c_k a_k†) f`.

The two occurrences `a_{-k} + a_{-k}†` and `a_k + a_k†` of the summand are the
same after the reindexing `k ↦ -k` (`sum_neg_comp_eq_of_symm`, using evenness of
`c`), so the `1/2` cancels against the doubling. -/
lemma linHi_op_eq {Mode : Type*} [AddCommGroup Mode] [Fintype Mode]
    (F : Work.BoseB7.FockData Mode) (S : Finset Mode) (c : Mode → ℝ) (f : F.H)
    (hS : ∀ k : Mode, k ∈ S ↔ -k ∈ S) (hc : ∀ k : Mode, c (-k) = c k) :
    (∑ k ∈ S, ((1 / 2 : ℝ) * c k) •
        (F.a k + F.aDag k + F.a (-k) + F.aDag (-k))) f
      = (∑ k ∈ S, (c k) • F.a k) f + (∑ k ∈ S, (c k) • F.aDag k) f := by
  -- split each summand into its `+k` and `-k` halves, and the sum into two sums
  have hterm : ∀ k ∈ S, (((1 / 2 : ℝ) * c k) •
        (F.a k + F.aDag k + F.a (-k) + F.aDag (-k))) f
      = ((1 / 2 : ℝ) * c k) • ((F.a k + F.aDag k) f)
        + ((1 / 2 : ℝ) * c k) • ((F.a (-k) + F.aDag (-k)) f) := by
    intro k _
    have hassoc : (F.a k + F.aDag k + F.a (-k) + F.aDag (-k) : F.H →ₗ[ℝ] F.H)
        = (F.a k + F.aDag k) + (F.a (-k) + F.aDag (-k)) := by abel
    rw [hassoc, LinearMap.smul_apply, LinearMap.add_apply, smul_add]
  have hs1 : (∑ k ∈ S, (((1 / 2 : ℝ) * c k) •
        (F.a k + F.aDag k + F.a (-k) + F.aDag (-k))) f)
      = (∑ k ∈ S, ((1 / 2 : ℝ) * c k) • ((F.a k + F.aDag k) f))
        + (∑ k ∈ S, ((1 / 2 : ℝ) * c k) • ((F.a (-k) + F.aDag (-k)) f)) := by
    rw [← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl hterm
  -- the `-k` half is the `+k` half after reindexing
  have hre : (∑ k ∈ S, ((1 / 2 : ℝ) * c k) • ((F.a (-k) + F.aDag (-k)) f))
      = (∑ k ∈ S, ((1 / 2 : ℝ) * c k) • ((F.a k + F.aDag k) f)) := by
    rw [Finset.sum_nbij' (fun k => -k) (fun k => -k)]
    · intro a ha; exact (hS a).mp ha
    · intro a ha; exact (hS a).mp ha
    · intro a ha; simp
    · intro a ha; simp
    · intro a ha; rw [hc a]
  -- the two halves double, cancelling the `1/2`
  have hdbl : (∑ k ∈ S, ((1 / 2 : ℝ) * c k) • ((F.a k + F.aDag k) f))
        + (∑ k ∈ S, ((1 / 2 : ℝ) * c k) • ((F.a k + F.aDag k) f))
      = (∑ k ∈ S, (c k) • ((F.a k + F.aDag k) f)) := by
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl (fun k hk => ?_)
    rw [← add_smul]
    congr 1
    ring
  -- separate the annihilation and creation halves
  have hfin : (∑ k ∈ S, (c k) • ((F.a k + F.aDag k) f))
      = (∑ k ∈ S, (c k) • F.a k) f + (∑ k ∈ S, (c k) • F.aDag k) f := by
    rw [LinearMap.sum_apply, LinearMap.sum_apply, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl (fun k hk => ?_)
    simp only [LinearMap.smul_apply, LinearMap.add_apply, smul_add]
  rw [LinearMap.sum_apply]
  rw [hs1, hre, hdbl, hfin]

/-- **The ℓ²-bound for a weighted annihilation sum.**  For a mode set `S`, real
coefficients `c` and a state `f` whose `a`-energies sum to at most `K`,

  `|⟨(Σ_{k ∈ S} c_k a_k) f, f⟩| ≤ √(Σ_{k ∈ S} c_k²)·√K·√‖f‖²`.

Proof: the form expands as `Σ_k c_k ⟨a_k f, f⟩`; the finset Cauchy–Schwarz
inequality (`Finset.sum_mul_sq_le_sq_mul_sq`) gives the `ℓ²` factor
`√(Σ c_k²)`, the per-mode Cauchy–Schwarz `⟨a_k f, f⟩² ≤ ⟨a_k f, a_k f⟩‖f‖²`
(`Work.BoseB7.bp_cauchy_sq`) turns `Σ_k ⟨a_k f, f⟩²` into
`‖f‖²·Σ_k ⟨a_k f, a_k f⟩ ≤ ‖f‖²K`, and `√(‖f‖²K) = √‖f‖²·√K`. -/
lemma bp_sum_a_le {Mode : Type*} [AddCommGroup Mode] [Fintype Mode]
    (F : Work.BoseB7.FockData Mode) (S : Finset Mode) (c : Mode → ℝ) (f : F.H) (K : ℝ)
    (hK : 0 ≤ K) (hnorm : (∑ k ∈ S, F.bp (F.a k f) (F.a k f)) ≤ K) :
    |F.bp ((∑ k ∈ S, (c k) • F.a k) f) f|
      ≤ Real.sqrt (∑ k ∈ S, (c k) ^ 2) * Real.sqrt K * Real.sqrt (F.bp f f) := by
  -- the form of `A = Σ_k c_k a_k` is `Σ_k c_k ⟨a_k f, f⟩`
  have hformA : F.bp ((∑ k ∈ S, (c k) • F.a k) f) f
      = ∑ k ∈ S, c k * F.bp (F.a k f) f := by
    simp only [LinearMap.sum_apply, LinearMap.smul_apply, map_sum, map_smul, smul_eq_mul]
  -- Cauchy–Schwarz in the index `k`
  have hcs : (∑ k ∈ S, c k * F.bp (F.a k f) f) ^ 2
      ≤ (∑ k ∈ S, (c k) ^ 2) * (∑ k ∈ S, (F.bp (F.a k f) f) ^ 2) :=
    Finset.sum_mul_sq_le_sq_mul_sq S c (fun k => F.bp (F.a k f) f)
  -- the per-mode Cauchy–Schwarz, summed
  have hW : 0 ≤ F.bp f f := F.bp_nonneg f
  have hkey : ∑ k ∈ S, (F.bp (F.a k f) f) ^ 2 ≤ F.bp f f * K := by
    have h1 : ∑ k ∈ S, (F.bp (F.a k f) f) ^ 2
        ≤ ∑ k ∈ S, F.bp (F.a k f) (F.a k f) * F.bp f f :=
      Finset.sum_le_sum
        (fun k _ => Work.BoseB7.bp_cauchy_sq F (F.a k f) f)
    have h2 : ∑ k ∈ S, F.bp (F.a k f) (F.a k f) * F.bp f f
        = (∑ k ∈ S, F.bp (F.a k f) (F.a k f)) * F.bp f f :=
      (Finset.sum_mul S (fun k => F.bp (F.a k f) (F.a k f)) (F.bp f f)).symm
    have h4 : (∑ k ∈ S, F.bp (F.a k f) (F.a k f)) * F.bp f f ≤ K * F.bp f f :=
      mul_le_mul_of_nonneg_right hnorm hW
    linarith [h1, h2, h4]
  have hsD : 0 ≤ ∑ k ∈ S, (c k) ^ 2 := Finset.sum_nonneg (fun k _ => sq_nonneg _)
  calc |F.bp ((∑ k ∈ S, (c k) • F.a k) f) f|
      = Real.sqrt ((F.bp ((∑ k ∈ S, (c k) • F.a k) f) f) ^ 2) :=
        (Real.sqrt_sq_eq_abs _).symm
    _ = Real.sqrt ((∑ k ∈ S, c k * F.bp (F.a k f) f) ^ 2) := by rw [hformA]
    _ ≤ Real.sqrt ((∑ k ∈ S, (c k) ^ 2) * (∑ k ∈ S, (F.bp (F.a k f) f) ^ 2)) :=
        Real.sqrt_le_sqrt hcs
    _ = Real.sqrt (∑ k ∈ S, (c k) ^ 2)
          * Real.sqrt (∑ k ∈ S, (F.bp (F.a k f) f) ^ 2) := Real.sqrt_mul hsD _
    _ ≤ Real.sqrt (∑ k ∈ S, (c k) ^ 2) * Real.sqrt (F.bp f f * K) :=
        mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt hkey) (Real.sqrt_nonneg _)
    _ = Real.sqrt (∑ k ∈ S, (c k) ^ 2) * (Real.sqrt (F.bp f f) * Real.sqrt K) := by
        rw [Real.sqrt_mul hW]
    _ = Real.sqrt (∑ k ∈ S, (c k) ^ 2) * Real.sqrt K * Real.sqrt (F.bp f f) := by ring

/-- **The form of the linear Bogoliubov term is bounded by the `a`-energies.**

For a *negation-symmetric* mode set `S` (`hS`), an *even* coefficient family `c`
(`hc`), a state `f` and a bound `K ≥ Σ_{k ∈ S} ⟨a_k f, a_k f⟩`,

  `|⟨f, Σ_{k ∈ S} (c_k/2)(a_k + a_k† + a_{-k} + a_{-k}†) f⟩|
     ≤ 2 √(Σ_{k ∈ S} c_k²) √K √‖f‖²`.

This is the linear slot of `eq:Combined1` at the level of the `B7` Fock
interface: the symmetry assumptions are exactly the box's reflection symmetry
`c(-k) = c_k`, `k ∈ S ↔ -k ∈ S`, which makes the four-term summand collapse to
`c_k (a_k + a_k†)` (`linHi_op_eq`), whose form is twice that of the annihilation
part `Σ_k c_k a_k` (adjointness of `a_k†` and symmetry of `bp`), bounded by
`bp_sum_a_le`. -/
theorem linHi_form_le {Mode : Type*} [AddCommGroup Mode] [Fintype Mode] [DecidableEq Mode]
    (F : Work.BoseB7.FockData Mode) (S : Finset Mode) (c : Mode → ℝ) (f : F.H) (K : ℝ)
    (hS : ∀ k : Mode, k ∈ S ↔ -k ∈ S) (hc : ∀ k : Mode, c (-k) = c k)
    (hK : 0 ≤ K) (hnorm : (∑ k ∈ S, F.bp (F.a k f) (F.a k f)) ≤ K) :
    |F.bp ((∑ k ∈ S, ((1 / 2 : ℝ) * c k) •
        (F.a k + F.aDag k + F.a (-k) + F.aDag (-k))) f) f|
      ≤ 2 * Real.sqrt (∑ k ∈ S, (c k) ^ 2) * Real.sqrt K * Real.sqrt (F.normSq f) := by
  -- the form of the creation half equals the form of the annihilation half
  have hadj : F.bp ((∑ k ∈ S, (c k) • F.aDag k) f) f
      = F.bp ((∑ k ∈ S, (c k) • F.a k) f) f := by
    have h1 : F.bp ((∑ k ∈ S, (c k) • F.aDag k) f) f
        = ∑ k ∈ S, c k * F.bp f (F.a k f) := by
      simp only [LinearMap.sum_apply, LinearMap.smul_apply, map_sum, map_smul, smul_eq_mul,
        F.aDag_adjoint]
    have h2 : F.bp f ((∑ k ∈ S, (c k) • F.a k) f)
        = ∑ k ∈ S, c k * F.bp f (F.a k f) := by
      simp only [LinearMap.sum_apply, LinearMap.smul_apply, map_sum, map_smul, smul_eq_mul]
    rw [h1, ← F.bp_symm f ((∑ k ∈ S, (c k) • F.a k) f), h2]
  -- the form of `L` is twice that of `A`
  have hL : F.bp ((∑ k ∈ S, ((1 / 2 : ℝ) * c k) •
        (F.a k + F.aDag k + F.a (-k) + F.aDag (-k))) f) f
      = 2 * F.bp ((∑ k ∈ S, (c k) • F.a k) f) f := by
    rw [linHi_op_eq F S c f hS hc, map_add, LinearMap.add_apply, hadj]
    ring
  calc |F.bp ((∑ k ∈ S, ((1 / 2 : ℝ) * c k) •
        (F.a k + F.aDag k + F.a (-k) + F.aDag (-k))) f) f|
      = 2 * |F.bp ((∑ k ∈ S, (c k) • F.a k) f) f| := by
        rw [hL, abs_mul, abs_of_nonneg (show (0 : ℝ) ≤ 2 by norm_num)]
    _ ≤ 2 * (Real.sqrt (∑ k ∈ S, (c k) ^ 2) * Real.sqrt K * Real.sqrt (F.bp f f)) :=
        mul_le_mul_of_nonneg_left (bp_sum_a_le F S c f K hK hnorm) (by norm_num)
    _ = 2 * Real.sqrt (∑ k ∈ S, (c k) ^ 2) * Real.sqrt K * Real.sqrt (F.normSq f) := by
        rw [Work.BoseB7.FockData.normSq]; ring

end Work.BoseBogFS
