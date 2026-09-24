/-
# `APSwitchUpper` — the switched (arithmetic-progression) upper bound of Chen's argument

This is the vocabulary module of the area that bounds

  `Σ_{q ∈ winPrimes M Y} apMass x M q`,

the term subtracted by the `1/2·Σ_q` of Chen's switch (`Submission.switch_decomposition`).
It supplies:

* `apMassD x M d` — the `θ`-mass of the `M`-rough shifted primes divisible by `d`
  (so that `apMassD x M q = apMass x M q` definitionally);
* `lambdaUp D M m` — the Rosser–Iwaniec upper-bound (`λ⁺`) weight sum over the admissible
  chain set `Chen.Gp 1 D M`, evaluated at `m`;
* `bvSum x K` — the Bombieri–Vinogradov remainder sum `Σ_{d odd ≤ K} |θ_d(x) − x/φ(d)|`;
* `apLevel K q = K/q` — the level of distribution attached to the residue class `q`.

Everything downstream (`Mobius.lean`, `UpperSieve.lean`, `Window.lean`, `Error.lean`,
`Main.lean`) is stated in this vocabulary.
-/
import Submission.Chen.SwitchDefs
import Submission.Commons.NumberTheory.BombieriVinogradov.level_of_distribution_shift_vonMangoldt

open Finset
open scoped BigOperators
open Commons.NumberTheory.Chen

namespace Work.NumberTheory.Chen.APSwitchUpper

noncomputable section

attribute [local instance] Classical.propDecidable

/-! ## Vocabulary -/

/-- `θ`-mass of the `M`-rough shifted primes `p ≤ x` with `d ∣ p + 2`.

`apMassD x M d = Σ_{p ∈ s0Set x M, d ∣ p+2} log p`, so that `apMassD x M q` is exactly the
`Submission.apMass x M q` of the switch. -/
noncomputable def apMassD (x M d : ℕ) : ℝ :=
  ((Submission.s0Set x M).filter (fun p => d ∣ p + 2)).sum (fun p => Real.log (p : ℝ))

/-- The Rosser–Iwaniec upper-bound (`λ⁺`) weight sum over the admissible chain set
`Gp 1 D M`:  `Σ_{c ∈ Gp 1 D M} (-1)^{|c|} · 1_{lprod c ∣ m}`.

This is the pointwise majorant of the indicator `ChenEight.Id m M` that truncates the
Möbius sum at level `D` (see `Id_le_lambdaUp`). -/
noncomputable def lambdaUp (D : ℝ) (M m : ℕ) : ℝ :=
  (Gp 1 D M).sum (fun c => (-1 : ℝ) ^ c.length * (if lprod c ∣ m then (1 : ℝ) else 0))

/-- The Bombieri–Vinogradov remainder sum over odd moduli `≤ K`:

`bvSum x K = Σ_{1 ≤ d ≤ K, d odd} |θ_d(x) − x/φ(d)|`. -/
noncomputable def bvSum (x K : ℕ) : ℝ :=
  ((Finset.Icc 1 K).filter (fun d : ℕ => d % 2 = 1)).sum (fun d => |ChenEight.rD x d|)

/-- The level of distribution attached to the residue class `q`:  `D_q = K/q`. -/
noncomputable def apLevel (K q : ℕ) : ℝ := (K : ℝ) / (q : ℝ)

/-- The Bombieri–Vinogradov cutoff `K(x) = ⌊√x / (log x)^B⌋`. -/
noncomputable def bvK (B : ℝ) (x : ℕ) : ℕ :=
  ⌊Real.sqrt (x : ℝ) / (Real.log (x : ℝ)) ^ B⌋₊

/-! ## The `β = 1` Buchstab layers of the upper-bound main term

Mirroring `Commons.NumberTheory.Chen.Tsieve2`/`Tone`/`condT` (the `β = 2` layer machinery of
`Submission/Work/NumberTheory/Chen/ri_layer_beta2.lean`), these are the layer sums of the
`β = 1` chain sets `Gp 1`/`Gm 1` underlying `MpSum`.  The Buchstab identity
`MpSum D Y = Vsieve Y + Σ_{n odd} Tsieve1 n D Y` (`mpSum_layer_identity`) is the first step
of the sharp upper-bound linear sieve. -/

/-- the terminating first layer: the chains `[q]` of the `β = 1` upper-bound set that cannot
be extended, i.e. those with `q² > D`. -/
noncomputable def Tone1 (D : ℝ) (Y : ℕ) : ℝ :=
  ∑ q ∈ (oddPrimesLt Y).filter (fun q : ℕ => ¬ ((q : ℝ) ^ ((1 : ℝ) + 1) ≤ D)),
    (1 / ((q : ℝ) - 1)) * Vsieve q

/-- the admissibility condition at position `1` of a `β = 1` chain (quadratic at odd
positions, linear at even ones). -/
def condT1 (n : ℕ) (q : ℕ) (D : ℝ) : Prop :=
  if n % 2 = 1 then (q : ℝ) ^ ((1 : ℝ) + 1) ≤ D else (q : ℝ) ≤ D

instance (n : ℕ) (q : ℕ) (D : ℝ) : Decidable (condT1 n q D) := by
  unfold condT1; split <;> infer_instance

/-- The Buchstab layer sums of the `β = 1` upper-bound sieve: `Tsieve1 n D Y` is the mass of
the chains of length `n` whose admissibility conditions hold at positions `1..n-1` and fail at
position `n`. -/
noncomputable def Tsieve1 : ℕ → ℝ → ℕ → ℝ
  | 0, D, Y => Vsieve Y
  | (n + 1), D, Y => if n = 0 then Tone1 D Y else
      ∑ q ∈ (oddPrimesLt Y).filter (fun q : ℕ => condT1 (n + 1) q D),
        (1 / ((q : ℝ) - 1)) * Tsieve1 n (D / q) q

lemma Tsieve1_zero (D : ℝ) (Y : ℕ) : Tsieve1 0 D Y = Vsieve Y := rfl

lemma Tsieve1_one (D : ℝ) (Y : ℕ) : Tsieve1 1 D Y = Tone1 D Y := by
  rw [Tsieve1]; simp

lemma Tsieve1_succ_succ (n : ℕ) (D : ℝ) (Y : ℕ) :
    Tsieve1 (n + 2) D Y =
      ∑ q ∈ (oddPrimesLt Y).filter (fun q : ℕ => condT1 (n + 2) q D),
        (1 / ((q : ℝ) - 1)) * Tsieve1 (n + 1) (D / q) q := by
  rw [Tsieve1]; simp

/-- The chain remainder attached to the residue class `q` and level `D`:
`Σ_{c ∈ Gp 1 D M} |θ_{q·lprod c}(x) − x/φ(q·lprod c)|`.

This is the part of `apMassD x M q` that the Rosser `λ⁺` sieve leaves as an error; summing it
over the window primes against `bvSum` is the injectivity lemma `sum_chainErr_le_bvSum`. -/
noncomputable def chainErr (x M q : ℕ) (D : ℝ) : ℝ :=
  (Gp 1 D M).sum (fun c => |ChenEight.rD x (q * lprod c)|)

/-! ## Elementary API -/

/-- `apMassD` at `q` is exactly the `apMass` of the switch. -/
theorem apMassD_eq_apMass (x M q : ℕ) : apMassD x M q = Submission.apMass x M q := rfl

/-- `apMassD` is the sum defining it, unfolded to a filter. -/
theorem apMassD_eq (x M d : ℕ) :
    apMassD x M d
      = ((Submission.s0Set x M).filter (fun p => d ∣ p + 2)).sum
          (fun p => Real.log (p : ℝ)) := rfl

/-- `apMassD (x) M 1` is the total `θ`-mass of the `M`-rough shifted primes. -/
theorem apMassD_one (x M : ℕ) :
    apMassD x M 1 = (Submission.s0Set x M).sum (fun p => Real.log (p : ℝ)) := by
  rw [apMassD_eq]
  refine Finset.sum_congr ?_ (fun p _ => rfl)
  ext p
  simp

/-- `apMassD` is nonnegative. -/
theorem apMassD_nonneg (x M d : ℕ) : 0 ≤ apMassD x M d := by
  rw [apMassD_eq]
  exact Finset.sum_nonneg (fun p _ => Real.log_natCast_nonneg p)

/-- `apMassD` is monotone in the modulus divisibility: if `d ∣ e` then `d ∣ p+2` is weaker
than `e ∣ p+2`, so the `d`-mass dominates the `e`-mass. -/
theorem apMassD_le_apMassD_of_dvd {x M d e : ℕ} (h : d ∣ e) :
    apMassD x M e ≤ apMassD x M d := by
  rw [apMassD_eq, apMassD_eq]
  refine Finset.sum_le_sum_of_subset_of_nonneg ?_ (fun p _ _ => Real.log_natCast_nonneg p)
  intro p hp
  rw [Finset.mem_filter] at hp ⊢
  exact ⟨hp.1, dvd_trans h hp.2⟩

/-- The `λ⁺` weight sum at `m = 1`: only the empty chain contributes, `lprod [] = 1`. -/
theorem lambdaUp_one (D : ℝ) (M : ℕ) : lambdaUp D M 1 = 1 := by
  unfold lambdaUp
  rw [Finset.sum_eq_single ([] : List ℕ)]
  · simp [lprod]
  · intro c hc hne
    have hnot : ¬ lprod c ∣ 1 := by
      intro h
      rw [lprod] at h
      have hp1 : c.prod = 1 := Nat.dvd_one.mp h
      obtain ⟨q, l, rfl⟩ := List.exists_cons_of_ne_nil hne
      rw [List.prod_cons] at hp1
      have hq : 3 ≤ q :=
        prime_three_le ((chain_primes 1 M D).1 _ hc q List.mem_cons_self).1
          ((chain_primes 1 M D).1 _ hc q List.mem_cons_self).2.1
      have hqdvd : q ∣ 1 := ⟨l.prod, hp1.symm⟩
      have := Nat.le_of_dvd (by norm_num) hqdvd
      omega
    simp [hnot]
  · intro h
    exact absurd (nil_mem_Gp 1 D M) h

/-- `bvSum` is nonnegative. -/
theorem bvSum_nonneg (x K : ℕ) : 0 ≤ bvSum x K := by
  unfold bvSum
  exact Finset.sum_nonneg (fun d _ => abs_nonneg _)

/-- `bvSum` is monotone in the level. -/
theorem bvSum_mono {x K K' : ℕ} (h : K ≤ K') : bvSum x K ≤ bvSum x K' := by
  unfold bvSum
  refine Finset.sum_le_sum_of_subset_of_nonneg ?_ (fun d _ _ => abs_nonneg _)
  intro d hd
  rw [Finset.mem_filter, Finset.mem_Icc] at hd ⊢
  exact ⟨⟨hd.1.1, le_trans hd.1.2 h⟩, hd.2⟩

end

end Work.NumberTheory.Chen.APSwitchUpper
