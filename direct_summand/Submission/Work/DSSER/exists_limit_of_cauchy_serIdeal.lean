import Mathlib
import Submission.Work.DSSER.Basic
import Submission.Work.DSSER.IdealPow
import Submission.Work.DSSER.moduleFinite_serRing
import Submission.Work.DSSER.isAdicComplete_maximalIdeal_serRing
import Submission.Work.DSSER.maximalIdeal_pow_map_le_serIdeal_pow

universe u

namespace Work.DSSER

open IsLocalRing

/-- The "digit-decomposition" comparison `(Z)^(p(n+d)) ≤ 𝔪^n R'` used to relate the `(Z)`-adic
and `𝔪`-adic topologies on `R' = R[Z]/(Z_i^p - z_i)`.

`serIdeal_pow_eq_span` writes `(Z)^(p(n+d))` as the span of the `Z^w` with `|w| = p(n+d)`, so it
suffices for each such `Z^w` to lie in `𝔪^n R'`: write `w i = p * (w i / p) + w i % p`, so
`Z^w = Z^(w mod p) * z^(w / p)` (`serZpow_div_mod`), and `z^(w / p) ∈ 𝔪^n` by `zMono_mem_pow`
since `Σ (w i / p) ≥ n` follows from `|w| = p(n+d)` and `Σ (w i % p) ≤ d (p - 1)`. -/
theorem serIdeal_pow_le_maximalIdeal_pow_map_aux (R : Type u) [CommRing R] [IsLocalRing R]
    (p : ℕ) (hp : 0 < p) {d : ℕ} (z : Fin d → R)
    (hm : Ideal.span (Set.range z) = IsLocalRing.maximalIdeal R) (n : ℕ) :
    Work.DSSER.serIdeal p z ^ (p * (n + d)) ≤
      Ideal.map (algebraMap R (Work.DSSER.serRing R p z)) (IsLocalRing.maximalIdeal R ^ n) := by
  rw [serIdeal_pow_eq_span R p z (p * (n + d))]
  refine Ideal.span_le.mpr ?_
  rintro a ⟨w, hw, rfl⟩
  rw [serZpow_div_mod]
  refine Ideal.mul_mem_left _ _ ?_
  refine Ideal.mem_map_of_mem _ ?_
  apply (Ideal.pow_le_pow_right ?_) (zMono_mem_pow hm (fun i => w i / p))
  -- It remains to bound `n ≤ Σ i, w i / p` from `Σ i, w i = p * (n + d)`.
  have key : ∀ i, p * (w i / p) + w i % p = w i := fun i => Nat.div_add_mod (w i) p
  have hdecomp : p * (∑ i, w i / p) + (∑ i, w i % p) = ∑ i, w i := by
    rw [Finset.mul_sum, ← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun i _ => key i
  have hRn : ∑ i, w i % p ≤ d * (p - 1) := by
    calc ∑ i, w i % p ≤ ∑ _i : Fin d, (p - 1) :=
          Finset.sum_le_sum fun i _ => by have := Nat.mod_lt (w i) hp; omega
      _ = d * (p - 1) := by rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul]
  have h2 : d * (p - 1) ≤ p * d :=
    (Nat.mul_le_mul_left d (Nat.sub_le p 1)).trans_eq (Nat.mul_comm d p)
  have hbnd : p * n + (∑ i, w i % p) ≤ p * (n + d) := by
    calc p * n + (∑ i, w i % p) ≤ p * n + d * (p - 1) := Nat.add_le_add_left hRn (p * n)
      _ ≤ p * n + p * d := Nat.add_le_add_left h2 (p * n)
      _ = p * (n + d) := (Nat.mul_add p n d).symm
  have hfinal : p * n + (∑ i, w i % p) ≤ p * (∑ i, w i / p) + (∑ i, w i % p) := by
    rw [hdecomp, hw]; exact hbnd
  exact Nat.le_of_mul_le_mul_left (Nat.add_le_add_iff_right.mp hfinal) hp

/-- **Convergence in the `(Z)`-adic topology.**  A sequence in `R' = R[Z]/(Z_i^p - z_i)` whose
successive differences lie in `(Z)^m` (for `m ≤ n`) converges in the `(Z)`-adic topology, provided
`R` is complete Noetherian local, `𝔪 = (z)` and `0 < p`.

Route: `(Z)^(p(k+d)) ≤ 𝔪^k R'` (`serIdeal_pow_le_maximalIdeal_pow_map`), so the subsequence
`k ↦ f (p * (k + d))` is `𝔪`-Cauchy and converges by `IsPrecomplete.prec` for
`IsAdicComplete 𝔪 R'` (`isAdicComplete_maximalIdeal_serRing`); finally
`𝔪^n R' ≤ (Z)^n` (`maximalIdeal_pow_map_le_serIdeal_pow`). -/
theorem exists_limit_of_cauchy_serIdeal (R : Type u) [CommRing R] [IsLocalRing R]
    [IsNoetherianRing R] [IsAdicComplete (IsLocalRing.maximalIdeal R) R] (p : ℕ) (hp : 0 < p)
    {d : ℕ} (z : Fin d → R) (hm : Ideal.span (Set.range z) = IsLocalRing.maximalIdeal R)
    (f : ℕ → Work.DSSER.serRing R p z)
    (hf : ∀ m n, m ≤ n → f m - f n ∈ Work.DSSER.serIdeal p z ^ m) :
    ∃ L, ∀ n, f n - L ∈ Work.DSSER.serIdeal p z ^ n := by
  -- `R'` is `𝔪`-adically complete.
  have hcomp : IsAdicComplete (maximalIdeal R) (serRing R p z) :=
    isAdicComplete_maximalIdeal_serRing R p hp z
  -- The `p`-step subsequence `k ↦ f (p (k + d))` is `𝔪`-Cauchy: `(Z)^(p(k+d)) ≤ 𝔪^k R'`.
  let g : ℕ → serRing R p z := fun k => f (p * (k + d))
  have hgmem : ∀ {m n : ℕ}, m ≤ n →
      g m - g n ∈ (maximalIdeal R ^ m • ⊤ : Submodule R (serRing R p z)) := by
    intro m n hmn
    have hle : p * (m + d) ≤ p * (n + d) := Nat.mul_le_mul_left p (Nat.add_le_add_right hmn d)
    have h1 : g m - g n ∈ serIdeal p z ^ (p * (m + d)) := hf _ _ hle
    have h2 := serIdeal_pow_le_maximalIdeal_pow_map_aux R p hp z hm m
    rw [Ideal.smul_top_eq_map]
    exact h2 h1
  have hg : ∀ {m n : ℕ}, m ≤ n →
      g m ≡ g n [SMOD (maximalIdeal R ^ m • ⊤ : Submodule R (serRing R p z))] :=
    fun {m n} hmn => SModEq.sub_mem.mpr (hgmem hmn)
  -- Precompleteness produces a limit `L` of the subsequence in the `𝔪`-adic topology.
  obtain ⟨L, hL⟩ := IsPrecomplete.prec (I := maximalIdeal R) (M := serRing R p z)
    hcomp.toIsPrecomplete hg
  refine ⟨L, fun n => ?_⟩
  -- `f n - L = (f n - f (p (n+d))) + (f (p (n+d)) - L)`, both terms in `(Z)^n`.
  have hsplit : f n - L = (f n - f (p * (n + d))) + (f (p * (n + d)) - L) := by abel
  rw [hsplit]
  refine (serIdeal p z ^ n).add_mem ?_ ?_
  · exact hf n (p * (n + d))
      (le_trans (Nat.le_add_right n d) (Nat.le_mul_of_pos_left (n + d) hp))
  · have hmem : f (p * (n + d)) - L ∈ (maximalIdeal R ^ n • ⊤ : Submodule R (serRing R p z)) :=
      SModEq.sub_mem.mp (hL n)
    rw [Ideal.smul_top_eq_map] at hmem
    exact maximalIdeal_pow_map_le_serIdeal_pow R p hp z hm n hmem

end Work.DSSER
