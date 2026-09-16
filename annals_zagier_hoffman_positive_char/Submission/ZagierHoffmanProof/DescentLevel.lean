import Submission.ZagierHoffmanProof.DescentIndependent

/-!
# The sparsification of the second relation at an ARBITRARY weight level

`AbpDescent.descent_sparse` sparsifies the twisted second relation `∑_t B_t·(𝓛(t)·ω^{w₀-w(t)})^{(1)} = 0`
at the TOP weight `w₀`.  Dac §5.2 iterates the argument over the weights: after the top weight has
been killed one divides the relation by `ω^{w-w₁}` and specialises again.  This file provides the
weight-`w'` version of the sparsification (the sum being over the tuples of weight `≤ w'`, the
exponent being `w' - tmWeight t`), which is what the iteration needs.
-/

set_option autoImplicit false
set_option maxHeartbeats 1000000
open Polynomial Matrix Finset
open scoped WithZero Topology Classical

namespace ZagierHoffmanPositiveChar

variable {F : Type*} [Field F] [Finite F]

section SparseLevel

variable {γ : ℚᵐ⁰} {ω : PowerSeries (Ambient F)}
variable {S : Finset (List (ℕ × Polynomial (Ambient F)))}

/-- **Sparsification at the weight level `w'`.**  If
`∑_{tmWeight t ≤ w'} B_t·(𝓛(t)·ω^{w'-tmWeight t})^{(1)} = 0` as a power series, then at every point
`θ^{q^N}` (`N ≥ 1`) only the tuples of weight exactly `w'` survive, because `ω^{(1)}` has a zero at
each `θ^{q^k}`. -/
theorem descent_sparse_level (hγ0 : 0 < γ) (hγ : γ < 1) (harch : GammaArchimedean ℚᵐ⁰)
    (hq : 2 ≤ Nat.card F) (hωse : GSuperEntire γ ω)
    (hΩ1 : ∀ j : ℕ, 2 ≤ j → evalSeriesGen (frobTwist (R := Ambient F) (p := Nat.card F) 1 ω)
      ((ambTheta F) ^ (Nat.card F) ^ j) = 0)
    (hLse : ∀ t : ↥(tmI S), GSuperEntire γ (tmL (Nat.card F) ω t.1))
    (hMZ : ∀ (t : ↥(tmI S)) (k : ℕ),
      evalSeriesGen (tmL (Nat.card F) ω t.1) ((ambTheta F) ^ (Nat.card F ^ k))
        = (evalSeriesGen (tmL (Nat.card F) ω t.1) (ambTheta F)) ^ (Nat.card F ^ k))
    {w' : ℕ} {B : ↥(tmI S) → Polynomial (Ambient F)}
    (hrel : (∑ t ∈ Finset.univ.filter (fun t : ↥(tmI S) => tmWeight t.1 ≤ w'),
      coeHom (K := Ambient F) (B t)
        * (frobTwist (R := Ambient F) (p := Nat.card F) 1 (tmL (Nat.card F) ω t.1)
          * (frobTwist (R := Ambient F) (p := Nat.card F) 1 ω) ^ (w' - tmWeight t.1))) = 0) :
    ∀ N : ℕ, 2 ≤ N → (∑ t ∈ Finset.univ.filter (fun t : ↥(tmI S) => tmWeight t.1 = w'),
      (B t).eval ((ambTheta F) ^ (Nat.card F) ^ N)
        * (evalSeriesGen (tmL (Nat.card F) ω t.1) (ambTheta F)) ^ (Nat.card F ^ N)) = 0 := by
  classical
  have hΩse : GSuperEntire γ (frobTwist (R := Ambient F) (p := Nat.card F) 1 ω) :=
    hωse.frobTwist hγ.le 1
  have hle : ∀ t ∈ Finset.univ.filter (fun t : ↥(tmI S) => tmWeight t.1 ≤ w'),
      tmWeight t.1 ≤ w' := fun t ht => (Finset.mem_filter.mp ht).2
  intro N hN
  -- (1) evaluate the relation at `θ ^ q ^ N`
  have hsuper : ∀ t ∈ Finset.univ.filter (fun t : ↥(tmI S) => tmWeight t.1 ≤ w'),
      GSuperEntire γ (coeHom (K := Ambient F) (B t)
        * (frobTwist (R := Ambient F) (p := Nat.card F) 1 (tmL (Nat.card F) ω t.1)
          * (frobTwist (R := Ambient F) (p := Nat.card F) 1 ω) ^ (w' - tmWeight t.1))) := by
    intro t _
    have h1 : GSuperEntire γ (coeHom (K := Ambient F) (B t)) :=
      GSuperEntire.polynomial hγ0 hγ.le (B t)
    have h2 : GSuperEntire γ
        (frobTwist (R := Ambient F) (p := Nat.card F) 1 (tmL (Nat.card F) ω t.1)) :=
      (hLse t).frobTwist hγ.le 1
    have h3 : GSuperEntire γ
        ((frobTwist (R := Ambient F) (p := Nat.card F) 1 ω) ^ (w' - tmWeight t.1)) :=
      hΩse.pow hγ.le _
    have h23 : GSuperEntire γ
        (frobTwist (R := Ambient F) (p := Nat.card F) 1 (tmL (Nat.card F) ω t.1)
          * (frobTwist (R := Ambient F) (p := Nat.card F) 1 ω) ^ (w' - tmWeight t.1)) :=
      GSuperEntire.mul (f := frobTwist (R := Ambient F) (p := Nat.card F) 1
          (tmL (Nat.card F) ω t.1))
        (g := (frobTwist (R := Ambient F) (p := Nat.card F) 1 ω) ^ (w' - tmWeight t.1))
        hγ.le h2 h3
    exact GSuperEntire.mul (f := coeHom (K := Ambient F) (B t))
      (g := frobTwist (R := Ambient F) (p := Nat.card F) 1 (tmL (Nat.card F) ω t.1)
        * (frobTwist (R := Ambient F) (p := Nat.card F) 1 ω) ^ (w' - tmWeight t.1))
      hγ.le h1 h23
  have h0 : evalSeriesGen (K := Ambient F) (Γ₀ := ℚᵐ⁰)
      (∑ t ∈ Finset.univ.filter (fun t : ↥(tmI S) => tmWeight t.1 ≤ w'),
        coeHom (K := Ambient F) (B t)
        * (frobTwist (R := Ambient F) (p := Nat.card F) 1 (tmL (Nat.card F) ω t.1)
          * (frobTwist (R := Ambient F) (p := Nat.card F) 1 ω) ^ (w' - tmWeight t.1)))
      ((ambTheta F) ^ (Nat.card F) ^ N) = 0 := by
    rw [hrel, evalSeriesGen_zero_amb]
  rw [evalSeriesGen_finset_sum (K := Ambient F) (Γ₀ := ℚᵐ⁰) hγ harch _ _ hsuper] at h0
  -- (2) compute each term
  have hcompute : ∀ t : ↥(tmI S),
      evalSeriesGen (coeHom (K := Ambient F) (B t)
        * (frobTwist (R := Ambient F) (p := Nat.card F) 1 (tmL (Nat.card F) ω t.1)
          * (frobTwist (R := Ambient F) (p := Nat.card F) 1 ω) ^ (w' - tmWeight t.1)))
        ((ambTheta F) ^ (Nat.card F) ^ N)
      = (B t).eval ((ambTheta F) ^ (Nat.card F) ^ N)
        * (evalSeriesGen (tmL (Nat.card F) ω t.1) (ambTheta F)) ^ (Nat.card F ^ N)
        * (evalSeriesGen (frobTwist (R := Ambient F) (p := Nat.card F) 1 ω)
            ((ambTheta F) ^ (Nat.card F) ^ N)) ^ (w' - tmWeight t.1) := by
    intro t
    have htw : evalSeriesGen (frobTwist (R := Ambient F) (p := Nat.card F) 1
        (tmL (Nat.card F) ω t.1)) ((ambTheta F) ^ (Nat.card F) ^ N)
        = (evalSeriesGen (tmL (Nat.card F) ω t.1) (ambTheta F)) ^ (Nat.card F ^ N) := by
      have hqN : (Nat.card F) ^ (N - 1) * Nat.card F = (Nat.card F) ^ N := by
        conv_rhs => rw [← Nat.sub_add_cancel (show 1 ≤ N by omega)]
        rw [pow_succ]
      have hp : ((ambTheta F) ^ (Nat.card F ^ (N - 1))) ^ (Nat.card F)
          = (ambTheta F) ^ (Nat.card F) ^ N := by
        rw [← pow_mul, hqN]
      have h := evalSeriesGen_frobTwist hγ harch (Nat.card F) (hLse t)
        ((ambTheta F) ^ (Nat.card F ^ (N - 1))) 1
      rw [pow_one] at h
      rw [hp, hMZ t (N - 1), ← pow_mul, hqN] at h
      exact h
    rw [show coeHom (K := Ambient F) (B t)
        * (frobTwist (R := Ambient F) (p := Nat.card F) 1 (tmL (Nat.card F) ω t.1)
          * (frobTwist (R := Ambient F) (p := Nat.card F) 1 ω) ^ (w' - tmWeight t.1))
        = coeHom (K := Ambient F) (B t)
            * frobTwist (R := Ambient F) (p := Nat.card F) 1 (tmL (Nat.card F) ω t.1)
          * (frobTwist (R := Ambient F) (p := Nat.card F) 1 ω) ^ (w' - tmWeight t.1) by ring]
    simp only [coeHom_apply]
    rw [evalSeriesGen_mul hγ harch
        (GSuperEntire.mul hγ.le
          (GSuperEntire.polynomial hγ0 hγ.le (B t)) ((hLse t).frobTwist hγ.le 1))
        (hΩse.pow hγ.le _) _,
      evalSeriesGen_mul hγ harch
        (GSuperEntire.polynomial hγ0 hγ.le (B t)) ((hLse t).frobTwist hγ.le 1) _,
      evalSeriesGen_polynomial, htw, evalSeriesGen_pow hγ harch hΩse _ _]
  rw [Finset.sum_congr rfl (fun t _ => hcompute t)] at h0
  -- (3) only the entries of weight `w'` survive
  have hzero : ∀ t ∈ Finset.univ.filter (fun t : ↥(tmI S) => tmWeight t.1 ≤ w'),
      t ∉ Finset.univ.filter (fun t : ↥(tmI S) => tmWeight t.1 = w') →
      ((B t).eval ((ambTheta F) ^ (Nat.card F) ^ N)
        * (evalSeriesGen (tmL (Nat.card F) ω t.1) (ambTheta F)) ^ (Nat.card F ^ N)
        * (evalSeriesGen (frobTwist (R := Ambient F) (p := Nat.card F) 1 ω)
            ((ambTheta F) ^ (Nat.card F) ^ N)) ^ (w' - tmWeight t.1)) = 0 := by
    intro t ht ht'
    have hne : tmWeight t.1 ≠ w' := fun h => ht' (Finset.mem_filter.mpr ⟨Finset.mem_univ t, h⟩)
    have hlt : tmWeight t.1 < w' := lt_of_le_of_ne (hle t ht) hne
    rw [hΩ1 N hN, zero_pow (by omega : w' - tmWeight t.1 ≠ 0), mul_zero]
  have hpt : ∀ t ∈ Finset.univ.filter (fun t : ↥(tmI S) => tmWeight t.1 = w'),
      (B t).eval ((ambTheta F) ^ (Nat.card F) ^ N)
        * (evalSeriesGen (tmL (Nat.card F) ω t.1) (ambTheta F)) ^ (Nat.card F ^ N)
      = (B t).eval ((ambTheta F) ^ (Nat.card F) ^ N)
        * (evalSeriesGen (tmL (Nat.card F) ω t.1) (ambTheta F)) ^ (Nat.card F ^ N)
        * (evalSeriesGen (frobTwist (R := Ambient F) (p := Nat.card F) 1 ω)
            ((ambTheta F) ^ (Nat.card F) ^ N)) ^ (w' - tmWeight t.1) := by
    intro t ht
    have hwt : tmWeight t.1 = w' := (Finset.mem_filter.mp ht).2
    rw [hwt, Nat.sub_self, pow_zero, mul_one]
  rw [show (∑ t ∈ Finset.univ.filter (fun t : ↥(tmI S) => tmWeight t.1 = w'),
        (B t).eval ((ambTheta F) ^ (Nat.card F) ^ N)
          * (evalSeriesGen (tmL (Nat.card F) ω t.1) (ambTheta F)) ^ (Nat.card F ^ N))
      = ∑ t ∈ Finset.univ.filter (fun t : ↥(tmI S) => tmWeight t.1 = w'),
        ((B t).eval ((ambTheta F) ^ (Nat.card F) ^ N)
          * (evalSeriesGen (tmL (Nat.card F) ω t.1) (ambTheta F)) ^ (Nat.card F ^ N)
          * (evalSeriesGen (frobTwist (R := Ambient F) (p := Nat.card F) 1 ω)
              ((ambTheta F) ^ (Nat.card F) ^ N)) ^ (w' - tmWeight t.1))
      from Finset.sum_congr rfl hpt]
  rw [Finset.sum_subset
    (s₁ := Finset.univ.filter (fun t : ↥(tmI S) => tmWeight t.1 = w'))
    (s₂ := Finset.univ.filter (fun t : ↥(tmI S) => tmWeight t.1 ≤ w'))
    (by intro x hx
        rw [Finset.mem_filter] at hx ⊢
        exact ⟨hx.1, le_of_eq hx.2⟩)
    hzero]
  exact h0

end SparseLevel

section Divide

/-- **Dividing the second relation by `ω^{w-w'}`.**  If all the coefficients `B_t` of weight `> w'`
vanish, the twisted second relation (with the exponent `w - tmWeight t`, all `tmWeight t ≤ w`) can
be reduced to the level-`w'` relation (exponent `w' - tmWeight t`, sum over `tmWeight ≤ w'`). -/
theorem descent_relation_level {ω : PowerSeries (Ambient F)}
    {S : Finset (List (ℕ × Polynomial (Ambient F)))} {w w' : ℕ} (hw' : w' ≤ w)
    (hΩne : frobTwist (R := Ambient F) (p := Nat.card F) 1 ω ≠ 0)
    {B : ↥(tmI S) → Polynomial (Ambient F)}
    (hBzero : ∀ t : ↥(tmI S), w' < tmWeight t.1 → B t = 0)
    (hrel : (∑ t ∈ (Finset.univ : Finset ↥(tmI S)), coeHom (K := Ambient F) (B t)
      * (frobTwist (R := Ambient F) (p := Nat.card F) 1 (tmL (Nat.card F) ω t.1)
        * (frobTwist (R := Ambient F) (p := Nat.card F) 1 ω) ^ (w - tmWeight t.1))) = 0) :
    (∑ t ∈ Finset.univ.filter (fun t : ↥(tmI S) => tmWeight t.1 ≤ w'),
      coeHom (K := Ambient F) (B t)
        * (frobTwist (R := Ambient F) (p := Nat.card F) 1 (tmL (Nat.card F) ω t.1)
          * (frobTwist (R := Ambient F) (p := Nat.card F) 1 ω) ^ (w' - tmWeight t.1))) = 0 := by
  classical
  have hterm : ∀ t ∈ Finset.univ.filter (fun t : ↥(tmI S) => tmWeight t.1 ≤ w'),
      coeHom (K := Ambient F) (B t)
        * (frobTwist (R := Ambient F) (p := Nat.card F) 1 (tmL (Nat.card F) ω t.1)
          * (frobTwist (R := Ambient F) (p := Nat.card F) 1 ω) ^ (w - tmWeight t.1))
      = (coeHom (K := Ambient F) (B t)
          * (frobTwist (R := Ambient F) (p := Nat.card F) 1 (tmL (Nat.card F) ω t.1)
            * (frobTwist (R := Ambient F) (p := Nat.card F) 1 ω) ^ (w' - tmWeight t.1)))
        * (frobTwist (R := Ambient F) (p := Nat.card F) 1 ω) ^ (w - w') := by
    intro t ht
    have hle : tmWeight t.1 ≤ w' := (Finset.mem_filter.mp ht).2
    have hexp : w' - tmWeight t.1 + (w - w') = w - tmWeight t.1 := by omega
    rw [← hexp, pow_add]
    ring
  have h1 : (∑ t ∈ Finset.univ.filter (fun t : ↥(tmI S) => tmWeight t.1 ≤ w'),
        coeHom (K := Ambient F) (B t)
          * (frobTwist (R := Ambient F) (p := Nat.card F) 1 (tmL (Nat.card F) ω t.1)
            * (frobTwist (R := Ambient F) (p := Nat.card F) 1 ω) ^ (w - tmWeight t.1)))
      = (∑ t ∈ Finset.univ.filter (fun t : ↥(tmI S) => tmWeight t.1 ≤ w'),
          coeHom (K := Ambient F) (B t)
            * (frobTwist (R := Ambient F) (p := Nat.card F) 1 (tmL (Nat.card F) ω t.1)
              * (frobTwist (R := Ambient F) (p := Nat.card F) 1 ω) ^ (w' - tmWeight t.1)))
        * (frobTwist (R := Ambient F) (p := Nat.card F) 1 ω) ^ (w - w') := by
    rw [Finset.sum_mul]
    exact Finset.sum_congr rfl hterm
  have h2 : (∑ t ∈ Finset.univ.filter (fun t : ↥(tmI S) => tmWeight t.1 ≤ w'),
        coeHom (K := Ambient F) (B t)
          * (frobTwist (R := Ambient F) (p := Nat.card F) 1 (tmL (Nat.card F) ω t.1)
            * (frobTwist (R := Ambient F) (p := Nat.card F) 1 ω) ^ (w - tmWeight t.1)))
      = ∑ t ∈ (Finset.univ : Finset ↥(tmI S)), coeHom (K := Ambient F) (B t)
          * (frobTwist (R := Ambient F) (p := Nat.card F) 1 (tmL (Nat.card F) ω t.1)
            * (frobTwist (R := Ambient F) (p := Nat.card F) 1 ω) ^ (w - tmWeight t.1)) := by
    refine Finset.sum_subset
      (s₁ := Finset.univ.filter (fun t : ↥(tmI S) => tmWeight t.1 ≤ w'))
      (s₂ := (Finset.univ : Finset ↥(tmI S))) ?_ ?_
    · intro x _; exact Finset.mem_univ x
    · intro x _ hx
      have hgt : w' < tmWeight x.1 := by
        by_contra h
        exact hx (Finset.mem_filter.mpr ⟨Finset.mem_univ x, not_lt.mp h⟩)
      rw [hBzero x hgt, map_zero, zero_mul]
  have h3 : (∑ t ∈ Finset.univ.filter (fun t : ↥(tmI S) => tmWeight t.1 ≤ w'),
        coeHom (K := Ambient F) (B t)
          * (frobTwist (R := Ambient F) (p := Nat.card F) 1 (tmL (Nat.card F) ω t.1)
            * (frobTwist (R := Ambient F) (p := Nat.card F) 1 ω) ^ (w' - tmWeight t.1)))
      * (frobTwist (R := Ambient F) (p := Nat.card F) 1 ω) ^ (w - w') = 0 := by
    rw [← h1, h2]
    exact hrel
  rcases mul_eq_zero.mp h3 with h | h
  · exact h
  · exact absurd h (pow_ne_zero _ hΩne)

end Divide

section Iterate

/-- **Dac §5.2, Step 2, complete.**  From the twisted second relation at the top weight `w`, the
`K`-independence of every weight level (condition (LW)) and the height bound `tmWeight ≤ w`, all the
coefficients `B_t` vanish (the iteration over the weights of the paper). -/
theorem descent_B_zero_all {γ : ℚᵐ⁰} {ω : PowerSeries (Ambient F)}
    (hγ0 : 0 < γ) (hγ : γ < 1) (harch : GammaArchimedean ℚᵐ⁰) (hq : 2 ≤ Nat.card F)
    (hω : GIsSmall γ ω) (hωse : GSuperEntire γ ω)
    (hc : ∀ k : ℕ, 1 ≤ k → evalSeriesGen ω ((ambTheta F) ^ (Nat.card F ^ k)) = 0)
    (hωfe : (PowerSeries.X - PowerSeries.C ((ambTheta F) ^ Nat.card F))
      * frobTwist (R := Ambient F) (p := Nat.card F) 1 ω = ω)
    (hΩ1 : ∀ j : ℕ, 2 ≤ j → evalSeriesGen (frobTwist (R := Ambient F) (p := Nat.card F) 1 ω)
      ((ambTheta F) ^ (Nat.card F) ^ j) = 0)
    (hΩne : frobTwist (R := Ambient F) (p := Nat.card F) 1 ω ≠ 0)
    {S : Finset (List (ℕ × Polynomial (Ambient F)))} {w : ℕ}
    (hsm : ∀ s ∈ S, ∀ y ∈ s, GIsSmall γ (ω ^ y.1 * (y.2 : PowerSeries (Ambient F))))
    (hSse : ∀ s ∈ S, ∀ y ∈ s, GSuperEntire γ ((y.2 : PowerSeries (Ambient F))))
    (hpos : ∀ s ∈ S, ∀ y ∈ s, 1 ≤ y.1)
    (hQmem : ∀ s ∈ S, ∀ y ∈ s, ∀ k, (y.2).coeff k ∈ ambA F 0)
    (hLW : ∀ w' : ℕ, w' ≤ w → LinearIndependent (ambK F)
      (fun t : {t : ↥(tmI S) // tmWeight t.1 = w'} => tmZ (F := F) ω t.1.1))
    (hwle : ∀ t : ↥(tmI S), tmWeight t.1 ≤ w)
    {B : ↥(tmI S) → Polynomial (Ambient F)}
    (hBmem : ∀ t k, (B t).coeff k ∈ ambKperf F)
    (hrel : (∑ t ∈ (Finset.univ : Finset ↥(tmI S)), coeHom (K := Ambient F) (B t)
      * (frobTwist (R := Ambient F) (p := Nat.card F) 1 (tmL (Nat.card F) ω t.1)
        * (frobTwist (R := Ambient F) (p := Nat.card F) 1 ω) ^ (w - tmWeight t.1))) = 0) :
    ∀ t : ↥(tmI S), B t = 0 := by
  classical
  have hLse : ∀ t : ↥(tmI S), GSuperEntire γ (tmL (Nat.card F) ω t.1) :=
    fun t => gSuperEntire_tmL (F := F) hγ harch hq hω hωse hsm hSse t
  have hMZ : ∀ (t : ↥(tmI S)) (k : ℕ),
      evalSeriesGen (tmL (Nat.card F) ω t.1) ((ambTheta F) ^ (Nat.card F ^ k))
        = (evalSeriesGen (tmL (Nat.card F) ω t.1) (ambTheta F)) ^ (Nat.card F ^ k) :=
    fun t k => tmL_frobenius_pow (F := F) (S := S) hγ0 hγ harch hq hω hωse hsm hSse hpos
      (fun k hk => hc k hk) t k
  -- one step of the iteration: given all higher levels killed, kill the level `w'`
  have step : ∀ w' : ℕ, w' ≤ w → (∀ u : ↥(tmI S), w' < tmWeight u.1 → B u = 0) →
      ∀ t : ↥(tmI S), tmWeight t.1 = w' → B t = 0 := by
    intro w' hw' hBzero t ht
    have hrel' := descent_relation_level (F := F) (S := S) (ω := ω) hw' hΩne hBzero hrel
    have hev := descent_sparse_level (F := F) (S := S) (ω := ω) hγ0 hγ harch hq hωse hΩ1
      hLse hMZ hrel'
    exact descent_B_zero (F := F) hγ0 hγ harch hq hω hωse hc hωfe hsm hSse hpos hQmem
      (hLW w' hw') hBmem (fun j hj => hev j (by omega)) t ht
  -- iterate downwards from the top weight
  have hkey : ∀ k : ℕ, ∀ t : ↥(tmI S), tmWeight t.1 = w - k → B t = 0 := by
    intro k
    induction k using Nat.strong_induction_on with
    | h k ih =>
      intro t ht
      refine step (w - k) (by omega) (fun u hu => ?_) t ht
      have huw : tmWeight u.1 ≤ w := hwle u
      have hlt : w - tmWeight u.1 < k := by omega
      exact ih (w - tmWeight u.1) hlt u (by omega)
  intro t
  exact hkey (w - tmWeight t.1) t (by have := hwle t; omega)

end Iterate

end ZagierHoffmanPositiveChar
