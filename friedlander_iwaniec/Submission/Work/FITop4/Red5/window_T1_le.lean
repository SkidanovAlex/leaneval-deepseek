/-
# `Submission.Work.FITop4.Red5.window_T1_le` — the `T1` window of the (5.17) Cauchy step

The `T1` term of the §§4–5.2 reduction is the sum of the cell sums over the outer dyadic window
`wSph m`, `Mn < m ≤ 2Mn`:

  `T1 = Σ_{m ∈ (Mn, 2Mn]} Σ_{i,k} Σ_{w : |w|² = m} ‖Σ_{z ∈ primAnn 2N} β^(i,k)_z Z(Re wz)‖`.

The reindexing `Σ_{m∈(M,2M]} Σ_{w:|w|²=m} = Σ_{w ∈ annM}` (`fiber_sum_annM`) turns it into a sum
over the annulus `annM`, on which

* the support of `β^(i,k) = pieceCoeff (Pa i k) (φ k) (q k) (p i)` lies in the *same* set as the
  inner summation range of `boxN` — namely in `primAnn (2N) ∩ boxN (Pa i k)`: the support condition
  `pcCond` puts `z` in the polar box `Pa.N < |z|² ≤ (1+θ)·Pa.N`, while the radial mollifier's
  support clause `p u ≠ 0 → u ≤ 2N` puts it below `2N`, so the two inner sums coincide;
* Cauchy–Schwarz over the finitely many `w ∈ annM` (`sum_norm_inner_le`, the (5.17) step), using
  `f ≥ 1` on the annulus and `card (annM Pa) ≤ 100·M`, bounds the sum of norms by
  `sqrt (100 M · Dform)`.

Summing the per-`(i,k)` inequality gives the statement.
-/
import Mathlib
import Submission.Work.FITop4.Red5.assembly_helpers
import Submission.Work.FITop4.Red5.piecesSetup
import Submission.Work.FITop4.Red5.pieceDefs
import Submission.Work.FITop4.Red4.sum_norm_inner_le

set_option autoImplicit false

namespace Work.FITop4.Red5

open Finset
open scoped BigOperators

attribute [local instance] Classical.propDecidable

noncomputable section

/-! ## 1. Membership of the primary annulus -/

/-- Membership in `primAnn R`, unfolded. -/
lemma mem_primAnn_iff' {R : ℕ} {z : GaussianInt} :
    z ∈ primAnn R ↔ z ∈ Work.FIPlan.gBox ((R : ℕ) : ℤ) ∧ 1 ≤ Work.FIPlan.gnorm z
      ∧ Work.FIPlan.gnorm z ≤ R ∧ Work.FIPlan.IsPrimary z := by
  simp only [primAnn, Finset.mem_filter]
  tauto

/-! ## 2. The support of a cell coefficient

The two facts that make the inner sums over `primAnn (2N)` and over `boxN Pa` coincide: a
non-vanishing cell coefficient forces (i) `(N) < |z|² ≤ 2N` and primitivity, i.e. membership in
`primAnn (2N)` (the `≤ 2N` coming from the radial mollifier support `hsup`), and (ii) membership in
the *box* `boxN Pa` (whose radius `radN Pa = ⌈√(4 Pa.N)⌉` dominates `2N ≤ 2 Pa.N`). -/

lemma pieceCoeff_ne_zero_supp {Pa : Work.FITop.Params} {N : ℕ} {φ : ℝ} {q p : ℝ → ℝ}
    (hN : 1 ≤ N) (ha : (N : ℝ) ≤ Pa.N)
    (hsup : ∀ u : ℝ, p u ≠ 0 → u ≤ 2 * (N : ℝ)) :
    ∀ z : GaussianInt, pieceCoeff Pa φ q p z ≠ 0 →
      z ∈ primAnn (2 * N) ∧ z ∈ Work.FITop.boxN Pa := by
  intro z hz
  -- the polar box / small primes / truncation condition holds
  have hcond : InPolarBox Pa φ z ∧ NoSmallPrimes Pa z ∧
      (((Work.FIPlan.gnorm z).divisors.card : ℕ) : ℝ) ≤ Pa.τ := by
    by_contra hc
    exact hz (by rw [pieceCoeff, if_neg hc])
  have hbox := hcond.1
  -- and the radial mollifier does not vanish at `|z|²`
  have hp : p ((Work.FIPlan.gnorm z : ℕ) : ℝ) ≠ 0 := by
    intro hp0
    refine hz ?_
    rw [pieceCoeff, if_pos hcond, hp0]
    simp
  have hsupz : (Work.FIPlan.gnorm z : ℝ) ≤ 2 * (N : ℝ) := hsup _ hp
  have hleN : Work.FIPlan.gnorm z ≤ 2 * N := by
    exact_mod_cast hsupz
  have hle2 : (Work.FIPlan.gnorm z : ℝ) ≤ 2 * Pa.N := by linarith [hsupz, ha]
  have hgnorm_nonneg : (0 : ℝ) ≤ Pa.N := le_trans (by positivity) ha
  -- (i) membership in `primAnn (2N)`
  have h1 : 1 ≤ Work.FIPlan.gnorm z := by
    have hNr : (1 : ℝ) ≤ (N : ℝ) := by exact_mod_cast hN
    have hlt : (N : ℝ) < (Work.FIPlan.gnorm z : ℝ) := lt_of_le_of_lt ha hbox.2.1
    have : (1 : ℝ) ≤ (Work.FIPlan.gnorm z : ℝ) := by linarith
    exact_mod_cast this
  have hgb : z ∈ Work.FIPlan.gBox ((2 * N : ℕ) : ℤ) :=
    mem_gBox_of_norm_sq (w := z) (m := Work.FIPlan.gnorm z) (R := 2 * N) rfl (by
      calc Work.FIPlan.gnorm z ≤ 2 * N := hleN
        _ ≤ (2 * N) ^ 2 := by
            have h1' : 1 ≤ 2 * N := by omega
            have h := Nat.mul_le_mul_left (2 * N) h1'
            simpa [pow_two, mul_one] using h)
  have hmem1 : z ∈ primAnn (2 * N) := by
    rw [mem_primAnn_iff']
    exact ⟨hgb, h1, hleN, hbox.1⟩
  -- (ii) membership in the inner box `boxN Pa`
  have hmem2 : z ∈ Work.FITop.boxN Pa := by
    rw [Work.FITop.boxN, Work.FITop.radN]
    refine mem_gBox_of_norm_sq (w := z) (m := Work.FIPlan.gnorm z)
      (R := ⌈Real.sqrt (4 * Pa.N)⌉₊) rfl ?_
    have hceil : Real.sqrt (4 * Pa.N) ≤ (((⌈Real.sqrt (4 * Pa.N)⌉₊ : ℕ)) : ℝ) :=
      Nat.le_ceil _
    have hsq : 4 * Pa.N ≤ (((⌈Real.sqrt (4 * Pa.N)⌉₊ : ℕ)) : ℝ) ^ 2 := by
      calc 4 * Pa.N = (Real.sqrt (4 * Pa.N)) ^ 2 :=
            (Real.sq_sqrt (by linarith)).symm
        _ ≤ _ := pow_le_pow_left₀ (Real.sqrt_nonneg _) hceil 2
    have h := le_trans hle2 (by linarith : 2 * Pa.N ≤ 4 * Pa.N)
    have h' : (Work.FIPlan.gnorm z : ℝ) ≤ (((⌈Real.sqrt (4 * Pa.N)⌉₊ : ℕ)) : ℝ) ^ 2 :=
      le_trans h hsq
    exact_mod_cast h'
  exact ⟨hmem1, hmem2⟩

/-- **The inner `z`-sums over `primAnn (2N)` and over `boxN Pa` coincide**: both are the sum over
the support of the cell coefficient (which lies in their intersection), and the coefficient
vanishes off either set. -/
lemma sum_primAnn_eq_sum_boxN {Pa : Work.FITop.Params} {N : ℕ} {φ : ℝ} {q p : ℝ → ℝ}
    (hN : 1 ≤ N) (ha : (N : ℝ) ≤ Pa.N)
    (hsup : ∀ u : ℝ, p u ≠ 0 → u ≤ 2 * (N : ℝ)) (w : GaussianInt) :
    (∑ z ∈ primAnn (2 * N), pieceCoeff Pa φ q p z * Work.FITop3.Zc w z)
      = ∑ z ∈ Work.FITop.boxN Pa, pieceCoeff Pa φ q p z * Work.FITop3.Zc w z := by
  set f : GaussianInt → ℂ := fun z => pieceCoeff Pa φ q p z * Work.FITop3.Zc w z with hf
  have hsupp' : ∀ z : GaussianInt, pieceCoeff Pa φ q p z ≠ 0 →
      z ∈ primAnn (2 * N) ∧ z ∈ Work.FITop.boxN Pa :=
    pieceCoeff_ne_zero_supp (Pa := Pa) (N := N) (φ := φ) (q := q) (p := p) hN ha hsup
  have hb0 : ∀ z : GaussianInt, f z ≠ 0 → pieceCoeff Pa φ q p z ≠ 0 := fun z hz hb =>
    hz (by show pieceCoeff Pa φ q p z * Work.FITop3.Zc w z = 0; rw [hb, zero_mul])
  have h1 : ∀ z, f z ≠ 0 → z ∈ primAnn (2 * N) := fun z hz => (hsupp' z (hb0 z hz)).1
  have h2 : ∀ z, f z ≠ 0 → z ∈ Work.FITop.boxN Pa := fun z hz => (hsupp' z (hb0 z hz)).2
  have hA : (∑ z ∈ primAnn (2 * N) ∩ Work.FITop.boxN Pa, f z) = ∑ z ∈ primAnn (2 * N), f z :=
    Finset.sum_subset Finset.inter_subset_left (fun z hz1 hznot => by
      by_contra hne
      exact hznot (Finset.mem_inter.mpr ⟨hz1, h2 z hne⟩))
  have hB : (∑ z ∈ primAnn (2 * N) ∩ Work.FITop.boxN Pa, f z) = ∑ z ∈ Work.FITop.boxN Pa, f z :=
    Finset.sum_subset Finset.inter_subset_right (fun z hz2 hznot => by
      by_contra hne
      exact hznot (Finset.mem_inter.mpr ⟨h1 z hne, hz2⟩))
  exact hA.symm.trans hB

/-! ## 3. The window bound -/

theorem window_T1_le (x N Pz Mn : ℕ) (C τ θ : ℝ) (K K' : ℕ)
    (a : Fin K → ℝ) (p : Fin K → ℝ → ℝ) (φ : Fin K' → ℝ) (q : Fin K' → ℝ → ℝ)
    (Pa : Fin K → Fin K' → Work.FITop.Params) (f : Fin K → Fin K' → ℤ → ℝ)
    (hN : 1 ≤ N) (hMn : 1 ≤ Mn)
    (hPaM : ∀ i k, (Pa i k).M = (Mn : ℝ)) (hPaN : ∀ i k, (Pa i k).N = a i)
    (ha : ∀ i, (N : ℝ) ≤ a i)
    (hsup : ∀ i u, p i u ≠ 0 → u ≤ 2 * (N : ℝ))
    (hMaj : ∀ i k, IsMajorant (Pa i k) (f i k)) :
    (∑ m ∈ Finset.Icc (Mn + 1) (2 * Mn),
        ∑ i, ∑ k, ∑ w ∈ wSph m,
          ‖∑ z ∈ primAnn (2 * N),
             pieceCoeff (Pa i k) (φ k) (q k) (p i) z * Work.FITop3.Zc w z‖)
      ≤ ∑ i, ∑ k, Real.sqrt (100 * (Pa i k).M
          * Dform (Pa i k) (f i k) (pieceCoeff (Pa i k) (φ k) (q k) (p i))) := by
  -- move the `m`-sum inwards
  have hswap :
      (∑ m ∈ Finset.Icc (Mn + 1) (2 * Mn),
        ∑ i, ∑ k, ∑ w ∈ wSph m,
          ‖∑ z ∈ primAnn (2 * N),
             pieceCoeff (Pa i k) (φ k) (q k) (p i) z * Work.FITop3.Zc w z‖)
      = ∑ i, ∑ k, ∑ m ∈ Finset.Icc (Mn + 1) (2 * Mn), ∑ w ∈ wSph m,
          ‖∑ z ∈ primAnn (2 * N),
             pieceCoeff (Pa i k) (φ k) (q k) (p i) z * Work.FITop3.Zc w z‖ := by
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro i _
    rw [Finset.sum_comm]
  rw [hswap]
  refine Finset.sum_le_sum (fun i _ => ?_)
  refine Finset.sum_le_sum (fun k _ => ?_)
  have hNle : (N : ℝ) ≤ (Pa i k).N := by rw [hPaN i k]; exact ha i
  have hsup' : ∀ u : ℝ, p i u ≠ 0 → u ≤ 2 * (N : ℝ) := fun u hu => hsup i u hu
  -- the two inner sums are the same
  have hinner : ∀ w : GaussianInt,
      (∑ z ∈ primAnn (2 * N), pieceCoeff (Pa i k) (φ k) (q k) (p i) z * Work.FITop3.Zc w z)
        = ∑ z ∈ Work.FITop.boxN (Pa i k),
            pieceCoeff (Pa i k) (φ k) (q k) (p i) z * Work.FITop3.Zc w z :=
    fun w => sum_primAnn_eq_sum_boxN hN hNle hsup' w
  -- reindex the `m`-window as the annulus
  have hstep :
      (∑ m ∈ Finset.Icc (Mn + 1) (2 * Mn), ∑ w ∈ wSph m,
          ‖∑ z ∈ primAnn (2 * N),
             pieceCoeff (Pa i k) (φ k) (q k) (p i) z * Work.FITop3.Zc w z‖)
      = ∑ w ∈ Work.FITop3.annM (Pa i k),
          ‖∑ z ∈ Work.FITop.boxN (Pa i k),
             pieceCoeff (Pa i k) (φ k) (q k) (p i) z * Work.FITop3.Zc w z‖ := by
    have hfun : ∀ w : GaussianInt,
        ‖∑ z ∈ primAnn (2 * N),
            pieceCoeff (Pa i k) (φ k) (q k) (p i) z * Work.FITop3.Zc w z‖
          = ‖∑ z ∈ Work.FITop.boxN (Pa i k),
            pieceCoeff (Pa i k) (φ k) (q k) (p i) z * Work.FITop3.Zc w z‖ := fun w => by
      rw [hinner w]
    rw [show (∑ m ∈ Finset.Icc (Mn + 1) (2 * Mn), ∑ w ∈ wSph m,
          ‖∑ z ∈ primAnn (2 * N),
             pieceCoeff (Pa i k) (φ k) (q k) (p i) z * Work.FITop3.Zc w z‖)
        = ∑ m ∈ Finset.Icc (Mn + 1) (2 * Mn), ∑ w ∈ wSph m,
          ‖∑ z ∈ Work.FITop.boxN (Pa i k),
             pieceCoeff (Pa i k) (φ k) (q k) (p i) z * Work.FITop3.Zc w z‖ from by
      apply Finset.sum_congr rfl
      intro m _
      exact Finset.sum_congr rfl (fun w _ => hfun w)]
    exact (fiber_sum_annM (Pa := Pa i k) (A := Mn) (hPaM i k) hMn
      (fun w => ‖∑ z ∈ Work.FITop.boxN (Pa i k),
             pieceCoeff (Pa i k) (φ k) (q k) (p i) z * Work.FITop3.Zc w z‖)).symm
  rw [hstep]
  -- Cauchy–Schwarz over the annulus, with `f ≥ 1` there and `card (annM) ≤ 100 M`
  have hCS := Work.FITop4.Red4.sum_norm_inner_le (Pa i k) (f i k)
    (pieceCoeff (Pa i k) (φ k) (q k) (p i)) (hMaj i k)
  have hnn : 0 ≤ ∑ w ∈ Work.FITop3.annM (Pa i k),
      ‖∑ z ∈ Work.FITop.boxN (Pa i k),
          pieceCoeff (Pa i k) (φ k) (q k) (p i) z * Work.FITop3.Zc w z‖ :=
    Finset.sum_nonneg fun w _ => norm_nonneg _
  calc ∑ w ∈ Work.FITop3.annM (Pa i k),
        ‖∑ z ∈ Work.FITop.boxN (Pa i k),
            pieceCoeff (Pa i k) (φ k) (q k) (p i) z * Work.FITop3.Zc w z‖
      = Real.sqrt ((∑ w ∈ Work.FITop3.annM (Pa i k),
          ‖∑ z ∈ Work.FITop.boxN (Pa i k),
              pieceCoeff (Pa i k) (φ k) (q k) (p i) z * Work.FITop3.Zc w z‖) ^ 2) :=
        (Real.sqrt_sq hnn).symm
    _ ≤ Real.sqrt (100 * (Pa i k).M
          * Dform (Pa i k) (f i k) (pieceCoeff (Pa i k) (φ k) (q k) (p i))) :=
        Real.sqrt_le_sqrt hCS

end

end Work.FITop4.Red5
