import Mathlib
import Submission.Work.BourgainPlan.IonescuWainger.StrataArcArith
import Submission.Work.BourgainPlan.IonescuWainger.tsum_prod_sigmaA_mul_conj_eq_zero_of_nonce

open Finset MeasureTheory
open scoped BigOperators ENNReal lp

set_option autoImplicit false
set_option maxHeartbeats 2000000

namespace Work.BourgainPlan.IonescuWainger

/-- **Disjointness of the Minkowski sums of the unions of arcs of the two halves of a nonce
family, Tao's strata convention.**  This is `disjoint_setSumFin_iUnion_arcSet_of_nonce` with the
exact-denominator sets `sigmaAFinset` replaced everywhere by Tao's strata `sigmaStrataFinset`.

A common point of the two Minkowski sums exhibits tuples `α i ∈ Σ_{A (inl i)}`,
`β i ∈ Σ_{A (inr i)}` (strata, as `Set Circle`) and perturbations `θ i, θ' i` with
`|θ i|, |θ' i| ≤ ε` whose signed sums agree; this is forbidden by
`sigmaStrata_nonce_sum_perturbed_ne_zero` with `ι = Fin (n+1) ⊕ Fin (n+1)`,
`sgn = Sum.elim (fun _ => 1) (fun _ => -1)` and `Fintype.card (Fin (n+1) ⊕ Fin (n+1)) = 2(n+1)`. -/
theorem disjoint_setSumFin_iUnion_arcSet_of_nonce_strata {n : ℕ} {S : Finset ℕ}
    (h2 : ∀ q ∈ S, 2 ≤ q) (hS : ∀ p ∈ S, ∀ q ∈ S, p ≠ q → Nat.Coprime p q)
    {A : Fin (n + 1) ⊕ Fin (n + 1) → Finset ℕ} (hA : ∀ j, A j ⊆ S) (hnonce : HasNonce A)
    {ε : ℝ} (hsmall : 2 * ((n + 1 : ℕ) : ℝ) * ε < 1 / ((∏ j, QA (A j) : ℕ) : ℝ)) :
    Disjoint
      (setSumFin (n + 1)
        (fun i => ⋃ α ∈ (sigmaStrataFinset (A (Sum.inl i)) : Set Circle), arcSet α ε))
      (setSumFin (n + 1)
        (fun i => ⋃ β ∈ (sigmaStrataFinset (A (Sum.inr i)) : Set Circle), arcSet β ε)) := by
  classical
  rw [Set.disjoint_left]
  intro x hx hy
  rcases hx with ⟨g, hg, hgsum⟩
  rcases hy with ⟨h, hh, hhsum⟩
  have hchoiceL : ∀ i, ∃ α : Circle, α ∈ (sigmaStrataFinset (A (Sum.inl i)) : Set Circle) ∧
      ∃ θ : ℝ, |θ| ≤ ε ∧ g i = α + (θ : Circle) := by
    intro i
    rcases Set.mem_iUnion.mp (hg i) with ⟨α, hα⟩
    rcases Set.mem_iUnion.mp hα with ⟨hαmem, hαarc⟩
    rcases hαarc with ⟨θ, hθ, hgθ⟩
    exact ⟨α, hαmem, θ, hθ, hgθ⟩
  choose α hαmem θ hθ hgθ using hchoiceL
  have hchoiceR : ∀ i, ∃ β : Circle, β ∈ (sigmaStrataFinset (A (Sum.inr i)) : Set Circle) ∧
      ∃ θ : ℝ, |θ| ≤ ε ∧ h i = β + (θ : Circle) := by
    intro i
    rcases Set.mem_iUnion.mp (hh i) with ⟨β, hβ⟩
    rcases Set.mem_iUnion.mp hβ with ⟨hβmem, hβarc⟩
    rcases hβarc with ⟨θ, hθ, hhθ⟩
    exact ⟨β, hβmem, θ, hθ, hhθ⟩
  choose β hβmem θ' hθ' hhθ using hchoiceR
  obtain ⟨q, j, hqj, huniq⟩ := hnonce
  set sgn : Fin (n + 1) ⊕ Fin (n + 1) → ℤ := Sum.elim (fun _ => (1 : ℤ)) (fun _ => (-1 : ℤ))
    with hsgn
  have hsgn' : ∀ i, sgn i = 1 ∨ sgn i = -1 := by rintro (i | i) <;> simp [sgn]
  have hαA : ∀ i : Fin (n + 1) ⊕ Fin (n + 1),
      (Sum.elim α β) i ∈ (sigmaStrataFinset (A i) : Set Circle) := by
    rintro (i | i)
    · simpa using hαmem i
    · simpa using hβmem i
  have hθA : ∀ i : Fin (n + 1) ⊕ Fin (n + 1), |(Sum.elim θ θ') i| ≤ ε := by
    rintro (i | i)
    · simpa using hθ i
    · simpa using hθ' i
  have hsmall' : (Fintype.card (Fin (n + 1) ⊕ Fin (n + 1)) : ℝ) * ε
      < 1 / ((∏ i, QA (A i) : ℕ) : ℝ) := by
    have hc : (Fintype.card (Fin (n + 1) ⊕ Fin (n + 1)) : ℝ) = 2 * ((n + 1 : ℕ) : ℝ) := by
      rw [Fintype.card_sum, Fintype.card_fin]
      push_cast
      ring
    rw [hc]
    exact hsmall
  refine sigmaStrata_nonce_sum_perturbed_ne_zero h2 hS hA hsgn' hαA
    ⟨j, q, hqj, fun i hi hqi => hi (huniq i hqi)⟩ hθA hsmall' ?_
  have hterm : ∀ i : Fin (n + 1),
      (1 : ℤ) • (α i + (θ i : Circle)) + (-1 : ℤ) • (β i + (θ' i : Circle)) = g i - h i := by
    intro i
    rw [one_smul, neg_one_smul, ← hgθ i, ← hhθ i]
    abel
  rw [Fintype.sum_sum_type]
  simp only [sgn, Sum.elim_inl, Sum.elim_inr]
  rw [← Finset.sum_add_distrib]
  simp only [hterm]
  rw [Finset.sum_sub_distrib, hgsum, hhsum, sub_self]

/-- Tao's `ortho`(ii) (denominator orthogonality) for the major-arc systems `f_{Σ_A}` in Tao's
*strata* convention: for a band-limited system `f` (`f δ` Fourier-supported in `arcSet δ ε`) and a
family `A : Fin (n+1) ⊕ Fin (n+1) → Finset ℕ` of subsets of a pairwise coprime `S` (all elements
`≥ 2`) carrying a nonce, subject to the smallness `2(n+1)ε < 1/∏_j Q_{A j}`, the products of the
strata sums over the two halves of the family are orthogonal in `ℓ²(ℤ)`:

`Σ_m ∏_i conj (Σ_{α ∈ Σ_{A (inl i)}} f_α(m)) · (Σ_{β ∈ Σ_{A (inr i)}} f_β(m)) = 0`.

This is `tsum_prod_sigmaA_mul_conj_eq_zero_of_nonce` with the exact-denominator sets `sigmaAFinset`
replaced by Tao's strata `sigmaStrataFinset`.

Route (a verbatim port of `tsum_prod_sigmaA_mul_conj_eq_zero_of_nonce`, file in the same directory).
Two ingredients: (a) the strata analogue `disjoint_setSumFin_iUnion_arcSet_of_nonce_strata` of
`disjoint_setSumFin_iUnion_arcSet_of_nonce` (FreqArc.lean) — a common point of the two Minkowski
sums `setSumFin (n+1) (fun i => ⋃ α ∈ (sigmaStrataFinset (A (inl i)) : Set Circle), arcSet α ε)`
and its `inr` counterpart yields tuples `α i ∈ Σ_{A (inl i)}`, `β i ∈ Σ_{A (inr i)}` (strata, as
`Set Circle`) and perturbations `θ, θ'` with `|θ i|, |θ' i| ≤ ε` whose signed sums agree, which
`Work.BourgainPlan.IonescuWainger.sigmaStrata_nonce_sum_perturbed_ne_zero`
(`StrataArcArith.lean`, already proved) forbids with `ι = Fin (n+1) ⊕ Fin (n+1)`,
`sgn = Sum.elim (fun _ => 1) (fun _ => -1)` and `Fintype.card (Fin (n+1) ⊕ Fin (n+1)) = 2(n+1)`;
(b) the abstract pairing lemma `tsum_prod_star_mul_eq_zero_of_freqSupport` (in
`tsum_prod_sigmaA_mul_conj_eq_zero_of_nonce.lean`) applied to the families
`fun i m => ∑ α ∈ sigmaStrataFinset (A (Sum.inl i)), f α m` with frequency supports
`⋃ α ∈ (sigmaStrataFinset (A (Sum.inl i)) : Set Circle), arcSet α ε` (from
`hasFreqSupport_finsetSum`), whose `ℓ²`-membership is `Memℓp.finsetSum`.  Note that already-proved
convenience lemmas live in `indicator_sigmaStrataFinset_incl_excl.lean`
(`mem_sigmaSubAFinset_iff_zsmul_eq_zero`, `exists_arcPt_of_zsmul_eq_zero`) and in
`opArc_l2_endpoint_strata.lean` (`circle_strata_add_mem`, `circle_strata_disjoint`,
`circle_strata_decomp_unique`). -/
theorem tsum_prod_sigmaStrata_mul_conj_eq_zero_of_nonce {n : ℕ} {S : Finset ℕ}
    (h2 : ∀ q ∈ S, 2 ≤ q) (hS : ∀ p ∈ S, ∀ q ∈ S, p ≠ q → Nat.Coprime p q)
    {f : Work.BourgainPlan.IonescuWainger.Circle → ℤ → ℂ} (hf : ∀ δ, Memℓp (f δ) 2) {ε : ℝ}
    (hF : ∀ δ, Work.BourgainPlan.IonescuWainger.HasFreqSupport (f δ) (hf δ)
      (Work.BourgainPlan.IonescuWainger.arcSet δ ε))
    {A : Fin (n + 1) ⊕ Fin (n + 1) → Finset ℕ} (hA : ∀ j, A j ⊆ S)
    (hnonce : Work.BourgainPlan.IonescuWainger.HasNonce A)
    (hsmall : 2 * ((n + 1 : ℕ) : ℝ) * ε <
      1 / ((∏ j, Work.BourgainPlan.IonescuWainger.QA (A j) : ℕ) : ℝ)) :
    ∑' m : ℤ, ∏ i,
      (star (∑ α ∈ Work.BourgainPlan.IonescuWainger.sigmaStrataFinset (A (Sum.inl i)), f α m)
        * (∑ β ∈ Work.BourgainPlan.IonescuWainger.sigmaStrataFinset (A (Sum.inr i)), f β m)) = 0 := by
  have hFsupp : ∀ i : Fin (n + 1), HasFreqSupport
      (fun m => ∑ α ∈ sigmaStrataFinset (A (Sum.inl i)), f α m)
      (Memℓp.finsetSum (sigmaStrataFinset (A (Sum.inl i))) (fun α _ => hf α))
      (⋃ α ∈ (sigmaStrataFinset (A (Sum.inl i)) : Set Circle), arcSet α ε) :=
    fun i => hasFreqSupport_finsetSum (sigmaStrataFinset (A (Sum.inl i)))
      (f := fun α => f α) (hf := fun α => hf α) (E := fun α => arcSet α ε)
      (hE := fun α => hF α)
  have hGsupp : ∀ i : Fin (n + 1), HasFreqSupport
      (fun m => ∑ β ∈ sigmaStrataFinset (A (Sum.inr i)), f β m)
      (Memℓp.finsetSum (sigmaStrataFinset (A (Sum.inr i))) (fun β _ => hf β))
      (⋃ β ∈ (sigmaStrataFinset (A (Sum.inr i)) : Set Circle), arcSet β ε) :=
    fun i => hasFreqSupport_finsetSum (sigmaStrataFinset (A (Sum.inr i)))
      (f := fun β => f β) (hf := fun β => hf β) (E := fun β => arcSet β ε)
      (hE := fun β => hF β)
  exact tsum_prod_star_mul_eq_zero_of_freqSupport
    (fun i m => ∑ α ∈ sigmaStrataFinset (A (Sum.inl i)), f α m)
    (fun i m => ∑ β ∈ sigmaStrataFinset (A (Sum.inr i)), f β m)
    (fun i => Memℓp.finsetSum (sigmaStrataFinset (A (Sum.inl i))) (fun α _ => hf α))
    (fun i => Memℓp.finsetSum (sigmaStrataFinset (A (Sum.inr i))) (fun β _ => hf β))
    (fun i => ⋃ α ∈ (sigmaStrataFinset (A (Sum.inl i)) : Set Circle), arcSet α ε)
    (fun i => ⋃ β ∈ (sigmaStrataFinset (A (Sum.inr i)) : Set Circle), arcSet β ε)
    hFsupp hGsupp
    (disjoint_setSumFin_iUnion_arcSet_of_nonce_strata h2 hS hA hnonce hsmall)

end Work.BourgainPlan.IonescuWainger
