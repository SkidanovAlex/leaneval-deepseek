import Mathlib
import Submission.Work.BourgainPlan.IonescuWainger.BandLimitedL2Ortho
import Submission.Work.BourgainPlan.IonescuWainger.coe_sigmaAFinset
import Submission.Work.BourgainPlan.IonescuWainger.ShiftArcDefs

/-!
# Tao's `ortho`(ii) for the *major-arc systems* `f_{Σ_A}` (nonce form)

Source: T. Tao, *The Ionescu–Wainger multiplier theorem and the adeles*, arXiv:2008.05066, §4
(Lemma `ortho`(ii) for the hypersystem `(f_{Σ_A})_{A ∈ binom(S,≤k)}`).

`tsum_prod_mul_conj_eq_zero_of_nonce_l2` (`BandLimitedL2Ortho.lean`) is Tao's denominator
orthogonality for the *single* arc functions `f_{α_i}`, with `α_i ∈ Σ_{A_i}`.  The hypersystem
consumed by `superorthogonal_khintchine_hypersystem` consists instead of the **major-arc systems**

`f_{Σ_A} = Σ_{α ∈ Σ_A} f_α`,

whose frequency support is the *union* of the arcs `arcSet α ε` over `α ∈ Σ_A`.  This file proves
that the same orthogonality holds for these sums: the two key observations are that

* the frequency support of a finite sum is contained in the union of the frequency supports
  (`hasFreqSupport_finsetSum`), and
* the Minkowski sums of the *unions* of the arcs of the two halves of a nonce family are disjoint,
  simply because the tuples `α_i ∈ Σ_{A (inl i)}`, `β_i ∈ Σ_{A (inr i)}` range over the unions and
  each fixed pair is handled by `disjoint_setSumFin_arcSet_of_nonce`.

Main declarations:

* `disjoint_setSumFin_iUnion_arcSet_of_nonce` — the disjointness of the Minkowski sums of the
  unions of the arcs (the frequency side);
* `tsum_prod_star_mul_eq_zero_of_freqSupport` — the `ℓ²` pairing form
  `Σ_m ∏_i conj (f_i m) · g_i m = 0` (the conjugate on the first factor rather than the second);
* `tsum_prod_sigmaA_mul_conj_eq_zero_of_nonce` — **Tao's `ortho`(ii) for the major-arc systems**.
-/

open Finset MeasureTheory
open scoped BigOperators ENNReal lp

set_option autoImplicit false
set_option maxHeartbeats 2000000

namespace Work.BourgainPlan.IonescuWainger

/-- **Disjointness of the Minkowski sums of the unions of arcs of the two halves of a nonce
family.**  For a family `A : Fin (n+1) ⊕ Fin (n+1) → Finset ℕ` of subsets of a pairwise coprime
`S` (all elements `≥ 2`) carrying a nonce, and `2·(n+1)·ε < 1/∏_j Q_{A j}`, the Minkowski sums of
the full frequency supports `⋃_{α ∈ Σ_{A (inl i)}} arcSet α ε` and
`⋃_{β ∈ Σ_{A (inr i)}} arcSet β ε` are disjoint.

Proof: a point of each Minkowski sum exhibits tuples `α i ∈ Σ_{A (inl i)}`, `β i ∈ Σ_{A (inr i)}`
and perturbations `θ i, θ' i` with `|θ i|, |θ' i| ≤ ε` whose signed sums agree; a *single* pair of
arc tuples therefore meets both Minkowski sums of the single arcs, contradicting
`disjoint_setSumFin_arcSet_of_nonce`. -/
theorem disjoint_setSumFin_iUnion_arcSet_of_nonce {n : ℕ} {S : Finset ℕ}
    (h2 : ∀ q ∈ S, 2 ≤ q) (hS : ∀ p ∈ S, ∀ q ∈ S, p ≠ q → Nat.Coprime p q)
    {A : Fin (n + 1) ⊕ Fin (n + 1) → Finset ℕ} (hA : ∀ j, A j ⊆ S) (hnonce : HasNonce A)
    {ε : ℝ} (hsmall : 2 * ((n + 1 : ℕ) : ℝ) * ε < 1 / ((∏ j, QA (A j) : ℕ) : ℝ)) :
    Disjoint
      (setSumFin (n + 1)
        (fun i => ⋃ α ∈ (sigmaAFinset (A (Sum.inl i)) : Set Circle), arcSet α ε))
      (setSumFin (n + 1)
        (fun i => ⋃ β ∈ (sigmaAFinset (A (Sum.inr i)) : Set Circle), arcSet β ε)) := by
  classical
  have hA0 : ∀ j, 0 ∉ A j := fun j h0 => by
    have := h2 0 (hA j h0); omega
  rw [Set.disjoint_left]
  intro x hx hy
  rcases hx with ⟨g, hg, hgsum⟩
  rcases hy with ⟨h, hh, hhsum⟩
  have hchoiceL : ∀ i, ∃ α : Circle, α ∈ (sigmaAFinset (A (Sum.inl i)) : Set Circle) ∧
      ∃ θ : ℝ, |θ| ≤ ε ∧ g i = α + (θ : Circle) := by
    intro i
    rcases Set.mem_iUnion.mp (hg i) with ⟨α, hα⟩
    rcases Set.mem_iUnion.mp hα with ⟨hαmem, hαarc⟩
    rcases hαarc with ⟨θ, hθ, hgθ⟩
    exact ⟨α, hαmem, θ, hθ, hgθ⟩
  choose α hαmem θ hθ hgθ using hchoiceL
  have hchoiceR : ∀ i, ∃ β : Circle, β ∈ (sigmaAFinset (A (Sum.inr i)) : Set Circle) ∧
      ∃ θ : ℝ, |θ| ≤ ε ∧ h i = β + (θ : Circle) := by
    intro i
    rcases Set.mem_iUnion.mp (hh i) with ⟨β, hβ⟩
    rcases Set.mem_iUnion.mp hβ with ⟨hβmem, hβarc⟩
    rcases hβarc with ⟨θ, hθ, hhθ⟩
    exact ⟨β, hβmem, θ, hθ, hhθ⟩
  choose β hβmem θ' hθ' hhθ using hchoiceR
  have hα : ∀ i, α i ∈ sigmaA (A (Sum.inl i)) := fun i => by
    rw [← coe_sigmaAFinset (hA0 _)]; exact hαmem i
  have hβ : ∀ i, β i ∈ sigmaA (A (Sum.inr i)) := fun i => by
    rw [← coe_sigmaAFinset (hA0 _)]; exact hβmem i
  have hdisj := disjoint_setSumFin_arcSet_of_nonce h2 hS hA hnonce hα hβ hsmall
  have hx' : x ∈ setSumFin (n + 1) (fun i => arcSet (α i) ε) :=
    ⟨g, fun i => by rw [hgθ i]; exact ⟨θ i, hθ i, rfl⟩, hgsum⟩
  have hy' : x ∈ setSumFin (n + 1) (fun i => arcSet (β i) ε) :=
    ⟨h, fun i => by rw [hhθ i]; exact ⟨θ' i, hθ' i, rfl⟩, hhsum⟩
  exact (Set.disjoint_left.mp hdisj hx') hy'

/-- **The `ℓ²` pairing form with the conjugate on the first factor.**  If `f i, g i ∈ ℓ²(ℤ)` have
frequency supports in `E i`, `D i` and `Disjoint (Σ_i E i) (Σ_i D i)`, then
`Σ_m ∏_i conj (f i m) · g i m = 0`.

This is `tsum_prod_mul_conj_eq_zero_of_freqSupport` with the roles of the two families exchanged and
the conjugation moved from the product of the `g i` to the product of the `f i`, via
`conj (x · conj y) = conj x · y` and the continuity of `star` on `ℂ`. -/
theorem tsum_prod_star_mul_eq_zero_of_freqSupport {n : ℕ} (f g : Fin (n + 1) → ℤ → ℂ)
    (hf : ∀ i, Memℓp (f i) 2) (hg : ∀ i, Memℓp (g i) 2)
    (E D : Fin (n + 1) → Set Circle) (hE : ∀ i, HasFreqSupport (f i) (hf i) (E i))
    (hD : ∀ i, HasFreqSupport (g i) (hg i) (D i))
    (hdisj : Disjoint (setSumFin (n + 1) E) (setSumFin (n + 1) D)) :
    ∑' m : ℤ, ∏ i, (star (f i m) * g i m) = 0 := by
  have hEq : (∑' m : ℤ, ∏ i, (star (f i m) * g i m))
      = ∑' m : ℤ, star ((∏ i, f i m) * star (∏ i, g i m)) :=
    tsum_congr fun m => by
      rw [star_mul, star_star, star_prod, Finset.prod_mul_distrib]
      exact mul_comm _ _
  rw [hEq, ← tsum_star]
  rw [tsum_prod_mul_conj_eq_zero_of_freqSupport f g hf hg E D hE hD hdisj, star_zero]

/-- **Tao's `ortho`(ii) for the major-arc systems `f_{Σ_A}` (nonce form).**

Let `f : 𝕋 → ℤ → ℂ` be a band-limited system: every `f δ ∈ ℓ²(ℤ)` has Fourier support in the arc
`arcSet δ ε`.  For a family `A : Fin (n+1) ⊕ Fin (n+1) → Finset ℕ` of subsets of a pairwise
coprime `S` (all elements `≥ 2`) carrying a nonce, subject to the smallness
`2·(n+1)·ε < 1/∏_j Q_{A j}`, the major-arc systems of the two halves are orthogonal in `ℓ²(ℤ)`:

`Σ_m ∏_i conj (Σ_{α ∈ Σ_{A (inl i)}} f_α(m)) · (Σ_{β ∈ Σ_{A (inr i)}} f_β(m)) = 0`.

This is exactly the hypothesis shape consumed by Tao's `sys-ortho`(ii) for the hypersystem
`(f_{Σ_A})` (see `superorthogonal_khintchine_hypersystem`). -/
theorem tsum_prod_sigmaA_mul_conj_eq_zero_of_nonce {n : ℕ} {S : Finset ℕ}
    (h2 : ∀ q ∈ S, 2 ≤ q) (hS : ∀ p ∈ S, ∀ q ∈ S, p ≠ q → Nat.Coprime p q)
    {f : Circle → ℤ → ℂ} (hf : ∀ δ, Memℓp (f δ) 2) {ε : ℝ}
    (hF : ∀ δ, HasFreqSupport (f δ) (hf δ) (arcSet δ ε))
    {A : Fin (n + 1) ⊕ Fin (n + 1) → Finset ℕ} (hA : ∀ j, A j ⊆ S) (hnonce : HasNonce A)
    (hsmall : 2 * ((n + 1 : ℕ) : ℝ) * ε < 1 / ((∏ j, QA (A j) : ℕ) : ℝ)) :
    ∑' m : ℤ, ∏ i, (star (∑ α ∈ sigmaAFinset (A (Sum.inl i)), f α m)
      * (∑ β ∈ sigmaAFinset (A (Sum.inr i)), f β m)) = 0 := by
  have hFsupp : ∀ i : Fin (n + 1), HasFreqSupport
      (fun m => ∑ α ∈ sigmaAFinset (A (Sum.inl i)), f α m)
      (Memℓp.finsetSum (sigmaAFinset (A (Sum.inl i))) (fun α _ => hf α))
      (⋃ α ∈ (sigmaAFinset (A (Sum.inl i)) : Set Circle), arcSet α ε) :=
    fun i => hasFreqSupport_finsetSum (sigmaAFinset (A (Sum.inl i)))
      (f := fun α => f α) (hf := fun α => hf α) (E := fun α => arcSet α ε)
      (hE := fun α => hF α)
  have hGsupp : ∀ i : Fin (n + 1), HasFreqSupport
      (fun m => ∑ β ∈ sigmaAFinset (A (Sum.inr i)), f β m)
      (Memℓp.finsetSum (sigmaAFinset (A (Sum.inr i))) (fun β _ => hf β))
      (⋃ β ∈ (sigmaAFinset (A (Sum.inr i)) : Set Circle), arcSet β ε) :=
    fun i => hasFreqSupport_finsetSum (sigmaAFinset (A (Sum.inr i)))
      (f := fun β => f β) (hf := fun β => hf β) (E := fun β => arcSet β ε)
      (hE := fun β => hF β)
  exact tsum_prod_star_mul_eq_zero_of_freqSupport
    (fun i m => ∑ α ∈ sigmaAFinset (A (Sum.inl i)), f α m)
    (fun i m => ∑ β ∈ sigmaAFinset (A (Sum.inr i)), f β m)
    (fun i => Memℓp.finsetSum (sigmaAFinset (A (Sum.inl i))) (fun α _ => hf α))
    (fun i => Memℓp.finsetSum (sigmaAFinset (A (Sum.inr i))) (fun β _ => hf β))
    (fun i => ⋃ α ∈ (sigmaAFinset (A (Sum.inl i)) : Set Circle), arcSet α ε)
    (fun i => ⋃ β ∈ (sigmaAFinset (A (Sum.inr i)) : Set Circle), arcSet β ε)
    hFsupp hGsupp
    (disjoint_setSumFin_iUnion_arcSet_of_nonce h2 hS hA hnonce hsmall)

end Work.BourgainPlan.IonescuWainger
