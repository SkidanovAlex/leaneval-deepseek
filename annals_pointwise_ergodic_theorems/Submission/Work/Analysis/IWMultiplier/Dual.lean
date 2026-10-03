/-
Copyright (c) 2026 The AnnalsChallenge team. All rights reserved.
Released under Apache 2.0 license as described in the LICENSE file.
Authors: The AnnalsChallenge team
-/
import Submission.Work.Analysis.IWMultiplier.IWLqBound_interpolation

/-!
# Duality for the Ionescu–Wainger multiplier

The pair of lemmas in this file is the duality step of the vector-valued Ionescu–Wainger multiplier
theorem: the `ℓ^{q'}` bound for the multiplier with the conjugate symbol follows from the `ℓ^q`
bound for the multiplier with the original symbol, with the *same* constant.  This is the adjoint
of the multiplier, `(T^{≤l}_φ)* = T^{≤l}_{φ̄}` (cf. `Work.Analysis.IonescuWainger.iwOpSet_adjoint`),
together with the isometry of the duality pairing.

In the notation of this area the adjoint identity is

`pairingEnorm (iwConv A Φ̄ g) f = pairingEnorm g (iwConv A Φ f)`

for finitely supported `f, g`, where `pairingEnorm u v = ‖∑_n ⟪u n, v n⟫‖ₑ` is the duality pairing of
`Work.Analysis.IWMultiplier.VecDefs`.  The two ingredients are the kernel identity
`iwKernel (iwSymbolSet A Φ̄) j = star (iwKernel (iwSymbolSet A Φ) (-j))` and the symmetry
`pairingEnorm u v = pairingEnorm v u` of the pairing.

## Main results

* `Work.Analysis.IWMultiplier.iwKernel_star_neg`;
* `Work.Analysis.IWMultiplier.pairingEnorm_comm`;
* `Work.Analysis.IWMultiplier.pairingEnorm_adjoint`;
* `Work.Analysis.IWMultiplier.IWLqBound_of_dual`.
-/

set_option autoImplicit false
set_option maxHeartbeats 4000000

open scoped BigOperators ENNReal NNReal InnerProductSpace
open MeasureTheory

namespace Work.Analysis.IWMultiplier

open Work.Analysis.IonescuWainger

local notation "countZ" => (MeasureTheory.Measure.count : MeasureTheory.Measure ℤ)


/-- The kernel of the conjugate symbol is the conjugate of the reflected kernel. -/
theorem iwKernel_star_neg (A : Finset Circle) (Φ : Circle → ℂ) (j : ℤ) :
    iwKernel (iwSymbolSet A (fun ξ => star (Φ ξ))) j
      = star (iwKernel (iwSymbolSet A Φ) (-j)) := by
  simp only [iwKernel, fourierCoeff, neg_neg, smul_eq_mul, ← starRingEnd_apply, ← integral_conj,
    map_mul, fourier_neg]
  refine integral_congr_ae (ae_of_all _ fun t => ?_)
  simp only [iwSymbolSet_apply, map_sum]

/-- The duality pairing is symmetric in its two arguments. -/
theorem pairingEnorm_comm {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    (u v : ℤ → H) : pairingEnorm u v = pairingEnorm v u := by
  rw [pairingEnorm, pairingEnorm]
  have hterm : ∀ n : ℤ, ⟪v n, u n⟫_ℂ = starRingEnd ℂ (⟪u n, v n⟫_ℂ) := fun n => by
    simpa using (inner_conj_symm (v n) (u n)).symm
  have h : (∑' n : ℤ, ⟪v n, u n⟫_ℂ) = starRingEnd ℂ (∑' n : ℤ, ⟪u n, v n⟫_ℂ) := by
    rw [tsum_congr hterm, ← Complex.conj_tsum]
  rw [h]
  simp

section Adjoint

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]

/-- **The adjoint of the IW multiplier is the multiplier with the conjugate symbol.**  In the
language of the duality pairing `pairingEnorm u v = ‖∑_n ⟪u n, v n⟫‖ₑ`, for finitely supported
`f, g`:

`pairingEnorm (iwConv A Φ̄ g) f = pairingEnorm g (iwConv A Φ f)`.

This is the finite computation `∑_{n,m} K_{m-n} ⟪g m, f n⟫` (with `K_j` the kernel of
`iwSymbolSet A Φ`) computed in the two possible orders, using
`iwKernel_star_neg` for the kernel of the conjugate symbol. -/
theorem pairingEnorm_adjoint (A : Finset Circle) (Φ : Circle → ℂ) (f g : ℤ → H)
    (hf : (Function.support f).Finite) (hg : (Function.support g).Finite) :
    pairingEnorm (iwConv A (fun ξ => star (Φ ξ)) g) f = pairingEnorm g (iwConv A Φ f) := by
  classical
  have hf0 : ∀ n : ℤ, n ∉ hf.toFinset → f n = 0 := fun n hn => by
    by_contra hne
    exact hn (hf.mem_toFinset.mpr hne)
  have hg0 : ∀ n : ℤ, n ∉ hg.toFinset → g n = 0 := fun n hn => by
    by_contra hne
    exact hn (hg.mem_toFinset.mpr hne)
  have h₁ : (∑' n : ℤ, ⟪iwConv A (fun ξ => star (Φ ξ)) g n, f n⟫_ℂ)
      = ∑ n ∈ hf.toFinset, ∑ m ∈ hg.toFinset,
          iwKernel (iwSymbolSet A Φ) (m - n) * ⟪g m, f n⟫_ℂ := by
    rw [tsum_eq_sum (L := SummationFilter.unconditional ℤ) (s := hf.toFinset)
      (fun n hn => by rw [hf0 n hn, inner_zero_right])]
    refine Finset.sum_congr rfl fun n _ => ?_
    rw [iwConv_apply_eq_sum A _ g hg.toFinset hg0 n, sum_inner]
    refine Finset.sum_congr rfl fun m _ => ?_
    rw [inner_smul_left, iwKernel_star_neg, starRingEnd_apply, star_star, neg_sub]
  have h₂ : (∑' n : ℤ, ⟪g n, iwConv A Φ f n⟫_ℂ)
      = ∑ n ∈ hg.toFinset, ∑ m ∈ hf.toFinset,
          iwKernel (iwSymbolSet A Φ) (n - m) * ⟪g n, f m⟫_ℂ := by
    rw [tsum_eq_sum (L := SummationFilter.unconditional ℤ) (s := hg.toFinset)
      (fun n hn => by rw [hg0 n hn, inner_zero_left])]
    refine Finset.sum_congr rfl fun n _ => ?_
    rw [iwConv_apply_eq_sum A Φ f hf.toFinset hf0 n, inner_sum]
    refine Finset.sum_congr rfl fun m _ => ?_
    rw [inner_smul_right]
  have hcomm : (∑ n ∈ hf.toFinset, ∑ m ∈ hg.toFinset,
        iwKernel (iwSymbolSet A Φ) (m - n) * ⟪g m, f n⟫_ℂ)
      = ∑ n ∈ hg.toFinset, ∑ m ∈ hf.toFinset,
        iwKernel (iwSymbolSet A Φ) (n - m) * ⟪g n, f m⟫_ℂ := by
    rw [Finset.sum_comm]
  rw [pairingEnorm, pairingEnorm, h₁, hcomm, h₂]

end Adjoint

/-- **Duality for the Ionescu–Wainger multiplier.**  A bound at the exponent `q` gives, with the
*same* constant, the bound at the Hölder dual exponent `q' = q/(q-1)` for the multiplier with the
conjugate symbol.  This is the `ℓ^q`/`ℓ^{q'}` duality of the adjoint `(T^{≤l}_φ)* = T^{≤l}_{φ̄}`
(`pairingEnorm_adjoint`), combined with the duality characterisation
`eLpNorm_le_of_pairing_le` of the `ℓ^{q'}` norm and Hölder's inequality `pairingEnorm_le`. -/
theorem IWLqBound_of_dual (A : Finset Circle) (Φ : Circle → ℂ)
    {q : ENNReal} {C : NNReal} (h : IWLqBound A Φ q C) (hq : 1 < q.toReal) :
    IWLqBound A (fun ξ => star (Φ ξ))
      (ENNReal.ofReal (q.toReal / (q.toReal - 1))) C := by
  intro H _ _ _ g hg
  let p : ℝ := q.toReal
  have hp1 : 1 < p := hq
  have hqtop : q ≠ ⊤ := by
    intro hh
    rw [hh] at hq
    norm_num at hq
  have hq_eq : ENNReal.ofReal p = q := ENNReal.ofReal_toReal hqtop
  have hdual1 : 1 < p / (p - 1) := by
    rw [lt_div_iff₀ (by linarith : (0 : ℝ) < p - 1)]
    linarith
  have hconj2 : p.HolderConjugate (p / (p - 1)) := by
    refine ⟨?_, by linarith, by positivity⟩
    rw [inv_div]
    field_simp
    ring
  have hconj : (p / (p - 1)).HolderConjugate p := hconj2.symm
  have hexp : ENNReal.ofReal (q.toReal / (q.toReal - 1)) = ENNReal.ofReal (p / (p - 1)) := rfl
  rw [hexp]
  refine eLpNorm_le_of_pairing_le hdual1 hconj (iwConv A (fun ξ => star (Φ ξ)) g) ?_
  intro f hf
  rw [pairingEnorm_adjoint A Φ f g hf hg, pairingEnorm_comm]
  calc pairingEnorm (iwConv A Φ f) g
      ≤ eLpNorm (iwConv A Φ f) (ENNReal.ofReal p) countZ
          * eLpNorm g (ENNReal.ofReal (p / (p - 1))) countZ :=
        pairingEnorm_le (iwConv A Φ f) g hg (ennreal_holderConjugate_ofReal hconj2)
    _ ≤ (ENNReal.ofReal (C : ℝ) * eLpNorm f (ENNReal.ofReal p) countZ)
          * eLpNorm g (ENNReal.ofReal (p / (p - 1))) countZ := by
        refine mul_le_mul_of_nonneg_right ?_ (by positivity)
        rw [hq_eq]
        exact h H f hf
    _ = (ENNReal.ofReal (C : ℝ) * eLpNorm g (ENNReal.ofReal (p / (p - 1))) countZ)
          * eLpNorm f (ENNReal.ofReal p) countZ := by ring

end Work.Analysis.IWMultiplier
