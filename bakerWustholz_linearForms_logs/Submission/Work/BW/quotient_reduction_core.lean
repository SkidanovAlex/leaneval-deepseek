import Mathlib
import ChallengeDeps
import Submission.Work.BW.Defs
import Submission.Work.BW.DefsMult
import Submission.Work.BW.DefsMP
import Submission.Work.BW.zeroDeg_reduce
import Submission.Work.BW.applyW_cons_eq_applyDer
import Submission.Work.BW.quotient_reduction

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

namespace Work.BW

/-- The partial-degeneracy reduction without any hypothesis on `B`: drop the torus coordinates
`k` with `𝒟 k.succ < 1` (on which `P` has degree `0`), rename `P` onto the remaining coordinates
`range σ` (`σ` strictly increasing), and transport the vanishing of `applyDer c` at `ptS ℓ s` to
the vanishing of `applyW w` at `ptTheta (exp ∘ ℓ ∘ σ) s`, `w = (e₀, (0, c m ∘ σ))`.
This is `quotient_reduction` with `B`, `hB`, `hker`, `hBi` and the `span = ⊤` conjunct removed, and
with `StrictMono σ` and "every dropped coordinate is degenerate" added to the output. -/
theorem quotient_reduction_core {r : ℕ} (P : MvPolynomial (Fin (r + 1)) ℂ) (hP : P ≠ 0)
    (𝒟 : Fin (r + 1) → ℝ) (hdeg : ∀ j, (P.degreeOf j : ℝ) ≤ 𝒟 j) (h𝒟0 : 1 ≤ 𝒟 0)
    (Sq Tq : ℕ → ℕ) (𝒮 𝒯 : ℝ)
    (hSsum : ((∑ m ∈ Finset.range (r + 1), Sq m : ℕ) : ℝ) ≤ 𝒮)
    (hTsum : ((∑ m ∈ Finset.range (r + 1), Tq m : ℕ) : ℝ) ≤ 𝒯)
    (c : Fin (r - 1) → Fin r → ℚ) (ℓ : Fin r → ℂ)
    (hvan : ∀ s : ℕ, (s : ℝ) ≤ 𝒮 → ∀ (t0 : ℕ) (t : Fin (r - 1) → ℕ),
      ((t0 + ∑ m, t m : ℕ) : ℝ) ≤ 𝒯 →
      MvPolynomial.eval (ptS ℓ s) (applyDer c t0 t P) = 0)
    (i : Fin r) (hi : 𝒟 i.succ < 1) :
    ∃ (N' : ℕ) (σ : Fin N' → Fin r) (P' : MvPolynomial (Fin (N' + 1)) ℂ) (δ : Fin (N' + 1) → ℝ)
      (w : Fin (r - 1 + 1) → Fin (N' + 1) → ℂ),
      N' < r ∧ StrictMono σ ∧ (∀ k : Fin r, k ∉ Set.range σ → 𝒟 k.succ < 1) ∧ P' ≠ 0 ∧
      (∀ j, 0 ≤ δ j) ∧ 1 ≤ δ 0 ∧ (∀ j, 1 ≤ ⌊δ j⌋₊) ∧
      (∀ j, P'.degreeOf j ≤ ⌊δ j⌋₊) ∧
      (∀ j, δ j = 𝒟 (liftIdx σ j)) ∧
      (∀ m : Fin (r - 1), w m.succ = Fin.cons 0 (fun j : Fin N' => ((c m (σ j) : ℚ) : ℂ))) ∧
      w 0 = Pi.single (0 : Fin (N' + 1)) (1 : ℂ) ∧
      (∀ s, s ≤ ∑ m ∈ Finset.range (N' + 1), Sq m → ∀ t : Fin (r - 1 + 1) → ℕ,
        ∑ k, t k ≤ ∑ m ∈ Finset.range (N' + 1), Tq m →
        MvPolynomial.eval (ptTheta (fun j => Complex.exp (ℓ (σ j))) s) (applyW w t P') = 0) := by
  classical
  -- `Z` is the set of coordinates where `𝒟 ≥ 1`; `σ` enumerates `Z` increasingly.
  set Z : Finset (Fin r) := Finset.univ.filter (fun k => 1 ≤ 𝒟 k.succ) with hZdef
  set σ : Fin Z.card → Fin r := ⇑(Z.orderEmbOfFin rfl) with hσdef
  have hσmono : StrictMono σ := (Z.orderEmbOfFin rfl).strictMono
  have hσinj : Function.Injective σ := hσmono.injective
  have hσrange : Set.range σ = ↑Z := Finset.range_orderEmbOfFin Z rfl
  have hσge : ∀ j, 1 ≤ 𝒟 (σ j).succ := by
    intro j
    have := Finset.orderEmbOfFin_mem Z rfl j
    simpa only [hZdef, Finset.mem_filter, Finset.mem_univ, true_and] using this
  have hσlt : ∀ k, k ∉ Set.range σ → 𝒟 k.succ < 1 := by
    intro k hk
    have hks : k ∉ Z := fun h => hk (by rw [hσrange]; exact h)
    simp only [hZdef, Finset.mem_filter, Finset.mem_univ, true_and] at hks
    exact not_le.mp hks
  have hN'lt : Z.card < r := by
    have hssub : Z ⊂ Finset.univ := Finset.ssubset_iff_subset_ne.mpr
      ⟨Finset.subset_univ Z, fun h => by
        have : i ∈ Z := by rw [h]; exact Finset.mem_univ i
        simp only [hZdef, Finset.mem_filter, Finset.mem_univ, true_and] at this
        exact absurd this (not_le.mpr hi)⟩
    simpa using Finset.card_lt_card hssub
  have hZdeg : ∀ k, k ∉ Set.range σ → P.degreeOf k.succ = 0 := by
    intro k hk
    have hlt : (P.degreeOf k.succ : ℝ) < 1 := lt_of_le_of_lt (hdeg k.succ) (hσlt k hk)
    have : P.degreeOf k.succ < 1 := by exact_mod_cast hlt
    omega
  obtain ⟨P', hP'ren, hP'deg, hP'transfer⟩ :=
    zeroDeg_reduce (q := r - 1 + 1) σ hσmono P hZdeg
  -- the invariant-derivation family `W` on the big torus and the transported family `w`
  let W : Fin (r - 1 + 1) → Fin (r + 1) → ℂ :=
    Fin.cons (Pi.single (0 : Fin (r + 1)) (1 : ℂ))
      (fun m : Fin (r - 1) => Fin.cons 0 (fun ii : Fin r => ((c m ii : ℚ) : ℂ)))
  let w : Fin (r - 1 + 1) → Fin (Z.card + 1) → ℂ :=
    Fin.cons (Pi.single (0 : Fin (Z.card + 1)) (1 : ℂ))
      (fun m : Fin (r - 1) => Fin.cons 0 (fun j : Fin Z.card => ((c m (σ j) : ℚ) : ℂ)))
  have hWdef : W = Fin.cons (Pi.single (0 : Fin (r + 1)) (1 : ℂ))
      (fun m : Fin (r - 1) => Fin.cons 0 (fun ii : Fin r => ((c m ii : ℚ) : ℂ))) := rfl
  have hwdef : w = Fin.cons (Pi.single (0 : Fin (Z.card + 1)) (1 : ℂ))
      (fun m : Fin (r - 1) => Fin.cons 0 (fun j : Fin Z.card => ((c m (σ j) : ℚ) : ℂ))) := rfl
  have hWw : (fun k => W k ∘ liftIdx σ) = w := by
    rw [hWdef, hwdef]
    funext k
    rcases Fin.eq_zero_or_eq_succ k with rfl | ⟨m, rfl⟩
    · rw [Fin.cons_zero, Fin.cons_zero]; exact qr_pi_single σ
    · rw [Fin.cons_succ, Fin.cons_succ]; exact qr_cons σ (c m)
  have hw0 : w 0 = Pi.single (0 : Fin (Z.card + 1)) (1 : ℂ) := by
    rw [hwdef]; exact Fin.cons_zero _ _
  have hw1 : ∀ m : Fin (r - 1),
      w m.succ = Fin.cons 0 (fun j : Fin Z.card => ((c m (σ j) : ℚ) : ℂ)) := by
    intro m; rw [hwdef]; exact Fin.cons_succ _ _ _
  have hδnn : ∀ j : Fin (Z.card + 1), (0:ℝ) ≤ (fun j => 𝒟 (liftIdx σ j)) j := by
    intro j
    rcases Fin.eq_zero_or_eq_succ j with rfl | ⟨k, rfl⟩
    · simp only [zeroDeg_liftIdx_zero]; linarith [h𝒟0]
    · simp only [zeroDeg_liftIdx_succ]; linarith [hσge k]
  have hδ0 : (1:ℝ) ≤ (fun j => 𝒟 (liftIdx σ j)) 0 := by
    simp only [zeroDeg_liftIdx_zero]; exact h𝒟0
  have hδ1 : ∀ j : Fin (Z.card + 1), (1:ℕ) ≤ ⌊(fun j => 𝒟 (liftIdx σ j)) j⌋₊ := by
    intro j
    rcases Fin.eq_zero_or_eq_succ j with rfl | ⟨k, rfl⟩
    · simp only [zeroDeg_liftIdx_zero]; exact (Nat.one_le_floor_iff _).mpr h𝒟0
    · simp only [zeroDeg_liftIdx_succ]; exact (Nat.one_le_floor_iff _).mpr (hσge k)
  have hdeg' : ∀ j : Fin (Z.card + 1), P'.degreeOf j ≤ ⌊(fun j => 𝒟 (liftIdx σ j)) j⌋₊ := by
    intro j
    rw [hP'deg j]
    exact Nat.le_floor (by simpa using hdeg (liftIdx σ j))
  refine ⟨Z.card, σ, P', (fun j => 𝒟 (liftIdx σ j)), w,
    hN'lt, hσmono, hσlt, ?_, hδnn, hδ0, hδ1, hdeg', ?_, hw1, hw0, ?_⟩
  · intro h0; exact hP (by rw [← hP'ren, h0, map_zero])
  · intro j; rfl
  · intro s hs t ht
    have hsub : Finset.range (Z.card + 1) ⊆ Finset.range (r + 1) := Finset.range_mono (by omega)
    have hSbound : (s : ℝ) ≤ 𝒮 := by
      have hle : (∑ m ∈ Finset.range (Z.card + 1), Sq m) ≤ (∑ m ∈ Finset.range (r + 1), Sq m) :=
        Finset.sum_le_sum_of_subset hsub
      have h1 : (s : ℝ) ≤ ((∑ m ∈ Finset.range (Z.card + 1), Sq m : ℕ) : ℝ) := by
        exact_mod_cast hs
      have h2 : ((∑ m ∈ Finset.range (Z.card + 1), Sq m : ℕ) : ℝ) ≤
          ((∑ m ∈ Finset.range (r + 1), Sq m : ℕ) : ℝ) := by exact_mod_cast hle
      linarith [h1, h2, hSsum]
    have hTbound : ((t 0 + ∑ m : Fin (r - 1), t m.succ : ℕ) : ℝ) ≤ 𝒯 := by
      have hle : (∑ m ∈ Finset.range (Z.card + 1), Tq m) ≤ (∑ m ∈ Finset.range (r + 1), Tq m) :=
        Finset.sum_le_sum_of_subset hsub
      have ht' : (t 0 + ∑ m : Fin (r - 1), t m.succ) ≤ ∑ m ∈ Finset.range (Z.card + 1), Tq m := by
        simpa only [Fin.sum_univ_succ] using ht
      have h1 : ((t 0 + ∑ m : Fin (r - 1), t m.succ : ℕ) : ℝ) ≤
          ((∑ m ∈ Finset.range (r + 1), Tq m : ℕ) : ℝ) := by
        exact_mod_cast le_trans ht' hle
      linarith [h1, hTsum]
    have hT := hP'transfer W t (fun j => Complex.exp (ℓ j)) s
    have hθσ : (fun j => Complex.exp (ℓ j)) ∘ σ = (fun j => Complex.exp (ℓ (σ j))) := by
      funext j; rfl
    rw [hWdef, hWw, hθσ, qr_ptS, applyW_cons_eq_applyDer] at hT
    exact hT.symm.trans (hvan s hSbound (t 0) (fun m => t m.succ) hTbound)

end Work.BW
