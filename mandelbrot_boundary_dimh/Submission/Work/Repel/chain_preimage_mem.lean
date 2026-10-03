import Mathlib
import Submission.Work.L62.chain
import Submission.Work.Interfaces.Parabolic

/-!
# Preimages along a chain, shifted by integers

`Work.L62.IsChain` gives a chain of discs `W j` on which `ĥ = R - β` maps `W (j+1)` bijectively
onto `W j`; the whole interval of the construction is that `ĥ` is `T`-equivariant
(`IsTEquivariantOn R DR`, i.e. `DR` is invariant under `w ↦ w + 1` and `R (w+1) = R w + 1` on
`DR`).  This file records the consequence used by the §6 composite of Shishikura's Lemma 6.2
(rows "5/6" of the design table):

  for every `u' ∈ W 0` and every integer `k`, there is exactly one `u ∈ W j + k` with
  `ĥ^[j] u = u' + k`.

The point is that `ĥ^[j]` commutes with the integer translation `w ↦ w + k` *on the chain*
(`W i ⊆ DR` for `i ≥ 1`, and `DR` is `T`-invariant, so every intermediate point of the shifted
orbit stays in `DR`), and that `ĥ^[j] : W j → W 0` is injective.  In particular the chain
bijection `ĥ^[j] : W j + k → W 0 + k` of row 5 of the design table is available, which is what the
composite `z ↦ w₀ ↦ ζ ↦ u ∈ W j + k ↦ ĥ^[j] u ∈ W 0 + k ↦ u'` uses.
-/

namespace Work.Repel

open MandelDim Set

noncomputable section

/-! ## Integer translations of `T`-invariant sets and `T`-equivariant maps -/

/-- A `T`-invariant set is invariant under every natural shift. -/
lemma chainPre_mem_add_nat {D : Set ℂ} (hD : IsTInvariant D) (n : ℕ) (w : ℂ) :
    (w ∈ D ↔ w + ((n : ℤ) : ℂ) ∈ D) := by
  induction n with
  | zero => simp
  | succ m ih =>
      have hcast : w + (((m + 1 : ℕ) : ℤ) : ℂ) = (w + ((m : ℤ) : ℂ)) + 1 := by
        push_cast; ring
      rw [hcast, ← hD (w + ((m : ℤ) : ℂ)), ih]

/-- A `T`-invariant set is invariant under every integer shift. -/
lemma chainPre_mem_add_int {D : Set ℂ} (hD : IsTInvariant D) (k : ℤ) (w : ℂ) :
    (w ∈ D ↔ w + (k : ℂ) ∈ D) := by
  rcases lt_or_ge 0 k with hk | hk
  · obtain ⟨n, rfl⟩ := Int.eq_ofNat_of_zero_le hk.le
    exact chainPre_mem_add_nat hD n w
  · obtain ⟨n, hn⟩ := Int.eq_ofNat_of_zero_le (show 0 ≤ -k by omega)
    have hk' : k = -(n : ℤ) := by omega
    have h := chainPre_mem_add_nat hD n (w + (k : ℂ))
    have hcast : w + (k : ℂ) + ((n : ℤ) : ℂ) = w := by
      rw [hk']; push_cast; ring
    rw [hcast] at h
    exact h.symm

/-- A `T`-equivariant map shifts by natural amounts on its domain. -/
lemma chainPre_equiv_add_nat {E : ℂ → ℂ} {D : Set ℂ} (h : IsTEquivariantOn E D) (n : ℕ)
    {w : ℂ} (hw : w ∈ D) : E (w + ((n : ℤ) : ℂ)) = E w + ((n : ℤ) : ℂ) := by
  induction n with
  | zero => simp
  | succ m ih =>
      have hmem : w + ((m : ℤ) : ℂ) ∈ D := (chainPre_mem_add_nat h.1 m w).mp hw
      have hcast : w + (((m + 1 : ℕ) : ℤ) : ℂ) = (w + ((m : ℤ) : ℂ)) + 1 := by
        push_cast; ring
      have hcast2 : E w + (((m + 1 : ℕ) : ℤ) : ℂ) = (E w + ((m : ℤ) : ℂ)) + 1 := by
        push_cast; ring
      rw [hcast, h.2 (w + ((m : ℤ) : ℂ)) hmem, ih, hcast2]

/-- A `T`-equivariant map shifts by negative natural amounts on its domain. -/
lemma chainPre_equiv_add_neg_nat {E : ℂ → ℂ} {D : Set ℂ} (h : IsTEquivariantOn E D) (n : ℕ)
    {w : ℂ} (hw : w ∈ D) :
    E (w + (-((n : ℤ) : ℂ))) = E w + (-((n : ℤ) : ℂ)) := by
  induction n with
  | zero => simp
  | succ m ih =>
      have hmem : w + (-(((m + 1 : ℕ) : ℤ) : ℂ)) ∈ D := by
        have h' := (chainPre_mem_add_int h.1 (-(((m + 1 : ℕ) : ℤ))) w).mp hw
        simpa using h'
      have h1 := h.2 (w + (-(((m + 1 : ℕ) : ℤ) : ℂ))) hmem
      have heq : (w + (-(((m + 1 : ℕ) : ℤ) : ℂ))) + 1 = w + (-((m : ℤ) : ℂ)) := by
        push_cast; ring
      rw [heq] at h1
      have h2 : E (w + (-(((m + 1 : ℕ) : ℤ) : ℂ))) = E (w + (-((m : ℤ) : ℂ))) + (-1) := by
        rw [h1]; ring
      rw [h2, ih]
      push_cast; ring

/-- A `T`-equivariant map shifts by any integer amount on its domain. -/
lemma chainPre_equiv_add_int {E : ℂ → ℂ} {D : Set ℂ} (h : IsTEquivariantOn E D) (k : ℤ)
    {w : ℂ} (hw : w ∈ D) : E (w + (k : ℂ)) = E w + (k : ℂ) := by
  rcases lt_or_ge 0 k with hk | hk
  · obtain ⟨n, rfl⟩ := Int.eq_ofNat_of_zero_le hk.le
    exact chainPre_equiv_add_nat h n hw
  · obtain ⟨n, hn⟩ := Int.eq_ofNat_of_zero_le (show 0 ≤ -k by omega)
    have hk' : k = -(n : ℤ) := by omega
    rw [hk']
    simp only [Int.cast_neg]
    exact chainPre_equiv_add_neg_nat h n hw

/-- A `T`-equivariant map commutes with an integer translation along an orbit, as long as the
first `j` points of the orbit stay in the domain. -/
lemma chainPre_iterate_add_int {E : ℂ → ℂ} {D : Set ℂ} (h : IsTEquivariantOn E D) :
    ∀ (j : ℕ) (k : ℤ) {w : ℂ}, (∀ i < j, E^[i] w ∈ D) →
      E^[j] (w + (k : ℂ)) = E^[j] w + (k : ℂ) := by
  intro j
  induction j with
  | zero => intro k w _; simp
  | succ n ih =>
      intro k w hw
      have h0 : w ∈ D := hw 0 (Nat.succ_pos n)
      have hshift : E (w + (k : ℂ)) = E w + (k : ℂ) := chainPre_equiv_add_int h k h0
      have h1 : E^[n] (E w + (k : ℂ)) = E^[n] (E w) + (k : ℂ) := by
        refine ih k (fun i hi => ?_)
        have hii : E^[i] (E w) = E^[i + 1] w := (Function.iterate_succ_apply E i w).symm
        rw [hii]
        exact hw (i + 1) (by omega)
      simp only [Function.iterate_succ_apply]
      rw [hshift]
      exact h1

/-! ## The chain version -/

/-- `ĥ^[i]` maps `W j` into `W (j - i)`. -/
lemma chainPre_iterate_mem {R : ℂ → ℂ} {β : ℂ} {DR : Set ℂ} {ζa ζb : ℂ} {ρ sgn C₀ C₁ C₁' : ℝ}
    {W : ℕ → Set ℂ} (h : Work.L62.IsChain R β DR ζa ζb ρ sgn C₀ C₁ C₁' W) :
    ∀ {j i : ℕ}, i ≤ j → ∀ {w : ℂ}, w ∈ W j → (fun u => R u - β)^[i] w ∈ W (j - i) := by
  intro j i
  induction i with
  | zero => intro _ w hw; simpa using hw
  | succ n ih =>
      intro hn w hw
      have hnj : n ≤ j := le_trans (Nat.le_succ n) hn
      have hmem := ih hnj hw
      have himg := (h.chain (j - n - 1)).2.2
      have hidx : j - n - 1 + 1 = j - n := by omega
      rw [hidx] at himg
      have h2 : (fun u => R u - β) ((fun u => R u - β)^[n] w) ∈ W (j - n - 1) := by
        rw [← himg]
        exact mem_image_of_mem _ hmem
      show (fun u => R u - β)^[n + 1] w ∈ W (j - (n + 1))
      rw [Function.iterate_succ_apply']
      rw [show j - (n + 1) = j - n - 1 by omega]
      exact h2

/-- **Preimages along the chain, shifted by an integer.**  For every `u' ∈ W 0` and every `k : ℤ`
there is exactly one `u ∈ W j + k` whose image under `ĥ^[j]` is `u' + k`. -/
theorem chain_preimage_mem
    {R : ℂ → ℂ} {β : ℂ} {DR : Set ℂ} {ζa ζb : ℂ} {ρ sgn C₀ C₁ C₁' : ℝ} {W : ℕ → Set ℂ}
    (h : Work.L62.IsChain R β DR ζa ζb ρ sgn C₀ C₁ C₁' W)
    (hReq : MandelDim.IsTEquivariantOn R DR) {j : ℕ} {k : ℤ} {u' : ℂ} (hu' : u' ∈ W 0) :
    ∃! u : ℂ, u ∈ (fun w : ℂ => w + ((k : ℤ) : ℂ)) '' W j ∧
      (fun w => R w - β)^[j] u = u' + ((k : ℤ) : ℂ) := by
  have hTeq : IsTEquivariantOn (fun w => R w - β) DR := Work.L62.isTEquivariantOn_sub hReq
  -- an unshifted preimage in `W j`, unique by injectivity of `ĥ^[j]`
  obtain ⟨w₀, hw₀W, hw₀eq⟩ : ∃ w ∈ W j, (fun w => R w - β)^[j] w = u' := by
    have hmem : u' ∈ (fun w => R w - β)^[j] '' W j := by
      rw [h.image_iterate j]; exact hu'
    obtain ⟨w, hw, he⟩ := hmem
    exact ⟨w, hw, he⟩
  have hiter₀ : ∀ i < j, (fun u => R u - β)^[i] w₀ ∈ DR := by
    intro i hi
    exact h.W_subset_DR (j := j - i) (by omega) (chainPre_iterate_mem h (le_of_lt hi) hw₀W)
  refine ⟨w₀ + (k : ℂ), ⟨mem_image_of_mem _ hw₀W, ?_⟩, ?_⟩
  · rw [chainPre_iterate_add_int hTeq j k hiter₀, hw₀eq]
  · rintro v ⟨hvW, hveq⟩
    obtain ⟨w₁, hw₁W, hvk⟩ := hvW
    have hvk' : w₁ + (k : ℂ) = v := hvk
    have hiter₁ : ∀ i < j, (fun u => R u - β)^[i] w₁ ∈ DR := by
      intro i hi
      exact h.W_subset_DR (j := j - i) (by omega) (chainPre_iterate_mem h (le_of_lt hi) hw₁W)
    have hsplit := chainPre_iterate_add_int hTeq j k hiter₁
    have hpre : (fun u => R u - β)^[j] w₁ = u' := by
      have h2 : (fun u => R u - β)^[j] w₁ + (k : ℂ) = u' + (k : ℂ) := by
        rw [← hsplit, hvk']
        exact hveq
      exact add_right_cancel h2
    have hw : w₁ = w₀ := h.injOn_iterate j hw₁W hw₀W (by rw [hpre, hw₀eq])
    rw [← hvk', hw]

end

end Work.Repel
