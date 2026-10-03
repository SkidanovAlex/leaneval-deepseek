import Mathlib
import Submission.Work.L62.chain
import Submission.Work.Interfaces.Parabolic

/-!
# REPEL: walking along the chain `W ·` with a shifted return map

Let `h : Work.L62.IsChain R β DR ζa ζb ρ sgn C₀ C₁ C₁' W` be a backward chain of discs for the
lifted map `ĥ = R - β`: `ĥ` sends `W (j+1)` bijectively onto `W j`, `W (j+1) ⊆ DR`, and `DR` is
`T`-invariant with `R` `T`-equivariant on it.

Suppose `R₁` is another lifted `T`-equivariant map on `DR₁ ⊇ DR` which differs from `ĥ` by an
integer translation, `R₁ w = ĥ w - c` with `c : ℕ` (`hc`, in the form `R w - β = R₁ w + c`).
Then the two orbits of any `T`-translate `u = w + k` of a point `w ∈ W j` agree, up to the
running translation `i ↦ i·c`, for as long as the walk stays on the chain:

`R₁^[i] u = ĥ^[i] u - i·c`  for `i ≤ j`,  and `R₁^[i] u ∈ DR₁` for `i < j`.

The point of `i < j` (strictly) in the membership statement is that `W j` for `j ≥ 1` lies in `DR`
(`IsChain.W_subset_DR`) while `W 0` need not; after `j` steps of the walk the orbit reaches
`W 0 + ℤ`, where nothing is guaranteed.

The substance is that `R` commutes with *integer* translations (`E_add_int`), so the shift by `c`
(`ℤ`-valued) can be moved outside the iterate — the reason `c` is a natural number is irrelevant,
only that the translation is integral.
-/

namespace Work.Repel

open Set

noncomputable section

/-! ## Integer translation of `ĥ = R - β` -/

/-- `T`-equivariance of `R` on the `T`-invariant set `DR`, iterated over an integer shift: for
`w ∈ DR` and `k : ℤ`, `ĥ (w + k) = ĥ w + k` (and `w + k ∈ DR`). -/
lemma sub_beta_add_int {R : ℂ → ℂ} {β : ℂ} {DR : Set ℂ}
    (hReq : MandelDim.IsTEquivariantOn R DR) {w : ℂ} (hw : w ∈ DR) (k : ℤ) :
    (fun u => R u - β) (w + ((k : ℤ) : ℂ)) = (fun u => R u - β) w + ((k : ℤ) : ℂ) := by
  have h := Work.Horn.MandelDim.E_add_int hReq.1 (fun z hz _ => hReq.2 z hz) hw k
  show R (w + (k : ℂ)) - β = R w - β + (k : ℂ)
  rw [h]
  ring

/-- The negative natural shift version of `sub_beta_add_int`. -/
lemma sub_beta_sub_nat {R : ℂ → ℂ} {β : ℂ} {DR : Set ℂ}
    (hReq : MandelDim.IsTEquivariantOn R DR) {w : ℂ} (hw : w ∈ DR) (m : ℕ) :
    (fun u => R u - β) (w - ((m : ℕ) : ℂ)) = (fun u => R u - β) w - ((m : ℕ) : ℂ) := by
  have h := Work.Horn.MandelDim.E_sub_nat hReq.1 (fun z hz _ => hReq.2 z hz) hw m
  show R (w - (m : ℂ)) - β = R w - β - (m : ℂ)
  rw [h]
  ring

/-! ## Walking down the chain -/

/-- Walking down the chain: `ĥ^[i]` maps `W j` into `W (j - i)`. -/
lemma chain_walk_mem {R : ℂ → ℂ} {β : ℂ} {DR : Set ℂ} {ζa ζb : ℂ} {ρ sgn C₀ C₁ C₁' : ℝ}
    {W : ℕ → Set ℂ} (h : Work.L62.IsChain R β DR ζa ζb ρ sgn C₀ C₁ C₁' W)
    {j : ℕ} {w : ℂ} (hw : w ∈ W j) :
    ∀ i, i ≤ j → (fun u => R u - β)^[i] w ∈ W (j - i) := by
  intro i
  induction i with
  | zero => intro _; simpa using hw
  | succ n ih =>
      intro hn
      have hn' : n ≤ j := le_trans (Nat.le_succ n) hn
      have hmem : (fun u => R u - β)^[n] w ∈ W (j - n) := ih hn'
      have hstep : (fun u => R u - β) '' W (j - n) = W (j - n - 1) := by
        have h0 := (h.chain (j - n - 1)).2.2
        rwa [show j - n - 1 + 1 = j - n by omega] at h0
      rw [Function.iterate_succ_apply']
      rw [show j - (n + 1) = j - n - 1 by omega, ← hstep]
      exact Set.mem_image_of_mem _ hmem

/-- `ĥ^[i]` commutes with an integer translation, for `i ≤ j` steps along the chain. -/
lemma chain_walk_add_int {R : ℂ → ℂ} {β : ℂ} {DR : Set ℂ} {ζa ζb : ℂ} {ρ sgn C₀ C₁ C₁' : ℝ}
    {W : ℕ → Set ℂ} (h : Work.L62.IsChain R β DR ζa ζb ρ sgn C₀ C₁ C₁' W)
    (hReq : MandelDim.IsTEquivariantOn R DR) {j : ℕ} {k : ℤ} {w : ℂ} (hw : w ∈ W j) :
    ∀ i, i ≤ j → (fun u => R u - β)^[i] (w + ((k : ℤ) : ℂ))
      = (fun u => R u - β)^[i] w + ((k : ℤ) : ℂ) := by
  intro i
  induction i with
  | zero => intro _; simp
  | succ n ih =>
      intro hn
      have hn' : n ≤ j := le_trans (Nat.le_succ n) hn
      have hn1 : 1 ≤ j - n := by omega
      have hmemW : (fun u => R u - β)^[n] w ∈ W (j - n) := chain_walk_mem h hw n hn'
      have hmem : (fun u => R u - β)^[n] w ∈ DR := h.W_subset_DR hn1 hmemW
      rw [Function.iterate_succ_apply', Function.iterate_succ_apply', ih hn']
      exact sub_beta_add_int hReq hmem k

/-! ## The main statement -/

theorem walk_of_sub
    {R : ℂ → ℂ} {β : ℂ} {DR : Set ℂ} {ζa ζb : ℂ} {ρ sgn C₀ C₁ C₁' : ℝ} {W : ℕ → Set ℂ}
    (h : Work.L62.IsChain R β DR ζa ζb ρ sgn C₀ C₁ C₁' W)
    (hReq : MandelDim.IsTEquivariantOn R DR)
    {R₁ : ℂ → ℂ} {DR₁ : Set ℂ} (h₁ : MandelDim.IsTEquivariantOn R₁ DR₁)
    (hsub : DR ⊆ DR₁) {c : ℕ} (hc : ∀ w, R w - β = R₁ w + ((c : ℕ) : ℂ))
    {j : ℕ} {k : ℤ} {u : ℂ} (hu : u ∈ (fun w : ℂ => w + ((k : ℤ) : ℂ)) '' W j) :
    (∀ i < j, R₁^[i] u ∈ DR₁) ∧
      ∀ i ≤ j, R₁^[i] u = (fun w => R w - β)^[i] u - ((i * c : ℕ) : ℂ) := by
  obtain ⟨w₀, hw₀W, hw₀u⟩ := hu
  have hu' : u = w₀ + ((k : ℤ) : ℂ) := hw₀u.symm
  have hwalk : ∀ i ≤ j, (fun w => R w - β)^[i] u
      = (fun w => R w - β)^[i] w₀ + ((k : ℤ) : ℂ) := by
    intro i hi
    rw [hu']
    exact chain_walk_add_int h hReq hw₀W i hi
  have hc' : ∀ x : ℂ, R₁ x = (fun w => R w - β) x - ((c : ℕ) : ℂ) := by
    intro x
    have h0 := hc x
    change R₁ x = R x - β - (c : ℂ)
    rw [h0]
    ring
  have hmain : ∀ i ≤ j, R₁^[i] u = (fun w => R w - β)^[i] u - ((i * c : ℕ) : ℂ) := by
    intro i hi
    induction i with
    | zero => simp
    | succ n ih =>
        have hn : n ≤ j := le_trans (Nat.le_succ n) hi
        have hn1 : 1 ≤ j - n := by omega
        have hmemW : (fun w => R w - β)^[n] w₀ ∈ W (j - n) := chain_walk_mem h hw₀W n hn
        have hmemDR : (fun w => R w - β)^[n] w₀ ∈ DR := h.W_subset_DR hn1 hmemW
        have hDR : (fun w => R w - β)^[n] u ∈ DR := by
          rw [hwalk n hn]
          exact Work.Horn.MandelDim.IsTInvariant.add_int hReq.1 hmemDR k
        rw [Function.iterate_succ_apply', ih hn, hc']
        rw [Function.iterate_succ_apply']
        rw [sub_beta_sub_nat hReq hDR (n * c)]
        push_cast
        ring
  constructor
  · intro i hi
    have hi' : i ≤ j := le_of_lt hi
    have hj1 : 1 ≤ j - i := by omega
    have hmemW : (fun w => R w - β)^[i] w₀ ∈ W (j - i) := chain_walk_mem h hw₀W i hi'
    have hmemDR : (fun w => R w - β)^[i] w₀ ∈ DR := h.W_subset_DR hj1 hmemW
    have hmemDR₁ : (fun w => R w - β)^[i] w₀ ∈ DR₁ := hsub hmemDR
    have hthis : R₁^[i] u
        = (fun w => R w - β)^[i] w₀ + (((k - (((i * c : ℕ)) : ℤ)) : ℤ) : ℂ) := by
      rw [hmain i hi', hwalk i hi']
      push_cast
      ring
    rw [hthis]
    exact Work.Horn.MandelDim.IsTInvariant.add_int h₁.1 hmemDR₁ (k - (((i * c : ℕ)) : ℤ))
  · exact hmain

end

end Work.Repel
