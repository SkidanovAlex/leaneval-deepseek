import Mathlib
import Submission.Work.Peluse.Ulower.thetaDefs
import Submission.Work.Peluse.Ulower.StepLe.blindConvertK_lowrank

/-!
# `fibrePairs`: the fibre bookkeeping of the blind conversion step

This is step 7 of `Work.Peluse.Ulower.StepLe.blindConvertK` (see
`NOTES_blindConvertK_SESSION.md`): a dense set `H₂` of triples `(u,h,v)` on which the Gowers
transform `gowersDiff β h u v` takes the *pinned* value `v₀` is compressed to a set `P` of
*shift pairs* `(u,v)` with a frozen third component `hfr u`, at the cost of a factor `D^σ`.

The proof is a fibre count.  For each `u ∈ [1,D]^σ` choose `hfr u` maximising the number of
`v`'s with `(u, hfr u, v) ∈ H₂`; then every `u`-fibre of `H₂` is at most `D^σ` times this fibre,
and the pairs `(u,v)` with `(u,hfr u,v) ∈ H₂` lie in `H₁` (they are the `ω = false` corner of a
triple of `□_σ(H₁)`) and satisfy the pinning.
-/

namespace Work.Peluse.Ulower.StepLe

open scoped BigOperators

/-- The `ω = false` corner of a triple of Peluse's `□_σ(H)` is its last pair: membership in
`ThetaSet σ D H` gives `(k.1, k.2.2) ∈ H`. -/
private lemma mem_ThetaSet_snd {σ D : ℕ} {H : Finset ((Fin σ → ℤ) × (Fin σ → ℤ))}
    {k : (Fin σ → ℤ) × (Fin σ → ℤ) × (Fin σ → ℤ)}
    (hk : k ∈ Work.Peluse.Ulower.ThetaSet σ D H) : (k.1, k.2.2) ∈ H := by
  have h := (Finset.mem_filter.mp hk).2 (fun _ : Fin σ => false)
  have hlam : (fun i : Fin σ =>
      if (fun _ : Fin σ => false) i then k.2.1 i else k.2.2 i) = k.2.2 := by
    funext i; simp
  rwa [hlam] at h

/-- A triple of Peluse's `□_σ(H)` lies in `[1,D]^σ × ([1,D]^σ × [1,D]^σ)`. -/
private lemma mem_ThetaSet_prod {σ D : ℕ} {H : Finset ((Fin σ → ℤ) × (Fin σ → ℤ))}
    {k : (Fin σ → ℤ) × (Fin σ → ℤ) × (Fin σ → ℤ)}
    (hk : k ∈ Work.Peluse.Ulower.ThetaSet σ D H) :
    k ∈ Work.Peluse.Ulower.thetaBox σ D ×ˢ
      (Work.Peluse.Ulower.thetaBox σ D ×ˢ Work.Peluse.Ulower.thetaBox σ D) :=
  (Finset.mem_filter.mp hk).1

/-- **Fibre bookkeeping for the pinned Gowers triples.**  If `H₂ ⊆ □_σ(H₁)` and the Gowers
transform of `β` is pinned to the value `v₀` on all of `H₂`, then there are a frozen shift
`hfr` (depending only on the *first* component) and a set of shift pairs `P ⊆ H₁` such that
`|H₂| ≤ D^σ |P|` and every pair of `P` is pinned at the frozen shift. -/
theorem fibrePairs {σ D : ℕ} (hD : 1 ≤ D) {β : (Fin σ → ℤ) → (Fin σ → ℤ) → ℝ} {v₀ : ℝ}
    {H₁ : Finset ((Fin σ → ℤ) × (Fin σ → ℤ))}
    {H₂ : Finset ((Fin σ → ℤ) × (Fin σ → ℤ) × (Fin σ → ℤ))}
    (hsub : H₂ ⊆ Work.Peluse.Ulower.ThetaSet σ D H₁)
    (hpin : ∀ k ∈ H₂, Work.Peluse.Ulower.StepLe.gowersDiff β k.2.1 k.1 k.2.2 = v₀) :
    ∃ (hfr : (Fin σ → ℤ) → Fin σ → ℤ)
      (P : Finset ((Fin σ → ℤ) × (Fin σ → ℤ))),
      P ⊆ H₁ ∧ (H₂.card : ℝ) ≤ (D : ℝ) ^ σ * (P.card : ℝ) ∧
      ∀ p ∈ P, Work.Peluse.Ulower.StepLe.gowersDiff β (hfr p.1) p.1 p.2 = v₀ := by
  classical
  let Box : Finset (Fin σ → ℤ) := Work.Peluse.Ulower.thetaBox σ D
  have hDZ : (1 : ℤ) ≤ (D : ℤ) := by exact_mod_cast hD
  have hBoxne : Box.Nonempty := by
    refine ⟨fun _ => 1, ?_⟩
    show (fun _ : Fin σ => 1) ∈ Work.Peluse.Ulower.thetaBox σ D
    rw [Work.Peluse.Ulower.mem_thetaBox]
    intro i
    exact Finset.mem_Icc.mpr ⟨le_rfl, hDZ⟩
  have hboxes : Box.card = D ^ σ := Work.Peluse.Ulower.thetaBox_card σ D
  -- the number of `v`'s in the `u`-fibre of `H₂` over `k2`
  let N : (Fin σ → ℤ) → (Fin σ → ℤ) → ℕ :=
    fun u k2 => ∑ k3 ∈ Box, if (u, k2, k3) ∈ H₂ then 1 else 0
  have hN : ∀ u k2, N u k2 = ∑ k3 ∈ Box, if (u, k2, k3) ∈ H₂ then 1 else 0 :=
    fun u k2 => rfl
  -- choose, for each `u`, the first component that maximises the fibre
  have hex : ∀ u : Fin σ → ℤ, ∃ b ∈ Box, ∀ b' ∈ Box, N u b' ≤ N u b :=
    fun u => Finset.exists_max_image Box (N u) hBoxne
  let hfr : (Fin σ → ℤ) → Fin σ → ℤ := fun u => (hex u).choose
  have hfrmax : ∀ u b', b' ∈ Box → N u b' ≤ N u (hfr u) :=
    fun u b' hb => (hex u).choose_spec.2 b' hb
  let P : Finset ((Fin σ → ℤ) × (Fin σ → ℤ)) :=
    (Box ×ˢ Box).filter (fun p => (p.1, hfr p.1, p.2) ∈ H₂)
  have hPmem : ∀ p, p ∈ P ↔ p ∈ Box ×ˢ Box ∧ (p.1, hfr p.1, p.2) ∈ H₂ :=
    fun p => Finset.mem_filter
  refine ⟨hfr, P, ?_, ?_, ?_⟩
  · -- `P ⊆ H₁`
    intro p hp
    exact mem_ThetaSet_snd (hsub ((hPmem p).mp hp).2)
  · -- the fibre count
    have hsub_prod : H₂ ⊆ Box ×ˢ (Box ×ˢ Box) := by
      intro k hk
      have h1 : k ∈ Work.Peluse.Ulower.thetaBox σ D ×ˢ
          (Work.Peluse.Ulower.thetaBox σ D ×ˢ Work.Peluse.Ulower.thetaBox σ D) :=
        mem_ThetaSet_prod (hsub hk)
      exact h1
    have hH2sum : H₂.card = ∑ u ∈ Box, ∑ k2 ∈ Box, N u k2 := by
      have hEq : H₂ = (Box ×ˢ (Box ×ˢ Box)).filter (fun a => a ∈ H₂) := by
        rw [Finset.filter_mem_eq_inter, Finset.inter_eq_right.mpr hsub_prod]
      rw [hEq, Finset.card_filter]
      simp only [Finset.sum_product]
      refine Finset.sum_congr rfl (fun u _ => Finset.sum_congr rfl (fun k2 _ => ?_))
      rw [hN]
    have hstep1 : ∑ u ∈ Box, ∑ k2 ∈ Box, N u k2 ≤ ∑ u ∈ Box, ∑ k2 ∈ Box, N u (hfr u) :=
      Finset.sum_le_sum (fun u _ => Finset.sum_le_sum (fun k2 hk2 => hfrmax u k2 hk2))
    have hstep2 : ∑ u ∈ Box, ∑ k2 ∈ Box, N u (hfr u) = ∑ u ∈ Box, Box.card * N u (hfr u) := by
      refine Finset.sum_congr rfl (fun u _ => ?_)
      rw [Finset.sum_const, smul_eq_mul]
    have hstep3 : ∑ u ∈ Box, Box.card * N u (hfr u) = Box.card * ∑ u ∈ Box, N u (hfr u) := by
      rw [Finset.mul_sum]
    have hPsum : P.card = ∑ u ∈ Box, N u (hfr u) := by
      show ((Box ×ˢ Box).filter (fun p => (p.1, hfr p.1, p.2) ∈ H₂)).card = _
      rw [Finset.card_filter, Finset.sum_product]
    have hnat : H₂.card ≤ D ^ σ * P.card := by
      calc H₂.card = ∑ u ∈ Box, ∑ k2 ∈ Box, N u k2 := hH2sum
        _ ≤ ∑ u ∈ Box, ∑ k2 ∈ Box, N u (hfr u) := hstep1
        _ = ∑ u ∈ Box, Box.card * N u (hfr u) := hstep2
        _ = Box.card * ∑ u ∈ Box, N u (hfr u) := hstep3
        _ = Box.card * P.card := by rw [hPsum]
        _ = D ^ σ * P.card := by rw [hboxes]
    exact_mod_cast hnat
  · -- the pinning on `P`
    intro p hp
    exact hpin _ ((hPmem p).mp hp).2

end Work.Peluse.Ulower.StepLe
