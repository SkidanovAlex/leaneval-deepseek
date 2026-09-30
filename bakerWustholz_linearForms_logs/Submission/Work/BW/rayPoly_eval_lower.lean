import Mathlib
import Submission.Work.BW.DefsMult
import Submission.Work.BW.subgroup_rayDegAux
import Submission.Work.BW.boxClass_lower

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

open scoped BigOperators

namespace Work.BW

/-- Arithmetic core of `rayPoly_eval_lower`: if `D ≥ 1` coordinatewise, `C ≥ 0`, `J` is a
`ρ`-element subset of `Fin N` (so `ρ ≤ N` and `|Jᶜ| = N - ρ`) and `t ≥ 1`, then
`(t·D₀+1)^{[ε]} · C · ∏_{i∉J}(t·D_{i+1}+1)` dominates
`C · D₀^{[ε]} · ∏_{i∉J} D_{i+1} · t^{N+1-([ε=false]+ρ)}`.

Indeed `t·D₀+1 ≥ t·D₀` (when `ε`) and `∏_{i∉J}(t·D_{i+1}+1) ≥ ∏_{i∉J}(t·D_{i+1}) =
t^{N-ρ}·∏_{i∉J}D_{i+1}`, and `[ε] + (N-ρ) = N+1-([ε=false]+ρ)`. -/
lemma lower_arith_aux {N ρ : ℕ} (D : Fin (N + 1) →₀ ℕ) (hD : ∀ i, 1 ≤ D i) (ε : Bool)
    (C : ℚ) (hC : 0 ≤ C) (J : Finset (Fin N)) (hJ : J.card = ρ) (t : ℕ) (ht : 1 ≤ t) :
    (C * (if ε then (D 0 : ℚ) else 1) * ∏ i ∈ Jᶜ, (D i.succ : ℚ)) *
        (t : ℚ) ^ (N + 1 - ((if ε then 0 else 1) + ρ))
      ≤ (if ε then (t : ℚ) * (D 0 : ℚ) + 1 else 1) *
          (C * ∏ i ∈ Jᶜ, ((t : ℚ) * (D i.succ : ℚ) + 1)) := by
  have hcard : Jᶜ.card = N - ρ := by rw [Finset.card_compl, Fintype.card_fin, hJ]
  obtain hρN : ρ ≤ N := by
    have h := Finset.card_le_univ J
    simp only [Fintype.card_fin] at h
    omega
  have hPnn : (0 : ℚ) ≤ ∏ i ∈ Jᶜ, (D i.succ : ℚ) :=
    Finset.prod_nonneg (fun i _ => Nat.cast_nonneg _)
  have hprod : (t : ℚ) ^ (N - ρ) * (∏ i ∈ Jᶜ, (D i.succ : ℚ))
      ≤ ∏ i ∈ Jᶜ, ((t : ℚ) * (D i.succ : ℚ) + 1) := by
    rw [← hcard]
    calc (t : ℚ) ^ (Jᶜ.card) * (∏ i ∈ Jᶜ, (D i.succ : ℚ))
        = ∏ i ∈ Jᶜ, ((t : ℚ) * (D i.succ : ℚ)) := by
          rw [Finset.prod_mul_distrib, Finset.prod_const]
      _ ≤ ∏ i ∈ Jᶜ, ((t : ℚ) * (D i.succ : ℚ) + 1) := by
          refine Finset.prod_le_prod₀ (fun i _ => ?_) (fun i _ => ?_)
          · exact mul_nonneg (Nat.cast_nonneg t) (Nat.cast_nonneg _)
          · linarith
  cases ε with
  | false =>
    show (C * 1 * ∏ i ∈ Jᶜ, (D i.succ : ℚ)) * (t : ℚ) ^ (N + 1 - (1 + ρ))
      ≤ 1 * (C * ∏ i ∈ Jᶜ, ((t : ℚ) * (D i.succ : ℚ) + 1))
    have hexp : N + 1 - (1 + ρ) = N - ρ := by omega
    rw [hexp]
    calc (C * 1 * ∏ i ∈ Jᶜ, (D i.succ : ℚ)) * (t : ℚ) ^ (N - ρ)
        = C * ((t : ℚ) ^ (N - ρ) * ∏ i ∈ Jᶜ, (D i.succ : ℚ)) := by ring
      _ ≤ C * (∏ i ∈ Jᶜ, ((t : ℚ) * (D i.succ : ℚ) + 1)) :=
          mul_le_mul_of_nonneg_left hprod hC
      _ = 1 * (C * ∏ i ∈ Jᶜ, ((t : ℚ) * (D i.succ : ℚ) + 1)) := by ring
  | true =>
    show (C * (D 0 : ℚ) * ∏ i ∈ Jᶜ, (D i.succ : ℚ)) * (t : ℚ) ^ (N + 1 - (0 + ρ))
      ≤ ((t : ℚ) * (D 0 : ℚ) + 1) * (C * ∏ i ∈ Jᶜ, ((t : ℚ) * (D i.succ : ℚ) + 1))
    have hexp : N + 1 - (0 + ρ) = (N - ρ) + 1 := by omega
    rw [hexp, pow_succ]
    have h1 : (t : ℚ) * (D 0 : ℚ) ≤ (t : ℚ) * (D 0 : ℚ) + 1 := by linarith
    have h2 : C * ((t : ℚ) ^ (N - ρ) * (∏ i ∈ Jᶜ, (D i.succ : ℚ)))
        ≤ C * (∏ i ∈ Jᶜ, ((t : ℚ) * (D i.succ : ℚ) + 1)) :=
          mul_le_mul_of_nonneg_left hprod hC
    have h3 : (0 : ℚ) ≤ C * ((t : ℚ) ^ (N - ρ) * (∏ i ∈ Jᶜ, (D i.succ : ℚ))) :=
      mul_nonneg hC (mul_nonneg (pow_nonneg (Nat.cast_nonneg t) _) hPnn)
    have h4 : (0 : ℚ) ≤ (t : ℚ) * (D 0 : ℚ) + 1 := by positivity
    calc (C * (D 0 : ℚ) * (∏ i ∈ Jᶜ, (D i.succ : ℚ))) * ((t : ℚ) ^ (N - ρ) * (t : ℚ))
        = ((t : ℚ) * (D 0 : ℚ)) *
            (C * ((t : ℚ) ^ (N - ρ) * (∏ i ∈ Jᶜ, (D i.succ : ℚ)))) := by ring
      _ ≤ ((t : ℚ) * (D 0 : ℚ) + 1) * (C * (∏ i ∈ Jᶜ, ((t : ℚ) * (D i.succ : ℚ) + 1))) :=
          mul_le_mul h1 h2 h3 h4

/-- Lower bound for the ray Hilbert polynomial of `subIdeal N ρ ε M`: if the ray Hilbert function is `(t·D₀+1)^ε` times the box class count (`hcount`), `q` is the ray Hilbert polynomial, and `J` is a non-singular `ρ`-set of columns (`minorJ M J hJ ≠ 0`), then eventually `q(t) ≥ c_J·t^{N+1-k}` with `c_J = |Δ_J|·D₀^ε·∏_{i∉J} D_{i+1}`, `k = [ε = false] + ρ`.

Route: for `t ≥ max T₀ |Δ_J|` combine `hcount` with the proven `Submission.Work.BW.boxClass_lower` (its size hypothesis `|Δ_J| ≤ m i + 1` holds because `m i = t·D_{i+1}` and `D_{i+1} ≥ 1`), and use `t·D + 1 ≥ t·D`. -/
theorem rayPoly_eval_lower {N ρ : ℕ} (D : Fin (N + 1) →₀ ℕ) (hD : ∀ i, 1 ≤ D i) (ε : Bool)
    (M : Fin ρ → Fin N → ℤ) (hM : PrimSys M) {q : Polynomial ℚ}
    (hcount : ∀ t : ℕ, rayHilb N D (subIdeal N ρ ε M) t =
      (if ε then t * D 0 + 1 else 1) * boxClassCount N ρ M (fun i => t * D i.succ))
    (hq : IsRayPoly N D (subIdeal N ρ ε M) q)
    (J : Finset (Fin N)) (hJ : J.card = ρ) (hΔ : minorJ M J hJ ≠ 0) :
    ∃ T : ℕ, ∀ t : ℕ, T ≤ t →
      (|(minorJ M J hJ : ℚ)| * (if ε then (D 0 : ℚ) else 1) * ∏ i ∈ Jᶜ, (D i.succ : ℚ)) *
        (t : ℚ) ^ (N + 1 - ((if ε then 0 else 1) + ρ)) ≤ q.eval (t : ℚ) := by
  unfold IsRayPoly at hq
  obtain ⟨T₀, hT₀⟩ := Filter.eventually_atTop.mp hq
  -- `t` large enough to (i) be in the eventual range of `q` and (ii) satisfy the size
  -- hypothesis of `boxClass_lower`, namely `|Δ_J| ≤ t·D_j + 1` for `j ∈ J`.
  refine ⟨max T₀ (max 1 (minorJ M J hJ).natAbs), fun t ht => ?_⟩
  have ht₀ : T₀ ≤ t := le_trans (le_max_left _ _) ht
  have ht₁ : 1 ≤ t := le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) ht
  have htd : (minorJ M J hJ).natAbs ≤ t :=
    le_trans (le_trans (le_max_right _ _) (le_max_right _ _)) ht
  have hbig : ∀ j ∈ J, (minorJ M J hJ).natAbs ≤ (fun i => t * D i.succ) j + 1 := by
    intro j _
    have h1 : t ≤ t * D j.succ :=
      Nat.le_mul_of_pos_right t (by have := hD j.succ; omega)
    show (minorJ M J hJ).natAbs ≤ t * D j.succ + 1
    omega
  have hlow := boxClass_lower M (fun i => t * D i.succ) J hJ hbig
  -- rewrite both `if ε` factors and the product of `Nat`-casts into the `ℚ`-shape
  have hif : (if ε then (t : ℚ) * (D 0 : ℚ) + 1 else 1)
      = ((if ε then t * D 0 + 1 else 1 : ℕ) : ℚ) := by
    cases ε <;> simp
  have hpr : (∏ i ∈ Jᶜ, ((t : ℚ) * (D i.succ : ℚ) + 1))
      = ∏ i ∈ Jᶜ, (((t * D i.succ : ℕ) : ℚ) + 1) := by
    refine Finset.prod_congr rfl (fun i _ => ?_)
    push_cast
    ring
  calc (|(minorJ M J hJ : ℚ)| * (if ε then (D 0 : ℚ) else 1) * ∏ i ∈ Jᶜ, (D i.succ : ℚ)) *
        (t : ℚ) ^ (N + 1 - ((if ε then 0 else 1) + ρ))
      ≤ (if ε then (t : ℚ) * (D 0 : ℚ) + 1 else 1) *
          (|(minorJ M J hJ : ℚ)| * ∏ i ∈ Jᶜ, ((t : ℚ) * (D i.succ : ℚ) + 1)) :=
        lower_arith_aux D hD ε _ (abs_nonneg _) J hJ t ht₁
    _ = ((if ε then t * D 0 + 1 else 1 : ℕ) : ℚ) *
          (|(minorJ M J hJ : ℚ)| * ∏ i ∈ Jᶜ, (((t * D i.succ : ℕ) : ℚ) + 1)) := by
        rw [hif, hpr]
    _ ≤ ((if ε then t * D 0 + 1 else 1 : ℕ) : ℚ) *
          (boxClassCount N ρ M (fun i => t * D i.succ) : ℚ) :=
        mul_le_mul_of_nonneg_left hlow (Nat.cast_nonneg _)
    _ = (rayHilb N D (subIdeal N ρ ε M) t : ℚ) := by
        rw [hcount t, Nat.cast_mul]
    _ = q.eval (t : ℚ) := hT₀ t ht₀

end Work.BW
