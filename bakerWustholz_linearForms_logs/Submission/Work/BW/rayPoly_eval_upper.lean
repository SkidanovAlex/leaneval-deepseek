import Mathlib
import Submission.Work.BW.DefsMult
import Submission.Work.BW.subgroup_rayDegAux
import Submission.Work.BW.boxClass_upper

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

namespace Work.BW

/-!
# Upper bound for the ray Hilbert polynomial

`rayPoly_eval_upper`: writing `k = [ε = false] + ρ` for the codimension of the subgroup
`G' = 0 × ker 𝒵` resp. `G_a × ker 𝒵` in `G_a × G_m^N`, the ray Hilbert polynomial `q` of the
closure of `G'` satisfies `q(t) ≤ C·t^{N+1-k}` for all `t ≥ 1`.

The proof has two halves.

* For `t ≥ max T₀ 1` (where `T₀` is where `q` starts computing the ray Hilbert function), the
  hypothesis `hcount` expresses `rayHilb` through the number of classes of the ray box, which
  grows at most linearly by `boxClass_upper`.  The factor `t·D₀+1` contributes at most one extra
  power of `t` in the `ε = true` case.
* The finitely many `t < max T₀ 1` are absorbed into the constant, since `t^n ≥ 1` for `t ≥ 1`.
-/

/-- Absorbing the finitely many values below a threshold: if `g t ≤ C₀·t^e` for `t ≥ T` (with
`1 ≤ T`), then `g t ≤ C·t^e` for **all** `t ≥ 1`, the finitely many `t < T` contributing to `C`.
Only `t^e ≥ 1` for `t ≥ 1` is used. -/
lemma le_pow_of_forall_le_pow {e : ℕ} (g : ℕ → ℚ) (C₀ : ℚ) {T : ℕ} (hT : 1 ≤ T)
    (hbig : ∀ t : ℕ, T ≤ t → g t ≤ C₀ * (t : ℚ) ^ e) :
    ∃ C : ℚ, ∀ t : ℕ, 1 ≤ t → g t ≤ C * (t : ℚ) ^ e := by
  let S : ℚ := (Finset.range T).sup' ⟨0, Finset.mem_range.mpr (by omega)⟩ g
  refine ⟨max 0 (max C₀ S), ?_⟩
  intro t ht
  rcases lt_or_ge t T with h | h
  · have h1 : g t ≤ S := Finset.le_sup' _ (Finset.mem_range.mpr h)
    have h2 : S ≤ max 0 (max C₀ S) := le_trans (le_max_right _ _) (le_max_right _ _)
    have h3 : (0 : ℚ) ≤ max 0 (max C₀ S) := le_max_left _ _
    have h4 : (1 : ℚ) ≤ (t : ℚ) ^ e := one_le_pow₀ (by exact_mod_cast ht)
    calc g t ≤ max 0 (max C₀ S) := le_trans h1 h2
      _ = max 0 (max C₀ S) * 1 := (mul_one _).symm
      _ ≤ max 0 (max C₀ S) * (t : ℚ) ^ e := mul_le_mul_of_nonneg_left h4 h3
  · have h1 := hbig t h
    have h2 : C₀ ≤ max 0 (max C₀ S) := le_trans (le_max_left _ _) (le_max_right _ _)
    calc g t ≤ C₀ * (t : ℚ) ^ e := h1
      _ ≤ max 0 (max C₀ S) * (t : ℚ) ^ e :=
          mul_le_mul_of_nonneg_right h2 (pow_nonneg (Nat.cast_nonneg t) e)

/-- A primitive system `M : Fin ρ → Fin N → ℤ` can only exist for `ρ ≤ N` (its rows are
`ℚ`-linearly independent vectors of `ℚ^N`). -/
lemma card_le_of_primSys {N ρ : ℕ} {M : Fin ρ → Fin N → ℤ} (hM : PrimSys M) : ρ ≤ N := by
  have h1 : Fintype.card (Fin ρ) ≤ Module.finrank ℚ (Fin N → ℚ) :=
    LinearIndependent.fintype_card_le_finrank hM.1
  simpa using h1

/-- Upper bound for the ray Hilbert polynomial of `subIdeal N ρ ε M`: if the ray Hilbert function is `(t·D₀+1)^ε` times the box class count (`hcount`) and `q` is the ray Hilbert polynomial (`IsRayPoly`), then `q(t) ≤ C·t^{N+1-k}` for all `t ≥ 1`, `k = [ε = false] + ρ`.

Route: for `t ≥ max T₀ 1` combine `hcount` with the proven `Submission.Work.BW.boxClass_upper` (linear growth of the class count) and `t·D₀+1 ≤ t·(D₀+1)`; the finitely many `t < T₀` are absorbed into the constant (all summands of `∑_{t<T₀}|q(t)|` are admissible since `t^n ≥ 1`). -/
theorem rayPoly_eval_upper {N ρ : ℕ} (D : Fin (N + 1) →₀ ℕ) (hD : ∀ i, 1 ≤ D i) (ε : Bool)
    (M : Fin ρ → Fin N → ℤ) (hM : PrimSys M) {q : Polynomial ℚ}
    (hcount : ∀ t : ℕ, rayHilb N D (subIdeal N ρ ε M) t =
      (if ε then t * D 0 + 1 else 1) * boxClassCount N ρ M (fun i => t * D i.succ))
    (hq : IsRayPoly N D (subIdeal N ρ ε M) q) :
    ∃ C : ℚ, ∀ t : ℕ, 1 ≤ t →
      q.eval (t : ℚ) ≤ C * (t : ℚ) ^ (N + 1 - ((if ε then 0 else 1) + ρ)) := by
  -- `hD` is not needed for the bound (the box class count grows linearly for any `D`), but it
  -- is part of the statement; keep it referenced.
  have hDle : ∀ i, 1 ≤ D i := hD
  obtain ⟨C', hC'⟩ := boxClass_upper M hM D
  obtain ⟨T₀, hT₀⟩ := Filter.eventually_atTop.mp hq
  have hρN : ρ ≤ N := card_le_of_primSys hM
  cases ε
  · -- `ε = false`: the ray Hilbert function is the box class count itself.
    have hcount₁ : ∀ t : ℕ, rayHilb N D (subIdeal N ρ false M) t =
        1 * boxClassCount N ρ M (fun i => t * D i.succ) := fun t => by simpa using hcount t
    have hexp : N + 1 - (1 + ρ) = N - ρ := by rw [Nat.add_comm 1 ρ, Nat.add_sub_add_right]
    have hbig : ∀ t : ℕ, max T₀ 1 ≤ t →
        q.eval (t : ℚ) ≤ C' * (t : ℚ) ^ (N + 1 - (1 + ρ)) := by
      intro t ht
      have ht1 : 1 ≤ t := le_trans (le_max_right _ _) ht
      have hTt : T₀ ≤ t := le_trans (le_max_left _ _) ht
      have h1 : q.eval (t : ℚ) =
          (boxClassCount N ρ M (fun i => t * D i.succ) : ℚ) := by
        rw [← hT₀ t hTt, hcount₁ t]
        simp
      rw [h1, hexp]
      exact hC' t ht1
    obtain ⟨C, hC⟩ := le_pow_of_forall_le_pow (fun t => q.eval (t : ℚ)) C'
      (le_max_right (T₀ : ℕ) 1) hbig
    exact ⟨C, fun t ht => hC t ht⟩
  · -- `ε = true`: the extra factor `t·D₀+1` contributes one more power of `t`.
    have hcount₂ : ∀ t : ℕ, rayHilb N D (subIdeal N ρ true M) t =
        (t * D 0 + 1) * boxClassCount N ρ M (fun i => t * D i.succ) := fun t => by
      simpa using hcount t
    have hbig : ∀ t : ℕ, max T₀ 1 ≤ t →
        q.eval (t : ℚ) ≤ (C' * ((D 0 : ℚ) + 1)) * (t : ℚ) ^ (N + 1 - (0 + ρ)) := by
      intro t ht
      have ht1 : 1 ≤ t := le_trans (le_max_right _ _) ht
      have hTt : T₀ ≤ t := le_trans (le_max_left _ _) ht
      have hB : (boxClassCount N ρ M (fun i => t * D i.succ) : ℚ) ≤ C' * (t : ℚ) ^ (N - ρ) :=
        hC' t ht1
      have hBnn : (0 : ℚ) ≤ (boxClassCount N ρ M (fun i => t * D i.succ) : ℚ) :=
        Nat.cast_nonneg _
      have h1 : q.eval (t : ℚ) = ((t * D 0 + 1 : ℕ) : ℚ) *
          (boxClassCount N ρ M (fun i => t * D i.succ) : ℚ) := by
        rw [← hT₀ t hTt, hcount₂ t]
        push_cast
        ring
      have hfac : ((t * D 0 + 1 : ℕ) : ℚ) ≤ (t : ℚ) * ((D 0 : ℚ) + 1) := by
        have ht1q : (1 : ℚ) ≤ (t : ℚ) := by exact_mod_cast ht1
        have hcast : ((t * D 0 + 1 : ℕ) : ℚ) = (t : ℚ) * (D 0 : ℚ) + 1 := by
          push_cast
          ring
        rw [hcast, mul_add, mul_one]
        linarith
      have hstep : ((t : ℚ) * ((D 0 : ℚ) + 1)) * (C' * (t : ℚ) ^ (N - ρ)) =
          (C' * ((D 0 : ℚ) + 1)) * (t : ℚ) ^ (N + 1 - (0 + ρ)) := by
        rw [show N + 1 - (0 + ρ) = (N - ρ) + 1 by omega, pow_succ']
        ring
      calc q.eval (t : ℚ) = ((t * D 0 + 1 : ℕ) : ℚ) *
              (boxClassCount N ρ M (fun i => t * D i.succ) : ℚ) := h1
        _ ≤ ((t : ℚ) * ((D 0 : ℚ) + 1)) * (C' * (t : ℚ) ^ (N - ρ)) :=
            mul_le_mul hfac hB hBnn (by positivity)
        _ = (C' * ((D 0 : ℚ) + 1)) * (t : ℚ) ^ (N + 1 - (0 + ρ)) := hstep
    obtain ⟨C, hC⟩ := le_pow_of_forall_le_pow (fun t => q.eval (t : ℚ))
      (C' * ((D 0 : ℚ) + 1)) (le_max_right (T₀ : ℕ) 1) hbig
    exact ⟨C, fun t ht => hC t ht⟩

end Work.BW
