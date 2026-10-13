/-
  WilC4/ClusterER_definable_self : `ClusterER Y B₀` is `∅`-definable when `Y` and `B₀` are.

  This is the **self-contained** version of `WilC4/ClusterER_definable`.  The definability proof
  there is carried out through the witness sets of `WilC4/ClusterSets` + `WilC4/ClusterCoord`,
  which sit in the namespace `Work.WilC4`; in particular `ClusterCoord` declares *public*
  `Work.WilC4.forall_fin1_iff` and `Work.WilC4.exists_fin1_iff`, which are the same public names
  as those declared by `WilC4/monoDefinable_W` and `WilC4/PBRealize`.  Hence no module may import
  both the `ClusterDefs` family and the `mono_real` family — while the consumer of the present
  lemma (`WilC4/ulpm_E_finite`) needs the definability of `ClusterER` *and* `ulpm_mono_param`
  (⟹ `mono_real` ⟹ `monoDefinable_W`).

  Here the same development is reproduced verbatim, but under the fresh namespace
  `Work.WilC4.CESAux` (modules `ClusterSelf/Tool`, `ClusterSelf/Sets`, `ClusterSelf/Coord`), and
  the arithmetic normalisations of `ClusterER_definable` are reproduced in a sub-namespace.  As a
  result importing this module brings in **no** name of `Work.WilC4` other than the theorem
  `ClusterER_definable_self` itself.  The imports are `Mathlib`, `ErealDefs`, the pure-arithmetic
  `ErealArith` lemmas, and `Work.WilC2.Basic` (already in the import closure of `mono_real`).

  The proof is the one of `ClusterER_definable`: build the witness set `Q1 = Spos ∩ (Sdeep ∩ Srat)`
  (membership is the `β`-witness condition), eliminate `x` and then `c`, rewrite `0 < β →` as a
  complement, and quantify `β` universally; the arithmetic normalisations `deep_eq_le`/`quot_eq_le`
  identify the resulting set `ClusterERfam k Y B₀` with `{v : Fin 1 → ℝ | v 0 ∈ ClusterER Y B₀}`.
-/
import Mathlib
import Submission.Work.WilC4.ErealDefs
import Submission.Work.WilC4.ErealArith.deep_eq_le
import Submission.Work.WilC4.ErealArith.quot_eq_le
import Submission.Work.WilC4.ClusterSelf.Coord

set_option autoImplicit false
set_option maxHeartbeats 4000000
noncomputable section

namespace Work.WilC4

open WilkiesDesign WilkiesDesign.CG

namespace CESAux

open Work.WilC4.ErealArith (deep_eq_le quot_eq_le)

variable {k : ℕ}

/-! ## 1. The arithmetic normalisations -/

theorem ratio_iff {β y y' ρ : ℝ} (hβ : β ≠ 0) (hy : y ≠ 0) :
    (∃ ω ι : ℝ, y * ω = y' ∧ β * ι = 1 ∧ ¬(|ω - ρ| ≤ ι)) ↔ ¬(|y' / y - ρ| ≤ 1 / β) := by
  constructor
  · rintro ⟨ω, ι, hω, hι, hnot⟩ hcon
    have hω' : y' / y = ω := by rw [← hω, mul_div_cancel_left₀ _ hy]
    have hι' : 1 / β = ι := by rw [← hι, mul_div_cancel_left₀ _ hβ]
    rw [hω', hι'] at hcon
    exact hnot hcon
  · intro hcon
    refine ⟨y' / y, 1 / β, ?_, ?_, hcon⟩
    · rw [mul_comm, div_mul_cancel₀ _ hy]
    · rw [mul_comm, div_mul_cancel₀ _ hβ]

/-- The deepness condition written with the auxiliary `x/(2β)` is exactly `IsDeepR`. -/
theorem IsDeepE_iff {B₀ : Set (Fin (k + 1) → ℝ)} {c : Fin k → ℝ} {β x : ℝ} (hβ : β ≠ 0) :
    IsDeepE k B₀ c β x ↔ IsDeepR B₀ c β x := by
  have h2 : (β + β) * x = 2 * β * x := by rw [two_mul]
  simp only [IsDeepE, IsDeepR, h2]
  constructor
  · intro h b hb hc
    exact h b ⟨hb, (deep_eq_le hβ).mpr hc.1, hc.2⟩
  · intro h b hbad
    exact h b hbad.1 ⟨(deep_eq_le hβ).mp hbad.2.1, hbad.2.2⟩

/-- The ratio condition written with the auxiliaries `x/β`, `2t`, `y'/y`, `1/β` is exactly the
window condition of `IsWit`. -/
theorem RatE_iff {Y : Set (Fin (k + 2) → ℝ)} {ρ β x : ℝ} {c : Fin k → ℝ} (hβ : β ≠ 0) :
    RatE k Y ρ β x c ↔
      (∀ t : ℝ, x / β ≤ t → t ≤ x * β →
        ∀ y y' : ℝ, Route.Gr Y c t y → Route.Gr Y c (2 * t) y' → y ≠ 0 →
          |y' / y - ρ| ≤ 1 / β) := by
  simp only [RatE]
  constructor
  · intro h t ht1 ht2 y y' hy hy' hy0
    by_contra hcon
    apply h t
    obtain ⟨e, he1, he2⟩ := (quot_eq_le hβ).mpr ht1
    refine ⟨e, y, y', t + t, y' / y, 1 / β, he1, he2, ht2, rfl, hy, ?_, ?_, ?_, hy0, hcon⟩
    · rw [two_mul] at hy'; exact hy'
    · rw [mul_comm, div_mul_cancel₀ _ hy0]
    · rw [mul_comm, div_mul_cancel₀ _ hβ]
  · intro h t
    rintro ⟨e, y, y', τ, ω, ι, he1, he2, ht2, hτ, hy, hy', hyω, hβι, hy0, hnot⟩
    have ht1 : x / β ≤ t := (quot_eq_le hβ).mp ⟨e, he1, he2⟩
    have hy2 : Route.Gr Y c (2 * t) y' := by rw [two_mul, ← hτ]; exact hy'
    have hcon : |y' / y - ρ| ≤ 1 / β := h t ht1 ht2 y y' hy hy2 hy0
    exact (ratio_iff hβ hy0).mp ⟨ω, ι, hyω, hβι, hnot⟩ hcon

/-! ## 2. The witness set in coordinates -/

theorem Q1_tuple (Y : Set (Fin (k + 2) → ℝ)) (B₀ : Set (Fin (k + 1) → ℝ))
    (ρ β : ℝ) (c : Fin k → ℝ) (x : ℝ) :
    tupleC4 k ρ β c x ∈ Q1 k Y B₀ ↔ (0 < x ∧ IsDeepE k B₀ c β x ∧ RatE k Y ρ β x c) := by
  rw [Q1, Set.mem_inter_iff, Set.mem_inter_iff, Spos_tuple, Sdeep_mem, Srat_mem]

theorem Q1_isWit (Y : Set (Fin (k + 2) → ℝ)) (B₀ : Set (Fin (k + 1) → ℝ))
    (ρ β : ℝ) (c : Fin k → ℝ) (x : ℝ) (hβ : 0 < β) :
    tupleC4 k ρ β c x ∈ Q1 k Y B₀ ↔ IsWit Y B₀ ρ β c x := by
  rw [Q1_tuple, IsDeepE_iff (ne_of_gt hβ), RatE_iff (ne_of_gt hβ)]
  rw [IsWit]

/-! ## 3. The tuples -/

/-- The tuple built from the free coordinates is the canonical tuple `tupleC4`. -/
theorem tuple_eq (v u : Fin 1 → ℝ) (c : Fin k → ℝ) (x : Fin 1 → ℝ) :
    Sum.elim (Sum.elim (Sum.elim v u) c) x = tupleC4 k (v 0) (u 0) c (x 0) := by
  rw [fin1_funext v, fin1_funext u, fin1_funext x]
  rfl

/-- Membership in `Q0`, read off the free coordinates. -/
theorem Q0_mem (Y : Set (Fin (k + 2) → ℝ)) (B₀ : Set (Fin (k + 1) → ℝ))
    (v u : Fin 1 → ℝ) :
    Sum.elim v u ∈ Q0 k Y B₀ ↔
      0 < u 0 → ∃ (c : Fin k → ℝ) (x : Fin 1 → ℝ),
        Sum.elim (Sum.elim (Sum.elim v u) c) x ∈ Q1 k Y B₀ := by
  simp only [Q0, Q0raw, Q01, Sbeta, Set.mem_union, Set.mem_compl_iff, Set.mem_ofPred_eq,
    Set.mem_setOf_eq, b2, Sum.elim_inr]
  constructor
  · rintro (h | h) h0
    · exact absurd h0 h
    · exact h
  · intro h
    by_cases h0 : 0 < u 0
    · exact Or.inr (h h0)
    · exact Or.inl h0

end CESAux

open Work.WilC4.CESAux

/-! ## 4. The theorem -/

theorem ClusterER_definable_self {k : ℕ} (Y : Set (Fin (k + 2) → ℝ)) (B₀ : Set (Fin (k + 1) → ℝ))
    (hY : (∅ : Set ℝ).Definable WilkiesDesign.CG.LRc Y)
    (hB₀ : (∅ : Set ℝ).Definable WilkiesDesign.CG.LRc B₀) :
    (∅ : Set ℝ).Definable₁ WilkiesDesign.CG.LRc (Work.WilC4.ClusterER Y B₀) := by
  rw [Set.Definable₁]
  have h := ClusterERfam_definable k hY hB₀
  convert h using 1
  ext v
  simp only [ClusterERfam, Set.mem_ofPred_eq, Set.mem_setOf_eq]
  rw [mem_ClusterER]
  constructor
  · intro hv u
    rw [Q0_mem Y B₀ v u]
    intro hu
    obtain ⟨c, x, hx⟩ := hv (u 0) hu
    refine ⟨c, fun _ : Fin 1 => x, ?_⟩
    have h2 : tupleC4 k (v 0) (u 0) c x ∈ Q1 k Y B₀ :=
      (Q1_isWit Y B₀ (v 0) (u 0) c x hu).mpr hx
    simpa [tuple_eq v u c (fun _ : Fin 1 => x)] using h2
  · intro hv β hβ
    obtain ⟨c, x, hx⟩ := (Q0_mem Y B₀ v (fun _ : Fin 1 => β)).mp (hv (fun _ : Fin 1 => β)) hβ
    refine ⟨c, x 0, (Q1_isWit Y B₀ (v 0) β c (x 0) hβ).mp ?_⟩
    simpa [tuple_eq v (fun _ : Fin 1 => β) c x] using hx

end Work.WilC4
