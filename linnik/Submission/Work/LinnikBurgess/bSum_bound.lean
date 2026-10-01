import Mathlib
import Submission.Work.LinnikBurgess.gWeighted_bSum

/-!
# The `B`-sum (weight form) with the `g ∣ ∏(B_l - x)` condition

We bound the sum, over triples `B : Fin 3 → Fin H`, of `∏_l √(gcd m |B_l - x|)`, restricted to
`B_l ≠ x` and `g ∣ ∏_l (B_l - x)`.

The reindexing `B_l ↦ |B_l - x|` maps each `B l : Fin H` to `|B l - x| < H` (here `x < H` is
used); the map `B ↦ (|B_l - x|)_l` is at most `2^3`-to-one onto the nonzero differences, because
it is injective once the sign pattern `l ↦ [x ≤ B l]` is fixed.  Hence the sum is at most
`8` times the `g`-weighted sum `gWeighted_bSum`.
-/

open scoped BigOperators

namespace Work.LinnikBurgess

/-- For `B l : Fin H` and `x < H` the difference `|B l - x|` is `< H`. -/
private lemma bSum_natAbs_lt {H x : ℕ} (hx : x < H) (B : Fin 3 → Fin H) (l : Fin 3) :
    (((B l : ℕ) : ℤ) - (x : ℤ)).natAbs < H := by
  have hBl : (B l : ℕ) < H := (B l).isLt
  rcases lt_or_ge (B l : ℕ) x with h | h
  · have h2 : (((B l : ℕ) : ℤ) - (x : ℤ)) = -((((x - (B l : ℕ)) : ℕ)) : ℤ) := by omega
    rw [h2, Int.natAbs_neg, Int.natAbs_natCast]; omega
  · have h2 : (((B l : ℕ) : ℤ) - (x : ℤ)) = ((((B l : ℕ) - x : ℕ)) : ℤ) := by omega
    rw [h2, Int.natAbs_natCast]; omega

/-- The reindexing map `B ↦ |B_l - x|` is injective once the sign pattern `l ↦ [x ≤ B l]` is
fixed. -/
private lemma bSum_inj {H x : ℕ} : ∀ B B' : Fin 3 → Fin H,
    (∀ l, (((B l : ℕ) : ℤ) - (x : ℤ)).natAbs = ((((B' l : ℕ) : ℤ) - (x : ℤ)).natAbs)) →
    (∀ l, (decide (x ≤ (B l : ℕ))) = (decide (x ≤ (B' l : ℕ)))) → B = B' := by
  intro B B' hval hsign
  funext l
  have hv := hval l
  have hiff : (x ≤ (B l : ℕ)) ↔ (x ≤ (B' l : ℕ)) := decide_eq_decide.mp (hsign l)
  apply Fin.ext
  by_cases h : x ≤ (B l : ℕ)
  · have h' := hiff.mp h
    have e1 : (((B l : ℕ) : ℤ) - (x : ℤ)).natAbs = (B l : ℕ) - x := by
      have h2 : (((B l : ℕ) : ℤ) - (x : ℤ)) = ((((B l : ℕ) - x : ℕ)) : ℤ) := by omega
      rw [h2, Int.natAbs_natCast]
    have e2 : (((B' l : ℕ) : ℤ) - (x : ℤ)).natAbs = (B' l : ℕ) - x := by
      have h2 : (((B' l : ℕ) : ℤ) - (x : ℤ)) = ((((B' l : ℕ) - x : ℕ)) : ℤ) := by omega
      rw [h2, Int.natAbs_natCast]
    rw [e1, e2] at hv
    omega
  · have h' : ¬ (x ≤ (B' l : ℕ)) := fun hh => h (hiff.mpr hh)
    have e1 : (((B l : ℕ) : ℤ) - (x : ℤ)).natAbs = x - (B l : ℕ) := by
      have h2 : (((B l : ℕ) : ℤ) - (x : ℤ)) = -((((x - (B l : ℕ)) : ℕ)) : ℤ) := by omega
      rw [h2, Int.natAbs_neg, Int.natAbs_natCast]
    have e2 : (((B' l : ℕ) : ℤ) - (x : ℤ)).natAbs = x - (B' l : ℕ) := by
      have h2 : (((B' l : ℕ) : ℤ) - (x : ℤ)) = -((((x - (B' l : ℕ)) : ℕ)) : ℤ) := by omega
      rw [h2, Int.natAbs_neg, Int.natAbs_natCast]
    rw [e1, e2] at hv
    omega

/-- The `B`-sum (weight form), with the `g ∣ ∏(B_l - x)` condition.  For `0 < m`, `gcd(m,g) = 1`,
`0 < g`, and a pivot `x < H`, the sum over `B : Fin 3 → Fin H` of `∏_l √gcd(m, |B_l - x|)`,
restricted to `B_l ≠ x` and `g ∣ ∏_l (B_l - x)`, is at most `8·τ(g)^2·H^3/g·τ(m)^3`. -/
theorem bSum_bound {m g H : ℕ} (hm : 0 < m) (hmg : Nat.Coprime m g) (hg : 0 < g) (x : ℕ)
    (hx : x < H) :
    (∑ B : Fin 3 → Fin H,
        (if (∀ l : Fin 3, (B l : ℕ) ≠ x) ∧ ((g : ℤ) ∣ ∏ l : Fin 3, (((B l : ℕ) : ℤ) - (x : ℤ)))
          then ∏ l : Fin 3,
            Real.sqrt (((Nat.gcd m ((((B l : ℕ) : ℤ) - (x : ℤ)).natAbs)) : ℕ) : ℝ)
          else (0:ℝ)))
      ≤ 8 * ((g.divisors.card : ℝ)) ^ 2 * ((H : ℝ) ^ 3 / (g : ℝ)) * ((m.divisors.card : ℝ)) ^ 3 := by
  classical
  let F : (Fin 3 → Fin H) → (Fin 3 → Fin H) :=
    fun B l => ⟨(((B l : ℕ) : ℤ) - (x : ℤ)).natAbs, bSum_natAbs_lt hx B l⟩
  let sign : (Fin 3 → Fin H) → (Fin 3 → Bool) := fun B l => decide (x ≤ (B l : ℕ))
  let Ψ : (Fin 3 → Fin H) → ℝ :=
    fun v => ∏ l : Fin 3, Real.sqrt (((Nat.gcd m (v l : ℕ)) : ℕ) : ℝ)
  let adm : (Fin 3 → Fin H) → Prop :=
    fun B => (∀ l : Fin 3, (B l : ℕ) ≠ x) ∧ ((g : ℤ) ∣ ∏ l : Fin 3, (((B l : ℕ) : ℤ) - (x : ℤ)))
  let admN : (Fin 3 → Fin H) → Prop :=
    fun v => (∀ l : Fin 3, (v l : ℕ) ≠ 0) ∧ (g ∣ ∏ l : Fin 3, (v l : ℕ))
  let G : (Fin 3 → Fin H) → ℝ := fun v => if admN v then Ψ v else 0
  change (∑ B : Fin 3 → Fin H, (if adm B then Ψ (F B) else 0))
      ≤ 8 * ((g.divisors.card : ℝ)) ^ 2 * ((H : ℝ) ^ 3 / (g : ℝ)) * ((m.divisors.card : ℝ)) ^ 3
  have hΨnn : ∀ v, 0 ≤ Ψ v := fun v => Finset.prod_nonneg (fun l _ => Real.sqrt_nonneg _)
  have hGnn : ∀ v, 0 ≤ G v := by
    intro v; simp only [G]; split_ifs with h
    · exact hΨnn v
    · exact le_refl 0
  -- Step A: admissible `B` give an admissible image under the reindexing
  have hA : ∀ B, adm B → admN (F B) := by
    intro B hB
    obtain ⟨hne, hdvd⟩ := hB
    refine ⟨?_, ?_⟩
    · intro l
      show (((B l : ℕ) : ℤ) - (x : ℤ)).natAbs ≠ 0
      intro hh
      rw [Int.natAbs_eq_zero] at hh
      exact hne l (by omega)
    · show g ∣ ∏ l : Fin 3, ((((B l : ℕ) : ℤ) - (x : ℤ)).natAbs)
      have hprod : (∏ l : Fin 3, ((((B l : ℕ) : ℤ) - (x : ℤ)).natAbs))
          = (∏ l : Fin 3, (((B l : ℕ) : ℤ) - (x : ℤ))).natAbs :=
        (map_prod Int.natAbsHom (fun l : Fin 3 => (((B l : ℕ) : ℤ) - (x : ℤ)))
          Finset.univ).symm
      rw [hprod]
      have h1 : (g : ℤ) ∣ (((∏ l : Fin 3, (((B l : ℕ) : ℤ) - (x : ℤ))).natAbs : ℕ) : ℤ) :=
        Int.dvd_natAbs.mpr hdvd
      exact Int.ofNat_dvd.mp h1
  -- Step B: each fibre of the reindexing has at most `2^3 = 8` elements
  have hfiber : ∀ v : Fin 3 → Fin H,
      (((Finset.univ : Finset (Fin 3 → Fin H)).filter (fun B => F B = v)).card) ≤ 8 := by
    intro v
    have hinj : ∀ B B' : Fin 3 → Fin H, F B = F B' → sign B = sign B' → B = B' := by
      intro B B' hFB hs
      refine bSum_inj (x := x) B B' (fun l => ?_) (fun l => ?_)
      · exact congrArg Fin.val (congrFun hFB l)
      · exact congrFun hs l
    have hcard := Finset.card_le_card_of_injOn
      (s := (Finset.univ : Finset (Fin 3 → Fin H)).filter (fun B => F B = v))
      (t := (Finset.univ : Finset (Fin 3 → Bool))) sign
      (fun B _ => Finset.mem_univ _)
      (fun B hB B' hB' hab => by
        have h1 : F B = v := (Finset.mem_filter.mp hB).2
        have h2 : F B' = v := (Finset.mem_filter.mp hB').2
        exact hinj B B' (by rw [h1, h2]) hab)
    have h2 : ((Finset.univ : Finset (Fin 3 → Bool)).card) = 8 := by decide
    omega
  -- Step C: reindex the sum over `B` onto its image under `F`, then compare with `gWeighted_bSum`
  have hC1 : (∑ B : Fin 3 → Fin H, (if adm B then Ψ (F B) else 0))
      = ∑ B ∈ (Finset.univ : Finset (Fin 3 → Fin H)).filter adm, Ψ (F B) :=
    (Finset.sum_filter (s := (Finset.univ : Finset (Fin 3 → Fin H))) adm
      (fun B => Ψ (F B))).symm
  have hC2 : (∑ B ∈ (Finset.univ : Finset (Fin 3 → Fin H)).filter adm, Ψ (F B))
      ≤ ∑ v ∈ (Finset.univ : Finset (Fin 3 → Fin H)).filter admN, 8 * G v := by
    have hpoint : ∀ B ∈ (Finset.univ : Finset (Fin 3 → Fin H)).filter adm,
        (∑ v ∈ (Finset.univ : Finset (Fin 3 → Fin H)).filter admN,
          (if F B = v then Ψ (F B) else 0)) = Ψ (F B) := by
      intro B hB
      have hadm : adm B := (Finset.mem_filter.mp hB).2
      have hFBmem : F B ∈ (Finset.univ : Finset (Fin 3 → Fin H)).filter admN :=
        Finset.mem_filter.mpr ⟨Finset.mem_univ _, hA B hadm⟩
      rw [Finset.sum_ite_eq, if_pos hFBmem]
    calc (∑ B ∈ (Finset.univ : Finset (Fin 3 → Fin H)).filter adm, Ψ (F B))
        = ∑ B ∈ (Finset.univ : Finset (Fin 3 → Fin H)).filter adm,
            ∑ v ∈ (Finset.univ : Finset (Fin 3 → Fin H)).filter admN,
              (if F B = v then Ψ (F B) else 0) :=
          Finset.sum_congr rfl (fun B hB => (hpoint B hB).symm)
      _ = ∑ v ∈ (Finset.univ : Finset (Fin 3 → Fin H)).filter admN,
            ∑ B ∈ (Finset.univ : Finset (Fin 3 → Fin H)).filter adm,
              (if F B = v then Ψ (F B) else 0) := Finset.sum_comm
      _ ≤ ∑ v ∈ (Finset.univ : Finset (Fin 3 → Fin H)).filter admN, 8 * G v := by
          apply Finset.sum_le_sum
          intro v _
          have hcard : ((((Finset.univ : Finset (Fin 3 → Fin H)).filter adm).filter
              (fun B => F B = v)).card : ℝ) ≤ 8 := by
            have hle : (((Finset.univ : Finset (Fin 3 → Fin H)).filter adm).filter
                  (fun B => F B = v)).card
                ≤ ((Finset.univ : Finset (Fin 3 → Fin H)).filter (fun B => F B = v)).card :=
              Finset.card_le_card (Finset.filter_subset_filter (fun B => F B = v)
                (Finset.subset_univ ((Finset.univ : Finset (Fin 3 → Fin H)).filter adm)))
            exact_mod_cast le_trans hle (hfiber v)
          have hsum : (∑ B ∈ (Finset.univ : Finset (Fin 3 → Fin H)).filter adm,
                (if F B = v then Ψ (F B) else 0))
              = ((((Finset.univ : Finset (Fin 3 → Fin H)).filter adm).filter
                  (fun B => F B = v)).card : ℝ) * Ψ v := by
            rw [← Finset.sum_filter]
            rw [Finset.sum_congr rfl
              (fun B hB => by rw [(Finset.mem_filter.mp hB).2])]
            rw [Finset.sum_const, nsmul_eq_mul]
          rw [hsum]
          by_cases hemp : (((Finset.univ : Finset (Fin 3 → Fin H)).filter adm).filter
              (fun B => F B = v)).Nonempty
          · obtain ⟨B, hB⟩ := hemp
            have hadm : adm B := (Finset.mem_filter.mp (Finset.mem_filter.mp hB).1).2
            have hFB : F B = v := (Finset.mem_filter.mp hB).2
            have hGN : G v = Ψ v := by
              show (if admN v then Ψ v else 0) = Ψ v
              rw [if_pos (by rw [← hFB]; exact hA B hadm)]
            rw [hGN]
            exact mul_le_mul_of_nonneg_right hcard (hΨnn v)
          · have hzero : (((Finset.univ : Finset (Fin 3 → Fin H)).filter adm).filter
                (fun B => F B = v)).card = 0 :=
              Nat.eq_zero_of_not_pos (fun h => hemp (Finset.card_pos.mp h))
            rw [hzero]
            simp only [Nat.cast_zero, zero_mul]
            exact mul_nonneg (by norm_num) (hGnn v)
  have hconv : (∑ v : Fin 3 → Fin H, (if admN v then Ψ v else 0))
      = ∑ v : Fin 3 → Fin H,
          (if (∀ l : Fin 3, (v l : ℕ) ≠ 0) ∧ ((g : ℤ) ∣ ∏ l : Fin 3, (((v l : ℕ)) : ℤ))
            then ∏ l : Fin 3, Real.sqrt (((Nat.gcd m (v l : ℕ)) : ℕ) : ℝ) else (0:ℝ)) := by
    apply Finset.sum_congr rfl
    intro v _
    have hiff : admN v ↔
        ((∀ l : Fin 3, (v l : ℕ) ≠ 0) ∧ ((g : ℤ) ∣ ∏ l : Fin 3, (((v l : ℕ)) : ℤ))) := by
      show ((∀ l : Fin 3, (v l : ℕ) ≠ 0) ∧ (g ∣ ∏ l : Fin 3, (v l : ℕ))) ↔ _
      constructor
      · rintro ⟨h1, h2⟩
        exact ⟨h1, by rw [← Nat.cast_prod]; exact Int.ofNat_dvd.mpr h2⟩
      · rintro ⟨h1, h2⟩
        exact ⟨h1, Int.ofNat_dvd.mp (by rwa [← Nat.cast_prod] at h2)⟩
    by_cases h : admN v
    · rw [if_pos h, if_pos (hiff.mp h)]
    · rw [if_neg h, if_neg (fun hh => h (hiff.mpr hh))]
  calc (∑ B : Fin 3 → Fin H, (if adm B then Ψ (F B) else 0))
      = ∑ B ∈ (Finset.univ : Finset (Fin 3 → Fin H)).filter adm, Ψ (F B) := hC1
    _ ≤ ∑ v ∈ (Finset.univ : Finset (Fin 3 → Fin H)).filter admN, 8 * G v := hC2
    _ = 8 * ∑ v : Fin 3 → Fin H, (if admN v then Ψ v else 0) := by
          have h1 : (∑ v ∈ (Finset.univ : Finset (Fin 3 → Fin H)).filter admN, G v)
              = ∑ v ∈ (Finset.univ : Finset (Fin 3 → Fin H)).filter admN, Ψ v := by
            apply Finset.sum_congr rfl; intro v hv
            show (if admN v then Ψ v else 0) = Ψ v
            rw [if_pos (Finset.mem_filter.mp hv).2]
          have h2 : (∑ v ∈ (Finset.univ : Finset (Fin 3 → Fin H)).filter admN, Ψ v)
              = ∑ v : Fin 3 → Fin H, (if admN v then Ψ v else 0) := by
            rw [Finset.sum_filter]
          rw [← Finset.mul_sum, h1, h2]
    _ = 8 * (∑ v : Fin 3 → Fin H,
          (if (∀ l : Fin 3, (v l : ℕ) ≠ 0) ∧ ((g : ℤ) ∣ ∏ l : Fin 3, (((v l : ℕ)) : ℤ))
            then ∏ l : Fin 3, Real.sqrt (((Nat.gcd m (v l : ℕ)) : ℕ) : ℝ) else (0:ℝ))) := by
          rw [hconv]
    _ ≤ 8 * (((g.divisors.card : ℝ)) ^ 2 * ((H : ℝ) ^ 3 / (g : ℝ))
          * ((m.divisors.card : ℝ)) ^ 3) :=
          mul_le_mul_of_nonneg_left (gWeighted_bSum (m := m) (g := g) (H := H) hm hmg hg)
            (by norm_num)
    _ = 8 * ((g.divisors.card : ℝ)) ^ 2 * ((H : ℝ) ^ 3 / (g : ℝ))
          * ((m.divisors.card : ℝ)) ^ 3 := by ring

end Work.LinnikBurgess
