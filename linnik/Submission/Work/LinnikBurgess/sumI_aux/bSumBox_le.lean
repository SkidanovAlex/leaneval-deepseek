import Mathlib
import Submission.Work.LinnikBurgess.sumI_defs
import Submission.Work.LinnikBurgess.bSum_bound

namespace Work.LinnikBurgess.sumI_aux

open scoped BigOperators

/-- Reindexing the box `[1,H]^3` onto `Fin 3 → Fin H` by the shift `b l ↦ b l + 1`:
`∑_{b ∈ box3 H} F b = ∑_{B : Fin 3 → Fin H} F (fun l => B l + 1)`.  The two sets both have
`H^3` elements and the shift is a bijection `Fin H → [1,H]`. -/
lemma sum_box3_eq_sum_fin (H : ℕ) (F : (Fin 3 → ℕ) → ℝ) :
    ∑ b ∈ Work.LinnikBurgess.box3 H, F b
      = ∑ B : Fin 3 → Fin H, F (fun l => (B l : ℕ) + 1) := by
  have key := Finset.sum_bij
    (s := Work.LinnikBurgess.box3 H) (t := (Finset.univ : Finset (Fin 3 → Fin H)))
    (f := F) (g := fun B : Fin 3 → Fin H => F (fun l => (B l : ℕ) + 1))
    (fun a ha => fun l => ⟨a l - 1, by
      have h := Fintype.mem_piFinset.mp ha l
      rw [Finset.mem_Icc] at h
      omega⟩)
    (fun a ha => Finset.mem_univ _)
    (fun a1 ha1 a2 ha2 heq => by
      funext l
      have hv := congrArg Fin.val (congrFun heq l)
      have h1 := Fintype.mem_piFinset.mp ha1 l
      have h2 := Fintype.mem_piFinset.mp ha2 l
      rw [Finset.mem_Icc] at h1 h2
      simp only at hv
      omega)
    (fun b _ => by
      refine ⟨fun l => (b l : ℕ) + 1, ?_, ?_⟩
      · show (fun l => (b l : ℕ) + 1) ∈ Fintype.piFinset (fun _ : Fin 3 => Finset.Icc 1 H)
        rw [Fintype.mem_piFinset]
        intro l
        rw [Finset.mem_Icc]
        have := (b l).isLt
        omega
      · funext l
        apply Fin.ext
        simp)
    (fun a ha => by
      show F a = F (fun l => (((a l - 1 : ℕ)) + 1))
      congr 1
      funext l
      have h := Fintype.mem_piFinset.mp ha l
      rw [Finset.mem_Icc] at h
      omega)
  simpa using key

/-- **Pointwise comparison.**  For `1 ≤ x0` and `B : Fin 3 → Fin H`, the `box3`-integrand at the
triple `b l = B l + 1` equals the integrand of `bSum_bound` at the pivot `x0 - 1`. -/
lemma bSumBox_term_eq {H m g x0 : ℕ} (hx0 : 1 ≤ x0) (B : Fin 3 → Fin H) :
    (if (∀ l : Fin 3, (B l : ℕ) + 1 ≠ x0) ∧ (g ∣ ∏ k : Fin 3, Work.LinnikBurgess.del x0 ((B k : ℕ) + 1))
        then ∏ k : Fin 3, Work.LinnikBurgess.wg m x0 ((B k : ℕ) + 1) else 0)
      = (if (∀ l : Fin 3, (B l : ℕ) ≠ x0 - 1)
            ∧ ((g : ℤ) ∣ ∏ l : Fin 3, (((B l : ℕ) : ℤ) - ((x0 - 1 : ℕ) : ℤ)))
          then ∏ l : Fin 3,
            Real.sqrt (((Nat.gcd m ((((B l : ℕ) : ℤ) - ((x0 - 1 : ℕ) : ℤ)).natAbs)) : ℕ) : ℝ)
          else 0) := by
  have hne : (∀ l : Fin 3, (B l : ℕ) + 1 ≠ x0) ↔ (∀ l : Fin 3, (B l : ℕ) ≠ x0 - 1) := by
    constructor <;> intro h l <;> have := h l <;> omega
  have hdel : ∀ l : Fin 3,
      Work.LinnikBurgess.del x0 ((B l : ℕ) + 1) = ((((B l : ℕ) : ℤ) - ((x0 - 1 : ℕ) : ℤ)).natAbs) := by
    intro l
    show (((x0 : ℤ) - (((B l : ℕ) + 1 : ℕ) : ℤ)).natAbs) = _
    have hc : ((x0 - 1 : ℕ) : ℤ) = (x0 : ℤ) - 1 := by push_cast [hx0]; ring
    rw [hc]
    have : ((x0 : ℤ) - (((B l : ℕ) + 1 : ℕ) : ℤ)) = -(((B l : ℕ) : ℤ) - ((x0 : ℤ) - 1)) := by
      push_cast; ring
    rw [this, Int.natAbs_neg]
  have hdvd : (g ∣ ∏ k : Fin 3, Work.LinnikBurgess.del x0 ((B k : ℕ) + 1)) ↔
      ((g : ℤ) ∣ ∏ l : Fin 3, (((B l : ℕ) : ℤ) - ((x0 - 1 : ℕ) : ℤ))) := by
    have h1 : (∏ k : Fin 3, Work.LinnikBurgess.del x0 ((B k : ℕ) + 1))
        = (∏ k : Fin 3, (((B k : ℕ) : ℤ) - ((x0 - 1 : ℕ) : ℤ))).natAbs := by
      rw [Finset.prod_congr rfl (fun k _ => hdel k)]
      exact (map_prod Int.natAbsHom
        (fun k : Fin 3 => (((B k : ℕ) : ℤ) - ((x0 - 1 : ℕ) : ℤ))) Finset.univ).symm
    rw [h1, ← Int.ofNat_dvd, Int.dvd_natAbs]
  have hprod : (∏ k : Fin 3, Work.LinnikBurgess.wg m x0 ((B k : ℕ) + 1))
      = ∏ l : Fin 3,
          Real.sqrt (((Nat.gcd m ((((B l : ℕ) : ℤ) - ((x0 - 1 : ℕ) : ℤ)).natAbs)) : ℕ) : ℝ) := by
    apply Finset.prod_congr rfl
    intro l _
    show Real.sqrt (((Nat.gcd m (Work.LinnikBurgess.del x0 ((B l : ℕ) + 1)) : ℕ) : ℝ)) = _
    rw [hdel l]
  by_cases hc : (∀ l : Fin 3, (B l : ℕ) + 1 ≠ x0)
      ∧ (g ∣ ∏ k : Fin 3, Work.LinnikBurgess.del x0 ((B k : ℕ) + 1))
  · rw [if_pos hc, if_pos ⟨hne.mp hc.1, hdvd.mp hc.2⟩, hprod]
  · rw [if_neg hc, if_neg (fun hh => hc ⟨hne.mpr hh.1, hdvd.mpr hh.2⟩)]

/-- The `box3`-form of `bSum_bound`: the `b`-sum with pivot `x0` of the weights `∏_k wg m x0 (b k)`, restricted to `b k ≠ x0` and `g ∣ ∏_k del x0 (b k)`, is at most `8 τ(g)^2 H^3/g τ(m)^3`. -/
theorem bSumBox_le {m g H : ℕ} (hm : 0 < m) (hmg : Nat.Coprime m g) (hg : 0 < g)
    {x0 : ℕ} (hx0 : x0 ∈ Finset.Icc 1 H) :
    Work.LinnikBurgess.bSumBox H m g x0
      ≤ 8 * ((g.divisors.card : ℝ) ^ 2) * ((H : ℝ) ^ 3 / (g : ℝ))
          * ((m.divisors.card : ℝ) ^ 3) := by
  obtain ⟨hx01, hx0H⟩ := Finset.mem_Icc.mp hx0
  have hxlt : x0 - 1 < H := by omega
  rw [Work.LinnikBurgess.bSumBox]
  rw [sum_box3_eq_sum_fin]
  calc (∑ B : Fin 3 → Fin H,
        (if (∀ l : Fin 3, (B l : ℕ) + 1 ≠ x0)
              ∧ (g ∣ ∏ k : Fin 3, Work.LinnikBurgess.del x0 ((B k : ℕ) + 1))
            then ∏ k : Fin 3, Work.LinnikBurgess.wg m x0 ((B k : ℕ) + 1) else 0))
      = ∑ B : Fin 3 → Fin H,
          (if (∀ l : Fin 3, (B l : ℕ) ≠ x0 - 1)
                ∧ ((g : ℤ) ∣ ∏ l : Fin 3, (((B l : ℕ) : ℤ) - ((x0 - 1 : ℕ) : ℤ)))
              then ∏ l : Fin 3,
                Real.sqrt (((Nat.gcd m ((((B l : ℕ) : ℤ) - ((x0 - 1 : ℕ) : ℤ)).natAbs)) : ℕ) : ℝ)
              else 0) := by
        apply Finset.sum_congr rfl
        intro B _
        exact bSumBox_term_eq hx01 B
    _ ≤ 8 * ((g.divisors.card : ℝ) ^ 2) * ((H : ℝ) ^ 3 / (g : ℝ))
          * ((m.divisors.card : ℝ) ^ 3) :=
        Work.LinnikBurgess.bSum_bound hm hmg hg (x0 - 1) hxlt

end Work.LinnikBurgess.sumI_aux
