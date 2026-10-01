import Mathlib
import Submission.Work.LinnikBurgess.frame_count_prov_defs
import Submission.Work.LinnikBurgess.frame_count_prov_helpers
import Submission.Work.ZeroFreeTables.P9F.caseS_defs
import Submission.Work.ZeroFreeTables.P9F.caseS_collapse
import Submission.Work.LinnikBurgess.card_decompFinset_le
import Submission.Work.LinnikBurgess.sumSqrtGcd_Icc_le_aux
import Submission.Work.LinnikBurgess.frame_count_prov_aux.bsum_expansion
import Submission.Commons.NumberTheory.Divisors.sum_gcd_le_of_pos

/-!
# The Case S estimate of the frame count

In Case S of the frame count the two non-pivot entries of the first triple coincide
(`a 1 = a 2 = s`).  Writing `α = a 0` for the pivot, the weight is
`(wg m α s)^2 · ∏_k wg m α (b k)` and the constraint `g ∣ contAB a b` implies
`g ∣ ∏_k |α - b k|`.  Dropping `DLd` and relaxing the constraints gives the factorised
bound

`sumS H m d g ≤ ∑_{α ∈ [1,H]} Ss H m α · Ys H m g α`

(`Work.ZeroFreeTables.P9F.caseS_collapse`), with

* `Ss H m α = ∑_{s ≠ α} (wg m α s)^2 ≤ H τ(m)`, and
* `Ys H m g α ≤ τ(g)^2 H^3 τ(m)^3 / g`.

Multiplying and summing over the `H` choices of `α` gives `τ(g)^2 τ(m)^4 H^5 / g`,
which is below `30000 τ(m d g)^8 (H^6/(dg) + H^5/g)`.
-/

open scoped BigOperators

namespace Work.LinnikBurgess

open Classical

/-- `sumS` is `sum2` with the case predicate `CaseS`. -/
lemma sumS_eq_sum2 (H m d g : ℕ) : sumS H m d g = sum2 H m d g CaseS := by
  unfold sumS sum2
  simp only [box3, Work.LinnikBurgess.sum_piFinset_fin3]

/-- **The collapsed `x`-weight sum of Case S.** `Ss H m α = ∑_{s ∈ [1,H], s ≠ α} (wg m α s)^2` is
at most `H·τ(m)` for `α ∈ [1,H]` and `0 < m`. -/
theorem sumS_ss_le (H m : ℕ) (hm : 0 < m) (α : ℕ) (hα : α ∈ Finset.Icc 1 H) :
    Work.ZeroFreeTables.P9F.Ss H m α ≤ (H : ℝ) * ((m.divisors.card : ℕ) : ℝ) := by
  obtain ⟨hα1, hαH⟩ := Finset.mem_Icc.mp hα
  have hsplit : (Finset.Icc 1 H).filter (fun s => s ≠ α)
      = Finset.Icc 1 (α - 1) ∪ Finset.Icc (α + 1) H := by
    ext s
    simp only [Finset.mem_filter, Finset.mem_Icc, Finset.mem_union]
    omega
  have hdisj : Disjoint (Finset.Icc 1 (α - 1)) (Finset.Icc (α + 1) H) := by
    rw [Finset.disjoint_left]
    intro a ha hb
    simp only [Finset.mem_Icc] at ha hb
    omega
  have hdel_lo : ∀ s ∈ Finset.Icc 1 (α - 1), Work.LinnikBurgess.del α s = α - s := by
    intro s hs
    simp only [Finset.mem_Icc] at hs
    rw [Work.LinnikBurgess.del]
    have h : ((α : ℤ) - (s : ℤ)) = (((α - s : ℕ)) : ℤ) := by omega
    rw [h, Int.natAbs_natCast]
  have hdel_hi : ∀ s ∈ Finset.Icc (α + 1) H, Work.LinnikBurgess.del α s = s - α := by
    intro s hs
    simp only [Finset.mem_Icc] at hs
    rw [Work.LinnikBurgess.del]
    have h : ((α : ℤ) - (s : ℤ)) = -(((s - α : ℕ)) : ℤ) := by omega
    rw [h, Int.natAbs_neg, Int.natAbs_natCast]
  have hbound : ∀ N : ℕ,
      (∑ c ∈ Finset.Icc 1 N, ((Nat.gcd m c : ℕ) : ℝ)) ≤ (N : ℝ) * ((m.divisors.card : ℕ) : ℝ) := by
    intro N
    have hnat : ∑ c ∈ Finset.Icc 1 N, Nat.gcd m c ≤ N * m.divisors.card := by
      calc ∑ c ∈ Finset.Icc 1 N, Nat.gcd m c = ∑ c ∈ Finset.Icc 1 N, Nat.gcd c m :=
            Finset.sum_congr rfl (fun c _ => Nat.gcd_comm _ _)
        _ ≤ N * m.divisors.card := Commons.NumberTheory.Divisors.sum_gcd_le_of_pos N m hm
    calc (∑ c ∈ Finset.Icc 1 N, ((Nat.gcd m c : ℕ) : ℝ))
        = ((∑ c ∈ Finset.Icc 1 N, Nat.gcd m c : ℕ) : ℝ) := (Nat.cast_sum _ _).symm
      _ ≤ ((N * m.divisors.card : ℕ) : ℝ) := by exact_mod_cast hnat
      _ = (N : ℝ) * ((m.divisors.card : ℕ) : ℝ) := by push_cast; ring
  have hbij_lo : (∑ s ∈ Finset.Icc 1 (α - 1), ((Nat.gcd m (α - s) : ℕ) : ℝ))
      = ∑ c ∈ Finset.Icc 1 (α - 1), ((Nat.gcd m c : ℕ) : ℝ) := by
    refine Finset.sum_bij (fun a _ => α - a) (fun a ha => ?_) (fun a1 ha1 a2 ha2 heq => ?_)
      (fun b hb => ?_) (fun a ha => rfl)
    · simp only [Finset.mem_Icc] at ha ⊢; omega
    · simp only [Finset.mem_Icc] at ha1 ha2; omega
    · simp only [Finset.mem_Icc] at hb
      exact ⟨α - b, by simp only [Finset.mem_Icc]; omega, by omega⟩
  have hbij_hi : (∑ s ∈ Finset.Icc (α + 1) H, ((Nat.gcd m (s - α) : ℕ) : ℝ))
      = ∑ c ∈ Finset.Icc 1 (H - α), ((Nat.gcd m c : ℕ) : ℝ) := by
    refine Finset.sum_bij (fun a _ => a - α) (fun a ha => ?_) (fun a1 ha1 a2 ha2 heq => ?_)
      (fun b hb => ?_) (fun a ha => rfl)
    · simp only [Finset.mem_Icc] at ha ⊢; omega
    · simp only [Finset.mem_Icc] at ha1 ha2; omega
    · simp only [Finset.mem_Icc] at hb
      exact ⟨b + α, by simp only [Finset.mem_Icc]; omega, by omega⟩
  have hnat : (α - 1) + (H - α) = H - 1 := by omega
  have e1 : (∑ s ∈ Finset.Icc 1 (α - 1), ((Nat.gcd m (Work.LinnikBurgess.del α s) : ℕ) : ℝ))
      = ∑ s ∈ Finset.Icc 1 (α - 1), ((Nat.gcd m (α - s) : ℕ) : ℝ) :=
    Finset.sum_congr rfl (fun s hs => by rw [hdel_lo s hs])
  have e2 : (∑ s ∈ Finset.Icc (α + 1) H, ((Nat.gcd m (Work.LinnikBurgess.del α s) : ℕ) : ℝ))
      = ∑ s ∈ Finset.Icc (α + 1) H, ((Nat.gcd m (s - α) : ℕ) : ℝ) :=
    Finset.sum_congr rfl (fun s hs => by rw [hdel_hi s hs])
  rw [Work.ZeroFreeTables.P9F.Ss_eq_gcd_sum, hsplit, Finset.sum_union hdisj, e1, e2,
    hbij_lo, hbij_hi]
  calc (∑ c ∈ Finset.Icc 1 (α - 1), ((Nat.gcd m c : ℕ) : ℝ))
        + ∑ c ∈ Finset.Icc 1 (H - α), ((Nat.gcd m c : ℕ) : ℝ)
      ≤ ((α - 1 : ℕ) : ℝ) * ((m.divisors.card : ℕ) : ℝ)
        + ((H - α : ℕ) : ℝ) * ((m.divisors.card : ℕ) : ℝ) :=
        add_le_add (hbound (α - 1)) (hbound (H - α))
    _ = (((H - 1 : ℕ)) : ℝ) * ((m.divisors.card : ℕ) : ℝ) := by
        rw [← add_mul, ← Nat.cast_add, hnat]
    _ ≤ (H : ℝ) * ((m.divisors.card : ℕ) : ℝ) := by
        refine mul_le_mul_of_nonneg_right ?_ (by positivity)
        exact_mod_cast Nat.sub_le H 1

/-- **Per-coordinate bound of Case S.** For `α ∈ [1,H]`, `0 < m` and `0 < e` with
`gcd(m,e) = 1`, the sum of `wg m α y = √(gcd m |α-y|)` over the `y ∈ [1,H]` with
`y ≠ α` and `e ∣ |α - y|` is at most `H·τ(m)/e`. -/
theorem sumS_coord_le (H m e α : ℕ) (hm : 0 < m) (he : 0 < e) (hcop : Nat.Coprime m e)
    (hα : α ∈ Finset.Icc 1 H) :
    ∑ y ∈ (Finset.Icc 1 H).filter (fun y => y ≠ α ∧ e ∣ Work.LinnikBurgess.del α y),
        Work.LinnikBurgess.wg m α y
      ≤ (H : ℝ) * ((m.divisors.card : ℕ) : ℝ) / (e : ℝ) := by
  obtain ⟨hα1, hαH⟩ := Finset.mem_Icc.mp hα
  have hdel_le : ∀ {y : ℕ}, y ≤ α → Work.LinnikBurgess.del α y = α - y := by
    intro y hy
    rw [Work.LinnikBurgess.del]
    have h : ((α : ℤ) - (y : ℤ)) = (((α - y : ℕ)) : ℤ) := by omega
    rw [h, Int.natAbs_natCast]
  have hdel_ge : ∀ {y : ℕ}, α ≤ y → Work.LinnikBurgess.del α y = y - α := by
    intro y hy
    rw [Work.LinnikBurgess.del]
    have h : ((α : ℤ) - (y : ℤ)) = -(((y - α : ℕ)) : ℤ) := by omega
    rw [h, Int.natAbs_neg, Int.natAbs_natCast]
  have hgcd : ∀ k : ℕ, Nat.gcd m (e * k) = Nat.gcd m k := by
    intro k
    rw [Nat.gcd_comm m (e * k), Nat.gcd_comm m k]
    exact Nat.Coprime.gcd_mul_left_cancel k hcop.symm
  set A₁ := (Finset.Icc 1 (α - 1)).filter (fun y => e ∣ α - y) with hA₁
  set A₂ := (Finset.Icc (α + 1) H).filter (fun y => e ∣ y - α) with hA₂
  have hsplit : (Finset.Icc 1 H).filter (fun y => y ≠ α ∧ e ∣ Work.LinnikBurgess.del α y)
      = A₁ ∪ A₂ := by
    ext y
    simp only [Finset.mem_filter, Finset.mem_Icc, Finset.mem_union, hA₁, hA₂]
    constructor
    · rintro ⟨⟨hy1, hyH⟩, hyne, hdvd⟩
      rcases lt_or_gt_of_ne hyne with h | h
      · left
        exact ⟨⟨hy1, by omega⟩, by rwa [hdel_le (le_of_lt h)] at hdvd⟩
      · right
        exact ⟨⟨by omega, hyH⟩, by rwa [hdel_ge (le_of_lt h)] at hdvd⟩
    · rintro (⟨⟨hy1, hy2⟩, hdvd⟩ | ⟨⟨hy1, hy2⟩, hdvd⟩)
      · exact ⟨⟨hy1, by omega⟩, by omega, by rwa [hdel_le (by omega : y ≤ α)]⟩
      · exact ⟨⟨by omega, hy2⟩, by omega, by rwa [hdel_ge (by omega : α ≤ y)]⟩
  have hdisj : Disjoint A₁ A₂ := by
    rw [Finset.disjoint_left]
    intro y hy1 hy2
    simp only [Finset.mem_filter, Finset.mem_Icc, hA₁] at hy1
    simp only [Finset.mem_filter, Finset.mem_Icc, hA₂] at hy2
    omega
  have hbij1 : (∑ y ∈ A₁, Work.LinnikBurgess.wg m α y)
      = ∑ s ∈ Finset.Icc 1 ((α - 1) / e), Real.sqrt (((Nat.gcd m s : ℕ)) : ℝ) := by
    refine Finset.sum_bij' (fun y _ => (α - y) / e) (fun s _ => α - e * s)
      (fun y hy => ?_) (fun s hs => ?_) (fun y hy => ?_) (fun s hs => ?_) (fun y hy => ?_)
    · simp only [Finset.mem_filter, Finset.mem_Icc, hA₁] at hy
      obtain ⟨⟨hy1, hy2⟩, hdvd⟩ := hy
      simp only [Finset.mem_Icc]
      refine ⟨?_, Nat.div_le_div_right (by omega)⟩
      exact Nat.div_pos (Nat.le_of_dvd (by omega) hdvd) he
    · simp only [Finset.mem_Icc] at hs
      simp only [Finset.mem_filter, Finset.mem_Icc, hA₁]
      obtain ⟨hs1, hs2⟩ := hs
      have hpos : 1 ≤ e * s := Nat.mul_pos he (by omega)
      have hle : e * s ≤ α - 1 :=
        (Nat.mul_le_mul_left e hs2).trans (Nat.mul_div_le (α - 1) e)
      refine ⟨⟨by omega, by omega⟩, ?_⟩
      have h : α - (α - e * s) = e * s := by omega
      rw [h]
      exact dvd_mul_right e s
    · simp only [Finset.mem_filter, Finset.mem_Icc, hA₁] at hy
      obtain ⟨⟨hy1, hy2⟩, hdvd⟩ := hy
      have h1 : e * ((α - y) / e) = α - y := Nat.mul_div_cancel' hdvd
      rw [h1]; omega
    · simp only [Finset.mem_Icc] at hs
      obtain ⟨hs1, hs2⟩ := hs
      have hpos : 1 ≤ e * s := Nat.mul_pos he (by omega)
      have hle : e * s ≤ α - 1 :=
        (Nat.mul_le_mul_left e hs2).trans (Nat.mul_div_le (α - 1) e)
      have h : α - (α - e * s) = e * s := by omega
      rw [h, Nat.mul_div_cancel_left s he]
    · simp only [Finset.mem_filter, Finset.mem_Icc, hA₁] at hy
      obtain ⟨⟨hy1, hy2⟩, hdvd⟩ := hy
      have hdel' : Work.LinnikBurgess.del α y = e * ((α - y) / e) := by
        rw [hdel_le (by omega : y ≤ α)]
        exact (Nat.mul_div_cancel' hdvd).symm
      rw [Work.LinnikBurgess.wg, hdel', hgcd ((α - y) / e)]
  have hbij2 : (∑ y ∈ A₂, Work.LinnikBurgess.wg m α y)
      = ∑ s ∈ Finset.Icc 1 ((H - α) / e), Real.sqrt (((Nat.gcd m s : ℕ)) : ℝ) := by
    refine Finset.sum_bij' (fun y _ => (y - α) / e) (fun s _ => e * s + α)
      (fun y hy => ?_) (fun s hs => ?_) (fun y hy => ?_) (fun s hs => ?_) (fun y hy => ?_)
    · simp only [Finset.mem_filter, Finset.mem_Icc, hA₂] at hy
      obtain ⟨⟨hy1, hy2⟩, hdvd⟩ := hy
      simp only [Finset.mem_Icc]
      refine ⟨?_, Nat.div_le_div_right (by omega)⟩
      exact Nat.div_pos (Nat.le_of_dvd (by omega) hdvd) he
    · simp only [Finset.mem_Icc] at hs
      simp only [Finset.mem_filter, Finset.mem_Icc, hA₂]
      obtain ⟨hs1, hs2⟩ := hs
      have hpos : 1 ≤ e * s := Nat.mul_pos he (by omega)
      have hle : e * s ≤ H - α :=
        (Nat.mul_le_mul_left e hs2).trans (Nat.mul_div_le (H - α) e)
      refine ⟨⟨by omega, by omega⟩, ?_⟩
      rw [Nat.add_sub_cancel]
      exact dvd_mul_right e s
    · simp only [Finset.mem_filter, Finset.mem_Icc, hA₂] at hy
      obtain ⟨⟨hy1, hy2⟩, hdvd⟩ := hy
      have h1 : e * ((y - α) / e) = y - α := Nat.mul_div_cancel' hdvd
      rw [h1]; omega
    · simp only [Finset.mem_Icc] at hs
      obtain ⟨hs1, hs2⟩ := hs
      have hpos : 1 ≤ e * s := Nat.mul_pos he (by omega)
      have hle : e * s ≤ H - α :=
        (Nat.mul_le_mul_left e hs2).trans (Nat.mul_div_le (H - α) e)
      rw [Nat.add_sub_cancel, Nat.mul_div_cancel_left s he]
    · simp only [Finset.mem_filter, Finset.mem_Icc, hA₂] at hy
      obtain ⟨⟨hy1, hy2⟩, hdvd⟩ := hy
      have hdel' : Work.LinnikBurgess.del α y = e * ((y - α) / e) := by
        rw [hdel_ge (by omega : α ≤ y)]
        exact (Nat.mul_div_cancel' hdvd).symm
      rw [Work.LinnikBurgess.wg, hdel', hgcd ((y - α) / e)]
  have hτm : (0 : ℝ) ≤ ((m.divisors.card : ℕ) : ℝ) := by positivity
  have heR : (0 : ℝ) < (e : ℝ) := by exact_mod_cast he
  rw [hsplit, Finset.sum_union hdisj, hbij1, hbij2]
  refine (add_le_add (Work.LinnikBurgess.sumSqrtGcd_Icc_le_aux m ((α - 1) / e) hm)
    (Work.LinnikBurgess.sumSqrtGcd_Icc_le_aux m ((H - α) / e) hm)).trans ?_
  have hA : (((α - 1) / e : ℕ) : ℝ) ≤ ((α - 1 : ℕ) : ℝ) / (e : ℝ) := Nat.cast_div_le
  have hB : (((H - α) / e : ℕ) : ℝ) ≤ ((H - α : ℕ) : ℝ) / (e : ℝ) := Nat.cast_div_le
  have hnat : (α - 1) + (H - α) = H - 1 := by omega
  have hc : (((α - 1 : ℕ)) : ℝ) + (((H - α : ℕ)) : ℝ) = (((H - 1 : ℕ)) : ℝ) := by
    rw [← Nat.cast_add, hnat]
  calc (((α - 1) / e : ℕ) : ℝ) * ((m.divisors.card : ℕ) : ℝ)
        + (((H - α) / e : ℕ) : ℝ) * ((m.divisors.card : ℕ) : ℝ)
      ≤ (((α - 1 : ℕ) : ℝ) / (e : ℝ)) * ((m.divisors.card : ℕ) : ℝ)
        + (((H - α : ℕ) : ℝ) / (e : ℝ)) * ((m.divisors.card : ℕ) : ℝ) :=
        add_le_add (mul_le_mul_of_nonneg_right hA hτm) (mul_le_mul_of_nonneg_right hB hτm)
    _ = (((H - 1 : ℕ)) : ℝ) * ((m.divisors.card : ℕ) : ℝ) / (e : ℝ) := by
        rw [← hc]; ring
    _ ≤ (H : ℝ) * ((m.divisors.card : ℕ) : ℝ) / (e : ℝ) := by
        apply div_le_div_of_nonneg_right _ heR.le
        exact mul_le_mul_of_nonneg_right (by exact_mod_cast Nat.sub_le H 1) hτm

/-- **The `y`-sum of Case S.** `Ys H m g α = ∑_{y ∈ box3 H} [∀l, y l ≠ α][g ∣ ∏_k |α - y k|] ∏_k wg m α (y k)`
is at most `τ(g)^2 · H^3 · τ(m)^3 / g` for `α ∈ [1,H]`, `0 < m`, `0 < g` and `gcd(m,g) = 1`. -/
theorem sumS_ys_le (H m g : ℕ) (hm : 0 < m) (hg : 0 < g) (hcop : Nat.Coprime m g) (α : ℕ)
    (hα : α ∈ Finset.Icc 1 H) :
    Work.ZeroFreeTables.P9F.Ys H m g α
      ≤ ((g.divisors.card : ℕ) : ℝ) ^ 2 * (H : ℝ) ^ 3
          * ((m.divisors.card : ℕ) : ℝ) ^ 3 / (g : ℝ) := by
  have hYs_eq : Work.ZeroFreeTables.P9F.Ys H m g α = ∑ b ∈ box3 H,
      (if g ∣ ∏ k : Fin 3, del α (b k) then
        ∏ k : Fin 3, (if b k ≠ α then wg m α (b k) else 0) else 0) := by
    unfold Work.ZeroFreeTables.P9F.Ys
    refine Finset.sum_congr rfl (fun b _ => ?_)
    by_cases hQ : g ∣ ∏ k : Fin 3, del α (b k)
    · by_cases h : ∀ l : Fin 3, b l ≠ α
      · rw [if_pos ⟨h, hQ⟩, if_pos hQ]
        exact Finset.prod_congr rfl (fun k _ => (if_pos (h k)).symm)
      · rw [if_neg (fun hh => h hh.1), if_pos hQ]
        push Not at h
        obtain ⟨l, hl⟩ := h
        exact (Finset.prod_eq_zero (Finset.mem_univ l)
          (by rw [if_neg (fun hh => hh hl)])).symm
    · rw [if_neg (fun hh => hQ hh.2), if_neg hQ]
  rw [hYs_eq]
  refine (Work.LinnikBurgess.frame_count_prov_aux.bsum_expansion hg (fun _ y => wg m α y)
      (fun _ y => wg_nonneg m α y)).trans ?_
  set A : Finset (Fin 3 → ℕ) :=
    (Fintype.piFinset (fun _ : Fin 3 => g.divisors)).filter
      (fun a : Fin 3 → ℕ => ∏ k : Fin 3, a k = g) with hA
  have hmem : ∀ a ∈ A, (∀ k : Fin 3, a k ∣ g) ∧ ∏ k : Fin 3, a k = g := by
    intro a ha
    rw [hA, Finset.mem_filter, Fintype.mem_piFinset] at ha
    exact ⟨fun k => (Nat.mem_divisors.mp (ha.1 k)).1, ha.2⟩
  have hprod_bound : ∀ a ∈ A,
      (∏ k : Fin 3,
          ∑ y ∈ (Finset.Icc 1 H).filter (fun y => y ≠ α ∧ a k ∣ del α y), wg m α y)
        ≤ ((H : ℝ) * ((m.divisors.card : ℕ) : ℝ)) ^ 3 / (g : ℝ) := by
    intro a ha
    obtain ⟨hdvd, hproda⟩ := hmem a ha
    have hle : ∀ k : Fin 3,
        (∑ y ∈ (Finset.Icc 1 H).filter (fun y => y ≠ α ∧ a k ∣ del α y), wg m α y)
          ≤ (H : ℝ) * ((m.divisors.card : ℕ) : ℝ) / ((a k : ℕ) : ℝ) := fun k =>
      sumS_coord_le H m (a k) α hm (Nat.pos_of_dvd_of_pos (hdvd k) hg)
        (Nat.Coprime.coprime_dvd_right (hdvd k) hcop) hα
    refine (Finset.prod_le_prod₀ (fun k _ => Finset.sum_nonneg (fun y _ => wg_nonneg m α y))
      (fun k _ => hle k)).trans (le_of_eq ?_)
    have hc : ((g : ℕ) : ℝ) = ∏ k : Fin 3, ((a k : ℕ) : ℝ) := by
      rw [← hproda, Nat.cast_prod]
    rw [hc, Fin.prod_univ_three, Fin.prod_univ_three]
    have h0 : ((a 0 : ℕ) : ℝ) ≠ 0 :=
      (by exact_mod_cast (Nat.pos_of_dvd_of_pos (hdvd 0) hg).ne' : ((a 0 : ℕ) : ℝ) ≠ 0)
    have h1 : ((a 1 : ℕ) : ℝ) ≠ 0 :=
      (by exact_mod_cast (Nat.pos_of_dvd_of_pos (hdvd 1) hg).ne' : ((a 1 : ℕ) : ℝ) ≠ 0)
    have h2 : ((a 2 : ℕ) : ℝ) ≠ 0 :=
      (by exact_mod_cast (Nat.pos_of_dvd_of_pos (hdvd 2) hg).ne' : ((a 2 : ℕ) : ℝ) ≠ 0)
    field_simp
    try ring
  calc ∑ a ∈ A,
        ∏ k : Fin 3,
          ∑ y ∈ (Finset.Icc 1 H).filter (fun y => y ≠ α ∧ a k ∣ del α y), wg m α y
      ≤ ∑ _a ∈ A, ((H : ℝ) * ((m.divisors.card : ℕ) : ℝ)) ^ 3 / (g : ℝ) :=
        Finset.sum_le_sum hprod_bound
    _ = ((A.card : ℕ) : ℝ) * (((H : ℝ) * ((m.divisors.card : ℕ) : ℝ)) ^ 3 / (g : ℝ)) := by
        rw [Finset.sum_const, nsmul_eq_mul]
    _ ≤ (((g.divisors.card : ℕ) : ℝ) ^ 2)
          * (((H : ℝ) * ((m.divisors.card : ℕ) : ℝ)) ^ 3 / (g : ℝ)) := by
        refine mul_le_mul_of_nonneg_right ?_ (by positivity)
        simpa [hA] using Work.LinnikBurgess.card_decompFinset_le hg
    _ = ((g.divisors.card : ℕ) : ℝ) ^ 2 * (H : ℝ) ^ 3
          * ((m.divisors.card : ℕ) : ℝ) ^ 3 / (g : ℝ) := by ring

/-- The `τ`-arithmetic closing Case S. -/
lemma sumS_arith (H m d g : ℕ) (hm : Squarefree m) (hd : 0 < d) (hg : 0 < g) :
    ((g.divisors.card : ℝ)) ^ 2 * ((m.divisors.card : ℝ)) ^ 4 * (H : ℝ) ^ 5 / (g : ℝ)
      ≤ rhsC 30000 H m d g := by
  have hm0 : m ≠ 0 := hm.ne_zero
  have hTpos : 0 < m * d * g := by positivity
  have hT1 : (1 : ℝ) ≤ (((m * d * g).divisors.card : ℕ) : ℝ) := by
    have : 1 ≤ (m * d * g).divisors.card :=
      Nat.one_le_iff_ne_zero.mpr
        (Finset.card_ne_zero.mpr ⟨_, Nat.mem_divisors_self _ hTpos.ne'⟩)
    exact_mod_cast this
  have hτg : ((g.divisors.card : ℕ) : ℝ) ≤ (((m * d * g).divisors.card : ℕ) : ℝ) := by
    have : g.divisors.card ≤ (m * d * g).divisors.card :=
      card_divisors_le_of_dvd ⟨m * d, by ring⟩ hTpos.ne'
    exact_mod_cast this
  have hτm : ((m.divisors.card : ℕ) : ℝ) ≤ (((m * d * g).divisors.card : ℕ) : ℝ) := by
    have : m.divisors.card ≤ (m * d * g).divisors.card :=
      card_divisors_le_of_dvd ⟨d * g, by ring⟩ hTpos.ne'
    exact_mod_cast this
  have hgR : (0 : ℝ) < (g : ℝ) := by exact_mod_cast hg
  have hdg : (0 : ℝ) < (d : ℝ) * (g : ℝ) := by
    have hdR : (0 : ℝ) < (d : ℝ) := by exact_mod_cast hd
    positivity
  have hmono : ((g.divisors.card : ℝ)) ^ 2 * ((m.divisors.card : ℝ)) ^ 4
      ≤ (((m * d * g).divisors.card : ℝ)) ^ 8 := by
    calc ((g.divisors.card : ℝ)) ^ 2 * ((m.divisors.card : ℝ)) ^ 4
        ≤ (((m * d * g).divisors.card : ℝ)) ^ 2
            * (((m * d * g).divisors.card : ℝ)) ^ 4 :=
          mul_le_mul (pow_le_pow_left₀ (by positivity) hτg 2)
            (pow_le_pow_left₀ (by positivity) hτm 4) (by positivity) (by positivity)
      _ = (((m * d * g).divisors.card : ℝ)) ^ 6 := by ring
      _ ≤ (((m * d * g).divisors.card : ℝ)) ^ 8 := pow_le_pow_right₀ hT1 (by norm_num)
  have hP : (0 : ℝ) ≤ (((m * d * g).divisors.card : ℝ)) ^ 8
      * ((H : ℝ) ^ 6 / ((d : ℝ) * (g : ℝ)) + (H : ℝ) ^ 5 / (g : ℝ)) := by positivity
  rw [rhsC]
  refine (?_ : ((g.divisors.card : ℝ)) ^ 2 * ((m.divisors.card : ℝ)) ^ 4 * (H : ℝ) ^ 5 / (g : ℝ)
      ≤ (((m * d * g).divisors.card : ℝ)) ^ 8
        * ((H : ℝ) ^ 6 / ((d : ℝ) * (g : ℝ)) + (H : ℝ) ^ 5 / (g : ℝ))).trans ?_
  · rw [mul_div_assoc]
    exact mul_le_mul hmono (le_add_of_nonneg_left (div_nonneg (by positivity) hdg.le))
      (div_nonneg (by positivity) hgR.le) (by positivity)
  · calc (((m * d * g).divisors.card : ℝ)) ^ 8
          * ((H : ℝ) ^ 6 / ((d : ℝ) * (g : ℝ)) + (H : ℝ) ^ 5 / (g : ℝ))
        ≤ 1 * ((((m * d * g).divisors.card : ℝ)) ^ 8
          * ((H : ℝ) ^ 6 / ((d : ℝ) * (g : ℝ)) + (H : ℝ) ^ 5 / (g : ℝ))) := by
          rw [one_mul]
      _ ≤ ((30000 : ℕ) : ℝ) * ((((m * d * g).divisors.card : ℝ)) ^ 8
          * ((H : ℝ) ^ 6 / ((d : ℝ) * (g : ℝ)) + (H : ℝ) ^ 5 / (g : ℝ))) :=
          mul_le_mul_of_nonneg_right (by norm_num) hP
      _ = ((30000 : ℕ) : ℝ) * (((m * d * g).divisors.card : ℝ)) ^ 8
          * ((H : ℝ) ^ 6 / ((d : ℝ) * (g : ℝ)) + (H : ℝ) ^ 5 / (g : ℝ)) := by ring

/-- **Case S estimate** (collapsed case `a 1 = a 2`).  With `m` squarefree, `gcd(m,d) = gcd(m,g) = 1`, `0 < d`, `0 < g`, this part of the master sum is at most `30000 · τ(m d g)^8 · (H^6/(dg) + H^5/g)`. -/
theorem sumS_le {H m d g : ℕ} (hm : Squarefree m) (hmd : Nat.Coprime m d) (hmg : Nat.Coprime m g)
    (hd : 0 < d) (hg : 0 < g) :
    sumS H m d g ≤ rhsC 30000 H m d g := by
  have hm0 : 0 < m := Nat.pos_of_ne_zero hm.ne_zero
  rw [sumS_eq_sum2]
  refine (Work.ZeroFreeTables.P9F.caseS_collapse H m d g).trans ?_
  have hstep : (∑ α ∈ Finset.Icc 1 H,
        Work.ZeroFreeTables.P9F.Ss H m α * Work.ZeroFreeTables.P9F.Ys H m g α)
      ≤ ∑ _α ∈ Finset.Icc 1 H,
          ((H : ℝ) * ((m.divisors.card : ℕ) : ℝ))
            * (((g.divisors.card : ℕ) : ℝ) ^ 2 * (H : ℝ) ^ 3
                * ((m.divisors.card : ℕ) : ℝ) ^ 3 / (g : ℝ)) := by
    refine Finset.sum_le_sum (fun α hα => ?_)
    exact mul_le_mul (sumS_ss_le H m hm0 α hα) (sumS_ys_le H m g hm0 hg hmg α hα)
      (Work.ZeroFreeTables.P9F.Ys_nonneg H m g α) (by positivity)
  have hsum : (∑ _α ∈ Finset.Icc 1 H,
        ((H : ℝ) * ((m.divisors.card : ℕ) : ℝ))
          * (((g.divisors.card : ℕ) : ℝ) ^ 2 * (H : ℝ) ^ 3
              * ((m.divisors.card : ℕ) : ℝ) ^ 3 / (g : ℝ)))
      = ((g.divisors.card : ℝ)) ^ 2 * ((m.divisors.card : ℝ)) ^ 4 * (H : ℝ) ^ 5 / (g : ℝ) := by
    rw [Finset.sum_const, Nat.card_Icc, nsmul_eq_mul, Nat.add_sub_cancel]
    push_cast
    ring
  exact (hstep.trans (le_of_eq hsum)).trans (sumS_arith H m d g hm hd hg)

end Work.LinnikBurgess
