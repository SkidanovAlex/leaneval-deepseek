import Mathlib
import Submission.Work.FIArea4.WdyadGen.Wdyad_strata_defs
import Submission.Work.FIArea4.WdyadGen.TZbox_one_bound

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

/-!
# The energy of a single modulus zone `TZone`

For a single modulus `d₀` and a fixed `r` coprime to `d₀`, the class sum

`TZone d₀ β r s = ∑_{a < d₀} β a d₀ · Mentry d₀ a r s`

collapses to a *single* term: the congruence `s ≡ r a (mod d₀)` has the unique solution
`a = solA d₀ r s` (the representative in `[0,d₀)` of `r⁻¹ s`), and `Mentry d₀ a r s` is the
Jacobi symbol `(r | d₀')` times the indicator of that congruence.  Consequently

`|TZone d₀ β r s|² ≤ |β (solA d₀ r s) d₀|²`,

and since `s ↦ solA d₀ r s` is `d₀`-periodic, summing over any interval `(lo,hi]` gives at most
`((hi-lo)/d₀ + 1)` copies of the row energy `rowE β d₀ = ∑_{a<d₀} |β a d₀|²`.  Summing in `r`
over the dyadic window `(R,2R]` (which has `R` elements) yields `TZone_energy_le`.

Everything is elementary; the only number theory is the fact that multiplication by the unit
`r⁻¹` permutes `ZMod d₀` (so the period sum is exactly the row energy).
-/

namespace Work.FIArea4.WdyadGen

open Finset
open scoped BigOperators

attribute [local instance] Classical.propDecidable

noncomputable section

/-! ## Periodic sums over an arbitrary interval -/

/-- A `d`-periodic nonnegative function summed over an arbitrary interval `(lo,hi]` is bounded by
`((hi-lo)/d + 1)` times its period sum. -/
lemma sum_Ioc_periodic_le_general (d : ℕ) (hd : 0 < d) (g : ℕ → ℝ)
    (hper : ∀ r, g (r + d) = g r) (h0 : ∀ r, 0 ≤ g r) (lo hi : ℕ) :
    ∑ s ∈ Finset.Ioc lo hi, g s ≤ (((hi - lo : ℕ) : ℝ) / d + 1) * ∑ c ∈ Finset.range d, g c := by
  set M : ℕ := (hi - lo) / d + 1 with hM
  have hlt : hi - lo < M * d := by
    have hmod : (hi - lo) % d < d := Nat.mod_lt _ hd
    have hdm : d * ((hi - lo) / d) + (hi - lo) % d = hi - lo := Nat.div_add_mod (hi - lo) d
    calc hi - lo = d * ((hi - lo) / d) + (hi - lo) % d := hdm.symm
      _ < d * ((hi - lo) / d) + d := by omega
      _ = M * d := by rw [hM]; ring
  have hleh : hi ≤ lo + M * d := by
    by_cases h : hi ≤ lo
    · exact le_trans h (Nat.le_add_right lo (M * d))
    · push_neg at h
      have h2 : hi - lo + lo = hi := Nat.sub_add_cancel (le_of_lt h)
      have h3 : hi - lo ≤ M * d := le_of_lt hlt
      calc hi = hi - lo + lo := h2.symm
        _ ≤ M * d + lo := Nat.add_le_add_right h3 lo
        _ = lo + M * d := Nat.add_comm _ _
  calc ∑ s ∈ Finset.Ioc lo hi, g s
      ≤ ∑ s ∈ Finset.Ioc lo (lo + M * d), g s :=
        Finset.sum_le_sum_of_subset_of_nonneg (Finset.Ioc_subset_Ioc_right hleh)
          (fun x _ _ => h0 x)
    _ = M * ∑ c ∈ Finset.range d, g c := sum_Ioc_periodic_mul d hd g hper lo M
    _ ≤ (((hi - lo : ℕ) : ℝ) / d + 1) * ∑ c ∈ Finset.range d, g c := by
        apply mul_le_mul_of_nonneg_right _ (Finset.sum_nonneg (fun c _ => h0 c))
        have h4 : ((M : ℕ) : ℝ) ≤ ((hi - lo : ℕ) : ℝ) / d + 1 := by
          rw [hM]; push_cast
          have := Nat.cast_div_le (α := ℝ) (m := hi - lo) (n := d)
          linarith
        exact h4

/-! ## The solution `a` of `r a ≡ s (mod d₀)` -/

/-- The unique residue class `a ∈ [0,d)` solving `r a ≡ s (mod d)`, realised as the `Nat`-value of
`r⁻¹ · s` (valid whenever `r` is a unit of `ZMod d`, i.e. `(r,d) = 1`). -/
def solA (d : ℕ) (r s : ℕ) (hc : Nat.Coprime r d) : ℕ :=
  ((↑((ZMod.unitOfCoprime r hc)⁻¹ : (ZMod d)ˣ) : ZMod d) * (s : ZMod d)).val

lemma solA_lt (d r s : ℕ) (hd : 1 ≤ d) (hc : Nat.Coprime r d) : solA d r s hc < d := by
  haveI : NeZero d := ⟨by omega⟩
  unfold solA
  exact ZMod.val_lt _

/-- `solA d r s` solves the congruence `r a ≡ s (mod d)`. -/
lemma solA_spec (d r s : ℕ) (hd : 1 ≤ d) (hc : Nat.Coprime r d) :
    (r : ZMod d) * (solA d r s hc : ZMod d) = (s : ZMod d) := by
  haveI : NeZero d := ⟨by omega⟩
  unfold solA
  rw [ZMod.natCast_zmod_val, ← ZMod.coe_unitOfCoprime r hc, ← mul_assoc, Units.mul_inv, one_mul]

/-- The solution of `r a ≡ s (mod d)` in `[0,d)` is unique when `(r,d) = 1`. -/
lemma solA_unique (d r s a : ℕ) (hd : 1 ≤ d) (hc : Nat.Coprime r d)
    (ha : a < d) (h : (s : ZMod d) = (r : ZMod d) * (a : ZMod d)) :
    a = solA d r s hc := by
  haveI : NeZero d := ⟨by omega⟩
  have hval : (a : ZMod d)
      = (↑((ZMod.unitOfCoprime r hc)⁻¹ : (ZMod d)ˣ) : ZMod d) * (s : ZMod d) := by
    have hkey : (↑((ZMod.unitOfCoprime r hc)⁻¹ : (ZMod d)ˣ) : ZMod d)
        * (↑(ZMod.unitOfCoprime r hc) : ZMod d) = 1 := Units.inv_mul _
    calc (a : ZMod d) = 1 * (a : ZMod d) := (one_mul _).symm
      _ = ((↑((ZMod.unitOfCoprime r hc)⁻¹ : (ZMod d)ˣ) : ZMod d)
            * (↑(ZMod.unitOfCoprime r hc) : ZMod d)) * (a : ZMod d) := by rw [hkey]
      _ = (↑((ZMod.unitOfCoprime r hc)⁻¹ : (ZMod d)ˣ) : ZMod d)
            * ((↑(ZMod.unitOfCoprime r hc) : ZMod d) * (a : ZMod d)) := by ring
      _ = (↑((ZMod.unitOfCoprime r hc)⁻¹ : (ZMod d)ˣ) : ZMod d)
            * ((r : ZMod d) * (a : ZMod d)) := by rw [ZMod.coe_unitOfCoprime]
      _ = (↑((ZMod.unitOfCoprime r hc)⁻¹ : (ZMod d)ˣ) : ZMod d) * (s : ZMod d) := by rw [← h]
  have := congrArg ZMod.val hval
  rw [ZMod.val_natCast_of_lt ha] at this
  rw [solA]
  exact this

/-! ## The single-term collapse of `TZone` -/

/-- When `(r,d) = 1`, the entry `Mentry d a r s` is the Jacobi symbol times the indicator of the
congruence `s ≡ r a (mod d)`. -/
lemma Mentry_coprime_eq (d a r s : ℕ) (hc : Nat.Coprime r d) :
    Work.FIArea4.Mentry d a r s
      = ((jacobiSym (r : ℤ) (Work.FIPlan.oddPart d) : ℤ) : ℂ)
        * (if (s : ZMod d) = (r : ZMod d) * (a : ZMod d) then 1 else 0) := by
  rw [Work.FIArea4.Mentry]
  by_cases h : (s : ZMod d) = (r : ZMod d) * (a : ZMod d)
  · rw [if_pos ⟨hc, h⟩, if_pos h, mul_one]
  · rw [if_neg (fun hc' => h hc'.2), if_neg h, mul_zero]

/-- The `a`-sum defining `TZone` collapses to the single term `a = solA d r s`. -/
lemma TZone_collapse (d : ℕ) (hd : 1 ≤ d) (β : ℕ → ℕ → ℂ) (r s : ℕ) (hc : Nat.Coprime r d) :
    TZone d β r s
      = ((jacobiSym (r : ℤ) (Work.FIPlan.oddPart d) : ℤ) : ℂ) * β (solA d r s hc) d := by
  haveI : NeZero d := ⟨by omega⟩
  have hsum : (∑ a ∈ Finset.range d, β a d * Work.FIArea4.Mentry d a r s)
      = ((jacobiSym (r : ℤ) (Work.FIPlan.oddPart d) : ℤ) : ℂ)
        * ∑ a ∈ Finset.range d,
            β a d * (if (s : ZMod d) = (r : ZMod d) * (a : ZMod d) then 1 else 0) := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro a _
    rw [Mentry_coprime_eq d a r s hc]
    ring
  rw [TZone, hsum]
  congr 1
  rw [Finset.sum_eq_single (solA d r s hc)]
  · rw [if_pos (solA_spec d r s hd hc).symm, mul_one]
  · intro a ha hne
    rw [if_neg (fun h => hne (solA_unique d r s a hd hc (Finset.mem_range.mp ha) h)), mul_zero]
  · intro hnotmem
    exact absurd (Finset.mem_range.mpr (solA_lt d r s hd hc)) hnotmem

/-- Pointwise bound: the modulus of `TZone` is at most the modulus of the single surviving
coefficient. -/
lemma normSq_TZone_le (d : ℕ) (hd : 1 ≤ d) (β : ℕ → ℕ → ℂ) (r s : ℕ) (hc : Nat.Coprime r d) :
    Complex.normSq (TZone d β r s) ≤ Complex.normSq (β (solA d r s hc) d) := by
  rw [TZone_collapse d hd β r s hc, Complex.normSq_mul]
  calc Complex.normSq ((jacobiSym (r : ℤ) (Work.FIPlan.oddPart d) : ℤ) : ℂ)
          * Complex.normSq (β (solA d r s hc) d)
      ≤ 1 * Complex.normSq (β (solA d r s hc) d) :=
        mul_le_mul_of_nonneg_right (normSq_jacobiSym_le_one r (Work.FIPlan.oddPart d))
          (Complex.normSq_nonneg _)
    _ = Complex.normSq (β (solA d r s hc) d) := one_mul _

/-- `TZone` vanishes identically when `(r,d) ≠ 1`. -/
lemma TZone_eq_zero_of_not_coprime (d : ℕ) (β : ℕ → ℕ → ℂ) (r s : ℕ)
    (h : ¬ Nat.Coprime r d) : TZone d β r s = 0 := by
  rw [TZone]
  apply Finset.sum_eq_zero
  intro a _
  have hcond : ¬ (Nat.Coprime r d ∧ (s : ZMod d) = (r : ZMod d) * (a : ZMod d)) :=
    fun hc => h hc.1
  rw [Work.FIArea4.Mentry, if_neg hcond, mul_zero]

/-! ## The period sum is the row energy -/

/-- The (period) sum of `‖β (solA d r c) d‖²` over `c < d` is exactly the row energy: the map
`c ↦ solA d r c` is the permutation of `[0,d)` induced by multiplication by the unit `r⁻¹`. -/
lemma sum_range_normSq_solA (d : ℕ) (hd : 1 ≤ d) (β : ℕ → ℕ → ℂ) (r : ℕ)
    (hc : Nat.Coprime r d) :
    (∑ c ∈ Finset.range d, Complex.normSq (β (solA d r c hc) d)) = rowE β d := by
  haveI : NeZero d := ⟨by omega⟩
  set U1 : (ZMod d)ˣ := (ZMod.unitOfCoprime r hc)⁻¹ with hU1
  set U0 : (ZMod d)ˣ := ZMod.unitOfCoprime r hc with hU0
  have hVW : (↑U1 : ZMod d) * (↑U0 : ZMod d) = 1 := by rw [hU1, hU0]; exact Units.inv_mul _
  have hWV : (↑U0 : ZMod d) * (↑U1 : ZMod d) = 1 := by rw [hU1, hU0]; exact Units.mul_inv _
  have hsolfun : ∀ c, solA d r c hc = ((↑U1 : ZMod d) * (c : ZMod d)).val := by
    intro c
    unfold solA
    rw [hU1]
  rw [rowE]
  have hcongr : (∑ c ∈ Finset.range d, Complex.normSq (β (solA d r c hc) d))
      = ∑ c ∈ Finset.range d, Complex.normSq (β (((↑U1 : ZMod d) * (c : ZMod d)).val) d) := by
    apply Finset.sum_congr rfl
    intro c _
    rw [hsolfun c]
  rw [hcongr]
  refine Finset.sum_bij (fun c _ => ((↑U1 : ZMod d) * (c : ZMod d)).val) ?_ ?_ ?_ ?_
  · intro c _
    exact Finset.mem_range.mpr (ZMod.val_lt _)
  · intro c1 hc1 c2 hc2 heq
    have hEq : (↑U1 : ZMod d) * (c1 : ZMod d) = (↑U1 : ZMod d) * (c2 : ZMod d) := by
      have h2 : ((((↑U1 : ZMod d) * (c1 : ZMod d)).val : ℕ) : ZMod d)
          = ((((↑U1 : ZMod d) * (c2 : ZMod d)).val : ℕ) : ZMod d) := by rw [heq]
      rwa [ZMod.natCast_zmod_val, ZMod.natCast_zmod_val] at h2
    have hz : (c1 : ZMod d) = (c2 : ZMod d) := by
      have := congrArg (fun x => (↑U0 : ZMod d) * x) hEq
      simp only [← mul_assoc, hWV, one_mul] at this
      exact this
    have := congrArg ZMod.val hz
    rwa [ZMod.val_natCast_of_lt (Finset.mem_range.mp hc1),
        ZMod.val_natCast_of_lt (Finset.mem_range.mp hc2)] at this
  · intro a ha
    refine ⟨((↑U0 : ZMod d) * (a : ZMod d)).val, Finset.mem_range.mpr (ZMod.val_lt _), ?_⟩
    have hc0 : ((((↑U0 : ZMod d) * (a : ZMod d)).val : ℕ) : ZMod d)
        = (↑U0 : ZMod d) * (a : ZMod d) := ZMod.natCast_zmod_val _
    rw [hc0]
    have hkey : (↑U1 : ZMod d) * ((↑U0 : ZMod d) * (a : ZMod d)) = (a : ZMod d) := by
      rw [← mul_assoc, hVW, one_mul]
    rw [hkey, ZMod.val_natCast_of_lt (Finset.mem_range.mp ha)]
  · intro c _
    rfl

/-! ## The per-`r` bound and the final energy estimate -/

/-- For a fixed `r` coprime to `d`, the `s`-energy of `TZone` is bounded by
`((hi-lo)/d + 1)` times the row energy. -/
lemma TZone_s_sum_le (d : ℕ) (hd : 1 ≤ d) (β : ℕ → ℕ → ℂ) (r : ℕ) (hc : Nat.Coprime r d)
    (lo hi : ℕ) :
    ∑ s ∈ Finset.Ioc lo hi, Complex.normSq (TZone d β r s)
      ≤ (((hi - lo : ℕ) : ℝ) / d + 1) * rowE β d := by
  have hpt : ∀ s, Complex.normSq (TZone d β r s) ≤ Complex.normSq (β (solA d r s hc) d) :=
    fun s => normSq_TZone_le d hd β r s hc
  have hper : ∀ s, (fun t => Complex.normSq (β (solA d r t hc) d)) (s + d)
      = (fun t => Complex.normSq (β (solA d r t hc) d)) s := by
    intro s
    show Complex.normSq (β (solA d r (s + d) hc) d) = Complex.normSq (β (solA d r s hc) d)
    have hcast : ((s + d : ℕ) : ZMod d) = (s : ZMod d) := by
      rw [Nat.cast_add, ZMod.natCast_self, add_zero]
    have hs : solA d r (s + d) hc = solA d r s hc := by
      unfold solA
      rw [hcast]
    rw [hs]
  have hb := sum_Ioc_periodic_le_general d (by omega)
    (fun t => Complex.normSq (β (solA d r t hc) d)) hper
    (fun t => Complex.normSq_nonneg _) lo hi
  have hperiod : (∑ c ∈ Finset.range d, Complex.normSq (β (solA d r c hc) d)) = rowE β d :=
    sum_range_normSq_solA d hd β r hc
  calc ∑ s ∈ Finset.Ioc lo hi, Complex.normSq (TZone d β r s)
      ≤ ∑ s ∈ Finset.Ioc lo hi, Complex.normSq (β (solA d r s hc) d) :=
        Finset.sum_le_sum (fun s _ => hpt s)
    _ ≤ (((hi - lo : ℕ) : ℝ) / d + 1)
          * ∑ c ∈ Finset.range d, Complex.normSq (β (solA d r c hc) d) := hb
    _ = (((hi - lo : ℕ) : ℝ) / d + 1) * rowE β d := by rw [hperiod]

theorem TZone_energy_le (d₀ : ℕ) (hd₀ : 1 ≤ d₀) (β : ℕ → ℕ → ℂ) (R lo hi : ℕ) :
    ∑ r ∈ Finset.Ioc R (2 * R), ∑ s ∈ Finset.Ioc lo hi,
        Complex.normSq (Work.FIArea4.WdyadGen.TZone d₀ β r s)
      ≤ (R : ℝ) * (((hi - lo : ℕ) : ℝ) / d₀ + 1)
          * (Work.FIArea4.WdyadGen.rowE β d₀) := by
  have hnn : (0 : ℝ) ≤ (((hi - lo : ℕ) : ℝ) / d₀ + 1) := by
    have hd0 : (0 : ℝ) < d₀ := by exact_mod_cast (by omega : 0 < d₀)
    have := div_nonneg (Nat.cast_nonneg (hi - lo)) (le_of_lt hd0)
    linarith
  have hr : ∀ r, ∑ s ∈ Finset.Ioc lo hi, Complex.normSq (TZone d₀ β r s)
      ≤ (((hi - lo : ℕ) : ℝ) / d₀ + 1) * rowE β d₀ := by
    intro r
    by_cases hc : Nat.Coprime r d₀
    · exact TZone_s_sum_le d₀ hd₀ β r hc lo hi
    · have hz : (∑ s ∈ Finset.Ioc lo hi, Complex.normSq (TZone d₀ β r s)) = 0 := by
        apply Finset.sum_eq_zero
        intro s _
        rw [TZone_eq_zero_of_not_coprime d₀ β r s hc, Complex.normSq_zero]
      rw [hz]
      exact mul_nonneg hnn (rowE_nonneg β d₀)
  calc ∑ r ∈ Finset.Ioc R (2 * R), ∑ s ∈ Finset.Ioc lo hi, Complex.normSq (TZone d₀ β r s)
      ≤ ∑ r ∈ Finset.Ioc R (2 * R), (((hi - lo : ℕ) : ℝ) / d₀ + 1) * rowE β d₀ :=
        Finset.sum_le_sum (fun r _ => hr r)
    _ = ((Finset.Ioc R (2 * R)).card : ℝ)
          * ((((hi - lo : ℕ) : ℝ) / d₀ + 1) * rowE β d₀) := by
        rw [Finset.sum_const, nsmul_eq_mul]
    _ = (R : ℝ) * ((((hi - lo : ℕ) : ℝ) / d₀ + 1) * rowE β d₀) := by
        rw [Nat.card_Ioc, show 2 * R - R = R from by omega]
    _ = (R : ℝ) * (((hi - lo : ℕ) : ℝ) / d₀ + 1) * (rowE β d₀) := by ring

end

end Work.FIArea4.WdyadGen
