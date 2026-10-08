import Mathlib
import Submission.Work.BrauerSuzuki.Q8.Ctx
import Submission.Work.BrauerSuzuki.Q8.Card
import Submission.Work.BrauerSuzuki.Q8.Eta
import Submission.Work.BrauerSuzuki.Q8.Eta2
import Submission.Work.BrauerSuzuki.Q8.step6_inner_eta
import Submission.Work.BrauerSuzuki.Q8.step9_one_notMem_Bset
import Submission.Work.BrauerSuzuki.Q8.step9_sum_sq_sub_sq
import Submission.Work.CharCore.Basic
import Submission.Work.CharCore.irr_orthonormal
import Submission.Work.CharCore.cfInner_int_vchar
import Submission.Work.CharCore.principalChar_mem_Irr
import Submission.Work.CharCore.step9_global_sums

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

/-!
# Glauberman (1974), step (9): `χᵢ(x) = εᵢ`

This file proves step (9) of Glauberman's block-free proof of the `Q₈` case of
Brauer–Suzuki (see `REFS/brauer_suzuki.md` §3):

> For each of the three irreducible characters `χᵢ` of `G` produced in step (2), and the sign
> `εᵢ = (χᵢ, η)_G = ±1`, one has `χᵢ(x) = εᵢ`.

The formalisation is self-contained in the hypotheses listed below; the argument is the
following chain of ordinary-character computations.

* Step (6) (`Work.BrauerSuzuki.Q8.step6_inner_eta`) identifies the inner product of a
  non-principal irreducible `χ` with `η` as the average `|H*|⁻¹ ∑_{u ∈ H*} χ (x u)`, so
  `hη` gives `∑_{u ∈ H*} χ (x u) = |H*| ε`; and `h6sq` gives the analogous identity
  `∑_{u ∈ H*} χ (x u)² = |H*| m` for the square, with `m = (χ², η)_G` odd (`h8sq`).
* Since `χ` is integer valued (`hint`), write `χ g = (a g : ℂ)` with `a : G → ℤ`. The
  variance identity `∑_{u ∈ H*} (a (x u) - e)² = |H*| (m - 1)` (with `ε = (e : ℂ)`,
  `e = ±1`) gives `1 ≤ m`.
* On the other hand, splitting `G` into the conjugates `B` of `A*` (where `η = 4`) and its
  complement (where `η = 0`), the global sums `∑_g a g = 0` and `∑_g (a g)² = |G|`
  give `4 ∑_{y ∈ B} a y = |G| e` and `4 ∑_{y ∈ B} (a y)² = |G| m`, whereas for every integer
  `n` and every sign `e = ±1` one has `n² + e n ≥ 0`, strictly at `n = a 1 ≥ 2` (`hdeg`).
  Summing over the complement of `B` yields `|G| (3 - m) > 0`, i.e. `m < 3`.
* With `m` odd, `1 ≤ m < 3` forces `m = 1`, and then the variance identity
  `∑_{u ∈ H*} (a (x u) - e)² = 0` forces `a (x · 1) = a x = e`, i.e. `χ x = ε`.
-/

set_option autoImplicit false

namespace Work.BrauerSuzuki.Q8

open Classical
open scoped Pointwise

open Classical in
theorem step9_chi_x {G : Type*} [Group G] [Fintype G] {x : G} {S : Sylow 2 G}
    (h : Work.BrauerSuzuki.Q8.Ctx G x S) {χ : G → ℂ} {ε : ℂ}
    (hIrr : χ ∈ Work.CharCore.Irr G) (hne : χ ≠ (fun _ => (1 : ℂ)))
    (hε : ε = 1 ∨ ε = -1)
    (hη : Work.CharCore.cfInner χ h.eta = ε)
    (h6sq : Work.CharCore.cfInner (χ ^ 2) h.eta =
      (Nat.card ↥(Work.BrauerSuzuki.Q8.Hstar x) : ℂ)⁻¹ *
        ∑ u : ↥(Work.BrauerSuzuki.Q8.Hstar x), (χ (x * (u : G))) ^ 2)
    (hint : ∀ g : G, ∃ n : ℤ, χ g = (n : ℂ))
    (h8 : ∃ n : ℤ, χ x = (n : ℂ) ∧ Odd n)
    (h8sq : ∃ m : ℤ, Work.CharCore.cfInner (χ ^ 2) h.eta = (m : ℂ) ∧ Odd m)
    (h4a : χ (x ^ 2) ≠ χ 1) (hdeg : 2 ≤ Work.CharCore.irrDeg χ) :
    χ x = ε := by
  classical
  -- ### Integer-valuedness of `χ`
  let a : G → ℤ := fun g => Classical.choose (hint g)
  have ha : ∀ g : G, χ g = (a g : ℂ) := fun g => Classical.choose_spec (hint g)
  -- ### The sign `ε = (e : ℂ)`, `e = ±1`; and `m` with `(χ², η) = m`
  obtain ⟨e, he, hepm⟩ : ∃ e : ℤ, (e : ℂ) = ε ∧ (e = 1 ∨ e = -1) := by
    rcases hε with h1 | h1
    · exact ⟨1, by rw [h1]; norm_num, Or.inl rfl⟩
    · exact ⟨-1, by rw [h1]; norm_num, Or.inr rfl⟩
  obtain ⟨m, hm, hmodd⟩ := h8sq
  have he_sq : e * e = 1 := by rcases hepm with rfl | rfl <;> norm_num
  have hcardC : (Fintype.card G : ℂ) ≠ 0 := by
    have h : Fintype.card G ≠ 0 := Fintype.card_ne_zero
    exact_mod_cast h
  have hNne : (Nat.card ↥(Hstar x) : ℂ) ≠ 0 := by
    have h : Nat.card ↥(Hstar x) ≠ 0 := by
      rw [Nat.card_eq_fintype_card]
      exact Fintype.card_ne_zero
    exact_mod_cast h
  -- ### Step (6) for `χ` and for `χ²`
  have hS1n : (∑ u : ↥(Hstar x), χ (x * (u : G))) = (Nat.card ↥(Hstar x) : ℂ) * ε := by
    have h6 := Work.BrauerSuzuki.Q8.step6_inner_eta h hIrr
    rw [hη] at h6
    calc ∑ u : ↥(Hstar x), χ (x * (u : G))
        = (Nat.card ↥(Hstar x) : ℂ) *
            ((Nat.card ↥(Hstar x) : ℂ)⁻¹ * ∑ u : ↥(Hstar x), χ (x * (u : G))) := by
          rw [← mul_assoc, mul_inv_cancel₀ hNne, one_mul]
      _ = (Nat.card ↥(Hstar x) : ℂ) * ε := by rw [← h6]
  have hS1 : (∑ u : ↥(Hstar x), χ (x * (u : G))) = (Fintype.card ↥(Hstar x) : ℂ) * ε := by
    rw [Fintype.card_eq_nat_card]; exact hS1n
  have hS2n : (∑ u : ↥(Hstar x), (χ (x * (u : G))) ^ 2) =
      (Nat.card ↥(Hstar x) : ℂ) * (m : ℂ) := by
    calc ∑ u : ↥(Hstar x), (χ (x * (u : G))) ^ 2
        = (Nat.card ↥(Hstar x) : ℂ) *
            ((Nat.card ↥(Hstar x) : ℂ)⁻¹ * ∑ u : ↥(Hstar x), (χ (x * (u : G))) ^ 2) := by
          rw [← mul_assoc, mul_inv_cancel₀ hNne, one_mul]
      _ = (Nat.card ↥(Hstar x) : ℂ) * Work.CharCore.cfInner (χ ^ 2) h.eta := by rw [h6sq]
      _ = (Nat.card ↥(Hstar x) : ℂ) * (m : ℂ) := by rw [hm]
  have hS2 : (∑ u : ↥(Hstar x), (χ (x * (u : G))) ^ 2) =
      (Fintype.card ↥(Hstar x) : ℂ) * (m : ℂ) := by
    rw [Fintype.card_eq_nat_card]; exact hS2n
  -- ### The same sums over `ℤ`
  have hS1z : (∑ u : ↥(Hstar x), a (x * (u : G))) = (Fintype.card ↥(Hstar x) : ℤ) * e := by
    apply Int.cast_injective (α := ℂ)
    push_cast
    rw [show (∑ u : ↥(Hstar x), ((a (x * (u : G)) : ℤ) : ℂ))
          = ∑ u : ↥(Hstar x), χ (x * (u : G)) from
        Finset.sum_congr rfl (fun u _ => (ha (x * (u : G))).symm)]
    rw [hS1, he]
  have hS2z : (∑ u : ↥(Hstar x), (a (x * (u : G))) ^ 2) = (Fintype.card ↥(Hstar x) : ℤ) * m := by
    apply Int.cast_injective (α := ℂ)
    push_cast
    rw [show (∑ u : ↥(Hstar x), ((a (x * (u : G)) : ℤ) : ℂ) ^ 2)
          = ∑ u : ↥(Hstar x), (χ (x * (u : G))) ^ 2 from
        Finset.sum_congr rfl (fun u _ => by rw [(ha (x * (u : G))).symm])]
    rw [hS2]
  -- ### Variance: `1 ≤ m`
  have hvar : (∑ u : ↥(Hstar x), (a (x * (u : G)) - e) ^ 2) =
      (Fintype.card ↥(Hstar x) : ℤ) * (m - 1) :=
    step9_sum_sq_sub_sq (fun u : ↥(Hstar x) => a (x * (u : G))) he_sq hS1z hS2z
  have hm_ge : 1 ≤ m := by
    have hnn : (0 : ℤ) ≤ ∑ u : ↥(Hstar x), (a (x * (u : G)) - e) ^ 2 :=
      Finset.sum_nonneg (fun u _ => sq_nonneg _)
    rw [hvar] at hnn
    have hpos : (0 : ℤ) < (Fintype.card ↥(Hstar x) : ℤ) := by
      have h : 0 < Fintype.card ↥(Hstar x) := Fintype.card_pos
      exact_mod_cast h
    have := (mul_nonneg_iff_of_pos_left hpos).mp hnn
    omega
  -- ### The global sums of section 2 (Dade 4.20 / 4.31)
  obtain ⟨hsum0, hsum2⟩ := Work.CharCore.step9_global_sums hIrr hne ha
  -- ### The values of `η`; `η = 4` on `B` and `0` off it
  have hstar_eta : ∀ y : G, starRingEnd ℂ (h.eta y) = h.eta y := by
    intro y
    by_cases hy : y ∈ Bset x
    · rw [h.eta_apply_Bset hy, map_ofNat]
    · rw [h.eta_apply_notMem_Bset hy, map_zero]
  have heta_chi : (∑ y : G, χ y * h.eta y) = (Fintype.card G : ℂ) * ε := by
    have hc := hη
    rw [Work.CharCore.cfInner_apply] at hc
    have hmul : (Fintype.card G : ℂ) *
        ((Fintype.card G : ℂ)⁻¹ * ∑ y : G, χ y * starRingEnd ℂ (h.eta y))
        = (Fintype.card G : ℂ) * ε := by rw [hc]
    rw [← mul_assoc, mul_inv_cancel₀ hcardC, one_mul] at hmul
    rw [← hmul]
    exact Finset.sum_congr rfl (fun y _ => by rw [hstar_eta y])
  have hB_chi : (4 : ℂ) * ∑ y ∈ (Finset.univ.filter (fun y : G => y ∈ Bset x)), χ y
      = (Fintype.card G : ℂ) * ε := by
    have h1 : (∑ y : G, χ y * h.eta y)
        = ∑ y : G, (if y ∈ Bset x then 4 * χ y else 0) :=
      Finset.sum_congr rfl (fun y _ => by
        by_cases hy : y ∈ Bset x
        · rw [h.eta_apply_Bset hy, if_pos hy]; ring
        · rw [h.eta_apply_notMem_Bset hy, if_neg hy, mul_zero])
    have h2 : (∑ y : G, (if y ∈ Bset x then 4 * χ y else 0))
        = 4 * ∑ y ∈ (Finset.univ.filter (fun y : G => y ∈ Bset x)), χ y := by
      rw [Finset.mul_sum]
      exact (Finset.sum_filter (fun y : G => y ∈ Bset x) (fun y => (4 : ℂ) * χ y)).symm
    rw [← heta_chi, h1, h2]
  have hB_chi_sq : (4 : ℂ) *
      ∑ y ∈ (Finset.univ.filter (fun y : G => y ∈ Bset x)), (χ y) ^ 2
      = (Fintype.card G : ℂ) * (m : ℂ) := by
    have hc := hm
    rw [Work.CharCore.cfInner_apply] at hc
    have hsub : (∑ y : G, (χ ^ 2) y * starRingEnd ℂ (h.eta y))
        = ∑ y : G, (χ y) ^ 2 * h.eta y := by
      refine Finset.sum_congr rfl (fun y _ => ?_)
      have h2 : (χ ^ 2) y = (χ y) ^ 2 := by simp
      rw [h2, hstar_eta y]
    rw [hsub] at hc
    have hmul : (Fintype.card G : ℂ) *
        ((Fintype.card G : ℂ)⁻¹ * ∑ y : G, (χ y) ^ 2 * h.eta y)
        = (Fintype.card G : ℂ) * (m : ℂ) := by rw [hc]
    rw [← mul_assoc, mul_inv_cancel₀ hcardC, one_mul] at hmul
    have h1 : (∑ y : G, (χ y) ^ 2 * h.eta y)
        = ∑ y : G, (if y ∈ Bset x then 4 * (χ y) ^ 2 else 0) :=
      Finset.sum_congr rfl (fun y _ => by
        by_cases hy : y ∈ Bset x
        · rw [h.eta_apply_Bset hy, if_pos hy]; ring
        · rw [h.eta_apply_notMem_Bset hy, if_neg hy, mul_zero])
    have h2 : (∑ y : G, (if y ∈ Bset x then 4 * (χ y) ^ 2 else 0))
        = 4 * ∑ y ∈ (Finset.univ.filter (fun y : G => y ∈ Bset x)), (χ y) ^ 2 := by
      rw [Finset.mul_sum]
      exact (Finset.sum_filter (fun y : G => y ∈ Bset x)
        (fun y => (4 : ℂ) * (χ y) ^ 2)).symm
    rw [h1, h2] at hmul
    exact hmul
  -- ### The companion sums over `B` in `ℤ`
  have hA : 4 * ∑ y ∈ (Finset.univ.filter (fun y : G => y ∈ Bset x)), a y
      = (Fintype.card G : ℤ) * e := by
    apply Int.cast_injective (α := ℂ)
    push_cast
    rw [show (∑ y ∈ (Finset.univ.filter (fun y : G => y ∈ Bset x)), ((a y : ℤ) : ℂ))
          = ∑ y ∈ (Finset.univ.filter (fun y : G => y ∈ Bset x)), χ y from
        Finset.sum_congr rfl (fun y _ => (ha y).symm)]
    rw [hB_chi, he]
  have hB : 4 * ∑ y ∈ (Finset.univ.filter (fun y : G => y ∈ Bset x)), (a y) ^ 2
      = (Fintype.card G : ℤ) * m := by
    apply Int.cast_injective (α := ℂ)
    push_cast
    rw [show (∑ y ∈ (Finset.univ.filter (fun y : G => y ∈ Bset x)), ((a y : ℤ) : ℂ) ^ 2)
          = ∑ y ∈ (Finset.univ.filter (fun y : G => y ∈ Bset x)), (χ y) ^ 2 from
        Finset.sum_congr rfl (fun y _ => by rw [(ha y).symm])]
    rw [hB_chi_sq]
  -- ### Splitting the group into `B` and its complement
  have hsplitC : ∀ f : G → ℤ,
      (∑ y ∈ (Finset.univ.filter (fun y : G => y ∈ Bset x)), f y)
        + (∑ y ∈ (Finset.univ.filter (fun y : G => y ∉ Bset x)), f y) = ∑ y : G, f y :=
    fun f => Finset.sum_filter_add_sum_filter_not (Finset.univ : Finset G)
      (fun y : G => y ∈ Bset x) f
  have hC : (∑ y ∈ (Finset.univ.filter (fun y : G => y ∈ Bset x)), a y)
      + (∑ y ∈ (Finset.univ.filter (fun y : G => y ∉ Bset x)), a y) = 0 := by
    rw [hsplitC a, hsum0]
  have hD : (∑ y ∈ (Finset.univ.filter (fun y : G => y ∈ Bset x)), (a y) ^ 2)
      + (∑ y ∈ (Finset.univ.filter (fun y : G => y ∉ Bset x)), (a y) ^ 2)
      = (Fintype.card G : ℤ) := by
    rw [hsplitC (fun y : G => (a y) ^ 2), hsum2]
  -- ### The sums over the complement of `B`
  have hCa : 4 * (∑ y ∈ (Finset.univ.filter (fun y : G => y ∉ Bset x)), a y)
      = -((Fintype.card G : ℤ) * e) := by
    have h1 : (∑ y ∈ (Finset.univ.filter (fun y : G => y ∉ Bset x)), a y)
        = -(∑ y ∈ (Finset.univ.filter (fun y : G => y ∈ Bset x)), a y) := by
      linarith [hC]
    rw [h1, mul_neg, hA]
  have hCa2 : 4 * (∑ y ∈ (Finset.univ.filter (fun y : G => y ∉ Bset x)), (a y) ^ 2)
      = (Fintype.card G : ℤ) * (4 - m) := by
    have h1 : (∑ y ∈ (Finset.univ.filter (fun y : G => y ∉ Bset x)), (a y) ^ 2)
        = (Fintype.card G : ℤ)
          - (∑ y ∈ (Finset.univ.filter (fun y : G => y ∈ Bset x)), (a y) ^ 2) := by
      linarith [hD]
    rw [h1, mul_sub, hB]; ring
  -- ### The key inequality
  have ha1 : (2 : ℤ) ≤ a 1 := by
    have h2 : a 1 = (Work.CharCore.irrDeg χ : ℤ) := by
      apply Int.cast_injective (α := ℂ)
      push_cast
      rw [← ha 1, Work.CharCore.irrDeg_spec hIrr]
    have h3 : (2 : ℤ) ≤ (Work.CharCore.irrDeg χ : ℤ) := by exact_mod_cast hdeg
    omega
  have hE : 4 * (∑ y ∈ (Finset.univ.filter (fun y : G => y ∉ Bset x)),
        ((a y) ^ 2 + e * (a y))) = (Fintype.card G : ℤ) * (3 - m) := by
    have hsplit : (∑ y ∈ (Finset.univ.filter (fun y : G => y ∉ Bset x)),
          ((a y) ^ 2 + e * (a y)))
        = (∑ y ∈ (Finset.univ.filter (fun y : G => y ∉ Bset x)), (a y) ^ 2)
          + e * (∑ y ∈ (Finset.univ.filter (fun y : G => y ∉ Bset x)), a y) := by
      rw [Finset.sum_add_distrib, ← Finset.mul_sum]
    rw [hsplit]
    have h1 : 4 * ((∑ y ∈ (Finset.univ.filter (fun y : G => y ∉ Bset x)), (a y) ^ 2)
          + e * (∑ y ∈ (Finset.univ.filter (fun y : G => y ∉ Bset x)), a y))
        = 4 * (∑ y ∈ (Finset.univ.filter (fun y : G => y ∉ Bset x)), (a y) ^ 2)
          + e * (4 * (∑ y ∈ (Finset.univ.filter (fun y : G => y ∉ Bset x)), a y)) := by
      ring
    rw [h1, hCa2, hCa]
    have he2 : e ^ 2 = 1 := by rw [pow_two, he_sq]
    rw [show e * (-((Fintype.card G : ℤ) * e)) = -((Fintype.card G : ℤ) * e ^ 2) from by
      ring, he2]
    ring
  have hpos : 0 < ∑ y ∈ (Finset.univ.filter (fun y : G => y ∉ Bset x)),
      ((a y) ^ 2 + e * (a y)) := by
    have hnonneg : ∀ y ∈ (Finset.univ.filter (fun y : G => y ∉ Bset x)),
        0 ≤ (a y) ^ 2 + e * (a y) := by
      intro y _
      rcases hepm with h | h <;> rw [h] <;> nlinarith [sq_nonneg (a y)]
    have h1mem : (1 : G) ∈ Finset.univ.filter (fun y : G => y ∉ Bset x) :=
      Finset.mem_filter.mpr ⟨Finset.mem_univ _, step9_one_notMem_Bset⟩
    have h1pos : 0 < (a 1) ^ 2 + e * (a 1) := by
      rcases hepm with h | h <;> rw [h] <;> nlinarith [ha1, sq_nonneg (a 1)]
    exact lt_of_lt_of_le h1pos (Finset.single_le_sum hnonneg h1mem)
  -- ### `m < 3`, hence `m = 1`
  have hm_lt : m < 3 := by
    have hGpos : (0 : ℤ) < (Fintype.card G : ℤ) := by
      have h : 0 < Fintype.card G := Fintype.card_pos
      exact_mod_cast h
    have hprod : (0 : ℤ) < (Fintype.card G : ℤ) * (3 - m) := by
      rw [← hE]; linarith
    have := (mul_pos_iff_of_pos_left hGpos).mp hprod
    omega
  have hm_eq : m = 1 := by
    obtain ⟨k, hk⟩ := hmodd
    omega
  -- ### Conclusion
  have hax : a x = e := by
    have hzero : (∑ u : ↥(Hstar x), (a (x * (u : G)) - e) ^ 2) = 0 := by
      rw [hvar, hm_eq]; ring
    have hnonneg : ∀ u ∈ (Finset.univ : Finset ↥(Hstar x)),
        0 ≤ (a (x * (u : G)) - e) ^ 2 := fun u _ => sq_nonneg _
    have hall := (Finset.sum_eq_zero_iff_of_nonneg hnonneg).mp hzero
    have h1 := hall ⟨1, (Hstar x).one_mem⟩ (Finset.mem_univ _)
    have h2 : a (x * ((⟨1, (Hstar x).one_mem⟩ : ↥(Hstar x)) : G)) - e = 0 :=
      (pow_eq_zero_iff (by norm_num : (2 : ℕ) ≠ 0)).mp h1
    rw [show ((⟨1, (Hstar x).one_mem⟩ : ↥(Hstar x)) : G) = 1 from rfl, mul_one] at h2
    exact sub_eq_zero.mp h2
  rw [ha x, hax, he]

end Work.BrauerSuzuki.Q8
