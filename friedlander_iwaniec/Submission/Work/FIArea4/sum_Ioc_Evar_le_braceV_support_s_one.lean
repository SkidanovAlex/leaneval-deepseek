import Mathlib
import Submission.Work.FIArea4.prop_11_1_defs
import Submission.Work.FIPlan.Interface
import Submission.Work.FIArea4.Evar_le_trivial

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

namespace Work.FIArea4

open Finset
open scoped BigOperators

attribute [local instance] Classical.propDecidable

noncomputable section

/-- The `r`-set contributing to the residue class `a (mod d)` when the coefficient matrix is
supported on `s = 1`: those `r ∈ [1, 2R]` coprime to `d` with `r a ≡ 1 (mod d)`. -/
def EvarR1 (R d a : ℕ) : Finset ℕ :=
  (EvarR R d).filter (fun r => (1 : ZMod d) = (r : ZMod d) * (a : ZMod d))

lemma mem_EvarR1 {R d a r : ℕ} :
    r ∈ EvarR1 R d a ↔ r ∈ Finset.Icc 1 (2 * R) ∧ Nat.Coprime r d ∧
      (1 : ZMod d) = (r : ZMod d) * (a : ZMod d) := by
  rw [EvarR1, Finset.mem_filter, mem_EvarR]
  tauto

lemma EvarR1_card_le (R d a : ℕ) (_hd : 0 < d) :
    (EvarR1 R d a).card ≤ 2 * R / d + 1 := by
  have hmt : Set.MapsTo (fun r : ℕ => r / d) ↑(EvarR1 R d a)
      ↑(Finset.range (2 * R / d + 1)) := by
    intro r hr
    rw [Finset.mem_coe, mem_EvarR1] at hr
    rw [Finset.mem_coe, Finset.mem_range]
    have hle : r ≤ 2 * R := (Finset.mem_Icc.mp hr.1).2
    calc r / d ≤ 2 * R / d := Nat.div_le_div_right hle
      _ < 2 * R / d + 1 := Nat.lt_succ_self _
  have hinj : Set.InjOn (fun r : ℕ => r / d) ↑(EvarR1 R d a) := by
    intro r hr r' hr' heq
    rw [Finset.mem_coe, mem_EvarR1] at hr hr'
    obtain ⟨-, -, hr1⟩ := hr
    obtain ⟨-, -, hr1'⟩ := hr'
    have hc : (r : ZMod d) = (r' : ZMod d) := by
      have h3 : ((r : ZMod d) - (r' : ZMod d)) * (a : ZMod d) = 0 := by
        rw [sub_mul, ← hr1, ← hr1', sub_self]
      have h4 : ((r : ZMod d) - (r' : ZMod d)) * (a : ZMod d) * (r : ZMod d) = 0 := by
        rw [h3, zero_mul]
      have har : (a : ZMod d) * (r : ZMod d) = 1 := by rw [mul_comm]; exact hr1.symm
      rw [mul_assoc, har, mul_one] at h4
      exact sub_eq_zero.mp h4
    have hmod : r % d = r' % d := (ZMod.natCast_eq_natCast_iff' r r' d).mp hc
    have hdiv : r / d = r' / d := heq
    calc r = d * (r / d) + r % d := (Nat.div_add_mod r d).symm
      _ = d * (r' / d) + r % d := by rw [hdiv]
      _ = d * (r' / d) + r' % d := by rw [hmod]
      _ = r' := Nat.div_add_mod r' d
  have h2 := Finset.card_le_card_of_injOn (fun r : ℕ => r / d) hmt hinj
  rwa [Finset.card_range] at h2

lemma pairwiseDisjoint_EvarR1 (R d : ℕ) (_hd : 0 < d) :
    (↑(Finset.range d) : Set ℕ).PairwiseDisjoint (EvarR1 R d) := by
  intro a ha b hb hab
  show Disjoint (EvarR1 R d a) (EvarR1 R d b)
  rw [Finset.disjoint_left]
  intro r hra hrb
  rw [mem_EvarR1] at hra hrb
  have h1 := hra.2.2
  have h2 := hrb.2.2
  have h3 : (r : ZMod d) * ((a : ZMod d) - (b : ZMod d)) = 0 := by
    rw [mul_sub, ← h1, ← h2, sub_self]
  have h4 : ((a : ZMod d) * (r : ZMod d)) * ((a : ZMod d) - (b : ZMod d)) = 0 := by
    rw [mul_assoc, h3, mul_zero]
  have har : (a : ZMod d) * (r : ZMod d) = 1 := by rw [mul_comm]; exact h1.symm
  rw [har, one_mul] at h4
  have hcong : (a : ZMod d) = (b : ZMod d) := sub_eq_zero.mp h4
  have hlt : a < d := by simpa using ha
  have hlt' : b < d := by simpa using hb
  have hmod : a = b := by
    have h := (ZMod.natCast_eq_natCast_iff' a b d).mp hcong
    rwa [Nat.mod_eq_of_lt hlt, Nat.mod_eq_of_lt hlt'] at h
  exact hab hmod

/-- With `α` supported on `s = 1`, the residue class `a (mod d)` of `Evar` receives only the
moduli `r ≡ a⁻¹ (mod d)`; hence the class sum is the sum over `EvarR1 R d a`. -/
lemma Evar_eq_sum_EvarR1 (R S d : ℕ) (α : ℕ → ℕ → ℂ) (hS : 1 ≤ S)
    (h : ∀ r s, α r s ≠ 0 → s = 1) :
    Work.FIPlan.Evar R S d α
      = ∑ a ∈ Finset.range d, Complex.normSq (∑ r ∈ EvarR1 R d a,
          α r 1 * (jacobiSym (r : ℤ) (Work.FIPlan.oddPart d) : ℂ)) := by
  rw [Work.FIPlan.Evar]
  refine Finset.sum_congr rfl (fun a _ => ?_)
  congr 1
  have hinner : ∀ r : ℕ,
      (∑ s ∈ (Finset.Icc 1 (2 * S)).filter
          (fun s' => ((s' : ℕ) : ZMod d) = ((r : ℕ) : ZMod d) * ((a : ℕ) : ZMod d)),
        α r s * (jacobiSym (r : ℤ) (Work.FIPlan.oddPart d) : ℂ))
      = if (1 : ZMod d) = (r : ZMod d) * (a : ZMod d)
          then α r 1 * (jacobiSym (r : ℤ) (Work.FIPlan.oddPart d) : ℂ) else 0 := by
    intro r
    by_cases hc : (1 : ZMod d) = (r : ZMod d) * (a : ZMod d)
    · rw [if_pos hc]
      have hmem : 1 ∈ (Finset.Icc 1 (2 * S)).filter
          (fun s' => ((s' : ℕ) : ZMod d) = ((r : ℕ) : ZMod d) * ((a : ℕ) : ZMod d)) := by
        refine Finset.mem_filter.mpr ⟨Finset.mem_Icc.mpr ⟨le_refl 1, by omega⟩, ?_⟩
        simpa using hc
      refine Finset.sum_eq_single 1 (fun s _ hs1 => ?_) (fun hnot => absurd hmem hnot)
      have haz : α r s = 0 := by
        by_contra hne
        exact hs1 (h r s hne)
      rw [haz, zero_mul]
    · rw [if_neg hc]
      refine Finset.sum_eq_zero (fun s hs => ?_)
      have hsne : s ≠ 1 := by
        intro hse
        apply hc
        have hss := (Finset.mem_filter.mp hs).2
        rw [hse] at hss
        simpa using hss
      have haz : α r s = 0 := by
        by_contra hne
        exact hsne (h r s hne)
      rw [haz, zero_mul]
  calc (∑ r ∈ (Finset.Icc 1 (2 * R)).filter (fun r => Nat.Coprime r d),
        ∑ s ∈ (Finset.Icc 1 (2 * S)).filter
          (fun s' => ((s' : ℕ) : ZMod d) = ((r : ℕ) : ZMod d) * ((a : ℕ) : ZMod d)),
          α r s * (jacobiSym (r : ℤ) (Work.FIPlan.oddPart d) : ℂ))
      = ∑ r ∈ (Finset.Icc 1 (2 * R)).filter (fun r => Nat.Coprime r d),
          (if (1 : ZMod d) = (r : ZMod d) * (a : ZMod d)
            then α r 1 * (jacobiSym (r : ℤ) (Work.FIPlan.oddPart d) : ℂ) else 0) :=
        Finset.sum_congr rfl (fun r _ => hinner r)
    _ = ∑ r ∈ EvarR1 R d a, α r 1 * (jacobiSym (r : ℤ) (Work.FIPlan.oddPart d) : ℂ) := by
        rw [← Finset.sum_filter]
        rfl

/-- **The local variance under the `s = 1` support hypothesis.**  If `α r s = 0` whenever
`s ≠ 1`, then each residue class `a (mod d)` of `Evar` sees the `r ≡ a⁻¹ (mod d)`, so it contains
at most `2R/d + 1` coefficients and Cauchy–Schwarz gives

  `E(d) ≤ (2R/d + 1) · Σ_{r ≤ 2R, s ≤ 2S} ‖α r s‖²`. -/
lemma Evar_le_of_support_s_one (R S d : ℕ) (α : ℕ → ℕ → ℂ) (hS : 1 ≤ S) (hd : 0 < d)
    (h : ∀ r s, α r s ≠ 0 → s = 1) :
    Work.FIPlan.Evar R S d α
      ≤ (2 * (R : ℝ) / (d : ℝ) + 1) *
        (∑ r ∈ Finset.Icc 1 (2 * R), ∑ s ∈ Finset.Icc 1 (2 * S),
          Complex.normSq (α r s)) := by
  have hper : ∀ a : ℕ, Complex.normSq (∑ r ∈ EvarR1 R d a,
        α r 1 * (jacobiSym (r : ℤ) (Work.FIPlan.oddPart d) : ℂ))
      ≤ (2 * (R : ℝ) / (d : ℝ) + 1) * ∑ r ∈ EvarR1 R d a, Complex.normSq (α r 1) := by
    intro a
    have hcs := normSq_sum_le_card_mul_sum (EvarR1 R d a)
      (fun r => α r 1 * (jacobiSym (r : ℤ) (Work.FIPlan.oddPart d) : ℂ))
    have hterm : ∑ r ∈ EvarR1 R d a,
          Complex.normSq (α r 1 * (jacobiSym (r : ℤ) (Work.FIPlan.oddPart d) : ℂ))
        ≤ ∑ r ∈ EvarR1 R d a, Complex.normSq (α r 1) :=
      Finset.sum_le_sum (fun r _ => normSq_mul_jacobiSym_le _ _ _)
    have hcard : ((EvarR1 R d a).card : ℝ) ≤ 2 * (R : ℝ) / (d : ℝ) + 1 := by
      have h1 : ((EvarR1 R d a).card : ℝ) ≤ ((2 * R / d + 1 : ℕ) : ℝ) := by
        exact_mod_cast EvarR1_card_le R d a hd
      have h2 : ((2 * R / d + 1 : ℕ) : ℝ) ≤ 2 * (R : ℝ) / (d : ℝ) + 1 := by
        have h3 : (((2 * R / d : ℕ)) : ℝ) ≤ 2 * (R : ℝ) / (d : ℝ) := by
          have hh := Nat.cast_div_le (α := ℝ) (m := 2 * R) (n := d)
          push_cast at hh
          exact hh
        push_cast
        linarith
      linarith
    calc Complex.normSq (∑ r ∈ EvarR1 R d a,
            α r 1 * (jacobiSym (r : ℤ) (Work.FIPlan.oddPart d) : ℂ))
        ≤ ((EvarR1 R d a).card : ℝ) * ∑ r ∈ EvarR1 R d a,
            Complex.normSq (α r 1 * (jacobiSym (r : ℤ) (Work.FIPlan.oddPart d) : ℂ)) := hcs
      _ ≤ ((EvarR1 R d a).card : ℝ) * ∑ r ∈ EvarR1 R d a, Complex.normSq (α r 1) :=
          mul_le_mul_of_nonneg_left hterm (Nat.cast_nonneg _)
      _ ≤ (2 * (R : ℝ) / (d : ℝ) + 1) * ∑ r ∈ EvarR1 R d a, Complex.normSq (α r 1) :=
          mul_le_mul_of_nonneg_right hcard
            (Finset.sum_nonneg (fun r _ => Complex.normSq_nonneg _))
  have hUp : ∑ a ∈ Finset.range d, (∑ r ∈ EvarR1 R d a, Complex.normSq (α r 1))
      ≤ ∑ r ∈ Finset.Icc 1 (2 * R), Complex.normSq (α r 1) := by
    rw [← Finset.sum_biUnion (pairwiseDisjoint_EvarR1 R d hd)
        (f := fun r => Complex.normSq (α r 1))]
    refine Finset.sum_le_sum_of_subset_of_nonneg ?_ (fun r _ _ => Complex.normSq_nonneg _)
    rw [Finset.biUnion_subset]
    intro a _
    exact (Finset.filter_subset _ _).trans (Finset.filter_subset _ _)
  calc Work.FIPlan.Evar R S d α
      = ∑ a ∈ Finset.range d, Complex.normSq (∑ r ∈ EvarR1 R d a,
          α r 1 * (jacobiSym (r : ℤ) (Work.FIPlan.oddPart d) : ℂ)) :=
        Evar_eq_sum_EvarR1 R S d α hS h
    _ ≤ ∑ a ∈ Finset.range d,
          (2 * (R : ℝ) / (d : ℝ) + 1) * (∑ r ∈ EvarR1 R d a, Complex.normSq (α r 1)) :=
        Finset.sum_le_sum (fun a _ => hper a)
    _ = (2 * (R : ℝ) / (d : ℝ) + 1) *
          ∑ a ∈ Finset.range d, (∑ r ∈ EvarR1 R d a, Complex.normSq (α r 1)) :=
        (Finset.mul_sum _ _ _).symm
    _ ≤ (2 * (R : ℝ) / (d : ℝ) + 1) * ∑ r ∈ Finset.Icc 1 (2 * R), Complex.normSq (α r 1) :=
        mul_le_mul_of_nonneg_left hUp (by positivity)
    _ ≤ (2 * (R : ℝ) / (d : ℝ) + 1) *
          (∑ r ∈ Finset.Icc 1 (2 * R), ∑ s ∈ Finset.Icc 1 (2 * S),
            Complex.normSq (α r s)) := by
        refine mul_le_mul_of_nonneg_left ?_ (by positivity)
        refine Finset.sum_le_sum (fun r _ => ?_)
        exact Finset.single_le_sum (fun s _ => Complex.normSq_nonneg _)
          (Finset.mem_Icc.mpr ⟨le_refl 1, by omega⟩)

/-- `braceV` dominates `D` (for `R, S ≥ 1`). -/
lemma le_braceV_left (D R S : ℕ) (ε : ℝ) (hR : 1 ≤ R) (hS : 1 ≤ S) (hε : 0 < ε) :
    (D : ℝ) ≤ Work.FIArea4.braceV D R S ε := by
  have hR1 : (1 : ℝ) ≤ (R : ℝ) := by exact_mod_cast hR
  have hS1 : (1 : ℝ) ≤ (S : ℝ) := by exact_mod_cast hS
  have hRS1 : (1 : ℝ) ≤ (R : ℝ) * (S : ℝ) := by nlinarith
  have hsq : (1 : ℝ) ≤ Real.sqrt ((R : ℝ) * (S : ℝ)) := by
    rw [Real.one_le_sqrt]; exact hRS1
  have hfac : (1 : ℝ) ≤ ((R : ℝ) * (S : ℝ)) ^ ε := Real.one_le_rpow hRS1 hε.le
  have hDnn : (0 : ℝ) ≤ (D : ℝ) := Nat.cast_nonneg D
  have hFnn : (0 : ℝ) ≤ ((R : ℝ) * (S : ℝ)) ^ ε := Real.rpow_nonneg (by positivity) ε
  have hB2 : (0 : ℝ) ≤ (R : ℝ) * ((S : ℝ) ^ ((3 : ℝ) / 4)) :=
    mul_nonneg (Nat.cast_nonneg _) (Real.rpow_nonneg (Nat.cast_nonneg _) _)
  have hB3 : (0 : ℝ) ≤ (S : ℝ) * ((R : ℝ) ^ ((3 : ℝ) / 4)) :=
    mul_nonneg (Nat.cast_nonneg _) (Real.rpow_nonneg (Nat.cast_nonneg _) _)
  have hkey : (D : ℝ) ≤ (D : ℝ) * Real.sqrt ((R : ℝ) * (S : ℝ)) *
      ((R : ℝ) * (S : ℝ)) ^ ε := by
    calc (D : ℝ) = (D : ℝ) * 1 * 1 := by ring
      _ ≤ (D : ℝ) * Real.sqrt ((R : ℝ) * (S : ℝ)) * ((R : ℝ) * (S : ℝ)) ^ ε :=
          mul_le_mul (mul_le_mul_of_nonneg_left hsq hDnn) hfac (by norm_num) (by positivity)
  have hA : (0 : ℝ) ≤ (D : ℝ) ^ (-(1 : ℝ) / 2) * (R : ℝ) * (S : ℝ) := by positivity
  calc (D : ℝ) ≤ (D : ℝ) * Real.sqrt ((R : ℝ) * (S : ℝ)) * ((R : ℝ) * (S : ℝ)) ^ ε := hkey
    _ ≤ ((D : ℝ) * Real.sqrt ((R : ℝ) * (S : ℝ))
          + (R : ℝ) * ((S : ℝ) ^ ((3 : ℝ) / 4)) + (S : ℝ) * ((R : ℝ) ^ ((3 : ℝ) / 4)))
        * ((R : ℝ) * (S : ℝ)) ^ ε :=
        mul_le_mul_of_nonneg_right (by linarith) hFnn
    _ ≤ Work.FIArea4.braceV D R S ε := by
        unfold Work.FIArea4.braceV
        linarith

/-- `braceV` dominates `R` (for `R, S ≥ 1`). -/
lemma le_braceV_right (D R S : ℕ) (ε : ℝ) (hR : 1 ≤ R) (hS : 1 ≤ S) (hε : 0 < ε) :
    (R : ℝ) ≤ Work.FIArea4.braceV D R S ε := by
  have hR1 : (1 : ℝ) ≤ (R : ℝ) := by exact_mod_cast hR
  have hS1 : (1 : ℝ) ≤ (S : ℝ) := by exact_mod_cast hS
  have hRS1 : (1 : ℝ) ≤ (R : ℝ) * (S : ℝ) := by nlinarith
  have hfac : (1 : ℝ) ≤ ((R : ℝ) * (S : ℝ)) ^ ε := Real.one_le_rpow hRS1 hε.le
  have hS34 : (1 : ℝ) ≤ (S : ℝ) ^ ((3 : ℝ) / 4) := Real.one_le_rpow hS1 (by norm_num)
  have hRnn : (0 : ℝ) ≤ (R : ℝ) := Nat.cast_nonneg R
  have hFnn : (0 : ℝ) ≤ ((R : ℝ) * (S : ℝ)) ^ ε := Real.rpow_nonneg (by positivity) ε
  have hB1 : (0 : ℝ) ≤ (D : ℝ) * Real.sqrt ((R : ℝ) * (S : ℝ)) :=
    mul_nonneg (Nat.cast_nonneg _) (Real.sqrt_nonneg _)
  have hB3 : (0 : ℝ) ≤ (S : ℝ) * ((R : ℝ) ^ ((3 : ℝ) / 4)) :=
    mul_nonneg (Nat.cast_nonneg _) (Real.rpow_nonneg (Nat.cast_nonneg _) _)
  have hkey : (R : ℝ) ≤ (R : ℝ) * ((S : ℝ) ^ ((3 : ℝ) / 4)) * ((R : ℝ) * (S : ℝ)) ^ ε := by
    calc (R : ℝ) = (R : ℝ) * 1 * 1 := by ring
      _ ≤ (R : ℝ) * ((S : ℝ) ^ ((3 : ℝ) / 4)) * ((R : ℝ) * (S : ℝ)) ^ ε :=
          mul_le_mul (mul_le_mul_of_nonneg_left hS34 hRnn) hfac (by norm_num) (by positivity)
  have hA : (0 : ℝ) ≤ (D : ℝ) ^ (-(1 : ℝ) / 2) * (R : ℝ) * (S : ℝ) := by positivity
  calc (R : ℝ) ≤ (R : ℝ) * ((S : ℝ) ^ ((3 : ℝ) / 4)) * ((R : ℝ) * (S : ℝ)) ^ ε := hkey
    _ ≤ ((D : ℝ) * Real.sqrt ((R : ℝ) * (S : ℝ))
          + (R : ℝ) * ((S : ℝ) ^ ((3 : ℝ) / 4)) + (S : ℝ) * ((R : ℝ) ^ ((3 : ℝ) / 4)))
        * ((R : ℝ) * (S : ℝ)) ^ ε :=
        mul_le_mul_of_nonneg_right (by linarith) hFnn
    _ ≤ Work.FIArea4.braceV D R S ε := by
        unfold Work.FIArea4.braceV
        linarith

lemma sum_Ioc_Evar_le_braceV_support_s_one (D R S : ℕ) (α : ℕ → ℕ → ℂ) (ε : ℝ)
    (hD : 1 ≤ D) (hR : 1 ≤ R) (hS : 1 ≤ S) (hε : 0 < ε)
    (h : ∀ r s, α r s ≠ 0 → s = 1) :
    (∑ d ∈ Finset.Ioc D (2*D), Work.FIPlan.Evar R S d α)
      ≤ 3 * Work.FIArea4.braceV D R S ε
        * (∑ r ∈ Finset.Icc 1 (2*R), ∑ s ∈ Finset.Icc 1 (2*S), Complex.normSq (α r s)) := by
  set T : ℝ := ∑ r ∈ Finset.Icc 1 (2 * R), ∑ s ∈ Finset.Icc 1 (2 * S),
    Complex.normSq (α r s) with hT
  have hTnn : 0 ≤ T := by
    rw [hT]
    exact Finset.sum_nonneg (fun r _ => Finset.sum_nonneg (fun s _ => Complex.normSq_nonneg _))
  have hbrace : 2 * (R : ℝ) + (D : ℝ) ≤ 3 * Work.FIArea4.braceV D R S ε := by
    have h1 := le_braceV_left D R S ε hR hS hε
    have h2 := le_braceV_right D R S ε hR hS hε
    linarith
  have hsum : ∑ d ∈ Finset.Ioc D (2 * D), (2 * (R : ℝ) / (d : ℝ) + 1)
      ≤ 2 * (R : ℝ) + (D : ℝ) := by
    have hterm : ∀ d ∈ Finset.Ioc D (2 * D),
        2 * (R : ℝ) / (d : ℝ) + 1 ≤ 2 * (R : ℝ) / (D : ℝ) + 1 := by
      intro d hdmem
      have hdge : D ≤ d := le_of_lt (Finset.mem_Ioc.mp hdmem).1
      have hDpos : (0 : ℝ) < (D : ℝ) := by exact_mod_cast (by omega : 0 < D)
      have hle : 2 * (R : ℝ) / (d : ℝ) ≤ 2 * (R : ℝ) / (D : ℝ) :=
        div_le_div_of_nonneg_left (by positivity) hDpos (by exact_mod_cast hdge)
      linarith
    have hcard : (Finset.Ioc D (2 * D)).card = D := by rw [Nat.card_Ioc]; omega
    have hDne : (D : ℝ) ≠ 0 := by exact_mod_cast (by omega : D ≠ 0)
    calc ∑ d ∈ Finset.Ioc D (2 * D), (2 * (R : ℝ) / (d : ℝ) + 1)
        ≤ ∑ d ∈ Finset.Ioc D (2 * D), (2 * (R : ℝ) / (D : ℝ) + 1) := Finset.sum_le_sum hterm
      _ = ((Finset.Ioc D (2 * D)).card : ℝ) * (2 * (R : ℝ) / (D : ℝ) + 1) := by
          rw [Finset.sum_const, nsmul_eq_mul]
      _ = (D : ℝ) * (2 * (R : ℝ) / (D : ℝ) + 1) := by rw [hcard]
      _ = 2 * (R : ℝ) + (D : ℝ) := by
          field_simp
  calc ∑ d ∈ Finset.Ioc D (2 * D), Work.FIPlan.Evar R S d α
      ≤ ∑ d ∈ Finset.Ioc D (2 * D), (2 * (R : ℝ) / (d : ℝ) + 1) * T := by
        refine Finset.sum_le_sum (fun d hdmem => ?_)
        have hdpos : 0 < d := by
          have := (Finset.mem_Ioc.mp hdmem).1; omega
        rw [hT]
        exact Evar_le_of_support_s_one R S d α hS hdpos h
    _ = (∑ d ∈ Finset.Ioc D (2 * D), (2 * (R : ℝ) / (d : ℝ) + 1)) * T := by
        rw [Finset.sum_mul]
    _ ≤ (2 * (R : ℝ) + (D : ℝ)) * T := mul_le_mul_of_nonneg_right hsum hTnn
    _ ≤ (3 * Work.FIArea4.braceV D R S ε) * T := mul_le_mul_of_nonneg_right hbrace hTnn

end

end Work.FIArea4
