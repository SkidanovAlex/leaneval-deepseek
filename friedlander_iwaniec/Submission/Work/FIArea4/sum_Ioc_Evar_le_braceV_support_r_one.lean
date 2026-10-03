/-
# The brace bound for the variance sum, when `α` is supported on `r = 1`

Friedlander–Iwaniec, *The polynomial X² + Y⁴ captures its primes*, §11: the local variance (11.7)

`E(d) = Σ_{a < d} |Σ_{r̄s ≡ a (d)} α_{rs} (r/d')|²`

and the global variance `V(D) = Σ_{D < d ≤ 2D} E(d)` (11.11) are bounded by the "brace" of (11.14)

`V(D) ≪ {D^{-1/2}RS + (D√(RS) + R S^{3/4} + S R^{3/4})(RS)^ε} ‖α‖²`.

This file treats the **degenerate support** in which the coefficient matrix `α` lives on the line
`r = 1` (this is exactly what happens in the §15 separation of variables, where the `r`-variable
has been reduced to the single term `r = 1`).  In that case the class sums collapse to partial
sums of the one-variable sequence `s ↦ α 1 s`:

* the `r`-sum of `E(d)` contains only the term `r = 1` (the Jacobi weight is `jw d 1 = 1`);
* hence `E(d) = Σ_{a < d} |Σ_{s ∈ [1,2S], s ≡ a (d)} α 1 s|²` — a sum of squared partial sums of
  one sequence over the residue classes of `[1,2S]` modulo `d`;
* each class contains at most `2S/d + 1` terms and the classes partition `[1,2S]`, so
  Cauchy–Schwarz gives the (much stronger than the trivial) bound
  `E(d) ≤ (2S/d + 1) Σ_{s ≤ 2S} ‖α 1 s‖²`;
* summing over `d ∈ (D, 2D]` gives `V(D) ≤ (D + 2S) Σ‖α‖²`, and `D + 2S ≤ 3 · braceV D R S ε`
  because the brace dominates both `D` (through the term `D√(RS)(RS)^ε`) and `S` (through the term
  `S R^{3/4}(RS)^ε`), for `R, S ≥ 1` and `ε > 0`.

This is the `r = 1` half of the "diagonal" case of the §15 separation of variables; the `s = 1`
half is the parallel lemma `sum_Ioc_Evar_le_braceV_support_s_one`.
-/
import Mathlib
import Submission.Work.FIArea4.prop_11_1_defs
import Submission.Work.FIPlan.Interface
import Submission.Work.FIArea4.Evar_eq_sum_clsSum
import Submission.Work.FIArea4.Evar_le_trivial

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

namespace Work.FIArea4

open Finset
open scoped BigOperators

attribute [local instance] Classical.propDecidable

noncomputable section

/-! ## The residue classes of the one-variable box `[1,2S]` -/

/-- The `s`'s of the box `[1,2S]` lying in the residue class `a` modulo `d`.  These are the
classes into which the class sums of `E(d)` degenerate when `α` is supported on `r = 1`. -/
def SclsR1 (S d a : ℕ) : Finset ℕ :=
  (Finset.Icc 1 (2 * S)).filter (fun t : ℕ => (t : ZMod d) = (a : ZMod d))

/-- **The class sum of `E(d)` when `α` is supported on `r = 1`.**  Since `α r s = 0` for `r ≠ 1`
and the Jacobi weight at `r = 1` is `jw d 1 = 1`, the class sum `X_a` of (11.7) is the partial sum
of the sequence `s ↦ α 1 s` over the `s ∈ [1,2S]` with `s ≡ a (mod d)`. -/
lemma clsSum_eq_reduced_r_one (R S d a : ℕ) (α : ℕ → ℕ → ℂ) (hR : 1 ≤ R)
    (h : ∀ r s, α r s ≠ 0 → r = 1) :
    clsSum R S d α a = ∑ s ∈ SclsR1 S d a, α 1 s := by
  have hstep : clsSum R S d α a
      = ∑ r ∈ EvarR R d, ∑ s ∈ (Finset.Icc 1 (2 * S)).filter
            (fun t : ℕ => (t : ZMod d) = (r : ZMod d) * (a : ZMod d)),
          α r s * jw d r := by
    rw [clsSum, EvarCls, EvarR]
    exact sum_product_filter _ _ _ _
  rw [hstep]
  have hcollapse :
      (∑ r ∈ EvarR R d, ∑ s ∈ (Finset.Icc 1 (2 * S)).filter
            (fun t : ℕ => (t : ZMod d) = (r : ZMod d) * (a : ZMod d)),
          α r s * jw d r)
      = ∑ s ∈ (Finset.Icc 1 (2 * S)).filter
            (fun t : ℕ => (t : ZMod d) = ((1 : ℕ) : ZMod d) * (a : ZMod d)), α 1 s * jw d 1 := by
    refine Finset.sum_eq_single (M := ℂ)
      (f := fun r : ℕ => ∑ s ∈ (Finset.Icc 1 (2 * S)).filter
            (fun t : ℕ => (t : ZMod d) = (r : ZMod d) * (a : ZMod d)), α r s * jw d r) 1 ?_ ?_
    · -- every `r ≠ 1` contributes nothing, because `α` vanishes there
      intro r hr hne
      exact Finset.sum_eq_zero (fun s _ => by
        have hr0 : α r s = 0 := by
          by_contra hc
          exact hne (h r s hc)
        rw [hr0, zero_mul])
    · -- and `r = 1` does lie in the `r`-support `EvarR R d`
      intro hnot
      exact absurd (mem_EvarR.mpr ⟨Finset.mem_Icc.mpr ⟨le_rfl, by omega⟩,
        Nat.coprime_one_left d⟩) hnot
  rw [hcollapse]
  -- the Jacobi weight at `r = 1` is `1`, and `1 · a = a` modulo `d`
  have hjw : jw d 1 = 1 := by simp [jw, jacobiSym.one_left]
  rw [hjw]
  simp only [mul_one]
  have hf : (Finset.Icc 1 (2 * S)).filter
        (fun t : ℕ => (t : ZMod d) = ((1 : ℕ) : ZMod d) * (a : ZMod d)) = SclsR1 S d a := by
    rw [SclsR1]
    apply Finset.filter_congr
    intro s _
    simp
  rw [hf]

/-- A residue class of `[1,2S]` modulo `d` contains at most `2S/d + 1` elements: `s ↦ s/d` is
injective on the class (the remainder `s % d` is fixed by the class) with values in
`range (2S/d + 1)`. -/
lemma card_SclsR1_le (S d a : ℕ) : (SclsR1 S d a).card ≤ 2 * S / d + 1 := by
  have hmt : Set.MapsTo (fun s : ℕ => s / d) ↑(SclsR1 S d a) ↑(Finset.range (2 * S / d + 1)) := by
    intro s hs
    rw [Finset.mem_coe, SclsR1, Finset.mem_filter] at hs
    rw [Finset.mem_coe, Finset.mem_range]
    have hle : s ≤ 2 * S := (Finset.mem_Icc.mp hs.1).2
    calc s / d ≤ 2 * S / d := Nat.div_le_div_right hle
      _ < 2 * S / d + 1 := Nat.lt_succ_self _
  have hinj : Set.InjOn (fun s : ℕ => s / d) ↑(SclsR1 S d a) := by
    intro s hs t ht heq
    rw [Finset.mem_coe, SclsR1, Finset.mem_filter] at hs ht
    have heq' : s / d = t / d := heq
    have hmod : s % d = t % d := by
      rw [← ZMod.natCast_eq_natCast_iff' s t d]
      rw [hs.2, ht.2]
    calc s = d * (s / d) + s % d := (Nat.div_add_mod s d).symm
      _ = d * (t / d) + s % d := by rw [heq']
      _ = d * (t / d) + t % d := by rw [hmod]
      _ = t := Nat.div_add_mod t d
  have h := Finset.card_le_card_of_injOn (fun s : ℕ => s / d) hmt hinj
  rw [Finset.card_range] at h
  exact h

/-- The residue classes of `[1,2S]` modulo `d` are pairwise disjoint. -/
lemma pairwiseDisjoint_SclsR1 (S d : ℕ) :
    (↑(Finset.range d) : Set ℕ).PairwiseDisjoint (SclsR1 S d) := by
  intro a ha b hb hab
  show Disjoint (SclsR1 S d a) (SclsR1 S d b)
  rw [Finset.disjoint_left]
  intro s hs ht
  rw [SclsR1, Finset.mem_filter] at hs ht
  have ha' : a < d := by simpa using ha
  have hb' : b < d := by simpa using hb
  have hz : (a : ZMod d) = (b : ZMod d) := hs.2.symm.trans ht.2
  have hmod : a % d = b % d := (ZMod.natCast_eq_natCast_iff' a b d).mp hz
  rw [Nat.mod_eq_of_lt ha', Nat.mod_eq_of_lt hb'] at hmod
  exact hab hmod

/-- The residue classes `a < d` cover the whole box `[1,2S]` (`a = s % d`). -/
lemma biUnion_SclsR1 (S d : ℕ) (hd : 0 < d) :
    (Finset.range d).biUnion (SclsR1 S d) = Finset.Icc 1 (2 * S) := by
  apply Finset.Subset.antisymm
  · intro s hs
    rw [Finset.mem_biUnion] at hs
    obtain ⟨a, -, hsa⟩ := hs
    exact (Finset.mem_filter.mp hsa).1
  · intro s hs
    rw [Finset.mem_biUnion]
    refine ⟨s % d, Finset.mem_range.mpr (Nat.mod_lt s hd), ?_⟩
    rw [SclsR1, Finset.mem_filter]
    refine ⟨hs, ?_⟩
    rw [ZMod.natCast_eq_natCast_iff']
    exact (Nat.mod_mod s d).symm

/-- **The residue classes partition the box**, so a sum over the classes is the sum over the
box. -/
lemma sum_SclsR1_eq (S d : ℕ) (hd : 0 < d) (f : ℕ → ℝ) :
    ∑ a ∈ Finset.range d, ∑ s ∈ SclsR1 S d a, f s = ∑ s ∈ Finset.Icc 1 (2 * S), f s := by
  rw [← Finset.sum_biUnion (pairwiseDisjoint_SclsR1 S d), biUnion_SclsR1 S d hd]

/-! ## The local variance on the line `r = 1` -/

/-- **The local variance when `α` is supported on `r = 1`.**  The class sums are partial sums of
the single sequence `s ↦ α 1 s`, each class holding at most `2S/d + 1` terms, so Cauchy–Schwarz
gives
`E(d) ≤ (2S/d + 1) Σ_{s ≤ 2S} ‖α 1 s‖²`,
which is `≪ (d^{-1}S + 1)‖α‖²` — the paper's `≪ d^{-1}RS` with the `R` replaced by `1`. -/
lemma Evar_le_reduced_r_one (R S d : ℕ) (α : ℕ → ℕ → ℂ) (hR : 1 ≤ R) (hd : 0 < d)
    (h : ∀ r s, α r s ≠ 0 → r = 1) :
    Work.FIPlan.Evar R S d α ≤ (2 * (S : ℝ) / (d : ℝ) + 1) *
      ∑ s ∈ Finset.Icc 1 (2 * S), Complex.normSq (α 1 s) := by
  rw [Evar_eq_sum_clsSum]
  have hper : ∀ a, Complex.normSq (clsSum R S d α a) ≤
      (2 * (S : ℝ) / (d : ℝ) + 1) * ∑ s ∈ SclsR1 S d a, Complex.normSq (α 1 s) := by
    intro a
    rw [clsSum_eq_reduced_r_one R S d a α hR h]
    refine le_trans (normSq_sum_le_card_mul_sum (SclsR1 S d a) (fun s => α 1 s)) ?_
    apply mul_le_mul_of_nonneg_right _ (Finset.sum_nonneg (fun s _ => Complex.normSq_nonneg _))
    have h1 : ((SclsR1 S d a).card : ℝ) ≤ ((2 * S / d + 1 : ℕ) : ℝ) := by
      exact_mod_cast card_SclsR1_le S d a
    have h2 : ((2 * S / d + 1 : ℕ) : ℝ) ≤ 2 * (S : ℝ) / (d : ℝ) + 1 := by
      have h3 : (((2 * S / d : ℕ)) : ℝ) ≤ 2 * (S : ℝ) / (d : ℝ) := by
        have h := (Nat.cast_div_le (m := 2 * S) (n := d) :
          (((2 * S / d : ℕ)) : ℝ) ≤ ((2 * S : ℕ) : ℝ) / (d : ℝ))
        push_cast at h
        exact h
      calc ((2 * S / d + 1 : ℕ) : ℝ) = ((2 * S / d : ℕ) : ℝ) + 1 := by push_cast; ring
        _ ≤ 2 * (S : ℝ) / (d : ℝ) + 1 := by linarith
    linarith
  calc ∑ a ∈ Finset.range d, Complex.normSq (clsSum R S d α a)
      ≤ ∑ a ∈ Finset.range d, (2 * (S : ℝ) / (d : ℝ) + 1) *
          ∑ s ∈ SclsR1 S d a, Complex.normSq (α 1 s) :=
        Finset.sum_le_sum (fun a _ => hper a)
    _ = (2 * (S : ℝ) / (d : ℝ) + 1) *
          ∑ a ∈ Finset.range d, ∑ s ∈ SclsR1 S d a, Complex.normSq (α 1 s) := by
        rw [Finset.mul_sum]
    _ = (2 * (S : ℝ) / (d : ℝ) + 1) *
          ∑ s ∈ Finset.Icc 1 (2 * S), Complex.normSq (α 1 s) := by
        rw [sum_SclsR1_eq S d hd]

/-! ## The brace dominates `D + 2S` -/

/-- For `D, R, S ≥ 1` and `ε > 0`, the brace of (11.14) dominates `D + 2S`: its second factor
contains `D√(RS)(RS)^ε ≥ D` and `S R^{3/4}(RS)^ε ≥ S`, and the first term of the brace is
nonnegative. -/
lemma add_two_mul_le_three_braceV_r_one (D R S : ℕ) (ε : ℝ)
    (hD : 1 ≤ D) (hR : 1 ≤ R) (hS : 1 ≤ S) (hε : 0 < ε) :
    (D : ℝ) + 2 * (S : ℝ) ≤ 3 * braceV D R S ε := by
  have hx : 1 ≤ (D : ℝ) := by exact_mod_cast hD
  have hy : 1 ≤ (R : ℝ) := by exact_mod_cast hR
  have hz : 1 ≤ (S : ℝ) := by exact_mod_cast hS
  have hyz : 1 ≤ (R : ℝ) * (S : ℝ) := by nlinarith
  have hsqrt : 1 ≤ Real.sqrt ((R : ℝ) * (S : ℝ)) := Real.one_le_sqrt.mpr hyz
  have hpr : 1 ≤ (((R : ℝ) * (S : ℝ)) ^ ε) := Real.one_le_rpow hyz hε.le
  have hy34 : 1 ≤ (R : ℝ) ^ ((3 : ℝ) / 4) := Real.one_le_rpow hy (by norm_num)
  have hA : (D : ℝ) ≤ (D : ℝ) * Real.sqrt ((R : ℝ) * (S : ℝ)) * (((R : ℝ) * (S : ℝ)) ^ ε) := by
    have h1 : (1 : ℝ) ≤ Real.sqrt ((R : ℝ) * (S : ℝ)) * (((R : ℝ) * (S : ℝ)) ^ ε) := by
      have hm := mul_le_mul hsqrt hpr (by norm_num : (0 : ℝ) ≤ 1)
        (by positivity : (0 : ℝ) ≤ Real.sqrt _)
      simpa using hm
    calc (D : ℝ) = (D : ℝ) * 1 := by ring
      _ ≤ (D : ℝ) * (Real.sqrt ((R : ℝ) * (S : ℝ)) * (((R : ℝ) * (S : ℝ)) ^ ε)) :=
          mul_le_mul_of_nonneg_left h1 (by positivity)
      _ = (D : ℝ) * Real.sqrt ((R : ℝ) * (S : ℝ)) * (((R : ℝ) * (S : ℝ)) ^ ε) := by ring
  have hC : (S : ℝ) ≤ (S : ℝ) * (R : ℝ) ^ ((3 : ℝ) / 4) * (((R : ℝ) * (S : ℝ)) ^ ε) := by
    have h1 : (1 : ℝ) ≤ (R : ℝ) ^ ((3 : ℝ) / 4) * (((R : ℝ) * (S : ℝ)) ^ ε) := by
      have hm := mul_le_mul hy34 hpr (by norm_num : (0 : ℝ) ≤ 1)
        (by positivity : (0 : ℝ) ≤ (R : ℝ) ^ ((3 : ℝ) / 4))
      simpa using hm
    calc (S : ℝ) = (S : ℝ) * 1 := by ring
      _ ≤ (S : ℝ) * ((R : ℝ) ^ ((3 : ℝ) / 4) * (((R : ℝ) * (S : ℝ)) ^ ε)) :=
          mul_le_mul_of_nonneg_left h1 (by positivity)
      _ = (S : ℝ) * (R : ℝ) ^ ((3 : ℝ) / 4) * (((R : ℝ) * (S : ℝ)) ^ ε) := by ring
  have hbrace : (D : ℝ) + (S : ℝ) ≤ braceV D R S ε := by
    have hp : 0 ≤ (D : ℝ) ^ (-(1 : ℝ) / 2) * (R : ℝ) * (S : ℝ) := by positivity
    have hmid : 0 ≤ (R : ℝ) * (S : ℝ) ^ ((3 : ℝ) / 4) * (((R : ℝ) * (S : ℝ)) ^ ε) := by
      positivity
    have hexp : ((D : ℝ) * Real.sqrt ((R : ℝ) * (S : ℝ))
          + (R : ℝ) * (S : ℝ) ^ ((3 : ℝ) / 4)
          + (S : ℝ) * (R : ℝ) ^ ((3 : ℝ) / 4)) * (((R : ℝ) * (S : ℝ)) ^ ε)
        = (D : ℝ) * Real.sqrt ((R : ℝ) * (S : ℝ)) * (((R : ℝ) * (S : ℝ)) ^ ε)
          + (R : ℝ) * (S : ℝ) ^ ((3 : ℝ) / 4) * (((R : ℝ) * (S : ℝ)) ^ ε)
          + (S : ℝ) * (R : ℝ) ^ ((3 : ℝ) / 4) * (((R : ℝ) * (S : ℝ)) ^ ε) := by ring
    rw [braceV, hexp]
    linarith [hA, hC, hp, hmid]
  nlinarith [hbrace, hx, hz]

/-! ## The brace bound for the variance sum -/

/-- **The brace bound for `Σ_{D < d ≤ 2D} E(d)` when `α` is supported on `r = 1`.**
Summing the local bound `E(d) ≤ (2S/d + 1)‖α‖²` over the `D` moduli `d ∈ (D,2D]` gives
`V(D) ≤ (D + 2S)‖α‖²`, and `D + 2S ≤ 3 · braceV D R S ε`. -/
lemma sum_Ioc_Evar_le_braceV_support_r_one (D R S : ℕ) (α : ℕ → ℕ → ℂ) (ε : ℝ)
    (hD : 1 ≤ D) (hR : 1 ≤ R) (hS : 1 ≤ S) (hε : 0 < ε)
    (h : ∀ r s, α r s ≠ 0 → r = 1) :
    (∑ d ∈ Finset.Ioc D (2*D), Work.FIPlan.Evar R S d α)
      ≤ 3 * Work.FIArea4.braceV D R S ε
        * (∑ r ∈ Finset.Icc 1 (2*R), ∑ s ∈ Finset.Icc 1 (2*S), Complex.normSq (α r s)) := by
  set T : ℝ := ∑ r ∈ Finset.Icc 1 (2*R), ∑ s ∈ Finset.Icc 1 (2*S), Complex.normSq (α r s) with hTdef
  have hTnn : 0 ≤ T := by
    rw [hTdef]
    exact Finset.sum_nonneg (fun r _ => Finset.sum_nonneg (fun s _ => Complex.normSq_nonneg _))
  have hper : ∀ d ∈ Finset.Ioc D (2*D),
      Work.FIPlan.Evar R S d α ≤ (2*(S:ℝ)/(d:ℝ) + 1) * T := by
    intro d hdmem
    have hdpos : 0 < d := by have h1 := (Finset.mem_Ioc.mp hdmem).1; omega
    have hmain := Evar_le_reduced_r_one R S d α hR hdpos h
    have hsub : (∑ s ∈ Finset.Icc 1 (2*S), Complex.normSq (α 1 s)) ≤ T := by
      rw [hTdef]
      refine Finset.single_le_sum (f := fun r => ∑ s ∈ Finset.Icc 1 (2*S), Complex.normSq (α r s))
        (fun r _ => Finset.sum_nonneg (fun s _ => Complex.normSq_nonneg _)) ?_
      rw [Finset.mem_Icc]
      omega
    exact le_trans hmain (mul_le_mul_of_nonneg_left hsub (by positivity))
  have hcoef : ∑ d ∈ Finset.Ioc D (2*D), (2*(S:ℝ)/(d:ℝ) + 1) ≤ (D:ℝ) + 2*(S:ℝ) := by
    have hstep1 : ∑ d ∈ Finset.Ioc D (2*D), (2*(S:ℝ)/(d:ℝ) + 1)
        ≤ ∑ d ∈ Finset.Ioc D (2*D), (2*(S:ℝ)/(D:ℝ) + 1) := by
      refine Finset.sum_le_sum (fun d hd => ?_)
      have hDpos : (0:ℝ) < (D:ℝ) := by exact_mod_cast hD
      have hDd : (D:ℝ) ≤ (d:ℝ) := by
        have h' := (Finset.mem_Ioc.mp hd).1
        exact_mod_cast le_of_lt h'
      have hle : 2*(S:ℝ)/(d:ℝ) ≤ 2*(S:ℝ)/(D:ℝ) :=
        div_le_div_of_nonneg_left (by positivity) hDpos hDd
      linarith
    have hstep2 : ∑ d ∈ Finset.Ioc D (2*D), (2*(S:ℝ)/(D:ℝ) + 1)
        = (D:ℝ) * (2*(S:ℝ)/(D:ℝ) + 1) := by
      rw [Finset.sum_const, Nat.card_Ioc]
      have h2 : 2 * D - D = D := by omega
      rw [h2, nsmul_eq_mul]
    have hstep3 : (D:ℝ) * (2*(S:ℝ)/(D:ℝ) + 1) = (D:ℝ) + 2*(S:ℝ) := by
      have hDne : (D:ℝ) ≠ 0 := by positivity
      field_simp
      ring
    linarith [hstep1, hstep2.le, hstep2.ge, hstep3.le]
  calc (∑ d ∈ Finset.Ioc D (2*D), Work.FIPlan.Evar R S d α)
      ≤ ∑ d ∈ Finset.Ioc D (2*D), (2*(S:ℝ)/(d:ℝ) + 1) * T := Finset.sum_le_sum hper
    _ = (∑ d ∈ Finset.Ioc D (2*D), (2*(S:ℝ)/(d:ℝ) + 1)) * T := by rw [Finset.sum_mul]
    _ ≤ ((D:ℝ) + 2*(S:ℝ)) * T := mul_le_mul_of_nonneg_right hcoef hTnn
    _ ≤ (3 * braceV D R S ε) * T :=
        mul_le_mul_of_nonneg_right (add_two_mul_le_three_braceV_r_one D R S ε hD hR hS hε) hTnn
    _ = 3 * braceV D R S ε * T := by ring

end

end Work.FIArea4
