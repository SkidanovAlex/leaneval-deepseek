import Mathlib
import Submission.Work.ZassenhausSuzuki.Odd.OddDefs
import Submission.Work.ZassenhausSuzuki.Odd.OddCore
import Submission.Work.ZassenhausSuzuki.Odd.OddFib
import Submission.Work.ZassenhausSuzuki.Odd.q_structure
import Submission.Work.ZassenhausSuzuki.Odd.isCZ_basic
import Submission.Work.ZassenhausSuzuki.Odd.twoPoint_isCZ
import Submission.Work.ZassenhausSuzuki.Odd.isCZ_conj_of_prime_dvd
import Submission.Work.ZassenhausSuzuki.Odd.kA_mem
import Submission.Work.ZassenhausSuzuki.Odd.card_conjugates
import Submission.Work.ZassenhausSuzuki.Odd.sum_card_mul_card_sub_one

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

/-!
# The fibre data fed to the numerical endgame

For every order `a` occurring in `ℱ = IsCZ` this file fixes the number `mVal a` of `ℱ`-subgroups
of order `a` and the normaliser index `kVal a` of such a subgroup, and proves the arithmetic
relations used by `Work.ZassenhausSuzuki.Odd.endgame_numeric`.
-/

set_option autoImplicit false
set_option linter.unusedVariables false
set_option maxHeartbeats 2000000

namespace Work.ZassenhausSuzuki.Odd

open Submission.Blueprint

/-- Membership in a conjugate subgroup. -/
theorem mem_conj_iff {G : Type} [Group G] {A : Subgroup G} {g x : G} :
    x ∈ Submission.Blueprint.conj g A ↔ g⁻¹ * x * g ∈ A := by
  simp only [Submission.Blueprint.conj, Subgroup.mem_map, MulEquiv.coe_toMonoidHom,
    MulAut.conj_apply]
  constructor
  · rintro ⟨a, ha, rfl⟩
    rw [show g⁻¹ * (g * a * g⁻¹) * g = a from by group]
    exact ha
  · intro hx
    exact ⟨g⁻¹ * x * g, hx, by group⟩

/-- The normaliser of a conjugate is the conjugate of the normaliser. -/
theorem map_normalizer_eq {G : Type} [Group G] (A : Subgroup G) (g : G) :
    Subgroup.normalizer ((Submission.Blueprint.conj g A : Subgroup G) : Set G)
      = Submission.Blueprint.conj g (Subgroup.normalizer (A : Set G)) := by
  ext x
  rw [mem_conj_iff, Subgroup.mem_normalizer_iff, Subgroup.mem_normalizer_iff]
  constructor
  · intro hx z
    have h := hx (g * z * g⁻¹)
    rw [mem_conj_iff, mem_conj_iff] at h
    rw [show g⁻¹ * (g * z * g⁻¹) * g = z from by group] at h
    rw [show (g⁻¹ * x * g) * z * (g⁻¹ * x * g)⁻¹ = g⁻¹ * (x * (g * z * g⁻¹) * x⁻¹) * g
      from by group]
    exact h
  · intro hx z
    rw [mem_conj_iff, mem_conj_iff]
    rw [show g⁻¹ * (x * z * x⁻¹) * g
      = (g⁻¹ * x * g) * (g⁻¹ * z * g) * (g⁻¹ * x * g)⁻¹ from by group]
    exact hx (g⁻¹ * z * g)

/-- `kA` is invariant under conjugation. -/
theorem kA_conj {G : Type} [Group G] [Finite G] (A : Subgroup G) (g : G) :
    kA (Submission.Blueprint.conj g A) = kA A := by
  have hN := map_normalizer_eq A g
  have hcard : Nat.card ↥(Subgroup.normalizer
      ((Submission.Blueprint.conj g A : Subgroup G) : Set G))
      = Nat.card ↥(Subgroup.normalizer (A : Set G)) := by
    rw [hN]
    exact Work.ZassenhausSuzuki.Odd.card_conj_eq _ g
  have hcardA : Nat.card ↥(Submission.Blueprint.conj g A) = Nat.card ↥A :=
    Work.ZassenhausSuzuki.Odd.card_conj_eq A g
  have hd : kA (Submission.Blueprint.conj g A) * Nat.card ↥(Submission.Blueprint.conj g A)
      = Nat.card ↥(Subgroup.normalizer
          ((Submission.Blueprint.conj g A : Subgroup G) : Set G)) := by
    have h1 := Subgroup.card_mul_index
      ((Submission.Blueprint.conj g A).subgroupOf
        (Subgroup.normalizer ((Submission.Blueprint.conj g A : Subgroup G) : Set G)))
    have h2 : Nat.card ↥((Submission.Blueprint.conj g A).subgroupOf
        (Subgroup.normalizer ((Submission.Blueprint.conj g A : Subgroup G) : Set G)))
        = Nat.card ↥(Submission.Blueprint.conj g A) :=
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe (Subgroup.le_normalizer)).toEquiv
    rw [h2, mul_comm] at h1
    exact h1
  have he : kA A * Nat.card ↥A = Nat.card ↥(Subgroup.normalizer (A : Set G)) := by
    have h1 := Subgroup.card_mul_index (A.subgroupOf (Subgroup.normalizer (A : Set G)))
    have h2 : Nat.card ↥(A.subgroupOf (Subgroup.normalizer (A : Set G))) = Nat.card ↥A :=
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe (Subgroup.le_normalizer)).toEquiv
    rw [h2, mul_comm] at h1
    exact h1
  have hpos : 0 < Nat.card ↥A := Nat.card_pos
  have hkey : kA (Submission.Blueprint.conj g A) * Nat.card ↥A = kA A * Nat.card ↥A := by
    calc kA (Submission.Blueprint.conj g A) * Nat.card ↥A
        = kA (Submission.Blueprint.conj g A) * Nat.card ↥(Submission.Blueprint.conj g A) := by
          rw [hcardA]
      _ = Nat.card ↥(Subgroup.normalizer
            ((Submission.Blueprint.conj g A : Subgroup G) : Set G)) := hd
      _ = Nat.card ↥(Subgroup.normalizer (A : Set G)) := hcard
      _ = kA A * Nat.card ↥A := he.symm
  exact Nat.mul_right_cancel hpos hkey

variable {G : Type} [Group G] [Finite G] {H Q : Subgroup G} {t : G}

/-- The number of `ℱ`-subgroups of order `a`. -/
noncomputable def mVal (G : Type) [Group G] [Finite G] (a : ℕ) : ℕ := (Fib G a).card

/-- A chosen `ℱ`-subgroup of order `a`. -/
noncomputable def repVals (G : Type) [Group G] [Finite G] (a : ℕ) : Subgroup G :=
  if h : a ∈ Vals G then Classical.choose ((mem_Vals (G := G)).mp h) else ⊥

/-- The normaliser index of a chosen `ℱ`-subgroup of order `a`. -/
noncomputable def kVal (G : Type) [Group G] [Finite G] (a : ℕ) : ℕ :=
  if h : a ∈ Vals G then kA (repVals G a) else 0

theorem repVals_mem {a : ℕ} (ha : a ∈ Vals G) :
    repVals G a ∈ FinsetCZ (G := G) ∧ Nat.card ↥(repVals G a) = a := by
  classical
  unfold repVals
  rw [dif_pos ha]
  exact Classical.choose_spec ((mem_Vals (G := G)).mp ha)

theorem kVal_eq {a : ℕ} (ha : a ∈ Vals G) : kVal G a = kA (repVals G a) := by
  classical
  unfold kVal
  rw [dif_pos ha]

/-- `mVal a * a * kVal a = |G|` for every order `a` occurring in `ℱ`. -/
theorem mVal_mul_kVal (h : SzOddHyp H Q t) {a : ℕ} (ha : a ∈ Vals G) :
    mVal G a * a * kVal G a = Nat.card G := by
  classical
  obtain ⟨hmem, hcard⟩ := repVals_mem (G := G) ha
  have hCZ : IsCZ (repVals G a) := mem_FinsetCZ.mp hmem
  have hconj := card_conjugates h hCZ
  have hfib := card_Fib_eq_card_conj h hCZ
  rw [hfib, hcard] at hconj
  rw [kVal_eq (G := G) ha]
  rw [mul_assoc]
  exact hconj

theorem kVal_mem (h : SzOddHyp H Q t) {a : ℕ} (ha : a ∈ Vals G) :
    kVal G a = 2 ∨ kVal G a = 4 := by
  classical
  obtain ⟨hmem, -⟩ := repVals_mem (G := G) ha
  rw [kVal_eq (G := G) ha]
  exact kA_mem h (mem_FinsetCZ.mp hmem)

theorem five_le_of_mem_Vals (h : SzOddHyp H Q t) {a : ℕ} (ha : a ∈ Vals G) : 5 ≤ a := by
  classical
  obtain ⟨hmem, hcard⟩ := repVals_mem (G := G) ha
  rw [← hcard]
  exact isCZ_card_ge_five h (mem_FinsetCZ.mp hmem)

theorem isCZ_of_mem_Vals {a : ℕ} (ha : a ∈ Vals G) : IsCZ (repVals G a) := by
  classical
  exact mem_FinsetCZ.mp (repVals_mem (G := G) ha).1

/-- `q - 1 = |twoPoint H t|` belongs to `Vals`. -/
theorem q_sub_one_mem_Vals (h : SzOddHyp H Q t) : q H - 1 ∈ Vals G := by
  classical
  obtain ⟨hCZ, hcard, -, -⟩ := twoPoint_isCZ h
  exact mem_Vals.mpr ⟨twoPoint H t, mem_FinsetCZ.mpr hCZ, hcard⟩

/-- The `k`-value of the order `q - 1` is `2` (`D = twoPoint H t` has normaliser index `2`). -/
theorem kVal_q_sub_one (h : SzOddHyp H Q t) : kVal G (q H - 1) = 2 := by
  classical
  obtain ⟨hCZ, hcard, hk, -⟩ := twoPoint_isCZ h
  obtain ⟨hmem, hcardA⟩ := repVals_mem (G := G) (q_sub_one_mem_Vals h)
  have hCZ' : IsCZ (repVals G (q H - 1)) := mem_FinsetCZ.mp hmem
  have hconj : ∃ g : G, twoPoint H t = conj g (repVals G (q H - 1)) :=
    isCZ_conj_of_card_eq h hCZ' hCZ (by rw [hcardA, hcard])
  rw [kVal_eq (G := G) (q_sub_one_mem_Vals h)]
  obtain ⟨g, hg⟩ := hconj
  rw [← kA_conj (A := repVals G (q H - 1)) g, ← hg]
  exact hk

/-- Every order occurring in `ℱ` other than `q - 1` is coprime to `q * (q - 1)`. -/
theorem coprime_of_mem_Vals (h : SzOddHyp H Q t) {a : ℕ} (ha : a ∈ Vals G)
    (hane : a ≠ q H - 1) : Nat.Coprime a (q H * (q H - 1)) := by
  classical
  obtain ⟨hCZ, hcard, -, -⟩ := twoPoint_isCZ h
  have hCZ' : IsCZ (repVals G a) := isCZ_of_mem_Vals ha
  have hcardA := (repVals_mem (G := G) ha).2
  have hcop1 : Nat.Coprime a (q H - 1) := by
    by_contra hc
    obtain ⟨p, hp, hpdvd⟩ := Nat.Prime.not_coprime_iff_dvd.mp hc
    have hp1 : p ∣ a := hpdvd.1
    have hp2 : p ∣ q H - 1 := hpdvd.2
    have hp1' : p ∣ Nat.card ↥(repVals G a) := by rw [hcardA]; exact hp1
    have hB : p ∣ Nat.card ↥(twoPoint H t) := by rw [hcard]; exact hp2
    obtain ⟨g, hg⟩ := isCZ_conj_of_prime_dvd h hCZ' hCZ hp hp1' hB
    have : a = q H - 1 := by
      rw [← hcardA, ← card_conj_eq (repVals G a) g, ← hg, hcard]
    exact hane this
  have hodd : Odd a := by
    obtain ⟨-, hodd, -⟩ := isCZ_basic h hCZ'
    rwa [hcardA] at hodd
  have hcop2 : Nat.Coprime a (q H) := by
    obtain ⟨l, hl⟩ := (q_structure h).2.2.2.1
    rw [hl]
    exact Nat.Coprime.pow_right l (Odd.coprime_two_right hodd)
  exact Nat.Coprime.mul_right hcop2 hcop1

/-- Distinct orders occurring in `ℱ` other than `q - 1` are coprime. -/
theorem coprime_pair_of_mem_Vals (h : SzOddHyp H Q t) {a b : ℕ} (ha : a ∈ Vals G)
    (hb : b ∈ Vals G) (hab : a ≠ b) : Nat.Coprime a b := by
  classical
  by_contra hc
  obtain ⟨p, hp, hpdvd⟩ := Nat.Prime.not_coprime_iff_dvd.mp hc
  obtain ⟨-, hcardA⟩ := repVals_mem (G := G) ha
  obtain ⟨-, hcardB⟩ := repVals_mem (G := G) hb
  have h1 : p ∣ Nat.card ↥(repVals G a) := by rw [hcardA]; exact hpdvd.1
  have h2 : p ∣ Nat.card ↥(repVals G b) := by rw [hcardB]; exact hpdvd.2
  obtain ⟨g, hg⟩ := isCZ_conj_of_prime_dvd h (isCZ_of_mem_Vals ha) (isCZ_of_mem_Vals hb) hp h1 h2
  have hg' : repVals G b = conj g (repVals G a) := hg
  have : a = b := by rw [← hcardA, ← card_conj_eq (repVals G a) g, ← hg', hcardB]
  exact hab this

/-- The class-count relation, in the form used by the numerical endgame. -/
theorem hsum2_rat (h : SzOddHyp H Q t) :
    ∑ a ∈ Vals G, (mVal G a : ℚ) * a * (a - 1)
      = (q H ^ 2 * (q H - 1) * (q H ^ 2 + 1) : ℚ) * (q H - 1) := by
  classical
  have hq1 : 1 ≤ q H := by have := (q_structure h).2.2.1; omega
  have hnat : (∑ a ∈ Vals G, mVal G a * (a * (a - 1)))
      = q H ^ 2 * (q H - 1) * (q H ^ 2 + 1) * (q H - 1) := by
    rw [show (∑ a ∈ Vals G, mVal G a * (a * (a - 1)))
        = ∑ a ∈ Vals G, (Fib G a).card * (a * (a - 1)) from rfl]
    rw [← sum_card_mul_card_sub_one_eq_sum_Fib (G := G)]
    rw [sum_card_mul_card_sub_one h, card_G_eq h]
  have hmain : (((∑ a ∈ Vals G, mVal G a * (a * (a - 1))) : ℕ) : ℚ)
      = ∑ a ∈ Vals G, (mVal G a : ℚ) * a * (a - 1) := by
    rw [Nat.cast_sum]
    refine Finset.sum_congr rfl ?_
    intro a ha
    have ha1 : 1 ≤ a := by have := five_le_of_mem_Vals h ha; omega
    have h1 : ((a - 1 : ℕ) : ℚ) = (a : ℚ) - 1 := by rw [Nat.cast_sub ha1, Nat.cast_one]
    rw [Nat.cast_mul, Nat.cast_mul, h1]
    ring
  rw [← hmain, hnat]
  simp only [Nat.cast_mul, Nat.cast_pow, Nat.cast_add, Nat.cast_one, Nat.cast_sub hq1]

end Work.ZassenhausSuzuki.Odd
