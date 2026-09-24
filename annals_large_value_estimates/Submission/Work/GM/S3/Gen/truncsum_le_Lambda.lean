import Mathlib
import Submission.Work.GM.S3.Gen.Iterm_norm_swap

/-!
# The truncation-cube sum of `‖I_m‖` is at most three times its `Λ`-part

GM §7 use the symmetry of `I_m` under permuting the three slots to bound the full sum over the
truncation cube by three times the sum over the region `Λ = {m : |m₁| ≤ |m₂| ∧ |m₃| ≤ |m₂|}` in
which the *second* coordinate has the largest modulus (GM 7.2, and the cell decomposition of the
present development, see `NOTES_cell_route.md`).

Concretely, for the cube `C = Icc(-⌊Kc⌋) ⌊Kc⌋ × Icc(-⌊Kc⌋) ⌊Kc⌋ × Icc(-⌊Kc⌋) ⌊Kc⌋` and

* `A m = ‖I_m‖` if all three coordinates of `m` are nonzero, `0` otherwise,
* `B m = ‖I_m‖` if all three coordinates are nonzero **and** `m ∈ Λ`, `0` otherwise,

we prove `Σ_{m ∈ C} A m ≤ 3 Σ_{m ∈ C} B m`.

The mechanism is the two norm-preserving involutions of `ℤ³`

* `tslSw12 (m₁,m₂,m₃) = (-m₂,-m₁,-m₃)`  (`‖I_{tslSw12 m}‖ = ‖I_m‖`, `norm_Iterm_swap12`),
* `tslSw23 (m₁,m₂,m₃) = (-m₁,-m₃,-m₂)`  (`‖I_{tslSw23 m}‖ = ‖I_m‖`, `norm_Iterm_swap23`),

which exchange `Λ` with the two regions `Λ₁` (`|m₁|` largest) and `Λ₃` (`|m₃|` largest), and are
self-inverse bijections of the cube.  Every triple with all coordinates nonzero lies in
`Λ ∪ Λ₁ ∪ Λ₃`, so

`Σ_C A ≤ Σ_Λ A + Σ_{Λ₁} A + Σ_{Λ₃} A = Σ_Λ A + Σ_Λ A + Σ_Λ A = 3 Σ_C B`.
-/

namespace Work.GM.S3.Gen

open Finset
open scoped BigOperators
open Submission.GM (Iterm)

/-- The involution `(m₁,m₂,m₃) ↦ (-m₂,-m₁,-m₃)` of `ℤ³` (it exchanges the two first slots and
negates): on `‖Iterm‖` it is the identity and it maps `Λ₁` onto `Λ`. -/
def tslSw12 (m : ℤ × ℤ × ℤ) : ℤ × ℤ × ℤ := (-m.2.1, -m.1, -m.2.2)

/-- The involution `(m₁,m₂,m₃) ↦ (-m₁,-m₃,-m₂)` of `ℤ³` (it exchanges the two last slots and
negates): on `‖Iterm‖` it is the identity and it maps `Λ₃` onto `Λ`. -/
def tslSw23 (m : ℤ × ℤ × ℤ) : ℤ × ℤ × ℤ := (-m.1, -m.2.2, -m.2.1)

theorem tslSw12_invol (m : ℤ × ℤ × ℤ) : tslSw12 (tslSw12 m) = m := by simp [tslSw12]

theorem tslSw23_invol (m : ℤ × ℤ × ℤ) : tslSw23 (tslSw23 m) = m := by simp [tslSw23]

/-- `m` has no vanishing coordinate. -/
def tslNz (m : ℤ × ℤ × ℤ) : Prop := m.1 ≠ 0 ∧ m.2.1 ≠ 0 ∧ m.2.2 ≠ 0

/-- GM's `Λ`: the *second* coordinate has the largest modulus. -/
def tslLam (m : ℤ × ℤ × ℤ) : Prop := |(m.1 : ℝ)| ≤ |(m.2.1 : ℝ)| ∧ |(m.2.2 : ℝ)| ≤ |(m.2.1 : ℝ)|

/-- `Λ₁`: the *first* coordinate has the largest modulus. -/
def tslLam1 (m : ℤ × ℤ × ℤ) : Prop := |(m.2.1 : ℝ)| ≤ |(m.1 : ℝ)| ∧ |(m.2.2 : ℝ)| ≤ |(m.1 : ℝ)|

/-- `Λ₃`: the *third* coordinate has the largest modulus. -/
def tslLam3 (m : ℤ × ℤ × ℤ) : Prop := |(m.1 : ℝ)| ≤ |(m.2.2 : ℝ)| ∧ |(m.2.1 : ℝ)| ≤ |(m.2.2 : ℝ)|

theorem tslNz_tslSw12 (m : ℤ × ℤ × ℤ) : tslNz (tslSw12 m) ↔ tslNz m := by
  simp [tslNz, tslSw12, and_left_comm]

theorem tslNz_tslSw23 (m : ℤ × ℤ × ℤ) : tslNz (tslSw23 m) ↔ tslNz m := by
  simp [tslNz, tslSw23, and_comm]

theorem tslLam_tslSw12 (m : ℤ × ℤ × ℤ) : tslLam (tslSw12 m) ↔ tslLam1 m := by simp [tslLam, tslLam1, tslSw12]

theorem tslLam1_tslSw12 (m : ℤ × ℤ × ℤ) : tslLam1 (tslSw12 m) ↔ tslLam m := by simp [tslLam, tslLam1, tslSw12]

theorem tslLam_tslSw23 (m : ℤ × ℤ × ℤ) : tslLam (tslSw23 m) ↔ tslLam3 m := by simp [tslLam, tslLam3, tslSw23]

theorem tslLam3_tslSw23 (m : ℤ × ℤ × ℤ) : tslLam3 (tslSw23 m) ↔ tslLam m := by simp [tslLam, tslLam3, tslSw23]

theorem tsl_norm_tslSw12 (N : ℕ) (W : Finset ℝ) (m : ℤ × ℤ × ℤ) :
    ‖Iterm N W (tslSw12 m)‖ = ‖Iterm N W m‖ := by
  have h := norm_Iterm_swap12 N W m.1 m.2.1 m.2.2
  simpa [tslSw12] using h.symm

theorem tsl_norm_tslSw23 (N : ℕ) (W : Finset ℝ) (m : ℤ × ℤ × ℤ) :
    ‖Iterm N W (tslSw23 m)‖ = ‖Iterm N W m‖ := by
  have h := norm_Iterm_swap23 N W m.1 m.2.1 m.2.2
  simpa [tslSw23] using h.symm

/-- `A m = ‖I_m‖` on triples with no vanishing coordinate, `0` otherwise. -/
noncomputable def tslA (N : ℕ) (W : Finset ℝ) (m : ℤ × ℤ × ℤ) : ℝ := by
  classical exact if tslNz m then ‖Iterm N W m‖ else 0

/-- `B m = ‖I_m‖` on `Λ`-triples with no vanishing coordinate, `0` otherwise. -/
noncomputable def tslB (N : ℕ) (W : Finset ℝ) (m : ℤ × ℤ × ℤ) : ℝ := by
  classical exact if tslNz m ∧ tslLam m then ‖Iterm N W m‖ else 0

/-- `C m = ‖I_m‖` on `Λ₁`-triples with no vanishing coordinate, `0` otherwise. -/
noncomputable def tslC (N : ℕ) (W : Finset ℝ) (m : ℤ × ℤ × ℤ) : ℝ := by
  classical exact if tslNz m ∧ tslLam1 m then ‖Iterm N W m‖ else 0

/-- `D m = ‖I_m‖` on `Λ₃`-triples with no vanishing coordinate, `0` otherwise. -/
noncomputable def tslD (N : ℕ) (W : Finset ℝ) (m : ℤ × ℤ × ℤ) : ℝ := by
  classical exact if tslNz m ∧ tslLam3 m then ‖Iterm N W m‖ else 0

/-- Of three real numbers, one is a maximum. -/
lemma tsl_max_cases (x y z : ℝ) : (y ≤ x ∧ z ≤ x) ∨ (x ≤ y ∧ z ≤ y) ∨ (x ≤ z ∧ y ≤ z) := by
  rcases le_total x y with hxy | hyx
  · rcases le_total y z with hyz | hzy
    · exact Or.inr (Or.inr ⟨le_trans hxy hyz, hyz⟩)
    · exact Or.inr (Or.inl ⟨hxy, hzy⟩)
  · rcases le_total x z with hxz | hzx
    · exact Or.inr (Or.inr ⟨hxz, le_trans hyx hxz⟩)
    · exact Or.inl ⟨hyx, hzx⟩

theorem truncsum_le_Lambda (N : ℕ) (W : Finset ℝ) (Kc : ℝ) :
    (∑ m₁ ∈ Finset.Icc (-⌊Kc⌋) ⌊Kc⌋,
      ∑ m₂ ∈ Finset.Icc (-⌊Kc⌋) ⌊Kc⌋,
      ∑ m₃ ∈ Finset.Icc (-⌊Kc⌋) ⌊Kc⌋,
        (if m₁ ≠ 0 ∧ m₂ ≠ 0 ∧ m₃ ≠ 0 then ‖Submission.GM.Iterm N W (m₁, m₂, m₃)‖ else 0)) ≤
      3 * (∑ m₁ ∈ Finset.Icc (-⌊Kc⌋) ⌊Kc⌋,
        ∑ m₂ ∈ Finset.Icc (-⌊Kc⌋) ⌊Kc⌋,
        ∑ m₃ ∈ Finset.Icc (-⌊Kc⌋) ⌊Kc⌋,
          (if m₁ ≠ 0 ∧ m₂ ≠ 0 ∧ m₃ ≠ 0 ∧ |(m₁ : ℝ)| ≤ |(m₂ : ℝ)| ∧ |(m₃ : ℝ)| ≤ |(m₂ : ℝ)|
            then ‖Submission.GM.Iterm N W (m₁, m₂, m₃)‖ else 0)) := by
  classical
  set s : Finset ℤ := Finset.Icc (-⌊Kc⌋) ⌊Kc⌋ with hs
  -- the cube `s ×ˢ (s ×ˢ s)` is invariant under the two swaps
  have hneg : ∀ a ∈ s, -a ∈ s := by
    intro a ha
    rw [hs] at ha ⊢
    simp only [Finset.mem_Icc] at ha ⊢
    constructor <;> omega
  have hSiff : ∀ m : ℤ × ℤ × ℤ, m ∈ s ×ˢ (s ×ˢ s) ↔ m.1 ∈ s ∧ m.2.1 ∈ s ∧ m.2.2 ∈ s := by
    intro m; simp [Finset.mem_product]
  have hS12 : ∀ m ∈ s ×ˢ (s ×ˢ s), tslSw12 m ∈ s ×ˢ (s ×ˢ s) := by
    intro m hm
    rw [hSiff] at hm ⊢
    simp only [tslSw12]
    exact ⟨hneg _ hm.2.1, hneg _ hm.1, hneg _ hm.2.2⟩
  have hS23 : ∀ m ∈ s ×ˢ (s ×ˢ s), tslSw23 m ∈ s ×ˢ (s ×ˢ s) := by
    intro m hm
    rw [hSiff] at hm ⊢
    simp only [tslSw23]
    exact ⟨hneg _ hm.1, hneg _ hm.2.2, hneg _ hm.2.1⟩
  -- the two triple sums, read as sums over the cube
  have hAconv : (∑ m ∈ s ×ˢ (s ×ˢ s), tslA N W m)
      = ∑ m₁ ∈ s, ∑ m₂ ∈ s, ∑ m₃ ∈ s,
          (if m₁ ≠ 0 ∧ m₂ ≠ 0 ∧ m₃ ≠ 0 then ‖Iterm N W (m₁, m₂, m₃)‖ else 0) := by
    rw [Finset.sum_product]
    simp only [Finset.sum_product]
    refine Finset.sum_congr rfl (fun a _ => Finset.sum_congr rfl (fun b _ =>
      Finset.sum_congr rfl (fun c _ => ?_)))
    unfold tslA
    by_cases h : tslNz (a, b, c)
    · rw [if_pos h, if_pos (by simpa [tslNz] using h)]
    · rw [if_neg h, if_neg (by simpa [tslNz] using h)]
  have hBconv : (∑ m ∈ s ×ˢ (s ×ˢ s), tslB N W m)
      = ∑ m₁ ∈ s, ∑ m₂ ∈ s, ∑ m₃ ∈ s,
          (if m₁ ≠ 0 ∧ m₂ ≠ 0 ∧ m₃ ≠ 0 ∧ |(m₁ : ℝ)| ≤ |(m₂ : ℝ)| ∧ |(m₃ : ℝ)| ≤ |(m₂ : ℝ)|
            then ‖Iterm N W (m₁, m₂, m₃)‖ else 0) := by
    rw [Finset.sum_product]
    simp only [Finset.sum_product]
    refine Finset.sum_congr rfl (fun a _ => Finset.sum_congr rfl (fun b _ =>
      Finset.sum_congr rfl (fun c _ => ?_)))
    unfold tslB
    by_cases h : tslNz (a, b, c) ∧ tslLam (a, b, c)
    · have h' : a ≠ 0 ∧ b ≠ 0 ∧ c ≠ 0 ∧ |(a : ℝ)| ≤ |(b : ℝ)| ∧ |(c : ℝ)| ≤ |(b : ℝ)| := by
        simpa [tslNz, tslLam, and_assoc] using h
      rw [if_pos h, if_pos h']
    · have h' : ¬(a ≠ 0 ∧ b ≠ 0 ∧ c ≠ 0 ∧ |(a : ℝ)| ≤ |(b : ℝ)| ∧ |(c : ℝ)| ≤ |(b : ℝ)|) := by
        simpa [tslNz, tslLam, and_assoc] using h
      rw [if_neg h, if_neg h']
  -- the combinatorial inequality on the cube
  have hmain : ∑ m ∈ s ×ˢ (s ×ˢ s), tslA N W m
      ≤ 3 * ∑ m ∈ s ×ˢ (s ×ˢ s), tslB N W m := by
    have h1 : ∑ m ∈ s ×ˢ (s ×ˢ s), tslA N W m
        ≤ ∑ m ∈ s ×ˢ (s ×ˢ s), (tslB N W m + tslC N W m + tslD N W m) := by
      refine Finset.sum_le_sum (fun m _ => ?_)
      have hBnn : 0 ≤ tslB N W m := by unfold tslB; split <;> simp
      have hCnn : 0 ≤ tslC N W m := by unfold tslC; split <;> simp
      have hDnn : 0 ≤ tslD N W m := by unfold tslD; split <;> simp
      by_cases hnz : tslNz m
      · have hA : tslA N W m = ‖Iterm N W m‖ := by unfold tslA; exact if_pos hnz
        rcases tsl_max_cases (|(m.2.1 : ℝ)|) (|(m.1 : ℝ)|) (|(m.2.2 : ℝ)|) with
          ⟨e1, e2⟩ | ⟨e1, e2⟩ | ⟨e1, e2⟩
        · have hB : tslB N W m = ‖Iterm N W m‖ := by
            unfold tslB; exact if_pos ⟨hnz, ⟨e1, e2⟩⟩
          rw [hA, hB]; linarith
        · have hC : tslC N W m = ‖Iterm N W m‖ := by
            unfold tslC; exact if_pos ⟨hnz, ⟨e1, e2⟩⟩
          rw [hA, hC]; linarith
        · have hD : tslD N W m = ‖Iterm N W m‖ := by
            unfold tslD; exact if_pos ⟨hnz, ⟨e2, e1⟩⟩
          rw [hA, hD]; linarith
      · have hA : tslA N W m = 0 := by unfold tslA; exact if_neg hnz
        rw [hA]; linarith
    have h2 : ∑ m ∈ s ×ˢ (s ×ˢ s), tslC N W m = ∑ m ∈ s ×ˢ (s ×ˢ s), tslB N W m := by
      refine Finset.sum_bij' (fun m _ => tslSw12 m) (fun m _ => tslSw12 m) hS12 hS12 ?_ ?_ ?_
      · intro a _; exact tslSw12_invol a
      · intro a _; exact tslSw12_invol a
      · intro a _
        unfold tslC tslB
        by_cases h : tslNz a ∧ tslLam1 a
        · have h' : tslNz (tslSw12 a) ∧ tslLam (tslSw12 a) :=
            ⟨(tslNz_tslSw12 a).mpr h.1, (tslLam_tslSw12 a).mpr h.2⟩
          rw [if_pos h, if_pos h']
          exact (tsl_norm_tslSw12 N W a).symm
        · have h' : ¬ (tslNz (tslSw12 a) ∧ tslLam (tslSw12 a)) :=
            fun hh => h ⟨(tslNz_tslSw12 a).mp hh.1, (tslLam_tslSw12 a).mp hh.2⟩
          rw [if_neg h, if_neg h']
    have h3 : ∑ m ∈ s ×ˢ (s ×ˢ s), tslD N W m = ∑ m ∈ s ×ˢ (s ×ˢ s), tslB N W m := by
      refine Finset.sum_bij' (fun m _ => tslSw23 m) (fun m _ => tslSw23 m) hS23 hS23 ?_ ?_ ?_
      · intro a _; exact tslSw23_invol a
      · intro a _; exact tslSw23_invol a
      · intro a _
        unfold tslD tslB
        by_cases h : tslNz a ∧ tslLam3 a
        · have h' : tslNz (tslSw23 a) ∧ tslLam (tslSw23 a) :=
            ⟨(tslNz_tslSw23 a).mpr h.1, (tslLam_tslSw23 a).mpr h.2⟩
          rw [if_pos h, if_pos h']
          exact (tsl_norm_tslSw23 N W a).symm
        · have h' : ¬ (tslNz (tslSw23 a) ∧ tslLam (tslSw23 a)) :=
            fun hh => h ⟨(tslNz_tslSw23 a).mp hh.1, (tslLam_tslSw23 a).mp hh.2⟩
          rw [if_neg h, if_neg h']
    calc ∑ m ∈ s ×ˢ (s ×ˢ s), tslA N W m
        ≤ ∑ m ∈ s ×ˢ (s ×ˢ s), (tslB N W m + tslC N W m + tslD N W m) := h1
      _ = ∑ m ∈ s ×ˢ (s ×ˢ s), tslB N W m + ∑ m ∈ s ×ˢ (s ×ˢ s), tslC N W m
            + ∑ m ∈ s ×ˢ (s ×ˢ s), tslD N W m := by
          rw [Finset.sum_add_distrib, Finset.sum_add_distrib]
      _ = 3 * ∑ m ∈ s ×ˢ (s ×ˢ s), tslB N W m := by
          rw [h2, h3]; ring
  rw [← hAconv, ← hBconv]
  exact hmain

end Work.GM.S3.Gen
