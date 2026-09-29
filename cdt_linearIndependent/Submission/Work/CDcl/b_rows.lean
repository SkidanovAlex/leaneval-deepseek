import Mathlib
import Submission.Work.CDcl.rowdefs

/-!
# `Work.CDcl.b_rows`: the `B`-rows of `CDClosed`

Given the `D`-closure data `(q₀, A₀)` of the seven pure functions
`Submission.CDTPlan.pureB = ![B₁,…,B₇]`,

  `q₀ · (pureB a)' = Σ_k A₀ a k · pureB k`   for all `a : Fin 7`,

we produce the corresponding row for the 17-tuple `Submission.CDTPlan.seventeen`
(entries `0..4, 9, 10` are `B₁,…,B₅,B₆,B₇`), with the common denominator `qOf q₀ = X⁴ · q₀`
and the coefficient matrix `AOf`. The only work is the reindexing of the 17-term sum onto
the seven `B`-slots via `eIdx`.
-/

namespace Work.CDcl

open PowerSeries Polynomial

noncomputable section

/-- `eIdx` is injective. -/
lemma eIdx_inj : Function.Injective eIdx := by
  intro a b h
  fin_cases a <;> fin_cases b <;> simp [eIdx] at h ⊢

/-- `seventeen` restricts to `pureB` along the slot embedding `eIdx`. -/
lemma seventeen_eIdx (m n : ℕ) (ra rb rab r0 : ℤ) (b : Fin 7) :
    Submission.CDTPlan.seventeen m n ra rb rab r0 (eIdx b)
      = Submission.CDTPlan.pureB b := by
  fin_cases b <;> simp [Submission.CDTPlan.seventeen, Submission.CDTPlan.pureB, eIdx]

/-- On the `B`-rows, `AOf` is the rescaled `A₀`. -/
lemma AOf_eIdx (q0 : Polynomial ℚ) (A0 : Fin 7 → Fin 7 → Polynomial ℚ) (G : PowerSeries ℚ)
    (a : Fin 7) (j : Fin 17) :
    AOf q0 A0 G (eIdx a) j = rowB q0 A0 a j := by
  fin_cases a <;> simp [AOf, eIdx]

/-- `rowB` evaluated at a slot index. -/
lemma rowB_eIdx (q0 : Polynomial ℚ) (A0 : Fin 7 → Fin 7 → Polynomial ℚ) (a b : Fin 7) :
    rowB q0 A0 a (eIdx b) = Polynomial.X ^ 4 * A0 a b := by
  fin_cases b <;> simp [rowB, eIdx]

/-- `rowB` vanishes off the image of `eIdx`. -/
lemma rowB_zero (q0 : Polynomial ℚ) (A0 : Fin 7 → Fin 7 → Polynomial ℚ) (a : Fin 7) {j : Fin 17}
    (h : j ∉ Set.range eIdx) : rowB q0 A0 a j = 0 := by
  have h5 : ¬ j.val < 5 := by
    intro hlt
    exact h ⟨⟨j.val, by omega⟩, by ext; simp [eIdx, hlt]⟩
  have h9 : j.val ≠ 9 := by
    intro h9
    exact h ⟨5, by ext; simp [eIdx, h9]⟩
  have h10 : j.val ≠ 10 := by
    intro h10
    exact h ⟨6, by ext; simp [eIdx, h10]⟩
  have h0 : j.val ≠ 0 := by omega
  have h1 : j.val ≠ 1 := by omega
  have h2 : j.val ≠ 2 := by omega
  have h3 : j.val ≠ 3 := by omega
  have h4 : j.val ≠ 4 := by omega
  simp [rowB, h0, h1, h2, h3, h4, h9, h10]

/-- A sum over `Fin 17` whose summand vanishes off the slots `eIdx` collapses to a sum over
`Fin 7`. -/
lemma sum_eIdx {M : Type*} [AddCommMonoid M] (f : Fin 17 → M)
    (h : ∀ j, j ∉ Set.range eIdx → f j = 0) :
    ∑ j : Fin 17, f j = ∑ a : Fin 7, f (eIdx a) := by
  classical
  have hinj : Set.InjOn eIdx ↑(Finset.univ : Finset (Fin 7)) :=
    fun a _ b _ hab => eIdx_inj hab
  have himg : (Finset.univ.filter (fun j : Fin 17 => j ∈ Set.range eIdx))
      = Finset.image eIdx Finset.univ := by
    ext j; simp
  have hzero : ∀ x ∈ (Finset.univ : Finset (Fin 17)),
      x ∉ Finset.univ.filter (fun j : Fin 17 => j ∈ Set.range eIdx) → f x = 0 := by
    intro x _ hx
    exact h x (by
      intro hmem
      exact hx (Finset.mem_filter.mpr ⟨Finset.mem_univ x, hmem⟩))
  rw [← Finset.sum_subset
    (Finset.filter_subset (fun j : Fin 17 => j ∈ Set.range eIdx) Finset.univ) hzero]
  rw [himg, Finset.sum_image hinj]

/-- The sum of the `rowB`-row against the 17 functions is the `B`-row of `pureB`, rescaled by
`X⁴`. -/
lemma rowB_sum (q0 : Polynomial ℚ) (A0 : Fin 7 → Fin 7 → Polynomial ℚ) (a : Fin 7)
    (m n : ℕ) (ra rb rab r0 : ℤ) :
    (∑ j : Fin 17, (rowB q0 A0 a j : PowerSeries ℚ)
        * Submission.CDTPlan.seventeen m n ra rb rab r0 j)
    = ((Polynomial.X ^ 4 : Polynomial ℚ) : PowerSeries ℚ)
        * ∑ k : Fin 7, (A0 a k : PowerSeries ℚ) * Submission.CDTPlan.pureB k := by
  rw [sum_eIdx (fun j => (rowB q0 A0 a j : PowerSeries ℚ)
        * Submission.CDTPlan.seventeen m n ra rb rab r0 j)
      (fun j hj => by rw [rowB_zero q0 A0 a hj, Polynomial.coe_zero, zero_mul])]
  have hb : ∀ b : Fin 7,
      (rowB q0 A0 a (eIdx b) : PowerSeries ℚ)
        * Submission.CDTPlan.seventeen m n ra rb rab r0 (eIdx b)
      = ((Polynomial.X ^ 4 : Polynomial ℚ) : PowerSeries ℚ)
        * ((A0 a b : PowerSeries ℚ) * Submission.CDTPlan.pureB b) := by
    intro b
    rw [rowB_eIdx, seventeen_eIdx, Polynomial.coe_mul]
    ring
  rw [Finset.sum_congr rfl (fun b _ => hb b), Finset.mul_sum]

theorem b_rows (q0 : Polynomial ℚ) (A0 : Fin 7 → Fin 7 → Polynomial ℚ)
    (hA0 : ∀ a : Fin 7, (q0 : PowerSeries ℚ) *
        PowerSeries.derivative (R := ℚ) (Submission.CDTPlan.pureB a)
      = ∑ k, (A0 a k : PowerSeries ℚ) * Submission.CDTPlan.pureB k)
    (m n : ℕ) (ra rb rab r0 : ℤ) (a : Fin 7) :
    (Work.CDcl.qOf q0 : PowerSeries ℚ) *
        PowerSeries.derivative (R := ℚ)
          (Submission.CDTPlan.seventeen m n ra rb rab r0 (Work.CDcl.eIdx a))
      = ∑ j, (Work.CDcl.AOf q0 A0 (Submission.CDTPlan.GC m n ra rb rab r0) (Work.CDcl.eIdx a) j :
            PowerSeries ℚ) * Submission.CDTPlan.seventeen m n ra rb rab r0 j := by
  rw [seventeen_eIdx]
  rw [show (∑ j : Fin 17, (AOf q0 A0 (Submission.CDTPlan.GC m n ra rb rab r0)
        (eIdx a) j : PowerSeries ℚ)
        * Submission.CDTPlan.seventeen m n ra rb rab r0 j)
      = ∑ j : Fin 17, (rowB q0 A0 a j : PowerSeries ℚ)
        * Submission.CDTPlan.seventeen m n ra rb rab r0 j from
      Finset.sum_congr rfl (fun j _ => by rw [AOf_eIdx])]
  rw [rowB_sum q0 A0 a m n ra rb rab r0, ← hA0 a, qOf, Polynomial.coe_mul]
  ring

end

end Work.CDcl
