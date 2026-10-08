import Mathlib
import Submission.Work.BG.CharBridge

open scoped Classical

namespace Work.BG

open OddOrder.RepresentationTheory

/-- Orthonormality of irreducible characters, stated for unbundled class functions. -/
private lemma inner_irr {G : Type*} [Group G] [Finite G] [Fintype G]
    [Invertible (Nat.card G : ℂ)]
    {φ ψ : ClassFunction G ℂ} (hφ : IsIrreducibleCharacter φ)
    (hψ : IsIrreducibleCharacter ψ) :
    ClassFunction.inner φ ψ = if φ = ψ then 1 else 0 := by
  have h := irreducibleCharacter_inner_eq_ite (⟨φ, hφ⟩ : IrreducibleCharacter G)
    (⟨ψ, hψ⟩ : IrreducibleCharacter G)
  simp only [IrreducibleCharacter.coe_mk] at h
  by_cases hab : φ = ψ
  · have hc : (⟨φ, hφ⟩ : IrreducibleCharacter G) = ⟨ψ, hψ⟩ := Subtype.ext hab
    rw [ite_eq_left hc] at h
    rw [ite_eq_left hab]; exact h
  · have hc : ¬ ((⟨φ, hφ⟩ : IrreducibleCharacter G) = ⟨ψ, hψ⟩) :=
      fun hh => hab (Subtype.ext_iff.mp hh)
    rw [ite_eq_right hc] at h
    rw [ite_eq_right hab]; exact h

/-- Inner-product computation in the case `γ = α`, `ζ = β`:
the orthogonality `⟨aα+bβ, cα+dβ⟩ = 0` forces `a c + b d = 0` over `ℤ`. -/
private lemma inner_eq_case1 {G : Type*} [Group G] [Finite G] [Fintype G]
    [Invertible (Nat.card G : ℂ)]
    {a b c d : ℤ} {α β : ClassFunction G ℂ}
    (hα : IsIrreducibleCharacter α) (hβ : IsIrreducibleCharacter β) (hαβ : α ≠ β)
    (horth : ClassFunction.inner ((a : ℂ) • α + (b : ℂ) • β)
        ((c : ℂ) • α + (d : ℂ) • β) = 0) :
    a * c + b * d = 0 := by
  have hαα : ClassFunction.inner α α = 1 := by rw [inner_irr hα hα]; simp
  have hαβ0 : ClassFunction.inner α β = 0 := by
    rw [inner_irr hα hβ]; rw [ite_eq_right hαβ]
  have hβα0 : ClassFunction.inner β α = 0 := by
    rw [inner_irr hβ hα]; rw [ite_eq_right (Ne.symm hαβ)]
  have hββ : ClassFunction.inner β β = 1 := by rw [inner_irr hβ hβ]; simp
  have hnorm := horth
  simp only [ClassFunction.inner_add_left, ClassFunction.inner_add_right,
    ClassFunction.inner_smul_left, ClassFunction.inner_smul_right,
    hαα, hαβ0, hβα0, hββ] at hnorm
  simp only [mul_one, mul_zero, add_zero, zero_add, star_intCast] at hnorm
  have hcast : (((a * c + b * d : ℤ)) : ℂ) = 0 := by
    push_cast
    linear_combination hnorm
  exact Int.cast_eq_zero.mp hcast

/-- Inner-product computation in the case `γ = β`, `ζ = α`:
the orthogonality `⟨aα+bβ, cβ+dα⟩ = 0` forces `a d + b c = 0` over `ℤ`. -/
private lemma inner_eq_case2 {G : Type*} [Group G] [Finite G] [Fintype G]
    [Invertible (Nat.card G : ℂ)]
    {a b c d : ℤ} {α β : ClassFunction G ℂ}
    (hα : IsIrreducibleCharacter α) (hβ : IsIrreducibleCharacter β) (hαβ : α ≠ β)
    (horth : ClassFunction.inner ((a : ℂ) • α + (b : ℂ) • β)
        ((c : ℂ) • β + (d : ℂ) • α) = 0) :
    a * d + b * c = 0 := by
  have hαα : ClassFunction.inner α α = 1 := by rw [inner_irr hα hα]; simp
  have hαβ0 : ClassFunction.inner α β = 0 := by
    rw [inner_irr hα hβ]; rw [ite_eq_right hαβ]
  have hβα0 : ClassFunction.inner β α = 0 := by
    rw [inner_irr hβ hα]; rw [ite_eq_right (Ne.symm hαβ)]
  have hββ : ClassFunction.inner β β = 1 := by rw [inner_irr hβ hβ]; simp
  have hnorm := horth
  simp only [ClassFunction.inner_add_left, ClassFunction.inner_add_right,
    ClassFunction.inner_smul_left, ClassFunction.inner_smul_right,
    hαα, hαβ0, hβα0, hββ] at hnorm
  simp only [mul_one, mul_zero, add_zero, zero_add, star_intCast] at hnorm
  have hcast : (((a * d + b * c : ℤ)) : ℂ) = 0 := by
    push_cast
    linear_combination hnorm
  exact Int.cast_eq_zero.mp hcast

/-- Degree computation in the case `γ = α`, `ζ = β`, given `α 1 = p`, `β 1 = q`. -/
private lemma deg_eq_case1 {G : Type*} [Group G] [Finite G] [Fintype G]
    [Invertible (Nat.card G : ℂ)]
    {a b c d p q : ℤ} {α β : ClassFunction G ℂ}
    (hα1 : α 1 = (p : ℂ)) (hβ1 : β 1 = (q : ℂ))
    (hdeg : ((a : ℂ) • α + (b : ℂ) • β) (1 : G) =
        ((c : ℂ) • α + (d : ℂ) • β) (1 : G)) :
    (a - c) * p + (b - d) * q = 0 := by
  have hdeg' : (a : ℂ) * (p : ℂ) + (b : ℂ) * (q : ℂ) =
      (c : ℂ) * (p : ℂ) + (d : ℂ) * (q : ℂ) := by
    simpa [hα1, hβ1] using hdeg
  have hcast : ((((a - c) * p + (b - d) * q : ℤ)) : ℂ) = 0 := by
    push_cast
    linear_combination hdeg'
  exact Int.cast_eq_zero.mp hcast

/-- Degree computation in the case `γ = β`, `ζ = α`, given `α 1 = p`, `β 1 = q`. -/
private lemma deg_eq_case2 {G : Type*} [Group G] [Finite G] [Fintype G]
    [Invertible (Nat.card G : ℂ)]
    {a b c d p q : ℤ} {α β : ClassFunction G ℂ}
    (hα1 : α 1 = (p : ℂ)) (hβ1 : β 1 = (q : ℂ))
    (hdeg : ((a : ℂ) • α + (b : ℂ) • β) (1 : G) =
        ((c : ℂ) • β + (d : ℂ) • α) (1 : G)) :
    (a - d) * p + (b - c) * q = 0 := by
  have hdeg' : (a : ℂ) * (p : ℂ) + (b : ℂ) * (q : ℂ) =
      (c : ℂ) * (q : ℂ) + (d : ℂ) * (p : ℂ) := by
    simpa [hα1, hβ1] using hdeg
  have hcast : ((((a - d) * p + (b - c) * q : ℤ)) : ℂ) = 0 := by
    push_cast
    linear_combination hdeg'
  exact Int.cast_eq_zero.mp hcast

/-- Integer arithmetic contradiction for the case `γ = α`, `ζ = β`. -/
private lemma arith_case1 {a b c d p q : ℤ} (ha : a = 1 ∨ a = -1)
    (hb : b = 1 ∨ b = -1) (hc : c = 1 ∨ c = -1) (hd : d = 1 ∨ d = -1)
    (hp : 0 < p) (hq : 0 < q) (horth : a * c + b * d = 0)
    (hdeg : (a - c) * p + (b - d) * q = 0) : False := by
  rcases ha with rfl | rfl <;> rcases hb with rfl | rfl <;>
    rcases hc with rfl | rfl <;> rcases hd with rfl | rfl <;>
    omega

/-- Integer arithmetic contradiction for the case `γ = β`, `ζ = α`. -/
private lemma arith_case2 {a b c d p q : ℤ} (ha : a = 1 ∨ a = -1)
    (hb : b = 1 ∨ b = -1) (hc : c = 1 ∨ c = -1) (hd : d = 1 ∨ d = -1)
    (hp : 0 < p) (hq : 0 < q) (horth : a * d + b * c = 0)
    (hdeg : (a - d) * p + (b - c) * q = 0) : False := by
  rcases ha with rfl | rfl <;> rcases hb with rfl | rfl <;>
    rcases hc with rfl | rfl <;> rcases hd with rfl | rfl <;>
    omega

theorem doubleCoincidence {G : Type*} [Group G] [Finite G] [Fintype G]
    [Invertible (Nat.card G : ℂ)]
    {a b c d : ℤ} (ha : a = 1 ∨ a = -1) (hb : b = 1 ∨ b = -1)
    (hc : c = 1 ∨ c = -1) (hd : d = 1 ∨ d = -1)
    {α β γ ζ : OddOrder.RepresentationTheory.ClassFunction G ℂ}
    (hα : OddOrder.RepresentationTheory.IsIrreducibleCharacter α)
    (hβ : OddOrder.RepresentationTheory.IsIrreducibleCharacter β)
    (hγ : OddOrder.RepresentationTheory.IsIrreducibleCharacter γ)
    (hζ : OddOrder.RepresentationTheory.IsIrreducibleCharacter ζ)
    (hαβ : α ≠ β) (hγζ : γ ≠ ζ)
    (hshare : (α = γ ∧ β = ζ) ∨ (α = ζ ∧ β = γ))
    (horth : OddOrder.RepresentationTheory.ClassFunction.inner
        ((a : ℂ) • α + (b : ℂ) • β) ((c : ℂ) • γ + (d : ℂ) • ζ) = 0)
    (hdeg : ((a : ℂ) • α + (b : ℂ) • β) (1 : G) =
        ((c : ℂ) • γ + (d : ℂ) • ζ) (1 : G)) : False := by
  obtain ⟨p0, hp0pos, hp0eq, _⟩ := hα.exists_natDegree_charValue_one_dvd_card (G := G)
  obtain ⟨q0, hq0pos, hq0eq, _⟩ := hβ.exists_natDegree_charValue_one_dvd_card (G := G)
  have hp : 0 < (p0 : ℤ) := by exact_mod_cast hp0pos
  have hq : 0 < (q0 : ℤ) := by exact_mod_cast hq0pos
  have hα1 : α 1 = ((p0 : ℤ) : ℂ) := by push_cast; exact hp0eq
  have hβ1 : β 1 = ((q0 : ℤ) : ℂ) := by push_cast; exact hq0eq
  rcases hshare with ⟨h1, h2⟩ | ⟨h1, h2⟩
  · rw [← h1, ← h2] at horth hdeg
    exact arith_case1 ha hb hc hd hp hq
      (inner_eq_case1 hα hβ hαβ horth) (deg_eq_case1 hα1 hβ1 hdeg)
  · rw [← h1, ← h2] at horth hdeg
    exact arith_case2 ha hb hc hd hp hq
      (inner_eq_case2 hα hβ hαβ horth) (deg_eq_case2 hα1 hβ1 hdeg)

end Work.BG
