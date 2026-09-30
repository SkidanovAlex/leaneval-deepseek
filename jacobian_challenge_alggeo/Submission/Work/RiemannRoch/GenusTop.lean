/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Area RR: `A_K = A(E₀) + K` — strong approximation from Riemann's inequality

The image of `A(E)` in `H1 C 0` has dimension `deg E - l E + 1`, which is bounded by the Riemann
constant; it is therefore maximal for some `E₀ ≥ 0`.  Adding the pole divisor of an adèle
enlarges that image (the adèle itself becomes bounded by `E₀ ⊔ poleDiv a`), so maximality forces
`A(E₀) + K = A_K`.  This is RR2.e of the design; it gives the finiteness of the genus without
any appeal to strong approximation.
-/
import Submission.Work.RiemannRoch.Genus
import Submission.Work.RiemannRoch.RiemannBound

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.


set_option autoImplicit false
set_option linter.style.haveILetI false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 800000

open CategoryTheory Limits AlgebraicGeometry
open scoped Classical

universe u

namespace Work.RiemannRoch

open Work.CurveBasics

namespace Curve

noncomputable section

variable {k : Type u} [Field k]

/-- The predicate saying that `n` is at most the dimension of the image of `A(E)` in `H1 C 0`
for some effective `E`. -/
def Attained (C : Curve k) (n : ℕ) : Prop :=
  ∃ E : C.Div, 0 ≤ E ∧ n ≤ Module.finrank k ↥(SEmap C E)

/-- **Strong approximation for adèles** (Serre II §5, Stichtenoth 1.4.14): there is a divisor
`E₀` with `A(E₀) + K = A_K`. -/
theorem exists_Asub_sup_diagK_eq_top (C : Curve k) : ∃ E : C.Div, Asub C E ⊔ diagK C = ⊤ := by
  obtain ⟨γ, hγ⟩ := exists_riemann_bound C
  have hP0 : Attained C 0 := ⟨0, le_refl 0, Nat.zero_le _⟩
  obtain ⟨E₀, hE₀, hE₀low⟩ : Attained C (Nat.findGreatest (Attained C) ((γ + 1).toNat)) :=
    Nat.findGreatest_spec (Nat.zero_le _) hP0
  have hmax : ∀ E : C.Div, 0 ≤ E →
      Module.finrank k ↥(SEmap C E) ≤ Nat.findGreatest (Attained C) ((γ + 1).toNat) := by
    intro E hE
    exact Nat.le_findGreatest (finrank_SEmap_le C hγ hE) ⟨E, hE, le_refl _⟩
  have hM : Module.finrank k ↥(SEmap C E₀) = Nat.findGreatest (Attained C) ((γ + 1).toNat) :=
    le_antisymm (hmax E₀ hE₀) hE₀low
  refine ⟨E₀, top_unique fun a _ => ?_⟩
  set E' : C.Div := E₀ ⊔ poleDiv C a with hE'def
  have hE' : 0 ≤ E' := le_trans hE₀ le_sup_left
  have hfin : Module.finrank k ↥(SEmap C E') ≤ Module.finrank k ↥(SEmap C E₀) := by
    rw [hM]; exact hmax E' hE'
  have heq : SEmap C E₀ = SEmap C E' := by
    haveI : FiniteDimensional k ↥(SEmap C E') := finite_SEmap C hE'
    exact Submodule.eq_of_le_of_finrank_le (SEmap_mono C le_sup_left) hfin
  have ha : a ∈ Asub C E' := Asub_mono C le_sup_right (mem_A_poleDiv C a)
  have hmk : Submodule.mkQ (Asub C 0 ⊔ diagK C) a ∈ SEmap C E₀ := by
    rw [heq]
    exact Submodule.mem_map_of_mem ha
  obtain ⟨b, hb, hbmk⟩ := mem_SEmap.mp hmk
  have hdiff : a - b ∈ Asub C 0 ⊔ diagK C := by
    have h1 : Submodule.mkQ (Asub C 0 ⊔ diagK C) a = Submodule.mkQ (Asub C 0 ⊔ diagK C) b := by
      rw [hbmk]
    have h2 : Submodule.mkQ (Asub C 0 ⊔ diagK C) (a - b) = 0 := by
      rw [map_sub, h1, sub_self]
    exact (Submodule.Quotient.mk_eq_zero (Asub C 0 ⊔ diagK C)).mp h2
  have hb' : b ∈ Asub C E₀ ⊔ diagK C :=
    (le_sup_left : Asub C E₀ ≤ Asub C E₀ ⊔ diagK C) hb
  have hle' : Asub C 0 ⊔ diagK C ≤ Asub C E₀ ⊔ diagK C :=
    sup_le_sup_right (Asub_mono C hE₀) (diagK C)
  have hd' : a - b ∈ Asub C E₀ ⊔ diagK C := hle' hdiff
  have hsum : b + (a - b) ∈ Asub C E₀ ⊔ diagK C := add_mem hb' hd'
  simpa using hsum

/-- The genus is finite: `H^1(C, O_C)` is finite dimensional (Serre II §5, unconditionally). -/
theorem hasFiniteGenus (C : Curve k) : HasFiniteGenus C := by
  obtain ⟨E₀, hE₀⟩ := exists_Asub_sup_diagK_eq_top C
  have hE₀' : (0 : C.Div) ≤ E₀ ⊔ 0 := (le_sup_right : (0 : C.Div) ≤ E₀ ⊔ 0)
  have htop : Asub C (E₀ ⊔ 0) ⊔ diagK C = ⊤ := by
    rw [eq_top_iff, ← hE₀]
    exact sup_le_sup_right (Asub_mono C le_sup_left) (diagK C)
  have hfinR : Module.Finite k (relQuot (Asub C 0 ⊔ diagK C) ⊤) := by
    rw [← htop]
    exact (Work.RiemannRoch.RR.finrank_sup_diagK_quot C (D := 0) (E := E₀ ⊔ 0) hE₀').1
  have e1 : relQuot (Asub C 0 ⊔ diagK C) (⊤ : Submodule k (Adeles C)) ≃ₗ[k]
      ↥(⊤ : Submodule k (↥(Adeles C) ⧸ (Asub C 0 ⊔ diagK C))) := by
    have h := relQuotEquivMap (Asub C 0 ⊔ diagK C) (⊤ : Submodule k (Adeles C))
    rw [Submodule.map_top, Submodule.range_mkQ] at h
    exact h
  show Module.Finite k (↥(Adeles C) ⧸ (Asub C 0 ⊔ diagK C))
  exact (e1.trans Submodule.topEquiv).finiteDimensional

end

end Curve

end Work.RiemannRoch
