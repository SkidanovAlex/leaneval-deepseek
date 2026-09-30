import Mathlib
import Submission.Work.RiemannRoch.Duality.Basic
import Submission.Work.RiemannRoch.Duality.deg_le_of_mem_WD
import Submission.Work.RiemannRoch.RR.mem_WD_sup
import Submission.Work.CurveBasics.Divisor.deg_eq_zero_iff
import Submission.Work.CurveBasics.Divisor.deg_nonneg

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.


set_option autoImplicit false
set_option maxHeartbeats 1600000
set_option linter.style.haveILetI false

namespace Work.RiemannRoch.Duality

open scoped Classical

/-- **Degree bound for a nonzero Weil differential** (a self-contained proof of
`deg_le_of_mem_WD`).  If `0 ≠ ω ∈ WD C D` then `deg D ≤ 2g - 2`.

Proof: fix a place `P` and put `Δ = m·P`.  Multiplication by an element of `L Δ` is injective
on `ω` and sends `WD C D` into `WD C (D + div f) ≤ WD C (D - Δ)`, so
`l Δ ≤ i (D - Δ)`.  For `m` large, `deg (D - Δ) < 0`, hence `L (D - Δ) = 0` and
Riemann–Roch evaluates `i (D - Δ) = -deg D + m·deg P - 1 + g`.  Riemann's inequality gives
`l Δ ≥ m·deg P + 1 - g`; subtracting yields the claim. -/
theorem deg_le_of_mem_WD_aux {k : Type*} [Field k] (C : Work.CurveBasics.Curve k)
    {ω : Module.Dual k (Work.RiemannRoch.Curve.Adeles C)} (hω0 : ω ≠ 0)
    {D : C.Div} (hD : ω ∈ Work.RiemannRoch.Curve.WD C D) :
    C.deg D ≤ 2 * (Work.RiemannRoch.Curve.genus C : ℤ) - 2 := by
  classical
  obtain ⟨P⟩ := Work.RiemannRoch.Curve.nonempty_place C
  have hP1 : (1 : ℤ) ≤ (P.degree : ℤ) := by
    have h : (1 : ℕ) ≤ P.degree :=
      Nat.one_le_iff_ne_zero.mpr (Nat.pos_iff_ne_zero.mp
        (Work.CurveBasics.Place.residueDegree_pos P))
    exact_mod_cast h
  obtain ⟨m, hm1, hm2⟩ : ∃ m : ℤ, 1 ≤ m ∧ C.deg D < m := by
    refine ⟨((C.deg D).natAbs : ℤ) + 1, by omega, ?_⟩
    have h : C.deg D ≤ ((C.deg D).natAbs : ℤ) := Int.le_natAbs
    linarith
  have hmul : m ≤ m * (P.degree : ℤ) := by nlinarith [hm1, hP1]
  have hmD : C.deg D < m * (P.degree : ℤ) := lt_of_lt_of_le hm2 hmul
  set Δ : C.Div := m • Work.CurveBasics.Curve.Div.place P with hΔ
  have hdegΔ : C.deg Δ = m * (P.degree : ℤ) := by
    rw [hΔ, Work.CurveBasics.Curve.deg_zsmul, Work.CurveBasics.Curve.deg_place, smul_eq_mul]
  have hneg : C.deg (D - Δ) < 0 := by
    rw [Work.CurveBasics.Curve.deg_sub, hdegΔ]; linarith
  have hL : C.L (D - Δ) = ⊥ :=
    Work.RiemannRoch.RR.L_eq_bot_of_deg_neg C hneg
  have hl0 : C.l (D - Δ) = 0 := by
    rw [Work.CurveBasics.Curve.l, hL]
    exact finrank_bot k C.functionField
  -- multiplication by `f ∈ L Δ` maps into `WD C (D - Δ)`
  have hmem : ∀ f : ↥(C.L Δ),
      (Work.RiemannRoch.Curve.smulWLin C ω) ((f : ↥(C.L Δ)) : C.functionField) ∈
        Work.RiemannRoch.Curve.WD C (D - Δ) := by
    intro f
    rw [Work.RiemannRoch.Curve.smulWLin_apply]
    rcases eq_or_ne ((f : ↥(C.L Δ)) : C.functionField) 0 with hf | hf
    · rw [hf, Work.RiemannRoch.Curve.smulW_zero_left]
      exact Submodule.zero_mem _
    · refine Work.RiemannRoch.Curve.WD_anti C ?_
        (Work.RiemannRoch.RR.smulW_mem_WD C hf hD)
      rw [Finsupp.le_def]
      intro Q
      have hfL : -Δ Q ≤ AlgebraicGeometry.Scheme.ord ((f : ↥(C.L Δ)) : C.functionField) Q.point := by
        have h1 : (C.div ((f : ↥(C.L Δ)) : C.functionField) + Δ).IsEffective :=
          ((C.mem_L_iff).mp f.2).resolve_left hf
        exact (C.isEffective_div_add_iff).mp h1 Q
      simp only [Finsupp.sub_apply, Finsupp.add_apply, Work.CurveBasics.Curve.div_apply]
      linarith
  let ψA : ↥(C.L Δ) →ₗ[k] Work.RiemannRoch.Curve.WeilDifferential C :=
    (Work.RiemannRoch.Curve.smulWLin C ω).comp (C.L Δ).subtype
  have hinjA : Function.Injective ψA := by
    intro f g hfg
    have hdiff : Work.RiemannRoch.Curve.smulW C ((f - g : ↥(C.L Δ)) : C.functionField) ω = 0 := by
      have h1 : ψA (f - g) = 0 := by rw [map_sub, hfg, sub_self]
      simpa [ψA, LinearMap.comp_apply, Work.RiemannRoch.Curve.smulWLin_apply] using h1
    by_contra hne
    have hne0 : (f - g : ↥(C.L Δ)) ≠ 0 := fun h => hne (sub_eq_zero.mp h)
    have hne' : ((f - g : ↥(C.L Δ)) : C.functionField) ≠ 0 :=
      fun h => hne0 (Subtype.ext h)
    exact hω0 ((Work.RiemannRoch.RR.smulW_eq_zero_iff C hne' ω).mp hdiff)
  have hle : (C.l Δ : ℤ) ≤ (Work.RiemannRoch.Curve.i C (D - Δ) : ℤ) := by
    haveI : FiniteDimensional k ↥(Work.RiemannRoch.Curve.WD C (D - Δ)) :=
      (Work.RiemannRoch.Curve.WDequiv C (D - Δ)).finiteDimensional
    have hfin1 : Module.finrank k ↥(C.L Δ) = Module.finrank k ↥(LinearMap.range ψA) :=
      (LinearEquiv.ofInjective ψA hinjA).finrank_eq
    have hrange : LinearMap.range ψA ≤ Work.RiemannRoch.Curve.WD C (D - Δ) := by
      rintro x ⟨f, rfl⟩
      exact hmem f
    have hfin2 : Module.finrank k ↥(LinearMap.range ψA)
        ≤ Module.finrank k ↥(Work.RiemannRoch.Curve.WD C (D - Δ)) :=
      Submodule.finrank_mono hrange
    rw [finrank_WD] at hfin2
    rw [← hfin1] at hfin2
    exact_mod_cast hfin2
  have hriem := Work.RiemannRoch.Curve.riemann_inequality C Δ
  rw [hdegΔ] at hriem
  have hRR := Work.RiemannRoch.Curve.riemannRoch C (D - Δ)
  rw [Work.CurveBasics.Curve.deg_sub, hdegΔ, hl0] at hRR
  push_cast at hRR
  simp only [zero_sub] at hRR
  have hi : (Work.RiemannRoch.Curve.i C (D - Δ) : ℤ)
      = -C.deg D + m * (P.degree : ℤ) - 1 + (Work.RiemannRoch.Curve.genus C : ℤ) := by
    linarith
  rw [hi] at hle
  linarith

/-- **Every nonzero Weil differential has a divisor.**  This is Serre, *Algebraic Groups and
Class Fields*, II §8: the set `{D | ω ∈ WD D}` is directed (it is closed under `⊔`) and bounded
in degree by `2g - 2`; a divisor of maximal degree is therefore the largest element. -/
theorem exists_isDivW {k : Type*} [Field k] (C : Work.CurveBasics.Curve k)
    {ω : Module.Dual k (Work.RiemannRoch.Curve.Adeles C)}
    (hω : ω ∈ Work.RiemannRoch.Curve.Omega C) (hω0 : ω ≠ 0) :
    ∃ W : C.Div, Work.RiemannRoch.Curve.IsDivW C ω W := by
  classical
  obtain ⟨D₀, hD₀⟩ := Work.RiemannRoch.Curve.mem_Omega_iff.mp hω
  set B : ℤ := 2 * (Work.RiemannRoch.Curve.genus C : ℤ) - 2 with hB
  have hbdd : ∀ D : C.Div, ω ∈ Work.RiemannRoch.Curve.WD C D → C.deg D ≤ B :=
    fun D hD => deg_le_of_mem_WD_aux C hω0 hD
  have htoNat : ∀ D : C.Div, ω ∈ Work.RiemannRoch.Curve.WD C D →
      ((B - C.deg D).toNat : ℤ) = B - C.deg D :=
    fun D hD => Int.toNat_of_nonneg (by linarith [hbdd D hD])
  have hex : ∃ n : ℕ, ∃ D : C.Div,
      ω ∈ Work.RiemannRoch.Curve.WD C D ∧ (B - C.deg D).toNat = n :=
    ⟨_, D₀, hD₀, rfl⟩
  obtain ⟨W, hW, hWn⟩ := Nat.find_spec hex
  have hmax : ∀ D : C.Div, ω ∈ Work.RiemannRoch.Curve.WD C D → D ≤ W := by
    intro D hD
    have hsup : ω ∈ Work.RiemannRoch.Curve.WD C (D ⊔ W) :=
      Work.RiemannRoch.RR.mem_WD_sup C hD hW
    have hle : Nat.find hex ≤ (B - C.deg (D ⊔ W)).toNat :=
      Nat.find_min' hex ⟨D ⊔ W, hsup, rfl⟩
    have hle' : (B - C.deg W).toNat ≤ (B - C.deg (D ⊔ W)).toNat := by
      rw [hWn]; exact hle
    have h1 : ((B - C.deg W).toNat : ℤ) ≤ ((B - C.deg (D ⊔ W)).toNat : ℤ) := by
      exact_mod_cast hle'
    rw [htoNat W hW, htoNat (D ⊔ W) hsup] at h1
    have hEff : (D ⊔ W - W).IsEffective := by
      intro Q
      rw [Finsupp.sub_apply, Finsupp.sup_apply]
      exact sub_nonneg.mpr (le_max_right _ _)
    have hge : C.deg W ≤ C.deg (D ⊔ W) := by
      have h := Work.CurveBasics.Divisor.deg_nonneg hEff
      rw [Work.CurveBasics.Curve.deg_sub] at h
      linarith
    have hzero : D ⊔ W - W = 0 := by
      refine (Work.CurveBasics.Divisor.deg_eq_zero_iff hEff).mp ?_
      rw [Work.CurveBasics.Curve.deg_sub]
      linarith
    have hsup_eq : D ⊔ W = W := sub_eq_zero.mp hzero
    rw [Finsupp.le_def]
    intro Q
    have h2 : D Q ≤ (D ⊔ W) Q := by
      rw [Finsupp.sup_apply]; exact le_max_left _ _
    rwa [hsup_eq] at h2
  exact ⟨W, hW, hmax⟩

end Work.RiemannRoch.Duality
