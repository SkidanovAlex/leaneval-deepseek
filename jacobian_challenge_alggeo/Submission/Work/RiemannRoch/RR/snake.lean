import Mathlib
import Submission.Work.RiemannRoch.Quotients
import Submission.Work.RiemannRoch.Aquot.localIdeal_quotient_finrank
import Submission.Work.RiemannRoch.Aquot.rank_quotient_tower

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.


set_option autoImplicit false
set_option linter.style.haveILetI false
set_option linter.unusedSectionVars false

open CategoryTheory Limits AlgebraicGeometry
open scoped Classical

universe u

namespace Work.RiemannRoch

open Work.CurveBasics

namespace Curve

noncomputable section

variable {k : Type u} [Field k]

/-- A pointwise description of the lattice `A(D + m·Q)`. -/
private lemma mem_A_add_single_iff_fa {C : Curve k} {D : C.Div} {Q : C.Place} {m : ℤ}
    {x : C.Place → C.functionField} :
    x ∈ A C (D + Finsupp.single Q m) ↔
      x Q ∈ localIdeal C Q (D Q + m) ∧
        (∀ P : C.Place, P ≠ Q → x P ∈ localIdeal C P (D P)) := by
  rw [mem_A]
  constructor
  · intro h
    refine ⟨?_, ?_⟩
    · have := h Q
      rwa [Finsupp.add_apply, Finsupp.single_eq_same] at this
    · intro P hP
      have := h P
      rwa [Finsupp.add_apply, Finsupp.single_eq_of_ne hP, add_zero] at this
  · rintro ⟨hQ, hP⟩ P
    rw [Finsupp.add_apply]
    by_cases h : P = Q
    · subst h
      rw [Finsupp.single_eq_same]
      exact hQ
    · rw [Finsupp.single_eq_of_ne h, add_zero]
      exact hP P h

/-- **The bridge.**  Only the `Q`-th coordinate distinguishes `A(D + n·Q)` from `A(D)`, so
`A(D + n·Q)/A(D)` is the local ideal quotient `I_Q(D Q + n)/I_Q(D Q)`. -/
def aquotEquivLocalIdeal {k : Type u} [Field k] (C : Curve k)
    (D : C.Div) (Q : C.Place) (n : ℕ) :
    Aquot C D (D + Finsupp.single Q (n : ℤ)) ≃ₗ[k]
      (↥(localIdeal C Q (D Q + (n : ℤ))) ⧸
        (localIdeal C Q (D Q)).comap (localIdeal C Q (D Q + (n : ℤ))).subtype) := by
  classical
  have hmem : ∀ x : ↥(A C (D + Finsupp.single Q (n : ℤ))),
      x.1 Q ∈ localIdeal C Q (D Q + (n : ℤ)) :=
    fun x => (mem_A_add_single_iff_fa.mp x.2).1
  let proj : ↥(A C (D + Finsupp.single Q (n : ℤ))) →ₗ[k]
      ↥(localIdeal C Q (D Q + (n : ℤ))) :=
    ((LinearMap.proj (R := k) Q).comp
      (A C (D + Finsupp.single Q (n : ℤ))).subtype).codRestrict _ hmem
  let Φ : ↥(A C (D + Finsupp.single Q (n : ℤ))) →ₗ[k]
      (↥(localIdeal C Q (D Q + (n : ℤ))) ⧸
        (localIdeal C Q (D Q)).comap (localIdeal C Q (D Q + (n : ℤ))).subtype) :=
    (Submodule.mkQ ((localIdeal C Q (D Q)).comap
      (localIdeal C Q (D Q + (n : ℤ))).subtype)).comp proj
  have hproj : ∀ x : ↥(A C (D + Finsupp.single Q (n : ℤ))),
      ((proj x : ↥(localIdeal C Q (D Q + (n : ℤ)))) : C.functionField) = x.1 Q := fun x => rfl
  have hΦ : ∀ x, Φ x = Submodule.Quotient.mk (proj x) := fun x => rfl
  have hker : Φ.ker = (A C D).comap (A C (D + Finsupp.single Q (n : ℤ))).subtype := by
    ext x
    rw [LinearMap.mem_ker, hΦ, Submodule.Quotient.mk_eq_zero, Submodule.mem_comap,
      Submodule.mem_comap]
    constructor
    · intro hx
      have hxQ : x.1 Q ∈ localIdeal C Q (D Q) := by
        rw [← hproj x]
        exact (Submodule.mem_comap.mp hx)
      rw [mem_A]
      intro P
      by_cases hP : P = Q
      · subst hP; exact hxQ
      · exact (mem_A_add_single_iff_fa.mp x.2).2 P hP
    · intro hxD
      show x.1 Q ∈ localIdeal C Q (D Q)
      exact (mem_A.mp hxD) Q
  have hrange : Φ.range = ⊤ := by
    rw [Submodule.eq_top_iff']
    intro y
    refine Submodule.Quotient.induction_on _ y ?_
    intro w
    let x : C.Place → C.functionField := fun P => if P = Q then (w.1 : C.functionField) else 0
    have hx : x ∈ A C (D + Finsupp.single Q (n : ℤ)) := by
      rw [mem_A_add_single_iff_fa]
      refine ⟨?_, ?_⟩
      · rw [show x Q = (w.1 : C.functionField) by simp [x]]
        exact w.2
      · intro P hP
        rw [show x P = 0 by simp [x, hP]]
        exact Submodule.zero_mem _
    refine LinearMap.mem_range.mpr ⟨⟨x, hx⟩, ?_⟩
    have h1 : proj ⟨x, hx⟩ = w := by
      apply Subtype.ext
      rw [hproj]
      simp [x]
    rw [hΦ, h1]
  exact (Submodule.quotEquivOfEq Φ.ker ((A C D).comap
      (A C (D + Finsupp.single Q (n : ℤ))).subtype) hker).symm.trans
    ((LinearMap.quotKerEquivRange Φ).trans (LinearEquiv.ofTop Φ.range hrange))
end

end Curve

end Work.RiemannRoch

namespace Work.RiemannRoch.RR

open Work.CurveBasics
open Work.RiemannRoch.Curve

section

variable {k : Type u} [Field k]

/-! ## Finiteness of the quotients `A(E)/A(D)` -/

/-- Finiteness of the one-place quotient `A(D + n·[Q]) / A(D)`. -/
theorem finiteDimensional_Aquot_single (C : Curve k) (D : C.Div) (Q : C.Place) (n : ℕ) :
    FiniteDimensional k (Aquot C D (D + Finsupp.single Q (n : ℤ))) := by
  haveI h : Module.Finite k (↥(localIdeal C Q (D Q + (n : ℤ))) ⧸
      (localIdeal C Q (D Q)).comap (localIdeal C Q (D Q + (n : ℤ))).subtype) :=
    (Work.RiemannRoch.Aquot.localIdeal_quotient_finrank C Q (m := D Q)
      (n := D Q + (n : ℤ)) (by omega)).1
  exact Module.Finite.equiv (aquotEquivLocalIdeal C D Q n).symm

/-- Variant of `finiteDimensional_Aquot_single` where the target divisor is only given up to
equality. -/
theorem finiteDimensional_Aquot_single' (C : Curve k) (D : C.Div) (Q : C.Place) (n : ℕ)
    (D' : C.Div) (hD' : D' = D + Finsupp.single Q (n : ℤ)) :
    FiniteDimensional k (Aquot C D D') := by
  subst hD'
  exact finiteDimensional_Aquot_single C D Q n

/-- **`A(E)/A(D)` is finite dimensional over `k` for `D ≤ E`.** -/
theorem finiteDimensional_Aquot (C : Curve k) {D E : C.Div} (h : D ≤ E) :
    FiniteDimensional k (Aquot C D E) := by
  classical
  have hF : ∀ Q : C.Place, 0 ≤ (E - D) Q := by
    intro Q
    have h1 : D Q ≤ E Q := Finsupp.le_def.mp h Q
    simp only [Finsupp.sub_apply]
    linarith
  have key : ∀ F : C.Div, (∀ Q : C.Place, 0 ≤ F Q) → ∀ D : C.Div,
      FiniteDimensional k (Aquot C D (D + F)) := by
    intro F
    refine Finsupp.induction (motive := fun F => (∀ Q : C.Place, 0 ≤ F Q) →
      ∀ D : C.Div, FiniteDimensional k (Aquot C D (D + F))) F ?_ ?_
    · intro _ D
      haveI : Subsingleton (Aquot C D (D + 0)) := by
        rw [Submodule.Quotient.subsingleton_iff, Submodule.eq_top_iff']
        intro x
        rw [Submodule.mem_comap]
        exact A_mono C (Finsupp.le_def.mpr (fun Q => by simp)) x.2
      exact Module.Finite.of_surjective (0 : k →ₗ[k] (Aquot C D (D + 0)))
        (fun x => ⟨0, by rw [LinearMap.zero_apply]; exact Subsingleton.elim _ _⟩)
    · intro a b f ha hb ih hF D
      have hfa : f a = 0 := Finsupp.notMem_support_iff.mp ha
      have hb0 : 0 ≤ b := by
        have h1 := hF a
        rw [Finsupp.add_apply, Finsupp.single_eq_same, hfa, add_zero] at h1
        exact h1
      have hf0 : ∀ Q : C.Place, 0 ≤ f Q := by
        intro Q
        rcases eq_or_ne Q a with hQ | hQ
        · subst hQ; rw [hfa]
        · have h1 := hF Q
          rw [Finsupp.add_apply, Finsupp.single_eq_of_ne hQ, zero_add] at h1
          exact h1
      have hle1 : D ≤ D + f := Finsupp.le_def.mpr (fun Q => by
        rw [Finsupp.add_apply]; exact le_add_of_nonneg_right (hf0 Q))
      have hle2 : D + f ≤ D + (Finsupp.single a b + f) := Finsupp.le_def.mpr (fun Q => by
        have hs : 0 ≤ Finsupp.single a b Q := by
          rw [Finsupp.single_apply]
          split_ifs with hh
          · exact hb0
          · exact le_refl 0
        simp only [Finsupp.add_apply]
        linarith)
      have hrank := Work.RiemannRoch.Aquot.rank_quotient_tower (k := k)
        (S := A C D) (T := A C (D + f)) (A := A C (D + (Finsupp.single a b + f)))
        (A_mono C hle1) (A_mono C hle2)
      have hstep : FiniteDimensional k (Aquot C (D + f) (D + (Finsupp.single a b + f))) :=
        finiteDimensional_Aquot_single' C (D + f) a b.toNat (D + (Finsupp.single a b + f))
          (by rw [Int.toNat_of_nonneg hb0]; abel)
      have hrec : FiniteDimensional k (Aquot C D (D + f)) := ih hf0 D
      refine Module.rank_lt_aleph0_iff.mp ?_
      rw [hrank]
      exact Cardinal.add_lt_aleph0 (Module.rank_lt_aleph0_iff.mpr hstep)
        (Module.rank_lt_aleph0_iff.mpr hrec)
  have hDE : D + (E - D) = E := add_sub_cancel _ _
  exact hDE ▸ key (E - D) hF D

/-! ## The short exact sequence `0 → L(E)/L(D) → A(E)/A(D) → (A(E)+K)/(A(D)+K) → 0` -/

/-- **The dimension count behind Riemann–Roch.**  For submodules `P ≤ Q` and any `Kk` of a
`k`-module `V` with `Q/P` finite dimensional,

`dim Q/P = dim (Q ∩ Kk)/(P ∩ Kk) + dim (Q + Kk)/(P + Kk)`.

This is the dimension count for the short exact sequence
`0 → (Q ∩ Kk)/(P ∩ Kk) → Q/P → (Q + Kk)/(P + Kk) → 0`. -/
theorem finrank_snake_aux {k : Type u} [Field k] {V : Type u} [AddCommGroup V] [Module k V]
    (P Q Kk : Submodule k V) (hPQ : P ≤ Q)
    [FiniteDimensional k (↥Q ⧸ P.comap Q.subtype)] :
    Module.finrank k (↥Q ⧸ P.comap Q.subtype) =
      Module.finrank k (↥(Q ⊓ Kk) ⧸ (P ⊓ Kk).comap (Q ⊓ Kk).subtype) +
      Module.finrank k (↥(Q ⊔ Kk) ⧸ (P ⊔ Kk).comap (Q ⊔ Kk).subtype) := by
  have hMN : P.comap Q.subtype ≤ (P ⊔ Kk).comap Q.subtype := Submodule.comap_mono le_sup_left
  -- the `K`-side: `Q/((P+K) ∩ Q) ≃ (Q+K)/(P+K)`
  have hK : Module.finrank k (↥Q ⧸ (P ⊔ Kk).comap Q.subtype) =
      Module.finrank k (↥(Q ⊔ Kk) ⧸ (P ⊔ Kk).comap (Q ⊔ Kk).subtype) := by
    let ψ : ↥Q →ₗ[k] (↥(Q ⊔ Kk) ⧸ (P ⊔ Kk).comap (Q ⊔ Kk).subtype) :=
      (Submodule.mkQ _).comp (Submodule.inclusion le_sup_left)
    have hker : ψ.ker = (P ⊔ Kk).comap Q.subtype := by
      ext x
      rw [LinearMap.mem_ker, Submodule.mem_comap]
      show ((Submodule.mkQ _) (Submodule.inclusion le_sup_left x) = 0) ↔
        (x : V) ∈ P ⊔ Kk
      rw [Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero, Submodule.mem_comap]
      rfl
    have hsurj : Function.Surjective ψ := by
      intro z
      obtain ⟨y, rfl⟩ := Submodule.mkQ_surjective _ z
      obtain ⟨q, hq, k, hk, hqk⟩ := Submodule.mem_sup.mp y.2
      refine ⟨⟨q, hq⟩, ?_⟩
      show (Submodule.mkQ _) (Submodule.inclusion le_sup_left ⟨q, hq⟩) = (Submodule.mkQ _) y
      rw [Submodule.mkQ_apply, Submodule.mkQ_apply, Submodule.Quotient.eq]
      refine Submodule.mem_comap.mpr ?_
      change (q : V) - (y : V) ∈ P ⊔ Kk
      have h1 : (q : V) - (y : V) = -k := by rw [← hqk]; abel
      rw [h1]
      exact Submodule.neg_mem _ (Submodule.mem_sup_right hk)
    exact (((Submodule.quotEquivOfEq ψ.ker ((P ⊔ Kk).comap Q.subtype) hker).symm).trans
      (ψ.quotKerEquivOfSurjective hsurj)).finrank_eq
  -- the `L`-side: `(Q ∩ K)/(P ∩ K)` is the image of `Q ∩ K` in `Q/P`
  have hL : Module.finrank k (↥(Q ⊓ Kk) ⧸ (P ⊓ Kk).comap (Q ⊓ Kk).subtype) =
      Module.finrank k ↥(((P ⊔ Kk).comap Q.subtype).map (P.comap Q.subtype).mkQ) := by
    let ψ : ↥(Q ⊓ Kk) →ₗ[k] (↥Q ⧸ P.comap Q.subtype) :=
      (Submodule.mkQ _).comp (Submodule.inclusion inf_le_left)
    have hker : ψ.ker = (P ⊓ Kk).comap (Q ⊓ Kk).subtype := by
      ext x
      rw [LinearMap.mem_ker, Submodule.mem_comap]
      constructor
      · intro h
        have h1 : (Submodule.mkQ (P.comap Q.subtype))
            (Submodule.inclusion inf_le_left x) = 0 := h
        rw [Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero, Submodule.mem_comap] at h1
        exact ⟨h1, x.2.2⟩
      · intro h
        show (Submodule.mkQ (P.comap Q.subtype)) (Submodule.inclusion inf_le_left x) = 0
        rw [Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero, Submodule.mem_comap]
        exact h.1
    have hrange : ψ.range = ((P ⊔ Kk).comap Q.subtype).map (P.comap Q.subtype).mkQ := by
      ext z
      constructor
      · rintro ⟨x, rfl⟩
        rw [Submodule.mem_map]
        refine ⟨Submodule.inclusion inf_le_left x, ?_, rfl⟩
        rw [Submodule.mem_comap]
        exact Submodule.mem_sup_right x.2.2
      · intro hz
        rw [Submodule.mem_map] at hz
        obtain ⟨y, hy, hyz⟩ := hz
        rw [Submodule.mem_comap] at hy
        obtain ⟨p, hp, k', hk', hpk⟩ := Submodule.mem_sup.mp hy
        have hpk' : p + k' = (y : V) := hpk
        have hkQ : k' ∈ Q := by
          have h1 : k' = (y : V) - p := by rw [← hpk']; abel
          rw [h1]
          exact Submodule.sub_mem Q y.2 (hPQ hp)
        refine ⟨⟨k', Submodule.mem_inf.mpr ⟨hkQ, hk'⟩⟩, ?_⟩
        rw [← hyz]
        show (Submodule.mkQ (P.comap Q.subtype))
            (Submodule.inclusion inf_le_left ⟨k', Submodule.mem_inf.mpr ⟨hkQ, hk'⟩⟩) =
          (Submodule.mkQ (P.comap Q.subtype)) y
        rw [Submodule.mkQ_apply, Submodule.mkQ_apply, Submodule.Quotient.eq]
        refine Submodule.mem_comap.mpr ?_
        change (k' : V) - (y : V) ∈ P
        have h1 : (k' : V) - (y : V) = -p := by rw [← hpk']; abel
        rw [h1]
        exact Submodule.neg_mem P hp
    exact ((Submodule.quotEquivOfEq _ _ hker.symm).trans
      ((ψ.quotKerEquivRange).trans (LinearEquiv.ofEq _ _ hrange))).finrank_eq
  -- put the two together along the tower
  have h1 := Submodule.finrank_quotient_add_finrank
    (R := k) (((P ⊔ Kk).comap Q.subtype).map (P.comap Q.subtype).mkQ)
  have hKq : Module.finrank k ((↥Q ⧸ P.comap Q.subtype) ⧸
      ((P ⊔ Kk).comap Q.subtype).map (P.comap Q.subtype).mkQ)
      = Module.finrank k (↥Q ⧸ (P ⊔ Kk).comap Q.subtype) :=
    (Submodule.quotientQuotientEquivQuotient (P.comap Q.subtype)
      ((P ⊔ Kk).comap Q.subtype) hMN).finrank_eq
  rw [hKq] at h1
  rw [hK] at h1
  rw [← hL] at h1
  omega

end

/-- **The snake identity for the adèle lattices.**  For `D ≤ E` the dimension of
`A(E)/A(D)` is the sum of the dimensions of the `L`-part and the `K`-part:
`dim A(E)/A(D) = dim L(E)/L(D) + dim (A(E)+K)/(A(D)+K)`. -/
theorem snake {k : Type u} [Field k] (C : Work.CurveBasics.Curve k) {D E : C.Div}
    (h : D ≤ E) :
    Module.finrank k (Work.RiemannRoch.Curve.Aquot C D E) =
      Module.finrank k (Work.RiemannRoch.Curve.Lquot C D E) +
        Module.finrank k (Work.RiemannRoch.Curve.Kquot C D E) := by
  haveI : FiniteDimensional k (Aquot C D E) := finiteDimensional_Aquot C h
  exact finrank_snake_aux (A C D) (A C E) (Kdiag C) (A_mono C h)

end Work.RiemannRoch.RR
