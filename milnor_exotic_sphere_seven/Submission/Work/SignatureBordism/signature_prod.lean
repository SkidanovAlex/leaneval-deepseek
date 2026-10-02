import Mathlib
import Submission.Work.SignatureBordism.Signature

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

/-!
# Additivity of the signature over orthogonal direct sums

For quadratic forms `Q₁`, `Q₂` over a linearly ordered field, the signature of the orthogonal
direct sum `Q₁.prod Q₂` is the sum of the signatures.  The proof rests on the additivity of the
positive and negative indices (`sigPos`, `sigNeg`) over orthogonal direct sums, which we obtain
from `QuadraticForm.sigPos_add_finrank_le_of_nonpos` together with the existence, for a form `Q`,
of a subspace of dimension `finrank - sigPos Q` on which `Q` is nonpositive (the orthogonal
complement of a maximal positive definite subspace).
-/

namespace Work.SignatureBordism

open QuadraticMap

noncomputable section

section Prod

variable {𝕜 V W : Type*} [Field 𝕜] [LinearOrder 𝕜] [IsStrictOrderedRing 𝕜]
  [AddCommGroup V] [Module 𝕜 V] [AddCommGroup W] [Module 𝕜 W]
  [FiniteDimensional 𝕜 V] [FiniteDimensional 𝕜 W]

/-- `↥(p.prod q)` is linearly equivalent to `↥p × ↥q`. -/
private def subProdEquiv (p : Submodule 𝕜 V) (q : Submodule 𝕜 W) :
    ↥(p.prod q) ≃ₗ[𝕜] ↥p × ↥q where
  toFun x := (⟨x.1.1, (Submodule.mem_prod.mp x.2).1⟩, ⟨x.1.2, (Submodule.mem_prod.mp x.2).2⟩)
  invFun x := ⟨(x.1.1, x.2.1), Submodule.mem_prod.mpr ⟨x.1.2, x.2.2⟩⟩
  left_inv x := by ext <;> rfl
  right_inv x := by ext <;> rfl
  map_add' x y := by ext <;> rfl
  map_smul' c x := by ext <;> rfl

omit [LinearOrder 𝕜] [IsStrictOrderedRing 𝕜] in
private lemma finrank_prod_submodule (p : Submodule 𝕜 V) (q : Submodule 𝕜 W) :
    Module.finrank 𝕜 ↥(p.prod q) = Module.finrank 𝕜 ↥p + Module.finrank 𝕜 ↥q := by
  rw [LinearEquiv.finrank_eq (subProdEquiv p q), Module.finrank_prod]

/-- **Complement of a maximal positive definite subspace.**  There is a subspace of dimension
`finrank 𝕜 V - sigPos Q` on which `Q` is nonpositive (its "negative plus radical" part). -/
private lemma exists_finrank_sub_sigPos_nonpos (Q : QuadraticForm 𝕜 V) :
    ∃ Vneg : Submodule 𝕜 V, Module.finrank 𝕜 ↥Vneg = Module.finrank 𝕜 V - sigPos Q ∧
      ∀ x ∈ Vneg, Q x ≤ 0 := by
  obtain ⟨U, hUfin, hUpd⟩ := exists_finrank_eq_sigNeg_and_negDef Q
  have hUneg : ∀ x ∈ U, x ≠ 0 → Q x < 0 := by
    intro x hx hx0
    have h := hUpd ⟨x, hx⟩ (by simpa using hx0)
    rw [QuadraticMap.restrict_apply] at h
    simp only [neg_apply] at h
    linarith
  have hUle : ∀ x ∈ U, Q x ≤ 0 := by
    intro x hx
    by_cases hx0 : x = 0
    · rw [hx0, QuadraticMap.map_zero]
    · exact (hUneg x hx hx0).le
  refine ⟨U ⊔ Q.radical, ?_, ?_⟩
  · have hdisj : U ⊓ Q.radical = ⊥ := by
      rw [eq_bot_iff]
      intro x hx
      rw [Submodule.mem_bot]
      obtain ⟨hxU, hxR⟩ := Submodule.mem_inf.mp hx
      by_contra hx0
      have h0 : Q x = 0 := (QuadraticMap.mem_radical_iff'.mp hxR).1
      have := hUneg x hxU hx0
      linarith
    have hfr := Submodule.finrank_sup_add_finrank_inf_eq (K := 𝕜) U Q.radical
    rw [hdisj, finrank_bot, add_zero] at hfr
    rw [hfr, hUfin]
    have hrad := QuadraticForm.sigPos_add_sigNeg_add_radical (Q := Q)
    omega
  · intro x hx
    obtain ⟨u, hu, r, hr, rfl⟩ := Submodule.mem_sup.mp hx
    have hru : Q (u + r) = Q u := by
      rw [add_comm u r, (QuadraticMap.mem_radical_iff'.mp hr).2 u]
    exact hru.trans_le (hUle u hu)

/-- **Additivity of the positive index over orthogonal direct sums.** -/
private theorem sigPos_prod (Q₁ : QuadraticForm 𝕜 V) (Q₂ : QuadraticForm 𝕜 W) :
    sigPos (Q₁.prod Q₂) = sigPos Q₁ + sigPos Q₂ := by
  refine le_antisymm ?_ ?_
  · obtain ⟨Vneg, hVfin, hVneg⟩ := exists_finrank_sub_sigPos_nonpos Q₁
    obtain ⟨Wneg, hWfin, hWneg⟩ := exists_finrank_sub_sigPos_nonpos Q₂
    have hneg : ∀ x ∈ Vneg.prod Wneg, (Q₁.prod Q₂) x ≤ 0 := by
      intro x hx
      obtain ⟨hx1, hx2⟩ := Submodule.mem_prod.mp hx
      rw [QuadraticMap.prod_apply]
      exact add_nonpos (hVneg x.1 hx1) (hWneg x.2 hx2)
    have h := QuadraticForm.sigPos_add_finrank_le_of_nonpos (Q := Q₁.prod Q₂) hneg
    rw [finrank_prod_submodule Vneg Wneg, hVfin, hWfin, Module.finrank_prod] at h
    have h₁ := QuadraticForm.sigPos_add_sigNeg_add_radical (Q := Q₁)
    have h₂ := QuadraticForm.sigPos_add_sigNeg_add_radical (Q := Q₂)
    omega
  · obtain ⟨U1, hU1fin, hU1pd⟩ := exists_finrank_eq_sigPos_and_posDef Q₁
    obtain ⟨U2, hU2fin, hU2pd⟩ := exists_finrank_eq_sigPos_and_posDef Q₂
    have hpd : ((Q₁.prod Q₂).restrict (U1.prod U2)).PosDef := by
      intro x hx
      have hx1 : x.1.1 ∈ U1 := (Submodule.mem_prod.mp x.2).1
      have hx2 : x.1.2 ∈ U2 := (Submodule.mem_prod.mp x.2).2
      have hxne : x.1 ≠ 0 := fun h => hx (Subtype.ext h)
      rw [QuadraticMap.restrict_apply, QuadraticMap.prod_apply]
      rcases eq_or_ne x.1.1 0 with ha | ha
      · have hb : x.1.2 ≠ 0 := fun hb => hxne (Prod.ext ha hb)
        have h2 : 0 < Q₂ x.1.2 := by
          have hh := hU2pd ⟨x.1.2, hx2⟩ (fun h => hb (Subtype.ext_iff.mp h))
          rwa [QuadraticMap.restrict_apply] at hh
        rw [ha, QuadraticMap.map_zero, zero_add]
        exact h2
      · have h1 : 0 < Q₁ x.1.1 := by
          have hh := hU1pd ⟨x.1.1, hx1⟩ (fun h => ha (Subtype.ext_iff.mp h))
          rwa [QuadraticMap.restrict_apply] at hh
        have h2 : 0 ≤ Q₂ x.1.2 := by
          have hh := hU2pd.nonneg ⟨x.1.2, hx2⟩
          rwa [QuadraticMap.restrict_apply] at hh
        exact add_pos_of_pos_of_nonneg h1 h2
    have h := le_sigPos_of_posDef (Q₁.prod Q₂) hpd
    rw [finrank_prod_submodule U1 U2, hU1fin, hU2fin] at h
    exact h

/-- **Additivity of the negative index over orthogonal direct sums.** -/
private theorem sigNeg_prod (Q₁ : QuadraticForm 𝕜 V) (Q₂ : QuadraticForm 𝕜 W) :
    sigNeg (Q₁.prod Q₂) = sigNeg Q₁ + sigNeg Q₂ := by
  have h : -(Q₁.prod Q₂) = (-Q₁).prod (-Q₂) := by
    ext x
    simp only [QuadraticMap.prod_apply, neg_apply]
    ring
  rw [show sigNeg (Q₁.prod Q₂) = sigPos (-(Q₁.prod Q₂)) from rfl,
    show sigNeg Q₁ = sigPos (-Q₁) from rfl,
    show sigNeg Q₂ = sigPos (-Q₂) from rfl, h, sigPos_prod]

end Prod

open QuadraticMap in
theorem signature_prod {𝕜 V W : Type*} [Field 𝕜] [LinearOrder 𝕜] [IsStrictOrderedRing 𝕜]
    [AddCommGroup V] [Module 𝕜 V] [AddCommGroup W] [Module 𝕜 W]
    [FiniteDimensional 𝕜 V] [FiniteDimensional 𝕜 W]
    (Q₁ : QuadraticForm 𝕜 V) (Q₂ : QuadraticForm 𝕜 W) :
    Work.SignatureBordism.signature (Q₁.prod Q₂) =
      Work.SignatureBordism.signature Q₁ + Work.SignatureBordism.signature Q₂ := by
  rw [signature, sigPos_prod Q₁ Q₂, sigNeg_prod Q₁ Q₂, signature, signature]
  push_cast
  ring

end

end Work.SignatureBordism
