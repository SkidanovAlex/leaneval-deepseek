import Mathlib
import Submission.Work.Mostow.HaarBase
import Submission.Work.Mostow.poSheet
import Submission.Work.Mostow.poCenter
import Submission.Work.Mostow.QIDefs

/-!
# A `Γ`-packed set is no larger than a fundamental domain

`Work.Mostow.volH_le_fundamentalDomain`: if `D` is a fundamental domain for a discrete subgroup
`Γ ≤ PO(n,1)` acting on `ℍⁿ = E n`, and `A` is a null-measurable set whose `Γ`-translates are
pairwise a.e. disjoint, then `volH A ≤ volH D`.

The mathematical content is the standard "packing bound": the sets `γ • A ∩ D` (`γ ∈ Γ`) are
pairwise a.e. disjoint subsets of `D`, and `MeasureTheory.IsFundamentalDomain.measure_eq_tsum'`
computes `volH A` as the sum of their measures.

To *state* the packing bound Mathlib needs a `MulAction Γ (E n)`.  The action of `PO n 1` on `E n`
is defined through an arbitrary representative (`g • u = actO (Quotient.out g) u`, see
`Submission.Mostow.Interfaces`), so the action axioms are not immediate.  The key point is that two
representatives of the same class differ by a central element of `O(n,1)`, and central elements act
trivially; this is proved here (`actO_eq_id_of_mem_center`) by the same diagonal/boost computation
as the classification `Work.Mostow.poCenter` of the centre, but for *every* `n` (no `2 ≤ n`).
-/

namespace Work.Mostow

open Submission.Mostow LeanEval.Geometry.MostowRigidity MeasureTheory Matrix
open scoped ENNReal Pointwise

noncomputable section

variable {n : ℕ}

/-! ## Central elements of `O(n,1)` act trivially on the chart -/

/-- A central element of `O(n,1)` acts trivially on the chart `E n`.

Testing a central `C` against the diagonal sign matrices `diagSignElem b` shows that `mat C` is
diagonal; testing it against the hyperbolic boosts `boostElem i` shows that all diagonal entries
are equal, so `mat C = λ • 1`; the defining relation of `O(n,1)` forces `λ = ±1`, and both `±1`
act by the identity. -/
lemma actO_eq_id_of_mem_center {C : O1 n} (hC : C ∈ Subgroup.center (O1 n)) : actO C = id := by
  have hcomm : ∀ g : O1 n, g * C = C * g := (Subgroup.mem_center_iff).1 hC
  -- (1) `mat C` is diagonal: test against the diagonal sign matrices.
  have hoff : ∀ a b : Fin n ⊕ Fin 1, a ≠ b → mat C a b = 0 := by
    intro a b hab
    have hentry : (mat (diagSignElem b) * mat C) a b = (mat C * mat (diagSignElem b)) a b := by
      have := congrArg (fun X : O1 n => mat X a b) (hcomm (diagSignElem b))
      simpa [mat_mul] using this
    simp only [mat_diagSignElem, diagSign, Matrix.diagonal_mul, Matrix.mul_diagonal] at hentry
    rw [if_neg hab] at hentry
    simp at hentry
    linarith
  have hdiag : mat C = Matrix.diagonal (fun c => mat C c c) := by
    ext a b
    by_cases hab : a = b
    · subst hab; simp
    · rw [Matrix.diagonal_apply, if_neg hab]
      exact hoff a b hab
  -- (2) all diagonal entries are equal: test against the hyperbolic boosts.
  have hentry_eq : ∀ i : Fin n,
      mat C (Sum.inl i) (Sum.inl i) = mat C (Sum.inr 0) (Sum.inr 0) := by
    intro i
    have hb : (mat (boostElem i) * mat C) (Sum.inl i) (Sum.inr 0) =
        (mat C * mat (boostElem i)) (Sum.inl i) (Sum.inr 0) := by
      have := congrArg (fun X : O1 n => mat X (Sum.inl i) (Sum.inr 0)) (hcomm (boostElem i))
      simpa [mat_mul] using this
    rw [mat_boostElem i, hdiag, Matrix.diagonal_mul, Matrix.mul_diagonal] at hb
    simp only [boost_apply_spatial_time] at hb
    rw [mul_comm (mat C (Sum.inl i) (Sum.inl i)) ((3 : ℝ) / 4)] at hb
    exact (mul_left_cancel₀ (by norm_num : (3 : ℝ) / 4 ≠ 0) hb).symm
  have hconst : ∀ c : Fin n ⊕ Fin 1, mat C c c = mat C (Sum.inr 0) (Sum.inr 0) := by
    intro c
    rcases c with i | j
    · exact hentry_eq i
    · obtain rfl : j = 0 := Subsingleton.elim j 0
      rfl
  have hmat_const : mat C = Matrix.diagonal
      (fun _ : Fin n ⊕ Fin 1 => mat C (Sum.inr 0) (Sum.inr 0)) := by
    rw [hdiag, Matrix.diagonal_eq_diagonal_iff]
    exact hconst
  set e := mat C (Sum.inr 0) (Sum.inr 0) with he
  -- (3) the defining relation of `O(n,1)` forces `e ^ 2 = 1`.
  have hesq : e ^ 2 = 1 := by
    have hcol := O1_form_col C
    rw [hmat_const, Matrix.diagonal_transpose, pmOneMat_eq_diagonal_poCenterDefs, mul_assoc,
      Matrix.diagonal_mul_diagonal, Matrix.diagonal_mul_diagonal,
      Matrix.diagonal_eq_diagonal_iff] at hcol
    have h0 := hcol (Sum.inr 0)
    simp only [jSign_inr] at h0
    nlinarith
  rw [← Matrix.smul_one_eq_diagonal] at hmat_const
  rcases sq_eq_one_iff.mp hesq with h | h
  · have hC1 : C = 1 := mat_injective (by rw [hmat_const, h, one_smul, mat_one])
    rw [hC1]
    funext u
    exact poSheet_actO_one u
  · have hCn1 : C = -1 := mat_injective
      (by rw [hmat_const, h, neg_smul, one_smul, mat_neg, mat_one])
    rw [hCn1]
    funext u
    rw [poSheet_actO_neg]
    simpa using poSheet_actO_one u

/-! ## The `PO n 1`-action axioms -/

/-- A representative computes the same `actO` as the element it represents. -/
lemma actO_rep_eq_mk (A : O1 n) : actO (rep (A : PO n 1)) = actO A := by
  have hc : (rep (A : PO n 1))⁻¹ * A ∈ Subgroup.center (O1 n) :=
    QuotientGroup.eq.1 (QuotientGroup.out_eq' (A : PO n 1))
  have hA : A = rep (A : PO n 1) * ((rep (A : PO n 1))⁻¹ * A) := by
    rw [← mul_assoc, mul_inv_cancel, one_mul]
  have h2 : actO A = actO (rep (A : PO n 1)) := by
    calc actO A
        = actO (rep (A : PO n 1) * ((rep (A : PO n 1))⁻¹ * A)) :=
          congrArg (fun X : O1 n => actO X) hA
      _ = actO (rep (A : PO n 1)) ∘ actO ((rep (A : PO n 1))⁻¹ * A) := by
          funext u
          exact poSheet_actO_mul _ _ u
      _ = actO (rep (A : PO n 1)) := by
          rw [actO_eq_id_of_mem_center hc, Function.comp_id]
  exact h2.symm

/-- The action of `PO n 1` computed by a matrix representative. -/
lemma poSMul_mk (A : O1 n) (u : E n) : (A : PO n 1) • u = actO A u := by
  show actO (rep (A : PO n 1)) u = actO A u
  rw [actO_rep_eq_mk]

lemma poOneSMul (u : E n) : (1 : PO n 1) • u = u := by
  rw [show (1 : PO n 1) = ((1 : O1 n) : PO n 1) from
        (QuotientGroup.mk_one (Subgroup.center (O1 n))).symm, poSMul_mk, poSheet_actO_one]

lemma poMulSMul (g h : PO n 1) (u : E n) : (g * h) • u = g • (h • u) := by
  obtain ⟨A, rfl⟩ := QuotientGroup.mk_surjective g
  obtain ⟨B, rfl⟩ := QuotientGroup.mk_surjective h
  simp only [← QuotientGroup.mk_mul, poSMul_mk, poSheet_actO_mul]

/-! ## The main bound -/

theorem volH_le_fundamentalDomain {n : ℕ} (hI : Submission.Mostow.HypIsometryProp n)
    {Γ : Subgroup (LeanEval.Geometry.MostowRigidity.PO n 1)}
    (hdisc : IsDiscrete (SetLike.coe Γ)) {D A : Set (Submission.Mostow.E n)}
    (hD : MeasureTheory.IsFundamentalDomain Γ D (Submission.Mostow.volH n))
    (hAmeas : MeasureTheory.NullMeasurableSet A (Submission.Mostow.volH n))
    (hdisj : ∀ γ : Γ, γ ≠ 1 → MeasureTheory.AEDisjoint (Submission.Mostow.volH n)
      ((fun x => (γ : LeanEval.Geometry.MostowRigidity.PO n 1) • x) '' A) A) :
    Submission.Mostow.volH n A ≤ Submission.Mostow.volH n D := by
  have hId : HypIsoData n := HypIsoData.ofProp hI
  -- the action of `Γ` on `ℍⁿ = E n`
  letI : MulAction (PO n 1) (E n) :=
    { one_smul := fun u => poOneSMul u
      mul_smul := fun g h u => poMulSMul g h u }
  letI : MulAction Γ (E n) := inferInstance
  haveI : MeasurableConstSMul Γ (E n) :=
    ⟨fun c => (hId.contDiff_smul (c : PO n 1)).continuous.measurable⟩
  haveI : SMulInvariantMeasure Γ (E n) (volH n) :=
    ⟨fun c s hs => (hId.measurePreserving_smul (c : PO n 1)).measure_preimage hs.nullMeasurableSet⟩
  haveI : Countable Γ := countable_of_isDiscrete (PO n 1) hdisc
  refine hD.measure_le_of_pairwise_disjoint hAmeas ?_
  rintro g₁ g₂ hne
  show volH n ((g₁ • A ∩ D) ∩ (g₂ • A ∩ D)) = 0
  have hsub₁ : (g₁ • A ∩ D) ∩ (g₂ • A ∩ D) ⊆ g₁ • A ∩ g₂ • A :=
    fun x hx => ⟨hx.1.1, hx.2.1⟩
  have hδne : g₂⁻¹ * g₁ ≠ (1 : Γ) := by
    intro h
    have h1 : g₁ = g₂ := by
      calc g₁ = g₂ * (g₂⁻¹ * g₁) := by group
        _ = g₂ := by rw [h, mul_one]
    exact hne h1
  have hg₁ : g₁ • A = g₂ • ((g₂⁻¹ * g₁) • A) := by
    rw [smul_smul, ← mul_assoc, mul_inv_cancel, one_mul]
  have hsub₂ : g₁ • A ∩ g₂ • A ⊆ g₂ • ((g₂⁻¹ * g₁) • A ∩ A) := by
    rw [Set.smul_set_inter, hg₁]
  have hnull : volH n (g₂ • ((g₂⁻¹ * g₁) • A ∩ A)) = 0 := by
    rw [measure_smul (volH n) g₂]
    exact hdisj (g₂⁻¹ * g₁) hδne
  exact measure_mono_null (hsub₁.trans hsub₂) hnull

end

end Work.Mostow
