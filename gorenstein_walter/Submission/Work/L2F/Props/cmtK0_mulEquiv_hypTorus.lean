import Mathlib
import Submission.Work.L2F.Props.PGL2CommutatorTorusDefs
import Submission.Work.L2F.Conic.mem_hypTorus
import Submission.Work.L2F.Mat2.det_smul_one_add_smul
import Submission.Work.L2F.Mat2.commute_entries
import Submission.Work.L2F.Mat2.sq_eq_trace_smul_sub_det

open scoped MatrixGroups
open Matrix

set_option autoImplicit false

namespace Work.L2F.Props

variable {F : Type*} [Field F]

/-! ## The commutant of a non-scalar matrix `S` with `S * S = lam • 1`

All of this is linear algebra over an arbitrary field: no characteristic hypothesis is needed. -/

/-- A non-scalar `2 × 2` matrix `S` with `S * S = lam • 1` has `S.trace = 0` and
`S.det = -lam`.  (Cayley–Hamilton gives `S.trace • S = (lam + S.det) • 1`; a non-zero trace would
exhibit `S` as a scalar matrix.) -/
private lemma trace_det_of_sq_smul_one (S : Matrix (Fin 2) (Fin 2) F) (lam : F)
    (hS : S * S = lam • 1) (hns : ∀ c : F, S ≠ c • 1) :
    S.trace = 0 ∧ S.det = -lam := by
  have hCH : S * S = S.trace • S - S.det • (1 : Matrix (Fin 2) (Fin 2) F) :=
    Work.L2F.Mat2.sq_eq_trace_smul_sub_det F S
  have hmain : S.trace • S = (lam + S.det) • (1 : Matrix (Fin 2) (Fin 2) F) := by
    rw [hCH] at hS
    rw [sub_eq_iff_eq_add] at hS
    rw [hS, ← add_smul]
  have htr : S.trace = 0 := by
    by_contra h
    have hcoe : S = ((S.trace)⁻¹ * (lam + S.det)) • (1 : Matrix (Fin 2) (Fin 2) F) := by
      have h1 := congrArg (fun M : Matrix (Fin 2) (Fin 2) F => (S.trace)⁻¹ • M) hmain
      rw [smul_smul, smul_smul, inv_mul_cancel₀ h, one_smul] at h1
      exact h1
    exact (hns _) hcoe
  have hzero : (lam + S.det) • (1 : Matrix (Fin 2) (Fin 2) F) = 0 := by
    rw [← hmain, htr, zero_smul]
  refine ⟨htr, ?_⟩
  have h00 := congrArg (fun M : Matrix (Fin 2) (Fin 2) F => M 0 0) hzero
  exact eq_neg_of_add_eq_zero_right (by simpa using h00)

/-- A non-scalar `2 × 2` matrix `S` with `S * S = lam • 1` has zero diagonal sum: more precisely,
`S 1 1 = -S 0 0`. -/
private lemma sq_smul_one_entry (S : Matrix (Fin 2) (Fin 2) F) (lam : F)
    (hS : S * S = lam • 1) (hns : ∀ c : F, S ≠ c • 1) : S 1 1 = -S 0 0 := by
  obtain ⟨htr, -⟩ := trace_det_of_sq_smul_one S lam hS hns
  have h' : S 0 0 + S 1 1 = 0 := by rwa [Matrix.trace_fin_two] at htr
  exact eq_neg_of_add_eq_zero_right h'

/-- The commutant of a non-scalar `S` with `S * S = lam • 1` is the two-dimensional commutative
algebra `F·1 + F·S`. -/
private lemma commutant_sq_smul_one (S : Matrix (Fin 2) (Fin 2) F) (lam : F)
    (hS : S * S = lam • 1) (hns : ∀ c : F, S ≠ c • 1)
    (Y : Matrix (Fin 2) (Fin 2) F) (hcomm : Y * S = S * Y) :
    ∃ a b : F, Y = a • 1 + b • S := by
  obtain ⟨htr, -⟩ := trace_det_of_sq_smul_one S lam hS hns
  have hS11 : S 1 1 = -S 0 0 := sq_smul_one_entry S lam hS hns
  obtain ⟨E1, E2, E3⟩ := Work.L2F.Mat2.commute_entries F S Y htr hcomm
  by_cases hq : S 0 1 = 0
  · by_cases hr : S 1 0 = 0
    · -- `S` is diagonal; non-scalarity forces `2 * S 0 0 ≠ 0`
      have h2p : (2 : F) * S 0 0 ≠ 0 := by
        intro h2
        refine hns (S 0 0) ?_
        have hneg : -S 0 0 = S 0 0 := by
          have h' : S 0 0 + S 0 0 = 0 := by rwa [two_mul] at h2
          exact (eq_neg_of_add_eq_zero_right h').symm
        have h11 : S 1 1 = S 0 0 := by rw [hS11, hneg]
        ext i j
        fin_cases i <;> fin_cases j <;> simp [Matrix.smul_apply, hq, hr, h11]
      have hY01 : Y 0 1 = 0 := by
        have h := E2
        rw [hq, zero_mul] at h
        exact (mul_eq_zero.mp h.symm).resolve_left h2p
      have hY10 : Y 1 0 = 0 := by
        have h := E3
        rw [hr, zero_mul] at h
        exact (mul_eq_zero.mp h.symm).resolve_left h2p
      refine ⟨(Y 0 0 + Y 1 1) / 2, (Y 0 0 - Y 1 1) / (2 * S 0 0), ?_⟩
      have h2' : (2 : F) ≠ 0 := fun h => h2p (by rw [h, zero_mul])
      have hS00 : S 0 0 ≠ 0 := fun h => h2p (by rw [h, mul_zero])
      ext i j
      fin_cases i <;> fin_cases j
      · simp [Matrix.add_apply, Matrix.smul_apply]
        field_simp
        ring
      · simp [Matrix.add_apply, Matrix.smul_apply, hq]
        exact hY01
      · simp [Matrix.add_apply, Matrix.smul_apply, hr]
        exact hY10
      · simp [Matrix.add_apply, Matrix.smul_apply]
        rw [hS11]
        field_simp
        ring
    · -- `S 0 1 = 0`, `S 1 0 ≠ 0`
      have hY01 : Y 0 1 = 0 := by
        have h := E1
        rw [hq, zero_mul] at h
        exact (mul_eq_zero.mp h).resolve_right hr
      have hb10 : (Y 1 0 / S 1 0) * S 1 0 = Y 1 0 := div_mul_cancel₀ _ hr
      have hb2 : 2 * ((Y 1 0 / S 1 0) * S 0 0) = Y 0 0 - Y 1 1 := by
        apply mul_right_cancel₀ hr
        rw [mul_comm (Y 0 0 - Y 1 1) (S 1 0), E3]
        field_simp
      refine ⟨Y 0 0 - (Y 1 0 / S 1 0) * S 0 0, Y 1 0 / S 1 0, ?_⟩
      ext i j
      fin_cases i <;> fin_cases j
      · simp [Matrix.add_apply, Matrix.smul_apply]
      · simp [Matrix.add_apply, Matrix.smul_apply, hq]
        exact hY01
      · simp [Matrix.add_apply, Matrix.smul_apply, hq]
        exact hb10.symm
      · simp [Matrix.add_apply, Matrix.smul_apply]
        rw [hS11,
          show (Y 0 0 - Y 1 0 / S 1 0 * S 0 0) + Y 1 0 / S 1 0 * (-S 0 0)
              = Y 0 0 - 2 * ((Y 1 0 / S 1 0) * S 0 0) from by ring,
          hb2]
        ring
  · -- `S 0 1 ≠ 0`
    have hb01 : (Y 0 1 / S 0 1) * S 0 1 = Y 0 1 := div_mul_cancel₀ _ hq
    have hb10 : (Y 0 1 / S 0 1) * S 1 0 = Y 1 0 := by
      rw [div_mul_eq_mul_div, E1, mul_div_cancel_left₀ _ hq]
    have hb2 : 2 * ((Y 0 1 / S 0 1) * S 0 0) = Y 0 0 - Y 1 1 := by
      apply mul_right_cancel₀ hq
      rw [mul_comm (Y 0 0 - Y 1 1) (S 0 1), E2]
      field_simp
    refine ⟨Y 0 0 - (Y 0 1 / S 0 1) * S 0 0, Y 0 1 / S 0 1, ?_⟩
    ext i j
    fin_cases i <;> fin_cases j
    · simp [Matrix.add_apply, Matrix.smul_apply]
    · simp [Matrix.add_apply, Matrix.smul_apply]
      exact hb01.symm
    · simp [Matrix.add_apply, Matrix.smul_apply]
      exact hb10.symm
    · simp [Matrix.add_apply, Matrix.smul_apply]
      rw [hS11,
        show (Y 0 0 - Y 0 1 / S 0 1 * S 0 0) + Y 0 1 / S 0 1 * (-S 0 0)
            = Y 0 0 - 2 * ((Y 0 1 / S 0 1) * S 0 0) from by ring,
        hb2]
      ring

/-- The multiplication formula in the commutative algebra `F·1 + F·S`. -/
private lemma smul_one_add_smul_mul (S : Matrix (Fin 2) (Fin 2) F) (lam : F)
    (hS : S * S = lam • 1) (a b c e : F) :
    (a • 1 + b • S) * (c • 1 + e • S) =
      (a * c + lam * (b * e)) • (1 : Matrix (Fin 2) (Fin 2) F) + (a * e + b * c) • S := by
  simp only [Matrix.add_mul, Matrix.mul_add, Matrix.smul_mul, Matrix.mul_smul, Matrix.one_mul,
    Matrix.mul_one, hS, smul_smul, add_smul, smul_add]
  module

/-- `a • 1 + b • S` commutes with `S` when `S * S = lam • 1`. -/
private lemma smul_one_add_smul_comm (S : Matrix (Fin 2) (Fin 2) F) (lam : F)
    (hS : S * S = lam • 1) (a b : F) :
    (a • 1 + b • S) * S = S * (a • 1 + b • S) := by
  have h1 := smul_one_add_smul_mul S lam hS a b 0 1
  have h2 := smul_one_add_smul_mul S lam hS 0 1 a b
  simp only [zero_mul, mul_zero, zero_add, add_zero, mul_one, one_mul, zero_smul, one_smul] at h1 h2
  rw [h1, h2]

/-- The determinant of `a • 1 + b • S`, for a non-scalar `S` with `S * S = lam • 1`, is
`a ^ 2 - lam * b ^ 2`. -/
private lemma smul_one_add_smul_det (S : Matrix (Fin 2) (Fin 2) F) (lam : F)
    (hS : S * S = lam • 1) (hns : ∀ c : F, S ≠ c • 1) (a b : F) :
    (a • 1 + b • S).det = a ^ 2 - lam * b ^ 2 := by
  obtain ⟨htr, hdet⟩ := trace_det_of_sq_smul_one S lam hS hns
  rw [Work.L2F.Mat2.det_smul_one_add_smul F S a b, htr, hdet]
  ring

/-- The only way `a • 1 + b • S` can vanish for a non-scalar `S` is `a = b = 0`. -/
private lemma smul_one_add_smul_eq_zero (S : Matrix (Fin 2) (Fin 2) F)
    (hns : ∀ c : F, S ≠ c • 1) (a b : F) (h : a • 1 + b • S = 0) : a = 0 ∧ b = 0 := by
  have hb : b = 0 := by
    by_contra hb
    have h2 := congrArg (fun M : Matrix (Fin 2) (Fin 2) F => b⁻¹ • M) h
    simp only [smul_add, smul_smul, smul_zero] at h2
    rw [inv_mul_cancel₀ hb, one_smul, add_eq_zero_iff_eq_neg] at h2
    refine hns (-(b⁻¹ * a)) ?_
    rw [neg_smul, h2, neg_neg]
  subst hb
  have h1 : a • (1 : Matrix (Fin 2) (Fin 2) F) = 0 := by rw [← h]; simp
  have h2 := congrArg (fun M : Matrix (Fin 2) (Fin 2) F => M 0 0) h1
  exact ⟨by simpa using h2, rfl⟩

/-- The pair `(a, b)` in `a • 1 + b • S` is unique when `S` is not a scalar matrix. -/
private lemma smul_one_add_smul_inj (S : Matrix (Fin 2) (Fin 2) F)
    (hns : ∀ c : F, S ≠ c • 1) (a b c e : F) (h : a • 1 + b • S = c • 1 + e • S) :
    a = c ∧ b = e := by
  have h0 : (a - c) • (1 : Matrix (Fin 2) (Fin 2) F) + (b - e) • S = 0 := by
    have hsub : (a - c) • (1 : Matrix (Fin 2) (Fin 2) F) + (b - e) • S
        = (a • 1 + b • S) - (c • 1 + e • S) := by module
    rw [hsub, h, sub_self]
  obtain ⟨h1, h2⟩ := smul_one_add_smul_eq_zero S hns _ _ h0
  exact ⟨sub_eq_zero.mp h1, sub_eq_zero.mp h2⟩

/-! ## The `hypTorus` side -/

/-- Every element of `hypTorus F lam` is `!![a, lam * b; b, a]` with `a ^ 2 - lam * b ^ 2 = 1`; its
`(0,0)` and `(1,0)` entries are exactly the coefficients `a` and `b`. -/
private lemma hypTorus_form {lam : F} (x : ↥(Work.L2F.hypTorus F lam)) :
    ((((x : SL(2, F)) : Matrix (Fin 2) (Fin 2) F)) 0 0) ^ 2
        - lam * ((((x : SL(2, F)) : Matrix (Fin 2) (Fin 2) F)) 1 0) ^ 2 = 1 ∧
      ((x : SL(2, F)) : Matrix (Fin 2) (Fin 2) F) =
        !![((x : SL(2, F)) : Matrix (Fin 2) (Fin 2) F) 0 0,
            lam * (((x : SL(2, F)) : Matrix (Fin 2) (Fin 2) F) 1 0);
            ((x : SL(2, F)) : Matrix (Fin 2) (Fin 2) F) 1 0,
            ((x : SL(2, F)) : Matrix (Fin 2) (Fin 2) F) 0 0] := by
  obtain ⟨a, b, hab, hM⟩ := (Work.L2F.Conic.mem_hypTorus F lam (x : SL(2, F))).mp x.2
  have h00 : ((x : SL(2, F)) : Matrix (Fin 2) (Fin 2) F) 0 0 = a := by rw [hM]; simp
  have h10 : ((x : SL(2, F)) : Matrix (Fin 2) (Fin 2) F) 1 0 = b := by rw [hM]; simp
  rw [h00, h10]
  exact ⟨hab, hM⟩

/-- The `(0,0)` slot of a product of two elements of `hypTorus F lam`, in terms of the slots of the
factors: this is the multiplication law `(a + bS)(c + eS) = (ac + lam·be) + (ae + bc)S`. -/
private lemma hypTorus_mul_entry00 {lam : F} (x y : ↥(Work.L2F.hypTorus F lam)) :
    (((x * y : ↥(Work.L2F.hypTorus F lam)) : SL(2, F)) : Matrix (Fin 2) (Fin 2) F) 0 0 =
      (((x : SL(2, F)) : Matrix (Fin 2) (Fin 2) F)) 0 0
          * (((y : SL(2, F)) : Matrix (Fin 2) (Fin 2) F)) 0 0
        + lam * ((((x : SL(2, F)) : Matrix (Fin 2) (Fin 2) F)) 1 0
          * (((y : SL(2, F)) : Matrix (Fin 2) (Fin 2) F)) 1 0) := by
  rw [Subgroup.coe_mul, Matrix.SpecialLinearGroup.coe_mul, Matrix.mul_apply, Fin.sum_univ_two,
    (hypTorus_form x).2, (hypTorus_form y).2]
  simp
  ring

/-- The `(1,0)` slot of a product of two elements of `hypTorus F lam`. -/
private lemma hypTorus_mul_entry10 {lam : F} (x y : ↥(Work.L2F.hypTorus F lam)) :
    (((x * y : ↥(Work.L2F.hypTorus F lam)) : SL(2, F)) : Matrix (Fin 2) (Fin 2) F) 1 0 =
      (((x : SL(2, F)) : Matrix (Fin 2) (Fin 2) F)) 0 0
          * (((y : SL(2, F)) : Matrix (Fin 2) (Fin 2) F)) 1 0
        + (((x : SL(2, F)) : Matrix (Fin 2) (Fin 2) F)) 1 0
          * (((y : SL(2, F)) : Matrix (Fin 2) (Fin 2) F)) 0 0 := by
  rw [Subgroup.coe_mul, Matrix.SpecialLinearGroup.coe_mul, Matrix.mul_apply, Fin.sum_univ_two,
    (hypTorus_form x).2, (hypTorus_form y).2]
  simp
  ring

/-- An explicit element of `SL(2,F)` with entries `a, lam*b ; b, a` and `a² - lam·b² = 1`
has determinant `1`. -/
private lemma sl_mk_hyp_det (lam a b : F) (hab : a ^ 2 - lam * b ^ 2 = 1) :
    (!![a, lam * b; b, a] : Matrix (Fin 2) (Fin 2) F).det = 1 := by
  rw [Matrix.det_fin_two_of]
  rw [← hab]
  ring

/-- `cmtK0 F S` is isomorphic to the norm-one torus `hypTorus F lam`.  The map sends
`a • 1 + b • S` to `!![a, lam*b; b, a]`; it is multiplicative because
`(a + bS)(c + eS) = (ac + lam·be) + (ae + bc)S` and matches `hypTorus`'s multiplication
(`Work.L2F.Conic.hypMat_mul`). -/
theorem cmtK0_mulEquiv_hypTorus (F : Type*) [Field F] (S : Matrix.GeneralLinearGroup (Fin 2) F) (lam : F)
    (hS : (S : Matrix (Fin 2) (Fin 2) F) * (S : Matrix (Fin 2) (Fin 2) F) = lam • 1)
    (hlam : lam ≠ 0) (hns : ∀ c : F, (S : Matrix (Fin 2) (Fin 2) F) ≠ c • 1) :
    Nonempty (Work.L2F.Props.cmtK0 F S ≃* Work.L2F.hypTorus F lam) := by
  let Sm : Matrix (Fin 2) (Fin 2) F := (S : Matrix (Fin 2) (Fin 2) F)
  have hSm : Sm * Sm = lam • 1 := by simpa only [Sm] using hS
  have hnsm : ∀ c : F, Sm ≠ c • 1 := fun c => by simpa only [Sm] using hns c
  -- the underlying `SL(2,F)`-valued map
  let phiSL : ↥(Work.L2F.hypTorus F lam) → SL(2, F) := fun x =>
    ⟨((x : SL(2, F)) : Matrix (Fin 2) (Fin 2) F) 0 0 • (1 : Matrix (Fin 2) (Fin 2) F)
        + ((x : SL(2, F)) : Matrix (Fin 2) (Fin 2) F) 1 0 • Sm, by
      obtain ⟨a, b, hab, hM⟩ := (Work.L2F.Conic.mem_hypTorus F lam (x : SL(2, F))).mp x.2
      have h00 : ((x : SL(2, F)) : Matrix (Fin 2) (Fin 2) F) 0 0 = a := by rw [hM]; simp
      have h10 : ((x : SL(2, F)) : Matrix (Fin 2) (Fin 2) F) 1 0 = b := by rw [hM]; simp
      rw [h00, h10, smul_one_add_smul_det Sm lam hSm hnsm a b, hab]⟩
  have hphiSL : ∀ x : ↥(Work.L2F.hypTorus F lam),
      ((phiSL x : SL(2, F)) : Matrix (Fin 2) (Fin 2) F)
        = ((x : SL(2, F)) : Matrix (Fin 2) (Fin 2) F) 0 0 • (1 : Matrix (Fin 2) (Fin 2) F)
          + ((x : SL(2, F)) : Matrix (Fin 2) (Fin 2) F) 1 0 • Sm := fun x => rfl
  -- the map, into the centralizer of `S` in `SL(2,F)`
  let phiFun : ↥(Work.L2F.hypTorus F lam) → ↥(Work.L2F.Props.cmtK0 F S) := fun x =>
    ⟨phiSL x, by
      rw [Work.L2F.Props.mem_cmtK0_iff_comm]
      apply Units.ext
      rw [Matrix.GeneralLinearGroup.coe_mul, Matrix.GeneralLinearGroup.coe_mul]
      exact smul_one_add_smul_comm Sm lam hSm _ _⟩
  have hphiFun : ∀ x : ↥(Work.L2F.hypTorus F lam),
      ((phiFun x : SL(2, F)) : Matrix (Fin 2) (Fin 2) F)
        = ((x : SL(2, F)) : Matrix (Fin 2) (Fin 2) F) 0 0 • (1 : Matrix (Fin 2) (Fin 2) F)
          + ((x : SL(2, F)) : Matrix (Fin 2) (Fin 2) F) 1 0 • Sm := fun x => hphiSL x
  let Φ : ↥(Work.L2F.hypTorus F lam) →* ↥(Work.L2F.Props.cmtK0 F S) :=
    { toFun := phiFun
      map_one' := by
        apply Subtype.ext
        apply Subtype.ext
        rw [hphiFun 1]
        simp [Matrix.add_apply, Matrix.smul_apply]
      map_mul' := by
        intro x y
        apply Subtype.ext
        rw [Subgroup.coe_mul]
        apply Subtype.ext
        rw [Matrix.SpecialLinearGroup.coe_mul]
        simp only [hphiFun (x * y), hphiFun x, hphiFun y]
        rw [hypTorus_mul_entry00 x y, hypTorus_mul_entry10 x y,
          smul_one_add_smul_mul Sm lam hSm _ _ _ _] }
  have hinj : Function.Injective Φ := by
    intro x y hxy
    have hmat : (((Φ x : SL(2, F)) : Matrix (Fin 2) (Fin 2) F))
        = (((Φ y : SL(2, F)) : Matrix (Fin 2) (Fin 2) F)) :=
      congrArg (fun z : ↥(Work.L2F.Props.cmtK0 F S) =>
        (((z : SL(2, F)) : Matrix (Fin 2) (Fin 2) F))) hxy
    change (((x : SL(2, F)) : Matrix (Fin 2) (Fin 2) F) 0 0 • (1 : Matrix (Fin 2) (Fin 2) F)
        + ((x : SL(2, F)) : Matrix (Fin 2) (Fin 2) F) 1 0 • Sm)
      = (((y : SL(2, F)) : Matrix (Fin 2) (Fin 2) F) 0 0 • (1 : Matrix (Fin 2) (Fin 2) F)
        + ((y : SL(2, F)) : Matrix (Fin 2) (Fin 2) F) 1 0 • Sm) at hmat
    obtain ⟨e0, e1⟩ := smul_one_add_smul_inj Sm hnsm _ _ _ _ hmat
    apply Subtype.ext
    apply Subtype.ext
    rw [(hypTorus_form x).2, (hypTorus_form y).2, e0, e1]
  have hsurj : Function.Surjective Φ := by
    intro z
    have hcommGL : Matrix.SpecialLinearGroup.toGL (z : SL(2, F)) * S
        = S * Matrix.SpecialLinearGroup.toGL (z : SL(2, F)) :=
      (Work.L2F.Props.mem_cmtK0_iff_comm F S (z : SL(2, F))).mp z.2
    have hcomm : ((z : SL(2, F)) : Matrix (Fin 2) (Fin 2) F) * Sm
        = Sm * ((z : SL(2, F)) : Matrix (Fin 2) (Fin 2) F) := by
      have h := congrArg (fun u : GL (Fin 2) F => (u : Matrix (Fin 2) (Fin 2) F)) hcommGL
      rw [Matrix.GeneralLinearGroup.coe_mul, Matrix.GeneralLinearGroup.coe_mul] at h
      change ((↑(Matrix.SpecialLinearGroup.toGL (z : SL(2, F))) : Matrix (Fin 2) (Fin 2) F))
          * (S : Matrix (Fin 2) (Fin 2) F)
        = (S : Matrix (Fin 2) (Fin 2) F)
          * (↑(Matrix.SpecialLinearGroup.toGL (z : SL(2, F))) : Matrix (Fin 2) (Fin 2) F)
      exact h
    obtain ⟨a, b, hab⟩ := commutant_sq_smul_one Sm lam hSm hnsm _ hcomm
    have hdet : ((z : SL(2, F)) : Matrix (Fin 2) (Fin 2) F).det = 1 :=
      Matrix.SpecialLinearGroup.det_coe _
    have hnorm : a ^ 2 - lam * b ^ 2 = 1 := by
      rw [hab, smul_one_add_smul_det Sm lam hSm hnsm a b] at hdet
      exact hdet
    have hzdet : (!![a, lam * b; b, a] : Matrix (Fin 2) (Fin 2) F).det = 1 :=
      sl_mk_hyp_det lam a b hnorm
    have hzmem : (⟨!![a, lam * b; b, a], hzdet⟩ : SL(2, F)) ∈ Work.L2F.hypTorus F lam :=
      (Work.L2F.Conic.mem_hypTorus F lam ⟨!![a, lam * b; b, a], hzdet⟩).mpr ⟨a, b, hnorm, rfl⟩
    let z' : ↥(Work.L2F.hypTorus F lam) := ⟨⟨!![a, lam * b; b, a], hzdet⟩, hzmem⟩
    refine ⟨z', ?_⟩
    have hzmat : ((z' : SL(2, F)) : Matrix (Fin 2) (Fin 2) F) = !![a, lam * b; b, a] := rfl
    have h1 : ((Φ z' : SL(2, F)) : Matrix (Fin 2) (Fin 2) F)
        = ((z' : SL(2, F)) : Matrix (Fin 2) (Fin 2) F) 0 0 • (1 : Matrix (Fin 2) (Fin 2) F)
          + ((z' : SL(2, F)) : Matrix (Fin 2) (Fin 2) F) 1 0 • Sm := hphiFun z'
    have h2 : ((z' : SL(2, F)) : Matrix (Fin 2) (Fin 2) F) 0 0 • (1 : Matrix (Fin 2) (Fin 2) F)
          + ((z' : SL(2, F)) : Matrix (Fin 2) (Fin 2) F) 1 0 • Sm
        = a • (1 : Matrix (Fin 2) (Fin 2) F) + b • Sm := by
      rw [hzmat]
      simp
    apply Subtype.ext
    apply Subtype.ext
    rw [h1, h2, hab]
  exact ⟨(MulEquiv.ofBijective Φ ⟨hinj, hsurj⟩).symm⟩

end Work.L2F.Props
