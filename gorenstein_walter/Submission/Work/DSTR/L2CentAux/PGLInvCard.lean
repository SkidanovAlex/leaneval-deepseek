import Mathlib
import Submission.Work.L2F.Torus.commute_iff_mem_algSpan
import Submission.Work.L2F.Mat2.sq_eq_trace_smul_sub_det
import Submission.Work.L2F.Mat2.det_smul_one_add_smul
import Submission.Work.DSTR.L2CentAux.CardKerMap

/-!
# `Work.DSTR.L2CentAux.PGLInvCard`

The centraliser of an involution `t` of `PGL(2,q)`, `q = p^k` odd and `q ≥ 5`, has order
`2(q-1)` or `2(q+1)`.

Lifting `t` to `G ∈ GL(2,F)` gives `G^2 = D • 1` with `D ≠ 0`, `tr G = 0` and `G` not scalar, so
`(2 : F) ≠ 0` makes `G` a "regular semisimple" element whose commutant in `M_2(F)` is the
two-dimensional algebra `F·1 + F·G`.  The centraliser of `G` in `GL(2,F)` is therefore in bijection
with `{(a,b) | a^2 - D b^2 ≠ 0}`, of order `(q-1)^2` when `D` is a square and `q^2 - 1` when it is
not.  The normaliser of `⟨G⟩` in `GL(2,F)` is twice as large (an inverting element always exists),
and its image in `PGL(2,F)` — which is exactly the centraliser of `t` — has order `2(q∓1)`.
-/

open scoped MatrixGroups

namespace Work.DSTR.L2CentAux


/-- Setup: an involution of `PGL(2,F)` lifts to `G ∈ GL(2,F)` with `G^2 = D • 1`, `tr G = 0`,
and `G` not scalar. -/
lemma setup {F : Type*} [Field F] (h2 : (2 : F) ≠ 0)
    (t : Matrix.ProjGenLinGroup (Fin 2) F) (ht : orderOf t = 2) :
    ∃ (G : Matrix.GeneralLinearGroup (Fin 2) F) (D : F), D ≠ 0 ∧
      Matrix.ProjGenLinGroup.mk G = t ∧
      (G : Matrix (Fin 2) (Fin 2) F) * (G : Matrix (Fin 2) (Fin 2) F) = D • 1 ∧
      (G : Matrix (Fin 2) (Fin 2) F).trace = 0 ∧
      ¬ ∃ c : F, (G : Matrix (Fin 2) (Fin 2) F) = c • 1 := by
  classical
  have ht1 : t ≠ 1 := by
    intro h; rw [h, orderOf_one] at ht; exact absurd ht (by norm_num)
  have htt : t * t = 1 := by
    have h1 : orderOf t ∣ 2 := by rw [ht]
    have h2' := (orderOf_dvd_iff_pow_eq_one (x := t) (n := 2)).mp h1
    rwa [pow_two] at h2'
  obtain ⟨G, hG⟩ := Matrix.ProjGenLinGroup.mk_surjective t
  have hGGmem : G * G ∈ (Matrix.ProjGenLinGroup.mk : Matrix.GeneralLinearGroup (Fin 2) F →*
      Matrix.ProjGenLinGroup (Fin 2) F).ker := by
    rw [MonoidHom.mem_ker, map_mul, hG, htt]
  rw [Matrix.ProjGenLinGroup.ker_mk, Matrix.GeneralLinearGroup.center_eq_range_scalar,
    MonoidHom.mem_range] at hGGmem
  obtain ⟨w, hw⟩ := hGGmem
  have hw' : (G : Matrix (Fin 2) (Fin 2) F) * (G : Matrix (Fin 2) (Fin 2) F) = (w : F) • 1 := by
    have h := congrArg (fun x : Matrix.GeneralLinearGroup (Fin 2) F =>
      (x : Matrix (Fin 2) (Fin 2) F)) hw
    rw [Matrix.GeneralLinearGroup.coe_mul, Matrix.GeneralLinearGroup.coe_scalar] at h
    rw [← h]
    ext i j
    by_cases hij : i = j <;> simp [Matrix.scalar_apply, hij]
  have hD : (w : F) ≠ 0 := w.ne_zero
  have hns : ¬ ∃ c : F, (G : Matrix (Fin 2) (Fin 2) F) = c • 1 := by
    rintro ⟨c, hc⟩
    have hcc : c * c = (w : F) := by
      have hsq : (w : F) • (1 : Matrix (Fin 2) (Fin 2) F) = (c * c) • 1 := by
        rw [← hw', hc, Matrix.smul_mul, Matrix.mul_smul, Matrix.one_mul, smul_smul]
      have h := congrArg (fun M : Matrix (Fin 2) (Fin 2) F => M 0 0) hsq
      simpa using h.symm
    have hc0 : c ≠ 0 := by rintro rfl; simp at hcc; exact hD hcc.symm
    apply ht1
    rw [← hG, Matrix.ProjGenLinGroup.mk_eq_one,
      Matrix.GeneralLinearGroup.mem_center_iff_val_mem_range_scalar]
    refine ⟨Units.mk0 c hc0, ?_⟩
    show (Matrix.scalar (Fin 2) (↑(Units.mk0 c hc0) : F) : Matrix (Fin 2) (Fin 2) F) =
      (G : Matrix (Fin 2) (Fin 2) F)
    rw [Units.val_mk0, hc]
    ext i j
    by_cases hij : i = j <;> simp [Matrix.scalar_apply, hij]
  have htr : (G : Matrix (Fin 2) (Fin 2) F).trace = 0 := by
    by_contra htrne
    have hCH := Work.L2F.Mat2.sq_eq_trace_smul_sub_det F (G : Matrix (Fin 2) (Fin 2) F)
    have hkey : (G : Matrix (Fin 2) (Fin 2) F).trace • (G : Matrix (Fin 2) (Fin 2) F) =
        ((w : F) + (G : Matrix (Fin 2) (Fin 2) F).det) • 1 := by
      rw [hCH] at hw'
      rw [sub_eq_iff_eq_add] at hw'
      rw [hw', add_smul]
    refine hns ⟨((G : Matrix (Fin 2) (Fin 2) F).trace)⁻¹ *
      ((w : F) + (G : Matrix (Fin 2) (Fin 2) F).det), ?_⟩
    have h := congrArg (fun M : Matrix (Fin 2) (Fin 2) F =>
      ((G : Matrix (Fin 2) (Fin 2) F).trace)⁻¹ • M) hkey
    simp only [smul_smul, inv_mul_cancel₀ htrne, one_smul] at h
    exact h
  exact ⟨G, (w : F), hD, hG, hw', htr, hns⟩



/-- The scalar matrix `u • 1` as an element of `GL(2,F)`. -/
lemma coe_scalar_eq_smul {F : Type*} [Field F] (u : Fˣ) :
    ((Matrix.GeneralLinearGroup.scalar (Fin 2) u : Matrix.GeneralLinearGroup (Fin 2) F) :
      Matrix (Fin 2) (Fin 2) F) = (u : F) • 1 := by
  rw [Matrix.GeneralLinearGroup.coe_scalar]
  ext i j
  by_cases h : i = j <;> simp [Matrix.scalar_apply, h]

/-- `X = a • G` as matrices implies `mk X = mk G` when `a ≠ 0`. -/
lemma mk_eq_of_eq_smul {F : Type*} [Field F] (X G : Matrix.GeneralLinearGroup (Fin 2) F)
    {a : F} (ha : a ≠ 0)
    (h : (X : Matrix (Fin 2) (Fin 2) F) = a • (G : Matrix (Fin 2) (Fin 2) F)) :
    Matrix.ProjGenLinGroup.mk X = Matrix.ProjGenLinGroup.mk G := by
  obtain ⟨u, rfl⟩ : ∃ u : Fˣ, (u : F) = a := ⟨Units.mk0 a ha, rfl⟩
  have hX : X = Matrix.GeneralLinearGroup.scalar (Fin 2) u * G := by
    apply Units.ext
    rw [Matrix.GeneralLinearGroup.coe_mul, coe_scalar_eq_smul, Matrix.smul_mul, Matrix.one_mul, h]
  rw [hX, map_mul, Matrix.ProjGenLinGroup.mk_scalar, one_mul]

/-- `mk X = mk G` iff `X = a • G` for some nonzero scalar `a`. -/
lemma mk_eq_mk_iff_eq_smul {F : Type*} [Field F] (X G : Matrix.GeneralLinearGroup (Fin 2) F) :
    Matrix.ProjGenLinGroup.mk X = Matrix.ProjGenLinGroup.mk G ↔
      ∃ a : F, a ≠ 0 ∧ (X : Matrix (Fin 2) (Fin 2) F) = a • (G : Matrix (Fin 2) (Fin 2) F) := by
  constructor
  · intro h
    obtain ⟨u, hu⟩ := Matrix.ProjGenLinGroup.mk_eq_mk_iff.mp h
    have hu' : (X : Matrix (Fin 2) (Fin 2) F) * ((u : F) • 1) = (G : Matrix (Fin 2) (Fin 2) F) := by
      have h2 := congrArg (fun t : Matrix.GeneralLinearGroup (Fin 2) F =>
        (t : Matrix (Fin 2) (Fin 2) F)) hu
      rwa [Matrix.GeneralLinearGroup.coe_mul, coe_scalar_eq_smul] at h2
    refine ⟨(u : F)⁻¹, inv_ne_zero u.ne_zero, ?_⟩
    have h4 := congrArg (fun M : Matrix (Fin 2) (Fin 2) F => M * (((u : F)⁻¹) • (1 : Matrix (Fin 2) (Fin 2) F))) hu'
    simp only [Matrix.mul_assoc, Matrix.smul_mul, Matrix.one_mul, smul_smul,
      mul_inv_cancel₀ u.ne_zero, one_smul, Matrix.mul_one] at h4
    rw [h4, Matrix.mul_smul, Matrix.mul_one]
  · rintro ⟨a, ha, h⟩
    exact mk_eq_of_eq_smul X G ha h

/-- The fibre of `GL(2,F) → PGL(2,F)` through `G`, up to conjugating `G` to `±G`. -/
theorem MkConjEq {F : Type*} [Field F] (h G : Matrix.GeneralLinearGroup (Fin 2) F) :
    Matrix.ProjGenLinGroup.mk (h * G * h⁻¹) = Matrix.ProjGenLinGroup.mk G ↔
      ((h * G * h⁻¹ : Matrix.GeneralLinearGroup (Fin 2) F) : Matrix (Fin 2) (Fin 2) F) =
        ((G : Matrix.GeneralLinearGroup (Fin 2) F) : Matrix (Fin 2) (Fin 2) F) ∨
      ((h * G * h⁻¹ : Matrix.GeneralLinearGroup (Fin 2) F) : Matrix (Fin 2) (Fin 2) F) =
        -((G : Matrix.GeneralLinearGroup (Fin 2) F) : Matrix (Fin 2) (Fin 2) F) := by
  set X : Matrix.GeneralLinearGroup (Fin 2) F := h * G * h⁻¹ with hX
  constructor
  · intro hmk
    obtain ⟨a, ha, hXa⟩ := (mk_eq_mk_iff_eq_smul X G).mp hmk
    have hdetX : (X : Matrix (Fin 2) (Fin 2) F).det = (G : Matrix (Fin 2) (Fin 2) F).det := by
      have h2 : Matrix.GeneralLinearGroup.det X = Matrix.GeneralLinearGroup.det G := by
        rw [hX, map_mul, map_mul, map_inv,
          mul_comm (Matrix.GeneralLinearGroup.det h) (Matrix.GeneralLinearGroup.det G),
          mul_assoc, mul_inv_cancel, mul_one]
      have h3 := congrArg (fun u : Fˣ => (u : F)) h2
      rwa [Matrix.GeneralLinearGroup.val_det_apply, Matrix.GeneralLinearGroup.val_det_apply] at h3
    have hd0 : (G : Matrix (Fin 2) (Fin 2) F).det ≠ 0 := by
      have hh := (Matrix.GeneralLinearGroup.det G).ne_zero
      rwa [Matrix.GeneralLinearGroup.val_det_apply] at hh
    have ha2 : a ^ 2 = 1 := by
      have h1 : a ^ 2 * (G : Matrix (Fin 2) (Fin 2) F).det =
          (X : Matrix (Fin 2) (Fin 2) F).det := by
        rw [hXa, Matrix.det_smul, Fintype.card_fin]
      have hd : a ^ 2 * (G : Matrix (Fin 2) (Fin 2) F).det =
          (G : Matrix (Fin 2) (Fin 2) F).det := by rw [h1, hdetX]
      exact mul_right_cancel₀ hd0 (by rw [one_mul]; exact hd)
    rcases sq_eq_one_iff.mp ha2 with h1 | h1
    · left; rw [hXa, h1, one_smul]
    · right; rw [hXa, h1]; simp
  · rintro (hXG | hXG)
    · exact congrArg Matrix.ProjGenLinGroup.mk (Units.ext hXG)
    · have hXeq : X = Matrix.GeneralLinearGroup.scalar (Fin 2) (-1 : Fˣ) * G := by
        apply Units.ext
        rw [hXG, Matrix.GeneralLinearGroup.coe_mul, coe_scalar_eq_smul, Matrix.smul_mul,
          Matrix.one_mul]
        simp
      rw [hXeq, map_mul, Matrix.ProjGenLinGroup.mk_scalar, one_mul]


/-- The image of a conjugate of `G` in `PGL` is `t` (with `mk G = t`) iff the conjugate is `±G`. -/
theorem mem_comap_centralizer_iff {F : Type*} [Field F]
    (G : Matrix.GeneralLinearGroup (Fin 2) F) (t : Matrix.ProjGenLinGroup (Fin 2) F)
    (hG : Matrix.ProjGenLinGroup.mk G = t) (h : Matrix.GeneralLinearGroup (Fin 2) F) :
    h ∈ (Subgroup.centralizer ({t} : Set (Matrix.ProjGenLinGroup (Fin 2) F))).comap
          Matrix.ProjGenLinGroup.mk ↔
      ((h * G * h⁻¹ : Matrix.GeneralLinearGroup (Fin 2) F) : Matrix (Fin 2) (Fin 2) F) =
        (G : Matrix (Fin 2) (Fin 2) F) ∨
      ((h * G * h⁻¹ : Matrix.GeneralLinearGroup (Fin 2) F) : Matrix (Fin 2) (Fin 2) F) =
        -(G : Matrix (Fin 2) (Fin 2) F) := by
  rw [Subgroup.mem_comap, Subgroup.mem_centralizer_iff]
  simp only [Set.mem_singleton_iff, forall_eq]
  have key : (t * Matrix.ProjGenLinGroup.mk h = Matrix.ProjGenLinGroup.mk h * t) ↔
      (Matrix.ProjGenLinGroup.mk (h * G * h⁻¹) = Matrix.ProjGenLinGroup.mk G) := by
    have e1 : (t * Matrix.ProjGenLinGroup.mk h = Matrix.ProjGenLinGroup.mk h * t) ↔
        (Matrix.ProjGenLinGroup.mk h * t * (Matrix.ProjGenLinGroup.mk h)⁻¹ = t) := by
      constructor
      · intro hh; rw [← hh]; group
      · intro hh
        calc t * Matrix.ProjGenLinGroup.mk h
            = (Matrix.ProjGenLinGroup.mk h * t * (Matrix.ProjGenLinGroup.mk h)⁻¹) *
                Matrix.ProjGenLinGroup.mk h := by rw [hh]
          _ = Matrix.ProjGenLinGroup.mk h * t := by group
    have e2 : (Matrix.ProjGenLinGroup.mk h * t * (Matrix.ProjGenLinGroup.mk h)⁻¹ = t) ↔
        (Matrix.ProjGenLinGroup.mk (h * G * h⁻¹) = Matrix.ProjGenLinGroup.mk G) := by
      rw [← hG]
      simp only [map_mul, map_inv]
    rw [e1, e2]
  rw [key, MkConjEq]


/-- **An inverting element for a traceless `G` with `G ^ 2 = D • 1`.** -/
theorem ExistsConjNeg {F : Type*} [Field F] (h2 : (2 : F) ≠ 0)
    (G : Matrix.GeneralLinearGroup (Fin 2) F) (D : F) (hD : D ≠ 0)
    (hG2 : (G : Matrix (Fin 2) (Fin 2) F) * (G : Matrix (Fin 2) (Fin 2) F) = D • 1)
    (htr : (G : Matrix (Fin 2) (Fin 2) F).trace = 0)
    (hns : ¬ ∃ c : F, (G : Matrix (Fin 2) (Fin 2) F) = c • 1) :
    ∃ u : Matrix.GeneralLinearGroup (Fin 2) F,
      (u : Matrix (Fin 2) (Fin 2) F) * (G : Matrix (Fin 2) (Fin 2) F) =
        -((G : Matrix (Fin 2) (Fin 2) F) * (u : Matrix (Fin 2) (Fin 2) F)) := by
  have h11 : (G : Matrix (Fin 2) (Fin 2) F) 1 1 = - (G : Matrix (Fin 2) (Fin 2) F) 0 0 := by
    have h := htr
    rw [Matrix.trace_fin_two] at h
    exact eq_neg_of_add_eq_zero_right h
  obtain ⟨p, q, r, hGmat⟩ : ∃ p q r : F,
      (G : Matrix (Fin 2) (Fin 2) F) = !![p, q; r, -p] := by
    refine ⟨(G : Matrix (Fin 2) (Fin 2) F) 0 0, (G : Matrix (Fin 2) (Fin 2) F) 0 1,
      (G : Matrix (Fin 2) (Fin 2) F) 1 0, ?_⟩
    ext i j
    fin_cases i <;> fin_cases j <;> simp [h11]
  rw [hGmat]
  by_cases hr : r = 0
  · by_cases hq : q = 0
    · refine ⟨Matrix.GeneralLinearGroup.mkOfDetNeZero !![(0 : F), 1; 1, 0]
        (by rw [Matrix.det_fin_two_of]; simp), ?_⟩
      rw [Matrix.GeneralLinearGroup.val_mkOfDetNeZero]
      ext i j
      fin_cases i <;> fin_cases j <;>
        simp [Matrix.mul_apply, Fin.sum_univ_two, Matrix.neg_apply, hr, hq]
    · refine ⟨Matrix.GeneralLinearGroup.mkOfDetNeZero !![q, 0; -2 * p, -q]
        (by rw [Matrix.det_fin_two_of]; simpa using neg_ne_zero.mpr (mul_ne_zero hq hq)), ?_⟩
      rw [Matrix.GeneralLinearGroup.val_mkOfDetNeZero]
      ext i j
      fin_cases i <;> fin_cases j <;>
        simp [Matrix.mul_apply, Fin.sum_univ_two, Matrix.neg_apply, hr, hq] <;> ring
  · refine ⟨Matrix.GeneralLinearGroup.mkOfDetNeZero !![r, -2 * p; 0, -r]
      (by rw [Matrix.det_fin_two_of]; simpa using neg_ne_zero.mpr (mul_ne_zero hr hr)), ?_⟩
    rw [Matrix.GeneralLinearGroup.val_mkOfDetNeZero]
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [Matrix.mul_apply, Fin.sum_univ_two, Matrix.neg_apply, hr] <;> ring


/-- The number of `(a,b)` with `a^2 - D b^2 ≠ 0` when `D = s^2` is a square. -/
theorem NcardSqSubSqSq {F : Type*} [Field F] [Fintype F] (h2 : (2 : F) ≠ 0)
    (D : F) (hD : D ≠ 0) (hs : ∃ s : F, s ^ 2 = D) :
    Nat.card {x : F × F // x.1 ^ 2 - D * x.2 ^ 2 ≠ 0} = (Nat.card F - 1) ^ 2 := by
  classical
  obtain ⟨s, hs⟩ := hs
  have hs0 : s ≠ 0 := by
    rintro rfl; rw [pow_two, zero_mul] at hs; exact hD hs.symm
  have hbij : Nat.card {x : F × F // x.1 ^ 2 - D * x.2 ^ 2 ≠ 0} =
      Nat.card {y : F × F // y.1 * y.2 ≠ 0} := by
    refine Nat.card_congr (Equiv.subtypeEquiv
      { toFun := fun x : F × F => (x.1 - s * x.2, x.1 + s * x.2)
        invFun := fun y : F × F => ((y.1 + y.2) / 2, (y.2 - y.1) / (2 * s))
        left_inv := ?_
        right_inv := ?_ } ?_)
    · rintro ⟨a, b⟩
      simp only [Prod.mk.injEq]
      refine ⟨?_, ?_⟩
      · rw [show a - s * b + (a + s * b) = 2 * a from by ring, mul_div_cancel_left₀ _ h2]
      · rw [show a + s * b - (a - s * b) = (2 * s) * b from by ring,
          mul_div_cancel_left₀ _ (mul_ne_zero h2 hs0)]
    · rintro ⟨a, b⟩
      simp only [Prod.mk.injEq]
      refine ⟨?_, ?_⟩ <;> · field_simp; ring
    · intro x
      show x.1 ^ 2 - D * x.2 ^ 2 ≠ 0 ↔ (x.1 - s * x.2) * (x.1 + s * x.2) ≠ 0
      have h : x.1 ^ 2 - D * x.2 ^ 2 = (x.1 - s * x.2) * (x.1 + s * x.2) := by
        rw [← hs]; ring
      rw [h]
  rw [hbij]
  have h1 : Nat.card {y : F × F // y.1 * y.2 ≠ 0} = Nat.card Fˣ * Nat.card Fˣ := by
    have e : {y : F × F // y.1 * y.2 ≠ 0} ≃ Fˣ × Fˣ :=
    { toFun := fun y : {z : F × F // z.1 * z.2 ≠ 0} =>
        (Units.mk0 y.1.1 (left_ne_zero_of_mul y.2), Units.mk0 y.1.2 (right_ne_zero_of_mul y.2))
      invFun := fun u : Fˣ × Fˣ => ⟨(u.1, u.2), mul_ne_zero u.1.ne_zero u.2.ne_zero⟩
      left_inv := by
        rintro ⟨⟨a, b⟩, hab⟩
        apply Subtype.ext
        simp [Units.val_mk0]
      right_inv := by
        rintro ⟨u, v⟩
        apply Prod.ext <;> apply Units.ext <;> simp [Units.val_mk0] }
    rw [Nat.card_congr e, Nat.card_prod]
  rw [h1, Nat.card_units F, pow_two]

/-- The number of `(a,b)` with `a^2 - D b^2 ≠ 0` when `D` is a nonsquare. -/
theorem NcardSqSubSqNonSq {F : Type*} [Field F] [Fintype F] (h2 : (2 : F) ≠ 0)
    (D : F) (hD : D ≠ 0) (hs : ¬ ∃ s : F, s ^ 2 = D) :
    Nat.card {x : F × F // x.1 ^ 2 - D * x.2 ^ 2 ≠ 0} = Nat.card F ^ 2 - 1 := by
  classical
  have key : ∀ x : F × F, x.1 ^ 2 - D * x.2 ^ 2 ≠ 0 ↔ x ≠ 0 := by
    intro x
    constructor
    · intro h hx; exact h (by rw [hx]; simp)
    · intro hx h0
      apply hx
      have h1 : x.1 ^ 2 = D * x.2 ^ 2 := by linear_combination h0
      by_cases hx2 : x.2 = 0
      · have hx1 : x.1 = 0 := by
          have hh := h1
          rw [hx2] at hh
          simp at hh
          exact hh
        exact Prod.ext hx1 hx2
      · exfalso
        apply hs
        refine ⟨x.1 / x.2, ?_⟩
        rw [div_pow, div_eq_iff (pow_ne_zero 2 hx2)]
        exact h1
  rw [Nat.card_congr (Equiv.subtypeEquivRight key)]
  rw [Nat.card_eq_fintype_card, Fintype.card_subtype_compl (fun x : F × F => x = 0)]
  have hzero : Fintype.card {x : F × F // x = 0} = 1 :=
    Fintype.card_eq_one_iff.mpr ⟨⟨0, rfl⟩, fun y => Subtype.ext y.2⟩
  rw [hzero, Fintype.card_prod, Nat.card_eq_fintype_card (α := F), pow_two]


/-- The centralizer in `GL(2,F)` of a traceless `G` with `G ^ 2 = D • 1` is in bijection with
the set of `(a,b)` with `a^2 - D b^2 ≠ 0`. -/
theorem CentGLEqSet {F : Type*} [Field F] [Fintype F] (h2 : (2 : F) ≠ 0)
    (G : Matrix.GeneralLinearGroup (Fin 2) F) (D : F) (hD : D ≠ 0)
    (hG2 : (G : Matrix (Fin 2) (Fin 2) F) * (G : Matrix (Fin 2) (Fin 2) F) = D • 1)
    (htr : (G : Matrix (Fin 2) (Fin 2) F).trace = 0)
    (hns : ¬ ∃ c : F, (G : Matrix (Fin 2) (Fin 2) F) = c • 1) :
    Nat.card (Subgroup.centralizer ({G} : Set (Matrix.GeneralLinearGroup (Fin 2) F))) =
      Nat.card {x : F × F // x.1 ^ 2 - D * x.2 ^ 2 ≠ 0} := by
  classical
  have hdetG : (G : Matrix (Fin 2) (Fin 2) F).det = -D := by
    have hCH := Work.L2F.Mat2.sq_eq_trace_smul_sub_det F (G : Matrix (Fin 2) (Fin 2) F)
    rw [hG2, htr, zero_smul, zero_sub] at hCH
    have h := congrArg (fun M : Matrix (Fin 2) (Fin 2) F => M 0 0) hCH
    simp at h
    have h2 : (G : Matrix (Fin 2) (Fin 2) F).det + D = 0 := by rw [h]; ring
    exact eq_neg_of_add_eq_zero_left h2
  have hdetfun : ∀ a b : F, (a • (1 : Matrix (Fin 2) (Fin 2) F) +
      b • (G : Matrix (Fin 2) (Fin 2) F)).det = a ^ 2 - D * b ^ 2 := by
    intro a b
    rw [Work.L2F.Mat2.det_smul_one_add_smul F (G : Matrix (Fin 2) (Fin 2) F) a b, htr, hdetG]
    ring
  have hcomm : ∀ a b : F, (a • (1 : Matrix (Fin 2) (Fin 2) F) +
      b • (G : Matrix (Fin 2) (Fin 2) F)) * (G : Matrix (Fin 2) (Fin 2) F) =
      (G : Matrix (Fin 2) (Fin 2) F) * (a • (1 : Matrix (Fin 2) (Fin 2) F) +
        b • (G : Matrix (Fin 2) (Fin 2) F)) := by
    intro a b
    simp only [Matrix.add_mul, Matrix.mul_add, Matrix.smul_mul, Matrix.mul_smul, Matrix.one_mul,
      Matrix.mul_one, hG2]
  have hmem : ∀ x : {x : F × F // x.1 ^ 2 - D * x.2 ^ 2 ≠ 0},
      (Matrix.GeneralLinearGroup.mkOfDetNeZero
        (x.1.1 • (1 : Matrix (Fin 2) (Fin 2) F) + x.1.2 • (G : Matrix (Fin 2) (Fin 2) F))
        (by rw [hdetfun]; exact x.2) : Matrix.GeneralLinearGroup (Fin 2) F) ∈
      Subgroup.centralizer ({G} : Set (Matrix.GeneralLinearGroup (Fin 2) F)) := by
    intro x
    rw [Subgroup.mem_centralizer_iff]
    intro y hy
    rw [Set.mem_singleton_iff] at hy
    rw [hy]
    apply Units.ext
    rw [Matrix.GeneralLinearGroup.coe_mul, Matrix.GeneralLinearGroup.coe_mul,
      Matrix.GeneralLinearGroup.val_mkOfDetNeZero]
    exact (hcomm x.1.1 x.1.2).symm
  refine (Nat.card_congr ?_).symm
  refine Equiv.ofBijective (fun x => (⟨Matrix.GeneralLinearGroup.mkOfDetNeZero
      (x.1.1 • (1 : Matrix (Fin 2) (Fin 2) F) + x.1.2 • (G : Matrix (Fin 2) (Fin 2) F))
      (by rw [hdetfun]; exact x.2), hmem x⟩ :
        Subgroup.centralizer ({G} : Set (Matrix.GeneralLinearGroup (Fin 2) F)))) ⟨?_, ?_⟩
  · rintro x y hxy
    have h1 : Matrix.GeneralLinearGroup.mkOfDetNeZero
        (x.1.1 • (1 : Matrix (Fin 2) (Fin 2) F) + x.1.2 • (G : Matrix (Fin 2) (Fin 2) F))
        (by rw [hdetfun]; exact x.2) =
        Matrix.GeneralLinearGroup.mkOfDetNeZero
        (y.1.1 • (1 : Matrix (Fin 2) (Fin 2) F) + y.1.2 • (G : Matrix (Fin 2) (Fin 2) F))
        (by rw [hdetfun]; exact y.2) := congrArg Subtype.val hxy
    have h2 : x.1.1 • (1 : Matrix (Fin 2) (Fin 2) F) + x.1.2 • (G : Matrix (Fin 2) (Fin 2) F) =
        y.1.1 • (1 : Matrix (Fin 2) (Fin 2) F) + y.1.2 • (G : Matrix (Fin 2) (Fin 2) F) := by
      have := congrArg (fun t : Matrix.GeneralLinearGroup (Fin 2) F =>
        (t : Matrix (Fin 2) (Fin 2) F)) h1
      rwa [Matrix.GeneralLinearGroup.val_mkOfDetNeZero,
        Matrix.GeneralLinearGroup.val_mkOfDetNeZero] at this
    have h3 : (x.1.1 - y.1.1) • (1 : Matrix (Fin 2) (Fin 2) F) +
        (x.1.2 - y.1.2) • (G : Matrix (Fin 2) (Fin 2) F) = 0 := by
      have h4 : (x.1.1 - y.1.1) • (1 : Matrix (Fin 2) (Fin 2) F) +
          (x.1.2 - y.1.2) • (G : Matrix (Fin 2) (Fin 2) F) =
          (x.1.1 • (1 : Matrix (Fin 2) (Fin 2) F) + x.1.2 • (G : Matrix (Fin 2) (Fin 2) F)) -
          (y.1.1 • (1 : Matrix (Fin 2) (Fin 2) F) + y.1.2 • (G : Matrix (Fin 2) (Fin 2) F)) := by
        rw [sub_smul, sub_smul]; abel
      rw [h4, h2, sub_self]
    have hns' : ∀ c : F, (G : Matrix (Fin 2) (Fin 2) F) ≠ c • 1 := fun c => by
      rintro h; exact hns ⟨c, h⟩
    obtain ⟨h31, h32⟩ := Work.L2F.Torus.algSpan_eq_zero F hns' (x.1.1 - y.1.1) (x.1.2 - y.1.2) h3
    exact Subtype.ext (Prod.ext (sub_eq_zero.mp h31) (sub_eq_zero.mp h32))
  · intro h
    have hcomm' : (h : Matrix.GeneralLinearGroup (Fin 2) F) * (G : Matrix (Fin 2) (Fin 2) F) =
        (G : Matrix (Fin 2) (Fin 2) F) * (h : Matrix.GeneralLinearGroup (Fin 2) F) := by
      have h1 := (Subgroup.mem_centralizer_iff.mp h.2) G (by simp)
      have h2 := congrArg (fun t : Matrix.GeneralLinearGroup (Fin 2) F =>
        (t : Matrix (Fin 2) (Fin 2) F)) h1
      simp only [Matrix.GeneralLinearGroup.coe_mul] at h2
      exact h2.symm
    obtain ⟨a, b, hab⟩ := (Work.L2F.Torus.commute_iff_mem_algSpan F h2
      (G : Matrix (Fin 2) (Fin 2) F) (h : Matrix.GeneralLinearGroup (Fin 2) F) D htr hG2 hD).mp hcomm'
    have habne : a ^ 2 - D * b ^ 2 ≠ 0 := by
      have hh : ((h : Matrix.GeneralLinearGroup (Fin 2) F) :
          Matrix (Fin 2) (Fin 2) F).det ≠ 0 := by
        have hh := (Matrix.GeneralLinearGroup.det (h : Matrix.GeneralLinearGroup (Fin 2) F)).ne_zero
        rwa [Matrix.GeneralLinearGroup.val_det_apply] at hh
      rw [hab, hdetfun a b] at hh
      exact hh
    refine ⟨⟨(a, b), habne⟩, ?_⟩
    apply Subtype.ext
    apply Units.ext
    rw [Matrix.GeneralLinearGroup.val_mkOfDetNeZero]
    exact hab.symm


/-- If a finite subgroup `K` is the disjoint union of `C₀` and a left translate `C₁ = u • C₀`,
then `|K| = 2 |C₀|`. -/
theorem TwoMulUnionTranslate {G : Type*} [Group G] [Finite G] (K C₀ : Subgroup G)
    (C₁ : Set G) (u : G)
    (hK : ∀ h : G, h ∈ K ↔ h ∈ C₀ ∨ h ∈ C₁)
    (hdisj : Disjoint (C₀ : Set G) C₁)
    (hC1 : ∀ h : G, h ∈ C₁ ↔ u⁻¹ * h ∈ C₀) :
    Nat.card K = 2 * Nat.card C₀ := by
  classical
  have hKset : (K : Set G) = (C₀ : Set G) ∪ C₁ := by
    ext h; rw [Set.mem_union]; exact hK h
  have hC1n : C₁.ncard = (C₀ : Set G).ncard := by
    refine Set.ncard_congr (fun h _ => u⁻¹ * h) ?_ ?_ ?_
    · intro h hh; exact (hC1 h).mp hh
    · intro a b ha hb hab
      have := congrArg (fun t => u * t) hab
      simpa [mul_assoc] using this
    · intro b hb
      exact ⟨u * b, (hC1 (u * b)).mpr (by simpa [mul_assoc] using hb), by simp [mul_assoc]⟩
  change Nat.card ↥(K : Set G) = 2 * Nat.card ↥(C₀ : Set G)
  calc Nat.card ↥(K : Set G) = (K : Set G).ncard := Nat.card_coe_set_eq _
    _ = ((C₀ : Set G) ∪ C₁).ncard := by rw [hKset]
    _ = (C₀ : Set G).ncard + C₁.ncard := Set.ncard_union_eq hdisj
    _ = (C₀ : Set G).ncard + (C₀ : Set G).ncard := by rw [hC1n]
    _ = 2 * Nat.card ↥(C₀ : Set G) := by rw [Nat.card_coe_set_eq]; ring


/-! ## `-1` in `GL(2,F)` and its basic properties -/

/-- The matrix `-1` as an element of `GL(2,F)`. -/
def negOneGL (F : Type*) [Field F] : Matrix.GeneralLinearGroup (Fin 2) F :=
  Matrix.GeneralLinearGroup.mkOfDetNeZero (-(1 : Matrix (Fin 2) (Fin 2) F))
    (by
      have h : (-(1 : Matrix (Fin 2) (Fin 2) F)).det = 1 := by
        rw [Matrix.det_neg, Fintype.card_fin, Matrix.det_one]; ring
      rw [h]; exact one_ne_zero)

@[simp]
theorem negOneGL_apply (F : Type*) [Field F] :
    ((negOneGL F : Matrix.GeneralLinearGroup (Fin 2) F) : Matrix (Fin 2) (Fin 2) F) = -1 :=
  Matrix.GeneralLinearGroup.val_mkOfDetNeZero _ _

theorem negOneGL_mul_self (F : Type*) [Field F] : negOneGL F * negOneGL F = 1 := by
  apply Units.ext
  rw [Matrix.GeneralLinearGroup.coe_mul, negOneGL_apply, Matrix.neg_mul, Matrix.one_mul,
    neg_neg, Matrix.GeneralLinearGroup.coe_one]

theorem negOneGL_comm (F : Type*) [Field F] (A : Matrix.GeneralLinearGroup (Fin 2) F) :
    negOneGL F * A = A * negOneGL F := by
  apply Units.ext
  rw [Matrix.GeneralLinearGroup.coe_mul, Matrix.GeneralLinearGroup.coe_mul, negOneGL_apply,
    Matrix.neg_mul, Matrix.one_mul, Matrix.mul_neg, Matrix.mul_one]

/-- Membership in `{h | h * G * h⁻¹ = -G}` in matrix form. -/
lemma conj_eq_negOneGL_iff {F : Type*} [Field F] (h G : Matrix.GeneralLinearGroup (Fin 2) F) :
    h * G * h⁻¹ = negOneGL F * G ↔
      ((h * G * h⁻¹ : Matrix.GeneralLinearGroup (Fin 2) F) : Matrix (Fin 2) (Fin 2) F) =
        -(G : Matrix (Fin 2) (Fin 2) F) := by
  constructor
  · intro hx
    rw [hx, Matrix.GeneralLinearGroup.coe_mul, negOneGL_apply, Matrix.neg_mul, Matrix.one_mul]
  · intro hx
    apply Units.ext
    rw [hx, Matrix.GeneralLinearGroup.coe_mul, negOneGL_apply, Matrix.neg_mul, Matrix.one_mul]

/-- Membership of `w` in the centralizer of `G`, in terms of conjugating `G` by `w`. -/
lemma mem_centralizer_iff_conj {F : Type*} [Field F] (G w : Matrix.GeneralLinearGroup (Fin 2) F) :
    w ∈ Subgroup.centralizer ({G} : Set (Matrix.GeneralLinearGroup (Fin 2) F)) ↔
      (w : Matrix (Fin 2) (Fin 2) F) * (G : Matrix (Fin 2) (Fin 2) F) *
        ((w⁻¹ : Matrix.GeneralLinearGroup (Fin 2) F) : Matrix (Fin 2) (Fin 2) F) =
        (G : Matrix (Fin 2) (Fin 2) F) := by
  have hw1 : (w : Matrix (Fin 2) (Fin 2) F) *
      ((w⁻¹ : Matrix.GeneralLinearGroup (Fin 2) F) : Matrix (Fin 2) (Fin 2) F) = 1 := by
    have := congrArg (fun t : Matrix.GeneralLinearGroup (Fin 2) F =>
      (t : Matrix (Fin 2) (Fin 2) F)) (mul_inv_cancel w)
    rwa [Matrix.GeneralLinearGroup.coe_mul, Matrix.GeneralLinearGroup.coe_one] at this
  have hw2 : ((w⁻¹ : Matrix.GeneralLinearGroup (Fin 2) F) : Matrix (Fin 2) (Fin 2) F) *
      (w : Matrix (Fin 2) (Fin 2) F) = 1 := by
    have := congrArg (fun t : Matrix.GeneralLinearGroup (Fin 2) F =>
      (t : Matrix (Fin 2) (Fin 2) F)) (inv_mul_cancel w)
    rwa [Matrix.GeneralLinearGroup.coe_mul, Matrix.GeneralLinearGroup.coe_one] at this
  rw [Subgroup.mem_centralizer_iff]
  constructor
  · intro h
    have h3 := congrArg (fun t : Matrix.GeneralLinearGroup (Fin 2) F =>
      (t : Matrix (Fin 2) (Fin 2) F)) (h G (by simp))
    simp only [Matrix.GeneralLinearGroup.coe_mul] at h3
    calc (w : Matrix (Fin 2) (Fin 2) F) * (G : Matrix (Fin 2) (Fin 2) F) *
          ((w⁻¹ : Matrix.GeneralLinearGroup (Fin 2) F) : Matrix (Fin 2) (Fin 2) F)
        = (G : Matrix (Fin 2) (Fin 2) F) * (w : Matrix (Fin 2) (Fin 2) F) *
          ((w⁻¹ : Matrix.GeneralLinearGroup (Fin 2) F) : Matrix (Fin 2) (Fin 2) F) := by
          rw [← h3]
      _ = (G : Matrix (Fin 2) (Fin 2) F) * ((w : Matrix (Fin 2) (Fin 2) F) *
          ((w⁻¹ : Matrix.GeneralLinearGroup (Fin 2) F) : Matrix (Fin 2) (Fin 2) F)) := by
          rw [Matrix.mul_assoc]
      _ = (G : Matrix (Fin 2) (Fin 2) F) := by rw [hw1, Matrix.mul_one]
  · intro h
    intro y hy
    rw [Set.mem_singleton_iff] at hy
    rw [hy]
    apply Units.ext
    simp only [Matrix.GeneralLinearGroup.coe_mul]
    calc (G : Matrix (Fin 2) (Fin 2) F) * (w : Matrix (Fin 2) (Fin 2) F)
        = (w : Matrix (Fin 2) (Fin 2) F) * (G : Matrix (Fin 2) (Fin 2) F) *
          ((w⁻¹ : Matrix.GeneralLinearGroup (Fin 2) F) : Matrix (Fin 2) (Fin 2) F) *
          (w : Matrix (Fin 2) (Fin 2) F) := by rw [h]
      _ = (w : Matrix (Fin 2) (Fin 2) F) * (G : Matrix (Fin 2) (Fin 2) F) := by
          rw [show (w : Matrix (Fin 2) (Fin 2) F) * (G : Matrix (Fin 2) (Fin 2) F) *
              ((w⁻¹ : Matrix.GeneralLinearGroup (Fin 2) F) : Matrix (Fin 2) (Fin 2) F) *
              (w : Matrix (Fin 2) (Fin 2) F) =
              (w : Matrix (Fin 2) (Fin 2) F) * (G : Matrix (Fin 2) (Fin 2) F) *
              (((w⁻¹ : Matrix.GeneralLinearGroup (Fin 2) F) : Matrix (Fin 2) (Fin 2) F) *
              (w : Matrix (Fin 2) (Fin 2) F)) from by noncomm_ring,
            hw2, Matrix.mul_one]

/-- The centre of `GL(2,F)` for a finite field `F` has `|F| - 1` elements. -/
theorem centerGL_card (F : Type*) [Field F] [Fintype F] :
    Nat.card (Subgroup.center (Matrix.GeneralLinearGroup (Fin 2) F)) = Nat.card F - 1 := by
  have hinj : Function.Injective
      (Matrix.GeneralLinearGroup.scalar (Fin 2) :
        Fˣ → Matrix.GeneralLinearGroup (Fin 2) F) := by
    intro u v huv
    have h := congrArg (fun t : Matrix.GeneralLinearGroup (Fin 2) F =>
      (t : Matrix (Fin 2) (Fin 2) F) 0 0) huv
    refine Units.ext ?_
    simpa [Matrix.GeneralLinearGroup.coe_scalar, Matrix.scalar_apply] using h
  rw [Matrix.GeneralLinearGroup.center_eq_range_scalar, ← Subgroup.map_top]
  rw [Subgroup.card_map_of_injective hinj]
  rw [Nat.card_congr (Subgroup.topEquiv (G := Fˣ)).toEquiv, Nat.card_units F]


/-- Membership of `w` in the centralizer of `G`, in terms of conjugating `G` by `w`. -/
lemma mem_centralizer_iff_conj_GL {F : Type*} [Field F] (G w : Matrix.GeneralLinearGroup (Fin 2) F) :
    w ∈ Subgroup.centralizer ({G} : Set (Matrix.GeneralLinearGroup (Fin 2) F)) ↔
      w * G * w⁻¹ = G := by
  rw [mem_centralizer_iff_conj G w]
  constructor
  · intro h
    refine Units.ext ?_
    simpa only [Matrix.GeneralLinearGroup.coe_mul] using h
  · intro h
    have := congrArg (fun t : Matrix.GeneralLinearGroup (Fin 2) F =>
      (t : Matrix (Fin 2) (Fin 2) F)) h
    simpa only [Matrix.GeneralLinearGroup.coe_mul] using this

/-- **The centralizer of an involution of `PGL(2,F)` has order `2(q-1)` or `2(q+1)`.** -/
theorem pgl_involution_centralizer_card (F : Type*) [Field F] [Fintype F] (h2 : (2 : F) ≠ 0)
    (t : Matrix.ProjGenLinGroup (Fin 2) F) (ht : orderOf t = 2) :
    Nat.card (Subgroup.centralizer ({t} : Set (Matrix.ProjGenLinGroup (Fin 2) F))) =
        2 * (Nat.card F - 1) ∨
      Nat.card (Subgroup.centralizer ({t} : Set (Matrix.ProjGenLinGroup (Fin 2) F))) =
        2 * (Nat.card F + 1) := by
  classical
  obtain ⟨G, D, hD, hG, hG2, htr, hns⟩ := setup h2 t ht
  set C : Subgroup (Matrix.ProjGenLinGroup (Fin 2) F) :=
    Subgroup.centralizer ({t} : Set (Matrix.ProjGenLinGroup (Fin 2) F)) with hCdef
  set K : Subgroup (Matrix.GeneralLinearGroup (Fin 2) F) :=
    C.comap Matrix.ProjGenLinGroup.mk with hKdef
  have hKmap : K.map Matrix.ProjGenLinGroup.mk = C := by
    rw [hKdef, hCdef, Subgroup.map_comap_eq,
      MonoidHom.range_eq_top_of_surjective _ Matrix.ProjGenLinGroup.mk_surjective]
    exact top_inf_eq C
  have hkerle : (Matrix.ProjGenLinGroup.mk :
      Matrix.GeneralLinearGroup (Fin 2) F →* Matrix.ProjGenLinGroup (Fin 2) F).ker ≤ K := by
    intro g hg
    rw [hKdef, Subgroup.mem_comap, MonoidHom.mem_ker.mp hg]
    exact C.one_mem
  have hcard1 : Nat.card K = Nat.card C * (Nat.card F - 1) := by
    rw [CardKerMap Matrix.ProjGenLinGroup.mk K hkerle, hKmap, Matrix.ProjGenLinGroup.ker_mk,
      centerGL_card]
  -- the inverting element
  obtain ⟨u, hu⟩ := ExistsConjNeg h2 G D hD hG2 htr hns
  have hmul_u : (u : Matrix (Fin 2) (Fin 2) F) *
      ((u⁻¹ : Matrix.GeneralLinearGroup (Fin 2) F) : Matrix (Fin 2) (Fin 2) F) = 1 := by
    have := congrArg (fun s : Matrix.GeneralLinearGroup (Fin 2) F =>
      (s : Matrix (Fin 2) (Fin 2) F)) (mul_inv_cancel u)
    rwa [Matrix.GeneralLinearGroup.coe_mul, Matrix.GeneralLinearGroup.coe_one] at this
  have huGL : u * G * u⁻¹ = negOneGL F * G := by
    apply Units.ext
    simp only [Matrix.GeneralLinearGroup.coe_mul, negOneGL_apply F, Matrix.neg_mul,
      Matrix.one_mul]
    calc (u : Matrix (Fin 2) (Fin 2) F) * (G : Matrix (Fin 2) (Fin 2) F) *
          ((u⁻¹ : Matrix.GeneralLinearGroup (Fin 2) F) : Matrix (Fin 2) (Fin 2) F)
        = -((G : Matrix (Fin 2) (Fin 2) F) * (u : Matrix (Fin 2) (Fin 2) F)) *
          ((u⁻¹ : Matrix.GeneralLinearGroup (Fin 2) F) : Matrix (Fin 2) (Fin 2) F) := by rw [hu]
      _ = -(((G : Matrix (Fin 2) (Fin 2) F) * (u : Matrix (Fin 2) (Fin 2) F)) *
          ((u⁻¹ : Matrix.GeneralLinearGroup (Fin 2) F) : Matrix (Fin 2) (Fin 2) F)) := by
          rw [Matrix.neg_mul]
      _ = -((G : Matrix (Fin 2) (Fin 2) F) * ((u : Matrix (Fin 2) (Fin 2) F) *
          ((u⁻¹ : Matrix.GeneralLinearGroup (Fin 2) F) : Matrix (Fin 2) (Fin 2) F))) := by
          rw [Matrix.mul_assoc]
      _ = -((G : Matrix (Fin 2) (Fin 2) F) * 1) := by rw [hmul_u]
      _ = -(G : Matrix (Fin 2) (Fin 2) F) := by rw [Matrix.mul_one]
  have huGLinv : u⁻¹ * G * u = negOneGL F * G := by
    have h1 : G = negOneGL F * (u⁻¹ * G * u) := by
      calc G = u⁻¹ * (u * G * u⁻¹) * u := by group
        _ = u⁻¹ * (negOneGL F * G) * u := by rw [huGL]
        _ = u⁻¹ * (G * negOneGL F) * u := by rw [negOneGL_comm F G]
        _ = (u⁻¹ * G * u) * negOneGL F := by
            have h2 : u⁻¹ * (G * negOneGL F) * u = (u⁻¹ * G) * (negOneGL F * u) := by
              noncomm_ring
            rw [h2, negOneGL_comm F u]
            noncomm_ring
        _ = negOneGL F * (u⁻¹ * G * u) := by rw [negOneGL_comm F (u⁻¹ * G * u)]
    calc u⁻¹ * G * u = (negOneGL F * negOneGL F) * (u⁻¹ * G * u) := by
          rw [negOneGL_mul_self F, one_mul]
      _ = negOneGL F * (negOneGL F * (u⁻¹ * G * u)) := by rw [mul_assoc]
      _ = negOneGL F * G := by rw [← h1]
  set C₀ : Subgroup (Matrix.GeneralLinearGroup (Fin 2) F) :=
    Subgroup.centralizer ({G} : Set (Matrix.GeneralLinearGroup (Fin 2) F)) with hC0def
  set C₁ : Set (Matrix.GeneralLinearGroup (Fin 2) F) :=
    {h | h * G * h⁻¹ = negOneGL F * G} with hC1def
  have hmemK : ∀ h : Matrix.GeneralLinearGroup (Fin 2) F, h ∈ K ↔ h ∈ C₀ ∨ h ∈ C₁ := by
    intro h
    have h1 := mem_comap_centralizer_iff G t hG h
    rw [← hCdef, ← hKdef] at h1
    rw [h1, hC0def, hC1def]
    simp only [Set.mem_setOf_eq]
    rw [mem_centralizer_iff_conj_GL G h]
    constructor
    · rintro (hx | hx)
      · left; exact Units.ext hx
      · right; exact (conj_eq_negOneGL_iff h G).mpr hx
    · rintro (hx | hx)
      · left
        have := congrArg (fun s : Matrix.GeneralLinearGroup (Fin 2) F =>
          (s : Matrix (Fin 2) (Fin 2) F)) hx
        simpa only [Matrix.GeneralLinearGroup.coe_mul] using this
      · right; exact (conj_eq_negOneGL_iff h G).mp hx
  have hGne : (G : Matrix.GeneralLinearGroup (Fin 2) F) ≠ negOneGL F * G := by
    intro hh
    have h := congrArg (fun s : Matrix.GeneralLinearGroup (Fin 2) F =>
      (s : Matrix (Fin 2) (Fin 2) F)) hh
    simp only [Matrix.GeneralLinearGroup.coe_mul, negOneGL_apply F, Matrix.neg_mul,
      Matrix.one_mul] at h
    have hsum : (G : Matrix (Fin 2) (Fin 2) F) + (G : Matrix (Fin 2) (Fin 2) F) = 0 := by
      nth_rewrite 1 [h]; rw [neg_add_cancel]
    have h2z : (2 : F) • (G : Matrix (Fin 2) (Fin 2) F) = 0 := by
      rw [two_smul]; exact hsum
    obtain ⟨i, j, hij⟩ : ∃ i j, (G : Matrix (Fin 2) (Fin 2) F) i j ≠ 0 := by
      by_contra hcon
      push_neg at hcon
      have hzero : (G : Matrix (Fin 2) (Fin 2) F) = 0 := by ext i j; exact hcon i j
      have hdet : (G : Matrix (Fin 2) (Fin 2) F).det ≠ 0 := by
        have hhh := (Matrix.GeneralLinearGroup.det G).ne_zero
        rwa [Matrix.GeneralLinearGroup.val_det_apply] at hhh
      rw [hzero, Matrix.det_zero] at hdet
      exact hdet rfl
    have hcontra := congrArg (fun M : Matrix (Fin 2) (Fin 2) F => M i j) h2z
    simp only [Matrix.smul_apply, smul_eq_mul, Matrix.zero_apply] at hcontra
    rcases mul_eq_zero.mp hcontra with hh2 | hh2
    · exact h2 hh2
    · exact hij hh2
  have hdisj : Disjoint (C₀ : Set (Matrix.GeneralLinearGroup (Fin 2) F)) C₁ := by
    refine Set.disjoint_left.mpr fun h h1 h2 => ?_
    have h2' : h * G * h⁻¹ = negOneGL F * G := h2
    rw [(mem_centralizer_iff_conj_GL G h).mp h1] at h2'
    exact hGne h2'
  have hC1t : ∀ h : Matrix.GeneralLinearGroup (Fin 2) F, h ∈ C₁ ↔ u⁻¹ * h ∈ C₀ := by
    intro h
    rw [hC1def]
    simp only [Set.mem_setOf_eq]
    rw [hC0def, mem_centralizer_iff_conj_GL G (u⁻¹ * h)]
    rw [show (u⁻¹ * h) * G * (u⁻¹ * h)⁻¹ = u⁻¹ * (h * G * h⁻¹) * u from by group]
    constructor
    · intro hx
      calc u⁻¹ * (h * G * h⁻¹) * u = u⁻¹ * (negOneGL F * G) * u := by rw [hx]
        _ = u⁻¹ * (G * negOneGL F) * u := by rw [negOneGL_comm F G]
        _ = (u⁻¹ * G * u) * negOneGL F := by
            have h2 : u⁻¹ * (G * negOneGL F) * u = (u⁻¹ * G) * (negOneGL F * u) := by
              noncomm_ring
            rw [h2, negOneGL_comm F u]
            noncomm_ring
        _ = (negOneGL F * G) * negOneGL F := by rw [huGLinv]
        _ = negOneGL F * (G * negOneGL F) := by group
        _ = negOneGL F * (negOneGL F * G) := by rw [negOneGL_comm F G]
        _ = (negOneGL F * negOneGL F) * G := by rw [mul_assoc]
        _ = G := by rw [negOneGL_mul_self F, one_mul]
    · intro hx
      calc h * G * h⁻¹ = u * (u⁻¹ * (h * G * h⁻¹) * u) * u⁻¹ := by group
        _ = u * G * u⁻¹ := by rw [hx]
        _ = negOneGL F * G := huGL
  have hcard2 : Nat.card K = 2 * Nat.card C₀ := TwoMulUnionTranslate K C₀ C₁ u hmemK hdisj hC1t
  have hcard3 : Nat.card C₀ = (Nat.card F - 1) ^ 2 ∨ Nat.card C₀ = Nat.card F ^ 2 - 1 := by
    rw [hC0def, CentGLEqSet h2 G D hD hG2 htr hns]
    by_cases hs : ∃ s : F, s ^ 2 = D
    · exact Or.inl (NcardSqSubSqSq h2 D hD hs)
    · exact Or.inr (NcardSqSubSqNonSq h2 D hD hs)
  have hmain : Nat.card C * (Nat.card F - 1) = 2 * Nat.card C₀ := by rw [← hcard1, hcard2]
  have hq : 0 < Nat.card F - 1 := by
    have h2q : 2 ≤ Nat.card F := by
      rw [Nat.card_eq_fintype_card]; exact Fintype.one_lt_card
    omega
  rcases hcard3 with h3 | h3
  · left
    have heq : Nat.card C * (Nat.card F - 1) =
        (2 * (Nat.card F - 1)) * (Nat.card F - 1) := by
      rw [hmain, h3, pow_two]; ring
    exact Nat.mul_right_cancel hq heq
  · right
    have h1q : 1 ≤ Nat.card F := by
      have h2q : 2 ≤ Nat.card F := by
        rw [Nat.card_eq_fintype_card]; exact Fintype.one_lt_card
      omega
    have hfac : Nat.card F ^ 2 - 1 = (Nat.card F + 1) * (Nat.card F - 1) := by
      rw [Nat.mul_sub_left_distrib, mul_one]
      have hsq : (Nat.card F + 1) * Nat.card F = Nat.card F ^ 2 + Nat.card F := by ring
      rw [hsq]
      omega
    have heq : Nat.card C * (Nat.card F - 1) =
        (2 * (Nat.card F + 1)) * (Nat.card F - 1) := by
      rw [hmain, h3, hfac]
      ring
    exact Nat.mul_right_cancel hq heq


/-- **`PGL(2,q)`, `q` odd: the centralizer of an involution has order `2(q∓1)`.** -/
theorem PGLInvCard {p k : ℕ} [Fact p.Prime] (hp : Odd p) (hk : 5 ≤ p ^ k)
    (t : PGL(2, GaloisField p k)) (ht : orderOf t = 2) :
    Nat.card (Subgroup.centralizer ({t} : Set (PGL(2, GaloisField p k)))) = 2 * (p ^ k - 1) ∨
      Nat.card (Subgroup.centralizer ({t} : Set (PGL(2, GaloisField p k)))) = 2 * (p ^ k + 1) := by
  haveI : Fintype (GaloisField p k) := Fintype.ofFinite (GaloisField p k)
  have hp2 : p ≠ 2 := by
    rintro rfl
    obtain ⟨m, hm⟩ := hp
    omega
  have h2 : (2 : GaloisField p k) ≠ 0 := by
    intro hc
    have hc' : ((2 : ℕ) : GaloisField p k) = 0 := by simpa using hc
    rw [CharP.cast_eq_zero_iff (GaloisField p k) p 2] at hc'
    have hple : p ≤ 2 := Nat.le_of_dvd (by norm_num) hc'
    have hpge : 2 ≤ p := (Fact.out : p.Prime).two_le
    exact hp2 (le_antisymm hple hpge)
  have hk0 : k ≠ 0 := by
    rintro rfl
    simp at hk
  have hcard : Nat.card (GaloisField p k) = p ^ k := GaloisField.card p k hk0
  rcases pgl_involution_centralizer_card (GaloisField p k) h2 t ht with h | h
  · left; rw [h, hcard]
  · right; rw [h, hcard]



end Work.DSTR.L2CentAux
