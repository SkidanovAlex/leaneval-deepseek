import Mathlib
import Submission.Work.L2F.Defs
import Submission.Work.L2F.Props.PGL2CommutatorTorusDefs
import Submission.Work.L2F.Props.centralizer_mk_eq
import Submission.Work.L2F.Mat2.sq_eq_trace_smul_sub_det
import Submission.Work.L2F.Semisimple.primeOrderCentralizer
import Submission.Work.L2F.Props.CentralizerTorusDefs
import Submission.Work.L2F.Props.glCent_algSpan
import Submission.Work.L2F.Props.glD_ne_zero
import Submission.Work.L2F.Props.rhoSL_mul
import Submission.Work.L2F.Props.rhoSL_mem_hypToSLHom_range
import Submission.Work.L2F.Props.exists_rhoSL_eq

open scoped MatrixGroups
open Matrix

namespace Work.L2F.Props

/-! ## Arithmetic of `q` and `m` -/

/-- A finite field of characteristic `≠ 2` has odd cardinality. -/
lemma odd_card_of_two_ne_zero (F : Type*) [Field F] [Fintype F] (h2 : (2 : F) ≠ 0) :
    Odd (Nat.card F) := by
  obtain ⟨p, hchar, n, hp, hcard⟩ := FiniteField.card' F
  have hp2 : p ≠ 2 := by
    rintro rfl
    exact h2 (CharP.cast_eq_zero F 2)
  have hodd : Odd p := hp.odd_of_ne_two hp2
  rw [Nat.card_eq_fintype_card, hcard]
  exact hodd.pow

/-- An odd number is `1` or `3` mod `4`. -/
lemma mod_four_of_odd (q : ℕ) (h : Odd q) : q % 4 = 1 ∨ q % 4 = 3 := by
  obtain ⟨k, hk⟩ := h; omega

/-- The number `m = (q+1)/2` (`q ≡ 1 mod 4`) or `(q-1)/2` (`q ≡ 3 mod 4`) is odd. -/
lemma odd_m_of_odd_card (q m : ℕ) (hoddq : Odd q)
    (hmdef : m = (if q % 4 = 1 then (q + 1) / 2 else (q - 1) / 2)) : Odd m := by
  subst hmdef
  rcases mod_four_of_odd q hoddq with h4 | h4
  · rw [if_pos h4]
    refine ⟨q / 4, ?_⟩
    have h : q = 4 * (q / 4) + 1 := by omega
    omega
  · rw [if_neg (by omega)]
    refine ⟨q / 4, ?_⟩
    have h : q = 4 * (q / 4) + 3 := by omega
    omega

/-- `2 m = q + 1` or `2 m = q - 1`. -/
lemma two_mul_m_eq (q m : ℕ) (hoddq : Odd q)
    (hmdef : m = (if q % 4 = 1 then (q + 1) / 2 else (q - 1) / 2)) :
    2 * m = q + 1 ∨ 2 * m = q - 1 := by
  subst hmdef
  rcases mod_four_of_odd q hoddq with h4 | h4
  · left
    rw [if_pos h4]
    exact Nat.mul_div_cancel' (by omega : 2 ∣ q + 1)
  · right
    rw [if_neg (by omega)]
    exact Nat.mul_div_cancel' (by omega : 2 ∣ q - 1)

/-- The integer `m` is nonzero in a field of characteristic `≠ 2` whose cardinality is `q`. -/
lemma m_ne_zero_char (F : Type*) [Field F] [Fintype F] {q m : ℕ} (hq : Nat.card F = q)
    (hoddq : Odd q) (hmdef : m = (if q % 4 = 1 then (q + 1) / 2 else (q - 1) / 2)) :
    (m : F) ≠ 0 := by
  have h1q : 1 ≤ q := by obtain ⟨k, hk⟩ := hoddq; omega
  have h2m := two_mul_m_eq q m hoddq hmdef
  have hqF : (q : F) = 0 := by
    rw [← hq, Nat.card_eq_fintype_card]
    exact Nat.cast_card_eq_zero F
  intro hm0
  have hzero : ((2 * m : ℕ) : F) = 0 := by rw [Nat.cast_mul, hm0, mul_zero]
  rcases h2m with h | h
  · rw [h, Nat.cast_add, Nat.cast_one, hqF, zero_add] at hzero
    exact one_ne_zero hzero
  · rw [h] at hzero
    have : ((q - 1 : ℕ) : F) = (q : F) - 1 := by
      rw [Nat.cast_sub h1q]; norm_num
    rw [this, hqF, zero_sub] at hzero
    exact one_ne_zero (neg_eq_zero.mp hzero)

/-- An element of order `m > 1`, `m` odd, is not an involution. -/
lemma sq_ne_one_of_orderOf {G : Type*} [Group G] (x : G) {m : ℕ} (hx : orderOf x = m)
    (hodd : Odd m) (hm : 1 < m) : x ^ 2 ≠ 1 := by
  intro h
  have hdvd : orderOf x ∣ 2 := orderOf_dvd_iff_pow_eq_one.mpr h
  rw [hx] at hdvd
  have hle := Nat.le_of_dvd (by norm_num) hdvd
  obtain ⟨k, hk⟩ := hodd
  omega

/-! ## Trace of a conjugate -/

/-- `tr (A B A⁻¹) = tr B` for `A, B ∈ GL(2,F)`. -/
lemma trace_conj_GL (F : Type*) [Field F] (A B : GL (Fin 2) F) :
    ((A * B * A⁻¹ : GL (Fin 2) F) : Matrix (Fin 2) (Fin 2) F).trace
      = ((B : GL (Fin 2) F) : Matrix (Fin 2) (Fin 2) F).trace := by
  have hunit : IsUnit (A : Matrix (Fin 2) (Fin 2) F) := by
    rw [Matrix.isUnit_iff_isUnit_det, ← Matrix.GeneralLinearGroup.val_det_apply]
    exact (Matrix.GeneralLinearGroup.det A).isUnit
  rw [Matrix.GeneralLinearGroup.coe_mul, Matrix.GeneralLinearGroup.coe_mul,
    Matrix.GeneralLinearGroup.coe_inv]
  exact Matrix.trace_conj hunit (B : Matrix (Fin 2) (Fin 2) F)

/-- `tr (-B) = - tr B` for `B ∈ GL(2,F)`. -/
lemma trace_negGL (F : Type*) [Field F] (g : GL (Fin 2) F) :
    ((Work.L2F.Props.negGL F g : GL (Fin 2) F) : Matrix (Fin 2) (Fin 2) F).trace
      = - ((g : GL (Fin 2) F) : Matrix (Fin 2) (Fin 2) F).trace := by
  rw [Work.L2F.Props.negGL_apply, Matrix.trace_neg]

/-! ## The centralizer in `PGL(2,F)` of `mk g` is the image of the centralizer of `g` -/

/-- If `x = mk g` is not an involution, then an element of `PGL(2,F)` centralizes `x` iff it
has a lift centralizing `g`.  Consequently
`C_{PGL}(mk g) = (C_{GL}(g)).map mk`.

Indeed `mk A` and `mk g` commute iff `A g A⁻¹ = u • g` for a scalar `u`; taking determinants
gives `u = ±1`.  If `u = -1` then `tr g = -tr g = 0`, so `g² = -det(g) • 1` is scalar by
Cayley–Hamilton, whence `x² = 1`, contradicting the hypothesis.  Hence `u = 1`. -/
theorem centralizer_mk_eq_map (F : Type*) [Field F] (g : GL (Fin 2) F) (h2 : (2 : F) ≠ 0)
    (hx2 : (Matrix.ProjGenLinGroup.mk g) ^ 2 ≠ 1) :
    Subgroup.centralizer ({Matrix.ProjGenLinGroup.mk g} :
        Set (Matrix.ProjGenLinGroup (Fin 2) F)) =
      (Subgroup.centralizer ({g} : Set (GL (Fin 2) F))).map Matrix.ProjGenLinGroup.mk := by
  apply le_antisymm
  · intro z hz
    obtain ⟨A, rfl⟩ := Matrix.ProjGenLinGroup.mk_surjective z
    rw [Subgroup.mem_map]
    refine ⟨A, ?_, rfl⟩
    rw [Subgroup.mem_centralizer_singleton_iff]
    have hcomm : Matrix.ProjGenLinGroup.mk A * Matrix.ProjGenLinGroup.mk g =
        Matrix.ProjGenLinGroup.mk g * Matrix.ProjGenLinGroup.mk A :=
      Subgroup.mem_centralizer_singleton_iff.mp hz
    rw [Work.L2F.Props.mk_mul_comm_mk_iff] at hcomm
    obtain ⟨u, hu⟩ := hcomm
    rcases Work.L2F.Props.eq_or_eq_negGL_of_eq_scalar_mul hu with h | h
    · have h' := congrArg (fun x : GL (Fin 2) F => x * A) h
      simpa [mul_assoc] using h'
    · exfalso
      have htr_conj : ((A * g * A⁻¹ : GL (Fin 2) F) : Matrix (Fin 2) (Fin 2) F).trace
          = ((g : GL (Fin 2) F) : Matrix (Fin 2) (Fin 2) F).trace :=
        trace_conj_GL F A g
      have htr0 : ((g : GL (Fin 2) F) : Matrix (Fin 2) (Fin 2) F).trace = 0 := by
        have h' := htr_conj
        rw [h] at h'
        rw [trace_negGL F g] at h'
        have h2' : (2 : F) * ((g : GL (Fin 2) F) : Matrix (Fin 2) (Fin 2) F).trace = 0 := by
          linear_combination -h'
        exact (mul_eq_zero.mp h2').resolve_left h2
      have hsq : ((g : GL (Fin 2) F) : Matrix (Fin 2) (Fin 2) F) *
            ((g : GL (Fin 2) F) : Matrix (Fin 2) (Fin 2) F)
          = (-(((g : GL (Fin 2) F) : Matrix (Fin 2) (Fin 2) F).det)) • 1 := by
        have h := Work.L2F.Mat2.sq_eq_trace_smul_sub_det F
          ((g : GL (Fin 2) F) : Matrix (Fin 2) (Fin 2) F)
        rw [htr0, zero_smul, zero_sub] at h
        rw [h, neg_smul]
      have hgg : Matrix.ProjGenLinGroup.mk (g * g) = 1 := by
        rw [Matrix.ProjGenLinGroup.mk_eq_one, Matrix.GeneralLinearGroup.center_eq_range_scalar]
        refine ⟨-(Matrix.GeneralLinearGroup.det g), ?_⟩
        apply Units.ext
        simp only [Matrix.GeneralLinearGroup.coe_scalar, Matrix.GeneralLinearGroup.coe_mul,
          Units.val_neg, Matrix.GeneralLinearGroup.val_det_apply, Matrix.scalar_apply,
          ← Matrix.smul_one_eq_diagonal]
        exact hsq.symm
      apply hx2
      rw [pow_two, ← map_mul]
      exact hgg
  · rintro z ⟨h, hh, rfl⟩
    rw [Subgroup.mem_centralizer_singleton_iff]
    rw [← map_mul, ← map_mul]
    congr 1
    exact Subgroup.mem_centralizer_singleton_iff.mp hh

/-! ## The map `x ↦ det x⁻¹ • (x * x)` and the torus -/

/-- `↑(g ^ m) = (↑g) ^ m` for `g ∈ GL(2,F)`. -/
lemma GL_coe_pow (F : Type*) [Field F] (g : GL (Fin 2) F) (m : ℕ) :
    ((g ^ m : GL (Fin 2) F) : Matrix (Fin 2) (Fin 2) F) =
      ((g : Matrix (Fin 2) (Fin 2) F)) ^ m := by
  induction m with
  | zero => rw [pow_zero, pow_zero, Matrix.GeneralLinearGroup.coe_one]
  | succ k ih => rw [pow_succ, pow_succ, Matrix.GeneralLinearGroup.coe_mul, ih]

/-- `rhoSL` of a scalar matrix is `1`. -/
lemma rhoSL_scalar (F : Type*) [Field F] (u : Fˣ) :
    rhoSL F (Matrix.GeneralLinearGroup.scalar (Fin 2) u) = 1 := by
  apply Subtype.ext
  rw [rhoSL_coe, rhoMat, Matrix.SpecialLinearGroup.coe_one,
    ← Matrix.GeneralLinearGroup.val_det_apply, Matrix.GeneralLinearGroup.det_scalar,
    Fintype.card_fin, ← Matrix.GeneralLinearGroup.coe_mul, ← map_mul,
    Matrix.GeneralLinearGroup.coe_scalar, Matrix.scalar_apply, ← Matrix.smul_one_eq_diagonal,
    pow_two]
  rw [Units.val_mul, smul_smul,
    inv_mul_cancel₀ (mul_ne_zero (Units.ne_zero u) (Units.ne_zero u)), one_smul]

/-- The centralizer of `g` in `GL(2,F)` is commutative (it lies in the commutative algebra
`F·1 + F·glW`). -/
theorem glCent_comm (F : Type*) [Field F] (h2 : (2 : F) ≠ 0) (g : GL (Fin 2) F)
    (hd : glD F g ≠ 0) (hns : ∀ c : F, glW F g ≠ c • (1 : Matrix (Fin 2) (Fin 2) F))
    (x y : GL (Fin 2) F)
    (hx : x ∈ Subgroup.centralizer ({g} : Set (GL (Fin 2) F)))
    (hy : y ∈ Subgroup.centralizer ({g} : Set (GL (Fin 2) F))) : x * y = y * x := by
  obtain ⟨a, b, hab⟩ := (glCent_algSpan F h2 g hd hns x).mp hx
  obtain ⟨c, e, hce⟩ := (glCent_algSpan F h2 g hd hns y).mp hy
  apply Units.ext
  rw [Matrix.GeneralLinearGroup.coe_mul, Matrix.GeneralLinearGroup.coe_mul, hab, hce,
    Work.L2F.Semisimple.smul_one_add_smul_mul F (glW F g) (glD F g) (glW_mul_self F h2 g) a b c e,
    Work.L2F.Semisimple.smul_one_add_smul_mul F (glW F g) (glD F g) (glW_mul_self F h2 g) c e a b]
  rw [show a * c + glD F g * (b * e) = c * a + glD F g * (e * b) from by ring,
    show a * e + b * c = c * b + e * a from by ring]

/-- The monoid homomorphism `C_{GL(2,F)}(g) →* SL(2,F)`, `x ↦ det(x)⁻¹ • (x * x)`. -/
noncomputable def rhoHom (F : Type*) [Field F] (g : GL (Fin 2) F) (h2 : (2 : F) ≠ 0)
    (hd : glD F g ≠ 0) (hns : ∀ c : F, glW F g ≠ c • (1 : Matrix (Fin 2) (Fin 2) F)) :
    ↥(Subgroup.centralizer ({g} : Set (GL (Fin 2) F))) →* SL(2, F) where
  toFun x := rhoSL F (x : GL (Fin 2) F)
  map_one' := by
    rw [Subgroup.coe_one, rhoSL_one]
  map_mul' := fun x y => by
    have hc : ((x : GL (Fin 2) F) : Matrix (Fin 2) (Fin 2) F) *
        ((y : GL (Fin 2) F) : Matrix (Fin 2) (Fin 2) F) =
        ((y : GL (Fin 2) F) : Matrix (Fin 2) (Fin 2) F) *
        ((x : GL (Fin 2) F) : Matrix (Fin 2) (Fin 2) F) := by
      have h := congrArg (fun z : GL (Fin 2) F => (z : Matrix (Fin 2) (Fin 2) F))
        (glCent_comm F h2 g hd hns (x : GL (Fin 2) F) (y : GL (Fin 2) F) x.2 y.2)
      rw [Matrix.GeneralLinearGroup.coe_mul, Matrix.GeneralLinearGroup.coe_mul] at h
      exact h
    show rhoSL F ((x * y : ↥(Subgroup.centralizer ({g} : Set (GL (Fin 2) F)))):
      GL (Fin 2) F) = rhoSL F (x : GL (Fin 2) F) * rhoSL F (y : GL (Fin 2) F)
    rw [Subgroup.coe_mul, rhoSL_mul F (x : GL (Fin 2) F) (y : GL (Fin 2) F) hc]

/-- Characterisation of the range of `hypToSLHom`: it is the set of matrices `c • 1 + e • glW`
with `c ^ 2 - glD * e ^ 2 = 1`. -/
lemma mem_hypToSLHom_range (F : Type*) [Field F] (g : GL (Fin 2) F) (h2 : (2 : F) ≠ 0)
    (u : SL(2, F)) :
    u ∈ (Work.L2F.Semisimple.hypToSLHom F (glW F g) (glD F g) (glW_trace F h2 g)
      (glW_mul_self F h2 g)).range ↔
      ∃ c e : F, c ^ 2 - glD F g * e ^ 2 = 1 ∧
        (u : Matrix (Fin 2) (Fin 2) F) = c • 1 + e • glW F g := by
  constructor
  · rintro ⟨t, ht⟩
    obtain ⟨a, b, hab, htq⟩ :=
      (Work.L2F.Conic.mem_hypTorus F (glD F g) (t : SL(2, F))).mp t.2
    refine ⟨a, b, hab, ?_⟩
    rw [← ht]
    change ((Work.L2F.Semisimple.hypToSL F (glW F g) (glD F g) (glW_trace F h2 g)
      (glW_mul_self F h2 g) t : SL(2, F)) : Matrix (Fin 2) (Fin 2) F)
        = a • 1 + b • glW F g
    rw [Work.L2F.Semisimple.hypToSL_apply]
    have h00 : ((t : SL(2, F)) : Matrix (Fin 2) (Fin 2) F) 0 0 = a := by rw [htq]; rfl
    have h10 : ((t : SL(2, F)) : Matrix (Fin 2) (Fin 2) F) 1 0 = b := by rw [htq]; rfl
    rw [h00, h10]
  · rintro ⟨c, e, hce, hue⟩
    set t : ↥(Work.L2F.hypTorus F (glD F g)) :=
      ⟨⟨Work.L2F.Mat2.quadMat (glD F g) c e,
        by rw [Work.L2F.Mat2.quadMat_det]; exact hce⟩,
        (Work.L2F.Conic.mem_hypTorus F (glD F g) _).mpr ⟨c, e, hce, rfl⟩⟩ with ht
    refine ⟨t, ?_⟩
    apply Subtype.ext
    change ((Work.L2F.Semisimple.hypToSL F (glW F g) (glD F g) (glW_trace F h2 g)
      (glW_mul_self F h2 g) t : SL(2, F)) : Matrix (Fin 2) (Fin 2) F) =
        (u : Matrix (Fin 2) (Fin 2) F)
    rw [Work.L2F.Semisimple.hypToSL_apply]
    have h00 : ((t : SL(2, F)) : Matrix (Fin 2) (Fin 2) F) 0 0 = c := by
      rw [ht]; rfl
    have h10 : ((t : SL(2, F)) : Matrix (Fin 2) (Fin 2) F) 1 0 = e := by
      rw [ht]; rfl
    rw [h00, h10, hue]

/-- `rhoSL x = 1` iff `mk x = 1`, for `x` in the centralizer of `g`. -/
lemma rhoSL_eq_one_iff (F : Type*) [Field F] (g : GL (Fin 2) F) (h2 : (2 : F) ≠ 0)
    (hd : glD F g ≠ 0) (hns : ∀ c : F, glW F g ≠ c • (1 : Matrix (Fin 2) (Fin 2) F))
    (x : GL (Fin 2) F) (hx : x ∈ Subgroup.centralizer ({g} : Set (GL (Fin 2) F))) :
    rhoSL F x = 1 ↔ Matrix.ProjGenLinGroup.mk x = 1 := by
  obtain ⟨a, b, hab⟩ := (glCent_algSpan F h2 g hd hns x).mp hx
  have hdet0 : ((x : Matrix (Fin 2) (Fin 2) F).det) ≠ 0 := by
    rw [← Matrix.GeneralLinearGroup.val_det_apply]
    exact (Matrix.GeneralLinearGroup.det x).ne_zero
  constructor
  · intro h
    have hr : rhoMat F x = 1 := by
      have := congrArg (fun z : SL(2, F) => (z : Matrix (Fin 2) (Fin 2) F)) h
      rwa [rhoSL_coe, Matrix.SpecialLinearGroup.coe_one] at this
    -- `x * x = det x • 1`
    have hxx : (x : Matrix (Fin 2) (Fin 2) F) * (x : Matrix (Fin 2) (Fin 2) F) =
        (x : Matrix (Fin 2) (Fin 2) F).det • 1 := by
      have h1 : (x : Matrix (Fin 2) (Fin 2) F).det • (rhoMat F x) =
          (x : Matrix (Fin 2) (Fin 2) F).det • (1 : Matrix (Fin 2) (Fin 2) F) := by
        rw [hr]
      rw [rhoMat, smul_smul, mul_inv_cancel₀ hdet0, one_smul] at h1
      exact h1
    have hdetab : (x : Matrix (Fin 2) (Fin 2) F).det = a ^ 2 - glD F g * b ^ 2 := by
      rw [hab]
      exact Work.L2F.Semisimple.det_smul_one_add_smul F (glW F g) (glD F g)
        (glW_trace F h2 g) (glW_mul_self F h2 g) a b
    have hxxab : (x : Matrix (Fin 2) (Fin 2) F) * (x : Matrix (Fin 2) (Fin 2) F) =
        (a * a + glD F g * (b * b)) • 1 + (a * b + b * a) • glW F g := by
      rw [hab]
      exact Work.L2F.Semisimple.smul_one_add_smul_mul F (glW F g) (glD F g)
        (glW_mul_self F h2 g) a b a b
    -- take traces of `x * x = det x • 1`
    have hb : b = 0 := by
      have htr := congrArg Matrix.trace hxx
      rw [hxxab] at htr
      rw [Matrix.trace_add, Matrix.trace_smul, Matrix.trace_smul, Matrix.trace_one,
        Fintype.card_fin, glW_trace F h2 g] at htr
      simp only [smul_eq_mul, mul_zero, add_zero] at htr
      rw [hdetab, Matrix.trace_smul, Matrix.trace_one, Fintype.card_fin] at htr
      simp only [smul_eq_mul] at htr
      have h4 : (4 : F) * (glD F g * b ^ 2) = 0 := by linear_combination htr
      have h40 : (4 : F) ≠ 0 := by
        have h44 : (4 : F) = 2 * 2 := by norm_num
        rw [h44]; exact mul_ne_zero h2 h2
      have h' := (mul_eq_zero.mp h4).resolve_left h40
      have h'' := (mul_eq_zero.mp h').resolve_left hd
      rw [pow_two] at h''
      exact mul_self_eq_zero.mp h''
    -- `x = a • 1` is scalar, with `a ≠ 0`
    have hxa : (x : Matrix (Fin 2) (Fin 2) F) = a • 1 := by
      rw [hab, hb, zero_smul, add_zero]
    rw [Matrix.ProjGenLinGroup.mk_eq_one, Matrix.GeneralLinearGroup.center_eq_range_scalar]
    refine ⟨Units.mk0 a ?_, ?_⟩
    · intro ha0
      exact hdet0 (by rw [hxa, ha0, zero_smul, Matrix.det_zero])
    · apply Units.ext
      rw [Matrix.GeneralLinearGroup.coe_scalar, Matrix.scalar_apply,
        ← Matrix.smul_one_eq_diagonal]
      exact hxa.symm
  · intro h
    have hx' : x ∈ Subgroup.center (GL (Fin 2) F) := Matrix.ProjGenLinGroup.mk_eq_one.mp h
    rw [Matrix.GeneralLinearGroup.center_eq_range_scalar] at hx'
    obtain ⟨u, hu⟩ := hx'
    rw [← hu, rhoSL_scalar]

/-- The range of `rhoHom` is the range of `hypToSLHom`, i.e. the norm-one torus. -/
theorem rhoHom_range (F : Type*) [Field F] (g : GL (Fin 2) F) (h2 : (2 : F) ≠ 0)
    (hd : glD F g ≠ 0) (hns : ∀ c : F, glW F g ≠ c • (1 : Matrix (Fin 2) (Fin 2) F)) :
    (rhoHom F g h2 hd hns).range = (Work.L2F.Semisimple.hypToSLHom F (glW F g) (glD F g)
      (glW_trace F h2 g) (glW_mul_self F h2 g)).range := by
  apply le_antisymm
  · rintro u ⟨x, rfl⟩
    obtain ⟨a, b, hab⟩ := (glCent_algSpan F h2 g hd hns (x : GL (Fin 2) F)).mp x.2
    exact rhoSL_mem_hypToSLHom_range F g h2 hd (x : GL (Fin 2) F) a b hab
  · intro u hu
    obtain ⟨c, e, hce, hue⟩ := (mem_hypToSLHom_range F g h2 u).mp hu
    obtain ⟨x, hxmem, hxeq⟩ := exists_rhoSL_eq F g h2 hd c e hce
    refine ⟨⟨x, hxmem⟩, ?_⟩
    apply Subtype.ext
    change (rhoSL F x : Matrix (Fin 2) (Fin 2) F) = (u : Matrix (Fin 2) (Fin 2) F)
    exact hxeq.trans hue.symm

theorem centralizer_torus_cyclic (F : Type*) [Field F] [Fintype F] (h2 : (2 : F) ≠ 0) (q : ℕ)
    (hq : Nat.card F = q) (hm : 1 < (if q % 4 = 1 then (q + 1) / 2 else (q - 1) / 2))
    (x : Matrix.ProjGenLinGroup (Fin 2) F)
    (hx : orderOf x = (if q % 4 = 1 then (q + 1) / 2 else (q - 1) / 2)) :
    IsCyclic (Subgroup.centralizer ({x} : Set (Matrix.ProjGenLinGroup (Fin 2) F))) := by
  classical
  -- lift `x` to `GL(2,F)`
  obtain ⟨g, hg⟩ := Matrix.ProjGenLinGroup.mk_surjective x
  -- `m`, its parity and its non-vanishing in `F`
  set m : ℕ := (if q % 4 = 1 then (q + 1) / 2 else (q - 1) / 2) with hmdef
  have hoddq : Odd q := by rw [← hq]; exact odd_card_of_two_ne_zero F h2
  have hoddm : Odd m := odd_m_of_odd_card q m hoddq hmdef
  have hmF : (m : F) ≠ 0 := m_ne_zero_char F hq hoddq hmdef
  have hx2 : x ^ 2 ≠ 1 := sq_ne_one_of_orderOf x hx hoddm hm
  have hx2' : (Matrix.ProjGenLinGroup.mk g) ^ 2 ≠ 1 := by rw [hg]; exact hx2
  -- the centralizer in `PGL` is the image of the centralizer in `GL`
  have hcent : Subgroup.centralizer ({x} : Set (Matrix.ProjGenLinGroup (Fin 2) F)) =
      (Subgroup.centralizer ({g} : Set (GL (Fin 2) F))).map Matrix.ProjGenLinGroup.mk := by
    rw [← hg]; exact centralizer_mk_eq_map F g h2 hx2'
  -- `glW` is not scalar: otherwise `g` would be scalar and `x = 1`
  have hns : ∀ c : F, glW F g ≠ c • (1 : Matrix (Fin 2) (Fin 2) F) := by
    intro c hc
    have hscalar : (g : Matrix (Fin 2) (Fin 2) F) =
        ((g : Matrix (Fin 2) (Fin 2) F).trace / 2 + c) • 1 := by
      conv_lhs => rw [glW_add F g]
      rw [hc, ← add_smul]
    set d : F := (g : Matrix (Fin 2) (Fin 2) F).trace / 2 + c with hddef
    have hdet : (g : Matrix (Fin 2) (Fin 2) F).det = d ^ 2 := by
      rw [hscalar, Matrix.det_smul, Matrix.det_one, Fintype.card_fin]; ring
    have hd0 : d ≠ 0 := by
      intro h0
      have huz : ((g : Matrix (Fin 2) (Fin 2) F).det) ≠ 0 := by
        rw [← Matrix.GeneralLinearGroup.val_det_apply]
        exact (Matrix.GeneralLinearGroup.det g).ne_zero
      rw [hdet, h0] at huz
      exact huz (by norm_num)
    have hmk : Matrix.ProjGenLinGroup.mk g = 1 := by
      rw [Matrix.ProjGenLinGroup.mk_eq_one, Matrix.GeneralLinearGroup.center_eq_range_scalar]
      refine ⟨Units.mk0 d hd0, ?_⟩
      apply Units.ext
      rw [Matrix.GeneralLinearGroup.coe_scalar, Matrix.scalar_apply, ← Matrix.smul_one_eq_diagonal]
      exact hscalar.symm
    have hx1 : x = 1 := by rw [← hg]; exact hmk
    have h1 : orderOf x = 1 := by rw [hx1]; exact orderOf_one
    rw [hx] at h1
    omega
  -- `g ^ m` is scalar
  have hgpow : ∃ μ : F, ((g : Matrix (Fin 2) (Fin 2) F)) ^ m =
      μ • (1 : Matrix (Fin 2) (Fin 2) F) := by
    have hxm : x ^ m = 1 := by rw [← hx]; exact pow_orderOf_eq_one x
    have hgm : Matrix.ProjGenLinGroup.mk (g ^ m) = 1 := by rw [map_pow, hg]; exact hxm
    rw [Matrix.ProjGenLinGroup.mk_eq_one, Matrix.GeneralLinearGroup.center_eq_range_scalar] at hgm
    obtain ⟨u, hu⟩ := hgm
    refine ⟨(u : F), ?_⟩
    rw [← GL_coe_pow F g m, ← hu, Matrix.GeneralLinearGroup.coe_scalar, Matrix.scalar_apply,
      ← Matrix.smul_one_eq_diagonal]
  -- the discriminant is nonzero
  have hd : glD F g ≠ 0 := glD_ne_zero F h2 g m hmF hgpow hns
  -- the isomorphism `C_PGL(x) ≃* range (rhoHom)`
  set H : Subgroup (GL (Fin 2) F) := Subgroup.centralizer ({g} : Set (GL (Fin 2) F)) with hH
  let Phi : ↥H →* Matrix.ProjGenLinGroup (Fin 2) F :=
    (Matrix.ProjGenLinGroup.mk).comp H.subtype
  let Psi : ↥H →* SL(2, F) := rhoHom F g h2 hd hns
  have hPhirange : Phi.range = Subgroup.centralizer
      ({x} : Set (Matrix.ProjGenLinGroup (Fin 2) F)) := by
    show ((Matrix.ProjGenLinGroup.mk).comp H.subtype).range = _
    rw [MonoidHom.range_comp, Subgroup.range_subtype, hH]
    exact hcent.symm
  have hker : Phi.ker = Psi.ker := by
    ext z
    rw [MonoidHom.mem_ker, MonoidHom.mem_ker]
    exact (rhoSL_eq_one_iff F g h2 hd hns (z : GL (Fin 2) F) z.2).symm
  have e : Phi.range ≃* Psi.range :=
    ((QuotientGroup.quotientKerEquivRange Phi).symm.trans
      (QuotientGroup.quotientMulEquivOfEq hker)).trans
      (QuotientGroup.quotientKerEquivRange Psi)
  have hcyc : IsCyclic ↥Psi.range := by
    have hrange : Psi.range = (Work.L2F.Semisimple.hypToSLHom F (glW F g) (glD F g)
        (glW_trace F h2 g) (glW_mul_self F h2 g)).range := rhoHom_range F g h2 hd hns
    rw [hrange]
    have hinj : Function.Injective (Work.L2F.Semisimple.hypToSLHom F (glW F g) (glD F g)
        (glW_trace F h2 g) (glW_mul_self F h2 g)).rangeRestrict := fun a b hab =>
      Work.L2F.Semisimple.hypToSLHom_injective F h2 (glW F g) (glD F g) (glW_trace F h2 g)
        (glW_mul_self F h2 g) hd hns (Subtype.ext_iff.mp hab)
    have hbij : Function.Bijective (Work.L2F.Semisimple.hypToSLHom F (glW F g) (glD F g)
        (glW_trace F h2 g) (glW_mul_self F h2 g)).rangeRestrict :=
      ⟨hinj, MonoidHom.rangeRestrict_surjective _⟩
    exact (MulEquiv.isCyclic (MulEquiv.ofBijective _ hbij)).mp
      (Work.L2F.Conic.hypTorus_cyclic F h2 (glD F g) hd)
  rw [← hPhirange]
  exact (MulEquiv.isCyclic e).mpr hcyc

end Work.L2F.Props
