import Mathlib
import Submission.Work.HP.Q44Setup
import Submission.Work.HP.Q44Child.abs_wCoeff_le
import Submission.Work.HP.Q44Child.ncard_range_le_prod

/-!
# The number of witness classes in a ball (`Work.HP.Q44Child.witness_class_count`)

For a `ℤ`-linearly independent triple `v : Fin 3 → (Fin 5 → ℤ)` and a radius `J ≥ 1` we bound
the number of distinct values of `wClass v a` as `a` runs over the integral coefficient
vectors of Euclidean norm at most `J`.

This is the "witness class count" of BLBS, *The Hasse principle for random Fano
hypersurfaces* (Annals 2023), Lemma `Lemma l56`: the image of the ball is contained in a
product of intervals whose side lengths are the row norms `‖wCoeff v e‖`, and the row norm
of the `e`-th row is `≪ ∏_j ‖v_j‖^{e_j}`.  Multiplying over the `15` exponent vectors
`e : Tri4` and using `Σ_e e_j = 20` gives the exponent `20` in the product.
-/

set_option autoImplicit false
set_option maxRecDepth 4000

noncomputable section

namespace Work.HP.Q44Child

open Work.HP

/-! ## The exponent set `Tri4` of degree-`4` monomials in three variables -/

lemma mon_toFinsupp_degree (m : Mon 4 2) : (Mon.toFinsupp m).sum (fun _ n => n) = 4 := by
  show Finsupp.degree (Mon.toFinsupp m) = 4
  rw [Finsupp.degree_eq_sum]
  simp only [Mon.toFinsupp, Finsupp.equivFunOnFinite_symm_apply_apply]
  exact m.2

lemma mon_toFinsupp_inj' {a b : Mon 4 2} (h : Mon.toFinsupp a = Mon.toFinsupp b) : a = b := by
  have h1 : a.1 = b.1 := by
    funext i
    have h2 := DFunLike.congr_fun h i
    simp only [Mon.toFinsupp, Finsupp.equivFunOnFinite_symm_apply_apply] at h2
    exact Fin.ext (by omega)
  exact Subtype.ext h1

lemma finsupp_sum_eq_sum_fin (x : Fin 3 →₀ ℕ) : x.sum (fun _ n => n) = ∑ i, x i :=
  Finsupp.sum_fintype x (fun _ n => n) (by intro i; rfl)

/-- The degree-`4` exponent vectors of three variables, as the monomials in three variables. -/
def tri4Equiv : Mon 4 2 ≃ Tri4 where
  toFun m := ⟨Mon.toFinsupp m, mon_toFinsupp_degree m⟩
  invFun e :=
    ⟨fun j => ⟨e.1 j, by
        have h : ∑ i, e.1 i = 4 := by rw [← finsupp_sum_eq_sum_fin]; exact e.2
        have h2 := Finset.single_le_sum (f := e.1) (fun i _ => Nat.zero_le _) (Finset.mem_univ j)
        omega⟩,
      by rw [← finsupp_sum_eq_sum_fin]; exact e.2⟩
  left_inv m := by
    ext i
    simp [Mon.toFinsupp]
  right_inv e := by
    ext i
    simp [Mon.toFinsupp]

instance : Fintype Tri4 := Fintype.ofEquiv (Mon 4 2) tri4Equiv

lemma card_tri4 : Fintype.card Tri4 = 15 := by decide

lemma sum_tri4_coord (j : Fin 3) : ∑ e : Tri4, (e.1 j : ℕ) = 20 := by
  fin_cases j <;> decide

/-- `∏_{e} ∏_j B_j^{e_j} = ∏_j B_j^{20}`: the exponents of the three variables average out,
because `Σ_{e} e_j = 20` for every `j`. -/
lemma prod_tri4_coord (B : Fin 3 → ℝ) :
    ∏ e : Tri4, ∏ j : Fin 3, B j ^ (e.1 j) = ∏ j : Fin 3, B j ^ 20 := by
  rw [Finset.prod_comm]
  refine Finset.prod_congr rfl fun j _ => ?_
  rw [Finset.prod_pow_eq_pow_sum, sum_tri4_coord j]

lemma card_mon44 : Fintype.card (Mon 4 4) = 70 := by decide

/-! ## The main count -/

theorem witness_class_count :
    ∃ C : ℝ, 0 < C ∧ ∀ (v : Fin 3 → (Fin 5 → ℤ)), LinearIndependent ℤ v → ∀ J : ℝ, 1 ≤ J →
      (Set.range (fun a : {a : Work.HP.Mon 4 4 → ℤ // Work.HP.eNorm a ≤ J} =>
          Work.HP.wClass v a.1)).Finite ∧
      ((Set.range (fun a : {a : Work.HP.Mon 4 4 → ℤ // Work.HP.eNorm a ≤ J} =>
          Work.HP.wClass v a.1)).ncard : ℝ)
        ≤ C * J ^ 15 * ∏ j : Fin 3, Work.HP.eNorm (v j) ^ 20 := by
  classical
  refine ⟨(5 * (10000 * 70)) ^ 15, by positivity, ?_⟩
  intro v hv J hJ
  -- the coordinate bound `B j = ‖v j‖`
  set B : Fin 3 → ℝ := fun j => eNorm (v j) with hB
  have hvj : ∀ j : Fin 3, v j ≠ 0 := by
    intro j h0
    have hrel : ∑ i : Fin 3, (Pi.single j (1 : ℤ) : Fin 3 → ℤ) i • v i = 0 := by
      rw [Finset.sum_eq_single j (fun b _ hb => by rw [Pi.single_eq_of_ne hb, zero_smul])
        (fun hj => absurd (Finset.mem_univ j) hj)]
      simp [h0]
    have h1 := (Fintype.linearIndependent_iff.mp hv)
      (Pi.single j (1 : ℤ) : Fin 3 → ℤ) hrel j
    simp at h1
  have hB1 : ∀ j : Fin 3, 1 ≤ B j := by
    intro j
    obtain ⟨i0, hi⟩ : ∃ i, v j i ≠ 0 := by
      by_contra h
      exact hvj j (funext fun i => by simpa using not_exists.mp h i)
    have h2 : (1 : ℝ) ≤ ((v j i0 : ℤ) : ℝ) ^ 2 := by
      have h2' : (1 : ℤ) ≤ (v j i0) ^ 2 := by
        rcases lt_or_gt_of_ne (show v j i0 ≠ 0 from hi) with h | h
        · nlinarith
        · nlinarith
      exact_mod_cast h2'
    have h3 : ((v j i0 : ℤ) : ℝ) ^ 2 ≤ ∑ i : Fin 5, ((v j i : ℤ) : ℝ) ^ 2 :=
      Finset.single_le_sum (f := fun i : Fin 5 => ((v j i : ℤ) : ℝ) ^ 2)
        (fun i _ => sq_nonneg _) (Finset.mem_univ i0)
    rw [hB]
    calc (1 : ℝ) = Real.sqrt 1 := Real.sqrt_one.symm
      _ ≤ Real.sqrt (∑ i : Fin 5, ((v j i : ℤ) : ℝ) ^ 2) := Real.sqrt_le_sqrt (le_trans h2 h3)
      _ = eNorm (v j) := rfl
  have hvB : ∀ (i : Fin 5) (j : Fin 3), |((v j i : ℤ) : ℝ)| ≤ B j := by
    intro i j
    rw [hB]
    rw [show |((v j i : ℤ) : ℝ)| = Real.sqrt (((v j i : ℤ) : ℝ) ^ 2) from
      (Real.sqrt_sq_eq_abs _).symm]
    exact Real.sqrt_le_sqrt (Finset.single_le_sum
      (f := fun i : Fin 5 => ((v j i : ℤ) : ℝ) ^ 2) (fun i _ => sq_nonneg _) (Finset.mem_univ i))
  -- coordinates of the image are bounded by `R`
  have hrow : ∀ (e : Tri4) (m : Mon 4 4),
      |(wCoeff v e.1 m : ℝ)| ≤ 10000 * ∏ j : Fin 3, B j ^ (e.1 j) :=
    fun e m => abs_wCoeff_le v B hB1 hvB e.1 m
  have himg : ∀ (a : {a : Mon 4 4 → ℤ // eNorm a ≤ J}) (e : Tri4),
      |(wClass v a.1 e : ℝ)| ≤ 10000 * 70 * J * ∏ j : Fin 3, B j ^ (e.1 j) := by
    intro a e
    have ha : ∀ m : Mon 4 4, |((a.1 m : ℤ) : ℝ)| ≤ J := by
      intro m
      calc |((a.1 m : ℤ) : ℝ)| = Real.sqrt (((a.1 m : ℤ) : ℝ) ^ 2) :=
            (Real.sqrt_sq_eq_abs _).symm
        _ ≤ Real.sqrt (∑ i : Mon 4 4, ((a.1 i : ℤ) : ℝ) ^ 2) :=
            Real.sqrt_le_sqrt (Finset.single_le_sum
              (f := fun i : Mon 4 4 => ((a.1 i : ℤ) : ℝ) ^ 2) (fun i _ => sq_nonneg _)
              (Finset.mem_univ m))
        _ = eNorm a.1 := rfl
        _ ≤ J := a.2
    calc |(wClass v a.1 e : ℝ)|
        = |∑ m : Mon 4 4, ((a.1 m : ℤ) : ℝ) * ((wCoeff v e.1 m : ℝ))| := by
          simp only [wClass, Int.cast_sum, Int.cast_mul]
      _ ≤ ∑ m : Mon 4 4, |((a.1 m : ℤ) : ℝ) * ((wCoeff v e.1 m : ℝ))| :=
          Finset.abs_sum_le_sum_abs _ _
      _ = ∑ m : Mon 4 4, |((a.1 m : ℤ) : ℝ)| * |((wCoeff v e.1 m : ℝ))| := by
          simp [abs_mul]
      _ ≤ ∑ _m : Mon 4 4, J * (10000 * ∏ j : Fin 3, B j ^ (e.1 j)) := by
          refine Finset.sum_le_sum fun m _ => ?_
          exact mul_le_mul (ha m) (hrow e m) (abs_nonneg _) (le_trans zero_le_one hJ)
      _ = 70 * (J * (10000 * ∏ j : Fin 3, B j ^ (e.1 j))) := by
          rw [Finset.sum_const, Finset.card_univ, card_mon44, nsmul_eq_mul]
          norm_num
      _ = 10000 * 70 * J * ∏ j : Fin 3, B j ^ (e.1 j) := by ring
  -- the box count
  set R : Tri4 → ℝ := fun e => 10000 * 70 * J * ∏ j : Fin 3, B j ^ (e.1 j) with hR
  set N : Tri4 → ℕ := fun e => ⌈R e⌉₊ with hN
  have hR1 : ∀ e : Tri4, 1 ≤ R e := by
    intro e
    rw [hR]
    have h1 : 1 ≤ ∏ j : Fin 3, B j ^ (e.1 j) := by
      refine Finset.one_le_prod₀ fun j _ => ?_
      exact one_le_pow₀ (hB1 j)
    have h2 : (1 : ℝ) ≤ J := hJ
    nlinarith [h1, h2]
  have hNbound : ∀ (a : {a : Mon 4 4 → ℤ // eNorm a ≤ J}) (e : Tri4),
      |wClass v a.1 e| ≤ (N e : ℤ) := by
    intro a e
    have h1 : ((|wClass v a.1 e| : ℤ) : ℝ) ≤ R e := by
      rw [Int.cast_abs]
      exact himg a e
    have h2 : R e ≤ (N e : ℝ) := by
      rw [hN]
      exact Nat.le_ceil _
    exact_mod_cast le_trans h1 h2
  obtain ⟨hfin, hcard⟩ :=
    ncard_range_le_prod (fun a : {a : Mon 4 4 → ℤ // eNorm a ≤ J} => wClass v a.1) N hNbound
  refine ⟨hfin, ?_⟩
  -- the arithmetic
  have hstep1 : ∀ e : Tri4, ((2 * N e + 1 : ℕ) : ℝ) ≤ 5 * R e := by
    intro e
    have h1 : (N e : ℝ) < R e + 1 := by
      rw [hN]; exact Nat.ceil_lt_add_one (le_trans zero_le_one (hR1 e))
    have h3 : (1 : ℝ) ≤ R e := hR1 e
    have h4 : ((2 * N e + 1 : ℕ) : ℝ) = 2 * (N e : ℝ) + 1 := by push_cast; ring
    rw [h4]
    linarith
  have hstep2 : ((∏ e : Tri4, (2 * N e + 1) : ℕ) : ℝ) ≤ ∏ e : Tri4, (5 * R e) := by
    rw [Nat.cast_prod]
    refine Finset.prod_le_prod₀ (fun e _ => by positivity) (fun e _ => hstep1 e)
  have hstep3 : (∏ e : Tri4, (5 * R e))
      = (5 * (10000 * 70 * J)) ^ 15 * ∏ j : Fin 3, B j ^ 20 := by
    have h1 : ∀ e : Tri4, 5 * R e
        = (5 * (10000 * 70 * J)) * ∏ j : Fin 3, B j ^ (e.1 j) := by
      intro e; rw [hR]; ring
    have h2 : (∏ e : Tri4, (5 * R e))
        = ∏ e : Tri4, ((5 * (10000 * 70 * J)) * ∏ j : Fin 3, B j ^ (e.1 j)) :=
      Finset.prod_congr rfl (fun e _ => h1 e)
    rw [h2, Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ, card_tri4,
      prod_tri4_coord]
  have hstep4 : (5 * (10000 * 70 * J)) ^ 15 * ∏ j : Fin 3, B j ^ 20
      ≤ (5 * (10000 * 70)) ^ 15 * J ^ 15 * ∏ j : Fin 3, eNorm (v j) ^ 20 := by
    have h1 : (5 * (10000 * 70 * J)) ^ 15 = (5 * (10000 * 70)) ^ 15 * J ^ 15 := by ring
    have h2 : (∏ j : Fin 3, B j ^ 20) = ∏ j : Fin 3, eNorm (v j) ^ 20 := by
      rw [hB]
    rw [h1, h2]
  calc ((Set.range (fun a : {a : Mon 4 4 → ℤ // eNorm a ≤ J} => wClass v a.1)).ncard : ℝ)
      ≤ ((∏ e : Tri4, (2 * N e + 1) : ℕ) : ℝ) := by exact_mod_cast hcard
    _ ≤ ∏ e : Tri4, (5 * R e) := hstep2
    _ = (5 * (10000 * 70 * J)) ^ 15 * ∏ j : Fin 3, B j ^ 20 := hstep3
    _ ≤ (5 * (10000 * 70)) ^ 15 * J ^ 15 * ∏ j : Fin 3, eNorm (v j) ^ 20 := hstep4

end Work.HP.Q44Child
