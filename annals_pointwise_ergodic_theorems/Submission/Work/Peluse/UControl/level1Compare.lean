import Mathlib
import Submission.Work.Peluse.UControl.levelCompareDefs

/-!
# The level-one comparison

The terminal state of the first phase of the PET chain (`Phase1Terminal d n lc Y`) has live slots
`(P, h)` with `h : Fin n → Bool`, `h ≠ 0`, of degree `d - 1` and leading coefficient
`C d · C lc · shift h`.  In particular, at `d = 2`, the state *is* the level-`1` datum
`levelOneDatum n` of the nested family: its slots are the nonempty subsets of `Fin n`, and its
shifts are the datum's directions `2·lc·Σ_{s ∈ ω} a₁(s)`.

This file proves the comparison: from the terminal state's correlation `lam` (an average over the
window tower with the weights `ν = ∏ μ_H`) one obtains the datum's `linFamAvg` (an average over
the parameter box), losing only the factor `3^n` — the ratio of the uniform weight of the box to
the largest window weight `μ_H ≤ 1/H`.
-/

set_option autoImplicit false
open scoped BigOperators
open Polynomial

namespace Work.Peluse.UControl

noncomputable section

attribute [local instance] Classical.propDecidable

variable {n : ℕ}

/-! ## 1. Evaluating a polynomial of degree at most one -/

/-- A polynomial all of whose coefficients of index `≥ 2` vanish is `C (coeff 0) + C (coeff 1)·X`. -/
lemma eq_C_add_C_mul_X_of_coeff_eq_zero {R : Type*} [Semiring R] (p : R[X])
    (h : ∀ k, 2 ≤ k → p.coeff k = 0) : p = C (p.coeff 0) + C (p.coeff 1) * X := by
  ext k
  match k with
  | 0 => simp
  | 1 => simp
  | (k + 2) =>
      rw [h (k + 2) (by omega)]
      simp

lemma eval_map_coeff_eq {n : ℕ} (p : Polynomial (MvPolynomial (Fin n) ℤ)) (h : p.natDegree ≤ 1)
    (f : MvPolynomial (Fin n) ℤ →+* ℤ) (y : ℤ) :
    (p.map f).eval y = f (p.coeff 1) * y + f (p.coeff 0) := by
  have hcoeff : ∀ k, 2 ≤ k → p.coeff k = 0 :=
    fun k hk => Polynomial.coeff_eq_zero_of_natDegree_lt (by omega)
  conv_lhs => rw [eq_C_add_C_mul_X_of_coeff_eq_zero p hcoeff]
  simp only [Polynomial.map_add, Polynomial.map_mul, Polynomial.map_C, Polynomial.map_X,
    Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_X]
  ring

/-! ## 2. The slots of the terminal state and the level-one indices -/

/-- The slots of the terminal state are the level-`1` indices. -/
lemma levelSlot_bijective {n : ℕ} (lc : ℤ) (Y : HistData 2 n) (hT : Phase1Terminal 2 n lc Y) :
    Function.Bijective (levelSlot lc Y hT) := by
  constructor
  · intro i i' h
    have h2 : levelSlotBool n i = levelSlotBool n i' := by
      have h3 := congrArg (fun (x : (Y.toSym).S.ι) => x.1.2) h
      simpa [levelSlot] using h3
    have h4 : (i1Symm n i).val = (i1Symm n i').val := by
      have h5 := congrArg finsetOfBool h2
      rw [levelSlotBool, levelSlotBool, finsetOfBool_boolOfFinset,
        finsetOfBool_boolOfFinset] at h5
      exact h5
    have h6 : i1Symm n i = i1Symm n i' := Subtype.ext h4
    exact (Fintype.equivFin ((levelOneDatum n).I 1)).symm.injective h6
  · intro x
    obtain ⟨hx1, hx2, -, -⟩ := hT.1 x.1 x.2
    have hwne : (finsetOfBool x.1.2).Nonempty := by
      rw [← boolOfFinset_ne_zero_iff (finsetOfBool x.1.2), boolOfFinset_finsetOfBool]
      exact hx2
    refine ⟨Fintype.equivFin ((levelOneDatum n).I 1) ⟨finsetOfBool x.1.2, hwne⟩, ?_⟩
    have hi : i1Symm n (Fintype.equivFin ((levelOneDatum n).I 1)
        ⟨finsetOfBool x.1.2, hwne⟩) = ⟨finsetOfBool x.1.2, hwne⟩ :=
      Equiv.symm_apply_apply _ _
    have hb : levelSlotBool n (Fintype.equivFin ((levelOneDatum n).I 1)
        ⟨finsetOfBool x.1.2, hwne⟩) = x.1.2 := by
      rw [levelSlotBool, hi, boolOfFinset_finsetOfBool]
    refine Subtype.ext ?_
    show ((Sum.inr 0 : InitIdx 2), levelSlotBool n _) = x.1
    rw [hb]
    exact Prod.ext hx1.symm rfl

/-- Reindexing a product over the slots of the terminal state along the level-`1` indices. -/
lemma prod_slots_eq {n : ℕ} (lc : ℤ) (Y : HistData 2 n) (hT : Phase1Terminal 2 n lc Y)
    (F : (Y.toSym).S.ι → ℂ) :
    ∏ i : (Y.toSym).S.ι, F i
      = ∏ i' : Fin (Fintype.card ((levelOneDatum n).I 1)), F (levelSlot lc Y hT i') := by
  classical
  have hbij := levelSlot_bijective lc Y hT
  refine (Fintype.prod_equiv (Equiv.ofBijective (levelSlot lc Y hT) hbij)
    (fun i' => F (levelSlot lc Y hT i')) F ?_).symm
  intro i'
  rw [Equiv.ofBijective_apply]

/-! ## 3. The shift of a slot of the terminal state -/

/-- The shift polynomial of the terminal slot `levelSlot i`, evaluated at the window parameter of
the tower point `t` and at `y`, is the datum's direction times `y` plus the constant term `β`. -/
lemma levelPoly_eval {n : ℕ} {lc : ℤ} {Y : HistData 2 n} (hT : Phase1Terminal 2 n lc Y)
    (H : ℕ) (t : WinTower H n) (k : Fin (2 * H + 1))
    (i : Fin (Fintype.card ((levelOneDatum n).I 1))) (y : ℤ) :
    ((((Y.toSym).S.P (levelSlot lc Y hT i)).map
        (MvPolynomial.eval (WinTower.param H n t))).eval y)
      = petDir (levelOneDatum n) 2 lc (towerIdx H n (k, t)) i * y
        + levelBeta Y H (towerIdx H n (k, t)) i := by
  classical
  have hstate : ((((Y.toSym).S.P (levelSlot lc Y hT i)).map
      (MvPolynomial.eval (WinTower.param H n t))).eval y)
      = (((Y.Q (Sum.inr 0 : InitIdx 2) (levelSlotBool n i)).map
          (MvPolynomial.eval (WinTower.param H n t))).eval y) := rfl
  rw [hstate]
  have hmem : ((Sum.inr 0 : InitIdx 2), levelSlotBool n i) ∈ Y.H :=
    hT.2 (levelSlotBool n i) ((boolOfFinset_ne_zero_iff _).mpr (i1Symm n i).2)
  obtain ⟨-, -, hdeg, hlc⟩ := hT.1 ((Sum.inr 0 : InitIdx 2), levelSlotBool n i) hmem
  have hdeg1 : (Y.Q (Sum.inr 0 : InitIdx 2) (levelSlotBool n i)).natDegree = 1 := by
    simpa using hdeg
  have hL : (((Y.Q (Sum.inr 0 : InitIdx 2) (levelSlotBool n i)).map
      (MvPolynomial.eval (WinTower.param H n t))).eval y)
      = MvPolynomial.eval (WinTower.param H n t)
          ((Y.Q (Sum.inr 0 : InitIdx 2) (levelSlotBool n i)).coeff 1) * y
        + MvPolynomial.eval (WinTower.param H n t)
          ((Y.Q (Sum.inr 0 : InitIdx 2) (levelSlotBool n i)).coeff 0) :=
    eval_map_coeff_eq _ hdeg1.le _ y
  have hc1 : (Y.Q (Sum.inr 0 : InitIdx 2) (levelSlotBool n i)).coeff 1
      = MvPolynomial.C (2 : ℤ) * MvPolynomial.C lc * HistData.shift (levelSlotBool n i) := by
    have h2 := Polynomial.coeff_natDegree
      (p := Y.Q (Sum.inr 0 : InitIdx 2) (levelSlotBool n i))
    rw [hdeg1] at h2
    rw [h2, hlc]
    simp
  have hfil : (Finset.univ.filter (fun s : Fin n => levelSlotBool n i s))
      = (i1Symm n i).val := by
    show finsetOfBool (levelSlotBool n i) = (i1Symm n i).val
    rw [levelSlotBool, finsetOfBool_boolOfFinset]
  have hcoeff1 : MvPolynomial.eval (WinTower.param H n t)
        ((Y.Q (Sum.inr 0 : InitIdx 2) (levelSlotBool n i)).coeff 1)
      = 2 * lc * ∑ s ∈ (i1Symm n i).val, WinTower.param H n t s := by
    rw [hc1]
    simp only [map_mul, MvPolynomial.eval_C, histShift_eval]
    rw [hfil]
  have hbeta : levelBeta Y H (towerIdx H n (k, t)) i
      = MvPolynomial.eval (WinTower.param H n t)
          ((Y.Q (Sum.inr 0 : InitIdx 2) (levelSlotBool n i)).coeff 0) := by
    rw [levelBeta, towerIdx_one]
    rw [show (fun s : Fin n => WinTower.param H n t s) = WinTower.param H n t from rfl]
    rw [towerOf_param]
  have hdir : petDir (levelOneDatum n) 2 lc (towerIdx H n (k, t)) i
      = 2 * lc * ∑ s ∈ (i1Symm n i).val, WinTower.param H n t s := by
    rw [petDir_levelOne, towerIdx_one]
  rw [hL, hcoeff1, hdir, hbeta]

/-! ## 4. The parameter families of the tower and of the parameter box -/

lemma towerIdx_mem_parBox (H : ℕ) (p : Fin (2 * H + 1) × WinTower H n) :
    towerIdx H n p ∈ (levelOneDatum n).parBox 2 H := by
  rw [IdxDatum.mem_parBox, Fin.forall_fin_two]
  refine ⟨?_, ?_⟩
  · intro s
    rw [towerIdx_zero]
    exact IdxDatum.boxVal_mem H p.1
  · intro s
    rw [towerIdx_one]
    exact abs_le.mp (param_abs_le H n p.2 s)

lemma towerIdx_surj (H : ℕ) {a : (levelOneDatum n).Idx 2}
    (ha : a ∈ (levelOneDatum n).parBox 2 H) : ∃ p, towerIdx H n p = a := by
  rw [IdxDatum.mem_parBox] at ha
  have h0 := ha 0 PUnit.unit
  have h1 : ∀ s : Fin n, -(H : ℤ) ≤ a 1 s ∧ a 1 s ≤ H := fun s => ha 1 s
  set p : Fin (2 * H + 1) × WinTower H n :=
    (winValInv H (a 0 PUnit.unit), towerOf H n (fun s => a 1 s)) with hpdef
  refine ⟨p, ?_⟩
  have hk : IdxDatum.boxVal H (winValInv H (a 0 PUnit.unit)) = a 0 PUnit.unit :=
    winVal_winValInv h0.1 h0.2
  have ht : WinTower.param H n (towerOf H n (fun s => a 1 s)) = fun s => a 1 s :=
    param_towerOf H n _ h1
  have hfun : ∀ j : Fin 2, towerIdx H n p j = a j := by
    rw [Fin.forall_fin_two]
    refine ⟨?_, ?_⟩
    · funext s
      rw [towerIdx_zero]
      show IdxDatum.boxVal H (winValInv H (a 0 PUnit.unit)) = a 0 s
      rw [hk]
      exact congrArg (fun z => a 0 z) (Subsingleton.elim PUnit.unit s)
    · funext s
      rw [towerIdx_one]
      exact congrFun ht s
  exact _root_.funext hfun

/-- `linCore` only depends on the level-`1` part of its parameter family. -/
lemma linCore_level_indep (N M : ℕ) (lc : ℤ) (Ftop : ℤ → ℂ)
    (b : Fin (Fintype.card ((levelOneDatum n).I 1)) → Bool)
    (β : (levelOneDatum n).Idx 2 → Fin (Fintype.card ((levelOneDatum n).I 1)) → ℤ)
    (hβ : ∀ a a', (∀ s, a 1 s = a' 1 s) → ∀ i, β a i = β a' i)
    {a a' : (levelOneDatum n).Idx 2} (h : ∀ s, a 1 s = a' 1 s) :
    linCore (levelOneDatum n) 2 lc N M Ftop b β a
      = linCore (levelOneDatum n) 2 lc N M Ftop b β a' := by
  classical
  have hsum : ∀ i : Fin (Fintype.card ((levelOneDatum n).I 1)),
      (∑ s ∈ (i1Symm n i).val, a 1 s) = ∑ s ∈ (i1Symm n i).val, a' 1 s :=
    fun i => Finset.sum_congr rfl (fun s _ => h s)
  unfold linCore
  refine congrArg (fun z => ((N : ℂ) * (M : ℂ))⁻¹ * z) ?_
  refine tsum_congr (fun x => ?_)
  refine congrArg (fun z => Ftop x * z) ?_
  refine Finset.sum_congr rfl (fun y _ => ?_)
  refine Finset.prod_congr rfl (fun i _ => ?_)
  rw [petDir_levelOne, petDir_levelOne, hsum i, hβ a a' h i]

/-! ## 5. The correlation of the terminal state -/

lemma star_histCorr {n : ℕ} (Y : HistData 2 n) (H N M : ℕ) (G : (Y.toSym).S.ι → ℤ → ℂ)
    (g : WinTower H n → ℤ → ℂ) (t : WinTower H n) :
    star (histCorr Y H N M G g t)
      = ((N : ℂ) * (M : ℂ))⁻¹ * ∑' x : ℤ, star (g t x) *
          ∑ y ∈ Finset.Icc 1 M, ∏ i : (Y.toSym).S.ι,
            star (G i (x + ((((Y.toSym).S.P i).map
              (MvPolynomial.eval (WinTower.param H n t))).eval (y : ℤ)))) := by
  have hterm : ∀ x : ℤ, star (g t x * ∑ y ∈ Finset.Icc 1 M, ∏ i : (Y.toSym).S.ι,
        G i (x + ((((Y.toSym).S.P i).map
          (MvPolynomial.eval (WinTower.param H n t))).eval (y : ℤ))))
      = star (g t x) * ∑ y ∈ Finset.Icc 1 M, ∏ i : (Y.toSym).S.ι,
        star (G i (x + ((((Y.toSym).S.P i).map
          (MvPolynomial.eval (WinTower.param H n t))).eval (y : ℤ)))) := by
    intro x
    rw [star_mul', star_sum]
    refine congrArg (fun z => star (g t x) * z) ?_
    refine Finset.sum_congr rfl (fun y _ => ?_)
    rw [star_prod]
  unfold histCorr
  rw [star_mul', tsum_star]
  rw [show star ((N : ℂ) * (M : ℂ))⁻¹ = ((N : ℂ) * (M : ℂ))⁻¹ from by simp]
  rw [tsum_congr hterm]

/-- `star (if b then star z else z) = if !b then star z else z`. -/
lemma star_ite (b : Bool) (z : ℂ) : star (if b then star z else z) = if !b then star z else z := by
  cases b <;> simp

/-- **The comparison of the correlations.**  The modulus of the state's correlation at a tower
point is the modulus of `linCore` at the corresponding level-`2` parameter family. -/
lemma histCorr_eq_linCore {n : ℕ} {lc : ℤ} {Y : HistData 2 n} (hT : Phase1Terminal 2 n lc Y)
    (H N M : ℕ) (Ftop : ℤ → ℂ) (G : (Y.toSym).S.ι → ℤ → ℂ) (g : WinTower H n → ℤ → ℂ)
    (c₀ : Bool)
    (htop : ∀ i, (∀ x, G i x = Ftop x) ∨ (∀ x, G i x = star (Ftop x)))
    (hg : ∀ a x, g a x = (if c₀ then star (Ftop x) else Ftop x))
    (t : WinTower H n) (k : Fin (2 * H + 1)) :
    ‖histCorr Y H N M G g t‖
      = ‖linCore (levelOneDatum n) 2 lc N M Ftop (bOf hT c₀ Ftop G) (levelBeta Y H)
          (towerIdx H n (k, t))‖ := by
  classical
  have hmain : histCorr Y H N M G g t
        = linCore (levelOneDatum n) 2 lc N M Ftop (bOf hT c₀ Ftop G) (levelBeta Y H)
            (towerIdx H n (k, t))
      ∨ star (histCorr Y H N M G g t)
        = linCore (levelOneDatum n) 2 lc N M Ftop (bOf hT c₀ Ftop G) (levelBeta Y H)
            (towerIdx H n (k, t)) := by
    cases c₀ with
    | false =>
      left
      unfold histCorr linCore
      refine congrArg (fun z => ((N : ℂ) * (M : ℂ))⁻¹ * z) ?_
      refine tsum_congr (fun x => ?_)
      have hgx : g t x = Ftop x := by simpa using hg t x
      rw [hgx]
      refine congrArg (fun z => Ftop x * z) ?_
      refine Finset.sum_congr rfl (fun y _ => ?_)
      rw [prod_slots_eq (lc := lc) Y hT (F := fun i => G i (x + ((((Y.toSym).S.P i).map
        (MvPolynomial.eval (WinTower.param H n t))).eval (y : ℤ))))]
      refine Finset.prod_congr rfl (fun i' _ => ?_)
      rw [levelPoly_eval hT H t k i' y,
        sGOf_spec Ftop G htop (levelSlot lc Y hT i'), bOf_false]
    | true =>
      right
      rw [star_histCorr]
      unfold linCore
      refine congrArg (fun z => ((N : ℂ) * (M : ℂ))⁻¹ * z) ?_
      refine tsum_congr (fun x => ?_)
      have hgx : star (g t x) = Ftop x := by
        rw [hg t x]; simp
      rw [hgx]
      refine congrArg (fun z => Ftop x * z) ?_
      refine Finset.sum_congr rfl (fun y _ => ?_)
      rw [prod_slots_eq (lc := lc) Y hT (F := fun i => star (G i (x + ((((Y.toSym).S.P i).map
        (MvPolynomial.eval (WinTower.param H n t))).eval (y : ℤ)))))]
      refine Finset.prod_congr rfl (fun i' _ => ?_)
      rw [levelPoly_eval hT H t k i' y,
        sGOf_spec Ftop G htop (levelSlot lc Y hT i'), star_ite, bOf_true]
  rcases hmain with h | h
  · rw [h]
  · rw [← h, norm_star]

/-! ## 6. The weights -/

lemma muL_le_inv (H : ℕ) (hH : 1 ≤ H) (x : ℤ) : Work.Peluse.muL H x ≤ ((H : ℝ))⁻¹ := by
  rw [Work.Peluse.muL]
  have hcard : ((((((Finset.Icc 1 H).product (Finset.Icc 1 H)).filter
      (fun p : ℕ × ℕ => (p.1 : ℤ) - (p.2 : ℤ) = x)).card : ℕ) : ℝ)) ≤ (H : ℝ) := by
    have hle : (((Finset.Icc 1 H).product (Finset.Icc 1 H)).filter
        (fun p : ℕ × ℕ => (p.1 : ℤ) - (p.2 : ℤ) = x)).card ≤ (Finset.Icc 1 H).card := by
      refine Finset.card_le_card_of_injOn (fun p : ℕ × ℕ => p.1) ?_ ?_
      · intro p hp
        have hp' : p ∈ (((Finset.Icc 1 H).product (Finset.Icc 1 H)).filter
            (fun p : ℕ × ℕ => (p.1 : ℤ) - (p.2 : ℤ) = x)) := hp
        exact (Finset.mem_product.mp (Finset.mem_filter.mp hp').1).1
      · intro p hp q hq hpq
        have hp' : p ∈ (((Finset.Icc 1 H).product (Finset.Icc 1 H)).filter
            (fun p : ℕ × ℕ => (p.1 : ℤ) - (p.2 : ℤ) = x)) := hp
        have hq' : q ∈ (((Finset.Icc 1 H).product (Finset.Icc 1 H)).filter
            (fun p : ℕ × ℕ => (p.1 : ℤ) - (p.2 : ℤ) = x)) := hq
        have hpx : (p.1 : ℤ) - (p.2 : ℤ) = x := (Finset.mem_filter.mp hp').2
        have hqx : (q.1 : ℤ) - (q.2 : ℤ) = x := (Finset.mem_filter.mp hq').2
        have hpq' : p.1 = q.1 := hpq
        have h2 : p.2 = q.2 := by omega
        exact Prod.ext hpq' h2
    rw [Nat.card_Icc] at hle
    have h1 : H + 1 - 1 = H := by omega
    rw [h1] at hle
    exact_mod_cast hle
  calc ((H : ℝ) ^ 2)⁻¹ * (((((Finset.Icc 1 H).product (Finset.Icc 1 H)).filter
        (fun p : ℕ × ℕ => (p.1 : ℤ) - (p.2 : ℤ) = x)).card : ℕ))
      ≤ ((H : ℝ) ^ 2)⁻¹ * (H : ℝ) := mul_le_mul_of_nonneg_left hcard (by positivity)
    _ = ((H : ℝ))⁻¹ := by
        have hH0 : ((H : ℝ)) ≠ 0 := by positivity
        rw [pow_two, mul_inv, mul_assoc, inv_mul_cancel₀ hH0, mul_one]

lemma nu_le_inv (H : ℕ) (hH : 1 ≤ H) : ∀ (n : ℕ) (t : WinTower H n),
    WinTower.nu H n t ≤ ((H : ℝ))⁻¹ ^ n := by
  intro n
  induction n with
  | zero => intro t; simp [WinTower.nu]
  | succ n ih =>
    intro t
    obtain ⟨t', k⟩ := t
    rw [WinTower.nu_succ H n t' k, pow_succ]
    exact mul_le_mul (ih t') (muL_le_inv H hH _) (Work.Peluse.PET.muL_nonneg H _) (by positivity)

lemma nu_le_three (H : ℕ) (hH : 1 ≤ H) (n : ℕ) (t : WinTower H n) :
    WinTower.nu H n t ≤ (3 : ℝ) ^ n / (2 * (H : ℝ) + 1) ^ n := by
  have hH1 : (1 : ℝ) ≤ (H : ℝ) := by exact_mod_cast hH
  have h1 : ((H : ℝ))⁻¹ ≤ 3 / (2 * (H : ℝ) + 1) := by
    have hpos : (0 : ℝ) < (2 * (H : ℝ) + 1) / 3 := by positivity
    have hle : (2 * (H : ℝ) + 1) / 3 ≤ (H : ℝ) := by
      rw [div_le_iff₀ (by norm_num : (0 : ℝ) < 3)]
      linarith
    have h2 : 1 / (H : ℝ) ≤ 3 / (2 * (H : ℝ) + 1) := by
      have h3 := one_div_le_one_div_of_le hpos hle
      rwa [one_div_div] at h3
    simpa [one_div] using h2
  calc WinTower.nu H n t ≤ ((H : ℝ))⁻¹ ^ n := nu_le_inv H hH n t
    _ ≤ (3 / (2 * (H : ℝ) + 1)) ^ n := pow_le_pow_left₀ (by positivity) h1 n
    _ = (3 : ℝ) ^ n / (2 * (H : ℝ) + 1) ^ n := by
        rw [div_pow]

/-! ## 7. The parameter box -/

lemma card_parBox_le (H : ℕ) :
    ((levelOneDatum n).parBox 2 H).card ≤ (2 * H + 1) ^ (n + 1) := by
  rw [IdxDatum.parBox]
  refine le_trans Finset.card_image_le ?_
  rw [Fintype.card_piFinset]
  have hinner : ∀ j : Fin 2,
      (Fintype.piFinset fun _ : (levelOneDatum n).S j =>
        (Finset.univ : Finset (Fin (2 * H + 1)))).card
        = (2 * H + 1) ^ Fintype.card ((levelOneDatum n).S j) := by
    intro j
    rw [Fintype.card_piFinset]
    simp [Finset.prod_const]
  simp only [hinner]
  rw [Fin.prod_univ_two]
  have h0 : Fintype.card ((levelOneDatum n).S 0) = 1 := Fintype.card_punit
  have h1 : Fintype.card ((levelOneDatum n).S 1) = n := Fintype.card_fin n
  have hgoal : (2 * H + 1) ^ Fintype.card ((levelOneDatum n).S 0) *
      (2 * H + 1) ^ Fintype.card ((levelOneDatum n).S 1) = (2 * H + 1) ^ (n + 1) := by
    rw [h0, h1, pow_one, pow_succ, mul_comm]
  exact le_of_eq hgoal

/-- The parameter box dominates `(2H+1)` copies of the tower sum. -/
lemma sum_parBox_ge (H : ℕ) (lc : ℤ) (N M : ℕ) (Ftop : ℤ → ℂ)
    (b : Fin (Fintype.card ((levelOneDatum n).I 1)) → Bool)
    (β : (levelOneDatum n).Idx 2 → Fin (Fintype.card ((levelOneDatum n).I 1)) → ℤ)
    (hβ : ∀ a a', (∀ s, a 1 s = a' 1 s) → ∀ i, β a i = β a' i) :
    (2 * (H : ℝ) + 1) * ∑ t : WinTower H n,
        ‖linCore (levelOneDatum n) 2 lc N M Ftop b β (towerIdx H n (0, t))‖
      ≤ ∑ a ∈ (levelOneDatum n).parBox 2 H,
          ‖linCore (levelOneDatum n) 2 lc N M Ftop b β a‖ := by
  classical
  have hsub : Finset.univ.image (towerIdx H n) ⊆ (levelOneDatum n).parBox 2 H := by
    intro a ha
    obtain ⟨p, -, rfl⟩ := Finset.mem_image.mp ha
    exact towerIdx_mem_parBox H p
  have hstep1 : ∑ a ∈ Finset.univ.image (towerIdx H n),
        ‖linCore (levelOneDatum n) 2 lc N M Ftop b β a‖
      ≤ ∑ a ∈ (levelOneDatum n).parBox 2 H,
          ‖linCore (levelOneDatum n) 2 lc N M Ftop b β a‖ :=
    Finset.sum_le_sum_of_subset_of_nonneg hsub (fun a _ _ => norm_nonneg _)
  have hsum_image : (∑ a ∈ Finset.univ.image (towerIdx H n),
        ‖linCore (levelOneDatum n) 2 lc N M Ftop b β a‖)
      = ∑ p : Fin (2 * H + 1) × WinTower H n,
          ‖linCore (levelOneDatum n) 2 lc N M Ftop b β (towerIdx H n p)‖ :=
    Finset.sum_image (f := fun a : (levelOneDatum n).Idx 2 =>
        ‖linCore (levelOneDatum n) 2 lc N M Ftop b β a‖)
      (s := (Finset.univ : Finset (Fin (2 * H + 1) × WinTower H n)))
      (g := towerIdx H n) (fun x _ y _ hxy => towerIdx_injective H n hxy)
  have hprod : (∑ p : Fin (2 * H + 1) × WinTower H n,
        ‖linCore (levelOneDatum n) 2 lc N M Ftop b β (towerIdx H n p)‖)
      = ∑ k : Fin (2 * H + 1), ∑ t : WinTower H n,
          ‖linCore (levelOneDatum n) 2 lc N M Ftop b β (towerIdx H n (k, t))‖ :=
    Fintype.sum_prod_type _
  have hindep : ∀ k : Fin (2 * H + 1), (∑ t : WinTower H n,
        ‖linCore (levelOneDatum n) 2 lc N M Ftop b β (towerIdx H n (k, t))‖)
      = ∑ t : WinTower H n,
          ‖linCore (levelOneDatum n) 2 lc N M Ftop b β (towerIdx H n (0, t))‖ := by
    intro k
    refine Finset.sum_congr rfl (fun t _ => ?_)
    rw [linCore_level_indep N M lc Ftop b β hβ (a := towerIdx H n (k, t))
      (a' := towerIdx H n (0, t)) (fun s => by rw [towerIdx_one, towerIdx_one])]
  have hconst : (∑ _k : Fin (2 * H + 1), (∑ t : WinTower H n,
        ‖linCore (levelOneDatum n) 2 lc N M Ftop b β (towerIdx H n (0, t))‖))
      = (2 * (H : ℝ) + 1) * ∑ t : WinTower H n,
          ‖linCore (levelOneDatum n) 2 lc N M Ftop b β (towerIdx H n (0, t))‖ := by
    rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    push_cast
    ring
  calc (2 * (H : ℝ) + 1) * ∑ t : WinTower H n,
        ‖linCore (levelOneDatum n) 2 lc N M Ftop b β (towerIdx H n (0, t))‖
      = ∑ _k : Fin (2 * H + 1), ∑ t : WinTower H n,
          ‖linCore (levelOneDatum n) 2 lc N M Ftop b β (towerIdx H n (0, t))‖ :=
        hconst.symm
    _ = ∑ k : Fin (2 * H + 1), ∑ t : WinTower H n,
          ‖linCore (levelOneDatum n) 2 lc N M Ftop b β (towerIdx H n (k, t))‖ :=
        Finset.sum_congr rfl (fun k _ => (hindep k).symm)
    _ = ∑ p : Fin (2 * H + 1) × WinTower H n,
          ‖linCore (levelOneDatum n) 2 lc N M Ftop b β (towerIdx H n p)‖ := hprod.symm
    _ = ∑ a ∈ Finset.univ.image (towerIdx H n),
          ‖linCore (levelOneDatum n) 2 lc N M Ftop b β a‖ := hsum_image.symm
    _ ≤ ∑ a ∈ (levelOneDatum n).parBox 2 H,
          ‖linCore (levelOneDatum n) 2 lc N M Ftop b β a‖ := hstep1

/-! ## 8. The comparison theorem -/

theorem level1Compare_aux {n : ℕ} (hn : 2 ≤ n) (lc : ℤ) (Y : HistData 2 n)
    (hT : Phase1Terminal 2 n lc Y) (N M : ℕ) (H : ℕ) (γ' : ℝ) (Ftop : ℤ → ℂ)
    (G : (Y.toSym).S.ι → ℤ → ℂ) (g : WinTower H n → ℤ → ℂ)
    (htop : ∀ i, (∀ x, G i x = Ftop x) ∨ (∀ x, G i x = star (Ftop x)))
    (hg : ∃ c₀ : Bool, ∀ a x, g a x = (if c₀ then star (Ftop x) else Ftop x))
    {c D : ℕ} (hSB : (histPet Y H G g).toState.ShiftBound N M c D)
    (hc : 1 ≤ c) (hH : 1 ≤ H) {B : ℝ}
    (hlam : B ≤ (histPet Y H G g).toState.lam N M) :
    ∃ (b : Fin (Fintype.card ((levelOneDatum n).I 1)) → Bool)
      (β : (levelOneDatum n).Idx 2 → Fin (Fintype.card ((levelOneDatum n).I 1)) → ℤ),
      (∀ a ∈ (levelOneDatum n).parBox 2 H,
          ∀ i : Fin (Fintype.card ((levelOneDatum n).I 1)), ∀ y ∈ Finset.Icc 1 M,
            |petDir (levelOneDatum n) 2 lc a i * (y : ℤ) + β a i| ≤ (D : ℤ) * (N : ℤ)) ∧
      B ≤ (3 : ℝ) ^ n * linFamAvg (levelOneDatum n) 2 lc N M H Ftop b β := by
  classical
  obtain ⟨c₀, hg₀⟩ := hg
  refine ⟨bOf hT c₀ Ftop G, levelBeta Y H, ?hshift, ?havg⟩
  · intro a ha i y hy
    obtain ⟨p, hp⟩ := towerIdx_surj (n := n) H ha
    rw [← hp]
    have hy1 : (1 : ℤ) ≤ (y : ℤ) := by exact_mod_cast (Finset.mem_Icc.mp hy).1
    have hy2 : (y : ℤ) ≤ (M : ℤ) := by exact_mod_cast (Finset.mem_Icc.mp hy).2
    have hz : |(y : ℤ)| ≤ (c : ℤ) * (M : ℤ) := by
      rw [abs_of_nonneg (by omega)]
      have hc1 : (1 : ℤ) ≤ (c : ℤ) := by exact_mod_cast hc
      have hM0 : (0 : ℤ) ≤ (M : ℤ) := by omega
      nlinarith
    have hb := hSB (levelSlot lc Y hT i) p.2 (y : ℤ) hz
    have hb' : |((((Y.toSym).S.P (levelSlot lc Y hT i)).map
        (MvPolynomial.eval (WinTower.param H n p.2))).eval (y : ℤ))|
        ≤ (D : ℤ) * (N : ℤ) := hb
    rw [levelPoly_eval hT H p.2 p.1 i (y : ℤ)] at hb'
    rw [hp] at hb' ⊢
    exact hb'
  · have hlam' : B ≤ ∑ t : WinTower H n, WinTower.nu H n t * ‖histCorr Y H N M G g t‖ :=
      hlam
    have hX : ∀ t : WinTower H n, ‖histCorr Y H N M G g t‖
        = ‖linCore (levelOneDatum n) 2 lc N M Ftop (bOf hT c₀ Ftop G) (levelBeta Y H)
            (towerIdx H n (0, t))‖ :=
      fun t => histCorr_eq_linCore hT H N M Ftop G g c₀ htop hg₀ t 0
    have hstep2 : (∑ t : WinTower H n, WinTower.nu H n t * ‖histCorr Y H N M G g t‖)
        ≤ ((3 : ℝ) ^ n / (2 * (H : ℝ) + 1) ^ n) *
            ∑ t : WinTower H n, ‖histCorr Y H N M G g t‖ := by
      rw [Finset.mul_sum]
      refine Finset.sum_le_sum (fun t _ => ?_)
      exact mul_le_mul_of_nonneg_right (nu_le_three H hH n t) (norm_nonneg _)
    have hstep3 : (∑ t : WinTower H n, ‖histCorr Y H N M G g t‖)
        = ∑ t : WinTower H n,
            ‖linCore (levelOneDatum n) 2 lc N M Ftop (bOf hT c₀ Ftop G) (levelBeta Y H)
              (towerIdx H n (0, t))‖ :=
      Finset.sum_congr rfl (fun t _ => hX t)
    have hβ : ∀ a a' : (levelOneDatum n).Idx 2, (∀ s, a 1 s = a' 1 s) →
        ∀ i, levelBeta Y H a i = levelBeta Y H a' i := by
      intro a a' h i
      have h2 : (fun s : Fin n => a 1 s) = fun s => a' 1 s := _root_.funext h
      unfold levelBeta
      rw [h2]
      rfl
    have hpar := sum_parBox_ge H lc N M Ftop (bOf hT c₀ Ftop G) (levelBeta Y H) hβ
    have hcard_pos : (0 : ℝ) < (((levelOneDatum n).parBox 2 H).card : ℝ) := by
      have hmem : towerIdx H n (0, towerOf H n (fun _ : Fin n => 0)) ∈
          (levelOneDatum n).parBox 2 H := towerIdx_mem_parBox H _
      have : 0 < ((levelOneDatum n).parBox 2 H).card := Finset.card_pos.mpr ⟨_, hmem⟩
      exact_mod_cast this
    have hcard_le : (((levelOneDatum n).parBox 2 H).card : ℝ)
        ≤ (2 * (H : ℝ) + 1) ^ (n + 1) := by
      have h := card_parBox_le (n := n) H
      have hcast : (((2 * H + 1) ^ (n + 1) : ℕ) : ℝ) = (2 * (H : ℝ) + 1) ^ (n + 1) := by
        push_cast
        ring
      rw [← hcast]
      exact_mod_cast h
    have hinv : ((2 * (H : ℝ) + 1) ^ (n + 1))⁻¹
        ≤ ((((levelOneDatum n).parBox 2 H).card : ℝ))⁻¹ := by
      simpa using one_div_le_one_div_of_le hcard_pos hcard_le
    have hlin : linFamAvg (levelOneDatum n) 2 lc N M H Ftop (bOf hT c₀ Ftop G) (levelBeta Y H)
        = ((((levelOneDatum n).parBox 2 H).card : ℝ))⁻¹ *
            ∑ a ∈ (levelOneDatum n).parBox 2 H,
              ‖linCore (levelOneDatum n) 2 lc N M Ftop (bOf hT c₀ Ftop G) (levelBeta Y H) a‖ :=
      linFamAvg_eq_card_mul_sum (levelOneDatum n) 2 lc N M H Ftop (bOf hT c₀ Ftop G)
        (levelBeta Y H)
    have hlast : (3 : ℝ) ^ n / (2 * (H : ℝ) + 1) ^ n *
          ∑ t : WinTower H n,
            ‖linCore (levelOneDatum n) 2 lc N M Ftop (bOf hT c₀ Ftop G) (levelBeta Y H)
              (towerIdx H n (0, t))‖
        ≤ (3 : ℝ) ^ n * linFamAvg (levelOneDatum n) 2 lc N M H Ftop (bOf hT c₀ Ftop G)
            (levelBeta Y H) := by
      rw [hlin]
      have hSnn : (0 : ℝ) ≤ ∑ a ∈ (levelOneDatum n).parBox 2 H,
          ‖linCore (levelOneDatum n) 2 lc N M Ftop (bOf hT c₀ Ftop G) (levelBeta Y H) a‖ :=
        Finset.sum_nonneg (fun a _ => norm_nonneg _)
      have hstepA : (3 : ℝ) ^ n / (2 * (H : ℝ) + 1) ^ n *
            ∑ t : WinTower H n,
              ‖linCore (levelOneDatum n) 2 lc N M Ftop (bOf hT c₀ Ftop G) (levelBeta Y H)
                (towerIdx H n (0, t))‖
          = (3 : ℝ) ^ n * ((2 * (H : ℝ) + 1) ^ (n + 1))⁻¹ *
              ((2 * (H : ℝ) + 1) * ∑ t : WinTower H n,
                ‖linCore (levelOneDatum n) 2 lc N M Ftop (bOf hT c₀ Ftop G) (levelBeta Y H)
                  (towerIdx H n (0, t))‖) := by
        rw [pow_succ]
        field_simp
      rw [hstepA]
      refine le_trans (mul_le_mul_of_nonneg_left hpar (by positivity)) ?_
      refine le_trans (mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left hinv (by positivity)) hSnn) ?_
      rw [mul_assoc]
    calc B ≤ ∑ t : WinTower H n, WinTower.nu H n t * ‖histCorr Y H N M G g t‖ := hlam'
      _ ≤ ((3 : ℝ) ^ n / (2 * (H : ℝ) + 1) ^ n) *
            ∑ t : WinTower H n, ‖histCorr Y H N M G g t‖ := hstep2
      _ = ((3 : ℝ) ^ n / (2 * (H : ℝ) + 1) ^ n) *
            ∑ t : WinTower H n,
              ‖linCore (levelOneDatum n) 2 lc N M Ftop (bOf hT c₀ Ftop G) (levelBeta Y H)
                (towerIdx H n (0, t))‖ := by rw [hstep3]
      _ ≤ (3 : ℝ) ^ n * linFamAvg (levelOneDatum n) 2 lc N M H Ftop (bOf hT c₀ Ftop G)
            (levelBeta Y H) := hlast

theorem level1Compare {n : ℕ} (hn : 2 ≤ n) (lc : ℤ) (Y : HistData 2 n)
    (hT : Phase1Terminal 2 n lc Y) (N M : ℕ) (γ' : ℝ) (Ftop : ℤ → ℂ)
    (G : (Y.toSym).S.ι → ℤ → ℂ) (g : WinTower ⌊γ' * (M : ℝ)⌋.toNat n → ℤ → ℂ)
    (htop : ∀ i, (∀ x, G i x = Ftop x) ∨ (∀ x, G i x = star (Ftop x)))
    (hg : ∃ c₀ : Bool, ∀ a x, g a x = (if c₀ then star (Ftop x) else Ftop x))
    {c D : ℕ} (hSB : (histPet Y ⌊γ' * (M : ℝ)⌋.toNat G g).toState.ShiftBound N M c D)
    (hc : 1 ≤ c) (hH : 1 ≤ ⌊γ' * (M : ℝ)⌋.toNat) {B : ℝ}
    (hlam : B ≤ (histPet Y ⌊γ' * (M : ℝ)⌋.toNat G g).toState.lam N M) :
    ∃ (b : Fin (Fintype.card ((levelOneDatum n).I 1)) → Bool)
      (β : (levelOneDatum n).Idx 2 → Fin (Fintype.card ((levelOneDatum n).I 1)) → ℤ),
      (∀ a ∈ (levelOneDatum n).parBox 2 ⌊γ' * (M : ℝ)⌋.toNat,
          ∀ i : Fin (Fintype.card ((levelOneDatum n).I 1)), ∀ y ∈ Finset.Icc 1 M,
            |petDir (levelOneDatum n) 2 lc a i * (y : ℤ) + β a i| ≤ (D : ℤ) * (N : ℤ)) ∧
      B ≤ (3 : ℝ) ^ n * linFamAvg (levelOneDatum n) 2 lc N M ⌊γ' * (M : ℝ)⌋.toNat Ftop b β :=
  level1Compare_aux hn lc Y hT N M ⌊γ' * (M : ℝ)⌋.toNat γ' Ftop G g htop hg hSB hc hH hlam

end

end Work.Peluse.UControl
