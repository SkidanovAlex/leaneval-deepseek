import Mathlib
import Submission.Work.LinnikBurgess.burgess_lead_defs
import Submission.Work.LinnikBurgess.gaussTwoLocal_defs
import Submission.Work.LinnikBurgess.gaussQuad_bound
import Submission.Work.LinnikBurgess.peel_gauss
import Submission.Work.LinnikBurgess.vcap_two_gamma
import Submission.Work.LinnikBurgess.dvd_natCast_val_iff

/-!
# Lemma A (U2): the two-term stationary phase for the cubic correlation at a prime power

`Work.LinnikBurgess.corr6_primePow_gaussTwo_le` bounds the cubic character correlation over
`ZMod (p^e)` (`p` an odd prime, `2m ≤ e ≤ 3m`) by `p^(e/2) · gaussTwoRHS p e m a b`.

The proof decomposes `x = y + p^m w` (two `p`-adic digits), peels the correlation to a constant
times the quadratic Gauss sum `∑_w θ^((α w + γ w²).val)` (`peel_gauss`), bounds that Gauss sum
(`gaussQuad_bound`), and sums over the `p^m` values of the low digit `y`.
-/

open scoped BigOperators
open Classical

namespace Work.LinnikBurgess


/-- Reindexing a `ZMod`-sum as a range sum. -/
lemma zmod_sum_range_aux (N : ℕ) [NeZero N] (g : ZMod N → ℂ) :
    (∑ x : ZMod N, g x) = ∑ j ∈ Finset.range N, g ((j : ℕ) : ZMod N) := by
  have hbij : Function.Bijective (fun i : Fin N => ((i : ℕ) : ZMod N)) := by
    refine ⟨fun a b hab => ?_, fun x => ⟨⟨x.val, ZMod.val_lt x⟩, ?_⟩⟩
    · refine Fin.ext ?_
      have h1 := (ZMod.natCast_eq_natCast_iff (a : ℕ) (b : ℕ) N).mp hab
      rw [Nat.ModEq] at h1
      have ha := a.isLt; have hb := b.isLt
      simp only [Nat.mod_eq_of_lt ha, Nat.mod_eq_of_lt hb] at h1
      exact h1
    · show ((x.val : ℕ) : ZMod N) = x
      exact ZMod.natCast_zmod_val x
  rw [Finset.sum_range]
  exact (Fintype.sum_bijective _ hbij (fun i : Fin N => g ((i : ℕ) : ZMod N)) g (fun i => rfl)).symm

/-- `IsUnit` of a natural number cast into `ZMod (p^e)` is equivalent to non-divisibility by `p`. -/
lemma zmod_isUnit_natCast_iff {p e n : ℕ} [Fact p.Prime] (he : 1 ≤ e) :
    IsUnit (((n : ℕ) : ZMod (p ^ e))) ↔ ¬ p ∣ n := by
  rw [ZMod.isUnit_iff_coprime, Nat.coprime_pow_right_iff (by omega : 0 < e), Nat.coprime_comm,
    (Fact.out : p.Prime).coprime_iff_not_dvd]

/-- The correlation summand. -/
noncomputable def corrG (p e : ℕ) (χ : DirichletCharacter ℂ (p ^ e)) (a b : Fin 3 → ℕ)
    (x : ZMod (p ^ e)) : ℂ :=
  χ (∏ l : Fin 3, (x + (a l : ZMod (p ^ e))))
    * (starRingEnd ℂ) (χ (∏ l : Fin 3, (x + (b l : ZMod (p ^ e)))))

/-- The correlation summand vanishes when some shift is not a unit at `p`. -/
lemma vanish_nonunit {p e m : ℕ} [Fact p.Prime] (hm : 1 ≤ m) (h2m : 2 * m ≤ e)
    (χ : DirichletCharacter ℂ (p ^ e)) (a b : Fin 3 → ℕ) (y : ℕ) (hy : ¬ UnitAt p y a b)
    (w : ℕ) :
    χ (∏ l : Fin 3, (((y + p ^ m * w : ℕ) : ZMod (p ^ e)) + ((a l : ℕ) : ZMod (p ^ e))))
      * (starRingEnd ℂ)
          (χ (∏ l : Fin 3, (((y + p ^ m * w : ℕ) : ZMod (p ^ e)) + ((b l : ℕ) : ZMod (p ^ e)))))
        = 0 := by
  have he1 : 1 ≤ e := by omega
  have hpw : p ∣ p ^ m * w := (dvd_pow_self p (by omega : m ≠ 0)).mul_right w
  rw [UnitAt] at hy
  push_neg at hy
  obtain ⟨l, hl⟩ := hy
  have hfacA : ∀ l' : Fin 3,
      (((y + p ^ m * w : ℕ) : ZMod (p ^ e)) + ((a l' : ℕ) : ZMod (p ^ e)))
        = (((y + p ^ m * w) + a l' : ℕ) : ZMod (p ^ e)) := by
    intro l'; simp only [Nat.cast_add]
  have hfacB : ∀ l' : Fin 3,
      (((y + p ^ m * w : ℕ) : ZMod (p ^ e)) + ((b l' : ℕ) : ZMod (p ^ e)))
        = (((y + p ^ m * w) + b l' : ℕ) : ZMod (p ^ e)) := by
    intro l'; simp only [Nat.cast_add]
  by_cases hA : p ∣ y + a l
  · have hA' : p ∣ (y + p^m * w) + a l := by
      rw [show (y + p^m * w) + a l = (y + a l) + p^m * w by ring]
      exact Nat.dvd_add hA hpw
    have hnu : ¬ IsUnit ((((y + p^m * w) + a l : ℕ)) : ZMod (p ^ e)) := by
      intro hu; exact (zmod_isUnit_natCast_iff he1).mp hu hA'
    have hprod : ¬ IsUnit
        (∏ l' : Fin 3, (((y + p ^ m * w : ℕ) : ZMod (p ^ e)) + ((a l' : ℕ) : ZMod (p ^ e)))) := by
      rw [← Finset.mul_prod_erase Finset.univ
        (fun l' : Fin 3 => (((y + p ^ m * w : ℕ) : ZMod (p ^ e)) + ((a l' : ℕ) : ZMod (p ^ e))))
        (Finset.mem_univ l)]
      intro hu
      exact hnu (hfacA l ▸ (IsUnit.mul_iff.mp hu).1)
    rw [MulChar.map_nonunit χ hprod, zero_mul]
  · have hB : p ∣ y + b l := hl hA
    have hB' : p ∣ (y + p^m * w) + b l := by
      rw [show (y + p^m * w) + b l = (y + b l) + p^m * w by ring]
      exact Nat.dvd_add hB hpw
    have hnu : ¬ IsUnit ((((y + p^m * w) + b l : ℕ)) : ZMod (p ^ e)) := by
      intro hu; exact (zmod_isUnit_natCast_iff he1).mp hu hB'
    have hprod : ¬ IsUnit
        (∏ l' : Fin 3, (((y + p ^ m * w : ℕ) : ZMod (p ^ e)) + ((b l' : ℕ) : ZMod (p ^ e)))) := by
      rw [← Finset.mul_prod_erase Finset.univ
        (fun l' : Fin 3 => (((y + p ^ m * w : ℕ) : ZMod (p ^ e)) + ((b l' : ℕ) : ZMod (p ^ e))))
        (Finset.mem_univ l)]
      intro hu
      exact hnu (hfacB l ▸ (IsUnit.mul_iff.mp hu).1)
    rw [MulChar.map_nonunit χ hprod, map_zero, mul_zero]

/-- Lemma A (U2).  Brute-force sanity first: p=5,e=6; p=7,e=5; p=3,e=6 with random shifts — the inequality holds with equality occurring. -/
theorem corr6_primePow_gaussTwo_le {p e m : ℕ} [Fact p.Prime] (hp2 : p ≠ 2) (hm : 1 ≤ m)
    (h3 : e ≤ 3 * m) (h2 : 2 * m ≤ e) (χ : DirichletCharacter ℂ (p ^ e)) (hχ : χ.IsPrimitive)
    (a b : Fin 3 → ℕ) :
    ‖∑ x : ZMod (p ^ e), χ (∏ l : Fin 3, (x + (a l : ZMod (p ^ e))))
        * (starRingEnd ℂ) (χ (∏ l : Fin 3, (x + (b l : ZMod (p ^ e)))))‖
      ≤ (p : ℝ) ^ ((e : ℝ) / 2) * gaussTwoRHS p e m a b := by
  have hp : p.Prime := Fact.out
  have hppos : 0 < p := hp.pos
  have hmle : m ≤ e := by omega
  have he1 : 1 ≤ e := by omega
  have hK1 : 1 ≤ e - m := by omega
  have hKme : p ^ e = p ^ m * p ^ (e - m) := by rw [← pow_add, Nat.add_sub_of_le hmle]
  have hpR : (0 : ℝ) < (p : ℝ) := by exact_mod_cast hppos
  set bnd : ℕ → ℝ := fun y =>
      (if UnitAt p y a b ∧ p ^ (m + vcap p (e - 2 * m) (defect2 p e a b y).val)
            ∣ (defect1 p e a b y).val
        then (p : ℝ) ^ (((vcap p (e - 2 * m) (defect2 p e a b y).val : ℕ) : ℝ) / 2) else 0)
    with hbnddef
  -- Step 1: reindex the `ZMod (p^e)`-sum as a `range` sum
  have hrange : (∑ x : ZMod (p ^ e), corrG p e χ a b x)
      = ∑ j ∈ Finset.range (p ^ e), corrG p e χ a b (((j : ℕ) : ZMod (p ^ e))) :=
    zmod_sum_range_aux (p ^ e) (corrG p e χ a b)
  -- Step 2: split `j < p^e` as `j = (j % p^m) + p^m * (j / p^m)`
  have hbij1 : (∑ j ∈ Finset.range (p ^ e), corrG p e χ a b (((j : ℕ) : ZMod (p ^ e))))
      = ∑ yw ∈ Finset.range (p ^ m) ×ˢ Finset.range (p ^ (e - m)),
          corrG p e χ a b (((yw.1 + p ^ m * yw.2 : ℕ) : ZMod (p ^ e))) := by
    refine Finset.sum_bij (fun j _ => (j % p ^ m, j / p ^ m)) ?_ ?_ ?_ ?_
    · intro j hj
      rw [Finset.mem_product, Finset.mem_range, Finset.mem_range]
      refine ⟨Nat.mod_lt _ (pow_pos hppos m), ?_⟩
      rw [Nat.div_lt_iff_lt_mul (pow_pos hppos m)]
      calc j < p ^ e := Finset.mem_range.mp hj
        _ = p ^ m * p ^ (e - m) := hKme
        _ = p ^ (e - m) * p ^ m := by ring
    · intro j1 _ j2 _ heq
      rw [Prod.mk.injEq] at heq
      obtain ⟨h1, h2⟩ := heq
      calc j1 = p ^ m * (j1 / p ^ m) + j1 % p ^ m := (Nat.div_add_mod j1 (p ^ m)).symm
        _ = p ^ m * (j2 / p ^ m) + j2 % p ^ m := by rw [h1, h2]
        _ = j2 := Nat.div_add_mod j2 (p ^ m)
    · intro yw hyw
      rw [Finset.mem_product, Finset.mem_range, Finset.mem_range] at hyw
      obtain ⟨hy, hw⟩ := hyw
      refine ⟨yw.1 + p ^ m * yw.2, ?_, ?_⟩
      · rw [Finset.mem_range]
        calc yw.1 + p ^ m * yw.2 < p ^ m + p ^ m * yw.2 := by omega
          _ = p ^ m * (yw.2 + 1) := by ring
          _ ≤ p ^ m * p ^ (e - m) := Nat.mul_le_mul_left _ (by omega)
          _ = p ^ e := hKme.symm
      · rw [Prod.mk.injEq]
        exact ⟨by rw [Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt hy],
          by rw [Nat.add_mul_div_left _ _ (pow_pos hppos m), Nat.div_eq_of_lt hy, Nat.zero_add]⟩
    · intro j _
      congr 1
      have hjj : j % p ^ m + p ^ m * (j / p ^ m) = j := by
        rw [Nat.add_comm, Nat.div_add_mod]
      rw [hjj]
  have hbij2 : (∑ yw ∈ Finset.range (p ^ m) ×ˢ Finset.range (p ^ (e - m)),
          corrG p e χ a b (((yw.1 + p ^ m * yw.2 : ℕ) : ZMod (p ^ e))))
      = ∑ y ∈ Finset.range (p ^ m), ∑ w ∈ Finset.range (p ^ (e - m)),
          corrG p e χ a b (((y + p ^ m * w : ℕ) : ZMod (p ^ e))) :=
    Finset.sum_product _ _ _
  have hbij := hbij1.trans hbij2
  -- Step 3: per-`y` bound
  have hbnd : ∀ y ∈ Finset.range (p ^ m),
      ‖∑ w ∈ Finset.range (p ^ (e - m)), corrG p e χ a b (((y + p ^ m * w : ℕ) : ZMod (p ^ e)))‖
        ≤ (p : ℝ) ^ ((e : ℝ) / 2) * bnd y := by
    intro y hy
    by_cases hunit : UnitAt p y a b
    · -- unit case: peel + Gauss sum bound
      set δ : ℕ := (defect2 p e a b y).val with hδdef
      set γ : ZMod (p ^ (e - m)) :=
        -(2 : ZMod (p ^ (e - m)))⁻¹ * ((p ^ m : ℕ) : ZMod (p ^ (e - m))) * ((δ : ℕ) : ZMod (p ^ (e - m)))
        with hγdef
      set α : ZMod (p ^ (e - m)) := (((defect1 p e a b y).val : ℕ) : ZMod (p ^ (e - m))) with hαdef
      have hconv : (∑ w : ZMod (p ^ (e - m)), corrG p e χ a b (((y + p ^ m * w.val : ℕ) : ZMod (p ^ e))))
          = ∑ w ∈ Finset.range (p ^ (e - m)),
              corrG p e χ a b (((y + p ^ m * w : ℕ) : ZMod (p ^ e))) := by
        rw [zmod_sum_range_aux (p ^ (e - m))
          (fun w : ZMod (p ^ (e - m)) => corrG p e χ a b (((y + p ^ m * w.val : ℕ) : ZMod (p ^ e))))]
        refine Finset.sum_congr rfl (fun j hj => ?_)
        congr 1
        rw [ZMod.val_natCast, Nat.mod_eq_of_lt (Finset.mem_range.mp hj)]
      have hsummand : ∀ w : ZMod (p ^ (e - m)),
          corrG p e χ a b (((y + p ^ m * w.val : ℕ) : ZMod (p ^ e)))
            = χ (∏ l : Fin 3, (((y : ℕ) : ZMod (p ^ e)) + ((p ^ m : ℕ) : ZMod (p ^ e))
                  * ((w.val : ℕ) : ZMod (p ^ e)) + (a l : ZMod (p ^ e))))
              * (starRingEnd ℂ) (χ (∏ l : Fin 3, (((y : ℕ) : ZMod (p ^ e)) + ((p ^ m : ℕ) : ZMod (p ^ e))
                  * ((w.val : ℕ) : ZMod (p ^ e)) + (b l : ZMod (p ^ e))))) := by
        intro w
        have ha : (∏ l : Fin 3, ((((y + p ^ m * w.val : ℕ) : ZMod (p ^ e)) + (a l : ZMod (p ^ e)))))
            = ∏ l : Fin 3, (((y : ℕ) : ZMod (p ^ e)) + ((p ^ m : ℕ) : ZMod (p ^ e))
                * ((w.val : ℕ) : ZMod (p ^ e)) + (a l : ZMod (p ^ e))) := by
          apply Finset.prod_congr rfl
          intro l _; push_cast; ring
        have hb : (∏ l : Fin 3, ((((y + p ^ m * w.val : ℕ) : ZMod (p ^ e)) + (b l : ZMod (p ^ e)))))
            = ∏ l : Fin 3, (((y : ℕ) : ZMod (p ^ e)) + ((p ^ m : ℕ) : ZMod (p ^ e))
                * ((w.val : ℕ) : ZMod (p ^ e)) + (b l : ZMod (p ^ e))) := by
          apply Finset.prod_congr rfl
          intro l _; push_cast; ring
        simp only [corrG]
        rw [ha, hb]
      have hpeel := peel_gauss hp2 hm h3 h2 χ a b y hunit
      have hgq := gaussQuad_bound (p := p) (K := e - m) hp2 hK1 (psiFun p e m χ 1)
        (psiFun_one_isPrimitiveRoot hp2 hm h3 h2 χ hχ) α γ
      have hvcapg : vcap p (e - m) (2 * γ).val = m + vcap p (e - 2 * m) δ := by
        rw [hγdef, hδdef]
        exact vcap_two_gamma hp2 hm h2 (defect2 p e a b y).val (ZMod.val_lt _)
      have hgle : m + vcap p (e - 2 * m) δ ≤ e - m := by
        have := vcap_le p (e - 2 * m) δ
        omega
      have hcond : (p ^ vcap p (e - m) (2 * γ).val ∣ α.val)
          ↔ (p ^ (m + vcap p (e - 2 * m) δ) ∣ (defect1 p e a b y).val) := by
        rw [hvcapg, hαdef]
        exact dvd_natCast_val_iff (p := p) (K := e - m) (g := m + vcap p (e - 2 * m) δ)
          (d := (defect1 p e a b y).val) hgle
      have hC : ‖χ (∏ l : Fin 3, (((y : ℕ) : ZMod (p ^ e)) + (a l : ZMod (p ^ e))))
            * (starRingEnd ℂ) (χ (∏ l : Fin 3, (((y : ℕ) : ZMod (p ^ e)) + (b l : ZMod (p ^ e)))))‖
          ≤ 1 := by
        rw [norm_mul, Complex.norm_conj]
        exact mul_le_one₀ (DirichletCharacter.norm_le_one χ _) (norm_nonneg _)
          (DirichletCharacter.norm_le_one χ _)
      have hbndy : bnd y = (if (p ^ (m + vcap p (e - 2 * m) δ) ∣ (defect1 p e a b y).val)
          then (p : ℝ) ^ (((vcap p (e - 2 * m) δ : ℕ) : ℝ) / 2) else 0) := by
        rw [hbnddef, hδdef]
        simp only [hunit, true_and]
      have hexp : (((e - m : ℕ) : ℝ) + ((m + vcap p (e - 2 * m) δ : ℕ) : ℝ)) / 2
          = (e : ℝ) / 2 + ((vcap p (e - 2 * m) δ : ℕ) : ℝ) / 2 := by
        have h1 : (e - m) + (m + vcap p (e - 2 * m) δ) = e + vcap p (e - 2 * m) δ := by omega
        have h2 : ((e - m : ℕ) : ℝ) + ((m + vcap p (e - 2 * m) δ : ℕ) : ℝ)
            = ((e : ℕ) : ℝ) + ((vcap p (e - 2 * m) δ : ℕ) : ℝ) := by
          rw [← Nat.cast_add, ← Nat.cast_add, h1]
        rw [h2]; ring
      have hstep : (if (p ^ vcap p (e - m) (2 * γ).val ∣ α.val)
              then (p : ℝ) ^ ((((e - m : ℕ) : ℝ) + ((vcap p (e - m) (2 * γ).val : ℕ) : ℝ)) / 2)
              else 0)
          ≤ (p : ℝ) ^ ((e : ℝ) / 2) * bnd y := by
        by_cases hc : (p ^ vcap p (e - m) (2 * γ).val) ∣ α.val
        · rw [if_pos hc]
          have hc2 : (p ^ (m + vcap p (e - 2 * m) δ)) ∣ (defect1 p e a b y).val := hcond.mp hc
          have hb2 : bnd y = (p : ℝ) ^ (((vcap p (e - 2 * m) δ : ℕ) : ℝ) / 2) := by
            rw [hbndy]; simp only [hunit, true_and, if_pos hc2]
          rw [hb2]
          calc (p : ℝ) ^ ((((e - m : ℕ) : ℝ) + ((vcap p (e - m) (2 * γ).val : ℕ) : ℝ)) / 2)
              = (p : ℝ) ^ ((e : ℝ) / 2 + ((vcap p (e - 2 * m) δ : ℕ) : ℝ) / 2) := by
                rw [hvcapg, hexp]
            _ = (p : ℝ) ^ ((e : ℝ) / 2) * (p : ℝ) ^ (((vcap p (e - 2 * m) δ : ℕ) : ℝ) / 2) :=
                Real.rpow_add hpR _ _
          exact le_refl _
        · rw [if_neg hc]
          have hc2 : ¬ ((p ^ (m + vcap p (e - 2 * m) δ)) ∣ (defect1 p e a b y).val) :=
            fun h => hc (hcond.mpr h)
          have hb2 : bnd y = 0 := by rw [hbndy]; simp only [hunit, true_and, if_neg hc2]
          rw [hb2, mul_zero]
      rw [hconv.symm, Finset.sum_congr rfl (fun w _ => hsummand w)]
      rw [hpeel, norm_mul]
      calc ‖χ (∏ l : Fin 3, (((y : ℕ) : ZMod (p ^ e)) + (a l : ZMod (p ^ e))))
              * (starRingEnd ℂ) (χ (∏ l : Fin 3, (((y : ℕ) : ZMod (p ^ e)) + (b l : ZMod (p ^ e)))))‖
            * ‖gaussQuad p (e - m) (psiFun p e m χ 1) α γ‖
          ≤ 1 * ‖gaussQuad p (e - m) (psiFun p e m χ 1) α γ‖ :=
            mul_le_mul_of_nonneg_right hC (norm_nonneg _)
        _ = ‖gaussQuad p (e - m) (psiFun p e m χ 1) α γ‖ := one_mul _
        _ ≤ (p : ℝ) ^ ((e : ℝ) / 2) * bnd y := hgq.trans hstep
    · -- non-unit case: the summand vanishes
      have h0 : ∀ w ∈ Finset.range (p ^ (e - m)),
          corrG p e χ a b (((y + p ^ m * w : ℕ) : ZMod (p ^ e))) = 0 := by
        intro w _
        simp only [corrG]
        exact vanish_nonunit hm h2 χ a b y hunit w
      have hsum0 : (∑ w ∈ Finset.range (p ^ (e - m)),
          corrG p e χ a b (((y + p ^ m * w : ℕ) : ZMod (p ^ e)))) = 0 := by
        rw [Finset.sum_congr rfl h0, Finset.sum_const_zero]
      rw [hsum0, norm_zero, hbnddef]
      simp only [hunit, false_and, if_false, mul_zero]
      exact le_refl 0
  -- Step 4: sum up
  have hfin : ‖∑ y ∈ Finset.range (p ^ m), ∑ w ∈ Finset.range (p ^ (e - m)),
        corrG p e χ a b (((y + p ^ m * w : ℕ) : ZMod (p ^ e)))‖
      ≤ (p : ℝ) ^ ((e : ℝ) / 2) * gaussTwoRHS p e m a b := by
    calc ‖∑ y ∈ Finset.range (p ^ m), ∑ w ∈ Finset.range (p ^ (e - m)),
            corrG p e χ a b (((y + p ^ m * w : ℕ) : ZMod (p ^ e)))‖
        ≤ ∑ y ∈ Finset.range (p ^ m), ‖∑ w ∈ Finset.range (p ^ (e - m)),
            corrG p e χ a b (((y + p ^ m * w : ℕ) : ZMod (p ^ e)))‖ := norm_sum_le _ _
      _ ≤ ∑ y ∈ Finset.range (p ^ m), (p : ℝ) ^ ((e : ℝ) / 2) * bnd y :=
          Finset.sum_le_sum hbnd
      _ = (p : ℝ) ^ ((e : ℝ) / 2) * ∑ y ∈ Finset.range (p ^ m), bnd y := by
          rw [Finset.mul_sum]
      _ = (p : ℝ) ^ ((e : ℝ) / 2) * gaussTwoRHS p e m a b := by
          rw [show gaussTwoRHS p e m a b = ∑ y ∈ Finset.range (p ^ m), bnd y from by
            rw [gaussTwoRHS, hbnddef]]
  have hfold : (∑ x : ZMod (p ^ e), χ (∏ l : Fin 3, (x + (a l : ZMod (p ^ e))))
        * (starRingEnd ℂ) (χ (∏ l : Fin 3, (x + (b l : ZMod (p ^ e))))))
      = ∑ x : ZMod (p ^ e), corrG p e χ a b x := rfl
  rw [hfold, hrange, hbij]
  exact hfin


end Work.LinnikBurgess
