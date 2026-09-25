import Mathlib
import Submission.Work.BourgainPlan.Maximal.poly_dilation_lp
import Submission.Work.BourgainPlan.Maximal.poly_dilation_lp_shift_const
import Submission.Work.BourgainPlan.Maximal.ell2HLMaxLp
import Submission.Work.BourgainPlan.Maximal.ell2Maximal
import Submission.Work.BourgainPlan.Maximal.piece_le_hlMax_of_deriv_pos
import Submission.Work.BourgainPlan.Maximal.flat_piece_le_hlMax
import Submission.Work.BourgainPlan.Maximal.tail_le_hlMax
import Submission.Work.BourgainPlan.Maximal.poly_sup_le_finset_hlMax

/-!
# The `ℓ²`-valued polynomial-dilation maximal inequality on `L^p`

Bourgain, *Pointwise ergodic theorems for arithmetic sets*, IHÉS 69 (1989), §7.1: for a polynomial
`P ∈ ℤ[X]` that is nonnegative on `[0,∞)` and every `1 < p < ∞`, the maximal operator

`f ↦ sup_N ∫_{(0,1]} |f (· − P (N s))| ds`

satisfies the vector-valued (`ℓ²`) maximal inequality

`‖ (Σ_t (sup_N ∫ |f_t (· − P(N s))| ds)²)^{1/2} ‖_{L^p} ≤ C ‖ (Σ_t f_t²)^{1/2} ‖_{L^p}`,

with `C` independent of the number of components.

The proof has three parts.

* `poly_sup_le_finset_hlMax` (in the imported module) is the pointwise domination of the sup over `N`
  by a constant times a *finite sum of translates* of the Hardy--Littlewood maximal function, plus a
  finite sum of translates of the test function itself:
  `sup_N ∫_{(0,1]} ψ (x − P (Ns)) ≤ ofReal K * Σ_{c∈T} hlMax ψ (x−c) + Σ_{c∈D} ψ (x−c)`.
* `ell2_shift_hlMax_bound` handles the Hardy--Littlewood pieces: Cauchy--Schwarz over the finite set
  of translates turns the `ℓ²`-norm of a sum of translates of `hlMax` into the vector-valued
  maximal function of the *family indexed by `Fin n × {c // c ∈ T}`*, to which the vector-valued
  Hardy--Littlewood theorem (`ell2HLMaxLp`, via the uniform-in-the-index-type form
  `ell2HLMaxLp_uniform`) applies; the resulting shifts of the test function are then absorbed by the
  translation invariance of Lebesgue measure (`lintegral_rpow_finset_sum_comp_sub_le`).
* `ell2_shift_raw_bound` handles the finitely many translates of the test function, again by
  translation invariance.
-/

open MeasureTheory Set
open scoped ENNReal BigOperators

set_option maxHeartbeats 2000000

namespace Work.BourgainPlan.Maximal




private lemma rpow_sum_le_sum_rpow_of_le_one {ι : Type*} (s : Finset ι) (a : ι → ENNReal)
    {q : ℝ} (hq0 : 0 < q) (hq1 : q ≤ 1) :
    (∑ i ∈ s, a i) ^ q ≤ ∑ i ∈ s, (a i) ^ q := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [ENNReal.zero_rpow_of_pos hq0]
  | insert i s hi ih =>
      rw [Finset.sum_insert hi, Finset.sum_insert hi]
      calc (a i + ∑ j ∈ s, a j) ^ q ≤ (a i) ^ q + (∑ j ∈ s, a j) ^ q :=
            ENNReal.rpow_add_le_add_rpow (a i) _ hq0.le hq1
        _ ≤ (a i) ^ q + ∑ j ∈ s, (a j) ^ q := add_le_add le_rfl ih

private lemma rpow_sum_le_card_rpow_mul_sum_rpow {ι : Type*} (s : Finset ι) (a : ι → ENNReal)
    {q : ℝ} (hq : 0 < q) :
    (∑ i ∈ s, a i) ^ q ≤ (s.card : ENNReal) ^ q * ∑ i ∈ s, (a i) ^ q := by
  rcases Finset.eq_empty_or_nonempty s with rfl | hne
  · simp [ENNReal.zero_rpow_of_pos hq]
  · have hcard1 : (1 : ENNReal) ≤ (s.card : ENNReal) := by
      rw [← Nat.cast_one, Nat.cast_le]; exact Finset.card_pos.mpr hne
    rcases lt_or_ge (1:ℝ) q with hq1 | hq1
    · refine (ENNReal.rpow_sum_le_const_mul_sum_rpow s a hq1.le).trans ?_
      exact mul_le_mul_of_nonneg_right
        (ENNReal.rpow_le_rpow_of_exponent_le hcard1 (by linarith)) zero_le
    · refine (rpow_sum_le_sum_rpow_of_le_one s a hq hq1).trans ?_
      exact le_mul_of_one_le_left zero_le (ENNReal.one_le_rpow hcard1 hq)

private lemma rpow_add_le_two_rpow_mul {q : ℝ} (hq : 0 < q) (a b : ENNReal) :
    (a + b) ^ q ≤ (2 : ENNReal) ^ q * (a ^ q + b ^ q) := by
  have h1 : a + b ≤ 2 * max a b := by
    rw [two_mul]
    exact add_le_add (le_max_left _ _) (le_max_right _ _)
  refine (ENNReal.rpow_le_rpow h1 hq.le).trans ?_
  rw [ENNReal.mul_rpow_of_nonneg _ _ hq.le]
  exact mul_le_mul_of_nonneg_left (by
    rcases le_total a b with h | h
    · rw [max_eq_right h]; exact le_add_self
    · rw [max_eq_left h]; exact le_self_add) zero_le

private lemma lintegral_Icc_comp_sub (ψ : ℝ → ENNReal) (a b c : ℝ) :
    ∫⁻ y in Set.Icc a b, ψ (y - c) = ∫⁻ u in Set.Icc (a - c) (b - c), ψ u := by
  have hderiv : ∀ x ∈ Set.Icc a b,
      HasDerivWithinAt (fun u : ℝ => u - c) 1 (Set.Icc a b) x :=
    fun x _ => by simpa using ((hasDerivAt_id x).sub_const c).hasDerivWithinAt
  have hinj : Set.InjOn (fun u : ℝ => u - c) (Set.Icc a b) := by
    intro x _ y _ hxy; simp only at hxy; linarith
  have h := lintegral_image_eq_lintegral_abs_deriv_mul measurableSet_Icc hderiv hinj ψ
  have himg : (fun u : ℝ => u - c) '' Set.Icc a b = Set.Icc (a - c) (b - c) := by
    ext w; constructor
    · rintro ⟨u, hu, rfl⟩; rw [Set.mem_Icc] at hu ⊢; constructor <;> linarith [hu.1, hu.2]
    · intro hw; rw [Set.mem_Icc] at hw
      exact ⟨w + c, by rw [Set.mem_Icc]; constructor <;> linarith [hw.1, hw.2], by ring⟩
  rw [himg] at h
  simpa only [abs_one, ENNReal.ofReal_one, one_mul] using h.symm

private lemma hlMax_comp_sub (ψ : ℝ → ENNReal) (c x : ℝ) :
    Commons.Analysis.Maximal.hlMax (fun y => ψ (y - c)) x
      = Commons.Analysis.Maximal.hlMax ψ (x - c) := by
  rw [Commons.Analysis.Maximal.hlMax, Commons.Analysis.Maximal.hlMax]
  refine le_antisymm ?_ ?_
  · refine iSup_le fun a => iSup_le fun b => iSup_le fun hab => ?_
    rw [lintegral_Icc_comp_sub ψ a b c]
    rw [show b - a = (b - c) - (a - c) by ring]
    exact Commons.Analysis.Maximal.hlMax_le_of_mem ψ (by linarith [hab.1]) (by linarith [hab.2])
  · refine iSup_le fun a => iSup_le fun b => iSup_le fun hab => ?_
    have h1 : ∫⁻ u in Set.Icc a b, ψ u = ∫⁻ y in Set.Icc (a + c) (b + c), ψ (y - c) := by
      rw [lintegral_Icc_comp_sub ψ (a + c) (b + c) c]
      simp only [add_sub_cancel_right]
    rw [h1, show b - a = (b + c) - (a + c) by ring]
    exact le_iSup_of_le (a + c) (le_iSup_of_le (b + c) (le_iSup_of_le
      ⟨by linarith [hab.1], by linarith [hab.2]⟩ le_rfl))

private lemma sum_subtype_eq_sum {M : Type*} [AddCommMonoid M] (T : Finset ℝ) (F : ℝ → M) :
    (∑ c : {c : ℝ // c ∈ T}, F c.1) = ∑ c ∈ T, F c := by
  rw [Finset.univ_eq_attach T, Finset.sum_attach]

private lemma lintegral_shift (F : ℝ → ENNReal) (c : ℝ) :
    ∫⁻ x, F (x - c) = ∫⁻ x, F x := by
  have h := lintegral_add_right_eq_self (μ := volume) F (-c)
  simpa [sub_eq_add_neg] using h

private lemma lintegral_rpow_finset_sum_comp_sub_le (s : Finset ℝ) (g : ℝ → ENNReal)
    (hg : Measurable g) {q : ℝ} (hq : 0 < q) :
    ∫⁻ x, (∑ c ∈ s, g (x - c)) ^ q
      ≤ (s.card : ENNReal) ^ q * (s.card : ENNReal) * ∫⁻ x, g x ^ q := by
  have hmeas : ∀ c ∈ s, Measurable (fun x : ℝ => g (x - c) ^ q) := fun c _ =>
    (ENNReal.continuous_rpow_const (y := q)).measurable.comp
      (hg.comp (measurable_id.sub measurable_const))
  have hsummeas : Measurable (fun x : ℝ => ∑ c ∈ s, g (x - c) ^ q) :=
    Finset.measurable_sum _ hmeas
  calc ∫⁻ x, (∑ c ∈ s, g (x - c)) ^ q
      ≤ ∫⁻ x, (s.card : ENNReal) ^ q * ∑ c ∈ s, g (x - c) ^ q :=
        lintegral_mono fun x => rpow_sum_le_card_rpow_mul_sum_rpow s (fun c => g (x - c)) hq
    _ = (s.card : ENNReal) ^ q * ∫⁻ x, ∑ c ∈ s, g (x - c) ^ q :=
        lintegral_const_mul _ hsummeas
    _ = (s.card : ENNReal) ^ q * ∑ c ∈ s, ∫⁻ x, g (x - c) ^ q := by
        rw [lintegral_finsetSum s hmeas]
    _ = (s.card : ENNReal) ^ q * ∑ c ∈ s, ∫⁻ x, g x ^ q := by
        congr 1
        exact Finset.sum_congr rfl fun c _ => lintegral_shift (fun y => g y ^ q) c
    _ = (s.card : ENNReal) ^ q * ((s.card : ENNReal) * ∫⁻ x, g x ^ q) := by
        rw [Finset.sum_const, nsmul_eq_mul]
    _ = (s.card : ENNReal) ^ q * (s.card : ENNReal) * ∫⁻ x, g x ^ q := by ring


private lemma sum_fin_subtype_comm {n : ℕ} (T : Finset ℝ) (F : ℝ → Fin n → ENNReal) :
    (∑ t : Fin n, ∑ c : {c : ℝ // c ∈ T}, F c.1 t) = ∑ c ∈ T, ∑ t : Fin n, F c t := by
  rw [Finset.sum_comm]
  exact sum_subtype_eq_sum T (fun c => ∑ t : Fin n, F c t)

private lemma ofReal_mul_ofReal' {a b : ℝ} (ha : 0 ≤ a) :
    ENNReal.ofReal a * ENNReal.ofReal b = ENNReal.ofReal (a * b) :=
  (ENNReal.ofReal_mul ha).symm

private lemma natCast_rpow' (m : ℕ) {c : ℝ} (hc : 0 ≤ c) :
    (m : ENNReal) ^ c = ENNReal.ofReal ((m : ℝ) ^ c) := by
  rw [← ENNReal.ofReal_natCast m]
  exact ENNReal.ofReal_rpow_of_nonneg (Nat.cast_nonneg m) hc


private lemma ell2HLMaxLp_uniform {p : ℝ} (hp : 1 < p) :
    ∃ C : ℝ, 0 < C ∧ ∀ {ι : Type} [Fintype ι] (f : ι → ℝ → ℝ), (∀ t, Measurable (f t)) →
      ∫⁻ x, (∑ t, (Commons.Analysis.Maximal.hlMax (fun y => ‖f t y‖ₑ) x) ^ (2 : ℝ)) ^ (p / 2)
        ≤ ENNReal.ofReal (C ^ p) * ∫⁻ x, (∑ t, ‖f t x‖ₑ ^ (2 : ℝ)) ^ (p / 2) := by
  obtain ⟨C, hC, hb⟩ := ell2HLMaxLp (p := p) hp
  refine ⟨C, hC, ?_⟩
  intro ι _ f hf
  classical
  let n := Fintype.card ι
  let e : ι ≃ Fin n := Fintype.equivFin ι
  let g : Fin n → ℝ → ℝ := fun i => f (e.symm i)
  have hg : ∀ i, Measurable (g i) := fun i => hf _
  have hmain := hb n g hg
  have hL : (∫⁻ x, (∑ t : ι,
        (Commons.Analysis.Maximal.hlMax (fun y => ‖f t y‖ₑ) x) ^ (2 : ℝ)) ^ (p / 2))
      = ∫⁻ x, (∑ i : Fin n,
        (Commons.Analysis.Maximal.hlMax (fun y => ‖g i y‖ₑ) x) ^ (2 : ℝ)) ^ (p / 2) := by
    refine lintegral_congr fun x => ?_
    congr 1
    exact Fintype.sum_equiv e
      (fun t : ι => (Commons.Analysis.Maximal.hlMax (fun y => ‖f t y‖ₑ) x) ^ (2 : ℝ))
      (fun i : Fin n => (Commons.Analysis.Maximal.hlMax (fun y => ‖g i y‖ₑ) x) ^ (2 : ℝ))
      (fun t => by simp [g])
  have hR : (∫⁻ x, (∑ i : Fin n, ‖g i x‖ₑ ^ (2 : ℝ)) ^ (p / 2))
      = ∫⁻ x, (∑ t : ι, ‖f t x‖ₑ ^ (2 : ℝ)) ^ (p / 2) := by
    refine lintegral_congr fun x => ?_
    congr 1
    exact (Fintype.sum_equiv e (fun t : ι => ‖f t x‖ₑ ^ (2 : ℝ))
      (fun i : Fin n => ‖g i x‖ₑ ^ (2 : ℝ)) (fun t => by simp [g])).symm
  rw [hL, ← hR]
  exact hmain

private noncomputable def ell2HLc (p : ℝ) : ℝ :=
  if h : 1 < p then Classical.choose (ell2HLMaxLp_uniform (p := p) h) else 1

private lemma ell2HLc_pos {p : ℝ} (hp : 1 < p) : 0 < ell2HLc p := by
  rw [ell2HLc, dif_pos hp]
  exact (Classical.choose_spec (ell2HLMaxLp_uniform (p := p) hp)).1

private lemma ell2HLc_bound {p : ℝ} (hp : 1 < p) {ι : Type} [Fintype ι] (f : ι → ℝ → ℝ)
    (hf : ∀ t, Measurable (f t)) :
    ∫⁻ x, (∑ t, (Commons.Analysis.Maximal.hlMax (fun y => ‖f t y‖ₑ) x) ^ (2 : ℝ)) ^ (p / 2)
      ≤ ENNReal.ofReal ((ell2HLc p) ^ p) * ∫⁻ x, (∑ t, ‖f t x‖ₑ ^ (2 : ℝ)) ^ (p / 2) := by
  rw [ell2HLc, dif_pos hp]
  exact (Classical.choose_spec (ell2HLMaxLp_uniform (p := p) hp)).2 f hf


private lemma ofReal_mul_four {a b c d : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c) (_hd : 0 ≤ d) :
    ENNReal.ofReal (a * b * c * d)
      = ENNReal.ofReal a * ENNReal.ofReal b * (ENNReal.ofReal c * ENNReal.ofReal d) := by
  rw [ofReal_mul_ofReal' ha, ofReal_mul_ofReal' hc, ofReal_mul_ofReal' (mul_nonneg ha hb)]
  congr 1
  ring

private lemma const_combine (C2 p : ℝ) (m : ℕ) (Z : ENNReal) (hp0 : 0 ≤ p) (hC2 : 0 ≤ C2) :
    (m : ENNReal) ^ p * ENNReal.ofReal (C2 ^ p) * ((m : ENNReal) ^ (p/2) * (m : ENNReal) * Z)
      = ENNReal.ofReal (C2 ^ p * (m:ℝ) ^ p * (m:ℝ) ^ (p/2) * (m:ℝ)) * Z := by
  have hq0 : (0:ℝ) ≤ p/2 := by linarith
  have hm : (0:ℝ) ≤ (m:ℝ) := Nat.cast_nonneg m
  rw [natCast_rpow' m hp0, natCast_rpow' m hq0, ← ENNReal.ofReal_natCast m,
    mul_comm (ENNReal.ofReal ((m:ℝ) ^ p)) (ENNReal.ofReal (C2 ^ p))]
  calc ENNReal.ofReal (C2 ^ p) * ENNReal.ofReal ((m:ℝ) ^ p) *
        (ENNReal.ofReal ((m:ℝ) ^ (p/2)) * ENNReal.ofReal ((m:ℝ)) * Z)
      = (ENNReal.ofReal (C2 ^ p) * ENNReal.ofReal ((m:ℝ) ^ p) *
          (ENNReal.ofReal ((m:ℝ) ^ (p/2)) * ENNReal.ofReal ((m:ℝ)))) * Z := by ring
    _ = ENNReal.ofReal (C2 ^ p * (m:ℝ) ^ p * (m:ℝ) ^ (p/2) * (m:ℝ)) * Z := by
        rw [← ofReal_mul_four (Real.rpow_nonneg hC2 p) (Real.rpow_nonneg hm p)
          (Real.rpow_nonneg hm (p/2)) hm]

private lemma const_le_rpow (base p : ℝ) (hp : 1 < p) (hb : 0 ≤ base) :
    base ≤ (base ^ (1/p) + 1) ^ p := by
  have hp0 : (0:ℝ) ≤ p := le_of_lt (lt_trans zero_lt_one hp)
  have hp1 : (0:ℝ) < p := lt_trans zero_lt_one hp
  have h1 : base ^ (1/p) ≤ base ^ (1/p) + 1 := le_add_of_nonneg_right (by norm_num : (0:ℝ) ≤ 1)
  refine le_trans (le_of_eq ?_) (Real.rpow_le_rpow (Real.rpow_nonneg hb _) h1 hp0)
  rw [← Real.rpow_mul hb, one_div, inv_mul_cancel₀ (ne_of_gt hp1), Real.rpow_one]

private lemma ell2_shift_hlMax_bound {p : ℝ} (hp : 1 < p) {n : ℕ} (T : Finset ℝ)
    (f : Fin n → ℝ → ℝ) (hf : ∀ t, Measurable (f t)) :
    ∫⁻ x, (∑ t, (∑ c ∈ T, Commons.Analysis.Maximal.hlMax (fun y => ‖f t y‖ₑ) (x - c)) ^ (2:ℝ)) ^ (p/2)
      ≤ ENNReal.ofReal ((((ell2HLc p) ^ p * (T.card : ℝ) ^ p * (T.card : ℝ) ^ (p/2)
            * (T.card : ℝ)) ^ (1/p) + 1) ^ p)
        * ∫⁻ x, (∑ t, ‖f t x‖ₑ ^ (2:ℝ)) ^ (p/2) := by
  classical
  have hp0 : (0:ℝ) ≤ p := le_of_lt (lt_trans zero_lt_one hp)
  have hq : (0:ℝ) < p/2 := by linarith
  have hcard0 : (0:ℝ) ≤ (T.card : ℝ) := Nat.cast_nonneg _
  have hHLapp := ell2HLc_bound (p := p) hp
    (ι := Fin n × {c : ℝ // c ∈ T}) (fun i => fun y => f i.1 (y - i.2.1))
    (fun i => (hf i.1).comp (measurable_id.sub_const i.2.1))
  have hId1 : ∀ x : ℝ, (∑ i : Fin n × {c : ℝ // c ∈ T},
        (Commons.Analysis.Maximal.hlMax (fun y => ‖f i.1 (y - i.2.1)‖ₑ) x) ^ (2:ℝ))
      = ∑ t : Fin n, ∑ c ∈ T,
          (Commons.Analysis.Maximal.hlMax (fun y => ‖f t (y - c)‖ₑ) x) ^ (2:ℝ) := by
    intro x
    rw [Fintype.sum_prod_type]
    exact Finset.sum_congr rfl fun t _ =>
      (sum_subtype_eq_sum T (fun c => (Commons.Analysis.Maximal.hlMax (fun y => ‖f t (y - c)‖ₑ) x) ^ (2:ℝ)))
  have hId2 : ∀ x : ℝ, (∑ i : Fin n × {c : ℝ // c ∈ T}, ‖f i.1 (x - i.2.1)‖ₑ ^ (2:ℝ))
      = ∑ c ∈ T, ∑ t : Fin n, ‖f t (x - c)‖ₑ ^ (2:ℝ) := by
    intro x
    rw [Fintype.sum_prod_type]
    exact sum_fin_subtype_comm T (fun c t => ‖f t (x - c)‖ₑ ^ (2:ℝ))
  have hstep0 : ∀ x : ℝ, (∑ t : Fin n, (∑ c ∈ T,
        Commons.Analysis.Maximal.hlMax (fun y => ‖f t y‖ₑ) (x - c)) ^ (2:ℝ))
      = ∑ t : Fin n, (∑ c ∈ T,
        Commons.Analysis.Maximal.hlMax (fun y => ‖f t (y - c)‖ₑ) x) ^ (2:ℝ) := by
    intro x
    refine Finset.sum_congr rfl fun t _ => ?_
    congr 1
    exact Finset.sum_congr rfl fun c _ => (hlMax_comp_sub (fun y => ‖f t y‖ₑ) c x).symm
  have hstep1 : ∀ x : ℝ, (∑ t : Fin n, (∑ c ∈ T,
        Commons.Analysis.Maximal.hlMax (fun y => ‖f t (y - c)‖ₑ) x) ^ (2:ℝ))
      ≤ (T.card : ENNReal) ^ (2:ℝ) * (∑ i : Fin n × {c : ℝ // c ∈ T},
        (Commons.Analysis.Maximal.hlMax (fun y => ‖f i.1 (y - i.2.1)‖ₑ) x) ^ (2:ℝ)) := by
    intro x
    calc ∑ t : Fin n, (∑ c ∈ T, Commons.Analysis.Maximal.hlMax (fun y => ‖f t (y - c)‖ₑ) x) ^ (2:ℝ)
        ≤ ∑ t : Fin n, ((T.card : ENNReal) ^ (2:ℝ) *
            ∑ c ∈ T, (Commons.Analysis.Maximal.hlMax (fun y => ‖f t (y - c)‖ₑ) x) ^ (2:ℝ)) :=
          Finset.sum_le_sum fun t _ =>
            rpow_sum_le_card_rpow_mul_sum_rpow T _ (by norm_num : (0:ℝ) < 2)
      _ = (T.card : ENNReal) ^ (2:ℝ) * (∑ i : Fin n × {c : ℝ // c ∈ T},
            (Commons.Analysis.Maximal.hlMax (fun y => ‖f i.1 (y - i.2.1)‖ₑ) x) ^ (2:ℝ)) := by
          rw [← Finset.mul_sum, ← hId1 x]
  have hPsum_meas : Measurable (fun x : ℝ => (∑ i : Fin n × {c : ℝ // c ∈ T},
        (Commons.Analysis.Maximal.hlMax (fun y => ‖f i.1 (y - i.2.1)‖ₑ) x) ^ (2:ℝ)) ^ (p/2)) :=
    (ENNReal.continuous_rpow_const (y := p/2)).measurable.comp
      (Finset.measurable_sum _ fun i _ =>
        (ENNReal.continuous_rpow_const (y := (2:ℝ))).measurable.comp
          (Commons.Analysis.Maximal.measurable_hlMax (fun y => ‖f i.1 (y - i.2.1)‖ₑ)))
  have hstep2 : ∀ x : ℝ, (∑ t : Fin n, (∑ c ∈ T,
        Commons.Analysis.Maximal.hlMax (fun y => ‖f t y‖ₑ) (x - c)) ^ (2:ℝ)) ^ (p/2)
      ≤ (T.card : ENNReal) ^ p * (∑ i : Fin n × {c : ℝ // c ∈ T},
        (Commons.Analysis.Maximal.hlMax (fun y => ‖f i.1 (y - i.2.1)‖ₑ) x) ^ (2:ℝ)) ^ (p/2) := by
    intro x
    rw [hstep0 x]
    refine (ENNReal.rpow_le_rpow (hstep1 x) hq.le).trans ?_
    rw [ENNReal.mul_rpow_of_nonneg _ _ hq.le, ← ENNReal.rpow_mul, show (2:ℝ) * (p/2) = p by ring]
  have hgmeas : Measurable (fun x : ℝ => ∑ t : Fin n, ‖f t x‖ₑ ^ (2:ℝ)) :=
    Finset.measurable_sum _ fun t _ =>
      (ENNReal.continuous_rpow_const (y := (2:ℝ))).measurable.comp (hf t).enorm
  have hmain : ∫⁻ x, (∑ t, (∑ c ∈ T, Commons.Analysis.Maximal.hlMax (fun y => ‖f t y‖ₑ) (x - c)) ^ (2:ℝ)) ^ (p/2)
      ≤ ENNReal.ofReal ((ell2HLc p) ^ p * (T.card : ℝ) ^ p * (T.card : ℝ) ^ (p/2) * (T.card : ℝ))
        * ∫⁻ x, (∑ t, ‖f t x‖ₑ ^ (2:ℝ)) ^ (p/2) := by
    calc ∫⁻ x, (∑ t, (∑ c ∈ T, Commons.Analysis.Maximal.hlMax (fun y => ‖f t y‖ₑ) (x - c)) ^ (2:ℝ)) ^ (p/2)
        ≤ ∫⁻ x, (T.card : ENNReal) ^ p * (∑ i : Fin n × {c : ℝ // c ∈ T},
            (Commons.Analysis.Maximal.hlMax (fun y => ‖f i.1 (y - i.2.1)‖ₑ) x) ^ (2:ℝ)) ^ (p/2) :=
          lintegral_mono hstep2
      _ = (T.card : ENNReal) ^ p * ∫⁻ x, (∑ i : Fin n × {c : ℝ // c ∈ T},
            (Commons.Analysis.Maximal.hlMax (fun y => ‖f i.1 (y - i.2.1)‖ₑ) x) ^ (2:ℝ)) ^ (p/2) :=
          lintegral_const_mul _ hPsum_meas
      _ ≤ (T.card : ENNReal) ^ p * (ENNReal.ofReal ((ell2HLc p) ^ p) *
            ∫⁻ x, (∑ i : Fin n × {c : ℝ // c ∈ T}, ‖f i.1 (x - i.2.1)‖ₑ ^ (2:ℝ)) ^ (p/2)) :=
          mul_le_mul_of_nonneg_left hHLapp zero_le
      _ = (T.card : ENNReal) ^ p * ENNReal.ofReal ((ell2HLc p) ^ p) *
            ∫⁻ x, (∑ c ∈ T, ∑ t : Fin n, ‖f t (x - c)‖ₑ ^ (2:ℝ)) ^ (p/2) := by
          have hid : (∫⁻ x, (∑ i : Fin n × {c : ℝ // c ∈ T},
                ‖f i.1 (x - i.2.1)‖ₑ ^ (2:ℝ)) ^ (p/2))
              = ∫⁻ x, (∑ c ∈ T, ∑ t : Fin n, ‖f t (x - c)‖ₑ ^ (2:ℝ)) ^ (p/2) :=
            lintegral_congr fun x => by rw [hId2 x]
          rw [hid]
          ring
      _ ≤ (T.card : ENNReal) ^ p * ENNReal.ofReal ((ell2HLc p) ^ p) *
            ((T.card : ENNReal) ^ (p/2) * (T.card : ENNReal) *
              ∫⁻ x, (∑ t : Fin n, ‖f t x‖ₑ ^ (2:ℝ)) ^ (p/2)) := by
          refine mul_le_mul_of_nonneg_left ?_ zero_le
          exact lintegral_rpow_finset_sum_comp_sub_le T
            (fun y : ℝ => ∑ t : Fin n, ‖f t y‖ₑ ^ (2:ℝ)) hgmeas hq
      _ = ENNReal.ofReal ((ell2HLc p) ^ p * (T.card : ℝ) ^ p * (T.card : ℝ) ^ (p/2) * (T.card : ℝ)) *
            ∫⁻ x, (∑ t : Fin n, ‖f t x‖ₑ ^ (2:ℝ)) ^ (p/2) :=
          const_combine (ell2HLc p) p T.card _ hp0 (ell2HLc_pos hp).le
  refine hmain.trans (mul_le_mul_of_nonneg_right (ENNReal.ofReal_le_ofReal ?_) zero_le)
  have hcpos := ell2HLc_pos (p := p) hp
  have hb : (0:ℝ) ≤ (ell2HLc p) ^ p * (T.card : ℝ) ^ p * (T.card : ℝ) ^ (p/2) * (T.card : ℝ) := by
    positivity
  exact const_le_rpow _ p hp hb

private lemma ell2_shift_raw_bound {p : ℝ} (hp : 1 < p) {n : ℕ} (D : Finset ℝ)
    (f : Fin n → ℝ → ℝ) (hf : ∀ t, Measurable (f t)) :
    ∫⁻ x, (∑ t, (∑ c ∈ D, ‖f t (x - c)‖ₑ) ^ (2:ℝ)) ^ (p/2)
      ≤ ENNReal.ofReal ((((D.card : ℝ) ^ p * (D.card : ℝ) ^ (p/2)
            * (D.card : ℝ)) ^ (1/p) + 1) ^ p)
        * ∫⁻ x, (∑ t, ‖f t x‖ₑ ^ (2:ℝ)) ^ (p/2) := by
  classical
  have hp0 : (0:ℝ) ≤ p := le_of_lt (lt_trans zero_lt_one hp)
  have hq : (0:ℝ) < p/2 := by linarith
  let g : ℝ → ENNReal := fun x => ∑ t : Fin n, ‖f t x‖ₑ ^ (2:ℝ)
  have hgmeas : Measurable g := Finset.measurable_sum _ fun t _ =>
      (ENNReal.continuous_rpow_const (y := (2:ℝ))).measurable.comp (hf t).enorm
  have hpt : ∀ x : ℝ, (∑ t : Fin n, (∑ c ∈ D, ‖f t (x - c)‖ₑ) ^ (2:ℝ))
      ≤ (D.card : ENNReal) ^ (2:ℝ) * (∑ c ∈ D, g (x - c)) := by
    intro x
    calc ∑ t : Fin n, (∑ c ∈ D, ‖f t (x - c)‖ₑ) ^ (2:ℝ)
        ≤ ∑ t : Fin n, ((D.card : ENNReal) ^ (2:ℝ) * ∑ c ∈ D, (‖f t (x - c)‖ₑ) ^ (2:ℝ)) :=
          Finset.sum_le_sum fun t _ =>
            rpow_sum_le_card_rpow_mul_sum_rpow D _ (by norm_num : (0:ℝ) < 2)
      _ = (D.card : ENNReal) ^ (2:ℝ) * ∑ t : Fin n, ∑ c ∈ D, (‖f t (x - c)‖ₑ) ^ (2:ℝ) :=
          (Finset.mul_sum _ _ _).symm
      _ = (D.card : ENNReal) ^ (2:ℝ) * ∑ c ∈ D, ∑ t : Fin n, (‖f t (x - c)‖ₑ) ^ (2:ℝ) := by
          rw [Finset.sum_comm]
      _ = (D.card : ENNReal) ^ (2:ℝ) * (∑ c ∈ D, g (x - c)) := rfl
  have hXmeas : Measurable (fun x : ℝ => (∑ c ∈ D, g (x - c)) ^ (p/2)) :=
    (ENNReal.continuous_rpow_const (y := p/2)).measurable.comp
      (Finset.measurable_sum _ fun c _ =>
        hgmeas.comp (measurable_id.sub_const c))
  have hmain : ∫⁻ x, (∑ t, (∑ c ∈ D, ‖f t (x - c)‖ₑ) ^ (2:ℝ)) ^ (p/2)
      ≤ ENNReal.ofReal ((D.card : ℝ) ^ p * (D.card : ℝ) ^ (p/2) * (D.card : ℝ))
        * ∫⁻ x, (∑ t, ‖f t x‖ₑ ^ (2:ℝ)) ^ (p/2) := by
    calc ∫⁻ x, (∑ t, (∑ c ∈ D, ‖f t (x - c)‖ₑ) ^ (2:ℝ)) ^ (p/2)
        ≤ ∫⁻ x, ((D.card : ENNReal) ^ (2:ℝ) * (∑ c ∈ D, g (x - c))) ^ (p/2) :=
          lintegral_mono fun x => ENNReal.rpow_le_rpow (hpt x) hq.le
      _ = ∫⁻ x, (D.card : ENNReal) ^ p * (∑ c ∈ D, g (x - c)) ^ (p/2) := by
          refine lintegral_congr fun x => ?_
          rw [ENNReal.mul_rpow_of_nonneg _ _ hq.le, ← ENNReal.rpow_mul,
            show (2:ℝ) * (p/2) = p by ring]
      _ = (D.card : ENNReal) ^ p * ∫⁻ x, (∑ c ∈ D, g (x - c)) ^ (p/2) :=
          lintegral_const_mul _ hXmeas
      _ ≤ (D.card : ENNReal) ^ p * ((D.card : ENNReal) ^ (p/2) * (D.card : ENNReal) *
            ∫⁻ x, g x ^ (p/2)) :=
          mul_le_mul_of_nonneg_left
            (lintegral_rpow_finset_sum_comp_sub_le D g hgmeas hq) zero_le
      _ = ENNReal.ofReal ((D.card : ℝ) ^ p * (D.card : ℝ) ^ (p/2) * (D.card : ℝ)) *
            ∫⁻ x, (∑ t : Fin n, ‖f t x‖ₑ ^ (2:ℝ)) ^ (p/2) := by
          have hcc := const_combine 1 p D.card (∫⁻ x, g x ^ (p/2)) hp0
            (by norm_num : (0:ℝ) ≤ 1)
          simp only [Real.one_rpow, ENNReal.ofReal_one, one_mul, mul_one] at hcc
          exact hcc
  refine hmain.trans (mul_le_mul_of_nonneg_right (ENNReal.ofReal_le_ofReal ?_) zero_le)
  exact const_le_rpow _ p hp (by positivity)


private lemma two_add_rpow_two_le (a b : ENNReal) :
    (a + b) ^ (2:ℝ) ≤ 4 * (a ^ (2:ℝ) + b ^ (2:ℝ)) := by
  have h := rpow_add_le_two_rpow_mul (q := (2:ℝ)) (by norm_num) a b
  have h2 : (2:ENNReal) ^ (2:ℝ) = 4 := by
    rw [show (2:ℝ) = ((2:ℕ):ℝ) by norm_num, ENNReal.rpow_natCast]
    norm_num
  rwa [h2] at h

private lemma four_rpow_mul_two_rpow {r : ℝ} (hr : 0 ≤ r) :
    (4:ENNReal) ^ r * (2:ENNReal) ^ r = (8:ENNReal) ^ r := by
  rw [← ENNReal.mul_rpow_of_nonneg (4:ENNReal) (2:ENNReal) (z := r) hr]
  norm_num

private lemma eight_rpow_eq_ofReal {r : ℝ} (hr : 0 ≤ r) :
    (8:ENNReal) ^ r = ENNReal.ofReal ((8:ℝ) ^ r) := by
  rw [show (8:ENNReal) = ENNReal.ofReal (8:ℝ) from (ENNReal.ofReal_ofNat 8).symm,
    ENNReal.ofReal_rpow_of_nonneg (x := (8:ℝ)) (p := r) (by norm_num) hr]

private theorem ell2PolyDilationSupMaxLp_of_pointwise (P : Polynomial ℤ) {p : ℝ} (hp : 1 < p)
    (h : ∃ K : ℝ, 0 < K ∧ ∃ T D : Finset ℝ, ∀ (ψ : ℝ → ENNReal), Measurable ψ → ∀ x : ℝ,
      (⨆ N : ℕ, ∫⁻ s in Set.Ioc (0:ℝ) 1, ψ (x - (P.map (Int.castRingHom ℝ)).eval ((N:ℝ)*s)))
        ≤ ENNReal.ofReal K * ∑ c ∈ T, Commons.Analysis.Maximal.hlMax ψ (x - c)
          + ∑ c ∈ D, ψ (x - c)) :
    ∃ C : ℝ, 0 < C ∧ ∀ (n : ℕ) (f : Fin n → ℝ → ℝ), (∀ t, Measurable (f t)) →
      ∫⁻ x, (∑ t, (⨆ N : ℕ, ∫⁻ s in Set.Ioc (0 : ℝ) 1,
              ‖f t (x - (P.map (Int.castRingHom ℝ)).eval ((N : ℝ) * s))‖ₑ) ^ (2 : ℝ)) ^ (p / 2)
        ≤ ENNReal.ofReal (C ^ p) * ∫⁻ x, (Work.BourgainPlan.Maximal.ell2Sq f x) ^ (p / 2) := by
  obtain ⟨K, hK, T, D, hpoint⟩ := h
  have hp0 : (0:ℝ) ≤ p := le_of_lt (lt_trans zero_lt_one hp)
  have hq : (0:ℝ) < p/2 := by linarith
  let Q : Polynomial ℝ := P.map (Int.castRingHom ℝ)
  have hcell : 0 < ell2HLc p := ell2HLc_pos (p := p) hp
  let cU : ℝ := ((ell2HLc p)^p * (T.card:ℝ)^p * (T.card:ℝ)^(p/2) * (T.card:ℝ))^(1/p) + 1
  let cV : ℝ := ((D.card:ℝ)^p * (D.card:ℝ)^(p/2) * (D.card:ℝ))^(1/p) + 1
  let cT : ℝ := (8:ℝ)^(p/2) * ((K*cU)^p + cV^p)
  have hcUpos : 0 < cU := by positivity
  have hcVpos : 0 < cV := by positivity
  have hcTnonneg : (0:ℝ) ≤ cT := by positivity
  refine ⟨cT^(1/p) + 1, by positivity, ?_⟩
  intro n f hf
  let ψ : Fin n → ℝ → ENNReal := fun t x => ‖f t x‖ₑ
  have hψ : ∀ t, Measurable (ψ t) := fun t => (hf t).enorm
  let A : Fin n → ℝ → ENNReal := fun t x => ∑ c ∈ T, Commons.Analysis.Maximal.hlMax (ψ t) (x - c)
  let B : Fin n → ℝ → ENNReal := fun t x => ∑ c ∈ D, ψ t (x - c)
  let S : Fin n → ℝ → ENNReal := fun t x => ⨆ N : ℕ, ∫⁻ s in Set.Ioc (0:ℝ) 1,
      ψ t (x - Q.eval ((N:ℝ) * s))
  let U : ℝ → ENNReal := fun x => ∑ t, (ENNReal.ofReal K * A t x) ^ (2:ℝ)
  let V : ℝ → ENNReal := fun x => ∑ t, (B t x) ^ (2:ℝ)
  let R : ENNReal := ∫⁻ x, (∑ t, ψ t x ^ (2:ℝ)) ^ (p/2)
  have hSAB : ∀ t x, S t x ≤ ENNReal.ofReal K * A t x + B t x := fun t x => hpoint (ψ t) (hψ t) x
  have hA_meas : ∀ t, Measurable (A t) := fun t =>
    Finset.measurable_sum _ fun c _ =>
      (Commons.Analysis.Maximal.measurable_hlMax (ψ t)).comp (measurable_id.sub_const c)
  have hUmeas : Measurable U := by
    show Measurable (fun x => ∑ t, (ENNReal.ofReal K * A t x) ^ (2:ℝ))
    refine Finset.measurable_sum _ fun t _ => ?_
    exact (ENNReal.continuous_rpow_const (y := (2:ℝ))).measurable.comp
      (measurable_const.mul (hA_meas t))
  have hVmeas : Measurable V := by
    show Measurable (fun x => ∑ t, (B t x) ^ (2:ℝ))
    refine Finset.measurable_sum _ fun t _ => ?_
    exact (ENNReal.continuous_rpow_const (y := (2:ℝ))).measurable.comp
      (Finset.measurable_sum _ fun c _ => (hψ t).comp (measurable_id.sub_const c))
  have hUqmeas : Measurable (fun x => U x ^ (p/2)) :=
    (ENNReal.continuous_rpow_const (y := p/2)).measurable.comp hUmeas
  have hVqmeas : Measurable (fun x => V x ^ (p/2)) :=
    (ENNReal.continuous_rpow_const (y := p/2)).measurable.comp hVmeas
  have hUVsum_meas : Measurable (fun x => U x ^ (p/2) + V x ^ (p/2)) := hUqmeas.add hVqmeas
  have hpt1 : ∀ x, (∑ t, (S t x) ^ (2:ℝ)) ≤ 4 * (U x + V x) := by
    intro x
    calc ∑ t, (S t x) ^ (2:ℝ)
        ≤ ∑ t, (ENNReal.ofReal K * A t x + B t x) ^ (2:ℝ) :=
          Finset.sum_le_sum fun t _ => ENNReal.rpow_le_rpow (hSAB t x) (by norm_num)
      _ ≤ ∑ t, 4 * ((ENNReal.ofReal K * A t x) ^ (2:ℝ) + (B t x) ^ (2:ℝ)) :=
          Finset.sum_le_sum fun t _ => two_add_rpow_two_le _ _
      _ = 4 * (U x + V x) := by
          show (∑ t, 4 * ((ENNReal.ofReal K * A t x) ^ (2:ℝ) + (B t x) ^ (2:ℝ)))
            = 4 * ((∑ t, (ENNReal.ofReal K * A t x) ^ (2:ℝ)) + ∑ t, (B t x) ^ (2:ℝ))
          rw [← Finset.mul_sum, Finset.sum_add_distrib]
  have hpt2 : ∀ x, (∑ t, (S t x) ^ (2:ℝ)) ^ (p/2)
      ≤ (8:ENNReal) ^ (p/2) * (U x ^ (p/2) + V x ^ (p/2)) := by
    intro x
    refine (ENNReal.rpow_le_rpow (hpt1 x) hq.le).trans ?_
    rw [ENNReal.mul_rpow_of_nonneg _ _ hq.le]
    refine (mul_le_mul_of_nonneg_left (rpow_add_le_two_rpow_mul hq (U x) (V x)) zero_le).trans ?_
    rw [← mul_assoc, four_rpow_mul_two_rpow hq.le]
  have hconst : ∀ x : ℝ, U x ^ (p/2)
      = ENNReal.ofReal (K^p) * (∑ t, (A t x) ^ (2:ℝ)) ^ (p/2) := by
    intro x
    show (∑ t, (ENNReal.ofReal K * A t x) ^ (2:ℝ)) ^ (p/2)
      = ENNReal.ofReal (K^p) * (∑ t, (A t x) ^ (2:ℝ)) ^ (p/2)
    rw [Finset.sum_congr rfl (fun t (_ : t ∈ Finset.univ) =>
      ENNReal.mul_rpow_of_nonneg _ _ (by norm_num : (0:ℝ) ≤ 2))]
    have hK2 : (K ^ (2:ℝ)) ^ (p/2) = K^p := by
      rw [← Real.rpow_mul hK.le (2:ℝ) (p/2), show (2:ℝ) * (p/2) = p by ring]
    rw [← Finset.mul_sum,
      ENNReal.ofReal_rpow_of_nonneg (x := K) (p := (2:ℝ)) hK.le (by norm_num : (0:ℝ) ≤ 2),
      ENNReal.mul_rpow_of_nonneg _ _ hq.le,
      ENNReal.ofReal_rpow_of_nonneg (x := K ^ (2:ℝ)) (p := p/2)
        (by positivity : (0:ℝ) ≤ K ^ (2:ℝ)) hq.le,
      hK2]
  have hAqmeas : Measurable (fun x : ℝ => (∑ t, (A t x) ^ (2:ℝ)) ^ (p/2)) :=
    (ENNReal.continuous_rpow_const (y := p/2)).measurable.comp
      (Finset.measurable_sum _ fun t _ =>
        (ENNReal.continuous_rpow_const (y := (2:ℝ))).measurable.comp (hA_meas t))
  have hUbound : ∫⁻ x, U x ^ (p/2) ≤ ENNReal.ofReal ((K*cU) ^ p) * R := by
    have hUb := ell2_shift_hlMax_bound (p := p) hp T f hf
    calc ∫⁻ x, U x ^ (p/2)
        = ENNReal.ofReal (K^p) * (∫⁻ x, (∑ t, (A t x) ^ (2:ℝ)) ^ (p/2)) := by
          rw [lintegral_congr hconst, lintegral_const_mul _ hAqmeas]
      _ ≤ ENNReal.ofReal (K^p) * (ENNReal.ofReal (cU ^ p) * R) :=
          mul_le_mul_of_nonneg_left hUb zero_le
      _ = ENNReal.ofReal ((K*cU) ^ p) * R := by
          rw [← mul_assoc, ← ENNReal.ofReal_mul (Real.rpow_nonneg hK.le p),
            ← Real.mul_rpow hK.le hcUpos.le]
  have hVbound : ∫⁻ x, V x ^ (p/2) ≤ ENNReal.ofReal (cV ^ p) * R :=
    ell2_shift_raw_bound (p := p) hp D f hf
  have hfinal : ∫⁻ x, (∑ t, (S t x) ^ (2:ℝ)) ^ (p/2) ≤ ENNReal.ofReal cT * R := by
    calc ∫⁻ x, (∑ t, (S t x) ^ (2:ℝ)) ^ (p/2)
        ≤ ∫⁻ x, (8:ENNReal) ^ (p/2) * (U x ^ (p/2) + V x ^ (p/2)) := lintegral_mono hpt2
      _ = (8:ENNReal) ^ (p/2) * (∫⁻ x, (U x ^ (p/2) + V x ^ (p/2))) :=
          lintegral_const_mul _ hUVsum_meas
      _ = (8:ENNReal) ^ (p/2) * ((∫⁻ x, U x ^ (p/2)) + ∫⁻ x, V x ^ (p/2)) := by
          rw [lintegral_add_left hUqmeas]
      _ ≤ (8:ENNReal) ^ (p/2) * (ENNReal.ofReal ((K*cU) ^ p) * R + ENNReal.ofReal (cV ^ p) * R) :=
          mul_le_mul_of_nonneg_left (add_le_add hUbound hVbound) zero_le
      _ = ENNReal.ofReal ((8:ℝ)^(p/2) * ((K*cU)^p + cV^p)) * R := by
          rw [eight_rpow_eq_ofReal (by positivity : (0:ℝ) ≤ p/2), ← add_mul,
            ← ENNReal.ofReal_add (p := (K*cU)^p) (q := cV^p) (by positivity) (by positivity),
            ← mul_assoc,
            ← ENNReal.ofReal_mul (p := (8:ℝ)^(p/2)) (q := (K*cU)^p + cV^p) (by positivity)]
      _ = ENNReal.ofReal cT * R := rfl
  have hgoal : (∫⁻ x, (∑ t, (S t x) ^ (2:ℝ)) ^ (p/2))
      ≤ ENNReal.ofReal ((cT^(1/p) + 1) ^ p) * R :=
    hfinal.trans (mul_le_mul_of_nonneg_right
      (ENNReal.ofReal_le_ofReal (const_le_rpow cT p hp hcTnonneg)) zero_le)
  have hR : R = ∫⁻ x, (Work.BourgainPlan.Maximal.ell2Sq f x) ^ (p/2) := by
    show (∫⁻ x, (∑ t, ψ t x ^ (2:ℝ)) ^ (p/2)) = ∫⁻ x, (Work.BourgainPlan.Maximal.ell2Sq f x) ^ (p/2)
    refine lintegral_congr fun x => ?_
    rw [show (∑ t, ψ t x ^ (2:ℝ)) = Work.BourgainPlan.Maximal.ell2Sq f x from rfl]
  rw [hR] at hgoal
  exact hgoal


/-- **Bourgain's `ℓ²`-valued polynomial-dilation maximal inequality on `L^p`, `1 < p < ∞`.**

For `P ∈ ℤ[X]` nonnegative on `[0,∞)`, the maximal function
`sup_N ∫_{(0,1]} |f_t (x − P (N s))| ds` satisfies the vector-valued (Fefferman--Stein) maximal
inequality on `L^p(ℓ²)`, with a constant depending only on `P` and `p`. -/
theorem ell2PolyDilationSupMaxLp (P : Polynomial ℤ) (hP : ∀ x : ℝ, 0 ≤ x → 0 ≤ (P.map (Int.castRingHom ℝ)).eval x) {p : ℝ} (hp : 1 < p) : ∃ C : ℝ, 0 < C ∧ ∀ (n : ℕ) (f : Fin n → ℝ → ℝ), (∀ t, Measurable (f t)) → ∫⁻ x, (∑ t, (⨆ N : ℕ, ∫⁻ s in Set.Ioc (0 : ℝ) 1, ‖f t (x - (P.map (Int.castRingHom ℝ)).eval ((N : ℝ) * s))‖ₑ) ^ (2 : ℝ)) ^ (p / 2) ≤ ENNReal.ofReal (C ^ p) * ∫⁻ x, (Work.BourgainPlan.Maximal.ell2Sq f x) ^ (p / 2) :=
  ell2PolyDilationSupMaxLp_of_pointwise P hp (poly_sup_le_finset_hlMax P hP)

end Work.BourgainPlan.Maximal
