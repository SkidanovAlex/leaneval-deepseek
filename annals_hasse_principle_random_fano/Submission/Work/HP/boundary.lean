import Mathlib
import Submission.Work.HP.ArchDefs
import Submission.Work.HP.tau_basic
import Submission.Work.HP.volume_rNorm_ball
import Submission.Work.HP.volume_rNorm_ball_lt
import Submission.Work.HP.rNorm_smul
import Submission.Work.HP.BoundaryMain.exists_crit_zero
import Submission.Work.HP.BoundaryMain.card_grad_small

namespace Work.HP

open MeasureTheory MvPolynomial
open scoped ENNReal

/-! ## Basic lemmas on `rNorm`, `formEvalR`, `gradVec` -/

lemma rNorm_toR_eq_eNorm' (d n : ℕ) (v : Mon d n → ℤ) : rNorm (toR v) = eNorm v := rfl

section Basic

variable {ι : Type*}

private lemma norm_le_rNorm [Fintype ι] (v : ι → ℝ) : ‖v‖ ≤ rNorm v := by
  have key : (Finset.univ.sup (fun b => ‖v b‖₊) : NNReal) ≤ Real.toNNReal (rNorm v) := by
    refine Finset.sup_le (fun i _ => ?_)
    show ‖v i‖₊ ≤ Real.toNNReal (rNorm v)
    rw [← NNReal.coe_le_coe, coe_nnnorm, Real.coe_toNNReal']
    rw [max_eq_left (rNorm_nonneg v), Real.norm_eq_abs]
    exact abs_apply_le_rNorm v i
  calc ‖v‖ = ((Finset.univ.sup (fun b => ‖v b‖₊) : NNReal) : ℝ) := Pi.norm_def v
    _ ≤ (Real.toNNReal (rNorm v) : ℝ) := by exact_mod_cast key
    _ = rNorm v := Real.coe_toNNReal _ (rNorm_nonneg v)

lemma continuous_rNorm' [Fintype ι] : Continuous (fun v : ι → ℝ => rNorm v) := by
  have h : (fun v : ι → ℝ => rNorm v) = fun v => Real.sqrt (∑ i, v i ^ 2) := rfl
  rw [h]
  exact Real.continuous_sqrt.comp (continuous_finsetSum _ (fun i _ => (continuous_apply i).pow 2))

lemma isClosed_rNorm_le [Fintype ι] (r : ℝ) : IsClosed {v : ι → ℝ | rNorm v ≤ r} :=
  isClosed_le continuous_rNorm' continuous_const

lemma isCompact_rNorm_le [Fintype ι] (r : ℝ) : IsCompact {v : ι → ℝ | rNorm v ≤ r} := by
  refine (ProperSpace.isCompact_closedBall (0 : ι → ℝ) r).of_isClosed_subset
    (isClosed_rNorm_le r) ?_
  intro v hv
  rw [Metric.mem_closedBall, dist_zero_right]
  exact le_trans (norm_le_rNorm v) hv

end Basic

lemma continuous_formEvalR' (d n : ℕ) (c : Mon d n → ℝ) :
    Continuous (fun x : Fin (n + 1) → ℝ => formEvalR d n c x) := by
  unfold formEvalR veronese
  refine continuous_finsetSum _ (fun m _ => ?_)
  refine Continuous.mul continuous_const ?_
  exact continuous_finsetProd _ (fun i _ => (continuous_apply i).pow _)

lemma formEvalR_add' (d n : ℕ) (u v : Mon d n → ℝ) (x : Fin (n + 1) → ℝ) :
    formEvalR d n (u + v) x = formEvalR d n u x + formEvalR d n v x := by
  simp only [formEvalR, Pi.add_apply, add_mul, Finset.sum_add_distrib]

lemma formEvalR_affine (d n : ℕ) (A D : Mon d n → ℝ) (t : ℝ) (x : Fin (n + 1) → ℝ) :
    formEvalR d n (A + t • D) x = formEvalR d n A x + t * formEvalR d n D x := by
  rw [formEvalR_add', formEvalR_smul]

lemma formEvalR_point_smul' (d n : ℕ) (c : Mon d n → ℝ) (t : ℝ) (x : Fin (n + 1) → ℝ) :
    formEvalR d n c (t • x) = t ^ d * formEvalR d n c x := by
  have hprod : ∀ m : Mon d n, (∏ i : Fin (n + 1), (t * x i) ^ ((m.1 i : ℕ)))
      = t ^ d * ∏ i : Fin (n + 1), x i ^ ((m.1 i : ℕ)) := by
    intro m
    rw [Finset.prod_congr rfl (fun i _ => mul_pow t (x i) ((m.1 i : ℕ))),
      Finset.prod_mul_distrib, Finset.prod_pow_eq_pow_sum, m.2]
  simp only [formEvalR, veronese, Pi.smul_apply, smul_eq_mul]
  rw [Finset.sum_congr rfl (fun m _ => by rw [hprod m]), Finset.mul_sum]
  exact Finset.sum_congr rfl (fun m _ => by ring)

private lemma finite_eNorm_le (d n : ℕ) (A : ℝ) : {a : Mon d n → ℤ | eNorm a ≤ A}.Finite := by
  have hpi : ({a : Mon d n → ℤ | ∀ m, a m ∈ Finset.Icc (-(⌈A⌉₊ : ℤ)) (⌈A⌉₊ : ℤ)}).Finite := by
    have h := Set.Finite.pi (t := fun _m : Mon d n =>
      (Finset.Icc (-(⌈A⌉₊ : ℤ)) (⌈A⌉₊ : ℤ) : Set ℤ)) (fun _ => Finset.finite_toSet _)
    simpa [Set.pi] using h
  refine hpi.subset ?_
  intro a ha
  simp only [Set.mem_ofPred_eq] at ha ⊢
  intro m
  rw [Finset.mem_Icc]
  have h1 : |((a m : ℤ) : ℝ)| ≤ A := by
    calc |((a m : ℤ) : ℝ)| = |(toR a) m| := rfl
      _ ≤ rNorm (toR a) := abs_apply_le_rNorm _ _
      _ = eNorm a := rNorm_toR_eq_eNorm' d n a
      _ ≤ A := ha
  have hceil : A ≤ (((⌈A⌉₊ : ℤ)) : ℝ) := by
    have := Nat.le_ceil A; push_cast; exact this
  have hle := abs_le.mp h1
  refine ⟨?_, ?_⟩
  · exact_mod_cast (show -(((⌈A⌉₊ : ℤ)) : ℝ) ≤ ((a m : ℤ) : ℝ) from by linarith [hle.1, hceil])
  · exact_mod_cast (show ((a m : ℤ) : ℝ) ≤ ((⌈A⌉₊ : ℤ) : ℝ) from by linarith [hle.2, hceil])

lemma gradVec_add (d n : ℕ) (u v : Mon d n → ℝ) (x : Fin (n + 1) → ℝ) :
    gradVec d n (u + v) x = gradVec d n u x + gradVec d n v x := by
  funext j
  simp only [gradVec, gradF, Pi.add_apply, add_mul, Finset.sum_add_distrib]

lemma NN_ge (d n : ℕ) (hd : 1 ≤ d) : n + 1 ≤ NN d n := by
  let g : Fin (n + 1) → Fin (n + 1) → Fin (d + 1) :=
    fun i l => if l = i then ⟨d, Nat.lt_succ_self d⟩ else 0
  have hsum : ∀ i : Fin (n + 1), (∑ l : Fin (n + 1), (g i l : ℕ)) = d := by
    intro i
    show (∑ l : Fin (n + 1),
      ((if l = i then (⟨d, Nat.lt_succ_self d⟩ : Fin (d + 1)) else 0 : Fin (d + 1)) : ℕ)) = d
    rw [Finset.sum_eq_single i (fun l _ hl => by rw [if_neg hl]; rfl)
      (fun h => absurd (Finset.mem_univ i) h), if_pos rfl]
  let f : Fin (n + 1) → Mon d n := fun i => ⟨g i, hsum i⟩
  have hf : Function.Injective f := by
    intro i j hij
    have h1 : (f i).1 i = (f j).1 i := by rw [hij]
    have h2 : (f i).1 i = (⟨d, Nat.lt_succ_self d⟩ : Fin (d + 1)) := by simp [f, g]
    have h3 : (f j).1 i = (if i = j then (⟨d, Nat.lt_succ_self d⟩ : Fin (d + 1)) else 0) := by
      simp only [f, g]
    rw [h2, h3] at h1
    by_cases h : i = j
    · exact h
    · rw [if_neg h] at h1
      exact absurd (congrArg Fin.val h1) (by simp; omega)
  calc n + 1 = Fintype.card (Fin (n + 1)) := by simp
    _ ≤ Fintype.card (Mon d n) := Fintype.card_le_of_injective f hf
    _ = NN d n := rfl

lemma one_sub_pow_le_mul (t : ℝ) (ht : 0 ≤ t) (k : ℕ) : 1 - t ^ k ≤ k * (1 - t) := by
  have h := one_add_mul_le_pow (a := t - 1) (by linarith) k
  have h1 : (1 : ℝ) + (t - 1) = t := by ring
  rw [h1] at h
  nlinarith [h]

/-- Measures of a thin spherical shell. -/
lemma volume_shell_toReal_le {N : ℕ} (hN : 1 ≤ N) (t : ℝ) (ht : 0 ≤ t) (ht1 : t ≤ 1) :
    (volume {y : Fin N → ℝ | t < rNorm y ∧ rNorm y ≤ 1}).toReal
      ≤ (N : ℝ) * (1 - t) * (volume {y : Fin N → ℝ | rNorm y ≤ 1}).toReal := by
  haveI : Nonempty (Fin N) := ⟨⟨0, hN⟩⟩
  set Vl : ℝ≥0∞ := volume {y : Fin N → ℝ | rNorm y ≤ 1} with hVl
  have hVlfin : Vl ≠ ⊤ := by rw [hVl]; exact (isCompact_rNorm_le 1).measure_lt_top.ne
  have h2 : volume {y : Fin N → ℝ | rNorm y ≤ t} = ENNReal.ofReal (t ^ N) * Vl := by
    simpa only [sub_zero, Fintype.card_fin, hVl] using
      (volume_rNorm_ball (0 : Fin N → ℝ) t ht)
  have h2fin : volume {y : Fin N → ℝ | rNorm y ≤ t} ≠ ⊤ := by
    rw [h2]; exact ENNReal.mul_ne_top ENNReal.ofReal_ne_top hVlfin
  have hdisj : Disjoint {y : Fin N → ℝ | t < rNorm y ∧ rNorm y ≤ 1}
      {y : Fin N → ℝ | rNorm y ≤ t} := by
    rw [Set.disjoint_left]
    rintro y ⟨h1, -⟩ h2'
    exact absurd h2' (not_le.mpr h1)
  have hmeas2 : MeasurableSet {y : Fin N → ℝ | rNorm y ≤ t} := (isClosed_rNorm_le t).measurableSet
  have hunion : {y : Fin N → ℝ | rNorm y ≤ 1}
      = {y : Fin N → ℝ | t < rNorm y ∧ rNorm y ≤ 1} ∪ {y : Fin N → ℝ | rNorm y ≤ t} := by
    ext y
    constructor
    · intro hy
      by_cases h : t < rNorm y
      · exact Or.inl ⟨h, hy⟩
      · exact Or.inr (not_lt.mp h)
    · rintro (⟨-, h⟩ | h)
      · exact h
      · exact le_trans h ht1
  have hshellfin : volume {y : Fin N → ℝ | t < rNorm y ∧ rNorm y ≤ 1} ≠ ⊤ := by
    refine ne_of_lt (lt_of_le_of_lt (measure_mono ?_) (isCompact_rNorm_le 1).measure_lt_top)
    intro y hy; exact hy.2
  have hunion2 : Vl = volume {y : Fin N → ℝ | t < rNorm y ∧ rNorm y ≤ 1}
      + ENNReal.ofReal (t ^ N) * Vl := by
    conv_lhs => rw [hVl, hunion, measure_union hdisj hmeas2]
    rw [h2]
  have htoReal : Vl.toReal = (volume {y : Fin N → ℝ | t < rNorm y ∧ rNorm y ≤ 1}).toReal
      + t ^ N * Vl.toReal := by
    conv_lhs => rw [hunion2]
    rw [ENNReal.toReal_add hshellfin (ENNReal.mul_ne_top ENNReal.ofReal_ne_top hVlfin),
      ENNReal.toReal_mul, ENNReal.toReal_ofReal (by positivity)]
  have hbound : 1 - t ^ N ≤ (N : ℝ) * (1 - t) := one_sub_pow_le_mul t ht N
  nlinarith [htoReal, hbound, ENNReal.toReal_nonneg (a := Vl)]

/-- Transferring a critical zero of a nearby form to a gradient bound on a small ball. -/
lemma grad_bound_near (d n : ℕ)
    (Cg : ℝ) (hCg : 0 ≤ Cg)
    (hgrad : ∀ (b : Mon d n → ℝ) (x : Fin (n + 1) → ℝ), rNorm x ≤ 1 →
        rNorm (gradVec d n b x) ≤ Cg * rNorm b)
    (Cl : ℝ) (hCl : 0 ≤ Cl)
    (hgradlip : ∀ (b : Mon d n → ℝ) (x y : Fin (n + 1) → ℝ), rNorm x ≤ 2 → rNorm y ≤ 2 →
        rNorm (gradVec d n b y - gradVec d n b x) ≤ Cl * rNorm b * rNorm (y - x))
    (A : ℝ) (hA : 1 ≤ A) (a : Mon d n → ℤ) (c : Mon d n → ℝ) (x y : Fin (n + 1) → ℝ)
    (hae : eNorm a ≤ A) (hca : rNorm (c - toR a) ≤ 1) (hcx : gradVec d n c x = 0)
    (hx : rNorm x = 1) (hy1 : rNorm y ≤ 1) (hyx : rNorm (y - x) ≤ 1 / A) :
    rNorm (gradVec d n (toR a) y) ≤ Cg + 2 * Cl := by
  have hsplit : gradVec d n (toR a) y
      = gradVec d n (toR a - c) y + (gradVec d n c y - gradVec d n c x) := by
    rw [show toR a = (toR a - c) + c from by abel, gradVec_add, hcx]
    abel
  have hca' : rNorm (toR a - c) ≤ 1 := by rw [rNorm_sub_comm]; exact hca
  have hcA : rNorm c ≤ A + 1 := by
    have h1 : rNorm c ≤ rNorm (toR a) + rNorm (toR a - c) := by
      calc rNorm c = rNorm (toR a - (toR a - c)) := by rw [sub_sub_cancel]
        _ ≤ rNorm (toR a) + rNorm (toR a - c) := rNorm_sub_le _ _
    have h2 : rNorm (toR a) = eNorm a := rNorm_toR_eq_eNorm' d n a
    rw [h2] at h1
    linarith
  calc rNorm (gradVec d n (toR a) y)
      = rNorm (gradVec d n (toR a - c) y + (gradVec d n c y - gradVec d n c x)) := by rw [hsplit]
    _ ≤ rNorm (gradVec d n (toR a - c) y) + rNorm (gradVec d n c y - gradVec d n c x) :=
        rNorm_add_le _ _
    _ ≤ Cg * rNorm (toR a - c) + Cl * rNorm c * rNorm (y - x) := by
        refine add_le_add (hgrad (toR a - c) y hy1) ?_
        exact hgradlip c x y (by rw [hx]; norm_num) (by linarith)
    _ ≤ Cg * 1 + Cl * (A + 1) * (1 / A) := by
        refine add_le_add ?_ ?_
        · exact mul_le_mul_of_nonneg_left hca' hCg
        · exact mul_le_mul (mul_le_mul_of_nonneg_left hcA hCl) hyx (rNorm_nonneg _) (mul_nonneg hCl (by linarith))
    _ ≤ Cg + 2 * Cl := by
        have hstep : Cl * (A + 1) * (1 / A) ≤ 2 * Cl := by
          have hdiv : (A + 1) * (1 / A) ≤ 2 := by
            rw [mul_one_div, div_le_iff₀ (by linarith)]
            linarith
          calc Cl * (A + 1) * (1 / A) = Cl * ((A + 1) * (1 / A)) := by ring
            _ ≤ Cl * 2 := mul_le_mul_of_nonneg_left hdiv hCl
            _ = 2 * Cl := by ring
        linarith


theorem boundary (d n : ℕ) (hd : 2 ≤ d) (hn : 3 ≤ n)
    (hgrad : ∃ C, 0 < C ∧ ∀ (a : Mon d n → ℝ) (x : Fin (n + 1) → ℝ), rNorm x ≤ 1 →
        rNorm (gradVec d n a x) ≤ C * rNorm a)
    (hgradlip : ∃ C, 0 < C ∧ ∀ (a : Mon d n → ℝ) (x y : Fin (n + 1) → ℝ), rNorm x ≤ 2 → rNorm y ≤ 2 →
        rNorm (gradVec d n a y - gradVec d n a x) ≤ C * rNorm a * rNorm (y - x))
    (htay : ∃ C, 0 < C ∧ ∀ (a : Mon d n → ℝ) (x y : Fin (n + 1) → ℝ), rNorm x ≤ 2 → rNorm y ≤ 2 →
        |formEvalR d n a y - formEvalR d n a x - dotR (gradVec d n a x) (y - x)|
          ≤ C * rNorm a * (rNorm (y - x)) ^ 2)
    (hval : ∃ C, 0 < C ∧ ∀ (a : Mon d n → ℝ) (x : Fin (n + 1) → ℝ), rNorm x ≤ 2 →
        |formEvalR d n a x| ≤ C * rNorm a)
    (hclose : IsClosed {a : Mon d n → ℝ | IPt d n a}) :
    ∃ K : ℝ, 0 < K ∧ ∀ A : ℝ, 1 ≤ A → ((Uset d n A).ncard : ℝ) ≤ K * A ^ (NN d n - 1) := by
  classical
  obtain ⟨Cg, hCg, hgradb⟩ := hgrad
  obtain ⟨Cl, hCl, hgradlipb⟩ := hgradlip
  obtain ⟨Ctay, hCtay, htayb⟩ := htay
  obtain ⟨Cval, hCval, hvalb⟩ := hval
  have hd1 : 1 ≤ d := by omega
  have hn1 : 1 ≤ n + 1 := by omega
  have hNN : n + 1 ≤ NN d n := NN_ge d n hd1
  have hCg0 : 0 ≤ Cg := le_of_lt hCg
  have hCl0 : 0 ≤ Cl := le_of_lt hCl
  have hC1 : 0 < Cg + 2 * Cl := by linarith
  obtain ⟨K0, hK0pos, hK0⟩ := BoundaryMain.card_grad_small d n hd (Cg + 2 * Cl) hC1
  set Cst : ℝ := ((n : ℝ) + 1) * (3 / 4) * 8 ^ (n + 1) with hCst
  have hCstpos : 0 < Cst := by rw [hCst]; positivity
  have hmain : ∀ A : ℝ, 2 ≤ A →
      ((Uset d n A).ncard : ℝ) ≤ (K0 + 1) * Cst * A ^ (NN d n - 1) := by
    intro A hA2
    have hA1 : (1 : ℝ) ≤ A := by linarith
    set F : Set (Mon d n → ℤ) := Uset d n A with hF
    have hgoal : ((F.ncard : ℝ)) ≤ (K0 + 1) * Cst * A ^ (NN d n - 1) := by
      have hFfin : F.Finite := (finite_eNorm_le d n A).subset (fun a ha => (by
        rw [hF] at ha; exact ha.2.1))
      have hFmem : ∀ a : Mon d n → ℤ, a ∈ F ↔ IsPrim a ∧ eNorm a ≤ A ∧ IPt d n (toR a) ∧
          ¬ (∀ y : Mon d n → ℝ, rNorm (toR a - y) ≤ 1 → IPt d n y) := by
        intro a; rw [hF]; exact Iff.rfl
      have hx_exists : ∀ a : Mon d n → ℤ, a ∈ F →
          ∃ x : Fin (n + 1) → ℝ, rNorm x = 1 ∧
            ∀ y : Fin (n + 1) → ℝ, rNorm y ≤ 1 → rNorm (y - x) ≤ 1 / A →
              rNorm (gradVec d n (toR a) y) ≤ Cg + 2 * Cl := by
        intro a ha
        obtain ⟨hprim, hnorm, hIPt, hnot⟩ := (hFmem a).mp ha
        have hb : ∃ b : Mon d n → ℝ, rNorm (b - toR a) ≤ 1 ∧ ¬ IPt d n b := by
          by_contra hb
          apply hnot
          intro y hy
          by_contra hy'
          exact hb ⟨y, by rwa [rNorm_sub_comm], hy'⟩
        obtain ⟨b, hb1, hb2⟩ := hb
        obtain ⟨c, hc1, x, hx1, hx2, hx3⟩ :=
          BoundaryMain.exists_crit_zero d n hclose Ctay Cval htayb hvalb a b hIPt hb1 hb2
        refine ⟨x, hx1, fun y hy1 hy2 => ?_⟩
        exact grad_bound_near d n Cg hCg0 hgradb Cl hCl0 hgradlipb A hA1 a c x y hnorm hc1 hx3 hx1 hy1 hy2
      set xfun : (Mon d n → ℤ) → (Fin (n + 1) → ℝ) := fun a =>
        if ha : a ∈ F then Classical.choose (hx_exists a ha) else 0 with hxfun_def
      have hxfun : ∀ a (ha : a ∈ F), rNorm (xfun a) = 1 ∧
          ∀ y : Fin (n + 1) → ℝ, rNorm y ≤ 1 → rNorm (y - xfun a) ≤ 1 / A →
            rNorm (gradVec d n (toR a) y) ≤ Cg + 2 * Cl := by
        intro a ha
        have key : xfun a = Classical.choose (hx_exists a ha) := by
          rw [hxfun_def]
          simp only
          rw [dif_pos ha]
        rw [key]
        exact Classical.choose_spec (hx_exists a ha)
      set r : ℝ := 1 / (8 * A) with hr
      have hrpos : 0 < r := by rw [hr]; positivity
      set ζ : (Mon d n → ℤ) → (Fin (n + 1) → ℝ) := fun a => (1 - 1 / (2 * A)) • xfun a with hζ
      set Bs : (Mon d n → ℤ) → Set (Fin (n + 1) → ℝ) := fun a => {y | rNorm (y - ζ a) ≤ r} with hBs
      have hζn : ∀ a ∈ F, rNorm (ζ a) = 1 - 1 / (2 * A) := by
        intro a ha
        rw [hζ, rNorm_smul', (hxfun a ha).1, mul_one, abs_of_nonneg]
        rw [sub_nonneg, div_le_one (by positivity)]
        linarith
      have hζx : ∀ a ∈ F, rNorm (ζ a - xfun a) = 1 / (2 * A) := by
        intro a ha
        have hsub : ζ a - xfun a = (-(1 / (2 * A))) • xfun a := by
          rw [hζ]
          ext i
          simp only [Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
          ring
        rw [hsub, rNorm_smul', (hxfun a ha).1, mul_one, abs_neg, abs_of_pos (by positivity)]
      have hball : ∀ a ∈ F, ∀ y, y ∈ Bs a →
          rNorm y ≤ 1 ∧ 1 - 3 / (4 * A) < rNorm y ∧ 1 / 2 ≤ rNorm y ∧
          rNorm (y - xfun a) ≤ 1 / A ∧
          rNorm (gradVec d n (toR a) y) ≤ Cg + 2 * Cl := by
        intro a ha y hy
        have hζa := hζn a ha
        have hζx' := hζx a ha
        have hyr : rNorm (y - ζ a) ≤ r := by simpa only [hBs, Set.mem_ofPred_eq] using hy
        have hy8 : rNorm (y - ζ a) ≤ 1 / (8 * A) := by rw [← hr]; exact hyr
        have hyup : rNorm y ≤ 1 := by
          have h1 : rNorm y ≤ rNorm (ζ a) + rNorm (y - ζ a) := by
            calc rNorm y = rNorm (ζ a + (y - ζ a)) := by rw [add_sub_cancel]
              _ ≤ rNorm (ζ a) + rNorm (y - ζ a) := rNorm_add_le _ _
          rw [hζa] at h1
          have h2 : 1 / (8 * A) ≤ 1 / (2 * A) := by
            rw [div_le_div_iff₀ (by positivity) (by positivity)]; linarith
          linarith
        have hylow5 : 1 - 5 / (8 * A) ≤ rNorm y := by
          have h1 : rNorm (ζ a) ≤ rNorm y + rNorm (y - ζ a) := by
            calc rNorm (ζ a) = rNorm (y - (y - ζ a)) := by rw [sub_sub_cancel]
              _ ≤ rNorm y + rNorm (y - ζ a) := rNorm_sub_le _ _
          rw [hζa] at h1
          have h2 : 1 / (8 * A) + 1 / (2 * A) = 5 / (8 * A) := by field_simp; ring
          linarith [h1, hy8, h2]
        have hylow : 1 / 2 ≤ rNorm y := by
          have h2 : 5 / (8 * A) ≤ 1 / 2 := by
            rw [div_le_div_iff₀ (by positivity) (by norm_num)]; linarith
          linarith
        have hyt : 1 - 3 / (4 * A) < rNorm y := by
          have h2 : 5 / (8 * A) < 3 / (4 * A) := by
            rw [div_lt_div_iff₀ (by positivity) (by positivity)]; linarith
          linarith
        have hyx : rNorm (y - xfun a) ≤ 1 / A := by
          have h1 : rNorm (y - xfun a) ≤ rNorm (y - ζ a) + rNorm (ζ a - xfun a) := by
            calc rNorm (y - xfun a) = rNorm ((y - ζ a) + (ζ a - xfun a)) := by abel
              _ ≤ rNorm (y - ζ a) + rNorm (ζ a - xfun a) := rNorm_add_le _ _
          rw [hζx'] at h1
          have h2 : 1 / (8 * A) + 1 / (2 * A) ≤ 1 / A := by
            have he : 1 / (8 * A) + 1 / (2 * A) = 5 / (8 * A) := by
              field_simp; ring
            rw [he, div_le_div_iff₀ (by positivity) (by positivity)]
            linarith
          linarith
        exact ⟨hyup, hyt, hylow, hyx, (hxfun a ha).2 y hyup hyx⟩
      set Vl : ℝ≥0∞ := volume {y : Fin (n + 1) → ℝ | rNorm y ≤ 1} with hVl
      have hVlfin : Vl ≠ ⊤ := by rw [hVl]; exact (isCompact_rNorm_le 1).measure_lt_top.ne
      have hBmeas : ∀ a ∈ hFfin.toFinset, MeasurableSet (Bs a) := by
        intro a _
        have hcl : IsClosed (Bs a) := by
          rw [hBs]
          exact isClosed_le (continuous_rNorm'.comp (continuous_id.sub continuous_const)) continuous_const
        exact hcl.measurableSet
      have hvol : ∀ a ∈ hFfin.toFinset,
          volume (Bs a) = ENNReal.ofReal (r ^ (n + 1)) * Vl := by
        intro a _
        have hvr := volume_rNorm_ball (ζ a) r (le_of_lt hrpos)
        simpa only [hBs, hvr, Fintype.card_fin, hVl]
      set M : ℕ := ⌈K0 * A ^ (NN d n - (n + 1))⌉₊ with hM
      set Λ : Set (Fin (n + 1) → ℝ) := {y | 1 - 3 / (4 * A) < rNorm y ∧ rNorm y ≤ 1} with hΛ
      have hΛmeas : MeasurableSet Λ := by
        have h1 : MeasurableSet {y : Fin (n + 1) → ℝ | 1 - 3 / (4 * A) < rNorm y} :=
          isOpen_lt (show Continuous (fun _ : Fin (n + 1) → ℝ => 1 - 3 / (4 * A))
              from continuous_const) continuous_rNorm' |>.measurableSet
        have h2 : MeasurableSet {y : Fin (n + 1) → ℝ | rNorm y ≤ 1} :=
          (isClosed_rNorm_le 1).measurableSet
        have h3 : {y : Fin (n + 1) → ℝ | 1 - 3 / (4 * A) < rNorm y ∧ rNorm y ≤ 1}
            = {y : Fin (n + 1) → ℝ | 1 - 3 / (4 * A) < rNorm y}
              ∩ {y : Fin (n + 1) → ℝ | rNorm y ≤ 1} := by
          ext y; simp
        rw [hΛ, h3]
        exact h1.inter h2
      let mult : (Fin (n + 1) → ℝ) → ℝ≥0∞ :=
        fun y => ((hFfin.toFinset.filter (fun a => y ∈ Bs a)).card : ℝ≥0∞)
      have hpt : ∀ y : Fin (n + 1) → ℝ,
          mult y ≤ Λ.indicator (fun _ => (↑M : ℝ≥0∞)) y := by
        intro y
        by_cases hy : y ∈ Λ
        · rw [Set.indicator_of_mem hy]
          change ((hFfin.toFinset.filter (fun a => y ∈ Bs a)).card : ℝ≥0∞) ≤ (↑M : ℝ≥0∞)
          have hsub : ↑(hFfin.toFinset.filter (fun a => y ∈ Bs a)) ⊆
              {a : Mon d n → ℤ | eNorm a ≤ A ∧ rNorm (gradVec d n (toR a) y) ≤ Cg + 2 * Cl} := by
            intro a ha'
            rw [Finset.mem_coe, Finset.mem_filter] at ha'
            obtain ⟨haF, hya⟩ := ha'
            exact ⟨((hFmem a).mp (hFfin.mem_toFinset.mp haF)).2.1,
              (hball a (hFfin.mem_toFinset.mp haF) y hya).2.2.2.2⟩
          have hfin : ({a : Mon d n → ℤ | eNorm a ≤ A ∧
              rNorm (gradVec d n (toR a) y) ≤ Cg + 2 * Cl} : Set _).Finite :=
            (finite_eNorm_le d n A).subset (fun a ha => ha.1)
          have hcard1 : (hFfin.toFinset.filter (fun a => y ∈ Bs a)).card ≤
              ({a : Mon d n → ℤ | eNorm a ≤ A ∧
                rNorm (gradVec d n (toR a) y) ≤ Cg + 2 * Cl} : Set _).ncard := by
            rw [← Set.ncard_coe_finset (hFfin.toFinset.filter (fun a => y ∈ Bs a))]
            exact Set.ncard_le_ncard hsub hfin
          have hy12 : 1 / 2 ≤ rNorm y := by
            have h1 : 1 - 3 / (4 * A) < rNorm y := by rw [hΛ] at hy; exact hy.1
            have h2 : 5 / 8 ≤ 1 - 3 / (4 * A) := by
              have h3 : 3 / (4 * A) ≤ 3 / 8 := by
                rw [div_le_div_iff₀ (by positivity) (by norm_num)]; linarith
              linarith
            linarith
          have hcard2 : (({a : Mon d n → ℤ | eNorm a ≤ A ∧
              rNorm (gradVec d n (toR a) y) ≤ Cg + 2 * Cl} : Set _).ncard : ℝ)
                ≤ K0 * A ^ (NN d n - (n + 1)) :=
            hK0 y hy12 A hA1
          have hcard3 : (hFfin.toFinset.filter (fun a => y ∈ Bs a)).card ≤ M := by
            have h1 : ((hFfin.toFinset.filter (fun a => y ∈ Bs a)).card : ℝ) ≤
                K0 * A ^ (NN d n - (n + 1)) :=
              le_trans (by exact_mod_cast hcard1) hcard2
            have h2 : K0 * A ^ (NN d n - (n + 1)) ≤ (M : ℝ) := by
              rw [hM]; exact Nat.le_ceil _
            exact_mod_cast le_trans h1 h2
          exact_mod_cast hcard3
        · rw [Set.indicator_of_notMem hy]
          change ((hFfin.toFinset.filter (fun a => y ∈ Bs a)).card : ℝ≥0∞) ≤ 0
          have hzero : (hFfin.toFinset.filter (fun a => y ∈ Bs a)).card = 0 := by
            rw [Finset.card_eq_zero]
            apply Finset.filter_eq_empty_iff.mpr
            intro a haF hya
            have hb := (hball a (hFfin.mem_toFinset.mp haF) y hya)
            exact hy (by rw [hΛ]; exact ⟨hb.2.1, hb.1⟩)
          rw [hzero]
          simp
      have hlayer : ∑ a ∈ hFfin.toFinset, volume (Bs a) = ∫⁻ y, mult y := by
        have hpoint : ∀ a ∈ hFfin.toFinset,
            volume (Bs a) = ∫⁻ y, (Bs a).indicator (fun _ => (1 : ℝ≥0∞)) y := by
          intro a ha
          rw [MeasureTheory.lintegral_indicator_const (hBmeas a ha) (1 : ℝ≥0∞)]
          simp
        calc ∑ a ∈ hFfin.toFinset, volume (Bs a)
            = ∑ a ∈ hFfin.toFinset, ∫⁻ y, (Bs a).indicator (fun _ => (1 : ℝ≥0∞)) y :=
              Finset.sum_congr rfl hpoint
          _ = ∫⁻ y, ∑ a ∈ hFfin.toFinset, (Bs a).indicator (fun _ => (1 : ℝ≥0∞)) y :=
              (MeasureTheory.lintegral_finsetSum hFfin.toFinset
                (fun a ha => measurable_const.indicator (hBmeas a ha))).symm
          _ = ∫⁻ y, mult y := by
              congr 1
              funext y
              change (∑ a ∈ hFfin.toFinset, (Bs a).indicator (fun _ => (1 : ℝ≥0∞)) y)
                  = ((hFfin.toFinset.filter (fun a => y ∈ Bs a)).card : ℝ≥0∞)
              have hite : (∑ a ∈ hFfin.toFinset, (Bs a).indicator (fun _ => (1 : ℝ≥0∞)) y)
                  = ∑ a ∈ hFfin.toFinset, (if y ∈ Bs a then (1 : ℝ≥0∞) else 0) :=
                Finset.sum_congr rfl (fun a _ => by
                  by_cases hya : y ∈ Bs a
                  · rw [Set.indicator_of_mem hya]; simp [hya]
                  · rw [Set.indicator_of_notMem hya]; simp [hya])
              rw [hite]
              exact_mod_cast (Finset.card_filter (fun a => y ∈ Bs a) hFfin.toFinset).symm
      have hint : ∑ a ∈ hFfin.toFinset, volume (Bs a) ≤ (M : ℝ≥0∞) * volume Λ := by
        rw [hlayer]
        calc ∫⁻ y, mult y
            ≤ ∫⁻ y, Λ.indicator (fun _ => (↑M : ℝ≥0∞)) y := by
              refine lintegral_mono ?_
              intro y
              exact hpt y
          _ = (↑M : ℝ≥0∞) * volume Λ :=
              MeasureTheory.lintegral_indicator_const hΛmeas (↑M : ℝ≥0∞)
      have hbase : ∑ a ∈ hFfin.toFinset, volume (Bs a)
          = ((hFfin.toFinset.card : ℝ≥0∞)) * (ENNReal.ofReal (r ^ (n + 1)) * Vl) := by
        rw [Finset.sum_congr rfl hvol, Finset.sum_const, nsmul_eq_mul]
      have hΛfin : volume Λ ≠ ⊤ := by
        refine ne_of_lt (lt_of_le_of_lt (measure_mono ?_) (isCompact_rNorm_le 1).measure_lt_top)
        intro y hy
        rw [hΛ] at hy
        exact hy.2
      have hRfin : (M : ℝ≥0∞) * volume Λ ≠ ⊤ :=
        ENNReal.mul_ne_top (ENNReal.natCast_ne_top M) hΛfin
      have hchain : ((hFfin.toFinset.card : ℝ≥0∞)) * (ENNReal.ofReal (r ^ (n + 1)) * Vl) ≤
          (M : ℝ≥0∞) * volume Λ := by
        rw [← hbase]
        exact hint
      have hchainR : (F.ncard : ℝ) * (r ^ (n + 1) * Vl.toReal) ≤
          (M : ℝ) * (volume Λ).toReal := by
        have h1 := ENNReal.toReal_mono hRfin hchain
        simp only [ENNReal.toReal_mul, ENNReal.toReal_ofReal (by positivity : (0:ℝ) ≤ r ^ (n + 1)),
          ENNReal.toReal_natCast] at h1
        have h2 : ((hFfin.toFinset.card : ℝ)) = (F.ncard : ℝ) := by
          rw [Set.ncard_eq_toFinset_card F hFfin]
        rw [h2] at h1
        exact h1
      have hΛle : (volume Λ).toReal ≤ ((n : ℝ) + 1) * (3 / (4 * A)) * Vl.toReal := by
        have h2 : 3 / (4 * A) ≤ 1 := by
          rw [div_le_one (by positivity)]
          linarith
        have h3 : (0 : ℝ) ≤ 3 / (4 * A) := by positivity
        have ht0 : (0 : ℝ) ≤ 1 - 3 / (4 * A) := by linarith
        have ht1 : (1 : ℝ) - 3 / (4 * A) ≤ 1 := by linarith
        have h := volume_shell_toReal_le (N := n + 1) hn1 (1 - 3 / (4 * A)) ht0 ht1
        have h1 : (1 : ℝ) - (1 - 3 / (4 * A)) = 3 / (4 * A) := by ring
        rw [h1] at h
        rw [hΛ, hVl]
        simpa only [Nat.cast_add, Nat.cast_one] using h
      have hVlpos : 0 < Vl.toReal := by
        have hne : (0 : Fin (n + 1) → ℝ) ∈ interior {y : Fin (n + 1) → ℝ | rNorm y ≤ 1} :=
          interior_maximal (fun y hy => le_of_lt hy)
            (isOpen_lt continuous_rNorm' continuous_const)
            (by show rNorm (0 : Fin (n + 1) → ℝ) < 1
                rw [show rNorm (0 : Fin (n + 1) → ℝ) = 0 by simp [rNorm]]
                norm_num)
        have hpos : 0 < Vl := by
          rw [hVl]
          exact MeasureTheory.Measure.measure_pos_of_nonempty_interior (μ := volume)
            (s := {y : Fin (n + 1) → ℝ | rNorm y ≤ 1}) ⟨0, hne⟩
        exact ENNReal.toReal_pos hpos.ne' hVlfin
      have h5 : (F.ncard : ℝ) ≤ (M : ℝ) * (((n : ℝ) + 1) * (3 / (4 * A))) / r ^ (n + 1) := by
        have h3 : (F.ncard : ℝ) * r ^ (n + 1) * Vl.toReal ≤
            ((M : ℝ) * (((n : ℝ) + 1) * (3 / (4 * A)))) * Vl.toReal := by
          calc (F.ncard : ℝ) * r ^ (n + 1) * Vl.toReal
              = (F.ncard : ℝ) * (r ^ (n + 1) * Vl.toReal) := by ring
            _ ≤ (M : ℝ) * (((n : ℝ) + 1) * (3 / (4 * A)) * Vl.toReal) :=
                le_trans hchainR (mul_le_mul_of_nonneg_left hΛle (by positivity))
            _ = ((M : ℝ) * (((n : ℝ) + 1) * (3 / (4 * A)))) * Vl.toReal := by ring
        have h4 := le_of_mul_le_mul_right h3 hVlpos
        rw [le_div_iff₀ (by positivity)]
        exact h4
      have hA0 : A ≠ 0 := by positivity
      have hCe : ((n : ℝ) + 1) * (3 / (4 * A)) / r ^ (n + 1) = Cst * A ^ n := by
        rw [hr, hCst, one_div_pow]
        field_simp
        ring
      have h5' : (F.ncard : ℝ) ≤ (M : ℝ) * (Cst * A ^ n) := by
        have h5e : (M : ℝ) * (((n : ℝ) + 1) * (3 / (4 * A))) / r ^ (n + 1)
            = (M : ℝ) * (Cst * A ^ n) := by
          rw [mul_div_assoc, hCe]
        rw [h5e] at h5
        exact h5
      have hMM : (M : ℝ) ≤ K0 * A ^ (NN d n - (n + 1)) + 1 := by
        rw [hM]
        exact le_of_lt (Nat.ceil_lt_add_one (by positivity))
      have hkey : (F.ncard : ℝ) ≤ (K0 * A ^ (NN d n - (n + 1)) + 1) * (Cst * A ^ n) := by
        refine le_trans h5' ?_
        exact mul_le_mul_of_nonneg_right hMM (by positivity)
      have hfin : (K0 * A ^ (NN d n - (n + 1)) + 1) * (Cst * A ^ n) ≤
          (K0 + 1) * Cst * A ^ (NN d n - 1) := by
        have hpowid : A ^ (NN d n - (n + 1)) * A ^ n = A ^ (NN d n - 1) := by
          rw [← pow_add, show NN d n - (n + 1) + n = NN d n - 1 by omega]
        have h3 : Cst * A ^ n ≤ Cst * A ^ (NN d n - 1) :=
          mul_le_mul_of_nonneg_left (pow_le_pow_right₀ hA1 (by omega)) (le_of_lt hCstpos)
        calc (K0 * A ^ (NN d n - (n + 1)) + 1) * (Cst * A ^ n)
            = K0 * Cst * (A ^ (NN d n - (n + 1)) * A ^ n) + Cst * A ^ n := by ring
          _ = K0 * Cst * A ^ (NN d n - 1) + Cst * A ^ n := by rw [hpowid]
          _ ≤ K0 * Cst * A ^ (NN d n - 1) + Cst * A ^ (NN d n - 1) := by linarith [h3]
          _ = (K0 + 1) * Cst * A ^ (NN d n - 1) := by ring
      exact le_trans hkey hfin
    exact hgoal
  refine ⟨(K0 + 1) * Cst * 2 ^ (NN d n - 1), ?_, ?_⟩
  · have h1 : 0 < (K0 + 1) := by linarith
    have h2 : 0 < (2 : ℝ) ^ (NN d n - 1) := by positivity
    positivity
  · intro A hA1
    by_cases h2 : 2 ≤ A
    · have hm := hmain A h2
      have h3 : (1 : ℝ) ≤ 2 ^ (NN d n - 1) := one_le_pow₀ (by norm_num)
      have h4 : 0 ≤ (K0 + 1) * Cst * A ^ (NN d n - 1) := by positivity
      calc ((Uset d n A).ncard : ℝ) ≤ (K0 + 1) * Cst * A ^ (NN d n - 1) := hm
        _ ≤ (K0 + 1) * Cst * 2 ^ (NN d n - 1) * A ^ (NN d n - 1) := by nlinarith [h3, h4]
        _ = ((K0 + 1) * Cst * 2 ^ (NN d n - 1)) * A ^ (NN d n - 1) := by ring
    · have hmono : (Uset d n A).ncard ≤ (Uset d n 2).ncard :=
        Set.ncard_le_ncard (fun a ha => ⟨ha.1, le_trans ha.2.1 (by linarith), ha.2.2.1, ha.2.2.2⟩)
          ((finite_eNorm_le d n 2).subset (fun a ha => ha.2.1))
      have hm := hmain 2 (le_refl 2)
      have hAe : (1 : ℝ) ≤ A ^ (NN d n - 1) := one_le_pow₀ hA1
      have h3 : 0 ≤ (K0 + 1) * Cst * 2 ^ (NN d n - 1) := by positivity
      calc ((Uset d n A).ncard : ℝ) ≤ ((Uset d n 2).ncard : ℝ) := by exact_mod_cast hmono
        _ ≤ (K0 + 1) * Cst * 2 ^ (NN d n - 1) := hm
        _ ≤ (K0 + 1) * Cst * 2 ^ (NN d n - 1) * A ^ (NN d n - 1) := by nlinarith [hAe, h3]
        _ = ((K0 + 1) * Cst * 2 ^ (NN d n - 1)) * A ^ (NN d n - 1) := by ring

end Work.HP
