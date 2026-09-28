import Mathlib
import Submission.Work.HP.Defs
import Submission.Work.HP.Psi
import Submission.Work.HP.HP2.veronese_sup
import Submission.Work.HP.eNorm_veronese_bounds
import Submission.Work.HP.rNorm_smul
import Submission.Work.HP.tau_basic
import Submission.Work.HP.evaldefs
import Submission.Work.HP.HP2.Phi_continuous
import Submission.Work.HP.HP2.slice_contradiction

set_option autoImplicit false
set_option maxHeartbeats 1000000
noncomputable section
open Work.HP Finset

namespace Work.HP.HP2

lemma continuous_rNorm (n : ℕ) : Continuous (fun x : Fin (n + 1) → ℝ => rNorm x) := by
  simp only [rNorm]; fun_prop

lemma continuous_rNorm' (ι : Type*) [Fintype ι] : Continuous (fun x : ι → ℝ => rNorm x) := by
  simp only [rNorm]; fun_prop

lemma isCompact_rNorm_ball (n : ℕ) : IsCompact {x : Fin (n + 1) → ℝ | rNorm x ≤ 1} := by
  refine IsCompact.of_isClosed_subset (isCompact_closedBall (0 : Fin (n + 1) → ℝ) 1) ?_ ?_
  · exact isClosed_le (continuous_rNorm n) continuous_const
  · intro x hx
    simp only [Set.mem_ofPred_eq] at hx
    rw [Metric.mem_closedBall, dist_eq_norm, sub_zero]
    exact le_trans (norm_le_rNorm x) hx

lemma rNorm_ball_nonempty (n : ℕ) :
    ({x : Fin (n + 1) → ℝ | rNorm x ≤ 1} : Set (Fin (n + 1) → ℝ)).Nonempty :=
  ⟨0, by simp only [Set.mem_ofPred_eq, rNorm]; simp⟩

lemma dotR_smul_right {ι : Type*} [Fintype ι] (v w : ι → ℝ) (c : ℝ) :
    dotR v (c • w) = c * dotR v w := by
  simp only [dotR, Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
  exact Finset.sum_congr rfl fun i _ => by ring

lemma eNorm_pos {d n : ℕ} {a : Mon d n → ℤ} (ha : a ≠ 0) : 0 < eNorm a := by
  simp only [eNorm]
  apply Real.sqrt_pos.mpr
  obtain ⟨m, hm⟩ : ∃ m, a m ≠ 0 := by
    by_contra h; push Not at h; exact ha (funext h)
  have hm2 : (0:ℝ) < (((a m : ℤ) : ℝ)) ^ 2 := by
    have : ((a m : ℤ) : ℝ) ≠ 0 := by exact_mod_cast hm
    positivity
  exact lt_of_lt_of_le hm2
    (Finset.single_le_sum (fun i _ => sq_nonneg (((a i : ℤ) : ℝ))) (Finset.mem_univ m))

lemma rNorm_unit_vec (d n : ℕ) :
    ∃ b : Mon d n → ℝ, rNorm b = 1 := by
  refine ⟨fun m => if m = mon0 d n then (1:ℝ) else 0, ?_⟩
  rw [rNorm]
  have hsum : (∑ m : Mon d n,
      ((fun m : Mon d n => if m = mon0 d n then (1:ℝ) else 0) m) ^ 2) = 1 := by
    rw [Finset.sum_eq_single (mon0 d n)]
    · simp
    · intro m _ hm
      simp only [if_neg hm]; simp
    · intro h; exact absurd (Finset.mem_univ (mon0 d n)) h
  rw [hsum, Real.sqrt_one]

lemma Psi_eq_norm_sq (d n : ℕ) (a : Mon d n → ℤ) (ha : a ≠ 0) (α : ℝ)
    (x : Fin (n + 1) → ℝ) :
    Psi d n a α x = (eNorm a) ^ 2 *
      (4 * α ^ 2 * (dotR (veronese d n x) (((eNorm a)⁻¹) • toR a)) ^ 2 -
        (rNorm (veronese d n x)) ^ 2) := by
  have hA : 0 < eNorm a := eNorm_pos ha
  have hd1 : dotR (veronese d n x) (((eNorm a)⁻¹) • toR a)
      = (eNorm a)⁻¹ * formEvalR d n (toR a) x := by
    rw [dotR_smul_right, dotR_veronese]
  rw [Psi, hd1]
  field_simp

lemma sup_pos (d n : ℕ) (hd : 1 ≤ d) (hn : 1 ≤ n)
    (b : Mon d n → ℝ) (α : ℝ) (hb : rNorm b = 1) (hα : α ≠ 0) :
    0 < sSup ((fun x : Fin (n + 1) → ℝ =>
      |4 * α ^ 2 * (dotR (veronese d n x) b) ^ 2 - (rNorm (veronese d n x)) ^ 2|) ''
        {x : Fin (n + 1) → ℝ | rNorm x ≤ 1}) := by
  set K : Set (Fin (n + 1) → ℝ) := {x | rNorm x ≤ 1} with hKdef
  set f : (Fin (n + 1) → ℝ) → ℝ := fun x =>
    |4 * α ^ 2 * (dotR (veronese d n x) b) ^ 2 - (rNorm (veronese d n x)) ^ 2| with hfdef
  have hK : IsCompact K := isCompact_rNorm_ball n
  have hKne : K.Nonempty := rNorm_ball_nonempty n
  have hfcont : Continuous f := by
    rw [hfdef]; simp only [rNorm, dotR, veronese]; fun_prop
  have hbd : BddAbove (f '' K) := hK.bddAbove_image hfcont.continuousOn
  have hnonneg : ∀ y ∈ f '' K, 0 ≤ y := by
    rintro y ⟨x, hx, rfl⟩; exact abs_nonneg _
  obtain ⟨y₀, hy₀⟩ := hKne.image f
  have h0le : 0 ≤ sSup (f '' K) :=
    le_trans (hnonneg y₀ hy₀) (le_csSup hbd hy₀)
  by_contra hcon
  push Not at hcon
  have hzero : ∀ x ∈ K, f x = 0 := by
    intro x hx
    have h1 : f x ≤ sSup (f '' K) := le_csSup hbd (Set.mem_image_of_mem f hx)
    have h2 : 0 ≤ f x := abs_nonneg _
    linarith
  exact slice_contradiction d n hd hn b α hb hα
    (fun x hx => by
      have h := hzero x hx
      rw [hfdef] at h
      exact sub_eq_zero.mp (abs_eq_zero.mp h))

theorem sup_lower_on_compact (d n : ℕ) (hd : 1 ≤ d) (hn : 1 ≤ n) {A₀ : ℝ} (hA₀ : 1 ≤ A₀) :
    ∃ c₂ : ℝ, 0 < c₂ ∧ ∀ (b : Mon d n → ℝ) (α : ℝ), rNorm b = 1 → 1 ≤ α → α ≤ A₀ →
      c₂ ≤ sSup ((fun x : Fin (n + 1) → ℝ =>
        |4 * α ^ 2 * (dotR (veronese d n x) b) ^ 2 -
          (rNorm (veronese d n x)) ^ 2|) '' {x : Fin (n + 1) → ℝ | rNorm x ≤ 1}) := by
  set g : (Mon d n → ℝ) × ℝ → ℝ := fun p =>
    sSup ((fun x : Fin (n + 1) → ℝ =>
      |4 * p.2 ^ 2 * (dotR (veronese d n x) p.1) ^ 2 -
        (rNorm (veronese d n x)) ^ 2|) '' {x : Fin (n + 1) → ℝ | rNorm x ≤ 1}) with hgdef
  have hgcont : Continuous g := by rw [hgdef]; exact Phi_continuous d n
  set P : Set ((Mon d n → ℝ) × ℝ) := {p | rNorm p.1 = 1 ∧ 1 ≤ p.2 ∧ p.2 ≤ A₀} with hPdef
  have hPcompact : IsCompact P := by
    refine IsCompact.of_isClosed_subset
      ((isCompact_closedBall (0 : Mon d n → ℝ) 1).prod
        (isCompact_Icc : IsCompact (Set.Icc (1:ℝ) A₀))) ?_ ?_
    · rw [hPdef]
      exact (isClosed_eq (continuous_rNorm' (Mon d n) |>.comp continuous_fst)
          continuous_const).inter
        ((isClosed_le continuous_const continuous_snd).inter
          (isClosed_le continuous_snd continuous_const))
    · rintro p ⟨hp1, hp2, hp3⟩
      refine ⟨?_, hp2, hp3⟩
      rw [Metric.mem_closedBall, dist_eq_norm, sub_zero]
      exact le_trans (norm_le_rNorm p.1) (le_of_eq hp1)
  obtain ⟨b₀, hb₀⟩ := rNorm_unit_vec d n
  have hPne : P.Nonempty := ⟨(b₀, 1), hb₀, le_refl 1, hA₀⟩
  have hpos : ∀ p ∈ P, 0 < g p := by
    intro p hp
    obtain ⟨hp1, hp2, hp3⟩ := hp
    have hα : p.2 ≠ 0 := by linarith
    rw [hgdef]
    exact sup_pos d n hd hn p.1 p.2 hp1 hα
  obtain ⟨p₀, hp₀P, hp₀min⟩ := hPcompact.exists_isMinOn hPne hgcont.continuousOn
  refine ⟨g p₀, hpos p₀ hp₀P, ?_⟩
  intro b α hb hα hα2
  exact hp₀min (show (b, α) ∈ P from ⟨hb, hα, hα2⟩)

private lemma Psi_M_zero (d : ℕ) (hd : 1 ≤ d) :
    ∃ c : ℝ, 0 < c ∧ ∀ (a : Mon d 0 → ℤ) (α : ℝ), a ≠ 0 → 1 ≤ α →
      ∃ M : ℝ, 0 < M ∧
        (∀ x : Fin (0 + 1) → ℝ, rNorm x ≤ 1 → |Psi d 0 a α x| ≤ M) ∧
        (∃ x : Fin (0 + 1) → ℝ, rNorm x ≤ 1 ∧ M ≤ |Psi d 0 a α x|) ∧
        c * α ^ 2 * (eNorm a) ^ 2 ≤ M := by
  haveI hsub1 : Subsingleton (Fin (0 + 1)) :=
    ⟨fun a b => Fin.ext (by have ha := a.isLt; have hb := b.isLt; omega)⟩
  let m0 : Mon d 0 := ⟨fun _ => ⟨d, Nat.lt_succ_self d⟩, by
    simp [Fin.sum_univ_one]⟩
  haveI : Subsingleton (Mon d 0) := by
    refine ⟨fun m1 m2 => ?_⟩
    have h : m1.1 = m2.1 := by
      funext i
      have hi : i = 0 := Fin.ext (by have ha := i.isLt; omega)
      rw [hi]
      apply Fin.ext
      have h1 : (m1.1 0 : ℕ) = d := by have := m1.2; simpa [Fin.sum_univ_one] using this
      have h2 : (m2.1 0 : ℕ) = d := by have := m2.2; simpa [Fin.sum_univ_one] using this
      rw [h1, h2]
    exact Subtype.ext h
  have hver : ∀ (x : Fin (0 + 1) → ℝ) (m : Mon d 0), veronese d 0 x m = x 0 ^ d := by
    intro x m
    rw [veronese]
    have h0 : (m.1 0 : ℕ) = d := by have := m.2; simpa [Fin.sum_univ_one] using this
    rw [Finset.prod_eq_single (0 : Fin (0 + 1))]
    · rw [h0]
    · intro i _ hi
      exact absurd (Fin.ext (by have ha := i.isLt; omega)) hi
    · intro h; exact absurd (Finset.mem_univ (0 : Fin (0 + 1))) h
  refine ⟨3, by norm_num, fun a α ha hα => ?_⟩
  have hconst : ∀ m : Mon d 0, a m = a m0 := fun m => congrArg a (Subsingleton.elim m m0)
  have hform : ∀ x : Fin (0 + 1) → ℝ, formEvalR d 0 (toR a) x = (a m0 : ℝ) * x 0 ^ d := by
    intro x
    simp only [formEvalR]
    rw [Finset.sum_congr rfl (fun m _ => by rw [hver x m])]
    rw [Fintype.sum_subsingleton (fun m : Mon d 0 => toR a m * x 0 ^ d) m0]
    simp only [toR]
  have hrnorm_ver : ∀ x : Fin (0 + 1) → ℝ, rNorm (veronese d 0 x) = |x 0| ^ d := by
    intro x
    simp only [rNorm]
    have hsum : (∑ m : Mon d 0, (veronese d 0 x m) ^ 2) = (x 0 ^ d) ^ 2 := by
      rw [Finset.sum_congr rfl (fun m _ => by rw [hver x m])]
      rw [Fintype.sum_subsingleton (fun m : Mon d 0 => (x 0 ^ d) ^ 2) m0]
    rw [hsum, Real.sqrt_sq_eq_abs, abs_pow]
  have henorm : eNorm a = |((a m0 : ℤ) : ℝ)| := by
    simp only [eNorm]
    have hsum : (∑ m : Mon d 0, (((a m : ℤ) : ℝ)) ^ 2) = (((a m0 : ℤ) : ℝ)) ^ 2 := by
      rw [Fintype.sum_subsingleton (fun m : Mon d 0 => (((a m : ℤ) : ℝ)) ^ 2) m0]
    rw [hsum, Real.sqrt_sq_eq_abs]
  have hPsi : ∀ x : Fin (0 + 1) → ℝ,
      Psi d 0 a α x = (((a m0 : ℤ) : ℝ)) ^ 2 * (x 0 ^ d) ^ 2 * (4 * α ^ 2 - 1) := by
    intro x
    rw [Psi, hform x, henorm, hrnorm_ver x]
    have hx2 : (|x 0| ^ d) ^ 2 = (x 0 ^ d) ^ 2 := by rw [← abs_pow, sq_abs]
    rw [hx2, sq_abs]
    ring
  have ham : (((a m0 : ℤ) : ℝ)) ≠ 0 := by
    have : a m0 ≠ 0 := by
      intro h; exact ha (funext fun m => by rw [hconst m, h]; rfl)
    exact_mod_cast this
  have hα1 : (1:ℝ) ≤ α := hα
  have h4 : 0 < 4 * α ^ 2 - 1 := by nlinarith [hα1]
  set M : ℝ := (((a m0 : ℤ) : ℝ)) ^ 2 * (4 * α ^ 2 - 1) with hMdef
  have hMpos : 0 < M := by
    rw [hMdef]; exact mul_pos (sq_pos_of_ne_zero ham) h4
  refine ⟨M, hMpos, ?_, ?_, ?_⟩
  · intro x hx
    have hx1 : |x 0| ≤ 1 := le_trans (abs_apply_le_rNorm x 0) hx
    have hxd : (x 0 ^ d) ^ 2 ≤ 1 := by
      have hxa : |x 0 ^ d| ≤ 1 := by
        rw [abs_pow]; exact pow_le_one₀ (abs_nonneg _) hx1
      calc (x 0 ^ d) ^ 2 = |x 0 ^ d| ^ 2 := (sq_abs _).symm
        _ ≤ 1 ^ 2 := pow_le_pow_left₀ (abs_nonneg _) hxa 2
        _ = 1 := one_pow 2
    rw [hPsi x, hMdef]
    rw [abs_of_nonneg (mul_nonneg (mul_nonneg (sq_nonneg _) (sq_nonneg _)) h4.le)]
    calc ((((a m0 : ℤ) : ℝ)) ^ 2 * (x 0 ^ d) ^ 2) * (4 * α ^ 2 - 1)
        ≤ ((((a m0 : ℤ) : ℝ)) ^ 2 * 1) * (4 * α ^ 2 - 1) :=
          mul_le_mul_of_nonneg_right
            (mul_le_mul_of_nonneg_left hxd (sq_nonneg _)) h4.le
      _ = (((a m0 : ℤ) : ℝ)) ^ 2 * (4 * α ^ 2 - 1) := by ring
  · have hxnorm : rNorm (fun _ => (1:ℝ) : Fin (0 + 1) → ℝ) = 1 := by
      rw [rNorm]
      have hsum : (∑ _i : Fin (0 + 1), ((1:ℝ)) ^ 2) = 1 := by
        rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
        norm_num
      rw [hsum, Real.sqrt_one]
    refine ⟨fun _ => (1:ℝ), ?_, ?_⟩
    · exact le_of_eq hxnorm
    · rw [hMdef, hPsi (fun _ => (1:ℝ))]
      have hone : (((1:ℝ)) ^ d) ^ 2 = 1 := by rw [one_pow, one_pow]
      rw [hone, mul_one]
      exact le_abs_self _
  · rw [hMdef, henorm, sq_abs]
    have : 3 * α ^ 2 ≤ 4 * α ^ 2 - 1 := by nlinarith [hα1]
    calc 3 * α ^ 2 * (((a m0 : ℤ) : ℝ)) ^ 2
        = (((a m0 : ℤ) : ℝ)) ^ 2 * (3 * α ^ 2) := by ring
      _ ≤ (((a m0 : ℤ) : ℝ)) ^ 2 * (4 * α ^ 2 - 1) :=
          mul_le_mul_of_nonneg_left this (by positivity)

theorem Psi_M (d n : ℕ) (hd : 1 ≤ d) :
    ∃ c : ℝ, 0 < c ∧ ∀ (a : Work.HP.Mon d n → ℤ) (α : ℝ), a ≠ 0 → 1 ≤ α →
      ∃ M : ℝ, 0 < M ∧
        (∀ x : Fin (n + 1) → ℝ, Work.HP.rNorm x ≤ 1 → |Work.HP.Psi d n a α x| ≤ M) ∧
        (∃ x : Fin (n + 1) → ℝ, Work.HP.rNorm x ≤ 1 ∧ M ≤ |Work.HP.Psi d n a α x|) ∧
        c * α ^ 2 * (Work.HP.eNorm a) ^ 2 ≤ M := by
  rcases Nat.eq_zero_or_pos n with hn0 | hn
  · subst hn0
    exact Psi_M_zero d hd
  obtain ⟨cv, hcvpos, hver⟩ := veronese_sup d n hd
  have hNpos : (0:ℝ) < (NN d n : ℝ) := by
    have h := one_le_NN d n
    exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one h)
  set A₀ : ℝ := max 1 (Real.sqrt ((NN d n : ℝ) / (3 * cv ^ 2))) with hA₀def
  have hA₀ge1 : 1 ≤ A₀ := le_max_left _ _
  have hA₀sq : (NN d n : ℝ) / (3 * cv ^ 2) ≤ A₀ ^ 2 := by
    have h1 : Real.sqrt ((NN d n : ℝ) / (3 * cv ^ 2)) ≤ A₀ := le_max_right _ _
    calc (NN d n : ℝ) / (3 * cv ^ 2)
        = (Real.sqrt ((NN d n : ℝ) / (3 * cv ^ 2))) ^ 2 :=
          (Real.sq_sqrt (by positivity)).symm
      _ ≤ A₀ ^ 2 := pow_le_pow_left₀ (Real.sqrt_nonneg _) h1 2
  obtain ⟨c₂, hc₂pos, hc₂⟩ := sup_lower_on_compact d n hd hn (A₀ := A₀) hA₀ge1
  refine ⟨min (cv ^ 2) (c₂ / A₀ ^ 2), ?_, ?_⟩
  · exact lt_min (by positivity) (div_pos hc₂pos (pow_pos (lt_of_lt_of_le zero_lt_one hA₀ge1) 2))
  · intro a α ha hα
    have hApos : 0 < eNorm a := eNorm_pos ha
    set g : (Fin (n + 1) → ℝ) → ℝ := fun x => |Psi d n a α x| with hgdef
    have hK : IsCompact {x : Fin (n + 1) → ℝ | rNorm x ≤ 1} := isCompact_rNorm_ball n
    have hKne : ({x : Fin (n + 1) → ℝ | rNorm x ≤ 1}).Nonempty := rNorm_ball_nonempty n
    have hgcont : Continuous g := by
      rw [hgdef]; simp only [Psi, rNorm, formEvalR, veronese]; fun_prop
    have hbd : BddAbove (g '' {x : Fin (n + 1) → ℝ | rNorm x ≤ 1}) :=
      hK.bddAbove_image hgcont.continuousOn
    set M : ℝ := sSup (g '' {x : Fin (n + 1) → ℝ | rNorm x ≤ 1}) with hMdef
    have hbound : min (cv ^ 2) (c₂ / A₀ ^ 2) * α ^ 2 * (eNorm a) ^ 2 ≤ M := by
      rcases le_total α A₀ with hle | hge
      · set â : Mon d n → ℝ := ((eNorm a)⁻¹) • toR a with hâdef
        have hâ1 : rNorm â = 1 := by
          rw [hâdef, rNorm_smul', abs_of_pos (inv_pos.mpr hApos), rNorm_toR,
            inv_mul_cancel₀ (ne_of_gt hApos)]
        set f₂ : (Fin (n + 1) → ℝ) → ℝ := fun x =>
          |4 * α ^ 2 * (dotR (veronese d n x) â) ^ 2 -
            (rNorm (veronese d n x)) ^ 2| with hf₂def
        have hf₂cont : Continuous f₂ := by
          rw [hf₂def]; simp only [rNorm, dotR, veronese]; fun_prop
        obtain ⟨x₁, hx₁K, hx₁eq⟩ := hK.exists_sSup_image_eq hKne hf₂cont.continuousOn
        have hval : c₂ ≤ f₂ x₁ := by
          rw [← hx₁eq]
          exact hc₂ â α hâ1 hα hle
        have hrel : |Psi d n a α x₁| = (eNorm a) ^ 2 * f₂ x₁ := by
          rw [hf₂def, hâdef]
          rw [Psi_eq_norm_sq d n a ha α x₁, abs_mul, abs_of_nonneg (sq_nonneg (eNorm a))]
        have h1 : (eNorm a) ^ 2 * c₂ ≤ |Psi d n a α x₁| := by
          rw [hrel]
          exact mul_le_mul_of_nonneg_left hval (sq_nonneg (eNorm a))
        have h2 : min (cv ^ 2) (c₂ / A₀ ^ 2) * α ^ 2 * (eNorm a) ^ 2 ≤
            (eNorm a) ^ 2 * c₂ := by
          have hc_le : min (cv ^ 2) (c₂ / A₀ ^ 2) ≤ c₂ / A₀ ^ 2 := min_le_right _ _
          have hα2 : α ^ 2 ≤ A₀ ^ 2 :=
            pow_le_pow_left₀ (le_trans zero_le_one hα) hle 2
          calc min (cv ^ 2) (c₂ / A₀ ^ 2) * α ^ 2 * (eNorm a) ^ 2
              ≤ (c₂ / A₀ ^ 2) * α ^ 2 * (eNorm a) ^ 2 :=
                mul_le_mul_of_nonneg_right
                  (mul_le_mul_of_nonneg_right hc_le (sq_nonneg α)) (sq_nonneg (eNorm a))
            _ ≤ (c₂ / A₀ ^ 2) * A₀ ^ 2 * (eNorm a) ^ 2 :=
                mul_le_mul_of_nonneg_right
                  (mul_le_mul_of_nonneg_left hα2 (div_nonneg hc₂pos.le
                    (pow_pos (lt_of_lt_of_le zero_lt_one hA₀ge1) 2).le))
                  (sq_nonneg (eNorm a))
            _ = (eNorm a) ^ 2 * c₂ := by field_simp
        exact le_trans h2 (le_trans h1
          (le_csSup hbd (Set.mem_image_of_mem g hx₁K)))
      · obtain ⟨x₀, hx₀K, hx₀val⟩ := hver a
        have hQ2 : cv ^ 2 * (eNorm a) ^ 2 ≤ (formEvalR d n (toR a) x₀) ^ 2 := by
          have h1 : cv * eNorm a ≤ |formEvalR d n (toR a) x₀| := hx₀val
          have h2 : (0:ℝ) ≤ cv * eNorm a := mul_nonneg hcvpos.le hApos.le
          have h3 : (cv * eNorm a) ^ 2 ≤ (formEvalR d n (toR a) x₀) ^ 2 := by
            rw [← sq_abs (formEvalR d n (toR a) x₀)]
            exact pow_le_pow_left₀ h2 h1 2
          simpa only [mul_pow] using h3
        have hS2 : (rNorm (veronese d n x₀)) ^ 2 ≤ (NN d n : ℝ) := by
          have h := veronese_rNorm_upper d n x₀
          have hx0d : rNorm x₀ ^ d ≤ 1 := by
            calc rNorm x₀ ^ d ≤ 1 ^ d := pow_le_pow_left₀ (rNorm_nonneg _) hx₀K d
              _ = 1 := one_pow d
          have hSnn : 0 ≤ rNorm (veronese d n x₀) := rNorm_nonneg _
          have hnd : 0 ≤ rNorm x₀ ^ d := pow_nonneg (rNorm_nonneg _) d
          calc (rNorm (veronese d n x₀)) ^ 2
              ≤ (Real.sqrt (NN d n) * rNorm x₀ ^ d) ^ 2 := pow_le_pow_left₀ hSnn h 2
            _ = (NN d n : ℝ) * (rNorm x₀ ^ d) ^ 2 := by
                rw [mul_pow, Real.sq_sqrt (le_of_lt hNpos)]
            _ ≤ (NN d n : ℝ) * 1 :=
                mul_le_mul_of_nonneg_left (by nlinarith [hx0d, hnd]) (le_of_lt hNpos)
            _ = (NN d n : ℝ) := mul_one _
        have h3 : (NN d n : ℝ) ≤ 3 * α ^ 2 * cv ^ 2 := by
          have hα2 : A₀ ^ 2 ≤ α ^ 2 :=
            pow_le_pow_left₀ (le_trans zero_le_one hA₀ge1) hge 2
          have h4 : (NN d n : ℝ) / (3 * cv ^ 2) ≤ α ^ 2 := le_trans hA₀sq hα2
          rw [div_le_iff₀ (by positivity)] at h4
          linarith
        have hPsi : cv ^ 2 * α ^ 2 * (eNorm a) ^ 2 ≤ Psi d n a α x₀ := by
          rw [Psi]
          nlinarith [hQ2, hS2, h3, sq_nonneg α, sq_nonneg cv, hcvpos, hApos, sq_nonneg (eNorm a)]
        calc min (cv ^ 2) (c₂ / A₀ ^ 2) * α ^ 2 * (eNorm a) ^ 2
            ≤ cv ^ 2 * α ^ 2 * (eNorm a) ^ 2 :=
              mul_le_mul_of_nonneg_right
                (mul_le_mul_of_nonneg_right (min_le_left _ _) (sq_nonneg α))
                (sq_nonneg (eNorm a))
          _ ≤ Psi d n a α x₀ := hPsi
          _ ≤ |Psi d n a α x₀| := le_abs_self _
          _ ≤ M := le_csSup hbd (Set.mem_image_of_mem g hx₀K)
    have hMpos : 0 < M :=
      lt_of_lt_of_le
        (mul_pos
          (mul_pos
            (lt_min (by positivity)
              (div_pos hc₂pos (pow_pos (lt_of_lt_of_le zero_lt_one hA₀ge1) 2)))
            (pow_pos (lt_of_lt_of_le zero_lt_one hα) 2))
          (pow_pos hApos 2))
        hbound
    refine ⟨M, hMpos, ?_, ?_, ?_⟩
    · intro x hx
      exact le_csSup hbd (Set.mem_image_of_mem g hx)
    · obtain ⟨x₀, hx₀K, hx₀eq⟩ := hK.exists_sSup_image_eq hKne hgcont.continuousOn
      exact ⟨x₀, hx₀K, by rw [hMdef]; exact le_of_eq hx₀eq⟩
    · exact hbound

end Work.HP.HP2
