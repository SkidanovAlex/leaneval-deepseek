import Mathlib
import Submission.Work.FIArea4.P13Defs
import Submission.Work.FIArea4.pair_sum_le_Evar
import Submission.Work.FIArea4.P13_same_ray

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

/-!
# The trivial estimate of the `p ∣ r` part of the §13 variance (FI (13.2))
-/

namespace Work.FIArea4

open Finset
open scoped BigOperators

attribute [local instance] Classical.propDecidable

noncomputable section

/-! ## Definitions -/

/-- The pair box `[1,2R] × [1,2S]`. -/
def P13box (R S : ℕ) : Finset (ℕ × ℕ) := Finset.Icc 1 (2 * R) ×ˢ Finset.Icc 1 (2 * S)

/-- The pairs of the `a`-th residue class whose first coordinate is divisible by `p`. -/
def P13Sset (R S d p a : ℕ) : Finset (ℕ × ℕ) :=
  (EvarCls R S d a).filter (fun q => p ∣ q.1)

/-- The absolute-value majorant of the `p ∣ r`-restricted pair sum over a congruence modulo `d`. -/
def P13WI (R S d p : ℕ) (α : ℕ → ℕ → ℂ) : ℝ :=
  ∑ r1 ∈ Finset.Icc 1 (2 * R), ∑ s1 ∈ Finset.Icc 1 (2 * S),
  ∑ r2 ∈ Finset.Icc 1 (2 * R), ∑ s2 ∈ Finset.Icc 1 (2 * S),
    (if (p ∣ r1 ∧ p ∣ r2 ∧ ((r1 * s2 : ℕ) : ZMod d) = ((r2 * s1 : ℕ) : ZMod d))
     then ‖α r1 s1‖ * ‖α r2 s2‖ else 0)

/-- The number of moduli `d ∈ (D,2D]` for which the two pairs `q1`, `q2` lie in the same class. -/
def P13cl (D : ℕ) (q1 q2 : ℕ × ℕ) : ℝ :=
  (((Finset.Ioc D (2 * D)).filter
      (fun d => ((q1.1 * q2.2 : ℕ) : ZMod d) = ((q2.1 * q1.2 : ℕ) : ZMod d))).card : ℝ)

/-! ## Elementary lemmas -/

lemma mem_P13box {R S : ℕ} {q : ℕ × ℕ} :
    q ∈ P13box R S ↔ q.1 ∈ Finset.Icc 1 (2 * R) ∧ q.2 ∈ Finset.Icc 1 (2 * S) := by
  simp [P13box]

/-- The Jacobi weight does not increase the norm. -/
lemma norm_mul_jw_le (d r : ℕ) (z : ℂ) : ‖z * jw d r‖ ≤ ‖z‖ := by
  rw [jw]
  have h := normSq_mul_jacobiSym_le z (r : ℤ) (Work.FIPlan.oddPart d)
  rw [Complex.normSq_eq_norm_sq, Complex.normSq_eq_norm_sq] at h
  calc ‖z * ((jacobiSym (r : ℤ) (Work.FIPlan.oddPart d) : ℤ) : ℂ)‖
      = Real.sqrt (‖z * ((jacobiSym (r : ℤ) (Work.FIPlan.oddPart d) : ℤ) : ℂ)‖ ^ 2) :=
        (Real.sqrt_sq (norm_nonneg _)).symm
    _ ≤ Real.sqrt (‖z‖ ^ 2) := Real.sqrt_le_sqrt h
    _ = ‖z‖ := Real.sqrt_sq (norm_nonneg _)

/-- The norm of the restricted coefficient is bounded by the indicator of `p ∣ r` times the norm
of `α`. -/
lemma P13_norm_ite_le (d p : ℕ) (α : ℕ → ℕ → ℂ) (r s : ℕ) :
    ‖(if (Nat.Coprime r d ∧ p ∣ r) then α r s else 0)‖
      ≤ (if p ∣ r then ‖α r s‖ else 0) := by
  by_cases hp : p ∣ r
  · rw [if_pos hp]
    by_cases hc : Nat.Coprime r d
    · rw [if_pos ⟨hc, hp⟩]
    · rw [if_neg (fun h => hc h.1)]
      simp
  · rw [if_neg hp, if_neg (fun h => hp h.2)]
    simp

/-- Triangle inequality for a fourfold nested sum. -/
lemma norm_sum4_le {M : Type*} [SeminormedAddCommGroup M] (a b c e : Finset ℕ)
    (f : ℕ → ℕ → ℕ → ℕ → M) :
    ‖∑ x ∈ a, ∑ y ∈ b, ∑ z ∈ c, ∑ w ∈ e, f x y z w‖
      ≤ ∑ x ∈ a, ∑ y ∈ b, ∑ z ∈ c, ∑ w ∈ e, ‖f x y z w‖ := by
  refine le_trans (norm_sum_le _ _) (Finset.sum_le_sum (fun x _ => ?_))
  refine le_trans (norm_sum_le _ _) (Finset.sum_le_sum (fun y _ => ?_))
  refine le_trans (norm_sum_le _ _) (Finset.sum_le_sum (fun z _ => ?_))
  exact norm_sum_le _ _

/-- `P13cl D q q = D`: for equal pairs the congruence is automatic. -/
lemma P13cl_self (D : ℕ) (q : ℕ × ℕ) : P13cl D q q = D := by
  have hfilter : (Finset.Ioc D (2 * D)).filter
      (fun d => ((q.1 * q.2 : ℕ) : ZMod d) = ((q.1 * q.2 : ℕ) : ZMod d)) = Finset.Ioc D (2 * D) := by
    apply Finset.filter_true_of_mem
    intro d _
    rfl
  have hc : (Finset.Ioc D (2 * D)).card = D := by
    rw [Nat.card_Ioc]
    omega
  rw [P13cl, hfilter, hc]

/-- `P13cl` is at most the number of moduli, `D`. -/
lemma P13cl_le_D (D : ℕ) (q1 q2 : ℕ × ℕ) : P13cl D q1 q2 ≤ D := by
  have hc : (Finset.Ioc D (2 * D)).card = D := by
    rw [Nat.card_Ioc]; omega
  rw [P13cl]
  exact_mod_cast le_trans (Finset.card_le_card (Finset.filter_subset _ _)) (le_of_eq hc)

/-- `d ∣ Nat.dist A Bc` whenever `A ≡ Bc (mod d)`. -/
lemma P13_dist_dvd (A Bc d : ℕ) (h : A ≡ Bc [MOD d]) : d ∣ Nat.dist A Bc := by
  rcases Nat.le_total A Bc with hle | hle
  · rw [Nat.dist_eq_sub_of_le hle]
    have hh : Bc - A ≡ A - A [MOD d] := h.symm.sub hle le_rfl (Nat.ModEq.refl A)
    rwa [Nat.sub_self, Nat.modEq_zero_iff_dvd] at hh
  · rw [Nat.dist_eq_sub_of_le_right hle]
    have hh : A - Bc ≡ Bc - Bc [MOD d] := h.sub hle le_rfl (Nat.ModEq.refl Bc)
    rwa [Nat.sub_self, Nat.modEq_zero_iff_dvd] at hh

/-- The number of moduli `d ∈ (D,2D]` compatible with two *distinct* pairs is at most the number of
divisors of the distance `|A − B|`. -/
lemma P13_cong_card_le (D A Bc : ℕ) (h : A ≠ Bc) :
    ((Finset.Ioc D (2 * D)).filter (fun d => ((A : ℕ) : ZMod d) = ((Bc : ℕ) : ZMod d))).card
      ≤ (Nat.dist A Bc).divisors.card := by
  have hdist : Nat.dist A Bc ≠ 0 := by
    intro h0
    rcases Nat.le_total A Bc with hle | hle
    · rw [Nat.dist_eq_sub_of_le hle] at h0
      exact h (le_antisymm hle (Nat.sub_eq_zero_iff_le.mp h0))
    · rw [Nat.dist_eq_sub_of_le_right hle] at h0
      exact h (le_antisymm (Nat.sub_eq_zero_iff_le.mp h0) hle)
  refine Finset.card_le_card ?_
  intro d hd
  rw [Finset.mem_filter] at hd
  obtain ⟨hdmem, hcong⟩ := hd
  rw [Finset.mem_Ioc] at hdmem
  have hdpos : 0 < d := by omega
  have hmod : A % d = Bc % d := (ZMod.natCast_eq_natCast_iff' A Bc d).mp hcong
  rw [Nat.mem_divisors]
  exact ⟨P13_dist_dvd A Bc d hmod, hdist⟩

/-- The multiples of `p ≥ 1` in `[1,n]` number exactly `n / p`. -/
lemma P13_card_filter_dvd_aux (n p : ℕ) (hp : 1 ≤ p) :
    ((Finset.Icc 1 n).filter (fun r => p ∣ r)).card = n / p := by
  have hset : (Finset.Icc 1 n).filter (fun r => p ∣ r)
      = (Finset.Icc 1 (n / p)).image (fun k => p * k) := by
    ext r
    simp only [Finset.mem_filter, Finset.mem_Icc, Finset.mem_image]
    constructor
    · rintro ⟨⟨hr1, hr2⟩, k, rfl⟩
      have hk1 : 1 ≤ k := by
        rcases Nat.eq_zero_or_pos k with hk | hk
        · subst hk; simp at hr1
        · exact hk
      refine ⟨k, ⟨hk1, ?_⟩, rfl⟩
      rw [Nat.le_div_iff_mul_le (by omega : 0 < p)]
      calc k * p = p * k := Nat.mul_comm k p
        _ ≤ n := hr2
    · rintro ⟨k, ⟨hk1, hk2⟩, rfl⟩
      refine ⟨⟨?_, ?_⟩, k, rfl⟩
      · exact le_trans hk1 (Nat.le_mul_of_pos_left k (by omega : 0 < p))
      · calc p * k ≤ p * (n / p) := Nat.mul_le_mul_left p hk2
          _ ≤ n := Nat.mul_div_le n p
  rw [hset, Finset.card_image_of_injective _ (fun a b hh => Nat.mul_left_cancel (by omega : 0 < p) hh),
    Nat.card_Icc, Nat.add_sub_cancel]

/-- The number of pairs `(r,s)` of the box with `p ∣ r` is at most `4RS/p + 4`. -/
lemma P13_count_p_dvd_card (R S p : ℕ) :
    ((((Finset.Icc 1 (2 * R)) ×ˢ (Finset.Icc 1 (2 * S))).filter (fun q => p ∣ q.1)).card : ℝ)
      ≤ 4 * (R : ℝ) * (S : ℝ) / (p : ℝ) + 4 := by
  have hsplit : ((Finset.Icc 1 (2 * R)) ×ˢ (Finset.Icc 1 (2 * S))).filter (fun q => p ∣ q.1)
      = ((Finset.Icc 1 (2 * R)).filter (fun r => p ∣ r)) ×ˢ (Finset.Icc 1 (2 * S)) := by
    ext q
    simp only [Finset.mem_filter, Finset.mem_product]
    tauto
  rw [hsplit, Finset.card_product]
  rcases Nat.eq_zero_or_pos p with hp | hp
  · subst hp
    have hempty : (Finset.Icc 1 (2 * R)).filter (fun r => 0 ∣ r) = ∅ := by
      rw [Finset.eq_empty_iff_forall_notMem]
      intro r hr
      rw [Finset.mem_filter] at hr
      obtain ⟨hmem, k, hk⟩ := hr
      rw [Finset.mem_Icc] at hmem
      omega
    rw [hempty]
    simp
  · rw [Nat.cast_mul]
    have hcard : (((Finset.Icc 1 (2 * R)).filter (fun r => p ∣ r)).card : ℝ)
        = ((2 * R / p : ℕ) : ℝ) := by
      rw [P13_card_filter_dvd_aux (2 * R) p hp]
    have hS : (((Finset.Icc 1 (2 * S)).card : ℕ) : ℝ) = 2 * (S : ℝ) := by
      rw [Nat.card_Icc]; push_cast; ring
    rw [hcard, hS]
    have hdiv : ((2 * R / p : ℕ) : ℝ) ≤ 2 * (R : ℝ) / (p : ℝ) := by
      have hh := Nat.cast_div_le (α := ℝ) (m := 2 * R) (n := p)
      push_cast at hh
      exact hh
    have h2S : (0 : ℝ) ≤ 2 * (S : ℝ) := by positivity
    calc ((2 * R / p : ℕ) : ℝ) * (2 * (S : ℝ))
        ≤ (2 * (R : ℝ) / (p : ℝ)) * (2 * (S : ℝ)) := mul_le_mul_of_nonneg_right hdiv h2S
      _ = 4 * (R : ℝ) * (S : ℝ) / (p : ℝ) := by ring
      _ ≤ 4 * (R : ℝ) * (S : ℝ) / (p : ℝ) + 4 := by linarith

/-- The class sum of `EvarB` is the sum over the pair set `P13Sset`. -/
lemma P13_EvarClsSum_eq (R S d p : ℕ) (α : ℕ → ℕ → ℂ) (a : ℕ) :
    EvarClsSum R S d α (fun r => p ∣ r) a
      = ∑ q ∈ P13Sset R S d p a, α q.1 q.2 * jw d q.1 := by
  have hL : EvarClsSum R S d α (fun r => p ∣ r) a
      = ∑ r ∈ Finset.Icc 1 (2 * R),
          if (Nat.Coprime r d ∧ p ∣ r) then
            (∑ s ∈ (Finset.Icc 1 (2 * S)).filter
                (fun s' => ((s' : ℕ) : ZMod d) = ((r : ℕ) : ZMod d) * ((a : ℕ) : ZMod d)),
              α r s * jw d r)
          else 0 := by
    simp only [EvarClsSum, jw]
  have hset : (EvarCls R S d a).filter (fun q => p ∣ q.1)
      = ((Finset.Icc 1 (2 * R)) ×ˢ (Finset.Icc 1 (2 * S))).filter
          (fun q => (Nat.Coprime q.1 d ∧ p ∣ q.1) ∧
            ((q.2 : ZMod d) = (q.1 : ZMod d) * (a : ZMod d))) := by
    ext q
    simp only [Finset.mem_filter, mem_EvarCls, mem_EvarR, Finset.mem_product]
    tauto
  rw [hL]
  conv_rhs => rw [P13Sset, hset, Finset.sum_filter, Finset.sum_product]
  refine Finset.sum_congr rfl (fun r _ => ?_)
  by_cases hP : Nat.Coprime r d ∧ p ∣ r
  · rw [if_pos hP, Finset.sum_filter]
    refine Finset.sum_congr rfl (fun s _ => ?_)
    have hiff : (((s : ℕ) : ZMod d) = ((r : ℕ) : ZMod d) * ((a : ℕ) : ZMod d))
        ↔ ((Nat.Coprime r d ∧ p ∣ r) ∧
            ((s : ℕ) : ZMod d) = ((r : ℕ) : ZMod d) * ((a : ℕ) : ZMod d)) :=
      ⟨fun h => ⟨hP, h⟩, fun h => h.2⟩
    rw [if_congr hiff rfl rfl]
  · rw [if_neg hP]
    exact (Finset.sum_eq_zero (fun s _ => by rw [if_neg (fun h => hP h.1)])).symm

/-- `clsSum` of the restricted coefficient is the sum over the pair set `P13Sset`. -/
lemma P13_clsSum_restrict (R S d p : ℕ) (α : ℕ → ℕ → ℂ) (a : ℕ) :
    clsSum R S d (fun r s => if (Nat.Coprime r d ∧ p ∣ r) then α r s else 0) a
      = ∑ q ∈ P13Sset R S d p a, α q.1 q.2 * jw d q.1 := by
  rw [clsSum, P13Sset, Finset.sum_filter]
  refine Finset.sum_congr rfl (fun q hq => ?_)
  have hcop : Nat.Coprime q.1 d := (mem_EvarR.mp (mem_EvarCls.mp hq).1).2
  by_cases hp : p ∣ q.1
  · simp [hcop, hp]
  · simp [hp]

/-- `EvarB` as a sum of squared class sums of the restricted coefficient. -/
lemma P13_EvarB_eq (R S d p : ℕ) (α : ℕ → ℕ → ℂ) :
    EvarB R S d p α
      = ∑ a ∈ Finset.range d,
          Complex.normSq (clsSum R S d
            (fun r s => if (Nat.Coprime r d ∧ p ∣ r) then α r s else 0) a) := by
  rw [EvarB]
  refine Finset.sum_congr rfl (fun a _ => ?_)
  rw [P13_EvarClsSum_eq, ← P13_clsSum_restrict]

/-- **The reduction to an absolute-value pair sum**. -/
lemma P13_EvarB_le_WI (R S d p : ℕ) (α : ℕ → ℕ → ℂ) (hd : 0 < d) :
    EvarB R S d p α ≤ P13WI R S d p α := by
  set u : ℕ → ℕ → ℂ := fun r s => if (Nat.Coprime r d ∧ p ∣ r) then α r s else 0 with hu
  have hcopu : ∀ r s, u r s ≠ 0 → Nat.Coprime r d := by
    intro r s h
    by_contra hc
    apply h
    rw [hu]
    simp [hc]
  have hE : EvarB R S d p α = ∑ a ∈ Finset.range d, Complex.normSq (clsSum R S d u a) := by
    rw [P13_EvarB_eq]
  have hpair : pairSum R S d u u = ((EvarB R S d p α : ℝ) : ℂ) := by
    rw [hE, pairSum_decomp R S d hd u u hcopu hcopu, Complex.ofReal_sum]
    refine Finset.sum_congr rfl (fun a _ => ?_)
    exact Complex.mul_conj _
  have hEvarBnn : 0 ≤ EvarB R S d p α := by
    rw [EvarB]
    exact Finset.sum_nonneg (fun a _ => Complex.normSq_nonneg _)
  have hnorm : EvarB R S d p α = ‖pairSum R S d u u‖ := by
    rw [hpair]
    simp [abs_of_nonneg hEvarBnn]
  have htri : ‖pairSum R S d u u‖ ≤ P13WI R S d p α := by
    have hpairTerm : pairSum R S d u u
        = ∑ r1 ∈ Finset.Icc 1 (2 * R), ∑ s1 ∈ Finset.Icc 1 (2 * S),
          ∑ r2 ∈ Finset.Icc 1 (2 * R), ∑ s2 ∈ Finset.Icc 1 (2 * S),
            pairTerm d u u (r1, s1) (r2, s2) := by
      simp only [pairSum, pairTerm]
      refine Finset.sum_congr rfl (fun r1 _ => Finset.sum_congr rfl (fun s1 _ =>
        Finset.sum_congr rfl (fun r2 _ => Finset.sum_congr rfl (fun s2 _ => ?_))))
      by_cases hc : ((r1 * s2 : ℕ) : ZMod d) = ((r2 * s1 : ℕ) : ZMod d)
      · rw [if_pos hc, if_pos hc]
        exact pairTerm_eq d u u r1 s1 r2 s2
      · rw [if_neg hc, if_neg hc]
    have hlev : ∀ r1 s1 r2 s2 : ℕ,
        ‖pairTerm d u u (r1, s1) (r2, s2)‖
          ≤ (if (p ∣ r1 ∧ p ∣ r2 ∧ ((r1 * s2 : ℕ) : ZMod d) = ((r2 * s1 : ℕ) : ZMod d))
             then ‖α r1 s1‖ * ‖α r2 s2‖ else 0) := by
      intro r1 s1 r2 s2
      by_cases hc : ((r1 * s2 : ℕ) : ZMod d) = ((r2 * s1 : ℕ) : ZMod d)
      · rw [pairTerm, if_pos hc]
        have h1 : ‖u r1 s1‖ ≤ (if p ∣ r1 then ‖α r1 s1‖ else 0) := by
          rw [hu]; exact P13_norm_ite_le d p α r1 s1
        have h2 : ‖u r2 s2‖ ≤ (if p ∣ r2 then ‖α r2 s2‖ else 0) := by
          rw [hu]; exact P13_norm_ite_le d p α r2 s2
        calc ‖(u r1 s1 * jw d r1) * star (u r2 s2 * jw d r2)‖
            = ‖u r1 s1 * jw d r1‖ * ‖u r2 s2 * jw d r2‖ := by rw [norm_mul, norm_star]
          _ ≤ ‖u r1 s1‖ * ‖u r2 s2‖ := by
              exact mul_le_mul (norm_mul_jw_le d r1 (u r1 s1))
                (norm_mul_jw_le d r2 (u r2 s2)) (norm_nonneg _) (norm_nonneg _)
          _ ≤ (if p ∣ r1 then ‖α r1 s1‖ else 0) * (if p ∣ r2 then ‖α r2 s2‖ else 0) :=
              mul_le_mul h1 h2 (norm_nonneg _) (by split_ifs <;> positivity)
          _ = (if (p ∣ r1 ∧ p ∣ r2) then ‖α r1 s1‖ * ‖α r2 s2‖ else 0) := by
              by_cases hp1 : p ∣ r1 <;> by_cases hp2 : p ∣ r2 <;> simp [hp1, hp2]
          _ = (if (p ∣ r1 ∧ p ∣ r2 ∧ ((r1 * s2 : ℕ) : ZMod d) = ((r2 * s1 : ℕ) : ZMod d))
                then ‖α r1 s1‖ * ‖α r2 s2‖ else 0) := by
              rw [if_congr (show (p ∣ r1 ∧ p ∣ r2) ↔ (p ∣ r1 ∧ p ∣ r2 ∧
                    ((r1 * s2 : ℕ) : ZMod d) = ((r2 * s1 : ℕ) : ZMod d)) from
                  ⟨fun h => ⟨h.1, h.2, hc⟩, fun h => ⟨h.1, h.2.1⟩⟩) rfl rfl]
      · rw [pairTerm, if_neg hc, norm_zero]
        exact le_of_eq (if_neg (fun h => hc h.2.2)).symm
    rw [hpairTerm]
    calc ‖∑ r1 ∈ Finset.Icc 1 (2 * R), ∑ s1 ∈ Finset.Icc 1 (2 * S),
            ∑ r2 ∈ Finset.Icc 1 (2 * R), ∑ s2 ∈ Finset.Icc 1 (2 * S),
              pairTerm d u u (r1, s1) (r2, s2)‖
        ≤ ∑ r1 ∈ Finset.Icc 1 (2 * R), ∑ s1 ∈ Finset.Icc 1 (2 * S),
            ∑ r2 ∈ Finset.Icc 1 (2 * R), ∑ s2 ∈ Finset.Icc 1 (2 * S),
              ‖pairTerm d u u (r1, s1) (r2, s2)‖ :=
          norm_sum4_le _ _ _ _ _
      _ ≤ ∑ r1 ∈ Finset.Icc 1 (2 * R), ∑ s1 ∈ Finset.Icc 1 (2 * S),
            ∑ r2 ∈ Finset.Icc 1 (2 * R), ∑ s2 ∈ Finset.Icc 1 (2 * S),
              (if (p ∣ r1 ∧ p ∣ r2 ∧ ((r1 * s2 : ℕ) : ZMod d) = ((r2 * s1 : ℕ) : ZMod d))
               then ‖α r1 s1‖ * ‖α r2 s2‖ else 0) := by
          refine Finset.sum_le_sum (fun r1 _ => Finset.sum_le_sum (fun s1 _ =>
            Finset.sum_le_sum (fun r2 _ => Finset.sum_le_sum (fun s2 _ => hlev r1 s1 r2 s2))))
      _ = P13WI R S d p α := rfl
  rw [hnorm]
  exact htri

/-! ## The auxiliary pair function and the summation over `d` -/

/-- The box-level summand of the `d`-summation: the pair `q1` of the `p ∣ r` support, the pair
`q2`, weighted by the number of compatible moduli `d ∈ (D,2D]`. -/
def P13X (D p : ℕ) (α : ℕ → ℕ → ℂ) (q1 q2 : ℕ × ℕ) : ℝ :=
  if (p ∣ q1.1 ∧ p ∣ q2.1) then ‖α q1.1 q1.2‖ * ‖α q2.1 q2.2‖ * P13cl D q1 q2 else 0

lemma P13_X_self (D p : ℕ) (α : ℕ → ℕ → ℂ) (q : ℕ × ℕ) :
    P13X D p α q q = (if p ∣ q.1 then Complex.normSq (α q.1 q.2) * (D : ℝ) else 0) := by
  simp only [P13X]
  by_cases hp : p ∣ q.1
  · rw [if_pos ⟨hp, hp⟩, P13cl_self, if_pos hp]
    rw [Complex.normSq_eq_norm_sq, sq]
  · rw [if_neg (fun h => hp h.1), if_neg hp]

/-- The `L²`-mass on the `p ∣ r` support, as a sum over the pair box. -/
lemma P13_L2p_eq (R S p : ℕ) (α : ℕ → ℕ → ℂ) :
    (∑ q ∈ P13box R S, (if p ∣ q.1 then Complex.normSq (α q.1 q.2) else 0))
      = L2p R S p α := by
  rw [P13box, Finset.sum_product, L2p, Finset.sum_filter]
  refine Finset.sum_congr rfl (fun r _ => ?_)
  by_cases hp : p ∣ r <;> simp [hp]

lemma P13_L2p_nonneg (R S p : ℕ) (α : ℕ → ℕ → ℂ) : 0 ≤ L2p R S p α := by
  rw [L2p]
  refine Finset.sum_nonneg (fun r _ => Finset.sum_nonneg (fun s _ => ?_))
  exact Complex.normSq_nonneg _

/-- `(if c then x·y else 0) = y·(if c then x else 0)`. -/
lemma P13_ite_mul (c : Prop) [Decidable c] (x y : ℝ) :
    (if c then x * y else 0) = y * (if c then x else 0) := by
  by_cases h : c <;> simp [h, mul_comm]

/-- Interchanging the outermost sum of a fivefold nested sum. -/
lemma sum_comm5 {M : Type*} [AddCommMonoid M] (s1 s2 s3 s4 s5 : Finset ℕ)
    (f : ℕ → ℕ → ℕ → ℕ → ℕ → M) :
    (∑ a ∈ s1, ∑ b1 ∈ s2, ∑ b2 ∈ s3, ∑ b3 ∈ s4, ∑ b4 ∈ s5, f a b1 b2 b3 b4)
      = (∑ b1 ∈ s2, ∑ b2 ∈ s3, ∑ b3 ∈ s4, ∑ b4 ∈ s5, ∑ a ∈ s1, f a b1 b2 b3 b4) := by
  have h1 : (∑ a ∈ s1, ∑ b1 ∈ s2, ∑ b2 ∈ s3, ∑ b3 ∈ s4, ∑ b4 ∈ s5, f a b1 b2 b3 b4)
      = ∑ b1 ∈ s2, ∑ a ∈ s1, ∑ b2 ∈ s3, ∑ b3 ∈ s4, ∑ b4 ∈ s5, f a b1 b2 b3 b4 :=
    Finset.sum_comm
  have h2 : (∑ b1 ∈ s2, ∑ a ∈ s1, ∑ b2 ∈ s3, ∑ b3 ∈ s4, ∑ b4 ∈ s5, f a b1 b2 b3 b4)
      = ∑ b1 ∈ s2, ∑ b2 ∈ s3, ∑ a ∈ s1, ∑ b3 ∈ s4, ∑ b4 ∈ s5, f a b1 b2 b3 b4 := by
    refine Finset.sum_congr rfl (fun b1 _ => Finset.sum_comm)
  have h3 : (∑ b1 ∈ s2, ∑ b2 ∈ s3, ∑ a ∈ s1, ∑ b3 ∈ s4, ∑ b4 ∈ s5, f a b1 b2 b3 b4)
      = ∑ b1 ∈ s2, ∑ b2 ∈ s3, ∑ b3 ∈ s4, ∑ a ∈ s1, ∑ b4 ∈ s5, f a b1 b2 b3 b4 := by
    refine Finset.sum_congr rfl (fun b1 _ => Finset.sum_congr rfl (fun b2 _ => Finset.sum_comm))
  have h4 : (∑ b1 ∈ s2, ∑ b2 ∈ s3, ∑ b3 ∈ s4, ∑ a ∈ s1, ∑ b4 ∈ s5, f a b1 b2 b3 b4)
      = ∑ b1 ∈ s2, ∑ b2 ∈ s3, ∑ b3 ∈ s4, ∑ b4 ∈ s5, ∑ a ∈ s1, f a b1 b2 b3 b4 := by
    refine Finset.sum_congr rfl (fun b1 _ => Finset.sum_congr rfl (fun b2 _ =>
      Finset.sum_congr rfl (fun b3 _ => Finset.sum_comm)))
  exact h1.trans (h2.trans (h3.trans h4))

/-- A fourfold nested sum over the `r`- and `s`-ranges is a double sum over the pair box. -/
lemma sum4_eq_sum_box (R S : ℕ) (G : ℕ → ℕ → ℕ → ℕ → ℝ) :
    (∑ r1 ∈ Finset.Icc 1 (2 * R), ∑ s1 ∈ Finset.Icc 1 (2 * S),
     ∑ r2 ∈ Finset.Icc 1 (2 * R), ∑ s2 ∈ Finset.Icc 1 (2 * S), G r1 s1 r2 s2)
      = ∑ q1 ∈ P13box R S, ∑ q2 ∈ P13box R S, G q1.1 q1.2 q2.1 q2.2 := by
  have h1 : (∑ q1 ∈ P13box R S, ∑ q2 ∈ P13box R S, G q1.1 q1.2 q2.1 q2.2)
      = ∑ p ∈ Finset.Icc 1 (2 * R) ×ˢ Finset.Icc 1 (2 * S),
          ∑ q2 ∈ P13box R S, G p.1 p.2 q2.1 q2.2 := by
    rw [P13box]
  have h2 : (∑ p ∈ Finset.Icc 1 (2 * R) ×ˢ Finset.Icc 1 (2 * S),
          ∑ q2 ∈ P13box R S, G p.1 p.2 q2.1 q2.2)
      = ∑ r1 ∈ Finset.Icc 1 (2 * R), ∑ s1 ∈ Finset.Icc 1 (2 * S),
          ∑ q2 ∈ P13box R S, G r1 s1 q2.1 q2.2 :=
    Finset.sum_product _ _ _
  have h3 : ∀ r1 s1 : ℕ, (∑ q2 ∈ P13box R S, G r1 s1 q2.1 q2.2)
      = ∑ r2 ∈ Finset.Icc 1 (2 * R), ∑ s2 ∈ Finset.Icc 1 (2 * S), G r1 s1 r2 s2 := by
    intro r1 s1
    rw [P13box]
    exact Finset.sum_product _ _ _
  rw [h1, h2]
  refine Finset.sum_congr rfl (fun r1 _ => Finset.sum_congr rfl (fun s1 _ => ?_))
  exact (h3 r1 s1).symm

/-- The diagonal term: pairs with `q1 = q2` contribute `D` times the energy `L2p`. -/
lemma P13_diag_le (D R S p : ℕ) (α : ℕ → ℕ → ℂ) :
    (∑ q1 ∈ P13box R S, P13X D p α q1 q1) ≤ (D : ℝ) * L2p R S p α := by
  have hmain : (∑ q1 ∈ P13box R S, P13X D p α q1 q1) = (D : ℝ) * L2p R S p α := by
    calc ∑ q1 ∈ P13box R S, P13X D p α q1 q1
        = ∑ q1 ∈ P13box R S,
            (if p ∣ q1.1 then Complex.normSq (α q1.1 q1.2) * (D : ℝ) else 0) :=
          Finset.sum_congr rfl (fun q1 _ => P13_X_self D p α q1)
      _ = (D : ℝ) * ∑ q1 ∈ P13box R S,
            (if p ∣ q1.1 then Complex.normSq (α q1.1 q1.2) else 0) := by
          rw [Finset.mul_sum]
          refine Finset.sum_congr rfl (fun q1 _ => ?_)
          exact P13_ite_mul (p ∣ q1.1) (Complex.normSq (α q1.1 q1.2)) (D : ℝ)
      _ = (D : ℝ) * L2p R S p α := by rw [P13_L2p_eq]
  exact hmain.le

/-- The off-diagonal term: distinct pairs `q1 ≠ q2` each support at most `B` moduli. -/
lemma P13_off_le (D R S p : ℕ) (α : ℕ → ℕ → ℂ) (B : ℝ) (hB0 : 0 ≤ B)
    (hB : ∀ m : ℕ, 1 ≤ m → m ≤ 8 * R * S → ((m.divisors.card : ℕ) : ℝ) ≤ B)
    (hsup : ∀ r s, α r s ≠ 0 → Nat.Coprime r (2 * s)) :
    (∑ q1 ∈ P13box R S,
        ∑ q2 ∈ (P13box R S).filter (fun q2 => q2 ≠ q1), P13X D p α q1 q2)
      ≤ B * (4 * (R : ℝ) * (S : ℝ) / (p : ℝ) + 4) * L2p R S p α := by
  set V : ℕ × ℕ → ℝ := fun q => if p ∣ q.1 then ‖α q.1 q.2‖ else 0 with hV
  have hVnn : ∀ q, 0 ≤ V q := by
    intro q; rw [hV]; by_cases hq : p ∣ q.1 <;> simp [hq]
  have hVpf : ∀ q, p ∣ q.1 → V q = ‖α q.1 q.2‖ := by
    intro q hq; rw [hV]; simp [hq]
  have hVnf : ∀ q, ¬ p ∣ q.1 → V q = 0 := by
    intro q hq; rw [hV]; simp [hq]
  have hbound : ∀ q1 q2, q1 ∈ P13box R S → q2 ∈ P13box R S → q2 ≠ q1 →
      P13X D p α q1 q2 ≤ B * (V q1 * V q2) := by
    intro q1 q2 hq1 hq2 hne
    rw [P13X]
    by_cases hp : p ∣ q1.1 ∧ p ∣ q2.1
    · rw [if_pos hp, hVpf q1 hp.1, hVpf q2 hp.2]
      by_cases hz : ‖α q1.1 q1.2‖ * ‖α q2.1 q2.2‖ = 0
      · rw [hz]
        simp
      · have hn1 : α q1.1 q1.2 ≠ 0 := fun h0 => hz (by rw [h0]; simp)
        have hn2 : α q2.1 q2.2 ≠ 0 := fun h0 => hz (by rw [h0]; simp)
        have hAB : q1.1 * q2.2 ≠ q2.1 * q1.2 := by
          intro h
          obtain ⟨h1, h2⟩ := P13_same_ray (hsup _ _ hn1) (hsup _ _ hn2) h
          exact hne (Prod.ext h1 h2).symm
        have hq1a : q1.1 ≤ 2 * R := (Finset.mem_Icc.mp (mem_P13box.mp hq1).1).2
        have hq1b : q1.2 ≤ 2 * S := (Finset.mem_Icc.mp (mem_P13box.mp hq1).2).2
        have hq2a : q2.1 ≤ 2 * R := (Finset.mem_Icc.mp (mem_P13box.mp hq2).1).2
        have hq2b : q2.2 ≤ 2 * S := (Finset.mem_Icc.mp (mem_P13box.mp hq2).2).2
        have hA : q1.1 * q2.2 ≤ 8 * R * S := by
          calc q1.1 * q2.2 ≤ (2 * R) * (2 * S) := Nat.mul_le_mul hq1a hq2b
            _ = 4 * R * S := by ring
            _ ≤ 8 * R * S := by
                calc (4 : ℕ) * R * S = 4 * (R * S) := by ring
                  _ ≤ 8 * (R * S) := Nat.mul_le_mul_right _ (by norm_num)
                  _ = 8 * R * S := by ring
        have hBd : q2.1 * q1.2 ≤ 8 * R * S := by
          calc q2.1 * q1.2 ≤ (2 * R) * (2 * S) := Nat.mul_le_mul hq2a hq1b
            _ = 4 * R * S := by ring
            _ ≤ 8 * R * S := by
                calc (4 : ℕ) * R * S = 4 * (R * S) := by ring
                  _ ≤ 8 * (R * S) := Nat.mul_le_mul_right _ (by norm_num)
                  _ = 8 * R * S := by ring
        have hpos : 1 ≤ Nat.dist (q1.1 * q2.2) (q2.1 * q1.2) := by
          rcases Nat.lt_or_gt_of_ne hAB with h | h
          · rw [Nat.dist_eq_sub_of_le (le_of_lt h)]; omega
          · rw [Nat.dist_eq_sub_of_le_right (le_of_lt h)]; omega
        have hdist : Nat.dist (q1.1 * q2.2) (q2.1 * q1.2) ≤ 8 * R * S := by
          rcases Nat.le_total (q1.1 * q2.2) (q2.1 * q1.2) with h | h
          · rw [Nat.dist_eq_sub_of_le h]; omega
          · rw [Nat.dist_eq_sub_of_le_right h]; omega
        have hcl : P13cl D q1 q2 ≤ B := by
          rw [P13cl]
          have hcard := P13_cong_card_le D (q1.1 * q2.2) (q2.1 * q1.2) hAB
          have hB' : (((Nat.dist (q1.1 * q2.2) (q2.1 * q1.2)).divisors.card : ℕ) : ℝ) ≤ B :=
            hB _ hpos hdist
          exact le_trans (Nat.cast_le.mpr hcard) hB'
        calc ‖α q1.1 q1.2‖ * ‖α q2.1 q2.2‖ * P13cl D q1 q2
            ≤ ‖α q1.1 q1.2‖ * ‖α q2.1 q2.2‖ * B :=
              mul_le_mul_of_nonneg_left hcl (by positivity)
          _ = B * (‖α q1.1 q1.2‖ * ‖α q2.1 q2.2‖) := by ring
    · rw [if_neg hp]
      have hz : V q1 * V q2 = 0 := by
        by_cases h1 : p ∣ q1.1
        · have h2 : ¬ p ∣ q2.1 := fun h2 => hp ⟨h1, h2⟩
          simp [hVpf q1 h1, hVnf q2 h2]
        · simp [hVnf q1 h1]
      rw [hz]
      simp
  have hVsum_eq : ∑ q ∈ P13box R S, V q
      = ∑ q ∈ (P13box R S).filter (fun q => p ∣ q.1), V q := by
    rw [Finset.sum_filter]
    refine Finset.sum_congr rfl (fun q _ => ?_)
    by_cases hq : p ∣ q.1
    · simp [hq, hVpf q hq]
    · simp [hq, hVnf q hq]
  have hV2f : ∑ q ∈ (P13box R S).filter (fun q => p ∣ q.1), V q ^ 2 = L2p R S p α := by
    rw [Finset.sum_filter, ← P13_L2p_eq]
    refine Finset.sum_congr rfl (fun q _ => ?_)
    by_cases hq : p ∣ q.1
    · simp [hq, hVpf q hq, Complex.normSq_eq_norm_sq]
    · simp [hq]
  have hcs : (∑ q1 ∈ P13box R S, V q1) ^ 2
      ≤ (((P13box R S).filter (fun q => p ∣ q.1)).card : ℝ) * L2p R S p α := by
    rw [hVsum_eq]
    calc (∑ q ∈ (P13box R S).filter (fun q => p ∣ q.1), V q) ^ 2
        ≤ ((((P13box R S).filter (fun q => p ∣ q.1)).card : ℕ) : ℝ) *
            ∑ q ∈ (P13box R S).filter (fun q => p ∣ q.1), V q ^ 2 :=
          sq_sum_le_card_mul_sum_sq
      _ = (((P13box R S).filter (fun q => p ∣ q.1)).card : ℝ) * L2p R S p α := by rw [hV2f]
  calc (∑ q1 ∈ P13box R S,
          ∑ q2 ∈ (P13box R S).filter (fun q2 => q2 ≠ q1), P13X D p α q1 q2)
      ≤ ∑ q1 ∈ P13box R S, ∑ q2 ∈ (P13box R S).filter (fun q2 => q2 ≠ q1), B * (V q1 * V q2) := by
        refine Finset.sum_le_sum (fun q1 hq1 => Finset.sum_le_sum (fun q2 hq2 => ?_))
        rw [Finset.mem_filter] at hq2
        exact hbound q1 q2 hq1 hq2.1 hq2.2
    _ = B * (∑ q1 ∈ P13box R S,
          ∑ q2 ∈ (P13box R S).filter (fun q2 => q2 ≠ q1), V q1 * V q2) := by
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl (fun q1 _ => ?_)
        rw [Finset.mul_sum]
    _ ≤ B * (∑ q1 ∈ P13box R S, V q1) ^ 2 := by
        refine mul_le_mul_of_nonneg_left ?_ hB0
        calc ∑ q1 ∈ P13box R S, ∑ q2 ∈ (P13box R S).filter (fun q2 => q2 ≠ q1), V q1 * V q2
            ≤ ∑ q1 ∈ P13box R S, ∑ q2 ∈ P13box R S, V q1 * V q2 := by
              refine Finset.sum_le_sum (fun q1 _ => Finset.sum_le_sum_of_subset_of_nonneg
                (Finset.filter_subset _ _) (fun q2 _ _ => mul_nonneg (hVnn q1) (hVnn q2)))
          _ = (∑ q1 ∈ P13box R S, V q1) ^ 2 := by rw [sq, Finset.sum_mul_sum]
    _ ≤ B * ((4 * (R : ℝ) * (S : ℝ) / (p : ℝ) + 4) * L2p R S p α) := by
        refine mul_le_mul_of_nonneg_left ?_ hB0
        refine le_trans hcs ?_
        exact mul_le_mul_of_nonneg_right (P13_count_p_dvd_card R S p) (P13_L2p_nonneg R S p α)
    _ = B * (4 * (R : ℝ) * (S : ℝ) / (p : ℝ) + 4) * L2p R S p α := by ring

/-- **The trivial estimate for the `d`-summation** (FI (13.2)): summing the absolute-value
majorant over the dyadic range `D < d ≤ 2D` costs `D + B(4RS/p + 4)` times the `L²`-mass on the
`p ∣ r` support. -/
lemma P13_WI_sum_le (D R S p : ℕ) (α : ℕ → ℕ → ℂ) (B : ℝ) (hB0 : 0 ≤ B)
    (hB : ∀ m : ℕ, 1 ≤ m → m ≤ 8 * R * S → ((m.divisors.card : ℕ) : ℝ) ≤ B)
    (hsup : ∀ r s, α r s ≠ 0 → Nat.Coprime r (2 * s)) :
    (∑ d ∈ Finset.Ioc D (2 * D), P13WI R S d p α)
      ≤ ((D : ℝ) + B * (4 * (R : ℝ) * (S : ℝ) / (p : ℝ) + 4)) * L2p R S p α := by
  have hswap : (∑ d ∈ Finset.Ioc D (2 * D), P13WI R S d p α)
      = (∑ r1 ∈ Finset.Icc 1 (2 * R), ∑ s1 ∈ Finset.Icc 1 (2 * S),
         ∑ r2 ∈ Finset.Icc 1 (2 * R), ∑ s2 ∈ Finset.Icc 1 (2 * S),
         ∑ d ∈ Finset.Ioc D (2 * D),
           (if (p ∣ r1 ∧ p ∣ r2 ∧ ((r1 * s2 : ℕ) : ZMod d) = ((r2 * s1 : ℕ) : ZMod d))
            then ‖α r1 s1‖ * ‖α r2 s2‖ else 0)) := by
    simp only [P13WI]
    exact sum_comm5 (Finset.Ioc D (2 * D)) (Finset.Icc 1 (2 * R)) (Finset.Icc 1 (2 * S))
      (Finset.Icc 1 (2 * R)) (Finset.Icc 1 (2 * S))
      (fun d r1 s1 r2 s2 =>
        (if (p ∣ r1 ∧ p ∣ r2 ∧ ((r1 * s2 : ℕ) : ZMod d) = ((r2 * s1 : ℕ) : ZMod d))
         then ‖α r1 s1‖ * ‖α r2 s2‖ else 0))
  have hinner : ∀ r1 s1 r2 s2 : ℕ,
      (∑ d ∈ Finset.Ioc D (2 * D),
          (if (p ∣ r1 ∧ p ∣ r2 ∧ ((r1 * s2 : ℕ) : ZMod d) = ((r2 * s1 : ℕ) : ZMod d))
           then ‖α r1 s1‖ * ‖α r2 s2‖ else 0))
      = (if (p ∣ r1 ∧ p ∣ r2) then ‖α r1 s1‖ * ‖α r2 s2‖ * P13cl D (r1, s1) (r2, s2) else 0) := by
    intro r1 s1 r2 s2
    by_cases hp : p ∣ r1 ∧ p ∣ r2
    · rw [if_pos hp]
      have hfilt : (Finset.Ioc D (2 * D)).filter
            (fun d => p ∣ r1 ∧ p ∣ r2 ∧ ((r1 * s2 : ℕ) : ZMod d) = ((r2 * s1 : ℕ) : ZMod d))
          = (Finset.Ioc D (2 * D)).filter
            (fun d => ((r1 * s2 : ℕ) : ZMod d) = ((r2 * s1 : ℕ) : ZMod d)) := by
        ext d
        simp only [Finset.mem_filter]
        constructor
        · rintro ⟨hd, h⟩; exact ⟨hd, h.2.2⟩
        · rintro ⟨hd, h⟩; exact ⟨hd, hp.1, hp.2, h⟩
      rw [← Finset.sum_filter, hfilt, Finset.sum_const, nsmul_eq_mul, P13cl]
      ring
    · rw [if_neg hp]
      refine Finset.sum_eq_zero (fun d _ => ?_)
      rw [if_neg (fun h => hp ⟨h.1, h.2.1⟩)]
  have hstep2 : (∑ r1 ∈ Finset.Icc 1 (2 * R), ∑ s1 ∈ Finset.Icc 1 (2 * S),
        ∑ r2 ∈ Finset.Icc 1 (2 * R), ∑ s2 ∈ Finset.Icc 1 (2 * S),
        ∑ d ∈ Finset.Ioc D (2 * D),
          (if (p ∣ r1 ∧ p ∣ r2 ∧ ((r1 * s2 : ℕ) : ZMod d) = ((r2 * s1 : ℕ) : ZMod d))
           then ‖α r1 s1‖ * ‖α r2 s2‖ else 0))
      = (∑ r1 ∈ Finset.Icc 1 (2 * R), ∑ s1 ∈ Finset.Icc 1 (2 * S),
        ∑ r2 ∈ Finset.Icc 1 (2 * R), ∑ s2 ∈ Finset.Icc 1 (2 * S),
          (if (p ∣ r1 ∧ p ∣ r2) then ‖α r1 s1‖ * ‖α r2 s2‖ * P13cl D (r1, s1) (r2, s2)
           else 0)) := by
    refine Finset.sum_congr rfl (fun r1 _ => Finset.sum_congr rfl (fun s1 _ =>
      Finset.sum_congr rfl (fun r2 _ => Finset.sum_congr rfl (fun s2 _ => ?_))))
    exact hinner r1 s1 r2 s2
  have hbox_eq : (∑ d ∈ Finset.Ioc D (2 * D), P13WI R S d p α)
      = ∑ q1 ∈ P13box R S, ∑ q2 ∈ P13box R S, P13X D p α q1 q2 := by
    rw [hswap, hstep2, sum4_eq_sum_box]
    refine Finset.sum_congr rfl (fun q1 _ => Finset.sum_congr rfl (fun q2 _ => ?_))
    rfl
  have hsplit : (∑ q1 ∈ P13box R S, ∑ q2 ∈ P13box R S, P13X D p α q1 q2)
      = (∑ q1 ∈ P13box R S, P13X D p α q1 q1)
        + ∑ q1 ∈ P13box R S,
            ∑ q2 ∈ (P13box R S).filter (fun q2 => q2 ≠ q1), P13X D p α q1 q2 := by
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl (fun q1 hq1 => ?_)
    have h1 : ∑ q2 ∈ (P13box R S).filter (fun q2 => q2 = q1), P13X D p α q1 q2
        = P13X D p α q1 q1 := by
      rw [Finset.sum_filter, Finset.sum_ite_eq' _ _ _]
      rw [if_pos hq1]
    have h2 := Finset.sum_filter_add_sum_filter_not (P13box R S) (fun q2 => q2 = q1)
      (fun q2 => P13X D p α q1 q2)
    rw [h1] at h2
    exact h2.symm
  calc (∑ d ∈ Finset.Ioc D (2 * D), P13WI R S d p α)
      = ∑ q1 ∈ P13box R S, ∑ q2 ∈ P13box R S, P13X D p α q1 q2 := hbox_eq
    _ = (∑ q1 ∈ P13box R S, P13X D p α q1 q1)
        + ∑ q1 ∈ P13box R S,
            ∑ q2 ∈ (P13box R S).filter (fun q2 => q2 ≠ q1), P13X D p α q1 q2 := hsplit
    _ ≤ (D : ℝ) * L2p R S p α + B * (4 * (R : ℝ) * (S : ℝ) / (p : ℝ) + 4) * L2p R S p α :=
        add_le_add (P13_diag_le D R S p α) (P13_off_le D R S p α B hB0 hB hsup)
    _ = ((D : ℝ) + B * (4 * (R : ℝ) * (S : ℝ) / (p : ℝ) + 4)) * L2p R S p α := by ring

theorem P13_EvarB_sum (D R S p : ℕ) (α : ℕ → ℕ → ℂ) (B : ℝ)
    (hB : ∀ m : ℕ, 1 ≤ m → m ≤ 8 * R * S → ((m.divisors.card : ℕ) : ℝ) ≤ B)
    (hsup : ∀ r s, α r s ≠ 0 → Nat.Coprime r (2 * s)) :
    ∑ d ∈ Finset.Ioc D (2 * D), EvarB R S d p α
      ≤ ((D : ℝ) + B * (4 * (R : ℝ) * (S : ℝ) / (p : ℝ) + 4)) * L2p R S p α := by
  have hstep1 : (∑ d ∈ Finset.Ioc D (2 * D), EvarB R S d p α)
      ≤ ∑ d ∈ Finset.Ioc D (2 * D), P13WI R S d p α := by
    refine Finset.sum_le_sum (fun d hd => ?_)
    rw [Finset.mem_Ioc] at hd
    exact P13_EvarB_le_WI R S d p α (by omega)
  rcases Nat.eq_zero_or_pos (R * S) with hRS | hRS
  · have hL2p : L2p R S p α = 0 := by
      rw [L2p]
      rcases Nat.mul_eq_zero.mp hRS with hR | hS
      · refine Finset.sum_eq_zero (fun r hr => ?_)
        rw [Finset.mem_filter, Finset.mem_Icc] at hr
        omega
      · refine Finset.sum_eq_zero (fun r _ => Finset.sum_eq_zero (fun s hs => ?_))
        rw [Finset.mem_Icc] at hs
        omega
    have hWI0 : ∀ d, P13WI R S d p α = 0 := by
      intro d
      simp only [P13WI]
      rcases Nat.mul_eq_zero.mp hRS with hR | hS
      · refine Finset.sum_eq_zero (fun r1 hr => ?_)
        rw [Finset.mem_Icc] at hr
        omega
      · refine Finset.sum_eq_zero (fun r1 _ => Finset.sum_eq_zero (fun s1 hs => ?_))
        rw [Finset.mem_Icc] at hs
        omega
    calc (∑ d ∈ Finset.Ioc D (2 * D), EvarB R S d p α)
        ≤ ∑ d ∈ Finset.Ioc D (2 * D), P13WI R S d p α := hstep1
      _ = 0 := Finset.sum_eq_zero (fun d _ => hWI0 d)
      _ = ((D : ℝ) + B * (4 * (R : ℝ) * (S : ℝ) / (p : ℝ) + 4)) * L2p R S p α := by
          rw [hL2p, mul_zero]
  · have hRS1 : 1 ≤ R * S := by omega
    have h1le : 1 ≤ 8 * R * S := by
      calc 1 ≤ 8 * 1 := by norm_num
        _ ≤ 8 * (R * S) := Nat.mul_le_mul_left 8 hRS1
        _ = 8 * R * S := by ring
    have hB0 : 0 ≤ B := by
      have h := hB 1 le_rfl h1le
      have h1 : ((1 : ℕ).divisors.card : ℝ) = 1 := by simp
      rw [h1] at h
      linarith
    calc (∑ d ∈ Finset.Ioc D (2 * D), EvarB R S d p α)
        ≤ ∑ d ∈ Finset.Ioc D (2 * D), P13WI R S d p α := hstep1
      _ ≤ ((D : ℝ) + B * (4 * (R : ℝ) * (S : ℝ) / (p : ℝ) + 4)) * L2p R S p α :=
          P13_WI_sum_le D R S p α B hB0 hB hsup

end

end Work.FIArea4
