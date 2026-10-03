import Mathlib
import Submission.Work.FIArea4.box_defs
import Submission.Work.FIArea4.flat_defs
import Submission.Work.FIArea4.Vflip.KK_eq_tsum_gen
import Submission.Work.FIArea4.Vflip.count_coset_supp
import Submission.Work.FIArea4.Vflip.card_sq_filter_le
import Submission.Work.FIArea4.Vflip.count_coset_box
import Submission.Work.FIArea4.tsum_bump_le_card
import Submission.Work.FIArea4.flat_numeric
import Submission.Work.FIArea4.flat_pair_sum_le

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

namespace Work.FIArea4

open Finset
open scoped BigOperators

noncomputable section

attribute [local instance] Classical.propDecidable

/-! ### basic definitions -/

/-- The lattice sum of `f` along the progression `r*a + q*ℤ`. -/
def fbnM (f : ℝ → ℝ) (r a q : ℕ) : ℝ := ∑' m : ℤ, f ((r * a : ℝ) + (m : ℝ) * (q : ℝ))

/-- The local energy of the flat part attached to a modulus `d`, using the `q`-lattice. -/
def fbnP (f : ℝ → ℝ) (R q E d : ℕ) (γ : ℕ → ℕ → ℂ) : ℝ :=
  ∑ r ∈ (Finset.Ioc R (2 * R)).filter (fun r => Nat.Coprime r E),
    ∑ a ∈ Finset.range q, ‖γ (a % d) d‖ ^ 2 * fbnM f r a q

/-- The energy of `γ` at a single modulus. -/
def fbnE (γ : ℕ → ℕ → ℂ) (d : ℕ) : ℝ := ∑ a ∈ Finset.range d, ‖γ a d‖ ^ 2

lemma fbnM_nonneg {f : ℝ → ℝ} (hf : ∀ x, 0 ≤ f x) (r a q : ℕ) : 0 ≤ fbnM f r a q :=
  tsum_nonneg (fun m => hf _)

/-! ### uniqueness of the residue class -/

lemma mul_mod_inj {q r a a' : ℕ} (hq : 0 < q) (hrq : Nat.Coprime r q)
    (ha : a < q) (ha' : a' < q) (h : (r * a) % q = (r * a') % q) : a = a' := by
  haveI : NeZero q := ⟨by omega⟩
  have hz : ((r * a : ℕ) : ZMod q) = ((r * a' : ℕ) : ZMod q) := by
    rw [ZMod.natCast_eq_natCast_iff]; exact h
  push_cast at hz
  have hunit : IsUnit ((r : ZMod q)) := (ZMod.isUnit_iff_coprime r q).mpr hrq
  have h2 : ((a : ℕ) : ZMod q) = ((a' : ℕ) : ZMod q) := by
    have h3 := congrArg (fun z : ZMod q => ((r : ZMod q))⁻¹ * z) hz
    rwa [← mul_assoc, ZMod.inv_mul_of_unit _ hunit, one_mul,
         ← mul_assoc, ZMod.inv_mul_of_unit _ hunit, one_mul] at h3
  have h4 := congrArg ZMod.val h2
  simp only [ZMod.val_natCast] at h4
  rwa [Nat.mod_eq_of_lt ha, Nat.mod_eq_of_lt ha'] at h4

/-! ### Poisson identity for the bump -/

lemma rpow_neg_two_le {a b : ℝ} (ha : 0 < a) (hab : a ≤ b) :
    b ^ (-(2:ℝ)) ≤ a ^ (-(2:ℝ)) :=
  Real.rpow_le_rpow_of_nonpos ha hab (by norm_num)

lemma bump_KK_tsum (S : ℕ) (hS : 1 ≤ S) (f : ℝ → ℝ) (F : ℝ → ℂ) (C₀ : ℝ)
    (hM : BumpData S f F C₀) (R d1 d2 a : ℕ) (hd1 : 1 ≤ d1) (hd2 : 1 ≤ d2)
    (hflat : ∃ m : ℕ, Work.FIPlan.oddPart d1 * Work.FIPlan.oddPart d2 = m ^ 2) :
    KK F R d1 d2 a = ∑ r ∈ (Finset.Ioc R (2 * R)).filter (fun r => Nat.Coprime r (d1 * d2)),
        ∑' m : ℤ, ((f ((r * a : ℝ) + (m : ℝ) * (Nat.lcm d1 d2 : ℝ))) : ℂ) := by
  obtain ⟨h1, h2, h3, h4, h5, h6, h7⟩ := hM
  have hS1 : (1:ℝ) ≤ (S:ℝ) := by exact_mod_cast hS
  have hcont : Continuous (fun x : ℝ => (f x : ℂ)) := Complex.continuous_ofReal.comp h4
  have hg : (fun x : ℝ => (f x : ℂ)) =O[Filter.cocompact ℝ] (fun x : ℝ => abs x ^ (-(2:ℝ))) := by
    refine Asymptotics.IsBigO.of_bound 1 ?_
    rw [Filter.eventually_iff, Filter.mem_cocompact]
    refine ⟨Set.Icc (-(5 * (S:ℝ) / 2)) (5 * (S:ℝ) / 2), isCompact_Icc, ?_⟩
    intro x hx
    simp only [Set.mem_ofPred_eq]
    have hfx : f x = 0 := by
      by_contra h
      obtain ⟨hlo, hhi⟩ := h3 x h
      rw [Set.mem_compl_iff, Set.mem_Icc, not_and_or, not_le, not_le] at hx
      rcases hx with hx | hx
      · linarith
      · linarith
    rw [hfx, Complex.ofReal_zero, norm_zero]
    positivity
  have hFg : ∀ ξ, FourierTransform.fourier (fun x : ℝ => (f x : ℂ)) ξ = F ξ :=
    fun ξ => (h6 ξ).symm
  have hFbigO : (FourierTransform.fourier (fun x : ℝ => (f x : ℂ)))
      =O[Filter.cocompact ℝ] (fun x : ℝ => abs x ^ (-(2:ℝ))) := by
    refine Asymptotics.IsBigO.of_bound C₀ ?_
    rw [Filter.eventually_iff, Filter.mem_cocompact]
    refine ⟨{0}, isCompact_singleton, ?_⟩
    intro x hx
    simp only [Set.mem_ofPred_eq]
    rw [hFg x]
    have hx0 : (0:ℝ) < |x| := abs_pos.mpr (by simpa using hx)
    have hT : (0:ℝ) < (S:ℝ) * |x| := by positivity
    have hnorm : ‖abs x ^ (-(2:ℝ))‖ = abs x ^ (-(2:ℝ)) := by
      rw [Real.norm_eq_abs, abs_of_nonneg]; positivity
    rw [hnorm]
    have hrpow : (1 + (S:ℝ) * |x|) ^ (-(2:ℝ)) ≤ ((S:ℝ) * |x|) ^ (-(2:ℝ)) :=
      rpow_neg_two_le hT (by linarith)
    have hb2 : (S:ℝ) * (((S:ℝ) * |x|) ^ (-(2:ℝ))) ≤ abs x ^ (-(2:ℝ)) := by
      have e1 : ((S:ℝ) * |x|) ^ (-(2:ℝ)) = (((S:ℝ) * |x|) * ((S:ℝ) * |x|))⁻¹ := by
        rw [Real.rpow_neg (by positivity) (2:ℝ), Real.rpow_two]; ring
      have e2 : abs x ^ (-(2:ℝ)) = (|x| * |x|)⁻¹ := by
        rw [Real.rpow_neg (abs_nonneg x) (2:ℝ), Real.rpow_two]; ring
      rw [e1, e2]
      have hmul : (S:ℝ) * (((S:ℝ)*|x|) * ((S:ℝ)*|x|))⁻¹ = (|x| * |x|)⁻¹ * (S:ℝ)⁻¹ := by
        field_simp
      rw [hmul]
      have hSinv : (S:ℝ)⁻¹ ≤ 1 := by
        rw [inv_le_one₀ (by positivity)]; exact hS1
      have hpos : (0:ℝ) ≤ (|x| * |x|)⁻¹ := by positivity
      nlinarith [hSinv, hpos]
    calc ‖F x‖ ≤ C₀ * (S:ℝ) * (1 + (S:ℝ) * |x|) ^ (-(2:ℝ)) := h7 x
      _ = C₀ * ((S:ℝ) * (1 + (S:ℝ) * |x|) ^ (-(2:ℝ))) := by ring
      _ ≤ C₀ * ((S:ℝ) * ((S:ℝ) * |x|) ^ (-(2:ℝ))) :=
            mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hrpow (by positivity)) h5.le
      _ ≤ C₀ * abs x ^ (-(2:ℝ)) := mul_le_mul_of_nonneg_left hb2 h5.le
  have hkey := Vflip.KK_eq_tsum_gen (fun x : ℝ => (f x : ℂ)) hcont (by norm_num : (1:ℝ) < 2)
    hg hFbigO R S d1 d2 a hS hd1 hd2 hflat
  have hFF : F = (FourierTransform.fourier (fun x : ℝ => (f x : ℂ))) := funext h6
  rw [hFF, hkey]

/-! ### the KK bound -/

lemma fbn_KK_le {S : ℕ} (hS : 1 ≤ S) {f : ℝ → ℝ} {F : ℝ → ℂ} {C₀ : ℝ}
    (hM : BumpData S f F C₀) (R d1 d2 : ℕ) (hd1 : 1 ≤ d1) (hd2 : 1 ≤ d2)
    (hflat : flatPair d1 d2) (a : ℕ) :
    ‖KK F R d1 d2 a‖ ≤ ∑ r ∈ (Finset.Ioc R (2 * R)).filter (fun r => Nat.Coprime r (d1 * d2)),
        fbnM f r a (Nat.lcm d1 d2) := by
  obtain ⟨h1,h2,h3,h4,h5,h6,h7⟩ := hM
  rw [bump_KK_tsum S hS f F C₀ ⟨h1,h2,h3,h4,h5,h6,h7⟩ R d1 d2 a hd1 hd2 hflat]
  refine (norm_sum_le _ _).trans (Finset.sum_le_sum ?_)
  intro r hr
  rw [← Complex.ofReal_tsum, Complex.norm_real, Real.norm_eq_abs]
  rw [abs_of_nonneg (tsum_nonneg (fun m => h1 _))]
  exact le_of_eq rfl

/-! ### Cauchy-Schwarz in the `a` variable -/

lemma fbn_cs_inner (s : Finset ℕ) (x y M : ℕ → ℝ) (hM : ∀ a, 0 ≤ M a) :
    ∑ a ∈ s, x a * y a * M a
      ≤ Real.sqrt (∑ a ∈ s, x a ^ 2 * M a) * Real.sqrt (∑ a ∈ s, y a ^ 2 * M a) := by
  have h1 : ∑ a ∈ s, x a * y a * M a
      = ∑ a ∈ s, (x a * Real.sqrt (M a)) * (y a * Real.sqrt (M a)) := by
    apply Finset.sum_congr rfl; intro a ha
    have hsq : Real.sqrt (M a) * Real.sqrt (M a) = M a := Real.mul_self_sqrt (hM a)
    rw [show (x a * Real.sqrt (M a)) * (y a * Real.sqrt (M a))
        = x a * y a * (Real.sqrt (M a) * Real.sqrt (M a)) by ring, hsq]
  rw [h1]
  refine (Real.sum_mul_le_sqrt_mul_sqrt s (fun a => x a * Real.sqrt (M a))
    (fun a => y a * Real.sqrt (M a))).trans (le_of_eq ?_)
  have e1 : (∑ i ∈ s, (x i * Real.sqrt (M i)) ^ 2) = ∑ a ∈ s, x a ^ 2 * M a :=
    Finset.sum_congr rfl (fun a ha => by rw [mul_pow, Real.sq_sqrt (hM a)])
  have e2 : (∑ i ∈ s, (y i * Real.sqrt (M i)) ^ 2) = ∑ a ∈ s, y a ^ 2 * M a :=
    Finset.sum_congr rfl (fun a ha => by rw [mul_pow, Real.sq_sqrt (hM a)])
  rw [e1, e2]

/-! ### the per-pair bound -/

lemma fbn_pair_le {S : ℕ} (hS : 1 ≤ S) {f : ℝ → ℝ} {F : ℝ → ℂ} {C₀ : ℝ}
    (hM : BumpData S f F C₀) (R d1 d2 : ℕ) (γ : ℕ → ℕ → ℂ)
    (hd1 : 1 ≤ d1) (hd2 : 1 ≤ d2) (hflat : flatPair d1 d2) :
    ‖∑ a ∈ Finset.range (Nat.lcm d1 d2),
        γ (a % d1) d1 * (starRingEnd ℂ) (γ (a % d2) d2) * KK F R d1 d2 a‖
      ≤ Real.sqrt (fbnP f R (Nat.lcm d1 d2) (d1 * d2) d1 γ)
          * Real.sqrt (fbnP f R (Nat.lcm d1 d2) (d1 * d2) d2 γ) := by
  obtain ⟨h1,h2,h3,h4,h5,h6,h7⟩ := hM
  set q : ℕ := Nat.lcm d1 d2 with hq
  set Fr : Finset ℕ := (Finset.Ioc R (2*R)).filter (fun r => Nat.Coprime r (d1*d2)) with hFr
  have hstep1 : ‖∑ a ∈ Finset.range q, γ (a%d1) d1 * (starRingEnd ℂ) (γ (a%d2) d2) * KK F R d1 d2 a‖
      ≤ ∑ a ∈ Finset.range q, ∑ r ∈ Fr, ‖γ (a%d1) d1‖ * ‖γ (a%d2) d2‖ * fbnM f r a q := by
    refine (norm_sum_le _ _).trans (Finset.sum_le_sum ?_)
    intro a ha
    have h2' := fbn_KK_le hS ⟨h1,h2,h3,h4,h5,h6,h7⟩ R d1 d2 hd1 hd2 hflat a
    rw [← hq, ← hFr] at h2'
    calc ‖γ (a%d1) d1 * (starRingEnd ℂ) (γ (a%d2) d2) * KK F R d1 d2 a‖
        = ‖γ (a%d1) d1‖ * ‖γ (a%d2) d2‖ * ‖KK F R d1 d2 a‖ := by
          rw [norm_mul, norm_mul, Complex.norm_conj]
      _ ≤ ‖γ (a%d1) d1‖ * ‖γ (a%d2) d2‖ * (∑ r ∈ Fr, fbnM f r a q) :=
          mul_le_mul_of_nonneg_left h2' (by positivity)
      _ = ∑ r ∈ Fr, ‖γ (a%d1) d1‖ * ‖γ (a%d2) d2‖ * fbnM f r a q := by
          rw [Finset.mul_sum]
  have hstep3 : (∑ r ∈ Fr, ∑ a ∈ Finset.range q,
        ‖γ (a%d1) d1‖ * ‖γ (a%d2) d2‖ * fbnM f r a q)
      ≤ Real.sqrt (∑ r ∈ Fr, ∑ a ∈ Finset.range q, ‖γ (a%d1) d1‖^2 * fbnM f r a q)
        * Real.sqrt (∑ r ∈ Fr, ∑ a ∈ Finset.range q, ‖γ (a%d2) d2‖^2 * fbnM f r a q) := by
    have hnn : ∀ r a, 0 ≤ fbnM f r a q := fun r a => fbnM_nonneg h1 r a q
    have hpt : ∀ r, ∑ a ∈ Finset.range q, ‖γ (a%d1) d1‖ * ‖γ (a%d2) d2‖ * fbnM f r a q
        ≤ Real.sqrt (∑ a ∈ Finset.range q, ‖γ (a%d1) d1‖^2 * fbnM f r a q)
          * Real.sqrt (∑ a ∈ Finset.range q, ‖γ (a%d2) d2‖^2 * fbnM f r a q) :=
      fun r => fbn_cs_inner _ _ _ _ (fun a => hnn r a)
    refine (Finset.sum_le_sum (fun r hr => hpt r)).trans ?_
    have hmain := Real.sum_mul_le_sqrt_mul_sqrt Fr
      (fun r => Real.sqrt (∑ a ∈ Finset.range q, ‖γ (a%d1) d1‖^2 * fbnM f r a q))
      (fun r => Real.sqrt (∑ a ∈ Finset.range q, ‖γ (a%d2) d2‖^2 * fbnM f r a q))
    have e1 : (∑ r ∈ Fr, (Real.sqrt (∑ a ∈ Finset.range q, ‖γ (a%d1) d1‖^2 * fbnM f r a q))^2)
        = ∑ r ∈ Fr, ∑ a ∈ Finset.range q, ‖γ (a%d1) d1‖^2 * fbnM f r a q :=
      Finset.sum_congr rfl (fun r _ => Real.sq_sqrt (Finset.sum_nonneg (fun a _ =>
        mul_nonneg (by positivity) (hnn r a))))
    have e2 : (∑ r ∈ Fr, (Real.sqrt (∑ a ∈ Finset.range q, ‖γ (a%d2) d2‖^2 * fbnM f r a q))^2)
        = ∑ r ∈ Fr, ∑ a ∈ Finset.range q, ‖γ (a%d2) d2‖^2 * fbnM f r a q :=
      Finset.sum_congr rfl (fun r _ => Real.sq_sqrt (Finset.sum_nonneg (fun a _ =>
        mul_nonneg (by positivity) (hnn r a))))
    rw [e1, e2] at hmain
    exact hmain
  calc ‖∑ a ∈ Finset.range q, γ (a%d1) d1 * (starRingEnd ℂ) (γ (a%d2) d2) * KK F R d1 d2 a‖
      ≤ ∑ a ∈ Finset.range q, ∑ r ∈ Fr, ‖γ (a%d1) d1‖ * ‖γ (a%d2) d2‖ * fbnM f r a q := hstep1
    _ = ∑ r ∈ Fr, ∑ a ∈ Finset.range q, ‖γ (a%d1) d1‖ * ‖γ (a%d2) d2‖ * fbnM f r a q :=
        Finset.sum_comm
    _ ≤ Real.sqrt (∑ r ∈ Fr, ∑ a ∈ Finset.range q, ‖γ (a%d1) d1‖^2 * fbnM f r a q)
        * Real.sqrt (∑ r ∈ Fr, ∑ a ∈ Finset.range q, ‖γ (a%d2) d2‖^2 * fbnM f r a q) := hstep3
    _ = Real.sqrt (fbnP f R (Nat.lcm d1 d2) (d1 * d2) d1 γ)
        * Real.sqrt (fbnP f R (Nat.lcm d1 d2) (d1 * d2) d2 γ) := by
        unfold fbnP
        rw [← hq, ← hFr]

/-! ### the fibre bound -/

lemma fbn_fiber_le (B : Finset ℕ) (q d r a1 : ℕ) (hq : 0 < q) (hdq : d ∣ q)
    (hrq : Nat.Coprime r q) (ha1 : a1 < d) :
    ∑ a ∈ (Finset.range q).filter (fun a => a % d = a1),
        (B.filter (fun s => s % q = (r * a) % q)).card
      ≤ (B.filter (fun s => s % d = (r * a1) % d)).card := by
  rw [← Work.FIArea4.card_filter_product_eq_sum_fst
      ((Finset.range q).filter (fun a => a % d = a1)) B
      (fun p : ℕ × ℕ => p.2 % q = (r * p.1) % q)]
  rw [Finset.product_eq_sprod]
  refine Finset.card_le_card_of_injOn Prod.snd ?_ ?_
  · intro p hp
    simp only [Finset.mem_coe, Finset.mem_filter, Finset.mem_product] at hp ⊢
    obtain ⟨⟨⟨ha, hpa⟩, hs⟩, hP⟩ := hp
    refine ⟨hs, ?_⟩
    have hmul : (r * p.1) % d = (r * a1) % d := by
      rw [Nat.mul_mod r p.1 d, hpa, Nat.mul_mod r a1 d, Nat.mod_eq_of_lt ha1]
    rw [← Nat.mod_mod_of_dvd p.2 hdq, hP, Nat.mod_mod_of_dvd _ hdq, hmul]
  · intro p hp p' hp' heq
    simp only [Finset.mem_coe, Finset.mem_filter, Finset.mem_product] at hp hp'
    obtain ⟨⟨⟨ha, hpa⟩, hs⟩, hP⟩ := hp
    obtain ⟨⟨⟨ha', hpa'⟩, hs'⟩, hP'⟩ := hp'
    have hmod : (r * p.1) % q = (r * p'.1) % q := by rw [← hP, ← hP', heq]
    have h1 : p.1 = p'.1 :=
      mul_mod_inj hq hrq (Finset.mem_range.mp ha) (Finset.mem_range.mp ha') hmod
    exact Prod.ext h1 heq

/-! ### bounding the local energy -/

lemma suppBox_subset_box (S : ℕ) (hS : 1 ≤ S) :
    Work.FIArea4.suppBox S ⊆ Finset.Ioc (S / 2 - 1) (S / 2 - 1 + (2 * S + 2)) := by
  intro s hs
  rw [Work.FIArea4.suppBox, Finset.mem_Ioc] at hs
  rw [Finset.mem_Ioc]
  have h1 : 5*S/2 ≤ S/2 - 1 + (2*S + 2) := by omega
  omega

set_option maxHeartbeats 2000000 in
lemma fbnP_le {S : ℕ} (hS : 1 ≤ S) {f : ℝ → ℝ}
    (hfnn : ∀ x, 0 ≤ f x) (hf1 : ∀ x, f x ≤ 1)
    (hsupp : ∀ x, f x ≠ 0 → (S : ℝ) / 2 ≤ x ∧ x ≤ 5 * (S : ℝ) / 2)
    (R q E d : ℕ) (γ : ℕ → ℕ → ℂ) (hR : 1 ≤ R) (hd : 1 ≤ d)
    (hq : 0 < q) (hdq : d ∣ q) (hEq : q ∣ E) :
    fbnP f R q E d γ
      ≤ ((10 * (R * (2*S+2) / d + min R (2*S+2) + 1) : ℕ) : ℝ) * fbnE γ d := by
  set B : Finset ℕ := Finset.Ioc (S / 2 - 1) (S / 2 - 1 + (2 * S + 2)) with hB
  set Fr : Finset ℕ := (Finset.Ioc R (2 * R)).filter (fun r => Nat.Coprime r E) with hFr
  set K : ℝ := ((10 * (R * (2*S+2) / d + min R (2*S+2) + 1) : ℕ) : ℝ) with hK
  have hle1 : ∀ r a, fbnM f r a q ≤ ((B.filter (fun s => s % q = (r * a) % q)).card : ℝ) := by
    intro r a
    refine (tsum_bump_le_card hS hfnn hf1 hsupp r a q hq).trans ?_
    exact_mod_cast Finset.card_le_card (Finset.filter_subset_filter _ (suppBox_subset_box S hS))
  have hstepA : fbnP f R q E d γ
      ≤ ∑ r ∈ Fr, ∑ a ∈ Finset.range q,
          ‖γ (a % d) d‖ ^ 2 * ((B.filter (fun s => s % q = (r * a) % q)).card : ℝ) := by
    unfold fbnP
    rw [← hFr]
    apply Finset.sum_le_sum; intro r hr
    apply Finset.sum_le_sum; intro a ha
    exact mul_le_mul_of_nonneg_left (hle1 r a) (by positivity)
  have hstepB : ∀ r ∈ Fr, ∑ a ∈ Finset.range q,
        ‖γ (a % d) d‖ ^ 2 * ((B.filter (fun s => s % q = (r * a) % q)).card : ℝ)
      ≤ ∑ a1 ∈ Finset.range d,
        ‖γ a1 d‖ ^ 2 * ((B.filter (fun s => s % d = (r * a1) % d)).card : ℝ) := by
    intro r hr
    have hrq : Nat.Coprime r q := Nat.Coprime.coprime_dvd_right hEq (Finset.mem_filter.mp hr).2
    rw [← Finset.sum_fiberwise_of_maps_to
      (t := Finset.range d) (g := fun a => a % d)
      (fun i hi => Finset.mem_range.mpr (Nat.mod_lt _ hd))
      (fun a => ‖γ (a % d) d‖ ^ 2 * ((B.filter (fun s => s % q = (r * a) % q)).card : ℝ))]
    apply Finset.sum_le_sum; intro a1 ha1
    have ha1lt : a1 < d := Finset.mem_range.mp ha1
    have hcongr : ∑ a ∈ (Finset.range q).filter (fun a => a % d = a1),
          ‖γ (a % d) d‖ ^ 2 * ((B.filter (fun s => s % q = (r * a) % q)).card : ℝ)
        = ∑ a ∈ (Finset.range q).filter (fun a => a % d = a1),
          ‖γ a1 d‖ ^ 2 * ((B.filter (fun s => s % q = (r * a) % q)).card : ℝ) := by
      apply Finset.sum_congr rfl; intro a ha
      rw [(Finset.mem_filter.mp ha).2]
    rw [hcongr, ← Finset.mul_sum]
    refine mul_le_mul_of_nonneg_left ?_ (by positivity)
    exact_mod_cast fbn_fiber_le B q d r a1 hq hdq hrq ha1lt
  have hcount : ∀ a1 ∈ Finset.range d,
      ∑ r ∈ Fr, ((B.filter (fun s => s % d = (r * a1) % d)).card : ℝ) ≤ K := by
    intro a1 ha1
    rw [hK, ← Nat.cast_sum]
    apply Nat.cast_le.mpr
    calc ∑ r ∈ Fr, (B.filter (fun s => s % d = (r * a1) % d)).card
        ≤ ∑ r ∈ Finset.Ioc R (2*R), (B.filter (fun s => s % d = (r * a1) % d)).card :=
          Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
            (fun r _ _ => Nat.zero_le _)
      _ = (((Finset.Ioc R (2*R)).product B).filter
              (fun p : ℕ × ℕ => p.2 % d = (p.1 * a1) % d)).card :=
          (Work.FIArea4.card_filter_product_eq_sum_fst (Finset.Ioc R (2*R)) B
            (fun p : ℕ × ℕ => p.2 % d = (p.1 * a1) % d)).symm
      _ ≤ 10 * (R * (2*S+2) / d + min R (2*S+2) + 1) := by
          rw [hB]
          exact Vflip.count_coset_box (S/2 - 1) (2*S+2) R d a1 hR (by omega) hd (by omega)
  calc fbnP f R q E d γ
      ≤ ∑ r ∈ Fr, ∑ a ∈ Finset.range q,
          ‖γ (a % d) d‖ ^ 2 * ((B.filter (fun s => s % q = (r * a) % q)).card : ℝ) := hstepA
    _ ≤ ∑ r ∈ Fr, ∑ a1 ∈ Finset.range d,
          ‖γ a1 d‖ ^ 2 * ((B.filter (fun s => s % d = (r * a1) % d)).card : ℝ) :=
        Finset.sum_le_sum hstepB
    _ = ∑ a1 ∈ Finset.range d,
          ‖γ a1 d‖ ^ 2 * (∑ r ∈ Fr, ((B.filter (fun s => s % d = (r * a1) % d)).card : ℝ)) := by
        rw [Finset.sum_comm]
        apply Finset.sum_congr rfl; intro a1 ha1
        rw [Finset.mul_sum]
    _ ≤ ∑ a1 ∈ Finset.range d, ‖γ a1 d‖ ^ 2 * K := by
        apply Finset.sum_le_sum; intro a1 ha1
        exact mul_le_mul_of_nonneg_left (hcount a1 ha1) (by positivity)
    _ = K * fbnE γ d := by
        rw [fbnE, Finset.mul_sum]
        apply Finset.sum_congr rfl; intro a1 ha1; rw [mul_comm]

/-! ### the main theorem -/

set_option maxHeartbeats 4000000 in
theorem flat_part_le_unif :
    ∃ C : ℝ, 0 < C ∧ ∀ (S : ℕ) (hS : 1 ≤ S) (f : ℝ → ℝ) (F : ℝ → ℂ) (C₀ : ℝ)
      (hM : Work.FIArea4.BumpData S f F C₀) (D R : ℕ) (γ : ℕ → ℕ → ℂ), 1 ≤ D → 1 ≤ R →
      ‖∑ d1 ∈ Finset.Ioc D (2 * D),
         ∑ d2 ∈ (Finset.Ioc D (2 * D)).filter (fun d2 =>
             Nat.sqrt (Work.FIPlan.oddPart d1 * Work.FIPlan.oddPart d2) ^ 2
               = Work.FIPlan.oddPart d1 * Work.FIPlan.oddPart d2),
          ∑ a ∈ Finset.range (Nat.lcm d1 d2),
            γ (a % d1) d1 * (starRingEnd ℂ) (γ (a % d2) d2) * Work.FIArea4.KK F R d1 d2 a‖
      ≤ C * (((D : ℝ) ^ (-(1 : ℝ) / 2) * (R : ℝ) * (S : ℝ))
              + (D : ℝ) * Real.sqrt ((R : ℝ) * (S : ℝ)))
          * (∑ d ∈ Finset.Ioc D (2 * D), ∑ a ∈ Finset.range d, Complex.normSq (γ a d)) := by
  refine ⟨200, by norm_num, ?_⟩
  intro S hS f F C₀ hM D R γ hD hR
  obtain ⟨h1,h2,h3,h4,h5,h6,h7⟩ := hM
  let A : Finset ℕ := Finset.Ioc D (2 * D)
  let Q : ℕ → ℕ → Prop := fun d1 d2 =>
    Nat.sqrt (Work.FIPlan.oddPart d1 * Work.FIPlan.oddPart d2) ^ 2
      = Work.FIPlan.oddPart d1 * Work.FIPlan.oddPart d2
  obtain ⟨K0, hK0⟩ : ∃ K0 : ℝ, K0 = ((10 * (R * (2*S+2) / D + 4 * min R S + 1) : ℕ) : ℝ) :=
    ⟨_, rfl⟩
  have hK0nn : 0 ≤ K0 := by rw [hK0]; positivity
  have hEs : ∀ d : ℕ, 0 ≤ fbnE γ d := fun d => Finset.sum_nonneg (fun a _ => by positivity)
  -- the per-pair bound
  have hpair : ∀ d1 ∈ A, ∀ d2 ∈ A.filter (Q d1),
      Real.sqrt (fbnP f R (Nat.lcm d1 d2) (d1 * d2) d1 γ)
        * Real.sqrt (fbnP f R (Nat.lcm d1 d2) (d1 * d2) d2 γ)
      ≤ K0 * Real.sqrt (fbnE γ d1 * fbnE γ d2) := by
    intro d1 hd1 d2 hd2
    have hd1i : d1 ∈ Finset.Ioc D (2*D) := hd1
    have hd2i : d2 ∈ Finset.Ioc D (2*D) := (Finset.mem_filter.mp hd2).1
    have hd1ge : 1 ≤ d1 := by have := (Finset.mem_Ioc.mp hd1i).1; omega
    have hd2ge : 1 ≤ d2 := by have := (Finset.mem_Ioc.mp hd2i).1; omega
    have hflat : flatPair d1 d2 := (flatPair_iff_sqrt d1 d2).mpr (Finset.mem_filter.mp hd2).2
    have hq : 0 < Nat.lcm d1 d2 := Nat.lcm_pos (lt_of_lt_of_le (by norm_num) hd1ge)
      (lt_of_lt_of_le (by norm_num) hd2ge)
    have hlcmE : Nat.lcm d1 d2 ∣ d1 * d2 :=
      Nat.lcm_dvd (dvd_mul_right d1 d2) (dvd_mul_left d2 d1)
    have hP1 := fbnP_le hS h1 h2 h3 R (Nat.lcm d1 d2) (d1*d2) d1 γ hR hd1ge hq
      (Nat.dvd_lcm_left d1 d2) hlcmE
    have hP2 := fbnP_le hS h1 h2 h3 R (Nat.lcm d1 d2) (d1*d2) d2 γ hR hd2ge hq
      (Nat.dvd_lcm_right d1 d2) hlcmE
    obtain ⟨K1, hK1def⟩ : ∃ K1 : ℝ,
        K1 = ((10 * (R*(2*S+2)/d1 + min R (2*S+2) + 1) : ℕ) : ℝ) := ⟨_, rfl⟩
    obtain ⟨K2, hK2def⟩ : ∃ K2 : ℝ,
        K2 = ((10 * (R*(2*S+2)/d2 + min R (2*S+2) + 1) : ℕ) : ℝ) := ⟨_, rfl⟩
    have hK1le : K1 ≤ K0 := by
      have hd1lt : D < d1 := (Finset.mem_Ioc.mp hd1i).1
      rw [hK1def, hK0]
      apply Nat.cast_le.mpr
      have hdiv : R * (2*S+2) / d1 ≤ R * (2*S+2) / D :=
        Nat.div_le_div_left (by omega : D ≤ d1) (by omega : 0 < D)
      have hmin : min R (2*S+2) ≤ 4 * min R S := by
        rcases le_total R S with hRS | hRS
        · rw [min_eq_left hRS, min_eq_left (by omega : R ≤ 2*S+2)]; omega
        · rw [min_eq_right hRS]
          have := min_le_right R (2*S+2); omega
      omega
    have hK2le : K2 ≤ K0 := by
      have hd2lt : D < d2 := (Finset.mem_Ioc.mp hd2i).1
      rw [hK2def, hK0]
      apply Nat.cast_le.mpr
      have hdiv : R * (2*S+2) / d2 ≤ R * (2*S+2) / D :=
        Nat.div_le_div_left (by omega : D ≤ d2) (by omega : 0 < D)
      have hmin : min R (2*S+2) ≤ 4 * min R S := by
        rcases le_total R S with hRS | hRS
        · rw [min_eq_left hRS, min_eq_left (by omega : R ≤ 2*S+2)]; omega
        · rw [min_eq_right hRS]
          have := min_le_right R (2*S+2); omega
      omega
    have hK1nn : 0 ≤ K1 := by rw [hK1def]; positivity
    have hK2nn : 0 ≤ K2 := by rw [hK2def]; positivity
    have hfP1 : fbnP f R (Nat.lcm d1 d2) (d1 * d2) d1 γ ≤ K1 * fbnE γ d1 := by
      rw [hK1def]; exact hP1
    have hfP2 : fbnP f R (Nat.lcm d1 d2) (d1 * d2) d2 γ ≤ K2 * fbnE γ d2 := by
      rw [hK2def]; exact hP2
    calc Real.sqrt (fbnP f R (Nat.lcm d1 d2) (d1 * d2) d1 γ)
            * Real.sqrt (fbnP f R (Nat.lcm d1 d2) (d1 * d2) d2 γ)
        ≤ Real.sqrt (K1 * fbnE γ d1) * Real.sqrt (K2 * fbnE γ d2) :=
          mul_le_mul (Real.sqrt_le_sqrt hfP1) (Real.sqrt_le_sqrt hfP2)
            (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)
      _ = Real.sqrt K1 * Real.sqrt (fbnE γ d1) * (Real.sqrt K2 * Real.sqrt (fbnE γ d2)) := by
          rw [Real.sqrt_mul hK1nn (fbnE γ d1), Real.sqrt_mul hK2nn (fbnE γ d2)]
      _ ≤ Real.sqrt K0 * Real.sqrt (fbnE γ d1) * (Real.sqrt K0 * Real.sqrt (fbnE γ d2)) := by
          apply mul_le_mul
          · exact mul_le_mul (Real.sqrt_le_sqrt hK1le) le_rfl (Real.sqrt_nonneg _)
              (Real.sqrt_nonneg _)
          · exact mul_le_mul (Real.sqrt_le_sqrt hK2le) le_rfl (Real.sqrt_nonneg _)
              (Real.sqrt_nonneg _)
          · positivity
          · positivity
      _ = K0 * Real.sqrt (fbnE γ d1 * fbnE γ d2) := by
          rw [show Real.sqrt K0 * Real.sqrt (fbnE γ d1) * (Real.sqrt K0 * Real.sqrt (fbnE γ d2))
              = (Real.sqrt K0 * Real.sqrt K0) * (Real.sqrt (fbnE γ d1) * Real.sqrt (fbnE γ d2))
              by ring,
            Real.mul_self_sqrt hK0nn, ← Real.sqrt_mul (hEs d1) (fbnE γ d2)]
  -- the double sum bound
  have hsplit : ‖∑ d1 ∈ A, ∑ d2 ∈ A.filter (Q d1),
        ∑ a ∈ Finset.range (Nat.lcm d1 d2),
          γ (a % d1) d1 * (starRingEnd ℂ) (γ (a % d2) d2) * KK F R d1 d2 a‖
      ≤ ∑ d1 ∈ A, ∑ d2 ∈ A.filter (Q d1),
          Real.sqrt (fbnP f R (Nat.lcm d1 d2) (d1 * d2) d1 γ)
            * Real.sqrt (fbnP f R (Nat.lcm d1 d2) (d1 * d2) d2 γ) := by
    refine (norm_sum_le _ _).trans (Finset.sum_le_sum (fun d1 hd1 => ?_))
    refine (norm_sum_le _ _).trans (Finset.sum_le_sum (fun d2 hd2 => ?_))
    have hd1i : d1 ∈ Finset.Ioc D (2*D) := hd1
    have hd2i : d2 ∈ Finset.Ioc D (2*D) := (Finset.mem_filter.mp hd2).1
    have hd1ge : 1 ≤ d1 := by have := (Finset.mem_Ioc.mp hd1i).1; omega
    have hd2ge : 1 ≤ d2 := by have := (Finset.mem_Ioc.mp hd2i).1; omega
    have hflat : flatPair d1 d2 := (flatPair_iff_sqrt d1 d2).mpr (Finset.mem_filter.mp hd2).2
    exact fbn_pair_le hS ⟨h1,h2,h3,h4,h5,h6,h7⟩ R d1 d2 γ hd1ge hd2ge hflat
  rw [show (∑ d ∈ A, ∑ a ∈ Finset.range d, Complex.normSq (γ a d)) = ∑ d ∈ A, fbnE γ d from by
    apply Finset.sum_congr rfl; intro d hd
    rw [fbnE]
    apply Finset.sum_congr rfl; intro a ha
    rw [Complex.normSq_eq_norm_sq]]
  calc ‖∑ d1 ∈ A, ∑ d2 ∈ A.filter (Q d1),
        ∑ a ∈ Finset.range (Nat.lcm d1 d2),
          γ (a % d1) d1 * (starRingEnd ℂ) (γ (a % d2) d2) * KK F R d1 d2 a‖
      ≤ ∑ d1 ∈ A, ∑ d2 ∈ A.filter (Q d1),
          Real.sqrt (fbnP f R (Nat.lcm d1 d2) (d1 * d2) d1 γ)
            * Real.sqrt (fbnP f R (Nat.lcm d1 d2) (d1 * d2) d2 γ) := hsplit
    _ ≤ ∑ d1 ∈ A, ∑ d2 ∈ A.filter (Q d1), K0 * Real.sqrt (fbnE γ d1 * fbnE γ d2) :=
        Finset.sum_le_sum (fun d1 hd1 => Finset.sum_le_sum (fun d2 hd2 => hpair d1 hd1 d2 hd2))
    _ = K0 * ∑ d1 ∈ A, ∑ d2 ∈ A.filter (Q d1), Real.sqrt (fbnE γ d1 * fbnE γ d2) := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl; intro d1 hd1
        rw [Finset.mul_sum]
    _ ≤ K0 * (Real.sqrt (2*D) * ∑ d ∈ A, fbnE γ d) := by
        apply mul_le_mul_of_nonneg_left ?_ hK0nn
        simpa only [A, Q] using flat_pair_sum_le D hD (fbnE γ) hEs
    _ = (K0 * Real.sqrt (2*D)) * ∑ d ∈ A, fbnE γ d := by ring
    _ ≤ (200 * ((D:ℝ)^(-(1:ℝ)/2) * (R:ℝ) * (S:ℝ)
            + (D:ℝ) * Real.sqrt ((R:ℝ) * (S:ℝ)))) * ∑ d ∈ A, fbnE γ d :=
        mul_le_mul_of_nonneg_right (by rw [hK0]; exact flat_numeric D R S hD hR hS)
          (Finset.sum_nonneg (fun d _ => hEs d))
    _ = 200 * ((D:ℝ)^(-(1:ℝ)/2) * (R:ℝ) * (S:ℝ)
            + (D:ℝ) * Real.sqrt ((R:ℝ) * (S:ℝ))) * ∑ d ∈ A, fbnE γ d := by ring

end
end Work.FIArea4
