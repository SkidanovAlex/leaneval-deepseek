import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.Data.Int.Star
import Submission.Commons.NumberTheory.DivisorBound.card_divisors_le_rpow
import Submission.Commons.Analysis.ExponentialSums.hua_bound
import Submission.Commons.Analysis.ExponentialSums.iterated_differencing_step
import Submission.Commons.Algebra.Polynomial.signed_sum_pow_lower

set_option maxHeartbeats 0

open Finset
open scoped BigOperators Topology ComplexConjugate Polynomial
open Polynomial
open Commons.Algebra.Polynomial

namespace Commons.Analysis.ExponentialSums

namespace WeylAux
noncomputable def dz (x : ℝ) : ℝ := |x - (round x : ℝ)|

lemma dz_le_half (x : ℝ) : dz x ≤ 1/2 := abs_sub_round x
lemma dz_eq_abs (x : ℝ) : dz x = |x - (round x : ℝ)| := rfl

lemma dz_add_intCast (t : ℝ) (z : ℤ) : dz ((z:ℝ) + t) = dz t := by
  unfold dz
  rw [add_comm ((z:ℝ)) t, round_add_intCast]
  congr 1; push_cast; ring

lemma one_div_le_dz_div (Q : ℕ) (hQ : 1 ≤ Q) (a : ℤ) (h : ¬ ((Q:ℤ) ∣ a)) :
    1/(Q:ℝ) ≤ dz ((a:ℝ)/(Q:ℝ)) := by
  have hQpos : (0:ℝ) < Q := by exact_mod_cast hQ
  have hQz : (0:ℤ) < Q := by exact_mod_cast hQ
  set r : ℤ := a % (Q:ℤ) with hr
  have hr0 : 0 ≤ r := Int.emod_nonneg a (ne_of_gt hQz)
  have hrQ : r < (Q:ℤ) := Int.emod_lt_of_pos a hQz
  have hrne : r ≠ 0 := by
    intro h0; apply h; rw [Int.dvd_iff_emod_eq_zero]; exact h0
  have hr1 : 1 ≤ r := by omega
  have hdecR : (a:ℝ) = (Q:ℝ)*((a/(Q:ℤ):ℤ):ℝ) + (r:ℝ) := by
    have hdec := Int.mul_ediv_add_emod a (Q:ℤ)
    rw [← hr] at hdec
    have h2 := congrArg (fun z : ℤ => (z:ℝ)) hdec
    push_cast at h2
    exact h2.symm
  have hcast : (a:ℝ)/(Q:ℝ) = ((a/(Q:ℤ):ℤ):ℝ) + (r:ℝ)/(Q:ℝ) := by
    have hQR : (Q:ℝ) ≠ 0 := by positivity
    rw [div_eq_iff hQR]; rw [hdecR]; field_simp
  rw [hcast, dz_add_intCast]
  have hrQR0 : (0:ℝ) < (r:ℝ)/(Q:ℝ) := by
    apply div_pos; exact_mod_cast hr1; exact hQpos
  have hrQR1 : (r:ℝ)/(Q:ℝ) < 1 := by
    rw [div_lt_one hQpos]; exact_mod_cast hrQ
  have hconv : dz ((r:ℝ)/(Q:ℝ)) = min ((r:ℝ)/(Q:ℝ)) (1 - (r:ℝ)/(Q:ℝ)) := by
    unfold dz
    rw [abs_sub_round_eq_min, Int.fract_eq_self.mpr ⟨le_of_lt hrQR0, hrQR1⟩]
  rw [hconv]
  apply le_min
  · exact div_le_div_of_nonneg_right (by exact_mod_cast hr1) (le_of_lt hQpos)
  · rw [le_sub_iff_add_le, ← add_div, div_le_one hQpos]
    exact_mod_cast (by omega : 1 + r ≤ (Q:ℤ))

lemma not_dvd_mul (Q : ℕ) (hQ : 1 ≤ Q) (b : ℤ) (hcop : Int.gcd b (Q:ℤ) = 1)
    (h : ℤ) (hh0 : h ≠ 0) (hhQ : |h| < (Q:ℤ)) : ¬ ((Q:ℤ) ∣ h * b) := by
  intro hd
  have hgcd : (Q:ℤ).gcd b = 1 := by rw [Int.gcd_comm]; exact hcop
  have hQh : (Q:ℤ) ∣ h := Int.dvd_of_dvd_mul_left_of_gcd_one hd hgcd
  rcases hQh with ⟨k, hk⟩
  have hQpos : (0:ℤ) < Q := by exact_mod_cast hQ
  have habs : |h| = (Q:ℤ) * |k| := by
    rw [hk, abs_mul]; rw [abs_of_nonneg (by positivity : (0:ℤ) ≤ (Q:ℤ))]
  have hk0 : k = 0 := by
    have h1 : (Q:ℤ) * |k| < (Q:ℤ) := by linarith [habs, hhQ]
    have h2 : |k| < 1 := by nlinarith [hQpos, abs_nonneg k]
    exact Int.abs_lt_one_iff.mp h2
  rw [hk, hk0] at hh0; simp at hh0



-- separation of {m α}
lemma sep' (Q : ℕ) (hQ : 1 ≤ Q) (b : ℤ) (hcop : Int.gcd b (Q:ℤ) = 1)
    (α : ℝ) (K : ℝ) (hK : 1 ≤ K) (hb : |α - (b:ℝ)/(Q:ℝ)| ≤ K/(Q:ℝ)^2)
    (h : ℤ) (hh0 : h ≠ 0) (hhQ : (|h|:ℝ) < (Q:ℝ)/(2*K)) :
    1/(2*(Q:ℝ)) ≤ dz ((h:ℝ)*α) := by
  have hQpos : (0:ℝ) < Q := by exact_mod_cast hQ
  have hKpos : 0 < K := lt_of_lt_of_le zero_lt_one hK
  have hhQZ : (|h|:ℤ) < (Q:ℤ) := by
    have h2 : (|h|:ℝ) < (Q:ℝ) := by
      refine lt_of_lt_of_le hhQ ?_
      rw [div_le_iff₀ (by positivity)]; nlinarith [hKpos, hQpos]
    exact_mod_cast h2
  have hdzb : 1/(Q:ℝ) ≤ dz ((h:ℝ)*(b:ℝ)/(Q:ℝ)) := by
    have hnotdvd : ¬ ((Q:ℤ) ∣ h * b) := not_dvd_mul Q hQ b hcop h hh0 hhQZ
    rw [show (h:ℝ)*(b:ℝ)/(Q:ℝ) = (((h*b):ℤ):ℝ)/(Q:ℝ) by push_cast; ring]
    exact one_div_le_dz_div Q hQ (h*b) hnotdvd
  have hdiff : |(h:ℝ)*α - (h:ℝ)*(b:ℝ)/(Q:ℝ)| ≤ 1/(2*Q) := by
    rw [show (h:ℝ)*α - (h:ℝ)*(b:ℝ)/(Q:ℝ) = (h:ℝ)*(α - (b:ℝ)/(Q:ℝ)) by ring,
        abs_mul]
    exact le_of_lt (calc (|h|:ℝ) * |α - (b:ℝ)/(Q:ℝ)| ≤ (|h|:ℝ) * (K/(Q:ℝ)^2) :=
          mul_le_mul_of_nonneg_left hb (abs_nonneg _)
      _ < ((Q:ℝ)/(2*K)) * (K/(Q:ℝ)^2) := by
          apply mul_lt_mul_of_pos_right hhQ; positivity
      _ = 1/(2*Q) := by field_simp)
  have key : dz ((h:ℝ)*(b:ℝ)/(Q:ℝ)) ≤ |(h:ℝ)*(b:ℝ)/(Q:ℝ) - (h:ℝ)*α| + dz ((h:ℝ)*α) := by
    have h1 : |(h:ℝ)*(b:ℝ)/(Q:ℝ) - (round ((h:ℝ)*(b:ℝ)/(Q:ℝ)):ℤ)| ≤
              |(h:ℝ)*(b:ℝ)/(Q:ℝ) - (round ((h:ℝ)*α):ℤ)| := round_le _ _
    calc dz ((h:ℝ)*(b:ℝ)/(Q:ℝ))
        = |(h:ℝ)*(b:ℝ)/(Q:ℝ) - (round ((h:ℝ)*(b:ℝ)/(Q:ℝ)):ℤ)| := rfl
      _ ≤ |(h:ℝ)*(b:ℝ)/(Q:ℝ) - (round ((h:ℝ)*α):ℤ)| := h1
      _ ≤ |(h:ℝ)*(b:ℝ)/(Q:ℝ) - (h:ℝ)*α| + |(h:ℝ)*α - (round ((h:ℝ)*α):ℤ)| := by
            rw [show (h:ℝ)*(b:ℝ)/(Q:ℝ) - (round ((h:ℝ)*α):ℤ)
                  = ((h:ℝ)*(b:ℝ)/(Q:ℝ) - (h:ℝ)*α) + ((h:ℝ)*α - (round ((h:ℝ)*α):ℤ)) by ring]
            exact abs_add_le _ _
      _ = |(h:ℝ)*(b:ℝ)/(Q:ℝ) - (h:ℝ)*α| + dz ((h:ℝ)*α) := rfl
  have hsym : |(h:ℝ)*(b:ℝ)/(Q:ℝ) - (h:ℝ)*α| = |(h:ℝ)*α - (h:ℝ)*(b:ℝ)/(Q:ℝ)| := abs_sub_comm _ _
  have hsplit : 1/(Q:ℝ) - 1/(2*Q) = 1/(2*Q) := by ring
  linarith [hdzb, hdiff, key, hsym, hsplit]



lemma card_le_of_sep {ι : Type*} (s : Finset ι) (p : ι → ℝ) {δ L : ℝ} (hδ : 0 < δ)
    (hL : 0 ≤ L)
    (hsep : ∀ a ∈ s, ∀ b ∈ s, a ≠ b → δ ≤ |p a - p b|)
    (hlo : ∀ a ∈ s, 0 ≤ p a) (hhi : ∀ a ∈ s, p a ≤ L) :
    (s.card : ℝ) ≤ L/δ + 1 := by
  have hinj : Set.InjOn (fun a => ⌊p a / δ⌋) s := by
    intro a ha b hb heq
    simp only at heq
    by_contra hne
    have hs := hsep a ha b hb hne
    have ha1 : (⌊p a / δ⌋ : ℝ) ≤ p a / δ := Int.floor_le _
    have ha2 : p a / δ < (⌊p a / δ⌋ : ℝ) + 1 := Int.lt_floor_add_one _
    have hb1 : (⌊p b / δ⌋ : ℝ) ≤ p b / δ := Int.floor_le _
    have hb2 : p b / δ < (⌊p b / δ⌋ : ℝ) + 1 := Int.lt_floor_add_one _
    rw [heq] at ha1 ha2
    have hlt : |p a - p b| < δ := by
      rw [le_div_iff₀ hδ] at ha1 hb1
      rw [div_lt_iff₀ hδ] at ha2 hb2
      rw [abs_lt]
      constructor <;> nlinarith
    linarith
  have himg : s.image (fun a => ⌊p a / δ⌋) ⊆ Finset.Icc 0 ⌊L/δ⌋ := by
    intro z hz
    rw [Finset.mem_image] at hz
    obtain ⟨a, ha, rfl⟩ := hz
    rw [Finset.mem_Icc]
    refine ⟨?_, ?_⟩
    · rw [Int.le_floor, Int.cast_zero]; exact div_nonneg (hlo a ha) (le_of_lt hδ)
    · exact Int.floor_le_floor (div_le_div_of_nonneg_right (hhi a ha) (le_of_lt hδ))
  have hcard := Finset.card_le_card himg
  have h2 : ((Finset.Icc (0:ℤ) ⌊L/δ⌋).card : ℝ) = ⌊L/δ⌋ + 1 := by
    have h0 : (0:ℤ) ≤ ⌊L/δ⌋ := Int.le_floor.mpr (by rw [Int.cast_zero]; exact div_nonneg hL (le_of_lt hδ))
    have h := Int.card_Icc_of_le (a := (0:ℤ)) (b := ⌊L/δ⌋) (by linarith)
    have h3 := congrArg (fun z : ℤ => (z:ℝ)) h
    push_cast at h3
    rw [h3]; push_cast; ring
  calc (s.card : ℝ) = ((s.image (fun a => ⌊p a / δ⌋)).card : ℝ) := by
        rw [Finset.card_image_of_injOn hinj]
    _ ≤ ((Finset.Icc (0:ℤ) ⌊L/δ⌋).card : ℝ) := by exact_mod_cast hcard
    _ = ⌊L/δ⌋ + 1 := h2
    _ ≤ L/δ + 1 := by linarith [Int.floor_le (L/δ)]



lemma Ncount_le (Q : ℕ) (hQ : 1 ≤ Q) (bc : ℤ) (hcop : Int.gcd bc (Q:ℤ) = 1)
    (α : ℝ) (K : ℝ) (hK : 1 ≤ K) (hb : |α - (bc:ℝ)/(Q:ℝ)| ≤ K/(Q:ℝ)^2)
    (H : ℕ) (hH : (H:ℝ) ≤ (Q:ℝ)/(2*K)) (η : ℝ) (hη : 0 ≤ η) :
    (((Finset.Icc 1 H).filter (fun (m:ℕ) => dz ((m:ℝ)*α) ≤ η)).card : ℝ) ≤ 4*η*Q + 2 := by
  have hQpos : (0:ℝ) < Q := by exact_mod_cast hQ
  have hKpos : 0 < K := lt_of_lt_of_le zero_lt_one hK
  have key := card_le_of_sep ((Finset.Icc 1 H).filter (fun (m:ℕ) => dz ((m:ℝ)*α) ≤ η))
      (fun (m:ℕ) => ((m:ℝ)*α - (round ((m:ℝ)*α):ℝ)) + η)
      (δ := 1/(2*(Q:ℝ))) (L := 2*η) (by positivity) (by linarith)
      ?_ ?_ ?_
  · calc (((Finset.Icc 1 H).filter (fun (m:ℕ) => dz ((m:ℝ)*α) ≤ η)).card : ℝ)
        ≤ 2*η/(1/(2*(Q:ℝ))) + 1 := key
      _ = 4*η*Q + 1 := by field_simp; ring
      _ ≤ 4*η*Q + 2 := by linarith
  · intro a ha c hc hac
    simp only [Finset.mem_filter] at ha hc
    have haI := ha.1; have hcI := hc.1
    have ha1 : 1 ≤ a := (Finset.mem_Icc.mp haI).1
    have hc1 : 1 ≤ c := (Finset.mem_Icc.mp hcI).1
    have haH : (a:ℤ) ≤ H := by exact_mod_cast (Finset.mem_Icc.mp haI).2
    have hcH : (c:ℤ) ≤ H := by exact_mod_cast (Finset.mem_Icc.mp hcI).2
    have hne : (a:ℤ) - c ≠ 0 := by
      intro h0
      apply hac
      have : (a:ℤ) = c := by omega
      omega
    have h1conv : (((a:ℤ)-c:ℤ):ℝ) = (a:ℝ) - (c:ℝ) := by push_cast; ring
    have habslt : |((((a:ℤ)-c:ℤ)):ℝ)| < (Q:ℝ)/(2*K) := by
      have h1 : |(a:ℤ)-c| ≤ (H:ℤ) - 1 := by
        rw [abs_le]; constructor <;> omega
      rw [h1conv]
      have h2 : |(a:ℝ) - (c:ℝ)| ≤ (H:ℝ) - 1 := by
        have h2' : (((|((a:ℤ)-c)|:ℤ)):ℝ) ≤ (H:ℝ) - 1 := by exact_mod_cast h1
        rw [Int.cast_abs] at h2'
        rw [h1conv] at h2'
        exact h2'
      have h4 : (H:ℝ) - 1 < (Q:ℝ)/(2*K) := by linarith
      linarith [h2, h4]
    have hs := sep' Q hQ bc hcop α K hK hb ((a:ℤ)-c) hne habslt
    have hs2 : 1/(2*(Q:ℝ)) ≤ dz ((a:ℝ)*α - (c:ℝ)*α) := by
      rw [show (a:ℝ)*α - (c:ℝ)*α = ((((a:ℤ)-c:ℤ):ℝ))*α by rw [h1conv]; ring]
      exact hs
    have hrel : dz ((a:ℝ)*α - (c:ℝ)*α) ≤
        |(((a:ℝ)*α - (round ((a:ℝ)*α):ℝ)) + η) - (((c:ℝ)*α - (round ((c:ℝ)*α):ℝ)) + η)| := by
      have hr := round_le ((a:ℝ)*α - (c:ℝ)*α) ((round ((a:ℝ)*α)) - (round ((c:ℝ)*α)))
      have heq : ((a:ℝ)*α - (c:ℝ)*α) - (((round ((a:ℝ)*α)) - (round ((c:ℝ)*α)) : ℤ):ℝ)
          = (((a:ℝ)*α - (round ((a:ℝ)*α):ℝ)) + η) - (((c:ℝ)*α - (round ((c:ℝ)*α):ℝ)) + η) := by
        push_cast; ring
      calc dz ((a:ℝ)*α - (c:ℝ)*α)
          = abs (((a:ℝ)*α - (c:ℝ)*α) - (round ((a:ℝ)*α - (c:ℝ)*α):ℤ)) := rfl
        _ ≤ abs (((a:ℝ)*α - (c:ℝ)*α) - (((round ((a:ℝ)*α)) - (round ((c:ℝ)*α)) : ℤ):ℝ)) := hr
        _ = _ := by rw [heq]
    exact le_trans hs2 hrel
  · intro m hm
    simp only [Finset.mem_filter] at hm
    have hdm : dz ((m:ℝ)*α) ≤ η := hm.2
    have habs : |(m:ℝ)*α - (round ((m:ℝ)*α):ℝ)| ≤ η := hdm
    rw [abs_le] at habs
    linarith [habs.1]
  · intro m hm
    simp only [Finset.mem_filter] at hm
    have hdm : dz ((m:ℝ)*α) ≤ η := hm.2
    have habs : |(m:ℝ)*α - (round ((m:ℝ)*α):ℝ)| ≤ η := hdm
    rw [abs_le] at habs
    linarith [habs.2]


noncomputable def pe (x : ℝ) : ℂ := Complex.exp (((2 * Real.pi * x : ℝ) : ℂ) * Complex.I)
noncomputable def FK (K : ℕ) (x : ℝ) : ℝ := (1/(K:ℝ)) * ‖∑ j ∈ Finset.range K, pe ((j:ℝ)*x)‖^2

lemma pe_norm (x : ℝ) : ‖pe x‖ = 1 := by unfold pe; rw [Complex.norm_exp_ofReal_mul_I]
lemma pe_add (x y : ℝ) : pe (x + y) = pe x * pe y := by
  unfold pe; rw [← Complex.exp_add]; congr 1; push_cast; ring
lemma pe_nat (n : ℕ) (x : ℝ) : pe ((n:ℝ) * x) = pe x ^ n := by
  unfold pe
  rw [show (((2 * Real.pi * ((n:ℝ)*x)) : ℝ) : ℂ) * Complex.I
        = (n:ℂ) * (((2*Real.pi*x : ℝ):ℂ) * Complex.I) by push_cast; ring]
  rw [Complex.exp_nat_mul]
lemma pe_conj (x : ℝ) : (starRingEnd ℂ) (pe x) = pe (-x) := by
  unfold pe; rw [← Complex.exp_conj]; congr 1
  rw [map_mul, Complex.conj_I, Complex.conj_ofReal]; push_cast; ring
lemma pe_mul_sub (a b : ℝ) : pe a * (starRingEnd ℂ) (pe b) = pe (a - b) := by
  rw [pe_conj, ← pe_add, sub_eq_add_neg]
lemma norm_pe_sub_one (t : ℝ) : ‖pe t - 1‖ = 2 * |Real.sin (Real.pi * t)| := by
  unfold pe
  rw [show (((2*Real.pi*t:ℝ):ℂ) * Complex.I) = Complex.I * ((2*Real.pi*t:ℝ):ℂ) by ring]
  rw [Complex.norm_exp_I_mul_ofReal_sub_one]
  rw [show 2*Real.pi*t/2 = Real.pi*t by ring, Real.norm_eq_abs, abs_mul]; norm_num

lemma abs_sin_pi_eq (x : ℝ) :
    |Real.sin (Real.pi*x)| = Real.sin (Real.pi * |x - (round x:ℝ)|) := by
  set u : ℝ := x - (round x:ℝ) with hu
  have hsplit : Real.pi*x = Real.pi*u + (round x:ℝ)*Real.pi := by rw [hu]; ring
  rw [hsplit, Real.sin_add_int_mul_pi, abs_mul]
  have h1 : |(-1:ℝ)^(round x)| = 1 := by rw [abs_zpow]; simp
  rw [h1, one_mul, Real.abs_sin_eq_sin_abs_of_abs_le_pi]
  · rw [abs_mul, abs_of_pos Real.pi_pos]
  · rw [abs_mul, abs_of_pos Real.pi_pos]
    have := dz_le_half x; rw [dz_eq_abs, ← hu] at this; nlinarith [this, Real.pi_pos]

lemma dz_le_half' (x : ℝ) : dz x ≤ 1/2 := abs_sub_round x

-- four dz ≤ |pe t - 1|
lemma four_dz_le (t : ℝ) : 4 * dz t ≤ ‖pe t - 1‖ := by
  rw [norm_pe_sub_one, abs_sin_pi_eq, dz_eq_abs]
  set u : ℝ := t - (round t:ℝ) with hu
  have hle : |u| ≤ 1/2 := by rw [hu]; exact dz_le_half t
  have h1 : Real.pi * |u| ≤ Real.pi/2 := by nlinarith [hle, Real.pi_pos]
  have h2 := Real.mul_le_sin (x := Real.pi*|u|) (by positivity) h1
  have he : (2/Real.pi)*(Real.pi*|u|) = 2*|u| := by field_simp
  rw [hu]; linarith [h2, he]

lemma pe_eq_one_imp_dz_zero (t : ℝ) (h : pe t = 1) : dz t = 0 := by
  have hnorm : ‖pe t - 1‖ = 0 := by rw [h]; simp
  rw [norm_pe_sub_one] at hnorm
  have hsin : Real.sin (Real.pi*t) = 0 := by
    have h0 : |Real.sin (Real.pi*t)| = 0 := by linarith
    exact abs_eq_zero.mp h0
  rw [Real.sin_eq_zero_iff] at hsin
  obtain ⟨m, hm⟩ := hsin
  have ht : t = (m:ℝ) := by
    have hp : Real.pi ≠ 0 := Real.pi_ne_zero
    have : Real.pi * t = Real.pi * (m:ℝ) := by rw [← hm]; ring
    exact mul_left_cancel₀ hp this
  rw [dz, ht, round_intCast]; simp

-- geometric sum bound (dz > 0)
lemma geom_le_pos (m R : ℕ) (α : ℝ) (hz : 0 < dz ((m:ℝ)*α)) :
    ‖∑ n ∈ Finset.Icc 1 R, pe (((m:ℝ)*(n:ℝ))*α)‖ ≤ min (R:ℝ) (1/(2*dz ((m:ℝ)*α))) := by
  have hterm : ∀ n : ℕ, pe (((m:ℝ)*(n:ℝ))*α) = (pe ((m:ℝ)*α))^n := by
    intro n
    rw [show (((m:ℝ)*(n:ℝ))*α) = (n:ℝ)*((m:ℝ)*α) by ring, pe_nat]
  rw [Finset.sum_congr rfl (fun n _ => hterm n)]
  refine le_min ?_ ?_
  · calc ‖∑ n ∈ Finset.Icc 1 R, (pe ((m:ℝ)*α))^n‖
        ≤ ∑ n ∈ Finset.Icc 1 R, ‖(pe ((m:ℝ)*α))^n‖ := norm_sum_le _ _
      _ = ∑ n ∈ Finset.Icc 1 R, (1:ℝ) := by
            apply Finset.sum_congr rfl; intro n _
            rw [norm_pow, pe_norm, one_pow]
      _ = R := by rw [Finset.sum_const, Nat.card_Icc]; simp
  · have hzne : pe ((m:ℝ)*α) ≠ 1 := fun h => by
      have := pe_eq_one_imp_dz_zero ((m:ℝ)*α) h; linarith
    have hre : (∑ n ∈ Finset.Icc 1 R, (pe ((m:ℝ)*α))^n)
        = pe ((m:ℝ)*α) * ∑ j ∈ Finset.range R, (pe ((m:ℝ)*α))^j := by
      rw [show Finset.Icc 1 R = Finset.Ico 1 (R+1) by
        ext n; simp only [Finset.mem_Icc, Finset.mem_Ico]; omega]
      rw [Finset.sum_Ico_eq_sum_range, Nat.add_sub_cancel]
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl; intro j _
      rw [show 1+j = j+1 by omega, pow_succ]; ring
    rw [hre, geom_sum_eq hzne R]
    rw [norm_mul, norm_div, pe_norm, one_mul]
    have hnum : ‖(pe ((m:ℝ)*α))^R - 1‖ ≤ 2 := by
      calc ‖(pe ((m:ℝ)*α))^R - 1‖ ≤ ‖(pe ((m:ℝ)*α))^R‖ + ‖(1:ℂ)‖ := norm_sub_le _ _
        _ = 2 := by rw [norm_pow, pe_norm, one_pow]; norm_num
    have hden : 4 * dz ((m:ℝ)*α) ≤ ‖pe ((m:ℝ)*α) - 1‖ := four_dz_le _
    have hdenpos : 0 < ‖pe ((m:ℝ)*α) - 1‖ := lt_of_lt_of_le (by linarith) hden
    rw [div_le_div_iff₀ hdenpos (by positivity)]
    nlinarith [hnum, hden]


lemma FK_nonneg (K : ℕ) (x : ℝ) : 0 ≤ FK K x := by unfold FK; positivity

lemma sin_pi_le (x : ℝ) : |Real.sin (Real.pi*x)| ≤ Real.pi * |x - (round x:ℝ)| := by
  rw [abs_sin_pi_eq]
  have h := Real.sin_le (x := Real.pi * |x - (round x:ℝ)|) (by positivity)
  nlinarith [h]

lemma abs_sin_pi_nat_mul_shift (n : ℕ) (x : ℝ) :
    Real.sin (Real.pi*((n:ℝ)*x)) =
      (-1 : ℝ)^((n:ℤ)*(round x)) * Real.sin (Real.pi*((n:ℝ)*(x - (round x:ℝ)))) := by
  have h : Real.pi*((n:ℝ)*x) = Real.pi*((n:ℝ)*(x - (round x:ℝ))) + (((n:ℤ)*(round x):ℤ):ℝ)*Real.pi := by
    rw [show x = (x - (round x:ℝ)) + (round x:ℝ) by ring]
    push_cast; ring
  rw [h, Real.sin_add_int_mul_pi]

lemma abs_sin_pi_nat_mul_ge (n : ℕ) (hn : 1 ≤ n) (x : ℝ)
    (hx : |x - (round x:ℝ)| ≤ 1/(2*n)) :
    2*(n:ℝ)*|x - (round x:ℝ)| ≤ |Real.sin (Real.pi*((n:ℝ)*x))| := by
  set u : ℝ := x - (round x:ℝ) with hu
  have hu1 : |u| ≤ 1/(2*n) := hx
  have hmain : Real.pi*((n:ℝ)*x) = Real.pi*((n:ℝ)*u) + (((n:ℤ)*(round x):ℤ):ℝ)*Real.pi := by
    have hxu : (n:ℝ)*x = (n:ℝ)*u + (n:ℝ)*(round x:ℝ) := by rw [hu]; ring
    calc Real.pi*((n:ℝ)*x) = Real.pi*((n:ℝ)*u + (n:ℝ)*(round x:ℝ)) := by rw [hxu]
      _ = Real.pi*((n:ℝ)*u) + (((n:ℤ)*(round x):ℤ):ℝ)*Real.pi := by push_cast; ring
  rw [hmain, Real.sin_add_int_mul_pi, abs_mul]
  have h1 : |(-1:ℝ)^((n:ℤ)*(round x))| = 1 := by rw [abs_zpow]; simp
  rw [h1, one_mul]
  have hnu : (n:ℝ)*|u| ≤ 1/2 := by
    have h := mul_le_mul_of_nonneg_left hu1 (Nat.cast_nonneg n)
    have h2 : (n:ℝ) * (1/(2*(n:ℝ))) = 1/2 := by
      rw [one_div, mul_inv_eq_iff_eq_mul₀ (by positivity)]; ring
    rwa [h2] at h
  have habs : |Real.sin (Real.pi*((n:ℝ)*u))| = Real.sin (Real.pi*((n:ℝ)*|u|)) := by
    rw [Real.abs_sin_eq_sin_abs_of_abs_le_pi]
    · rw [abs_mul, abs_mul, abs_of_pos Real.pi_pos, abs_of_nonneg (Nat.cast_nonneg n)]
    · rw [abs_mul, abs_of_pos Real.pi_pos, abs_mul, abs_of_nonneg (Nat.cast_nonneg n)]
      nlinarith [hnu, Real.pi_pos]
  rw [habs]
  have hj := Real.mul_le_sin (x := Real.pi*((n:ℝ)*|u|)) (by positivity) (by nlinarith [hnu, Real.pi_pos])
  have he : (2/Real.pi)*(Real.pi*((n:ℝ)*|u|)) = 2*((n:ℝ)*|u|) := by field_simp
  linarith [hj, he]

lemma norm_geom_pe (K : ℕ) (x : ℝ) (h : pe x ≠ 1) :
    ‖∑ j ∈ Finset.range K, pe ((j:ℝ)*x)‖ = |Real.sin (Real.pi*((K:ℝ)*x))| / |Real.sin (Real.pi*x)| := by
  have hgeom := geom_sum_eq h K
  have hpow : ∀ j ∈ Finset.range K, pe ((j:ℝ)*x) = (pe x)^j := fun j _ => pe_nat j x
  rw [Finset.sum_congr rfl hpow, hgeom, norm_div]
  rw [show (pe x)^K = pe ((K:ℝ)*x) by rw [pe_nat]]
  rw [norm_pe_sub_one, norm_pe_sub_one]
  rw [mul_div_mul_left _ _ (by norm_num : (2:ℝ) ≠ 0)]

lemma FK_lower (K : ℕ) (hK : 1 ≤ K) (x : ℝ) (hx : dz x ≤ 1/(2*K)) :
    (4/Real.pi^2) * K ≤ FK K x := by
  have hKpos : (0:ℝ) < K := by exact_mod_cast hK
  have hK1 : (1:ℝ) ≤ K := by exact_mod_cast hK
  by_cases h1 : pe x = 1
  · unfold FK
    have hsum : (∑ j ∈ Finset.range K, pe ((j:ℝ)*x)) = (K:ℂ) := by
      have : ∀ j ∈ Finset.range K, pe ((j:ℝ)*x) = 1 := by
        intro j _; rw [pe_nat, h1, one_pow]
      rw [Finset.sum_congr rfl this, Finset.sum_const, Finset.card_range]; simp
    rw [hsum, show ‖(K:ℂ)‖ = (K:ℝ) by simp]
    have hpi2 : (4:ℝ) ≤ Real.pi^2 := by nlinarith [Real.pi_gt_three]
    have hle1 : (4:ℝ)/Real.pi^2 ≤ 1 := by
      rw [div_le_one (by positivity)]; exact hpi2
    have hKsq : (1/(K:ℝ)) * (K:ℝ)^2 = (K:ℝ) := by
      rw [pow_two, ← mul_assoc, one_div, inv_mul_cancel₀ (ne_of_gt hKpos)]; ring
    rw [hKsq]
    exact mul_le_of_le_one_left (le_of_lt hKpos) hle1
  · unfold FK
    rw [norm_geom_pe K x h1]
    set u : ℝ := x - (round x:ℝ) with hu
    have hzu : dz x = |u| := by rw [dz_eq_abs, hu]
    have hu1 : |u| ≤ 1/(2*K) := by rw [← hzu]; exact hx
    have hu0 : 0 < |u| := by
      rcases eq_or_lt_of_le (abs_nonneg u) with hh | hh
      · exfalso; apply h1
        have hxr : x = (round x : ℝ) := by
          rw [hu] at hh; linarith [abs_eq_zero.mp hh.symm]
        rw [hxr]; unfold pe
        rw [show (((2*Real.pi*((round x:ℤ):ℝ)):ℝ):ℂ)*Complex.I
              = ((round x:ℤ):ℂ)*(2*(Real.pi:ℂ)*Complex.I) by push_cast; ring]
        rw [Complex.exp_int_mul, Complex.exp_two_pi_mul_I]; simp
      · exact hh
    have hsin_pos : 0 < |Real.sin (Real.pi*x)| := by
      rw [abs_sin_pi_eq]
      apply Real.sin_pos_of_pos_of_lt_pi
      · have : 0 < |x - (round x:ℝ)| := by rw [← hu]; exact hu0
        positivity
      · have h2 : |x - (round x:ℝ)| ≤ 1/(2*K) := by rw [← dz_eq_abs]; exact hx
        have h3 : (1:ℝ)/(2*K) ≤ 1/2 := by
          rw [div_le_iff₀ (by positivity)]; linarith [hK1]
        nlinarith [h2, h3, Real.pi_pos]
    have hKx : 2*(K:ℝ)*|u| ≤ |Real.sin (Real.pi*((K:ℝ)*x))| := by
      have h := abs_sin_pi_nat_mul_ge K hK x (by rw [← hu]; rw [← hzu]; exact hx)
      rwa [← hu] at h
    have hxle : |Real.sin (Real.pi*x)| ≤ Real.pi*|u| := by
      have h := sin_pi_le x; rwa [← hu] at h
    have hratio : 2*(K:ℝ)/Real.pi ≤ |Real.sin (Real.pi*((K:ℝ)*x))| / |Real.sin (Real.pi*x)| := by
      rw [le_div_iff₀ hsin_pos]
      have h2 : (2*(K:ℝ)/Real.pi)*(Real.pi*|u|) = 2*(K:ℝ)*|u| := by field_simp
      nlinarith [mul_le_mul_of_nonneg_left hxle (by positivity : 0 ≤ 2*(K:ℝ)/Real.pi), hKx, h2]
    have hr_nonneg : 0 ≤ 2*(K:ℝ)/Real.pi := by positivity
    have hsq := pow_le_pow_left₀ hr_nonneg hratio 2
    have hfinal : (1/(K:ℝ)) * ((2*(K:ℝ)/Real.pi)^2) = (4/Real.pi^2)*K := by
      field_simp; ring
    calc (4/Real.pi^2)*K = (1/(K:ℝ)) * ((2*(K:ℝ)/Real.pi)^2) := hfinal.symm
      _ ≤ (1/(K:ℝ)) * (|Real.sin (Real.pi*((K:ℝ)*x))| / |Real.sin (Real.pi*x)|)^2 :=
          mul_le_mul_of_nonneg_left hsq (by positivity)



lemma FK_exp (K : ℕ) (hK : 1 ≤ K) (y : ℝ) :
    (((K:ℝ)*FK K y : ℝ) : ℂ) =
      ∑ j ∈ Finset.range K, ∑ l ∈ Finset.range K, pe (((j:ℝ)-(l:ℝ))*y) := by
  have hKne : (K:ℝ) ≠ 0 := by positivity
  have hFK : ((K:ℝ)*FK K y : ℝ) = ‖∑ j ∈ Finset.range K, pe ((j:ℝ)*y)‖^2 := by
    unfold FK
    rw [one_div, ← mul_assoc, mul_inv_cancel₀ hKne, one_mul]
  rw [hFK]
  set w := ∑ j ∈ Finset.range K, pe ((j:ℝ)*y) with hw
  have hsq : ((‖w‖^2 : ℝ) : ℂ) = w * (starRingEnd ℂ) w := by
    rw [Complex.mul_conj, Complex.normSq_eq_norm_sq]
  rw [hsq, hw, map_sum, Finset.sum_mul]
  apply Finset.sum_congr rfl; intro j hj
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl; intro l hl
  have : pe ((j:ℝ)*y) * (starRingEnd ℂ) (pe ((l:ℝ)*y)) = pe (((j:ℝ)-(l:ℝ))*y) := by
    rw [pe_mul_sub]; congr 1; ring
  rw [this]

-- pair sum bound
lemma pair_sum_le (K : ℕ) (S : ℤ → ℂ) :
    ∑ j ∈ Finset.range K, ∑ l ∈ Finset.range K, ‖S ((j:ℤ)-(l:ℤ))‖ ≤
      (K:ℝ) * ∑ m ∈ Finset.Icc (-(K:ℤ)+1) ((K:ℤ)-1), ‖S m‖ := by
  rw [Finset.sum_comm]
  calc ∑ l ∈ Finset.range K, ∑ j ∈ Finset.range K, ‖S ((j:ℤ)-(l:ℤ))‖
      ≤ ∑ l ∈ Finset.range K, ∑ m ∈ Finset.Icc (-(K:ℤ)+1) ((K:ℤ)-1), ‖S m‖ := by
        apply Finset.sum_le_sum; intro l hl
        rw [← Finset.sum_image (g := fun j : ℕ => (j:ℤ)-(l:ℤ)) (f := fun m : ℤ => ‖S m‖)
          (by intro x _ y _ h; exact Nat.cast_injective (sub_left_injective h))]
        apply Finset.sum_le_sum_of_subset_of_nonneg
        · intro m hm
          rw [Finset.mem_image] at hm
          obtain ⟨j, hj, rfl⟩ := hm
          rw [Finset.mem_Icc]
          have hl' : (l:ℤ) ≤ (K:ℤ)-1 := by
            rw [Finset.mem_range] at hl; omega
          have hj'' : (j:ℤ) ≤ (K:ℤ)-1 := by
            rw [Finset.mem_range] at hj; omega
          constructor <;> omega
        · intro m _ _; exact norm_nonneg _
    _ = (K:ℝ) * ∑ m ∈ Finset.Icc (-(K:ℤ)+1) ((K:ℤ)-1), ‖S m‖ := by
        rw [Finset.sum_const, Finset.card_range]; simp


lemma pe_neg (x : ℝ) : pe (-x) = (starRingEnd ℂ) (pe x) := pe_conj x |>.symm

lemma dz_neg (x : ℝ) : dz (-x) = dz x := by
  apply le_antisymm
  · calc dz (-x) = |(-x) - (round (-x):ℤ)| := rfl
      _ ≤ |(-x) - ((-round x):ℤ)| := round_le _ _
      _ = |x - (round x:ℤ)| := by
          rw [show (-x) - ((-round x):ℤ) = -(x - (round x:ℤ)) by push_cast; ring, abs_neg]
      _ = dz x := rfl
  · calc dz x = |x - (round x:ℤ)| := rfl
      _ ≤ |x - ((-(round (-x))):ℤ)| := round_le _ _
      _ = |(-x) - (round (-x):ℤ)| := by
          rw [show x - ((-(round (-x))):ℤ) = -((-x) - (round (-x):ℤ)) by push_cast; ring, abs_neg]
      _ = dz (-x) := rfl

-- main FK expansion and bound
lemma pe_zero : pe (0:ℝ) = 1 := by unfold pe; simp

lemma icc_split (K : ℕ) :
    Finset.Icc (-(K:ℤ)+1) ((K:ℤ)-1) = Finset.Icc (-(K:ℤ)+1) (-1) ∪ Finset.Icc 0 ((K:ℤ)-1) := by
  ext m; simp only [Finset.mem_union, Finset.mem_Icc]; omega

lemma reindex_neg_icc (K : ℕ) (f : ℤ → ℝ) :
    ∑ m ∈ Finset.Icc (-(K:ℤ)+1) (-1), f m = ∑ t ∈ Finset.Icc 1 ((K:ℤ)-1), f (-t) := by
  refine Finset.sum_bij (fun m _ => -m) ?_ ?_ ?_ ?_
  · intro m hm; rw [Finset.mem_Icc] at hm ⊢; omega
  · intro a ha b hb h; omega
  · intro t ht; exact ⟨-t, by rw [Finset.mem_Icc] at ht ⊢; omega, by omega⟩
  · intro m hm; ring

lemma icc_int_eq (K : ℕ) (hK : 1 ≤ K) (g : ℤ → ℝ) :
    ∑ t ∈ Finset.Icc (1:ℤ) ((K:ℤ)-1), g t = ∑ t ∈ Finset.Icc 1 (K-1), g (t:ℤ) := by
  refine Finset.sum_bij (fun t _ => t.toNat) ?_ ?_ ?_ ?_
  · intro t ht; rw [Finset.mem_Icc] at ht ⊢; omega
  · intro a ha b hb h
    rw [Finset.mem_Icc] at ha hb
    have h1 : ((a.toNat : ℕ) : ℤ) = a := Int.toNat_of_nonneg (by omega)
    have h2 : ((b.toNat : ℕ) : ℤ) = b := Int.toNat_of_nonneg (by omega)
    omega
  · intro t ht
    rw [Finset.mem_Icc] at ht
    refine ⟨(t:ℤ), ?_, ?_⟩
    · rw [Finset.mem_Icc]; omega
    · simp
  · intro t ht
    rw [Finset.mem_Icc] at ht
    congr 1
    exact (Int.toNat_of_nonneg (by omega : (0:ℤ) ≤ t)).symm

lemma icc_split2 (K : ℕ) (hK : 1 ≤ K) :
    Finset.Icc (0:ℤ) ((K:ℤ)-1) = insert 0 (Finset.Icc 1 ((K:ℤ)-1)) := by
  ext m; simp only [Finset.mem_insert, Finset.mem_Icc]; omega

lemma FK_sum_le (K : ℕ) (hK : 1 ≤ K) (α β : ℝ) (R : ℕ)
    (hdz : ∀ m : ℤ, m ≠ 0 → |m| < (K:ℤ) → 0 < dz ((m:ℝ)*α)) :
    ∑ n ∈ Finset.Icc 1 R, FK K ((n:ℝ)*α+β) ≤
      (R:ℝ) + 2 * ∑ m ∈ Finset.Icc 1 (K-1), min (R:ℝ) (1/(2*dz ((m:ℝ)*α))) := by
  set S : ℤ → ℂ := fun m => ∑ n ∈ Finset.Icc 1 R, pe (((m:ℝ)*(n:ℝ))*α) with hS
  have hKne : (K:ℝ) ≠ 0 := by positivity
  have hA : ∑ n ∈ Finset.Icc 1 R, FK K ((n:ℝ)*α+β)
      = (1/(K:ℝ)) * ∑ n ∈ Finset.Icc 1 R, ((K:ℝ)*FK K ((n:ℝ)*α+β)) := by
    rw [Finset.mul_sum]; apply Finset.sum_congr rfl; intro n _; field_simp
  have hB : ∑ n ∈ Finset.Icc 1 R, ((K:ℝ)*FK K ((n:ℝ)*α+β))
      = (∑ j ∈ Finset.range K, ∑ l ∈ Finset.range K, pe (((j:ℝ)-(l:ℝ))*β) * S ((j:ℤ)-(l:ℤ))).re := by
    have h1 : ∑ n ∈ Finset.Icc 1 R, ((K:ℝ)*FK K ((n:ℝ)*α+β))
        = (∑ n ∈ Finset.Icc 1 R, ((((K:ℝ)*FK K ((n:ℝ)*α+β) : ℝ)) : ℂ)).re := by
      rw [Complex.re_sum]; apply Finset.sum_congr rfl; intro n _; simp
    rw [h1]
    congr 1
    rw [show (∑ n ∈ Finset.Icc 1 R, ((((K:ℝ)*FK K ((n:ℝ)*α+β) : ℝ)) : ℂ))
        = ∑ n ∈ Finset.Icc 1 R, ∑ j ∈ Finset.range K, ∑ l ∈ Finset.range K,
            pe (((j:ℝ)-(l:ℝ))*((n:ℝ)*α+β)) from by
      apply Finset.sum_congr rfl; intro n _; exact FK_exp K hK _]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl; intro j hj
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl; intro l hl
    rw [hS, Finset.mul_sum]
    apply Finset.sum_congr rfl; intro n _
    rw [show (((j:ℝ)-(l:ℝ))*((n:ℝ)*α+β)) = ((j:ℝ)-(l:ℝ))*β + ((((j:ℤ)-(l:ℤ):ℤ):ℝ)*(n:ℝ)*α) by push_cast; ring, pe_add]
  rw [hA, hB]
  have hle : (∑ j ∈ Finset.range K, ∑ l ∈ Finset.range K, pe (((j:ℝ)-(l:ℝ))*β) * S ((j:ℤ)-(l:ℤ))).re
      ≤ ∑ j ∈ Finset.range K, ∑ l ∈ Finset.range K, ‖S ((j:ℤ)-(l:ℤ))‖ := by
    refine le_trans (Complex.re_le_norm _) ?_
    calc ‖∑ j ∈ Finset.range K, ∑ l ∈ Finset.range K, pe (((j:ℝ)-(l:ℝ))*β) * S ((j:ℤ)-(l:ℤ))‖
        ≤ ∑ j ∈ Finset.range K, ‖∑ l ∈ Finset.range K, pe (((j:ℝ)-(l:ℝ))*β) * S ((j:ℤ)-(l:ℤ))‖ := norm_sum_le _ _
      _ ≤ ∑ j ∈ Finset.range K, ∑ l ∈ Finset.range K, ‖pe (((j:ℝ)-(l:ℝ))*β) * S ((j:ℤ)-(l:ℤ))‖ :=
            Finset.sum_le_sum (fun j _ => norm_sum_le _ _)
      _ = ∑ j ∈ Finset.range K, ∑ l ∈ Finset.range K, ‖S ((j:ℤ)-(l:ℤ))‖ := by
            apply Finset.sum_congr rfl; intro j _
            apply Finset.sum_congr rfl; intro l _
            rw [norm_mul, pe_norm, one_mul]
  refine le_trans (mul_le_mul_of_nonneg_left hle (by positivity)) ?_
  refine le_trans (mul_le_mul_of_nonneg_left (pair_sum_le K S) (by positivity)) ?_
  rw [show (1/(K:ℝ)) * ((K:ℝ) * ∑ m ∈ Finset.Icc (-(K:ℤ)+1) ((K:ℤ)-1), ‖S m‖)
        = ∑ m ∈ Finset.Icc (-(K:ℤ)+1) ((K:ℤ)-1), ‖S m‖ by
      rw [one_div, ← mul_assoc, inv_mul_cancel₀ hKne, one_mul]]
  -- bounds on individual ‖S m‖
  have hS0 : ‖S 0‖ = (R:ℝ) := by
    rw [hS]
    change ‖∑ n ∈ Finset.Icc 1 R, pe (((0:ℤ):ℝ)*(n:ℝ)*α)‖ = (R:ℝ)
    have hsum : (∑ n ∈ Finset.Icc 1 R, pe (((0:ℤ):ℝ)*(n:ℝ)*α)) = (R:ℂ) := by
      simp only [Int.cast_zero, zero_mul, pe_zero, Finset.sum_const, Nat.card_Icc]
      simp
    rw [hsum, show ‖(R:ℂ)‖ = (R:ℝ) by simp]
  have hposL : ∀ m : ℤ, 1 ≤ m → m ≤ (K:ℤ)-1 → ‖S m‖ ≤ min (R:ℝ) (1/(2*dz (((m.toNat:ℤ):ℝ)*α))) := by
    intro m hm1 hmK
    have hmne : m ≠ 0 := by omega
    have hmeq : (m:ℝ) = ((m.toNat:ℤ):ℝ) := by rw [Int.toNat_of_nonneg (by omega)]
    have hmabs : |m| < (K:ℤ) := by rw [abs_of_nonneg (by omega : (0:ℤ) ≤ m)]; omega
    have hd := hdz m hmne hmabs
    have hd' : 0 < dz (((m.toNat:ℤ):ℝ)*α) := by rw [← hmeq]; exact hd
    simp only [hS]
    rw [show (∑ n ∈ Finset.Icc 1 R, pe (((m:ℝ)*(n:ℝ))*α))
          = ∑ n ∈ Finset.Icc 1 R, pe ((((m.toNat:ℤ):ℝ)*(n:ℝ))*α) from by
        apply Finset.sum_congr rfl; intro n _; rw [hmeq]]
    exact geom_le_pos m.toNat R α hd'
  have hnegL : ∀ m : ℤ, -(K:ℤ)+1 ≤ m → m ≤ -1 →
      ‖S m‖ ≤ min (R:ℝ) (1/(2*dz ((((-m).toNat:ℤ):ℝ)*α))) := by
    intro m hm2 hm1
    have hmne : m ≠ 0 := by omega
    have hmeq : ((-m:ℤ):ℝ) = ((((-m).toNat:ℤ):ℝ)) := by rw [Int.toNat_of_nonneg (by omega)]
    have hmabs : |m| < (K:ℤ) := by rw [abs_of_nonpos (by omega : m ≤ 0)]; omega
    have hd := hdz m hmne hmabs
    have hd' : 0 < dz ((((-m).toNat:ℤ):ℝ)*α) := by
      rw [← hmeq, show ((-m:ℤ):ℝ) = -((m:ℝ)) by push_cast; ring,
          show (-((m:ℝ)))*α = -((m:ℝ)*α) by ring, dz_neg]
      exact hd
    simp only [hS]
    have hconj : (∑ n ∈ Finset.Icc 1 R, pe (((m:ℝ)*(n:ℝ))*α))
        = (starRingEnd ℂ) (∑ n ∈ Finset.Icc 1 R, pe ((((-m:ℤ):ℝ)*(n:ℝ))*α)) := by
      rw [map_sum]
      apply Finset.sum_congr rfl; intro n _
      rw [pe_conj]
      congr 1; push_cast; ring
    rw [hconj, Complex.norm_conj]
    rw [show (∑ n ∈ Finset.Icc 1 R, pe ((((-m:ℤ):ℝ)*(n:ℝ))*α))
          = ∑ n ∈ Finset.Icc 1 R, pe (((((-m).toNat:ℤ):ℝ)*(n:ℝ))*α) from by
      apply Finset.sum_congr rfl; intro n _; rw [hmeq]]
    exact geom_le_pos (-m).toNat R α hd'
  -- combine
  have hsplit : ∑ m ∈ Finset.Icc (-(K:ℤ)+1) ((K:ℤ)-1), ‖S m‖
      ≤ (R:ℝ) + 2 * ∑ m ∈ Finset.Icc 1 (K-1), min (R:ℝ) (1/(2*dz ((m:ℝ)*α))) := by
    rw [icc_split, Finset.sum_union (by
      rw [Finset.disjoint_left]; intro m hm1 hm2
      rw [Finset.mem_Icc] at hm1 hm2; omega)]
    rw [reindex_neg_icc]
    have hnegA : ∑ t ∈ Finset.Icc (1:ℤ) ((K:ℤ)-1), ‖S (-t)‖
        ≤ ∑ t ∈ Finset.Icc 1 (K-1), min (R:ℝ) (1/(2*dz ((t:ℝ)*α))) := by
      rw [icc_int_eq K hK]
      apply Finset.sum_le_sum; intro t ht
      rw [Finset.mem_Icc] at ht
      have hb := hnegL (-(t:ℤ)) (by omega) (by omega)
      simp only [neg_neg, Int.toNat_natCast] at hb
      rw [show (t:ℝ) = ((t:ℤ):ℝ) by norm_cast]
      exact hb
    have hposA : ∑ t ∈ Finset.Icc (1:ℤ) ((K:ℤ)-1), ‖S t‖
        ≤ ∑ t ∈ Finset.Icc 1 (K-1), min (R:ℝ) (1/(2*dz ((t:ℝ)*α))) := by
      rw [icc_int_eq K hK]
      apply Finset.sum_le_sum; intro t ht
      rw [Finset.mem_Icc] at ht
      have hb := hposL (t:ℤ) (by omega) (by omega)
      simp only [Int.toNat_natCast] at hb
      rw [show (t:ℝ) = ((t:ℤ):ℝ) by norm_cast]
      exact hb
    have h0A : ∑ m ∈ Finset.Icc (0:ℤ) ((K:ℤ)-1), ‖S m‖
        ≤ (R:ℝ) + ∑ t ∈ Finset.Icc 1 (K-1), min (R:ℝ) (1/(2*dz ((t:ℝ)*α))) := by
      rw [icc_split2 K hK, Finset.sum_insert (by simp)]
      rw [hS0]
      linarith [hposA]
    linarith
  linarith [hsplit]



lemma inv_range_le_log (n : ℕ) : ∑ i ∈ Finset.range n, (1:ℝ)/((i:ℝ)+1) ≤ 1 + Real.log n := by
  induction n with
  | zero => simp
  | succ m ih =>
    rw [Finset.sum_range_succ]
    rcases Nat.eq_zero_or_pos m with h | h
    · subst h; simp
    · have hm0 : (0:ℝ) < m := by exact_mod_cast h
      have hstep : (1:ℝ)/((m:ℝ)+1) ≤ Real.log ((m:ℝ)+1) - Real.log (m:ℝ) := by
        have h := Real.log_le_sub_one_of_pos (show (0:ℝ) < (m:ℝ)/(m+1) by positivity)
        rw [show (m:ℝ)/((m:ℝ)+1) - 1 = -(1/((m:ℝ)+1)) by field_simp; ring] at h
        have h2 : Real.log ((m:ℝ)/((m:ℝ)+1)) = - Real.log (((m:ℝ)+1)/(m:ℝ)) := by
          rw [show (m:ℝ)/((m:ℝ)+1) = (((m:ℝ)+1)/(m:ℝ))⁻¹ by field_simp, Real.log_inv]
        rw [h2] at h
        have h3 : Real.log (((m:ℝ)+1)/(m:ℝ)) = Real.log ((m:ℝ)+1) - Real.log (m:ℝ) :=
          Real.log_div (by positivity) (ne_of_gt hm0)
        linarith [h, h3]
      have hcast : ((m+1 : ℕ) : ℝ) = (m:ℝ) + 1 := by push_cast; ring
      have hlogcast : Real.log ((m+1 : ℕ) : ℝ) = Real.log ((m:ℝ)+1) := by rw [hcast]
      rw [hlogcast]
      linarith [ih, hstep]

lemma min_inv_le_card (R : ℕ) (x : ℝ) (hx : 0 < x) :
    min (R:ℝ) (1/(2*x)) ≤ ((Finset.Icc 1 R).filter (fun (t:ℕ) => x ≤ 1/(2*(t:ℝ)))).card + 1 := by
  set M := min (R:ℝ) (1/(2*x)) with hM
  have hM0 : 0 ≤ M := by rw [hM]; positivity
  have hsub : Finset.Icc 1 ⌊M⌋₊ ⊆ (Finset.Icc 1 R).filter (fun (t:ℕ) => x ≤ 1/(2*(t:ℝ))) := by
    intro t ht
    rw [Finset.mem_Icc] at ht
    have ht1 : (1:ℕ) ≤ t := ht.1
    have htM : (t:ℝ) ≤ M := le_trans (by exact_mod_cast ht.2) (Nat.floor_le hM0)
    rw [Finset.mem_filter, Finset.mem_Icc]
    refine ⟨⟨ht1, by exact_mod_cast (le_trans htM ((le_of_eq hM).trans (min_le_left _ _)))⟩, ?_⟩
    have hMx : M ≤ 1/(2*x) := (le_of_eq hM).trans (min_le_right _ _)
    have htpos : (0:ℝ) < t := by exact_mod_cast ht1
    rw [le_div_iff₀ (mul_pos two_pos hx)] at hMx
    rw [le_div_iff₀ (by positivity : (0:ℝ) < 2*(t:ℝ))]
    nlinarith [htM, hMx, hx]
  have hcard : (⌊M⌋₊ : ℕ) ≤ ((Finset.Icc 1 R).filter (fun (t:ℕ) => x ≤ 1/(2*(t:ℝ)))).card := by
    have := Finset.card_le_card hsub
    rwa [Nat.card_Icc, Nat.add_sub_cancel] at this
  have hMle : M ≤ ((⌊M⌋₊ : ℕ) : ℝ) + 1 := le_of_lt (Nat.lt_floor_add_one M)
  have hc : ((⌊M⌋₊ : ℕ) : ℝ) ≤ (((Finset.Icc 1 R).filter (fun (t:ℕ) => x ≤ 1/(2*(t:ℝ)))).card : ℝ) := by
    exact_mod_cast hcard
  linarith

lemma layer (R L : ℕ) (α : ℝ) (hdz : ∀ m ∈ Finset.Icc 1 L, 0 < dz ((m:ℝ)*α)) :
    ∑ m ∈ Finset.Icc 1 L, min (R:ℝ) (1/(2*dz ((m:ℝ)*α)))
      ≤ (L:ℝ) + ∑ t ∈ Finset.Icc 1 R,
          (((Finset.Icc 1 L).filter (fun (m:ℕ) => dz ((m:ℝ)*α) ≤ 1/(2*(t:ℝ)))).card : ℝ) := by
  have hpt : ∀ m ∈ Finset.Icc 1 L, min (R:ℝ) (1/(2*dz ((m:ℝ)*α)))
      ≤ 1 + ∑ t ∈ Finset.Icc 1 R, (if dz ((m:ℝ)*α) ≤ 1/(2*(t:ℝ)) then (1:ℝ) else 0) := by
    intro m hm
    have h1 := min_inv_le_card R (dz ((m:ℝ)*α)) (hdz m hm)
    have h2 : (((Finset.Icc 1 R).filter (fun (t:ℕ) => dz ((m:ℝ)*α) ≤ 1/(2*(t:ℝ)))).card : ℝ)
        = ∑ t ∈ Finset.Icc 1 R, (if dz ((m:ℝ)*α) ≤ 1/(2*(t:ℝ)) then (1:ℝ) else 0) := by
      rw [Finset.card_filter]; push_cast; ring
    linarith [h1, h2.symm.le, h2.le]
  calc ∑ m ∈ Finset.Icc 1 L, min (R:ℝ) (1/(2*dz ((m:ℝ)*α)))
      ≤ ∑ m ∈ Finset.Icc 1 L, (1 + ∑ t ∈ Finset.Icc 1 R,
          (if dz ((m:ℝ)*α) ≤ 1/(2*(t:ℝ)) then (1:ℝ) else 0)) := Finset.sum_le_sum hpt
    _ = (L:ℝ) + ∑ m ∈ Finset.Icc 1 L, ∑ t ∈ Finset.Icc 1 R,
          (if dz ((m:ℝ)*α) ≤ 1/(2*(t:ℝ)) then (1:ℝ) else 0) := by
        rw [Finset.sum_add_distrib, Finset.sum_const, Nat.card_Icc]; simp
    _ = (L:ℝ) + ∑ t ∈ Finset.Icc 1 R, ∑ m ∈ Finset.Icc 1 L,
          (if dz ((m:ℝ)*α) ≤ 1/(2*(t:ℝ)) then (1:ℝ) else 0) := by rw [Finset.sum_comm]
    _ = (L:ℝ) + ∑ t ∈ Finset.Icc 1 R,
          (((Finset.Icc 1 L).filter (fun (m:ℕ) => dz ((m:ℝ)*α) ≤ 1/(2*(t:ℝ)))).card : ℝ) := by
        congr 1
        apply Finset.sum_congr rfl; intro t _
        rw [Finset.card_filter]; push_cast; ring

-- Fejer step: count <= (pi^2/(4K')) sum FK
lemma fejer_card_le (b : ℤ) (Q : ℕ) (hQ : 1 ≤ Q) (hcop : Int.gcd b (Q:ℤ) = 1)
    (α β : ℝ) (K : ℝ) (hK : 1 ≤ K) (hb : |α - (b:ℝ)/(Q:ℝ)| ≤ K/(Q:ℝ)^2)
    (R : ℕ) (δ : ℝ) (hδ0 : 0 < δ) (K' : ℕ) (hK'1 : 1 ≤ K')
    (hδK' : δ ≤ 1/(2*(K':ℝ))) (hK'Q : (K':ℝ) ≤ (Q:ℝ)/(2*K)) :
    (((Finset.Icc 1 R).filter (fun (n:ℕ) => dz ((n:ℝ)*α+β) ≤ δ)).card : ℝ) ≤
        (Real.pi^2/(4*(K':ℝ))) * ∑ n ∈ Finset.Icc 1 R, FK K' ((n:ℝ)*α+β) := by
  rw [Finset.card_filter]
  push_cast
  rw [Finset.mul_sum]
  apply Finset.sum_le_sum; intro n _
  by_cases hp : dz ((n:ℝ)*α+β) ≤ δ
  · rw [if_pos hp]
    have hlow := FK_lower K' hK'1 ((n:ℝ)*α+β) (le_trans hp hδK')
    have hge : (1:ℝ) ≤ (Real.pi^2/(4*(K':ℝ))) * ((4/Real.pi^2)*(K':ℝ)) := by
      rw [show (Real.pi^2/(4*(K':ℝ))) * ((4/Real.pi^2)*(K':ℝ)) = 1 by field_simp]
    calc (1:ℝ) = 1 := rfl
      _ ≤ (Real.pi^2/(4*(K':ℝ))) * ((4/Real.pi^2)*(K':ℝ)) := hge
      _ ≤ (Real.pi^2/(4*(K':ℝ))) * FK K' ((n:ℝ)*α+β) := by
          apply mul_le_mul_of_nonneg_left _ (by positivity)
          linarith [hlow]
  · rw [if_neg hp]
    have hK'pos : (0:ℝ) < K' := lt_of_lt_of_le zero_lt_one (by exact_mod_cast hK'1)
    have := FK_nonneg K' ((n:ℝ)*α+β)
    positivity

lemma log_nonneg_2 (x : ℝ) (hx : 0 ≤ x) : 0 ≤ Real.log (2 + x) :=
  Real.log_nonneg (by linarith)

lemma inv_floor_half_le (δ : ℝ) (hδ0 : 0 < δ) (hδ12 : δ ≤ 1/2) :
    (1:ℝ)/((⌊1/(2*δ)⌋₊ : ℕ) : ℝ) ≤ 4*δ := by
  rcases le_or_gt δ (1/4) with hd | hd
  · have hfloor : (1:ℝ)/(4*δ) ≤ ((⌊1/(2*δ)⌋₊ : ℕ) : ℝ) := by
      have h1 : (1:ℝ)/(2*δ) - 1 < ((⌊1/(2*δ)⌋₊ : ℕ) : ℝ) := by
        have := Nat.lt_floor_add_one (1/(2*δ)); linarith
      have h2 : (1:ℝ)/(4*δ) ≤ (1:ℝ)/(2*δ) - 1 := by
        rw [le_sub_iff_add_le, div_add_one (by positivity : (4*δ:ℝ) ≠ 0),
            div_le_div_iff₀ (by positivity : (0:ℝ) < 4*δ) (by positivity : (0:ℝ) < 2*δ)]
        nlinarith [hδ0, hd]
      linarith [h1, h2]
    have hKf1 : 1 ≤ ⌊1/(2*δ)⌋₊ := by
      rw [Nat.one_le_floor_iff, le_div_iff₀ (by positivity : (0:ℝ) < 2*δ)]; linarith [hδ12]
    have hh : (1:ℝ) ≤ ((⌊1/(2*δ)⌋₊ : ℕ):ℝ) := by exact_mod_cast hKf1
    rw [div_le_iff₀ (by linarith : (0:ℝ) < ((⌊1/(2*δ)⌋₊ : ℕ):ℝ))]
    have hm := mul_le_mul_of_nonneg_left hfloor (by positivity : (0:ℝ) ≤ 4*δ)
    rw [one_div, mul_inv_cancel₀ (by positivity : (4*δ:ℝ) ≠ 0)] at hm
    linarith [hm]
  · have hfloor : ⌊1/(2*δ)⌋₊ = 1 := by
      rw [Nat.floor_eq_iff (by positivity : (0:ℝ) ≤ 1/(2*δ))]
      constructor
      · rw [le_div_iff₀ (by positivity : (0:ℝ) < 2*δ)]; norm_num; linarith [hδ12]
      · rw [div_lt_iff₀ (by positivity : (0:ℝ) < 2*δ)]
        push_cast
        linarith [hd]
    rw [hfloor]; norm_num
    linarith [hd]

lemma inv_floor_QK_le (Q : ℕ) (hQ : 1 ≤ Q) (K : ℝ) (hK : 0 < K) (hQK : 2*K ≤ Q) :
    (1:ℝ)/((⌊(Q:ℝ)/(2*K)⌋₊ : ℕ) : ℝ) ≤ 4*K/(Q:ℝ) := by
  have hQpos : (0:ℝ) < (Q:ℝ) := by exact_mod_cast hQ
  rcases le_or_gt (2:ℝ) ((Q:ℝ)/(2*K)) with hd | hd
  · have hfloor : (Q:ℝ)/(4*K) ≤ ((⌊(Q:ℝ)/(2*K)⌋₊ : ℕ) : ℝ) := by
      have h1 : (Q:ℝ)/(2*K) - 1 < ((⌊(Q:ℝ)/(2*K)⌋₊ : ℕ) : ℝ) := by
        have := Nat.lt_floor_add_one ((Q:ℝ)/(2*K)); linarith
      have h4K : 4*K ≤ (Q:ℝ) := by
        rw [le_div_iff₀ (by positivity : (0:ℝ) < 2*K)] at hd; linarith [hd]
      have h2 : (Q:ℝ)/(4*K) ≤ (Q:ℝ)/(2*K) - 1 := by
        rw [le_sub_iff_add_le, div_add_one (by positivity : (4*K:ℝ) ≠ 0),
            div_le_div_iff₀ (by positivity : (0:ℝ) < 4*K) (by positivity : (0:ℝ) < 2*K)]
        nlinarith [hK, h4K]
      linarith [h1, h2]
    have hKq1 : 1 ≤ ⌊(Q:ℝ)/(2*K)⌋₊ := by
      rw [Nat.one_le_floor_iff, le_div_iff₀ (by positivity : (0:ℝ) < 2*K)]; linarith [hQK]
    have hh : (1:ℝ) ≤ ((⌊(Q:ℝ)/(2*K)⌋₊ : ℕ):ℝ) := by exact_mod_cast hKq1
    have hKqpos : (0:ℝ) < ((⌊(Q:ℝ)/(2*K)⌋₊ : ℕ):ℝ) := by linarith [hh]
    rw [div_le_iff₀ hKqpos]
    rw [show (4*K)/(Q:ℝ) * ((⌊(Q:ℝ)/(2*K)⌋₊ : ℕ):ℝ) = (4*K*((⌊(Q:ℝ)/(2*K)⌋₊ : ℕ):ℝ))/(Q:ℝ) by ring]
    rw [le_div_iff₀ hQpos]
    have hm : (4*K) * ((Q:ℝ)/(4*K)) ≤ (4*K) * ((⌊(Q:ℝ)/(2*K)⌋₊ : ℕ):ℝ) :=
      mul_le_mul_of_nonneg_left hfloor (by positivity : (0:ℝ) ≤ 4*K)
    rw [show (4*K) * ((Q:ℝ)/(4*K)) = (Q:ℝ) by field_simp] at hm
    linarith [hm]
  · have hfloor : ⌊(Q:ℝ)/(2*K)⌋₊ = 1 := by
      rw [Nat.floor_eq_iff (by positivity : (0:ℝ) ≤ (Q:ℝ)/(2*K))]
      constructor
      · rw [le_div_iff₀ (by positivity : (0:ℝ) < 2*K)]; norm_num; linarith [hQK]
      · rw [div_lt_iff₀ (by positivity : (0:ℝ) < 2*K)]
        rw [div_lt_iff₀ (by positivity : (0:ℝ) < 2*K)] at hd
        push_cast; linarith [hd]
    have hd4 : (Q:ℝ) < 4*K := by
      rw [div_lt_iff₀ (by positivity : (0:ℝ) < 2*K)] at hd; linarith [hd]
    rw [hfloor]
    rw [show (1:ℝ)/((1:ℕ):ℝ) = 1 by norm_num]
    rw [le_div_iff₀ hQpos]
    nlinarith [hd4, hK]

lemma dz_pos_small (Q : ℕ) (hQ : 1 ≤ Q) (b : ℤ) (hg : Int.gcd b (Q:ℤ) = 1)
    (α : ℝ) (K : ℝ) (hK : 1 ≤ K) (hb : |α - (b:ℝ)/(Q:ℝ)| ≤ K/(Q:ℝ)^2)
    (K' : ℕ) (hK'q : (K':ℝ) ≤ (Q:ℝ)/(2*K)) :
    ∀ m : ℤ, m ≠ 0 → |m| < (K':ℤ) → 0 < dz ((m:ℝ)*α) := by
  intro m hm hlt
  have hQpos : (0:ℝ) < (Q:ℝ) := by exact_mod_cast hQ
  have hltQ : |((m:ℝ))| < (Q:ℝ)/(2*K) := lt_of_lt_of_le (by exact_mod_cast hlt) hK'q
  have h := sep' Q hQ b hg α K hK hb m hm hltQ
  have h1 : (0:ℝ) < 1/(2*(Q:ℝ)) := by positivity
  linarith [h, h1]

lemma fejer_count_le (b : ℤ) (Q : ℕ) (hQ : 1 ≤ Q) (hg : Int.gcd b (Q:ℤ) = 1)
    (α β : ℝ) (K : ℝ) (hK : 1 ≤ K) (hb : |α - (b:ℝ)/(Q:ℝ)| ≤ K/(Q:ℝ)^2)
    (R : ℕ) (δ : ℝ) (hδ0 : 0 < δ) (K' : ℕ) (hK'1 : 1 ≤ K')
    (hδK' : δ ≤ 1/(2*(K':ℝ))) (hK'q : (K':ℝ) ≤ (Q:ℝ)/(2*K)) :
    (((Finset.Icc 1 R).filter (fun (n:ℕ) => dz ((n:ℝ)*α+β) ≤ δ)).card : ℝ) ≤
      (Real.pi^2/(4*(K':ℝ))) * ((R:ℝ) + 2 * ∑ m ∈ Finset.Icc 1 (K'-1),
          min (R:ℝ) (1/(2*dz ((m:ℝ)*α)))) := by
  have h1 := fejer_card_le b Q hQ hg α β K hK hb R δ hδ0 K' hK'1 hδK' hK'q
  have h2 := FK_sum_le K' hK'1 α β R (dz_pos_small Q hQ b hg α K hK hb K' hK'q)
  have hpos : (0:ℝ) ≤ Real.pi^2/(4*(K':ℝ)) := by positivity
  linarith [h1, mul_le_mul_of_nonneg_left h2 hpos]

lemma sum_min_le (b : ℤ) (Q : ℕ) (hQ : 1 ≤ Q) (hg : Int.gcd b (Q:ℤ) = 1)
    (α : ℝ) (K : ℝ) (hK : 1 ≤ K) (hb : |α - (b:ℝ)/(Q:ℝ)| ≤ K/(Q:ℝ)^2)
    (R : ℕ) (K' : ℕ) (hK'1 : 1 ≤ K') (hK'q : (K':ℝ) ≤ (Q:ℝ)/(2*K))
    (hLg : 1 + Real.log (R:ℝ) ≤ 1 + Real.log (2 + (R:ℝ) + (Q:ℝ))) :
    ∑ m ∈ Finset.Icc 1 (K'-1), min (R:ℝ) (1/(2*dz ((m:ℝ)*α)))
      ≤ 2*(R:ℝ) + (K':ℝ) + 2*(Q:ℝ)*(1 + Real.log (2 + (R:ℝ) + (Q:ℝ))) := by
  have hQpos : (0:ℝ) < (Q:ℝ) := by exact_mod_cast hQ
  have hl := layer R (K'-1) α (by
    intro m hm
    rw [Finset.mem_Icc] at hm
    exact dz_pos_small Q hQ b hg α K hK hb K' hK'q (m:ℤ) (by omega) (by
      rw [abs_of_nonneg (by omega : (0:ℤ) ≤ (m:ℤ))]
      have : m ≤ K'-1 := hm.2
      omega))
  have hnc : ∀ t ∈ Finset.Icc 1 R,
      (((Finset.Icc 1 (K'-1)).filter (fun (m:ℕ) => dz ((m:ℝ)*α) ≤ 1/(2*(t:ℝ)))).card : ℝ)
        ≤ 4*(1/(2*(t:ℝ)))*(Q:ℝ) + 2 := by
    intro t ht
    rw [Finset.mem_Icc] at ht
    refine Ncount_le Q hQ b hg α K hK hb (K'-1) ?_ (1/(2*(t:ℝ))) (by positivity)
    rw [show ((K'-1:ℕ):ℝ) = (K':ℝ) - 1 by rw [Nat.cast_sub hK'1]; norm_num]
    linarith [hK'q]
  have hsum : ∑ t ∈ Finset.Icc 1 R,
      (((Finset.Icc 1 (K'-1)).filter (fun (m:ℕ) => dz ((m:ℝ)*α) ≤ 1/(2*(t:ℝ)))).card : ℝ)
        ≤ 2*(Q:ℝ)*(1 + Real.log (2 + (R:ℝ) + (Q:ℝ))) + 2*(R:ℝ) := by
    have h2 : ∑ t ∈ Finset.Icc 1 R, (4*(1/(2*(t:ℝ)))*(Q:ℝ) + 2)
        ≤ 2*(Q:ℝ)*(1 + Real.log (2 + (R:ℝ) + (Q:ℝ))) + 2*(R:ℝ) := by
      rw [Finset.sum_add_distrib]
      have h3 : ∑ t ∈ Finset.Icc 1 R, 4*(1/(2*(t:ℝ)))*(Q:ℝ)
          = 2*(Q:ℝ) * ∑ t ∈ Finset.Icc 1 R, (1:ℝ)/(t:ℝ) := by
        rw [Finset.mul_sum]; apply Finset.sum_congr rfl; intro t ht
        rw [Finset.mem_Icc] at ht
        have ht0 : (t:ℝ) ≠ 0 := by have h1 := ht.1; positivity
        rw [show (4:ℝ)*(1/(2*(t:ℝ)))*(Q:ℝ) = 2*(Q:ℝ)*((1:ℝ)/(t:ℝ)) by
          field_simp; ring]
      have h4 : ∑ t ∈ Finset.Icc 1 R, (2:ℝ) = 2*(R:ℝ) := by
        have hc : (Finset.Icc 1 R).card = R := by rw [Nat.card_Icc, Nat.add_sub_cancel]
        rw [Finset.sum_const, hc, nsmul_eq_mul]; ring
      rw [h3, h4]
      have h5 : ∑ t ∈ Finset.Icc 1 R, (1:ℝ)/(t:ℝ) ≤ 1 + Real.log (2 + (R:ℝ) + (Q:ℝ)) := by
        have hb1 : ∑ t ∈ Finset.Icc 1 R, (1:ℝ)/(t:ℝ) = ∑ t ∈ Finset.range R, (1:ℝ)/((t:ℝ)+1) := by
          rw [show Finset.Icc 1 R = Finset.Ico 1 (R+1) by ext i; simp only [Finset.mem_Icc, Finset.mem_Ico]; omega]
          rw [Finset.sum_Ico_eq_sum_range]
          simp only [Nat.add_sub_cancel]
          apply Finset.sum_congr rfl; intro k _
          congr 1; push_cast; ring
        rw [hb1]
        linarith [inv_range_le_log R, hLg]
      nlinarith [h5, hQpos]
    calc _ ≤ ∑ t ∈ Finset.Icc 1 R, (4*(1/(2*(t:ℝ)))*(Q:ℝ) + 2) := Finset.sum_le_sum hnc
      _ ≤ _ := h2
  have hsub : (((K'-1:ℕ)):ℝ) ≤ (K':ℝ) := by exact_mod_cast Nat.sub_le _ _
  linarith [hl, hsum, hsub]

lemma log_le_log_Lg (R Q : ℕ) : Real.log (R:ℝ) ≤ Real.log (2 + (R:ℝ) + (Q:ℝ)) := by
  rcases Nat.eq_zero_or_pos R with h | h
  · subst h; rw [Nat.cast_zero, Real.log_zero]
    exact Real.log_nonneg (by have h2 : (0:ℝ) ≤ (Q:ℝ) := Nat.cast_nonneg Q; linarith)
  · apply Real.log_le_log (by positivity)
    have h1 : (0:ℝ) ≤ (R:ℝ) := Nat.cast_nonneg R
    have h2 : (0:ℝ) ≤ (Q:ℝ) := Nat.cast_nonneg Q
    linarith

lemma one_le_floor_half (δ : ℝ) (hδ0 : 0 < δ) (hδ12 : δ ≤ 1/2) : 1 ≤ ⌊1/(2*δ)⌋₊ := by
  rw [Nat.one_le_floor_iff, le_div_iff₀ (by positivity : (0:ℝ) < 2*δ)]; nlinarith [hδ12]
lemma one_le_floor_QK (Q : ℕ) (K : ℝ) (hK : 0 < K) (hQK : 2*K ≤ Q) : 1 ≤ ⌊(Q:ℝ)/(2*K)⌋₊ := by
  rw [Nat.one_le_floor_iff, le_div_iff₀ (by positivity : (0:ℝ) < 2*K)]; nlinarith [hQK]

theorem rho_bound (K : ℝ) (hK : 1 ≤ K) (α β : ℝ) (Q : ℕ) (b : ℤ) (hQ : 1 ≤ Q)
    (hg : Int.gcd b (Q:ℤ) = 1) (hb : |α - (b:ℝ)/(Q:ℝ)| ≤ K/(Q:ℝ)^2)
    (R : ℕ) (δ : ℝ) (hδ0 : 0 < δ) (hδ1 : δ ≤ 1) :
    (((Finset.Icc 1 R).filter (fun (n:ℕ) => dz ((n:ℝ)*α+β) ≤ δ)).card : ℝ) ≤
      (1000:ℝ) * (δ * ((R:ℝ) + (Q:ℝ)*(1 + Real.log (2 + (R:ℝ) + (Q:ℝ))))
           + K * ((R:ℝ)/(Q:ℝ) + 1 + Real.log (2 + (R:ℝ) + (Q:ℝ)))) := by
  have hQpos : (0:ℝ) < Q := by exact_mod_cast hQ
  have hKpos : 0 < K := lt_of_lt_of_le zero_lt_one hK
  set Lg := 1 + Real.log (2 + (R:ℝ) + (Q:ℝ)) with hLg
  have hLg1 : 1 ≤ Lg := by
    rw [hLg]
    have := Real.log_nonneg (show (1:ℝ) ≤ 2 + (R:ℝ) + (Q:ℝ) by
      have h1 : (0:ℝ) ≤ (R:ℝ) := Nat.cast_nonneg R
      have h2 : (0:ℝ) ≤ (Q:ℝ) := Nat.cast_nonneg Q
      linarith)
    linarith
  have heql : (1000:ℝ) * (δ * ((R:ℝ) + (Q:ℝ)*(1 + Real.log (2 + (R:ℝ) + (Q:ℝ)))) +
        K * ((R:ℝ)/(Q:ℝ) + 1 + Real.log (2 + (R:ℝ) + (Q:ℝ))))
        = 1000 * (δ * ((R:ℝ) + (Q:ℝ)*Lg) + K * ((R:ℝ)/(Q:ℝ) + Lg)) := by
    rw [← hLg]; ring
  rw [heql]
  by_cases hδ12 : δ ≤ 1/2
  ·
    by_cases hQK : (2:ℝ)*K ≤ (Q:ℝ)
    · set K' : ℕ := if ⌊1/(2*δ)⌋₊ ≤ ⌊(Q:ℝ)/(2*K)⌋₊ then ⌊1/(2*δ)⌋₊ else ⌊(Q:ℝ)/(2*K)⌋₊ with hK'def
      have hK'1 : 1 ≤ K' := by
        rw [hK'def]; split
        · exact one_le_floor_half δ hδ0 hδ12
        · exact one_le_floor_QK Q K hKpos hQK
      have hK'q : (K':ℝ) ≤ (Q:ℝ)/(2*K) := by
        rw [hK'def]; split
        · rename_i hc
          exact le_trans (by exact_mod_cast hc) (Nat.floor_le (by positivity))
        · exact Nat.floor_le (by positivity)
      have hδK' : δ ≤ 1/(2*(K':ℝ)) := by
        rw [hK'def]; split
        · have hp : (0:ℝ) < ((⌊1/(2*δ)⌋₊ : ℕ):ℝ) := by
            have h : (1:ℝ) ≤ ((⌊1/(2*δ)⌋₊ : ℕ):ℝ) := by exact_mod_cast (one_le_floor_half δ hδ0 hδ12)
            linarith
          have hle : ((⌊1/(2*δ)⌋₊ : ℕ) : ℝ) ≤ 1/(2*δ) := Nat.floor_le (by positivity)
          rw [le_div_iff₀ (by linarith : (0:ℝ) < 2*((⌊1/(2*δ)⌋₊ : ℕ):ℝ))]
          rw [le_div_iff₀ (by positivity : (0:ℝ) < 2*δ)] at hle
          nlinarith [hle]
        · rename_i hc
          have hlt : ((⌊(Q:ℝ)/(2*K)⌋₊ : ℕ) : ℝ) < 1/(2*δ) := by
            have h1 : ((⌊(Q:ℝ)/(2*K)⌋₊ : ℕ) : ℝ) < ((⌊1/(2*δ)⌋₊ : ℕ) : ℝ) := by
              exact_mod_cast (lt_of_not_ge hc)
            have h2 : ((⌊1/(2*δ)⌋₊ : ℕ) : ℝ) ≤ 1/(2*δ) := Nat.floor_le (by positivity)
            linarith
          have hp : (0:ℝ) < ((⌊(Q:ℝ)/(2*K)⌋₊ : ℕ):ℝ) := by
            have h : (1:ℝ) ≤ ((⌊(Q:ℝ)/(2*K)⌋₊ : ℕ):ℝ) := by exact_mod_cast (one_le_floor_QK Q K hKpos hQK)
            linarith
          rw [lt_div_iff₀ (by positivity : (0:ℝ) < 2*δ)] at hlt
          rw [le_div_iff₀ (by linarith : (0:ℝ) < 2*((⌊(Q:ℝ)/(2*K)⌋₊ : ℕ):ℝ))]
          nlinarith [hlt, hδ0]
      have hinv : (1:ℝ)/(K':ℝ) ≤ 4*δ + 4*K/(Q:ℝ) := by
        rw [hK'def]; split
        · have := inv_floor_half_le δ hδ0 hδ12
          linarith [show (0:ℝ) ≤ 4*K/(Q:ℝ) by positivity]
        · have := inv_floor_QK_le Q hQ K hKpos hQK
          linarith [show (0:ℝ) ≤ 4*δ by positivity]
      have h1 := fejer_count_le b Q hQ hg α β K hK hb R δ hδ0 K' hK'1 hδK' hK'q
      have h2 := sum_min_le b Q hQ hg α K hK hb R K' hK'1 hK'q (by
        have h1 : (0:ℝ) ≤ (R:ℝ) := Nat.cast_nonneg R
        have h2 : (0:ℝ) ≤ (Q:ℝ) := Nat.cast_nonneg Q
        have h1' : (0:ℝ) ≤ (R:ℝ) := Nat.cast_nonneg R
        have h2' : (0:ℝ) ≤ (Q:ℝ) := Nat.cast_nonneg Q
        have h3 : Real.log (R:ℝ) ≤ Real.log (2 + (R:ℝ) + (Q:ℝ)) := log_le_log_Lg R Q
        linarith [h3])
      -- combine
      have hstep : (((Finset.Icc 1 R).filter (fun (n:ℕ) => dz ((n:ℝ)*α+β) ≤ δ)).card : ℝ)
          ≤ (Real.pi^2/(4*(K':ℝ))) * ((R:ℝ) + 2*(2*(R:ℝ) + (K':ℝ) + 2*(Q:ℝ)*Lg)) := by
        calc _ ≤ (Real.pi^2/(4*(K':ℝ))) * ((R:ℝ) + 2 * ∑ m ∈ Finset.Icc 1 (K'-1),
                min (R:ℝ) (1/(2*dz ((m:ℝ)*α)))) := h1
          _ ≤ (Real.pi^2/(4*(K':ℝ))) * ((R:ℝ) + 2*(2*(R:ℝ) + (K':ℝ) + 2*(Q:ℝ)*Lg)) := by
              apply mul_le_mul_of_nonneg_left _ (by positivity)
              linarith [h2]
      have hRQL1 : 1 ≤ (R:ℝ) + (Q:ℝ)*Lg := by
        have h1 : (1:ℝ) ≤ (Q:ℝ)*Lg := by nlinarith [hLg1, hQpos]
        have h2 : (0:ℝ) ≤ (R:ℝ) := Nat.cast_nonneg R
        linarith
      have hK'pos : (0:ℝ) < K' := lt_of_lt_of_le zero_lt_one (by exact_mod_cast hK'1)
      have hA : ((R:ℝ) + 2*(2*(R:ℝ) + (K':ℝ) + 2*(Q:ℝ)*Lg))/(K':ℝ)
          = (5*(R:ℝ) + 4*(Q:ℝ)*Lg)/(K':ℝ) + 2 := by
        have hne : (K':ℝ) ≠ 0 := ne_of_gt hK'pos
        field_simp
        ring
      have hB : (5*(R:ℝ) + 4*(Q:ℝ)*Lg)/(K':ℝ)
          ≤ (4*δ + 4*K/(Q:ℝ))*(5*(R:ℝ) + 4*(Q:ℝ)*Lg) := by
        have hinv' : (K':ℝ)⁻¹ ≤ 4*δ + 4*K/(Q:ℝ) := by
          have h := hinv
          rwa [one_div] at h
        calc (5*(R:ℝ) + 4*(Q:ℝ)*Lg)/(K':ℝ)
            = (5*(R:ℝ) + 4*(Q:ℝ)*Lg) * (K':ℝ)⁻¹ := by rw [div_eq_mul_inv]
          _ ≤ (5*(R:ℝ) + 4*(Q:ℝ)*Lg) * (4*δ + 4*K/(Q:ℝ)) :=
              mul_le_mul_of_nonneg_left hinv' (by positivity)
          _ = (4*δ + 4*K/(Q:ℝ))*(5*(R:ℝ) + 4*(Q:ℝ)*Lg) := by ring
      have hXnn : (0:ℝ) ≤ (5*(R:ℝ) + 4*(Q:ℝ)*Lg) := by positivity
      have hpi4 : Real.pi^2/4 ≤ 4 := by nlinarith [Real.pi_lt_four, Real.pi_pos]
      have hth : (Real.pi^2/(4*(K':ℝ))) * ((R:ℝ) + 2*(2*(R:ℝ) + (K':ℝ) + 2*(Q:ℝ)*Lg))
          = (Real.pi^2/4) * ((5*(R:ℝ) + 4*(Q:ℝ)*Lg)/(K':ℝ) + 2) := by
        have hne : (K':ℝ) ≠ 0 := ne_of_gt hK'pos
        field_simp
        ring
      rw [hth] at hstep
      have hbig : (Real.pi^2/4) * ((5*(R:ℝ) + 4*(Q:ℝ)*Lg)/(K':ℝ) + 2)
          ≤ 4 * ((4*δ + 4*K/(Q:ℝ))*(5*(R:ℝ) + 4*(Q:ℝ)*Lg) + 2) := by
        have h2 : (5*(R:ℝ) + 4*(Q:ℝ)*Lg)/(K':ℝ) + 2
            ≤ (4*δ + 4*K/(Q:ℝ))*(5*(R:ℝ) + 4*(Q:ℝ)*Lg) + 2 := by linarith [hB]
        calc (Real.pi^2/4) * ((5*(R:ℝ) + 4*(Q:ℝ)*Lg)/(K':ℝ) + 2)
            ≤ 4 * ((5*(R:ℝ) + 4*(Q:ℝ)*Lg)/(K':ℝ) + 2) :=
              mul_le_mul_of_nonneg_right hpi4 (by positivity)
          _ ≤ 4 * ((4*δ + 4*K/(Q:ℝ))*(5*(R:ℝ) + 4*(Q:ℝ)*Lg) + 2) :=
              mul_le_mul_of_nonneg_left h2 (by norm_num)
      have hKLg : (1:ℝ) ≤ K*Lg := by nlinarith [hK, hLg1]
      have hfin : 4 * ((4*δ + 4*K/(Q:ℝ))*(5*(R:ℝ) + 4*(Q:ℝ)*Lg) + 2)
          ≤ 1000 * (δ * ((R:ℝ) + (Q:ℝ)*Lg) + K * ((R:ℝ)/(Q:ℝ) + Lg)) := by
        have hR0 : (0:ℝ) ≤ (R:ℝ) := Nat.cast_nonneg R
        have hQ0 : (0:ℝ) ≤ (Q:ℝ) := Nat.cast_nonneg Q
        have hRQ : (0:ℝ) ≤ (R:ℝ)/(Q:ℝ) := by positivity
        have hexp : (4:ℝ) * ((4*δ + 4*K/(Q:ℝ))*(5*(R:ℝ) + 4*(Q:ℝ)*Lg) + 2)
            = 80*δ*(R:ℝ) + 64*δ*((Q:ℝ)*Lg) + 80*K*((R:ℝ)/(Q:ℝ)) + 64*K*Lg + 8 := by
          have hQne : (Q:ℝ) ≠ 0 := ne_of_gt hQpos
          field_simp
          ring
        rw [hexp]
        nlinarith [hKLg, hδ0, hR0, hQ0, hRQ, hKpos, hQpos, hLg1,
          mul_nonneg (le_of_lt hδ0) hR0, mul_nonneg (le_of_lt hδ0) hQ0,
          mul_nonneg (le_of_lt hδ0) (le_trans zero_le_one hLg1),
          mul_nonneg (mul_nonneg (le_of_lt hδ0) hQ0) (le_trans zero_le_one hLg1)]
      linarith [hstep, hbig, hfin]
    · push_neg at hQK
      have hcard : (((Finset.Icc 1 R).filter (fun (n:ℕ) => dz ((n:ℝ)*α+β) ≤ δ)).card : ℝ) ≤ (R:ℝ) := by
        have h := Finset.card_filter_le (Finset.Icc 1 R) (fun (n:ℕ) => dz ((n:ℝ)*α+β) ≤ δ)
        rw [Nat.card_Icc] at h
        have h2 : R+1-1 = R := by omega
        rw [h2] at h
        exact_mod_cast h
      have hRQ : (R:ℝ) ≤ 2*K*((R:ℝ)/(Q:ℝ)) := by
        rw [show (2:ℝ)*K*((R:ℝ)/(Q:ℝ)) = (2*K*(R:ℝ))/(Q:ℝ) by ring, le_div_iff₀ hQpos]
        have hR0 : (0:ℝ) ≤ R := Nat.cast_nonneg R
        nlinarith [hQK, hR0]
      have h1 : (R:ℝ) ≤ 1000 * (K * ((R:ℝ)/(Q:ℝ) + Lg)) := by
        have hk : K*((R:ℝ)/(Q:ℝ)) ≤ K*((R:ℝ)/(Q:ℝ) + Lg) := by
          apply mul_le_mul_of_nonneg_left _ (le_of_lt hKpos); linarith [hLg1]
        nlinarith [hRQ, hk, hKpos, hLg1]
      linarith [hcard, h1, show (0:ℝ) ≤ δ*((R:ℝ)+(Q:ℝ)*Lg) by positivity]
  ·
    have hcard : (((Finset.Icc 1 R).filter (fun (n:ℕ) => dz ((n:ℝ)*α+β) ≤ δ)).card : ℝ) ≤ (R:ℝ) := by
      have h := Finset.card_filter_le (Finset.Icc 1 R) (fun (n:ℕ) => dz ((n:ℝ)*α+β) ≤ δ)
      rw [Nat.card_Icc] at h
      have h2 : R+1-1 = R := by omega
      rw [h2] at h
      exact_mod_cast h
    have hgoal : (R:ℝ) ≤ 1000 * (δ * ((R:ℝ) + (Q:ℝ)*Lg) + K * ((R:ℝ)/(Q:ℝ) + Lg)) := by
      have hhalf : (1:ℝ)/2 ≤ δ := by
        have h := lt_of_not_ge hδ12
        linarith
      have hR0 : (0:ℝ) ≤ (R:ℝ) := Nat.cast_nonneg R
      have hsum0 : (0:ℝ) ≤ (R:ℝ) + (Q:ℝ)*Lg := by positivity
      have h1 : (R:ℝ) ≤ 1000 * ((1:ℝ)/2 * ((R:ℝ) + (Q:ℝ)*Lg)) := by nlinarith [hR0, hsum0]
      have h2 : (1:ℝ)/2 * ((R:ℝ) + (Q:ℝ)*Lg) ≤ δ * ((R:ℝ) + (Q:ℝ)*Lg) :=
        mul_le_mul_of_nonneg_right hhalf hsum0
      have h3 : (0:ℝ) ≤ K * ((R:ℝ)/(Q:ℝ) + Lg) := by positivity
      calc (R:ℝ) ≤ 1000 * ((1:ℝ)/2 * ((R:ℝ) + (Q:ℝ)*Lg)) := h1
        _ ≤ 1000 * (δ * ((R:ℝ) + (Q:ℝ)*Lg)) := by
            exact mul_le_mul_of_nonneg_left h2 (by norm_num)
        _ ≤ 1000 * (δ * ((R:ℝ) + (Q:ℝ)*Lg) + K * ((R:ℝ)/(Q:ℝ) + Lg)) := by
            exact mul_le_mul_of_nonneg_left (by linarith) (by norm_num)
    linarith [hcard, hgoal]

/-! ## The reciprocal weight and the geometric sum bound -/

lemma dz_nonneg (x : ℝ) : 0 ≤ dz x := abs_nonneg _

lemma dz_eq_zero_iff (x : ℝ) : dz x = 0 ↔ ∃ z : ℤ, x = (z:ℝ) := by
  constructor
  · intro h
    have h1 : x - (round x : ℝ) = 0 := abs_eq_zero.mp h
    exact ⟨round x, by push_cast; linarith⟩
  · rintro ⟨z, rfl⟩
    rw [dz, round_intCast]; simp

/-- The reciprocal-type weight: it dominates `min (N, 1/(2 dz u))` and equals `N` when `dz u = 0`. -/
noncomputable def rho (u : ℝ) (N : ℕ) : ℝ := min (N:ℝ) (1/(2*max (dz u) (1/(2*(N:ℝ)))))

lemma rho_nonneg (u : ℝ) (N : ℕ) : 0 ≤ rho u N := by
  unfold rho; exact le_min (Nat.cast_nonneg N) (by positivity)

lemma rho_le_N (u : ℝ) (N : ℕ) : rho u N ≤ (N:ℝ) := min_le_left _ _

lemma norm_geom_range_le (L : ℕ) {z : ℂ} (hz : z ≠ 1) (hzn : ‖z‖ = 1) :
    ‖∑ x ∈ Finset.range L, z^x‖ ≤ 2/‖1 - z‖ := by
  have hgeom : (1 - z) * ∑ x ∈ Finset.range L, z^x = 1 - z^L := by
    have h := geom_sum_mul z L
    rw [show (1 - z) * ∑ x ∈ Finset.range L, z^x
          = -((∑ x ∈ Finset.range L, z^x) * (z - 1)) by ring, h]
    ring
  have h1 : ‖(1 - z) * ∑ x ∈ Finset.range L, z^x‖ ≤ 2 := by
    rw [hgeom]
    calc ‖1 - z^L‖ ≤ ‖(1:ℂ)‖ + ‖z^L‖ := norm_sub_le _ _
      _ ≤ 2 := by
          rw [norm_one, norm_pow, hzn, one_pow]
          norm_num
  have h1z : 0 < ‖1 - z‖ := norm_pos_iff.mpr (sub_ne_zero.mpr hz.symm)
  rw [norm_mul] at h1
  rw [le_div_iff₀ h1z]
  rw [mul_comm]
  exact h1

lemma geom_sum_range_pe_le (L : ℕ) (β γ : ℝ) (hβ : 0 < dz β) :
    ‖∑ x ∈ Finset.range L, pe (β * (x:ℝ) + γ)‖ ≤ min (L:ℝ) (1/(2*dz β)) := by
  have hterm : ∀ x : ℕ, pe (β * (x:ℝ) + γ) = pe γ * (pe β)^x := by
    intro x
    rw [show β * (x:ℝ) + γ = γ + (x:ℝ)*β by ring, pe_add, pe_nat, mul_comm]
  rw [Finset.sum_congr rfl (fun x _ => hterm x), ← Finset.mul_sum]
  rw [norm_mul, pe_norm, one_mul]
  refine le_min ?_ ?_
  · calc ‖∑ x ∈ Finset.range L, (pe β)^x‖ ≤ ∑ x ∈ Finset.range L, ‖(pe β)^x‖ := norm_sum_le _ _
      _ = (L:ℝ) := by simp [norm_pow, pe_norm]
  · have hz1 : pe β ≠ 1 := fun h => absurd (pe_eq_one_imp_dz_zero β h) (ne_of_gt hβ)
    have h4 : 4 * dz β ≤ ‖1 - pe β‖ := by
      rw [norm_sub_rev]; exact four_dz_le β
    have h2 : ‖∑ x ∈ Finset.range L, (pe β)^x‖ ≤ 2/‖1 - pe β‖ :=
      norm_geom_range_le L hz1 (pe_norm β)
    have h4pos : 0 < ‖1 - pe β‖ := by linarith [h4, hβ]
    have : 2/‖1 - pe β‖ ≤ 1/(2*dz β) := by
      rw [div_le_div_iff₀ h4pos (by linarith : (0:ℝ) < 2*dz β)]
      linarith [h4]
    linarith [h2, this]

lemma geom_sum_range_pe_le_rho (L N : ℕ) (hLN : L ≤ N) (hN : 1 ≤ N) (β γ : ℝ) :
    ‖∑ x ∈ Finset.range L, pe (β * (x:ℝ) + γ)‖ ≤ rho β N := by
  by_cases h0 : dz β = 0
  · have h1 : ∀ x : ℕ, pe (β * (x:ℝ) + γ) = pe γ := by
      intro x
      have hb : pe (β * (x:ℝ)) = 1 := by
        obtain ⟨z, rfl⟩ := (dz_eq_zero_iff β).mp h0
        rw [show ((z:ℝ)*(x:ℝ)) = ((z*(x:ℤ):ℤ):ℝ) by push_cast; ring]
        unfold pe
        rw [show (↑(2*Real.pi*((z*(x:ℤ):ℤ):ℝ)):ℂ)*Complex.I
              = ((z*(x:ℤ):ℤ):ℂ) * (2*(↑Real.pi:ℂ)*Complex.I) by push_cast; ring]
        rw [Complex.exp_int_mul_two_pi_mul_I]
      rw [pe_add, hb, one_mul]
    rw [Finset.sum_congr rfl (fun x _ => h1 x), Finset.sum_const, Finset.card_range,
      nsmul_eq_mul, norm_mul, pe_norm, mul_one, Complex.norm_natCast]
    have hN : rho β N = (N:ℝ) := by
      unfold rho
      rw [h0, max_eq_right (by positivity)]
      have : (1:ℝ)/(2*(1/(2*(N:ℝ)))) = (N:ℝ) := by field_simp
      rw [this, min_self]
    rw [hN]; exact_mod_cast hLN
  · have hpos : 0 < dz β := lt_of_le_of_ne (dz_nonneg β) (Ne.symm h0)
    by_cases h2 : (1:ℝ)/(2*(N:ℝ)) ≤ dz β
    · have hmax : max (dz β) (1/(2*(N:ℝ))) = dz β := max_eq_left h2
      have hN : rho β N = 1/(2*dz β) := by
        unfold rho; rw [hmax]
        apply min_eq_right
        rw [div_le_iff₀ (by positivity : (0:ℝ) < 2*(N:ℝ))] at h2
        rw [div_le_iff₀ (by linarith : (0:ℝ) < 2*dz β)]
        nlinarith [h2]
      rw [hN]
      exact le_trans (geom_sum_range_pe_le L β γ hpos) (min_le_right _ _)
    · have hmax : max (dz β) (1/(2*(N:ℝ))) = 1/(2*(N:ℝ)) :=
        max_eq_right (le_of_lt (lt_of_not_ge h2))
      have hN : rho β N = (N:ℝ) := by
        unfold rho
        rw [hmax]
        have : (1:ℝ)/(2*(1/(2*(N:ℝ)))) = (N:ℝ) := by field_simp
        rw [this, min_self]
      rw [hN]
      have h1 : ‖∑ x ∈ Finset.range L, pe (β * (x:ℝ) + γ)‖ ≤ (L:ℝ) := by
        calc ‖∑ x ∈ Finset.range L, pe (β * (x:ℝ) + γ)‖
            ≤ ∑ x ∈ Finset.range L, ‖pe (β * (x:ℝ) + γ)‖ := norm_sum_le _ _
          _ = (L:ℝ) := by simp [pe_norm]
      exact le_trans h1 (by exact_mod_cast hLN)

/-! ## Reducing the rational approximation to a coprime pair -/

lemma nat_coprime_of_dvd {m n c : ℕ} (hmn : m.Coprime n) (hc : c ∣ n) : m.Coprime c := by
  rw [Nat.coprime_iff_gcd_eq_one] at hmn ⊢
  have : Nat.gcd m c ∣ Nat.gcd m n :=
    Nat.dvd_gcd (Nat.gcd_dvd_left m c) (dvd_trans (Nat.gcd_dvd_right m c) hc)
  exact Nat.dvd_one.mp (by rwa [hmn] at this)

lemma exists_reduced (k : ℕ) {a q : ℤ} (hq : 1 ≤ q) (hgcd : Int.gcd a q = 1) :
    ∃ (b : ℤ) (Q : ℕ), 1 ≤ Q ∧ Int.gcd b (Q:ℤ) = 1 ∧ (Q:ℤ) ≤ q ∧
      ((k.factorial : ℝ) * (a:ℝ) / (q:ℝ) = (b:ℝ)/(Q:ℝ)) ∧
      ((q:ℝ)/(Q:ℝ) ≤ (k.factorial : ℝ)) := by
  set q₀ : ℕ := q.toNat with hq₀
  have hq0 : 0 < q₀ := by rw [hq₀]; omega
  have hqcast : (q₀ : ℤ) = q := Int.toNat_of_nonneg (by omega)
  have hqR : ((q₀:ℕ):ℝ) = (q:ℝ) := by
    have := congrArg (fun z : ℤ => (z:ℝ)) hqcast
    simpa using this
  set G : ℕ := Nat.gcd k.factorial q₀ with hG
  have hGpos : 0 < G := by rw [hG]; exact Nat.gcd_pos_of_pos_right _ hq0
  have hGk : G ∣ k.factorial := by rw [hG]; exact Nat.gcd_dvd_left _ _
  have hGq : G ∣ q₀ := by rw [hG]; exact Nat.gcd_dvd_right _ _
  refine ⟨((k.factorial / G : ℕ) : ℤ) * a, q₀ / G, ?_, ?_, ?_, ?_, ?_⟩
  · rw [Nat.one_le_div_iff hGpos]; exact Nat.le_of_dvd hq0 hGq
  · rw [Int.gcd_eq_natAbs]
    have h1 : (((k.factorial / G : ℕ) : ℤ) * a).natAbs = (k.factorial / G) * a.natAbs := by
      rw [Int.natAbs_mul, Int.natAbs_natCast]
    rw [h1, Int.natAbs_natCast]
    have h2 : Nat.Coprime (k.factorial / G) (q₀ / G) := Nat.coprime_div_gcd_div_gcd hGpos
    have h3 : Nat.Coprime a.natAbs (q₀ / G) := by
      apply nat_coprime_of_dvd _ (Nat.div_dvd_of_dvd hGq)
      rw [Nat.coprime_iff_gcd_eq_one]
      have h5 : Int.gcd a q = 1 := hgcd
      rw [Int.gcd_eq_natAbs] at h5
      have h6 : q.natAbs = q₀ := by
        conv_lhs => rw [← hqcast]
        exact Int.natAbs_natCast q₀
      rwa [h6] at h5
    exact Nat.Coprime.mul_left h2 h3
  · have h7 : (q₀ / G : ℕ) ≤ q₀ := Nat.div_le_self _ _
    have : ((q₀ / G : ℕ) : ℤ) ≤ (q₀:ℤ) := by exact_mod_cast h7
    rwa [hqcast] at this
  · have hb : ((((k.factorial / G : ℕ) : ℤ) * a : ℤ) : ℝ)
        = (((k.factorial / G : ℕ)) : ℝ) * (a:ℝ) := by
      simp only [Int.cast_mul, Int.cast_natCast]
    have hkG : (((k.factorial / G : ℕ)) : ℝ) = (k.factorial : ℝ)/(G:ℝ) :=
      Nat.cast_div hGk (by positivity)
    have hqG : (((q₀ / G : ℕ)) : ℝ) = (q₀:ℝ)/(G:ℝ) := Nat.cast_div hGq (by positivity)
    rw [← hqR]
    rw [hb, hkG, hqG]
    field_simp
  · have hqG : (((q₀ / G : ℕ)) : ℝ) = (q₀:ℝ)/(G:ℝ) := Nat.cast_div hGq (by positivity)
    rw [← hqR, hqG]
    have hGle : G ≤ k.factorial := Nat.le_of_dvd (Nat.factorial_pos k) hGk
    have : (q₀:ℝ)/((q₀:ℝ)/(G:ℝ)) = (G:ℝ) := by
      field_simp
    rw [this]
    exact_mod_cast hGle

/-- The counting bound for the frequency `k! * lc` where `lc` approximates `a/q`. -/
lemma count_le_approx (k : ℕ) {a q : ℤ} (hq : 1 ≤ q) (hgcd : Int.gcd a q = 1)
    {t lc δ : ℝ} (ht : 1 ≤ t) (hδ0 : 0 < δ) (hδ1 : δ ≤ 1)
    (hlc : |lc - (a:ℝ)/q| ≤ t/(q:ℝ)^2) (M : ℕ) :
    (((Finset.Icc 1 M).filter (fun m : ℕ => dz ((m:ℝ)*((k.factorial:ℝ)*lc)) ≤ δ)).card : ℝ)
      ≤ 1000*(δ*((M:ℝ) + (q:ℝ)*(1 + Real.log (2 + (M:ℝ) + (q:ℝ))))
          + ((k.factorial:ℝ)*t)*((M:ℝ)*(k.factorial:ℝ)/(q:ℝ)
              + 1 + Real.log (2 + (M:ℝ) + (q:ℝ)))) := by
  obtain ⟨b, Q, hQ1, hgcdb, hQq, hident, hratio⟩ := exists_reduced k hq hgcd
  have hQpos : (0:ℝ) < (Q:ℝ) := by exact_mod_cast hQ1
  have hqpos : (0:ℝ) < (q:ℝ) := by exact_mod_cast hq
  have hK : (1:ℝ) ≤ (k.factorial:ℝ)*t := by
    have h1 : (1:ℝ) ≤ (k.factorial:ℝ) := by
      exact_mod_cast (Nat.factorial_pos k)  -- hmm: factorial_pos gives 0 < k! 
    nlinarith [ht, h1]
  have hα : |((k.factorial:ℝ)*lc) - (b:ℝ)/(Q:ℝ)| ≤ ((k.factorial:ℝ)*t)/(Q:ℝ)^2 := by
    have h1 : (k.factorial:ℝ)*lc - (b:ℝ)/(Q:ℝ) = (k.factorial:ℝ)*(lc - (a:ℝ)/q) := by
      rw [← hident]; ring
    rw [h1, abs_mul]
    have h2 : |(k.factorial:ℝ)| = (k.factorial:ℝ) := abs_of_nonneg (by positivity)
    rw [h2]
    have hQle : (Q:ℝ) ≤ (q:ℝ) := by exact_mod_cast hQq
    have h3 : (q:ℝ)^2 ≥ (Q:ℝ)^2 := by nlinarith
    have h4 : t/(q:ℝ)^2 ≤ t/(Q:ℝ)^2 := by
      rw [div_le_div_iff₀ (by positivity) (by positivity)]
      nlinarith [ht, h3]
    calc (k.factorial:ℝ) * |lc - (a:ℝ)/q| ≤ (k.factorial:ℝ) * (t/(q:ℝ)^2) :=
          mul_le_mul_of_nonneg_left hlc (by positivity)
      _ ≤ (k.factorial:ℝ) * (t/(Q:ℝ)^2) := mul_le_mul_of_nonneg_left h4 (by positivity)
      _ = ((k.factorial:ℝ)*t)/(Q:ℝ)^2 := by ring
  have hbound := rho_bound ((k.factorial:ℝ)*t) hK ((k.factorial:ℝ)*lc) 0 Q b hQ1 hgcdb hα M δ hδ0 hδ1
  simp only [add_zero] at hbound
  have hLg : (1:ℝ) + Real.log (2 + (M:ℝ) + (Q:ℝ)) ≤ 1 + Real.log (2 + (M:ℝ) + (q:ℝ)) := by
    have h1 : Real.log (2 + (M:ℝ) + (Q:ℝ)) ≤ Real.log (2 + (M:ℝ) + (q:ℝ)) := by
      apply Real.log_le_log (by positivity)
      have : (Q:ℝ) ≤ (q:ℝ) := by exact_mod_cast hQq
      linarith
    linarith
  have hLg0' : (0:ℝ) ≤ 1 + Real.log (2 + (M:ℝ) + (Q:ℝ)) := by
    have h1 : (1:ℝ) ≤ 2 + (M:ℝ) + (Q:ℝ) := by
      have h2 : (1:ℝ) ≤ (Q:ℝ) := by exact_mod_cast hQ1
      have h3 : (0:ℝ) ≤ (M:ℝ) := Nat.cast_nonneg M
      linarith
    linarith [Real.log_nonneg h1]
  have hprod : (Q:ℝ)*(1 + Real.log (2 + (M:ℝ) + (Q:ℝ)))
      ≤ (q:ℝ)*(1 + Real.log (2 + (M:ℝ) + (q:ℝ))) :=
    mul_le_mul (by exact_mod_cast hQq) hLg hLg0' (by positivity)
  have hMQ : (M:ℝ)/(Q:ℝ) ≤ (M:ℝ)*(k.factorial:ℝ)/(q:ℝ) := by
    have h1 : (1:ℝ)/(Q:ℝ) ≤ (k.factorial:ℝ)/(q:ℝ) := by
      rw [div_le_div_iff₀ hQpos hqpos]
      rw [div_le_iff₀ hQpos] at hratio
      linarith [hratio]
    have h2 : (M:ℝ)/(Q:ℝ) = (M:ℝ)*((1:ℝ)/(Q:ℝ)) := by ring
    rw [h2, show (M:ℝ)*(k.factorial:ℝ)/(q:ℝ) = (M:ℝ)*((k.factorial:ℝ)/(q:ℝ)) by ring]
    exact mul_le_mul_of_nonneg_left h1 (Nat.cast_nonneg M)
  have h1 : δ*((M:ℝ) + (Q:ℝ)*(1 + Real.log (2 + (M:ℝ) + (Q:ℝ))))
      ≤ δ*((M:ℝ) + (q:ℝ)*(1 + Real.log (2 + (M:ℝ) + (q:ℝ)))) := by
    apply mul_le_mul_of_nonneg_left _ (le_of_lt hδ0)
    linarith [hprod]
  have h2 : ((M:ℝ)/(Q:ℝ) + 1 + Real.log (2 + (M:ℝ) + (Q:ℝ)))
      ≤ (M:ℝ)*(k.factorial:ℝ)/(q:ℝ) + 1 + Real.log (2 + (M:ℝ) + (q:ℝ)) := by
    linarith [hMQ, hLg]
  have hK0 : (0:ℝ) ≤ (k.factorial:ℝ)*t := by positivity
  have hmain : (1000:ℝ)*(δ*((M:ℝ) + (Q:ℝ)*(1 + Real.log (2 + (M:ℝ) + (Q:ℝ))))
          + ((k.factorial:ℝ)*t)*((M:ℝ)/(Q:ℝ) + 1 + Real.log (2 + (M:ℝ) + (Q:ℝ))))
      ≤ 1000*(δ*((M:ℝ) + (q:ℝ)*(1 + Real.log (2 + (M:ℝ) + (q:ℝ))))
          + ((k.factorial:ℝ)*t)*((M:ℝ)*(k.factorial:ℝ)/(q:ℝ)
              + 1 + Real.log (2 + (M:ℝ) + (q:ℝ)))) := by
    nlinarith [h1, h2, hK0, hδ0]
  exact le_trans hbound hmain


/-! ## Weyl differencing for incomplete sums -/

noncomputable def cw : ℕ → ℝ
  | 0 => 1
  | (n+1) => 2 * (cw n)^2

lemma cw_pos (r : ℕ) : 0 < cw r := by
  induction r with
  | zero => rw [cw]; norm_num
  | succ r ih => rw [cw]; positivity

noncomputable def Gsum (ψ : ℤ → ℝ) (r : ℕ) (L : ℕ) (h : Fin r → ℕ) : ℂ :=
  ∑ x ∈ Finset.range (L - ∑ i, h i), Ephase (iterDiff ψ r (fun i => (h i : ℤ))) (x : ℤ)

lemma iterDiff_snoc (g : ℤ → ℝ) (r : ℕ) (h : Fin r → ℤ) (d : ℤ) :
    iterDiff g (r+1) (Fin.snoc (α := fun _ => ℤ) h d)
      = fun x => iterDiff g r h (x + d) - iterDiff g r h x := by
  have hfun : (fun i : Fin r => (Fin.snoc (α := fun _ => ℤ) h d) i.castSucc) = h := by
    funext i; rw [Fin.snoc_castSucc]
  funext x
  show iterDiff g r (fun i => (Fin.snoc (α := fun _ => ℤ) h d) i.castSucc)
        (x + (Fin.snoc (α := fun _ => ℤ) h d) (Fin.last r))
      - iterDiff g r (fun i => (Fin.snoc (α := fun _ => ℤ) h d) i.castSucc) x
      = iterDiff g r h (x + d) - iterDiff g r h x
  rw [hfun, Fin.snoc_last]

lemma star_Ephase (ψ : ℤ → ℝ) (x : ℤ) :
    star (Ephase ψ x) = conj (Ephase ψ x) := rfl

lemma sum_snoc_nat {r : ℕ} (h : Fin r → ℕ) (d : ℕ) :
    (∑ i : Fin (r+1), Fin.snoc (α := fun _ => ℕ) h d i) = (∑ i : Fin r, h i) + d := by
  rw [Fin.sum_univ_castSucc]
  congr 1
  · apply Finset.sum_congr rfl
    intro i _
    rw [Fin.snoc_castSucc]
  · rw [Fin.snoc_last]

lemma Gsum_step (ψ : ℤ → ℝ) (r : ℕ) (L : ℕ) (h : Fin r → ℕ) :
    ‖Gsum ψ r L h‖ ^ 2 ≤ 2 * ∑ d ∈ Finset.range L, ‖Gsum ψ (r+1) L (Fin.snoc h d)‖ := by
  have h1 := iterated_differencing_step (L - ∑ i, h i)
    (fun x : ℕ => Ephase (iterDiff ψ r (fun i => (h i : ℤ))) (x : ℤ))
  simp only [Gsum] at h1 ⊢
  refine le_trans h1 ?_
  have hkey : ∀ d : ℕ, (∑ x ∈ Finset.range (L - ∑ i, h i - d),
        Ephase (iterDiff ψ r (fun i => (h i : ℤ))) ((x + d : ℕ) : ℤ) *
          star (Ephase (iterDiff ψ r (fun i => (h i : ℤ))) (x : ℤ)))
      = Gsum ψ (r+1) L (Fin.snoc (α := fun _ => ℕ) h d) := by
    intro d
    simp only [Gsum]
    have hrange : L - ∑ i, Fin.snoc (α := fun _ => ℕ) h d i = L - ∑ i, h i - d := by
      rw [sum_snoc_nat]
      omega
    have hphase : (fun i => ((Fin.snoc (α := fun _ => ℕ) h d) i : ℤ))
        = Fin.snoc (α := fun _ => ℤ) (fun i => (h i : ℤ)) (d : ℤ) := by
      funext i
      induction i using Fin.lastCases with
      | cast j => rw [Fin.snoc_castSucc, Fin.snoc_castSucc]
      | last => rw [Fin.snoc_last, Fin.snoc_last]
    rw [hrange, hphase]
    apply Finset.sum_congr rfl
    intro x _
    rw [show ((x + d : ℕ) : ℤ) = (x:ℤ) + (d:ℤ) by push_cast; ring]
    rw [star_Ephase]
    rw [show Ephase (iterDiff ψ r (fun i => (h i : ℤ))) ((x:ℤ) + (d:ℤ))
          * conj (Ephase (iterDiff ψ r (fun i => (h i : ℤ))) (x:ℤ))
        = shConj (d:ℤ) (Ephase (iterDiff ψ r (fun i => (h i : ℤ)))) (x:ℤ) from rfl]
    rw [shConj_Ephase]
    rw [show (fun y => iterDiff ψ r (fun i => (h i : ℤ)) (y + (d:ℤ))
          - iterDiff ψ r (fun i => (h i : ℤ)) y)
        = iterDiff ψ (r+1) (Fin.snoc (α := fun _ => ℤ) (fun i => (h i : ℤ)) (d:ℤ)) by
      rw [iterDiff_snoc]]
  have hL : ∑ h_1 ∈ Finset.range (L - ∑ i, h i),
        ‖∑ x ∈ Finset.range (L - ∑ i, h i - h_1),
          Ephase (iterDiff ψ r (fun i => (h i : ℤ))) ((x + h_1 : ℕ) : ℤ)
            * star (Ephase (iterDiff ψ r (fun i => (h i : ℤ))) (x : ℤ))‖
      = ∑ h_1 ∈ Finset.range (L - ∑ i, h i),
          ‖Gsum ψ (r+1) L (Fin.snoc (α := fun _ => ℕ) h h_1)‖ := by
    apply Finset.sum_congr rfl
    intro d _
    rw [hkey d]
  rw [hL]
  apply mul_le_mul_of_nonneg_left _ (by norm_num)
  apply Finset.sum_le_sum_of_subset_of_nonneg
  · intro d hd
    simp only [Finset.mem_range] at hd ⊢
    omega
  · intro d _ _; positivity

lemma two_pow_pred_le (r : ℕ) : r + 1 ≤ 2^r := by
  induction r with
  | zero => simp
  | succ r ih => rw [pow_succ]; omega

lemma diff_iter (ψ : ℤ → ℝ) (r : ℕ) (L : ℕ) :
    ‖∑ x ∈ Finset.range L, Ephase ψ (x:ℤ)‖ ^ (2^r)
      ≤ cw r * (L:ℝ)^(2^r - r - 1)
          * ∑ h : Fin r → Fin L, ‖Gsum ψ r L (fun i => ((h i : Fin L) : ℕ))‖ := by
  induction r with
  | zero =>
      have hconst : ∀ h : Fin 0 → Fin L,
          Gsum ψ 0 L (fun i => ((h i : Fin L) : ℕ)) = ∑ x ∈ Finset.range L, Ephase ψ (x:ℤ) := by
        intro h
        simp only [Gsum]
        have : (∑ i : Fin 0, ((h i : Fin L) : ℕ)) = 0 := by simp
        rw [this, Nat.sub_zero]
        rfl
      have h1 : ∀ h ∈ (Finset.univ : Finset (Fin 0 → Fin L)),
          ‖Gsum ψ 0 L (fun i => ((h i : Fin L) : ℕ))‖ = ‖∑ x ∈ Finset.range L, Ephase ψ (x:ℤ)‖ := by
        intro h _
        rw [hconst h]
      rw [Finset.sum_congr rfl h1, Finset.sum_const]
      simp [cw]
  | succ r ih =>
      have hCS : (∑ h : Fin r → Fin L, ‖Gsum ψ r L (fun i => ((h i : Fin L) : ℕ))‖)^2
          ≤ (L:ℝ)^r * ∑ h : Fin r → Fin L, ‖Gsum ψ r L (fun i => ((h i : Fin L) : ℕ))‖^2 := by
        have := sq_sum_le_card_mul_sum_sq (s := (Finset.univ : Finset (Fin r → Fin L)))
          (f := fun h : Fin r → Fin L => ‖Gsum ψ r L (fun i => ((h i : Fin L) : ℕ))‖)
        rw [Finset.card_univ, Fintype.card_fun, Fintype.card_fin, Fintype.card_fin] at this
        simpa [Nat.cast_pow] using this
      have hstep : ∑ h : Fin r → Fin L, ‖Gsum ψ r L (fun i => ((h i : Fin L) : ℕ))‖^2
          ≤ 2 * ∑ h : Fin (r+1) → Fin L, ‖Gsum ψ (r+1) L (fun i => ((h i : Fin L) : ℕ))‖ := by
        rw [sum_fun_succ (F := fun h : Fin (r+1) → Fin L =>
          ‖Gsum ψ (r+1) L (fun i => ((h i : Fin L) : ℕ))‖)]
        rw [Finset.mul_sum]
        apply Finset.sum_le_sum
        intro h _
        have h2 := Gsum_step ψ r L (fun i => ((h i : Fin L) : ℕ))
        have hconv : (∑ j : Fin L, ‖Gsum ψ (r+1) L (fun i => ((Fin.snoc (α := fun _ : Fin (r+1) => Fin L) h j i : Fin L) : ℕ))‖)
            = ∑ d ∈ Finset.range L, ‖Gsum ψ (r+1) L (Fin.snoc (α := fun _ => ℕ) (fun i => ((h i : Fin L) : ℕ)) d)‖ := by
          rw [← Fin.sum_univ_eq_sum_range (f := fun d : ℕ =>
            ‖Gsum ψ (r+1) L (Fin.snoc (α := fun _ => ℕ) (fun i => ((h i : Fin L) : ℕ)) d)‖)]
          apply Finset.sum_congr rfl
          intro j _
          congr 2
          funext i
          induction i using Fin.lastCases with
          | cast k => rw [Fin.snoc_castSucc, Fin.snoc_castSucc]
          | last => rw [Fin.snoc_last, Fin.snoc_last]
        rw [← hconv] at h2
        linarith [h2]
      have hexp := two_pow_succ_sub r
      have hSpow : ‖∑ x ∈ Finset.range L, Ephase ψ (x:ℤ)‖ ^ (2^(r+1))
          = (‖∑ x ∈ Finset.range L, Ephase ψ (x:ℤ)‖ ^ (2^r))^2 := by
        rw [← pow_mul, pow_succ]
      rw [hSpow]
      calc (‖∑ x ∈ Finset.range L, Ephase ψ (x:ℤ)‖ ^ (2^r))^2
          ≤ (cw r * (L:ℝ)^(2^r - r - 1)
              * ∑ h : Fin r → Fin L, ‖Gsum ψ r L (fun i => ((h i : Fin L) : ℕ))‖)^2 :=
            pow_le_pow_left₀ (by positivity) ih 2
        _ = (cw r)^2 * ((L:ℝ)^(2^r - r - 1))^2
              * (∑ h : Fin r → Fin L, ‖Gsum ψ r L (fun i => ((h i : Fin L) : ℕ))‖)^2 := by ring
        _ ≤ (cw r)^2 * ((L:ℝ)^(2^r - r - 1))^2
              * ((L:ℝ)^r * ∑ h : Fin r → Fin L, ‖Gsum ψ r L (fun i => ((h i : Fin L) : ℕ))‖^2) := by
            apply mul_le_mul_of_nonneg_left hCS
            positivity
        _ = (cw r)^2 * ((L:ℝ)^((2^r - r - 1) * 2) * (L:ℝ)^r)
              * ∑ h : Fin r → Fin L, ‖Gsum ψ r L (fun i => ((h i : Fin L) : ℕ))‖^2 := by
            rw [← pow_mul]; ring
        _ = (cw r)^2 * (L:ℝ)^((2^r - r - 1) * 2 + r)
              * ∑ h : Fin r → Fin L, ‖Gsum ψ r L (fun i => ((h i : Fin L) : ℕ))‖^2 := by
            rw [← pow_add]
        _ ≤ (cw r)^2 * (L:ℝ)^((2^r - r - 1) * 2 + r)
              * (2 * ∑ h : Fin (r+1) → Fin L, ‖Gsum ψ (r+1) L (fun i => ((h i : Fin L) : ℕ))‖) := by
            apply mul_le_mul_of_nonneg_left hstep
            positivity
        _ = cw (r+1) * (L:ℝ)^(2^(r+1) - (r+1) - 1)
              * ∑ h : Fin (r+1) → Fin L, ‖Gsum ψ (r+1) L (fun i => ((h i : Fin L) : ℕ))‖ := by
            rw [cw, hexp]
            ring
lemma eval_eq_sum_range' (f : ℝ[X]) (z : ℝ) :
    f.eval z = ∑ j ∈ Finset.range (f.natDegree+1), f.coeff j * z^j := by
  rw [Polynomial.eval_eq_sum_range]

lemma iterDiff_shifted_poly_affine (k : ℕ) (hk : 2 ≤ k) (f : ℝ[X]) (hf : f.natDegree = k)
    (M : ℤ) (h : Fin (k-1) → ℤ) :
    ∃ β γ : ℝ, β = (k.factorial : ℝ) * f.leadingCoeff * (∏ i : Fin (k-1), (h i : ℝ)) ∧
      ∀ x : ℤ, iterDiff (fun y : ℤ => f.eval ((M:ℝ) + (y:ℝ))) (k-1) h x = β * (x:ℝ) + γ := by
  obtain ⟨c₁, hc₁⟩ := signed_sum_pow_linear k hk h
  refine ⟨(k.factorial : ℝ) * f.leadingCoeff * (∏ i : Fin (k-1), (h i : ℝ)),
      (f.coeff k : ℝ) * ((k.factorial : ℝ) * (∏ i : Fin (k-1), (h i : ℝ)) * (M:ℝ) + (c₁ : ℝ))
        + (f.coeff (k-1) : ℝ) * (((k-1).factorial : ℝ) * (∏ i : Fin (k-1), (h i : ℝ))), rfl, ?_⟩
  intro x
  have hcoeff : f.leadingCoeff = f.coeff k := by rw [Polynomial.leadingCoeff, hf]
  have hlow : ∀ j, j ≤ k-1 →
      (∑ S : Finset (Fin (k-1)), (-1:ℝ)^((k-1)-S.card) * ((↑(M + x + ∑ i ∈ S, h i) : ℝ))^j)
        = if j = k-1 then ((k-1).factorial : ℝ) * (∏ i : Fin (k-1), (h i : ℝ)) else 0 := by
    intro j hj
    have hcast : (∑ S : Finset (Fin (k-1)),
          (-1:ℝ)^((k-1)-S.card) * ((↑(M + x + ∑ i ∈ S, h i) : ℝ))^j)
        = ((∑ S : Finset (Fin (k-1)),
            (-1:ℤ)^((k-1)-S.card) * (M + x + ∑ i ∈ S, h i)^j : ℤ) : ℝ) := by
      push_cast
      apply Finset.sum_congr rfl
      intro S _
      ring
    rw [hcast, signed_sum_pow_lower hj h (M + x)]
    by_cases hjk : j = k-1
    · rw [if_pos hjk, if_pos hjk]; push_cast; ring
    · rw [if_neg hjk, if_neg hjk]; simp
  have hkth : (∑ S : Finset (Fin (k-1)),
        (-1:ℝ)^((k-1)-S.card) * ((↑(M + x + ∑ i ∈ S, h i) : ℝ))^k)
      = (k.factorial : ℝ) * (∏ i : Fin (k-1), (h i : ℝ)) * ((M:ℝ)+(x:ℝ)) + (c₁ : ℝ) := by
    have hcast : (∑ S : Finset (Fin (k-1)),
          (-1:ℝ)^((k-1)-S.card) * ((↑(M + x + ∑ i ∈ S, h i) : ℝ))^k)
        = ((∑ S : Finset (Fin (k-1)),
            (-1:ℤ)^((k-1)-S.card) * (M + x + ∑ i ∈ S, h i)^k : ℤ) : ℝ) := by
      push_cast
      apply Finset.sum_congr rfl
      intro S _
      ring
    rw [hcast, hc₁ (M + x)]
    push_cast
    ring
  calc iterDiff (fun y : ℤ => f.eval ((M:ℝ) + (y:ℝ))) (k-1) h x
      = ∑ S : Finset (Fin (k-1)), (-1:ℝ)^((k-1)-S.card) *
          f.eval ((↑(M + x + ∑ i ∈ S, h i) : ℝ)) := by
        rw [iterDiff_eq_sum]
        apply Finset.sum_congr rfl
        intro S _
        congr 2
        push_cast
        ring
    _ = ∑ S : Finset (Fin (k-1)), (-1:ℝ)^((k-1)-S.card) *
          (∑ j ∈ Finset.range (k+1), f.coeff j * ((↑(M + x + ∑ i ∈ S, h i) : ℝ))^j) := by
        apply Finset.sum_congr rfl
        intro S _
        rw [eval_eq_sum_range' _ _, hf]
    _ = ∑ j ∈ Finset.range (k+1), f.coeff j *
          (∑ S : Finset (Fin (k-1)), (-1:ℝ)^((k-1)-S.card) * ((↑(M + x + ∑ i ∈ S, h i) : ℝ))^j) := by
        simp only [Finset.mul_sum]
        rw [Finset.sum_comm]
        apply Finset.sum_congr rfl
        intro j _
        apply Finset.sum_congr rfl
        intro S _
        ring
    _ = (k.factorial : ℝ) * f.leadingCoeff * (∏ i : Fin (k-1), (h i : ℝ)) * (x:ℝ)
        + ((f.coeff k : ℝ) * ((k.factorial : ℝ) * (∏ i : Fin (k-1), (h i : ℝ)) * (M:ℝ) + (c₁ : ℝ))
          + (f.coeff (k-1) : ℝ) * (((k-1).factorial : ℝ) * (∏ i : Fin (k-1), (h i : ℝ)))) := by
        have hstep : ∀ j ∈ Finset.range (k+1), f.coeff j *
              (∑ S : Finset (Fin (k-1)), (-1:ℝ)^((k-1)-S.card) * ((↑(M + x + ∑ i ∈ S, h i) : ℝ))^j)
            = (if j = k then f.coeff k * ((k.factorial : ℝ) * (∏ i : Fin (k-1), (h i : ℝ)) * ((M:ℝ)+(x:ℝ)) + (c₁:ℝ))
               else if j = k-1 then f.coeff (k-1) * (((k-1).factorial : ℝ) * (∏ i : Fin (k-1), (h i : ℝ))) else 0) := by
          intro j hj
          rcases lt_trichotomy j k with hlt | heq | hgt
          · have hjle : j ≤ k-1 := by omega
            rw [hlow j hjle]
            by_cases hjk : j = k-1
            · rw [if_pos hjk, if_pos hjk, if_neg (by omega : ¬ j = k), hjk]
            · rw [if_neg hjk, if_neg hjk, if_neg (by omega : ¬ j = k), mul_zero]
          · subst heq; rw [hkth, if_pos rfl]
          · simp only [Finset.mem_range] at hj; omega
        rw [Finset.sum_congr rfl hstep]
        rw [show Finset.range (k+1) = insert k (insert (k-1) (Finset.range (k-1))) by
          ext j; simp only [Finset.mem_range, Finset.mem_insert]; omega]
        rw [Finset.sum_insert (by simp only [Finset.mem_insert, Finset.mem_range]; omega),
            Finset.sum_insert (by simp only [Finset.mem_range]; omega)]
        rw [if_pos rfl]
        rw [if_neg (by omega : ¬ k-1 = k), if_pos rfl]
        rw [Finset.sum_eq_zero (fun j hj => by
          rw [if_neg (by simp only [Finset.mem_range] at hj; omega),
              if_neg (by simp only [Finset.mem_range] at hj; omega)])]
        rw [hcoeff]
        ring


/-! ## Geometric bound for the iterated sums and tuple counting -/

lemma iterDiff_phase_affine (k : ℕ) (hk : 2 ≤ k) (f : ℝ[X]) (hf : f.natDegree = k) (M : ℤ)
    (h : Fin (k-1) → ℤ) :
    ∃ β γ : ℝ,
      β = 2*Real.pi*((k.factorial : ℝ) * f.leadingCoeff * (∏ i : Fin (k-1), (h i : ℝ))) ∧
      ∀ x : ℤ, iterDiff (fun y : ℤ => 2*Real.pi*f.eval ((M:ℝ) + (y:ℝ))) (k-1) h x = β * (x:ℝ) + γ := by
  obtain ⟨β, γ, hβ, hγ⟩ := iterDiff_shifted_poly_affine k hk f hf M h
  refine ⟨2*Real.pi*β, 2*Real.pi*γ, ?_, ?_⟩
  · rw [hβ]
  · intro x
    have h1 := iterDiff_const_mul (2*Real.pi) (fun y : ℤ => f.eval ((M:ℝ) + (y:ℝ))) (k-1) h
    rw [h1]
    show (2*Real.pi) * iterDiff (fun y : ℤ => f.eval ((M:ℝ) + (y:ℝ))) (k-1) h x = _
    rw [hγ x]; ring


lemma geom_sum_Ephase_le_rho (L N : ℕ) (hLN : L ≤ N) (hN : 1 ≤ N) (β γ : ℝ) :
    ‖∑ x ∈ Finset.range L, Ephase (fun y : ℤ => β*(y:ℝ) + γ) (x:ℤ)‖ ≤ rho (β/(2*Real.pi)) N := by
  have hcongr : ∀ x : ℕ, Ephase (fun y : ℤ => β*(y:ℝ) + γ) (x:ℤ)
      = pe ((β/(2*Real.pi))*(x:ℝ) + γ/(2*Real.pi)) := by
    intro x
    unfold Ephase pe
    rw [show ((2 * Real.pi * ((β / (2 * Real.pi)) * (x:ℝ) + γ / (2 * Real.pi)) : ℝ) : ℂ)
          = (↑(β * (x:ℝ) + γ) : ℂ) by
      push_cast
      field_simp]
    simp
  rw [Finset.sum_congr rfl (fun x _ => hcongr x)]
  exact geom_sum_range_pe_le_rho L N hLN hN _ _

lemma Gsum_le_rho (k : ℕ) (hk : 2 ≤ k) (f : ℝ[X]) (hf : f.natDegree = k) (M : ℤ) (N : ℕ) (hN : 1 ≤ N)
    (h : Fin (k-1) → Fin N) :
    ‖Gsum (fun y : ℤ => 2*Real.pi*f.eval ((M:ℝ) + (y:ℝ))) (k-1) N (fun i => ((h i : Fin N) : ℕ))‖
      ≤ rho (((k.factorial:ℝ) * f.leadingCoeff
            * (∏ i : Fin (k-1), (((h i : Fin N)) : ℝ)))) N := by
  obtain ⟨β, γ, hβ, hγ⟩ := iterDiff_phase_affine k hk f hf M (fun i => ((h i : Fin N) : ℤ))
  have hpt : Ephase (iterDiff (fun y : ℤ => 2*Real.pi*f.eval ((M:ℝ) + (y:ℝ))) (k-1)
        (fun i => ((h i : Fin N) : ℤ)))
      = Ephase (fun y : ℤ => β*(y:ℝ) + γ) := by
    rw [show iterDiff (fun y : ℤ => 2*Real.pi*f.eval ((M:ℝ) + (y:ℝ))) (k-1)
        (fun i => ((h i : Fin N) : ℤ)) = fun y : ℤ => β*(y:ℝ) + γ from funext hγ]
  simp only [Gsum]
  have hsum : (∑ x ∈ Finset.range (N - ∑ x, ((h x : Fin N) : ℕ)),
        Ephase (iterDiff (fun y : ℤ => 2*Real.pi*f.eval ((M:ℝ) + (y:ℝ))) (k-1)
          (fun i => ((h i : Fin N) : ℤ))) (x:ℤ))
      = ∑ x ∈ Finset.range (N - ∑ x, ((h x : Fin N) : ℕ)),
          Ephase (fun y : ℤ => β*(y:ℝ) + γ) (x:ℤ) :=
    Finset.sum_congr rfl (fun x _ => congrFun hpt (x:ℤ))
  rw [hsum]
  have hb : β/(2*Real.pi)
      = (k.factorial:ℝ) * f.leadingCoeff * (∏ i : Fin (k-1), (((h i : Fin N)) : ℝ)) := by
    rw [hβ]; field_simp; push_cast; ring
  have hgeo := geom_sum_Ephase_le_rho (N - ∑ x, ((h x : Fin N) : ℕ)) N (Nat.sub_le _ _) hN β γ
  rw [hb] at hgeo
  exact hgeo

lemma card_tuples_prod (r N m : ℕ) (hm : 1 ≤ m) :
    ((Finset.univ : Finset (Fin r → Fin N)).filter
        (fun h => (∏ i, ((h i : Fin N) : ℕ)) = m)).card ≤ (Nat.divisors m).card ^ r := by
  have h1 : ((Finset.univ : Finset (Fin r → Fin N)).filter
        (fun h => (∏ i, ((h i : Fin N) : ℕ)) = m)).card
      = Fintype.card {h : Fin r → Fin N // (∏ i, ((h i : Fin N) : ℕ)) = m} := by
    rw [Fintype.card_subtype]
  rw [h1]
  calc Fintype.card {h : Fin r → Fin N // (∏ i, ((h i : Fin N) : ℕ)) = m}
      ≤ Fintype.card ((i : Fin r) → {d : ℕ // d ∈ Nat.divisors m}) := by
        refine Fintype.card_le_of_injective
          (fun h : {h : Fin r → Fin N // (∏ i, ((h i : Fin N) : ℕ)) = m} =>
            fun i => ⟨((h.1 i : Fin N) : ℕ), ?_⟩) ?_
        · rw [Nat.mem_divisors]
          refine ⟨?_, by omega⟩
          obtain ⟨hv, hprop⟩ := h
          have hd : ((hv i : Fin N) : ℕ) ∣ (∏ j, ((hv j : Fin N) : ℕ)) :=
            Finset.dvd_prod_of_mem _ (Finset.mem_univ i)
          rw [hprop] at hd
          exact hd
        · intro h h' heq
          have hv : ∀ i, ((h.1 i : Fin N) : ℕ) = ((h'.1 i : Fin N) : ℕ) := by
            intro i
            have := congrFun heq i
            exact congrArg Subtype.val this
          exact Subtype.ext (funext (fun i => Fin.ext (hv i)))
    _ = (Nat.divisors m).card ^ r := by
        rw [Fintype.card_fun, Fintype.card_fin, Fintype.card_coe]

/-! ## Counting tuples by their product, and the main assembly -/

lemma card_fiber_zero (r N : ℕ) (i : Fin r) :
    ((Finset.univ : Finset (Fin r → Fin N)).filter (fun h => ((h i : Fin N) : ℕ) = 0)).card
      ≤ N^(r-1) := by
  rw [← Fintype.card_subtype]
  have h1 : Fintype.card {h : Fin r → Fin N // ((h i : Fin N) : ℕ) = 0}
      ≤ Fintype.card ((j : {j : Fin r // j ≠ i}) → Fin N) := by
    apply Fintype.card_le_of_injective (f := fun h j => h.1 j.1)
    intro h h' heq
    obtain ⟨a, ha⟩ := h
    obtain ⟨b, hb⟩ := h'
    have hab : a = b := by
      funext j
      by_cases hj : j = i
      · subst hj
        exact Fin.ext (by rw [ha, hb])
      · exact congrFun heq ⟨j, hj⟩
    exact Subtype.ext hab
  calc Fintype.card {h : Fin r → Fin N // ((h i : Fin N) : ℕ) = 0}
      ≤ Fintype.card ((j : {j : Fin r // j ≠ i}) → Fin N) := h1
    _ = N^(r-1) := by
        rw [Fintype.card_fun, Fintype.card_fin]
        congr 1
        rw [Fintype.card_subtype]
        rw [show (Finset.univ.filter (fun j : Fin r => ¬ j = i)) = (Finset.univ.erase i) by
          ext j; simp [eq_comm]]
        rw [Finset.card_erase_of_mem (Finset.mem_univ i), Finset.card_univ, Fintype.card_fin]

lemma tuple_sum_le (k : ℕ) (hk : 2 ≤ k) {γ : ℝ} {N : ℕ} {δ Cη : ℝ} (hδ : 0 ≤ δ) (hCη0 : 0 ≤ Cη)
    (hCη : ∀ m : ℕ, 1 ≤ m → (((Nat.divisors m).card : ℝ))^(k-1) ≤ Cη * (m:ℝ)^δ) :
    ∑ h : Fin (k-1) → Fin N, rho (γ * ((∏ i, ((h i : Fin N) : ℕ)) : ℝ)) N
      ≤ (k-1 : ℝ) * (N:ℝ)^(k-1) + Cη * (N:ℝ)^(δ*(k-1))
          * ∑ m ∈ Finset.Icc 1 (N^(k-1)), rho (γ * (m:ℝ)) N := by
  set r := k-1 with hr
  have hr1 : 1 ≤ r := by omega
  set A0 : Finset (Fin r → Fin N) :=
    (Finset.univ : Finset (Fin r → Fin N)).filter (fun h => (∏ i, ((h i : Fin N) : ℕ)) = 0) with hA0
  set A1 : Finset (Fin r → Fin N) :=
    (Finset.univ : Finset (Fin r → Fin N)).filter (fun h => (∏ i, ((h i : Fin N) : ℕ)) ≠ 0) with hA1
  have hsplit : ∑ h ∈ A0, rho (γ * ((∏ i, ((h i : Fin N) : ℕ)) : ℝ)) N
      + ∑ h ∈ A1, rho (γ * ((∏ i, ((h i : Fin N) : ℕ)) : ℝ)) N
      = ∑ h : Fin r → Fin N, rho (γ * ((∏ i, ((h i : Fin N) : ℕ)) : ℝ)) N := by
    rw [hA0, hA1, Finset.sum_filter, Finset.sum_filter, ← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro h _
    by_cases hp : (∏ i, ((h i : Fin N) : ℕ)) = 0
    · rw [if_pos hp, if_neg (by simp [hp]), add_zero]
    · rw [if_neg hp, if_pos (by simp [hp]), zero_add]
  have hA0bound : ∑ h ∈ A0, rho (γ * ((∏ i, ((h i : Fin N) : ℕ)) : ℝ)) N ≤ (r:ℝ) * (N:ℝ)^r := by
    have hconst : ∀ h ∈ A0, rho (γ * ((∏ i, ((h i : Fin N) : ℕ)) : ℝ)) N = (N:ℝ) := by
      intro h hh
      have hp : (∏ i, ((h i : Fin N) : ℕ)) = 0 := (Finset.mem_filter.mp hh).2
      have hp0 : (γ * ∏ i, (((h i : Fin N) : ℕ) : ℝ)) = 0 := by
        rw [← Nat.cast_prod, hp, Nat.cast_zero, mul_zero]
      rw [hp0]
      show rho 0 N = (N:ℝ)
      unfold rho
      rw [show dz (0:ℝ) = 0 by simp [dz],
        max_eq_right (div_nonneg zero_le_one (by positivity))]
      have : (1:ℝ)/(2*(1/(2*(N:ℝ)))) = (N:ℝ) := by field_simp
      rw [this, min_self]
    rw [Finset.sum_congr rfl hconst, Finset.sum_const, nsmul_eq_mul]
    have hcard : (A0.card : ℝ) ≤ (r:ℝ) * (N:ℝ)^(r-1) := by
      have hsub : A0 ⊆ Finset.univ.biUnion (fun i : Fin r =>
          (Finset.univ : Finset (Fin r → Fin N)).filter (fun h => ((h i : Fin N) : ℕ) = 0)) := by
        intro h hh
        rw [Finset.mem_biUnion]
        have hp : (∏ i, ((h i : Fin N) : ℕ)) = 0 := (Finset.mem_filter.mp hh).2
        obtain ⟨i, _, hfz⟩ := Finset.prod_eq_zero_iff.mp hp
        exact ⟨i, Finset.mem_univ i, Finset.mem_filter.mpr ⟨Finset.mem_univ h, hfz⟩⟩
      have h2 : (A0.card : ℝ) ≤ ∑ i : Fin r,
          (((Finset.univ : Finset (Fin r → Fin N)).filter (fun h => ((h i : Fin N) : ℕ) = 0)).card : ℝ) := by
        have h3 := Finset.card_biUnion_le (s := (Finset.univ : Finset (Fin r)))
          (t := fun i : Fin r => (Finset.univ : Finset (Fin r → Fin N)).filter (fun h => ((h i : Fin N) : ℕ) = 0))
        exact_mod_cast le_trans (Finset.card_le_card hsub) h3
      have h4 : ∀ i : Fin r,
          (((Finset.univ : Finset (Fin r → Fin N)).filter (fun h => ((h i : Fin N) : ℕ) = 0)).card : ℝ)
            ≤ (N:ℝ)^(r-1) := by
        intro i
        have := card_fiber_zero r N i
        exact_mod_cast this
      calc (A0.card : ℝ) ≤ ∑ i : Fin r,
            (((Finset.univ : Finset (Fin r → Fin N)).filter (fun h => ((h i : Fin N) : ℕ) = 0)).card : ℝ) := h2
        _ ≤ ∑ i : Fin r, (N:ℝ)^(r-1) := Finset.sum_le_sum (fun i _ => h4 i)
        _ = (r:ℝ) * (N:ℝ)^(r-1) := by
            rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    calc ((A0.card : ℝ)) * (N:ℝ) ≤ ((r:ℝ) * (N:ℝ)^(r-1)) * (N:ℝ) :=
          mul_le_mul_of_nonneg_right hcard (Nat.cast_nonneg N)
      _ = (r:ℝ) * (N:ℝ)^r := by
          rw [mul_assoc, ← pow_succ]
          congr 2
          omega
  have hA1bound : ∑ h ∈ A1, rho (γ * ((∏ i, ((h i : Fin N) : ℕ)) : ℝ)) N
      ≤ Cη * (N:ℝ)^(δ*r) * ∑ m ∈ Finset.Icc 1 (N^r), rho (γ * (m:ℝ)) N := by
    have h2 : ∑ h ∈ A1, rho (γ * ((∏ i, ((h i : Fin N) : ℕ)) : ℝ)) N
        = ∑ m ∈ Finset.Icc 1 (N^r), ∑ h ∈ A1,
            (if (∏ i, ((h i : Fin N) : ℕ)) = m
              then rho (γ * ((∏ i, ((h i : Fin N) : ℕ)) : ℝ)) N else 0) := by
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro h hh
      have hne : (∏ i, ((h i : Fin N) : ℕ)) ≠ 0 := (Finset.mem_filter.mp hh).2
      have hle : (∏ i, ((h i : Fin N) : ℕ)) ≤ N^r := by
        calc (∏ i, ((h i : Fin N) : ℕ)) ≤ ∏ i : Fin r, N := by
              apply Finset.prod_le_prod
              · intro i _; exact Nat.zero_le _
              · intro i _; exact Nat.le_of_lt (h i).isLt
          _ = N^r := by rw [Finset.prod_const, Finset.card_univ, Fintype.card_fin]
      have hmem : (∏ i, ((h i : Fin N) : ℕ)) ∈ Finset.Icc 1 (N^r) := by
        rw [Finset.mem_Icc]
        exact ⟨Nat.one_le_iff_ne_zero.mpr hne, hle⟩
      rw [Finset.sum_eq_single (∏ i, ((h i : Fin N) : ℕ))]
      · rw [if_pos rfl]
      · intro m _ hm; rw [if_neg (fun hh => hm hh.symm)]
      · intro hnot; exact absurd hmem hnot
    rw [h2]
    calc ∑ m ∈ Finset.Icc 1 (N^r), ∑ h ∈ A1,
            (if (∏ i, ((h i : Fin N) : ℕ)) = m
              then rho (γ * ((∏ i, ((h i : Fin N) : ℕ)) : ℝ)) N else 0)
        ≤ ∑ m ∈ Finset.Icc 1 (N^r), (Cη * (N:ℝ)^(δ*r)) * rho (γ * (m:ℝ)) N := by
          apply Finset.sum_le_sum
          intro m hm
          rw [Finset.mem_Icc] at hm
          have hm1 : 1 ≤ m := hm.1
          have hmle : (m:ℝ) ≤ (N:ℝ)^r := by exact_mod_cast hm.2
          have hfiber : ((A1.filter (fun h => (∏ i, ((h i : Fin N) : ℕ)) = m)).card : ℝ)
              ≤ Cη * (m:ℝ)^δ := by
            have hcard := card_tuples_prod r N m hm1
            have hsub : A1.filter (fun h => (∏ i, ((h i : Fin N) : ℕ)) = m)
                ⊆ (Finset.univ : Finset (Fin r → Fin N)).filter
                    (fun h => (∏ i, ((h i : Fin N) : ℕ)) = m) := by
              intro h hh
              exact Finset.mem_filter.mpr ⟨Finset.mem_univ h, (Finset.mem_filter.mp hh).2⟩
            calc ((A1.filter (fun h => (∏ i, ((h i : Fin N) : ℕ)) = m)).card : ℝ)
                ≤ (((Finset.univ : Finset (Fin r → Fin N)).filter
                    (fun h => (∏ i, ((h i : Fin N) : ℕ)) = m)).card : ℝ) := by
                  exact_mod_cast Finset.card_le_card hsub
              _ ≤ Cη * (m:ℝ)^δ := by
                  have h2' : (((Finset.univ : Finset (Fin r → Fin N)).filter
                      (fun h => (∏ i, ((h i : Fin N) : ℕ)) = m)).card : ℝ)
                      ≤ ((Nat.divisors m).card : ℝ)^r := by
                    exact_mod_cast hcard
                  refine le_trans h2' ?_
                  rw [hr]
                  exact hCη m hm1
          have hmm : (m:ℝ)^δ ≤ (N:ℝ)^(δ*r) := by
            calc (m:ℝ)^δ ≤ ((N:ℝ)^r)^δ := Real.rpow_le_rpow (Nat.cast_nonneg m) hmle hδ
              _ = ((N:ℝ)^((r:ℕ):ℝ))^δ := by rw [← Real.rpow_natCast]
              _ = (N:ℝ)^(((r:ℕ):ℝ)*δ) := (Real.rpow_mul (Nat.cast_nonneg N) ((r:ℕ):ℝ) δ).symm
              _ = (N:ℝ)^(δ*(r:ℝ)) := by rw [mul_comm]
          have h3 : ∑ h ∈ A1, (if (∏ i, ((h i : Fin N) : ℕ)) = m
                then rho (γ * ((∏ i, ((h i : Fin N) : ℕ)) : ℝ)) N else 0)
              = ((A1.filter (fun h => (∏ i, ((h i : Fin N) : ℕ)) = m)).card : ℝ)
                  * rho (γ * (m:ℝ)) N := by
            rw [Finset.card_filter]
            push_cast
            rw [Finset.sum_mul]
            apply Finset.sum_congr rfl
            intro h hh
            by_cases hp : (∏ i, ((h i : Fin N) : ℕ)) = m
            · rw [if_pos hp, if_pos hp, one_mul]
              rw [show (γ * ∏ i, (((h i : Fin N) : ℕ) : ℝ)) = (γ * (m:ℝ)) by
                rw [← Nat.cast_prod, hp]]
            · rw [if_neg hp, if_neg hp, zero_mul]
          rw [h3]
          calc ((A1.filter (fun h => (∏ i, ((h i : Fin N) : ℕ)) = m)).card : ℝ)
                * rho (γ * (m:ℝ)) N
              ≤ (Cη * (m:ℝ)^δ) * rho (γ * (m:ℝ)) N :=
                mul_le_mul_of_nonneg_right hfiber (rho_nonneg _ _)
            _ ≤ (Cη * (N:ℝ)^(δ*r)) * rho (γ * (m:ℝ)) N :=
                mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hmm hCη0) (rho_nonneg _ _)
      _ = (Cη * (N:ℝ)^(δ*r)) * ∑ m ∈ Finset.Icc 1 (N^r), rho (γ * (m:ℝ)) N := by
          rw [Finset.mul_sum]
  rw [← hsplit]
  refine le_trans (add_le_add hA0bound hA1bound) ?_
  have h1 : (r:ℝ) = ((k-1:ℕ):ℝ) := by rw [hr]
  have h2 : (N:ℝ)^r = (N:ℝ)^(k-1) := by rw [hr]
  have h3 : (Finset.Icc 1 (N^r)) = (Finset.Icc 1 (N^(k-1))) := by rw [hr]
  rw [h1, h2, h3]
  have hk1 : ((k-1:ℕ):ℝ) = (k:ℝ) - 1 := by
    rw [Nat.cast_sub (by omega : 1 ≤ k)]; norm_num
  rw [hk1]



/-! ## Final estimates -/

lemma log_le_rpow_threshold {c : ℝ} (hc : 0 < c) :
    ∃ N₀ : ℝ, 0 < N₀ ∧ ∀ N : ℕ, N₀ ≤ (N:ℝ) → 1 + Real.log (N:ℝ) ≤ (N:ℝ)^(c/4) := by
  set B : ℝ := 8/c + 1 with hB
  have hBpos : 0 < B := by rw [hB]; positivity
  refine ⟨max 1 (B^(8/c)), ?_, ?_⟩
  · positivity
  · intro N hN
    have hN1 : (1:ℝ) ≤ (N:ℝ) := le_trans (le_max_left _ _) hN
    have hNpos : (0:ℝ) < (N:ℝ) := lt_of_lt_of_le one_pos hN1
    have hlog : Real.log (N:ℝ) ≤ (N:ℝ)^(c/8) / (c/8) :=
      Real.log_le_rpow_div (le_of_lt hNpos) (by positivity)
    have hcf : (N:ℝ)^(c/8) / (c/8) = (8/c) * (N:ℝ)^(c/8) := by field_simp
    rw [hcf] at hlog
    set X : ℝ := (N:ℝ)^(c/8) with hX
    have hX1 : 1 ≤ X := by rw [hX]; exact Real.one_le_rpow hN1 (by positivity)
    have hXgeB : B ≤ X := by
      have h1 : B^(8/c) ≤ (N:ℝ) := le_trans (le_max_right _ _) hN
      have h2 : (B^(8/c))^(c/8) ≤ (N:ℝ)^(c/8) :=
        Real.rpow_le_rpow (Real.rpow_nonneg (le_of_lt hBpos) _) h1 (by positivity)
      have h3 : (B^(8/c))^(c/8) = B := by
        rw [← Real.rpow_mul (le_of_lt hBpos)]
        have : (8/c) * (c/8) = 1 := by field_simp
        rw [this, Real.rpow_one]
      have h4 : (N:ℝ)^(c/8) = X := hX.symm
      rw [h4] at h2
      rwa [h3] at h2
    have hXsq : X*X = (N:ℝ)^(c/4) := by
      rw [hX, ← Real.rpow_add hNpos]; congr 1; ring
    have hBm : B - 1 = 8/c := by rw [hB]; ring
    have hmain : 1 + (8/c)*X ≤ X*X := by nlinarith [hXgeB, hX1, hBm]
    rw [hX] at hlog
    linarith [hlog, hmain, hXsq]

lemma sum_range_ite_add_lt' {M : Type*} [AddCommMonoid M] (L h : ℕ) (f : ℕ → M) :
    (∑ x ∈ Finset.range L, (if x + h < L then f x else 0))
      = ∑ x ∈ Finset.range (L - h), f x := by
  have h1 : (∑ x ∈ Finset.range (L - h), (if x + h < L then f x else 0))
      = ∑ x ∈ Finset.range (L - h), f x := by
    apply Finset.sum_congr rfl
    intro x hx
    rw [Finset.mem_range] at hx
    rw [if_pos (by omega)]
  have h2 : (∑ x ∈ Finset.range (L - h), (if x + h < L then f x else 0))
      = ∑ x ∈ Finset.range L, (if x + h < L then f x else 0) := by
    refine Finset.sum_subset ?_ ?_
    · intro x hx
      rw [Finset.mem_range] at hx ⊢
      omega
    · intro x hxL hxs
      rw [Finset.mem_range] at hxL
      simp only [Finset.mem_range, not_lt] at hxs
      rw [if_neg (by omega)]
  rw [← h1, ← h2]

lemma Icc_one_div_sum_le (N : ℕ) :
    ∑ t ∈ Finset.Icc 1 N, (1:ℝ)/(t:ℝ) ≤ 1 + Real.log N := by
  have h1 : ∑ t ∈ Finset.Icc 1 N, (1:ℝ)/(t:ℝ) = ∑ k ∈ Finset.range N, (1:ℝ)/((k:ℝ)+1) := by
    rw [show Finset.Icc 1 N = Finset.Ico 1 (N+1) by
      ext i; simp only [Finset.mem_Icc, Finset.mem_Ico]; omega]
    rw [Finset.sum_Ico_eq_sum_range]
    simp only [Nat.add_sub_cancel]
    apply Finset.sum_congr rfl
    intro k _
    congr 1
    push_cast; ring
  rw [h1]; exact inv_range_le_log N

lemma rho_sum_le (k : ℕ) (hk : 2 ≤ k) {ε t : ℝ} (hε : 0 < ε) (ht : 1 ≤ t) :
    ∃ C : ℝ, 0 < C ∧ ∀ {a q : ℤ} (hq : 1 ≤ q) (hgcd : Int.gcd a q = 1) {lc : ℝ}
      (hlc : |lc - (a:ℝ)/q| ≤ t/(q:ℝ)^2) (N : ℕ) (hN : 1 ≤ N)
      (hlogN : 1 + Real.log (N:ℝ) ≤ (N:ℝ)^(ε*((2:ℝ)^(k-1))/8)),
      ∑ m ∈ Finset.Icc 1 (N^(k-1)), rho (((k.factorial:ℝ)*lc) * (m:ℝ)) N
        ≤ C * ((N:ℝ)^(ε*((2:ℝ)^(k-1))/2)
            * ((N:ℝ)^(k-1) + (q:ℝ) + (N:ℝ)^k*t/(q:ℝ) + (N:ℝ)*t) + 1) := by
  refine ⟨max 1 (max (10000000 * ((k:ℝ)+4) * (k.factorial:ℝ)^2) 1), ?_, ?_⟩
  · positivity
  · intro a q hq hgcd lc hlc N hN hlogN
    have hMcast : ((N^(k-1) : ℕ) : ℝ) = (N:ℝ)^(k-1) := by push_cast; ring
    have hLg0 : (0:ℝ) ≤ 1 + Real.log (2 + ((N^(k-1):ℕ):ℝ) + (q:ℝ)) := by
      have h1 : (1:ℝ) ≤ 2 + ((N^(k-1):ℕ):ℝ) + (q:ℝ) := by
        have : (0:ℝ) ≤ ((N^(k-1):ℕ):ℝ) := Nat.cast_nonneg _
        have h2 : (1:ℝ) ≤ (q:ℝ) := by exact_mod_cast hq
        linarith
      linarith [Real.log_nonneg h1]
    have hNpos : 0 < N := hN
    have hN1 : (1:ℝ) ≤ (N:ℝ) := by exact_mod_cast hN
    -- layer decomposition
    have hlayer : ∑ m ∈ Finset.Icc 1 (N^(k-1)), rho (((k.factorial:ℝ)*lc) * (m:ℝ)) N
        ≤ ((N:ℝ)^(k-1)) + ∑ t' ∈ Finset.Icc 1 N,
            (((Finset.Icc 1 (N^(k-1))).filter
              (fun m : ℕ => dz (((k.factorial:ℝ)*lc) * (m:ℝ)) ≤ 1/(2*(t':ℝ)))).card : ℝ) := by
      have hpt : ∀ m ∈ Finset.Icc 1 (N^(k-1)),
          rho (((k.factorial:ℝ)*lc) * (m:ℝ)) N
            ≤ 1 + ∑ t' ∈ Finset.Icc 1 N,
                (if dz (((k.factorial:ℝ)*lc) * (m:ℝ)) ≤ 1/(2*(t':ℝ)) then (1:ℝ) else 0) := by
        intro m _
        have hx : 0 < max (dz (((k.factorial:ℝ)*lc) * (m:ℝ))) (1/(2*(N:ℝ))) :=
          lt_of_lt_of_le (div_pos one_pos (by linarith : (0:ℝ) < 2*(N:ℝ))) (le_max_right _ _)
        have h1 := min_inv_le_card N (max (dz (((k.factorial:ℝ)*lc) * (m:ℝ))) (1/(2*(N:ℝ)))) hx
        show rho (((k.factorial:ℝ)*lc) * (m:ℝ)) N
            ≤ 1 + ∑ t' ∈ Finset.Icc 1 N,
                (if dz (((k.factorial:ℝ)*lc) * (m:ℝ)) ≤ 1/(2*(t':ℝ)) then (1:ℝ) else 0)
        unfold rho
        have hsub : (Finset.Icc 1 N).filter (fun t' : ℕ =>
              max (dz (((k.factorial:ℝ)*lc) * (m:ℝ))) (1/(2*(N:ℝ))) ≤ 1/(2*(t':ℝ)))
            ⊆ (Finset.Icc 1 N).filter
              (fun t' : ℕ => dz (((k.factorial:ℝ)*lc) * (m:ℝ)) ≤ 1/(2*(t':ℝ))) := by
          intro t' ht'
          rw [Finset.mem_filter] at ht' ⊢
          exact ⟨ht'.1, le_trans (le_max_left _ _) ht'.2⟩
        have h2b : (∑ t' ∈ Finset.Icc 1 N,
                (if dz (((k.factorial:ℝ)*lc) * (m:ℝ)) ≤ 1/(2*(t':ℝ)) then (1:ℝ) else 0))
            = (((Finset.Icc 1 N).filter (fun t' : ℕ =>
                dz (((k.factorial:ℝ)*lc) * (m:ℝ)) ≤ 1/(2*(t':ℝ)))).card : ℝ) := by
          rw [Finset.card_filter]
          push_cast
          rfl
        have h2 : (((Finset.Icc 1 N).filter (fun t' : ℕ =>
              max (dz (((k.factorial:ℝ)*lc) * (m:ℝ))) (1/(2*(N:ℝ))) ≤ 1/(2*(t':ℝ)))).card : ℝ)
            ≤ ∑ t' ∈ Finset.Icc 1 N,
                (if dz (((k.factorial:ℝ)*lc) * (m:ℝ)) ≤ 1/(2*(t':ℝ)) then (1:ℝ) else 0) := by
          rw [h2b]
          exact_mod_cast Finset.card_le_card hsub
        linarith [h1, h2]
      calc _ ≤ ∑ m ∈ Finset.Icc 1 (N^(k-1)), (1 + ∑ t' ∈ Finset.Icc 1 N,
              (if dz (((k.factorial:ℝ)*lc) * (m:ℝ)) ≤ 1/(2*(t':ℝ)) then (1:ℝ) else 0)) :=
            Finset.sum_le_sum hpt
        _ = ((N:ℝ)^(k-1)) + ∑ m ∈ Finset.Icc 1 (N^(k-1)), ∑ t' ∈ Finset.Icc 1 N,
              (if dz (((k.factorial:ℝ)*lc) * (m:ℝ)) ≤ 1/(2*(t':ℝ)) then (1:ℝ) else 0) := by
            rw [Finset.sum_add_distrib, Finset.sum_const, Nat.card_Icc]
            have h1 : N^(k-1) + 1 - 1 = N^(k-1) := by omega
            rw [h1]
            simp only [nsmul_eq_mul, mul_one]
            rw [hMcast]
        _ = ((N:ℝ)^(k-1)) + ∑ t' ∈ Finset.Icc 1 N, ∑ m ∈ Finset.Icc 1 (N^(k-1)),
              (if dz (((k.factorial:ℝ)*lc) * (m:ℝ)) ≤ 1/(2*(t':ℝ)) then (1:ℝ) else 0) := by
            rw [Finset.sum_comm]
        _ = ((N:ℝ)^(k-1)) + ∑ t' ∈ Finset.Icc 1 N,
            (((Finset.Icc 1 (N^(k-1))).filter
              (fun m : ℕ => dz (((k.factorial:ℝ)*lc) * (m:ℝ)) ≤ 1/(2*(t':ℝ)))).card : ℝ) := by
            congr 1
            apply Finset.sum_congr rfl
            intro t' _
            rw [Finset.card_filter]
            push_cast
            rfl
    -- count bound
    have hcount : ∀ t' ∈ Finset.Icc 1 N,
        (((Finset.Icc 1 (N^(k-1))).filter
          (fun m : ℕ => dz (((k.factorial:ℝ)*lc) * (m:ℝ)) ≤ 1/(2*(t':ℝ)))).card : ℝ)
        ≤ 1000*((1/(2*(t':ℝ)))*(((N:ℝ)^(k-1)) + (q:ℝ)*(1 + Real.log (2 + ((N:ℝ)^(k-1)) + (q:ℝ))))
            + ((k.factorial:ℝ)*t)*(((N:ℝ)^(k-1))*(k.factorial:ℝ)/(q:ℝ)
              + 1 + Real.log (2 + ((N:ℝ)^(k-1)) + (q:ℝ)))) := by
      intro t' ht'
      rw [Finset.mem_Icc] at ht'
      have ht'1 : (1:ℝ) ≤ (t':ℝ) := by exact_mod_cast ht'.1
      have hd0 : (0:ℝ) < 1/(2*(t':ℝ)) := div_pos one_pos (by linarith)
      have hd1 : (1:ℝ)/(2*(t':ℝ)) ≤ 1 := by
        rw [div_le_one (by linarith : (0:ℝ) < 2*(t':ℝ))]
        linarith
      have hfil : ((Finset.Icc 1 (N^(k-1))).filter
          (fun m : ℕ => dz (((k.factorial:ℝ)*lc) * (m:ℝ)) ≤ 1/(2*(t':ℝ))))
          = ((Finset.Icc 1 (N^(k-1))).filter
          (fun m : ℕ => dz ((m:ℝ)*((k.factorial:ℝ)*lc)) ≤ 1/(2*(t':ℝ)))) := by
        apply Finset.filter_congr
        intro m _
        rw [mul_comm]
      rw [hfil, ← hMcast]
      exact count_le_approx k hq hgcd ht hd0 hd1 hlc (N^(k-1))
    -- harmonic sum
    have hharm : ∑ t' ∈ Finset.Icc 1 N, (1/(2*(t':ℝ))) ≤ 1 + Real.log N := by
      calc ∑ t' ∈ Finset.Icc 1 N, (1/(2*(t':ℝ)))
          = (1/2) * ∑ t' ∈ Finset.Icc 1 N, (1:ℝ)/(t':ℝ) := by
            rw [Finset.mul_sum]
            apply Finset.sum_congr rfl
            intro t' _
            ring
        _ ≤ (1/2) * (1 + Real.log N) :=
            mul_le_mul_of_nonneg_left (Icc_one_div_sum_le N) (by norm_num)
        _ ≤ 1 + Real.log N := by
            have h1 : (0:ℝ) ≤ 1 + Real.log (N:ℝ) := by
              have := Real.log_nonneg hN1; linarith
            linarith
    have hsum : ∑ t' ∈ Finset.Icc 1 N,
        (((Finset.Icc 1 (N^(k-1))).filter
          (fun m : ℕ => dz (((k.factorial:ℝ)*lc) * (m:ℝ)) ≤ 1/(2*(t':ℝ)))).card : ℝ)
        ≤ 1000*((((N:ℝ)^(k-1)) + (q:ℝ)*(1 + Real.log (2 + ((N:ℝ)^(k-1)) + (q:ℝ)))) * (1 + Real.log N)
            + (N:ℝ)*(((k.factorial:ℝ)*t)*(((N:ℝ)^(k-1))*(k.factorial:ℝ)/(q:ℝ)
              + 1 + Real.log (2 + ((N:ℝ)^(k-1)) + (q:ℝ))))) := by
      have hT1 : (0:ℝ) ≤ ((N:ℝ)^(k-1)) + (q:ℝ)*(1 + Real.log (2 + ((N:ℝ)^(k-1)) + (q:ℝ))) := by
        have h2 : (0:ℝ) ≤ (N:ℝ)^(k-1) := by positivity
        have h3 : (0:ℝ) ≤ 1 + Real.log (2 + ((N:ℝ)^(k-1)) + (q:ℝ)) := by
          have h4 : (1:ℝ) ≤ 2 + ((N:ℝ)^(k-1)) + (q:ℝ) := by
            have : (1:ℝ) ≤ (q:ℝ) := by exact_mod_cast hq
            linarith [show (0:ℝ) ≤ (N:ℝ)^(k-1) by positivity]
          linarith [Real.log_nonneg h4]
        positivity
      have hT2 : (0:ℝ) ≤ ((N:ℝ)^(k-1))*(k.factorial:ℝ)/(q:ℝ)
          + 1 + Real.log (2 + ((N:ℝ)^(k-1)) + (q:ℝ)) := by
        have h4 : (1:ℝ) ≤ 2 + ((N:ℝ)^(k-1)) + (q:ℝ) := by
          have : (1:ℝ) ≤ (q:ℝ) := by exact_mod_cast hq
          linarith [show (0:ℝ) ≤ (N:ℝ)^(k-1) by positivity]
        have h5 : (0:ℝ) ≤ Real.log (2 + ((N:ℝ)^(k-1)) + (q:ℝ)) := Real.log_nonneg h4
        have h6 : (0:ℝ) ≤ ((N:ℝ)^(k-1))*(k.factorial:ℝ)/(q:ℝ) := by positivity
        linarith
      have hS1 : (∑ t' ∈ Finset.Icc 1 N, 1000 * ((1/(2*(t':ℝ)))
            * (((N:ℝ)^(k-1)) + (q:ℝ)*(1 + Real.log (2 + ((N:ℝ)^(k-1)) + (q:ℝ))))))
          = 1000 * ((((N:ℝ)^(k-1)) + (q:ℝ)*(1 + Real.log (2 + ((N:ℝ)^(k-1)) + (q:ℝ))))
              * (∑ t' ∈ Finset.Icc 1 N, (1/(2*(t':ℝ))))) := by
        rw [Finset.mul_sum, Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro t' _
        ring
      have hS2 : (∑ t' ∈ Finset.Icc 1 N, 1000 * (((k.factorial:ℝ)*t)
            * (((N:ℝ)^(k-1))*(k.factorial:ℝ)/(q:ℝ) + 1 + Real.log (2 + ((N:ℝ)^(k-1)) + (q:ℝ)))))
          = 1000 * ((N:ℝ) * (((k.factorial:ℝ)*t)
            * (((N:ℝ)^(k-1))*(k.factorial:ℝ)/(q:ℝ) + 1 + Real.log (2 + ((N:ℝ)^(k-1)) + (q:ℝ))))) := by
        rw [Finset.sum_const, Nat.card_Icc, nsmul_eq_mul]
        have h1 : N + 1 - 1 = N := by omega
        rw [h1]; ring
      calc ∑ t' ∈ Finset.Icc 1 N,
            (((Finset.Icc 1 (N^(k-1))).filter
              (fun m : ℕ => dz (((k.factorial:ℝ)*lc) * (m:ℝ)) ≤ 1/(2*(t':ℝ)))).card : ℝ)
          ≤ ∑ t' ∈ Finset.Icc 1 N, 1000 * ((1/(2*(t':ℝ)))
              * (((N:ℝ)^(k-1)) + (q:ℝ)*(1 + Real.log (2 + ((N:ℝ)^(k-1)) + (q:ℝ))))
              + ((k.factorial:ℝ)*t)*(((N:ℝ)^(k-1))*(k.factorial:ℝ)/(q:ℝ)
                + 1 + Real.log (2 + ((N:ℝ)^(k-1)) + (q:ℝ)))) := Finset.sum_le_sum hcount
        _ = ∑ t' ∈ Finset.Icc 1 N, (1000 * ((1/(2*(t':ℝ)))
                * (((N:ℝ)^(k-1)) + (q:ℝ)*(1 + Real.log (2 + ((N:ℝ)^(k-1)) + (q:ℝ)))))
              + 1000 * (((k.factorial:ℝ)*t)*(((N:ℝ)^(k-1))*(k.factorial:ℝ)/(q:ℝ)
                + 1 + Real.log (2 + ((N:ℝ)^(k-1)) + (q:ℝ))))) := by
            apply Finset.sum_congr rfl
            intro t' _
            ring
        _ = (∑ t' ∈ Finset.Icc 1 N, 1000 * ((1/(2*(t':ℝ)))
                * (((N:ℝ)^(k-1)) + (q:ℝ)*(1 + Real.log (2 + ((N:ℝ)^(k-1)) + (q:ℝ))))))
              + (∑ t' ∈ Finset.Icc 1 N, 1000 * (((k.factorial:ℝ)*t)
                * (((N:ℝ)^(k-1))*(k.factorial:ℝ)/(q:ℝ) + 1 + Real.log (2 + ((N:ℝ)^(k-1)) + (q:ℝ))))) := by
            rw [Finset.sum_add_distrib]
        _ = 1000 * ((((N:ℝ)^(k-1)) + (q:ℝ)*(1 + Real.log (2 + ((N:ℝ)^(k-1)) + (q:ℝ))))
              * (∑ t' ∈ Finset.Icc 1 N, (1/(2*(t':ℝ)))))
              + 1000 * ((N:ℝ) * (((k.factorial:ℝ)*t)
                * (((N:ℝ)^(k-1))*(k.factorial:ℝ)/(q:ℝ) + 1 + Real.log (2 + ((N:ℝ)^(k-1)) + (q:ℝ))))) := by
            rw [hS1, hS2]
        _ ≤ 1000*((((N:ℝ)^(k-1)) + (q:ℝ)*(1 + Real.log (2 + ((N:ℝ)^(k-1)) + (q:ℝ)))) * (1 + Real.log N)
            + (N:ℝ)*(((k.factorial:ℝ)*t)*(((N:ℝ)^(k-1))*(k.factorial:ℝ)/(q:ℝ)
              + 1 + Real.log (2 + ((N:ℝ)^(k-1)) + (q:ℝ))))) := by
            have h1 : (0:ℝ) ≤ 1 + Real.log (N:ℝ) := by
              have := Real.log_nonneg hN1; linarith
            have hcoe : (0:ℝ) ≤ 1000 * (((N:ℝ)^(k-1)) + (q:ℝ)*(1 + Real.log (2 + ((N:ℝ)^(k-1)) + (q:ℝ)))) := by
              exact mul_nonneg (by norm_num) hT1
            nlinarith [hharm, hT1, hT2, h1, hcoe,
              mul_le_mul_of_nonneg_left hharm hcoe]
    -- trivial bound
    have htriv : (∑ m ∈ Finset.Icc 1 (N^(k-1)), rho (((k.factorial:ℝ)*lc) * (m:ℝ)) N) ≤ (N:ℝ)^k := by
      calc (∑ m ∈ Finset.Icc 1 (N^(k-1)), rho (((k.factorial:ℝ)*lc) * (m:ℝ)) N)
          ≤ ∑ m ∈ Finset.Icc 1 (N^(k-1)), (N:ℝ) := Finset.sum_le_sum (fun m _ => rho_le_N _ _)
        _ = ((Finset.Icc 1 (N^(k-1))).card : ℝ) * (N:ℝ) := by rw [Finset.sum_const, nsmul_eq_mul]
        _ = ((N:ℝ)^(k-1)) * (N:ℝ) := by
            rw [Nat.card_Icc]
            have h1 : N^(k-1) + 1 - 1 = N^(k-1) := by omega
            rw [h1, hMcast]
        _ = (N:ℝ)^k := by rw [← pow_succ]; congr 1; omega
    -- W ≤ N^{k-1} + 1000*(...)
    have hWle : (∑ m ∈ Finset.Icc 1 (N^(k-1)), rho (((k.factorial:ℝ)*lc) * (m:ℝ)) N)
        ≤ ((N:ℝ)^(k-1)) + 1000*((((N:ℝ)^(k-1)) + (q:ℝ)*(1 + Real.log (2 + ((N:ℝ)^(k-1)) + (q:ℝ))))
            * (1 + Real.log N)
          + (N:ℝ)*(((k.factorial:ℝ)*t)*(((N:ℝ)^(k-1))*(k.factorial:ℝ)/(q:ℝ)
            + 1 + Real.log (2 + ((N:ℝ)^(k-1)) + (q:ℝ))))) := by
      refine le_trans hlayer ?_
      exact add_le_add_right hsum _
    -- final arithmetic
    have hq1 : (1:ℝ) ≤ (q:ℝ) := by exact_mod_cast hq
    have hqpos : (0:ℝ) < (q:ℝ) := by linarith
    have hq0 : (0:ℝ) ≤ (q:ℝ) := le_of_lt hqpos
    have ht0 : (0:ℝ) ≤ t := le_trans zero_le_one ht
    have hFpos : (0:ℝ) < (k.factorial:ℝ) := by exact_mod_cast Nat.factorial_pos k
    have hF0 : (0:ℝ) ≤ (k.factorial:ℝ) := le_of_lt hFpos
    have hF1 : (1:ℝ) ≤ (k.factorial:ℝ) := by exact_mod_cast Nat.factorial_pos k
    have hL0 : (0:ℝ) ≤ 1 + Real.log (N:ℝ) := by
      have := Real.log_nonneg hN1; linarith
    have hK0 : (0:ℝ) ≤ (2:ℝ)^(k-1) := by positivity
    set P : ℝ := (N:ℝ)^(ε*((2:ℝ)^(k-1))/2) with hPdef
    have hP1 : (1:ℝ) ≤ P := by
      rw [hPdef]; exact Real.one_le_rpow hN1 (by positivity)
    have hP0 : (0:ℝ) ≤ P := le_trans zero_le_one hP1
    have hlog2 : 1 + Real.log (N:ℝ) ≤ P := by
      rw [hPdef]
      refine le_trans hlogN ?_
      exact Real.rpow_le_rpow_of_exponent_le hN1 (by nlinarith [hε, hK0])
    set X : ℝ := P * ((N:ℝ)^(k-1) + (q:ℝ) + (N:ℝ)^k*t/(q:ℝ) + (N:ℝ)*t) with hXdef
    have hNk1_0 : (0:ℝ) ≤ (N:ℝ)^(k-1) := by positivity
    have hNtk_q_0 : (0:ℝ) ≤ (N:ℝ)^k*t/(q:ℝ) := by positivity
    have hNt_0 : (0:ℝ) ≤ (N:ℝ)*t := by positivity
    have hX0 : (0:ℝ) ≤ X := by
      rw [hXdef]
      exact mul_nonneg hP0 (by linarith)
    have hX_A : P * ((N:ℝ)^(k-1)) ≤ X := by
      rw [hXdef]; nlinarith [hP0, hq0, hNk1_0, hNtk_q_0, hNt_0]
    have hX_q : (q:ℝ) * P ≤ X := by
      rw [hXdef]; nlinarith [hP0, hNk1_0, hNtk_q_0, hNt_0]
    have hX_B : P * ((N:ℝ)^k*t/(q:ℝ)) ≤ X := by
      rw [hXdef]; nlinarith [hP0, hq0, hNk1_0, hNt_0]
    have hX_C : P * ((N:ℝ)*t) ≤ X := by
      rw [hXdef]; nlinarith [hP0, hq0, hNk1_0, hNtk_q_0]
    have hX1 : (N:ℝ)^(k-1) ≤ X := le_trans (le_mul_of_one_le_left hNk1_0 hP1) hX_A
    have hX2 : ((N:ℝ)^(k-1)) * (1 + Real.log (N:ℝ)) ≤ X := by
      calc ((N:ℝ)^(k-1)) * (1 + Real.log (N:ℝ)) ≤ ((N:ℝ)^(k-1)) * P :=
            mul_le_mul_of_nonneg_left hlog2 hNk1_0
        _ = P * ((N:ℝ)^(k-1)) := by ring
        _ ≤ X := hX_A
    by_cases hcase : (N:ℝ)^k ≤ X
    · refine le_trans htriv ?_
      have hCm1 : (1:ℝ) ≤ max 1 (max (10000000 * ((k:ℝ)+4) * (k.factorial:ℝ)^2) 1) := le_max_left _ _
      have hXp0 : (0:ℝ) ≤ X + 1 := by linarith
      nlinarith [hcase, hXp0, hCm1]
    · push_neg at hcase
      have hqNk : (q:ℝ) ≤ (N:ℝ)^k := by
        have h1 : (q:ℝ) ≤ (q:ℝ) * P := le_mul_of_one_le_right hq0 hP1
        linarith [h1, hX_q, hcase.le]
      -- log bounds
      have hA1 : 1 + Real.log (2 + ((N:ℝ)^(k-1)) + (q:ℝ)) ≤ ((k:ℝ)+3) * (1 + Real.log (N:ℝ)) := by
        have hNk1 : (N:ℝ)^(k-1) ≤ (N:ℝ)^k := by
          apply pow_le_pow_right₀ hN1; omega
        have hNk1' : (1:ℝ) ≤ (N:ℝ)^k := one_le_pow₀ hN1
        have harg : 2 + ((N:ℝ)^(k-1)) + (q:ℝ) ≤ 4 * (N:ℝ)^k := by linarith
        have hpos1 : (0:ℝ) < 2 + ((N:ℝ)^(k-1)) + (q:ℝ) := by linarith
        have hlog := Real.log_le_log hpos1 harg
        rw [Real.log_mul (by norm_num) (by positivity), Real.log_pow] at hlog
        have hlog4 : Real.log 4 ≤ 3 := by
          have := Real.log_le_sub_one_of_pos (by norm_num : (0:ℝ) < 4); linarith
        have hlogN0 : (0:ℝ) ≤ Real.log (N:ℝ) := Real.log_nonneg hN1
        have hk2 : (2:ℝ) ≤ (k:ℝ) := by exact_mod_cast hk
        nlinarith [hlog, hlog4, hlogN0, hk2]
      have hbracket : (1 + Real.log (2 + ((N:ℝ)^(k-1)) + (q:ℝ))) * (1 + Real.log (N:ℝ)) ≤ ((k:ℝ)+3) * P := by
        have hLL : (1 + Real.log (N:ℝ)) * (1 + Real.log (N:ℝ)) ≤ P := by
          rw [hPdef]
          calc (1 + Real.log (N:ℝ)) * (1 + Real.log (N:ℝ))
              ≤ ((N:ℝ)^(ε*((2:ℝ)^(k-1))/8)) * ((N:ℝ)^(ε*((2:ℝ)^(k-1))/8)) :=
                mul_le_mul hlogN hlogN hL0 (by positivity)
            _ = (N:ℝ)^(ε*((2:ℝ)^(k-1))/4) := by
                rw [← Real.rpow_add (lt_of_lt_of_le one_pos hN1)]
                congr 1; ring
            _ ≤ (N:ℝ)^(ε*((2:ℝ)^(k-1))/2) :=
                Real.rpow_le_rpow_of_exponent_le hN1 (by nlinarith [hε, hK0])
        calc (1 + Real.log (2 + ((N:ℝ)^(k-1)) + (q:ℝ))) * (1 + Real.log (N:ℝ))
            ≤ (((k:ℝ)+3) * (1 + Real.log (N:ℝ))) * (1 + Real.log (N:ℝ)) :=
              mul_le_mul_of_nonneg_right hA1 hL0
          _ = ((k:ℝ)+3) * ((1 + Real.log (N:ℝ)) * (1 + Real.log (N:ℝ))) := by ring
          _ ≤ ((k:ℝ)+3) * P := mul_le_mul_of_nonneg_left hLL (by linarith)
      have hX3 : (q:ℝ) * ((1 + Real.log (2 + ((N:ℝ)^(k-1)) + (q:ℝ))) * (1 + Real.log (N:ℝ)))
          ≤ ((k:ℝ)+3) * X := by
        calc (q:ℝ) * ((1 + Real.log (2 + ((N:ℝ)^(k-1)) + (q:ℝ))) * (1 + Real.log (N:ℝ)))
            ≤ (q:ℝ) * (((k:ℝ)+3) * P) := mul_le_mul_of_nonneg_left hbracket hq0
          _ = ((k:ℝ)+3) * ((q:ℝ) * P) := by ring
          _ ≤ ((k:ℝ)+3) * X := mul_le_mul_of_nonneg_left hX_q (by linarith)
      have hNtk_q_le : (N:ℝ)^k*t/(q:ℝ) ≤ X := le_trans (le_mul_of_one_le_left hNtk_q_0 hP1) hX_B
      have hX4 : (N:ℝ) * (((k.factorial:ℝ)*t) * (((N:ℝ)^(k-1))*(k.factorial:ℝ)/(q:ℝ)))
          ≤ ((k.factorial:ℝ)^2) * X := by
        have heq : (N:ℝ) * (((k.factorial:ℝ)*t) * (((N:ℝ)^(k-1))*(k.factorial:ℝ)/(q:ℝ)))
            = ((k.factorial:ℝ)^2) * ((N:ℝ)^k*t/(q:ℝ)) := by
          have h3 : ((N:ℝ)^(k-1)) * (N:ℝ) = (N:ℝ)^k := by
            rw [← pow_succ]; congr 1; omega
          conv_rhs => rw [← h3]
          ring
        rw [heq]
        exact mul_le_mul_of_nonneg_left hNtk_q_le (by positivity)
      have hX5 : (N:ℝ) * (((k.factorial:ℝ)*t) * (1 + Real.log (2 + ((N:ℝ)^(k-1)) + (q:ℝ))))
          ≤ ((k.factorial:ℝ)*((k:ℝ)+3)) * X := by
        have hLt : (N:ℝ)*t*(1 + Real.log (N:ℝ)) ≤ X := by
          calc (N:ℝ)*t*(1 + Real.log (N:ℝ)) ≤ (N:ℝ)*t*P := mul_le_mul_of_nonneg_left hlog2 hNt_0
            _ = P * ((N:ℝ)*t) := by ring
            _ ≤ X := hX_C
        calc (N:ℝ) * (((k.factorial:ℝ)*t) * (1 + Real.log (2 + ((N:ℝ)^(k-1)) + (q:ℝ))))
            ≤ (N:ℝ) * (((k.factorial:ℝ)*t) * (((k:ℝ)+3) * (1 + Real.log (N:ℝ)))) :=
              mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hA1 (by positivity)) (by positivity)
          _ = ((k.factorial:ℝ)*((k:ℝ)+3)) * ((N:ℝ)*t*(1 + Real.log (N:ℝ))) := by ring
          _ ≤ ((k.factorial:ℝ)*((k:ℝ)+3)) * X :=
              mul_le_mul_of_nonneg_left hLt (by positivity)
      -- put together
      have hmain : ((N:ℝ)^(k-1)) + 1000*((((N:ℝ)^(k-1)) + (q:ℝ)*(1 + Real.log (2 + ((N:ℝ)^(k-1)) + (q:ℝ))))
              * (1 + Real.log N)
            + (N:ℝ)*(((k.factorial:ℝ)*t)*(((N:ℝ)^(k-1))*(k.factorial:ℝ)/(q:ℝ)
              + 1 + Real.log (2 + ((N:ℝ)^(k-1)) + (q:ℝ)))))
          ≤ (1 + 1000*(1 + ((k:ℝ)+3) + (k.factorial:ℝ)^2 + (k.factorial:ℝ)*((k:ℝ)+3))) * X := by
        have hexp : 1000*((((N:ℝ)^(k-1)) + (q:ℝ)*(1 + Real.log (2 + ((N:ℝ)^(k-1)) + (q:ℝ))))
              * (1 + Real.log N)
            + (N:ℝ)*(((k.factorial:ℝ)*t)*(((N:ℝ)^(k-1))*(k.factorial:ℝ)/(q:ℝ)
              + 1 + Real.log (2 + ((N:ℝ)^(k-1)) + (q:ℝ)))))
            = 1000 * (((N:ℝ)^(k-1)) * (1 + Real.log N)
              + (q:ℝ) * ((1 + Real.log (2 + ((N:ℝ)^(k-1)) + (q:ℝ))) * (1 + Real.log N))
              + (N:ℝ) * (((k.factorial:ℝ)*t) * (((N:ℝ)^(k-1))*(k.factorial:ℝ)/(q:ℝ)))
              + (N:ℝ) * (((k.factorial:ℝ)*t) * (1 + Real.log (2 + ((N:ℝ)^(k-1)) + (q:ℝ))))) := by ring
        rw [hexp]
        linarith [hX1, hX2, hX3, hX4, hX5]
      have hconst : 1 + 1000*(1 + ((k:ℝ)+3) + (k.factorial:ℝ)^2 + (k.factorial:ℝ)*((k:ℝ)+3))
          ≤ max 1 (max (10000000 * ((k:ℝ)+4) * (k.factorial:ℝ)^2) 1) := by
        have hkle : 1 + 1000*(1 + ((k:ℝ)+3) + (k.factorial:ℝ)^2 + (k.factorial:ℝ)*((k:ℝ)+3))
            ≤ 10000000 * ((k:ℝ)+4) * (k.factorial:ℝ)^2 := by
          have hk30 : (0:ℝ) ≤ (k:ℝ)+3 := by linarith
          have hk40 : (0:ℝ) ≤ (k:ℝ)+4 := by linarith
          have hk41 : (1:ℝ) ≤ (k:ℝ)+4 := by linarith
          have hF2_0 : (0:ℝ) ≤ (k.factorial:ℝ)^2 := by positivity
          have hF2_1 : (1:ℝ) ≤ (k.factorial:ℝ)^2 := one_le_pow₀ hF1
          have hFs : (k.factorial:ℝ) ≤ (k.factorial:ℝ)^2 := by nlinarith [hF1, hF0]
          have hT1 : (1:ℝ) ≤ ((k:ℝ)+4) * (k.factorial:ℝ)^2 :=
            le_trans hF2_1 (le_mul_of_one_le_left hF2_0 hk41)
          have hT2 : ((k:ℝ)+3) ≤ ((k:ℝ)+4) * (k.factorial:ℝ)^2 :=
            le_trans (by linarith : (k:ℝ)+3 ≤ (k:ℝ)+4)
              (le_mul_of_one_le_right hk40 hF2_1)
          have hT3 : (k.factorial:ℝ)^2 ≤ ((k:ℝ)+4) * (k.factorial:ℝ)^2 :=
            le_mul_of_one_le_left hF2_0 hk41
          have hT4 : (k.factorial:ℝ)*((k:ℝ)+3) ≤ ((k:ℝ)+4) * (k.factorial:ℝ)^2 := by
            calc (k.factorial:ℝ)*((k:ℝ)+3) ≤ (k.factorial:ℝ)*((k:ℝ)+4) :=
                  mul_le_mul_of_nonneg_left (by linarith) hF0
              _ ≤ (k.factorial:ℝ)^2 * ((k:ℝ)+4) := mul_le_mul_of_nonneg_right hFs hk40
              _ = ((k:ℝ)+4) * (k.factorial:ℝ)^2 := by ring
          have hbracket : 1 + ((k:ℝ)+3) + (k.factorial:ℝ)^2 + (k.factorial:ℝ)*((k:ℝ)+3)
              ≤ 4 * (((k:ℝ)+4) * (k.factorial:ℝ)^2) := by linarith
          have hmain2 : 1 + 1000*(1 + ((k:ℝ)+3) + (k.factorial:ℝ)^2 + (k.factorial:ℝ)*((k:ℝ)+3))
              ≤ 1 + 4000 * (((k:ℝ)+4) * (k.factorial:ℝ)^2) := by
            have hh := mul_le_mul_of_nonneg_left hbracket (by norm_num : (0:ℝ) ≤ 1000)
            linarith
          nlinarith [hmain2, hT1]
        exact le_trans hkle (le_trans (le_max_left _ _) (le_max_right _ _))
      refine le_trans hWle ?_
      refine le_trans hmain ?_
      refine le_trans (mul_le_mul_of_nonneg_right hconst hX0) ?_
      have hCm0 : (0:ℝ) ≤ max 1 (max (10000000 * ((k:ℝ)+4) * (k.factorial:ℝ)^2) 1) :=
        le_trans zero_le_one (le_max_left _ _)
      nlinarith [hX0, hCm0]


end WeylAux

open WeylAux

theorem weyl_inequality (k : ℕ) (hk : 1 ≤ k) {ε : ℝ} (hε : 0 < ε) {t : ℝ} (ht : 1 ≤ t) :
    ∃ C : ℝ, 0 < C ∧ ∀ (M : ℤ) (N : ℕ) (a q : ℤ) (f : Polynomial ℝ),
      q ≥ 1 → Int.gcd a q = 1 → f.natDegree = k →
      |f.leadingCoeff - (a : ℝ) / q| ≤ t / (q : ℝ) ^ 2 →
      ‖∑ x ∈ Finset.range N,
          Complex.exp (↑(2 * Real.pi * f.eval ((M : ℝ) + (x : ℝ))) * Complex.I)‖
        ≤ C * (N : ℝ) ^ (1 + ε) *
            (t / q + 1 / N + t / (N : ℝ) ^ (k - 1) + q / (N : ℝ) ^ k) ^ (2 : ℝ) ^ (1 - (k:ℝ)) := by
  rcases eq_or_lt_of_le hk with hk1 | hk2
  · subst hk1
    refine ⟨1, one_pos, ?_⟩
    intro M N a q f hq hgcd hf hlc
    rcases Nat.eq_zero_or_pos N with hN0 | hNpos
    · subst hN0
      have hz : (0:ℝ)^(1+ε) = 0 := Real.zero_rpow (by positivity)
      simp [hz]
    · have hN1 : (1:ℝ) ≤ (N:ℝ) := by exact_mod_cast hNpos
      have hNRpos : (0:ℝ) < (N:ℝ) := lt_of_lt_of_le one_pos hN1
      have hq0 : (0:ℝ) < (q:ℝ) := by
        have h : (1:ℝ) ≤ (q:ℝ) := by exact_mod_cast hq
        linarith
      have hsum_le : ‖∑ x ∈ Finset.range N,
          Complex.exp (↑(2 * Real.pi * f.eval ((M:ℝ) + (x:ℝ))) * Complex.I)‖ ≤ (N:ℝ) := by
        calc ‖∑ x ∈ Finset.range N,
              Complex.exp (↑(2 * Real.pi * f.eval ((M:ℝ) + (x:ℝ))) * Complex.I)‖
            ≤ ∑ x ∈ Finset.range N,
                ‖Complex.exp (↑(2 * Real.pi * f.eval ((M:ℝ) + (x:ℝ))) * Complex.I)‖ := norm_sum_le _ _
          _ = ∑ x ∈ Finset.range N, (1:ℝ) := by
              apply Finset.sum_congr rfl
              intro x _
              rw [Complex.norm_exp]
              simp
          _ = (N:ℝ) := by simp
      have hsub1 : (N:ℝ)^((1:ℕ)-1) = 1 := by simp
      have hpow1 : (N:ℝ)^(1:ℕ) = (N:ℝ) := by simp
      have hexp : (2:ℝ)^(1-((1:ℕ):ℝ)) = 1 := by norm_num
      rw [hsub1, hpow1, hexp, Real.rpow_one, one_mul, div_one]
      have hB1 : (1:ℝ) ≤ t/(q:ℝ) + 1/(N:ℝ) + t + (q:ℝ)/(N:ℝ) := by
        have h1 : (0:ℝ) ≤ t/(q:ℝ) := div_nonneg (le_trans zero_le_one ht) hq0.le
        have h2 : (0:ℝ) ≤ 1/(N:ℝ) := div_nonneg zero_le_one hNRpos.le
        have h3 : (0:ℝ) ≤ (q:ℝ)/(N:ℝ) := div_nonneg hq0.le hNRpos.le
        linarith
      have hY : (N:ℝ) ≤ (N:ℝ)^(1+ε) := by
        have h2 : (N:ℝ)^(1+ε) = (N:ℝ)^(1:ℝ) * (N:ℝ)^ε := Real.rpow_add hNRpos 1 ε
        have h3 : (1:ℝ) ≤ (N:ℝ)^ε := Real.one_le_rpow hN1 hε.le
        rw [h2, Real.rpow_one]; nlinarith
      calc ‖∑ x ∈ Finset.range N,
            Complex.exp (↑(2 * Real.pi * f.eval ((M:ℝ) + (x:ℝ))) * Complex.I)‖ ≤ (N:ℝ) := hsum_le
        _ ≤ (N:ℝ)^(1+ε) := hY
        _ ≤ (N:ℝ)^(1+ε) * (t/(q:ℝ) + 1/(N:ℝ) + t + (q:ℝ)/(N:ℝ)) :=
              le_mul_of_one_le_right (by positivity) hB1
  · have hk2' : 2 ≤ k := hk2
    have hkd : (0:ℝ) < (k:ℝ) - 1 := by
      have h : (2:ℝ) ≤ (k:ℝ) := by exact_mod_cast hk2'
      linarith
    have hr : ((k-1:ℕ):ℝ) = (k:ℝ) - 1 := by
      rw [Nat.cast_sub (by omega : 1 ≤ k)]; norm_num
    obtain ⟨Cdiv, hCdivpos, hCdiv⟩ :=
      Commons.NumberTheory.DivisorBound.card_divisors_le_rpow (ε/((k:ℝ)-1)) (div_pos hε hkd)
    have hCη0 : (0:ℝ) < Cdiv^(k-1) := by positivity
    obtain ⟨Cρ, hCρpos, hCρ⟩ := rho_sum_le k hk2' hε ht
    obtain ⟨N₀, hN₀pos, hN₀⟩ := log_le_rpow_threshold (c := ε*((2:ℝ)^(k-1))/2) (by positivity)
    set C₀ : ℝ := max 1 (cw (k-1) * ((k-1:ℝ) + Cdiv^(k-1)*Cρ + Cdiv^(k-1)*Cρ + 1)) with hC0def
    have hC0pos : (0:ℝ) < C₀ := lt_of_lt_of_le one_pos (le_max_left _ _)
    have hC01 : (1:ℝ) ≤ C₀ := le_max_left _ _
    set Csmall : ℝ := max 1 ((max 1 N₀)^(max 1 (1-ε))) with hCsdef
    have hCs1 : (1:ℝ) ≤ Csmall := le_max_left _ _
    refine ⟨max C₀ Csmall, lt_of_lt_of_le hC0pos (le_max_left _ _), ?_⟩
    intro M N a q f hq hgcd hf hlc
    rcases Nat.eq_zero_or_pos N with hN0 | hNpos
    · subst hN0
      have hz : (0:ℝ)^(1+ε) = 0 := Real.zero_rpow (by positivity)
      simp [hz]
    · have hN1 : (1:ℝ) ≤ (N:ℝ) := by exact_mod_cast hNpos
      have hNRpos : (0:ℝ) < (N:ℝ) := lt_of_lt_of_le one_pos hN1
      have hNR0 : (0:ℝ) ≤ (N:ℝ) := le_of_lt hNRpos
      have hq0 : (0:ℝ) < (q:ℝ) := by
        have h : (1:ℝ) ≤ (q:ℝ) := by exact_mod_cast hq
        linarith
      set B : ℝ := t/(q:ℝ) + 1/(N:ℝ) + t/((N:ℝ)^(k-1)) + (q:ℝ)/((N:ℝ)^k) with hBdef
      by_cases hcase : N₀ ≤ (N:ℝ)
      · -- large N
        have hlogN : 1 + Real.log (N:ℝ) ≤ (N:ℝ)^(ε*((2:ℝ)^(k-1))/8) := by
          have h := hN₀ N hcase
          rwa [show ε*((2:ℝ)^(k-1))/2/4 = ε*((2:ℝ)^(k-1))/8 by ring] at h
        have hρ : ∑ m ∈ Finset.Icc 1 (N^(k-1)), rho (((k.factorial:ℝ)*f.leadingCoeff) * (m:ℝ)) N
            ≤ Cρ * ((N:ℝ)^(ε*((2:ℝ)^(k-1))/2)
                * ((N:ℝ)^(k-1) + (q:ℝ) + (N:ℝ)^k*t/(q:ℝ) + (N:ℝ)*t) + 1) :=
          hCρ hq hgcd hlc N hNpos hlogN
        have hCη : ∀ m : ℕ, 1 ≤ m → (((Nat.divisors m).card : ℝ))^(k-1) ≤ Cdiv^(k-1) * (m:ℝ)^ε := by
          intro m hm
          have h1 : ((Nat.divisors m).card : ℝ) ≤ Cdiv * (m:ℝ)^(ε/((k:ℝ)-1)) := hCdiv m
          have h2 : (((Nat.divisors m).card : ℝ))^(k-1) ≤ (Cdiv * (m:ℝ)^(ε/((k:ℝ)-1)))^(k-1) :=
            pow_le_pow_left₀ (Nat.cast_nonneg _) h1 _
          have h3 : (Cdiv * (m:ℝ)^(ε/((k:ℝ)-1)))^(k-1) = Cdiv^(k-1) * (m:ℝ)^ε := by
            rw [mul_pow]
            congr 1
            rw [← Real.rpow_natCast ((m:ℝ)^(ε/((k:ℝ)-1))) (k-1),
              ← Real.rpow_mul (Nat.cast_nonneg m)]
            congr 1
            rw [hr]
            field_simp
          calc (((Nat.divisors m).card : ℝ))^(k-1) ≤ (Cdiv * (m:ℝ)^(ε/((k:ℝ)-1)))^(k-1) := h2
            _ = Cdiv^(k-1) * (m:ℝ)^ε := h3
        have hpr := diff_iter (fun y : ℤ => 2*Real.pi*f.eval ((M:ℝ) + (y:ℝ))) (k-1) N
        have hSe : (∑ x ∈ Finset.range N,
              Complex.exp (↑(2 * Real.pi * f.eval ((M:ℝ) + (x:ℝ))) * Complex.I))
            = ∑ x ∈ Finset.range N,
                Ephase (fun y : ℤ => 2*Real.pi*f.eval ((M:ℝ) + (y:ℝ))) (x:ℤ) := by
          apply Finset.sum_congr rfl
          intro x _
          simp only [Ephase, Int.cast_natCast]
        have hchain : ‖∑ x ∈ Finset.range N,
              Complex.exp (↑(2 * Real.pi * f.eval ((M:ℝ) + (x:ℝ))) * Complex.I)‖^(2^(k-1))
            ≤ cw (k-1) * (N:ℝ)^(2^(k-1)-(k-1)-1)
              * ((k-1:ℝ)*(N:ℝ)^(k-1)
                + Cdiv^(k-1)*(N:ℝ)^(ε*((k-1:ℕ):ℝ))
                  * (Cρ * ((N:ℝ)^(ε*((2:ℝ)^(k-1))/2)
                      * ((N:ℝ)^(k-1) + (q:ℝ) + (N:ℝ)^k*t/(q:ℝ) + (N:ℝ)*t) + 1))) := by
          rw [hSe]
          refine le_trans hpr ?_
          apply mul_le_mul_of_nonneg_left _ (mul_nonneg (le_of_lt (cw_pos (k-1))) (by positivity))
          have hsumstep : (∑ h : Fin (k-1) → Fin N,
                ‖Gsum (fun y : ℤ => 2*Real.pi*f.eval ((M:ℝ) + (y:ℝ))) (k-1) N
                  (fun i => ((h i : Fin N) : ℕ))‖)
              ≤ ∑ h : Fin (k-1) → Fin N,
                  rho (((k.factorial:ℝ)*f.leadingCoeff) * ((∏ i, ((h i : Fin N) : ℕ)) : ℝ)) N :=
            Finset.sum_le_sum (fun h _ => Gsum_le_rho k hk2' f hf M N hNpos h)
          refine le_trans hsumstep ?_
          refine le_trans (tuple_sum_le k hk2' (le_of_lt hε) (le_of_lt hCη0) hCη) ?_
          refine add_le_add_right ?_ _
          have hh := mul_le_mul_of_nonneg_left hρ
            (show (0:ℝ) ≤ Cdiv^(k-1) * (N:ℝ)^(ε*((k-1:ℕ):ℝ)) by positivity)
          simpa [hr] using hh
        have hWB : (N:ℝ)^(k-1) + (q:ℝ) + (N:ℝ)^k*t/(q:ℝ) + (N:ℝ)*t = (N:ℝ)^k * B := by
          have hNkpos : (0:ℝ) < (N:ℝ)^k := by positivity
          have hNk1pos : (0:ℝ) < (N:ℝ)^(k-1) := by positivity
          have h1 : (N:ℝ)^k * (1/(N:ℝ)) = (N:ℝ)^(k-1) := by
            rw [mul_one_div, div_eq_iff (ne_of_gt hNRpos)]
            rw [← pow_succ]; congr 1; omega
          have h3 : (N:ℝ)^k * (t/(N:ℝ)^(k-1)) = (N:ℝ)*t := by
            rw [← mul_div_assoc, div_eq_iff (ne_of_gt hNk1pos)]
            rw [show (N:ℝ)^k = (N:ℝ)^(k-1)*(N:ℝ) by rw [← pow_succ]; congr 1; omega]
            ring
          have h4 : (N:ℝ)^k * ((q:ℝ)/(N:ℝ)^k) = (q:ℝ) := by
            rw [← mul_div_assoc, mul_div_cancel_left₀ _ (ne_of_gt hNkpos)]
          have h5 : (N:ℝ)^k * (t/(q:ℝ)) = (N:ℝ)^k*t/(q:ℝ) := by rw [← mul_div_assoc]
          rw [hBdef]
          rw [mul_add, mul_add, mul_add, h5, h1, h3, h4]
          ring
        rw [hWB] at hchain
        -- now the pure arithmetic
        have hp0 : (0:ℝ) ≤ cw (k-1) := le_of_lt (cw_pos (k-1))
        have hCη0' : (0:ℝ) ≤ Cdiv^(k-1) := le_of_lt hCη0
        have hCρ0 : (0:ℝ) ≤ Cρ := le_of_lt hCρpos
        have hB0 : (0:ℝ) ≤ B := by
          rw [hBdef]
          have h1 : (0:ℝ) ≤ t/(q:ℝ) := div_nonneg (le_trans zero_le_one ht) hq0.le
          have h2 : (0:ℝ) ≤ 1/(N:ℝ) := div_nonneg zero_le_one hNR0
          have h3 : (0:ℝ) ≤ t/((N:ℝ)^(k-1)) := div_nonneg (le_trans zero_le_one ht) (by positivity)
          have h4 : (0:ℝ) ≤ (q:ℝ)/((N:ℝ)^k) := div_nonneg hq0.le (by positivity)
          linarith
        have hB1 : 1/(N:ℝ) ≤ B := by
          rw [hBdef]
          have h1 : (0:ℝ) ≤ t/(q:ℝ) := div_nonneg (le_trans zero_le_one ht) hq0.le
          have h2 : (0:ℝ) ≤ t/((N:ℝ)^(k-1)) := div_nonneg (le_trans zero_le_one ht) (by positivity)
          have h3 : (0:ℝ) ≤ (q:ℝ)/((N:ℝ)^k) := div_nonneg hq0.le (by positivity)
          linarith
        have hKre0 : (0:ℝ) ≤ (2:ℝ)^(k-1) := by positivity
        have hk1R0 : (0:ℝ) ≤ (k:ℝ) - 1 := le_of_lt hkd
        have hk1leK : k ≤ 2^(k-1) := by have := Nat.lt_two_pow_self (n := k-1); omega
        have hKr : ((2^(k-1) - (k-1) - 1 : ℕ) : ℝ) = (2:ℝ)^(k-1) - ((k-1:ℕ):ℝ) - 1 := by
          rw [Nat.sub_sub, Nat.cast_sub (by omega : (k-1)+1 ≤ 2^(k-1))]
          push_cast
          rw [hr]; ring
        have hK1r : ((2^(k-1) - 1 : ℕ) : ℝ) = (2:ℝ)^(k-1) - 1 := by
          rw [Nat.cast_sub (Nat.one_le_two_pow : 1 ≤ 2^(k-1))]
          push_cast; ring
        have hYeq : ((N:ℝ)^(1+ε))^(2^(k-1)) = (N:ℝ)^((1+ε)*((2:ℝ)^(k-1))) := by
          rw [← Real.rpow_natCast ((N:ℝ)^(1+ε)) (2^(k-1))]
          rw [← Real.rpow_mul hNR0]
          push_cast; ring
        have hrle : ((k-1:ℕ):ℝ) ≤ (2:ℝ)^(k-1)/2 := by
          have h1 : k-1 ≤ 2^(k-2) := by have := Nat.lt_two_pow_self (n := k-2); omega
          have h2 : (2:ℝ)^(k-1) = 2 * (2:ℝ)^(k-2) := by
            rw [show k-1 = (k-2)+1 by omega, pow_succ]; ring
          calc ((k-1:ℕ):ℝ) ≤ ((2^(k-2):ℕ):ℝ) := by exact_mod_cast h1
            _ = (2:ℝ)^(k-2) := by push_cast; rfl
            _ = (2:ℝ)^(k-1)/2 := by rw [h2]; ring
        have hpart1 : cw (k-1) * (N:ℝ)^(2^(k-1)-(k-1)-1) * ((k-1:ℝ)*(N:ℝ)^(k-1))
            ≤ (cw (k-1)*(k-1:ℝ)) * ((N:ℝ)^((1+ε)*((2:ℝ)^(k-1))) * B) := by
          have hcomb : (N:ℝ)^(2^(k-1)-(k-1)-1) * (N:ℝ)^(k-1) = (N:ℝ)^(2^(k-1)-1) := by
            rw [← pow_add]; congr 1; omega
          have hle : (N:ℝ)^(2^(k-1)-1) ≤ (N:ℝ)^((1+ε)*((2:ℝ)^(k-1))) * B := by
            have h1 : (N:ℝ)^((1+ε)*((2:ℝ)^(k-1))) * (1/(N:ℝ))
                ≤ (N:ℝ)^((1+ε)*((2:ℝ)^(k-1))) * B :=
              mul_le_mul_of_nonneg_left hB1 (Real.rpow_nonneg hNR0 _)
            have h2 : (N:ℝ)^((1+ε)*((2:ℝ)^(k-1))) * (1/(N:ℝ))
                = (N:ℝ)^((1+ε)*((2:ℝ)^(k-1)) - 1) := by
              rw [one_div, ← Real.rpow_neg_one, ← Real.rpow_add hNRpos]
              congr 1
            rw [h2] at h1
            have h3 : ((2:ℝ)^(k-1) - 1 : ℝ) ≤ (1+ε)*((2:ℝ)^(k-1)) - 1 := by nlinarith [hε, hKre0]
            have h4 : (N:ℝ)^(((2:ℝ)^(k-1) - 1 : ℝ)) ≤ (N:ℝ)^((1+ε)*((2:ℝ)^(k-1)) - 1) :=
              Real.rpow_le_rpow_of_exponent_le hN1 h3
            rw [← hK1r] at h4
            rw [Real.rpow_natCast (N:ℝ) (2^(k-1)-1)] at h4
            linarith [h1, h4]
          calc cw (k-1) * (N:ℝ)^(2^(k-1)-(k-1)-1) * ((k-1:ℝ)*(N:ℝ)^(k-1))
              = (cw (k-1)*(k-1:ℝ)) * ((N:ℝ)^(2^(k-1)-(k-1)-1) * (N:ℝ)^(k-1)) := by ring
            _ = (cw (k-1)*(k-1:ℝ)) * (N:ℝ)^(2^(k-1)-1) := by rw [hcomb]
            _ ≤ (cw (k-1)*(k-1:ℝ)) * ((N:ℝ)^((1+ε)*((2:ℝ)^(k-1))) * B) :=
                mul_le_mul_of_nonneg_left hle (mul_nonneg hp0 hk1R0)
        have hid : (N:ℝ)^(2^(k-1)-(k-1)-1) * (N:ℝ)^(ε*((k-1:ℕ):ℝ))
              * (N:ℝ)^(ε*((2:ℝ)^(k-1))/2) * (N:ℝ)^k
            = (N:ℝ)^(((2^(k-1)-(k-1)-1 : ℕ):ℝ) + ε*((k-1:ℕ):ℝ) + ε*((2:ℝ)^(k-1))/2 + (k:ℝ)) := by
          rw [← Real.rpow_natCast (N:ℝ) (2^(k-1)-(k-1)-1), ← Real.rpow_natCast (N:ℝ) k]
          rw [← Real.rpow_add hNRpos, ← Real.rpow_add hNRpos, ← Real.rpow_add hNRpos]
        have hexp : ((2^(k-1)-(k-1)-1 : ℕ):ℝ) + ε*((k-1:ℕ):ℝ) + ε*((2:ℝ)^(k-1))/2 + (k:ℝ)
            ≤ (1+ε)*((2:ℝ)^(k-1)) := by
          rw [hKr, hr]
          have hkR : ((k:ℕ):ℝ) = ((k-1:ℕ):ℝ) + 1 := by rw [hr]; ring
          rw [hkR]
          nlinarith [hrle, hε]
        have hprod : (N:ℝ)^(2^(k-1)-(k-1)-1) * (N:ℝ)^(ε*((k-1:ℕ):ℝ))
              * ((N:ℝ)^(ε*((2:ℝ)^(k-1))/2) * (N:ℝ)^k)
            ≤ (N:ℝ)^((1+ε)*((2:ℝ)^(k-1))) := by
          rw [show (N:ℝ)^(2^(k-1)-(k-1)-1) * (N:ℝ)^(ε*((k-1:ℕ):ℝ))
                * ((N:ℝ)^(ε*((2:ℝ)^(k-1))/2) * (N:ℝ)^k)
              = (N:ℝ)^(2^(k-1)-(k-1)-1) * (N:ℝ)^(ε*((k-1:ℕ):ℝ))
                * (N:ℝ)^(ε*((2:ℝ)^(k-1))/2) * (N:ℝ)^k by ring]
          rw [hid]
          exact Real.rpow_le_rpow_of_exponent_le hN1 hexp
        have hcomb2 : (N:ℝ)^(2^(k-1)-(k-1)-1) * (N:ℝ)^(ε*((k-1:ℕ):ℝ))
            ≤ (N:ℝ)^((1+ε)*((2:ℝ)^(k-1))) * B := by
          have h1 : (N:ℝ)^((1+ε)*((2:ℝ)^(k-1))) * (1/(N:ℝ))
              ≤ (N:ℝ)^((1+ε)*((2:ℝ)^(k-1))) * B :=
            mul_le_mul_of_nonneg_left hB1 (Real.rpow_nonneg hNR0 _)
          have h2 : (N:ℝ)^((1+ε)*((2:ℝ)^(k-1))) * (1/(N:ℝ))
              = (N:ℝ)^((1+ε)*((2:ℝ)^(k-1)) - 1) := by
            rw [one_div, ← Real.rpow_neg_one, ← Real.rpow_add hNRpos]
            congr 1
          rw [h2] at h1
          have hpow : (N:ℝ)^(2^(k-1)-(k-1)-1) * (N:ℝ)^(ε*((k-1:ℕ):ℝ))
              = (N:ℝ)^(((2^(k-1)-(k-1)-1 : ℕ):ℝ) + ε*((k-1:ℕ):ℝ)) := by
            rw [← Real.rpow_natCast (N:ℝ) (2^(k-1)-(k-1)-1), ← Real.rpow_add hNRpos]
          rw [hpow]
          have hexp2 : ((2^(k-1)-(k-1)-1 : ℕ):ℝ) + ε*((k-1:ℕ):ℝ) ≤ (1+ε)*((2:ℝ)^(k-1)) - 1 := by
            rw [hKr]
            nlinarith [hrle, hε, hKre0]
          have h3 : (N:ℝ)^(((2^(k-1)-(k-1)-1 : ℕ):ℝ) + ε*((k-1:ℕ):ℝ))
              ≤ (N:ℝ)^((1+ε)*((2:ℝ)^(k-1)) - 1) :=
            Real.rpow_le_rpow_of_exponent_le hN1 hexp2
          linarith [h1, h3]
        have hpart2 : cw (k-1) * (N:ℝ)^(2^(k-1)-(k-1)-1)
              * (Cdiv^(k-1)*(N:ℝ)^(ε*((k-1:ℕ):ℝ))
                * (Cρ * ((N:ℝ)^(ε*((2:ℝ)^(k-1))/2) * ((N:ℝ)^k * B) + 1)))
            ≤ (2*cw (k-1)*Cdiv^(k-1)*Cρ) * ((N:ℝ)^((1+ε)*((2:ℝ)^(k-1))) * B) := by
          calc cw (k-1) * (N:ℝ)^(2^(k-1)-(k-1)-1)
                * (Cdiv^(k-1)*(N:ℝ)^(ε*((k-1:ℕ):ℝ))
                  * (Cρ * ((N:ℝ)^(ε*((2:ℝ)^(k-1))/2) * ((N:ℝ)^k * B) + 1)))
              = (cw (k-1)*Cdiv^(k-1)*Cρ) * ((N:ℝ)^(2^(k-1)-(k-1)-1) * (N:ℝ)^(ε*((k-1:ℕ):ℝ))
                  * ((N:ℝ)^(ε*((2:ℝ)^(k-1))/2) * (N:ℝ)^k) * B)
                + (cw (k-1)*Cdiv^(k-1)*Cρ) * ((N:ℝ)^(2^(k-1)-(k-1)-1) * (N:ℝ)^(ε*((k-1:ℕ):ℝ))) := by ring
            _ ≤ (cw (k-1)*Cdiv^(k-1)*Cρ) * ((N:ℝ)^((1+ε)*((2:ℝ)^(k-1))) * B)
                + (cw (k-1)*Cdiv^(k-1)*Cρ) * ((N:ℝ)^((1+ε)*((2:ℝ)^(k-1))) * B) := by
                apply add_le_add
                · exact mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hprod hB0) (by positivity)
                · exact mul_le_mul_of_nonneg_left hcomb2 (by positivity)
            _ = (2*cw (k-1)*Cdiv^(k-1)*Cρ) * ((N:ℝ)^((1+ε)*((2:ℝ)^(k-1))) * B) := by ring
        have hconst : cw (k-1) * (k-1:ℝ) + 2*cw (k-1)*Cdiv^(k-1)*Cρ ≤ C₀ := by
          rw [hC0def]
          have h1 : cw (k-1) * ((k-1:ℝ) + Cdiv^(k-1)*Cρ + Cdiv^(k-1)*Cρ + 1)
              = cw (k-1)*(k-1:ℝ) + cw (k-1)*Cdiv^(k-1)*Cρ + cw (k-1)*Cdiv^(k-1)*Cρ + cw (k-1) := by ring
          nlinarith [h1, hp0,
            le_max_left (1:ℝ) (cw (k-1) * ((k-1:ℝ) + Cdiv^(k-1)*Cρ + Cdiv^(k-1)*Cρ + 1)),
            le_max_right (1:ℝ) (cw (k-1) * ((k-1:ℝ) + Cdiv^(k-1)*Cρ + Cdiv^(k-1)*Cρ + 1))]
        have hkey : cw (k-1) * (N:ℝ)^(2^(k-1)-(k-1)-1)
              * ((k-1:ℝ)*(N:ℝ)^(k-1)
                + Cdiv^(k-1)*(N:ℝ)^(ε*((k-1:ℕ):ℝ))
                  * (Cρ * ((N:ℝ)^(ε*((2:ℝ)^(k-1))/2) * ((N:ℝ)^k * B) + 1)))
            ≤ C₀ * ((N:ℝ)^((1+ε)*((2:ℝ)^(k-1))) * B) := by
          have hsplit : cw (k-1) * (N:ℝ)^(2^(k-1)-(k-1)-1)
                * ((k-1:ℝ)*(N:ℝ)^(k-1)
                  + Cdiv^(k-1)*(N:ℝ)^(ε*((k-1:ℕ):ℝ))
                    * (Cρ * ((N:ℝ)^(ε*((2:ℝ)^(k-1))/2) * ((N:ℝ)^k * B) + 1)))
              = cw (k-1) * (N:ℝ)^(2^(k-1)-(k-1)-1) * ((k-1:ℝ)*(N:ℝ)^(k-1))
                + cw (k-1) * (N:ℝ)^(2^(k-1)-(k-1)-1)
                  * (Cdiv^(k-1)*(N:ℝ)^(ε*((k-1:ℕ):ℝ))
                    * (Cρ * ((N:ℝ)^(ε*((2:ℝ)^(k-1))/2) * ((N:ℝ)^k * B) + 1))) := by ring
          rw [hsplit]
          have hy0 : (0:ℝ) ≤ (N:ℝ)^((1+ε)*((2:ℝ)^(k-1))) * B :=
            mul_nonneg (Real.rpow_nonneg hNR0 _) hB0
          nlinarith [hpart1, hpart2, hconst, hy0]
        have h6 : ‖∑ x ∈ Finset.range N,
              Complex.exp (↑(2 * Real.pi * f.eval ((M:ℝ) + (x:ℝ))) * Complex.I)‖^(2^(k-1))
            ≤ C₀ * (N:ℝ)^((1+ε)*((2:ℝ)^(k-1))) * B :=
          le_trans hchain (by simpa [mul_assoc] using hkey)
        -- root extraction
        have hKne : (2^(k-1) : ℕ) ≠ 0 := by positivity
        have hKcast : ((2^(k-1) : ℕ) : ℝ) = (2:ℝ)^(k-1) := by push_cast; rfl
        have hCm1 : (1:ℝ) ≤ max C₀ Csmall := le_trans hC01 (le_max_left _ _)
        have hCm0 : (0:ℝ) ≤ max C₀ Csmall := le_trans zero_le_one hCm1
        have hCmax : C₀ ≤ (max C₀ Csmall)^(2^(k-1)) := by
          have h1 : C₀ ≤ max C₀ Csmall := le_max_left _ _
          have h2 : max C₀ Csmall ≤ (max C₀ Csmall)^(2^(k-1)) := by
            have h := pow_le_pow_right₀ hCm1 (by have := Nat.one_le_two_pow (n := k-1); omega : 1 ≤ 2^(k-1))
            simpa using h
          linarith
        have hpow : ‖∑ x ∈ Finset.range N,
              Complex.exp (↑(2 * Real.pi * f.eval ((M:ℝ) + (x:ℝ))) * Complex.I)‖^(2^(k-1))
            ≤ (max C₀ Csmall * (N:ℝ)^(1+ε) * B^(((2^(k-1):ℕ):ℝ)⁻¹))^(2^(k-1)) := by
          refine le_trans h6 ?_
          conv_rhs => rw [mul_pow, mul_pow, ← Real.rpow_natCast ((N:ℝ)^(1+ε)) (2^(k-1)),
            ← Real.rpow_mul hNR0, Real.rpow_inv_natCast_pow hB0 hKne, hKcast]
          have hXB : (0:ℝ) ≤ (N:ℝ)^((1+ε)*((2:ℝ)^(k-1))) * B :=
            mul_nonneg (Real.rpow_nonneg hNR0 _) hB0
          nlinarith [hCmax, hXB]
        have hroot : ‖∑ x ∈ Finset.range N,
              Complex.exp (↑(2 * Real.pi * f.eval ((M:ℝ) + (x:ℝ))) * Complex.I)‖
            ≤ max C₀ Csmall * (N:ℝ)^(1+ε) * B^(((2^(k-1):ℕ):ℝ)⁻¹) :=
          le_of_pow_le_pow_left₀ hKne
            (mul_nonneg (mul_nonneg hCm0 (Real.rpow_nonneg hNR0 _))
              (Real.rpow_nonneg hB0 _)) hpow
        have hexpK : (2:ℝ)^(1-(k:ℝ)) = ((2:ℝ)^(k-1))⁻¹ := by
          have h1 : (1:ℝ)-(k:ℝ) = -(((k-1:ℕ):ℝ)) := by rw [hr]; ring
          rw [h1, Real.rpow_neg (by norm_num : (0:ℝ) ≤ 2), Real.rpow_natCast]
        rw [hexpK]
        rw [show (((2:ℝ)^(k-1))⁻¹) = (((2^(k-1):ℕ):ℝ))⁻¹ by rw [hKcast]]
        exact hroot
      · -- small N
        have hNle : (N:ℝ) ≤ max 1 N₀ := by
          have h : (N:ℝ) < N₀ := not_le.mp hcase
          exact le_trans h.le (le_max_right _ _)
        have hsum_le : ‖∑ x ∈ Finset.range N,
            Complex.exp (↑(2 * Real.pi * f.eval ((M:ℝ) + (x:ℝ))) * Complex.I)‖ ≤ (N:ℝ) := by
          calc ‖∑ x ∈ Finset.range N,
                Complex.exp (↑(2 * Real.pi * f.eval ((M:ℝ) + (x:ℝ))) * Complex.I)‖
              ≤ ∑ x ∈ Finset.range N,
                  ‖Complex.exp (↑(2 * Real.pi * f.eval ((M:ℝ) + (x:ℝ))) * Complex.I)‖ := norm_sum_le _ _
            _ = ∑ x ∈ Finset.range N, (1:ℝ) := by
                apply Finset.sum_congr rfl
                intro x _
                rw [Complex.norm_exp]
                simp
            _ = (N:ℝ) := by simp
        have hB1 : 1/(N:ℝ) ≤ B := by
          rw [hBdef]
          have h1 : (0:ℝ) ≤ t/(q:ℝ) := div_nonneg (le_trans zero_le_one ht) hq0.le
          have h2 : (0:ℝ) ≤ t/((N:ℝ)^(k-1)) := div_nonneg (le_trans zero_le_one ht) (by positivity)
          have h3 : (0:ℝ) ≤ (q:ℝ)/((N:ℝ)^k) := div_nonneg hq0.le (by positivity)
          linarith
        have hB0 : (0:ℝ) ≤ B := le_trans (div_nonneg zero_le_one hNR0) hB1
        have hK1 : (1:ℝ) ≤ (2:ℝ)^(k-1) := one_le_pow₀ (by norm_num)
        have hinf : (1:ℝ) ≤ ((2:ℝ)^(k-1))⁻¹ * (2:ℝ)^(k-1) := by
          rw [inv_mul_cancel₀ (ne_of_gt (lt_of_lt_of_le zero_lt_one hK1))]
        have hKinv1 : ((2:ℝ)^(k-1))⁻¹ ≤ 1 := by
          rw [inv_le_one₀ (lt_of_lt_of_le zero_lt_one hK1)]
          exact hK1
        have hCs : (N:ℝ)^(1-ε) ≤ Csmall := by
          rw [hCsdef]
          have hbase : (1:ℝ) ≤ max 1 N₀ := le_max_left _ _
          by_cases h : (1:ℝ) - ε ≤ 0
          · have h1 : (N:ℝ)^(1-ε) ≤ 1 := Real.rpow_le_one_of_one_le_of_nonpos hN1 h
            linarith [le_max_left (1:ℝ) ((max 1 N₀)^(max 1 (1-ε)))]
          · push_neg at h
            have h1 : (N:ℝ)^(1-ε) ≤ (max 1 N₀)^(1-ε) :=
              Real.rpow_le_rpow hNR0 hNle (le_of_lt h)
            have h2 : (max 1 N₀)^(1-ε) ≤ (max 1 N₀)^(max 1 (1-ε)) :=
              Real.rpow_le_rpow_of_exponent_le hbase (le_max_right _ _)
            linarith [le_max_right (1:ℝ) ((max 1 N₀)^(max 1 (1-ε)))]
        have hBN : (1/(N:ℝ))^(((2:ℝ)^(k-1))⁻¹) ≤ B^(((2:ℝ)^(k-1))⁻¹) :=
          Real.rpow_le_rpow (div_nonneg zero_le_one hNR0) hB1 (inv_nonneg.mpr (by positivity))
        have hinv : (1/(N:ℝ))^(((2:ℝ)^(k-1))⁻¹) = (N:ℝ)^(-((2:ℝ)^(k-1))⁻¹) := by
          rw [one_div, Real.inv_rpow hNR0, Real.rpow_neg hNR0]
        have hmid : (N:ℝ)^(1+ε-((2:ℝ)^(k-1))⁻¹)
            ≤ (N:ℝ)^(1+ε) * B^(((2:ℝ)^(k-1))⁻¹) := by
          have h1 : (N:ℝ)^(1+ε) * (1/(N:ℝ))^(((2:ℝ)^(k-1))⁻¹)
              ≤ (N:ℝ)^(1+ε) * B^(((2:ℝ)^(k-1))⁻¹) :=
            mul_le_mul_of_nonneg_left hBN (Real.rpow_nonneg hNR0 _)
          rw [hinv, ← Real.rpow_add hNRpos] at h1
          exact h1
        have hexpK : (2:ℝ)^(1-(k:ℝ)) = ((2:ℝ)^(k-1))⁻¹ := by
          have h1 : (1:ℝ)-(k:ℝ) = -(((k-1:ℕ):ℝ)) := by rw [hr]; ring
          rw [h1, Real.rpow_neg (by norm_num : (0:ℝ) ≤ 2), Real.rpow_natCast]
        rw [hexpK]
        calc ‖∑ x ∈ Finset.range N,
              Complex.exp (↑(2 * Real.pi * f.eval ((M:ℝ) + (x:ℝ))) * Complex.I)‖ ≤ (N:ℝ) := hsum_le
          _ = (N:ℝ)^(1-ε) * (N:ℝ)^ε := by
              rw [← Real.rpow_add hNRpos, show (1:ℝ)-ε+ε = 1 by ring, Real.rpow_one]
          _ ≤ Csmall * (N:ℝ)^ε := mul_le_mul_of_nonneg_right hCs (by positivity)
          _ ≤ max C₀ Csmall * (N:ℝ)^(1+ε) * B^(((2:ℝ)^(k-1))⁻¹) := by
              have h1 : (N:ℝ)^ε ≤ (N:ℝ)^(1+ε-((2:ℝ)^(k-1))⁻¹) :=
                Real.rpow_le_rpow_of_exponent_le hN1 (by linarith [hKinv1])
              have h2 : Csmall * (N:ℝ)^ε ≤ max C₀ Csmall * (N:ℝ)^(1+ε-((2:ℝ)^(k-1))⁻¹) := by
                apply mul_le_mul (le_max_right _ _) h1 (by positivity) (by positivity)
              calc Csmall * (N:ℝ)^ε
                  ≤ max C₀ Csmall * (N:ℝ)^(1+ε-((2:ℝ)^(k-1))⁻¹) := h2
                _ ≤ max C₀ Csmall * ((N:ℝ)^(1+ε) * B^(((2:ℝ)^(k-1))⁻¹)) :=
                    mul_le_mul_of_nonneg_left hmid (by positivity)
                _ = max C₀ Csmall * (N:ℝ)^(1+ε) * B^(((2:ℝ)^(k-1))⁻¹) := by ring


end Commons.Analysis.ExponentialSums