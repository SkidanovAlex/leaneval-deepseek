import Mathlib
import Submission.Work.FIArea4.WdyadDefs2
import Submission.Work.FIArea4.SqfreeKernel
import Submission.Work.FIArea4.sqfree_kernel
import Submission.Work.FIArea4.sqfreeKernel_eq_of_mul_sq
import Submission.Work.FIArea4.card_sqfreeKernel_eq_le_sqrt

namespace Work.FIArea4.Vflip

lemma oddPart_mul_two_pow' (d : ℕ) :
    2 ^ (d.factorization 2) * Work.FIPlan.oddPart d = d := by
  unfold Work.FIPlan.oddPart
  exact Nat.ordProj_mul_ordCompl_eq_self d 2

lemma oddPart_pos' {d : ℕ} (hd : d ≠ 0) : 0 < Work.FIPlan.oddPart d := by
  unfold Work.FIPlan.oddPart
  exact Nat.ordCompl_pos 2 hd

lemma oddPart_le' (d : ℕ) : Work.FIPlan.oddPart d ≤ d := by
  unfold Work.FIPlan.oddPart
  exact Nat.ordCompl_le d 2

/-- `oddPart` is injective on a dyadic interval `(D, 2D]`: two dyadic multiples of the same odd
number cannot both lie in `(D, 2D]`, since one would then be at least twice the other. -/
lemma oddPart_injOn_Ioc (D : ℕ) :
    Set.InjOn Work.FIPlan.oddPart (↑(Finset.Ioc D (2 * D)) : Set ℕ) := by
  intro x hx y hy hxy
  rw [Finset.mem_coe, Finset.mem_Ioc] at hx hy
  obtain ⟨hxlo, hxhi⟩ := hx
  obtain ⟨hylo, hyhi⟩ := hy
  have hmx : 2 ^ (x.factorization 2) * Work.FIPlan.oddPart x = x := oddPart_mul_two_pow' x
  have hmy : 2 ^ (y.factorization 2) * Work.FIPlan.oddPart y = y := oddPart_mul_two_pow' y
  by_contra hne
  rcases le_total (x.factorization 2) (y.factorization 2) with hk | hk
  · obtain ⟨c, hc⟩ := pow_dvd_pow (2 : ℕ) hk
    have hdvd : x ∣ y := by
      refine ⟨c, ?_⟩
      calc y = 2 ^ (y.factorization 2) * Work.FIPlan.oddPart y := hmy.symm
        _ = (2 ^ (x.factorization 2) * c) * Work.FIPlan.oddPart y := by rw [hc]
        _ = (2 ^ (x.factorization 2) * c) * Work.FIPlan.oddPart x := by rw [← hxy]
        _ = (2 ^ (x.factorization 2) * Work.FIPlan.oddPart x) * c := by ring
        _ = x * c := by rw [hmx]
    obtain ⟨q, hq⟩ := hdvd
    have hq2 : 2 ≤ q := by
      have hq1 : 1 ≤ q := by
        rcases Nat.eq_zero_or_pos q with h | h
        · rw [h, mul_zero] at hq; omega
        · exact h
      rcases lt_or_eq_of_le hq1 with h | h
      · omega
      · exact absurd (by rw [← h, mul_one] at hq; exact hq.symm) hne
    have hle : 2 * x ≤ y := by
      calc 2 * x ≤ q * x := Nat.mul_le_mul_right x hq2
        _ = x * q := by ring
        _ = y := hq.symm
    omega
  · obtain ⟨c, hc⟩ := pow_dvd_pow (2 : ℕ) hk
    have hdvd : y ∣ x := by
      refine ⟨c, ?_⟩
      calc x = 2 ^ (x.factorization 2) * Work.FIPlan.oddPart x := hmx.symm
        _ = (2 ^ (y.factorization 2) * c) * Work.FIPlan.oddPart x := by rw [hc]
        _ = (2 ^ (y.factorization 2) * c) * Work.FIPlan.oddPart y := by rw [hxy]
        _ = (2 ^ (y.factorization 2) * Work.FIPlan.oddPart y) * c := by ring
        _ = y * c := by rw [hmy]
    obtain ⟨q, hq⟩ := hdvd
    have hq2 : 2 ≤ q := by
      have hq1 : 1 ≤ q := by
        rcases Nat.eq_zero_or_pos q with h | h
        · rw [h, mul_zero] at hq; omega
        · exact h
      rcases lt_or_eq_of_le hq1 with h | h
      · omega
      · exact absurd (by rw [← h, mul_one] at hq; exact hq) hne
    have hle : 2 * y ≤ x := by
      calc 2 * y ≤ q * y := Nat.mul_le_mul_right y hq2
        _ = y * q := by ring
        _ = x := hq.symm
    omega

theorem card_sq_filter_le (D d1 : ℕ) (hD : 1 ≤ D) (hd1 : 1 ≤ d1) :
    (((Finset.Ioc D (2*D)).filter (fun d2 => Nat.sqrt (Work.FIPlan.oddPart d1 * Work.FIPlan.oddPart d2)^2
        = Work.FIPlan.oddPart d1 * Work.FIPlan.oddPart d2)).card : ℝ) ≤ Real.sqrt (2*D) := by
  set a : ℕ := Work.FIPlan.oddPart d1 with ha
  have ha1 : 1 ≤ a := by
    rw [ha]
    have h := oddPart_pos' (by omega : d1 ≠ 0)
    omega
  set d : ℕ := Work.FIArea4.sqfreeKernel a with hd
  have hdle : 1 ≤ d := by
    rw [hd]
    obtain ⟨hP, hmax, hsq, hdvd, hsf⟩ := Work.FIArea4.sqfree_kernel a (by omega : a ≠ 0)
    have : 0 < Work.FIArea4.sqfreeKernel a := by
      by_contra hc
      have hz : Work.FIArea4.sqfreeKernel a = 0 := by omega
      rw [hz] at hsq
      simp at hsq
      omega
    omega
  set S : Finset ℕ := (Finset.Ioc D (2*D)).filter
    (fun d2 => Nat.sqrt (a * Work.FIPlan.oddPart d2)^2 = a * Work.FIPlan.oddPart d2) with hS
  set T : Finset ℕ := (Finset.Icc 1 (2*D)).filter
    (fun m => Work.FIArea4.sqfreeKernel m = d) with hT
  -- `oddPart` maps `S` into the set of `m ≤ 2D` with squarefree kernel `d`
  have hmap : Set.MapsTo Work.FIPlan.oddPart ↑S ↑T := by
    intro d2 hd2
    simp only [Finset.mem_coe, hS, Finset.mem_filter, Finset.mem_Ioc] at hd2
    obtain ⟨⟨hd2lo, hd2hi⟩, hsq2⟩ := hd2
    have hodd1 : 1 ≤ Work.FIPlan.oddPart d2 := by
      have h := oddPart_pos' (by omega : d2 ≠ 0)
      omega
    have hodd2 : Work.FIPlan.oddPart d2 ≤ 2*D := le_trans (oddPart_le' d2) hd2hi
    simp only [Finset.mem_coe, hT, Finset.mem_filter, Finset.mem_Icc]
    refine ⟨⟨hodd1, hodd2⟩, ?_⟩
    rw [hd]
    exact (Work.FIArea4.sqfreeKernel_eq_of_mul_sq a (Work.FIPlan.oddPart d2) ha1 hodd1
      ⟨Nat.sqrt (a * Work.FIPlan.oddPart d2), hsq2.symm⟩).symm
  have hsub : (↑S : Set ℕ) ⊆ (↑(Finset.Ioc D (2*D)) : Set ℕ) := by
    intro z hz
    simp only [Finset.mem_coe, hS, Finset.mem_filter] at hz
    exact hz.1
  have hinj : Set.InjOn Work.FIPlan.oddPart ↑S :=
    fun x hx y hy hxy => oddPart_injOn_Ioc D (hsub hx) (hsub hy) hxy
  have hcard : S.card ≤ T.card := Finset.card_le_card_of_injOn _ hmap hinj
  -- the target set has at most `√(2D/d) ≤ √(2D)` elements
  have hTbound : (T.card : ℝ) ≤ Real.sqrt (((2*D : ℕ) : ℝ)) := by
    have h1 := Work.FIArea4.card_sqfreeKernel_eq_le_sqrt (2*D) d hdle
    have h1' : (T.card : ℝ) ≤ Real.sqrt (((2*D : ℕ) : ℝ) / (d : ℝ)) := by
      simpa only [hT] using h1
    have h2 : ((2*D : ℕ) : ℝ) / (d : ℝ) ≤ ((2*D : ℕ) : ℝ) := by
      have hdpos : (0 : ℝ) < (d : ℝ) := by exact_mod_cast (by omega : 0 < d)
      have hdge : (1 : ℝ) ≤ (d : ℝ) := by exact_mod_cast hdle
      rw [div_le_iff₀ hdpos]
      calc ((2*D : ℕ) : ℝ) = ((2*D : ℕ) : ℝ) * 1 := by ring
        _ ≤ ((2*D : ℕ) : ℝ) * (d : ℝ) :=
            mul_le_mul_of_nonneg_left hdge (by positivity)
    exact le_trans h1' (Real.sqrt_le_sqrt h2)
  have hcardR : (S.card : ℝ) ≤ (T.card : ℝ) := by exact_mod_cast hcard
  have htwoD : (((2*D : ℕ) : ℝ)) = 2*D := by push_cast; ring
  calc (S.card : ℝ) ≤ (T.card : ℝ) := hcardR
    _ ≤ Real.sqrt (((2*D : ℕ) : ℝ)) := hTbound
    _ = Real.sqrt (2*D) := by rw [htwoD]

end Work.FIArea4.Vflip
