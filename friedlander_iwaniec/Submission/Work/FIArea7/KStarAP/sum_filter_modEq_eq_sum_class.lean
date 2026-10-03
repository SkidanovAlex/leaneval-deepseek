import Mathlib

namespace Work.FIArea7.KStarAP

/-- For `κ > 0`, the integer `w` satisfies `-((z)/κ) ≤ w` iff `w * κ ≥ -z`. -/
private lemma neg_ediv_le_iff (κ z w : ℤ) (hκ : 0 < κ) : -((z)/κ) ≤ w ↔ w * κ ≥ -z := by
  rw [neg_le, Int.le_ediv_iff_mul_le hκ]
  constructor <;> intro h <;> linarith

/-- Reduction of a sum over the integers `s ∈ [S,T]` with `s ≡ d (mod B)` to a sum over the
quotient index `k = (s - d)/B`. -/
private lemma sum_filter_eq (B d S T : ℤ) (hB : 0 < B) (f : ℤ → ℂ) :
    ∑ s ∈ (Finset.Icc S T).filter (fun s => s ≡ d [ZMOD B]), f s
      = ∑ k ∈ Finset.Icc (-((d - S) / B)) (((T - d) / B)), f (d + B * k) := by
  have hBne : B ≠ 0 := ne_of_gt hB
  have hdvd_of : ∀ a : ℤ, a ≡ d [ZMOD B] → B ∣ a - d := by
    intro a ha
    have h1 : B ∣ d - a := Int.modEq_iff_dvd.mp ha
    have h2 : B ∣ -(d - a) := dvd_neg.mpr h1
    rwa [neg_sub] at h2
  refine Finset.sum_bij' (fun a _ => (a - d) / B) (fun a _ => d + B * a) ?_ ?_ ?_ ?_ ?_
  · intro a ha
    rw [Finset.mem_filter, Finset.mem_Icc] at ha
    obtain ⟨⟨hSa, haT⟩, hmod⟩ := ha
    rw [Finset.mem_Icc]
    have hdvd : B ∣ a - d := hdvd_of a hmod
    have hemp : (a - d) / B * B = a - d := Int.ediv_mul_cancel hdvd
    constructor
    · rw [neg_ediv_le_iff B (d - S) _ hB, hemp]
      linarith
    · exact Int.ediv_le_ediv hB (by linarith)
  · intro a ha
    rw [Finset.mem_Icc] at ha
    obtain ⟨hLa, haU⟩ := ha
    rw [Finset.mem_filter, Finset.mem_Icc]
    refine ⟨⟨?_, ?_⟩, ?_⟩
    · have h1 : S - d ≤ a * B := by
        have h := (neg_ediv_le_iff B (d - S) a hB).mp hLa
        rwa [neg_sub] at h
      have h2 : (a:ℤ) * B = B * a := mul_comm a B
      linarith
    · have h2 : B * a ≤ B * ((T - d) / B) := mul_le_mul_of_nonneg_left haU hB.le
      have h3 : B * ((T - d) / B) ≤ T - d := by
        rw [mul_comm B ((T - d) / B)]
        exact Int.ediv_mul_le (T - d) hBne
      linarith
    · rw [Int.modEq_iff_dvd]
      exact ⟨-a, by ring⟩
  · intro a ha
    rw [Finset.mem_filter] at ha
    obtain ⟨_, hmod⟩ := ha
    have hdvd : B ∣ a - d := hdvd_of a hmod
    have hemp : B * ((a - d) / B) = a - d := by
      rw [mul_comm]; exact Int.ediv_mul_cancel hdvd
    linarith
  · intro a ha
    exact Int.ediv_eq_of_eq_mul_right (b := B) hBne (by ring)
  · intro a ha
    rw [Finset.mem_filter] at ha
    obtain ⟨_, hmod⟩ := ha
    have hdvd : B ∣ a - d := hdvd_of a hmod
    have hemp : B * ((a - d) / B) = a - d := by
      rw [mul_comm]; exact Int.ediv_mul_cancel hdvd
    congr 1
    linarith

/-- Splitting a sum over an interval `[L,U]` according to the residue `e` of the index modulo
`κ` (`κ > 0`) and the quotient `w = k / κ`. -/
private lemma sum_Icc_eq_sum_class (L U κ : ℤ) (hκ : 0 < κ) (g : ℤ → ℂ) :
    ∑ k ∈ Finset.Icc L U, g k
      = ∑ e ∈ Finset.Ico (0:ℤ) κ,
          ∑ w ∈ Finset.Icc (-((e - L)/κ)) (((U - e)/κ)), g (e + κ * w) := by
  rw [Finset.sum_sigma' (Finset.Ico (0:ℤ) κ)
        (fun e => Finset.Icc (-((e - L)/κ)) (((U - e)/κ))) (fun e w => g (e + κ * w))]
  refine Finset.sum_bij' (fun k _ => ⟨k % κ, k / κ⟩) (fun x _ => x.fst + κ * x.snd) ?_ ?_ ?_ ?_ ?_
  · intro k hk
    rw [Finset.mem_Icc] at hk
    obtain ⟨hkL, hkU⟩ := hk
    have hde := (Int.ediv_emod_unique hκ).mp (show k / κ = k / κ ∧ k % κ = k % κ from ⟨rfl, rfl⟩)
    have hem : k % κ + κ * (k / κ) = k := hde.1
    have h0 : 0 ≤ k % κ := hde.2.1
    have hlt : k % κ < κ := hde.2.2
    have hem' : κ * (k / κ) = k - k % κ := by linarith
    rw [Finset.mem_sigma]
    refine ⟨Finset.mem_Ico.mpr ⟨h0, hlt⟩, Finset.mem_Icc.mpr ⟨?_, ?_⟩⟩
    · rw [neg_ediv_le_iff κ (k % κ - L) (k / κ) hκ, mul_comm (k / κ) κ, hem']
      linarith
    · have h2 : κ * (k / κ) ≤ U - k % κ := by linarith
      have hdiv : (κ * (k / κ)) / κ = k / κ := by
        rw [mul_comm κ (k / κ)]
        exact Int.mul_ediv_cancel (k / κ) (ne_of_gt hκ)
      calc k / κ = (κ * (k / κ)) / κ := hdiv.symm
           _ ≤ (U - k % κ) / κ := Int.ediv_le_ediv hκ h2
  · rintro ⟨e, w⟩ hx
    rw [Finset.mem_sigma, Finset.mem_Ico, Finset.mem_Icc] at hx
    obtain ⟨⟨he0, helt⟩, hwlo, hwhi⟩ := hx
    rw [Finset.mem_Icc]
    constructor
    · have h1 : w * κ ≥ -(e - L) := (neg_ediv_le_iff κ (e - L) w hκ).mp hwlo
      have h1' : (w:ℤ) * κ = κ * w := mul_comm w κ
      linarith
    · have h1 : w * κ ≤ U - e := (Int.le_ediv_iff_mul_le hκ).mp hwhi
      have h1' : (w:ℤ) * κ = κ * w := mul_comm w κ
      linarith
  · intro k hk
    have hem : k % κ + κ * (k / κ) = k :=
      ((Int.ediv_emod_unique hκ).mp (show k / κ = k / κ ∧ k % κ = k % κ from ⟨rfl, rfl⟩)).1
    exact hem
  · rintro ⟨e, w⟩ hx
    rw [Finset.mem_sigma, Finset.mem_Ico] at hx
    obtain ⟨⟨he0, helt⟩, _⟩ := hx
    have h := (Int.ediv_emod_unique hκ).mpr
      (show e + κ * w = e + κ * w ∧ 0 ≤ e ∧ e < κ from ⟨rfl, he0, helt⟩)
    obtain ⟨hdiv, hmod⟩ := h
    rw [hmod, hdiv]
  · intro k hk
    have hem : k % κ + κ * (k / κ) = k :=
      ((Int.ediv_emod_unique hκ).mp (show k / κ = k / κ ∧ k % κ = k % κ from ⟨rfl, rfl⟩)).1
    congr 1
    exact hem.symm

lemma sum_filter_modEq_eq_sum_class (B A κ : ℤ) (hB : 0 < B) (hκ : 0 < κ) (hA : A = B * κ)
    (d S T : ℤ) (f : ℤ → ℂ) :
    ∑ s ∈ (Finset.Icc S T).filter (fun s => s ≡ d [ZMOD B]), f s
      = ∑ e ∈ Finset.Ico (0:ℤ) κ,
          ∑ w ∈ Finset.Icc (-((e + ((d - S) / B)) / κ)) (((((T - d) / B) - e) / κ)),
            f (d + B * e + A * w) := by
  subst hA
  rw [sum_filter_eq B d S T hB f]
  rw [sum_Icc_eq_sum_class (-((d - S) / B)) (((T - d) / B)) κ hκ (fun k => f (d + B * k))]
  simp only [sub_neg_eq_add]
  refine Finset.sum_congr rfl (fun e _ => Finset.sum_congr rfl (fun w _ => ?_))
  congr 1
  ring

end Work.FIArea7.KStarAP
