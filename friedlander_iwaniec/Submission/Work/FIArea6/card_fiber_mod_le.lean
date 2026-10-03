import Mathlib
import Submission.Work.FIArea4.polarBox_card_le

namespace Work.FIArea6

noncomputable section

/-! ## Counting integers in an interval with a congruence condition -/

/-- **Integers in an interval of length `2ρ` that are all congruent modulo `d` number at most
`2ρ/d + 1`.**  The map `x ↦ (x - a)/d` is injective on such a set and sends it into an interval of
length `2ρ/d`. -/
lemma card_le_of_modEq_interval (S : Finset ℤ) {d : ℕ} (hd : 0 < d) (a : ℤ) {t ρ : ℝ}
    (hρ : 0 ≤ ρ)
    (hmod : ∀ x ∈ S, x ≡ a [ZMOD (d : ℤ)])
    (hint : ∀ x ∈ S, t ≤ (x : ℝ) ∧ (x : ℝ) ≤ t + 2 * ρ) :
    (S.card : ℝ) ≤ 2 * ρ / (d : ℝ) + 1 := by
  have hdR : (0 : ℝ) < (d : ℝ) := by exact_mod_cast hd
  have hinj : Set.InjOn (fun x : ℤ => (x - a) / (d : ℤ)) (S : Set ℤ) := by
    intro x hx y hy hxy
    have hx' : (d : ℤ) ∣ x - a := (hmod x hx).symm.dvd
    have hy' : (d : ℤ) ∣ y - a := (hmod y hy).symm.dvd
    have h1 : (x - a) / (d : ℤ) * (d : ℤ) = x - a := Int.ediv_mul_cancel hx'
    have h2 : (y - a) / (d : ℤ) * (d : ℤ) = y - a := Int.ediv_mul_cancel hy'
    have hxy' : (x - a) / (d : ℤ) = (y - a) / (d : ℤ) := hxy
    rw [hxy'] at h1
    linarith
  have hcard : (S.image (fun x : ℤ => (x - a) / (d : ℤ))).card = S.card :=
    Finset.card_image_of_injOn hinj
  have hb : ((S.image (fun x : ℤ => (x - a) / (d : ℤ))).card : ℝ) ≤ 2 * (ρ / (d : ℝ)) + 1 := by
    apply Work.FIArea4.card_int_le_of_mem_interval (S.image (fun x : ℤ => (x - a) / (d : ℤ)))
      (t := (t - (a : ℝ)) / (d : ℝ)) (ρ := ρ / (d : ℝ)) (div_nonneg hρ hdR.le)
    intro y hy
    obtain ⟨x, hx, hxy⟩ := Finset.mem_image.mp hy
    change (x - a) / (d : ℤ) = y at hxy
    have hx' : (d : ℤ) ∣ x - a := (hmod x hx).symm.dvd
    have hxeq : x - a = ((x - a) / (d : ℤ)) * (d : ℤ) := (Int.ediv_mul_cancel hx').symm
    have hxeqR : ((x : ℤ) : ℝ) = (a : ℝ) + (((x - a) / (d : ℤ) : ℤ) : ℝ) * (d : ℝ) := by
      have h : (x : ℤ) = a + ((x - a) / (d : ℤ)) * (d : ℤ) := by linarith
      exact_mod_cast h
    obtain ⟨h1, h2⟩ := hint x hx
    rw [← hxy]
    constructor
    · rw [hxeqR] at h1
      exact (div_le_iff₀ hdR).mpr (by linarith)
    · rw [hxeqR] at h2
      have h3 : (((x - a) / (d : ℤ) : ℤ) : ℝ) ≤ ((t - (a : ℝ)) + 2 * ρ) / (d : ℝ) :=
        (le_div_iff₀ hdR).mpr (by linarith)
      have h4 : ((t - (a : ℝ)) + 2 * ρ) / (d : ℝ)
          = (t - (a : ℝ)) / (d : ℝ) + 2 * (ρ / (d : ℝ)) := by
        rw [add_div, mul_div_assoc]
      linarith [h3, h4.le, h4.ge]
  have hconv : 2 * (ρ / (d : ℝ)) + 1 = 2 * ρ / (d : ℝ) + 1 := by ring
  rw [hconv] at hb
  simpa [hcard] using hb

/-! ## The fibre count -/

/-- **A disc of radius `ρ` contains at most `(2ρ/d + 1)²` Gaussian integers whose real and
imaginary parts are prescribed modulo `d`.**  The real parts lie in an interval of length `2ρ` and
are distinct, and so do the imaginary parts; each of those sets has `≤ 2ρ/d + 1` elements by
`card_le_of_modEq_interval`, and `z ↦ (z.re, z.im)` is injective. -/
theorem card_fiber_mod_le (S : Finset GaussianInt) (c : ℂ) (d : ℕ) (hd : 0 < d)
    (a b : ℤ) (ρ : ℝ) (hρ : 0 ≤ ρ)
    (hdist : ∀ z ∈ S, ‖z.toComplex - c‖ ≤ ρ)
    (hre : ∀ z ∈ S, z.re ≡ a [ZMOD (d : ℤ)])
    (him : ∀ z ∈ S, z.im ≡ b [ZMOD (d : ℤ)]) :
    (S.card : ℝ) ≤ (2 * ρ / (d : ℝ) + 1) ^ 2 := by
  set R : Finset ℤ := S.image (fun z => z.re) with hR
  set I : Finset ℤ := S.image (fun z => z.im) with hI
  have hdR : (0 : ℝ) < (d : ℝ) := by exact_mod_cast hd
  have hcard1 : S.card ≤ R.card * I.card := by
    have hinj : Function.Injective (fun z : GaussianInt => (z.re, z.im)) := by
      intro p q hpq
      exact Zsqrtd.ext (congrArg Prod.fst hpq) (congrArg Prod.snd hpq)
    calc S.card = (S.image (fun z : GaussianInt => (z.re, z.im))).card :=
          (Finset.card_image_of_injective S hinj).symm
      _ ≤ (R ×ˢ I).card := by
          apply Finset.card_le_card
          intro p hp
          obtain ⟨z, hz, hpz⟩ := Finset.mem_image.mp hp
          rw [← hpz]
          exact Finset.mem_product.mpr
            ⟨Finset.mem_image.mpr ⟨z, hz, rfl⟩, Finset.mem_image.mpr ⟨z, hz, rfl⟩⟩
      _ = R.card * I.card := Finset.card_product R I
  have hRcard : (R.card : ℝ) ≤ 2 * ρ / (d : ℝ) + 1 := by
    apply card_le_of_modEq_interval (t := c.re - ρ) R hd a hρ
    · intro x hx
      rw [hR] at hx
      obtain ⟨z, hz, rfl⟩ := Finset.mem_image.mp hx
      exact hre z hz
    · intro x hx
      rw [hR] at hx
      obtain ⟨z, hz, rfl⟩ := Finset.mem_image.mp hx
      have h1 := hdist z hz
      have h2 : |((z.re : ℤ) : ℝ) - c.re| ≤ ρ := by
        calc |((z.re : ℤ) : ℝ) - c.re| = |(z.toComplex - c).re| := by
              rw [Work.FIArea4.ofReal_re_eq_re z, Complex.sub_re]
          _ ≤ ‖z.toComplex - c‖ := Complex.abs_re_le_norm _
          _ ≤ ρ := h1
      rw [abs_le] at h2
      constructor <;> linarith [h2.1, h2.2]
  have hIcard : (I.card : ℝ) ≤ 2 * ρ / (d : ℝ) + 1 := by
    apply card_le_of_modEq_interval (t := c.im - ρ) I hd b hρ
    · intro x hx
      rw [hI] at hx
      obtain ⟨z, hz, rfl⟩ := Finset.mem_image.mp hx
      exact him z hz
    · intro x hx
      rw [hI] at hx
      obtain ⟨z, hz, rfl⟩ := Finset.mem_image.mp hx
      have h1 := hdist z hz
      have h2 : |((z.im : ℤ) : ℝ) - c.im| ≤ ρ := by
        calc |((z.im : ℤ) : ℝ) - c.im| = |(z.toComplex - c).im| := by
              rw [Work.FIArea4.ofReal_im_eq_im z, Complex.sub_im]
          _ ≤ ‖z.toComplex - c‖ := Complex.abs_im_le_norm _
          _ ≤ ρ := h1
      rw [abs_le] at h2
      constructor <;> linarith [h2.1, h2.2]
  have h0 : 0 ≤ 2 * ρ / (d : ℝ) + 1 := by
    have : 0 ≤ 2 * ρ / (d : ℝ) := div_nonneg (by linarith) hdR.le
    linarith
  calc (S.card : ℝ) ≤ (R.card : ℝ) * (I.card : ℝ) := by exact_mod_cast hcard1
    _ ≤ (2 * ρ / (d : ℝ) + 1) * (2 * ρ / (d : ℝ) + 1) :=
        mul_le_mul hRcard hIcard (by exact_mod_cast Nat.zero_le _) h0
    _ = (2 * ρ / (d : ℝ) + 1) ^ 2 := by ring

end

end Work.FIArea6
