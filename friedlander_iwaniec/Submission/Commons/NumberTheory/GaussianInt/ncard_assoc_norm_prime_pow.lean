import Mathlib
import Submission.Commons.NumberTheory.GaussianInt.irreducible_norm_eq_prime_or_sq
import Submission.Commons.NumberTheory.GaussianInt.ncard_assoc_irred_norm_prime
import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Analysis.Normed.Ring.Lemmas
import Mathlib.Data.Int.Star
import Mathlib.NumberTheory.Zsqrtd.QuadraticReciprocity
import Submission.Commons.NumberTheory.GaussianInt.ncard_units
import Submission.Commons.NumberTheory.GaussianInt.two_squares_repr_count_prime_pow

namespace Commons.NumberTheory.GaussianInt

open Zsqrtd

local notation "ℤ[i]" => GaussianInt

private lemma mk_eq_one_of_isUnit {u : ℤ[i]} (hu : IsUnit u) : Associates.mk u = 1 := by
  rw [show (1 : Associates ℤ[i]) = Associates.mk 1 from rfl]
  exact Associates.mk_eq_mk_iff_associated.mpr (associated_one_iff_isUnit.mpr hu)

/-- The finite set of Gaussian integers of norm `n` (`n ≥ 1`), as the image of the
representation box `repBox n` under `(a, b) ↦ a + b i`. -/
private noncomputable def normBox (n : ℕ) : Finset ℤ[i] :=
  (repBox n).image (fun w : ℤ × ℤ => (⟨w.1, w.2⟩ : ℤ[i]))

private lemma mem_normBox {n : ℕ} (hn : 1 ≤ n) (z : ℤ[i]) :
    z ∈ normBox n ↔ z.norm.natAbs = n := by
  rw [normBox, Finset.mem_image]
  constructor
  · rintro ⟨w, hw, rfl⟩
    exact (norm_natAbs_eq_iff _ n).mpr ((mem_repBox hn).mp hw)
  · intro hz
    exact ⟨(z.re, z.im), (mem_repBox hn).mpr ((norm_natAbs_eq_iff z n).mp hz),
      Zsqrtd.ext_iff.mpr ⟨rfl, rfl⟩⟩

private lemma ncard_norm_eq_card_normBox (n : ℕ) (hn : 1 ≤ n) :
    ({z : ℤ[i] | z.norm.natAbs = n} : Set ℤ[i]).ncard = (normBox n).card := by
  rw [← Set.ncard_coe_finset]
  congr 1
  ext z
  rw [Finset.mem_coe, Set.mem_ofPred_eq]
  exact (mem_normBox hn z).symm

private lemma card_normBox_eq_card_repBox (n : ℕ) : (normBox n).card = (repBox n).card := by
  rw [normBox, Finset.card_image_of_injective]
  intro a b h
  rw [Zsqrtd.ext_iff] at h
  exact Prod.ext h.1 h.2

/-- The fibre of `Associates.mk` over the class of `z0`, among the Gaussian integers of
norm `n`, has exactly `4` elements: the four unit multiples of `z0`. -/
private lemma ncard_norm_fiber (n : ℕ) (hn : 1 ≤ n) {z0 : ℤ[i]} (hz0n : z0.norm.natAbs = n) :
    ({a : ℤ[i] | a.norm.natAbs = n ∧ Associates.mk a = Associates.mk z0}).ncard = 4 := by
  have hz0ne : z0 ≠ 0 := by
    intro h; rw [h] at hz0n; simp at hz0n; omega
  have hbij : ({u : ℤ[i] | IsUnit u}).ncard
      = ({a : ℤ[i] | a.norm.natAbs = n ∧ Associates.mk a = Associates.mk z0}).ncard := by
    refine Set.ncard_congr (fun u _ => z0 * u) ?_ ?_ ?_
    · intro u hu
      rw [Set.mem_ofPred_eq]
      refine ⟨?_, ?_⟩
      · rw [Zsqrtd.norm_mul, Int.natAbs_mul, hz0n, Zsqrtd.norm_eq_one_iff.mpr hu, mul_one]
      · rw [← Associates.mk_mul_mk, mk_eq_one_of_isUnit hu, mul_one]
    · intro u _ v _ huv
      exact mul_left_cancel₀ hz0ne huv
    · intro a ha
      rw [Set.mem_ofPred_eq] at ha
      obtain ⟨-, hmk⟩ := ha
      rw [Associates.mk_eq_mk_iff_associated] at hmk
      obtain ⟨u, hu⟩ := hmk
      exact ⟨(↑u⁻¹ : ℤ[i]), u⁻¹.isUnit, by rw [← hu, mul_assoc, Units.mul_inv, mul_one]⟩
  rw [← hbij, ncard_units]

/-- The number of Gaussian integers of norm `n` is four times the number of their
associate classes, since every class contains exactly the four unit multiples. -/
private lemma card_normBox_eq_four_mul_ncard (n : ℕ) (hn : 1 ≤ n) :
    (normBox n).card = 4 * (Associates.mk '' {z : ℤ[i] | z.norm.natAbs = n}).ncard := by
  classical
  have hcoe : ((normBox n : Finset ℤ[i]) : Set ℤ[i]) = {z : ℤ[i] | z.norm.natAbs = n} := by
    ext z
    rw [Finset.mem_coe, Set.mem_ofPred_eq]
    exact mem_normBox hn z
  have hmaps : Set.MapsTo Associates.mk ((normBox n : Finset ℤ[i]) : Set ℤ[i])
      (((normBox n).image Associates.mk : Finset (Associates ℤ[i])) : Set (Associates ℤ[i])) :=
    fun a ha => Finset.mem_coe.mpr (Finset.mem_image.mpr ⟨a, Finset.mem_coe.mp ha, rfl⟩)
  have hcard := Finset.card_eq_sum_card_fiberwise hmaps
  have hfiber : ∀ b ∈ (normBox n).image Associates.mk,
      ((normBox n).filter (fun a => Associates.mk a = b)).card = 4 := by
    intro b hb
    rw [Finset.mem_image] at hb
    obtain ⟨z0, hz0, rfl⟩ := hb
    rw [← Set.ncard_coe_finset]
    have hset : ((normBox n).filter (fun a => Associates.mk a = Associates.mk z0) : Set ℤ[i])
        = {a : ℤ[i] | a.norm.natAbs = n ∧ Associates.mk a = Associates.mk z0} := by
      ext a
      rw [Finset.mem_coe, Finset.mem_filter]
      constructor
      · rintro ⟨h1, h2⟩; exact ⟨(mem_normBox hn a).mp h1, h2⟩
      · rintro ⟨h1, h2⟩; exact ⟨(mem_normBox hn a).mpr h1, h2⟩
    rw [hset]
    exact ncard_norm_fiber n hn ((mem_normBox hn z0).mp hz0)
  calc (normBox n).card
      = ∑ b ∈ (normBox n).image Associates.mk,
          ((normBox n).filter (fun a => Associates.mk a = b)).card := hcard
    _ = ∑ _b ∈ (normBox n).image Associates.mk, 4 := Finset.sum_congr rfl hfiber
    _ = 4 * ((normBox n).image Associates.mk).card := by
          rw [Finset.sum_const, smul_eq_mul, mul_comm]
    _ = 4 * (Associates.mk '' {z : ℤ[i] | z.norm.natAbs = n}).ncard := by
          rw [← Set.ncard_coe_finset, Finset.coe_image, hcoe]

/-- The number of Gaussian integers of norm `p ^ k` (`k ≥ 1`), read off from the number of
representations of `p ^ k` as a sum of two squares. -/
private lemma normBox_card_prime_pow (p k : ℕ) (hp : p.Prime) (hk : 1 ≤ k) :
    (normBox (p ^ k)).card
      = (if p = 2 then 4 else if p % 4 = 1 then 4 * (k + 1) else if Even k then 4 else 0) := by
  rw [card_normBox_eq_card_repBox]
  have hZ : ((repBox (p ^ k)).card : ℤ)
      = ((if p = 2 then 4 else if p % 4 = 1 then 4 * (k + 1) else if Even k then 4 else 0 : ℕ) : ℤ) := by
    have h := two_squares_repr_count_prime_pow p hp k hk
    change (((Finset.filter (fun z : ℤ × ℤ => z.1 ^ 2 + z.2 ^ 2 = ((p ^ k : ℕ) : ℤ))
        (Finset.Icc (-(((p ^ k : ℕ) : ℤ))) (((p ^ k : ℕ) : ℤ))
          ×ˢ Finset.Icc (-(((p ^ k : ℕ) : ℤ))) (((p ^ k : ℕ) : ℤ)))).card : ℤ))
      = ((if p = 2 then 4 else if p % 4 = 1 then 4 * (k + 1) else if Even k then 4 else 0 : ℕ) : ℤ)
    rw [h]
  exact Int.ofNat_inj.mp hZ

/-- Arithmetic closing step: `4 * M = R` determines `M`, where `R` is the number of
representations of `p ^ k`. -/
private lemma four_mul_eq_iff (p k M : ℕ) :
    4 * M = (if p = 2 then 4 else if p % 4 = 1 then 4 * (k + 1) else if Even k then 4 else 0) ↔
      M = (if p = 2 then 1 else if p % 4 = 1 then k + 1 else if Even k then 1 else 0) := by
  by_cases h2 : p = 2
  · simp only [if_pos h2]; constructor <;> intro h <;> omega
  · simp only [if_neg h2]
    by_cases h1 : p % 4 = 1
    · simp only [if_pos h1]; constructor <;> intro h <;> omega
    · simp only [if_neg h1]
      by_cases hev : Even k
      · simp only [if_pos hev]; constructor <;> intro h <;> omega
      · simp only [if_neg hev]; constructor <;> intro h <;> omega

theorem ncard_assoc_norm_prime_pow (p k : ℕ) (hp : p.Prime) :
    (Associates.mk '' {z : GaussianInt | z.norm.natAbs = p ^ k}).ncard
      = (if p = 2 then 1 else if p % 4 = 1 then k + 1 else if Even k then 1 else 0) := by
  rcases Nat.eq_zero_or_pos k with hk | hk
  · subst hk
    have hset : {z : GaussianInt | z.norm.natAbs = p ^ 0}
        = {z : GaussianInt | IsUnit z} := by
      ext z
      rw [Set.mem_ofPred_eq, Set.mem_ofPred_eq, pow_zero, Zsqrtd.norm_eq_one_iff]
    rw [hset]
    have himg : Associates.mk '' {z : GaussianInt | IsUnit z}
        = ({1} : Set (Associates GaussianInt)) := by
      ext κ
      constructor
      · rintro ⟨z, hz, rfl⟩
        rw [Set.mem_singleton_iff]
        exact mk_eq_one_of_isUnit hz
      · intro h
        rw [Set.mem_singleton_iff] at h
        exact ⟨1, isUnit_one, h.symm⟩
    rw [himg, Set.ncard_singleton]
    by_cases h2 : p = 2
    · rw [if_pos h2]
    · rw [if_neg h2]
      by_cases h1 : p % 4 = 1
      · rw [if_pos h1]
      · rw [if_neg h1, if_pos (show Even 0 from ⟨0, rfl⟩)]
  · have h4 := card_normBox_eq_four_mul_ncard (p ^ k) (Nat.one_le_pow k p hp.pos)
    have hN := normBox_card_prime_pow p k hp hk
    exact (four_mul_eq_iff p k _).mp (by rw [← h4, hN])

end Commons.NumberTheory.GaussianInt
