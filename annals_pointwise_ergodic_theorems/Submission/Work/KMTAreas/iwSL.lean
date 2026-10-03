/-
# The Tao denominator set `S_l` of the area A1 bridge, and its arithmetic

For the bridge from the workspace's Ionescu–Wainger frequency sets `iwArithFreqs ρ l` to Tao's
major-arc formulation (Tao, arXiv:2008.05066) one uses the **Tao denominator set**

  `S_l = {Q_0^{(l)}} ∪ {p^{D_ρ} : p ∈ (N_0^{(l)}, 2^l] prime}`,

which is the set denoted `S` in Appendix A of Krause–Mirek–Tao.  This file collects the
elementary arithmetic of `S_l`:

* `iwSLmax ρ l = max Q_0^{(l)} (2^{l D_ρ})` is an upper bound for the elements of `S_l`,
  *sharper* than the generic bound `2^{C 2^{ρl}}` of `Work.KMTAreas.iwS_element_le`: it is the
  bound that the numeric core of the IW multiplier theorem consumes (the deep route applies
  for all large `l` precisely because `log₂ (iwSLmax ρ l)` grows like `2^{ρl/2} ρ l`, not like
  `2^{ρl}`);
* `iwSL_two_le` — every element of `S_l` is `≥ 2`;
* `iwSL_coprime` — distinct elements of `S_l` are coprime (Tao's Lemma `iwac`);
* `iwSL_pairwise` — the two facts together, in the shape of the hypotheses
  `h2S`, `hS` of `Work.IonescuWainger.main_real_of_inputs`.
-/
import Mathlib
import Submission.Work.Analysis.IonescuWainger.Pset
import Submission.Work.KMTAreas.iwQ0_le

set_option autoImplicit false
set_option maxHeartbeats 1000000

open scoped BigOperators

namespace Work.KMTAreas

open Work.Analysis.IonescuWainger

/-- **The Tao denominator set `S_l`** of Appendix A of Krause–Mirek–Tao:
`S_l = {Q_0^{(l)}} ∪ {p^{D_ρ} : p ∈ (N_0^{(l)}, 2^l] prime}` (the set denoted `S` there; ours
carries the scale `l`). -/
noncomputable def iwSL (ρ : ℝ) (l : ℕ) : Finset ℕ :=
  insert (iwQ0 ρ l) ((iwPrimeRange ρ l).image (fun p => p ^ iwD ρ))

/-- The *sharp* element bound for `S_l`: `max Q_0^{(l)} (2^{l D_ρ})`. -/
noncomputable def iwSLmax (ρ : ℝ) (l : ℕ) : ℕ :=
  max (iwQ0 ρ l) (2 ^ (l * iwD ρ))

theorem iwSLmax_element_le (ρ : ℝ) (l : ℕ) : ∀ q ∈ iwSL ρ l, q ≤ iwSLmax ρ l := by
  intro q hq
  rw [iwSL, Finset.mem_insert] at hq
  rcases hq with rfl | hq
  · exact le_max_left _ _
  · rw [Finset.mem_image] at hq
    obtain ⟨p, hp, rfl⟩ := hq
    refine le_trans ?_ (le_max_right _ _) (α := ℕ)
    have hp2 : p ≤ 2 ^ l := (Finset.mem_Icc.mp (Finset.mem_filter.mp hp).1).2
    calc p ^ iwD ρ ≤ (2 ^ l) ^ iwD ρ := Nat.pow_le_pow_left hp2 _
      _ = 2 ^ (l * iwD ρ) := by rw [← pow_mul]

/-- `N_0^{(l)} = ⌊2^{ρl/2}⌋ + 1 ≥ 2` for `ρ > 0`. -/
theorem two_le_iwN0 (ρ : ℝ) (hρ : 0 < ρ) (l : ℕ) : 2 ≤ iwN0 ρ l := by
  have h1 : (1 : ℝ) ≤ (2 : ℝ) ^ (ρ * (l : ℝ) / 2) :=
    Real.one_le_rpow (by norm_num) (by positivity)
  have hpos : 0 < ⌊(2 : ℝ) ^ (ρ * (l : ℝ) / 2)⌋₊ := Nat.floor_pos.mpr h1
  have : 1 ≤ ⌊(2 : ℝ) ^ (ρ * (l : ℝ) / 2)⌋₊ := by omega
  rw [iwN0]
  omega

/-- `Q_0^{(l)} = (N_0^{(l)}!)^{D_ρ} ≥ 2` for `ρ > 0`. -/
theorem two_le_iwQ0 (ρ : ℝ) (hρ : 0 < ρ) (l : ℕ) : 2 ≤ iwQ0 ρ l := by
  have hN : 2 ≤ iwN0 ρ l := two_le_iwN0 ρ hρ l
  have hfac : 2 ≤ (iwN0 ρ l).factorial := by
    have h := Nat.factorial_le (by omega : 2 ≤ iwN0 ρ l)
    simpa using h
  rw [iwQ0]
  calc 2 ≤ 2 ^ iwD ρ := Nat.le_self_pow (Nat.succ_ne_zero _) 2
    _ ≤ (iwN0 ρ l).factorial ^ iwD ρ := Nat.pow_le_pow_left hfac (iwD ρ)

/-- Every element of `S_l` is at least `2`. -/
theorem iwSL_two_le (ρ : ℝ) (hρ : 0 < ρ) (l : ℕ) : ∀ q ∈ iwSL ρ l, 2 ≤ q := by
  intro q hq
  rw [iwSL, Finset.mem_insert] at hq
  rcases hq with rfl | hq
  · exact two_le_iwQ0 ρ hρ l
  · rw [Finset.mem_image] at hq
    obtain ⟨p, hp, rfl⟩ := hq
    have hp2 : 2 ≤ p := (Finset.mem_filter.mp hp).2.two_le
    calc 2 ≤ p := hp2
      _ ≤ p ^ iwD ρ := Nat.le_self_pow (Nat.succ_ne_zero _) p

/-- `Q_0^{(l)}` is coprime to `p^{D_ρ}` for every prime `p ∈ (N_0^{(l)}, 2^l]`: all prime
factors of `Q_0^{(l)} = (N_0^{(l)}!)^{D_ρ}` are at most `N_0^{(l)}`, hence strictly below `p`. -/
theorem coprime_iwQ0_pow (ρ : ℝ) (l : ℕ) {p : ℕ} (hp : p ∈ iwPrimeRange ρ l) :
    Nat.Coprime (iwQ0 ρ l) (p ^ iwD ρ) := by
  have hpprime : p.Prime := (Finset.mem_filter.mp hp).2
  have hpgt : iwN0 ρ l < p := by
    have := (Finset.mem_Icc.mp (Finset.mem_filter.mp hp).1).1
    omega
  have hcop : Nat.Coprime (iwN0 ρ l).factorial p := by
    rw [Nat.coprime_comm, hpprime.coprime_iff_not_dvd]
    intro hdvd
    exact absurd ((Nat.Prime.dvd_factorial hpprime).mp hdvd) (by omega)
  rw [iwQ0]
  exact (hcop.pow_left _).pow_right _

/-- Distinct elements of `S_l` are coprime (Tao's Lemma `iwac`). -/
theorem iwSL_coprime (ρ : ℝ) (l : ℕ) :
    ∀ p ∈ iwSL ρ l, ∀ q ∈ iwSL ρ l, p ≠ q → Nat.Coprime p q := by
  have hpow : Function.Injective (fun p : ℕ => p ^ iwD ρ) :=
    Nat.pow_left_injective (Nat.succ_ne_zero _)
  intro a ha b hb hab
  rw [iwSL, Finset.mem_insert] at ha hb
  rcases ha with rfl | ha
  · rcases hb with rfl | hb
    · exact absurd rfl hab
    · rw [Finset.mem_image] at hb
      obtain ⟨p, hp, rfl⟩ := hb
      exact coprime_iwQ0_pow ρ l hp
  · rw [Finset.mem_image] at ha
    obtain ⟨p, hp, rfl⟩ := ha
    rcases hb with rfl | hb
    · exact (coprime_iwQ0_pow ρ l hp).symm
    · rw [Finset.mem_image] at hb
      obtain ⟨q, hq, rfl⟩ := hb
      have hpq : p ≠ q := fun h => hab (by rw [h])
      have hcop : Nat.Coprime p q :=
        (Nat.coprime_primes (Finset.mem_filter.mp hp).2 (Finset.mem_filter.mp hq).2).mpr hpq
      exact (hcop.pow_left _).pow_right _

/-- **The arithmetic hypotheses of Tao's `main` for `S_l`**: every element of `S_l` is `≥ 2`
and distinct elements are coprime. -/
theorem iwSL_pairwise (ρ : ℝ) (hρ : 0 < ρ) (l : ℕ) :
    (∀ q ∈ iwSL ρ l, 2 ≤ q) ∧
      (∀ p ∈ iwSL ρ l, ∀ q ∈ iwSL ρ l, p ≠ q → Nat.Coprime p q) :=
  ⟨iwSL_two_le ρ hρ l, iwSL_coprime ρ l⟩

end Work.KMTAreas
