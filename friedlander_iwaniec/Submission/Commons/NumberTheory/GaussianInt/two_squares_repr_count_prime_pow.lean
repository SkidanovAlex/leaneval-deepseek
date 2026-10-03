import Mathlib
import Submission.Commons.NumberTheory.FriedlanderIwaniec.primitive_reps_ncard_le_four_mul_two_pow_omega
import Submission.Commons.NumberTheory.FriedlanderIwaniec.sum_two_squares_repr_le

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

namespace Commons.NumberTheory.GaussianInt

open Finset
open scoped BigOperators

/-! ## Boxes of representations and bridges to `Set.ncard` -/

/-- All `z = (x, y) ∈ ℤ × ℤ` with `x ^ 2 + y ^ 2 = N`, inside the box `[-N, N] ^ 2`. -/
noncomputable def repBox (N : ℕ) : Finset (ℤ × ℤ) :=
  (Finset.Icc (-(N : ℤ)) (N : ℤ) ×ˢ Finset.Icc (-(N : ℤ)) (N : ℤ)).filter
    (fun z => z.1 ^ 2 + z.2 ^ 2 = (N : ℤ))

/-- All *primitive* `z = (x, y)` with `x ^ 2 + y ^ 2 = m` (`Int.gcd x y = 1`). -/
noncomputable def primBox (m : ℕ) : Finset (ℤ × ℤ) :=
  (Finset.Icc (-(m : ℤ)) (m : ℤ) ×ˢ Finset.Icc (-(m : ℤ)) (m : ℤ)).filter
    (fun z => z.1 ^ 2 + z.2 ^ 2 = (m : ℤ) ∧ Int.gcd z.1 z.2 = 1)

lemma mem_repBox {N : ℕ} (hN : 1 ≤ N) {z : ℤ × ℤ} :
    z ∈ repBox N ↔ z.1 ^ 2 + z.2 ^ 2 = (N : ℤ) := by
  rw [repBox, Finset.mem_filter, Finset.mem_product]
  constructor
  · rintro ⟨-, h⟩; exact h
  · intro h
    refine ⟨⟨?_, ?_⟩, h⟩
    · rw [Finset.mem_Icc]
      have h1 : z.1.natAbs ≤ N :=
        Commons.NumberTheory.FriedlanderIwaniec.natAbs_le_of_sq_add_sq_eq hN h
      have : |z.1| ≤ (N : ℤ) := by rw [Int.abs_eq_natAbs]; exact_mod_cast h1
      exact abs_le.mp this
    · rw [Finset.mem_Icc]
      have h2 : z.2.natAbs ≤ N :=
        Commons.NumberTheory.FriedlanderIwaniec.natAbs_le_of_sq_add_sq_eq hN
          (by rw [add_comm]; exact h)
      have : |z.2| ≤ (N : ℤ) := by rw [Int.abs_eq_natAbs]; exact_mod_cast h2
      exact abs_le.mp this

lemma mem_primBox {m : ℕ} (hm : 1 ≤ m) {z : ℤ × ℤ} :
    z ∈ primBox m ↔ z.1 ^ 2 + z.2 ^ 2 = (m : ℤ) ∧ Int.gcd z.1 z.2 = 1 := by
  rw [primBox, Finset.mem_filter, Finset.mem_product]
  constructor
  · rintro ⟨-, h, hg⟩; exact ⟨h, hg⟩
  · rintro ⟨h, hg⟩
    refine ⟨⟨?_, ?_⟩, h, hg⟩
    · rw [Finset.mem_Icc]
      have h1 : z.1.natAbs ≤ m :=
        Commons.NumberTheory.FriedlanderIwaniec.natAbs_le_of_sq_add_sq_eq hm h
      have : |z.1| ≤ (m : ℤ) := by rw [Int.abs_eq_natAbs]; exact_mod_cast h1
      exact abs_le.mp this
    · rw [Finset.mem_Icc]
      have h2 : z.2.natAbs ≤ m :=
        Commons.NumberTheory.FriedlanderIwaniec.natAbs_le_of_sq_add_sq_eq hm
          (by rw [add_comm]; exact h)
      have : |z.2| ≤ (m : ℤ) := by rw [Int.abs_eq_natAbs]; exact_mod_cast h2
      exact abs_le.mp this

lemma card_repBox_eq_ncard (N : ℕ) (hN : 1 ≤ N) :
    (repBox N).card = ({z : ℤ × ℤ | z.1 ^ 2 + z.2 ^ 2 = (N : ℤ)}).ncard := by
  classical
  have hset : ({z : ℤ × ℤ | z.1 ^ 2 + z.2 ^ 2 = (N : ℤ)} : Set (ℤ × ℤ))
      = ↑(repBox N) := by
    ext z
    rw [Set.mem_ofPred_eq, Finset.mem_coe, mem_repBox hN]
  rw [hset, Set.ncard_coe_finset]

lemma card_primBox_eq_ncard (m : ℕ) (hm : 1 ≤ m) :
    (primBox m).card
      = ({z : ℤ × ℤ | z.1 ^ 2 + z.2 ^ 2 = (m : ℤ) ∧ Int.gcd z.1 z.2 = 1}).ncard := by
  classical
  have hset : ({z : ℤ × ℤ | z.1 ^ 2 + z.2 ^ 2 = (m : ℤ) ∧ Int.gcd z.1 z.2 = 1} :
        Set (ℤ × ℤ)) = ↑(primBox m) := by
    ext z
    rw [Set.mem_ofPred_eq, Finset.mem_coe, mem_primBox hm]
  rw [hset, Set.ncard_coe_finset]

/-! ## The gcd layer decomposition -/

/-- `Int.gcd` is multiplicative in the first factor. -/
lemma gcd_mul_gcd (d : ℕ) (a b : ℤ) : Int.gcd ((d : ℤ) * a) ((d : ℤ) * b) = d * Int.gcd a b := by
  rw [Int.gcd_eq_natAbs, Int.gcd_eq_natAbs, Int.natAbs_mul, Int.natAbs_mul,
    Int.natAbs_natCast, Nat.gcd_mul_left]

/-- One layer of the gcd decomposition: the representations of `N` with `gcd = d` correspond
bijectively to the primitive representations of `N / d ^ 2`. -/
lemma fiber_card_eq_primBox_card (N d : ℕ) (hN : 1 ≤ N) (hd : d ^ 2 ∣ N) :
    ((repBox N).filter (fun z => Int.gcd z.1 z.2 = d)).card = (primBox (N / d ^ 2)).card := by
  classical
  have hd0 : d ≠ 0 := by
    rintro rfl
    simp at hd
    omega
  have hdpos : (0 : ℤ) < (d : ℤ) := by exact_mod_cast Nat.pos_of_ne_zero hd0
  have hd2N : d ^ 2 ≤ N := Nat.le_of_dvd (by omega) hd
  have hm : 1 ≤ N / d ^ 2 := by
    rw [Nat.le_div_iff_mul_le (by positivity : 0 < d ^ 2), one_mul]
    exact hd2N
  have hmdvd : (N / d ^ 2) * d ^ 2 = N := Nat.div_mul_cancel hd
  have hd2cast : ((d : ℤ)) ^ 2 = ((d ^ 2 : ℕ) : ℤ) := by push_cast; ring
  refine Finset.card_bij (fun z _ => (z.1 / (d : ℤ), z.2 / (d : ℤ))) ?_ ?_ ?_
  · intro z hz
    rw [Finset.mem_filter] at hz
    obtain ⟨hzreps, hzgcd⟩ := hz
    rw [mem_repBox hN] at hzreps
    have hdvd1 : (d : ℤ) ∣ z.1 := by rw [← hzgcd]; exact Int.gcd_dvd_left _ _
    have hdvd2 : (d : ℤ) ∣ z.2 := by rw [← hzgcd]; exact Int.gcd_dvd_right _ _
    obtain ⟨a, ha⟩ := hdvd1
    obtain ⟨b, hb⟩ := hdvd2
    have hza : z.1 / (d : ℤ) = a := by
      rw [ha, Int.mul_ediv_cancel_left _ (ne_of_gt hdpos)]
    have hzb : z.2 / (d : ℤ) = b := by
      rw [hb, Int.mul_ediv_cancel_left _ (ne_of_gt hdpos)]
    have hnorm : a ^ 2 + b ^ 2 = ((N / d ^ 2 : ℕ) : ℤ) := by
      have h1 : ((d : ℤ)) ^ 2 * (a ^ 2 + b ^ 2) = (N : ℤ) := by
        rw [← hzreps, ha, hb]; ring
      rw [hd2cast] at h1
      have h3 : ((N / d ^ 2 : ℕ) : ℤ) * ((d ^ 2 : ℕ) : ℤ) = (N : ℤ) := by
        rw [← Nat.cast_mul, hmdvd]
      rw [mul_comm] at h1
      exact mul_right_cancel₀ (by positivity : ((d ^ 2 : ℕ) : ℤ) ≠ 0) (h1.trans h3.symm)
    have hgcda : Int.gcd a b = 1 := by
      have hh := gcd_mul_gcd d a b
      rw [← ha, ← hb, hzgcd] at hh
      have h2 : d * Int.gcd a b = d * 1 := by rw [mul_one]; exact hh.symm
      exact Nat.eq_of_mul_eq_mul_left (Nat.pos_of_ne_zero hd0) h2
    rw [mem_primBox hm]
    refine ⟨?_, ?_⟩
    · rw [hza, hzb]; exact hnorm
    · rw [hza, hzb]; exact hgcda
  · intro z hz w hw hzw
    rw [Finset.mem_filter] at hz hw
    have hzgcd := hz.2
    have hwgcd := hw.2
    have hdvd1 : (d : ℤ) ∣ z.1 := by rw [← hzgcd]; exact Int.gcd_dvd_left _ _
    have hdvd2 : (d : ℤ) ∣ z.2 := by rw [← hzgcd]; exact Int.gcd_dvd_right _ _
    have hwdvd1 : (d : ℤ) ∣ w.1 := by rw [← hwgcd]; exact Int.gcd_dvd_left _ _
    have hwdvd2 : (d : ℤ) ∣ w.2 := by rw [← hwgcd]; exact Int.gcd_dvd_right _ _
    have h1 : z.1 = w.1 := by
      have hh := congrArg Prod.fst hzw
      simp only at hh
      rw [← Int.ediv_mul_cancel hdvd1, hh, Int.ediv_mul_cancel hwdvd1]
    have h2 : z.2 = w.2 := by
      have hh := congrArg Prod.snd hzw
      simp only at hh
      rw [← Int.ediv_mul_cancel hdvd2, hh, Int.ediv_mul_cancel hwdvd2]
    exact Prod.ext h1 h2
  · intro w hw
    rw [mem_primBox hm] at hw
    obtain ⟨hweq, hwgcd⟩ := hw
    refine ⟨((d : ℤ) * w.1, (d : ℤ) * w.2), ?_, ?_⟩
    · rw [Finset.mem_filter, mem_repBox hN]
      refine ⟨?_, ?_⟩
      · have hsum : ((d : ℤ) * w.1) ^ 2 + ((d : ℤ) * w.2) ^ 2 = (N : ℤ) := by
          have e : ((d : ℤ) * w.1) ^ 2 + ((d : ℤ) * w.2) ^ 2
              = ((d : ℤ)) ^ 2 * (w.1 ^ 2 + w.2 ^ 2) := by ring
          rw [e, hweq, hd2cast, ← Nat.cast_mul,
            show (d ^ 2 * (N / d ^ 2)) = N from by rw [Nat.mul_comm]; exact hmdvd]
        exact hsum
      · rw [gcd_mul_gcd, hwgcd, mul_one]
    · rw [Int.mul_ediv_cancel_left _ (ne_of_gt hdpos), Int.mul_ediv_cancel_left _ (ne_of_gt hdpos)]


/-! ## An existence lemma: primitive representations of prime powers

For `p ≡ 1 (mod 4)` and `t ≥ 1`, we build a *primitive* representation of `p ^ t` by taking
powers of a Gaussian integer `π = a + b i` of norm `p` (such `a, b` exist by Fermat's theorem).
Primitivity is proved by reducing modulo `p`: the map `ℤ[i] → 𝔽_p` sending `i` to
`r = a · b⁻¹` sends `π` to `2a ≠ 0`, hence `π ^ t` has a nonzero image, so `p` cannot divide
both coordinates of `π ^ t`.  Since the gcd of the coordinates has square dividing `p ^ t`,
it must be `1`. -/

private lemma prime_not_dvd_of_sq_add_sq {p a b : ℕ} (hp : p.Prime) (hab : a ^ 2 + b ^ 2 = p) :
    ¬ p ∣ a ∧ ¬ p ∣ b := by
  have hpa2 : a ^ 2 ≤ p := by rw [← hab]; exact Nat.le_add_right _ _
  have hpb2 : b ^ 2 ≤ p := by rw [← hab]; exact Nat.le_add_left _ _
  have sq_ne_prime : ∀ m : ℕ, m ^ 2 ≠ p := by
    intro m hm
    have hdvd : m ∣ p := ⟨m, by rw [← hm]; ring⟩
    rcases hp.eq_one_or_self_of_dvd m hdvd with h1 | h1
    · rw [h1] at hm
      linarith [hp.two_le, hm]
    · rw [h1] at hm
      nlinarith [hp.two_le, hm]
  have key : ∀ m : ℕ, m ^ 2 ≤ p → p ∣ m → m = 0 := by
    intro m hm hmvd
    by_contra hne
    have h2 : p ^ 2 ∣ m ^ 2 := pow_dvd_pow_of_dvd hmvd 2
    have hpos : 0 < m ^ 2 := pow_pos (Nat.pos_of_ne_zero hne) 2
    have := Nat.le_of_dvd hpos h2
    nlinarith [hp.two_le, hm]
  constructor
  · intro h
    have ha0 : a = 0 := key a hpa2 h
    have hb : b ^ 2 = p := by rw [ha0] at hab; simpa using hab
    exact sq_ne_prime b hb
  · intro h
    have hb0 : b = 0 := key b hpb2 h
    have ha : a ^ 2 = p := by rw [hb0] at hab; simpa using hab
    exact sq_ne_prime a ha

/-- There is a *primitive* representation of `p ^ t` as a sum of two squares, for `p ≡ 1 (mod 4)`
and `t ≥ 1`.

Take a Gaussian integer `π = a + b i` of norm `p` (Fermat's theorem).  Then `π ^ t` has norm
`p ^ t`, and it is primitive: if `p` divided both coordinates of `π ^ t`, then reducing modulo `p`
along the ring hom `ℤ[i] → 𝔽_p` with `i ↦ r = a · b⁻¹` (a square root of `-1`, possible since
`p ∤ b`) would give `0 = F (π ^ t) = (F π) ^ t = (2a) ^ t ≠ 0`. -/
lemma exists_primitive_rep_prime_pow {p : ℕ} (hp : p.Prime) (hp4 : p % 4 = 1) {t : ℕ}
    (ht : 1 ≤ t) :
    ∃ A B : ℤ, A ^ 2 + B ^ 2 = ((p ^ t : ℕ) : ℤ) ∧ Int.gcd A B = 1 := by
  haveI : Fact p.Prime := ⟨hp⟩
  have hp43 : p % 4 ≠ 3 := by omega
  obtain ⟨a, b, hab⟩ := Nat.Prime.sq_add_sq (p := p) hp43
  obtain ⟨hpa, hpb⟩ := prime_not_dvd_of_sq_add_sq hp hab
  have hbne : (((b : ℤ) : ZMod p)) ≠ 0 := fun h0 =>
    hpb (Int.ofNat_dvd.mp ((ZMod.intCast_zmod_eq_zero_iff_dvd b p).mp h0))
  have hbb : ((b : ℤ) : ZMod p) * ((b : ℤ) : ZMod p)⁻¹ = 1 := mul_inv_cancel₀ hbne
  have hcast : ((a : ℤ) : ZMod p) ^ 2 + ((b : ℤ) : ZMod p) ^ 2 = 0 := by
    have h : (a : ZMod p) ^ 2 + (b : ZMod p) ^ 2 = 0 := by
      have h := congrArg (fun n : ℕ => (n : ZMod p)) hab
      push_cast at h
      rw [h]; simp
    push_cast
    exact h
  have ha2 : ((a : ℤ) : ZMod p) ^ 2 = -(((b : ℤ) : ZMod p) ^ 2) := by
    rw [← add_eq_zero_iff_eq_neg]; exact hcast
  let r : ZMod p := ((a : ℤ) : ZMod p) * ((b : ℤ) : ZMod p)⁻¹
  have hr : r * r = (-1 : ZMod p) := by
    show ((a : ℤ) : ZMod p) * ((b : ℤ) : ZMod p)⁻¹
        * (((a : ℤ) : ZMod p) * ((b : ℤ) : ZMod p)⁻¹) = -1
    calc ((a : ℤ) : ZMod p) * ((b : ℤ) : ZMod p)⁻¹
            * (((a : ℤ) : ZMod p) * ((b : ℤ) : ZMod p)⁻¹)
          = ((a : ℤ) : ZMod p) ^ 2 * (((b : ℤ) : ZMod p)⁻¹) ^ 2 := by ring
        _ = (-(((b : ℤ) : ZMod p) ^ 2)) * (((b : ℤ) : ZMod p)⁻¹) ^ 2 := by rw [ha2]
        _ = - ((((b : ℤ) : ZMod p) * ((b : ℤ) : ZMod p)⁻¹) ^ 2) := by rw [mul_pow]; ring
        _ = -1 := by rw [hbb]; ring
  let F : GaussianInt →+* ZMod p := Zsqrtd.lift (R := ZMod p) ⟨r, by rw [hr]; simp⟩
  have hEval : ∀ z : GaussianInt, F z = z.re + z.im * r := by
    intro z
    simp only [F, Zsqrtd.lift_apply_apply]
  let π : GaussianInt := ⟨(a : ℤ), (b : ℤ)⟩
  have hFπ : F π = 2 * ((a : ℤ) : ZMod p) := by
    rw [hEval]
    show ((a : ℤ) : ZMod p) + ((b : ℤ) : ZMod p) * r = 2 * ((a : ℤ) : ZMod p)
    have h2 : ((b : ℤ) : ZMod p) * r = ((a : ℤ) : ZMod p) := by
      show ((b : ℤ) : ZMod p) * (((a : ℤ) : ZMod p) * ((b : ℤ) : ZMod p)⁻¹) = ((a : ℤ) : ZMod p)
      rw [← mul_assoc, mul_comm ((b : ℤ) : ZMod p) ((a : ℤ) : ZMod p), mul_assoc, hbb, mul_one]
    rw [h2]; ring
  have hF2a : F π ≠ 0 := by
    rw [hFπ]
    intro h0
    have h2 : (((2 * a : ℕ) : ℤ) : ZMod p) = 0 := by simpa using h0
    have hdiv : p ∣ 2 * a :=
      Int.ofNat_dvd.mp ((ZMod.intCast_zmod_eq_zero_iff_dvd (((2 * a : ℕ) : ℤ)) p).mp h2)
    rcases hp.dvd_mul.mp hdiv with h | h
    · have : p = 2 := Nat.le_antisymm (Nat.le_of_dvd (by norm_num) h) hp.two_le
      rw [this] at hp4; norm_num at hp4
    · exact hpa h
  have hFpow : F (π ^ t) ≠ 0 := by rw [map_pow]; exact pow_ne_zero t hF2a
  have hnotdiv : ¬ ((p : ℤ) ∣ (π ^ t).re ∧ (p : ℤ) ∣ (π ^ t).im) := by
    rintro ⟨hA, hB⟩
    apply hFpow
    rw [hEval]
    have h1 : (((π ^ t).re : ℤ) : ZMod p) = 0 := by
      rw [ZMod.intCast_zmod_eq_zero_iff_dvd]; exact hA
    have h2 : (((π ^ t).im : ℤ) : ZMod p) = 0 := by
      rw [ZMod.intCast_zmod_eq_zero_iff_dvd]; exact hB
    rw [h1, h2]; ring
  have hnorm : (π ^ t).norm = ((p ^ t : ℕ) : ℤ) := by
    have hmul : ∀ s : ℕ, (π ^ s).norm = ((π.norm) ^ s) := by
      intro s
      induction s with
      | zero => simp
      | succ n ih => rw [pow_succ, Zsqrtd.norm_mul, ih, pow_succ]
    rw [hmul]
    have hπnorm : π.norm = (p : ℤ) := by
      show (Zsqrtd.norm (⟨(a : ℤ), (b : ℤ)⟩ : GaussianInt)) = (p : ℤ)
      rw [Zsqrtd.norm_def]
      have h : (a : ℤ) * (a : ℤ) + (b : ℤ) * (b : ℤ) = (p : ℤ) := by
        rw [← hab]; push_cast; ring
      linarith [h]
    rw [hπnorm]; push_cast; ring
  have hsum : (π ^ t).re ^ 2 + (π ^ t).im ^ 2 = ((p ^ t : ℕ) : ℤ) := by
    rw [← hnorm, Zsqrtd.norm_def]; ring
  refine ⟨(π ^ t).re, (π ^ t).im, hsum, ?_⟩
  by_contra hne
  have hg2dvd : (Int.gcd (π ^ t).re (π ^ t).im) ^ 2 ∣ p ^ t := by
    have h1 : ((Int.gcd (π ^ t).re (π ^ t).im : ℤ)) ∣ (π ^ t).re := Int.gcd_dvd_left _ _
    have h2 : ((Int.gcd (π ^ t).re (π ^ t).im : ℤ)) ∣ (π ^ t).im := Int.gcd_dvd_right _ _
    have h3 : ((Int.gcd (π ^ t).re (π ^ t).im : ℤ)) * ((Int.gcd (π ^ t).re (π ^ t).im : ℤ))
        ∣ (π ^ t).re * (π ^ t).re + (π ^ t).im * (π ^ t).im :=
      Int.dvd_add (mul_dvd_mul h1 h1) (mul_dvd_mul h2 h2)
    have h4 : (π ^ t).re * (π ^ t).re + (π ^ t).im * (π ^ t).im = ((p ^ t : ℕ) : ℤ) := by
      rw [← hsum]; ring
    rw [h4] at h3
    have h5 : (((Int.gcd (π ^ t).re (π ^ t).im) ^ 2 : ℕ) : ℤ) ∣ ((p ^ t : ℕ) : ℤ) := by
      push_cast; rw [sq]; exact h3
    exact Int.ofNat_dvd.mp h5
  obtain ⟨e, het, hge⟩ := (Nat.dvd_prime_pow hp).mp
    (dvd_trans (dvd_pow_self _ (by norm_num)) hg2dvd)
  have he1 : 1 ≤ e := by
    rcases Nat.eq_zero_or_pos e with h | h
    · exact absurd (by rw [hge, h, pow_zero]) hne
    · exact h
  have hpg : p ∣ Int.gcd (π ^ t).re (π ^ t).im := by rw [hge]; exact dvd_pow_self p (by omega)
  exact hnotdiv ⟨Int.dvd_trans (Int.ofNat_dvd.mpr hpg) (Int.gcd_dvd_left _ _),
    Int.dvd_trans (Int.ofNat_dvd.mpr hpg) (Int.gcd_dvd_right _ _)⟩


/-- The number of representations of a positive integer `N` as a sum of two squares is the
sum, over all `d` with `d ^ 2 ∣ N`, of the number of *primitive* representations of `N / d ^ 2`. -/
theorem ncard_reps_eq_sum_primitive (N : ℕ) (hN : 1 ≤ N) :
    ({z : ℤ × ℤ | z.1 ^ 2 + z.2 ^ 2 = (N : ℤ)}).ncard =
      ∑ d ∈ (Finset.range (N + 1)).filter (fun d => d ^ 2 ∣ N),
        ({w : ℤ × ℤ | w.1 ^ 2 + w.2 ^ 2 = ((N / d ^ 2 : ℕ) : ℤ) ∧
          Int.gcd w.1 w.2 = 1}).ncard := by
  classical
  rw [← card_repBox_eq_ncard N hN]
  have hmap : (repBox N : Set (ℤ × ℤ)).MapsTo (fun z => Int.gcd z.1 z.2)
      ((Finset.range (N + 1)).filter (fun d => d ^ 2 ∣ N)) := by
    intro z hz
    rw [Finset.mem_coe, mem_repBox hN] at hz
    rw [Finset.mem_coe, Finset.mem_filter, Finset.mem_range]
    change Int.gcd z.1 z.2 < N + 1 ∧ (Int.gcd z.1 z.2) ^ 2 ∣ N
    have hn1 : z.1.natAbs ≤ N :=
      Commons.NumberTheory.FriedlanderIwaniec.natAbs_le_of_sq_add_sq_eq hN hz
    have hn2 : z.2.natAbs ≤ N :=
      Commons.NumberTheory.FriedlanderIwaniec.natAbs_le_of_sq_add_sq_eq hN
        (by rw [add_comm]; exact hz)
    refine ⟨?_, ?_⟩
    · rw [Int.gcd_eq_natAbs]
      rcases Nat.eq_zero_or_pos z.1.natAbs with h | h
      · rw [h]; simp only [Nat.gcd_zero_left]; omega
      · have hg : Nat.gcd z.1.natAbs z.2.natAbs ≤ N :=
          le_trans (Nat.gcd_le_left z.2.natAbs h) hn1
        omega
    · have h1 : ((Int.gcd z.1 z.2 : ℤ)) ∣ z.1 := Int.gcd_dvd_left _ _
      have h2 : ((Int.gcd z.1 z.2 : ℤ)) ∣ z.2 := Int.gcd_dvd_right _ _
      have h3 : ((Int.gcd z.1 z.2 : ℤ)) * ((Int.gcd z.1 z.2 : ℤ))
          ∣ z.1 * z.1 + z.2 * z.2 :=
        Int.dvd_add (mul_dvd_mul h1 h1) (mul_dvd_mul h2 h2)
      have h4 : z.1 * z.1 + z.2 * z.2 = (N : ℤ) := by rw [← hz]; ring
      rw [h4] at h3
      have h5 : (((Int.gcd z.1 z.2) ^ 2 : ℕ) : ℤ) ∣ ((N : ℕ) : ℤ) := by
        push_cast; rw [sq]; exact h3
      exact Int.ofNat_dvd.mp h5
  rw [Finset.card_eq_sum_card_fiberwise hmap]
  refine Finset.sum_congr rfl ?_
  intro d hd
  rw [Finset.mem_filter] at hd
  have hm : 1 ≤ N / d ^ 2 := by
    have hpos : 0 < d ^ 2 := Nat.pos_of_dvd_of_pos hd.2 (by omega)
    rw [Nat.le_div_iff_mul_le hpos, one_mul]
    exact Nat.le_of_dvd (by omega) hd.2
  rw [fiber_card_eq_primBox_card N d hN hd.2, card_primBox_eq_ncard (N / d ^ 2) hm]


/-! ## Sign helpers and the `8`-element lower bound -/

private def sgn (i : Fin 2) : ℤ := if i = 0 then 1 else -1

private lemma sgn_injective : Function.Injective sgn := by
  intro i j h
  fin_cases i <;> fin_cases j <;> simp_all [sgn]

private lemma sgn_sq (i : Fin 2) : sgn i ^ 2 = 1 := by
  fin_cases i <;> simp [sgn]

private lemma sgn_natAbs (i : Fin 2) : (sgn i).natAbs = 1 := by
  fin_cases i <;> simp [sgn]

/-- If `(A, B)` is a primitive representation of `n ≥ 1` with `A, B ≠ 0` and `A ≠ ±B`, then
there are at least `8` primitive representations of `n`: the four signed versions of `(A, B)`
and the four signed versions of `(B, A)`. -/
private lemma eight_le_prim_ncard {n : ℕ} (hn : 1 ≤ n) {A B : ℤ}
    (hN : A ^ 2 + B ^ 2 = (n : ℤ)) (hA : A ≠ 0) (hB : B ≠ 0) (hgcd : Int.gcd A B = 1)
    (hAB : A ≠ B) (hAB' : A ≠ -B) :
    8 ≤ ({z : ℤ × ℤ | z.1 ^ 2 + z.2 ^ 2 = (n : ℤ) ∧ Int.gcd z.1 z.2 = 1}).ncard := by
  classical
  let f₁ : Fin 2 × Fin 2 → ℤ × ℤ := fun i => (sgn i.1 * A, sgn i.2 * B)
  let f₂ : Fin 2 × Fin 2 → ℤ × ℤ := fun i => (sgn i.1 * B, sgn i.2 * A)
  have hf₁ : Function.Injective f₁ := by
    rintro ⟨a, b⟩ ⟨a', b'⟩ h
    simp only [f₁, Prod.mk.injEq] at h
    obtain ⟨h1, h2⟩ := h
    have ha : a = a' := sgn_injective (mul_right_cancel₀ hA h1)
    have hb : b = b' := sgn_injective (mul_right_cancel₀ hB h2)
    simp [ha, hb]
  have hf₂ : Function.Injective f₂ := by
    rintro ⟨a, b⟩ ⟨a', b'⟩ h
    simp only [f₂, Prod.mk.injEq] at h
    obtain ⟨h1, h2⟩ := h
    have ha : a = a' := sgn_injective (mul_right_cancel₀ hB h1)
    have hb : b = b' := sgn_injective (mul_right_cancel₀ hA h2)
    simp [ha, hb]
  let S₁ : Finset (ℤ × ℤ) := (Finset.univ : Finset (Fin 2 × Fin 2)).image f₁
  let S₂ : Finset (ℤ × ℤ) := (Finset.univ : Finset (Fin 2 × Fin 2)).image f₂
  have hcard₁ : S₁.card = 4 := by
    rw [show S₁ = _ from rfl, Finset.card_image_of_injective _ hf₁]
    simp [Fintype.card_prod]
  have hcard₂ : S₂.card = 4 := by
    rw [show S₂ = _ from rfl, Finset.card_image_of_injective _ hf₂]
    simp [Fintype.card_prod]
  have hinter : S₁ ∩ S₂ = ∅ := by
    rw [Finset.eq_empty_iff_forall_notMem]
    intro x hx
    rw [Finset.mem_inter, show S₁ = _ from rfl, show S₂ = _ from rfl,
      Finset.mem_image, Finset.mem_image] at hx
    obtain ⟨⟨⟨a, b⟩, -, h1⟩, ⟨⟨a', b'⟩, -, h2⟩⟩ := hx
    have heq : f₁ (a, b) = f₂ (a', b') := by rw [h1, h2]
    simp only [f₁, f₂, Prod.mk.injEq] at heq
    have hsq : A ^ 2 = B ^ 2 := by
      have h := congrArg (fun x : ℤ => x ^ 2) heq.1
      simpa only [mul_pow, sgn_sq, one_mul] using h
    rcases sq_eq_sq_iff_eq_or_eq_neg.mp hsq with hh | hh
    · exact hAB hh
    · exact hAB' hh
  have hsub : (S₁ ∪ S₂) ⊆ primBox n := by
    intro z hz
    rw [Finset.mem_union, show S₁ = _ from rfl, show S₂ = _ from rfl,
      Finset.mem_image, Finset.mem_image] at hz
    rw [mem_primBox hn]
    rcases hz with ⟨⟨i, -, rfl⟩⟩ | ⟨⟨i, -, rfl⟩⟩
    · refine ⟨?_, ?_⟩
      · have h : (sgn i.1 * A) ^ 2 + (sgn i.2 * B) ^ 2 = A ^ 2 + B ^ 2 := by
          rw [mul_pow, mul_pow, sgn_sq, sgn_sq, one_mul, one_mul]
        exact h.trans hN
      · show Nat.gcd (sgn i.1 * A).natAbs (sgn i.2 * B).natAbs = 1
        rw [Int.natAbs_mul, Int.natAbs_mul, sgn_natAbs, sgn_natAbs, one_mul, one_mul]
        exact hgcd
    · refine ⟨?_, ?_⟩
      · have h : (sgn i.1 * B) ^ 2 + (sgn i.2 * A) ^ 2 = A ^ 2 + B ^ 2 := by
          rw [mul_pow, mul_pow, sgn_sq, sgn_sq, one_mul, one_mul]; ring
        exact h.trans hN
      · show Nat.gcd (sgn i.1 * B).natAbs (sgn i.2 * A).natAbs = 1
        rw [Int.natAbs_mul, Int.natAbs_mul, sgn_natAbs, sgn_natAbs, one_mul, one_mul,
          Nat.gcd_comm]
        exact hgcd
  have hcard : (S₁ ∪ S₂).card = 8 := by
    have h := Finset.card_union_add_card_inter S₁ S₂
    rw [hinter, Finset.card_empty, hcard₁, hcard₂] at h
    omega
  calc (8 : ℕ) = (S₁ ∪ S₂).card := hcard.symm
    _ ≤ (primBox n).card := Finset.card_le_card hsub
    _ = ({z : ℤ × ℤ | z.1 ^ 2 + z.2 ^ 2 = (n : ℤ) ∧ Int.gcd z.1 z.2 = 1}).ncard :=
        card_primBox_eq_ncard n hn


/-! ## Primitive representation counts -/

/-- The number of primitive representations of `m` as a sum of two squares. -/
noncomputable def primCount (m : ℕ) : ℕ :=
  ({z : ℤ × ℤ | z.1 ^ 2 + z.2 ^ 2 = (m : ℤ) ∧ Int.gcd z.1 z.2 = 1}).ncard

private lemma int_eq_zero_or_one_or_neg_one_of_sq_le_two {a : ℤ} (h : a ^ 2 ≤ 2) :
    a = 0 ∨ a = 1 ∨ a = -1 := by
  have h1 : 2 * a ≤ 3 := by nlinarith [h, sq_nonneg (a - 1)]
  have h2 : -3 ≤ 2 * a := by nlinarith [h, sq_nonneg (a + 1)]
  have hu : a ≤ 1 := by omega
  have hl : -1 ≤ a := by omega
  interval_cases a <;> simp

lemma primCount_one : primCount 1 = 4 := by
  unfold primCount
  have hset : ({z : ℤ × ℤ | z.1 ^ 2 + z.2 ^ 2 = ((1 : ℕ) : ℤ) ∧ Int.gcd z.1 z.2 = 1} :
        Set (ℤ × ℤ)) = ↑({(1, 0), (-1, 0), (0, 1), (0, -1)} : Finset (ℤ × ℤ)) := by
    ext z
    rw [Set.mem_ofPred_eq, Finset.mem_coe, Finset.mem_insert, Finset.mem_insert, Finset.mem_insert,
      Finset.mem_singleton]
    constructor
    · rintro ⟨h, -⟩
      norm_num at h
      have hz1 : z.1 = 0 ∨ z.1 = 1 ∨ z.1 = -1 := by
        have h1 : z.1 ^ 2 ≤ (2 : ℤ) := by linarith [sq_nonneg z.2]
        rcases int_eq_zero_or_one_or_neg_one_of_sq_le_two h1 with h' | h' | h'
        · exact Or.inl h'
        · exact Or.inr (Or.inl h')
        · exact Or.inr (Or.inr h')
      have hz2 : z.2 = 0 ∨ z.2 = 1 ∨ z.2 = -1 := by
        have h2 : z.2 ^ 2 ≤ (2 : ℤ) := by linarith [sq_nonneg z.1]
        rcases int_eq_zero_or_one_or_neg_one_of_sq_le_two h2 with h' | h' | h'
        · exact Or.inl h'
        · exact Or.inr (Or.inl h')
        · exact Or.inr (Or.inr h')
      rcases hz1 with h1 | h1 | h1 <;> rcases hz2 with h2 | h2 | h2
      · exfalso; rw [h1, h2] at h; norm_num at h
      · right; right; left; exact Prod.ext h1 h2
      · right; right; right; exact Prod.ext h1 h2
      · left; exact Prod.ext h1 h2
      · exfalso; rw [h1, h2] at h; norm_num at h
      · exfalso; rw [h1, h2] at h; norm_num at h
      · right; left; exact Prod.ext h1 h2
      · exfalso; rw [h1, h2] at h; norm_num at h
      · exfalso; rw [h1, h2] at h; norm_num at h
    · rintro (h | h | h | h) <;> rw [h] <;> decide
  rw [hset, Set.ncard_coe_finset]
  decide

lemma primCount_two : primCount 2 = 4 := by
  unfold primCount
  have hset : ({z : ℤ × ℤ | z.1 ^ 2 + z.2 ^ 2 = ((2 : ℕ) : ℤ) ∧ Int.gcd z.1 z.2 = 1} :
        Set (ℤ × ℤ)) =
      ↑({(1, 1), (1, -1), (-1, 1), (-1, -1)} : Finset (ℤ × ℤ)) := by
    ext z
    rw [Set.mem_ofPred_eq, Finset.mem_coe, Finset.mem_insert, Finset.mem_insert, Finset.mem_insert,
      Finset.mem_singleton]
    constructor
    · rintro ⟨h, -⟩
      norm_num at h
      have hz1 : z.1 = 0 ∨ z.1 = 1 ∨ z.1 = -1 := by
        have h1 : z.1 ^ 2 ≤ (2 : ℤ) := by linarith [sq_nonneg z.2]
        exact int_eq_zero_or_one_or_neg_one_of_sq_le_two h1
      have hz2 : z.2 = 0 ∨ z.2 = 1 ∨ z.2 = -1 := by
        have h2 : z.2 ^ 2 ≤ (2 : ℤ) := by nlinarith [sq_nonneg z.1]
        exact int_eq_zero_or_one_or_neg_one_of_sq_le_two h2
      rcases hz1 with h1 | h1 | h1 <;> rcases hz2 with h2 | h2 | h2
      · exfalso; rw [h1, h2] at h; norm_num at h
      · exfalso; rw [h1, h2] at h; norm_num at h
      · exfalso; rw [h1, h2] at h; norm_num at h
      · exfalso; rw [h1, h2] at h; norm_num at h
      · left; exact Prod.ext h1 h2
      · right; left; exact Prod.ext h1 h2
      · exfalso; rw [h1, h2] at h; norm_num at h
      · right; right; left; exact Prod.ext h1 h2
      · right; right; right; exact Prod.ext h1 h2
    · rintro (h | h | h | h) <;> rw [h] <;> decide
  rw [hset, Set.ncard_coe_finset]
  decide


/-- If `p ≡ 3 (mod 4)` is prime and `p ∣ a ^ 2 + b ^ 2`, then `p ∣ a` and `p ∣ b`. -/
private lemma prime_dvd_of_dvd_sq_add_sq {p a b : ℕ} (hp : p.Prime) (hp4 : p % 4 = 3)
    (h : p ∣ a ^ 2 + b ^ 2) : p ∣ a ∧ p ∣ b := by
  haveI : Fact p.Prime := ⟨hp⟩
  have hcast : (a : ZMod p) ^ 2 + (b : ZMod p) ^ 2 = 0 := by
    rw [← Nat.cast_pow, ← Nat.cast_pow, ← Nat.cast_add]
    exact (ZMod.natCast_eq_zero_iff (a ^ 2 + b ^ 2) p).mpr h
  have hsym : (b : ZMod p) ^ 2 + (a : ZMod p) ^ 2 = 0 := by rw [add_comm]; exact hcast
  -- if `y` is not divisible by `p` then `x` is forced to be
  have key : ∀ x y : ℕ, (x : ZMod p) ^ 2 + (y : ZMod p) ^ 2 = 0 → ¬ p ∣ y → p ∣ x := by
    intro x y hxy hy
    by_contra hx
    have hxn : (x : ZMod p) ≠ 0 := fun h0 => hx ((ZMod.natCast_eq_zero_iff x p).mp h0)
    have hxy' : (y : ZMod p) ^ 2 = -((x : ZMod p) ^ 2) := by
      rw [← add_eq_zero_iff_eq_neg, add_comm]; exact hxy
    exact absurd hp4 (ZMod.mod_four_ne_three_of_sq_eq_neg_sq' hxn hxy')
  constructor
  · by_contra hx
    have hb : p ∣ b := by
      by_contra hy
      exact hx (key a b hcast hy)
    have h2 : p ∣ a ^ 2 :=
      (Nat.dvd_add_iff_left (m := a ^ 2) (dvd_pow hb (n := 2) (by norm_num))).mpr h
    exact hx (hp.dvd_of_dvd_pow h2)
  · by_contra hy
    have ha : p ∣ a := by
      by_contra hx
      exact hy (key b a hsym hx)
    have h2 : p ∣ b ^ 2 :=
      (Nat.dvd_add_iff_left (m := b ^ 2) (n := a ^ 2) (dvd_pow ha (n := 2) (by norm_num))).mpr
        (by rw [add_comm]; exact h)
    exact hy (hp.dvd_of_dvd_pow h2)

lemma primCount_prime_pow_mod_three {p t : ℕ} (hp : p.Prime) (hp4 : p % 4 = 3) (ht : 1 ≤ t) :
    primCount (p ^ t) = 0 := by
  unfold primCount
  have hempty : ({z : ℤ × ℤ | z.1 ^ 2 + z.2 ^ 2 = ((p ^ t : ℕ) : ℤ) ∧
      Int.gcd z.1 z.2 = 1} : Set (ℤ × ℤ)) = ∅ := by
    rw [Set.eq_empty_iff_forall_notMem]
    rintro z ⟨h, hg⟩
    have hnat : ((z.1.natAbs ^ 2 + z.2.natAbs ^ 2 : ℕ) : ℤ) = ((p ^ t : ℕ) : ℤ) := by
      have e1 : ((z.1.natAbs ^ 2 : ℕ) : ℤ) = z.1 ^ 2 := by push_cast; exact sq_abs z.1
      have e2 : ((z.2.natAbs ^ 2 : ℕ) : ℤ) = z.2 ^ 2 := by push_cast; exact sq_abs z.2
      rw [Nat.cast_add, e1, e2, h]
    have hnat' : z.1.natAbs ^ 2 + z.2.natAbs ^ 2 = p ^ t := by exact_mod_cast hnat
    have hpdvd : p ∣ z.1.natAbs ^ 2 + z.2.natAbs ^ 2 := by
      rw [hnat']; exact dvd_pow_self p (by omega)
    obtain ⟨h1, h2⟩ := prime_dvd_of_dvd_sq_add_sq hp hp4 hpdvd
    have hpg : p ∣ Int.gcd z.1 z.2 := by
      rw [Int.gcd_eq_natAbs]; exact Nat.dvd_gcd h1 h2
    rw [hg] at hpg
    exact hp.not_dvd_one hpg
  rw [hempty]; exact Set.ncard_empty _

private lemma zmod4_sq_eq_zero_or_one (x : ZMod 4) : x ^ 2 = 0 ∨ x ^ 2 = 1 := by
  fin_cases x <;> decide

lemma primCount_two_pow {t : ℕ} (ht : 2 ≤ t) : primCount (2 ^ t) = 0 := by
  unfold primCount
  have h4 : (4 : ℕ) ∣ 2 ^ t := by
    have h : 2 ^ 2 ∣ 2 ^ t := Nat.pow_dvd_pow 2 ht
    simpa using h
  have hempty : ({z : ℤ × ℤ | z.1 ^ 2 + z.2 ^ 2 = ((2 ^ t : ℕ) : ℤ) ∧
      Int.gcd z.1 z.2 = 1} : Set (ℤ × ℤ)) = ∅ := by
    rw [Set.eq_empty_iff_forall_notMem]
    rintro z ⟨h, hg⟩
    have hnat : ((z.1.natAbs ^ 2 + z.2.natAbs ^ 2 : ℕ) : ℤ) = ((2 ^ t : ℕ) : ℤ) := by
      have e1 : ((z.1.natAbs ^ 2 : ℕ) : ℤ) = z.1 ^ 2 := by push_cast; exact sq_abs z.1
      have e2 : ((z.2.natAbs ^ 2 : ℕ) : ℤ) = z.2 ^ 2 := by push_cast; exact sq_abs z.2
      rw [Nat.cast_add, e1, e2, h]
    have hnat' : z.1.natAbs ^ 2 + z.2.natAbs ^ 2 = 2 ^ t := by exact_mod_cast hnat
    have hmod : ((z.1.natAbs : ZMod 4)) ^ 2 + ((z.2.natAbs : ZMod 4)) ^ 2 = 0 := by
      have hc := congrArg (fun x : ℕ => (x : ZMod 4)) hnat'
      rw [Nat.cast_add, Nat.cast_pow, Nat.cast_pow] at hc
      rw [hc, ZMod.natCast_eq_zero_iff]
      exact h4
    have hz1 : ((z.1.natAbs : ZMod 4)) ^ 2 = 0 := by
      rcases zmod4_sq_eq_zero_or_one (z.1.natAbs : ZMod 4) with h1 | h1
      · exact h1
      · exfalso
        rcases zmod4_sq_eq_zero_or_one (z.2.natAbs : ZMod 4) with h2 | h2 <;>
          rw [h1, h2] at hmod <;> exact absurd hmod (by decide)
    have hz2 : ((z.2.natAbs : ZMod 4)) ^ 2 = 0 := by
      rcases zmod4_sq_eq_zero_or_one (z.2.natAbs : ZMod 4) with h1 | h1
      · exact h1
      · exfalso
        rcases zmod4_sq_eq_zero_or_one (z.1.natAbs : ZMod 4) with h2 | h2 <;>
          rw [h1, h2] at hmod <;> exact absurd hmod (by decide)
    have key : ∀ w : ℕ, ((w : ZMod 4)) ^ 2 = 0 → 2 ∣ w := by
      intro w hw
      have h5 : ((w ^ 2 : ℕ) : ZMod 4) = 0 := by rw [Nat.cast_pow]; exact hw
      have h6 : 4 ∣ w ^ 2 := (ZMod.natCast_eq_zero_iff (w ^ 2) 4).mp h5
      exact Nat.prime_two.dvd_of_dvd_pow (dvd_trans (by norm_num : 2 ∣ 4) h6)
    have hpg : 2 ∣ Int.gcd z.1 z.2 := by
      rw [Int.gcd_eq_natAbs]; exact Nat.dvd_gcd (key _ hz1) (key _ hz2)
    rw [hg] at hpg
    exact absurd hpg (by norm_num)
  rw [hempty]; exact Set.ncard_empty _


lemma primCount_prime_pow_mod_one {p t : ℕ} (hp : p.Prime) (hp4 : p % 4 = 1) (ht : 1 ≤ t) :
    primCount (p ^ t) = 8 := by
  unfold primCount
  refine le_antisymm ?_ ?_
  · have h := Commons.NumberTheory.FriedlanderIwaniec.primitive_reps_ncard_le_four_mul_two_pow_omega
      (p ^ t) (Nat.one_le_pow t p hp.pos)
    rw [Nat.primeFactors_prime_pow (by omega) hp, Finset.card_singleton] at h
    simpa using h
  · obtain ⟨A, B, hN, hgcd⟩ := exists_primitive_rep_prime_pow hp hp4 ht
    have hA : A ≠ 0 := by
      rintro rfl
      have hB1 : B.natAbs = 1 := by
        have h := hgcd
        rw [Int.gcd_eq_natAbs] at h
        simpa using h
      have hB2 : B ^ 2 = 1 := by
        have := Int.natAbs_sq B
        rw [hB1] at this
        norm_num at this
        exact this.symm
      have hp1 : ((p ^ t : ℕ) : ℤ) = 1 := by rw [← hN]; simp [hB2]
      have hp1' : p ^ t = 1 := by exact_mod_cast hp1
      have h2 : 1 < p ^ t := Nat.one_lt_pow (by omega) hp.one_lt
      omega
    have hB : B ≠ 0 := by
      rintro rfl
      have hA1 : A.natAbs = 1 := by
        have h := hgcd
        rw [Int.gcd_eq_natAbs] at h
        simpa using h
      have hA2 : A ^ 2 = 1 := by
        have := Int.natAbs_sq A
        rw [hA1] at this
        norm_num at this
        exact this.symm
      have hp1 : ((p ^ t : ℕ) : ℤ) = 1 := by rw [← hN]; simp [hA2, add_comm]
      have hp1' : p ^ t = 1 := by exact_mod_cast hp1
      have h2 : 1 < p ^ t := Nat.one_lt_pow (by omega) hp.one_lt
      omega
    have hnot2 : p ≠ 2 := by rintro rfl; norm_num at hp4
    have hAB : A ≠ B := by
      rintro h
      have h2 : (2 : ℤ) ∣ ((p ^ t : ℕ) : ℤ) := ⟨A ^ 2, by rw [← hN, h]; ring⟩
      have h2n : 2 ∣ p ^ t := Int.ofNat_dvd.mp h2
      have hp2 : 2 ∣ p := Nat.prime_two.dvd_of_dvd_pow h2n
      rcases hp.eq_one_or_self_of_dvd 2 hp2 with h' | h'
      · norm_num at h'
      · exact hnot2 h'.symm
    have hAB' : A ≠ -B := by
      rintro h
      have hsq : A ^ 2 = B ^ 2 := by rw [h]; ring
      have h2 : (2 : ℤ) ∣ ((p ^ t : ℕ) : ℤ) := ⟨A ^ 2, by rw [← hN, hsq]; ring⟩
      have h2n : 2 ∣ p ^ t := Int.ofNat_dvd.mp h2
      have hp2 : 2 ∣ p := Nat.prime_two.dvd_of_dvd_pow h2n
      rcases hp.eq_one_or_self_of_dvd 2 hp2 with h' | h'
      · norm_num at h'
      · exact hnot2 h'.symm
    exact eight_le_prim_ncard (Nat.one_le_pow t p hp.pos) hN hA hB hgcd hAB hAB'


/-! ## Reindexing the divisor sum -/

private lemma sum_divisors_primCount {p k : ℕ} (hp : p.Prime) :
    ∑ d ∈ (Finset.range (p ^ k + 1)).filter (fun d => d ^ 2 ∣ p ^ k), primCount (p ^ k / d ^ 2)
      = ∑ e ∈ Finset.range (k / 2 + 1), primCount (p ^ (k - 2 * e)) := by
  have hT : (Finset.range (p ^ k + 1)).filter (fun d => d ^ 2 ∣ p ^ k)
      = (Finset.range (k / 2 + 1)).image (fun e => p ^ e) := by
    ext d
    rw [Finset.mem_filter, Finset.mem_range, Finset.mem_image]
    constructor
    · rintro ⟨hle, hdvd⟩
      have hdvd' : d ∣ p ^ k := dvd_trans (dvd_pow_self d (by norm_num)) hdvd
      obtain ⟨e, hek, rfl⟩ := (Nat.dvd_prime_pow hp).mp hdvd'
      refine ⟨e, ?_, rfl⟩
      rw [Finset.mem_range]
      have h2e : p ^ (2 * e) ∣ p ^ k := by
        have h : (p ^ e) ^ 2 = p ^ (2 * e) := by
          rw [← pow_mul, show e * 2 = 2 * e from by ring]
        rwa [h] at hdvd
      have := (Nat.pow_dvd_pow_iff_le_right hp.one_lt).mp h2e
      omega
    · rintro ⟨e, he, rfl⟩
      rw [Finset.mem_range] at he
      refine ⟨?_, ?_⟩
      · have : e ≤ k := by omega
        have h1 : p ^ e ≤ p ^ k := Nat.pow_le_pow_right hp.pos this
        omega
      · have h2e : 2 * e ≤ k := by omega
        rw [show (p ^ e) ^ 2 = p ^ (2 * e) from by rw [← pow_mul]; ring]
        exact pow_dvd_pow p h2e
  rw [hT]
  have hinj : Set.InjOn (fun e => p ^ e) ↑(Finset.range (k / 2 + 1)) := by
    intro x _ y _ hxy
    exact Nat.pow_right_injective hp.two_le hxy
  rw [Finset.sum_image (s := Finset.range (k / 2 + 1)) (g := fun e => p ^ e)
    (f := fun d => primCount (p ^ k / d ^ 2)) hinj]
  refine Finset.sum_congr rfl ?_
  intro e he
  rw [Finset.mem_range] at he
  congr 1
  have h2e : 2 * e ≤ k := by omega
  rw [show (p ^ e) ^ 2 = p ^ (2 * e) from by rw [← pow_mul]; ring]
  exact Nat.pow_div h2e hp.pos

/-! ## Evaluating the sum over `e` -/

private lemma sum_primCount_two (k : ℕ) :
    ∑ e ∈ Finset.range (k / 2 + 1), primCount (2 ^ (k - 2 * e)) = 4 := by
  rw [Finset.sum_eq_single (k / 2)]
  · rcases Nat.mod_two_eq_zero_or_one k with h | h
    · have : k - 2 * (k / 2) = 0 := by omega
      rw [this, pow_zero, primCount_one]
    · have : k - 2 * (k / 2) = 1 := by omega
      rw [this, pow_one, primCount_two]
  · intro b hb hbne
    rw [Finset.mem_range] at hb
    have h2 : 2 ≤ k - 2 * b := by omega
    rw [show k - 2 * b = 2 + (k - 2 * b - 2) from by omega]
    exact primCount_two_pow (by omega)
  · intro h
    exact absurd (Finset.mem_range.mpr (by omega)) h

private lemma sum_primCount_mod_one {p k : ℕ} (hp : p.Prime) (hp4 : p % 4 = 1) :
    ∑ e ∈ Finset.range (k / 2 + 1), primCount (p ^ (k - 2 * e)) = 4 * (k + 1) := by
  by_cases hk2 : 2 ∣ k
  · obtain ⟨m, rfl⟩ := hk2
    have hm : (2 * m) / 2 = m := Nat.mul_div_right m (by norm_num)
    rw [hm, Finset.sum_range_succ]
    have hlast : primCount (p ^ (2 * m - 2 * m)) = 4 := by
      rw [show 2 * m - 2 * m = 0 from by omega, pow_zero, primCount_one]
    have hrest : ∑ e ∈ Finset.range m, primCount (p ^ (2 * m - 2 * e)) = 8 * m := by
      have h : ∀ e ∈ Finset.range m, primCount (p ^ (2 * m - 2 * e)) = 8 := by
        intro e he
        rw [Finset.mem_range] at he
        exact primCount_prime_pow_mod_one hp hp4 (by omega)
      rw [Finset.sum_congr rfl h, Finset.sum_const, Finset.card_range, smul_eq_mul, mul_comm]
    rw [hlast, hrest]
    ring
  · have hkmod : k % 2 = 1 := by
      have hlt := Nat.mod_lt k (by norm_num : 0 < 2)
      omega
    have hk_eq : k = 2 * (k / 2) + 1 := by
      have := Nat.div_add_mod k 2
      omega
    have hall : ∀ e ∈ Finset.range (k / 2 + 1), primCount (p ^ (k - 2 * e)) = 8 := by
      intro e he
      rw [Finset.mem_range] at he
      exact primCount_prime_pow_mod_one hp hp4 (by omega)
    rw [Finset.sum_congr rfl hall, Finset.sum_const, Finset.card_range, smul_eq_mul]
    omega

private lemma sum_primCount_mod_three {p k : ℕ} (hp : p.Prime) (hp4 : p % 4 = 3) :
    ∑ e ∈ Finset.range (k / 2 + 1), primCount (p ^ (k - 2 * e)) = if Even k then 4 else 0 := by
  by_cases hk2 : 2 ∣ k
  · obtain ⟨m, rfl⟩ := hk2
    have hm : (2 * m) / 2 = m := Nat.mul_div_right m (by norm_num)
    rw [hm, Finset.sum_range_succ, if_pos (even_iff_two_dvd.mpr ⟨m, rfl⟩)]
    have hrest : ∑ e ∈ Finset.range m, primCount (p ^ (2 * m - 2 * e)) = 0 := by
      rw [Finset.sum_eq_zero]
      intro e he
      rw [Finset.mem_range] at he
      exact primCount_prime_pow_mod_three hp hp4 (by omega)
    rw [hrest, show 2 * m - 2 * m = 0 from by omega, pow_zero, primCount_one]
  · rw [if_neg (fun h => hk2 (even_iff_two_dvd.mp h))]
    rw [Finset.sum_eq_zero]
    intro e he
    rw [Finset.mem_range] at he
    exact primCount_prime_pow_mod_three hp hp4 (by omega)


/-- **The number of representations of a prime power as a sum of two squares.**

For a prime `p` and `k ≥ 1`, the number of pairs `(x, y) ∈ ℤ²` with `x² + y² = pᵏ` is
`4` if `p = 2`, `4(k+1)` if `p ≡ 1 (mod 4)`, `4` if `p ≡ 3 (mod 4)` and `k` is even, and `0`
otherwise. -/
theorem two_squares_repr_count_prime_pow (p : ℕ) (hp : p.Prime) (k : ℕ) (hk : 1 ≤ k) :
    ((Finset.filter (fun z : ℤ × ℤ => z.1 ^ 2 + z.2 ^ 2 = ((p ^ k : ℕ) : ℤ))
      (Finset.Icc (-(((p ^ k : ℕ) : ℤ))) (((p ^ k : ℕ) : ℤ))
        ×ˢ Finset.Icc (-(((p ^ k : ℕ) : ℤ))) (((p ^ k : ℕ) : ℤ)))).card : ℤ)
      = (if p = 2 then 4 else if p % 4 = 1 then 4 * (k + 1) else if Even k then 4 else 0) := by
  have hpk : 1 ≤ p ^ k := Nat.one_le_pow k p hp.pos
  have hN : (repBox (p ^ k)).card
      = (if p = 2 then 4 else if p % 4 = 1 then 4 * (k + 1) else if Even k then 4 else 0) := by
    rw [card_repBox_eq_ncard (p ^ k) hpk, ncard_reps_eq_sum_primitive (p ^ k) hpk]
    change (∑ d ∈ (Finset.range (p ^ k + 1)).filter (fun d => d ^ 2 ∣ p ^ k),
        primCount (p ^ k / d ^ 2)) = (if p = 2 then 4 else if p % 4 = 1 then 4 * (k + 1)
          else if Even k then 4 else 0)
    rw [sum_divisors_primCount hp]
    by_cases hp2 : p = 2
    · subst hp2
      rw [if_pos rfl, sum_primCount_two k]
    · rw [if_neg hp2]
      by_cases hp41 : p % 4 = 1
      · rw [if_pos hp41, sum_primCount_mod_one hp hp41]
      · rw [if_neg hp41]
        have hp43 : p % 4 = 3 := by
          rcases hp.eq_two_or_odd with h | h
          · exact absurd h hp2
          · omega
        rw [sum_primCount_mod_three hp hp43]
  change (((repBox (p ^ k)).card : ℤ) = (if p = 2 then 4 else if p % 4 = 1 then 4 * (k + 1)
    else if Even k then 4 else 0))
  rw [hN]

end Commons.NumberTheory.GaussianInt
