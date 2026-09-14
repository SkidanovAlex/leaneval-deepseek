import Mathlib.Algebra.Order.Star.Basic
import Submission.Commons.Data.ZMod.range_card_eq_subtype
import Submission.Commons.Data.Nat.padicValNat_factorization

set_option linter.style.haveILetI false

namespace Commons.NumberTheory.FriedlanderIwaniec

open Finset

/-! ## Elementary counting lemmas -/

/-- Number of multiples of `d` strictly below `m`, when `d ∣ m`. -/
lemma card_filter_range_dvd (m d : ℕ) (hd : 0 < d) (hdvd : d ∣ m) :
    ((Finset.range m).filter (fun x => d ∣ x)).card = m / d := by
  have key : ((Finset.range m).filter (fun x => d ∣ x)).card = (Finset.range (m / d)).card := by
    refine Finset.card_bij (fun x _ => x / d) ?_ ?_ ?_
    · intro x hx
      simp only [Finset.mem_range, Finset.mem_filter] at hx ⊢
      obtain ⟨hxm, hdx⟩ := hx
      have hx' : d * (x / d) = x := Nat.mul_div_cancel' hdx
      have hm' : d * (m / d) = m := Nat.mul_div_cancel' hdvd
      have : d * (x / d) < d * (m / d) := by rw [hx', hm']; exact hxm
      exact (Nat.mul_lt_mul_left hd).mp this
    · intro a ha b hb h
      simp only [Finset.mem_filter] at ha hb
      have haz : d * (a / d) = a := Nat.mul_div_cancel' ha.2
      have hbz : d * (b / d) = b := Nat.mul_div_cancel' hb.2
      rw [← haz, ← hbz, h]
    · intro k hk
      simp only [Finset.mem_range] at hk
      refine ⟨d * k, ?_, ?_⟩
      · simp only [Finset.mem_filter, Finset.mem_range]
        refine ⟨?_, dvd_mul_right d k⟩
        have hm' : d * (m / d) = m := Nat.mul_div_cancel' hdvd
        rw [← hm']
        exact (Nat.mul_lt_mul_left hd).mpr hk
      · exact Nat.mul_div_right k hd
  rw [key, Finset.card_range]

/-- Counting a predicate of `x % m` over a full period `range n` when `m ∣ n`. -/
lemma card_filter_range_mod (m n : ℕ) (hm : 0 < m) (hmn : m ∣ n)
    (ψ : ℕ → Prop) [DecidablePred ψ] :
    ((Finset.range n).filter (fun x => ψ (x % m))).card =
      (n / m) * ((Finset.range m).filter ψ).card := by
  have hn : n = m * (n / m) := (Nat.mul_div_cancel' hmn).symm
  have key : ((Finset.range n).filter (fun x => ψ (x % m))).card =
      (((Finset.range m).filter ψ) ×ˢ (Finset.range (n / m))).card := by
    refine Finset.card_bij (fun x _ => (x % m, x / m)) ?_ ?_ ?_
    · intro x hx
      rw [Finset.mem_filter] at hx
      obtain ⟨hxn, hψ⟩ := hx
      rw [Finset.mem_range] at hxn
      rw [Finset.mem_product]
      refine ⟨?_, ?_⟩
      · rw [Finset.mem_filter]
        exact ⟨Finset.mem_range.mpr (Nat.mod_lt x hm), hψ⟩
      · rw [Finset.mem_range, Nat.div_lt_iff_lt_mul hm]
        calc x < n := hxn
          _ = m * (n / m) := hn
          _ = (n / m) * m := by rw [Nat.mul_comm]
    · intro a ha b hb h
      simp only [Prod.mk.injEq] at h
      obtain ⟨h1, h2⟩ := h
      calc a = m * (a / m) + a % m := (Nat.div_add_mod a m).symm
        _ = m * (b / m) + b % m := by rw [h1, h2]
        _ = b := Nat.div_add_mod b m
    · rintro ⟨r, q⟩ hy
      rw [Finset.mem_product] at hy
      obtain ⟨hy1, hy2⟩ := hy
      rw [Finset.mem_filter, Finset.mem_range] at hy1
      obtain ⟨hrlt, hψ⟩ := hy1
      rw [Finset.mem_range] at hy2
      refine ⟨m * q + r, ?_, ?_⟩
      · rw [Finset.mem_filter]
        refine ⟨Finset.mem_range.mpr ?_, ?_⟩
        · calc m * q + r < m * q + m := Nat.add_lt_add_left hrlt _
            _ = m * (q + 1) := by rw [Nat.mul_add, Nat.mul_one]
            _ ≤ m * (n / m) := Nat.mul_le_mul_left m (Nat.succ_le_of_lt hy2)
            _ = n := hn.symm
        · rw [Nat.mul_add_mod, Nat.mod_eq_of_lt hrlt]
          exact hψ
      · rw [Nat.mul_add_mod, Nat.mod_eq_of_lt hrlt, Nat.mul_add_div hm,
            Nat.div_eq_of_lt hrlt, Nat.add_zero]
  rw [key, Finset.card_product, Finset.card_range, Nat.mul_comm]

/-- `p ^ e ∣ x ^ 2 ↔ p ^ ((e+1)/2) ∣ x` for a prime `p`. -/
lemma pow_dvd_sq_iff (p e x : ℕ) (hp : p.Prime) :
    p ^ e ∣ x ^ 2 ↔ p ^ ((e + 1) / 2) ∣ x := by
  haveI : Fact p.Prime := ⟨hp⟩
  constructor
  · intro h
    by_cases hx : x = 0
    · simp [hx]
    · have hx2 : x ^ 2 ≠ 0 := pow_ne_zero _ hx
      have h1 : e ≤ padicValNat p (x ^ 2) := (padicValNat_dvd_iff_le hx2).mp h
      rw [padicValNat.pow] at h1
      have h2 : (e + 1) / 2 ≤ padicValNat p x := by omega
      exact (padicValNat_dvd_iff_le hx).mpr h2
  · intro h
    obtain ⟨y, rfl⟩ := h
    rw [mul_pow, ← pow_mul]
    exact dvd_mul_of_dvd_left (Nat.pow_dvd_pow p (by omega : e ≤ (e + 1) / 2 * 2)) _

/-- Number of `x < p^e` with `p^e ∣ x^2` (roots of `x^2 = 0` in `ZMod (p^e)`). -/
lemma card_filter_range_sq_dvd_prime_pow (p e : ℕ) (hp : p.Prime) (he : 1 ≤ e) :
    ((Finset.range (p ^ e)).filter (fun x => p ^ e ∣ x ^ 2)).card = p ^ (e / 2) := by
  have hfil : ((Finset.range (p ^ e)).filter (fun x => p ^ e ∣ x ^ 2))
      = ((Finset.range (p ^ e)).filter (fun x => p ^ ((e + 1) / 2) ∣ x)) := by
    apply Finset.filter_congr
    intro x _
    exact pow_dvd_sq_iff p e x hp
  rw [hfil, card_filter_range_dvd (p ^ e) (p ^ ((e + 1) / 2)) (pow_pos hp.pos _)
        (Nat.pow_dvd_pow p (by omega))]
  rw [Nat.pow_div (by omega : (e + 1) / 2 ≤ e) hp.pos,
      show e - (e + 1) / 2 = e / 2 by omega]

/-- Bridge between `Set.ncard` in `ZMod n` and counting natural representatives. -/
lemma ncard_zmod_eq_range {n : ℕ} [NeZero n] (ψ : ZMod n → Prop) [DecidablePred ψ] :
    ({x : ZMod n | ψ x}.ncard) =
      ((Finset.range n).filter (fun r : ℕ => ψ (r : ZMod n))).card := by
  have h := Commons.Data.ZMod.range_card_eq_subtype n ψ
  rw [h]
  exact (Set.fintypeCard_eq_ncard ({x : ZMod n | ψ x})).symm

/-- `gcd (p^c * u) (p^j) = p^(min c j)` when `p ∤ u`. -/
lemma gcd_prime_pow_mul (p u j c : ℕ) (hp : p.Prime) (hu : ¬ p ∣ u) :
    (p ^ c * u).gcd (p ^ j) = p ^ min c j := by
  have hcu : u.Coprime p := ((Nat.Prime.coprime_iff_not_dvd hp).mpr hu).symm
  rcases le_total c j with h | h
  · rw [min_eq_left h]
    have hpj : p ^ j = p ^ c * p ^ (j - c) := by
      rw [← pow_add]; congr 1; omega
    rw [hpj, Nat.gcd_mul_left,
        Nat.Coprime.gcd_eq_one (Nat.Coprime.pow_right (j - c) hcu), mul_one]
  · rw [min_eq_right h]
    have hpc : p ^ c * u = p ^ j * (p ^ (c - j) * u) := by
      have h1 : p ^ c = p ^ j * p ^ (c - j) := by rw [← pow_add]; congr 1; omega
      rw [h1, mul_assoc]
    rw [hpc, Nat.gcd_eq_right (dvd_mul_right (p ^ j) (p ^ (c - j) * u))]

/-- `p^e ∣ p^a * W ↔ p^(e-a) ∣ W` for a prime `p` and `a ≤ e`. -/
lemma prime_pow_dvd_mul_iff {p a e W : ℕ} (ha : a ≤ e) (hp : p.Prime) :
    p ^ e ∣ p ^ a * W ↔ p ^ (e - a) ∣ W := by
  constructor
  · intro h
    have hpe : p ^ e = p ^ a * p ^ (e - a) := by rw [← pow_add]; congr 1; omega
    rw [hpe] at h
    exact (Nat.mul_dvd_mul_iff_left (pow_pos hp.pos a)).mp h
  · intro h
    obtain ⟨t, ht⟩ := h
    refine ⟨t, ?_⟩
    rw [ht, ← mul_assoc, ← pow_add, Nat.add_sub_of_le ha]

/-- Multiplying the roots of `γ^2 = -1` by a unit `v` gives the roots of `α^2 = -v^2`. -/
lemma ncard_sq_eq_neg_sq_of_unit {n : ℕ} (v : (ZMod n)ˣ) :
    ({α : ZMod n | α ^ 2 = -((v : ZMod n)) ^ 2}.ncard) =
      ({γ : ZMod n | γ ^ 2 = -1}.ncard) := by
  have hinj : Function.Injective (fun γ : ZMod n => (v : ZMod n) * γ) :=
    v.isUnit.mul_right_injective
  have himg : (fun γ : ZMod n => (v : ZMod n) * γ) '' {γ : ZMod n | γ ^ 2 = -1}
      = {α : ZMod n | α ^ 2 = -((v : ZMod n)) ^ 2} := by
    ext α
    constructor
    · rintro ⟨γ, hγ, rfl⟩
      change ((v : ZMod n) * γ) ^ 2 = -((v : ZMod n)) ^ 2
      rw [mul_pow, hγ]; ring
    · intro hα
      change α ^ 2 = -((v : ZMod n)) ^ 2 at hα
      refine ⟨(↑v⁻¹ : ZMod n) * α, ?_, ?_⟩
      · change ((↑v⁻¹ : ZMod n) * α) ^ 2 = -1
        calc ((↑v⁻¹ : ZMod n) * α) ^ 2
              = (↑v⁻¹ : ZMod n) ^ 2 * α ^ 2 := by ring
          _ = (↑v⁻¹ : ZMod n) ^ 2 * (-((v : ZMod n)) ^ 2) := by rw [hα]
          _ = -((↑v⁻¹ : ZMod n) * (v : ZMod n)) ^ 2 := by ring
          _ = -(1 : ZMod n) ^ 2 := by rw [Units.inv_mul]
          _ = -1 := by ring
      · change (v : ZMod n) * ((↑v⁻¹ : ZMod n) * α) = α
        rw [← mul_assoc, Units.mul_inv, one_mul]
  rw [← himg, Set.ncard_image_of_injective _ hinj]

/-- Same, for a natural number whose image in `ZMod n` is a unit. -/
lemma ncard_sq_eq_neg_sq_of_isUnit {n u : ℕ} (hu : IsUnit (u : ZMod n)) :
    ({α : ZMod n | α ^ 2 = -((u : ZMod n)) ^ 2}.ncard) =
      ({γ : ZMod n | γ ^ 2 = -1}.ncard) := by
  have h := ncard_sq_eq_neg_sq_of_unit hu.unit
  rwa [hu.unit_spec] at h

/-- `(x : ZMod n)^2 + (b : ZMod n)^2 = 0 ↔ n ∣ x^2 + b^2`. -/
lemma zmod_sq_add_sq_eq_zero_iff {n b x : ℕ} [NeZero n] :
    ((x : ZMod n) ^ 2 + (b : ZMod n) ^ 2 = 0) ↔ n ∣ x ^ 2 + b ^ 2 := by
  rw [← Nat.cast_pow, ← Nat.cast_pow, ← Nat.cast_add, ZMod.natCast_eq_zero_iff]

/-- `(x : ZMod n)^2 = -1 ↔ n ∣ x^2 + 1`. -/
lemma zmod_sq_eq_neg_one_iff {n x : ℕ} [NeZero n] :
    ((x : ZMod n) ^ 2 = -1) ↔ n ∣ x ^ 2 + 1 := by
  rw [eq_neg_iff_add_eq_zero, ← Nat.cast_pow, ← Nat.cast_one, ← Nat.cast_add,
      ZMod.natCast_eq_zero_iff]

/-! ## The reduction in the non-degenerate case -/

/-- Counting roots of `α^2 + b^2 = 0` in `ZMod (p^e)` when `b = p^c u` with `2c < e`:
the solutions are exactly `p^c u γ` for `γ` ranging over the square roots of `-1`
modulo `p^(e-2c)`, and each such `γ` has `p^c` lifts. -/
lemma ncard_sq_add_sq_prime_pow_reduction {p e c u : ℕ} (hp : p.Prime) (_he : 1 ≤ e)
    (hu : ¬ p ∣ u) (h2c : 2 * c < e) :
    ({α : ZMod (p ^ e) | α ^ 2 + ((p ^ c * u : ℕ) : ZMod (p ^ e)) ^ 2 = 0}.ncard) =
      p ^ c * ({γ : ZMod (p ^ (e - 2 * c)) | γ ^ 2 = -1}.ncard) := by
  haveI : Fact p.Prime := ⟨hp⟩
  have hp0 : 0 < p := hp.pos
  haveI : NeZero (p ^ e) := ⟨(pow_pos hp0 e).ne'⟩
  haveI : NeZero (p ^ (e - 2 * c)) := ⟨(pow_pos hp0 _).ne'⟩
  have h2ce : 2 * c ≤ e := le_of_lt h2c
  -- convert the left-hand side to a count of natural representatives
  have hS : ({α : ZMod (p ^ e) | α ^ 2 + ((p ^ c * u : ℕ) : ZMod (p ^ e)) ^ 2 = 0}.ncard) =
      ((Finset.range (p ^ e)).filter (fun x => p ^ e ∣ x ^ 2 + (p ^ c * u) ^ 2)).card := by
    rw [ncard_zmod_eq_range (n := p ^ e)
      (ψ := fun α : ZMod (p ^ e) => α ^ 2 + ((p ^ c * u : ℕ) : ZMod (p ^ e)) ^ 2 = 0)]
    exact congrArg Finset.card
      (Finset.filter_congr (fun r _ => zmod_sq_add_sq_eq_zero_iff (n := p ^ e) (b := p ^ c * u) (x := r)))
  set A := (Finset.range (p ^ e)).filter (fun x => p ^ e ∣ x ^ 2 + (p ^ c * u) ^ 2) with hA
  set B := (Finset.range (p ^ (e - c))).filter (fun y => p ^ (e - 2 * c) ∣ y ^ 2 + u ^ 2) with hB
  -- every element of `A` is divisible by `p^c`
  have hA_dvd : ∀ x ∈ A, p ^ c ∣ x := by
    intro x hx
    rw [hA, Finset.mem_filter] at hx
    obtain ⟨-, hxP⟩ := hx
    have hbu : (p ^ c * u) ^ 2 = p ^ (2 * c) * u ^ 2 := by
      rw [mul_pow, ← pow_mul, show c * 2 = 2 * c by ring]
    have h2 : p ^ (2 * c) ∣ x ^ 2 := by
      have h1 : p ^ (2 * c) ∣ x ^ 2 + (p ^ c * u) ^ 2 :=
        dvd_trans (Nat.pow_dvd_pow p h2ce) hxP
      have hb2 : p ^ (2 * c) ∣ (p ^ c * u) ^ 2 := by rw [hbu]; exact dvd_mul_right _ _
      have hsub := Nat.dvd_sub h1 hb2
      rwa [Nat.add_sub_cancel] at hsub
    have h3 := (pow_dvd_sq_iff p (2 * c) x hp).mp h2
    rwa [show (2 * c + 1) / 2 = c by omega] at h3
  -- the reduction `x ↦ x / p^c` is a bijection `A → B`
  have hAB : A.card = B.card := by
    refine Finset.card_bij (fun x _ => x / p ^ c) ?_ ?_ ?_
    · intro x hx
      have hpcx : p ^ c ∣ x := hA_dvd x hx
      rw [hA, Finset.mem_filter, Finset.mem_range] at hx
      obtain ⟨hxlt, hxP⟩ := hx
      rw [hB, Finset.mem_filter, Finset.mem_range]
      refine ⟨?_, ?_⟩
      · rw [Nat.div_lt_iff_lt_mul (pow_pos hp0 c)]
        calc x < p ^ e := hxlt
          _ = p ^ (e - c) * p ^ c := by rw [← pow_add]; congr 1; omega
      · have hx2 : x ^ 2 + (p ^ c * u) ^ 2 = p ^ (2 * c) * ((x / p ^ c) ^ 2 + u ^ 2) := by
          have hxc : x ^ 2 = p ^ (2 * c) * (x / p ^ c) ^ 2 := by
            conv_lhs => rw [(Nat.mul_div_cancel' hpcx).symm]
            rw [mul_pow, ← pow_mul, show c * 2 = 2 * c by ring]
          have hbu : (p ^ c * u) ^ 2 = p ^ (2 * c) * u ^ 2 := by
            rw [mul_pow, ← pow_mul, show c * 2 = 2 * c by ring]
          rw [hxc, hbu]; ring
        rw [hx2] at hxP
        exact (prime_pow_dvd_mul_iff (p := p) (a := 2 * c) (e := e) h2ce hp).mp hxP
    · intro a ha b' hb' hab
      rw [← Nat.mul_div_cancel' (hA_dvd a ha), ← Nat.mul_div_cancel' (hA_dvd b' hb'), hab]
    · intro y hy
      rw [hB, Finset.mem_filter, Finset.mem_range] at hy
      obtain ⟨hylt, hyP⟩ := hy
      refine ⟨p ^ c * y, ?_, ?_⟩
      · rw [hA, Finset.mem_filter, Finset.mem_range]
        refine ⟨?_, ?_⟩
        · calc p ^ c * y < p ^ c * p ^ (e - c) := Nat.mul_lt_mul_of_pos_left hylt (pow_pos hp0 c)
            _ = p ^ e := by rw [← pow_add]; congr 1; omega
        · have hy2 : (p ^ c * y) ^ 2 + (p ^ c * u) ^ 2 = p ^ (2 * c) * (y ^ 2 + u ^ 2) := by
            have hxy : (p ^ c * y) ^ 2 = p ^ (2 * c) * y ^ 2 := by
              rw [mul_pow, ← pow_mul, show c * 2 = 2 * c by ring]
            have hbu : (p ^ c * u) ^ 2 = p ^ (2 * c) * u ^ 2 := by
              rw [mul_pow, ← pow_mul, show c * 2 = 2 * c by ring]
            rw [hxy, hbu]; ring
          rw [hy2]
          exact (prime_pow_dvd_mul_iff (p := p) (a := 2 * c) (e := e) h2ce hp).mpr hyP
      · rw [Nat.mul_div_right _ (pow_pos hp0 c)]
  -- replace `y^2` by `(y % p^(e-2c))^2` so that the fiber-counting lemma applies
  have hBmod : B = (Finset.range (p ^ (e - c))).filter
      (fun y => p ^ (e - 2 * c) ∣ (y % p ^ (e - 2 * c)) ^ 2 + u ^ 2) := by
    rw [hB]
    apply Finset.filter_congr
    intro y _
    have hmod : y ^ 2 + u ^ 2 ≡ (y % p ^ (e - 2 * c)) ^ 2 + u ^ 2 [MOD p ^ (e - 2 * c)] :=
      (Nat.ModEq.pow 2 (Nat.mod_modEq y (p ^ (e - 2 * c))).symm).add_right (u ^ 2)
    rw [← Nat.modEq_zero_iff_dvd, ← Nat.modEq_zero_iff_dvd]
    exact ⟨fun hh => hmod.symm.trans hh, fun hh => hmod.trans hh⟩
  have hBcard : B.card = p ^ c *
      ((Finset.range (p ^ (e - 2 * c))).filter (fun r => p ^ (e - 2 * c) ∣ r ^ 2 + u ^ 2)).card := by
    rw [hBmod]
    rw [card_filter_range_mod (p ^ (e - 2 * c)) (p ^ (e - c)) (pow_pos hp0 _)
          (Nat.pow_dvd_pow p (by omega)) (fun r => p ^ (e - 2 * c) ∣ r ^ 2 + u ^ 2)]
    rw [Nat.pow_div (by omega : e - 2 * c ≤ e - c) hp0,
        show e - c - (e - 2 * c) = c by omega]
  -- identify the inner count with the number of square roots of `-1`
  have hcoset : ((Finset.range (p ^ (e - 2 * c))).filter (fun r => p ^ (e - 2 * c) ∣ r ^ 2 + u ^ 2)).card =
      ({γ : ZMod (p ^ (e - 2 * c)) | γ ^ 2 = -1}.ncard) := by
    have h1 : ((Finset.range (p ^ (e - 2 * c))).filter
          (fun r => p ^ (e - 2 * c) ∣ r ^ 2 + u ^ 2)).card =
        ({α : ZMod (p ^ (e - 2 * c)) | α ^ 2 + (u : ZMod (p ^ (e - 2 * c))) ^ 2 = 0}.ncard) := by
      rw [ncard_zmod_eq_range (n := p ^ (e - 2 * c))
        (ψ := fun α : ZMod (p ^ (e - 2 * c)) => α ^ 2 + (u : ZMod (p ^ (e - 2 * c))) ^ 2 = 0)]
      exact congrArg Finset.card (Finset.filter_congr (fun r _ =>
        (zmod_sq_add_sq_eq_zero_iff (n := p ^ (e - 2 * c)) (b := u) (x := r)).symm))
    rw [h1]
    rw [show ({α : ZMod (p ^ (e - 2 * c)) | α ^ 2 + (u : ZMod (p ^ (e - 2 * c))) ^ 2 = 0} : Set (ZMod (p ^ (e - 2 * c))))
          = {α : ZMod (p ^ (e - 2 * c)) | α ^ 2 = -((u : ZMod (p ^ (e - 2 * c)))) ^ 2} from by
            ext α; rw [Set.mem_ofPred_eq, Set.mem_ofPred_eq, add_eq_zero_iff_eq_neg]]
    have hcu : u.Coprime p := ((Nat.Prime.coprime_iff_not_dvd hp).mpr hu).symm
    exact ncard_sq_eq_neg_sq_of_isUnit (by rw [ZMod.isUnit_iff_coprime]; exact hcu.pow_right (e - 2 * c))
  calc ({α : ZMod (p ^ e) | α ^ 2 + ((p ^ c * u : ℕ) : ZMod (p ^ e)) ^ 2 = 0}.ncard)
        = A.card := hS
    _ = B.card := hAB
    _ = p ^ c * ((Finset.range (p ^ (e - 2 * c))).filter (fun r => p ^ (e - 2 * c) ∣ r ^ 2 + u ^ 2)).card := hBcard
    _ = p ^ c * ({γ : ZMod (p ^ (e - 2 * c)) | γ ^ 2 = -1}.ncard) := by rw [hcoset]

/-- The non-degenerate case of the main count: `p^e ∤ b^2`. -/
lemma sq_sum_sq_root_count_prime_pow_not_dvd {p e b : ℕ} (hp : p.Prime) (he : 1 ≤ e)
    (hb : ¬ p ^ e ∣ b ^ 2) :
    ({α : ZMod (p ^ e) | α ^ 2 + (b : ZMod (p ^ e)) ^ 2 = 0}.ncard) =
      Nat.gcd b (p ^ (e / 2)) *
        ({α : ZMod (p ^ e / Nat.gcd (b ^ 2) (p ^ e)) | α ^ 2 = -1}.ncard) := by
  haveI : Fact p.Prime := ⟨hp⟩
  have hp0 : 0 < p := hp.pos
  have hb0 : b ≠ 0 := by rintro rfl; exact hb (by simp)
  obtain ⟨hbfac, hu_notdvd⟩ := Commons.Data.Nat.padicValNat_factorization (p := p) (d := b) hb0
  have hb2fac : b ^ 2 = p ^ (2 * padicValNat p b) * (b / p ^ (padicValNat p b)) ^ 2 := by
    conv_lhs => rw [hbfac]
    rw [mul_pow, ← pow_mul, show padicValNat p b * 2 = 2 * padicValNat p b by ring]
  have h2c : 2 * padicValNat p b < e := by
    by_contra hle
    rw [not_lt] at hle
    exact hb (by rw [hb2fac]; exact dvd_mul_of_dvd_left (Nat.pow_dvd_pow p hle) _)
  have hce : padicValNat p b ≤ e / 2 := by omega
  have hu2_notdvd : ¬ p ∣ (b / p ^ (padicValNat p b)) ^ 2 :=
    fun h => hu_notdvd (hp.dvd_of_dvd_pow h)
  have hgcdb : Nat.gcd b (p ^ (e / 2)) = p ^ (padicValNat p b) := by
    conv_lhs => rw [hbfac]
    rw [gcd_prime_pow_mul p (b / p ^ (padicValNat p b)) (e / 2) (padicValNat p b) hp
          hu_notdvd, min_eq_left hce]
  have hgcdb2 : Nat.gcd (b ^ 2) (p ^ e) = p ^ (2 * padicValNat p b) := by
    conv_lhs => rw [hb2fac]
    rw [gcd_prime_pow_mul p ((b / p ^ (padicValNat p b)) ^ 2) e (2 * padicValNat p b) hp
          hu2_notdvd, min_eq_left (le_of_lt h2c)]
  have hM : p ^ e / Nat.gcd (b ^ 2) (p ^ e) = p ^ (e - 2 * padicValNat p b) := by
    rw [hgcdb2, Nat.pow_div (le_of_lt h2c) hp0]
  have hLHS : ({α : ZMod (p ^ e) | α ^ 2 + (b : ZMod (p ^ e)) ^ 2 = 0}.ncard) =
      p ^ (padicValNat p b) * ({γ : ZMod (p ^ (e - 2 * padicValNat p b)) | γ ^ 2 = -1}.ncard) := by
    have key := ncard_sq_add_sq_prime_pow_reduction (p := p) (e := e)
      (c := padicValNat p b) (u := b / p ^ (padicValNat p b)) hp he hu_notdvd h2c
    rw [show (p ^ (padicValNat p b) * (b / p ^ (padicValNat p b)) : ℕ) = b from hbfac.symm] at key
    exact key
  rw [hLHS, hgcdb, hM]

/-! ## The main theorem -/

lemma sq_sum_sq_root_count_prime_pow {p e b : ℕ} (hp : p.Prime) (he : 1 ≤ e) :
    ({α : ZMod (p ^ e) | α ^ 2 + (b : ZMod (p ^ e)) ^ 2 = 0}.ncard) =
      Nat.gcd b (p ^ (e / 2)) *
        ({α : ZMod (p ^ e / Nat.gcd (b ^ 2) (p ^ e)) | α ^ 2 = -1}.ncard) := by
  by_cases hb : p ^ e ∣ b ^ 2
  · haveI : NeZero (p ^ e) := ⟨(pow_pos hp.pos e).ne'⟩
    have hb2 : ((b : ZMod (p ^ e)) ^ 2 = 0) := by
      rw [← Nat.cast_pow, ZMod.natCast_eq_zero_iff]; exact hb
    have hset : {α : ZMod (p ^ e) | α ^ 2 + (b : ZMod (p ^ e)) ^ 2 = 0}
        = {α : ZMod (p ^ e) | α ^ 2 = 0} := by
      ext α; rw [Set.mem_ofPred_eq, Set.mem_ofPred_eq, hb2, add_zero]
    rw [hset]
    have hL : ({α : ZMod (p ^ e) | α ^ 2 = 0}.ncard) = p ^ (e / 2) := by
      have h1 : ({α : ZMod (p ^ e) | α ^ 2 = 0}.ncard) =
          ((Finset.range (p ^ e)).filter (fun r => p ^ e ∣ r ^ 2)).card := by
        rw [ncard_zmod_eq_range (n := p ^ e) (ψ := fun α : ZMod (p ^ e) => α ^ 2 = 0)]
        exact congrArg Finset.card (Finset.filter_congr (fun r _ => by
          rw [← Nat.cast_pow, ZMod.natCast_eq_zero_iff]))
      rw [h1, card_filter_range_sq_dvd_prime_pow p e hp he]
    rw [hL]
    have hgb : Nat.gcd b (p ^ (e / 2)) = p ^ (e / 2) := by
      apply Nat.gcd_eq_right
      exact dvd_trans (Nat.pow_dvd_pow p (by omega)) ((pow_dvd_sq_iff p e b hp).mp hb)
    have hM1 : p ^ e / Nat.gcd (b ^ 2) (p ^ e) = 1 := by
      rw [Nat.gcd_eq_right hb, Nat.div_self (pow_pos hp.pos e)]
    have hR1 : ({α : ZMod (p ^ e / Nat.gcd (b ^ 2) (p ^ e)) | α ^ 2 = -1}.ncard) = 1 := by
      rw [hM1]
      have : ({α : ZMod 1 | α ^ 2 = -1} : Set (ZMod 1)) = Set.univ := by
        ext α
        simp only [Set.mem_ofPred_eq, Set.mem_univ, iff_true]
        exact Subsingleton.elim _ _
      rw [this, Set.ncard_univ, Nat.card_zmod]
    rw [hgb, hR1, mul_one]
  · exact sq_sum_sq_root_count_prime_pow_not_dvd hp he hb

end Commons.NumberTheory.FriedlanderIwaniec