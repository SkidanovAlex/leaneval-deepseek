import Mathlib
import Submission.Work.FIArea7.FIsymbols
import Submission.Work.FIArea7.KronTwo
import Submission.Work.FIArea7.KronTwoAux
import Submission.Work.FIArea7.kronCore
import Submission.Work.FIArea7.kronEight
import Submission.Work.FIArea7.reflBook

set_option autoImplicit false

namespace Work.FIArea7

/-! ## 0. Local norm facts

`gnorm` written in coordinates, together with the standard consequences of a squarefree norm.
(These are copies of `Work.FIArea1.gnorm_int`, `gnorm_coords`, `gnorm_mul`, `gnorm_intCast`,
`sq_dvd_gnorm_of_dvd_coords` and `coprime_coords_of_sqfree`, kept here so that this module is
self-contained.) -/

lemma gnorm_int' (z : GaussianInt) : (Work.FIPlan.gnorm z : ℤ) = z.re ^ 2 + z.im ^ 2 := by
  have hnorm : z.norm = z.re ^ 2 + z.im ^ 2 := by rw [Zsqrtd.norm_def]; ring
  rw [Work.FIPlan.gnorm, hnorm,
    Int.natAbs_of_nonneg (by positivity : (0 : ℤ) ≤ z.re ^ 2 + z.im ^ 2)]

lemma gnorm_coords' (z : GaussianInt) :
    Work.FIPlan.gnorm z = z.re.natAbs ^ 2 + z.im.natAbs ^ 2 := by
  apply Nat.cast_injective (R := ℤ)
  rw [gnorm_int', Nat.cast_add, Nat.cast_pow, Nat.cast_pow, Int.natAbs_sq, Int.natAbs_sq]

lemma gnorm_mul' (w z : GaussianInt) :
    Work.FIPlan.gnorm (w * z) = Work.FIPlan.gnorm w * Work.FIPlan.gnorm z := by
  simp only [Work.FIPlan.gnorm, Zsqrtd.norm_mul, Int.natAbs_mul]

lemma gnorm_intCast' (n : ℤ) : Work.FIPlan.gnorm ((n : ℤ) : GaussianInt) = n.natAbs ^ 2 := by
  rw [gnorm_coords']; simp

lemma sq_dvd_gnorm_of_dvd_coords' {z : GaussianInt} {p : ℤ} (h1 : p ∣ z.re) (h2 : p ∣ z.im) :
    p.natAbs ^ 2 ∣ Work.FIPlan.gnorm z := by
  obtain ⟨a, ha⟩ := h1
  obtain ⟨b, hb⟩ := h2
  have hz : z = (p : GaussianInt) * (⟨a, b⟩ : GaussianInt) := by
    ext <;> simp [ha, hb]
  rw [hz, gnorm_mul', gnorm_intCast']
  exact dvd_mul_right _ _

/-- A squarefree `|z|²` forces the coordinates of `z` to be coprime (the paper's `(r,s) = 1`). -/
lemma coprime_coords_of_sqfree' {z : GaussianInt} (h : Squarefree (Work.FIPlan.gnorm z)) :
    Nat.Coprime z.re.natAbs z.im.natAbs := by
  rw [Nat.coprime_iff_gcd_eq_one]
  by_contra hne
  obtain ⟨p, hp, hpd⟩ := Nat.exists_prime_and_dvd hne
  have h1 : p ∣ z.re.natAbs := hpd.trans (Nat.gcd_dvd_left _ _)
  have h2 : p ∣ z.im.natAbs := hpd.trans (Nat.gcd_dvd_right _ _)
  have h1' : (p : ℤ) ∣ z.re := Int.natCast_dvd.mpr h1
  have h2' : (p : ℤ) ∣ z.im := Int.natCast_dvd.mpr h2
  have hsq : p ^ 2 ∣ Work.FIPlan.gnorm z := sq_dvd_gnorm_of_dvd_coords' h1' h2'
  exact (Nat.squarefree_iff_prime_squarefree.mp h p hp) (by rwa [pow_two] at hsq)


/-- `↑a.natAbs = -a` for `a ≤ 0`. -/
lemma natAbs_of_nonpos' {a : ℤ} (h : a ≤ 0) : (↑a.natAbs : ℤ) = -a := by
  rw [← Int.natAbs_neg a, Int.natAbs_of_nonneg (by linarith : (0 : ℤ) ≤ -a)]

/-! ## 1. The arithmetic statement in rational coordinates

This is the whole number-theoretic content of the lemma, with the Gaussian integers translated
into the pairs `(rᵢ, sᵢ)`.  It is proved by splitting `rᵢ = g·uᵢ` with `g = (r₁,r₂)`:

* `reflBook` splits `J(Re(z̄₁z₂)||Δ|)·J(|z₁|²||Δ|)` into `J(s₁s₂|g)·J(u₁u₂|D')`,
* `kronCore` evaluates `J(u₁u₂|D')·χ₂(u₁u₂)^{ν₂|D'|} = (s₁|u₁)(s₂|u₂)` (the reflection identity in
  the Kronecker convention — this is where `u₁ ≡ u₂ (mod 4)`, i.e. `mod 4` instead of `mod 8`, is
  used),
* `kronEight` shows `χ₂(Re(z̄₁z₂))·χ₂(|z₁|²) = χ₂(u₁u₂)`,

and `ν₂(|Δ|) = ν₂(|D'|)` because `g` is odd. -/
theorem reflArith {r1 r2 : ℕ} {s1 s2 : ℤ}
    (hr1 : Odd r1) (hr2 : Odd r2) (hs1 : Even s1) (hs2 : Even s2)
    (hr1s1 : r1.Coprime s1.natAbs) (hr2s2 : r2.Coprime s2.natAbs)
    (h4r : (r1 : ℤ) ≡ (r2 : ℤ) [ZMOD 4]) (h4s : s1 ≡ s2 [ZMOD 4])
    (hB : (((r1 : ℤ) ^ 2 + s1 ^ 2).natAbs).Coprime
      (((r1 : ℤ) * s2 - (r2 : ℤ) * s1).natAbs))
    (hD : (r1 : ℤ) * s2 - (r2 : ℤ) * s1 ≠ 0) :
    jacobiSym ((r1 : ℤ) * (r2 : ℤ) + s1 * s2)
        (((r1 : ℤ) * s2 - (r2 : ℤ) * s1).natAbs)
      * jacobiSym ((((r1 : ℤ) ^ 2 + s1 ^ 2).natAbs : ℕ) : ℤ)
        (((r1 : ℤ) * s2 - (r2 : ℤ) * s1).natAbs)
    = (kronTwo ((r1 : ℤ) * (r2 : ℤ) + s1 * s2)
        * kronTwo ((((r1 : ℤ) ^ 2 + s1 ^ 2).natAbs : ℕ) : ℤ))
        ^ ((((r1 : ℤ) * s2 - (r2 : ℤ) * s1).natAbs).factorization 2)
      * (jacobiSym s1 r1 * jacobiSym s2 r2) := by
  have hr1pos : 0 < r1 := by obtain ⟨k1, hk1⟩ := hr1; rw [hk1]; omega
  have hr2pos : 0 < r2 := by obtain ⟨k2, hk2⟩ := hr2; rw [hk2]; omega
  set g : ℕ := r1.gcd r2 with hg
  have hgdv1 : g ∣ r1 := by rw [hg]; exact Nat.gcd_dvd_left _ _
  have hgdv2 : g ∣ r2 := by rw [hg]; exact Nat.gcd_dvd_right _ _
  have hgpos : 0 < g := Nat.pos_of_dvd_of_pos hgdv1 hr1pos
  have hgpos' : 0 < r1.gcd r2 := by rw [← hg]; exact hgpos
  have hgne : g ≠ 0 := hgpos.ne'
  set u1 : ℕ := r1 / g with hu1
  set u2 : ℕ := r2 / g with hu2
  have hu1' : g * u1 = r1 := by rw [hu1, Nat.mul_div_cancel' hgdv1]
  have hu2' : g * u2 = r2 := by rw [hu2, Nat.mul_div_cancel' hgdv2]
  have hune1 : u1 ≠ 0 := by intro h; rw [h, mul_zero] at hu1'; omega
  have hune2 : u2 ≠ 0 := by intro h; rw [h, mul_zero] at hu2'; omega
  have hgu1odd : Odd (g * u1) := by rw [hu1']; exact hr1
  have hgu2odd : Odd (g * u2) := by rw [hu2']; exact hr2
  have hgodd : Odd g := (Nat.odd_mul.mp hgu1odd).1
  have hu1odd : Odd u1 := (Nat.odd_mul.mp hgu1odd).2
  have hu2odd : Odd u2 := (Nat.odd_mul.mp hgu2odd).2
  have hcop : u1.Coprime u2 := by
    rw [hu1, hu2, hg]
    exact Nat.coprime_div_gcd_div_gcd hgpos'
  have hu1dv : u1 ∣ r1 := ⟨g, by rw [mul_comm, hu1']⟩
  have hu2dv : u2 ∣ r2 := ⟨g, by rw [mul_comm, hu2']⟩
  have hgs1 : g.Coprime s1.natAbs := hr1s1.coprime_dvd_left hgdv1
  have hu1s1 : u1.Coprime s1.natAbs := hr1s1.coprime_dvd_left hu1dv
  have hu2s2 : u2.Coprime s2.natAbs := hr2s2.coprime_dvd_left hu2dv
  have hrc1 : (r1 : ℤ) = (g : ℤ) * (u1 : ℤ) := by rw [← hu1']; push_cast; ring
  have hrc2 : (r2 : ℤ) = (g : ℤ) * (u2 : ℤ) := by rw [← hu2']; push_cast; ring
  -- the determinant
  set D1 : ℕ := ((u1 : ℤ) * s2 - (u2 : ℤ) * s1).natAbs with hD1
  have hD1ne : (u1 : ℤ) * s2 - (u2 : ℤ) * s1 ≠ 0 := by
    intro h
    have h0 : (r1 : ℤ) * s2 - (r2 : ℤ) * s1
        = (g : ℤ) * ((u1 : ℤ) * s2 - (u2 : ℤ) * s1) := by rw [hrc1, hrc2]; ring
    exact hD (by rw [h0, h, mul_zero])
  have hD1pos : 0 < D1 := by rw [hD1, Int.natAbs_pos]; exact hD1ne
  have hD1ne' : D1 ≠ 0 := hD1pos.ne'
  have hmod : (((r1 : ℤ) * s2 - (r2 : ℤ) * s1).natAbs) = g * D1 := by
    rw [hD1]
    have h0 : (r1 : ℤ) * s2 - (r2 : ℤ) * s1
        = (g : ℤ) * ((u1 : ℤ) * s2 - (u2 : ℤ) * s1) := by rw [hrc1, hrc2]; ring
    rw [h0, Int.natAbs_mul, Int.natAbs_natCast]
  -- the mod-4 hypothesis descends from r's to u's
  have h4u : (u1 : ℤ) ≡ (u2 : ℤ) [ZMOD 4] := by
    have h2g : ¬ (2 : ℕ) ∣ g := by
      rw [← even_iff_two_dvd]; exact (Nat.not_even_iff_odd.mpr hgodd)
    have h4cop : Nat.Coprime 4 g := by
      have := Nat.Coprime.pow_left (n := 2) (m := 2) (k := g) (Nat.coprime_two_left.mpr hgodd)
      simpa using this
    have hgg : IsCoprime (4 : ℤ) (g : ℤ) := by
      rw [Int.isCoprime_iff_gcd_eq_one]
      have hgcd : Int.gcd (4 : ℤ) (g : ℤ) = Nat.gcd 4 g := by
        rw [Int.gcd_eq_natAbs]; norm_num
      rw [hgcd, Nat.coprime_iff_gcd_eq_one.mp h4cop]
    have h1 : (4 : ℤ) ∣ ((g : ℤ) * ((u2 : ℤ) - (u1 : ℤ))) := by
      have h := Int.modEq_iff_dvd.mp h4r
      rw [hrc1, hrc2] at h
      convert h using 1 <;> ring
    have h2 : (4 : ℤ) ∣ ((u2 : ℤ) - (u1 : ℤ)) := hgg.dvd_of_dvd_mul_left h1
    exact Int.modEq_iff_dvd.mpr h2
  -- coprimality of |z1|^2 with the determinant, transported
  have hB1 : (((r1 : ℤ) ^ 2 + s1 ^ 2).natAbs)
      = (((g : ℤ) ^ 2 * (u1 : ℤ) ^ 2 + s1 ^ 2).natAbs) := by
    congr 1; rw [hrc1]; ring
  have hB'' : ((((g : ℤ) ^ 2 * (u1 : ℤ) ^ 2 + s1 ^ 2).natAbs)).Coprime
      (((r1 : ℤ) * s2 - (r2 : ℤ) * s1).natAbs) := by
    rw [← hB1]; exact hB
  have hB' : (((g : ℤ) ^ 2 * (u1 : ℤ) ^ 2 + s1 ^ 2).natAbs).Coprime
      (((u1 : ℤ) * s2 - (u2 : ℤ) * s1).natAbs) := by
    rw [hmod] at hB''
    exact hB''.coprime_dvd_right (dvd_mul_left D1 g)
  -- the three arithmetic inputs
  have hKC : jacobiSym (((u1 * u2 : ℕ) : ℤ)) D1
      * kronTwo (((u1 * u2 : ℕ) : ℤ)) ^ (D1.factorization 2)
      = jacobiSym s1 u1 * jacobiSym s2 u2 :=
    kronCore hu1odd hu2odd hs1 hs2 hcop hu1s1 hu2s2 h4u hD1ne
  have hK8 : kronTwo ((g : ℤ) ^ 2 * (u1 : ℤ) * (u2 : ℤ) + s1 * s2)
      * kronTwo ((g : ℤ) ^ 2 * (u1 : ℤ) ^ 2 + s1 ^ 2)
      = kronTwo ((u1 : ℤ) * (u2 : ℤ)) :=
    kronEight hgodd hu1odd hu2odd hs1 hs2 h4u h4s
  have hRB : jacobiSym ((g : ℤ) ^ 2 * (u1 : ℤ) * (u2 : ℤ) + s1 * s2) (g * D1)
      * jacobiSym ((((g : ℤ) ^ 2 * (u1 : ℤ) ^ 2 + s1 ^ 2).natAbs : ℕ) : ℤ) (g * D1)
      = jacobiSym (s1 * s2) g * jacobiSym (((u1 * u2 : ℕ) : ℤ)) D1 :=
    reflBook hgpos hu1odd hu2odd hcop hgs1 hu1s1 hB' hD1ne
  -- the exponent
  have hfac : (g * D1).factorization 2 = D1.factorization 2 := by
    have h2g : ¬ (2 : ℕ) ∣ g := by
      rw [← even_iff_two_dvd]; exact (Nat.not_even_iff_odd.mpr hgodd)
    rw [Nat.factorization_mul hgne hD1ne', Finsupp.add_apply,
      Nat.factorization_eq_zero_of_not_dvd h2g, zero_add]
  -- splitting the rational symbols at r_i = g u_i
  have hR1 : jacobiSym s1 r1 = jacobiSym s1 g * jacobiSym s1 u1 := by
    rw [← hu1']
    exact jacobiSym.mul_right' s1 hgne hune1
  have hR2 : jacobiSym s2 r2 = jacobiSym s2 g * jacobiSym s2 u2 := by
    rw [← hu2']
    exact jacobiSym.mul_right' s2 hgne hune2
  have hxodd : Odd (((u1 * u2 : ℕ) : ℤ)) := by
    obtain ⟨m, hm⟩ := Nat.odd_mul.mpr ⟨hu1odd, hu2odd⟩
    exact ⟨m, by rw [hm]; push_cast; ring⟩
  have hK2 : kronTwo (((u1 * u2 : ℕ) : ℤ)) ^ (D1.factorization 2)
      * kronTwo (((u1 * u2 : ℕ) : ℤ)) ^ (D1.factorization 2) = 1 := by
    rw [← mul_pow, kronTwo_mul_self_of_odd hxodd, one_pow]
  have hKP : kronTwo (((u1 * u2 : ℕ) : ℤ)) ^ (D1.factorization 2)
      * (jacobiSym s1 u1 * jacobiSym s2 u2) = jacobiSym (((u1 * u2 : ℕ) : ℤ)) D1 := by
    rw [← hKC]
    calc kronTwo (((u1 * u2 : ℕ) : ℤ)) ^ (D1.factorization 2)
          * (jacobiSym (((u1 * u2 : ℕ) : ℤ)) D1
              * kronTwo (((u1 * u2 : ℕ) : ℤ)) ^ (D1.factorization 2))
        = jacobiSym (((u1 * u2 : ℕ) : ℤ)) D1
            * (kronTwo (((u1 * u2 : ℕ) : ℤ)) ^ (D1.factorization 2)
              * kronTwo (((u1 * u2 : ℕ) : ℤ)) ^ (D1.factorization 2)) := by ring
      _ = jacobiSym (((u1 * u2 : ℕ) : ℤ)) D1 := by rw [hK2, mul_one]
  -- the two sides
  have hA : (r1 : ℤ) * (r2 : ℤ) + s1 * s2
      = (g : ℤ) ^ 2 * (u1 : ℤ) * (u2 : ℤ) + s1 * s2 := by rw [hrc1, hrc2]; ring
  have hBv : ((((r1 : ℤ) ^ 2 + s1 ^ 2).natAbs : ℕ) : ℤ)
      = ((((g : ℤ) ^ 2 * (u1 : ℤ) ^ 2 + s1 ^ 2).natAbs : ℕ) : ℤ) := by rw [hB1]
  suffices hmain : jacobiSym ((r1 : ℤ) * (r2 : ℤ) + s1 * s2)
        (((r1 : ℤ) * s2 - (r2 : ℤ) * s1).natAbs)
      * jacobiSym ((((r1 : ℤ) ^ 2 + s1 ^ 2).natAbs : ℕ) : ℤ)
        (((r1 : ℤ) * s2 - (r2 : ℤ) * s1).natAbs)
      = jacobiSym (s1 * s2) g * jacobiSym (((u1 * u2 : ℕ) : ℤ)) D1 by
    rw [hmain]
    rw [hA, hBv, hmod, hfac]
    have hkk : kronTwo ((g : ℤ) ^ 2 * (u1 : ℤ) * (u2 : ℤ) + s1 * s2)
        * kronTwo ((((g : ℤ) ^ 2 * (u1 : ℤ) ^ 2 + s1 ^ 2).natAbs : ℕ) : ℤ)
        = kronTwo (((u1 * u2 : ℕ) : ℤ)) := by
      rw [show ((((g : ℤ) ^ 2 * (u1 : ℤ) ^ 2 + s1 ^ 2).natAbs : ℕ) : ℤ)
            = ((g : ℤ) ^ 2 * (u1 : ℤ) ^ 2 + s1 ^ 2) from
          Int.natAbs_of_nonneg (by positivity)]
      rw [hK8, Nat.cast_mul]
    rw [hkk, hR1, hR2, jacobiSym.mul_left s1 s2 g]
    calc jacobiSym s1 g * jacobiSym s2 g * jacobiSym (((u1 * u2 : ℕ) : ℤ)) D1
        = (jacobiSym s1 g * jacobiSym s2 g)
            * (kronTwo (((u1 * u2 : ℕ) : ℤ)) ^ (D1.factorization 2)
              * (jacobiSym s1 u1 * jacobiSym s2 u2)) := by rw [hKP]
      _ = kronTwo (((u1 * u2 : ℕ) : ℤ)) ^ (D1.factorization 2)
          * (jacobiSym s1 g * jacobiSym s1 u1 * (jacobiSym s2 g * jacobiSym s2 u2)) := by ring
  rw [hA, hBv, hmod]
  exact hRB

/-! ## 2. The Gaussian statement -/

theorem jacobiSym_reflection_mod4 {z1 z2 : GaussianInt}
    (hP1 : Work.FIPlan.IsPrimary z1) (hP2 : Work.FIPlan.IsPrimary z2)
    (hs1 : Squarefree (Work.FIPlan.gnorm z1)) (hs2 : Squarefree (Work.FIPlan.gnorm z2))
    (hc : IsCoprime z1 z2)
    (hcc : IsCoprime ((Work.FIPlan.gnorm z1 : ℕ) : ℤ) ((Work.FIPlan.absDelta z1 z2 : ℕ) : ℤ))
    (h4r : z1.re ≡ z2.re [ZMOD 4]) (h4i : z1.im ≡ z2.im [ZMOD 4])
    (hr : 0 < z1.re * z2.re) (hD : 0 < Work.FIPlan.absDelta z1 z2) :
    jacobiSym (z1.re * z2.re + z1.im * z2.im) (Work.FIPlan.absDelta z1 z2)
        * jacobiSym ((Work.FIPlan.gnorm z1 : ℕ) : ℤ) (Work.FIPlan.absDelta z1 z2)
      = (Work.FIArea7.kronTwo (z1.re * z2.re + z1.im * z2.im)
          * Work.FIArea7.kronTwo ((Work.FIPlan.gnorm z1 : ℕ) : ℤ))
          ^ ((Work.FIPlan.absDelta z1 z2).factorization 2)
        * (jacobiSym z1.im z1.re.natAbs * jacobiSym z2.im z2.re.natAbs) := by
  obtain ⟨hr1odd, hs1even, -⟩ := hP1
  obtain ⟨hr2odd, hs2even, -⟩ := hP2
  have hcop1 : (z1.re.natAbs).Coprime (z1.im.natAbs) := coprime_coords_of_sqfree' hs1
  have hcop2 : (z2.re.natAbs).Coprime (z2.im.natAbs) := coprime_coords_of_sqfree' hs2
  have hr1ne : z1.re ≠ 0 := by
    rintro h; rw [h] at hr1odd; obtain ⟨k, hk⟩ := hr1odd; omega
  have hr2ne : z2.re ≠ 0 := by
    rintro h; rw [h] at hr2odd; obtain ⟨k, hk⟩ := hr2odd; omega
  have hsign : (0 < z1.re ∧ 0 < z2.re) ∨ (z1.re < 0 ∧ z2.re < 0) := by
    rcases lt_trichotomy z1.re 0 with h | h | h
    · rcases lt_trichotomy z2.re 0 with h2 | h2 | h2
      · exact Or.inr ⟨h, h2⟩
      · exfalso; rw [h2, mul_zero] at hr; exact lt_irrefl 0 hr
      · exfalso; exact absurd (mul_neg_of_neg_of_pos h h2) (by linarith)
    · exact absurd h hr1ne
    · rcases lt_trichotomy z2.re 0 with h2 | h2 | h2
      · exfalso; exact absurd (mul_neg_of_pos_of_neg h h2) (by linarith)
      · exfalso; rw [h2, mul_zero] at hr; exact lt_irrefl 0 hr
      · exact Or.inl ⟨h, h2⟩
  have hprod : (z1.re.natAbs : ℤ) * (z2.re.natAbs : ℤ) = z1.re * z2.re := by
    rcases hsign with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · rw [Int.natAbs_of_nonneg (le_of_lt h1), Int.natAbs_of_nonneg (le_of_lt h2)]
    · rw [natAbs_of_nonpos' (le_of_lt h1), natAbs_of_nonpos' (le_of_lt h2)]; ring
  have hsq : (z1.re.natAbs : ℤ) ^ 2 = z1.re ^ 2 := by
    rcases hsign with ⟨h1, _⟩ | ⟨h1, _⟩
    · rw [Int.natAbs_of_nonneg (le_of_lt h1)]
    · rw [natAbs_of_nonpos' (le_of_lt h1)]; ring
  have hr1rn : (z1.re.natAbs : ℤ) = z1.re ∨ (z1.re.natAbs : ℤ) = -z1.re := by
    rcases hsign with ⟨h1, _⟩ | ⟨h1, _⟩
    · exact Or.inl (Int.natAbs_of_nonneg (le_of_lt h1))
    · exact Or.inr (natAbs_of_nonpos' (le_of_lt h1))
  have hr2rn : (z2.re.natAbs : ℤ) = z2.re ∨ (z2.re.natAbs : ℤ) = -z2.re := by
    rcases hsign with ⟨_, h2⟩ | ⟨_, h2⟩
    · exact Or.inl (Int.natAbs_of_nonneg (le_of_lt h2))
    · exact Or.inr (natAbs_of_nonpos' (le_of_lt h2))
  -- the determinant in `|z|`-coordinates
  have hDabs0 : Work.FIPlan.absDelta z1 z2
      = ((z1.re.natAbs : ℤ) * z2.im - (z2.re.natAbs : ℤ) * z1.im).natAbs := by
    have hδ : Work.FIPlan.absDelta z1 z2 = (z1.re * z2.im - z2.re * z1.im).natAbs := by
      rw [Work.FIPlan.absDelta, Work.FIPlan.Delta, im_mul, Zsqrtd.re_star, Zsqrtd.im_star]
      congr 1; ring
    rw [hδ]
    rcases hsign with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · rw [Int.natAbs_of_nonneg (le_of_lt h1), Int.natAbs_of_nonneg (le_of_lt h2)]
    · rw [natAbs_of_nonpos' (le_of_lt h1), natAbs_of_nonpos' (le_of_lt h2)]
      rw [show (-z1.re) * z2.im - (-z2.re) * z1.im = -(z1.re * z2.im - z2.re * z1.im) by ring,
        Int.natAbs_neg]
  have hgn : (Work.FIPlan.gnorm z1 : ℕ)
      = (((z1.re.natAbs : ℤ) ^ 2 + z1.im ^ 2).natAbs) := by
    have h1 : ((z1.re.natAbs : ℤ) ^ 2 + z1.im ^ 2).natAbs
        = z1.re.natAbs ^ 2 + z1.im.natAbs ^ 2 := by
      rw [← Int.natAbs_sq (z1.im)]
      rw [show ((z1.re.natAbs : ℤ) ^ 2 + (z1.im.natAbs : ℤ) ^ 2)
          = ((z1.re.natAbs ^ 2 + z1.im.natAbs ^ 2 : ℕ) : ℤ) by push_cast; ring,
        Int.natAbs_natCast]
    rw [h1, gnorm_coords']
  have hcc' : Nat.Coprime (Work.FIPlan.gnorm z1) (Work.FIPlan.absDelta z1 z2) := by
    have h := Int.isCoprime_iff_gcd_eq_one.mp hcc
    rw [Int.gcd_eq_natAbs] at h
    rw [Nat.coprime_iff_gcd_eq_one]
    simpa using h
  have hB : (((z1.re.natAbs : ℤ) ^ 2 + z1.im ^ 2).natAbs).Coprime
      (((z1.re.natAbs : ℤ) * z2.im - (z2.re.natAbs : ℤ) * z1.im).natAbs) := by
    rw [← hgn, ← hDabs0]
    exact hcc'
  have hD' : (z1.re.natAbs : ℤ) * z2.im - (z2.re.natAbs : ℤ) * z1.im ≠ 0 := by
    intro h
    have h0 : Work.FIPlan.absDelta z1 z2 = 0 := by
      rw [hDabs0, h]; rfl
    omega
  have h4r' : (z1.re.natAbs : ℤ) ≡ (z2.re.natAbs : ℤ) [ZMOD 4] := by
    rcases hsign with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · rw [Int.natAbs_of_nonneg (le_of_lt h1), Int.natAbs_of_nonneg (le_of_lt h2)]
      exact h4r
    · rw [natAbs_of_nonpos' (le_of_lt h1), natAbs_of_nonpos' (le_of_lt h2)]
      rw [Int.modEq_iff_dvd] at h4r ⊢
      rw [show (-z2.re) - (-z1.re) = -(z2.re - z1.re) by ring]
      exact dvd_neg.mpr h4r
  have hmain := reflArith (r1 := z1.re.natAbs) (r2 := z2.re.natAbs) (s1 := z1.im) (s2 := z2.im)
    hr1odd.natAbs hr2odd.natAbs hs1even hs2even hcop1 hcop2 h4r' h4i hB hD'
  rw [← hprod, hDabs0, hgn]
  exact hmain



end Work.FIArea7
