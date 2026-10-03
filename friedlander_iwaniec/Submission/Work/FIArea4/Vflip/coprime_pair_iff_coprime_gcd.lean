import Mathlib
import Submission.Work.FIArea4.Vflip.FlipSetup

namespace Work.FIArea4.Vflip

/-- **Auxiliary divisibility input.**  If `(r,s) = 1` and `d` divides the (absolute value of the)
integer `r s' - r' s`, then the common divisor `(r,d)` divides `r'`.

Indeed `(r,d) ∣ r`, `(r,d) ∣ d ∣ r s' - r' s`, hence `(r,d) ∣ r' s`; and `((r,d), s) ∣ (r,s) = 1`
gives `(r,d) ∣ r'`. -/
lemma gcd_dvd_of {r s r' s' d : ℕ} (hs : Nat.Coprime r s)
    (hdvd : d ∣ ((r : ℤ) * (s' : ℤ) - (r' : ℤ) * (s : ℤ)).natAbs) :
    Nat.gcd r d ∣ r' := by
  have hed : Nat.gcd r d ∣ d := Nat.gcd_dvd_right r d
  have her : Nat.gcd r d ∣ r := Nat.gcd_dvd_left r d
  have hdZ : ((d : ℤ)) ∣ ((r : ℤ) * (s' : ℤ) - (r' : ℤ) * (s : ℤ)) :=
    Int.dvd_natAbs.mp (Int.natCast_dvd_natCast.mpr hdvd)
  have heZ : ((Nat.gcd r d : ℕ) : ℤ) ∣ ((r : ℤ) * (s' : ℤ) - (r' : ℤ) * (s : ℤ)) :=
    (Int.natCast_dvd_natCast.mpr hed).trans hdZ
  have hA : ((Nat.gcd r d : ℕ) : ℤ) ∣ (r : ℤ) * (s' : ℤ) :=
    (Int.natCast_dvd_natCast.mpr her).mul_right (s' : ℤ)
  have hB : ((Nat.gcd r d : ℕ) : ℤ) ∣ (r' : ℤ) * (s : ℤ) := by
    have hsub : ((r : ℤ) * (s' : ℤ) - ((r : ℤ) * (s' : ℤ) - (r' : ℤ) * (s : ℤ)))
        = (r' : ℤ) * (s : ℤ) := by ring
    rw [← hsub]
    exact dvd_sub hA heZ
  have hBnat : Nat.gcd r d ∣ r' * s := by
    have : (Nat.gcd r d : ℤ) ∣ ((r' * s : ℕ) : ℤ) := by simpa using hB
    exact Int.ofNat_dvd.mp this
  have he_s : Nat.Coprime (Nat.gcd r d) s := hs.coprime_dvd_left her
  exact he_s.dvd_of_dvd_mul_right hBnat

/-- **The co-primality condition of the pair sum is a condition on the common divisor.**

`Work.FIPlan.Evar` sums over pairs `(r,s)` with `r` coprime to `d`; expanding `Evar` as the pair
sum `Evar_eq_pairSum` therefore restricts to pairs with `(r₁,d) = (r₂,d) = 1`.  Since the pairs of
the support satisfy `(rᵢ,sᵢ) = 1` and the congruence is `d ∣ r₁s₂ - r₂s₁`, this is *equivalent* to
the single condition `((r₁,r₂), d) = 1` — which is the form on which the Möbius inversion of §12
(`[((r₁,r₂),d) = 1] = Σ_{m ∣ (r₁,r₂)} μ(m)[m ∣ d]`) operates:

`(Nat.Coprime r₁ d ∧ Nat.Coprime r₂ d) ↔ Nat.Coprime (Nat.gcd r₁ r₂) d`.

(`⟹`: `(Nat.gcd r₁ r₂) ∣ r₁`.  `⟸`: `(r₁,d) ∣ r₁` and `(r₁,d) ∣ d ∣ r₁s₂ - r₂s₁`, so
`(r₁,d) ∣ r₂s₁`, and `((r₁,d), s₁) ∣ (r₁,s₁) = 1` gives `(r₁,d) ∣ r₂`, hence
`(r₁,d) ∣ Nat.gcd r₁ r₂` and so `(r₁,d) ∣ Nat.gcd (Nat.gcd r₁ r₂) d = 1`.) -/
theorem coprime_pair_iff_coprime_gcd {r1 s1 r2 s2 d : ℕ} (hs1 : Nat.Coprime r1 s1)
    (hs2 : Nat.Coprime r2 s2)
    (hdvd : d ∣ ((r1 : ℤ) * (s2 : ℤ) - (r2 : ℤ) * (s1 : ℤ)).natAbs) :
    (Nat.Coprime r1 d ∧ Nat.Coprime r2 d) ↔ Nat.Coprime (Nat.gcd r1 r2) d := by
  constructor
  · rintro ⟨h1, h2⟩
    have h := h1.gcd_left r2
    rwa [Nat.gcd_comm r2 r1] at h
  · intro hg
    have hg1 : Nat.gcd (Nat.gcd r1 r2) d = 1 := Nat.coprime_iff_gcd_eq_one.mp hg
    have hdvd' : d ∣ ((r2 : ℤ) * (s1 : ℤ) - (r1 : ℤ) * (s2 : ℤ)).natAbs := by
      have heq : (r2 : ℤ) * (s1 : ℤ) - (r1 : ℤ) * (s2 : ℤ)
          = -((r1 : ℤ) * (s2 : ℤ) - (r2 : ℤ) * (s1 : ℤ)) := by ring
      rw [heq, Int.natAbs_neg]
      exact hdvd
    refine ⟨?_, ?_⟩
    · have h : Nat.gcd r1 d ∣ Nat.gcd (Nat.gcd r1 r2) d :=
        Nat.dvd_gcd (Nat.dvd_gcd (Nat.gcd_dvd_left r1 d) (gcd_dvd_of hs1 hdvd))
          (Nat.gcd_dvd_right r1 d)
      rw [hg1] at h
      exact Nat.coprime_iff_gcd_eq_one.mpr (Nat.dvd_one.mp h)
    · have h : Nat.gcd r2 d ∣ Nat.gcd (Nat.gcd r1 r2) d :=
        Nat.dvd_gcd (Nat.dvd_gcd (gcd_dvd_of hs2 hdvd') (Nat.gcd_dvd_left r2 d))
          (Nat.gcd_dvd_right r2 d)
      rw [hg1] at h
      exact Nat.coprime_iff_gcd_eq_one.mpr (Nat.dvd_one.mp h)

end Work.FIArea4.Vflip
