import Mathlib
import Submission.Work.KMTPlan.A6.MdlIwLow

-- v4.35 port: restore the v4.34 instance-unification behaviour (respectTransparency) in this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

/-!
# Mean-zero functions on `ℤ/p^jℤ` satisfy the IW minor-arc condition for large `p`

The Ionescu--Wainger minor-arc condition of Krause--Mirek--Tao (Appendix A) for a function
`g : ℤ/Qℤ → ℂ` is

  `Work.KMTPlan.A6.MdlIwMinorArc ρ l Q g` : the discrete Fourier transform of `g` vanishes on
  every frequency `ξ` that is killed by some `q ∈ P_{≤l} = iwP ρ l`.

In this file we record the elementary observation that in the *prime power* model `Q = p ^ j`
with `p` a large prime this condition is automatic for mean-zero functions: if `p` exceeds
every element of the finite set `iwP ρ l`, then every `q ∈ iwP ρ l` is invertible in `ℤ/p^jℤ`,
so a residue class killed by such a `q` must be `0`.  Thus

  `iwLowFreqs ρ l (p ^ j) ⊆ {0}`,

and mean zero says precisely that the discrete Fourier transform vanishes at `0`.

Consequently the only arithmetic hypothesis needed for the model estimate `bile` in the
prime-power model is `∑ g = 0`, which is exactly what the "large prime" reduction of §5 of the
model chain supplies.
-/

set_option autoImplicit false

namespace Work.KMTPlan.A6

open Work.Analysis.IonescuWainger

noncomputable section

/-- If `p` is larger than every element of `iwP ρ l`, then no element of `iwP ρ l` is a multiple
of the prime `p`.  (All elements of `iwP ρ l` are positive by
`Work.Analysis.IonescuWainger.pos_of_mem_iwP`.) -/
theorem not_dvd_of_sup_iwP_lt {ρ : ℝ} {l p q : ℕ} (hB : (iwP ρ l).sup id < p)
    (hq : q ∈ iwP ρ l) : ¬ p ∣ q := by
  intro hdvd
  have h1 : p ≤ q := Nat.le_of_dvd (pos_of_mem_iwP hq) hdvd
  have h2 : q ≤ (iwP ρ l).sup id := Finset.le_sup (f := id) hq
  omega

/-- `q` is coprime to `p ^ j` as soon as the prime `p` does not divide `q`. -/
theorem coprime_pow_of_not_dvd_of_prime {p q j : ℕ} (hp : p.Prime) (h : ¬ p ∣ q) :
    q.Coprime (p ^ j) :=
  ((Nat.Prime.coprime_iff_not_dvd hp).mpr h).symm.pow_right j

/-- For a prime `p` exceeding every element of `iwP ρ l`, the only residue class modulo `p ^ j`
killed by an element of `iwP ρ l` is `0`. -/
theorem eq_zero_of_mem_iwLowFreqs {ρ : ℝ} {l p j : ℕ} [Fact p.Prime] [NeZero (p ^ j)]
    {ξ : ZMod (p ^ j)} (hB : (iwP ρ l).sup id < p)
    (hξ : ξ ∈ iwLowFreqs ρ l (p ^ j)) : ξ = 0 := by
  obtain ⟨q, hqmem, hqξ⟩ := (Finset.mem_filter.mp hξ).2
  have hnotdvd : ¬ p ∣ q := not_dvd_of_sup_iwP_lt hB hqmem
  have hcop : q.Coprime (p ^ j) := coprime_pow_of_not_dvd_of_prime Fact.out hnotdvd
  have hunit : IsUnit (q : ZMod (p ^ j)) := (ZMod.isUnit_iff_coprime q (p ^ j)).mpr hcop
  have hmul : (q : ZMod (p ^ j)) * ξ = 0 := by rw [← nsmul_eq_mul]; exact hqξ
  exact hunit.mul_left_eq_zero.mp (by rw [mul_comm]; exact hmul)

theorem MdlIwMinorArc_of_meanZero_largePrime (ρ : ℝ) (hρ : 0 < ρ) (hρ1 : ρ ≤ 1) (l : ℕ) :
    ∃ B : ℕ, ∀ (p j : ℕ) [Fact p.Prime] [NeZero (p ^ j)], B < p → ∀ g : ZMod (p ^ j) → ℂ,
      (∑ x : ZMod (p ^ j), g x) = 0 → Work.KMTPlan.A6.MdlIwMinorArc ρ l (p ^ j) g := by
  refine ⟨(iwP ρ l).sup id, ?_⟩
  intro p j hpinst hne hB g hg ξ hξ
  have hξ0 : ξ = 0 := eq_zero_of_mem_iwLowFreqs hB hξ
  rw [hξ0, ZMod.dft_apply_zero]
  simpa using hg

end

end Work.KMTPlan.A6
