/-
# `Submission.Work.FIArea6V.Area5TwoV_of_S16CoreTwoV`

The clean (V) lane's counterpart of `Work.FIArea6.area5Two_of_S16CoreTwo`
(`Submission/Work/FIArea6/area5Two_of_invBound.lean`).

`S16CoreTwoV` is *FI* Lemma 16.2 for the **strict** characters `IsCharMod4dStrict d χ` (values
supported on the units modulo `4d`), while `Area5TwoV` states the same bound for **all** characters
of modulus `4d` in the sense of the round-4 encoding `IsCharMod4d6 = Work.FITop3.IsCharMod4d`
(multiplicative, bounded by `1`, periodic modulo `4d`, vanishing on multiples of `4d`).

The two differ in exactly one place, and the reduction is the *same* as in the pinned lane: replace
`χ` by its strict part `χ̃ = χ·1_{(ℤ[i]/4d)^*}`, which agrees with `χ` on the support of any
`IsBetaCoeff6` coefficient and is strict by construction.  Every support point of `IsBetaCoeff6` is
free of primes `≤ Pz` (`IsBetaCoeff6.noSmallPrimes`), while `d ≤ Pz` by the threshold bookkeeping
`d_le_Pz_of_log_bound`, so every prime divisor of `4d` is `≤ Pz` and a support point is a unit
modulo `4d` (`isUnitMod4d_of_noSmallPrimes`).  Hence `β_z χ(z) = β_z χ̃(z)` for every `z`, the two
sums coincide, and `χ̃` is a strict character (`strictPart_isCharMod4dStrict`).

The V-lane adds two hypotheses to the `∀Pa`-clause — `TauVac Pa φ` and the axis-free polar box —
which are simply threaded through both statements unchanged.  The two statements carry the same
pair `(c, C)` and the same right-hand side `(4d)N(log N)^6`, so only the threshold `max x₀ X₀`
remains.
-/
import Mathlib
import Submission.Work.FIArea6V.Defs
import Submission.Work.FIArea6.area5Two_of_invBound
import Submission.Work.FIArea6Hecke.area5_6_of_S16Core

namespace Work.FIArea6V

open Finset
open scoped BigOperators

attribute [local instance] Classical.propDecidable

noncomputable section

/-- **`Area5TwoV` from the strict-character core `S16CoreTwoV`** (*FI* Lemma 16.2 at *all*
characters of modulus `4d`, in the τ-vacuous clean lane).

`S16CoreTwoV` asks for `IsCharMod4dStrict d χ`; `Area5TwoV` asks for the weaker `IsCharMod4d6 d χ`.
The gap is closed by the strict part `χ̃`: on the support of any `IsBetaCoeff6` coefficient the
values agree, and `χ̃` is strict.  Since both statements carry the same `(c, C)` and the same
right-hand side, only the threshold bookkeeping `d ≤ Pz` (`d_le_Pz_of_log_bound`) remains, and the
two lane hypotheses `TauVac Pa φ` and the axis-free polar box are passed through unchanged. -/
theorem Area5TwoV_of_S16CoreTwoV (h : Work.FIArea6V.S16CoreTwoV) :
    Work.FIArea6V.Area5TwoV := by
  intro ε hε0 hε4
  obtain ⟨c, C, x0, hc, hC, hx0, hS⟩ := h ε hε0 hε4
  obtain ⟨X0, hX0⟩ := Work.FIArea6Hecke.d_le_Pz_of_log_bound ε hε0
  refine ⟨c, C, max x0 X0, hc, hC, lt_of_lt_of_le hx0 (le_max_left _ _), ?_⟩
  intro Pa hx φ ν z0 d k chi hTau hAxis hν0 hνlt hd1 hdl hk hchi β hβ
  have hx0' : x0 ≤ (Pa.x : ℝ) := le_trans (le_max_left _ _) hx
  have hX : X0 ≤ (Pa.x : ℝ) := le_trans (le_max_right _ _) hx
  have hdPz : d ≤ Pa.Pz := hX0 Pa ν d hX hν0 hνlt hd1 hdl
  have hψ : Work.FIArea5.S16Hecke.IsCharMod4dStrict d
      (Work.FIArea6Hecke.GaussUnit.strictPart d chi) :=
    Work.FIArea6Hecke.GaussUnit.strictPart_isCharMod4dStrict hd1 hchi
  have key := hS Pa hx0' φ ν z0 d k (Work.FIArea6Hecke.GaussUnit.strictPart d chi)
    hTau hAxis hν0 hνlt hd1 hdl hk hψ β hβ
  have heq : (∑ z ∈ Work.FITop.boxN Pa,
        β z * Work.FIArea6Hecke.GaussUnit.strictPart d chi z
          * (z.toComplex / (Real.sqrt (Work.FIPlan.gnorm z : ℝ) : ℂ)) ^ k)
      = ∑ z ∈ Work.FITop.boxN Pa,
        β z * chi z * (z.toComplex / (Real.sqrt (Work.FIPlan.gnorm z : ℝ) : ℂ)) ^ k := by
    refine Finset.sum_congr rfl fun z _ => ?_
    by_cases hb : β z = 0
    · simp [hb]
    · have hunit : Work.FIArea5.S16Hecke.IsUnitMod4d d z :=
        Work.FIArea6Hecke.GaussUnit.isUnitMod4d_of_noSmallPrimes hd1 hdPz
          (Work.FITop4.IsBetaCoeff6.noSmallPrimes hβ hb)
      rw [Work.FIArea6Hecke.GaussUnit.strictPart_of_unit hunit]
  rw [heq] at key
  exact key

end

end Work.FIArea6V
