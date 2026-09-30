import Mathlib
import Submission.Work.BW.BWGradedBase

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

namespace Work.BW

/-- **A `p`-saturated ideal between a `p`-primary ideal and `p` is `p`-primary.** Let `R` be
Noetherian, `p` a prime, `Q` a `p`-primary ideal, and `I` an ideal with `Q ≤ I ≤ p` which is
`p`-saturated (`I = (I·R_p) ∩ R`). Then `I` is `p`-primary.

Route (short): put `A = R_p`, `f = algebraMap R A`, `J = I·A`. Then `J ⊆ pA = 𝔪` (so `J ≠ ⊤`), and
`p = Q.radical ≤ I.radical ≤ p` gives `pA ⊆ rad J`, hence `rad J = pA`, which is maximal; so
`Ideal.isPrimary_of_isMaximal_radical` gives `J.IsPrimary`. Since `hsat` says `J ∩ R = I`, i.e. `I` is
the comap of `J` along `f`, `Ideal.IsPrimary.comap` gives `I.IsPrimary`. The conjunct `I.radical = p`
follows from `p = Q.radical ≤ I.radical ≤ p.radical = p`. -/
theorem isPrimary_of_saturated_le {R : Type*} [CommRing R] [IsNoetherianRing R]
    (p Q I : Ideal R) (hp : p.IsPrime) (hQ : Q.IsPrimary) (hrad : Q.radical = p)
    (hQI : Q ≤ I) (hIp : I ≤ p)
    (hsat : ((I.map (algebraMap R (Localization.AtPrime p))).comap
      (algebraMap R (Localization.AtPrime p))) = I) :
    I.IsPrimary ∧ I.radical = p := by
  haveI : p.IsPrime := hp
  -- The radical of `I` is `p`.
  have hradI : I.radical = p := by
    apply le_antisymm
    · calc I.radical ≤ p.radical := Ideal.radical_mono hIp
        _ = p := hp.radical
    · calc p = Q.radical := hrad.symm
        _ ≤ I.radical := Ideal.radical_mono hQI
  refine ⟨?_, hradI⟩
  rw [Ideal.isPrimary_iff]
  refine ⟨?_, ?_⟩
  · intro htop
    exact hp.ne_top (top_le_iff.mp (htop ▸ hIp))
  · intro x y hxy
    by_cases hy : y ∈ p
    · refine Or.inr ?_
      rwa [hradI]
    · refine Or.inl ?_
      -- `y ∉ p` means `y` becomes a unit in `R_p`; saturation then forces `x ∈ I`.
      have hunit : IsUnit (algebraMap R (Localization.AtPrime p) y) :=
        (IsLocalization.AtPrime.isUnit_to_map_iff (Localization.AtPrime p) p y).mpr
          (Ideal.mem_primeCompl_iff.mpr hy)
      have hfxy : algebraMap R (Localization.AtPrime p) (x * y) ∈
          I.map (algebraMap R (Localization.AtPrime p)) := Ideal.mem_map_of_mem _ hxy
      rw [map_mul] at hfxy
      have hfx : algebraMap R (Localization.AtPrime p) x ∈
          I.map (algebraMap R (Localization.AtPrime p)) :=
        (Ideal.mul_unit_mem_iff_mem _ hunit).mp hfxy
      have hmem : x ∈ (I.map (algebraMap R (Localization.AtPrime p))).comap
          (algebraMap R (Localization.AtPrime p)) := Ideal.mem_comap.mpr hfx
      rwa [hsat] at hmem

end Work.BW
