import Mathlib
import Submission.Work.PSU3.StageB.Omega.API
import Submission.Work.PSU3.StageB.Omega.step9_of_coset
import Submission.Work.PSU3.StageB.Omega.exists_coset_zeta
import Submission.Work.PSU3.StageB.Omega.exists_zcQF_eq_of_mem_Q0

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

/-!
# `Work.PSU3.StageB.Omega.good_of_orbit`

Assembly of Peterfalvi II, Ch. VII §2 (9) into its "good element" form: every
`ω ∈ Q ∖ Q₀` has a `KW`-orbit mate `ω'` (i.e. `ω' ∈ orbKW hS fr ω`, so `ω'` differs from a
`KW`-conjugate of `ω` by an element of `Q₀`) which is again outside `Q₀` and satisfies the
canonical relation

  `f (ω') = (ω' · zc α)^ζ`

for some `α ∈ F*` (the fixed units `FX n`).

The two ingredients are exactly the two halves of §2 (8)/(9):

* `Omega.exists_coset_zeta` realises the coset `ζK`: the counting of §2 (8) forces some
  `x, z ∈ Q₀` and `k ∈ Ksub ∩ KW` with `f (ω x) = (ω z)^{k ζ}`;
* `Omega.step9_of_coset` turns that into `ω'` in the `KW`-orbit of `ω`, outside `Q₀`, with
  `f (ω') = (ω' y)^ζ` for some `y ∈ Q₀#`.

The only remaining step is that every `y ∈ Q₀#` *is* `zc α` for a unit `α` of the fixed field
(`Omega.exists_zcQF_eq_of_mem_Q0`; `Q₀` is `zc` of the fixed field of `σE`), which converts the
`y` of §2 (9) into the `zc α` of §2 (19)/(20) and hence into the input of `Omega.omegaHyp_of_good`.
-/

namespace Work.PSU3.StageB.Omega

open Work.PSU3

/-- **§2 (9), good-element form.**  For `ω ∈ Q ∖ Q₀` there are `ω' ∈ orbKW hS fr ω` with
`ω' ∉ Q₀` and `α ∈ F*` such that `f (ω') = (ω' · zc α)^ζ`. -/
theorem good_of_orbit {G : Type} [Group G] [Finite G] {H Q : Subgroup G} {t : G} {n : ℕ}
    (hS : Work.PSU3.PSU3Hyp H Q t) (fr : Work.PSU3.CoarseFrame H Q t n)
    {ω : ↥Q} (hω : (ω : G) ∉ fr.Q0) :
    ∃ ω' : ↥Q, ω' ∈ Work.PSU3.StageB.orbKW hS fr ω ∧ (ω' : G) ∉ fr.Q0 ∧
      ∃ α : ↥(Work.PSU3.StageB.FX n),
        Work.PSU3.StageB.fcan hS.split ω' =
          Work.PSU3.StageB.qconj hS.split (Work.PSU3.StageB.zetaD fr)
            (ω' * Work.PSU3.StageB.zcQF fr α) := by
  -- §2 (8): the coset `ζK` is realised, giving the input of (9).
  have hreal := exists_coset_zeta hS fr hω
  -- §2 (9): the `Q₀`-coset of `ω` produces the good element `ω'` with a `Q₀#`-shift `y`.
  obtain ⟨ω', horb, hω'Q0, y, hyQ0, hy1, hmain⟩ := step9_of_coset hS fr hω hreal
  -- `y ∈ Q₀#` is `zc α` for a unit `α` of the fixed field.
  obtain ⟨α, hα⟩ := exists_zcQF_eq_of_mem_Q0 fr hyQ0 hy1
  exact ⟨ω', horb, hω'Q0, α, by rw [hα]; exact hmain⟩

end Work.PSU3.StageB.Omega
