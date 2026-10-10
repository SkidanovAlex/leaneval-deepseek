import Mathlib.GroupTheory.Nilpotent
import Submission.Work.ProP.finite_of_fg_of_finite_exponent
import Submission.Work.ProP.lowerCentralSeries_le_pCentralSeries
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace Work.ProP

/-- Every element of the free group is a `p ^ ν`-th power modulo the `ν`-th term of the
descending `p`-central series: `x ^ p ^ ν ∈ P_ν` for every `x ∈ F^(n)`.

Induction on `ν`.  For `ν = 0` this says `x ∈ ⊤`.  The step is
`(x ^ p ^ ν) ^ p ∈ P_ν ^ p ≤ P_{ν+1}`, the inclusion being part of the definition of the
`p`-central step. -/
private theorem pow_pow_mem_pCentralSeries {p : ℕ} (n : ℕ) :
    ∀ ν, ∀ x : FreeGroup (Fin n),
      x ^ p ^ ν ∈ Work.Shrinking.pCentralSeries p (FreeGroup (Fin n)) ν := by
  intro ν
  induction ν with
  | zero => intro x; simp
  | succ ν ih =>
      intro x
      have h := Work.Shrinking.pow_mem_pCentralSeries_succ p (FreeGroup (Fin n)) (ih x)
      have e : x ^ p ^ (ν + 1) = (x ^ p ^ ν) ^ p := by rw [pow_succ, pow_mul]
      rw [e]
      exact h

/-- The generic kernel quotients `F^(n)/F^(n)(ν)` are finite.

Proof: write `Q = FreeGroup (Fin n) ⧸ P_ν` with `P_ν = pCentralSeries p (FreeGroup (Fin n)) ν`.
(1) `Group.FG Q` (a quotient of the free group on `Fin n`).
(2) `Q` has finite exponent: `x ^ p ^ ν ∈ P_ν` for every `x ∈ FreeGroup (Fin n)` (induction on
    `ν`: the step is `(x ^ p ^ ν) ^ p ∈ P_ν ^ p ≤ P_{ν+1}`, the inclusion `P_ν ^ p ≤ P_{ν+1}`
    being part of the definition of the `p`-central step), so `Monoid.exponent Q ∣ p ^ ν`
    (`Monoid.exponent_dvd_of_forall_pow_eq_one`).  Note that the exponent is `p ^ ν` and **not**
    `p ^ (ν - 1)`: already `F^(n)(1) = Φ_p(F^(n))` has exponent `p` (indeed
    `Work.ProP.card_freePQuotient_one` computes its order as `p ^ n`).
(3) `Q` is nilpotent: `γ_ν ≤ P_ν` by `Work.ProP.lowerCentralSeries_le_pCentralSeries`, so the
    `ν`-th term of the lower central series of `Q` is trivial (use
    `Subgroup.map_lowerCentralSeries` for the quotient map, together with
    `Work.Shrinking.map_pCentralSeries_surjective`), whence `Group.IsNilpotent Q`
    (`Subgroup.isNilpotent_iff_lowerCentralSeries`).
(4) Conclude `Finite Q` from `Work.ProP.finite_of_fg_of_finite_exponent`, whose positivity
    hypothesis `0 < p ^ ν` always holds. -/
theorem finite_freePQuotient {p : ℕ} [Fact p.Prime] (n ν : ℕ) : Finite (FreePQuotient p n ν) := by
  -- (1) the quotient of the free group on `Fin n` is finitely generated
  have hfg : Group.FG (FreePQuotient p n ν) := inferInstance
  -- (3) it is nilpotent: the `ν`-th term of the lower central series is already trivial
  have hN : Group.IsNilpotent (FreePQuotient p n ν) := by
    apply (Group.isNilpotent_top (G := FreePQuotient p n ν)).mp
    apply (Subgroup.isNilpotent_iff_lowerCentralSeries
      (⊤ : Subgroup (FreePQuotient p n ν))).mpr
    refine ⟨ν, ?_⟩
    -- transport the lower central series along the (surjective) quotient map
    have hmap := Subgroup.map_lowerCentralSeries (⊤ : Subgroup (FreeGroup (Fin n)))
      (freePQuotientMk p n ν) ν
    have hrange : Subgroup.map (freePQuotientMk p n ν) (⊤ : Subgroup (FreeGroup (Fin n)))
        = ⊤ := Subgroup.map_top_of_surjective _ (freePQuotientMk_surjective p n ν)
    rw [hrange] at hmap
    rw [← hmap, Subgroup.map_eq_bot_iff]
    intro x hx
    rw [MonoidHom.mem_ker, freePQuotientMk_apply, QuotientGroup.eq_one_iff]
    exact lowerCentralSeries_le_pCentralSeries p (FreeGroup (Fin n)) ν hx
  -- (2) and (4): finite exponent and finitely generated together give finiteness
  refine finite_of_fg_of_finite_exponent (G := FreePQuotient p n ν) hfg hN
    (pow_pos (Fact.out : p.Prime).pos ν) ?_
  intro g
  obtain ⟨x, rfl⟩ := freePQuotientMk_surjective p n ν g
  rw [← map_pow, freePQuotientMk_apply, QuotientGroup.eq_one_iff]
  exact pow_pow_mem_pCentralSeries n ν x

end Work.ProP
