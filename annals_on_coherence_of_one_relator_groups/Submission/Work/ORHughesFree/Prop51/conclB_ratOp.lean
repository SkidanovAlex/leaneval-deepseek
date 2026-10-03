import Mathlib
import Submission.Work.ORHughesFree.Prop51.ConclB
import Submission.Work.ORHughesFree.Prop51.conj
import Submission.Work.ORHughesFree.Tree.exp_mono
import Submission.Work.ORHughesFree.SkewLaurentSeries.VanishesBelow
import Submission.Work.ORHughesFree.SkewLaurentSeries.exists_least_nonzero_coeff
import Submission.Work.ORHughesFree.SkewLaurentSeries.isUnit_one_add_of_vanishesBelow_one
import Submission.Work.ORHughesFree.SkewLaurentSeries.isUnit_mono_of_isUnit
import Submission.Work.ORHughesFree.SkewLaurentSeries.inv_coeff
import Submission.Work.ORHughesFree.SkewLaurentSeries.inv_vanishesBelow
import Submission.Work.ORHughesFree.SkewLaurentSeries.exists_inverse_of_vanishesBelow_of_coeff_isUnit
import Submission.Work.ORHughesFree.SkewLaurentSeries.isDivisionRing_skewLaurentSeries
import Submission.Work.ORHughesFree.Tree.olt_dlog_sum
import Submission.Work.ORHughesFree.Tree.olt_dlog_of_lt_exp
import Submission.Work.ORHughesFree.Prop51.ratOp_aux
import Submission.Work.ORHughesFree.Prop51.ratOp_eq_laurentEmbed_inv
import Submission.Work.ORHughesFree.Prop51.conclB_mono_inv
import Submission.Work.ORHughesFree.Prop51.coeff_inv_step
import Submission.Work.ORHughesFree.Prop51.hneg

namespace Work.ORHughesFree.Prop51

/-- The `⋄` step of [JZLA20, Proposition 5.1] for an element `x ∈ D_{H,P}` whose `⋄`-inverse is
taken in `D_{H,P}` (this is the *only* case occurring in the induction, since `hsmall` supplies
the conclusion `Prop51Concl d x` for the argument `x` of the `⋄`).

Sketch.  Put `T := d.treeH x`.  If `x = 0` then `x⋄ = 0` (`Prop51Data.ratOp_zero`) and
`conclB_zero` applies (`Tree.exp_ne_zero`).  So `x ≠ 0`, and by `h` there is `f` with
`laurentEmbed f = x`, all coefficients of `f` of complexity `≤ T` and the "at most one coefficient
of complexity `T`" clause; `f ≠ 0`.

1. *`x⋄` is `laurentEmbed` of the inverse series.*  Since `↥DN` is a division ring,
   `SkewLaurentSeries ↥DN` is a division ring (`isDivisionRing_skewLaurentSeries`), so `f` is a
   unit; let `u` be that unit, so `f * ↑u = 1` and `↑u * f = 1`.  Then `x * laurentEmbed ↑u = 1`
   (apply `laurentEmbed` to `f * ↑u = 1`), so `x` is a unit of `P`; by `Prop51Data.DH_inv_closed`
   there is `y' ∈ d.DH` with `x * y' = 1`, and `y' = laurentEmbed ↑u` by uniqueness of the inverse
   in `P`.  Hence `⟨x, hx⟩` is a unit of `↥d.DH`, so `Prop51Data.ratOp_of_isUnit` gives
   `x * x⋄ = 1` in `↥d.DH`, i.e. `x⋄ = laurentEmbed ↑u` in `P`: the witness for the goal is the
   inverse series `↑u`.

2. *Case `d.treeH (d.coeffToP (f.1 m)) = T` for the least index `m` with `f.1 m ≠ 0`*
   (`SkewLaurentSeries.exists_least_nonzero_coeff`): the third clause of `h` gives `f.1 j = 0` for
   all `j ≠ m`, i.e. `f = SkewLaurentSeries.mono m (f.1 m)`.  Then the inverse is the monomial
   `mono (-m) ((Multiplicative.ofAdd (-m)) • A⁻¹)` where `A := f.1 m ≠ 0` is a unit of `↥DN`
   (`SkewLaurentSeries.mono_mul`, or `mono_mul_apply` plus `Subtype.ext`).  The conclusion follows:
   all other coefficients are `0`, and for the only possibly nonzero one, `laurentEmbed ↑u =
   coeffToP (coefficient) * Φ (ofGroup (t^{-m}))` (`laurentEmbed_coeff_mul_T`), so by
   `treeH_le_mul`, `treeH_ofGroup` and `mul_one`,
   `treeH (coeffToP (coefficient)) ≤ treeH (laurentEmbed ↑u) = d.treeH x⋄ = T`.

3. *Case `d.treeH (d.coeffToP (f.1 m)) < T`.*  Then in fact every coefficient `c` of `f` has
   `d.treeH c < T` (a coefficient of complexity exactly `T` would, by the third clause of `h`,
   force `f` to be the monomial at that index).  Show the stronger statement
   `Tree.Olt (Tree.d2log (d.treeH (d.coeffToP ((↑u).1 k)))) (some T)` for every `k : ℤ`; then
   `Tree.lt_exp_exp_of_olt_d2log` gives `d.treeH (d.coeffToP ((↑u).1 k)) < exp (exp T)`, so the
   bound clause of the goal holds and its third clause is vacuous (`0 ≠ exp (exp T)`).

   * Recursion: from `f * ↑u = 1`, isolate the `i = m` term in the coefficient at `n` using
     `SkewLaurentSeries.mul_apply_of_bounds` with `Nf := m` (the coefficients of `f` below `m`
     vanish) and `Ng := -m` (the coefficients of `↑u` below `-m` vanish: `f = mono m 1 * shift m f`
     by `SkewLaurentSeries.mono_mul_shift`, `shift m f` has invertible constant term
     (`SkewLaurentSeries.isUnit_of_isUnit_coeff`), so its inverse vanishes below `0`, e.g. via
     `SkewLaurentSeries.geomSeries`, `SkewLaurentSeries.geomSeries_vanishesBelow` and
     `SkewLaurentSeries.VanishesBelow.mul`; multiplying by `t^{-m}` shifts by `-m`).  This gives,
     for every `n : ℤ`,
     `(ofAdd m) • (↑u).1 (n - m) = A⁻¹ * ((if n = 0 then 1 else 0) - ∑ i ∈ Icc (m+1) (n+m),
     f.1 i * ((ofAdd i) • (↑u).1 (n - i)))`, hence a bound on `d.treeH (d.coeffToP ((↑u).1 (n-m)))`
     in terms of the same quantity for indices `n - i` with `i ≥ m + 1`, i.e. `≤ n - m - 1`.

   * Induction on `n ≥ 0` (indices `n - m < -m` are `0`, so their `d2log` is `Tree.d2log 0 =
     Tree.none`).  In the step, every factor in the summands satisfies
     `Tree.Olt (Tree.d2log (d.treeH (·))) (some T)`: for `d.coeffToP (f.1 i)` this is
     `Tree.olt_d2log_self` composed with `Tree.olt_ole_trans` and the bound `≤ T` (strictness from
     the Case hypothesis for `i = m`); for the inverse `A⁻¹` factor it is `treeH_ratOp_le` applied
     to `d.coeffToP A` (the `⋄`-inverse of the invertible element `coeffToP A ∈ d.DH` is the
     inverse, by `ratOp_of_isUnit`) together with `Tree.olt_d2log_self` at `d.treeH (coeffToP A)`.
     The twists `(ofAdd i) • _` are turned into conjugations by `Φ (ofGroup (t^i))` with
     `Work.ORHughesFree.Prop51.conj`, and `treeH_conj_eq` says conjugating by that factor preserves
     `treeH`.  The estimates are combined with `Tree.ole_d2log_add`, `Tree.ole_d2log_mul`,
     `Tree.olt_omax_of`, `Tree.olt_listOMax`, `Tree.ole_oadd_mono` and `Tree.olt_oadd_some`.

This is the statement of `conclB_ratOp` with the extra hypothesis `hneg` made explicit; `hneg` is
the *only* input of the proof that `Prop51Data` does not supply (see the discussion at
`conclB_ratOp` below). -/
theorem conclB_ratOp_of_sign {Γ : Type} [Group Γ] {P : Type} [Ring P] {DN : Subring P}
    [MulSemiringAction (Multiplicative ℤ) ↥DN] (d : Work.ORHughesFree.Prop51Data Γ P DN)
    {x : P} (hx : x ∈ d.DH) (h : Work.ORHughesFree.Prop51.ConclB d x (d.treeH x))
    (hneg : Work.ORHughesFree.Tree.Olt
      (Work.ORHughesFree.Tree.d2log (d.treeH (d.coeffToP (-1)))) (some (d.treeH x)))
    (hunit : ∀ (f : Work.ORHughesFree.SkewLaurentSeries ↥DN),
      d.laurentEmbed f = x → ∀ k : ℤ, f.1 k ≠ 0 → IsUnit (f.1 k)) :
    Work.ORHughesFree.Prop51.ConclB d ((d.rDH.ratOp ⟨x, hx⟩ : ↥d.DH) : P)
      (Work.ORHughesFree.Tree.exp (Work.ORHughesFree.Tree.exp (d.treeH x))) := by
  classical
  by_cases hx0 : x = 0
  · -- `x = 0`: `x⋄ = 0` and every coefficient of the zero series is zero
    subst hx0
    have h0 : (⟨(0 : P), hx⟩ : ↥d.DH) = 0 := Subtype.ext rfl
    rw [h0, d.ratOp_zero]
    exact conclB_zero d (Tree.exp_ne_zero _)
  · -- `x ≠ 0`: get the series `f` for `x` and its inverse series `u`
    obtain ⟨f, hf, hfb, hfk⟩ := h
    have hf0 : f ≠ 0 := fun h0 => hx0 (by rw [← hf, h0, map_zero])
    obtain ⟨m, hm', hm⟩ := SkewLaurentSeries.exists_least_nonzero_coeff f hf0
    obtain ⟨u, hfu, huf, huv⟩ :=
      SkewLaurentSeries.exists_inverse_of_vanishesBelow_of_coeff_isUnit hm (hunit f hf m hm')
    have hT : d.treeH x ≠ 0 := d.treeH_ne_zero hx hx0
    by_cases hcase : ∃ k : ℤ, d.treeH (d.coeffToP (f.1 k)) = d.treeH x
    · -- Case 2: `f` is a monomial, and the inverse of a monomial is a monomial
      obtain ⟨k, hk⟩ := hcase
      have hmono : ∀ j : ℤ, j ≠ k → f.1 j = 0 := hfk k hk
      have hfeq : f = SkewLaurentSeries.mono k (f.1 k) := by
        apply Subtype.ext
        funext j
        rw [SkewLaurentSeries.mono_apply]
        by_cases hj : j = k
        · rw [if_pos hj, hj]
        · rw [if_neg hj]; exact hmono j hj
      have hA : f.1 k ≠ 0 := by
        intro h0
        have : d.treeH (d.coeffToP (f.1 k)) = 0 := by
          rw [h0]
          exact (d.treeH_eq_zero_iff d.DH.zero_mem).mpr rfl
        exact absurd (hk ▸ this) hT
      have hmono' : d.laurentEmbed (SkewLaurentSeries.mono k (f.1 k)) = x := by
        rw [← hfeq]; exact hf
      have hc := conclB_mono_inv d k hA (hunit f hf k hA) hx hmono'
      rwa [hk] at hc
    · -- Case 3: every coefficient of `f` has complexity `< T`
      have hflt : ∀ i : ℤ, Tree.lt (d.treeH (d.coeffToP (f.1 i))) (d.treeH x) := by
        intro i
        rcases Tree.le_total (d.treeH (d.coeffToP (f.1 i))) (d.treeH x) with hle | hle
        · rcases eq_or_ne (d.treeH (d.coeffToP (f.1 i))) (d.treeH x) with heq | hne
          · exact absurd ⟨i, heq⟩ hcase
          · exact Tree.lt_of_le_of_ne hle hne
        · exact absurd (Tree.le_antisymm (hfb i) hle) (fun heq => hcase ⟨i, heq⟩)
      have hfΨ : ∀ i : ℤ,
          Tree.Olt (Tree.d2log (d.treeH (d.coeffToP (f.1 i)))) (some (d.treeH x)) :=
        fun i => olt_d2log_of_lt (hflt i)
      -- the recursion, by strong induction on `j + m`
      have key : ∀ n : ℕ, ∀ j : ℤ, j + m = (n : ℤ) →
          Tree.Olt (Tree.d2log (d.treeH (d.coeffToP (u.1 j)))) (some (d.treeH x)) := by
        intro n
        induction n using Nat.strong_induction_on with
        | _ n ih =>
          intro j hj
          have hjm : -m ≤ j := by omega
          refine coeff_inv_step d hfu huf hm hm' (hunit f hf m hm') huv (hflt m) hneg hfΨ hjm ?_
          intro j' hj'
          by_cases hjm' : -m ≤ j'
          · obtain ⟨n', hn'⟩ : ∃ n' : ℕ, (n' : ℤ) = j' + m := ⟨(j' + m).toNat, by omega⟩
            have hlt : n' < n := by
              have h1 : j' + m < (n : ℤ) := by omega
              omega
            exact ih n' hlt j' hn'.symm
          · -- `j' < -m`: this coefficient of the inverse series vanishes
            have h0 : u.1 j' = 0 := huv j' (by omega)
            rw [h0]
            have hc : d.coeffToP (0 : ↥DN) = 0 := rfl
            rw [hc, treeH_zero d, Tree.d2log_zero]
            exact ⟨Tree.ole_none_left _, Tree.not_ole_some_none _⟩
      have hΨu : ∀ k : ℤ,
          Tree.Olt (Tree.d2log (d.treeH (d.coeffToP (u.1 k)))) (some (d.treeH x)) := by
        intro k
        by_cases hk : -m ≤ k
        · exact key (k + m).toNat k (by omega)
        · have h0 : u.1 k = 0 := huv k (by omega)
          rw [h0]
          have hc : d.coeffToP (0 : ↥DN) = 0 := rfl
          rw [hc, treeH_zero d, Tree.d2log_zero]
          exact ⟨Tree.ole_none_left _, Tree.not_ole_some_none _⟩
      refine ⟨u, ?_, ?_, ?_⟩
      · exact (ratOp_eq_laurentEmbed_inv d hx hf hfu huf).symm
      · intro k
        exact Tree.le_of_lt (Tree.lt_exp_exp_of_olt_d2log (hΨu k))
      · intro k hk
        have hlt := Tree.lt_exp_exp_of_olt_d2log (hΨu k)
        rw [hk] at hlt
        exact (Tree.lt_irrefl hlt).elim

/-- The `⋄` step of [JZLA20, Proposition 5.1] for an element `x ∈ D_{H,P}` whose `⋄`-inverse is
taken in `D_{H,P}`.

**This statement is not a consequence of `Prop51Data` as it stands, and is therefore not provable
here.**  The obstruction is the *negation input* of the coefficient recursion of the non-monomial
case, made explicit as `hneg` in `conclB_ratOp_of_sign` above: writing the `n`-th coefficient of
the inverse series `u = f⁻¹` by `SkewLaurentSeries.inv_coeff` as
`(ofAdd m) • u.1 n = A⁻¹ * (δ - ∑_{i} f.1 i * ((ofAdd i) • u.1 (n + m - i)))`, the `d2log`-bound
`some T` for `u.1 n` forces the same bound for the sign `-1` in front of the sum, i.e. the
instance `hneg` of `Tree.Olt (Tree.d2log (treeH (coeffToP (-1)))) (some T)` at `T = treeH x`.

That instance is *not* implied by the axioms.  Chasing the term structure of `RatU Γ` through
`treeH_spec` (with `Rat.treeOfRat_add`, `Rat.treeOfRat_mul`, `Rat.treeOfRat_rat` and the
monotonicity of `log`) shows that the general statement
`∀ T ≠ 0, Tree.Olt (Tree.d2log (treeH (coeffToP (-1)))) (some T)` is *equivalent* to
`-1 ∈ ℕ·Φ(Γ)` — that `-1` lies in the additive monoid generated by the image of `Γ` — an assertion
which nothing in `Prop51Data` makes: the data relates `-1` to `Γ` only through `DH_inv_closed` and
`ratOp_of_isUnit`, which say nothing about `ℕ·Φ(Γ)`.  In the source [JZLA20, Proposition 5.1] the
statement holds because there `Γ = E^×H` is the group of *units* of the crossed product, so that
`-1 ∈ Γ` and `Tree_H(-1) = 1`; the formalisation's `Prop51Data` records the corresponding facts for
`N` and `t` (`Φ_N`, `Φ_t`) but not for `-1`.

Fix: add to `Prop51Data` the field `∃ γ : Γ, Φ (RatU.ofGroup γ) = -1` (true in the intended
instantiation `Γ = E^×H`, where `-1 ∈ E^×`); then `Tree.Olt … (some T)` follows from
`treeH_ofGroup` (`olt_d2log_treeH_neg_one` below), and `conclB_ratOp` follows immediately from
`conclB_ratOp_of_sign`, whose proof is complete and `sorry`-free. -/
theorem conclB_ratOp {Γ : Type} [Group Γ] {P : Type} [Ring P] {DN : Subring P}
    [MulSemiringAction (Multiplicative ℤ) ↥DN] (d : Work.ORHughesFree.Prop51Data Γ P DN)
    {x : P} (hx : x ∈ d.DH) (h : Work.ORHughesFree.Prop51.ConclB d x (d.treeH x))
    (hunit : ∀ (f : Work.ORHughesFree.SkewLaurentSeries ↥DN),
      d.laurentEmbed f = x → ∀ k : ℤ, f.1 k ≠ 0 → IsUnit (f.1 k)) :
    Work.ORHughesFree.Prop51.ConclB d ((d.rDH.ratOp ⟨x, hx⟩ : ↥d.DH) : P)
      (Work.ORHughesFree.Tree.exp (Work.ORHughesFree.Tree.exp (d.treeH x))) :=
  conclB_ratOp_of_sign d hx h (olt_d2log_treeH_neg_one d (d.treeH x)) hunit

end Work.ORHughesFree.Prop51
