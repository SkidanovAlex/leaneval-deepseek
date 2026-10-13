import Submission.Work.DSMap.Map

/-!
# DSDEN — common denominators in `W[1/x]` (the `DEN` node of the MIX2 route)

Subproject of the direct-summand development (curric-46 lead), LeanEval problem
`direct_summand`, mixed-characteristic area, `M3`-free `MIX2` route
(`sources/dsmap/direct_summand_mix2.md`).

The frozen interface this area proves is
`DSMap.Mix2.exists_chart_gens` — "**DEN**: common denominators `ϖ₀^{pe}` in `W[1/p]`" —
together with `DSMap.Mix2.isUnit_varpi_pow`.  Both live in `Submission/Work/DSDEN/Main.lean`;
this file holds the reusable core they are built from.

## Mathematical content

For a commutative ring `W`, an element `x` and a unit `v` of `W`, every element of the
localisation `W[1/x] = Localization.Away x` is a fraction whose numerator lies in `W` and whose
denominator is a power of `x * v`: the power `(x * v)^e` is a *common denominator* for any
*finite* family of elements of `W[1/x]`.  The point of exhibiting `x * v` (rather than `x`) is
that the perfectoid normalisation `ϖ₀^p = p · v` presents the pseudo-uniformizer as `p` times a
unit *of `W`*, so that the denominator `p^e` may be replaced by `(p v)^e = ϖ₀^{p e}`
(`Work.DSDEN.exists_chart_gens_proved`).

## Main results

* `Work.DSDEN.exists_common_denom_pow` — common denominator `x^e` for a finite family in
  `W[1/x]`.
* `Work.DSDEN.exists_common_denom_mul_unit` — the same with `x` replaced by `x * v`, `v` a unit
  of `W` (the form the perfectoid node needs).
* `Work.DSDEN.exists_chart_gens_proved` (in `Main.lean`) — **DEN**: common denominator
  `ϖ₀^{p e}` for a finite family in `W[1/p]`, over a `DSMap.PerfectoidData`.
* `Work.DSDEN.isUnit_varpi_pow_proved` (in `Main.lean`) — `ϖ₀^e` is a unit of `W[1/p]`.

The statement of the two `proved` theorems is *identical* (up to universe names) to the frozen
statements `DSMap.Mix2.exists_chart_gens`, `DSMap.Mix2.isUnit_varpi_pow`; see
`Submission/Work/DSDEN/AxiomCheck.lean` for the type-identity checks.
-/

set_option linter.style.haveILetI false

namespace Work.DSDEN

universe u v

/-! ## Common denominators -/

section Denom

variable {W : Type u} [CommRing W] {ι : Type v}

/-- **Clearing denominators in `W[1/x]`.**  `IsLocalization.Away.surj` in the normal form used
below: for `s ∈ W[1/x]` there are `n` and `w ∈ W` with `s * x^n = w` in `W[1/x]`. -/
theorem exists_denom_pow (x : W) (s : Localization.Away x) :
    ∃ (n : ℕ) (w : W), s * algebraMap W (Localization.Away x) x ^ n = algebraMap W _ w :=
  IsLocalization.Away.surj x s

/-- **Common denominator `(x * v)^e`.**  For *any* `v : W` and any finite family
`s : ι → W[1/x]` there is one exponent `e` and one family `t : ι → W` with `s k = t k / (x v)^e`
for every `k`, i.e. `algebraMap (t k) = algebraMap ((x v)^e) * s k` in `W[1/x]`.

The exponent is the sum of the individual denominators `n k` supplied by
`IsLocalization.Away.surj`, and the numerator `t k = w k * x^(e - n k) * v^e` is the naive
numerator `w k` times the part `(x v)^e / x^(n k) = x^(e - n k) v^e` of the common denominator
that does not cancel against `x^(n k)`. -/
theorem exists_common_denom (x v : W) [Finite ι] (s : ι → Localization.Away x) :
    ∃ (e : ℕ) (t : ι → W), ∀ k,
      algebraMap W (Localization.Away x) (t k) =
        algebraMap W _ ((x * v) ^ e) * s k := by
  classical
  letI : Fintype ι := Fintype.ofFinite ι
  choose n w hw using fun k => IsLocalization.Away.surj x (s k)
  refine ⟨∑ k, n k, fun k => w k * x ^ (∑ i, n i - n k) * v ^ (∑ i, n i), fun k => ?_⟩
  have hle : n k ≤ ∑ i, n i :=
    Finset.single_le_sum (fun i _ => Nat.zero_le _) (Finset.mem_univ k)
  have hx : (x * v) ^ (∑ i, n i) = x ^ (∑ i, n i) * v ^ (∑ i, n i) := mul_pow x v _
  rw [hx, map_mul, map_mul, map_mul, map_pow, map_pow, map_pow]
  rw [← hw k,
    show (algebraMap W (Localization.Away x)) x ^ (∑ i, n i) =
        (algebraMap W (Localization.Away x)) x ^ n k *
          (algebraMap W (Localization.Away x)) x ^ (∑ i, n i - n k) from by
      rw [← pow_add, Nat.add_sub_cancel' hle]]
  ring

/-- **Common denominator `(x * v)^e`, `v` a unit of `W`.**  The case of
`Work.DSDEN.exists_common_denom` needed by the perfectoid node: rescaling the denominator `x^e`
by a *unit* of `W` is what allows `p^e` to be replaced by `(p v)^e = ϖ₀^{p e}`. -/
theorem exists_common_denom_mul_unit (x : W) (v : Wˣ) [Finite ι]
    (s : ι → Localization.Away x) :
    ∃ (e : ℕ) (t : ι → W), ∀ k,
      algebraMap W (Localization.Away x) (t k) =
        algebraMap W _ ((x * (v : W)) ^ e) * s k :=
  exists_common_denom x (v : W) s

/-- **Common denominator `x^e`.**  The special case `v = 1` of
`Work.DSDEN.exists_common_denom`: for a finite family `s : ι → W[1/x]` there is one exponent `e`
and one family `t : ι → W` with `algebraMap (t k) = algebraMap (x^e) * s k`. -/
theorem exists_common_denom_pow (x : W) [Finite ι] (s : ι → Localization.Away x) :
    ∃ (e : ℕ) (t : ι → W), ∀ k,
      algebraMap W (Localization.Away x) (t k) = algebraMap W _ (x ^ e) * s k := by
  obtain ⟨e, t, ht⟩ := exists_common_denom_mul_unit x 1 s
  exact ⟨e, t, fun k => by simpa using ht k⟩

/-- **Stability of a common denominator.**  If the denominator `c^e` works for the family `s`,
so does every larger power `c^{e'}` (`e ≤ e'`): the numerators are multiplied by `c^{e'-e}`.

This is how two families with different common denominators are combined: raise both exponents to
a common bound. -/
theorem exists_common_denom_mono (x c : W) {e e' : ℕ} (he : e ≤ e')
    {ι : Type v} {s : ι → Localization.Away x} {t : ι → W}
    (h : ∀ k, algebraMap W (Localization.Away x) (t k) = algebraMap W _ (c ^ e) * s k) :
    ∃ t' : ι → W, ∀ k, algebraMap W (Localization.Away x) (t' k) =
      algebraMap W _ (c ^ e') * s k := by
  refine ⟨fun k => t k * c ^ (e' - e), fun k => ?_⟩
  have key : algebraMap W (Localization.Away x) (c ^ e) *
      algebraMap W (Localization.Away x) (c ^ (e' - e)) =
      algebraMap W (Localization.Away x) (c ^ e') := by
    rw [← map_mul, ← pow_add, Nat.add_sub_cancel' he]
  rw [map_mul, h k]
  rw [show ((algebraMap W (Localization.Away x) (c ^ e) * s k) *
        algebraMap W (Localization.Away x) (c ^ (e' - e))) =
      (algebraMap W (Localization.Away x) (c ^ e) *
        algebraMap W (Localization.Away x) (c ^ (e' - e))) * s k from by ring, key]

end Denom

end Work.DSDEN
