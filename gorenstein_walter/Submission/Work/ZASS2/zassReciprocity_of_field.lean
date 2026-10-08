import Mathlib
import Submission.Work.ZASS.Leaf9
import Submission.Work.ZASS.Z5
import Submission.Work.ZASS2.ZassS
import Submission.Work.ZASS2.zassCoords_alpha
import Submission.Work.ZASS2.two_dvd_of_involution_fixing
import Submission.Work.ZASS2.zassCoords_tau
import Submission.Work.ZASS2.zassCoords_isSquare_neg_one_iff_even
import Submission.Work.ZASS2.zassS_three_point
import Submission.Work.ZASS2.zassS_equivariant

namespace Work.ZASS2

open Work.GW2

private theorem option_exists_of_ne_none {α : Type*} {o : Option α} (h : o ≠ none) :
    ∃ a, o = some a := by
  cases o with
  | none => exact absurd rfl h
  | some a => exact ⟨a, rfl⟩

/-! # ZASS2 bridge: the group form of reciprocity from the field form

`ZassReciprocityProp` follows formally from `ZassReciprocityFieldProp` (the pure field
statement `S x = c/x`), which is proved in parallel in
`Submission/Work/ZASS2/zassReciprocityField.lean`; this bridge takes it as a hypothesis so that
it can be proved without waiting.

Route.  Given `ZassHyps2`, `C : ZassCoords G X inf zero U`, an involution `s` interchanging
`inf` and `zero` with `Inverts s (pairStab G inf zero)`, and the `d`-even fixed-point
hypothesis, define `S : C.E → C.E` by: for `C.Θ x = some y` with `y ≠ 0`, let `S y` be the
unique `y'` with `C.Θ (s • x) = some y'`.  (This `S` is `Work.ZASS2.zassS`, defined in
`Submission/Work/ZASS2/ZassS.lean` together with its API `zassS_spec`, `zassS_ne_zero`,
`zassS_involutive`.)

* `S y ≠ 0` (`y ≠ 0`): if `S y = 0` then `s • x = zero`, hence `x = s • zero = inf`, against
  `C.Θ x = some y`.
* `S (S y) = y`: from `s ^ 2 = 1` (`orderOf s = 2`).
* `S (a^2 * y) = S y / a^2`: take `h ∈ pairStab G inf zero` with `C.α h = a^2` (`C.α_range`);
  `Inverts s` gives `s * h * s⁻¹ = h⁻¹`, and `C.scale` computes `Θ (s • (h • x))` two ways
  (multiplicativity of `C.α`, i.e. `α (h⁻¹) = (α h)⁻¹`, is derivable from `C.scale` and
  injectivity of `Θ`).
* `¬ IsSquare (-1) → ∀ y ≠ 0, S y ≠ y`: a nonzero fixed point gives two fixed points of the
  involution `s` (the fixed-point set of an involution on an even set is even), so
  `s ∈ pairStab G x y'`, whose order `(p^k-1)/2` is odd; and `¬ IsSquare (-1 : C.E)` forces
  `(p^k-1)/2` odd (in a finite field of odd characteristic, `-1` is a square iff `4 ∣ q - 1`).
* The three-point rule: for `a ≠ 0` pick `h ∈ pairStab G inf zero` with `C.α h = a^2` and
  `u₁ ∈ U` with `C.τ u₁ = 1`; then `ZassStep S a` is the action of `u₁ * h * s` (`C.trans`,
  `C.scale`, `ZassSbar`, `ZassStep`), so if its third power fixes `none`, `some 0`, `some 1`,
  then `(u₁ * h * s)^3` fixes three points and `ZassHyps2` forces it to be `1`.
* `IsSquare (-1) → ∃ y ≠ 0, S y = y`: the hypothesis gives a fixed point `x` of `s`, which is
  neither `inf` nor `zero` (an involution fixing `inf` also fixes `zero`), so its coordinate
  `y` is nonzero and `S y = y`.

`hF` then gives `c` with `IsSquare (-c)` and `S y = c / y`, which is exactly the required
conclusion. -/
theorem zassReciprocity_of_field (hF : Work.GW2.ZassReciprocityFieldProp) :
    Work.GW2.ZassReciprocityProp := by
  intro G X _ _ _ _ p k _ hp hq hZ inf zero hne U hU C s hsord hsi hsz hinv hfix
  classical
  obtain ⟨_hUB, _hcardU, _hN, _hdec, _hfree, _hcommU, hexp⟩ := hU
  -- `s * s = 1` from `orderOf s = 2`
  have hss : s * s = 1 := by
    have h := pow_orderOf_eq_one s
    rw [hsord] at h
    simpa [pow_two] using h
  have hq2 : 2 ≤ p ^ k := by omega
  -- `C.E` has odd characteristic: `τ : U ≅ (C.E,+)` is additive and `U` has exponent `p`
  have h2E : (2 : C.E) ≠ 0 := (zassCoords_tau C hp hexp).2.2
  -- the `α`-calculus: `α` is multiplicative, `α 1 = 1`, injective, and `α h⁻¹ = (α h)⁻¹`
  obtain ⟨_hαmul, _hαone, _hαker, hαinv⟩ := zassCoords_alpha hZ hq2 hne C
  -- in a field of odd order `q`, `-1` is a square iff `(q - 1)/2` is even
  have hiff := zassCoords_isSquare_neg_one_iff_even hZ hq2 hne C h2E
  -- the three hypotheses of the field form that are immediate
  have hS0 : ∀ x : C.E, x ≠ 0 → zassS C s x ≠ 0 := fun x hx => zassS_ne_zero C hsz hss hx
  have hSS : ∀ x : C.E, x ≠ 0 → zassS C s (zassS C s x) = x :=
    fun x hx => zassS_involutive C hsz hss hx
  have hEqv : ∀ a x : C.E, a ≠ 0 → x ≠ 0 →
      zassS C s (a ^ 2 * x) = zassS C s x / a ^ 2 :=
    zassS_equivariant C hss hsz hinv hαinv
  -- no nonzero fixed point when `-1` is not a square
  have hNoFix : ¬ IsSquare (-1 : C.E) → ∀ x : C.E, x ≠ 0 → zassS C s x ≠ x := by
    intro hnsq y hy hyfix
    have hodd : Odd ((p ^ k - 1) / 2) :=
      Nat.not_even_iff_odd.mp (fun he => hnsq (hiff.mpr he))
    have h1 : C.Θ (s • (C.Θ.symm (some y))) = C.Θ (C.Θ.symm (some y)) := by
      rw [zassS_spec C hsz hss hy, hyfix, Equiv.apply_symm_apply C.Θ (some y)]
    have h2 : s • (C.Θ.symm (some y)) = C.Θ.symm (some y) := C.Θ.injective h1
    have h2dvd : 2 ∣ (p ^ k - 1) / 2 := two_dvd_of_involution_fixing hZ hp.pow hsord h2
    exact (Nat.not_odd_iff_even.mpr (even_iff_two_dvd.mpr h2dvd)) hodd
  -- a nonzero fixed point when `-1` is a square
  have hFix : IsSquare (-1 : C.E) → ∃ x : C.E, x ≠ 0 ∧ zassS C s x = x := by
    intro hsq
    obtain ⟨x, hxfix⟩ := hfix (hiff.mp hsq)
    have hxinf : x ≠ inf := by
      intro hx
      rw [hx, hsi] at hxfix
      exact hne hxfix.symm
    have hxzero : x ≠ zero := by
      intro hx
      rw [hx, hsz] at hxfix
      exact hne hxfix
    have hΘne : C.Θ x ≠ none := by
      intro h
      exact hxinf (C.Θ.injective (by rw [h, C.Θ_inf]))
    obtain ⟨y, hy⟩ := option_exists_of_ne_none hΘne
    have hyzero : y ≠ 0 := by
      intro hzero
      exact hxzero (C.Θ.injective (by rw [hy, hzero, C.Θ_zero]))
    refine ⟨y, hyzero, ?_⟩
    have hx' : C.Θ.symm (some y) = x := (C.Θ.symm_apply_eq).mpr hy.symm
    have hsp := zassS_spec C hsz hss hyzero
    have hsome : (some (zassS C s y) : Option C.E) = some y := by
      rw [← hsp, hx', hxfix, hy]
    exact Option.some.inj hsome
  -- the three-point rule
  have hThree : ∀ a : C.E, a ≠ 0 → (ZassStep (zassS C s) a)^[3] none = none →
      (ZassStep (zassS C s) a)^[3] (some 0) = some 0 →
      (ZassStep (zassS C s) a)^[3] (some 1) = some 1 →
      ∀ y, (ZassStep (zassS C s) a)^[3] y = y :=
    fun a ha => zassS_three_point hZ hne C hss hsi hsz hinv a ha
  -- the pure field form, applied at `S = zassS C s` on `C.E`
  obtain ⟨c, hc0, hcsq, hcform⟩ :=
    hF C.E (zassS C s) h2E hS0 hSS hEqv hNoFix hThree hFix
  refine ⟨c, hc0, hcsq, ?_⟩
  intro x y hy hxy
  have hx' : C.Θ.symm (some y) = x := (C.Θ.symm_apply_eq).mpr hxy.symm
  have hsp := zassS_spec C hsz hss hy
  rw [hx'] at hsp
  rw [hsp, hcform y hy]

end Work.ZASS2
