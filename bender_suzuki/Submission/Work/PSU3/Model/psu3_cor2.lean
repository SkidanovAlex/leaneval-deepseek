/-
# `psu3_cor2` (design D2 of `Submission/Work/PSU3/NOTES_LEAD_bs_psu3.md`)

Peterfalvi II, Ch. VII §1, for the model `Q = SZ(E)`, `E = GF(q²)`, `q = 2ⁿ`: given
`ζ ∈ Eˣ` with `ζ ≠ 1` and `ζ · σ(ζ) = 1` (i.e. `ζ` of order dividing `q+1` and outside the
fixed field `F`), there is `p ∈ Q` with `p.y = ζ⁻¹`, `p.x ≠ 0` and
`f(p) = ζ · p⁻¹` (the action of the torus element `ζ` on `p⁻¹`), where `f = fMapTot` is
Peterfalvi's map `f(x,y) = (x/y, 1/y)`.

The construction (Peterfalvi, loc. cit.): put `t = ζ + ζ⁻¹`.  From `ζ·σζ = 1` we get
`σζ = ζ⁻¹`, hence `σ t = t`; and `t ≠ 0`, because otherwise `ζ = ζ⁻¹`, i.e. `ζ² = 1`, and
in characteristic two `(ζ+1)² = ζ² + 1 = 0` forces `ζ = 1`.  In characteristic two the
squaring map is a bijection of the finite field `E`, so `t = u²` for some `u`; then
`σ(u)² = σ(t) = t = u²` shows `σ u = u`, i.e. `u · σu = u² = t`.  So
`p = (u, ζ⁻¹)` lies in `SZ E` (`p.y + σ p.y = ζ⁻¹ + ζ = t = u σu = p.x σ p.x`), with
`p.x ≠ 0`, and `p ≠ 1` because `p.y ≠ 0`.  Finally `f(p) = (u/ζ⁻¹, ζ) = (uζ, ζ)`, while
`ζ p⁻¹ = (ζ·(-u), (ζ σζ)·(p⁻¹).y) = (ζu, ζ)` since
`(p⁻¹).y = -ζ⁻¹ + uσu = -ζ⁻¹ + t = ζ`.
-/
import Mathlib
import Submission.Work.PSU3.Defs
import Submission.Work.PSU3.GaloisField
import Submission.Work.PSU3.FMap

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

namespace Work.PSU3.Model

theorem psu3_cor2 (n : ℕ) (ζ : (GaloisField 2 (2 * n))ˣ) (hζ1 : ζ ≠ 1)
    (hζ : (ζ : GaloisField 2 (2 * n)) * σE (ζ : GaloisField 2 (2 * n)) = 1) :
    ∃ p : SZ (GaloisField 2 (2 * n)), p.x ≠ 0 ∧ p.y = (ζ : GaloisField 2 (2 * n))⁻¹ ∧
      Work.PSU3.fMapTot p = SZ.torusAct ζ p⁻¹ := by
  set z : GaloisField 2 (2 * n) := (ζ : GaloisField 2 (2 * n)) with hzdef
  -- `σ z = z⁻¹`
  have hσζ : σE z = z⁻¹ := by
    rw [hzdef]
    exact eq_inv_of_mul_eq_one_right hζ
  -- `t = z + z⁻¹` is fixed by `σ`
  have ht_fixed : σE (z + z⁻¹) = z + z⁻¹ := by
    rw [map_add, σE_inv, hσζ, inv_inv, add_comm]
  -- `z·t = (z+1)²` in characteristic two
  have hzt : z * (z + z⁻¹) = (z + 1) ^ 2 := by
    have hz : z ≠ 0 := by rw [hzdef]; exact Units.ne_zero ζ
    rw [CharTwo.add_sq, one_pow, mul_add, mul_inv_cancel₀ hz, pow_two]
  -- `t ≠ 0`, since `t = z⁻¹(z+1)²` and `z + 1 ≠ 0`
  have ht_ne : z + z⁻¹ ≠ 0 := by
    intro h0
    have h2 : (z + 1) ^ 2 = 0 := by rw [← hzt, h0, mul_zero]
    have h3 : z + 1 = 0 := (pow_eq_zero_iff (by norm_num : 2 ≠ 0)).mp h2
    have h4 : z = 1 := by
      rw [add_eq_zero_iff_eq_neg, CharTwo.neg_eq] at h3
      exact h3
    apply hζ1
    rw [hzdef] at h4
    exact Units.ext h4
  -- squaring is a bijection of the finite field `E = GF(2^{2n})`
  obtain ⟨u, hu⟩ :=
    (PerfectRing.bijective_frobenius (R := GaloisField 2 (2 * n)) (p := 2)).2 (z + z⁻¹)
  have hu' : u ^ 2 = z + z⁻¹ := hu
  -- the square root of the `σ`-fixed element `t` is itself `σ`-fixed
  have hσu : σE u = u := by
    rw [← CharTwo.sq_inj]
    rw [← map_pow, hu', ht_fixed]
  have hu_ne : u ≠ 0 := by
    intro h
    apply ht_ne
    rw [← hu', h]
    simp
  -- the Hermitian relation for `p = (u, ζ⁻¹)`
  have hherm : z⁻¹ + σE z⁻¹ = u * σE u := by
    rw [σE_inv, hσζ, inv_inv, hσu, ← pow_two, hu']
    rw [add_comm z z⁻¹]
  refine ⟨⟨u, z⁻¹, hherm⟩, ?_, rfl, ?_⟩
  · simpa using hu_ne
  · have hp1 : (⟨u, z⁻¹, hherm⟩ : SZ (GaloisField 2 (2 * n))) ≠ 1 := by
      intro h
      have hy : z⁻¹ = 0 := by
        have := congrArg SZ.y h
        simpa using this
      exact inv_ne_zero (by rw [hzdef]; exact Units.ne_zero ζ) hy
    rw [fMapTot_of_ne_one hp1]
    ext <;>
      simp only [SZ.fMap_x, SZ.fMap_y, SZ.torusAct_x, SZ.torusAct_y, SZ.inv_x, SZ.inv_y]
    · rw [div_eq_mul_inv, inv_inv, hzdef, CharTwo.neg_eq]
      ring
    · rw [hζ, one_mul, inv_inv, hσu, ← pow_two, CharTwo.neg_eq]
      rw [CharTwo.eq_add_iff_add_eq, hu', CharTwo.add_cancel_left]

end Work.PSU3.Model
