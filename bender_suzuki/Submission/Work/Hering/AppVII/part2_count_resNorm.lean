import Mathlib
import Submission.Work.Hering.AppVII.part2_orbitSum_norm

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

/-!
# `Work.Hering.AppVII.part2_count_resNorm`

If the restriction of `χ : G → ℂ` to a normal subgroup `N ⊴ G` is the multiple
`e · (orbitSum N θ)` of the orbit sum of an irreducible character `θ` of `N`, then the sum
of the squared norms of `χ` over `N` is

`∑_{u ∈ N} ‖χ u‖² = e² · |charOrbit N θ| · |N|`.

Indeed, writing `f = orbitSum N θ`, the hypothesis gives `χ u = e * f u` for every `u ∈ N`, so

`∑_{u ∈ N} ‖χ u‖² = e² ∑_{u ∈ N} ‖f u‖²`,

while expanding the inner product `⟪f, f⟫ = |N|⁻¹ ∑_u f u * conj (f u)` and using
`z * conj z = (normSq z : ℂ)` shows `↑(∑_u ‖f u‖²) = |N| * ⟪f, f⟫`.  Finally
`Work.Hering.AppVII.part2_orbitSum_norm` evaluates `⟪f, f⟫ = |charOrbit N θ|`, since the orbit
of an irreducible character consists of distinct irreducible characters.

The result is the "norm count" read off from Clifford's theorem: the norm of `χ` over the
normal subgroup `N` is the multiplicity `e` squared times the size of the character orbit,
times `|N|`.
-/

noncomputable section

open Classical

namespace Work.Hering.AppVII

/-- For a finite group `H` and any function `f : H → ℂ`, the sum of the squared norms of the
values of `f`, regarded as a complex number, is `|H|` times the inner product `⟪f, f⟫`: expand
the inner product and use `z * conj z = (normSq z : ℂ)`. -/
private theorem sum_normSq_eq_card_mul_cfInner {H : Type*} [Group H] [Fintype H] (f : H → ℂ) :
    ((∑ u : H, Complex.normSq (f u) : ℝ) : ℂ)
      = (Fintype.card H : ℂ) * Work.Clifford.cfInner f f := by
  have h1 : (∑ u : H, f u * (starRingEnd ℂ) (f u))
      = ((∑ u : H, Complex.normSq (f u) : ℝ) : ℂ) := by
    rw [Complex.ofReal_sum]
    exact Finset.sum_congr rfl (fun u _ => Complex.mul_conj (f u))
  rw [Work.Clifford.cfInner, h1]
  have hc : ((Fintype.card H : ℕ) : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr Fintype.card_ne_zero
  rw [← mul_assoc, mul_inv_cancel₀ hc, one_mul]

theorem part2_count_resNorm {G : Type*} [Group G] [Fintype G] {N : Subgroup G} [N.Normal]
    [Fintype ↥N] {θ : ↥N → ℂ} (hθ : θ ∈ Work.Clifford.Irr ↥N) {χ : G → ℂ} {e : ℕ}
    (hres : Work.Clifford.resFun N χ = (e : ℂ) • Work.Clifford.orbitSum N θ) :
    ∑ u : ↥N, Complex.normSq (χ (u : G))
      = (e : ℝ) ^ 2 * ((Work.Clifford.charOrbit N θ).card : ℝ) * (Nat.card ↥N : ℝ) := by
  classical
  -- abbreviate the orbit sum
  set f : ↥N → ℂ := Work.Clifford.orbitSum N θ with hf
  -- the hypothesis, pointwise: `χ u = e * f u` for `u : N`
  have hpt : ∀ u : ↥N, χ (u : G) = (e : ℂ) * f u := by
    intro u
    have h := congrFun hres u
    simpa [Work.Clifford.resFun, f] using h
  -- step 1: pull the factor `e` out of the sum of squared norms
  have hstep1 : (∑ u : ↥N, Complex.normSq (χ (u : G)))
      = (e : ℝ) ^ 2 * ∑ u : ↥N, Complex.normSq (f u) := by
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun u _ => ?_
    rw [hpt u, Complex.normSq_mul]
    congr 1
    rw [← Complex.ofReal_natCast, Complex.normSq_ofReal]
    ring
  -- step 2: the norm of the orbit sum is the size of the orbit, times `|N|`
  have hstep2 : (∑ u : ↥N, Complex.normSq (f u))
      = ((Work.Clifford.charOrbit N θ).card : ℝ) * (Nat.card ↥N : ℝ) := by
    have hb := sum_normSq_eq_card_mul_cfInner f
    rw [hf, part2_orbitSum_norm hθ] at hb
    have hb2 : ((∑ u : ↥N, Complex.normSq (f u)) : ℝ)
        = (Fintype.card ↥N : ℝ) * ((Work.Clifford.charOrbit N θ).card : ℝ) := by
      refine Complex.ofReal_inj.mp ?_
      rw [hb]
      push_cast
      ring
    rw [hb2, Nat.card_eq_fintype_card]
    ring
  rw [hstep1, hstep2]
  ring

end Work.Hering.AppVII
