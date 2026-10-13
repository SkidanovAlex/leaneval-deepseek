import Mathlib
import Submission.Work.DSM5c.Untilt.Basic

/-!
# `p`-torsion-freeness of the untilt

For `R` a perfect ring of characteristic `p` and `w ∈ R` a non-zero-divisor, the untilt

  `untilt p R w = 𝕎 R ⧸ (ξ)`,  `ξ = [w] - p`

is `p`-torsion-free: `p` is a non-zero-divisor on `untilt p R w`.  This is the first structural
property listed in the PB3 design (`sources/dsmap/direct_summand_mix_design.md` §3, "`D_I` is
`p`-torsion-free because `D_I♭` is `t`-torsion-free"): the tilt of the chart is `t`-torsion-free,
i.e. `w` is a non-zero-divisor of `R`, and this is inherited by the untilt.

## Proof

Let `x : 𝕎 R` with `p · x ∈ (ξ)`; we must show `x ∈ (ξ)`.

1. Write `p·x = ξ·a`.  Since `[w] = ξ + p`, we get `[w]·a = ξ·a + p·a = p·(x + a) ∈ (p)`.
2. Apply `constantCoeff : 𝕎 R →+* R`.  On `[w]·a` it gives `w · constantCoeff a`; on `p·(x+a)` it
   gives `constantCoeff p · … = 0` because `p = 0` in `R`.  Hence `w · constantCoeff a = 0`, and
   since `w` is a non-zero-divisor, `constantCoeff a = 0`, i.e. `a ∈ ker constantCoeff = (p)`
   (`WittVector.ker_constantCoeff`); write `a = p·c`.
3. Then `p·x = ξ·a = ξ·(p·c) = p·(ξ·c)`, so `p·(x - ξ·c) = 0`, and `𝕎 R` is `p`-torsion-free
   (`WittVector.eq_zero_of_p_mul_eq_zero`): `x = ξ·c ∈ (ξ)`.

Equivalently, in one slogan: `w` regular in `R` makes the reduction of `[w]` modulo `p` injective on
`𝕎 R ⧸ (p)`, and `[w] ≡ p (mod ξ)` upgrades this to `p`-regularity of `ξ = [w] - p`.  No
Frobenius iteration is needed: the single mod-`p` reduction above already suffices.
-/

namespace Work.DSM5c.Untilt

universe a

set_option linter.unusedSectionVars false

open WittVector

variable {p : ℕ} [Fact p.Prime] {R : Type a} [CommRing R] [CharP R p] [PerfectRing R p]

/-- `[w] = ξ + p` in `𝕎 R`.  (A local copy so that this module is self-contained.) -/
theorem teichmuller_eq_xi_add_ptf (w : R) :
    WittVector.teichmuller p w = xi p R w + (p : WittVector p R) := by
  rw [xi]
  abel

/-- The constant coefficient of `p : 𝕎 R` vanishes, `p` being `0` in the characteristic-`p` ring
`R`. -/
theorem constantCoeff_p_ptf :
    WittVector.constantCoeff (p : WittVector p R) = 0 := by
  rw [map_natCast (WittVector.constantCoeff (p := p) (R := R)) p, CharP.cast_eq_zero]

/-- The constant coefficient of a Teichmüller lift is the element itself. -/
theorem constantCoeff_teichmuller_ptf (w : R) :
    WittVector.constantCoeff (WittVector.teichmuller p w) = w := by
  rw [WittVector.constantCoeff_apply, WittVector.teichmuller_coeff_zero]

/-- **The key step**: a non-zero-divisor `w ∈ R` makes the Teichmüller lift `[w]` a non-zero-divisor
on `𝕎 R` *modulo* `p`: if `[w] · a ∈ (p)` then already `a ∈ (p)`.

Indeed, `constantCoeff` is the reduction modulo `p` (`WittVector.ker_constantCoeff`), and it sends
`[w] · a` to `w · constantCoeff a`; a non-zero-divisor `w` then forces `constantCoeff a = 0`. -/
theorem mem_span_p_of_teichmuller_mul_mem
    (w : R) (hw : ∀ x : R, w * x = 0 → x = 0) {a : WittVector p R}
    (ha : WittVector.teichmuller p w * a ∈ Ideal.span {(p : WittVector p R)}) :
    a ∈ Ideal.span {(p : WittVector p R)} := by
  have h : w * WittVector.constantCoeff a = 0 := by
    obtain ⟨c, hc⟩ := Ideal.mem_span_singleton.mp ha
    have h0 : WittVector.constantCoeff (WittVector.teichmuller p w * a) = 0 := by
      rw [hc, map_mul, constantCoeff_p_ptf, zero_mul]
    simpa [map_mul, constantCoeff_teichmuller_ptf] using h0
  have hca : WittVector.constantCoeff a = 0 := hw _ h
  rw [← WittVector.ker_constantCoeff]
  simpa using hca

/-- **`p`-torsion-freeness of the untilt.**  If `w` is a non-zero-divisor of the perfect
characteristic-`p` ring `R`, then `p` is a non-zero-divisor of `untilt p R w = 𝕎 R ⧸ ([w] - p)`. -/
theorem untilt_p_torsionFree (p : ℕ) [Fact p.Prime] (R : Type a) [CommRing R] [CharP R p] [PerfectRing R p] (w : R)
    (hw : ∀ x : R, w * x = 0 → x = 0) :
    IsSMulRegular (Work.DSM5c.untilt p R w) (p : Work.DSM5c.untilt p R w) := by
  have teich : WittVector.teichmuller p w = xi p R w + (p : WittVector p R) :=
    teichmuller_eq_xi_add_ptf w
  -- it suffices to kill `p`-torsion
  have key : ∀ y : untilt p R w, (p : untilt p R w) • y = 0 → y = 0 := by
    intro y hy
    obtain ⟨x, rfl⟩ := Ideal.Quotient.mk_surjective y
    rw [smul_eq_mul] at hy
    have hpmk : (p : untilt p R w) =
        Ideal.Quotient.mk (Ideal.span {xi p R w}) (p : WittVector p R) :=
      (map_natCast (Ideal.Quotient.mk (Ideal.span {xi p R w})) p).symm
    rw [hpmk, ← map_mul] at hy
    have hmem : (p : WittVector p R) * x ∈ Ideal.span {xi p R w} :=
      Ideal.Quotient.eq_zero_iff_mem.mp hy
    obtain ⟨a, ha⟩ := Ideal.mem_span_singleton.mp hmem
    -- `[w] · a = p · (x + a)`, hence `a ∈ (p)`
    have hmem_p : a ∈ Ideal.span {(p : WittVector p R)} := by
      refine mem_span_p_of_teichmuller_mul_mem w hw ?_
      rw [show WittVector.teichmuller p w * a = (p : WittVector p R) * (x + a) from by
        rw [teich, add_mul, ← ha, ← mul_add]]
      exact Ideal.mem_span_singleton.mpr ⟨x + a, rfl⟩
    obtain ⟨c, hc⟩ := Ideal.mem_span_singleton.mp hmem_p
    -- `p · (x - ξ·c) = p·x - p·(ξ·c) = ξ·a - ξ·(p·c) = 0`, and `𝕎 R` is `p`-torsion-free
    have hx : x = xi p R w * c := by
      have h : (p : WittVector p R) * (x - xi p R w * c) = 0 := by
        rw [mul_sub, ha, hc]
        ring
      have h' : (x - xi p R w * c) * (p : WittVector p R) = 0 := by
        simpa [mul_comm] using h
      exact sub_eq_zero.mp
        (WittVector.eq_zero_of_p_mul_eq_zero (p := p) (k := R) (x - xi p R w * c) h')
    rw [Ideal.Quotient.eq_zero_iff_mem]
    exact Ideal.mem_span_singleton.mpr ⟨c, hx⟩
  -- conclude injectivity from `p`-torsion-freeness
  intro y z hyz
  have hyz' : (p : untilt p R w) * y = (p : untilt p R w) * z := by
    simpa [smul_eq_mul] using hyz
  have h0 : (p : untilt p R w) * (y - z) = 0 := by rw [mul_sub, hyz', sub_self]
  exact sub_eq_zero.mp (key (y - z) (by simpa [smul_eq_mul] using h0))

end Work.DSM5c.Untilt
