import Mathlib
import Submission.Work.BG.S02
import Submission.Work.BG.Defs
import Submission.Work.BG.t_mem_zpowers_of_mem_T

namespace Work.BG

/-!
# Area BG — Bender–Glauberman 1981, Lemma 2.2(b): the involution-pair lemma

`InvolutionPairProp C` (BG p. 205): if `g ∈ T = H₀ ∖ U` is the product `x * y` of two
non-identity involutions `x, y` of `G`, then `x ∈ H` and `x ∉ H₀`.

This is the "L2.2-b" leaf of the BG §2 development: the pair `x, y` of involutions with
`x * y = g ∈ T` must lie in the coset `H ∖ H₀`.

The proof is elementary and uses only the TI condition of Hypothesis 1.2 and the fact that
`t` is the only involution of `H₀`:

* `x * g * x⁻¹ = g⁻¹` because `g = x * y` and `x, y` are involutions.  Since `g⁻¹ ∈ T`
  (`T` is closed under inversion), the TI condition `N_G(T) = H` (`Hyp12.mem_H_of_conj_mem`)
  applied to `g ∈ T` gives `x ∈ H`.
* If `x ∈ H₀`, then `x` is an involution of `H₀`, hence `x = t`; likewise `y = x⁻¹ * g` is an
  involution of `H₀`, hence `y = t`; then `g = x * y = 1 ∈ U`, contradicting `g ∉ U`.
-/

theorem s02_involutionPair {G : Type} [Group G] [Finite G] [Fintype G] [Invertible (Nat.card G : ℂ)]
    (C : Work.BG.Sec2Ctx G) : Work.BG.InvolutionPairProp C := by
  intro g hg x y hx2 hy2 hx1 hy1 hxy
  have hgH0 : g ∈ C.P.H0 := hg.1
  have hgU : g ∉ C.P.U := hg.2
  -- `x` and `y` are invertible by themselves.
  have hx2' : x * x = 1 := by rwa [pow_two] at hx2
  have hy2' : y * y = 1 := by rwa [pow_two] at hy2
  have hxinv : x⁻¹ = x := inv_eq_of_mul_eq_one_left hx2'
  have hyinv : y⁻¹ = y := inv_eq_of_mul_eq_one_left hy2'
  -- `x` inverts `g`.
  have hxgx : x * g * x⁻¹ = g⁻¹ := by
    rw [← hxy, mul_inv_rev, hyinv, hxinv]
    calc x * (x * y) * x = (x * x) * (y * x) := by group
      _ = 1 * (y * x) := by rw [hx2']
      _ = y * x := by rw [one_mul]
  -- `T` is closed under inversion.
  have hginvT : g⁻¹ ∈ Tset C.P.H0 C.P.U :=
    ⟨C.P.H0.inv_mem hgH0, fun h => hgU (C.P.U.inv_mem_iff.mp h)⟩
  refine ⟨?_, ?_⟩
  · -- `x * g * x⁻¹ ∈ T` with `g ∈ T`, so TI gives `x ∈ H`.
    exact Hyp12.mem_H_of_conj_mem C.P (g := x) (x := g) hg (hxgx ▸ hginvT)
  · -- `H₀` has the single involution `t`; `x, y ∈ H₀` would force `x = y = t`, `g = 1 ∈ U`.
    intro hxH0
    have hxt : x = (C.t : G) := (C.inv_H0 x hxH0 hx2).resolve_left hx1
    have hyH0 : y ∈ C.P.H0 := by
      have hyy : y = x⁻¹ * g := by rw [← hxy]; group
      rw [hyy]; exact C.P.H0.mul_mem (C.P.H0.inv_mem hxH0) hgH0
    have hyt : y = (C.t : G) := (C.inv_H0 y hyH0 hy2).resolve_left hy1
    have ht2G : (C.t : G) * (C.t : G) = 1 := by
      have := congrArg (fun z : ↥C.P.H0 => (z : G)) C.t_sq
      simpa [pow_two] using this
    have hg1 : g = 1 := by rw [← hxy, hxt, hyt, ht2G]
    exact hgU (hg1 ▸ C.P.U.one_mem)

end Work.BG
