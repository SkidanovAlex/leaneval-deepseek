import Submission.ZagierHoffmanProof.AmbInf
import Submission.ZagierHoffmanProof.Block

/-!
# The transfer of `ζ_A` to the ambient field

`AmbInf.lean` builds the ring hom `ambInfHom : CompletionAtInfty F →+* Ambient F` extending
`ambKEquiv`.  Here we push the *defining sum* of `ζ_A` through it: since `ambInfHom` is continuous
and the `ζ_A`-summand family is summable, `HasSum.map` gives

  `ambInfHom (ζ_A F 𝔰) = ∑' a, (∏_i (ambKEquiv (a_i))(θ)^{𝔰_i})⁻¹`.

This is the `CompletionAtInfty`-side → `Ambient F`-side half of the MZV↔CMPL bridge.  In
particular it shows that **any `K`-linear relation between MZV's transfers to `Ambient F`**.
-/

set_option autoImplicit false
open Polynomial
open scoped WithZero Topology RatFunc.CompletionAtInfty

namespace ZagierHoffmanPositiveChar

variable (F : Type*) [Field F] [Finite F] [DecidableEq (RatFunc F)]

/-- **The main transfer statement**: the value of `ζ_A(𝔰)` inside `Ambient F` is obtained by
pushing `ambKEquiv` through the defining sum. -/
theorem ambInfHom_zeta_A {r : ℕ} (hr : 0 < r) (𝔰 : Fin r → ℕ+) :
    ambInfHom F (ζ_A F 𝔰) = ∑' a : monicStrictAntiNatDegree F r,
      (∏ i : Fin r, ((ambKEquiv F (a.val i : RatFunc F)) : Ambient F) ^ (𝔰 i : ℕ))⁻¹ := by
  have hsum : Summable (fun a : monicStrictAntiNatDegree F r =>
      (∏ i : Fin r, (((a.val i : Polynomial F) : RatFunc F) :
        RatFunc.CompletionAtInfty F) ^ (𝔰 i : ℕ))⁻¹) :=
    summable_zeta_term F hr 𝔰
  have h := hsum.hasSum.map (ambInfHom F) (continuous_ambInfHom F)
  have hzeta : ζ_A F 𝔰 = ∑' a : monicStrictAntiNatDegree F r,
      (∏ i : Fin r, (((a.val i : Polynomial F) : RatFunc F) :
        RatFunc.CompletionAtInfty F) ^ (𝔰 i : ℕ))⁻¹ := by
    rw [ζ_A_eq_tsum_zetaTerm]
    exact tsum_congr fun a => (zetaTerm_eq_zetaTermAux F 𝔰 a).symm
  rw [hzeta]
  refine h.tsum_eq.symm.trans ?_
  refine tsum_congr fun a => ?_
  simp only [Function.comp_apply, map_inv₀, map_prod, map_pow]
  congr 1
  exact Finset.prod_congr rfl fun i _ => by rw [ambInfHom_coe, ambKHomAmb_apply]

/-! ## §2. Transporting relations -/

/-- **A `K`-linear relation between MZV's transfers to `Ambient F`.**  This is the
`CompletionAtInfty F → Ambient F` half of Step 1 of ND21 §5: the relation used to start the proof
of Theorem B. -/
theorem ambInfHom_zeta_A_relation {ι : Type*} [Fintype ι]
    (r : ι → ℕ) (hr : ∀ i, 0 < r i) (𝔰 : ∀ i, Fin (r i) → ℕ+) (c : ι → RatFunc F)
    (h : ∑ i, c i • ζ_A F (𝔰 i) = 0) :
    ∑ i, ((ambKEquiv F (c i) : ↥(ambK F)) : Ambient F) * ambInfHom F (ζ_A F (𝔰 i)) = 0 := by
  have h1 : ∑ i, ambInfHom F (c i • ζ_A F (𝔰 i)) = 0 := by
    have := congrArg (ambInfHom F) h
    rwa [map_zero, map_sum] at this
  rw [← h1]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Algebra.smul_def, map_mul]
  congr 1
  have hcoe : (algebraMap (RatFunc F) (RatFunc.CompletionAtInfty F)) (c i)
      = ((c i : RatFunc.CompletionAtInfty F)) := rfl
  rw [hcoe, ambInfHom_coe, ambKHomAmb_apply]

end ZagierHoffmanPositiveChar
