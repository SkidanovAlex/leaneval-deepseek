import Mathlib
import Submission.Work.SSGRoute.H2locAux.Defs
import Submission.Work.SSGRoute.Interfaces
import Submission.Work.SSGRoute.isCoboundary2On_top_of_isProPrimeToP
import Submission.Work.SSGRoute.coboundary2_top_of_coboundary2_on_coprime_index
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

set_option linter.style.haveILetI false
set_option linter.unusedVariables false

namespace Work.SSGRoute.PT

/-- Let `Γ` be a compact topological group, `W ⊴ Γ` a closed normal subgroup that is
pro-prime-to-`p` (`Work.SSGRoute.IsProPrimeToP p ↥W`), `N` a finite `𝔽_p`-module on which `Γ`
acts through `act : Γ →* G`, and `c : Γ × Γ → N` a locally constant `2`-cocycle.  Then there is a
locally constant `1`-cochain `b : Γ → N` whose coboundary reproduces `c` on the whole of
`Γ × W`.

The construction averages `c (g, ·)` over the finite coset space `W ⧸ U` for an open normal
subgroup `U ≤ W` whose index is invertible in `𝔽_p` (the index is coprime to `p` because `W` is
pro-prime-to-`p`); the cocycle identity expresses the coboundary of the average as
`n • c (g, w)` plus a telescoping difference of sums, which cancels because left multiplication by
`w` permutes the cosets. -/
theorem exists_primitive_vanishing_on_proPrimeToP
    (p : ℕ) [Fact p.Prime] {Γ G N : Type} [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ]
    [CompactSpace Γ] [Group G] [AddCommGroup N] [Module (ZMod p) N] [DistribMulAction G N]
    [SMulCommClass G (ZMod p) N] [Finite N]
    (act : Γ →* G) (W : Subgroup Γ) (hWn : W.Normal) (hWcl : IsClosed (W : Set Γ))
    (hWpro : Work.SSGRoute.IsProPrimeToP p ↥W)
    (c : Γ → Γ → N) (hc : SSGRoute.IsCocycle2 act c)
    (hlc : SSGRoute.IsLocConst2 c) :
    ∃ b : Γ → N, SSGRoute.IsLocConstOn (⊤ : Subgroup Γ) b ∧
      ∀ g : Γ, ∀ w ∈ W, c g w = act g • b w - b (g * w) + b g := by
  classical
  haveI hWn' : W.Normal := hWn
  haveI : CompactSpace ↥W := isCompact_iff_compactSpace.mp hWcl.isCompact
  -- local constancy of `c` gives an open subgroup `U₀ ≤ Γ`
  obtain ⟨U₀, hU₀open, hU₀inv⟩ := hlc
  -- `U₀` intersected with `W`, an open subgroup of `↥W` of finite index
  let U₀W : Subgroup ↥W := U₀.comap W.subtype
  have hU₀Wopen : IsOpen (U₀W : Set ↥W) := hU₀open.preimage continuous_subtype_val
  haveI : Finite (↥W ⧸ U₀W) := Subgroup.quotient_finite_of_isOpen U₀W hU₀Wopen
  haveI : U₀W.FiniteIndex := Subgroup.finiteIndex_of_finite_quotient
  -- its normal core: a normal finite-index subgroup of `↥W` on which `c` is invariant
  let U : Subgroup ↥W := U₀W.normalCore
  haveI : U.Normal := Subgroup.normalCore_normal U₀W
  haveI : U.FiniteIndex := inferInstance
  have hUle : U ≤ U₀W := Subgroup.normalCore_le U₀W
  have hcopP : Nat.Coprime U.index p := (hWpro U inferInstance).symm
  letI : Fintype (↥W ⧸ U) := Subgroup.fintypeQuotientOfFiniteIndex (H := U)
  let n : ℕ := U.index
  -- the averaged cochain
  let C : Γ → N := fun σ => ∑ q : ↥W ⧸ U, c σ ((Quotient.out q : ↥W) : Γ)
  -- invariance of `c` under right multiplication by elements of `U`
  have hUinv : ∀ (σ : Γ) (x h : ↥W), h ∈ U → c σ ((x : Γ) * (h : Γ)) = c σ (x : Γ) := by
    intro σ x h hh
    have hhU₀ : (h : Γ) ∈ U₀ := (Subgroup.mem_comap).mp (hUle hh)
    have h := hU₀inv σ (x : Γ) 1 (h : Γ) U₀.one_mem hhU₀
    simpa using h
  -- the averaged cochain has coboundary `n • c`
  have hC : ∀ (σ : Γ) (τ : ↥W),
      act σ • C (τ : Γ) - C (σ * (τ : Γ)) + C σ = n • c σ (τ : Γ) := by
    intro σ τ
    have hterm : ∀ q : ↥W ⧸ U,
        act σ • c (τ : Γ) ((Quotient.out q : ↥W) : Γ)
          - c (σ * (τ : Γ)) ((Quotient.out q : ↥W) : Γ)
          + c σ ((Quotient.out q : ↥W) : Γ)
        = c σ (τ : Γ) + c σ ((Quotient.out q : ↥W) : Γ)
          - c σ ((τ : Γ) * ((Quotient.out q : ↥W) : Γ)) := by
      intro q
      have h := hc σ (τ : Γ) ((Quotient.out q : ↥W) : Γ)
      have hA := cob2_solve3 h
      rw [hA]; abel
    have hperm : (∑ q : ↥W ⧸ U, c σ ((τ : Γ) * ((Quotient.out q : ↥W) : Γ)))
        = ∑ q : ↥W ⧸ U, c σ ((Quotient.out q : ↥W) : Γ) := by
      have h1 : ∀ q : ↥W ⧸ U, c σ ((τ : Γ) * ((Quotient.out q : ↥W) : Γ))
          = c σ (((Quotient.out (QuotientGroup.mk' U τ * q) : ↥W)) : Γ) := by
        intro q
        obtain ⟨h, hh, hx⟩ := cob2_exists_decomp U (τ * Quotient.out q)
        have hq : QuotientGroup.mk' U (τ * Quotient.out q) = QuotientGroup.mk' U τ * q := by
          rw [map_mul, QuotientGroup.mk'_apply, QuotientGroup.mk'_apply, QuotientGroup.out_eq']
        have hxΓ : (τ : Γ) * ((Quotient.out q : ↥W) : Γ)
            = ((Quotient.out (QuotientGroup.mk' U (τ * Quotient.out q)) : ↥W) : Γ) * (h : Γ) := by
          have := congrArg (fun x : ↥W => (x : Γ)) hx
          simpa using this
        rw [hxΓ, hUinv σ (Quotient.out (QuotientGroup.mk' U (τ * Quotient.out q))) h hh]
        rw [hq]
      rw [Finset.sum_congr rfl (fun q _ => h1 q)]
      exact Equiv.sum_comp (Equiv.mulLeft (QuotientGroup.mk' U τ))
        (fun q => c σ ((Quotient.out q : ↥W) : Γ))
    have hsum : act σ • C (τ : Γ) - C (σ * (τ : Γ)) + C σ
        = (∑ q : ↥W ⧸ U, c σ (τ : Γ))
          + (∑ q : ↥W ⧸ U, c σ ((Quotient.out q : ↥W) : Γ))
          - (∑ q : ↥W ⧸ U, c σ ((τ : Γ) * ((Quotient.out q : ↥W) : Γ))) := by
      have hL : act σ • C (τ : Γ) - C (σ * (τ : Γ)) + C σ
          = ∑ q : ↥W ⧸ U, (act σ • c (τ : Γ) ((Quotient.out q : ↥W) : Γ)
              - c (σ * (τ : Γ)) ((Quotient.out q : ↥W) : Γ)
              + c σ ((Quotient.out q : ↥W) : Γ)) := by
        show act σ • (∑ q : ↥W ⧸ U, c (τ : Γ) ((Quotient.out q : ↥W) : Γ))
            - (∑ q : ↥W ⧸ U, c (σ * (τ : Γ)) ((Quotient.out q : ↥W) : Γ))
            + (∑ q : ↥W ⧸ U, c σ ((Quotient.out q : ↥W) : Γ)) = _
        rw [Finset.smul_sum, ← Finset.sum_sub_distrib, ← Finset.sum_add_distrib]
      have hR : (∑ q : ↥W ⧸ U, c σ (τ : Γ)) + (∑ q : ↥W ⧸ U, c σ ((Quotient.out q : ↥W) : Γ))
          - (∑ q : ↥W ⧸ U, c σ ((τ : Γ) * ((Quotient.out q : ↥W) : Γ)))
          = ∑ q : ↥W ⧸ U, (c σ (τ : Γ) + c σ ((Quotient.out q : ↥W) : Γ)
              - c σ ((τ : Γ) * ((Quotient.out q : ↥W) : Γ))) := by
        rw [← Finset.sum_add_distrib, ← Finset.sum_sub_distrib]
      rw [hL, hR]
      exact Finset.sum_congr rfl (fun q _ => hterm q)
    rw [hsum, hperm]
    have hcard : Fintype.card (↥W ⧸ U) = n := by
      rw [Fintype.card_eq_nat_card, ← Subgroup.index_eq_card]
    simp only [Finset.sum_const, Finset.card_univ, hcard]
    abel
  have hn_ne : (((n : ℕ)) : ZMod p) ≠ 0 :=
    ((ZMod.isUnit_iff_coprime n p).mpr hcopP).ne_zero
  refine ⟨fun σ => ((n : ZMod p))⁻¹ • C σ, ⟨U₀, hU₀open, ?_⟩, ?_⟩
  · -- local constancy of the averaged cochain
    intro σ _ u hu _
    show ((n : ZMod p))⁻¹ • C (σ * u) = ((n : ZMod p))⁻¹ • C σ
    congr 1
    show (∑ q : ↥W ⧸ U, c (σ * u) ((Quotient.out q : ↥W) : Γ))
        = ∑ q : ↥W ⧸ U, c σ ((Quotient.out q : ↥W) : Γ)
    apply Finset.sum_congr rfl
    intro q _
    have h := hU₀inv σ ((Quotient.out q : ↥W) : Γ) u 1 hu U₀.one_mem
    simpa using h
  · -- the coboundary relation on `Γ × W`
    intro g w hw
    have hCτ := hC g ⟨w, hw⟩
    simp only at hCτ
    show c g w = act g • (((n : ZMod p))⁻¹ • C w) - ((n : ZMod p))⁻¹ • C (g * w)
        + ((n : ZMod p))⁻¹ • C g
    rw [smul_comm (act g) (((n : ZMod p))⁻¹) (C w), ← smul_sub, ← smul_add, hCτ,
      ← Nat.cast_smul_eq_nsmul (ZMod p) n (c g w), smul_smul]
    rw [inv_mul_cancel₀ hn_ne, one_smul]

end Work.SSGRoute.PT
