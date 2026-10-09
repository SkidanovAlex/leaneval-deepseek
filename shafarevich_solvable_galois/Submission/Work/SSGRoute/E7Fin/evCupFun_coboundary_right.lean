import Mathlib
import Submission.Work.SSGRoute.E7Fin.cupPairing
import Submission.Work.SSGRoute.E7Fin.evCupFun_coboundary_left
import Submission.Work.SSGRoute.Interfaces
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace Work.SSGRoute.E7Fin

open SSGRoute
open scoped TensorProduct

/-- **The cup product of a `1`-cocycle with a `1`-coboundary is a `2`-coboundary** (the mirror of
`E7Fin.evCupFun_coboundary_left`; together they give clause (3) of the local pairing list for the
cup-generated family): if `a` is a locally constant `1`-cocycle on `H` and `b h = res h • n - n` for
`h ∈ H` with `n : DualMod p (M ⊗ T)`, then `evCupFun a b` is a `2`-coboundary, with cobounding
cochain `g ↦ -evLin (a g ⊗ (g • n))` (the negative of the cup `a ∪ n` of the `1`-cocycle `a` with
the `0`-cochain `n`).

Indeed, writing `act g = res k K g`, `b h = act h • n - n` gives
`evCupFun a b (g,h) = evLin (a g ⊗ (act g * act h) • n) - evLin (a g ⊗ act g • n)`, while
`δ z (g,h) = act g • z h - z (g * h) + z g` for `z g = evLin (a g ⊗ act g • n)` and the cocycle
identity `a (g*h) = a g + act g • a h`; the Leibniz rule `δ(a ∪ n) = δa ∪ n - a ∪ δn` gives
`δz = -evCupFun a b`, so the witness is `-z`.  All of this uses the diagonal action `hdiagM`.

The cobounding cochain must be *locally constant* on `H`; this is the hypothesis `hstab`, that the
orbit map `g ↦ res k K g • n` is locally constant for every `n : DualMod p (M ⊗ T)` (the module `b`
lands in — the orbit maps for `M` itself are *not* what is needed here).  For the intended
coefficients (`DualMod p (M ⊗ T)` an `𝔽_p[Gal(K/k)]`-module with `K/k` finite) `hstab` is
automatic: the stabiliser of `n` has finite index in the finite group `Gal(K/k)`, so its preimage
under the continuous `res k K` is an open subgroup of `G_k`; `hstab` is kept as a hypothesis to
avoid the Krull-topology machinery here. -/
theorem evCupFun_coboundary_right
    (p : ℕ) [Fact p.Prime] (k Ω : Type) [Field k] [Field Ω] [Algebra k Ω]
    (K : IntermediateField k Ω) [Normal k K] (T : Type) [AddCommGroup T] [Module (ZMod p) T]
    [DistribMulAction (K ≃ₐ[k] K) T] [SMulCommClass (K ≃ₐ[k] K) (ZMod p) T]
    (M : Type) [AddCommGroup M] [Module (ZMod p) M] [DistribMulAction (K ≃ₐ[k] K) M]
    [SMulCommClass (K ≃ₐ[k] K) (ZMod p) M]
    [DistribMulAction (K ≃ₐ[k] K) (TensorProduct (ZMod p) M T)]
    [SMulCommClass (K ≃ₐ[k] K) (ZMod p) (TensorProduct (ZMod p) M T)]
    (hdiagM : ∀ (g : K ≃ₐ[k] K) (x : M) (t : T),
      g • (TensorProduct.tmul (ZMod p) x t) = TensorProduct.tmul (ZMod p) (g • x) (g • t))
    (H : Subgroup (Ω ≃ₐ[k] Ω))
    (a : (Ω ≃ₐ[k] Ω) → M)
    (b : (Ω ≃ₐ[k] Ω) → Work.SSGRoute.DualMod p (TensorProduct (ZMod p) M T))
    (ha : SSGRoute.IsCocycleOn (SSGRoute.res k K) H a)
    (ha_lc : SSGRoute.IsLocConstOn H a)
    (hb : SSGRoute.IsCoboundaryOn (SSGRoute.res k K) H b)
    (hstab : ∀ n : Work.SSGRoute.DualMod p (TensorProduct (ZMod p) M T),
      SSGRoute.IsLocConstOn H (fun g => SSGRoute.res k K g • n)) :
    SSGRoute.IsCoboundary2On (SSGRoute.res k K) H
      (Work.SSGRoute.E7Fin.evCupFun p k Ω K T M a b) := by
  obtain ⟨n, hn⟩ := hb
  obtain ⟨Ua, hUa_open, hUa⟩ := ha_lc
  obtain ⟨Un, hUn_open, hUn⟩ := hstab n
  refine ⟨fun g => - evLin p M T (TensorProduct.tmul (ZMod p) (a g) (SSGRoute.res k K g • n)),
    ⟨Ua ⊓ Un, ?_, ?_⟩, ?_⟩
  · rw [Subgroup.coe_inf]
    exact hUa_open.inter hUn_open
  · intro g hg u hu huH
    have h1 : a (g * u) = a g := hUa g hg u hu.1 huH
    have h2 : SSGRoute.res k K (g * u) • n = SSGRoute.res k K g • n := hUn g hg u hu.2 huH
    simp only [h1, h2]
  · intro g hg h hh
    have hact : SSGRoute.res k K g • (SSGRoute.res k K h • n) =
        SSGRoute.res k K (g * h) • n := by
      rw [← mul_smul, ← map_mul]
    have hbh : SSGRoute.res k K g • b h =
        SSGRoute.res k K (g * h) • n - SSGRoute.res k K g • n := by
      rw [hn h hh, smul_sub, hact]
    have hL : evLin p M T (TensorProduct.tmul (ZMod p) (a g) (SSGRoute.res k K g • b h))
        = evLin p M T (TensorProduct.tmul (ZMod p) (a g) (SSGRoute.res k K (g * h) • n))
          - evLin p M T (TensorProduct.tmul (ZMod p) (a g) (SSGRoute.res k K g • n)) := by
      rw [hbh, TensorProduct.tmul_sub, map_sub]
    have hRh : SSGRoute.res k K g
          • (- evLin p M T (TensorProduct.tmul (ZMod p) (a h) (SSGRoute.res k K h • n)))
        = - evLin p M T (TensorProduct.tmul (ZMod p) (SSGRoute.res k K g • a h)
            (SSGRoute.res k K (g * h) • n)) := by
      rw [smul_neg, smul_evLin_tmul p k Ω K T M hdiagM, hact]
    have hRm : - evLin p M T (TensorProduct.tmul (ZMod p) (a (g * h)) (SSGRoute.res k K (g * h) • n))
        = - (evLin p M T (TensorProduct.tmul (ZMod p) (a g) (SSGRoute.res k K (g * h) • n))
            + evLin p M T (TensorProduct.tmul (ZMod p) (SSGRoute.res k K g • a h)
                (SSGRoute.res k K (g * h) • n))) := by
      rw [ha g hg h hh, TensorProduct.add_tmul, map_add]
    show evLin p M T (TensorProduct.tmul (ZMod p) (a g) (SSGRoute.res k K g • b h))
        = SSGRoute.res k K g
            • (- evLin p M T (TensorProduct.tmul (ZMod p) (a h) (SSGRoute.res k K h • n)))
          - (- evLin p M T (TensorProduct.tmul (ZMod p) (a (g * h)) (SSGRoute.res k K (g * h) • n)))
          + (- evLin p M T (TensorProduct.tmul (ZMod p) (a g) (SSGRoute.res k K g • n)))
    rw [hL, hRh, hRm]
    abel

end Work.SSGRoute.E7Fin
