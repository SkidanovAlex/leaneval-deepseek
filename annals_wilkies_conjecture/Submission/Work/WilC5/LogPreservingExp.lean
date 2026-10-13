import Mathlib
import Submission.Work.WilC5.S4StepNewSetup
import Submission.Work.WilC5.expE_of_logFun_preserving
import Submission.Work.WilC5.logFun_expE
import Submission.Work.WilC5.expE_lt_iff_logFun_lt

set_option autoImplicit false
set_option maxHeartbeats 1000000
noncomputable section
open Classical

namespace Work.WilC5

open WilkiesDesign WilkiesDesign.CG FirstOrder FirstOrder.Language

/-! ## Auxiliary facts about the `LRc`-constants `0` and `1`

The constants `0` and `1` of `LRc` are the ring symbols `ringSymL Ring.zeroFunc` and
`ringSymL Ring.oneFunc`; the corresponding `LEc`-values are `zeroE` and `oneE`.  The four lemmas
below record that a substructure's `0` and `1` coerce to the ambient ones and that an `LRc`-embedding
sends them to the target's `0` and `1`.  They are needed only in the degenerate case `τ b = 0` of the
main proof, where the logarithm does *not* separate `τ (exp b)` from `exp (τ b)`. -/

/-- The `LRc`-zero of a substructure, seen in the ambient structure, is the ambient `LRc`-zero. -/
theorem coe_zeroEL_sub {K : Type} [LEc.Structure K] (B : LRc.Substructure K) :
    ((zeroEL : ↥B) : K) = (zeroE : K) := by
  show (Substructure.subtype B)
      (@Structure.funMap LRc ↥B _ 0 (ringSymL Ring.zeroFunc) (![] : Fin 0 → ↥B)) = (zeroE : K)
  have h := (Substructure.subtype B).map_fun (ringSymL Ring.zeroFunc) (![] : Fin 0 → ↥B)
  have h2 : ((Substructure.subtype B) ∘ (![] : Fin 0 → ↥B)) = (![] : Fin 0 → K) := by
    funext i; exact Fin.elim0 i
  rw [h2] at h; rw [h]
  show @Structure.funMap LRc K _ 0 (Sum.inl (Sum.inl Ring.zeroFunc)) (![] : Fin 0 → K) = (zeroE : K)
  rw [reductStruct_funMap_ring]; rfl

/-- The `LRc`-one of a substructure, seen in the ambient structure, is the ambient `LRc`-one. -/
theorem coe_oneEL_sub {K : Type} [LEc.Structure K] (B : LRc.Substructure K) :
    ((oneEL : ↥B) : K) = (oneE : K) := by
  show (Substructure.subtype B)
      (@Structure.funMap LRc ↥B _ 0 (ringSymL Ring.oneFunc) (![] : Fin 0 → ↥B)) = (oneE : K)
  have h := (Substructure.subtype B).map_fun (ringSymL Ring.oneFunc) (![] : Fin 0 → ↥B)
  have h2 : ((Substructure.subtype B) ∘ (![] : Fin 0 → ↥B)) = (![] : Fin 0 → K) := by
    funext i; exact Fin.elim0 i
  rw [h2] at h; rw [h]
  show @Structure.funMap LRc K _ 0 (Sum.inl (Sum.inl Ring.oneFunc)) (![] : Fin 0 → K) = (oneE : K)
  rw [reductStruct_funMap_ring]; rfl

/-- An `LRc`-embedding of a substructure sends the substructure's `LRc`-zero to the target's. -/
theorem map_zeroEL_embed {K L : Type} [LEc.Structure K] [LEc.Structure L]
    (B : LRc.Substructure K) (τ : LRc.Embedding ↥B L) :
    τ (zeroEL : ↥B) = (zeroE : L) := by
  show τ (@Structure.funMap LRc ↥B _ 0 (ringSymL Ring.zeroFunc) (![] : Fin 0 → ↥B)) = (zeroE : L)
  have h := τ.map_fun (ringSymL Ring.zeroFunc) (![] : Fin 0 → ↥B)
  have h2 : (τ ∘ (![] : Fin 0 → ↥B)) = (![] : Fin 0 → L) := by
    funext i; exact Fin.elim0 i
  rw [h2] at h; rw [h]
  show @Structure.funMap LRc L _ 0 (Sum.inl (Sum.inl Ring.zeroFunc)) (![] : Fin 0 → L) = (zeroE : L)
  rw [reductStruct_funMap_ring]; rfl

/-- An `LRc`-embedding of a substructure sends the substructure's `LRc`-one to the target's. -/
theorem map_oneEL_embed {K L : Type} [LEc.Structure K] [LEc.Structure L]
    (B : LRc.Substructure K) (τ : LRc.Embedding ↥B L) :
    τ (oneEL : ↥B) = (oneE : L) := by
  show τ (@Structure.funMap LRc ↥B _ 0 (ringSymL Ring.oneFunc) (![] : Fin 0 → ↥B)) = (oneE : L)
  have h := τ.map_fun (ringSymL Ring.oneFunc) (![] : Fin 0 → ↥B)
  have h2 : (τ ∘ (![] : Fin 0 → ↥B)) = (![] : Fin 0 → L) := by
    funext i; exact Fin.elim0 i
  rw [h2] at h; rw [h]
  show @Structure.funMap LRc L _ 0 (Sum.inl (Sum.inl Ring.oneFunc)) (![] : Fin 0 → L) = (oneE : L)
  rw [reductStruct_funMap_ring]; rfl

/-! ## The key elementary consequence of uniqueness of the logarithm

`logDefSet x y` is the graph of the definable logarithm.  For `y ≠ 0` it determines `x`: the second
clause of `logDefSet` forces `exp y = 1`, hence `y = 0` by injectivity of `exp`. -/

/-- If `x` is a logarithm of a *non-zero* `y` in a model of `TE`, then `x = exp y`. -/
theorem eq_of_logDefSet_of_ne_zero {M : Type} [LEc.Structure M] (hM : M ⊨ TE) {x y : M}
    (h : logDefSet x y) (hy : y ≠ (zeroE : M)) : x = expE y := by
  rcases h with ⟨_, hxy⟩ | ⟨_, hxy⟩
  · exact hxy.symm
  · exact absurd (expE_injective_of_model hM y zeroE (by rw [hxy, expE_zero_of_model hM])) hy

/-- **A log-preserving embedding of a `Dcl`-closed substructure preserves the exponential.**  `K`
and `L` are models of `TE`, `B ≤ K` is an `LRc`-substructure closed under the definable logarithm
and under the exponential, and `τ : B → L` is an `LRc`-embedding commuting with the definable
logarithm on `B`.  Then `τ` also commutes with the exponential on `B`.

This is the substructure form of `Work.WilC5.expE_of_logFun_preserving` (which is stated for
embeddings `K → L` of whole models), and it is the last structural input of the §4 iteration: the
`S4Pair` of the iteration carries log-preservation as its invariant, and the transport lemmas of
Claim 3 (`Work.WilC5.StepSeqCutStep`) take exp-preservation of `τ` on `B` as a hypothesis.

Proof: for `b : ↥B`, `logFun (expE b) = b` in `K` (`Work.WilC5.logFun_expE`), so
`logFun (τ ⟨expE b, _⟩) = τ b` by log-preservation; hence both `τ ⟨expE b, _⟩` and `expE (τ b)`
satisfy `logDefSet · (τ b)` in the model `L ⊨ TE`, and uniqueness of the logarithm in a model of
`TE` gives the claim.  (No positivity of `τ (expE b)` is needed.) -/
theorem LogPreservingExp
    {K L : Type} [WilkiesDesign.CG.LEc.Structure K] [WilkiesDesign.CG.LEc.Structure L]
    [Field L]
    (hK : K ⊨ WilkiesDesign.CG.TE) (hL : L ⊨ WilkiesDesign.CG.TE)
    {B : WilkiesDesign.CG.LRc.Substructure K}
    (hBlog : ∀ x ∈ (B : Set K), Work.WilC5.logFun x ∈ (B : Set K))
    (hBexp : ∀ x ∈ (B : Set K), Work.WilC5.expE x ∈ (B : Set K))
    (τ : WilkiesDesign.CG.LRc.Embedding ↥B L)
    (hτlog : ∀ b : ↥B,
      τ ⟨Work.WilC5.logFun (b : K), hBlog (b : K) b.2⟩ = Work.WilC5.logFun (τ b)) :
    ∀ b : ↥B, τ ⟨Work.WilC5.expE (b : K), hBexp (b : K) b.2⟩ = Work.WilC5.expE (τ b) := by
  intro b
  -- the `LRc`-constants `0` and `1`: their coercion to `K` and their image under `τ`
  have hτ0 : τ (zeroEL : ↥B) = (zeroE : L) := map_zeroEL_embed B τ
  have hτ1 : τ (oneEL : ↥B) = (oneE : L) := map_oneEL_embed B τ
  have hc0 : ((zeroEL : ↥B) : K) = (zeroE : K) := coe_zeroEL_sub B
  have hc1 : ((oneEL : ↥B) : K) = (oneE : K) := coe_oneEL_sub B
  -- ## 1. log-preservation identifies the logarithm of `τ ⟨exp b, _⟩`
  have hlog_u : logFun (τ ⟨expE (b : K), hBexp (b : K) b.2⟩) = τ b := by
    have h := hτlog ⟨expE (b : K), hBexp (b : K) b.2⟩
    -- `logFun (expE b) = b`, so the argument of `τ` on the left is `b`
    have harg : (⟨logFun (expE (b : K)),
        hBlog (expE (b : K)) (hBexp (b : K) b.2)⟩ : ↥B) = b := by
      apply Subtype.ext
      exact logFun_expE hK (b : K)
    rw [harg] at h
    exact h.symm
  by_cases hb : τ b = (zeroE : L)
  · -- ## 2a. the degenerate case `τ b = 0`: then `b = 0` and both sides are `1`
    have hbz : b = (zeroEL : ↥B) := τ.injective (hb.trans hτ0.symm)
    have hbK : (b : K) = (zeroE : K) := by rw [hbz, hc0]
    have hexpK : expE (b : K) = (oneE : K) := by rw [hbK, expE_zero_of_model hK]
    have huH : (⟨expE (b : K), hBexp (b : K) b.2⟩ : ↥B) = (oneEL : ↥B) := by
      apply Subtype.ext
      show expE (b : K) = ((oneEL : ↥B) : K)
      rw [hexpK, hc1]
    rw [huH, hτ1, hb, expE_zero_of_model hL]
  · -- ## 2b. otherwise `logDefSet · (τ b)` pins down its argument as `expE (τ b)`
    have hspec : logDefSet (τ ⟨expE (b : K), hBexp (b : K) b.2⟩) (τ b) := by
      rw [← hlog_u]
      exact logFun_spec_of_model hL _
    exact eq_of_logDefSet_of_ne_zero hL hspec hb

end Work.WilC5
