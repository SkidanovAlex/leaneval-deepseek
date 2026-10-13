/-
  WilC5 — the *inverse* direction of `LogStructEmbedding`: if an `LRc`-embedding of the
  `rexp`-reducts of two models of `TE` preserves the definable logarithm, it preserves the full
  exponential.

  Let `K, L ⊨ TE`, and let `f : reductStruct K ↪[LRc] reductStruct L` be an embedding of the
  `rexp`-reducts (so `f` commutes with the ring operations, the real constants, and the
  *restricted* exponential `rexpFromExp`).  We are given that `f` commutes with the definable
  logarithm `logFun` (`ExpLog.lean`):

      `f (logFun x) = logFun (f x)`   for all `x : K`,

  and must deduce that it commutes with the *full* exponential `expE`:

      `f (expE x) = expE (f x)`   for all `x : K`.

  The proof is entirely through the logarithm, which is the inverse of the exponential in a model
  of `TE` (`logFun_expE.lean`, `expE_lt_iff_logFun_lt.lean`):

  * `logFun (expE x) = x`, so applying `f` and the hypothesis `hf` gives
    `logFun (f (expE x)) = f x`, and by the same token `logFun (expE (f x)) = f x`; hence
    `logFun (f (expE x)) = logFun (expE (f x))`;
  * both `f (expE x)` and `expE (f x)` are strictly positive — `expE` is strictly positive in
    every model of `TE` (`expE_pos_of_model`), and strict positivity is preserved *and reflected*
    by `f` because it is the `LRc`-definable order `leE x y := ∃z, z*z = y - x` (`RingOps` /
    `Order` below);
  * on strictly positive elements the logarithm is a left inverse of the exponential
    (`expE_logFun_of_pos_of_model`), so `logFun (f (expE x)) = logFun (expE (f x))` gives
    `f (expE x) = expE (f x)`.

  Nothing here is specific to `ℝ`: the only inputs about `TE` are the transfer facts already
  available in the workspace.
-/
import Mathlib
import Submission.Work.WilC5.ExpLog
import Submission.Work.WilC5.Bridge
import Submission.Work.Wilkies.CG.Spec
import Submission.Work.WilC5.LogDefSetModel
import Submission.Work.WilC5.LogFunMap
import Submission.Work.WilC5.logFun_expE
import Submission.Work.WilC5.expE_lt_iff_logFun_lt
import Submission.Work.WilC5.ReductEmb
import Submission.Work.WilC5.LRcOps
import Submission.Work.WilC5.embedding_map_leEL

set_option autoImplicit false
set_option maxHeartbeats 1000000
noncomputable section
open Classical

namespace Work.WilC5

open WilkiesDesign WilkiesDesign.CG WilkiesConjecture FirstOrder Language
open scoped FirstOrder

/-! ## 1. An `LRc`-embedding of the `rexp`-reducts commutes with the ring operations

`reductStruct M` interprets the ring symbols of `LRc` by the ring symbols of `LEc`, so the
`LRc`-operations `addEL`, `mulEL`, … of `LRcOps.lean` are *definitionally* the `LEc`-operations
`addE`, `mulE`, … of `Bridge.lean`.  Hence the commutation lemmas of `embedding_map_leEL.lean`
transfer verbatim. -/

section RingOps

variable {K L : Type} [LEc.Structure K] [LEc.Structure L]

theorem map_mulE_reduct
    (f : @Embedding LRc K L (reductStruct K) (reductStruct L)) (x y : K) :
    f (mulE x y) = mulE (f x) (f y) := by
  letI : LRc.Structure K := reductStruct K
  letI : LRc.Structure L := reductStruct L
  exact map_mulEL f x y

theorem map_addE_reduct
    (f : @Embedding LRc K L (reductStruct K) (reductStruct L)) (x y : K) :
    f (addE x y) = addE (f x) (f y) := by
  letI : LRc.Structure K := reductStruct K
  letI : LRc.Structure L := reductStruct L
  exact map_addEL f x y

theorem map_negE_reduct
    (f : @Embedding LRc K L (reductStruct K) (reductStruct L)) (x : K) :
    f (negE x) = negE (f x) := by
  letI : LRc.Structure K := reductStruct K
  letI : LRc.Structure L := reductStruct L
  exact map_negEL f x

theorem map_subE_reduct
    (f : @Embedding LRc K L (reductStruct K) (reductStruct L)) (x y : K) :
    f (subE x y) = subE (f x) (f y) := by
  letI : LRc.Structure K := reductStruct K
  letI : LRc.Structure L := reductStruct L
  exact map_subEL f x y

/-- `f` maps the zero of `K` to the zero of `L`. -/
theorem map_zeroE_reduct
    (f : @Embedding LRc K L (reductStruct K) (reductStruct L)) :
    f (zeroE : K) = (zeroE : L) := by
  letI : LRc.Structure K := reductStruct K
  letI : LRc.Structure L := reductStruct L
  have h : f (zeroEL : K) = (zeroEL : L) := by
    rw [zeroEL, zeroEL, f.map_fun]
    congr 1
    ext i; exact Fin.elim0 i
  exact h

end RingOps

/-! ## 2. The definable order is preserved and reflected

The definable order `leE x y := isSquare (subE y x) = ∃ z, mulE z z = subE y x` is
quantifier-free definable, so it is preserved by *every* `LRc`-embedding of the reducts
(`leE_map_reduct`).  For the converse we use the two order facts available in models of `TE`:
totality at the source (`le_total_of_model`, `ReductEmb.lean`) and antisymmetry at the target
(`le_antisymm_of_model`). -/

section Order

variable {K L : Type} [LEc.Structure K] [LEc.Structure L]

/-- The definable order is preserved by an `LRc`-embedding of the `rexp`-reducts. -/
theorem leE_map_reduct
    (f : @Embedding LRc K L (reductStruct K) (reductStruct L)) {x y : K}
    (h : leE x y) : leE (f x) (f y) := by
  obtain ⟨z, hz⟩ := h
  exact ⟨f z, by rw [← map_mulE_reduct f z z, ← map_subE_reduct f y x, hz]⟩

/-- The definable order is reflected by an `LRc`-embedding of the `rexp`-reducts of models of
`TE`. -/
theorem leE_reflect_reduct
    (hK : K ⊨ TE) (hL : L ⊨ TE)
    (f : @Embedding LRc K L (reductStruct K) (reductStruct L)) {x y : K}
    (h : leE (f x) (f y)) : leE x y := by
  letI : LRc.Structure K := reductStruct K
  letI : LRc.Structure L := reductStruct L
  rcases le_total_of_model hK x y with hxy | hyx
  · exact hxy
  · have h1 : leE (f y) (f x) := leE_map_reduct f hyx
    have h2 : f x = f y := le_antisymm_of_model hL (f x) (f y) h h1
    have h3 : x = y := f.toEmbedding.injective h2
    subst h3
    exact hyx

/-- Strict positivity `0 < x` (`leE zeroE x ∧ ¬ leE x zeroE`) is preserved *and reflected* by an
`LRc`-embedding of the `rexp`-reducts of models of `TE`. -/
theorem pos_map_iff_reduct
    (hK : K ⊨ TE) (hL : L ⊨ TE)
    (f : @Embedding LRc K L (reductStruct K) (reductStruct L)) (x : K) :
    (leE (zeroE : K) x ∧ ¬ leE x (zeroE : K)) ↔
      (leE (zeroE : L) (f x) ∧ ¬ leE (f x) (zeroE : L)) := by
  have h0 : f (zeroE : K) = (zeroE : L) := map_zeroE_reduct f
  constructor
  · intro h
    refine ⟨?_, ?_⟩
    · have h1 := leE_map_reduct f h.1
      rwa [h0] at h1
    · intro hc
      refine h.2 ?_
      have hc' := hc
      rw [← h0] at hc'
      exact leE_reflect_reduct hK hL f hc'
  · intro h
    refine ⟨?_, ?_⟩
    · have h1 := h.1
      rw [← h0] at h1
      exact leE_reflect_reduct hK hL f h1
    · intro hc
      refine h.2 ?_
      have hc' := leE_map_reduct f hc
      rwa [h0] at hc'

end Order

/-! ## 3. The target -/

theorem expE_of_logFun_preserving {K L : Type}
    [WilkiesDesign.CG.LEc.Structure K] [WilkiesDesign.CG.LEc.Structure L]
    (hK : FirstOrder.Language.Theory.Model K WilkiesDesign.CG.TE)
    (hL : FirstOrder.Language.Theory.Model L WilkiesDesign.CG.TE)
    (f : @FirstOrder.Language.Embedding WilkiesDesign.CG.LRc K L
      (Work.WilC5.reductStruct K) (Work.WilC5.reductStruct L))
    (hf : ∀ x : K, f (Work.WilC5.logFun x) = Work.WilC5.logFun (f x)) :
    ∀ x : K, f (Work.WilC5.expE x) = Work.WilC5.expE (f x) := by
  intro x
  -- `exp x` (in `K`) and `exp (f x)` (in `L`) are strictly positive, and so is `f (exp x)`.
  have hxpos : leE (zeroE : K) (expE x) ∧ ¬ leE (expE x) (zeroE : K) := expE_pos_of_model hK x
  have hfxpos : leE (zeroE : L) (f (expE x)) ∧ ¬ leE (f (expE x)) (zeroE : L) :=
    (pos_map_iff_reduct hK hL f (expE x)).mp hxpos
  have hgxpos : leE (zeroE : L) (expE (f x)) ∧ ¬ leE (expE (f x)) (zeroE : L) :=
    expE_pos_of_model hL (f x)
  -- The logarithms of `f (exp x)` and of `exp (f x)` both equal `f x`.
  have h1 : logFun (f (expE x)) = f x := by
    rw [← hf (expE x), logFun_expE hK x]
  have h2 : logFun (expE (f x)) = f x := logFun_expE hL (f x)
  -- On strictly positive elements `exp ∘ logFun` is the identity.
  calc f (expE x) = expE (logFun (f (expE x))) :=
        (expE_logFun_of_pos_of_model hL hfxpos).symm
    _ = expE (logFun (expE (f x))) := by rw [h1, h2]
    _ = expE (f x) := expE_logFun_of_pos_of_model hL hgxpos

end Work.WilC5
