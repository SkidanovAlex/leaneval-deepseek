-- NOTE (WilC5 / S4OnePoint_general): a clash-free *copy* of `Submission/Work/WilC5/StepSeqLogPresAux.lean`
-- (proved by colleagues): every import in the `StepSeqLogClosure`/`StepSeqLogPres` chain is
-- redirected to the corresponding `…Cut` copy (in which the auxiliary definition `canonSyn` is
-- renamed), because the original `Work.WilC5.canonSyn` clashes with the identically named
-- definition of `Submission/Work/WilC5/StepKeyOfValProp.lean`, which is imported transitively by
-- `Submission/Work/WilC5/ExistsStepSeq.lean`; both are needed by the final assembly of vdDMM
-- Lemma 4.4 (`StepSeqTower.lean`).

/-
  WilC5 — `StepSeqLogPresAux`: compatibility of an `LRc`-embedding of a `rexp`-reduct with the
  field operations.

  `T ≤ K` is an `LRc`-substructure of the `rexp`-reduct `Work.WilC5.reductStruct K` and
  `σ : ↥T ↪[LRc] L` is an `LRc`-embedding into the `rexp`-reduct of `L`.  The `LRc`-symbols of
  these two structures are the ring symbols together with `rexp` (there are no relation symbols),
  and `Work.WilC5.reductStruct_funMap_ring` identifies them with the `LEc`-symbols
  `addE`/`mulE`/`negE`/`zeroE`/`oneE`.  Hence, with the coherence hypotheses `addE x y = x + y`, …,
  the embedding `σ` commutes with the field operations, with `ℤ`-casts, with integer powers and
  with finite sums and products.

  These are the `rexp`-reduct analogues of `Work.WilC5.S4ExpG.lpEmbed_*`, which are stated at the
  *syntactic* structure `LR.withConstantsStructure ℝ` and are not applicable to substructures of
  the reduct.  The membership hypotheses are families of membership proofs of the intermediate
  values; in the application they come from the `Work.WilC2.Dcl`-closure of `T`.
-/
import Mathlib
import Submission.Work.WilC5.S4StepNewSetup
import Submission.Work.WilC5.StepNoNewAux.logFun_one_add_map_of_modelComplete
import Submission.Work.WilC5.LRcOps

set_option maxHeartbeats 4000000
set_option linter.unusedVariables false

noncomputable section
open Classical

namespace Work.WilC5.SSLPAux

open WilkiesDesign WilkiesDesign.CG WilkiesConjecture FirstOrder Language
open scoped FirstOrder

variable {K L : Type} [WilkiesDesign.CG.LEc.Structure K] [WilkiesDesign.CG.LEc.Structure L]
  [Field K] [Field L]

/-- The value of `add` at the level of `K`. -/
theorem valAddK (haddK : ∀ x y : K, Work.WilC5.addE x y = x + y) (x y : K) :
    @Structure.funMap WilkiesDesign.CG.LRc K _ 2
      (Work.WilC5.ringSymL FirstOrder.Ring.addFunc) ![x, y] = x + y := by
  change (Work.WilC5.addE x y) = x + y
  exact haddK x y

/-- The value of `mul` at the level of `K`. -/
theorem valMulK (hmulK : ∀ x y : K, Work.WilC5.mulE x y = x * y) (x y : K) :
    @Structure.funMap WilkiesDesign.CG.LRc K _ 2
      (Work.WilC5.ringSymL FirstOrder.Ring.mulFunc) ![x, y] = x * y := by
  change (Work.WilC5.mulE x y) = x * y
  exact hmulK x y

/-- The value of `neg` at the level of `K`. -/
theorem valNegK (hnegK : ∀ x : K, Work.WilC5.negE x = -x) (x : K) :
    @Structure.funMap WilkiesDesign.CG.LRc K _ 1
      (Work.WilC5.ringSymL FirstOrder.Ring.negFunc) ![x] = -x := by
  change (Work.WilC5.negE x) = -x
  exact hnegK x

/-- The value of `1` at the level of `K`. -/
theorem valOneK (honeK : (Work.WilC5.oneE : K) = 1) :
    @Structure.funMap WilkiesDesign.CG.LRc K _ 0
      (Work.WilC5.ringSymL FirstOrder.Ring.oneFunc) (default : Fin 0 → K) = (1 : K) := by
  change (Work.WilC5.oneE : K) = 1
  exact honeK

/-- The value of `0` at the level of `K`. -/
theorem valZeroK (hzeroK : (Work.WilC5.zeroE : K) = 0) :
    @Structure.funMap WilkiesDesign.CG.LRc K _ 0
      (Work.WilC5.ringSymL FirstOrder.Ring.zeroFunc) (default : Fin 0 → K) = (0 : K) := by
  change (Work.WilC5.zeroE : K) = 0
  exact hzeroK

/-- The value of `rexp` at the level of `K`. -/
theorem valRexpK (u : K) :
    @Structure.funMap WilkiesDesign.CG.LRc K _ 1
      (Sum.inl (Sum.inr WilkiesDesign.CG.rexpFunc.rexp)) ![u] = Work.WilC5.rexpFromExp u := by
  change Work.WilC5.rexpFromExp u = Work.WilC5.rexpFromExp u
  rfl

/-- The value of `add` at the level of `L`. -/
theorem valAddL (haddL : ∀ x y : L, Work.WilC5.addE x y = x + y) (x y : L) :
    @Structure.funMap WilkiesDesign.CG.LRc L _ 2
      (Work.WilC5.ringSymL FirstOrder.Ring.addFunc) ![x, y] = x + y := by
  change (Work.WilC5.addE x y) = x + y
  exact haddL x y

/-- The value of `mul` at the level of `L`. -/
theorem valMulL (hmulL : ∀ x y : L, Work.WilC5.mulE x y = x * y) (x y : L) :
    @Structure.funMap WilkiesDesign.CG.LRc L _ 2
      (Work.WilC5.ringSymL FirstOrder.Ring.mulFunc) ![x, y] = x * y := by
  change (Work.WilC5.mulE x y) = x * y
  exact hmulL x y

/-- The value of `neg` at the level of `L`. -/
theorem valNegL (hnegL : ∀ x : L, Work.WilC5.negE x = -x) (x : L) :
    @Structure.funMap WilkiesDesign.CG.LRc L _ 1
      (Work.WilC5.ringSymL FirstOrder.Ring.negFunc) ![x] = -x := by
  change (Work.WilC5.negE x) = -x
  exact hnegL x

/-- The value of `1` at the level of `L`. -/
theorem valOneL (honeL : (Work.WilC5.oneE : L) = 1) :
    @Structure.funMap WilkiesDesign.CG.LRc L _ 0
      (Work.WilC5.ringSymL FirstOrder.Ring.oneFunc) (default : Fin 0 → L) = (1 : L) := by
  change (Work.WilC5.oneE : L) = 1
  exact honeL

/-- The value of `0` at the level of `L`. -/
theorem valZeroL (hzeroL : (Work.WilC5.zeroE : L) = 0) :
    @Structure.funMap WilkiesDesign.CG.LRc L _ 0
      (Work.WilC5.ringSymL FirstOrder.Ring.zeroFunc) (default : Fin 0 → L) = (0 : L) := by
  change (Work.WilC5.zeroE : L) = 0
  exact hzeroL

/-- The value of `rexp` at the level of `L`. -/
theorem valRexpL (u : L) :
    @Structure.funMap WilkiesDesign.CG.LRc L _ 1
      (Sum.inl (Sum.inr WilkiesDesign.CG.rexpFunc.rexp)) ![u] = Work.WilC5.rexpFromExp u := by
  change Work.WilC5.rexpFromExp u = Work.WilC5.rexpFromExp u
  rfl

variable {T : @WilkiesDesign.CG.LRc.Substructure K (Work.WilC5.reductStruct K)}

/-- Membership of the `add`-value of two elements of `T`, in field notation (on `K`). -/
theorem memAdd (haddK : ∀ x y : K, Work.WilC5.addE x y = x + y) {x y : K}
    (hx : x ∈ (T : Set K)) (hy : y ∈ (T : Set K)) : x + y ∈ (T : Set K) := by
  have h := T.fun_mem (Work.WilC5.ringSymL FirstOrder.Ring.addFunc :
    WilkiesDesign.CG.LRc.Functions 2) ![x, y] (by intro i; fin_cases i <;> assumption)
  rwa [valAddK haddK x y] at h

/-- Membership of the `mul`-value of two elements of `T`. -/
theorem memMul (hmulK : ∀ x y : K, Work.WilC5.mulE x y = x * y) {x y : K}
    (hx : x ∈ (T : Set K)) (hy : y ∈ (T : Set K)) : x * y ∈ (T : Set K) := by
  have h := T.fun_mem (Work.WilC5.ringSymL FirstOrder.Ring.mulFunc :
    WilkiesDesign.CG.LRc.Functions 2) ![x, y] (by intro i; fin_cases i <;> assumption)
  rwa [valMulK hmulK x y] at h

/-- Membership of the `neg`-value of an element of `T`. -/
theorem memNeg (hnegK : ∀ x : K, Work.WilC5.negE x = -x) {x : K}
    (hx : x ∈ (T : Set K)) : -x ∈ (T : Set K) := by
  have h := T.fun_mem (Work.WilC5.ringSymL FirstOrder.Ring.negFunc :
    WilkiesDesign.CG.LRc.Functions 1) ![x] (by intro i; fin_cases i; exact hx)
  rwa [valNegK hnegK x] at h

/-- `1 ∈ T`. -/
theorem memOne (honeK : (Work.WilC5.oneE : K) = 1) : (1 : K) ∈ (T : Set K) := by
  have h := T.fun_mem (Work.WilC5.ringSymL FirstOrder.Ring.oneFunc :
    WilkiesDesign.CG.LRc.Functions 0) (default : Fin 0 → K) (fun i => Fin.elim0 i)
  rwa [valOneK honeK] at h

/-- `0 ∈ T`. -/
theorem memZero (hzeroK : (Work.WilC5.zeroE : K) = 0) : (0 : K) ∈ (T : Set K) := by
  have h := T.fun_mem (Work.WilC5.ringSymL FirstOrder.Ring.zeroFunc :
    WilkiesDesign.CG.LRc.Functions 0) (default : Fin 0 → K) (fun i => Fin.elim0 i)
  rwa [valZeroK hzeroK] at h

/-- `T` is closed under subtraction. -/
theorem memSub (haddK : ∀ x y : K, Work.WilC5.addE x y = x + y)
    (hnegK : ∀ x : K, Work.WilC5.negE x = -x) {x y : K}
    (hx : x ∈ (T : Set K)) (hy : y ∈ (T : Set K)) : x - y ∈ (T : Set K) := by
  rw [sub_eq_add_neg]
  exact memAdd haddK hx (memNeg hnegK hy)

section Emb

variable (σ : @Embedding WilkiesDesign.CG.LRc ↥T L _ (Work.WilC5.reductStruct L))

/-- `σ` commutes with addition. -/
theorem embAdd (haddK : ∀ x y : K, Work.WilC5.addE x y = x + y)
    (haddL : ∀ x y : L, Work.WilC5.addE x y = x + y) (x y : ↥T) :
    ∀ (h : (x : K) + (y : K) ∈ (T : Set K)), σ ⟨(x : K) + (y : K), h⟩ = σ x + σ y := by
  intro h
  have h0 : (x : K) + (y : K) ∈ (T : Set K) := memAdd (T := T) haddK x.2 y.2
  have hsub : (⟨(x : K) + (y : K), h⟩ : ↥T) = ⟨(x : K) + (y : K), h0⟩ := Subtype.ext rfl
  have key : (⟨(x : K) + (y : K), h0⟩ : ↥T) =
      @Structure.funMap WilkiesDesign.CG.LRc ↥T _ 2
        (Work.WilC5.ringSymL FirstOrder.Ring.addFunc) ![x, y] := by
    apply Subtype.ext
    rw [Work.WilC5.StepNoNewAux.coe_funMap_substructure]
    have ht : (fun i => (((![x, y] : Fin 2 → ↥T) i : ↥T) : K)) = ![(x : K), (y : K)] := by
      funext i; fin_cases i <;> rfl
    rw [ht]
    exact (valAddK haddK (x : K) (y : K)).symm
  have hmap := @Embedding.map_fun' WilkiesDesign.CG.LRc ↥T L _
    (Work.WilC5.reductStruct L) σ 2 (Work.WilC5.ringSymL FirstOrder.Ring.addFunc) ![x, y]
  have hc : (σ ∘ ![x, y] : Fin 2 → L) = ![σ x, σ y] := by funext i; fin_cases i <;> rfl
  calc σ ⟨(x : K) + (y : K), h⟩ = σ ⟨(x : K) + (y : K), h0⟩ := by rw [hsub]
    _ = σ (@Structure.funMap WilkiesDesign.CG.LRc ↥T _ 2
          (Work.WilC5.ringSymL FirstOrder.Ring.addFunc) ![x, y]) := by rw [key]
    _ = @Structure.funMap WilkiesDesign.CG.LRc L _ 2
          (Work.WilC5.ringSymL FirstOrder.Ring.addFunc) (σ ∘ ![x, y]) := hmap
    _ = @Structure.funMap WilkiesDesign.CG.LRc L _ 2
          (Work.WilC5.ringSymL FirstOrder.Ring.addFunc) ![σ x, σ y] := by rw [hc]
    _ = σ x + σ y := valAddL haddL (σ x) (σ y)

/-- `σ` commutes with multiplication. -/
theorem embMul (hmulK : ∀ x y : K, Work.WilC5.mulE x y = x * y)
    (hmulL : ∀ x y : L, Work.WilC5.mulE x y = x * y) (x y : ↥T) :
    ∀ (h : (x : K) * (y : K) ∈ (T : Set K)), σ ⟨(x : K) * (y : K), h⟩ = σ x * σ y := by
  intro h
  have h0 : (x : K) * (y : K) ∈ (T : Set K) := memMul (T := T) hmulK x.2 y.2
  have hsub : (⟨(x : K) * (y : K), h⟩ : ↥T) = ⟨(x : K) * (y : K), h0⟩ := Subtype.ext rfl
  have key : (⟨(x : K) * (y : K), h0⟩ : ↥T) =
      @Structure.funMap WilkiesDesign.CG.LRc ↥T _ 2
        (Work.WilC5.ringSymL FirstOrder.Ring.mulFunc) ![x, y] := by
    apply Subtype.ext
    rw [Work.WilC5.StepNoNewAux.coe_funMap_substructure]
    have ht : (fun i => (((![x, y] : Fin 2 → ↥T) i : ↥T) : K)) = ![(x : K), (y : K)] := by
      funext i; fin_cases i <;> rfl
    rw [ht]
    exact (valMulK hmulK (x : K) (y : K)).symm
  have hmap := @Embedding.map_fun' WilkiesDesign.CG.LRc ↥T L _
    (Work.WilC5.reductStruct L) σ 2 (Work.WilC5.ringSymL FirstOrder.Ring.mulFunc) ![x, y]
  have hc : (σ ∘ ![x, y] : Fin 2 → L) = ![σ x, σ y] := by funext i; fin_cases i <;> rfl
  calc σ ⟨(x : K) * (y : K), h⟩ = σ ⟨(x : K) * (y : K), h0⟩ := by rw [hsub]
    _ = σ (@Structure.funMap WilkiesDesign.CG.LRc ↥T _ 2
          (Work.WilC5.ringSymL FirstOrder.Ring.mulFunc) ![x, y]) := by rw [key]
    _ = @Structure.funMap WilkiesDesign.CG.LRc L _ 2
          (Work.WilC5.ringSymL FirstOrder.Ring.mulFunc) (σ ∘ ![x, y]) := hmap
    _ = @Structure.funMap WilkiesDesign.CG.LRc L _ 2
          (Work.WilC5.ringSymL FirstOrder.Ring.mulFunc) ![σ x, σ y] := by rw [hc]
    _ = σ x * σ y := valMulL hmulL (σ x) (σ y)

/-- `σ` commutes with negation. -/
theorem embNeg (hnegK : ∀ x : K, Work.WilC5.negE x = -x)
    (hnegL : ∀ x : L, Work.WilC5.negE x = -x) (x : ↥T) :
    ∀ (h : -(x : K) ∈ (T : Set K)), σ ⟨-(x : K), h⟩ = -σ x := by
  intro h
  have h0 : -(x : K) ∈ (T : Set K) := memNeg (T := T) hnegK x.2
  have hsub : (⟨-(x : K), h⟩ : ↥T) = ⟨-(x : K), h0⟩ := Subtype.ext rfl
  have key : (⟨-(x : K), h0⟩ : ↥T) =
      @Structure.funMap WilkiesDesign.CG.LRc ↥T _ 1
        (Work.WilC5.ringSymL FirstOrder.Ring.negFunc) ![x] := by
    apply Subtype.ext
    rw [Work.WilC5.StepNoNewAux.coe_funMap_substructure]
    have ht : (fun i => (((![x] : Fin 1 → ↥T) i : ↥T) : K)) = ![(x : K)] := by
      funext i; fin_cases i <;> rfl
    rw [ht]
    exact (valNegK hnegK (x : K)).symm
  have hmap := @Embedding.map_fun' WilkiesDesign.CG.LRc ↥T L _
    (Work.WilC5.reductStruct L) σ 1 (Work.WilC5.ringSymL FirstOrder.Ring.negFunc) ![x]
  have hc : (σ ∘ ![x] : Fin 1 → L) = ![σ x] := by funext i; fin_cases i <;> rfl
  calc σ ⟨-(x : K), h⟩ = σ ⟨-(x : K), h0⟩ := by rw [hsub]
    _ = σ (@Structure.funMap WilkiesDesign.CG.LRc ↥T _ 1
          (Work.WilC5.ringSymL FirstOrder.Ring.negFunc) ![x]) := by rw [key]
    _ = @Structure.funMap WilkiesDesign.CG.LRc L _ 1
          (Work.WilC5.ringSymL FirstOrder.Ring.negFunc) (σ ∘ ![x]) := hmap
    _ = @Structure.funMap WilkiesDesign.CG.LRc L _ 1
          (Work.WilC5.ringSymL FirstOrder.Ring.negFunc) ![σ x] := by rw [hc]
    _ = -σ x := valNegL hnegL (σ x)

/-- `σ` commutes with the constant `1`. -/
theorem embOne (honeK : (Work.WilC5.oneE : K) = 1) (honeL : (Work.WilC5.oneE : L) = 1) :
    ∀ (h : (1 : K) ∈ (T : Set K)), σ ⟨(1 : K), h⟩ = (1 : L) := by
  intro h
  have h0 : (1 : K) ∈ (T : Set K) := memOne (T := T) honeK
  have hsub : (⟨(1 : K), h⟩ : ↥T) = ⟨(1 : K), h0⟩ := Subtype.ext rfl
  have key : (⟨(1 : K), h0⟩ : ↥T) =
      @Structure.funMap WilkiesDesign.CG.LRc ↥T _ 0
        (Work.WilC5.ringSymL FirstOrder.Ring.oneFunc) (default : Fin 0 → ↥T) := by
    apply Subtype.ext
    rw [Work.WilC5.StepNoNewAux.coe_funMap_substructure]
    have ht : (fun i => (((default : Fin 0 → ↥T) i : ↥T) : K)) = (default : Fin 0 → K) :=
      Subsingleton.elim _ _
    rw [ht]
    exact (valOneK honeK).symm
  have hmap := @Embedding.map_fun' WilkiesDesign.CG.LRc ↥T L _
    (Work.WilC5.reductStruct L) σ 0 (Work.WilC5.ringSymL FirstOrder.Ring.oneFunc)
    (default : Fin 0 → ↥T)
  have hc : (σ ∘ (default : Fin 0 → ↥T)) = (default : Fin 0 → L) := Subsingleton.elim _ _
  calc σ ⟨(1 : K), h⟩ = σ ⟨(1 : K), h0⟩ := by rw [hsub]
    _ = σ (@Structure.funMap WilkiesDesign.CG.LRc ↥T _ 0
          (Work.WilC5.ringSymL FirstOrder.Ring.oneFunc) (default : Fin 0 → ↥T)) := by rw [key]
    _ = @Structure.funMap WilkiesDesign.CG.LRc L _ 0
          (Work.WilC5.ringSymL FirstOrder.Ring.oneFunc) (σ ∘ (default : Fin 0 → ↥T)) := hmap
    _ = @Structure.funMap WilkiesDesign.CG.LRc L _ 0
          (Work.WilC5.ringSymL FirstOrder.Ring.oneFunc) (default : Fin 0 → L) := by rw [hc]
    _ = (1 : L) := valOneL honeL

/-- `σ` commutes with the constant `0`. -/
theorem embZero (hzeroK : (Work.WilC5.zeroE : K) = 0) (hzeroL : (Work.WilC5.zeroE : L) = 0) :
    ∀ (h : (0 : K) ∈ (T : Set K)), σ ⟨(0 : K), h⟩ = (0 : L) := by
  intro h
  have h0 : (0 : K) ∈ (T : Set K) := memZero (T := T) hzeroK
  have hsub : (⟨(0 : K), h⟩ : ↥T) = ⟨(0 : K), h0⟩ := Subtype.ext rfl
  have key : (⟨(0 : K), h0⟩ : ↥T) =
      @Structure.funMap WilkiesDesign.CG.LRc ↥T _ 0
        (Work.WilC5.ringSymL FirstOrder.Ring.zeroFunc) (default : Fin 0 → ↥T) := by
    apply Subtype.ext
    rw [Work.WilC5.StepNoNewAux.coe_funMap_substructure]
    have ht : (fun i => (((default : Fin 0 → ↥T) i : ↥T) : K)) = (default : Fin 0 → K) :=
      Subsingleton.elim _ _
    rw [ht]
    exact (valZeroK hzeroK).symm
  have hmap := @Embedding.map_fun' WilkiesDesign.CG.LRc ↥T L _
    (Work.WilC5.reductStruct L) σ 0 (Work.WilC5.ringSymL FirstOrder.Ring.zeroFunc)
    (default : Fin 0 → ↥T)
  have hc : (σ ∘ (default : Fin 0 → ↥T)) = (default : Fin 0 → L) := Subsingleton.elim _ _
  calc σ ⟨(0 : K), h⟩ = σ ⟨(0 : K), h0⟩ := by rw [hsub]
    _ = σ (@Structure.funMap WilkiesDesign.CG.LRc ↥T _ 0
          (Work.WilC5.ringSymL FirstOrder.Ring.zeroFunc) (default : Fin 0 → ↥T)) := by rw [key]
    _ = @Structure.funMap WilkiesDesign.CG.LRc L _ 0
          (Work.WilC5.ringSymL FirstOrder.Ring.zeroFunc) (σ ∘ (default : Fin 0 → ↥T)) := hmap
    _ = @Structure.funMap WilkiesDesign.CG.LRc L _ 0
          (Work.WilC5.ringSymL FirstOrder.Ring.zeroFunc) (default : Fin 0 → L) := by rw [hc]
    _ = (0 : L) := valZeroL hzeroL

/-- `σ` commutes with subtraction. -/
theorem embSub (haddK : ∀ x y : K, Work.WilC5.addE x y = x + y)
    (haddL : ∀ x y : L, Work.WilC5.addE x y = x + y)
    (hnegK : ∀ x : K, Work.WilC5.negE x = -x)
    (hnegL : ∀ x : L, Work.WilC5.negE x = -x) (x y : ↥T) :
    ∀ (h : (x : K) - (y : K) ∈ (T : Set K)), σ ⟨(x : K) - (y : K), h⟩ = σ x - σ y := by
  intro h
  have hmem : -(y : K) ∈ (T : Set K) := memNeg (T := T) hnegK y.2
  have h' : (x : K) + (-(y : K)) ∈ (T : Set K) := memAdd (T := T) haddK x.2 hmem
  have h1 : (⟨(x : K) - (y : K), h⟩ : ↥T) = ⟨(x : K) + (-(y : K)), h'⟩ := by
    apply Subtype.ext
    show (x : K) - (y : K) = (x : K) + -(y : K)
    rw [sub_eq_add_neg]
  rw [h1, embAdd σ haddK haddL x ⟨-(y : K), hmem⟩ h', embNeg σ hnegK hnegL y hmem]
  show σ x + -σ y = σ x - σ y
  rw [sub_eq_add_neg]

/-- `σ` commutes with inversion. -/
theorem embInv (hmulK : ∀ x y : K, Work.WilC5.mulE x y = x * y)
    (hmulL : ∀ x y : L, Work.WilC5.mulE x y = x * y)
    (honeK : (Work.WilC5.oneE : K) = 1) (honeL : (Work.WilC5.oneE : L) = 1)
    (x : ↥T) (hx : (x : K) ≠ 0) :
    ∀ (h : ((x : K))⁻¹ ∈ (T : Set K)), σ ⟨(x : K)⁻¹, h⟩ = (σ x)⁻¹ := by
  intro h
  have hmul0 : (x : K) * (x : K)⁻¹ ∈ (T : Set K) := by
    rw [mul_inv_cancel₀ hx]; exact memOne (T := T) honeK
  have h1 := embMul σ hmulK hmulL x ⟨(x : K)⁻¹, h⟩ hmul0
  have hval : (x : K) * (x : K)⁻¹ = (1 : K) := mul_inv_cancel₀ hx
  rw [show (⟨(x : K) * (x : K)⁻¹, hmul0⟩ : ↥T) = ⟨(1 : K), memOne (T := T) honeK⟩ from
    Subtype.ext hval, embOne σ honeK honeL (memOne (T := T) honeK)] at h1
  exact (inv_eq_of_mul_eq_one_right h1.symm).symm

/-- `σ` commutes with `ℤ`-casts. -/
theorem embInt (haddK : ∀ x y : K, Work.WilC5.addE x y = x + y)
    (haddL : ∀ x y : L, Work.WilC5.addE x y = x + y)
    (honeK : (Work.WilC5.oneE : K) = 1) (honeL : (Work.WilC5.oneE : L) = 1)
    (hnegK : ∀ x : K, Work.WilC5.negE x = -x)
    (hnegL : ∀ x : L, Work.WilC5.negE x = -x)
    (hzeroK : (Work.WilC5.zeroE : K) = 0) (hzeroL : (Work.WilC5.zeroE : L) = 0)
    (hmem : ∀ m : ℤ, ((m : ℤ) : K) ∈ (T : Set K)) :
    ∀ z : ℤ, σ ⟨((z : ℤ) : K), hmem z⟩ = ((z : ℤ) : L) := by
  have h1 : (1 : K) ∈ (T : Set K) := memOne (T := T) honeK
  intro z
  induction z using Int.induction_on with
  | zero =>
    rw [show (⟨((0 : ℤ) : K), hmem 0⟩ : ↥T) = ⟨(0 : K), memZero (T := T) hzeroK⟩ from
      Subtype.ext (by norm_num)]
    rw [embZero σ hzeroK hzeroL (memZero (T := T) hzeroK)]
    norm_num
  | succ k ih =>
    have hcast : (((k : ℤ) + 1 : ℤ) : K) = ((k : ℤ) : K) + 1 := by push_cast; ring
    have hmem' : ((k : ℤ) : K) + 1 ∈ (T : Set K) := memAdd (T := T) haddK (hmem k) h1
    have heq : (⟨(((k : ℤ) + 1 : ℤ) : K), hmem _⟩ : ↥T)
        = ⟨((k : ℤ) : K) + (1 : K), hmem'⟩ := by
      apply Subtype.ext
      show (((k : ℤ) + 1 : ℤ) : K) = ((k : ℤ) : K) + 1
      exact hcast
    rw [heq, embAdd σ haddK haddL ⟨_, hmem k⟩ ⟨(1 : K), h1⟩ hmem', ih,
      embOne σ honeK honeL h1]
    push_cast; ring
  | pred k ih =>
    have hcast : (((-k : ℤ) - 1 : ℤ) : K) = ((-k : ℤ) : K) - 1 := by push_cast; ring
    have hmem' : ((-k : ℤ) : K) - (1 : K) ∈ (T : Set K) :=
      memSub (T := T) haddK hnegK (hmem (-k)) h1
    have heq : (⟨(((-k : ℤ) - 1 : ℤ) : K), hmem _⟩ : ↥T)
        = ⟨((-k : ℤ) : K) - (1 : K), hmem'⟩ := by
      apply Subtype.ext
      show (((-k : ℤ) - 1 : ℤ) : K) = ((-k : ℤ) : K) - 1
      exact hcast
    rw [heq, embSub σ haddK haddL hnegK hnegL ⟨_, hmem (-k)⟩ ⟨(1 : K), h1⟩ hmem', ih,
      embOne σ honeK honeL h1]
    push_cast; ring

/-- `σ` commutes with integer powers. -/
theorem embZPow (haddK : ∀ x y : K, Work.WilC5.addE x y = x + y)
    (haddL : ∀ x y : L, Work.WilC5.addE x y = x + y)
    (hmulK : ∀ x y : K, Work.WilC5.mulE x y = x * y)
    (hmulL : ∀ x y : L, Work.WilC5.mulE x y = x * y)
    (honeK : (Work.WilC5.oneE : K) = 1) (honeL : (Work.WilC5.oneE : L) = 1)
    (hzeroK : (Work.WilC5.zeroE : K) = 0) (hzeroL : (Work.WilC5.zeroE : L) = 0)
    (x : ↥T) (hx : (x : K) ≠ 0) (hmem : ∀ z : ℤ, (x : K) ^ z ∈ (T : Set K)) :
    ∀ z : ℤ, σ ⟨(x : K) ^ z, hmem z⟩ = (σ x) ^ z := by
  have hmemInv : ((x : K))⁻¹ ∈ (T : Set K) := by
    have h := hmem (-1)
    rwa [zpow_neg_one] at h
  have hσx : (σ x) ≠ 0 := by
    intro h
    have h0 : σ x = σ ⟨(0 : K), memZero (T := T) hzeroK⟩ := by
      rw [h, embZero σ hzeroK hzeroL (memZero (T := T) hzeroK)]
    exact hx (congrArg Subtype.val (σ.injective h0))
  intro z
  induction z using Int.induction_on with
  | zero =>
    have heq : (⟨(x : K) ^ (0 : ℤ), hmem 0⟩ : ↥T) = ⟨(1 : K), memOne (T := T) honeK⟩ := by
      apply Subtype.ext
      show (x : K) ^ (0 : ℤ) = (1 : K)
      rw [zpow_zero]
    rw [heq, embOne σ honeK honeL (memOne (T := T) honeK), zpow_zero]
  | succ k ih =>
    have hstep : (x : K) ^ (k : ℤ) * (x : K) ∈ (T : Set K) := by
      have h := hmem ((k : ℤ) + 1)
      rwa [zpow_add_one₀ hx] at h
    have heq : (⟨(x : K) ^ ((k : ℤ) + 1), hmem _⟩ : ↥T)
        = ⟨(x : K) ^ (k : ℤ) * (x : K), hstep⟩ := by
      apply Subtype.ext
      show (x : K) ^ ((k : ℤ) + 1) = (x : K) ^ (k : ℤ) * (x : K)
      rw [zpow_add_one₀ hx]
    rw [heq, embMul σ hmulK hmulL ⟨_, hmem k⟩ x hstep, ih, zpow_add_one₀ hσx]
  | pred k ih =>
    have hstep : (x : K) ^ (-(k : ℤ)) * (x : K)⁻¹ ∈ (T : Set K) := by
      have h := hmem (-(k : ℤ) - 1)
      rwa [zpow_sub_one₀ hx] at h
    have heq : (⟨(x : K) ^ (-(k : ℤ) - 1), hmem _⟩ : ↥T)
        = ⟨(x : K) ^ (-(k : ℤ)) * (x : K)⁻¹, hstep⟩ := by
      apply Subtype.ext
      show (x : K) ^ (-(k : ℤ) - 1) = (x : K) ^ (-(k : ℤ)) * (x : K)⁻¹
      rw [zpow_sub_one₀ hx]
    rw [heq, embMul σ hmulK hmulL ⟨_, hmem (-(k : ℤ))⟩ ⟨_, hmemInv⟩ hstep, ih,
      embInv σ hmulK hmulL honeK honeL x hx hmemInv, zpow_sub_one₀ hσx]

/-- `σ` commutes with finite sums. -/
theorem embSum (haddK : ∀ x y : K, Work.WilC5.addE x y = x + y)
    (haddL : ∀ x y : L, Work.WilC5.addE x y = x + y)
    (hzeroK : (Work.WilC5.zeroE : K) = 0) (hzeroL : (Work.WilC5.zeroE : L) = 0)
    {ι : Type*} (s : Finset ι) (f : ι → ↥T) :
    ∀ (hmem : ∀ t : Finset ι, (∑ i ∈ t, (f i : K)) ∈ (T : Set K)),
      σ ⟨∑ i ∈ s, (f i : K), hmem s⟩ = ∑ i ∈ s, σ (f i) := by
  classical
  induction s using Finset.induction with
  | empty =>
    intro hmem
    rw [show (⟨∑ i ∈ (∅ : Finset ι), (f i : K), hmem ∅⟩ : ↥T)
        = ⟨(0 : K), memZero (T := T) hzeroK⟩ from Subtype.ext (by simp)]
    rw [embZero σ hzeroK hzeroL (memZero (T := T) hzeroK)]
    simp
  | insert a s ha ih =>
    intro hmem
    have hmem' : (f a : K) + (∑ i ∈ s, (f i : K)) ∈ (T : Set K) :=
      memAdd (T := T) haddK (f a).2 (hmem s)
    rw [show (⟨∑ i ∈ insert a s, (f i : K), hmem (insert a s)⟩ : ↥T)
        = ⟨(f a : K) + (∑ i ∈ s, (f i : K)), hmem'⟩ from Subtype.ext (Finset.sum_insert ha)]
    rw [embAdd σ haddK haddL (f a) ⟨_, hmem s⟩ hmem', ih hmem, Finset.sum_insert ha]

/-- `σ` commutes with finite products of integer powers. -/
theorem embProd (haddK : ∀ x y : K, Work.WilC5.addE x y = x + y)
    (haddL : ∀ x y : L, Work.WilC5.addE x y = x + y)
    (hmulK : ∀ x y : K, Work.WilC5.mulE x y = x * y)
    (hmulL : ∀ x y : L, Work.WilC5.mulE x y = x * y)
    (honeK : (Work.WilC5.oneE : K) = 1) (honeL : (Work.WilC5.oneE : L) = 1)
    (hzeroK : (Work.WilC5.zeroE : K) = 0) (hzeroL : (Work.WilC5.zeroE : L) = 0)
    {ι : Type*} (s : Finset ι) (f : ι → ↥T) (z : ι → ℤ) :
    ∀ (hz : ∀ i ∈ s, (f i : K) ≠ 0)
      (hmem : ∀ (t : Finset ι) (z' : ι → ℤ), (∏ i ∈ t, (f i : K) ^ (z' i)) ∈ (T : Set K)),
      σ ⟨∏ i ∈ s, (f i : K) ^ (z i), hmem s z⟩ = ∏ i ∈ s, (σ (f i)) ^ (z i) := by
  classical
  induction s using Finset.induction with
  | empty =>
    intro hz hmem
    have heq : (⟨∏ i ∈ (∅ : Finset ι), (f i : K) ^ (z i), hmem ∅ z⟩ : ↥T)
        = ⟨(1 : K), memOne (T := T) honeK⟩ := by
      apply Subtype.ext
      show (∏ i ∈ (∅ : Finset ι), (f i : K) ^ (z i)) = (1 : K)
      simp
    rw [heq, embOne σ honeK honeL (memOne (T := T) honeK)]
    simp
  | insert a s ha ih =>
    intro hz hmem
    have hza : (f a : K) ^ (z a) ∈ (T : Set K) := by
      have h := hmem {a} z
      rwa [Finset.prod_singleton] at h
    have hmem' : (f a : K) ^ (z a) * (∏ i ∈ s, (f i : K) ^ (z i)) ∈ (T : Set K) :=
      memMul (T := T) hmulK hza (hmem s z)
    have heq : (⟨∏ i ∈ insert a s, (f i : K) ^ (z i), hmem (insert a s) z⟩ : ↥T)
        = ⟨(f a : K) ^ (z a) * (∏ i ∈ s, (f i : K) ^ (z i)), hmem'⟩ := by
      apply Subtype.ext
      show (∏ i ∈ insert a s, (f i : K) ^ (z i))
        = (f a : K) ^ (z a) * (∏ i ∈ s, (f i : K) ^ (z i))
      rw [Finset.prod_insert ha]
    rw [heq, embMul σ hmulK hmulL ⟨_, hza⟩ ⟨_, hmem s z⟩ hmem']
    rw [embZPow σ haddK haddL hmulK hmulL honeK honeL hzeroK hzeroL (f a)
        (hz a (Finset.mem_insert_self a s))
        (fun w => by
          have h := hmem {a} (fun _ => w)
          rwa [Finset.prod_singleton] at h) (z a)]
    rw [ih (fun i hi => hz i (Finset.mem_insert_of_mem hi)) hmem, Finset.prod_insert ha]

/-- `σ` commutes with the restricted exponential `rexpFromExp` (at the `funMap` level). -/
theorem embRexp (u : ↥T) :
    σ (@Structure.funMap WilkiesDesign.CG.LRc ↥T _ 1
        (Sum.inl (Sum.inr WilkiesDesign.CG.rexpFunc.rexp)) ![u])
      = Work.WilC5.rexpFromExp (σ u) := by
  have hmap := @Embedding.map_fun' WilkiesDesign.CG.LRc ↥T L _
    (Work.WilC5.reductStruct L) σ 1 (Sum.inl (Sum.inr WilkiesDesign.CG.rexpFunc.rexp)) ![u]
  have hc : (σ ∘ ![u] : Fin 1 → L) = ![σ u] := by funext i; fin_cases i <;> rfl
  calc σ (@Structure.funMap WilkiesDesign.CG.LRc ↥T _ 1
          (Sum.inl (Sum.inr WilkiesDesign.CG.rexpFunc.rexp)) ![u])
      = @Structure.funMap WilkiesDesign.CG.LRc L _ 1
          (Sum.inl (Sum.inr WilkiesDesign.CG.rexpFunc.rexp)) (σ ∘ ![u]) := hmap
    _ = @Structure.funMap WilkiesDesign.CG.LRc L _ 1
          (Sum.inl (Sum.inr WilkiesDesign.CG.rexpFunc.rexp)) ![σ u] := by rw [hc]
    _ = Work.WilC5.rexpFromExp (σ u) := valRexpL (σ u)

/-- `σ` commutes with the restricted exponential `rexpFromExp` (at the value level). -/
theorem embRexpVal (u : ↥T) (h : Work.WilC5.rexpFromExp (u : K) ∈ (T : Set K)) :
    σ ⟨Work.WilC5.rexpFromExp (u : K), h⟩ = Work.WilC5.rexpFromExp (σ u) := by
  have key : (⟨Work.WilC5.rexpFromExp (u : K), h⟩ : ↥T) =
      @Structure.funMap WilkiesDesign.CG.LRc ↥T _ 1
        (Sum.inl (Sum.inr WilkiesDesign.CG.rexpFunc.rexp)) ![u] := by
    apply Subtype.ext
    change Work.WilC5.rexpFromExp (u : K) = @Structure.funMap WilkiesDesign.CG.LRc K _ 1
      (Sum.inl (Sum.inr WilkiesDesign.CG.rexpFunc.rexp))
      (fun i => (((![u] : Fin 1 → ↥T) i : ↥T) : K))
    have ht : (fun i => (((![u] : Fin 1 → ↥T) i : ↥T) : K)) = ![(u : K)] := by
      funext i; fin_cases i <;> rfl
    rw [ht]
    exact (valRexpK (u : K)).symm
  rw [key]
  exact embRexp σ u

end Emb

end Work.WilC5.SSLPAux
