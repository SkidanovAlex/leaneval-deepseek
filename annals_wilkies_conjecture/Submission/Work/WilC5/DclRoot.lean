import Mathlib
import Submission.Work.WilC5.model_pow_root
import Submission.Work.WilC2.Square
import Submission.Work.WilC2.Dcl
import Submission.Work.WilC5.Values
import Submission.Work.WilC5.S4StepDefs
import Submission.Work.WilC5.LRcReduct
import Submission.Work.WilC5.S4ExpG.Glue
import Submission.Work.WilC5.S4Exp.hynew_exp
import Submission.Work.WilC5.Reduct

set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
set_option linter.style.haveILetI false
set_option linter.unusedVariables false
noncomputable section
open Classical
namespace Work.WilC5

open WilkiesDesign WilkiesDesign.CG WilkiesConjecture FirstOrder Language
open scoped FirstOrder

/-! ## 0. The `LRc`-formula `∃ u, (u * u = y ∧ y ^ (N+1) = z)`

The formula is written directly with the ring symbols of `LRc`, so that its realization at the
`rexp`-reduct `reductStruct K` is computed by `reductStruct_funMap_ring` and the hypothesis
`mulE = (· * ·)`.  (Going through the language inclusion `ring →ᴸ LR →ᴸ LRc` instead runs into the
fact that instance search resolves the ring symbols of `LRc` at `lrcRingReduct`, which is not the
`Ring.CompatibleRing` structure of the surrounding context.) -/

/-- The `LRc`-term `a * b`. -/
private def mulT {α : Type} (a b : LRc.Term α) : LRc.Term α :=
  Term.func (Sum.inl (Sum.inl Ring.mulFunc)) ![a, b]

/-- The `LRc`-term `t * t * ⋯ * t` (`n` factors), so that `powT t n` realises `t ^ (n + 1)`. -/
private def powT {α : Type} (t : LRc.Term α) : ℕ → LRc.Term α
  | 0 => t
  | (n + 1) => mulT (powT t n) t

/-- Realization of `mulT` at the `rexp`-reduct. -/
private theorem realize_mulT {K : Type} [LEc.Structure K] [Monoid K] {α : Type} (v : α → K)
    (hmul : ∀ x y : K, mulE x y = x * y) (a b : LRc.Term α) :
    @Term.realize LRc K (reductStruct K) α v (mulT a b) =
      @Term.realize LRc K (reductStruct K) α v a *
        @Term.realize LRc K (reductStruct K) α v b := by
  change @Term.realize LRc K (reductStruct K) α v
      (Term.func (Sum.inl (Sum.inl Ring.mulFunc)) ![a, b]) = _
  rw [Term.realize_func]
  have hx : (fun i => @Term.realize LRc K (reductStruct K) α v (![a, b] i)) =
      ![@Term.realize LRc K (reductStruct K) α v a,
        @Term.realize LRc K (reductStruct K) α v b] := by
    funext i; fin_cases i <;> rfl
  rw [hx, Work.WilC5.reductStruct_funMap_ring]
  exact hmul _ _

/-- Realization of `powT` at the `rexp`-reduct: `powT t n` realises `t ^ (n + 1)`. -/
private theorem realize_powT {K : Type} [LEc.Structure K] [Monoid K] {α : Type} (v : α → K)
    (hmul : ∀ x y : K, mulE x y = x * y) (t : LRc.Term α) (n : ℕ) :
    @Term.realize LRc K (reductStruct K) α v (powT t n) =
      (@Term.realize LRc K (reductStruct K) α v t) ^ (n + 1) := by
  induction n with
  | zero =>
    change @Term.realize LRc K (reductStruct K) α v t = _
    rw [Nat.zero_add, pow_one]
  | succ n ih =>
    change @Term.realize LRc K (reductStruct K) α v (mulT (powT t n) t) = _
    rw [realize_mulT v hmul, ih]
    exact (pow_succ _ (n + 1)).symm

/-- The `LRc`-formula `u * u = y ∧ y ^ (N+1) = z`, with `u` the last block of variables, `y` the
middle block and the parameter `z` the first block. -/
private def rootBody {γ : Type} (p : γ) (N : ℕ) : LRc.Formula ((γ ⊕ Fin 1) ⊕ Fin 1) :=
  Term.equal (mulT (Term.var (Sum.inr (0 : Fin 1))) (Term.var (Sum.inr (0 : Fin 1))))
      (Term.var (Sum.inl (Sum.inr (0 : Fin 1))))
    ⊓ Term.equal (powT (Term.var (Sum.inl (Sum.inr (0 : Fin 1)))) N)
      (Term.var (Sum.inl (Sum.inl p)))

/-- Realization of `rootBody` at the `rexp`-reduct. -/
private theorem rootBody_realize {K : Type} [LEc.Structure K] [Monoid K] {γ : Type} (p : γ)
    (N : ℕ) (hmul : ∀ x y : K, mulE x y = x * y) (v : ((γ ⊕ Fin 1) ⊕ Fin 1) → K) :
    @Formula.Realize LRc K (reductStruct K) ((γ ⊕ Fin 1) ⊕ Fin 1) (rootBody p N) v ↔
      (v (Sum.inr (0 : Fin 1)) * v (Sum.inr (0 : Fin 1)) = v (Sum.inl (Sum.inr (0 : Fin 1))))
        ∧ (v (Sum.inl (Sum.inr (0 : Fin 1)))) ^ (N + 1) = v (Sum.inl (Sum.inl p)) := by
  change ((Term.equal (mulT (Term.var (Sum.inr (0 : Fin 1))) (Term.var (Sum.inr (0 : Fin 1))))
      (Term.var (Sum.inl (Sum.inr (0 : Fin 1))))) ⊓
    (Term.equal (powT (Term.var (Sum.inl (Sum.inr (0 : Fin 1)))) N)
      (Term.var (Sum.inl (Sum.inl p))))).Realize v ↔ _
  rw [Formula.realize_inf, Formula.realize_equal, Formula.realize_equal]
  rw [realize_mulT v hmul, realize_powT v hmul]
  simp

/-- **The set of square `(N+1)`-th roots of `z` is `LRc`-definable from the parameter `z`**, at the
`rexp`-reduct of an `LEc`-structure.  The defining formula is `∃ u, (u * u = y ∧ y ^ (N+1) = z)`. -/
private theorem rootSet_definable_reduct {K : Type} [LEc.Structure K] [Monoid K]
    (hmul : ∀ x y : K, mulE x y = x * y) (z : K) (N : ℕ) :
    @Set.Definable₁ K ({z} : Set K) LRc (reductStruct K)
      {y : K | (∃ u : K, u * u = y) ∧ y ^ (N + 1) = z} := by
  rw [Set.Definable₁, Set.definable_iff_exists_formula_sum]
  let p : ({z} : Set K) := ⟨z, by simp⟩
  refine ⟨@Formula.iExs LRc (({z} : Set K) ⊕ Fin 1) (Fin 1) _ (rootBody p N), ?_⟩
  ext v
  simp only [Set.mem_ofPred_eq]
  rw [Formula.realize_iExs]
  constructor
  · rintro ⟨⟨u, hu⟩, huz⟩
    refine ⟨fun _ => u, ?_⟩
    rw [rootBody_realize p N hmul]
    exact ⟨by simpa using hu, by simpa using huz⟩
  · rintro ⟨i, hi⟩
    rw [rootBody_realize p N hmul] at hi
    obtain ⟨h1, h2⟩ := hi
    exact ⟨⟨i 0, by simpa using h1⟩, by simpa using h2⟩

/-- **Uniqueness of the positive `Q`-th root** (`Q ≥ 1`) in an ordered field: `y ↦ y ^ Q` is
strictly increasing on the positive elements. -/
private lemma pow_inj_of_pos {K : Type} [Field K] [LinearOrder K] [IsStrictOrderedRing K]
    {y y' : K} (hy : 0 < y) (hy' : 0 < y') {Q : ℕ} (hQ : 1 ≤ Q)
    (h : y ^ Q = y' ^ Q) : y = y' := by
  rcases lt_trichotomy y y' with hlt | heq | hgt
  · have h1 := pow_lt_pow_left₀ hlt (le_of_lt hy) (by omega : Q ≠ 0)
    rw [h] at h1
    exact absurd h1 (lt_irrefl _)
  · exact heq
  · have h1 := pow_lt_pow_left₀ hgt (le_of_lt hy') (by omega : Q ≠ 0)
    rw [h] at h1
    exact absurd h1 (lt_irrefl _)

/-- **Roots inside a `Dcl`-closed substructure.**  If `K ⊨ TE` (so `K` is real closed, via
`Work.WilC5.model_pow_root`/`Work.WilC2.model_exists_sq`) and `B ≤ K` is closed under the `LRc`-
definable closure `Dcl` (at the `rexp`-reduct), then every positive `z ∈ B` has its positive `Q`-th
root in `B`.  Indeed the root exists in the real closed field `K`, is *unique* (as a positive
element with `y^Q = z`), and the set `{y : K | 0 < y ∧ y^Q = z}` is a singleton definable in `LRc`
from the parameter `z ∈ B`; hence the root lies in `Dcl {z} ⊆ Dcl B ⊆ B`. -/
theorem DclRoot {K : Type} [WilkiesDesign.CG.LEc.Structure K] [Field K] [LinearOrder K]
    [IsStrictOrderedRing K] [FirstOrder.Ring.CompatibleRing K]
    [WilkiesDesign.CG.rexpL.Structure K] [(FirstOrder.Language.constantsOn ℝ).Structure K]
    (hK : K ⊨ WilkiesDesign.CG.TE)
    (hrexp : ∀ x : K, @FirstOrder.Language.Structure.funMap WilkiesDesign.CG.rexpL K _ 1
        WilkiesDesign.CG.rexpFunc.rexp ![x] = Work.WilC5.rexpFromExp x)
    (hadd : ∀ x y : K, Work.WilC5.addE x y = x + y)
    (hmul : ∀ x y : K, Work.WilC5.mulE x y = x * y)
    (hone : (Work.WilC5.oneE : K) = 1)
    (hleneg : ∀ x y : K, Work.WilC5.leE x y ↔ x ≤ y)
    {B : WilkiesDesign.CG.LRc.Substructure K}
    (hBdcl : @Work.WilC2.Dcl K (Work.WilC5.reductStruct K) (B : Set K) ⊆ (B : Set K))
    {z : K} (hz : z ∈ (B : Set K)) (hzpos : 0 < z) {Q : ℕ} (hQ : 1 ≤ Q) :
    ∃ b ∈ (B : Set K), 0 < b ∧ b ^ Q = z := by
  classical
  have hTE : K ⊨ WilkiesDesign.CG.TE := hK
  -- ## 0. The `LEc` ring operations not fixed by the hypotheses
  have hzero : (Work.WilC5.zeroE : K) = 0 := Work.WilC5.S4Exp.zeroE_eq_zero hTE hadd
  have hneg : ∀ x : K, Work.WilC5.negE x = -x :=
    fun x => Work.WilC5.S4Exp.negE_eq_neg hTE hadd x
  -- ## 1. A `Ring.CompatibleRing` structure whose ring is that of the `rexp`-reduct
  let myCR : FirstOrder.Ring.CompatibleRing K :=
    { toStructure := @Work.WilC5.lrcRingReduct K (Work.WilC5.instStructureLRcOfLEc K)
      funMap_add := fun x => by
        rw [Work.WilC5.lrcRingReduct_funMap]
        have hx : x = ![x 0, x 1] := by funext i; fin_cases i <;> rfl
        rw [hx]; exact hadd _ _
      funMap_mul := fun x => by
        rw [Work.WilC5.lrcRingReduct_funMap]
        have hx : x = ![x 0, x 1] := by funext i; fin_cases i <;> rfl
        rw [hx]; exact hmul _ _
      funMap_neg := fun x => by
        rw [Work.WilC5.lrcRingReduct_funMap]
        have hx : x = ![x 0] := by funext i; fin_cases i <;> rfl
        rw [hx]; exact hneg _
      funMap_zero := fun x => by
        rw [Work.WilC5.lrcRingReduct_funMap]
        rw [show x = default from Subsingleton.elim _ _]
        exact hzero
      funMap_one := fun x => by
        rw [Work.WilC5.lrcRingReduct_funMap]
        rw [show x = default from Subsingleton.elim _ _]
        exact hone }
  letI : FirstOrder.Ring.CompatibleRing K := myCR
  letI hRX : rexpL.Structure K := Work.WilC5.lrcRexpReduct K
  letI hCT : (FirstOrder.Language.constantsOn ℝ).Structure K := Work.WilC5.lrcConstReduct K
  letI hLR : LRc.Structure K := LR.withConstantsStructure ℝ
  -- ## 2. The canonical structure is the reduct, and it is a model of `TR`
  have hstruct : (Work.WilC5.reductStruct K : LRc.Structure K) = (inferInstance : LRc.Structure K) :=
    Work.WilC5.reductStruct_eq_withConstants (M := K)
  have hTRRed : @Theory.Model LRc K (Work.WilC5.reductStruct K) TR :=
    Work.WilC5.reduct_model_TR K hTE
  have hTR : @Theory.Model LRc K (inferInstance) TR := hstruct ▸ hTRRed
  -- ## 3. A positive `Q`-th root of `z`, manufactured as a square
  obtain ⟨s, hs⟩ := Work.WilC2.model_exists_sq (M := K) hTR z (le_of_lt hzpos)
  obtain ⟨w, hw⟩ := Work.WilC5.model_pow_root (M := K) hTR s (n := 2 * Q) (by omega)
  have hwz : w ^ (2 * Q) = z := by rw [hw, pow_two]; exact hs.symm
  have hpos : 0 < w * w := by
    refine mul_self_pos.mpr ?_
    intro hw0
    rw [hw0, zero_pow (by omega : 2 * Q ≠ 0)] at hwz
    exact absurd hwz.symm (ne_of_gt hzpos)
  have hbpow : (w * w) ^ Q = z := by
    rw [← pow_two w, ← pow_mul w 2 Q, hwz]
  -- ## 4. The definable set of square `Q`-th roots of `z` is the singleton `{w * w}`
  have hset : {y : K | (∃ u : K, u * u = y) ∧ y ^ Q = z} = ({w * w} : Set K) := by
    ext y
    constructor
    · rintro ⟨⟨u, rfl⟩, hyQ⟩
      have huu : u * u ≠ 0 := by
        intro h0
        rw [h0, zero_pow (by omega : Q ≠ 0)] at hyQ
        exact absurd hyQ.symm (ne_of_gt hzpos)
      have hu0 : u ≠ 0 := fun h => huu (by rw [h, mul_zero])
      exact pow_inj_of_pos (mul_self_pos.mpr hu0) hpos hQ (hyQ.trans hbpow.symm)
    · intro hy
      rw [Set.mem_singleton_iff] at hy
      subst hy
      exact ⟨⟨w, rfl⟩, hbpow⟩
  -- ## 5. `{w * w}` is definable from `{z}` in `LRc`, hence lies in `Dcl {z} ⊆ Dcl B ⊆ B`
  have hdef_red : @Set.Definable₁ K ({z} : Set K) LRc (Work.WilC5.reductStruct K)
      ({w * w} : Set K) := by
    have hdef_set := rootSet_definable_reduct (K := K) hmul z (Q - 1)
    have hset2 : {y : K | (∃ u : K, u * u = y) ∧ y ^ Q = z} =
        {y : K | (∃ u : K, u * u = y) ∧ y ^ (Q - 1 + 1) = z} := by
      ext y; rw [Nat.sub_add_cancel hQ]
    rw [← hset, hset2]
    exact hdef_set
  have hb_dcl : w * w ∈ @Work.WilC2.Dcl K (Work.WilC5.reductStruct K) ({z} : Set K) := hdef_red
  have hmono : @Work.WilC2.Dcl K (Work.WilC5.reductStruct K) ({z} : Set K) ⊆
      @Work.WilC2.Dcl K (Work.WilC5.reductStruct K) (B : Set K) :=
    @Work.WilC2.dcl_mono K (Work.WilC5.reductStruct K) ({z} : Set K) (B : Set K)
      (Set.singleton_subset_iff.mpr hz)
  exact ⟨w * w, hBdcl (hmono hb_dcl), hpos, hbpow⟩

end Work.WilC5
