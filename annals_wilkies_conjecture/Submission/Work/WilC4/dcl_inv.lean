/-
  WilC4 : area C4 of `annals_wilkies_conjecture` (Wilkie's valuation inequality for `TR`).

  The definable closure `Dcl S A` is closed under inversion: if `x` is definable from the
  parameters `S ∪ A` and `x ≠ 0`, then so is `x⁻¹`.

  The language `LRc` has no function symbol for inversion, so the argument is that `y ↦ y⁻¹`
  is cut out, over the parameter `x`, by the atomic formula `x * y = 1`.  Formally: the
  relation `w (inr 0) * w (inl 0) = 1` is definable (in the language of rings, with no
  parameters); intersecting it with the A-definable condition `w (inr 0) = x` and projecting
  out the (existentially quantified) first coordinate leaves the A-definable set
  `{y | x * y = 1}`, which is the singleton `{x⁻¹}` because `x ≠ 0`.
-/
import Mathlib
import Submission.Work.WilC4.Defs

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section
open Classical
open FirstOrder FirstOrder.Language
namespace Work.WilC4
open WilkiesDesign WilkiesDesign.CG

/-! ## The `Fin 1`-singleton indexed by a point -/

/-- The singleton consisting of the constant tuple `fun _ => x` is the set of tuples whose
zeroth coordinate is `x`.  This is the only place where the two formulations of "`{x}` is
definable" (the `Set.Definable` one and the one with an explicit tuple) are compared. -/
theorem const_tuple_set {M : Type} (x : M) :
    ({fun _ : Fin 1 => x} : Set (Fin 1 → M)) = {v : Fin 1 → M | v 0 = x} := by
  ext v
  simp only [Set.mem_singleton_iff, Set.mem_ofPred_eq]
  constructor
  · intro hv
    rw [hv]
  · intro hv
    funext i
    rw [Subsingleton.elim i 0]
    exact hv

/-- `Dcl S A` is closed under inversion.  The hypothetical `x ≠ 0` is what makes the
parameter-definable set `{y | x * y = 1}` the singleton `{x⁻¹}`. -/
theorem dcl_inv {M : Type} [Field M] [LinearOrder M] [IsStrictOrderedRing M] [FirstOrder.Ring.CompatibleRing M] [WilkiesDesign.CG.rexpL.Structure M] [(FirstOrder.Language.constantsOn ℝ).Structure M] {S A : Set M} {x : M} (hx : x ∈ Dcl S A) (hx0 : x ≠ 0) : x⁻¹ ∈ Dcl S A := by
  show (S ∪ A).Definable LRc {fun _ : Fin 1 => x⁻¹}
  -- `x` is definable, hence so is the set of `Fin 1`-tuples whose zeroth coordinate is `x`.
  have hxdef : (S ∪ A).Definable LRc {v : Fin 1 → M | v 0 = x} := by
    rw [← const_tuple_set x]
    simpa only [Dcl, DefinableElt, Set.mem_ofPred_eq] using hx
  -- The graph of multiplication (with the unit `1` of the field) is definable without
  -- parameters: it is the set where the two terms `w (inr 0) * w (inl 0)` and `1` agree.
  have hG : (∅ : Set M).Definable LRc
      {w : (Fin 1 ⊕ Fin 1) → M | w (Sum.inr 0) * w (Sum.inl 0) = 1} := by
    let tmul : LRc.Term (Fin 1 ⊕ Fin 1) :=
      Term.func (Sum.inl (Sum.inl FirstOrder.Ring.mulFunc))
        ![Term.var (Sum.inr 0), Term.var (Sum.inl 0)]
    let tone : LRc.Term (Fin 1 ⊕ Fin 1) :=
      Term.func (Sum.inl (Sum.inl FirstOrder.Ring.oneFunc)) Fin.elim0
    have hf : (∅ : Set M).DefinableFun LRc tmul.realize := Term.definableFun_realize tmul
    have hg : (∅ : Set M).DefinableFun LRc tone.realize := Term.definableFun_realize tone
    have h := hf.ofPred_eq hg
    convert h using 1
    ext w
    simp [tmul, tone]
  -- The same graph, restricted to the `inr`-coordinate holding the parameter `x`.
  have hC : (S ∪ A).Definable LRc {w : (Fin 1 ⊕ Fin 1) → M | w (Sum.inr 0) = x} := by
    have h := hxdef.preimage_comp (fun _ : Fin 1 => (Sum.inr 0 : Fin 1 ⊕ Fin 1))
    convert h using 1
    ext w
    simp
  have hInt : (S ∪ A).Definable LRc
      ({w : (Fin 1 ⊕ Fin 1) → M | w (Sum.inr 0) * w (Sum.inl 0) = 1} ∩
        {w : (Fin 1 ⊕ Fin 1) → M | w (Sum.inr 0) = x}) :=
    (hG.mono (Set.empty_subset _)).inter hC
  -- Projecting out the existentially quantified first coordinate leaves `{y | x * y = 1}`.
  have hProj := Set.Definable.exists_of_finite hInt
  have hset : {v : Fin 1 → M | ∃ u : Fin 1 → M, Sum.elim v u ∈
      ({w : (Fin 1 ⊕ Fin 1) → M | w (Sum.inr 0) * w (Sum.inl 0) = 1} ∩
        {w : (Fin 1 ⊕ Fin 1) → M | w (Sum.inr 0) = x})} = {fun _ : Fin 1 => x⁻¹} := by
    ext v
    simp only [Set.mem_ofPred_eq, Set.mem_inter_iff, Set.mem_singleton_iff]
    constructor
    · rintro ⟨u, h1, h2⟩
      have h1' : u 0 * v 0 = 1 := by simpa using h1
      have h2' : u 0 = x := by simpa using h2
      have hxv : x * v 0 = 1 := by rw [← h2']; exact h1'
      funext i
      rw [Subsingleton.elim i 0]
      calc v 0 = (x⁻¹ * x) * v 0 := by rw [inv_mul_cancel₀ hx0, one_mul]
        _ = x⁻¹ * (x * v 0) := by rw [mul_assoc]
        _ = x⁻¹ := by rw [hxv, mul_one]
    · intro hv
      refine ⟨fun _ => x, ?_, ?_⟩
      · rw [hv]
        simpa using mul_inv_cancel₀ hx0
      · rfl
  rw [hset] at hProj
  exact hProj

end Work.WilC4
