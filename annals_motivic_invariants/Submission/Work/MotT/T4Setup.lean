import Mathlib
import Submission.Work.MotT.Defs
import Submission.Work.MotV.twCoord_eq
import Submission.Work.MotT.TKSetup
import Submission.Work.MotC2.Translation
import Submission.Work.MotC2.Negation
import Submission.Work.MotT.functionField_baseChange_map

set_option linter.unusedVariables false -- v435-speed

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

set_option autoImplicit false
set_option linter.style.haveILetI false

/-!
# Vocabulary of the T4 (LAM) node `Work.MotT.twist_iso_pointK`

The LAM proof (`MOTIVIC_C6_R4_LEAD.md` §3.3, node T4) runs the following objects:

* the **Kummer cocycle** `c(γ,h) = γ(⁵√h)/⁵√h ∈ μ₅` of `h ∈ Kˣ` at `γ ∈ Aut_K(K̄)`;
* the **diagonal automorphism** `Δ_c` of `Ω = K̄(E)`, acting on the Klein ratios `κ_i/κ_0` by
  multiplication by `c^i` (`Work.MotV.KleinData.Good.T_diag`);
* its identification `Δ_c = τ_{Q_c}` with a **translation** (a consequence of node C2,
  `Work.MotC2.aut_functionField`; the `[-1]`-part is provably trivial, see
  `Submission/Work/MotT/diagEps_eq_zero.lean`), giving the 5-torsion point `Q_c = η(c)`;
* the **two-root Kummer field** `L = K(ζ, w₁, w₂)` (`KummerField2`) — node T4 runs C2 over `L`,
  so that the point produced by the LAM argument is `L`-rational and hence `K`-rational after the
  Galois descent `L^{Gal(L/K)} = K`;
* the **twisted Galois action on the points of `E`**: `γ ·_h P = γP - η(c(γ,h))`.

## Two corrections relative to the previous session (important)

1. **Sign of the twisted point action.**  The coordinate functions `twCoordK D h i = w^{-i}κ_i/κ_0`
   are invariant under the *function-field* action `γ*_h = Δ_{c(γ,h)} ∘ γ̃`.  The corresponding
   action on the points of `E` is `γ ·_h P = γP - η(c(γ,h))` (because `τ_{Q}(κ_i/κ_0) =
   c^i κ_i/κ_0` with `c` the cocycle of `Δ_c = τ_Q`), so the `K`-points of the twist `C_h` are the
   points with `γP = P + η(c(γ,h))` — the *opposite* sign to the one used last session.  So
   `IsTwistKPoint h P` must read `∀ γ, galPt γ P = P + etaPt h γ`.

2. **`AutRigid` (node C2 as defined in `Submission/Work/MotT/Defs.lean`) is mis-stated.**  It reads
   `Θ = transAlgEquiv E Q * (negAlgEquiv E) ^ (ε : ℤ)` with `ε : ℤˣ`.  Since `ℤˣ = {1, -1}` and
   `negAlgEquiv E` is an involution (`Work.MotC2.negAlgEquiv_mul_self`),
   `(negAlgEquiv E) ^ (ε : ℤ) = negAlgEquiv E` for *every* `ε : ℤˣ`
   (see `Submission/Work/MotT/autRigid_defect.lean`): the pure-translation case `ε = 0` is never
   allowed, so `AutRigid` asserts that *every* automorphism is `τ_Q ∘ [-1]`, which is false.
   Consequently the hypothesis `hC2` of the requested statement `Work.MotT.twist_iso_pointK` is a
   *false* proposition, i.e. that statement is *vacuous*; the true mathematics is the design's T4,
   which runs C2 itself (`Work.MotC2.aut_functionField`, proved, `ε : Fin 2`) and is the form used
   by `Work.MotT.c2_decomposition` below.
-/

namespace Work.MotT

noncomputable section

open WeierstrassCurve WeierstrassCurve.Affine

variable {K : Type} [Field K]

/-- The base change of an elliptic curve is elliptic (instance, in a form that the elaborator finds
for `D.E.baseChange K̄`). -/
theorem baseChange_isElliptic (D : Work.MotV.KleinData K) (hD : D.Good) :
    (D.E.baseChange (KbK K)).IsElliptic := by
  haveI := hD.elliptic
  exact inferInstanceAs ((D.E.map (algebraMap K (KbK K))).IsElliptic)

/-! ## §1 The Kummer cocycle -/

/-- **The Kummer cocycle** `c(γ,h) = γ(⁵√h)/⁵√h` of `h ∈ Kˣ` at `γ`. -/
def kummerCocycle (h : K) (γ : KbK K ≃ₐ[K] KbK K) : KbK K :=
  γ (root5K h) / root5K h

/-- `c(γ,h) ^ 5 = 1`: the cocycle takes values in `μ₅`. -/
theorem kummerCocycle_pow_five (h : K) (hh : h ≠ 0) (γ : KbK K ≃ₐ[K] KbK K) :
    kummerCocycle h γ ^ 5 = 1 := by
  have h0 : root5K h ≠ 0 := root5K_ne_zero hh
  have hγ : γ (root5K h) ^ 5 = root5K h ^ 5 := by
    rw [← map_pow, root5K_spec, γ.commutes]
  rw [kummerCocycle, div_pow, hγ, div_self (pow_ne_zero 5 h0)]

/-- A fifth root of unity different from `1` is primitive. -/
theorem isPrimitiveRoot_of_pow_five_eq_one {c : KbK K} (hc : c ^ 5 = 1) (h1 : c ≠ 1) :
    IsPrimitiveRoot c 5 := by
  rw [IsPrimitiveRoot.iff_orderOf]
  have hprime : Nat.Prime 5 := by norm_num
  rcases hprime.eq_one_or_self_of_dvd (orderOf c) (orderOf_dvd_iff_pow_eq_one.mpr hc) with h | h
  · exact absurd (orderOf_eq_one_iff.mp h) h1
  · exact h

/-! ## §2 The Galois action on the points of `E`, translation and negation -/

/-- The `K`-algebra automorphism `γ` of `K̄` acting on the points of `E_{K̄}`. -/
def galPt (D : Work.MotV.KleinData K) (hD : D.Good) (γ : KbK K ≃ₐ[K] KbK K)
    (P : (D.E.baseChange (KbK K)).toAffine.Point) : (D.E.baseChange (KbK K)).toAffine.Point :=
  letI := Classical.decEq (KbK K)
  letI : (D.E.baseChange (KbK K)).IsElliptic := baseChange_isElliptic D hD
  WeierstrassCurve.Affine.Point.map (W' := D.E) (S := K) (F := KbK K) (K := KbK K) γ.toAlgHom P

/-- The pullback of the translation by a point of `E_{K̄}`. -/
def transK (D : Work.MotV.KleinData K) (hD : D.Good)
    (Q : (D.E.baseChange (KbK K)).toAffine.Point) : OmK D ≃ₐ[KbK K] OmK D := by
  haveI := baseChange_isElliptic D hD
  letI := Classical.decEq (KbK K)
  exact Work.MotC2.transAlgEquiv (D.E.baseChange (KbK K)) Q

/-- The pullback of `[-1]`. -/
def negK (D : Work.MotV.KleinData K) (hD : D.Good) : OmK D ≃ₐ[KbK K] OmK D := by
  haveI := baseChange_isElliptic D hD
  letI := Classical.decEq (KbK K)
  exact Work.MotC2.negAlgEquiv (D.E.baseChange (KbK K))

/-! ## §3 The two-root Kummer field `L = K(ζ, w₁, w₂)`

Node T4 runs C2 over the finite Galois field `L = K(ζ, w₁, w₂)` (with `wᵢ = root5K hᵢ`): this is
what makes the point produced by the LAM argument `L`-rational, hence `K`-rational after the Galois
descent `L^{Gal(L/K)} = K`.  The one-root field `K(ζ, w) = KummerField K h hk` and its transport
`ML D h hk` live in `Submission/Work/MotT/TKSetup.lean`. -/

/-- **`L = K(ζ, w₁, w₂)`**: the two-root Kummer field. -/
def KummerField2 (K : Type) [Field K] (h₁ h₂ : K) (hk : ringChar K ≠ 5) :
    IntermediateField K (KbK K) :=
  IntermediateField.adjoin K ({zeta5K K hk, root5K h₁, root5K h₂} : Set (KbK K))

theorem zeta5K_mem_KummerField2 (h₁ h₂ : K) (hk : ringChar K ≠ 5) :
    zeta5K K hk ∈ KummerField2 K h₁ h₂ hk :=
  IntermediateField.subset_adjoin K _ (by simp [KummerField2])

theorem root5K_mem_KummerField2_left (h₁ h₂ : K) (hk : ringChar K ≠ 5) :
    root5K h₁ ∈ KummerField2 K h₁ h₂ hk :=
  IntermediateField.subset_adjoin K _ (by simp [KummerField2])

theorem root5K_mem_KummerField2_right (h₁ h₂ : K) (hk : ringChar K ≠ 5) :
    root5K h₂ ∈ KummerField2 K h₁ h₂ hk :=
  IntermediateField.subset_adjoin K _ (by simp [KummerField2])

/-- The element `w₁ = ⁵√h₁` of `L = K(ζ, w₁, w₂)`. -/
def wL1 (K : Type) [Field K] (h₁ h₂ : K) (hk : ringChar K ≠ 5) : ↥(KummerField2 K h₁ h₂ hk) :=
  ⟨root5K h₁, root5K_mem_KummerField2_left h₁ h₂ hk⟩

/-- The element `w₂ = ⁵√h₂` of `L = K(ζ, w₁, w₂)`. -/
def wL2 (K : Type) [Field K] (h₁ h₂ : K) (hk : ringChar K ≠ 5) : ↥(KummerField2 K h₁ h₂ hk) :=
  ⟨root5K h₂, root5K_mem_KummerField2_right h₁ h₂ hk⟩

/-- The primitive fifth root of unity as an element of `L`. -/
def zL2 (K : Type) [Field K] (h₁ h₂ : K) (hk : ringChar K ≠ 5) :
    ↥(KummerField2 K h₁ h₂ hk) :=
  ⟨zeta5K K hk, zeta5K_mem_KummerField2 h₁ h₂ hk⟩

theorem wL1_pow_five (K : Type) [Field K] (h₁ h₂ : K) (hk : ringChar K ≠ 5) :
    (wL1 K h₁ h₂ hk) ^ 5 = algebraMap K ↥(KummerField2 K h₁ h₂ hk) h₁ := by
  apply Subtype.ext
  show root5K h₁ ^ 5 = algebraMap K (KbK K) h₁
  exact root5K_spec h₁

theorem wL2_pow_five (K : Type) [Field K] (h₁ h₂ : K) (hk : ringChar K ≠ 5) :
    (wL2 K h₁ h₂ hk) ^ 5 = algebraMap K ↥(KummerField2 K h₁ h₂ hk) h₂ := by
  apply Subtype.ext
  show root5K h₂ ^ 5 = algebraMap K (KbK K) h₂
  exact root5K_spec h₂

theorem zL2_isPrimitiveRoot (K : Type) [Field K] (h₁ h₂ : K) (hk : ringChar K ≠ 5) :
    IsPrimitiveRoot (zL2 K h₁ h₂ hk) 5 := by
  haveI : Fact (Nat.Prime 5) := ⟨by norm_num⟩
  have hζ := zeta5K_isPrimitiveRoot K hk
  rw [IsPrimitiveRoot.iff_orderOf]
  refine orderOf_eq_prime ?_ ?_
  · apply Subtype.ext
    show (zeta5K K hk) ^ 5 = 1
    exact hζ.pow_eq_one
  · intro h1
    exact hζ.ne_one (by norm_num) (congrArg Subtype.val h1)

/-! ## §4 The function field `L(E)` over the two-root Kummer field `L = K(ζ, w₁, w₂)` -/

variable (D : Work.MotV.KleinData K)

/-- **`M = L(E)`**: the function field of the model base changed to the two-root Kummer field
`L = K(ζ, w₁, w₂)`. -/
abbrev ML2 (D : Work.MotV.KleinData K) (h₁ h₂ : K) (hk : ringChar K ≠ 5) : Type :=
  FunctionField (D.E.baseChange ↥(KummerField2 K h₁ h₂ hk))

/-- The twisted Klein coordinates of the T-twist for `h₁` inside `M = L(E)`. -/
def yM21 (D : Work.MotV.KleinData K) (h₁ h₂ : K) (hk : ringChar K ≠ 5) (i : Fin 5) :
    ML2 D h₁ h₂ hk :=
  (algebraMap ↥(KummerField2 K h₁ h₂ hk) (ML2 D h₁ h₂ hk) (wL1 K h₁ h₂ hk))⁻¹ ^ (i : ℕ) *
    (Work.MotV.kleinCoord D ↥(KummerField2 K h₁ h₂ hk) i /
      Work.MotV.kleinCoord D ↥(KummerField2 K h₁ h₂ hk) 0)

/-- The twisted Klein coordinates of the T-twist for `h₂` inside `M = L(E)`. -/
def yM22 (D : Work.MotV.KleinData K) (h₁ h₂ : K) (hk : ringChar K ≠ 5) (i : Fin 5) :
    ML2 D h₁ h₂ hk :=
  (algebraMap ↥(KummerField2 K h₁ h₂ hk) (ML2 D h₁ h₂ hk) (wL2 K h₁ h₂ hk))⁻¹ ^ (i : ℕ) *
    (Work.MotV.kleinCoord D ↥(KummerField2 K h₁ h₂ hk) i /
      Work.MotV.kleinCoord D ↥(KummerField2 K h₁ h₂ hk) 0)

/-- The `K`-twist field `K(C_{h₁})` inside `M = L(E)`. -/
def AM21 (D : Work.MotV.KleinData K) (h₁ h₂ : K) (hk : ringChar K ≠ 5) :
    IntermediateField K (ML2 D h₁ h₂ hk) :=
  IntermediateField.adjoin K (Set.range (yM21 D h₁ h₂ hk))

/-- The `K`-twist field `K(C_{h₂})` inside `M = L(E)`. -/
def AM22 (D : Work.MotV.KleinData K) (h₁ h₂ : K) (hk : ringChar K ≠ 5) :
    IntermediateField K (ML2 D h₁ h₂ hk) :=
  IntermediateField.adjoin K (Set.range (yM22 D h₁ h₂ hk))

/-- The base change map `M = L(E) → K̄(E)`. -/
def iota2 (D : Work.MotV.KleinData K) (h₁ h₂ : K) (hk : ringChar K ≠ 5) :
    ML2 D h₁ h₂ hk →ₐ[K] OmK D :=
  Classical.choose (functionField_baseChange_map K D.E ↥(KummerField2 K h₁ h₂ hk) (KbK K)
    (IsScalarTower.toAlgHom K ↥(KummerField2 K h₁ h₂ hk) (KbK K)))

/-- The defining properties of `iota2`: it acts on the constants `L` by the inclusion `L ⊆ K̄` and
fixes `x, y`; in particular it is injective. -/
theorem iota2_spec (D : Work.MotV.KleinData K) (h₁ h₂ : K) (hk : ringChar K ≠ 5) :
    (∀ l : ↥(KummerField2 K h₁ h₂ hk),
        iota2 D h₁ h₂ hk (algebraMap ↥(KummerField2 K h₁ h₂ hk) (ML2 D h₁ h₂ hk) l) =
          algebraMap (KbK K) (OmK D) l) ∧
      iota2 D h₁ h₂ hk (Work.MotV.genX (D.E.baseChange ↥(KummerField2 K h₁ h₂ hk))) =
        Work.MotV.genX (D.E.baseChange (KbK K)) ∧
      iota2 D h₁ h₂ hk (Work.MotV.genY (D.E.baseChange ↥(KummerField2 K h₁ h₂ hk))) =
        Work.MotV.genY (D.E.baseChange (KbK K)) ∧
      Function.Injective (iota2 D h₁ h₂ hk) := by
  have h := Classical.choose_spec (functionField_baseChange_map K D.E ↥(KummerField2 K h₁ h₂ hk)
    (KbK K) (IsScalarTower.toAlgHom K ↥(KummerField2 K h₁ h₂ hk) (KbK K)))
  exact ⟨h.1, h.2.1, h.2.2.1, h.2.2.2 (fun a b hab => Subtype.ext hab)⟩

theorem iota2_algebraMap (D : Work.MotV.KleinData K) (h₁ h₂ : K) (hk : ringChar K ≠ 5)
    (l : ↥(KummerField2 K h₁ h₂ hk)) :
    iota2 D h₁ h₂ hk (algebraMap ↥(KummerField2 K h₁ h₂ hk) (ML2 D h₁ h₂ hk) l) =
      algebraMap (KbK K) (OmK D) l :=
  (iota2_spec D h₁ h₂ hk).1 l

theorem iota2_genX (D : Work.MotV.KleinData K) (h₁ h₂ : K) (hk : ringChar K ≠ 5) :
    iota2 D h₁ h₂ hk (Work.MotV.genX (D.E.baseChange ↥(KummerField2 K h₁ h₂ hk))) =
      Work.MotV.genX (D.E.baseChange (KbK K)) :=
  (iota2_spec D h₁ h₂ hk).2.1

theorem iota2_genY (D : Work.MotV.KleinData K) (h₁ h₂ : K) (hk : ringChar K ≠ 5) :
    iota2 D h₁ h₂ hk (Work.MotV.genY (D.E.baseChange ↥(KummerField2 K h₁ h₂ hk))) =
      Work.MotV.genY (D.E.baseChange (KbK K)) :=
  (iota2_spec D h₁ h₂ hk).2.2.1

theorem iota2_injective (D : Work.MotV.KleinData K) (h₁ h₂ : K) (hk : ringChar K ≠ 5) :
    Function.Injective (iota2 D h₁ h₂ hk) :=
  (iota2_spec D h₁ h₂ hk).2.2.2

end

end Work.MotT
