import Mathlib
import Submission.Work.MotV5.ASTwistData
import Submission.Work.MotV5.Defs
import Submission.Work.MotV5.tp_as
import Submission.Work.MotV5.asTwistFieldTrue_basic
import Submission.Work.MotV5.RigAS.twistFieldTrue_sup_asRoot
import Submission.Work.MotV5.RigAS.kleinField_le_twistFieldTrue
import Submission.Work.MotV5.RigAS.PlaceData
import Submission.Work.MotV5.RigAS.descent
import Submission.Work.MotV5.exists_polarApprox_of_unramified
import Submission.Work.MotV5.RigAS.placeData_e1
import Submission.Work.Reflect.PolyId
set_option maxRecDepth 100000

set_option linter.unusedVariables false -- v435-speed

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.MotV5.RigAS

open Work.MotV5
open scoped WithZero

set_option maxHeartbeats 1600000
set_option linter.unusedSectionVars false

/-!
# The Artin–Schreier bridge for the corrected twist field (rigidity branch)

Target of this file: `Work.MotV5.RigAS.bridge_twist`, the AS-bridge condition
`Work.MotV5.ASUnramified` for the *corrected* twist field
`F = asTwistFieldTrue D g τ σS = asTwistFieldFix D τ σS ⊓ asFieldL D g`
(the fixed field of the twisted action `σ' = asTwistAction D τ σS` inside `L(E) = asFieldL D g`).

The paper's analytic half (`Work.MotV5.hurwitz_AS`, `Work.MotV5.tp_as`,
`Work.MotV5.base_preserved_AS`, in particular `asHyp_of_ASUnramified`) consumes exactly this
condition to produce the "base field is preserved" input of the rigidity proof, so `bridge_twist`
is the geometric input of the whole characteristic-`5` branch.

## Elementary companion: the bridge for `L(E)` is trivial

The ambient field `L(E) = asFieldL D g` *contains* the Artin–Schreier root
`W = algebraMap (Kb 𝕜) (Om D) (asRoot g)`, and `W⁵ - W = g` by `asRoot_spec`.  Hence the bridge
condition for `L(E)` holds with `u = W` and zero remainder (`bridge_asFieldL` below).

The corrected twist field `F` does **not** contain `W`
(`Work.MotV5.asRoot_notMem_asTwistFieldTrue`), so the same trivial witness is unavailable; the
bridge for `F` must produce, at each valuation of `F` at which `t` has a pole, an element of `F`
whose `℘ = X⁵ - X` value agrees with `g` modulo the valuation ring.  Note that this is *not*
the statement that `g ∈ ℘(F_v)`: only the polar part has to be matched.

## Route

`L(E)/F` is cyclic of degree `5` with group `⟨σ'⟩` (Artin, from `h5L`/`hneL`/`hpres`); the
compositum identity `asTwistFieldTrue ⊔ K⟮asRoot g⟯ = asFieldL` records that `L(E) = F⟮W⟯`
(delegated as `MotV5/RigAS/twistFieldTrue_sup_asRoot`).

**The geometric part of `F` is *not* all of `K(E)`.**  `σ' = σS ∘ τ` fixes `K(E)` pointwise only
through `τ` (`hτk`); `σS` acts on the Klein ratios by the shift
`rᵢ = κᵢ/κ₀ ↦ r_{i+1}/r₁`, so `F ∩ K(E) = K(E)^{⟨σS⟩} = K(E')`, `E' = E/⟨Q⟩` the quotient by the
`5`-torsion translation `Q` that realises `σS` (`hσS` + the Klein model axioms force
`σS = translation by Q`, `Q ≠ 0`; the degenerate `σS = 1` is excluded).  The correct membership
lemma is therefore `x ∈ kleinField D → σS x = x → x ∈ asTwistFieldTrue D g τ σS`
(delegated as `MotV5/RigAS/kleinField_le_twistFieldTrue`); the statement
`kleinField D ≤ asTwistFieldTrue D g τ σS` is **false** and must not be used.

**What remains for `bridge_twist`.**  For a place `P` of `F` over the pole of `t`:
* the relation `e(P/∞) · e(R/P) = e(R/∞) = 5` (`R` a place of `L(E)` above `P`, `e(R/∞) = 5`
  because `W⁵ - W = g` makes the extension `L(E)/K(E)` totally ramified over every place of
  `K(E)` above `∞`, which has `e = 1`, while `K(E)/K` is a constant curve) gives
  `e(P/∞) ∈ {1, 5}`; the necessary condition `5 ∣ e(P/∞)` for the bridge is therefore equivalent
  to `e(P/∞) = 5`, i.e. to `e(R/P) = 1`;
* `e(R/P) = 1` holds because `σ'` acts on the residue field `κ(R)` by the (nontrivial) action of
  `σS`, whose geometric part is the translation by `Q ≠ 0`: the induced automorphism of `κ(R)`
  moves `x` or `y` (the coordinates separate points), so `κ(P) ⊊ κ(R)`, `f(R/P) = 5`, and
  `e(R/P) = 1`; the alternative `e(R/P) = 5` (totally ramified local extension) would force
  `e(P/∞) = 1` and then `ord_P(g) = -3 ∉ 5ℤ`, which is impossible for a `u ∈ F_P` with
  `ord_P(g - ℘u) ≥ 0`;
* in the split case `F_P = L(E)_R` (so `W ∈ F_P`), density of `F` in `F_P` immediately gives
  `u ∈ F` with `v(g - ℘u) ≤ 1`; in the inert case `F_P = L(E)_R^{σ'}` one takes the negative-part
  (`u₀ = ∑_{n<0} bₙ zⁿ`) of the expansion of `W` in a uniformiser `z` of `F_P`: the recursion
  `bₙ = b_{n/5}⁵ - gₙ` (from `℘(W) = g`) shows inductively that every `bₙ` (`n < 0`) lies in the
  residue field `κ(P)` (the chain `n, n/5, …` terminates in `{-1,-2,-3,-4}`), so `u₀ ∈ F_P`, and
  `℘(u₀) - g` has only nonnegative `z`-adic exponents, i.e. `v(g - ℘u₀) ≤ 1`; density of `F`
  in `F_P` upgrades `u₀` to an element `u ∈ F` (for `δ ∈ F_P` with `v(δ) ≤ 1` one has
  `v(℘(δ)) ≤ v(δ) ≤ 1`, so small perturbations of `u₀` do not destroy the condition).

**Missing machinery.**  The second and third bullets need the local theory of the places of
`F`/`L(E)` above `∞` (ramification indices, residue fields, decomposition groups, completions and
the density of `F` in them, and the `℘`-recursion for the expansion of `W`).  The pieces that are
*formalised* so far are `bridge_asFieldL`, `twistFieldTrue_sup_asRoot` and
`kleinField_le_twistFieldTrue`; the rest is the local chapter.

## Sharpened analysis of the bridge condition (state of the argument)

`F = asTwistFieldTrue D g τ σS` has transcendence degree `2` over `𝕜` (it contains
`kleinField D ^ ⟨σS⟩`, a function field over `K = 𝕜(t)`), so its `𝕜`-valuations are divisorial and
`e·f·g = [F : 𝕜(t)]` is *not* available.  The correct statements are the following.

* **The pole order of `t` on `F` is a multiple of `5`.**  Write `v = v_P^m` with `P` a prime divisor
  of `F`.  The centre of `v` on `ℙ¹_t` is the place `∞` (the only place of `𝕜(t)` at which `t` has a
  pole).  In the Artin–Schreier cover `L₀ = K⟮W⟯ = 𝕜(W)(t)` of `K = 𝕜(t)`, the function `t` has a
  pole of order `5` at the unique place `P₀` over `∞`: `t³ + t = ℘(W) = W⁵ - W`, and
  `ord_∞(t³ + t) = -3` is not divisible by `5`, so `∞` is totally ramified (`e = 5`, since
  `ord_{P₀}(W) = -3e/5` must be an integer), whence `ord_{P₀}(t) = 5·(-1) = -5` and
  `ord_{P₀}(W) = -3`.  Consequently the pole fibre of `t` in `L = asFieldL = L₀(E)` is
  `5 × (a divisor)`, and descending to `F` along the quotient by `⟨σ'⟩` (the pole fibre is
  `σ'`-stable) gives `ord_P(t) ∈ 5ℤ`.  In particular the **necessary condition** of
  `exists_fifth_pow_of_bridge` below — that `v g` be a fifth power of the value group — is
  automatic, since `v g = v (t³ + t) = (v t)³` whenever `1 < v t`.

  *(An earlier revision of this file carried the claim `e(v̂/v) ∈ {1,5}` with both cases possible
  and declared the polar-part question open.  That rested on the normalization `ord_{P₀}(W) = -3`
  combined with the pole place of `t` read off in `F` instead of in `L₀`; with the correct
  coordinate, `𝕜(W)/𝕜(t)` is totally ramified over `∞` and `5 ∣ ord_P(t)` at every pole of `t`.)*

* **The bridge is the polar-part descent.**  With `W = asRoot g` one has
  `g - ℘(u) = ℘(W) - ℘(u) = ℘(W - u)` for every `u ∈ F`, so the bridge at `v` says exactly that
  some `F`-translate of `W` is integral at `v`; the formal implication is
  `bridge_of_mem_add_integer` below.

* **The descent itself** is `Work.MotV5.exists_polarApprox_of_unramified`: it needs an extension `V`
  of `v` to `L` with the same valuation ring, `σ'`-stable, of ramification index `1`
  (`V (L^×) = v (F^×)`) and with `σ'`-fixed residue classes coming from `F`; then it produces
  `u ∈ F` with `V (ι u - W) ≤ 1`.

* **The local hypotheses** are exactly `∃ V, IsPlaceData D g τ σS σ h v V`, see
  `Submission/Work/MotV5/RigAS/PlaceData.lean` for the definitions and for the roadmap of its two
  halves `IsPlaceExtension` and `IsResidueLift`.  Their geometric content: the pole place in `L` is
  the unique place above the pole of `t` (so it is `σ'`-stable and `e·f = 5`), its residue field is
  `K(E) = kleinField D`, on which `σ'` acts through the nontrivial fifth-torsion shift `σS` (so the
  inertia is trivial: `e = 1`, `f = 5`), and the `σS`-fixed part of `kleinField D` lies in `F`
  (`Work.MotV5.RigAS.kleinField_le_twistFieldTrue`).
-/

/-- **The `℘`-value bound.**  For a field of characteristic `5` and a valuation `v` with values in
a multiplicative ordered group with zero,

  `v (u⁵ - u) ≤ max ((v u)⁵) (v u)`,

because `u⁵ - u = u (u⁴ - 1)` and `v (u⁴ - 1) ≤ max ((v u)⁴) 1`. -/
theorem v_pow_five_sub_self_le {F Γ₀ : Type*} [Field F] [CharP F 5]
    [LinearOrderedCommGroupWithZero Γ₀] (v : Valuation F Γ₀) (u : F) :
    v (u ^ 5 - u) ≤ max (v u ^ 5) (v u) := by
  rcases eq_or_ne u 0 with rfl | hu
  · simp only [zero_pow (by norm_num : (5 : ℕ) ≠ 0), sub_zero, map_zero]
    exact zero_le
  · have h1 : u ^ 5 - u = u * (u ^ 4 - 1) := by ring
    have h2 : v (u ^ 4 - 1) ≤ max (v u ^ 4) 1 := by
      have h := Valuation.map_sub_le (v := v) (x := u ^ 4) (y := 1)
        (g := max (v u ^ 4) 1)
        (by rw [Valuation.map_pow]; exact le_max_left _ _)
        (by rw [map_one]; exact le_max_right _ _)
      exact h
    calc v (u ^ 5 - u) = v u * v (u ^ 4 - 1) := by rw [h1, Valuation.map_mul]
      _ ≤ v u * max (v u ^ 4) 1 := by gcongr
      _ = max (v u * v u ^ 4) (v u * 1) := mul_max _ _ _
      _ = max (v u ^ 5) (v u) := by
          rw [mul_one]
          congr 1
          exact (pow_succ' (v u) 4).symm

/-- **Small perturbations preserve the Artin–Schreier condition.**  If `v u ≤ 1` (the element `u`
has no pole at `v`), then `v (u⁵ - u) ≤ 1` as well.  This is the step that lets one replace an
approximating element `u₀ ∈ F_v` in the proof of `bridge_twist` by an element `u ∈ F` with
`v (u - u₀) ≤ 1`: the difference of the two `℘`-values is `℘ (u - u₀)`, whose value is `≤ 1`. -/
theorem v_pow_five_sub_self_le_one {F Γ₀ : Type*} [Field F] [CharP F 5]
    [LinearOrderedCommGroupWithZero Γ₀] (v : Valuation F Γ₀) (u : F) (hu : v u ≤ 1) :
    v (u ^ 5 - u) ≤ 1 := by
  refine le_trans (v_pow_five_sub_self_le v u) (max_le_iff.mpr ⟨?_, hu⟩)
  exact pow_le_one₀ zero_le hu

/-- **The `℘`-value of a pole is a fifth power.**  If `1 < v u` (so `u` has a pole at `v`), then
`v (u⁵ - u) = (v u)⁵`: the second term is dominated and `u⁵ - u = u (u⁴ - 1)` with
`v (u⁴ - 1) = v (u⁴) = (v u)⁴`. -/
theorem v_pow_five_sub_self_of_one_lt {F Γ₀ : Type*} [Field F] [CharP F 5]
    [LinearOrderedCommGroupWithZero Γ₀] (v : Valuation F Γ₀) {u : F} (hu : 1 < v u) :
    v (u ^ 5 - u) = v u ^ 5 := by
  have h4 : v (u ^ 4 - 1) = v u ^ 4 := by
    have h := Valuation.map_sub_eq_of_lt_left (v := v) (x := u ^ 4) (y := 1) ?_
    · rw [Valuation.map_pow] at h; exact h
    · rw [map_one, Valuation.map_pow]; exact one_lt_pow₀ hu (by norm_num)
  calc v (u ^ 5 - u) = v u * v (u ^ 4 - 1) := by
        rw [show u ^ 5 - u = u * (u ^ 4 - 1) by ring, Valuation.map_mul]
    _ = v u * v u ^ 4 := by rw [h4]
    _ = v u ^ 5 := by rw [← pow_succ']

/-- **The necessary condition at a pole.**  If `1 < v g` and some `u` satisfies
`v (g - (u⁵ - u)) ≤ 1` (the bridge condition at `v`), then `v g` is a **fifth power** in the value
group.  Indeed the pole orders of `g` and of `u⁵ - u` must then coincide, and a pole order of
`u⁵ - u` is of the form `(v u)⁵`.

Consequently the bridge condition at a valuation `v` can only hold if `v g` is a fifth power —
which for the twist field is automatic: `v g = v t³ = (v ζ)^{-15}` is the fifth power of
`(v ζ)^{-3}`, cf. the module documentation. -/
theorem exists_fifth_pow_of_bridge {F Γ₀ : Type*} [Field F] [CharP F 5]
    [LinearOrderedCommGroupWithZero Γ₀] (v : Valuation F Γ₀) {g u : F}
    (hg : 1 < v g) (h : v (g - (u ^ 5 - u)) ≤ 1) : ∃ w : Γ₀, v g = w ^ 5 := by
  have hvu : v (u ^ 5 - u) = v g := by
    rcases lt_trichotomy (v (u ^ 5 - u)) (v g) with hlt | heq | hgt
    · rw [Valuation.map_sub_eq_of_lt_left (v := v) hlt] at h
      exact absurd h (not_le_of_gt hg)
    · exact heq
    · rw [Valuation.map_sub_eq_of_lt_right (v := v) hgt] at h
      exact absurd (lt_of_lt_of_le hgt h) (not_lt_of_gt hg)
  have hu : 1 < v u := by
    by_contra hcon
    have h1 := v_pow_five_sub_self_le_one v u (le_of_not_gt hcon)
    rw [hvu] at h1
    exact absurd h1 (not_le_of_gt hg)
  exact ⟨v u, by rw [← hvu, v_pow_five_sub_self_of_one_lt v hu]⟩

/-- **The Artin–Schreier bridge is trivially true for the ambient field `L(E) = asFieldL D g`**:
the root `W = asRoot g` lies in `asFieldL D g` and satisfies `W⁵ - W = g` exactly, so the
remainder is `0`.  Consequently `ASUnramified` holds for `asFieldL D g` with the witness
`u = W`.

This is the companion of `Work.MotV5.bridge_as` (which is the same statement for the refuted
interpolation model `asTwistField`) for the *correct* ambient field, and it shows that the
content of `bridge_twist` is precisely the failure of `asRoot g` to lie in the corrected twist
field (`Work.MotV5.asRoot_notMem_asTwistFieldTrue`). -/
theorem bridge_asFieldL (𝕜 : Type) [Field 𝕜] (D : Work.MotV.KleinData 𝕜) (g : RatFunc 𝕜) :
    ASUnramified 𝕜 ↥(asFieldL D g)
      (algebraMap (RatFunc 𝕜) ↥(asFieldL D g) RatFunc.X)
      (algebraMap (RatFunc 𝕜) ↥(asFieldL D g) g) := by
  intro v _ _
  -- the root `W = asRoot g`, viewed as an element of `asFieldL D g`
  have hW : algebraMap (Work.MotV.Kb 𝕜) (Work.MotV.Om D) (asRoot g) ∈ asFieldL D g := by
    have hgen : asFieldL D g = IntermediateField.adjoin (RatFunc 𝕜)
        (Set.range (fun i : Fin 5 => Work.MotV.kleinCoord D (Work.MotV.Kb 𝕜) i
            / Work.MotV.kleinCoord D (Work.MotV.Kb 𝕜) 0)
          ∪ ({algebraMap (Work.MotV.Kb 𝕜) (Work.MotV.Om D) (asRoot g)} :
              Set (Work.MotV.Om D))) := by
      unfold asFieldL kleinField
      rw [IntermediateField.adjoin_union]
    rw [hgen]
    exact IntermediateField.subset_adjoin _ _ (Set.mem_union_right _ (Set.mem_singleton _))
  refine ⟨⟨algebraMap (Work.MotV.Kb 𝕜) (Work.MotV.Om D) (asRoot g), hW⟩, ?_⟩
  -- `℘(W) = g`, so the difference is `0` and its valuation is `0 ≤ 1`
  have hrel : (algebraMap (Work.MotV.Kb 𝕜) (Work.MotV.Om D) (asRoot g) : Work.MotV.Om D) ^ 5
      - algebraMap (Work.MotV.Kb 𝕜) (Work.MotV.Om D) (asRoot g)
      = algebraMap (RatFunc 𝕜) (Work.MotV.Om D) g := by
    have h1 : algebraMap (Work.MotV.Kb 𝕜) (Work.MotV.Om D) (asRoot g) ^ 5
        - algebraMap (Work.MotV.Kb 𝕜) (Work.MotV.Om D) (asRoot g)
        = algebraMap (Work.MotV.Kb 𝕜) (Work.MotV.Om D) (asRoot g ^ 5 - asRoot g) := by
      rw [map_sub, map_pow]
    rw [h1, asRoot_spec]
    exact (IsScalarTower.algebraMap_apply (RatFunc 𝕜) (Work.MotV.Kb 𝕜) (Work.MotV.Om D) g).symm
  have hcoe : (algebraMap (RatFunc 𝕜) ↥(asFieldL D g) g
        - ((⟨algebraMap (Work.MotV.Kb 𝕜) (Work.MotV.Om D) (asRoot g), hW⟩ : ↥(asFieldL D g)) ^ 5
          - ⟨algebraMap (Work.MotV.Kb 𝕜) (Work.MotV.Om D) (asRoot g), hW⟩)) = 0 := by
    apply Subtype.ext
    show algebraMap (RatFunc 𝕜) (Work.MotV.Om D) g
      - ((algebraMap (Work.MotV.Kb 𝕜) (Work.MotV.Om D) (asRoot g)) ^ 5
        - algebraMap (Work.MotV.Kb 𝕜) (Work.MotV.Om D) (asRoot g)) = (0 : Work.MotV.Om D)
    rw [← hrel]
    abel
  rw [hcoe, map_zero]
  exact zero_le_one' _

/-- **The bridge condition from the `F`-rationality of the polar part of `W`.**  If `W` is a
`℘`-preimage of `g` in an extension `L` of `F` and `u ∈ F` satisfies `V (ι u - W) ≤ 1` for a
valuation `V` on `L` whose valuation ring contracts to that of `v`, then `v (g - ℘ u) ≤ 1`.

This is the interface between the "the polar part of `W` at `v` lies in `F`" statement of the
module documentation (the crux of the bridge) and the target `bridge_twist`: indeed
`℘(u) - g = ℘(u - W)` and `V (u - W) ≤ 1 → V (℘(u - W)) ≤ 1`
(`v_pow_five_sub_self_le_one`). -/
theorem bridge_of_mem_add_integer {F L Γ₀ Γ₁ : Type*} [Field F] [Field L] [Algebra F L]
    [CharP F 5] [LinearOrderedCommGroupWithZero Γ₀] [LinearOrderedCommGroupWithZero Γ₁]
    (v : Valuation F Γ₀) (V : Valuation L Γ₁) {g : F} {W : L} {u : F}
    (hW : W ^ 5 - W = algebraMap F L g)
    (hu : V (algebraMap F L u - W) ≤ 1)
    (hcompat : ∀ x : F, V (algebraMap F L x) ≤ 1 ↔ v x ≤ 1) :
    v (g - (u ^ 5 - u)) ≤ 1 := by
  haveI : CharP L 5 := charP_of_injective_algebraMap (RingHom.injective (algebraMap F L)) 5
  haveI : Fact (Nat.Prime 5) := ⟨by norm_num⟩
  have h1 : V (algebraMap F L (u ^ 5 - u - g)) ≤ 1 := by
    have h2 := v_pow_five_sub_self_le_one V (algebraMap F L u - W) hu
    have h3 : ((algebraMap F L u - W) ^ 5 - (algebraMap F L u - W))
        = algebraMap F L (u ^ 5 - u - g) := by
      have e1 : (algebraMap F L u - W) ^ 5 = (algebraMap F L u) ^ 5 - W ^ 5 :=
        sub_pow_char (p := 5) _ _
      have e2 : algebraMap F L (u ^ 5 - u - g)
          = ((algebraMap F L u) ^ 5 - algebraMap F L u) - (W ^ 5 - W) := by
        rw [map_sub, map_sub, map_pow, hW]
      rw [e1, e2]
      first | refl_ring1 | ring
    rw [h3] at h2
    exact h2
  have h4 : v (u ^ 5 - u - g) ≤ 1 := (hcompat _).mp h1
  have h5 : g - (u ^ 5 - u) = -(u ^ 5 - u - g) := by ring
  rw [h5, Valuation.map_neg]
  exact h4

/-! ## The values above `1` of `ℤᵐ⁰` are well-founded

`exists_polarApprox_of_unramified` needs the well-foundedness of `{a : Γ₁ | 1 < a}` under `<`.
For `Γ₁ = ℤᵐ⁰` this is the discreteness of `ℤ` (`ℤᵐ⁰ = WithZero (Multiplicative ℤ)`): the elements
`> 1` are the `exp n` with `n > 0`, and `exp` is strictly monotone, so `a ↦ (log a).toNat` is a
measure with values in `ℕ`. -/

/-- **The values strictly above `1` of `ℤᵐ⁰` are well-founded** (no infinite strictly descending
chains of elements `> 1`). -/
theorem wellFounded_zhat_one_lt : WellFounded (fun a b : ℤᵐ⁰ => 1 < a ∧ a < b) := by
  refine (InvImage.wf (fun a : ℤᵐ⁰ => (WithZero.log a).toNat) Nat.lt_wfRel.wf).mono ?_
  rintro a b ⟨ha, hlt⟩
  rw [InvImage]
  -- `1 < a` and `a < b` say `0 < log a < log b`; monotonicity of `Int.toNat` on `ℕ` concludes.
  have hane : a ≠ 0 := fun h => by rw [h] at ha; exact absurd ha (by simp)
  have hbne : b ≠ 0 := fun h => by
    rw [h] at hlt
    exact absurd hlt (by simp)
  have hla : 0 < WithZero.log a := by
    have h1 : 1 < WithZero.exp (WithZero.log a) := by rwa [WithZero.exp_log hane]
    rwa [WithZero.one_lt_exp_iff] at h1
  have hlb : 0 < WithZero.log b := by
    have h1 : 1 < WithZero.exp (WithZero.log b) := by
      rw [WithZero.exp_log hbne]; exact lt_trans ha hlt
    rwa [WithZero.one_lt_exp_iff] at h1
  have hlt' : WithZero.log a < WithZero.log b := by
    have h1 : WithZero.exp (WithZero.log a) < WithZero.exp (WithZero.log b) := by
      rw [WithZero.exp_log hane, WithZero.exp_log hbne]; exact hlt
    rwa [WithZero.exp_lt_exp] at h1
  exact (Int.toNat_lt_toNat hlb).mpr hlt'

/-! ## The assembly -/

/-- **The AS bridge from the local place datum.**

`IsPlaceData D g τ σS σ h v V` supplies a `ℤᵐ⁰`-valued place `V` of `L(E) = asFieldL D g` above
`v`, extending `v`, stable under `σ'`, with trivial ramification and trivial inertia.  These are
exactly the hypotheses of the polar-part descent `Work.MotV5.exists_polarApprox_of_unramified`,
applied to `W = asRoot g` (whose `℘`-value is `g`) and to the twisted action restricted to `L(E)`.

Consequently `bridge_twist` reduces to the existence of such a `V` for every `v`, and the whole
geometric content of the bridge is concentrated in the construction of `V`. -/
theorem bridge_twist_of_placeData (𝕜 : Type) [Field 𝕜] [CharP 𝕜 5] (D : Work.MotV.KleinData 𝕜)
    (hD : Work.MotV5.KleinData.ASGood D) (g : RatFunc 𝕜)
    (hg : g = Work.MotV.fAS 𝕜 ∨ g = 2 • Work.MotV.fAS 𝕜)
    (τ : Work.MotV.Om D ≃ₐ[RatFunc 𝕜] Work.MotV.Om D)
    (σS : Work.MotV.Om D ≃ₐ[Work.MotV.Kb 𝕜] Work.MotV.Om D)
    (σ : Work.MotV.Kb 𝕜 ≃ₐ[RatFunc 𝕜] Work.MotV.Kb 𝕜)
    (h : Work.MotV5.ASTwistData 𝕜 D g τ σS σ)
    (hP : ∀ v : Valuation ↥(Work.MotV5.asTwistFieldTrue D g τ σS) ℤᵐ⁰,
      Work.MotV.TrivOn 𝕜 v →
      1 < v (algebraMap (RatFunc 𝕜) ↥(Work.MotV5.asTwistFieldTrue D g τ σS) RatFunc.X) →
      ∃ V : Valuation ↥(Work.MotV5.asFieldL D g) ℤᵐ⁰,
        IsPlaceData D g τ σS σ h v V) :
    Work.MotV5.ASUnramified 𝕜 ↥(Work.MotV5.asTwistFieldTrue D g τ σS)
      (algebraMap (RatFunc 𝕜) ↥(Work.MotV5.asTwistFieldTrue D g τ σS) RatFunc.X)
      (algebraMap (RatFunc 𝕜) ↥(Work.MotV5.asTwistFieldTrue D g τ σS) g) := by
  intro v htriv ht
  obtain ⟨V, hP⟩ := hP v htriv ht
  have hPE : IsPlaceExtension D g τ σS σ h v V := hP.1
  have hVres : IsResidueLift D g τ σS σ h v V := hP.2
  obtain ⟨hVext, hVΓ⟩ := hPE
  -- the inclusion `F → L` as a ring homomorphism, and the induced `Algebra` structure
  let incl : ↥(Work.MotV5.asTwistFieldTrue D g τ σS) →+* ↥(Work.MotV5.asFieldL D g) :=
    { toFun := twistIncl D g τ σS
      map_one' := Subtype.ext rfl
      map_mul' := fun x y => Subtype.ext rfl
      map_zero' := Subtype.ext rfl
      map_add' := fun x y => Subtype.ext rfl }
  letI : Algebra ↥(Work.MotV5.asTwistFieldTrue D g τ σS) ↥(Work.MotV5.asFieldL D g) :=
    incl.toAlgebra
  have halg : ∀ x : ↥(Work.MotV5.asTwistFieldTrue D g τ σS),
      algebraMap ↥(Work.MotV5.asTwistFieldTrue D g τ σS) ↥(Work.MotV5.asFieldL D g) x
        = twistIncl D g τ σS x := fun _ => rfl
  -- the Artin–Schreier root `W`, as an element of `L(E)`
  have hw : algebraMap (Work.MotV.Kb 𝕜) (Work.MotV.Om D) (asRoot g) ∈ Work.MotV5.asFieldL D g := by
    show _ ∈ Work.MotV5.kleinField D ⊔ _
    exact (le_sup_right : _ ≤ Work.MotV5.kleinField D ⊔ _)
      (IntermediateField.subset_adjoin _ _ (Set.mem_singleton _))
  set W : ↥(Work.MotV5.asFieldL D g) :=
    ⟨algebraMap (Work.MotV.Kb 𝕜) (Work.MotV.Om D) (asRoot g), hw⟩ with hWdef
  -- `℘(W) = g` in `L(E)`
  have hW : W ^ 5 - W = algebraMap ↥(Work.MotV5.asTwistFieldTrue D g τ σS)
      ↥(Work.MotV5.asFieldL D g)
      (algebraMap (RatFunc 𝕜) ↥(Work.MotV5.asTwistFieldTrue D g τ σS) g) := by
    apply Subtype.ext
    show ((W : ↥(Work.MotV5.asFieldL D g)) : Work.MotV.Om D) ^ 5
        - ((W : ↥(Work.MotV5.asFieldL D g)) : Work.MotV.Om D)
      = algebraMap (RatFunc 𝕜) (Work.MotV.Om D) g
    rw [hWdef]
    have h1 : algebraMap (Work.MotV.Kb 𝕜) (Work.MotV.Om D) (asRoot g) ^ 5
        - algebraMap (Work.MotV.Kb 𝕜) (Work.MotV.Om D) (asRoot g)
        = algebraMap (Work.MotV.Kb 𝕜) (Work.MotV.Om D) (asRoot g ^ 5 - asRoot g) := by
      rw [map_sub, map_pow]
    rw [h1, asRoot_spec]
    exact (IsScalarTower.algebraMap_apply (RatFunc 𝕜) (Work.MotV.Kb 𝕜) (Work.MotV.Om D) g).symm
  -- the twisted action shifts `W` by `1`
  have hσW : twistSigmaL D g τ σS σ h W = W + 1 := by
    apply Subtype.ext
    rw [twistSigmaL_coe, hWdef]
    show asTwistAction D τ σS (algebraMap (Work.MotV.Kb 𝕜) (Work.MotV.Om D) (asRoot g))
      = algebraMap (Work.MotV.Kb 𝕜) (Work.MotV.Om D) (asRoot g) + 1
    rw [Work.MotV5.asTwistAction, AlgEquiv.trans_apply, AlgEquiv.restrictScalars_apply]
    rw [h.hτ, AlgEquiv.commutes, h.hσ, map_add, map_one]
  -- the twisted action fixes `F`
  have hσF : ∀ x : ↥(Work.MotV5.asTwistFieldTrue D g τ σS),
      twistSigmaL D g τ σS σ h
        (algebraMap ↥(Work.MotV5.asTwistFieldTrue D g τ σS) ↥(Work.MotV5.asFieldL D g) x)
        = algebraMap ↥(Work.MotV5.asTwistFieldTrue D g τ σS) ↥(Work.MotV5.asFieldL D g) x := by
    intro x
    apply Subtype.ext
    rw [twistSigmaL_coe, halg]
    show asTwistAction D τ σS
        ((twistIncl D g τ σS x : ↥(Work.MotV5.asFieldL D g)) : Work.MotV.Om D)
      = ((twistIncl D g τ σS x : ↥(Work.MotV5.asFieldL D g)) : Work.MotV.Om D)
    rw [twistIncl_coe]
    have hx : (x : Work.MotV.Om D) ∈ Work.MotV5.asTwistFieldFix D τ σS :=
      Work.MotV5.asTwistFieldTrue_le_asTwistFieldFix D g τ σS x.2
    rw [Work.MotV5.asTwistFieldFix, IntermediateField.mem_fixedField_iff] at hx
    have h2 : asTwistAction D τ σS • (x : Work.MotV.Om D) = (x : Work.MotV.Om D) :=
      hx (asTwistAction D τ σS) (Subgroup.mem_zpowers _)
    rwa [AlgEquiv.smul_def] at h2
  -- the descent hypotheses
  have hfv : ∀ x : ↥(Work.MotV5.asTwistFieldTrue D g τ σS),
      V (algebraMap ↥(Work.MotV5.asTwistFieldTrue D g τ σS) ↥(Work.MotV5.asFieldL D g) x) ≤ 1
        ↔ v x ≤ 1 := by
    intro x
    rw [halg, hVext x]
  have hΓ : ∀ x : ↥(Work.MotV5.asFieldL D g), x ≠ 0 →
      ∃ y : ↥(Work.MotV5.asTwistFieldTrue D g τ σS), y ≠ 0 ∧
        V (algebraMap ↥(Work.MotV5.asTwistFieldTrue D g τ σS) ↥(Work.MotV5.asFieldL D g) y)
          = V x := by
    intro x hx
    obtain ⟨y, hy, hyV⟩ := hVΓ x hx
    exact ⟨y, hy, by rw [halg]; exact hyV⟩
  have hres : ∀ x : ↥(Work.MotV5.asFieldL D g), V x ≤ 1 →
      V (twistSigmaL D g τ σS σ h x - x) < 1 →
      ∃ y : ↥(Work.MotV5.asTwistFieldTrue D g τ σS),
        V (algebraMap ↥(Work.MotV5.asTwistFieldTrue D g τ σS) ↥(Work.MotV5.asFieldL D g) y
          - x) < 1 := by
    intro x hx1 hx2
    obtain ⟨y, hy⟩ := hVres x hx1 hx2
    exact ⟨y, by rw [halg]; exact hy⟩
  haveI : CharP ↥(Work.MotV5.asTwistFieldTrue D g τ σS) 5 :=
    charP_of_injective_algebraMap
      (algebraMap (RatFunc 𝕜) ↥(Work.MotV5.asTwistFieldTrue D g τ σS)).injective 5
  obtain ⟨u, hu⟩ := exists_polarApprox_of_unramified' v V (twistSigmaL D g τ σS σ h)
    hW hσW hσF hfv hΓ wellFounded_zhat_one_lt hres
  exact ⟨u, bridge_of_mem_add_integer v V hW hu hfv⟩

theorem bridge_twist (𝕜 : Type) [Field 𝕜] [CharP 𝕜 5] (D : Work.MotV.KleinData 𝕜)
    (hD : Work.MotV5.KleinData.ASGood D) (g : RatFunc 𝕜)
    (hg : g = Work.MotV.fAS 𝕜 ∨ g = 2 • Work.MotV.fAS 𝕜)
    (τ : Work.MotV.Om D ≃ₐ[RatFunc 𝕜] Work.MotV.Om D)
    (σS : Work.MotV.Om D ≃ₐ[Work.MotV.Kb 𝕜] Work.MotV.Om D)
    (σ : Work.MotV.Kb 𝕜 ≃ₐ[RatFunc 𝕜] Work.MotV.Kb 𝕜)
    (h : Work.MotV5.ASTwistData 𝕜 D g τ σS σ) :
    Work.MotV5.ASUnramified 𝕜 ↥(Work.MotV5.asTwistFieldTrue D g τ σS)
      (algebraMap (RatFunc 𝕜) ↥(Work.MotV5.asTwistFieldTrue D g τ σS) RatFunc.X)
      (algebraMap (RatFunc 𝕜) ↥(Work.MotV5.asTwistFieldTrue D g τ σS) g) :=
  -- The local place datum at every pole of `t` (`placeData_e1`) plus the polar-part descent
  -- (`bridge_twist_of_placeData`, proved above in this file).
  bridge_twist_of_placeData 𝕜 D hD g hg τ σS σ h (placeData_e1 𝕜 D hD g hg τ σS σ h)

end Work.MotV5.RigAS
