import Mathlib
import Submission.Work.MotV.Defs
import Submission.Work.MotV.hurwitz_five

set_option linter.unusedVariables false -- v435-speed

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.MotV

open WeierstrassCurve WeierstrassCurve.Affine
open scoped WithZero

namespace Work.MotV

/-- Helper for `base_preserved`: an `𝕜`-algebra hom out of `𝕜(X)` whose value at the generator
`X` lies in the image of `algebraMap (RatFunc 𝕜) F` has all of its image there. -/
lemma exists_algebraMap_of_X_mem {𝕜 F : Type*} [Field 𝕜] [Field F] [Algebra 𝕜 F]
    [Algebra (RatFunc 𝕜) F] [IsScalarTower 𝕜 (RatFunc 𝕜) F]
    (φ : RatFunc 𝕜 →ₐ[𝕜] F)
    (hX : ∃ d : RatFunc 𝕜, algebraMap (RatFunc 𝕜) F d = φ RatFunc.X) :
    ∀ c : RatFunc 𝕜, ∃ d : RatFunc 𝕜, φ c = algebraMap (RatFunc 𝕜) F d := by
  intro c
  let β : RatFunc 𝕜 →ₐ[𝕜] F := IsScalarTower.toAlgHom 𝕜 (RatFunc 𝕜) F
  let L : IntermediateField 𝕜 (RatFunc 𝕜) := β.fieldRange.comap φ
  have hm : ∀ x : RatFunc 𝕜, x ∈ L ↔ φ x ∈ β.fieldRange := fun x => Iff.rfl
  have hXL : RatFunc.X ∈ L := by
    obtain ⟨d, hd⟩ := hX
    exact (hm _).mpr (AlgHom.mem_fieldRange.mpr ⟨d, hd⟩)
  have htop : (⊤ : IntermediateField 𝕜 (RatFunc 𝕜)) ≤ L := by
    rw [← RatFunc.adjoin_X]
    rw [IntermediateField.adjoin_le_iff]
    intro x hx
    rw [Set.mem_singleton_iff] at hx
    subst hx
    exact hXL
  have hc : c ∈ L := htop IntermediateField.mem_top
  obtain ⟨d, hd⟩ := AlgHom.mem_fieldRange.mp ((hm c).mp hc)
  exact ⟨d, hd.symm⟩

/-- Node V1: a `𝕜`-algebra isomorphism `θ : F₁ ≃ₐ[𝕜] F₂` of the two twist fields, *realized* as
subfields of the function field of an elliptic curve `E/N` with `N` algebraically closed of
characteristic `≠ 5` and algebraic over `K = RatFunc 𝕜`, preserves the base `K`: it maps
`algebraMap c` to `algebraMap d` for a suitable `d`.  (`hR₁`, `hR₂` say that `K` is algebraically
closed in `F₁`, `F₂`; `hB₁`, `hB₂` say `hT = t(t-1)` is fifth-power valued in `F₁`, `F₂`.)

Route.  Node H1 (`Work.MotV.hurwitz_five`, in `Submission/Work/MotV/hurwitz_five.lean`; the file
also declares it as `Work.MotV.Work.MotV.hurwitz_five` because of a nested namespace, so check
which name is in scope) is the only mathematical input.
Let `s := θ (algebraMap (RatFunc 𝕜) F₁ (RatFunc.X))` and `r := ι₂ s ∈ FunctionField E`.
1. **`r(r-1)` is fifth-power valued.**  For `v : Valuation (FunctionField E) ℤᵐ⁰` with `TrivOn N v`,
   the composite `w := v ∘ ι₂ ∘ θ` is a valuation of `F₁` trivial on `𝕜` (`hι₂` identifies the
   scalars), and `hB₁` gives `∃ u : F₁, w (algebraMap (RatFunc 𝕜) F₁ (hT 𝕜)) = w u ^ 5`.  Now
   `w (algebraMap (t(t-1))) = w (algebraMap t) * w (algebraMap t - 1) = v r * v (r - 1)`, i.e.
   `v (r * (r - 1)) = w u ^ 5 = (v (ι₂ (θ u)))^5`.  So node H1 applies (with the same `N`).
2. **`s` is algebraic over `K`.**  H1 gives `ι₂ s = algebraMap N _ c` for some `c`; since `ι₂` is
   `K`-linear (`hι₂`) and injective (a nonzero ring hom between fields; `ι₂ ≠ 0` because `hι₂`
   applied to `1` gives `ι₂ 1 = 1`), and every element of `N` is algebraic over `K`
   (`Algebra.IsAlgebraic (RatFunc 𝕜) N`), `s` is algebraic over `K`.
3. **`s ∈ K`.**  `hR₂` applied to `s` gives `s = algebraMap (RatFunc 𝕜) F₂ d`.
4. **General `c`.**  Write `c = p(X)/q(X)` with `p, q ∈ 𝕜[X]`, `q ≠ 0`; then
   `θ (algebraMap c) = p(s) / q(s)` because `θ` is a `𝕜`-algebra homomorphism, and `q(s) ≠ 0`
   since `θ` is injective and `algebraMap q ≠ 0`.  As `s ∈ K`, `p(s)/q(s) ∈ K`, i.e.
   `θ (algebraMap c) = algebraMap d` for some `d : K`. -/
theorem base_preserved {𝕜 F₁ F₂ N : Type*} [Field 𝕜] [Field F₁] [Field F₂] [Field N]
    [IsAlgClosed N] (hN : ringChar N ≠ 5)
    [Algebra 𝕜 F₁] [Algebra 𝕜 F₂] [Algebra (RatFunc 𝕜) F₁] [Algebra (RatFunc 𝕜) F₂]
    [IsScalarTower 𝕜 (RatFunc 𝕜) F₁] [IsScalarTower 𝕜 (RatFunc 𝕜) F₂]
    [Algebra (RatFunc 𝕜) N] [Algebra.IsAlgebraic (RatFunc 𝕜) N]
    (E : WeierstrassCurve N) [E.IsElliptic]
    (ι₁ : F₁ →+* Affine.FunctionField E) (ι₂ : F₂ →+* Affine.FunctionField E)
    (hι₁ : ∀ c : RatFunc 𝕜, ι₁ (algebraMap _ F₁ c) = algebraMap N _ (algebraMap _ N c))
    (hι₂ : ∀ c : RatFunc 𝕜, ι₂ (algebraMap _ F₂ c) = algebraMap N _ (algebraMap _ N c))
    (hB₁ : FifthPowerValued 𝕜 (algebraMap (RatFunc 𝕜) F₁ (hT 𝕜)))
    (hB₂ : FifthPowerValued 𝕜 (algebraMap (RatFunc 𝕜) F₂ (hT 𝕜)))
    (hR₁ : ∀ r : F₁, IsAlgebraic (RatFunc 𝕜) r → ∃ c, algebraMap (RatFunc 𝕜) F₁ c = r)
    (hR₂ : ∀ r : F₂, IsAlgebraic (RatFunc 𝕜) r → ∃ c, algebraMap (RatFunc 𝕜) F₂ c = r)
    (θ : F₁ ≃ₐ[𝕜] F₂) :
    ∀ c : RatFunc 𝕜, ∃ d, θ (algebraMap (RatFunc 𝕜) F₁ c) = algebraMap (RatFunc 𝕜) F₂ d := by
  intro c
  set s : F₂ := θ (algebraMap (RatFunc 𝕜) F₁ RatFunc.X) with hs
  -- Step 1: `ι₂ s · (ι₂ s - 1)` is fifth-power valued over `N`
  have hmain : FifthPowerValued N (ι₂ s * (ι₂ s - 1)) := by
    intro v hv
    let f : F₁ →+* Affine.FunctionField E := ι₂.comp θ.toRingHom
    let w : Valuation F₁ ℤᵐ⁰ := Valuation.comap f v
    have hw : TrivOn 𝕜 w := by
      intro a ha
      have h1 : f (algebraMap 𝕜 F₁ a)
          = algebraMap N (Affine.FunctionField E)
              (algebraMap (RatFunc 𝕜) N (algebraMap 𝕜 (RatFunc 𝕜) a)) := by
        show ι₂ (θ (algebraMap 𝕜 F₁ a)) = _
        rw [θ.commutes a, IsScalarTower.algebraMap_apply 𝕜 (RatFunc 𝕜) F₂ a,
          hι₂ (algebraMap 𝕜 (RatFunc 𝕜) a)]
      rw [Valuation.comap_apply, h1]
      have hK : algebraMap 𝕜 (RatFunc 𝕜) a ≠ 0 := by
        simpa using (FaithfulSMul.algebraMap_injective 𝕜 (RatFunc 𝕜)).ne ha
      exact hv _ (by simpa using (FaithfulSMul.algebraMap_injective (RatFunc 𝕜) N).ne hK)
    obtain ⟨u, hu⟩ := hB₁ w hw
    have key : f (algebraMap (RatFunc 𝕜) F₁ (hT 𝕜)) = ι₂ s * (ι₂ s - 1) := by
      have hA : algebraMap (RatFunc 𝕜) F₁ (hT 𝕜) =
          algebraMap (RatFunc 𝕜) F₁ RatFunc.X *
            (algebraMap (RatFunc 𝕜) F₁ RatFunc.X - 1) := by
        simp [hT]
      rw [hA]
      show ι₂ (θ (algebraMap (RatFunc 𝕜) F₁ RatFunc.X *
        (algebraMap (RatFunc 𝕜) F₁ RatFunc.X - 1))) = ι₂ s * (ι₂ s - 1)
      rw [map_mul, map_sub, map_one, map_mul, map_sub, map_one, hs.symm]
    have hkey : w (algebraMap (RatFunc 𝕜) F₁ (hT 𝕜)) = v (ι₂ s * (ι₂ s - 1)) := by
      rw [Valuation.comap_apply, key]
    refine ⟨f u, ?_⟩
    rw [← hkey, hu, Valuation.comap_apply]
  -- Step 2: node H1 makes `ι₂ s` constant, hence `s` is algebraic over `K`
  obtain ⟨c₀, hc₀⟩ := hurwitz_five hN E (ι₂ s) hmain
  have hs_alg : IsAlgebraic (RatFunc 𝕜) s := by
    let ι₂' : F₂ →ₐ[RatFunc 𝕜] Affine.FunctionField E :=
      { toRingHom := ι₂, commutes' := fun k => hι₂ k }
    have hinj : Function.Injective ι₂' := by
      intro x y hxy
      exact RingHom.injective ι₂ hxy
    have h1 : IsAlgebraic (RatFunc 𝕜) (algebraMap N (Affine.FunctionField E) c₀) :=
      IsAlgebraic.ringHom_of_comp_eq (f := RingHom.id (RatFunc 𝕜))
        (g := algebraMap N (Affine.FunctionField E)) (Algebra.IsAlgebraic.isAlgebraic c₀)
        (fun _ _ h => h)
        (by ext x; exact IsScalarTower.algebraMap_apply (RatFunc 𝕜) N (Affine.FunctionField E) x)
    refine (isAlgebraic_algHom_iff ι₂' hinj).mp ?_
    rw [show ι₂' s = algebraMap N (Affine.FunctionField E) c₀ from hc₀.symm]
    exact h1
  -- Step 3: `K` is algebraically closed in `F₂`, and `θ` is `K`-linear on the generator
  obtain ⟨d, hd⟩ := hR₂ s hs_alg
  let φ : RatFunc 𝕜 →ₐ[𝕜] F₂ := θ.toAlgHom.comp (IsScalarTower.toAlgHom 𝕜 (RatFunc 𝕜) F₁)
  have hgen : ∀ c : RatFunc 𝕜, ∃ d, φ c = algebraMap (RatFunc 𝕜) F₂ d :=
    exists_algebraMap_of_X_mem φ ⟨d, by rw [hd, hs]; rfl⟩
  obtain ⟨d', hd'⟩ := hgen c
  exact ⟨d', hd'⟩

end Work.MotV

set_option linter.dupNamespace false

/-- `Work.MotV.base_preserved`: the canonical (single-namespace) statement, definitionally equal to
the declaration `Work.MotV.Work.MotV.base_preserved` above, which is kept so that the doubly nested
name also resolves. -/
theorem base_preserved {𝕜 F₁ F₂ N : Type*} [Field 𝕜] [Field F₁] [Field F₂] [Field N]
    [IsAlgClosed N] (hN : ringChar N ≠ 5)
    [Algebra 𝕜 F₁] [Algebra 𝕜 F₂] [Algebra (RatFunc 𝕜) F₁] [Algebra (RatFunc 𝕜) F₂]
    [IsScalarTower 𝕜 (RatFunc 𝕜) F₁] [IsScalarTower 𝕜 (RatFunc 𝕜) F₂]
    [Algebra (RatFunc 𝕜) N] [Algebra.IsAlgebraic (RatFunc 𝕜) N]
    (E : WeierstrassCurve N) [E.IsElliptic]
    (ι₁ : F₁ →+* Affine.FunctionField E) (ι₂ : F₂ →+* Affine.FunctionField E)
    (hι₁ : ∀ c : RatFunc 𝕜, ι₁ (algebraMap _ F₁ c) = algebraMap N _ (algebraMap _ N c))
    (hι₂ : ∀ c : RatFunc 𝕜, ι₂ (algebraMap _ F₂ c) = algebraMap N _ (algebraMap _ N c))
    (hB₁ : FifthPowerValued 𝕜 (algebraMap (RatFunc 𝕜) F₁ (hT 𝕜)))
    (hB₂ : FifthPowerValued 𝕜 (algebraMap (RatFunc 𝕜) F₂ (hT 𝕜)))
    (hR₁ : ∀ r : F₁, IsAlgebraic (RatFunc 𝕜) r → ∃ c, algebraMap (RatFunc 𝕜) F₁ c = r)
    (hR₂ : ∀ r : F₂, IsAlgebraic (RatFunc 𝕜) r → ∃ c, algebraMap (RatFunc 𝕜) F₂ c = r)
    (θ : F₁ ≃ₐ[𝕜] F₂) :
    ∀ c : RatFunc 𝕜, ∃ d, θ (algebraMap (RatFunc 𝕜) F₁ c) = algebraMap (RatFunc 𝕜) F₂ d :=
  _root_.Work.MotV.Work.MotV.base_preserved hN E ι₁ ι₂ hι₁ hι₂ hB₁ hB₂ hR₁ hR₂ θ

end Work.MotV
