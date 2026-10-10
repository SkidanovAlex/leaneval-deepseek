import Mathlib
import Submission.Work.MotT.Defs
import Submission.Work.MotT.twistFieldTK_descent

set_option linter.unusedVariables false -- v435-speed

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.MotT

/-- In a domain which is an algebra over an algebraically closed field `K`, an element algebraic
over `K` is already a constant: the (nonzero) polynomial relation satisfied by `a` splits over `K`
into linear factors, and a product of nonzero elements of a domain is nonzero, so one of its roots
is `a`.

This is the `IsAlgClosed`-form of `Work.MotC.Uncond.isAlgebraic_of_injective_algHom`'s companion
argument: it is what makes an element of `F_h` algebraic over `K` land in `K̄ ⊆ F_h · K̄`. -/
theorem exists_algebraMap_of_isAlgebraic_of_isAlgClosed {K A : Type*} [Field K] [Field A]
    [Algebra K A] [IsAlgClosed K] {a : A} (h : IsAlgebraic K a) :
    ∃ c : K, algebraMap K A c = a := by
  obtain ⟨p, hp0, hp⟩ := h
  obtain ⟨m, hm⟩ := (Polynomial.splits_iff_exists_multiset (f := p)).mp (IsAlgClosed.splits p)
  have h1 : (Polynomial.aeval a) (Polynomial.C p.leadingCoeff *
        (m.map (fun x => Polynomial.X - Polynomial.C x)).prod)
      = (algebraMap K A) p.leadingCoeff * (m.map (fun x => a - algebraMap K A x)).prod := by
    rw [map_mul, map_multiset_prod, Polynomial.aeval_C]
    simp only [Multiset.map_map, Function.comp_apply, Polynomial.aeval_sub, Polynomial.aeval_X,
      Polynomial.aeval_C]
  have hp' : (algebraMap K A) p.leadingCoeff *
      (m.map (fun x => a - algebraMap K A x)).prod = 0 := by
    rw [← h1, ← hm]; exact hp
  have hlc : (algebraMap K A) p.leadingCoeff ≠ 0 := by
    intro h0
    exact hp0 (Polynomial.leadingCoeff_eq_zero.mp
      ((map_eq_zero_iff (algebraMap K A) (algebraMap K A).injective).mp h0))
  have h2 : (m.map (fun x => a - algebraMap K A x)).prod = 0 :=
    (mul_eq_zero.mp hp').resolve_left hlc
  have hmem : ∃ x ∈ m, a - algebraMap K A x = 0 := by
    simpa [Multiset.mem_map] using (Multiset.prod_eq_zero_iff.mp h2)
  obtain ⟨c, -, hc⟩ := hmem
  exact ⟨c, (sub_eq_zero.mp hc).symm⟩

/-- **The Klein scaling automorphisms of a Klein model, over any base `L ⊇ K`.**  For every fifth
root of unity `c` of `L` there is an `L`-algebra automorphism of the function field `L(E)` which
multiplies the Klein ratios `κ_i/κ_0` by `c^i` (`D.Good.T_diag` with `ζ = c` when `c ≠ 1`, and the
identity when `c = 1`).

This is the `T_diag` half of the twisted Galois action `γ* = τ_{c(γ)} ∘ γ` of the T-route: it is
what makes the twisted coordinates `w^{-i} κ_i/κ_0` invariant, and it does not appear among the
`T`-route nodes, so it is recorded here. -/
theorem exists_kleinScaling {K L : Type} [Field K] [Field L] [Algebra K L]
    (D : Work.MotV.KleinData K) (hD : D.Good) (c : L) (hc : c ^ 5 = 1) :
    ∃ τ : WeierstrassCurve.Affine.FunctionField (D.E.baseChange L) ≃ₐ[L]
        WeierstrassCurve.Affine.FunctionField (D.E.baseChange L),
      ∀ i : Fin 5, τ (Work.MotV.kleinCoord D L i / Work.MotV.kleinCoord D L 0)
        = (algebraMap L (WeierstrassCurve.Affine.FunctionField (D.E.baseChange L)) c) ^ (i : ℕ) *
          (Work.MotV.kleinCoord D L i / Work.MotV.kleinCoord D L 0) := by
  rcases eq_or_ne c 1 with rfl | hc1
  · refine ⟨1, fun i => ?_⟩
    simp
  · haveI : Fact (Nat.Prime 5) := ⟨by norm_num⟩
    have hprim : IsPrimitiveRoot c 5 := by
      rw [IsPrimitiveRoot.iff_orderOf]
      exact orderOf_eq_prime hc hc1
    obtain ⟨σ, hσ⟩ := hD.T_diag L c hprim
    exact ⟨σ, fun i => hσ i⟩

/-- **T3 (REG over `K`).**  The base field `K` is algebraically closed in the T-twist field
`F_h = Work.MotT.twistFieldTK D h` (for `h ≠ 0` and `ringChar K ≠ 5`).  This is the corollary of
T2 (`Work.MotT.twistFieldTK_descent`) whose `{K : Type}`-form fixes the universe defect of route V's
`Work.MotV.twist_regular`.  Route: T2 gives `F_h` linearly disjoint from `K̄` over `K` (hence
`F_h ⊓ K̄ = K` via `LinearDisjoint.inf_eq_bot`); an `r ∈ F_h` algebraic over `K` is algebraic over
`K̄`, and since `K̄` is algebraically closed and `K̄(E)` is a domain containing `K̄`, the minimal
polynomial of `r` splits in `K̄[X] ⊆ OmK D[X]` with `r` one of its roots, so `r ∈ K̄`; therefore
`r ∈ F_h ⊓ K̄ = K`, which is the claim.

Declare it in namespace `Work.MotT` so that its full name is `Work.MotT.twistFieldTK_regular`. -/
theorem twistFieldTK_regular {K : Type} [Field K] (D : Work.MotV.KleinData K) (hD : D.Good)
    (hk : ringChar K ≠ 5) (h : K) (hh : h ≠ 0) (r : Work.MotT.twistFieldTK D h)
    (hr : IsAlgebraic K r) :
    ∃ c : K, algebraMap K (Work.MotT.twistFieldTK D h) c = r := by
  obtain ⟨hLI, _hsup⟩ := twistFieldTK_descent D hD hk h hh
  set f := IsScalarTower.toAlgHom K (KbK K) (OmK D) with hf
  -- T2 gives linear disjointness of `F_h` with `K̄`; the corresponding intersection is `K`.
  have hbot_sub : (twistFieldTK D h).toSubalgebra ⊓ f.range = ⊥ :=
    Subalgebra.LinearDisjoint.inf_eq_bot hLI
  have hbot : twistFieldTK D h ⊓ f.fieldRange = ⊥ := by
    refine le_antisymm ?_ bot_le
    intro x hx
    rw [IntermediateField.mem_inf] at hx
    rw [IntermediateField.mem_bot]
    have hx' : x ∈ (twistFieldTK D h).toSubalgebra ⊓ f.range := ⟨hx.1, hx.2⟩
    rw [hbot_sub] at hx'
    exact hx'
  -- `r` is algebraic over `K`, hence over `K̄`.
  have hr' : IsAlgebraic K ((r : OmK D)) :=
    (isAlgebraic_algHom_iff (IntermediateField.val (twistFieldTK D h)) Subtype.coe_injective).mpr hr
  have hKb : IsAlgebraic (KbK K) ((r : OmK D)) := by
    obtain ⟨p, hp0, hp⟩ := hr'
    refine ⟨p.map (algebraMap K (KbK K)), ?_, ?_⟩
    · intro h0
      exact hp0 ((Polynomial.map_eq_zero_iff (algebraMap K (KbK K)).injective).mp h0)
    · rw [Polynomial.aeval_map_algebraMap (KbK K) (r : OmK D) p]
      exact hp
  -- `K̄` is algebraically closed, so `r` is the image of some `c : K̄`.
  obtain ⟨c, hc⟩ := exists_algebraMap_of_isAlgebraic_of_isAlgClosed hKb
  have hmem : algebraMap (KbK K) (OmK D) c ∈ twistFieldTK D h ⊓ f.fieldRange := by
    refine ⟨?_, ?_⟩
    · rw [hc]; exact r.2
    · exact ⟨c, rfl⟩
  rw [hbot] at hmem
  rw [IntermediateField.mem_bot] at hmem
  obtain ⟨c', hc'⟩ := hmem
  refine ⟨c', ?_⟩
  apply Subtype.ext
  change algebraMap K (OmK D) c' = (r : OmK D)
  rw [hc']; exact hc

end Work.MotT
