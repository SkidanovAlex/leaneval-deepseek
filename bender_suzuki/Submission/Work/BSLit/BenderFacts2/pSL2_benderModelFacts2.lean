import Mathlib
import Submission.Work.BSLit.Defs
import Submission.Work.Models.ModelData.pSL2ModelData
import Submission.Work.Models.Port.PSL2Torus
import Submission.Work.BSLit.BenderFacts2.Facts2Aux
import Submission.Work.BSLit.BenderFacts2.isStronglyEmbedded_map_mulEquiv
import Submission.Work.BSLit.BenderFacts2.benderFacts2For_map_mulEquiv
import Submission.Work.BSLit.BenderFacts2.sl2_mem_U_of_orderOf_eq_two_pow
import Submission.Work.BSLit.BenderFacts2.Facts2SL2Aux
import Submission.Work.BSLit.BenderFacts2.sl2_centralizer_isCyclic_of_trace_ne_zero

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

namespace Work.BSLit.BenderFacts2

/-- **The lead's `BenderModelFacts2Prop` for `PSL(2, 2ⁿ)`** (`n ≥ 2`), with `Y = PSL2Model n`. Route: reduce to `H = B` with `Submission.PSL2.pSL2StronglyEmbedded_eq_benderPair_borel` (conjugation preserves `orderOf`, `x ^ 4 = 1`, the centraliser up to isomorphism, `IsCyclic`, the number of involutions and `IsZassenhaus` — for the last one either prove the transport directly or use the group-theoretic form of the three-point condition `∀ x y, x ∉ H → y ∉ H → x⁻¹ * y ∉ H → H ⊓ conj x H ⊓ conj y H = ⊥`). (1°) `B = U ⋊ T` with `U = (unipotentPSLHom (GaloisField 2 n)).range ≅ (K,+)` elementary abelian and `T` odd, so a 2-element of `B` lies in `U` and hence squares to 1. (2°) the involutions of `B` are the transvections `u(c)`, `c ≠ 0`; `t` is `B`-conjugate to the Weyl element `w := weylPSL K` (all involutions of `PSL2Model n` are conjugate and `B w B` is the unique non-Borel double coset), so assume `t = w`. Then `u(c) * w` is the matrix `!![c, 1; 1, 0]` with characteristic polynomial `X² + cX + 1`, whose centraliser in `SL(2, K)` is the unit group of the commutative algebra `K[g]` (≅ `GF(2^{2n})` or `GF(2^n) × GF(2^n)`), hence cyclic of order `2^n + 1` or `2^n - 1`; `u(c)` inverts every element of it (have `u(c) g u(c)⁻¹ = g⁻¹` and use that `K[g]` is commutative with `y * (u(c) y u(c)⁻¹) = 1` whenever `det y = 1`), and `127 ≤ #Inv H = 2^n - 1` gives `2^n ≥ 128`, so the order is `≥ 6`. Useful files: `Work.Models.PSL2.*` (`unip`, `U`, `B`, `D`, `w`, `bruhat`, `centralizer_unip`), `Work.Models.Port.PSL2Torus` (`diagPSLHom`, `weylPSL`, `inf_map_conj_weyl_eq_diag`, `centralizer_unipotentPSLHom_eq_range`), `Work.Models.ModelData.pSL2ModelData`. -/
theorem pSL2_benderModelFacts2 (n : ℕ) (hn : 2 ≤ n) :
    ∀ H : Subgroup (LeanEval.GroupTheory.Defs.PSL2Model n),
      LeanEval.GroupTheory.Defs.IsStronglyEmbedded H →
      (∀ x ∈ H, (∃ k : ℕ, orderOf x = 2 ^ k) → x ^ 4 = 1) ∧
      (Submission.Blueprint.IsZassenhaus H →
        ∀ u ∈ Submission.Blueprint.involutions (H : Set (LeanEval.GroupTheory.Defs.PSL2Model n)),
        ∀ t : LeanEval.GroupTheory.Defs.PSL2Model n, orderOf t = 2 → t ∉ H →
        IsCyclic ↥(Subgroup.centralizer ({u * t} : Set (LeanEval.GroupTheory.Defs.PSL2Model n))) ∧
        (∀ y ∈ Subgroup.centralizer ({u * t} : Set (LeanEval.GroupTheory.Defs.PSL2Model n)),
          u * y * u⁻¹ = y⁻¹) ∧
        (127 ≤ (Submission.Blueprint.involutions
            (H : Set (LeanEval.GroupTheory.Defs.PSL2Model n))).ncard →
          6 ≤ Nat.card ↥(Subgroup.centralizer
            ({u * t} : Set (LeanEval.GroupTheory.Defs.PSL2Model n))))) := by
  intro H hH
  -- `SL(2, 2ⁿ) ≅ PSL(2, 2ⁿ)` (the centre of `SL(2,F)` is trivial in characteristic two)
  obtain ⟨e⟩ := Work.Models.PSL2.pslEquiv n
  have hH' : LeanEval.GroupTheory.Defs.IsStronglyEmbedded (H.map e.symm.toMonoidHom) :=
    (isStronglyEmbedded_map_mulEquiv e.symm H).mpr hH
  have hfacts := benderFacts2For_sl2 n (H.map e.symm.toMonoidHom) hH'
  have hback : BenderFacts2For (LeanEval.GroupTheory.Defs.PSL2Model n) H :=
    (benderFacts2For_map_mulEquiv e.symm H).mp hfacts
  exact ⟨hback.1, fun _ => hback.2⟩

end Work.BSLit.BenderFacts2
