import Mathlib
import Submission.Work.ORLyndon.CLDirect.cldDefs
import Submission.Work.ORLyndon.CLDirect.conj_pow_eq
import Submission.Work.ORLyndon.CLDirect.clPi_of
import Submission.Work.ORLyndon.CLDirect.clDelta_of
import Submission.Work.ORLyndon.CLDirect.clDelta_pow
import Submission.Work.ORLyndon.CLDirect.clDelta_conj_of_trivial

namespace Work.ORLyndon.CLDirect

/-- `φ(f u^l f⁻¹) = f̄ · N_w` where `N_w = Σ_{k<l} w^k`. Sketch: `conj_pow_eq D f l` gives `m` with `m * D.s q = f`; set `a := D.e.symm m`, `b := of q`; then `D.e.symm ⟨f u^l f⁻¹,_⟩ = a * b^l * a⁻¹` (by `MulEquiv.symm_apply_eq` / `D.e.injective`, using `Subtype.ext` and `coe_pow`). Apply `clDelta_conj_of_trivial` with `h = b^l` (hypothesis `presentRho (D.e (b^l)) = presentRho ((s u s⁻¹)^l) = 1` by `map_pow`, `D.e_of`, `conj_pow`, `presentRho_relator`). Then `clDelta_pow` with `k = l`, and `clPi_of`, `clDelta_of` give `Σ_i of (ρ(s u s⁻¹))^i · of (ρ s) = of (ρ s) · Σ_i of (ρ u)^i` (using `conj_pow`, `map_mul`). Finally `clPi (of a) * of (ρ s) = of (ρ (m * s)) = of (ρ f)` by `clPi_of` and the first conjunct of `conj_pow_eq`; unfold `normElem`. -/
theorem clPhi_conj_pow {X : Type*} [DecidableEq X] {K : Type*} [Field K] {u : FreeGroup X}
    (D : Work.ORLyndon.CLDirect.CLData u) (l : ℕ) (f : FreeGroup X) :
    Work.ORLyndon.CLDirect.clPhi (K := K) D l (f * u ^ l * f⁻¹) =
      MonoidAlgebra.of K _ (Work.ORLyndon.presentRho (u ^ l) f) *
        Work.ORLyndon.normElem K l (Work.ORLyndon.presentRho (u ^ l) u) := by
  classical
  -- Split `f` along the Cohen--Lyndon section: `m ∈ M` with `m * s q = f` and
  -- `f u^l f⁻¹ = m (e (of q))^l m⁻¹`.
  obtain ⟨m, hm1, hm2⟩ := Work.ORLyndon.CLDirect.conj_pow_eq D f l
  set q := QuotientGroup.mk f with hq
  have hmem : f * u ^ l * f⁻¹ ∈ Subgroup.normalClosure ({u} : Set (FreeGroup X)) :=
    hm2 ▸ (m * D.e (FreeGroup.of q) ^ l * m⁻¹).2
  rw [Work.ORLyndon.CLDirect.clPhi, dif_pos hmem]
  -- `D.e.symm ⟨f u^l f⁻¹, _⟩ = a * b^l * a⁻¹` with `a = e.symm m`, `b = of q`.
  have hsyme : D.e.symm ⟨f * u ^ l * f⁻¹, hmem⟩ =
      D.e.symm m * (FreeGroup.of q) ^ l * (D.e.symm m)⁻¹ := by
    apply D.e.injective
    rw [MulEquiv.apply_symm_apply]
    apply Subtype.ext
    simp only [map_mul, map_pow, map_inv, MulEquiv.apply_symm_apply,
      Subgroup.coe_mul, Subgroup.coe_pow, Subgroup.coe_inv]
    rw [D.e_of q, conj_pow, ← hm1]
    group
  rw [hsyme]
  -- `b^l` dies in the one-relator group.
  have hh : Work.ORLyndon.presentRho (u ^ l)
      ((D.e ((FreeGroup.of q) ^ l) : ↥(Subgroup.normalClosure ({u} : Set (FreeGroup X)))) :
        FreeGroup X) = 1 := by
    rw [map_pow, Subgroup.coe_pow, D.e_of q, conj_pow, map_mul, map_mul,
      Work.ORLyndon.presentRho_relator, mul_one, map_inv, mul_inv_cancel]
  rw [Work.ORLyndon.CLDirect.clDelta_conj_of_trivial (K := K) D l (D.e.symm m)
    ((FreeGroup.of q) ^ l) hh]
  rw [Work.ORLyndon.CLDirect.clDelta_pow]
  rw [Work.ORLyndon.CLDirect.clDelta_of]
  -- Abbreviate the images in `G` of `D.s q` and `u`.
  set s : Work.ORLyndon.OneRelatorGroup (u ^ l) :=
    Work.ORLyndon.presentRho (u ^ l) (D.s q) with hs
  set w : Work.ORLyndon.OneRelatorGroup (u ^ l) := Work.ORLyndon.presentRho (u ^ l) u with hw
  -- The Cohen--Lyndon basis element maps to the conjugate of `w` by `s`.
  have hDeG : Work.ORLyndon.presentRho (u ^ l)
      ((D.e (FreeGroup.of q) : ↥(Subgroup.normalClosure ({u} : Set (FreeGroup X)))) : FreeGroup X)
      = s * w * s⁻¹ := by
    rw [D.e_of q, hs, hw, map_mul, map_mul, map_inv]
  have hPi_a : Work.ORLyndon.CLDirect.clPi (K := K) D l
      (MonoidAlgebra.of K _ (D.e.symm m)) =
      MonoidAlgebra.of K _ (Work.ORLyndon.presentRho (u ^ l) (↑m : FreeGroup X)) := by
    rw [Work.ORLyndon.CLDirect.clPi_of, MulEquiv.apply_symm_apply]
  have hbase : Work.ORLyndon.CLDirect.clPi (K := K) D l
      (MonoidAlgebra.of K _ (FreeGroup.of q)) = MonoidAlgebra.of K _ (s * w * s⁻¹) := by
    rw [Work.ORLyndon.CLDirect.clPi_of, hDeG]
  -- The geometric sum of a conjugate telescopes.
  have hterm : ∀ i : ℕ, (Work.ORLyndon.CLDirect.clPi (K := K) D l
      (MonoidAlgebra.of K _ (FreeGroup.of q)))^i =
      MonoidAlgebra.of K _ s * (MonoidAlgebra.of K _ w)^i * MonoidAlgebra.of K _ (s⁻¹) := by
    intro i
    rw [hbase, ← map_pow, conj_pow, map_mul, map_mul, map_pow]
  have hsum : (∑ i ∈ Finset.range l, (Work.ORLyndon.CLDirect.clPi (K := K) D l
      (MonoidAlgebra.of K _ (FreeGroup.of q)))^i) =
      MonoidAlgebra.of K _ s * (Work.ORLyndon.normElem K l w) * MonoidAlgebra.of K _ (s⁻¹) := by
    rw [Work.ORLyndon.normElem, Finset.sum_congr rfl (fun i _ => hterm i), Finset.mul_sum,
      Finset.sum_mul]
  rw [hPi_a, hsum]
  have hsi : MonoidAlgebra.of K _ (s⁻¹) * MonoidAlgebra.of K _ s = 1 := by
    rw [← map_mul, inv_mul_cancel, map_one]
  have hmf : MonoidAlgebra.of K _ (Work.ORLyndon.presentRho (u ^ l) (↑m : FreeGroup X)) *
      MonoidAlgebra.of K _ s = MonoidAlgebra.of K _ (Work.ORLyndon.presentRho (u ^ l) f) := by
    rw [hs, ← map_mul, ← map_mul, hm1]
  simp only [mul_assoc]
  rw [hsi, mul_one, ← mul_assoc, hmf]

end Work.ORLyndon.CLDirect
