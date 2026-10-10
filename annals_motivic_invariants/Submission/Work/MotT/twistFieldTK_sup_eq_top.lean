import Mathlib
import Submission.Work.MotT.Defs
import Submission.Work.MotV.Defs
import Submission.Work.MotC.adjoin_genX_genY_eq_top

set_option linter.unusedVariables false -- v435-speed

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.MotT

open WeierstrassCurve WeierstrassCurve.Affine

/-- **The linear algebra of the generating relation.**  Let `S` be an `K`-subfield of a field `L`,
let `κ, z, c : Fin 5 → L` and suppose that

* `c i ∈ S` and `z i ∈ S` for every `i`,
* `κ i = κ 0 * z i` for every `i` (the `z i` are the "Kummer twists" of the `κ i`),
* `1 = ∑ i, c i * κ i` (the relation `kleinBas D L 0 = 1` written in the basis `κ`).

Then every `κ i` belongs to `S`.  Proof: multiplying the relation by `κ 0` (using `κ 0 * z 0 = κ 0`,
i.e. `z 0 = 1`) exhibits `∑ i, c i * z i` as the inverse of `κ 0`; that sum lies in `S` because all
its terms do, hence so does `κ 0 = (κ 0⁻¹)⁻¹`, and then `κ i = κ 0 * z i ∈ S`. -/
private theorem mem_of_twisted_span {L : Type*} [Field L] {K : Type*} [Field K] [Algebra K L]
    (S : IntermediateField K L) (κ z c : Fin 5 → L)
    (hc : ∀ i, c i ∈ S) (hz : ∀ i, z i ∈ S)
    (hκ : ∀ i, κ i = κ 0 * z i) (hone : (1 : L) = ∑ i, c i * κ i) :
    ∀ i, κ i ∈ S := by
  have hprod : κ 0 * (∑ i, c i * z i) = 1 := by
    rw [Finset.mul_sum, hone]
    exact Finset.sum_congr rfl fun i _ => by rw [hκ i]; ring
  have hsum_mem : (∑ i, c i * z i) ∈ S :=
    Subfield.sum_mem S.toSubfield fun i _ => mul_mem (hc i) (hz i)
  have hinv : (∑ i, c i * z i) = (κ 0)⁻¹ := eq_inv_of_mul_eq_one_right hprod
  have hκ0 : κ 0 ∈ S := by
    have h1 : (κ 0)⁻¹ ∈ S := hinv ▸ hsum_mem
    simpa using inv_mem h1
  intro i
  rw [hκ i]
  exact mul_mem hκ0 (hz i)

/-- **T2b, first half.** The T-twist field `K(C_h) ⊆ K̄(E)` together with the constants `K̄`
generates the whole function field `K̄(E)`.  (Declare it in namespace `Work.MotT`.)

Route.  `Good.spans` writes each element `kleinBas D L m` of the basis `1, x, y, x², xy` of `L(5·O)`
as an `L`-linear combination of the Klein forms `kleinCoord D L i`; at `L = KbK K` this gives
`x, y ∈ K̄ · (κ_i)`.  Each `κ_i = κ_0 · w^i · twCoordK D h i` (`pow_mul_twCoordK`), and the `m = 0`
case of `spans` (`1 = ∑ e_{0i} κ_i`) gives `κ_0^{-1} = ∑ e_{0i} w^i · twCoordK D h i ∈ K̄ · F_h`,
hence `κ_0 ∈ K̄ · F_h` and then `κ_i ∈ K̄ · F_h`; so `x, y ∈ K̄ · F_h`.  Finally
`K̄(x, y) = K̄(E)` is `Work.MotC.adjoin_genX_genY_eq_top` at `W = D.E.baseChange (KbK K)`
(`Work.MotV.genX`/`genY` are definitionally the `Work.MotC.C6.genX`/`genY` of that statement). -/
theorem twistFieldTK_sup_eq_top {K : Type} [Field K] (D : Work.MotV.KleinData K) (hD : D.Good)
    (h : K) (hh : h ≠ 0) :
    Work.MotT.twistFieldTK D h ⊔
      (IsScalarTower.toAlgHom K (Work.MotT.KbK K) (Work.MotT.OmK D)).fieldRange = ⊤ := by
  classical
  -- `S := K(C_h) ⊔ K̄` is the field we show to be everything.
  let S : IntermediateField K (Work.MotT.OmK D) :=
    Work.MotT.twistFieldTK D h ⊔
      (IsScalarTower.toAlgHom K (Work.MotT.KbK K) (Work.MotT.OmK D)).fieldRange
  change S = ⊤
  have hfr : (IsScalarTower.toAlgHom K (Work.MotT.KbK K) (Work.MotT.OmK D)).fieldRange ≤ S :=
    le_sup_right
  have htwle : Work.MotT.twistFieldTK D h ≤ S := le_sup_left
  -- `S` contains the image of the constants `K̄`.
  have hconst : ∀ x : Work.MotT.KbK K,
      algebraMap (Work.MotT.KbK K) (Work.MotT.OmK D) x ∈ S := fun x =>
    hfr (AlgHom.mem_fieldRange.mpr ⟨x, rfl⟩)
  -- `S` contains the twisted Klein coordinates, i.e. the T-twist field.
  have htw : ∀ i : Fin 5, Work.MotT.twCoordK D h i ∈ S := fun i =>
    htwle (IntermediateField.subset_adjoin K _ (Set.mem_range_self i))
  -- `κ_i = κ_0 · (w^i · y_i)`: the defining identity of the twisted coordinates.
  have hκz : ∀ i : Fin 5, Work.MotV.kleinCoord D (Work.MotT.KbK K) i =
      Work.MotV.kleinCoord D (Work.MotT.KbK K) 0 *
        (Work.MotT.wK D h ^ (i : ℕ) * Work.MotT.twCoordK D h i) := by
    intro i
    have h0 : Work.MotV.kleinCoord D (Work.MotT.KbK K) 0 ≠ 0 :=
      hD.coord0_ne (Work.MotT.KbK K)
    have hi := Work.MotT.pow_mul_twCoordK D h hh i
    calc Work.MotV.kleinCoord D (Work.MotT.KbK K) i
        = Work.MotV.kleinCoord D (Work.MotT.KbK K) i /
            Work.MotV.kleinCoord D (Work.MotT.KbK K) 0 *
            Work.MotV.kleinCoord D (Work.MotT.KbK K) 0 := (div_mul_cancel₀ _ h0).symm
      _ = (Work.MotT.wK D h ^ (i : ℕ) * Work.MotT.twCoordK D h i) *
            Work.MotV.kleinCoord D (Work.MotT.KbK K) 0 := by rw [← hi]
      _ = Work.MotV.kleinCoord D (Work.MotT.KbK K) 0 *
            (Work.MotT.wK D h ^ (i : ℕ) * Work.MotT.twCoordK D h i) := by ring
  -- `Good.spans` at `L = K̄`, in the `m = 0, 1, 2` cases.
  obtain ⟨e, he⟩ := hD.spans
  have hbas0 : Work.MotV.kleinBas D (Work.MotT.KbK K) 0 = 1 := by simp [Work.MotV.kleinBas]
  have hbas1 : Work.MotV.kleinBas D (Work.MotT.KbK K) 1 =
      Work.MotV.genX (D.E.baseChange (Work.MotT.KbK K)) := by simp [Work.MotV.kleinBas]
  have hbas2 : Work.MotV.kleinBas D (Work.MotT.KbK K) 2 =
      Work.MotV.genY (D.E.baseChange (Work.MotT.KbK K)) := by simp [Work.MotV.kleinBas]
  have hone : (1 : Work.MotT.OmK D) = ∑ i : Fin 5,
      algebraMap (Work.MotT.KbK K) (Work.MotT.OmK D)
        (algebraMap K (Work.MotT.KbK K) (e 0 i)) *
      Work.MotV.kleinCoord D (Work.MotT.KbK K) i := by
    rw [← he (Work.MotT.KbK K) 0, hbas0]
  have hx : Work.MotV.genX (D.E.baseChange (Work.MotT.KbK K)) = ∑ i : Fin 5,
      algebraMap (Work.MotT.KbK K) (Work.MotT.OmK D)
        (algebraMap K (Work.MotT.KbK K) (e 1 i)) *
      Work.MotV.kleinCoord D (Work.MotT.KbK K) i := by
    rw [← he (Work.MotT.KbK K) 1, hbas1]
  have hy : Work.MotV.genY (D.E.baseChange (Work.MotT.KbK K)) = ∑ i : Fin 5,
      algebraMap (Work.MotT.KbK K) (Work.MotT.OmK D)
        (algebraMap K (Work.MotT.KbK K) (e 2 i)) *
      Work.MotV.kleinCoord D (Work.MotT.KbK K) i := by
    rw [← he (Work.MotT.KbK K) 2, hbas2]
  -- `κ_0^{-1} = ∑ e_{0i} w^i y_i ∈ S`, hence `κ_i ∈ S` for all `i`.
  have hmem0 : ∀ i : Fin 5, Work.MotV.kleinCoord D (Work.MotT.KbK K) i ∈ S :=
    mem_of_twisted_span S _
      (fun i : Fin 5 => Work.MotT.wK D h ^ (i : ℕ) * Work.MotT.twCoordK D h i)
      (fun i : Fin 5 => algebraMap (Work.MotT.KbK K) (Work.MotT.OmK D)
        (algebraMap K (Work.MotT.KbK K) (e 0 i)))
      (fun i => hconst (algebraMap K (Work.MotT.KbK K) (e 0 i)))
      (fun i => mul_mem (pow_mem (hconst (Work.MotT.root5K h)) (i : ℕ)) (htw i))
      hκz hone
  -- Hence the basis `1, x, y, x², xy` of `L(5·O)`, and in particular `x` and `y`, lie in `S`.
  have hxS : Work.MotV.genX (D.E.baseChange (Work.MotT.KbK K)) ∈ S := by
    rw [hx]
    exact Subfield.sum_mem S.toSubfield fun i _ =>
      mul_mem (hconst (algebraMap K (Work.MotT.KbK K) (e 1 i))) (hmem0 i)
  have hyS : Work.MotV.genY (D.E.baseChange (Work.MotT.KbK K)) ∈ S := by
    rw [hy]
    exact Subfield.sum_mem S.toSubfield fun i _ =>
      mul_mem (hconst (algebraMap K (Work.MotT.KbK K) (e 2 i))) (hmem0 i)
  -- `K̄(x, y) = K̄(E)` generates everything, and it is contained in `S`.
  have htop : (⊤ : IntermediateField K (Work.MotT.OmK D)) ≤ S := by
    intro z _
    have hz : z ∈ IntermediateField.adjoin (Work.MotT.KbK K)
        ({Work.MotC.C6.genX (D.E.baseChange (Work.MotT.KbK K)),
          Work.MotC.C6.genY (D.E.baseChange (Work.MotT.KbK K))} : Set (Work.MotT.OmK D)) := by
      rw [Work.MotC.adjoin_genX_genY_eq_top (D.E.baseChange (Work.MotT.KbK K))]
      exact trivial
    exact IntermediateField.adjoin_induction (Work.MotT.KbK K)
      (p := fun u _ => u ∈ S)
      (fun u hu => by
        rw [Set.mem_insert_iff, Set.mem_singleton_iff] at hu
        rcases hu with rfl | rfl
        · exact hxS
        · exact hyS)
      (fun x => hconst x)
      (fun u v _ _ hu hv => add_mem hu hv)
      (fun u _ hu => inv_mem hu)
      (fun u v _ _ hu hv => mul_mem hu hv)
      hz
  exact le_antisymm le_top htop

end Work.MotT
