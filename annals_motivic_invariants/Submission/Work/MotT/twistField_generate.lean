import Mathlib
import Submission.Work.MotT.Defs
import Submission.Work.MotC.adjoin_genX_genY_eq_top

set_option linter.unusedVariables false -- v435-speed

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.MotT

/-- **The twist field together with the Kummer constants generates the function field.**  Let
`K → L` be a field extension, `h ∈ Kˣ`, `w ∈ L` with `w ^ 5 = algebraMap K L h` (so `w ≠ 0`), and
let `L(E) = FunctionField (W.baseChange L)` be the function field of the base-changed Weierstrass
curve.  With the twisted Klein coordinates
`y_i = (algebraMap L _ w)⁻¹ ^ i * (kleinCoord D L i / kleinCoord D L 0)` (using `D.Good.spans`),
the field `K(y_i) ⊆ L(E)` becomes `⊤` after adjoining the constants `L`.

Route.  `Good.spans` at the field `L` writes each `kleinBas D L m` as an `L`-linear combination of
the `kleinCoord D L i`; the case `m = 0` reads `1 = ∑ e_{0i} κ_i` with `e ∈ K`, and since
`κ_i = κ_0 * w ^ i * y_i` (which needs `w ≠ 0`, supplied by `hh` and `hw`) the identity
`κ_0⁻¹ = ∑ e_{0i} w ^ i y_i ∈ L · K(y_i)` follows (use `coord0_ne` for `κ_0 ≠ 0`); hence `κ_0` and
every `κ_i` lie in `L · K(y_i)`, so `x, y ∈ L · K(y_i)` by the cases `m = 1, 2`.  Finally
`L(x, y) = L(E)` is `Work.MotC.adjoin_genX_genY_eq_top` at `W = D.E.baseChange L`, whose
`Work.MotC.C6.genX`/`genY` are definitionally `Work.MotV.genX`/`genY`. -/
theorem twistField_generate {K L : Type} [Field K] [Field L] [Algebra K L]
    (D : Work.MotV.KleinData K) (hD : D.Good) (h : K) (hh : h ≠ 0) (w : L)
    (hw : w ^ 5 = algebraMap K L h) :
    IntermediateField.adjoin K (Set.range (fun i : Fin 5 =>
        (algebraMap L (WeierstrassCurve.Affine.FunctionField (D.E.baseChange L)) w)⁻¹ ^ (i : ℕ) *
          (Work.MotV.kleinCoord D L i / Work.MotV.kleinCoord D L 0))) ⊔
      (IsScalarTower.toAlgHom K L
        (WeierstrassCurve.Affine.FunctionField (D.E.baseChange L))).fieldRange = ⊤ := by
  let F := WeierstrassCurve.Affine.FunctionField (D.E.baseChange L)
  let κ : Fin 5 → F := fun i => Work.MotV.kleinCoord D L i
  let y : Fin 5 → F := fun i => (algebraMap L F w)⁻¹ ^ (i : ℕ) * (κ i / κ 0)
  let A : IntermediateField K F := IntermediateField.adjoin K (Set.range y)
  let B : IntermediateField K F := (IsScalarTower.toAlgHom K L F).fieldRange
  change A ⊔ B = ⊤
  obtain ⟨e, he⟩ := hD.spans
  have hmemB : ∀ x : L, algebraMap L F x ∈ B := by
    intro x
    exact AlgHom.mem_fieldRange.mpr ⟨x, IsScalarTower.toAlgHom_apply K L F x⟩
  have hκ0 : κ 0 ≠ 0 := hD.coord0_ne L
  have hwK : algebraMap K F h ≠ 0 :=
    fun h0 => hh ((algebraMap K F).injective (by rw [h0, map_zero]))
  have hwF : algebraMap L F w ≠ 0 := by
    intro h0
    refine hwK ?_
    rw [IsScalarTower.algebraMap_apply K L F h, ← hw, map_pow, h0]
    exact zero_pow (by norm_num)
  have hwy : ∀ i : Fin 5, (algebraMap L F w) ^ (i : ℕ) * y i = κ i / κ 0 := by
    intro i
    simp only [y]
    rw [← mul_assoc, ← mul_pow, mul_inv_cancel₀ hwF, one_pow, one_mul]
  have h1 : (1 : F) = ∑ i : Fin 5, algebraMap L F (algebraMap K L (e 0 i)) * κ i := by
    have hh1 := he L 0
    rw [show Work.MotV.kleinBas D L 0 = (1 : F) from rfl] at hh1
    simpa [κ] using hh1
  have hz : (κ 0)⁻¹ = ∑ i : Fin 5,
      (algebraMap L F (algebraMap K L (e 0 i)) * (algebraMap L F w) ^ (i : ℕ)) * y i := by
    have h1' : (κ 0)⁻¹ = ∑ i : Fin 5,
        algebraMap L F (algebraMap K L (e 0 i)) * (κ i / κ 0) := by
      rw [← one_mul (κ 0)⁻¹, h1]
      rw [Finset.sum_mul]
      exact Finset.sum_congr rfl fun i _ => by ring
    rw [h1']
    exact Finset.sum_congr rfl fun i _ => by rw [← hwy i]; ring
  have hyA : ∀ i : Fin 5, y i ∈ A := fun i =>
    IntermediateField.subset_adjoin K (Set.range y) ⟨i, rfl⟩
  have hcoefB : ∀ i : Fin 5,
      algebraMap L F (algebraMap K L (e 0 i)) * (algebraMap L F w) ^ (i : ℕ) ∈ B :=
    fun i => mul_mem (hmemB _) (pow_mem (hmemB w) _)
  have hκ0inv : (κ 0)⁻¹ ∈ A ⊔ B := by
    rw [hz]
    exact sum_mem fun i _ =>
      mul_mem ((le_sup_right : B ≤ A ⊔ B) (hcoefB i)) ((le_sup_left : A ≤ A ⊔ B) (hyA i))
  have hκ0mem : κ 0 ∈ A ⊔ B := by
    have hh' := inv_mem hκ0inv
    rwa [inv_inv] at hh'
  have hκmem : ∀ i : Fin 5, κ i ∈ A ⊔ B := by
    intro i
    have hκi : κ i = κ 0 * ((algebraMap L F w) ^ (i : ℕ) * y i) := by
      rw [hwy i]
      exact (mul_div_cancel₀ (κ i) hκ0).symm
    rw [hκi]
    exact mul_mem hκ0mem
      (mul_mem ((le_sup_right : B ≤ A ⊔ B) (pow_mem (hmemB w) _))
        ((le_sup_left : A ≤ A ⊔ B) (hyA i)))
  have hbas : ∀ m : Fin 5, Work.MotV.kleinBas D L m ∈ A ⊔ B := by
    intro m
    rw [he L m]
    exact sum_mem fun i _ =>
      mul_mem ((le_sup_right : B ≤ A ⊔ B) (hmemB (algebraMap K L (e m i))))
        (hκmem i)
  have hx : Work.MotV.genX (D.E.baseChange L) ∈ A ⊔ B := by
    have h' := hbas 1; exact h'
  have hy : Work.MotV.genY (D.E.baseChange L) ∈ A ⊔ B := by
    have h' := hbas 2; exact h'
  let C : IntermediateField L F :=
    Subfield.toIntermediateField (A ⊔ B).toSubfield
      (fun x => (le_sup_right : B ≤ A ⊔ B) (hmemB x))
  have hCtop : C = ⊤ := by
    have hle : IntermediateField.adjoin L
        ({Work.MotC.C6.genX (D.E.baseChange L), Work.MotC.C6.genY (D.E.baseChange L)} : Set F) ≤ C := by
      rw [IntermediateField.adjoin_le_iff]
      intro z hz
      rw [Set.mem_insert_iff, Set.mem_singleton_iff] at hz
      rcases hz with rfl | rfl
      · exact hx
      · exact hy
    have htop : (⊤ : IntermediateField L F) ≤ C := by
      rw [← Work.MotC.adjoin_genX_genY_eq_top (D.E.baseChange L)]
      exact hle
    exact le_antisymm le_top htop
  have hcarrier : ((A ⊔ B : IntermediateField K F) : Set F) = Set.univ := by
    have h1c : ((C : IntermediateField L F) : Set F)
        = ((A ⊔ B : IntermediateField K F) : Set F) := rfl
    have h2c : ((C : IntermediateField L F) : Set F) = Set.univ := by
      rw [hCtop]; rfl
    rw [← h1c, h2c]
  exact le_antisymm le_top fun z _ => (Set.ext_iff.mp hcarrier z).mpr trivial

end Work.MotT
