import Mathlib
import Submission.Work.MotAS.ASResidual
import Submission.Work.MotAS.ASZGC.Defs
import Submission.Work.MotAS.ASRulV2M.sat_mem_gen
import Submission.Work.Reflect.PolyId

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# `Work.MotAS.ASRulV2M.sat_mem13`

The two remaining saturation memberships `zcubAS a b g k ∈ SatAS a b g` for `k = 1, 3`, in the
`ASZGC` normalisation.

* `zcubAS_decomp1`, `zcubAS_decomp3` — the `X 0`-decompositions of `zcubAS a b g 1` and
  `zcubAS a b g 3` in the `ASZGC` basis `fk<k>_<j>`.  The difference of the two sides is a polynomial
  whose coefficients are all divisible by `5`; `ring_nf` puts it in normal form and
  `reduce_mod_char!` (which needs a *local* `CharP (MvPolynomial (Fin 3) K) 5` instance) collapses
  it.
* `zcubAS_mem_sat_1_of`, `_3_of` — given `P ∣ Nn<k>` (`Nn_dvd_gen`), the geometric-series identity
  `geom3` writes `(ren D₀)^3 · z_k = ren (Nn<k>) + cofactor · G`, and `ren (Nn<k>) = ren P · ren S`.
-/

set_option maxHeartbeats 4000000
set_option maxRecDepth 100000
set_option linter.unusedVariables false

namespace Work.MotAS.ASRulV2M

open MvPolynomial

/-- The `X 0`-decomposition of `zcubAS a b g 1` (in the `ASZGC` normalisation). -/
theorem zcubAS_decomp1 (K : Type) [Field K] [CharP K 5] (a b g : K) :
    Work.MotAS.zcubAS a b g 1
      = MvPolynomial.rename (Fin.succ : Fin 2 → Fin 3) (Work.MotAS.ASZGC.fk1_0 a b g)
        + MvPolynomial.rename (Fin.succ : Fin 2 → Fin 3) (Work.MotAS.ASZGC.fk1_1 a b g)
            * MvPolynomial.X 0
        + MvPolynomial.rename (Fin.succ : Fin 2 → Fin 3) (Work.MotAS.ASZGC.fk1_2 a b g)
            * MvPolynomial.X 0 ^ 2
        + MvPolynomial.rename (Fin.succ : Fin 2 → Fin 3) (Work.MotAS.ASZGC.fk1_3 a b g)
            * MvPolynomial.X 0 ^ 3 := by
  haveI : CharP (MvPolynomial (Fin 3) K) 5 := inferInstance
  simp only [Work.MotAS.zcubAS, Work.MotAS.kleinRAS, Work.MotAS.kleinRAS0, Work.MotAS.kleinRAS1,
    Work.MotAS.kleinRAS2, Work.MotAS.kleinRAS3, Work.MotAS.kleinRAS4,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.cons_val_three,
    Matrix.cons_val_four, Matrix.head_cons, Matrix.tail_cons, Fin.isValue,
    Work.MotAS.ASZGC.fk1_0, Work.MotAS.ASZGC.fk1_1, Work.MotAS.ASZGC.fk1_2,
    Work.MotAS.ASZGC.fk1_3,
    map_add, map_mul, map_pow, map_ofNat, MvPolynomial.rename_C, MvPolynomial.rename_X,
    Fin.succ_zero_eq_one, Fin.succ_one_eq_two]
  refl_ring1 (mod := 5)

/-- The `X 0`-decomposition of `zcubAS a b g 3` (in the `ASZGC` normalisation). -/
theorem zcubAS_decomp3 (K : Type) [Field K] [CharP K 5] (a b g : K) :
    Work.MotAS.zcubAS a b g 3
      = MvPolynomial.rename (Fin.succ : Fin 2 → Fin 3) (Work.MotAS.ASZGC.fk3_0 a b g)
        + MvPolynomial.rename (Fin.succ : Fin 2 → Fin 3) (Work.MotAS.ASZGC.fk3_1 a b g)
            * MvPolynomial.X 0
        + MvPolynomial.rename (Fin.succ : Fin 2 → Fin 3) (Work.MotAS.ASZGC.fk3_2 a b g)
            * MvPolynomial.X 0 ^ 2
        + MvPolynomial.rename (Fin.succ : Fin 2 → Fin 3) (Work.MotAS.ASZGC.fk3_3 a b g)
            * MvPolynomial.X 0 ^ 3 := by
  haveI : CharP (MvPolynomial (Fin 3) K) 5 := inferInstance
  simp only [Work.MotAS.zcubAS, Work.MotAS.kleinRAS, Work.MotAS.kleinRAS0, Work.MotAS.kleinRAS1,
    Work.MotAS.kleinRAS2, Work.MotAS.kleinRAS3, Work.MotAS.kleinRAS4,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.cons_val_three,
    Matrix.cons_val_four, Matrix.head_cons, Matrix.tail_cons, Fin.isValue,
    Work.MotAS.ASZGC.fk3_0, Work.MotAS.ASZGC.fk3_1, Work.MotAS.ASZGC.fk3_2,
    Work.MotAS.ASZGC.fk3_3,
    map_add, map_mul, map_pow, map_ofNat, MvPolynomial.rename_C, MvPolynomial.rename_X,
    Fin.succ_zero_eq_one, Fin.succ_one_eq_two]
  refl_ring1 (mod := 5)

/-- The membership for `k = 1`, given `P ∣ Nn1`. -/
theorem zcubAS_mem_sat_1_of (K : Type) [Field K] [CharP K 5] (a b g : K)
    (h : Work.MotAS.ASZElim.P a b g ∣ Work.MotAS.ASZGC.Nn1 a b g) :
    ∃ N : ℕ, (Work.MotC5N3.X2AuxInputs.D a b g) ^ N * Work.MotAS.zcubAS a b g 1
      ∈ Ideal.span {Work.MotC5N3.X2AuxInputs.Pemb a b g, Work.MotC5N3.X2AuxInputs.G a b g} := by
  obtain ⟨S, hS⟩ := h
  have hNn : MvPolynomial.rename (Fin.succ : Fin 2 → Fin 3) (Work.MotAS.ASZGC.Nn1 a b g)
      = MvPolynomial.rename (Fin.succ : Fin 2 → Fin 3) (Work.MotAS.ASZGC.fk1_0 a b g)
          * (MvPolynomial.rename (Fin.succ : Fin 2 → Fin 3) (Work.MotAS.ASZGC.D0 a b g)) ^ 3
        + MvPolynomial.rename (Fin.succ : Fin 2 → Fin 3) (Work.MotAS.ASZGC.fk1_1 a b g)
          * (MvPolynomial.rename (Fin.succ : Fin 2 → Fin 3) (Work.MotAS.ASZGC.D0 a b g)) ^ 2
          * (-MvPolynomial.rename (Fin.succ : Fin 2 → Fin 3) (Work.MotAS.ASZGC.R0 a b g))
        + MvPolynomial.rename (Fin.succ : Fin 2 → Fin 3) (Work.MotAS.ASZGC.fk1_2 a b g)
          * (MvPolynomial.rename (Fin.succ : Fin 2 → Fin 3) (Work.MotAS.ASZGC.D0 a b g))
          * (-MvPolynomial.rename (Fin.succ : Fin 2 → Fin 3) (Work.MotAS.ASZGC.R0 a b g)) ^ 2
        + MvPolynomial.rename (Fin.succ : Fin 2 → Fin 3) (Work.MotAS.ASZGC.fk1_3 a b g)
          * (-MvPolynomial.rename (Fin.succ : Fin 2 → Fin 3) (Work.MotAS.ASZGC.R0 a b g)) ^ 3 := by
    rw [Work.MotAS.ASZGC.Nn1]
    simp only [map_add, map_mul, map_pow, map_neg, map_one, map_zero, pow_zero, mul_one]
    first | refl_ring1 | ring
  refine ⟨3, ?_⟩
  rw [Work.ASZF.D_eq_renameD0 K a b g, zcubAS_decomp1 K a b g,
    geom3 (MvPolynomial.rename (Fin.succ : Fin 2 → Fin 3) (Work.MotAS.ASZGC.D0 a b g))
      (MvPolynomial.rename (Fin.succ : Fin 2 → Fin 3) (Work.MotAS.ASZGC.R0 a b g))
      (MvPolynomial.X 0)
      (MvPolynomial.rename (Fin.succ : Fin 2 → Fin 3) (Work.MotAS.ASZGC.fk1_0 a b g))
      (MvPolynomial.rename (Fin.succ : Fin 2 → Fin 3) (Work.MotAS.ASZGC.fk1_1 a b g))
      (MvPolynomial.rename (Fin.succ : Fin 2 → Fin 3) (Work.MotAS.ASZGC.fk1_2 a b g))
      (MvPolynomial.rename (Fin.succ : Fin 2 → Fin 3) (Work.MotAS.ASZGC.fk1_3 a b g)),
    ← hNn, hS, map_mul]
  rw [show MvPolynomial.rename (Fin.succ : Fin 2 → Fin 3) (Work.MotAS.ASZGC.D0 a b g)
        * MvPolynomial.X 0
        + MvPolynomial.rename (Fin.succ : Fin 2 → Fin 3) (Work.MotAS.ASZGC.R0 a b g)
      = Work.MotC5N3.X2AuxInputs.G a b g from by
    rw [Work.MotC5N3.X2AuxInputs.G, Work.ASZF.D_eq_renameD0 K a b g,
      Work.ASZF.R_eq_renameR0 K a b g]]
  have hPemb_mem : Work.MotC5N3.X2AuxInputs.Pemb a b g
      ∈ Ideal.span {Work.MotC5N3.X2AuxInputs.Pemb a b g, Work.MotC5N3.X2AuxInputs.G a b g} :=
    Ideal.subset_span (Set.mem_insert _ _)
  have hG_mem : Work.MotC5N3.X2AuxInputs.G a b g
      ∈ Ideal.span {Work.MotC5N3.X2AuxInputs.Pemb a b g, Work.MotC5N3.X2AuxInputs.G a b g} :=
    Ideal.subset_span (Set.mem_insert_of_mem _ (Set.mem_singleton_iff.mpr rfl))
  refine Ideal.add_mem _ ?_ ?_
  · exact Ideal.mul_mem_right (MvPolynomial.rename (Fin.succ : Fin 2 → Fin 3) S)
      (Ideal.span {Work.MotC5N3.X2AuxInputs.Pemb a b g, Work.MotC5N3.X2AuxInputs.G a b g})
      hPemb_mem
  · exact Ideal.mul_mem_left _ _ hG_mem

/-- The membership for `k = 3`, given `P ∣ Nn3`. -/
theorem zcubAS_mem_sat_3_of (K : Type) [Field K] [CharP K 5] (a b g : K)
    (h : Work.MotAS.ASZElim.P a b g ∣ Work.MotAS.ASZGC.Nn3 a b g) :
    ∃ N : ℕ, (Work.MotC5N3.X2AuxInputs.D a b g) ^ N * Work.MotAS.zcubAS a b g 3
      ∈ Ideal.span {Work.MotC5N3.X2AuxInputs.Pemb a b g, Work.MotC5N3.X2AuxInputs.G a b g} := by
  obtain ⟨S, hS⟩ := h
  have hNn : MvPolynomial.rename (Fin.succ : Fin 2 → Fin 3) (Work.MotAS.ASZGC.Nn3 a b g)
      = MvPolynomial.rename (Fin.succ : Fin 2 → Fin 3) (Work.MotAS.ASZGC.fk3_0 a b g)
          * (MvPolynomial.rename (Fin.succ : Fin 2 → Fin 3) (Work.MotAS.ASZGC.D0 a b g)) ^ 3
        + MvPolynomial.rename (Fin.succ : Fin 2 → Fin 3) (Work.MotAS.ASZGC.fk3_1 a b g)
          * (MvPolynomial.rename (Fin.succ : Fin 2 → Fin 3) (Work.MotAS.ASZGC.D0 a b g)) ^ 2
          * (-MvPolynomial.rename (Fin.succ : Fin 2 → Fin 3) (Work.MotAS.ASZGC.R0 a b g))
        + MvPolynomial.rename (Fin.succ : Fin 2 → Fin 3) (Work.MotAS.ASZGC.fk3_2 a b g)
          * (MvPolynomial.rename (Fin.succ : Fin 2 → Fin 3) (Work.MotAS.ASZGC.D0 a b g))
          * (-MvPolynomial.rename (Fin.succ : Fin 2 → Fin 3) (Work.MotAS.ASZGC.R0 a b g)) ^ 2
        + MvPolynomial.rename (Fin.succ : Fin 2 → Fin 3) (Work.MotAS.ASZGC.fk3_3 a b g)
          * (-MvPolynomial.rename (Fin.succ : Fin 2 → Fin 3) (Work.MotAS.ASZGC.R0 a b g)) ^ 3 := by
    rw [Work.MotAS.ASZGC.Nn3]
    simp only [map_add, map_mul, map_pow, map_neg, map_one, map_zero, pow_zero, mul_one]
    first | refl_ring1 | ring
  refine ⟨3, ?_⟩
  rw [Work.ASZF.D_eq_renameD0 K a b g, zcubAS_decomp3 K a b g,
    geom3 (MvPolynomial.rename (Fin.succ : Fin 2 → Fin 3) (Work.MotAS.ASZGC.D0 a b g))
      (MvPolynomial.rename (Fin.succ : Fin 2 → Fin 3) (Work.MotAS.ASZGC.R0 a b g))
      (MvPolynomial.X 0)
      (MvPolynomial.rename (Fin.succ : Fin 2 → Fin 3) (Work.MotAS.ASZGC.fk3_0 a b g))
      (MvPolynomial.rename (Fin.succ : Fin 2 → Fin 3) (Work.MotAS.ASZGC.fk3_1 a b g))
      (MvPolynomial.rename (Fin.succ : Fin 2 → Fin 3) (Work.MotAS.ASZGC.fk3_2 a b g))
      (MvPolynomial.rename (Fin.succ : Fin 2 → Fin 3) (Work.MotAS.ASZGC.fk3_3 a b g)),
    ← hNn, hS, map_mul]
  rw [show MvPolynomial.rename (Fin.succ : Fin 2 → Fin 3) (Work.MotAS.ASZGC.D0 a b g)
        * MvPolynomial.X 0
        + MvPolynomial.rename (Fin.succ : Fin 2 → Fin 3) (Work.MotAS.ASZGC.R0 a b g)
      = Work.MotC5N3.X2AuxInputs.G a b g from by
    rw [Work.MotC5N3.X2AuxInputs.G, Work.ASZF.D_eq_renameD0 K a b g,
      Work.ASZF.R_eq_renameR0 K a b g]]
  have hPemb_mem : Work.MotC5N3.X2AuxInputs.Pemb a b g
      ∈ Ideal.span {Work.MotC5N3.X2AuxInputs.Pemb a b g, Work.MotC5N3.X2AuxInputs.G a b g} :=
    Ideal.subset_span (Set.mem_insert _ _)
  have hG_mem : Work.MotC5N3.X2AuxInputs.G a b g
      ∈ Ideal.span {Work.MotC5N3.X2AuxInputs.Pemb a b g, Work.MotC5N3.X2AuxInputs.G a b g} :=
    Ideal.subset_span (Set.mem_insert_of_mem _ (Set.mem_singleton_iff.mpr rfl))
  refine Ideal.add_mem _ ?_ ?_
  · exact Ideal.mul_mem_right (MvPolynomial.rename (Fin.succ : Fin 2 → Fin 3) S)
      (Ideal.span {Work.MotC5N3.X2AuxInputs.Pemb a b g, Work.MotC5N3.X2AuxInputs.G a b g})
      hPemb_mem
  · exact Ideal.mul_mem_left _ _ hG_mem

end Work.MotAS.ASRulV2M
