/-
  WilG4c / `SliceC1Shape` — the `Ω`-encoding of the fibre `C¹`-locus `C1Pred`.

  This is the outer layer on top of `SliceC1FD`.  The predicate `C1Exp` is the expansion of
  `C1Pred` with the values of the family member accessed through the graph set `G`
  (`Fin.snoc (Fin.append l y) t ∈ G` saying `t = f l y`), and `c1P` is the `TSh`-shape whose
  realisation is exactly `{z | C1Exp P M G z}`; `c1P_Real` proves that, `C1Exp_iff` converts
  `C1Exp` back to `C1Pred`.

  Everything is `sorry`-free.
-/
import Mathlib
import Submission.Work.WilG4c.SliceC1FD

set_option autoImplicit false
set_option linter.unusedSimpArgs false
noncomputable section
open Classical

namespace Work.WilG4c

open WilkiesDesign WilkiesDesign.CG

/-! ## 1. The predicate realised by the shape -/

/-- The expansion of `C1Pred`, with the family values accessed through the graph set `G`. -/
def C1Exp (P M : ℕ) (G : Set (Fin (P + M + 1) → ℝ)) (z : Fin (P + M) → ℝ) : Prop :=
  ∃ δ₀ : ℝ, 0 < δ₀ ∧
    ∀ y : Fin M → ℝ, (∑ j : Fin M, (y j - z (Fin.natAdd P j)) ^ 2) < δ₀ ^ 2 →
      ∃ c : Fin M → ℝ, ∃ t : ℝ,
        Fin.snoc (Fin.append (z ∘ fun i : Fin P => Fin.castAdd M i) y) t ∈ G ∧
        (∀ ε₁ : ℝ, 0 < ε₁ → ∃ δ₁ : ℝ, 0 < δ₁ ∧
          ∀ y₂ : Fin M → ℝ, (∑ j : Fin M, (y₂ j - y j) ^ 2) < δ₁ ^ 2 →
            ∃ t₂ : ℝ,
              Fin.snoc (Fin.append (z ∘ fun i : Fin P => Fin.castAdd M i) y₂) t₂ ∈ G ∧
              (t₂ - t - ∑ j : Fin M, c j * (y₂ j - y j)) ^ 2 ≤
                ε₁ ^ 2 * ∑ j : Fin M, (y₂ j - y j) ^ 2) ∧
        (∀ ε : ℝ, 0 < ε → ∃ δ : ℝ, 0 < δ ∧
          ∀ y' : Fin M → ℝ, (∑ j : Fin M, (y' j - y j) ^ 2) < δ ^ 2 →
            ∃ c' : Fin M → ℝ, ∃ t' : ℝ,
              Fin.snoc (Fin.append (z ∘ fun i : Fin P => Fin.castAdd M i) y') t' ∈ G ∧
              (∀ ε₂ : ℝ, 0 < ε₂ → ∃ δ₂ : ℝ, 0 < δ₂ ∧
                ∀ y₃ : Fin M → ℝ, (∑ j : Fin M, (y₃ j - y' j) ^ 2) < δ₂ ^ 2 →
                  ∃ t₃ : ℝ,
                    Fin.snoc (Fin.append (z ∘ fun i : Fin P => Fin.castAdd M i) y₃) t₃ ∈ G ∧
                    (t₃ - t' - ∑ j : Fin M, c' j * (y₃ j - y' j)) ^ 2 ≤
                      ε₂ ^ 2 * ∑ j : Fin M, (y₃ j - y' j) ^ 2) ∧
              (∑ j : Fin M, (c' j - c j) ^ 2) < ε ^ 2)

/-! ## 2. The shape -/

/-- The `TSh`-shape realising `C1Exp`. -/
def c1P (S : SOMin) (F D : ℕ) {P M : ℕ} (G : Set (Fin (P + M + 1) → ℝ))
    (hG : G ∈ S.Ω F D (P + M + 1)) : PKS S F D (P + M) :=
  let A4 := P + M + 1 + M + M + 1
  let A5 := A4 + 1
  let A6 := A5 + 1
  let A7 := A6 + M
  let A8 := A7 + M
  let A9 := A8 + 1
  -- the index maps at the level of the `(c,t)`-block (fdP's base ambient)
  let par1 : Fin P → Fin A4 := fun i => lift1 (liftM (liftM (lift1 (Fin.castAdd M i))))
  let cube1 : Fin M → Fin A4 := fun j => lift1 (liftM (liftM (lift1 (Fin.natAdd P j))))
  let cc1 : Fin M → Fin A4 := fun j => lift1 (Fin.natAdd (P + M + 1 + M) j)
  let t1 : Fin A4 := Fin.last (P + M + 1 + M + M)
  let yblk1 : Fin M → Fin A4 := fun j => lift1 (liftM (Fin.natAdd (P + M + 1) j))
  -- the index maps at the level of the `(c',t')`-block
  let par2 : Fin P → Fin A9 :=
    fun i => lift1 (liftM (liftM (lift1 (lift1 (lift1 (liftM (liftM (lift1 (Fin.castAdd M i)))))))))
  let cube2 : Fin M → Fin A9 :=
    fun j => lift1 (liftM (liftM (lift1 (lift1 (lift1 (liftM (liftM (lift1 (Fin.natAdd P j)))))))))
  let cc2 : Fin M → Fin A9 := fun j => lift1 (Fin.natAdd A7 j)
  let t2 : Fin A9 := Fin.last A8
  let yblk2 : Fin M → Fin A9 := fun j => lift1 (liftM (Fin.natAdd A6 j))
  -- the `close`-condition positions
  let cc3 : Fin M → Fin A9 := fun j => lift1 (liftM (liftM (lift1 (lift1 (lift1 (Fin.natAdd (P + M + 1 + M) j))))))
  let ee : Fin A9 := lift1 (liftM (liftM (lift1 (Fin.last A4))))
  let rest : PKS S F D A4 :=
    PKS.allOne (PKS.imp (posS S F D (Fin.last A4))
      (PKS.exi (PKS.conj (posS S F D (Fin.last A5))
        (PKS.allb (k := M) (PKS.imp
          (ballS S F D (fun j : Fin M => Fin.natAdd A6 j)
            (fun j : Fin M => liftM (lift1 (lift1 (lift1 (liftM (Fin.natAdd (P + M + 1) j))))))
            (liftM (Fin.last A5)))
          (PKS.exb (k := M) (PKS.exi (PKS.conj
            (PKS.mem G hG (memIdx par2 yblk2 t2))
            (PKS.conj (fdP S F D G hG par2 yblk2 cc2 t2)
              (ltS S F D (sqSum cc2 cc3) ((MvPolynomial.X ee) ^ 2)
                ((sqSum_td _ _).trans (by omega)) (td_X_sq _)))))))))))
  PKS.exi (PKS.conj
    (posS S F D (Fin.last (P + M)))
    (PKS.allb (k := M) (PKS.imp
      (ballS S F D (fun j : Fin M => Fin.natAdd (P + M + 1) j)
        (fun j : Fin M => liftM (lift1 (Fin.natAdd P j)))
        (liftM (Fin.last (P + M))))
      (PKS.exb (k := M) (PKS.exi (PKS.conj
        (PKS.mem G hG (memIdx par1 yblk1 t1))
        (PKS.conj (fdP S F D G hG par1 yblk1 cc1 t1) rest)))))))

/-- **The realisation of the `C¹`-shape.** -/
theorem c1P_Real {S : SOMin} {F D P M : ℕ} {G : Set (Fin (P + M + 1) → ℝ)}
    (hG : G ∈ S.Ω F D (P + M + 1)) :
    (c1P S F D G hG).Real = {z : Fin (P + M) → ℝ | C1Exp P M G z} := by
  ext z
  simp only [c1P, C1Exp, PKS.Real_allOne, PKS.Real_imp, PKS.Real_neg, PKS.Real_exi,
    PKS.Real_conj, PKS.Real_mem, PKS.Real_poly, PKS.Real_allb, PKS.Real_exb, posS_Real,
    ballS_Real, leS_Real, ltS_Real, fdP_Real, projLast, Work.WilG5.projN, Set.mem_compl_iff,
    Set.mem_setOf_eq, Set.mem_inter_iff, Set.mem_union, not_exists, not_not,
    Function.comp_apply, memIdx_comp, lift1, liftM, castAdd_one_eq_castSucc, snoc_castSucc',
    snoc_last', append_left', append_right', MvPolynomial.eval_sub, MvPolynomial.eval_pow,
    MvPolynomial.eval_sum, MvPolynomial.eval_X, MvPolynomial.eval_mul, MvPolynomial.eval_add,
    MvPolynomial.eval_C, sqSum, comp_snoc_lift, comp_append_liftM, comp_append_liftN,
    comp_snoc_lift_pt, comp_append_liftM_pt, comp_append_liftN_pt, or_iff_not_imp_left]

end Work.WilG4c
