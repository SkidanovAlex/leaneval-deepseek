import Mathlib
import Submission.Work.Diff.EXT.ConnCov.RicFlip.OSubKit

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

/-!
# `Bnd1CompOSub`: the `Bnd1` shape is preserved by the composition with a one-atom substitution

Let `Φ : OSub a b ord` be a *one-atom substitution*: at the distinguished output slot `Φ.idx` the
`ord`-th covariant derivative of the connection difference is inserted, applied to the `ord + 2`
input slots `Φ.τ`, while every other output slot `j` is one of the input slots, `Φ.σ j`.

The claim proved here is the purely *multiplicative* bookkeeping of the word induction of the
connection flip: if a `b`-slot object `Θ` satisfies the bound

  `|Θ F x| ≤ C ∏_{j : Fin b} (1 + ‖F_j(x)‖)`

for every smooth tuple `F` (`Bnd1 Θ C`), and if the `δ`-tower of order `ord` satisfies

  `‖∇^{ord}δ(v, X, Z)(x)‖ ≤ V · (∏_i (1 + ‖v_i(x)‖)) (1 + ‖X(x)‖) (1 + ‖Z(x)‖)`

for every smooth tuple (`BndV (deltaTowerM G t ord) V`), then the composed object
`F ↦ Θ (Φ.eval G t F)` satisfies the same shape with constant `C (1 + V)`.

The mathematics is a partition of the slots: `(Φ.τ, Φ.σ ↾ {j ≠ idx})` is a bijection onto the `a`
input slots, so the product over the `a` input slots splits *exactly* into the product over the atom
slots and the product over the remaining output slots.  The factor `(1 + V)` pays for replacing the
single factor `1 + ‖Θ_slot‖` at `Φ.idx` by the atom bound, using that every factor is `≥ 1`.
-/

set_option linter.unusedSectionVars false
set_option maxHeartbeats 1600000

open LeanEval.Geometry.SphereTheorem Submission.Diff Submission.Diff.Alg
open scoped Manifold ContDiff Bundle Topology BigOperators
open Bundle ContDiff Set VectorField CovariantDerivative Metric
open Work.Diff.EXT.ATower (SmE)

namespace Work.Diff.EXT.ConnCov.RicFlip

/-! ## Elementary product facts -/

/-- A product of real numbers `≥ 1` is `≥ 1`.  (`Finset.one_le_prod` is only available for
`MulLeftMono` monoids, which `ℝ` is not.) -/
theorem one_le_prod_real {ι : Type*} {f : ι → ℝ} : ∀ (s : Finset ι), (∀ i ∈ s, 1 ≤ f i) →
    1 ≤ ∏ i ∈ s, f i := by
  classical
  intro s
  refine Finset.induction_on s ?_ ?_
  · intro _; simp
  · intro a s ha ih h
    rw [Finset.prod_insert ha]
    have hfa : 1 ≤ f a := h a (Finset.mem_insert_self a s)
    have hs : 1 ≤ ∏ i ∈ s, f i := ih (fun i hi => h i (Finset.mem_insert_of_mem hi))
    have h0 : (0 : ℝ) ≤ f a := by linarith
    have := mul_le_mul hfa hs (by norm_num : (0 : ℝ) ≤ 1) h0
    simpa using this

/-- Splitting a product over `Fin (ord + 2)` into the `ord` derivative slots and the two value
slots. -/
theorem prod_fin_ord_add_two {ord : ℕ} (w : Fin (ord + 2) → ℝ) :
    ∏ l : Fin (ord + 2), w l
      = (∏ i : Fin ord, w (Fin.castAdd 2 i)) * w (Fin.natAdd ord 0) * w (Fin.natAdd ord 1) := by
  rw [Fin.prod_univ_add, Fin.prod_univ_two, mul_assoc]

/-! ## The product bookkeeping of a one-atom substitution -/

namespace O

variable {a b ord : ℕ}

/-- Reindexing a product over the `a` input slots of a one-atom substitution by the bijection
`(Φ.τ, Φ.σ ↾ {j ≠ idx})`. -/
theorem prod_elim (Φ : OSub a b ord) (u : Fin a → ℝ) :
    ∏ i : Fin a, u i
      = (∏ l : Fin (ord + 2), u (Φ.τ l))
        * ∏ j : {j : Fin b // j ≠ Φ.idx}, u (Φ.σ j.1) := by
  have he : (∏ x : Fin (ord + 2) ⊕ {j : Fin b // j ≠ Φ.idx},
      u (Sum.elim Φ.τ (fun i : {i : Fin b // i ≠ Φ.idx} => Φ.σ i.1) x)) = ∏ i : Fin a, u i :=
    Equiv.prod_comp (Equiv.ofBijective _ Φ.bij) u
  rw [← he, Fintype.prod_sum_type]
  simp only [Sum.elim_inl, Sum.elim_inr]

/-- The same reindexing with the remaining slots written as `Finset.univ.erase Φ.idx`. -/
theorem prod_univ (Φ : OSub a b ord) (u : Fin a → ℝ) :
    (∏ l : Fin (ord + 2), u (Φ.τ l)) * (∏ j ∈ Finset.univ.erase Φ.idx, u (Φ.σ j))
      = ∏ i : Fin a, u i := by
  have h : ∏ j ∈ Finset.univ.erase Φ.idx, u (Φ.σ j)
      = ∏ j : {j : Fin b // j ≠ Φ.idx}, u (Φ.σ j.1) := by
    refine Finset.prod_bij
      (fun (j : Fin b) (hj : j ∈ Finset.univ.erase Φ.idx) =>
        (⟨j, (Finset.mem_erase.mp hj).1⟩ : {j : Fin b // j ≠ Φ.idx})) ?_ ?_ ?_ ?_
    · intro j hj; exact Finset.mem_univ _
    · intro j₁ h₁ j₂ h₂ heq; exact Subtype.ext_iff.mp heq
    · intro j _
      exact ⟨j.1, Finset.mem_erase.mpr ⟨j.2, Finset.mem_univ j.1⟩, Subtype.ext rfl⟩
    · intro j hj; rfl
  rw [h, ← prod_elim Φ u]

/-- **The product comparison for a one-atom substitution.**  If the output slot `Φ.idx` is bounded
by `(1+V)` times the product over the atom slots and every other output slot is *equal* to the
corresponding input slot, then the product over the outputs is bounded by `(1+V)` times the product
over the inputs. -/
theorem prod_le_mul_prod (Φ : OSub a b ord) (u : Fin a → ℝ) (gm : Fin b → ℝ)
    (hu : ∀ i, 1 ≤ u i)
    (hrest : ∀ j, j ≠ Φ.idx → gm j = u (Φ.σ j))
    {V : ℝ} (hV : 0 ≤ V)
    (hatom : gm Φ.idx ≤ (1 + V) * ∏ l : Fin (ord + 2), u (Φ.τ l)) :
    ∏ j : Fin b, gm j ≤ (1 + V) * ∏ i : Fin a, u i := by
  have hA0 : 0 ≤ ∏ l : Fin (ord + 2), u (Φ.τ l) :=
    Finset.prod_nonneg (fun l _ => by linarith [hu (Φ.τ l)])
  have hB0 : 0 ≤ ∏ j ∈ Finset.univ.erase Φ.idx, u (Φ.σ j) :=
    Finset.prod_nonneg (fun j _ => by linarith [hu (Φ.σ j)])
  have hBeq : ∏ j ∈ Finset.univ.erase Φ.idx, gm j
      = ∏ j ∈ Finset.univ.erase Φ.idx, u (Φ.σ j) :=
    Finset.prod_congr rfl (fun j hj => hrest j (Finset.mem_erase.mp hj).1)
  have hmul : gm Φ.idx * ∏ j ∈ Finset.univ.erase Φ.idx, u (Φ.σ j)
      ≤ ((1 + V) * ∏ l : Fin (ord + 2), u (Φ.τ l))
        * ∏ j ∈ Finset.univ.erase Φ.idx, u (Φ.σ j) :=
    mul_le_mul hatom le_rfl hB0 (mul_nonneg (by linarith) hA0)
  rw [← Finset.mul_prod_erase Finset.univ gm (Finset.mem_univ Φ.idx), hBeq]
  refine le_trans hmul (le_of_eq ?_)
  rw [mul_assoc, prod_univ]

end O

/-! ## The main theorem -/

theorem Bnd1CompOSub
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [CompleteSpace E]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I (⊤ : ℕ∞) M]
    [I.Boundaryless] [T2Space M]
    (hLC : Submission.Diff.LCSmooth I M)
    (G : ℝ → Submission.Diff.SMet I M) (t : ℝ) {a b ord : ℕ}
    (Φ : Work.Diff.EXT.ConnCov.RicFlip.O.OSub a b ord)
    {Θ : Work.Diff.EXT.ConnCov.AMB.Fam (I := I) (M := M) b} {C : ℝ} (hC : 0 ≤ C)
    (hΘ : Work.Diff.EXT.ConnCov.AMB.Bnd1 (I := I) (M := M) G t Θ C)
    {V : ℝ} (hV0 : 0 ≤ V)
    (hV : Work.Diff.EXT.ConnCov.AMB.BndV (I := I) (M := M) G t
      (Work.Diff.EXT.ConnCov.RicFlip.deltaTowerM G t ord) V) :
    Work.Diff.EXT.ConnCov.AMB.Bnd1 (I := I) (M := M) G t
      (fun F => Θ (Work.Diff.EXT.ConnCov.RicFlip.O.OSub.eval G t Φ F)) (C * (1 + V)) := by
  intro F x hF
  -- abbreviations for the two products
  set u : Fin a → ℝ := fun i => 1 + Real.sqrt ((G t).inner x (F i x) (F i x)) with hu
  set gm : Fin b → ℝ :=
    fun j => 1 + Real.sqrt ((G t).inner x ((Φ.eval G t F) j x) ((Φ.eval G t F) j x)) with hgm
  have hu1 : ∀ i, 1 ≤ u i := by
    intro i
    show (1 : ℝ) ≤ 1 + Real.sqrt ((G t).inner x (F i x) (F i x))
    have := Real.sqrt_nonneg ((G t).inner x (F i x) (F i x))
    linarith
  -- smoothness of the connection difference and of the atom
  have hbase : ∀ (w : Fin 0 → AMB.TF) (X Y : AMB.TF),
      SmE I M X → SmE I M Y → SmE I M (deltaBaseM G t w X Y) := by
    intro w X Y hX hY
    have h1 := ATower.lcOf_apply_smE hLC (G t) X Y hX hY
    have h2 := ATower.lcOf_apply_smE hLC (G 0) X Y hX hY
    exact h1.sub_section h2
  have hatomsm : SmE I M (O.atomEval G t Φ.τ F) :=
    smE_vtowerM hLC (G t) (deltaBaseM G t) hbase ord
      (fun l : Fin ord => F (Φ.τ (Fin.castAdd 2 l)))
      (F (Φ.τ (Fin.natAdd ord 0))) (F (Φ.τ (Fin.natAdd ord 1)))
      (fun l => hF _) (hF _) (hF _)
  have hHsm : ∀ j : Fin b, SmE I M ((Φ.eval G t F) j) := by
    intro j
    by_cases hj : j = Φ.idx
    · subst hj
      rw [O.OSub.eval_atom]
      exact hatomsm
    · rw [O.OSub.eval_slot Φ F hj]
      exact hF _
  have h1 := hΘ (Φ.eval G t F) x hHsm
  -- the product comparison
  have hprod : ∏ j : Fin b, gm j ≤ (1 + V) * ∏ i : Fin a, u i := by
    refine O.prod_le_mul_prod Φ u gm hu1 ?_ hV0 ?_
    · intro j hj
      show 1 + Real.sqrt ((G t).inner x ((Φ.eval G t F) j x) ((Φ.eval G t F) j x))
        = 1 + Real.sqrt ((G t).inner x (F (Φ.σ j) x) (F (Φ.σ j) x))
      rw [O.OSub.eval_slot Φ F hj]
    · -- the atom slot
      show 1 + Real.sqrt ((G t).inner x ((Φ.eval G t F) Φ.idx x) ((Φ.eval G t F) Φ.idx x))
        ≤ (1 + V) * ∏ l : Fin (ord + 2), u (Φ.τ l)
      rw [O.OSub.eval_atom]
      -- the atom bound, from `hV`
      have hVb2 : Real.sqrt ((G t).inner x (O.atomEval G t Φ.τ F x) (O.atomEval G t Φ.τ F x))
          ≤ V * ∏ l : Fin (ord + 2), u (Φ.τ l) := by
        have key : V * ∏ l : Fin (ord + 2), u (Φ.τ l)
            = V * (∏ i : Fin ord, (1 + Real.sqrt ((G t).inner x
                (F (Φ.τ (Fin.castAdd 2 i)) x) (F (Φ.τ (Fin.castAdd 2 i)) x))))
              * (1 + Real.sqrt ((G t).inner x (F (Φ.τ (Fin.natAdd ord 0)) x)
                  (F (Φ.τ (Fin.natAdd ord 0)) x)))
              * (1 + Real.sqrt ((G t).inner x (F (Φ.τ (Fin.natAdd ord 1)) x)
                  (F (Φ.τ (Fin.natAdd ord 1)) x))) := by
          simp only [hu, prod_fin_ord_add_two, mul_assoc]
        have h := hV (fun l : Fin ord => F (Φ.τ (Fin.castAdd 2 l)))
          (F (Φ.τ (Fin.natAdd ord 0))) (F (Φ.τ (Fin.natAdd ord 1)))
          (fun l => hF _) (hF _) (hF _) x
        rw [key]
        exact h
      have hP1 : 1 ≤ ∏ l : Fin (ord + 2), u (Φ.τ l) :=
        one_le_prod_real Finset.univ (fun l _ => hu1 (Φ.τ l))
      nlinarith [hVb2, hP1, hV0]
  -- assemble
  calc |Θ (Φ.eval G t F) x|
      ≤ C * ∏ j : Fin b, gm j := by simpa only [hgm] using h1
    _ ≤ C * ((1 + V) * ∏ i : Fin a, u i) := mul_le_mul_of_nonneg_left hprod hC
    _ = C * (1 + V) * ∏ i : Fin a, u i := by ring

end Work.Diff.EXT.ConnCov.RicFlip
