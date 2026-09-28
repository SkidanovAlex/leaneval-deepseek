import Mathlib
import Submission.Work.HP.Defs
import Submission.Work.HP.PairsAux
import Submission.Work.Q44Geom.defs
import Submission.Work.Q44Geom.levels
import Submission.Work.Q44Geom.pairs
import Submission.Work.Q44Geom.complBasis
import Submission.Work.Q44Geom.uniqueDirection
import Submission.Work.Q44Geom.isSolIff
import Submission.Work.Q44Geom.levelHom
import Submission.Work.Q44Geom.gcdOne
import Submission.Work.Q44Geom.planeBound
import Submission.Work.Q44Geom.formOfHom
import Submission.Work.Q44Geom.planeBoundFin
import Submission.Work.Q44Geom.formOfHom
import Submission.Work.Q44Geom.planeBoundFin
import Submission.Work.Q44Geom.gcdOne

/-!
# `Work.Q44Geom.planes44`

The number of `3`-dimensional rational linear subspaces `P ⊆ ℚ⁵` which contain two fixed
linearly independent vectors `b₁, b₂` and are contained in the zero locus of an irreducible
quartic form `f = formOf 4 4 c` is bounded by an absolute constant, *provided* `f` is not
invariant under translations by the plane `ℓ = span(b₁,b₂)`.

## Architecture

`V = ℚ⁵`, `ℓ = span{b₁, b₂}`, `f = formOf 4 4 c` homogeneous of degree `4` (`formOf_isHomogeneous`).

* `complBasis`: pick `w : Fin 3 → V` with `(w, b₁, b₂)` a basis of `V`; write `W = span w`.
* `uniqueDirection`: for `P ⊇ {b₁,b₂}` with `finrank = 3` there is a *unique* `1`-dimensional
  `L ⊆ ℚ³` with `P = span{b₁,b₂} ⊔ toV w L`.  This makes `P ↦ L` injective.
* `isSolIff`: if `f` vanishes on `ℓ`, then `f` vanishes on `ℓ + ℚ (Σ p_a w_a)` iff all level
  forms `levelForm w b₁ b₂ f ![i,j]` with `i + j ≤ 3` vanish at `p`.
* `levelHom`: those level forms are homogeneous of degree `4 - (i+j)`.
* `gcdOne`: no nonconstant form divides all of them (else `f` is reducible or invariant, both
  excluded by the hypotheses).
* `planeBound`: forms in `ℚ[Fin 3]` of degree `≤ 4` with no common nonconstant divisor have at
  most `B` common rational points of `P²`.

Putting these together bounds `#F`.
-/

set_option autoImplicit false
set_option linter.unusedVariables false
noncomputable section

open MvPolynomial

namespace Work.Q44Geom

/-- The `10` level forms of degree `≤ 3`, indexed by the pairs `(i,j)` with `i + j ≤ 3`. -/
def levelFamily (b₁ b₂ : Fin 5 → ℚ) (w : Fin 3 → Fin 5 → ℚ) (f : MvPolynomial (Fin 5) ℚ) :
    {q : Fin 4 × Fin 4 // (q.1 : ℕ) + (q.2 : ℕ) ≤ 3} → MvPolynomial (Fin 3) ℚ :=
  fun q => levelForm w b₁ b₂ f ![(q.1.1 : ℕ), (q.1.2 : ℕ)]

/-- `planeBound` with an arbitrary finite index type, allowing identically vanishing members
(which impose no condition and are compatible with the divisibility hypothesis, since every
form divides `0`). -/
theorem planeBound' (B : ℕ)
    (hB : ∀ (n : ℕ) (G : Fin n → MvPolynomial (Fin 3) ℚ),
      (∀ i, G i ≠ 0) →
      (∀ i, ∃ d : ℕ, d ≤ 4 ∧ (G i).IsHomogeneous d) →
      (∀ h : MvPolynomial (Fin 3) ℚ, (∀ i, h ∣ G i) → IsUnit h) →
      {L : Submodule ℚ (Fin 3 → ℚ) | Module.finrank ℚ L = 1 ∧
        ∀ x ∈ L, ∀ i, MvPolynomial.eval x (G i) = 0}.Finite ∧
      {L : Submodule ℚ (Fin 3 → ℚ) | Module.finrank ℚ L = 1 ∧
        ∀ x ∈ L, ∀ i, MvPolynomial.eval x (G i) = 0}.ncard ≤ B)
    (ι : Type) [Fintype ι] (G : ι → MvPolynomial (Fin 3) ℚ)
    (hdeg : ∀ i, ∃ d : ℕ, d ≤ 4 ∧ (G i).IsHomogeneous d)
    (hgcd : ∀ h, (∀ i, h ∣ G i) → IsUnit h) :
    {L : Submodule ℚ (Fin 3 → ℚ) | Module.finrank ℚ L = 1 ∧
      ∀ x ∈ L, ∀ i, MvPolynomial.eval x (G i) = 0}.Finite ∧
    {L : Submodule ℚ (Fin 3 → ℚ) | Module.finrank ℚ L = 1 ∧
      ∀ x ∈ L, ∀ i, MvPolynomial.eval x (G i) = 0}.ncard ≤ B :=
  planeBoundFin B hB ι G hdeg hgcd

theorem planes44 :
    ∃ C : ℝ, 0 < C ∧ ∀ (c : Work.HP.Mon 4 4 → ℤ), Work.HP.formOf 4 4 c ≠ 0 →
      Irreducible (Work.HP.formOf 4 4 c) →
      ∀ (b₁ b₂ : Fin 5 → ℚ), b₁ ≠ 0 → b₂ ≠ 0 → LinearIndependent ℚ ![b₁, b₂] →
      MvPolynomial.eval b₁ (Work.HP.formOf 4 4 c) = 0 →
      MvPolynomial.eval b₂ (Work.HP.formOf 4 4 c) = 0 →
      (¬ ∀ (a b : ℚ) (x : Fin 5 → ℚ),
          MvPolynomial.eval (x + a • b₁ + b • b₂) (Work.HP.formOf 4 4 c)
            = MvPolynomial.eval x (Work.HP.formOf 4 4 c)) →
      ∀ (F : Set (Submodule ℚ (Fin 5 → ℚ))), F ⊆ {P : Submodule ℚ (Fin 5 → ℚ) |
          Module.finrank ℚ P = 3 ∧ b₁ ∈ P ∧ b₂ ∈ P ∧
          (∀ x ∈ P, MvPolynomial.eval x (Work.HP.formOf 4 4 c) = 0)} → F.Finite ∧
        (F.ncard : ℝ) ≤ C := by
  obtain ⟨B, hB⟩ := planeBound
  refine ⟨(B : ℝ) + 1, by positivity, ?_⟩
  intro c hf0 hfirr b₁ b₂ hb1 hb2 hbind hfb1 hfb2 hnd F hFsub
  by_cases hℓ : ∀ u : Fin 2 → ℚ,
      MvPolynomial.eval (u 0 • b₁ + u 1 • b₂) (Work.HP.formOf 4 4 c) = 0
  · -- **Main case**: `f` vanishes on `ℓ = span{b₁,b₂}`
    obtain ⟨w, hw, hwspan⟩ := complBasis b₁ b₂ hbind
    have hfhom : (Work.HP.formOf 4 4 c).IsHomogeneous 4 := formOfHom c
    -- the ten level forms have no common nonconstant divisor
    have hgcd : ∀ h : MvPolynomial (Fin 3) ℚ,
        (∀ q : {q : Fin 4 × Fin 4 // (q.1 : ℕ) + (q.2 : ℕ) ≤ 3},
          h ∣ levelFamily b₁ b₂ w (Work.HP.formOf 4 4 c) q) → IsUnit h := by
      intro h hh
      refine gcdOne b₁ b₂ w hw hwspan _ hfhom hfirr hnd hℓ h ?_
      intro i hi j hj hij
      have := hh ⟨(⟨i, Finset.mem_range.mp hi⟩, ⟨j, Finset.mem_range.mp hj⟩), by simpa using hij⟩
      simpa [levelFamily] using this
    -- and they are homogeneous of degree at most four
    have hdeg : ∀ q : {q : Fin 4 × Fin 4 // (q.1 : ℕ) + (q.2 : ℕ) ≤ 3},
        ∃ d : ℕ, d ≤ 4 ∧ (levelFamily b₁ b₂ w (Work.HP.formOf 4 4 c) q).IsHomogeneous d := by
      intro q
      have h1 : (q.1.1 : ℕ) ≤ 3 := Nat.le_of_lt_succ q.1.1.isLt
      have h2 : (q.1.2 : ℕ) ≤ 3 := Nat.le_of_lt_succ q.1.2.isLt
      have h3 : (q.1.1 : ℕ) + (q.1.2 : ℕ) ≤ 3 := by simpa using q.2
      refine ⟨4 - ((q.1.1 : ℕ) + (q.1.2 : ℕ)), by omega, ?_⟩
      simpa [levelFamily] using
        levelHom w b₁ b₂ (Work.HP.formOf 4 4 c) hfhom ![((q.1.1 : ℕ)), ((q.1.2 : ℕ))]
          (by simp only [Matrix.cons_val_zero, Matrix.cons_val_one]; omega)
    -- the directions on which all level forms vanish are finite and at most `B` in number
    obtain ⟨hfin, hbnd⟩ :=
      planeBound' B hB {q : Fin 4 × Fin 4 // (q.1 : ℕ) + (q.2 : ℕ) ≤ 3}
        (levelFamily b₁ b₂ w (Work.HP.formOf 4 4 c)) hdeg hgcd
    set S : Set (Submodule ℚ (Fin 3 → ℚ)) :=
      {L | Module.finrank ℚ L = 1 ∧
        ∀ x ∈ L, ∀ q : {q : Fin 4 × Fin 4 // (q.1 : ℕ) + (q.2 : ℕ) ≤ 3},
          MvPolynomial.eval x (levelFamily b₁ b₂ w (Work.HP.formOf 4 4 c) q) = 0} with hS
    -- every plane of `F` determines a unique direction in `S`
    have hmaps : ∀ P ∈ F, ∃ L ∈ S, P = Submodule.span ℚ
        ({b₁, b₂} ∪ Set.range (fun p : L => toV w (p : Fin 3 → ℚ))) := by
      intro P hP
      obtain ⟨hr, hb1', hb2', hvanish⟩ := hFsub hP
      obtain ⟨L, hLp, -⟩ := uniqueDirection b₁ b₂ w hw hwspan P hb1' hb2' hr
      refine ⟨L, ⟨hLp.1, ?_⟩, hLp.2⟩
      intro x hx q
      have hmem : toV w x ∈ P := by
        rw [hLp.2]
        exact Submodule.subset_span (Or.inr ⟨⟨x, hx⟩, rfl⟩)
      have hsub : ∀ u : Fin 2 → ℚ,
          MvPolynomial.eval (substPoint w b₁ b₂ x u) (Work.HP.formOf 4 4 c) = 0 := by
        intro u
        have hpt : substPoint w b₁ b₂ x u = toV w x + (u 0 • b₁ + u 1 • b₂) := by
          funext i
          simp only [substPoint, Pi.add_apply, Pi.smul_apply, toV_apply, Finset.sum_apply]
          have hs : (∑ a : Fin 3, x a * w a i) = ∑ a : Fin 3, w a i * x a :=
            Finset.sum_congr rfl fun a _ => mul_comm (x a) (w a i)
          rw [hs]
          ring
        rw [hpt]
        exact hvanish _ (P.add_mem hmem (P.add_mem (P.smul_mem (u 0) hb1') (P.smul_mem (u 1) hb2')))
      have := (isSolIff w b₁ b₂ (Work.HP.formOf 4 4 c) hfhom x hℓ).1 hsub
      exact this (q.1.1) (by simp) (q.1.2) (by simp) (by simpa using q.2)
    -- conclusion: `F` injects into the finite set `S`
    classical
    let fL : Submodule ℚ (Fin 5 → ℚ) → Submodule ℚ (Fin 3 → ℚ) :=
      fun P => if h : P ∈ F then Classical.choose (hmaps P h) else ⊥
    have hfL : ∀ P (hP : P ∈ F), fL P ∈ S ∧
        P = Submodule.span ℚ ({b₁, b₂} ∪ Set.range (fun p : fL P => toV w (p : Fin 3 → ℚ))) := by
      intro P hP
      have hval : fL P = Classical.choose (hmaps P hP) := by
        simp only [fL]
        rw [dif_pos hP]
      rw [hval]
      exact Classical.choose_spec (hmaps P hP)
    have hinj : Set.InjOn fL F := by
      intro P hP Q hQ heq
      rw [(hfL P hP).2, (hfL Q hQ).2, heq]
    have hsub : F ⊆ fL ⁻¹' S := fun P hP => (hfL P hP).1
    have hfinS : S.Finite := hfin
    refine ⟨?_, ?_⟩
    · exact (hfinS.subset (Set.image_subset_iff.mpr hsub)).of_finite_image hinj
    · have hbd : F.ncard ≤ B := by
        calc F.ncard ≤ (fL '' F).ncard := hinj.ncard_image.symm.le
          _ ≤ S.ncard := Set.ncard_le_ncard (Set.image_subset_iff.mpr hsub) hfinS
          _ ≤ B := hbnd
      have : (F.ncard : ℝ) ≤ (B : ℝ) := by exact_mod_cast hbd
      linarith
  · -- `f` does not vanish on `ℓ`, so no `P ⊇ {b₁,b₂}` with `f|_P = 0` exists
    have hempty : F = ∅ := by
      rw [Set.eq_empty_iff_forall_notMem]
      intro P hP
      obtain ⟨hr, hb1', hb2', hvanish⟩ := hFsub hP
      obtain ⟨u, hu⟩ := not_forall.mp hℓ
      exact hu (hvanish _ (P.add_mem (P.smul_mem (u 0) hb1') (P.smul_mem (u 1) hb2')))
    refine ⟨?_, ?_⟩
    · rw [hempty]; exact Set.finite_empty
    · rw [hempty]
      simp only [Set.ncard_empty, Nat.cast_zero]
      positivity

end Work.Q44Geom
