import Mathlib
import Submission.Work.Kunneth.Cross
import Submission.Work.Kunneth.crossCochain_apply
import Submission.Work.Cohomology.Kunneth.ezEval
import Submission.Work.Cohomology.CupRing

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 400000

/-!
# The cross product of two cocycles is a cocycle

For simplicial sets `X` and `Y`, the cross product `Work.Kunneth.crossCochain X Y p q α β` of a
`p`-cochain `α` of `X` and a `q`-cochain `β` of `Y` is the `(p+q)`-cochain of `X ⊗ Y` given by
`(α × β)(σ,τ) = α(σ)·β(τ)`.  Its coboundary is given by the Leibniz rule
`δ(α × β) = δα × β + (-1)^p α × δβ`; in particular the cross product of two *cocycles* is again
a cocycle.  That is the statement proved here:

`Work.Kunneth.crossCochain_isCocycle`.

The proof is the standard one, carried out on the generators of the simplicial chains of
`X ⊗ Y` (as in `Work.Cohomology.cupLeibniz` for the cup product): evaluating the coboundary at an
`(p+q+1)`-simplex `z = (σ,τ)` writes `δ(α × β)(z)` as the alternating sum of the values of
`α × β` on the faces of `z`; splitting that sum into the faces with index `≤ p` and those with
index `≥ p+1` and using the face identities `E1`–`E6` of `Work.Cohomology.cupLeibniz` (applied to
`σ` in `X` for the front faces and to `τ` in `Y` for the back faces) turns the two blocks into the
alternating sums of `α` on the front `(p+1)`-face of `σ` and of `β` on the back `(q+1)`-face of
`τ`, which vanish because `α` and `β` are cocycles.
-/

set_option autoImplicit false
set_option maxHeartbeats 1600000

open CategoryTheory CategoryTheory.Limits HomologicalComplex
open scoped MonoidalCategory TensorProduct Simplicial

namespace Work.Kunneth

noncomputable section

attribute [-instance] AddCommGroup.toIntModule

variable (X Y : SSet)

@[simp] lemma sProd_δ_fst {n : ℕ} (i : Fin (n+2)) (z : (sProd X Y) _⦋n+1⦌) :
    ((sProd X Y).δ i z).1 = X.δ i z.1 := rfl

@[simp] lemma sProd_δ_snd {n : ℕ} (i : Fin (n+2)) (z : (sProd X Y) _⦋n+1⦌) :
    ((sProd X Y).δ i z).2 = Y.δ i z.2 := rfl

lemma backFaceLE_eq_backFace (Y : SSet) (p q : ℕ) (h : q ≤ p+q) (τ : Y _⦋p+q⦌) :
    backFaceLE Y q (p+q) h τ = Work.Cohomology.backFace Y p q τ := by
  have hHom : backInclLE q (p+q) h = Work.Cohomology.backIncl p q := by
    apply SimplexCategory.Hom.ext
    apply OrderHom.ext
    funext j
    apply Fin.ext
    show p + q - q + (j : ℕ) = p + (j : ℕ)
    omega
  simp only [backFaceLE, Work.Cohomology.backFace]
  rw [hHom]

theorem crossCochain_apply' (p q : ℕ)
    (α : Work.Cohomology.Cochain ℤ X p) (β : Work.Cohomology.Cochain ℤ Y q)
    (z : (sProd X Y) _⦋p+q⦌) :
    Work.Cohomology.genEval ℤ (sProd X Y) (crossCochain X Y p q α β) z
      = Work.Cohomology.genEval ℤ X α
          (Work.Cohomology.frontFace X p (p+q) (by omega) z.1) *
        Work.Cohomology.genEval ℤ Y β (Work.Cohomology.backFace Y p q z.2) := by
  rw [crossCochain_apply, backFaceLE_eq_backFace]

lemma sum_genEval_of_cocycle {R : Type} [CommRing R] {X : SSet} {k : ℕ}
    (γ : Work.Cohomology.Cochain R X k) (hγ : Work.Cohomology.cochainDiff R X γ = 0)
    (σ : X _⦋k+1⦌) :
    ∑ i : Fin (k+2), (-1:R) ^ (i:ℕ) * Work.Cohomology.genEval R X γ (X.δ i σ) = 0 := by
  have h := congrArg (fun (f : Work.Cohomology.Cochain R X (k+1)) =>
    Work.Cohomology.genEval R X f σ) hγ
  rw [Work.Cohomology.genEval_cochainDiff] at h
  simpa only [Work.Cohomology.genEval, LinearMap.zero_apply] using h

theorem crossCochain_isCocycle (X Y : SSet) (p q : ℕ)
    (α : Work.Cohomology.Cochain ℤ X p) (β : Work.Cohomology.Cochain ℤ Y q)
    (hα : Work.Cohomology.cochainDiff ℤ X α = 0) (hβ : Work.Cohomology.cochainDiff ℤ Y β = 0) :
    Work.Cohomology.cochainDiff ℤ (Work.Kunneth.sProd X Y)
      (Work.Kunneth.crossCochain X Y p q α β) = 0 := by
  apply Work.Cohomology.genEval_ext
  intro z
  have hz : Work.Cohomology.genEval ℤ (sProd X Y)
      (0 : Work.Cohomology.Cochain ℤ (sProd X Y) (p+q+1)) z = 0 := by
    simp [Work.Cohomology.genEval]
  rw [hz, Work.Cohomology.genEval_cochainDiff]
  let F : X _⦋p+1⦌ := Work.Cohomology.frontFace X (p+1) (p+q+1) (by omega) z.1
  let B : Y _⦋q⦌ := Work.Cohomology.backFace Y (p+1) q (Y.map (Work.Cohomology.shiftHom p q).op z.2)
  let Fr : X _⦋p⦌ := Work.Cohomology.frontFace X p (p+(q+1)) (by omega) z.1
  let tau' : Y _⦋q+1⦌ := Work.Cohomology.backFace Y p (q+1) z.2
  let dface : ℕ → (sProd X Y) _⦋p+q⦌ :=
    fun k => if h : k < p+q+2 then (sProd X Y).δ ⟨k,h⟩ z else (sProd X Y).δ 0 z
  let G : ℕ → ℤ := fun k => (-1:ℤ)^k *
    (Work.Cohomology.genEval ℤ X α
        (Work.Cohomology.frontFace X p (p+q) (by omega) (dface k).1) *
      Work.Cohomology.genEval ℤ Y β (Work.Cohomology.backFace Y p q (dface k).2))
  let dF : ℕ → X _⦋p⦌ := fun i => if h : i < p+2 then X.δ ⟨i,h⟩ F else X.δ 0 F
  let Hsum : ℕ → ℤ := fun i => (-1:ℤ)^i *
    (Work.Cohomology.genEval ℤ X α (dF i) * Work.Cohomology.genEval ℤ Y β B)
  let dtau : ℕ → Y _⦋q⦌ := fun j => if h : j < q+2 then Y.δ ⟨j,h⟩ tau' else Y.δ 0 tau'
  let Esum : ℕ → ℤ := fun j => (-1:ℤ)^j *
    (Work.Cohomology.genEval ℤ X α Fr * Work.Cohomology.genEval ℤ Y β (dtau j))
  have hL : ∑ i : Fin (p+q+2), (-1:ℤ)^(i:ℕ) *
        Work.Cohomology.genEval ℤ (sProd X Y) (crossCochain X Y p q α β)
          ((sProd X Y).δ i z)
      = ∑ k ∈ Finset.range (p+q+2), G k := by
    refine (Finset.sum_congr rfl ?_).trans (Fin.sum_univ_eq_sum_range G (p+q+2))
    intro i _
    simp only [G, dface, dif_pos (by omega : (i:ℕ) < p+q+2), sProd_δ_fst, sProd_δ_snd]
    rw [crossCochain_apply']
    simp only [sProd_δ_fst, sProd_δ_snd]
  have hAtot : ∑ i ∈ Finset.range (p+2), Hsum i = 0 := by
    have hc := sum_genEval_of_cocycle (R := ℤ) α hα F
    have key : ∀ i : Fin (p+2), Hsum ↑i =
        ((-1:ℤ)^(i:ℕ) * Work.Cohomology.genEval ℤ X α (X.δ i F)) *
          Work.Cohomology.genEval ℤ Y β B := by
      intro i
      simp only [Hsum, dF, dif_pos i.isLt]
      ring
    rw [← Fin.sum_univ_eq_sum_range Hsum (p+2)]
    rw [Finset.sum_congr rfl (fun i _ => key i)]
    rw [← Finset.sum_mul, hc, zero_mul]
  have hBtot : ∑ j ∈ Finset.range (q+2), Esum j = 0 := by
    have hc := sum_genEval_of_cocycle (R := ℤ) β hβ tau'
    have key : ∀ j : Fin (q+2), Esum ↑j =
        Work.Cohomology.genEval ℤ X α Fr *
          ((-1:ℤ)^(j:ℕ) * Work.Cohomology.genEval ℤ Y β (Y.δ j tau')) := by
      intro j
      simp only [Esum, dtau, dif_pos j.isLt]
      ring
    rw [← Fin.sum_univ_eq_sum_range Esum (q+2)]
    rw [Finset.sum_congr rfl (fun j _ => key j)]
    rw [← Finset.mul_sum, hc, mul_zero]
  have hA : ∑ i ∈ Finset.range (p+1), Hsum i = -Hsum (p+1) := by
    have h := Finset.sum_range_succ Hsum (p+1)
    rw [hAtot] at h
    linarith
  have hB : ∑ j ∈ Finset.range (q+1), Esum (j+1) = -Esum 0 := by
    have h := Finset.sum_range_succ' Esum (q+1)
    rw [hBtot] at h
    linarith
  have hcancel : Hsum (p+1) + (-1:ℤ)^p * Esum 0 = 0 := by
    simp only [Hsum, Esum, dF, dtau, F, B, tau', Fr,
      dif_pos (by omega : p+1 < p+2), dif_pos (by omega : (0:ℕ) < q+2)]
    rw [Work.Cohomology.E5 p q (⟨p+1, by omega⟩ : Fin (p+2)) (by rfl) z.1,
        Work.Cohomology.E6 p q (⟨0, by omega⟩ : Fin (q+2)) (by rfl) (Work.Cohomology.shiftHom p q)
          (Work.Cohomology.shiftHom_val p q) z.2]
    rw [show ((-1:ℤ)^(p+1)) = -(-1:ℤ)^p by rw [pow_succ]; ring]
    ring
  have hG1 : ∀ k ∈ Finset.range (p+1), G k = Hsum k := by
    intro k hk
    simp only [Finset.mem_range] at hk
    simp only [G, Hsum, dface, dF, F, B,
      dif_pos (by omega : k < p+q+2), dif_pos (by omega : k < p+2),
      sProd_δ_fst, sProd_δ_snd]
    rw [Work.Cohomology.E1 p q (⟨k, by omega⟩ : Fin (p+q+2)) (by show k ≤ p; omega) z.1,
        Work.Cohomology.E2 p q (⟨k, by omega⟩ : Fin (p+q+2)) (by show k ≤ p; omega)
          (Work.Cohomology.shiftHom p q) (Work.Cohomology.shiftHom_val p q) z.2]
  have hG2 : ∀ k ∈ Finset.range (q+1), G ((p+1)+k) = (-1:ℤ)^p * Esum (k+1) := by
    intro k hk
    simp only [Finset.mem_range] at hk
    simp only [G, Esum, dface, dtau, Fr, tau',
      dif_pos (by omega : (p+1)+k < p+q+2), dif_pos (by omega : k+1 < q+2),
      sProd_δ_fst, sProd_δ_snd]
    rw [Work.Cohomology.E3 p q (⟨(p+1)+k, by omega⟩ : Fin (p+q+2))
          (by show (p+1) ≤ (p+1)+k; omega) z.1,
        Work.Cohomology.E4 p q (⟨(p+1)+k, by omega⟩ : Fin (p+q+2))
          (by show (p+1) ≤ (p+1)+k; omega)
          (⟨k+1, by omega⟩ : Fin (q+2)) (by show k+1 = ((p+1)+k) - p; omega) z.2]
    rw [show ((-1:ℤ)^((p+1)+k)) = (-1:ℤ)^p * ((-1:ℤ)^(k+1)) by
      rw [show (p+1)+k = p + (k+1) by omega, pow_add]]
    ring
  rw [hL]
  rw [show p+q+2 = (p+1)+(q+1) by omega, Finset.sum_range_add G (p+1) (q+1)]
  rw [Finset.sum_congr rfl hG1, Finset.sum_congr rfl hG2]
  rw [hA, ← Finset.mul_sum, hB]
  linear_combination -hcancel

end

end Work.Kunneth
