import Submission.Work.Stems.Hur2c.PsiLin_degen_cycle
import Submission.Work.RatHurewicz.cubicalBridgeDeg
import Submission.Work.Stems.Hur2b.cubD_comp_cubD

/-!
# Injectivity of the degree-`2` Hurewicz map (cubical proof)

**Step (5)** of `Submission/Work/Stems/Hur2c/STATUS.md`: if `X` is simply connected and the
Hurewicz image of `a ∈ π₂(X,x₀)` vanishes, then `a = 1`.

The input is the chain-level bridge `Work.RatHurewicz.cubicalBridgeDeg`: for a based `2`-cube `p`
with vanishing Hurewicz image there is a `3`-chain `c` with
`∂c ∓ single p.1 1 ∈ Deg 2 X`; that difference is a degenerate `2`-**cycle** (a based cube has
`∂ (single p.1 1) = 0`, and `∂ ∘ ∂ = 0`), so `(4b)`
(`Work.Stems.Hur2c.PsiLin_eq_zero_of_degen_cycle`) kills it, while `(Z)`
(`Work.Stems.Hur2.PsiLin_single_based`) identifies `Ψ (single p.1 1)` with `⟦p⟧` and `(Y)`
(`PsiLin_cubD_eq_zero` below) kills `Ψ (∂c)`.
-/

open scoped unitInterval Topology

namespace Work.Stems

open Work.Stems.Cubical
open Work.Stems.Hur2

noncomputable section

variable {X : Type} [TopologicalSpace X] [SimplyConnectedSpace X]

/-! ## `(Y)` for arbitrary `3`-chains -/

/-- `(Y)` extended by linearity: `Ψ` kills the boundary of every cubical `3`-chain. -/
theorem PsiLin_cubD_eq_zero (x₀ : X) (c : Cub 3 X) :
    Work.Stems.Hur2.PsiLin x₀ (cubD 2 X c) = 0 := by
  refine Finsupp.induction_linear
    (motive := fun c => Work.Stems.Hur2.PsiLin x₀ (cubD 2 X c) = 0) c ?_ ?_ ?_
  · simp
  · intro f g hf hg
    rw [map_add, map_add, hf, hg, add_zero]
  · intro a k
    rw [show Finsupp.single a k = k • Finsupp.single a (1 : ℤ) from by
      rw [Finsupp.smul_single', mul_one]]
    simp only [map_smul]
    rw [Work.Stems.Hur2b.PsiLin_cubD_single x₀ a, smul_zero]

/-- `∂ ∘ ∂ = 0` at the level of elements. -/
theorem cubD_comp_cubD_apply (n : ℕ) (c : Cub (n + 2) X) :
    cubD n X (cubD (n + 1) X c) = 0 := by
  have h := congrArg (fun (f : Cub (n + 2) X →ₗ[ℤ] Cub n X) => f c)
    (Work.Stems.Hur2b.cubD_comp_cubD n (X := X))
  simpa only [LinearMap.comp_apply, LinearMap.zero_apply] using h

/-! ## The boundary of a based cube vanishes -/

/-- A face of a *based* `2`-cube is the constant cube at the base point. -/
theorem faceCube_based_const (x₀ : X) (p : GenLoop (Fin 2) X x₀) (i : Fin 2)
    (b : unitInterval) (hb : b = 0 ∨ b = 1) :
    faceCube i b p.1 = ContinuousMap.const (IC 1) x₀ := by
  ext t
  refine p.2 (faceCM i b t) ?_
  rw [Cube.boundary]
  rcases hb with rfl | rfl
  · exact ⟨i, Or.inl (Work.Stems.Hur2c.faceCM_frozen i 0 t)⟩
  · exact ⟨i, Or.inr (Work.Stems.Hur2c.faceCM_frozen i 1 t)⟩

/-- **A based `2`-cube is a cycle.** -/
theorem cubD_single_based (x₀ : X) (p : GenLoop (Fin 2) X x₀) :
    cubD 1 X (Finsupp.single p.1 1) = 0 := by
  rw [cubD_single, Fin.sum_univ_two]
  rw [faceCube_based_const x₀ p 0 0 (Or.inl rfl),
    faceCube_based_const x₀ p 0 1 (Or.inr rfl),
    faceCube_based_const x₀ p 1 0 (Or.inl rfl),
    faceCube_based_const x₀ p 1 1 (Or.inr rfl)]
  simp

/-! ## Injectivity -/

/-- `(Z)` converts the vanishing of `Ψ (single p.1 1)` into `⟦p⟧ = 1`. -/
theorem hpsi_eq_one (x₀ : X) (a : HomotopyGroup (Fin 2) X x₀)
    (h : Work.Stems.Hur2.PsiLin x₀ (Finsupp.single (Quotient.out a).1 1) = 0) : a = 1 := by
  letI : Group (HomotopyGroup (Fin 2) X x₀) := HomotopyGroup.group (Fin 2)
  let p : GenLoop (Fin 2) X x₀ := Quotient.out a
  let b : HomotopyGroup (Fin 2) X x₀ := Quotient.mk _ p
  have hb : b = a := Quotient.out_eq a
  have hZ : Work.Stems.Hur2.PsiLin x₀ (Finsupp.single p.1 1) = Additive.ofMul b :=
    Work.Stems.Hur2.PsiLin_single_based x₀ p
  have h0 : Additive.ofMul b = 0 := hZ.symm.trans h
  have h1 : b = 1 := by simpa using h0
  rw [← hb]
  exact h1

/-- **The degree-`2` Hurewicz map is injective** for a simply connected space. -/
theorem hurewiczMapN_two_injective (x₀ : X) (a : HomotopyGroup (Fin 2) X x₀)
    (ha : hurewiczMapN 2 (by norm_num) x₀ a = 0) : a = 1 := by
  obtain ⟨c, hc | hc⟩ :=
    Work.RatHurewicz.cubicalBridgeDeg 2 (by norm_num) x₀ (Quotient.out a)
      (by
        rw [show (Quotient.mk _ (Quotient.out a) : HomotopyGroup (Fin 2) X x₀) = a
          from Quotient.out_eq a]
        exact ha)
  · -- `∂c - single p 1 ∈ Deg 2 X`
    have hcomp : cubD 1 X (cubD 2 X c) = 0 := cubD_comp_cubD_apply 1 c
    have hcyc : cubD 1 X (cubD 2 X c - Finsupp.single (Quotient.out a).1 1) = 0 := by
      rw [map_sub, hcomp, cubD_single_based x₀ (Quotient.out a), sub_zero]
    have hpsi : Work.Stems.Hur2.PsiLin x₀ (Finsupp.single (Quotient.out a).1 1) = 0 := by
      have h0 := Work.Stems.Hur2c.PsiLin_eq_zero_of_degen_cycle_of_Deg x₀
        (cubD 2 X c - Finsupp.single (Quotient.out a).1 1) hc hcyc
      rw [map_sub, PsiLin_cubD_eq_zero, zero_sub, neg_eq_zero] at h0
      exact h0
    exact hpsi_eq_one x₀ a hpsi
  · -- `∂c + single p 1 ∈ Deg 2 X`
    have hcomp : cubD 1 X (cubD 2 X c) = 0 := cubD_comp_cubD_apply 1 c
    have hcyc : cubD 1 X (cubD 2 X c + Finsupp.single (Quotient.out a).1 1) = 0 := by
      rw [map_add, hcomp, cubD_single_based x₀ (Quotient.out a), zero_add]
    have hpsi : Work.Stems.Hur2.PsiLin x₀ (Finsupp.single (Quotient.out a).1 1) = 0 := by
      have h0 := Work.Stems.Hur2c.PsiLin_eq_zero_of_degen_cycle_of_Deg x₀
        (cubD 2 X c + Finsupp.single (Quotient.out a).1 1) hc hcyc
      rw [map_add, PsiLin_cubD_eq_zero, zero_add] at h0
      exact h0
    exact hpsi_eq_one x₀ a hpsi

end

end Work.Stems
