import Mathlib
import Submission.Commons.Lattice.SuccessiveMinima.exact_realization
import Submission.Commons.Lattice.SuccessiveMinima.positive

/-!
# Interior exclusion: short lattice points live in the span of a realising flag (shared commons)

If `v : Fin d → L` is a family of `d` independent lattice points with `‖vⱼ‖ ≤ λⱼ(L)` for
every `j` (a *realising* family of the successive minima, cf. `exact_realization`), then the
interior of the ball of radius `λℓ` contains no lattice point outside the flag subspace
spanned by the first `ℓ - 1` vectors: every `y ∈ L` with `‖y‖ < λℓ(L)` satisfies
`y ∈ span {v₀, …, v_{ℓ-2}}`.

Proof structure (induction on `ℓ`):
- `ℓ = 1`: any nonzero lattice point has norm `≥ λ₁`, so `y = 0`;
- block case `λ_{ℓ-1} = λℓ`: `‖y‖ < λ_{ℓ-1}`, apply the induction hypothesis at `ℓ - 1`;
- gap case `λ_{ℓ-1} < λℓ`: if `y` were outside the span of the first `ℓ - 1` vectors, those
  vectors together with `y` would be `ℓ` independent lattice points each of norm `< λℓ`
  (the first `ℓ - 1` vectors have norm `≤ λ_{ℓ-1} < λℓ` by monotonicity), contradicting the
  definition of `λℓ` as the infimum of such radii.

All declarations are Mathlib-only apart from the Commons successive-minima API.
-/

noncomputable section
open Set Filter Metric
set_option autoImplicit false
set_option linter.unusedSectionVars false

namespace Commons.Lattice.SuccessiveMinima

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]

/-- A family of vectors which is `ℝ`-linearly independent is `ℤ`-linearly independent
(any integer linear relation is a real one after casting the coefficients). -/
lemma linearIndependent_int_of_linearIndependent_real {ι : Type*} [Fintype ι] {w : ι → E}
    (hw : LinearIndependent ℝ w) : LinearIndependent ℤ w := by
  rw [Fintype.linearIndependent_iff]
  intro g hg i
  have hgR : (∑ j : ι, ((g j : ℤ) : ℝ) • w j) = 0 := by
    calc
      (∑ j : ι, ((g j : ℤ) : ℝ) • w j) = ∑ j : ι, (g j : ℤ) • w j := by
        apply Finset.sum_congr rfl
        intro j hj
        rw [← Int.cast_smul_eq_zsmul ℝ (g j) (w j)]
      _ = 0 := hg
  have hz := (Fintype.linearIndependent_iff.mp hw) (fun j : ι => ((g j : ℤ) : ℝ)) hgR
  have : (g i : ℝ) = 0 := hz i
  exact_mod_cast this

theorem interior_exclusion {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] (L : Submodule ℤ E) [DiscreteTopology L] [IsZLattice ℝ L]
    {d : ℕ} (hfin : Module.finrank ℤ L = d)
    (v : Fin d → L) (hvind : LinearIndependent ℝ (fun j : Fin d => (v j : E)))
    (hv : ∀ j : Fin d, ‖(v j : E)‖ ≤ Commons.Lattice.SuccessiveMinima.successiveMinimum L (j.val + 1)) :
    ∀ ℓ : ℕ, 1 ≤ ℓ → ℓ ≤ d → ∀ y : L,
      ‖(y : E)‖ < Commons.Lattice.SuccessiveMinima.successiveMinimum L ℓ →
      (y : E) ∈ Submodule.span ℝ {x : E | ∃ j : Fin d, j.val < ℓ - 1 ∧ x = (v j : E)} := by
  classical
  let μ : ℕ → ℝ := fun i => successiveMinimum L i
  let S : ℕ → Set E := fun n => {x : E | ∃ j : Fin d, j.val < n - 1 ∧ x = (v j : E)}
  change ∀ ℓ : ℕ, 1 ≤ ℓ → ℓ ≤ d → ∀ y : L, ‖(y : E)‖ < μ ℓ → (y : E) ∈ Submodule.span ℝ (S ℓ)
  have hfin' : Module.finrank ℤ L = d := hfin
  have hmono : ∀ {i j : ℕ}, i ≤ j → j ≤ d → μ i ≤ μ j := by
    intro i j hij hj
    dsimp [μ]
    exact successiveMinimum_mono L hij (by simpa [hfin] using hj)
  have hfirst : ∀ y : L, y ≠ 0 → μ 1 ≤ ‖(y : E)‖ := by
    intro y hy
    dsimp [μ]
    exact first_successiveMinimum_le_of_mem y hy
  -- prefix set equality
  have hgens : ∀ (m : ℕ), (hm : m ≤ d) →
      {x : E | ∃ j : Fin d, j.val < m ∧ x = (v j : E)}
        = Set.range (fun k : Fin m => (v (Fin.castLE hm k) : E)) := by
    intro m hm
    ext x
    constructor
    · rintro ⟨j, hj, rfl⟩
      refine ⟨⟨j.val, hj⟩, ?_⟩
      change (v (Fin.castLE hm ⟨j.val, hj⟩) : E) = (v j : E)
      have hidx : Fin.castLE hm ⟨j.val, hj⟩ = j := Fin.eq_of_val_eq (by rfl)
      rw [hidx]
    · rintro ⟨k, rfl⟩
      refine ⟨Fin.castLE hm k, k.isLt, rfl⟩
  intro ℓ
  induction ℓ with
  | zero =>
      intro h1
      omega
  | succ ℓ ih =>
      intro h1 hn y hy
      -- goal: (y : E) ∈ Submodule.span ℝ (S (ℓ + 1))
      have hℓ0 : ℓ = 0 ∨ 1 ≤ ℓ := by omega
      rcases hℓ0 with rfl | hℓ1
      · -- base case: ℓ = 0, prove Claim 1
        have hy0 : y = 0 := by
          by_contra hyne
          have hle : μ 1 ≤ ‖(y : E)‖ := hfirst y hyne
          have : μ (0 + 1) ≤ ‖(y : E)‖ := by simpa using hle
          linarith
        subst y
        simp [S]
      · -- ℓ ≥ 1
        have hℓd : ℓ ≤ d := by omega
        have hleℓ : μ ℓ ≤ μ (ℓ + 1) := hmono (by omega) (by omega)
        by_cases hEq : μ ℓ = μ (ℓ + 1)
        · -- block case
          have hy' : ‖(y : E)‖ < μ ℓ := by
            rw [hEq]
            simpa using hy
          have hmem' : (y : E) ∈ Submodule.span ℝ (S ℓ) := ih hℓ1 hℓd y hy'
          have hsub : S ℓ ⊆ S (ℓ + 1) := by
            intro x hx
            rcases hx with ⟨j, hj, rfl⟩
            refine ⟨j, ?_, rfl⟩
            omega
          exact (Submodule.span_mono hsub) hmem'
        · -- gap case: μ ℓ < μ (ℓ + 1)
          have hgap : μ ℓ < μ (ℓ + 1) := lt_of_le_of_ne hleℓ hEq
          by_contra hmem
          -- hmem : (y : E) ∉ Submodule.span ℝ (S (ℓ + 1))
          have hspanEq' : Submodule.span ℝ (S (ℓ + 1)) =
              Submodule.span ℝ (Set.range (fun k : Fin ℓ => (v (Fin.castLE hℓd k) : E))) := by
            apply congrArg (Submodule.span ℝ)
            simpa [S] using hgens ℓ hℓd
          have hnotR : (y : E) ∉ Submodule.span ℝ
              (Set.range (fun k : Fin ℓ => (v (Fin.castLE hℓd k) : E))) := by
            intro hR
            exact hmem (by rw [hspanEq']; exact hR)
          have hLIu : LinearIndependent ℝ (fun k : Fin ℓ => (v (Fin.castLE hℓd k) : E)) := by
            exact hvind.comp (Fin.castLE hℓd) (Fin.castLE_injective hℓd)
          let fE : Fin (ℓ + 1) → E :=
            Fin.snoc (fun k : Fin ℓ => (v (Fin.castLE hℓd k) : E)) (y : E)
          have hfE_LI : LinearIndependent ℝ fE := by
            exact (linearIndependent_finSnoc (K := ℝ) (x := (y : E))
              (v := fun k : Fin ℓ => (v (Fin.castLE hℓd k) : E))).2 ⟨hLIu, hnotR⟩
          let f : Fin (ℓ + 1) → L := Fin.snoc (fun k : Fin ℓ => v (Fin.castLE hℓd k)) y
          have hf_imgs : (fun j : Fin (ℓ + 1) => (f j : E)) = fE := by
            ext j
            cases j using Fin.lastCases with
            | last => simp [f, fE]
            | cast k => simp [f, fE]
          have hfLIz : LinearIndependent ℤ (fun j : Fin (ℓ + 1) => (f j : E)) := by
            apply linearIndependent_int_of_linearIndependent_real
            simpa [hf_imgs] using hfE_LI
          -- norms of each < μ (ℓ+1)
          have hf_lt : ∀ j : Fin (ℓ + 1), ‖(f j : E)‖ < μ (ℓ + 1) := by
            intro j
            by_cases hjeq : j.val = ℓ
            · have hjl : j = Fin.last ℓ := by apply Fin.ext; exact hjeq
              have hyjl : ‖(f (Fin.last ℓ) : E)‖ < μ (ℓ + 1) := by
                simpa [f, Fin.snoc_last] using hy
              simpa [hjl] using hyjl
            · have hjlt : j.val < ℓ := lt_of_le_of_ne (Nat.lt_succ_iff.mp j.isLt) (by
                intro h
                exact hjeq h)
              let k : Fin ℓ := ⟨j.val, hjlt⟩
              have hk : j = k.castSucc := by apply Fin.ext; rfl
              have hvj : f j = v (Fin.castLE hℓd k) := by
                rw [hk]
                exact Fin.snoc_castSucc (α := fun _ : Fin (ℓ + 1) => L) (x := y)
                  (p := fun k0 : Fin ℓ => v (Fin.castLE hℓd k0)) (i := k)
              have hbj : ‖(f j : E)‖ ≤ successiveMinimum L (k.val + 1) := by
                rw [hvj]
                exact hv (Fin.castLE hℓd k)
              have hbμ : ‖(f j : E)‖ ≤ μ (k.val + 1) := by simpa [μ] using hbj
              have hmon : μ (k.val + 1) ≤ μ ℓ := hmono (by omega) (by omega)
              have hmonlt : μ (k.val + 1) < μ (ℓ + 1) := lt_of_le_of_lt hmon hgap
              exact lt_of_le_of_lt hbμ hmonlt
          let r : ℝ := (Finset.univ : Finset (Fin (ℓ + 1))).sup' (by simp)
              (fun j : Fin (ℓ + 1) => ‖(f j : E)‖)
          have hrlt : r < μ (ℓ + 1) := by
            dsimp [r]
            exact (Finset.sup'_lt_iff (s := (Finset.univ : Finset (Fin (ℓ + 1)))) (H := by simp)
              (f := fun j : Fin (ℓ + 1) => ‖(f j : E)‖) (a := μ (ℓ + 1))).2
              (by intro j hj; exact hf_lt j)
          have hrge : 0 ≤ r := by
            let j0 : Fin (ℓ + 1) := ⟨0, by omega⟩
            exact le_trans (norm_nonneg (f j0 : E)) (Finset.le_sup'
              (s := (Finset.univ : Finset (Fin (ℓ + 1))))
              (f := fun j : Fin (ℓ + 1) => ‖(f j : E)‖) (b := j0) (by simp))
          have hnormle : ∀ j : Fin (ℓ + 1), ‖(f j : E)‖ ≤ r := by
            intro j
            dsimp [r]
            exact Finset.le_sup' (s := (Finset.univ : Finset (Fin (ℓ + 1))))
              (f := fun j : Fin (ℓ + 1) => ‖(f j : E)‖) (b := j) (by simp)
          have hleR : μ (ℓ + 1) ≤ r := by
            dsimp [μ]
            exact successiveMinimum_le_of_exists L (ℓ + 1) hrge f hfLIz hnormle
          linarith
end Commons.Lattice.SuccessiveMinima
