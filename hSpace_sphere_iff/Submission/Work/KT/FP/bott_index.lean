import Mathlib
import Submission.Work.KT.Defs
import Submission.Work.KT.Fund.Kappa
import Submission.Work.KT.Fund.SpectralAux
import Submission.Work.KT.Fund.laurent_approx
import Submission.Work.KT.FP.PencilDefs
import Submission.Work.KT.FP.Linsample
import Submission.Work.KT.FP.SliceAux
import Submission.Work.KT.FP.pencil_proj_data
import Submission.Work.KT.FP.proj_identities
import Submission.Work.KT.FP.wPen_admissible

import Submission.Work.KT.FP.laurent_homotopy_lift
import Submission.Work.KT.FP.lindAt_admissible
import Submission.Work.KT.FP.lindAt_pad
import Submission.Work.KT.FP.lindAt_slice_eq
import Submission.Work.KT.FP.lind_linear
import Submission.Work.KT.FP.laurentMap_injective
import Submission.Work.KT.FP.lindAt_eq_of_homotopic
import Submission.Work.KT.FP.disc_unit_homotopic_const
import Submission.Work.KT.FP.bott_index_aux
import Submission.Work.KT.FP.bott_index_const

/-! Guidance from the project lead (the requester):

ROUTE: Submission/Work/KT/FP_README.md and DESIGN.md 'Addendum: fund_product split' (the lead's split of fund_product). CONVENTION: [Ring A] + explicit commutativity. Siblings run in parallel; fund_product = EG.fund_product_of_bott ... (fp_retract X).1 hrmul (fp_retract X).2 (fp_surj ...) (fp_inj ...).

| 4 | `bott_index` | 5–10k | **high** (the remaining Bott content) | `laurent_approx`, `homotopy_inv`, the spectral machinery | now |
| 5 | `fp_inj` | 0.5–1k | low | 3, 4, `Fund.kappa_bott` (in flight) | now; closes when 3, 4 and `kappa_bott` land |

The assembly (`fund_product_assembled`) is **proved** from 1, 2 and 5, using `EG.fund_product_of_bott`
(proved) and `k0_basic` (proved).

---

## 1 `fp_retract`
* **`r ∘ s = id`.** `(Fund.bp X) ≫ fst = id` as continuous maps, so
  `pullAlg fst ≫ pullAlg bp = pullAlg id`. Then use `k0_basic` conjuncts 3 and 4 (`K0.map` of a
  composite and of `id`).
* **`r γ = 1`.** `bp ≫ snd` is the constant map at `pt`, so `pullAlg (const pt)` factors as
  `(Algebra.ofId ℂ C(X,ℂ)).comp (evalC pt)`. Apply `K0.map_comp`, then `EG.hopf_eval_one pt`
  (`= cls (Mat.one ℂ 1)`). Finally, `K0.map` of `algebraMap` sends `Mat.one ℂ 1` to
  `Mat.one C(X,ℂ) 1` (`mapCls` + `Matrix.map_one`).

## 2 `fp_surj`
1. **`r y = 0 ⇒ pullUp y = 0`.** Use `Fund.Disc`: `pullUp y = sD (ev0 (pullUp y))`, and
   `ev0 ∘ pullUp = r` (both restrict to `X × {up 0} = X × {pt}`).
2. **`pullDn y = 0`.**
   * Write `pullDn y = sD a'`.
   * The square commutes, so `ρ (pullDn y) = ρ (pullUp y) = 0`, with `ρ` the boundary restriction.
   * `ρ ∘ sD` is the pull-back along `X × S¹ → X`, which has a left inverse (evaluate at `1 ∈ S¹`).
     Hence `a' = 0`.
3. **Conclude.** `kappa_span` gives `y = Σ cᵢ (κ uᵢ − κ 1)`. Then `κ 1 = cls 1` (`Fund.kappa_one`),
   and `EG.kappa_reduce` gives each `κ uᵢ − cls 1 = μ (s bᵢ) β`. Sum by additivity of `μ` and `s`:
   `b = Σ cᵢ bᵢ`.

## 3 `kappa_eq_disc` (the converse of `kappa_span`'s `clutchIdem_mvN`)
1. **Stable MvN.** `κ u = κ v` gives `cls (clutchIdem u) = cls (clutchIdem v)` over `pullAlg2 X`
   (`k0Glue` is an isomorphism). Apply `cls_eq_stable_mvN`, then add the complement to make the
   stabiliser trivial: `clutchIdem u ⊕ 1_k ~ clutchIdem v ⊕ 1_k`.
2. **Pass to `u ⊕ 1`.** The `clutchIdem_add_mvn` / `clutchIdem_one` pattern (as in `Fund.kappa_add`)
   gives `clutchIdem (u⊕1) ~ clutchIdem (v⊕1)`.
3. **Disc units.** Project the MvN witnesses `(a, b)` by `prF`/`prS`. Sandwich them with the
   trivialisations to get units over `C(X × Ball ℂ)`:
   * upper disc: `α₀ := graphLinv (F_v) · a₀ · graphB (F_u)`;
   * lower disc: `α₁ := recipLinv · a₁ · recipB`, with inverses built the same way from `b`.
   * The lemmas are all in `kappa_span.lean`: `graphLinv_mul`, `graphB_mul_graphLinv`,
     `recipB_inv_mul_graphB`, `rgraphLinv_map`.
   * First replace `a` by `Q a P` (possible since `ba = P`, `ab = Q`).
4. **Compatibility on the circle.** `α₁| · (u⊕1) = (v⊕1) · α₀|`, from `clutch_agree` and
   `recipB_inv_mul_graphB`. So `u⊕1 = g₀| (v⊕1) g₁|` with `g₀ = α₁⁻¹` and `g₁ = α₀`.
* Reuse `Bott.mvN_glue`, `Bott.k0_mv_inj`/`stable_free` and `Bott.isUnit_mulMap_prod`.
-/

set_option maxHeartbeats 1000000

namespace Work.KT.FP

open Matrix

noncomputable section

variable {X : Type} [TopologicalSpace X] [CompactSpace X] [T2Space X]

/-! ## The Bott index

The index of a unit over `X × S¹` is computed from a Laurent approximant `P` of degree bound
`m`: `lindAt X n m P ρ` is the class of the pencil projection of the W linearisation of
`z^m · P`, corrected by `m` trivial blocks.  The lemmas
`lindAt_admissible`, `lindAt_pad`, `lindAt_eq_of_homotopic`, `lind_linear` and
`laurentMap_injective` (all in this directory) make this well defined and computable.
-/

/-- A degree bound for a matrix of Laurent polynomials. -/
def lbound (X : Type) [TopologicalSpace X] (n : ℕ)
    (P : Matrix (Fin n) (Fin n) (LaurentPolynomial C(X, ℂ))) : ℕ :=
  Finset.univ.sup fun ij : Fin n × Fin n => (P ij.1 ij.2).coeff.support.sup Int.natAbs

lemma lbound_spec (X : Type) [TopologicalSpace X] (n : ℕ)
    (P : Matrix (Fin n) (Fin n) (LaurentPolynomial C(X, ℂ))) (i j : Fin n) (k : ℤ)
    (hk : ((lbound X n P : ℕ) : ℤ) < k ∨ k < -((lbound X n P : ℕ) : ℤ)) :
    (P i j).coeff k = 0 := by
  by_contra h
  have hmem : k ∈ (P i j).coeff.support := Finsupp.mem_support_iff.mpr h
  have h1 : Int.natAbs k ≤ (P i j).coeff.support.sup Int.natAbs :=
    Finset.le_sup (f := Int.natAbs) hmem
  have h2 : (P i j).coeff.support.sup Int.natAbs ≤ lbound X n P :=
    Finset.le_sup (f := fun ij : Fin n × Fin n => (P ij.1 ij.2).coeff.support.sup Int.natAbs)
      (Finset.mem_univ (i, j))
  have h3 : Int.natAbs k ≤ lbound X n P := le_trans h1 h2
  have h4 : (Int.natAbs k : ℤ) ≤ ((lbound X n P : ℕ) : ℤ) := by exact_mod_cast h3
  have hk1 : k ≤ (Int.natAbs k : ℤ) := Int.le_natAbs
  have hk2 : -k ≤ (Int.natAbs k : ℤ) := by
    have h := Int.le_natAbs (a := -k)
    rwa [Int.natAbs_neg] at h
  rcases hk with hk | hk <;> omega

/-- The data of a Laurent approximant of a unit over `X × S¹`: a degree bound `m`, a Laurent
matrix `P`, an admissible radius `ρ` for its W linearisation, and the homotopy from `u` to
`P.map (laurentMap X)`. -/
structure ApproxData (X : Type) [TopologicalSpace X] [CompactSpace X] [T2Space X] (n : ℕ)
    (u : (Matrix (Fin n) (Fin n) C(X × Sph ℂ, ℂ))ˣ) where
  m : ℕ
  P : Matrix (Fin n) (Fin n) (LaurentPolynomial C(X, ℂ))
  bound : ∀ (i j : Fin n) (k : ℤ), (m : ℤ) < k ∨ k < -(m : ℤ) → (P i j).coeff k = 0
  unit : IsUnit (P.map (Work.KT.laurentMap X))
  rho : ℝ
  rho_pos : 0 < rho
  rho_le : rho ≤ 1
  adm : ∀ z : ℂ, rho ≤ ‖z‖ → ‖z‖ ≤ 1 → IsUnit (z • linAf X n m + linBf X n m P)
  hom : ∃ H : (Matrix (Fin n) (Fin n) C((X × Sph ℂ) × unitInterval, ℂ))ˣ,
      (∀ (i j : Fin n) (x : X) (z : Sph ℂ),
        (H : Matrix (Fin n) (Fin n) C((X × Sph ℂ) × unitInterval, ℂ)) i j ((x, z), 0)
          = (u : Matrix (Fin n) (Fin n) C(X × Sph ℂ, ℂ)) i j (x, z)) ∧
      (∀ (i j : Fin n) (x : X) (z : Sph ℂ),
        (H : Matrix (Fin n) (Fin n) C((X × Sph ℂ) × unitInterval, ℂ)) i j ((x, z), 1)
          = (P.map (Work.KT.laurentMap X)) i j (x, z))

lemma approxData_nonempty (X : Type) [TopologicalSpace X] [CompactSpace X] [T2Space X] (n : ℕ)
    (u : (Matrix (Fin n) (Fin n) C(X × Sph ℂ, ℂ))ˣ) : Nonempty (ApproxData X n u) := by
  obtain ⟨P, hP, H, hH, h0, h1⟩ :=
    Work.KT.Fund.laurent_approx X n (u : Matrix (Fin n) (Fin n) C(X × Sph ℂ, ℂ)) u.isUnit
  obtain ⟨ρ, hρ0, hρ1, hadm⟩ :=
    lindAt_admissible X n (lbound X n P) P (lbound_spec X n P) hP
  refine ⟨⟨lbound X n P, P, lbound_spec X n P, hP, ρ, hρ0, hρ1, hadm, ?_⟩⟩
  refine ⟨hH.unit, ?_, ?_⟩
  · intro i j x z
    exact h0 i j x z
  · intro i j x z
    exact h1 i j x z

/-- The canonical approximant data of a unit. -/
noncomputable def adata (X : Type) [TopologicalSpace X] [CompactSpace X] [T2Space X] (n : ℕ)
    (u : (Matrix (Fin n) (Fin n) C(X × Sph ℂ, ℂ))ˣ) : ApproxData X n u :=
  Classical.choice (approxData_nonempty X n u)

/-- The value of the Bott index of a unit, computed from its canonical approximant. -/
noncomputable def Nval (X : Type) [TopologicalSpace X] [CompactSpace X] [T2Space X] (n : ℕ)
    (u : (Matrix (Fin n) (Fin n) C(X × Sph ℂ, ℂ))ˣ) : K0 C(X, ℂ) :=
  lindAt X n (adata X n u).m (adata X n u).P (adata X n u).rho

/-! ## Homotopy invariance of the index

`lindAt X n m P ρ` only depends on the homotopy class of the Laurent matrix `P` inside the units
over `X × S¹`, and is independent of the stated degree bound `m` (`lindAt_pad_chain`).  We package
this as `lindAt_hom_inv`, in the shape in which the canonical approximant `adata` delivers its
homotopy: a *unit* of matrices over `(X × S¹) × [0,1]`.
-/

/-- **Homotopy invariance of `lindAt` for Laurent representatives of different degree bounds.** -/
theorem lindAt_hom_inv (X : Type) [TopologicalSpace X] [CompactSpace X] [T2Space X]
    (n m₀ m₁ : ℕ)
    (P₀ P₁ : Matrix (Fin n) (Fin n) (LaurentPolynomial C(X, ℂ)))
    (hb₀ : ∀ (i j : Fin n) (k : ℤ), (m₀ : ℤ) < k ∨ k < -(m₀ : ℤ) → (P₀ i j).coeff k = 0)
    (hb₁ : ∀ (i j : Fin n) (k : ℤ), (m₁ : ℤ) < k ∨ k < -(m₁ : ℤ) → (P₁ i j).coeff k = 0)
    (H : (Matrix (Fin n) (Fin n) C((X × Sph ℂ) × unitInterval, ℂ))ˣ)
    (h₀ : ∀ (i j : Fin n) (x : X) (z : Sph ℂ),
      (H : Matrix (Fin n) (Fin n) C((X × Sph ℂ) × unitInterval, ℂ)) i j ((x, z), 0)
        = (P₀.map (Work.KT.laurentMap X)) i j (x, z))
    (h₁ : ∀ (i j : Fin n) (x : X) (z : Sph ℂ),
      (H : Matrix (Fin n) (Fin n) C((X × Sph ℂ) × unitInterval, ℂ)) i j ((x, z), 1)
        = (P₁.map (Work.KT.laurentMap X)) i j (x, z))
    {ρ₀ ρ₁ : ℝ} (hρ₀0 : 0 < ρ₀) (hρ₀1 : ρ₀ ≤ 1) (hρ₁0 : 0 < ρ₁) (hρ₁1 : ρ₁ ≤ 1)
    (hadm₀ : ∀ z : ℂ, ρ₀ ≤ ‖z‖ → ‖z‖ ≤ 1 → IsUnit (z • linAf X n m₀ + linBf X n m₀ P₀))
    (hadm₁ : ∀ z : ℂ, ρ₁ ≤ ‖z‖ → ‖z‖ ≤ 1 → IsUnit (z • linAf X n m₁ + linBf X n m₁ P₁)) :
    lindAt X n m₀ P₀ ρ₀ = lindAt X n m₁ P₁ ρ₁ := by
  set M : ℕ := max m₀ m₁ with hM
  have hm₀ : m₀ ≤ M := le_max_left _ _
  have hm₁ : m₁ ≤ M := le_max_right _ _
  have hcast₀ : (m₀ : ℤ) ≤ (M : ℤ) := by exact_mod_cast hm₀
  have hcast₁ : (m₁ : ℤ) ≤ (M : ℤ) := by exact_mod_cast hm₁
  have hb₀M : ∀ (i j : Fin n) (k : ℤ), (M : ℤ) < k ∨ k < -(M : ℤ) → (P₀ i j).coeff k = 0 := by
    intro i j k hk
    exact hb₀ i j k (by rcases hk with hk | hk <;> omega)
  have hb₁M : ∀ (i j : Fin n) (k : ℤ), (M : ℤ) < k ∨ k < -(M : ℤ) → (P₁ i j).coeff k = 0 := by
    intro i j k hk
    exact hb₁ i j k (by rcases hk with hk | hk <;> omega)
  have hadm₀M : ∀ z : ℂ, ρ₀ ≤ ‖z‖ → ‖z‖ ≤ 1 →
      IsUnit (z • linAf X n M + linBf X n M P₀) :=
    lindAt_adm_mono X n m₀ M hm₀ P₀ hb₀ hρ₀0 hadm₀
  have hadm₁M : ∀ z : ℂ, ρ₁ ≤ ‖z‖ → ‖z‖ ≤ 1 →
      IsUnit (z • linAf X n M + linBf X n M P₁) :=
    lindAt_adm_mono X n m₁ M hm₁ P₁ hb₁ hρ₁0 hadm₁
  have h₀' : ∀ (i j : Fin n) (x : X) (z : Sph ℂ),
      (unitPull (swapCm X) H : Matrix (Fin n) (Fin n) C((X × unitInterval) × Sph ℂ, ℂ)) i j
          ((x, 0), z)
        = (P₀.map (Work.KT.laurentMap X)) i j (x, z) := by
    intro i j x z
    rw [unitPull_swapCm_apply]
    exact h₀ i j x z
  have h₁' : ∀ (i j : Fin n) (x : X) (z : Sph ℂ),
      (unitPull (swapCm X) H : Matrix (Fin n) (Fin n) C((X × unitInterval) × Sph ℂ, ℂ)) i j
          ((x, 1), z)
        = (P₁.map (Work.KT.laurentMap X)) i j (x, z) := by
    intro i j x z
    rw [unitPull_swapCm_apply]
    exact h₁ i j x z
  have hmid : lindAt X n M P₀ ρ₀ = lindAt X n M P₁ ρ₁ :=
    lindAt_eq_of_homotopic X n M P₀ P₁ hb₀M hb₁M (unitPull (swapCm X) H) h₀' h₁'
      hρ₀0 hρ₀1 hρ₁0 hρ₁1 hadm₀M hadm₁M
  have e₀ : lindAt X n M P₀ ρ₀ = lindAt X n m₀ P₀ ρ₀ :=
    lindAt_pad_chain X n P₀ hm₀ hb₀ hρ₀0 hρ₀1
      (fun j hj1 _ => lindAt_adm_mono X n m₀ j hj1 P₀ hb₀ hρ₀0 hadm₀)
  have e₁ : lindAt X n M P₁ ρ₁ = lindAt X n m₁ P₁ ρ₁ :=
    lindAt_pad_chain X n P₁ hm₁ hb₁ hρ₁0 hρ₁1
      (fun j hj1 _ => lindAt_adm_mono X n m₁ j hj1 P₁ hb₁ hρ₁0 hadm₁)
  rw [← e₀, ← e₁]
  exact hmid

/-! ## The index of a unit, computed from any Laurent representative presented by a homotopy -/

/-- The slice at `0` of a unit homotopy, as an equality of units. -/
lemma unitEval_zero_eq {n : ℕ} (Y : Type) [TopologicalSpace Y]
    (K : (Matrix (Fin n) (Fin n) C(Y × unitInterval, ℂ))ˣ)
    (a : (Matrix (Fin n) (Fin n) C(Y, ℂ))ˣ)
    (h : ∀ (i j : Fin n) (y : Y), (K : Matrix (Fin n) (Fin n) C(Y × unitInterval, ℂ)) i j (y, 0)
      = (a : Matrix (Fin n) (Fin n) C(Y, ℂ)) i j y) :
    unitEval 0 K = a := by
  ext i j y
  rw [unitEval_apply]
  exact h i j y

/-- The slice at `1` of a unit homotopy, as an equality of units. -/
lemma unitEval_one_eq {n : ℕ} (Y : Type) [TopologicalSpace Y]
    (K : (Matrix (Fin n) (Fin n) C(Y × unitInterval, ℂ))ˣ)
    (a : (Matrix (Fin n) (Fin n) C(Y, ℂ))ˣ)
    (h : ∀ (i j : Fin n) (y : Y), (K : Matrix (Fin n) (Fin n) C(Y × unitInterval, ℂ)) i j (y, 1)
      = (a : Matrix (Fin n) (Fin n) C(Y, ℂ)) i j y) :
    unitEval 1 K = a := by
  ext i j y
  rw [unitEval_apply]
  exact h i j y

/-- **`Nval` computed from any Laurent representative together with a unit homotopy to it.**  This
is the only form of well-definedness of `Nval` that the final proof uses. -/
theorem Nval_eq_of_hom (X : Type) [TopologicalSpace X] [CompactSpace X] [T2Space X]
    (n : ℕ) (u : (Matrix (Fin n) (Fin n) C(X × Sph ℂ, ℂ))ˣ)
    (P : Matrix (Fin n) (Fin n) (LaurentPolynomial C(X, ℂ))) (m : ℕ)
    (hbP : ∀ (i j : Fin n) (k : ℤ), (m : ℤ) < k ∨ k < -(m : ℤ) → (P i j).coeff k = 0)
    {ρ : ℝ} (hρ0 : 0 < ρ) (hρ1 : ρ ≤ 1)
    (hadm : ∀ z : ℂ, ρ ≤ ‖z‖ → ‖z‖ ≤ 1 → IsUnit (z • linAf X n m + linBf X n m P))
    (K : (Matrix (Fin n) (Fin n) C((X × Sph ℂ) × unitInterval, ℂ))ˣ)
    (hK0 : ∀ (i j : Fin n) (x : X) (z : Sph ℂ),
      (K : Matrix (Fin n) (Fin n) C((X × Sph ℂ) × unitInterval, ℂ)) i j ((x, z), 0)
        = (u : Matrix (Fin n) (Fin n) C(X × Sph ℂ, ℂ)) i j (x, z))
    (hK1 : ∀ (i j : Fin n) (x : X) (z : Sph ℂ),
      (K : Matrix (Fin n) (Fin n) C((X × Sph ℂ) × unitInterval, ℂ)) i j ((x, z), 1)
        = (P.map (Work.KT.laurentMap X)) i j (x, z)) :
    Nval X n u = lindAt X n m P ρ := by
  obtain ⟨Hu, hu0, hu1⟩ := (adata X n u).hom
  have hK0u : unitEval 0 K = u := by
    refine unitEval_zero_eq (X × Sph ℂ) K u ?_
    intro i j p
    obtain ⟨x, z⟩ := p
    exact hK0 i j x z
  have hu0u : unitEval 0 Hu = u := by
    refine unitEval_zero_eq (X × Sph ℂ) Hu u ?_
    intro i j p
    obtain ⟨x, z⟩ := p
    exact hu0 i j x z
  have hmid : unitEval 0 K = unitEval 1 (unitPull (revCm X) Hu) := by
    rw [unitEval_one_unitPull_rev]
    exact hK0u.trans hu0u.symm
  let Hcat : (Matrix (Fin n) (Fin n) C((X × Sph ℂ) × unitInterval, ℂ))ˣ :=
    unitConcat (unitPull (revCm X) Hu) K
  have hcat0 : unitEval 0 Hcat = unitEval 0 (unitPull (revCm X) Hu) :=
    unitEval_zero_unitConcat _ _ hmid
  have hcat1 : unitEval 1 Hcat = unitEval 1 K := unitEval_one_unitConcat _ _ hmid
  have hH0 : ∀ (i j : Fin n) (x : X) (z : Sph ℂ),
      (Hcat : Matrix (Fin n) (Fin n) C((X × Sph ℂ) × unitInterval, ℂ)) i j ((x, z), 0)
        = ((adata X n u).P.map (Work.KT.laurentMap X)) i j (x, z) := by
    intro i j x z
    have h1 : (unitEval 0 Hcat : Matrix (Fin n) (Fin n) C(X × Sph ℂ, ℂ)) i j (x, z)
        = ((adata X n u).P.map (Work.KT.laurentMap X)) i j (x, z) := by
      rw [hcat0, unitEval_zero_unitPull_rev, unitEval_apply]
      exact hu1 i j x z
    simpa [unitEval_apply] using h1
  have hH1 : ∀ (i j : Fin n) (x : X) (z : Sph ℂ),
      (Hcat : Matrix (Fin n) (Fin n) C((X × Sph ℂ) × unitInterval, ℂ)) i j ((x, z), 1)
        = (P.map (Work.KT.laurentMap X)) i j (x, z) := by
    intro i j x z
    have h1 : (unitEval 1 Hcat : Matrix (Fin n) (Fin n) C(X × Sph ℂ, ℂ)) i j (x, z)
        = (P.map (Work.KT.laurentMap X)) i j (x, z) := by
      rw [hcat1, unitEval_apply]
      exact hK1 i j x z
    simpa [unitEval_apply] using h1
  exact lindAt_hom_inv X n (adata X n u).m m (adata X n u).P P (adata X n u).bound hbP Hcat
    hH0 hH1 (adata X n u).rho_pos (adata X n u).rho_le hρ0 hρ1 (adata X n u).adm hadm

/-- **Homotopy invariance of `Nval`**: two units joined by a homotopy through units over `X × S¹`
have the same Bott index. -/
theorem Nval_hom_inv (X : Type) [TopologicalSpace X] [CompactSpace X] [T2Space X]
    (n : ℕ) (u w : (Matrix (Fin n) (Fin n) C(X × Sph ℂ, ℂ))ˣ)
    (K : (Matrix (Fin n) (Fin n) C((X × Sph ℂ) × unitInterval, ℂ))ˣ)
    (hK0 : ∀ (i j : Fin n) (x : X) (z : Sph ℂ),
      (K : Matrix (Fin n) (Fin n) C((X × Sph ℂ) × unitInterval, ℂ)) i j ((x, z), 0)
        = (u : Matrix (Fin n) (Fin n) C(X × Sph ℂ, ℂ)) i j (x, z))
    (hK1 : ∀ (i j : Fin n) (x : X) (z : Sph ℂ),
      (K : Matrix (Fin n) (Fin n) C((X × Sph ℂ) × unitInterval, ℂ)) i j ((x, z), 1)
        = (w : Matrix (Fin n) (Fin n) C(X × Sph ℂ, ℂ)) i j (x, z)) :
    Nval X n u = Nval X n w := by
  obtain ⟨Hu, hu0, hu1⟩ := (adata X n u).hom
  obtain ⟨Hw, hw0, hw1⟩ := (adata X n w).hom
  have hK0u : unitEval 0 K = u := by
    refine unitEval_zero_eq (X × Sph ℂ) K u ?_
    intro i j p
    obtain ⟨x, z⟩ := p
    exact hK0 i j x z
  have hK1w : unitEval 1 K = w := by
    refine unitEval_one_eq (X × Sph ℂ) K w ?_
    intro i j p
    obtain ⟨x, z⟩ := p
    exact hK1 i j x z
  have hu0u : unitEval 0 Hu = u := by
    refine unitEval_zero_eq (X × Sph ℂ) Hu u ?_
    intro i j p
    obtain ⟨x, z⟩ := p
    exact hu0 i j x z
  have hw0w : unitEval 0 Hw = w := by
    refine unitEval_zero_eq (X × Sph ℂ) Hw w ?_
    intro i j p
    obtain ⟨x, z⟩ := p
    exact hw0 i j x z
  have hmid1 : unitEval 0 K = unitEval 1 (unitPull (revCm X) Hu) := by
    rw [unitEval_one_unitPull_rev]
    exact hK0u.trans hu0u.symm
  have hc2 : unitEval 1 (unitConcat (unitPull (revCm X) Hu) K) = unitEval 1 K :=
    unitEval_one_unitConcat _ _ hmid1
  have hmid2 : unitEval 0 Hw = unitEval 1 (unitConcat (unitPull (revCm X) Hu) K) := by
    rw [hc2]
    exact hw0w.trans hK1w.symm
  let Hcat : (Matrix (Fin n) (Fin n) C((X × Sph ℂ) × unitInterval, ℂ))ˣ :=
    unitConcat (unitConcat (unitPull (revCm X) Hu) K) Hw
  have hcat0 : unitEval 0 Hcat = unitEval 0 (unitPull (revCm X) Hu) := by
    rw [unitEval_zero_unitConcat _ _ hmid2, unitEval_zero_unitConcat _ _ hmid1]
  have hcat1 : unitEval 1 Hcat = unitEval 1 Hw := unitEval_one_unitConcat _ _ hmid2
  have hH0 : ∀ (i j : Fin n) (x : X) (z : Sph ℂ),
      (Hcat : Matrix (Fin n) (Fin n) C((X × Sph ℂ) × unitInterval, ℂ)) i j ((x, z), 0)
        = ((adata X n u).P.map (Work.KT.laurentMap X)) i j (x, z) := by
    intro i j x z
    have h1 : (unitEval 0 Hcat : Matrix (Fin n) (Fin n) C(X × Sph ℂ, ℂ)) i j (x, z)
        = ((adata X n u).P.map (Work.KT.laurentMap X)) i j (x, z) := by
      rw [hcat0, unitEval_zero_unitPull_rev, unitEval_apply]
      exact hu1 i j x z
    simpa [unitEval_apply] using h1
  have hH1 : ∀ (i j : Fin n) (x : X) (z : Sph ℂ),
      (Hcat : Matrix (Fin n) (Fin n) C((X × Sph ℂ) × unitInterval, ℂ)) i j ((x, z), 1)
        = ((adata X n w).P.map (Work.KT.laurentMap X)) i j (x, z) := by
    intro i j x z
    have h1 : (unitEval 1 Hcat : Matrix (Fin n) (Fin n) C(X × Sph ℂ, ℂ)) i j (x, z)
        = ((adata X n w).P.map (Work.KT.laurentMap X)) i j (x, z) := by
      rw [hcat1, unitEval_apply]
      exact hw1 i j x z
    simpa [unitEval_apply] using h1
  exact lindAt_hom_inv X n (adata X n u).m (adata X n w).m (adata X n u).P (adata X n w).P
    (adata X n u).bound (adata X n w).bound Hcat hH0 hH1 (adata X n u).rho_pos (adata X n u).rho_le
    (adata X n w).rho_pos (adata X n w).rho_le (adata X n u).adm (adata X n w).adm

/-! ## The normalisation clause

The degree bound of the sample Laurent matrix `linSample X n P = (1 - P) + P·T`, and the fact that
the unit `(1 - P) + z·P` has index `[P]` (`Work.KT.FP.lind_linear`).
-/

lemma linSample_bound (X : Type) [TopologicalSpace X] (n : ℕ)
    (P : Matrix (Fin n) (Fin n) C(X, ℂ)) :
    ∀ (i j : Fin n) (k : ℤ), ((1 : ℕ) : ℤ) < k ∨ k < -((1 : ℕ) : ℤ) →
      (linSample X n P i j).coeff k = 0 := by
  intro i j k hk
  rw [show (linSample X n P i j).coeff k
      = (if (0 : ℤ) = k then (1 - P) i j else 0) + (if (1 : ℤ) = k then P i j else 0) from
    coeff_C_add_C_mul_T _ _ k]
  have h0 : ¬ ((0 : ℤ) = k) := by rcases hk with h | h <;> omega
  have h1 : ¬ ((1 : ℤ) = k) := by rcases hk with h | h <;> omega
  rw [if_neg h0, if_neg h1, add_zero]

/-- **The normalisation clause**: a unit of the form `(1 - P) + z·P` has Bott index `[P]`. -/
theorem Nval_normalised (X : Type) [TopologicalSpace X] [CompactSpace X] [T2Space X]
    (n : ℕ) (P : Matrix (Fin n) (Fin n) C(X, ℂ)) (hP : P * P = P)
    (u : (Matrix (Fin n) (Fin n) C(X × Sph ℂ, ℂ))ˣ)
    (hu : (u : Matrix (Fin n) (Fin n) C(X × Sph ℂ, ℂ))
      = Work.KT.Fund.pullMat X (1 - P)
        + (Work.KT.zUnit X : C(X × Sph ℂ, ℂ)) • Work.KT.Fund.pullMat X P) :
    Nval X n u = cls (⟨n, P⟩ : Mat C(X, ℂ)) := by
  obtain ⟨hlin, hval⟩ := lind_linear X n P hP
  have hPunit : IsUnit ((linSample X n P).map (Work.KT.laurentMap X)) := by
    rw [hlin, ← hu]
    exact u.isUnit
  obtain ⟨ρ, hρ0, hρ1, hadm⟩ :=
    lindAt_admissible X n 1 (linSample X n P) (linSample_bound X n P) hPunit
  have hK0 : ∀ (i j : Fin n) (x : X) (z : Sph ℂ),
      (unitConst u : Matrix (Fin n) (Fin n) C((X × Sph ℂ) × unitInterval, ℂ)) i j ((x, z), 0)
        = (u : Matrix (Fin n) (Fin n) C(X × Sph ℂ, ℂ)) i j (x, z) := by
    intro i j x z
    rw [unitConst, unitPull_apply]
    rfl
  have heq : (linSample X n P).map (Work.KT.laurentMap X)
      = (u : Matrix (Fin n) (Fin n) C(X × Sph ℂ, ℂ)) := hlin.trans hu.symm
  have hK1 : ∀ (i j : Fin n) (x : X) (z : Sph ℂ),
      (unitConst u : Matrix (Fin n) (Fin n) C((X × Sph ℂ) × unitInterval, ℂ)) i j ((x, z), 1)
        = ((linSample X n P).map (Work.KT.laurentMap X)) i j (x, z) := by
    intro i j x z
    rw [unitConst, unitPull_apply, heq]
    rfl
  rw [Nval_eq_of_hom X n u (linSample X n P) 1 (linSample_bound X n P) hρ0 hρ1 hadm
    (unitConst u) hK0 hK1]
  exact hval hρ0 hρ1 hadm

/-! ## The invariance clause: the radial product homotopy

If `w = g₀| · u · g₁|` with `g₀`, `g₁` units over the disc `X × D`, then `w` is homotopic, through
units over `X × S¹`, to `M₀ · u · M₁` where `Mᵢ = gᵢ(·,0)` is the value of `gᵢ` on the zero
section.  The homotopy is the pointwise product of the two radial contractions
(`Work.KT.FP.disc_unit_homotopic_const`) with the constant homotopy at `u`.
-/

/-- The inclusion of the boundary circle into the disc, over a fixed base. -/
def bdryCm (X : Type) [TopologicalSpace X] : C(X × Sph ℂ, X × Ball ℂ) where
  toFun p := (p.1, Fund.sphIncl p.2)
  continuous_toFun := Continuous.prodMk continuous_fst
    (Fund.sphIncl.continuous.comp continuous_snd)

lemma pullAlg_bdryCm (X : Type) [TopologicalSpace X] (g : C(X × Ball ℂ, ℂ)) :
    Work.KT.pullAlg (bdryCm X) g = Fund.bdryRestrict X g := by
  ext p
  rfl

lemma unitPull_bdryCm_val (X : Type) [TopologicalSpace X] {n : ℕ}
    (G : (Matrix (Fin n) (Fin n) C(X × Ball ℂ, ℂ))ˣ) :
    ((unitPull (bdryCm X) G : (Matrix (Fin n) (Fin n) C(X × Sph ℂ, ℂ))ˣ) :
        Matrix (Fin n) (Fin n) C(X × Sph ℂ, ℂ))
      = (G : Matrix (Fin n) (Fin n) C(X × Ball ℂ, ℂ)).map (fun f => Fund.bdryRestrict X f) := by
  ext i j p
  rfl

/-- **The product homotopy of the invariance clause.** -/
theorem disc_product_homotopy (X : Type) [TopologicalSpace X] [CompactSpace X] [T2Space X]
    (n : ℕ) (g₀ g₁ : (Matrix (Fin n) (Fin n) C(X × Ball ℂ, ℂ))ˣ)
    (u w : (Matrix (Fin n) (Fin n) C(X × Sph ℂ, ℂ))ˣ)
    (hw : (w : Matrix (Fin n) (Fin n) C(X × Sph ℂ, ℂ))
      = (g₀ : Matrix (Fin n) (Fin n) C(X × Ball ℂ, ℂ)).map (fun f => Fund.bdryRestrict X f)
        * (u : Matrix (Fin n) (Fin n) C(X × Sph ℂ, ℂ))
        * (g₁ : Matrix (Fin n) (Fin n) C(X × Ball ℂ, ℂ)).map (fun f => Fund.bdryRestrict X f)) :
    ∃ (M₀ M₁ : (Matrix (Fin n) (Fin n) C(X, ℂ))ˣ)
      (H : (Matrix (Fin n) (Fin n) C((X × Sph ℂ) × unitInterval, ℂ))ˣ),
      (∀ (i j : Fin n) (x : X) (z : Sph ℂ),
        (H : Matrix (Fin n) (Fin n) C((X × Sph ℂ) × unitInterval, ℂ)) i j ((x, z), 0)
          = ((unitPull (ContinuousMap.fst : C(X × Sph ℂ, X)) M₀ * u
              * unitPull (ContinuousMap.fst : C(X × Sph ℂ, X)) M₁ :
                (Matrix (Fin n) (Fin n) C(X × Sph ℂ, ℂ))ˣ) :
              Matrix (Fin n) (Fin n) C(X × Sph ℂ, ℂ)) i j (x, z)) ∧
      (∀ (i j : Fin n) (x : X) (z : Sph ℂ),
        (H : Matrix (Fin n) (Fin n) C((X × Sph ℂ) × unitInterval, ℂ)) i j ((x, z), 1)
          = (w : Matrix (Fin n) (Fin n) C(X × Sph ℂ, ℂ)) i j (x, z)) := by
  obtain ⟨M₀, H₀, h₀0, h₀1⟩ := disc_unit_homotopic_const X n g₀
  obtain ⟨M₁, H₁, h₁0, h₁1⟩ := disc_unit_homotopic_const X n g₁
  have he0 : unitEval 0 H₀ = unitPull (ContinuousMap.fst : C(X × Sph ℂ, X)) M₀ :=
    unitEval_zero_eq (X × Sph ℂ) H₀ _ (fun i j p => by
      obtain ⟨x, z⟩ := p
      simpa using h₀0 i j x z)
  have he0' : unitEval 0 H₁ = unitPull (ContinuousMap.fst : C(X × Sph ℂ, X)) M₁ :=
    unitEval_zero_eq (X × Sph ℂ) H₁ _ (fun i j p => by
      obtain ⟨x, z⟩ := p
      simpa using h₁0 i j x z)
  have he1 : unitEval 1 H₀ = unitPull (bdryCm X) g₀ :=
    unitEval_one_eq (X × Sph ℂ) H₀ _ (fun i j p => by
      obtain ⟨x, z⟩ := p
      rw [unitPull_apply]
      show ((H₀ : Matrix (Fin n) (Fin n) C((X × Sph ℂ) × unitInterval, ℂ)) i j) ((x, z), 1)
        = ((g₀ : Matrix (Fin n) (Fin n) C(X × Ball ℂ, ℂ)) i j) (x, Fund.sphIncl z)
      exact h₀1 i j x z)
  have he1' : unitEval 1 H₁ = unitPull (bdryCm X) g₁ :=
    unitEval_one_eq (X × Sph ℂ) H₁ _ (fun i j p => by
      obtain ⟨x, z⟩ := p
      rw [unitPull_apply]
      show ((H₁ : Matrix (Fin n) (Fin n) C((X × Sph ℂ) × unitInterval, ℂ)) i j) ((x, z), 1)
        = ((g₁ : Matrix (Fin n) (Fin n) C(X × Ball ℂ, ℂ)) i j) (x, Fund.sphIncl z)
      exact h₁1 i j x z)
  refine ⟨M₀, M₁, H₀ * unitConst u * H₁, ?_, ?_⟩
  · intro i j x z
    have hu : unitEval 0 (H₀ * unitConst u * H₁)
        = unitPull (ContinuousMap.fst : C(X × Sph ℂ, X)) M₀ * u
          * unitPull (ContinuousMap.fst : C(X × Sph ℂ, X)) M₁ := by
      rw [unitEval_mul, unitEval_mul, he0, he0', unitEval_const]
    exact unitEval_eq_entries (X × Sph ℂ) 0 (H₀ * unitConst u * H₁) _ hu i j (x, z)
  · intro i j x z
    have hu : unitEval 1 (H₀ * unitConst u * H₁)
        = unitPull (bdryCm X) g₀ * u * unitPull (bdryCm X) g₁ := by
      rw [unitEval_mul, unitEval_mul, he1, he1', unitEval_const]
    have h2 := unitEval_eq_entries (X × Sph ℂ) 1 (H₀ * unitConst u * H₁) _ hu i j (x, z)
    rw [h2, Units.val_mul, Units.val_mul, unitPull_bdryCm_val, unitPull_bdryCm_val, ← hw]

/-! ## The invariance of `lindAt` under a constant unit

`matPProj` is unchanged by multiplying the pencil on the left by a unit (`Work.KT.FP.pCirc_mul_unit`)
and is equivariant under conjugating the pencil by a unit (`Work.KT.FP.pCirc_conj`).  Together with
`Work.KT.FP.linBf_const_identities_bc` this gives the invariance of `lindAt` under multiplication and
conjugation by a *constant* matrix.
-/

lemma matPProj_mul_unit {N : ℕ} (A B L : Matrix (Fin N) (Fin N) C(X, ℂ)) (hL : IsUnit L) (ρ : ℝ) :
    matPProj X N (L * A) (L * B) ρ = matPProj X N A B ρ := by
  letI : NormedRing (Matrix (Fin N) (Fin N) C(X, ℂ)) := Matrix.linftyOpNormedRing
  letI : NormedAlgebra ℂ (Matrix (Fin N) (Fin N) C(X, ℂ)) := Matrix.linftyOpNormedAlgebra
  letI : CompleteSpace (Matrix (Fin N) (Fin N) C(X, ℂ)) := Matrix.instCompleteSpace _ _ _
  have h := @pCirc_mul_unit (Matrix (Fin N) (Fin N) C(X, ℂ)) Matrix.linftyOpNormedRing
    Matrix.linftyOpNormedAlgebra (Matrix.instCompleteSpace (Fin N) (Fin N) C(X, ℂ)) A B L hL ρ
  show pProj (L * A) (L * B) ρ = pProj A B ρ
  simp only [pProj]
  rw [h]

lemma matPProj_conj {N : ℕ} (A B L : Matrix (Fin N) (Fin N) C(X, ℂ)) (hL : IsUnit L) (ρ : ℝ) :
    matPProj X N (L * A * Ring.inverse L) (L * B * Ring.inverse L) ρ
      = L * matPProj X N A B ρ * Ring.inverse L := by
  letI : NormedRing (Matrix (Fin N) (Fin N) C(X, ℂ)) := Matrix.linftyOpNormedRing
  letI : NormedAlgebra ℂ (Matrix (Fin N) (Fin N) C(X, ℂ)) := Matrix.linftyOpNormedAlgebra
  letI : CompleteSpace (Matrix (Fin N) (Fin N) C(X, ℂ)) := Matrix.instCompleteSpace _ _ _
  have h := @pCirc_conj (Matrix (Fin N) (Fin N) C(X, ℂ)) Matrix.linftyOpNormedRing
    Matrix.linftyOpNormedAlgebra (Matrix.instCompleteSpace (Fin N) (Fin N) C(X, ℂ)) A B L hL ρ
  show pProj (L * A * Ring.inverse L) (L * B * Ring.inverse L) ρ = L * pProj A B ρ * Ring.inverse L
  simp only [pProj]
  rw [h, mul_smul_comm, smul_mul_assoc]

/-- Left multiplication by a constant unit does not change `lindAt`. -/
theorem lindAt_mul_const_left (X : Type) [TopologicalSpace X] [CompactSpace X] [T2Space X]
    (n m : ℕ) (M : (Matrix (Fin n) (Fin n) C(X, ℂ))ˣ)
    (P : Matrix (Fin n) (Fin n) (LaurentPolynomial C(X, ℂ))) (ρ : ℝ) :
    lindAt X n m ((constLU X M : Matrix (Fin n) (Fin n) (LaurentPolynomial C(X, ℂ))) * P) ρ
      = lindAt X n m P ρ := by
  obtain ⟨hLA, hLB, hAA, hAB, hUL, hUA⟩ := linBf_const_identities_bc X n m M P
  have hproj : matPProj X ((2 * m + 1) * n) (linAf X n m)
        (linBf X n m ((constLU X M : Matrix (Fin n) (Fin n) (LaurentPolynomial C(X, ℂ))) * P)) ρ
      = matPProj X ((2 * m + 1) * n) (linAf X n m) (linBf X n m P) ρ := by
    have h := matPProj_mul_unit (N := (2 * m + 1) * n) (A := linAf X n m) (B := linBf X n m P)
      (L := blockLastF X n (2 * m) (M : Matrix (Fin n) (Fin n) C(X, ℂ))) hUL ρ
    rw [hLA, hLB] at h
    exact h
  unfold lindAt
  rw [hproj]

/-- Conjugation by a constant unit does not change `lindAt`. -/
theorem lindAt_conj (X : Type) [TopologicalSpace X] [CompactSpace X] [T2Space X]
    (n m : ℕ) (M : (Matrix (Fin n) (Fin n) C(X, ℂ))ˣ)
    (P : Matrix (Fin n) (Fin n) (LaurentPolynomial C(X, ℂ))) (ρ : ℝ) :
    lindAt X n m ((constLU X M : Matrix (Fin n) (Fin n) (LaurentPolynomial C(X, ℂ))) * P
        * (↑(constLU X M)⁻¹ : Matrix (Fin n) (Fin n) (LaurentPolynomial C(X, ℂ)))) ρ
      = lindAt X n m P ρ := by
  obtain ⟨hLA, hLB, hAA, hAB, hUL, hUA⟩ := linBf_const_identities_bc X n m M P
  have hD : blockAllF X n (2 * m) (M : Matrix (Fin n) (Fin n) C(X, ℂ))
      * blockAllF X n (2 * m) (↑M⁻¹ : Matrix (Fin n) (Fin n) C(X, ℂ)) = 1 :=
    blockAllF_mul_inv X n (2 * m) M
  have hD' : blockAllF X n (2 * m) (↑M⁻¹ : Matrix (Fin n) (Fin n) C(X, ℂ))
      * blockAllF X n (2 * m) (M : Matrix (Fin n) (Fin n) C(X, ℂ)) = 1 :=
    blockAllF_inv_mul X n (2 * m) M
  have hproj : matPProj X ((2 * m + 1) * n) (linAf X n m)
        (linBf X n m ((constLU X M : Matrix (Fin n) (Fin n) (LaurentPolynomial C(X, ℂ))) * P
          * (↑(constLU X M)⁻¹ : Matrix (Fin n) (Fin n) (LaurentPolynomial C(X, ℂ))))) ρ
      = blockAllF X n (2 * m) (M : Matrix (Fin n) (Fin n) C(X, ℂ))
        * matPProj X ((2 * m + 1) * n) (linAf X n m) (linBf X n m P) ρ
        * blockAllF X n (2 * m) (↑M⁻¹ : Matrix (Fin n) (Fin n) C(X, ℂ)) := by
    have h := matPProj_conj (N := (2 * m + 1) * n) (A := linAf X n m) (B := linBf X n m P)
      (L := blockAllF X n (2 * m) (M : Matrix (Fin n) (Fin n) C(X, ℂ))) hUA ρ
    rw [ringInverse_blockAllF X n (2 * m) M] at h
    rw [hAA, hAB] at h
    exact h
  have hcls : cls (⟨(2 * m + 1) * n, blockAllF X n (2 * m) (M : Matrix (Fin n) (Fin n) C(X, ℂ))
        * matPProj X ((2 * m + 1) * n) (linAf X n m) (linBf X n m P) ρ
        * blockAllF X n (2 * m) (↑M⁻¹ : Matrix (Fin n) (Fin n) C(X, ℂ))⟩ : Mat C(X, ℂ))
      = cls (⟨(2 * m + 1) * n,
          matPProj X ((2 * m + 1) * n) (linAf X n m) (linBf X n m P) ρ⟩ : Mat C(X, ℂ)) := by
    have h := cls_conj_unit (N := (2 * m + 1) * n)
      (D := ⟨blockAllF X n (2 * m) (M : Matrix (Fin n) (Fin n) C(X, ℂ)),
        blockAllF X n (2 * m) (↑M⁻¹ : Matrix (Fin n) (Fin n) C(X, ℂ)), hD, hD'⟩)
      (P := matPProj X ((2 * m + 1) * n) (linAf X n m) (linBf X n m P) ρ)
    simpa using h
  unfold lindAt
  rw [hproj, hcls]

/-- The pullback of a unit of matrices over `C(X, ℂ)` to `X × S¹`. -/
noncomputable def cnstU (X : Type) [TopologicalSpace X] {n : ℕ}
    (M : (Matrix (Fin n) (Fin n) C(X, ℂ))ˣ) :
    (Matrix (Fin n) (Fin n) C(X × Sph ℂ, ℂ))ˣ :=
  unitPull (ContinuousMap.fst : C(X × Sph ℂ, X)) M

@[simp] lemma cnstU_mul (X : Type) [TopologicalSpace X] {n : ℕ}
    (M N : (Matrix (Fin n) (Fin n) C(X, ℂ))ˣ) :
    cnstU X (M * N) = cnstU X M * cnstU X N := map_mul _ _ _

@[simp] lemma cnstU_inv (X : Type) [TopologicalSpace X] {n : ℕ}
    (M : (Matrix (Fin n) (Fin n) C(X, ℂ))ˣ) :
    cnstU X M⁻¹ = (cnstU X M)⁻¹ := unitPull_inv _ _

@[simp] lemma cnstU_val (X : Type) [TopologicalSpace X] {n : ℕ}
    (M : (Matrix (Fin n) (Fin n) C(X, ℂ))ˣ) :
    ((cnstU X M : (Matrix (Fin n) (Fin n) C(X × Sph ℂ, ℂ))ˣ) :
        Matrix (Fin n) (Fin n) C(X × Sph ℂ, ℂ)) = Work.KT.Fund.pullMat X M := rfl

/-- **`Nval` is unchanged by left multiplication by a constant unit.** -/
theorem Nval_mul_const_left (X : Type) [TopologicalSpace X] [CompactSpace X] [T2Space X]
    (n : ℕ) (M : (Matrix (Fin n) (Fin n) C(X, ℂ))ˣ)
    (u : (Matrix (Fin n) (Fin n) C(X × Sph ℂ, ℂ))ˣ) :
    Nval X n (cnstU X M * u) = Nval X n u := by
  obtain ⟨Hu, hu0, hu1⟩ := (adata X n u).hom
  have h1mat : (unitEval 1 Hu : Matrix (Fin n) (Fin n) C(X × Sph ℂ, ℂ))
      = (adata X n u).P.map (Work.KT.laurentMap X) := by
    ext i j p
    obtain ⟨x, z⟩ := p
    rw [unitEval_apply]
    exact hu1 i j x z
  have hbQ : ∀ (i j : Fin n) (k : ℤ), ((adata X n u).m : ℤ) < k ∨ k < -((adata X n u).m : ℤ) →
      (((↑(constLU X M) : Matrix (Fin n) (Fin n) (LaurentPolynomial C(X, ℂ)))
        * (adata X n u).P) i j).coeff k = 0 :=
    bound_constLM_mul_lp n (adata X n u).m (M : Matrix (Fin n) (Fin n) C(X, ℂ))
      (adata X n u).P (adata X n u).bound
  have hadm : ∀ z : ℂ, (adata X n u).rho ≤ ‖z‖ → ‖z‖ ≤ 1 →
      IsUnit (z • linAf X n (adata X n u).m
        + linBf X n (adata X n u).m ((↑(constLU X M) :
            Matrix (Fin n) (Fin n) (LaurentPolynomial C(X, ℂ))) * (adata X n u).P)) := by
    intro z h1 h2
    obtain ⟨hLA, hLB, hAA, hAB, hUL, hUA⟩ :=
      linBf_const_identities_bc X n (adata X n u).m M (adata X n u).P
    have hkey : blockLastF X n (2 * (adata X n u).m) (M : Matrix (Fin n) (Fin n) C(X, ℂ))
          * (z • linAf X n (adata X n u).m
              + linBf X n (adata X n u).m (adata X n u).P)
        = z • linAf X n (adata X n u).m
          + linBf X n (adata X n u).m ((↑(constLU X M) :
              Matrix (Fin n) (Fin n) (LaurentPolynomial C(X, ℂ))) * (adata X n u).P) := by
      rw [mul_add, mul_smul_comm, hLA, hLB]
    rw [← hkey]
    exact hUL.mul ((adata X n u).adm z h1 h2)
  have hsl0 : unitEval 0 (unitConst (cnstU X M) * Hu) = cnstU X M * u := by
    rw [unitEval_mul, unitEval_const,
      unitEval_zero_eq (X × Sph ℂ) Hu u (fun i j p => by
        obtain ⟨x, z⟩ := p
        exact hu0 i j x z)]
  have hK0 : ∀ (i j : Fin n) (x : X) (z : Sph ℂ),
      (unitConst (cnstU X M) * Hu : Matrix (Fin n) (Fin n) C((X × Sph ℂ) × unitInterval, ℂ))
          i j ((x, z), 0)
        = (cnstU X M * u : Matrix (Fin n) (Fin n) C(X × Sph ℂ, ℂ)) i j (x, z) :=
    fun i j x z => unitEval_eq_entries (X × Sph ℂ) 0 (unitConst (cnstU X M) * Hu)
      (cnstU X M * u) hsl0 i j (x, z)
  have hsl1 : (unitEval 1 (unitConst (cnstU X M) * Hu) :
        Matrix (Fin n) (Fin n) C(X × Sph ℂ, ℂ))
      = (((↑(constLU X M) : Matrix (Fin n) (Fin n) (LaurentPolynomial C(X, ℂ)))
          * (adata X n u).P).map (Work.KT.laurentMap X)) := by
    rw [unitEval_mul, unitEval_const, Units.val_mul, h1mat, cnstU_val, constLU_coe,
      ← laurentMap_constLM, ← Matrix.map_mul]
  have hK1 : ∀ (i j : Fin n) (x : X) (z : Sph ℂ),
      (unitConst (cnstU X M) * Hu : Matrix (Fin n) (Fin n) C((X × Sph ℂ) × unitInterval, ℂ))
          i j ((x, z), 1)
        = (((↑(constLU X M) : Matrix (Fin n) (Fin n) (LaurentPolynomial C(X, ℂ)))
            * (adata X n u).P).map (Work.KT.laurentMap X)) i j (x, z) := by
    intro i j x z
    show (unitEval 1 (unitConst (cnstU X M) * Hu) :
        Matrix (Fin n) (Fin n) C(X × Sph ℂ, ℂ)) i j (x, z) = _
    exact congrArg (fun A : Matrix (Fin n) (Fin n) C(X × Sph ℂ, ℂ) => A i j (x, z)) hsl1
  rw [Nval_eq_of_hom X n (cnstU X M * u)
    ((↑(constLU X M) : Matrix (Fin n) (Fin n) (LaurentPolynomial C(X, ℂ)))
      * (adata X n u).P) (adata X n u).m hbQ (adata X n u).rho_pos (adata X n u).rho_le hadm
    (unitConst (cnstU X M) * Hu) hK0 hK1]
  exact lindAt_mul_const_left X n (adata X n u).m M (adata X n u).P (adata X n u).rho

/-- **`Nval` is unchanged by conjugating by a constant unit:** `M⁻¹ · u · M` has the same index
as `u`. -/
theorem Nval_conj (X : Type) [TopologicalSpace X] [CompactSpace X] [T2Space X]
    (n : ℕ) (M : (Matrix (Fin n) (Fin n) C(X, ℂ))ˣ)
    (u : (Matrix (Fin n) (Fin n) C(X × Sph ℂ, ℂ))ˣ) :
    Nval X n (cnstU X M⁻¹ * u * cnstU X M) = Nval X n u := by
  obtain ⟨Hu, hu0, hu1⟩ := (adata X n u).hom
  have h1mat : (unitEval 1 Hu : Matrix (Fin n) (Fin n) C(X × Sph ℂ, ℂ))
      = (adata X n u).P.map (Work.KT.laurentMap X) := by
    ext i j p
    obtain ⟨x, z⟩ := p
    rw [unitEval_apply]
    exact hu1 i j x z
  have hbU : ∀ (i j : Fin n) (k : ℤ), ((adata X n u).m : ℤ) < k ∨ k < -((adata X n u).m : ℤ) →
      (((adata X n u).P * constLM X (M : Matrix (Fin n) (Fin n) C(X, ℂ))) i j).coeff k = 0 :=
    bound_mul_constLM_lp n (adata X n u).m (M : Matrix (Fin n) (Fin n) C(X, ℂ))
      (adata X n u).P (adata X n u).bound
  have hbQ' : ∀ (i j : Fin n) (k : ℤ), ((adata X n u).m : ℤ) < k ∨ k < -((adata X n u).m : ℤ) →
      ((constLM X (↑M⁻¹ : Matrix (Fin n) (Fin n) C(X, ℂ))
        * ((adata X n u).P * constLM X (M : Matrix (Fin n) (Fin n) C(X, ℂ)))) i j).coeff k = 0 :=
    bound_constLM_mul_lp n (adata X n u).m (↑M⁻¹ : Matrix (Fin n) (Fin n) C(X, ℂ))
      ((adata X n u).P * constLM X (M : Matrix (Fin n) (Fin n) C(X, ℂ))) hbU
  have hbQ : ∀ (i j : Fin n) (k : ℤ), ((adata X n u).m : ℤ) < k ∨ k < -((adata X n u).m : ℤ) →
      ((constLM X (↑M⁻¹ : Matrix (Fin n) (Fin n) C(X, ℂ))
        * (adata X n u).P * constLM X (M : Matrix (Fin n) (Fin n) C(X, ℂ))) i j).coeff k = 0 := by
    intro i j k hk
    simpa only [Matrix.mul_assoc] using hbQ' i j k hk
  have hAdm : ∀ z : ℂ, (adata X n u).rho ≤ ‖z‖ → ‖z‖ ≤ 1 →
      IsUnit (z • linAf X n (adata X n u).m + linBf X n (adata X n u).m
        ((↑(constLU X M⁻¹) : Matrix (Fin n) (Fin n) (LaurentPolynomial C(X, ℂ)))
          * (adata X n u).P
          * (↑(constLU X M) : Matrix (Fin n) (Fin n) (LaurentPolynomial C(X, ℂ))))) := by
    intro z h1 h2
    obtain ⟨hLA, hLB, hAA, hAB, hUL, hUA⟩ :=
      linBf_const_identities_bc X n (adata X n u).m M⁻¹ (adata X n u).P
    have hA' : blockAllF X n (2 * (adata X n u).m) (↑M⁻¹ : Matrix (Fin n) (Fin n) C(X, ℂ))
        * linAf X n (adata X n u).m
        * blockAllF X n (2 * (adata X n u).m) (M : Matrix (Fin n) (Fin n) C(X, ℂ))
        = linAf X n (adata X n u).m := hAA
    have hB' : blockAllF X n (2 * (adata X n u).m) (↑M⁻¹ : Matrix (Fin n) (Fin n) C(X, ℂ))
        * linBf X n (adata X n u).m (adata X n u).P
        * blockAllF X n (2 * (adata X n u).m) (M : Matrix (Fin n) (Fin n) C(X, ℂ))
        = linBf X n (adata X n u).m ((↑(constLU X M⁻¹) :
              Matrix (Fin n) (Fin n) (LaurentPolynomial C(X, ℂ)))
            * (adata X n u).P
            * (↑(constLU X M) : Matrix (Fin n) (Fin n) (LaurentPolynomial C(X, ℂ)))) := hAB
    have hzA : blockAllF X n (2 * (adata X n u).m) (↑M⁻¹ : Matrix (Fin n) (Fin n) C(X, ℂ))
        * (z • linAf X n (adata X n u).m)
        * blockAllF X n (2 * (adata X n u).m) (M : Matrix (Fin n) (Fin n) C(X, ℂ))
        = z • linAf X n (adata X n u).m := by
      rw [mul_smul_comm, smul_mul_assoc, hA']
    obtain ⟨-, -, -, -, -, hUM⟩ :=
      linBf_const_identities_bc X n (adata X n u).m M (adata X n u).P
    have hkey : blockAllF X n (2 * (adata X n u).m) (↑M⁻¹ : Matrix (Fin n) (Fin n) C(X, ℂ))
          * (z • linAf X n (adata X n u).m + linBf X n (adata X n u).m (adata X n u).P)
          * blockAllF X n (2 * (adata X n u).m) (M : Matrix (Fin n) (Fin n) C(X, ℂ))
        = z • linAf X n (adata X n u).m
          + linBf X n (adata X n u).m ((↑(constLU X M⁻¹) :
              Matrix (Fin n) (Fin n) (LaurentPolynomial C(X, ℂ)))
            * (adata X n u).P
            * (↑(constLU X M) : Matrix (Fin n) (Fin n) (LaurentPolynomial C(X, ℂ)))) := by
      simp only [mul_add, add_mul, hzA, hB']
    rw [← hkey]
    exact IsUnit.mul (IsUnit.mul hUA ((adata X n u).adm z h1 h2)) hUM
  have hsl0 : unitEval 0 (unitConst (cnstU X M⁻¹) * Hu * unitConst (cnstU X M))
      = cnstU X M⁻¹ * u * cnstU X M := by
    rw [unitEval_mul, unitEval_mul, unitEval_const, unitEval_const,
      unitEval_zero_eq (X × Sph ℂ) Hu u (fun i j p => by
        obtain ⟨x, z⟩ := p
        exact hu0 i j x z)]
  have hK0 : ∀ (i j : Fin n) (x : X) (z : Sph ℂ),
      (unitConst (cnstU X M⁻¹) * Hu * unitConst (cnstU X M) :
          Matrix (Fin n) (Fin n) C((X × Sph ℂ) × unitInterval, ℂ)) i j ((x, z), 0)
        = (cnstU X M⁻¹ * u * cnstU X M : Matrix (Fin n) (Fin n) C(X × Sph ℂ, ℂ))
            i j (x, z) :=
    fun i j x z => unitEval_eq_entries (X × Sph ℂ) 0
      (unitConst (cnstU X M⁻¹) * Hu * unitConst (cnstU X M)) (cnstU X M⁻¹ * u * cnstU X M)
      hsl0 i j (x, z)
  have hsl1 : (unitEval 1 (unitConst (cnstU X M⁻¹) * Hu * unitConst (cnstU X M)) :
        Matrix (Fin n) (Fin n) C(X × Sph ℂ, ℂ))
      = (((↑(constLU X M⁻¹) : Matrix (Fin n) (Fin n) (LaurentPolynomial C(X, ℂ)))
          * (adata X n u).P
          * (↑(constLU X M) : Matrix (Fin n) (Fin n) (LaurentPolynomial C(X, ℂ)))).map
          (Work.KT.laurentMap X)) := by
    rw [unitEval_mul, unitEval_mul, unitEval_const, unitEval_const, Units.val_mul, Units.val_mul,
      h1mat, cnstU_val, cnstU_val, constLU_coe, constLU_coe,
      ← laurentMap_constLM, ← laurentMap_constLM,
      ← Matrix.map_mul, ← Matrix.map_mul]
  have hK1 : ∀ (i j : Fin n) (x : X) (z : Sph ℂ),
      (unitConst (cnstU X M⁻¹) * Hu * unitConst (cnstU X M) :
          Matrix (Fin n) (Fin n) C((X × Sph ℂ) × unitInterval, ℂ)) i j ((x, z), 1)
        = (((↑(constLU X M⁻¹) : Matrix (Fin n) (Fin n) (LaurentPolynomial C(X, ℂ)))
            * (adata X n u).P
            * (↑(constLU X M) : Matrix (Fin n) (Fin n) (LaurentPolynomial C(X, ℂ)))).map
            (Work.KT.laurentMap X)) i j (x, z) := by
    intro i j x z
    show (unitEval 1 (unitConst (cnstU X M⁻¹) * Hu * unitConst (cnstU X M)) :
        Matrix (Fin n) (Fin n) C(X × Sph ℂ, ℂ)) i j (x, z) = _
    exact congrArg (fun A : Matrix (Fin n) (Fin n) C(X × Sph ℂ, ℂ) => A i j (x, z)) hsl1
  rw [Nval_eq_of_hom X n (cnstU X M⁻¹ * u * cnstU X M)
    ((↑(constLU X M⁻¹) : Matrix (Fin n) (Fin n) (LaurentPolynomial C(X, ℂ)))
      * (adata X n u).P
      * (↑(constLU X M) : Matrix (Fin n) (Fin n) (LaurentPolynomial C(X, ℂ)))) (adata X n u).m hbQ
    (adata X n u).rho_pos (adata X n u).rho_le hAdm
    (unitConst (cnstU X M⁻¹) * Hu * unitConst (cnstU X M)) hK0 hK1]
  exact lindAt_conj X n (adata X n u).m M⁻¹ (adata X n u).P (adata X n u).rho

/-- **The invariance clause**: `Nval` is unchanged by multiplying on the left and right by units
that extend over the disc. -/
theorem bott_index_inv (X : Type) [TopologicalSpace X] [CompactSpace X] [T2Space X]
    (n : ℕ) (u w : (Matrix (Fin n) (Fin n) C(X × Sph ℂ, ℂ))ˣ)
    (g₀ g₁ : (Matrix (Fin n) (Fin n) C(X × Ball ℂ, ℂ))ˣ)
    (hw : (w : Matrix (Fin n) (Fin n) C(X × Sph ℂ, ℂ))
      = (g₀ : Matrix (Fin n) (Fin n) C(X × Ball ℂ, ℂ)).map (fun f => Fund.bdryRestrict X f)
        * (u : Matrix (Fin n) (Fin n) C(X × Sph ℂ, ℂ))
        * (g₁ : Matrix (Fin n) (Fin n) C(X × Ball ℂ, ℂ)).map (fun f => Fund.bdryRestrict X f)) :
    Nval X n w = Nval X n u := by
  obtain ⟨M₀, M₁, H, hH0, hH1⟩ := disc_product_homotopy X n g₀ g₁ u w hw
  have h1 : Nval X n w = Nval X n (cnstU X M₀ * u * cnstU X M₁) :=
    (Nval_hom_inv X n (cnstU X M₀ * u * cnstU X M₁) w H hH0 hH1).symm
  have h2 : Nval X n (cnstU X M₀ * u * cnstU X M₁) = Nval X n u := by
    have hassoc : cnstU X M₀ * u * cnstU X M₁
        = cnstU X (M₀ * M₁) * (cnstU X M₁⁻¹ * u * cnstU X M₁) := by
      rw [cnstU_mul, cnstU_inv]
      group
    rw [hassoc,
      Nval_mul_const_left X n (M₀ * M₁) (cnstU X M₁⁻¹ * u * cnstU X M₁),
      Nval_conj X n M₁ u]
  rw [h1, h2]

/-! ## The theorem -/

/-- The Bott index (the K(X)-valued winding number, i.e. minus the index bundle of the Toeplitz
family): a function on units over `X × S¹` that is unchanged by multiplying on either side by
units extending over the disc, and equals `[P]` on `(1 − P) + z·P`. -/
theorem bott_index (X : Type) [TopologicalSpace X] [CompactSpace X] [T2Space X] :
    ∃ N : ∀ n : ℕ, (Matrix (Fin n) (Fin n) C(X × Sph ℂ, ℂ))ˣ → K0 C(X, ℂ),
      (∀ (n : ℕ) (u w : (Matrix (Fin n) (Fin n) C(X × Sph ℂ, ℂ))ˣ)
          (g₀ g₁ : (Matrix (Fin n) (Fin n) C(X × Ball ℂ, ℂ))ˣ),
          (w : Matrix (Fin n) (Fin n) C(X × Sph ℂ, ℂ)) =
            (g₀ : Matrix (Fin n) (Fin n) C(X × Ball ℂ, ℂ)).map (fun f => Fund.bdryRestrict X f) *
              (u : Matrix (Fin n) (Fin n) C(X × Sph ℂ, ℂ)) *
              (g₁ : Matrix (Fin n) (Fin n) C(X × Ball ℂ, ℂ)).map
                (fun f => Fund.bdryRestrict X f) →
          N n w = N n u) ∧
      ∀ (n : ℕ) (P : Matrix (Fin n) (Fin n) C(X, ℂ)), P * P = P →
        ∀ u : (Matrix (Fin n) (Fin n) C(X × Sph ℂ, ℂ))ˣ,
          (u : Matrix (Fin n) (Fin n) C(X × Sph ℂ, ℂ)) =
            Fund.pullMat X (1 - P) + (zUnit X : C(X × Sph ℂ, ℂ)) • Fund.pullMat X P →
          N n u = cls (⟨n, P⟩ : Mat C(X, ℂ)) := by
  refine ⟨fun n u => Nval X n u, ?_, ?_⟩
  · intro n u w g₀ g₁ hw
    exact bott_index_inv X n u w g₀ g₁ hw
  · intro n P hP u hu
    exact Nval_normalised X n P hP u hu

end

end Work.KT.FP

