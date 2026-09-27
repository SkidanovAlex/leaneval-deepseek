import Mathlib
import Submission.Work.KT.Defs
import Submission.Work.KT.Fund.AssemblyDefs
import Submission.Work.KT.ExtGen.r_s_bookkeeping
import Submission.Work.KT.EG.hopf_eval_one

/-! Guidance from the project lead (the requester):

ROUTE: Submission/Work/KT/FP_README.md and DESIGN.md 'Addendum: fund_product split' (the lead's split of fund_product). CONVENTION: [Ring A] + explicit commutativity. Siblings run in parallel; fund_product = EG.fund_product_of_bott ... (fp_retract X).1 hrmul (fp_retract X).2 (fp_surj ...) (fp_inj ...).

| 1 | `fp_retract` | 0.3–0.6k | low | `EG.hopf_eval_one` (proved), `k0_basic` | now |
| 2 | `fp_surj` | 0.5–1.5k | low–med | `kappa_span`, `Fund.kappa_one`, `Fund.Disc` (proved); `EG.kappa_reduce` (in flight, EG owner) | now; closes when `kappa_reduce` lands |
| 3 | `kappa_eq_disc` | 1.5–3k | medium | κ-calculus (proved) | now |
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
-/

namespace Work.KT.FP

noncomputable section

/-! ## Two auxiliary facts -/

/-- Along the structure map `ℂ → R`, `K₀` sends the class of the trivial line over `ℂ` to the class
of the trivial line over `R`. -/
lemma mapA_ofId_one (R : Type) [CommRing R] [Algebra ℂ R] :
    K0.mapA (Algebra.ofId ℂ R) (cls (Mat.one ℂ 1)) = cls (Mat.one R 1) := by
  have hmat : Mat.map (Algebra.ofId ℂ R).toRingHom (Mat.one ℂ 1) = Mat.one R 1 := by
    show (⟨1, (1 : Matrix (Fin 1) (Fin 1) ℂ).map (Algebra.ofId ℂ R).toRingHom⟩ : Mat R)
        = ⟨1, (1 : Matrix (Fin 1) (Fin 1) R)⟩
    congr 1
    ext i j
    fin_cases i
    fin_cases j
    simp [Matrix.map_apply]
  rw [K0.map_cls (Algebra.ofId ℂ R).toRingHom (Mat.one_isIdem ℂ 1), hmat]

/-- `bp^* ∘ snd^*` is the pull-back along `snd ∘ bp`, which is the constant map at the base point
`pt` of `S²`; as an algebra homomorphism that is evaluation at `pt` followed by the structure map
`ℂ → C(X, ℂ)`. -/
lemma pullAlg_bp_comp_snd (X : Type) [TopologicalSpace X] :
    (pullAlg (Fund.bp X)).comp (pullAlg (ContinuousMap.snd : C(X × S2, S2)))
      = (Algebra.ofId ℂ C(X, ℂ)).comp (evalC (Fund.pt : S2)) := by
  ext f x
  simp [pullAlg, Algebra.ofId_apply, Fund.bp, Fund.pt]

/-- The base-point restriction `r = bp^*` retracts the pull-back `s = fst^*`, and sends the Hopf
class to the trivial line: `r ∘ s = id` and `r(snd^*[H]) = [1₁]`. -/
theorem fp_retract (X : Type) [TopologicalSpace X] [CompactSpace X] [T2Space X] :
    (∀ a : K0 C(X, ℂ), K0.mapA (A := C(X × S2, ℂ)) (B := C(X, ℂ)) (pullAlg (Fund.bp X))
      (K0.mapA (A := C(X, ℂ)) (B := C(X × S2, ℂ))
        (pullAlg (ContinuousMap.fst : C(X × S2, X))) a) = a) ∧
    K0.mapA (A := C(X × S2, ℂ)) (B := C(X, ℂ)) (pullAlg (Fund.bp X))
      (K0.mapA (A := C(S2, ℂ)) (B := C(X × S2, ℂ))
        (pullAlg (ContinuousMap.snd : C(X × S2, S2))) (cls hopfIdem)) =
      cls (Mat.one C(X, ℂ) 1) := by
  refine ⟨fun a => ?_, ?_⟩
  · -- `r ∘ s = id`: `fst ∘ bp = id`, hence `pullAlg fst ≫ pullAlg bp = pullAlg id = id`.
    have hbp : (ContinuousMap.fst : C(X × S2, X)).comp (Fund.bp X) = ContinuousMap.id X := by
      ext x
      rfl
    have h1 : (pullAlg (Fund.bp X)).comp (pullAlg (ContinuousMap.fst : C(X × S2, X)))
        = AlgHom.id ℂ C(X, ℂ) := by
      rw [← Fund.pullAlg_comp (Fund.bp X) (ContinuousMap.fst : C(X × S2, X)), hbp,
        Fund.pullAlg_id]
    show K0.mapA (pullAlg (Fund.bp X))
      (K0.mapA (pullAlg (ContinuousMap.fst : C(X × S2, X))) a) = a
    rw [ba_mapA_comp_apply (pullAlg (ContinuousMap.fst : C(X × S2, X)))
      (pullAlg (Fund.bp X)) a, h1, ba_mapA_id_apply]
  · -- `r γ = 1`: `(snd ∘ bp)^*` is evaluation at `pt`, where the Hopf bundle is trivial.
    show K0.mapA (pullAlg (Fund.bp X))
      (K0.mapA (pullAlg (ContinuousMap.snd : C(X × S2, S2))) (cls hopfIdem))
        = cls (Mat.one C(X, ℂ) 1)
    rw [ba_mapA_comp_apply (pullAlg (ContinuousMap.snd : C(X × S2, S2)))
      (pullAlg (Fund.bp X)) (cls hopfIdem), pullAlg_bp_comp_snd X]
    rw [← ba_mapA_comp_apply (evalC (Fund.pt : S2)) (Algebra.ofId ℂ C(X, ℂ)) (cls hopfIdem)]
    rw [EG.hopf_eval_one (Fund.pt : S2)]
    exact mapA_ofId_one C(X, ℂ)

end

end Work.KT.FP
