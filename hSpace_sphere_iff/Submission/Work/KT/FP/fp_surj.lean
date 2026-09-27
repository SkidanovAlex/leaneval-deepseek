import Mathlib
import Submission.Work.KT.Defs
import Submission.Work.KT.Fund.AssemblyDefs
import Submission.Work.KT.Fund.Disc
import Submission.Work.KT.Fund.Geom
import Submission.Work.KT.Fund.Basic
import Submission.Work.KT.k0_basic
import Submission.Work.KT.kappa_span
import Submission.Work.KT.Fund.kappa_one
import Submission.Work.KT.EG.kappa_reduce

/-! Guidance from the project lead (the requester):

ROUTE: Submission/Work/KT/FP_README.md and DESIGN.md 'Addendum: fund_product split' (the lead's split of fund_product). CONVENTION: [Ring A] + explicit commutativity. Siblings run in parallel; fund_product = EG.fund_product_of_bott ... (fp_retract X).1 hrmul (fp_retract X).2 (fp_surj ...) (fp_inj ...).

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
   `recipB_inv_mul_graphB`. So `u⊕1 = g₀| (v⊕1) g₁|` with `g₀ = α₁⁻¹` and `g₁ = α₀`.
-/

namespace Work.KT.FP


/-! ## The two restriction lemmas

Let `r = bp^* : K0 C(X × S²) → K0 C(X)` be the restriction to the fibre over the base point
`pt = up 0`.  We need that every class killed by `r` is killed by both disc restrictions
`pullUp`, `pullDn : C(X × S², ℂ) →+* C(X × D, ℂ)`:

* `ev0 ∘ pullUp = r` (`ev0 = zeroX^*` is evaluation at the centre of the disc), so
  `r y = 0` gives `ev0 (pullUp y) = 0`, and `pullUp y = sD (ev0 (pullUp y))` by `Fund.sD_ev0`,
  where `sD = fst^* : K0 C(X) → K0 C(X × D)`;
* the boundary restrictions of `pullUp y` and `pullDn y` agree
  (`Fund.bdryRestrict_pullUp_eq_pullDn`), so `bdryRestrict (pullDn y) = 0`; writing
  `pullDn y = sD a` (`Fund.sD_ev0`) and using `bdryRestrict ∘ sD = π^*` with `π : X × S¹ → X`
  the projection, the section `x ↦ (x, 1)` shows that `π^*` is injective, hence `a = 0`.
-/

/-- Evaluation of `pullAlg` (`pullAlg g f = f ∘ g`; the analogue of `Fund.pullAlg_apply'`, which
lives in a module outside this file's import closure). -/
lemma pullAlg_apply_comp {Y Z : Type} [TopologicalSpace Y] [TopologicalSpace Z] (g : C(Y, Z))
    (f : C(Z, ℂ)) : pullAlg g f = f.comp g :=
  ContinuousMap.compStarAlgHom'_apply ℂ ℂ g f

/-- The point `1` of the unit circle `S¹`. -/
def oneSphPt : Sph ℂ :=
  ⟨(1 : ℂ), by rw [Metric.mem_sphere, dist_eq_norm, sub_zero]; norm_num⟩

/-- The section `x ↦ (x, 1)` of `X × S¹ → X`. -/
def oneSph (X : Type) [TopologicalSpace X] : C(X, X × Sph ℂ) where
  toFun x := (x, oneSphPt)
  continuous_toFun := continuous_id.prodMk continuous_const

lemma projSph_comp_oneSph (X : Type) [TopologicalSpace X] :
    (ContinuousMap.fst : C(X × Sph ℂ, X)).comp (oneSph X) = ContinuousMap.id X := by
  ext x
  rfl

/-- `(π^* ∘ (x ↦ (x,1))^*) = id`, so `K0` of the projection `X × S¹ → X` is injective. -/
lemma pullAlg_projSph_comp_oneSph (X : Type) [TopologicalSpace X] :
    ((pullAlg (oneSph X)).toRingHom.comp
        (pullAlg (ContinuousMap.fst : C(X × Sph ℂ, X))).toRingHom) = RingHom.id (C(X, ℂ)) := by
  rw [← Fund.pullAlg_comp_toRingHom (oneSph X) (ContinuousMap.fst : C(X × Sph ℂ, X)),
    projSph_comp_oneSph X, Fund.pullAlg_id X]
  rfl

/-- `ev0 ∘ pullUp = r`, where `ev0` is evaluation at the centre of the disc and `r = bp^*`. -/
lemma pullUp_comp_zeroX (X : Type) [TopologicalSpace X] :
    (pullAlg (Fund.zeroX X)).toRingHom.comp (Fund.pullUp X)
      = (pullAlg (Fund.bp X)).toRingHom := by
  refine RingHom.ext fun f => ContinuousMap.ext fun x => ?_
  change pullAlg (Fund.zeroX X) (Fund.pullUp X f) x = pullAlg (Fund.bp X) f x
  rw [pullAlg_apply_comp (Fund.zeroX X) (Fund.pullUp X f), pullAlg_apply_comp (Fund.bp X) f,
    ContinuousMap.comp_apply, ContinuousMap.comp_apply, Fund.pullUp_apply]
  refine congrArg f ?_
  refine Prod.ext rfl ?_
  show Fund.up (Fund.zeroX X x).2 = Fund.up (0 : Ball ℂ)
  exact congrArg Fund.up (Subtype.ext rfl)

/-- `bdryRestrict ∘ sD = π^*`, where `sD = fst^* : K0 C(X) → K0 C(X × D)` and `π : X × S¹ → X`
is the projection. -/
lemma bdryRestrict_comp_projX (X : Type) [TopologicalSpace X] :
    (Fund.bdryRestrict X).comp (pullAlg (Fund.projX X)).toRingHom
      = (pullAlg (ContinuousMap.fst : C(X × Sph ℂ, X))).toRingHom := by
  refine RingHom.ext fun f => ContinuousMap.ext fun p => ?_
  simp [pullAlg, Fund.bdryRestrict, Fund.projX]

/-- Every class killed by the base-point restriction `r` is killed by the upper disc restriction
`pullUp`. -/
lemma ker_r_subset_ker_pullUp (X : Type) [TopologicalSpace X] [CompactSpace X] [T2Space X] :
    ∀ y : K0 C(X × S2, ℂ),
      K0.mapA (A := C(X × S2, ℂ)) (B := C(X, ℂ)) (pullAlg (Fund.bp X)) y = 0 →
      K0.map (Fund.pullUp X) y = 0 := by
  intro y hy
  have h1 : Fund.ev0 X (K0.map (Fund.pullUp X) y) = 0 := by
    show K0.map (pullAlg (Fund.zeroX X)).toRingHom (K0.map (Fund.pullUp X) y) = 0
    rw [← K0.map_comp_apply (Fund.pullUp X) (pullAlg (Fund.zeroX X)).toRingHom y,
      pullUp_comp_zeroX X]
    exact hy
  calc K0.map (Fund.pullUp X) y
      = Fund.sD X (Fund.ev0 X (K0.map (Fund.pullUp X) y)) := (Fund.sD_ev0 X _).symm
    _ = Fund.sD X 0 := by rw [h1]
    _ = 0 := map_zero _

/-- Every class killed by the base-point restriction `r` is killed by the lower disc restriction
`pullDn`. -/
lemma ker_r_subset_ker_pullDn (X : Type) [TopologicalSpace X] [CompactSpace X] [T2Space X] :
    ∀ y : K0 C(X × S2, ℂ),
      K0.mapA (A := C(X × S2, ℂ)) (B := C(X, ℂ)) (pullAlg (Fund.bp X)) y = 0 →
      K0.map (Fund.pullDn X) y = 0 := by
  intro y hy
  have hUp : K0.map (Fund.pullUp X) y = 0 := ker_r_subset_ker_pullUp X y hy
  -- the two boundary restrictions agree, so the boundary of `pullDn y` vanishes
  have hcomp : (Fund.bdryRestrict X).comp (Fund.pullUp X)
      = (Fund.bdryRestrict X).comp (Fund.pullDn X) :=
    RingHom.ext fun f => Fund.bdryRestrict_pullUp_eq_pullDn X f
  have hb : K0.map (Fund.bdryRestrict X) (K0.map (Fund.pullDn X) y) = 0 := by
    rw [← K0.map_comp_apply (Fund.pullDn X) (Fund.bdryRestrict X) y, ← hcomp,
      K0.map_comp_apply (Fund.pullUp X) (Fund.bdryRestrict X) y, hUp, map_zero]
  -- write `pullDn y = sD a` and compute the boundary of `sD a` as `π^* a`
  have hkey : K0.map (pullAlg (ContinuousMap.fst : C(X × Sph ℂ, X))).toRingHom
      (Fund.ev0 X (K0.map (Fund.pullDn X) y)) = 0 := by
    have h := hb
    rw [← Fund.sD_ev0 X (K0.map (Fund.pullDn X) y)] at h
    change K0.map (Fund.bdryRestrict X)
      (K0.map (pullAlg (Fund.projX X)).toRingHom
        (Fund.ev0 X (K0.map (Fund.pullDn X) y))) = 0 at h
    rw [← K0.map_comp_apply (pullAlg (Fund.projX X)).toRingHom (Fund.bdryRestrict X)
      (Fund.ev0 X (K0.map (Fund.pullDn X) y)), bdryRestrict_comp_projX X] at h
    exact h
  -- `π^*` is injective, so `a = 0`
  have ha : Fund.ev0 X (K0.map (Fund.pullDn X) y) = 0 := by
    have h := congrArg (K0.map (pullAlg (oneSph X)).toRingHom) hkey
    rw [map_zero] at h
    rw [← K0.map_comp_apply (pullAlg (ContinuousMap.fst : C(X × Sph ℂ, X))).toRingHom
      (pullAlg (oneSph X)).toRingHom (Fund.ev0 X (K0.map (Fund.pullDn X) y))] at h
    rw [pullAlg_projSph_comp_oneSph X, K0.map_id_apply] at h
    exact h
  calc K0.map (Fund.pullDn X) y
      = Fund.sD X (Fund.ev0 X (K0.map (Fund.pullDn X) y)) := (Fund.sD_ev0 X _).symm
    _ = Fund.sD X 0 := by rw [ha]
    _ = 0 := map_zero _

/-! ## The assembly

With `y ∈ ker r` written by `kappa_span` as `y = Σ cᵢ (κ(uᵢ) - κ(1))`, the trivial clutching
classes are `cls (Mat.one _ (N i))` (`Fund.kappa_one`) and the clutching reduction `hD` turns each
summand into `bottMap μ (bᵢ) = μ (s bᵢ) β`; the sum is reassembled using the `ℤ`-linearity of
`bottMap μ : A → M`, `a ↦ μ (s a) β` (`bottMap_add`, `bottMap_zsmul`, `bottMap_sum`). -/

/-- `bottMap μ : a ↦ μ (s a) β` is additive. -/
lemma bottMap_add (X : Type) [TopologicalSpace X] [CompactSpace X] [T2Space X]
    (μ : K0 C(X × S2, ℂ) →+ K0 C(X × S2, ℂ) →+ K0 C(X × S2, ℂ)) (a b : K0 C(X, ℂ)) :
    Fund.bottMap X μ (a + b) = Fund.bottMap X μ a + Fund.bottMap X μ b := by
  show μ (Fund.s X (a + b)) (Fund.beta X)
      = μ (Fund.s X a) (Fund.beta X) + μ (Fund.s X b) (Fund.beta X)
  rw [map_add (Fund.s X) a b, map_add μ (Fund.s X a) (Fund.s X b)]
  rfl

/-- `bottMap μ` is `ℤ`-linear. -/
lemma bottMap_zsmul (X : Type) [TopologicalSpace X] [CompactSpace X] [T2Space X]
    (μ : K0 C(X × S2, ℂ) →+ K0 C(X × S2, ℂ) →+ K0 C(X × S2, ℂ)) (c : ℤ) (a : K0 C(X, ℂ)) :
    Fund.bottMap X μ (c • a) = c • Fund.bottMap X μ a := by
  show μ (Fund.s X (c • a)) (Fund.beta X) = c • μ (Fund.s X a) (Fund.beta X)
  rw [map_zsmul (Fund.s X) c a, map_zsmul μ c (Fund.s X a)]
  rfl

/-- `bottMap μ` sends a finite `ℤ`-linear combination to the corresponding combination. -/
lemma bottMap_finset (X : Type) [TopologicalSpace X] [CompactSpace X] [T2Space X]
    (μ : K0 C(X × S2, ℂ) →+ K0 C(X × S2, ℂ) →+ K0 C(X × S2, ℂ))
    {ι : Type} (c : ι → ℤ) (bb : ι → K0 C(X, ℂ)) (s : Finset ι) :
    Fund.bottMap X μ (s.sum (fun i => c i • bb i))
      = s.sum (fun i => c i • Fund.bottMap X μ (bb i)) := by
  classical
  refine Finset.induction_on s ?_ ?_
  · simp only [Finset.sum_empty]
    rw [show Fund.bottMap X μ 0 = 0 from by simp only [Fund.bottMap, map_zero]; rfl]
  · intro a s ha ih
    rw [Finset.sum_insert ha, Finset.sum_insert ha, bottMap_add X μ, ih, bottMap_zsmul X μ]

/-- The version of `bottMap_finset` for a finite index type. -/
lemma bottMap_sum (X : Type) [TopologicalSpace X] [CompactSpace X] [T2Space X]
    (μ : K0 C(X × S2, ℂ) →+ K0 C(X × S2, ℂ) →+ K0 C(X × S2, ℂ))
    {ι : Type} [Fintype ι] (c : ι → ℤ) (bb : ι → K0 C(X, ℂ)) :
    Fund.bottMap X μ (∑ i, c i • bb i) = ∑ i, c i • Fund.bottMap X μ (bb i) :=
  bottMap_finset X μ c bb Finset.univ



/-- **Surjectivity half of Bott periodicity**, in the form taking the clutching reduction
`EG.kappa_reduce` as a hypothesis: every class killed by `r` is a multiple of the Bott class
`β = γ - 1` by a pulled-back class `s b`. -/
theorem fp_surj_of (X : Type) [TopologicalSpace X] [CompactSpace X] [T2Space X]
    (μ : K0 C(X × S2, ℂ) →+ K0 C(X × S2, ℂ) →+ K0 C(X × S2, ℂ)) (hμ : IsK0Mul μ)
    (hD : ∀ (n : ℕ) (u : (Matrix (Fin n) (Fin n) C(X × Sph ℂ, ℂ))ˣ),
      ∃ b : K0 C(X, ℂ),
        Fund.kappa X n u - cls (Mat.one C(X × S2, ℂ) n) = Fund.bottMap X μ b) :
    ∀ y : K0 C(X × S2, ℂ),
      K0.mapA (A := C(X × S2, ℂ)) (B := C(X, ℂ)) (pullAlg (Fund.bp X)) y = 0 →
      ∃ b : K0 C(X, ℂ),
        y = μ (K0.mapA (A := C(X, ℂ)) (B := C(X × S2, ℂ))
              (pullAlg (ContinuousMap.fst : C(X × S2, X))) b)
            (K0.mapA (A := C(S2, ℂ)) (B := C(X × S2, ℂ))
              (pullAlg (ContinuousMap.snd : C(X × S2, S2))) (cls hopfIdem) -
              cls (Mat.one C(X × S2, ℂ) 1)) := by
  intro y hy
  obtain ⟨m, N, u, c, hz⟩ := kappa_span X y (ker_r_subset_ker_pullUp X y hy)
    (ker_r_subset_ker_pullDn X y hy)
  let bb : Fin m → K0 C(X, ℂ) := fun i => (hD (N i) (u i)).choose
  have hbb : ∀ i : Fin m,
      Fund.kappa X (N i) (u i) - cls (Mat.one C(X × S2, ℂ) (N i)) = Fund.bottMap X μ (bb i) :=
    fun i => (hD (N i) (u i)).choose_spec
  have hz' : y = ∑ i, c i •
      (Fund.kappa X (N i) (u i) - cls (Mat.one C(X × S2, ℂ) (N i))) := by
    rw [hz]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Fund.kappa_one]
  refine ⟨∑ i, c i • bb i, ?_⟩
  change y = Fund.bottMap X μ (∑ i, c i • bb i)
  rw [hz', bottMap_sum X μ c bb]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [hbb i]



/-- Surjectivity half of Bott periodicity: every class killed by the base-point restriction is
`s(b)·(γ − 1)`. -/
theorem fp_surj (X : Type) [TopologicalSpace X] [CompactSpace X] [T2Space X]
    (μ : K0 C(X × S2, ℂ) →+ K0 C(X × S2, ℂ) →+ K0 C(X × S2, ℂ)) (hμ : IsK0Mul μ) :
    ∀ y : K0 C(X × S2, ℂ),
      K0.mapA (A := C(X × S2, ℂ)) (B := C(X, ℂ)) (pullAlg (Fund.bp X)) y = 0 →
      ∃ b : K0 C(X, ℂ),
        y = μ (K0.mapA (A := C(X, ℂ)) (B := C(X × S2, ℂ))
              (pullAlg (ContinuousMap.fst : C(X × S2, X))) b)
            (K0.mapA (A := C(S2, ℂ)) (B := C(X × S2, ℂ))
              (pullAlg (ContinuousMap.snd : C(X × S2, S2))) (cls hopfIdem) -
              cls (Mat.one C(X × S2, ℂ) 1)) :=
  fp_surj_of X μ hμ fun n u => EG.kappa_reduce X n u μ hμ

end Work.KT.FP
