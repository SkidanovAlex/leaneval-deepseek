import Mathlib
import Submission.Work.ThomBordism.Grassmann.Model
import Submission.Work.Thom.pontryaginClass_comap
import Submission.Work.Whitney.Stability
import Submission.Work.Whitney.chernClass_whitneySum_pullback_eq
import Submission.Work.Gen.Euler
import Submission.Work.Gen.ChernGenerator
import Submission.Work.Gen.ChernGeneratorTwo
import Submission.Work.Gen.TautDualPuncture
import Submission.Work.Projective.CP2Concrete
import Submission.Work.Projective.cp2H_cup_generates
import Submission.Work.Projective.cpnUV_homotopyEquiv_sphere
import Submission.Work.Thom.Euler
import Submission.Work.ThomBordism.Grassmann.p1RatNeZero_of_twoTwo
import Submission.Work.ThomBordism.Grassmann.probeP1Base
import Submission.Work.ThomBordism.Grassmann.zStd_pontryagin_ne_zero
import Submission.Work.ThomBordism.Grassmann.p1RatPuncture

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 400000

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000

/-!
# `p1Rat_ne_zero_via_probe` — state of the proof

Target: for `k, m ≥ 10`, `p1Rat k m = 1 ⊗ p₁(γ) ≠ 0` in `H⁴(G̃r_k(ℝ^{k+m});ℤ) ⊗ ℚ`.

## The plan, and which half is missing

The proof is a **probe**: a continuous map `σ : ℂP² → G̃r_k(ℝ^{k+m})` (complex line in `ℂ³ ↪ ℝ^{k+m}`,
plus a fixed oriented complement) whose pullback of the tautological bundle `γ` is
`realification(O(1)) ⊕ ε^{k-2}`.  Naturality of `p₁` (`Work.Thom.pontryaginClass_comap`), stability
(`Work.Whitney.pontryagin1_whitneySumR_trivial`) and `1 ⊗ x ≠ 0` for `x` non-torsion give

  `σ^*(1 ⊗ p₁(γ)) = 1 ⊗ p₁(realification(O(1)))`,

so it suffices that the latter be non-zero.  There are **two independent routes** to that:

**(A) The Whitney route** (`p₁(realification(L)) = ±c₁(L)⌣c₁(L)`): via the rank-`(1,1)` instance of
the Whitney sum formula `c₂(L ⊕ M) = c₁(L)⌣c₁(M)`, i.e. `Work.Whitney.TopClassMul` at `m = n = 1`
(`Submission/Work/Whitney/Hypotheses.lean`; the Gen-area consumer is
`Work.Gen.chernClass_lineC_two_of_core`, conditional on `WhCore`).  **This instance is the known
bottleneck of the whole workspace**: it is being pursued through Leray–Hirsch
(`Submission/Work/LerayHirsch/`, reduced there to `KunnethCP` + `LerayHirschGlue`) and is *not*
available in the tree.  It is the only genuinely missing classical input of route (A).

**(B) The Gysin route — NON-VANISHING ONLY, and it needs no Whitney input.**  The first Pontryagin
class of `realification(L)` is `-c₂(ℂ ⊗_ℝ L_ℝ)` (`Work.Thom.pontryaginClass`), and for a complex
line bundle `ℂ ⊗_ℝ L_ℝ ≅ L ⊕ L̄`; so it suffices that the *top* Chern class `c₂` of the rank-`2`
complex bundle `E := ℂ ⊗_ℝ L_ℝ` be non-zero — i.e. that the Euler class of the rank-`4` real bundle
`E_ℝ = L_ℝ ⊕ L_ℝ` be non-zero.  The Gysin sequence of `E_ℝ` over `ℂP²` reads
`H⁰(ℂP²) --∪e--> H⁴(ℂP²) → H⁴(E_ℝ∖0) → H¹(ℂP²) = 0`, and `H⁴(ℂP²;ℤ) = ℤ` with generator `u²`
(**proved below**, `gen_uSq_two_span`, by exactly the Gysin argument that
`Work.Gen.uSq_span` uses for `ℂP⁴`).  Hence **`e ≠ 0` as soon as `H⁴(E_ℝ∖0) = 0`** — and that
vanishing is a purely topological statement about a sphere bundle, *not* a Whitney-formula
statement.  The standard route to it: `E_ℝ ≅ L_ℝ ⊕ L_ℝ` (for `L = O(1)`), and `S(L_ℝ) ≅ S⁵` (the
unit vectors in the tautological line are the unit vectors of `ℂ³`), so the unit sphere bundle of
`E_ℝ ≃ S(L_ℝ) * S(L_ℝ) ≃ S⁵ * S⁵ ≃ S¹¹` and `H⁴(S¹¹) = 0`.  (A second, more elementary route to
the same vanishing: Mayer–Vietoris on the two pieces `(L∖0) ⊕ L` and `L ⊕ (L∖0)`, whose
intersection has `H³ = 0`.)

## What is proved in this file (sorry-free, axioms ⊆ {propext, Classical.choice, Quot.sound})

* `tmul_one_ne_zero_of_iso_int` — a class of a `ℤ`-module isomorphic to `ℤ` survives `⊗ ℚ`;
* `puncturedComplexHZeroOf`, `puncturedTautDualTwoHZero` — `H^k(ℂ³∖0) = 0` off degrees `0, 5`
  (from the Mayer–Vietoris computation of the projective chapter);
* `cp2T`, `cp2_gysin_surj` — the Gysin sequence of `O(1)` over `ℂP²`;
* `gen_uSq_two_span` — **`H⁴(ℂP²;ℤ) = ℤ⟨u²⟩ = ℤ⟨c₁(O(1))²⟩`** (no Whitney input!);
* `gen_uSq_two_ne_zero`, `cp2CohFourEquiv`, `rat_uSq_two_ne_zero` — **`1 ⊗ u² ≠ 0`**.

## What is missing

1. the probe `σ : ℂP² → G̃r_k(ℝ^{k+m})` and its bundle iso (delegation-ready statement:
   `Work.Gen.probe_CP2_OG24` + `Work.ThomBordism.Grassmann.probe_sumMap`, reviewed and approved;
   the composite is a `BundleIso.comap`/`trans` away);
2. `p₁(realification(tautDual 2)) ≠ 0` — route (A) (`Work.Whitney.TopClassMul` at `(1,1)`, the
   workspace bottleneck) or route (B) (`H⁴` of the sphere bundle of `L_ℝ ⊕ L_ℝ`, needing the
   join/Mayer–Vietoris computation above).

The statement `p1Rat_ne_zero_via_probe` itself is **true** (both routes are mathematically valid).

## The probe: ingredients located (API check, ready to write)

* the target of the direct-sum step is `OG (2 + κ) m` with fibre type `Fin (2 + κ)`: state the bundle
  isomorphism against `Work.Whitney.whitneySumR γ_{2,4} (trivial (Fin κ))`, whose fibre is
  `EuclideanSpace ℝ (Fin (2 + κ))` — **no degree cast is needed** (this is why one works with
  `2 + κ` rather than `k`);  transport to `Fin k` only at the very end if at all;
* the fixed orthonormal `κ`-frame is `(EuclideanSpace.basisFun (Fin κ) ℝ).orthonormal`, embedded in
  `Amb ((2 + κ) + m)` along `Fin.natAdd (2 + κ)`, and `Amb 4 ↪ Amb ((2 + κ) + m)` along
  `Fin.castAdd m ∘ Fin.castAdd κ` (`Fin.castAdd`, `Fin.natAdd` are the index maps);
* `Work.Thom.bundleComap_comp` composes the two probe maps into one (`τ.comp σ`);
* the assembly only needs: `Work.Thom.pontryaginClass_comap` (naturality),
  `Work.Thom.chernClass_BundleIso` (iso-invariance of the Chern classes),
  `Work.Thom.complexificationCore_bundleComap`, and the stability results
  `Work.Whitney.pontryagin1_whitneySumR_trivial` /
  `Work.Thom.pontryagin1_sumEpsR` (the latter is the iso-invariance of `p₁` in the
  sum-with-a-trivial-line form, which is what the probe produces).

The remaining links to write: (i) the two probe lemmas above; (ii) `p₁`-invariance under a real
`BundleIso` (from `chernClass_BundleIso` applied to the complexification — `complexificationCore`
of a real bundle isomorphism — and `Work.Thom.pontryagin1_sumEpsR` / stability);
(iii) `p₁(realification(tautDual 2)) ≠ 0` via route (A) or (B).

## Two traps found while writing `probeFrame_soAct` (the equivariance), recorded so they are not
## rediscovered

* `Fintype.sum_sum_type` (the correct name; there is no `Finset.sum_sum_type`) must be applied to a
  sum *already* reindexed onto `Fin 2 ⊕ Fin κ` with `finSumFinEquiv (m := 2) (n := κ)` given
  explicitly and immediately before, otherwise the split silently produces the wrong index type in
  the second block (`Fin 2` instead of `Fin κ`).
* A `rw`/`congr` step that unfolds `∑` over `Fin 2` puts the sum into the `List.foldr` normal form,
  so `congr 1` afterwards matches a single term rather than a sum.  The robust route is therefore to
  state the two `hL`/`hR` identities of the equivariance *with the sums fully annotated in the
  statement* (as `∑ a' : Fin 2, A a' a • emb6 κ m hm (f a')`), prove the reindexing as
  `Equiv.sum_comp (finSumFinEquiv (m := 2) (n := κ)) …` and the block split as a `have` whose
  right-hand side is the annotated sum plus `0`, and to avoid `Fintype.sum_sum_type` inside a
  `congr`-driven goal.
* In the `inr` branch the target is `fixedFrame κ m l = ∑ l', (if l' = l then 1 else 0) • fixedFrame
  κ m l'`, whose right-hand side is `ite_smul` + `one_smul` + `zero_smul` + `Finset.sum_ite_eq'` +
  `Finset.mem_univ` + `if_pos trivial`; the left-hand side unfolds by
  `simp only [probeFrame, Equiv.symm_apply_apply, probeFrameFun_inr]`.
-/

namespace Work.ThomBordism.Grassmann

open CategoryTheory Limits

noncomputable section

variable {M : Type*} [AddCommGroup M] [Module ℤ M]

/-! ## The rationalisation of a torsion-free class of a module isomorphic to `ℤ` -/

/-- **`1 ⊗ x ≠ 0` in `M ⊗[ℤ] ℚ` when `M ≅ ℤ` and `x ≠ 0`.**  A module isomorphic to `ℤ` is
torsion free, and `x ⊗ 1` dies in `M ⊗[ℤ] ℚ` exactly when `x` is torsion. -/
theorem tmul_one_ne_zero_of_iso_int (e : M ≃ₗ[ℤ] ℤ) {x : M} (hx : x ≠ 0) :
    (1 : ℚ) ⊗ₜ[ℤ] x ≠ 0 := by
  intro h0
  have h1 : (TensorProduct.congr (LinearEquiv.refl ℤ ℚ) e) ((1 : ℚ) ⊗ₜ[ℤ] x)
      = (1 : ℚ) ⊗ₜ[ℤ] (e x) := by
    rw [TensorProduct.congr_tmul]
    rfl
  have h3 : (1 : ℚ) ⊗ₜ[ℤ] (e x) = 0 := by
    rw [← h1, h0, map_zero]
  have h4 : ((e x : ℤ) : ℚ) = 0 := by
    have h5 := congrArg (TensorProduct.rid ℤ ℚ) h3
    rw [TensorProduct.rid_tmul, map_zero] at h5
    simpa using h5
  have h2 : e x = 0 := by exact_mod_cast h4
  exact hx (e.injective (by rw [h2, map_zero]))


/-! ## `u² ∈ H⁴(ℂP²;ℤ)` generates, by the Gysin sequence of `O(1)` -/

/-- The Thom class of the tautological dual line bundle `O(1)` over `ℂP²`; its Euler class is
`u = c₁(O(1)) = Work.Gen.uCoh 2`. -/
noncomputable def cp2T : Work.Thom.ThomClass (Work.Thom.realification (Work.Gen.tautDual 2)) 2 :=
  Work.Thom.thomClassRank 1 (Nat.succ_le_succ (Nat.zero_le 0)) (Work.Gen.tautDual 2)

/-- **The Gysin map `∪u : H^k(ℂP²;ℤ) → H^{k+2}(ℂP²;ℤ)` is surjective in the relevant range**: the
punctured total space of `O(1)` is `ℂ³∖{0}`, which has no cohomology in degree `k+2 ≠ 0, 5`, and
the Gysin sequence `H^k → H^{k+2} → H^{k+2}(E∖0)` is exact. -/
theorem cp2_gysin_surj (k : ℕ) (hk0 : k + 2 ≠ 0) (hk : k + 2 ≠ 5) :
    Function.Surjective (Work.Thom.gysinEuler cp2T k) := by
  intro y
  have hvan := puncturedTautDualTwoHZero (k + 2) hk0 hk
  haveI : Subsingleton ↑(Work.Thom.Coh ℤ (k + 2)
      ↥(Work.Thom.zeroComplement (Work.Thom.realification (Work.Gen.tautDual 2)))) :=
    ModuleCat.subsingleton_of_isZero hvan
  have hrange := Work.Thom.gysin_exact_at_base cp2T k
  have : y ∈ Set.range ⇑(Work.Thom.gysinEuler cp2T k) := by
    rw [hrange]
    exact Subsingleton.elim _ _
  exact this

/-- **The Gysin sequence of `O(1)` on `ℂP²`**: `H⁴(ℂP²;ℤ) = ℤ⟨u²⟩`. -/
theorem gen_uSq_two_span : Submodule.span ℤ {Work.Gen.uSq 2} = ⊤ := by
  have he : Work.Thom.gysinEuler cp2T 2 (Work.Gen.uCoh 2) = Work.Gen.uSq 2 := by
    rw [Work.Thom.gysinEuler_eq_cupEuler]
    rfl
  have hgen := Work.Gen.span_singleton_map_eq_top' (Work.Thom.gysinEuler cp2T 2)
    (cp2_gysin_surj 2 (by norm_num) (by norm_num)) (Work.Gen.uCoh 2) Work.Gen.ChernGeneratorTwo
  rwa [he] at hgen

/-- `H⁴(ℂP²;ℤ) ≃ₗ[ℤ] ℤ`, from the Mayer–Vietoris computation
`Work.Projective.singularCohomology_four_cp2`. -/
noncomputable def cp2CohFourEquiv :
    Work.Thom.Coh ℤ 4 (Work.Projective.CP 2) ≃ₗ[ℤ] ℤ :=
  LinearEquiv.ofBijective (Classical.choice Work.Projective.singularCohomology_four_cp2).hom.hom
    ⟨(ModuleCat.mono_iff_injective _).mp inferInstance,
      (ModuleCat.epi_iff_surjective _).mp inferInstance⟩

/-- **`u² ≠ 0` in `H⁴(ℂP²;ℤ)`**: it generates a non-trivial module. -/
theorem gen_uSq_two_ne_zero : Work.Gen.uSq 2 ≠ 0 := by
  intro h
  have hbot : (⊤ : Submodule ℤ (Work.Thom.Coh ℤ 4 (Work.Projective.CP 2))) = ⊥ := by
    rw [← gen_uSq_two_span]
    simp [h]
  haveI hsub : Subsingleton (Work.Thom.Coh ℤ 4 (Work.Projective.CP 2)) :=
    ⟨fun a b => by
      have ha : a ∈ (⊥ : Submodule ℤ (Work.Thom.Coh ℤ 4 (Work.Projective.CP 2))) := by
        rw [← hbot]; trivial
      have hb : b ∈ (⊥ : Submodule ℤ (Work.Thom.Coh ℤ 4 (Work.Projective.CP 2))) := by
        rw [← hbot]; trivial
      rw [Submodule.mem_bot] at ha hb
      rw [ha, hb]⟩
  exact Int.zero_ne_one (by
    have h' : cp2CohFourEquiv.symm (0 : ℤ) = cp2CohFourEquiv.symm 1 := Subsingleton.elim _ _
    simpa using congrArg (⇑cp2CohFourEquiv) h')

/-- **`1 ⊗ u² ≠ 0` in `H⁴(ℂP²;ℤ) ⊗ ℚ`.**  The class `u²` generates `H⁴(ℂP²;ℤ) ≅ ℤ`, hence is not
torsion, hence survives rationalisation. -/
theorem rat_uSq_two_ne_zero :
    (1 : ℚ) ⊗ₜ[ℤ] Work.Gen.uSq 2 ≠ 0 :=
  tmul_one_ne_zero_of_iso_int cp2CohFourEquiv gen_uSq_two_ne_zero

/-! ## The probe: the fixed complement frame

The direct-sum step `G̃r₂(ℝ⁶) → G̃r_{2+κ}(ℝ^{2+κ+m})`, `P ↦ P ⊕ P₀`, needs a *fixed* oriented
orthonormal `κ`-frame `P₀` in the complement of a fixed copy of `ℝ⁴ = Amb 4 ⊆ Amb ((2+κ)+m)`.
Here it is: the standard basis vectors supported on the coordinates
`κ ⊆ Fin (2+κ) ⊆ Fin ((2+κ)+m)` (last block of the `Fin (2+κ)` coordinates). -/

/-- **The inner product of two standard coordinate vectors**: `⟨e_a, e_b⟩ = if a = b then 1 else 0`
in `EuclideanSpace ℝ ι` (immediate from `EuclideanSpace.basisFun`). -/
theorem inner_single_single {ι : Type*} [Fintype ι] [DecidableEq ι] (a b : ι) :
    inner ℝ (EuclideanSpace.single (𝕜 := ℝ) a 1 : EuclideanSpace ℝ ι)
      (EuclideanSpace.single (𝕜 := ℝ) b 1) = if a = b then (1 : ℝ) else 0 := by
  have h1 := orthonormal_iff_ite.mp (EuclideanSpace.basisFun ι ℝ).orthonormal a b
  simpa only [EuclideanSpace.basisFun_apply] using h1

/-- The fixed orthonormal `κ`-frame of `Amb ((2+κ)+m)` supported on the `Fin κ`-block of the
coordinates `Fin (2+κ) ⊆ Fin ((2+κ)+m)` (both splittings through `finSumFinEquiv`). -/
noncomputable def fixedFrame (κ m : ℕ) : Fin κ → Amb ((2 + κ) + m) :=
  fun i => EuclideanSpace.single (𝕜 := ℝ)
    (finSumFinEquiv (Sum.inl (finSumFinEquiv (Sum.inr i)))) 1

/-- The fixed complement frame is orthonormal: it is the standard orthonormal basis of the ambient
space, restricted to the `Fin κ`-block. -/
theorem fixedFrame_orthonormal (κ m : ℕ) : Orthonormal ℝ (fixedFrame κ m) := by
  rw [orthonormal_iff_ite]
  intro i j
  have hb : ∀ i : Fin κ, fixedFrame κ m i
      = EuclideanSpace.single (𝕜 := ℝ)
          (finSumFinEquiv (m := 2 + κ) (n := m)
            (Sum.inl (finSumFinEquiv (m := 2) (n := κ) (Sum.inr i)))) 1 := fun i => rfl
  rw [hb i, hb j, inner_single_single]
  by_cases hij : i = j
  · subst hij
    simp
  · have hne : ¬ (finSumFinEquiv (m := 2 + κ) (n := m)
          (Sum.inl (finSumFinEquiv (m := 2) (n := κ) (Sum.inr i)))
        = finSumFinEquiv (m := 2 + κ) (n := m)
          (Sum.inl (finSumFinEquiv (m := 2) (n := κ) (Sum.inr j)))) := by
      intro h
      have h1 : Sum.inl (finSumFinEquiv (m := 2) (n := κ) (Sum.inr i))
          = Sum.inl (finSumFinEquiv (m := 2) (n := κ) (Sum.inr j)) :=
        (finSumFinEquiv (m := 2 + κ) (n := m)).injective h
      have h2 := Sum.inl_injective h1
      have h3 : Sum.inr i = Sum.inr j :=
        (finSumFinEquiv (m := 2) (n := κ)).injective h2
      exact hij (Sum.inr_injective h3)
    rw [if_neg hne, if_neg hij]

/-! ## The probe: the ambient embedding and the direct-sum map -/

/-- The index embedding `Fin 6 → Fin ((2+κ)+m)` underlying the probe: the first two coordinates of
`Amb 6` go to the `Fin 2`-block of the target rank `Fin (2+κ)`, the last four to the `Fin m`-block
(this is where `4 ≤ m` enters). -/
noncomputable def embIdx (κ m : ℕ) (hm : 4 ≤ m) : Fin 6 → Fin ((2 + κ) + m) :=
  fun i => finSumFinEquiv (m := 2 + κ) (n := m)
    (Sum.map (Fin.castAdd κ) (Fin.castLE hm)
      ((finSumFinEquiv (m := 2) (n := 4)).symm i))

theorem embIdx_injective (κ m : ℕ) (hm : 4 ≤ m) : Function.Injective (embIdx κ m hm) := by
  intro i j hij
  have h1 := (finSumFinEquiv (m := 2 + κ) (n := m)).injective (by simpa only [embIdx] using hij)
  rcases hi : (finSumFinEquiv (m := 2) (n := 4)).symm i with a | b <;>
    rcases hj : (finSumFinEquiv (m := 2) (n := 4)).symm j with a' | b'
  · have h := h1
    rw [hi, hj] at h
    simp only [Sum.map_inl, Sum.map_inr] at h
    have h3 : a = a' := Fin.ext (by simpa using congrArg Fin.val (Sum.inl_injective h))
    rw [← (finSumFinEquiv (m := 2) (n := 4)).apply_symm_apply i,
      ← (finSumFinEquiv (m := 2) (n := 4)).apply_symm_apply j, hi, hj, h3]
  · have h := h1
    rw [hi, hj] at h
    simp only [Sum.map_inl, Sum.map_inr] at h
    exact absurd h Sum.inl_ne_inr
  · have h := h1
    rw [hi, hj] at h
    simp only [Sum.map_inl, Sum.map_inr] at h
    exact absurd h Sum.inr_ne_inl
  · have h := h1
    rw [hi, hj] at h
    simp only [Sum.map_inl, Sum.map_inr] at h
    have h3 : Fin.castLE hm b = Fin.castLE hm b' := Sum.inr_injective h
    have h4 : b = b' := Fin.ext (by simpa using congrArg Fin.val h3)
    rw [← (finSumFinEquiv (m := 2) (n := 4)).apply_symm_apply i,
      ← (finSumFinEquiv (m := 2) (n := 4)).apply_symm_apply j, hi, hj, h4]

/-- The ambient embedding `Amb 6 → Amb ((2+κ)+m)` of the probe: the coordinate functional at `i`
goes to the coordinate functional at `embIdx κ m hm i`.  It is a linear map by construction; it is
an isometry because `embIdx` is injective (`embIdx_injective`). -/
noncomputable def emb6 (κ m : ℕ) (hm : 4 ≤ m) : Amb 6 →ₗ[ℝ] Amb ((2 + κ) + m) :=
  ∑ i : Fin 6,
    (EuclideanSpace.proj (𝕜 := ℝ) i).smulRight
      (EuclideanSpace.single (𝕜 := ℝ) (embIdx κ m hm i) 1)

/-- **The ambient embedding `emb6` preserves inner products** (it is a linear isometry): the index
map `embIdx` is injective and the standard coordinate vectors are orthonormal. -/
theorem inner_emb6 (κ m : ℕ) (hm : 4 ≤ m) (v w : Amb 6) :
    inner ℝ (emb6 κ m hm v) (emb6 κ m hm w) = inner ℝ v w := by
  have hv : emb6 κ m hm v = ∑ i : Fin 6, v.ofLp i •
      (EuclideanSpace.single (𝕜 := ℝ) (embIdx κ m hm i) 1 : Amb ((2 + κ) + m)) := by
    simp only [emb6, LinearMap.sum_apply]; rfl
  have hw : emb6 κ m hm w = ∑ i : Fin 6, w.ofLp i •
      (EuclideanSpace.single (𝕜 := ℝ) (embIdx κ m hm i) 1 : Amb ((2 + κ) + m)) := by
    simp only [emb6, LinearMap.sum_apply]; rfl
  have hif : ∀ i j : Fin 6, (if embIdx κ m hm i = embIdx κ m hm j then (1 : ℝ) else 0)
      = if i = j then 1 else 0 := by
    intro i j
    by_cases h : i = j
    · rw [if_pos h, if_pos (by rw [h])]
    · rw [if_neg h, if_neg (fun he => h (embIdx_injective κ m hm he))]
  have hL : inner ℝ (emb6 κ m hm v) (emb6 κ m hm w)
      = ∑ i : Fin 6, v.ofLp i * w.ofLp i := by
    rw [hv, hw, sum_inner]
    simp only [inner_sum]
    simp only [inner_smul_left, inner_smul_right, inner_single_single, hif, star_trivial, starRingEnd_apply]
    refine Finset.sum_congr rfl (fun i _ => ?_)
    rw [Finset.sum_eq_single i]
    · rw [if_pos rfl]; ring
    · intro j _ hj
      rw [if_neg (fun h : i = j => hj h.symm)]
      ring
    · intro hi; exact absurd (Finset.mem_univ i) hi
  have hR : inner ℝ v w = ∑ i : Fin 6, v.ofLp i * w.ofLp i := by
    rw [PiLp.inner_apply]
    refine Finset.sum_congr rfl (fun i _ => ?_)
    rw [RCLike.inner_apply]
    simp [mul_comm]
  rw [hL, hR]

/-- The `embIdx`-image of a coordinate of `Amb 6` never lies in the `Fin κ`-block of the target
rank (`Fin (2+κ)`), i.e. never equals the supporting index of `fixedFrame`. -/
theorem embIdx_ne_fixedIdx (κ m : ℕ) (hm : 4 ≤ m) (i : Fin 6) (l : Fin κ) :
    embIdx κ m hm i ≠ finSumFinEquiv (m := 2 + κ) (n := m)
      (Sum.inl (finSumFinEquiv (m := 2) (n := κ) (Sum.inr l))) := by
  rcases hi : (finSumFinEquiv (m := 2) (n := 4)).symm i with a | b
  · intro h
    simp only [embIdx, hi, finSumFinEquiv_apply_left, finSumFinEquiv_apply_right] at h
    have h2 : (a : ℕ) = 2 + (l : ℕ) := congrArg Fin.val h
    omega
  · intro h
    simp only [embIdx, hi, finSumFinEquiv_apply_left, finSumFinEquiv_apply_right] at h
    exact absurd ((finSumFinEquiv (m := 2 + κ) (n := m)).injective h) Sum.inr_ne_inl

/-- **The `emb6`-image of `Amb 6` is orthogonal to the fixed complement frame** (the two blocks of
the target rank are disjoint). -/
theorem inner_emb6_fixedFrame (κ m : ℕ) (hm : 4 ≤ m) (v : Amb 6) (l : Fin κ) :
    inner ℝ (emb6 κ m hm v) (fixedFrame κ m l) = 0 := by
  have hv : emb6 κ m hm v = ∑ i : Fin 6, v.ofLp i •
      (EuclideanSpace.single (𝕜 := ℝ) (embIdx κ m hm i) 1 : Amb ((2 + κ) + m)) := by
    simp only [emb6, LinearMap.sum_apply]; rfl
  have hf : fixedFrame κ m l = EuclideanSpace.single (𝕜 := ℝ)
      (finSumFinEquiv (m := 2 + κ) (n := m)
        (Sum.inl (finSumFinEquiv (m := 2) (n := κ) (Sum.inr l)))) 1 := rfl
  rw [hv, hf, sum_inner]
  refine Finset.sum_eq_zero (fun i _ => ?_)
  rw [inner_smul_left, inner_single_single, starRingEnd_apply, star_trivial,
    if_neg (embIdx_ne_fixedIdx κ m hm i l), mul_zero]

/-! ## The probe: the Stiefel-level map and its orthonormality -/

/-- The frame of the direct-sum probe, on the sum `Fin 2 ⊕ Fin κ` of the two blocks: the plane part
is the embedded input frame, the complement part is the fixed frame. -/
noncomputable def probeFrameFun (κ m : ℕ) (hm : 4 ≤ m) (f : Fin 2 → Amb 6) :
    Fin 2 ⊕ Fin κ → Amb ((2 + κ) + m)
  | Sum.inl a => emb6 κ m hm (f a)
  | Sum.inr l => fixedFrame κ m l

@[simp] theorem probeFrameFun_inl (κ m : ℕ) (hm : 4 ≤ m) (f : Fin 2 → Amb 6) (a : Fin 2) :
    probeFrameFun κ m hm f (Sum.inl a) = emb6 κ m hm (f a) := rfl

@[simp] theorem probeFrameFun_inr (κ m : ℕ) (hm : 4 ≤ m) (f : Fin 2 → Amb 6) (l : Fin κ) :
    probeFrameFun κ m hm f (Sum.inr l) = fixedFrame κ m l := rfl

noncomputable def probeFrame (κ m : ℕ) (hm : 4 ≤ m) (f : Fin 2 → Amb 6) :
    Fin (2 + κ) → Amb ((2 + κ) + m) :=
  fun j => probeFrameFun κ m hm f ((finSumFinEquiv (m := 2) (n := κ)).symm j)

theorem probeFrame_orthonormal (κ m : ℕ) (hm : 4 ≤ m) {f : Fin 2 → Amb 6}
    (hf : Orthonormal ℝ f) : Orthonormal ℝ (probeFrame κ m hm f) := by
  rw [orthonormal_iff_ite]
  intro i j
  have hf' := orthonormal_iff_ite.mp hf
  have hfF := orthonormal_iff_ite.mp (fixedFrame_orthonormal κ m)
  rcases hi : (finSumFinEquiv (m := 2) (n := κ)).symm i with a | l <;>
    rcases hj : (finSumFinEquiv (m := 2) (n := κ)).symm j with a' | l'
  · have hi1 : probeFrame κ m hm f i = emb6 κ m hm (f a) := by
      simp only [probeFrame, hi, probeFrameFun_inl]
    have hj1 : probeFrame κ m hm f j = emb6 κ m hm (f a') := by
      simp only [probeFrame, hj, probeFrameFun_inl]
    rw [hi1, hj1, inner_emb6, hf']
    by_cases h : a = a'
    · rw [if_pos h, if_pos ((finSumFinEquiv (m := 2) (n := κ)).symm.injective
        (by rw [hi, hj, h]))]
    · rw [if_neg h, if_neg (fun hij => h (Sum.inl_injective (by rw [← hi, ← hj, hij])))]
  · have hi1 : probeFrame κ m hm f i = emb6 κ m hm (f a) := by
      simp only [probeFrame, hi, probeFrameFun_inl]
    have hj1 : probeFrame κ m hm f j = fixedFrame κ m l' := by
      simp only [probeFrame, hj, probeFrameFun_inr]
    rw [hi1, hj1, inner_emb6_fixedFrame,
      if_neg (fun hij => Sum.inl_ne_inr (by rw [← hi, ← hj, hij]))]
  · have hi1 : probeFrame κ m hm f i = fixedFrame κ m l := by
      simp only [probeFrame, hi, probeFrameFun_inr]
    have hj1 : probeFrame κ m hm f j = emb6 κ m hm (f a') := by
      simp only [probeFrame, hj, probeFrameFun_inl]
    rw [hi1, hj1, real_inner_comm, inner_emb6_fixedFrame,
      if_neg (fun hij => Sum.inr_ne_inl (by rw [← hi, ← hj, hij]))]
  · have hi1 : probeFrame κ m hm f i = fixedFrame κ m l := by
      simp only [probeFrame, hi, probeFrameFun_inr]
    have hj1 : probeFrame κ m hm f j = fixedFrame κ m l' := by
      simp only [probeFrame, hj, probeFrameFun_inr]
    rw [hi1, hj1, hfF]
    by_cases h : l = l'
    · rw [if_pos h, if_pos ((finSumFinEquiv (m := 2) (n := κ)).symm.injective
        (by rw [hi, hj, h]))]
    · rw [if_neg h, if_neg (fun hij => h (Sum.inr_injective (by rw [← hi, ← hj, hij])))]

/-- **The Stiefel-level map of the probe**: append the fixed complement frame to the image of the
input frame under the ambient embedding `emb6`. -/
noncomputable def probeStiefel (κ m : ℕ) (hm : 4 ≤ m) (f : Stiefel 2 4) :
    Stiefel (2 + κ) m :=
  ⟨probeFrame κ m hm f.1, probeFrame_orthonormal κ m hm f.2⟩

/-- **The reassembly map of the probe is continuous**: the map
`f ↦ (a ↦ emb6 (f a)) ⊕ (l ↦ fixedFrame l)` on the function space `Fin 2 → Amb 6` is continuous
(its `j`-th component is either a continuous linear image of `f a` or constant). -/
theorem continuous_probeFrame_fun (κ m : ℕ) (hm : 4 ≤ m) :
    Continuous (fun f : Fin 2 → Amb 6 => probeFrame κ m hm f) := by
  refine continuous_pi (fun j => ?_)
  rcases h : (finSumFinEquiv (m := 2) (n := κ)).symm j with a | l
  · have hEq : (fun f : Fin 2 → Amb 6 => probeFrame κ m hm f j)
        = fun f => emb6 κ m hm (f a) := by
      funext f
      show probeFrameFun κ m hm f ((finSumFinEquiv (m := 2) (n := κ)).symm j)
        = emb6 κ m hm (f a)
      rw [h]
      rfl
    rw [hEq]
    exact (LinearMap.continuous_of_finiteDimensional (emb6 κ m hm)).comp (continuous_apply a)
  · have hEq : (fun f : Fin 2 → Amb 6 => probeFrame κ m hm f j)
        = fun _ => fixedFrame κ m l := by
      funext f
      show probeFrameFun κ m hm f ((finSumFinEquiv (m := 2) (n := κ)).symm j)
        = fixedFrame κ m l
      rw [h]
      rfl
    rw [hEq]
    exact continuous_const

/-- **The Stiefel-level map of the probe is continuous** (for the subspace topologies of the
Stiefel manifolds): it is the reassembly map composed with the projection
`Stiefel 2 4 → (Fin 2 → Amb 6)`, with the orthonormality proof supplied by
`probeFrame_orthonormal`. -/
theorem continuous_probeStiefel (κ m : ℕ) (hm : 4 ≤ m) :
    Continuous (probeStiefel κ m hm) :=
  Continuous.subtype_mk
    ((continuous_probeFrame_fun κ m hm).comp continuous_subtype_val)
    (fun f => probeFrame_orthonormal κ m hm f.2)

/-! ## The probe: the block-diagonal action (equivariance ingredients) -/

/-- The entries of the block-diagonal matrix `diag(A, 1_κ)` on `Fin 2 ⊕ Fin κ`, presented on the
sum of the two blocks. -/
noncomputable def blockDiagEntry (κ : ℕ) (A : Matrix (Fin 2) (Fin 2) ℝ) :
    Fin 2 ⊕ Fin κ → Fin 2 ⊕ Fin κ → ℝ
  | Sum.inl a, Sum.inl b => A a b
  | Sum.inl _, Sum.inr _ => 0
  | Sum.inr _, Sum.inl _ => 0
  | Sum.inr l, Sum.inr l' => if l = l' then 1 else 0

/-- **The block-diagonal matrix `diag(A, 1_κ)`** on `Fin (2+κ)`: it acts by `A` on the plane block
(`Fin 2`) and trivially on the complement block (`Fin κ`).  This is the matrix by which the probe's
`SO(2)`-action on the input frame becomes an `SO(2+κ)`-action on the output frame. -/
noncomputable def blockDiag (κ : ℕ) (A : Matrix (Fin 2) (Fin 2) ℝ) :
    Matrix (Fin (2 + κ)) (Fin (2 + κ)) ℝ :=
  fun i j => blockDiagEntry κ A ((finSumFinEquiv (m := 2) (n := κ)).symm i)
    ((finSumFinEquiv (m := 2) (n := κ)).symm j)

@[simp] theorem blockDiag_inl_inl (κ : ℕ) (A : Matrix (Fin 2) (Fin 2) ℝ) (a b : Fin 2) :
    blockDiag κ A (finSumFinEquiv (Sum.inl a)) (finSumFinEquiv (Sum.inl b)) = A a b := by
  simp [blockDiag, blockDiagEntry]

@[simp] theorem blockDiag_inl_inr (κ : ℕ) (A : Matrix (Fin 2) (Fin 2) ℝ) (a : Fin 2) (l : Fin κ) :
    blockDiag κ A (finSumFinEquiv (Sum.inl a)) (finSumFinEquiv (Sum.inr l)) = 0 := by
  simp [blockDiag, blockDiagEntry]

@[simp] theorem blockDiag_inr_inl (κ : ℕ) (A : Matrix (Fin 2) (Fin 2) ℝ) (l : Fin κ) (a : Fin 2) :
    blockDiag κ A (finSumFinEquiv (Sum.inr l)) (finSumFinEquiv (Sum.inl a)) = 0 := by
  simp [blockDiag, blockDiagEntry]

@[simp] theorem blockDiag_inr_inr (κ : ℕ) (A : Matrix (Fin 2) (Fin 2) ℝ) (l l' : Fin κ) :
    blockDiag κ A (finSumFinEquiv (Sum.inr l)) (finSumFinEquiv (Sum.inr l'))
      = if l = l' then 1 else 0 := by
  simp [blockDiag, blockDiagEntry]


/-! ## The probe: the chain of "add a line" and "include the ambient" maps

These three lemmas replicate the (separately developed) probe chain of
`Submission/Work/ThomBordism/Grassmann/probeP1.lean` inside this module, so that the target does not
depend on that module's import closure.  `probeP1Base` (the base case `(k, m) = (2, 4)`) is imported
from `Submission/Work/ThomBordism/Grassmann/probeP1Base.lean`. -/

/-- The probe statement at `(k, m)`: there is a continuous map `ℂP² → G̃r_k(ℝ^{k+m})` whose
pullback of the first Pontryagin class of the tautological bundle is `± p₁(zStd)`. -/
abbrev probeStatement' (k m : ℕ) : Prop :=
  ∃ σ : C(Work.Projective.CP 2, OG k m),
    (Work.Thom.CohMap σ ℤ 4).hom (p1 k m) = Work.Thom.pontryagin1 zStd ∨
    (Work.Thom.CohMap σ ℤ 4).hom (p1 k m) = - Work.Thom.pontryagin1 zStd

/-- The chain of "add a line" maps `G̃r₂(ℝ⁶) → G̃r_k(ℝ⁴)`: iterating `CohMap_p1_addLine`, every
such map pulls `p₁(γ_{k,4})` back to `p₁(γ_{2,4})`. -/
theorem probeChainAddLine' : ∀ d : ℕ, ∃ Φ : C(OG 2 4, OG (2 + d) 4),
    (Work.Thom.CohMap Φ ℤ 4).hom (p1 (2 + d) 4) = p1 2 4 := by
  intro d
  induction d with
  | zero =>
      refine ⟨ContinuousMap.id _, ?_⟩
      rw [Work.Thom.CohMap_id]
      rfl
  | succ d ih =>
      obtain ⟨Φ, hΦ⟩ := ih
      obtain ⟨φ, hφ⟩ := CohMap_p1_addLine (2 + d) 4
      refine ⟨φ.comp Φ, ?_⟩
      change (Work.Thom.CohMap (φ.comp Φ) ℤ 4).hom (p1 (2 + d + 1) 4) = p1 2 4
      rw [Work.Thom.CohMap_comp Φ φ ℤ 4]
      change (Work.Thom.CohMap Φ ℤ 4).hom ((Work.Thom.CohMap φ ℤ 4).hom (p1 (2 + d + 1) 4))
        = p1 2 4
      rw [hφ, hΦ]

/-- The chain of ambient-inclusion maps `G̃r_k(ℝ⁴) → G̃r_k(ℝ^{k+m})`: iterating `CohMap_p1_incl`,
every such map pulls `p₁(γ_{k,m})` back to `p₁(γ_{k,4})`. -/
theorem probeChainIncl' (k : ℕ) : ∀ e : ℕ, ∃ Ψ : C(OG k 4, OG k (4 + e)),
    (Work.Thom.CohMap Ψ ℤ 4).hom (p1 k (4 + e)) = p1 k 4 := by
  intro e
  induction e with
  | zero =>
      refine ⟨ContinuousMap.id _, ?_⟩
      rw [Work.Thom.CohMap_id]
      rfl
  | succ e ih =>
      obtain ⟨Ψ, hΨ⟩ := ih
      obtain ⟨ψ, hψ⟩ := CohMap_p1_incl k (4 + e)
      refine ⟨ψ.comp Ψ, ?_⟩
      change (Work.Thom.CohMap (ψ.comp Ψ) ℤ 4).hom (p1 k (4 + e + 1)) = p1 k 4
      rw [Work.Thom.CohMap_comp Ψ ψ ℤ 4]
      change (Work.Thom.CohMap Ψ ℤ 4).hom ((Work.Thom.CohMap ψ ℤ 4).hom (p1 k (4 + e + 1)))
        = p1 k 4
      rw [hψ, hΨ]

/-- Reduction of the probe statement to the base case `(k, m) = (2, 4)`. -/
theorem probeStatement'_of_base (h : probeStatement' 2 4) :
    ∀ k m : ℕ, 4 ≤ k → 4 ≤ m → probeStatement' k m := by
  intro k m hk hm
  obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le (show 2 ≤ k by omega)
  obtain ⟨e, rfl⟩ := Nat.exists_eq_add_of_le hm
  obtain ⟨Φ, hΦ⟩ := probeChainAddLine' d
  obtain ⟨σ₀, hσ₀⟩ := h
  obtain ⟨Ψ, hΨ⟩ := probeChainIncl' (2 + d) e
  refine ⟨Ψ.comp (Φ.comp σ₀), ?_⟩
  rw [Work.Thom.CohMap_comp (Φ.comp σ₀) Ψ ℤ 4]
  change (Work.Thom.CohMap (Φ.comp σ₀) ℤ 4).hom
        ((Work.Thom.CohMap Ψ ℤ 4).hom (p1 (2 + d) (4 + e))) = Work.Thom.pontryagin1 zStd ∨
      (Work.Thom.CohMap (Φ.comp σ₀) ℤ 4).hom
        ((Work.Thom.CohMap Ψ ℤ 4).hom (p1 (2 + d) (4 + e))) = - Work.Thom.pontryagin1 zStd
  rw [hΨ]
  rw [Work.Thom.CohMap_comp σ₀ Φ ℤ 4]
  change (Work.Thom.CohMap σ₀ ℤ 4).hom ((Work.Thom.CohMap Φ ℤ 4).hom (p1 (2 + d) 4))
        = Work.Thom.pontryagin1 zStd ∨
      (Work.Thom.CohMap σ₀ ℤ 4).hom ((Work.Thom.CohMap Φ ℤ 4).hom (p1 (2 + d) 4))
        = - Work.Thom.pontryagin1 zStd
  rw [hΦ]
  exact hσ₀

/-- **The probe for every `k, m ≥ 4`**, from `probeP1Base`. -/
theorem probeStatement_of (k m : ℕ) (hk : 4 ≤ k) (hm : 4 ≤ m) : probeStatement' k m :=
  probeStatement'_of_base Work.ThomBordism.Grassmann.probeP1Base k m hk hm

/-- **The target**: `Work.ThomBordism.Grassmann.p1Rat k m ≠ 0` for `k, m ≥ 10`.

See the module docstring for the plan (probe `ℂP² → G̃r_k(ℝ^{k+m})`), for what is already proved
here (the Gysin-based non-vanishing `1 ⊗ u² ≠ 0`), and for the two remaining inputs. -/
theorem p1Rat_ne_zero_via_probe (k m : ℕ) (hk : 10 ≤ k) (hm : 10 ≤ m) :
    Work.ThomBordism.Grassmann.p1Rat k m ≠ 0 := by
  obtain ⟨σ, hσ | hσ⟩ := probeStatement_of k m (by omega) (by omega)
  · have h4 : (1 : ℚ) ⊗ₜ[ℤ]
        ((Work.Thom.CohMap σ ℤ 4).hom (Work.ThomBordism.Grassmann.p1 k m)) ≠ 0 := by
      rw [hσ]
      exact tmul_one_ne_zero_of_iso_int cp2CohFourEquiv
        Work.ThomBordism.Grassmann.zStd_pontryagin_ne_zero
    have h5 : TensorProduct.map (LinearMap.id : ℚ →ₗ[ℤ] ℚ) ((Work.Thom.CohMap σ ℤ 4).hom)
        (Work.ThomBordism.Grassmann.p1Rat k m) ≠ 0 := by
      rw [show Work.ThomBordism.Grassmann.p1Rat k m
          = (1 : ℚ) ⊗ₜ[ℤ] Work.ThomBordism.Grassmann.p1 k m from rfl,
        TensorProduct.map_tmul]
      simpa using h4
    intro h0
    exact h5 (by rw [h0, map_zero])
  · have h4 : (1 : ℚ) ⊗ₜ[ℤ]
        ((Work.Thom.CohMap σ ℤ 4).hom (Work.ThomBordism.Grassmann.p1 k m)) ≠ 0 := by
      rw [hσ, TensorProduct.tmul_neg]
      exact neg_ne_zero.mpr (tmul_one_ne_zero_of_iso_int cp2CohFourEquiv
        Work.ThomBordism.Grassmann.zStd_pontryagin_ne_zero)
    have h5 : TensorProduct.map (LinearMap.id : ℚ →ₗ[ℤ] ℚ) ((Work.Thom.CohMap σ ℤ 4).hom)
        (Work.ThomBordism.Grassmann.p1Rat k m) ≠ 0 := by
      rw [show Work.ThomBordism.Grassmann.p1Rat k m
          = (1 : ℚ) ⊗ₜ[ℤ] Work.ThomBordism.Grassmann.p1 k m from rfl,
        TensorProduct.map_tmul]
      simpa using h4
    intro h0
    exact h5 (by rw [h0, map_zero])

end

end Work.ThomBordism.Grassmann
