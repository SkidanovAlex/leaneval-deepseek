import Mathlib
import Submission.Work.Diff.EXT.aCovArr_eq_covKAExt
import Submission.Work.Diff.EXT.ATens.Defs
import Submission.Work.Diff.EXT.ATens.Kit

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

/-!
# Linearity of `covKAExt` in its direction slots (`KaLinD`)

`Work.Diff.EXT.KaLinD G t U k` is the statement that `Work.Diff.EXT.covKAExt G t k` (the `k`-th
covariant derivative of the lowered connection difference `aOf G t` with respect to the fixed
background connection `∇^{G 0}`) is `C^∞(U)`-linear in each *direction* slot.

The proof is an induction on `k` on the *packed* recursion `Work.Diff.EXT.cktA`
(`Submission/Work/Diff/EXT/ATens/Defs.lean`), the version of `covKAExt` with the `k` direction
slots and the three argument slots packed into one `Fin (k+3)`-tuple.  At each level `k` we prove
simultaneously

* `KSm k`: `cktA G t k F` is `C^∞` on `U` for tuples of fields which are `C^∞` on `U`;
* `KLin k`: `cktA G t k` is `C^∞(U)`-linear in *every* slot of the tuple.

`KaLinD` is the specialisation to the direction slots (`Fin.castAdd 3 i`).
-/

set_option linter.unusedSectionVars false
set_option maxHeartbeats 1000000

open LeanEval.Geometry.SphereTheorem Submission.Diff Submission.Diff.Alg
open scoped Manifold ContDiff Bundle Topology BigOperators
open Bundle ContDiff Set VectorField CovariantDerivative Metric Filter

namespace Work.Diff.EXT.ATower

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [CompleteSpace E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I (⊤ : ℕ∞) M]
  [I.Boundaryless] [T2Space M]

/-! ## Elementary helpers -/

/-- A finite combination of smooth fields with smooth coefficients is smooth. -/
lemma kaSm_finset_sum_smul {ι : Type*} (s : Finset ι) {U : Set M}
    (d : ι → M → ℝ) (V : ι → TfA (I := I) (M := M))
    (hd : ∀ q, CMDiff[U] ∞ (d q)) (hV : ∀ q, KaSm (I := I) (M := M) U (V q)) :
    KaSm (I := I) (M := M) U (fun y => ∑ q ∈ s, d q y • V q y) := by
  classical
  induction s using Finset.induction_on with
  | empty =>
      intro y hy
      simp only [Finset.sum_empty]
      exact contMDiffWithinAt_zeroSection ℝ (fun x : M => TangentSpace I x) (IB := I)
  | insert a s ha ih =>
      have hfun : (fun y : M => ∑ q ∈ insert a s, d q y • V q y)
          = (d a • V a) + (fun y => ∑ q ∈ s, d q y • V q y) := by
        funext y; rw [Finset.sum_insert ha]; rfl
      rw [hfun]
      intro y hy
      exact ((hd a y hy).smul_section (hV a y hy)).add_section (ih y hy)

/-- The `Finset.univ` form of `kaSm_finset_sum_smul`. -/
lemma kaSm_sum_smul {ι : Type*} [Fintype ι] {U : Set M}
    (d : ι → M → ℝ) (V : ι → TfA (I := I) (M := M))
    (hd : ∀ q, CMDiff[U] ∞ (d q)) (hV : ∀ q, KaSm (I := I) (M := M) U (V q)) :
    KaSm (I := I) (M := M) U (fun y => ∑ q, d q y • V q y) := by
  have h := kaSm_finset_sum_smul (I := I) (M := M) Finset.univ d V hd hV
  simpa only [Finset.mem_univ, Finset.sum_attach] using h

/-- A field which is `C^∞` on an open set is differentiable at each of its points. -/
lemma mdiffAt_of_kaSm {U : Set M} (hU : IsOpen U) {X : TfA (I := I) (M := M)}
    (hX : KaSm (I := I) (M := M) U X) {z : M} (hz : z ∈ U) : MDiffAt (T% X) z :=
  (hX.contMDiffAt (hU.mem_nhds hz)).mdifferentiableAt (by simp)

/-- A scalar function which is `C^∞` on an open set is differentiable at each of its points. -/
lemma mdiffAt_fun_of_cmdiff {U : Set M} (hU : IsOpen U) {f : M → ℝ}
    (hf : CMDiff[U] ∞ f) {z : M} (hz : z ∈ U) : MDiffAt f z :=
  (hf.contMDiffAt (hU.mem_nhds hz)).mdifferentiableAt (by simp)

/-- A finite sum of products of differentiable scalar functions is differentiable. -/
lemma mdiffAt_finset_sum_mul {ι : Type*} (s : Finset ι) (d Φ : ι → M → ℝ) {y : M}
    (hd : ∀ q ∈ s, MDiffAt (d q) y) (hΦ : ∀ q ∈ s, MDiffAt (Φ q) y) :
    MDiffAt (fun z => ∑ q ∈ s, d q z * Φ q z) y := by
  classical
  induction s using Finset.induction_on with
  | empty => simp only [Finset.sum_empty]; exact mdifferentiableAt_const (c := (0:ℝ)) (x := y)
  | insert a s ha ih =>
      simp only [Finset.sum_insert ha]
      exact ((hd a (Finset.mem_insert_self a s)).mul (hΦ a (Finset.mem_insert_self a s))).add
        (ih (fun q hq => hd q (Finset.mem_insert_of_mem hq))
            (fun q hq => hΦ q (Finset.mem_insert_of_mem hq)))

/-- The product rule for `mvfderiv` of a finite sum of products of scalar functions. -/
lemma mvfderiv_finset_sum_mul {ι : Type*} (s : Finset ι) (d Φ : ι → M → ℝ) {y : M}
    (hd : ∀ q ∈ s, MDiffAt (d q) y) (hΦ : ∀ q ∈ s, MDiffAt (Φ q) y) :
    mvfderiv I (fun z => ∑ q ∈ s, d q z * Φ q z) y
      = ∑ q ∈ s, (d q y • mvfderiv I (Φ q) y + (mvfderiv I (d q) y).smulRight (Φ q y)) := by
  classical
  induction s using Finset.induction_on with
  | empty =>
      simp only [Finset.sum_empty]
      exact mvfderiv_const (0:ℝ)
  | insert a s ha ih =>
      have hda : MDiffAt (d a) y := hd a (Finset.mem_insert_self a s)
      have hΦa : MDiffAt (Φ a) y := hΦ a (Finset.mem_insert_self a s)
      have hds : ∀ q ∈ s, MDiffAt (d q) y := fun q hq => hd q (Finset.mem_insert_of_mem hq)
      have hΦs : ∀ q ∈ s, MDiffAt (Φ q) y := fun q hq => hΦ q (Finset.mem_insert_of_mem hq)
      have h1 : MDiffAt (fun z => d a z * Φ a z) y := hda.mul hΦa
      have h2 : MDiffAt (fun z => ∑ q ∈ s, d q z * Φ q z) y :=
        mdiffAt_finset_sum_mul s d Φ hds hΦs
      have e : (fun z => ∑ q ∈ insert a s, d q z * Φ q z)
          = (fun z => d a z * Φ a z) + (fun z => ∑ q ∈ s, d q z * Φ q z) := by
        funext z; simp only [Finset.sum_insert ha, Pi.add_apply]
      have hmv : mvfderiv I (fun z => d a z * Φ a z) y
          = d a y • mvfderiv I (Φ a) y + (mvfderiv I (d a) y).smulRight (Φ a y) :=
        mvfderiv_smul (a := d a) (g := Φ a) hda hΦa
      rw [e, mvfderiv_add h1 h2, hmv, ih hds hΦs, Finset.sum_insert ha]

/-- `mvfderiv` is linear in its direction argument. -/
lemma mvfderiv_sum_smul_dir {ι : Type*} [Fintype ι] (d : ι → M → ℝ)
    (V : ι → TfA (I := I) (M := M)) (Φ : M → ℝ) (y : M) :
    mvfderiv I Φ y (∑ q, d q y • V q y) = ∑ q, d q y * mvfderiv I Φ y (V q y) := by
  rw [map_sum]
  exact Finset.sum_congr rfl (fun q _ => by rw [ContinuousLinearMap.map_smul, smul_eq_mul])

/-! ## The covariant derivative of a field in a direction (`dirFA`) -/

/-- Additivity of `dirFA g · Z` in the field argument, at a point where both fields are
differentiable. -/
lemma dirFA_add_md (g : SMet I M) {X₁ X₂ : TfA (I := I) (M := M)}
    {v0 : TfA (I := I) (M := M)} {y : M}
    (hX₁ : MDiffAt (T% X₁) y) (hX₂ : MDiffAt (T% X₂) y) :
    dirFA g (X₁ + X₂) v0 y = dirFA g X₁ v0 y + dirFA g X₂ v0 y := by
  have h := (lcOf g).isCovariantDerivativeOn.add (σ := X₁) (σ' := X₂) hX₁ hX₂
  simp only [dirFA, h]
  rfl

/-- The Leibniz rule for `dirFA` in the field argument, at a point where the field and the
coefficient are differentiable. -/
lemma dirFA_smul_md (g : SMet I M) {X : TfA (I := I) (M := M)} {f : M → ℝ}
    {v0 : TfA (I := I) (M := M)} {y : M}
    (hf : MDiffAt f y) (hX : MDiffAt (T% X) y) :
    dirFA g (f • X) v0 y = f y • dirFA g X v0 y + ((mvfderiv I f y) (v0 y)) • X y := by
  have h := (lcOf g).isCovariantDerivativeOn.leibniz (σ := X) (g := f) hX hf
  simp only [dirFA] at h ⊢
  rw [h]
  simp only [add_apply, smul_apply, ContinuousLinearMap.smulRight_apply]

/-- The Leibniz rule for `dirFA` in the field argument, for a finite combination of fields, on an
open set `U`. -/
lemma dirFA_finset_sum_smul_on {ι : Type*} (s : Finset ι) {U : Set M} (hU : IsOpen U)
    (g : SMet I M) (d : ι → M → ℝ) (V : ι → TfA (I := I) (M := M))
    (Z : TfA (I := I) (M := M))
    (hd : ∀ q, CMDiff[U] ∞ (d q)) (hV : ∀ q, KaSm (I := I) (M := M) U (V q))
    (hZ : KaSm (I := I) (M := M) U Z) :
    ∀ z ∈ U, dirFA g (fun z' => ∑ q ∈ s, d q z' • V q z') Z z
      = ∑ q ∈ s, (d q z • dirFA g (V q) Z z + ((mvfderiv I (d q) z) (Z z)) • V q z) := by
  classical
  induction s using Finset.induction_on with
  | empty =>
      intro z hz
      simp only [Finset.sum_empty]
      rw [dirFA,
        show (fun z' : M => (0 : TangentSpace I z')) = (0 : Π z : M, TangentSpace I z) from rfl,
        CovariantDerivative.zero]
      simp
  | insert a s ha ih =>
      intro z hz
      have hda : MDiffAt (d a) z := mdiffAt_fun_of_cmdiff hU (hd a) hz
      have hVa : MDiffAt (T% (V a)) z := mdiffAt_of_kaSm hU (hV a) hz
      have hrest : MDiffAt (T% (fun z' => ∑ q ∈ s, d q z' • V q z')) z :=
        mdiffAt_of_kaSm hU (kaSm_finset_sum_smul s d V hd hV) hz
      have hXa : MDiffAt (T% (d a • V a)) z := MDifferentiableAt.smul_section hda hVa
      have hfun : (fun z' : M => ∑ q ∈ insert a s, d q z' • V q z')
          = (d a • V a) + (fun z' => ∑ q ∈ s, d q z' • V q z') := by
        funext z'; rw [Finset.sum_insert ha]; rfl
      rw [hfun, dirFA_add_md g hXa hrest, dirFA_smul_md g hda hVa, ih z hz, Finset.sum_insert ha]

/-- Two fields which agree on an open set have the same covariant derivative there. -/
lemma dirFA_congr_on {U : Set M} (hU : IsOpen U) (g : SMet I M)
    {X X' : TfA (I := I) (M := M)} (Z : TfA (I := I) (M := M))
    (hX : KaSm (I := I) (M := M) U X) (hX' : KaSm (I := I) (M := M) U X')
    (heq : ∀ z ∈ U, X z = X' z) :
    ∀ z ∈ U, dirFA g X Z z = dirFA g X' Z z := by
  intro z hz
  have hd1 : MDiffAt (T% X) z := mdiffAt_of_kaSm hU hX hz
  have hd2 : MDiffAt (T% X') z := mdiffAt_of_kaSm hU hX' hz
  have hev : X =ᶠ[𝓝 z] X' := by
    filter_upwards [hU.mem_nhds hz] with w hw
    exact heq w hw
  have h := Work.Diff.GE.Kato3.lcOf_congr_eventuallyEq g hd1 hd2 hev
  simp only [dirFA]
  rw [h]

/-! ## The packed recursion at `Fin.cons` -/

/-- The recursion `cktA` computed on a tuple in `Fin.cons` form. -/
lemma cktA_cons (G : ℝ → SMet I M) (t : ℝ) (k : ℕ) (W : TfA (I := I) (M := M))
    (G0 : Fin (k+3) → TfA (I := I) (M := M)) :
    cktA G t (k+1) (Fin.cons W G0)
      = fun y => mvfderiv I (fun z => cktA G t k G0 z) y (W y)
        - ∑ i : Fin (k+3), cktA G t k (Function.update G0 i (dirFA (G 0) (G0 i) W)) y := by
  funext y
  rw [cktA_succ]
  simp only [Fin.cons_zero, Fin.cons_succ, Pi.sub_apply, Finset.sum_apply]

end Work.Diff.EXT.ATower

namespace Work.Diff.EXT.ATower

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [CompleteSpace E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I (⊤ : ℕ∞) M]
  [I.Boundaryless] [T2Space M]

/-! ## Level `0`: the lowered connection difference is linear in its three slots -/

lemma cktA_zero (G : ℝ → SMet I M) (t : ℝ) (X : Fin 3 → TfA (I := I) (M := M)) (z : M) :
    cktA G t 0 X z = aOf G t (X 0) (X 1) (X 2) z := rfl

/-- Linearity in the first argument (`A`) of `aOf`, at a point. -/
lemma aOf_lin_val0 {ι : Type*} [Fintype ι] (G : ℝ → SMet I M) (t : ℝ) (d : ι → M → ℝ)
    (V : ι → TfA (I := I) (M := M)) (B C W' : TfA (I := I) (M := M)) (z : M)
    (ha : W' z = ∑ q, d q z • V q z) :
    aOf G t W' B C z = ∑ q, d q z * aOf G t (V q) B C z := by
  simp only [aOf]
  rw [ha]
  have h : lcOf (G t) B z (∑ q, d q z • V q z) - lcOf (G 0) B z (∑ q, d q z • V q z)
      = ∑ q, d q z • (lcOf (G t) B z (V q z) - lcOf (G 0) B z (V q z)) := by
    rw [map_sum, map_sum, ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl (fun q _ => ?_)
    rw [map_smul, map_smul, smul_sub]
  rw [h, map_sum, sum_apply]
  refine Finset.sum_congr rfl (fun q _ => ?_)
  rw [map_smul, smul_apply, smul_eq_mul]

/-- Linearity in the last argument (`C`) of `aOf`, at a point. -/
lemma aOf_lin_val2 {ι : Type*} [Fintype ι] (G : ℝ → SMet I M) (t : ℝ) (d : ι → M → ℝ)
    (V : ι → TfA (I := I) (M := M)) (A B W' : TfA (I := I) (M := M)) (z : M)
    (hc : W' z = ∑ q, d q z • V q z) :
    aOf G t A B W' z = ∑ q, d q z * aOf G t A B (V q) z := by
  simp only [aOf]
  rw [hc, map_sum]
  refine Finset.sum_congr rfl (fun q _ => ?_)
  rw [map_smul, smul_eq_mul]

/-- Linearity in the middle argument (`B`) of `aOf` on an open set: the two derivative
corrections of the connections `∇^{G t}` and `∇^{G 0}` cancel. -/
lemma aOf_lin_slot1 {ι : Type*} [Fintype ι] {U : Set M} (hU : IsOpen U)
    (G : ℝ → SMet I M) (t : ℝ) (d : ι → M → ℝ) (V : ι → TfA (I := I) (M := M))
    (A C W' : TfA (I := I) (M := M))
    (hd : ∀ q, CMDiff[U] ∞ (d q)) (hV : ∀ q, KaSm (I := I) (M := M) U (V q))
    (hA : KaSm (I := I) (M := M) U A) (hC : KaSm (I := I) (M := M) U C)
    (hW' : KaSm (I := I) (M := M) U W')
    (heq : ∀ z ∈ U, W' z = ∑ q, d q z • V q z) :
    ∀ z ∈ U, aOf G t A W' C z = ∑ q, d q z * aOf G t A (V q) C z := by
  intro z hz
  have hWc : KaSm (I := I) (M := M) U (fun y => ∑ q, d q y • V q y) := kaSm_sum_smul d V hd hV
  have hcongt := dirFA_congr_on hU (G t) A hW' hWc heq z hz
  have hcong0 := dirFA_congr_on hU (G 0) A hW' hWc heq z hz
  have ht := dirFA_finset_sum_smul_on Finset.univ hU (G t) d V A hd hV hA z hz
  have h0 := dirFA_finset_sum_smul_on Finset.univ hU (G 0) d V A hd hV hA z hz
  have hcancel : (∑ q, (d q z • dirFA (G t) (V q) A z + ((mvfderiv I (d q) z) (A z)) • V q z))
      - (∑ q, (d q z • dirFA (G 0) (V q) A z + ((mvfderiv I (d q) z) (A z)) • V q z))
      = ∑ q, d q z • (dirFA (G t) (V q) A z - dirFA (G 0) (V q) A z) := by
    rw [← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl (fun q _ => ?_)
    have h1 : d q z • dirFA (G t) (V q) A z + (mvfderiv I (d q) z) (A z) • V q z
        - (d q z • dirFA (G 0) (V q) A z + (mvfderiv I (d q) z) (A z) • V q z)
        = d q z • dirFA (G t) (V q) A z - d q z • dirFA (G 0) (V q) A z := by abel
    rw [h1, ← smul_sub]
  simp only [aOf]
  rw [dirFA] at hcongt hcong0
  rw [hcongt, hcong0, ht, h0, hcancel, map_sum, sum_apply]
  refine Finset.sum_congr rfl (fun q _ => ?_)
  rw [map_smul, smul_apply, smul_eq_mul]
  simp only [dirFA]

end Work.Diff.EXT.ATower

namespace Work.Diff.EXT.ATower

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [CompleteSpace E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I (⊤ : ℕ∞) M]
  [I.Boundaryless] [T2Space M]

/-! ## More computational helpers -/

/-- `mvfderiv` of two functions which agree near a point, applied to a vector. -/
lemma mvfderiv_congr_eventuallyEq_apply {f₁ f₂ : M → ℝ} {z : M} (u : TangentSpace I z)
    (h : f₁ =ᶠ[𝓝 z] f₂) : mvfderiv I f₁ z u = mvfderiv I f₂ z u :=
  congrArg (fun L : TangentSpace I z →L[ℝ] ℝ => L u)
    (Work.Diff.GE.mvfderiv_congr_eventuallyEq (I := I) h)

/-- The product rule for `mvfderiv` of a finite sum of products, applied to a vector. -/
lemma mvfderiv_finset_sum_mul_apply {ι : Type*} (s : Finset ι) (d Φ : ι → M → ℝ) {y : M}
    (u : TangentSpace I y)
    (hd : ∀ q ∈ s, MDiffAt (d q) y) (hΦ : ∀ q ∈ s, MDiffAt (Φ q) y) :
    mvfderiv I (fun z => ∑ q ∈ s, d q z * Φ q z) y u
      = ∑ q ∈ s, (d q y * mvfderiv I (Φ q) y u + (mvfderiv I (d q) y u) * Φ q y) := by
  rw [mvfderiv_finset_sum_mul s d Φ hd hΦ, sum_apply]
  exact Finset.sum_congr rfl (fun q _ => by
    simp only [add_apply, smul_apply, ContinuousLinearMap.smulRight_apply, smul_eq_mul])

/-- Pointwise linearity of `dirFA g X ·` in the direction, for a combination of fields. -/
lemma dirFA_comb_eq {ι : Type*} [Fintype ι] {U : Set M} (hU : IsOpen U) (g : SMet I M)
    (X : TfA (I := I) (M := M)) (d : ι → M → ℝ) (V : ι → TfA (I := I) (M := M))
    (W' : TfA (I := I) (M := M))
    (heq : ∀ z ∈ U, W' z = ∑ q, d q z • V q z) :
    ∀ z ∈ U, dirFA g X W' z = ∑ q, d q z • dirFA g X (V q) z := by
  intro z hz
  rw [dirFA, heq z hz, map_sum]
  refine Finset.sum_congr rfl (fun q _ => ?_)
  rw [map_smul]
  rfl

/-- The Leibniz rule for `dirFA g W' Z` on `U`, for `W'` a combination of fields. -/
lemma dirFA_sum_smul_eqOn {ι : Type*} [Fintype ι] {U : Set M} (hU : IsOpen U) (g : SMet I M)
    (d : ι → M → ℝ) (V : ι → TfA (I := I) (M := M)) (W' Z : TfA (I := I) (M := M))
    (hd : ∀ q, CMDiff[U] ∞ (d q)) (hV : ∀ q, KaSm (I := I) (M := M) U (V q))
    (hW' : KaSm (I := I) (M := M) U W') (hZ : KaSm (I := I) (M := M) U Z)
    (heq : ∀ z ∈ U, W' z = ∑ q, d q z • V q z) :
    ∀ z ∈ U, dirFA g W' Z z
      = ∑ q, (d q z • dirFA g (V q) Z z + ((mvfderiv I (d q) z) (Z z)) • V q z) := by
  intro z hz
  rw [dirFA_congr_on hU g Z hW' (kaSm_sum_smul d V hd hV) heq z hz]
  exact dirFA_finset_sum_smul_on Finset.univ hU g d V Z hd hV hZ z hz

/-- The recursion `cktA` at `Fin.cons`, in applied form. -/
lemma cktA_cons_apply (G : ℝ → SMet I M) (t : ℝ) (k : ℕ) (W : TfA (I := I) (M := M))
    (G0 : Fin (k+3) → TfA (I := I) (M := M)) (z : M) :
    cktA G t (k+1) (Fin.cons W G0) z
      = mvfderiv I (fun y => cktA G t k G0 y) z (W z)
        - ∑ i : Fin (k+3),
            cktA G t k (Function.update G0 i (dirFA (G 0) (G0 i) W)) z := by
  rw [cktA_cons]

/-! ## The two induction statements -/

/-- Smoothness of the level-`k` expression on `U`, for tuples of fields smooth on `U`. -/
abbrev KSm (G : ℝ → SMet I M) (t : ℝ) (U : Set M) (k : ℕ) : Prop :=
  ∀ F : Fin (k+3) → TfA (I := I) (M := M), (∀ p, KaSm (I := I) (M := M) U (F p)) →
    CMDiff[U] ∞ (fun z => cktA G t k F z)

/-- `C^∞(U)`-linearity of the level-`k` expression in each slot. -/
abbrev KLin (G : ℝ → SMet I M) (t : ℝ) (U : Set M) (k : ℕ) : Prop :=
  ∀ (F : Fin (k+3) → TfA (I := I) (M := M)) (s : Fin (k+3)) {ι : Type} [Fintype ι]
    (d : ι → M → ℝ) (V : ι → TfA (I := I) (M := M)) (W' : TfA (I := I) (M := M)),
    (∀ p, KaSm (I := I) (M := M) U (F p)) → (∀ q, CMDiff[U] ∞ (d q)) →
    (∀ q, KaSm (I := I) (M := M) U (V q)) → KaSm (I := I) (M := M) U W' →
    (∀ z ∈ U, W' z = ∑ q, d q z • V q z) →
    ∀ z ∈ U, cktA G t k (Function.update F s W') z
      = ∑ q, d q z * cktA G t k (Function.update F s (V q)) z

end Work.Diff.EXT.ATower

namespace Work.Diff.EXT.ATower

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [CompleteSpace E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I (⊤ : ℕ∞) M]
  [I.Boundaryless] [T2Space M]

lemma ksm_zero (G : ℝ → SMet I M) (t : ℝ) {U : Set M} (hU : IsOpen U) :
    KSm (I := I) (M := M) G t U 0 := by
  intro F hF
  have h1 : KaSm (I := I) (M := M) U (fun y => lcOf (G t) (F 1) y (F 0 y)) :=
    ka_lcField_smooth (I := I) (G t) hU (hF 1) (hF 0)
  have h0 : KaSm (I := I) (M := M) U (fun y => lcOf (G 0) (F 1) y (F 0 y)) :=
    ka_lcField_smooth (I := I) (G 0) hU (hF 1) (hF 0)
  exact ka_metric_pairing_smooth (I := I) (G t) (h1.sub_section h0) (hF 2)

lemma klin_zero (G : ℝ → SMet I M) (t : ℝ) {U : Set M} (hU : IsOpen U) :
    KLin (I := I) (M := M) G t U 0 := by
  intro F s ι _ d V W' hF hd hV hW' heq z hz
  have hF0 : KaSm (I := I) (M := M) U (F 0) := hF 0
  have hF1 : KaSm (I := I) (M := M) U (F 1) := hF 1
  have hF2 : KaSm (I := I) (M := M) U (F 2) := hF 2
  fin_cases s
  · simp only [cktA_zero, Function.update_self,
      Function.update_of_ne (by decide : (1 : Fin 3) ≠ (0 : Fin 3)),
      Function.update_of_ne (by decide : (2 : Fin 3) ≠ (0 : Fin 3))]
    exact aOf_lin_val0 G t d V (F 1) (F 2) W' z (heq z hz)
  · simp only [cktA_zero,
      Function.update_of_ne (by decide : (0 : Fin 3) ≠ (1 : Fin 3)),
      Function.update_self,
      Function.update_of_ne (by decide : (2 : Fin 3) ≠ (1 : Fin 3))]
    exact aOf_lin_slot1 hU G t d V (F 0) (F 2) W' hd hV hF0 hF2 hW' heq z hz
  · simp only [cktA_zero,
      Function.update_of_ne (by decide : (0 : Fin 3) ≠ (2 : Fin 3)),
      Function.update_of_ne (by decide : (1 : Fin 3) ≠ (2 : Fin 3)),
      Function.update_self]
    exact aOf_lin_val2 G t d V (F 0) (F 1) W' z (heq z hz)

end Work.Diff.EXT.ATower

namespace Work.Diff.EXT.ATower

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [CompleteSpace E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I (⊤ : ℕ∞) M]
  [I.Boundaryless] [T2Space M]

/-- Swapping two distinct slots in an update. -/
lemma update_swap {k : ℕ} (G0 : Fin k → TfA (I := I) (M := M)) {i j : Fin k} (h : i ≠ j)
    (X Y : TfA (I := I) (M := M)) :
    Function.update (Function.update G0 j X) i Y = Function.update (Function.update G0 i Y) j X := by
  funext p
  by_cases hp1 : p = i
  · rw [hp1, Function.update_self, Function.update_of_ne h X (Function.update G0 i Y),
      Function.update_self]
  · by_cases hp2 : p = j
    · rw [hp2, Function.update_of_ne (Ne.symm h) Y (Function.update G0 j X), Function.update_self,
        Function.update_self]
    · rw [Function.update_of_ne hp1 Y (Function.update G0 j X), Function.update_of_ne hp2 X G0,
        Function.update_of_ne hp2 X (Function.update G0 i Y), Function.update_of_ne hp1 Y G0]

/-- The algebraic identity underlying linearity in a slot for the packed recursion. -/
lemma sum_mul_sub_sum_univ {ι κ : Type*} [Fintype ι] [Fintype κ]
    (c : ι → ℝ) (f : ι → ℝ) (g : κ → ι → ℝ) :
    ∑ q, c q * (f q - ∑ i, g i q) = (∑ q, c q * f q) - ∑ i, ∑ q, c q * g i q := by
  have h1 : ∀ q, c q * (f q - ∑ i, g i q) = c q * f q - c q * (∑ i, g i q) :=
    fun q => mul_sub _ _ _
  rw [Finset.sum_congr rfl (fun q _ => h1 q), Finset.sum_sub_distrib]
  congr 1
  rw [Finset.sum_congr rfl (fun q _ => Finset.mul_sum Finset.univ _ (c q)), Finset.sum_comm]

end Work.Diff.EXT.ATower

namespace Work.Diff.EXT.ATower

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [CompleteSpace E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I (⊤ : ℕ∞) M]
  [I.Boundaryless] [T2Space M]

/-- A finite sum of functions which are `C^∞` on `U` is `C^∞` on `U`. -/
lemma cmdiff_sum {ι : Type*} [Fintype ι] {U : Set M} {f : ι → M → ℝ}
    (hf : ∀ i, CMDiff[U] ∞ (f i)) : CMDiff[U] ∞ (fun y => ∑ i, f i y) := by
  intro z hz
  exact ContMDiffWithinAt.sum (t := Finset.univ) (fun i _ => hf i z hz)

theorem ksm_klin (G : ℝ → SMet I M) (t : ℝ) {U : Set M} (hU : IsOpen U) :
    ∀ k, KSm (I := I) (M := M) G t U k ∧ KLin (I := I) (M := M) G t U k := by
  intro k
  induction k with
  | zero => exact ⟨ksm_zero G t hU, klin_zero G t hU⟩
  | succ k ih =>
      obtain ⟨ihsm, ihlin⟩ := ih
      refine ⟨?_, ?_⟩
      · -- ================= smoothness =================
        intro F hF
        have hG0 : ∀ p : Fin (k+3),
            KaSm (I := I) (M := M) U ((fun i : Fin (k+3) => F i.succ) p) := fun p => hF p.succ
        rw [show (fun z : M => cktA G t (k+1) F z) = cktA G t (k+1) F from rfl, cktA_succ]
        refine ContMDiffOn.sub ?_ ?_
        · exact ka_mvfderiv_apply (I := I) hU (ihsm _ hG0) (hF 0)
        · set Fs : Fin (k+3) → (M → ℝ) := fun i => cktA G t k
              (Function.update (fun j : Fin (k+3) => F j.succ) i
                (dirFA (G 0) ((fun j : Fin (k+3) => F j.succ) i) (F 0))) with hFs
          have hfun : (∑ s : Fin (k+3), Fs s) = fun y => ∑ s : Fin (k+3), Fs s y := by
            funext y; rw [Finset.sum_apply]
          rw [hfun]
          refine cmdiff_sum (fun i => ihsm _ ?_)
          intro p
          rcases eq_or_ne p i with h | h
          · rw [h, Function.update_self]
            exact ka_lcField_smooth (I := I) (G 0) hU (hG0 i) (hF 0)
          · rw [Function.update_of_ne h]; exact hG0 p
      · -- ================= linearity =================
        intro F s ι _ d V W' hF hd hV hW' heq z hz
        have hG0 : ∀ p : Fin (k+3),
            KaSm (I := I) (M := M) U ((fun i : Fin (k+3) => F i.succ) p) := fun p => hF p.succ
        have hZ : KaSm (I := I) (M := M) U (F 0) := hF 0
        by_cases hs0 : s = 0
        · -- ---------- case s = 0 ----------
          subst hs0
          simp only [update_zero_eq_consA, cktA_cons_apply]
          have hT1 : mvfderiv I (fun y => cktA G t k (fun i : Fin (k+3) => F i.succ) y) z (W' z)
              = ∑ q, d q z * mvfderiv I (fun y => cktA G t k (fun i : Fin (k+3) => F i.succ) y) z
                  (V q z) := by
            rw [heq z hz,
              mvfderiv_sum_smul_dir (ι := ι) d V
                (fun y => cktA G t k (fun i : Fin (k+3) => F i.succ) y) z]
          have hT2 : ∀ i : Fin (k+3),
              cktA G t k (Function.update (fun j : Fin (k+3) => F j.succ) i
                  (dirFA (G 0) ((fun j : Fin (k+3) => F j.succ) i) W')) z
              = ∑ q, d q z * cktA G t k (Function.update (fun j : Fin (k+3) => F j.succ) i
                  (dirFA (G 0) ((fun j : Fin (k+3) => F j.succ) i) (V q))) z := by
            intro i
            refine ihlin (fun j : Fin (k+3) => F j.succ) i d
              (fun q => dirFA (G 0) ((fun j : Fin (k+3) => F j.succ) i) (V q))
              (dirFA (G 0) ((fun j : Fin (k+3) => F j.succ) i) W') hG0 hd ?_ ?_ ?_ z hz
            · intro q
              exact ka_lcField_smooth (I := I) (G 0) hU (hG0 i) (hV q)
            · exact ka_lcField_smooth (I := I) (G 0) hU (hG0 i) hW'
            · exact dirFA_comb_eq hU (G 0) ((fun j : Fin (k+3) => F j.succ) i) d V W' heq
          rw [hT1, Finset.sum_congr rfl (fun i _ => hT2 i), sum_mul_sub_sum_univ]
        · -- ---------- case s = j.succ ----------
          obtain ⟨j, rfl⟩ := Fin.eq_succ_of_ne_zero hs0
          set G0 : Fin (k+3) → TfA (I := I) (M := M) := fun i : Fin (k+3) => F i.succ with hG0def
          have hG0' : ∀ p, KaSm (I := I) (M := M) U (G0 p) := by
            intro p; rw [hG0def]; exact hF p.succ
          simp only [update_succ_eq_consA, cktA_cons_apply, ← hG0def]
          have hT1 : mvfderiv I (fun y => cktA G t k (Function.update G0 j W') y) z (F 0 z)
              = ∑ q, (d q z * mvfderiv I (fun y => cktA G t k (Function.update G0 j (V q)) y) z
                    (F 0 z)
                  + (mvfderiv I (d q) z) (F 0 z)
                    * cktA G t k (Function.update G0 j (V q)) z) := by
            have hev : (fun y => cktA G t k (Function.update G0 j W') y)
                =ᶠ[𝓝 z] (fun y => ∑ q, d q y * cktA G t k (Function.update G0 j (V q)) y) := by
              filter_upwards [hU.mem_nhds hz] with y hy
              exact ihlin G0 j d V W' hG0' hd hV hW' heq y hy
            rw [mvfderiv_congr_eventuallyEq_apply (F 0 z) hev,
              mvfderiv_finset_sum_mul_apply Finset.univ d
                (fun q y => cktA G t k (Function.update G0 j (V q)) y) (F 0 z)]
            · intro q _
              exact mdiffAt_fun_of_cmdiff hU (hd q) hz
            · intro q _
              refine mdiffAt_fun_of_cmdiff hU (ihsm _ ?_) hz
              intro p
              rcases eq_or_ne p j with h | h
              · rw [h, Function.update_self]; exact hV q
              · rw [Function.update_of_ne h]; exact hG0' p
          have hVar_ne : ∀ i : Fin (k+3), i ≠ j →
              cktA G t k (Function.update (Function.update G0 j W') i
                  (dirFA (G 0) ((Function.update G0 j W') i) (F 0))) z
              = ∑ q, d q z * cktA G t k (Function.update (Function.update G0 j (V q)) i
                  (dirFA (G 0) ((Function.update G0 j (V q)) i) (F 0))) z := by
            intro i hij
            have hL : Function.update (Function.update G0 j W') i
                (dirFA (G 0) ((Function.update G0 j W') i) (F 0))
                = Function.update (Function.update G0 i (dirFA (G 0) (G0 i) (F 0))) j W' := by
              rw [Function.update_of_ne hij W' G0]
              exact update_swap G0 hij W' (dirFA (G 0) (G0 i) (F 0))
            rw [hL]
            have hih := ihlin (Function.update G0 i (dirFA (G 0) (G0 i) (F 0))) j d V W'
              (fun p => by
                rcases eq_or_ne p i with h | h
                · rw [h, Function.update_self]
                  exact ka_lcField_smooth (I := I) (G 0) hU (hG0' i) hZ
                · rw [Function.update_of_ne h]; exact hG0' p)
              hd hV hW' heq z hz
            rw [hih]
            refine Finset.sum_congr rfl (fun q _ => ?_)
            congr 1
            rw [Function.update_of_ne hij (V q) G0,
              ← update_swap G0 hij (V q) (dirFA (G 0) (G0 i) (F 0))]
          have hVar_j : cktA G t k (Function.update G0 j (dirFA (G 0) W' (F 0))) z
              = ∑ q, d q z * cktA G t k (Function.update G0 j (dirFA (G 0) (V q) (F 0))) z
                + ∑ q, (mvfderiv I (d q) z) (F 0 z)
                    * cktA G t k (Function.update G0 j (V q)) z := by
            have hW'' : KaSm (I := I) (M := M) U (dirFA (G 0) W' (F 0)) :=
              ka_lcField_smooth (I := I) (G 0) hU hW' hZ
            have hd2 : ∀ p : ι ⊕ ι, CMDiff[U] ∞
                (Sum.elim (fun q => d q) (fun q => fun y => (mvfderiv I (d q) y) (F 0 y)) p) := by
              intro p
              rcases p with q | q
              · exact hd q
              · exact ka_mvfderiv_apply (I := I) hU (hd q) hZ
            have hV2 : ∀ p : ι ⊕ ι, KaSm (I := I) (M := M) U
                (Sum.elim (fun q => dirFA (G 0) (V q) (F 0)) (fun q => V q) p) := by
              intro p
              rcases p with q | q
              · exact ka_lcField_smooth (I := I) (G 0) hU (hV q) hZ
              · exact hV q
            have heq2 : ∀ z' ∈ U, dirFA (G 0) W' (F 0) z'
                = ∑ p : ι ⊕ ι,
                    (Sum.elim (fun q => d q) (fun q => fun y => (mvfderiv I (d q) y) (F 0 y)) p) z'
                    • (Sum.elim (fun q => dirFA (G 0) (V q) (F 0)) (fun q => V q) p) z' := by
              intro z' hz'
              rw [Fintype.sum_sum_type]
              simp only [Sum.elim_inl, Sum.elim_inr]
              rw [dirFA_sum_smul_eqOn hU (G 0) d V W' (F 0) hd hV hW' hZ heq z' hz',
                Finset.sum_add_distrib]
            have hih := ihlin G0 j _ _
              (dirFA (G 0) W' (F 0)) hG0' hd2 hV2 hW'' heq2 z hz
            rw [hih, Fintype.sum_sum_type]
            simp only [Sum.elim_inl, Sum.elim_inr]
          have hVar : ∀ i : Fin (k+3),
              cktA G t k (Function.update (Function.update G0 j W') i
                  (dirFA (G 0) ((Function.update G0 j W') i) (F 0))) z
              = (∑ q, d q z * cktA G t k (Function.update (Function.update G0 j (V q)) i
                    (dirFA (G 0) ((Function.update G0 j (V q)) i) (F 0))) z)
                + (if i = j then ∑ q, (mvfderiv I (d q) z) (F 0 z)
                    * cktA G t k (Function.update G0 j (V q)) z else 0) := by
            intro i
            by_cases hij : i = j
            · rw [hij, if_pos rfl]
              simp only [Function.update_self, Function.update_idem]
              exact hVar_j
            · rw [if_neg hij, add_zero]
              exact hVar_ne i hij
          rw [hT1, Finset.sum_add_distrib, Finset.sum_congr rfl (fun i _ => hVar i),
            Finset.sum_add_distrib]
          have hE : ∑ i : Fin (k+3), (if i = j then ∑ q, (mvfderiv I (d q) z) (F 0 z)
                * cktA G t k (Function.update G0 j (V q)) z else 0)
              = ∑ q, (mvfderiv I (d q) z) (F 0 z)
                  * cktA G t k (Function.update G0 j (V q)) z := by
            rw [Finset.sum_ite_eq' Finset.univ j
              (fun _ => ∑ q, (mvfderiv I (d q) z) (F 0 z)
                  * cktA G t k (Function.update G0 j (V q)) z)]
            simp
          have hR : (∑ q, d q z * (mvfderiv I (fun y => cktA G t k (Function.update G0 j (V q)) y) z
                  (F 0 z)
                - ∑ i : Fin (k+3), cktA G t k (Function.update (Function.update G0 j (V q)) i
                    (dirFA (G 0) ((Function.update G0 j (V q)) i) (F 0))) z))
              = (∑ q, d q z * mvfderiv I (fun y => cktA G t k (Function.update G0 j (V q)) y) z
                    (F 0 z))
                - ∑ i : Fin (k+3), ∑ q, d q z * cktA G t k (Function.update (Function.update G0 j (V q)) i
                    (dirFA (G 0) ((Function.update G0 j (V q)) i) (F 0))) z := by
            have h1 : ∀ q, d q z * (mvfderiv I (fun y => cktA G t k (Function.update G0 j (V q)) y) z
                    (F 0 z)
                  - ∑ i : Fin (k+3), cktA G t k (Function.update (Function.update G0 j (V q)) i
                      (dirFA (G 0) ((Function.update G0 j (V q)) i) (F 0))) z)
                = d q z * mvfderiv I (fun y => cktA G t k (Function.update G0 j (V q)) y) z (F 0 z)
                  - d q z * ∑ i : Fin (k+3), cktA G t k (Function.update (Function.update G0 j (V q)) i
                      (dirFA (G 0) ((Function.update G0 j (V q)) i) (F 0))) z :=
              fun q => mul_sub _ _ _
            rw [Finset.sum_congr rfl (fun q _ => h1 q), Finset.sum_sub_distrib]
            congr 1
            rw [Finset.sum_congr rfl (fun q _ => Finset.mul_sum Finset.univ _ (d q z)),
              Finset.sum_comm]
          rw [hE, hR]
          ring

end Work.Diff.EXT.ATower

namespace Work.Diff.EXT.ATower

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [CompleteSpace E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I (⊤ : ℕ∞) M]
  [I.Boundaryless] [T2Space M]

theorem KaLinD_holds
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [CompleteSpace E]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I (⊤ : ℕ∞) M]
    [I.Boundaryless] [T2Space M]
    (hLC : Submission.Diff.LCSmooth I M) (G : ℝ → Submission.Diff.SMet I M) (t : ℝ) (x₀ : M) :
    ∀ k : ℕ, Work.Diff.EXT.KaLinD (I := I) (M := M) G t (chartAt H x₀).source k := by
  intro k
  have hU : IsOpen (chartAt H x₀).source := (chartAt H x₀).open_source
  have hlin := (ksm_klin (I := I) (M := M) G t hU k).2
  intro w i t3 W' ι _ d V hw ht3 hW' hd hV heq
  intro x hx
  have htuple : ∀ p : Fin (k+3), KaSm (I := I) (M := M) (chartAt H x₀).source
      ((mkT3 w t3) p) := by
    intro p
    refine Fin.addCases (motive := fun p => KaSm (I := I) (M := M) (chartAt H x₀).source
      ((mkT3 w t3) p)) ?_ ?_ p
    · intro i'; rw [mkT3_castAdd]; exact hw i'
    · intro q; rw [mkT3_natAdd]; exact ht3 q
  have hkey := hlin (mkT3 w t3) (Fin.castAdd 3 i) d V W' htuple hd hV hW' heq x hx
  have hL : KKT (I := I) (M := M) G t k (Function.update w i W') t3 x
      = cktA G t k (Function.update (mkT3 w t3) (Fin.castAdd 3 i) W') x := by
    rw [KKT, update_castAdd_mkT3]
    exact (cktA_mkT3_eq G t k (Function.update w i W') t3 x).symm
  have hR : ∀ q, KKT (I := I) (M := M) G t k (Function.update w i (V q)) t3 x
      = cktA G t k (Function.update (mkT3 w t3) (Fin.castAdd 3 i) (V q)) x := by
    intro q
    rw [KKT, update_castAdd_mkT3]
    exact (cktA_mkT3_eq G t k (Function.update w i (V q)) t3 x).symm
  have hRsum : (∑ q, d q x * KKT (I := I) (M := M) G t k (Function.update w i (V q)) t3 x)
      = ∑ q, d q x * cktA G t k (Function.update (mkT3 w t3) (Fin.castAdd 3 i) (V q)) x := by
    refine Finset.sum_congr rfl (fun q _ => ?_)
    rw [hR q]
  rw [hL, hRsum]
  exact hkey

end Work.Diff.EXT.ATower
