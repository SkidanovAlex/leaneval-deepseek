import Mathlib
import Submission.Work.Thom.chernClass_comap
import Submission.Work.Thom.complexification
import Submission.Work.Thom.manifoldP1
import Submission.Work.Cohomology.punit
import Submission.Work.Cohomology.sphereCohomologyZero

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 400000

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1600000
set_option linter.unusedSectionVars false
set_option linter.style.haveILetI false

/-!
# Vanishing of the characteristic classes of trivial and pulled-back bundles

The **first consequence of the naturality of the Chern classes** (`Work.Thom.chernClass_comap`,
ADDENDUM 22 of `README.md`) is a *vanishing principle*: if `W` is a complex bundle over `B₀` whose
`j`-th Chern class is `0` — for instance because `H^{2j}(B₀;ℤ) = 0` — then every pullback
`f^*W` has `c_j(f^*W) = 0`.

Two instances are delivered here, both of them things the deliverable of this chapter asks for:

* `Work.Thom.chernClass_trivial` — **`c_j` of a trivial complex bundle is `0` for `j ≠ 0`**
  (`c_0 = 1` is `Work.Thom.chernClass_zero_eq_oneH`).  Indeed the trivial bundle over `B` is the
  pullback of the trivial bundle over the **one-point space**, where `H^{2j} = 0`
  (`Work.Cohomology.punit`), and `c_j` is natural.
* `Work.Thom.chernClass_comap_eq_zero_of_subsingleton_cohomology` and
  `Work.Thom.chernClass_comap_eq_zero_of_sphere` — the same for a pullback from any base with
  vanishing `H^{2j}` (in particular from a sphere `Sⁿ` with `2j ≠ 0, n`).

Consequences for the Pontryagin classes (`Work.Thom.pontryagin1`, `Work.Thom.pontryaginClass`):

* `Work.Thom.pontryagin1_trivial` — `p₁` of a **trivial real bundle** is `0`;
* `Work.Thom.pontryaginClass_trivial` — `p_i` of a trivial real bundle is `0` for `i ≠ 0`.

This is the case "`E ⊕ ε^k`" of *stability* in which the other summand is trivial; the general
Whitney formula `p(E ⊕ F) = p(E)p(F)` — hence stability `p(E ⊕ ε^k) = p(E)` and `p₁(TSⁿ) = 0` for
`TSⁿ ⊕ ε¹ ≅ ε^{n+1}` trivial — still needs the splitting principle, whose exact remaining content
is recorded in `README.md` ADDENDUM 23.
-/

namespace Work.Thom

open Work.TangentClasses

noncomputable section

variable {B : Type} [TopologicalSpace B] {F : Type} [NormedAddCommGroup F] [NormedSpace ℂ F]
variable {ι : Type}

/-! ## The trivial bundle over the point -/

/-- **Pulling back the trivial bundle gives the trivial bundle.**  In particular the trivial bundle
over `B` is the pullback of the trivial bundle over the one-point space `PUnit` along the unique
map `B → PUnit`, which is what makes the vanishing of its Chern classes a computation over the
point. -/
theorem bundleComap_trivial [Inhabited ι] (f : C(B, PUnit)) :
    bundleComap (trivialVectorBundleCore ℂ PUnit F ι) f = trivialVectorBundleCore ℂ B F ι := by
  refine bundleCore_ext (funext fun i => ?_) rfl (fun i j x => rfl)
  exact Set.preimage_univ

/-- The **positive-degree cohomology of the one-point space vanishes**, in the `Subsingleton` form
used for classes (`Work.Cohomology.punit`). -/
theorem subsingleton_cohomology_punit {k : ℕ} (hk : 0 < k) :
    Subsingleton (Work.Cohomology.singularCohomology ℤ k (TopCat.of PUnit)) := by
  obtain ⟨n, rfl⟩ : ∃ n, k = n + 1 := ⟨k - 1, by omega⟩
  exact ModuleCat.subsingleton_of_isZero (Work.Cohomology.punit ℤ n)

/-! ## The vanishing principle -/

/-- **The vanishing principle**: the `j`-th Chern class of a pullback of `W` is `0` as soon as that
of `W` is. -/
theorem chernClass_bundleComap_eq_zero {m j : ℕ} {B₀ : Type} [TopologicalSpace B₀] {ι : Type}
    [Fintype ι] (W : VectorBundleCore ℂ B₀ (EuclideanSpace ℂ (Fin m)) ι) (f : C(B, B₀))
    (hW : chernClass m j W = 0) : chernClass m j (bundleComap W f) = 0 := by
  rw [chernClass_comap W f, hW, map_zero]

/-- **The vanishing principle, cohomological form**: if the target of the pullback has vanishing
`H^{2j}`, every pulled-back `c_j` vanishes. -/
theorem chernClass_bundleComap_eq_zero_of_subsingleton {m j : ℕ} {B₀ : Type}
    [TopologicalSpace B₀] {ι : Type} [Fintype ι]
    (W : VectorBundleCore ℂ B₀ (EuclideanSpace ℂ (Fin m)) ι) (f : C(B, B₀))
    (h : Subsingleton (Coh ℤ (2 * j) B₀)) : chernClass m j (bundleComap W f) = 0 := by
  haveI := h
  rw [chernClass_comap W f, Subsingleton.elim (chernClass m j W) 0, map_zero]

/-- **The Chern classes of a trivial complex bundle vanish above degree `0`.** -/
theorem chernClass_trivial {m j : ℕ} [Fintype ι] [Inhabited ι] (hj : j ≠ 0) :
    chernClass m j (trivialVectorBundleCore ℂ B (EuclideanSpace ℂ (Fin m)) ι) = 0 := by
  have h := chernClass_comap
    (Z := trivialVectorBundleCore ℂ PUnit (EuclideanSpace ℂ (Fin m)) ι)
    (f := ContinuousMap.const B PUnit.unit) (j := j)
  rw [bundleComap_trivial (F := EuclideanSpace ℂ (Fin m)) (ContinuousMap.const B PUnit.unit)] at h
  haveI : Subsingleton (Coh ℤ (2 * j) PUnit) :=
    subsingleton_cohomology_punit (k := 2 * j) (by omega)
  rw [Subsingleton.elim (chernClass m j
    (trivialVectorBundleCore ℂ PUnit (EuclideanSpace ℂ (Fin m)) ι)) 0, map_zero] at h
  exact h

/-- The **cohomology of a sphere vanishes off degrees `0` and `n`**, in the `Subsingleton` form
(`Work.Cohomology.sphereCohomologyZero`). -/
theorem subsingleton_cohomology_sphere {n k : ℕ} (hn : 1 ≤ n) (h0 : k ≠ 0) (hnk : k ≠ n) :
    Subsingleton (Coh ℤ k ↥(Metric.sphere (0 : EuclideanSpace ℝ (Fin (n + 1))) 1)) :=
  ModuleCat.subsingleton_of_isZero (Work.Cohomology.sphereCohomologyZero n k hn h0 hnk)

/-- **A bundle pulled back from a sphere has vanishing Chern classes in the middle range**: for
`2j ∉ {0, n}`, `c_j(f^*W) = 0` for any bundle `W` over `Sⁿ` and any `f : B → Sⁿ`. -/
theorem chernClass_bundleComap_eq_zero_of_sphere {m j n : ℕ} (hn : 1 ≤ n) (h0 : 2 * j ≠ 0)
    (hnk : 2 * j ≠ n) {ι : Type} [Fintype ι]
    (W : VectorBundleCore ℂ ↥(Metric.sphere (0 : EuclideanSpace ℝ (Fin (n + 1))) 1)
      (EuclideanSpace ℂ (Fin m)) ι)
    (f : C(B, ↥(Metric.sphere (0 : EuclideanSpace ℝ (Fin (n + 1))) 1))) :
    chernClass m j (bundleComap W f) = 0 :=
  chernClass_bundleComap_eq_zero_of_subsingleton W f
    (subsingleton_cohomology_sphere hn h0 hnk)

/-- **A bundle over a base with vanishing `H^{2j}` has vanishing `c_j`.**  (The trivial bundle is the
case `B = PUnit` of this, by `Work.Thom.chernClass_trivial`.) -/
theorem chernClass_eq_zero_of_subsingleton {m j : ℕ} {ι : Type} [Fintype ι]
    (Z : VectorBundleCore ℂ B (EuclideanSpace ℂ (Fin m)) ι)
    (h : Subsingleton (Coh ℤ (2 * j) B)) : chernClass m j Z = 0 := by
  haveI := h
  exact Subsingleton.elim _ _

/-- **A real bundle over a base with vanishing `H⁴` has vanishing first Pontryagin class.** -/
theorem pontryagin1_eq_zero_of_subsingleton {k : ℕ} {ι : Type} [Fintype ι]
    (Z : RealBundle B (EuclideanSpace ℝ (Fin k)) ι) (h : Subsingleton (Coh ℤ 4 B)) :
    pontryagin1 Z = 0 := by
  rw [pontryagin1_def]
  have h2 : Subsingleton (Coh ℤ (2 * 2) B) := by
    rw [show (2 : ℕ) * 2 = 4 from rfl]
    exact h
  rw [chernClass_eq_zero_of_subsingleton (m := k) (j := 2) (complexificationCore Z) h2,
    neg_zero]

/-- **The first Pontryagin class of a real bundle pulled back from `Sⁿ`, `n ≠ 4`, vanishes**: the
target of the pullback has vanishing `H⁴`. -/
theorem pontryagin1_bundleComap_eq_zero_of_sphere {k : ℕ} (n : ℕ) (hn : 1 ≤ n) (hn4 : n ≠ 4)
    {ι : Type} [Fintype ι]
    (W : RealBundle ↥(Metric.sphere (0 : EuclideanSpace ℝ (Fin (n + 1))) 1)
      (EuclideanSpace ℝ (Fin k)) ι)
    (π : C(B, ↥(Metric.sphere (0 : EuclideanSpace ℝ (Fin (n + 1))) 1))) :
    pontryagin1 (bundleComap W π) = 0 := by
  have h : Subsingleton (Coh ℤ (2 * 2) ↥(Metric.sphere (0 : EuclideanSpace ℝ (Fin (n + 1))) 1)) :=
    subsingleton_cohomology_sphere hn (by norm_num) (by omega)
  rw [pontryagin1_def, complexificationCore_bundleComap,
    chernClass_bundleComap_eq_zero_of_subsingleton (complexificationCore W) π h, neg_zero]

/-! ## The complexification of a trivial real bundle -/

/-- **The complexification of a trivial real bundle is the trivial complex bundle.** -/
theorem complexificationCore_trivial {k : ℕ} [Inhabited ι] :
    complexificationCore (RealBundle.trivial B (EuclideanSpace ℝ (Fin k)) ι)
      = trivialVectorBundleCore ℂ B (EuclideanSpace ℂ (Fin k)) ι := by
  refine bundleCore_ext rfl rfl (fun i j x => ?_)
  apply ContinuousLinearMap.ext
  intro v
  rw [complexificationCore_coordChange]
  have h1 : (RealBundle.trivial B (EuclideanSpace ℝ (Fin k)) ι).coordChange i j x
      = ContinuousLinearMap.id ℝ (EuclideanSpace ℝ (Fin k)) := rfl
  rw [h1]
  have h2 : cxTrans (ContinuousLinearMap.id ℝ (EuclideanSpace ℝ (Fin k)))
      = ContinuousLinearMap.id ℂ (EuclideanSpace ℂ (Fin k)) := by
    rw [show ContinuousLinearMap.id ℝ (EuclideanSpace ℝ (Fin k))
        = (1 : EuclideanSpace ℝ (Fin k) →L[ℝ] EuclideanSpace ℝ (Fin k)) from rfl,
      show ContinuousLinearMap.id ℂ (EuclideanSpace ℂ (Fin k))
        = (1 : EuclideanSpace ℂ (Fin k) →L[ℂ] EuclideanSpace ℂ (Fin k)) from rfl]
    exact cxTrans_one (k := k)
  rw [h2]
  rfl

/-! ## The Pontryagin classes of a trivial bundle -/

/-- **The degree cast `Work.Thom.cohTransport` sends `0` to `0`.** -/
theorem cohTransport_zero {B : Type} [TopologicalSpace B] {n n' : ℕ} (h : n = n') :
    cohTransport h (0 : Coh ℤ n B) = 0 :=
  map_zero (cohTransportLM h)

/-- **The first Pontryagin class of a trivial real bundle is `0`.** -/
theorem pontryagin1_trivial {k : ℕ} [Fintype ι] [Inhabited ι] :
    pontryagin1 (RealBundle.trivial B (EuclideanSpace ℝ (Fin k)) ι) = 0 := by
  rw [pontryagin1_def, complexificationCore_trivial]
  rw [chernClass_trivial (m := k) (j := 2) (by norm_num), neg_zero]

/-- **The Pontryagin classes of a trivial real bundle vanish above degree `0`.** -/
theorem pontryaginClass_trivial (i : ℕ) {k : ℕ} [Fintype ι] [Inhabited ι] (hi : i ≠ 0) :
    pontryaginClass i (RealBundle.trivial B (EuclideanSpace ℝ (Fin k)) ι) = 0 := by
  rw [pontryaginClass, complexificationCore_trivial,
    chernClass_trivial (m := k) (j := 2 * i) (by omega), zsmul_zero, cohTransport_zero]

end

end Work.Thom
