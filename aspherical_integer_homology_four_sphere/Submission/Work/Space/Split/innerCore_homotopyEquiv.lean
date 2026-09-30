import Mathlib
import Submission.Work.Space.Split

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


/-!
# The inner core of the filling pieces is homotopy equivalent to `⊔_v T_v`

The filling pieces of the assembled space `M̂` are the `⊔_v [-1,1]² × T_v`, with layer parameter
`sqNorm = ‖·‖∞`. The *inner core* `{sqNorm < 1}` of `Split.lean` (`innerCore a.Torus`) is the union
of the open collars, and it deformation retracts onto the union of the tori `⊔_v T_v` by pushing the
square coordinate `p` to `0`.

This file formalises that deformation retraction and packages it as a homotopy equivalence
`innerCore a.Torus ≃ₕ ⊔_v T_v`.

The formalisation goes through the "sigma model" `⊔_v (open square × T_v)`, which carries the same
topology as the inner core (as a subspace of `⊔_v ([-1,1]² × T_v)`) and in which the collapse map is
plain `Sigma.map`, avoiding dependent transports.

## Main results

* `Work.Space.Split.scalePt` — the scaling of the square by a factor in `[0,1]`.
* `Work.Space.Split.coreHomeo` — the sigma model of the inner core is homeomorphic to it.
* `Work.Space.Split.coreSigma_homotopyEquiv` — the sigma model is homotopy equivalent to `⊔_v T_v`.
* `Work.Space.Split.innerCore_homotopyEquiv` — the target statement.
-/

noncomputable section

open Set Topology Function
open scoped Topology unitInterval

namespace Work.Space.Split

/-! ## Scaling the square -/

/-- Scaling a point of the square by a factor in `[0,1]`: the layers `‖p‖∞` shrink linearly. -/
def scalePt (s : I) (p : SquarePt) : SquarePt :=
  ⟨(s : ℝ) • (p : E2), convex_sq.smul_mem_of_zero_mem zero_mem_Sq p.2 ⟨s.2.1, s.2.2⟩⟩

/-- The layer of a scaled point is the layer scaled by the factor. -/
theorem sqNorm_scalePt (s : I) (p : SquarePt) :
    sqNorm (scalePt s p) = (s : ℝ) * sqNorm p := by
  simp only [scalePt, sqNorm, nrm, PiLp.smul_apply, smul_eq_mul, abs_mul,
    abs_of_nonneg s.2.1]
  rw [mul_max_of_nonneg _ _ s.2.1]

/-- Scaling by `0` lands at the centre of the square. -/
theorem scalePt_zero (p : SquarePt) : scalePt 0 p = ⟨0, zero_mem_Sq⟩ := by
  apply Subtype.ext
  simp [scalePt]

/-- Scaling by `1` is the identity. -/
theorem scalePt_one (p : SquarePt) : scalePt 1 p = p := by
  apply Subtype.ext
  simp [scalePt]

theorem continuous_scalePt : Continuous fun w : I × SquarePt => scalePt w.1 w.2 := by
  have h : Continuous fun w : I × SquarePt => (w.1 : ℝ) • (w.2 : E2) :=
    (continuous_subtype_val.comp continuous_fst).smul
      (continuous_subtype_val.comp continuous_snd)
  exact Continuous.subtype_mk h (fun w =>
    convex_sq.smul_mem_of_zero_mem zero_mem_Sq w.2.2 ⟨w.1.2.1, w.1.2.2⟩)

/-- The centre of the square has layer `0`. -/
theorem sqNorm_zeroPt : sqNorm ⟨0, zero_mem_Sq⟩ = 0 := by
  simp [sqNorm, nrm]

/-! ## Generalities on sigma types -/

/-- A map of sigma types which is the identity on the base and continuous on every fiber is
continuous. -/
lemma continuous_sigma_map_id {ι : Type*} (S T : ι → Type*) [∀ i, TopologicalSpace (S i)]
    [∀ i, TopologicalSpace (T i)] (f : ∀ i, S i → T i) (hf : ∀ i, Continuous (f i)) :
    Continuous (Sigma.map id f) := by
  rw [continuous_sigma_iff]
  intro i
  show Continuous (fun x : S i => (⟨i, f i x⟩ : Σ j, T j))
  exact continuous_sigmaMk.comp (hf i)

/-- A map of sigma types which is the identity on the base and an embedding on every fiber is an
embedding. -/
lemma isEmbedding_sigma_map_id {ι : Type*} (S T : ι → Type*) [∀ i, TopologicalSpace (S i)]
    [∀ i, TopologicalSpace (T i)] (f : ∀ i, S i → T i) (hf : ∀ i, Topology.IsEmbedding (f i)) :
    Topology.IsEmbedding (Sigma.map id f) :=
  (Topology.isEmbedding_sigmaMap (f₁ := id) (f₂ := f) Function.injective_id).mpr hf

section

variable (a : Assembly)

/-- The collar fiber over a cusp: the open square times the torus `T_v`. -/
abbrev coreFiber (v : Cusp) : Type _ := {b : SquarePt × a.Torus v // sqNorm b.1 < 1}

/-- The inner core, as a disjoint union over the cusps (`T_v` included). -/
abbrev coreSigma : Type _ := Σ v : Cusp, coreFiber a v

/-- Inclusion of the collar model into the filling pieces `⊔_v ([-1,1]² × T_v)`. -/
def coreToY : coreSigma a → a.Y := fun w => ⟨w.1, w.2.1⟩

theorem continuous_coreToY : Continuous (coreToY a) :=
  continuous_sigma_map_id (fun v => coreFiber a v) (fun v => SquarePt × a.Torus v)
    (fun v => (Subtype.val : coreFiber a v → SquarePt × a.Torus v))
    (fun _ => continuous_subtype_val)

theorem isEmbedding_coreToY : Topology.IsEmbedding (coreToY a) :=
  isEmbedding_sigma_map_id (fun v => coreFiber a v) (fun v => SquarePt × a.Torus v)
    (fun v => (Subtype.val : coreFiber a v → SquarePt × a.Torus v))
    (fun _ => Topology.IsEmbedding.subtypeVal)

theorem coreToY_mem (w : coreSigma a) : coreToY a w ∈ innerCore a.Torus := w.2.2

theorem innerCore_subset_range : innerCore a.Torus ⊆ range (coreToY a) := by
  rintro q hq
  exact ⟨⟨q.1, ⟨q.2, hq⟩⟩, rfl⟩

/-- The sigma model of the inner core is homeomorphic to the inner core itself. -/
def coreHomeo : coreSigma a ≃ₜ {q : a.Y // q ∈ innerCore a.Torus} :=
  (Homeomorph.Set.univ (coreSigma a)).symm.trans
    ((Homeomorph.setCongr (Set.eq_univ_of_forall (coreToY_mem a)).symm).trans
      ((isEmbedding_coreToY a).homeomorphOfSubsetRange (innerCore_subset_range a)))

/-! ## The collapse of the collar onto the core -/

/-- The componentwise collapse `(b, s) ↦ (scalePt s b, ...)` of one collar fiber. -/
def Hcomp (v : Cusp) (z : coreFiber a v × I) : coreFiber a v :=
  ⟨(scalePt z.2 z.1.1.1, z.1.1.2), by
    rw [sqNorm_scalePt]
    calc (z.2 : ℝ) * sqNorm z.1.1.1 ≤ 1 * sqNorm z.1.1.1 :=
          mul_le_mul_of_nonneg_right z.2.2.2 (sqNorm_nonneg _)
      _ = sqNorm z.1.1.1 := one_mul _
      _ < 1 := z.1.2⟩

theorem continuous_Hcomp (v : Cusp) : Continuous (Hcomp a v) := by
  have hmem : ∀ z : coreFiber a v × I, sqNorm (scalePt z.2 z.1.1.1) < 1 := by
    intro z
    rw [sqNorm_scalePt]
    calc (z.2 : ℝ) * sqNorm z.1.1.1 ≤ 1 * sqNorm z.1.1.1 :=
          mul_le_mul_of_nonneg_right z.2.2.2 (sqNorm_nonneg _)
      _ = sqNorm z.1.1.1 := one_mul _
      _ < 1 := z.1.2
  have hunder : Continuous fun z : coreFiber a v × I =>
      (scalePt z.2 z.1.1.1, z.1.1.2) := by
    refine Continuous.prodMk ?_ ?_
    · exact continuous_scalePt.comp
        (continuous_snd.prodMk (continuous_fst.comp (continuous_subtype_val.comp continuous_fst)))
    · exact continuous_snd.comp (continuous_subtype_val.comp continuous_fst)
  exact Continuous.subtype_mk hunder hmem

/-! ## The homotopy equivalence `coreSigma a ≃ₕ ⊔_v T_v` -/

/-- Forget the collar, keeping the torus coordinate. -/
def toCuspSum : coreSigma a → (Σ v : Cusp, a.Torus v) :=
  Sigma.map (β₂ := fun v => a.Torus v) id (fun _ (b : coreFiber a _) => b.1.2)

theorem continuous_toCuspSum : Continuous (toCuspSum a) :=
  continuous_sigma_map_id (fun v => coreFiber a v) (fun v => a.Torus v)
    (fun _ b => b.1.2) (fun _ => continuous_snd.comp continuous_subtype_val)

/-- The continuous map forgetting the collar. -/
def toCuspSumCm : C(coreSigma a, Σ v : Cusp, a.Torus v) :=
  ⟨toCuspSum a, continuous_toCuspSum a⟩

/-- Put a point of the torus at the core `sqNorm = 0` of the collar. -/
def fromCuspSum : (Σ v : Cusp, a.Torus v) → coreSigma a :=
  Sigma.map (β₂ := fun v => coreFiber a v) id
    (fun _ (t : a.Torus _) => ⟨(⟨0, zero_mem_Sq⟩, t), by rw [sqNorm_zeroPt]; norm_num⟩)

theorem continuous_fromCuspSum : Continuous (fromCuspSum a) :=
  continuous_sigma_map_id (fun v => a.Torus v) (fun v => coreFiber a v)
    (fun _ t => ⟨(⟨0, zero_mem_Sq⟩, t), by rw [sqNorm_zeroPt]; norm_num⟩)
    (fun _ => Continuous.subtype_mk (continuous_const.prodMk continuous_id)
      (fun _ => by rw [sqNorm_zeroPt]; norm_num))

/-- The continuous map placing the torus at the core of the collar. -/
def fromCuspSumCm : C((Σ v : Cusp, a.Torus v), coreSigma a) :=
  ⟨fromCuspSum a, continuous_fromCuspSum a⟩

theorem toCuspSum_comp_fromCuspSum :
    (toCuspSumCm a).comp (fromCuspSumCm a) = ContinuousMap.id (Σ v : Cusp, a.Torus v) := by
  apply ContinuousMap.ext
  intro x
  cases x with
  | mk v t => rfl

/-- The distribution homeomorphism `I × ⊔_v F_v ≃ₜ ⊔_v (I × F_v)`. -/
def eI : I × coreSigma a ≃ₜ (Σ v : Cusp, coreFiber a v × I) :=
  (Homeomorph.prodComm I (coreSigma a)).trans
    (Homeomorph.sigmaProdDistrib (Y := I) (X := fun v : Cusp => coreFiber a v))

theorem eI_apply (s : I) (x : coreSigma a) : eI a (s, x) = ⟨x.1, (x.2, s)⟩ := by
  simp [eI]

/-- The collapse map, on the sigma model. -/
def homotopyMap : (Σ v : Cusp, coreFiber a v × I) → coreSigma a :=
  Sigma.map (β₂ := fun v => coreFiber a v) id (fun _ => Hcomp a _)

theorem continuous_homotopyMap : Continuous (homotopyMap a) :=
  continuous_sigma_map_id (fun v => coreFiber a v × I) (fun v => coreFiber a v)
    (fun _ => Hcomp a _) (fun _ => continuous_Hcomp a _)

/-- The collapse of the collar, as a map `I × coreSigma a → coreSigma a`. -/
def homotopyCm : C(I × coreSigma a, coreSigma a) :=
  ⟨fun z => homotopyMap a (eI a z), (continuous_homotopyMap a).comp (eI a).continuous⟩

theorem homotopyCm_apply (s : I) (x : coreSigma a) :
    homotopyCm a (s, x) = ⟨x.1, Hcomp a x.1 (x.2, s)⟩ := by
  show homotopyMap a (eI a (s, x)) = ⟨x.1, Hcomp a x.1 (x.2, s)⟩
  rw [eI_apply]
  rfl

theorem homotopyCm_zero (x : coreSigma a) :
    homotopyCm a (0, x) = (fromCuspSumCm a).comp (toCuspSumCm a) x := by
  rw [homotopyCm_apply]
  rcases x with ⟨v, b⟩
  rcases b with ⟨⟨p, t⟩, hb⟩
  simp only [Hcomp, scalePt_zero, fromCuspSumCm, toCuspSumCm, ContinuousMap.comp_apply,
    fromCuspSum, toCuspSum, id_eq]
  rfl

theorem homotopyCm_one (x : coreSigma a) :
    homotopyCm a (1, x) = x := by
  rw [homotopyCm_apply]
  rcases x with ⟨v, b⟩
  rcases b with ⟨⟨p, t⟩, hb⟩
  simp only [Hcomp, scalePt_one]

/-- The sigma model of the inner core is homotopy equivalent to the union of the tori. -/
theorem coreSigma_homotopyEquiv :
    Nonempty (ContinuousMap.HomotopyEquiv (coreSigma a) (Σ v : Cusp, a.Torus v)) :=
  ⟨ContinuousMap.HomotopyEquiv.mk (toCuspSumCm a) (fromCuspSumCm a)
    ⟨ContinuousMap.Homotopy.mk (homotopyCm a) (fun x => homotopyCm_zero a x)
      (fun x => homotopyCm_one a x)⟩
    (by rw [toCuspSum_comp_fromCuspSum a])⟩

end

theorem innerCore_homotopyEquiv (a : Assembly) :
    Nonempty (ContinuousMap.HomotopyEquiv {q : a.Y // q ∈ innerCore a.Torus}
      (Σ v : Cusp, a.Torus v)) :=
  ⟨(coreHomeo a).toHomotopyEquiv.symm.trans (coreSigma_homotopyEquiv a).some⟩

end Work.Space.Split
