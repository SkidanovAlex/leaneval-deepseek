/-
Copyright: subproject `OROneRel` -- one-relator combinatorics (node N2).

# The residual case of the Magnus step: the kernel route

`Work.OROneRel.magnusStepCase2` is the `l`-tracked Magnus--Moldavanskii step.  Its divisibility case
is proved (`Work.OROneRel.magnusStepCase2_of_weight`); the *residual* case is the one in which no
letter `t` of `u` carries a killing weight `c` with `c t = 1`.

This file contains the *assembly* half of a route to the residual case which needs no
graph-of-spaces input beyond the (proved) `ℤ`-quotient HNN structure `hnnKernelForm_tracking`:
if the kernel of the weight map

  `presentedCohom c u l hc : ⟨α | u ^ l⟩ →* Multiplicative ℤ`

is isomorphic to the one-relator group `⟨β | v ^ l⟩` in a way sending the root `v` to the class of
`u`, then the target holds.  Concretely:

* `presentedCohom_mk` evaluates the weight map on words;
* `closure_ker_presentedCohom` proves that the kernel of the weight map together with the class of a
  deck element `τ` (any `τ` with `cohom c τ = ofAdd 1`) generates `⟨α | u ^ l⟩` -- the generation
  input of `hnnKernelForm_tracking`;
* `magnusStepCase2_of_kernelData` is the assembly: the kernel data produces
  `⟨α | u ^ l⟩ ≃* HNNExtension ↥H ⊤ ⊤ ψ'` restricting to the inclusion of the base
  (`hnnKernelForm_tracking`), and `magnusStepCase2_of_hnnData` then transports the one-relator
  presentation `⟨β | v ^ l⟩` of `↥H` to the vertex, with the root tracking coming from `hψ`.

The one remaining input -- the *identification* `⟨β | v ^ l⟩ ≃* ker (presentedCohom c u l hc)` for
the residual case, i.e. Linton's `ℤ`-domain theorem for the `ℤ`-cover of `⟨α | u ^ l⟩` -- is *not*
part of this file: it is the open content of the residual case.  Everything here is proved.
-/
import Mathlib
import Submission.Work.OROneRel.Basic
import Submission.Work.OROneRel.MagnusGenDefs
import Submission.Work.OROneRel.vertexKernelDefs
import Submission.Work.OROneRel.hnnKernelForm_tracking
import Submission.Work.OROneRel.magnusStepCase2_of_hnnData

namespace Work.OROneRel

universe u

variable {α : Type u}

/-- **The weight map on words.**  `presentedCohom` is the descent of the weight `cohom c` to
`⟨α | u ^ l⟩`, so on the class of a word it is the weight of that word. -/
theorem presentedCohom_comp_mk (c : α → ℤ) (u : FreeGroup α) (l : ℕ) (hc : cohom c u = 1) :
    (presentedCohom c u l hc).comp (PresentedGroup.mk ({u ^ l} : Set (FreeGroup α))) =
      cohom c := by
  refine FreeGroup.ext_hom _ _ fun x => ?_
  show presentedCohom c u l hc (PresentedGroup.of x) = cohom c (FreeGroup.of x)
  rw [presentedCohom_of, cohom_of]

theorem presentedCohom_mk (c : α → ℤ) (u : FreeGroup α) (l : ℕ) (hc : cohom c u = 1)
    (w : FreeGroup α) :
    presentedCohom c u l hc (PresentedGroup.mk ({u ^ l} : Set (FreeGroup α)) w) = cohom c w :=
  congrArg (fun f : FreeGroup α →* Multiplicative ℤ => f w) (presentedCohom_comp_mk c u l hc)

/-- The generator decomposition: for a weight `c` killing `u` and a deck element `τ`, every
generator of `⟨α | u ^ l⟩` lies in any subgroup containing the kernel of the weight map and the class
of `τ`. -/
theorem of_mem_of_ker_le (c : α → ℤ) (u : FreeGroup α) (l : ℕ) (hc : cohom c u = 1)
    {τ : FreeGroup α} (hτ : cohom c τ = Multiplicative.ofAdd 1)
    {K : Subgroup (PresentedGroup ({u ^ l} : Set (FreeGroup α)))}
    (hker : ((presentedCohom c u l hc).ker : Set (PresentedGroup ({u ^ l} : Set (FreeGroup α)))) ⊆ K)
    (hτK : PresentedGroup.mk ({u ^ l} : Set (FreeGroup α)) τ ∈ K) :
    ∀ x : α, PresentedGroup.of x ∈ K := by
  intro x
  -- the kernel element `τ ^ (-(c x)) * of x`
  have hmem : PresentedGroup.mk ({u ^ l} : Set (FreeGroup α)) (τ ^ (-(c x)) * FreeGroup.of x) ∈
      (presentedCohom c u l hc).ker := by
    rw [MonoidHom.mem_ker, presentedCohom_mk, map_mul, map_zpow, cohom_of, hτ]
    rw [← Int.ofAdd_mul, ← ofAdd_add,
      show (1 : ℤ) * (-(c x)) + c x = 0 from by ring]
    rfl
  -- the decomposition of the generator `x` in `⟨α | u ^ l⟩`
  have hfree : τ ^ (c x) * (τ ^ (-(c x)) * FreeGroup.of x) = FreeGroup.of x := by
    rw [← mul_assoc, ← zpow_add, add_neg_cancel, zpow_zero, one_mul]
  have h1 : (PresentedGroup.mk ({u ^ l} : Set (FreeGroup α)) τ) ^ (c x) *
      PresentedGroup.mk ({u ^ l} : Set (FreeGroup α)) (τ ^ (-(c x)) * FreeGroup.of x) =
      PresentedGroup.mk ({u ^ l} : Set (FreeGroup α)) (FreeGroup.of x) := by
    rw [← map_zpow, ← map_mul, hfree]
  have hof : PresentedGroup.of x = (PresentedGroup.mk ({u ^ l} : Set (FreeGroup α)) τ) ^ (c x) *
      PresentedGroup.mk ({u ^ l} : Set (FreeGroup α)) (τ ^ (-(c x)) * FreeGroup.of x) := by
    rw [PresentedGroup.of, h1]
  rw [hof]
  exact K.mul_mem (K.zpow_mem hτK (c x)) (hker hmem)

/-- **The kernel of the weight map and a deck element generate.**  If `cohom c τ = ofAdd 1` then the
class of `τ` together with the kernel of `presentedCohom c u l hc` generates `⟨α | u ^ l⟩`. -/
theorem closure_ker_presentedCohom (c : α → ℤ) (u : FreeGroup α) (l : ℕ) (hc : cohom c u = 1)
    {τ : FreeGroup α} (hτ : cohom c τ = Multiplicative.ofAdd 1) :
    Subgroup.closure (((presentedCohom c u l hc).ker : Set (PresentedGroup ({u ^ l} : Set (FreeGroup α)))) ∪
      {PresentedGroup.mk ({u ^ l} : Set (FreeGroup α)) τ}) = ⊤ := by
  rw [eq_top_iff]
  intro g _
  refine PresentedGroup.generated_by _ _ (fun x => ?_) g
  exact of_mem_of_ker_le c u l hc hτ (fun y hy => Subgroup.subset_closure (Or.inl hy))
    (Subgroup.subset_closure (Or.inr (Set.mem_singleton_iff.mpr rfl))) x

/-- **The residual case of the Magnus step from the kernel identification.**

Given a weight `c` killing `u` together with a deck element `τ` (`cohom c τ = ofAdd 1`), and an
identification of `⟨β | v ^ l⟩` with the kernel of the weight map `presentedCohom c u l hc` which
sends the root `v` to the class of `u`, the target `magnusStepCase2` holds.  The HNN structure of
`⟨α | u ^ l⟩` over `↥ker` is `hnnKernelForm_tracking` (both associated subgroups are the whole
vertex, and the comparison map is the identity on the base), and the vertex is replaced by the
one-relator group `⟨β | v ^ l⟩` through `magnusStepCase2_of_hnnData`. -/
theorem magnusStepCase2_of_kernelData {α : Type u} (u : FreeGroup α) (l : ℕ) (hl : 1 ≤ l)
    (hu : ¬ Work.OROneRel.IsProperPower u)
    {c : α → ℤ} (hc : Work.OROneRel.cohom c u = 1)
    (hτ : ∃ τ : FreeGroup α, Work.OROneRel.cohom c τ = Multiplicative.ofAdd 1)
    (β : Type u) (v : FreeGroup β) (hpp : ¬ Work.OROneRel.IsProperPower v)
    (hnorm : Work.OROneRel.relatorNorm v < Work.OROneRel.relatorNorm u)
    (ψ : PresentedGroup ({v ^ l} : Set (FreeGroup β)) ≃*
      ↥(presentedCohom c u l hc).ker)
    (hψ : ((ψ (PresentedGroup.mk ({v ^ l} : Set (FreeGroup β)) v) : ↥(presentedCohom c u l hc).ker) :
        PresentedGroup ({u ^ l} : Set (FreeGroup α))) =
        PresentedGroup.mk ({u ^ l} : Set (FreeGroup α)) u) :
    ∃ (β : Type u) (v : FreeGroup β), ¬ Work.OROneRel.IsProperPower v ∧
      Work.OROneRel.relatorNorm v < Work.OROneRel.relatorNorm u ∧
      ∃ (A B : Subgroup (PresentedGroup ({v ^ l} : Set (FreeGroup β)))) (φ : A ≃* B)
        (e : PresentedGroup ({u ^ l} : Set (FreeGroup α)) ≃*
          HNNExtension (PresentedGroup ({v ^ l} : Set (FreeGroup β))) A B φ),
        ∃ c : HNNExtension (PresentedGroup ({v ^ l} : Set (FreeGroup β))) A B φ,
          e (PresentedGroup.mk ({u ^ l} : Set (FreeGroup α)) u) =
            c * HNNExtension.of (PresentedGroup.mk ({v ^ l} : Set (FreeGroup β)) v) * c⁻¹ := by
  classical
  obtain ⟨τ, hτ⟩ := hτ
  -- the generation input of `hnnKernelForm_tracking`
  have hgen : Subgroup.closure
      ((((presentedCohom c u l hc).ker : Subgroup (PresentedGroup ({u ^ l} : Set (FreeGroup α)))) : Set _) ∪
        {PresentedGroup.mk ({u ^ l} : Set (FreeGroup α)) τ}) = ⊤ :=
    closure_ker_presentedCohom c u l hc hτ
  have hφt : presentedCohom c u l hc (PresentedGroup.mk ({u ^ l} : Set (FreeGroup α)) τ) =
      Multiplicative.ofAdd 1 := by
    rw [presentedCohom_mk]; exact hτ
  obtain ⟨ψ', E, hEof, -, -⟩ :=
    hnnKernelForm_tracking ((presentedCohom c u l hc).ker) (PresentedGroup.mk ({u ^ l}) τ)
      (presentedCohom c u l hc) hφt (fun g => MonoidHom.mem_ker) hgen
  exact ⟨β, v, hpp, hnorm, magnusStepCase2_of_hnnData u l hl hu β v hpp hnorm
    ((presentedCohom c u l hc).ker) ψ hψ ⊤ ⊤ ψ' E hEof⟩

end Work.OROneRel
