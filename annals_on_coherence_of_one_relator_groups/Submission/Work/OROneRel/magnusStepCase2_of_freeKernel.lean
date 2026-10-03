import Mathlib
import Submission.Work.OROneRel.residualKernelAssembly
import Submission.Work.OROneRel.mmStepData_of_freeKernel_free
import Submission.Work.OROneRel.not_isProperPower_of

namespace Work.OROneRel

universe u

/-!
# The Magnus step from a *free* kernel of the weight map

`Work.OROneRel.magnusStepCase2_of_kernelData` (`Submission.Work.OROneRel.residualKernelAssembly`)
assembles the residual case of the Magnus--Moldavanskii step from the single remaining input: an
identification `⟨β | v ^ l⟩ ≃* ker (presentedCohom c u l hc)` sending the class of the vertex root
`v` to the class of `u`.  Its two ingredients are

* `hnnKernelForm_tracking` -- the *tracked* HNN structure `⟨α | u ^ l⟩ ≅ HNN ↥ker ⊤ ⊤ (conj τ)`
  with the comparison map pinned down on the base, and
* the transport bookkeeping `magnusStepCase2_of_hnnData`, which carries the root tracking to an
  isomorphism of `⟨α | u ^ l⟩` with an HNN extension of the vertex group.

The target of this file is the *free-kernel* case: when the weight map's kernel is free,
presented by the terminal one-relator group `⟨Option γ | of none⟩`
(`presentedGroup_optionNone_equiv_freeGroup`), the vertex identification and its root tracking are
available outright, so the Magnus step follows.  Note that no `¬ IsProperPower u` hypothesis is
needed: the transport argument is independent of it (and it is in any case forced by the freeness
of the kernel, `⟨α | u⟩` then being an extension of a free group by `ℤ`).

Since the transport argument of `magnusStepCase2_of_hnnData` does not use its `¬ IsProperPower u`
hypothesis, we reproduce it here as `magnusStepCase2_of_hnnData_root` with that hypothesis dropped;
then the free-kernel identification of the vertex is supplied by
`presentedGroup_optionNone_equiv_freeGroup` composed with the given `↥ker ≃* FreeGroup γ`.
-/

/-- **Root-tracking transport of an HNN structure** (the transport half of
`Work.OROneRel.magnusStepCase2_of_hnnData`, with the `¬ IsProperPower u` hypothesis removed since
the argument does not use it).

Given a subgroup `H ≤ ⟨α | u ^ l⟩` presented by `⟨β | v ^ l⟩` via `ψ` in such a way that the class
of `u` is the image of the class of `v`, together with an isomorphism
`e : HNNExtension ↥H A B φ ≃* ⟨α | u ^ l⟩` restricting to the inclusion on the base, the target
form of the Magnus step follows: `⟨α | u ^ l⟩` is an HNN extension of `⟨β | v ^ l⟩` in which the
class of `u` is the stable generator `of (mk v)` up to conjugation. -/
theorem magnusStepCase2_of_hnnData_root {α : Type u} (u : FreeGroup α) (l : ℕ)
    {β : Type u} {v : FreeGroup β}
    (H : Subgroup (PresentedGroup ({u ^ l} : Set (FreeGroup α))))
    (ψ : PresentedGroup ({v ^ l} : Set (FreeGroup β)) ≃* ↥H)
    (hψ : ((ψ (PresentedGroup.mk ({v ^ l} : Set (FreeGroup β)) v) : ↥H)
        : PresentedGroup ({u ^ l} : Set (FreeGroup α))) = PresentedGroup.mk ({u ^ l}) u)
    (A B : Subgroup ↥H) (φ : A ≃* B)
    (e : HNNExtension ↥H A B φ ≃* PresentedGroup ({u ^ l} : Set (FreeGroup α)))
    (he : ∀ h : ↥H, e (HNNExtension.of (φ := φ) h) = ((h : ↥H) : PresentedGroup ({u ^ l}))) :
    ∃ (A' B' : Subgroup (PresentedGroup ({v ^ l} : Set (FreeGroup β)))) (φ' : A' ≃* B')
      (e' : PresentedGroup ({u ^ l} : Set (FreeGroup α)) ≃*
        HNNExtension (PresentedGroup ({v ^ l} : Set (FreeGroup β))) A' B' φ'),
      ∃ c : HNNExtension (PresentedGroup ({v ^ l} : Set (FreeGroup β))) A' B' φ',
        e' (PresentedGroup.mk ({u ^ l} : Set (FreeGroup α)) u) =
          c * HNNExtension.of (PresentedGroup.mk ({v ^ l} : Set (FreeGroup β)) v) * c⁻¹ := by
  classical
  -- transport the HNN structure along `ψ⁻¹`
  obtain ⟨A', B', φ', Ĥ, -, -, hof, -⟩ :=
    hnnExtension_iso_of_baseMulEquiv ψ.symm A B φ
  refine ⟨A', B', φ', e.symm.trans Ĥ, 1, ?_⟩
  -- the class of `u` is the image of the class of `v`
  have hsymm : e.symm (PresentedGroup.mk ({u ^ l} : Set (FreeGroup α)) u) =
      HNNExtension.of (ψ (PresentedGroup.mk ({v ^ l} : Set (FreeGroup β)) v)) := by
    have h := he (ψ (PresentedGroup.mk ({v ^ l} : Set (FreeGroup β)) v))
    rw [hψ] at h
    rw [← h, MulEquiv.symm_apply_apply]
  rw [MulEquiv.trans_apply, hsymm, hof]
  simp

theorem magnusStepCase2_of_freeKernel {α : Type u} (u : FreeGroup α)
    (hn : 2 ≤ Work.OROneRel.relatorNorm u)
    {c : α → ℤ} (hc : Work.OROneRel.cohom c u = 1)
    (hτ : ∃ τ : FreeGroup α, Work.OROneRel.cohom c τ = Multiplicative.ofAdd 1)
    (hfree : ∃ γ : Type u, Nonempty (↥(Work.OROneRel.presentedCohom c u 1 hc).ker ≃* FreeGroup γ)) :
    ∃ (β : Type u) (v : FreeGroup β), ¬ Work.OROneRel.IsProperPower v ∧
      Work.OROneRel.relatorNorm v < Work.OROneRel.relatorNorm u ∧
      ∃ (A B : Subgroup (PresentedGroup ({v ^ 1} : Set (FreeGroup β)))) (φ : A ≃* B)
        (e : PresentedGroup ({u ^ 1} : Set (FreeGroup α)) ≃*
          HNNExtension (PresentedGroup ({v ^ 1} : Set (FreeGroup β))) A B φ),
        ∃ c : HNNExtension (PresentedGroup ({v ^ 1} : Set (FreeGroup β))) A B φ,
          e (PresentedGroup.mk ({u ^ 1} : Set (FreeGroup α)) u) =
            c * HNNExtension.of (PresentedGroup.mk ({v ^ 1} : Set (FreeGroup β)) v) * c⁻¹ := by
  classical
  obtain ⟨τ, hτ⟩ := hτ
  obtain ⟨γ, ⟨eK⟩⟩ := hfree
  -- the free group `F(γ)` presented by the terminal one-relator group `⟨Option γ | of none⟩`
  obtain ⟨eP⟩ := presentedGroup_optionNone_equiv_freeGroup γ
  -- the tracked HNN structure of `⟨α | u⟩` over the kernel of the weight map
  have hφt : presentedCohom c u 1 hc (PresentedGroup.mk ({u ^ 1} : Set (FreeGroup α)) τ) =
      Multiplicative.ofAdd 1 := by
    rw [presentedCohom_mk]
    exact hτ
  have hgen : Subgroup.closure (((presentedCohom c u 1 hc).ker :
      Set (PresentedGroup ({u ^ 1} : Set (FreeGroup α)))) ∪
      {PresentedGroup.mk ({u ^ 1} : Set (FreeGroup α)) τ}) = ⊤ :=
    closure_ker_presentedCohom c u 1 hc hτ
  obtain ⟨ψv, E, hEof, -, -⟩ := hnnKernelForm_tracking (presentedCohom c u 1 hc).ker
    (PresentedGroup.mk ({u ^ 1} : Set (FreeGroup α)) τ) (presentedCohom c u 1 hc) hφt
    (fun g => MonoidHom.mem_ker) hgen
  -- the vertex is the terminal relator `of none` on `Option γ`
  refine ⟨Option γ, FreeGroup.of (Option.none : Option γ),
    not_isProperPower_of (Option.none : Option γ), ?_, ?_⟩
  · -- its norm is `1 < 2 ≤ relatorNorm u`
    have h1 : relatorNorm (FreeGroup.of (Option.none : Option γ)) = 1 := by
      show FreeGroup.norm (FreeGroup.of (Option.none : Option γ)) = 1
      exact FreeGroup.norm_of _
    rw [h1]
    omega
  · -- the vertex identification `⟨Option γ | of none⟩ ≃* ker`, transported to `{v ^ 1} = {v}`
    have hrel : ({(FreeGroup.of (Option.none : Option γ)) ^ 1} : Set (FreeGroup (Option γ))) =
        {FreeGroup.of (Option.none : Option γ)} := by
      rw [pow_one]
    let ψ : PresentedGroup ({(FreeGroup.of (Option.none : Option γ)) ^ 1} :
        Set (FreeGroup (Option γ))) ≃* ↥(presentedCohom c u 1 hc).ker :=
      hrel.symm ▸ (eP.trans eK.symm)
    -- both the class of the vertex root and the class of `u` are trivial, so the tracking is free
    have hψ : ((ψ (PresentedGroup.mk ({(FreeGroup.of (Option.none : Option γ)) ^ 1} :
        Set (FreeGroup (Option γ))) (FreeGroup.of (Option.none : Option γ))) :
        ↥(presentedCohom c u 1 hc).ker) : PresentedGroup ({u ^ 1} : Set (FreeGroup α))) =
        PresentedGroup.mk ({u ^ 1} : Set (FreeGroup α)) u := by
      have h1 : ψ (PresentedGroup.mk ({(FreeGroup.of (Option.none : Option γ)) ^ 1} :
          Set (FreeGroup (Option γ))) (FreeGroup.of (Option.none : Option γ))) = 1 := by
        rw [PresentedGroup.one_of_mem (by simp), MulEquiv.map_one]
      have h2 : PresentedGroup.mk ({u ^ 1} : Set (FreeGroup α)) u = 1 :=
        PresentedGroup.one_of_mem (by simp)
      rw [h1, h2]
      rfl
    exact magnusStepCase2_of_hnnData_root u 1 (presentedCohom c u 1 hc).ker ψ hψ
      (⊤ : Subgroup ↥(presentedCohom c u 1 hc).ker)
      (⊤ : Subgroup ↥(presentedCohom c u 1 hc).ker) ψv E hEof

end Work.OROneRel
