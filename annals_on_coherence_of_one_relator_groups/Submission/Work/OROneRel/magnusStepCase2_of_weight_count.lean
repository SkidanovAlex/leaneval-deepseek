import Mathlib
import Submission.Work.OROneRel.wgtMMDefs
import Submission.Work.OROneRel.magnusStepCase2_of_weight

/-!
# The weighted Magnus step, in weight-count form

`Work.OROneRel.magnusStepCase2_of_weight_count` is the *weight count* variant of
`Work.OROneRel.magnusStepCase2_of_weight`: the explicit letter `t` and integer weight `c`
(`c t = 1`, `cohom c u = 1`, `t ∈ relatorLetters u`) are hypotheses rather than an existential, and
the drop in relator norm is recorded in the sharp combinatorial form produced by the construction
itself, namely

  `relatorNorm v ≤ (wvListAux c t 0 (wordOf u)).length`,

the length of the decorated word of `u` with the `t`-symbols deleted.  This is what the construction
actually yields (the tensor of `norm_mk_le` with the length of the relabelled decorated word `wWL`),
and it is exactly the count of surviving symbols, whereas `relatorNorm v < relatorNorm u` is the
coarser statement obtained from it by comparing with the length of `wordOf u`.

The proof is the construction of `magnusStepCase2_of_weight`: the decorated word `wWL c t (u ^ l)`,
the interval closure `wBeta c t (u ^ l)`, and the Magnus--Moldavanskii isomorphism
`wTheta`/`wPsi` transported along the power `u ↦ u ^ l`; only the final norm estimate is replaced by
the counting estimate above.
-/

namespace Work.OROneRel

universe u

/-- **The weight-count bound for the weighted Magnus rewriting.**  The relator `wW c t u` is the
word `wWL c t u`, a relabelling of the decorated word `wvListAux c t 0 (wordOf u)` with the
`t`-symbols deleted; hence its norm is at most the length of that word. -/
theorem relatorNorm_wW_le_wvListAux_length {α : Type u} [DecidableEq α] (c : α → ℤ) (t : α)
    (u : FreeGroup α) :
    relatorNorm (wW c t u) ≤ (wvListAux c t 0 (wordOf u)).length := by
  have hnorm : relatorNorm (wW c t u) ≤ (wWL c t u).length := by
    rw [wW, relatorNorm]
    exact @FreeGroup.norm_mk_le (wBeta c t u) (wWL c t u) (Classical.decEq _)
  rwa [wWL, List.length_map] at hnorm

theorem magnusStepCase2_of_weight_count {α : Type u} [DecidableEq α] (u : FreeGroup α) (l : ℕ)
    (hl : 1 ≤ l) (hu : ¬ Work.OROneRel.IsProperPower u)
    (hcyc : Work.OROneRel.IsCyclicallyReducedRelator u)
    (hn : 2 ≤ Work.OROneRel.relatorNorm u)
    (hbad : ∀ x : α, x ∈ Work.OROneRel.relatorLetters u → Work.OROneRel.eps x u ≠ 0)
    (t : α) (c : α → ℤ) (ht : t ∈ Work.OROneRel.relatorLetters u) (hct : c t = 1)
    (hcu : Work.OROneRel.cohom c u = 1) :
    ∃ (β : Type u) (v : FreeGroup β), ¬ Work.OROneRel.IsProperPower v ∧
      Work.OROneRel.relatorNorm v
        ≤ (Work.OROneRel.wvListAux c t 0 (Work.OROneRel.wordOf u)).length ∧
      ∃ (A B : Subgroup (PresentedGroup ({v ^ l} : Set (FreeGroup β)))) (φ : A ≃* B)
        (e : PresentedGroup ({u ^ l} : Set (FreeGroup α)) ≃*
          HNNExtension (PresentedGroup ({v ^ l} : Set (FreeGroup β))) A B φ),
        ∃ c' : HNNExtension (PresentedGroup ({v ^ l} : Set (FreeGroup β))) A B φ,
          e (PresentedGroup.mk ({u ^ l} : Set (FreeGroup α)) u) =
            c' * HNNExtension.of (PresentedGroup.mk ({v ^ l} : Set (FreeGroup β)) v) * c'⁻¹ := by
  classical
  have hu1 : u ≠ 1 := ne_one_of_not_isProperPower hu
  have hcyc' : IsCyclicallyReducedRelator (u ^ l) := isCyclicallyReducedRelator_pow hcyc l
  have h1' : u ^ l ≠ 1 := by
    intro h
    have hle := le_relatorNorm_pow u l hu1
    rw [h] at hle
    simp [relatorNorm, FreeGroup.norm] at hle
    omega
  have htw : wordOf (u ^ l) = (List.replicate l (wordOf u)).flatten :=
    wordOf_pow_flatten u l hcyc
  have ht' : t ∈ relatorLetters (u ^ l) := by
    obtain ⟨b, hb⟩ := ht
    refine ⟨b, ?_⟩
    show (t, b) ∈ wordOf (u ^ l)
    rw [htw]
    exact List.mem_flatten.mpr ⟨wordOf u, List.mem_replicate.mpr ⟨by omega, rfl⟩, hb⟩
  have hcu' : cohom c (u ^ l) = 1 := by rw [map_pow, hcu, one_pow]
  obtain ⟨hred', hcycW', hne', hTA', hTB', _⟩ := wgtToolboxGen c t (u ^ l) hcyc' h1' ht' hct hcu'
  have hnpW : ¬ IsProperPower (wW c t u) := not_isProperPower_wW c t u hct hcu hu
  obtain ⟨eβ, heβ, hpow⟩ := wgtPower c t u l hl hcyc hcu
  have hcw' : IsCyclicallyReducedRelator (wW c t (u ^ l)) := by
    rw [IsCyclicallyReducedRelator, wW, FreeGroup.toWord_mk, hred'.reduce_eq]
    exact hcycW'
  have hFw : FreiheitssatzAt (wW c t (u ^ l)) := freiheitssatz_at _
  obtain ⟨hphi, _, _, hchain⟩ := wgtPhiChain c t (u ^ l) hFw hcw' hTA' hTB'
  obtain ⟨hrel, hlift⟩ := wgtThetaFacts c t (u ^ l) hct hcu' hFw hcw' hTA' hTB' hchain
  obtain ⟨hcompat, hc2, hc3⟩ := wgtCompositions c t (u ^ l) hct hcu' hFw hcw' hTA' hTB' hphi hchain hrel
  let e1 : PresentedGroup ({u ^ l} : Set (FreeGroup α)) ≃* wK c t (u ^ l) hFw hcw' hTA' hTB' :=
    (MonoidHom.toMulEquiv (wPsi c t (u ^ l) hct hcu' hFw hcw' hTA' hTB' hcompat)
      (wTheta c t (u ^ l) hFw hcw' hTA' hTB' hrel) hc3 hc2).symm
  let f : wBeta c t u → wBeta c t (u ^ l) := fun p => eβ.symm p
  let v : FreeGroup (wBeta c t (u ^ l)) := FreeGroup.map f (wW c t u)
  have hvnorm : relatorNorm v = relatorNorm (wW c t u) := by
    show relatorNorm (FreeGroup.map f (wW c t u)) = relatorNorm (wW c t u)
    rw [relatorNorm_map_of_injective_wgt f eβ.symm.injective]
  have hnpv : ¬ IsProperPower v := by
    have := not_isProperPower_map_of f (fun q : wBeta c t (u ^ l) => eβ q)
      (fun p => Equiv.apply_symm_apply eβ p) hnpW
    simpa only [v, f] using this
  have hvpow : v ^ l = wW c t (u ^ l) := by
    have h1 : v ^ l = FreeGroup.map f ((wW c t u) ^ l) := (map_pow (FreeGroup.map f) (wW c t u) l).symm
    rw [h1, ← hpow, wgt_map_map]
    rw [show (fun p : wBeta c t (u ^ l) => f (eβ p)) = (fun p => p) from
      funext (fun p => by simp only [f]; exact Equiv.symm_apply_apply eβ p), wgt_map_id]
  have hset : ({v ^ l} : Set (FreeGroup (wBeta c t (u ^ l)))) = {wW c t (u ^ l)} := by
    rw [hvpow]
  have huf : u = wrho t c (FreeGroup.map (fun p : wBeta c t (u ^ l) => (p.1 : WgtBeta t)) v) := by
    have h1 : FreeGroup.map (fun p : wBeta c t (u ^ l) => (p.1 : WgtBeta t)) v
        = FreeGroup.map (fun p : wBeta c t u => (p.1 : WgtBeta t)) (wW c t u) := by
      show FreeGroup.map (fun p : wBeta c t (u ^ l) => (p.1 : WgtBeta t)) (FreeGroup.map f (wW c t u)) = _
      rw [wgt_map_map]
      rw [show (fun p : wBeta c t u => ((f p).1 : WgtBeta t))
          = (fun p : wBeta c t u => (p.1 : WgtBeta t)) from
        funext (fun p => by
          rw [← heβ (eβ.symm p)]
          exact congrArg Subtype.val (Equiv.apply_symm_apply eβ p))]
    rw [h1]
    exact (wrho_wW c t u hct hcu).symm
  have htrack : e1 (PresentedGroup.mk ({u ^ l} : Set (FreeGroup α)) u)
      = HNNExtension.of (PresentedGroup.mk ({wW c t (u ^ l)} : Set (FreeGroup (wBeta c t (u ^ l)))) v) := by
    have hcomp : (wTheta c t (u ^ l) hFw hcw' hTA' hTB' hrel).comp
        (PresentedGroup.mk ({u ^ l} : Set (FreeGroup α)))
        = FreeGroup.lift (wThetaFun c t (u ^ l) hFw hcw' hTA' hTB') := by
      refine FreeGroup.ext_hom _ _ fun y => ?_
      show wTheta c t (u ^ l) hFw hcw' hTA' hTB' hrel (PresentedGroup.of y)
          = FreeGroup.lift (wThetaFun c t (u ^ l) hFw hcw' hTA' hTB') (FreeGroup.of y)
      rw [FreeGroup.lift_apply_of]
      exact wTheta_of c t (u ^ l) hFw hcw' hTA' hTB' hrel y
    have h2 : e1 (PresentedGroup.mk ({u ^ l} : Set (FreeGroup α)) u)
        = (FreeGroup.lift (wThetaFun c t (u ^ l) hFw hcw' hTA' hTB')) u :=
      congrArg (fun g => g u) hcomp
    have h3 : (FreeGroup.lift (wThetaFun c t (u ^ l) hFw hcw' hTA' hTB')) u
        = (FreeGroup.lift (wThetaFun c t (u ^ l) hFw hcw' hTA' hTB'))
            (wrho t c (FreeGroup.map (fun p : wBeta c t (u ^ l) => (p.1 : WgtBeta t)) v)) :=
      congrArg (FreeGroup.lift (wThetaFun c t (u ^ l) hFw hcw' hTA' hTB')) huf
    rw [h2, h3]
    exact hlift v
  refine ⟨wBeta c t (u ^ l), v, hnpv,
    hvnorm ▸ relatorNorm_wW_le_wvListAux_length c t u, ?_⟩
  rw [hset]
  exact ⟨wA c t (u ^ l), wB c t (u ^ l), wPhi hFw hcw' hTA' hTB', e1, 1, by
    rw [htrack, one_mul, inv_one, mul_one]⟩

end Work.OROneRel
