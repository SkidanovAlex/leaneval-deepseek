/-
Copyright: subproject `OROneRel` -- one-relator combinatorics (node N2).

# The substituted root of the Magnus step again satisfies Karrass--Magnus--Solitar

`Work.OROneRel.kmsRoot_subst_image`: if `u` is cyclically reduced, not a proper power, `t, x` are
letters of `u` with `x ≠ t` and `σ_x u ≠ 0`, then the Magnus/Putman substitution
`u' = subst t x (σ_x u) (σ_t u) u` (`t ↦ t^(σ_x u)`, `x ↦ x * t^(-(σ_t u))`, other generators fixed)
makes the exponent sum of `t` vanish, and `KMSRoot u' l` holds for every `l ≥ 1`, given the statement
of the theorem for every relator of strictly smaller norm.

## The proof

Since `σ_t u' = (σ_x u) (σ_t u) - (σ_t u) (σ_x u) = 0`, the exponent-sum-zero Magnus--Moldavanskii
step applies to `u'`: `⟨α | u'^l⟩` is an HNN extension of the one-relator group
`⟨mmBeta t (u'^l) | (rootW t u' l)^l⟩` (with stable letter `t`), and the class of `u'` is conjugate to
the class of the *root* `rootW t u' l`.  So `kmsRoot_of_hnn` reduces `KMSRoot u' l` to
`KMSRoot (rootW t u' l) l`, which is supplied by the induction hypothesis as soon as

  `relatorNorm (rootW t u' l) < relatorNorm u`.

That is the whole point of the substitution: `rootW` is a word in the decorated letters, so
`relatorNorm (rootW t u' l) ≤ nonTLetters t u'`; the substitution replaces every `t`-letter by a
power of `t` and every other letter by a word with a single letter `≠ t`, hence
`nonTLetters t u' ≤ nonTLetters t u`; and `t` occurs in `u`, so `nonTLetters t u < relatorNorm u`.

Two technical points are handled on the way.

* `u'` need not be cyclically reduced (e.g. `u = t x` gives `u' = t x t⁻¹`), and the Magnus step
  demands a cyclically reduced relator.  We therefore pass to `w = cyclicReduction u'`, prove
  `KMSRoot w l` and transport back along the isomorphism `⟨α | u'^l⟩ ≃* ⟨α | w^l⟩` of conjugate
  relators (`KMSRoot_of_mulEquiv_conj`).  The substitution still does not increase the non-`t`
  letter count (`nonTLetters_cyclicReduction_le`), which is what keeps the norm bound: the two ends
  removed by the cyclic reduction only remove letters.
* `u'` is not a proper power (`wcp_not_isProperPower_subst`), so neither is its cyclic reduction
  (`not_isProperPower_of_isConj`).

The two cases of `KMSRoot w l` are handled uniformly by the induction hypothesis: if `t` no longer
occurs in `w`, then `relatorNorm w = nonTLetters t w < relatorNorm u` and the induction hypothesis
applies to `w` directly; otherwise the exponent-sum-zero Magnus step at `w` runs and the induction
hypothesis applies to its root.

The Magnus step itself is reproduced here (`kmsRootMagnusStep_aux`) rather than imported from
`Submission.Work.OROneRel.magnus_step_root`, so that this module does not depend on the (much larger)
Magnus--Moldavanskii development.
-/
import Mathlib
import Submission.Work.OROneRel.NoZeroDefs
import Submission.Work.OROneRel.KMSDefs
import Submission.Work.OROneRel.HNNStep
import Submission.Work.OROneRel.MagnusRewrite
import Submission.Work.OROneRel.eps_eq_toAdd_sigma
import Submission.Work.OROneRel.mmStepData_of_expsum_zero
import Submission.Work.OROneRel.EpsV2.Toolbox
import Submission.Work.OROneRel.ne_one_of_not_isProperPower
import Submission.Work.OROneRel.isCyclicallyReducedRelator_pow
import Submission.Work.OROneRel.relatorNorm_pow_of_isCyclicallyReduced
import Submission.Work.OROneRel.freiheitssatz_at
import Submission.Work.OROneRel.wcp_not_isProperPower_subst
import Submission.Work.OROneRel.psiSubstDefs
import Submission.Work.OROneRel.wnePsiNotProperPower
import Submission.Work.OROneRel.nonTLetters_Psi_le
import Submission.Work.OROneRel.nonTLetters_lt_norm
import Submission.Work.OROneRel.nonTLetters_cyclicReduction_le
import Submission.Work.OROneRel.presentedGroup_pow_conj_iso
import Submission.Work.OROneRel.exists_cyclicallyReduced_conjugate
import Submission.Work.OROneRel.sigma_cyclicReduction
import Submission.Work.OROneRel.not_isProperPower_of_isConj

namespace Work.OROneRel

universe u

/-! ## The exponent-sum-zero Magnus step at the root, with an explicit base -/

/-- The defining relator of the base of the exponent-sum-zero Magnus step at the root `u`: the
`l`-th power of the Magnus rewriting `EpsV2.rootW t u l`. -/
abbrev kmsRootRel {α : Type u} (t : α) (u : FreeGroup α) (l : ℕ)
    (hu : IsCyclicallyReducedRelator u) (he : eps t u = 0) (hl : 1 ≤ l) :
    Set (FreeGroup (mmBeta t (u ^ l))) :=
  {(Work.OROneRel.EpsV2.rootW t u l hu he hl) ^ l}

/-- **The exponent-sum-zero Magnus step, with the root tracked and the base explicit.**  This is
`Work.OROneRel.magnus_step_root_eps_zero_aux` with the (identical) Magnus rewriting of
`Submission.Work.OROneRel.EpsV2.Toolbox`, proved here so that the module does not depend on
`Submission.Work.OROneRel.magnus_step_root`. -/
theorem kmsRootMagnusStep_aux {α : Type u} (u : FreeGroup α) (l : ℕ) (hl : 1 ≤ l) (t : α)
    (hu : ¬ IsProperPower u)
    (hcyc : IsCyclicallyReducedRelator u)
    (ht : t ∈ relatorLetters u)
    (he : eps t u = 0) :
    ∃ (A B : Subgroup (PresentedGroup (kmsRootRel t u l hcyc he hl)))
      (φ : A ≃* B)
      (e : PresentedGroup ({u ^ l} : Set (FreeGroup α)) ≃*
        HNNExtension (PresentedGroup (kmsRootRel t u l hcyc he hl)) A B φ),
        ∃ c : HNNExtension (PresentedGroup (kmsRootRel t u l hcyc he hl)) A B φ,
          e (PresentedGroup.mk ({u ^ l} : Set (FreeGroup α)) u) =
            c * HNNExtension.of (PresentedGroup.mk (kmsRootRel t u l hcyc he hl)
              (Work.OROneRel.EpsV2.rootW t u l hcyc he hl)) * c⁻¹ := by
  classical
  have hu1 : u ≠ 1 := ne_one_of_not_isProperPower hu
  have hcycr : IsCyclicallyReducedRelator (u ^ l) := isCyclicallyReducedRelator_pow hcyc l
  have hepsr : eps t (u ^ l) = 0 := by
    have h1 : sigma t (u ^ l) = 1 := by
      rw [map_pow, (eps_eq_zero_iff_sigma_eq_one t u).mp he, one_pow]
    exact (eps_eq_zero_iff_sigma_eq_one t (u ^ l)).mpr h1
  have hnormu : 0 < relatorNorm u := by
    refine Nat.pos_of_ne_zero fun h0 => hu1 ?_
    have h2 : FreeGroup.norm u = 0 := h0
    exact FreeGroup.norm_eq_zero.mp h2
  have hrne : u ^ l ≠ 1 := by
    intro h
    have h1 : relatorNorm (u ^ l) = 0 := by
      rw [h]
      simp [relatorNorm, FreeGroup.norm]
    rw [relatorNorm_pow_of_isCyclicallyReduced u hcyc l] at h1
    rcases Nat.mul_eq_zero.mp h1 with h2 | h2
    · omega
    · omega
  have htr : t ∈ relatorLetters (u ^ l) := by
    have hh : FreeGroup.IsCyclicallyReduced (FreeGroup.toWord u) := by
      simpa only [IsCyclicallyReducedRelator] using hcyc
    have hred : FreeGroup.IsReduced (List.flatten (List.replicate l (FreeGroup.toWord u))) :=
      (hh.flatten_replicate l).1
    have hword : FreeGroup.toWord (u ^ l)
        = List.flatten (List.replicate l (FreeGroup.toWord u)) := by
      rw [FreeGroup.toWord_pow, hred.reduce_eq]
    rw [relatorLetters, hword]
    obtain ⟨b, hb⟩ := ht
    exact ⟨b, List.mem_flatten.mpr
      ⟨FreeGroup.toWord u, List.mem_replicate.mpr ⟨by omega, rfl⟩, hb⟩⟩
  have hred : FreeGroup.IsReduced (mmWL t (u ^ l)) := mmWL_isReduced t (u ^ l) hcycr hepsr
  have hFw : FreiheitssatzAt (mmW t (u ^ l)) := freiheitssatz_at _
  have hc : IsCyclicallyReducedRelator (mmW t (u ^ l)) := mmW_isCyclicallyReduced hcycr hepsr
  have hA : mmW t (u ^ l) ∉ Subgroup.closure (FreeGroup.of '' mmTA t (u ^ l)) :=
    mmW_notMem_closure_TA hrne htr hepsr hred
  have hB : mmW t (u ^ l) ∉ Subgroup.closure (FreeGroup.of '' mmTB t (u ^ l)) :=
    mmW_notMem_closure_TB hrne htr hepsr hred
  have hrel : FreeGroup.lift (mmThetaFun (r := u ^ l) hFw hc hA hB) (u ^ l) = 1 :=
    mmThetaFun_relator (r := u ^ l) hepsr hFw hc hA hB
  let Θ : mmG (u ^ l) →* mmK t (u ^ l) hFw hc hA hB := mmTheta (r := u ^ l) hFw hc hA hB hrel
  let Ψ : mmK t (u ^ l) hFw hc hA hB →* mmG (u ^ l) := mmPsi (r := u ^ l) hepsr hFw hc hA hB
  have h1 : Ψ.comp Θ = MonoidHom.id _ := mmPsi_comp_mmTheta (r := u ^ l) hepsr hFw hc hA hB hrel
  have h2 : Θ.comp Ψ = MonoidHom.id _ := mmTheta_comp_mmPsi (r := u ^ l) hepsr hFw hc hA hB hrel
  let e : mmG (u ^ l) ≃* mmK t (u ^ l) hFw hc hA hB := MonoidHom.toMulEquiv Θ Ψ h1 h2
  have hcomp' : Θ.comp (PresentedGroup.mk ({u ^ l} : Set (FreeGroup α)))
      = FreeGroup.lift (mmThetaFun (r := u ^ l) hFw hc hA hB) := by
    refine FreeGroup.ext_hom _ _ fun a => ?_
    rw [MonoidHom.comp_apply, FreeGroup.lift_apply_of]
    exact mmTheta_of (r := u ^ l) hFw hc hA hB hrel a
  have htrk : e (PresentedGroup.mk ({u ^ l} : Set (FreeGroup α)) u)
      = HNNExtension.of ((PresentedGroup.mk ({mmW t (u ^ l)} : Set (FreeGroup (mmBeta t (u ^ l)))))
          (Work.OROneRel.EpsV2.rootW t u l hcyc he hl)) := by
    show Θ (PresentedGroup.mk ({u ^ l} : Set (FreeGroup α)) u) = _
    rw [← MonoidHom.comp_apply, hcomp']
    have hroot : (FreeGroup.lift (mmThetaFun (r := u ^ l) hFw hc hA hB)) u
        = (FreeGroup.lift (mmThetaFun (r := u ^ l) hFw hc hA hB))
            (FreeGroup.lift (fun p : mmBeta t (u ^ l) => Work.OROneRel.EpsV2.mmRhoFun t p.1)
              (Work.OROneRel.EpsV2.rootW t u l hcyc he hl)) := by
      congr 1
      exact (Work.OROneRel.EpsV2.lift_mmRho_rootW t u l hcyc he hl).symm
    rw [hroot]
    exact Work.OROneRel.EpsV2.mmTheta_lift_mmRho hFw hc hA hB
      (Work.OROneRel.EpsV2.rootW t u l hcyc he hl)
  have key : ∃ (A B : Subgroup (PresentedGroup (kmsRootRel t u l hcyc he hl)))
      (φ : A ≃* B)
      (e : PresentedGroup ({u ^ l} : Set (FreeGroup α)) ≃*
        HNNExtension (PresentedGroup (kmsRootRel t u l hcyc he hl)) A B φ),
      ∃ c : HNNExtension (PresentedGroup (kmsRootRel t u l hcyc he hl)) A B φ,
        e (PresentedGroup.mk ({u ^ l} : Set (FreeGroup α)) u) =
          c * HNNExtension.of (PresentedGroup.mk (kmsRootRel t u l hcyc he hl)
                (Work.OROneRel.EpsV2.rootW t u l hcyc he hl)) * c⁻¹ := by
    rw [show kmsRootRel t u l hcyc he hl
        = ({mmW t (u ^ l)} : Set (FreeGroup (mmBeta t (u ^ l)))) from by
      rw [kmsRootRel, Work.OROneRel.EpsV2.rootW_pow]]
    exact ⟨mmA t (u ^ l), mmB t (u ^ l), mmPhi (t := t) (r := u ^ l) hFw hc hA hB, e, 1, by
      rw [htrk, one_mul, inv_one, mul_one]⟩
  exact key

/-! ## The norm of the Magnus root is bounded by the non-`t` letter count -/

/-- The Magnus root `EpsV2.rootW t u l` is a word in the decorated letters, one per letter of `u`
different from `t`; hence its norm is at most `nonTLetters t u`. -/
theorem kmsRoot_rootW_le_nonTLetters {α : Type u} (t : α) (u : FreeGroup α) (l : ℕ)
    (hcyc : IsCyclicallyReducedRelator u) (he : eps t u = 0) (hl : 1 ≤ l) :
    relatorNorm (Work.OROneRel.EpsV2.rootW t u l hcyc he hl) ≤ nonTLetters t u := by
  classical
  have h1 : relatorNorm (Work.OROneRel.EpsV2.rootW t u l hcyc he hl)
      ≤ (mmList t u).length := by
    rw [Work.OROneRel.EpsV2.rootW_eq]
    refine le_trans FreeGroup.norm_mk_le ?_
    rw [List.length_map,
      show (mmWL t u).length = (mmList t u).length from by rw [mmWL, List.length_map]]
  have h2 : (mmList t u).length = nonTLetters t u := by
    rw [mmList, magRew_zero_eq_rewrite,
      show rewrite t u.toWord = rewriteAux t 0 u.toWord from rfl, rewriteAux_length,
      nonTLetters, List.countP_eq_length_filter]
  omega

/-- If the letter `t` does not occur in `w`, the non-`t` letter count is the length of `w`. -/
theorem nonTLetters_eq_relatorNorm_of_notMem {α : Type u} {t : α} {w : FreeGroup α}
    (h : t ∉ relatorLetters w) : nonTLetters t w = relatorNorm w := by
  classical
  have hno : ∀ p ∈ FreeGroup.toWord w, p.1 ≠ t := by
    rintro ⟨a, b⟩ hp hcon
    exact h ⟨b, hcon ▸ hp⟩
  have hfil : (FreeGroup.toWord w).filter (fun p : α × Bool => decide (p.1 ≠ t))
      = FreeGroup.toWord w := by
    apply List.filter_eq_self.mpr
    intro p hp
    simp [hno p hp]
  simp only [nonTLetters, relatorNorm, FreeGroup.norm, List.countP_eq_length_filter, hfil]

/-! ## Transport of `KMSRoot` along an isomorphism up to conjugacy -/

/-- `KMSRoot` is invariant under an isomorphism of the two root presentations that carries the root
to a *conjugate* of the other root.  This is the shape in which conjugate relators present
isomorphic groups (`presentedGroup_pow_conj_iso`). -/
theorem KMSRoot_of_mulEquiv_conj {α : Type u} {u w : FreeGroup α} {l : ℕ}
    (e : PresentedGroup ({u ^ l} : Set (FreeGroup α)) ≃*
      PresentedGroup ({w ^ l} : Set (FreeGroup α)))
    (c : PresentedGroup ({w ^ l} : Set (FreeGroup α)))
    (he : e (PresentedGroup.mk ({u ^ l} : Set (FreeGroup α)) u) =
      c * PresentedGroup.mk ({w ^ l} : Set (FreeGroup α)) w * c⁻¹)
    (hw : KMSRoot w l) : KMSRoot u l := by
  refine ⟨?_, ?_⟩
  · rw [← orderOf_mulEquiv e (PresentedGroup.mk ({u ^ l} : Set (FreeGroup α)) u), he,
      orderOf_conj, hw.1]
  · intro g hg
    have hge : IsOfFinOrder (e g) := (isOfFinOrder_mulEquiv_iff e g).mpr hg
    obtain ⟨k, d, hd⟩ := hw.2 (e g) hge
    refine ⟨k, e.symm d * (e.symm c)⁻¹, ?_⟩
    apply e.injective
    simp only [map_mul, map_inv, map_pow, MulEquiv.apply_symm_apply]
    rw [he, hd, pow_conj_eq]
    group

/-! ## The main statement -/

theorem kmsRoot_subst_image {α : Type u} (u : FreeGroup α) (l : ℕ) (hl : 1 ≤ l) {t x : α}
    (hxt : x ≠ t) (hcyc : Work.OROneRel.IsCyclicallyReducedRelator u)
    (hu : ¬ Work.OROneRel.IsProperPower u)
    (ht : t ∈ Work.OROneRel.relatorLetters u) (hx : x ∈ Work.OROneRel.relatorLetters u)
    (hpx : Work.OROneRel.eps x u ≠ 0)
    (IH : ∀ {β : Type u} (v : FreeGroup β), ¬ Work.OROneRel.IsProperPower v →
      Work.OROneRel.relatorNorm v < Work.OROneRel.relatorNorm u → Work.OROneRel.KMSRoot v l) :
    Work.OROneRel.KMSRoot
      (Work.OROneRel.subst t x (Work.OROneRel.eps x u) (Work.OROneRel.eps t u) u) l := by
  classical
  -- the substituted relator
  set u' : FreeGroup α := subst t x (eps x u) (eps t u) u with hu'def
  -- it is not a proper power
  have hpp : ¬ IsProperPower u' := by
    have h0 : ¬ IsProperPower (subst t x (Multiplicative.toAdd (sigma x u))
        (Multiplicative.toAdd (sigma t u)) u) :=
      wcp_not_isProperPower_subst u hxt hcyc hu (by rw [← eps_eq_toAdd_sigma]; exact hpx)
    have hsub : u' = subst t x (Multiplicative.toAdd (sigma x u))
        (Multiplicative.toAdd (sigma t u)) u := by
      simp only [hu'def, eps_eq_toAdd_sigma]
    rw [hsub]; exact h0
  -- cyclic reduction
  set w : FreeGroup α := cyclicReduction u' with hwdef
  have hconj : cyclicConjugator u' * w * (cyclicConjugator u')⁻¹ = u' := by
    rw [hwdef]; exact cyclicConjugator_mul_cyclicReduction_mul_inv u'
  have hcycw : IsCyclicallyReducedRelator w := by
    rw [hwdef]; exact isCyclicallyReducedRelator_cyclicReduction u'
  have hppw : ¬ IsProperPower w := by
    intro hw
    obtain ⟨z, k, hk, hzk⟩ := hw
    have hzu : u' = (cyclicConjugator u' * z * (cyclicConjugator u')⁻¹) ^ k := by
      conv_lhs => rw [← hconj]
      rw [hzk, ← pow_conj_eq]
    exact hpp ⟨_, k, hk, hzu⟩
  -- the exponent sum of `t` still vanishes
  have hew : eps t w = 0 := by
    have h1 : eps t w = eps t u' := by
      rw [hwdef, eps_eq_toAdd_sigma, sigma_cyclicReduction, ← eps_eq_toAdd_sigma]
    rw [h1, hu'def, eps_subst_t hxt]
    ring
  -- the norm bound
  have hnt : nonTLetters t w < relatorNorm u := by
    have h1 : nonTLetters t w ≤ nonTLetters t u' := by
      rw [hwdef]; exact nonTLetters_cyclicReduction_le u' t
    have h2 : nonTLetters t u' ≤ nonTLetters t u := by
      have hPsi : Psi u t x u = u' := by
        rw [hu'def, Psi_eq_subst u hxt]
        simp only [eps_eq_toAdd_sigma]
      rw [← hPsi]
      exact nonTLetters_Psi_le u t x hxt
    exact lt_of_le_of_lt (le_trans h1 h2) (nonTLetters_lt_norm u t ht)
  -- `KMSRoot w l`, the cyclically reduced conjugate
  have hkms_w : KMSRoot w l := by
    by_cases htw : t ∈ relatorLetters w
    · -- the exponent-sum-zero Magnus step at `w`
      obtain ⟨A, B, φ, e2, c2, hc2⟩ :=
        kmsRootMagnusStep_aux w l hl t hppw hcycw htw hew
      exact kmsRoot_of_hnn hc2 (IH (Work.OROneRel.EpsV2.rootW t w l hcycw hew hl)
        (Work.OROneRel.EpsV2.not_isProperPower_rootW t w l hppw hcycw hew hl)
        (lt_of_le_of_lt (kmsRoot_rootW_le_nonTLetters t w l hcycw hew hl) hnt))
    · -- then `w` itself has the smaller norm
      refine IH w hppw ?_
      rw [← nonTLetters_eq_relatorNorm_of_notMem htw]
      exact hnt
  -- transport back along `⟨α | u'^l⟩ ≃* ⟨α | w^l⟩`
  obtain ⟨e1, he1⟩ := presentedGroup_pow_conj_iso u' w (cyclicConjugator u') l hconj
  refine KMSRoot_of_mulEquiv_conj e1
    (PresentedGroup.mk ({w ^ l} : Set (FreeGroup α)) (cyclicConjugator u')) ?_ hkms_w
  rw [he1]
  have hmm := congrArg (PresentedGroup.mk ({w ^ l} : Set (FreeGroup α))) hconj
  simp only [map_mul, map_inv] at hmm
  exact hmm.symm

end Work.OROneRel
