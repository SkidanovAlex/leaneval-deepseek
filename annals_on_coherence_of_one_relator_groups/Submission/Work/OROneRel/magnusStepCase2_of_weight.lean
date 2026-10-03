import Mathlib
import Submission.Work.OROneRel.Basic
import Submission.Work.OROneRel.MagnusRewrite
import Submission.Work.OROneRel.MagnusGenDefs
import Submission.Work.OROneRel.rhoC_injective_range
import Submission.Work.OROneRel.GaugeDefs
import Submission.Work.OROneRel.Interface
import Submission.Work.OROneRel.range_presentedGroupMap
import Submission.Work.OROneRel.wgtMMDefs
import Submission.Work.OROneRel.ne_one_of_not_isProperPower
import Submission.Work.OROneRel.freiheitssatz_at
import Submission.Work.OROneRel.le_relatorNorm_pow
import Submission.Work.OROneRel.isCyclicallyReducedRelator_pow
import Submission.Work.OROneRel.exists_hnnStepCore
import Submission.Work.OROneRel.wgtCompositions
import Submission.Work.OROneRel.wgtThetaFacts
import Submission.Work.OROneRel.wgtPhiChain
import Submission.Work.OROneRel.wgtPower
import Submission.Work.OROneRel.wgtToolboxGen

/-!
# The weighted Magnus step (`magnusStepCase2_of_weight`)

For a cyclically reduced relator `u` which is not a proper power, of norm `≥ 2`, all of whose letters
have non-zero exponent sum, and for which there exist a letter `t` of `u` and an integer weight
`c : α → ℤ` with `c t = 1` and `cohom c u = 1`, the one-relator group `⟨α | u ^ l⟩` is an HNN
extension of a shorter one-relator group `⟨β | v ^ l⟩` with the same exponent `l`, a root `v` which is
again not a proper power, and with the class of `u` conjugate to the class of the root `v`.

The construction is the *weighted* Magnus--Moldavanskii step: the symbol `(x,i)` stands for the
conjugate `t ^ i * x * t ^ (-i - c x)` (`wrho`), the `t`-symbols have trivial loop class and are
deleted (`wvListAux`), and the remaining decorated word `v = wv c t u` satisfies `wrho v = u` and has
norm strictly less than `relatorNorm u`.  The base of the step is `⟨β | v ^ l⟩` with
`β = wBeta c t u` the interval closure of the occurring symbols; the isomorphism is the explicit
Magnus--Moldavanskii isomorphism (`wTheta`/`wPsi`) transported along the power `u ↦ u ^ l`.

The definitions of the weighted rewriting live in `Submission.Work.OROneRel.wgtMMDefs`.
-/

namespace Work.OROneRel

universe u

variable {α : Type u}


/-- `FreeGroup.map` is compatible with composition. -/
theorem wgt_map_map {β γ δ : Type*} (g : γ → δ) (f : β → γ) (x : FreeGroup β) :
    FreeGroup.map g (FreeGroup.map f x) = FreeGroup.map (fun b => g (f b)) x := by
  induction x using FreeGroup.induction_on with
  | one => simp
  | of b => simp only [FreeGroup.map.of]
  | inv_of b ih => rw [map_inv, map_inv, ih, map_inv]
  | mul b c ihb ihc => rw [map_mul, map_mul, ihb, ihc, map_mul]

theorem wgt_map_id {β : Type*} (x : FreeGroup β) :
    FreeGroup.map (fun b : β => b) x = x := by
  induction x using FreeGroup.induction_on with
  | one => simp
  | of b => simp only [FreeGroup.map.of]
  | inv_of b ih => rw [map_inv, ih]
  | mul b c ihb ihc => rw [map_mul, ihb, ihc]

/-- The base relator `wW c t u` is not a proper power. -/
theorem not_isProperPower_wW [DecidableEq α] (c : α → ℤ) (t : α) (u : FreeGroup α)
    (hct : c t = 1) (hcu : cohom c u = 1) (hpp : ¬ IsProperPower u) :
    ¬ IsProperPower (wW c t u) := by
  rintro ⟨z, k, hk, hzk⟩
  refine hpp ⟨wrho t c (FreeGroup.map (fun p : wBeta c t u => (p.1 : WgtBeta t)) z), k, hk, ?_⟩
  have h2 : wrho t c (FreeGroup.map (fun p : wBeta c t u => (p.1 : WgtBeta t)) (wW c t u)) = u :=
    wrho_wW c t u hct hcu
  have h3 : wrho t c (FreeGroup.map (fun p : wBeta c t u => (p.1 : WgtBeta t)) (z ^ k)) = u := by
    rw [← hzk]; exact h2
  have h5 : wrho t c (FreeGroup.map (fun p : wBeta c t u => (p.1 : WgtBeta t)) z) ^ k
      = wrho t c (FreeGroup.map (fun p : wBeta c t u => (p.1 : WgtBeta t)) (z ^ k)) := by
    rw [show wrho t c (FreeGroup.map (fun p : wBeta c t u => (p.1 : WgtBeta t)) z) ^ k
        = wrho t c ((FreeGroup.map (fun p : wBeta c t u => (p.1 : WgtBeta t)) z) ^ k) from
      (map_pow (wrho t c) (FreeGroup.map (fun p : wBeta c t u => (p.1 : WgtBeta t)) z) k).symm]
    congr 1
    exact (map_pow (FreeGroup.map (fun p : wBeta c t u => (p.1 : WgtBeta t))) z k).symm
  have h4 : wrho t c (FreeGroup.map (fun p : wBeta c t u => (p.1 : WgtBeta t)) z) ^ k = u := by
    rw [h5]; exact h3
  exact h4.symm

/-- `¬ IsProperPower` is preserved by an injective relabelling of the generators. -/
theorem not_isProperPower_map_of {β γ : Type*} (f : β → γ) (g : γ → β)
    (hgf : ∀ b, g (f b) = b) {w : FreeGroup β} (hw : ¬ IsProperPower w) :
    ¬ IsProperPower (FreeGroup.map f w) := by
  rintro ⟨z, k, hk, hzk⟩
  refine hw ⟨FreeGroup.map g z, k, hk, ?_⟩
  have h : FreeGroup.map g (FreeGroup.map f w) = w := by
    rw [wgt_map_map, show (fun b => g (f b)) = (fun b => b) from funext hgf, wgt_map_id]
  have h5 : FreeGroup.map g z ^ k = FreeGroup.map g (z ^ k) := (map_pow (FreeGroup.map g) z k).symm
  have h2 : FreeGroup.map g z ^ k = w := by
    rw [h5, ← hzk]; exact h
  exact h2.symm

/-- An injective relabelling of the generators preserves the relator norm. -/
theorem relatorNorm_map_of_injective_wgt {β γ : Type*} (f : β → γ) (hf : Function.Injective f)
    (X : FreeGroup β) : relatorNorm (FreeGroup.map f X) = relatorNorm X := by
  classical
  rw [relatorNorm, relatorNorm, FreeGroup.norm, FreeGroup.norm,
    toWord_map_of_injective_classical f hf X, List.length_map]

theorem magnusStepCase2_of_weight {α : Type u} (u : FreeGroup α) (l : ℕ) (hl : 1 ≤ l)
    (hu : ¬ Work.OROneRel.IsProperPower u)
    (hcyc : Work.OROneRel.IsCyclicallyReducedRelator u)
    (hn : 2 ≤ Work.OROneRel.relatorNorm u)
    (hbad : ∀ x : α, x ∈ Work.OROneRel.relatorLetters u → Work.OROneRel.eps x u ≠ 0)
    (hw : ∃ (t : α) (c : α → ℤ), t ∈ Work.OROneRel.relatorLetters u ∧ c t = 1 ∧
      Work.OROneRel.cohom c u = 1) :
    ∃ (β : Type u) (v : FreeGroup β), ¬ Work.OROneRel.IsProperPower v ∧
      Work.OROneRel.relatorNorm v < Work.OROneRel.relatorNorm u ∧
      ∃ (A B : Subgroup (PresentedGroup ({v ^ l} : Set (FreeGroup β)))) (φ : A ≃* B)
        (e : PresentedGroup ({u ^ l} : Set (FreeGroup α)) ≃*
          HNNExtension (PresentedGroup ({v ^ l} : Set (FreeGroup β))) A B φ),
        ∃ c : HNNExtension (PresentedGroup ({v ^ l} : Set (FreeGroup β))) A B φ,
          e (PresentedGroup.mk ({u ^ l} : Set (FreeGroup α)) u) =
            c * HNNExtension.of (PresentedGroup.mk ({v ^ l} : Set (FreeGroup β)) v) * c⁻¹ := by
  classical
  obtain ⟨t, c, ht, hct, hcu⟩ := hw
  have hu1 : u ≠ 1 := ne_one_of_not_isProperPower hu
  have hcyc' : IsCyclicallyReducedRelator (u ^ l) := isCyclicallyReducedRelator_pow hcyc l
  have h1' : u ^ l ≠ 1 := by
    intro h
    have hle := le_relatorNorm_pow u l hu1
    rw [h] at hle
    simp [relatorNorm, FreeGroup.norm] at hle
    omega
  have htw : (u ^ l).toWord = (List.replicate l u.toWord).flatten := by
    have hcr : FreeGroup.IsCyclicallyReduced u.toWord := by
      simpa only [IsCyclicallyReducedRelator] using hcyc
    rw [FreeGroup.toWord_pow, (hcr.flatten_replicate l).1.reduce_eq]
  have ht' : t ∈ relatorLetters (u ^ l) := by
    obtain ⟨b, hb⟩ := ht
    exact ⟨b, by rw [htw]; exact List.mem_flatten.mpr ⟨u.toWord, List.mem_replicate.mpr ⟨by omega, rfl⟩, hb⟩⟩
  have hcu' : cohom c (u ^ l) = 1 := by rw [map_pow, hcu, one_pow]
  obtain ⟨hred', hcycW', hne', hTA', hTB', _⟩ := wgtToolboxGen c t (u ^ l) hcyc' h1' ht' hct hcu'
  obtain ⟨_, _, _, _, _, hnormW⟩ := wgtToolboxGen c t u hcyc hu1 ht hct hcu
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
  refine ⟨wBeta c t (u ^ l), v, hnpv, hvnorm ▸ hnormW, ?_⟩
  rw [hset]
  exact ⟨wA c t (u ^ l), wB c t (u ^ l), wPhi hFw hcw' hTA' hTB', e1, 1, by
    rw [htrack, one_mul, inv_one, mul_one]⟩

