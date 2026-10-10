import Mathlib
import Submission.Work.MotK.TwRuling.KleinKerMain
import Submission.Work.MotAS.QleAevalHomogeneous
import Submission.Work.MotK.TwRuling.hom_le_kleinKer_sup_std_v2

set_option linter.unusedVariables false -- v435-speed

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# `Work.MotAS.kleinKer_mem_v2` — the split Klein kernel statement, with the division lemma wired in

`Work.MotK.TwRuling.kleinKer_mem_of_homogeneous_aeval_eq_zero`
(`Submission/Work/MotK/TwRuling/KleinKerMain.lean`) is proved modulo two `sorry`s that are
placeholders for

* `Work.MotK.TwRuling.Q_le_aeval_homogeneousSubmodule` (proved, in its own module), and
* `Work.MotK.TwRuling.hom_le_kleinKer_sup_std` (open; the proof is being produced as
  `Work.MotK.TwRuling.hom_le_kleinKer_sup_std_v2`).

This file reproves the statement with the division lemma `hom_le_kleinKer_sup_std_v2` imported and
used, so that the *AS* branch (and anyone else) can use it as soon as the division lemma lands —
without editing the sibling `MotK` file.  The argument is transcribed verbatim from
`KleinKerMain.lean`; the two missing memberships are `Q_le_aeval_homogeneousSubmodule` and
`hom_le_kleinKer_sup_std_v2`.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 800000

open WeierstrassCurve WeierstrassCurve.Affine

namespace Work.MotAS

open MvPolynomial

/-- **The kernel of the Klein evaluation is the Pfaffian ideal** (split/Galois model), with the
normal-form lemma `hom_le_kleinKer_sup_std_v2` in place of the corresponding `sorry` of
`Work.MotK.TwRuling.kleinKer_mem_of_homogeneous_aeval_eq_zero`. -/
theorem kleinKer_mem_v2 (K : Type) [Field K] (D : Work.MotV.KleinData K) (hD : D.Good)
    (L : Type) [Field L] [Algebra K L] (n : ℕ) (F : MvPolynomial (Fin 5) L)
    (hF : F ∈ MvPolynomial.homogeneousSubmodule (Fin 5) L n)
    (hF0 : MvPolynomial.aeval (Work.MotV.kleinCoord D L) F = 0) :
    F ∈ Work.MotK.TwRuling.kleinKerIdeal L (algebraMap K L D.a) (algebraMap K L D.b) := by
  have hab : algebraMap K L D.a * algebraMap K L D.b ≠ 0 := by
    rw [← map_mul]
    exact (map_ne_zero_iff _ (algebraMap K L).injective).mpr hD.ab_ne
  set Φ : MvPolynomial (Fin 5) L →ₐ[L] Affine.FunctionField (D.E.baseChange L) :=
    MvPolynomial.aeval (Work.MotV.kleinCoord D L) with hΦdef
  set Il := Work.MotK.TwRuling.kleinKerSub L (algebraMap K L D.a) (algebraMap K L D.b)
    with hIdef
  set S : Submodule L (MvPolynomial (Fin 5) L) :=
    Submodule.span L (Set.range (Work.MotK.TwRuling.stdMono L n)) with hSdef
  -- §4.1 `Φ` kills `Il`
  have hmapI : Submodule.map Φ.toLinearMap Il = ⊥ := by
    rw [eq_bot_iff, Submodule.map_le_iff_le_comap]
    intro x hx
    rw [Submodule.mem_comap, Submodule.mem_bot]
    rw [hIdef] at hx
    exact Work.MotK.TwRuling.aeval_mem_kleinKerSub K D hD L x hx
  -- §4.2 `Q n ≤ Φ '' S`
  have hQle : Work.MotK.TwRuling.Five.Q (D.E.baseChange L) n ≤
      Submodule.map Φ.toLinearMap (MvPolynomial.homogeneousSubmodule (Fin 5) L n) := by
    rw [hΦdef]
    exact Q_le_aeval_homogeneous_v2 K D hD L n
  have hred : MvPolynomial.homogeneousSubmodule (Fin 5) L n ≤ Il ⊔ S := by
    rw [hIdef, hSdef]
    exact Work.MotK.TwRuling.hom_le_kleinKer_sup_std_v2 L (algebraMap K L D.a)
      (algebraMap K L D.b) hab n
  have hQleS : Work.MotK.TwRuling.Five.Q (D.E.baseChange L) n ≤
      Submodule.map Φ.toLinearMap S := by
    refine le_trans hQle ?_
    calc Submodule.map Φ.toLinearMap (MvPolynomial.homogeneousSubmodule (Fin 5) L n)
        ≤ Submodule.map Φ.toLinearMap (Il ⊔ S) := Submodule.map_mono hred
      _ = Submodule.map Φ.toLinearMap Il ⊔ Submodule.map Φ.toLinearMap S :=
          Submodule.map_sup Il S Φ.toLinearMap
      _ = Submodule.map Φ.toLinearMap S := by simp [hmapI]
  -- §4.3 `Φ` is injective on `S`
  haveI hfinS : Module.Finite L ↥S := Module.Finite.span_of_finite L (Set.finite_range _)
  have hker : (Φ.toLinearMap.domRestrict S).ker = ⊥ := by
    have hrn := LinearMap.finrank_range_add_finrank_ker (Φ.toLinearMap.domRestrict S)
    rw [LinearMap.range_domRestrict] at hrn
    have hle1 : Module.finrank L ↥S ≤
        Module.finrank L ↥(Submodule.map Φ.toLinearMap S) :=
      le_trans (Work.MotK.TwRuling.finrank_stdSpan_le K D hD L n)
        (Submodule.finrank_mono hQleS)
    have hle2 : Module.finrank L ↥(Submodule.map Φ.toLinearMap S) ≤ Module.finrank L ↥S :=
      Submodule.finrank_map_le Φ.toLinearMap S
    have hfin : Module.finrank L ↥(Submodule.map Φ.toLinearMap S) = Module.finrank L ↥S :=
      le_antisymm hle2 hle1
    rw [hfin] at hrn
    have h0 : Module.finrank L ↥(Φ.toLinearMap.domRestrict S).ker = 0 := by omega
    exact Submodule.finrank_eq_zero.mp h0
  have hinj : Function.Injective (Φ.toLinearMap.domRestrict S) :=
    LinearMap.ker_eq_bot.mp hker
  -- §4.4 conclude
  have hFsup : F ∈ S ⊔ Il := by
    rw [sup_comm]
    exact hred hF
  obtain ⟨G, hG, H, hH, hGH⟩ := Submodule.mem_sup.mp hFsup
  have hΦH : Φ H = 0 := by
    rw [hIdef] at hH
    exact Work.MotK.TwRuling.aeval_mem_kleinKerSub K D hD L H hH
  have hΦG : Φ G = 0 := by
    have h1 : Φ F = Φ G + Φ H := by rw [← hGH, map_add]
    rw [hF0, hΦH, add_zero] at h1
    exact h1.symm
  have hG0 : G = 0 := by
    have h1 : (Φ.toLinearMap.domRestrict S) ⟨G, hG⟩ = 0 := hΦG
    have h2 : (Φ.toLinearMap.domRestrict S) (0 : ↥S) = 0 := map_zero _
    have heq : (⟨G, hG⟩ : ↥S) = 0 := hinj (by rw [h1, h2])
    exact Subtype.ext_iff.mp heq
  have hFH : F = H := by rw [← hGH, hG0, zero_add]
  rw [hFH]
  rw [hIdef] at hH
  exact hH

end Work.MotAS
