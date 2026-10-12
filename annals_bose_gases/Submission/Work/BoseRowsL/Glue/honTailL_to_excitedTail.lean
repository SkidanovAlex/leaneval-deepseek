import ChallengeDeps
import Mathlib.Data.ZMod.ValMinAbs
import Submission.Work.BoseRowsL.Defs
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Work.BoseRowsL.Glue.honTailL_to_excitedTail`

The interface field `Work.BoseRowsL.HonestInterfaceL.tailL` bounds the **lattice** tail
`ℓ⁻³ Σ_{n ∈ S} (ĝ(k_n)² + Ŵ₁(k_n)²)/‖k_n‖²` over a finite set `S ⊂ ℤ³` of lattice points which
all lie beyond `uvRad ℓ N`.  Consumers of the interface work with the sum over the **box modes**
`k ∈ Lab N`, filtered by `uvRad (ellH v μ) (HM μ).N < ‖kmom k‖`.

This lemma is the elementary reindexing bridge between the two: the box momenta are
`kmom k = ℓ⁻¹ • vec (labVec N k)` (definitionally), `labVec N : Lab N → ℤ³` is injective, and the
filter hypothesis transports along the injection.  No analysis is involved.
-/

noncomputable section

open scoped BigOperators

namespace Work.BoseRowsL.Glue

/-- `Work.BoseBoxFock.labVec N` is injective (`ZMod.valMinAbs` is a section of `ℤ → ZMod (2N+1)`). -/
private lemma labVec_injective_local (N : ℕ) :
    Function.Injective (Work.BoseBoxFock.labVec N) := by
  intro a b hab
  funext i
  exact ZMod.valMinAbs_inj.mp (congrFun hab i)

theorem honTailL_to_excitedTail {v : EuclideanSpace ℝ (Fin 3) → ℝ} {h : Work.UBB.ScatSol v}
    {fc fu : Work.BoseBoxFix.LowCut} {R : ℝ} {hthr : Work.BoseGateFS.GateThresholds v h fc fu R}
    (H : Work.BoseRowsL.HonestInterfaceL R hthr) :
    ∀ (HM : ∀ μ : ℝ, Work.BoseBoxFock.HonestModes v μ),
      (∀ μ, H.Ng' μ ≤ (HM μ).N) →
      ∀ μ : ℝ, 0 < μ → μ * _root_.BoseGases.a v ^ 3 ≤ hthr.εg →
      Work.BoseBoxFock.ellH v μ ^ (-(3 : ℝ)) *
        ∑ k ∈ (Work.BoseB7.excited (Work.BoseBoxFock.Lab (HM μ).N)).filter
            (fun k => Work.BoseBoxFock.uvRad (Work.BoseBoxFock.ellH v μ) (HM μ).N
              < ‖(Work.BoseRowsFS.honF v h fc fu HM μ).kmom k‖),
          (Work.BoseFixR.chat (Submission.BoseGases.g0 v h)
              ((Work.BoseRowsFS.honF v h fc fu HM μ).kmom k) ^ 2
            + Work.BoseFixR.chat (Work.BoseFixR.W1fun v h (Work.BoseBoxFock.ellH v μ))
                ((Work.BoseRowsFS.honF v h fc fu HM μ).kmom k) ^ 2)
            / ‖(Work.BoseRowsFS.honF v h fc fu HM μ).kmom k‖ ^ 2
        ≤ H.Cw ^ 2 * _root_.BoseGases.a v * (R / Work.BoseBoxFock.ellH v μ) ^ 4 := by
  intro HM hNg μ hμ hreg
  -- the box modes beyond `uvRad`, and their image in the lattice `ℤ³`
  set T : Finset (Work.BoseBoxFock.Lab (HM μ).N) :=
    (Work.BoseB7.excited (Work.BoseBoxFock.Lab (HM μ).N)).filter
      (fun k => Work.BoseBoxFock.uvRad (Work.BoseBoxFock.ellH v μ) (HM μ).N
        < ‖(Work.BoseRowsFS.honF v h fc fu HM μ).kmom k‖) with hT
  set S : Finset (Fin 3 → ℤ) := T.image (Work.BoseBoxFock.labVec (HM μ).N) with hS
  -- the box momentum is the lattice momentum, definitionally
  have hkmom : ∀ k : Work.BoseBoxFock.Lab (HM μ).N,
      (Work.BoseRowsFS.honF v h fc fu HM μ).kmom k
        = (Work.BoseBoxFock.ellH v μ)⁻¹
            • Work.BoseB4.vec (Work.BoseBoxFock.labVec (HM μ).N k) :=
    fun k => rfl
  -- every lattice point of `S` lies beyond `uvRad`
  have hSmem : ∀ n ∈ S, Work.BoseBoxFock.uvRad (Work.BoseBoxFock.ellH v μ) (HM μ).N
      < ‖(Work.BoseBoxFock.ellH v μ)⁻¹ • Work.BoseB4.vec n‖ := by
    intro n hn
    rw [hS, Finset.mem_image] at hn
    obtain ⟨k, hk, rfl⟩ := hn
    rw [← hkmom k]
    exact (Finset.mem_filter.mp hk).2
  -- reindex the label sum along the injection `labVec N`
  have hsum : (∑ k ∈ T,
        (Work.BoseFixR.chat (Submission.BoseGases.g0 v h)
            ((Work.BoseRowsFS.honF v h fc fu HM μ).kmom k) ^ 2
          + Work.BoseFixR.chat (Work.BoseFixR.W1fun v h (Work.BoseBoxFock.ellH v μ))
              ((Work.BoseRowsFS.honF v h fc fu HM μ).kmom k) ^ 2)
          / ‖(Work.BoseRowsFS.honF v h fc fu HM μ).kmom k‖ ^ 2)
      = ∑ n ∈ S,
        (Work.BoseFixR.chat (Submission.BoseGases.g0 v h)
            ((Work.BoseBoxFock.ellH v μ)⁻¹ • Work.BoseB4.vec n) ^ 2
          + Work.BoseFixR.chat (Work.BoseFixR.W1fun v h (Work.BoseBoxFock.ellH v μ))
              ((Work.BoseBoxFock.ellH v μ)⁻¹ • Work.BoseB4.vec n) ^ 2)
          / ‖(Work.BoseBoxFock.ellH v μ)⁻¹ • Work.BoseB4.vec n‖ ^ 2 := by
    rw [hS, Finset.sum_image (s := T) (g := Work.BoseBoxFock.labVec (HM μ).N)
      (f := fun n => (Work.BoseFixR.chat (Submission.BoseGases.g0 v h)
            ((Work.BoseBoxFock.ellH v μ)⁻¹ • Work.BoseB4.vec n) ^ 2
          + Work.BoseFixR.chat (Work.BoseFixR.W1fun v h (Work.BoseBoxFock.ellH v μ))
              ((Work.BoseBoxFock.ellH v μ)⁻¹ • Work.BoseB4.vec n) ^ 2)
          / ‖(Work.BoseBoxFock.ellH v μ)⁻¹ • Work.BoseB4.vec n‖ ^ 2)
      (fun a _ b _ hab => labVec_injective_local _ hab)]
    refine Finset.sum_congr rfl (fun k _ => ?_)
    rw [hkmom k]
  rw [hsum]
  exact H.tailL μ hμ hreg (HM μ).N (hNg μ) S hSmem

end Work.BoseRowsL.Glue
