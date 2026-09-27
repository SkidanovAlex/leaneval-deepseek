import Mathlib
import Submission.Work.Drive.N2Lead.mobiusPacketDefs
import Submission.Work.Drive.N2Lead.mobiusUpperDefs
import Submission.Work.Drive.N2Lead.mobiusGoodDrawing
import Submission.Work.Drive.N2Lead.twistToolkit
import Submission.Work.Drive.N2Lead.isCertifiedAt_of_ambientPath
import Submission.Work.Drive.N2Lead.isCertifiedAt_of_starRegions

/-!
# The upper certificate of the Möbius saddle window

The drawing `Work.Drive.N2Lead.mobiusWindowDrawing D η S` of a `MobiusPacket` is the model piece
`cE3 ∘ Ψ ∘ Z` on the strip `|Im (Z ·)²| < 39/20` and the transported park picture `A ∘ foot`
outside it.  The certificate at the upper level `f p + 3η/2` is proved as in the design
(`N2Lead/NOTES_LEAD_mobiusSaddle.md` §2.4): the star-shapedness of the *twisted* picture
`mobiusTwisted D η S ε εp Dp` (the slab twists `twistY a' (-1)`, `twistX ε (-1)` and the push
`pushY Dp εp 1`) is delegated (`Work.Drive.N2Lead.mobiusUpperStarRows`), and the certificate is
transferred back along the three ambient paths (`Work.Drive.N2Lead.isCertifiedAt_of_ambientPath`).
-/

namespace Work.Drive.N2Lead

open scoped Manifold ContDiff Topology
open Set Filter

noncomputable section

variable {M : Type*} [TopologicalSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin 2)) M]
    [IsManifold (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 2))) ((⊤ : ℕ∞) : WithTop ℕ∞) M]
    [T2Space M] [SecondCountableTopology M] [CompactSpace M]

/-! ## A level isotopy followed by a global diffeomorphism -/

/-- **A level isotopy followed by a global diffeomorphism of `ℝ³` is a level isotopy.** -/
lemma isLevelIsotopy_comp_global {f : M → ℝ} {u : ℝ} {g : M → EuclideanSpace ℝ (Fin 3)}
    (hg : Work.Drive.N2C.IsLevelIsotopy f u (fun _ : ℝ => g))
    {F : EuclideanSpace ℝ (Fin 3) → EuclideanSpace ℝ (Fin 3)}
    (hF : ContDiff ℝ tpTop F) (hinj : Function.Injective F)
    (himm : ∀ w : EuclideanSpace ℝ (Fin 3), Function.Injective (fderiv ℝ F w)) :
    Work.Drive.N2C.IsLevelIsotopy f u (fun _ : ℝ => fun y => F (g y)) := by
  have hF' : ContDiff ℝ tpTop (Function.uncurry (fun _ : ℝ => F)) := by
    have h : Function.uncurry (fun _ : ℝ => F) = fun p : ℝ × EuclideanSpace ℝ (Fin 3) => F p.2 := by
      funext p; rfl
    rw [h]
    exact hF.comp contDiff_snd
  have h := Work.Drive.N2C.isLevelIsotopy_ambient_contDiff (f := f) (b := u)
    (e := fun _ : ℝ => g) hg (F := fun _ : ℝ => F) hF'
    (fun _ => hinj) (fun _ w => himm w)
  simpa only [Function.uncurry] using h

/-! ## The upper level is regular -/

/-- **The level `f p + 3η/2` is regular**, from the value separation of the window datum and the
relations `(ρ j / 8)² * packetEtaB = 2η`, `(ρ j / 8)² * packetEta = 3η/2` of the packet. -/
lemma mobiusUpper_not_critical {f : M → ℝ} {p : M} (D : Work.Drive.N2.WindowDatum f p) {η : ℝ}
    (hη : 0 < η) (hsep : (D.ρ D.j / 8) ^ 2 * Work.Drive.N2.packetEtaB D η < 2 * D.ηd) :
    ∀ x : M, f x = f p + 3 * η / 2 → ¬ Work.Drive.Morse.IsCritical f x := by
  intro x hx hcrit
  obtain ⟨i, hi⟩ := D.hcover x hcrit
  have hfx : f x = f (D.x i) := by rw [hi]
  have hηd : 3 * η / 2 < 2 * D.ηd := by
    have h1 := Work.Drive.N2.packetEtaB_law (D := D) (η := η)
    have h2 : η < D.ηd := by nlinarith [hsep, h1, D.hρ D.j]
    linarith
  by_cases hij : i = D.j
  · subst hij
    rw [D.hxj] at hfx
    linarith
  · have h2 := D.hsep i D.j hij
    rw [D.hxj] at h2
    have h3 : |f (D.x i) - f p| = 3 * η / 2 := by
      rw [← hfx, hx, add_sub_cancel_left, abs_of_pos (by linarith)]
    linarith [h3]

end

end Work.Drive.N2Lead
