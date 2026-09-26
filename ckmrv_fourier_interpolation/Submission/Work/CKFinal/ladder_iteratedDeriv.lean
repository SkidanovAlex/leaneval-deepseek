import Mathlib
import Submission.Work.Asymptotics.TSasm.cuspOneLowHalfTile_TS
import Submission.Work.Asymptotics.PaperLayerLadderTS

namespace Work.CKFinal

/-- **The `T`-ladder of the CKMRV layer, differentiated in `r`.**

The pointwise ladder `layer(1 + u) = 2 layer(u) - layer(u - 1)`
(`Work.Asymptotics.lh_layer_vadd_ladder`) holds for every `r`; the layer differs from the smooth
`paperLayer` only at `r = 0` and, for positive order, this single puncture is invisible to the
iterated derivative in `r` (`Work.Asymptotics.ts_punctured_iteratedDeriv`).  On `paperLayer` the
ladder is a linear identity, so it survives `l`-fold differentiation in `r`. -/
theorem ladder_iteratedDeriv (ℓ : Work.Kernels.LogLambdaData) (d : ℕ) (hd : d = 8 ∨ d = 24)
    (u : UpperHalfPlane) (hu : u ∈ Work.Asymptotics.DomainD) (hre : 0 < u.re)
    (hm : ((-1 : ℝ) +ᵥ u) ∈ Work.Asymptotics.DomainD) {l : ℕ} (hl : 1 ≤ l) (r : ℝ) :
    iteratedDeriv l (fun s : ℝ =>
        Work.Asymptotics.layer (Work.Asymptotics.Gcusp ℓ d) ℓ d ((-1 : ℝ) +ᵥ u) s) r
      = 2 * iteratedDeriv l (fun s : ℝ =>
            Work.Asymptotics.layer (Work.Asymptotics.Gcusp ℓ d) ℓ d u s) r
        - iteratedDeriv l (fun s : ℝ =>
            Work.Asymptotics.layer (Work.Asymptotics.Gcusp ℓ d) ℓ d ((1 : ℝ) +ᵥ u) s) r := by
  have hcum : ContDiff ℝ ⊤ (fun s : ℝ =>
      Work.Asymptotics.paperLayer (Work.Asymptotics.Gcusp ℓ d) ℓ d ((-1 : ℝ) +ᵥ u) s) :=
    Work.Asymptotics.ts_paperLayer_contDiff_at ℓ d hd ((-1 : ℝ) +ᵥ u) hm
  have hcu : ContDiff ℝ ⊤ (fun s : ℝ =>
      Work.Asymptotics.paperLayer (Work.Asymptotics.Gcusp ℓ d) ℓ d u s) :=
    Work.Asymptotics.ts_paperLayer_contDiff_at ℓ d hd u hu
  have hcp : ContDiff ℝ ⊤ (fun s : ℝ =>
      Work.Asymptotics.paperLayer (Work.Asymptotics.Gcusp ℓ d) ℓ d ((1 : ℝ) +ᵥ u) s) :=
    Work.Asymptotics.ts_paperLayer_contDiff_vadd_one ℓ d hd u hu hre
  have hp_m := Work.Asymptotics.ts_punctured_iteratedDeriv (G := Work.Asymptotics.Gcusp ℓ d)
    ℓ d ((-1 : ℝ) +ᵥ u) hl hcum
  have hp_u := Work.Asymptotics.ts_punctured_iteratedDeriv (G := Work.Asymptotics.Gcusp ℓ d)
    ℓ d u hl hcu
  have hp_p := Work.Asymptotics.ts_punctured_iteratedDeriv (G := Work.Asymptotics.Gcusp ℓ d)
    ℓ d ((1 : ℝ) +ᵥ u) hl hcp
  have hladeq : (fun s : ℝ =>
      Work.Asymptotics.paperLayer (Work.Asymptotics.Gcusp ℓ d) ℓ d ((1 : ℝ) +ᵥ u) s)
      = fun s : ℝ =>
        2 * Work.Asymptotics.paperLayer (Work.Asymptotics.Gcusp ℓ d) ℓ d u s
          - Work.Asymptotics.paperLayer (Work.Asymptotics.Gcusp ℓ d) ℓ d ((-1 : ℝ) +ᵥ u) s := by
    funext s
    exact Work.Asymptotics.lh_paperLayer_vadd_ladder ℓ d hd u hu hre s
  have h2 : iteratedDeriv l (fun s : ℝ =>
        Work.Asymptotics.paperLayer (Work.Asymptotics.Gcusp ℓ d) ℓ d ((1 : ℝ) +ᵥ u) s) r
      = 2 * iteratedDeriv l (fun s : ℝ =>
            Work.Asymptotics.paperLayer (Work.Asymptotics.Gcusp ℓ d) ℓ d u s) r
        - iteratedDeriv l (fun s : ℝ =>
            Work.Asymptotics.paperLayer (Work.Asymptotics.Gcusp ℓ d) ℓ d ((-1 : ℝ) +ᵥ u) s) r := by
    rw [hladeq]
    rw [show (fun s : ℝ =>
          2 * Work.Asymptotics.paperLayer (Work.Asymptotics.Gcusp ℓ d) ℓ d u s
            - Work.Asymptotics.paperLayer (Work.Asymptotics.Gcusp ℓ d) ℓ d ((-1 : ℝ) +ᵥ u) s)
        = (fun s : ℝ => 2 * Work.Asymptotics.paperLayer (Work.Asymptotics.Gcusp ℓ d) ℓ d u s)
          - (fun s : ℝ =>
              Work.Asymptotics.paperLayer (Work.Asymptotics.Gcusp ℓ d) ℓ d ((-1 : ℝ) +ᵥ u) s)
        from rfl]
    rw [iteratedDeriv_sub
        ((contDiff_const.mul hcu).contDiffAt.of_le le_top) (hcum.contDiffAt.of_le le_top),
      iteratedDeriv_const_mul_field]
  rw [hp_m, hp_u, hp_p, h2]
  ring

end Work.CKFinal
