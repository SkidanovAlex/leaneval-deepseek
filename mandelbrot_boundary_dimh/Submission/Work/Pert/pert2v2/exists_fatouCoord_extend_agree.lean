import Mathlib
import Submission.Work.Pert.MaxDom
import Submission.Work.Pert.Gates
import Submission.Work.Pert.pert2v2.dphiP_coordP_congr_of_eqOn
import Submission.Work.Interfaces.Fatou

/-!
# PERT · `Work.Pert.pert2v2.exists_fatouCoord_extend_agree`

**The single-coordinate construction** (`NOTES_pert2v2_session20.md` §4.3, and the `Φm`/`Φ⋆`
mismatch of `NOTES_pert2v2_DESIGN.md` §6): given a Fatou coordinate `Φ` of `F` on the smaller
`𝒬`-region `Qreg c₁ c₂`, there is a Fatou coordinate `ΨE` of `F` on the *larger* region
`Qreg b₁ b₂ ⊇ Qreg c₁ c₂` which agrees with `Φ` on the smaller one and — the point of the lemma —
induces the *same* maximal-domain coordinate `φ_f = coordP f Df τ • (Qreg c₁ c₂)` on the smaller
region.

## Proof

* `FatouExists` (A.2.1(ii) existence) applied to `(b₁, b₂)` produces a Fatou coordinate `Ψ` of `F`
  on the whole `Qreg b₁ b₂`; restricting it along `hsub` gives one on `Qreg c₁ c₂`
  (`IsFatouCoordOn` is a conjunction of three statements, each of which restricts).
* `FatouUnique` (A.2.1(ii), uniqueness up to an additive constant) on the *shared* region
  `Qreg c₁ c₂` gives `c` with `Φ z = Ψ z + c` there.  Then `ΨE := Ψ + c` is a Fatou coordinate of
  `F` on `Qreg b₁ b₂` — adding a constant preserves differentiability, injectivity and the Abel
  equation `Φ (F z) = Φ z + 1` (`Work.Pert.MandelDim.IsFatouCoordOn.add_const`) — and
  `ΨE = Φ` pointwise on `Qreg c₁ c₂`.
* `coordP`/`DphiP` see the coordinate `Φ` **only** through its values on the gate `Q`: they are
  built from `Φ '' Q` and the chosen preimage `invOn Φ Q ·` (`MaxDom`, `AsmDefs`).  So if
  `InjOn Φ Q` and `ΨE = Φ` on `Q`, the domain and the value are literally unchanged — this is
  `Work.Pert.pert2v2.dphiP_coordP_congr_of_eqOn`, proved alongside this file (the chain
  `invOn → seedP → GoodP → mIdxP → coordP`).
-/

namespace Work.Pert.pert2v2

open Set

noncomputable section

theorem exists_fatouCoord_extend_agree {F Φ : ℂ → ℂ} {b₁ b₂ c₁ c₂ : Option ℂ}
    (hEx : MandelDim.FatouExists) (hUn : MandelDim.FatouUnique)
    (f : ℂ → ℂ) (Df : Set ℂ) (τ : ℂ → ℂ)
    (hadm : MandelDim.QAdm b₁ b₂)
    (hNT : MandelDim.NearTranslationOn F (MandelDim.Qreg b₁ b₂))
    (hadm' : MandelDim.QAdm c₁ c₂)
    (hNT' : MandelDim.NearTranslationOn F (MandelDim.Qreg c₁ c₂))
    (hsub : MandelDim.Qreg c₁ c₂ ⊆ MandelDim.Qreg b₁ b₂)
    (hΦ : MandelDim.IsFatouCoordOn F Φ (MandelDim.Qreg c₁ c₂)) :
    ∃ ΨE : ℂ → ℂ,
      MandelDim.IsFatouCoordOn F ΨE (MandelDim.Qreg b₁ b₂) ∧
      (∀ z ∈ MandelDim.Qreg c₁ c₂, ΨE z = Φ z) ∧
      Work.Pert.DphiP f Df τ ΨE (MandelDim.Qreg c₁ c₂) =
        Work.Pert.DphiP f Df τ Φ (MandelDim.Qreg c₁ c₂) ∧
      (∀ w : ℂ, Work.Pert.coordP f Df τ ΨE (MandelDim.Qreg c₁ c₂) w =
        Work.Pert.coordP f Df τ Φ (MandelDim.Qreg c₁ c₂) w) := by
  classical
  -- a Fatou coordinate on the larger region, and its restriction to the smaller one
  obtain ⟨Ψ, hΨbig, -⟩ := hEx b₁ b₂ F hadm hNT
  have hΨsmall : MandelDim.IsFatouCoordOn F Ψ (MandelDim.Qreg c₁ c₂) :=
    ⟨hΨbig.1.mono hsub, hΨbig.2.1.mono hsub,
      fun z hz hFz => hΨbig.2.2 z (hsub hz) (hsub hFz)⟩
  -- uniqueness on the shared region pins the additive constant
  obtain ⟨c, hc⟩ := hUn c₁ c₂ F Ψ Φ hadm' hNT' hΨsmall hΦ
  have heqOn : ∀ z ∈ MandelDim.Qreg c₁ c₂, (fun z => Ψ z + c) z = Φ z := by
    intro z hz
    simpa using (hc z hz).symm
  -- `DphiP`/`coordP` only see the coordinate on the gate
  obtain ⟨hDphi, hcoord⟩ := dphiP_coordP_congr_of_eqOn (f := f) (Df := Df) (τ := τ)
    (Φ := Φ) (Ψ := fun z => Ψ z + c) (Q := MandelDim.Qreg c₁ c₂) hΦ.2.1 heqOn
  exact ⟨fun z => Ψ z + c, Work.Pert.MandelDim.IsFatouCoordOn.add_const hΨbig c,
    heqOn, hDphi, hcoord⟩

end

end Work.Pert.pert2v2
