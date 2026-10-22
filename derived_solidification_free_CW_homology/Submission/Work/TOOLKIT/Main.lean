/-
AREA TOOLKIT — the deliverable: `toolkit_prop : Submission.Blueprint.ToolkitProp`.

The area is the chapter of homological algebra of `D(LightCondAb)` that the paper's proof needs:
closure properties of solid-equivalences.  The pieces are

* `Basic.lean`   — vocabulary (`DCat`, `KCat`, `SDCat`, `iD`, `precomp`, `precompD`, the
  connecting map `conn` of the contravariant long exact sequence) and the formal closure
  properties `comp`, `of_comp_left`, `of_comp_right`, `of_iso`;
* `Les/`         — exactness of the contravariant long exact `Hom(-, iD.obj N⟦m⟧)` sequences
  (`les_exact`, `conn_naturality`) and the three two-out-of-three statements for a morphism of
  distinguished triangles (`solidEquiv_middle`, `solidEquiv_right`, `solidEquiv_left`);
* `Ses.lean`     — the fields `ses₁`, `ses₂`, `ses₃`;
* `Shift/`       — shift-invariance of solid-equivalences;
* `Sigma.lean`   — the field `sigma`, from `Q` preserving small coproducts (`Coprod.lean`);
* `Coprod.lean`  — for other areas (in particular RESOL): the coproduct/colimit instances of
  `Instances.lean`, and C1–C3 (`quasiIso_colimMap`, `quasiIso_sigma`, `hq_sigma_bijective`,
  `Qh_sigma_bijective`, `Q_sigma_bijective`);
* `SeqColim/`    — the field `seqColim` (telescope sequence);
* `Levelwise/`   — the field `levelwise` (brutal truncations);
* `Axioms.lean`  — audit: every declaration of the area depends only on `propext`,
  `Classical.choice`, `Quot.sound`.

Nothing in the area imports another area of the workspace: the only external import is
`Submission.Blueprint.Interfaces`.  Its mathematical inputs are exactly Mathlib plus AB4/AB5 for
`LightCondAb`.
-/
import Submission.Work.TOOLKIT.Basic
import Submission.Work.TOOLKIT.Les.les_exact
import Submission.Work.TOOLKIT.Les.conn_naturality
import Submission.Work.TOOLKIT.Ses
import Submission.Work.TOOLKIT.Sigma
import Submission.Work.TOOLKIT.Coprod
import Submission.Work.TOOLKIT.SeqColim.solidEquiv_seqColim_of
import Submission.Work.TOOLKIT.Levelwise.solidEquiv_levelwise_of

open CategoryTheory Limits LightProfinite LightCondensed MonoidalCategory MonoidalClosed
open _root_.LightCondensed _root_.LightCondensed.Solid
open Submission.Blueprint

noncomputable section

namespace Work.TOOLKIT

/-- **The `seqColim` field**: solid-equivalences are stable under sequential colimits along
monomorphisms. -/
theorem solidEquiv_seqColim (F G : CategoryTheory.Functor ℕ Cpx) (τ : F ⟶ G)
    (hF : ∀ n, Mono (F.map (homOfLE (Nat.le_succ n))))
    (hG : ∀ n, Mono (G.map (homOfLE (Nat.le_succ n))))
    (h : ∀ n, SolidEquiv (DerivedCategory.Q.map (τ.app n))) :
    SolidEquiv (DerivedCategory.Q.map (colim.map τ)) :=
  SeqColim.solidEquiv_seqColim_of
    (fun h₁ h₂ φ h₁' h₂' => solidEquiv_ses₃ h₁ h₂ φ h₁' h₂')
    solidEquiv_sigma F G τ hF hG h

/-- **The `levelwise` field**: the degreewise criterion for complexes concentrated in degrees
`≤ 0`. -/
theorem solidEquiv_levelwise (K L : Cpx) (f : K ⟶ L)
    (hK : ∀ q : ℤ, 0 < q → IsZero (K.X q)) (hL : ∀ q : ℤ, 0 < q → IsZero (L.X q))
    (hf : ∀ q : ℤ, SolidEquiv ((DerivedCategory.singleFunctor LightCondAb 0).map (f.f q))) :
    SolidEquiv (DerivedCategory.Q.map f) :=
  Levelwise.solidEquiv_levelwise_of
    (fun h₁ h₂ φ h₁' h₃' => solidEquiv_ses₂ h₁ h₂ φ h₁' h₃')
    solidEquiv_seqColim K L f hK hL hf

/-- **AREA TOOLKIT**: closure properties of solid-equivalences. -/
theorem toolkit_prop : Submission.Blueprint.ToolkitProp where
  comp := fun f g hf hg => solidEquiv_comp f g hf hg
  of_comp_left := fun f g hf hfg => solidEquiv_of_comp_left f g hf hfg
  of_comp_right := fun f g hg hfg => solidEquiv_of_comp_right f g hg hfg
  of_iso := fun f hf => solidEquiv_of_iso f hf
  ses₂ := fun h₁ h₂ φ hφ₁ hφ₃ => solidEquiv_ses₂ h₁ h₂ φ hφ₁ hφ₃
  ses₃ := fun h₁ h₂ φ hφ₁ hφ₂ => solidEquiv_ses₃ h₁ h₂ φ hφ₁ hφ₂
  ses₁ := fun h₁ h₂ φ hφ₂ hφ₃ => solidEquiv_ses₁ h₁ h₂ φ hφ₂ hφ₃
  sigma := fun J K L _ _ f hf => solidEquiv_sigma J K L f hf
  seqColim := fun F G τ hF hG h => solidEquiv_seqColim F G τ hF hG h
  levelwise := fun K L f hK hL hf => solidEquiv_levelwise K L f hK hL hf

end Work.TOOLKIT
