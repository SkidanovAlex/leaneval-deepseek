import Mathlib
import Submission.Work.ATOM.ZS.PsiLiftDefs
import Submission.Work.ATOM.ZS.NullSeqMaps
import Submission.Work.ATOM.ZS.e_pred_eq_of_psi_infty
import Submission.Work.ATOM.ZS.psiN_gBig
import Submission.Work.ANALYTIC.EA_shift

open CategoryTheory MonoidalCategory LightCondensed

namespace Work.ATOM.ZS

/-!
# AREA ATOM / `ℤ[S]`: the identity `h₁` of the null-sequence scheme for `ℤ[S]`

The identity `h₁` of REFS/03 §1 is

  `((1 - S) ⊗ id) ≫ F = G ≫ g̃`   on `P ⊗ ℤ[S]`.

Both sides are morphisms `P ⊗ ℤ[S] ⟶ ℤ̃[S]`.  Since `Work.ATOM.EA S : ℤ[(ℕ∪{∞}) × S] ⟶ P ⊗ ℤ[S]`
is an epimorphism (a cokernel projection followed by an isomorphism), it suffices to check the
identity after pulling back along `EA S`, where all the maps have explicit descriptions:

* `EA S ≫ ((1-S) ⊗ id) = (1 - zmap (shift × id)) ≫ EA S` (`Work.ANALYTIC.EA_shift`) together with
  `EA S ≫ F = Fsection` (`Work.ATOM.F_spec`);
* `EA S ≫ G = Gsection = zmap ψ ≫ P_proj` (`Work.ATOM.G_spec`), `P_proj ≫ g = gBig`
  (`Work.ATOM.g_spec`) and `gRed = g ≫ qred`.

Both reduced forms are the morphism `(zmap eShift - zmap ePred) ≫ qred : ℤ[(ℕ∪{∞}) × S] ⟶ ℤ̃[S]`,
whose value on the generator `(k,x)` is `[e_k x] - [e_{k-1} x]`: this is the content of
`EA_preShift_F` and of `EA_G_gRed` (the latter using `Work.ATOM.ZS.psiN_gBig`).
-/

/-- `EA S : ℤ[(ℕ∪{∞}) × S] ⟶ P ⊗ ℤ[S]` is an epimorphism: it is the composite of the isomorphism
`zfreeTensorIso` with `P_proj ▷ ℤ[S]`, and `P_proj = cokernel.π P_map` is a cokernel projection,
which stays an epimorphism after tensoring with `ℤ[S]` (`- ▷ ℤ[S]` is a left adjoint, hence
preserves colimits). -/
theorem epi_EA (S : LightProfinite.{0}) : Epi (Work.ATOM.EA S) := by
  haveI hπ : Epi LightCondensed.P_proj := LightCondensed.PSequence_exact.epi_g
  haveI hw : Epi (LightCondensed.P_proj ▷ Work.ATOM.zfree S) := by
    change Epi ((tensorRight (Work.ATOM.zfree S)).map LightCondensed.P_proj)
    exact Functor.map_epi (tensorRight (Work.ATOM.zfree S)) LightCondensed.P_proj
  rw [Work.ATOM.EA]
  exact epi_comp _ _

/-- **The reduced left hand side of `h₁`.**  Pulling back `((1-S) ⊗ id) ≫ F` along `EA S` gives
`(zmap eShift - zmap ePred) ≫ qred`, i.e. on the generator `(k,x)`:
`[e_k x] - [e_{k-1} x]`.  Route: `Work.ANALYTIC.EA_shift` moves `1 - S` past `EA S`, and
`Work.ATOM.F_spec` replaces `EA S ≫ F` by `Fsection = (zmap pr₂N - zmap ePred) ≫ qred`; the
remaining difference of the two `zmap`-terms is evaluated with `Work.ATOM.shiftNS_pr₂N` (the
second coordinate is unchanged by the shift) and `Work.ATOM.eShift_eq` (`eShift = ePred ∘ shift`).
-/
theorem EA_preShift_F (S : LightProfinite.{0}) [Infinite S] :
    Work.ATOM.EA S ≫ (Work.ATOM.preShift (Work.ATOM.zfree S) ≫ Work.ATOM.F S) =
      (Work.ATOM.zmap (Work.ATOM.eShift S) - Work.ATOM.zmap (Work.ATOM.ePred S)) ≫
        Work.ATOM.qred S (Work.ATOM.levelData S).s₀ := by
  have hEA := Work.ANALYTIC.EA_shift S
  have hshift : Work.ATOM.preShift (Work.ATOM.zfree S) =
      (LightCondensed.oneMinusShift ▷ Work.ATOM.zfree S) := rfl
  have hA_B : Work.ATOM.zmap (Work.ATOM.shiftNS S) ≫ Work.ATOM.zmap (Work.ATOM.pr₂N S) =
      Work.ATOM.zmap (Work.ATOM.pr₂N S) := by
    rw [← zmap_comp, Work.ATOM.shiftNS_pr₂N S]
  have hA_C : Work.ATOM.zmap (Work.ATOM.shiftNS S) ≫ Work.ATOM.zmap (Work.ATOM.ePred S) =
      Work.ATOM.zmap (Work.ATOM.eShift S) := by
    rw [← zmap_comp, Work.ATOM.eShift_eq]
  calc Work.ATOM.EA S ≫ (Work.ATOM.preShift (Work.ATOM.zfree S) ≫ Work.ATOM.F S)
      = (Work.ATOM.EA S ≫ Work.ATOM.preShift (Work.ATOM.zfree S)) ≫ Work.ATOM.F S :=
        Category.assoc _ _ _
    _ = ((𝟙 (Work.ATOM.zfree (Work.ATOM.NS S)) - Work.ATOM.zmap (Work.ATOM.shiftNS S)) ≫
          Work.ATOM.EA S) ≫ Work.ATOM.F S := by rw [hshift, hEA]
    _ = (𝟙 (Work.ATOM.zfree (Work.ATOM.NS S)) - Work.ATOM.zmap (Work.ATOM.shiftNS S)) ≫
          Work.ATOM.Fsection S := by rw [Category.assoc, Work.ATOM.F_spec]
    _ = (Work.ATOM.zmap (Work.ATOM.eShift S) - Work.ATOM.zmap (Work.ATOM.ePred S)) ≫
          Work.ATOM.qred S (Work.ATOM.levelData S).s₀ := by
        rw [Work.ATOM.Fsection, Preadditive.sub_comp, Category.id_comp]
        rw [← Category.assoc (Work.ATOM.zmap (Work.ATOM.shiftNS S)),
          Preadditive.comp_sub, hA_B, hA_C]
        rw [← Preadditive.sub_comp]
        congr 1
        exact sub_sub_sub_cancel_left _ _ _

/-- **The reduced right hand side of `h₁`.**  Pulling back `G ≫ g̃` along `EA S` gives the same
morphism `(zmap eShift - zmap ePred) ≫ qred`: on the generator `(k,x)` both sides are
`[e_k x] - [e_{k-1} x]`.  Route: `EA S ≫ G = Gsection = zmap ψ ≫ P_proj`
(`Work.ATOM.G_spec`), `P_proj ≫ g = gBig` (`Work.ATOM.g_spec`), and
`zmap ψ ≫ gBig = zmap eShift - zmap ePred` (`Work.ATOM.ZS.psiN_gBig`). -/
theorem EA_G_gRed (S : LightProfinite.{0}) [Infinite S] :
    Work.ATOM.EA S ≫ (Work.ATOM.G S ≫ Work.ATOM.gRed S) =
      (Work.ATOM.zmap (Work.ATOM.eShift S) - Work.ATOM.zmap (Work.ATOM.ePred S)) ≫
        Work.ATOM.qred S (Work.ATOM.levelData S).s₀ := by
  calc Work.ATOM.EA S ≫ (Work.ATOM.G S ≫ Work.ATOM.gRed S)
      = (Work.ATOM.EA S ≫ Work.ATOM.G S) ≫ Work.ATOM.gRed S := Category.assoc _ _ _
    _ = Work.ATOM.Gsection S ≫ Work.ATOM.gRed S := by rw [Work.ATOM.G_spec]
    _ = (Work.ATOM.zmap (Work.ATOM.psiN S) ≫ LightCondensed.P_proj) ≫
          (Work.ATOM.g S ≫ Work.ATOM.qred S (Work.ATOM.levelData S).s₀) := rfl
    _ = (Work.ATOM.zmap (Work.ATOM.psiN S) ≫ Work.ATOM.gBig S) ≫
          Work.ATOM.qred S (Work.ATOM.levelData S).s₀ := by
        rw [← Category.assoc (Work.ATOM.zmap (Work.ATOM.psiN S) ≫ LightCondensed.P_proj)
            (Work.ATOM.g S) (Work.ATOM.qred S (Work.ATOM.levelData S).s₀),
          Category.assoc (Work.ATOM.zmap (Work.ATOM.psiN S)) LightCondensed.P_proj
            (Work.ATOM.g S),
          Work.ATOM.g_spec]
    _ = (Work.ATOM.zmap (Work.ATOM.eShift S) - Work.ATOM.zmap (Work.ATOM.ePred S)) ≫
          Work.ATOM.qred S (Work.ATOM.levelData S).s₀ := by
        rw [psiN_gBig S]

/-- **Identity `h₁` of REFS/03 §1**: `T ≫ F = G ≫ g̃`, where `T = (1-S) ⊗ id` on `P ⊗ ℤ[S]`.
On generators `(k,x)` of `(ℕ∪{∞}) × S` both sides give `[e_k x] - [e_{k-1} x]`: the left side is
`F(k,x) - F(k+1,x)`, and on the right `G(k,x) = e_{ψ(k,x)}` so we use
`Work.ATOM.psiN_eq_of` (`g̃(e_j) = [a_j] - [e_{n(j)-1} a_j]`) when `ψ(k,x) = j`, and
`Work.ATOM.ZS.e_pred_eq_of_mem_A` (when `e_k x` is of level `< k`, so `ψ(k,x) = ∞`, both sides
vanish) / `e_fix_of_mem_A_of_le` otherwise.  Route in Lean: precompose with `Work.ATOM.EA S`
(an epimorphism, so precomposition is injective) and reduce to the `Work.ATOM.F_spec`,
`Work.ATOM.G_spec` and `Work.ATOM.g_spec` descriptions; then check on a closed cover of
`(ℕ∪{∞}) × S` with `Work.ATOM.zmap_ext_of_closed_cover`. -/
theorem h_one (S : LightProfinite.{0}) [Infinite S] :
    Work.ATOM.preShift (Work.ATOM.zfree S) ≫ Work.ATOM.F S = Work.ATOM.G S ≫ Work.ATOM.gRed S := by
  haveI := epi_EA S
  refine (cancel_epi (Work.ATOM.EA S)).mp ?_
  rw [EA_preShift_F S, EA_G_gRed S]

end Work.ATOM.ZS
